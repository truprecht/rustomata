use super::{Bracket, BracketContent, Delta, PMCFGRule, StateStorage};
use crate::{grammars::pmcfg::VarT, util::tree::GornTree};
use num_traits::Zero;
use std::collections::HashMap;
use vecmultimap::VecMultiMapAdapter;

#[derive(PartialEq, Debug)]
pub struct LabelledTreeNode<L, I> {
    content: I,
    successors: Vec<(L, LabelledTreeNode<L, I>)>,
}

impl<L: std::fmt::Debug, I: std::fmt::Debug> std::fmt::Display for LabelledTreeNode<L, I> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        use std::iter::repeat;
        let mut position_stack = vec![(self, 0, 0)];
        writeln!(f, "{:?}", self.content)?;

        while let Some((parent, child_index, level)) = position_stack.pop() {
            if parent.successors.len() <= child_index {
                continue;
            }

            let &(ref label, ref child) = &parent.successors[child_index];
            repeat("\t")
                .take(level)
                .fold(Ok(()), |r, s| r.and_then(|_| write!(f, "{}", s)))?;
            writeln!(f, "{:?} {:?}", label, child.content)?;
            position_stack.push((parent, child_index + 1, level));
            position_stack.push((child, 0, level + 1));
        }

        Ok(())
    }
}

impl<I: PartialEq> LabelledTreeNode<(usize, usize), I> {
    /// Checks consistency of a cow derivation.
    /// The check implemented in csparsing::toderiv is slightly faster,
    /// since it does not need to convert the given word into a cow
    /// derivation.
    #[allow(dead_code)]
    pub fn is_consistent(&self) -> bool {
        Self::is_consistent_vec(vec![self])
    }

    fn is_consistent_vec(trees: Vec<&Self>) -> bool {
        // check if all elements are equal
        if let Some((t, ts)) = trees.split_first() {
            if !ts.iter().all(|te| te.content == t.content) {
                return false;
            }
        }

        // collect successors
        let mut successors_per_fst: Vec<Vec<&Self>> = Vec::new();
        for t in trees {
            for &((i, _), ref successor) in &t.successors {
                VecMultiMapAdapter(&mut successors_per_fst).push_to(i, successor);
            }
        }

        // consistency for successors
        successors_per_fst.into_iter().all(Self::is_consistent_vec)
    }
}

/// In the context of this module, an object is either a rule or a fallback id.
#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
pub enum ROF<R, F> {
    R(R),
    F(F),
}
/// Either a rule index or a fallback identified by lhs and rhs nonterminal.
pub type RuleOrFallback = ROF<usize, (u32, u32)>;
/// Either a rule index and looked-up rule or a fallback structure that
/// contains the lhs and rhs nonterminal, and the split-nonterminal
/// (component and lcfrs-nonterminal).
type LookedUpRuleOrFallback<'a, N, T, W> =
    ROF<(usize, &'a PMCFGRule<N, T, W>), (u32, u32, (u8, &'a N))>;

/// An edge-labeled tree where each node is either a gramar rule or
/// a fallback identifier.
pub type CowDerivation = LabelledTreeNode<(usize, usize), RuleOrFallback>;
/// Re-index for successors of a group of `CowDerivation`s.
/// A new successor index is given for each rule and successor.
type ReIndex = HashMap<(RuleOrFallback, usize), usize>;

impl CowDerivation {
    /// Reads a `CowDerivation` off a Dyck word over `Delta`-symbols.
    /// The `StateStorage` is used to get the referenced component in the case
    /// of fallback signatures.
    pub fn new<N>(v: &[Delta], states: &StateStorage<N>) -> Self {
        use self::{Bracket::*, BracketContent::*};

        let mut root: CowDerivation = LabelledTreeNode {
            content: ROF::R(0),
            successors: Vec::new(),
        };
        let mut pos: Vec<*mut CowDerivation> =
            vec![&mut root as *mut CowDerivation];

        for symbol in v {
            match *symbol {
                Open(Component(rule, _)) => unsafe {
                    (**pos.last().unwrap()).content = ROF::R(rule as usize);
                },
                Open(Fallback(from, to)) => unsafe {
                    let successor_component = states.get(to).unwrap().0;
                    let current_node = *pos.last().unwrap();
                    (*current_node).content = ROF::F((from, to));
                    (*current_node).successors.push((
                        (0, successor_component as usize),
                        LabelledTreeNode {
                            content: ROF::R(0),
                            successors: Vec::new(),
                        }
                    ));
                    let p = &mut (*current_node).successors[0].1
                        as *mut CowDerivation;
                    pos.push(p);
                },
                Open(Variable(_, i, j)) => unsafe {
                    (**pos.last().unwrap()).successors.push((
                        (i as usize, j as usize),
                        LabelledTreeNode {
                            content: ROF::R(0),
                            successors: Vec::new(),
                        },
                    ));
                    let p = &mut (**pos.last().unwrap()).successors.last_mut().unwrap().1
                        as *mut CowDerivation;
                    pos.push(p);
                },
                Close(Variable(_, _, _))
                | Close(Fallback(_, _))=> {
                    pos.pop();
                }
                _ => {}
            }
        }

        root
    }

    /// Collects the child trees of a group of `CowDerivation`s.
    /// Each of those child trees is assigned a group index by the `reindex`
    /// structure determined by the tree's root (rule/fallback id) and
    /// the first edge label.
    fn collect_children<'a, I>(trees: I, reindex: ReIndex) -> Vec<Vec<(usize, &'a Self)>>
    where
        I: Iterator<Item = &'a Self>,
    {
        let mut successors_per_fst: Vec<Vec<(usize, &Self)>> = Vec::new();

        for t in trees {
            for &((i, j), ref successor) in &t.successors {
                let index = reindex[&(t.content, i)];
                VecMultiMapAdapter(&mut successors_per_fst).push_to(index, (j, successor));
            }
        }

        successors_per_fst
    }

    /// Constructs a derivation from a given `CowDerivation`.
    pub fn fallback<N, T, W>(
        &self,
        int: &[PMCFGRule<N, T, W>],
        nt_int: &StateStorage<N>,
    ) -> GornTree<PMCFGRule<N, T, W>>
    where
        N: Clone,
        T: Clone,
        W: Zero,
    {
        let mut deriv = GornTree::new();
        Self::fallback_vec(&[(0, self)], int, &mut deriv, Vec::new(), nt_int);
        deriv
    }

    /// Merge a list of rules given by an iterator over triples containing
    /// * a component index,
    /// * a rule or a fallback signature.
    /// Returns a reordering of rhs nonterminals (ruleid, rhs index ↦ new rhs index)
    /// and the constructed rule.
    fn merge_rules<'a, N, T, W, I>(head: N, roots: I) -> (ReIndex, PMCFGRule<N, T, W>)
    where
        W: 'a + Zero,
        N: 'a + Clone,
        T: 'a + Clone,
        I: Clone + Iterator<Item = (usize, LookedUpRuleOrFallback<'a, N, T, W>)>,
    {
        // store iterator for a second pass
        let second_pass = roots.clone();

        // first pass through compositions:
        // collects all used nonterminals and reorders them by occurance
        let mut nt_reindex = HashMap::new();
        let mut tail = Vec::new();
        let mut fanout = 0;
        for (component, rof) in roots {
            match rof {
                ROF::R((rule_id, rule)) => {
                    for i in rule.composition[component]
                        .iter()
                        .filter_map(|symbol| match *symbol {
                            VarT::Var(i, _) => Some(i),
                            _ => None,
                        })
                    {
                        nt_reindex.entry((ROF::R(rule_id), i)).or_insert_with(|| {
                            tail.push(rule.tail[i].clone());
                            tail.len() - 1
                        });
                    }
                }
                ROF::F((h, t, tail_info)) => {
                    tail.push(tail_info.1.clone());
                    nt_reindex.insert((ROF::F((h, t)), 0), tail.len() - 1);
                }
            }

            fanout = usize::max(fanout, component + 1);
        }

        // second pass through compositions:
        // uses reordering of nonterminals and applies it
        // to all variables' first indices
        let mut composition = Vec::new();
        composition.resize_with(fanout, Vec::new);
        for (component, rof) in second_pass {
            match rof {
                ROF::R((ruleid, rule)) => {
                    composition[component].extend(rule.composition[component].iter().map(
                        |symbol| match symbol {
                            VarT::T(t) => VarT::T(t.clone()),
                            &VarT::Var(i, j) => VarT::Var(nt_reindex[&(ROF::R(ruleid), i)], j),
                        },
                    ));
                }
                ROF::F((h, t, tail_info)) => {
                    let successor_index = nt_reindex[&(ROF::F((h, t)), 0)];
                    composition[component].push(VarT::Var(successor_index, tail_info.0 as usize));
                }
            }
        }

        (
            nt_reindex,
            PMCFGRule {
                head,
                tail,
                composition: composition.into(),
                weight: W::zero(),
            },
        )
    }

    // Merges a group of cow derivations.
    fn fallback_vec<N, T, W>(
        roots: &[(usize, &Self)],
        int: &[PMCFGRule<N, T, W>],
        tree: &mut GornTree<PMCFGRule<N, T, W>>,
        pos: Vec<usize>,
        nt_int: &StateStorage<N>,
    ) where
        N: Clone,
        T: Clone,
        W: Zero,
    {
        let root_lhs = match roots[0].1.content {
            ROF::R(id) => int[id].head.clone(),
            ROF::F((head, _)) => nt_int.get(head).unwrap().1.clone(),
        };

        let lookup_rof = |rof| match rof {
            &ROF::R(rule_id) => ROF::R((rule_id, &int[rule_id])),
            &ROF::F((h, t)) => ROF::F((h, t, nt_int.get(t).unwrap())),
        };

        let (nt_reindex, root_node) = Self::merge_rules(
            root_lhs,
            roots.iter().map(|&(j, ref t)| (j, lookup_rof(&t.content))),
        );

        // process children with same first label
        for (sidx, child_group) in Self::collect_children(roots.iter().map(|&(_, t)| t), nt_reindex)
            .into_iter()
            .enumerate()
            .filter(|&(_, ref v)| !v.is_empty())
        {
            let mut spos = pos.clone();
            spos.push(sidx);
            Self::fallback_vec(&child_group, int, tree, spos, nt_int);
        }

        tree.insert(pos, root_node);
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::grammars::pmcfg::Composition;
    use log_domain::LogDomain;
    use num_traits::One;

    #[test]
    fn rule_merging() {
        use self::VarT::*;
        use self::ROF::*;
        let one: LogDomain<f64> = LogDomain::one();

        let rules: Vec<(usize, usize, PMCFGRule<char, char, LogDomain<f64>>)> = vec![
            (
                0,
                0,
                PMCFGRule {
                    head: 'A',
                    tail: vec!['B', 'C'],
                    weight: one,
                    composition: Composition {
                        composition: vec![vec![Var(1, 0)], vec![Var(0, 0)]],
                    },
                },
            ),
            (
                1,
                1,
                PMCFGRule {
                    head: 'A',
                    tail: vec!['D', 'E'],
                    weight: one,
                    composition: Composition {
                        composition: vec![vec![], vec![Var(0, 0), Var(1, 0)]],
                    },
                },
            ),
        ];

        assert_eq!(
            CowDerivation::merge_rules('A', rules.iter().map(|&(c, rid, ref r)| (c, R((rid, r))))).1,
            PMCFGRule {
                head: 'A',
                tail: vec!['C', 'D', 'E'],
                weight: LogDomain::zero(),
                composition: Composition {
                    composition: vec![vec![Var(0, 0)], vec![Var(1, 0), Var(2, 0)]]
                }
            }
        )
    }

    #[test]
    fn readoff() {
        let states = StateStorage::<usize>::with_capacity(0);
        for (word, cowd, _) in fails_with_fallbacks() {
            assert_eq!(CowDerivation::new(&word, &states), cowd)
        }
    }

    #[test]
    fn tree_merging() {
        let states = StateStorage::with_capacity(0);
        for (word, _, tree) in fails_with_fallbacks() {
            assert_eq!(CowDerivation::new(&word, &states).fallback(&rules(), &states), tree);
        }
    }

    fn rules() -> Vec<PMCFGRule<char, &'static str, LogDomain<f64>>> {
        use self::VarT::*;
        let one: LogDomain<f64> = LogDomain::one();

        let mut vec = Vec::new();

        vec.push(PMCFGRule {
            head: 'S',
            tail: vec!['A'],
            composition: Composition {
                composition: vec![vec![Var(0, 0), Var(0, 1)]],
            },
            weight: one,
        });

        vec.push(PMCFGRule {
            head: 'A',
            tail: Vec::new(),
            composition: Composition {
                composition: vec![vec![], vec![T("asdf")]],
            },
            weight: one,
        });
        vec.push(PMCFGRule {
            head: 'A',
            tail: Vec::new(),
            composition: Composition {
                composition: vec![vec![T("qwer")], vec![]],
            },
            weight: one,
        });

        vec.push(PMCFGRule {
            head: 'A',
            tail: vec!['B', 'C'],
            composition: Composition {
                composition: vec![vec![Var(1, 1)], vec![]],
            },
            weight: one,
        });
        vec.push(PMCFGRule {
            head: 'A',
            tail: vec!['D', 'E'],
            composition: Composition {
                composition: vec![vec![], vec![Var(1, 1)]],
            },
            weight: one,
        });
        vec.push(PMCFGRule {
            head: 'C',
            tail: vec!['A'],
            composition: Composition {
                composition: vec![vec![Var(0, 0)], vec![Var(0, 1)]],
            },
            weight: one,
        });
        vec.push(PMCFGRule {
            head: 'E',
            tail: vec!['A'],
            composition: Composition {
                composition: vec![vec![Var(0, 1)], vec![Var(0, 0)]],
            },
            weight: one,
        });

        vec
    }

    fn fails_with_fallbacks() -> Vec<(
        Vec<Delta>,
        CowDerivation,
        GornTree<PMCFGRule<char, &'static str, LogDomain<f64>>>,
    )> {
        use self::Bracket::*;
        use self::BracketContent::*;
        use self::VarT::*;
        use self::ROF::*;
        let rules = rules();

        vec![
            (
                vec![
                    Open(Component(0, 0)),
                    Open(Variable(0, 0, 0)),
                    Open(Component(1, 0)),
                    Close(Component(1, 0)),
                    Close(Variable(0, 0, 0)),
                    Open(Variable(0, 0, 1)),
                    Open(Component(2, 0)),
                    Close(Component(2, 0)),
                    Close(Variable(0, 0, 1)),
                    Close(Component(0, 0)),
                ],
                LabelledTreeNode {
                    content: R(0),
                    successors: vec![
                        (
                            (0, 0),
                            LabelledTreeNode {
                                content: R(1),
                                successors: vec![],
                            },
                        ),
                        (
                            (0, 1),
                            LabelledTreeNode {
                                content: R(2),
                                successors: vec![],
                            },
                        ),
                    ],
                },
                vec![
                    (vec![], rules[0].clone()),
                    (
                        vec![0],
                        PMCFGRule {
                            head: 'A',
                            tail: vec![],
                            composition: Composition {
                                composition: vec![vec![], vec![]],
                            },
                            weight: LogDomain::zero(),
                        },
                    ),
                ]
                .into_iter()
                .collect(),
            ),
            (
                vec![
                    Open(Component(0, 0)),
                    Open(Variable(0, 0, 0)),
                    Open(Component(3, 0)),
                    Open(Variable(3, 1, 1)),
                    Open(Component(5, 1)),
                    Open(Variable(5, 0, 1)),
                    Open(Component(2, 1)),
                    Close(Component(2, 1)),
                    Close(Variable(5, 0, 1)),
                    Close(Component(5, 1)),
                    Close(Variable(3, 1, 1)),
                    Close(Component(3, 0)),
                    Close(Variable(0, 0, 0)),
                    Open(Variable(0, 0, 1)),
                    Open(Component(4, 1)),
                    Open(Variable(4, 1, 1)),
                    Open(Component(6, 1)),
                    Open(Variable(6, 0, 0)),
                    Open(Component(1, 0)),
                    Close(Component(1, 0)),
                    Close(Variable(6, 0, 0)),
                    Close(Component(6, 1)),
                    Close(Variable(4, 1, 1)),
                    Close(Component(4, 0)),
                    Close(Variable(0, 0, 1)),
                    Close(Component(0, 0)),
                ],
                LabelledTreeNode {
                    content: R(0),
                    successors: vec![
                        (
                            (0, 0),
                            LabelledTreeNode {
                                content: R(3),
                                successors: vec![(
                                    (1, 1),
                                    LabelledTreeNode {
                                        content: R(5),
                                        successors: vec![(
                                            (0, 1),
                                            LabelledTreeNode {
                                                content: R(2),
                                                successors: vec![],
                                            },
                                        )],
                                    },
                                )],
                            },
                        ),
                        (
                            (0, 1),
                            LabelledTreeNode {
                                content: R(4),
                                successors: vec![(
                                    (1, 1),
                                    LabelledTreeNode {
                                        content: R(6),
                                        successors: vec![(
                                            (0, 0),
                                            LabelledTreeNode {
                                                content: R(1),
                                                successors: vec![],
                                            },
                                        )],
                                    },
                                )],
                            },
                        ),
                    ],
                },
                vec![
                    (vec![], rules[0].clone()),
                    (
                        vec![0],
                        PMCFGRule {
                            head: 'A',
                            tail: vec!['C', 'E'],
                            composition: Composition {
                                composition: vec![vec![Var(0, 1)], vec![Var(1, 1)]],
                            },
                            weight: LogDomain::zero(),
                        },
                    ),
                    (
                        vec![0, 0],
                        PMCFGRule {
                            head: 'C',
                            tail: vec!['A'],
                            composition: Composition {
                                composition: vec![vec![], vec![Var(0, 1)]],
                            },
                            weight: LogDomain::zero(),
                        },
                    ),
                    (
                        vec![0, 0, 0],
                        PMCFGRule {
                            head: 'A',
                            tail: vec![],
                            composition: Composition {
                                composition: vec![vec![], vec![]],
                            },
                            weight: LogDomain::zero(),
                        },
                    ),
                    (
                        vec![0, 1],
                        PMCFGRule {
                            head: 'E',
                            tail: vec!['A'],
                            composition: Composition {
                                composition: vec![vec![], vec![Var(0, 0)]],
                            },
                            weight: LogDomain::zero(),
                        },
                    ),
                    (
                        vec![0, 1, 0],
                        PMCFGRule {
                            head: 'A',
                            tail: vec![],
                            composition: Composition {
                                composition: vec![vec![]],
                            },
                            weight: LogDomain::zero(),
                        },
                    ),
                ]
                .into_iter()
                .collect(),
            ),
        ]
    }
}
