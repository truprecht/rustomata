use std::collections::{BTreeMap, HashMap};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::Index;
use std::slice;
use std::vec;

use crate::mcfg::Mcfg;
use rustomata_util::gorntree::GornTree;

#[cfg(feature = "from-string")]
mod from_str;
pub mod negra;
mod rule_macro;

#[cfg(feature = "serialization")]
use serde::{Serialize, Deserialize};

/// Variable or terminal symbol in a PMCFG.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
#[cfg_attr(feature = "serialization", derive(Serialize, Deserialize))]
pub enum VarT<T> {
    /// `Var(i, j)` represents the `j`th component of the `i`th successor.
    /// Indexing starts from `0`.
    Var(usize, usize),
    T(T),
}

impl<T> VarT<T> {
    pub fn is_var(&self) -> bool {
        match self {
            &VarT::Var(_, _) => true,
            _ => false,
        }
    }

    pub fn is_t(&self) -> bool {
        match self {
            &VarT::T(_) => true,
            _ => false,
        }
    }

    pub fn unwrap_var(&self) -> (usize, usize) {
        if let &VarT::Var(i, j) = self {
            (i, j)
        } else {
            panic!("unwrapped VarT was not a variable")
        }
    }

    pub fn unwrap_t(&self) -> &T {
        if let &VarT::T(ref t) = self {
            t
        } else {
            panic!("unwrapped VarT was not a terminal")
        }
    }

    pub fn map_t<U, F: Fn(T) -> U>(self, f: F) -> VarT<U> {
        match self {
            VarT::T(t) => VarT::T(f(t)),
            VarT::Var(i, j) => VarT::Var(i, j)
        }
    }
}

/// Composition function in a PMCFG.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
#[cfg_attr(feature = "serialization", derive(Serialize, Deserialize))]
pub struct Composition<T> {
    pub composition: Vec<Vec<VarT<T>>>,
}

impl<T> Composition<T> {
    pub fn len(&self) -> usize {
        self.composition.len()
    }

    pub fn iter(&self) -> <&Self as IntoIterator>::IntoIter {
        self.into_iter()
    }
}

impl<T> Index<usize> for Composition<T> {
    type Output = Vec<VarT<T>>;
    fn index(&self, idx: usize) -> &Self::Output {
        &self.composition[idx]
    }
}

impl<T> From<Vec<Vec<VarT<T>>>> for Composition<T> {
    fn from(encapsulated_value: Vec<Vec<VarT<T>>>) -> Self {
        Composition {
            composition: encapsulated_value,
        }
    }
}

impl<T> IntoIterator for Composition<T> {
    type Item = Vec<VarT<T>>;
    type IntoIter = vec::IntoIter<Vec<VarT<T>>>;

    fn into_iter(self) -> vec::IntoIter<Vec<VarT<T>>> {
        self.composition.into_iter()
    }
}

impl<'a, T> IntoIterator for &'a Composition<T> {
    type Item = &'a Vec<VarT<T>>;
    type IntoIter = slice::Iter<'a, Vec<VarT<T>>>;

    fn into_iter(self) -> slice::Iter<'a, Vec<VarT<T>>> {
        (&self.composition).into_iter()
    }
}

impl<'a, T> IntoIterator for &'a mut Composition<T> {
    type Item = &'a mut Vec<VarT<T>>;
    type IntoIter = slice::IterMut<'a, Vec<VarT<T>>>;

    fn into_iter(self) -> slice::IterMut<'a, Vec<VarT<T>>> {
        (&mut self.composition).into_iter()
    }
}

/// A rule of a weighted PMCFG.
///
/// ```
/// use std::str::FromStr;
/// use rustomata_grammar::pmcfg::{Composition, PMCFGRule, VarT::*};
/// use rustomata_grammar::pmcfg_rule;
///
/// let head = 'A';
/// let tail = vec!['A'];
/// let composition = Composition::from(vec![
///     vec![T('a'), Var(0, 0), T('b')],
///     vec![T('c'), Var(0, 1)],
/// ]);
/// let weight = 0.4;
///
/// assert_eq!(
///     PMCFGRule { head, tail, composition, weight },
///     pmcfg_rule!('A' => [[T('a'), Var(0, 0), T('b')], [T('c'), Var(0, 1)]] ('A') # 0.4)
/// );
/// ```
#[derive(Debug, PartialOrd, Ord, Clone)]
#[cfg_attr(feature = "serialization", derive(Serialize, Deserialize))]
pub struct PMCFGRule<N, T, W> {
    pub head: N,
    pub tail: Vec<N>,
    pub composition: Composition<T>,
    pub weight: W,
}

impl<N, T, W> PMCFGRule<N, T, W>
where
    T: Clone,
    W: Clone,
{
    pub fn map_nonterminals<F, M>(&self, f: F) -> PMCFGRule<M, T, W>
    where
        F: Fn(&N) -> M,
    {
        PMCFGRule {
            head: f(&self.head),
            tail: self.tail.iter().map(f).collect(),
            composition: self.composition.clone(),
            weight: self.weight.clone(),
        }
    }
}

/// A weighted, parallel multiple context-free grammar (PMCFG) with a set of initial nonterminal
/// symbols and a set of PMCFG rules.
///
/// ```
/// use std::str::FromStr;
/// use rustomata_grammar::pmcfg::{PMCFG, VarT::*};
/// use rustomata_grammar::pmcfg_rule;
///
/// let initial = vec!['S'];
/// let rules = vec![
///     pmcfg_rule!('S' => [[Var(0, 0), Var(0, 1)]] ('A') # 1f64),
///     pmcfg_rule!('A' => [[T('a'), Var(0, 0), T('b')], [T('c'), Var(0, 1)]] ('A') # 0.4),
///     pmcfg_rule!('A' => [[], []] () # 0.6),
/// ];
/// 
/// let pmcfg = PMCFG::<char, char, f64> { initial, rules };
/// ```
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct PMCFG<N, T, W> {
    // TODO: use HashSet
    pub initial: Vec<N>,
    pub rules: Vec<PMCFGRule<N, T, W>>,
}

impl<N, T, W> From<Mcfg<N, T, W>> for PMCFG<N, T, W> {
    fn from(mcfg: Mcfg<N, T, W>) -> Self {
        let (rules, initial) = mcfg.destruct();
        PMCFG {
            rules,
            initial: vec![initial],
        }
    }
}

impl<N: Hash, T: Hash, W> Hash for PMCFGRule<N, T, W> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.head.hash(state);
        self.tail.hash(state);
        self.composition.hash(state);
    }
}

impl<N: PartialEq, T: PartialEq, W> PartialEq for PMCFGRule<N, T, W> {
    fn eq(&self, other: &Self) -> bool {
        self.head == other.head && self.tail == other.tail && self.composition == other.composition
    }
}

impl<N: Eq, T: Eq, W> Eq for PMCFGRule<N, T, W> {}

impl<T: fmt::Display> fmt::Display for Composition<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut buffer = "".to_string();

        let mut iter0 = self.composition.iter().peekable();
        let mut iter1;

        buffer.push_str("[");
        while let Some(proj) = iter0.next() {
            iter1 = proj.into_iter().peekable();
            buffer.push_str("[");
            while let Some(vart) = iter1.next() {
                buffer.push_str(format!("{}", vart).as_str());
                if iter1.peek().is_some() {
                    buffer.push_str(", ");
                }
            }
            buffer.push_str("]");
            if iter0.peek().is_some() {
                buffer.push_str(", ");
            }
        }
        buffer.push_str("]");

        write!(f, "{}", buffer)
    }
}

impl<T: fmt::Display> fmt::Display for VarT<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            VarT::Var(i, j) => write!(f, "Var {} {}", i, j),
            VarT::T(ref x) => write!(f, "T \"{}\"", x),
        }
    }
}

impl<N: fmt::Display, T: fmt::Display, W: fmt::Display> fmt::Display for PMCFGRule<N, T, W> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut buffer = "".to_string();

        let mut iter = self.tail.iter().peekable();

        buffer.push_str("(");
        while let Some(nt) = iter.next() {
            buffer.push_str(format!("\"{}\"", nt).as_str());
            if iter.peek().is_some() {
                buffer.push_str(", ");
            }
        }
        buffer.push_str(")");

        write!(
            f,
            "\"{}\" → {} {}  # {}",
            self.head, self.composition, buffer, self.weight
        )
        // write!(f, "\"{}\" → {}", self.head, self.composition)
    }
}

impl<N: fmt::Display, T: fmt::Display, W: fmt::Display> fmt::Display for PMCFG<N, T, W> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut buffer = "".to_string();

        let mut iter = self.initial.iter().peekable();

        buffer.push_str("initial: [");
        while let Some(nt) = iter.next() {
            buffer.push_str(format!("\"{}\"", nt).as_str());
            if iter.peek().is_some() {
                buffer.push_str(", ");
            }
        }
        buffer.push_str("]\n\n");

        for r in &self.rules {
            buffer.push_str(format!("{}\n", r).as_str());
        }

        write!(f, "{}", buffer)
    }
}

pub fn evaluate<T>(term_map: &GornTree<Composition<T>>) -> Composition<T>
where
    T: Clone + fmt::Display,
{
    evaluate_pos(term_map, vec![])
}

pub fn evaluate_pos<T>(term_map: &GornTree<Composition<T>>, address: Vec<usize>) -> Composition<T>
where
    T: Clone + fmt::Display,
{
    let unexpanded_composition = term_map.get(&address).unwrap();
    let mut expanded_nonterminals = BTreeMap::new();
    let mut expanded_composition = Vec::new();

    for component in unexpanded_composition {
        let mut expanded_component = Vec::new();

        for variable in component {
            match variable {
                &VarT::Var(num_nonter, num_compon) => {
                    if !expanded_nonterminals.contains_key(&num_nonter) {
                        let mut child_address = address.clone();
                        child_address.push(num_nonter);
                        let nonter_compos = evaluate_pos(term_map, child_address).composition;
                        expanded_nonterminals.insert(num_nonter, nonter_compos);
                    }

                    let nonter_compos = expanded_nonterminals.get(&num_nonter).unwrap();

                    if let Some(compon) = nonter_compos.get(num_compon) {
                        for terminal in compon {
                            expanded_component.push(terminal.clone());
                        }
                    } else {
                        panic!(
                            "{}: use of {}-th component of nonterminal {} that has only {} components!",
                            unexpanded_composition,
                            num_compon,
                            num_nonter,
                            nonter_compos.len()
                        );
                    }
                }
                &VarT::T(ref terminal) => {
                    expanded_component.push(VarT::T(terminal.clone()));
                }
            }
        }

        expanded_composition.push(expanded_component);
    }

    Composition::from(expanded_composition)
}

pub fn to_term<H, T, W>(
    tree_map: &GornTree<PMCFGRule<H, T, W>>,
) -> (GornTree<Composition<T>>, GornTree<H>)
where
    H: Clone,
    T: Clone,
{
    let mut term_map = GornTree::new();
    let mut head_map = GornTree::new();

    for (
        address,
        &PMCFGRule {
            ref head,
            tail: _,
            ref composition,
            weight: _,
        },
    ) in tree_map
    {
        term_map.insert(address.clone(), composition.clone());
        head_map.insert(address.clone(), head.clone());
    }

    (term_map, head_map)
}

#[derive(Copy, Clone, PartialEq, PartialOrd, Eq, Ord, Debug)]
pub enum OldOrNew<T> {
    Old(T), New(T)
}
/// Takes a tree stack _(encoded in a Gorn tree)_ of PMCFG rules of arbitrary form, and transforms
/// it into a tree stack of PMCFG rules of a normal form, requiring each rule to be of one of the
/// following forms:
///
/// * Exactly one terminal symbol and no nonterminal symbols
/// * Arbitrarily many nonterminal symbols and no terminal symbols
///
/// The word that can be derived from the tree stack remains the same after the transformation.
///
/// ```
/// use std::str::FromStr;
/// use rustomata_grammar::pmcfg::{VarT::*, separate_terminal_rules, evaluate, to_term, OldOrNew::*};
/// use rustomata_grammar::pmcfg_rule;
/// use rustomata_util::gorntree::GornTree;
///
/// let mut arbitrary = GornTree::new();
/// arbitrary.insert(vec![], pmcfg_rule!('S' => [[Var(0, 0), Var(0, 1)]] ('A') # 1f64));
/// arbitrary.insert(vec![0], pmcfg_rule!('A' => [[T('a'), Var(0, 0), T('b')], [T('c'), Var(0, 1)]] ('A') # 0.4));
/// arbitrary.insert(vec![0, 0], pmcfg_rule!('A' => [[], []] () # 0.6));
///
/// let mut normal_form = GornTree::new();
/// normal_form.insert(vec![], pmcfg_rule!(Old('S') => [[Var(0, 0), Var(0, 1)]] (Old('A')) # 1f64));
/// normal_form.insert(vec![0], pmcfg_rule!(Old('A') => [[Var(1, 0), Var(0, 0), Var(2, 0)], [Var(3, 0), Var(0, 1)]] (Old('A'), New('a'), New('b'), New('c')) # 0.4));
/// normal_form.insert(vec![0, 0], pmcfg_rule!(Old('A') => [[], []] () # 0.6));
/// normal_form.insert(vec![0, 1], pmcfg_rule!(New('a') => [[T('a')]] () # 0.4));
/// normal_form.insert(vec![0, 2], pmcfg_rule!(New('b') => [[T('b')]] () # 0.4));
/// normal_form.insert(vec![0, 3], pmcfg_rule!(New('c') => [[T('c')]] () # 0.4));
///
/// assert_eq!(
///     &normal_form,
///     &separate_terminal_rules(&arbitrary)
/// );
/// assert_eq!(
///     evaluate(&(to_term(&normal_form).0)),
///     evaluate(&(to_term(&arbitrary).0))
/// );
/// ```
pub fn separate_terminal_rules<HT, W>(
    tree_map: &GornTree<PMCFGRule<HT, HT, W>>,
) -> GornTree<PMCFGRule<OldOrNew<HT>, HT, W>>
where
    HT: Clone + Eq + Hash,
    W: Clone,
{
    use self::OldOrNew::*;
    let mut new_tree = GornTree::new();
    let mut old_heads = Vec::new();

    for (
        _,
        &PMCFGRule {
            ref head,
            tail: _,
            composition: _,
            weight: _,
        },
    ) in tree_map
    {
        old_heads.push(head.clone());
    }

    for (
        address,
        &PMCFGRule {
            ref head,
            ref tail,
            ref composition,
            ref weight,
        },
    ) in tree_map
    {
        let mut next_child_num = tail.len()..;
        let mut terminal_child_num = HashMap::new();
        let mut terminal_children = Vec::new();
        let mut new_composition = Vec::new();
        let mut first_variable = true;
        let mut contains_only_one_terminal = false;

        for component in composition {
            let mut new_component = Vec::new();

            for variable in component {
                match variable {
                    &VarT::Var(num_nonter, num_compon) => {
                        new_component.push(VarT::Var(num_nonter, num_compon));
                    }
                    &VarT::T(ref terminal) => {
                        contains_only_one_terminal = first_variable;

                        let child_num = if terminal_child_num.contains_key(terminal) {
                            *terminal_child_num.get(terminal).unwrap()
                        } else {
                            let number = next_child_num.next().unwrap();
                            terminal_child_num.insert(terminal.clone(), number);
                            terminal_children.push(terminal.clone());
                            number
                        };

                        new_component.push(VarT::Var(child_num, 0));
                    }
                }

                first_variable = false;
            }

            new_composition.push(new_component);
        }

        let new_rule = if contains_only_one_terminal {
            assert!(tail.is_empty());
            PMCFGRule {
                head: Old(head.clone()),
                tail: vec![],
                composition: composition.clone(),
                weight: weight.clone(),
            }
        } else {
            let mut unique_terminal_children = Vec::new();

            for terminal in terminal_children {
                let original_terminal = terminal.clone();

                // while old_heads.contains(&terminal) {
                //     terminal.extend(vec![original_terminal.clone()]);
                // }

                unique_terminal_children.push(New(terminal.clone()));

                let mut child_address = address.clone();
                child_address.push(*terminal_child_num.get(&original_terminal).unwrap());
                new_tree.insert(
                    child_address,
                    PMCFGRule {
                        head: New(terminal),
                        tail: Vec::new(),
                        composition: Composition::from(vec![vec![VarT::T(original_terminal)]]),
                        weight: weight.clone(),
                    },
                );
            }

            let new_tail = tail.iter().cloned().map(|nt| Old(nt)).chain(unique_terminal_children).collect();

            PMCFGRule {
                head: Old(head.clone()),
                tail: new_tail,
                composition: Composition::from(new_composition),
                weight: weight.clone(),
            }
        };

        new_tree.insert(address.clone(), new_rule);
    }

    new_tree
}

#[cfg(test)]
mod tests {
    use self::VarT::{Var, T};
    use self::OldOrNew::{Old, New};
    use super::*;
    use crate::pmcfg_rule;

    pub fn example_tree_map() -> GornTree<PMCFGRule<char, char, usize>> {
        let mut tree_map = GornTree::new();

        tree_map.insert(
            vec![],
            pmcfg_rule!('S' => [[Var(0, 0), Var(1, 0), Var(0, 1), Var(1, 1)]] ('A', 'B') # 1),
        );
        tree_map.insert(
            vec![0],
            pmcfg_rule!('A' => [[Var(1, 0), Var(0, 0)], [Var(2, 0), Var(0, 1)]] ('A', 'a', 'c') # 1),
        );
        tree_map.insert(
            vec![0, 0],
            pmcfg_rule!('A' => [[Var(1, 0), Var(0, 0)], [Var(2, 0), Var(0, 1)]] ('A', 'a', 'c') # 1),
        );
        tree_map.insert(
            vec![0, 0, 0],
            pmcfg_rule!('A' => [[], []] () # 1)
        );
        tree_map.insert(
            vec![0, 0, 1],
            pmcfg_rule!('a' => [[T('a')]] () # 1),
        );
        tree_map.insert(
            vec![0, 0, 2],
            pmcfg_rule!('c' => [[T('c')]] () # 1),
        );
        tree_map.insert(
            vec![0, 1],
            pmcfg_rule!('a' => [[T('a')]] () # 1),
        );
        tree_map.insert(
            vec![0, 2],
            pmcfg_rule!('c' => [[T('c')]] () # 1),
        );
        tree_map.insert(
            vec![1],
            pmcfg_rule!('B' => [[Var(1, 0), Var(0, 0)], [Var(2, 0), Var(0, 1)]] ('B', 'b', 'd') # 1),
        );
        tree_map.insert(
            vec![1, 0],
            pmcfg_rule!('B' => [[], []] () # 1)
        );
        tree_map.insert(
            vec![1, 1],
            pmcfg_rule!('b' => [[T('b')]] () # 1),
        );
        tree_map.insert(
            vec![1, 2],
            pmcfg_rule!('d' => [[T('d')]] () # 1),
        );

        tree_map
    }

    #[test]
    fn test_evaluate() {
        let tree_map = example_tree_map();
        let mut term_map = GornTree::new();

        for (
            address,
            PMCFGRule {
                head: _,
                tail: _,
                composition,
                weight: _,
            },
        ) in tree_map
        {
            term_map.insert(address, composition);
        }

        let expanded_compos = Composition::from(vec![vec![
            T('a'),
            T('a'),
            T('b'),
            T('c'),
            T('c'),
            T('d'),
        ]]);

        assert_eq!(expanded_compos, evaluate(&term_map));
    }

    #[test]
    #[should_panic(
        expected = "[[Var 0 0, Var 0 1]]: use of 1-th component of nonterminal 0 that has only 1 components!"
    )]
    fn test_evaluate_invalid_composition() {
        let mut term_map = GornTree::new();
        term_map.insert(vec![], Composition::from(vec![vec![Var(0, 0), Var(0, 1)]]));
        term_map.insert(vec![0], Composition::from(vec![vec![T('a')]]));

        evaluate(&term_map);
    }

    #[test]
    fn test_to_term() {
        let mut tree_map: GornTree<PMCFGRule<char, char, usize>> = GornTree::new();

        tree_map.insert(
            vec![],
            pmcfg_rule!('A' => [[Var(0, 0), T('a'), Var(0, 1), T('b')]] ('B') # 1)
        );
        tree_map.insert(
            vec![0],
            pmcfg_rule!('B' => [[Var(1, 0)], [T('c')]] ('C') # 1)
        );
        tree_map.insert(
            vec![0, 1],
            pmcfg_rule!('C' => [[], []] () # 1)
        );

        let mut term_map = GornTree::new();
        term_map.insert(
            vec![],
            Composition::from(vec![vec![Var(0, 0), T('a'), Var(0, 1), T('b')]]),
        );
        term_map.insert(
            vec![0],
            Composition::from(vec![vec![Var(1, 0)], vec![T('c')]]),
        );
        term_map.insert(vec![0, 1], Composition::from(vec![vec![], vec![]]));

        let mut head_map = GornTree::new();
        head_map.insert(vec![],     'A');
        head_map.insert(vec![0],    'B');
        head_map.insert(vec![0, 1], 'C');

        assert_eq!((term_map, head_map), to_term(&tree_map));
    }

    #[test]
    fn test_to_term_inverse() {
        let tree_map = example_tree_map();
        let (term_map, head_map) = to_term(&tree_map);
        let mut reconstructed_tree_map = GornTree::new();

        for (address, composition) in term_map {
            let head = head_map.get(&address).unwrap().clone();
            reconstructed_tree_map.insert(
                address,
                PMCFGRule {
                    head,
                    tail: vec![],
                    composition,
                    weight: 0,
                },
            );
        }

        for (address, rule) in tree_map {
            let PMCFGRule {
                head: ref orig_head,
                tail: _,
                composition: ref orig_composition,
                weight: _,
            } = rule;
            let &PMCFGRule {
                ref head,
                tail: _,
                ref composition,
                weight: _,
            } = reconstructed_tree_map.get(&address).unwrap();
            assert_eq!(orig_head, head);
            assert_eq!(orig_composition, composition);
        }
    }

    #[test]
    fn test_separate_terminal_rules() {
        let mut tree_map: GornTree<PMCFGRule<char, char, usize>> = GornTree::new();
        tree_map.insert(
            vec![],
            pmcfg_rule!('S' => [[Var(0, 0), T('b'), Var(1, 0), T('d')]] ('A', 'B') # 1)
        );
        tree_map.insert(
            vec![0],
            pmcfg_rule!('A' => [[Var(0, 0)], [T('x')]] ('C') # 1)
        );
        tree_map.insert(
            vec![0, 0],
            pmcfg_rule!('C' => [[T('a')]] () # 1)
        );
        tree_map.insert(vec![1], pmcfg_rule!('B' => [[T('c')]] () # 1));

        let mut separated_control_map: GornTree<PMCFGRule<OldOrNew<char>, char, usize>> = GornTree::new();
        separated_control_map.insert(
            vec![],
            pmcfg_rule!(Old('S') => [[Var(0, 0), Var(2, 0), Var(1, 0), Var(3, 0)]] (Old('A'), Old('B'), New('b'), New('d')) # 1)
        );
        separated_control_map.insert(
            vec![0],
            pmcfg_rule!(Old('A') => [[Var(0, 0)], [Var(1, 0)]] (Old('C'), New('x')) # 1)
        );
        separated_control_map.insert(
            vec![0, 0],
            pmcfg_rule!(Old('C') => [[T('a')]] () # 1)
        );
        separated_control_map.insert(
            vec![0, 1],
            pmcfg_rule!(New('x') => [[T('x')]] () # 1)
        );
        separated_control_map.insert(vec![1], pmcfg_rule!(Old('B') => [[T('c')]] () # 1));
        separated_control_map.insert(vec![2], pmcfg_rule!(New('b') => [[T('b')]] () # 1));
        separated_control_map.insert(vec![3], pmcfg_rule!(New('d') => [[T('d')]] () # 1));

        for (ref address, ref rule) in separate_terminal_rules(&tree_map) {
            assert_eq!(
                (address, separated_control_map.get(address).unwrap()),
                (address, rule,)
            );
        }
    }

    // #[test]
    // fn test_separate_terminal_rules_idempotence() {
    //     let tree_map = example_tree_map();

    //     let separated_tree_map1 = separate_terminal_rules(&tree_map);
    //     assert_eq!(&tree_map, &separated_tree_map1);
    //     let separated_tree_map2 = separate_terminal_rules(&separated_tree_map1);
    //     assert_eq!(&tree_map, &separated_tree_map2);
    // }

    #[test]
    fn test_separate_terminal_rules_conflicting_names() {
        let mut tree_map: GornTree<PMCFGRule<&str, &str, usize>> = GornTree::new();
        tree_map.insert(
            vec![],
            pmcfg_rule!("S" => [[Var(0, 0), T("a"), Var(1, 0), T("b")]] ("a", "b") # 1)
        );
        tree_map.insert(
            vec![0],
            pmcfg_rule!("a" => [[T("b")]] () # 1)
        );
        tree_map.insert(
            vec![1],
            pmcfg_rule!("b" => [[Var(0, 0)]] ("bb") # 1)
        );
        tree_map.insert(
            vec![1, 0],
            pmcfg_rule!("bb" => [[T("c")]] () # 1)
        );

        let mut separated_control_map = GornTree::new();
        separated_control_map.insert(
            vec![],
            pmcfg_rule!(Old("S") => [[Var(0, 0), Var(2, 0), Var(1, 0), Var(3, 0)]] (Old("a"), Old("b"), New("a"), New("b")) # 1)
        );
        separated_control_map.insert(
            vec![0],
            pmcfg_rule!(Old("a") => [[T("b")]] () # 1)
        );
        separated_control_map.insert(
            vec![1],
            pmcfg_rule!(Old("b") => [[Var(0, 0)]] (Old("bb")) # 1)
        );
        separated_control_map.insert(
            vec![1, 0],
            pmcfg_rule!(Old("bb") => [[T("c")]] () # 1)
        );
        separated_control_map.insert(
            vec![2],
            pmcfg_rule!(New("a") => [[T("a")]] () # 1)
        );
        separated_control_map.insert(
            vec![3],
            pmcfg_rule!(New("b") => [[T("b")]] () # 1)
        );

        for (ref address, ref rule) in separate_terminal_rules(&tree_map) {
            assert_eq!(
                (address, separated_control_map.get(address).unwrap()),
                (address, rule,)
            );
        }
    }
}
