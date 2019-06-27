mod automaton;
mod cowderiv;
mod state_storage;
pub mod result;

use super::Lcfrs;
use state_storage::StateStorage;

use crate::dyck::Bracket;
use crate::pmcfg::PMCFGRule;
use crate::factorizable::Factorizable;
use rustomata_util::gorntree::GornTree;
use num_traits::{One, Zero};
use std::time::{Duration, Instant};
use std::{
    collections::BTreeMap,
    fmt::{Display, Error, Formatter},
    hash::Hash,
    ops::Mul,
};

use self::automaton::{Automaton, SxOutside, RuleMaskBuilder, ChartIt, FbChartIt};

/// The indices of a bracket in a CS representation for an lcfrs.
/// Assumes integerized an itergerized set of (at most 2^32) rules and fanouts
/// and arities ≤ 2^8.
#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug, PartialOrd, Ord, Serialize, Deserialize)]
pub enum BracketContent {
    /// We construe `Ignore` as a parenthesis without index; it is introduced
    /// for binarization.
    Ignore,
    // store fallback rule application
    // unary from state 0 to state 1
    Fallback(u32, u32),
    /// We do not store the specific terminal as bracket index.
    Terminal,
    Component(u32, u8),
    Variable(u32, u8, u8),
}

impl BracketContent {
    #[inline(always)]
    pub fn is_ignore(self) -> bool {
        match self {
            BracketContent::Ignore => true,
            _ => false,
        }
    }
}

type Delta = Bracket<BracketContent>;

impl Display for BracketContent {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        match *self {
            BracketContent::Component(rule_id, comp_id) => write!(f, "_{}^{}", rule_id, comp_id),
            BracketContent::Variable(rule_id, i, j) => write!(f, "_{{{},{}}}^{}", rule_id, i, j),
            BracketContent::Terminal => write!(f, "_{{TERM}}"),
            _ => Ok(()),
        }
    }
}

/// A C-S representation of a grammar.
#[derive(Debug, Serialize, Deserialize)]
pub struct CSRepresentation<N, T, W>
where
    T: Eq + Hash,
{
    generator: Automaton<T, W>,
    estimates: SxOutside<W>,
    rulemaskbuilder: RuleMaskBuilder<T>,
    rules: Vec<PMCFGRule<N, T, W>>,
    init: N,
    states: StateStorage<N>,

}

pub struct GeneratorBuilder<'a, N, T: Eq + Hash, W> {
    grammar: &'a CSRepresentation<N, T, W>,
    candidates: Option<usize>,
    beam: usize,
    delta: W,
    root_prediction: bool,
    fallback_penalty: W
}

/// A parse result containing either an iterator over all found parse
/// trees, a single fallback (pseudo) parse tree or nothing.
pub type ParseResult<N, T, W, I>
    = self::result::ParseResult<I, GornTree<PMCFGRule<N, T, W>>>;
/// A parse result containing either the best parse tree and
/// the number of enumerated candidates, a fallback (pseudo) parse tree
/// and the number of enumerated candidates or nothing.
pub type DebugResult<N, T, W>
    = self::result::ParseResult<(GornTree<PMCFGRule<N, T, W>>, usize), (GornTree<PMCFGRule<N, T, W>>, usize)>;

impl<'a, N, T, W> GeneratorBuilder<'a, N, T, W>
where
    T: Eq + Hash + Clone,
    W: Zero + Ord + Copy + One + Mul<Output=W>,
    N: Clone
{
    pub fn set_candidates(&mut self, c: usize) { self.candidates = Some(c); }
    pub fn set_beam(&mut self, b: usize) { self.beam = b; }
    pub fn set_delta(&mut self, d: W) { self.delta = d; }
    pub fn allow_root_prediction(&mut self) { self.root_prediction = true; }
    pub fn set_fallback_penalty(&mut self, fp: W) { self.fallback_penalty = fp; }

    fn trees(
        &self,
        word: &[T]
    ) -> self::result::ParseResult<ChartIt<'a, W>, FbChartIt<'a, W>>
    {
        let &Self { grammar, beam, delta, .. } = self;
        let filter = grammar.rulemaskbuilder.build(word);
        let cyk_result = grammar.generator.fill_chart(word, beam, delta, &grammar.estimates, &filter);
        if self.root_prediction {
            cyk_result.build_iterator_with_fallback(&self.grammar.generator, beam, delta, filter, self.fallback_penalty)
        } else {
            cyk_result.build_iterator(&self.grammar.generator, filter)
        }
    }

    pub fn parse(&'a self, word: &[T]) -> ParseResult<N, T, W, impl 'a + Iterator<Item=GornTree<&'a PMCFGRule<N, T, W>>>> {
        use self::result::ParseResult::*;
        let mut candidates = self.candidates;
        match self.trees(word) {
            None => None,
            Fallback(mut it) => {
                let word = it.next().unwrap();
                let fallbacktree = cowderiv::FallbackCowDerivation::new(&word).fallback(&self.grammar.rules, &self.grammar.states);
                Fallback(fallbacktree)
            }
            Ok(it) => {
                let count_candidates = move |_: &Vec<Delta>| -> bool {
                    candidates.as_mut().map_or(true, |c| if *c == 0 { false } else { *c -= 1; true } )
                };
                let mut pit = it.peekable();
                let firstword = pit.peek().unwrap().clone();
                let mut rest = pit.take_while(count_candidates)
                                  .filter_map(move |bs| self.grammar.toderiv(&bs))
                                  .peekable();
                if rest.peek().is_some() {
                    Ok(rest)
                } else {
                    Fallback(cowderiv::CowDerivation::new(&firstword).fallback(&self.grammar.rules))
                }
            }
        }
    }

    pub fn debug(&self, word: &[T]) -> (usize, usize, Duration, DebugResult<N, T, W>) {
        use self::result::ParseResult::*;
        let starting_time = Instant::now();

        let mut candidates = self.candidates;
        let debug_result = match self.trees(word) {
            None => None,
            Fallback(mut it) => {
                let word = it.next().unwrap();
                let fallbacktree = cowderiv::FallbackCowDerivation::new(&word);
                Fallback((fallbacktree.fallback(&self.grammar.rules, &self.grammar.states), 1))
            }
            Ok(it) => {
                let count_candidates = move |_: &Vec<Delta>| -> bool {
                    candidates.as_mut().map_or(true, |c| if *c == 0 { false } else { *c -= 1; true } )
                };
                let mut pit = it.peekable();
                let firstword = pit.peek().unwrap().clone();
                let mut enumerated_words = 0;
                let mut rest = pit.take_while(count_candidates)
                                  .filter_map(move |bs| { enumerated_words += 1; self.grammar.toderiv(&bs) })
                                  .peekable();
                if rest.peek().is_some() {
                    Ok((rest.next().unwrap().cloned(), enumerated_words))
                } else {
                    Fallback((cowderiv::CowDerivation::new(&firstword).fallback(&self.grammar.rules), enumerated_words))
                }
            }
        };
        
        ( self.grammar.rules.len()
        , word.len()
        , starting_time.elapsed()
        , debug_result
        )
    }
}

impl<N, T, W> CSRepresentation<N, T, W>
where
    T: Ord + Hash + Clone,
    W: Ord + Copy + One + Mul<Output = W>,
    N: Clone,
{
    /// Instantiates a CS representation for an `LCFRS`.
    pub fn new<M>(grammar: M, estimates_max_width: usize) -> Self
    where
        M: Into<Lcfrs<N, T, W>>,
        W: Factorizable + Zero,
        N: Hash + Eq,
    {
        assert!(estimates_max_width <= u8::max_value() as usize);
        let (rules, initial) = grammar.into().destruct();
        let (generator, states) = {
            let rules_with_id = rules.iter().enumerate().map(|(i, r)| (i as u32, r));
            Automaton::from_grammar(rules_with_id, initial.clone())
        };
        let rulemaskbuilder = RuleMaskBuilder::new(rules.iter(), &initial);
        let estimates = SxOutside::from_automaton(&generator, estimates_max_width as u8);
        
        CSRepresentation { generator, states, rulemaskbuilder, estimates, rules, init: initial }
    }

    pub fn build_generator(&self) -> GeneratorBuilder<N, T, W>
    where
        W: Zero,
    {
        GeneratorBuilder {
            grammar: self,
            beam: self.generator.states(),
            delta: W::zero(),
            candidates: None,
            root_prediction: false,
            fallback_penalty: W::zero()
        }
    }
}

impl<N, T, W> CSRepresentation<N, T, W>
where
    T: Hash + Eq
{
    /// Reads off a parse tree from a multiple Dyck word. Fails if the word is not in R ∩ D.
    fn toderiv<'a>(&'a self, word: &[Delta]) -> Option<GornTree<&'a PMCFGRule<N, T, W>>> {
        let mut tree = BTreeMap::new();
        let mut pos = Vec::new();

        for sigma in word {
            match *sigma {
                Bracket::Open(BracketContent::Component(rule_id, _)) => {
                    let rule_at_pos = tree.entry(pos.clone()).or_insert(rule_id);
                    if rule_at_pos != &rule_id {
                        return None;
                    }
                },
                Bracket::Open(BracketContent::Fallback(_, _)) => {
                    let rule_at_pos = tree.entry(pos.clone()).or_insert(u32::max_value());
                    if rule_at_pos != &u32::max_value() {
                        return None;
                    }
                },
                Bracket::Open(BracketContent::Variable(_, i, _)) => {
                    pos.push(i as usize);
                },
                Bracket::Close(BracketContent::Variable(_, _, _)) => {
                    pos.pop();
                },
                _ => (),
            }
        }

        Some(
            tree.into_iter()
                .map(|(pos, i)| (pos, &self.rules[i as usize]))
                .collect(),
        )
    }
}

#[cfg(test)]
mod test {
    use super::{CSRepresentation, Lcfrs};
    use rustomata_grammars::pmcfg::{Composition, PMCFGRule, VarT};
    use log_domain::LogDomain;

    #[test]
    fn csrep() {
        let grammar = lcfrs();
        let d1 = vec![(vec![], &grammar.rules[1])].into_iter().collect();
        let d2 = vec![
            (vec![], &grammar.rules[0]),
            (vec![0], &grammar.rules[1]),
            (vec![1], &grammar.rules[1]),
        ].into_iter()
            .collect();

        let cs = CSRepresentation::new(grammar.clone(), 0);
        let gen = cs.build_generator();
        assert_eq!(gen.parse(&['A']).as_option().unwrap().next(), Some(d1));
        assert_eq!(
            gen.parse(&['A', 'A']).as_option().unwrap().next(),
            Some(d2)
        );
    }

    fn lcfrs() -> Lcfrs<&'static str, char, LogDomain<f64>> {
        Lcfrs {
            init: "S",
            rules: vec![
                PMCFGRule {
                    head: "S",
                    tail: vec!["S", "S"],
                    composition: Composition {
                        composition: vec![vec![VarT::Var(0, 0), VarT::Var(1, 0)]],
                    },
                    weight: LogDomain::new(0.3f64).unwrap(),
                },
                PMCFGRule {
                    head: "S",
                    tail: vec![],
                    composition: Composition {
                        composition: vec![vec![VarT::T('A')]],
                    },
                    weight: LogDomain::new(0.7f64).unwrap(),
                },
            ],
        }
    }
}
