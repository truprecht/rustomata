use rustomata_grammar::{
    pmcfg::{PMCFGRule, VarT},
    factorizable::Factorizable
};
use fnv::FnvHashMap;
use integeriser::{HashIntegeriser, Integeriser};
use num_traits::One;
use num_traits::Zero;
use std::{collections::BinaryHeap, default::Default, hash::Hash, mem::replace, ops::Mul};
use vecmultimap::VecMultiMap;

#[cfg(feature = "serialization")]
use serde::{Serialize, Deserialize};

mod chart;
mod estimates;
mod kbest;
mod rulemask;

use crate::{Bracket, BracketContent};
use crate::state_storage::StateStorage;
use crate::result::ParseResult;
use self::chart::{ Chart, FbChart, DenseChart, Dummy, FallbackChart, Fallback };
pub use self::kbest::{ChartIterator, ChartIt, FbChartIt};
pub use self::estimates::SxOutside;
pub use self::rulemask::{Mask, RuleMaskBuilder};

pub type RuleIdT = u32;
pub type StateT = u32;
pub type RangeT = u8;

/// stores a lhs state and weight of a rule
pub type BuRule<W> = (W, StateT);
/// stores rhs states, rule identifier and rule weight for binary rules
pub type TdBinary<W> = (RuleIdT, StateT, StateT, W);
/// stores rhs state, rule identifier and rule weight for chain rules
pub type TdUnary<W> = (RuleIdT, StateT, W);
/// stores rule identifier and weight of a terminal rule
pub type TdNullary<W> = (RuleIdT, W);
/// Stores the following brackets associated with a single (binarized) rule:
/// * outer bracket,
/// * left bracket, and
/// * right bracket;
/// some of them may be BracketContent::Ignore.
pub type TdBrackets = (BracketContent, BracketContent, BracketContent);
/// non-existent integerized state
pub static NOSTATE: u32 = u32::max_value();

/// Stores binarized rules of the context-free approximation of an lcfrs
/// with brackets of the chomsky-schützenberger construction.
/// These rules are stored indexed by left rhs nonterminal (bottom-up) and
/// lhs nonterminal (top-down).
#[derive(Debug)]
#[cfg_attr(feature = "serialization", derive(Serialize, Deserialize))]
pub struct Automaton<T: Eq + Hash, W>(
    // rules indexed by successor nonterminals and terminals for bottom-up processing
    Vec<Vec<(RuleIdT, StateT, BuRule<W>)>>, // binary compatability: left state -> [(right state, action)]
    Vec<Vec<(RuleIdT, BuRule<W>)>>,         // unary wraps: state -> [action]
    FnvHashMap<T, Vec<(RuleIdT, BuRule<W>)>>, // terminals: termial -> [action]
    // rules indexed by lhs nonterminal for top-down processing
    Vec<Vec<TdBinary<W>>>,
    Vec<Vec<TdUnary<W>>>,
    Vec<Vec<TdNullary<W>>>,
    // misc data
    Vec<Vec<(StateT, W, StateT)>>, // mirrored binary compatability map;
    // this is only used for the inside weight
    StateT,          // initial
    Vec<TdBrackets>, // stores the brackets associated with each rule
    // stores states that are not result of binarization
    Vec<bool>
);

/// intermediate representation for states:
/// * either nonterminal with component index,
/// * or unique state indexed by rule, component and position
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum State<Nt> {
    Non(Nt, usize),
    Unique(RuleIdT, usize, usize),
}

impl<T: Eq + Hash, W> Automaton<T, W> {
    /// extracts an `Automaton` from a given grammar with integerized rules
    pub fn from_grammar<'a, N>(
        rules: impl Iterator<Item = (RuleIdT, &'a PMCFGRule<N, T, W>)>,
        init: N,
    ) -> (Self, StateStorage<N>)
    where
        T: 'a + Clone,
        W: 'a + Factorizable + Mul<Output = W> + One + Copy,
        N: 'a + Clone + Hash + Eq,
    {
        use self::BracketContent::*;
        use self::State::*;

        let mut bu_initials: FnvHashMap<T, Vec<(RuleIdT, BuRule<W>)>> = FnvHashMap::default();
        let mut bu_unaries = VecMultiMap::new();
        let mut bu_binaries = VecMultiMap::new();
        let mut td_initials = VecMultiMap::new();
        let mut td_unaries = VecMultiMap::new();
        let mut td_binaries = VecMultiMap::new();
        let mut rule_to_brackets = Vec::new();

        let mut state_integerizer = HashIntegeriser::new();

        for (rule_id, rule) in rules {
            let weight_factors = rule.weight.factorize(rule.composition.len());
            for (component_id, (component, component_weight)) in
                rule.composition.iter().zip(weight_factors).enumerate()
            {
                let component_t = Component(rule_id as u32, component_id as u8);
                let state_i = state_integerizer.integerise(Non(&rule.head, component_id)) as StateT;

                // handle terminal rules and chain rules
                if component.len() == 1 {
                    match component[0] {
                        VarT::T(ref t) => {
                            bu_initials.entry(t.clone()).or_default().push((
                                rule_to_brackets.len() as RuleIdT,
                                (component_weight, state_i),
                            ));
                            td_initials.push_to(
                                state_i as usize,
                                (rule_to_brackets.len() as RuleIdT, component_weight),
                            );
                            rule_to_brackets.push((component_t, Terminal, Ignore));
                        }
                        VarT::Var(i, j) => {
                            let variable_t = Variable(rule_id as u32, i as u8, j as u8);
                            let successor_state_i =
                                state_integerizer.integerise(Non(&rule.tail[i], j)) as StateT;
                            bu_unaries.push_to(
                                successor_state_i as usize,
                                (
                                    rule_to_brackets.len() as RuleIdT,
                                    (component_weight, state_i),
                                ),
                            );
                            td_unaries.push_to(
                                state_i as usize,
                                (
                                    rule_to_brackets.len() as RuleIdT,
                                    successor_state_i,
                                    component_weight,
                                ),
                            );
                            rule_to_brackets.push((component_t, variable_t, Ignore));
                        }
                    }
                }
                // handle rules with multiple nonnterminals
                else {
                    let v1 = component[0].unwrap_var();
                    let v2 = component[1].unwrap_var();
                    let successors = (
                        state_integerizer.integerise(Non(&rule.tail[v1.0], v1.1)) as StateT,
                        state_integerizer.integerise(Non(&rule.tail[v2.0], v2.1)) as StateT,
                    );
                    let vt1 = Variable(rule_id as u32, v1.0 as u8, v1.1 as u8);
                    let vt2 = Variable(rule_id as u32, v2.0 as u8, v2.1 as u8);
                    // set lhs nontermal as target state or create unique
                    // state if there are nontermals left
                    let (mut targetstate, mut outer_t) = if component.len() == 2 {
                        (state_i, component_t)
                    } else {
                        (
                            state_integerizer.integerise(Unique(rule_id, component_id, 0))
                                as StateT,
                            Ignore,
                        )
                    };
                    bu_binaries.push_to(
                        successors.0 as usize,
                        (
                            rule_to_brackets.len() as RuleIdT,
                            successors.1,
                            (component_weight, targetstate),
                        ),
                    );
                    td_binaries.push_to(
                        targetstate as usize,
                        (
                            rule_to_brackets.len() as RuleIdT,
                            successors.0,
                            successors.1,
                            component_weight,
                        ),
                    );
                    rule_to_brackets.push((outer_t, vt1, vt2));
                    // continue for the remaining nonterminals in the same manner
                    for succ_offset in 1..=(component.len() - 2) {
                        let l_successor = targetstate;
                        let v = component[1 + succ_offset].unwrap_var();
                        let vt = Variable(rule_id as u32, v.0 as u8, v.1 as u8);
                        let r_successor =
                            state_integerizer.integerise(Non(&rule.tail[v.0], v.1)) as StateT;
                        if component.len() == 2 + succ_offset {
                            targetstate = state_i;
                            outer_t = component_t;
                        } else {
                            targetstate = state_integerizer.integerise(Unique(
                                rule_id,
                                component_id,
                                succ_offset,
                            )) as StateT;
                            outer_t = Ignore;
                        };
                        bu_binaries.push_to(
                            l_successor as usize,
                            (
                                rule_to_brackets.len() as RuleIdT,
                                r_successor,
                                (W::one(), targetstate),
                            ),
                        );
                        td_binaries.push_to(
                            targetstate as usize,
                            (
                                rule_to_brackets.len() as RuleIdT,
                                l_successor,
                                r_successor,
                                W::one(),
                            ),
                        );
                        rule_to_brackets.push((outer_t, Ignore, vt));
                    }
                }
            }
        }

        let mut q_storage = StateStorage::with_capacity(state_integerizer.size());
        let mut not_binarized = vec![false; state_integerizer.size()];
        for state in state_integerizer.values() {
            if let Non(n, c) = *state {
                not_binarized[state_integerizer.find_key(state).unwrap()] = true;
                q_storage[state_integerizer.find_key(state).unwrap() as u32] = Some((c as u8, n.clone()));
            }
        }

        let binaries = bu_binaries.into_vec_with_size(state_integerizer.size());
        let mut binaries_mirrorred = VecMultiMap::new();
        for (ql, qr, w, q0) in binaries
            .iter()
            .enumerate()
            .flat_map(|(ql, v)| v.iter().map(move |&(_, qr, (w, q0))| (ql, qr, w, q0)))
        {
            binaries_mirrorred.push_to(qr as usize, (ql as StateT, w, q0));
        }
        
        let a = Automaton (
            binaries,
            bu_unaries.into_vec_with_size(state_integerizer.size()),
            bu_initials,
            td_binaries.into_vec_with_size(state_integerizer.size()),
            td_unaries.into_vec_with_size(state_integerizer.size()),
            td_initials.into_vec_with_size(state_integerizer.size()),
            binaries_mirrorred.into_vec_with_size(state_integerizer.size()),
            state_integerizer.integerise(Non(&init, 0)) as StateT,
            rule_to_brackets,
            not_binarized
        );

        (a, q_storage)
    }

    pub fn states(&self) -> usize {
        self.0.len()
    }
}

type CykResult<'a, W> = ParseResult<Chart<W>, Chart<W>>;

impl<'a, W: Copy + Mul<Output=W> + Ord + Zero> CykResult<'a, W> {
    pub fn build_iterator_with_fallback<T>(
        self,
        automaton: &'a Automaton<T, W>,
        beta: usize,
        delta: W,
        filter: Vec<bool>,
        penalty: W
    ) -> ParseResult<ChartIt<'a, W>, FbChartIt<'a, W>>
    where
        T: Eq + Hash,
    {
        match self {
            ParseResult::Ok(chart)
                => ParseResult::Ok(ChartIterator::new(chart, automaton, filter)),
            ParseResult::Fallback(chart)
                => {
                    let chart2 = fill_fallbacks(&chart, automaton, beta, delta, penalty);
                    let mut ci = ChartIterator::new(chart2, automaton, ());
                    ci.set_penalty(penalty);
                    ParseResult::Fallback(ci)
                },
            _ => ParseResult::None
        }
    }

    pub fn build_iterator<T>(
        self,
        automaton: &'a Automaton<T, W>,
        filter: Vec<bool>
    ) -> ParseResult<ChartIt<'a, W>, FbChartIt<'a, W>>
    where
        T: Eq + Hash,
    {
        match self {
            ParseResult::Ok(chart)
                => ParseResult::Ok(ChartIterator::new(chart, automaton, filter)),
            _ => ParseResult::None
        }
    }
}

fn fill_fallbacks<'a, T, W>(
    chart: &Chart<W>,
    automaton: &'a Automaton<T, W>,
    _beta: usize,
    delta: W,
    penalty: W
) -> FbChart<'a, W>
where
    W: Copy + Mul<Output=W> + Ord + Zero,
    T: Hash + Eq
{
    let (n, states, beta) = chart.get_meta();
    let n = n as u8;
    let mut chart2 = DenseChart::new(n as usize, states, beta, FallbackChart::new(penalty, n as usize, &automaton.9));
    let mut heap_of_nonterminals: BinaryHeap<(W, StateT)> = BinaryHeap::with_capacity(beta);

    // copy unary range entries and add fallback entry
    for l in 0..n {
        for (nt, w) in chart.iterate_nont(l, l+1) {
            chart2.add_entry(l, l+1, nt, w);
        }
    }

    // fill bottom-up according to rules and penalty
    for range in 2..=n {
        for l in 0..=n-range {
            let r = l + range;
            let mut i = beta;
            heap_of_nonterminals.clear();

            for mid in (l+1)..r {
                for (lnt, lew) in chart2.iterate_nont(l as u8, mid as u8) {
                    let available_rules = &automaton.0[lnt as usize];
                    heap_of_nonterminals.extend(available_rules.iter().filter_map(
                        |&(_rid, rnt, (ruw, lhs))| {
                            let riw
                                = chart2
                                    .get_weight(mid as u8, r as u8, rnt)?;
                            // let _ = outsides.get(lhs, l, r, n)?;
                            Some((lew * ruw * riw, lhs))
                        },
                    ));
                }
            }
            
            // unary step and insertion into chart
            let mut skip = vec![false; automaton.0.len()];
            let worst_weight = delta.max(penalty) * heap_of_nonterminals.peek().map_or(W::zero(), |&(w, _)| w);
            while let Some((w, q)) = heap_of_nonterminals.pop() {
                if i == 0 || w <= worst_weight { break; }
                if replace(&mut skip[q as usize], true) { continue; }
                
                chart2.add_entry(l as u8, r as u8, q, w);
                heap_of_nonterminals.extend(
                    automaton.1[q as usize]
                        .iter()
                        .map(|&(_rid, (rw, q))| (rw * w, q))
                );
                i -= 1;
            }
        }
    }

    chart2
}

impl<T: Eq + Hash, W: Ord + Mul<Output=W> + Copy + Zero + One> Automaton<T, W> {
    /// implements the CKY algorithm with chain rules
    pub fn fill_chart<M: Mask>(&self, word: &[T], beam: usize, delta: W, outsides: &SxOutside<W>, rule_filter: &M) -> CykResult<W> {
        let n = word.len();
        let nonterminals = self.0.len();

        // contains the constituents ordered by weight
        let mut heap_of_nonterminals: BinaryHeap<(W, StateT)> = BinaryHeap::with_capacity(beam);
        let mut chart: DenseChart<W, Dummy> = DenseChart::new(n, nonterminals, beam, Dummy);

        for range in 1..=n {
            for l in 0..=(n - range) {
                let r = l + range;
                let mut i = beam;

                heap_of_nonterminals.clear();

                // initial predictions for each position in word
                // TODO: force these to be inserted into chart
                if range == 1 {
                    if let Some(initials) = self.2.get(&word[l]) {
                        heap_of_nonterminals.extend(initials.iter().map(|&(_, t)| t));
                    }
                }

                // binary step
                for mid in l + 1..r {
                    for (lnt, lew) in chart.iterate_nont(l as u8, mid as u8) {
                        let available_rules = &self.0[lnt as usize];
                        let cache = (NOSTATE, None);
                        heap_of_nonterminals.extend(available_rules.iter().filter_map(
                            |&(rid, rnt, (ruw, lhs))| {
                                if !rule_filter.lookup(rid) {
                                    return None;
                                }
                                let riw = if cache.0 == rnt {
                                    cache.1
                                } else {
                                    chart.get_weight(mid as u8, r as u8, rnt)
                                }?;
                                let _ = outsides.get(lhs, l, r, n)?;
                                Some((lew * ruw * riw, lhs))
                            },
                        ));
                    }
                }

                // unary step and insertion into chart
                let mut skip = vec![false; self.0.len()];
                let worst_weight = delta * heap_of_nonterminals.peek().map_or(W::zero(), |&(w, _)| w);
                while let Some((w, q)) = heap_of_nonterminals.pop() {
                    if i == 0 || w < worst_weight { break; }
                    if replace(&mut skip[q as usize], true) { continue; }
                    
                    chart.add_entry(l as u8, r as u8, q, w);
                    heap_of_nonterminals.extend(self.1[q as usize].iter().filter_map(
                        |&(rid, (rw, q))| {
                            if !rule_filter.lookup(rid) {
                                return None;
                            }
                            let _ = outsides.get(q, l, r, n)?;
                            Some((rw * w, q))
                        },
                    ));
                    i -= 1;
                }
            }
        }

        if chart.get_weight(0, n as u8, self.7).is_some() {
            ParseResult::Ok(chart)
        } else if chart.has_leaf_entries() {
            ParseResult::Fallback(chart)
        } else {
            ParseResult::None
        }
    }
}
