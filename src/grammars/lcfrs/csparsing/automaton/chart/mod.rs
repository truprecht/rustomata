use super::{RangeT, StateT};
use num_traits::Zero;

mod fallback;

pub use fallback::{Dummy, Fallback, FallbackChart};

pub type Chart<W> = DenseChart<W, Dummy>;
pub type FbChart<'a, W> = DenseChart<W, FallbackChart<'a, W>>;

/// A chart for cfg parsing.
#[derive(Debug, Clone)]
pub struct DenseChart<W, F>(
    Vec<u16>,         // no. of saved nonterminals per span
    Vec<(StateT, W)>, // nonterminals with viterbi weigh per span (max <beam> entries)
    Vec<W>,           // viterbi weight per span and nonterminal
    usize,            // n
    usize,            // states
    u16,              // max no. of constituents per span
    F,
);

pub fn chart_size(n: usize) -> usize {
    n * (n + 1) / 2
}
pub fn chart_size_with_states(n: usize, states: usize) -> usize {
    n * (n + 1) * states / 2
}

pub fn index(i: RangeT, j: RangeT, n: usize) -> usize {
    let (i, j) = (i as usize, j as usize);
    (n * (n + 1) - (n - (j - i) + 1) * (n - (j - i) + 2)) / 2 + i
}
pub fn index_with_state(i: RangeT, j: RangeT, q: StateT, n: usize, states: usize) -> usize {
    let (i, j, q) = (i as usize, j as usize, q as usize);
    ((n * (n + 1) - (n - (j - i) + 1) * (n - (j - i) + 2)) / 2 + i) * states + q
}

impl<W, F> DenseChart<W, F> {
    /// Allocates the whole space needed for the chart.
    /// All data structures are initialized with zeroes.
    pub fn new(n: usize, states: usize, bt_per_cell: usize, f: F) -> Self
    where
        W: Copy + Zero,
    {
        assert!(bt_per_cell <= u16::max_value() as usize);
        DenseChart(
            vec![0; chart_size(n)],
            vec![(0, W::zero()); chart_size(n) * bt_per_cell],
            vec![W::zero(); chart_size_with_states(n, states)],
            n,
            states,
            bt_per_cell as u16,
            f,
        )
    }

    /// Gives information about the size of the chart. Returns n, the state
    /// count and the beam width.
    pub fn get_meta(&self) -> (usize, usize, usize) {
        (self.3, self.4, self.5 as usize)
    }

    // pub fn add_fallback(&mut self, i: RangeT, j: RangeT, q: StateT, weight: W) {
    //     self.6[index(i, j, self.3)] = (q, weight);
    // }

    pub fn get_best(&self, i: RangeT, j: RangeT) -> Option<(StateT, W)>
    where
        W: Copy + PartialEq + Zero,
    {
        let index = index(i, j, self.3) * self.5 as usize;
        let (state, w) = self.1[index];
        if w == W::zero() {
            None
        } else {
            Some((state, w))
        }
    }

    pub fn has_leaf_entries(&self) -> bool
    where
        W: Copy + PartialEq + Zero,
    {
        (0..self.3 as u8).all(|i| self.get_best(i, i + 1).is_some())
    }
}

impl<W, F: fallback::Fallback<W>> DenseChart<W, F> {
    /// Adds a constituent with viterbi weight to a span.
    pub fn add_entry(&mut self, i: RangeT, j: RangeT, state: StateT, weight: W)
    where
        W: Copy + PartialEq + Zero,
    {
        let tri_index = index(i, j, self.3);
        let nts = &mut self.0[tri_index];
        debug_assert!(*nts < self.5);

        self.1[tri_index * self.5 as usize + *nts as usize] = (state, weight);
        self.2[tri_index * self.4 + state as usize] = weight;
        *nts += 1;
        self.6.insert(i, j, state, weight);
    }

    pub fn get_fallback(&self, i: RangeT, j: RangeT, q: StateT) -> Option<(StateT, W)>
    where
        W: Zero + PartialEq,
    {
        self.6.get(i, j, q)
    }

    /// Gets weight for specific constituent and span.
    pub fn get_weight(&self, i: RangeT, j: RangeT, q: StateT) -> Option<W>
    where
        W: Copy + PartialEq + Zero,
    {
        let w = self.2[index_with_state(i, j, q, self.3, self.4)];
        if w == W::zero() {
            self.6.get(i, j, q).map(|(_, w)| w)
        } else {
            Some(w)
        }
    }

    pub fn get_weight_without_fallback(&self, i: RangeT, j: RangeT, q: StateT) -> Option<W>
    where
        W: Copy + PartialEq + Zero,
    {
        let w = self.2[index_with_state(i, j, q, self.3, self.4)];
        if w == W::zero() {
            None
        } else {
            Some(w)
        }
    }

    /// Iterates all constituents for a span.
    /// Constituents that are only directly reachable via a fallback mechanism
    /// are chained, so some constituents might be repeated.
    pub fn iterate_nont<'a>(
        &'a self,
        i: RangeT,
        j: RangeT,
    ) -> impl 'a + Iterator<Item = (StateT, W)>
    where
        W: Copy,
    {
        let tri_index = index(i, j, self.3);
        let first_index = tri_index * self.5 as usize;
        let last_index = first_index + self.0[tri_index] as usize;
        self.1[first_index..last_index]
            .iter()
            .cloned()
            .chain(self.6.iterate_nont(i, j))
    }
}
