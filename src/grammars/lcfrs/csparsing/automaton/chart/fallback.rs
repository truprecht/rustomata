use super::{chart_size, index, RangeT, StateT};
use num_traits::Zero;

/// This trait generalizes a structure storing a fallback weight for
/// each span in a word.
pub trait Fallback<W> {
    /// type of an iterator over fallback weights
    type It: Iterator<Item = (StateT, W)>;
    /// inserts a fallback weight for a span if there's none stored
    fn insert(&mut self, i: RangeT, j: RangeT, q: StateT, weight: W);
    /// returns fallback weight and viterbi-best state per span
    fn get(&self, i: RangeT, j: RangeT, q: StateT) -> Option<(StateT, W)>;
    /// iterates over all states with nonzero fallback weight
    fn iterate_nont(&self, i: RangeT, j: RangeT) -> Self::It;
}

/// This struct does not store anything at all.
pub struct Dummy;

impl<W> Fallback<W> for Dummy {
    type It = std::iter::Empty<(StateT, W)>;
    fn insert(&mut self, _: RangeT, _: RangeT, _: StateT, _: W) {}
    fn get(&self, _: RangeT, _: RangeT, _: StateT) -> Option<(StateT, W)> {
        None
    }
    fn iterate_nont(&self, _: RangeT, _: RangeT) -> Self::It {
        std::iter::empty()
    }
}

/// Implements an iterator over all states with nonzero fallback weight.
pub struct FallbackIt<'a, W> {
    weight: Option<W>,
    admissable_states: &'a [bool],
    next: usize,
}

impl<'a, W: Copy> Iterator for FallbackIt<'a, W> {
    type Item = (StateT, W);
    fn next(&mut self) -> Option<Self::Item> {
        let w = self.weight?;
        let offset = self.admissable_states[self.next..]
            .iter()
            .enumerate()
            .filter_map(|(o, b)| if *b { Some(o) } else { None })
            .next()?;
        self.next += offset + 1;
        Some((self.next as StateT - 1, w))
    }
}

impl<'a, W: Copy + std::ops::Mul<Output = W> + PartialEq + Zero> Fallback<W>
    for FallbackChart<'a, W>
{
    type It = FallbackIt<'a, W>;
    fn insert(&mut self, i: RangeT, j: RangeT, q: StateT, weight: W) {
        self.insert(i, j, q, weight);
    }
    fn get(&self, i: RangeT, j: RangeT, q: StateT) -> Option<(StateT, W)> {
        self.get(i, j, q)
    }
    fn iterate_nont(&self, i: RangeT, j: RangeT) -> Self::It {
        FallbackIt {
            weight: self.get_unchecked(i, j),
            admissable_states: self.admissable_states,
            next: 0,
        }
    }
}

#[derive(Debug, Clone)]
pub struct FallbackChart<'a, W> {
    fallback_per_span: Vec<(StateT, W)>,
    fallback_penalty: W,
    admissable_states: &'a [bool],
    n: usize,
}

impl<'a, W: Zero> FallbackChart<'a, W> {
    pub fn new(fallback_penalty: W, n: usize, admissable_states: &'a [bool]) -> Self
    where
        W: Copy,
    {
        let fallback_per_span = vec![(0, W::zero()); chart_size(n)];

        Self {
            fallback_penalty,
            n,
            admissable_states,
            fallback_per_span,
        }
    }

    fn insert(&mut self, i: RangeT, j: RangeT, q: StateT, weight: W)
    where
        W: Copy + std::ops::Mul<Output = W> + PartialEq,
    {
        let entry = &mut self.fallback_per_span[index(i, j, self.n)];

        if self.admissable_states[q as usize] && entry.1 == W::zero() {
            *entry = (q, weight * self.fallback_penalty);
        }
    }

    fn get_unchecked(&self, i: RangeT, j: RangeT) -> Option<W>
    where
        W: Copy + PartialEq,
    {
        let w = self.fallback_per_span[index(i, j, self.n)].1;
        if w != W::zero() {
            Some(w)
        } else {
            None
        }
    }

    fn get(&self, i: RangeT, j: RangeT, q: StateT) -> Option<(StateT, W)>
    where
        W: Copy + PartialEq,
    {
        let (s, w) = self.fallback_per_span[index(i, j, self.n)];
        if self.admissable_states[q as usize] && w != W::zero() {
            Some((s, w))
        } else {
            None
        }
    }
}
