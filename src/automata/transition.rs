use std::cmp::Ordering;
use std::ops::Mul;
use std::fmt::{self, Debug, Display};
use std::hash::{Hash, Hasher};

use automata::Instruction;
use automata::Configuration;

/// Transition of an automaton with `weight`, reading the sequence `word`, and applying the `instruction`.
#[derive(Clone, Debug)]
pub struct Transition<I, T, W> {
    pub word: Vec<T>,
    pub weight: W,
    pub instruction: I,
}

impl<I, T, W> Hash for Transition<I, T, W>
    where I: Hash,
          T: Hash,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.word.hash(state);
        self.instruction.hash(state);
    }
}

/// `impl` of `PartialEq` that ignores the `weight` (to conform to the `impl` of `Hash`)
impl<I, T, W> PartialEq for Transition<I, T, W>
    where I: PartialEq,
          T: PartialEq
{
    fn eq(&self, other: &Self) -> bool {
        self.word == other.word && self.instruction == other.instruction
    }
}

impl<I, T, W> Eq for Transition<I, T, W>
    where I: Eq,
          T: Eq
{}

impl<I, T, W> Transition<I, T, W>
    where I: Instruction,
          I::Storage: Clone,
          T: Clone + PartialEq,
          W: Mul<Output = W> + Copy,
{
    pub fn apply(&self, c: &Configuration<I::Storage, T, W>)
                 -> Vec<Configuration<I::Storage, T, W>> {
        if !c.word.starts_with(&self.word[..]) {
            return Vec::new()
        }

        let mut confs = Vec::new();
        for s1 in self.instruction.apply(c.storage.clone()) {
            confs.push(
                Configuration {
                    word: c.word.clone().split_off(self.word.len()),
                    storage: s1,
                    weight: c.weight * self.weight,
                }
            )
        }

        confs
    }
}

impl<I, T, W> PartialOrd for Transition<I, T, W>
    where I: PartialEq,
          T: PartialEq,
          W: Eq + PartialOrd,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self.weight == other.weight {
            self.word.len().partial_cmp(&other.word.len())
        } else {
            self.weight.partial_cmp(&other.weight)
        }
    }
}

impl<I, T, W> Ord for Transition<I, T, W>
    where I: Eq,
          T: Eq,
          W: Eq + Ord
{
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl<I, T, W> Display for Transition<I, T, W>
    where I: Display,
          T: Debug,
          W: Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Transition {:?} {}  # {}", self.word, self.instruction, self.weight)
    }
}
