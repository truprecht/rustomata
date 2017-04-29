extern crate num_traits;

use std::collections::HashSet;
use std::fmt::Debug;
use std::hash::Hash;
use std::vec::Vec;
use self::num_traits::One;
use self::num_traits::cast::FromPrimitive;

use std::marker::PhantomData;

use automata;
use cfg;
use push_down::{PushDown, PushDownAutomaton, PushDownInstruction};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum PushState<X,Y> {
    Designated,
    Initial,
    Nt(X),
    T(Y),
}

impl<N: Clone + Debug + Ord + PartialEq + Hash,
     T: Clone + Debug + Ord + PartialEq + Hash,
     W: Clone + Debug + Ord + PartialEq + One + FromPrimitive
     > From<cfg::CFG<N, T, W>> for PushDownAutomaton<PushState<N,T>, T, W> {
     fn from(g: cfg::CFG<N, T, W>) -> Self {
        let mut transitions = Vec::new();

        let mut t_buffer= HashSet::new();

        ///creates a Transition for every rule that replaces the nonterminal of the left side with the rightside of the rule
        for r in g.rules.clone(){
            let mut st = Vec::new();
            for v in r.composition.composition{

                match v{
                    cfg::LetterT::Value(x) => {
                        t_buffer.insert(x.clone());
                        st.push(PushState::T(x.clone()));
                    },
                    cfg::LetterT::Label(x) => {
                        st.push(PushState::Nt(x.clone()));
                    },
                }
            }

            transitions.push(
                automata::Transition {
                    _dummy: PhantomData,
                    word: Vec::new(),
                    weight: r.weight.clone(),
                    instruction: PushDownInstruction::Replace {
                        current_val: PushState::Nt(r.head.clone()),
                        new_val: st.clone(),
                    }
                }
            );

        }
        ///creates a transition for every terminal that reads the word
        for t in t_buffer{
            let mut tvec = Vec::new();
            tvec.push(t.clone());
            transitions.push(
                automata::Transition {
                    _dummy: PhantomData,
                    word: tvec.clone(),
                    weight: W::one(),
                    instruction: PushDownInstruction::Pop {
                        current_val: PushState::T(t.clone()),
                    }
                }
            );


        }
        ///creates a transition for the `Initial` symbol to all Nonterminals in `initial` with weight `1/initial.len()`
        let ini_val=1.0/g.initial.len() as f64;
        let ini_weight=W::from_f64(ini_val).unwrap();

        for ini in g.initial{
            let mut tvec = Vec::new();
            tvec.push(PushState::Nt(ini));
            transitions.push(
                automata::Transition {
                    _dummy: PhantomData,
                    word: Vec::new(),
                    weight: ini_weight.clone(),
                    instruction: PushDownInstruction::Replace {
                        current_val: PushState::Initial,
                        new_val: tvec,
                    }
                }
            );
        }

        PushDownAutomaton::new(
            transitions,
            PushDown::new(PushState::Designated, PushState::Initial),
        )
    }
}