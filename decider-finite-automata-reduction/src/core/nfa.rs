use super::{row, BadProof, ColVector, Matrix, NFAState, ProofResult, RowVector, Symbol, SYMBOLS};
use serde::{Deserialize, Serialize};

/// A Nondeterministic Finite Automaton, with states indexed by `NFAState`s.
/// During operation, we can track the `RowVector` of possible `NFAState`s it could have.
/// Transition matrices act on these `RowVector`s by right-multiplication.
/// Testing a `RowVector` for acceptance is also matrix multiplication.
/// Reference: https://planetmath.org/matrixcharacterizationsofautomata
#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct NFA {
    pub t: [Matrix; SYMBOLS],
    pub accepted: ColVector,
}

impl NFA {
    /// An NFA with n states (initialized empty transitions and acceptance).
    pub fn new(states: usize) -> NFA {
        NFA {
            t: core::array::from_fn(|_| Matrix::new(states)),
            accepted: ColVector::new(),
        }
    }

    /// The number of states.
    pub fn len(&self) -> usize {
        self.t[0].len()
    }

    /// The outcomes of a single step, from a precise state.
    pub fn step(&self, q: NFAState, s: Symbol) -> RowVector {
        self.step_vec(row(q), s)
    }

    /// The outcomes of a single step, from any state in a vector.
    pub fn step_vec(&self, v: RowVector, s: Symbol) -> RowVector {
        v * &self.t[s as usize]
    }

    /// Ensure the data define a valid NFA.
    pub fn validate(&self) -> ProofResult<()> {
        self.accepted.validate(self.len())?;
        if self.t.iter().any(|t| t.len() != self.len()) {
            Err(BadProof::BadDimensions)
        } else {
            self.t.iter().try_for_each(|m| m.validate())
        }
    }

    /// Check the assumption that `v` is an "accepted steady state", meaning:
    /// - if the NFA currently reaches all states in `v` (`state >= v`), this remains true after
    ///   either transition (`state * &self.t[s] >= v` for each symbol `s`).
    /// - in a state where all of `v` is reachable, the NFA will accept.
    pub fn check_accepted_steady_state(&self, v: RowVector) -> ProofResult<()> {
        v.validate(self.len())?;
        if !(v * self.accepted) {
            Err(BadProof::RejectedSteadyState)
        } else if !(0..SYMBOLS).all(|s| v * &self.t[s] >= v) {
            Err(BadProof::BadSteadyState)
        } else {
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_validation() {
        let nfa = NFA::new(1);
        assert_eq!(nfa.len(), 1);
        assert_eq!(nfa.validate(), Ok(()));
        let nfa: NFA = serde_json::from_str(r#"{"t":[[0],[0]],"accepted":0}"#).unwrap();
        assert_eq!(nfa.validate(), Ok(()));
        let nfa: NFA = serde_json::from_str(r#"{"t":[[0],[0,0]],"accepted":0}"#).unwrap();
        assert_eq!(nfa.validate(), Err(BadProof::BadDimensions));
        let nfa: NFA = serde_json::from_str(r#"{"t":[[4],[2]],"accepted":0}"#).unwrap();
        assert_eq!(nfa.validate(), Err(BadProof::BadVector));
    }

    #[test]
    fn test_check_accepted_steady_state() {
        // Set up a 4-state NFA where reading (b) transitions (q) to (q^b), and state 0 is accepted.
        let nfa: NFA = serde_json::from_str(r#"{"t":[[1,2,4,8],[2,1,8,4]],"accepted":1}"#).unwrap();
        let good = nfa.check_accepted_steady_state(row(0) | row(1));
        let trash = nfa.check_accepted_steady_state(row(7));
        let reject = nfa.check_accepted_steady_state(row(2) | row(3));
        let escapee = nfa.check_accepted_steady_state(row(0));
        assert_eq!(good, Ok(()));
        assert_eq!(trash, Err(BadProof::BadVector));
        assert_eq!(reject, Err(BadProof::RejectedSteadyState));
        assert_eq!(escapee, Err(BadProof::BadSteadyState));
    }

    #[test]
    fn test_step() {
        // Same 4-state NFA where reading (b) transitions (q) to (q^b):
        let nfa: NFA = serde_json::from_str(r#"{"t":[[1,2,4,8],[2,1,8,4]],"accepted":1}"#).unwrap();
        for i in 0..4 as NFAState {
            for b in 0..2u8 {
                assert_eq!(nfa.step(i, b), row(i ^ b));
                assert_eq!(nfa.step_vec(row(0) | row(1), b), row(0) | row(1));
            }
        }
    }
}
