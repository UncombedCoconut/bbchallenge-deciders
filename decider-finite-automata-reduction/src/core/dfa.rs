use super::{BadProof, DFAState, ProofResult, Symbol, SYMBOLS};
use serde::{Deserialize, Serialize};

/// A Deterministic Finite Automaton, with states indexed by ``DFAState`s and initial state 0.
#[derive(Serialize, Deserialize, Clone, Debug)]
#[serde(transparent)]
pub struct DFA {
    pub t: Vec<[DFAState; SYMBOLS]>,
}

impl DFA {
    /// A DFA with n states (initialized with all transitions leading to the initial state).
    pub fn new(n: usize) -> DFA {
        DFA {
            t: vec![[0; SYMBOLS]; n],
        }
    }

    /// The number of states.
    pub fn len(&self) -> usize {
        self.t.len()
    }

    /// The outcome of a single step.
    pub fn step(&self, q: DFAState, s: Symbol) -> DFAState {
        self.t[q as usize][s as usize]
    }

    /// Ensure the data define a valid DFA.
    pub fn validate(&self) -> ProofResult<()> {
        if self.t.is_empty() {
            Err(BadProof::BadDFASize)
        } else if self.t.iter().flatten().any(|&v| (v as usize) >= self.len()) {
            Err(BadProof::BadDFATransition)
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
        let dfa = DFA::new(1);
        assert_eq!(dfa.validate(), Ok(()));
        let dfa: DFA = serde_json::from_str("[[0, 1], [0, 2], [0, 0]]").unwrap();
        assert_eq!(dfa.validate(), Ok(()));
        let dfa: DFA = serde_json::from_str("[]").unwrap();
        assert_eq!(dfa.validate(), Err(BadProof::BadDFASize));
        let dfa: DFA = serde_json::from_str("[[0, 42]]").unwrap();
        assert_eq!(dfa.validate(), Err(BadProof::BadDFATransition));
    }

    #[test]
    fn test_step() {
        // Again, all looping transitions except 0->1 when reading '0':
        let dfa: DFA = serde_json::from_str("[[1, 0], [1, 1]]").unwrap();
        assert_eq!(dfa.step(0, 0), 1);
        assert_eq!(dfa.step(0, 1), 0);
        assert_eq!(dfa.step(1, 0), 1);
        assert_eq!(dfa.step(1, 0), 1);
    }
}
