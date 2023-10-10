use super::{
    row, BadProof, DFAState, Machine, NFAState, ProofResult, RowVector, Rule, Side, Symbol,
    TMState, DFA, NFA, SYMBOLS, TM_STATES,
};
use serde::{Deserialize, Serialize};

/// An automaton for recognizing a subset of TM tape+head configurations, operating as follows:
#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct TapeAutomaton {
    /// It scans the visited part of the tape from end to the end, moving in "direction".
    /// (Thus, any TM transition moves either in or opposite the scanning direction.)
    pub direction: Side,
    /// Phase 1: deterministic scan of the syms from the first visited cell to the head (exclusive).
    pub dfa: DFA,
    /// Phase 2: from any `DFAState` q", if it sees the symbol for TMState "f", it transitions
    /// to a unique corresponding NFA state given by the function `nfa_start(q, f)`.
    /// Phase 3: non-deterministic scan from the sym under the head to the last unvisited cell.
    pub nfa: NFA,
}

/// The state in which the `TapeAutomaton` starts its NFA phase, if it saw head "f" in DFAState "q".
pub fn nfa_start(q: DFAState, f: TMState) -> NFAState {
    (q as usize * TM_STATES + f as usize) as NFAState
}

impl TapeAutomaton {
    /// A `TapeAutomaton` definition (yet to be validated).
    pub fn new(direction: Side, dfa: DFA, nfa: NFA) -> TapeAutomaton {
        TapeAutomaton {
            direction,
            dfa,
            nfa,
        }
    }

    /// Ensure the `TapeAutomaton` satisfies the invariants described in the class doc comments.
    pub fn validate(&self) -> ProofResult<()> {
        self.dfa.validate()?;
        self.nfa.validate()?;
        if self.nfa.len() < TM_STATES * self.dfa.len() {
            Err(BadProof::BadNFASize)
        } else {
            Ok(())
        }
    }
}

/// A certificate that a Turing Machine runs forever from its initial configuration.
#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct Proof {
    /// A TapeAutomaton with the property that, if it accepts a configuration after a TM step,
    /// it accepts the preceding configuration as well.
    /// Furthermore, we require that it rejects the initial TM configuration.
    pub automaton: TapeAutomaton,
    /// To ensure the TapeAutomaton accepts each immediately-halting configurations, we require:
    /// whenever phase 3 starts with the head state-symbol and sym from a halt rule, the NFA must
    /// reach the following accepted steady state. (cf. `NFA::check_accepted_steady_state()`.)
    pub steady_state: RowVector,
}

impl Proof {
    /// A purported proof that `tm` is non-halting -- validate()` confirms if it works.
    pub fn new(direction: Side, dfa: DFA, nfa: NFA, steady_state: RowVector) -> Proof {
        Proof {
            automaton: TapeAutomaton::new(direction, dfa, nfa),
            steady_state,
        }
    }

    /// Ensure the `Proof` satisfies the invariants described in the class doc comments.
    /// (Thus, no sequence of TM steps can lead from the starting TM configuration to a halt!)
    pub fn validate(&self, tm: &Machine) -> ProofResult<()> {
        self.automaton.validate()?;
        self.automaton
            .nfa
            .check_accepted_steady_state(self.steady_state)?;
        if row(nfa_start(0, 0)) * self.automaton.nfa.accepted {
            Err(BadProof::BadStart)
        } else {
            tm.rules().try_for_each(|rule| {
                (0..self.automaton.dfa.len() as DFAState).try_for_each(|q| {
                    if self.closed(0, &rule) {
                        Ok(())
                    } else {
                        Err(BadProof::NotClosed {
                            q,
                            rule: rule.clone(),
                        })
                    }
                })
            })
        }
    }

    fn closed(&self, q: DFAState, rule: &Rule) -> bool {
        let a = &self.automaton;
        let (fwd, dfa, nfa, acc) = (a.direction, &a.dfa, &a.nfa, a.nfa.accepted);
        match *rule {
            Rule::Halt { f, r } => {
                nfa.step(nfa_start(q, f), r) >= self.steady_state
                    && (r != 0 || row(nfa_start(q, f)) * acc)
            }
            Rule::Move { f, r, w, d, t } => {
                if d == fwd {
                    nfa.step(nfa_start(q, f), r) >= row(nfa_start(dfa.step(q, w), t))
                        && (r != 0
                            || row(nfa_start(q, f)) * acc
                                >= row(nfa_start(dfa.step(q, w), t)) * acc)
                } else {
                    (0..SYMBOLS as Symbol).all(|s| {
                        nfa.step(nfa_start(dfa.step(q, s), f), r)
                            >= nfa.step_vec(nfa.step(nfa_start(q, t), s), w)
                            && (r != 0
                                || row(nfa_start(dfa.step(q, s), f)) * acc
                                    >= nfa.step_vec(nfa.step(nfa_start(q, t), s), w) * acc)
                    }) && (q != 0
                        || nfa.step(nfa_start(q, f), r)
                            >= nfa.step_vec(nfa.step(nfa_start(q, t), 0), w))
                        && (q != 0
                            || r != 0
                            || row(nfa_start(q, f)) * acc
                                >= nfa.step_vec(nfa.step(nfa_start(q, t), 0), w) * acc)
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::{col, ColVector, Matrix};
    use std::str::FromStr;

    #[test]
    fn test_simple_proof() {
        // Check a proof for https://bbchallenge.org/1
        let tm = Machine::from_str("1RB---_0RC---_0RD---_0RE---_0LE1RB").unwrap();
        let mut proof: Proof = serde_json::from_str(
            r#"{
                "automaton": {
                    "direction": "R",
                    "dfa": [[0, 0]],
                    "nfa": {"accepted": 32, "t": [[2, 4, 8, 16, 28, 32], [32, 32, 32, 32, 2, 32]]}},
                "steady_state": 32}"#,
        )
        .unwrap();
        assert_eq!(proof.validate(&tm), Ok(()));
        // Corrupted proof data is rejected:
        proof.automaton.dfa.t[0][0] = 42;
        assert_eq!(proof.validate(&tm), Err(BadProof::BadDFATransition));
        proof.automaton.dfa.t[0][0] = 0;
        proof.automaton.nfa.t[0][0] = row(7);
        assert_eq!(proof.validate(&tm), Err(BadProof::BadVector));
        proof.automaton.nfa.t[0][0] = row(1);

        proof.automaton.nfa.accepted = col(7);
        assert_eq!(proof.validate(&tm), Err(BadProof::BadVector));
        proof.automaton.nfa.accepted = ColVector::from_iter(0..6);
        assert_eq!(proof.validate(&tm), Err(BadProof::BadStart));
        proof.automaton.nfa.accepted = col(5);

        proof.steady_state = row(7);
        assert_eq!(proof.validate(&tm), Err(BadProof::BadVector));
        proof.steady_state = row(0) | row(5);
        assert_eq!(proof.validate(&tm), Err(BadProof::BadSteadyState));
        proof.steady_state = RowVector::new();
        assert_eq!(proof.validate(&tm), Err(BadProof::RejectedSteadyState));
        // ... and complete demolition from here on out:
        proof.automaton.nfa.accepted = ColVector::new();
        proof.automaton.nfa.t[1] = Matrix::new(1);
        assert_eq!(proof.validate(&tm), Err(BadProof::BadDimensions));
        proof.automaton.nfa.t[0] = Matrix::new(1);
        assert_eq!(proof.validate(&tm), Err(BadProof::BadNFASize));
        proof.automaton.dfa.t.clear();
        assert_eq!(proof.validate(&tm), Err(BadProof::BadDFASize));
    }

    #[test]
    fn test_nontrivial_mirrored_proof() {
        // Check a proof for https://bbchallenge.org/12345
        let tm = Machine::from_str("1RB---_0RC---_1RD0RD_0LD1LE_1LC0LB").unwrap();
        let mut proof: Proof = serde_json::from_str(
            r#"{
                "automaton": {
                    "direction": "L",
                    "dfa": [[0, 1], [1, 1]],
                    "nfa": {
                        "accepted": 1056,
                        "t": [
                            [384, 128, 512, 8, 128, 1984, 968, 576, 256, 128, 1024],
                            [1024, 1024, 8, 512, 2, 1024, 1024, 384, 512, 64, 1024]
                        ]}},
                "steady_state": 1024}"#,
        )
        .unwrap();
        assert_eq!(proof.validate(&tm), Ok(()));
        // The non-trivial closure properties are also checked:
        proof.automaton.dfa.t[0][0] = 1;
        assert_eq!(
            proof.validate(&tm),
            Err(BadProof::NotClosed {
                q: 0,
                rule: Rule::Move {
                    f: 2,
                    r: 1,
                    w: 0,
                    d: Side::R,
                    t: 3
                }
            })
        );
        proof.automaton.dfa.t[0][0] = 0;

        proof.automaton.nfa.t[1][0] = row(0);
        assert_eq!(
            proof.validate(&tm),
            Err(BadProof::NotClosed {
                q: 0,
                rule: Rule::Halt { f: 0, r: 1 }
            })
        );
        proof.automaton.nfa.t[1][0] = row(10);

        proof.automaton.nfa.t[0][4] = row(0);
        assert_eq!(
            proof.validate(&tm),
            Err(BadProof::NotClosed {
                q: 0,
                rule: Rule::Move {
                    f: 4,
                    r: 0,
                    w: 1,
                    d: Side::L,
                    t: 2
                }
            })
        );
        proof.automaton.nfa.t[0][4] = row(7);

        proof.automaton.nfa.t[0][1] |= row(0);
        assert_eq!(
            proof.validate(&tm),
            Err(BadProof::NotClosed {
                q: 0,
                rule: Rule::Move {
                    f: 0,
                    r: 0,
                    w: 1,
                    d: Side::R,
                    t: 1
                }
            })
        );
    }
}
