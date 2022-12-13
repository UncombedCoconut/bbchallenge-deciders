//! This prover searches directly for a successful `TapeAutomaton`.
//! The depth parameter controls the DFA size.
//! As `../README.md` explains, we know an NFA only needs `(depth*TM_STATES+1)` states:
//! `nfa_start(q, f)` as defined in proof.rs, plus a special HALT state.
//! HALT is automatically an "accepted steady state", suggesting the following `Proof` search:
//! pick a direction, then pick a DFA, then construct the minimal NFA (in terms of added transitions
//! and accepted states) satisfying the closure conditions in proof.rs.
//! The search has succeeded iff  the NFA rejects `nfa_start(0, 0)`.
//! This is a powerful algorithm already, but now let's look closer:
//! When we "pick a DFA", we're building the transition table incrementally.
//! If we only know it through a fixed `(q, b)`, we can still compute the minimal NFA satisfying
//! the closure criteria we know about. This might already accept `nfa_start(0, 0)`, in which case
//! we needn't bother to complete the DFA; otherwise, we've at least made progress building the NFA.

use super::{DFAPrefixIterator, Prover, ProverOptions};
use crate::core::{
    col, nfa_start, row, DFAState, Machine, NFAState, Proof, Rule, Side, DFA, NFA, TM_STATES,
};

/// A prover which attempts a direct search for a `TapeAutomaton` meeting the proof criteria.
/// If one exists with at most `depth` DFA states, the prover will find it.
pub struct MemProver<const MEM: usize, const RIP: bool> {
    /// The DFA size to use.
    depth: usize,
}

impl<const MEM: usize, const RIP: bool> Prover for MemProver<MEM, RIP> {
    fn name(&self) -> String {
        if MEM == 0 {
            format!("direct-{}", self.depth)
        } else if RIP {
            format!("mem{}_rip-{}", MEM, self.depth)
        } else {
            format!("mem{}-{}", MEM, self.depth)
        }
    }

    fn prove(&mut self, tm: &Machine) -> Option<Proof> {
        self.prove_side(tm, Side::R)
            .or_else(|| self.prove_side(tm, Side::L))
    }
}

impl<const MEM: usize, const RIP: bool> ProverOptions for MemProver<MEM, RIP> {
    fn new(depth: usize) -> Self {
        Self { depth }
    }
}

impl<const MEM: usize, const RIP: bool> MemProver<MEM, RIP> {
    /// The basic algorithm: try to complete a `TapeAutomaton` from the deterministic part.
    pub fn complete_unverified(tm: &Machine, direction: Side, dfa: DFA) -> Option<Proof> {
        let mut nfa = NFA::new(dfa.len() * TM_STATES + 1);
        let halt = (dfa.len() * TM_STATES) as NFAState;
        Self::init(&dfa, &mut nfa, tm, halt);
        for q_new in 0..dfa.len() as DFAState {
            for b_new in 0..2 {
                Self::saturate(&dfa, &mut nfa, tm, direction, q_new, b_new);
            }
        }
        let steady_state = row(halt);
        Some(Proof::new(direction, dfa, nfa, steady_state))
    }

    /// Try to return a Proof for `tm`, given the choice of scan direction.
    fn prove_side(&mut self, tm: &Machine, direction: Side) -> Option<Proof> {
        let mut dfas = DFAPrefixIterator::new(self.depth, MEM, RIP);
        let mut nfas = vec![NFA::new(self.depth * TM_STATES + 1); 2 * self.depth];
        let halt = (TM_STATES * self.depth) as NFAState;
        loop {
            let (q_new, b_new) = dfas.next()?;
            let ply = (2 * q_new + b_new) as usize;
            if ply == 0 {
                Self::init(&dfas.dfa, &mut nfas[0], tm, halt);
            } else {
                nfas[ply] = nfas[ply - 1].clone();
            }
            Self::saturate(&dfas.dfa, &mut nfas[ply], tm, direction, q_new, b_new);
            if row(nfa_start(0, 0)) * nfas[ply].accepted {
                dfas.skip_current_subtree();
                continue;
            }
            let steady_state = row(halt);
            let nfa = nfas[ply].clone();
            if (q_new as usize, b_new) == (self.depth - 1, 1) {
                return Some(Proof::new(direction, dfas.dfa, nfa, steady_state));
            }
        }
    }

    /// Initialize the NFA from the halt rules, which are independent of our DFA choices.
    fn init(dfa: &DFA, nfa: &mut NFA, tm: &Machine, halt: NFAState) {
        nfa.accepted = col(halt);
        for b in 0..2 {
            nfa.t[b][halt] = row(halt);
        }
        tm.rules().for_each(|rule| {
            if let Rule::Halt { f, r } = rule {
                for q in 0..dfa.len() {
                    nfa.t[r as usize][nfa_start(q as NFAState, f)] |= row(halt);
                }
            }
        })
    }

    /// Update `nfa` with all transitions and acceptances required by the closure conditions,
    /// given that `dfa` is known up to the `(q_new, b_new)` transition.
    /// The closure conditions for Move rules in the direction opposite our scan direction
    /// depend on the allowed NFA transitions, so this process repeats until there's nothing new.
    fn saturate(dfa: &DFA, nfa: &mut NFA, tm: &Machine, a_dir: Side, q_new: DFAState, b_new: u8) {
        tm.rules().for_each(|rule| match rule {
            Rule::Move { f, r, w, d, t } if d == a_dir && w == b_new => {
                nfa.t[r as usize][nfa_start(q_new, f)] |= row(nfa_start(dfa.step(q_new, w), t));
            }
            _ => {}
        });
        loop {
            let mut grew = false;
            tm.rules().for_each(|rule| match rule {
                Rule::Move { f, r, w, d, t } if d != a_dir => {
                    'qb: for q in 0.. {
                        for b in 0..2 {
                            if (q, b) > (q_new, b_new) {
                                break 'qb;
                            }
                            let q2 = dfa.step(q, b);
                            let t_r_q2 = nfa.t[r as usize][nfa_start(q2, f)];
                            let new = nfa.step_vec(nfa.step(nfa_start(q, t), b), w);
                            nfa.t[r as usize][nfa_start(q2, f)] |= new;
                            grew |= nfa.t[r as usize][nfa_start(q2, f)] != t_r_q2;
                        }
                    }
                }
                _ => {}
            });
            if !grew {
                break;
            }
        }
        loop {
            let old = nfa.accepted;
            nfa.accepted |= &nfa.t[0] * nfa.accepted;
            if nfa.accepted == old {
                break;
            }
        }
    }
}

pub type DirectProver = MemProver<0, false>;
