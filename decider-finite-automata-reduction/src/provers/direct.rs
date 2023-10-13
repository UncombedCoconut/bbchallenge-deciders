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
//! If we only know it through a fixed `(q, s)`, we can still compute the minimal NFA satisfying
//! the closure criteria we know about. This might already accept `nfa_start(0, 0)`, in which case
//! we needn't bother to complete the DFA; otherwise, we've at least made progress building the NFA.

use super::{DFAPrefixIterator, Prover, ProverOptions};
use crate::core::{
    col, nfa_start, row, DFAState, Machine, NFAState, Proof, Rule, Side, Symbol, DFA, NFA, SYMBOLS,
    TM_STATES,
};

/// A prover which attempts a direct search for a `TapeAutomaton` meeting the proof criteria.
/// If one exists with at most `depth` DFA states, the prover will find it.
pub struct DirectProver {
    /// The DFA size to use.
    depth: usize,
    /// If using the "sink heuristic": expect a state <= this bound to transition only to itself.
    max_sink_state: usize,
}

impl Prover for DirectProver {
    fn name(&self) -> String {
        format!("direct-{}", self.depth)
    }

    fn prove(&mut self, tm: &Machine) -> Option<Proof> {
        self.prove_side(tm, Side::R).or_else(|| self.prove_side(tm, Side::L))
    }
}

impl ProverOptions for DirectProver {
    fn new(depth: usize) -> Self {
        let max_sink_state = SYMBOLS.pow(depth.ilog(SYMBOLS));
        DirectProver { depth, max_sink_state }
    }
}

impl DirectProver {
    /// The basic algorithm: try to complete a `TapeAutomaton` from the deterministic part.
    pub fn complete_unverified(tm: &Machine, direction: Side, dfa: DFA) -> Option<Proof> {
        let mut nfa = NFA::new(dfa.len() * TM_STATES + 1);
        let halt = (dfa.len() * TM_STATES) as NFAState;
        Self::init(&dfa, &mut nfa, tm, halt);
        for q_new in 0..dfa.len() as DFAState {
            for s_new in 0..(SYMBOLS as Symbol) {
                Self::saturate(&dfa, &mut nfa, tm, direction, q_new, s_new);
            }
        }
        let steady_state = row(halt);
        Some(Proof::new(direction, dfa, nfa, steady_state))
    }

    /// Try to return a Proof for `tm`, given the choice of scan direction.
    fn prove_side(&mut self, tm: &Machine, direction: Side) -> Option<Proof> {
        let mut dfas = DFAPrefixIterator::new(self.depth);
        let mut nfas = vec![NFA::new(self.depth * TM_STATES + 1); SYMBOLS * self.depth + 1];
        let mut initial_non_sink_states = 0;
        let halt = (TM_STATES * self.depth) as NFAState;
        Self::init(&dfas.dfa, &mut nfas[0], tm, halt);
        loop {
            let (q_new, s_new) = dfas.next()?;
            let ply = (SYMBOLS as Symbol * q_new + s_new + 1) as usize;
            nfas[ply] = nfas[ply - 1].clone();
            if cfg!(feature = "sink_heuristic") {
                // Heuristic: Nearly all solutions have a "sink state" transitioning only to itself,
                // typically recognizing a pattern the TM never writes in its infinite lifetime.
                // Our DFAs are ordered breadth-first, so one may assume one of the first ~SYMBOLS^k
                // states should find one. This saves A LOT of time and, when wrong, can be fixed
                // by a higher-depth search. The exact threshold was chosen empirically and saves
                // far more time than it loses on higher-depth re-searches.
                initial_non_sink_states = std::cmp::min(initial_non_sink_states, q_new as usize);
                if initial_non_sink_states == q_new as usize
                    && (dfas.dfa.t[initial_non_sink_states][0] != q_new
                        || s_new == 1 && dfas.dfa.t[initial_non_sink_states][1] != q_new)
                {
                    initial_non_sink_states += 1;
                }
                if initial_non_sink_states > self.max_sink_state {
                    dfas.skip_current_subtree();
                    continue;
                }
            }
            Self::saturate(&dfas.dfa, &mut nfas[ply], tm, direction, q_new, s_new);
            if row(nfa_start(0, 0)) * nfas[ply].accepted {
                dfas.skip_current_subtree();
                continue;
            }
            if ply + 1 == nfas.len() {
                let steady_state = row(halt);
                let nfa = nfas[ply].clone();
                return Some(Proof::new(direction, dfas.dfa, nfa, steady_state));
            }
            if cfg!(feature = "fix_zero") && ply == 1 && dfas.dfa.t[0][0] > 0 {
                return None;
            }
        }
    }

    /// Initialize the NFA from the halt rules, which are independent of our DFA choices.
    fn init(dfa: &DFA, nfa: &mut NFA, tm: &Machine, halt: NFAState) {
        nfa.accepted = col(halt);
        for s in 0..SYMBOLS {
            nfa.t[s][halt] = row(halt);
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
    /// given that `dfa` is known up to the `(q_new, s_new)` transition.
    /// The closure conditions for Move rules in the direction opposite our scan direction
    /// depend on the allowed NFA transitions, so this process repeats until there's nothing new.
    fn saturate(dfa: &DFA, nfa: &mut NFA, tm: &Machine, fwd: Side, q_new: DFAState, s_new: Symbol) {
        tm.rules().for_each(|rule| match rule {
            Rule::Move { f, r, w, d, t } if d == fwd && w == s_new => {
                nfa.t[r as usize][nfa_start(q_new, f)] |= row(nfa_start(dfa.step(q_new, w), t));
            }
            _ => {}
        });
        loop {
            let mut grew = false;
            tm.rules().for_each(|rule| match rule {
                Rule::Move { f, r, w, d, t } if d != fwd => {
                    for q in 0..=q_new {
                        for s in 0..(SYMBOLS as Symbol) {
                            if (q, s) <= (q_new, s_new) {
                                let q2 = dfa.step(q, s);
                                let t_r_q2 = nfa.t[r as usize][nfa_start(q2, f)];
                                let new = nfa.step_vec(nfa.step(nfa_start(q, t), s), w);
                                nfa.t[r as usize][nfa_start(q2, f)] |= new;
                                grew |= nfa.t[r as usize][nfa_start(q2, f)] != t_r_q2;
                                if q == 0 && s == 0 {
                                    let t_r_0 = nfa.t[r as usize][nfa_start(0, f)];
                                    let new = nfa.step_vec(nfa.step(nfa_start(0, t), 0), w);
                                    nfa.t[r as usize][nfa_start(0, f)] |= new;
                                    grew |= nfa.t[r as usize][nfa_start(0, f)] != t_r_0;
                                }
                            }
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
