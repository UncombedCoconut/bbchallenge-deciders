//! This prover searches for a simpler form of recognizing automaton:
//! Consume the tape on both ends with DFAs. Exclude the symbol `r` under the head (state `f`).
//! When we "meet in the middle", we have a tuple `(qL, f, r, qR)`.
//! We define a subset of these tuples as accepted, subject to the start/halt/closure rules.
//! Searching for useful MitM-DFA recognizers can take forever, so we make a SAT solver do it.
//! This gives a `TapeAutomaton` if we build an NFA from states `nfa_start(f, r)` plus each `qR`.
//! However, it's simpler to hand our DirectProver the left DFA and let it finish.
//!
//! The same DFA-pair/SAT technique was pioneered by others in the bbchallenge community:
//! - Konrad Deka (@djmati1111, https://github.com/colette-b/bbchallenge)
//! - Mateusz Naściszewski (@Mateon1, https://discuss.bbchallenge.org/u/mateon1)

use super::{DirectProver, Prover, ProverOptions};
use crate::core::{DFAState, Machine, Proof, Rule, Side, Symbol, TMState, DFA, SYMBOLS, TM_STATES};
use cat_solver::Solver;
use std::cmp::{max, min};
use std::ops::Range;

// SAT solvers build up to problem definitions in Conjunctive Normal Form (CNF) as follows:
// A *variable* is represented by a positive `i32`. A *literal* is a variable x or its negation -x.
// A *clause* is a the disjunction (OR) of some literals, represented here as a list.
type L = i32;
const TRUE: L = 1; // It's useful to have an always-true literal
const FALSE: L = -TRUE; // ... and its opposite.

// To specify a BFS-ordered DFA (cf. `dfa_iterator.rs`) on each side, we use propositions
// - `dfa_eq(side, q, s, t)` for whether `dfa[side].t[q][s] == t`
// - `dfa_le(side, q, s, t)` for whether `dfa[side].t[q][s] <= t`
// - `tmax_eq(side, qs, t)` for whether the max transition value before `qs` is `t`.
// These propositions get their own variables, except where redundant.
// This lets our clauses encode the ordering conditions and, crucially, "sequential at-most-one"
// constraints for each `dfa.t` value. (See https://www.carstensinz.de/papers/CP-2005.pdf:
// To limit `x` to one value, we encode the rules: `x=k` implies `x≤k` implies `x≤k+1` and `x≠k+1`.)
const FROM_LEFT: usize = 0;
const FROM_RIGHT: usize = 1;
const MAX_FIRST_TRANSITION: DFAState = if cfg!(feature = "fix_zero") { 0 } else { 1 };

/// A prover which searches for "Meet-in-the-Middle DFA" recognizers.
#[derive(Default)]
pub struct MitMDFAProver {
    sizes: [usize; 2],
    dfa_eq_0: [Vec<L>; 2], // [lr][q*SYMBOLS+s] -> base for sequence of dfa_eq(lr, q, s, _) vars.
    dfa_le_0: [Vec<L>; 2], // [lr][q*SYMBOLS+s] -> base for sequence of dfa_le(lr, q, s, _) vars.
    tmax_eq_0: [Vec<L>; 2], // [lr][q*SYMBOLS+s] -> base for sequence of tmax_eq(lr, q, s, _) vars.
}

impl MitMDFAProver {
    fn dfa_range(&self, lr: usize, q: DFAState, s: Symbol) -> Range<DFAState> {
        0..min(
            SYMBOLS as DFAState * q + s as DFAState + MAX_FIRST_TRANSITION + 1,
            self.sizes[lr] as DFAState,
        )
    }

    fn dfa_eq(&self, lr: usize, q: DFAState, s: Symbol, t: DFAState) -> L {
        let r = self.dfa_range(lr, q, s);
        if !r.contains(&t) {
            FALSE
        } else if r.len() == 1 {
            TRUE
        } else if r.len() == 2 && t != r.start {
            -self.dfa_eq(lr, q, s, r.start)
        } else {
            self.dfa_eq_0[lr][q as usize * SYMBOLS + s as usize] + t as L
        }
    }

    fn dfa_le(&self, lr: usize, q: DFAState, s: Symbol, t: DFAState) -> L {
        let r = self.dfa_range(lr, q, s);
        if t <= r.start {
            self.dfa_eq(lr, q, s, t)
        } else if t + 1 < r.end {
            self.dfa_le_0[lr][q as usize * SYMBOLS + s as usize] + t as L
        } else {
            TRUE
        }
    }

    fn tmax_range(&self, lr: usize, qs: usize) -> Range<DFAState> {
        let min_reached = min(qs / SYMBOLS, self.sizes[lr] - 1) as DFAState;
        let unreachable = min(qs + MAX_FIRST_TRANSITION as usize, self.sizes[lr]) as DFAState;
        min_reached..unreachable
    }

    fn tmax_eq(&self, lr: usize, qs: usize, t: DFAState) -> L {
        let r = self.tmax_range(lr, qs);
        if !r.contains(&t) {
            FALSE
        } else if r.len() == 1 {
            TRUE
        } else if r.len() == 2 && t != r.start {
            -self.tmax_eq(lr, qs, r.start)
        } else {
            self.tmax_eq_0[lr][qs] + t as L
        }
    }

    fn accept(&self, ql: DFAState, f: TMState, r: Symbol, qr: DFAState) -> L {
        if (ql, f, r, qr) == (0, 0, 0, 0) {
            FALSE
        } else {
            let (il, ir, nl) = (ql as usize, qr as usize, self.sizes[0]);
            1 + (il + nl * (f as usize + TM_STATES * (r as usize + SYMBOLS * ir))) as L
        }
    }

    fn dfa_eval(&self, solver: &Solver, lr: usize, q: DFAState, s: Symbol) -> DFAState {
        // We have the less-or-equal variables solved, but a linear search is more than fast enough.
        let r = self.dfa_range(lr, q, s);
        for t in r.start..r.end - 1 {
            match solver.value(self.dfa_eq(lr, q, s, t)) {
                Some(true) | None => return t,
                Some(false) => {}
            }
        }
        r.end - 1
    }

    fn init(&mut self, tm: &Machine) -> Solver {
        let mut sat = Solver::new();
        sat.add_clause([TRUE]);
        // DFA transitions:
        for lr in 0..2 {
            for q in 0..(self.sizes[lr] as DFAState) {
                for s in 0..(SYMBOLS as Symbol) {
                    // Outcomes are mutually exclusive.
                    for t in 0..(self.sizes[lr] as DFAState) {
                        sat.add_clause([-self.dfa_eq(lr, q, s, t), self.dfa_le(lr, q, s, t)]);
                        sat.add_clause([-self.dfa_le(lr, q, s, t), self.dfa_le(lr, q, s, t + 1)]);
                        sat.add_clause([-self.dfa_eq(lr, q, s, t + 1), -self.dfa_le(lr, q, s, t)]);
                    }
                    // An outcome occurs.
                    sat.add_clause(self.dfa_range(lr, q, s).map(|t| self.dfa_eq(lr, q, s, t)));
                }
            }
        }
        // Closure conditions:
        for ql in 0..(self.sizes[0] as DFAState) {
            for qr in 0..(self.sizes[1] as DFAState) {
                tm.rules().for_each(|rule| match rule {
                    Rule::Halt { f, r } => sat.add_clause([self.accept(ql, f, r, qr)]),
                    Rule::Move { f, r, w, d, t } => {
                        // If d==Side::R (else symmetric): (s f@r) |- (t@s w), (^ f@r) |- (t@0 w).
                        let (fwd, rev, n_fwd, n_rev, q_fwd, q_rev) = if d == Side::L {
                            (FROM_LEFT, FROM_RIGHT, self.sizes[0], self.sizes[1], ql, qr)
                        } else {
                            (FROM_RIGHT, FROM_LEFT, self.sizes[1], self.sizes[0], qr, ql)
                        };
                        for qs in 0..(n_fwd as DFAState) {
                            for s in 0..(SYMBOLS as Symbol) {
                                for qw in 0..(n_rev as DFAState) {
                                    let (acc_pre, acc_post) = if d == Side::L {
                                        (self.accept(qs, f, r, q_rev), self.accept(q_fwd, t, s, qw))
                                    } else {
                                        (self.accept(q_rev, f, r, qs), self.accept(qw, t, s, q_fwd))
                                    };
                                    sat.add_clause([
                                        -self.dfa_eq(fwd, q_fwd, s, qs),
                                        -self.dfa_eq(rev, q_rev, w, qw),
                                        -acc_post,
                                        acc_pre,
                                    ]);
                                    if q_fwd == 0 && s == 0 && qs == 0 {
                                        sat.add_clause([
                                            -self.dfa_eq(rev, q_rev, w, qw),
                                            -acc_post,
                                            acc_pre,
                                        ]);
                                    }
                                }
                            }
                        }
                    }
                });
            }
        }
        // BFS-ordering, to break symmetries to avoid redundant searches; cf. `dfa_iterator.rs`.
        // (See also a simpler version in z3py by colette-b/@djmati1111:
        // https://github.com/colette-b/bbchallenge/blob/main/sat2_cfl.py#L64 plus chat explanation
        // https://discord.com/channels/960643023006490684/1028746861395316776/1030907938249912431.)

        for lr in 0..2 {
            for q in 0..(self.sizes[lr] as DFAState) {
                for s in 0..(SYMBOLS as Symbol) {
                    let qs = q as usize * SYMBOLS + s as usize;
                    for m in self.tmax_range(lr, qs) {
                        sat.add_clause([-self.tmax_eq(lr, qs, m), self.dfa_le(lr, q, s, m + 1)]);
                        sat.add_clause([
                            -self.tmax_eq(lr, qs, m),
                            -self.dfa_le(lr, q, s, m),
                            self.tmax_eq(lr, qs + 1, m),
                        ]);
                        sat.add_clause([
                            -self.tmax_eq(lr, qs, m),
                            -self.dfa_eq(lr, q, s, m + 1),
                            self.tmax_eq(lr, qs + 1, m + 1),
                        ]);
                    }
                }
            }
        }
        sat
    }
}

impl Prover for MitMDFAProver {
    fn name(&self) -> String {
        format!("mitm_dfa-{}", max(self.sizes[0], self.sizes[1]))
    }

    fn prove(&mut self, tm: &Machine) -> Option<Proof> {
        let mut solver = self.init(tm);
        if solver.solve() == Some(true) {
            let mut dfa = DFA::new(self.sizes[0]);
            for q in 0..dfa.len() {
                for s in 0..SYMBOLS {
                    dfa.t[q][s] = self.dfa_eval(&solver, FROM_LEFT, q as DFAState, s as Symbol);
                }
            }
            DirectProver::complete_unverified(tm, Side::R, dfa)
        } else {
            None
        }
    }
}

impl ProverOptions for MitMDFAProver {
    fn new(depth: usize) -> Self {
        let mut p: MitMDFAProver = Default::default();
        p.sizes.fill(depth);
        let mut used = p.sizes[0] * TM_STATES * SYMBOLS * p.sizes[1]; // accept() vars, overlapping TRUE
        for lr in 0..2 {
            for q in 0..(p.sizes[lr] as DFAState) {
                for s in 0..(SYMBOLS as Symbol) {
                    let qs = q as usize * SYMBOLS + s as usize;
                    let r = p.dfa_range(lr, q, s);
                    p.dfa_eq_0[lr].push(used as L + 1 - r.start as L);
                    used += r.len() - if (1..=2).contains(&r.len()) { 1 } else { 0 };
                    p.dfa_le_0[lr].push(used as L + 1 - (r.start + 1) as L);
                    used += r.len().saturating_sub(2);
                    let r = p.tmax_range(lr, qs);
                    p.tmax_eq_0[lr].push(used as L + 1 - r.start as L);
                    used += r.len() - if (1..=2).contains(&r.len()) { 1 } else { 0 };
                }
            }
        }
        p
    }
}
