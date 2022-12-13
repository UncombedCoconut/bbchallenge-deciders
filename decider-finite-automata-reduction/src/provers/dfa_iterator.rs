//! Iterators for DFAs (on alphabet {0,1}), and prefixes (incomplete transition tables) thereof.

use crate::core::{DFAState, DFA};

/// Iterates over possible n-state DFAs, subject to two restrictions:
/// 1. `DFA::check_leading_zeros()` passes
/// 2. The `DFAState` IDs `0..n` make their first appearances in order in the transition table.
///    (In Rust that would be: in `dfa.t.iter().flatten()`.)
///
/// We visit the possible flattened transition tables in lexicographic order.
/// Condition 2 stops us from emitting DFAs which are isomorphic (the same after relabelling).
/// Equivalent form: the DFA must be the first (by lex order) in its isomorphism class.
///
/// The iterator has two flavors. `DFAPrefixIterator` yields once per (nonempty) partially-filled
/// transition table, so long as it's a prefix of a total DFA following rules 1-2.
/// `DFAIterator` yields once per completed DFA.
/// `DFAPrefixIterator` supports an additional method, `skip_current_subtree()`, if the caller
/// is uninterested in DFAs starting with the most recently yielded prefix.
///
/// We DON'T yield references to the DFA -- you try getting Rust's borrow checker to allow that! :)
/// Instead: the dfa is accessible as a field, DFAPrefixIterator yields the changed `(q, b)` index,
/// and DFAIterator yields `()`.
pub struct DFAPrefixIterator {
    /// The DFA under construction.
    pub dfa: DFA,
    /// The DFA has elements `[q][b]` filled in for `2*q+b < qb`.
    qb: usize,
    /// For each qb, `max{dfa.t[q][b] | 2*q+b < qb}`.
    tmax: Vec<DFAState>,
    /// Whether we've been asked to skip everything starting with the current prefix.
    skip_current: bool,
    /// How many transitions' worth of "memory" each state must have.
    mem: usize,
    /// Whether to make an exception for the "mem" requirement where a state may transition only to itself.
    rip: bool,
    /// For each q, a mem-bit word whose LSB is the immediately preceding transition, etc.
    history: Vec<u64>,
}

/// See `DFAPrefixIterator`.
pub struct DFAIterator(pub DFAPrefixIterator);

impl DFAPrefixIterator {
    pub fn new(n: usize, mem: usize, rip: bool) -> Self {
        Self {
            dfa: DFA::new(n),
            qb: 0,
            tmax: vec![0; 2 * n + 1],
            skip_current: false,
            mem,
            rip,
            history: vec![0; n],
        }
    }

    pub fn skip_current_subtree(&mut self) {
        self.skip_current = true;
    }

    fn qb_pair(&self) -> (usize, usize) {
        (self.qb / 2, self.qb % 2)
    }

    fn is_rip_state(&self, q: usize) -> bool {
        self.dfa.t[q][0] == q as DFAState && self.dfa.t[q][1] == q as DFAState
    }
}

impl DFAIterator {
    pub fn new(n: usize) -> Self {
        Self(DFAPrefixIterator::new(n, 0, false))
    }
}

impl Iterator for DFAPrefixIterator {
    type Item = (DFAState, u8);

    fn next(&mut self) -> Option<Self::Item> {
        if !self.rip && (1 << self.mem) > self.dfa.len() {
            return None;
        }
        let m = (self.dfa.len() - 1) as DFAState;
        // If the table wasn't full yet, but we've promised it can be filled, the next prefix
        // is the first extension of the current one.
        if self.qb < 2 * self.dfa.len() && !self.skip_current {
            let (q, b) = self.qb_pair();
            let history = (b as u64 + 2 * self.history[q]) & ((1u64 << self.mem) - 1);
            // Case 1: the next entry must be an unvisited state (thus the first one).
            // That's the case if doing otherwise would close the transition graph, early -- i.e.,
            // states `> tmax[qb]` exist and would become unreachable from ones `<= tmax[qb]`.
            // Case 2: no such restriction, so the lex-next table fills in a 0.
            if self.tmax[self.qb] < m && self.qb == 2 * (self.tmax[self.qb] as usize) + 1 {
                self.dfa.t[q][b] = self.tmax[self.qb] + 1;
            } else {
                self.dfa.t[q][b] = 0 as DFAState;
                while self.dfa.t[q][b] <= self.tmax[self.qb]
                    && self.history[self.dfa.t[q][b] as usize] != history
                    && (!self.rip || self.dfa.t[q][b] < q as DFAState && !self.is_rip_state(q))
                {
                    self.dfa.t[q][b] += 1;
                }
            }
            self.history[self.dfa.t[q][b] as usize] = history;
            self.qb += 1;
            self.tmax[self.qb] = std::cmp::max(self.tmax[self.qb - 1], self.dfa.t[q][b]);
            return Some((q as DFAState, b as u8));
        }
        self.skip_current = false;
        // If instead the table was full, we have to backtrack (or "carry" as we count?)
        // After we backtrack, either incrementing the current transition is the lex-first option,
        // or raising it any further would violate rules 1-2 or exit 0..n - backtrack further if so.
        while self.qb > 1 {
            self.qb -= 1;
            let (q, b) = self.qb_pair();
            let history = (b as u64 + 2 * self.history[q]) & ((1u64 << self.mem) - 1);
            if self.dfa.t[q][b] <= self.tmax[self.qb] && self.dfa.t[q][b] < m {
                self.dfa.t[q][b] += 1;
                while self.dfa.t[q][b] <= self.tmax[self.qb]
                    && self.history[self.dfa.t[q][b] as usize] != history
                    && (!self.rip || self.dfa.t[q][b] < q as DFAState && !self.is_rip_state(q))
                {
                    self.dfa.t[q][b] += 1;
                }
                if self.dfa.t[q][b] > m {
                    continue;
                }
                self.history[self.dfa.t[q][b] as usize] = history;
                self.qb += 1;
                self.tmax[self.qb] = std::cmp::max(self.tmax[self.qb - 1], self.dfa.t[q][b]);
                return Some((q as DFAState, b as u8));
            }
        }
        None
    }
}

impl Iterator for DFAIterator {
    type Item = ();

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let q_max = (self.0.dfa.len() - 1) as DFAState;
            if self.0.next()? == (q_max, 1) {
                return Some(());
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_1_state() {
        // It's actually pretty easy to screw this up. :-)
        let mut it = DFAIterator::new(1);
        assert_eq!(it.next(), Some(()));
        assert_eq!(it.0.dfa.t, [[0, 0]]);
        assert_eq!(it.next(), None);
    }

    #[test]
    fn test_2_states() {
        let mut it = DFAIterator::new(2);
        assert_eq!(it.next(), Some(()));
        assert_eq!(it.0.dfa.t, [[0, 1], [0, 0]]);
        assert_eq!(it.next(), Some(()));
        assert_eq!(it.0.dfa.t, [[0, 1], [0, 1]]);
        assert_eq!(it.next(), Some(()));
        assert_eq!(it.0.dfa.t, [[0, 1], [1, 0]]);
        assert_eq!(it.next(), Some(()));
        assert_eq!(it.0.dfa.t, [[0, 1], [1, 1]]);
        assert_eq!(it.next(), None);
    }

    #[test]
    fn test_skips() {
        let mut it = DFAPrefixIterator::new(3, 0, false);
        assert_eq!(it.next(), Some((0, 0)));
        assert_eq!(it.dfa.t, [[0, 0], [0, 0], [0, 0]]);
        assert_eq!(it.next(), Some((0, 1)));
        assert_eq!(it.dfa.t, [[0, 1], [0, 0], [0, 0]]);
        assert_eq!(it.next(), Some((1, 0)));
        assert_eq!(it.dfa.t, [[0, 1], [0, 0], [0, 0]]);
        it.skip_current_subtree(); // Done with 0, 1, 0, _
        assert_eq!(it.next(), Some((1, 0)));
        assert_eq!(it.dfa.t, [[0, 1], [1, 0], [0, 0]]);
        assert_eq!(it.next(), Some((1, 1)));
        assert_eq!(it.dfa.t, [[0, 1], [1, 2], [0, 0]]);
        it.skip_current_subtree(); // Done with 0, 1, 1, 2, _
        assert_eq!(it.next(), Some((1, 0)));
        assert_eq!(it.dfa.t, [[0, 1], [2, 2], [0, 0]]);
        // This entry here is irrelevant: ^  -- caller may not rely on it being zeroed.
        it.skip_current_subtree(); // Done with 0, 1, 2, _
        assert_eq!(it.next(), None);
    }

    #[test]
    fn test_counts() {
        // Counts of complete 0-insensitive binary DFAs follow https://oeis.org/A107668
        assert_eq!(DFAIterator::new(1).count(), 1);
        assert_eq!(DFAIterator::new(2).count(), 4);
        assert_eq!(DFAIterator::new(3).count(), 45);
        assert_eq!(DFAIterator::new(4).count(), 816);
    }

    #[test]
    fn test_memory() {
        for n in 1..5 {
            for mem in 1..=2 {
                for rip in [false, true] {
                    println!("n={} mem={} rip={}", n, mem, rip);
                    let mut it = DFAPrefixIterator::new(n, mem, rip);
                    while let Some((q, b)) = it.next() {
                        let mut tt = vec![0 as DFAState; 2 * (q as usize) + (b as usize) + 1];
                        for qb in 0..tt.len() {
                            tt[qb] = it.dfa.t[qb / 2][qb % 2];
                        }
                        println!("{:?}", tt);
                    }
                }
            }
        }
    }
}
