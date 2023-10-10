//! Iterators for DFAs, and prefixes (incomplete transition tables) thereof.

use crate::core::{DFAState, Symbol, DFA, SYMBOLS};

/// Iterates over possible n-state, BFS-ordered DFAs: that is, DFAs such that a breadth-first
/// search of states from the initial one (taking the edges/transitions in tape-alphabetical order)
/// visits them in order. This is a symmetry-breaking condition, to prevent redundant searches of
/// isomorphic DFAs.
///
/// As it constructs the `dfa.t[q][s]` entries in lex order, the iterator yields the pair `(q, s)`.
/// The caller may skip all extensions of the current partial DFA by calling `skip_current_subtree`.
pub struct DFAPrefixIterator {
    /// The DFA under construction.
    pub dfa: DFA,
    /// The DFA has elements `[q][s]` filled in for `SYMBOLS*q+s < qs`.
    qs: usize,
    /// For each qs, `max{{0} U {dfa.t[q][s] | SYMBOLS*q+s < qs})`.
    tmax: Vec<DFAState>,
    /// Whether we've been asked to skip everything starting with the current prefix.
    skip_current: bool,
}

impl DFAPrefixIterator {
    pub fn new(n: usize) -> Self {
        Self {
            dfa: DFA::new(n),
            qs: 0,
            tmax: vec![0; SYMBOLS * n + 1],
            skip_current: false,
        }
    }

    pub fn skip_current_subtree(&mut self) {
        self.skip_current = true;
    }

    fn qs_pair(&self) -> (usize, usize) {
        (self.qs / SYMBOLS, self.qs % SYMBOLS)
    }
}

impl Iterator for DFAPrefixIterator {
    type Item = (DFAState, Symbol);

    fn next(&mut self) -> Option<Self::Item> {
        let m = (self.dfa.len() - 1) as DFAState;
        // If the table wasn't full yet, but we've promised it can be filled, the next prefix
        // is the first extension of the current one.
        if self.qs < SYMBOLS * self.dfa.len() && !self.skip_current {
            let (q, s) = self.qs_pair();
            // Case 1: the next entry must be an unvisited state (thus the first one).
            // That's the case if doing otherwise would close the transition graph, early -- i.e.,
            // states `> tmax[qs]` exist and would become unreachable from ones `<= tmax[qs]`.
            // Case 2: no such restriction, so the lex-next table fills in a 0.
            if self.tmax[self.qs] < m && self.qs == SYMBOLS * (self.tmax[self.qs] as usize) + 1 {
                self.dfa.t[q][s] = self.tmax[self.qs] + 1;
            } else {
                self.dfa.t[q][s] = 0 as DFAState;
            }
            self.qs += 1;
            self.tmax[self.qs] = std::cmp::max(self.tmax[self.qs - 1], self.dfa.t[q][s]);
            return Some((q as DFAState, s as Symbol));
        }
        self.skip_current = false;
        // If instead the table was full, we have to backtrack (or "carry" as we count?)
        // After we backtrack, either incrementing the current transition is the lex-first option,
        // or it's not an option and we must backtrack further.
        while self.qs > 0 {
            self.qs -= 1;
            let (q, s) = self.qs_pair();
            if self.dfa.t[q][s] <= self.tmax[self.qs] && self.dfa.t[q][s] < m {
                self.dfa.t[q][s] += 1;
                self.qs += 1;
                self.tmax[self.qs] = std::cmp::max(self.tmax[self.qs - 1], self.dfa.t[q][s]);
                return Some((q as DFAState, s as Symbol));
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_1_state() {
        // It's actually pretty easy to screw this up. :-)
        let mut it = DFAPrefixIterator::new(1);
        assert_eq!(it.next(), Some((0, 0)));
        assert_eq!(it.dfa.t, [[0, 0]]);
        assert_eq!(it.next(), Some((0, 1)));
        assert_eq!(it.dfa.t, [[0, 0]]);
        assert_eq!(it.next(), None);
    }

    #[test]
    fn test_2_states() {
        let mut it = DFAPrefixIterator::new(2);
        let expected: [(DFAState, Symbol, [[DFAState; 2]; 2]); 23] = [
            (0, 0, [[0, 0], [0, 0]]),
            (0, 1, [[0, 1], [0, 0]]),
            (1, 0, [[0, 1], [0, 0]]),
            (1, 1, [[0, 1], [0, 0]]),
            (1, 1, [[0, 1], [0, 1]]),
            (1, 0, [[0, 1], [1, 1]]),
            (1, 1, [[0, 1], [1, 0]]),
            (1, 1, [[0, 1], [1, 1]]),
            (0, 0, [[1, 1], [1, 1]]),
            (0, 1, [[1, 0], [1, 1]]),
            (1, 0, [[1, 0], [0, 1]]),
            (1, 1, [[1, 0], [0, 0]]),
            (1, 1, [[1, 0], [0, 1]]),
            (1, 0, [[1, 0], [1, 1]]),
            (1, 1, [[1, 0], [1, 0]]),
            (1, 1, [[1, 0], [1, 1]]),
            (0, 1, [[1, 1], [1, 1]]),
            (1, 0, [[1, 1], [0, 1]]),
            (1, 1, [[1, 1], [0, 0]]),
            (1, 1, [[1, 1], [0, 1]]),
            (1, 0, [[1, 1], [1, 1]]),
            (1, 1, [[1, 1], [1, 0]]),
            (1, 1, [[1, 1], [1, 1]]),
        ];
        for (q, s, dfa) in expected {
            assert_eq!(it.next(), Some((q, s)));
            assert_eq!(it.dfa.t, dfa);
        }
        assert_eq!(it.next(), None);
    }

    #[test]
    fn test_skips() {
        let mut it = DFAPrefixIterator::new(3);
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
        assert_eq!(it.next(), Some((0, 0)));
        it.skip_current_subtree(); // Done with 1, _, _, _
        assert_eq!(it.next(), None);
    }
}
