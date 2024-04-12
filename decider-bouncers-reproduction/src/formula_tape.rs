use crate::directional_tm::TapeHead;

use super::directional_tm;
use super::directional_tm::{Direction, Tape, TapeContent};
use std::fmt;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
/// Begin and end indexes of a repeater in a formula tape.
pub struct RepeaterPos {
    pub beg: usize,
    /// end is exclusive, and repeater cannot be empty beg < end
    pub end: usize,
}

/// Formula tape (wall-repeater formula tape) as defined in the bouncers writeup.
///
/// ```
/// use decider_bouncers_reproduction::formula_tape::{FormulaTape, RepeaterPos};
/// use decider_bouncers_reproduction::directional_tm::{Direction, Tape, TapeHead};
/// let machine_str = "1RB1LE_1LC1RD_1LB1RC_1LA0RD_---0LA";
/// let formula_tape = FormulaTape { tape: Tape::new_partial(machine_str, &[1,1,0,1,1,0,1], TapeHead::default(), &[0,0]), repeaters_pos: vec![RepeaterPos { beg: 0, end: 4 }] };
/// assert_eq!(format!("{formula_tape}"), "(1101)101A>00");
/// let formula_tape = FormulaTape { tape: Tape::new(machine_str, &[1,1,1,1,1,1,1,1,1,0,1,1,1,1,0], TapeHead::default(), &[1]), repeaters_pos: vec![RepeaterPos { beg: 1, end: 4 },RepeaterPos { beg: 13, end: 15 }] };
/// assert_eq!(format!("{formula_tape}"), "0∞(111)111111011(11)0A>10∞");
/// let formula_tape = FormulaTape { tape: Tape::new(machine_str, &[1,1,1,1,1,1,1,1,1,0,1,1], TapeHead::default(), &[1,1,0,1]), repeaters_pos: vec![RepeaterPos { beg: 1, end: 4 },RepeaterPos { beg: 14, end: 16 }] };
/// assert_eq!(format!("{formula_tape}"), "0∞(111)111111011A>(11)010∞");
/// ```
pub struct FormulaTape {
    pub tape: Tape,
    pub repeaters_pos: Vec<RepeaterPos>, // sorted by beg *and* end (if unwraped the array is a sorted array of positions)
}

#[derive(Debug, PartialEq, Eq)]
pub enum FormulaTapeError {
    TMError(directional_tm::TMError),
    NoShiftRule,
    /// Relative to the head's direction.
    NoRepeaterAfterHead,
    /// Relative to the head's direction.
    NoRepeaterBeforeHead,
}

impl FormulaTapeError {
    fn result_from_tm_error<T>(
        res: Result<T, directional_tm::TMError>,
    ) -> Result<T, FormulaTapeError> {
        match res {
            Ok(x) => Ok(x),
            Err(e) => Err(FormulaTapeError::TMError(e)),
        }
    }
}

impl FormulaTape {
    fn pos_is_repeater_beg(&self, pos: usize) -> bool {
        self.repeaters_pos
            .binary_search_by_key(&pos, |repeater_pos| repeater_pos.beg)
            .is_ok()
    }

    fn pos_is_repeater_end(&self, pos: usize) -> bool {
        self.repeaters_pos
            .binary_search_by_key(&pos, |repeater_pos| repeater_pos.end)
            .is_ok()
    }

    /// Returns the position of the next repeater after the head (after is relative to the head's direction).
    ///
    ///  ```
    /// use decider_bouncers_reproduction::formula_tape::{FormulaTape, RepeaterPos, FormulaTapeError};
    /// use decider_bouncers_reproduction::directional_tm::{Direction, Tape, TapeHead};
    /// let machine_str = "1RB1LE_1LC1RD_1LB1RC_1LA0RD_---0LA";
    /// let formula_tape = FormulaTape { tape: Tape::new(machine_str, &[1,1,1,1,1,1,1,1,1,0,1,1,1,1,0], TapeHead::default(), &[1]), repeaters_pos: vec![RepeaterPos { beg: 1, end: 4 },RepeaterPos { beg: 13, end: 15 }] };
    /// let repeater_after_head = formula_tape.repeater_pos_after_head();
    /// assert_eq!(format!("{formula_tape}"), "0∞(111)111111011(11)0A>10∞");
    /// assert_eq!(repeater_after_head, Err(FormulaTapeError::NoRepeaterAfterHead));
    /// let formula_tape = FormulaTape { tape: Tape::new(machine_str, &[1,1,1,1,1,1,1,1,1,0,1,1], TapeHead::default(), &[1,1,0,1]), repeaters_pos: vec![RepeaterPos { beg: 1, end: 4 },RepeaterPos { beg: 14, end: 16 }] };
    /// let repeater_after_head = formula_tape.repeater_pos_after_head();
    /// assert_eq!(format!("{formula_tape}"), "0∞(111)111111011A>(11)010∞");
    /// assert_eq!(repeater_after_head, Ok(RepeaterPos { beg: 14, end: 16 }));
    /// let formula_tape = FormulaTape { tape: Tape::new(machine_str, &[1,1,1,1,1,1,1,1,1,0,1,1], TapeHead::default(), &[0,1,1,1,0,1]), repeaters_pos: vec![RepeaterPos { beg: 1, end: 4 },RepeaterPos { beg: 16, end: 18 }] };
    /// let repeater_after_head = formula_tape.repeater_pos_after_head();
    /// assert_eq!(format!("{formula_tape}"), "0∞(111)111111011A>01(11)010∞");
    /// assert_eq!(repeater_after_head, Ok(RepeaterPos { beg: 16, end: 18 }));
    /// ```
    pub fn repeater_pos_after_head(&self) -> Result<RepeaterPos, FormulaTapeError> {
        let head = FormulaTapeError::result_from_tm_error(self.tape.get_current_head())?;

        let repeater_pos = self
            .repeaters_pos
            .binary_search_by_key(&self.tape.head_pos, |repeater_pos| repeater_pos.beg);

        if head.pointing_direction == Direction::RIGHT {
            match repeater_pos {
                Ok(_) => Err(FormulaTapeError::TMError(
                    directional_tm::TMError::InvalidTapeError,
                )),
                Err(repeater_index) => {
                    if repeater_index == self.repeaters_pos.len() {
                        return Err(FormulaTapeError::NoRepeaterAfterHead);
                    }
                    Ok(self.repeaters_pos[repeater_index])
                }
            }
        } else {
            match repeater_pos {
                Ok(_) => Err(FormulaTapeError::TMError(
                    directional_tm::TMError::InvalidTapeError,
                )),
                Err(repeater_index) => {
                    if repeater_index == 0 {
                        return Err(FormulaTapeError::NoRepeaterAfterHead);
                    }
                    Ok(self.repeaters_pos[repeater_index - 1])
                }
            }
        }
    }

    /// Returns the position of the last repeater before the head (before is relative to the head's direction).
    fn repeater_pos_before_head(&self) -> Result<RepeaterPos, FormulaTapeError> {
        let head = FormulaTapeError::result_from_tm_error(self.tape.get_current_head())?;

        let repeater_pos = self
            .repeaters_pos
            .binary_search_by_key(&self.tape.head_pos, |repeater_pos| repeater_pos.beg);

        if head.pointing_direction == Direction::RIGHT {
            match repeater_pos {
                Ok(_) => Err(FormulaTapeError::TMError(
                    directional_tm::TMError::InvalidTapeError,
                )),
                Err(repeater_index) => {
                    if repeater_index == 0 {
                        return Err(FormulaTapeError::NoRepeaterBeforeHead);
                    }
                    Ok(self.repeaters_pos[repeater_index - 1])
                }
            }
        } else {
            match repeater_pos {
                Ok(_) => Err(FormulaTapeError::TMError(
                    directional_tm::TMError::InvalidTapeError,
                )),
                Err(repeater_index) => {
                    if repeater_index == self.repeaters_pos.len() {
                        return Err(FormulaTapeError::NoRepeaterBeforeHead);
                    }
                    Ok(self.repeaters_pos[repeater_index])
                }
            }
        }
    }

    fn head_is_pointing_at_repeater(&self) -> bool {
        if self.tape.head_pos == 0 {
            return self.pos_is_repeater_beg(self.tape.head_pos + 1);
        }
        self.pos_is_repeater_beg(self.tape.head_pos + 1)
            || self.pos_is_repeater_end(self.tape.head_pos - 1)
    }

    fn shift_rule_tape(&self) -> Result<Tape, FormulaTapeError> {
        assert!(self.head_is_pointing_at_repeater());

        let head = match &self.tape.tape_content[self.tape.head_pos] {
            TapeContent::Head(head) => head,
            _ => {
                return Err(FormulaTapeError::TMError(
                    directional_tm::TMError::InvalidTapeError,
                ))
            }
        };

        let repeater_pos_after_head: RepeaterPos = self.repeater_pos_after_head()?; // Head is pointing at a repeater, so there must be a repeater after the head.
        let repeater_pos_before_head: Result<RepeaterPos, FormulaTapeError> =
            self.repeater_pos_before_head(); // There's not necessarily a repeater before the head.

        let shift_rule_tape_beg = match head.pointing_direction {
            Direction::RIGHT => {
                if let Ok(repeater_pos_before_head) = repeater_pos_before_head {
                    repeater_pos_before_head.end
                } else {
                    match self.tape.tape_content[0] {
                        TapeContent::InfiniteZero => 1,
                        _ => 0,
                    }
                }
            }
            Direction::LEFT => repeater_pos_after_head.beg,
        };

        let shift_rule_tape_end = match head.pointing_direction {
            Direction::RIGHT => repeater_pos_after_head.end,
            Direction::LEFT => {
                if let Ok(repeater_pos_before_head) = repeater_pos_before_head {
                    repeater_pos_before_head.beg
                } else {
                    match self.tape.tape_content[self.tape.len() - 1] {
                        TapeContent::InfiniteZero => self.tape.len() - 1,
                        _ => self.tape.len(),
                    }
                }
            }
        };

        match self.tape.sub_tape(shift_rule_tape_beg, shift_rule_tape_end) {
            Some(tape) => Ok(tape),
            None => Err(FormulaTapeError::TMError(
                directional_tm::TMError::InvalidTapeError,
            )),
        }
    }

    /// Implements a formula tape step: it corresponds to a standard TM step when the head in not pointing at a repeater and corresponds to running a shift rule (if any exists) otherwise.
    fn step(&mut self) -> Result<(), FormulaTapeError> {
        if !self.head_is_pointing_at_repeater() {
            return FormulaTapeError::result_from_tm_error(self.tape.step());
        }

        Ok(())
    }
}

impl fmt::Display for FormulaTape {
    /// Returns the string representation of a formula tape.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for i in 0..self.tape.tape_content.len() {
            match &self.tape.tape_content[i] {
                TapeContent::InfiniteZero => write!(f, "0∞")?,
                TapeContent::Symbol(x) => {
                    if self.pos_is_repeater_beg(i) {
                        write!(f, "({}", x)?;
                    } else if self.pos_is_repeater_end(i + 1) {
                        write!(f, "{})", x)?;
                    } else {
                        write!(f, "{}", x)?;
                    }
                }
                TapeContent::Head(head) => {
                    if i != self.tape.head_pos {
                        panic!("Stored head position {} is not consistent with actual head position {} in tape.", self.tape.head_pos, i);
                    }

                    if head.pointing_direction == Direction::RIGHT {
                        write!(f, "{}>", (head.state + b'A') as char)?;
                    } else {
                        write!(f, "<{}", (head.state + b'A') as char)?;
                    }
                }
            }
        }
        write!(f, "")
    }
}
