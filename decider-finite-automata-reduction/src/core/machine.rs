//! A Turing Machine definition which matches the bbchallenge.org database format.

use super::{Symbol, TMState, SYMBOLS, TM_STATES};
use serde::{Deserialize, Serialize};
use serde_with::{DeserializeFromStr, SerializeDisplay};
use std::fmt::{Display, Formatter};
use std::str::FromStr;
use thiserror::Error;
use zerocopy::{AsBytes, FromBytes, FromZeroes};

/// A low-level transition, as in https://bbchallenge.org/method#format
#[derive(AsBytes, FromBytes, FromZeroes, Clone, Debug, Default, Eq, PartialEq)]
#[repr(C)]
struct Trans {
    sym: u8,
    dir: u8,
    new: u8,
}

#[derive(Error, Debug)]
#[error("use https://discuss.bbchallenge.org/t/standard-tm-text-format")]
pub struct BadTMText;

impl FromStr for Trans {
    type Err = BadTMText;

    fn from_str(text: &str) -> Result<Self, Self::Err> {
        let mut chars = text.chars();
        let sym = match chars.next() {
            Some('-') => 0 as Symbol,
            Some(c) if c.is_ascii_digit() => (c as u32 - '0' as u32) as Symbol,
            _ => return Err(BadTMText {}),
        };
        if sym as usize >= SYMBOLS {
            return Err(BadTMText {});
        }
        let dir = match chars.next() {
            Some('-') | Some('R') => 0u8,
            Some('L') => 1u8,
            _ => return Err(BadTMText {}),
        };
        let new = match chars.next().and_then(|c| c.to_digit(10 + TM_STATES as u32)) {
            Some(b36) if b36 > 9 => (b36 - 9) as u8,
            _ => 0u8,
        };
        Ok(Trans { sym, dir, new })
    }
}

impl Display for Trans {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        if self.new == 0 {
            write!(f, "---")
        } else {
            write!(
                f,
                "{}{}{}",
                self.sym,
                if self.dir == 0 { 'R' } else { 'L' },
                char::from_digit(self.new as u32 + 9, 36).unwrap_or('?').to_ascii_uppercase()
            )
        }
    }
}

/// A Turing machine definition, as in https://bbchallenge.org/method#format
#[derive(
    AsBytes,
    FromBytes,
    FromZeroes,
    Clone,
    SerializeDisplay,
    DeserializeFromStr,
    Debug,
    Default,
    Eq,
    PartialEq,
)]
#[repr(C)]
pub struct Machine {
    code: [[Trans; SYMBOLS]; TM_STATES],
}

/// Left or right.
#[derive(Serialize, Deserialize, Clone, Copy, Debug, Eq, PartialEq)]
pub enum Side {
    L,
    R,
}

impl Display for Side {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

/// An higher-level transition, as a tagged enum. Conventions: "f"rom, "r"ead, "t"o, "w"rite.
#[derive(Serialize, Deserialize, Clone, Debug, Eq, PartialEq)]
pub enum Rule {
    Move { f: TMState, r: u8, w: u8, d: Side, t: TMState },
    Halt { f: TMState, r: u8 },
}

impl Display for Rule {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl Machine {
    pub fn rules(&self) -> impl Iterator<Item = Rule> + '_ {
        self.code.iter().flatten().enumerate().map(|(fr, trans)| {
            let (f, r) = ((fr / SYMBOLS) as TMState, (fr % SYMBOLS) as u8);
            if trans.new == 0 {
                Rule::Halt { f, r }
            } else {
                let w = trans.sym;
                let d = if trans.dir == 0 { Side::R } else { Side::L };
                let t = trans.new - 1;
                Rule::Move { f, r, w, d, t }
            }
        })
    }
}

impl FromStr for Machine {
    type Err = BadTMText;

    fn from_str(text: &str) -> Result<Self, Self::Err> {
        let mut tm = Machine::default();
        for r in 0..TM_STATES {
            for s in 0..SYMBOLS {
                if let Some(t) = text.get(r + 3 * (SYMBOLS * r + s)..r + 3 * (SYMBOLS * r + s + 1))
                {
                    tm.code[r][s] = Trans::from_str(t)?;
                } else {
                    return Err(BadTMText {});
                }
            }
        }
        Ok(tm)
    }
}

impl Display for Machine {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        for (i, t01) in self.code.iter().enumerate() {
            write!(f, "{}{}{}", if i == 0 { "" } else { "_" }, t01[0], t01[1])?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_encoding() {
        let champ_bin = b"\x01\x00\x02\x01\x01\x03\x01\x00\x03\x01\x00\x02\x01\x00\x04\
                                    \x00\x01\x05\x01\x01\x01\x01\x01\x04\x00\x00\x00\x00\x01\x01";
        let champ = Machine::from_str("1RB1LC_1RC1RB_1RD0LE_1LA1LD_---0LA").unwrap();
        let champ_rules: Vec<Rule> = champ.rules().collect();
        assert_eq!(champ_bin, champ.as_bytes());
        let tm = Machine::read_from(champ_bin as &[u8]);
        assert_eq!(tm, Some(champ));
        let (f, r, w, d, t) = (0, 0, 1, Side::R, 1);
        assert_eq!(champ_rules[0], Rule::Move { f, r, w, d, t });
        assert_eq!(champ_rules[8], Rule::Halt { f: 4, r: 0 });

        assert_eq!(
            Machine::from_str("1RB1LC_1RC1RB_1RD0LE_1LA1LD_---0LA").unwrap(),
            Machine::from_str("1RB1LC_1RC1RB_1RD0LE_1LA1LD_0RZ0LA").unwrap()
        )
    }
}
