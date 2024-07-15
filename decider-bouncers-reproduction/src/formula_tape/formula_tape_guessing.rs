use super::*;

use std::{
    collections::{HashMap, HashSet},
    process::exit,
    vec,
};

use ndarray::{Array, IntoDimension, NdIndex};
use std::cell::Cell;

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
enum FormulaTapeAtoms {
    Symbol(u8),
    Repeater(Vec<u8>),
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
struct FormulaTapeSearchConfiguration {
    pos_tape1: usize,
    pos_tape2: usize,
    pos_tape3: usize,
    proto_formula_tape: Vec<FormulaTapeAtoms>,
}

fn vproto2s(v: &Vec<FormulaTapeAtoms>) -> String {
    let mut s = String::new();
    for atom in v.iter() {
        match atom {
            FormulaTapeAtoms::Symbol(symbol) => s.push_str(&format!("{}", symbol)),
            FormulaTapeAtoms::Repeater(repeater) => s.push_str(&format!("({})", v2s(repeater))),
        }
    }
    s
}

impl std::fmt::Display for FormulaTapeSearchConfiguration {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(
            f,
            "{}, {}, {}",
            self.pos_tape1, self.pos_tape2, self.pos_tape3
        )?;
        for atom in self.proto_formula_tape.iter() {
            match atom {
                FormulaTapeAtoms::Symbol(symbol) => write!(f, "{}", symbol)?,
                FormulaTapeAtoms::Repeater(repeater) => write!(f, "({})", v2s(repeater))?,
            }
        }
        write!(f, "")
    }
}

fn proto_formula_tape_to_formula_tape(
    machine_str: &str,
    head: TapeHead,
    proto_formula_tape: Vec<FormulaTapeAtoms>,
) -> FormulaTape {
    let mut tape_content = vec![];
    let mut repeaters_pos: Vec<RepeaterPos> = vec![];

    let offset = if head.pointing_direction == Direction::LEFT {
        2
    } else {
        1
    };

    let mut repeater_offset = 0;
    for (i, atom) in proto_formula_tape.iter().enumerate() {
        match atom {
            FormulaTapeAtoms::Symbol(symbol) => tape_content.push(*symbol),
            FormulaTapeAtoms::Repeater(repeater) => {
                tape_content.extend(repeater);
                repeaters_pos.push(RepeaterPos {
                    beg: offset + repeater_offset + i,
                    end: offset + repeater_offset + i + repeater.len(),
                });
                repeater_offset += repeater.len() - 1;
            }
        }
    }

    let tape = if head.pointing_direction == Direction::LEFT {
        Tape::new(machine_str, &[], head, &tape_content)
    } else {
        Tape::new(machine_str, &tape_content, head, &[])
    };

    FormulaTape {
        tape,
        repeaters_pos,
    }
}

impl From<(usize, usize, usize)> for FormulaTapeSearchConfiguration {
    fn from((pos_tape1, pos_tape2, pos_tape3): (usize, usize, usize)) -> Self {
        Self {
            pos_tape1,
            pos_tape2,
            pos_tape3,
            proto_formula_tape: vec![],
        }
    }
}

impl From<(usize, usize, usize, Vec<FormulaTapeAtoms>)> for FormulaTapeSearchConfiguration {
    fn from(
        (pos_tape1, pos_tape2, pos_tape3, proto_formula_tape): (
            usize,
            usize,
            usize,
            Vec<FormulaTapeAtoms>,
        ),
    ) -> Self {
        Self {
            pos_tape1,
            pos_tape2,
            pos_tape3,
            proto_formula_tape,
        }
    }
}

fn remove_head_and_infinite_0(tape: Tape) -> Vec<u8> {
    let tape = tape.clone();
    return tape
        .tape_content
        .iter()
        .filter(|content| match content {
            TapeContent::Head(_) => false,
            TapeContent::InfiniteZero => false,
            _ => true,
        })
        .map(|content| match content {
            TapeContent::Symbol(symbol) => symbol,
            _ => panic!("Unexpected content"),
        })
        .copied()
        .collect::<Vec<u8>>();
}

use memo::Memo;
use std::num::NonZeroU32;

pub fn fit_formula_tape_from_triple_mei(
    tape0: Tape,
    tape1: Tape,
    tape2: Tape,
) -> Option<FormulaTape> {
    let machine_str = tape0.machine_transition.machine_std_format.clone();
    let head = tape0.get_current_head().unwrap();
    let tape0 = remove_head_and_infinite_0(tape0);
    let tape1 = remove_head_and_infinite_0(tape1);
    let tape2 = remove_head_and_infinite_0(tape2);

    //println!("Testing triplet");
    //println!("{} {} {}", v2s(&tape0), v2s(&tape1), v2s(&tape2));

    // Using implem from https://github.com/meithecatte/busycoq/blob/master/beaver/src/decider/bouncers.rs#L574
    #[derive(Clone, Copy)]
    struct DPResult(NonZeroU32);

    enum Step {
        Sym,
        Repeat(usize),
        End,
    }

    impl DPResult {
        const NO_SOLUTION: u32 = u32::MAX;
        const SYMBOL: u32 = u32::MAX - 1;
        const END: u32 = u32::MAX - 2;
        const MAX_REPEATER: u32 = u32::MAX - 3;

        fn ok(self) -> bool {
            self.0.get() != Self::NO_SOLUTION
        }

        fn fail() -> Self {
            DPResult(NonZeroU32::new(Self::NO_SOLUTION).unwrap())
        }

        fn symbol() -> Self {
            DPResult(NonZeroU32::new(Self::SYMBOL).unwrap())
        }

        fn repeater(k: usize) -> Self {
            let k: u32 = k.try_into().unwrap();
            if k > Self::MAX_REPEATER {
                panic!("Repeater too large");
            }

            DPResult(NonZeroU32::new(k).unwrap())
        }

        fn end() -> Self {
            DPResult(NonZeroU32::new(Self::END).unwrap())
        }

        fn decode(self) -> Option<Step> {
            match self.0.get() {
                Self::NO_SOLUTION => None,
                Self::SYMBOL => Some(Step::Sym),
                Self::END => Some(Step::End),
                k => Some(Step::Repeat(k as usize)),
            }
        }
    }

    let f = |(i0, d), memo: &Memo<DPResult, _, _>| -> DPResult {
        let i1 = i0 + d;
        let i2 = i0 + 2 * d;

        // If i0 and i1 point to the end, then i2 also does
        if i0 == tape0.len() && i1 == tape1.len() {
            return DPResult::end();
        }

        if i0 < tape0.len()
            && i1 < tape1.len()
            && i2 < tape2.len()
            && tape0[i0] == tape1[i1]
            && tape1[i1] == tape2[i2]
            && memo.get((i0 + 1, d)).ok()
        {
            return DPResult::symbol();
        }

        let remaining_s0: usize = tape0.len() - i0;
        let remaining_s1 = tape1.len() - i1;
        let longest_match = tape1
            .iter()
            .skip(i1)
            .zip(tape2.iter().skip(i2))
            .take(remaining_s1 - remaining_s0)
            .take_while(|&(a, b)| a == b)
            .count();
        for k in (1..=longest_match).rev() {
            if tape2[i2..i2 + k] == tape2[i2 + k..i2 + 2 * k] && memo.get((i0, d + k)).ok() {
                return DPResult::repeater(k);
            }
        }

        DPResult::fail()
    };

    let mut proto_formula_tape: Vec<FormulaTapeAtoms> = vec![];

    let memo = Memo::new((tape0.len() + 1, tape1.len() - tape0.len() + 1), &f);
    let mut i0 = 0;
    let mut d = 0;

    loop {
        match memo.get((i0, d)).decode()? {
            Step::Sym => {
                proto_formula_tape.push(FormulaTapeAtoms::Symbol(tape0[i0]));
                i0 += 1;
            }
            Step::Repeat(k) => {
                proto_formula_tape.push(FormulaTapeAtoms::Repeater(
                    tape1[i0 + d..i0 + d + k].to_vec(),
                ));

                d += k;
            }
            Step::End => {
                return Some(proto_formula_tape_to_formula_tape(
                    &machine_str,
                    head,
                    proto_formula_tape,
                ))
            }
        }
    }
}

pub fn fit_formula_tape_from_triple_recursive_implem(
    tape0: Tape,
    tape1: Tape,
    tape2: Tape,
) -> Option<FormulaTape> {
    let machine_str = tape0.machine_transition.machine_std_format.clone();
    let head = tape0.get_current_head().unwrap();
    let tape0 = remove_head_and_infinite_0(tape0);
    let tape1 = remove_head_and_infinite_0(tape1);
    let tape2 = remove_head_and_infinite_0(tape2);

    #[derive(Debug, Clone, Eq, PartialEq, Hash, Copy)]
    enum DPStep {
        Sym,
        Repeat(usize),
        End,
        Fail,
    }

    struct DPEnv {
        tape0: Vec<u8>,
        tape1: Vec<u8>,
        tape2: Vec<u8>,
        memo: HashMap<(usize, usize), DPStep>,
    }

    let mut env = DPEnv {
        tape0,
        tape1,
        tape2,
        memo: HashMap::new(),
    };

    // Implements savask's Dynamic Programming algorithm to guess the formula tape from 3 tapes.
    // See: https://gist.github.com/savask/888aa5e058559c972413790c29d7ad72
    // And: https://discord.com/channels/960643023006490684/1028745661459472484/1167757825875914782
    fn rec_DP_algo(pos_tape_0: usize, total_repeater_size: usize, env: &mut DPEnv) -> DPStep {
        //println!("ENTER {} {}", pos_tape_0, total_repeater_size);

        if env.memo.get(&(pos_tape_0, total_repeater_size)).is_some() {
            return env.memo[&(pos_tape_0, total_repeater_size)];
        }

        let i1 = pos_tape_0 + total_repeater_size;
        let i2 = pos_tape_0 + 2 * total_repeater_size;

        if pos_tape_0 == env.tape0.len() && i1 == env.tape1.len() {
            //println!("END {} {}", pos_tape_0, total_repeater_size);
            return DPStep::End;
        }

        if pos_tape_0 < env.tape0.len()
            && i1 < env.tape1.len()
            && i2 < env.tape2.len()
            && env.tape0[pos_tape_0] == env.tape1[i1]
            && env.tape1[i1] == env.tape2[i2]
        {
            //println!("TEST SYM {} {}", pos_tape_0, total_repeater_size);
            let res = rec_DP_algo(pos_tape_0 + 1, total_repeater_size, env);
            //println!("TEST SYM RESULT {:?}", res);
            if res != DPStep::Fail {
                env.memo
                    .insert((pos_tape_0, total_repeater_size), DPStep::Sym);
                //println!("SYM {} {}", pos_tape_0, total_repeater_size);
                return DPStep::Sym;
            }
        }

        let remaining_s0: usize = env.tape0.len() - pos_tape_0;
        let remaining_s1 = env.tape1.len() - i1;
        let longest_match = env
            .tape1
            .iter()
            .skip(i1)
            .zip(env.tape2.iter().skip(i2))
            .take(remaining_s1 - remaining_s0)
            .take_while(|&(a, b)| a == b)
            .count();
        for k in (1..=longest_match).rev() {
            if env.tape2[i2..i2 + k] == env.tape2[i2 + k..i2 + 2 * k] {
                let res = rec_DP_algo(pos_tape_0, total_repeater_size + k, env);
                if res != DPStep::Fail {
                    env.memo
                        .insert((pos_tape_0, total_repeater_size), DPStep::Repeat(k));

                    return DPStep::Repeat(k);
                }
            }
        }

        //println!("FAIL3 {} {}", pos_tape_0, total_repeater_size);
        env.memo
            .insert((pos_tape_0, total_repeater_size), DPStep::Fail);
        DPStep::Fail
    }

    let mut proto_formula_tape: Vec<FormulaTapeAtoms> = vec![];
    let mut pos_tape_0 = 0;
    let mut total_repeater_size = 0;

    loop {
        match rec_DP_algo(pos_tape_0, total_repeater_size, &mut env) {
            DPStep::Sym => {
                proto_formula_tape.push(FormulaTapeAtoms::Symbol(env.tape0[pos_tape_0]));
                pos_tape_0 += 1;
            }
            DPStep::Repeat(k) => {
                proto_formula_tape.push(FormulaTapeAtoms::Repeater(
                    env.tape1
                        [pos_tape_0 + total_repeater_size..pos_tape_0 + total_repeater_size + k]
                        .to_vec(),
                ));

                total_repeater_size += k;
            }
            DPStep::End => {
                return Some(proto_formula_tape_to_formula_tape(
                    &machine_str,
                    head,
                    proto_formula_tape,
                ))
            }
            DPStep::Fail => {
                return None;
            }
        }
    }
}

/// ```
/// use decider_bouncers_reproduction::formula_tape::formula_tape_guessing::fit_formula_tape_from_triple_greedy_iterative_implem;
/// use decider_bouncers_reproduction::directional_tm::Tape;
/// let tape0:Tape = "0∞10110A>0∞".parse().unwrap();
/// let tape1:Tape = "0∞10110101110A>0∞".parse().unwrap();
/// let tape2:Tape = "0∞10110101101011110A>0∞".parse().unwrap();
/// let res = fit_formula_tape_from_triple_greedy_iterative_implem(tape0, tape1, tape2);
/// println!("{:?}", res);
/// assert!(res.is_none());
/// ```
pub fn fit_formula_tape_from_triple_greedy_iterative_implem(
    tape0: Tape,
    tape1: Tape,
    tape2: Tape,
) -> Option<FormulaTape> {
    let mut proto_formula_tape: Vec<FormulaTapeAtoms> = vec![];
    let machine_str = tape0.machine_transition.machine_std_format.clone();
    let head = tape0.get_current_head().unwrap();
    let tape0 = remove_head_and_infinite_0(tape0);
    let tape1 = remove_head_and_infinite_0(tape1);
    let tape2 = remove_head_and_infinite_0(tape2);

    let mut pos_tape0 = 0;
    let mut total_repeater_size = 0;

    'outer: loop {
        let pos_tape1 = pos_tape0 + total_repeater_size;
        let pos_tape2 = pos_tape0 + 2 * total_repeater_size;

        if pos_tape0 == tape0.len() && pos_tape1 == tape1.len() {
            return Some(proto_formula_tape_to_formula_tape(
                &machine_str,
                head,
                proto_formula_tape,
            ));
        }

        if pos_tape0 < tape0.len()
            && pos_tape1 < tape1.len()
            && pos_tape2 < tape2.len()
            && tape0[pos_tape0] == tape1[pos_tape1]
            && tape1[pos_tape1] == tape2[pos_tape2]
        {
            proto_formula_tape.push(FormulaTapeAtoms::Symbol(tape0[pos_tape0]));
            pos_tape0 += 1;
            continue;
        }

        let remaining_tape0 = tape0.len() - pos_tape0;
        let remaining_tape1 = tape1.len() - pos_tape1;
        let mut longest_match = 0;
        while longest_match < remaining_tape1 - remaining_tape0
            && pos_tape1 + longest_match < tape1.len()
            && pos_tape2 + longest_match < tape2.len()
            && tape1[pos_tape1 + longest_match] == tape2[pos_tape2 + longest_match]
        {
            longest_match += 1;
        }

        for k in (1..=longest_match).rev() {
            if tape2[pos_tape2..pos_tape2 + k] == tape2[pos_tape2 + k..pos_tape2 + 2 * k] {
                proto_formula_tape.push(FormulaTapeAtoms::Repeater(
                    tape1[pos_tape1..pos_tape1 + k].to_vec(),
                ));
                total_repeater_size += k;
                continue 'outer;
            }
        }
        return None;
    }
}

pub fn fit_formula_tape_from_triple_greedy_recursive_implem(
    tape0: Tape,
    tape1: Tape,
    tape2: Tape,
) -> Option<FormulaTape> {
    let machine_str = tape0.machine_transition.machine_std_format.clone();
    let head = tape0.get_current_head().unwrap();
    let tape0 = remove_head_and_infinite_0(tape0);
    let tape1 = remove_head_and_infinite_0(tape1);
    let tape2 = remove_head_and_infinite_0(tape2);

    #[derive(Debug, Clone, Eq, PartialEq, Hash, Copy)]
    enum DPStep {
        Sym,
        Repeat(usize),
        End,
        Fail,
    }

    struct DPEnv {
        tape0: Vec<u8>,
        tape1: Vec<u8>,
        tape2: Vec<u8>,
        memo: HashMap<(usize, usize), DPStep>,
    }

    let mut env = DPEnv {
        tape0,
        tape1,
        tape2,
        memo: HashMap::new(),
    };

    // Implements savask's Dynamic Programming algorithm to guess the formula tape from 3 tapes.
    // See: https://gist.github.com/savask/888aa5e058559c972413790c29d7ad72
    // And: https://discord.com/channels/960643023006490684/1028745661459472484/1167757825875914782
    fn rec_DP_algo(pos_tape_0: usize, total_repeater_size: usize, env: &mut DPEnv) -> DPStep {
        //println!("ENTER {} {}", pos_tape_0, total_repeater_size);

        if env.memo.get(&(pos_tape_0, total_repeater_size)).is_some() {
            return env.memo[&(pos_tape_0, total_repeater_size)];
        }

        let i1 = pos_tape_0 + total_repeater_size;
        let i2 = pos_tape_0 + 2 * total_repeater_size;

        if pos_tape_0 == env.tape0.len() && i1 == env.tape1.len() {
            //println!("END {} {}", pos_tape_0, total_repeater_size);
            return DPStep::End;
        }

        if pos_tape_0 < env.tape0.len()
            && i1 < env.tape1.len()
            && i2 < env.tape2.len()
            && env.tape0[pos_tape_0] == env.tape1[i1]
            && env.tape1[i1] == env.tape2[i2]
        {
            //println!("TEST SYM {} {}", pos_tape_0, total_repeater_size);
            let res = rec_DP_algo(pos_tape_0 + 1, total_repeater_size, env);
            //println!("TEST SYM RESULT {:?}", res);
            if res == DPStep::Fail {
                env.memo
                    .insert((pos_tape_0, total_repeater_size), DPStep::Fail);

                //println!("FAIL1 {} {}", pos_tape_0, total_repeater_size);
                return DPStep::Fail;
            }
            env.memo
                .insert((pos_tape_0, total_repeater_size), DPStep::Sym);
            //println!("SYM {} {}", pos_tape_0, total_repeater_size);
            return DPStep::Sym;
        }

        let remaining_s0: usize = env.tape0.len() - pos_tape_0;
        let remaining_s1 = env.tape1.len() - i1;
        let longest_match = env
            .tape1
            .iter()
            .skip(i1)
            .zip(env.tape2.iter().skip(i2))
            .take(remaining_s1 - remaining_s0)
            .take_while(|&(a, b)| a == b)
            .count();
        for k in (1..=longest_match).rev() {
            if env.tape2[i2..i2 + k] == env.tape2[i2 + k..i2 + 2 * k] {
                let res = rec_DP_algo(pos_tape_0, total_repeater_size + k, env);
                if res == DPStep::Fail {
                    env.memo
                        .insert((pos_tape_0, total_repeater_size), DPStep::Fail);
                    //println!("FAIL2 {} {}", pos_tape_0, total_repeater_size);
                    return DPStep::Fail;
                }
                env.memo
                    .insert((pos_tape_0, total_repeater_size), DPStep::Repeat(k));
                //println!("REPEAT {} {}", pos_tape_0, total_repeater_size);
                return DPStep::Repeat(k);
            }
        }

        //println!("FAIL3 {} {}", pos_tape_0, total_repeater_size);
        DPStep::Fail
    }

    let mut proto_formula_tape: Vec<FormulaTapeAtoms> = vec![];
    let mut pos_tape_0 = 0;
    let mut total_repeater_size = 0;

    loop {
        match rec_DP_algo(pos_tape_0, total_repeater_size, &mut env) {
            DPStep::Sym => {
                proto_formula_tape.push(FormulaTapeAtoms::Symbol(env.tape0[pos_tape_0]));
                pos_tape_0 += 1;
            }
            DPStep::Repeat(k) => {
                proto_formula_tape.push(FormulaTapeAtoms::Repeater(
                    env.tape1
                        [pos_tape_0 + total_repeater_size..pos_tape_0 + total_repeater_size + k]
                        .to_vec(),
                ));

                total_repeater_size += k;
            }
            DPStep::End => {
                return Some(proto_formula_tape_to_formula_tape(
                    &machine_str,
                    head,
                    proto_formula_tape,
                ))
            }
            DPStep::Fail => {
                return None;
            }
        }
    }
}
