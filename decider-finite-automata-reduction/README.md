# [Decider] Finite Automata Reduction

## Usage

To build it and view usage options, [install Rust](https://www.rust-lang.org/learn/get-started) and, in this directory:

```
$ cargo run --release -- --help
   ...
Usage: decider-finite-automata-reduction [-p <prover...>] [-l <limit...>] [-x <exclude...>] [-s] [--ip <ip>] [--port <port>] [-a <ad-hoc...>] [-d <db>] [-i <index>]

Decide TMs, using finite-state recognizers for their halting configurations.

Options:
  -p, --prover      prover(s) to use: see example
  -l, --limit       maximum search depth (DFA size) for corresponding prover
  -x, --exclude     exclude search depth (DFA size) for corresponding prover
  -s, --server      run as a server; clients will solve in parallel
  --ip              server IP address
  --port            server port
  -a, --ad-hoc      analyze only the given TMs/seeds and show any proofs found
  -d, --db          path to the DB file
  -i, --index       path to the undecided index file (used if present)
  --help            display usage information

Examples:
  # Analyze individual machines:
  $ decider-finite-automata-reduction -a 7410754 -a 1RB0RC_0LC1LE_0RD1LB_1RA1RC_0LB---
  # Parallel processing:
  $ decider-finite-automata-reduction --server --ip 10.0.0.1 -p direct -x 0 -l 8 -p mitm_dfa -x 8
  # And in other terminal tabs and/or computers on the network, once per CPU
  $ decider-finite-automata-reduction --ip 10.0.0.1
```

(After building, you can also pass command lines directly to the binary, e.g. `target/release/decider-finite-automata-reduction --help`.)

For BB(5), you'll want to have `../all_5_states_undecided_machines_with_global_header` and `../bb5_undecided_index` -- see `../README.md`.
(Alternate locations may be provided on the command line.)
Settings recommended for BB(5): `--server --ip $(hostname -i) -p direct -x 0 -l 7 -p mitm_dfa -x 9 -l 11 -p direct -x 7 -l 9 -p mitm_dfa -x 11 -l 12`.
The server command will wait for one or more client commands to start, then use them to solve machines in parallel.

In general, deeper searches succeed more often but take dramatically more time. 
(Rough time/TM: `-p direct` depths 1-10: 4μs, 12μs, 17μs, 300μs, 1ms, 4ms, 30ms, 30s, 2m, 20m assuming `features=sink_heuristic`;
                `-p mitm_dfa` 1-12: 7μs, 50μs, 300μs, 1ms, 5ms, 20ms, 80ms, 300ms, 1s, 4s, 20s, 40s.)
The program will solve most of the seed DB at low depth before going deeper.
The `mitm_dfa` prover covers a subset of the `direct` prover's search space, so it's redundant to use it at a depth where `direct` has been used.
(Up to depth 7, it's also slower, but from depth 8 it's increasingly faster.)

Results will be saved to the `output` subdir:

- `finite_automata_reduction.index`: solved DB indexes in [this format](https://bbchallenge.org/method#undecided-machines-index-file)
- `finite_automata_reduction.dvf`: a [Decider Verification File](https://github.com/TonyGuil/bbchallenge/blob/main/README), explained below.

### Individual machines

As in the first command-line example, the decider's `--ad-hoc` mode lets you solve one or more machines,
given as [Seed DB](https://bbchallenge.org/method#seed-database) indexes or [machine code](http://discuss.bbchallenge.org/t/standard-tm-text-format/60/17?u=uncombedcoconut) text.
It will output the data of any successful proof (explained below) as pretty-printed JSON.

### Build-time options

The default build options work only for BB(5) and up to search depths of 12, and make the `direct` prover search exhaustively.

To double the depth limit (at the cost of some speed), add `--features u128` to the `cargo build` / `cargo run` command lines.
To change the number of TM states, edit `src/limits.rs`. The program will expect a seed DB format with a corresponding number of bytes per machine.
Beware, some unit tests assume `TM_STATES == 5`, and nearly all testing has been in BB(5) mode.
Similarly, to change the number of tape symbols, update the `SYMBOLS` value in the same file, but beware of unit tests assuming the default value of 2.

To speed up the `direct` prover dramatically at most depths, build with `--features sink_heuristic`.
The effect is to reduce the search space in a way that leads to a few false negatives (TMs proven only at later iterations than necessary), but *much* faster search iterations.
Overall, this means TMs are solved in less time. The reason this isn't the default is to simplify the algorithm in the paper and for reproducers.

Disabling the `fix_zero` feature via `--no-default-features` makes an opposite trade-off, by switching to a more general "visit-tracking" version of FAR.
The price is a severe speed penalty in the proof search, and incompatibility with `.dvf`-file verifiers designed for the original proof conditions.
The upside is that a few TMs gain proofs at lower depth.

## How it works: practice

Note: the decider correctness paper [here](https://github.com/bbchallenge/bbchallenge-proofs/blob/finite-automata-reduction/deciders/correctness-deciders.pdf) covers similar material,
though it sidesteps the material in the "theory" section relating this decider to related techniques.

We search for the data of the following non-halting proof (which is easily checked, even if the search is complex).
In this section, I'll take it for granted that a complex definition is worth writing out. (That's the hard part.)
The next section will explain the background and motivations.

### Proof template

The proof, once we define its terms, will say: "the following finite-state machine, by construction, recognizes all halting tape configurations for this TM.
It doesn't recognize the initial configuration. Therefore the TM doesn't halt from its initial configuration."

The BB Challenge community sometimes calls this a "co-CTL" proof. More on that later.

Now for the definitions. The below is also expressed as commented Rust code, in `src/proof.rs`.

1. Define a finite-state machine of the following form, whose job is to scan TM configurations (WLOG left to right) and "recognize" some of them:
    1. Start at the leftmost tape cell which the TM has visited.
    2. Read the tape as a [DFA (Q, Σ, δ, q₀)](https://en.wikipedia.org/wiki/Deterministic_finite_automaton) up to (but excluding) the head position.
    3. Transition to an [NFA (Q', Σ, δ', F)](https://en.wikipedia.org/wiki/Nondeterministic_finite_automata) whose state space Q' includes QˣQ™,
       i.e., has a specific NFA state (q, f) for whichever DFA end-state q and TM head-state f we get.
    4. Read the tape as an NFA, reading all symbols from the head position onward that the TM has written.
       The TM configuration is *recognized* if there's a possible end state belonging to F.
2. Also designate a *steady state* S⊆Q', i.e., a set of states such that δ'(S, s)⊇S for any symbol s∈Σ, which furthermore contains at least one state from F.
   In other words, if at any step the NFA could have reached all of S, that's also true on the next step and the configuration will ultimately be recognized.
3. Define the *closure* properties which effectively say, if the configuration after a TM step is recognized, the configuration before it is too:
    - In case of a right transition (f, r) ↦ (w, **R**, t), whose effect on the tape is to change the sequence `f>r` to `w t>`:
      ∀q∈Q: δ'((q, f), r) ∋ (δ(q, w), t).
    - In the above case, if r=0, there's also a transition from `f>$` (`f>` at the end of the visited tape) to `w t>$`, and we also require:
      ∀q∈Q: (q, f) ∈ F ⟸ (δ(q, w), t) ∈ F.
    - In case of a left transition (f, r) ↦ (w, **L**, t), whose effect on the tape is to change the sequence `s f>r` to `t>s w`:
      ∀(q,s)∈Q×Σ: δ'((δ(q, s), f), r) ⊇ δ'(δ'((q, t), s), w).
    - The above also has special cases at the edges of the visited tape: `^f>r` to `^t>0w`, `s f>$` to `t>s w$` if r=0, and `^f>$` to `^t>0 w$` if r=0.
      We then require:
      * δ'((q₀, f), r) ⊇ δ'(δ'((q₀, t), 0), w),
      * ∀(q,s)∈Q×Σ: (δ(q, s), f) ∈ F ⟸ δ'(δ'((q, t), s), w) ∩ F ≠ ∅ if r=0.
      * (q₀, f) ∈ F ⟸ δ'(δ'((q₀, t), 0), w) ∈ F if r=0.
4. In case of a halt rule for (f, r), require an NFA transition to the steady state (thus guaranteeing recognition): 
   ∀q∈Q: δ'((q, f), r) ⊇ S. If r=0, we require that `f>$` is recognized, i.e., Qx{f} ⊆ F.
5. Finally, require the initial configuration not to be recognized: (q₀, `A`)∉F.

Note: In case the DFA ignores leading zeros i.e, δ(q₀, 0) = q₀) and the NFA ignores trailing zeros (i.e., δ'(F, 0) = F),
the rules about the four special-case transitions at the edges of the visited tape are redundant,
and the "start"/"end" of the tape can be set at arbitrary points beyond any nonzero tape contents.
Thus, one need not distinguish visisted and unvisited tape cells when working with leading-/trailing-zero-invariant automata.
**The first first published version of this decider worked this way. Thus, independent verifier programs have assumed leading/trailing zero invariance.**

### Proof data format

In a computer representation of the above, we number the DFA states, identifying q₀ with 0, and number the NFA states, identifying (q, f) with 5q+f
(in the BB(5) case, of course; and similarly for other values of 5.)

We represent a DFA as a simple nested list, [[δ(0, 0), δ(0, 1), …], [δ(1, 0), δ(1, 1), …], …, [δ(n, 0), δ(n, 1), …]].

In a [Decider Verification File](https://github.com/TonyGuil/bbchallenge/blob/main/README), this is flattened to a sequence of |Σ|n bytes.

To represent transitions, sets of accepted states, and sets of reachable states, we use a well-known
[matrix characterization of automata](https://planetmath.org/matrixcharacterizationsofautomata):
they become matrices, row vectors, and column vectors, respectively.
Boolean matrices suffice. Vectors are represented as bitfields. Matrices are [row-major](https://en.wikipedia.org/wiki/Row-_and_column-major_order).

This explains the JSON objects that come back from a `--ad-hoc` command to the decider.
That's a lot for a data format, so our Verification Files actually only include the DFA.
As it turns out, the rest of the proof can be reconstructed almost instantly.

### Code and test structure

The program's code is divided into four modules:

- core: defines the data and correctness criteria of a proof, as above (plus essentials like the TM, DFA, NFA, and boolean vector/matrix representations).
  This part is extensively documented and unit tested.
- io: defines how to work with the file formats involved. This part is merely battle-tested and reasonably documented.
- provers: the secret sauce: not actually secret, obviously, but it's impossible to make these "so simple that there are obviously no deficiencies".
           Instead, this code is restricted to outputting Proof objects which are checked before the decider considers a machine solved.
- driver: utility code for handling such concerns as distributed processing and progress monitoring.

In terms of correctness, the most important part is `core/proof.rs`.
As usual for Rust programs — unit tests are in-line, so `core/proof.rs` also has the tests that bad proofs are rejected.

### Verification File

In our [Decider Verification Files](https://github.com/TonyGuil/bbchallenge/blob/main/README), we specify the following:
- `DeciderType` = 10
- `InfoLength` is variable, but corresponds to
- `DeciderSpecificInfo` contains 1 byte for the direction (0 if as above the FSM is to scan left-to-right, 1 if reversed),
  then |Σ|n bytes for a DFA transition table as described above
- Note that Tony Guilfoyle (the above repo's author) has both implemented an independent verifier, and specified a format variant (`DeciderType` = 11)
  where the decider info defines the full DFA+NFA proof.
- Warning: The DVF format has an `nEntries` header. This decider operates in append mode and lets that become stale.
  It may also write multiple proof records for the same `SeedDatabaseIndex`. These are quirks to fix in post-processing.
  Some Python scripts to aid in post-processing (and conversion to enriched `DeciderType=11` format) are available in
  [this repository](https://github.com/UncombedCoconut/bbchallenge-nfa-verification).

So, in full, the format of `output/finite_automata_reduction.dvf` is:
* nEntries: `uint32_t` (big-endian, *not reliable*)
* For each entry:
    - SeedDatabaseIndex: `uint32_t` (big-endian)
    - DeciderType: `uint32_t` (big-endian, always 10)
    - InfoLength: `uint32_t` (big-endian)
    - Direction: `uint8_t` (0 if the automaton reads left-to-right, 1 otherwise)
    - TransitionTable: `uint8_t[InfoLength-1]` (entries `[δ(0, 0), δ(0, 1), …; δ(1, 0), δ(1, 1), …; …; δ(n, 0), δ(n, 1), …]`, where `n = (InfoLength-1)/|Σ|`)

## How it works: theory

### CTL and Co-CTL
The [Closed Tape Language](https://www.sligocki.com/2022/06/10/ctl.html) technique analyzes TM behavior using regular languages.
Its potential has been well-known to the community.

Compared to the definitions above, this is *complemented* (CTL recognizes the start and avoids recognizing halting configurations).
It is also *time-reversed* (if the configuration before a TM step is recognized, the configuration after it is too).
Indeed, the complement of a language making a "co-CTL proof" work makes a "CTL proof" work, and vice-versa: this is just contraposition.
(Before implies after iff not after implies not before.)

These two techniques thus have precisely the same power, though some proof searches may be better at finding one than the other, and there may be overhead
when translating between the two proof styles.

### Automata connections

Picture a Turing Machine as a two-stack machine: a fixed head pushes and pulls on two half-tapes.
If we split the left "stack" configurations into finitely many classes, and consider the transitions between (class, head, right-tape) tuples, we get a nondeterministic stack machine.
The following paper builds a finite state machine which recognizes configurations from which a stack machine can halt:

[[BEM97](https://www.irif.fr/~abou//BEM97.pdf)] Bouajjani, A., Esparza, J., & Maler, O. (1997, July). Reachability analysis of pushdown automata: Application to model-checking.
In International Conference on Concurrency Theory (pp. 135-150). Springer, Berlin, Heidelberg.

If you have a (regular) (co-) CTL, it has a finite-state recognizer.
The recognizer classifies left half-tapes by the state reached.
The classification produces a stack machine.
Its exact solution is again a regular co-CTL, so these characterizations are also interchangeable.

### Quotients of Turing Machines
Let L be a co-CTL for a TM.

As mentioned in the "Proof Template" section — for a *tape* language to make sense we must require it to be (reverse) closed under TM transitions *and*
invariant under zero-padding.

Let \~ be the [left syntactic equivalence](https://en.wikipedia.org/wiki/Syntactic_monoid#Syntactic_equivalence) relation it induces on tape-alphabet strings.

Let `[u]` denote the \~-equivalence class of a tape-string u, and v be another tape-string.

Define TM/\~ as a machine with configurations `[u] f>v`, and transitions `[u] f>v` ↦ `[u'] f'>v'` for each valid TM step `^u f>v$` ↦ `^u f>v'$`.

Define halting for TM/\~ as for TM, and L(TM/\~) — the language TM/\~ accepts — to contain the configurations from which a halt is reachable.

When we view the `[u] f>` as states and the `v` as a stack, [BEM97] says TM/\~ is a "pushdown system" and L(TM/\~) is recognized by a certain finite automaton.

Thus, L' = { `u f>v` | TM/\~ may accept `[u] f>v 0ⁿ` for some n } is a regular language we can recognize.

L' is also a co-CTL: if it accepts `u f>v` after one step, then TM/\~ accepts it after one step (and zero-padding), so ditto before the one step, so L' accepts `u f>v`.

L' accepts halting words. If L does too, then L'⊆L, so we've recovered an equal or finer co-CTL.

### Direct recognizer for L(TM/\~)
While [BEM97] is a nice tool, it's helpful to derive the L(TM/\~) recognizer directly.
So: let’s decide if a configuration starting with `[u] f>s₀` can lead to a halt, by considering how:
it would via a finite transition sequence, which either reads the next symbol s₁ at some point or first hits a halt-transition.
If the former is possible, that’s an unconditional yes;
the latter is possible iff `[u] f>s₀v` may lead to some `[u'] f'>v` (via transitions which ignore the `v`) and `[u'] f>s₁s₂…` can lead to a halt.
This gives an inductively defined recognizer, which operates as an NFA on the state space {HALT} ∪ Q×Q™.
That last paragraph defines its transitions mathematically. We can make the definition effective by defining *them* inductively:

* In case of a halt rule for (f, r): for any `[u]`, `[u] f>, r`↦`HALT` is an `r`-transition. (`HALT` simply transitions to itself.)
* In case of a right transition (f, r) ↦ (w, **R**, t), whose effect on the tape is to change the sequence `f>r` to `w t>`:
  for any `[u]`, `[u] f>, r`↦`[uw] t>` is an `r`-transition.
* In case of a left transition (f, r) ↦ (w, **L**, t), whose effect on the tape is to change the sequence `s₀ f>r` to `t>s₀ w`:
  whenever `[u] t>, s₀, w`↦`[u'] t'>` is a composition of `s₀`- and `w`-transitions, there’s an `r`-transition from `[ub₀] f>, r`↦`[u'] t'>`.

To compute the recognizing NFA’s transition relation, we may close an initially empty relation under these rules.

This is what `direct.rs` does.

Consequently, direct.rs is also able to complete a proof from just the DFA side.
This makes it a useful partner to the verifier, even if it's untrusted: if someone claims a DFA works in a proof, the verifier can ask this algorithm to complete it, then check the completed proof.

### Meet-in-the-Middle DFAs
There is another finite state machine architecture to consider for a tape language recognizer, which is appealing because it's very simple:
Any regular tape language remains regular when reversed.
Thus, there exist DFAs recognizing the original and reversed language.
If we delete everything except the `s`-transitions for each tape-symbol `s`,
we get finite-state classifiers for the left and right halves of the tape (in both cases excluding the symbol under the head).

Here, too, we can consider the connection between DFAs and semantic equivalence:
we see that any tape configuration's membership in the language is determined by what the left-tape DFA does, what the right-tape DFA does, and the head configuration (state and symbol underneath).

If we define a finite-state recognizer which operates this way — runs both tape halves through a DFA, and checks this triple against an accepted set —
we see that the relevant closure conditions are fairly easy to formulate.

There are two ways to connect this construction back to the DFA+NFA constructions discussed above: either reverse the arrows on the right-tape DFA (making it nondeterministic) and change the accept states into a bunch of transitions, or simply throw away the right-tape DFA and apply the TM/~ construction.

The decider in `mitm_dfa.rs` follows on a path first set by others — see there for details — and sets up the closure conditions for the MitM-DFA as a boolean satisfiability problem.
Thanks and credit go to:

- Konrad Deka (@djmati1111, https://github.com/colette-b/bbchallenge)
- Mateusz Naściszewski (@Mateon1, https://discuss.bbchallenge.org/u/mateon1)
