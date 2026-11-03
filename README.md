# ledger-spike

A small spike: a double-entry ledger core whose rules are **specified and proved in Lean 4**,
with the **pure OCaml implementation generated from the Lean source** by a small Lean
program, plus a **drift check** and **differential tests** against the Lean model.
Working name; this is the pure core only (no MCP, no storage, no I/O).

```
domain/            Lean 4 project (core Lean only, no Mathlib; toolchain pinned in domain/lean-toolchain)
  Ledger/Defs.lean        types, bounds, validate, balanceOf   <- spec AND generator input
  Ledger/Statements.lean  theorem statements (`def Foo : Prop`), reviewable apart from proofs
  Ledger/Proofs.lean      the proofs
  Ledger/Check.lean       re-ascribes each proof to its statement + `#print axioms`
  Emit.lean               Lean -> OCaml text generator (`lake exe emit <outdir>`)
  Oracle.lean             stdin/stdout reference verdicts for differential tests
  Reject/Bad.lean         deliberately unsupported Lean, used to test the generator refuses it
gen/               GENERATED ledger_gen.ml + .mli, checked in. Never hand-edit.
test/              unit.ml (boundaries, overflow) and diff.ml (seeded differential vs the oracle)
scripts/           verify.sh (everything), proof-gate.sh, check-gen.sh, gen.sh, test-reject.sh
```

## Run it

Prerequisites: [elan](https://github.com/leanprover/elan) (it fetches the pinned Lean, 4.35.0),
and an OCaml 5.x opam switch with `dune` and `alcotest`:

```sh
opam switch create 5.3.0 && eval $(opam env) && opam install dune alcotest   # once
scripts/verify.sh                                                            # everything
```

`verify.sh` = Lean build + proof gate, generator rejection tests, drift check, `dune build`,
unit tests, and 3000 seeded random differential cases (`LEDGER_SEED`, `LEDGER_CASES`) plus two
ledger-size boundary cases. To regenerate after editing the Lean source: `scripts/gen.sh`, then commit.
CI (`.github/workflows/ci.yml`) has a Lean-only `drift` job and a full `test` job.
*(The CI file has not been exercised on GitHub; the scripts it calls have been run locally.)*

## What is proved, what is tested, what is trusted

| Claim | Status |
|---|---|
| Appending a balanced tx to a zero-total ledger keeps total 0 (`appendKeepsTotalZero`) | **proved** (Lean, about the Lean model) |
| `validate t = true ↔ Valid t` (`validateSound`, `validateComplete`), and `Ledger.valid ↔ LedgerOk` | **proved** |
| In bounds, every sum the OCaml code computes fits a 63-bit `int` (`txSumFitsInt63`, `balanceFitsInt63`) | **proved** about Lean `Int`; that OCaml then computes the same value is the *bridge* below |
| The generated OCaml behaves like the Lean definitions | **tested only** (unit + differential), not proved |
| The Lean→OCaml translation (`Emit.lean`), the OCaml compiler/runtime, `Sys.int_size = 63` | **trusted** |
| The oracle's parser/printer and the test generators | **trusted** (a bug there could hide a mismatch; mutation-tested, see below) |

The proofs cover the Lean model, **not** the generated program. `Emit.lean` drops instance and type
arguments of whitelisted heads and renames operators; that is the one place the Lean term is not
printed verbatim, and it is covered by tests, not proof.

Axioms (`scripts/proof-gate.sh`; `Check.lean`; nothing outside `propext`, `Classical.choice`, `Quot.sound`;
no `sorry`/`axiom`/`native_decide`/`unsafe`/`implemented_by`/`extern` in the spec or proofs):

```
'Spec.maxAmountIsTenPow12' does not depend on any axioms
'Spec.txSumFitsInt63' depends on axioms: [propext, Classical.choice, Quot.sound]
'Spec.balanceFitsInt63' depends on axioms: [propext, Classical.choice, Quot.sound]
'Spec.appendKeepsTotalZero' depends on axioms: [propext, Quot.sound]
'Spec.validateSound' depends on axioms: [propext, Quot.sound]
'Spec.validateComplete' depends on axioms: [propext, Quot.sound]
'Spec.ledgerValidIff' depends on axioms: [propext, Quot.sound]
```

## The Lean `Int` vs OCaml `int` divergence (explicit, not assumed)

Lean `Int` is unbounded; OCaml `int` is 63-bit (`-2^62 … 2^62-1`). The domain is therefore bounded:

* `|amount| ≤ 10^12` (`maxAmount`), at most `1000` postings per transaction (`maxPostings`) — as specified.
* **Added:** at most `10^6` postings per ledger (`maxLedgerPostings`). The two bounds above are enough for
  `validate` (|sum| ≤ 10^15) but **not** for per-account balances: balances accumulate over the whole ledger,
  and a few thousand maximal transactions would pass 2^62 ≈ 4.6·10^18. With 10^6 postings, |balance| ≤ 10^18.

`FitsInt63 x := -2^62 ≤ x ≤ 2^62-1`. `TxSumFitsInt63` / `BalanceFitsInt63` are stated for **every
suffix** (`drop k`) because `List.foldr` computes sums of suffixes: this covers each intermediate
accumulator the generated code evaluates, not just the final result. The bridge argument — and its trusted
step — is: the generated code uses only `+`/`-`/`*`/comparisons on values that, by those theorems, equal
the exact Lean values and fit in 63 bits, so native arithmetic agrees with Lean's. `validate` rejects
out-of-bounds input, but note: even if the sum wrapped on such input, a bounds conjunct is already false,
so the verdict is unaffected (`test/unit.ml` shows `[max_int; max_int; 2]` wrapping to 0 and still being
rejected). `ledger_balance_of` is only exact when `ledger_valid` holds; that is its documented precondition.
Account ids are arbitrary `int`s (equality is faithful in both worlds).

## Generator (`domain/Emit.lean`)

Ordinary text generation, not an extraction framework: it reads the kernel term of each requested
definition from the compiled environment and prints OCaml for a **whitelisted subset**; anything else is an
error naming the declaration and constant (`scripts/test-reject.sh` checks six such cases). Supported:

* types: `Int`/`Nat` → `int`, `Bool`, `List α`, arrows, `structure`s → records, `abbrev` type aliases;
* terms: variables, `fun`, `let`, `if`/`cond`, `true`/`false`, `Spec.*` constants and fully-applied functions,
  structure constructors/projections, Int/Nat literals, `+ * -` (Int-only `-`: Nat's truncating `-` is rejected),
  unary `-`, `&& || !`, `decide` of `≤ < ≥ > = ≠ ∧ ∨ ¬` on Int/Nat/Bool,
  `List.{nil,cons,foldr,map,filter,all,length}`.
* **no** `match`, general recursion, division, typeclass-polymorphic code, `Option`, strings. Loops are `List.foldr`
  (structural recursion packaged as a combinator; OCaml 5's growable stack makes `List.fold_right` fine at these sizes).

Output is deterministic (no timestamps), carries a header naming the Lean declarations it came from, and gets
a minimal generated `.mli`. `scripts/check-gen.sh` regenerates to a temp dir and diffs against `gen/`.

## Differential tests

`oracle` (Lean) reads cases from stdin — transaction lines of `ACCOUNT:AMOUNT` tokens, a `.` line ends a case —
and prints per-tx `validate`, ledger `valid`, and per-account balances computed with unbounded Lean `Int`.
`test/diff.ml` generates random cases (balanced, unbalanced, empty, single-posting, ±10^12 and ±(10^12+1),
`max_int`/`min_int`, 1000/1001/1002-posting transactions, sum-wraps-to-zero cases, force-valid ledgers, valid
ledgers with one corrupted tx), runs the generated OCaml and the oracle, and compares every line. Seeded
(`LEDGER_SEED`, default 1). It also asserts that both accept and reject paths are well exercised.
The oracle additionally re-checks `validate` against `decide (Valid t)` at runtime.

Mutation check (done by hand, not automated): seven single-line mutations of `gen/ledger_gen.ml`
(off-by-one in each bound, dropped oversize/sum check, wrong account match, min postings 1) are each caught by
the differential test alone.

## Tool versions used

Lean 4.35.0 (Lake 5.0.0), elan 4.2.4, OCaml 5.3.0, dune 3.24.2, alcotest 1.9.1, Ubuntu 24.04.
