import Ledger.Defs
/-! Deliberately outside the generator's subset. `scripts/test-reject.sh`
checks that `emit` refuses each one with an error instead of emitting code. -/
namespace Reject
open Spec

/-- Nat subtraction truncates; OCaml's does not. -/
def natSub (t : Transaction) : Nat := t.postings.length - 5

/-- Int division/modulo have different rounding conventions. -/
def intDiv (a : Int) : Int := a / 7

/-- Pattern matching / recursion on lists is not in the subset. -/
def firstAmount (t : Transaction) : Int :=
  match t.postings with
  | [] => 0
  | p :: _ => p.amount

/-- Library function outside the whitelist. -/
def maxAmt (t : Transaction) : Int := (t.postings.map Posting.amount).foldl max 0

/-- Proposition-level definitions are proof-only. -/
def propUse (t : Transaction) : Bool := decide (Balanced t)

/-- Non-structure inductive types are not emitted. -/
def optUse (t : Transaction) : Option Int := some t.sum
end Reject
