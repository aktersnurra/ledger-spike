import Ledger.Defs
/-!
# Theorem statements (review these; proofs live in `Proofs.lean`)

Statements are plain `Prop` definitions so they can be read, and locked, apart
from their proofs. `Check.lean` re-ascribes each proof to its statement.
-/
namespace Spec

/-! ## The Lean `Int` / OCaml `int` bridge -/

/-- OCaml's `int` on a 64-bit platform is 63-bit two's complement. -/
def int63Min : Int := -4611686018427387904   -- -2^62
def int63Max : Int :=  4611686018427387903   --  2^62 - 1
def FitsInt63 (x : Int) : Prop := int63Min ≤ x ∧ x ≤ int63Max

/-- `maxAmount` really is 10^12 (it is written as a literal for the generator). -/
def MaxAmountIsTenPow12 : Prop := maxAmount = 10 ^ 12

/-- Inside the bounds, `Transaction.sum` fits an OCaml `int`. `foldr` evaluates
the sums of the suffixes `postings.drop k`, so quantifying over `k` covers every
intermediate accumulator the generated code computes, not just the result. -/
def TxSumFitsInt63 : Prop :=
  ∀ t : Transaction, InBounds t →
    ∀ k : Nat, FitsInt63 (Transaction.sum ⟨t.postings.drop k⟩)

/-- Same for per-account balances over a valid ledger (and its suffixes). -/
def BalanceFitsInt63 : Prop :=
  ∀ (l : Ledger) (a : Account), LedgerOk l →
    ∀ k : Nat, FitsInt63 (Ledger.balanceOf a (l.drop k))

/-! ## Ledger invariant -/

/-- Appending a balanced transaction to a zero-total ledger keeps it zero. -/
def AppendKeepsTotalZero : Prop :=
  ∀ (l : Ledger) (t : Transaction), Balanced t → l.total = 0 → (l ++ [t]).total = 0

/-! ## The boolean checker is the predicate -/

def ValidateSound : Prop :=
  ∀ t : Transaction, Transaction.validate t = true → Valid t

def ValidateComplete : Prop :=
  ∀ t : Transaction, Valid t → Transaction.validate t = true

def LedgerValidIff : Prop :=
  ∀ l : Ledger, Ledger.valid l = true ↔ LedgerOk l

end Spec
