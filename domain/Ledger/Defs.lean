/-!
# Ledger core: definitions

Everything in this file is (a) the specification the proofs talk about and
(b) the source that `Emit.lean` translates to OCaml. Definitions that are
emitted must stay inside the generator's subset (see README): structures of
`Int`/lists, `Int`/`Nat` `+ - * ≤ < =`, `Bool` `&& || !`, `if`, and the list
combinators `foldr map filter all length`. No `match`, no recursion: loops are
`List.foldr`, which *is* structural recursion, just packaged.

Prop-level predicates (`Balanced`, `Valid`, ...) are for proofs only and are
never emitted.
-/
namespace Spec

/-! ## Bounds (the deliberate Lean `Int` vs OCaml `int` divergence)

Lean `Int` is unbounded; OCaml `int` is 63-bit. The domain is therefore
bounded, and `Proofs.lean` shows every sum the generated code computes fits. -/

/-- Largest absolute amount, in minor units (10^12). -/
def maxAmount : Int := 1000000000000
/-- Most postings in one transaction. -/
def maxPostings : Nat := 1000
/-- Most postings in a whole ledger. Needed for per-account balances to fit
(10^12 * 10^6 = 10^18 < 2^62); the per-transaction bounds alone are not enough. -/
def maxLedgerPostings : Nat := 1000000

/-! ## Domain types -/

/-- Account id. Any `Int`: equality on OCaml's `int` agrees with Lean's. -/
abbrev Account := Int

structure Posting where
  account : Account
  /-- Signed amount in minor units. -/
  amount : Int

/-- Non-emptiness is enforced by `Balanced` (≥ 2 postings), not by the type,
which keeps the generator's type language to plain records. -/
structure Transaction where
  postings : List Posting

abbrev Ledger := List Transaction

/-! ## Computable core (emitted to OCaml) -/

def Posting.inBounds (p : Posting) : Bool :=
  decide (-maxAmount ≤ p.amount) && decide (p.amount ≤ maxAmount)

/-- Sum of a transaction's posting amounts. Equals the Lean `Int` sum only within
the bounds (see `TxSumFitsInt63`); callers should check `validate` first. -/
def Transaction.sum (t : Transaction) : Int :=
  t.postings.foldr (fun p acc => p.amount + acc) 0

/-- True iff `t` is balanced and within bounds (`validate_iff`).
Order matters for the OCaml code: `&&` short-circuits, so `sum` is only
evaluated once every amount and the posting count are known to be in bounds. -/
def Transaction.validate (t : Transaction) : Bool :=
  decide (2 ≤ t.postings.length) && decide (t.postings.length ≤ maxPostings) &&
  t.postings.all Posting.inBounds && decide (t.sum = 0)

def Ledger.postingCount (l : Ledger) : Nat :=
  l.foldr (fun t n => t.postings.length + n) 0

/-- Every transaction valid and at most `maxLedgerPostings` postings in total. -/
def Ledger.valid (l : Ledger) : Bool :=
  l.all Transaction.validate && decide (l.postingCount ≤ maxLedgerPostings)

/-- Sum of the amounts of all postings to account `a`. Exact (no overflow) when
`Ledger.valid l` holds (see `BalanceFitsInt63`). -/
def Ledger.balanceOf (a : Account) (l : Ledger) : Int :=
  l.foldr
    (fun t acc =>
      t.postings.foldr (fun p s => if p.account = a then p.amount + s else s) 0 + acc)
    0

/-! ## Proof-only (never emitted) -/

/-- Sum of every amount in the ledger. -/
def Ledger.total (l : Ledger) : Int := l.foldr (fun t acc => t.sum + acc) 0

def AmountOk (a : Int) : Prop := -maxAmount ≤ a ∧ a ≤ maxAmount

/-- Balanced: at least two postings, amounts sum to zero. Decidable, hence computable. -/
def Balanced (t : Transaction) : Prop := 2 ≤ t.postings.length ∧ t.sum = 0

def InBounds (t : Transaction) : Prop :=
  t.postings.length ≤ maxPostings ∧ ∀ p ∈ t.postings, AmountOk p.amount

def Valid (t : Transaction) : Prop := Balanced t ∧ InBounds t

def LedgerOk (l : Ledger) : Prop :=
  (∀ t ∈ l, Valid t) ∧ l.postingCount ≤ maxLedgerPostings

instance : DecidablePred AmountOk := fun _ => by unfold AmountOk; infer_instance
instance : DecidablePred Balanced := fun _ => by unfold Balanced; infer_instance
instance : DecidablePred InBounds := fun _ => by unfold InBounds; infer_instance
instance : DecidablePred Valid := fun _ => by unfold Valid; infer_instance

end Spec
