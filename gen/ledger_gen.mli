(* GENERATED FILE -- DO NOT EDIT.

   Written by domain/Emit.lean (`cd domain && lake exe emit ../gen`) from the
   Lean module Ledger.Defs. Lean declarations emitted, in order:
     Spec.Account -> account
     Spec.Posting -> posting
     Spec.Transaction -> transaction
     Spec.Ledger -> ledger
     Spec.maxAmount -> max_amount
     Spec.maxPostings -> max_postings
     Spec.maxLedgerPostings -> max_ledger_postings
     Spec.Transaction.sum -> transaction_sum
     Spec.Posting.inBounds -> posting_in_bounds
     Spec.Transaction.validate -> transaction_validate
     Spec.Ledger.postingCount -> ledger_posting_count
     Spec.Ledger.valid -> ledger_valid
     Spec.Ledger.balanceOf -> ledger_balance_of

   This is the interface of ledger_gen.ml. Pure: no I/O, no state, no exceptions.
   Regenerate with scripts/gen.sh; scripts/check-gen.sh fails CI on any drift.
   Trusted, not proved: this translation and the OCaml compiler. The Lean
   theorems are about the Lean definitions; this file is tested against them. *)

(* Account id. Any 'Int': equality on OCaml's 'int' agrees with Lean's. *)
type account = int

type posting = {
  account : account;
  amount : int;
}

(* Non-emptiness is enforced by 'Balanced' (≥ 2 postings), not by the type,
which keeps the generator's type language to plain records. *)
type transaction = {
  postings : posting list;
}

type ledger = transaction list

(* Largest absolute amount, in minor units (10^12). *)
val max_amount : int

(* Most postings in one transaction. *)
val max_postings : int

(* Most postings in a whole ledger. Needed for per-account balances to fit
(10^12 * 10^6 = 10^18 < 2^62); the per-transaction bounds alone are not enough. *)
val max_ledger_postings : int

(* Sum of a transaction's posting amounts. Equals the Lean 'Int' sum only within
the bounds (see 'TxSumFitsInt63'); callers should check 'validate' first. *)
val transaction_sum : transaction -> int

(* True iff 't' is balanced and within bounds ('validate_iff').
The sum is evaluated last. On out-of-bounds input the OCaml sum may wrap, but
then a bounds conjunct is already false, so the verdict is unaffected; when all
bounds hold, the sum cannot overflow ('TxSumFitsInt63'). *)
val transaction_validate : transaction -> bool

(* Every transaction valid and at most 'maxLedgerPostings' postings in total. *)
val ledger_valid : ledger -> bool

(* Sum of the amounts of all postings to account 'a'. Exact (no overflow) when
'Ledger.valid l' holds (see 'BalanceFitsInt63'). *)
val ledger_balance_of : account -> ledger -> int
