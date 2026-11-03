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

   Interface: see ledger_gen.mli. Pure: no I/O, no state, no exceptions.
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
let max_amount : int =
  1000000000000

(* Most postings in one transaction. *)
let max_postings : int =
  1000

(* Most postings in a whole ledger. Needed for per-account balances to fit
(10^12 * 10^6 = 10^18 < 2^62); the per-transaction bounds alone are not enough. *)
let max_ledger_postings : int =
  1000000

(* Sum of a transaction's posting amounts. Equals the Lean 'Int' sum only within
the bounds (see 'TxSumFitsInt63'); callers should check 'validate' first. *)
let transaction_sum (t : transaction) : int =
  List.fold_right
    (fun (p : posting) (acc : int) -> (p.amount + acc))
    t.postings
    0

let posting_in_bounds (p : posting) : bool =
  ((-max_amount) <= p.amount) && (p.amount <= max_amount)

(* True iff 't' is balanced and within bounds ('validate_iff').
Order matters for the OCaml code: '&&' short-circuits, so 'sum' is only
evaluated once every amount and the posting count are known to be in bounds. *)
let transaction_validate (t : transaction) : bool =
  (2 <= (List.length t.postings))
   && ((List.length t.postings) <= max_postings)
   && (List.for_all posting_in_bounds t.postings)
   && ((transaction_sum t) = 0)

let ledger_posting_count (l : ledger) : int =
  List.fold_right
    (fun (t : transaction) (n : int) -> ((List.length t.postings) + n))
    l
    0

(* Every transaction valid and at most 'maxLedgerPostings' postings in total. *)
let ledger_valid (l : ledger) : bool =
  (List.for_all transaction_validate l)
   && ((ledger_posting_count l) <= max_ledger_postings)

(* Sum of the amounts of all postings to account 'a'. Exact (no overflow) when
'Ledger.valid l' holds (see 'BalanceFitsInt63'). *)
let ledger_balance_of (a : account) (l : ledger) : int =
  List.fold_right
    (fun (t : transaction) (acc : int) ->
      ((List.fold_right
          (fun (p : posting) (s : int) ->
            (if (p.account = a) then (p.amount + s) else s))
          t.postings
          0) + acc))
    l
    0
