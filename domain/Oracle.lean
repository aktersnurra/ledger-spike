import Ledger.Proofs
/-!
# Oracle: the Lean reference verdicts, over stdin/stdout

Input: a sequence of *cases*. A case is zero or more transaction lines followed
by a line `.`. A transaction line is space-separated `ACCOUNT:AMOUNT` tokens
(integers); an empty line is the empty transaction.

Output, per case:
  `T ok|bad`      one per transaction line: `Transaction.validate`
  `L ok|bad`      `Ledger.valid` of all the case's transactions
  `B <acct> <n>`  `Ledger.balanceOf` over the *valid* transactions, one line per
                  account occurring in them, ascending
  `.`
The Lean side computes with unbounded `Int`; it never overflows.
-/
open Spec

def parsePosting (tok : String) : Option Posting :=
  match tok.splitOn ":" with
  | [a, m] => do pure { account := ← a.toInt?, amount := ← m.toInt? }
  | _ => none

def parseTx (line : String) : Option Transaction :=
  ((line.splitOn " ").filter (· ≠ "")).mapM parsePosting |>.map (⟨·⟩)

def verdict (b : Bool) : String := if b then "ok" else "bad"

def report (txs : List Transaction) (out : IO.FS.Stream) : IO Unit := do
  for t in txs do
    let v := Transaction.validate t
    -- runtime re-check of `validate_iff` against the Prop-level predicate
    if decide (Valid t) != v then
      throw (IO.userError "validate disagrees with decide (Valid t): spec bug")
    out.putStrLn s!"T {verdict v}"
  out.putStrLn s!"L {verdict (Ledger.valid txs)}"
  let good := txs.filter Transaction.validate
  let accts := (good.flatMap (·.postings.map (·.account))).eraseDups.mergeSort (fun a b => decide (a ≤ b))
  for a in accts do
    out.putStrLn s!"B {a} {Ledger.balanceOf a good}"
  out.putStrLn "."

def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let out ← IO.getStdout
  let mut cur : Array Transaction := #[]
  let mut n := 0
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break   -- EOF (an empty tx line is "\n", not "")
    n := n + 1
    let line := line.trimAscii.toString
    if line == "." then
      report cur.toList out
      cur := #[]
    else match parseTx line with
      | some t => cur := cur.push t
      | none =>
        IO.eprintln s!"oracle: cannot parse line {n}: {line}"
        return 2
  return 0
