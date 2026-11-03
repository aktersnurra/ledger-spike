(* Shared by the differential drivers: the oracle's line format and the expected
   verdict computed from the generated OCaml. *)
module L = Ledger_gen

let tx_line (t : L.transaction) =
  String.concat " " (List.map (fun (q : L.posting) -> Printf.sprintf "%d:%d" q.account q.amount) t.postings)

let case_text txs = String.concat "" (List.map (fun t -> tx_line t ^ "\n") txs) ^ ".\n"

let ok b = if b then "ok" else "bad"

let expected txs =
  let ts = List.map (fun t -> "T " ^ ok (L.transaction_validate t)) txs in
  let good = List.filter L.transaction_validate txs in
  let accts =
    List.concat_map (fun (t : L.transaction) -> List.map (fun (q : L.posting) -> q.account) t.postings) good
    |> List.sort_uniq compare
  in
  let bs = List.map (fun a -> Printf.sprintf "B %d %d" a (L.ledger_balance_of a good)) accts in
  ts @ [ "L " ^ ok (L.ledger_valid txs) ] @ bs

let trunc s = if String.length s > 600 then String.sub s 0 600 ^ "...[truncated]" else s
