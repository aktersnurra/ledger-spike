(* Property-based tests with Hegel (shrinking, engine-driven generation).

   1. oracle_agrees: generated OCaml = Lean oracle, on random ledgers. The Lean oracle
      is ONE long-lived process driven case by case over pipes.
   2. Oracle-free properties of the generated code. Lean proves these for the model;
      here they check the implementation actually has them.

   env: LEDGER_ORACLE (required), LEDGER_SEED (default 1), LEDGER_PBT_CASES (default 1000) *)
open Hegel
module L = Ledger_gen
open Support

let env_int name d = match Sys.getenv_opt name with Some s -> int_of_string s | None -> d
let seed = env_int "LEDGER_SEED" 1
let cases = env_int "LEDGER_PBT_CASES" 1000
let settings n = Settings.create ~test_cases:n ~seed ()
let m = L.max_amount
let p account amount : L.posting = { account; amount }
let tx ps : L.transaction = { postings = ps }

(* ---------- the oracle as a persistent subprocess ---------- *)
let session =
  lazy
    (let path =
       match Sys.getenv_opt "LEDGER_ORACLE" with
       | Some o -> o
       | None -> Alcotest.fail "LEDGER_ORACLE not set: run scripts/verify.sh"
     in
     let ic, oc = Unix.open_process_args path [| path |] in
     at_exit (fun () -> ignore (Unix.close_process (ic, oc)));
     (ic, oc))

let ask text =
  let ic, oc = Lazy.force session in
  output_string oc text;
  flush oc;
  let rec go acc =
    match input_line ic with
    | "." -> List.rev acc
    | l -> go (l :: acc)
    | exception End_of_file -> failwith "oracle closed its output"
  in
  go []

(* ---------- generators: plain functions of the test case ---------- *)
let int tc lo hi = draw_silent tc (integers ~min_value:lo ~max_value:hi ())
let pick tc l = draw_silent tc (sampled_from l)
let list_of tc lo hi f = List.init (int tc lo hi) (fun _ -> f tc)

let boundary =
  [ 0; 1; -1; m; -m; m - 1; 1 - m; m + 1; -(m + 1); 2 * m; max_int; min_int; max_int - 1; min_int + 1 ]

let account tc = if int tc 0 24 = 0 then pick tc [ max_int; min_int; -1; 0 ] else int tc 0 5
let small_posting tc = let a = account tc in p a (int tc (-1000) 1000)
let sum ps = List.fold_left (fun a (q : L.posting) -> a + q.amount) 0 ps

let balanced tc =
  let body = list_of tc 1 6 small_posting in
  tx (body @ [ p (account tc) (-sum body) ])

let max_size n = tx (List.init n (fun i -> p (i mod 4) (if i mod 2 = 0 then m else -m)))

(* Big structures are built from a single draw, so the shrinker (which minimises the
   number of choices, not the size of the value) treats them as "simple" and reports
   a 1000-posting counterexample even when a 2-posting one exists. Hence [~big]:
   properties run once without it (small, shrinkable) and once with it (boundaries). *)
let valid_tx ~big tc =
  match int tc 0 9 with
  | 0 -> let a = pick tc [ m; -m; m - 1; 0 ] in tx [ p (account tc) a; p (account tc) (-a) ]
  | 1 when big -> max_size (2 * int tc 1 500)
  | _ -> balanced tc

let big_tx tc =
  match int tc 0 1 with
  | 0 -> max_size (int tc 998 1004) (* straddles max_postings *)
  | _ -> tx (List.init 999 (fun i -> p i m) @ [ p 999 (-999 * m) ]) (* balanced, one amount out of bounds *)

let special tc =
  match int tc 0 9 with
  | 0 -> tx []
  | 1 -> tx [ p (account tc) (pick tc boundary) ]
  | 2 -> tx [ p 1 (m + 1); p 2 (-(m + 1)) ]
  | 5 -> tx [ p 1 max_int; p 2 max_int; p 3 2 ] (* wraps to 0 in 63-bit *)
  | 6 -> tx [ p 1 min_int; p 2 min_int ]
  | 7 -> tx [ p 5 7; p 5 (-7) ]
  | 8 -> tx [ p 1 0; p 2 0 ]
  | _ -> tx (list_of tc 1 4 (fun tc -> p (account tc) (pick tc boundary)))

let any_tx ~big tc =
  match int tc 0 3 with
  | 0 -> tx (list_of tc 0 6 (fun tc -> let a = account tc in p a (pick tc boundary)))
  | 1 when big -> big_tx tc
  | 1 -> special tc
  | 2 -> special tc
  | _ -> balanced tc

let any_ledger ~big tc = list_of tc 0 6 (any_tx ~big)
let valid_ledger ~big tc = list_of tc 0 6 (valid_tx ~big)

(* ---------- properties ---------- *)
(* coverage of the oracle property, so a degenerate generator cannot pass quietly *)
let n_runs = ref 0 and n_tx = ref 0 and n_valid = ref 0 and n_ledgers_ok = ref 0

let oracle_agrees ~big tc =
  let txs = if int tc 0 2 = 0 then valid_ledger ~big tc else any_ledger ~big tc in
  incr n_runs;
  n_tx := !n_tx + List.length txs;
  n_valid := !n_valid + List.length (List.filter L.transaction_validate txs);
  if L.ledger_valid txs then incr n_ledgers_ok;
  let text = case_text txs in
  note tc (trunc text);
  let e = expected txs and g = ask text in
  if e <> g then
    failwith (Printf.sprintf "ocaml and lean differ\n-- ocaml --\n%s\n-- lean --\n%s" (String.concat "\n" e) (String.concat "\n" g))

let accounts l =
  List.concat_map (fun (t : L.transaction) -> List.map (fun (q : L.posting) -> q.account) t.postings) l
  |> List.sort_uniq compare

(* The double-entry invariant, on the implementation: balances of all accounts cancel. *)
let balances_cancel tc =
  let l = valid_ledger ~big:true tc in
  assert (L.ledger_valid l);
  assert (List.fold_left (fun s a -> s + L.ledger_balance_of a l) 0 (accounts l) = 0)

let balance_additive tc =
  let l1 = valid_ledger ~big:false tc and l2 = valid_ledger ~big:false tc in
  let a = if int tc 0 3 = 0 then account tc else pick tc (accounts (l1 @ l2) @ [ 0 ]) in
  assert (L.ledger_balance_of a (l1 @ l2) = L.ledger_balance_of a l1 + L.ledger_balance_of a l2)

let append_validity tc =
  let l = any_ledger ~big:true tc and t = any_tx ~big:true tc in
  assert (L.ledger_valid (l @ [ t ]) = (L.ledger_valid l && L.transaction_validate t))

let oracle_prop name ~big n =
  Alcotest.test_case name `Slow (fun () ->
      n_runs := 0; n_tx := 0; n_valid := 0; n_ledgers_ok := 0;
      run_hegel_test ~settings:(settings n) (oracle_agrees ~big);
      Printf.printf "seed=%d runs=%d txs=%d (valid %d, invalid %d) valid-ledgers=%d\n%!" seed !n_runs !n_tx
        !n_valid (!n_tx - !n_valid) !n_ledgers_ok;
      Alcotest.(check bool) "enough valid txs" true (!n_valid * 5 > !n_tx);
      Alcotest.(check bool) "enough invalid txs" true ((!n_tx - !n_valid) * 5 > !n_tx);
      Alcotest.(check bool) "enough valid ledgers" true (!n_ledgers_ok * 10 > !n_runs))

(* The ledger-size bound (10^6 postings) is unreachable by 6-transaction ledgers, so probe it
   directly: k copies of a valid 1000-posting transaction, k straddling 1000.
   Expected values are derived independently of the generated code. *)
let ledger_size_boundary tc =
  let k = int tc 998 1002 in
  let t = max_size 1000 in
  let l = List.init k (fun _ -> t) in
  assert (L.ledger_valid l = (k <= 1000));
  (* max_size: account 0 gets +10^12 on 250 of the 1000 postings per tx *)
  if k <= 1000 then assert (L.ledger_balance_of 0 l = k * 250 * m)

let prop name n f = Alcotest.test_case name `Slow (fun () -> run_hegel_test ~settings:(settings n) f)

let () =
  Alcotest.run "pbt"
    [ ( "hegel",
        [ oracle_prop "ocaml = lean oracle (small, shrinkable)" ~big:false cases;
          oracle_prop "ocaml = lean oracle (size boundaries)" ~big:true (cases / 2);
 prop "ledger size boundary (10^6 postings)" 50 ledger_size_boundary;
          prop "balances of all accounts cancel" (cases / 3) balances_cancel;
          prop "balance_of is additive over append" (cases / 3) balance_additive;
          prop "ledger_valid (l @ [t]) = ledger_valid l && validate t" (cases / 3) append_validity ] ) ]
