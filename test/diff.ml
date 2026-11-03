(* Differential test: generated OCaml vs the Lean oracle, seeded and reproducible.

   env: LEDGER_ORACLE  path to the oracle exe (required; scripts/verify.sh sets it)
        LEDGER_SEED    default 1
        LEDGER_CASES   random cases, default 3000
   Replay a failure with the same LEDGER_SEED. *)
module L = Ledger_gen

let env_int name d = match Sys.getenv_opt name with Some s -> int_of_string s | None -> d
let seed = env_int "LEDGER_SEED" 1
let n_cases = env_int "LEDGER_CASES" 3000
let m = L.max_amount

let p account amount : L.posting = { account; amount }
let tx ps : L.transaction = { postings = ps }

(* ---------- generators ---------- *)
let pick rng a = a.(Random.State.int rng (Array.length a))
let small rng = Random.State.int rng 2001 - 1000

let boundary =
  [| 0; 1; -1; m; -m; m - 1; 1 - m; m + 1; -(m + 1); 2 * m; max_int; min_int; max_int - 1; min_int + 1 |]

let acct rng =
  if Random.State.int rng 25 = 0 then pick rng [| max_int; min_int; -1; 0 |]
  else Random.State.int rng 6

let amt rng = if Random.State.int rng 3 = 0 then pick rng boundary else small rng

(* balanced by construction *)
let balanced rng =
  let k = 1 + Random.State.int rng 7 in
  let body = List.init k (fun _ -> p (acct rng) (small rng)) in
  let s = List.fold_left (fun a (q : L.posting) -> a + q.amount) 0 body in
  tx (body @ [ p (acct rng) (-s) ])

let boundary_pair rng =
  let a = pick rng [| m; -m; m - 1; 0 |] in
  tx [ p (acct rng) a; p (acct rng) (-a) ]

let max_size n = tx (List.init n (fun i -> p (i mod 4) (if i mod 2 = 0 then m else -m)))

let random_tx rng =
  tx (List.init (Random.State.int rng 7) (fun _ -> p (acct rng) (amt rng)))

let special rng =
  match Random.State.int rng 12 with
  | 0 -> tx []
  | 1 -> tx [ p (acct rng) (amt rng) ]
  | 2 -> max_size 1000
  | 3 -> max_size 1002 (* balanced, too many postings *)
  | 4 -> max_size 1001
  | 5 -> tx (List.init 999 (fun i -> p i m) @ [ p 999 (-999 * m) ]) (* balanced, one amount out of bounds *)
  | 6 -> tx [ p 1 (m + 1); p 2 (-(m + 1)) ]
  | 7 -> tx [ p 1 max_int; p 2 max_int; p 3 2 ] (* sum wraps to 0 in 63-bit *)
  | 8 -> tx [ p 1 min_int; p 2 min_int ]
  | 9 -> tx [ p 1 0; p 2 0 ]
  | 10 -> tx [ p 5 7; p 5 (-7) ]
  | _ -> tx (List.init (1 + Random.State.int rng 3) (fun _ -> p (acct rng) 0))

let valid_tx rng =
  match Random.State.int rng 10 with
  | 0 -> boundary_pair rng
  | 1 -> max_size (2 * (1 + Random.State.int rng 500))
  | _ -> balanced rng

let any_tx rng =
  match Random.State.int rng 4 with 0 -> random_tx rng | 1 -> special rng | _ -> balanced rng

let gen_case rng : L.transaction list =
  let n = Random.State.int rng 9 in
  match Random.State.int rng 4 with
  | 0 | 1 -> List.init n (fun _ -> any_tx rng)
  | 2 -> List.init n (fun _ -> valid_tx rng) (* force-valid: exercises accept paths *)
  | _ ->
    (* valid ledger with exactly one replaced (usually corrupt) transaction *)
    let l = List.init (max n 1) (fun _ -> valid_tx rng) in
    let i = Random.State.int rng (List.length l) in
    List.mapi (fun j t -> if i = j then special rng else t) l

(* two ledger-size boundary cases: exactly 10^6 postings, and 10^6 + 2 *)
let big_tx = tx (List.init 500 (fun _ -> p 1 m) @ List.init 500 (fun _ -> p 2 (-m)))
let big_cases () =
  let l = List.init 1000 (fun _ -> big_tx) in
  [ l; tx [ p 1 1; p 2 (-1) ] :: l ]

(* ---------- text format and expected output ---------- *)
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

(* ---------- run ---------- *)
let read_lines file =
  let ic = open_in file in
  let rec go acc = match input_line ic with l -> go (l :: acc) | exception End_of_file -> List.rev acc in
  let r = go [] in
  close_in ic; r

(* split oracle output into per-case line lists at "." *)
let split_cases lines =
  let rec go cur acc = function
    | [] -> List.rev acc
    | "." :: rest -> go [] (List.rev cur :: acc) rest
    | l :: rest -> go (l :: cur) acc rest
  in
  go [] [] lines

let trunc s = if String.length s > 600 then String.sub s 0 600 ^ "...[truncated]" else s

let differential () =
  let oracle =
    match Sys.getenv_opt "LEDGER_ORACLE" with
    | Some o -> o
    | None -> Alcotest.fail "LEDGER_ORACLE not set: run scripts/verify.sh (it builds the Lean oracle and sets it)"
  in
  let rng = Random.State.make [| seed |] in
  let cases = List.init n_cases (fun _ -> gen_case rng) @ big_cases () in
  let inp = Filename.temp_file "ledger" ".in" and outp = Filename.temp_file "ledger" ".out" in
  let oc = open_out inp in
  List.iter (fun c -> output_string oc (case_text c)) cases;
  close_out oc;
  let rc = Sys.command (Printf.sprintf "%s < %s > %s" (Filename.quote oracle) (Filename.quote inp) (Filename.quote outp)) in
  if rc <> 0 then Alcotest.failf "oracle exited with %d" rc;
  let got = split_cases (read_lines outp) in
  Alcotest.(check int) "oracle answered every case" (List.length cases) (List.length got);
  let n_tx = ref 0 and n_valid = ref 0 and n_ledger_ok = ref 0 in
  List.iteri
    (fun i (c, g) ->
      let e = expected c in
      List.iter (fun t -> incr n_tx; if L.transaction_validate t then incr n_valid) c;
      if L.ledger_valid c then incr n_ledger_ok;
      if e <> g then
        Alcotest.failf "MISMATCH case %d (LEDGER_SEED=%d)\n-- input --\n%s-- ocaml --\n%s\n-- lean oracle --\n%s"
          i seed (trunc (case_text c)) (trunc (String.concat "\n" e)) (trunc (String.concat "\n" g)))
    (List.combine cases got);
  Printf.printf "seed=%d cases=%d txs=%d (valid %d, invalid %d) valid-ledgers=%d\n%!" seed (List.length cases)
    !n_tx !n_valid (!n_tx - !n_valid) !n_ledger_ok;
  (* guard against a degenerate generator: both paths must be well exercised *)
  Alcotest.(check bool) "enough valid txs" true (!n_valid * 5 > !n_tx);
  Alcotest.(check bool) "enough invalid txs" true ((!n_tx - !n_valid) * 5 > !n_tx);
  Alcotest.(check bool) "enough valid ledgers" true (!n_ledger_ok * 10 > List.length cases)

let () = Alcotest.run "diff" [ ("oracle", [ Alcotest.test_case "ocaml = lean" `Slow differential ]) ]
