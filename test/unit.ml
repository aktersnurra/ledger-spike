(* Targeted unit tests: boundaries and the int63 overflow argument. *)
module L = Ledger_gen

let p account amount : L.posting = { account; amount }
let tx ps : L.transaction = { postings = ps }
let m = L.max_amount

let check_bool name expected actual = Alcotest.(check bool) name expected actual

let validate_cases () =
  let v ps = L.transaction_validate (tx ps) in
  check_bool "balanced pair" true (v [ p 1 5; p 2 (-5) ]);
  check_bool "zero amounts, two postings" true (v [ p 1 0; p 2 0 ]);
  check_bool "same account both sides" true (v [ p 1 7; p 1 (-7) ]);
  check_bool "three-way split" true (v [ p 1 10; p 2 (-4); p 3 (-6) ]);
  check_bool "empty" false (v []);
  check_bool "single zero posting" false (v [ p 1 0 ]);
  check_bool "single nonzero posting" false (v [ p 1 5 ]);
  check_bool "unbalanced" false (v [ p 1 5; p 2 (-4) ])

let boundary_cases () =
  let v ps = L.transaction_validate (tx ps) in
  Alcotest.(check int) "max_amount is 10^12" 1_000_000_000_000 m;
  Alcotest.(check int) "max_postings" 1000 L.max_postings;
  check_bool "+10^12 / -10^12 ok" true (v [ p 1 m; p 2 (-m) ]);
  check_bool "-10^12 / +10^12 ok" true (v [ p 1 (-m); p 2 m ]);
  check_bool "10^12+1 rejected though balanced" false (v [ p 1 (m + 1); p 2 (-(m + 1)) ]);
  check_bool "-(10^12+1) rejected though balanced" false (v [ p 1 (-(m + 1)); p 2 (m + 1) ]);
  let alt n = List.init n (fun i -> p (i mod 3) (if i mod 2 = 0 then m else -m)) in
  check_bool "1000 postings at the bound" true (v (alt 1000));
  check_bool "1001 postings rejected (odd, unbalanced)" false (v (alt 1001));
  check_bool "1002 postings rejected though balanced" false (v (alt 1002));
  let sum ps = List.fold_left (fun a (q : L.posting) -> a + q.amount) 0 ps in
  Alcotest.(check int) "alt 1002 really sums to 0" 0 (sum (alt 1002))

(* The Lean theorem TxSumFitsInt63 says: inside the bounds the sum fits in 63 bits.
   Here: the platform really is 63-bit, and the extreme cases are exact. *)
let overflow_bound () =
  Alcotest.(check int) "OCaml int is 63-bit (theorem assumes this)" 63 Sys.int_size;
  Alcotest.(check bool) "1000 * 10^12 < max_int" true
    (L.max_postings * m < max_int && L.max_postings * m > 0);
  Alcotest.(check bool) "10^6 * 10^12 < max_int" true
    (L.max_ledger_postings * m < max_int && L.max_ledger_postings * m > 0);
  let all_max = tx (List.init 1000 (fun _ -> p 1 m)) in
  Alcotest.(check int) "sum of 1000 x 10^12 exact" 1_000_000_000_000_000 (L.transaction_sum all_max);
  check_bool "...and (being unbalanced) invalid" false (L.transaction_validate all_max);
  let all_min = tx (List.init 1000 (fun _ -> p 1 (-m))) in
  Alcotest.(check int) "sum of 1000 x -10^12 exact" (-1_000_000_000_000_000) (L.transaction_sum all_min)

(* Why the bounds exist: outside them native ints wrap, and validate must not be fooled. *)
let wrap_hazard () =
  let naive ps = List.fold_left (fun a (q : L.posting) -> a + q.amount) 0 ps in
  let w1 = [ p 1 max_int; p 2 max_int; p 3 2 ] in
  Alcotest.(check int) "naive OCaml sum wraps to 0 (true Lean sum is 2^63)" 0 (naive w1);
  check_bool "validate rejects it" false (L.transaction_validate (tx w1));
  let w2 = [ p 1 min_int; p 2 min_int ] in
  Alcotest.(check int) "naive sum of two min_int wraps to 0" 0 (naive w2);
  check_bool "validate rejects it" false (L.transaction_validate (tx w2))

(* The ledger-level bound: 1000 maximal transactions give balances of +-5*10^17. *)
let big_tx = tx (List.init 500 (fun _ -> p 1 m) @ List.init 500 (fun _ -> p 2 (-m)))

let ledger_bound () =
  let l = List.init 1000 (fun _ -> big_tx) in
  check_bool "1000 x 1000 postings is a valid ledger (exactly 10^6)" true (L.ledger_valid l);
  Alcotest.(check int) "balance of account 1, exact" 500_000_000_000_000_000 (L.ledger_balance_of 1 l);
  Alcotest.(check int) "balance of account 2, exact" (-500_000_000_000_000_000) (L.ledger_balance_of 2 l);
  Alcotest.(check int) "unrelated account" 0 (L.ledger_balance_of 3 l);
  check_bool "one more posting pair exceeds max_ledger_postings" false
    (L.ledger_valid (tx [ p 1 1; p 2 (-1) ] :: l));
  check_bool "ledger with an invalid tx is invalid" false (L.ledger_valid [ tx [] ]);
  check_bool "empty ledger valid" true (L.ledger_valid [])

let balance_cases () =
  let l = [ tx [ p 1 10; p 2 (-10) ]; tx [ p 2 3; p 1 (-3); p 3 0 ] ] in
  Alcotest.(check int) "acct 1" 7 (L.ledger_balance_of 1 l);
  Alcotest.(check int) "acct 2" (-7) (L.ledger_balance_of 2 l);
  Alcotest.(check int) "acct 3" 0 (L.ledger_balance_of 3 l);
  Alcotest.(check int) "empty ledger" 0 (L.ledger_balance_of 1 [])

let () =
  Alcotest.run "unit"
    [ ( "ledger_gen",
        [ Alcotest.test_case "validate" `Quick validate_cases;
          Alcotest.test_case "boundaries" `Quick boundary_cases;
          Alcotest.test_case "int63 bound" `Quick overflow_bound;
          Alcotest.test_case "wrap hazard" `Quick wrap_hazard;
          Alcotest.test_case "ledger bound" `Quick ledger_bound;
          Alcotest.test_case "balances" `Quick balance_cases ] ) ]
