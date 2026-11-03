import Lean
/-!
# Emit: print the Lean definitions in `Ledger.Defs` as plain OCaml

This is ordinary text generation, not an extraction framework. It reads the
kernel term of each requested definition from the compiled environment and
pretty-prints it, but ONLY for the small subset below; anything else is a hard
error that names the declaration and the offending constant.

## Supported subset
Types : `Int` `Nat` (-> `int`), `Bool`, `List α`, arrows, and `Spec.*`
        structures (-> records) and `abbrev` type aliases.
Terms : variables, `fun`, `let`, `if`/`cond`, `true`/`false`, `Spec.*` constants
        and fully-applied `Spec.*` functions, structure constructors/projections,
        Int/Nat literals, `+ * -` (`-` Int only: Nat's truncating `-` is rejected),
        unary `-` (Int), `&& || !`, `decide` of `≤ < ≥ > = ≠ ∧ ∨ ¬` on Int/Nat/Bool,
        and `List.{nil,cons,foldr,map,filter,all,length}` (fully applied).
        Recursion = `List.foldr`; there is no `match`, no general recursion,
        no division, no typeclass-polymorphic code.
Instance and type arguments of the supported heads are dropped (they carry no
runtime content); that is the only place where the Lean term is not printed
verbatim, and it is where the generator is trusted.
-/
open Lean Meta

namespace Emit

def defaultModule : Name := `Ledger.Defs
/-- Public interface of the generated module, in order. -/
def defaultRoots : List Name :=
  [`Spec.maxAmount, `Spec.maxPostings, `Spec.maxLedgerPostings,
   `Spec.Transaction.sum, `Spec.Transaction.validate,
   `Spec.Ledger.valid, `Spec.Ledger.balanceOf]

/-! ## Names -/

def ocamlKeywords : List String :=
  ["and","as","assert","begin","class","constraint","do","done","downto","else","end",
   "exception","external","false","for","fun","function","functor","if","in","include",
   "inherit","initializer","lazy","let","match","method","module","mutable","new",
   "nonrec","object","of","open","or","private","rec","sig","struct","then","to","true",
   "try","type","val","virtual","when","while","with"]

def snake (s : String) : String :=
  s.foldl (fun acc c =>
    if c.isUpper then (if acc.isEmpty then acc else acc ++ "_") ++ c.toLower.toString
    else acc.push c) ""

def safeIdent (s : String) : String :=
  if ocamlKeywords.contains s then s ++ "_" else s

/-- `Spec.Ledger.balanceOf` -> `ledger_balance_of`. -/
def ocamlName (n : Name) : String :=
  safeIdent ("_".intercalate ((n.components.drop 1).map (snake ·.toString)))

def inSpec (n : Name) : Bool := (`Spec).isPrefixOf n && n != `Spec

/-! ## Types -/

partial def ty (e : Expr) : MetaM String := do
  match e with
  | .const n _ =>
    match n.toString with
    | "Int" | "Nat" => pure "int"
    | "Bool" => pure "bool"
    | _ => if inSpec n then pure (ocamlName n) else throwError "unsupported type `{n}`"
  | .app (.const ``List _) a =>
    let s ← ty a
    pure (if s.contains '>' then s!"({s}) list" else s!"{s} list")
  | .forallE _ a b _ =>
    if b.hasLooseBVars then throwError "unsupported dependent type `{e}`"
    let sa ← ty a
    let sb ← ty b
    pure (if sa.contains '>' then s!"({sa}) -> {sb}" else s!"{sa} -> {sb}")
  | _ => throwError "unsupported type `{e}`"

/-! ## Terms -/

structure Names where
  used : Std.HashSet String := {}
  map : Std.HashMap FVarId String := {}

abbrev EM := StateRefT Names MetaM

def pad (n : Nat) : String := "".pushn ' ' n
def fits (s : String) : Bool := s.length ≤ 76 && !s.contains '\n'

/-- Remove one pair of redundant outer parentheses. -/
def stripOuter (s : String) : String := Id.run do
  let cs := s.toList
  if cs.head? != some '(' || cs.getLast? != some ')' then return s
  let mut depth : Int := 0
  let mut i := 0
  for c in cs do
    if c == '(' then depth := depth + 1
    if c == ')' then depth := depth - 1
    if depth == 0 && i != cs.length - 1 then return s
    i := i + 1
  return String.ofList (cs.drop 1 |>.dropLast)

/-- `(head a b c)`, one line if it fits, else one argument per line. -/
def mkApp (ind : Nat) (head : String) (args : List String) : String :=
  let one := " ".intercalate (head :: args)
  if fits one then s!"({one})"
  else s!"({head}\n" ++ "\n".intercalate (args.map (pad (ind + 2) ++ ·)) ++ ")"

/-- `(a OP b OP c)`, one line if it fits, else leading operators. -/
def mkChain (ind : Nat) (op : String) (xs : List String) : String :=
  let one := s!" {op} ".intercalate xs
  if fits one then s!"({one})"
  else match xs with
    | [] => "()"
    | x :: rest => "(" ++ x ++ ("".intercalate (rest.map fun r => s!"\n{pad (ind + 1)}{op} {r}")) ++ ")"

def freshName (base : String) : EM String := do
  let st ← get
  let mut cand := safeIdent (snake base)
  if cand.isEmpty then cand := "x"
  let mut k := 1
  while st.used.contains cand do
    cand := s!"{safeIdent (snake base)}_{k}"
    k := k + 1
  modify fun s => { s with used := s.used.insert cand }
  pure cand

def bind (x : Expr) : EM String := do
  let d ← x.fvarId!.getDecl
  let nm ← freshName d.userName.eraseMacroScopes.toString
  modify fun s => { s with map := s.map.insert x.fvarId! nm }
  pure nm

def isNum (t : Expr) : MetaM Bool := do
  let t ← whnfR t
  pure (t.isConstOf ``Int || t.isConstOf ``Nat)
def isInt (t : Expr) : MetaM Bool := do pure ((← whnfR t).isConstOf ``Int)
def isScalar (t : Expr) : MetaM Bool := do
  let t ← whnfR t
  pure (t.isConstOf ``Int || t.isConstOf ``Nat || t.isConstOf ``Bool)

def bad {α} (what : String) (e : Expr) : EM α :=
  throwError "unsupported {what}: `{e}`"

mutual
partial def pe (ind : Nat) (e : Expr) : EM String := do
  match e with
  | .mdata _ e => pe ind e
  | .fvar id =>
    match (← get).map[id]? with
    | some s => pure s
    | none => bad "free variable" e
  | .lam .. =>
    lambdaTelescope e fun xs body => do
      let mut ps := #[]
      for x in xs do
        let nm ← bind x
        ps := ps.push s!"({nm} : {← ty (← inferType x)})"
      let b ← pe (ind + 2) body
      let head := s!"(fun {" ".intercalate ps.toList} ->"
      let one := s!"{head} {b})"
      pure (if fits one then one else s!"{head}\n{pad (ind + 2)}{b})")
  | .letE n t v b _ =>
    let sv ← pe (ind + 2) v
    withLetDecl n t v fun x => do
      let nm ← bind x
      let sb ← pe ind (b.instantiate1 x)
      pure s!"(let {nm} = {sv} in\n{pad ind}{sb})"
  | .proj sn i s =>
    let fs := getStructureFields (← getEnv) sn
    pure s!"{← pe ind s}.{safeIdent fs[i]!.toString}"
  | .const .. | .app .. =>
    match e.getAppFn with
    | .const n _ => peApp ind n e.getAppArgs
    | f => bad "application head" f
  | _ => bad "expression" e

partial def peApp (ind : Nat) (n : Name) (args : Array Expr) : EM String := do
  let env ← getEnv
  let need (k : Nat) : EM Unit :=
    unless args.size == k do
      throwError "`{n}` must be applied to exactly {k} arguments here (got {args.size})"
  let sub (i : Nat) : EM String := pe (ind + 2) args[i]!
  let binop (op : String) : EM String := do
    need 6
    for i in [0:3] do
      unless (← isNum args[i]!) do throwError "`{n}` on non-Int/Nat type `{args[i]!}`"
    pure s!"({← sub 4} {op} {← sub 5})"
  match n.toString with
  | "OfNat.ofNat" =>
    need 3
    unless (← isNum args[0]!) do throwError "numeric literal of type `{args[0]!}`"
    match args[1]! with
    | .lit (.natVal v) => pure (toString v)
    | a => bad "literal" a
  | "HAdd.hAdd" => binop "+"
  | "HMul.hMul" => binop "*"
  | "HSub.hSub" =>
    unless (← isInt args[0]!) do
      throwError "subtraction on `{args[0]!}`: Nat `-` truncates, OCaml's does not"
    binop "-"
  | "Neg.neg" =>
    need 3
    unless (← isInt args[0]!) do throwError "`Neg.neg` on non-Int type"
    pure s!"(-{← sub 2})"
  | "Bool.true" => pure "true"
  | "Bool.false" => pure "false"
  | "Bool.and" => need 2; chain ind "&&" (args.toList) (isAnd := true)
  | "Bool.or" => need 2; chain ind "||" (args.toList) (isAnd := false)
  | "Bool.not" | "not" => need 1; pure s!"(not {← sub 0})"
  | "Decidable.decide" => need 2; pp ind args[0]!
  | "ite" =>
    need 5
    mkIf ind (← pp (ind + 4) args[1]!) (← sub 3) (← sub 4)
  | "cond" =>
    need 4
    mkIf ind (← sub 1) (← sub 2) (← sub 3)
  | "List.foldr" =>
    need 5
    pure (mkApp ind "List.fold_right" [← sub 2, ← sub 4, ← sub 3])
  | "List.map" => need 4; pure (mkApp ind "List.map" [← sub 2, ← sub 3])
  | "List.filter" => need 3; pure (mkApp ind "List.filter" [← sub 1, ← sub 2])
  | "List.all" => need 3; pure (mkApp ind "List.for_all" [← sub 2, ← sub 1])
  | "List.length" => need 2; pure (mkApp ind "List.length" [← sub 1])
  | "List.nil" => need 1; pure "[]"
  | "List.cons" => need 3; pure s!"({← sub 1} :: {← sub 2})"
  | _ =>
    unless inSpec n do
      throwError "constant `{n}` is outside the supported subset"
    if let some _ := env.getProjectionFnInfo? n then
      need 1
      pure s!"{← sub 0}.{safeIdent n.getString!}"
    else match env.find? n with
      | some (.ctorInfo c) =>
        need c.numFields
        let fs := getStructureFields env c.induct
        let kvs ← fs.toList.mapIdxM fun i f => do pure s!"{safeIdent f.toString} = {← sub i}"
        pure ("{ " ++ "; ".intercalate kvs ++ " }")
      | some (.defnInfo _) =>
        if args.isEmpty then pure (ocamlName n)
        else pure (mkApp ind (ocamlName n) (← args.toList.mapM (pe (ind + 2))))
      | _ => throwError "declaration `{n}` is outside the supported subset"

partial def chain (ind : Nat) (op : String) (args : List Expr) (isAnd : Bool) : EM String := do
  -- flatten nested `&&` / `||` (associative, evaluation order preserved)
  let rec flat (e : Expr) : List Expr :=
    match e.getAppFnArgs with
    | (n, #[a, b]) =>
      if (isAnd && n == ``Bool.and) || (!isAnd && n == ``Bool.or) then flat a ++ flat b else [e]
    | _ => [e]
  let parts := args.flatMap flat
  pure (mkChain ind op (← parts.mapM (pe (ind + 1))))

partial def mkIf (ind : Nat) (c a b : String) : EM String := do
  let one := s!"if {c} then {a} else {b}"
  pure (if fits one then s!"({one})"
        else s!"(if {c}\n{pad (ind + 1)}then {a}\n{pad (ind + 1)}else {b})")

/-- A `Prop` appearing under `decide`, printed as an OCaml `bool` expression. -/
partial def pp (ind : Nat) (p : Expr) : EM String := do
  let args := p.getAppArgs
  let sub (i : Nat) : EM String := pe (ind + 2) args[i]!
  let cmp (op : String) : EM String := do
    unless args.size == 4 && (← isNum args[0]!) do throwError "unsupported comparison `{p}`"
    pure s!"({← sub 2} {op} {← sub 3})"
  match p.getAppFn with
  | .const n _ =>
    match n.toString with
    | "LE.le" => cmp "<="
    | "LT.lt" => cmp "<"
    | "GE.ge" => cmp ">="
    | "GT.gt" => cmp ">"
    | "Eq" | "Ne" =>
      unless args.size == 3 && (← isScalar args[0]!) do throwError "unsupported equality `{p}`"
      pure s!"({← sub 1} {if n == ``Eq then "=" else "<>"} {← sub 2})"
    | "And" => unless args.size == 2 do bad "proposition" p
               pure (mkChain ind "&&" [← pp (ind + 1) args[0]!, ← pp (ind + 1) args[1]!])
    | "Or" => unless args.size == 2 do bad "proposition" p
              pure (mkChain ind "||" [← pp (ind + 1) args[0]!, ← pp (ind + 1) args[1]!])
    | "Not" => unless args.size == 1 do bad "proposition" p
               pure s!"(not {← pp (ind + 2) args[0]!})"
    | "True" => pure "true"
    | "False" => pure "false"
    | _ => bad "proposition" p
  | _ => bad "proposition" p
end

/-! ## Declarations -/

inductive Kind | struct | alias | value

structure Plan where
  seen : NameSet := {}
  types : Array Name := #[]
  values : Array Name := #[]

/-- What is `n`? Constructors and projections redirect to their structure. -/
def classify (n : Name) : MetaM (Option Name ⊕ Kind) := do
  let env ← getEnv
  if isStructure env n then return .inr .struct
  if let some pi := env.getProjectionFnInfo? n then
    return .inl (some (← getConstInfoCtor pi.ctorName).induct)
  match env.find? n with
  | some (.ctorInfo c) => return .inl (some c.induct)
  | some (.defnInfo d) =>
    return .inr (if d.type == mkSort Level.one then .alias else .value)
  | _ => throwError "declaration `{n}` is outside the supported subset \
        (only structures, type abbreviations and plain definitions can be emitted)"

partial def visit (n : Name) : StateT Plan MetaM Unit := do
  if (← get).seen.contains n then return
  modify fun p => { p with seen := p.seen.insert n }
  try
    match ← classify n with
    | .inl none => pure ()
    | .inl (some s) => visit s
    | .inr k =>
      let info ← getConstInfo n
      let env ← getEnv
      let deps :=
        match k with
        | .struct => info.type.getUsedConstants ++ (getStructureCtor env n).type.getUsedConstants
        | _ => info.type.getUsedConstants ++ (match info.value? with | some v => v.getUsedConstants | none => #[])
      for d in deps do
        if inSpec d && d != n then visit d
      match k with
      | .value => modify fun p => { p with values := p.values.push n }
      | _ => modify fun p => { p with types := p.types.push n }
  catch e =>
    throwError "while emitting `{n}`: {e.toMessageData}"

def docComment (n : Name) : MetaM String := do
  match ← findDocString? (← getEnv) n with
  | none => pure ""
  | some d =>
    let d := (d.trimAscii.toString.replace "(*" "( *").replace "*)" "* )"
      |>.replace "\"" "'" |>.replace "`" "'"
    pure s!"(* {" ".intercalate (d.splitOn.filter (· ≠ ""))} *)\n"

def typeDecl (n : Name) : MetaM String := do
  let env ← getEnv
  let doc ← docComment n
  if isStructure env n then
    let ctor := getStructureCtor env n
    forallTelescope ctor.type fun xs _ => do
      let fs := getStructureFields env n
      let mut lines := #[]
      for h : i in [0:xs.size] do
        lines := lines.push s!"  {safeIdent fs[i]!.toString} : {← ty (← inferType xs[i])};"
      pure (doc ++ s!"type {ocamlName n} = \{\n{"\n".intercalate lines.toList}\n}")
  else
    pure (doc ++ s!"type {ocamlName n} = {← ty (← getConstInfo n).value!}")

def valDecl (n : Name) : MetaM String := do
  let info ← getConstInfoDefn n
  let doc ← docComment n
  lambdaTelescope info.value fun xs body => do
    let (s, _) ← (do
      let mut ps := #[]
      for x in xs do
        let nm ← bind x
        ps := ps.push s!" ({nm} : {← ty (← inferType x)})"
      let b ← pe 2 body
      let ret ← ty (← inferType body)
      pure s!"let {ocamlName n}{"".intercalate ps.toList} : {ret} =\n  {stripOuter b}\n" : EM String).run {}
    pure (doc ++ s)

def valSig (n : Name) : MetaM String := do
  pure ((← docComment n) ++ s!"val {ocamlName n} : {← ty (← getConstInfo n).type}")

def generate (module : Name) (roots : List Name) : MetaM (String × String) := do
  let env ← getEnv
  unless env.contains module do pure ()
  let ((), plan) ← (do for r in roots do visit r : StateT Plan MetaM Unit).run {}
  let ctx {α} (n : Name) (x : MetaM α) : MetaM α :=
    try x catch e => throwError "in `{n}`: {e.toMessageData}"
  let tys ← plan.types.mapM fun n => ctx n (typeDecl n)
  let vals ← plan.values.mapM fun n => ctx n (valDecl n)
  let sigs ← roots.mapM valSig
  let inventory := (plan.types ++ plan.values).toList.map fun n =>
    s!"     {n} -> {ocamlName n}"
  let header := s!"(* GENERATED FILE -- DO NOT EDIT.\n\n   Written by domain/Emit.lean (`cd domain && lake exe emit ../gen`) from the\n   Lean module {module}. Lean declarations emitted, in order:\n" ++
    "\n".intercalate inventory ++
    "\n\n   Interface: see ledger_gen.mli. Pure: no I/O, no state, no exceptions.\n   Regenerate with scripts/gen.sh; scripts/check-gen.sh fails CI on any drift.\n   Trusted, not proved: this translation and the OCaml compiler. The Lean\n   theorems are about the Lean definitions; this file is tested against them. *)\n\n"
  let tydefs := "\n\n".intercalate tys.toList
  let ml := header ++ tydefs ++ "\n\n" ++ "\n".intercalate vals.toList
  let mli := header.replace "Interface: see ledger_gen.mli. Pure" "This is the interface of ledger_gen.ml. Pure" ++ tydefs ++ "\n\n" ++ "\n\n".intercalate sigs ++ "\n"
  pure (ml, mli)

def run (outDir : String) (module : Name) (roots : List Name) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module }] {}
  let act := (generate module roots).run' {}
  try
    let (ml, mli) ← (act.toIO { fileName := "<emit>", fileMap := default } { env }).map (·.1)
    IO.FS.createDirAll outDir
    IO.FS.writeFile s!"{outDir}/ledger_gen.ml" ml
    IO.FS.writeFile s!"{outDir}/ledger_gen.mli" mli
    pure 0
  catch e =>
    IO.eprintln s!"emit: error: {e}"
    pure 1

end Emit

/-- `emit <outdir> [--module M --root N ...]`. Without flags: Ledger.Defs + default roots. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [] => IO.eprintln "usage: emit <outdir> [--module <Module> --root <Decl> ...]"; pure 2
  | out :: rest =>
    let rec go (a : List String) (m : Name) (rs : List Name) : IO UInt32 :=
      match a with
      | "--module" :: v :: t => go t v.toName rs
      | "--root" :: v :: t => go t m (rs ++ [v.toName])
      | [] => Emit.run out m (if rs.isEmpty then Emit.defaultRoots else rs)
      | x :: _ => do IO.eprintln s!"emit: unknown argument {x}"; pure 2
    go rest Emit.defaultModule []
