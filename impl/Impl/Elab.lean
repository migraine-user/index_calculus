import Impl.Interpreter
import Impl.Syntax
import Impl.TypeCheck
open Lean Elab Meta Term Syntax

declare_syntax_cat _term
declare_syntax_cat place
declare_syntax_cat range
declare_syntax_cat bin_op

-- entry
syntax "(lang|" _term ")" : term

syntax  num: _term
syntax "for " ident " : " range " in " _term: _term
syntax "let " ident " := " _term " in " _term: _term
syntax "(" _term ", " _term ")" : _term
syntax "if " ident " ≤  " num " then " _term " else " _term: _term

syntax num"⋯"num: range
syntax "empty" : range
syntax " + ": bin_op
syntax " * ": bin_op
syntax " - ": bin_op
syntax " / ": bin_op

syntax ident : place
syntax place "[" _term "]" : place
syntax place ".fst" : place
syntax place ".snd" : place

syntax place : _term

syntax scientific: _term
syntax _term bin_op _term: _term

syntax "(" _term ")" : _term

def mkFloatLit (x : Nat × Bool × Nat)  : Expr :=
  let (n, b, m) := x
  let n := Lean.mkNatLit n
  let m := Lean.mkNatLit m
  if b then
    mkApp3 (mkConst ``Float.ofScientific []) n (.const ``Bool.true []) m
  else
    mkApp3 (mkConst ``Float.ofScientific []) n (.const ``Bool.false []) m


mutual
partial def elabRange : Syntax -> MetaM Expr
  | `(range| empty ) => pure $ mkConst ``Range.empty []
  | `(range| $a:num⋯$b:num) => pure $
    mkApp2
    (mkConst ``Range.range [])
    (mkNatLit a.getNat)
    (mkNatLit b.getNat)
  | _ => throwUnsupportedSyntax

partial def elabTerm : Syntax -> MetaM Expr
  | `(_term| ($t:_term)) => elabTerm t
  | `(_term| $f:scientific) => mkAppM ``floatLit #[mkFloatLit f.getScientific]
  | `(_term| $a:_term $op:bin_op $b:_term) => do
    let aa <- elabTerm a
    let bb <- elabTerm b
    let op <- match op with
    | `(bin_op| + ) => pure ``Arith.plus
    | `(bin_op| - ) => pure ``Arith.minus
    | `(bin_op| / ) => pure ``Arith.divide
    | `(bin_op| * ) => pure ``Arith.times
    | _ => throwUnsupportedSyntax
    return (mkApp3
    (mkConst ``Term.binary [])
    aa
    (mkConst op [])
    bb)
  | `(_term| $p:place) => do
    let p <- elabPlace p
    mkAppM ``Term.place #[p]
  | `(_term| $n:num) => do
    let n := Lean.mkNatLit n.getNat
    mkAppM ``Term.natLit #[n]
  | `(num| $n:num) => do
    let n := Lean.mkNatLit n.getNat
    mkAppM ``Term.natLit #[n]
  | `(_term| ( $l, $r) ) => do
    let l <- elabTerm l
    let r <- elabTerm r
    pure $ mkApp2 (mkConst ``Term.tuple []) l r
  | `(_term| let $x := $t in $t_in) => do
    let x :=  Lean.mkApp (mkConst ``Ident.ident []) (x.getId.toString |> mkStrLit)
    let t <- elabTerm t
    let t_in <- elabTerm t_in
    pure $ mkApp3 (mkConst ``Term.let_ []) x t t_in
  | `(_term| if $l:ident ≤  $r:num then $t_if:_term else $t_else:_term) => do
    let i := Lean.mkApp (mkConst ``Ident.ident []) (l.getId.toString |> mkStrLit)
    let r <- elabTerm r
    let t_if <- elabTerm t_if
    let t_else <- elabTerm t_else
    let cond := mkApp2 (mkConst ``Leq.leq []) i r
    mkAppM ``Term.ternary #[cond, t_if, t_else]
  | `(_term| for $i : $r in $t) => do
    let i := Lean.mkApp (mkConst ``Ident.ident []) (i.getId.toString |> Lean.mkStrLit)
    let r <- elabRange r
    let t <- elabTerm t
    mkAppM ``Term.for_ #[i, r, t]
  | s => throwError (toString s)
partial def elabPlace : Syntax -> MetaM Expr
  | `(place| $p:ident) =>
    let strLit := p.getId.toString |> Lean.mkStrLit
    let identIdent := mkApp (mkConst ``Ident.ident []) strLit
    let placeExpr := mkApp (mkConst ``PlaceExpr.ident []) identIdent
    pure placeExpr
  | `(place| $p:place[$t:_term]) => do
    let lhs <- elabPlace p
    let i <- elabTerm t
    let iExpr <- mkAppM ``IndexExpr.mk #[lhs, i]
    mkAppM ``PlaceExpr.index #[iExpr]
  | `(place| $p:place .fst) => do
      let inner <- elabPlace p
      pure $ mkApp (mkConst ``PlaceExpr.fst []) inner
  | `(place| $p:place .snd) => do
    let inner <- elabPlace p
    pure $ mkApp (mkConst ``PlaceExpr.snd []) inner
  | _ => throwUnsupportedSyntax

end
#eval `(place| a[1])
#check `( _term| 1 )
elab "test_elabPlace" t:place : term => elabPlace t
#eval test_elabPlace a[1]
elab "test_elabRange" t:range : term => elabRange t

#eval test_elabRange 1⋯2
elab "test_elabTerm" t:_term : term => elabTerm t
#eval test_elabTerm let x:=1 in for i : 1⋯2 in x[1]
elab "(lang|" t:_term ")" : term => elabTerm t

#eval (lang| let x:=1 in for i : 1⋯2 in x)
#eval (lang|
  if x ≤ 0 then 1.1 else 0.0
)
#eval true && true
#eval (lang|
  for x : 0⋯2 in 1.2
)
#eval (lang|
  for i : 0⋯2 in
    for j : 0⋯2 in
      if i ≤  0 then
        if j ≤ 0 then
          1.0
        else
          0.0
      else if i ≤  1 then
        if j ≤  1 then
          1.0
        else
          0.0
      else if i ≤  2 then
        if j ≤  0 then
          1.0
        else
          0.0
      else 0.0)
#eval term [] (lang|
  for i : 0⋯2 in
    for j : 0⋯2 in
      if i ≤  0 then
        if j ≤ 0 then
          1.0
        else
          0.0
      else if i ≤  1 then
        if j ≤  1 then
          1.0
        else
          0.0
      else if i ≤  2 then
        if j ≤  0 then
          1.0
        else
          0.0
      else 0.0
)

#eval term [] (lang|
  let arr := for i : 0⋯4 in
    for j : 0⋯4 in
      3.14159
  in for i : 0⋯2 in
    for j : 0⋯1 in
      (arr[i][j], arr[i][j])
)

#eval term [] (lang|
  let arr := for i : 0⋯4 in
    for j : 0⋯4 in
      3.14159
  in for i : 0⋯2 in
    for j : 0⋯1 in
      (arr[i][j] + arr[i][j], arr[i][j] + arr[i][j])
)

#eval term [] (lang|
  let arr := for i : 0⋯4 in
    for j : 0⋯4 in
      3.14159
  in for i : 0⋯2 in
    for j : 0⋯1 in
      (arr, arr[i][j] + arr[i][j])
)

def ex := run [] (lang|
  let arr := for i : 0⋯4 in
    for j : 2⋯4 in
      3.14159
  in for i : 0⋯2 in
    for j : 0⋯1 in
      (arr, arr[i][j] + arr[i][j])
)

#eval ex
