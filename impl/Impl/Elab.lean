import Impl.Syntax
open Lean Elab Meta Term Syntax

declare_syntax_cat _term
declare_syntax_cat arith
declare_syntax_cat place
declare_syntax_cat range

-- entry
syntax "(lang|" _term ")" : term

syntax  arith : _term
syntax  num: _term
syntax  place: _term
syntax "for " ident " : " range " in " _term: _term
syntax "let " ident " := " _term " in " _term: _term
syntax "(" _term ", " _term ")" : _term
syntax "if " _term " ⊆ " _term " then " _term " else " _term: _term

syntax num"⋯"num: range
syntax "empty" : range
syntax scientific : arith
declare_syntax_cat bin_op
syntax " + ": bin_op
syntax " * ": bin_op
syntax " - ": bin_op
syntax " / ": bin_op
syntax arith bin_op arith : arith
syntax "(" arith ")" : arith

syntax  ident : place
syntax  place "["_term"]" : place
syntax  place:50 ".fst" : place
syntax  place:50 ".snd" : place


def mkFloatLit (x : Nat × Bool × Nat)  : Expr :=
  let (n, b, m) := x
  let n := Lean.mkNatLit n
  let m := Lean.mkNatLit m
  if b then
    mkApp3 (mkConst ``Float.ofScientific []) n (.const ``Bool.true []) m
  else
    mkApp3 (mkConst ``Float.ofScientific []) n (.const ``Bool.false []) m

partial def elabArith : Syntax -> MetaM Expr
  | `(arith| $f:scientific) => mkAppM ``floatLit #[mkFloatLit f.getScientific]
  | `(arith| $a:arith $op:bin_op $b:arith) => do
    let aa <- elabArith a
    let bb <- elabArith b
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
  | `(arith| ($a:arith)) => do
    elabArith a
  | _ => throwUnsupportedSyntax

elab "test_elabArith" t:arith : term => elabArith t

#reduce test_elabArith (5.2 + 2.1)
#eval test_elabArith (5.2 + 2.1)
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
  | `(_term| $a:arith) => elabArith a
  | `(_term| $n:num) => pure $ Lean.mkApp (mkConst ``Term.natLit []) (mkNatLit n.getNat)
  | `(_term| $p:place) => do
    let p <- elabPlace p
    mkAppM ``Term.place #[p]
  | `(_term| ( $l, $r) ) => do
    let l <- elabTerm l
    let r <- elabTerm r
    pure $ mkApp2 (mkConst ``Term.tuple []) l r
  | `(_term| let $x := $t in $t_in) => do
    let x :=  Lean.mkApp (mkConst ``Ident.ident []) (x.getId.toString |> mkStrLit)
    let t <- elabTerm t
    let t_in <- elabTerm t_in
    pure $ mkApp3 (mkConst ``Term.let_ []) x t t_in
  | `(_term| if $l ⊆ $r then $t_if else $t_else) => do
    let l <- elabTerm l
    let r <- elabTerm r
    let t_if <- elabTerm t_if
    let t_else <- elabTerm t_else
    let cond := mkApp2 (mkConst ``Contains.comp []) l r
    mkAppM ``Term.ternary #[cond, t_if, t_else]
  | `(_term| for $i : $r in $t) => do
    let i := Lean.mkApp (mkConst ``Ident.ident []) (i.getId.toString |> Lean.mkStrLit)
    let r <- elabRange r
    let t <- elabTerm t
    mkAppM ``Term.for_ #[i, r, t]
  | _ => throwUnsupportedSyntax
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
    pure $ mkApp (mkConst ``PlaceExpr.fst []) inner
  | _ => throwUnsupportedSyntax
end
elab "test_elabRange" t:range : term => elabRange t
#eval test_elabRange 1⋯2
elab "test_elabTerm" t:_term : term => elabTerm t
#eval test_elabTerm let x:=1 in for i : 1⋯2 in x[1]
