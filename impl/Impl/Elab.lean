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
syntax:65 _term "+" _term : _term
syntax:65 _term "-" _term : _term
syntax:70 _term "*" _term : _term
syntax:70 _term "/" _term : _term
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
  | `(_term| $f:scientific) => mkAppM ``Syntax.Term.floatLit #[mkFloatLit f.getScientific]
  | `(_term| $a:_term + $b:_term) => do
    let aa <- elabTerm a
    let bb <- elabTerm b
    return (mkApp3
    (mkConst ``Term.binary [])
    aa
    (mkConst ``Arith.plus [])
    bb)
  | `(_term| $a:_term - $b:_term) => do
    let aa <- elabTerm a
    let bb <- elabTerm b
    return (mkApp3
    (mkConst ``Term.binary [])
    aa
    (mkConst ``Arith.minus [])
    bb)
  | `(_term| $a:_term * $b:_term) => do
    let aa <- elabTerm a
    let bb <- elabTerm b
    return (mkApp3
    (mkConst ``Term.binary [])
    aa
    (mkConst ``Arith.times [])
    bb)
  | `(_term| $a:_term / $b:_term) => do
    let aa <- elabTerm a
    let bb <- elabTerm b
    return (mkApp3
    (mkConst ``Term.binary [])
    aa
    (mkConst ``Arith.divide [])
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
elab "(lang|" t:_term ")" : term => elabTerm t

def typecheck t := Typecheck.term [] t
def run t := Interpreter.run [] t
