import Lean

namespace Syntax
mutual
-- Base Type
inductive Ty: Type
| range: Range -> Ty
| data: DataTy -> Ty
deriving BEq, Repr

-- σ
inductive DataTy: Type
| float
| tuple: DataTy -> DataTy -> DataTy
| array: Nat -> DataTy -> DataTy
deriving Repr

-- Range
inductive Range: Type
| range(l:Nat)(r:Nat)
| empty
deriving Repr


inductive Ident: Type
| ident: String -> Ident
deriving BEq, Repr

inductive Leq: Type
| leq(lhs:Ident)(rhs:Term)
deriving Repr

inductive Arith: Type
| plus
| minus
| times
| divide

inductive Term: Type
| floatLit: Float -> Term
| natLit: Nat -> Term
| place: PlaceExpr -> Term
| for_(i:Ident)(r: Range)(body: Term)
| let_(x:Ident)(t:Term)(in_t: Term)
| tuple(fst: Term)(snd: Term)
| ternary(cond: Leq)(if_body: Term)(else_body: Term)
| binary(lhs : Term)(op: Arith)(rhs: Term)
deriving Repr

inductive PlaceExpr: Type
| ident: Ident -> PlaceExpr
| index: IndexExpr -> PlaceExpr
| fst: PlaceExpr -> PlaceExpr
| snd: PlaceExpr -> PlaceExpr
deriving Repr

structure IndexExpr where
    place: PlaceExpr
    index: Term
deriving Repr

end

def TyEnv := List (Ident × Ty)
end Syntax
