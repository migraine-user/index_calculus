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
| func: DataTy -> DataTy -> DataTy
deriving BEq, Repr

-- Range
inductive Range: Type
| range(l:Nat)(r:Nat)
| empty
deriving Repr

inductive Ident: Type
| ident: String -> Ident
deriving BEq, Repr

inductive Leq: Type
| leq(lhs:Term)(rhs:Term)
deriving Repr

inductive Arith: Type
| plus
| minus
| times
| divide
deriving Repr

inductive Term: Type
| floatLit: Float -> Term
| natLit: Nat -> Term
| for_(i:Ident)(r: Range)(body: Term)
| let_(x:Ident)(t:Term)(in_t: Term)
| tuple(fst: Term)(snd: Term)
| ternary(cond: Leq)(if_body: Term)(else_body: Term)
| binary(lhs : Term)(op: Arith)(rhs: Term)
| abs(x: Ident)(ty: DataTy)(body: Term)
| app (f: Term)(x: Term)
| var: Ident -> Term
| index(arr:Term)(i:Term)
| fst: Term -> Term
| snd: Term -> Term
deriving Repr

end

def TyEnv := List (Ident × Ty)

end Syntax
