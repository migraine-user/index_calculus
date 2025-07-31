inductive Range: Type
| Range(a:Nat)(b:Nat)(p:a≤b)
deriving Repr

inductive DataTy: Type
| Float
| Tuple: DataTy -> DataTy -> DataTy
| Array: Nat -> DataTy -> DataTy
deriving Repr

inductive Ty: Type
| Range: Range -> Ty
| Data: DataTy -> Ty
| Nat: Nat -> Ty
deriving Repr

inductive Indexable: Type
| Index: Nat -> Indexable
| Range: Range -> Indexable
deriving Repr

inductive Ident: Type
| Ident: String -> Ident
deriving BEq, Repr

mutual
inductive PlaceExpr: Type
| Ident: Ident -> PlaceExpr
| Index: IndexExpr -> PlaceExpr
| Fst: PlaceExpr -> PlaceExpr
| Snd: PlaceExpr -> PlaceExpr
deriving Repr

inductive IndexExpr : Type
| Index: PlaceExpr -> Term -> IndexExpr
deriving Repr

inductive Term: Type
| FloatLit: Float -> Term
| NatLit: Nat -> Term
| Place: PlaceExpr -> Term
| For: Ident -> Range -> Term -> Term
| Let: Ident -> Term -> Term -> Term
| Tuple: Term -> Term -> Term
deriving Repr
end

def TyEnv := List (Ident × Ty)
