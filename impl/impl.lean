inductive Range: Type
| One(a:Nat)(b:Nat)(p:a≤b)
| Cons(a:Nat)(b:Nat)(p:a≤b)(cdr: Range)

inductive DataTy: Type
| Float
| Tuple: DataTy -> DataTy -> DataTy
| Array: Nat -> DataTy -> DataTy

inductive Ty: Type
| Range: Range -> Ty
| Data: DataTy -> Ty

inductive Indexable: Type
| Index: Nat -> Indexable
| Range: Range -> Indexable

inductive Ident: Type
| Ident: String -> Ident

inductive PlaceExpr: Type
| Ident: Ident -> PlaceExpr
| Index: PlaceExpr -> Indexable -> PlaceExpr
| Slice: PlaceExpr -> Range -> PlaceExpr
| Fst: PlaceExpr -> PlaceExpr
| Snd: PlaceExpr -> PlaceExpr

inductive Term: Type
| FloatLit: Float -> Term
| Place: PlaceExpr -> Term
| For: Ident -> Range -> Term -> Term
| Let: Ident -> Term -> Term -> Term
| Tuple: Term -> Term -> Term

abbrev TyEnv := List Ident × Ty
