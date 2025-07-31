import Impl.Syntax
mutual
def term (tyEnv:TyEnv)(t:Term) : Option Ty :=
  match t with
  | Term.NatLit n => some (Ty.Nat n)
  | Term.FloatLit _ => Ty.Data DataTy.Float |> some
  | Term.Place _placeExpr => Option.map Ty.Data (placeExpr tyEnv _placeExpr)
  | Term.For id rnge body => do
    let ⟨l,r,_⟩ := rnge
    let elemTy <- term ((id, Ty.Range rnge)::tyEnv) body
    match elemTy with
    | Ty.Data elemTy => pure (Ty.Data (DataTy.Array (r-l) elemTy))
    | _ => none
  | Term.Let id tDef tBody => do
    match term tyEnv tDef with
    | Ty.Data dty => term ((id, Ty.Data dty)::tyEnv) tBody
    | _ => none
  | Term.Tuple t1 t2 =>
    do
      let ty1 <- term tyEnv t1
      let ty2 <- term tyEnv t2
      match (ty1, ty2) with
      | (Ty.Data dty1, Ty.Data dty2) => (DataTy.Tuple dty1 dty2) |> Ty.Data |> pure
      | _ => none

def findDef (tyEnv:TyEnv)(x:Ident) : Option Ty :=
  match tyEnv with
  | (id,ty)::rest => if id == x then some ty else findDef rest x
  | [] => none


def indexTerm (tyEnv: TyEnv) (t:Term) : Option Indexable :=
  match t with
  | Term.NatLit n => Indexable.Index n
  | t => do
    let ty <- term tyEnv t
    match ty with
    | Ty.Range r => Indexable.Range r
    | _ => none


def indexExpr (tyEnv: TyEnv)(t:IndexExpr) : Option DataTy := do
  let ⟨_placeExpr, _indexTerm⟩ := t
  let placeTy <- placeExpr tyEnv _placeExpr
  let tyIndex <- indexTerm tyEnv _indexTerm
  match placeTy with
  | DataTy.Array n dty =>
    match tyIndex with
    | Indexable.Index i => if i <= n then some dty else none
    | Indexable.Range rnge =>
      let ⟨_,r,_⟩ := rnge
      if r <= n then some dty else none
  | _ => none

def placeExpr (tyEnv:TyEnv)(t:PlaceExpr) : Option DataTy :=
  match t with
  | PlaceExpr.Ident id => do
    let ty <- findDef tyEnv id
    match ty with
    | Ty.Data dty => some dty
    | _ => none
  | PlaceExpr.Index _indexExpr => indexExpr tyEnv _indexExpr
  | PlaceExpr.Fst _placeExpr => do
    let ty <- placeExpr tyEnv _placeExpr
    match ty with
    | DataTy.Tuple a _ => some a
    | _ => none
  | PlaceExpr.Snd _placeExpr => do
    let ty <- placeExpr tyEnv _placeExpr
    match ty with
    | DataTy.Tuple _ b => some b
    | _ => none
end

def ex1 :=
  (Term.For (Ident.Ident "i") (Range.Range 0 5 (by decide))
    (Term.For (Ident.Ident "j") (Range.Range 0 6 (by decide))
      (Term.For (Ident.Ident "k") (Range.Range 0 7 (by decide))
        (Term.FloatLit 4.2))))
#eval ex1
#eval term [] ex1

def exLast :=
  let tupDef:= (Term.Tuple (Term.FloatLit 3.14159) (Term.For (Ident.Ident "i") (Range.Range 0 5 (by decide))
    (Term.FloatLit 6.25)))
  (Term.Let (Ident.Ident "tup") tupDef (Term.For (Ident.Ident "i") (Range.Range 0 10 (by decide)) (Term.Place (PlaceExpr.Ident (Ident.Ident "tup")))))
#eval exLast
#eval term [] exLast
