import Impl.Syntax
import Impl.Auxillary
abbrev TyResult := Except String Ty

mutual
partial def term (tyEnv: TyEnv) (t:Term) : TyResult :=
  match t with
    | .floatLit _ => .ok $ .data $ .float
    | .natLit n => .ok $ .range $ .range n n
    | .place p => do
      let pType <- place tyEnv p
      pure pType
    | .for_ i r body => do
      let r' := mkRng r
      let tyEnv' :=  (i,.range r')::tyEnv
      let tBody <- term tyEnv' body
      match tBody with
        | .range _ => .error "for body must be of data type"
        | .data dtBody => pure $ .data $ .array (length r') dtBody
    | .let_ x t in_t => do
      let tType <- term tyEnv t
      let tyEnv' := (x,tType)::tyEnv
      let in_tType <- term tyEnv' in_t
      match in_tType with
        | .range _ => .error "must return data from let"
        | .data dty => pure $ .data dty
    | .tuple l r => do
      let lTy <- term tyEnv l
      let rTy <- term tyEnv r
      let check := checkData "tuple content must be data"
      let lDty <- check lTy
      let rDty <- check rTy
      pure $ .data $ .tuple lDty rDty
    | .ternary (.leq i t) if_body else_body => do
      let iTy <- ident tyEnv i
      let iR <- checkRange "lhs must be a range" iTy
      let n <- match t with
      | .natLit m => pure m
      | _ => .error "rhs must be a natural literal"
      let (rIf, rElse) : Range × Range := match iR with
      | .range a b => (mkRng $ .range a n, mkRng $ .range (n+1) b)
      | .empty => (.empty, .empty)
      let (rIf, rElse) := (.range rIf, .range rElse)
      let t1 <- term ((i,rIf)::tyEnv) if_body
      let t2 <- term ((i,rElse)::tyEnv) else_body
      if t1 == t2
        then .ok t1
        else .error "the branches must have the same type"
    | .binary l op r => do
      let l <- term tyEnv l
      let r <- term tyEnv r
      if l == r && r == .data .float
        then pure $ .data .float
        else .error "arithmetic only supports floats"

partial def checkData (msg: String)(ty: Ty) : Except String DataTy :=
  match ty with
  | .data dty => pure $ dty
  | .range _ => .error msg
partial def checkRange (msg: String)(ty: Ty) : Except String Range :=
  match ty with
  | .data _ => .error msg
  | .range r => .ok r

partial def ident (tyEnv: TyEnv) (i:Ident) : TyResult :=
  match tyEnv with
  | (i', ty)::rest => if i == i'
    then .ok ty
    else ident rest i
  | [] => match i with
    | .ident s => .error $ s!"Identifier {s} not found"
partial def place (tyEnv: TyEnv) (p:PlaceExpr) : TyResult :=
  match p with
  | .ident i => ident tyEnv i
  | .index indexExpr => do
    let lhs <- place tyEnv indexExpr.place
    let rhs <- term tyEnv indexExpr.index
    match lhs with
      | .data (.array n elemTy) => match rhs with
        | .range .empty => .ok $ .data elemTy
        | .range (.range l r) => (if r < n
          then .ok $ .data elemTy
          else .error "out of bounds access")
        | _ => .error "you can only index with ranges"
      | _ => .error "you can only index access arrays"
  | .fst tup => do
    let tup <- place tyEnv tup
    match tup with
    | .data $ .tuple fst snd => .ok $ .data fst
    | _ => .error "not a tuple"
  | .snd tup => do
    let tup <- place tyEnv tup
    match tup with
    | .data $ .tuple fst snd => .ok $ .data snd
    | _ => .error "not a tuple"
end
