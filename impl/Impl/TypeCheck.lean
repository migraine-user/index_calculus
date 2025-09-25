import Impl.Syntax
import Impl.Auxillary

namespace Typecheck
abbrev TyResult := Except String Syntax.Ty

mutual
partial def term (tyEnv: Syntax.TyEnv) (t:Syntax.Term) : TyResult :=
  match t with
    | .var id => ident tyEnv id
    | .index arr i => do
      let arr <- term tyEnv arr
      let i <- term tyEnv i
      let .data dty := arr | .error "LHS must be a data type"
      let .array n dty := dty | .error "LHS must be an array"
      let .range rnge := i | .error "Index must be a range type"
      let .range l r := rnge | .error "Cannot index with empty array"
      if r < n then pure $ .data dty else .error "Index out of bounds"
    | .fst t => do
      let ty <- term tyEnv t
      let .data dty := ty | .error "must be data type"
      let .tuple l r := dty | .error "trying to access fst of non-tuple"
      pure $ .data l
    | .snd t => do
      let ty <- term tyEnv t
      let .data dty := ty | .error "must be data type"
      let .tuple l r := dty | .error "trying to access fst of non-tuple"
      pure $ .data r
    | .floatLit _ => .ok $ .data $ .float
    | .natLit n => .ok $ .range $ .range n n
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
      let (rIf, rElse) : Syntax.Range × Syntax.Range := match iR with
      | Syntax.Range.range a b => (mkRng $ .range a n, mkRng $ .range (n+1) b)
      | Syntax.Range.empty => (.empty, .empty)
      let (rIf, rElse) := (.range rIf, .range rElse)
      let t1 <- term ((i,rIf)::tyEnv) if_body
      let t2 <- term ((i,rElse)::tyEnv) else_body
      if t1 == t2
        then .ok t1
        else .error "the branches must have the same type"
    | .binary l _op r => do
      let l <- term tyEnv l
      let r <- term tyEnv r
      if l == r && r == .data .float
        then pure $ .data .float
        else .error "arithmetic only supports floats"
    | .abs x dty body => do
      let inTy := Syntax.Ty.data dty
      let tyEnv' := (x, inTy)::tyEnv
      let outputTy <- term tyEnv' body
      match outputTy with
      | .data odty => pure $ .data $ .func dty odty
      | _ => .error "a function must return a value of data type."
    | .app t1 t2 => do
      let tt1 <- term tyEnv t1
      let (iTy,oTy) <- match tt1 with
                  | .data (.func a b) => Except.ok $ (a,b)
                  | _ => .error "expected function type"
      let tt2 <- term tyEnv t2
      let xTy <- checkData "should be a data type" tt2
      if subtype xTy iTy then pure $ .data oTy else .error "input is not subtype"

partial def subtype (ty1: Syntax.DataTy) (ty2: Syntax.DataTy) : Bool :=
  match (ty1, ty2) with
  | (.float, .float) => true
  | (.tuple a b, .tuple a' b') => subtype a a' && subtype b b'
  | (.func a b, .func a' b') => subtype a' a && subtype b b'
  | _ => false
partial def checkData (msg: String)(ty: Syntax.Ty) : Except String Syntax.DataTy :=
  match ty with
  | .data dty => pure $ dty
  | .range _ => .error msg
partial def checkRange (msg: String)(ty: Syntax.Ty) : Except String Syntax.Range :=
  match ty with
  | .data _ => .error msg
  | .range r => .ok r

partial def ident (tyEnv: Syntax.TyEnv) (i:Syntax.Ident) : TyResult :=
  match tyEnv with
  | (i', ty)::rest => if i == i'
    then .ok ty
    else ident rest i
  | [] => match i with
    | .ident s => .error $ s!"Identifier {s} not found"
end

end Typecheck
