import Impl.Syntax
import Impl.Auxillary

namespace Typecheck
abbrev TyResult := Except String Syntax.Ty

mutual
def join : Syntax.DataTy → Syntax.DataTy → Option Syntax.DataTy
  | .float, .float => .some .float
  | .array n1 t1, .array n2 t2 => do
    let .some t := join t1 t2 | .none
    .some $ .array (min n1 n2) t
  | .tuple a b, .tuple a' b' => do
    let .some a'' := join a a' | .none
    let .some b'' := join b b' | .none
    .some $ .tuple a'' b''
  | .func a b, .func a' b' => do
    let .some a'' := meet a a' | .none
    let .some b'' := join b b' | .none
    .some $ .func a'' b''
  | t1, t2 => if t1 == t2 then .some t1 else .none
def meet: Syntax.DataTy -> Syntax.DataTy -> Option Syntax.DataTy
  | .float, .float => .some .float
  | .array n1 t1, .array n2 t2 => do
    let .some t := meet t1 t2 | .none
    .some $ .array (max n1 n2) t
  | .tuple a b, .tuple a' b' => do
    let .some a'' := meet a a' | .none
    let .some b'' := meet b b' | .none
    .some $ .tuple a'' b''
  | t1, t2 => if t1 == t2 then .some t1 else .none
end

mutual
def term (tyEnv: Syntax.TyEnv) (t:Syntax.Term) : TyResult :=
match t with
    | .var id => ident tyEnv id
    | .index arr i => do
      let arr <- term tyEnv arr
      let i <- term tyEnv i
      let .data dty := arr | .error "LHS must be a data type"
      let .array n dty := dty | .error "LHS must be an array"
      let .range rnge := i | .error "Index must be a range type"
      match rnge with
      | .empty => pure $ .data dty
      | .range _ r => if r < n then pure $ .data dty else .error "Index out of bounds"
    | .fst t => do
      let ty <- term tyEnv t
      let .data dty := ty | .error "must be data type"
      let .tuple l _ := dty | .error "trying to access fst of non-tuple"
      pure $ .data l
    | .snd t => do
      let ty <- term tyEnv t
      let .data dty := ty | .error "must be data type"
      let .tuple _ r := dty | .error "trying to access fst of non-tuple"
      pure $ .data r
    | .floatLit _ => .ok $ .data $ .float
    | .natLit n => .ok $ .range $ .range n n
    | .for_ i r body => do
      let tyEnv' :=  (i,.range r)::tyEnv
      let .ok (.data dtBody) := term tyEnv' body | .error "for body must be of data type"
      pure $ .data $ .array (length r) dtBody
    | .let_ x t in_t => do
      let tType <- term tyEnv t
      let tyEnv' := (x,tType)::tyEnv
      let .ok (.data dty) := term tyEnv' in_t | .error "must return data from let"
      pure $ .data dty
    | .tuple l r => do
      let lTy <- term tyEnv l
      let rTy <- term tyEnv r
      let .data lDty := lTy | .error "must be data"
      let .data rDty := rTy | .error "must be data"
      pure $ .data $ .tuple lDty rDty
    | .ternary (.leq t_ident t) if_body else_body => do
      let .var i := t_ident | .error "lhs must be an identifier"
      let iTy <- ident tyEnv i
      let .range iR := iTy | .error "lhs must be a range"
      let .natLit n := t | .error "rhs must be a natural literal"
      let (rIf, rElse)  <- match iR with
      | Syntax.Range.range a b =>
        let l := if a <= n then Syntax.Range.range a n else .empty
        let r := if n + 1 <= b then Syntax.Range.range (n+1) b else .empty
        pure (l, r)
      | .empty => pure (.empty, .empty)
      let (rIf, rElse) := (.range rIf, .range rElse)
      let .ok (.data t1) := term ((i,rIf)::tyEnv) if_body | .error "must be data type"
      let .ok (.data t2) := term ((i,rElse)::tyEnv) else_body | .error "must be data type"
      let .some t := meet t1 t2 | .error "cannot unify both branches"
      pure $ .data t
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
      let .data (.func iTy oTy) := tt1 | .error "expected function type"
      let tt2 <- term tyEnv t2
      let (.data xTy) := tt2 | .error "should be a data type"
      let .some _ := meet xTy iTy | .error "supplied argument doesn't unify"
      pure $ .data oTy

def ident (tyEnv: Syntax.TyEnv) (i:Syntax.Ident) : TyResult :=
  match tyEnv with
  | (i', ty)::rest => if i == i'
    then .ok ty
    else ident rest i
  | [] => match i with
    | .ident s => .error $ s!"Identifier {s} not found"
end

end Typecheck
