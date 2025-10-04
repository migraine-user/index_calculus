import Impl.TypeCheck
import Impl.Syntax

namespace Semantics
-- in term `t`, change `id` to `v`
def subst (t:Syntax.Term)(id:Syntax.Ident)(v:Syntax.Term) :=
match t with
| .floatLit _ | .natLit _ => t
| .for_ i r body => if i == id then t else .for_ i r (subst body id v)
| .let_ x tt in_t => if x == id then t else .let_ x tt (subst in_t id v)
| .tuple a b => .tuple (subst a id v) (subst b id v)
| .ternary (.leq lhs rhs) if_body else_body =>
  .ternary (.leq (subst lhs id v) (subst rhs id v)) (subst if_body id v) (subst else_body id v)
| .binary a op b => .binary (subst a id v) op (subst b id v)
| .abs x ty body => if x == id then t else .abs x ty (subst body id v)
| .app f x => .app (subst f id v) (subst x id v)
| .var x => if x == id then v else t
| .index arr i => .index (subst arr id v) (subst i id v)
| .fst t => .fst (subst t id v)
| .snd t => .snd (subst t id v)


partial def normalize (t:Syntax.Term): Option Syntax.Term :=
-- dbg_trace ("!!!!  " ++ repr t)
match t with
| .let_ id t body => do
  let v <- normalize t
  normalize $ subst body id v
| .tuple a b => do
  let a <- normalize a
  let b <- normalize b
  pure $ .tuple a b
| .ternary (.leq lhs rhs) if_body else_body => do
  let lhs <- normalize lhs
  let rhs <- normalize rhs
  let .natLit l := lhs | none
  let .natLit r := rhs | none
  let if_body <- normalize if_body
  let else_body <- normalize else_body
  if l <= r then if_body else else_body
| .binary lhs op rhs => do
  let lhs <- normalize lhs
  let rhs <- normalize rhs
  let .floatLit lhs := lhs | none
  let .floatLit rhs := rhs | none
  pure ∘ .floatLit $ match op with
  | .plus => lhs + rhs
  | .minus => lhs - rhs
  | .times => lhs * rhs
  | .divide => lhs / rhs
| .app f x => do
  let f <- normalize f
  let x <- normalize x
  let .abs x_id _ body := f | none
  normalize $ subst body x_id x
| .index arr n => do
  let arr <- normalize arr
  let n <- normalize n
  let .for_ i _ t := arr | .none
  let .natLit _ := n | .none
  normalize $ subst t i n
| .fst tup => do
  let tup <- normalize tup
  let .tuple a _ := tup | .none
  pure a
| .snd tup => do
  let tup <- normalize tup
  let .tuple _ b := tup | .none
  pure b
| t => t -- everything else is rejected by the type checker or is in normal form

end Semantics
