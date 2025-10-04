import Impl.Syntax
def length(r:Syntax.Range): Nat :=
  match r with
  | .range l r => r - l + 1
  | .empty => 0
