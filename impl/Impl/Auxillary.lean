import Impl.Syntax
def length: Syntax.Range -> Nat
| .range l r => r - l + 1
| .empty => 0
