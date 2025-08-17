import Impl.Syntax
def mkRng(r:Range): Range :=
  match r with
  | .empty => .empty
  | a..b => if a <= b then a..b else .empty


def length(r:Range): Nat :=
  match r with
  | .empty => 0
  | l..r => r - l + 1

-- Lean needs Range. to be there.
-- Inference is worse for lambdas more than defs.
infixl:65 " ∩ " => λ r_l r_r: Range =>
  match r_l, r_r with
  | (.empty, _) => Range.empty
  | (_, .empty) => Range.empty
  | (a..b, l..r) => Range.range (max a l) (min b r)

infixl:65 " \\ " => λ r_l r_r: Range =>
  match r_l ∩ r_r with
  | .empty => (r_l, Range.empty)
  | l_inter..r_inter => match r_l with
    | l_l..r_l => (mkRng l_l..l_inter-1, mkRng r_inter + 1, r_l)
    | .empty => panic! "Unreachable"
