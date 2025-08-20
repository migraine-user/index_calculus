import Impl.Syntax
def mkRng(r:Range): Range :=
  match r with
  | .empty => .empty
  | .range a b => if a <= b then r else .empty


def length(r:Range): Nat :=
  match r with
  | .empty => 0
  | .range l r => r - l + 1

-- Lean needs Range. to be there.
-- Inference is worse for lambdas more than defs.
-- private def inter (r_l r_r: Range) : Range :=
--   match (r_l, r_r) with
--   | (.empty, _) => Range.empty
--   | (_, .empty) => Range.empty
--   | (.range a b, .range l r) => Range.range (max a l) (min b r)
-- infixl:65 " ∩ " => inter
-- private def minus (l r : Range) : Range × Range :=
--   match l with
--   | .empty =>
--       (.empty, .empty)
--   | .range l₀ r₀ =>
--     match l ∩ r with
--     | .empty =>
--         (mkRng (.range l₀ r₀), .empty)
--     | .range li ri =>
--         ( mkRng (.range l₀ (max 0 (li - 1)))
--         , mkRng (.range (ri + 1) r₀) )
-- infixl:65 " \\ " => minus
-- def splitSubseteq(l: Range) (r: Range) : Range × Range × Range :=
--   let (r0, r1) := l \ r
--   let lr := l ∩ r
--   (lr, r0, r1)
