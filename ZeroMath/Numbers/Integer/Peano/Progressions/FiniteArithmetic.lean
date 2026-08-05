import ZeroMath.Numbers.Integer.Peano
import ZeroMath.Sequences.Progression

namespace ZeroMath.Numbers.Integer.Peano.Progressions

/-- A finite arithmetic progression of integer Peano numbers with nonzero common
difference, defined by an optional first element (`none` for the empty
progression), the common difference, and a limit such that no element lies past
the limit in the direction of travel. When the common difference is positive the
progression is strictly increasing and no element exceeds the limit; when it is
negative the progression is strictly decreasing and no element is less than the
limit. The progression is also empty when the first element already lies past
the limit. -/
structure FiniteArithmetic where
  first : Option Peano
  commonDifference : Peano
  limit : Peano
  commonDifference_ne_zero : commonDifference ≠ zero

namespace FiniteArithmetic

/-- Include `x` when it does not lie past `limit` for the given common
difference: at most the limit when the difference is positive, at least the
limit when it is negative. Returns `none` for a zero difference. -/
def tryInclude (commonDifference limit x : Peano) : Option Peano :=
  match commonDifference with
  | positive _ => if x ≤ limit then some x else none
  | negative _ => if limit ≤ x then some x else none
  | zero => none

/-- Convert a finite arithmetic progression to a general progression by taking
the same optional first element when it does not lie past the limit (otherwise
the empty progression) and advancing by the common difference while the next
element does not lie past the limit. -/
def toProgression (p : FiniteArithmetic) : Sequences.Progression Peano where
  first :=
    match p.first with
    | none => none
    | some x => tryInclude p.commonDifference p.limit x
  next := fun x =>
    tryInclude p.commonDifference p.limit (x + p.commonDifference)

end FiniteArithmetic

end ZeroMath.Numbers.Integer.Peano.Progressions
