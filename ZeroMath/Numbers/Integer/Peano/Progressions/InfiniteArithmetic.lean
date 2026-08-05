import ZeroMath.Numbers.Integer.Peano
import ZeroMath.Sequences.Progression

namespace ZeroMath.Numbers.Integer.Peano.Progressions

/-- An infinite arithmetic progression of integer Peano numbers, defined by the
first element and the common difference. When the common difference is positive
the progression is strictly increasing; when it is negative it is strictly
decreasing; when it is zero every element equals the first. -/
structure InfiniteArithmetic where
  first : Peano
  commonDifference : Peano

namespace InfiniteArithmetic

/-- Convert an infinite arithmetic progression to a general progression by
taking the same first element and advancing by the common difference at each
step (never ending). -/
def toProgression (p : InfiniteArithmetic) : Sequences.Progression Peano where
  first := some p.first
  next := fun x => some (x + p.commonDifference)

end InfiniteArithmetic

end ZeroMath.Numbers.Integer.Peano.Progressions
