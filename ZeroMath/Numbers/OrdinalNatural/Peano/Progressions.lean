import ZeroMath.Numbers.OrdinalNatural.Peano
import ZeroMath.Sequences.Progression

namespace ZeroMath.Numbers.OrdinalNatural.Peano

namespace Progressions

/-- An infinite arithmetic progression of Peano numbers with positive common
difference, defined by the first element and the common difference. Because
every Peano number is at least one, the common difference is always positive. -/
structure InfiniteArithmetic where
  first : Peano
  commonDifference : Peano

namespace InfiniteArithmetic

/-- Convert an infinite arithmetic progression to a general progression by
taking the same first element and advancing by the common difference at each
step (never ending). -/
def toProgression (p : InfiniteArithmetic) : Sequences.Progression Peano where
  first := p.first
  next := fun x => some (x + p.commonDifference)

end InfiniteArithmetic

end Progressions

end ZeroMath.Numbers.OrdinalNatural.Peano
