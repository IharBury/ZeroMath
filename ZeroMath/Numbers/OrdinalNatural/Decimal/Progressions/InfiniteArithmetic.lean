import ZeroMath.Numbers.OrdinalNatural.Decimal
import ZeroMath.Sequences.Progression

namespace ZeroMath.Numbers.OrdinalNatural.Decimal.Progressions

/-- An infinite arithmetic progression of Decimal numbers with positive common
difference, defined by the first element and the common difference. Because
every Decimal number is at least one, the common difference is always positive. -/
structure InfiniteArithmetic where
  first : Decimal
  commonDifference : Decimal

namespace InfiniteArithmetic

/-- Convert an infinite arithmetic progression to a general progression by
taking the same first element and advancing by the common difference at each
step (never ending). -/
def toProgression (p : InfiniteArithmetic) : Sequences.Progression Decimal where
  first := some p.first
  next := fun x => some (x + p.commonDifference)

end InfiniteArithmetic

end ZeroMath.Numbers.OrdinalNatural.Decimal.Progressions
