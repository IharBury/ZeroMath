import ZeroMath.Numbers.OrdinalNatural.Peano

namespace ZeroMath.Numbers.OrdinalNatural.Peano

namespace Progressions

/-- An infinite arithmetic progression of Peano numbers with positive common
difference, defined by the first element and the common difference. Because
every Peano number is at least one, the common difference is always positive. -/
structure InfiniteArithmetic where
  first : Peano
  commonDifference : Peano

namespace InfiniteArithmetic

end InfiniteArithmetic

end Progressions

end ZeroMath.Numbers.OrdinalNatural.Peano
