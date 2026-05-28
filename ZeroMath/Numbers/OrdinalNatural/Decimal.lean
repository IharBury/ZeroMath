import ZeroMath.Numbers.CardinalNatural.Peano
import ZeroMath.Sequences.List

namespace ZeroMath.Numbers.OrdinalNatural

namespace Decimal

def AllLessThanTen : Sequences.List CardinalNatural.Peano → Prop
  | .empty => True
  | .firstElement d ds => d < CardinalNatural.Peano.ten ∧ AllLessThanTen ds

def HasNonZero : Sequences.List CardinalNatural.Peano → Prop
  | .empty => False
  | .firstElement d ds => d ≠ CardinalNatural.Peano.zero ∨ HasNonZero ds

end Decimal

def Decimal := { l : ZeroMath.Sequences.List CardinalNatural.Peano // Decimal.AllLessThanTen l ∧ Decimal.HasNonZero l }

namespace Decimal

def isNormalized (d : Decimal) : Bool :=
  match d.val with
  | .empty => false
  | .firstElement digit _ => decide (digit ≠ CardinalNatural.Peano.zero)

end Decimal

end ZeroMath.Numbers.OrdinalNatural
