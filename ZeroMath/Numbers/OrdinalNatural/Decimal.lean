import ZeroMath.Numbers.CardinalNatural
import ZeroMath.Sequences.List

namespace ZeroMath.Numbers.OrdinalNatural

def AllLessThanTen : ZeroMath.Sequences.List ZeroMath.Numbers.CardinalNatural.Peano → Prop
  | _root_.List.nil => True
  | _root_.List.cons d ds => d < ZeroMath.Numbers.CardinalNatural.Peano.ten ∧ AllLessThanTen ds

def HasNonZero : ZeroMath.Sequences.List ZeroMath.Numbers.CardinalNatural.Peano → Prop
  | _root_.List.nil => False
  | _root_.List.cons d ds => d ≠ CardinalNatural.Peano.zero ∨ HasNonZero ds

def Decimal := { l : ZeroMath.Sequences.List ZeroMath.Numbers.CardinalNatural.Peano // AllLessThanTen l ∧ HasNonZero l }

end ZeroMath.Numbers.OrdinalNatural
