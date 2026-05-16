import ZeroMath.Numbers.CardinalNatural
import ZeroMath.Sequences.List

namespace ZeroMath.Numbers.CardinalNatural.Peano

def HasAtLeastOne : ZeroMath.Sequences.List Peano → Prop
  | _root_.List.nil => False
  | _root_.List.cons _ _ => True

end ZeroMath.Numbers.CardinalNatural.Peano

namespace ZeroMath.Numbers.CardinalNatural

def Decimal := { l : ZeroMath.Sequences.List Peano // Peano.AllLessThanTen l ∧ Peano.HasAtLeastOne l }

end ZeroMath.Numbers.CardinalNatural
