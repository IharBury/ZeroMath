import ZeroMath.Numbers.CardinalNatural.Peano
import ZeroMath.Sequences.List

namespace ZeroMath.Numbers.CardinalNatural

namespace Decimal

def Digit := {d : CardinalNatural.Peano // d < CardinalNatural.Peano.ten}

end Decimal

def Decimal := { l : Sequences.List Decimal.Digit // l ≠ Sequences.List.empty }

namespace Decimal

def isNormalized (d : Decimal) : Bool :=
  match d with
  | ⟨.empty, _⟩ => by contradiction
  | ⟨.firstElement digit _, _⟩ => decide (digit.val ≠ CardinalNatural.Peano.zero)

end Decimal

end ZeroMath.Numbers.CardinalNatural
