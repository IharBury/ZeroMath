import ZeroMath.Numbers.CardinalNatural
import ZeroMath.Sequences.List

namespace ZeroMath.Numbers.CardinalNatural

def Decimal := { l : ZeroMath.Sequences.List Peano // Peano.AllLessThanTen l ∧ ZeroMath.Sequences.List.HasAtLeastOne l }

end ZeroMath.Numbers.CardinalNatural
