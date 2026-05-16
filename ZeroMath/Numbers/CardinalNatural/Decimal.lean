import ZeroMath.Numbers.CardinalNatural
import ZeroMath.Sequences.List

namespace ZeroMath.Numbers.CardinalNatural

def Decimal := { l : ZeroMath.Sequences.List Peano // Peano.AllLessThanTen l ∧ ZeroMath.Sequences.List.HasAtLeastOne l }

def Decimal.toPeanoHelper : ZeroMath.Sequences.List Peano → Peano → Peano
  | _root_.List.nil, acc => acc
  | _root_.List.cons d ds, acc => Decimal.toPeanoHelper ds (acc * Peano.ten + d)

def Decimal.toPeano (d : Decimal) : Peano :=
  Decimal.toPeanoHelper d.val Peano.zero

end ZeroMath.Numbers.CardinalNatural
