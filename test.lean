import ZeroMath.Numbers.CardinalNatural.Decimal
import ZeroMath.Numbers.CardinalNatural

namespace ZeroMath.Numbers.CardinalNatural

def fromPeano2 (x : Peano) : Decimal :=
  match x with
  | Nat.zero => Decimal.zero
  | Nat.succ p => Decimal.successor (fromPeano2 p)

end ZeroMath.Numbers.CardinalNatural
