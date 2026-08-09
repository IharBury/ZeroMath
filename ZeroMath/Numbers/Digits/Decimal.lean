import ZeroMath.Numbers.CardinalNatural.Peano

namespace ZeroMath.Numbers.Digits

/-- A base-10 digit: a cardinal Peano natural strictly less than ten. -/
def Decimal := { d : CardinalNatural.Peano // d < CardinalNatural.Peano.ten }

deriving instance DecidableEq for Decimal

end ZeroMath.Numbers.Digits
