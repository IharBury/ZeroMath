import ZeroMath.Numbers.OrdinalNatural.Decimal

open ZeroMath
open ZeroMath.Numbers.OrdinalNatural
open ZeroMath.Numbers.CardinalNatural

namespace ZeroMath.Numbers.OrdinalNatural.Decimal

theorem equivalent_add_commutative (a b : Decimal) : a + b ≈ b + a := by
  rw [add_commutative]
  rfl

end ZeroMath.Numbers.OrdinalNatural.Decimal
