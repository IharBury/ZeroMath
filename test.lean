import ZeroMath.Numbers.OrdinalNatural.Decimal

open ZeroMath.Numbers.OrdinalNatural
open ZeroMath.Numbers

theorem Decimal.toPeano_successor (d : Decimal) : Decimal.toPeano (Decimal.successor d) = Peano.successor (Decimal.toPeano d) := by
  sorry

theorem Decimal.toPeano_fromPeano (x : Peano) : Decimal.toPeano (Decimal.fromPeano x) = x := by
  induction x with
  | one => exact Decimal.toPeano_fromPeano_one
  | successor p ih =>
    have h1 : Decimal.fromPeano (Peano.successor p) = Decimal.successor (Decimal.fromPeano p) := rfl
    rw [h1, Decimal.toPeano_successor, ih]
