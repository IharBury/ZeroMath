import ZeroMath.Numbers.OrdinalNatural

namespace ZeroMath.Numbers.Integer

inductive Peano where
  | positive : OrdinalNatural.Peano → Peano
  | zero : Peano
  | negative : OrdinalNatural.Peano → Peano

def Peano.toInt : Peano → Int
  | positive n => n.toNat
  | zero => 0
  | negative n => - (n.toNat : Int)

inductive Peano.LessThan : Peano → Peano → Prop where
  | negative_less_than_zero {n : OrdinalNatural.Peano} : Peano.LessThan (negative n) zero
  | zero_less_than_positive {n : OrdinalNatural.Peano} : Peano.LessThan zero (positive n)
  | negative_less_than_positive {n m : OrdinalNatural.Peano} : Peano.LessThan (negative n) (positive m)
  | positive_less_than_positive {n m : OrdinalNatural.Peano} : n < m → Peano.LessThan (positive n) (positive m)
  | negative_less_than_negative {n m : OrdinalNatural.Peano} : m < n → Peano.LessThan (negative n) (negative m)

instance : LT Peano where
  lt := Peano.LessThan

def Peano.LessThanOrEqual (a b : Peano) : Prop :=
  Peano.LessThan a b ∨ a = b

instance : LE Peano where
  le := Peano.LessThanOrEqual

end ZeroMath.Numbers.Integer
