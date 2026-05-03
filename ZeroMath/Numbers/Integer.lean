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
  | neg_lt_zero {n : OrdinalNatural.Peano} : Peano.LessThan (negative n) zero
  | zero_lt_pos {n : OrdinalNatural.Peano} : Peano.LessThan zero (positive n)
  | neg_lt_pos {n m : OrdinalNatural.Peano} : Peano.LessThan (negative n) (positive m)
  | pos_lt_pos {n m : OrdinalNatural.Peano} : n < m → Peano.LessThan (positive n) (positive m)
  | neg_lt_neg {n m : OrdinalNatural.Peano} : m < n → Peano.LessThan (negative n) (negative m)

instance : LT Peano where
  lt := Peano.LessThan

end ZeroMath.Numbers.Integer
