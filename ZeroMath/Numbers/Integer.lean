import ZeroMath.Numbers.OrdinalNatural

namespace ZeroMath.Numbers.Integer

inductive Peano where
  | pos : OrdinalNatural.Peano → Peano
  | zero : Peano
  | neg : OrdinalNatural.Peano → Peano

def Peano.toNat : Peano → Nat
  | pos n => n.toNat
  | zero => 0
  | neg _ => 0

end ZeroMath.Numbers.Integer
