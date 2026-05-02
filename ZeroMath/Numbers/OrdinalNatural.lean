namespace ZeroMath.Numbers.OrdinalNatural

inductive Peano where
  | one : Peano
  | succ : Peano → Peano

def Peano.toNat : Peano → Nat
  | one => 1
  | succ n => n.toNat + 1

end ZeroMath.Numbers.OrdinalNatural
