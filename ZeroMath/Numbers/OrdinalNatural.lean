namespace ZeroMath.Numbers.OrdinalNatural

inductive Peano where
  | one : Peano
  | successor : Peano → Peano

def Peano.toNat : Peano → Nat
  | one => 1
  | successor n => n.toNat + 1

end ZeroMath.Numbers.OrdinalNatural
