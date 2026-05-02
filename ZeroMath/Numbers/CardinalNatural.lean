namespace ZeroMath.Numbers.CardinalNatural

def Peano := Nat

inductive Peano.LessThan (a : Peano) : Peano → Prop where
  | base : Peano.LessThan a (a.succ)
  | step {b : Peano} : Peano.LessThan a b → Peano.LessThan a (b.succ)

instance : LT Peano where
  lt := Peano.LessThan

end ZeroMath.Numbers.CardinalNatural
