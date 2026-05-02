namespace ZeroMath.Numbers.OrdinalNatural

inductive Peano where
  | one : Peano
  | successor : Peano → Peano

def Peano.toNat : Peano → Nat
  | one => 1
  | successor n => n.toNat + 1

def Peano.fromNat : (n : Nat) → n ≠ 0 → Peano
  | 0, h => by contradiction
  | 1, _ => Peano.one
  | n + 2, _ => Peano.successor (fromNat (n + 1) Nat.noConfusion)

inductive Peano.LessThan (a : Peano) : Peano → Prop where
  | base : Peano.LessThan a (Peano.successor a)
  | step {b : Peano} : Peano.LessThan a b → Peano.LessThan a (Peano.successor b)

instance : LT Peano where
  lt := Peano.LessThan

def Peano.LessThanOrEqual (a b : Peano) : Prop :=
  a = b ∨ Peano.LessThan a b

instance : LE Peano where
  le := Peano.LessThanOrEqual

end ZeroMath.Numbers.OrdinalNatural
