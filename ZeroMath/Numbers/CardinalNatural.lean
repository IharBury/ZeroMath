namespace ZeroMath.Numbers.CardinalNatural

def Peano := Nat

namespace Peano

def zero : Peano := Nat.zero

def predecessor (n : Peano) (h : n ≠ zero) : Peano :=
  match n with
  | Nat.zero => by contradiction
  | Nat.succ n' => n'

end Peano

inductive Peano.LessThan (a : Peano) : Peano → Prop where
  | base : Peano.LessThan a (a.succ)
  | step {b : Peano} : Peano.LessThan a b → Peano.LessThan a (b.succ)

instance : LT Peano where
  lt := Peano.LessThan

def Peano.LessThanOrEqual (a b : Peano) : Prop :=
  a < b ∨ a = b

instance : LE Peano where
  le := Peano.LessThanOrEqual

end ZeroMath.Numbers.CardinalNatural
