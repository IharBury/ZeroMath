namespace ZeroMath.Numbers.CardinalNatural

def Peano := Nat

namespace Peano

def zero : Peano := Nat.zero

def predecessor (n : Peano) (h : n ≠ zero) : Peano :=
  match n with
  | Nat.zero => by contradiction
  | Nat.succ n' => n'

def add (a : Peano) : Peano → Peano
  | Nat.zero => a
  | Nat.succ b' => Nat.succ (add a b')

instance : Add Peano where
  add := add

def succ (a : Peano) : Peano := Nat.succ a

theorem add_zero (a : Peano) : a + zero = a := rfl

theorem zero_add (a : Peano) : zero + a = a := by
  induction a with
  | zero => rfl
  | succ a' ih => exact congrArg Nat.succ ih

theorem add_succ (a b : Peano) : a + b.succ = (a + b).succ := rfl

theorem succ_add (a b : Peano) : a.succ + b = (a + b).succ := by
  induction b with
  | zero => rfl
  | succ b' ih => exact congrArg Nat.succ ih

theorem add_comm (a b : Peano) : a + b = b + a := by
  show a + b = b + a
  induction b with
  | zero =>
    show a + zero = zero + a
    rw [add_zero, zero_add]
  | succ b' ih =>
    show a + succ b' = succ b' + a
    rw [add_succ, ih, succ_add]

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
