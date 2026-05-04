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

theorem add_zero (a : Peano) : add a zero = a := rfl

theorem zero_add (a : Peano) : add zero a = a := by
  induction a with
  | zero => rfl
  | succ a' ih =>
    show add zero a'.succ = a'.succ
    calc
      add zero a'.succ = (add zero a').succ := rfl
      _ = a'.succ := congrArg Nat.succ ih

theorem add_succ (a b : Peano) : add a b.succ = (add a b).succ := rfl

theorem succ_add (a b : Peano) : add a.succ b = (add a b).succ := by
  induction b with
  | zero => rfl
  | succ b' ih =>
    show add a.succ b'.succ = (add a b'.succ).succ
    calc
      add a.succ b'.succ = (add a.succ b').succ := rfl
      _ = (add a b').succ.succ := congrArg Nat.succ ih
      _ = (add a b'.succ).succ := rfl

theorem add_comm (a b : Peano) : add a b = add b a := by
  induction b with
  | zero =>
    show add a zero = add zero a
    rw [add_zero, zero_add]
  | succ b' ih =>
    show add a b'.succ = add b'.succ a
    rw [add_succ a b']
    rw [ih]
    rw [succ_add b' a]

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
