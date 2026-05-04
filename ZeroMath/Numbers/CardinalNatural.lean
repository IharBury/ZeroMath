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

instance : HAdd Peano Nat Peano where hAdd a b := add a b
instance : HAdd Nat Peano Peano where hAdd a b := add a b
instance : HAdd Peano Peano Peano where hAdd a b := add a b

theorem add_zero (a : Peano) : a + zero = a := rfl

theorem zero_add (a : Peano) : zero + a = a := by
  show add zero a = a
  induction a with
  | zero => rfl
  | succ a' ih =>
    show add zero a'.succ = a'.succ
    calc
      add zero a'.succ = (add zero a').succ := rfl
      _ = a'.succ := congrArg Nat.succ ih

theorem add_succ (a b : Peano) : a + b.succ = (a + b).succ := rfl

theorem succ_add (a b : Peano) : a.succ + b = (a + b).succ := by
  show add a.succ b = (add a b).succ
  induction b with
  | zero => rfl
  | succ b' ih =>
    show add a.succ b'.succ = (add a b'.succ).succ
    calc
      add a.succ b'.succ = (add a.succ b').succ := rfl
      _ = (add a b').succ.succ := congrArg Nat.succ ih
      _ = (add a b'.succ).succ := rfl

theorem add_comm (a b : Peano) : a + b = b + a := by
  show add a b = add b a
  induction b with
  | zero =>
    show add a zero = add zero a
    have h1 : add a zero = a + zero := rfl
    have h2 : add zero a = zero + a := rfl
    rw [h1, h2, add_zero, zero_add]
  | succ b' ih =>
    show add a b'.succ = add b'.succ a
    have h1 : a + b'.succ = (a + b').succ := add_succ a b'
    have h2 : b'.succ + a = (b' + a).succ := succ_add b' a
    have h3 : (a + b').succ = (b' + a).succ := congrArg Nat.succ ih
    have step1 : add a b'.succ = (a + b').succ := h1
    have step2 : (a + b').succ = b'.succ + a := Eq.trans h3 (Eq.symm h2)
    exact Eq.trans step1 step2

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
