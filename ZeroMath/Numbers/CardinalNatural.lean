import ZeroMath.Logic.Trichotomy

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

def successor (a : Peano) : Peano := Nat.succ a

theorem add_zero (a : Peano) : a + zero = a := rfl

theorem zero_add (a : Peano) : zero + a = a := by
  induction a with
  | zero => rfl
  | succ a' ih => exact congrArg Nat.succ ih

theorem add_succ (a b : Peano) : a + b.successor = (a + b).successor := rfl

theorem succ_add (a b : Peano) : a.successor + b = (a + b).successor := by
  induction b with
  | zero => rfl
  | succ b' ih => exact congrArg Nat.succ ih

theorem add_assoc (a b c : Peano) : (a + b) + c = a + (b + c) := by
  induction c with
  | zero => rfl
  | succ c' ih => exact congrArg Nat.succ ih

theorem add_comm (a b : Peano) : a + b = b + a := by
  show a + b = b + a
  induction b with
  | zero =>
    show a + zero = zero + a
    rw [add_zero, zero_add]
  | succ b' ih =>
    show a + successor b' = successor b' + a
    rw [add_succ, ih, succ_add]

end Peano

inductive Peano.LessThan (a : Peano) : Peano → Prop where
  | base : Peano.LessThan a (a.successor)
  | step {b : Peano} : Peano.LessThan a b → Peano.LessThan a (b.successor)

instance : LT Peano where
  lt := Peano.LessThan

namespace Peano

theorem lt_trans {a b c : Peano} (hab : a < b) (hbc : b < c) : a < c := by
  induction hbc with
  | base => exact Peano.LessThan.step hab
  | step _ ih => exact Peano.LessThan.step ih

end Peano

def Peano.LessThanOrEqual (a b : Peano) : Prop :=
  a < b ∨ a = b

instance : LE Peano where
  le := Peano.LessThanOrEqual

namespace Peano

theorem le_trans {a b c : Peano} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  cases hab with
  | inl hab_lt =>
    cases hbc with
    | inl hbc_lt => exact Or.inl (lt_trans hab_lt hbc_lt)
    | inr hbc_eq =>
      rw [← hbc_eq]
      exact Or.inl hab_lt
  | inr hab_eq =>
    rw [hab_eq]
    exact hbc

theorem lt_of_succ_lt {a b : Peano} (h : a.successor < b) : a < b := by
  exact lt_trans LessThan.base h

theorem lt_of_succ_lt_succ {a b : Peano} (h : a.successor < b.successor) : a < b := by
  generalize hz : b.successor = z at h
  induction h generalizing b with
  | base =>
    cases hz
    exact LessThan.base
  | step hlt _ =>
    cases hz
    exact lt_of_succ_lt hlt

theorem le_of_succ_le_succ {a b : Peano} (h : a.successor ≤ b.successor) : a ≤ b := by
  cases h with
  | inl hlt =>
    exact Or.inl (lt_of_succ_lt_succ hlt)
  | inr heq =>
    have : a = b := Nat.succ.inj heq
    exact Or.inr this

theorem not_succ_le_zero {a : Peano} (h : a.successor ≤ zero) : False := by
  cases h with
  | inl hlt =>
    generalize hz : zero = z at hlt
    induction hlt with
    | base => cases hz
    | step _ _ => cases hz
  | inr heq => cases heq

def subtract (a : Peano) : (b : Peano) → b ≤ a → Peano
  | Nat.zero, _ => a
  | Nat.succ b', h =>
    match a, h with
    | Nat.zero, h' => False.elim (not_succ_le_zero h')
    | Nat.succ a', h' => subtract a' b' (le_of_succ_le_succ h')

theorem not_lt_zero (a : Peano) : ¬(a < zero) := by
  intro h
  generalize hz : zero = z at h
  induction h with
  | base => cases hz
  | step _ _ => cases hz

theorem not_lt_self (a : Peano) : ¬(a < a) := by
  induction a with
  | zero => exact not_lt_zero zero
  | succ a' ih =>
    intro h
    exact ih (lt_of_succ_lt_succ h)

theorem succ_lt_succ {a b : Peano} (h : a < b) : a.successor < b.successor := by
  induction h with
  | base => exact LessThan.base
  | step _ ih => exact LessThan.step ih

theorem ne_of_lt {a b : Peano} (h : a < b) : a ≠ b := by
  intro heq
  rw [heq] at h
  exact not_lt_self b h

theorem not_lt_of_lt {a b : Peano} (h : a < b) : ¬(b < a) := by
  intro hba
  exact not_lt_self a (lt_trans h hba)

theorem zero_lt_succ (x : Peano) : zero < x.successor := by
  induction x with
  | zero => exact LessThan.base
  | succ x' ih => exact LessThan.step ih

theorem zero_le (x : Peano) : x = zero ∨ zero < x := by
  cases x with
  | zero => exact Or.inl rfl
  | succ x' => exact Or.inr (zero_lt_succ x')

theorem trichotomy_or (x y : Peano) : x < y ∨ x = y ∨ y < x := by
  induction x generalizing y with
  | zero =>
    cases zero_le y with
    | inl h => exact Or.inr (Or.inl h.symm)
    | inr h => exact Or.inl h
  | succ x ihx =>
    cases y with
    | zero =>
      exact Or.inr (Or.inr (zero_lt_succ x))
    | succ y =>
      cases ihx y with
      | inl h => exact Or.inl (succ_lt_succ h)
      | inr h =>
        cases h with
        | inl h =>
          rw [h]
          exact Or.inr (Or.inl rfl)
        | inr h =>
          exact Or.inr (Or.inr (succ_lt_succ h))

theorem trichotomy (x y : Peano) : ZeroMath.Logic.Trichotomy (x < y) (x = y) (y < x) := by
  cases trichotomy_or x y with
  | inl h =>
    exact ZeroMath.Logic.Trichotomy.first h (ne_of_lt h) (not_lt_of_lt h)
  | inr h =>
    cases h with
    | inl h =>
      subst h
      exact ZeroMath.Logic.Trichotomy.second rfl (not_lt_self x) (not_lt_self x)
    | inr h =>
      exact ZeroMath.Logic.Trichotomy.third h (not_lt_of_lt h) (ne_of_lt h).symm

end Peano

end ZeroMath.Numbers.CardinalNatural
