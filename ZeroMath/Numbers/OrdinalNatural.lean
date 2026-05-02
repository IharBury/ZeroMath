import ZeroMath.Logic.Trichotomy
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
  Peano.LessThan a b ∨ a = b

instance : LE Peano where
  le := Peano.LessThanOrEqual



namespace Peano

def predecessor (a : Peano) (h : a ≠ one) : Peano :=
  match a with
  | one => False.elim (h rfl)
  | successor b => b

def add (a : Peano) : Peano → Peano
  | one => successor a
  | successor b => successor (add a b)

instance : Add Peano where
  add := add

theorem succ_lt_succ {x y : Peano} (h : x < y) : successor x < successor y := by
  induction h with
  | base => exact LessThan.base
  | step _ ih => exact LessThan.step ih

theorem lt_trans {x y z : Peano} (h1 : x < y) (h2 : y < z) : x < z := by
  induction h2 with
  | base => exact LessThan.step h1
  | step _ ih => exact LessThan.step ih

theorem lt_of_succ_lt {x y : Peano} (h : successor x < y) : x < y := by
  exact lt_trans LessThan.base h

theorem lt_of_succ_lt_succ {x y : Peano} (h : successor x < successor y) : x < y := by
  generalize hy : successor y = sy at h
  induction h generalizing y with
  | base =>
    cases hy
    exact LessThan.base
  | step h1 _ =>
    cases hy
    exact lt_of_succ_lt h1

def sub (a : Peano) : (b : Peano) → b < a → Peano
  | one, h =>
    match a, h with
    | successor a', _ => a'
  | successor b', h =>
    match a, h with
    | successor a', h' => sub a' b' (lt_of_succ_lt_succ h')

theorem not_lt_one (x : Peano) : ¬ (x < one) := by
  intro h
  generalize ho : one = o at h
  induction h with
  | base => cases ho
  | step _ _ => cases ho

theorem not_lt_self (x : Peano) : ¬ (x < x) := by
  induction x with
  | one => exact not_lt_one one
  | successor x ih =>
    intro h
    exact ih (lt_of_succ_lt_succ h)

theorem not_lt_of_lt {x y : Peano} (h : x < y) : ¬ (y < x) := by
  intro h2
  have h3 := lt_trans h h2
  exact not_lt_self x h3

theorem ne_of_lt {x y : Peano} (h : x < y) : x ≠ y := by
  intro heq
  subst heq
  exact not_lt_self x h

theorem one_lt_succ (x : Peano) : one < successor x := by
  induction x with
  | one => exact LessThan.base
  | successor x ih => exact LessThan.step ih

theorem one_le (x : Peano) : x = one ∨ one < x := by
  induction x with
  | one => exact Or.inl rfl
  | successor x _ => exact Or.inr (one_lt_succ x)

theorem trichotomy_or (x y : Peano) : x < y ∨ x = y ∨ y < x := by
  induction x generalizing y with
  | one =>
    cases one_le y with
    | inl h => exact Or.inr (Or.inl h.symm)
    | inr h => exact Or.inl h
  | successor x ihx =>
    cases y with
    | one =>
      exact Or.inr (Or.inr (one_lt_succ x))
    | successor y =>
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

end ZeroMath.Numbers.OrdinalNatural
