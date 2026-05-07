import ZeroMath.Numbers.CardinalNatural
import ZeroMath.Sequences.List

namespace ZeroMath.Numbers.OrdinalNatural

def Decimal := { l : ZeroMath.Sequences.List ZeroMath.Numbers.CardinalNatural.Peano // CardinalNatural.Peano.AllLessThanTen l ∧ CardinalNatural.Peano.HasNonZero l }

open ZeroMath.Numbers

-- Since CardinalNatural.Peano is an alias for Nat we can just use Nat operations
def Decimal.toCardinalHelper : ZeroMath.Sequences.List Nat → Nat → Nat
  | _root_.List.nil, acc => acc
  | _root_.List.cons d ds, acc => Decimal.toCardinalHelper ds (acc * 10 + d)

def Decimal.toCardinalList (l : ZeroMath.Sequences.List Nat) : Nat :=
  Decimal.toCardinalHelper l 0

theorem Nat.eq_zero_of_add_eq_zero_l {n m : Nat} (h : n + m = 0) : n = 0 := by
  cases n with
  | zero => rfl
  | succ n' =>
    cases m with
    | zero => cases h
    | succ m' =>
      have h1 : Nat.succ n' + Nat.succ m' = Nat.succ (Nat.succ n' + m') := Nat.add_succ (Nat.succ n') m'
      rw [h1] at h
      cases h

theorem Nat.eq_zero_of_add_eq_zero_r {n m : Nat} (h : n + m = 0) : m = 0 := by
  cases n with
  | zero =>
    have h1 : 0 + m = m := Nat.zero_add m
    rw [h1] at h
    exact h
  | succ n' =>
    cases m with
    | zero => rfl
    | succ m' =>
      have h1 : Nat.succ n' + Nat.succ m' = Nat.succ (Nat.succ n' + m') := Nat.add_succ (Nat.succ n') m'
      rw [h1] at h
      cases h

theorem Decimal.toCardinalHelper_ne_zero (l : ZeroMath.Sequences.List Nat) (acc : Nat)
  (h : acc ≠ 0 ∨ CardinalNatural.Peano.HasNonZero l) :
  Decimal.toCardinalHelper l acc ≠ 0 := by
  induction l generalizing acc with
  | nil =>
    cases h with
    | inl h_acc => exact h_acc
    | inr h_zero => cases h_zero
  | cons d ds ih =>
    apply ih
    cases h with
    | inl h_acc =>
      left
      intro contra
      have h1 : acc * 10 + d = 0 := contra
      have h2 : acc * 10 = 0 := Nat.eq_zero_of_add_eq_zero_l h1
      have h3 : acc = 0 ∨ 10 = 0 := by
        cases acc with
        | zero => exact Or.inl rfl
        | succ a =>
          have h_nz : Nat.succ a * 10 ≠ 0 := by
            intro hc
            cases hc
          contradiction
      cases h3 with
      | inl ha => exact h_acc ha
      | inr hb => contradiction
    | inr h_zero =>
      cases h_zero with
      | inl h_d =>
        left
        intro contra
        have h1 : acc * 10 + d = 0 := contra
        have h2 : d = 0 := Nat.eq_zero_of_add_eq_zero_r h1
        exact h_d h2
      | inr h_ds =>
        right
        exact h_ds

def Decimal.toPeano (d : Decimal) : OrdinalNatural.Peano :=
  OrdinalNatural.Peano.fromNat (Decimal.toCardinalList d.val) (by
    have h : 0 ≠ 0 ∨ CardinalNatural.Peano.HasNonZero d.val := Or.inr d.property.right
    exact Decimal.toCardinalHelper_ne_zero d.val 0 h
  )

end ZeroMath.Numbers.OrdinalNatural
