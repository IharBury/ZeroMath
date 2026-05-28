import ZeroMath.Numbers.CardinalNatural.Peano
import ZeroMath.Sequences.List

namespace ZeroMath.Numbers.OrdinalNatural

namespace Decimal

def AllLessThanTen : Sequences.List CardinalNatural.Peano → Prop
  | .empty => True
  | .firstElement d ds => d < CardinalNatural.Peano.ten ∧ AllLessThanTen ds

def HasNonZero : Sequences.List CardinalNatural.Peano → Prop
  | .empty => False
  | .firstElement d ds => d ≠ CardinalNatural.Peano.zero ∨ HasNonZero ds

end Decimal

def Decimal := { l : ZeroMath.Sequences.List CardinalNatural.Peano // Decimal.AllLessThanTen l ∧ Decimal.HasNonZero l }

namespace Decimal

def isNormalized (d : Decimal) : Bool :=
  match d.val with
  | .empty => false
  | .firstElement digit _ => decide (digit ≠ CardinalNatural.Peano.zero)

def normalizeList : ZeroMath.Sequences.List CardinalNatural.Peano → ZeroMath.Sequences.List CardinalNatural.Peano
  | .empty => ZeroMath.Sequences.List.empty
  | .firstElement d ds =>
    if d = CardinalNatural.Peano.zero then
      Decimal.normalizeList ds
    else
      ZeroMath.Sequences.List.firstElement d ds

theorem normalizeList_allLessThanTen (l : ZeroMath.Sequences.List CardinalNatural.Peano)
  (h : AllLessThanTen l) : AllLessThanTen (Decimal.normalizeList l) := by
  induction l with
  | empty =>
    unfold Decimal.normalizeList
    unfold AllLessThanTen
    exact trivial
  | firstElement d ds ih =>
    unfold Decimal.normalizeList
    by_cases h_zero : d = CardinalNatural.Peano.zero
    · simp [h_zero]
      apply ih
      unfold AllLessThanTen at h
      exact h.right
    · simp [h_zero]
      unfold AllLessThanTen
      unfold AllLessThanTen at h
      exact h

theorem normalizeList_hasNonZero (l : ZeroMath.Sequences.List CardinalNatural.Peano)
  (h : HasNonZero l) : HasNonZero (Decimal.normalizeList l) := by
  induction l with
  | empty =>
    unfold HasNonZero at h
    cases h
  | firstElement d ds ih =>
    unfold Decimal.normalizeList
    by_cases h_zero : d = CardinalNatural.Peano.zero
    · simp [h_zero]
      apply ih
      unfold HasNonZero at h
      cases h with
      | inl h_d =>
        contradiction
      | inr h_ds =>
        exact h_ds
    · simp [h_zero]
      unfold HasNonZero
      left
      exact h_zero

def normalize (d : Decimal) : Decimal :=
  ⟨normalizeList d.val, ⟨normalizeList_allLessThanTen d.val d.property.left, normalizeList_hasNonZero d.val d.property.right⟩⟩

def Equivalent (a b : Decimal) : Prop :=
  normalize a = normalize b

instance instSetoid : Setoid Decimal where
  r := Equivalent
  iseqv := {
    refl := by
      intro a
      rfl
    symm := by
      intro a b h
      exact h.symm
    trans := by
      intro a b c hab hbc
      exact Eq.trans hab hbc
  }

theorem equivalent_iff_normalize_eq (a b : Decimal) :
  a ≈ b ↔ normalize a = normalize b := by
  rfl

theorem equivalent_of_normalize_eq {a b : Decimal}
  (h : normalize a = normalize b) : a ≈ b := by
  exact h

theorem normalize_eq_of_equivalent {a b : Decimal}
  (h : a ≈ b) : normalize a = normalize b := by
  exact h

theorem normalizeList_startsNonZero (l : ZeroMath.Sequences.List CardinalNatural.Peano)
  (h : HasNonZero l) :
  match normalizeList l with
  | .empty => False
  | .firstElement digit _ => digit ≠ CardinalNatural.Peano.zero := by
  induction l with
  | empty =>
    unfold HasNonZero at h
    cases h
  | firstElement d ds ih =>
    unfold Decimal.normalizeList
    by_cases h_zero : d = CardinalNatural.Peano.zero
    · simp [h_zero]
      apply ih
      unfold HasNonZero at h
      cases h with
      | inl h_d => contradiction
      | inr h_ds => exact h_ds
    · rw [if_neg h_zero]
      change d ≠ CardinalNatural.Peano.zero
      exact h_zero

theorem normalize_isNormalized (d : Decimal) :
  isNormalized (normalize d) = true := by
  have h_start := normalizeList_startsNonZero d.val d.property.right
  unfold isNormalized
  change (match normalizeList d.val with
    | .empty => false
    | .firstElement digit _ => decide (digit ≠ CardinalNatural.Peano.zero)) = true
  cases h_norm : normalizeList d.val with
  | empty =>
    rw [h_norm] at h_start
    cases h_start
  | firstElement digit rest =>
    rw [h_norm] at h_start
    simp [h_start]

def toCardinalHelper : ZeroMath.Sequences.List CardinalNatural.Peano → CardinalNatural.Peano → CardinalNatural.Peano
  | .empty, acc => acc
  | .firstElement d ds, acc => toCardinalHelper ds (acc * CardinalNatural.Peano.ten + d)

def toCardinalList (l : ZeroMath.Sequences.List CardinalNatural.Peano) : CardinalNatural.Peano :=
  toCardinalHelper l CardinalNatural.Peano.zero

theorem toCardinalHelper_ne_zero (l : ZeroMath.Sequences.List CardinalNatural.Peano) (acc : CardinalNatural.Peano)
  (h : acc ≠ CardinalNatural.Peano.zero ∨ HasNonZero l) :
  toCardinalHelper l acc ≠ CardinalNatural.Peano.zero := by
  induction l generalizing acc with
  | empty =>
    cases h with
    | inl h_acc => exact h_acc
    | inr h_zero => cases h_zero
  | firstElement d ds ih =>
    apply ih
    cases h with
    | inl h_acc =>
      left
      intro contra
      have h1 : acc * CardinalNatural.Peano.ten + d = CardinalNatural.Peano.zero := contra
      have h2 : acc * CardinalNatural.Peano.ten = CardinalNatural.Peano.zero := CardinalNatural.Peano.eq_zero_of_add_eq_zero_l h1
      have h3 : acc = CardinalNatural.Peano.zero ∨ CardinalNatural.Peano.ten = CardinalNatural.Peano.zero := by
        cases acc with
        | zero => exact Or.inl rfl
        | successor a =>
          have h_nz : CardinalNatural.Peano.successor a * CardinalNatural.Peano.ten ≠ CardinalNatural.Peano.zero := by
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
        have h1 : acc * CardinalNatural.Peano.ten + d = CardinalNatural.Peano.zero := contra
        have h2 : d = CardinalNatural.Peano.zero := CardinalNatural.Peano.eq_zero_of_add_eq_zero_r h1
        exact h_d h2
      | inr h_ds =>
        right
        exact h_ds

theorem normalizeList_toCardinalList (l : ZeroMath.Sequences.List CardinalNatural.Peano) :
  toCardinalList (normalizeList l) = toCardinalList l := by
  induction l with
  | empty => rfl
  | firstElement d ds ih =>
    unfold Decimal.normalizeList
    by_cases h_zero : d = CardinalNatural.Peano.zero
    · rw [if_pos h_zero]
      unfold Decimal.toCardinalList at ih ⊢
      rw [h_zero]
      change Decimal.toCardinalHelper (Decimal.normalizeList ds) CardinalNatural.Peano.zero =
        Decimal.toCardinalHelper ds (CardinalNatural.Peano.zero * CardinalNatural.Peano.ten + CardinalNatural.Peano.zero)
      rw [CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.add_zero]
      exact ih
    · rw [if_neg h_zero]

theorem normalize_toCardinalList (d : Decimal) :
  toCardinalList (normalize d).val = toCardinalList d.val := by
  unfold normalize
  exact normalizeList_toCardinalList d.val

def toPeano (d : Decimal) : OrdinalNatural.Peano :=
  CardinalNatural.Peano.toOrdinal (toCardinalList d.val) (by
    have h : CardinalNatural.Peano.zero ≠ CardinalNatural.Peano.zero ∨ HasNonZero d.val := Or.inr d.property.right
    exact toCardinalHelper_ne_zero d.val CardinalNatural.Peano.zero h
  )

theorem toOrdinal_congr {a b : CardinalNatural.Peano} (h_eq : a = b)
  (ha : a ≠ CardinalNatural.Peano.zero) (hb : b ≠ CardinalNatural.Peano.zero) :
  CardinalNatural.Peano.toOrdinal a ha = CardinalNatural.Peano.toOrdinal b hb := by
  cases h_eq
  rfl

theorem normalize_toPeano (x : Decimal) : x.normalize.toPeano = x.toPeano := by
  unfold toPeano
  apply toOrdinal_congr
  exact normalize_toCardinalList x

end Decimal

end ZeroMath.Numbers.OrdinalNatural
