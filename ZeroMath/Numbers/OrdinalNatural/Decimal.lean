import ZeroMath.Numbers.CardinalNatural
import ZeroMath.Sequences.List

namespace ZeroMath.Numbers.OrdinalNatural

def Decimal := { l : ZeroMath.Sequences.List ZeroMath.Numbers.CardinalNatural.Peano // CardinalNatural.Peano.AllLessThanTen l ∧ CardinalNatural.Peano.HasNonZero l }

open ZeroMath.Numbers

def Decimal.toCardinalHelper : ZeroMath.Sequences.List CardinalNatural.Peano → CardinalNatural.Peano → CardinalNatural.Peano
  | _root_.List.nil, acc => acc
  | _root_.List.cons d ds, acc => Decimal.toCardinalHelper ds (acc * CardinalNatural.Peano.ten + d)

def Decimal.toCardinalList (l : ZeroMath.Sequences.List CardinalNatural.Peano) : CardinalNatural.Peano :=
  Decimal.toCardinalHelper l CardinalNatural.Peano.zero

theorem Decimal.toCardinalHelper_ne_zero (l : ZeroMath.Sequences.List CardinalNatural.Peano) (acc : CardinalNatural.Peano)
  (h : acc ≠ CardinalNatural.Peano.zero ∨ CardinalNatural.Peano.HasNonZero l) :
  Decimal.toCardinalHelper l acc ≠ CardinalNatural.Peano.zero := by
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
      have h1 : acc * CardinalNatural.Peano.ten + d = CardinalNatural.Peano.zero := contra
      have h2 : acc * CardinalNatural.Peano.ten = CardinalNatural.Peano.zero := CardinalNatural.Peano.eq_zero_of_add_eq_zero_l h1
      have h3 : acc = CardinalNatural.Peano.zero ∨ CardinalNatural.Peano.ten = CardinalNatural.Peano.zero := by
        cases acc with
        | zero => exact Or.inl rfl
        | succ a =>
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

def Decimal.toPeano (d : Decimal) : OrdinalNatural.Peano :=
  OrdinalNatural.Peano.fromNat (Decimal.toCardinalList d.val) (by
    have h : CardinalNatural.Peano.zero ≠ CardinalNatural.Peano.zero ∨ CardinalNatural.Peano.HasNonZero d.val := Or.inr d.property.right
    exact Decimal.toCardinalHelper_ne_zero d.val CardinalNatural.Peano.zero h
  )

theorem succ_le_of_lt {a b : CardinalNatural.Peano} (h : a < b) : CardinalNatural.Peano.successor a ≤ b := by
  induction h with
  | base => exact Or.inr rfl
  | step hlt ih =>
    cases ih with
    | inl h1 => exact Or.inl (CardinalNatural.Peano.LessThan.step h1)
    | inr h2 =>
      rw [h2]
      exact Or.inl CardinalNatural.Peano.LessThan.base

def Decimal.successorHelper : ZeroMath.Sequences.List CardinalNatural.Peano → ZeroMath.Sequences.List CardinalNatural.Peano
  | _root_.List.nil => _root_.List.cons (CardinalNatural.Peano.successor CardinalNatural.Peano.zero) _root_.List.nil
  | _root_.List.cons d ds =>
    if CardinalNatural.Peano.successor d = CardinalNatural.Peano.ten then
      _root_.List.cons CardinalNatural.Peano.zero (Decimal.successorHelper ds)
    else
      _root_.List.cons (CardinalNatural.Peano.successor d) ds

theorem Decimal.successorHelper_allLessThanTen (l : ZeroMath.Sequences.List CardinalNatural.Peano) (h : CardinalNatural.Peano.AllLessThanTen l) :
  CardinalNatural.Peano.AllLessThanTen (Decimal.successorHelper l) := by
  induction l with
  | nil =>
    unfold successorHelper
    unfold CardinalNatural.Peano.AllLessThanTen
    constructor
    · apply CardinalNatural.Peano.LessThan.step
      apply CardinalNatural.Peano.LessThan.step
      apply CardinalNatural.Peano.LessThan.step
      apply CardinalNatural.Peano.LessThan.step
      apply CardinalNatural.Peano.LessThan.step
      apply CardinalNatural.Peano.LessThan.step
      apply CardinalNatural.Peano.LessThan.step
      apply CardinalNatural.Peano.LessThan.step
      apply CardinalNatural.Peano.LessThan.base
    · exact trivial
  | cons d ds ih =>
    unfold successorHelper
    split
    · next h_eq =>
      unfold CardinalNatural.Peano.AllLessThanTen
      constructor
      · apply CardinalNatural.Peano.LessThan.step
        apply CardinalNatural.Peano.LessThan.step
        apply CardinalNatural.Peano.LessThan.step
        apply CardinalNatural.Peano.LessThan.step
        apply CardinalNatural.Peano.LessThan.step
        apply CardinalNatural.Peano.LessThan.step
        apply CardinalNatural.Peano.LessThan.step
        apply CardinalNatural.Peano.LessThan.step
        apply CardinalNatural.Peano.LessThan.step
        apply CardinalNatural.Peano.LessThan.base
      · apply ih
        unfold CardinalNatural.Peano.AllLessThanTen at h
        exact h.right
    · next h_neq =>
      unfold CardinalNatural.Peano.AllLessThanTen
      constructor
      · unfold CardinalNatural.Peano.AllLessThanTen at h
        have hd_lt : d < CardinalNatural.Peano.ten := h.left
        have hd_succ_le : CardinalNatural.Peano.successor d ≤ CardinalNatural.Peano.ten := succ_le_of_lt hd_lt
        cases hd_succ_le with
        | inl hlt => exact hlt
        | inr heq => contradiction
      · unfold CardinalNatural.Peano.AllLessThanTen at h
        exact h.right

theorem Decimal.successorHelper_hasNonZero (l : ZeroMath.Sequences.List CardinalNatural.Peano) :
  CardinalNatural.Peano.HasNonZero (Decimal.successorHelper l) := by
  induction l with
  | nil =>
    unfold successorHelper
    unfold CardinalNatural.Peano.HasNonZero
    left
    intro contra
    cases contra
  | cons d ds ih =>
    unfold successorHelper
    split
    · next h_eq =>
      unfold CardinalNatural.Peano.HasNonZero
      right
      exact ih
    · next h_neq =>
      unfold CardinalNatural.Peano.HasNonZero
      left
      intro contra
      cases contra

def Decimal.successor (d : Decimal) : Decimal :=
  ⟨Decimal.successorHelper d.val, ⟨Decimal.successorHelper_allLessThanTen d.val d.property.left, Decimal.successorHelper_hasNonZero d.val⟩⟩

end ZeroMath.Numbers.OrdinalNatural
