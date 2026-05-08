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

def Decimal.addOneBigEndian : ZeroMath.Sequences.List CardinalNatural.Peano → ZeroMath.Sequences.List CardinalNatural.Peano × Bool
  | _root_.List.nil => (ZeroMath.Sequences.List.empty, true)
  | _root_.List.cons d ds =>
    let (ds', carry) := Decimal.addOneBigEndian ds
    if carry then
      if CardinalNatural.Peano.successor d = CardinalNatural.Peano.ten then
        (ZeroMath.Sequences.List.firstElement CardinalNatural.Peano.zero ds', true)
      else
        (ZeroMath.Sequences.List.firstElement (CardinalNatural.Peano.successor d) ds', false)
    else
      (ZeroMath.Sequences.List.firstElement d ds', false)

def Decimal.successorHelper (l : ZeroMath.Sequences.List CardinalNatural.Peano) : ZeroMath.Sequences.List CardinalNatural.Peano :=
  let (l', carry) := Decimal.addOneBigEndian l
  if carry then
    ZeroMath.Sequences.List.firstElement (CardinalNatural.Peano.successor CardinalNatural.Peano.zero) l'
  else
    l'

theorem Decimal.addOneBigEndian_allLessThanTen (l : ZeroMath.Sequences.List CardinalNatural.Peano) (h : CardinalNatural.Peano.AllLessThanTen l) :
  CardinalNatural.Peano.AllLessThanTen (Decimal.addOneBigEndian l).1 := by
  induction l with
  | nil =>
    unfold addOneBigEndian
    unfold CardinalNatural.Peano.AllLessThanTen
    exact trivial
  | cons d ds ih =>
    unfold addOneBigEndian
    have h_ih : CardinalNatural.Peano.AllLessThanTen (addOneBigEndian ds).1 := by
      apply ih
      unfold CardinalNatural.Peano.AllLessThanTen at h
      exact h.right
    generalize h_add : addOneBigEndian ds = res
    rw [h_add] at h_ih
    cases res with
    | mk ds' carry =>
      dsimp only
      split
      · next h_carry =>
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
          · exact h_ih
        · next h_neq =>
          unfold CardinalNatural.Peano.AllLessThanTen
          constructor
          · unfold CardinalNatural.Peano.AllLessThanTen at h
            have hd_lt : d < CardinalNatural.Peano.ten := h.left
            have hd_succ_le : CardinalNatural.Peano.successor d ≤ CardinalNatural.Peano.ten := succ_le_of_lt hd_lt
            cases hd_succ_le with
            | inl hlt => exact hlt
            | inr heq => contradiction
          · exact h_ih
      · next h_no_carry =>
        unfold CardinalNatural.Peano.AllLessThanTen
        constructor
        · unfold CardinalNatural.Peano.AllLessThanTen at h
          exact h.left
        · exact h_ih

theorem Decimal.succ_ne_zero (a : CardinalNatural.Peano) : CardinalNatural.Peano.successor a ≠ CardinalNatural.Peano.zero := by
  intro contra
  cases contra

theorem Decimal.addOneBigEndian_hasNonZero (l : ZeroMath.Sequences.List CardinalNatural.Peano)
  (h_nz : CardinalNatural.Peano.HasNonZero l) :
  CardinalNatural.Peano.HasNonZero (Decimal.addOneBigEndian l).1 ∨ (Decimal.addOneBigEndian l).2 = true := by
  induction l with
  | nil =>
    unfold CardinalNatural.Peano.HasNonZero at h_nz
    cases h_nz
  | cons d ds ih =>
    unfold addOneBigEndian
    generalize h_add : addOneBigEndian ds = res
    cases res with
    | mk ds' carry =>
      dsimp only
      split
      · next h_carry =>
        split
        · next h_eq =>
          right
          rfl
        · next h_neq =>
          left
          unfold CardinalNatural.Peano.HasNonZero
          left
          exact Decimal.succ_ne_zero d
      · next h_no_carry =>
        unfold CardinalNatural.Peano.HasNonZero at h_nz
        cases h_nz with
        | inl h_d =>
          left
          unfold CardinalNatural.Peano.HasNonZero
          left
          exact h_d
        | inr h_ds =>
          have ih_app := ih h_ds
          rw [h_add] at ih_app
          dsimp only at ih_app
          cases ih_app with
          | inl h_ds' =>
            left
            unfold CardinalNatural.Peano.HasNonZero
            right
            exact h_ds'
          | inr h_carry_true =>
            rw [h_carry_true] at h_no_carry
            contradiction

theorem Decimal.successorHelper_hasNonZero (l : ZeroMath.Sequences.List CardinalNatural.Peano)
  (h_nz : CardinalNatural.Peano.HasNonZero l) :
  CardinalNatural.Peano.HasNonZero (Decimal.successorHelper l) := by
  unfold successorHelper
  generalize h_add : addOneBigEndian l = res
  cases res with
  | mk l' carry =>
    dsimp only
    split
    · next h_carry =>
      unfold CardinalNatural.Peano.HasNonZero
      left
      exact Decimal.succ_ne_zero CardinalNatural.Peano.zero
    · next h_no_carry =>
      have h_prop := Decimal.addOneBigEndian_hasNonZero l h_nz
      rw [h_add] at h_prop
      dsimp only at h_prop
      cases h_prop with
      | inl h1 => exact h1
      | inr h2 =>
        rw [h2] at h_no_carry
        contradiction

theorem Decimal.successorHelper_allLessThanTen (l : ZeroMath.Sequences.List CardinalNatural.Peano)
  (h : CardinalNatural.Peano.AllLessThanTen l) :
  CardinalNatural.Peano.AllLessThanTen (Decimal.successorHelper l) := by
  unfold successorHelper
  have h_add := Decimal.addOneBigEndian_allLessThanTen l h
  generalize h_eq : addOneBigEndian l = res
  rw [h_eq] at h_add
  cases res with
  | mk l' carry =>
    dsimp only
    dsimp only at h_add
    split
    · next h_carry =>
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
      · exact h_add
    · next h_no_carry =>
      exact h_add

def Decimal.successor (d : Decimal) : Decimal :=
  ⟨Decimal.successorHelper d.val, ⟨Decimal.successorHelper_allLessThanTen d.val d.property.left, Decimal.successorHelper_hasNonZero d.val d.property.right⟩⟩

def Decimal.one : Decimal :=
  ⟨ZeroMath.Sequences.List.firstElement (CardinalNatural.Peano.successor CardinalNatural.Peano.zero) ZeroMath.Sequences.List.empty, ⟨by
    unfold CardinalNatural.Peano.AllLessThanTen
    constructor
    · exact CardinalNatural.Peano.LessThan.step (CardinalNatural.Peano.LessThan.step (CardinalNatural.Peano.LessThan.step (CardinalNatural.Peano.LessThan.step (CardinalNatural.Peano.LessThan.step (CardinalNatural.Peano.LessThan.step (CardinalNatural.Peano.LessThan.step (CardinalNatural.Peano.LessThan.step (CardinalNatural.Peano.LessThan.base))))))))
    · exact trivial
  , by
    unfold CardinalNatural.Peano.HasNonZero
    left
    intro contra
    cases contra
  ⟩⟩

def Decimal.fromPeano : OrdinalNatural.Peano → Decimal
  | OrdinalNatural.Peano.one => Decimal.one
  | OrdinalNatural.Peano.successor p => Decimal.successor (Decimal.fromPeano p)

end ZeroMath.Numbers.OrdinalNatural
