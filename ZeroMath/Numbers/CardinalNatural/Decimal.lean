import ZeroMath.Numbers.CardinalNatural
import ZeroMath.Sequences.List

namespace ZeroMath.Numbers.CardinalNatural

def Decimal := { l : ZeroMath.Sequences.List Peano // Peano.AllLessThanTen l ∧ ZeroMath.Sequences.List.HasAtLeastOne l }

def Decimal.toPeanoHelper : ZeroMath.Sequences.List Peano → Peano → Peano
  | _root_.List.nil, acc => acc
  | _root_.List.cons d ds, acc => Decimal.toPeanoHelper ds (acc * Peano.ten + d)

def Decimal.toPeano (d : Decimal) : Peano :=
  Decimal.toPeanoHelper d.val Peano.zero

def Decimal.addOneBigEndian : ZeroMath.Sequences.List Peano → ZeroMath.Sequences.List Peano × Bool
  | _root_.List.nil => (ZeroMath.Sequences.List.empty, true)
  | _root_.List.cons d ds =>
    let (ds', carry) := Decimal.addOneBigEndian ds
    if carry then
      if Peano.successor d = Peano.ten then
        (ZeroMath.Sequences.List.firstElement Peano.zero ds', true)
      else
        (ZeroMath.Sequences.List.firstElement (Peano.successor d) ds', false)
    else
      (ZeroMath.Sequences.List.firstElement d ds', false)

def Decimal.successorHelper (l : ZeroMath.Sequences.List Peano) : ZeroMath.Sequences.List Peano :=
  let (l', carry) := Decimal.addOneBigEndian l
  if carry then
    ZeroMath.Sequences.List.firstElement (Peano.successor Peano.zero) l'
  else
    l'

theorem Decimal.addOneBigEndian_allLessThanTen (l : ZeroMath.Sequences.List Peano) (h : Peano.AllLessThanTen l) :
  Peano.AllLessThanTen (Decimal.addOneBigEndian l).1 := by
  induction l with
  | nil =>
    unfold addOneBigEndian
    unfold Peano.AllLessThanTen
    exact trivial
  | cons d ds ih =>
    unfold addOneBigEndian
    have h_ih : Peano.AllLessThanTen (addOneBigEndian ds).1 := by
      apply ih
      unfold Peano.AllLessThanTen at h
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
          unfold Peano.AllLessThanTen
          constructor
          · apply Peano.LessThan.step
            apply Peano.LessThan.step
            apply Peano.LessThan.step
            apply Peano.LessThan.step
            apply Peano.LessThan.step
            apply Peano.LessThan.step
            apply Peano.LessThan.step
            apply Peano.LessThan.step
            apply Peano.LessThan.step
            apply Peano.LessThan.base
          · exact h_ih
        · next h_neq =>
          unfold Peano.AllLessThanTen
          constructor
          · unfold Peano.AllLessThanTen at h
            have hd_lt : d < Peano.ten := h.left
            have hd_succ_le : Peano.successor d ≤ Peano.ten := Peano.succ_le_of_lt hd_lt
            cases hd_succ_le with
            | inl hlt => exact hlt
            | inr heq => contradiction
          · exact h_ih
      · next h_no_carry =>
        unfold Peano.AllLessThanTen
        constructor
        · unfold Peano.AllLessThanTen at h
          exact h.left
        · exact h_ih

theorem Decimal.addOneBigEndian_hasAtLeastOne (l : ZeroMath.Sequences.List Peano) (h : ZeroMath.Sequences.List.HasAtLeastOne l) :
  ZeroMath.Sequences.List.HasAtLeastOne (Decimal.addOneBigEndian l).1 ∨ (Decimal.addOneBigEndian l).2 = true := by
  induction l with
  | nil =>
    unfold ZeroMath.Sequences.List.HasAtLeastOne at h
    cases h
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
          left
          unfold ZeroMath.Sequences.List.HasAtLeastOne
          exact trivial
        · next h_neq =>
          left
          unfold ZeroMath.Sequences.List.HasAtLeastOne
          exact trivial
      · next h_no_carry =>
        left
        unfold ZeroMath.Sequences.List.HasAtLeastOne
        exact trivial

theorem Decimal.successorHelper_hasAtLeastOne (l : ZeroMath.Sequences.List Peano)
  (h : ZeroMath.Sequences.List.HasAtLeastOne l) :
  ZeroMath.Sequences.List.HasAtLeastOne (Decimal.successorHelper l) := by
  unfold successorHelper
  generalize h_add : addOneBigEndian l = res
  cases res with
  | mk l' carry =>
    dsimp only
    split
    · next h_carry =>
      unfold ZeroMath.Sequences.List.HasAtLeastOne
      exact trivial
    · next h_no_carry =>
      have h_prop := Decimal.addOneBigEndian_hasAtLeastOne l h
      rw [h_add] at h_prop
      dsimp only at h_prop
      cases h_prop with
      | inl h1 => exact h1
      | inr h2 =>
        rw [h2] at h_no_carry
        contradiction

theorem Decimal.successorHelper_allLessThanTen (l : ZeroMath.Sequences.List Peano)
  (h : Peano.AllLessThanTen l) :
  Peano.AllLessThanTen (Decimal.successorHelper l) := by
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
      unfold Peano.AllLessThanTen
      constructor
      · apply Peano.LessThan.step
        apply Peano.LessThan.step
        apply Peano.LessThan.step
        apply Peano.LessThan.step
        apply Peano.LessThan.step
        apply Peano.LessThan.step
        apply Peano.LessThan.step
        apply Peano.LessThan.step
        apply Peano.LessThan.base
      · exact h_add
    · next h_no_carry =>
      exact h_add

def Decimal.successor (d : Decimal) : Decimal :=
  ⟨Decimal.successorHelper d.val, ⟨Decimal.successorHelper_allLessThanTen d.val d.property.left, Decimal.successorHelper_hasAtLeastOne d.val d.property.right⟩⟩

def Decimal.zero : Decimal :=
  ⟨ZeroMath.Sequences.List.firstElement Peano.zero ZeroMath.Sequences.List.empty, by
    constructor
    · unfold Peano.AllLessThanTen
      constructor
      · apply Peano.LessThan.step
        apply Peano.LessThan.step
        apply Peano.LessThan.step
        apply Peano.LessThan.step
        apply Peano.LessThan.step
        apply Peano.LessThan.step
        apply Peano.LessThan.step
        apply Peano.LessThan.step
        apply Peano.LessThan.step
        apply Peano.LessThan.base
      · exact trivial
    · unfold ZeroMath.Sequences.List.HasAtLeastOne
      exact trivial⟩

def Decimal.fromPeano : Peano → Decimal
  | Nat.zero => Decimal.zero
  | Nat.succ p => Decimal.successor (Decimal.fromPeano p)

end ZeroMath.Numbers.CardinalNatural
