import ZeroMath.Numbers.CardinalNatural
import ZeroMath.Sequences.List

namespace ZeroMath.Numbers.OrdinalNatural

def Decimal := { l : ZeroMath.Sequences.List ZeroMath.Numbers.CardinalNatural.Peano // CardinalNatural.Peano.AllLessThanTen l ∧ CardinalNatural.Peano.HasNonZero l }

open ZeroMath.Numbers

def Decimal.isNormalized (d : Decimal) : Bool :=
  match d.val with
  | _root_.List.nil => false
  | _root_.List.cons digit _ => decide (digit ≠ CardinalNatural.Peano.zero)


def Decimal.normalizeList : ZeroMath.Sequences.List CardinalNatural.Peano → ZeroMath.Sequences.List CardinalNatural.Peano
  | _root_.List.nil => ZeroMath.Sequences.List.empty
  | _root_.List.cons d ds =>
    if d = CardinalNatural.Peano.zero then
      Decimal.normalizeList ds
    else
      ZeroMath.Sequences.List.firstElement d ds

theorem Decimal.normalizeList_allLessThanTen (l : ZeroMath.Sequences.List CardinalNatural.Peano)
  (h : CardinalNatural.Peano.AllLessThanTen l) :
  CardinalNatural.Peano.AllLessThanTen (Decimal.normalizeList l) := by
  induction l with
  | nil =>
    unfold Decimal.normalizeList
    unfold CardinalNatural.Peano.AllLessThanTen
    exact trivial
  | cons d ds ih =>
    unfold Decimal.normalizeList
    by_cases h_zero : d = CardinalNatural.Peano.zero
    · simp [h_zero]
      apply ih
      unfold CardinalNatural.Peano.AllLessThanTen at h
      exact h.right
    · simp [h_zero]
      unfold CardinalNatural.Peano.AllLessThanTen
      unfold CardinalNatural.Peano.AllLessThanTen at h
      exact h

theorem Decimal.normalizeList_hasNonZero (l : ZeroMath.Sequences.List CardinalNatural.Peano)
  (h : CardinalNatural.Peano.HasNonZero l) :
  CardinalNatural.Peano.HasNonZero (Decimal.normalizeList l) := by
  induction l with
  | nil =>
    unfold CardinalNatural.Peano.HasNonZero at h
    cases h
  | cons d ds ih =>
    unfold Decimal.normalizeList
    by_cases h_zero : d = CardinalNatural.Peano.zero
    · simp [h_zero]
      apply ih
      unfold CardinalNatural.Peano.HasNonZero at h
      cases h with
      | inl h_d =>
        contradiction
      | inr h_ds =>
        exact h_ds
    · simp [h_zero]
      unfold CardinalNatural.Peano.HasNonZero
      left
      exact h_zero

def Decimal.normalize (d : Decimal) : Decimal :=
  ⟨Decimal.normalizeList d.val, ⟨Decimal.normalizeList_allLessThanTen d.val d.property.left, Decimal.normalizeList_hasNonZero d.val d.property.right⟩⟩

def Decimal.Equivalent (a b : Decimal) : Prop :=
  Decimal.normalize a = Decimal.normalize b

instance Decimal.instSetoid : Setoid Decimal where
  r := Decimal.Equivalent
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

theorem Decimal.equivalent_iff_normalize_eq (a b : Decimal) :
  a ≈ b ↔ Decimal.normalize a = Decimal.normalize b := by
  rfl

theorem Decimal.equivalent_of_normalize_eq {a b : Decimal}
  (h : Decimal.normalize a = Decimal.normalize b) : a ≈ b := by
  exact h

theorem Decimal.normalize_eq_of_equivalent {a b : Decimal}
  (h : a ≈ b) : Decimal.normalize a = Decimal.normalize b := by
  exact h

theorem Decimal.normalizeList_startsNonZero (l : ZeroMath.Sequences.List CardinalNatural.Peano)
  (h : CardinalNatural.Peano.HasNonZero l) :
  match Decimal.normalizeList l with
  | _root_.List.nil => False
  | _root_.List.cons digit _ => digit ≠ CardinalNatural.Peano.zero := by
  induction l with
  | nil =>
    unfold CardinalNatural.Peano.HasNonZero at h
    cases h
  | cons d ds ih =>
    unfold Decimal.normalizeList
    by_cases h_zero : d = CardinalNatural.Peano.zero
    · simp [h_zero]
      apply ih
      unfold CardinalNatural.Peano.HasNonZero at h
      cases h with
      | inl h_d => contradiction
      | inr h_ds => exact h_ds
    · rw [if_neg h_zero]
      change d ≠ CardinalNatural.Peano.zero
      exact h_zero

theorem Decimal.normalize_isNormalized (d : Decimal) :
  Decimal.isNormalized (Decimal.normalize d) = true := by
  have h_start := Decimal.normalizeList_startsNonZero d.val d.property.right
  unfold Decimal.isNormalized
  change (match Decimal.normalizeList d.val with
    | _root_.List.nil => false
    | _root_.List.cons digit _ => decide (digit ≠ CardinalNatural.Peano.zero)) = true
  cases h_norm : Decimal.normalizeList d.val with
  | nil =>
    rw [h_norm] at h_start
    cases h_start
  | cons digit rest =>
    rw [h_norm] at h_start
    simp [h_start]

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

theorem Decimal.normalizeList_toCardinalList (l : ZeroMath.Sequences.List CardinalNatural.Peano) :
  Decimal.toCardinalList (Decimal.normalizeList l) = Decimal.toCardinalList l := by
  induction l with
  | nil => rfl
  | cons d ds ih =>
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
      rfl

theorem Decimal.normalize_toCardinalList (d : Decimal) :
  Decimal.toCardinalList (Decimal.normalize d).val = Decimal.toCardinalList d.val := by
  unfold Decimal.normalize
  exact Decimal.normalizeList_toCardinalList d.val


def Decimal.toPeano (d : Decimal) : OrdinalNatural.Peano :=
  OrdinalNatural.Peano.fromNat (Decimal.toCardinalList d.val) (by
    have h : CardinalNatural.Peano.zero ≠ CardinalNatural.Peano.zero ∨ CardinalNatural.Peano.HasNonZero d.val := Or.inr d.property.right
    exact Decimal.toCardinalHelper_ne_zero d.val CardinalNatural.Peano.zero h
  )

theorem Decimal.normalize_toPeano (x : Decimal) :
  x.normalize.toPeano = x.toPeano := by
  unfold Decimal.toPeano
  apply OrdinalNatural.Peano.fromNat_eq_of_eq
  exact Decimal.normalize_toCardinalList x

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
            have hd_succ_le : CardinalNatural.Peano.successor d ≤ CardinalNatural.Peano.ten := CardinalNatural.Peano.succ_le_of_lt hd_lt
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
          exact CardinalNatural.Peano.succ_ne_zero d
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
      exact CardinalNatural.Peano.succ_ne_zero CardinalNatural.Peano.zero
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


theorem Decimal.addOneBigEndian_toCardinalHelper (l : ZeroMath.Sequences.List CardinalNatural.Peano)
  (h : CardinalNatural.Peano.AllLessThanTen l) (acc : CardinalNatural.Peano) :
  Decimal.toCardinalHelper (Decimal.addOneBigEndian l).1
      (if (Decimal.addOneBigEndian l).2 then acc + CardinalNatural.Peano.successor CardinalNatural.Peano.zero else acc) =
    Decimal.toCardinalHelper l acc + CardinalNatural.Peano.successor CardinalNatural.Peano.zero := by
  induction l generalizing acc with
  | nil =>
    unfold Decimal.addOneBigEndian
    unfold Decimal.toCardinalHelper
    rfl
  | cons d ds ih =>
    have h_tail : CardinalNatural.Peano.AllLessThanTen ds := by
      unfold CardinalNatural.Peano.AllLessThanTen at h
      exact h.right
    generalize h_add : Decimal.addOneBigEndian ds = res
    cases res with
    | mk ds' carry =>
      have ih_acc :
        Decimal.toCardinalHelper ds'
            (if carry then (acc * CardinalNatural.Peano.ten + d) + CardinalNatural.Peano.successor CardinalNatural.Peano.zero else acc * CardinalNatural.Peano.ten + d) =
          Decimal.toCardinalHelper ds (acc * CardinalNatural.Peano.ten + d) + CardinalNatural.Peano.successor CardinalNatural.Peano.zero := by
        have ih0 := ih h_tail (acc * CardinalNatural.Peano.ten + d)
        rw [h_add] at ih0
        exact ih0
      cases carry with
      | false =>
        simp [Decimal.addOneBigEndian, h_add, Decimal.toCardinalHelper] at ih_acc ⊢
        exact ih_acc
      | true =>
        simp [Decimal.addOneBigEndian, h_add, Decimal.toCardinalHelper] at ih_acc ⊢
        by_cases h_eq : CardinalNatural.Peano.successor d = CardinalNatural.Peano.ten
        · simp [h_eq]
          rw [← ih_acc]
          have h_arg : CardinalNatural.Peano.successor acc * CardinalNatural.Peano.ten + CardinalNatural.Peano.zero =
              acc * CardinalNatural.Peano.ten + d + CardinalNatural.Peano.successor CardinalNatural.Peano.zero := by
            rw [CardinalNatural.Peano.add_zero]
            rw [CardinalNatural.Peano.succ_multiply]
            rw [← h_eq]
            rfl
          change Decimal.toCardinalHelper ds' (CardinalNatural.Peano.successor acc * CardinalNatural.Peano.ten + CardinalNatural.Peano.zero) =
            Decimal.toCardinalHelper ds' (acc * CardinalNatural.Peano.ten + d + CardinalNatural.Peano.successor CardinalNatural.Peano.zero)
          rw [h_arg]
        · simp [h_eq]
          rw [← ih_acc]
          rfl

theorem Decimal.successorHelper_toCardinalList (l : ZeroMath.Sequences.List CardinalNatural.Peano)
  (h : CardinalNatural.Peano.AllLessThanTen l) :
  Decimal.toCardinalList (Decimal.successorHelper l) =
    Decimal.toCardinalList l + CardinalNatural.Peano.successor CardinalNatural.Peano.zero := by
  unfold Decimal.successorHelper
  unfold Decimal.toCardinalList
  have h_add := Decimal.addOneBigEndian_toCardinalHelper l h CardinalNatural.Peano.zero
  generalize h_eq : Decimal.addOneBigEndian l = res
  rw [h_eq] at h_add
  cases res with
  | mk l' carry =>
    dsimp only at h_add
    dsimp only
    cases carry with
    | false =>
      exact h_add
    | true =>
      exact h_add

def Decimal.successor (d : Decimal) : Decimal :=
  ⟨Decimal.successorHelper d.val, ⟨Decimal.successorHelper_allLessThanTen d.val d.property.left, Decimal.successorHelper_hasNonZero d.val d.property.right⟩⟩

theorem Decimal.successor_toCardinalList (d : Decimal) :
  Decimal.toCardinalList (Decimal.successor d).val =
    Decimal.toCardinalList d.val + CardinalNatural.Peano.successor CardinalNatural.Peano.zero := by
  unfold Decimal.successor
  dsimp only
  exact Decimal.successorHelper_toCardinalList d.val d.property.left

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


def Decimal.columnarAddDigit (a b : CardinalNatural.Peano) (carry : Bool) : CardinalNatural.Peano × Bool :=
  let total := _root_.Nat.add (_root_.Nat.add a b)
    (if carry then CardinalNatural.Peano.successor CardinalNatural.Peano.zero else CardinalNatural.Peano.zero)
  if _root_.Nat.blt total CardinalNatural.Peano.ten then
    (total, false)
  else
    (_root_.Nat.sub total CardinalNatural.Peano.ten, true)

def Decimal.addAlignedLists :
    ZeroMath.Sequences.List CardinalNatural.Peano →
    ZeroMath.Sequences.List CardinalNatural.Peano →
    ZeroMath.Sequences.List CardinalNatural.Peano × Bool
  | _root_.List.nil, _root_.List.nil => (ZeroMath.Sequences.List.empty, false)
  | _root_.List.cons a as, _root_.List.nil =>
    let (tail, carry) := Decimal.addAlignedLists as _root_.List.nil
    let (digit, nextCarry) := Decimal.columnarAddDigit a CardinalNatural.Peano.zero carry
    (ZeroMath.Sequences.List.firstElement digit tail, nextCarry)
  | _root_.List.nil, _root_.List.cons b bs =>
    let (tail, carry) := Decimal.addAlignedLists _root_.List.nil bs
    let (digit, nextCarry) := Decimal.columnarAddDigit CardinalNatural.Peano.zero b carry
    (ZeroMath.Sequences.List.firstElement digit tail, nextCarry)
  | _root_.List.cons a as, _root_.List.cons b bs =>
    let (tail, carry) := Decimal.addAlignedLists as bs
    let (digit, nextCarry) := Decimal.columnarAddDigit a b carry
    (ZeroMath.Sequences.List.firstElement digit tail, nextCarry)
termination_by a b => a.length + b.length

def Decimal.lengthList {α : Type u} : ZeroMath.Sequences.List α → CardinalNatural.Peano
  | _root_.List.nil => CardinalNatural.Peano.zero
  | _root_.List.cons _ xs => CardinalNatural.Peano.successor (Decimal.lengthList xs)

def Decimal.leftPadZeros : CardinalNatural.Peano → ZeroMath.Sequences.List CardinalNatural.Peano → ZeroMath.Sequences.List CardinalNatural.Peano
  | Nat.zero, l => l
  | Nat.succ n, l => ZeroMath.Sequences.List.firstElement CardinalNatural.Peano.zero (Decimal.leftPadZeros n l)

def Decimal.alignAndAddLists (a b : ZeroMath.Sequences.List CardinalNatural.Peano) :
    ZeroMath.Sequences.List CardinalNatural.Peano × Bool :=
  let aLength := Decimal.lengthList a
  let bLength := Decimal.lengthList b
  if _root_.Nat.blt aLength bLength then
    Decimal.addAlignedLists (Decimal.leftPadZeros (_root_.Nat.sub bLength aLength) a) b
  else
    Decimal.addAlignedLists a (Decimal.leftPadZeros (_root_.Nat.sub aLength bLength) b)

def Decimal.finishColumnarSum (sum : ZeroMath.Sequences.List CardinalNatural.Peano × Bool) :
    ZeroMath.Sequences.List CardinalNatural.Peano :=
  let (digits, carry) := sum
  if carry then
    ZeroMath.Sequences.List.firstElement (CardinalNatural.Peano.successor CardinalNatural.Peano.zero) digits
  else
    digits

theorem Decimal.zero_lt_successor (n : CardinalNatural.Peano) :
  CardinalNatural.Peano.zero < CardinalNatural.Peano.successor n := by
  induction n with
  | zero => exact CardinalNatural.Peano.LessThan.base
  | succ n ih => exact CardinalNatural.Peano.LessThan.step ih

theorem Decimal.cardinalLt_of_natLt {a b : CardinalNatural.Peano} (h : _root_.Nat.lt a b) : a < b := by
  induction b generalizing a with
  | zero =>
    exact False.elim (Nat.not_lt_zero a h)
  | succ b ih =>
    cases a with
    | zero =>
      exact Decimal.zero_lt_successor b
    | succ a =>
      have h_pred : _root_.Nat.lt a b := Nat.lt_of_succ_lt_succ h
      exact CardinalNatural.Peano.succ_lt_succ (ih h_pred)

theorem Decimal.natLt_of_cardinalLt {a b : CardinalNatural.Peano} (h : a < b) : _root_.Nat.lt a b := by
  induction h with
  | base =>
    exact Nat.lt_add_one _
  | step _ ih =>
    exact Nat.lt_succ_of_lt ih

theorem Decimal.zero_lt_ten : CardinalNatural.Peano.zero < CardinalNatural.Peano.ten := by
  apply Decimal.cardinalLt_of_natLt
  exact Nat.zero_lt_succ 9

theorem Decimal.one_lt_ten : CardinalNatural.Peano.successor CardinalNatural.Peano.zero < CardinalNatural.Peano.ten := by
  apply Decimal.cardinalLt_of_natLt
  exact Nat.succ_lt_succ (Nat.zero_lt_succ 8)

theorem Decimal.columnarAddDigit_allLessThanTenBool (a b : CardinalNatural.Peano) (carry : Bool)
  (ha : _root_.Nat.blt a CardinalNatural.Peano.ten = true) (hb : _root_.Nat.blt b CardinalNatural.Peano.ten = true) :
  _root_.Nat.blt (Decimal.columnarAddDigit a b carry).1 CardinalNatural.Peano.ten = true := by
  unfold Decimal.columnarAddDigit
  have ha_lt : _root_.Nat.lt a CardinalNatural.Peano.ten := Nat.blt_eq.mp ha
  have hb_lt : _root_.Nat.lt b CardinalNatural.Peano.ten := Nat.blt_eq.mp hb
  have ha_bound : _root_.Nat.lt a (10 : Nat) := by
    unfold CardinalNatural.Peano.ten at ha_lt
    exact ha_lt
  have hb_bound : _root_.Nat.lt b (10 : Nat) := by
    unfold CardinalNatural.Peano.ten at hb_lt
    exact hb_lt
  cases carry
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split
    · next h => exact h
    · next h =>
      apply Nat.blt_eq.mpr
      unfold CardinalNatural.Peano.ten at h ⊢
      have h_not_lt : ¬ _root_.Nat.lt (_root_.Nat.add (_root_.Nat.add a b) CardinalNatural.Peano.zero) 10 := by
        intro ht
        exact h (Nat.blt_eq.mpr ht)
      have h_ge : 10 ≤ _root_.Nat.add (_root_.Nat.add a b) CardinalNatural.Peano.zero := Nat.le_of_not_gt h_not_lt
      have h_ab : _root_.Nat.add a b < 10 + 10 := Nat.add_lt_add ha_bound hb_bound
      have h_total : _root_.Nat.add (_root_.Nat.add a b) CardinalNatural.Peano.zero < 10 + 10 := by
        simpa [CardinalNatural.Peano.zero] using h_ab
      exact Nat.sub_lt_right_of_lt_add h_ge h_total
  · simp only [↓reduceIte]
    split
    · next h => exact h
    · next h =>
      apply Nat.blt_eq.mpr
      unfold CardinalNatural.Peano.ten at h ⊢
      have h_not_lt : ¬ _root_.Nat.lt (_root_.Nat.add (_root_.Nat.add a b) (CardinalNatural.Peano.successor CardinalNatural.Peano.zero)) 10 := by
        intro ht
        exact h (Nat.blt_eq.mpr ht)
      have h_ge : 10 ≤ _root_.Nat.add (_root_.Nat.add a b) (CardinalNatural.Peano.successor CardinalNatural.Peano.zero) := Nat.le_of_not_gt h_not_lt
      have hb1 : _root_.Nat.le (_root_.Nat.add b (CardinalNatural.Peano.successor CardinalNatural.Peano.zero)) 10 := by
        unfold CardinalNatural.Peano.successor CardinalNatural.Peano.zero
        exact Nat.succ_le_of_lt hb_bound
      have h_total : _root_.Nat.add (_root_.Nat.add a b) (CardinalNatural.Peano.successor CardinalNatural.Peano.zero) < 10 + 10 := by
        have hab := Nat.add_lt_add_of_lt_of_le ha_bound hb1
        simpa [Nat.add_assoc] using hab
      exact Nat.sub_lt_right_of_lt_add h_ge h_total

def Decimal.allLessThanTenBool : ZeroMath.Sequences.List CardinalNatural.Peano → Bool
  | _root_.List.nil => true
  | _root_.List.cons digit rest =>
    if _root_.Nat.blt digit CardinalNatural.Peano.ten then
      Decimal.allLessThanTenBool rest
    else
      false

theorem Decimal.allLessThanTenBool_sound (digits : ZeroMath.Sequences.List CardinalNatural.Peano)
  (h : Decimal.allLessThanTenBool digits = true) : CardinalNatural.Peano.AllLessThanTen digits := by
  induction digits with
  | nil =>
    unfold Decimal.allLessThanTenBool at h
    unfold CardinalNatural.Peano.AllLessThanTen
    exact trivial
  | cons digit rest ih =>
    unfold Decimal.allLessThanTenBool at h
    by_cases h_digit : _root_.Nat.blt digit CardinalNatural.Peano.ten = true
    · simp [h_digit] at h
      unfold CardinalNatural.Peano.AllLessThanTen
      constructor
      · exact Decimal.cardinalLt_of_natLt (Nat.blt_eq.mp h_digit)
      · exact ih h
    · simp [h_digit] at h

theorem Decimal.leftPadZeros_allLessThanTenBool (n : CardinalNatural.Peano) (l : ZeroMath.Sequences.List CardinalNatural.Peano)
  (h : Decimal.allLessThanTenBool l = true) : Decimal.allLessThanTenBool (Decimal.leftPadZeros n l) = true := by
  induction n with
  | zero =>
    unfold Decimal.leftPadZeros
    exact h
  | succ n ih =>
    unfold Decimal.leftPadZeros
    change (if _root_.Nat.blt CardinalNatural.Peano.zero CardinalNatural.Peano.ten then Decimal.allLessThanTenBool (Decimal.leftPadZeros n l) else false) = true
    have h_zero : _root_.Nat.blt CardinalNatural.Peano.zero CardinalNatural.Peano.ten = true := by
      apply Nat.blt_eq.mpr
      unfold CardinalNatural.Peano.zero CardinalNatural.Peano.ten
      exact Nat.zero_lt_succ 9
    rw [h_zero]
    exact ih

theorem Decimal.addAlignedLists_allLessThanTenBool (a b : ZeroMath.Sequences.List CardinalNatural.Peano)
  (ha : Decimal.allLessThanTenBool a = true) (hb : Decimal.allLessThanTenBool b = true) :
  Decimal.allLessThanTenBool (Decimal.addAlignedLists a b).1 = true := by
  induction a generalizing b with
  | nil =>
    induction b with
    | nil =>
      unfold Decimal.addAlignedLists
      unfold Decimal.allLessThanTenBool
      rfl
    | cons b bs ih =>
      unfold Decimal.addAlignedLists
      unfold Decimal.allLessThanTenBool at hb
      by_cases hb_digit : _root_.Nat.blt b CardinalNatural.Peano.ten = true
      · simp [hb_digit] at hb
        have h_tail : Decimal.allLessThanTenBool (Decimal.addAlignedLists _root_.List.nil bs).1 = true := by
          exact ih hb
        generalize h_sum : Decimal.addAlignedLists _root_.List.nil bs = sum
        rw [h_sum] at h_tail
        cases sum with
        | mk tail carry =>
          dsimp only at h_tail ⊢
          change (if _root_.Nat.blt (Decimal.columnarAddDigit CardinalNatural.Peano.zero b carry).1 CardinalNatural.Peano.ten then Decimal.allLessThanTenBool tail else false) = true
          have h_digit := Decimal.columnarAddDigit_allLessThanTenBool CardinalNatural.Peano.zero b carry (by
            apply Nat.blt_eq.mpr
            unfold CardinalNatural.Peano.zero CardinalNatural.Peano.ten
            exact Nat.zero_lt_succ 9) hb_digit
          rw [h_digit]
          exact h_tail
      · simp [hb_digit] at hb
  | cons a as ih =>
    cases b with
    | nil =>
      unfold Decimal.addAlignedLists
      unfold Decimal.allLessThanTenBool at ha
      by_cases ha_digit : _root_.Nat.blt a CardinalNatural.Peano.ten = true
      · simp [ha_digit] at ha
        have h_tail : Decimal.allLessThanTenBool (Decimal.addAlignedLists as _root_.List.nil).1 = true := by
          apply ih
          · exact ha
          · unfold Decimal.allLessThanTenBool
            rfl
        generalize h_sum : Decimal.addAlignedLists as _root_.List.nil = sum
        rw [h_sum] at h_tail
        cases sum with
        | mk tail carry =>
          dsimp only at h_tail ⊢
          change (if _root_.Nat.blt (Decimal.columnarAddDigit a CardinalNatural.Peano.zero carry).1 CardinalNatural.Peano.ten then Decimal.allLessThanTenBool tail else false) = true
          have h_digit := Decimal.columnarAddDigit_allLessThanTenBool a CardinalNatural.Peano.zero carry ha_digit (by
            apply Nat.blt_eq.mpr
            unfold CardinalNatural.Peano.zero CardinalNatural.Peano.ten
            exact Nat.zero_lt_succ 9)
          rw [h_digit]
          exact h_tail
      · simp [ha_digit] at ha
    | cons b bs =>
      unfold Decimal.addAlignedLists
      unfold Decimal.allLessThanTenBool at ha hb
      by_cases ha_digit : _root_.Nat.blt a CardinalNatural.Peano.ten = true
      · by_cases hb_digit : _root_.Nat.blt b CardinalNatural.Peano.ten = true
        · simp [ha_digit, hb_digit] at ha hb
          have h_tail : Decimal.allLessThanTenBool (Decimal.addAlignedLists as bs).1 = true := by
            exact ih bs ha hb
          generalize h_sum : Decimal.addAlignedLists as bs = sum
          rw [h_sum] at h_tail
          cases sum with
          | mk tail carry =>
            dsimp only at h_tail ⊢
            change (if _root_.Nat.blt (Decimal.columnarAddDigit a b carry).1 CardinalNatural.Peano.ten then Decimal.allLessThanTenBool tail else false) = true
            have h_digit := Decimal.columnarAddDigit_allLessThanTenBool a b carry ha_digit hb_digit
            rw [h_digit]
            exact h_tail
        · simp [hb_digit] at hb
      · simp [ha_digit] at ha

theorem Decimal.alignAndAddLists_allLessThanTenBool (a b : ZeroMath.Sequences.List CardinalNatural.Peano)
  (ha : Decimal.allLessThanTenBool a = true) (hb : Decimal.allLessThanTenBool b = true) :
  Decimal.allLessThanTenBool (Decimal.alignAndAddLists a b).1 = true := by
  unfold Decimal.alignAndAddLists
  by_cases h : _root_.Nat.blt (Decimal.lengthList a) (Decimal.lengthList b) = true
  · simp [h]
    exact Decimal.addAlignedLists_allLessThanTenBool (Decimal.leftPadZeros (_root_.Nat.sub (Decimal.lengthList b) (Decimal.lengthList a)) a) b
      (Decimal.leftPadZeros_allLessThanTenBool (_root_.Nat.sub (Decimal.lengthList b) (Decimal.lengthList a)) a ha) hb
  · simp [h]
    exact Decimal.addAlignedLists_allLessThanTenBool a (Decimal.leftPadZeros (_root_.Nat.sub (Decimal.lengthList a) (Decimal.lengthList b)) b)
      ha (Decimal.leftPadZeros_allLessThanTenBool (_root_.Nat.sub (Decimal.lengthList a) (Decimal.lengthList b)) b hb)

theorem Decimal.finishColumnarSum_allLessThanTenBool (sum : ZeroMath.Sequences.List CardinalNatural.Peano × Bool)
  (h : Decimal.allLessThanTenBool sum.1 = true) : Decimal.allLessThanTenBool (Decimal.finishColumnarSum sum) = true := by
  unfold Decimal.finishColumnarSum
  cases sum with
  | mk digits carry =>
    dsimp only at h ⊢
    cases carry with
    | false => exact h
    | true =>
      change (if _root_.Nat.blt (CardinalNatural.Peano.successor CardinalNatural.Peano.zero) CardinalNatural.Peano.ten then Decimal.allLessThanTenBool digits else false) = true
      have h_one : _root_.Nat.blt (CardinalNatural.Peano.successor CardinalNatural.Peano.zero) CardinalNatural.Peano.ten = true := by
        apply Nat.blt_eq.mpr
        unfold CardinalNatural.Peano.successor CardinalNatural.Peano.zero CardinalNatural.Peano.ten
        exact Nat.succ_lt_succ (Nat.zero_lt_succ 8)
      rw [h_one]
      exact h

theorem Decimal.allLessThanTenBool_complete (digits : ZeroMath.Sequences.List CardinalNatural.Peano)
  (h : CardinalNatural.Peano.AllLessThanTen digits) : Decimal.allLessThanTenBool digits = true := by
  induction digits with
  | nil =>
    unfold Decimal.allLessThanTenBool
    rfl
  | cons digit rest ih =>
    unfold CardinalNatural.Peano.AllLessThanTen at h
    change (if _root_.Nat.blt digit CardinalNatural.Peano.ten then Decimal.allLessThanTenBool rest else false) = true
    have h_digit : _root_.Nat.blt digit CardinalNatural.Peano.ten = true := by
      apply Nat.blt_eq.mpr
      exact Decimal.natLt_of_cardinalLt h.left
    rw [h_digit]
    exact ih h.right

theorem Decimal.add_digits_allLessThanTenBool (a b : Decimal) :
  Decimal.allLessThanTenBool (Decimal.finishColumnarSum (Decimal.alignAndAddLists a.val b.val)) = true := by
  apply Decimal.finishColumnarSum_allLessThanTenBool
  apply Decimal.alignAndAddLists_allLessThanTenBool
  · exact Decimal.allLessThanTenBool_complete a.val a.property.left
  · exact Decimal.allLessThanTenBool_complete b.val b.property.left

def Decimal.hasNonZeroBool : ZeroMath.Sequences.List CardinalNatural.Peano → Bool
  | _root_.List.nil => false
  | _root_.List.cons digit rest =>
    if digit = CardinalNatural.Peano.zero then
      Decimal.hasNonZeroBool rest
    else
      true

theorem Decimal.hasNonZeroBool_sound (digits : ZeroMath.Sequences.List CardinalNatural.Peano)
  (h : Decimal.hasNonZeroBool digits = true) : CardinalNatural.Peano.HasNonZero digits := by
  induction digits with
  | nil =>
    unfold Decimal.hasNonZeroBool at h
    contradiction
  | cons digit rest ih =>
    unfold Decimal.hasNonZeroBool at h
    by_cases h_zero : digit = CardinalNatural.Peano.zero
    · simp [h_zero] at h
      unfold CardinalNatural.Peano.HasNonZero
      right
      exact ih h
    · simp [h_zero] at h
      unfold CardinalNatural.Peano.HasNonZero
      left
      exact h_zero

theorem Decimal.columnarAddDigit_nonZero_or_carry (a b : CardinalNatural.Peano) (carry : Bool)
  (h : a ≠ CardinalNatural.Peano.zero ∨ b ≠ CardinalNatural.Peano.zero ∨ carry = true) :
  (Decimal.columnarAddDigit a b carry).1 ≠ CardinalNatural.Peano.zero ∨ (Decimal.columnarAddDigit a b carry).2 = true := by
  unfold Decimal.columnarAddDigit
  cases carry <;> simp at h ⊢ <;> split
  · left
    intro hc
    change _root_.Nat.add (_root_.Nat.add a b) CardinalNatural.Peano.zero = CardinalNatural.Peano.zero at hc
    have h_ab_zero : _root_.Nat.add a b = CardinalNatural.Peano.zero := Nat.eq_zero_of_add_eq_zero_right hc
    have ha_zero : a = CardinalNatural.Peano.zero := Nat.eq_zero_of_add_eq_zero_right h_ab_zero
    have hb_zero : b = CardinalNatural.Peano.zero := Nat.eq_zero_of_add_eq_zero_left h_ab_zero
    cases h with
    | inl ha => exact ha ha_zero
    | inr hb => exact hb hb_zero
  · right
    rfl
  · left
    intro hc
    change _root_.Nat.add (_root_.Nat.add a b) (CardinalNatural.Peano.successor CardinalNatural.Peano.zero) = CardinalNatural.Peano.zero at hc
    have h_one_zero : CardinalNatural.Peano.successor CardinalNatural.Peano.zero = CardinalNatural.Peano.zero := Nat.eq_zero_of_add_eq_zero_left hc
    cases h_one_zero
  · right
    rfl

theorem Decimal.leftPadZeros_hasNonZero (n : CardinalNatural.Peano) (l : ZeroMath.Sequences.List CardinalNatural.Peano)
  (h : CardinalNatural.Peano.HasNonZero l) : CardinalNatural.Peano.HasNonZero (Decimal.leftPadZeros n l) := by
  induction n with
  | zero =>
    unfold Decimal.leftPadZeros
    exact h
  | succ n ih =>
    unfold Decimal.leftPadZeros
    unfold CardinalNatural.Peano.HasNonZero
    right
    exact ih

theorem Decimal.finishColumnarSum_hasNonZero (sum : ZeroMath.Sequences.List CardinalNatural.Peano × Bool)
  (h : CardinalNatural.Peano.HasNonZero sum.1 ∨ sum.2 = true) :
  CardinalNatural.Peano.HasNonZero (Decimal.finishColumnarSum sum) := by
  unfold Decimal.finishColumnarSum
  cases sum with
  | mk digits carry =>
    dsimp only at h ⊢
    cases carry with
    | false =>
      cases h with
      | inl h_digits => exact h_digits
      | inr h_carry => contradiction
    | true =>
      unfold CardinalNatural.Peano.HasNonZero
      left
      exact CardinalNatural.Peano.succ_ne_zero CardinalNatural.Peano.zero

theorem Decimal.addAlignedLists_hasNonZero_or_carry (a b : ZeroMath.Sequences.List CardinalNatural.Peano)
  (h : CardinalNatural.Peano.HasNonZero a ∨ CardinalNatural.Peano.HasNonZero b) :
  CardinalNatural.Peano.HasNonZero (Decimal.addAlignedLists a b).1 ∨ (Decimal.addAlignedLists a b).2 = true := by
  induction a generalizing b with
  | nil =>
    cases h with
    | inl h_nil => cases h_nil
    | inr h_b =>
      induction b with
      | nil => cases h_b
      | cons b bs ih =>
        unfold Decimal.addAlignedLists
        generalize h_sum : Decimal.addAlignedLists _root_.List.nil bs = sum
        cases sum with
        | mk tail carry =>
          dsimp only
          unfold CardinalNatural.Peano.HasNonZero at h_b
          cases h_b with
          | inl hb_head =>
            have h_digit := Decimal.columnarAddDigit_nonZero_or_carry CardinalNatural.Peano.zero b carry (Or.inr (Or.inl hb_head))
            cases h_digit with
            | inl h_digit_nz =>
              left
              unfold CardinalNatural.Peano.HasNonZero
              left
              exact h_digit_nz
            | inr h_carry =>
              right
              exact h_carry
          | inr hb_tail =>
            have h_tail := ih hb_tail
            rw [h_sum] at h_tail
            dsimp only at h_tail
            cases h_tail with
            | inl h_tail_nz =>
              left
              unfold CardinalNatural.Peano.HasNonZero
              right
              exact h_tail_nz
            | inr h_tail_carry =>
              have h_digit := Decimal.columnarAddDigit_nonZero_or_carry CardinalNatural.Peano.zero b carry (Or.inr (Or.inr h_tail_carry))
              cases h_digit with
              | inl h_digit_nz =>
                left
                unfold CardinalNatural.Peano.HasNonZero
                left
                exact h_digit_nz
              | inr h_carry =>
                right
                exact h_carry
  | cons a as ih =>
    cases b with
    | nil =>
      unfold Decimal.addAlignedLists
      generalize h_sum : Decimal.addAlignedLists as _root_.List.nil = sum
      cases sum with
      | mk tail carry =>
        dsimp only
        have h_a : CardinalNatural.Peano.HasNonZero (a :: as) := by
          cases h with
          | inl h_a => exact h_a
          | inr h_nil => cases h_nil
        unfold CardinalNatural.Peano.HasNonZero at h_a
        cases h_a with
        | inl ha_head =>
          have h_digit := Decimal.columnarAddDigit_nonZero_or_carry a CardinalNatural.Peano.zero carry (Or.inl ha_head)
          cases h_digit with
          | inl h_digit_nz =>
            left
            unfold CardinalNatural.Peano.HasNonZero
            left
            exact h_digit_nz
          | inr h_carry =>
            right
            exact h_carry
        | inr ha_tail =>
          have h_tail := ih _root_.List.nil (Or.inl ha_tail : CardinalNatural.Peano.HasNonZero as ∨ CardinalNatural.Peano.HasNonZero _root_.List.nil)
          rw [h_sum] at h_tail
          dsimp only at h_tail
          cases h_tail with
          | inl h_tail_nz =>
            left
            unfold CardinalNatural.Peano.HasNonZero
            right
            exact h_tail_nz
          | inr h_tail_carry =>
            have h_digit := Decimal.columnarAddDigit_nonZero_or_carry a CardinalNatural.Peano.zero carry (Or.inr (Or.inr h_tail_carry))
            cases h_digit with
            | inl h_digit_nz =>
              left
              unfold CardinalNatural.Peano.HasNonZero
              left
              exact h_digit_nz
            | inr h_carry =>
              right
              exact h_carry
    | cons b bs =>
      unfold Decimal.addAlignedLists
      generalize h_sum : Decimal.addAlignedLists as bs = sum
      cases sum with
      | mk tail carry =>
        dsimp only
        have h_current_or_tail : a ≠ CardinalNatural.Peano.zero ∨ b ≠ CardinalNatural.Peano.zero ∨ CardinalNatural.Peano.HasNonZero as ∨ CardinalNatural.Peano.HasNonZero bs := by
          cases h with
          | inl h_a =>
            unfold CardinalNatural.Peano.HasNonZero at h_a
            cases h_a with
            | inl ha => exact Or.inl ha
            | inr has => exact Or.inr (Or.inr (Or.inl has))
          | inr h_b =>
            unfold CardinalNatural.Peano.HasNonZero at h_b
            cases h_b with
            | inl hb => exact Or.inr (Or.inl hb)
            | inr hbs => exact Or.inr (Or.inr (Or.inr hbs))
        cases h_current_or_tail with
        | inl ha_head =>
          have h_digit := Decimal.columnarAddDigit_nonZero_or_carry a b carry (Or.inl ha_head)
          cases h_digit with
          | inl h_digit_nz =>
            left
            unfold CardinalNatural.Peano.HasNonZero
            left
            exact h_digit_nz
          | inr h_carry =>
            right
            exact h_carry
        | inr rest =>
          cases rest with
          | inl hb_head =>
            have h_digit := Decimal.columnarAddDigit_nonZero_or_carry a b carry (Or.inr (Or.inl hb_head))
            cases h_digit with
            | inl h_digit_nz =>
              left
              unfold CardinalNatural.Peano.HasNonZero
              left
              exact h_digit_nz
            | inr h_carry =>
              right
              exact h_carry
          | inr tail_cases =>
            have h_tail : CardinalNatural.Peano.HasNonZero tail ∨ carry = true := by
              cases tail_cases with
              | inl has =>
                have h_rec := ih bs (Or.inl has)
                rw [h_sum] at h_rec
                exact h_rec
              | inr hbs =>
                have h_rec := ih bs (Or.inr hbs)
                rw [h_sum] at h_rec
                exact h_rec
            cases h_tail with
            | inl h_tail_nz =>
              left
              unfold CardinalNatural.Peano.HasNonZero
              right
              exact h_tail_nz
            | inr h_tail_carry =>
              have h_digit := Decimal.columnarAddDigit_nonZero_or_carry a b carry (Or.inr (Or.inr h_tail_carry))
              cases h_digit with
              | inl h_digit_nz =>
                left
                unfold CardinalNatural.Peano.HasNonZero
                left
                exact h_digit_nz
              | inr h_carry =>
                right
                exact h_carry

theorem Decimal.alignAndAddLists_hasNonZero_or_carry (a b : ZeroMath.Sequences.List CardinalNatural.Peano)
  (ha : CardinalNatural.Peano.HasNonZero a) :
  CardinalNatural.Peano.HasNonZero (Decimal.alignAndAddLists a b).1 ∨ (Decimal.alignAndAddLists a b).2 = true := by
  unfold Decimal.alignAndAddLists
  by_cases h : _root_.Nat.blt (Decimal.lengthList a) (Decimal.lengthList b) = true
  · simp [h]
    exact Decimal.addAlignedLists_hasNonZero_or_carry (Decimal.leftPadZeros (_root_.Nat.sub (Decimal.lengthList b) (Decimal.lengthList a)) a) b
      (Or.inl (Decimal.leftPadZeros_hasNonZero (_root_.Nat.sub (Decimal.lengthList b) (Decimal.lengthList a)) a ha))
  · simp [h]
    exact Decimal.addAlignedLists_hasNonZero_or_carry a (Decimal.leftPadZeros (_root_.Nat.sub (Decimal.lengthList a) (Decimal.lengthList b)) b)
      (Or.inl ha)



theorem Decimal.toCardinalHelper_eq (l : ZeroMath.Sequences.List CardinalNatural.Peano) (acc : CardinalNatural.Peano) :
  Decimal.toCardinalHelper l acc = _root_.Nat.add (_root_.Nat.mul acc (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList l))) (Decimal.toCardinalList l) := by
  induction l generalizing acc with
  | nil =>
    simp [Decimal.toCardinalHelper, Decimal.toCardinalList, Decimal.lengthList, CardinalNatural.Peano.ten, CardinalNatural.Peano.zero, HMul.hMul, HAdd.hAdd]
    change acc = _root_.Nat.add (_root_.Nat.mul acc (Nat.succ Nat.zero)) Nat.zero
    rw [show _root_.Nat.mul acc (Nat.succ Nat.zero) = acc from Nat.mul_one acc]
    rw [show _root_.Nat.add acc Nat.zero = acc from Nat.add_zero acc]
  | cons d ds ih =>
    change Decimal.toCardinalHelper ds (acc * CardinalNatural.Peano.ten + d) = _root_.Nat.add (_root_.Nat.mul acc (_root_.Nat.pow CardinalNatural.Peano.ten (CardinalNatural.Peano.successor (Decimal.lengthList ds)))) (Decimal.toCardinalHelper ds (CardinalNatural.Peano.zero * CardinalNatural.Peano.ten + d))
    rw [CardinalNatural.Peano.zero_multiply]
    rw [CardinalNatural.Peano.zero_add]
    rw [ih (acc * CardinalNatural.Peano.ten + d)]
    rw [ih d]
    rw [show acc * CardinalNatural.Peano.ten + d = _root_.Nat.add (_root_.Nat.mul acc CardinalNatural.Peano.ten) d by
      rw [show acc * CardinalNatural.Peano.ten = _root_.Nat.mul acc CardinalNatural.Peano.ten from CardinalNatural.Peano.multiply_eq_nat_mul acc CardinalNatural.Peano.ten]
      exact CardinalNatural.Peano.add_eq_nat_add (_root_.Nat.mul acc CardinalNatural.Peano.ten) d]
    unfold CardinalNatural.Peano.ten CardinalNatural.Peano.successor
    rw [show _root_.Nat.pow (10 : Nat) (Nat.succ (Decimal.lengthList ds)) = _root_.Nat.mul (_root_.Nat.pow (10 : Nat) (Decimal.lengthList ds)) (10 : Nat) from Nat.pow_succ 10 (Decimal.lengthList ds)]
    rw [show _root_.Nat.mul (_root_.Nat.add (_root_.Nat.mul acc 10) d) (_root_.Nat.pow (10 : Nat) (Decimal.lengthList ds)) = _root_.Nat.add (_root_.Nat.mul (_root_.Nat.mul acc 10) (_root_.Nat.pow (10 : Nat) (Decimal.lengthList ds))) (_root_.Nat.mul d (_root_.Nat.pow (10 : Nat) (Decimal.lengthList ds))) from Nat.add_mul (_root_.Nat.mul acc 10) d (_root_.Nat.pow (10 : Nat) (Decimal.lengthList ds))]
    rw [show _root_.Nat.mul (_root_.Nat.mul acc 10) (_root_.Nat.pow (10 : Nat) (Decimal.lengthList ds)) = _root_.Nat.mul acc (_root_.Nat.mul 10 (_root_.Nat.pow (10 : Nat) (Decimal.lengthList ds))) from Nat.mul_assoc acc 10 (_root_.Nat.pow (10 : Nat) (Decimal.lengthList ds))]
    rw [show _root_.Nat.mul 10 (_root_.Nat.pow (10 : Nat) (Decimal.lengthList ds)) = _root_.Nat.mul (_root_.Nat.pow (10 : Nat) (Decimal.lengthList ds)) 10 from Nat.mul_comm 10 (_root_.Nat.pow (10 : Nat) (Decimal.lengthList ds))]
    exact (Nat.add_assoc (_root_.Nat.mul acc (_root_.Nat.mul (_root_.Nat.pow (10 : Nat) (Decimal.lengthList ds)) 10)) (_root_.Nat.mul d (_root_.Nat.pow (10 : Nat) (Decimal.lengthList ds))) (Decimal.toCardinalList ds))

theorem Decimal.toCardinalList_cons (d : CardinalNatural.Peano) (ds : ZeroMath.Sequences.List CardinalNatural.Peano) :
  Decimal.toCardinalList (d :: ds) = _root_.Nat.add (_root_.Nat.mul d (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList ds))) (Decimal.toCardinalList ds) := by
  change Decimal.toCardinalHelper ds (CardinalNatural.Peano.zero * CardinalNatural.Peano.ten + d) = _root_.Nat.add (_root_.Nat.mul d (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList ds))) (Decimal.toCardinalList ds)
  rw [CardinalNatural.Peano.zero_multiply]
  rw [CardinalNatural.Peano.zero_add]
  exact Decimal.toCardinalHelper_eq ds d

theorem Decimal.columnarAddDigit_value (a b : CardinalNatural.Peano) (carry : Bool) :
  _root_.Nat.add (Decimal.columnarAddDigit a b carry).1 (if (Decimal.columnarAddDigit a b carry).2 then CardinalNatural.Peano.ten else CardinalNatural.Peano.zero) =
    _root_.Nat.add (_root_.Nat.add a b) (if carry then CardinalNatural.Peano.successor CardinalNatural.Peano.zero else CardinalNatural.Peano.zero) := by
  unfold Decimal.columnarAddDigit
  cases carry <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · split
    · rfl
    · next h =>
      dsimp only
      unfold CardinalNatural.Peano.ten CardinalNatural.Peano.zero
      have hge : 10 ≤ _root_.Nat.add (_root_.Nat.add a b) 0 := by
        apply Nat.le_of_not_gt
        intro hlt
        exact h (Nat.blt_eq.mpr hlt)
      rw [show _root_.Nat.add (_root_.Nat.add a b) 0 = _root_.Nat.add a b from Nat.add_zero (_root_.Nat.add a b)] at hge
      simp
      exact Nat.sub_add_cancel hge
  · split
    · rfl
    · next h =>
      dsimp only
      unfold CardinalNatural.Peano.ten CardinalNatural.Peano.zero CardinalNatural.Peano.successor
      have hge : 10 ≤ _root_.Nat.add (_root_.Nat.add a b) 1 := by
        apply Nat.le_of_not_gt
        intro hlt
        exact h (Nat.blt_eq.mpr hlt)
      change 10 ≤ Nat.succ (_root_.Nat.add a b) at hge
      have hge' : 9 ≤ _root_.Nat.add a b := by omega
      simp
      exact Nat.sub_add_cancel hge'


theorem Decimal.columnar_place_combine (digit a b p tail asValue bsValue : Nat) (nextCarry carry : Bool)
  (hdigit : digit + (if nextCarry then 10 else 0) = a + b + (if carry then 1 else 0))
  (htail : tail + (if carry then p else 0) = asValue + bsValue) :
  digit * p + tail + (if nextCarry then p * 10 else 0) = (a * p + asValue) + (b * p + bsValue) := by
  cases nextCarry <;> cases carry <;> simp at hdigit htail ⊢
  all_goals
    have hm := congrArg (fun n => n * p) hdigit
    simp only at hm
    repeat rw [Nat.add_mul] at hm
    omega

theorem Decimal.addAlignedLists_length (a b : ZeroMath.Sequences.List CardinalNatural.Peano)
  (hlen : Decimal.lengthList a = Decimal.lengthList b) :
  Decimal.lengthList (Decimal.addAlignedLists a b).1 = Decimal.lengthList a := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil =>
      unfold Decimal.addAlignedLists Decimal.lengthList
      rfl
    | cons b bs =>
      unfold Decimal.lengthList at hlen
      cases hlen
  | cons a as ih =>
    cases b with
    | nil =>
      unfold Decimal.lengthList at hlen
      cases hlen
    | cons b bs =>
      have htail : Decimal.lengthList as = Decimal.lengthList bs := by
        unfold Decimal.lengthList at hlen
        exact Nat.succ.inj hlen
      unfold Decimal.addAlignedLists
      generalize hsum : Decimal.addAlignedLists as bs = sum
      cases sum with
      | mk tail carry =>
        dsimp only
        unfold ZeroMath.Sequences.List.firstElement
        unfold Decimal.lengthList
        have ih_app := ih bs htail
        rw [hsum] at ih_app
        dsimp only at ih_app
        rw [ih_app]

theorem Decimal.addAlignedLists_toCardinalList (a b : ZeroMath.Sequences.List CardinalNatural.Peano)
  (hlen : Decimal.lengthList a = Decimal.lengthList b) :
  _root_.Nat.add (Decimal.toCardinalList (Decimal.addAlignedLists a b).1)
      (if (Decimal.addAlignedLists a b).2 then _root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList a) else CardinalNatural.Peano.zero) =
    _root_.Nat.add (Decimal.toCardinalList a) (Decimal.toCardinalList b) := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil =>
      unfold Decimal.addAlignedLists Decimal.toCardinalList Decimal.toCardinalHelper Decimal.lengthList CardinalNatural.Peano.zero
      rfl
    | cons b bs =>
      unfold Decimal.lengthList at hlen
      cases hlen
  | cons a as ih =>
    cases b with
    | nil =>
      unfold Decimal.lengthList at hlen
      cases hlen
    | cons b bs =>
      have htail : Decimal.lengthList as = Decimal.lengthList bs := by
        unfold Decimal.lengthList at hlen
        exact Nat.succ.inj hlen
      unfold Decimal.addAlignedLists
      generalize hsum : Decimal.addAlignedLists as bs = sum
      cases sum with
      | mk tail carry =>
        dsimp only
        have ih_app := ih bs htail
        rw [hsum] at ih_app
        dsimp only at ih_app
        unfold ZeroMath.Sequences.List.firstElement
        rw [Decimal.toCardinalList_cons]
        rw [Decimal.toCardinalList_cons a as]
        rw [Decimal.toCardinalList_cons b bs]
        have hdigit := Decimal.columnarAddDigit_value a b carry
        have htail_len := Decimal.addAlignedLists_length as bs htail
        rw [hsum] at htail_len
        dsimp only at htail_len
        rw [htail_len]
        rw [htail]
        have hpow : _root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList (a :: as)) =
            _root_.Nat.mul (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList as)) CardinalNatural.Peano.ten := by
          change _root_.Nat.pow CardinalNatural.Peano.ten (CardinalNatural.Peano.successor (Decimal.lengthList as)) =
            _root_.Nat.mul (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList as)) CardinalNatural.Peano.ten
          unfold CardinalNatural.Peano.successor
          exact Nat.pow_succ CardinalNatural.Peano.ten (Decimal.lengthList as)
        rw [hpow]
        rw [htail]
        have hdigit_nat :
            _root_.Nat.add (Decimal.columnarAddDigit a b carry).1
                (if (Decimal.columnarAddDigit a b carry).2 then (10 : Nat) else Nat.zero) =
              _root_.Nat.add (_root_.Nat.add a b) (if carry then (1 : Nat) else Nat.zero) := by
          simpa [CardinalNatural.Peano.ten, CardinalNatural.Peano.zero, CardinalNatural.Peano.successor] using hdigit
        have ih_nat :
            _root_.Nat.add (Decimal.toCardinalList tail)
                (if carry then _root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList bs) else Nat.zero) =
              _root_.Nat.add (Decimal.toCardinalList as) (Decimal.toCardinalList bs) := by
          simpa [CardinalNatural.Peano.zero, htail] using ih_app
        exact Decimal.columnar_place_combine
          (Decimal.columnarAddDigit a b carry).1 a b (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList bs))
          (Decimal.toCardinalList tail) (Decimal.toCardinalList as) (Decimal.toCardinalList bs)
          (Decimal.columnarAddDigit a b carry).2 carry hdigit_nat ih_nat



theorem Decimal.leftPadZeros_length (n : CardinalNatural.Peano) (l : ZeroMath.Sequences.List CardinalNatural.Peano) :
  Decimal.lengthList (Decimal.leftPadZeros n l) = _root_.Nat.add n (Decimal.lengthList l) := by
  induction n with
  | zero =>
    unfold Decimal.leftPadZeros
    exact (Nat.zero_add (Decimal.lengthList l)).symm
  | succ n ih =>
    unfold Decimal.leftPadZeros
    unfold ZeroMath.Sequences.List.firstElement
    unfold Decimal.lengthList
    rw [ih]
    unfold CardinalNatural.Peano.successor
    cases l with
    | nil => exact (Nat.succ_add n CardinalNatural.Peano.zero).symm
    | cons head xs => exact (Nat.succ_add n (Nat.succ (Decimal.lengthList xs))).symm


theorem Decimal.leftPadZeros_toCardinalList (n : CardinalNatural.Peano) (l : ZeroMath.Sequences.List CardinalNatural.Peano) :
  Decimal.toCardinalList (Decimal.leftPadZeros n l) = Decimal.toCardinalList l := by
  induction n with
  | zero =>
    unfold Decimal.leftPadZeros
    rfl
  | succ n ih =>
    unfold Decimal.leftPadZeros
    unfold ZeroMath.Sequences.List.firstElement
    rw [Decimal.toCardinalList_cons]
    rw [ih]
    unfold CardinalNatural.Peano.zero
    rw [show _root_.Nat.mul Nat.zero (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList (Decimal.leftPadZeros n l))) = Nat.zero from Nat.zero_mul (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList (Decimal.leftPadZeros n l)))]
    rw [show _root_.Nat.add Nat.zero (Decimal.toCardinalList l) = Decimal.toCardinalList l from Nat.zero_add (Decimal.toCardinalList l)]


theorem Decimal.finishColumnarSum_toCardinalList (sum : ZeroMath.Sequences.List CardinalNatural.Peano × Bool) :
  Decimal.toCardinalList (Decimal.finishColumnarSum sum) =
    _root_.Nat.add (Decimal.toCardinalList sum.1)
      (if sum.2 then _root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList sum.1) else CardinalNatural.Peano.zero) := by
  cases sum with
  | mk digits carry =>
    cases carry with
    | false =>
      unfold Decimal.finishColumnarSum
      dsimp only
      simp
      change Decimal.toCardinalList digits = _root_.Nat.add (Decimal.toCardinalList digits) Nat.zero
      exact (Nat.add_zero (Decimal.toCardinalList digits)).symm
    | true =>
      unfold Decimal.finishColumnarSum
      dsimp only
      simp
      unfold ZeroMath.Sequences.List.firstElement
      rw [Decimal.toCardinalList_cons]
      unfold CardinalNatural.Peano.successor CardinalNatural.Peano.zero
      change _root_.Nat.add (_root_.Nat.mul (Nat.succ Nat.zero) (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList digits))) (Decimal.toCardinalList digits) = _root_.Nat.add (Decimal.toCardinalList digits) (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList digits))
      rw [show _root_.Nat.mul (Nat.succ Nat.zero) (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList digits)) = _root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList digits) from Nat.one_mul (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList digits))]
      exact Nat.add_comm (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList digits)) (Decimal.toCardinalList digits)

theorem Decimal.columnarAddDigit_comm (a b : CardinalNatural.Peano) (carry : Bool) :
  Decimal.columnarAddDigit a b carry = Decimal.columnarAddDigit b a carry := by
  unfold Decimal.columnarAddDigit
  simp [Nat.add_comm a b]

theorem Decimal.addAlignedLists_nil_comm (l : ZeroMath.Sequences.List CardinalNatural.Peano) :
  Decimal.addAlignedLists _root_.List.nil l = Decimal.addAlignedLists l _root_.List.nil := by
  induction l with
  | nil =>
    unfold Decimal.addAlignedLists
    rfl
  | cons d ds ih =>
    unfold Decimal.addAlignedLists
    rw [ih]
    generalize hsum : Decimal.addAlignedLists ds _root_.List.nil = sum
    cases sum with
    | mk tail carry =>
      dsimp only
      rw [Decimal.columnarAddDigit_comm CardinalNatural.Peano.zero d carry]

theorem Decimal.addAlignedLists_comm (a b : ZeroMath.Sequences.List CardinalNatural.Peano) :
  Decimal.addAlignedLists a b = Decimal.addAlignedLists b a := by
  induction a generalizing b with
  | nil =>
    exact Decimal.addAlignedLists_nil_comm b
  | cons a as ih =>
    cases b with
    | nil =>
      exact (Decimal.addAlignedLists_nil_comm (a :: as)).symm
    | cons b bs =>
      unfold Decimal.addAlignedLists
      rw [ih bs]
      generalize hsum : Decimal.addAlignedLists bs as = sum
      cases sum with
      | mk tail carry =>
        dsimp only
        rw [Decimal.columnarAddDigit_comm a b carry]

theorem Decimal.alignAndAddLists_comm (a b : ZeroMath.Sequences.List CardinalNatural.Peano) :
  Decimal.alignAndAddLists a b = Decimal.alignAndAddLists b a := by
  unfold Decimal.alignAndAddLists
  by_cases h_ab : _root_.Nat.blt (Decimal.lengthList a) (Decimal.lengthList b) = true
  · simp [h_ab]
    split
    · next h_ba =>
      have hlt_ab : _root_.Nat.lt (Decimal.lengthList a) (Decimal.lengthList b) := Nat.blt_eq.mp h_ab
      have hlt_ba : _root_.Nat.lt (Decimal.lengthList b) (Decimal.lengthList a) := h_ba
      exact False.elim ((Nat.lt_asymm hlt_ab) hlt_ba)
    · exact Decimal.addAlignedLists_comm (Decimal.leftPadZeros (_root_.Nat.sub (Decimal.lengthList b) (Decimal.lengthList a)) a) b
  · have h_ab_false : _root_.Nat.blt (Decimal.lengthList a) (Decimal.lengthList b) = false := by
      cases h : _root_.Nat.blt (Decimal.lengthList a) (Decimal.lengthList b) with
      | false => rfl
      | true => exact False.elim (h_ab h)
    simp [h_ab_false]
    split
    · exact Decimal.addAlignedLists_comm a (Decimal.leftPadZeros (_root_.Nat.sub (Decimal.lengthList a) (Decimal.lengthList b)) b)
    · next h_not_ba =>
      have hle_ba : _root_.Nat.le (Decimal.lengthList b) (Decimal.lengthList a) := by
        apply Nat.le_of_not_gt
        intro hlt
        exact h_ab (Nat.blt_eq.mpr hlt)
      have hle_ab : _root_.Nat.le (Decimal.lengthList a) (Decimal.lengthList b) := by
        apply Nat.le_of_not_gt
        intro hlt
        exact h_not_ba hlt
      have hlen : Decimal.lengthList a = Decimal.lengthList b := Nat.le_antisymm hle_ab hle_ba
      rw [hlen]
      simp [Nat.sub_self]
      unfold Decimal.leftPadZeros
      exact Decimal.addAlignedLists_comm a b

theorem Decimal.alignAndAddLists_finish_toCardinalList (a b : ZeroMath.Sequences.List CardinalNatural.Peano) :
  Decimal.toCardinalList (Decimal.finishColumnarSum (Decimal.alignAndAddLists a b)) =
    _root_.Nat.add (Decimal.toCardinalList a) (Decimal.toCardinalList b) := by
  unfold Decimal.alignAndAddLists
  by_cases h : _root_.Nat.blt (Decimal.lengthList a) (Decimal.lengthList b) = true
  · simp [h]
    rw [Decimal.finishColumnarSum_toCardinalList]
    change _root_.Nat.add (Decimal.toCardinalList (Decimal.addAlignedLists (Decimal.leftPadZeros (_root_.Nat.sub (Decimal.lengthList b) (Decimal.lengthList a)) a) b).1)
      (if (Decimal.addAlignedLists (Decimal.leftPadZeros (_root_.Nat.sub (Decimal.lengthList b) (Decimal.lengthList a)) a) b).2 then
        _root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList (Decimal.addAlignedLists (Decimal.leftPadZeros (_root_.Nat.sub (Decimal.lengthList b) (Decimal.lengthList a)) a) b).1)
       else CardinalNatural.Peano.zero) = _root_.Nat.add (Decimal.toCardinalList a) (Decimal.toCardinalList b)
    have hlen_pad : Decimal.lengthList (Decimal.leftPadZeros (_root_.Nat.sub (Decimal.lengthList b) (Decimal.lengthList a)) a) = Decimal.lengthList b := by
      rw [Decimal.leftPadZeros_length]
      have hlt : _root_.Nat.lt (Decimal.lengthList a) (Decimal.lengthList b) := Nat.blt_eq.mp h
      exact Nat.sub_add_cancel (Nat.le_of_lt hlt)
    have hsum := Decimal.addAlignedLists_toCardinalList (Decimal.leftPadZeros (_root_.Nat.sub (Decimal.lengthList b) (Decimal.lengthList a)) a) b hlen_pad
    have hlen_res := Decimal.addAlignedLists_length (Decimal.leftPadZeros (_root_.Nat.sub (Decimal.lengthList b) (Decimal.lengthList a)) a) b hlen_pad
    rw [hlen_res]
    rw [hsum]
    rw [Decimal.leftPadZeros_toCardinalList]
  · simp [h]
    rw [Decimal.finishColumnarSum_toCardinalList]
    change _root_.Nat.add (Decimal.toCardinalList (Decimal.addAlignedLists a (Decimal.leftPadZeros (_root_.Nat.sub (Decimal.lengthList a) (Decimal.lengthList b)) b)).1)
      (if (Decimal.addAlignedLists a (Decimal.leftPadZeros (_root_.Nat.sub (Decimal.lengthList a) (Decimal.lengthList b)) b)).2 then
        _root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList (Decimal.addAlignedLists a (Decimal.leftPadZeros (_root_.Nat.sub (Decimal.lengthList a) (Decimal.lengthList b)) b)).1)
       else CardinalNatural.Peano.zero) = _root_.Nat.add (Decimal.toCardinalList a) (Decimal.toCardinalList b)
    have hlen_pad : Decimal.lengthList (Decimal.leftPadZeros (_root_.Nat.sub (Decimal.lengthList a) (Decimal.lengthList b)) b) = Decimal.lengthList a := by
      rw [Decimal.leftPadZeros_length]
      have hnlt : ¬ _root_.Nat.lt (Decimal.lengthList a) (Decimal.lengthList b) := by
        intro hlt
        exact h (Nat.blt_eq.mpr hlt)
      exact Nat.sub_add_cancel (Nat.le_of_not_gt hnlt)
    have hsum := Decimal.addAlignedLists_toCardinalList a (Decimal.leftPadZeros (_root_.Nat.sub (Decimal.lengthList a) (Decimal.lengthList b)) b) hlen_pad.symm
    have hlen_res := Decimal.addAlignedLists_length a (Decimal.leftPadZeros (_root_.Nat.sub (Decimal.lengthList a) (Decimal.lengthList b)) b) hlen_pad.symm
    rw [hlen_res]
    rw [hsum]
    rw [Decimal.leftPadZeros_toCardinalList]


def Decimal.add (a b : Decimal) : Decimal :=
  let sum := Decimal.alignAndAddLists a.val b.val
  let digits := Decimal.finishColumnarSum sum
  have h_digits : Decimal.allLessThanTenBool digits = true := Decimal.add_digits_allLessThanTenBool a b
  ⟨digits, ⟨Decimal.allLessThanTenBool_sound digits h_digits,
    Decimal.finishColumnarSum_hasNonZero sum (Decimal.alignAndAddLists_hasNonZero_or_carry a.val b.val a.property.right)⟩⟩

instance Decimal.instAdd : Add Decimal where
  add := Decimal.add

theorem Decimal.add_syntax_eq_add (a b : Decimal) : a + b = Decimal.add a b := by
  rfl

def Decimal.fromPeano : OrdinalNatural.Peano → Decimal
  | OrdinalNatural.Peano.one => Decimal.one
  | OrdinalNatural.Peano.successor p => Decimal.successor (Decimal.fromPeano p)

theorem Decimal.toPeano_fromPeano_one :
  Decimal.toPeano (Decimal.fromPeano OrdinalNatural.Peano.one) = OrdinalNatural.Peano.one := by
  rfl

theorem Decimal.toPeano_successor (d : Decimal)
  (h_succ : ∀ d, Decimal.toCardinalList (Decimal.successor d).val = Decimal.toCardinalList d.val + CardinalNatural.Peano.successor CardinalNatural.Peano.zero) :
  Decimal.toPeano (Decimal.successor d) = OrdinalNatural.Peano.successor (Decimal.toPeano d) := by
  unfold Decimal.toPeano
  unfold Decimal.successor
  dsimp
  have h2 : Decimal.toCardinalList (Decimal.successorHelper d.val) = Decimal.toCardinalList d.val + CardinalNatural.Peano.successor CardinalNatural.Peano.zero := h_succ d
  have h_ne : Decimal.toCardinalList (Decimal.successorHelper d.val) ≠ CardinalNatural.Peano.zero := by
    rw [h2]
    intro hc
    cases hc
  have h3 : ∀ (n : CardinalNatural.Peano) (hn1 : n ≠ CardinalNatural.Peano.zero) (hn2 : n + CardinalNatural.Peano.successor CardinalNatural.Peano.zero ≠ CardinalNatural.Peano.zero), OrdinalNatural.Peano.fromNat (n + CardinalNatural.Peano.successor CardinalNatural.Peano.zero) hn2 = OrdinalNatural.Peano.successor (OrdinalNatural.Peano.fromNat n hn1) := by
    intro n hn1 hn2
    cases n with
    | zero => contradiction
    | succ n => rfl
  have hn1 : Decimal.toCardinalList d.val ≠ CardinalNatural.Peano.zero := by
    have h : CardinalNatural.Peano.zero ≠ CardinalNatural.Peano.zero ∨ CardinalNatural.Peano.HasNonZero d.val := Or.inr d.property.right
    exact Decimal.toCardinalHelper_ne_zero d.val CardinalNatural.Peano.zero h
  have hn2 : Decimal.toCardinalList d.val + CardinalNatural.Peano.successor CardinalNatural.Peano.zero ≠ CardinalNatural.Peano.zero := by
    intro hc
    cases hc
  have h4 := h3 (Decimal.toCardinalList d.val) hn1 hn2
  have h5 : OrdinalNatural.Peano.fromNat (Decimal.toCardinalList (Decimal.successorHelper d.val)) h_ne = OrdinalNatural.Peano.fromNat (Decimal.toCardinalList d.val + CardinalNatural.Peano.successor CardinalNatural.Peano.zero) hn2 := by
    apply OrdinalNatural.Peano.fromNat_toNat_helper
    have h_toNat2 : (OrdinalNatural.Peano.fromNat (Decimal.toCardinalList d.val + CardinalNatural.Peano.successor CardinalNatural.Peano.zero) hn2).toNat = Decimal.toCardinalList d.val + CardinalNatural.Peano.successor CardinalNatural.Peano.zero := OrdinalNatural.Peano.toNat_fromNat _ _
    rw [h_toNat2]
    exact h2.symm
  exact Eq.trans h5 h4

theorem Decimal.toPeano_fromPeano_with_successor_cardinal (x : OrdinalNatural.Peano)
  (h_succ : ∀ d, Decimal.toCardinalList (Decimal.successor d).val = Decimal.toCardinalList d.val + CardinalNatural.Peano.successor CardinalNatural.Peano.zero) :
  Decimal.toPeano (Decimal.fromPeano x) = x := by
  induction x with
  | one => exact Decimal.toPeano_fromPeano_one
  | successor p ih =>
    have h1 : Decimal.fromPeano (OrdinalNatural.Peano.successor p) = Decimal.successor (Decimal.fromPeano p) := rfl
    have h2 : Decimal.toPeano (Decimal.successor (Decimal.fromPeano p)) = OrdinalNatural.Peano.successor (Decimal.toPeano (Decimal.fromPeano p)) := Decimal.toPeano_successor (Decimal.fromPeano p) h_succ
    rw [h1, h2, ih]

theorem Decimal.toPeano_fromPeano (x : OrdinalNatural.Peano) :
  Decimal.toPeano (Decimal.fromPeano x) = x := by
  exact Decimal.toPeano_fromPeano_with_successor_cardinal x Decimal.successor_toCardinalList

theorem Decimal.toPeano_toNat (d : Decimal) :
  d.toPeano.toNat = Decimal.toCardinalList d.val := by
  unfold Decimal.toPeano
  exact OrdinalNatural.Peano.toNat_fromNat _ _

theorem Decimal.add_toCardinalList (x y : Decimal) :
  Decimal.toCardinalList (x + y).val =
    _root_.Nat.add (Decimal.toCardinalList x.val) (Decimal.toCardinalList y.val) := by
  rw [Decimal.add_syntax_eq_add]
  unfold Decimal.add
  dsimp only
  exact Decimal.alignAndAddLists_finish_toCardinalList x.val y.val

theorem Decimal.add_comm_eq (a b : Decimal) :
  a + b = b + a := by
  apply Subtype.ext
  rw [Decimal.add_syntax_eq_add, Decimal.add_syntax_eq_add]
  unfold Decimal.add
  dsimp only
  exact congrArg Decimal.finishColumnarSum (Decimal.alignAndAddLists_comm a.val b.val)

theorem Decimal.add_comm (a b : Decimal) :
  a + b ≈ b + a := by
  have h := Decimal.add_comm_eq a b
  rw [h]
  exact Setoid.refl (b + a)


theorem Decimal.fromPeano_toCardinalList (p : OrdinalNatural.Peano) :
  Decimal.toCardinalList (Decimal.fromPeano p).val = p.toNat := by
  induction p with
  | one => rfl
  | successor p ih =>
    unfold Decimal.fromPeano
    rw [Decimal.successor_toCardinalList]
    rw [ih]
    rfl

theorem Decimal.toCardinalList_lt_pow_length (l : ZeroMath.Sequences.List CardinalNatural.Peano)
  (h : CardinalNatural.Peano.AllLessThanTen l) :
  _root_.Nat.lt (Decimal.toCardinalList l) (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList l)) := by
  induction l with
  | nil =>
    unfold Decimal.toCardinalList Decimal.toCardinalHelper Decimal.lengthList CardinalNatural.Peano.ten CardinalNatural.Peano.zero
    exact Nat.zero_lt_succ 0
  | cons d ds ih =>
    unfold CardinalNatural.Peano.AllLessThanTen at h
    rw [Decimal.toCardinalList_cons]
    rw [show Decimal.lengthList (d :: ds) = Nat.succ (Decimal.lengthList ds) from rfl]
    rw [show _root_.Nat.pow CardinalNatural.Peano.ten (Nat.succ (Decimal.lengthList ds)) =
      _root_.Nat.mul (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList ds)) CardinalNatural.Peano.ten from
      _root_.Nat.pow_succ CardinalNatural.Peano.ten (Decimal.lengthList ds)]
    have h_tail := ih h.right
    have h_pow_pos : _root_.Nat.lt 0 (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList ds)) := by
      apply Nat.pow_pos
      unfold CardinalNatural.Peano.ten
      exact Nat.zero_lt_succ 9
    have h_digit : _root_.Nat.lt d CardinalNatural.Peano.ten := Decimal.natLt_of_cardinalLt h.left
    unfold CardinalNatural.Peano.ten at h_digit ⊢
    have h_step : _root_.Nat.lt
        (_root_.Nat.add (_root_.Nat.mul d (_root_.Nat.pow (10 : Nat) (Decimal.lengthList ds))) (Decimal.toCardinalList ds))
        (_root_.Nat.mul (Nat.succ d) (_root_.Nat.pow (10 : Nat) (Decimal.lengthList ds))) := by
      let p := _root_.Nat.pow (10 : Nat) (Decimal.lengthList ds)
      have hsucc : _root_.Nat.mul (Nat.succ d) p = _root_.Nat.add (_root_.Nat.mul d p) p := _root_.Nat.succ_mul d p
      exact hsucc.symm ▸ Nat.add_lt_add_left h_tail (_root_.Nat.mul d p)
    have h_digit_mul : _root_.Nat.le (_root_.Nat.mul (Nat.succ d) (_root_.Nat.pow (10 : Nat) (Decimal.lengthList ds)))
        (_root_.Nat.mul (_root_.Nat.pow (10 : Nat) (Decimal.lengthList ds)) 10) := by
      have h_digit_mul' : _root_.Nat.le (_root_.Nat.mul (Nat.succ d) (_root_.Nat.pow (10 : Nat) (Decimal.lengthList ds)))
          (_root_.Nat.mul 10 (_root_.Nat.pow (10 : Nat) (Decimal.lengthList ds))) := by
        exact Nat.mul_le_mul_right (_root_.Nat.pow (10 : Nat) (Decimal.lengthList ds)) h_digit
      have hcomm : _root_.Nat.mul (10 : Nat) (_root_.Nat.pow (10 : Nat) (Decimal.lengthList ds)) =
          _root_.Nat.mul (_root_.Nat.pow (10 : Nat) (Decimal.lengthList ds)) 10 := _root_.Nat.mul_comm (10 : Nat) (_root_.Nat.pow (10 : Nat) (Decimal.lengthList ds))
      exact hcomm ▸ h_digit_mul'
    exact Nat.lt_of_lt_of_le h_step h_digit_mul

theorem Decimal.pow_pred_length_le_toCardinalList
  (l : ZeroMath.Sequences.List CardinalNatural.Peano)
  (h : match l with
    | _root_.List.nil => False
    | _root_.List.cons digit _ => digit ≠ CardinalNatural.Peano.zero) :
  _root_.Nat.le (_root_.Nat.pow CardinalNatural.Peano.ten (_root_.Nat.pred (Decimal.lengthList l))) (Decimal.toCardinalList l) := by
  cases l with
  | nil => cases h
  | cons d ds =>
    rw [Decimal.toCardinalList_cons]
    rw [show Decimal.lengthList (d :: ds) = Nat.succ (Decimal.lengthList ds) from rfl]
    rw [Nat.pred_succ]
    have hd_pos : _root_.Nat.le 1 d := Nat.succ_le_of_lt (Nat.pos_of_ne_zero h)
    have h_mul : _root_.Nat.le (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList ds))
        (_root_.Nat.mul d (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList ds))) := by
      simpa [Nat.one_mul] using Nat.mul_le_mul_right (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList ds)) hd_pos
    have h_add : _root_.Nat.le (_root_.Nat.mul d (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList ds)))
        (_root_.Nat.add (_root_.Nat.mul d (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList ds))) (Decimal.toCardinalList ds)) := by
      exact Nat.le_add_right _ _
    exact Nat.le_trans h_mul h_add

theorem Decimal.isNormalized_head_ne_zero (d : Decimal) (h : d.isNormalized = true) :
  match d.val with
  | _root_.List.nil => False
  | _root_.List.cons digit _ => digit ≠ CardinalNatural.Peano.zero := by
  cases h_val : d.val with
  | nil =>
    unfold Decimal.isNormalized at h
    rw [h_val] at h
    contradiction
  | cons digit rest =>
    unfold Decimal.isNormalized at h
    rw [h_val] at h
    exact of_decide_eq_true h

theorem Decimal.length_eq_of_toCardinalList_eq_of_isNormalized (a b : Decimal)
  (ha : a.isNormalized = true) (hb : b.isNormalized = true)
  (hval : Decimal.toCardinalList a.val = Decimal.toCardinalList b.val) :
  Decimal.lengthList a.val = Decimal.lengthList b.val := by
  apply Nat.le_antisymm
  · apply Nat.le_of_not_gt
    intro hlt
    have hb_upper := Decimal.toCardinalList_lt_pow_length b.val b.property.left
    have ha_lower := Decimal.pow_pred_length_le_toCardinalList a.val (Decimal.isNormalized_head_ne_zero a ha)
    rw [hval] at ha_lower
    have hle_pred : _root_.Nat.le (Decimal.lengthList b.val) (_root_.Nat.pred (Decimal.lengthList a.val)) := Nat.le_pred_of_lt hlt
    have hpow_le : _root_.Nat.le (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList b.val))
        (_root_.Nat.pow CardinalNatural.Peano.ten (_root_.Nat.pred (Decimal.lengthList a.val))) := by
      apply Nat.pow_le_pow_right
      · unfold CardinalNatural.Peano.ten
        exact Nat.zero_lt_succ 9
      · exact hle_pred
    exact Nat.not_lt_of_ge (Nat.le_trans hpow_le ha_lower) hb_upper
  · apply Nat.le_of_not_gt
    intro hlt
    have ha_upper := Decimal.toCardinalList_lt_pow_length a.val a.property.left
    have hb_lower := Decimal.pow_pred_length_le_toCardinalList b.val (Decimal.isNormalized_head_ne_zero b hb)
    rw [← hval] at hb_lower
    have hle_pred : _root_.Nat.le (Decimal.lengthList a.val) (_root_.Nat.pred (Decimal.lengthList b.val)) := Nat.le_pred_of_lt hlt
    have hpow_le : _root_.Nat.le (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList a.val))
        (_root_.Nat.pow CardinalNatural.Peano.ten (_root_.Nat.pred (Decimal.lengthList b.val))) := by
      apply Nat.pow_le_pow_right
      · unfold CardinalNatural.Peano.ten
        exact Nat.zero_lt_succ 9
      · exact hle_pred
    exact Nat.not_lt_of_ge (Nat.le_trans hpow_le hb_lower) ha_upper

theorem Decimal.digit_mul_add_div (d r p : Nat)
  (hp : _root_.Nat.lt 0 p) (hr : _root_.Nat.lt r p) :
  (_root_.Nat.add (_root_.Nat.mul d p) r) / p = d := by
  rw [show _root_.Nat.add (_root_.Nat.mul d p) r = _root_.Nat.add r (_root_.Nat.mul d p) from _root_.Nat.add_comm (_root_.Nat.mul d p) r]
  have h := Nat.add_mul_div_right r d hp
  simpa [Nat.div_eq_of_lt hr] using h

theorem Decimal.digit_mul_add_mod (d r p : Nat)
  (hr : _root_.Nat.lt r p) :
  (_root_.Nat.add (_root_.Nat.mul d p) r) % p = r := by
  rw [show _root_.Nat.add (_root_.Nat.mul d p) r = _root_.Nat.add r (_root_.Nat.mul d p) from _root_.Nat.add_comm (_root_.Nat.mul d p) r]
  have h := Nat.add_mul_mod_self_right r d p
  exact h.trans (Nat.mod_eq_of_lt hr)

theorem Decimal.list_eq_of_toCardinalList_eq_of_length_eq
  (a b : ZeroMath.Sequences.List CardinalNatural.Peano)
  (ha : CardinalNatural.Peano.AllLessThanTen a) (hb : CardinalNatural.Peano.AllLessThanTen b)
  (hlen : Decimal.lengthList a = Decimal.lengthList b)
  (hval : Decimal.toCardinalList a = Decimal.toCardinalList b) :
  a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons d ds =>
      unfold Decimal.lengthList at hlen
      contradiction
  | cons d ds ih =>
    cases b with
    | nil =>
      unfold Decimal.lengthList at hlen
      contradiction
    | cons e es =>
      unfold CardinalNatural.Peano.AllLessThanTen at ha hb
      unfold Decimal.lengthList at hlen
      have hlen_tail : Decimal.lengthList ds = Decimal.lengthList es := Nat.succ.inj hlen
      rw [Decimal.toCardinalList_cons d ds, Decimal.toCardinalList_cons e es] at hval
      rw [← hlen_tail] at hval
      have h_tail_a := Decimal.toCardinalList_lt_pow_length ds ha.right
      have h_tail_b := Decimal.toCardinalList_lt_pow_length es hb.right
      rw [← hlen_tail] at h_tail_b
      let p := _root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList ds)
      have hp_pos : 0 < p := by
        unfold p
        apply Nat.pow_pos
        unfold CardinalNatural.Peano.ten
        exact Nat.zero_lt_succ 9
      have hq : d = e := by
        have hdiv := congrArg (fun n => n / p) hval
        simp only at hdiv
        unfold p at hdiv hp_pos
        rw [Decimal.digit_mul_add_div d (Decimal.toCardinalList ds) (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList ds)) hp_pos h_tail_a] at hdiv
        rw [Decimal.digit_mul_add_div e (Decimal.toCardinalList es) (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList ds)) hp_pos h_tail_b] at hdiv
        exact hdiv
      have ht : Decimal.toCardinalList ds = Decimal.toCardinalList es := by
        have hmod := congrArg (fun n => n % p) hval
        simp only at hmod
        unfold p at hmod
        rw [Decimal.digit_mul_add_mod d (Decimal.toCardinalList ds) (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList ds)) h_tail_a] at hmod
        rw [Decimal.digit_mul_add_mod e (Decimal.toCardinalList es) (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList ds)) h_tail_b] at hmod
        exact hmod
      have htails := ih es ha.right hb.right hlen_tail ht
      rw [hq, htails]

theorem Decimal.eq_of_toCardinalList_eq_of_isNormalized (a b : Decimal)
  (ha : a.isNormalized = true) (hb : b.isNormalized = true)
  (hval : Decimal.toCardinalList a.val = Decimal.toCardinalList b.val) :
  a = b := by
  apply Subtype.ext
  exact Decimal.list_eq_of_toCardinalList_eq_of_length_eq a.val b.val a.property.left b.property.left
    (Decimal.length_eq_of_toCardinalList_eq_of_isNormalized a b ha hb hval) hval

theorem Decimal.equivalent_of_toCardinalList_eq {a b : Decimal}
  (h : Decimal.toCardinalList a.val = Decimal.toCardinalList b.val) :
  a ≈ b := by
  apply Decimal.equivalent_of_normalize_eq
  apply Decimal.eq_of_toCardinalList_eq_of_isNormalized
  · exact Decimal.normalize_isNormalized a
  · exact Decimal.normalize_isNormalized b
  · rw [Decimal.normalize_toCardinalList, Decimal.normalize_toCardinalList]
    exact h

/-- The decimal digit nine. -/
def Decimal.nine : CardinalNatural.Peano :=
  _root_.Nat.pred CardinalNatural.Peano.ten

/-- Subtracts one from a big-endian decimal digit list, returning a borrow flag. -/
def Decimal.subtractOneBigEndian :
    ZeroMath.Sequences.List CardinalNatural.Peano → ZeroMath.Sequences.List CardinalNatural.Peano × Bool
  | _root_.List.nil => (ZeroMath.Sequences.List.empty, true)
  | _root_.List.cons d ds =>
    let (ds', borrow) := Decimal.subtractOneBigEndian ds
    if borrow then
      if h : d = CardinalNatural.Peano.zero then
        (ZeroMath.Sequences.List.firstElement Decimal.nine ds', true)
      else
        (ZeroMath.Sequences.List.firstElement (CardinalNatural.Peano.predecessor d h) ds', false)
    else
      (ZeroMath.Sequences.List.firstElement d ds', false)

/-- Computes predecessor digits by subtracting one from a big-endian decimal digit list. -/
def Decimal.predecessorHelper (l : ZeroMath.Sequences.List CardinalNatural.Peano) :
    ZeroMath.Sequences.List CardinalNatural.Peano :=
  (Decimal.subtractOneBigEndian l).1

theorem Decimal.nine_lt_ten : Decimal.nine < CardinalNatural.Peano.ten := by
  apply Decimal.cardinalLt_of_natLt
  unfold Decimal.nine CardinalNatural.Peano.ten
  exact Nat.lt_succ_self 9

theorem Decimal.predecessor_lt_ten (d : CardinalNatural.Peano)
  (h_digit : d < CardinalNatural.Peano.ten) (h_nonzero : d ≠ CardinalNatural.Peano.zero) :
  CardinalNatural.Peano.predecessor d h_nonzero < CardinalNatural.Peano.ten := by
  cases d with
  | zero => contradiction
  | succ n =>
    unfold CardinalNatural.Peano.predecessor
    apply Decimal.cardinalLt_of_natLt
    exact Nat.lt_of_succ_lt (Decimal.natLt_of_cardinalLt h_digit)

theorem Decimal.subtractOneBigEndian_allLessThanTenBool
  (l : ZeroMath.Sequences.List CardinalNatural.Peano)
  (h : CardinalNatural.Peano.AllLessThanTen l) :
  Decimal.allLessThanTenBool (Decimal.subtractOneBigEndian l).1 = true := by
  induction l with
  | nil =>
    unfold Decimal.subtractOneBigEndian Decimal.allLessThanTenBool
    rfl
  | cons d ds ih =>
    unfold Decimal.subtractOneBigEndian
    have h_tail : CardinalNatural.Peano.AllLessThanTen ds := by
      unfold CardinalNatural.Peano.AllLessThanTen at h
      exact h.right
    have h_digit : d < CardinalNatural.Peano.ten := by
      unfold CardinalNatural.Peano.AllLessThanTen at h
      exact h.left
    generalize h_sub : Decimal.subtractOneBigEndian ds = res
    cases res with
    | mk ds' borrow =>
      have ih_tail : Decimal.allLessThanTenBool ds' = true := by
        simpa [h_sub] using ih h_tail
      dsimp only
      cases borrow with
      | false =>
        change (if _root_.Nat.blt d CardinalNatural.Peano.ten then Decimal.allLessThanTenBool ds' else false) = true
        have h_blt : _root_.Nat.blt d CardinalNatural.Peano.ten = true := by
          apply Nat.blt_eq.mpr
          exact Decimal.natLt_of_cardinalLt h_digit
        rw [h_blt]
        exact ih_tail
      | true =>
        by_cases h_zero : d = CardinalNatural.Peano.zero
        · rw [dif_pos h_zero]
          change (if _root_.Nat.blt Decimal.nine CardinalNatural.Peano.ten then Decimal.allLessThanTenBool ds' else false) = true
          have h_blt : _root_.Nat.blt Decimal.nine CardinalNatural.Peano.ten = true := by
            apply Nat.blt_eq.mpr
            exact Decimal.natLt_of_cardinalLt Decimal.nine_lt_ten
          rw [h_blt]
          exact ih_tail
        · rw [dif_neg h_zero]
          change (if _root_.Nat.blt (CardinalNatural.Peano.predecessor d h_zero) CardinalNatural.Peano.ten then Decimal.allLessThanTenBool ds' else false) = true
          have h_blt : _root_.Nat.blt (CardinalNatural.Peano.predecessor d h_zero) CardinalNatural.Peano.ten = true := by
            apply Nat.blt_eq.mpr
            exact Decimal.natLt_of_cardinalLt (Decimal.predecessor_lt_ten d h_digit h_zero)
          rw [h_blt]
          exact ih_tail

theorem Decimal.subtractOneBigEndian_noBorrow
  (l : ZeroMath.Sequences.List CardinalNatural.Peano)
  (h : CardinalNatural.Peano.HasNonZero l) :
  (Decimal.subtractOneBigEndian l).2 = false := by
  induction l with
  | nil =>
    unfold CardinalNatural.Peano.HasNonZero at h
    cases h
  | cons d ds ih =>
    unfold Decimal.subtractOneBigEndian
    generalize h_sub : Decimal.subtractOneBigEndian ds = res
    cases res with
    | mk ds' borrow =>
      dsimp only
      cases borrow with
      | false => rfl
      | true =>
        by_cases h_zero : d = CardinalNatural.Peano.zero
        · rw [dif_pos h_zero]
          unfold CardinalNatural.Peano.HasNonZero at h
          cases h with
          | inl h_head => contradiction
          | inr h_tail =>
            have ih_tail := ih h_tail
            rw [h_sub] at ih_tail
            contradiction
        · rw [dif_neg h_zero]
          rfl


theorem Decimal.subtractOneBigEndian_length
  (l : ZeroMath.Sequences.List CardinalNatural.Peano) :
  Decimal.lengthList (Decimal.subtractOneBigEndian l).1 = Decimal.lengthList l := by
  induction l with
  | nil => rfl
  | cons d ds ih =>
    unfold Decimal.subtractOneBigEndian
    generalize h_sub : Decimal.subtractOneBigEndian ds = res
    cases res with
    | mk ds' borrow =>
      have ih_tail : Decimal.lengthList ds' = Decimal.lengthList ds := by
        simpa [h_sub] using ih
      dsimp only
      cases borrow with
      | false =>
        unfold ZeroMath.Sequences.List.firstElement Decimal.lengthList
        exact congrArg CardinalNatural.Peano.successor ih_tail
      | true =>
        by_cases h_zero : d = CardinalNatural.Peano.zero
        · rw [dif_pos h_zero]
          unfold ZeroMath.Sequences.List.firstElement Decimal.lengthList
          exact congrArg CardinalNatural.Peano.successor ih_tail
        · rw [dif_neg h_zero]
          unfold ZeroMath.Sequences.List.firstElement Decimal.lengthList
          exact congrArg CardinalNatural.Peano.successor ih_tail

theorem Decimal.subtractOneBigEndian_value
  (l : ZeroMath.Sequences.List CardinalNatural.Peano) :
  _root_.Nat.add (Decimal.toCardinalList (Decimal.subtractOneBigEndian l).1) 1 =
    _root_.Nat.add (Decimal.toCardinalList l)
      (if (Decimal.subtractOneBigEndian l).2 then _root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList l) else 0) := by
  induction l with
  | nil =>
    unfold Decimal.subtractOneBigEndian Decimal.toCardinalList Decimal.toCardinalHelper Decimal.lengthList CardinalNatural.Peano.ten
    rfl
  | cons d ds ih =>
    unfold Decimal.subtractOneBigEndian
    generalize h_sub : Decimal.subtractOneBigEndian ds = res
    cases res with
    | mk ds' borrow =>
      have ih_tail := ih
      rw [h_sub] at ih_tail
      dsimp only at ih_tail ⊢
      have h_len : Decimal.lengthList ds' = Decimal.lengthList ds := by
        have h_len_all := Decimal.subtractOneBigEndian_length ds
        rw [h_sub] at h_len_all
        exact h_len_all
      cases borrow with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        unfold ZeroMath.Sequences.List.firstElement
        rw [Decimal.toCardinalList_cons d ds', Decimal.toCardinalList_cons d ds]
        rw [h_len]
        simp at ih_tail
        change _root_.Nat.add (_root_.Nat.add (_root_.Nat.mul d (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList ds))) (Decimal.toCardinalList ds')) 1 =
          _root_.Nat.add (_root_.Nat.add (_root_.Nat.mul d (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList ds))) (Decimal.toCardinalList ds)) 0
        simpa [Nat.add_assoc] using congrArg
          (fun x => _root_.Nat.add (_root_.Nat.mul d (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList ds))) x) ih_tail
      | true =>
        simp only [↓reduceIte]
        by_cases h_zero : d = CardinalNatural.Peano.zero
        · rw [dif_pos h_zero]
          unfold ZeroMath.Sequences.List.firstElement
          rw [Decimal.toCardinalList_cons Decimal.nine ds', Decimal.toCardinalList_cons d ds]
          rw [h_len]
          simp at ih_tail
          simp only [↓reduceIte]
          subst h_zero
          unfold Decimal.nine CardinalNatural.Peano.ten CardinalNatural.Peano.zero
          change _root_.Nat.add (_root_.Nat.add (_root_.Nat.mul 9 (_root_.Nat.pow (10 : Nat) (Decimal.lengthList ds))) (Decimal.toCardinalList ds')) 1 =
            _root_.Nat.add (_root_.Nat.add (_root_.Nat.mul 0 (_root_.Nat.pow (10 : Nat) (Decimal.lengthList ds))) (Decimal.toCardinalList ds))
              (_root_.Nat.pow (10 : Nat) (_root_.Nat.succ (Decimal.lengthList ds)))
          unfold CardinalNatural.Peano.ten at ih_tail
          have h_congr := congrArg
            (fun x => _root_.Nat.add (_root_.Nat.mul 9 (_root_.Nat.pow (10 : Nat) (Decimal.lengthList ds))) x) ih_tail
          have h_left :
              _root_.Nat.add (_root_.Nat.add (_root_.Nat.mul 9 (_root_.Nat.pow (10 : Nat) (Decimal.lengthList ds))) (Decimal.toCardinalList ds')) 1 =
                _root_.Nat.add (_root_.Nat.mul 9 (_root_.Nat.pow (10 : Nat) (Decimal.lengthList ds)))
                  (_root_.Nat.add (Decimal.toCardinalList ds) (_root_.Nat.pow (10 : Nat) (Decimal.lengthList ds))) := by
            simpa [Nat.add_assoc] using h_congr
          have h_pow : _root_.Nat.pow (10 : Nat) (_root_.Nat.succ (Decimal.lengthList ds)) =
              _root_.Nat.mul (_root_.Nat.pow (10 : Nat) (Decimal.lengthList ds)) 10 := by
            exact Nat.pow_succ 10 (Decimal.lengthList ds)
          rw [h_left, h_pow]
          let power : Nat := _root_.Nat.pow (10 : Nat) (Decimal.lengthList ds)
          change _root_.Nat.add (_root_.Nat.mul 9 power) (_root_.Nat.add (Decimal.toCardinalList ds) power) =
            _root_.Nat.add (_root_.Nat.add (_root_.Nat.mul 0 power) (Decimal.toCardinalList ds)) (_root_.Nat.mul power 10)
          rw [show power.mul 10 = _root_.Nat.add (_root_.Nat.mul 9 power) power by
            exact (Nat.mul_succ power 9).trans (by
              rw [Nat.mul_comm power 9]
              rfl)]
          simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        · rw [dif_neg h_zero]
          unfold ZeroMath.Sequences.List.firstElement
          rw [Decimal.toCardinalList_cons (CardinalNatural.Peano.predecessor d h_zero) ds', Decimal.toCardinalList_cons d ds]
          rw [h_len]
          simp at ih_tail
          simp only [Bool.false_eq_true, ↓reduceIte]
          cases d with
          | zero => contradiction
          | succ n =>
            unfold CardinalNatural.Peano.predecessor
            change _root_.Nat.add (_root_.Nat.add (_root_.Nat.mul n (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList ds))) (Decimal.toCardinalList ds')) 1 =
              _root_.Nat.add (_root_.Nat.add (_root_.Nat.mul (_root_.Nat.succ n) (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList ds))) (Decimal.toCardinalList ds)) 0
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, _root_.Nat.succ_mul] using congrArg
              (fun x => _root_.Nat.add (_root_.Nat.mul n (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList ds))) x) ih_tail

theorem Decimal.toCardinalList_eq_zero_of_hasNonZeroBool_false
  (l : ZeroMath.Sequences.List CardinalNatural.Peano)
  (h : Decimal.hasNonZeroBool l = false) :
  Decimal.toCardinalList l = CardinalNatural.Peano.zero := by
  induction l with
  | nil => rfl
  | cons d ds ih =>
    unfold Decimal.hasNonZeroBool at h
    by_cases h_zero : d = CardinalNatural.Peano.zero
    · simp [h_zero] at h
      rw [Decimal.toCardinalList_cons, h_zero]
      simpa [CardinalNatural.Peano.zero] using ih h
    · simp [h_zero] at h

theorem Decimal.predecessorHelper_hasNonZero (d : Decimal) (h : ¬ d ≈ Decimal.one) :
  Decimal.hasNonZeroBool (Decimal.predecessorHelper d.val) = true := by
  by_cases h_nonzero : Decimal.hasNonZeroBool (Decimal.predecessorHelper d.val) = true
  · exact h_nonzero
  · have h_false : Decimal.hasNonZeroBool (Decimal.predecessorHelper d.val) = false := by
      cases h_bool : Decimal.hasNonZeroBool (Decimal.predecessorHelper d.val) with
      | false => rfl
      | true => contradiction
    have h_value := Decimal.subtractOneBigEndian_value d.val
    have h_noBorrow := Decimal.subtractOneBigEndian_noBorrow d.val d.property.right
    unfold Decimal.predecessorHelper at h_false
    have h_zero := Decimal.toCardinalList_eq_zero_of_hasNonZeroBool_false (Decimal.subtractOneBigEndian d.val).1 h_false
    rw [h_noBorrow] at h_value
    simp only [Bool.false_eq_true, ↓reduceIte] at h_value
    rw [h_zero] at h_value
    simp at h_value
    have h_one : Decimal.toCardinalList Decimal.one.val = CardinalNatural.Peano.successor CardinalNatural.Peano.zero := rfl
    have h_eq_one : Decimal.toCardinalList d.val = Decimal.toCardinalList Decimal.one.val := by
      rw [h_one]
      change Decimal.toCardinalList d.val = _root_.Nat.succ _root_.Nat.zero
      exact h_value.symm
    exact False.elim (h (Decimal.equivalent_of_toCardinalList_eq h_eq_one))

/-- Computes the predecessor of a decimal ordinal natural that is not equivalent to one. -/
def Decimal.predecessor (d : Decimal) (h : ¬ d ≈ Decimal.one) : Decimal :=
  let digits := Decimal.predecessorHelper d.val
  ⟨digits, ⟨
    Decimal.allLessThanTenBool_sound digits (by
      unfold digits Decimal.predecessorHelper
      exact Decimal.subtractOneBigEndian_allLessThanTenBool d.val d.property.left),
    Decimal.hasNonZeroBool_sound digits (by
      unfold digits
      exact Decimal.predecessorHelper_hasNonZero d h)⟩⟩

theorem Decimal.predecessor_toCardinalList (d : Decimal) (h : ¬ d ≈ Decimal.one) :
  _root_.Nat.add (Decimal.toCardinalList (Decimal.predecessor d h).val) 1 = Decimal.toCardinalList d.val := by
  unfold Decimal.predecessor Decimal.predecessorHelper
  dsimp only
  have h_value := Decimal.subtractOneBigEndian_value d.val
  have h_noBorrow := Decimal.subtractOneBigEndian_noBorrow d.val d.property.right
  rw [h_noBorrow] at h_value
  simpa using h_value

theorem Decimal.add_assoc (a b c : Decimal) :
  a + b + c ≈ a + (b + c) := by
  apply Decimal.equivalent_of_toCardinalList_eq
  repeat rw [Decimal.add_toCardinalList]
  exact Nat.add_assoc (Decimal.toCardinalList a.val) (Decimal.toCardinalList b.val) (Decimal.toCardinalList c.val)

theorem Decimal.successorHelper_startsNonZero
  (l : ZeroMath.Sequences.List CardinalNatural.Peano)
  (h : match l with
    | _root_.List.nil => False
    | _root_.List.cons digit _ => digit ≠ CardinalNatural.Peano.zero) :
  match Decimal.successorHelper l with
  | _root_.List.nil => False
  | _root_.List.cons digit _ => digit ≠ CardinalNatural.Peano.zero := by
  cases l with
  | nil => cases h
  | cons digit rest =>
    unfold Decimal.successorHelper Decimal.addOneBigEndian
    generalize h_add : Decimal.addOneBigEndian rest = res
    cases res with
    | mk rest' carry =>
      dsimp only
      cases carry with
      | false =>
        exact h
      | true =>
        by_cases hten : CardinalNatural.Peano.successor digit = CardinalNatural.Peano.ten
        · rw [if_pos hten]
          change CardinalNatural.Peano.successor CardinalNatural.Peano.zero ≠ CardinalNatural.Peano.zero
          exact CardinalNatural.Peano.succ_ne_zero CardinalNatural.Peano.zero
        · rw [if_neg hten]
          change CardinalNatural.Peano.successor digit ≠ CardinalNatural.Peano.zero
          exact CardinalNatural.Peano.succ_ne_zero digit

theorem Decimal.successor_isNormalized (d : Decimal)
  (h : d.isNormalized = true) :
  (Decimal.successor d).isNormalized = true := by
  have h_start := Decimal.successorHelper_startsNonZero d.val (Decimal.isNormalized_head_ne_zero d h)
  unfold Decimal.successor Decimal.isNormalized
  change (match Decimal.successorHelper d.val with
    | _root_.List.nil => false
    | _root_.List.cons digit _ => decide (digit ≠ CardinalNatural.Peano.zero)) = true
  cases h_succ : Decimal.successorHelper d.val with
  | nil =>
    rw [h_succ] at h_start
    cases h_start
  | cons digit rest =>
    rw [h_succ] at h_start
    exact decide_eq_true h_start

theorem Decimal.fromPeano_isNormalized (p : OrdinalNatural.Peano) :
  (Decimal.fromPeano p).isNormalized = true := by
  induction p with
  | one => rfl
  | successor p ih =>
    unfold Decimal.fromPeano
    exact Decimal.successor_isNormalized (Decimal.fromPeano p) ih

theorem Decimal.fromPeano_toPeano_of_isNormalized (x : Decimal)
  (h : x.isNormalized = true) :
  Decimal.fromPeano (x.toPeano) = x := by
  apply Decimal.eq_of_toCardinalList_eq_of_isNormalized
  · exact Decimal.fromPeano_isNormalized x.toPeano
  · exact h
  · rw [Decimal.fromPeano_toCardinalList]
    exact Decimal.toPeano_toNat x

theorem Decimal.add_toPeano (x y : Decimal) :
  (x + y).toPeano = x.toPeano + y.toPeano := by
  apply OrdinalNatural.Peano.fromNat_toNat_helper
  rw [Peano.toNat_add]
  rw [Decimal.toPeano_toNat]
  rw [Decimal.toPeano_toNat]
  exact (Decimal.add_toCardinalList x y).symm

def Decimal.lessThanListBool : ZeroMath.Sequences.List CardinalNatural.Peano → ZeroMath.Sequences.List CardinalNatural.Peano → Bool
  | _root_.List.nil, _root_.List.nil => false
  | _root_.List.nil, _root_.List.cons _ _ => true
  | _root_.List.cons _ _, _root_.List.nil => false
  | _root_.List.cons xd xs, _root_.List.cons yd ys =>
    if _root_.Nat.blt xd yd then
      true
    else if _root_.Nat.blt yd xd then
      false
    else
      Decimal.lessThanListBool xs ys

def Decimal.lessThanListLenBool (x y : ZeroMath.Sequences.List CardinalNatural.Peano) : Bool :=
  let xLen := x.length
  let yLen := y.length
  if _root_.Nat.blt xLen yLen then
    true
  else if _root_.Nat.blt yLen xLen then
    false
  else
    Decimal.lessThanListBool x y

def Decimal.lessThanBool (x y : Decimal) : Bool :=
  Decimal.lessThanListLenBool (Decimal.normalize x).val (Decimal.normalize y).val

def Decimal.LessThan (x y : Decimal) : Prop :=
  x.toPeano < y.toPeano

instance : LT Decimal where
  lt := Decimal.LessThan

def Decimal.LessThanOrEquivalent (x y : Decimal) : Prop :=
  x < y ∨ x ≈ y

instance : LE Decimal where
  le := Decimal.LessThanOrEquivalent

theorem Decimal.lt_trans {a b c : Decimal} (h1 : a < b) (h2 : b < c) : a < c := by
  have h1' : a.toPeano < b.toPeano := h1
  have h2' : b.toPeano < c.toPeano := h2
  exact Peano.lt_trans h1' h2'

theorem Decimal.le_trans {a b c : Decimal} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  have h1' : a < b ∨ a ≈ b := h1
  have h2' : b < c ∨ b ≈ c := h2
  cases h1' with
  | inl h1_lt =>
    cases h2' with
    | inl h2_lt =>
      left
      exact Decimal.lt_trans h1_lt h2_lt
    | inr h2_eq =>
      left
      have hab : a.toPeano < b.toPeano := h1_lt
      have hbc : b.toPeano = c.toPeano := by
        rw [← Decimal.normalize_toPeano b, ← Decimal.normalize_toPeano c]
        have heq : Decimal.normalize b = Decimal.normalize c := h2_eq
        rw [heq]
      have hac : a.toPeano < c.toPeano := by
        rw [← hbc]
        exact hab
      exact hac
  | inr h1_eq =>
    cases h2' with
    | inl h2_lt =>
      left
      have hab : a.toPeano = b.toPeano := by
        rw [← Decimal.normalize_toPeano a, ← Decimal.normalize_toPeano b]
        have heq : Decimal.normalize a = Decimal.normalize b := h1_eq
        rw [heq]
      have hbc : b.toPeano < c.toPeano := h2_lt
      have hac : a.toPeano < c.toPeano := by
        rw [hab]
        exact hbc
      exact hac
    | inr h2_eq =>
      right
      have hab : Decimal.normalize a = Decimal.normalize b := h1_eq
      have hbc : Decimal.normalize b = Decimal.normalize c := h2_eq
      exact Eq.trans hab hbc

theorem Decimal.trichotomy (x y : Decimal) : ZeroMath.Logic.Trichotomy (x < y) (x ≈ y) (y < x) := by
  have h := OrdinalNatural.Peano.trichotomy x.toPeano y.toPeano
  cases h with
  | first p nq nr =>
    apply ZeroMath.Logic.Trichotomy.first
    · exact p
    · intro h_eq
      have h_peano : x.toPeano = y.toPeano := by
        rw [← Decimal.normalize_toPeano x, ← Decimal.normalize_toPeano y]
        have heq : Decimal.normalize x = Decimal.normalize y := h_eq
        rw [heq]
      exact nq h_peano
    · exact nr
  | second q np nr =>
    apply ZeroMath.Logic.Trichotomy.second
    · apply Decimal.equivalent_of_toCardinalList_eq
      have h1 := Decimal.toPeano_toNat x
      have h2 := Decimal.toPeano_toNat y
      rw [q] at h1
      exact h1.symm.trans h2
    · exact np
    · exact nr
  | third r np nq =>
    apply ZeroMath.Logic.Trichotomy.third
    · exact r
    · exact np
    · intro h_eq
      have h_peano : x.toPeano = y.toPeano := by
        rw [← Decimal.normalize_toPeano x, ← Decimal.normalize_toPeano y]
        have heq : Decimal.normalize x = Decimal.normalize y := h_eq
        rw [heq]
      exact nq h_peano

/-- Subtracts two single decimal digits with a borrow flag, returning the result digit and a new borrow flag. -/
def Decimal.columnarSubtractDigit (a b : CardinalNatural.Peano) (borrow : Bool) : CardinalNatural.Peano × Bool :=
  let total_b := _root_.Nat.add b
    (if borrow then CardinalNatural.Peano.successor CardinalNatural.Peano.zero else CardinalNatural.Peano.zero)
  if _root_.Nat.blt a total_b then
    (_root_.Nat.add (_root_.Nat.sub CardinalNatural.Peano.ten total_b) a, true)
  else
    (_root_.Nat.sub a total_b, false)

theorem Decimal.columnarSubtractDigit_allLessThanTenBool (a b : CardinalNatural.Peano) (borrow : Bool)
    (ha : _root_.Nat.blt a CardinalNatural.Peano.ten = true)
    (hb : _root_.Nat.blt b CardinalNatural.Peano.ten = true) :
    _root_.Nat.blt (Decimal.columnarSubtractDigit a b borrow).1 CardinalNatural.Peano.ten = true := by
  unfold Decimal.columnarSubtractDigit
  have ha_lt : _root_.Nat.lt a CardinalNatural.Peano.ten := Nat.blt_eq.mp ha
  have hb_lt : _root_.Nat.lt b CardinalNatural.Peano.ten := Nat.blt_eq.mp hb
  have ha_bound : _root_.Nat.lt a (10 : Nat) := by unfold CardinalNatural.Peano.ten at ha_lt; exact ha_lt
  have hb_bound : _root_.Nat.lt b (10 : Nat) := by unfold CardinalNatural.Peano.ten at hb_lt; exact hb_lt
  cases borrow
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split
    · next h =>
      apply Nat.blt_eq.mpr
      unfold CardinalNatural.Peano.ten CardinalNatural.Peano.zero
      simp only [Nat.add_zero]
      have h_lt : _root_.Nat.lt a b := by
        have := Nat.blt_eq.mp h
        simp only [Nat.add_zero] at this
        exact this
      exact Nat.lt_of_lt_of_eq (Nat.add_lt_add_left h_lt (_root_.Nat.sub 10 b)) (Nat.sub_add_cancel (Nat.le_of_lt hb_bound))
    · next h =>
      apply Nat.blt_eq.mpr
      unfold CardinalNatural.Peano.ten CardinalNatural.Peano.zero
      simp only [Nat.add_zero]
      exact Nat.lt_of_le_of_lt (Nat.sub_le a b) ha_bound
  · simp only [↓reduceIte, CardinalNatural.Peano.successor, CardinalNatural.Peano.zero]
    split
    · next h =>
      apply Nat.blt_eq.mpr
      unfold CardinalNatural.Peano.ten
      have h_lt : _root_.Nat.lt a (_root_.Nat.add b (Nat.succ Nat.zero)) := Nat.blt_eq.mp h
      have hb1_le : Nat.succ b ≤ 10 := Nat.succ_le_of_lt hb_bound
      have hstep : _root_.Nat.add b (Nat.succ Nat.zero) = Nat.succ b := rfl
      show _root_.Nat.lt (_root_.Nat.add (_root_.Nat.sub 10 (_root_.Nat.add b (Nat.succ Nat.zero))) a) 10
      rw [hstep]
      exact Nat.lt_of_lt_of_eq (Nat.add_lt_add_left h_lt (_root_.Nat.sub 10 (Nat.succ b))) (Nat.sub_add_cancel hb1_le)
    · next h =>
      apply Nat.blt_eq.mpr
      unfold CardinalNatural.Peano.ten
      show _root_.Nat.lt (_root_.Nat.sub a (_root_.Nat.add b (Nat.succ Nat.zero))) 10
      exact Nat.lt_of_le_of_lt (Nat.sub_le a (_root_.Nat.add b (Nat.succ Nat.zero))) ha_bound

theorem Decimal.columnarSubtractDigit_value (a b : CardinalNatural.Peano) (borrow : Bool)
    (hb : _root_.Nat.blt b CardinalNatural.Peano.ten = true) :
    _root_.Nat.add (_root_.Nat.add (Decimal.columnarSubtractDigit a b borrow).1 b)
      (if borrow then CardinalNatural.Peano.successor CardinalNatural.Peano.zero else CardinalNatural.Peano.zero) =
    _root_.Nat.add a
      (if (Decimal.columnarSubtractDigit a b borrow).2 then CardinalNatural.Peano.ten else CardinalNatural.Peano.zero) := by
  unfold Decimal.columnarSubtractDigit
  have hb_lt : _root_.Nat.lt b CardinalNatural.Peano.ten := Nat.blt_eq.mp hb
  have hb_bound : _root_.Nat.lt b (10 : Nat) := by unfold CardinalNatural.Peano.ten at hb_lt; exact hb_lt
  -- Key fact: Nat.add b Nat.zero = b by rfl
  have hb0 : _root_.Nat.add b Nat.zero = b := rfl
  cases borrow
  · -- borrow = false: total_b = Nat.add b Nat.zero
    simp only [Bool.false_eq_true, ↓reduceIte, CardinalNatural.Peano.zero, CardinalNatural.Peano.ten]
    -- Rewrite Nat.add b Nat.zero to b everywhere in the goal
    rw [hb0]
    split
    · next h =>
      -- a < b case: result = 10 - b + a, borrow_out = true
      simp only [ite_true]
      -- Goal: (((10-b).add a).add b).add Nat.zero = Nat.add a 10
      have hb_le : _root_.Nat.le b 10 := Nat.le_of_lt hb_bound
      have hsub : _root_.Nat.add (_root_.Nat.sub 10 b) b = 10 := Nat.sub_add_cancel hb_le
      -- Prove by rearranging: 10-b+a+b+0 = a+10
      have h0 : _root_.Nat.add (_root_.Nat.add (_root_.Nat.add (_root_.Nat.sub 10 b) a) b) Nat.zero =
                _root_.Nat.add (_root_.Nat.add (_root_.Nat.sub 10 b) a) b := rfl
      rw [h0]
      have h1 : _root_.Nat.add (_root_.Nat.add (_root_.Nat.sub 10 b) a) b =
                _root_.Nat.add (_root_.Nat.sub 10 b) (_root_.Nat.add a b) := Nat.add_assoc _ _ _
      rw [h1, show _root_.Nat.add a b = _root_.Nat.add b a from Nat.add_comm a b,
          show _root_.Nat.add (_root_.Nat.sub 10 b) (_root_.Nat.add b a) =
               _root_.Nat.add (_root_.Nat.add (_root_.Nat.sub 10 b) b) a from (Nat.add_assoc _ _ _).symm,
          hsub]
      exact Nat.add_comm 10 a
    · next h =>
      -- a >= b case: result = a - b, borrow_out = false
      simp only [ite_false]
      -- Goal: (Nat.sub a b, false).fst + b + 0 = a + 0 (both have trailing 0)
      -- = Nat.add (Nat.add (Nat.sub a b) b) Nat.zero = Nat.add a Nat.zero
      have hb_le : _root_.Nat.le b a :=
        Nat.le_of_not_lt (fun ht => h (Nat.blt_eq.mpr ht))
      have hsub : _root_.Nat.add (_root_.Nat.sub a b) b = a := Nat.sub_add_cancel hb_le
      -- Both sides end in Nat.zero (= 0), factor out
      show _root_.Nat.add (_root_.Nat.add (_root_.Nat.sub a b) b) Nat.zero = _root_.Nat.add a Nat.zero
      have h0 : _root_.Nat.add (_root_.Nat.add (_root_.Nat.sub a b) b) Nat.zero =
                _root_.Nat.add (_root_.Nat.sub a b) b := rfl
      have h1 : _root_.Nat.add a Nat.zero = a := rfl
      rw [h0, hsub, h1]
  · -- borrow = true: total_b = Nat.add b (Nat.succ Nat.zero)
    simp only [↓reduceIte, CardinalNatural.Peano.successor, CardinalNatural.Peano.zero, CardinalNatural.Peano.ten]
    split
    · next h =>
      -- a < b.succ case: result = 10 - (b+1) + a, borrow_out = true
      simp only [ite_true]
      -- Goal: Nat.add (Nat.add (Nat.add (Nat.sub 10 B1) a) b) 1 = Nat.add a 10
      -- where B1 = Nat.add b (Nat.succ Nat.zero) = b + 1
      have h_lt : _root_.Nat.lt a (_root_.Nat.add b (Nat.succ Nat.zero)) := Nat.blt_eq.mp h
      have hb1_le : _root_.Nat.le (_root_.Nat.add b (Nat.succ Nat.zero)) 10 := Nat.succ_le_of_lt hb_bound
      have hsub : _root_.Nat.add (_root_.Nat.sub 10 (_root_.Nat.add b (Nat.succ Nat.zero)))
          (_root_.Nat.add b (Nat.succ Nat.zero)) = 10 :=
        Nat.sub_add_cancel hb1_le
      -- Prove: (10-B1+a+b)+1 = a+10
      -- = (10-B1+a)+B1 = (10-B1)+(a+B1) = (10-B1)+(B1+a) = ((10-B1)+B1)+a = 10+a = a+10
      let B1 := _root_.Nat.add b (Nat.succ Nat.zero)
      have hstep1 : _root_.Nat.add (_root_.Nat.add (_root_.Nat.add (_root_.Nat.sub 10 B1) a) b) (Nat.succ Nat.zero) =
                    _root_.Nat.add (_root_.Nat.add (_root_.Nat.sub 10 B1) a) B1 := Nat.add_assoc _ _ _
      rw [hstep1,
          show _root_.Nat.add (_root_.Nat.add (_root_.Nat.sub 10 B1) a) B1 =
               _root_.Nat.add (_root_.Nat.sub 10 B1) (_root_.Nat.add a B1) from Nat.add_assoc _ _ _,
          show _root_.Nat.add a B1 = _root_.Nat.add B1 a from Nat.add_comm a B1,
          show _root_.Nat.add (_root_.Nat.sub 10 B1) (_root_.Nat.add B1 a) =
               _root_.Nat.add (_root_.Nat.add (_root_.Nat.sub 10 B1) B1) a from (Nat.add_assoc _ _ _).symm,
          hsub]
      exact Nat.add_comm 10 a
    · next h =>
      -- a >= b.succ case: result = a - (b+1), borrow_out = false
      simp only [ite_false]
      -- Goal: Nat.add (Nat.add (Nat.sub a B1) b) 1 = Nat.add a Nat.zero
      -- = (a-B1+b)+1 = a+0 = a
      -- = (a-B1)+(b+1) = a-B1+B1 = a
      have hbs_le : _root_.Nat.le (_root_.Nat.add b (Nat.succ Nat.zero)) a :=
        Nat.le_of_not_lt (fun ht => h (Nat.blt_eq.mpr ht))
      have hsub : _root_.Nat.add (_root_.Nat.sub a (_root_.Nat.add b (Nat.succ Nat.zero)))
          (_root_.Nat.add b (Nat.succ Nat.zero)) = a :=
        Nat.sub_add_cancel hbs_le
      let B1 := _root_.Nat.add b (Nat.succ Nat.zero)
      have hstep1 : _root_.Nat.add (_root_.Nat.add (_root_.Nat.sub a B1) b) (Nat.succ Nat.zero) =
                    _root_.Nat.add (_root_.Nat.sub a B1) B1 := Nat.add_assoc _ _ _
      show _root_.Nat.add (_root_.Nat.add (_root_.Nat.sub a B1) b) (Nat.succ Nat.zero) = _root_.Nat.add a Nat.zero
      have h_rhs : _root_.Nat.add a Nat.zero = a := rfl
      rw [hstep1, hsub, h_rhs]

/-- Subtracts two big-endian decimal digit lists column by column, returning the result and a borrow flag. -/
def Decimal.subtractAlignedLists :
    ZeroMath.Sequences.List CardinalNatural.Peano →
    ZeroMath.Sequences.List CardinalNatural.Peano →
    ZeroMath.Sequences.List CardinalNatural.Peano × Bool
  | _root_.List.nil, _root_.List.nil => (ZeroMath.Sequences.List.empty, false)
  | _root_.List.cons a as, _root_.List.nil =>
    let (tail, borrow) := Decimal.subtractAlignedLists as _root_.List.nil
    let (digit, nextBorrow) := Decimal.columnarSubtractDigit a CardinalNatural.Peano.zero borrow
    (ZeroMath.Sequences.List.firstElement digit tail, nextBorrow)
  | _root_.List.nil, _root_.List.cons b bs =>
    let (tail, borrow) := Decimal.subtractAlignedLists _root_.List.nil bs
    let (digit, nextBorrow) := Decimal.columnarSubtractDigit CardinalNatural.Peano.zero b borrow
    (ZeroMath.Sequences.List.firstElement digit tail, nextBorrow)
  | _root_.List.cons a as, _root_.List.cons b bs =>
    let (tail, borrow) := Decimal.subtractAlignedLists as bs
    let (digit, nextBorrow) := Decimal.columnarSubtractDigit a b borrow
    (ZeroMath.Sequences.List.firstElement digit tail, nextBorrow)
termination_by a b => a.length + b.length

theorem Decimal.subtractAlignedLists_allLessThanTenBool (a b : ZeroMath.Sequences.List CardinalNatural.Peano)
    (ha : Decimal.allLessThanTenBool a = true) (hb : Decimal.allLessThanTenBool b = true) :
    Decimal.allLessThanTenBool (Decimal.subtractAlignedLists a b).1 = true := by
  induction a generalizing b with
  | nil =>
    induction b with
    | nil =>
      unfold Decimal.subtractAlignedLists Decimal.allLessThanTenBool
      rfl
    | cons b bs ih =>
      unfold Decimal.subtractAlignedLists
      unfold Decimal.allLessThanTenBool at hb
      by_cases hb_digit : _root_.Nat.blt b CardinalNatural.Peano.ten = true
      · simp [hb_digit] at hb
        generalize h_sub : Decimal.subtractAlignedLists _root_.List.nil bs = sub
        cases sub with
        | mk tail borrow =>
          have h_tail : Decimal.allLessThanTenBool tail = true := by simpa [h_sub] using ih hb
          dsimp only
          change (if _root_.Nat.blt (Decimal.columnarSubtractDigit CardinalNatural.Peano.zero b borrow).1
              CardinalNatural.Peano.ten then Decimal.allLessThanTenBool tail else false) = true
          have h_digit := Decimal.columnarSubtractDigit_allLessThanTenBool CardinalNatural.Peano.zero b borrow
            (by apply Nat.blt_eq.mpr; unfold CardinalNatural.Peano.zero CardinalNatural.Peano.ten; exact Nat.zero_lt_succ 9)
            hb_digit
          rw [h_digit]; exact h_tail
      · simp [hb_digit] at hb
  | cons a as ih =>
    cases b with
    | nil =>
      unfold Decimal.subtractAlignedLists
      unfold Decimal.allLessThanTenBool at ha
      by_cases ha_digit : _root_.Nat.blt a CardinalNatural.Peano.ten = true
      · simp [ha_digit] at ha
        generalize h_sub : Decimal.subtractAlignedLists as _root_.List.nil = sub
        cases sub with
        | mk tail borrow =>
          have h_tail : Decimal.allLessThanTenBool tail = true := by
            simpa [h_sub] using ih _root_.List.nil ha (by unfold Decimal.allLessThanTenBool; rfl)
          dsimp only
          change (if _root_.Nat.blt (Decimal.columnarSubtractDigit a CardinalNatural.Peano.zero borrow).1
              CardinalNatural.Peano.ten then Decimal.allLessThanTenBool tail else false) = true
          have h_digit := Decimal.columnarSubtractDigit_allLessThanTenBool a CardinalNatural.Peano.zero borrow ha_digit
            (by apply Nat.blt_eq.mpr; unfold CardinalNatural.Peano.zero CardinalNatural.Peano.ten; exact Nat.zero_lt_succ 9)
          rw [h_digit]; exact h_tail
      · simp [ha_digit] at ha
    | cons b bs =>
      unfold Decimal.subtractAlignedLists
      unfold Decimal.allLessThanTenBool at ha hb
      by_cases ha_digit : _root_.Nat.blt a CardinalNatural.Peano.ten = true
      · by_cases hb_digit : _root_.Nat.blt b CardinalNatural.Peano.ten = true
        · simp [ha_digit, hb_digit] at ha hb
          generalize h_sub : Decimal.subtractAlignedLists as bs = sub
          cases sub with
          | mk tail borrow =>
            have h_tail : Decimal.allLessThanTenBool tail = true := by simpa [h_sub] using ih bs ha hb
            dsimp only
            change (if _root_.Nat.blt (Decimal.columnarSubtractDigit a b borrow).1
                CardinalNatural.Peano.ten then Decimal.allLessThanTenBool tail else false) = true
            have h_digit := Decimal.columnarSubtractDigit_allLessThanTenBool a b borrow ha_digit hb_digit
            rw [h_digit]; exact h_tail
        · simp [hb_digit] at hb
      · simp [ha_digit] at ha

theorem Decimal.subtractAlignedLists_length (a b : ZeroMath.Sequences.List CardinalNatural.Peano)
    (hlen : Decimal.lengthList a = Decimal.lengthList b) :
    Decimal.lengthList (Decimal.subtractAlignedLists a b).1 = Decimal.lengthList a := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => unfold Decimal.subtractAlignedLists Decimal.lengthList; rfl
    | cons b bs => unfold Decimal.lengthList at hlen; cases hlen
  | cons a as ih =>
    cases b with
    | nil => unfold Decimal.lengthList at hlen; cases hlen
    | cons b bs =>
      have htail : Decimal.lengthList as = Decimal.lengthList bs := by
        unfold Decimal.lengthList at hlen; exact Nat.succ.inj hlen
      unfold Decimal.subtractAlignedLists
      generalize h_sub : Decimal.subtractAlignedLists as bs = sub
      cases sub with
      | mk tail borrow =>
        dsimp only
        unfold ZeroMath.Sequences.List.firstElement Decimal.lengthList
        have ih_app := ih bs htail
        rw [h_sub] at ih_app; dsimp only at ih_app
        exact congrArg CardinalNatural.Peano.successor ih_app

theorem Decimal.columnar_place_combine_subtract
    (digit a b p tail asValue bsValue : Nat) (nextBorrow borrow : Bool)
    (hdigit : digit + b + (if borrow then 1 else 0) = a + (if nextBorrow then 10 else 0))
    (htail : tail + bsValue = asValue + (if borrow then p else 0)) :
    digit * p + tail + (b * p + bsValue) = a * p + asValue + (if nextBorrow then p * 10 else 0) := by
  cases nextBorrow <;> cases borrow <;> simp at hdigit htail ⊢
  all_goals
    have hm := congrArg (fun n => n * p) hdigit
    simp only at hm
    repeat rw [Nat.add_mul] at hm
    omega

theorem Decimal.subtractAlignedLists_toCardinalList (a b : ZeroMath.Sequences.List CardinalNatural.Peano)
    (hlen : Decimal.lengthList a = Decimal.lengthList b)
    (hb : CardinalNatural.Peano.AllLessThanTen b) :
    _root_.Nat.add (Decimal.toCardinalList (Decimal.subtractAlignedLists a b).1) (Decimal.toCardinalList b) =
    _root_.Nat.add (Decimal.toCardinalList a)
      (if (Decimal.subtractAlignedLists a b).2 then
        _root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList a) else CardinalNatural.Peano.zero) := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil =>
      unfold Decimal.subtractAlignedLists Decimal.toCardinalList Decimal.toCardinalHelper Decimal.lengthList
        CardinalNatural.Peano.zero
      rfl
    | cons b bs => unfold Decimal.lengthList at hlen; cases hlen
  | cons a as ih =>
    cases b with
    | nil => unfold Decimal.lengthList at hlen; cases hlen
    | cons b bs =>
      have htail : Decimal.lengthList as = Decimal.lengthList bs := by
        unfold Decimal.lengthList at hlen; exact Nat.succ.inj hlen
      unfold CardinalNatural.Peano.AllLessThanTen at hb
      have hb_digit : _root_.Nat.blt b CardinalNatural.Peano.ten = true :=
        Nat.blt_eq.mpr (Decimal.natLt_of_cardinalLt hb.left)
      unfold Decimal.subtractAlignedLists
      generalize h_sub : Decimal.subtractAlignedLists as bs = sub
      cases sub with
      | mk tail borrow =>
        dsimp only
        have ih_app := ih bs htail hb.right
        rw [h_sub] at ih_app; dsimp only at ih_app
        unfold ZeroMath.Sequences.List.firstElement
        rw [Decimal.toCardinalList_cons, Decimal.toCardinalList_cons a as,
            Decimal.toCardinalList_cons b bs]
        have hdigit := Decimal.columnarSubtractDigit_value a b borrow hb_digit
        have htail_len := Decimal.subtractAlignedLists_length as bs htail
        rw [h_sub] at htail_len; dsimp only at htail_len
        rw [htail_len, htail]
        have hpow : _root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList (a :: as)) =
            _root_.Nat.mul (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList bs)) CardinalNatural.Peano.ten := by
          change _root_.Nat.pow CardinalNatural.Peano.ten (CardinalNatural.Peano.successor (Decimal.lengthList as)) =
            _root_.Nat.mul (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList bs)) CardinalNatural.Peano.ten
          rw [htail]
          unfold CardinalNatural.Peano.successor
          exact Nat.pow_succ CardinalNatural.Peano.ten (Decimal.lengthList bs)
        rw [hpow]
        have hdigit_nat :
            _root_.Nat.add (_root_.Nat.add (Decimal.columnarSubtractDigit a b borrow).1 b)
                (if borrow then (1 : Nat) else Nat.zero) =
              _root_.Nat.add a (if (Decimal.columnarSubtractDigit a b borrow).2 then (10 : Nat) else Nat.zero) := by
          simpa [CardinalNatural.Peano.ten, CardinalNatural.Peano.zero, CardinalNatural.Peano.successor] using hdigit
        have ih_nat :
            _root_.Nat.add (Decimal.toCardinalList tail) (Decimal.toCardinalList bs) =
              _root_.Nat.add (Decimal.toCardinalList as)
                (if borrow then _root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList bs) else Nat.zero) := by
          simpa [CardinalNatural.Peano.zero, htail] using ih_app
        exact Decimal.columnar_place_combine_subtract
          (Decimal.columnarSubtractDigit a b borrow).1 a b
          (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList bs))
          (Decimal.toCardinalList tail) (Decimal.toCardinalList as) (Decimal.toCardinalList bs)
          (Decimal.columnarSubtractDigit a b borrow).2 borrow hdigit_nat ih_nat

theorem Decimal.toCardinalList_lt_pow10 (l : ZeroMath.Sequences.List CardinalNatural.Peano)
    (h : CardinalNatural.Peano.AllLessThanTen l) :
    Decimal.toCardinalList l < _root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList l) := by
  induction l with
  | nil =>
    unfold Decimal.toCardinalList Decimal.toCardinalHelper Decimal.lengthList CardinalNatural.Peano.zero
      CardinalNatural.Peano.ten
    exact Decimal.cardinalLt_of_natLt Nat.one_pos
  | cons d ds ih =>
    unfold CardinalNatural.Peano.AllLessThanTen at h
    have hd_lt : d < CardinalNatural.Peano.ten := h.left
    have hds := ih h.right
    rw [Decimal.toCardinalList_cons]
    -- Use lemma: lengthList (d :: ds) = successor (lengthList ds)
    have hlen_cons : Decimal.lengthList (d :: ds) = CardinalNatural.Peano.successor (Decimal.lengthList ds) := by
      simp only [Decimal.lengthList]
    -- Use: pow 10 (successor n) = pow 10 n * 10
    have hpow_succ : _root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList (d :: ds)) =
        _root_.Nat.mul (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList ds)) 10 := by
      rw [hlen_cons]
      unfold CardinalNatural.Peano.successor CardinalNatural.Peano.ten
      exact Nat.pow_succ 10 (Decimal.lengthList ds)
    rw [hpow_succ]
    -- Convert hds and hd_lt to Nat lt
    have hds_nat : _root_.Nat.lt (Decimal.toCardinalList ds)
        (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList ds)) :=
      Decimal.natLt_of_cardinalLt hds
    have hd_nat : _root_.Nat.lt d (10 : Nat) := by
      unfold CardinalNatural.Peano.ten at hd_lt
      exact Decimal.natLt_of_cardinalLt hd_lt
    have hd_succ : Nat.succ d ≤ 10 := Nat.succ_le_of_lt hd_nat
    -- Convert pow ten to pow 10
    have hpow_ten : _root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList ds) =
        _root_.Nat.pow 10 (Decimal.lengthList ds) := by
      unfold CardinalNatural.Peano.ten; rfl
    -- Now prove: d * pow 10 len + toCardinalList ds < pow 10 len * 10
    -- As Nat: d * p + r < p * 10 where r < p and d+1 ≤ 10
    apply Decimal.cardinalLt_of_natLt
    -- Rewrite pow 10 to use Nat 10
    rw [hpow_ten] at hds_nat ⊢
    -- hds_nat : Nat.lt r p  where r = toCardinalList ds, p = pow 10 len
    -- Need: d * p + r < p * 10
    -- Step: d * p + r < d * p + p = (d+1) * p ≤ 10 * p = p * 10
    have h1 : _root_.Nat.lt
        (_root_.Nat.add (_root_.Nat.mul d (_root_.Nat.pow 10 (Decimal.lengthList ds)))
          (Decimal.toCardinalList ds))
        (_root_.Nat.add (_root_.Nat.mul d (_root_.Nat.pow 10 (Decimal.lengthList ds)))
          (_root_.Nat.pow 10 (Decimal.lengthList ds))) :=
      Nat.add_lt_add_left hds_nat _
    have h2 : _root_.Nat.le
        (_root_.Nat.add (_root_.Nat.mul d (_root_.Nat.pow 10 (Decimal.lengthList ds)))
          (_root_.Nat.pow 10 (Decimal.lengthList ds)))
        (_root_.Nat.mul (_root_.Nat.pow 10 (Decimal.lengthList ds)) 10) := by
      -- d * p + p = (d+1) * p ≤ 10 * p = p * 10
      have hsucc_eq : _root_.Nat.add (_root_.Nat.mul d (_root_.Nat.pow 10 (Decimal.lengthList ds)))
            (_root_.Nat.pow 10 (Decimal.lengthList ds)) =
          _root_.Nat.mul (Nat.succ d) (_root_.Nat.pow 10 (Decimal.lengthList ds)) := by
        rw [show _root_.Nat.mul (Nat.succ d) (_root_.Nat.pow 10 (Decimal.lengthList ds)) =
                _root_.Nat.add (_root_.Nat.mul d (_root_.Nat.pow 10 (Decimal.lengthList ds)))
                  (_root_.Nat.pow 10 (Decimal.lengthList ds)) from Nat.succ_mul d _]
      rw [hsucc_eq]
      -- (d+1) * p ≤ 10 * p (since d+1 ≤ 10)
      have hmul : Nat.succ d * _root_.Nat.pow 10 (Decimal.lengthList ds) ≤
          10 * _root_.Nat.pow 10 (Decimal.lengthList ds) :=
        Nat.mul_le_mul_right _ hd_succ
      -- 10 * p = p * 10 by comm
      rw [show _root_.Nat.mul (_root_.Nat.pow 10 (Decimal.lengthList ds)) 10 =
              _root_.Nat.mul 10 (_root_.Nat.pow 10 (Decimal.lengthList ds)) from
        Nat.mul_comm _ _]
      exact hmul
    exact Nat.lt_of_lt_of_le h1 h2

theorem Decimal.subtractAlignedLists_noBorrow (a b : ZeroMath.Sequences.List CardinalNatural.Peano)
    (hlen : Decimal.lengthList a = Decimal.lengthList b)
    (ha : CardinalNatural.Peano.AllLessThanTen a)
    (hb : CardinalNatural.Peano.AllLessThanTen b)
    (hge : Decimal.toCardinalList a ≥ Decimal.toCardinalList b) :
    (Decimal.subtractAlignedLists a b).2 = false := by
  apply Classical.byContradiction
  intro h_borrow
  have h_borrow_true : (Decimal.subtractAlignedLists a b).2 = true := by
    have : (Decimal.subtractAlignedLists a b).2 ≠ false := h_borrow
    cases hb2 : (Decimal.subtractAlignedLists a b).2 with
    | false => exact absurd hb2 this
    | true => rfl
  have h_val := Decimal.subtractAlignedLists_toCardinalList a b hlen hb
  rw [h_borrow_true] at h_val
  simp only [↓reduceIte] at h_val
  have h_result_lt := Decimal.toCardinalList_lt_pow10 (Decimal.subtractAlignedLists a b).1 (by
    apply Decimal.allLessThanTenBool_sound
    apply Decimal.subtractAlignedLists_allLessThanTenBool
    · exact Decimal.allLessThanTenBool_complete a ha
    · exact Decimal.allLessThanTenBool_complete b hb)
  have h_result_len := Decimal.subtractAlignedLists_length a b hlen
  rw [h_result_len] at h_result_lt
  have h_pow_pos : 0 < _root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList a) := by
    apply Nat.pow_pos; unfold CardinalNatural.Peano.ten; decide
  -- h_val (as Nat): result + b = a + pow
  -- h_result_lt (convert to Nat): result < pow
  -- hge (convert to Nat): b ≤ a (i.e., ¬ a < b)
  -- From these: a + pow = result + b < pow + b ≤ pow + a, so a + pow < pow + a, contradiction
  have h_res_lt_nat : _root_.Nat.lt (Decimal.toCardinalList (Decimal.subtractAlignedLists a b).1)
      (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList a)) :=
    Decimal.natLt_of_cardinalLt h_result_lt
  have hge_nat : _root_.Nat.le (Decimal.toCardinalList b) (Decimal.toCardinalList a) := by
    cases hge with
    | inl hlt => exact Nat.le_of_lt (Decimal.natLt_of_cardinalLt hlt)
    | inr heq => exact Nat.le_of_eq heq
  -- h_val is already the Nat equality we need (after simp reduced the if-then-else)
  have h_val_nat : _root_.Nat.add (Decimal.toCardinalList (Decimal.subtractAlignedLists a b).1)
      (Decimal.toCardinalList b) =
      _root_.Nat.add (Decimal.toCardinalList a)
        (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList a)) :=
    h_val
  -- Now: result + b = a + pow, result < pow, b ≤ a
  -- result < pow ≤ a + pow - b ≤ a + pow (not quite)
  -- a + pow = result + b ≥ result + 0 = result, but need contradiction
  -- From result + b = a + pow and result < pow:
  -- a + pow = result + b < pow + b ≤ pow + a (since b ≤ a)
  -- So a + pow < pow + a = a + pow, contradiction!
  have h_lt1 : _root_.Nat.lt
      (_root_.Nat.add (Decimal.toCardinalList (Decimal.subtractAlignedLists a b).1)
        (Decimal.toCardinalList b))
      (_root_.Nat.add (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList a))
        (Decimal.toCardinalList b)) :=
    Nat.add_lt_add_right h_res_lt_nat _
  have h_rhs_le : _root_.Nat.add (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList a))
        (Decimal.toCardinalList b) ≤
      _root_.Nat.add (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList a))
        (Decimal.toCardinalList a) :=
    Nat.add_le_add_left hge_nat _
  have h_lt2 : _root_.Nat.lt
      (_root_.Nat.add (Decimal.toCardinalList (Decimal.subtractAlignedLists a b).1)
        (Decimal.toCardinalList b))
      (_root_.Nat.add (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList a))
        (Decimal.toCardinalList a)) :=
    Nat.lt_of_lt_of_le h_lt1 h_rhs_le
  rw [h_val_nat] at h_lt2
  -- h_lt2 : Nat.add (toCardinalList a) (pow ten len) < Nat.add (pow ten len) (toCardinalList a)
  -- But Nat.add a b = Nat.add b a (comm), so both sides are equal, contradiction
  have h_comm : _root_.Nat.add (Decimal.toCardinalList a)
        (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList a)) =
      _root_.Nat.add (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList a))
        (Decimal.toCardinalList a) := Nat.add_comm _ _
  rw [h_comm] at h_lt2
  exact Nat.lt_irrefl _ h_lt2

theorem Decimal.OrdinalPeano_lt_toNat {a b : OrdinalNatural.Peano} (h : a < b) : a.toNat < b.toNat := by
  induction h with
  | base => simp [OrdinalNatural.Peano.toNat]
  | step _ ih => simp [OrdinalNatural.Peano.toNat]; omega

theorem Decimal.lt_toCardinalList_lt (a b : Decimal) (h : a < b) :
    Decimal.toCardinalList a.val < Decimal.toCardinalList b.val := by
  have h_peano : a.toPeano < b.toPeano := h
  have h_toNat := Decimal.OrdinalPeano_lt_toNat h_peano
  rw [Decimal.toPeano_toNat, Decimal.toPeano_toNat] at h_toNat
  exact Decimal.cardinalLt_of_natLt h_toNat

/-- Returns true if all-less-than-ten holds, for a list known to have AllLessThanTen but possibly b list. -/
theorem Decimal.allLessThanTen_of_allLessThanTenBool_true (l : ZeroMath.Sequences.List CardinalNatural.Peano)
    (h : Decimal.allLessThanTenBool l = true) : CardinalNatural.Peano.AllLessThanTen l :=
  Decimal.allLessThanTenBool_sound l h

/-- Subtracts b from a assuming a > b; pads b to the same length as a first. -/
def Decimal.subtractHelper (a b : ZeroMath.Sequences.List CardinalNatural.Peano) :
    ZeroMath.Sequences.List CardinalNatural.Peano :=
  (Decimal.subtractAlignedLists a
    (Decimal.leftPadZeros (_root_.Nat.sub (Decimal.lengthList a) (Decimal.lengthList b)) b)).1

theorem Decimal.subtractHelper_allLessThanTenBool
    (a b : ZeroMath.Sequences.List CardinalNatural.Peano)
    (ha : Decimal.allLessThanTenBool a = true) (hb : Decimal.allLessThanTenBool b = true) :
    Decimal.allLessThanTenBool (Decimal.subtractHelper a b) = true := by
  unfold Decimal.subtractHelper
  apply Decimal.subtractAlignedLists_allLessThanTenBool
  · exact ha
  · exact Decimal.leftPadZeros_allLessThanTenBool _ b hb

theorem Decimal.subtractHelper_toCardinalList
    (a b : ZeroMath.Sequences.List CardinalNatural.Peano)
    (ha : CardinalNatural.Peano.AllLessThanTen a)
    (hb : CardinalNatural.Peano.AllLessThanTen b)
    (hge : Decimal.toCardinalList a ≥ Decimal.toCardinalList b)
    (hlen_ge : Decimal.lengthList a ≥ Decimal.lengthList b) :
    _root_.Nat.add (Decimal.toCardinalList (Decimal.subtractHelper a b)) (Decimal.toCardinalList b) =
    Decimal.toCardinalList a := by
  unfold Decimal.subtractHelper
  -- Convert hlen_ge from Peano ≥ to Nat ≤ for arithmetic
  have hlen_nat : _root_.Nat.le (Decimal.lengthList b) (Decimal.lengthList a) := by
    cases hlen_ge with
    | inl hlt => exact Nat.le_of_lt (Decimal.natLt_of_cardinalLt hlt)
    | inr heq => exact Nat.le_of_eq heq
  have hpad_len : Decimal.lengthList (Decimal.leftPadZeros
      (_root_.Nat.sub (Decimal.lengthList a) (Decimal.lengthList b)) b) = Decimal.lengthList a := by
    rw [Decimal.leftPadZeros_length]
    exact Nat.sub_add_cancel hlen_nat
  have hpad_val : Decimal.toCardinalList (Decimal.leftPadZeros
      (_root_.Nat.sub (Decimal.lengthList a) (Decimal.lengthList b)) b) =
      Decimal.toCardinalList b :=
    Decimal.leftPadZeros_toCardinalList _ b
  have hpad_alllt : CardinalNatural.Peano.AllLessThanTen
      (Decimal.leftPadZeros (_root_.Nat.sub (Decimal.lengthList a) (Decimal.lengthList b)) b) :=
    Decimal.allLessThanTenBool_sound _
      (Decimal.leftPadZeros_allLessThanTenBool _ b (Decimal.allLessThanTenBool_complete b hb))
  have h_val := Decimal.subtractAlignedLists_toCardinalList a
    (Decimal.leftPadZeros (_root_.Nat.sub (Decimal.lengthList a) (Decimal.lengthList b)) b)
    hpad_len.symm hpad_alllt
  rw [hpad_val] at h_val
  have h_no_borrow := Decimal.subtractAlignedLists_noBorrow a
    (Decimal.leftPadZeros (_root_.Nat.sub (Decimal.lengthList a) (Decimal.lengthList b)) b)
    hpad_len.symm ha hpad_alllt (by rwa [hpad_val])
  rw [h_no_borrow] at h_val
  simpa [CardinalNatural.Peano.zero] using h_val

theorem Decimal.lengthList_le_of_toCardinalList_le
    (a b : ZeroMath.Sequences.List CardinalNatural.Peano)
    (ha : CardinalNatural.Peano.AllLessThanTen a)
    (hb : CardinalNatural.Peano.AllLessThanTen b)
    (ha_nz : CardinalNatural.Peano.HasNonZero a)
    (hb_nz : CardinalNatural.Peano.HasNonZero b)
    (hb_head : ∃ d ds, b = _root_.List.cons d ds ∧ d ≠ CardinalNatural.Peano.zero)
    (hle : Decimal.toCardinalList b < Decimal.toCardinalList a) :
    Decimal.lengthList b ≤ Decimal.lengthList a := by
  apply Classical.byContradiction
  intro h_gt
  -- h_gt : ¬ (Decimal.lengthList b ≤ Decimal.lengthList a)
  -- Convert to Nat: ¬ Nat.le (lengthList b) (lengthList a)
  have h_nat_not_le : ¬ _root_.Nat.le (Decimal.lengthList b) (Decimal.lengthList a) := by
    intro hle'
    apply h_gt
    cases Nat.eq_or_lt_of_le hle' with
    | inl heq => exact Or.inr heq
    | inr hlt => exact Or.inl (Decimal.cardinalLt_of_natLt hlt)
  have hb_len_gt_nat : _root_.Nat.lt (Decimal.lengthList a) (Decimal.lengthList b) :=
    Nat.lt_of_not_le h_nat_not_le
  have ha_val_lt := Decimal.toCardinalList_lt_pow10 a ha
  have ha_val_lt_nat : _root_.Nat.lt (Decimal.toCardinalList a)
      (_root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList a)) :=
    Decimal.natLt_of_cardinalLt ha_val_lt
  have hpow_le : _root_.Nat.pow CardinalNatural.Peano.ten (Decimal.lengthList a) ≤
      _root_.Nat.pow CardinalNatural.Peano.ten (_root_.Nat.pred (Decimal.lengthList b)) := by
    apply Nat.pow_le_pow_right
    · unfold CardinalNatural.Peano.ten; decide
    · exact Nat.le_pred_of_lt hb_len_gt_nat
  -- Use hb_head to get: pow 10 (pred (lengthList b)) ≤ toCardinalList b
  have hb_ge_nat : _root_.Nat.le
      (_root_.Nat.pow CardinalNatural.Peano.ten (_root_.Nat.pred (Decimal.lengthList b)))
      (Decimal.toCardinalList b) := by
    obtain ⟨d, ds, hb_eq, hd_ne⟩ := hb_head
    rw [hb_eq]
    -- Now b = d :: ds with d ≠ 0, use pow_pred_length_le_toCardinalList
    exact Decimal.pow_pred_length_le_toCardinalList (d :: ds) hd_ne
  -- Contradiction: toCardinalList b < toCardinalList a < pow 10 lenA ≤ pow 10 (pred lenB) ≤ toCardinalList b
  have hle_nat : _root_.Nat.lt (Decimal.toCardinalList b) (Decimal.toCardinalList a) :=
    Decimal.natLt_of_cardinalLt hle
  exact Nat.lt_irrefl (Decimal.toCardinalList b)
    (Nat.lt_of_lt_of_le hle_nat
      (Nat.le_trans (Nat.le_of_lt ha_val_lt_nat)
        (Nat.le_trans hpow_le hb_ge_nat)))

theorem Decimal.subtract_hasNonZero (a b : Decimal) (h : b < a) :
    Decimal.hasNonZeroBool (Decimal.subtractHelper a.val b.normalize.val) = true := by
  apply Classical.byContradiction
  intro h_false
  have h_zero : Decimal.hasNonZeroBool (Decimal.subtractHelper a.val b.normalize.val) = false := by
    have h_ne : Decimal.hasNonZeroBool (Decimal.subtractHelper a.val b.normalize.val) ≠ true := h_false
    cases hb2 : Decimal.hasNonZeroBool (Decimal.subtractHelper a.val b.normalize.val) with
    | false => rfl
    | true => exact absurd hb2 h_ne
  have h_val_zero := Decimal.toCardinalList_eq_zero_of_hasNonZeroBool_false _ h_zero
  have h_lt := Decimal.lt_toCardinalList_lt b a h
  have h_lt_nat : _root_.Nat.lt (Decimal.toCardinalList b.val) (Decimal.toCardinalList a.val) :=
    Decimal.natLt_of_cardinalLt h_lt
  -- Use normalized b: toCardinalList b.normalize.val = toCardinalList b.val
  have hb_norm_val : Decimal.toCardinalList b.normalize.val = Decimal.toCardinalList b.val :=
    Decimal.normalize_toCardinalList b
  have h_lt_norm : Decimal.toCardinalList b.normalize.val < Decimal.toCardinalList a.val := by
    rw [hb_norm_val]; exact h_lt
  have h_lt_norm_nat : _root_.Nat.lt (Decimal.toCardinalList b.normalize.val) (Decimal.toCardinalList a.val) :=
    Decimal.natLt_of_cardinalLt h_lt_norm
  have hb_norm_head : ∃ d ds, b.normalize.val = _root_.List.cons d ds ∧
      d ≠ CardinalNatural.Peano.zero := by
    have h_match := Decimal.isNormalized_head_ne_zero b.normalize (Decimal.normalize_isNormalized b)
    cases hv : b.normalize.val with
    | nil => simp only [hv] at h_match
    | cons d ds =>
      simp only [hv] at h_match
      exact ⟨d, ds, rfl, h_match⟩
  have hlen_ge := Decimal.lengthList_le_of_toCardinalList_le a.val b.normalize.val a.property.left
    b.normalize.property.left a.property.right b.normalize.property.right hb_norm_head h_lt_norm
  -- hlen_ge : Decimal.lengthList b.normalize.val ≤ Decimal.lengthList a.val (Peano LE)
  -- Need Peano GE for subtractHelper_toCardinalList: lengthList a ≥ lengthList b.normalize
  have hlen_ge_rev : Decimal.lengthList a.val ≥ Decimal.lengthList b.normalize.val := by
    cases hlen_ge with
    | inl hlt => exact Or.inl (Decimal.cardinalLt_of_natLt (Decimal.natLt_of_cardinalLt hlt))
    | inr heq => exact Or.inr heq
  have h_sum := Decimal.subtractHelper_toCardinalList a.val b.normalize.val a.property.left b.normalize.property.left
    (Or.inl h_lt_norm) hlen_ge_rev
  rw [h_val_zero, hb_norm_val] at h_sum
  -- h_sum : Nat.add CardinalNatural.Peano.zero (toCardinalList b.val) = toCardinalList a.val
  have h_eq : Decimal.toCardinalList b.val = Decimal.toCardinalList a.val := by
    simpa [CardinalNatural.Peano.zero] using h_sum
  exact Nat.lt_irrefl (Decimal.toCardinalList b.val) (h_eq ▸ h_lt_nat)

/-- Subtracts b from a given a proof that b < a, using columnar subtraction. -/
def Decimal.subtract (a b : Decimal) (h : b < a) : Decimal :=
  let digits := Decimal.subtractHelper a.val b.normalize.val
  ⟨digits, ⟨
    Decimal.allLessThanTenBool_sound digits (by
      unfold digits
      apply Decimal.subtractHelper_allLessThanTenBool
      · exact Decimal.allLessThanTenBool_complete a.val a.property.left
      · exact Decimal.allLessThanTenBool_complete b.normalize.val b.normalize.property.left),
    Decimal.hasNonZeroBool_sound digits (by
      unfold digits
      exact Decimal.subtract_hasNonZero a b h)⟩⟩

theorem Decimal.subtract_toCardinalList (a b : Decimal) (h : b < a) :
    _root_.Nat.add (Decimal.toCardinalList (Decimal.subtract a b h).val) (Decimal.toCardinalList b.val) =
    Decimal.toCardinalList a.val := by
  unfold Decimal.subtract
  dsimp only
  have h_lt := Decimal.lt_toCardinalList_lt b a h
  have h_lt_nat : _root_.Nat.lt (Decimal.toCardinalList b.val) (Decimal.toCardinalList a.val) :=
    Decimal.natLt_of_cardinalLt h_lt
  -- Use normalized b: toCardinalList b.normalize.val = toCardinalList b.val
  have hb_norm_val : Decimal.toCardinalList b.normalize.val = Decimal.toCardinalList b.val :=
    Decimal.normalize_toCardinalList b
  have h_lt_norm : Decimal.toCardinalList b.normalize.val < Decimal.toCardinalList a.val := by
    rw [hb_norm_val]; exact h_lt
  have hb_norm_head : ∃ d ds, b.normalize.val = _root_.List.cons d ds ∧
      d ≠ CardinalNatural.Peano.zero := by
    have h_match := Decimal.isNormalized_head_ne_zero b.normalize (Decimal.normalize_isNormalized b)
    cases hv : b.normalize.val with
    | nil => simp only [hv] at h_match
    | cons d ds =>
      simp only [hv] at h_match
      exact ⟨d, ds, rfl, h_match⟩
  have hlen_ge := Decimal.lengthList_le_of_toCardinalList_le a.val b.normalize.val a.property.left
    b.normalize.property.left a.property.right b.normalize.property.right hb_norm_head h_lt_norm
  -- Convert hlen_ge from Peano LE to Peano GE (reversed)
  have hlen_ge_rev : Decimal.lengthList a.val ≥ Decimal.lengthList b.normalize.val := by
    cases hlen_ge with
    | inl hlt => exact Or.inl (Decimal.cardinalLt_of_natLt (Decimal.natLt_of_cardinalLt hlt))
    | inr heq => exact Or.inr heq
  have h_result := Decimal.subtractHelper_toCardinalList a.val b.normalize.val a.property.left b.normalize.property.left
    (Or.inl h_lt_norm) hlen_ge_rev
  rw [hb_norm_val] at h_result
  exact h_result

end ZeroMath.Numbers.OrdinalNatural
