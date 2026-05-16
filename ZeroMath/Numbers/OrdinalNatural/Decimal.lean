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

def Decimal.add (a b : Decimal) : Decimal :=
  let sum := Decimal.alignAndAddLists a.val b.val
  let digits := Decimal.finishColumnarSum sum
  if h_digits : Decimal.allLessThanTenBool digits = true then
    ⟨digits, ⟨Decimal.allLessThanTenBool_sound digits h_digits,
      Decimal.finishColumnarSum_hasNonZero sum (Decimal.alignAndAddLists_hasNonZero_or_carry a.val b.val a.property.right)⟩⟩
  else
    Decimal.one

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

end ZeroMath.Numbers.OrdinalNatural
