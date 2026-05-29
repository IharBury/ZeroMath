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

theorem normalize_toPeano (x : Decimal) : x.normalize.toPeano = x.toPeano := by
  unfold toPeano
  apply CardinalNatural.Peano.toOrdinal_congr
  exact normalize_toCardinalList x

def addOneBigEndian : ZeroMath.Sequences.List CardinalNatural.Peano → ZeroMath.Sequences.List CardinalNatural.Peano × Bool
  | .empty => (ZeroMath.Sequences.List.empty, true)
  | .firstElement d ds =>
    let (ds', carry) := Decimal.addOneBigEndian ds
    if carry then
      if CardinalNatural.Peano.successor d = CardinalNatural.Peano.ten then
        (ZeroMath.Sequences.List.firstElement CardinalNatural.Peano.zero ds', true)
      else
        (ZeroMath.Sequences.List.firstElement (CardinalNatural.Peano.successor d) ds', false)
    else
      (ZeroMath.Sequences.List.firstElement d ds', false)

def successorHelper (l : ZeroMath.Sequences.List CardinalNatural.Peano) : ZeroMath.Sequences.List CardinalNatural.Peano :=
  let (l', carry) := addOneBigEndian l
  if carry then
    ZeroMath.Sequences.List.firstElement (CardinalNatural.Peano.successor CardinalNatural.Peano.zero) l'
  else
    l'

theorem addOneBigEndian_allLessThanTen (l : ZeroMath.Sequences.List CardinalNatural.Peano) (h : AllLessThanTen l) :
  AllLessThanTen (Decimal.addOneBigEndian l).1 := by
  induction l with
  | empty =>
    unfold addOneBigEndian
    unfold AllLessThanTen
    exact trivial
  | firstElement d ds ih =>
    unfold addOneBigEndian
    have h_ih : AllLessThanTen (addOneBigEndian ds).1 := by
      apply ih
      unfold AllLessThanTen at h
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
          unfold AllLessThanTen
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
          unfold AllLessThanTen
          constructor
          · unfold AllLessThanTen at h
            have hd_lt : d < CardinalNatural.Peano.ten := h.left
            have hd_succ_le : CardinalNatural.Peano.successor d ≤ CardinalNatural.Peano.ten := CardinalNatural.Peano.succ_le_of_lt hd_lt
            cases hd_succ_le with
            | inl hlt => exact hlt
            | inr heq => contradiction
          · exact h_ih
      · next h_no_carry =>
        unfold AllLessThanTen
        constructor
        · unfold AllLessThanTen at h
          exact h.left
        · exact h_ih

theorem addOneBigEndian_hasNonZero (l : ZeroMath.Sequences.List CardinalNatural.Peano)
  (h_nz : HasNonZero l) :
  HasNonZero (addOneBigEndian l).1 ∨ (addOneBigEndian l).2 = true := by
  induction l with
  | empty =>
    unfold HasNonZero at h_nz
    cases h_nz
  | firstElement d ds ih =>
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
          unfold HasNonZero
          left
          exact CardinalNatural.Peano.successor_ne_zero d
      · next h_no_carry =>
        unfold HasNonZero at h_nz
        cases h_nz with
        | inl h_d =>
          left
          unfold HasNonZero
          left
          exact h_d
        | inr h_ds =>
          have ih_app := ih h_ds
          rw [h_add] at ih_app
          dsimp only at ih_app
          cases ih_app with
          | inl h_ds' =>
            left
            unfold HasNonZero
            right
            exact h_ds'
          | inr h_carry_true =>
            rw [h_carry_true] at h_no_carry
            contradiction

theorem successorHelper_hasNonZero (l : ZeroMath.Sequences.List CardinalNatural.Peano)
  (h_nz : HasNonZero l) :
  HasNonZero (successorHelper l) := by
  unfold successorHelper
  generalize h_add : addOneBigEndian l = res
  cases res with
  | mk l' carry =>
    dsimp only
    split
    · next h_carry =>
      unfold HasNonZero
      left
      exact CardinalNatural.Peano.successor_ne_zero CardinalNatural.Peano.zero
    · next h_no_carry =>
      have h_prop := Decimal.addOneBigEndian_hasNonZero l h_nz
      rw [h_add] at h_prop
      dsimp only at h_prop
      cases h_prop with
      | inl h1 => exact h1
      | inr h2 =>
        rw [h2] at h_no_carry
        contradiction

theorem successorHelper_allLessThanTen (l : ZeroMath.Sequences.List CardinalNatural.Peano)
  (h : AllLessThanTen l) :
  AllLessThanTen (successorHelper l) := by
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
      unfold AllLessThanTen
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

theorem addOneBigEndian_toCardinalHelper (l : ZeroMath.Sequences.List CardinalNatural.Peano)
  (h : AllLessThanTen l) (acc : CardinalNatural.Peano) :
  Decimal.toCardinalHelper (Decimal.addOneBigEndian l).1
      (if (Decimal.addOneBigEndian l).2 then acc + CardinalNatural.Peano.successor CardinalNatural.Peano.zero else acc) =
    Decimal.toCardinalHelper l acc + CardinalNatural.Peano.successor CardinalNatural.Peano.zero := by
  induction l generalizing acc with
  | empty =>
    unfold Decimal.addOneBigEndian
    unfold Decimal.toCardinalHelper
    rfl
  | firstElement d ds ih =>
    have h_tail : AllLessThanTen ds := by
      unfold AllLessThanTen at h
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
            rw [CardinalNatural.Peano.successor_multiply]
            rw [← h_eq]
            rfl
          change Decimal.toCardinalHelper ds' (CardinalNatural.Peano.successor acc * CardinalNatural.Peano.ten + CardinalNatural.Peano.zero) =
            Decimal.toCardinalHelper ds' (acc * CardinalNatural.Peano.ten + d + CardinalNatural.Peano.successor CardinalNatural.Peano.zero)
          rw [h_arg]
        · simp [h_eq]
          rw [← ih_acc]
          rfl

theorem successorHelper_toCardinalList (l : ZeroMath.Sequences.List CardinalNatural.Peano)
  (h : AllLessThanTen l) :
  toCardinalList (successorHelper l) =
    toCardinalList l + CardinalNatural.Peano.successor CardinalNatural.Peano.zero := by
  unfold successorHelper
  unfold toCardinalList
  have h_add := addOneBigEndian_toCardinalHelper l h CardinalNatural.Peano.zero
  generalize h_eq : addOneBigEndian l = res
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

def successor (d : Decimal) : Decimal :=
  ⟨successorHelper d.val, ⟨successorHelper_allLessThanTen d.val d.property.left, successorHelper_hasNonZero d.val d.property.right⟩⟩

theorem successor_toCardinalList (d : Decimal) :
  toCardinalList (successor d).val =
    toCardinalList d.val + CardinalNatural.Peano.successor CardinalNatural.Peano.zero := by
  unfold successor
  dsimp only
  exact successorHelper_toCardinalList d.val d.property.left

def one : Decimal :=
  ⟨ZeroMath.Sequences.List.firstElement (CardinalNatural.Peano.successor CardinalNatural.Peano.zero) ZeroMath.Sequences.List.empty, ⟨by
    unfold AllLessThanTen
    constructor
    · exact CardinalNatural.Peano.LessThan.step (CardinalNatural.Peano.LessThan.step (CardinalNatural.Peano.LessThan.step (CardinalNatural.Peano.LessThan.step (CardinalNatural.Peano.LessThan.step (CardinalNatural.Peano.LessThan.step (CardinalNatural.Peano.LessThan.step (CardinalNatural.Peano.LessThan.step (CardinalNatural.Peano.LessThan.base))))))))
    · exact trivial
  , by
    unfold HasNonZero
    left
    intro contra
    cases contra
  ⟩⟩

def padListsHelper (l1 l2 : ZeroMath.Sequences.List CardinalNatural.Peano) :
  (ZeroMath.Sequences.List CardinalNatural.Peano × ZeroMath.Sequences.List CardinalNatural.Peano) :=
  let len1 := l1.length
  let len2 := l2.length
  if CardinalNatural.Peano.isLessThan len2 len1 then
    have h_le : len2 ≤ len1 := sorry
    (l1, ZeroMath.Sequences.List.padAtStart l2 CardinalNatural.Peano.zero (CardinalNatural.Peano.subtract len1 len2 h_le))
  else
    have h_le : len1 ≤ len2 := sorry
    (ZeroMath.Sequences.List.padAtStart l1 CardinalNatural.Peano.zero (CardinalNatural.Peano.subtract len2 len1 h_le), l2)

def addListsHelperBigEndianPadded (l1 l2 : ZeroMath.Sequences.List CardinalNatural.Peano) : ZeroMath.Sequences.List CardinalNatural.Peano × Bool :=
  match l1, l2 with
  | .empty, .empty => (.empty, false)
  | .firstElement d1 ds1, .firstElement d2 ds2 =>
    let (ds', carry) := addListsHelperBigEndianPadded ds1 ds2
    let sum1 := d1 + d2
    let sum2 := if carry then sum1 + CardinalNatural.Peano.successor CardinalNatural.Peano.zero else sum1
    if CardinalNatural.Peano.isLessThan sum2 CardinalNatural.Peano.ten then
      (.firstElement sum2 ds', false)
    else
      have h_le : CardinalNatural.Peano.ten ≤ sum2 := sorry
      (.firstElement (CardinalNatural.Peano.subtract sum2 CardinalNatural.Peano.ten h_le) ds', true)
  | _, _ => (.empty, false)

def addListBigEndian (l1 l2 : ZeroMath.Sequences.List CardinalNatural.Peano) : ZeroMath.Sequences.List CardinalNatural.Peano :=
  let (padded_l1, padded_l2) := padListsHelper l1 l2
  let (res_list, carry) := addListsHelperBigEndianPadded padded_l1 padded_l2
  if carry then
    .firstElement (CardinalNatural.Peano.successor CardinalNatural.Peano.zero) res_list
  else
    res_list

def add (a b : Decimal) : Decimal :=
  let list_res := Decimal.normalizeList (addListBigEndian a.val b.val)
  let h_lt : AllLessThanTen list_res := sorry
  let h_nz : HasNonZero list_res := sorry
  ⟨list_res, ⟨h_lt, h_nz⟩⟩

end Decimal

end ZeroMath.Numbers.OrdinalNatural
