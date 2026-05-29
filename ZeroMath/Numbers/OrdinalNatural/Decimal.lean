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

def hasNonZeroBool : Sequences.List CardinalNatural.Peano → Bool
  | .empty => false
  | .firstElement d ds => if d = CardinalNatural.Peano.zero then hasNonZeroBool ds else true

theorem hasNonZeroBool_true_implies_hasNonZero {l : Sequences.List CardinalNatural.Peano}
  (h : hasNonZeroBool l = true) : HasNonZero l := by
  induction l with
  | empty =>
    unfold hasNonZeroBool at h
    contradiction
  | firstElement d ds ih =>
    unfold hasNonZeroBool at h
    unfold HasNonZero
    by_cases h_zero : d = CardinalNatural.Peano.zero
    · rw [if_pos h_zero] at h
      right
      exact ih h
    · left
      exact h_zero

end Decimal

def Decimal := { l : Sequences.List CardinalNatural.Peano // Decimal.AllLessThanTen l ∧ Decimal.HasNonZero l }

namespace Decimal

def isNormalized (d : Decimal) : Bool :=
  match d.val with
  | .empty => false
  | .firstElement digit _ => decide (digit ≠ CardinalNatural.Peano.zero)

def normalizeList : Sequences.List CardinalNatural.Peano → Sequences.List CardinalNatural.Peano
  | .empty => Sequences.List.empty
  | .firstElement d ds =>
    if d = CardinalNatural.Peano.zero then
      Decimal.normalizeList ds
    else
      Sequences.List.firstElement d ds

theorem normalizeList_allLessThanTen (l : Sequences.List CardinalNatural.Peano)
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

theorem normalizeList_hasNonZero (l : Sequences.List CardinalNatural.Peano)
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

theorem normalizeList_startsNonZero (l : Sequences.List CardinalNatural.Peano)
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

def toCardinalHelper : Sequences.List CardinalNatural.Peano → CardinalNatural.Peano → CardinalNatural.Peano
  | .empty, acc => acc
  | .firstElement d ds, acc => toCardinalHelper ds (acc * CardinalNatural.Peano.ten + d)

def toCardinalList (l : Sequences.List CardinalNatural.Peano) : CardinalNatural.Peano :=
  toCardinalHelper l CardinalNatural.Peano.zero

theorem toCardinalHelper_ne_zero (l : Sequences.List CardinalNatural.Peano) (acc : CardinalNatural.Peano)
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

theorem normalizeList_toCardinalList (l : Sequences.List CardinalNatural.Peano) :
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

def addOneBigEndian : Sequences.List CardinalNatural.Peano → Sequences.List CardinalNatural.Peano × Bool
  | .empty => (Sequences.List.empty, true)
  | .firstElement d ds =>
    let (ds', carry) := Decimal.addOneBigEndian ds
    if carry then
      if d.successor = CardinalNatural.Peano.ten then
        (Sequences.List.firstElement CardinalNatural.Peano.zero ds', true)
      else
        (Sequences.List.firstElement d.successor ds', false)
    else
      (Sequences.List.firstElement d ds', false)

def successorHelper (l : Sequences.List CardinalNatural.Peano) : Sequences.List CardinalNatural.Peano :=
  let (l', carry) := addOneBigEndian l
  if carry then
    Sequences.List.firstElement CardinalNatural.Peano.one l'
  else
    l'

theorem addOneBigEndian_allLessThanTen (l : Sequences.List CardinalNatural.Peano) (h : AllLessThanTen l) :
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

theorem addOneBigEndian_hasNonZero (l : Sequences.List CardinalNatural.Peano)
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

theorem successorHelper_hasNonZero (l : Sequences.List CardinalNatural.Peano)
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

theorem successorHelper_allLessThanTen (l : Sequences.List CardinalNatural.Peano)
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

theorem addOneBigEndian_toCardinalHelper (l : Sequences.List CardinalNatural.Peano)
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

theorem successorHelper_toCardinalList (l : Sequences.List CardinalNatural.Peano)
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
  ⟨Sequences.List.firstElement CardinalNatural.Peano.one Sequences.List.empty, ⟨by
    unfold AllLessThanTen
    constructor
    · exact CardinalNatural.Peano.LessThan.step (CardinalNatural.Peano.LessThan.step (CardinalNatural.Peano.LessThan.step
        (CardinalNatural.Peano.LessThan.step (CardinalNatural.Peano.LessThan.step (CardinalNatural.Peano.LessThan.step (CardinalNatural.Peano.LessThan.step
          (CardinalNatural.Peano.LessThan.step (CardinalNatural.Peano.LessThan.base))))))))
    · exact trivial
  , by
    unfold HasNonZero
    left
    intro contra
    cases contra
  ⟩⟩

theorem padAtStart_allLessThanTen (l : Sequences.List CardinalNatural.Peano) (h : AllLessThanTen l) (paddingValue : CardinalNatural.Peano)
  (h_pad : paddingValue < CardinalNatural.Peano.ten) (n : CardinalNatural.Peano) :
  AllLessThanTen (Sequences.List.padAtStart l paddingValue n) := by
  induction n generalizing l with
  | zero => exact h
  | successor n' ih =>
    unfold Sequences.List.padAtStart
    apply ih
    unfold AllLessThanTen
    constructor
    · exact h_pad
    · exact h

theorem padAtStart_hasNonZero (l : Sequences.List CardinalNatural.Peano) (h : HasNonZero l) (paddingValue : CardinalNatural.Peano) (n : CardinalNatural.Peano) :
  HasNonZero (Sequences.List.padAtStart l paddingValue n) := by
  induction n generalizing l with
  | zero => exact h
  | successor n' ih =>
    unfold Sequences.List.padAtStart
    apply ih
    unfold HasNonZero
    right
    exact h

def addAlignedLists (a b : Sequences.List CardinalNatural.Peano) : Sequences.List CardinalNatural.Peano × Bool :=
  match a, b with
  | .empty, .empty => (Sequences.List.empty, false)
  | .firstElement da das, .firstElement db dbs =>
    let (ds_sum, carry) := addAlignedLists das dbs
    let digit_sum := da + db + (if carry then CardinalNatural.Peano.one else CardinalNatural.Peano.zero)
    match h_less : CardinalNatural.Peano.isLessThan digit_sum CardinalNatural.Peano.ten with
    | true =>
      (Sequences.List.firstElement digit_sum ds_sum, false)
    | false =>
      have h_le : CardinalNatural.Peano.ten ≤ digit_sum := CardinalNatural.Peano.isLessThan_false_implies_le h_less
      (Sequences.List.firstElement (CardinalNatural.Peano.subtract digit_sum CardinalNatural.Peano.ten h_le) ds_sum, true)
  | _, _ => (Sequences.List.empty, false) -- This case should not occur if lists are properly padded

def addToList (a b : Sequences.List CardinalNatural.Peano) : Sequences.List CardinalNatural.Peano :=
  let (a', b') := Sequences.List.padAtStartToSameLength a b CardinalNatural.Peano.zero
  let (sum, carry) := addAlignedLists a' b'
  if carry then
    Sequences.List.firstElement CardinalNatural.Peano.one sum
  else
    sum

theorem digit_sum_lt_twenty (da db : CardinalNatural.Peano) (carry : Bool)
  (hda : da < CardinalNatural.Peano.ten) (hdb : db < CardinalNatural.Peano.ten) :
  da + db + (if carry then CardinalNatural.Peano.one else CardinalNatural.Peano.zero) <
    CardinalNatural.Peano.ten + CardinalNatural.Peano.ten := by
  cases carry with
  | false =>
    simp
    exact CardinalNatural.Peano.lt_trans (CardinalNatural.Peano.add_lt_add_right hda db) (CardinalNatural.Peano.add_lt_add_left hdb CardinalNatural.Peano.ten)
  | true =>
    have h_da_succ_le : da + CardinalNatural.Peano.one ≤ CardinalNatural.Peano.ten := by
      change da.successor ≤ CardinalNatural.Peano.ten
      exact CardinalNatural.Peano.succ_le_of_lt hda
    have h_sum_le : (da + CardinalNatural.Peano.one) + db ≤ CardinalNatural.Peano.ten + db :=
      CardinalNatural.Peano.add_le_add_right h_da_succ_le db
    have h_ten_db_lt : CardinalNatural.Peano.ten + db < CardinalNatural.Peano.ten + CardinalNatural.Peano.ten :=
      CardinalNatural.Peano.add_lt_add_left hdb CardinalNatural.Peano.ten
    simp
    rw [CardinalNatural.Peano.add_associative da db CardinalNatural.Peano.one]
    rw [CardinalNatural.Peano.add_commutative db CardinalNatural.Peano.one]
    rw [← CardinalNatural.Peano.add_associative da CardinalNatural.Peano.one db]
    exact CardinalNatural.Peano.le_lt_trans h_sum_le h_ten_db_lt

  theorem subtract_ten_lt_ten (digit_sum : CardinalNatural.Peano)
  (h_le : CardinalNatural.Peano.ten ≤ digit_sum)
  (h_lt_twenty : digit_sum < CardinalNatural.Peano.ten + CardinalNatural.Peano.ten) :
  CardinalNatural.Peano.subtract digit_sum CardinalNatural.Peano.ten h_le < CardinalNatural.Peano.ten := by
  exact CardinalNatural.Peano.subtract_lt_of_lt_add h_le h_lt_twenty

theorem addAlignedLists_allLessThanTen (a b : Sequences.List CardinalNatural.Peano)
  (ha : AllLessThanTen a) (hb : AllLessThanTen b) :
  AllLessThanTen (addAlignedLists a b).1 := by
  induction a generalizing b with
  | empty =>
    cases b with
    | empty =>
      unfold addAlignedLists
      unfold AllLessThanTen
      exact trivial
    | firstElement _ _ =>
      unfold addAlignedLists
      unfold AllLessThanTen
      exact trivial
  | firstElement da das ih =>
    cases b with
    | empty =>
      unfold addAlignedLists
      unfold AllLessThanTen
      exact trivial
    | firstElement db dbs =>
      unfold addAlignedLists
      unfold AllLessThanTen at ha hb
      have h_tail := ih dbs ha.right hb.right
      generalize h_add : addAlignedLists das dbs = res
      rw [h_add] at h_tail
      cases res with
      | mk ds_sum carry =>
        dsimp only
        have h_digit_twenty := digit_sum_lt_twenty da db carry ha.left hb.left
        split
        · next h_less =>
          unfold AllLessThanTen
          constructor
          · exact (CardinalNatural.Peano.isLessThan_eq_true_iff_lt _ _).mp h_less
          · exact h_tail
        · next h_less =>
          unfold AllLessThanTen
          constructor
          · have h_le : CardinalNatural.Peano.ten ≤ da + db + (if carry then CardinalNatural.Peano.one else CardinalNatural.Peano.zero) :=
              CardinalNatural.Peano.isLessThan_false_implies_le h_less
            exact subtract_ten_lt_ten (da + db + (if carry then CardinalNatural.Peano.one else CardinalNatural.Peano.zero)) h_le h_digit_twenty
          · exact h_tail

theorem addAlignedLists_hasNonZero_or_carry (a b : Sequences.List CardinalNatural.Peano)
  (h_shape : Sequences.List.SameLength a b) (h_nz : HasNonZero a) :
  HasNonZero (addAlignedLists a b).1 ∨ (addAlignedLists a b).2 = true := by
  induction h_shape with
  | empty =>
    unfold HasNonZero at h_nz
    cases h_nz
  | firstElement h_tail ih =>
    unfold addAlignedLists
    generalize h_add : addAlignedLists _ _ = res
    cases res with
    | mk ds_sum carry =>
      dsimp only
      split
      · next _ =>
        unfold HasNonZero at h_nz
        cases h_nz with
        | inl h_da =>
          left
          unfold HasNonZero
          left
          exact CardinalNatural.Peano.add_ne_zero_of_left_ne_zero _ _
            (CardinalNatural.Peano.add_ne_zero_of_left_ne_zero _ _ h_da)
        | inr h_das =>
          have ih_app := ih h_das
          rw [h_add] at ih_app
          dsimp only at ih_app
          cases ih_app with
          | inl h_sum =>
            left
            unfold HasNonZero
            right
            exact h_sum
          | inr h_carry =>
            left
            unfold HasNonZero
            left
            rw [h_carry]
            exact CardinalNatural.Peano.add_ne_zero_of_right_ne_zero _ _
              (CardinalNatural.Peano.successor_ne_zero CardinalNatural.Peano.zero)
      · next _ =>
        right
        rfl

theorem addAlignedLists_hasNonZero (a b : Sequences.List CardinalNatural.Peano)
  (h_shape : Sequences.List.SameLength a b) (h_nz : HasNonZero a) :
  HasNonZero (addAlignedLists a b).1 ∨ (addAlignedLists a b).2 = true := by
  exact addAlignedLists_hasNonZero_or_carry a b h_shape h_nz

theorem addToList_allLessThanTen (a b : Sequences.List CardinalNatural.Peano)
  (ha : AllLessThanTen a) (hb : AllLessThanTen b) :
  AllLessThanTen (addToList a b) := by
  unfold addToList
  generalize h_pad : Sequences.List.padAtStartToSameLength a b CardinalNatural.Peano.zero = padded
  cases padded with
  | mk a' b' =>
    have h_pad_props : AllLessThanTen a' ∧ AllLessThanTen b' := by
      unfold Sequences.List.padAtStartToSameLength at h_pad
      dsimp only at h_pad
      split at h_pad
      · cases h_pad
        constructor
        · exact ha
        · apply padAtStart_allLessThanTen
          · exact hb
          · exact CardinalNatural.Peano.zero_lt_ten
      · cases h_pad
        constructor
        · apply padAtStart_allLessThanTen
          · exact ha
          · exact CardinalNatural.Peano.zero_lt_ten
        · exact hb
    have h_sum := addAlignedLists_allLessThanTen a' b' h_pad_props.left h_pad_props.right
    generalize h_add : addAlignedLists a' b' = res
    rw [h_add] at h_sum
    cases res with
    | mk sum carry =>
      dsimp only
      rw [h_add]
      dsimp only
      cases carry with
      | false => exact h_sum
      | true =>
        unfold AllLessThanTen
        constructor
        · exact CardinalNatural.Peano.one_lt_ten
        · exact h_sum

theorem addToList_hasNonZero (a b : Sequences.List CardinalNatural.Peano)
  (_ha : AllLessThanTen a) (_hb : AllLessThanTen b) (h_nz : HasNonZero a) :
  HasNonZero (addToList a b) := by
  unfold addToList
  generalize h_pad : Sequences.List.padAtStartToSameLength a b CardinalNatural.Peano.zero = padded
  cases padded with
  | mk a' b' =>
    have h_shape : Sequences.List.SameLength a' b' := by
      have h_same := Sequences.List.padAtStartToSameLength_sameLength a b CardinalNatural.Peano.zero
      rw [h_pad] at h_same
      exact h_same
    have h_a_nz : HasNonZero a' := by
      unfold Sequences.List.padAtStartToSameLength at h_pad
      dsimp only at h_pad
      split at h_pad
      · cases h_pad
        exact h_nz
      · cases h_pad
        exact padAtStart_hasNonZero a h_nz CardinalNatural.Peano.zero _
    have h_sum_or_carry := addAlignedLists_hasNonZero a' b' h_shape h_a_nz
    generalize h_add : addAlignedLists a' b' = res
    rw [h_add] at h_sum_or_carry
    cases res with
    | mk sum carry =>
      dsimp only at h_sum_or_carry ⊢
      rw [h_add]
      dsimp only
      cases carry with
      | false =>
        cases h_sum_or_carry with
        | inl h_sum => exact h_sum
        | inr h_false => contradiction
      | true =>
        unfold HasNonZero
        left
        exact CardinalNatural.Peano.successor_ne_zero CardinalNatural.Peano.zero

def add (a b : Decimal) : Decimal :=
  ⟨addToList a.val b.val, ⟨by
    unfold addToList
    apply addToList_allLessThanTen
    · exact a.property.left
    · exact b.property.left
  , by
    unfold addToList
    apply addToList_hasNonZero
    · exact a.property.left
    · exact b.property.left
    · exact a.property.right
  ⟩⟩

instance : Add Decimal where
  add := add

end Decimal

end ZeroMath.Numbers.OrdinalNatural
