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

theorem Equivalent_iff_normalize_eq (a b : Decimal) :
  Equivalent a b ↔ normalize a = normalize b := by
  rfl

theorem equivalent_of_normalize_eq {a b : Decimal}
  (h : normalize a = normalize b) : a ≈ b := by
  exact h

theorem normalize_eq_of_equivalent {a b : Decimal}
  (h : instSetoid.r a b) : normalize a = normalize b := by
  exact h

theorem toPeano_eq_of_equivalent {a b : Decimal} (h : a ≈ b) :
  a.toPeano = b.toPeano := by
  rw [← normalize_toPeano a, ← normalize_toPeano b]
  have h_norm : normalize a = normalize b := h
  rw [h_norm]

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

theorem addAlignedLists_commutative (a b : Sequences.List CardinalNatural.Peano)
  (h_shape : Sequences.List.SameLength a b) :
  addAlignedLists a b = addAlignedLists b a := by
  induction h_shape with
  | empty => rfl
  | firstElement h_tail ih =>
    unfold addAlignedLists
    rw [ih]
    rw [CardinalNatural.Peano.add_commutative]

theorem addToList_commutative (a b : Sequences.List CardinalNatural.Peano) :
  addToList a b = addToList b a := by
  unfold addToList
  rw [Sequences.List.padAtStartToSameLength_commutative a b CardinalNatural.Peano.zero]
  have h_shape := Sequences.List.padAtStartToSameLength_sameLength a b CardinalNatural.Peano.zero
  generalize h_pad : Sequences.List.padAtStartToSameLength a b CardinalNatural.Peano.zero = padded
  rw [h_pad] at h_shape
  cases padded with
  | mk a' b' =>
    dsimp only at h_shape ⊢
    rw [addAlignedLists_commutative a' b' h_shape]

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

def toNatListHelper : Sequences.List CardinalNatural.Peano → Nat → Nat
  | .empty, acc => acc
  | .firstElement d ds, acc => toNatListHelper ds (acc * 10 + d.toNat)

def listLengthNat : Sequences.List CardinalNatural.Peano → Nat
  | .empty => 0
  | .firstElement _ ds => listLengthNat ds + 1

theorem toCardinalHelper_toNat (l : Sequences.List CardinalNatural.Peano)
  (acc : CardinalNatural.Peano) :
  (toCardinalHelper l acc).toNat = toNatListHelper l acc.toNat := by
  induction l generalizing acc with
  | empty => rfl
  | firstElement d ds ih =>
    unfold toCardinalHelper toNatListHelper
    rw [ih]
    rw [CardinalNatural.Peano.add_toNat, CardinalNatural.Peano.multiply_toNat]
    rfl

theorem toCardinalList_toNat (l : Sequences.List CardinalNatural.Peano) :
  (toCardinalList l).toNat = toNatListHelper l 0 := by
  unfold toCardinalList
  rw [toCardinalHelper_toNat]
  rfl

theorem toNatListHelper_add_acc (l : Sequences.List CardinalNatural.Peano)
  (acc extra : Nat) :
  toNatListHelper l (acc + extra) =
    toNatListHelper l acc + extra * 10 ^ listLengthNat l := by
  induction l generalizing acc extra with
  | empty => simp [toNatListHelper, listLengthNat]
  | firstElement d ds ih =>
    unfold toNatListHelper listLengthNat
    have h_arg : (acc + extra) * 10 + d.toNat = (acc * 10 + d.toNat) + extra * 10 := by
      omega
    rw [h_arg]
    rw [ih]
    rw [Nat.pow_succ]
    simp [Nat.mul_assoc, Nat.mul_comm]

theorem padAtStart_zero_toNatListHelper (l : Sequences.List CardinalNatural.Peano)
  (n : CardinalNatural.Peano) :
  toNatListHelper (Sequences.List.padAtStart l CardinalNatural.Peano.zero n) 0 =
    toNatListHelper l 0 := by
  induction n generalizing l with
  | zero => rfl
  | successor n ih =>
    unfold Sequences.List.padAtStart
    rw [ih]
    cases l <;> rfl

theorem padAtStart_zero_toCardinalList (l : Sequences.List CardinalNatural.Peano)
  (n : CardinalNatural.Peano) :
  toCardinalList (Sequences.List.padAtStart l CardinalNatural.Peano.zero n) =
    toCardinalList l := by
  apply CardinalNatural.Peano.eq_of_toNat_eq
  rw [toCardinalList_toNat, toCardinalList_toNat]
  exact padAtStart_zero_toNatListHelper l n

theorem addAlignedLists_length
  {a b : Sequences.List CardinalNatural.Peano}
  (h_shape : Sequences.List.SameLength a b) :
  listLengthNat (addAlignedLists a b).1 = listLengthNat a := by
  induction h_shape with
  | empty => rfl
  | firstElement h_tail ih =>
    unfold addAlignedLists
    generalize h_add : addAlignedLists _ _ = res
    cases res with
    | mk ds_sum carry =>
      dsimp only at ih ⊢
      rw [h_add] at ih
      cases carry <;> split <;> simp [listLengthNat, ih]

theorem addAlignedLists_toNatListHelper
  {a b : Sequences.List CardinalNatural.Peano}
  (h_shape : Sequences.List.SameLength a b) (accA accB : Nat) :
  let res := addAlignedLists a b
  toNatListHelper res.1 (accA + accB) +
      (if res.2 then 10 ^ listLengthNat a else 0) =
    toNatListHelper a accA + toNatListHelper b accB := by
  induction h_shape generalizing accA accB with
  | empty =>
    simp [addAlignedLists, toNatListHelper]
  | firstElement h_tail ih =>
    rename_i da db das dbs
    generalize h_add : addAlignedLists das dbs = tail
    cases tail with
    | mk ds_sum carry =>
      have ih_app := ih (accA * 10 + da.toNat) (accB * 10 + db.toNat)
      rw [h_add] at ih_app
      dsimp only at ih_app
      have h_len : listLengthNat ds_sum = listLengthNat das := by
        have h := addAlignedLists_length h_tail
        rw [h_add] at h
        exact h
      unfold addAlignedLists
      rw [h_add]
      dsimp only
      cases carry with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at ih_app ⊢
        split
        · next _ =>
          simp [toNatListHelper]
          simp at ih_app
          have h_acc : (accA + accB) * 10 + (da.toNat + db.toNat) =
              accA * 10 + da.toNat + (accB * 10 + db.toNat) := by
            omega
          rw [h_acc]
          exact ih_app
        · next h_less =>
          simp [toNatListHelper]
          have h_sub_cancel := CardinalNatural.Peano.subtract_add_cancel
            (da + db + CardinalNatural.Peano.zero) CardinalNatural.Peano.ten
            (CardinalNatural.Peano.isLessThan_false_implies_le h_less)
          have h_sub_nat :
              (CardinalNatural.Peano.subtract (da + db + CardinalNatural.Peano.zero)
                CardinalNatural.Peano.ten
                (CardinalNatural.Peano.isLessThan_false_implies_le h_less)).toNat + 10 =
                da.toNat + db.toNat := by
            have h := congrArg CardinalNatural.Peano.toNat h_sub_cancel
            rw [CardinalNatural.Peano.add_toNat] at h
            rw [CardinalNatural.Peano.add_toNat, CardinalNatural.Peano.add_toNat] at h
            simp at h
            exact h
          simp at ih_app
          rw [← ih_app]
          simp [listLengthNat]
          rw [← h_len]
          let sub := CardinalNatural.Peano.subtract (da + db + CardinalNatural.Peano.zero)
                CardinalNatural.Peano.ten
                (CardinalNatural.Peano.isLessThan_false_implies_le h_less)
          change toNatListHelper ds_sum ((accA + accB) * 10 + sub.toNat) + 10 ^ (listLengthNat ds_sum + 1) =
            toNatListHelper ds_sum (accA * 10 + da.toNat + (accB * 10 + db.toNat))
          rw [Nat.pow_succ]
          rw [Nat.mul_comm (10 ^ listLengthNat ds_sum) 10]
          rw [← toNatListHelper_add_acc ds_sum ((accA + accB) * 10 + sub.toNat) 10]
          have h_sub : sub.toNat + 10 = da.toNat + db.toNat := by
            dsimp [sub]
            exact h_sub_nat
          have h_acc : (accA + accB) * 10 + sub.toNat + 10 =
              accA * 10 + da.toNat + (accB * 10 + db.toNat) := by
            omega
          rw [h_acc]
      | true =>
        simp only [↓reduceIte] at ih_app ⊢
        split
        · next _ =>
          simp [toNatListHelper]
          have h_acc : (accA + accB) * 10 + (da.toNat + db.toNat + CardinalNatural.Peano.one.toNat) =
              (accA * 10 + da.toNat + (accB * 10 + db.toNat)) + 1 := by
            change (accA + accB) * 10 + (da.toNat + db.toNat + 1) =
              (accA * 10 + da.toNat + (accB * 10 + db.toNat)) + 1
            omega
          rw [h_acc]
          rw [toNatListHelper_add_acc ds_sum (accA * 10 + da.toNat + (accB * 10 + db.toNat)) 1]
          simp
          rw [h_len]
          simpa using ih_app
        · next h_less =>
          simp [toNatListHelper]
          have h_sub_cancel := CardinalNatural.Peano.subtract_add_cancel
            (da + db + CardinalNatural.Peano.one) CardinalNatural.Peano.ten
            (CardinalNatural.Peano.isLessThan_false_implies_le h_less)
          have h_sub_nat :
              (CardinalNatural.Peano.subtract (da + db + CardinalNatural.Peano.one)
                CardinalNatural.Peano.ten
                (CardinalNatural.Peano.isLessThan_false_implies_le h_less)).toNat + 10 =
                da.toNat + db.toNat + 1 := by
            have h := congrArg CardinalNatural.Peano.toNat h_sub_cancel
            rw [CardinalNatural.Peano.add_toNat] at h
            rw [CardinalNatural.Peano.add_toNat, CardinalNatural.Peano.add_toNat] at h
            exact h
          rw [← ih_app]
          simp [listLengthNat]
          rw [← h_len]
          let sub := CardinalNatural.Peano.subtract (da + db + CardinalNatural.Peano.one)
                CardinalNatural.Peano.ten
                (CardinalNatural.Peano.isLessThan_false_implies_le h_less)
          change toNatListHelper ds_sum ((accA + accB) * 10 + sub.toNat) + 10 ^ (listLengthNat ds_sum + 1) =
            toNatListHelper ds_sum (accA * 10 + da.toNat + (accB * 10 + db.toNat)) + 10 ^ listLengthNat ds_sum
          rw [Nat.pow_succ]
          rw [Nat.mul_comm (10 ^ listLengthNat ds_sum) 10]
          rw [← toNatListHelper_add_acc ds_sum ((accA + accB) * 10 + sub.toNat) 10]
          have h_sub : sub.toNat + 10 = da.toNat + db.toNat + 1 := by
            dsimp [sub]
            exact h_sub_nat
          have h_acc : (accA + accB) * 10 + sub.toNat + 10 =
              accA * 10 + da.toNat + (accB * 10 + db.toNat) + 1 := by
            omega
          rw [h_acc]
          rw [toNatListHelper_add_acc ds_sum (accA * 10 + da.toNat + (accB * 10 + db.toNat)) 1]
          simp

theorem addAlignedLists_toCardinalList
  {a b : Sequences.List CardinalNatural.Peano}
  (h_shape : Sequences.List.SameLength a b) :
  let res := addAlignedLists a b
  toCardinalList res.1 +
      (if res.2 then CardinalNatural.Peano.fromNat (10 ^ listLengthNat a) else CardinalNatural.Peano.zero) =
    toCardinalList a + toCardinalList b := by
  apply CardinalNatural.Peano.eq_of_toNat_eq
  dsimp only
  rw [CardinalNatural.Peano.add_toNat, CardinalNatural.Peano.add_toNat]
  repeat rw [toCardinalList_toNat]
  have h := addAlignedLists_toNatListHelper h_shape 0 0
  dsimp only at h
  cases h_carry : (addAlignedLists a b).2 <;> simp [h_carry] at h ⊢
  · exact h
  · rw [CardinalNatural.Peano.toNat_fromNat]
    exact h

theorem addToList_toCardinalList (a b : Sequences.List CardinalNatural.Peano) :
  toCardinalList (addToList a b) = toCardinalList a + toCardinalList b := by
  unfold addToList
  generalize h_pad : Sequences.List.padAtStartToSameLength a b CardinalNatural.Peano.zero = padded
  cases padded with
  | mk a' b' =>
    have h_shape : Sequences.List.SameLength a' b' := by
      have h_same := Sequences.List.padAtStartToSameLength_sameLength a b CardinalNatural.Peano.zero
      rw [h_pad] at h_same
      exact h_same
    have h_padded_values : toCardinalList a' = toCardinalList a ∧ toCardinalList b' = toCardinalList b := by
      unfold Sequences.List.padAtStartToSameLength at h_pad
      dsimp only at h_pad
      split at h_pad
      · cases h_pad
        constructor
        · rfl
        · exact padAtStart_zero_toCardinalList b _
      · cases h_pad
        constructor
        · exact padAtStart_zero_toCardinalList a _
        · rfl
    generalize h_add : addAlignedLists a' b' = res
    cases res with
    | mk sum carry =>
      have h_aligned := addAlignedLists_toCardinalList h_shape
      rw [h_add] at h_aligned
      dsimp only at h_aligned
      cases carry with
      | false =>
        simp at h_aligned ⊢
        rw [h_add]
        simp
        rw [h_padded_values.left, h_padded_values.right] at h_aligned
        exact h_aligned
      | true =>
        apply CardinalNatural.Peano.eq_of_toNat_eq
        rw [toCardinalList_toNat]
        unfold toNatListHelper
        rw [CardinalNatural.Peano.add_toNat]
        simp [h_add]
        have h_nat := congrArg CardinalNatural.Peano.toNat h_aligned
        rw [CardinalNatural.Peano.add_toNat] at h_nat
        simp [CardinalNatural.Peano.toNat_fromNat] at h_nat
        repeat rw [toCardinalList_toNat] at h_nat
        have hpA := congrArg CardinalNatural.Peano.toNat h_padded_values.left
        have hpB := congrArg CardinalNatural.Peano.toNat h_padded_values.right
        rw [toCardinalList_toNat] at hpA
        rw [toCardinalList_toNat] at hpB
        rw [← hpA, ← hpB]
        have h_len : listLengthNat sum = listLengthNat a' := by
          have h := addAlignedLists_length h_shape
          rw [h_add] at h
          exact h
        change toNatListHelper sum CardinalNatural.Peano.one.toNat =
          toNatListHelper a' 0 + toNatListHelper b' 0
        change toNatListHelper sum 1 = toNatListHelper a' 0 + toNatListHelper b' 0
        rw [toNatListHelper_add_acc sum 0 1]
        rw [h_len]
        simpa using h_nat


def StartsNonZero : Sequences.List CardinalNatural.Peano → Prop
  | .empty => False
  | .firstElement d _ => d ≠ CardinalNatural.Peano.zero

theorem cardinal_lt_toNat {a b : CardinalNatural.Peano} (h : a < b) :
  a.toNat < b.toNat := by
  induction h with
  | base =>
    simp [CardinalNatural.Peano.toNat]
  | step _ ih =>
    exact Nat.lt_succ_of_lt ih

theorem toNatListHelper_lt_pow (l : Sequences.List CardinalNatural.Peano)
  (h : AllLessThanTen l) :
  toNatListHelper l 0 < 10 ^ listLengthNat l := by
  induction l with
  | empty =>
    simp [toNatListHelper, listLengthNat]
  | firstElement d ds ih =>
    unfold AllLessThanTen at h
    unfold toNatListHelper listLengthNat
    rw [toNatListHelper_add_acc ds (0 * 10) d.toNat]
    simp
    have h_tail := ih h.right
    have h_digit : d.toNat < 10 := by
      have hd := cardinal_lt_toNat h.left
      exact hd
    rw [Nat.pow_succ]
    have h_digit_le : d.toNat ≤ 9 := Nat.le_of_lt_succ h_digit
    have h_mul_le : d.toNat * 10 ^ listLengthNat ds ≤ 9 * 10 ^ listLengthNat ds :=
      Nat.mul_le_mul_right (10 ^ listLengthNat ds) h_digit_le
    omega

theorem toNatListHelper_ge_pow_of_startsNonZero
  {l : Sequences.List CardinalNatural.Peano}
  (h_start : StartsNonZero l) :
  match l with
  | .empty => False
  | .firstElement _ ds => 10 ^ listLengthNat ds ≤ toNatListHelper l 0 := by
  cases l with
  | empty => exact h_start
  | firstElement d ds =>
    unfold toNatListHelper
    rw [toNatListHelper_add_acc ds (0 * 10) d.toNat]
    simp
    have h_digit_ne : d.toNat ≠ 0 := CardinalNatural.Peano.toNat_ne_zero d h_start
    have h_digit_pos : 1 ≤ d.toNat := Nat.succ_le_of_lt (Nat.pos_of_ne_zero h_digit_ne)
    have h_mul_ge : 1 * 10 ^ listLengthNat ds ≤ d.toNat * 10 ^ listLengthNat ds :=
      Nat.mul_le_mul_right (10 ^ listLengthNat ds) h_digit_pos
    omega

theorem listLengthNat_eq_of_sameLength {a b : Sequences.List CardinalNatural.Peano}
  (h : Sequences.List.SameLength a b) : listLengthNat a = listLengthNat b := by
  induction h with
  | empty => rfl
  | firstElement _ ih =>
    unfold listLengthNat
    rw [ih]

theorem sameLength_of_listLengthNat_eq {a b : Sequences.List CardinalNatural.Peano}
  (h : listLengthNat a = listLengthNat b) : Sequences.List.SameLength a b := by
  induction a generalizing b with
  | empty =>
    cases b with
    | empty => exact Sequences.List.SameLength.empty
    | firstElement d ds =>
      unfold listLengthNat at h
      cases h
  | firstElement d ds ih =>
    cases b with
    | empty =>
      unfold listLengthNat at h
      cases h
    | firstElement e es =>
      apply Sequences.List.SameLength.firstElement
      apply ih
      unfold listLengthNat at h
      exact Nat.succ.inj h

theorem list_eq_of_sameLength_toNatListHelper_eq
  {a b : Sequences.List CardinalNatural.Peano}
  (h_shape : Sequences.List.SameLength a b)
  (ha : AllLessThanTen a) (hb : AllLessThanTen b)
  (h_val : toNatListHelper a 0 = toNatListHelper b 0) : a = b := by
  induction h_shape with
  | empty => rfl
  | firstElement h_tail ih =>
    rename_i da db das dbs
    unfold AllLessThanTen at ha hb
    unfold toNatListHelper at h_val
    rw [toNatListHelper_add_acc das (0 * 10) da.toNat] at h_val
    rw [toNatListHelper_add_acc dbs (0 * 10) db.toNat] at h_val
    simp at h_val
    have h_len : listLengthNat das = listLengthNat dbs := listLengthNat_eq_of_sameLength h_tail
    have h_tail_a_lt := toNatListHelper_lt_pow das ha.right
    have h_tail_b_lt := toNatListHelper_lt_pow dbs hb.right
    rw [← h_len] at h_val h_tail_b_lt
    rw [Nat.mul_comm da.toNat (10 ^ listLengthNat das)] at h_val
    rw [Nat.mul_comm db.toNat (10 ^ listLengthNat das)] at h_val
    have h_da : da.toNat = db.toNat := by
      let base := 10 ^ listLengthNat das
      have h_base_pos : 0 < base := by
        dsimp [base]
        exact Nat.pow_pos (by decide : 0 < 10)
      have h_left_div : (toNatListHelper das 0 + base * da.toNat) / base = da.toNat := by
        rw [Nat.add_mul_div_left _ _ h_base_pos]
        rw [Nat.div_eq_of_lt]
        · simp
        · dsimp [base]
          exact h_tail_a_lt
      have h_right_div : (toNatListHelper dbs 0 + base * db.toNat) / base = db.toNat := by
        rw [Nat.add_mul_div_left _ _ h_base_pos]
        rw [Nat.div_eq_of_lt]
        · simp
        · dsimp [base]
          exact h_tail_b_lt
      have h_div := congrArg (fun n => n / base) h_val
      change (toNatListHelper das 0 + base * da.toNat) / base =
        (toNatListHelper dbs 0 + base * db.toNat) / base at h_div
      rw [h_left_div, h_right_div] at h_div
      exact h_div
    have h_digits : da = db := CardinalNatural.Peano.eq_of_toNat_eq h_da
    subst h_digits
    have h_tail_val : toNatListHelper das 0 = toNatListHelper dbs 0 := by
      let base := 10 ^ listLengthNat das
      have h_left_mod : (toNatListHelper das 0 + base * da.toNat) % base = toNatListHelper das 0 := by
        rw [Nat.add_mul_mod_self_left]
        rw [Nat.mod_eq_of_lt]
        dsimp [base]
        exact h_tail_a_lt
      have h_right_mod : (toNatListHelper dbs 0 + base * da.toNat) % base = toNatListHelper dbs 0 := by
        rw [Nat.add_mul_mod_self_left]
        rw [Nat.mod_eq_of_lt]
        dsimp [base]
        exact h_tail_b_lt
      have h_mod := congrArg (fun n => n % base) h_val
      change (toNatListHelper das 0 + base * da.toNat) % base =
        (toNatListHelper dbs 0 + base * da.toNat) % base at h_mod
      rw [h_left_mod, h_right_mod] at h_mod
      exact h_mod
    have h_tails := ih ha.right hb.right h_tail_val
    rw [h_tails]

theorem normalizedList_eq_of_toNatListHelper_eq
  {a b : Sequences.List CardinalNatural.Peano}
  (ha : AllLessThanTen a) (hb : AllLessThanTen b)
  (ha_start : StartsNonZero a)
  (hb_start : StartsNonZero b)
  (h_val : toNatListHelper a 0 = toNatListHelper b 0) : a = b := by
  have h_len : listLengthNat a = listLengthNat b := by
    cases Nat.lt_trichotomy (listLengthNat a) (listLengthNat b) with
    | inl hlt =>
      cases b with
      | empty => cases hb_start
      | firstElement db dbs =>
        have h_upper := toNatListHelper_lt_pow a ha
        have h_lower := toNatListHelper_ge_pow_of_startsNonZero (l := Sequences.List.firstElement db dbs) hb_start
        have hle : listLengthNat a ≤ listLengthNat dbs := by
          change listLengthNat a < (listLengthNat dbs).succ at hlt
          exact Nat.le_of_lt_succ hlt
        have hpow_le : 10 ^ listLengthNat a ≤ 10 ^ listLengthNat dbs :=
          Nat.pow_le_pow_right (by decide : 0 < 10) hle
        have hlt_val : toNatListHelper a 0 < toNatListHelper (Sequences.List.firstElement db dbs) 0 :=
          Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le h_upper hpow_le) h_lower
        rw [h_val] at hlt_val
        exact False.elim (Nat.lt_irrefl _ hlt_val)
    | inr hrest =>
      cases hrest with
      | inl heq => exact heq
      | inr hlt =>
        cases a with
        | empty => cases ha_start
        | firstElement da das =>
          have h_upper := toNatListHelper_lt_pow b hb
          have h_lower := toNatListHelper_ge_pow_of_startsNonZero (l := Sequences.List.firstElement da das) ha_start
          have hle : listLengthNat b ≤ listLengthNat das := by
            change listLengthNat b < (listLengthNat das).succ at hlt
            exact Nat.le_of_lt_succ hlt
          have hpow_le : 10 ^ listLengthNat b ≤ 10 ^ listLengthNat das :=
            Nat.pow_le_pow_right (by decide : 0 < 10) hle
          have hlt_val : toNatListHelper b 0 < toNatListHelper (Sequences.List.firstElement da das) 0 :=
            Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le h_upper hpow_le) h_lower
          rw [← h_val] at hlt_val
          exact False.elim (Nat.lt_irrefl _ hlt_val)
  have h_shape := sameLength_of_listLengthNat_eq h_len
  exact list_eq_of_sameLength_toNatListHelper_eq h_shape ha hb h_val

theorem equivalent_of_toPeano_eq {a b : Decimal} (h : a.toPeano = b.toPeano) : a ≈ b := by
  change normalize a = normalize b
  apply Subtype.ext
  have h_val : toNatListHelper (normalize a).val 0 = toNatListHelper (normalize b).val 0 := by
    rw [← toCardinalList_toNat (normalize a).val, ← toCardinalList_toNat (normalize b).val]
    apply congrArg CardinalNatural.Peano.toNat
    have h_card : toCardinalList a.val = toCardinalList b.val := by
      have h_from := congrArg CardinalNatural.Peano.fromOrdinal h
      unfold toPeano at h_from
      repeat rw [CardinalNatural.Peano.fromOrdinal_toOrdinal] at h_from
      exact h_from
    rw [normalize_toCardinalList a, normalize_toCardinalList b]
    exact h_card
  have ha_start : StartsNonZero (normalize a).val := by
    unfold normalize
    exact normalizeList_startsNonZero a.val a.property.right
  have hb_start : StartsNonZero (normalize b).val := by
    unfold normalize
    exact normalizeList_startsNonZero b.val b.property.right
  let na := normalize a
  let nb := normalize b
  change na.val = nb.val
  exact @normalizedList_eq_of_toNatListHelper_eq na.val nb.val
    na.property.left nb.property.left ha_start hb_start h_val

theorem fromOrdinal_add (x y : Peano) :
  CardinalNatural.Peano.fromOrdinal (x + y) =
    CardinalNatural.Peano.fromOrdinal x + CardinalNatural.Peano.fromOrdinal y := by
  induction y with
  | one =>
    rw [Peano.add_one]
    change CardinalNatural.Peano.successor (CardinalNatural.Peano.fromOrdinal x) =
      CardinalNatural.Peano.fromOrdinal x + CardinalNatural.Peano.one
    rw [CardinalNatural.Peano.one, CardinalNatural.Peano.add_successor, CardinalNatural.Peano.add_zero]
  | successor y ih =>
    rw [Peano.add_succ]
    change CardinalNatural.Peano.successor (CardinalNatural.Peano.fromOrdinal (x + y)) =
      CardinalNatural.Peano.fromOrdinal x + CardinalNatural.Peano.successor (CardinalNatural.Peano.fromOrdinal y)
    rw [CardinalNatural.Peano.add_successor, ih]

theorem peano_eq_of_fromOrdinal_eq {x y : Peano}
  (h : CardinalNatural.Peano.fromOrdinal x = CardinalNatural.Peano.fromOrdinal y) : x = y := by
  obtain ⟨hx_nonzero, hx⟩ := CardinalNatural.Peano.toOrdinal_fromOrdinal x
  obtain ⟨hy_nonzero, hy⟩ := CardinalNatural.Peano.toOrdinal_fromOrdinal y
  exact hx.symm.trans ((CardinalNatural.Peano.toOrdinal_congr h hx_nonzero hy_nonzero).trans hy)

theorem add_toPeano (x y : Decimal) :
  (x + y).toPeano = x.toPeano + y.toPeano := by
  apply peano_eq_of_fromOrdinal_eq
  unfold toPeano
  change CardinalNatural.Peano.fromOrdinal
      (CardinalNatural.Peano.toOrdinal (toCardinalList (x + y).val) _) =
    CardinalNatural.Peano.fromOrdinal
      (CardinalNatural.Peano.toOrdinal (toCardinalList x.val) _ +
        CardinalNatural.Peano.toOrdinal (toCardinalList y.val) _)
  rw [CardinalNatural.Peano.fromOrdinal_toOrdinal]
  rw [fromOrdinal_add]
  rw [CardinalNatural.Peano.fromOrdinal_toOrdinal]
  rw [CardinalNatural.Peano.fromOrdinal_toOrdinal]
  change toCardinalList (addToList x.val y.val) = toCardinalList x.val + toCardinalList y.val
  exact addToList_toCardinalList x.val y.val

theorem add_commutative (a b : Decimal) : a + b = b + a := by
  apply Subtype.ext
  exact addToList_commutative a.val b.val

theorem equivalent_add_commutative (a b : Decimal) : a + b ≈ b + a := by
  rw [add_commutative]
  rfl

def fromPeano : Peano → Decimal
  | Peano.one => Decimal.one
  | Peano.successor p => successor (fromPeano p)

theorem fromPeano_toCardinalList (x : Peano) :
  toCardinalList (fromPeano x).val = CardinalNatural.Peano.fromOrdinal x := by
  induction x with
  | one =>
    rfl
  | successor x ih =>
    unfold fromPeano
    rw [successor_toCardinalList, ih]
    rfl

theorem toPeano_fromPeano (x : Peano) :
  toPeano (fromPeano x) = x := by
  unfold toPeano
  have h_card := fromPeano_toCardinalList x
  have h_toOrdinal := CardinalNatural.Peano.toOrdinal_fromOrdinal x
  obtain ⟨h_nonzero, h_eq⟩ := h_toOrdinal
  exact (CardinalNatural.Peano.toOrdinal_congr h_card _ h_nonzero).trans h_eq

def subtractOneBigEndian : Sequences.List CardinalNatural.Peano → Sequences.List CardinalNatural.Peano × Bool
  | .empty => (Sequences.List.empty, true)
  | .firstElement d ds =>
    let (ds', borrow) := subtractOneBigEndian ds
    if borrow then
      match d with
      | .zero => (Sequences.List.firstElement CardinalNatural.Peano.nine ds', true)
      | .successor d' => (Sequences.List.firstElement d' ds', false)
    else
      (Sequences.List.firstElement d ds', false)

theorem nine_lt_ten : CardinalNatural.Peano.nine < CardinalNatural.Peano.ten := CardinalNatural.Peano.LessThan.base

theorem subtractOneBigEndian_allLessThanTen (l : Sequences.List CardinalNatural.Peano)
  (h : AllLessThanTen l) : AllLessThanTen (subtractOneBigEndian l).1 := by
  induction l with
  | empty =>
    unfold subtractOneBigEndian
    unfold AllLessThanTen
    exact trivial
  | firstElement d ds ih =>
    unfold subtractOneBigEndian
    generalize h_sub : subtractOneBigEndian ds = res
    cases res with
    | mk ds' borrow =>
      dsimp only
      unfold AllLessThanTen at h
      have ih' := ih h.right
      rw [h_sub] at ih'
      dsimp only at ih'
      cases borrow with
      | false =>
        unfold AllLessThanTen
        constructor
        · exact h.left
        · exact ih'
      | true =>
        cases d with
        | zero =>
          unfold AllLessThanTen
          constructor
          · exact nine_lt_ten
          · exact ih'
        | successor d' =>
          unfold AllLessThanTen
          constructor
          · apply CardinalNatural.Peano.lt_of_succ_lt h.left
          · exact ih'

def Decimal.predecessorHelper (l : Sequences.List CardinalNatural.Peano) : Sequences.List CardinalNatural.Peano :=
  let (l', _) := subtractOneBigEndian l
  l'



theorem predecessorHelper_allLessThanTen (l : Sequences.List CardinalNatural.Peano)
  (h : AllLessThanTen l) : AllLessThanTen (Decimal.predecessorHelper l) := by
  unfold Decimal.predecessorHelper
  generalize h_sub : subtractOneBigEndian l = res
  have h_all := subtractOneBigEndian_allLessThanTen l h
  rw [h_sub] at h_all
  cases res with
  | mk ds' borrow =>
    exact h_all

theorem subtractOneBigEndian_borrow_implies_empty_or_hasNonZero (l : Sequences.List CardinalNatural.Peano)
  : (subtractOneBigEndian l).2 = true →
    l = Sequences.List.empty ∨ HasNonZero (subtractOneBigEndian l).1 := by
  induction l with
  | empty =>
    intro _
    left
    rfl
  | firstElement d ds ih =>
    intro h
    right
    unfold subtractOneBigEndian at h ⊢
    generalize h_sub : subtractOneBigEndian ds = res
    rw [h_sub] at h
    cases res with
    | mk ds' borrow =>
      dsimp only at h ⊢
      cases borrow with
      | false =>
        contradiction
      | true =>
        cases d with
        | zero =>
          unfold HasNonZero
          left
          exact CardinalNatural.Peano.successor_ne_zero CardinalNatural.Peano.eight
        | successor d' =>
          contradiction

theorem normalizeList_eq_one_or_hasNonZero_subtract (l : Sequences.List CardinalNatural.Peano)
  (h_nz : HasNonZero l) :
  Decimal.normalizeList l = Sequences.List.firstElement CardinalNatural.Peano.one Sequences.List.empty ∨
  HasNonZero (subtractOneBigEndian l).1 := by
  induction l with
  | empty =>
    unfold HasNonZero at h_nz
    contradiction
  | firstElement d ds ih =>
    unfold subtractOneBigEndian
    generalize h_sub : subtractOneBigEndian ds = res
    cases res with
    | mk ds' borrow =>
      dsimp only
      cases borrow with
      | false =>
        cases h_nz with
        | inl h_d =>
          right
          unfold HasNonZero
          left
          exact h_d
        | inr h_ds =>
          have ih' := ih h_ds
          cases ih' with
          | inl h_eq =>
            by_cases h_d_zero : d = CardinalNatural.Peano.zero
            · left
              unfold Decimal.normalizeList
              rw [if_pos h_d_zero]
              exact h_eq
            · right
              unfold HasNonZero
              left
              exact h_d_zero
          | inr h_has =>
            right
            unfold HasNonZero
            right
            rw [h_sub] at h_has
            exact h_has
      | true =>
        cases d with
        | zero =>
          right
          unfold HasNonZero
          left
          exact CardinalNatural.Peano.successor_ne_zero CardinalNatural.Peano.eight
        | successor d' =>
          cases d' with
          | zero =>
            have h_borrow : (subtractOneBigEndian ds).snd = true := by
              rw [h_sub]
            have h_ds_prop := subtractOneBigEndian_borrow_implies_empty_or_hasNonZero ds h_borrow
            cases h_ds_prop with
            | inl h_empty =>
              left
              unfold Decimal.normalizeList
              have h_not_zero : CardinalNatural.Peano.successor CardinalNatural.Peano.zero ≠ CardinalNatural.Peano.zero := by exact CardinalNatural.Peano.successor_ne_zero CardinalNatural.Peano.zero
              rw [if_neg h_not_zero]
              rw [h_empty]
              rfl
            | inr h_has =>
              right
              unfold HasNonZero
              right
              rw [h_sub] at h_has
              exact h_has
          | successor d'' =>
            right
            unfold HasNonZero
            left
            exact CardinalNatural.Peano.successor_ne_zero d''

theorem predecessorHelper_hasNonZero (d : Decimal) (h : ¬ Equivalent d Decimal.one) : HasNonZero (Decimal.predecessorHelper d.val) := by
  have h_prop := normalizeList_eq_one_or_hasNonZero_subtract d.val d.property.right
  cases h_prop with
  | inl h_eq =>
    unfold Equivalent at h
    unfold normalize at h
    unfold Decimal.one at h
    dsimp only at h
    have h_contra : (⟨Decimal.normalizeList d.val, ⟨Decimal.normalizeList_allLessThanTen d.val d.property.left, Decimal.normalizeList_hasNonZero d.val d.property.right⟩⟩ : Decimal) = Decimal.one := by
      apply Subtype.ext
      unfold Decimal.one
      dsimp only
      exact h_eq
    exact False.elim (h h_contra)
  | inr h_has =>
    unfold Decimal.predecessorHelper
    generalize h_sub : subtractOneBigEndian d.val = res
    cases res with
    | mk ds' borrow =>
      dsimp only
      rw [h_sub] at h_has
      exact h_has

def Decimal.predecessor (d : Decimal) (h : ¬ Equivalent d Decimal.one) : Decimal :=
  ⟨Decimal.predecessorHelper d.val, ⟨by
    apply predecessorHelper_allLessThanTen
    exact d.property.left
  , by
    apply predecessorHelper_hasNonZero
    exact h
  ⟩⟩

def predecessor (d : Decimal) (h : ¬ Equivalent d Decimal.one) : Decimal :=
  ZeroMath.Numbers.OrdinalNatural.Decimal.Decimal.predecessor d h

theorem subtractOneBigEndian_borrow_false_implies_hasNonZero
  (l : Sequences.List CardinalNatural.Peano) :
  (subtractOneBigEndian l).2 = false → HasNonZero l := by
  induction l with
  | empty =>
    intro h_borrow
    unfold subtractOneBigEndian at h_borrow
    contradiction
  | firstElement d ds ih =>
    intro h_borrow
    unfold subtractOneBigEndian at h_borrow
    generalize h_sub : subtractOneBigEndian ds = res
    rw [h_sub] at h_borrow
    cases res with
    | mk ds' borrow =>
      dsimp only at h_borrow
      cases borrow with
      | false =>
        unfold HasNonZero
        right
        apply ih
        rw [h_sub]
      | true =>
        cases d with
        | zero => contradiction
        | successor d' =>
          unfold HasNonZero
          left
          exact CardinalNatural.Peano.successor_ne_zero d'

theorem subtractOneBigEndian_no_borrow_of_hasNonZero {l : Sequences.List CardinalNatural.Peano}
  (h : HasNonZero l) : (subtractOneBigEndian l).2 = false := by
  induction l with
  | empty =>
    unfold HasNonZero at h
    contradiction
  | firstElement d ds ih =>
    unfold subtractOneBigEndian
    generalize h_sub : subtractOneBigEndian ds = res
    cases res with
    | mk ds' borrow =>
      dsimp only
      cases borrow with
      | false => rfl
      | true =>
        cases d with
        | zero =>
          unfold HasNonZero at h
          cases h with
          | inl h_d => contradiction
          | inr h_ds =>
            have h_no_borrow := ih h_ds
            rw [h_sub] at h_no_borrow
            contradiction
        | successor d' => rfl

theorem addOneBigEndian_subtractOneBigEndian
  (l : Sequences.List CardinalNatural.Peano) (h : AllLessThanTen l) :
  Decimal.addOneBigEndian (subtractOneBigEndian l).1 = (l, (subtractOneBigEndian l).2) := by
  induction l with
  | empty =>
    unfold subtractOneBigEndian Decimal.addOneBigEndian
    rfl
  | firstElement d ds ih =>
    unfold subtractOneBigEndian
    generalize h_sub : subtractOneBigEndian ds = res
    cases res with
    | mk ds' borrow =>
      dsimp only
      have h_tail_all : AllLessThanTen ds := by
        unfold AllLessThanTen at h
        exact h.right
      have ih_tail := ih h_tail_all
      rw [h_sub] at ih_tail
      dsimp only at ih_tail
      cases borrow with
      | false =>
        simp [Decimal.addOneBigEndian, ih_tail]
      | true =>
        cases d with
        | zero =>
          simp [Decimal.addOneBigEndian, ih_tail]
          rfl
        | successor d' =>
          have h_ne_ten : CardinalNatural.Peano.successor d' ≠ CardinalNatural.Peano.ten := by
            unfold AllLessThanTen at h
            exact CardinalNatural.Peano.ne_of_lt h.left
          simp [Decimal.addOneBigEndian, ih_tail, h_ne_ten]

theorem successor_predecessor_val (d : Decimal) (h : ¬ Equivalent d Decimal.one) :
  (d.predecessor h).successor.val = d.val := by
  unfold predecessor ZeroMath.Numbers.OrdinalNatural.Decimal.Decimal.predecessor Decimal.successor
    Decimal.predecessorHelper successorHelper
  dsimp only
  have h_add := addOneBigEndian_subtractOneBigEndian d.val d.property.left
  have h_no_borrow := subtractOneBigEndian_no_borrow_of_hasNonZero d.property.right
  rw [h_add, h_no_borrow]
  rfl

theorem successor_toPeano (x : Decimal) :
  x.successor.toPeano = x.toPeano.successor := by
  unfold toPeano
  have h_eq : toCardinalList x.successor.val = toCardinalList x.val + CardinalNatural.Peano.successor CardinalNatural.Peano.zero := successor_toCardinalList x
  have h_eq2 : toCardinalList x.val + CardinalNatural.Peano.successor CardinalNatural.Peano.zero = CardinalNatural.Peano.successor (toCardinalList x.val) := by
    rw [CardinalNatural.Peano.add_successor, CardinalNatural.Peano.add_zero]
  have h_eq3 : toCardinalList x.successor.val = CardinalNatural.Peano.successor (toCardinalList x.val) := Eq.trans h_eq h_eq2

  have h_congr_applied := CardinalNatural.Peano.toOrdinal_congr h_eq3
    (by
      have h : CardinalNatural.Peano.zero ≠ CardinalNatural.Peano.zero ∨ HasNonZero x.successor.val := Or.inr x.successor.property.right
      exact toCardinalHelper_ne_zero x.successor.val CardinalNatural.Peano.zero h
    )
    (CardinalNatural.Peano.successor_ne_zero _)

  have h_succ := CardinalNatural.Peano.toOrdinal_successor (toCardinalList x.val)
    (CardinalNatural.Peano.successor_ne_zero _)
    (by
      have h : CardinalNatural.Peano.zero ≠ CardinalNatural.Peano.zero ∨ HasNonZero x.val := Or.inr x.property.right
      exact toCardinalHelper_ne_zero x.val CardinalNatural.Peano.zero h
    )

  exact Eq.trans h_congr_applied h_succ

theorem peano_predecessor_congr {a b : OrdinalNatural.Peano}
  (ha : a ≠ OrdinalNatural.Peano.one) (hb : b ≠ OrdinalNatural.Peano.one)
  (h_eq : a = b) : a.predecessor ha = b.predecessor hb := by
  cases h_eq
  rfl

theorem predecessor_toPeano (x : Decimal) (h : ¬ Equivalent x Decimal.one) :
  ∃ h2, (x.predecessor h).toPeano = x.toPeano.predecessor h2 := by
  have h_successor_val := successor_predecessor_val x h
  have h_successor_toPeano : (x.predecessor h).successor.toPeano = x.toPeano := by
    unfold toPeano
    apply CardinalNatural.Peano.toOrdinal_congr
    rw [h_successor_val]
  have h_toPeano_succ : x.toPeano = OrdinalNatural.Peano.successor ((x.predecessor h).toPeano) := by
    exact h_successor_toPeano.symm.trans (successor_toPeano (x.predecessor h))
  have h2 : x.toPeano ≠ OrdinalNatural.Peano.one := by
    rw [h_toPeano_succ]
    intro h_one
    cases h_one
  exists h2
  let p := (x.predecessor h).toPeano
  have h2' : OrdinalNatural.Peano.successor p ≠ OrdinalNatural.Peano.one := by
    intro h_one
    cases h_one
  have h_pred_succ : p = (OrdinalNatural.Peano.successor p).predecessor h2' := rfl
  exact h_pred_succ.trans (peano_predecessor_congr h2' h2 h_toPeano_succ.symm)

def LessThan (x y : Decimal) : Prop :=
  x.toPeano < y.toPeano

instance : LT Decimal where
  lt := LessThan

def LessThanOrEquivalent (x y : Decimal) : Prop :=
  x < y ∨ x ≈ y

instance : LE Decimal where
  le := LessThanOrEquivalent

theorem lt_trans {a b c : Decimal} (h1 : a < b) (h2 : b < c) : a < c := by
  have h1' : a.toPeano < b.toPeano := h1
  have h2' : b.toPeano < c.toPeano := h2
  exact Peano.lt_trans h1' h2'

theorem le_trans {a b c : Decimal} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
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
        rw [← normalize_toPeano b, ← normalize_toPeano c]
        have heq : normalize b = normalize c := h2_eq
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
        rw [← normalize_toPeano a, ← normalize_toPeano b]
        have heq : normalize a = normalize b := h1_eq
        rw [heq]
      have hbc : b.toPeano < c.toPeano := h2_lt
      have hac : a.toPeano < c.toPeano := by
        rw [hab]
        exact hbc
      exact hac
    | inr h2_eq =>
      right
      have hab : normalize a = normalize b := h1_eq
      have hbc : normalize b = normalize c := h2_eq
      exact Eq.trans hab hbc

theorem not_lt_of_equivalent {a b : Decimal} (h : a ≈ b) : ¬ a < b := by
  intro hlt
  have h_eq := toPeano_eq_of_equivalent h
  have hlt_peano : a.toPeano < b.toPeano := hlt
  rw [h_eq] at hlt_peano
  exact Peano.not_lt_self b.toPeano hlt_peano

theorem not_equivalent_of_lt {a b : Decimal} (h : a < b) : ¬ a ≈ b := by
  intro h_eq
  exact not_lt_of_equivalent h_eq h

theorem not_gt_of_lt {a b : Decimal} (h : a < b) : ¬ b < a := by
  intro hba
  exact Peano.not_lt_of_lt h hba

theorem trichotomy (a b : Decimal) : ZeroMath.Logic.Trichotomy (a < b) (a ≈ b) (b < a) := by
  cases Peano.trichotomy a.toPeano b.toPeano with
  | first h_lt h_ne h_not_gt =>
    exact ZeroMath.Logic.Trichotomy.first h_lt (not_equivalent_of_lt h_lt) h_not_gt
  | second h_eq h_not_lt h_not_gt =>
    have h_equiv : a ≈ b := equivalent_of_toPeano_eq h_eq
    exact ZeroMath.Logic.Trichotomy.second h_equiv h_not_lt h_not_gt
  | third h_gt h_not_lt h_ne =>
    have h_not_equiv : ¬ a ≈ b := by
      intro h_equiv
      exact not_equivalent_of_lt h_gt h_equiv.symm
    exact ZeroMath.Logic.Trichotomy.third h_gt h_not_lt h_not_equiv

theorem add_associative (a b c : Decimal) : a + b + c ≈ a + (b + c) := by
  apply equivalent_of_toPeano_eq
  rw [add_toPeano, add_toPeano, add_toPeano, add_toPeano]
  exact ZeroMath.Numbers.OrdinalNatural.Peano.add_associative a.toPeano b.toPeano c.toPeano

theorem fromPeano_toPeano (x : Decimal) : fromPeano (toPeano x) ≈ x := by
  apply equivalent_of_toPeano_eq
  rw [toPeano_fromPeano]

def isLessThanAlignedLists (x y : Sequences.List CardinalNatural.Peano) : Bool :=
  match x, y with
  | .empty, .empty => false
  | .firstElement dx dxs, .firstElement dy dys =>
    if CardinalNatural.Peano.isLessThan dx dy then
      true
    else if CardinalNatural.Peano.isLessThan dy dx then
      false
    else
      isLessThanAlignedLists dxs dys
  | _, _ => false -- This case should not occur if the lists are properly padded to the same length

def isLessThan (x y : Decimal) : Bool :=
  let ⟨x', y'⟩ := Sequences.List.padAtStartToSameLength x.val y.val CardinalNatural.Peano.zero
  isLessThanAlignedLists x' y'

theorem isLessThanAlignedLists_eq_true_iff_nat_lt
  {a b : Sequences.List CardinalNatural.Peano}
  (h_shape : Sequences.List.SameLength a b)
  (ha : AllLessThanTen a) (hb : AllLessThanTen b) :
  isLessThanAlignedLists a b = true ↔ toNatListHelper a 0 < toNatListHelper b 0 := by
  induction h_shape with
  | empty =>
    simp [isLessThanAlignedLists, toNatListHelper]
  | firstElement h_tail ih =>
    rename_i da db das dbs
    unfold AllLessThanTen at ha hb
    unfold isLessThanAlignedLists
    by_cases h_ab_bool : CardinalNatural.Peano.isLessThan da db = true
    · simp [h_ab_bool]
      unfold toNatListHelper
      rw [toNatListHelper_add_acc das (0 * 10) da.toNat]
      rw [toNatListHelper_add_acc dbs (0 * 10) db.toNat]
      simp
      have h_da_lt_db : da.toNat < db.toNat :=
        cardinal_lt_toNat ((CardinalNatural.Peano.isLessThan_eq_true_iff_lt da db).mp h_ab_bool)
      have h_tail_lt := toNatListHelper_lt_pow das ha.right
      have h_len : listLengthNat das = listLengthNat dbs := listLengthNat_eq_of_sameLength h_tail
      rw [← h_len]
      have h_base_pos : 0 < 10 ^ listLengthNat das := Nat.pow_pos (by decide : 0 < 10)
      have h_db_pos : da.toNat + 1 ≤ db.toNat := Nat.succ_le_of_lt h_da_lt_db
      have h_mul_le : (da.toNat + 1) * 10 ^ listLengthNat das ≤ db.toNat * 10 ^ listLengthNat das :=
        Nat.mul_le_mul_right (10 ^ listLengthNat das) h_db_pos
      have h_succ_mul : (da.toNat + 1) * 10 ^ listLengthNat das =
          da.toNat * 10 ^ listLengthNat das + 10 ^ listLengthNat das := by
        rw [Nat.add_mul, Nat.one_mul]
      omega
    · simp [h_ab_bool]
      by_cases h_ba_bool : CardinalNatural.Peano.isLessThan db da = true
      · simp [h_ba_bool]
        unfold toNatListHelper
        rw [toNatListHelper_add_acc das (0 * 10) da.toNat]
        rw [toNatListHelper_add_acc dbs (0 * 10) db.toNat]
        simp
        have h_db_lt_da : db.toNat < da.toNat :=
          cardinal_lt_toNat ((CardinalNatural.Peano.isLessThan_eq_true_iff_lt db da).mp h_ba_bool)
        have h_tail_b_lt := toNatListHelper_lt_pow dbs hb.right
        have h_len : listLengthNat das = listLengthNat dbs := listLengthNat_eq_of_sameLength h_tail
        rw [← h_len] at h_tail_b_lt
        rw [← h_len]
        have h_base_pos : 0 < 10 ^ listLengthNat das := Nat.pow_pos (by decide : 0 < 10)
        have h_da_pos : db.toNat + 1 ≤ da.toNat := Nat.succ_le_of_lt h_db_lt_da
        have h_mul_le : (db.toNat + 1) * 10 ^ listLengthNat das ≤ da.toNat * 10 ^ listLengthNat das :=
          Nat.mul_le_mul_right (10 ^ listLengthNat das) h_da_pos
        have h_succ_mul : (db.toNat + 1) * 10 ^ listLengthNat das =
            db.toNat * 10 ^ listLengthNat das + 10 ^ listLengthNat das := by
          rw [Nat.add_mul, Nat.one_mul]
        omega
      · simp [h_ba_bool]
        have h_not_ab : ¬ da < db := (CardinalNatural.Peano.isLessThan_eq_false_iff_not_lt da db).mp (by
          cases h : CardinalNatural.Peano.isLessThan da db
          · rfl
          · rw [h] at h_ab_bool
            contradiction)
        have h_not_ba : ¬ db < da := (CardinalNatural.Peano.isLessThan_eq_false_iff_not_lt db da).mp (by
          cases h : CardinalNatural.Peano.isLessThan db da
          · rfl
          · rw [h] at h_ba_bool
            contradiction)
        have h_da_eq_db : da = db := by
          cases CardinalNatural.Peano.trichotomy_or da db with
          | inl hlt => exact False.elim (h_not_ab hlt)
          | inr hrest =>
            cases hrest with
            | inl heq => exact heq
            | inr hgt => exact False.elim (h_not_ba hgt)
        subst h_da_eq_db
        have ih_app := ih ha.right hb.right
        unfold toNatListHelper
        rw [toNatListHelper_add_acc das (0 * 10) da.toNat]
        rw [toNatListHelper_add_acc dbs (0 * 10) da.toNat]
        simp
        have h_len : listLengthNat das = listLengthNat dbs := listLengthNat_eq_of_sameLength h_tail
        rw [← h_len]
        constructor
        · intro h_less
          exact Nat.add_lt_add_right (ih_app.mp h_less) _
        · intro h_tail_less
          exact ih_app.mpr (Nat.lt_of_add_lt_add_right h_tail_less)

theorem cardinal_lt_of_toNat_lt {a b : CardinalNatural.Peano}
  (h : a.toNat < b.toNat) : a < b := by
  cases CardinalNatural.Peano.trichotomy_or a b with
  | inl hlt => exact hlt
  | inr hrest =>
    cases hrest with
    | inl heq =>
      rw [heq] at h
      exact False.elim (Nat.lt_irrefl _ h)
    | inr hgt =>
      have hgt_nat := cardinal_lt_toNat hgt
      exact False.elim (Nat.lt_asymm h hgt_nat)

theorem cardinal_lt_toOrdinal_iff {a b : CardinalNatural.Peano}
  (ha : a ≠ CardinalNatural.Peano.zero) (hb : b ≠ CardinalNatural.Peano.zero) :
  CardinalNatural.Peano.toOrdinal a ha < CardinalNatural.Peano.toOrdinal b hb ↔ a < b := by
  constructor
  · intro h
    cases a with
    | zero => contradiction
    | successor a' =>
      cases b with
      | zero => contradiction
      | successor b' =>
        cases a' with
        | zero =>
          cases b' with
          | zero =>
            unfold CardinalNatural.Peano.toOrdinal at h
            exact False.elim (Peano.not_lt_self Peano.one h)
          | successor b'' =>
            exact CardinalNatural.Peano.succ_lt_succ (CardinalNatural.Peano.zero_lt_succ _)
        | successor a'' =>
          cases b' with
          | zero =>
            unfold CardinalNatural.Peano.toOrdinal at h
            exact False.elim (Peano.not_lt_one _ h)
          | successor b'' =>
            unfold CardinalNatural.Peano.toOrdinal at h
            exact CardinalNatural.Peano.succ_lt_succ ((cardinal_lt_toOrdinal_iff _ _).mp (Peano.lt_of_succ_lt_succ h))
  · intro h
    cases a with
    | zero => contradiction
    | successor a' =>
      cases b with
      | zero => exact False.elim (CardinalNatural.Peano.not_lt_zero _ h)
      | successor b' =>
        cases a' with
        | zero =>
          cases b' with
          | zero =>
            exact False.elim (CardinalNatural.Peano.not_lt_self _ h)
          | successor b'' =>
            unfold CardinalNatural.Peano.toOrdinal
            exact Peano.one_lt_succ _
        | successor a'' =>
          cases b' with
          | zero =>
            have h_opp : CardinalNatural.Peano.zero.successor < a''.successor.successor := CardinalNatural.Peano.succ_lt_succ (CardinalNatural.Peano.zero_lt_succ _)
            exact False.elim (CardinalNatural.Peano.not_lt_of_lt h_opp h)
          | successor b'' =>
            unfold CardinalNatural.Peano.toOrdinal
            apply Peano.succ_lt_succ
            apply (cardinal_lt_toOrdinal_iff _ _).mpr
            exact CardinalNatural.Peano.lt_of_succ_lt_succ h

theorem isLessThan_eq_true_iff_lessThan (x y : Decimal) :
  isLessThan x y = true ↔ LessThan x y := by
  unfold isLessThan
  generalize h_pad : Sequences.List.padAtStartToSameLength x.val y.val CardinalNatural.Peano.zero = padded
  cases padded with
  | mk x' y' =>
    have h_shape : Sequences.List.SameLength x' y' := by
      have h_same := Sequences.List.padAtStartToSameLength_sameLength x.val y.val CardinalNatural.Peano.zero
      rw [h_pad] at h_same
      exact h_same
    have h_padded_values : toCardinalList x' = toCardinalList x.val ∧ toCardinalList y' = toCardinalList y.val := by
      unfold Sequences.List.padAtStartToSameLength at h_pad
      dsimp only at h_pad
      split at h_pad
      · cases h_pad
        constructor
        · rfl
        · exact padAtStart_zero_toCardinalList y.val _
      · cases h_pad
        constructor
        · exact padAtStart_zero_toCardinalList x.val _
        · rfl
    have h_all_x : AllLessThanTen x' := by
      unfold Sequences.List.padAtStartToSameLength at h_pad
      dsimp only at h_pad
      split at h_pad
      · cases h_pad
        exact x.property.left
      · cases h_pad
        apply padAtStart_allLessThanTen
        · exact x.property.left
        · exact CardinalNatural.Peano.zero_lt_ten
    have h_all_y : AllLessThanTen y' := by
      unfold Sequences.List.padAtStartToSameLength at h_pad
      dsimp only at h_pad
      split at h_pad
      · cases h_pad
        apply padAtStart_allLessThanTen
        · exact y.property.left
        · exact CardinalNatural.Peano.zero_lt_ten
      · cases h_pad
        exact y.property.left
    have h_lex := isLessThanAlignedLists_eq_true_iff_nat_lt h_shape h_all_x h_all_y
    constructor
    · intro h_bool
      have h_nat := h_lex.mp h_bool
      have h_card_nat : (toCardinalList x.val).toNat < (toCardinalList y.val).toNat := by
        rw [← h_padded_values.left, ← h_padded_values.right]
        repeat rw [toCardinalList_toNat]
        exact h_nat
      have h_card : toCardinalList x.val < toCardinalList y.val := cardinal_lt_of_toNat_lt h_card_nat
      unfold LessThan toPeano
      exact (cardinal_lt_toOrdinal_iff _ _).mpr h_card
    · intro h_less
      have h_card : toCardinalList x.val < toCardinalList y.val := by
        unfold LessThan toPeano at h_less
        exact (cardinal_lt_toOrdinal_iff _ _).mp h_less
      have h_nat : toNatListHelper x' 0 < toNatListHelper y' 0 := by
        rw [← toCardinalList_toNat x', ← toCardinalList_toNat y']
        rw [h_padded_values.left, h_padded_values.right]
        exact cardinal_lt_toNat h_card
      exact h_lex.mpr h_nat

theorem isLessThan_iff_lessThan (x y : Decimal) :
  isLessThan x y ↔ LessThan x y := by
  exact isLessThan_eq_true_iff_lessThan x y

end Decimal

end ZeroMath.Numbers.OrdinalNatural
