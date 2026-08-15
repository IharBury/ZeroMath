import ZeroMath.Numbers.CardinalNatural.Peano
import ZeroMath.Numbers.Digits.Decimal
import ZeroMath.Numbers.Digits.Decimal.Lists
import ZeroMath.Numbers.Integer.Peano
import ZeroMath.Sequences.List

namespace ZeroMath.Numbers.OrdinalNatural

namespace Decimal

abbrev Digit := Digits.Decimal

end Decimal

def Decimal := Digits.NonZeroList

instance : DecidableEq Decimal :=
  fun a b =>
    match decEq a.val b.val with
    | isTrue h => isTrue (Subtype.ext h)
    | isFalse h => isFalse (fun h' => h (congrArg Subtype.val h'))

namespace Decimal

export Digits (
  zeroDigit oneDigit twoDigit threeDigit fourDigit
  fiveDigit sixDigit sevenDigit eightDigit nineDigit
  DigitIsNonZero
  digit_val_successor_le_ten digit_val_le_ten digit_val_eq_nine_of_not_successor_lt_ten
  subtract_ten_lt_ten digit_sum_lt_twenty digit_carry_lt_twenty digit_cases
  successorList predecessorList subtractAlignedLists
  LessThanAlignedLists isLessThanAlignedLists
  isLessThanAlignedLists_iff_lessThanAlignedLists LessThanAlignedLists_congr
  addAlignedLists addAlignedLists_commutative
  addPartialListDigit addListDigit multiplyDigitsPeano multiplyDigits
  addListDigit_multiplyDigits_ne_empty addListDigit_multiplyDigits_not_three_or_more
  multiplyPartialListByDigit multiplyListByDigit multiplyList
  HasNonZero AllZero decidableAllZero
  allZero_of_predecessorList_borrow_true successorList_predecessorList
  successorList_ne_empty_of_carry_false predecessorList_ne_empty_of_borrow_false
  hasNonZero_ne_empty length_ne_zero_of_hasNonZero hasNonZero hasNonZero_tail_of_zero_first NonZeroList
  hasNonZero_normalizeList toCardinalNaturalPeano
  toCardinalNaturalPeano_acc_split toCardinalNaturalPeano_firstElement
  toCardinalNaturalPeano_padAtStart_zeroDigit
  toCardinalNaturalPeano_padAtStartToSameLength_first
  toCardinalNaturalPeano_padAtStartToSameLength_second
  toCardinalNaturalPeano_lt_tenPower
  LessThanAlignedLists_toCardinalNaturalPeano_lt
  LessThanAlignedLists_of_toCardinalNaturalPeano_lt
  toCardinalNaturalPeano_injective_sameLength toCardinalNaturalPeano_padAtEnd
  toCardinalNaturalPeano_addAlignedLists_result toCardinalNaturalPeano_addListDigit
  toCardinalNaturalPeano_multiplyDigitsPeano toCardinalNaturalPeano_multiplyDigits
  toCardinalNaturalPeano_addListDigit_multiplyDigits
  toCardinalNaturalPeano_multiplyListByDigit
  addPartialListDigit_specification addAlignedLists_specification
  multiplyPartialListByDigit_specification multiplyList_specification
  addAlignedLists_eq_of_swapped addAlignedLists_after_padding_commutative
  subtractAlignedLists_borrow_false_of_lessThan
  toCardinalNaturalPeano_eq_zero_of_isEmpty
  isLessThanLists subtractLists
  isLessThanLists_iff_toCardinalNaturalPeano_lt isLessThanLists_eq_false_iff_not_lt
  subtractLists_specification
  findQuotientDigitAuxiliary findQuotientDigit
  findQuotientDigitAuxiliary_specification findQuotientDigit_specification findQuotientDigit_nextRemainder_lt
  appendRootDigit appendRootDigit_toCardinalNaturalPeano
  listVal listVal_empty listVal_append listVal_append_zeroDigit listVal_appendRootDigit
  firstRootGroupSize firstRootGroupSize_ne_zero firstRootGroupSize_le firstRootGroupSize_mod
  rootPad
  findRootDigitAuxiliary findRootDigit rootWithRemainderAuxiliary
  divideWithRemainderAuxiliary
  toCardinalNaturalPeano_append
  divideWithRemainderAuxiliary_newQuotient_value divideWithRemainderAuxiliary_step_algebra
  divideWithRemainderAuxiliary_specification
  toCardinalNaturalPeano_ne_zero_of_acc_ne_zero
  toCardinalNaturalPeano_ge_tenPower_of_ne_zero
  toCardinalNaturalPeano_zero_of_allZero toCardinalNaturalPeano_normalizeList
  allZero_or_hasNonZero not_allZero_of_hasNonZero
  toCardinalNaturalPeano_ne_zero_of_hasNonZero
  toCardinalNaturalPeano_ne_zero_of_not_allZero
  hasNonZero_of_toCardinalNaturalPeano_ne_zero
  predecessorList_successorList
  subtractAlignedLists_specification_calc_false_true subtractAlignedLists_specification_calc_false_false
  subtractAlignedLists_specification_calc_true_true subtractAlignedLists_specification_calc_true_false
  subtractAlignedLists_specification subtractAlignedLists_borrow_false_of_not_lt
  successor_carry_accumulator successorList_toCardinalNaturalPeano
  padAtStartToSameLength_first_ne_empty padAtStartToSameLength_first_ne_empty_of_either
  addAlignedLists_first_ne_empty addAlignedLists_ne_empty
  subtractAlignedLists_first_ne_empty subtractAlignedLists_ne_empty
  subtractAlignedLists_borrow_false_of_eq
  multiplyPartialListByDigit_first_ne_empty multiplyListByDigit_ne_empty
  multiplyList_first_ne_empty
  hasNonZero_of_hasNonZero_bool hasNonZero_bool_eq_true_of_hasNonZero
  allZero_of_not_hasNonZero_bool
  hasNonZero_of_successorList_carry_true hasNonZero_of_successorList_carry_false
  hasNonZero_padAtStartToSameLength_first
  addAlignedLists_digit_sum_ne_zero_of_left_ne_zero
  addAlignedLists_digit_sum_ne_zero_of_carry_true
  hasNonZero_of_addAlignedLists_carry_true hasNonZero_of_addAlignedLists_carry_false
  hasNonZero_of_subtractAlignedLists_borrow_true
  hasNonZero_of_subtractAlignedLists_borrow_false_of_lessThan
  hasNonZero_multiplyList
  isNormalizedList isNormalizedNonZeroList
  normalizeList_isNormalized normalizeList_isNormalizedNonZero
  toCardinalNaturalPeano_lt_of_lessThanAlignedLists_padded
  lessThanAlignedLists_padded_of_toCardinalNaturalPeano_lt
  lessThanAlignedLists_padded_second_first_of_toCardinalNaturalPeano_lt
  padAtStartToSameLength_eq_of_toCardinalNaturalPeano_eq
  subtractAlignedLists_borrow_false_of_toCardinalNaturalPeano_eq
  subtractAlignedLists_borrow_true_of_toCardinalNaturalPeano_lt
  addLists addLists_of_aligned_result addLists_commutative
  addLists_ne_empty hasNonZero_addLists toCardinalNaturalPeano_addLists
  empty_of_predecessorList_borrow_true_allZero successorList_specification
  toCardinalNaturalPeano_of_successorList
  not_allZero_normalizeList_of_not_allZero successorList_carry_false_of_allZero
  not_allZero_cons_zero_of_successorList_carry predecessorList_of_successorList_carry
  normalizeList_of_successorList_allZero
  toCardinalNaturalPeano_even_iff_lastElement
  toCardinalNaturalPeano_lt_ten_multiply_tenPower
  leadingDigit_ne_zero_of_isNormalizedNonZeroList
  leadingDigit_ne_zero_of_isNormalizedList_ne_zero
  eq_zeroDigit_singleton_of_isNormalizedList_toCardinalNaturalPeano_zero
  toCardinalNaturalPeano_injective_of_leading_ne_zero
  RepresentsOne decidableRepresentsOne
  representsOne_of_predecessorList_borrow_false_allZero
  hasNonZero_of_representsOne normalizeList_eq_oneDigit_of_representsOne
  hasNonZero_of_predecessorList_borrow_false_of_not_representsOne)

def one : Decimal :=
  ⟨Sequences.List.firstElement ⟨CardinalNatural.Peano.one, CardinalNatural.Peano.one_lt_ten⟩ Sequences.List.empty, by
    apply Sequences.List.AnyElement.first
    intro h
    cases h⟩

def isNormalized (d : Decimal) : Bool := isNormalizedNonZeroList d.val

def normalize (a : Decimal) : Decimal :=
  ⟨(Digits.normalizeList a.val (hasNonZero_ne_empty a.property)).val, hasNonZero_normalizeList a.property⟩


def Equivalent (a b : Decimal) : Prop := a.normalize = b.normalize

instance : Setoid Decimal where
  r := Equivalent
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h1 h2 => h1.trans h2
  }
instance (x y : Decimal) : Decidable (x ≈ y) :=

  inferInstanceAs (Decidable (x.normalize = y.normalize))

def toCardinalPeano (a : Decimal) : CardinalNatural.Peano :=
  toCardinalNaturalPeano a.val CardinalNatural.Peano.zero

theorem normalizeList_toCardinalPeano (a : Sequences.List Digit) (h : HasNonZero a) :
  toCardinalPeano ⟨(Digits.normalizeList a (hasNonZero_ne_empty h)).val, hasNonZero_normalizeList h⟩ =
    toCardinalNaturalPeano a CardinalNatural.Peano.zero :=
  Digits.toCardinalNaturalPeano_normalizeList a (hasNonZero_ne_empty h)

theorem toCardinalPeano_ne_zero (a : Decimal) :
  toCardinalPeano a ≠ CardinalNatural.Peano.zero := by
  exact toCardinalNaturalPeano_ne_zero_of_hasNonZero a.val CardinalNatural.Peano.zero a.property

def toPeano (a : Decimal) : OrdinalNatural.Peano :=
  (toCardinalPeano a).toOrdinal (toCardinalPeano_ne_zero a)

theorem normalize_toPeano (x : Decimal) : x.normalize.toPeano = x.toPeano := by
  unfold toPeano
  apply CardinalNatural.Peano.toOrdinal_congr
  unfold normalize
  exact normalizeList_toCardinalPeano x.val x.property

theorem toPeano_eq_of_equivalent {a b : Decimal} (h : a ≈ b) :
  a.toPeano = b.toPeano := by
  have h_eq : a.normalize = b.normalize := h
  rw [← normalize_toPeano a, ← normalize_toPeano b, h_eq]

/-- Embed an ordinal Decimal as a positive integer Peano number. -/
def toIntegerPeano (a : Decimal) : Integer.Peano :=
  Integer.Peano.positive a.toPeano

theorem zero_lt_toIntegerPeano (a : Decimal) :
    Integer.Peano.zero < toIntegerPeano a :=
  Integer.Peano.LessThan.zero_less_than_positive

theorem toIntegerPeano_eq_of_equivalent {a b : Decimal} (h : a ≈ b) :
    toIntegerPeano a = toIntegerPeano b :=
  congrArg Integer.Peano.positive (toPeano_eq_of_equivalent h)

def successor (a : Decimal) : Decimal :=
  match h : successorList a.val with
  | ⟨digits, true⟩ =>
    ⟨Sequences.List.firstElement ⟨CardinalNatural.Peano.one, CardinalNatural.Peano.one_lt_ten⟩ digits, hasNonZero_of_successorList_carry_true h⟩
  | ⟨digits, false⟩ =>
    ⟨digits, hasNonZero_of_successorList_carry_false a.property h⟩

def two : Decimal := successor one

theorem normalizeList_eq_one_of_representsOne {a : Sequences.List Digit}
    (h : RepresentsOne a) :
    (⟨(Digits.normalizeList a (hasNonZero_ne_empty (hasNonZero_of_representsOne h))).val,
        hasNonZero_normalizeList (hasNonZero_of_representsOne h)⟩ : Decimal) = one :=
  Subtype.ext (normalizeList_eq_oneDigit_of_representsOne h)

theorem equivalent_one_of_representsOne {a : Sequences.List Digit} (h_nonzero : HasNonZero a)
    (h : RepresentsOne a) : Equivalent ⟨a, h_nonzero⟩ one := by
  unfold Equivalent normalize
  exact normalizeList_eq_one_of_representsOne h

theorem hasNonZero_of_predecessorList_borrow_false {a digits : Sequences.List Digit}
    (h_nonzero : HasNonZero a) (h_not_one : ¬ Equivalent ⟨a, h_nonzero⟩ one)
    (h : predecessorList a = ⟨digits, false⟩) : HasNonZero digits :=
  hasNonZero_of_predecessorList_borrow_false_of_not_representsOne h (fun hrep =>
    h_not_one (equivalent_one_of_representsOne h_nonzero hrep))

def predecessor (a : Decimal) (h : ¬ a ≈ one) : Decimal :=
  match h_result : predecessorList a.val with
  | ⟨_, true⟩ =>
      False.elim (not_allZero_of_hasNonZero a.property
        (allZero_of_predecessorList_borrow_true h_result))
  | ⟨digits, false⟩ =>
      ⟨digits, hasNonZero_of_predecessorList_borrow_false a.property h h_result⟩

theorem successor_predecessor (d : Decimal) (h : ¬ d ≈ one) :
  (d.predecessor h).successor = d := by
  cases h_predecessor : predecessorList d.val with
  | mk digits borrow =>
      cases borrow with
      | true =>
          exact False.elim (not_allZero_of_hasNonZero d.property
            (allZero_of_predecessorList_borrow_true h_predecessor))
      | false =>
          apply Subtype.ext
          have h_predecessor_val : (d.predecessor h).val = digits := by
            unfold predecessor
            split
            · next _ h_result =>
                rw [h_predecessor] at h_result
                cases h_result
            · next resultDigits h_result =>
                rw [h_predecessor] at h_result
                injection h_result with h_digits
                exact h_digits.symm
          have h_successor := successorList_predecessorList d.val
          rw [h_predecessor] at h_successor
          dsimp only at h_successor
          have h_successor_predecessor :
              successorList (d.predecessor h).val = ⟨d.val, false⟩ := by
            rw [h_predecessor_val, h_successor]
          unfold successor
          split
          · next _ h_result =>
              rw [h_successor_predecessor] at h_result
              cases h_result
          · next resultDigits h_result =>
              rw [h_successor_predecessor] at h_result
              injection h_result with h_digits
              exact h_digits.symm

def isLessThan (x y : Decimal) : Bool :=
  let pair := Sequences.List.padAtStartToSameLength x.val y.val zeroDigit
  isLessThanAlignedLists pair.1 pair.2
    (Sequences.List.padAtStartToSameLength_sameLength x.val y.val zeroDigit)
def LessThan (x y : Decimal) : Prop :=
  x.toPeano < y.toPeano

theorem toCardinalPeano_lt_of_lessThanAlignedLists_padded {a b : Decimal}
    (h : LessThanAlignedLists
      (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).1
      (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).2
      (Sequences.List.padAtStartToSameLength_sameLength a.val b.val zeroDigit)) :
    toCardinalPeano a < toCardinalPeano b :=
  toCardinalNaturalPeano_lt_of_lessThanAlignedLists_padded a.val b.val h

theorem lessThanAlignedLists_padded_of_toCardinalPeano_lt {a b : Decimal}
    (h : toCardinalPeano a < toCardinalPeano b) :
    LessThanAlignedLists
      (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).1
      (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).2
      (Sequences.List.padAtStartToSameLength_sameLength a.val b.val zeroDigit) :=
  lessThanAlignedLists_padded_of_toCardinalNaturalPeano_lt a.val b.val h

theorem toPeano_lt_iff_toCardinalPeano_lt (a b : Decimal) :
    a.toPeano < b.toPeano ↔ toCardinalPeano a < toCardinalPeano b := by
  constructor
  · intro h
    unfold toPeano at h
    exact CardinalNatural.Peano.lt_of_toOrdinal_lt
      (toCardinalPeano_ne_zero a) (toCardinalPeano_ne_zero b) h
  · intro h
    unfold toPeano
    exact CardinalNatural.Peano.toOrdinal_lt_of_lt
      (toCardinalPeano_ne_zero a) (toCardinalPeano_ne_zero b) h

theorem isLessThan_iff_lessThan (x y : Decimal) :
  isLessThan x y ↔ LessThan x y := by
  unfold isLessThan LessThan
  dsimp only
  constructor
  · intro h
    have h_aligned := (isLessThanAlignedLists_iff_lessThanAlignedLists _ _ _).mp h
    exact (toPeano_lt_iff_toCardinalPeano_lt x y).mpr
      (toCardinalPeano_lt_of_lessThanAlignedLists_padded h_aligned)
  · intro h
    exact (isLessThanAlignedLists_iff_lessThanAlignedLists _ _ _).mpr
      (lessThanAlignedLists_padded_of_toCardinalPeano_lt
        ((toPeano_lt_iff_toCardinalPeano_lt x y).mp h))

instance : LT Decimal where
  lt := LessThan

instance (x y : Decimal) : Decidable (x < y) :=
  if h : isLessThan x y then
    isTrue (isLessThan_iff_lessThan x y |>.mp h)
  else
    isFalse (fun h''' => h (isLessThan_iff_lessThan x y |>.mpr h'''))

def LessThanOrEquivalent (x y : Decimal) : Prop := x < y ∨ x ≈ y

instance : LE Decimal where
  le := LessThanOrEquivalent

instance (x y : Decimal) : Decidable (x ≤ y) :=
  if h_lt : x < y then
    isTrue (Or.inl h_lt)
  else if h_eq : x ≈ y then
    isTrue (Or.inr h_eq)
  else
    isFalse (fun h => match h with
      | Or.inl h_lt' => h_lt h_lt'
      | Or.inr h_eq' => h_eq h_eq')

theorem lessThanAlignedLists_padded_of_lt {a b : Decimal} (h : b < a) :
  let pair := Sequences.List.padAtStartToSameLength a.val b.val zeroDigit
  LessThanAlignedLists pair.2 pair.1
    (Sequences.List.sameLength_commutative
      (Sequences.List.padAtStartToSameLength_sameLength a.val b.val zeroDigit)) :=
  lessThanAlignedLists_padded_second_first_of_toCardinalNaturalPeano_lt a.val b.val
    ((toPeano_lt_iff_toCardinalPeano_lt b a).mp h)

def subtract (a b : Decimal) (h : b < a) : Decimal :=
  let pair := Sequences.List.padAtStartToSameLength a.val b.val zeroDigit
  let h_same : Sequences.List.SameLength pair.1 pair.2 :=
    Sequences.List.padAtStartToSameLength_sameLength a.val b.val zeroDigit
  match h_subtract : Decimal.subtractAlignedLists pair.1 pair.2 h_same with
  | ⟨digits, borrow⟩ =>
      if h2 : borrow then
        False.elim (by
          have h_borrow_false := subtractAlignedLists_borrow_false_of_lessThan
            h_same (lessThanAlignedLists_padded_of_lt h)
          rw [h_subtract] at h_borrow_false
          dsimp only at h_borrow_false
          rw [h2] at h_borrow_false
          cases h_borrow_false)
      else
        ⟨digits, by
          exact hasNonZero_of_subtractAlignedLists_borrow_false_of_lessThan
            h_same (lessThanAlignedLists_padded_of_lt h)
            (by
              rw [h_subtract]
              cases borrow with
              | false => rfl
              | true => exact False.elim (h2 rfl))
        ⟩

def add (a b : Decimal) : Decimal :=
  ⟨addLists a.val b.val, hasNonZero_addLists a.property⟩

instance : Add Decimal where
  add := add

theorem add_val_of_aligned_result (a b : Decimal) (digits : Sequences.List Digit) (carry : Bool)
  (h : addAlignedLists
    (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).1
    (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).2
    (Sequences.List.padAtStartToSameLength_sameLength a.val b.val zeroDigit) = ⟨digits, carry⟩) :
  (a + b).val = if carry then
    Sequences.List.firstElement oneDigit digits
  else digits := by
  change (add a b).val = _
  unfold add
  exact addLists_of_aligned_result a.val b.val digits carry h

theorem add_commutative (a b : Decimal) : a + b = b + a := by
  apply Subtype.ext
  exact addLists_commutative a.val b.val

theorem equivalent_add_commutative (a b : Decimal) : a + b ≈ b + a := by
  rw [add_commutative]
  rfl

theorem toCardinalPeano_successor (a : Decimal) :
  toCardinalPeano (successor a) = (toCardinalPeano a).successor := by
  unfold successor toCardinalPeano
  split
  · next digits h_successor =>
      have h_spec := successorList_specification a.val
      rw [h_successor] at h_spec
      dsimp only at h_spec
      obtain ⟨h_length, h_value⟩ := h_spec
      simp at h_value
      rw [toCardinalNaturalPeano_firstElement, h_length, CardinalNatural.Peano.one_multiply]
      calc
        _ = toCardinalNaturalPeano digits CardinalNatural.Peano.zero +
              CardinalNatural.Peano.tenPower a.val.length := CardinalNatural.Peano.add_commutative _ _
        _ = toCardinalNaturalPeano a.val CardinalNatural.Peano.zero + CardinalNatural.Peano.one := h_value
        _ = (toCardinalNaturalPeano a.val CardinalNatural.Peano.zero).successor := rfl
  · next digits h_successor =>
      have h_spec := successorList_specification a.val
      rw [h_successor] at h_spec
      dsimp only at h_spec
      simpa [CardinalNatural.Peano.add_one] using h_spec.2

theorem successor_toPeano (x : Decimal) :
  x.successor.toPeano = x.toPeano.successor := by
  unfold toPeano
  calc
    _ = CardinalNatural.Peano.toOrdinal (toCardinalPeano x).successor
        (CardinalNatural.Peano.successor_ne_zero _) :=
      CardinalNatural.Peano.toOrdinal_congr (toCardinalPeano_successor x) _ _
    _ = _ := CardinalNatural.Peano.toOrdinal_successor _ _ (toCardinalPeano_ne_zero x)

theorem predecessor_toPeano (x : Decimal) (h : ¬ x ≈ one) :
  ∃ h2, toPeano (x.predecessor h) = x.toPeano.predecessor h2 := by
  let y := toPeano (x.predecessor h)
  have h_successor : x.toPeano = OrdinalNatural.Peano.successor y := by
    rw [← successor_toPeano (x.predecessor h)]
    exact congrArg toPeano (successor_predecessor x h).symm
  cases h_toPeano : x.toPeano with
  | one =>
      rw [h_toPeano] at h_successor
      cases h_successor
  | successor p =>
      have h2 : OrdinalNatural.Peano.successor p ≠ OrdinalNatural.Peano.one := by
        intro h_one
        cases h_one
      exists h2
      have h_y : y = p := by
        rw [h_toPeano] at h_successor
        injection h_successor with h_p
        exact h_p.symm
      exact h_y

theorem successor_ne_one (x : Decimal) : ¬ x.successor ≈ one := by
  intro h_one
  have h_toPeano := toPeano_eq_of_equivalent h_one
  rw [successor_toPeano] at h_toPeano
  cases h_toPeano

theorem toCardinalPeano_add (x y : Decimal) :
  toCardinalPeano (x + y) = toCardinalPeano x + toCardinalPeano y := by
  change toCardinalNaturalPeano (add x y).val CardinalNatural.Peano.zero =
    toCardinalNaturalPeano x.val CardinalNatural.Peano.zero +
      toCardinalNaturalPeano y.val CardinalNatural.Peano.zero
  unfold add
  exact toCardinalNaturalPeano_addLists x.val y.val


theorem toCardinalPeano_subtract (x y : Decimal) (h : y < x) :
  toCardinalPeano (subtract x y h) + toCardinalPeano y = toCardinalPeano x := by
  change toCardinalNaturalPeano (subtract x y h).val CardinalNatural.Peano.zero +
      toCardinalNaturalPeano y.val CardinalNatural.Peano.zero =
    toCardinalNaturalPeano x.val CardinalNatural.Peano.zero
  unfold subtract
  dsimp only
  let pair := Sequences.List.padAtStartToSameLength x.val y.val zeroDigit
  let h_same : Sequences.List.SameLength pair.1 pair.2 :=
    Sequences.List.padAtStartToSameLength_sameLength x.val y.val zeroDigit
  by_cases h_borrow : (subtractAlignedLists pair.1 pair.2 h_same).2 = true
  · simp [pair, h_borrow]
    have h_borrow_false := subtractAlignedLists_borrow_false_of_lessThan
      h_same (lessThanAlignedLists_padded_of_lt h)
    exact False.elim (by
      rw [h_borrow] at h_borrow_false
      cases h_borrow_false)
  · simp [pair, h_borrow]
    cases h_subtract : subtractAlignedLists pair.1 pair.2 h_same with
    | mk digits borrow =>
        have h_spec := subtractAlignedLists_specification h_same
        rw [h_subtract] at h_spec
        dsimp only at h_spec
        obtain ⟨_, h_value⟩ := h_spec
        cases borrow with
        | false =>
            simp at h_value
            rw [← toCardinalNaturalPeano_padAtStartToSameLength_first x.val y.val,
              ← toCardinalNaturalPeano_padAtStartToSameLength_second x.val y.val]
            change toCardinalNaturalPeano digits CardinalNatural.Peano.zero +
                toCardinalNaturalPeano pair.2 CardinalNatural.Peano.zero =
              toCardinalNaturalPeano pair.1 CardinalNatural.Peano.zero
            exact h_value
        | true =>
            rw [h_subtract] at h_borrow
            exact False.elim (h_borrow rfl)

theorem add_toPeano (x y : Decimal) :
  (x + y).toPeano = x.toPeano + y.toPeano := by
  apply CardinalNatural.Peano.eq_of_fromOrdinal_eq
  rw [CardinalNatural.Peano.fromOrdinal_add]
  simp only [toPeano, CardinalNatural.Peano.fromOrdinal_toOrdinal]
  exact toCardinalPeano_add x y

theorem toCardinalPeano_lt_of_lt {a b : Decimal} (h : a < b) :
    toCardinalPeano a < toCardinalPeano b :=
  (toPeano_lt_iff_toCardinalPeano_lt a b).mp h

theorem toPeano_lt_of_lt {a b : Decimal} (h : a < b) : a.toPeano < b.toPeano :=
  h

theorem lt_of_toCardinalPeano_lt {a b : Decimal}
    (h : toCardinalPeano a < toCardinalPeano b) : a < b :=
  (toPeano_lt_iff_toCardinalPeano_lt a b).mpr h

theorem toCardinalPeano_eq_of_equivalent {a b : Decimal} (h : a ≈ b) :
    toCardinalPeano a = toCardinalPeano b := by
  have ha : toCardinalPeano a.normalize = toCardinalPeano a := by
    unfold toCardinalPeano normalize
    exact normalizeList_toCardinalPeano a.val a.property
  have hb : toCardinalPeano b.normalize = toCardinalPeano b := by
    unfold toCardinalPeano normalize
    exact normalizeList_toCardinalPeano b.val b.property
  rw [← ha, ← hb, h]

theorem lt_trans {a b c : Decimal} (h1 : a < b) (h2 : b < c) : a < c := by
  exact lt_of_toCardinalPeano_lt
    (CardinalNatural.Peano.lt_trans (toCardinalPeano_lt_of_lt h1)
      (toCardinalPeano_lt_of_lt h2))

theorem le_trans {a b c : Decimal} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  cases h1 with
  | inl hlt1 =>
      cases h2 with
      | inl hlt2 => exact Or.inl (lt_trans hlt1 hlt2)
      | inr heq2 =>
          apply Or.inl
          apply lt_of_toCardinalPeano_lt
          rw [← toCardinalPeano_eq_of_equivalent heq2]
          exact toCardinalPeano_lt_of_lt hlt1
  | inr heq1 =>
      cases h2 with
      | inl hlt2 =>
          apply Or.inl
          apply lt_of_toCardinalPeano_lt
          rw [toCardinalPeano_eq_of_equivalent heq1]
          exact toCardinalPeano_lt_of_lt hlt2
      | inr heq2 =>
          exact Or.inr (Setoid.trans heq1 heq2)

theorem normalize_injective {a b : Decimal}
    (ha : a.isNormalized = true) (hb : b.isNormalized = true)
    (heq : toCardinalPeano a = toCardinalPeano b) : a = b := by
  obtain ⟨val_a, prop_a⟩ := a
  obtain ⟨val_b, prop_b⟩ := b
  cases val_a with
  | empty => exact absurd rfl (hasNonZero_ne_empty prop_a)
  | firstElement da das =>
    cases val_b with
    | empty => exact absurd rfl (hasNonZero_ne_empty prop_b)
    | firstElement db dbs =>
      exact Subtype.ext
        (toCardinalNaturalPeano_injective_of_leading_ne_zero
          (leadingDigit_ne_zero_of_isNormalizedNonZeroList
            (by simpa [isNormalized] using ha))
          (leadingDigit_ne_zero_of_isNormalizedNonZeroList
            (by simpa [isNormalized] using hb))
          (by simpa [toCardinalPeano] using heq))

-- normalize produces a normalized Decimal
theorem normalize_isNormalized (d : Decimal) : d.normalize.isNormalized = true := by
  unfold normalize isNormalized
  exact Digits.normalizeList_isNormalizedNonZero d.property

theorem equivalent_of_toPeano_eq {a b : Decimal} (h : a.toPeano = b.toPeano) : a ≈ b := by
  have h_card : toCardinalPeano a = toCardinalPeano b := by
    have := congrArg CardinalNatural.Peano.fromOrdinal h
    simp only [toPeano] at this
    rwa [CardinalNatural.Peano.fromOrdinal_toOrdinal,
         CardinalNatural.Peano.fromOrdinal_toOrdinal] at this
  show a.normalize = b.normalize
  have ha_norm : toCardinalPeano a.normalize = toCardinalPeano a := by
    unfold toCardinalPeano normalize
    exact normalizeList_toCardinalPeano a.val a.property
  have hb_norm : toCardinalPeano b.normalize = toCardinalPeano b := by
    unfold toCardinalPeano normalize
    exact normalizeList_toCardinalPeano b.val b.property
  have h_norm_card : toCardinalPeano a.normalize = toCardinalPeano b.normalize := by
    rw [ha_norm, hb_norm, h_card]
  exact normalize_injective (normalize_isNormalized a) (normalize_isNormalized b) h_norm_card

theorem predecessor_successor (x : Decimal) :
  ∃ h, predecessor x.successor h ≈ x := by
  have h : ¬ x.successor ≈ one := successor_ne_one x
  refine ⟨h, ?_⟩
  apply equivalent_of_toPeano_eq
  obtain ⟨h2, h_predecessor_toPeano⟩ := predecessor_toPeano x.successor h
  have h_successor_toPeano : x.successor.toPeano = x.toPeano.successor := successor_toPeano x
  have h2' : x.toPeano.successor ≠ OrdinalNatural.Peano.one := by
    intro h_one
    exact h2 (h_successor_toPeano.trans h_one)
  have h_predecessor_toPeano' :
      (predecessor x.successor h).toPeano = (x.toPeano.successor).predecessor h2' := by
    exact h_predecessor_toPeano.trans (Peano.predecessor_congr h2 h2' h_successor_toPeano)
  obtain ⟨h3, h_predecessor_successor⟩ := OrdinalNatural.Peano.predecessor_successor_eq x.toPeano
  have h_predecessor_congr :
      (x.toPeano.successor).predecessor h2' = (x.toPeano.successor).predecessor h3 :=
    Peano.predecessor_congr h2' h3 rfl
  exact h_predecessor_toPeano'.trans (h_predecessor_congr.trans h_predecessor_successor)

theorem equivalent_of_toCardinalPeano_eq {a b : Decimal}
    (h : toCardinalPeano a = toCardinalPeano b) : a ≈ b := by
  show a.normalize = b.normalize
  have ha_norm : toCardinalPeano a.normalize = toCardinalPeano a := by
    unfold toCardinalPeano normalize
    exact normalizeList_toCardinalPeano a.val a.property
  have hb_norm : toCardinalPeano b.normalize = toCardinalPeano b := by
    unfold toCardinalPeano normalize
    exact normalizeList_toCardinalPeano b.val b.property
  have h_norm_card : toCardinalPeano a.normalize = toCardinalPeano b.normalize := by
    rw [ha_norm, hb_norm, h]
  exact normalize_injective (normalize_isNormalized a) (normalize_isNormalized b) h_norm_card

theorem add_associative (a b c : Decimal) : a + b + c ≈ a + (b + c) := by
  apply equivalent_of_toCardinalPeano_eq
  rw [toCardinalPeano_add, toCardinalPeano_add, toCardinalPeano_add,
    toCardinalPeano_add, CardinalNatural.Peano.add_associative]

/-- Addition respects Decimal equivalence in both arguments. -/
theorem equivalent_add {a b c d : Decimal} (hab : a ≈ b) (hcd : c ≈ d) :
    a + c ≈ b + d := by
  apply equivalent_of_toPeano_eq
  rw [add_toPeano, add_toPeano, toPeano_eq_of_equivalent hab,
    toPeano_eq_of_equivalent hcd]

/-- Addition on the right respects Decimal equivalence. -/
theorem equivalent_add_right {a b c : Decimal} (h : a ≈ b) : a + c ≈ b + c :=
  equivalent_add h (Setoid.refl _)

theorem lt_add_right (a b : Decimal) : b < a + b := by
  apply lt_of_toCardinalPeano_lt
  rw [toCardinalPeano_add, CardinalNatural.Peano.add_commutative
    (toCardinalPeano a) (toCardinalPeano b)]
  exact CardinalNatural.Peano.lt_add_of_right_ne_zero
    (toCardinalPeano b) (toCardinalPeano a) (toCardinalPeano_ne_zero a)

theorem subtract_add_cancel (a b : Decimal) (h : b < a) :
  subtract a b h + b ≈ a := by
  apply equivalent_of_toCardinalPeano_eq
  rw [toCardinalPeano_add, toCardinalPeano_subtract a b h]

theorem add_subtract_cancel (a b : Decimal) :
  ∃ h, subtract (a + b) b h ≈ a := by
  let h : b < a + b := lt_add_right a b
  refine ⟨h, ?_⟩
  apply equivalent_of_toCardinalPeano_eq
  apply CardinalNatural.Peano.add_cancel_right
    (toCardinalPeano (subtract (a + b) b h)) (toCardinalPeano a) (toCardinalPeano b)
  rw [toCardinalPeano_subtract (a + b) b h, toCardinalPeano_add]

/-- Strict inequality precludes Decimal equivalence. -/
theorem not_equivalent_of_lt {a b : Decimal} (h : a < b) : ¬ a ≈ b := by
  intro heq
  have hlt : a.toPeano < b.toPeano := toPeano_lt_of_lt h
  rw [toPeano_eq_of_equivalent heq] at hlt
  exact Peano.not_lt_self _ hlt

theorem trichotomy (a b : Decimal) :
    ZeroMath.Logic.Trichotomy (a < b) (a ≈ b) (b < a) := by
  cases CardinalNatural.Peano.trichotomy (toCardinalPeano a) (toCardinalPeano b) with
  | first hlt hne hnlt_reverse =>
      exact ZeroMath.Logic.Trichotomy.first
        (lt_of_toCardinalPeano_lt hlt)
        (fun heq => hne (toCardinalPeano_eq_of_equivalent heq))
        (fun h_reverse => hnlt_reverse (toCardinalPeano_lt_of_lt h_reverse))
  | second heq hnlt_forward hnlt_reverse =>
      exact ZeroMath.Logic.Trichotomy.second
        (equivalent_of_toCardinalPeano_eq heq)
        (fun h_forward => hnlt_forward (toCardinalPeano_lt_of_lt h_forward))
        (fun h_reverse => hnlt_reverse (toCardinalPeano_lt_of_lt h_reverse))
  | third hlt_reverse hnlt_forward hne =>
      exact ZeroMath.Logic.Trichotomy.third
        (lt_of_toCardinalPeano_lt hlt_reverse)
        (fun h_forward => hnlt_forward (toCardinalPeano_lt_of_lt h_forward))
        (fun heq => hne (toCardinalPeano_eq_of_equivalent heq))

/-- Result of comparing two Decimal numbers, packaged with a proof of the relationship. -/
inductive Comparison (a b : Decimal) where
  | less : a < b → Comparison a b
  | equivalent : a ≈ b → Comparison a b
  | greater : b < a → Comparison a b

/-- Compare two Decimal numbers, returning less, equivalent, or greater together with a proof. -/
def compare (a b : Decimal) : Comparison a b :=
  match Peano.compare a.toPeano b.toPeano with
  | Peano.Comparison.less h => Comparison.less h
  | Peano.Comparison.equal h => Comparison.equivalent (equivalent_of_toPeano_eq h)
  | Peano.Comparison.greater h => Comparison.greater h

def subtractWithRemainder (a b : Decimal) : Decimal × Option Decimal :=
  let pair := Sequences.List.padAtStartToSameLength a.val b.val zeroDigit
  let h_same : Sequences.List.SameLength pair.1 pair.2 :=
    Sequences.List.padAtStartToSameLength_sameLength a.val b.val zeroDigit
  let subres := subtractAlignedLists pair.1 pair.2 h_same
  if h_borrow : subres.2 = true then
      let digits := subres.1
      let bs := successor b
      have h_lt : a < bs := by
        apply lt_of_toCardinalPeano_lt
        rw [toCardinalPeano_successor]
        have h_ap : toCardinalPeano a = toCardinalNaturalPeano pair.1 CardinalNatural.Peano.zero := by
          unfold toCardinalPeano
          exact (toCardinalNaturalPeano_padAtStartToSameLength_first a.val b.val).symm
        have h_bp : toCardinalPeano b = toCardinalNaturalPeano pair.2 CardinalNatural.Peano.zero := by
          unfold toCardinalPeano
          exact (toCardinalNaturalPeano_padAtStartToSameLength_second a.val b.val).symm
        have h_d_lt : toCardinalNaturalPeano digits CardinalNatural.Peano.zero <
            CardinalNatural.Peano.tenPower pair.1.length := by
          have h_len : digits.length = pair.1.length := by
            have sp := subtractAlignedLists_specification h_same
            have h_call : subres = subtractAlignedLists pair.1 pair.2 h_same := rfl
            rw [← h_call] at sp
            simp [h_borrow] at sp
            obtain ⟨hlen, _⟩ := sp
            exact hlen
          have t := toCardinalNaturalPeano_lt_tenPower digits
          rw [h_len] at t
          exact t
        have hb : b < bs := by
          apply lt_of_toCardinalPeano_lt
          rw [toCardinalPeano_successor]
          exact CardinalNatural.Peano.LessThan.base
        have h_list_lt : toCardinalNaturalPeano pair.1 CardinalNatural.Peano.zero <
            toCardinalNaturalPeano pair.2 CardinalNatural.Peano.zero := by
          have sp_val := (subtractAlignedLists_specification h_same).2
          have h_call : subres = subtractAlignedLists pair.1 pair.2 h_same := rfl
          rw [← h_call] at sp_val
          simp [h_borrow] at sp_val
          have ineq : toCardinalNaturalPeano pair.1 CardinalNatural.Peano.zero + CardinalNatural.Peano.tenPower pair.1.length <
                CardinalNatural.Peano.tenPower pair.1.length + toCardinalNaturalPeano pair.2 CardinalNatural.Peano.zero := by
            rw [← sp_val]
            exact CardinalNatural.Peano.add_lt_add_right h_d_lt _
          rw [CardinalNatural.Peano.add_commutative (CardinalNatural.Peano.tenPower _) _] at ineq
          exact CardinalNatural.Peano.add_lt_cancel_right ineq
        have h_card_a_lt_bsucc : toCardinalPeano a < (toCardinalPeano b).successor := by
          rw [h_ap, h_bp]
          have h_b_lt_bsucc : toCardinalNaturalPeano pair.2 CardinalNatural.Peano.zero <
              (toCardinalNaturalPeano pair.2 CardinalNatural.Peano.zero).successor :=
            CardinalNatural.Peano.LessThan.base
          exact CardinalNatural.Peano.lt_trans h_list_lt h_b_lt_bsucc
        exact h_card_a_lt_bsucc
      let r := subtract bs a h_lt
      ⟨one, some r⟩
  else
      let digits := subres.1
      if h_nzb : hasNonZero digits then
        ⟨⟨digits, hasNonZero_of_hasNonZero_bool h_nzb⟩, none⟩
      else
        ⟨one, some one⟩

def trySubtract (a b : Decimal) : Option Decimal :=
  match subtractWithRemainder a b with
  | ⟨diff, none⟩ => some diff
  | ⟨_, some _⟩ => none

def fromPeano : Peano → Decimal
  | Peano.one => Decimal.one
  | Peano.successor p => successor (fromPeano p)

theorem toPeano_fromPeano (x : Peano) :
  toPeano (fromPeano x) = x := by
  induction x with
  | one => rfl
  | successor x ih =>
      have ih_card := congrArg CardinalNatural.Peano.fromOrdinal ih
      simp only [toPeano, CardinalNatural.Peano.fromOrdinal_toOrdinal] at ih_card
      unfold fromPeano
      apply CardinalNatural.Peano.eq_of_fromOrdinal_eq
      simp only [toPeano, CardinalNatural.Peano.fromOrdinal_toOrdinal,
        CardinalNatural.Peano.fromOrdinal, toCardinalPeano_successor]
      exact congrArg CardinalNatural.Peano.successor ih_card

/-- Convert a positive cardinal Peano natural to an ordinal Decimal. -/
def fromCardinalPeano : (a : CardinalNatural.Peano) →
    a ≠ CardinalNatural.Peano.zero → Decimal
  | .zero, h => False.elim (h rfl)
  | .successor .zero, _ => one
  | .successor (.successor n), _ =>
      successor (fromCardinalPeano n.successor (CardinalNatural.Peano.successor_ne_zero n))

theorem toPeano_fromCardinalPeano (a : CardinalNatural.Peano)
    (h : a ≠ CardinalNatural.Peano.zero) :
    toPeano (fromCardinalPeano a h) = a.toOrdinal h := by
  match a with
  | .zero => contradiction
  | .successor .zero => rfl
  | .successor (.successor n) =>
      have hpred : n.successor ≠ CardinalNatural.Peano.zero :=
        CardinalNatural.Peano.successor_ne_zero n
      have ih := toPeano_fromCardinalPeano n.successor hpred
      change toPeano (successor (fromCardinalPeano n.successor hpred)) = _
      rw [successor_toPeano, ih]
      exact (CardinalNatural.Peano.toOrdinal_successor n.successor h hpred).symm

theorem toCardinalPeano_fromCardinalPeano (a : CardinalNatural.Peano)
    (h : a ≠ CardinalNatural.Peano.zero) :
    toCardinalPeano (fromCardinalPeano a h) = a := by
  have hfrom :=
    congrArg CardinalNatural.Peano.fromOrdinal (toPeano_fromCardinalPeano a h)
  simp only [toPeano, CardinalNatural.Peano.fromOrdinal_toOrdinal] at hfrom
  exact hfrom

theorem fromCardinalPeano_toCardinalPeano (x : Decimal) :
    fromCardinalPeano (toCardinalPeano x) (toCardinalPeano_ne_zero x) ≈ x := by
  apply equivalent_of_toPeano_eq
  exact toPeano_fromCardinalPeano (toCardinalPeano x) (toCardinalPeano_ne_zero x)

/-- Convert a positive integer Peano number to an ordinal Decimal. -/
def fromIntegerPeano : (a : Integer.Peano) →
    Integer.Peano.zero < a → Decimal
  | .positive .one, _ => one
  | .positive (.successor n), _ =>
      successor (fromIntegerPeano (.positive n)
        Integer.Peano.LessThan.zero_less_than_positive)
  | .zero, h => False.elim (by cases h)
  | .negative _, h => False.elim (by cases h)

theorem toPeano_fromIntegerPeano (a : Integer.Peano)
    (h : Integer.Peano.zero < a) :
    toPeano (fromIntegerPeano a h) = Integer.Peano.toOrdinalNatural a h := by
  match a with
  | .positive .one =>
      simp only [fromIntegerPeano]
      exact toPeano_fromPeano Peano.one
  | .positive (.successor n) =>
      have hpred : Integer.Peano.zero < Integer.Peano.positive n :=
        Integer.Peano.LessThan.zero_less_than_positive
      have ih := toPeano_fromIntegerPeano (.positive n) hpred
      simp only [fromIntegerPeano]
      rw [successor_toPeano, ih]
      rfl
  | .zero => cases h
  | .negative _ => cases h

theorem toIntegerPeano_fromIntegerPeano (a : Integer.Peano)
    (h : Integer.Peano.zero < a) :
    toIntegerPeano (fromIntegerPeano a h) = a := by
  rw [toIntegerPeano, toPeano_fromIntegerPeano a h]
  exact (Integer.Peano.eq_positive_of_positive h).symm

theorem fromIntegerPeano_toIntegerPeano (x : Decimal) :
    fromIntegerPeano (toIntegerPeano x) (zero_lt_toIntegerPeano x) ≈ x := by
  apply equivalent_of_toPeano_eq
  exact toPeano_fromIntegerPeano (toIntegerPeano x) (zero_lt_toIntegerPeano x)

theorem subtract_toPeano (x y : Decimal) (h : y < x) :
  ∃ h2, toPeano (subtract x y h) = Peano.subtract x.toPeano y.toPeano h2 := by
  let h2 := toPeano_lt_of_lt h
  exists h2
  have h_decimal_add : (subtract x y h + y).toPeano = x.toPeano := by
    apply toPeano_eq_of_equivalent
    apply equivalent_of_toCardinalPeano_eq
    rw [toCardinalPeano_add]
    exact toCardinalPeano_subtract x y h
  rw [add_toPeano] at h_decimal_add
  have h_peano_add : Peano.subtract x.toPeano y.toPeano h2 + y.toPeano = x.toPeano :=
    Peano.subtract_add_cancel x.toPeano y.toPeano h2
  exact Peano.add_cancel_right (toPeano (subtract x y h))
    (Peano.subtract x.toPeano y.toPeano h2) y.toPeano
    (h_decimal_add.trans h_peano_add.symm)

theorem toPeano_one : toPeano one = Peano.one := by
  simpa [fromPeano] using toPeano_fromPeano Peano.one

/-- An index is equivalent to `one` iff its Peano embedding is `one`. -/
theorem toPeano_eq_one_iff_equivalent_one (index : Decimal) :
    index.toPeano = Peano.one ↔ index ≈ one := by
  constructor
  · intro h
    exact equivalent_of_toPeano_eq (h.trans toPeano_one.symm)
  · intro h
    exact (toPeano_eq_of_equivalent h).trans toPeano_one

/-- When the index is not equivalent to `one`, it is the successor of its
predecessor in the Peano embedding. -/
theorem toPeano_eq_successor_predecessor_toPeano (index : Decimal) (h : ¬ index ≈ one) :
    index.toPeano = (index.predecessor h).toPeano.successor := by
  obtain ⟨hne, heq⟩ := predecessor_toPeano index h
  rw [heq, Peano.successor_predecessor_eq]

theorem peano_subtractWithRemainder_first_of_le {a b : Peano} (h : a ≤ b) :
    (Peano.subtractWithRemainder a b).1 = Peano.one := by
  rcases Peano.subtractWithRemainder_correct a b with h_le_side | h_gt_side
  · rcases h_le_side with ⟨_, ⟨_, h_eq⟩⟩
    simpa using congrArg Prod.fst h_eq
  · rcases h_gt_side with ⟨h_gt, _⟩
    cases h with
    | inl hlt => exact False.elim (Peano.not_lt_of_lt hlt h_gt)
    | inr heq =>
      rw [heq] at h_gt
      exact False.elim (Peano.not_lt_self b h_gt)

theorem peano_subtractWithRemainder_first_of_lt {a b : Peano} (h : b < a) :
    ∃ h2, (Peano.subtractWithRemainder a b).1 = Peano.subtract a b h2 := by
  rcases Peano.subtractWithRemainder_correct a b with h_le_side | h_gt_side
  · rcases h_le_side with ⟨h_le, ⟨_, _⟩⟩
    cases h_le with
    | inl hlt => exact False.elim (Peano.not_lt_of_lt hlt h)
    | inr heq =>
      rw [heq] at h
      exact False.elim (Peano.not_lt_self b h)
  · rcases h_gt_side with ⟨_, ⟨h', h_eq⟩⟩
    exact ⟨h', congrArg Prod.fst h_eq⟩

theorem peano_subtractWithRemainder_second_of_le {a b : Peano} (h : a ≤ b) :
    ∃ h2, (Peano.subtractWithRemainder a b).2 = some (Peano.subtract b.successor a h2) := by
  rcases Peano.subtractWithRemainder_correct a b with h_le_side | h_gt_side
  · rcases h_le_side with ⟨_, ⟨h2, h_eq⟩⟩
    exact ⟨h2, congrArg Prod.snd h_eq⟩
  · rcases h_gt_side with ⟨h_gt, ⟨_, _⟩⟩
    cases h with
    | inl hlt => exact False.elim (Peano.not_lt_of_lt hlt h_gt)
    | inr heq =>
      rw [heq] at h_gt
      exact False.elim (Peano.not_lt_self b h_gt)

theorem peano_subtractWithRemainder_second_of_gt {a b : Peano} (h : b < a) :
    (Peano.subtractWithRemainder a b).2 = none := by
  rcases Peano.subtractWithRemainder_correct a b with h_le_side | h_gt_side
  · rcases h_le_side with ⟨h_le, ⟨_, _⟩⟩
    cases h_le with
    | inl hlt => exact False.elim (Peano.not_lt_of_lt hlt h)
    | inr heq =>
      rw [heq] at h
      exact False.elim (Peano.not_lt_self b h)
  · rcases h_gt_side with ⟨_, ⟨_, h_eq⟩⟩
    exact congrArg Prod.snd h_eq

theorem subtractAlignedLists_borrow_true_of_lessThan {a b : Decimal} (h : a < b) :
    (subtractAlignedLists
      (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).1
      (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).2
      (Sequences.List.padAtStartToSameLength_sameLength a.val b.val zeroDigit)).2 = true :=
  subtractAlignedLists_borrow_true_of_toCardinalNaturalPeano_lt (toCardinalPeano_lt_of_lt h)

theorem padAtStartToSameLength_eq_of_equivalent {a b : Decimal} (h : a ≈ b) :
  (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).1 =
    (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).2 :=
  padAtStartToSameLength_eq_of_toCardinalNaturalPeano_eq (toCardinalPeano_eq_of_equivalent h)

theorem subtractAlignedLists_borrow_false_of_equivalent {a b : Decimal} (h : a ≈ b) :
    (subtractAlignedLists
      (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).1
      (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).2
      (Sequences.List.padAtStartToSameLength_sameLength a.val b.val zeroDigit)).2 = false :=
  subtractAlignedLists_borrow_false_of_toCardinalNaturalPeano_eq (toCardinalPeano_eq_of_equivalent h)

theorem subtractWithRemainder_first_toPeano (a b : Decimal) :
    toPeano (subtractWithRemainder a b).1 =
      (Peano.subtractWithRemainder a.toPeano b.toPeano).1 := by
  rcases trichotomy a b with hlt | heq | hgt
  · have h_peano := peano_subtractWithRemainder_first_of_le (Or.inl (toPeano_lt_of_lt hlt))
    have h_card : toCardinalPeano (subtractWithRemainder a b).1 = toCardinalPeano one := by
      unfold subtractWithRemainder toCardinalPeano one
      dsimp only
      simp [dif_pos (subtractAlignedLists_borrow_true_of_lessThan hlt)]
    have h_lhs : toPeano (subtractWithRemainder a b).1 = toPeano one := by
      unfold toPeano
      exact CardinalNatural.Peano.toOrdinal_congr h_card
        (toCardinalPeano_ne_zero (subtractWithRemainder a b).1) (toCardinalPeano_ne_zero one)
    rw [h_lhs, toPeano_one, h_peano]
  · let h_same := Sequences.List.padAtStartToSameLength_sameLength a.val b.val zeroDigit
    have h_borrow := subtractAlignedLists_borrow_false_of_equivalent heq
    cases h_align : subtractAlignedLists
        (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).fst
        (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).snd h_same with
    | mk digits borrow =>
      cases borrow with
      | true =>
          exact False.elim (by rw [h_align] at h_borrow; cases h_borrow)
      | false =>
        by_cases h_nzb : hasNonZero digits = true
        · exact False.elim (by
            have h_nz : HasNonZero digits := hasNonZero_of_hasNonZero_bool h_nzb
            have h_spec := subtractAlignedLists_specification h_same
            rw [h_align] at h_spec
            dsimp only at h_spec
            obtain ⟨_, h_val⟩ := h_spec
            simp at h_val
            have h_ap_eq_bp :
                toCardinalNaturalPeano (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).1
                  CardinalNatural.Peano.zero =
              toCardinalNaturalPeano (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).2
                  CardinalNatural.Peano.zero := by
              have h_card := toCardinalPeano_eq_of_equivalent heq
              simp only [toCardinalPeano] at h_card
              simpa [← toCardinalNaturalPeano_padAtStartToSameLength_first a.val b.val,
                ← toCardinalNaturalPeano_padAtStartToSameLength_second a.val b.val] using h_card
            have h_zero : toCardinalNaturalPeano digits CardinalNatural.Peano.zero = CardinalNatural.Peano.zero := by
              have h_sum :
                  toCardinalNaturalPeano digits CardinalNatural.Peano.zero +
                    toCardinalNaturalPeano (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).2
                      CardinalNatural.Peano.zero =
                  toCardinalNaturalPeano (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).1
                    CardinalNatural.Peano.zero := by
                exact h_val
              rw [h_ap_eq_bp] at h_sum
              let bp := toCardinalNaturalPeano (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).2
                  CardinalNatural.Peano.zero
              exact CardinalNatural.Peano.add_left_cancel bp _ CardinalNatural.Peano.zero
                (CardinalNatural.Peano.add_commutative _ _ ▸ h_sum)
            exact (toCardinalNaturalPeano_ne_zero_of_hasNonZero digits CardinalNatural.Peano.zero h_nz) h_zero)
        · have h_peano := peano_subtractWithRemainder_first_of_le (Or.inr (toPeano_eq_of_equivalent heq))
          have h_card : toCardinalPeano (subtractWithRemainder a b).1 = toCardinalPeano one := by
            unfold subtractWithRemainder toCardinalPeano one
            dsimp only
            let pair := Sequences.List.padAtStartToSameLength a.val b.val zeroDigit
            simp [h_align, h_nzb]
          have h_lhs : toPeano (subtractWithRemainder a b).1 = toPeano one := by
            unfold toPeano
            exact CardinalNatural.Peano.toOrdinal_congr h_card
              (toCardinalPeano_ne_zero (subtractWithRemainder a b).1) (toCardinalPeano_ne_zero one)
          rw [h_lhs, toPeano_one, h_peano]
  · rcases peano_subtractWithRemainder_first_of_lt (toPeano_lt_of_lt hgt) with ⟨h3, h_peano⟩
    rcases subtract_toPeano a b hgt with ⟨h2, h_sub⟩
    let h_same := Sequences.List.padAtStartToSameLength_sameLength a.val b.val zeroDigit
    have h_borrow := subtractAlignedLists_borrow_false_of_lessThan h_same
      (lessThanAlignedLists_padded_of_lt hgt)
    cases h_subtract : subtractAlignedLists
        (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).fst
        (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).snd h_same with
    | mk digits borrow =>
      cases borrow with
      | true =>
          rw [h_subtract] at h_borrow
          cases h_borrow
      | false =>
          have h_nzb : hasNonZero digits = true :=
            hasNonZero_bool_eq_true_of_hasNonZero
              (hasNonZero_of_subtractAlignedLists_borrow_false_of_lessThan h_same
                (lessThanAlignedLists_padded_of_lt hgt) h_subtract)
          have h_has : hasNonZero
              (subtractAlignedLists
                (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).fst
                (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).snd h_same).fst =
            true := by simpa [h_subtract] using h_nzb
          have h_card : toCardinalPeano (subtractWithRemainder a b).1 =
              toCardinalPeano (subtract a b hgt) := by
            unfold toCardinalPeano subtractWithRemainder subtract
            dsimp only
            let pair := Sequences.List.padAtStartToSameLength a.val b.val zeroDigit
            simp [h_subtract, h_nzb]
          have h_lhs : toPeano (subtractWithRemainder a b).1 = toPeano (subtract a b hgt) := by
            unfold toPeano
            exact CardinalNatural.Peano.toOrdinal_congr h_card
              (toCardinalPeano_ne_zero (subtractWithRemainder a b).1)
              (toCardinalPeano_ne_zero (subtract a b hgt))
          rw [h_lhs, h_sub, h_peano]

theorem peano_subtract_successor_eq_one (b : Peano) :
    ∃ h, Peano.subtract b.successor b h = Peano.one := by
  induction b with
  | one =>
    refine ⟨Peano.LessThan.base, ?_⟩
    rfl
  | successor b ih =>
    rcases ih with ⟨_, ih⟩
    refine ⟨Peano.LessThan.base, ?_⟩
    dsimp [Peano.subtract]
    exact ih

/-- Every Decimal is strictly less than its successor. -/
theorem x_lt_successor_x (x : Decimal) : x < x.successor := by
  apply lt_of_toCardinalPeano_lt
  rw [toCardinalPeano_successor]
  exact CardinalNatural.Peano.LessThan.base

theorem lt_successor_of_lt {a b : Decimal} (h : a < b) : a < successor b :=
  lt_trans h (x_lt_successor_x b)

theorem subtractWithRemainder_second_toPeano (a b : Decimal) :
    Option.map toPeano (subtractWithRemainder a b).2 =
      (Peano.subtractWithRemainder a.toPeano b.toPeano).2 := by
  rcases trichotomy a b with hlt | heq | hgt
  · rcases peano_subtractWithRemainder_second_of_le (Or.inl (toPeano_lt_of_lt hlt)) with ⟨h2, h_peano⟩
    rcases subtract_toPeano (successor b) a (lt_successor_of_lt hlt) with ⟨h3, h_sub⟩
    unfold subtractWithRemainder
    dsimp only
    simp [dif_pos (subtractAlignedLists_borrow_true_of_lessThan hlt), h_sub, successor_toPeano, h_peano]
  · rcases peano_subtractWithRemainder_second_of_le (Or.inr (toPeano_eq_of_equivalent heq)) with ⟨h2, h_peano⟩
    let h_same := Sequences.List.padAtStartToSameLength_sameLength a.val b.val zeroDigit
    have h_borrow := subtractAlignedLists_borrow_false_of_equivalent heq
    cases h_align : subtractAlignedLists
        (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).fst
        (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).snd h_same with
    | mk digits borrow =>
      cases borrow with
      | true =>
          exact False.elim (by rw [h_align] at h_borrow; cases h_borrow)
      | false =>
        by_cases h_nzb : hasNonZero digits = true
        · exact False.elim (by
            have h_nz : HasNonZero digits := hasNonZero_of_hasNonZero_bool h_nzb
            have h_spec := subtractAlignedLists_specification h_same
            rw [h_align] at h_spec
            dsimp only at h_spec
            obtain ⟨_, h_val⟩ := h_spec
            simp at h_val
            have h_ap_eq_bp :
                toCardinalNaturalPeano (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).1
                  CardinalNatural.Peano.zero =
              toCardinalNaturalPeano (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).2
                  CardinalNatural.Peano.zero := by
              have h_card := toCardinalPeano_eq_of_equivalent heq
              simp only [toCardinalPeano] at h_card
              simpa [← toCardinalNaturalPeano_padAtStartToSameLength_first a.val b.val,
                ← toCardinalNaturalPeano_padAtStartToSameLength_second a.val b.val] using h_card
            have h_zero : toCardinalNaturalPeano digits CardinalNatural.Peano.zero = CardinalNatural.Peano.zero := by
              have h_sum :
                  toCardinalNaturalPeano digits CardinalNatural.Peano.zero +
                    toCardinalNaturalPeano (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).2
                      CardinalNatural.Peano.zero =
                  toCardinalNaturalPeano (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).1
                    CardinalNatural.Peano.zero := by
                exact h_val
              rw [h_ap_eq_bp] at h_sum
              let bp := toCardinalNaturalPeano (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).2
                  CardinalNatural.Peano.zero
              exact CardinalNatural.Peano.add_left_cancel bp _ CardinalNatural.Peano.zero
                (CardinalNatural.Peano.add_commutative _ _ ▸ h_sum)
            exact (toCardinalNaturalPeano_ne_zero_of_hasNonZero digits CardinalNatural.Peano.zero h_nz) h_zero)
        · have h_snd :
              (Peano.subtractWithRemainder a.toPeano b.toPeano).2 = some Peano.one := by
            rcases peano_subtractWithRemainder_second_of_le (Or.inr (toPeano_eq_of_equivalent heq)) with
              ⟨h2, h_peano⟩
            rw [h_peano]
            obtain ⟨h3, h_sub_one⟩ := peano_subtract_successor_eq_one b.toPeano
            have ha_eq := toPeano_eq_of_equivalent heq
            have h_sub : Peano.subtract b.toPeano.successor a.toPeano h2 =
                Peano.subtract b.toPeano.successor b.toPeano h3 :=
              Peano.subtract_eq_of_eq h2 h3 rfl ha_eq
            rw [h_sub, h_sub_one]
          unfold subtractWithRemainder
          dsimp only
          simp [h_align, h_nzb, toPeano_one, h_snd]
  · have h_peano := peano_subtractWithRemainder_second_of_gt (toPeano_lt_of_lt hgt)
    let h_same := Sequences.List.padAtStartToSameLength_sameLength a.val b.val zeroDigit
    have h_borrow := subtractAlignedLists_borrow_false_of_lessThan h_same
      (lessThanAlignedLists_padded_of_lt hgt)
    cases h_subtract : subtractAlignedLists
        (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).fst
        (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).snd h_same with
    | mk digits borrow =>
      cases borrow with
      | true =>
          rw [h_subtract] at h_borrow
          cases h_borrow
      | false =>
          have h_nzb : hasNonZero digits = true :=
            hasNonZero_bool_eq_true_of_hasNonZero
              (hasNonZero_of_subtractAlignedLists_borrow_false_of_lessThan h_same
                (lessThanAlignedLists_padded_of_lt hgt) h_subtract)
          unfold subtractWithRemainder
          dsimp only
          simp [h_subtract, h_nzb, h_peano]

theorem subtractWithRemainder_second_eq_some (a b c : Decimal)
    (h : (subtractWithRemainder a b).2 = some c) :
    (Peano.subtractWithRemainder a.toPeano b.toPeano).2 = some c.toPeano := by
  have hmap := subtractWithRemainder_second_toPeano a b
  rw [h] at hmap
  simpa [Option.map_some] using hmap.symm

theorem exists_subtract_of_trySubtract {x y z : Decimal} (h : trySubtract x y = some z) :
    ∃ h', subtract x y h' = z := by
  unfold trySubtract at h
  cases h_swr : subtractWithRemainder x y with
  | mk diff rem =>
    cases rem with
    | some _ =>
      simp only [h_swr] at h
      cases h
    | none =>
      simp only [h_swr] at h
      injection h with hz
      subst hz
      rcases trichotomy x y with hlt | heq | hgt
      · have hsnd := subtractWithRemainder_second_toPeano x y
        rw [h_swr] at hsnd
        dsimp only at hsnd
        rcases peano_subtractWithRemainder_second_of_le (Or.inl (toPeano_lt_of_lt hlt)) with
          ⟨_, h_peano⟩
        rw [h_peano] at hsnd
        cases hsnd
      · have hsnd := subtractWithRemainder_second_toPeano x y
        rw [h_swr] at hsnd
        dsimp only at hsnd
        rcases peano_subtractWithRemainder_second_of_le (Or.inr (toPeano_eq_of_equivalent heq)) with
          ⟨_, h_peano⟩
        rw [h_peano] at hsnd
        cases hsnd
      · refine ⟨hgt, ?_⟩
        let h_same := Sequences.List.padAtStartToSameLength_sameLength x.val y.val zeroDigit
        have h_borrow := subtractAlignedLists_borrow_false_of_lessThan h_same
          (lessThanAlignedLists_padded_of_lt hgt)
        cases h_subtract : subtractAlignedLists
            (Sequences.List.padAtStartToSameLength x.val y.val zeroDigit).fst
            (Sequences.List.padAtStartToSameLength x.val y.val zeroDigit).snd h_same with
        | mk digits borrow =>
          cases borrow with
          | true =>
              rw [h_subtract] at h_borrow
              cases h_borrow
          | false =>
              have h_nzb : hasNonZero digits = true :=
                hasNonZero_bool_eq_true_of_hasNonZero
                  (hasNonZero_of_subtractAlignedLists_borrow_false_of_lessThan h_same
                    (lessThanAlignedLists_padded_of_lt hgt) h_subtract)
              have h_swr' : subtractWithRemainder x y =
                  ⟨⟨digits, hasNonZero_of_hasNonZero_bool h_nzb⟩, none⟩ := by
                unfold subtractWithRemainder
                dsimp only
                simp [h_subtract, h_nzb]
              rw [h_swr] at h_swr'
              injection h_swr' with h_diff _
              apply Eq.symm
              rw [h_diff]
              apply Subtype.ext
              unfold subtract
              dsimp only
              simp [h_subtract]

theorem trySubtract_of_subtract {x y z : Decimal} (h : ∃ h', subtract x y h' = z) :
    trySubtract x y = some z := by
  obtain ⟨hlt, heq⟩ := h
  unfold trySubtract
  let h_same := Sequences.List.padAtStartToSameLength_sameLength x.val y.val zeroDigit
  have h_borrow := subtractAlignedLists_borrow_false_of_lessThan h_same
    (lessThanAlignedLists_padded_of_lt hlt)
  cases h_subtract : subtractAlignedLists
      (Sequences.List.padAtStartToSameLength x.val y.val zeroDigit).fst
      (Sequences.List.padAtStartToSameLength x.val y.val zeroDigit).snd h_same with
  | mk digits borrow =>
    cases borrow with
    | true =>
        rw [h_subtract] at h_borrow
        cases h_borrow
    | false =>
        have h_nzb : hasNonZero digits = true :=
          hasNonZero_bool_eq_true_of_hasNonZero
            (hasNonZero_of_subtractAlignedLists_borrow_false_of_lessThan h_same
              (lessThanAlignedLists_padded_of_lt hlt) h_subtract)
        have h_swr : subtractWithRemainder x y =
            ⟨⟨digits, hasNonZero_of_hasNonZero_bool h_nzb⟩, none⟩ := by
          unfold subtractWithRemainder
          dsimp only
          simp [h_subtract, h_nzb]
        rw [h_swr]
        apply congrArg some
        rw [← heq]
        apply Subtype.ext
        unfold subtract
        dsimp only
        simp [h_subtract]

theorem fromPeano_toPeano (x : Decimal) : fromPeano (toPeano x) ≈ x := by
  apply equivalent_of_toPeano_eq
  exact toPeano_fromPeano (toPeano x)

theorem add_subtract_associative (a b c : Decimal) (h : c < b) :
    ∃ h2, subtract (a + b) c h2 ≈ a + subtract b c h := by
  have hc_lt_ab : c < a + b := by
    apply lt_of_toCardinalPeano_lt
    have hb_card : toCardinalPeano c < toCardinalPeano b := toCardinalPeano_lt_of_lt h
    have h_add_card : toCardinalPeano b < toCardinalPeano (a + b) := by
      rw [toCardinalPeano_add, CardinalNatural.Peano.add_commutative]
      apply CardinalNatural.Peano.lt_add_of_right_ne_zero
      apply toCardinalPeano_ne_zero
    exact CardinalNatural.Peano.lt_trans hb_card h_add_card
  let h2 : c < a + b := hc_lt_ab
  refine ⟨h2, ?_⟩
  apply equivalent_of_toCardinalPeano_eq
  apply CardinalNatural.Peano.add_cancel_right
    (toCardinalPeano (subtract (a + b) c h2))
    (toCardinalPeano (a + subtract b c h))
    (toCardinalPeano c)
  rw [toCardinalPeano_subtract]
  rw [toCardinalPeano_add]
  have h_add_sub : toCardinalPeano (a + subtract b c h) + toCardinalPeano c = toCardinalPeano a + toCardinalPeano b := by
    rw [toCardinalPeano_add]
    rw [CardinalNatural.Peano.add_associative]
    rw [toCardinalPeano_subtract]
  rw [h_add_sub]


theorem subtract_subtract_associative (a b c : Decimal) (h : b < a) (h2 : c < subtract a b h) :
    ∃ h3, subtract (subtract a b h) c h2 ≈ subtract a (b + c) h3 := by
  have hbc_lt_a : b + c < a := by
    apply lt_of_toCardinalPeano_lt
    have h_sub : toCardinalPeano c < toCardinalPeano (subtract a b h) :=
      toCardinalPeano_lt_of_lt h2
    have h_add : toCardinalPeano c + toCardinalPeano b < toCardinalPeano (subtract a b h) + toCardinalPeano b := by
      apply ZeroMath.Numbers.CardinalNatural.Peano.add_lt_add_right h_sub
    rw [toCardinalPeano_subtract a b h] at h_add
    rw [toCardinalPeano_add]
    rw [ZeroMath.Numbers.CardinalNatural.Peano.add_commutative (toCardinalPeano b) (toCardinalPeano c)]
    exact h_add
  let h3 : b + c < a := hbc_lt_a
  refine ⟨h3, ?_⟩
  apply equivalent_of_toCardinalPeano_eq
  apply ZeroMath.Numbers.CardinalNatural.Peano.add_cancel_right
    (toCardinalPeano (subtract (subtract a b h) c h2))
    (toCardinalPeano (subtract a (b + c) h3))
    (toCardinalPeano (b + c))
  rw [toCardinalPeano_subtract a (b + c) h3]
  rw [toCardinalPeano_add]
  rw [ZeroMath.Numbers.CardinalNatural.Peano.add_commutative (toCardinalPeano b) (toCardinalPeano c)]
  rw [← ZeroMath.Numbers.CardinalNatural.Peano.add_associative]
  rw [toCardinalPeano_subtract (subtract a b h) c h2]
  rw [toCardinalPeano_subtract a b h]

def multiply (a b : Decimal) : Decimal :=
  ⟨(multiplyList a.val b.val).1, hasNonZero_multiplyList a.val b.val a.property b.property⟩

instance : Mul Decimal := ⟨multiply⟩

theorem multiply_toCardinalPeano (a b : Decimal) :
    toCardinalPeano (a * b) = toCardinalPeano a * toCardinalPeano b := by
  unfold toCardinalPeano
  change toCardinalNaturalPeano (multiplyList a.val b.val).1 CardinalNatural.Peano.zero =
    toCardinalNaturalPeano a.val CardinalNatural.Peano.zero *
      toCardinalNaturalPeano b.val CardinalNatural.Peano.zero
  exact (multiplyList_specification a.val b.val).2

theorem multiply_toPeano (a b : Decimal) :
    toPeano (a * b) = a.toPeano * b.toPeano := by
  apply CardinalNatural.Peano.eq_of_fromOrdinal_eq
  unfold toPeano
  rw [CardinalNatural.Peano.fromOrdinal_toOrdinal]
  rw [CardinalNatural.Peano.fromOrdinal_multiply]
  rw [CardinalNatural.Peano.fromOrdinal_toOrdinal, CardinalNatural.Peano.fromOrdinal_toOrdinal]
  exact multiply_toCardinalPeano a b

theorem equivalent_multiply_commutative (a b : Decimal) : a * b ≈ b * a := by
  apply equivalent_of_toCardinalPeano_eq
  rw [multiply_toCardinalPeano, multiply_toCardinalPeano]
  apply CardinalNatural.Peano.multiply_commutative

theorem equivalent_multiply_associative (a b c : Decimal) : a * b * c ≈ a * (b * c) := by
  apply equivalent_of_toCardinalPeano_eq
  rw [multiply_toCardinalPeano, multiply_toCardinalPeano, multiply_toCardinalPeano, multiply_toCardinalPeano]
  apply CardinalNatural.Peano.multiply_associative


theorem equivalent_multiply_distributive_over_add_right (a b c : Decimal) : a * (b + c) ≈ a * b + a * c := by
  apply equivalent_of_toCardinalPeano_eq
  rw [multiply_toCardinalPeano, toCardinalPeano_add, toCardinalPeano_add, multiply_toCardinalPeano, multiply_toCardinalPeano]
  apply CardinalNatural.Peano.multiply_distributive_over_add_right


theorem equivalent_multiply_distributive_over_add_left (a b c : Decimal) : (a + b) * c ≈ a * c + b * c := by
  apply equivalent_of_toCardinalPeano_eq
  rw [multiply_toCardinalPeano, toCardinalPeano_add, toCardinalPeano_add, multiply_toCardinalPeano, multiply_toCardinalPeano]
  apply CardinalNatural.Peano.multiply_distributive_over_add_left


theorem multiply_subtract_distributive (a b c : Decimal) (h : c < b) :
  ∃ h2, a * subtract b c h ≈ subtract (a * b) (a * c) h2 := by
  have h_ac_lt_ab : a * c < a * b := by
    apply lt_of_toCardinalPeano_lt
    rw [multiply_toCardinalPeano, multiply_toCardinalPeano]
    exact CardinalNatural.Peano.multiply_lt_of_lt_left
      (toCardinalPeano a) (toCardinalPeano_ne_zero a) (toCardinalPeano_lt_of_lt h)
  refine ⟨h_ac_lt_ab, equivalent_of_toPeano_eq ?_⟩
  obtain ⟨_, heq⟩ :=
    Peano.multiply_subtract a.toPeano b.toPeano c.toPeano (toPeano_lt_of_lt h)
  obtain ⟨_, hsub_bc⟩ := subtract_toPeano b c h
  obtain ⟨_, hsub_ac⟩ := subtract_toPeano (a * b) (a * c) h_ac_lt_ab
  rw [multiply_toPeano, hsub_bc, hsub_ac, heq]
  exact Peano.subtract_eq_of_eq _ _ (by rw [multiply_toPeano]) (by rw [multiply_toPeano])

theorem subtract_multiply_distributive (a b c : Decimal) (h : b < a) :
  ∃ h2, subtract a b h * c ≈ subtract (a * c) (b * c) h2 := by
  have h_bc_lt_ac : b * c < a * c := by
    apply lt_of_toCardinalPeano_lt
    rw [multiply_toCardinalPeano, multiply_toCardinalPeano]
    rw [CardinalNatural.Peano.multiply_commutative (toCardinalPeano b) (toCardinalPeano c)]
    rw [CardinalNatural.Peano.multiply_commutative (toCardinalPeano a) (toCardinalPeano c)]
    exact CardinalNatural.Peano.multiply_lt_of_lt_left
      (toCardinalPeano c) (toCardinalPeano_ne_zero c) (toCardinalPeano_lt_of_lt h)
  refine ⟨h_bc_lt_ac, equivalent_of_toPeano_eq ?_⟩
  obtain ⟨h2p, heq⟩ :=
    Peano.multiply_subtract c.toPeano a.toPeano b.toPeano (toPeano_lt_of_lt h)
  obtain ⟨_, hsub_ab⟩ := subtract_toPeano a b h
  obtain ⟨hr, hsub_bc⟩ := subtract_toPeano (a * c) (b * c) h_bc_lt_ac
  rw [multiply_toPeano, hsub_ab, hsub_bc, Peano.multiply_commutative]
  refine Eq.trans heq ?_
  exact Peano.subtract_eq_of_eq h2p hr
    (by rw [Peano.multiply_commutative, multiply_toPeano])
    (by rw [Peano.multiply_commutative, multiply_toPeano])

def powerByDigit (x : Decimal) (d : Digit) : Decimal :=
  match d with
  | ⟨val, h⟩ =>
    match val, h with
    | .zero, _ => one
    | .successor v1, h =>
      match v1, h with
      | .zero, _ => x
      | .successor v2, h =>
        match v2, h with
        | .zero, _ => x * x
        | .successor v3, h =>
          match v3, h with
          | .zero, _ =>
            let x2 := x * x
            x2 * x
          | .successor v4, h =>
            match v4, h with
            | .zero, _ =>
              let x2 := x * x
              x2 * x2
            | .successor v5, h =>
              match v5, h with
              | .zero, _ =>
                let x2 := x * x
                let x4 := x2 * x2
                x4 * x
              | .successor v6, h =>
                match v6, h with
                | .zero, _ =>
                  let x2 := x * x
                  let x4 := x2 * x2
                  x4 * x2
                | .successor v7, h =>
                  match v7, h with
                  | .zero, _ =>
                    let x2 := x * x
                    let x4 := x2 * x2
                    let x6 := x4 * x2
                    x6 * x
                  | .successor v8, h =>
                    match v8, h with
                    | .zero, _ =>
                      let x2 := x * x
                      let x4 := x2 * x2
                      x4 * x4
                    | .successor v9, h =>
                      match v9, h with
                      | .zero, _ =>
                        let x2 := x * x
                        let x3 := x2 * x
                        let x6 := x3 * x3
                        x6 * x3
                      | .successor v10, h =>
                        have h1 := CardinalNatural.Peano.lt_of_successor_lt_successor h
                        have h2 := CardinalNatural.Peano.lt_of_successor_lt_successor h1
                        have h3 := CardinalNatural.Peano.lt_of_successor_lt_successor h2
                        have h4 := CardinalNatural.Peano.lt_of_successor_lt_successor h3
                        have h5 := CardinalNatural.Peano.lt_of_successor_lt_successor h4
                        have h6 := CardinalNatural.Peano.lt_of_successor_lt_successor h5
                        have h7 := CardinalNatural.Peano.lt_of_successor_lt_successor h6
                        have h8 := CardinalNatural.Peano.lt_of_successor_lt_successor h7
                        have h9 := CardinalNatural.Peano.lt_of_successor_lt_successor h8
                        have h10 := CardinalNatural.Peano.lt_of_successor_lt_successor h9
                        False.elim (CardinalNatural.Peano.not_lt_zero v10 h10)

def powerTen (x : Decimal) : Decimal :=
  let x5 := powerByDigit x fiveDigit
  x5 * x5

def powerContinue (x : Decimal) (acc : Decimal) : Sequences.List Digit → Decimal
  | .empty => acc
  | .firstElement d ds =>
      let raised := powerTen acc
      match d.val with
      | .zero => powerContinue x raised ds
      | .successor _ => powerContinue x (raised * powerByDigit x d) ds

def powerList (x : Decimal) : Sequences.List Digit → Decimal
  | .empty => one
  | .firstElement d ds => powerContinue x (powerByDigit x d) ds

def power (x e : Decimal) : Decimal :=
  powerList x e.val

instance : HPow Decimal Decimal Decimal where
  hPow := power

theorem toCardinalPeano_one : toCardinalPeano one = CardinalNatural.Peano.one := by
  unfold toCardinalPeano one
  change toCardinalNaturalPeano Sequences.List.empty
      (CardinalNatural.Peano.zero * CardinalNatural.Peano.ten + CardinalNatural.Peano.one) =
    CardinalNatural.Peano.one
  rw [CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.zero_add]
  rfl

theorem powerByDigit_toCardinalPeano (x : Decimal) (d : Digit) :
    toCardinalPeano (powerByDigit x d) =
      CardinalNatural.Peano.power (toCardinalPeano x) d.val
        (Or.inl (toCardinalPeano_ne_zero x)) := by
  let cx := toCardinalPeano x
  have hx : cx ≠ CardinalNatural.Peano.zero := toCardinalPeano_ne_zero x
  unfold powerByDigit
  match d with
  | ⟨val, h⟩ =>
    match val, h with
    | .zero, _ =>
      change toCardinalPeano one = CardinalNatural.Peano.power cx .zero (Or.inl hx)
      rw [toCardinalPeano_one, CardinalNatural.Peano.power_zero_eq_one]
    | .successor v1, h =>
      match v1, h with
      | .zero, _ =>
        change toCardinalPeano x = CardinalNatural.Peano.power cx .one (Or.inl hx)
        rw [CardinalNatural.Peano.power_one_eq_self]
      | .successor v2, h =>
        match v2, h with
        | .zero, _ =>
          change toCardinalPeano (x * x) = CardinalNatural.Peano.power cx .two (Or.inl hx)
          rw [multiply_toCardinalPeano, CardinalNatural.Peano.power_two_eq cx hx]
        | .successor v3, h =>
          match v3, h with
          | .zero, _ =>
            change toCardinalPeano (let x2 := x * x; x2 * x) =
              CardinalNatural.Peano.power cx .three (Or.inl hx)
            show toCardinalPeano ((x * x) * x) =
              CardinalNatural.Peano.power cx .three (Or.inl hx)
            rw [multiply_toCardinalPeano, multiply_toCardinalPeano,
              CardinalNatural.Peano.power_three_eq cx hx]
          | .successor v4, h =>
            match v4, h with
            | .zero, _ =>
              change toCardinalPeano (let x2 := x * x; x2 * x2) =
                CardinalNatural.Peano.power cx .four (Or.inl hx)
              show toCardinalPeano ((x * x) * (x * x)) =
                CardinalNatural.Peano.power cx .four (Or.inl hx)
              rw [multiply_toCardinalPeano, multiply_toCardinalPeano,
                CardinalNatural.Peano.power_four_eq cx hx]
            | .successor v5, h =>
              match v5, h with
              | .zero, _ =>
                change toCardinalPeano (let x2 := x * x; let x4 := x2 * x2; x4 * x) =
                  CardinalNatural.Peano.power cx .five (Or.inl hx)
                show toCardinalPeano (((x * x) * (x * x)) * x) =
                  CardinalNatural.Peano.power cx .five (Or.inl hx)
                rw [multiply_toCardinalPeano, multiply_toCardinalPeano,
                  multiply_toCardinalPeano, CardinalNatural.Peano.power_five_eq cx hx]
              | .successor v6, h =>
                match v6, h with
                | .zero, _ =>
                  change toCardinalPeano (let x2 := x * x; let x4 := x2 * x2; x4 * x2) =
                    CardinalNatural.Peano.power cx .six (Or.inl hx)
                  show toCardinalPeano (((x * x) * (x * x)) * (x * x)) =
                    CardinalNatural.Peano.power cx .six (Or.inl hx)
                  rw [multiply_toCardinalPeano, multiply_toCardinalPeano,
                    multiply_toCardinalPeano, CardinalNatural.Peano.power_six_eq cx hx]
                | .successor v7, h =>
                  match v7, h with
                  | .zero, _ =>
                    change toCardinalPeano
                        (let x2 := x * x; let x4 := x2 * x2; let x6 := x4 * x2; x6 * x) =
                      CardinalNatural.Peano.power cx .seven (Or.inl hx)
                    show toCardinalPeano ((((x * x) * (x * x)) * (x * x)) * x) =
                      CardinalNatural.Peano.power cx .seven (Or.inl hx)
                    rw [multiply_toCardinalPeano, multiply_toCardinalPeano,
                      multiply_toCardinalPeano, multiply_toCardinalPeano,
                      CardinalNatural.Peano.power_seven_eq cx hx]
                  | .successor v8, h =>
                    match v8, h with
                    | .zero, _ =>
                      change toCardinalPeano (let x2 := x * x; let x4 := x2 * x2; x4 * x4) =
                        CardinalNatural.Peano.power cx .eight (Or.inl hx)
                      show toCardinalPeano (((x * x) * (x * x)) * ((x * x) * (x * x))) =
                        CardinalNatural.Peano.power cx .eight (Or.inl hx)
                      rw [multiply_toCardinalPeano, multiply_toCardinalPeano,
                        multiply_toCardinalPeano, CardinalNatural.Peano.power_eight_eq cx hx]
                    | .successor v9, h =>
                      match v9, h with
                      | .zero, _ =>
                        change toCardinalPeano
                            (let x2 := x * x; let x3 := x2 * x; let x6 := x3 * x3; x6 * x3) =
                          CardinalNatural.Peano.power cx .nine (Or.inl hx)
                        show toCardinalPeano
                            ((((x * x) * x) * ((x * x) * x)) * ((x * x) * x)) =
                          CardinalNatural.Peano.power cx .nine (Or.inl hx)
                        rw [multiply_toCardinalPeano, multiply_toCardinalPeano,
                          multiply_toCardinalPeano, multiply_toCardinalPeano,
                          CardinalNatural.Peano.power_nine_eq cx hx]
                      | .successor v10, h =>
                        have h1 := CardinalNatural.Peano.lt_of_successor_lt_successor h
                        have h2 := CardinalNatural.Peano.lt_of_successor_lt_successor h1
                        have h3 := CardinalNatural.Peano.lt_of_successor_lt_successor h2
                        have h4 := CardinalNatural.Peano.lt_of_successor_lt_successor h3
                        have h5 := CardinalNatural.Peano.lt_of_successor_lt_successor h4
                        have h6 := CardinalNatural.Peano.lt_of_successor_lt_successor h5
                        have h7 := CardinalNatural.Peano.lt_of_successor_lt_successor h6
                        have h8 := CardinalNatural.Peano.lt_of_successor_lt_successor h7
                        have h9 := CardinalNatural.Peano.lt_of_successor_lt_successor h8
                        have h10 := CardinalNatural.Peano.lt_of_successor_lt_successor h9
                        exact False.elim (CardinalNatural.Peano.not_lt_zero v10 h10)

theorem powerTen_toCardinalPeano (x : Decimal) :
    toCardinalPeano (powerTen x) =
      CardinalNatural.Peano.power (toCardinalPeano x) CardinalNatural.Peano.ten
        (Or.inl (toCardinalPeano_ne_zero x)) := by
  unfold powerTen
  show toCardinalPeano (powerByDigit x fiveDigit * powerByDigit x fiveDigit) = _
  rw [multiply_toCardinalPeano]
  rw [powerByDigit_toCardinalPeano]
  have hf : fiveDigit.val = CardinalNatural.Peano.five := rfl
  rw [hf]
  have hx := toCardinalPeano_ne_zero x
  have hadd := CardinalNatural.Peano.power_add_eq (toCardinalPeano x)
    CardinalNatural.Peano.five CardinalNatural.Peano.five hx
  have hsum : CardinalNatural.Peano.five + CardinalNatural.Peano.five =
      CardinalNatural.Peano.ten := rfl
  rw [hsum] at hadd
  exact hadd.symm

theorem powerContinue_toCardinalPeano (x acc : Decimal) (ds : Sequences.List Digit)
    (e : CardinalNatural.Peano)
    (hacc : toCardinalPeano acc =
      CardinalNatural.Peano.power (toCardinalPeano x) e
        (Or.inl (toCardinalPeano_ne_zero x))) :
    toCardinalPeano (powerContinue x acc ds) =
      CardinalNatural.Peano.power (toCardinalPeano x)
        (e * CardinalNatural.Peano.tenPower ds.length +
          toCardinalNaturalPeano ds CardinalNatural.Peano.zero)
        (Or.inl (toCardinalPeano_ne_zero x)) := by
  induction ds generalizing acc e with
  | empty =>
      change toCardinalPeano acc =
        CardinalNatural.Peano.power (toCardinalPeano x)
          (e * CardinalNatural.Peano.tenPower CardinalNatural.Peano.zero +
            CardinalNatural.Peano.zero)
          (Or.inl (toCardinalPeano_ne_zero x))
      simp only [CardinalNatural.Peano.tenPower, CardinalNatural.Peano.multiply_one,
        CardinalNatural.Peano.add_zero]
      exact hacc
  | firstElement d rest ih =>
      have hx := toCardinalPeano_ne_zero x
      have hraised : toCardinalPeano (powerTen acc) =
          CardinalNatural.Peano.power (toCardinalPeano x)
            (e * CardinalNatural.Peano.ten) (Or.inl hx) := by
        rw [powerTen_toCardinalPeano]
        have hpow_acc :
            CardinalNatural.Peano.power (toCardinalPeano acc) CardinalNatural.Peano.ten
              (Or.inl (toCardinalPeano_ne_zero acc)) =
            CardinalNatural.Peano.power
              (CardinalNatural.Peano.power (toCardinalPeano x) e (Or.inl hx))
              CardinalNatural.Peano.ten
              (Or.inl (CardinalNatural.Peano.power_ne_zero_of_base_ne_zero
                (toCardinalPeano x) e (Or.inl hx) hx)) :=
          CardinalNatural.Peano.eq_rec_power _ _ _ hacc _ _
        rw [hpow_acc]
        exact (CardinalNatural.Peano.power_multiply_eq (toCardinalPeano x) e
          CardinalNatural.Peano.ten hx).symm
      have hlen : (Sequences.List.firstElement d rest).length =
          rest.length + CardinalNatural.Peano.one := rfl
      cases hd : d.val with
      | zero =>
          have ih' := ih (powerTen acc) (e * CardinalNatural.Peano.ten) hraised
          have hexp :
              (e * CardinalNatural.Peano.ten) * CardinalNatural.Peano.tenPower rest.length +
                toCardinalNaturalPeano rest CardinalNatural.Peano.zero =
              e * CardinalNatural.Peano.tenPower (rest.length + CardinalNatural.Peano.one) +
                toCardinalNaturalPeano (Sequences.List.firstElement d rest)
                  CardinalNatural.Peano.zero := by
            rw [toCardinalNaturalPeano_firstElement, hd, CardinalNatural.Peano.zero_multiply,
              CardinalNatural.Peano.zero_add, CardinalNatural.Peano.tenPower_add_one,
              CardinalNatural.Peano.multiply_associative]
          rw [hlen]
          simp only [powerContinue, hd]
          exact (CardinalNatural.Peano.eq_rec_power_exponent (toCardinalPeano x) _ _
            hexp.symm (Or.inl hx) (Or.inl hx)) ▸ ih'
      | successor v =>
          have hnew_acc : toCardinalPeano (powerTen acc * powerByDigit x d) =
              CardinalNatural.Peano.power (toCardinalPeano x)
                (e * CardinalNatural.Peano.ten + d.val) (Or.inl hx) := by
            rw [multiply_toCardinalPeano, powerByDigit_toCardinalPeano, hraised]
            exact (CardinalNatural.Peano.power_add_eq (toCardinalPeano x)
              (e * CardinalNatural.Peano.ten) d.val hx).symm
          have ih' := ih (powerTen acc * powerByDigit x d)
            (e * CardinalNatural.Peano.ten + d.val) hnew_acc
          have hexp :
              (e * CardinalNatural.Peano.ten + d.val) *
                  CardinalNatural.Peano.tenPower rest.length +
                toCardinalNaturalPeano rest CardinalNatural.Peano.zero =
              e * CardinalNatural.Peano.tenPower (rest.length + CardinalNatural.Peano.one) +
                toCardinalNaturalPeano (Sequences.List.firstElement d rest)
                  CardinalNatural.Peano.zero := by
            rw [toCardinalNaturalPeano_firstElement, CardinalNatural.Peano.tenPower_add_one,
              CardinalNatural.Peano.multiply_distributive_over_add_left,
              CardinalNatural.Peano.multiply_associative,
              CardinalNatural.Peano.add_associative]
          rw [hlen]
          simp only [powerContinue, hd]
          exact (CardinalNatural.Peano.eq_rec_power_exponent (toCardinalPeano x) _ _
            hexp.symm (Or.inl hx) (Or.inl hx)) ▸ ih'

theorem powerList_toCardinalPeano (x : Decimal) (digits : Sequences.List Digit) :
    toCardinalPeano (powerList x digits) =
      CardinalNatural.Peano.power (toCardinalPeano x)
        (toCardinalNaturalPeano digits CardinalNatural.Peano.zero)
        (Or.inl (toCardinalPeano_ne_zero x)) := by
  match digits with
  | .empty =>
      change toCardinalPeano one =
        CardinalNatural.Peano.power (toCardinalPeano x) CardinalNatural.Peano.zero
          (Or.inl (toCardinalPeano_ne_zero x))
      rw [toCardinalPeano_one, CardinalNatural.Peano.power_zero_eq_one]
  | .firstElement d ds =>
      change toCardinalPeano (powerContinue x (powerByDigit x d) ds) = _
      have hacc := powerByDigit_toCardinalPeano x d
      have h := powerContinue_toCardinalPeano x (powerByDigit x d) ds d.val hacc
      rw [toCardinalNaturalPeano_firstElement]
      exact h

theorem power_toCardinalPeano (x y : Decimal) :
    toCardinalPeano (power x y) =
      CardinalNatural.Peano.power (toCardinalPeano x) (toCardinalPeano y)
        (Or.inl (toCardinalPeano_ne_zero x)) := by
  unfold power
  exact powerList_toCardinalPeano x y.val

theorem power_toPeano (x y : Decimal) :
    (power x y).toPeano = x.toPeano ^ y.toPeano := by
  apply CardinalNatural.Peano.eq_of_fromOrdinal_eq
  have hx := toCardinalPeano_ne_zero x
  have hy := toCardinalPeano_ne_zero y
  have h1 : CardinalNatural.Peano.fromOrdinal ((power x y).toPeano) =
      CardinalNatural.Peano.power (toCardinalPeano x) (toCardinalPeano y)
        (Or.inl hx) := by
    unfold toPeano
    rw [CardinalNatural.Peano.fromOrdinal_toOrdinal]
    exact power_toCardinalPeano x y
  have h2 : CardinalNatural.Peano.fromOrdinal (x.toPeano ^ y.toPeano) =
      CardinalNatural.Peano.power (toCardinalPeano x) (toCardinalPeano y)
        (Or.inl hx) := by
    rw [CardinalNatural.Peano.fromOrdinal_power]
    unfold toPeano
    refine Eq.trans
      (CardinalNatural.Peano.eq_rec_power
        (CardinalNatural.Peano.fromOrdinal
          (CardinalNatural.Peano.toOrdinal (toCardinalPeano x) hx))
        (toCardinalPeano x)
        (CardinalNatural.Peano.fromOrdinal
          (CardinalNatural.Peano.toOrdinal (toCardinalPeano y) hy))
        (CardinalNatural.Peano.fromOrdinal_toOrdinal (toCardinalPeano x) hx)
        (Or.inl (CardinalNatural.Peano.fromOrdinal_ne_zero _))
        (Or.inl hx))
      (CardinalNatural.Peano.eq_rec_power_exponent
        (toCardinalPeano x)
        (CardinalNatural.Peano.fromOrdinal
          (CardinalNatural.Peano.toOrdinal (toCardinalPeano y) hy))
        (toCardinalPeano y)
        (CardinalNatural.Peano.fromOrdinal_toOrdinal (toCardinalPeano y) hy)
        (Or.inl hx)
        (Or.inl hx))
  exact h1.trans h2.symm

theorem power_add (x y z : Decimal) : x ^ (y + z) ≈ (x ^ y) * (x ^ z) := by
  apply equivalent_of_toCardinalPeano_eq
  simp only [HPow.hPow]
  rw [power_toCardinalPeano, toCardinalPeano_add, multiply_toCardinalPeano,
    power_toCardinalPeano, power_toCardinalPeano]
  exact CardinalNatural.Peano.power_add_eq (toCardinalPeano x) (toCardinalPeano y) (toCardinalPeano z)
    (toCardinalPeano_ne_zero x)

theorem power_multiply (x a b : Decimal) : x ^ (a * b) ≈ (x ^ a) ^ b := by
  apply equivalent_of_toCardinalPeano_eq
  simp only [HPow.hPow]
  have hx := toCardinalPeano_ne_zero x
  rw [power_toCardinalPeano, multiply_toCardinalPeano, power_toCardinalPeano]
  have hbase := power_toCardinalPeano x a
  have hrhs :
      CardinalNatural.Peano.power (toCardinalPeano (power x a)) (toCardinalPeano b)
        (Or.inl (toCardinalPeano_ne_zero (power x a))) =
      CardinalNatural.Peano.power
        (CardinalNatural.Peano.power (toCardinalPeano x) (toCardinalPeano a) (Or.inl hx))
        (toCardinalPeano b)
        (Or.inl (CardinalNatural.Peano.power_ne_zero_of_base_ne_zero
          (toCardinalPeano x) (toCardinalPeano a) (Or.inl hx) hx)) :=
    CardinalNatural.Peano.eq_rec_power _ _ _ hbase _ _
  rw [hrhs]
  exact CardinalNatural.Peano.power_multiply_eq (toCardinalPeano x) (toCardinalPeano a) (toCardinalPeano b) hx

theorem multiply_power (x y a : Decimal) : (x * y) ^ a ≈ (x ^ a) * (y ^ a) := by
  apply equivalent_of_toPeano_eq
  simp only [HPow.hPow]
  rw [power_toPeano, multiply_toPeano, multiply_toPeano, power_toPeano, power_toPeano]
  exact Peano.multiply_power x.toPeano y.toPeano a.toPeano

def Power (e a : Decimal) : Prop := ∃ b : Decimal, b ^ e ≈ a

theorem Power_toPeano (e a : Decimal) : Power e a ↔ Peano.Power e.toPeano a.toPeano := by
  apply Iff.intro
  · intro h
    unfold Power at h
    unfold Peano.Power
    obtain ⟨b, hb⟩ := h
    exists b.toPeano
    rw [← power_toPeano]
    exact toPeano_eq_of_equivalent hb
  · intro h
    unfold Power
    unfold Peano.Power at h
    obtain ⟨b_peano, hb⟩ := h
    let b := fromPeano b_peano
    exists b
    apply equivalent_of_toPeano_eq
    simp only [HPow.hPow]
    rw [power_toPeano]
    have h_b_toPeano : b.toPeano = b_peano := toPeano_fromPeano b_peano
    rw [h_b_toPeano]
    exact hb

/-- `base ^ e`, treating the empty / all-zero list as the cardinal zero. -/
def powerListOrZero (base : Sequences.List Digit) (e : Decimal) : Sequences.List Digit :=
  if h : hasNonZero base then
    (power ⟨base, hasNonZero_of_hasNonZero_bool h⟩ e).val
  else
    .empty

/--
Integer `e`-th root of `a` with remainder: `(b, none)` when `a ≈ b ^ e`, and
`(b, some r)` when `a ≈ b ^ e + r` with `a < (b.successor) ^ e`.
Computed by the schoolbook columnar algorithm (digits grouped from the right
in blocks of `e`).
-/
def rootWithRemainder (a e : Decimal) : Decimal × Option Decimal :=
  let groupSize := toCardinalPeano e
  let remaining := firstRootGroupSize a.val.length groupSize (toCardinalPeano_ne_zero e)
  let (rootDigits, remDigits) :=
    rootWithRemainderAuxiliary (powerListOrZero · e) a.val groupSize .empty .empty remaining
  let root : Decimal :=
    if h : hasNonZero rootDigits then
      ⟨rootDigits, hasNonZero_of_hasNonZero_bool h⟩
    else
      one
  let rem : Option Decimal :=
    if h : hasNonZero remDigits then
      some ⟨remDigits, hasNonZero_of_hasNonZero_bool h⟩
    else
      none
  (root, rem)

abbrev powerOfDecimal (base : CardinalNatural.Peano) (e : Decimal) : CardinalNatural.Peano :=
  CardinalNatural.Peano.power base (toCardinalPeano e)
    (Or.inr (toCardinalPeano_ne_zero e))

theorem powerOfDecimal_lt {a b : CardinalNatural.Peano} (e : Decimal) (h : a < b) :
    powerOfDecimal a e < powerOfDecimal b e :=
  CardinalNatural.Peano.lt_power (toCardinalPeano_ne_zero e) h
    (Or.inr (toCardinalPeano_ne_zero e)) (Or.inr (toCardinalPeano_ne_zero e))

theorem powerOfDecimal_le {a b : CardinalNatural.Peano} (e : Decimal) (h : a ≤ b) :
    powerOfDecimal a e ≤ powerOfDecimal b e :=
  CardinalNatural.Peano.power_le_of_le (toCardinalPeano_ne_zero e) h
    (Or.inr (toCardinalPeano_ne_zero e)) (Or.inr (toCardinalPeano_ne_zero e))

theorem powerOfDecimal_zero (e : Decimal) :
    powerOfDecimal CardinalNatural.Peano.zero e = CardinalNatural.Peano.zero :=
  CardinalNatural.Peano.zero_power_of_nonzero_exponent
    (toCardinalPeano e) (toCardinalPeano_ne_zero e) _

theorem powerOfDecimal_one (e : Decimal) :
    powerOfDecimal CardinalNatural.Peano.one e = CardinalNatural.Peano.one :=
  CardinalNatural.Peano.one_power (toCardinalPeano e)
    (Or.inr (toCardinalPeano_ne_zero e))

theorem powerOfDecimal_congr {a b : CardinalNatural.Peano} (e : Decimal) (h : a = b) :
    powerOfDecimal a e = powerOfDecimal b e := by
  cases h
  rfl

theorem powerOfDecimal_multiply (x y : CardinalNatural.Peano) (e : Decimal) :
    powerOfDecimal (x * y) e = powerOfDecimal x e * powerOfDecimal y e := by
  obtain ⟨h3, heq⟩ :=
    CardinalNatural.Peano.power_multiply_dist x y (toCardinalPeano e)
      (Or.inr (toCardinalPeano_ne_zero e))
      (Or.inr (toCardinalPeano_ne_zero e))
  exact (CardinalNatural.Peano.eq_rec_power (x * y) (x * y) (toCardinalPeano e)
    rfl h3 (Or.inr (toCardinalPeano_ne_zero e))).symm.trans heq

theorem powerOfDecimal_multiply_ten (Y : CardinalNatural.Peano) (e : Decimal) :
    powerOfDecimal (Y * CardinalNatural.Peano.ten) e =
      powerOfDecimal Y e * CardinalNatural.Peano.tenPower (toCardinalPeano e) := by
  rw [powerOfDecimal_multiply, CardinalNatural.Peano.tenPower_eq_power]

theorem powerListOrZero_toCardinal (base : Sequences.List Digit) (e : Decimal) :
    listVal (powerListOrZero base e) = powerOfDecimal (listVal base) e := by
  unfold powerListOrZero
  by_cases h : hasNonZero base = true
  · rw [dif_pos h]
    have hpow := power_toCardinalPeano ⟨base, hasNonZero_of_hasNonZero_bool h⟩ e
    exact hpow.trans
      (CardinalNatural.Peano.eq_rec_power
        (toCardinalPeano ⟨base, hasNonZero_of_hasNonZero_bool h⟩)
        (listVal base)
        (toCardinalPeano e) rfl
        (Or.inl (toCardinalPeano_ne_zero ⟨base, hasNonZero_of_hasNonZero_bool h⟩))
        (Or.inr (toCardinalPeano_ne_zero e)))
  · have hz : listVal base = CardinalNatural.Peano.zero :=
      toCardinalNaturalPeano_zero_of_allZero (allZero_of_not_hasNonZero_bool h)
    rw [dif_neg h, hz]
    exact (powerOfDecimal_zero e).symm

theorem powerOfDecimal_shifted_le_trial (currentRoot : Sequences.List Digit) (e : Decimal)
    (d : Digit) :
    powerOfDecimal (listVal (Sequences.List.append currentRoot zeroDigit)) e ≤
      powerOfDecimal (listVal (Sequences.List.append currentRoot d)) e := by
  apply powerOfDecimal_le
  rw [listVal_append_zeroDigit, listVal_append]
  exact CardinalNatural.Peano.le_add_self_left _ _

theorem increment_add_shifted (currentRoot : Sequences.List Digit) (e : Decimal)
    (d : Digit) :
    listVal (subtractLists (powerListOrZero (Sequences.List.append currentRoot d) e)
        (powerListOrZero (Sequences.List.append currentRoot zeroDigit) e)) +
      powerOfDecimal (listVal (Sequences.List.append currentRoot zeroDigit)) e =
    powerOfDecimal (listVal (Sequences.List.append currentRoot d)) e := by
  have hnlt :
      ¬ listVal (powerListOrZero (Sequences.List.append currentRoot d) e) <
        listVal (powerListOrZero (Sequences.List.append currentRoot zeroDigit) e) := by
    rw [powerListOrZero_toCardinal, powerListOrZero_toCardinal]
    exact CardinalNatural.Peano.cardinal_not_lt_of_le
      (powerOfDecimal_shifted_le_trial currentRoot e d)
  have hsub :=
    subtractLists_specification
      (powerListOrZero (Sequences.List.append currentRoot d) e)
      (powerListOrZero (Sequences.List.append currentRoot zeroDigit) e) hnlt
  rw [← powerListOrZero_toCardinal, ← powerListOrZero_toCardinal]
  exact hsub

theorem rootDigit_taken_specification (remainder currentRoot : Sequences.List Digit)
    (e : Decimal) (d : Digit)
    (hnlt : ¬ listVal remainder <
      listVal (subtractLists
        (powerListOrZero (Sequences.List.append currentRoot d) e)
        (powerListOrZero (Sequences.List.append currentRoot zeroDigit) e))) :
    let increment :=
      subtractLists (powerListOrZero (Sequences.List.append currentRoot d) e)
        (powerListOrZero (Sequences.List.append currentRoot zeroDigit) e)
    let nextRem := subtractLists remainder increment
    listVal remainder + powerOfDecimal (listVal currentRoot * CardinalNatural.Peano.ten) e =
      powerOfDecimal (listVal currentRoot * CardinalNatural.Peano.ten + d.val) e +
        listVal nextRem ∧
    powerOfDecimal (listVal currentRoot * CardinalNatural.Peano.ten + d.val) e ≤
      listVal remainder + powerOfDecimal (listVal currentRoot * CardinalNatural.Peano.ten) e := by
  have hsub := subtractLists_specification remainder
    (subtractLists (powerListOrZero (Sequences.List.append currentRoot d) e)
      (powerListOrZero (Sequences.List.append currentRoot zeroDigit) e)) hnlt
  have hadd := increment_add_shifted currentRoot e d
  have hshift := listVal_append_zeroDigit currentRoot
  have htrial := listVal_append currentRoot d
  constructor
  · calc listVal remainder + powerOfDecimal (listVal currentRoot * CardinalNatural.Peano.ten) e
        = (listVal (subtractLists remainder
              (subtractLists (powerListOrZero (Sequences.List.append currentRoot d) e)
                (powerListOrZero (Sequences.List.append currentRoot zeroDigit) e))) +
            listVal (subtractLists
              (powerListOrZero (Sequences.List.append currentRoot d) e)
              (powerListOrZero (Sequences.List.append currentRoot zeroDigit) e))) +
            powerOfDecimal (listVal currentRoot * CardinalNatural.Peano.ten) e := hsub.symm ▸ rfl
      _ = listVal (subtractLists remainder
              (subtractLists (powerListOrZero (Sequences.List.append currentRoot d) e)
                (powerListOrZero (Sequences.List.append currentRoot zeroDigit) e))) +
            (listVal (subtractLists
              (powerListOrZero (Sequences.List.append currentRoot d) e)
              (powerListOrZero (Sequences.List.append currentRoot zeroDigit) e)) +
            powerOfDecimal (listVal currentRoot * CardinalNatural.Peano.ten) e) := by
          rw [CardinalNatural.Peano.add_associative]
      _ = listVal (subtractLists remainder
              (subtractLists (powerListOrZero (Sequences.List.append currentRoot d) e)
                (powerListOrZero (Sequences.List.append currentRoot zeroDigit) e))) +
            powerOfDecimal (listVal currentRoot * CardinalNatural.Peano.ten + d.val) e := by
          have hadd' := hadd
          rw [hshift, htrial] at hadd'
          rw [hadd']
      _ = powerOfDecimal (listVal currentRoot * CardinalNatural.Peano.ten + d.val) e +
            listVal (subtractLists remainder
              (subtractLists (powerListOrZero (Sequences.List.append currentRoot d) e)
                (powerListOrZero (Sequences.List.append currentRoot zeroDigit) e))) :=
          CardinalNatural.Peano.add_commutative _ _
  · have hle_inc := CardinalNatural.Peano.not_lt_implies_le hnlt
    have hle_add := CardinalNatural.Peano.add_le_add_right hle_inc
      (powerOfDecimal (listVal currentRoot * CardinalNatural.Peano.ten) e)
    have hadd' := hadd
    rw [hshift, htrial] at hadd'
    rwa [hadd'] at hle_add

theorem remainder_lt_zero_increment_false (remainder currentRoot : Sequences.List Digit)
    (e : Decimal) (hc : CardinalNatural.Peano.zero < CardinalNatural.Peano.ten)
    (hlt : listVal remainder <
      listVal (subtractLists
        (powerListOrZero (Sequences.List.append currentRoot ⟨CardinalNatural.Peano.zero, hc⟩) e)
        (powerListOrZero (Sequences.List.append currentRoot zeroDigit) e))) :
    False := by
  have hadd := increment_add_shifted currentRoot e ⟨CardinalNatural.Peano.zero, hc⟩
  have hshift := listVal_append_zeroDigit currentRoot
  have htrial := listVal_append currentRoot ⟨CardinalNatural.Peano.zero, hc⟩
  rw [hshift, htrial, CardinalNatural.Peano.add_zero] at hadd
  have hlt_add := CardinalNatural.Peano.add_lt_add_right hlt
    (powerOfDecimal (listVal currentRoot * CardinalNatural.Peano.ten) e)
  rw [hadd] at hlt_add
  have hlt_rem : listVal remainder < CardinalNatural.Peano.zero :=
    CardinalNatural.Peano.add_lt_cancel_right (by
      rwa [CardinalNatural.Peano.zero_add])
  exact CardinalNatural.Peano.not_lt_zero _ hlt_rem

theorem findRootDigitAuxiliary_specification (remainder : Sequences.List Digit) (exponent : Decimal)
    (currentRoot : Sequences.List Digit)
    (candidate : CardinalNatural.Peano) (hc : candidate < CardinalNatural.Peano.ten) :
    let result := findRootDigitAuxiliary (powerListOrZero · exponent) remainder currentRoot candidate hc
    let d := result.1
    let nextRem := result.2
    listVal remainder +
        powerOfDecimal (listVal currentRoot * CardinalNatural.Peano.ten) exponent =
      powerOfDecimal (listVal currentRoot * CardinalNatural.Peano.ten + d.val) exponent +
        listVal nextRem ∧
    powerOfDecimal (listVal currentRoot * CardinalNatural.Peano.ten + d.val) exponent ≤
      listVal remainder +
        powerOfDecimal (listVal currentRoot * CardinalNatural.Peano.ten) exponent ∧
    (candidate = d.val ∨
      listVal remainder +
          powerOfDecimal (listVal currentRoot * CardinalNatural.Peano.ten) exponent <
        powerOfDecimal (listVal currentRoot * CardinalNatural.Peano.ten + d.val.successor)
          exponent) := by
  induction candidate with
  | zero =>
    unfold findRootDigitAuxiliary
    dsimp only
    by_cases hlt : isLessThanLists remainder
        (subtractLists
          (powerListOrZero (Sequences.List.append currentRoot ⟨CardinalNatural.Peano.zero, hc⟩)
            exponent)
          (powerListOrZero (Sequences.List.append currentRoot zeroDigit) exponent)) = true
    · exact False.elim (remainder_lt_zero_increment_false remainder currentRoot exponent hc
        ((isLessThanLists_iff_toCardinalNaturalPeano_lt _ _).mp hlt))
    · rw [if_neg hlt]
      have hnlt := (isLessThanLists_eq_false_iff_not_lt remainder _).mp
        (eq_false_of_ne_true hlt)
      obtain ⟨heq, hle⟩ := rootDigit_taken_specification remainder currentRoot exponent
        ⟨CardinalNatural.Peano.zero, hc⟩ hnlt
      exact ⟨heq, hle, Or.inl rfl⟩
  | successor c ih =>
    unfold findRootDigitAuxiliary
    dsimp only
    by_cases hlt : isLessThanLists remainder
        (subtractLists
          (powerListOrZero (Sequences.List.append currentRoot ⟨c.successor, hc⟩) exponent)
          (powerListOrZero (Sequences.List.append currentRoot zeroDigit) exponent)) = true
    · rw [if_pos hlt]
      obtain ⟨heq, hle, hmax⟩ := ih (CardinalNatural.Peano.lt_of_successor_lt hc)
      refine ⟨heq, hle, ?_⟩
      cases hmax with
      | inl heq_d =>
        have hlt_val := (isLessThanLists_iff_toCardinalNaturalPeano_lt remainder _).mp hlt
        have hadd := increment_add_shifted currentRoot exponent ⟨c.successor, hc⟩
        have hshift := listVal_append_zeroDigit currentRoot
        have htrial := listVal_append currentRoot ⟨c.successor, hc⟩
        rw [hshift, htrial] at hadd
        have hlt_full := CardinalNatural.Peano.add_lt_add_right hlt_val
          (powerOfDecimal (listVal currentRoot * CardinalNatural.Peano.ten) exponent)
        rw [hadd] at hlt_full
        rw [← heq_d]
        exact Or.inr hlt_full
      | inr hlt' => exact Or.inr hlt'
    · rw [if_neg hlt]
      have hnlt := (isLessThanLists_eq_false_iff_not_lt remainder _).mp
        (eq_false_of_ne_true hlt)
      obtain ⟨heq, hle⟩ := rootDigit_taken_specification remainder currentRoot exponent
        ⟨c.successor, hc⟩ hnlt
      exact ⟨heq, hle, Or.inl rfl⟩

theorem findRootDigit_specification (remainder : Sequences.List Digit) (exponent : Decimal)
    (currentRoot : Sequences.List Digit) :
    let result := findRootDigit (powerListOrZero · exponent) remainder currentRoot
    let d := result.1
    let nextRem := result.2
    listVal remainder +
        powerOfDecimal (listVal currentRoot * CardinalNatural.Peano.ten) exponent =
      powerOfDecimal (listVal currentRoot * CardinalNatural.Peano.ten + d.val) exponent +
        listVal nextRem ∧
    powerOfDecimal (listVal currentRoot * CardinalNatural.Peano.ten + d.val) exponent ≤
      listVal remainder +
        powerOfDecimal (listVal currentRoot * CardinalNatural.Peano.ten) exponent ∧
    (d.val = CardinalNatural.Peano.nine ∨
      listVal remainder +
          powerOfDecimal (listVal currentRoot * CardinalNatural.Peano.ten) exponent <
        powerOfDecimal (listVal currentRoot * CardinalNatural.Peano.ten + d.val.successor)
          exponent) := by
  unfold findRootDigit
  obtain ⟨heq, hle, hmax⟩ :=
    findRootDigitAuxiliary_specification remainder exponent currentRoot
      CardinalNatural.Peano.nine CardinalNatural.Peano.nine_lt_ten
  refine ⟨heq, hle, ?_⟩
  cases hmax with
  | inl h_candidate => exact Or.inl h_candidate.symm
  | inr hbound => exact Or.inr hbound

def rootWindow (currentRoot remainder digits : Sequences.List Digit)
    (exponent : Decimal) (groupSize remainingInGroup : CardinalNatural.Peano)
    (hle : remainingInGroup ≤ groupSize) : CardinalNatural.Peano :=
  powerOfDecimal (listVal currentRoot) exponent *
      CardinalNatural.Peano.tenPower
        (digits.length + rootPad groupSize remainingInGroup hle) +
    listVal remainder * CardinalNatural.Peano.tenPower digits.length +
    listVal digits

theorem powerOfDecimal_successor_multiply_ten (Y : CardinalNatural.Peano) (e : Decimal) :
    powerOfDecimal (Y.successor * CardinalNatural.Peano.ten) e =
      powerOfDecimal Y.successor e * CardinalNatural.Peano.tenPower (toCardinalPeano e) :=
  powerOfDecimal_multiply_ten Y.successor e

theorem rootWindow_bring_down (currentRoot remainder : Sequences.List Digit)
    (d : Digit) (ds : Sequences.List Digit) (exponent : Decimal)
    (groupSize n : CardinalNatural.Peano)
    (hle : n.successor.successor ≤ groupSize) :
    rootWindow currentRoot remainder (Sequences.List.firstElement d ds)
      exponent groupSize n.successor.successor hle =
    rootWindow currentRoot (Sequences.List.append remainder d) ds
      exponent groupSize n.successor (CardinalNatural.Peano.le_of_successor_le hle) := by
  unfold rootWindow rootPad
  have hpad := CardinalNatural.Peano.subtract_successor_eq_predecessor_subtract groupSize n.successor hle
  have hlen : (Sequences.List.firstElement d ds).length =
      ds.length.successor := Sequences.List.length_firstElement d ds
  have hshift :
      (Sequences.List.firstElement d ds).length +
        CardinalNatural.Peano.subtract groupSize n.successor.successor hle =
      ds.length + CardinalNatural.Peano.subtract groupSize n.successor
        (CardinalNatural.Peano.le_of_successor_le hle) := by
    rw [hlen, hpad, CardinalNatural.Peano.successor_add,
      CardinalNatural.Peano.add_successor]
  have hrem : listVal (Sequences.List.append remainder d) =
      listVal remainder * CardinalNatural.Peano.ten + d.val :=
    toCardinalNaturalPeano_append remainder d
  have hdigits : listVal (Sequences.List.firstElement d ds) =
      d.val * CardinalNatural.Peano.tenPower ds.length + listVal ds :=
    toCardinalNaturalPeano_firstElement d ds
  have hten' : CardinalNatural.Peano.tenPower ds.length.successor =
      CardinalNatural.Peano.ten * CardinalNatural.Peano.tenPower ds.length := by
    rw [show ds.length.successor = ds.length + CardinalNatural.Peano.one from
      (CardinalNatural.Peano.add_one ds.length).symm,
      CardinalNatural.Peano.tenPower_add_one]
  rw [hshift, hrem, hdigits, hlen, hten']
  rw [← CardinalNatural.Peano.multiply_associative (listVal remainder)
    CardinalNatural.Peano.ten (CardinalNatural.Peano.tenPower ds.length)]
  rw [CardinalNatural.Peano.multiply_distributive_over_add_left]
  let A := powerOfDecimal (listVal currentRoot) exponent *
    CardinalNatural.Peano.tenPower (ds.length +
      CardinalNatural.Peano.subtract groupSize n.successor
        (CardinalNatural.Peano.le_of_successor_le hle))
  let B := listVal remainder * CardinalNatural.Peano.ten *
    CardinalNatural.Peano.tenPower ds.length
  let C := d.val * CardinalNatural.Peano.tenPower ds.length
  let D := listVal ds
  exact calc (A + B) + (C + D)
      = ((A + B) + C) + D :=
        (CardinalNatural.Peano.add_associative (A + B) C D).symm
    _ = (A + (B + C)) + D := by rw [CardinalNatural.Peano.add_associative A B C]

theorem powerOfDecimal_eq_toCardinal_power (b e : Decimal) :
    powerOfDecimal (toCardinalPeano b) e = toCardinalPeano (power b e) :=
  (CardinalNatural.Peano.eq_rec_power
      (toCardinalPeano b) (toCardinalPeano b) (toCardinalPeano e) rfl
      (Or.inr (toCardinalPeano_ne_zero e))
      (Or.inl (toCardinalPeano_ne_zero b))).trans
    (power_toCardinalPeano b e).symm

theorem rootWindow_at_choose (currentRoot remainder : Sequences.List Digit)
    (d : Digit) (ds : Sequences.List Digit) (exponent : Decimal)
    (groupSize : CardinalNatural.Peano)
    (hgs : groupSize = toCardinalPeano exponent)
    (hle : CardinalNatural.Peano.one ≤ groupSize) :
    rootWindow currentRoot remainder (Sequences.List.firstElement d ds)
      exponent groupSize CardinalNatural.Peano.one hle =
      (listVal (Sequences.List.append remainder d) +
        powerOfDecimal (listVal currentRoot * CardinalNatural.Peano.ten) exponent) *
        CardinalNatural.Peano.tenPower ds.length + listVal ds := by
  have hlen : (Sequences.List.firstElement d ds).length = ds.length.successor :=
    Sequences.List.length_firstElement d ds
  have hshift :
      (Sequences.List.firstElement d ds).length +
        rootPad groupSize CardinalNatural.Peano.one hle =
      ds.length + groupSize := by
    rw [hlen]
    unfold rootPad
    rw [CardinalNatural.Peano.successor_add_subtract_one_of_le]
  have hten : CardinalNatural.Peano.tenPower ds.length.successor =
      CardinalNatural.Peano.ten * CardinalNatural.Peano.tenPower ds.length := by
    rw [show ds.length.successor = ds.length + CardinalNatural.Peano.one from
      (CardinalNatural.Peano.add_one ds.length).symm,
      CardinalNatural.Peano.tenPower_add_one]
  have hnewR : listVal (Sequences.List.append remainder d) =
      listVal remainder * CardinalNatural.Peano.ten + d.val :=
    toCardinalNaturalPeano_append remainder d
  have hdigits : listVal (Sequences.List.firstElement d ds) =
      d.val * CardinalNatural.Peano.tenPower ds.length + listVal ds :=
    toCardinalNaturalPeano_firstElement d ds
  have hA :
      powerOfDecimal (listVal currentRoot) exponent *
        CardinalNatural.Peano.tenPower groupSize =
      powerOfDecimal (listVal currentRoot * CardinalNatural.Peano.ten) exponent := by
    rw [hgs, powerOfDecimal_multiply_ten]
  have hB :
      listVal remainder *
          (CardinalNatural.Peano.ten * CardinalNatural.Peano.tenPower ds.length) =
        (listVal remainder * CardinalNatural.Peano.ten) *
          CardinalNatural.Peano.tenPower ds.length :=
    (CardinalNatural.Peano.multiply_associative
      (listVal remainder) CardinalNatural.Peano.ten
      (CardinalNatural.Peano.tenPower ds.length)).symm
  unfold rootWindow
  rw [hshift, hdigits, hlen, hten, hnewR]
  rw [CardinalNatural.Peano.tenPower_add,
    CardinalNatural.Peano.multiply_commutative (CardinalNatural.Peano.tenPower ds.length),
    ← CardinalNatural.Peano.multiply_associative
      (powerOfDecimal (listVal currentRoot) exponent)
      (CardinalNatural.Peano.tenPower groupSize)]
  rw [hA, hB]
  let A := powerOfDecimal (listVal currentRoot * CardinalNatural.Peano.ten) exponent
  let B := listVal remainder * CardinalNatural.Peano.ten
  let C := d.val
  let N := CardinalNatural.Peano.tenPower ds.length
  let T := listVal ds
  exact calc A * N + B * N + (C * N + T)
      = A * N + (B * N + (C * N + T)) :=
        CardinalNatural.Peano.add_associative (A * N) (B * N) (C * N + T)
    _ = A * N + ((B * N + C * N) + T) := by
        rw [← CardinalNatural.Peano.add_associative (B * N) (C * N) T]
    _ = A * N + ((B + C) * N + T) := by
        rw [← CardinalNatural.Peano.multiply_distributive_over_add_left B C N]
    _ = (A * N + (B + C) * N) + T :=
        (CardinalNatural.Peano.add_associative (A * N) ((B + C) * N) T).symm
    _ = (A + (B + C)) * N + T := by
        rw [← CardinalNatural.Peano.multiply_distributive_over_add_left A (B + C) N]
    _ = ((B + C) + A) * N + T := by
        rw [CardinalNatural.Peano.add_commutative A (B + C)]

theorem rootWindow_after_choose (currentRoot remainder : Sequences.List Digit)
    (d : Digit) (ds : Sequences.List Digit) (exponent : Decimal)
    (groupSize : CardinalNatural.Peano) (q : Digit) (nextRem : Sequences.List Digit)
    (hgs : groupSize = toCardinalPeano exponent)
    (hle : CardinalNatural.Peano.one ≤ groupSize)
    (heq : listVal (Sequences.List.append remainder d) +
        powerOfDecimal (listVal currentRoot * CardinalNatural.Peano.ten) exponent =
      powerOfDecimal (listVal currentRoot * CardinalNatural.Peano.ten + q.val) exponent +
        listVal nextRem) :
    rootWindow currentRoot remainder (Sequences.List.firstElement d ds)
      exponent groupSize CardinalNatural.Peano.one hle =
    rootWindow (appendRootDigit currentRoot q) nextRem ds exponent
      groupSize groupSize (Or.inr rfl) := by
  have hpad0 : rootPad groupSize groupSize (Or.inr rfl) = CardinalNatural.Peano.zero :=
    CardinalNatural.Peano.subtract_eq_zero_of_eq (Or.inr rfl) rfl
  have hY : listVal (appendRootDigit currentRoot q) =
      listVal currentRoot * CardinalNatural.Peano.ten + q.val :=
    listVal_appendRootDigit currentRoot q
  rw [rootWindow_at_choose currentRoot remainder d ds exponent groupSize hgs hle, heq]
  unfold rootWindow
  rw [hY, hpad0, CardinalNatural.Peano.add_zero]
  rw [CardinalNatural.Peano.multiply_distributive_over_add_left]

theorem rootWindow_initial (a e : Decimal)
    (remaining : CardinalNatural.Peano)
    (hle : remaining ≤ toCardinalPeano e) :
    rootWindow Sequences.List.empty Sequences.List.empty a.val e
      (toCardinalPeano e) remaining hle = toCardinalPeano a := by
  unfold rootWindow toCardinalPeano
  rw [listVal_empty, powerOfDecimal_zero, CardinalNatural.Peano.zero_multiply,
    CardinalNatural.Peano.zero_add, CardinalNatural.Peano.zero_multiply,
    CardinalNatural.Peano.zero_add]

theorem rootWithRemainderAuxiliary_specification
    (digits : Sequences.List Digit) (exponent : Decimal)
    (groupSize : CardinalNatural.Peano)
    (hgs : groupSize = toCardinalPeano exponent) :
    ∀ (currentRoot remainder : Sequences.List Digit)
      (remainingInGroup : CardinalNatural.Peano),
      remainingInGroup ≠ CardinalNatural.Peano.zero →
      ∀ (hle : remainingInGroup ≤ groupSize),
        (digits.length = CardinalNatural.Peano.zero ∨
          ∃ q, digits.length = groupSize * q + remainingInGroup) →
        (digits.length = CardinalNatural.Peano.zero →
          remainingInGroup = groupSize) →
        rootWindow currentRoot remainder digits exponent
            groupSize remainingInGroup hle <
          powerOfDecimal (listVal currentRoot).successor exponent *
            CardinalNatural.Peano.tenPower
              (digits.length + rootPad groupSize remainingInGroup hle) →
      let result :=
        rootWithRemainderAuxiliary (powerListOrZero · exponent) digits groupSize currentRoot remainder
          remainingInGroup
      rootWindow currentRoot remainder digits exponent
          groupSize remainingInGroup hle =
        powerOfDecimal (listVal result.1) exponent + listVal result.2 ∧
      powerOfDecimal (listVal result.1) exponent + listVal result.2 <
        powerOfDecimal (listVal result.1).successor exponent := by
  induction digits with
  | empty =>
    intro currentRoot remainder remainingInGroup hk hle hmod hempty hbound
    have hrem_eq : remainingInGroup = groupSize := hempty rfl
    have hpad : rootPad groupSize remainingInGroup hle =
        CardinalNatural.Peano.zero :=
      CardinalNatural.Peano.subtract_eq_zero_of_eq hle hrem_eq.symm
    have hwin :
        rootWindow currentRoot remainder Sequences.List.empty exponent
          groupSize remainingInGroup hle =
          powerOfDecimal (listVal currentRoot) exponent + listVal remainder := by
      unfold rootWindow
      rw [hpad, listVal_empty]
      change
        powerOfDecimal (listVal currentRoot) exponent *
            CardinalNatural.Peano.tenPower
              (CardinalNatural.Peano.zero + CardinalNatural.Peano.zero) +
          listVal remainder *
            CardinalNatural.Peano.tenPower CardinalNatural.Peano.zero +
          CardinalNatural.Peano.zero =
        powerOfDecimal (listVal currentRoot) exponent + listVal remainder
      rw [CardinalNatural.Peano.add_zero]
      change
        powerOfDecimal (listVal currentRoot) exponent *
            CardinalNatural.Peano.tenPower CardinalNatural.Peano.zero +
          listVal remainder *
            CardinalNatural.Peano.tenPower CardinalNatural.Peano.zero +
          CardinalNatural.Peano.zero =
        powerOfDecimal (listVal currentRoot) exponent + listVal remainder
      rw [CardinalNatural.Peano.tenPower, CardinalNatural.Peano.multiply_one,
        CardinalNatural.Peano.multiply_one, CardinalNatural.Peano.add_zero]
    unfold rootWithRemainderAuxiliary
    constructor
    · exact hwin
    · have hlen0 :
          (Sequences.List.empty : Sequences.List Digit).length =
            CardinalNatural.Peano.zero := rfl
      rw [hwin] at hbound
      have hexp0 :
          (Sequences.List.empty : Sequences.List Digit).length +
            rootPad groupSize remainingInGroup hle =
            CardinalNatural.Peano.zero := by
        rw [hlen0, hpad, CardinalNatural.Peano.add_zero]
      rw [hexp0, CardinalNatural.Peano.tenPower, CardinalNatural.Peano.multiply_one] at hbound
      exact hbound
  | firstElement d ds ih =>
    intro currentRoot remainder remainingInGroup hk hle hmod hempty hbound
    unfold rootWithRemainderAuxiliary
    cases remainingInGroup with
    | zero => exact False.elim (hk rfl)
    | successor remaining' =>
      cases remaining' with
      | zero =>
        obtain ⟨heq, _, hmax⟩ :=
          findRootDigit_specification (Sequences.List.append remainder d) exponent currentRoot
        let qDigit :=
          (findRootDigit (powerListOrZero · exponent) (Sequences.List.append remainder d) currentRoot).1
        let nextRem :=
          (findRootDigit (powerListOrZero · exponent) (Sequences.List.append remainder d) currentRoot).2
        have hlen_ne :
            (Sequences.List.firstElement d ds).length ≠
              CardinalNatural.Peano.zero := by
          rw [Sequences.List.length_firstElement]
          exact CardinalNatural.Peano.successor_ne_zero _
        have hmod_ds :
            ds.length = CardinalNatural.Peano.zero ∨
              ∃ q, ds.length = groupSize * q + groupSize := by
          cases hmod with
          | inl h0 => exact False.elim (hlen_ne h0)
          | inr hex =>
            obtain ⟨q0, hq0⟩ := hex
            rw [Sequences.List.length_firstElement] at hq0
            exact CardinalNatural.Peano.eq_zero_or_multiply_add_self_of_successor_eq_multiply_add_one
              ds.length groupSize q0 hq0
        have hk_new : groupSize ≠ CardinalNatural.Peano.zero := by
          rw [hgs]
          exact toCardinalPeano_ne_zero exponent
        have hle_new : groupSize ≤ groupSize := Or.inr rfl
        have hempty_new :
            ds.length = CardinalNatural.Peano.zero → groupSize = groupSize :=
          fun _ => rfl
        have hwin :=
          rootWindow_after_choose currentRoot remainder d ds exponent
            groupSize qDigit nextRem hgs hle heq
        have hY :
            listVal (appendRootDigit currentRoot qDigit) =
              listVal currentRoot * CardinalNatural.Peano.ten + qDigit.val :=
          listVal_appendRootDigit currentRoot qDigit
        have hexp :
            (Sequences.List.firstElement d ds).length +
              rootPad groupSize CardinalNatural.Peano.zero.successor hle =
            ds.length + groupSize := by
          rw [Sequences.List.length_firstElement]
          unfold rootPad
          exact CardinalNatural.Peano.successor_add_subtract_one_of_le ds.length groupSize hle
        have hbound_new :
            rootWindow (appendRootDigit currentRoot qDigit) nextRem ds exponent
              groupSize groupSize hle_new <
            powerOfDecimal (listVal (appendRootDigit currentRoot qDigit)).successor exponent *
              CardinalNatural.Peano.tenPower
                (ds.length + rootPad groupSize groupSize hle_new) := by
          have hpad0 :
              rootPad groupSize groupSize hle_new = CardinalNatural.Peano.zero :=
            CardinalNatural.Peano.subtract_eq_zero_of_eq hle_new rfl
          rw [hpad0, CardinalNatural.Peano.add_zero]
          rw [← hwin]
          cases hmax with
          | inl hq9 =>
            have hsucc :
                (listVal (appendRootDigit currentRoot qDigit)).successor =
                  (listVal currentRoot).successor * CardinalNatural.Peano.ten := by
              rw [hY, hq9]
              exact CardinalNatural.Peano.successor_nine_multiply_ten (listVal currentRoot)
            have hbound' := hbound
            rw [hexp, CardinalNatural.Peano.tenPower_add] at hbound'
            have htenE :
                CardinalNatural.Peano.tenPower groupSize =
                  CardinalNatural.Peano.tenPower (toCardinalPeano exponent) := by
              rw [hgs]
            rw [htenE] at hbound'
            rw [CardinalNatural.Peano.multiply_commutative
              (CardinalNatural.Peano.tenPower ds.length)
              (CardinalNatural.Peano.tenPower (toCardinalPeano exponent))] at hbound'
            rw [← CardinalNatural.Peano.multiply_associative] at hbound'
            rw [← powerOfDecimal_multiply_ten (listVal currentRoot).successor exponent] at hbound'
            rwa [← hsucc] at hbound'
          | inr hpre =>
            have hexpand :=
              rootWindow_at_choose currentRoot remainder d ds exponent
                groupSize hgs hle
            have hsucc :
                (listVal (appendRootDigit currentRoot qDigit)).successor =
                  listVal currentRoot * CardinalNatural.Peano.ten +
                    qDigit.val.successor := by
              rw [hY, CardinalNatural.Peano.add_successor]
            rw [hexpand]
            rw [hsucc]
            exact CardinalNatural.Peano.multiply_tenPower_add_lt_of_lt
              hpre (toCardinalNaturalPeano_lt_tenPower ds)
        obtain ⟨ih_eq, ih_lt⟩ :=
          ih (appendRootDigit currentRoot qDigit) nextRem groupSize
            hk_new hle_new hmod_ds hempty_new hbound_new
        constructor
        · exact hwin.trans ih_eq
        · exact ih_lt
      | successor n =>
        have hle_new :
            n.successor ≤ groupSize := CardinalNatural.Peano.le_of_successor_le hle
        have hk_new : n.successor ≠ CardinalNatural.Peano.zero :=
          CardinalNatural.Peano.successor_ne_zero n
        have hlen_ne :
            (Sequences.List.firstElement d ds).length ≠
              CardinalNatural.Peano.zero := by
          rw [Sequences.List.length_firstElement]
          exact CardinalNatural.Peano.successor_ne_zero _
        have hds_ne : ds.length ≠ CardinalNatural.Peano.zero := by
          intro hz
          cases hmod with
          | inl h0 => exact hlen_ne h0
          | inr hex =>
            obtain ⟨q, hq⟩ := hex
            have hlen1 :
                (Sequences.List.firstElement d ds).length =
                  CardinalNatural.Peano.one := by
              rw [Sequences.List.length_firstElement, hz]
              rfl
            rw [hlen1] at hq
            exact CardinalNatural.Peano.one_ne_multiply_add_of_two_le
              groupSize n.successor.successor q
              (CardinalNatural.Peano.two_le_successor_successor n) hle hq
        have hmod_ds :
            ds.length = CardinalNatural.Peano.zero ∨
              ∃ q, ds.length = groupSize * q + n.successor := by
          cases hmod with
          | inl h0 => exact False.elim (hlen_ne h0)
          | inr hex =>
            obtain ⟨q, hq⟩ := hex
            refine Or.inr ⟨q, ?_⟩
            apply CardinalNatural.Peano.successor_injective
            rw [← Sequences.List.length_firstElement, hq,
              CardinalNatural.Peano.add_successor]
        have hempty_new :
            ds.length = CardinalNatural.Peano.zero → n.successor = groupSize :=
          fun h0 => False.elim (hds_ne h0)
        have hwin :=
          rootWindow_bring_down currentRoot remainder d ds exponent
            groupSize n hle
        have hexp :
            (Sequences.List.firstElement d ds).length +
              rootPad groupSize n.successor.successor hle =
            ds.length + rootPad groupSize n.successor hle_new := by
          unfold rootPad
          rw [Sequences.List.length_firstElement,
            CardinalNatural.Peano.subtract_successor_eq_predecessor_subtract groupSize n.successor hle,
            CardinalNatural.Peano.successor_add, CardinalNatural.Peano.add_successor]
        have hbound_new :
            rootWindow currentRoot (Sequences.List.append remainder d) ds
              exponent groupSize n.successor hle_new <
            powerOfDecimal (listVal currentRoot).successor exponent *
              CardinalNatural.Peano.tenPower
                (ds.length + rootPad groupSize n.successor hle_new) := by
          rw [← hwin, ← hexp]
          exact hbound
        obtain ⟨ih_eq, ih_lt⟩ :=
          ih currentRoot (Sequences.List.append remainder d) n.successor
            hk_new hle_new hmod_ds hempty_new hbound_new
        constructor
        · exact hwin.trans ih_eq
        · exact ih_lt

theorem rootWithRemainder_cardinal_specification (a e : Decimal) :
    let result := rootWithRemainder a e
    toCardinalPeano a =
      powerOfDecimal (toCardinalPeano result.1) e +
        (match result.2 with
          | none => CardinalNatural.Peano.zero
          | some rem => toCardinalPeano rem) ∧
    toCardinalPeano a <
      powerOfDecimal (toCardinalPeano result.1).successor e := by
  unfold rootWithRemainder
  dsimp only
  cases h_aux : rootWithRemainderAuxiliary (powerListOrZero · e) a.val (toCardinalPeano e)
      Sequences.List.empty Sequences.List.empty
      (firstRootGroupSize a.val.length (toCardinalPeano e)
        (toCardinalPeano_ne_zero e)) with
  | mk rootDigits remDigits =>
    have hgs : toCardinalPeano e = toCardinalPeano e := rfl
    have hlen_ne := length_ne_zero_of_hasNonZero a.property
    have hk :=
      firstRootGroupSize_ne_zero a.val.length (toCardinalPeano e)
        (toCardinalPeano_ne_zero e)
    have hle :=
      firstRootGroupSize_le a.val.length (toCardinalPeano e)
        (toCardinalPeano_ne_zero e)
    have hmod :
        a.val.length = CardinalNatural.Peano.zero ∨
          ∃ q, a.val.length =
            toCardinalPeano e * q +
              firstRootGroupSize a.val.length (toCardinalPeano e)
                (toCardinalPeano_ne_zero e) :=
      Or.inr (firstRootGroupSize_mod a.val.length (toCardinalPeano e)
        (toCardinalPeano_ne_zero e) hlen_ne)
    have hempty :
        a.val.length = CardinalNatural.Peano.zero →
          firstRootGroupSize a.val.length (toCardinalPeano e)
            (toCardinalPeano_ne_zero e) = toCardinalPeano e :=
      fun h0 => False.elim (hlen_ne h0)
    have hwin0 := rootWindow_initial a e
      (firstRootGroupSize a.val.length (toCardinalPeano e)
        (toCardinalPeano_ne_zero e)) hle
    have hbound :
        rootWindow Sequences.List.empty Sequences.List.empty a.val e
          (toCardinalPeano e)
          (firstRootGroupSize a.val.length (toCardinalPeano e)
            (toCardinalPeano_ne_zero e)) hle <
        powerOfDecimal (listVal Sequences.List.empty).successor e *
          CardinalNatural.Peano.tenPower
            (a.val.length +
              rootPad (toCardinalPeano e)
                (firstRootGroupSize a.val.length (toCardinalPeano e)
                  (toCardinalPeano_ne_zero e)) hle) := by
      rw [hwin0]
      have hsucc0 :
          (listVal Sequences.List.empty).successor = CardinalNatural.Peano.one := rfl
      rw [hsucc0, powerOfDecimal_one, CardinalNatural.Peano.one_multiply]
      have hlt := toCardinalNaturalPeano_lt_tenPower a.val
      have hle_pow :
          CardinalNatural.Peano.tenPower a.val.length ≤
            CardinalNatural.Peano.tenPower
              (a.val.length +
                rootPad (toCardinalPeano e)
                  (firstRootGroupSize a.val.length (toCardinalPeano e)
                    (toCardinalPeano_ne_zero e)) hle) :=
        CardinalNatural.Peano.tenPower_monotone
          (CardinalNatural.Peano.le_add_self_left _ _)
      exact CardinalNatural.Peano.lt_of_lt_of_le hlt hle_pow
    have hspec :=
      rootWithRemainderAuxiliary_specification a.val e (toCardinalPeano e) rfl
        Sequences.List.empty Sequences.List.empty
        (firstRootGroupSize a.val.length (toCardinalPeano e)
          (toCardinalPeano_ne_zero e))
        hk hle hmod hempty hbound
    rw [h_aux] at hspec
    dsimp only at hspec
    rw [hwin0] at hspec
    obtain ⟨heq, hlt⟩ := hspec
    have hroot_nz : hasNonZero rootDigits = true := by
      by_cases hq : hasNonZero rootDigits = true
      · exact hq
      · have hz : listVal rootDigits = CardinalNatural.Peano.zero :=
          toCardinalNaturalPeano_zero_of_allZero
            (allZero_of_not_hasNonZero_bool hq)
        rw [hz, powerOfDecimal_zero, CardinalNatural.Peano.zero_add] at heq hlt
        have hsucc0 :
            CardinalNatural.Peano.zero.successor = CardinalNatural.Peano.one := rfl
        rw [hsucc0, powerOfDecimal_one] at hlt
        exact False.elim
          (CardinalNatural.Peano.not_positive_lt_one
            (CardinalNatural.Peano.zero_lt_of_ne_zero _
              (toCardinalPeano_ne_zero a))
            (heq ▸ hlt))
    have hlt_a :
        toCardinalPeano a < powerOfDecimal (listVal rootDigits).successor e := by
      rw [heq]
      exact hlt
    by_cases hr : hasNonZero remDigits = true
    · rw [dif_pos hroot_nz, dif_pos hr]
      dsimp
      exact ⟨heq, hlt_a⟩
    · rw [dif_pos hroot_nz, dif_neg hr]
      dsimp
      have hr_zero : listVal remDigits = CardinalNatural.Peano.zero :=
        toCardinalNaturalPeano_zero_of_allZero
          (allZero_of_not_hasNonZero_bool hr)
      rw [hr_zero, CardinalNatural.Peano.add_zero] at heq
      exact ⟨heq, hlt_a⟩

def Divisible (a b : Decimal) : Prop := ∃ c, b * c ≈ a

theorem Divisible_toPeano (a b : Decimal) : Divisible a b ↔ Peano.Divisible a.toPeano b.toPeano := by
  apply Iff.intro
  · intro h
    unfold Divisible at h
    unfold Peano.Divisible
    obtain ⟨c, hc⟩ := h
    exists c.toPeano
    rw [← multiply_toPeano]
    exact toPeano_eq_of_equivalent hc
  · intro h
    unfold Divisible
    unfold Peano.Divisible at h
    obtain ⟨c_peano, hc⟩ := h
    let c := fromPeano c_peano
    exists c
    apply equivalent_of_toPeano_eq
    rw [multiply_toPeano]
    have h_c_toPeano : c.toPeano = c_peano := toPeano_fromPeano c_peano
    rw [h_c_toPeano]
    exact hc

def Even (a : Decimal) : Prop := Divisible a two

def Odd (a : Decimal) : Prop := ¬ Even a

theorem toPeano_two : toPeano two = Peano.two := by
  unfold two Peano.two
  rw [successor_toPeano, toPeano_one]

theorem Even_toPeano (a : Decimal) : Even a ↔ Peano.Even a.toPeano := by
  unfold Even Peano.Even
  rw [Divisible_toPeano, toPeano_two]

theorem Odd_toPeano (a : Decimal) : Odd a ↔ Peano.Odd a.toPeano := by
  unfold Odd Peano.Odd
  rw [Even_toPeano]

def lastDigit (a : Decimal) : Digit :=
  Sequences.List.lastElement a.val (hasNonZero_ne_empty a.property)

def isEven (a : Decimal) : Bool :=
  CardinalNatural.Peano.isEven (lastDigit a).val

def isOdd (a : Decimal) : Bool := !isEven a

theorem even_toPeano_iff_toCardinalPeano (a : Decimal) :
    Peano.Even a.toPeano ↔ CardinalNatural.Peano.Even (toCardinalPeano a) := by
  constructor
  · intro h
    unfold Peano.Even Peano.Divisible at h
    rcases h with ⟨c, hc⟩
    unfold CardinalNatural.Peano.Even CardinalNatural.Peano.Divisible
    refine ⟨CardinalNatural.Peano.two_ne_zero, CardinalNatural.Peano.fromOrdinal c, ?_⟩
    have h1 := congrArg CardinalNatural.Peano.fromOrdinal hc
    rw [CardinalNatural.Peano.fromOrdinal_multiply] at h1
    change CardinalNatural.Peano.two * CardinalNatural.Peano.fromOrdinal c =
      CardinalNatural.Peano.fromOrdinal a.toPeano at h1
    unfold toPeano at h1
    rw [CardinalNatural.Peano.fromOrdinal_toOrdinal] at h1
    exact h1
  · intro h
    unfold CardinalNatural.Peano.Even CardinalNatural.Peano.Divisible at h
    rcases h with ⟨_, c, hc⟩
    have hc_ne : c ≠ CardinalNatural.Peano.zero := by
      intro hz
      rw [hz, CardinalNatural.Peano.multiply_zero] at hc
      exact toCardinalPeano_ne_zero a hc.symm
    unfold Peano.Even Peano.Divisible
    refine ⟨CardinalNatural.Peano.toOrdinal c hc_ne, ?_⟩
    apply CardinalNatural.Peano.eq_of_fromOrdinal_eq
    rw [CardinalNatural.Peano.fromOrdinal_multiply]
    change CardinalNatural.Peano.two * CardinalNatural.Peano.fromOrdinal
        (CardinalNatural.Peano.toOrdinal c hc_ne) =
      CardinalNatural.Peano.fromOrdinal a.toPeano
    rw [CardinalNatural.Peano.fromOrdinal_toOrdinal]
    unfold toPeano
    rw [CardinalNatural.Peano.fromOrdinal_toOrdinal]
    exact hc

theorem even_toCardinalPeano_iff_lastDigit (a : Decimal) :
    CardinalNatural.Peano.Even (toCardinalPeano a) ↔
      CardinalNatural.Peano.Even (lastDigit a).val := by
  unfold toCardinalPeano lastDigit
  exact toCardinalNaturalPeano_even_iff_lastElement a.val (hasNonZero_ne_empty a.property)

theorem isEven_correct (x : Decimal) : Even x ↔ isEven x := by
  rw [Even_toPeano, even_toPeano_iff_toCardinalPeano,
    even_toCardinalPeano_iff_lastDigit]
  unfold isEven
  exact CardinalNatural.Peano.isEven_correct (lastDigit x).val

theorem isOdd_correct (x : Decimal) : Odd x ↔ isOdd x := by
  unfold Odd isOdd
  rw [isEven_correct]
  cases isEven x <;> simp

instance decidableEven (x : Decimal) : Decidable (Even x) :=
  decidable_of_iff' (isEven x) (isEven_correct x)

instance decidableOdd (x : Decimal) : Decidable (Odd x) :=
  decidable_of_iff' (isOdd x) (isOdd_correct x)

theorem even_successor {x : Decimal} (h : Even x) : Odd (successor x) := by
  rw [Odd_toPeano, successor_toPeano]
  exact Peano.even_successor ((Even_toPeano x).mp h)

theorem odd_successor {x : Decimal} (h : Odd x) : Even (successor x) := by
  rw [Even_toPeano, successor_toPeano]
  exact Peano.odd_successor ((Odd_toPeano x).mp h)

theorem even_predecessor {x : Decimal} (h : Even x) : ∃ h_ne, Odd (predecessor x h_ne) := by
  have h_peano_even := (Even_toPeano x).mp h
  obtain ⟨h_ne_peano, h_odd_peano⟩ := Peano.even_predecessor h_peano_even
  have h_ne : ¬ x ≈ one := by
    intro heq
    exact h_ne_peano ((toPeano_eq_of_equivalent heq).trans toPeano_one)
  refine ⟨h_ne, ?_⟩
  rw [Odd_toPeano]
  obtain ⟨h2, hpred⟩ := predecessor_toPeano x h_ne
  rw [hpred, Peano.predecessor_congr h2 h_ne_peano rfl]
  exact h_odd_peano

theorem odd_predecessor {x : Decimal} (h_odd : Odd x) (h_ne : ¬ x ≈ one) :
    Even (predecessor x h_ne) := by
  rw [Even_toPeano]
  obtain ⟨h2, hpred⟩ := predecessor_toPeano x h_ne
  have h_ne_peano : x.toPeano ≠ Peano.one := by
    intro heq
    exact h_ne (equivalent_of_toPeano_eq (heq.trans toPeano_one.symm))
  rw [hpred, Peano.predecessor_congr h2 h_ne_peano rfl]
  exact Peano.odd_predecessor ((Odd_toPeano x).mp h_odd) h_ne_peano

def divideWithRemainder (a b : Decimal) : Option Decimal × Option Decimal :=
  let (qDigits, rDigits) := divideWithRemainderAuxiliary a.val b.val .empty .empty
  let q : Option Decimal :=
    if h : hasNonZero qDigits then
      some ⟨qDigits, hasNonZero_of_hasNonZero_bool h⟩
    else
      none
  let r : Option Decimal :=
    if h : hasNonZero rDigits then
      some ⟨rDigits, hasNonZero_of_hasNonZero_bool h⟩
    else
      none
  (q, r)

def isDivisible (a b : Decimal) : Bool :=
  match divideWithRemainder a b with
  | (_, none) => true
  | (_, some _) => false

def tryDivide (a b : Decimal) : Option Decimal :=
  match divideWithRemainder a b with
  | (some q, none) => q
  | _ => none

def optionToCardinal : Option Decimal → CardinalNatural.Peano
  | none => CardinalNatural.Peano.zero
  | some d => toCardinalPeano d

theorem divideWithRemainder_cardinal_specification (x y : Decimal) :
    let result := divideWithRemainder x y
    toCardinalPeano x =
        toCardinalPeano y * optionToCardinal result.1 +
          optionToCardinal result.2 ∧
      optionToCardinal result.2 < toCardinalPeano y := by
  unfold divideWithRemainder
  dsimp only
  cases h_aux : divideWithRemainderAuxiliary x.val y.val Sequences.List.empty Sequences.List.empty with
  | mk qDigits rDigits =>
      have hdiv : toCardinalNaturalPeano y.val CardinalNatural.Peano.zero ≠ CardinalNatural.Peano.zero :=
        toCardinalPeano_ne_zero y
      have hrem : toCardinalNaturalPeano Sequences.List.empty CardinalNatural.Peano.zero <
          toCardinalNaturalPeano y.val CardinalNatural.Peano.zero := by
        exact CardinalNatural.Peano.zero_lt_of_ne_zero _ hdiv
      have hspec := divideWithRemainderAuxiliary_specification x.val y.val
        Sequences.List.empty Sequences.List.empty hrem
      rw [h_aux] at hspec
      dsimp only at hspec
      obtain ⟨h_eq_raw, h_lt_raw⟩ := hspec
      have h_eq :
          toCardinalPeano x =
            toCardinalPeano y * toCardinalNaturalPeano qDigits CardinalNatural.Peano.zero +
              toCardinalNaturalPeano rDigits CardinalNatural.Peano.zero := by
        unfold toCardinalPeano
        simpa [toCardinalNaturalPeano, CardinalNatural.Peano.zero_multiply,
          CardinalNatural.Peano.zero_add] using h_eq_raw
      have h_lt :
          toCardinalNaturalPeano rDigits CardinalNatural.Peano.zero < toCardinalPeano y := by
        unfold toCardinalPeano
        exact h_lt_raw
      by_cases hq : hasNonZero qDigits = true
      · by_cases hr : hasNonZero rDigits = true
        · simp [optionToCardinal, hq, hr, toCardinalPeano]
          exact ⟨h_eq, h_lt⟩
        · simp [optionToCardinal, hq, hr, toCardinalPeano]
          have hr_zero : toCardinalNaturalPeano rDigits CardinalNatural.Peano.zero =
              CardinalNatural.Peano.zero :=
            toCardinalNaturalPeano_zero_of_allZero (allZero_of_not_hasNonZero_bool hr)
          rw [hr_zero, CardinalNatural.Peano.add_zero] at h_eq
          exact ⟨h_eq, CardinalNatural.Peano.zero_lt_of_ne_zero _ hdiv⟩
      · have hq_zero : toCardinalNaturalPeano qDigits CardinalNatural.Peano.zero =
            CardinalNatural.Peano.zero :=
          toCardinalNaturalPeano_zero_of_allZero (allZero_of_not_hasNonZero_bool hq)
        by_cases hr : hasNonZero rDigits = true
        · simp [optionToCardinal, hq, hr, toCardinalPeano]
          rw [hq_zero] at h_eq
          exact ⟨h_eq, h_lt⟩
        · simp [optionToCardinal, hq, hr, toCardinalPeano]
          have hr_zero : toCardinalNaturalPeano rDigits CardinalNatural.Peano.zero =
              CardinalNatural.Peano.zero :=
            toCardinalNaturalPeano_zero_of_allZero (allZero_of_not_hasNonZero_bool hr)
          rw [hq_zero, hr_zero, CardinalNatural.Peano.add_zero] at h_eq
          exact ⟨h_eq, CardinalNatural.Peano.zero_lt_of_ne_zero _ hdiv⟩

theorem toPeano_eq_of_toCardinalPeano_eq {x y : Decimal}
    (h : toCardinalPeano x = toCardinalPeano y) :
    x.toPeano = y.toPeano := by
  apply CardinalNatural.Peano.eq_of_fromOrdinal_eq
  unfold toPeano
  rw [CardinalNatural.Peano.fromOrdinal_toOrdinal,
    CardinalNatural.Peano.fromOrdinal_toOrdinal]
  exact h

theorem toPeano_eq_multiply_of_toCardinalPeano_eq
    {x y q : Decimal}
    (h : toCardinalPeano x = toCardinalPeano y * toCardinalPeano q) :
    x.toPeano = y.toPeano * q.toPeano := by
  apply CardinalNatural.Peano.eq_of_fromOrdinal_eq
  unfold toPeano
  rw [CardinalNatural.Peano.fromOrdinal_toOrdinal]
  rw [CardinalNatural.Peano.fromOrdinal_multiply]
  rw [CardinalNatural.Peano.fromOrdinal_toOrdinal,
    CardinalNatural.Peano.fromOrdinal_toOrdinal]
  exact h

theorem toPeano_eq_multiply_add_of_toCardinalPeano_eq
    {x y q r : Decimal}
    (h : toCardinalPeano x =
        toCardinalPeano y * toCardinalPeano q + toCardinalPeano r) :
    x.toPeano = y.toPeano * q.toPeano + r.toPeano := by
  apply CardinalNatural.Peano.eq_of_fromOrdinal_eq
  unfold toPeano
  rw [CardinalNatural.Peano.fromOrdinal_toOrdinal]
  rw [CardinalNatural.Peano.fromOrdinal_add, CardinalNatural.Peano.fromOrdinal_multiply]
  rw [CardinalNatural.Peano.fromOrdinal_toOrdinal,
    CardinalNatural.Peano.fromOrdinal_toOrdinal,
    CardinalNatural.Peano.fromOrdinal_toOrdinal]
  exact h

theorem toPeano_lt_of_toCardinalPeano_lt {x y : Decimal}
    (h : toCardinalPeano x < toCardinalPeano y) :
    x.toPeano < y.toPeano :=
  (toPeano_lt_iff_toCardinalPeano_lt x y).mpr h

theorem rootWithRemainder_toPeano (a e : Decimal)
    {b : Decimal} {r : Option Decimal}
    (h : rootWithRemainder a e = (b, r)) :
    Peano.rootWithRemainder a.toPeano e.toPeano =
      (b.toPeano, Option.map toPeano r) := by
  have hspec := rootWithRemainder_cardinal_specification a e
  rw [h] at hspec
  dsimp only at hspec
  have hpow_b : powerOfDecimal (toCardinalPeano b) e = toCardinalPeano (power b e) :=
    powerOfDecimal_eq_toCardinal_power b e
  have hpow_succ :
      powerOfDecimal (toCardinalPeano b).successor e =
        toCardinalPeano (power b.successor e) := by
    rw [← toCardinalPeano_successor]
    exact powerOfDecimal_eq_toCardinal_power b.successor e
  cases r with
  | none =>
    dsimp at hspec
    obtain ⟨heq, _⟩ := hspec
    apply Peano.rootWithRemainder_eq_of_none
    have heq' : toCardinalPeano a = toCardinalPeano (power b e) :=
      heq.trans hpow_b
    have hpeano := toPeano_eq_of_toCardinalPeano_eq heq'
    rwa [power_toPeano] at hpeano
  | some rem =>
    dsimp at hspec
    obtain ⟨heq, hlt⟩ := hspec
    apply Peano.rootWithRemainder_eq_of_some
    · have heq' : toCardinalPeano a = toCardinalPeano (power b e + rem) := by
        rw [toCardinalPeano_add, ← hpow_b]
        exact heq
      have hpeano := toPeano_eq_of_toCardinalPeano_eq heq'
      rwa [add_toPeano, power_toPeano] at hpeano
    · have hlt' : toCardinalPeano a < toCardinalPeano (power b.successor e) :=
        hpow_succ ▸ hlt
      have hpeano := toPeano_lt_of_toCardinalPeano_lt hlt'
      rwa [power_toPeano, successor_toPeano] at hpeano

theorem rootWithRemainder_some_power (a e b r : Decimal) (h : Power e a)
    (hres : rootWithRemainder a e = (b, some r)) : False :=
  Peano.rootWithRemainder_some_power a.toPeano e.toPeano b.toPeano r.toPeano
    ((Power_toPeano e a).mp h) (rootWithRemainder_toPeano a e hres)

def tryRoot (e a : Decimal) : Option Decimal :=
  match rootWithRemainder a e with
  | (b, none) => b
  | _ => none

def root (e a : Decimal) (h : Power e a) : Decimal :=
  match hres : rootWithRemainder a e with
  | (b, none) => b
  | (b, some r) => False.elim (rootWithRemainder_some_power a e b r h hres)

theorem root_toPeano (e a : Decimal) (h : Power e a) :
    ∃ h2, (root e a h).toPeano = Peano.root e.toPeano a.toPeano h2 := by
  let h2 := (Power_toPeano e a).mp h
  refine ⟨h2, ?_⟩
  unfold root
  split
  · next b hres =>
    have hp := rootWithRemainder_toPeano a e hres
    unfold Peano.root
    split
    · next b' hres' =>
      have heq : (b', none) = (b.toPeano, none) := hres'.symm.trans hp
      exact (congrArg Prod.fst heq).symm
    · next b' r' hres' =>
      exact False.elim
        (Peano.rootWithRemainder_some_power a.toPeano e.toPeano b' r' h2 hres')
  · next b r hres =>
    exact False.elim (rootWithRemainder_some_power a e b r h hres)

theorem root_correct (e a : Decimal) (h : Power e a) : (root e a h) ^ e ≈ a := by
  apply equivalent_of_toPeano_eq
  obtain ⟨h2, hroot⟩ := root_toPeano e a h
  simp only [HPow.hPow]
  rw [power_toPeano, hroot]
  exact Peano.root_correct e.toPeano a.toPeano h2

theorem root_power_eq (e x : Decimal) : ∃ h, root e (x ^ e) h ≈ x := by
  let h : Power e (x ^ e) := ⟨x, rfl⟩
  exists h
  apply equivalent_of_toPeano_eq
  have hcorrect := toPeano_eq_of_equivalent (root_correct e (x ^ e) h)
  simp only [HPow.hPow] at hcorrect
  rw [power_toPeano, power_toPeano x e] at hcorrect
  exact Peano.power_cancel_left e.toPeano (root e (x ^ e) h).toPeano x.toPeano hcorrect

theorem tryRoot_toPeano (e a : Decimal) :
    Option.map toPeano (tryRoot e a) = Peano.tryRoot e.toPeano a.toPeano := by
  cases hres : rootWithRemainder a e with
  | mk b r =>
    have hp := rootWithRemainder_toPeano a e hres
    cases r with
    | none =>
      have htry : tryRoot e a = some b := by
        simp only [tryRoot, hres]
      have hp' : Peano.rootWithRemainder a.toPeano e.toPeano = (b.toPeano, none) := by
        simpa using hp
      have htryP : Peano.tryRoot e.toPeano a.toPeano = some b.toPeano := by
        simp only [Peano.tryRoot, hp']
      rw [htry, htryP]
      rfl
    | some rem =>
      have htry : tryRoot e a = none := by
        simp only [tryRoot, hres]
      have hp' : Peano.rootWithRemainder a.toPeano e.toPeano =
          (b.toPeano, some rem.toPeano) := by
        simpa using hp
      have htryP : Peano.tryRoot e.toPeano a.toPeano = none := by
        simp only [Peano.tryRoot, hp']
      rw [htry, htryP]
      rfl

theorem divideWithRemainder_toPeano (x y : Decimal)
    {a b : Option Decimal}
    (h : divideWithRemainder x y = (a, b)) :
    Peano.divideWithRemainder x.toPeano y.toPeano =
      (Option.map toPeano a, Option.map toPeano b) := by
  have hspec := divideWithRemainder_cardinal_specification x y
  rw [h] at hspec
  dsimp only at hspec
  cases a with
  | none =>
      cases b with
      | none =>
          dsimp [optionToCardinal] at hspec
          obtain ⟨h_eq, _⟩ := hspec
          exact False.elim (toCardinalPeano_ne_zero x h_eq)
      | some r =>
          dsimp [optionToCardinal] at hspec
          obtain ⟨h_eq, h_lt⟩ := hspec
          rw [CardinalNatural.Peano.multiply_zero,
            CardinalNatural.Peano.zero_add] at h_eq
          have hx_lt : toCardinalPeano x < toCardinalPeano y := by
            rw [h_eq]
            exact h_lt
          apply Peano.divideWithRemainder_eq_of_none_some
          · exact toPeano_lt_of_toCardinalPeano_lt hx_lt
          · exact toPeano_eq_of_toCardinalPeano_eq h_eq
  | some q =>
      cases b with
      | none =>
          dsimp [optionToCardinal] at hspec
          obtain ⟨h_eq, _⟩ := hspec
          apply Peano.divideWithRemainder_eq_of_some_none
          exact toPeano_eq_multiply_of_toCardinalPeano_eq h_eq
      | some r =>
          dsimp [optionToCardinal] at hspec
          obtain ⟨h_eq, h_lt⟩ := hspec
          apply Peano.divideWithRemainder_eq_of_some_some
          · exact toPeano_lt_of_toCardinalPeano_lt h_lt
          · exact toPeano_eq_multiply_add_of_toCardinalPeano_eq h_eq

theorem isDivisible_eq_peano (a b : Decimal) :
    isDivisible a b = Peano.isDivisible a.toPeano b.toPeano := by
  cases h : divideWithRemainder a b with
  | mk qa ra =>
    have hp := divideWithRemainder_toPeano a b h
    simp only [isDivisible, Peano.isDivisible, h, hp]
    cases ra <;> rfl

theorem isDivisible_correct (a b : Decimal) : Divisible a b ↔ isDivisible a b := by
  rw [Divisible_toPeano, isDivisible_eq_peano]
  exact Peano.isDivisible_correct a.toPeano b.toPeano

theorem divideWithRemainder_not_none_none (a b : Decimal) :
    divideWithRemainder a b ≠ (none, none) := by
  intro h
  have hp := divideWithRemainder_toPeano a b h
  exact Peano.divideWithRemainder_not_none_none a.toPeano b.toPeano hp

theorem divideWithRemainder_none_some_divisible (a b : Decimal) (r : Decimal)
    (h : Divisible a b) (hres : divideWithRemainder a b = (none, some r)) : False := by
  have hp := divideWithRemainder_toPeano a b hres
  have hpeano : Peano.Divisible a.toPeano b.toPeano := (Divisible_toPeano a b).mp h
  exact Peano.divideWithRemainder_none_some_divisible a.toPeano b.toPeano r.toPeano
    hpeano hp

theorem divideWithRemainder_some_some_divisible (a b : Decimal) (q r : Decimal)
    (h : Divisible a b) (hres : divideWithRemainder a b = (some q, some r)) : False := by
  have hp := divideWithRemainder_toPeano a b hres
  have hpeano : Peano.Divisible a.toPeano b.toPeano := (Divisible_toPeano a b).mp h
  exact Peano.divideWithRemainder_some_some_divisible a.toPeano b.toPeano q.toPeano
    r.toPeano hpeano hp

def divide (a b : Decimal) (h : Divisible a b) : Decimal :=
  match hres : divideWithRemainder a b with
  | (some q, none) => q
  | (none, none) => False.elim (divideWithRemainder_not_none_none a b hres)
  | (none, some r) => False.elim (divideWithRemainder_none_some_divisible a b r h hres)
  | (some q, some r) => False.elim (divideWithRemainder_some_some_divisible a b q r h hres)

theorem divide_toPeano {x y z : Decimal} (h : Divisible x y)
    (hz : divide x y h = z) :
    ∃ h2, Peano.divide x.toPeano y.toPeano h2 = z.toPeano := by
  let h2 := (Divisible_toPeano x y).mp h
  refine ⟨h2, ?_⟩
  have hres : divideWithRemainder x y = (some z, none) := by
    unfold divide at hz
    split at hz
    · next q hq =>
      rw [← hz]
      exact hq
    · next hq =>
      exact False.elim (divideWithRemainder_not_none_none x y hq)
    · next r hq =>
      exact False.elim (divideWithRemainder_none_some_divisible x y r h hq)
    · next q r hq =>
      exact False.elim (divideWithRemainder_some_some_divisible x y q r h hq)
  have hp : Peano.divideWithRemainder x.toPeano y.toPeano = (some z.toPeano, none) := by
    simpa using divideWithRemainder_toPeano x y hres
  apply Peano.multiply_cancel_left y.toPeano
  rw [Peano.divide_correct x.toPeano y.toPeano h2]
  exact Peano.divideWithRemainder_some_none x.toPeano y.toPeano z.toPeano hp

theorem exists_divide_of_tryDivide {x y z : Decimal} (h : tryDivide x y = some z) :
    ∃ h', divide x y h' = z := by
  have hres : divideWithRemainder x y = (some z, none) := by
    unfold tryDivide at h
    split at h
    · next q hq =>
      injection h with hz
      rw [← hz]
      exact hq
    · next _ _ =>
      cases h
  have hdiv : Divisible x y :=
    (isDivisible_correct x y).mpr (by simp [isDivisible, hres])
  refine ⟨hdiv, ?_⟩
  unfold divide
  split
  · next q hq =>
    have hcongr := hq.symm.trans hres
    injection hcongr with hqz _
    injection hqz
  · next hq =>
    exact False.elim (divideWithRemainder_not_none_none x y hq)
  · next r hq =>
    exact False.elim (divideWithRemainder_none_some_divisible x y r hdiv hq)
  · next q r hq =>
    exact False.elim (divideWithRemainder_some_some_divisible x y q r hdiv hq)

theorem tryDivide_of_divide {x y z : Decimal} (h : ∃ h', divide x y h' = z) :
    tryDivide x y = some z := by
  obtain ⟨hdiv, heq⟩ := h
  have hres : divideWithRemainder x y = (some z, none) := by
    unfold divide at heq
    split at heq
    · next q hq =>
      rw [← heq]
      exact hq
    · next hq =>
      exact False.elim (divideWithRemainder_not_none_none x y hq)
    · next r hq =>
      exact False.elim (divideWithRemainder_none_some_divisible x y r hdiv hq)
    · next q r hq =>
      exact False.elim (divideWithRemainder_some_some_divisible x y q r hdiv hq)
  simp [tryDivide, hres]

theorem divide_correct (a b : Decimal) (h : Divisible a b) :
    b * divide a b h ≈ a := by
  unfold divide
  split
  · next q hres =>
    have hp := divideWithRemainder_toPeano a b hres
    have heq := Peano.divideWithRemainder_some_none a.toPeano b.toPeano q.toPeano hp
    apply equivalent_of_toPeano_eq
    rw [multiply_toPeano]
    exact heq.symm
  · next hres =>
    exact False.elim (divideWithRemainder_not_none_none a b hres)
  · next r hres =>
    exact False.elim (divideWithRemainder_none_some_divisible a b r h hres)
  · next q r hres =>
    exact False.elim (divideWithRemainder_some_some_divisible a b q r h hres)

/-- A successful `tryDivide a b = some q` means `a ≈ b * q`. -/
theorem equivalent_of_tryDivide_multiply (a b q : Decimal)
    (h : tryDivide a b = some q) : a ≈ b * q := by
  obtain ⟨hdiv, heq⟩ := exists_divide_of_tryDivide h
  exact Setoid.trans (Setoid.symm (divide_correct a b hdiv))
    (by
      rw [heq]
      exact Setoid.refl _)

theorem divide_multiply_eq (x y : Decimal) : ∃ h, divide (y * x) y h ≈ x := by
  let h : Divisible (y * x) y := ⟨x, rfl⟩
  refine ⟨h, ?_⟩
  have heq := divide_correct (y * x) y h
  apply equivalent_of_toPeano_eq
  have hpeano := toPeano_eq_of_equivalent heq
  rw [multiply_toPeano, multiply_toPeano] at hpeano
  exact Peano.multiply_cancel_left y.toPeano (divide (y * x) y h).toPeano x.toPeano hpeano

theorem divide_add (x y z : Decimal) (h : Divisible x z) (h2 : Divisible y z) :
  ∃ h3, divide x z h + divide y z h2 ≈ divide (x + y) z h3 := by
  let h3 : Divisible (x + y) z :=
    ⟨divide x z h + divide y z h2, by
      apply equivalent_of_toPeano_eq
      have hx := toPeano_eq_of_equivalent (divide_correct x z h)
      have hy := toPeano_eq_of_equivalent (divide_correct y z h2)
      rw [multiply_toPeano, add_toPeano, add_toPeano, Peano.multiply_add]
      rw [multiply_toPeano] at hx hy
      rw [hx, hy]⟩
  refine ⟨h3, ?_⟩
  apply equivalent_of_toPeano_eq
  have hxy := toPeano_eq_of_equivalent (divide_correct (x + y) z h3)
  have hx := toPeano_eq_of_equivalent (divide_correct x z h)
  have hy := toPeano_eq_of_equivalent (divide_correct y z h2)
  rw [multiply_toPeano, add_toPeano] at hxy
  rw [multiply_toPeano] at hx hy
  exact Peano.multiply_cancel_left z.toPeano
    (divide x z h + divide y z h2).toPeano
    (divide (x + y) z h3).toPeano
    (by
      rw [add_toPeano, Peano.multiply_add, hx, hy]
      exact hxy.symm)

theorem divide_subtract_distrib {x y z : Decimal}
    (h1 : Divisible x z) (h2 : Divisible y z) (h3 : x > y) :
    ∃ h4 h5, divide (subtract x y h3) z h4 ≈
      subtract (divide x z h1) (divide y z h2) h5 := by
  let qx := divide x z h1
  let qy := divide y z h2
  have hx := toPeano_eq_of_equivalent (divide_correct x z h1)
  have hy := toPeano_eq_of_equivalent (divide_correct y z h2)
  rw [multiply_toPeano] at hx hy
  have h5 : qy < qx := by
    apply lt_of_toCardinalPeano_lt
    have hx_card := toCardinalPeano_eq_of_equivalent (divide_correct x z h1)
    have hy_card := toCardinalPeano_eq_of_equivalent (divide_correct y z h2)
    rw [multiply_toCardinalPeano] at hx_card hy_card
    have hmul :
        toCardinalPeano z * toCardinalPeano qy <
          toCardinalPeano z * toCardinalPeano qx := by
      rw [hy_card, hx_card]
      exact toCardinalPeano_lt_of_lt h3
    have h_le :=
      CardinalNatural.Peano.le_of_multiply_le_multiply_left
        (toCardinalPeano z) (toCardinalPeano qy) (toCardinalPeano qx)
        (toCardinalPeano_ne_zero z) (Or.inl hmul)
    cases h_le with
    | inl hlt => exact hlt
    | inr heq =>
      rw [heq] at hmul
      exact False.elim (CardinalNatural.Peano.not_lt_self _ hmul)
  have h_wit : z * subtract qx qy h5 ≈ subtract x y h3 := by
    apply equivalent_of_toPeano_eq
    rcases multiply_subtract_distributive z qx qy h5 with ⟨hmul_lt, hdist⟩
    have hdist_peano := toPeano_eq_of_equivalent hdist
    rcases subtract_toPeano (z * qx) (z * qy) hmul_lt with ⟨h_peano_lt, h_sub_mul⟩
    rcases subtract_toPeano x y h3 with ⟨h_peano_xy, h_sub_xy⟩
    have h_eq_sub :=
      Peano.subtract_eq_of_eq h_peano_lt h_peano_xy
        (by rw [multiply_toPeano]; exact hx)
        (by rw [multiply_toPeano]; exact hy)
    calc (z * subtract qx qy h5).toPeano
        = (subtract (z * qx) (z * qy) hmul_lt).toPeano := hdist_peano
      _ = Peano.subtract (z * qx).toPeano (z * qy).toPeano h_peano_lt := h_sub_mul
      _ = Peano.subtract x.toPeano y.toPeano h_peano_xy := h_eq_sub
      _ = (subtract x y h3).toPeano := h_sub_xy.symm
  let h4 : Divisible (subtract x y h3) z := ⟨subtract qx qy h5, h_wit⟩
  refine ⟨h4, h5, ?_⟩
  apply equivalent_of_toPeano_eq
  have hdiv := toPeano_eq_of_equivalent (divide_correct (subtract x y h3) z h4)
  have hw := toPeano_eq_of_equivalent h_wit
  rw [multiply_toPeano] at hdiv hw
  exact Peano.multiply_cancel_left z.toPeano
    (divide (subtract x y h3) z h4).toPeano
    (subtract qx qy h5).toPeano
    (hdiv.trans hw.symm)

theorem multiply_divide_associative (x y z : Decimal) (h : Divisible y z) :
  ∃ h2, x * divide y z h ≈ divide (x * y) z h2 := by
  let h2 : Divisible (x * y) z :=
    ⟨x * divide y z h, by
      apply equivalent_of_toPeano_eq
      have hy := toPeano_eq_of_equivalent (divide_correct y z h)
      rw [multiply_toPeano] at hy
      rw [multiply_toPeano, multiply_toPeano]
      rw [← Peano.multiply_associative]
      have hzx : z.toPeano * x.toPeano = x.toPeano * z.toPeano :=
        Peano.multiply_commutative z.toPeano x.toPeano
      rw [hzx, Peano.multiply_associative, hy, ← multiply_toPeano]⟩
  refine ⟨h2, ?_⟩
  apply equivalent_of_toPeano_eq
  have hxy := toPeano_eq_of_equivalent (divide_correct (x * y) z h2)
  have hy := toPeano_eq_of_equivalent (divide_correct y z h)
  rw [multiply_toPeano] at hxy hy
  exact Peano.multiply_cancel_left z.toPeano
    (x * divide y z h).toPeano
    (divide (x * y) z h2).toPeano
    (by
      rw [multiply_toPeano, ← Peano.multiply_associative]
      have hzx : z.toPeano * x.toPeano = x.toPeano * z.toPeano :=
        Peano.multiply_commutative z.toPeano x.toPeano
      rw [hzx, Peano.multiply_associative, hy, ← multiply_toPeano]
      exact hxy.symm)

theorem divide_divide_eq_divide_multiply_h2 {x y z : Decimal}
    (h1 : Divisible x (y * z)) : Divisible x y := by
  rcases h1 with ⟨c, hc⟩
  exact ⟨z * c, by
    apply equivalent_of_toPeano_eq
    have hc' := toPeano_eq_of_equivalent hc
    rw [multiply_toPeano, multiply_toPeano] at hc' ⊢
    rw [← Peano.multiply_associative, hc']⟩

theorem divide_divide_eq_divide_multiply (x y z : Decimal) (h1 : Divisible x (y * z)) :
  ∃ h2 h3, divide x (y * z) h1 ≈ divide (divide x y h2) z h3 := by
  let h2 : Divisible x y := divide_divide_eq_divide_multiply_h2 h1
  let q : Decimal := divide x (y * z) h1
  let r : Decimal := divide x y h2
  have hzq_eq_r : z * q ≈ r := by
    apply equivalent_of_toPeano_eq
    have hxyz := toPeano_eq_of_equivalent (divide_correct x (y * z) h1)
    have hxy := toPeano_eq_of_equivalent (divide_correct x y h2)
    rw [multiply_toPeano] at hxyz hxy
    have hyzq_eq_yr :
        y.toPeano * (z * q).toPeano = y.toPeano * r.toPeano := by
      rw [multiply_toPeano, ← Peano.multiply_associative, ← multiply_toPeano, hxyz, hxy]
    exact Peano.multiply_cancel_left y.toPeano (z * q).toPeano r.toPeano hyzq_eq_yr
  let h3 : Divisible r z := ⟨q, hzq_eq_r⟩
  refine ⟨h2, h3, ?_⟩
  apply equivalent_of_toPeano_eq
  have hdiv := toPeano_eq_of_equivalent (divide_correct r z h3)
  have hw := toPeano_eq_of_equivalent hzq_eq_r
  rw [multiply_toPeano] at hdiv hw
  exact Peano.multiply_cancel_left z.toPeano q.toPeano (divide r z h3).toPeano
    (hw.trans hdiv.symm)

instance {n : Nat} : OfNat Decimal n.succ where
  ofNat := fromPeano (Peano.fromNat n.succ (Nat.succ_ne_zero n))

instance : ToString Decimal where
  toString d := Digits.listToString d.normalize.val

instance : Repr Decimal where
  reprPrec d _ := toString d

instance : ReprAtom Decimal := ⟨⟩

instance : BEq Decimal where
  beq a b := decide (a ≈ b)

instance : Ord Decimal where
  compare a b :=
    if a < b then .lt
    else if b < a then .gt
    else .eq

example : (1 : Decimal) = one := rfl
example : (2 : Decimal) = two := rfl
example : toString (1 : Decimal) = "1" := rfl
example : ((1 : Decimal) == (1 : Decimal)) = true := rfl
example : compare (1 : Decimal) (2 : Decimal) = .lt := by decide

end Decimal

end ZeroMath.Numbers.OrdinalNatural
