import ZeroMath.Logic
import ZeroMath.Numbers.CardinalNatural.Decimal
import ZeroMath.Numbers.CardinalNatural.Peano
import ZeroMath.Numbers.Digits.Decimal
import ZeroMath.Numbers.Digits.Decimal.Lists
import ZeroMath.Numbers.Integer.Peano
import ZeroMath.Numbers.OrdinalNatural.Decimal
import ZeroMath.Sequences.List

namespace ZeroMath.Numbers.Integer

namespace Decimal

inductive Sign where
  | plus
  | minus

deriving instance DecidableEq for Sign

abbrev Digit := Digits.Decimal

end Decimal

/-- Decimal representation of an integer: an optional sign and a non-empty digit list. -/
structure Decimal where
  sign : Option Decimal.Sign
  digits : { l : Sequences.List Decimal.Digit // l ≠ Sequences.List.empty }

namespace Decimal

instance : DecidableEq Decimal :=
  fun x y =>
    match decEq x.sign y.sign, decEq x.digits.val y.digits.val with
    | isTrue hs, isTrue hd =>
      isTrue (by
        cases x
        cases y
        cases hs
        exact Decimal.mk.injEq _ _ _ _ ▸ ⟨rfl, Subtype.ext hd⟩)
    | isFalse hs, _ =>
      isFalse (fun h => by cases h; exact hs rfl)
    | _, isFalse hd =>
      isFalse (fun h => by
        cases h
        exact hd (congrArg Subtype.val (by rfl)))

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
  hasNonZero_ne_empty length_ne_zero_of_hasNonZero hasNonZero hasNonZero_tail_of_zero_first NonEmptyList
  normalizeList normalizeList_eq_zero_of_allZero hasNonZero_normalizeList
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
  subtractAlignedLists_borrow_false_of_lessThan
  subtractAlignedLists_specification
  successor_carry_accumulator successorList_toCardinalNaturalPeano
  normalizeList_cons_zero
  toCardinalNaturalPeano_append
  toCardinalNaturalPeano_ne_zero_of_acc_ne_zero
  toCardinalNaturalPeano_ge_tenPower_of_ne_zero
  toCardinalNaturalPeano_zero_of_allZero toCardinalNaturalPeano_normalizeList
  allZero_or_hasNonZero not_allZero_of_hasNonZero
  toCardinalNaturalPeano_ne_zero_of_hasNonZero
  toCardinalNaturalPeano_ne_zero_of_not_allZero
  hasNonZero_of_toCardinalNaturalPeano_ne_zero
  predecessorList_successorList
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
  isLessThanLists subtractLists
  isLessThanLists_iff_toCardinalNaturalPeano_lt isLessThanLists_eq_false_iff_not_lt
  subtractLists_specification
  findQuotientDigitAuxiliary findQuotientDigit
  findQuotientDigitAuxiliary_specification findQuotientDigit_specification findQuotientDigit_nextRemainder_lt
  appendRootDigit appendRootDigit_toCardinalNaturalPeano
  firstRootGroupSize firstRootGroupSize_ne_zero firstRootGroupSize_le firstRootGroupSize_mod
  findRootDigitAuxiliary findRootDigit rootWithRemainderAuxiliary
  divideWithRemainderAuxiliary
  divideWithRemainderAuxiliary_newQuotient_value divideWithRemainderAuxiliary_step_algebra
  divideWithRemainderAuxiliary_specification
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

def zero : Decimal :=
  ⟨none, ⟨Sequences.List.firstElement zeroDigit Sequences.List.empty, by simp⟩⟩

def one : Decimal :=
  ⟨none, ⟨Sequences.List.firstElement oneDigit Sequences.List.empty, by simp⟩⟩

def minusOne : Decimal :=
  ⟨some Sign.minus, ⟨Sequences.List.firstElement oneDigit Sequences.List.empty, by simp⟩⟩

/-- A decimal is normalized when it has no extra leading zeros, and non-negative values
carry no sign (`none` rather than `some Sign.plus`, and not `-0`). -/
def isNormalized (d : Decimal) : Bool :=
  match d.sign with
  | some Sign.plus => false
  | none => isNormalizedList d.digits.val
  | some Sign.minus => isNormalizedNonZeroList d.digits.val

example : isNormalized ⟨some Sign.plus, ⟨Sequences.List.firstElement oneDigit Sequences.List.empty, by simp⟩⟩ = false := rfl
example : isNormalized ⟨none, ⟨Sequences.List.firstElement oneDigit Sequences.List.empty, by simp⟩⟩ = true := rfl
example : isNormalized ⟨some Sign.minus, ⟨Sequences.List.firstElement oneDigit Sequences.List.empty, by simp⟩⟩ = true := rfl
example : isNormalized ⟨none, ⟨Sequences.List.firstElement zeroDigit (Sequences.List.firstElement oneDigit Sequences.List.empty), by simp⟩⟩ = false := rfl
example : isNormalized ⟨some Sign.minus, ⟨Sequences.List.firstElement zeroDigit Sequences.List.empty, by simp⟩⟩ = false := rfl
example : isNormalized ⟨none, ⟨Sequences.List.firstElement zeroDigit Sequences.List.empty, by simp⟩⟩ = true := rfl


/-- Strip leading zeros and canonicalize sign: `some Sign.plus` becomes `none`, and
any zero magnitude (including `-0`) becomes `zero`. -/
def normalize (a : Decimal) : Decimal :=
  if AllZero (normalizeList a.digits.val a.digits.property).val then
    zero
  else
    match a.sign with
    | some Sign.plus | none =>
        ⟨none, normalizeList a.digits.val a.digits.property⟩
    | some Sign.minus =>
        ⟨some Sign.minus, normalizeList a.digits.val a.digits.property⟩

example : normalize ⟨some Sign.plus, ⟨Sequences.List.firstElement zeroDigit Sequences.List.empty, by simp⟩⟩ = zero := rfl
example : normalize ⟨some Sign.minus, ⟨Sequences.List.firstElement zeroDigit Sequences.List.empty, by simp⟩⟩ = zero := rfl
example : normalize ⟨none, ⟨Sequences.List.firstElement zeroDigit Sequences.List.empty, by simp⟩⟩ = zero := rfl


/-- Absolute magnitude of a decimal integer as a cardinal Peano natural. -/
def absoluteCardinalPeano (a : Decimal) : CardinalNatural.Peano :=
  Digits.toCardinalNaturalPeano a.digits.val CardinalNatural.Peano.zero

/-- Convert a decimal integer to its Peano representation. -/
def toPeano (a : Decimal) : Peano :=
  let magnitude := Peano.fromCardinalNatural (absoluteCardinalPeano a)
  match a.sign with
  | some Sign.minus => Peano.negate magnitude
  | _ => magnitude

/-- Negate a decimal integer by flipping its sign. Zero magnitude (including `-0`)
maps to unsigned `zero`; otherwise non-negative values become negative and
negatives become unsigned (`none`). -/
def negate (a : Decimal) : Decimal :=
  if AllZero a.digits.val then
    zero
  else
    match a.sign with
    | some Sign.minus => ⟨none, a.digits⟩
    | _ => ⟨some Sign.minus, a.digits⟩

example : (negate zero).normalize = zero.normalize := rfl

instance : Neg Decimal where
  neg := negate

/-- Absolute value of a decimal integer: drop the sign, keeping the same digits. -/
def absoluteValue (a : Decimal) : Decimal :=
  ⟨none, a.digits⟩

example : absoluteValue one = one := rfl
example : absoluteValue minusOne = one := rfl
example : absoluteValue zero = zero := rfl

/-- Integer successor: increment non-negative magnitudes; for negatives, decrement the magnitude
(turning `-1` into `0`, and `-0` into `1`). -/
def successor (a : Decimal) : Decimal :=
  match a.sign with
  | some Sign.minus =>
    match h : predecessorList a.digits.val with
    | ⟨_, true⟩ =>
      one
    | ⟨digits, false⟩ =>
      if AllZero digits then
        zero
      else
        ⟨some Sign.minus, ⟨digits, predecessorList_ne_empty_of_borrow_false a.digits.property h⟩⟩
  | sign =>
    match h : successorList a.digits.val with
    | ⟨digits, true⟩ =>
      ⟨sign, ⟨Sequences.List.firstElement oneDigit digits, by simp⟩⟩
    | ⟨digits, false⟩ =>
      ⟨sign, ⟨digits, successorList_ne_empty_of_carry_false a.digits.property h⟩⟩

def two : Decimal := successor one

/-- Integer predecessor: decrement non-negative magnitudes; for negatives, increment the magnitude
    (turning `1` into `0`, and `0` into `-1`). -/
def predecessor (a : Decimal) : Decimal :=
  match a.sign with
  | some Sign.minus =>
    match h : successorList a.digits.val with
    | ⟨digits, true⟩ =>
      ⟨some Sign.minus, ⟨Sequences.List.firstElement oneDigit digits, by simp⟩⟩
    | ⟨digits, false⟩ =>
      ⟨some Sign.minus, ⟨digits, successorList_ne_empty_of_carry_false a.digits.property h⟩⟩
  | sign =>
    match h : predecessorList a.digits.val with
    | ⟨_, true⟩ =>
      minusOne
    | ⟨digits, false⟩ =>
      if AllZero digits then
        zero
      else
        ⟨sign, ⟨digits, predecessorList_ne_empty_of_borrow_false a.digits.property h⟩⟩

@[simp]
theorem toPeano_one : toPeano one = Peano.one := by
  rfl

@[simp]
theorem toPeano_zero : toPeano zero = Peano.zero := by
  rfl

@[simp]
theorem negate_toPeano (x : Decimal) : (-x).toPeano = -(x.toPeano) := by
  simp only [Neg.neg]
  unfold Decimal.negate
  split
  · next h_all =>
    have habs : absoluteCardinalPeano x = CardinalNatural.Peano.zero := by
      simpa [absoluteCardinalPeano] using toCardinalNaturalPeano_zero_of_allZero h_all
    have hx : toPeano x = Peano.zero := by
      unfold toPeano
      rw [habs]
      cases x.sign with
      | none => rfl
      | some s => cases s <;> rfl
    rw [toPeano_zero, hx]
    rfl
  · next _h_not =>
    cases hsign : x.sign with
    | none =>
        simp only [toPeano, absoluteCardinalPeano, hsign]
    | some s =>
        cases s with
        | plus =>
            simp only [toPeano, absoluteCardinalPeano, hsign]
        | minus =>
            simp only [toPeano, absoluteCardinalPeano, hsign]
            exact (Peano.negate_negate _).symm

@[simp]
theorem negate_zero : (-zero : Decimal) = zero := by
  simp only [Neg.neg]
  unfold Decimal.negate
  have h : AllZero zero.digits.val := by
    simp [zero, AllZero, zeroDigit]
  simp only [h, ↓reduceIte]

theorem negate_of_not_allZero_none (x : Decimal) (h : ¬ AllZero x.digits.val)
    (hsign : x.sign = none) :
    (-x) = ⟨some Sign.minus, x.digits⟩ := by
  simp only [Neg.neg]
  unfold Decimal.negate
  simp only [h, ↓reduceIte, hsign]

theorem negate_of_not_allZero_plus (x : Decimal) (h : ¬ AllZero x.digits.val)
    (hsign : x.sign = some Sign.plus) :
    (-x) = ⟨some Sign.minus, x.digits⟩ := by
  simp only [Neg.neg]
  unfold Decimal.negate
  simp only [h, ↓reduceIte, hsign]

theorem negate_of_not_allZero_minus (x : Decimal) (h : ¬ AllZero x.digits.val)
    (hsign : x.sign = some Sign.minus) :
    (-x) = ⟨none, x.digits⟩ := by
  simp only [Neg.neg]
  unfold Decimal.negate
  simp only [h, ↓reduceIte, hsign]

theorem negate_minus_digits (digits : { l : Sequences.List Digit // l ≠ Sequences.List.empty })
    (h : ¬ AllZero digits.val) :
    (-⟨some Sign.minus, digits⟩ : Decimal) = ⟨none, digits⟩ := by
  simp only [Neg.neg]
  unfold Decimal.negate
  simp only [h, ↓reduceIte]

theorem negate_none_digits (digits : { l : Sequences.List Digit // l ≠ Sequences.List.empty })
    (h : ¬ AllZero digits.val) :
    (-⟨none, digits⟩ : Decimal) = ⟨some Sign.minus, digits⟩ := by
  simp only [Neg.neg]
  unfold Decimal.negate
  simp only [h, ↓reduceIte]

theorem toPeano_signed_normalizeList (sign : Option Sign) (a : Sequences.List Digit)
    (ha : a ≠ Sequences.List.empty) :
    toPeano (match sign with
      | some Sign.plus | none => ⟨none, normalizeList a ha⟩
      | some Sign.minus => ⟨some Sign.minus, normalizeList a ha⟩) =
      match sign with
      | some Sign.minus =>
          Peano.negate (Peano.fromCardinalNatural
            (Digits.toCardinalNaturalPeano a CardinalNatural.Peano.zero))
      | _ =>
          Peano.fromCardinalNatural
            (Digits.toCardinalNaturalPeano a CardinalNatural.Peano.zero) := by
  cases sign with
  | none =>
      exact toCardinalNaturalPeano_normalizeList a ha ▸ rfl
  | some s =>
      cases s with
      | plus =>
          exact toCardinalNaturalPeano_normalizeList a ha ▸ rfl
      | minus =>
          exact toCardinalNaturalPeano_normalizeList a ha ▸ rfl

@[simp]
theorem normalize_toPeano (x : Decimal) : x.normalize.toPeano = x.toPeano := by
  unfold normalize
  split
  · next hzero =>
      have hmag := toCardinalNaturalPeano_zero_of_allZero hzero
      rw [toCardinalNaturalPeano_normalizeList] at hmag
      rw [toPeano_zero]
      unfold toPeano absoluteCardinalPeano
      rw [hmag]
      cases x.sign with
      | none => rfl
      | some s =>
          cases s with
          | plus => rfl
          | minus => rfl
  · next _hzero =>
      rw [toPeano_signed_normalizeList]
      unfold toPeano absoluteCardinalPeano
      cases x.sign with
      | none => rfl
      | some s =>
          cases s with
          | plus => rfl
          | minus => rfl

theorem signed_digits_isNormalized (sign : Option Sign) (digits : NonEmptyList)
    (hnorm : isNormalized ⟨none, digits⟩ = true) (hzero : ¬ AllZero digits.val) :
    (match sign with
      | some Sign.plus | none => ⟨none, digits⟩
      | some Sign.minus => ⟨some Sign.minus, digits⟩ : Decimal).isNormalized = true := by
  cases sign with
  | none => exact hnorm
  | some s =>
      cases s with
      | plus => exact hnorm
      | minus =>
          match digits with
          | ⟨Sequences.List.empty, hl⟩ => exact False.elim (hl rfl)
          | ⟨Sequences.List.firstElement d Sequences.List.empty, _⟩ =>
              have hd : d.val ≠ CardinalNatural.Peano.zero := by
                intro hd0
                exact hzero ⟨hd0, trivial⟩
              simp [isNormalized, isNormalizedNonZeroList, hd]
          | ⟨Sequences.List.firstElement d (Sequences.List.firstElement d' ds'), _⟩ =>
              have hd : ¬ d.val = CardinalNatural.Peano.zero := by
                have h' : isNormalizedList
                    (Sequences.List.firstElement d (Sequences.List.firstElement d' ds')) = true := by
                  simpa [isNormalized] using hnorm
                simpa [isNormalizedList, decide_eq_true_eq] using h'
              simp [isNormalized, isNormalizedNonZeroList, hd]

theorem normalizeList_isNormalized_digits (a : Sequences.List Digit)
    (ha : a ≠ Sequences.List.empty) :
    isNormalized ⟨none, normalizeList a ha⟩ = true := by
  change isNormalizedList (normalizeList a ha).val = true
  exact Digits.normalizeList_isNormalized a ha

@[simp]
theorem normalize_isNormalized (d : Decimal) : d.normalize.isNormalized = true := by
  unfold normalize
  split
  · rfl
  · next hzero =>
      exact signed_digits_isNormalized d.sign (normalizeList d.digits.val d.digits.property)
        (normalizeList_isNormalized_digits d.digits.val d.digits.property) hzero

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

example : Equivalent ⟨some Sign.minus, ⟨Sequences.List.firstElement zeroDigit Sequences.List.empty, by simp⟩⟩ zero := rfl
example : Equivalent ⟨some Sign.plus, ⟨Sequences.List.firstElement zeroDigit Sequences.List.empty, by simp⟩⟩ zero := rfl
example : Equivalent ⟨none, ⟨Sequences.List.firstElement zeroDigit (Sequences.List.firstElement zeroDigit Sequences.List.empty), by simp⟩⟩ zero := rfl
example : Equivalent ⟨some Sign.plus, ⟨Sequences.List.firstElement oneDigit Sequences.List.empty, by simp⟩⟩ ⟨none, ⟨Sequences.List.firstElement oneDigit Sequences.List.empty, by simp⟩⟩ := rfl

/-- Strict order on decimal integers, via their Peano representation. -/
def LessThan (x y : Decimal) : Prop :=
  x.toPeano < y.toPeano

instance : LT Decimal where
  lt := LessThan


/-- Whether a decimal represents a strictly negative value (minus sign, non-zero digits). -/
def isNegative (d : Decimal) : Bool :=
  match d.sign with
  | some Sign.minus =>
      if AllZero d.digits.val then false else true
  | _ => false

example : isNegative zero = false := rfl
example : isNegative one = false := rfl
example : isNegative minusOne = true := rfl

/-- Absolute magnitude comparison via left-padded digit-wise order. -/
def isMagnitudeLessThan (x y : Decimal) : Bool :=
  let pair := Sequences.List.padAtStartToSameLength x.digits.val y.digits.val zeroDigit
  isLessThanAlignedLists pair.1 pair.2
    (Sequences.List.padAtStartToSameLength_sameLength x.digits.val y.digits.val zeroDigit)

/-- Strict order on decimal integers via sign and digit-wise magnitude comparison. -/
def isLessThan (x y : Decimal) : Bool :=
  match isNegative x, isNegative y with
  | true, true => isMagnitudeLessThan y x
  | true, false => true
  | false, true => false
  | false, false => isMagnitudeLessThan x y

example : isLessThan minusOne one = true := rfl
example : isLessThan one minusOne = false := rfl

theorem absoluteCardinalPeano_lt_of_lessThanAlignedLists_padded {a b : Decimal}
    (h : LessThanAlignedLists
      (Sequences.List.padAtStartToSameLength a.digits.val b.digits.val zeroDigit).1
      (Sequences.List.padAtStartToSameLength a.digits.val b.digits.val zeroDigit).2
      (Sequences.List.padAtStartToSameLength_sameLength a.digits.val b.digits.val
        zeroDigit)) :
    absoluteCardinalPeano a < absoluteCardinalPeano b :=
  toCardinalNaturalPeano_lt_of_lessThanAlignedLists_padded a.digits.val b.digits.val h

theorem lessThanAlignedLists_padded_of_absoluteCardinalPeano_lt {a b : Decimal}
    (h : absoluteCardinalPeano a < absoluteCardinalPeano b) :
    LessThanAlignedLists
      (Sequences.List.padAtStartToSameLength a.digits.val b.digits.val zeroDigit).1
      (Sequences.List.padAtStartToSameLength a.digits.val b.digits.val zeroDigit).2
      (Sequences.List.padAtStartToSameLength_sameLength a.digits.val b.digits.val
        zeroDigit) :=
  lessThanAlignedLists_padded_of_toCardinalNaturalPeano_lt a.digits.val b.digits.val h

theorem isMagnitudeLessThan_iff_absolute_lt (x y : Decimal) :
    isMagnitudeLessThan x y ↔ absoluteCardinalPeano x < absoluteCardinalPeano y := by
  unfold isMagnitudeLessThan
  dsimp only
  constructor
  · intro h
    have h_aligned := (isLessThanAlignedLists_iff_lessThanAlignedLists _ _ _).mp h
    exact absoluteCardinalPeano_lt_of_lessThanAlignedLists_padded h_aligned
  · intro h
    exact (isLessThanAlignedLists_iff_lessThanAlignedLists _ _ _).mpr
      (lessThanAlignedLists_padded_of_absoluteCardinalPeano_lt h)

theorem absoluteCardinalPeano_ne_zero_of_not_allZero {a : Decimal}
    (h : ¬ AllZero a.digits.val) :
    absoluteCardinalPeano a ≠ CardinalNatural.Peano.zero := by
  simpa [absoluteCardinalPeano] using toCardinalNaturalPeano_ne_zero_of_not_allZero h

theorem toPeano_eq_fromCardinal_of_not_isNegative (x : Decimal)
    (h : isNegative x = false) :
    x.toPeano = Peano.fromCardinalNatural (absoluteCardinalPeano x) := by
  unfold isNegative at h
  cases hsign : x.sign with
  | none =>
      unfold toPeano
      rw [hsign]
  | some s =>
      cases s with
      | plus =>
          unfold toPeano
          rw [hsign]
      | minus =>
          simp only [hsign] at h
          split at h
          · next h_all =>
              have habs : absoluteCardinalPeano x = CardinalNatural.Peano.zero := by
                simpa [absoluteCardinalPeano] using toCardinalNaturalPeano_zero_of_allZero h_all
              unfold toPeano
              rw [hsign, habs]
              rfl
          · cases h

theorem toPeano_eq_negate_fromCardinal_of_isNegative (x : Decimal)
    (h : isNegative x = true) :
    x.toPeano = -(Peano.fromCardinalNatural (absoluteCardinalPeano x)) ∧
      absoluteCardinalPeano x ≠ CardinalNatural.Peano.zero := by
  unfold isNegative at h
  cases hsign : x.sign with
  | none => simp [hsign] at h
  | some s =>
      cases s with
      | plus => simp [hsign] at h
      | minus =>
          simp only [hsign] at h
          split at h
          · cases h
          · next h_not_all =>
              constructor
              · unfold toPeano
                rw [hsign]
                rfl
              · exact absoluteCardinalPeano_ne_zero_of_not_allZero h_not_all

theorem toPeano_lt_of_isNegative_not_isNegative {x y : Decimal}
    (hx : isNegative x = true) (hy : isNegative y = false) :
    x.toPeano < y.toPeano := by
  have ⟨hx_eq, hx_ne⟩ := toPeano_eq_negate_fromCardinal_of_isNegative x hx
  have hy_eq := toPeano_eq_fromCardinal_of_not_isNegative y hy
  rw [hx_eq, hy_eq]
  cases hxa : absoluteCardinalPeano x with
  | zero => exact False.elim (hx_ne hxa)
  | successor n =>
      cases absoluteCardinalPeano y with
      | zero =>
          simp only [Peano.fromCardinalNatural, Neg.neg, Peano.negate]
          exact Peano.LessThan.negative_less_than_zero
      | successor m =>
          simp only [Peano.fromCardinalNatural, Neg.neg, Peano.negate]
          exact Peano.LessThan.negative_less_than_positive

theorem not_toPeano_lt_of_not_isNegative_isNegative {x y : Decimal}
    (hx : isNegative x = false) (hy : isNegative y = true) :
    ¬ x.toPeano < y.toPeano :=
  Peano.not_lt_of_lt (toPeano_lt_of_isNegative_not_isNegative hy hx)

theorem isLessThan_iff_lessThan (x y : Decimal) :
    isLessThan x y ↔ LessThan x y := by
  unfold isLessThan LessThan
  cases hx : isNegative x with
  | true =>
      cases hy : isNegative y with
      | true =>
          dsimp only
          have ⟨hx_eq, hx_ne⟩ := toPeano_eq_negate_fromCardinal_of_isNegative x hx
          have ⟨hy_eq, hy_ne⟩ := toPeano_eq_negate_fromCardinal_of_isNegative y hy
          rw [hx_eq, hy_eq]
          constructor
          · intro h
            have habs : absoluteCardinalPeano y < absoluteCardinalPeano x :=
              (isMagnitudeLessThan_iff_absolute_lt y x).mp h
            exact (Peano.negate_fromCardinalNatural_lt_iff hx_ne hy_ne).mpr habs
          · intro h
            have habs : absoluteCardinalPeano y < absoluteCardinalPeano x :=
              (Peano.negate_fromCardinalNatural_lt_iff hx_ne hy_ne).mp h
            exact (isMagnitudeLessThan_iff_absolute_lt y x).mpr habs
      | false =>
          dsimp only
          constructor
          · intro _
            exact toPeano_lt_of_isNegative_not_isNegative hx hy
          · intro _
            rfl
  | false =>
      cases hy : isNegative y with
      | true =>
          dsimp only
          constructor
          · intro h
            cases h
          · intro h
            exact False.elim (not_toPeano_lt_of_not_isNegative_isNegative hx hy h)
      | false =>
          dsimp only
          have hx_eq := toPeano_eq_fromCardinal_of_not_isNegative x hx
          have hy_eq := toPeano_eq_fromCardinal_of_not_isNegative y hy
          rw [hx_eq, hy_eq]
          constructor
          · intro h
            exact (Peano.fromCardinalNatural_lt_iff _ _).mpr
              ((isMagnitudeLessThan_iff_absolute_lt x y).mp h)
          · intro h
            exact (isMagnitudeLessThan_iff_absolute_lt x y).mpr
              ((Peano.fromCardinalNatural_lt_iff _ _).mp h)

instance (x y : Decimal) : Decidable (x < y) :=
  if h : isLessThan x y then
    isTrue (isLessThan_iff_lessThan x y |>.mp h)
  else
    isFalse (fun h''' => h (isLessThan_iff_lessThan x y |>.mpr h'''))

example : minusOne < zero := by decide
example : minusOne < one := by decide
example : zero < one := by decide
example : one < two := by decide

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

theorem lt_trans {x y z : Decimal} (h1 : x < y) (h2 : y < z) : x < z :=
  Peano.lt_trans h1 h2
theorem toPeano_absoluteValue_fromCardinal (x : Decimal) :
    x.toPeano.absoluteValue = Peano.fromCardinalNatural (absoluteCardinalPeano x) := by
  unfold toPeano
  cases x.sign with
  | none =>
      cases absoluteCardinalPeano x with
      | zero => rfl
      | successor _ => rfl
  | some s =>
      cases s with
      | plus =>
          cases absoluteCardinalPeano x with
          | zero => rfl
          | successor _ => rfl
      | minus =>
          cases absoluteCardinalPeano x with
          | zero => rfl
          | successor _ => rfl

theorem absoluteCardinalPeano_eq_of_toPeano_eq {a b : Decimal}
    (h : a.toPeano = b.toPeano) : absoluteCardinalPeano a = absoluteCardinalPeano b := by
  apply Peano.fromCardinalNatural_injective
  rw [← toPeano_absoluteValue_fromCardinal a, ← toPeano_absoluteValue_fromCardinal b, h]

/-- The cardinal magnitude of a positive integer is `fromOrdinal` of that
positive ordinal. -/
theorem absoluteCardinalPeano_eq_fromOrdinal_of_toPeano_positive (x : Decimal)
    (d : OrdinalNatural.Peano) (h : x.toPeano = Peano.positive d) :
    absoluteCardinalPeano x = CardinalNatural.Peano.fromOrdinal d := by
  apply Peano.fromCardinalNatural_injective
  have habs :
      x.toPeano.absoluteValue =
        Peano.fromCardinalNatural (absoluteCardinalPeano x) :=
    toPeano_absoluteValue_fromCardinal x
  rw [h] at habs
  change Peano.positive d = Peano.fromCardinalNatural (absoluteCardinalPeano x) at habs
  rw [← habs]
  have hle : (Peano.zero : Peano) ≤ Peano.positive d :=
    Or.inl Peano.LessThan.zero_less_than_positive
  exact (Peano.fromCardinalNatural_toCardinalNatural (Peano.positive d) hle).symm

/-- The cardinal magnitude of a negative integer is `fromOrdinal` of that
negative ordinal. -/
theorem absoluteCardinalPeano_eq_fromOrdinal_of_toPeano_negative (x : Decimal)
    (d : OrdinalNatural.Peano) (h : x.toPeano = Peano.negative d) :
    absoluteCardinalPeano x = CardinalNatural.Peano.fromOrdinal d := by
  apply Peano.fromCardinalNatural_injective
  have habs :
      x.toPeano.absoluteValue =
        Peano.fromCardinalNatural (absoluteCardinalPeano x) :=
    toPeano_absoluteValue_fromCardinal x
  rw [h] at habs
  change Peano.positive d = Peano.fromCardinalNatural (absoluteCardinalPeano x) at habs
  rw [← habs]
  have hle : (Peano.zero : Peano) ≤ Peano.positive d :=
    Or.inl Peano.LessThan.zero_less_than_positive
  exact (Peano.fromCardinalNatural_toCardinalNatural (Peano.positive d) hle).symm

theorem absoluteCardinalPeano_ne_zero_of_normalized_minus (d : Decimal)
    (hsign : d.sign = some Sign.minus) (hnorm : d.isNormalized = true) :
    absoluteCardinalPeano d ≠ CardinalNatural.Peano.zero := by
  cases d with
  | mk sign digits =>
      cases hsign
      cases digits with
      | mk val hprop =>
          cases val with
          | empty => exact False.elim (hprop rfl)
          | firstElement digit rest =>
              simp only [isNormalized, isNormalizedNonZeroList] at hnorm
              have hne : digit.val ≠ CardinalNatural.Peano.zero :=
                of_decide_eq_true hnorm
              exact absoluteCardinalPeano_ne_zero_of_not_allZero (fun h => hne h.1)

theorem toPeano_ne_negative_of_sign_none (x : Decimal) (h : x.sign = none)
    (n : OrdinalNatural.Peano) : x.toPeano ≠ Peano.negative n := by
  unfold toPeano
  rw [h]
  cases absoluteCardinalPeano x with
  | zero => intro h'; cases h'
  | successor _ => intro h'; cases h'

theorem toPeano_eq_negative_of_normalized_minus (x : Decimal)
    (hsign : x.sign = some Sign.minus) (hnorm : x.isNormalized = true) :
    ∃ n, x.toPeano = Peano.negative n := by
  have hne := absoluteCardinalPeano_ne_zero_of_normalized_minus x hsign hnorm
  cases h : absoluteCardinalPeano x with
  | zero => exact False.elim (hne h)
  | successor m =>
      refine ⟨CardinalNatural.Peano.toOrdinal (CardinalNatural.Peano.successor m)
        (CardinalNatural.Peano.successor_ne_zero m), ?_⟩
      unfold toPeano
      rw [hsign, h]
      rfl

theorem eq_zero_of_normalized_absoluteCardinalPeano_zero {d : Decimal}
    (hd : d.isNormalized = true)
    (h : absoluteCardinalPeano d = CardinalNatural.Peano.zero) : d = zero := by
  cases d with
  | mk sign digits =>
      cases sign with
      | none =>
          cases digits with
          | mk val hprop =>
              have hlist :
                  val = Sequences.List.firstElement zeroDigit Sequences.List.empty := by
                simpa [absoluteCardinalPeano, isNormalized] using
                  eq_zeroDigit_singleton_of_isNormalizedList_toCardinalNaturalPeano_zero
                    hprop hd h
              subst hlist
              rfl
      | some s =>
          cases s with
          | plus =>
              simp only [isNormalized] at hd
              cases hd
          | minus =>
              exact False.elim
                (absoluteCardinalPeano_ne_zero_of_normalized_minus
                  ⟨some Sign.minus, digits⟩ rfl hd h)

theorem leadingDigit_ne_zero_of_normalized_ne_zero_absolute
    {sign : Option Sign} {digit : Digit} {rest : Sequences.List Digit}
    {hprop : Sequences.List.firstElement digit rest ≠ Sequences.List.empty}
    (hnorm : isNormalized ⟨sign, ⟨Sequences.List.firstElement digit rest, hprop⟩⟩ = true)
    (hne_abs :
      absoluteCardinalPeano ⟨sign, ⟨Sequences.List.firstElement digit rest, hprop⟩⟩ ≠
        CardinalNatural.Peano.zero) :
    digit.val ≠ CardinalNatural.Peano.zero := by
  cases sign with
  | none =>
      exact leadingDigit_ne_zero_of_isNormalizedList_ne_zero
        (by simpa [isNormalized] using hnorm)
        (by simpa [absoluteCardinalPeano] using hne_abs)
  | some s =>
      cases s with
      | plus =>
          simp only [isNormalized] at hnorm
          cases hnorm
      | minus =>
          exact leadingDigit_ne_zero_of_isNormalizedNonZeroList
            (by simpa [isNormalized] using hnorm)

theorem digits_val_eq_of_normalized_absoluteCardinalPeano_eq
    {a b : Decimal}
    (ha : a.isNormalized = true) (hb : b.isNormalized = true)
    (heq : absoluteCardinalPeano a = absoluteCardinalPeano b)
    (ha0 : absoluteCardinalPeano a ≠ CardinalNatural.Peano.zero) :
    a.digits.val = b.digits.val := by
  cases a with
  | mk sa da =>
      cases b with
      | mk sb db =>
          cases da with
          | mk val_a prop_a =>
              cases db with
              | mk val_b prop_b =>
                  cases val_a with
                  | empty => exact absurd rfl prop_a
                  | firstElement da das =>
                      cases val_b with
                      | empty => exact absurd rfl prop_b
                      | firstElement db dbs =>
                          exact toCardinalNaturalPeano_injective_of_leading_ne_zero
                            (leadingDigit_ne_zero_of_normalized_ne_zero_absolute ha ha0)
                            (leadingDigit_ne_zero_of_normalized_ne_zero_absolute hb
                              (by intro h; exact ha0 (heq.trans h)))
                            (by simpa [absoluteCardinalPeano] using heq)

theorem sign_eq_of_normalized_toPeano_eq {a b : Decimal}
    (ha : a.isNormalized = true) (hb : b.isNormalized = true)
    (heq : a.toPeano = b.toPeano) : a.sign = b.sign := by
  cases hsa : a.sign with
  | none =>
      cases hsb : b.sign with
      | none => rfl
      | some sb =>
          cases sb with
          | plus =>
              unfold isNormalized at hb
              rw [hsb] at hb
              cases hb
          | minus =>
              obtain ⟨n, hn⟩ := toPeano_eq_negative_of_normalized_minus b hsb hb
              exact False.elim (toPeano_ne_negative_of_sign_none a hsa n (heq.trans hn))
  | some sa =>
      cases sa with
      | plus =>
          unfold isNormalized at ha
          rw [hsa] at ha
          cases ha
      | minus =>
          cases hsb : b.sign with
          | none =>
              obtain ⟨n, hn⟩ := toPeano_eq_negative_of_normalized_minus a hsa ha
              exact False.elim (toPeano_ne_negative_of_sign_none b hsb n (heq.symm.trans hn))
          | some sb =>
              cases sb with
              | plus =>
                  unfold isNormalized at hb
                  rw [hsb] at hb
                  cases hb
              | minus =>
                  rfl

theorem normalize_injective {a b : Decimal}
    (ha : a.isNormalized = true) (hb : b.isNormalized = true)
    (heq : a.toPeano = b.toPeano) : a = b := by
  have habs := absoluteCardinalPeano_eq_of_toPeano_eq heq
  have hsign := sign_eq_of_normalized_toPeano_eq ha hb heq
  by_cases ha0 : absoluteCardinalPeano a = CardinalNatural.Peano.zero
  · have hb0 : absoluteCardinalPeano b = CardinalNatural.Peano.zero :=
      habs.symm.trans ha0
    rw [eq_zero_of_normalized_absoluteCardinalPeano_zero ha ha0,
      eq_zero_of_normalized_absoluteCardinalPeano_zero hb hb0]
  · have hdigits_val :=
      digits_val_eq_of_normalized_absoluteCardinalPeano_eq ha hb habs ha0
    cases a with
    | mk sa da =>
        cases b with
        | mk sb db =>
            cases hsign
            exact congrArg (fun d => Decimal.mk sa d) (Subtype.ext hdigits_val)

theorem toPeano_eq_of_equivalent {a b : Decimal} (h : a ≈ b) :
    a.toPeano = b.toPeano := by
  have h_eq : a.normalize = b.normalize := h
  rw [← normalize_toPeano a, ← normalize_toPeano b, h_eq]

theorem equivalent_of_toPeano_eq {a b : Decimal} (h : a.toPeano = b.toPeano) :
    a ≈ b := by
  show a.normalize = b.normalize
  exact normalize_injective (normalize_isNormalized a) (normalize_isNormalized b)
    ((normalize_toPeano a).trans (h.trans (normalize_toPeano b).symm))

theorem not_lt_self (a : Decimal) : ¬ (a < a) := by
  intro h
  exact Peano.not_lt_self a.toPeano h

theorem not_equivalent_of_lt {a b : Decimal} (h : a < b) : ¬ (a ≈ b) := by
  intro heq
  have hlt : a.toPeano < b.toPeano := h
  rw [toPeano_eq_of_equivalent heq] at hlt
  exact Peano.not_lt_self b.toPeano hlt

theorem not_lt_of_lt {a b : Decimal} (h : a < b) : ¬ (b < a) := fun hba =>
  not_lt_self a (lt_trans h hba)

theorem trichotomy_or (a b : Decimal) : a < b ∨ a ≈ b ∨ b < a := by
  cases Peano.trichotomy_or a.toPeano b.toPeano with
  | inl h =>
      exact Or.inl h
  | inr h =>
      cases h with
      | inl heq =>
          exact Or.inr (Or.inl (equivalent_of_toPeano_eq heq))
      | inr hgt =>
          exact Or.inr (Or.inr hgt)

theorem trichotomy (a b : Decimal) :
    ZeroMath.Logic.Trichotomy (a < b) (a ≈ b) (b < a) := by
  cases trichotomy_or a b with
  | inl h =>
      exact ZeroMath.Logic.Trichotomy.first h (not_equivalent_of_lt h) (not_lt_of_lt h)
  | inr h =>
      cases h with
      | inl heq =>
          exact ZeroMath.Logic.Trichotomy.second heq
            (fun hlt => not_equivalent_of_lt hlt heq)
            (fun hlt => not_equivalent_of_lt hlt heq.symm)
      | inr hgt =>
          exact ZeroMath.Logic.Trichotomy.third hgt (not_lt_of_lt hgt)
            (fun heq => not_equivalent_of_lt hgt heq.symm)

theorem le_of_not_le {a b : Decimal} (h : ¬ a ≤ b) : b ≤ a := by
  cases trichotomy_or a b with
  | inl hlt => exact absurd (Or.inl hlt : a ≤ b) h
  | inr h' =>
    cases h' with
    | inl heq => exact absurd (Or.inr heq : a ≤ b) h
    | inr hlt => exact Or.inl hlt

theorem lt_of_not_lt_not_equivalent {a b : Decimal} (hnlt : ¬ a < b)
    (hne : ¬ a ≈ b) : b < a := by
  cases trichotomy_or a b with
  | inl hlt => exact absurd hlt hnlt
  | inr h' =>
    cases h' with
    | inl heq => exact absurd heq hne
    | inr hlt => exact hlt

theorem ne_of_not_le {a b : Decimal} (h : ¬ a ≤ b) : a ≠ b :=
  fun heq => by
    cases heq
    exact h (Or.inr (Setoid.refl _))

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

theorem le_trans {a b c : Decimal} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  cases h1 with
  | inl hlt1 =>
      cases h2 with
      | inl hlt2 => exact Or.inl (lt_trans hlt1 hlt2)
      | inr heq2 =>
          apply Or.inl
          change a.toPeano < c.toPeano
          rw [← toPeano_eq_of_equivalent heq2]
          exact hlt1
  | inr heq1 =>
      cases h2 with
      | inl hlt2 =>
          apply Or.inl
          change a.toPeano < c.toPeano
          rw [toPeano_eq_of_equivalent heq1]
          exact hlt2
      | inr heq2 =>
          exact Or.inr (Setoid.trans heq1 heq2)

/-- Decimal `≤` is reflected by the Peano embedding. -/
theorem toPeano_le_of_le {a b : Decimal} (h : a ≤ b) : a.toPeano ≤ b.toPeano := by
  cases h with
  | inl hlt => exact Or.inl hlt
  | inr heq => exact Or.inr (toPeano_eq_of_equivalent heq)

/-- Decimal `≤` reflects the Peano embedding. -/
theorem le_of_toPeano_le {a b : Decimal} (h : a.toPeano ≤ b.toPeano) : a ≤ b := by
  cases h with
  | inl hlt => exact Or.inl hlt
  | inr heq => exact Or.inr (equivalent_of_toPeano_eq heq)

/-- Decimal `≤` is equivalent to `≤` of Peano embeddings. -/
theorem le_iff_toPeano_le (a b : Decimal) : a ≤ b ↔ a.toPeano ≤ b.toPeano :=
  ⟨toPeano_le_of_le, le_of_toPeano_le⟩

theorem successor_toPeano_none (x : Decimal) (hsign : x.sign = none) :
    x.successor.toPeano = x.toPeano.successor := by
  have hx : toPeano x = Peano.fromCardinalNatural (absoluteCardinalPeano x) := by
    unfold toPeano; rw [hsign]
  unfold successor
  rw [hsign]
  split
  · next h => nomatch h
  · next sign _ =>
      split
      · next digits hsucc =>
          have h_list := toCardinalNaturalPeano_of_successorList x.digits.val
          rw [hsucc] at h_list
          dsimp only at h_list
          rw [hx]
          change Peano.fromCardinalNatural
              (Digits.toCardinalNaturalPeano
                (Sequences.List.firstElement
                  ⟨CardinalNatural.Peano.one, CardinalNatural.Peano.one_lt_ten⟩ digits)
                CardinalNatural.Peano.zero) =
            (Peano.fromCardinalNatural (absoluteCardinalPeano x)).successor
          have habs :
              Digits.toCardinalNaturalPeano
                  (Sequences.List.firstElement
                    ⟨CardinalNatural.Peano.one, CardinalNatural.Peano.one_lt_ten⟩ digits)
                  CardinalNatural.Peano.zero =
                (absoluteCardinalPeano x).successor := by
            simpa [absoluteCardinalPeano, Digits.toCardinalNaturalPeano,
              CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.zero_add] using h_list
          rw [habs, Peano.fromCardinalNatural_successor]
      · next digits hsucc =>
          have h_list := toCardinalNaturalPeano_of_successorList x.digits.val
          rw [hsucc] at h_list
          dsimp only at h_list
          rw [hx]
          change Peano.fromCardinalNatural
              (Digits.toCardinalNaturalPeano digits CardinalNatural.Peano.zero) =
            (Peano.fromCardinalNatural (absoluteCardinalPeano x)).successor
          have habs :
              Digits.toCardinalNaturalPeano digits CardinalNatural.Peano.zero =
                (absoluteCardinalPeano x).successor := by
            simpa [absoluteCardinalPeano] using h_list
          rw [habs, Peano.fromCardinalNatural_successor]

theorem successor_toPeano_plus (x : Decimal) (hsign : x.sign = some Sign.plus) :
    x.successor.toPeano = x.toPeano.successor := by
  have hx : toPeano x = Peano.fromCardinalNatural (absoluteCardinalPeano x) := by
    unfold toPeano; rw [hsign]
  unfold successor
  rw [hsign]
  split
  · next h => nomatch h
  · next sign _ =>
      split
      · next digits hsucc =>
          have h_list := toCardinalNaturalPeano_of_successorList x.digits.val
          rw [hsucc] at h_list
          dsimp only at h_list
          rw [hx]
          change Peano.fromCardinalNatural
              (Digits.toCardinalNaturalPeano
                (Sequences.List.firstElement
                  ⟨CardinalNatural.Peano.one, CardinalNatural.Peano.one_lt_ten⟩ digits)
                CardinalNatural.Peano.zero) =
            (Peano.fromCardinalNatural (absoluteCardinalPeano x)).successor
          have habs :
              Digits.toCardinalNaturalPeano
                  (Sequences.List.firstElement
                    ⟨CardinalNatural.Peano.one, CardinalNatural.Peano.one_lt_ten⟩ digits)
                  CardinalNatural.Peano.zero =
                (absoluteCardinalPeano x).successor := by
            simpa [absoluteCardinalPeano, Digits.toCardinalNaturalPeano,
              CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.zero_add] using h_list
          rw [habs, Peano.fromCardinalNatural_successor]
      · next digits hsucc =>
          have h_list := toCardinalNaturalPeano_of_successorList x.digits.val
          rw [hsucc] at h_list
          dsimp only at h_list
          rw [hx]
          change Peano.fromCardinalNatural
              (Digits.toCardinalNaturalPeano digits CardinalNatural.Peano.zero) =
            (Peano.fromCardinalNatural (absoluteCardinalPeano x)).successor
          have habs :
              Digits.toCardinalNaturalPeano digits CardinalNatural.Peano.zero =
                (absoluteCardinalPeano x).successor := by
            simpa [absoluteCardinalPeano] using h_list
          rw [habs, Peano.fromCardinalNatural_successor]

theorem successor_toPeano_minus (x : Decimal) (hsign : x.sign = some Sign.minus) :
    x.successor.toPeano = x.toPeano.successor := by
  have hx_toPeano :
      toPeano x = Peano.negate (Peano.fromCardinalNatural (absoluteCardinalPeano x)) := by
    unfold toPeano; rw [hsign]
  unfold successor
  rw [hsign]
  split
  · next h_eq =>
      -- h_eq proves some Sign.minus = some Sign.minus (trivial); body is predecessorList match
      split
      · next digits hpred =>
          have h_all : AllZero x.digits.val :=
            allZero_of_predecessorList_borrow_true hpred
          have habs : absoluteCardinalPeano x = CardinalNatural.Peano.zero := by
            simpa [absoluteCardinalPeano] using toCardinalNaturalPeano_zero_of_allZero h_all
          have hx_peano : toPeano x = Peano.zero := by
            rw [hx_toPeano, habs]; rfl
          rw [toPeano_one, hx_peano]; rfl
      · next digits hpred =>
          have h_succ_pred : successorList digits = ⟨x.digits.val, false⟩ := by
            have h := successorList_predecessorList x.digits.val
            simpa [hpred] using h
          have h_abs :
              absoluteCardinalPeano x =
                (Digits.toCardinalNaturalPeano digits CardinalNatural.Peano.zero).successor := by
            have hsucc :=
              successorList_toCardinalNaturalPeano digits CardinalNatural.Peano.zero
            rw [h_succ_pred] at hsucc
            dsimp only at hsucc
            simpa [absoluteCardinalPeano] using hsucc
          split
          · next h_zero =>
              have hdigits0 := toCardinalNaturalPeano_zero_of_allZero h_zero
              have habs : absoluteCardinalPeano x = CardinalNatural.Peano.one := by
                rw [h_abs, hdigits0]; rfl
              have hx_peano : toPeano x = Peano.minusOne := by
                rw [hx_toPeano, habs]; rfl
              rw [toPeano_zero, hx_peano]; rfl
          · next h_zero =>
              have h_left :
                  toPeano
                      ⟨some Sign.minus,
                        ⟨digits,
                          predecessorList_ne_empty_of_borrow_false x.digits.property hpred⟩⟩ =
                    Peano.negate
                      (Peano.fromCardinalNatural
                        (Digits.toCardinalNaturalPeano digits CardinalNatural.Peano.zero)) := by
                simp only [toPeano, absoluteCardinalPeano]
              have hx_peano :
                  toPeano x =
                    Peano.negate
                      (Peano.successor
                        (Peano.fromCardinalNatural
                          (Digits.toCardinalNaturalPeano digits CardinalNatural.Peano.zero))) := by
                rw [hx_toPeano, h_abs, Peano.fromCardinalNatural_successor]
              rw [h_left, hx_peano]
              symm
              exact
                (congrArg Peano.successor
                  (Peano.negate_successor
                    (Peano.fromCardinalNatural
                      (Digits.toCardinalNaturalPeano digits CardinalNatural.Peano.zero)))).trans
                  (Peano.successor_predecessor _)
  · next sign h_ne =>
      exact False.elim (h_ne rfl)

@[simp]
theorem successor_toPeano (x : Decimal) :
    x.successor.toPeano = x.toPeano.successor := by
  cases hsign : x.sign with
  | none => exact successor_toPeano_none x hsign
  | some s =>
      cases s with
      | plus => exact successor_toPeano_plus x hsign
      | minus => exact successor_toPeano_minus x hsign

@[simp]
theorem toPeano_two : toPeano two = Peano.two := by
  unfold two
  rw [successor_toPeano, toPeano_one]
  rfl

@[simp]
theorem toPeano_minusOne : toPeano minusOne = Peano.minusOne := by
  rfl

theorem predecessor_toPeano_none (x : Decimal) (hsign : x.sign = none) :
    x.predecessor.toPeano = x.toPeano.predecessor := by
  have hx : toPeano x = Peano.fromCardinalNatural (absoluteCardinalPeano x) := by
    unfold toPeano; rw [hsign]
  unfold predecessor
  rw [hsign]
  split
  · next h => nomatch h
  · next sign _ =>
      split
      · next digits hpred =>
          have h_all : AllZero x.digits.val :=
            allZero_of_predecessorList_borrow_true hpred
          have habs : absoluteCardinalPeano x = CardinalNatural.Peano.zero := by
            simpa [absoluteCardinalPeano] using toCardinalNaturalPeano_zero_of_allZero h_all
          have hx_peano : toPeano x = Peano.zero := by
            rw [hx, habs]; rfl
          rw [toPeano_minusOne, hx_peano]; rfl
      · next digits hpred =>
          have h_succ_pred : successorList digits = ⟨x.digits.val, false⟩ := by
            have h := successorList_predecessorList x.digits.val
            simpa [hpred] using h
          have h_abs :
              absoluteCardinalPeano x =
                (Digits.toCardinalNaturalPeano digits CardinalNatural.Peano.zero).successor := by
            have hsucc :=
              successorList_toCardinalNaturalPeano digits CardinalNatural.Peano.zero
            rw [h_succ_pred] at hsucc
            dsimp only at hsucc
            simpa [absoluteCardinalPeano] using hsucc
          split
          · next h_zero =>
              have hdigits0 := toCardinalNaturalPeano_zero_of_allZero h_zero
              have habs : absoluteCardinalPeano x = CardinalNatural.Peano.one := by
                rw [h_abs, hdigits0]; rfl
              have hx_peano : toPeano x = Peano.one := by
                rw [hx, habs]; rfl
              rw [toPeano_zero, hx_peano]; rfl
          · next h_zero =>
              rw [hx]
              change Peano.fromCardinalNatural
                  (Digits.toCardinalNaturalPeano digits CardinalNatural.Peano.zero) =
                (Peano.fromCardinalNatural (absoluteCardinalPeano x)).predecessor
              rw [h_abs, Peano.fromCardinalNatural_successor]
              exact (Peano.predecessor_successor _).symm

theorem predecessor_toPeano_plus (x : Decimal) (hsign : x.sign = some Sign.plus) :
    x.predecessor.toPeano = x.toPeano.predecessor := by
  have hx : toPeano x = Peano.fromCardinalNatural (absoluteCardinalPeano x) := by
    unfold toPeano; rw [hsign]
  unfold predecessor
  rw [hsign]
  split
  · next h => nomatch h
  · next sign _ =>
      split
      · next digits hpred =>
          have h_all : AllZero x.digits.val :=
            allZero_of_predecessorList_borrow_true hpred
          have habs : absoluteCardinalPeano x = CardinalNatural.Peano.zero := by
            simpa [absoluteCardinalPeano] using toCardinalNaturalPeano_zero_of_allZero h_all
          have hx_peano : toPeano x = Peano.zero := by
            rw [hx, habs]; rfl
          rw [toPeano_minusOne, hx_peano]; rfl
      · next digits hpred =>
          have h_succ_pred : successorList digits = ⟨x.digits.val, false⟩ := by
            have h := successorList_predecessorList x.digits.val
            simpa [hpred] using h
          have h_abs :
              absoluteCardinalPeano x =
                (Digits.toCardinalNaturalPeano digits CardinalNatural.Peano.zero).successor := by
            have hsucc :=
              successorList_toCardinalNaturalPeano digits CardinalNatural.Peano.zero
            rw [h_succ_pred] at hsucc
            dsimp only at hsucc
            simpa [absoluteCardinalPeano] using hsucc
          split
          · next h_zero =>
              have hdigits0 := toCardinalNaturalPeano_zero_of_allZero h_zero
              have habs : absoluteCardinalPeano x = CardinalNatural.Peano.one := by
                rw [h_abs, hdigits0]; rfl
              have hx_peano : toPeano x = Peano.one := by
                rw [hx, habs]; rfl
              rw [toPeano_zero, hx_peano]; rfl
          · next h_zero =>
              rw [hx]
              change Peano.fromCardinalNatural
                  (Digits.toCardinalNaturalPeano digits CardinalNatural.Peano.zero) =
                (Peano.fromCardinalNatural (absoluteCardinalPeano x)).predecessor
              rw [h_abs, Peano.fromCardinalNatural_successor]
              exact (Peano.predecessor_successor _).symm

theorem predecessor_toPeano_minus (x : Decimal) (hsign : x.sign = some Sign.minus) :
    x.predecessor.toPeano = x.toPeano.predecessor := by
  have hx_toPeano :
      toPeano x = Peano.negate (Peano.fromCardinalNatural (absoluteCardinalPeano x)) := by
    unfold toPeano; rw [hsign]
  unfold predecessor
  rw [hsign]
  split
  · next h_eq =>
      split
      · next digits hsucc =>
          have h_list := toCardinalNaturalPeano_of_successorList x.digits.val
          rw [hsucc] at h_list
          dsimp only at h_list
          rw [hx_toPeano]
          change Peano.negate
              (Peano.fromCardinalNatural
                (Digits.toCardinalNaturalPeano
                  (Sequences.List.firstElement
                    ⟨CardinalNatural.Peano.one, CardinalNatural.Peano.one_lt_ten⟩ digits)
                  CardinalNatural.Peano.zero)) =
            (Peano.negate (Peano.fromCardinalNatural (absoluteCardinalPeano x))).predecessor
          have habs :
              Digits.toCardinalNaturalPeano
                  (Sequences.List.firstElement
                    ⟨CardinalNatural.Peano.one, CardinalNatural.Peano.one_lt_ten⟩ digits)
                  CardinalNatural.Peano.zero =
                (absoluteCardinalPeano x).successor := by
            simpa [absoluteCardinalPeano, Digits.toCardinalNaturalPeano,
              CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.zero_add] using h_list
          rw [habs, Peano.fromCardinalNatural_successor]
          exact Peano.negate_successor _
      · next digits hsucc =>
          have h_list := toCardinalNaturalPeano_of_successorList x.digits.val
          rw [hsucc] at h_list
          dsimp only at h_list
          rw [hx_toPeano]
          change Peano.negate
              (Peano.fromCardinalNatural
                (Digits.toCardinalNaturalPeano digits CardinalNatural.Peano.zero)) =
            (Peano.negate (Peano.fromCardinalNatural (absoluteCardinalPeano x))).predecessor
          have habs :
              Digits.toCardinalNaturalPeano digits CardinalNatural.Peano.zero =
                (absoluteCardinalPeano x).successor := by
            simpa [absoluteCardinalPeano] using h_list
          rw [habs, Peano.fromCardinalNatural_successor]
          exact Peano.negate_successor _
  · next sign h_ne =>
      exact False.elim (h_ne rfl)

@[simp]
theorem predecessor_toPeano (x : Decimal) :
    x.predecessor.toPeano = x.toPeano.predecessor := by
  cases hsign : x.sign with
  | none => exact predecessor_toPeano_none x hsign
  | some s =>
      cases s with
      | plus => exact predecessor_toPeano_plus x hsign
      | minus => exact predecessor_toPeano_minus x hsign

theorem normalize_eq_zero_of_allZero (a : Decimal) (h : AllZero a.digits.val) :
    a.normalize = zero := by
  unfold normalize
  have hnorm := Digits.normalizeList_eq_zero_of_allZero a.digits.property h
  have hzero : AllZero (normalizeList a.digits.val a.digits.property).val := by
    simp [AllZero, zeroDigit, hnorm]
  simp [hzero]

@[simp]
theorem normalize_zero : zero.normalize = zero := rfl

@[simp]
theorem normalize_one : one.normalize = one := rfl

@[simp]
theorem normalize_minusOne : minusOne.normalize = minusOne := rfl

theorem negate_negate (x : Decimal) : -(-x) ≈ x := by
  change (-(-x)).normalize = x.normalize
  by_cases h : AllZero x.digits.val
  · have hx : (-x) = zero := by
      simp only [Neg.neg]
      unfold Decimal.negate
      simp only [h, ↓reduceIte]
    rw [hx, negate_zero, normalize_zero, normalize_eq_zero_of_allZero x h]
  · have hnz := not_allZero_normalizeList_of_not_allZero x.digits.property h
    cases hsign : x.sign with
    | none =>
        rw [negate_of_not_allZero_none x h hsign, negate_minus_digits x.digits h]
        simp [normalize, hnz, hsign]
    | some s =>
        cases s with
        | plus =>
            rw [negate_of_not_allZero_plus x h hsign, negate_minus_digits x.digits h]
            simp [normalize, hnz, hsign]
        | minus =>
            rw [negate_of_not_allZero_minus x h hsign, negate_none_digits x.digits h]
            simp [normalize, hnz, hsign]

theorem absoluteValue_negate (x : Decimal) : x.absoluteValue ≈ (-x).absoluteValue := by
  change x.absoluteValue.normalize = (-x).absoluteValue.normalize
  by_cases h : AllZero x.digits.val
  · have hx : (-x) = zero := by
      simp only [Neg.neg]
      unfold Decimal.negate
      simp only [h, ↓reduceIte]
    rw [hx]
    unfold absoluteValue
    rw [normalize_eq_zero_of_allZero (⟨none, x.digits⟩ : Decimal) h]
    exact normalize_zero
  · cases hsign : x.sign with
    | none =>
        rw [negate_of_not_allZero_none x h hsign]
        unfold absoluteValue
        rfl
    | some s =>
        cases s with
        | plus =>
            rw [negate_of_not_allZero_plus x h hsign]
            unfold absoluteValue
            rfl
        | minus =>
            rw [negate_of_not_allZero_minus x h hsign]
            unfold absoluteValue
            rfl

@[simp]
theorem absoluteValue_toPeano (x : Decimal) :
    x.absoluteValue.toPeano = x.toPeano.absoluteValue := by
  simp only [Decimal.absoluteValue]
  have hmag : ({ sign := none, digits := x.digits } : Decimal).toPeano =
      Peano.fromCardinalNatural (absoluteCardinalPeano x) := by
    unfold toPeano absoluteCardinalPeano
    rfl
  have hnonneg (n : CardinalNatural.Peano) :
      (Peano.fromCardinalNatural n).absoluteValue = Peano.fromCardinalNatural n := by
    cases n with
    | zero => rfl
    | successor _ => rfl
  rw [hmag]
  cases hsign : x.sign with
  | none =>
      have hx : x.toPeano = Peano.fromCardinalNatural (absoluteCardinalPeano x) := by
        unfold toPeano; rw [hsign]
      rw [hx, hnonneg]
  | some s =>
      cases s with
      | plus =>
          have hx : x.toPeano = Peano.fromCardinalNatural (absoluteCardinalPeano x) := by
            unfold toPeano; rw [hsign]
          rw [hx, hnonneg]
      | minus =>
          have hx : x.toPeano =
              Peano.negate (Peano.fromCardinalNatural (absoluteCardinalPeano x)) := by
            unfold toPeano; rw [hsign]
          rw [hx, ← Peano.absoluteValue_negate, hnonneg]

theorem predecessor_one : predecessor one = zero := by
  decide

theorem predecessor_zero : predecessor zero = minusOne := by
  decide

theorem predecessor_successor_none (a : Decimal) (hsign : a.sign = none) :
    predecessor (successor a) ≈ a := by
  change (predecessor (successor a)).normalize = a.normalize
  unfold successor
  rw [hsign]
  split
  · next h => nomatch h
  · next sign _ =>
      split
      · next digits hsucc =>
          have h_pred := predecessorList_of_successorList_carry hsucc
          have hnz := not_allZero_cons_zero_of_successorList_carry a.digits.property hsucc
          unfold predecessor
          split
          · next h => nomatch h
          · next sign' _ =>
              split
              · next digs hpred =>
                  rw [h_pred] at hpred
                  cases hpred
              · next digs hpred =>
                  rw [h_pred] at hpred
                  injection hpred with hdigs _
                  subst hdigs
                  simp only [hnz, ↓reduceIte]
                  have hnz0 :=
                    not_allZero_normalizeList_of_not_allZero (by simp) hnz
                  have hnz1 :=
                    not_allZero_normalizeList_of_not_allZero a.digits.property (by
                      intro hall; exact hnz ⟨rfl, hall⟩)
                  simp [normalize, hsign, hnz1,
                    normalizeList_cons_zero zeroDigit a.digits.val rfl a.digits.property]
      · next digits hsucc =>
          have h_pred : predecessorList digits = ⟨a.digits.val, false⟩ := by
            have h' := predecessorList_successorList a.digits.val
            simpa [hsucc] using h'
          unfold predecessor
          split
          · next h => nomatch h
          · next sign' _ =>
              split
              · next digs hpred =>
                  rw [h_pred] at hpred
                  cases hpred
              · next digs hpred =>
                  rw [h_pred] at hpred
                  injection hpred with hdigs _
                  subst hdigs
                  split
                  · next hzero =>
                      have hnorm := normalize_eq_zero_of_allZero a hzero
                      rw [normalize_zero, hnorm]
                  · next hzero =>
                      have hnz' :=
                        not_allZero_normalizeList_of_not_allZero a.digits.property hzero
                      simp [normalize, hsign, hnz']

theorem predecessor_successor_plus (a : Decimal) (hsign : a.sign = some Sign.plus) :
    predecessor (successor a) ≈ a := by
  change (predecessor (successor a)).normalize = a.normalize
  unfold successor
  rw [hsign]
  split
  · next h => nomatch h
  · next sign _ =>
      split
      · next digits hsucc =>
          have h_pred := predecessorList_of_successorList_carry hsucc
          have hnz := not_allZero_cons_zero_of_successorList_carry a.digits.property hsucc
          unfold predecessor
          split
          · next h => nomatch h
          · next sign' _ =>
              split
              · next digs hpred =>
                  rw [h_pred] at hpred
                  cases hpred
              · next digs hpred =>
                  rw [h_pred] at hpred
                  injection hpred with hdigs _
                  subst hdigs
                  simp only [hnz, ↓reduceIte]
                  have hnz0 :=
                    not_allZero_normalizeList_of_not_allZero (by simp) hnz
                  have hnz1 :=
                    not_allZero_normalizeList_of_not_allZero a.digits.property (by
                      intro hall; exact hnz ⟨rfl, hall⟩)
                  simp [normalize, hsign, hnz1,
                    normalizeList_cons_zero zeroDigit a.digits.val rfl a.digits.property]
      · next digits hsucc =>
          have h_pred : predecessorList digits = ⟨a.digits.val, false⟩ := by
            have h' := predecessorList_successorList a.digits.val
            simpa [hsucc] using h'
          unfold predecessor
          split
          · next h => nomatch h
          · next sign' _ =>
              split
              · next digs hpred =>
                  rw [h_pred] at hpred
                  cases hpred
              · next digs hpred =>
                  rw [h_pred] at hpred
                  injection hpred with hdigs _
                  subst hdigs
                  split
                  · next hzero =>
                      have hnorm := normalize_eq_zero_of_allZero a hzero
                      rw [normalize_zero, hnorm]
                  · next hzero =>
                      have hnz' :=
                        not_allZero_normalizeList_of_not_allZero a.digits.property hzero
                      simp [normalize, hsign, hnz']

theorem predecessor_successor_minus (a : Decimal) (hsign : a.sign = some Sign.minus) :
    predecessor (successor a) ≈ a := by
  change (predecessor (successor a)).normalize = a.normalize
  unfold successor
  rw [hsign]
  split
  · next _ =>
      split
      · -- borrow true → successor = one; a all-zero → normalize zero
        next digits hpred =>
          have hall := allZero_of_predecessorList_borrow_true hpred
          have hnorm := normalize_eq_zero_of_allZero a hall
          rw [predecessor_one, normalize_zero, hnorm]
      · next digits hpred =>
          have h_succ : successorList digits = ⟨a.digits.val, false⟩ := by
            have h := successorList_predecessorList a.digits.val
            simpa [hpred] using h
          split
          · -- AllZero digits → successor = zero → predecessor = minusOne
            next hzero =>
              rw [predecessor_zero, normalize_minusOne]
              have hnorm :=
                normalizeList_of_successorList_allZero h_succ hzero a.digits.property
              have hnz' : ¬ AllZero (normalizeList a.digits.val a.digits.property).val := by
                rw [hnorm]
                simp [AllZero, oneDigit]
                exact CardinalNatural.Peano.successor_ne_zero CardinalNatural.Peano.zero
              rw [normalize, if_neg hnz', hsign, hnorm]
              rfl
          · -- not AllZero digits → successor restores a (nonzero magnitude)
            next hdigits_nz =>
              unfold predecessor
              split
              · next _ =>
                  split
                  · next digs hsucc =>
                      rw [h_succ] at hsucc
                      cases hsucc
                  · next digs hsucc =>
                      rw [h_succ] at hsucc
                      injection hsucc with hdigs _
                      subst hdigs
                      have ha0 : ¬ AllZero a.digits.val := by
                        intro hall
                        have hmag := toCardinalNaturalPeano_of_successorList digits
                        rw [h_succ] at hmag
                        dsimp only at hmag
                        have hzero := toCardinalNaturalPeano_zero_of_allZero hall
                        rw [hzero] at hmag
                        exact (CardinalNatural.Peano.successor_ne_zero _).symm hmag
                      have hnz' :=
                        not_allZero_normalizeList_of_not_allZero a.digits.property ha0
                      simp [normalize, hsign, hnz']
              · next sign hne =>
                  exact False.elim (hne rfl)
  · next sign hne =>
      exact False.elim (hne rfl)

theorem predecessor_successor (a : Decimal) : predecessor (successor a) ≈ a := by
  cases hsign : a.sign with
  | none => exact predecessor_successor_none a hsign
  | some s =>
      cases s with
      | plus => exact predecessor_successor_plus a hsign
      | minus => exact predecessor_successor_minus a hsign

theorem successor_minusOne : successor minusOne = zero := by
  decide

theorem successor_zero : successor zero = one := by
  decide

theorem successor_predecessor_none (a : Decimal) (hsign : a.sign = none) :
    successor (predecessor a) ≈ a := by
  change (successor (predecessor a)).normalize = a.normalize
  unfold predecessor
  rw [hsign]
  split
  · next h => nomatch h
  · next sign _ =>
      split
      · -- borrow true: predecessor = minusOne; a all-zero
        next digits hpred =>
          have hall := allZero_of_predecessorList_borrow_true hpred
          have hnorm := normalize_eq_zero_of_allZero a hall
          rw [successor_minusOne, normalize_zero, hnorm]
      · next digits hpred =>
          have h_succ : successorList digits = ⟨a.digits.val, false⟩ := by
            have h := successorList_predecessorList a.digits.val
            simpa [hpred] using h
          split
          · -- AllZero digits: predecessor = zero; successor zero = one
            next hzero =>
              rw [successor_zero, normalize_one]
              have hnorm :=
                normalizeList_of_successorList_allZero h_succ hzero a.digits.property
              have hnz' : ¬ AllZero (normalizeList a.digits.val a.digits.property).val := by
                rw [hnorm]
                simp [AllZero, oneDigit]
                exact CardinalNatural.Peano.successor_ne_zero CardinalNatural.Peano.zero
              unfold normalize
              rw [if_neg hnz', hsign, hnorm]
              rfl
          · -- not AllZero: predecessor = ⟨none, digits⟩
            next hdigits_nz =>
              unfold successor
              split
              · next h => nomatch h
              · next sign' _ =>
                  split
                  · next digs hsucc =>
                      rw [h_succ] at hsucc
                      cases hsucc
                  · next digs hsucc =>
                      rw [h_succ] at hsucc
                      injection hsucc with hdigs _
                      subst hdigs
                      have ha0 : ¬ AllZero a.digits.val := by
                        intro hall
                        have hmag := toCardinalNaturalPeano_of_successorList digits
                        rw [h_succ] at hmag
                        dsimp only at hmag
                        have hzero := toCardinalNaturalPeano_zero_of_allZero hall
                        rw [hzero] at hmag
                        exact (CardinalNatural.Peano.successor_ne_zero _).symm hmag
                      have hnz' :=
                        not_allZero_normalizeList_of_not_allZero a.digits.property ha0
                      simp [normalize, hsign, hnz']

theorem successor_predecessor_plus (a : Decimal) (hsign : a.sign = some Sign.plus) :
    successor (predecessor a) ≈ a := by
  change (successor (predecessor a)).normalize = a.normalize
  unfold predecessor
  rw [hsign]
  split
  · next h => nomatch h
  · next sign _ =>
      split
      · next digits hpred =>
          have hall := allZero_of_predecessorList_borrow_true hpred
          have hnorm := normalize_eq_zero_of_allZero a hall
          rw [successor_minusOne, normalize_zero, hnorm]
      · next digits hpred =>
          have h_succ : successorList digits = ⟨a.digits.val, false⟩ := by
            have h := successorList_predecessorList a.digits.val
            simpa [hpred] using h
          split
          · next hzero =>
              rw [successor_zero, normalize_one]
              have hnorm :=
                normalizeList_of_successorList_allZero h_succ hzero a.digits.property
              have hnz' : ¬ AllZero (normalizeList a.digits.val a.digits.property).val := by
                rw [hnorm]
                simp [AllZero, oneDigit]
                exact CardinalNatural.Peano.successor_ne_zero CardinalNatural.Peano.zero
              unfold normalize
              rw [if_neg hnz', hsign, hnorm]
              rfl
          · next hdigits_nz =>
              unfold successor
              split
              · next h => nomatch h
              · next sign' _ =>
                  split
                  · next digs hsucc =>
                      rw [h_succ] at hsucc
                      cases hsucc
                  · next digs hsucc =>
                      rw [h_succ] at hsucc
                      injection hsucc with hdigs _
                      subst hdigs
                      have ha0 : ¬ AllZero a.digits.val := by
                        intro hall
                        have hmag := toCardinalNaturalPeano_of_successorList digits
                        rw [h_succ] at hmag
                        dsimp only at hmag
                        have hzero := toCardinalNaturalPeano_zero_of_allZero hall
                        rw [hzero] at hmag
                        exact (CardinalNatural.Peano.successor_ne_zero _).symm hmag
                      have hnz' :=
                        not_allZero_normalizeList_of_not_allZero a.digits.property ha0
                      simp [normalize, hsign, hnz']

theorem successor_predecessor_minus (a : Decimal) (hsign : a.sign = some Sign.minus) :
    successor (predecessor a) ≈ a := by
  change (successor (predecessor a)).normalize = a.normalize
  unfold predecessor
  rw [hsign]
  split
  · next _ =>
      split
      · -- carry true: predecessor = ⟨minus, 1::digits⟩
        next digits hsucc =>
          have h_pred := predecessorList_of_successorList_carry hsucc
          have hnz := not_allZero_cons_zero_of_successorList_carry a.digits.property hsucc
          unfold successor
          split
          · next _ =>
              split
              · next digs hpred =>
                  rw [h_pred] at hpred
                  cases hpred
              · next digs hpred =>
                  rw [h_pred] at hpred
                  injection hpred with hdigs _
                  subst hdigs
                  simp only [hnz, ↓reduceIte]
                  have hnz0 :=
                    not_allZero_normalizeList_of_not_allZero (by simp) hnz
                  have hnz1 :=
                    not_allZero_normalizeList_of_not_allZero a.digits.property (by
                      intro hall; exact hnz ⟨rfl, hall⟩)
                  simp [normalize, hsign, hnz1,
                    normalizeList_cons_zero zeroDigit a.digits.val rfl a.digits.property]
          · next sign hne =>
              exact False.elim (hne rfl)
      · -- carry false: predecessor = ⟨minus, digits⟩
        next digits hsucc =>
          have h_pred : predecessorList digits = ⟨a.digits.val, false⟩ := by
            have h' := predecessorList_successorList a.digits.val
            simpa [hsucc] using h'
          unfold successor
          split
          · next _ =>
              split
              · next digs hpred =>
                  rw [h_pred] at hpred
                  cases hpred
              · next digs hpred =>
                  rw [h_pred] at hpred
                  injection hpred with hdigs _
                  subst hdigs
                  split
                  · -- AllZero a.digits: successor returns zero
                    next hzero =>
                      have hnorm := normalize_eq_zero_of_allZero a hzero
                      rw [normalize_zero, hnorm]
                  · next hzero =>
                      have hnz' :=
                        not_allZero_normalizeList_of_not_allZero a.digits.property hzero
                      simp [normalize, hsign, hnz']
          · next sign hne =>
              exact False.elim (hne rfl)
  · next sign hne =>
      exact False.elim (hne rfl)

theorem successor_predecessor (a : Decimal) : successor (predecessor a) ≈ a := by
  cases hsign : a.sign with
  | none => exact successor_predecessor_none a hsign
  | some s =>
      cases s with
      | plus => exact successor_predecessor_plus a hsign
      | minus => exact successor_predecessor_minus a hsign

def addMagnitudes (sign : Option Sign) (a b : Sequences.List Digit) : Decimal :=
  let digits := addLists a b
  if hd : digits = Sequences.List.empty then
    zero
  else if AllZero (normalizeList digits hd).val then
    zero
  else
    match sign with
    | some Sign.plus | none => ⟨none, normalizeList digits hd⟩
    | some Sign.minus => ⟨some Sign.minus, normalizeList digits hd⟩

/-- Subtract digit magnitudes `|larger| - |smaller|` when `|smaller| < |larger|`,
    attaching the given sign via `Digits.normalizeList` (`plus` → `none`). -/
def subtractMagnitudes (sign : Option Sign) (larger smaller : Decimal)
    (_h : absoluteCardinalPeano smaller < absoluteCardinalPeano larger) : Decimal :=
  let digits := subtractLists larger.digits.val smaller.digits.val
  if hd : digits = Sequences.List.empty then
    zero
  else if AllZero (normalizeList digits hd).val then
    zero
  else
    match sign with
    | some Sign.plus | none => ⟨none, normalizeList digits hd⟩
    | some Sign.minus => ⟨some Sign.minus, normalizeList digits hd⟩

/-- Opposite-sign addition: `nonneg + (-|neg|)` via magnitude comparison and columnar
    subtraction of the smaller from the larger. -/
def addOppositeSigns (nonneg neg : Decimal) : Decimal :=
  if h : isMagnitudeLessThan nonneg neg then
    subtractMagnitudes (some Sign.minus) neg nonneg
      ((isMagnitudeLessThan_iff_absolute_lt nonneg neg).mp h)
  else if h2 : isMagnitudeLessThan neg nonneg then
    subtractMagnitudes none nonneg neg
      ((isMagnitudeLessThan_iff_absolute_lt neg nonneg).mp h2)
  else
    zero

/-- Columnar addition of decimal integers: same-sign magnitudes are added digit-wise;
    opposite signs subtract the smaller magnitude from the larger. -/
def add (a b : Decimal) : Decimal :=
  match isNegative a, isNegative b with
  | false, false => addMagnitudes none a.digits.val b.digits.val
  | true, true => addMagnitudes (some Sign.minus) a.digits.val b.digits.val
  | false, true => addOppositeSigns a b
  | true, false => addOppositeSigns b a

instance : Add Decimal where
  add := add

/-- Integer subtraction: `a - b = a + (-b)`. -/
def subtract (a b : Decimal) : Decimal :=
  add a (negate b)

instance : Sub Decimal where
  sub := subtract

/-- Columnar multiplication of decimal integers: magnitudes multiply digit-wise;
    the result is negative iff exactly one operand is negative. -/
def multiply (a b : Decimal) : Decimal :=
  let sign : Option Sign :=
    match isNegative a, isNegative b with
    | true, false | false, true => some Sign.minus
    | _, _ => none
  let digits := (multiplyList a.digits.val b.digits.val).1
  if hd : digits = Sequences.List.empty then
    zero
  else if AllZero (normalizeList digits hd).val then
    zero
  else
    match sign with
    | some Sign.plus | none => ⟨none, normalizeList digits hd⟩
    | some Sign.minus => ⟨some Sign.minus, normalizeList digits hd⟩

instance : Mul Decimal where
  mul := multiply

theorem addMagnitudes_toPeano (sign : Option Sign) (a b : Sequences.List Digit) :
    toPeano (addMagnitudes sign a b) =
      match sign with
      | some Sign.minus =>
          -(Peano.fromCardinalNatural
            (Digits.toCardinalNaturalPeano a CardinalNatural.Peano.zero +
              Digits.toCardinalNaturalPeano b CardinalNatural.Peano.zero))
      | _ =>
          Peano.fromCardinalNatural
            (Digits.toCardinalNaturalPeano a CardinalNatural.Peano.zero +
              Digits.toCardinalNaturalPeano b CardinalNatural.Peano.zero) := by
  unfold addMagnitudes
  dsimp only
  have hsum := toCardinalNaturalPeano_addLists a b
  split
  · next heq =>
      have h_list :
          Digits.toCardinalNaturalPeano Sequences.List.empty CardinalNatural.Peano.zero =
            Digits.toCardinalNaturalPeano a CardinalNatural.Peano.zero +
              Digits.toCardinalNaturalPeano b CardinalNatural.Peano.zero := by
        simpa [heq] using hsum
      cases sign with
      | none =>
          simp [toPeano_zero, Digits.toCardinalNaturalPeano] at h_list ⊢
          exact congrArg Peano.fromCardinalNatural h_list.symm ▸ rfl
      | some s =>
          cases s with
          | plus =>
              simp [toPeano_zero, Digits.toCardinalNaturalPeano] at h_list ⊢
              exact congrArg Peano.fromCardinalNatural h_list.symm ▸ rfl
          | minus =>
              simp [toPeano_zero, Digits.toCardinalNaturalPeano] at h_list ⊢
              exact h_list ▸ rfl
  · next hd =>
      split
      · next hzero =>
          have hmag := toCardinalNaturalPeano_zero_of_allZero hzero
          rw [toCardinalNaturalPeano_normalizeList] at hmag
          have hsum0 := hsum.symm.trans hmag
          rw [toPeano_zero, hsum0]
          cases sign with
          | none => rfl
          | some s =>
              cases s with
              | plus => rfl
              | minus => rfl
      · next _hzero =>
          have h_norm := toPeano_signed_normalizeList sign (addLists a b) hd
          rw [h_norm]
          cases sign with
          | none =>
              exact congrArg Peano.fromCardinalNatural hsum
          | some s =>
              cases s with
              | plus =>
                  exact congrArg Peano.fromCardinalNatural hsum
              | minus =>
                  exact congrArg (fun n => -(Peano.fromCardinalNatural n)) hsum

theorem subtractMagnitudes_toPeano (sign : Option Sign) (larger smaller : Decimal)
    (h : absoluteCardinalPeano smaller < absoluteCardinalPeano larger) :
    toPeano (subtractMagnitudes sign larger smaller h) =
      match sign with
      | some Sign.minus =>
          -(Peano.fromCardinalNatural (absoluteCardinalPeano larger)) +
            Peano.fromCardinalNatural (absoluteCardinalPeano smaller)
      | _ =>
          Peano.fromCardinalNatural (absoluteCardinalPeano larger) +
            -(Peano.fromCardinalNatural (absoluteCardinalPeano smaller)) := by
  unfold subtractMagnitudes
  dsimp only
  have hnlt :
      ¬ absoluteCardinalPeano larger < absoluteCardinalPeano smaller :=
    fun hlt => CardinalNatural.Peano.not_lt_self _
      (CardinalNatural.Peano.lt_trans h hlt)
  have h_value :=
    subtractLists_specification larger.digits.val smaller.digits.val hnlt
  have h_sum :
      Digits.toCardinalNaturalPeano
          (subtractLists larger.digits.val smaller.digits.val)
          CardinalNatural.Peano.zero +
        absoluteCardinalPeano smaller =
      absoluteCardinalPeano larger := by
    simpa [absoluteCardinalPeano] using h_value
  split
  · next heq =>
      -- empty difference cannot occur under absoluteCardinalPeano smaller < larger.
      have h_eq : absoluteCardinalPeano smaller = absoluteCardinalPeano larger := by
        simp [Digits.toCardinalNaturalPeano, heq] at h_sum
        exact h_sum
      exact False.elim (CardinalNatural.Peano.not_lt_self _ (h_eq ▸ h))
  · next hd =>
      split
      · next hzero =>
          -- All-zero difference cannot occur under absoluteCardinalPeano smaller < larger.
          have hmag := toCardinalNaturalPeano_zero_of_allZero hzero
          rw [toCardinalNaturalPeano_normalizeList] at hmag
          rw [hmag, CardinalNatural.Peano.zero_add] at h_sum
          exact False.elim (CardinalNatural.Peano.not_lt_self _ (h_sum ▸ h))
      · next _hzero =>
          have h_norm :=
            toPeano_signed_normalizeList sign
              (subtractLists larger.digits.val smaller.digits.val) hd
          rw [h_norm]
          have h_peano_sum :
              Peano.fromCardinalNatural
                  (Digits.toCardinalNaturalPeano
                    (subtractLists larger.digits.val smaller.digits.val)
                    CardinalNatural.Peano.zero) +
                Peano.fromCardinalNatural (absoluteCardinalPeano smaller) =
              Peano.fromCardinalNatural (absoluteCardinalPeano larger) := by
            rw [← Peano.fromCardinalNatural_add, h_sum]
          have h_peano :
              Peano.fromCardinalNatural
                  (Digits.toCardinalNaturalPeano
                    (subtractLists larger.digits.val smaller.digits.val)
                    CardinalNatural.Peano.zero) =
                Peano.fromCardinalNatural (absoluteCardinalPeano larger) +
                  -(Peano.fromCardinalNatural (absoluteCardinalPeano smaller)) :=
            Peano.eq_add_negate_of_add_eq h_peano_sum
          cases sign with
          | none =>
              exact h_peano
          | some s =>
              cases s with
              | plus =>
                  exact h_peano
              | minus =>
                  have h_neg := congrArg Neg.neg h_peano
                  rw [Peano.negate_add, Peano.negate_negate] at h_neg
                  exact h_neg

theorem addOppositeSigns_toPeano (nonneg neg : Decimal)
    (hnonneg : isNegative nonneg = false) (hneg : isNegative neg = true) :
    (addOppositeSigns nonneg neg).toPeano = nonneg.toPeano + neg.toPeano := by
  have hnonneg_peano := toPeano_eq_fromCardinal_of_not_isNegative nonneg hnonneg
  have ⟨hneg_peano, _⟩ := toPeano_eq_negate_fromCardinal_of_isNegative neg hneg
  unfold addOppositeSigns
  split
  · next hlt =>
      rw [subtractMagnitudes_toPeano, hnonneg_peano, hneg_peano, Peano.add_commutative]
  · next hnlt =>
      split
      · next hgt =>
          rw [subtractMagnitudes_toPeano, hnonneg_peano, hneg_peano]
      · next hnge =>
          have h_not_lt : ¬ absoluteCardinalPeano nonneg < absoluteCardinalPeano neg := by
            intro hlt
            exact hnlt ((isMagnitudeLessThan_iff_absolute_lt nonneg neg).mpr hlt)
          have h_not_gt : ¬ absoluteCardinalPeano neg < absoluteCardinalPeano nonneg := by
            intro hgt
            exact hnge ((isMagnitudeLessThan_iff_absolute_lt neg nonneg).mpr hgt)
          have heq : absoluteCardinalPeano nonneg = absoluteCardinalPeano neg := by
            cases CardinalNatural.Peano.trichotomy_or
                (absoluteCardinalPeano nonneg) (absoluteCardinalPeano neg) with
            | inl hlt => exact False.elim (h_not_lt hlt)
            | inr hrest =>
                cases hrest with
                | inl heq => exact heq
                | inr hgt => exact False.elim (h_not_gt hgt)
          rw [toPeano_zero, hnonneg_peano, hneg_peano, heq, Peano.add_negate_self]

@[simp]
theorem add_toPeano (x y : Decimal) :
    (x + y).toPeano = x.toPeano + y.toPeano := by
  change (add x y).toPeano = x.toPeano + y.toPeano
  unfold add
  cases hx : isNegative x with
  | false =>
      cases hy : isNegative y with
      | false =>
          rw [addMagnitudes_toPeano]
          simp only
          rw [toPeano_eq_fromCardinal_of_not_isNegative x hx,
            toPeano_eq_fromCardinal_of_not_isNegative y hy,
            ← Peano.fromCardinalNatural_add]
          rfl
      | true =>
          exact addOppositeSigns_toPeano x y hx hy
  | true =>
      cases hy : isNegative y with
      | false =>
          have h := addOppositeSigns_toPeano y x hy hx
          rw [h, Peano.add_commutative]
      | true =>
          rw [addMagnitudes_toPeano]
          simp only
          have ⟨hx_peano, _⟩ := toPeano_eq_negate_fromCardinal_of_isNegative x hx
          have ⟨hy_peano, _⟩ := toPeano_eq_negate_fromCardinal_of_isNegative y hy
          rw [hx_peano, hy_peano, ← Peano.negate_add, ← Peano.fromCardinalNatural_add]
          rfl

theorem add_commutative (a b : Decimal) : a + b ≈ b + a := by
  apply equivalent_of_toPeano_eq
  rw [add_toPeano, add_toPeano, Peano.add_commutative]

theorem add_associative (a b c : Decimal) : a + b + c ≈ a + (b + c) := by
  apply equivalent_of_toPeano_eq
  rw [add_toPeano, add_toPeano, add_toPeano, add_toPeano, Peano.add_associative]

/-- Addition on the right respects Decimal equivalence. -/
theorem equivalent_add_right {a b c : Decimal} (h : a ≈ b) : a + c ≈ b + c := by
  apply equivalent_of_toPeano_eq
  rw [add_toPeano, add_toPeano, toPeano_eq_of_equivalent h]

/-- Addition on the left respects Decimal equivalence. -/
theorem equivalent_add_left {a b c : Decimal} (h : b ≈ c) : a + b ≈ a + c := by
  apply equivalent_of_toPeano_eq
  rw [add_toPeano, add_toPeano, toPeano_eq_of_equivalent h]

/-- Addition respects Decimal equivalence in both arguments. -/
theorem equivalent_add {a b c d : Decimal} (hab : a ≈ b) (hcd : c ≈ d) :
    a + c ≈ b + d :=
  Setoid.trans (equivalent_add_right hab) (equivalent_add_left hcd)

@[simp]
theorem subtract_toPeano (x y : Decimal) :
    (x - y).toPeano = x.toPeano - y.toPeano := by
  have h : x - y = x + -y := rfl
  rw [h, add_toPeano, negate_toPeano, ← Peano.subtract_eq_add_negate]

theorem add_subtract_cancel (a b : Decimal) : a + b - b ≈ a := by
  apply equivalent_of_toPeano_eq
  rw [subtract_toPeano, add_toPeano, Peano.add_subtract_cancel]

/-- `(a + b) - a` recovers a value equivalent to `b`. -/
theorem add_subtract_cancel_left (a b : Decimal) : a + b - a ≈ b := by
  apply equivalent_of_toPeano_eq
  rw [subtract_toPeano, add_toPeano, Peano.add_subtract_cancel_left]

theorem subtract_add_cancel (a b : Decimal) : a - b + b ≈ a := by
  apply equivalent_of_toPeano_eq
  rw [add_toPeano, subtract_toPeano, Peano.subtract_add_cancel]

/-- A successful step `x - prev ≈ diff` means `x ≈ prev + diff`. -/
theorem equivalent_add_of_subtract (x prev diff : Decimal)
    (h : x - prev ≈ diff) : x ≈ prev + diff := by
  have hsum : x - prev + prev ≈ x := subtract_add_cancel x prev
  have hdiff : diff + prev ≈ x :=
    Setoid.trans (equivalent_add_right (Setoid.symm h)) hsum
  exact Setoid.trans (Setoid.symm hdiff) (add_commutative diff prev)

theorem subtract_associative (a b c : Decimal) : a + b - c ≈ a + (b - c) := by
  apply equivalent_of_toPeano_eq
  rw [subtract_toPeano, add_toPeano, add_toPeano, subtract_toPeano, Peano.subtract_associative]

theorem subtract_add (a b c : Decimal) : a - b + c ≈ a - (b - c) := by
  apply equivalent_of_toPeano_eq
  rw [add_toPeano, subtract_toPeano, subtract_toPeano, subtract_toPeano, Peano.subtract_add]

@[simp]
theorem multiply_toPeano (x y : Decimal) :
    (x * y).toPeano = x.toPeano * y.toPeano := by
  change (multiply x y).toPeano = x.toPeano * y.toPeano
  unfold multiply
  have hmag := (multiplyList_specification x.digits.val y.digits.val).2
  dsimp only
  split
  · next heq =>
      -- empty product digit list: magnitude is zero
      have hmag' := hmag
      rw [heq] at hmag'
      simp [Digits.toCardinalNaturalPeano] at hmag'
      rw [toPeano_zero]
      cases hx : isNegative x with
      | false =>
          cases hy : isNegative y with
          | false =>
              rw [toPeano_eq_fromCardinal_of_not_isNegative x hx,
                toPeano_eq_fromCardinal_of_not_isNegative y hy,
                ← Peano.fromCardinalNatural_multiply]
              simp [absoluteCardinalPeano, ← hmag']
              rfl
          | true =>
              have ⟨hy_peano, _⟩ := toPeano_eq_negate_fromCardinal_of_isNegative y hy
              rw [toPeano_eq_fromCardinal_of_not_isNegative x hx, hy_peano,
                Peano.multiply_negate, ← Peano.fromCardinalNatural_multiply]
              simp [absoluteCardinalPeano, ← hmag']
              rfl
      | true =>
          cases hy : isNegative y with
          | false =>
              have ⟨hx_peano, _⟩ := toPeano_eq_negate_fromCardinal_of_isNegative x hx
              rw [hx_peano, toPeano_eq_fromCardinal_of_not_isNegative y hy,
                Peano.negate_multiply, ← Peano.fromCardinalNatural_multiply]
              simp [absoluteCardinalPeano, ← hmag']
              rfl
          | true =>
              have ⟨hx_peano, _⟩ := toPeano_eq_negate_fromCardinal_of_isNegative x hx
              have ⟨hy_peano, _⟩ := toPeano_eq_negate_fromCardinal_of_isNegative y hy
              rw [hx_peano, hy_peano, Peano.negate_multiply_negate, ← Peano.fromCardinalNatural_multiply]
              simp [absoluteCardinalPeano, ← hmag']
              rfl
  · next hd =>
      split
      · next hzero =>
          have hmag0 := toCardinalNaturalPeano_zero_of_allZero hzero
          rw [toCardinalNaturalPeano_normalizeList] at hmag0
          have hprod := hmag.symm.trans hmag0
          rw [toPeano_zero]
          cases hx : isNegative x with
          | false =>
              cases hy : isNegative y with
              | false =>
                  rw [toPeano_eq_fromCardinal_of_not_isNegative x hx,
                    toPeano_eq_fromCardinal_of_not_isNegative y hy,
                    ← Peano.fromCardinalNatural_multiply]
                  change _ = Peano.fromCardinalNatural
                    (Digits.toCardinalNaturalPeano x.digits.val CardinalNatural.Peano.zero *
                      Digits.toCardinalNaturalPeano y.digits.val CardinalNatural.Peano.zero)
                  rw [hprod]
                  rfl
              | true =>
                  have ⟨hy_peano, _⟩ := toPeano_eq_negate_fromCardinal_of_isNegative y hy
                  rw [toPeano_eq_fromCardinal_of_not_isNegative x hx, hy_peano,
                    Peano.multiply_negate, ← Peano.fromCardinalNatural_multiply]
                  change _ = -(Peano.fromCardinalNatural
                    (Digits.toCardinalNaturalPeano x.digits.val CardinalNatural.Peano.zero *
                      Digits.toCardinalNaturalPeano y.digits.val CardinalNatural.Peano.zero))
                  rw [hprod]
                  rfl
          | true =>
              cases hy : isNegative y with
              | false =>
                  have ⟨hx_peano, _⟩ := toPeano_eq_negate_fromCardinal_of_isNegative x hx
                  rw [hx_peano, toPeano_eq_fromCardinal_of_not_isNegative y hy,
                    Peano.negate_multiply, ← Peano.fromCardinalNatural_multiply]
                  change _ = -(Peano.fromCardinalNatural
                    (Digits.toCardinalNaturalPeano x.digits.val CardinalNatural.Peano.zero *
                      Digits.toCardinalNaturalPeano y.digits.val CardinalNatural.Peano.zero))
                  rw [hprod]
                  rfl
              | true =>
                  have ⟨hx_peano, _⟩ := toPeano_eq_negate_fromCardinal_of_isNegative x hx
                  have ⟨hy_peano, _⟩ := toPeano_eq_negate_fromCardinal_of_isNegative y hy
                  rw [hx_peano, hy_peano, Peano.negate_multiply_negate, ← Peano.fromCardinalNatural_multiply]
                  change _ = Peano.fromCardinalNatural
                    (Digits.toCardinalNaturalPeano x.digits.val CardinalNatural.Peano.zero *
                      Digits.toCardinalNaturalPeano y.digits.val CardinalNatural.Peano.zero)
                  rw [hprod]
                  rfl
      · next _hzero =>
          rw [toPeano_signed_normalizeList _ _ hd]
          cases hx : isNegative x with
          | false =>
              cases hy : isNegative y with
              | false =>
                  simp only
                  rw [toPeano_eq_fromCardinal_of_not_isNegative x hx,
                    toPeano_eq_fromCardinal_of_not_isNegative y hy,
                    ← Peano.fromCardinalNatural_multiply, hmag]
                  rfl
              | true =>
                  simp only
                  have ⟨hy_peano, _⟩ := toPeano_eq_negate_fromCardinal_of_isNegative y hy
                  rw [toPeano_eq_fromCardinal_of_not_isNegative x hx, hy_peano,
                    Peano.multiply_negate, ← Peano.fromCardinalNatural_multiply, hmag]
                  rfl
          | true =>
              cases hy : isNegative y with
              | false =>
                  simp only
                  have ⟨hx_peano, _⟩ := toPeano_eq_negate_fromCardinal_of_isNegative x hx
                  rw [hx_peano, toPeano_eq_fromCardinal_of_not_isNegative y hy,
                    Peano.negate_multiply, ← Peano.fromCardinalNatural_multiply, hmag]
                  rfl
              | true =>
                  simp only
                  have ⟨hx_peano, _⟩ := toPeano_eq_negate_fromCardinal_of_isNegative x hx
                  have ⟨hy_peano, _⟩ := toPeano_eq_negate_fromCardinal_of_isNegative y hy
                  rw [hx_peano, hy_peano, Peano.negate_multiply_negate, ← Peano.fromCardinalNatural_multiply,
                    hmag]
                  rfl

theorem multiply_commutative (a b : Decimal) : a * b ≈ b * a := by
  apply equivalent_of_toPeano_eq
  rw [multiply_toPeano, multiply_toPeano, Peano.multiply_commutative]

theorem multiply_associative (a b c : Decimal) : a * b * c ≈ a * (b * c) := by
  apply equivalent_of_toPeano_eq
  rw [multiply_toPeano, multiply_toPeano, multiply_toPeano, multiply_toPeano,
    Peano.multiply_associative]

theorem multiply_distributive_over_add_right (a b c : Decimal) :
    a * (b + c) ≈ a * b + a * c := by
  apply equivalent_of_toPeano_eq
  rw [multiply_toPeano, add_toPeano, add_toPeano, multiply_toPeano, multiply_toPeano,
    Peano.multiply_add]

theorem multiply_distributive_over_add_left (a b c : Decimal) :
    (a + b) * c ≈ a * c + b * c := by
  apply equivalent_of_toPeano_eq
  rw [multiply_toPeano, add_toPeano, add_toPeano, multiply_toPeano, multiply_toPeano,
    Peano.multiply_commutative (a.toPeano + b.toPeano), Peano.multiply_add,
    Peano.multiply_commutative c.toPeano a.toPeano, Peano.multiply_commutative c.toPeano b.toPeano]

theorem multiply_distributive_over_subtract_right (a b c : Decimal) :
    a * (b - c) ≈ a * b - a * c := by
  apply equivalent_of_toPeano_eq
  rw [multiply_toPeano, subtract_toPeano, subtract_toPeano, multiply_toPeano, multiply_toPeano,
    Peano.multiply_subtract]

theorem multiply_distributive_over_subtract_left (a b c : Decimal) :
    (a - b) * c ≈ a * c - b * c := by
  apply equivalent_of_toPeano_eq
  rw [multiply_toPeano, subtract_toPeano, subtract_toPeano, multiply_toPeano, multiply_toPeano,
    Peano.subtract_multiply]

/-- Multiplication respects Decimal equivalence in both arguments. -/
theorem equivalent_multiply {a b c d : Decimal} (hab : a ≈ b) (hcd : c ≈ d) :
    a * c ≈ b * d := by
  apply equivalent_of_toPeano_eq
  rw [multiply_toPeano, multiply_toPeano, toPeano_eq_of_equivalent hab,
    toPeano_eq_of_equivalent hcd]

/-- Convert an ordinal Peano natural to a non-negative decimal integer. -/
def fromOrdinalNaturalPeano : OrdinalNatural.Peano → Decimal
  | .one => one
  | .successor n => successor (fromOrdinalNaturalPeano n)

/-- Convert an integer Peano value to a decimal representation. -/
def fromPeano : Peano → Decimal
  | .zero => zero
  | .positive n => fromOrdinalNaturalPeano n
  | .negative n => -(fromOrdinalNaturalPeano n)

@[simp]
theorem toPeano_fromOrdinalNaturalPeano (n : OrdinalNatural.Peano) :
    (fromOrdinalNaturalPeano n).toPeano = Peano.positive n := by
  induction n with
  | one =>
    rfl
  | successor n ih =>
    unfold fromOrdinalNaturalPeano
    rw [successor_toPeano, ih]
    rfl

/-- `fromOrdinalNaturalPeano n` is never equivalent to zero. -/
theorem fromOrdinalNaturalPeano_not_equivalent_zero (n : OrdinalNatural.Peano) :
    ¬ fromOrdinalNaturalPeano n ≈ zero := by
  intro h
  have hz : (fromOrdinalNaturalPeano n).toPeano = Peano.zero :=
    (toPeano_eq_of_equivalent h).trans toPeano_zero
  rw [toPeano_fromOrdinalNaturalPeano] at hz
  exact Peano.positive_ne_zero n hz

/-- The Peano embedding of `fromOrdinalNaturalPeano n - one`. -/
theorem fromOrdinalNaturalPeano_subtract_one_toPeano (n : OrdinalNatural.Peano) :
    (fromOrdinalNaturalPeano n - one).toPeano =
      Peano.positive n - Peano.one := by
  rw [subtract_toPeano, toPeano_fromOrdinalNaturalPeano, toPeano_one]

@[simp]
theorem toPeano_fromPeano (x : Peano) : (fromPeano x).toPeano = x := by
  cases x with
  | zero => rfl
  | positive n =>
    exact toPeano_fromOrdinalNaturalPeano n
  | negative n =>
    unfold fromPeano
    rw [negate_toPeano, toPeano_fromOrdinalNaturalPeano]
    rfl

theorem fromPeano_toPeano (x : Decimal) : fromPeano (toPeano x) ≈ x := by
  apply equivalent_of_toPeano_eq
  exact toPeano_fromPeano (toPeano x)

/-- `fromOrdinalNaturalPeano n` is a strictly positive decimal integer. -/
theorem zero_lt_fromOrdinalNaturalPeano (n : OrdinalNatural.Peano) :
    zero < fromOrdinalNaturalPeano n := by
  change zero.toPeano < (fromOrdinalNaturalPeano n).toPeano
  rw [toPeano_zero, toPeano_fromOrdinalNaturalPeano]
  exact Peano.LessThan.zero_less_than_positive

theorem toPeano_positive_of_positive {a : Decimal} (h : zero < a) :
    Peano.zero < a.toPeano := by
  rw [← toPeano_zero]
  exact h

/-- Convert a strictly positive decimal integer to an ordinal Peano natural. -/
def toOrdinalNaturalPeano (a : Decimal) (h : zero < a) : OrdinalNatural.Peano :=
  Peano.toOrdinalNatural a.toPeano (toPeano_positive_of_positive h)

@[simp]
theorem toOrdinalNaturalPeano_fromOrdinalNaturalPeano (n : OrdinalNatural.Peano) :
    toOrdinalNaturalPeano (fromOrdinalNaturalPeano n)
      (zero_lt_fromOrdinalNaturalPeano n) = n := by
  have hpos :=
    Peano.eq_positive_of_positive (toPeano_positive_of_positive (zero_lt_fromOrdinalNaturalPeano n))
  have heq := hpos.symm.trans (toPeano_fromOrdinalNaturalPeano n)
  injection heq

theorem fromOrdinalNaturalPeano_toOrdinalNaturalPeano (a : Decimal) (h : zero < a) :
    fromOrdinalNaturalPeano (toOrdinalNaturalPeano a h) ≈ a := by
  apply equivalent_of_toPeano_eq
  rw [toPeano_fromOrdinalNaturalPeano]
  exact (Peano.eq_positive_of_positive (toPeano_positive_of_positive h)).symm

example : fromOrdinalNaturalPeano OrdinalNatural.Peano.one = one := rfl
example : toOrdinalNaturalPeano one (by decide) = OrdinalNatural.Peano.one := rfl
example : toOrdinalNaturalPeano two (by decide) = OrdinalNatural.Peano.two := rfl

/-- Reinterpret a positive ordinal Decimal as a non-negative integer Decimal
with the same digits and no sign. -/
def fromOrdinalNatural (a : OrdinalNatural.Decimal) : Decimal :=
  ⟨none, CardinalNatural.Decimal.fromOrdinal a⟩

/-- A strictly positive decimal integer has a nonzero digit. -/
theorem hasNonZero_of_positive {a : Decimal} (h : zero < a) :
    HasNonZero a.digits.val := by
  cases allZero_or_hasNonZero a.digits.val with
  | inl hall =>
    have hz : zero ≈ a := by
      change zero.normalize = a.normalize
      rw [normalize_zero, normalize_eq_zero_of_allZero a hall]
    exact (not_equivalent_of_lt h hz).elim
  | inr hnz => exact hnz

/-- Reinterpret a strictly positive integer Decimal as an ordinal Decimal with
the same digits. -/
def toOrdinalNatural (a : Decimal) (h : zero < a) : OrdinalNatural.Decimal :=
  ⟨a.digits.val, hasNonZero_of_positive h⟩

/-- Digit reinterpretation of an ordinal Decimal embeds as that ordinal's
positive integer Peano value. -/
@[simp]
theorem fromOrdinalNatural_toPeano (a : OrdinalNatural.Decimal) :
    (fromOrdinalNatural a).toPeano = Peano.positive a.toPeano := by
  change Peano.fromCardinalNatural (OrdinalNatural.Decimal.toCardinalPeano a) =
    Peano.positive a.toPeano
  have hcard : OrdinalNatural.Decimal.toCardinalPeano a =
      CardinalNatural.Peano.fromOrdinal a.toPeano :=
    (CardinalNatural.Peano.fromOrdinal_toOrdinal
      (OrdinalNatural.Decimal.toCardinalPeano a)
      (OrdinalNatural.Decimal.toCardinalPeano_ne_zero a)).symm
  rw [hcard, Peano.fromCardinalNatural_fromOrdinal]

/-- `fromOrdinalNatural a` is a strictly positive decimal integer. -/
theorem zero_lt_fromOrdinalNatural (a : OrdinalNatural.Decimal) :
    zero < fromOrdinalNatural a := by
  change zero.toPeano < (fromOrdinalNatural a).toPeano
  rw [toPeano_zero, fromOrdinalNatural_toPeano]
  exact Peano.LessThan.zero_less_than_positive

/-- `fromOrdinalNatural a` is never equivalent to zero. -/
theorem fromOrdinalNatural_not_equivalent_zero (a : OrdinalNatural.Decimal) :
    ¬ fromOrdinalNatural a ≈ zero :=
  fun heq =>
    not_equivalent_of_lt (zero_lt_fromOrdinalNatural a) (Setoid.symm heq)

/-- `fromOrdinalNatural` of any positive ordinal Decimal is at least `one`. -/
theorem one_le_fromOrdinalNatural (a : OrdinalNatural.Decimal) :
    one ≤ fromOrdinalNatural a := by
  apply le_of_toPeano_le
  rw [toPeano_one, fromOrdinalNatural_toPeano]
  cases OrdinalNatural.Peano.one_le a.toPeano with
  | inl heq => exact Or.inr (congrArg Peano.positive heq.symm)
  | inr hlt => exact Or.inl (Peano.LessThan.positive_less_than_positive hlt)

/-- The Peano embedding of `fromOrdinalNatural a - one`. -/
theorem fromOrdinalNatural_subtract_one_toPeano (a : OrdinalNatural.Decimal) :
    (fromOrdinalNatural a - one).toPeano =
      Peano.positive a.toPeano - Peano.one := by
  rw [subtract_toPeano, fromOrdinalNatural_toPeano, toPeano_one]

/-- Digit reinterpretation is a left inverse of `fromOrdinalNatural`. -/
@[simp]
theorem toOrdinalNatural_fromOrdinalNatural (a : OrdinalNatural.Decimal) :
    toOrdinalNatural (fromOrdinalNatural a) (zero_lt_fromOrdinalNatural a) = a :=
  rfl

/-- The ordinal Decimal from a positive integer has the same Peano value as
`toOrdinalNaturalPeano`. -/
@[simp]
theorem toOrdinalNatural_toPeano (a : Decimal) (h : zero < a) :
    (toOrdinalNatural a h).toPeano = toOrdinalNaturalPeano a h := by
  have heq : a.toPeano = Peano.positive (toOrdinalNaturalPeano a h) :=
    Peano.eq_positive_of_positive (toPeano_positive_of_positive h)
  have habs : absoluteCardinalPeano a =
      CardinalNatural.Peano.fromOrdinal (toOrdinalNaturalPeano a h) :=
    absoluteCardinalPeano_eq_fromOrdinal_of_toPeano_positive a
      (toOrdinalNaturalPeano a h) heq
  have hcard : OrdinalNatural.Decimal.toCardinalPeano (toOrdinalNatural a h) =
      CardinalNatural.Peano.fromOrdinal (toOrdinalNaturalPeano a h) := habs
  unfold OrdinalNatural.Decimal.toPeano
  rw [CardinalNatural.Peano.toOrdinal_congr hcard
    (OrdinalNatural.Decimal.toCardinalPeano_ne_zero (toOrdinalNatural a h))
    (CardinalNatural.Peano.fromOrdinal_ne_zero (toOrdinalNaturalPeano a h))]
  exact CardinalNatural.Peano.toOrdinal_fromOrdinal_helper
    (toOrdinalNaturalPeano a h)
    (CardinalNatural.Peano.fromOrdinal_ne_zero (toOrdinalNaturalPeano a h))

/-- Digit reinterpretation recovers a positive integer up to equivalence. -/
theorem fromOrdinalNatural_toOrdinalNatural (a : Decimal) (h : zero < a) :
    fromOrdinalNatural (toOrdinalNatural a h) ≈ a := by
  apply equivalent_of_toPeano_eq
  rw [fromOrdinalNatural_toPeano, toOrdinalNatural_toPeano]
  exact (Peano.eq_positive_of_positive (toPeano_positive_of_positive h)).symm

/-- `fromOrdinalNatural` agrees with `fromOrdinalNaturalPeano` of the ordinal
Peano embedding. -/
theorem fromOrdinalNatural_eq_fromOrdinalNaturalPeano
    (a : OrdinalNatural.Decimal) :
    fromOrdinalNatural a ≈ fromOrdinalNaturalPeano a.toPeano := by
  apply equivalent_of_toPeano_eq
  rw [fromOrdinalNatural_toPeano, toPeano_fromOrdinalNaturalPeano]

/-- `fromOrdinalNatural` of the Decimal embedding of an ordinal Peano agrees
with `fromOrdinalNaturalPeano`. -/
theorem fromOrdinalNatural_fromPeano (n : OrdinalNatural.Peano) :
    fromOrdinalNatural (OrdinalNatural.Decimal.fromPeano n) ≈
      fromOrdinalNaturalPeano n := by
  apply equivalent_of_toPeano_eq
  rw [fromOrdinalNatural_toPeano, OrdinalNatural.Decimal.toPeano_fromPeano,
    toPeano_fromOrdinalNaturalPeano]

example : fromOrdinalNatural OrdinalNatural.Decimal.one = one := rfl
example : toOrdinalNatural one (by decide) = OrdinalNatural.Decimal.one := rfl
example : toOrdinalNatural two (by decide) = OrdinalNatural.Decimal.two := rfl

/-- Convert a cardinal Peano natural to a non-negative decimal integer. -/
def fromCardinalNaturalPeano : CardinalNatural.Peano → Decimal
  | .zero => zero
  | .successor n => successor (fromCardinalNaturalPeano n)

@[simp]
theorem toPeano_fromCardinalNaturalPeano (n : CardinalNatural.Peano) :
    (fromCardinalNaturalPeano n).toPeano = Peano.fromCardinalNatural n := by
  induction n with
  | zero =>
    rfl
  | successor n ih =>
    unfold fromCardinalNaturalPeano
    rw [successor_toPeano, ih]
    exact (Peano.fromCardinalNatural_successor n).symm

/-- `fromCardinalNaturalPeano n` is a non-negative decimal integer. -/
theorem zero_le_fromCardinalNaturalPeano (n : CardinalNatural.Peano) :
    zero ≤ fromCardinalNaturalPeano n := by
  apply le_of_toPeano_le
  rw [toPeano_zero, toPeano_fromCardinalNaturalPeano]
  cases n with
  | zero => exact Or.inr rfl
  | successor _ => exact Or.inl Peano.LessThan.zero_less_than_positive

theorem toPeano_nonNegative_of_nonNegative {a : Decimal} (h : zero ≤ a) :
    Peano.zero ≤ a.toPeano := by
  rw [← toPeano_zero]
  exact toPeano_le_of_le h

/-- Convert a non-negative decimal integer to a cardinal Peano natural. -/
def toCardinalNaturalPeano (a : Decimal) (_h : zero ≤ a) : CardinalNatural.Peano :=
  absoluteCardinalPeano a

@[simp]
theorem toCardinalNaturalPeano_fromCardinalNaturalPeano (n : CardinalNatural.Peano) :
    toCardinalNaturalPeano (fromCardinalNaturalPeano n)
      (zero_le_fromCardinalNaturalPeano n) = n := by
  unfold toCardinalNaturalPeano
  apply Peano.fromCardinalNatural_injective
  rw [← toPeano_absoluteValue_fromCardinal, toPeano_fromCardinalNaturalPeano]
  cases n with
  | zero => rfl
  | successor _ => rfl

theorem fromCardinalNaturalPeano_toCardinalNaturalPeano (a : Decimal) (h : zero ≤ a) :
    fromCardinalNaturalPeano (toCardinalNaturalPeano a h) ≈ a := by
  apply equivalent_of_toPeano_eq
  unfold toCardinalNaturalPeano
  rw [toPeano_fromCardinalNaturalPeano]
  have habs := toPeano_absoluteValue_fromCardinal a
  have hpeano := toPeano_nonNegative_of_nonNegative h
  cases ha : a.toPeano with
  | zero =>
    rw [ha] at habs
    simp [Peano.absoluteValue] at habs
    exact habs.symm
  | positive _ =>
    rw [ha] at habs
    simp [Peano.absoluteValue] at habs
    exact habs.symm
  | negative _ =>
    rw [ha] at hpeano
    cases hpeano with
    | inl hlt => cases hlt
    | inr heq => cases heq

theorem toPeano_eq_fromCardinalNatural_of_zero_le (a : Decimal) (h : zero ≤ a) :
    a.toPeano = Peano.fromCardinalNatural (toCardinalNaturalPeano a h) := by
  have heq :=
    toPeano_eq_of_equivalent (fromCardinalNaturalPeano_toCardinalNaturalPeano a h)
  rw [toPeano_fromCardinalNaturalPeano] at heq
  exact heq.symm

example : fromCardinalNaturalPeano CardinalNatural.Peano.zero = zero := rfl
example : fromCardinalNaturalPeano CardinalNatural.Peano.one = one := successor_zero
example : toCardinalNaturalPeano zero (by decide) = CardinalNatural.Peano.zero := rfl
example : toCardinalNaturalPeano one (by decide) = CardinalNatural.Peano.one := rfl

/-- Reinterpret a cardinal Decimal as a non-negative integer Decimal
with the same digits and no sign. -/
def fromCardinalNatural (a : CardinalNatural.Decimal) : Decimal :=
  ⟨none, a⟩

/-- Reinterpret a non-negative integer Decimal as a cardinal Decimal with
the same digits. -/
def toCardinalNatural (a : Decimal) (_h : zero ≤ a) : CardinalNatural.Decimal :=
  ⟨a.digits.val, a.digits.property⟩

/-- Digit reinterpretation of a cardinal Decimal embeds as that cardinal's
non-negative integer Peano value. -/
@[simp]
theorem fromCardinalNatural_toPeano (a : CardinalNatural.Decimal) :
    (fromCardinalNatural a).toPeano = Peano.fromCardinalNatural a.toPeano :=
  rfl

/-- `fromCardinalNatural a` is a non-negative decimal integer. -/
theorem zero_le_fromCardinalNatural (a : CardinalNatural.Decimal) :
    zero ≤ fromCardinalNatural a := by
  apply le_of_toPeano_le
  rw [toPeano_zero, fromCardinalNatural_toPeano]
  cases a.toPeano with
  | zero => exact Or.inr rfl
  | successor _ => exact Or.inl Peano.LessThan.zero_less_than_positive

/-- Digit reinterpretation is a left inverse of `fromCardinalNatural`. -/
@[simp]
theorem toCardinalNatural_fromCardinalNatural (a : CardinalNatural.Decimal) :
    toCardinalNatural (fromCardinalNatural a) (zero_le_fromCardinalNatural a) = a :=
  rfl

/-- The cardinal Decimal from a non-negative integer has the same Peano value as
`toCardinalNaturalPeano`. -/
@[simp]
theorem toCardinalNatural_toPeano (a : Decimal) (h : zero ≤ a) :
    (toCardinalNatural a h).toPeano = toCardinalNaturalPeano a h :=
  rfl

/-- Digit reinterpretation recovers a non-negative integer up to equivalence. -/
theorem fromCardinalNatural_toCardinalNatural (a : Decimal) (h : zero ≤ a) :
    fromCardinalNatural (toCardinalNatural a h) ≈ a := by
  apply equivalent_of_toPeano_eq
  rw [fromCardinalNatural_toPeano, toCardinalNatural_toPeano]
  have hround :=
    toPeano_eq_of_equivalent (fromCardinalNaturalPeano_toCardinalNaturalPeano a h)
  rw [toPeano_fromCardinalNaturalPeano] at hround
  exact hround

/-- `fromCardinalNatural` agrees with `fromCardinalNaturalPeano` of the cardinal
Peano embedding. -/
theorem fromCardinalNatural_eq_fromCardinalNaturalPeano
    (a : CardinalNatural.Decimal) :
    fromCardinalNatural a ≈ fromCardinalNaturalPeano a.toPeano := by
  apply equivalent_of_toPeano_eq
  rw [fromCardinalNatural_toPeano, toPeano_fromCardinalNaturalPeano]

/-- `fromCardinalNatural` of the Decimal embedding of a cardinal Peano agrees
with `fromCardinalNaturalPeano`. -/
theorem fromCardinalNatural_fromPeano (n : CardinalNatural.Peano) :
    fromCardinalNatural (CardinalNatural.Decimal.fromPeano n) ≈
      fromCardinalNaturalPeano n := by
  apply equivalent_of_toPeano_eq
  rw [fromCardinalNatural_toPeano, CardinalNatural.Decimal.toPeano_fromPeano,
    toPeano_fromCardinalNaturalPeano]

example : fromCardinalNatural CardinalNatural.Decimal.zero = zero := rfl
example : fromCardinalNatural CardinalNatural.Decimal.one = one := rfl
example : toCardinalNatural zero (by decide) = CardinalNatural.Decimal.zero := rfl
example : toCardinalNatural one (by decide) = CardinalNatural.Decimal.one := rfl
example : toCardinalNatural two (by decide) = CardinalNatural.Decimal.two := rfl

theorem toPeano_ne_zero_of_not_equivalent_zero {x : Decimal} (h : ¬ x ≈ zero) :
    x.toPeano ≠ Peano.zero := by
  intro hx
  exact h (equivalent_of_toPeano_eq (hx.trans toPeano_zero.symm))

/-- `a` is divisible by `b` when `b` is non-zero (up to equivalence) and there is a
decimal quotient `c` with `b * c ≈ a`. -/
def Divisible (a b : Decimal) : Prop := ¬ (b ≈ zero) ∧ ∃ c, b * c ≈ a

theorem Divisible_toPeano (a b : Decimal) :
    Divisible a b ↔ Peano.Divisible a.toPeano b.toPeano := by
  apply Iff.intro
  · intro h
    unfold Divisible at h
    unfold Peano.Divisible
    obtain ⟨hb, c, hc⟩ := h
    refine ⟨toPeano_ne_zero_of_not_equivalent_zero hb, c.toPeano, ?_⟩
    rw [← multiply_toPeano]
    exact toPeano_eq_of_equivalent hc
  · intro h
    unfold Divisible
    unfold Peano.Divisible at h
    obtain ⟨hb, c_peano, hc⟩ := h
    let c := fromPeano c_peano
    refine ⟨?_, c, ?_⟩
    · intro heq
      exact hb ((toPeano_eq_of_equivalent heq).trans toPeano_zero)
    · apply equivalent_of_toPeano_eq
      rw [multiply_toPeano]
      have h_c_toPeano : c.toPeano = c_peano := toPeano_fromPeano c_peano
      rw [h_c_toPeano]
      exact hc

/-- Absolute magnitude as a cardinal decimal (digit list only). -/
def magnitude (a : Decimal) : CardinalNatural.Decimal :=
  ⟨a.digits.val, a.digits.property⟩

@[simp]
theorem magnitude_toPeano (a : Decimal) :
    a.magnitude.toPeano = absoluteCardinalPeano a := rfl

/-- `toCardinalNatural` is the digit list of `a`, the same as `magnitude`. -/
theorem toCardinalNatural_eq_magnitude (a : Decimal) (h : zero ≤ a) :
    toCardinalNatural a h = a.magnitude :=
  rfl

/-- Boolean divisibility on magnitudes via cardinal decimal long division. -/
def isDivisible (a b : Decimal) : Bool :=
  CardinalNatural.Decimal.isDivisible a.magnitude b.magnitude

theorem isDivisible_eq_cardinal_magnitude (a b : Decimal) :
    isDivisible a b =
      CardinalNatural.Decimal.isDivisible a.magnitude b.magnitude := rfl

theorem toPeano_eq_zero_of_absoluteCardinal_zero {a : Decimal}
    (ha : absoluteCardinalPeano a = CardinalNatural.Peano.zero) :
    a.toPeano = Peano.zero := by
  unfold toPeano
  cases a.sign with
  | none => simp only [ha, Peano.fromCardinalNatural]
  | some s =>
    cases s with
    | plus => simp only [ha, Peano.fromCardinalNatural]
    | minus => simp only [ha, Peano.fromCardinalNatural, Peano.negate]

/-- The cardinal magnitude of a nonzero decimal integer is a nonzero cardinal
decimal. -/
theorem magnitude_not_equivalent_zero_of_not_equivalent_zero {x : Decimal}
    (h : ¬ x ≈ zero) : ¬ x.magnitude ≈ CardinalNatural.Decimal.zero := by
  intro hm
  have hmag0 : x.magnitude.toPeano = CardinalNatural.Peano.zero := by
    rw [CardinalNatural.Decimal.toPeano_eq_of_equivalent hm,
      CardinalNatural.Decimal.toPeano_zero]
  have habs : absoluteCardinalPeano x = CardinalNatural.Peano.zero := by
    rw [← magnitude_toPeano, hmag0]
  have hx0 : x.toPeano = Peano.zero := toPeano_eq_zero_of_absoluteCardinal_zero habs
  exact h (equivalent_of_toPeano_eq (hx0.trans toPeano_zero.symm))

theorem toPeano_eq_signed_toOrdinal_of_absoluteCardinal_successor
    (a : Decimal) (n : CardinalNatural.Peano)
    (ha : absoluteCardinalPeano a = CardinalNatural.Peano.successor n) :
    a.toPeano =
        Peano.positive
          (CardinalNatural.Peano.toOrdinal (CardinalNatural.Peano.successor n)
            (CardinalNatural.Peano.successor_ne_zero n)) ∨
      a.toPeano =
        Peano.negative
          (CardinalNatural.Peano.toOrdinal (CardinalNatural.Peano.successor n)
            (CardinalNatural.Peano.successor_ne_zero n)) := by
  unfold toPeano
  cases a.sign with
  | none =>
    left
    show Peano.fromCardinalNatural (absoluteCardinalPeano a) =
      Peano.positive
        (CardinalNatural.Peano.toOrdinal (CardinalNatural.Peano.successor n)
          (CardinalNatural.Peano.successor_ne_zero n))
    rw [ha]
    rfl
  | some s =>
    cases s with
    | plus =>
      left
      show Peano.fromCardinalNatural (absoluteCardinalPeano a) =
        Peano.positive
          (CardinalNatural.Peano.toOrdinal (CardinalNatural.Peano.successor n)
            (CardinalNatural.Peano.successor_ne_zero n))
      rw [ha]
      rfl
    | minus =>
      right
      show Peano.negate (Peano.fromCardinalNatural (absoluteCardinalPeano a)) =
        Peano.negative
          (CardinalNatural.Peano.toOrdinal (CardinalNatural.Peano.successor n)
            (CardinalNatural.Peano.successor_ne_zero n))
      rw [ha]
      rfl

theorem peano_isDivisible_eq_absoluteCardinal (a b : Decimal) :
    CardinalNatural.Peano.isDivisible (absoluteCardinalPeano a) (absoluteCardinalPeano b) =
      Peano.isDivisible a.toPeano b.toPeano := by
  cases hb : absoluteCardinalPeano b with
  | zero =>
    have hb_peano := toPeano_eq_zero_of_absoluteCardinal_zero hb
    simp only [CardinalNatural.Peano.isDivisible, hb_peano, Peano.isDivisible]
  | successor b' =>
    cases ha : absoluteCardinalPeano a with
    | zero =>
      have ha_peano := toPeano_eq_zero_of_absoluteCardinal_zero ha
      have hb_ne : b.toPeano ≠ Peano.zero := by
        intro h0
        have habs := absoluteCardinalPeano_eq_of_toPeano_eq (h0.trans toPeano_zero.symm)
        simp only [absoluteCardinalPeano, zero, Digits.toCardinalNaturalPeano, zeroDigit] at habs
        exact CardinalNatural.Peano.successor_ne_zero b' (hb.symm.trans habs)
      simp only [CardinalNatural.Peano.isDivisible, ha_peano]
      cases hb_peano : b.toPeano with
      | zero => exact False.elim (hb_ne hb_peano)
      | positive _ => rfl
      | negative _ => rfl
    | successor a' =>
      have ha_pos :=
        toPeano_eq_signed_toOrdinal_of_absoluteCardinal_successor a a' ha
      have hb_pos :=
        toPeano_eq_signed_toOrdinal_of_absoluteCardinal_successor b b' hb
      have hcard_eq_ord :=
        CardinalNatural.Peano.isDivisible_toOrdinal
          (CardinalNatural.Peano.successor a')
          (CardinalNatural.Peano.successor b')
          (CardinalNatural.Peano.successor_ne_zero a')
          (CardinalNatural.Peano.successor_ne_zero b')
      rw [hcard_eq_ord]
      cases ha_pos with
      | inl ha_eq =>
        cases hb_pos with
        | inl hb_eq => simp only [ha_eq, hb_eq, Peano.isDivisible]
        | inr hb_eq => simp only [ha_eq, hb_eq, Peano.isDivisible]
      | inr ha_eq =>
        cases hb_pos with
        | inl hb_eq => simp only [ha_eq, hb_eq, Peano.isDivisible]
        | inr hb_eq => simp only [ha_eq, hb_eq, Peano.isDivisible]

theorem isDivisible_eq_peano (a b : Decimal) :
    isDivisible a b = Peano.isDivisible a.toPeano b.toPeano := by
  calc
    isDivisible a b
        = CardinalNatural.Decimal.isDivisible a.magnitude b.magnitude :=
          isDivisible_eq_cardinal_magnitude a b
    _ = CardinalNatural.Peano.isDivisible
          a.magnitude.toPeano b.magnitude.toPeano :=
          CardinalNatural.Decimal.isDivisible_eq_peano a.magnitude b.magnitude
    _ = CardinalNatural.Peano.isDivisible
          (absoluteCardinalPeano a) (absoluteCardinalPeano b) := by
            simp only [magnitude_toPeano]
    _ = Peano.isDivisible a.toPeano b.toPeano :=
          peano_isDivisible_eq_absoluteCardinal a b

theorem isDivisible_correct (a b : Decimal) : Divisible a b ↔ isDivisible a b := by
  rw [Divisible_toPeano, isDivisible_eq_peano]
  exact Peano.isDivisible_correct a.toPeano b.toPeano

def Even (a : Decimal) : Prop := Divisible a two

def Odd (a : Decimal) : Prop := ¬ Even a

theorem Even_toPeano (a : Decimal) : Even a ↔ Peano.Even a.toPeano := by
  unfold Even Peano.Even
  rw [Divisible_toPeano, toPeano_two]

theorem Odd_toPeano (a : Decimal) : Odd a ↔ Peano.Odd a.toPeano := by
  unfold Odd Peano.Odd
  rw [Even_toPeano]

def lastDigit (a : Decimal) : Digit :=
  Sequences.List.lastElement a.digits.val a.digits.property

def isEven (a : Decimal) : Bool :=
  CardinalNatural.Peano.isEven (lastDigit a).val

def isOdd (a : Decimal) : Bool := !isEven a

theorem absoluteCardinalPeano_two : absoluteCardinalPeano two = CardinalNatural.Peano.two := by
  apply Peano.fromCardinalNatural_injective
  rw [← toPeano_absoluteValue_fromCardinal, toPeano_two]
  rfl

theorem even_toPeano_iff_absoluteCardinal (a : Decimal) :
    Peano.Even a.toPeano ↔ CardinalNatural.Peano.Even (absoluteCardinalPeano a) := by
  unfold Peano.Even CardinalNatural.Peano.Even
  rw [Peano.isDivisible_correct, CardinalNatural.Peano.isDivisible_correct]
  rw [← toPeano_two, ← peano_isDivisible_eq_absoluteCardinal a two, absoluteCardinalPeano_two]

theorem even_toCardinalPeano_iff_lastDigit (a : Decimal) :
    CardinalNatural.Peano.Even (absoluteCardinalPeano a) ↔
      CardinalNatural.Peano.Even (lastDigit a).val := by
  unfold absoluteCardinalPeano lastDigit
  exact toCardinalNaturalPeano_even_iff_lastElement a.digits.val a.digits.property

theorem isEven_correct (x : Decimal) : Even x ↔ isEven x := by
  rw [Even_toPeano, even_toPeano_iff_absoluteCardinal, even_toCardinalPeano_iff_lastDigit]
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
  exact Peano.isEven_successor x.toPeano ((Even_toPeano x).mp h)

theorem odd_successor {x : Decimal} (h : Odd x) : Even (successor x) := by
  rw [Even_toPeano, successor_toPeano]
  exact Peano.isOdd_successor x.toPeano ((Odd_toPeano x).mp h)

theorem even_predecessor {x : Decimal} (h : Even x) : Odd (predecessor x) := by
  rw [Odd_toPeano, predecessor_toPeano]
  exact Peano.isEven_predecessor x.toPeano ((Even_toPeano x).mp h)

theorem odd_predecessor {x : Decimal} (h : Odd x) : Even (predecessor x) := by
  rw [Even_toPeano, predecessor_toPeano]
  exact Peano.isOdd_predecessor x.toPeano ((Odd_toPeano x).mp h)

/-- Optional exact division of decimal integers: magnitudes divide via cardinal
decimal `tryDivide`; the quotient is negative iff exactly one operand is
negative. Returns `none` when the divisor is zero or the remainder is nonzero. -/
def tryDivide (a b : Decimal) : Option Decimal :=
  (CardinalNatural.Decimal.tryDivide a.magnitude b.magnitude).map fun q =>
    if AllZero q.val then
      zero
    else
      match isNegative a, isNegative b with
      | true, false | false, true => ⟨some Sign.minus, ⟨q.val, q.property⟩⟩
      | _, _ => ⟨none, ⟨q.val, q.property⟩⟩

/-- Cardinal magnitude divisibility from integer decimal divisibility. -/
theorem divisible_magnitude (a b : Decimal) (h : Divisible a b) :
    CardinalNatural.Decimal.Divisible a.magnitude b.magnitude :=
  (CardinalNatural.Decimal.isDivisible_correct a.magnitude b.magnitude).mpr
    ((isDivisible_correct a b).mp h)

/-- Exact division of decimal integers when `b` divides `a`. Magnitudes divide
via cardinal decimal `divide`; the quotient is negative iff exactly one operand
is negative. Zero quotients are unsigned `zero`. -/
def divide (a b : Decimal) (h : Divisible a b) : Decimal :=
  let q := CardinalNatural.Decimal.divide a.magnitude b.magnitude
    (divisible_magnitude a b h)
  if AllZero q.val then
    zero
  else
    match isNegative a, isNegative b with
    | true, false | false, true => ⟨some Sign.minus, ⟨q.val, q.property⟩⟩
    | _, _ => ⟨none, ⟨q.val, q.property⟩⟩

/-- The Peano value of `divide x y h` is the signed cardinal quotient of the
magnitudes: negative iff `x` and `y` have opposite signs. -/
theorem divide_toPeano_eq_signed (x y : Decimal) (h : Divisible x y)
    {q : CardinalNatural.Decimal}
    (hq : q = CardinalNatural.Decimal.divide x.magnitude y.magnitude
      (divisible_magnitude x y h)) :
    (divide x y h).toPeano =
      match isNegative x, isNegative y with
      | true, false | false, true =>
          -(Peano.fromCardinalNatural q.toPeano)
      | _, _ =>
          Peano.fromCardinalNatural q.toPeano := by
  unfold divide
  simp only [← hq]
  split
  · next hzero =>
      have hq0 : q.toPeano = CardinalNatural.Peano.zero :=
        toCardinalNaturalPeano_zero_of_allZero hzero
      rw [toPeano_zero, hq0]
      cases isNegative x <;> cases isNegative y <;> rfl
  · next _hnz =>
      cases isNegative x <;> cases isNegative y <;> rfl

theorem divide_toPeano (x y : Decimal) (h : Divisible x y) :
    ∃ h2, (divide x y h).toPeano = Peano.divide x.toPeano y.toPeano h2 := by
  let h2 := (Divisible_toPeano x y).mp h
  refine ⟨h2, ?_⟩
  apply Peano.multiply_left_cancel y.toPeano
    (divide x y h).toPeano
    (Peano.divide x.toPeano y.toPeano h2)
    h2.1
  rw [Peano.divide_correct x.toPeano y.toPeano h2]
  let q := CardinalNatural.Decimal.divide x.magnitude y.magnitude
    (divisible_magnitude x y h)
  have hsigned := divide_toPeano_eq_signed x y h (q := q) rfl
  obtain ⟨hcard, hq⟩ :=
    CardinalNatural.Decimal.divide_toPeano x.magnitude y.magnitude
      (divisible_magnitude x y h)
  have hprod : y.magnitude.toPeano * q.toPeano = x.magnitude.toPeano := by
    rw [hq]
    exact CardinalNatural.Peano.multiply_divide
      x.magnitude.toPeano y.magnitude.toPeano hcard
  have hprod_abs :
      absoluteCardinalPeano y * q.toPeano = absoluteCardinalPeano x := by
    simpa [magnitude_toPeano] using hprod
  rw [hsigned]
  cases hx : isNegative x <;> cases hy : isNegative y
  · rw [toPeano_eq_fromCardinal_of_not_isNegative x hx,
      toPeano_eq_fromCardinal_of_not_isNegative y hy,
      ← Peano.fromCardinalNatural_multiply, hprod_abs]
  · have ⟨hy_peano, _⟩ := toPeano_eq_negate_fromCardinal_of_isNegative y hy
    rw [toPeano_eq_fromCardinal_of_not_isNegative x hx, hy_peano,
      Peano.negate_multiply_negate, ← Peano.fromCardinalNatural_multiply, hprod_abs]
  · have ⟨hx_peano, _⟩ := toPeano_eq_negate_fromCardinal_of_isNegative x hx
    rw [hx_peano, toPeano_eq_fromCardinal_of_not_isNegative y hy,
      Peano.multiply_negate, ← Peano.fromCardinalNatural_multiply, hprod_abs]
  · have ⟨hx_peano, _⟩ := toPeano_eq_negate_fromCardinal_of_isNegative x hx
    have ⟨hy_peano, _⟩ := toPeano_eq_negate_fromCardinal_of_isNegative y hy
    rw [hx_peano, hy_peano, Peano.negate_multiply,
      ← Peano.fromCardinalNatural_multiply, hprod_abs]

theorem exists_divide_of_tryDivide {x y z : Decimal} (h : tryDivide x y = some z) :
    ∃ h', divide x y h' = z := by
  cases hmag : CardinalNatural.Decimal.tryDivide x.magnitude y.magnitude with
  | none =>
      simp [tryDivide, hmag] at h
  | some q =>
      obtain ⟨hcard, _⟩ := CardinalNatural.Decimal.exists_divide_of_tryDivide hmag
      have hdiv : Divisible x y :=
        (isDivisible_correct x y).mpr
          ((CardinalNatural.Decimal.isDivisible_correct x.magnitude y.magnitude).mp
            hcard)
      refine ⟨hdiv, ?_⟩
      have hq :
          CardinalNatural.Decimal.divide x.magnitude y.magnitude
            (divisible_magnitude x y hdiv) = q := by
        have htry :=
          CardinalNatural.Decimal.tryDivide_of_divide
            (x := x.magnitude) (y := y.magnitude)
            ⟨divisible_magnitude x y hdiv, rfl⟩
        rw [hmag] at htry
        injection htry
      simp [tryDivide, divide, hmag, hq] at h ⊢
      exact h

theorem tryDivide_of_divide {x y z : Decimal} (h : ∃ h', divide x y h' = z) :
    tryDivide x y = some z := by
  obtain ⟨hdiv, heq⟩ := h
  have htry :
      CardinalNatural.Decimal.tryDivide x.magnitude y.magnitude =
        some (CardinalNatural.Decimal.divide x.magnitude y.magnitude
          (divisible_magnitude x y hdiv)) :=
    CardinalNatural.Decimal.tryDivide_of_divide
      ⟨divisible_magnitude x y hdiv, rfl⟩
  simp [tryDivide, divide, htry] at heq ⊢
  exact heq

/-- A successful `tryDivide` recovers the multiplicative relation `y * q ≈ x`. -/
theorem eq_of_tryDivide_multiply {x y q : Decimal} (h : tryDivide x y = some q) :
    y * q ≈ x := by
  obtain ⟨hdiv, heq⟩ := exists_divide_of_tryDivide h
  apply equivalent_of_toPeano_eq
  obtain ⟨h2, hdiv_eq⟩ := divide_toPeano x y hdiv
  rw [← heq, multiply_toPeano, hdiv_eq]
  exact Peano.divide_correct x.toPeano y.toPeano h2

/-- When `a ≈ b * q` and `b` is nonzero, `tryDivide a b` recovers a value
equivalent to `q`. -/
theorem tryDivide_of_equivalent_multiply {a b q : Decimal} (hb : ¬ b ≈ zero)
    (h : a ≈ b * q) :
    Option.Rel (· ≈ ·) (tryDivide a b) (some q) := by
  let hdiv : Divisible a b := ⟨hb, q, Setoid.symm h⟩
  have hquot : divide a b hdiv ≈ q := by
    apply equivalent_of_toPeano_eq
    obtain ⟨h2, hdiv_eq⟩ := divide_toPeano a b hdiv
    apply Peano.multiply_left_cancel b.toPeano (divide a b hdiv).toPeano q.toPeano
      (toPeano_ne_zero_of_not_equivalent_zero hb)
    rw [hdiv_eq, Peano.divide_correct a.toPeano b.toPeano h2,
      toPeano_eq_of_equivalent h, multiply_toPeano]
  have htry : tryDivide a b = some (divide a b hdiv) :=
    tryDivide_of_divide ⟨hdiv, rfl⟩
  rw [htry]
  exact Option.Rel.some hquot

/-- Dividing and then multiplying by the same nonzero divisor recovers the
original value up to decimal equivalence. -/
theorem multiply_divide_cancel (x y : Decimal) (h : Divisible x y) :
    (divide x y h) * y ≈ x := by
  apply equivalent_of_toPeano_eq
  obtain ⟨h2, hdiv⟩ := divide_toPeano x y h
  rw [multiply_toPeano, hdiv]
  exact Peano.multiply_divide_cancel x.toPeano y.toPeano h2

/-- If `z` divides `y`, then `z` also divides the product `x * y`. -/
theorem divide_multiply_h (x y z : Decimal) (h : Divisible y z) :
    Divisible (x * y) z := by
  apply (Divisible_toPeano (x * y) z).mpr
  rw [multiply_toPeano]
  exact Peano.divide_multiply_h x.toPeano y.toPeano z.toPeano
    ((Divisible_toPeano y z).mp h)

/-- Dividing a product by a divisor of the second factor recovers the product
of the first factor with that quotient. -/
theorem divide_multiply (x y z : Decimal) (h : Divisible y z) :
    ∃ h2, divide (x * y) z h2 ≈ x * divide y z h := by
  let h2 : Divisible (x * y) z := divide_multiply_h x y z h
  refine ⟨h2, ?_⟩
  apply equivalent_of_toPeano_eq
  obtain ⟨hy_div, hy⟩ := divide_toPeano y z h
  obtain ⟨hxy_div, hxy⟩ := divide_toPeano (x * y) z h2
  obtain ⟨h2_peano, hpeano⟩ :=
    Peano.divide_multiply x.toPeano y.toPeano z.toPeano hy_div
  apply Peano.multiply_left_cancel z.toPeano
    (divide (x * y) z h2).toPeano
    (x * divide y z h).toPeano
    hy_div.1
  calc
    z.toPeano * (divide (x * y) z h2).toPeano
        = z.toPeano * Peano.divide (x * y).toPeano z.toPeano hxy_div := by
          rw [hxy]
    _ = (x * y).toPeano :=
          Peano.divide_correct (x * y).toPeano z.toPeano hxy_div
    _ = x.toPeano * y.toPeano :=
          multiply_toPeano x y
    _ = z.toPeano * Peano.divide (x.toPeano * y.toPeano) z.toPeano h2_peano := by
          rw [Peano.divide_correct (x.toPeano * y.toPeano) z.toPeano h2_peano]
    _ = z.toPeano * (x.toPeano * Peano.divide y.toPeano z.toPeano hy_div) := by
          rw [hpeano]
    _ = z.toPeano * (x.toPeano * (divide y z h).toPeano) := by
          rw [hy]
    _ = z.toPeano * (x * divide y z h).toPeano := by
          rw [multiply_toPeano]

/-- If `y` divides `x` and `z` divides that quotient, then `y * z` divides `x`. -/
theorem divide_divide_h (x y z : Decimal) (h : Divisible x y)
    (h2 : Divisible (divide x y h) z) : Divisible x (y * z) := by
  apply (Divisible_toPeano x (y * z)).mpr
  rw [multiply_toPeano]
  obtain ⟨hy_div, hy⟩ := divide_toPeano x y h
  obtain ⟨hz_div, hz⟩ := divide_toPeano (divide x y h) z h2
  refine ⟨Peano.multiply_ne_zero hy_div.1 hz_div.1, (divide (divide x y h) z h2).toPeano, ?_⟩
  calc
    (y.toPeano * z.toPeano) * (divide (divide x y h) z h2).toPeano
        = y.toPeano * (z.toPeano * (divide (divide x y h) z h2).toPeano) := by
          rw [Peano.multiply_associative]
    _ = y.toPeano * (z.toPeano * Peano.divide (divide x y h).toPeano z.toPeano hz_div) := by
          rw [hz]
    _ = y.toPeano * (divide x y h).toPeano := by
          rw [Peano.divide_correct (divide x y h).toPeano z.toPeano hz_div]
    _ = y.toPeano * Peano.divide x.toPeano y.toPeano hy_div := by
          rw [hy]
    _ = x.toPeano :=
          Peano.divide_correct x.toPeano y.toPeano hy_div

/-- Dividing a quotient by a further divisor is equivalent to dividing by the
product of the two divisors. -/
theorem divide_divide (x y z : Decimal) (h : Divisible x y)
    (h2 : Divisible (divide x y h) z) :
    ∃ h3, divide (divide x y h) z h2 ≈ divide x (y * z) h3 := by
  let h3 : Divisible x (y * z) := divide_divide_h x y z h h2
  refine ⟨h3, ?_⟩
  apply equivalent_of_toPeano_eq
  obtain ⟨hy_div, hy⟩ := divide_toPeano x y h
  obtain ⟨hz_div, hz⟩ := divide_toPeano (divide x y h) z h2
  obtain ⟨hxyz_div, hxyz⟩ := divide_toPeano x (y * z) h3
  apply Peano.multiply_left_cancel (y * z).toPeano
    (divide (divide x y h) z h2).toPeano
    (divide x (y * z) h3).toPeano
    hxyz_div.1
  calc
    (y * z).toPeano * (divide (divide x y h) z h2).toPeano
        = (y.toPeano * z.toPeano) * (divide (divide x y h) z h2).toPeano := by
          rw [multiply_toPeano]
    _ = y.toPeano * (z.toPeano * (divide (divide x y h) z h2).toPeano) := by
          rw [Peano.multiply_associative]
    _ = y.toPeano * (z.toPeano * Peano.divide (divide x y h).toPeano z.toPeano hz_div) := by
          rw [hz]
    _ = y.toPeano * (divide x y h).toPeano := by
          rw [Peano.divide_correct (divide x y h).toPeano z.toPeano hz_div]
    _ = y.toPeano * Peano.divide x.toPeano y.toPeano hy_div := by
          rw [hy]
    _ = x.toPeano :=
          Peano.divide_correct x.toPeano y.toPeano hy_div
    _ = (y * z).toPeano * Peano.divide x.toPeano (y * z).toPeano hxyz_div := by
          rw [Peano.divide_correct x.toPeano (y * z).toPeano hxyz_div]
    _ = (y * z).toPeano * (divide x (y * z) h3).toPeano := by
          rw [hxyz]

/-- If `z` divides both `x` and `y`, then `z` also divides the sum `x + y`. -/
theorem divide_add_h (x y z : Decimal) (h : Divisible x z) (h2 : Divisible y z) :
    Divisible (x + y) z := by
  apply (Divisible_toPeano (x + y) z).mpr
  rw [add_toPeano]
  exact Peano.divide_add_h x.toPeano y.toPeano z.toPeano
    ((Divisible_toPeano x z).mp h)
    ((Divisible_toPeano y z).mp h2)

/-- Dividing a sum by a common divisor is equivalent to adding the individual
quotients. -/
theorem divide_add (x y z : Decimal) (h : Divisible x z) (h2 : Divisible y z) :
    ∃ h3, divide (x + y) z h3 ≈ divide x z h + divide y z h2 := by
  let h3 : Divisible (x + y) z := divide_add_h x y z h h2
  refine ⟨h3, ?_⟩
  apply equivalent_of_toPeano_eq
  obtain ⟨hx_div, hx⟩ := divide_toPeano x z h
  obtain ⟨hy_div, hy⟩ := divide_toPeano y z h2
  obtain ⟨hxy_div, hxy⟩ := divide_toPeano (x + y) z h3
  obtain ⟨h3_peano, hpeano⟩ :=
    Peano.divide_add x.toPeano y.toPeano z.toPeano hx_div hy_div
  apply Peano.multiply_left_cancel z.toPeano
    (divide (x + y) z h3).toPeano
    (divide x z h + divide y z h2).toPeano
    hx_div.1
  calc
    z.toPeano * (divide (x + y) z h3).toPeano
        = z.toPeano * Peano.divide (x + y).toPeano z.toPeano hxy_div := by
          rw [hxy]
    _ = (x + y).toPeano :=
          Peano.divide_correct (x + y).toPeano z.toPeano hxy_div
    _ = x.toPeano + y.toPeano :=
          add_toPeano x y
    _ = z.toPeano * Peano.divide (x.toPeano + y.toPeano) z.toPeano h3_peano := by
          rw [Peano.divide_correct (x.toPeano + y.toPeano) z.toPeano h3_peano]
    _ = z.toPeano * (Peano.divide x.toPeano z.toPeano hx_div +
          Peano.divide y.toPeano z.toPeano hy_div) := by
          rw [hpeano]
    _ = z.toPeano * ((divide x z h).toPeano + (divide y z h2).toPeano) := by
          rw [hx, hy]
    _ = z.toPeano * (divide x z h + divide y z h2).toPeano := by
          rw [add_toPeano]

/-- If `z` divides both `x` and `y`, then `z` also divides the difference `x - y`. -/
theorem divide_subtract_h (x y z : Decimal) (h : Divisible x z) (h2 : Divisible y z) :
    Divisible (x - y) z := by
  apply (Divisible_toPeano (x - y) z).mpr
  rw [subtract_toPeano]
  exact Peano.divide_subtract_h x.toPeano y.toPeano z.toPeano
    ((Divisible_toPeano x z).mp h)
    ((Divisible_toPeano y z).mp h2)

/-- Dividing a difference by a common divisor is equivalent to subtracting the
individual quotients. -/
theorem divide_subtract (x y z : Decimal) (h : Divisible x z) (h2 : Divisible y z) :
    ∃ h3, divide (x - y) z h3 ≈ divide x z h - divide y z h2 := by
  let h3 : Divisible (x - y) z := divide_subtract_h x y z h h2
  refine ⟨h3, ?_⟩
  apply equivalent_of_toPeano_eq
  obtain ⟨hx_div, hx⟩ := divide_toPeano x z h
  obtain ⟨hy_div, hy⟩ := divide_toPeano y z h2
  obtain ⟨hxy_div, hxy⟩ := divide_toPeano (x - y) z h3
  obtain ⟨h3_peano, hpeano⟩ :=
    Peano.divide_subtract x.toPeano y.toPeano z.toPeano hx_div hy_div
  apply Peano.multiply_left_cancel z.toPeano
    (divide (x - y) z h3).toPeano
    (divide x z h - divide y z h2).toPeano
    hx_div.1
  calc
    z.toPeano * (divide (x - y) z h3).toPeano
        = z.toPeano * Peano.divide (x - y).toPeano z.toPeano hxy_div := by
          rw [hxy]
    _ = (x - y).toPeano :=
          Peano.divide_correct (x - y).toPeano z.toPeano hxy_div
    _ = x.toPeano - y.toPeano :=
          subtract_toPeano x y
    _ = z.toPeano * Peano.divide (x.toPeano - y.toPeano) z.toPeano h3_peano := by
          rw [Peano.divide_correct (x.toPeano - y.toPeano) z.toPeano h3_peano]
    _ = z.toPeano * (Peano.divide x.toPeano z.toPeano hx_div -
          Peano.divide y.toPeano z.toPeano hy_div) := by
          rw [hpeano]
    _ = z.toPeano * ((divide x z h).toPeano - (divide y z h2).toPeano) := by
          rw [hx, hy]
    _ = z.toPeano * (divide x z h - divide y z h2).toPeano := by
          rw [subtract_toPeano]

/-- Dividing a left product by its nonzero left factor recovers the right factor. -/
theorem division_reverses_multiplication (x y : Decimal) (hy : ¬ y ≈ zero) :
    ∃ h, divide (y * x) y h ≈ x := by
  let h : Divisible (y * x) y := ⟨hy, x, rfl⟩
  refine ⟨h, ?_⟩
  apply equivalent_of_toPeano_eq
  obtain ⟨h2, hdiv⟩ := divide_toPeano (y * x) y h
  apply Peano.multiply_left_cancel y.toPeano
    (divide (y * x) y h).toPeano
    x.toPeano
    h2.1
  calc
    y.toPeano * (divide (y * x) y h).toPeano
        = y.toPeano * Peano.divide (y * x).toPeano y.toPeano h2 := by
          rw [hdiv]
    _ = (y * x).toPeano :=
          Peano.divide_correct (y * x).toPeano y.toPeano h2
    _ = y.toPeano * x.toPeano :=
          multiply_toPeano y x

theorem not_one_equivalent_zero : ¬ one ≈ zero := by
  intro h
  have hz : one.toPeano = Peano.zero :=
    (toPeano_eq_of_equivalent h).trans toPeano_zero
  rw [toPeano_one] at hz
  cases hz

theorem not_minusOne_equivalent_zero : ¬ minusOne ≈ zero := by
  intro h
  have hz : minusOne.toPeano = Peano.zero :=
    (toPeano_eq_of_equivalent h).trans toPeano_zero
  rw [toPeano_minusOne] at hz
  cases hz

theorem not_equivalent_zero_of_toPeano_ne_zero {x : Decimal}
    (hne : x.toPeano ≠ Peano.zero) : ¬ x ≈ zero := by
  intro heq
  exact hne ((toPeano_eq_of_equivalent heq).trans toPeano_zero)

theorem equivalent_zero_iff_toPeano_zero (x : Decimal) :
    x ≈ zero ↔ x.toPeano = Peano.zero := by
  constructor
  · intro h
    exact (toPeano_eq_of_equivalent h).trans toPeano_zero
  · intro h
    exact equivalent_of_toPeano_eq (h.trans toPeano_zero.symm)

theorem equivalent_one_iff_toPeano_one (x : Decimal) :
    x ≈ one ↔ x.toPeano = Peano.one := by
  constructor
  · intro h
    exact (toPeano_eq_of_equivalent h).trans toPeano_one
  · intro h
    exact equivalent_of_toPeano_eq (h.trans toPeano_one.symm)

theorem equivalent_minusOne_iff_toPeano_minusOne (x : Decimal) :
    x ≈ minusOne ↔ x.toPeano = Peano.minusOne := by
  constructor
  · intro h
    exact (toPeano_eq_of_equivalent h).trans toPeano_minusOne
  · intro h
    exact equivalent_of_toPeano_eq (h.trans toPeano_minusOne.symm)

theorem toPeano_negative_of_isNegative (x : Decimal) (h : isNegative x = true) :
    ∃ n, x.toPeano = Peano.negative n := by
  have ⟨heq, hne⟩ := toPeano_eq_negate_fromCardinal_of_isNegative x h
  cases habs : absoluteCardinalPeano x with
  | zero => exact False.elim (hne habs)
  | successor m =>
    refine ⟨CardinalNatural.Peano.toOrdinal m.successor
      (CardinalNatural.Peano.successor_ne_zero m), ?_⟩
    rw [heq, habs]
    rfl

theorem not_toPeano_negative_of_not_isNegative (x : Decimal)
    (h : isNegative x = false) (n : OrdinalNatural.Peano) :
    x.toPeano ≠ Peano.negative n := by
  rw [toPeano_eq_fromCardinal_of_not_isNegative x h]
  cases absoluteCardinalPeano x <;> intro h' <;> cases h'

theorem isNegative_eq_true_of_toPeano_negative {x : Decimal}
    {n : OrdinalNatural.Peano} (h : x.toPeano = Peano.negative n) :
    isNegative x = true := by
  cases hx : isNegative x with
  | true => rfl
  | false => exact False.elim (not_toPeano_negative_of_not_isNegative x hx n h)

theorem isOdd_iff_peano_odd (x : Decimal) :
    isOdd x = true ↔ Peano.Odd x.toPeano := by
  rw [← isOdd_correct, Odd_toPeano]

theorem isEven_iff_peano_even (x : Decimal) :
    isEven x = true ↔ Peano.Even x.toPeano := by
  rw [← isEven_correct, Even_toPeano]

theorem isEven_of_not_isOdd {x : Decimal} (h : isOdd x ≠ true) :
    isEven x = true := by
  cases hx : isEven x with
  | true => rfl
  | false =>
    have : isOdd x = true := by simp [isOdd, hx]
    exact False.elim (h this)

/-- Integer exponentiation is defined when the exponent is non-negative and the
pair is not `0 ^ 0`, or when the exponent is negative and the base is `±1`. -/
def ValidPowerCondition (a b : Decimal) : Bool :=
  if isNegative b then
    decide (a ≈ one ∨ a ≈ minusOne)
  else
    decide (¬ a ≈ zero ∨ ¬ b ≈ zero)

theorem validPowerCondition_one (e : Decimal) :
    ValidPowerCondition one e = true := by
  unfold ValidPowerCondition
  split
  · exact decide_eq_true (Or.inl (Setoid.refl one))
  · exact decide_eq_true (Or.inl not_one_equivalent_zero)

theorem validPowerCondition_minusOne (e : Decimal) :
    ValidPowerCondition minusOne e = true := by
  unfold ValidPowerCondition
  split
  · exact decide_eq_true (Or.inr (Setoid.refl minusOne))
  · exact decide_eq_true (Or.inl not_minusOne_equivalent_zero)

theorem validPowerCondition_magnitude (a b : Decimal)
    (h : ValidPowerCondition a b = true) :
    ¬ a.magnitude ≈ CardinalNatural.Decimal.zero ∨
      ¬ b.magnitude ≈ CardinalNatural.Decimal.zero := by
  unfold ValidPowerCondition at h
  split at h
  · have hunit : a ≈ one ∨ a ≈ minusOne := of_decide_eq_true h
    cases hunit with
    | inl hone =>
      exact Or.inl (magnitude_not_equivalent_zero_of_not_equivalent_zero
        (fun hz => not_one_equivalent_zero (Setoid.trans (Setoid.symm hone) hz)))
    | inr hminus =>
      exact Or.inl (magnitude_not_equivalent_zero_of_not_equivalent_zero
        (fun hz => not_minusOne_equivalent_zero (Setoid.trans (Setoid.symm hminus) hz)))
  · have hor : ¬ a ≈ zero ∨ ¬ b ≈ zero := of_decide_eq_true h
    cases hor with
    | inl ha =>
      exact Or.inl (magnitude_not_equivalent_zero_of_not_equivalent_zero ha)
    | inr hb =>
      exact Or.inr (magnitude_not_equivalent_zero_of_not_equivalent_zero hb)

theorem validPowerCondition_eq_peano (a b : Decimal) :
    ValidPowerCondition a b =
      Peano.ValidPowerCondition a.toPeano b.toPeano := by
  apply bool_eq_of_true_iff
  constructor
  · intro h
    cases hbneg : isNegative b with
    | true =>
      have h' : decide (a ≈ one ∨ a ≈ minusOne) = true := by
        simpa [ValidPowerCondition, hbneg] using h
      have hunit : a ≈ one ∨ a ≈ minusOne := of_decide_eq_true h'
      obtain ⟨n, hbn⟩ := toPeano_negative_of_isNegative b hbneg
      rw [hbn]
      cases hunit with
      | inl hone =>
        rw [Iff.mp (equivalent_one_iff_toPeano_one a) hone]
        rfl
      | inr hminus =>
        rw [Iff.mp (equivalent_minusOne_iff_toPeano_minusOne a) hminus]
        rfl
    | false =>
      have h' : decide (¬ a ≈ zero ∨ ¬ b ≈ zero) = true := by
        simpa [ValidPowerCondition, hbneg] using h
      have hor : ¬ a ≈ zero ∨ ¬ b ≈ zero := of_decide_eq_true h'
      cases hb : b.toPeano with
      | negative n =>
        exact False.elim (not_toPeano_negative_of_not_isNegative b hbneg n hb)
      | positive n => rfl
      | zero =>
        cases hor with
        | inl ha =>
          cases ha' : a.toPeano with
          | zero =>
            exact False.elim (toPeano_ne_zero_of_not_equivalent_zero ha ha')
          | positive _ => rfl
          | negative _ => rfl
        | inr hbne =>
          exact False.elim
            (hbne (Iff.mpr (equivalent_zero_iff_toPeano_zero b) hb))
  · intro h
    cases hbneg : isNegative b with
    | true =>
      obtain ⟨n, hbn⟩ := toPeano_negative_of_isNegative b hbneg
      have h' : Peano.ValidPowerCondition a.toPeano (Peano.negative n) = true := by
        rwa [hbn] at h
      simp [ValidPowerCondition, hbneg]
      cases ha : a.toPeano with
      | zero =>
        rw [ha] at h'
        exact False.elim (Bool.false_ne_true h')
      | positive k =>
        cases k with
        | one =>
          exact Or.inl (Iff.mpr (equivalent_one_iff_toPeano_one a) ha)
        | successor _ =>
          rw [ha] at h'
          exact False.elim (Bool.false_ne_true h')
      | negative k =>
        cases k with
        | one =>
          exact Or.inr (Iff.mpr (equivalent_minusOne_iff_toPeano_minusOne a) ha)
        | successor _ =>
          rw [ha] at h'
          exact False.elim (Bool.false_ne_true h')
    | false =>
      simp [ValidPowerCondition, hbneg]
      cases hb : b.toPeano with
      | negative n =>
        exact False.elim (not_toPeano_negative_of_not_isNegative b hbneg n hb)
      | positive _ =>
        exact Or.inr (not_equivalent_zero_of_toPeano_ne_zero
          (by rw [hb]; intro hz; cases hz))
      | zero =>
        have h' : Peano.ValidPowerCondition a.toPeano Peano.zero = true := by
          rwa [hb] at h
        cases ha : a.toPeano with
        | zero =>
          rw [ha] at h'
          exact False.elim (Bool.false_ne_true h')
        | positive _ =>
          exact Or.inl (not_equivalent_zero_of_toPeano_ne_zero
            (by rw [ha]; intro hz; cases hz))
        | negative _ =>
          exact Or.inl (not_equivalent_zero_of_toPeano_ne_zero
            (by rw [ha]; intro hz; cases hz))

/-- Wrap a cardinal decimal magnitude as a signed integer decimal. Zero
magnitude is always unsigned `zero`. -/
def ofSignedMagnitude (neg : Bool) (m : CardinalNatural.Decimal) : Decimal :=
  if AllZero m.val then
    zero
  else if neg then
    ⟨some Sign.minus, ⟨m.val, m.property⟩⟩
  else
    ⟨none, ⟨m.val, m.property⟩⟩

@[simp]
theorem ofSignedMagnitude_toPeano (neg : Bool) (m : CardinalNatural.Decimal) :
    (ofSignedMagnitude neg m).toPeano =
      if neg then
        -(Peano.fromCardinalNatural m.toPeano)
      else
        Peano.fromCardinalNatural m.toPeano := by
  unfold ofSignedMagnitude
  split
  · next hzero =>
    have hm0 : m.toPeano = CardinalNatural.Peano.zero :=
      toCardinalNaturalPeano_zero_of_allZero hzero
    rw [toPeano_zero, hm0]
    cases neg <;> rfl
  · next _hnz =>
    cases neg <;> rfl

/-- Exponentiation of decimal integers. Negative exponents are allowed only for
`±1`, where `a ^ (-n) = a ^ n`. The result is negative iff the base is negative
and the exponent is odd. -/
def power (a b : Decimal) (h : ValidPowerCondition a b = true) : Decimal :=
  ofSignedMagnitude (isNegative a && isOdd b)
    (CardinalNatural.Decimal.power a.magnitude b.magnitude
      (validPowerCondition_magnitude a b h))

theorem power_toPeano (x y : Decimal) (h : ValidPowerCondition x y = true) :
    ∃ h2, (power x y h).toPeano = Peano.power x.toPeano y.toPeano h2 := by
  have h2 : Peano.ValidPowerCondition x.toPeano y.toPeano = true := by
    rw [← validPowerCondition_eq_peano]
    exact h
  refine ⟨h2, ?_⟩
  unfold power
  rw [ofSignedMagnitude_toPeano]
  have hmag := validPowerCondition_magnitude x y h
  have hcard :
      x.magnitude.toPeano ≠ CardinalNatural.Peano.zero ∨
        y.magnitude.toPeano ≠ CardinalNatural.Peano.zero :=
    CardinalNatural.Decimal.power_condition_toPeano hmag
  have hmag_eq :
      (CardinalNatural.Decimal.power x.magnitude y.magnitude hmag).toPeano =
        CardinalNatural.Peano.power x.magnitude.toPeano y.magnitude.toPeano hcard :=
    CardinalNatural.Decimal.power_toPeano_eq x.magnitude y.magnitude hmag hcard
  simp only [magnitude_toPeano] at hcard hmag_eq
  rw [hmag_eq]
  revert h2
  generalize hy : y.toPeano = yp
  intro h2
  cases yp with
  | zero =>
    have hy0 : y ≈ zero := Iff.mpr (equivalent_zero_iff_toPeano_zero y) hy
    have hxne : ¬ x ≈ zero := by
      have hbnn : isNegative y = false := by
        cases hyn : isNegative y with
        | false => rfl
        | true =>
          obtain ⟨n, hn⟩ := toPeano_negative_of_isNegative y hyn
          rw [hy] at hn
          cases hn
      have h' : decide (¬ x ≈ zero ∨ ¬ y ≈ zero) = true := by
        simpa [ValidPowerCondition, hbnn] using h
      exact (of_decide_eq_true h').elim id (fun hyne => False.elim (hyne hy0))
    have hxabs : absoluteCardinalPeano x ≠ CardinalNatural.Peano.zero := by
      intro hx0
      exact toPeano_ne_zero_of_not_equivalent_zero hxne
        (toPeano_eq_zero_of_absoluteCardinal_zero hx0)
    have hyabs : absoluteCardinalPeano y = CardinalNatural.Peano.zero :=
      absoluteCardinalPeano_eq_of_toPeano_eq (hy.trans toPeano_zero.symm)
    have hodd : isOdd y = false := by
      have : Peano.Even y.toPeano := by
        rw [hy]
        exact Peano.isEven_zero
      have : isEven y = true := (isEven_iff_peano_even y).mpr this
      simp [isOdd, this]
    simp [hodd]
    have hpow := Peano.fromCardinalNatural_power_zero_exponent hxabs
    have hpow' :
        CardinalNatural.Peano.power (absoluteCardinalPeano x) (absoluteCardinalPeano y) hcard =
          CardinalNatural.Peano.power (absoluteCardinalPeano x) CardinalNatural.Peano.zero
            (Or.inl hxabs) :=
      CardinalNatural.Peano.eq_rec_power_exponent _ _ _ hyabs hcard (Or.inl hxabs)
    rw [hpow', hpow]
    exact (Peano.power_zero x.toPeano h2).symm
  | positive e =>
    have hyabs : absoluteCardinalPeano y = CardinalNatural.Peano.fromOrdinal e :=
      absoluteCardinalPeano_eq_fromOrdinal_of_toPeano_positive y e hy
    have hpow_exp :
        CardinalNatural.Peano.power (absoluteCardinalPeano x) (absoluteCardinalPeano y) hcard =
          CardinalNatural.Peano.power (absoluteCardinalPeano x)
            (CardinalNatural.Peano.fromOrdinal e)
            (Or.inr (CardinalNatural.Peano.fromOrdinal_ne_zero e)) :=
      CardinalNatural.Peano.eq_rec_power_exponent _ _ _ hyabs hcard _
    rw [hpow_exp]
    cases hx : x.toPeano with
    | zero =>
      have hxabs : absoluteCardinalPeano x = CardinalNatural.Peano.zero :=
        absoluteCardinalPeano_eq_of_toPeano_eq (hx.trans toPeano_zero.symm)
      have hnegx : isNegative x = false := by
        cases hxn : isNegative x with
        | false => rfl
        | true =>
          obtain ⟨n, hn⟩ := toPeano_negative_of_isNegative x hxn
          rw [hx] at hn
          cases hn
      simp [hnegx]
      have hpow := Peano.fromCardinalNatural_power_zero_base
        (CardinalNatural.Peano.fromOrdinal_ne_zero e)
      have hpow' :
          CardinalNatural.Peano.power (absoluteCardinalPeano x)
              (CardinalNatural.Peano.fromOrdinal e)
              (Or.inr (CardinalNatural.Peano.fromOrdinal_ne_zero e)) =
            CardinalNatural.Peano.power CardinalNatural.Peano.zero
              (CardinalNatural.Peano.fromOrdinal e)
              (Or.inr (CardinalNatural.Peano.fromOrdinal_ne_zero e)) :=
        CardinalNatural.Peano.eq_rec_power _ _ _ hxabs _ _
      rw [hpow', hpow]
      rfl
    | positive n =>
      have hxabs : absoluteCardinalPeano x = CardinalNatural.Peano.fromOrdinal n :=
        absoluteCardinalPeano_eq_fromOrdinal_of_toPeano_positive x n hx
      have hxne : absoluteCardinalPeano x ≠ CardinalNatural.Peano.zero := by
        rw [hxabs]
        exact CardinalNatural.Peano.fromOrdinal_ne_zero n
      have hnegx : isNegative x = false := by
        cases hxn : isNegative x with
        | false => rfl
        | true =>
          obtain ⟨k, hk⟩ := toPeano_negative_of_isNegative x hxn
          rw [hx] at hk
          cases hk
      simp [hnegx]
      have hpow := Peano.fromCardinalNatural_power_nonzero
        (absoluteCardinalPeano x) (CardinalNatural.Peano.fromOrdinal e) hxne
        (CardinalNatural.Peano.fromOrdinal_ne_zero e)
      have hpow' :
          CardinalNatural.Peano.power (absoluteCardinalPeano x)
              (CardinalNatural.Peano.fromOrdinal e)
              (Or.inr (CardinalNatural.Peano.fromOrdinal_ne_zero e)) =
            CardinalNatural.Peano.power (absoluteCardinalPeano x)
              (CardinalNatural.Peano.fromOrdinal e) (Or.inl hxne) :=
        CardinalNatural.Peano.eq_rec_power_exponent _ _ _ rfl _ _
      rw [hpow', hpow]
      have hord :
          CardinalNatural.Peano.toOrdinal (CardinalNatural.Peano.fromOrdinal e)
              (CardinalNatural.Peano.fromOrdinal_ne_zero e) = e :=
        CardinalNatural.Peano.toOrdinal_fromOrdinal_helper e _
      rw [hord, hxabs, Peano.fromCardinalNatural_fromOrdinal]
      change Peano.powerOrdinalExponent (Peano.positive n) e =
        Peano.power (Peano.positive n) (Peano.positive e) h2
      rw [Peano.power_positive_eq_powerOrdinalExponent]
    | negative n =>
      have hxabs : absoluteCardinalPeano x = CardinalNatural.Peano.fromOrdinal n :=
        absoluteCardinalPeano_eq_fromOrdinal_of_toPeano_negative x n hx
      have hxne : absoluteCardinalPeano x ≠ CardinalNatural.Peano.zero := by
        rw [hxabs]
        exact CardinalNatural.Peano.fromOrdinal_ne_zero n
      have hnegx : isNegative x = true := isNegative_eq_true_of_toPeano_negative hx
      have hpow := Peano.fromCardinalNatural_power_nonzero
        (absoluteCardinalPeano x) (CardinalNatural.Peano.fromOrdinal e) hxne
        (CardinalNatural.Peano.fromOrdinal_ne_zero e)
      have hpow' :
          CardinalNatural.Peano.power (absoluteCardinalPeano x)
              (CardinalNatural.Peano.fromOrdinal e)
              (Or.inr (CardinalNatural.Peano.fromOrdinal_ne_zero e)) =
            CardinalNatural.Peano.power (absoluteCardinalPeano x)
              (CardinalNatural.Peano.fromOrdinal e) (Or.inl hxne) :=
        CardinalNatural.Peano.eq_rec_power_exponent _ _ _ rfl _ _
      rw [hpow', hpow]
      have hord :
          CardinalNatural.Peano.toOrdinal (CardinalNatural.Peano.fromOrdinal e)
              (CardinalNatural.Peano.fromOrdinal_ne_zero e) = e :=
        CardinalNatural.Peano.toOrdinal_fromOrdinal_helper e _
      rw [hord, hxabs, Peano.fromCardinalNatural_fromOrdinal]
      change (if isNegative x && isOdd y then
          -(Peano.powerOrdinalExponent (Peano.positive n) e)
        else
          Peano.powerOrdinalExponent (Peano.positive n) e) =
        Peano.power (Peano.negative n) (Peano.positive e) h2
      rw [Peano.power_positive_eq_powerOrdinalExponent, hnegx]
      simp only [Bool.true_and]
      by_cases hodd : isOdd y = true
      · rw [if_pos (by simp [hodd])]
        have hoddP : Peano.Odd y.toPeano := Iff.mp (isOdd_iff_peano_odd y) hodd
        rw [hy] at hoddP
        rw [Peano.powerOrdinalExponent_positive_eq, Peano.powerOrdinalExponent_negative_eq_of_odd hoddP]
        rfl
      · rw [if_neg (by simp [hodd])]
        have hevenP : Peano.Even y.toPeano :=
          Iff.mp (isEven_iff_peano_even y) (isEven_of_not_isOdd hodd)
        rw [hy] at hevenP
        rw [Peano.powerOrdinalExponent_positive_eq, Peano.powerOrdinalExponent_negative_eq_of_even hevenP]
  | negative e =>
    have hyabs : absoluteCardinalPeano y = CardinalNatural.Peano.fromOrdinal e :=
      absoluteCardinalPeano_eq_fromOrdinal_of_toPeano_negative y e hy
    have hyneg : isNegative y = true := isNegative_eq_true_of_toPeano_negative hy
    have hunit : x ≈ one ∨ x ≈ minusOne := by
      have h' : decide (x ≈ one ∨ x ≈ minusOne) = true := by
        simpa [ValidPowerCondition, hyneg] using h
      exact of_decide_eq_true h'
    have hpow_exp :
        CardinalNatural.Peano.power (absoluteCardinalPeano x) (absoluteCardinalPeano y) hcard =
          CardinalNatural.Peano.power (absoluteCardinalPeano x)
            (CardinalNatural.Peano.fromOrdinal e)
            (Or.inr (CardinalNatural.Peano.fromOrdinal_ne_zero e)) :=
      CardinalNatural.Peano.eq_rec_power_exponent _ _ _ hyabs hcard _
    rw [hpow_exp]
    cases hunit with
    | inl hone =>
      have hx : x.toPeano = Peano.one := Iff.mp (equivalent_one_iff_toPeano_one x) hone
      have hxabs : absoluteCardinalPeano x = CardinalNatural.Peano.one :=
        absoluteCardinalPeano_eq_fromOrdinal_of_toPeano_positive x OrdinalNatural.Peano.one hx
      have hxne : absoluteCardinalPeano x ≠ CardinalNatural.Peano.zero := by
        rw [hxabs]
        exact CardinalNatural.Peano.successor_ne_zero _
      have hnegx : isNegative x = false := by
        cases hxn : isNegative x with
        | false => rfl
        | true =>
          obtain ⟨k, hk⟩ := toPeano_negative_of_isNegative x hxn
          rw [hx] at hk
          cases hk
      simp [hnegx]
      have hpow := Peano.fromCardinalNatural_power_nonzero
        (absoluteCardinalPeano x) (CardinalNatural.Peano.fromOrdinal e) hxne
        (CardinalNatural.Peano.fromOrdinal_ne_zero e)
      have hpow' :
          CardinalNatural.Peano.power (absoluteCardinalPeano x)
              (CardinalNatural.Peano.fromOrdinal e)
              (Or.inr (CardinalNatural.Peano.fromOrdinal_ne_zero e)) =
            CardinalNatural.Peano.power (absoluteCardinalPeano x)
              (CardinalNatural.Peano.fromOrdinal e) (Or.inl hxne) :=
        CardinalNatural.Peano.eq_rec_power_exponent _ _ _ rfl _ _
      rw [hpow', hpow]
      have hord :
          CardinalNatural.Peano.toOrdinal (CardinalNatural.Peano.fromOrdinal e)
              (CardinalNatural.Peano.fromOrdinal_ne_zero e) = e :=
        CardinalNatural.Peano.toOrdinal_fromOrdinal_helper e _
      rw [hord, hxabs, Peano.fromCardinalNatural_one]
      have h2' : Peano.ValidPowerCondition Peano.one (Peano.negative e) = true := by
        rw [hx] at h2
        exact h2
      calc
        Peano.powerOrdinalExponent Peano.one e = Peano.one := Peano.powerOrdinalExponent_one e
        _ = Peano.power Peano.one (Peano.negative e) h2' :=
          (Peano.power_one (Peano.negative e) h2').symm
        _ = Peano.power x.toPeano (Peano.negative e) h2 :=
          Peano.power_eq_of_base_eq hx.symm h2' h2
    | inr hminus =>
      have hx : x.toPeano = Peano.minusOne :=
        Iff.mp (equivalent_minusOne_iff_toPeano_minusOne x) hminus
      have hxabs : absoluteCardinalPeano x = CardinalNatural.Peano.one :=
        absoluteCardinalPeano_eq_fromOrdinal_of_toPeano_negative x OrdinalNatural.Peano.one hx
      have hxne : absoluteCardinalPeano x ≠ CardinalNatural.Peano.zero := by
        rw [hxabs]
        exact CardinalNatural.Peano.successor_ne_zero _
      have hnegx : isNegative x = true := isNegative_eq_true_of_toPeano_negative hx
      have hpow := Peano.fromCardinalNatural_power_nonzero
        (absoluteCardinalPeano x) (CardinalNatural.Peano.fromOrdinal e) hxne
        (CardinalNatural.Peano.fromOrdinal_ne_zero e)
      have hpow' :
          CardinalNatural.Peano.power (absoluteCardinalPeano x)
              (CardinalNatural.Peano.fromOrdinal e)
              (Or.inr (CardinalNatural.Peano.fromOrdinal_ne_zero e)) =
            CardinalNatural.Peano.power (absoluteCardinalPeano x)
              (CardinalNatural.Peano.fromOrdinal e) (Or.inl hxne) :=
        CardinalNatural.Peano.eq_rec_power_exponent _ _ _ rfl _ _
      rw [hpow', hpow]
      have hord :
          CardinalNatural.Peano.toOrdinal (CardinalNatural.Peano.fromOrdinal e)
              (CardinalNatural.Peano.fromOrdinal_ne_zero e) = e :=
        CardinalNatural.Peano.toOrdinal_fromOrdinal_helper e _
      rw [hord, hxabs, Peano.fromCardinalNatural_one]
      have h2' : Peano.ValidPowerCondition Peano.minusOne (Peano.negative e) = true := by
        rw [hx] at h2
        exact h2
      rw [hnegx]
      simp only [Bool.true_and]
      by_cases hodd : isOdd y = true
      · rw [if_pos (by simp [hodd])]
        have hoddP : Peano.Odd y.toPeano := Iff.mp (isOdd_iff_peano_odd y) hodd
        rw [hy] at hoddP
        rw [Peano.powerOrdinalExponent_one]
        change Peano.minusOne = Peano.power x.toPeano (Peano.negative e) h2
        calc
          Peano.minusOne = Peano.powerOrdinalExponent Peano.minusOne e :=
            (Peano.powerOrdinalExponent_minusOne_eq_of_odd_negative hoddP).symm
          _ = Peano.power Peano.minusOne (Peano.negative e) h2' :=
            (Peano.power_minusOne_negative e h2').symm
          _ = Peano.power x.toPeano (Peano.negative e) h2 :=
            Peano.power_eq_of_base_eq hx.symm h2' h2
      · rw [if_neg (by simp [hodd])]
        have hevenP : Peano.Even y.toPeano :=
          Iff.mp (isEven_iff_peano_even y) (isEven_of_not_isOdd hodd)
        rw [hy] at hevenP
        rw [Peano.powerOrdinalExponent_one]
        calc
          Peano.one = Peano.powerOrdinalExponent Peano.minusOne e :=
            (Peano.powerOrdinalExponent_minusOne_eq_of_even_negative hevenP).symm
          _ = Peano.power Peano.minusOne (Peano.negative e) h2' :=
            (Peano.power_minusOne_negative e h2').symm
          _ = Peano.power x.toPeano (Peano.negative e) h2 :=
            Peano.power_eq_of_base_eq hx.symm h2' h2

/-- `power_toPeano` with a chosen Peano-side condition. -/
theorem power_toPeano_eq (x y : Decimal) (h : ValidPowerCondition x y = true)
    (h2 : Peano.ValidPowerCondition x.toPeano y.toPeano = true) :
    (power x y h).toPeano = Peano.power x.toPeano y.toPeano h2 := by
  obtain ⟨h2', heq⟩ := power_toPeano x y h
  exact heq.trans (Peano.power_eq_of_exponent_eq rfl h2' h2)

theorem power_add (x y z : Decimal)
    (h : ValidPowerCondition x y = true) (h2 : ValidPowerCondition x z = true) :
    ∃ h3, power x (y + z) h3 ≈ power x y h * power x z h2 := by
  have hp : Peano.ValidPowerCondition x.toPeano y.toPeano = true := by
    rw [← validPowerCondition_eq_peano]
    exact h
  have hp2 : Peano.ValidPowerCondition x.toPeano z.toPeano = true := by
    rw [← validPowerCondition_eq_peano]
    exact h2
  obtain ⟨h3p, heq⟩ := Peano.power_add x.toPeano y.toPeano z.toPeano hp hp2
  have hsum : Peano.ValidPowerCondition x.toPeano (y + z).toPeano = true := by
    rw [add_toPeano]
    exact h3p
  have h3 : ValidPowerCondition x (y + z) = true := by
    rw [validPowerCondition_eq_peano]
    exact hsum
  refine ⟨h3, equivalent_of_toPeano_eq ?_⟩
  have hlhs : (power x (y + z) h3).toPeano =
      Peano.power x.toPeano (y.toPeano + z.toPeano) h3p :=
    (power_toPeano_eq x (y + z) h3 hsum).trans
      (Peano.power_eq_of_exponent_eq (add_toPeano y z) hsum h3p)
  rw [hlhs, multiply_toPeano, power_toPeano_eq x y h hp,
    power_toPeano_eq x z h2 hp2]
  exact heq

theorem power_multiply (x y z : Decimal)
    (h : ValidPowerCondition x y = true)
    (h2 : ValidPowerCondition (power x y h) z = true) :
    ∃ h3, power x (y * z) h3 ≈ power (power x y h) z h2 := by
  have hp : Peano.ValidPowerCondition x.toPeano y.toPeano = true := by
    rw [← validPowerCondition_eq_peano]
    exact h
  have hinner := power_toPeano_eq x y h hp
  have hp2 : Peano.ValidPowerCondition
      (Peano.power x.toPeano y.toPeano hp) z.toPeano = true := by
    have : Peano.ValidPowerCondition (power x y h).toPeano z.toPeano = true := by
      rw [← validPowerCondition_eq_peano]
      exact h2
    rwa [hinner] at this
  obtain ⟨h3p, heq⟩ := Peano.power_multiply x.toPeano y.toPeano z.toPeano hp hp2
  have hprod : Peano.ValidPowerCondition x.toPeano (y * z).toPeano = true := by
    rw [multiply_toPeano]
    exact h3p
  have h3 : ValidPowerCondition x (y * z) = true := by
    rw [validPowerCondition_eq_peano]
    exact hprod
  refine ⟨h3, equivalent_of_toPeano_eq ?_⟩
  have hlhs : (power x (y * z) h3).toPeano =
      Peano.power x.toPeano (y.toPeano * z.toPeano) h3p :=
    (power_toPeano_eq x (y * z) h3 hprod).trans
      (Peano.power_eq_of_exponent_eq (multiply_toPeano y z) hprod h3p)
  have hrhs : (power (power x y h) z h2).toPeano =
      Peano.power (Peano.power x.toPeano y.toPeano hp) z.toPeano hp2 :=
    (power_toPeano_eq (power x y h) z h2
      (by rw [← validPowerCondition_eq_peano]; exact h2)).trans
      (Peano.power_eq_of_base_eq hinner _ hp2)
  rw [hlhs, hrhs]
  exact heq

theorem multiply_power (x y z : Decimal)
    (h : ValidPowerCondition x z = true) (h2 : ValidPowerCondition y z = true) :
    ∃ h3, power (x * y) z h3 ≈ power x z h * power y z h2 := by
  have hp : Peano.ValidPowerCondition x.toPeano z.toPeano = true := by
    rw [← validPowerCondition_eq_peano]
    exact h
  have hp2 : Peano.ValidPowerCondition y.toPeano z.toPeano = true := by
    rw [← validPowerCondition_eq_peano]
    exact h2
  obtain ⟨h3p, heq⟩ := Peano.multiply_power x.toPeano y.toPeano z.toPeano hp hp2
  have hbase : Peano.ValidPowerCondition (x * y).toPeano z.toPeano = true := by
    rw [multiply_toPeano]
    exact h3p
  have h3 : ValidPowerCondition (x * y) z = true := by
    rw [validPowerCondition_eq_peano]
    exact hbase
  refine ⟨h3, equivalent_of_toPeano_eq ?_⟩
  have hlhs : (power (x * y) z h3).toPeano =
      Peano.power (x.toPeano * y.toPeano) z.toPeano h3p :=
    (power_toPeano_eq (x * y) z h3 hbase).trans
      (Peano.power_eq_of_base_eq (multiply_toPeano x y) hbase h3p)
  rw [hlhs, multiply_toPeano, power_toPeano_eq x z h hp,
    power_toPeano_eq y z h2 hp2]
  exact heq

/-- Transport a nonzero-or-nonzero integer decimal condition to cardinal
magnitudes, for use as a `CardinalNatural.Decimal.power` side-condition. -/
theorem power_condition_magnitude {a b : Decimal}
    (h : ¬ a ≈ zero ∨ ¬ b ≈ zero) :
    ¬ a.magnitude ≈ CardinalNatural.Decimal.zero ∨
      ¬ b.magnitude ≈ CardinalNatural.Decimal.zero :=
  h.elim
    (fun ha => Or.inl (magnitude_not_equivalent_zero_of_not_equivalent_zero ha))
    (fun hb => Or.inr (magnitude_not_equivalent_zero_of_not_equivalent_zero hb))

/-- Optional exponentiation of decimal integers, excluding `0 ^ 0`.
Non-negative exponents always succeed via signed cardinal magnitude power.
Negative exponents succeed iff `1` is divisible by `a ^ |b|`. The result is
negative iff the base is negative and the exponent is odd. -/
def tryPower (a b : Decimal) (h : ¬ a ≈ zero ∨ ¬ b ≈ zero) : Option Decimal :=
  let pos := ofSignedMagnitude (isNegative a && isOdd b)
    (CardinalNatural.Decimal.power a.magnitude b.magnitude
      (power_condition_magnitude h))
  if isNegative b then
    tryDivide one pos
  else
    some pos

theorem ne_zero_or_of_validPowerCondition {x y : Decimal}
    (h : ValidPowerCondition x y = true) : ¬ x ≈ zero ∨ ¬ y ≈ zero := by
  have hp : x.toPeano ≠ Peano.zero ∨ y.toPeano ≠ Peano.zero :=
    Peano.ne_zero_or_of_validPowerCondition
      (by rw [← validPowerCondition_eq_peano]; exact h)
  exact hp.elim
    (fun hx => Or.inl (not_equivalent_zero_of_toPeano_ne_zero hx))
    (fun hy => Or.inr (not_equivalent_zero_of_toPeano_ne_zero hy))

theorem validPowerCondition_of_not_isNegative {x y : Decimal}
    (hy : isNegative y = false) (h : ¬ x ≈ zero ∨ ¬ y ≈ zero) :
    ValidPowerCondition x y = true := by
  simp [ValidPowerCondition, hy]
  exact h

/-- `power` agrees with the signed cardinal magnitude used by `tryPower`. -/
theorem power_eq_tryPower_positive (x y : Decimal)
    (h : ValidPowerCondition x y = true)
    (h2 : ¬ x ≈ zero ∨ ¬ y ≈ zero) :
    power x y h =
      ofSignedMagnitude (isNegative x && isOdd y)
        (CardinalNatural.Decimal.power x.magnitude y.magnitude
          (power_condition_magnitude h2)) := by
  unfold power
  exact congrArg _ (CardinalNatural.Decimal.power_eq_of_condition
    (validPowerCondition_magnitude x y h) (power_condition_magnitude h2))

theorem tryDivide_toPeano_of_some {x y z : Decimal}
    (h : tryDivide x y = some z) :
    Peano.tryDivide x.toPeano y.toPeano = some z.toPeano := by
  obtain ⟨hdiv, heq⟩ := exists_divide_of_tryDivide h
  obtain ⟨h2, hpeano⟩ := divide_toPeano x y hdiv
  have htry := Peano.tryDivide_of_divide
    (x := x.toPeano) (y := y.toPeano) ⟨h2, rfl⟩
  rw [htry, ← hpeano, heq]

/-- Signed cardinal magnitude power with a nonzero exponent is `powerOrdinalExponent`. -/
theorem ofSignedMagnitude_power_toPeano_nonzero_exponent
    (x y : Decimal) (e : OrdinalNatural.Peano)
    (hmag : ¬ x.magnitude ≈ CardinalNatural.Decimal.zero ∨
      ¬ y.magnitude ≈ CardinalNatural.Decimal.zero)
    (hy : y.toPeano = Peano.positive e ∨ y.toPeano = Peano.negative e) :
    (ofSignedMagnitude (isNegative x && isOdd y)
      (CardinalNatural.Decimal.power x.magnitude y.magnitude hmag)).toPeano =
      Peano.powerOrdinalExponent x.toPeano e := by
  rw [ofSignedMagnitude_toPeano]
  have hcard :
      x.magnitude.toPeano ≠ CardinalNatural.Peano.zero ∨
        y.magnitude.toPeano ≠ CardinalNatural.Peano.zero :=
    CardinalNatural.Decimal.power_condition_toPeano hmag
  have hmag_eq :
      (CardinalNatural.Decimal.power x.magnitude y.magnitude hmag).toPeano =
        CardinalNatural.Peano.power x.magnitude.toPeano y.magnitude.toPeano hcard :=
    CardinalNatural.Decimal.power_toPeano_eq x.magnitude y.magnitude hmag hcard
  simp only [magnitude_toPeano] at hcard hmag_eq
  rw [hmag_eq]
  have hyabs : absoluteCardinalPeano y = CardinalNatural.Peano.fromOrdinal e := by
    cases hy with
    | inl hpos =>
      exact absoluteCardinalPeano_eq_fromOrdinal_of_toPeano_positive y e hpos
    | inr hneg =>
      exact absoluteCardinalPeano_eq_fromOrdinal_of_toPeano_negative y e hneg
  have hodd_iff : isOdd y = true ↔ Peano.Odd (Peano.positive e) := by
    rw [isOdd_iff_peano_odd]
    cases hy with
    | inl hpos => rw [hpos]
    | inr hneg =>
      rw [hneg]
      exact Peano.odd_negative_iff_odd_positive e
  have hpow_exp :
      CardinalNatural.Peano.power (absoluteCardinalPeano x) (absoluteCardinalPeano y) hcard =
        CardinalNatural.Peano.power (absoluteCardinalPeano x)
          (CardinalNatural.Peano.fromOrdinal e)
          (Or.inr (CardinalNatural.Peano.fromOrdinal_ne_zero e)) :=
    CardinalNatural.Peano.eq_rec_power_exponent _ _ _ hyabs hcard _
  rw [hpow_exp]
  cases hx : x.toPeano with
  | zero =>
    have hxabs : absoluteCardinalPeano x = CardinalNatural.Peano.zero :=
      absoluteCardinalPeano_eq_of_toPeano_eq (hx.trans toPeano_zero.symm)
    have hnegx : isNegative x = false := by
      cases hxn : isNegative x with
      | false => rfl
      | true =>
        obtain ⟨n, hn⟩ := toPeano_negative_of_isNegative x hxn
        rw [hx] at hn
        cases hn
    simp [hnegx]
    have hpow := Peano.fromCardinalNatural_power_zero_base
      (CardinalNatural.Peano.fromOrdinal_ne_zero e)
    have hpow' :
        CardinalNatural.Peano.power (absoluteCardinalPeano x)
            (CardinalNatural.Peano.fromOrdinal e)
            (Or.inr (CardinalNatural.Peano.fromOrdinal_ne_zero e)) =
          CardinalNatural.Peano.power CardinalNatural.Peano.zero
            (CardinalNatural.Peano.fromOrdinal e)
            (Or.inr (CardinalNatural.Peano.fromOrdinal_ne_zero e)) :=
      CardinalNatural.Peano.eq_rec_power _ _ _ hxabs _ _
    rw [hpow', hpow]
    exact (Peano.powerOrdinalExponent_zero_eq e).symm
  | positive n =>
    have hxabs : absoluteCardinalPeano x = CardinalNatural.Peano.fromOrdinal n :=
      absoluteCardinalPeano_eq_fromOrdinal_of_toPeano_positive x n hx
    have hxne : absoluteCardinalPeano x ≠ CardinalNatural.Peano.zero := by
      rw [hxabs]
      exact CardinalNatural.Peano.fromOrdinal_ne_zero n
    have hnegx : isNegative x = false := by
      cases hxn : isNegative x with
      | false => rfl
      | true =>
        obtain ⟨k, hk⟩ := toPeano_negative_of_isNegative x hxn
        rw [hx] at hk
        cases hk
    simp [hnegx]
    have hpow := Peano.fromCardinalNatural_power_nonzero
      (absoluteCardinalPeano x) (CardinalNatural.Peano.fromOrdinal e) hxne
      (CardinalNatural.Peano.fromOrdinal_ne_zero e)
    have hpow' :
        CardinalNatural.Peano.power (absoluteCardinalPeano x)
            (CardinalNatural.Peano.fromOrdinal e)
            (Or.inr (CardinalNatural.Peano.fromOrdinal_ne_zero e)) =
          CardinalNatural.Peano.power (absoluteCardinalPeano x)
            (CardinalNatural.Peano.fromOrdinal e) (Or.inl hxne) :=
      CardinalNatural.Peano.eq_rec_power_exponent _ _ _ rfl _ _
    rw [hpow', hpow]
    have hord :
        CardinalNatural.Peano.toOrdinal (CardinalNatural.Peano.fromOrdinal e)
            (CardinalNatural.Peano.fromOrdinal_ne_zero e) = e :=
      CardinalNatural.Peano.toOrdinal_fromOrdinal_helper e _
    rw [hord, hxabs, Peano.fromCardinalNatural_fromOrdinal]
  | negative n =>
    have hxabs : absoluteCardinalPeano x = CardinalNatural.Peano.fromOrdinal n :=
      absoluteCardinalPeano_eq_fromOrdinal_of_toPeano_negative x n hx
    have hxne : absoluteCardinalPeano x ≠ CardinalNatural.Peano.zero := by
      rw [hxabs]
      exact CardinalNatural.Peano.fromOrdinal_ne_zero n
    have hnegx : isNegative x = true := isNegative_eq_true_of_toPeano_negative hx
    have hpow := Peano.fromCardinalNatural_power_nonzero
      (absoluteCardinalPeano x) (CardinalNatural.Peano.fromOrdinal e) hxne
      (CardinalNatural.Peano.fromOrdinal_ne_zero e)
    have hpow' :
        CardinalNatural.Peano.power (absoluteCardinalPeano x)
            (CardinalNatural.Peano.fromOrdinal e)
            (Or.inr (CardinalNatural.Peano.fromOrdinal_ne_zero e)) =
          CardinalNatural.Peano.power (absoluteCardinalPeano x)
            (CardinalNatural.Peano.fromOrdinal e) (Or.inl hxne) :=
      CardinalNatural.Peano.eq_rec_power_exponent _ _ _ rfl _ _
    rw [hpow', hpow]
    have hord :
        CardinalNatural.Peano.toOrdinal (CardinalNatural.Peano.fromOrdinal e)
            (CardinalNatural.Peano.fromOrdinal_ne_zero e) = e :=
      CardinalNatural.Peano.toOrdinal_fromOrdinal_helper e _
    rw [hord, hxabs, Peano.fromCardinalNatural_fromOrdinal, hnegx]
    simp only [Bool.true_and]
    by_cases hoddB : isOdd y = true
    · rw [if_pos (by simp [hoddB])]
      have hoddP : Peano.Odd (Peano.positive e) := hodd_iff.mp hoddB
      rw [Peano.powerOrdinalExponent_positive_eq, Peano.powerOrdinalExponent_negative_eq_of_odd hoddP]
      rfl
    · rw [if_neg (by simp [hoddB])]
      have hevenP : Peano.Even (Peano.positive e) := by
        have hevenY : Peano.Even y.toPeano :=
          (isEven_iff_peano_even y).mp (isEven_of_not_isOdd hoddB)
        cases hy with
        | inl hpos =>
          rw [hpos] at hevenY
          exact hevenY
        | inr hneg =>
          rw [hneg] at hevenY
          exact (Peano.even_negative_iff_even_positive e).mp hevenY
      rw [Peano.powerOrdinalExponent_positive_eq, Peano.powerOrdinalExponent_negative_eq_of_even hevenP]

theorem exists_power_of_tryPower {x y z : Decimal}
    (h : ¬ x ≈ zero ∨ ¬ y ≈ zero)
    (htry : tryPower x y h = some z) :
    ∃ h2, power x y h2 ≈ z := by
  cases hy : isNegative y with
  | false =>
    have h2 : ValidPowerCondition x y = true :=
      validPowerCondition_of_not_isNegative hy h
    refine ⟨h2, equivalent_of_toPeano_eq ?_⟩
    have hpos :
        tryPower x y h =
          some (ofSignedMagnitude (isNegative x && isOdd y)
            (CardinalNatural.Decimal.power x.magnitude y.magnitude
              (power_condition_magnitude h))) := by
      simp [tryPower, hy]
    rw [hpos] at htry
    injection htry with hz
    rw [← hz, power_eq_tryPower_positive x y h2 h]
  | true =>
    obtain ⟨e, hyne⟩ := toPeano_negative_of_isNegative y hy
    have hpos :
        tryPower x y h =
          tryDivide one
            (ofSignedMagnitude (isNegative x && isOdd y)
              (CardinalNatural.Decimal.power x.magnitude y.magnitude
                (power_condition_magnitude h))) := by
      simp [tryPower, hy]
    rw [hpos] at htry
    have htry_peano :
        Peano.tryDivide Peano.one
          (Peano.powerOrdinalExponent x.toPeano e) = some z.toPeano := by
      have hdiv := tryDivide_toPeano_of_some htry
      rw [toPeano_one] at hdiv
      have hpow := ofSignedMagnitude_power_toPeano_nonzero_exponent x y e
        (power_condition_magnitude h) (Or.inr hyne)
      rwa [hpow] at hdiv
    have hcond : x.toPeano ≠ Peano.zero ∨ Peano.negative e ≠ Peano.zero :=
      Or.inr (fun hz => by cases hz)
    have htry' : Peano.tryPower x.toPeano (Peano.negative e) hcond =
        some z.toPeano := by
      rw [Peano.tryPower_negative, htry_peano]
    obtain ⟨hval, hpow⟩ := Peano.exists_power_of_tryPower hcond htry'
    have h2 : ValidPowerCondition x y = true := by
      rw [validPowerCondition_eq_peano, hyne]
      exact hval
    refine ⟨h2, equivalent_of_toPeano_eq ?_⟩
    obtain ⟨h3, hdec⟩ := power_toPeano x y h2
    rw [hdec]
    exact (Peano.power_eq_of_exponent_eq hyne h3 hval).trans hpow

theorem power_multiply_self_eq_one_of_valid_negative {x y : Decimal}
    (h : ValidPowerCondition x y = true) (hy : isNegative y = true) :
    (power x y h) * (power x y h) ≈ one := by
  apply equivalent_of_toPeano_eq
  rw [multiply_toPeano, toPeano_one]
  obtain ⟨e, hyne⟩ := toPeano_negative_of_isNegative y hy
  have hunit : x ≈ one ∨ x ≈ minusOne := of_decide_eq_true (by
    simpa [ValidPowerCondition, hy] using h)
  obtain ⟨hp, hpow⟩ := power_toPeano x y h
  have hpneg : Peano.ValidPowerCondition x.toPeano (Peano.negative e) = true := by
    rwa [hyne] at hp
  rw [hpow, Peano.power_eq_of_exponent_eq hyne hp hpneg]
  cases hunit with
  | inl hone =>
    have hx : x.toPeano = Peano.one :=
      Iff.mp (equivalent_one_iff_toPeano_one x) hone
    have hp' : Peano.ValidPowerCondition Peano.one (Peano.negative e) = true := by
      rwa [hx] at hpneg
    rw [Peano.power_eq_of_base_eq hx hpneg hp', Peano.power_one, Peano.one_multiply]
  | inr hminus =>
    have hx : x.toPeano = Peano.minusOne :=
      Iff.mp (equivalent_minusOne_iff_toPeano_minusOne x) hminus
    have hp' : Peano.ValidPowerCondition Peano.minusOne (Peano.negative e) =
        true := by
      rwa [hx] at hpneg
    rw [Peano.power_eq_of_base_eq hx hpneg hp', Peano.power_minusOne_negative]
    exact Peano.powerOrdinalExponent_minusOne_square e

theorem exists_tryPower_of_power {x y z : Decimal}
    (hpow : ∃ h, power x y h ≈ z) :
    ∃ h2, Option.Rel (· ≈ ·) (tryPower x y h2) (some z) := by
  obtain ⟨h, heq⟩ := hpow
  have h2 : ¬ x ≈ zero ∨ ¬ y ≈ zero := ne_zero_or_of_validPowerCondition h
  refine ⟨h2, ?_⟩
  cases hy : isNegative y with
  | false =>
    have htry : tryPower x y h2 = some (power x y h) := by
      simp [tryPower, hy]
      exact (power_eq_tryPower_positive x y h h2).symm
    rw [htry]
    exact Option.Rel.some heq
  | true =>
    have hb : ¬ power x y h ≈ zero := by
      intro hz
      have hsq := power_multiply_self_eq_one_of_valid_negative h hy
      have h00 : zero * zero ≈ zero :=
        equivalent_of_toPeano_eq (by
          rw [multiply_toPeano, toPeano_zero, Peano.multiply_zero])
      have hone0 : one ≈ zero :=
        Setoid.trans (Setoid.symm hsq)
          (Setoid.trans (equivalent_multiply hz hz) h00)
      exact not_one_equivalent_zero hone0
    have hone : one ≈ power x y h * z :=
      Setoid.trans (Setoid.symm (power_multiply_self_eq_one_of_valid_negative h hy))
        (equivalent_multiply (Setoid.refl _) heq)
    have hrel :=
      tryDivide_of_equivalent_multiply (a := one) (b := power x y h) (q := z) hb hone
    simp [tryPower, hy]
    rwa [← power_eq_tryPower_positive x y h h2]

/-- `a` is an `e`-th power when some allowed base `b` satisfies `power b e ≈ a`. -/
def Power (e a : Decimal) : Prop := ∃ b h, power b e h ≈ a

theorem Power_toPeano (e a : Decimal) :
    Power e a ↔ Peano.Power e.toPeano a.toPeano := by
  constructor
  · intro h
    rcases h with ⟨b, hb, heq⟩
    obtain ⟨h2, hpow⟩ := power_toPeano b e hb
    exact ⟨b.toPeano, h2, hpow.symm.trans (toPeano_eq_of_equivalent heq)⟩
  · intro h
    rcases h with ⟨b_peano, hb_peano, heq⟩
    let b := fromPeano b_peano
    have hb : ValidPowerCondition b e = true := by
      rw [validPowerCondition_eq_peano, toPeano_fromPeano]
      exact hb_peano
    obtain ⟨h2, hpow⟩ := power_toPeano b e hb
    exact ⟨b, hb, equivalent_of_toPeano_eq
      (hpow.trans
        ((Peano.power_eq_of_base_eq (toPeano_fromPeano b_peano) h2 hb_peano).trans
          heq))⟩

theorem isNegative_eq_false_of_toPeano_zero {x : Decimal}
    (h : x.toPeano = Peano.zero) : isNegative x = false := by
  cases hx : isNegative x with
  | false => rfl
  | true =>
    obtain ⟨n, hn⟩ := toPeano_negative_of_isNegative x hx
    rw [h] at hn
    cases hn

theorem isNegative_eq_false_of_toPeano_positive {x : Decimal}
    {n : OrdinalNatural.Peano} (h : x.toPeano = Peano.positive n) :
    isNegative x = false := by
  cases hx : isNegative x with
  | false => rfl
  | true =>
    obtain ⟨m, hm⟩ := toPeano_negative_of_isNegative x hx
    rw [h] at hm
    cases hm

theorem isOdd_eq_peano_isOdd (x : Decimal) :
    isOdd x = Peano.isOdd x.toPeano :=
  bool_eq_of_true_iff
    (Iff.trans (isOdd_iff_peano_odd x) (Peano.isOdd_correct x.toPeano))

theorem ofSignedMagnitude_toPeano_fromOrdinal (neg : Bool)
    (m : CardinalNatural.Decimal) (n : OrdinalNatural.Peano)
    (hm : m.toPeano = CardinalNatural.Peano.fromOrdinal n) :
    (ofSignedMagnitude neg m).toPeano =
      if neg then Peano.negative n else Peano.positive n := by
  rw [ofSignedMagnitude_toPeano, hm, Peano.fromCardinalNatural_fromOrdinal]
  cases neg <;> rfl

theorem ofSignedMagnitude_toPeano_zero_magnitude (neg : Bool)
    (m : CardinalNatural.Decimal)
    (hm : m.toPeano = CardinalNatural.Peano.zero) :
    (ofSignedMagnitude neg m).toPeano = Peano.zero := by
  rw [ofSignedMagnitude_toPeano, hm]
  cases neg <;> rfl

/-- Principal `e`-th root, or `none` when `e ≈ zero` or `a` is not an exact power.
Positive exponents use the cardinal magnitude root; the result is negative iff
`a` is negative (which requires an odd exponent). Negative exponents succeed
only for `±1`. -/
def tryPrincipalRoot (e a : Decimal) : Option Decimal :=
  if _ : e ≈ zero then
    none
  else if _ : isNegative e = true then
    if a ≈ one then
      some one
    else if a ≈ minusOne then
      if isOdd e then some minusOne else none
    else
      none
  else
    match CardinalNatural.Decimal.tryRoot e.magnitude a.magnitude with
    | none => none
    | some b =>
      if isNegative a then
        if isOdd e then some (ofSignedMagnitude true b) else none
      else
        some (ofSignedMagnitude false b)

theorem tryPrincipalRoot_of_equivalent_zero {e a : Decimal} (he : e ≈ zero) :
    tryPrincipalRoot e a = none := by
  simp only [tryPrincipalRoot, he, ↓reduceDIte]

theorem tryPrincipalRoot_of_negative_exponent {e a : Decimal} (he0 : ¬ e ≈ zero)
    (hneg : isNegative e = true) :
    tryPrincipalRoot e a =
      if a ≈ one then some one
      else if a ≈ minusOne then
        if isOdd e then some minusOne else none
      else none := by
  simp only [tryPrincipalRoot, he0, ↓reduceDIte, hneg]

theorem tryPrincipalRoot_of_nonNegative_exponent {e a : Decimal} (he0 : ¬ e ≈ zero)
    (hneg : isNegative e = false) :
    tryPrincipalRoot e a =
      match CardinalNatural.Decimal.tryRoot e.magnitude a.magnitude with
      | none => none
      | some b =>
        if isNegative a then
          if isOdd e then some (ofSignedMagnitude true b) else none
        else
          some (ofSignedMagnitude false b) := by
  have hne : ¬ isNegative e = true := by simp [hneg]
  simp only [tryPrincipalRoot, he0, ↓reduceDIte]
  exact dif_neg hne

theorem not_equivalent_one_of_toPeano_ne {x : Decimal}
    (h : x.toPeano ≠ Peano.one) : ¬ x ≈ one :=
  fun hx => h ((equivalent_one_iff_toPeano_one x).mp hx)

theorem not_equivalent_minusOne_of_toPeano_ne {x : Decimal}
    (h : x.toPeano ≠ Peano.minusOne) : ¬ x ≈ minusOne :=
  fun hx => h ((equivalent_minusOne_iff_toPeano_minusOne x).mp hx)

theorem tryPrincipalRoot_toPeano (e a : Decimal) :
    Option.map toPeano (tryPrincipalRoot e a) =
      Peano.tryPrincipalRoot e.toPeano a.toPeano := by
  cases he : e.toPeano with
  | zero =>
    have he0 : e ≈ zero := (equivalent_zero_iff_toPeano_zero e).mpr he
    rw [tryPrincipalRoot_of_equivalent_zero he0]
    change none = Peano.tryPrincipalRoot Peano.zero a.toPeano
    cases a.toPeano <;> rfl
  | positive e' =>
    have he0 : ¬ e ≈ zero :=
      not_equivalent_zero_of_toPeano_ne_zero (by rw [he]; intro hz; cases hz)
    have hnegE : isNegative e = false :=
      isNegative_eq_false_of_toPeano_positive he
    have habs_e : e.magnitude.toPeano = CardinalNatural.Peano.fromOrdinal e' := by
      rw [magnitude_toPeano]
      exact absoluteCardinalPeano_eq_fromOrdinal_of_toPeano_positive e e' he
    rw [tryPrincipalRoot_of_nonNegative_exponent he0 hnegE]
    cases ha : a.toPeano with
    | zero =>
      have hnegA : isNegative a = false := isNegative_eq_false_of_toPeano_zero ha
      have habs_a : a.magnitude.toPeano = CardinalNatural.Peano.zero := by
        rw [magnitude_toPeano]
        exact absoluteCardinalPeano_eq_of_toPeano_eq (ha.trans toPeano_zero.symm)
      have hcard := CardinalNatural.Decimal.tryRoot_toPeano e.magnitude a.magnitude
      rw [habs_e, habs_a,
        CardinalNatural.Peano.tryRoot_zero _
          (CardinalNatural.Peano.fromOrdinal_ne_zero e')] at hcard
      obtain ⟨b, hC, hb⟩ := option_map_eq_some hcard
      rw [hC, hnegA]
      change some (ofSignedMagnitude false b).toPeano =
        Peano.tryPrincipalRoot (Peano.positive e') Peano.zero
      rw [ofSignedMagnitude_toPeano_zero_magnitude false b hb]
      rfl
    | positive a' =>
      have hnegA : isNegative a = false :=
        isNegative_eq_false_of_toPeano_positive ha
      have habs_a : a.magnitude.toPeano =
          CardinalNatural.Peano.fromOrdinal a' := by
        rw [magnitude_toPeano]
        exact absoluteCardinalPeano_eq_fromOrdinal_of_toPeano_positive a a' ha
      have hcard := CardinalNatural.Decimal.tryRoot_toPeano e.magnitude a.magnitude
      rw [habs_e, habs_a, CardinalNatural.Peano.tryRoot_fromOrdinal] at hcard
      cases hord : OrdinalNatural.Peano.tryRoot e' a' with
      | none =>
        rw [hord] at hcard
        have hCnone := option_map_eq_none hcard
        rw [hCnone]
        change none =
          Option.map Peano.positive (OrdinalNatural.Peano.tryRoot e' a')
        rw [hord]
        rfl
      | some z =>
        rw [hord] at hcard
        obtain ⟨b, hC, hb⟩ := option_map_eq_some hcard
        rw [hC, hnegA]
        change some (ofSignedMagnitude false b).toPeano =
          Option.map Peano.positive (OrdinalNatural.Peano.tryRoot e' a')
        rw [ofSignedMagnitude_toPeano_fromOrdinal false b z hb, hord]
        rfl
    | negative a' =>
      have hnegA : isNegative a = true :=
        isNegative_eq_true_of_toPeano_negative ha
      have habs_a : a.magnitude.toPeano =
          CardinalNatural.Peano.fromOrdinal a' := by
        rw [magnitude_toPeano]
        exact absoluteCardinalPeano_eq_fromOrdinal_of_toPeano_negative a a' ha
      have hodd_eq : isOdd e = Peano.isOdd (Peano.positive e') := by
        rw [isOdd_eq_peano_isOdd, he]
      by_cases hodd : isOdd e = true
      · have hcard :=
          CardinalNatural.Decimal.tryRoot_toPeano e.magnitude a.magnitude
        rw [habs_e, habs_a, CardinalNatural.Peano.tryRoot_fromOrdinal] at hcard
        cases hord : OrdinalNatural.Peano.tryRoot e' a' with
        | none =>
          rw [hord] at hcard
          have hCnone := option_map_eq_none hcard
          rw [hCnone]
          change none =
            (if Peano.isOdd (Peano.positive e') then
              Option.map Peano.negative (OrdinalNatural.Peano.tryRoot e' a')
            else none)
          rw [← hodd_eq, hodd, hord]
          rfl
        | some z =>
          rw [hord] at hcard
          obtain ⟨b, hC, hb⟩ := option_map_eq_some hcard
          rw [hC, hnegA, hodd]
          change some (ofSignedMagnitude true b).toPeano =
            (if Peano.isOdd (Peano.positive e') then
              Option.map Peano.negative (OrdinalNatural.Peano.tryRoot e' a')
            else none)
          rw [ofSignedMagnitude_toPeano_fromOrdinal true b z hb, ← hodd_eq, hodd,
            hord]
          rfl
      · have hoddF : isOdd e = false := by
          cases hx : isOdd e with
          | true => exact False.elim (hodd hx)
          | false => rfl
        change
          Option.map toPeano
            (match CardinalNatural.Decimal.tryRoot e.magnitude a.magnitude with
            | none => none
            | some b =>
              if isNegative a then
                if isOdd e then some (ofSignedMagnitude true b) else none
              else some (ofSignedMagnitude false b)) =
            (if Peano.isOdd (Peano.positive e') then
              Option.map Peano.negative (OrdinalNatural.Peano.tryRoot e' a')
            else none)
        rw [← hodd_eq, hoddF]
        cases CardinalNatural.Decimal.tryRoot e.magnitude a.magnitude with
        | none => rfl
        | some b =>
          simp only [hnegA]
          rfl
  | negative e' =>
    have he0 : ¬ e ≈ zero :=
      not_equivalent_zero_of_toPeano_ne_zero (by rw [he]; intro hz; cases hz)
    have hnegE : isNegative e = true :=
      isNegative_eq_true_of_toPeano_negative he
    have hodd_eq : isOdd e = Peano.isOdd (Peano.negative e') := by
      rw [isOdd_eq_peano_isOdd, he]
    rw [tryPrincipalRoot_of_negative_exponent he0 hnegE]
    cases ha : a.toPeano with
    | zero =>
      have ha1 : ¬ a ≈ one :=
        not_equivalent_one_of_toPeano_ne (by rw [ha]; intro hz; cases hz)
      have haM1 : ¬ a ≈ minusOne :=
        not_equivalent_minusOne_of_toPeano_ne (by rw [ha]; intro hz; cases hz)
      simp only [ha1, haM1, ↓reduceIte]
      rfl
    | positive a' =>
      cases a' with
      | one =>
        have ha1 : a ≈ one :=
          (equivalent_one_iff_toPeano_one a).mpr (ha.trans toPeano_one.symm)
        simp only [ha1, ↓reduceIte]
        rfl
      | successor a'' =>
        have ha1 : ¬ a ≈ one :=
          not_equivalent_one_of_toPeano_ne (by rw [ha]; intro hz; cases hz)
        have haM1 : ¬ a ≈ minusOne :=
          not_equivalent_minusOne_of_toPeano_ne (by rw [ha]; intro hz; cases hz)
        simp only [ha1, haM1, ↓reduceIte]
        rfl
    | negative a' =>
      cases a' with
      | one =>
        have ha1 : ¬ a ≈ one :=
          not_equivalent_one_of_toPeano_ne (by rw [ha]; intro hz; cases hz)
        have haM1 : a ≈ minusOne :=
          (equivalent_minusOne_iff_toPeano_minusOne a).mpr
            (ha.trans toPeano_minusOne.symm)
        simp only [ha1, haM1, ↓reduceIte, hodd_eq]
        change
          Option.map toPeano
            (if Peano.isOdd (Peano.negative e') then some minusOne else none) =
            (if Peano.isOdd (Peano.negative e') then some Peano.minusOne else none)
        cases Peano.isOdd (Peano.negative e') <;> rfl
      | successor a'' =>
        have ha1 : ¬ a ≈ one :=
          not_equivalent_one_of_toPeano_ne (by rw [ha]; intro hz; cases hz)
        have haM1 : ¬ a ≈ minusOne :=
          not_equivalent_minusOne_of_toPeano_ne (by rw [ha]; intro hz; cases hz)
        simp only [ha1, haM1, ↓reduceIte]
        rfl

/-- Principal `e`-th root of an exact power `a`, for nonzero exponent `e`. -/
def principalRoot (e a : Decimal) (h : ¬ e ≈ zero ∧ Power e a) : Decimal :=
  match htry : tryPrincipalRoot e a with
  | some b => b
  | none =>
    False.elim (by
      have hmap := tryPrincipalRoot_toPeano e a
      have hsome := Peano.tryPrincipalRoot_eq_some_principalRoot e.toPeano a.toPeano
        ⟨toPeano_ne_zero_of_not_equivalent_zero h.1, (Power_toPeano e a).mp h.2⟩
      rw [htry] at hmap
      change none = Peano.tryPrincipalRoot e.toPeano a.toPeano at hmap
      rw [hsome] at hmap
      cases hmap)

theorem principalRoot_toPeano (e a : Decimal) (h : ¬ e ≈ zero ∧ Power e a) :
    ∃ h2, (principalRoot e a h).toPeano =
      Peano.principalRoot e.toPeano a.toPeano h2 := by
  let h2 : e.toPeano ≠ Peano.zero ∧ Peano.Power e.toPeano a.toPeano :=
    ⟨toPeano_ne_zero_of_not_equivalent_zero h.1, (Power_toPeano e a).mp h.2⟩
  refine ⟨h2, ?_⟩
  have hsome := Peano.tryPrincipalRoot_eq_some_principalRoot e.toPeano a.toPeano h2
  have hmap := tryPrincipalRoot_toPeano e a
  unfold principalRoot
  split
  · next b htry =>
    rw [htry] at hmap
    change some b.toPeano = Peano.tryPrincipalRoot e.toPeano a.toPeano at hmap
    rw [hsome] at hmap
    exact Option.some.inj hmap
  · next htry =>
    rw [htry] at hmap
    change none = Peano.tryPrincipalRoot e.toPeano a.toPeano at hmap
    rw [hsome] at hmap
    cases hmap

/-- Raising the extracted principal root to the exponent recovers `a`. -/
theorem principalRoot_correct (e a : Decimal) (h : ¬ e ≈ zero ∧ Power e a) :
    ∃ h2, power (principalRoot e a h) e h2 ≈ a := by
  obtain ⟨h2, hroot⟩ := principalRoot_toPeano e a h
  obtain ⟨hP, hpow⟩ := Peano.principalRoot_isPower e.toPeano a.toPeano h2
  have hP' : Peano.ValidPowerCondition
      (principalRoot e a h).toPeano e.toPeano = true := by
    rwa [hroot]
  have h2d : ValidPowerCondition (principalRoot e a h) e = true := by
    rwa [validPowerCondition_eq_peano]
  refine ⟨h2d, equivalent_of_toPeano_eq ?_⟩
  rw [power_toPeano_eq (principalRoot e a h) e h2d hP']
  exact (Peano.power_eq_of_base_eq hroot hP' hP).trans hpow

/-- The principal `e`-th root of `x ^ e` is equivalent to `x` when `e` is
nonzero and `x` is the principal choice: non-negative, or an odd exponent. -/
theorem principalRoot_power_eq (e x : Decimal) (he : ¬ e ≈ zero)
    (h2 : ValidPowerCondition x e = true)
    (hprin : ¬ x < zero ∨ Odd e) :
    ∃ h, principalRoot e (power x e h2) h ≈ x := by
  have heP : e.toPeano ≠ Peano.zero :=
    toPeano_ne_zero_of_not_equivalent_zero he
  have h2P : Peano.ValidPowerCondition x.toPeano e.toPeano = true := by
    rwa [← validPowerCondition_eq_peano]
  have hprinP : ¬ x.toPeano < Peano.zero ∨ Peano.Odd e.toPeano := by
    cases hprin with
    | inl hnn =>
      refine Or.inl ?_
      intro hlt
      have : x < zero := by
        change x.toPeano < zero.toPeano
        rwa [toPeano_zero]
      exact hnn this
    | inr hodd =>
      exact Or.inr ((Odd_toPeano e).mp hodd)
  obtain ⟨hP, heq⟩ :=
    Peano.principalRoot_power_eq e.toPeano x.toPeano heP h2P hprinP
  let h : ¬ e ≈ zero ∧ Power e (power x e h2) :=
    ⟨he, ⟨x, h2, rfl⟩⟩
  refine ⟨h, equivalent_of_toPeano_eq ?_⟩
  obtain ⟨h2', hroot⟩ := principalRoot_toPeano e (power x e h2) h
  have hpow : (power x e h2).toPeano =
      Peano.power x.toPeano e.toPeano h2P :=
    power_toPeano_eq x e h2 h2P
  have htrans :
      Peano.principalRoot e.toPeano (power x e h2).toPeano h2' =
        Peano.principalRoot e.toPeano
          (Peano.power x.toPeano e.toPeano h2P) hP :=
    Peano.principalRoot_eq_of_eq hpow h2' hP
  rw [hroot, htrans, heq]

theorem zero_le_absoluteValue (d : Decimal) : zero ≤ d.absoluteValue := by
  apply le_of_toPeano_le
  rw [toPeano_zero, absoluteValue_toPeano]
  cases d.toPeano with
  | zero =>
    simp only [Integer.Peano.absoluteValue]
    exact Or.inr rfl
  | positive _ =>
    simp only [Integer.Peano.absoluteValue]
    exact Or.inl Integer.Peano.LessThan.zero_less_than_positive
  | negative _ =>
    simp only [Integer.Peano.absoluteValue]
    exact Or.inl Integer.Peano.LessThan.zero_less_than_positive

/-- Cardinal place-value addends reinterpreted as non-negative integer decimals,
negated when `negative` is true. -/
def fromCardinalPlaceAddends (negative : Bool) :
    Sequences.List Numbers.CardinalNatural.Decimal → Sequences.List Decimal
  | Sequences.List.empty => Sequences.List.empty
  | Sequences.List.firstElement x xs =>
    Sequences.List.firstElement
      (if negative then -(fromCardinalNatural x) else fromCardinalNatural x)
      (fromCardinalPlaceAddends negative xs)

theorem fromCardinalPlaceAddends_ne_empty (negative : Bool)
    {l : Sequences.List Numbers.CardinalNatural.Decimal}
    (h : l ≠ Sequences.List.empty) :
    fromCardinalPlaceAddends negative l ≠ Sequences.List.empty := by
  cases l with
  | empty => exact False.elim (h rfl)
  | firstElement _ _ =>
    intro heq
    cases heq

/-- Place-value addends of an integer decimal, with the original sign. Zero
addends are omitted unless the number is zero. For `-347` this is
`[-300, -40, -7]`; for `-1005` this is `[-1000, -5]`. -/
def placeAddends (d : Decimal) : Sequences.List Decimal :=
  fromCardinalPlaceAddends (isNegative d)
    (Numbers.CardinalNatural.Decimal.placeAddends
      (toCardinalNatural d.absoluteValue (zero_le_absoluteValue d)))

theorem placeAddends_ne_empty (d : Decimal) :
    placeAddends d ≠ Sequences.List.empty :=
  fromCardinalPlaceAddends_ne_empty (isNegative d)
    (Numbers.CardinalNatural.Decimal.placeAddends_ne_empty _)

/-- Peano sum of a list of integer decimals, left to right. -/
def sumToPeano : Sequences.List Decimal → Peano
  | .empty => Peano.zero
  | .firstElement x xs => x.toPeano + sumToPeano xs

theorem sumToPeano_concatenate (a b : Sequences.List Decimal) :
    sumToPeano (Sequences.List.concatenate a b) =
      sumToPeano a + sumToPeano b := by
  induction a with
  | empty =>
    simp only [Sequences.List.concatenate, sumToPeano, Peano.zero_add]
  | firstElement x xs ih =>
    simp only [Sequences.List.concatenate, sumToPeano, ih, Peano.add_associative]

theorem fromCardinalPlaceAddends_sumToPeano_false :
    (l : Sequences.List Numbers.CardinalNatural.Decimal) →
    sumToPeano (fromCardinalPlaceAddends false l) =
      Peano.fromCardinalNatural
        (Numbers.CardinalNatural.Decimal.sumToPeano l)
  | .empty => rfl
  | .firstElement x xs => by
      have hcons :
          fromCardinalPlaceAddends false (Sequences.List.firstElement x xs) =
            Sequences.List.firstElement (fromCardinalNatural x)
              (fromCardinalPlaceAddends false xs) :=
        rfl
      rw [hcons, sumToPeano, Numbers.CardinalNatural.Decimal.sumToPeano,
        fromCardinalPlaceAddends_sumToPeano_false xs,
        fromCardinalNatural_toPeano, ← Peano.fromCardinalNatural_add]

theorem fromCardinalPlaceAddends_sumToPeano_true :
    (l : Sequences.List Numbers.CardinalNatural.Decimal) →
    sumToPeano (fromCardinalPlaceAddends true l) =
      -(Peano.fromCardinalNatural
        (Numbers.CardinalNatural.Decimal.sumToPeano l))
  | .empty => rfl
  | .firstElement x xs => by
      have hcons :
          fromCardinalPlaceAddends true (Sequences.List.firstElement x xs) =
            Sequences.List.firstElement (-fromCardinalNatural x)
              (fromCardinalPlaceAddends true xs) :=
        rfl
      rw [hcons, sumToPeano, Numbers.CardinalNatural.Decimal.sumToPeano,
        fromCardinalPlaceAddends_sumToPeano_true xs, negate_toPeano,
        fromCardinalNatural_toPeano, ← Peano.negate_add,
        ← Peano.fromCardinalNatural_add]

theorem absoluteCardinalPeano_absoluteValue (d : Decimal) :
    absoluteCardinalPeano d.absoluteValue = absoluteCardinalPeano d :=
  rfl

theorem toPeano_eq_sumToPeano_placeAddends (d : Decimal) :
    d.toPeano = sumToPeano (placeAddends d) := by
  unfold placeAddends
  have hmag :
      (toCardinalNatural d.absoluteValue (zero_le_absoluteValue d)).toPeano =
        absoluteCardinalPeano d := by
    rw [toCardinalNatural_toPeano]
    exact absoluteCardinalPeano_absoluteValue d
  have hsum :
      Numbers.CardinalNatural.Decimal.sumToPeano
          (Numbers.CardinalNatural.Decimal.placeAddends
            (toCardinalNatural d.absoluteValue (zero_le_absoluteValue d))) =
        absoluteCardinalPeano d :=
    (Numbers.CardinalNatural.Decimal.toPeano_eq_sumToPeano_placeAddends _).symm.trans
      hmag
  cases hneg : isNegative d with
  | true =>
      rw [fromCardinalPlaceAddends_sumToPeano_true, hsum]
      exact (toPeano_eq_negate_fromCardinal_of_isNegative d hneg).1
  | false =>
      rw [fromCardinalPlaceAddends_sumToPeano_false, hsum]
      exact toPeano_eq_fromCardinal_of_not_isNegative d hneg

/-- Sum of a non-empty list of integer decimals, left to right. -/
def addAll : (l : Sequences.List Decimal) → l ≠ Sequences.List.empty → Decimal
  | .empty, h => False.elim (h rfl)
  | .firstElement x .empty, _ => x
  | .firstElement x (.firstElement y ys), _ =>
      x + addAll (.firstElement y ys) (by intro heq; cases heq)

theorem addAll_singleton (x : Decimal) :
    addAll (.firstElement x .empty) (by simp) = x :=
  rfl

theorem addAll_firstElement_firstElement (x y : Decimal)
    (ys : Sequences.List Decimal) :
    addAll (.firstElement x (.firstElement y ys)) (by simp) =
      x + addAll (.firstElement y ys) (by intro heq; cases heq) :=
  rfl

theorem addAll_toPeano (l : Sequences.List Decimal) (h : l ≠ Sequences.List.empty) :
    (addAll l h).toPeano = sumToPeano l := by
  match l with
  | .empty => exact False.elim (h rfl)
  | .firstElement x .empty =>
    simp only [addAll, sumToPeano, Peano.add_zero]
  | .firstElement x (.firstElement y ys) =>
    rw [addAll_firstElement_firstElement, add_toPeano, sumToPeano]
    exact congrArg (fun s => x.toPeano + s)
      (addAll_toPeano (.firstElement y ys) (by intro heq; cases heq))

theorem toPeano_eq_addAll_placeAddends (d : Decimal) :
    d.toPeano = (addAll (placeAddends d) (placeAddends_ne_empty d)).toPeano := by
  rw [addAll_toPeano, toPeano_eq_sumToPeano_placeAddends]

/-- An integer decimal has the same value as the sum of its place-value
addends. -/
theorem equivalent_addAll_placeAddends (d : Decimal) :
    d ≈ addAll (placeAddends d) (placeAddends_ne_empty d) :=
  equivalent_of_toPeano_eq (toPeano_eq_addAll_placeAddends d)

/-- The written (normalized) form of an integer equals the written form of the
sum of its place-value addends. -/
theorem eq_addAll_placeAddends (d : Decimal) :
    d.normalize = (addAll (placeAddends d) (placeAddends_ne_empty d)).normalize :=
  equivalent_addAll_placeAddends d

/-- A normalized integer decimal equals the sum of its place-value addends when
that sum is also a normalized writing. -/
theorem eq_addAll_placeAddends_of_isNormalized (d : Decimal)
    (hd : d.isNormalized = true)
    (hs : (addAll (placeAddends d) (placeAddends_ne_empty d)).isNormalized = true) :
    d = addAll (placeAddends d) (placeAddends_ne_empty d) :=
  normalize_injective hd hs (toPeano_eq_addAll_placeAddends d)

/-- `count` copies of `addend`. Their sum is
`addend * fromCardinalNaturalPeano count`. -/
def repeatedAddends (addend : Decimal) (count : CardinalNatural.Peano) :
    Sequences.List Decimal :=
  Sequences.List.repeatValue addend count

theorem repeatedAddends_eq_repeatValue (addend : Decimal)
    (count : CardinalNatural.Peano) :
    repeatedAddends addend count = Sequences.List.repeatValue addend count :=
  rfl

theorem repeatedAddends_length (addend : Decimal)
    (count : CardinalNatural.Peano) :
    (repeatedAddends addend count).length = count :=
  Sequences.List.repeatValue_length addend count

theorem repeatedAddends_ne_empty (addend : Decimal)
    (count : CardinalNatural.Peano) (h : count ≠ CardinalNatural.Peano.zero) :
    repeatedAddends addend count ≠ Sequences.List.empty :=
  Sequences.List.repeatValue_ne_empty addend count h

theorem repeatedAddends_AllElements_toPeano (addend : Decimal)
    (count : CardinalNatural.Peano) :
    Sequences.List.AllElements (fun x => x.toPeano = addend.toPeano)
      (repeatedAddends addend count) := by
  induction count with
  | zero => exact Sequences.List.AllElements.empty
  | successor n ih =>
    exact Sequences.List.AllElements.firstElement addend
      (repeatedAddends addend n) rfl ih

theorem sumToPeano_eq_multiply_of_AllElements (addend : Decimal)
    (l : Sequences.List Decimal)
    (h : Sequences.List.AllElements (fun x => x.toPeano = addend.toPeano) l) :
    sumToPeano l = addend.toPeano * Peano.fromCardinalNatural l.length := by
  induction l with
  | empty =>
    simp only [sumToPeano, Sequences.List.length, Peano.fromCardinalNatural,
      Peano.multiply_zero]
  | firstElement x xs ih =>
    have hx := Sequences.List.AllElements.head h
    have hxs := Sequences.List.AllElements.tail h
    rw [sumToPeano, ih hxs, hx, Sequences.List.length_firstElement,
      Peano.fromCardinalNatural_successor, Peano.multiply_successor,
      Peano.add_commutative]

theorem sumToPeano_repeatedAddends (addend : Decimal)
    (count : CardinalNatural.Peano) :
    sumToPeano (repeatedAddends addend count) =
      addend.toPeano * Peano.fromCardinalNatural count := by
  rw [sumToPeano_eq_multiply_of_AllElements addend _
        (repeatedAddends_AllElements_toPeano addend count),
      repeatedAddends_length]

theorem toPeano_addAll_repeatedAddends (addend : Decimal)
    (count : CardinalNatural.Peano) (h : count ≠ CardinalNatural.Peano.zero) :
    (addAll (repeatedAddends addend count)
        (repeatedAddends_ne_empty addend count h)).toPeano =
      addend.toPeano * Peano.fromCardinalNatural count := by
  rw [addAll_toPeano, sumToPeano_repeatedAddends]

/-- Replacing a product with a sum of identical addends. -/
theorem equivalent_addAll_multiply (addend : Decimal)
    (count : CardinalNatural.Peano) (h : count ≠ CardinalNatural.Peano.zero) :
    addAll (repeatedAddends addend count)
        (repeatedAddends_ne_empty addend count h) ≈
      addend * fromCardinalNaturalPeano count :=
  equivalent_of_toPeano_eq (by
    rw [toPeano_addAll_repeatedAddends addend count h, multiply_toPeano,
      toPeano_fromCardinalNaturalPeano])

/-- Recover a product from a non-empty list of identical addends. -/
def tryProductFromAddends (l : Sequences.List Decimal) : Option Decimal :=
  match Sequences.List.tryRepeatedValue l with
  | some addend => some (addend * fromCardinalNaturalPeano l.length)
  | none => none

theorem tryProductFromAddends_repeatedAddends (addend : Decimal)
    (count : CardinalNatural.Peano) (h : count ≠ CardinalNatural.Peano.zero) :
    tryProductFromAddends (repeatedAddends addend count) =
      some (addend * fromCardinalNaturalPeano count) := by
  have htry :
      Sequences.List.tryRepeatedValue (repeatedAddends addend count) =
        some addend :=
    Sequences.List.tryRepeatedValue_repeatValue addend count h
  simp only [tryProductFromAddends, htry]
  exact congrArg some (congrArg (fun n => addend * fromCardinalNaturalPeano n)
    (repeatedAddends_length addend count))

instance : OfNat Decimal n where
  ofNat := fromPeano (Peano.fromNat n)

instance : ToString Decimal where
  toString d :=
    match d.sign with
    | some Sign.minus => "-" ++ Digits.listToString d.digits.val
    | some Sign.plus => "+" ++ Digits.listToString d.digits.val
    | none => Digits.listToString d.digits.val

instance : Repr Decimal where
  reprPrec d prec :=
    match d.sign with
    | none => toString d
    | some _ => Repr.addAppParen (toString d) prec

instance : ReprAtom Decimal := ⟨⟩

instance : BEq Decimal where
  beq a b := decide (a ≈ b)

instance : Ord Decimal where
  compare a b :=
    if a < b then Ordering.lt
    else if b < a then Ordering.gt
    else Ordering.eq

example : (0 : Decimal) = zero := rfl
example : (1 : Decimal) = one := rfl
example : (2 : Decimal) = two := rfl
example : toString (0 : Decimal) = "0" := rfl
example : toString minusOne = "-1" := rfl
example :
    let d : Decimal :=
      ⟨some Sign.minus,
        ⟨Sequences.List.firstElement zeroDigit Sequences.List.empty, by simp⟩⟩
    toString d = "-0" := rfl
example :
    let d : Decimal :=
      ⟨none,
        ⟨Sequences.List.firstElement zeroDigit
          (Sequences.List.firstElement oneDigit Sequences.List.empty), by simp⟩⟩
    toString d = "01" := rfl
example :
    let d : Decimal :=
      ⟨some Sign.plus,
        ⟨Sequences.List.firstElement oneDigit Sequences.List.empty, by simp⟩⟩
    toString d = "+1" := rfl
example :
    let d : Decimal :=
      ⟨some Sign.plus,
        ⟨Sequences.List.firstElement zeroDigit Sequences.List.empty, by simp⟩⟩
    toString d = "+0" := rfl
example : ((0 : Decimal) == (0 : Decimal)) = true := rfl
example : Ord.compare minusOne (0 : Decimal) = Ordering.lt := by decide

end Decimal

end ZeroMath.Numbers.Integer
