import ZeroMath.Numbers.CardinalNatural.Decimal
import ZeroMath.Numbers.CardinalNatural.Peano
import ZeroMath.Numbers.Digits.Decimal
import ZeroMath.Numbers.Digits.Decimal.Lists
import ZeroMath.Numbers.Integer.Peano
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
  hasNonZero_ne_empty hasNonZero hasNonZero_tail_of_zero_first NonEmptyList
  normalizeList normalizeList_eq_zero_of_allZero hasNonZero_normalizeList
  toCardinalNaturalPeano
  toCardinalNaturalPeano_acc_split toCardinalNaturalPeano_firstElement
  toCardinalNaturalPeano_padAtStart_zeroDigit
  toCardinalNaturalPeano_padAtStartToSameLength_fst
  toCardinalNaturalPeano_padAtStartToSameLength_snd
  toCardinalNaturalPeano_lt_tenPow
  LessThanAlignedLists_toCardinalNaturalPeano_lt
  LessThanAlignedLists_of_toCardinalNaturalPeano_lt
  toCardinalNaturalPeano_inj_sameLength toCardinalNaturalPeano_padAtEnd
  toCardinalNaturalPeano_addAlignedLists_result toCardinalNaturalPeano_addListDigit
  toCardinalNaturalPeano_multiplyDigitsPeano toCardinalNaturalPeano_multiplyDigits
  toCardinalNaturalPeano_addListDigit_multiplyDigits
  toCardinalNaturalPeano_multiplyListByDigit
  addPartialListDigit_spec addAlignedLists_spec
  multiplyPartialListByDigit_spec multiplyList_spec
  subtractAlignedLists_borrow_false_of_lessThan
  subtractAlignedLists_spec
  successor_carry_accumulator successorList_toCardinalNaturalPeano
  normalizeList_cons_zero
  toCardinalNaturalPeano_append
  toCardinalNaturalPeano_ne_zero_of_acc_ne_zero
  toCardinalNaturalPeano_ge_tenPow_of_ne_zero
  toCardinalNaturalPeano_zero_of_allZero toCardinalNaturalPeano_normalizeList
  allZero_or_hasNonZero not_allZero_of_hasNonZero
  toCardinalNaturalPeano_ne_zero_of_hasNonZero
  toCardinalNaturalPeano_ne_zero_of_not_allZero
  hasNonZero_of_toCardinalNaturalPeano_ne_zero
  predecessorList_successorList
  padAtStartToSameLength_fst_ne_empty padAtStartToSameLength_fst_ne_empty_of_either
  addAlignedLists_fst_ne_empty addAlignedLists_ne_empty
  subtractAlignedLists_fst_ne_empty subtractAlignedLists_ne_empty
  subtractAlignedLists_borrow_false_of_eq
  multiplyPartialListByDigit_fst_ne_empty multiplyListByDigit_ne_empty
  multiplyList_fst_ne_empty
  hasNonZero_of_hasNonZero_bool hasNonZero_bool_eq_true_of_hasNonZero
  allZero_of_not_hasNonZero_bool
  hasNonZero_of_successorList_carry_true hasNonZero_of_successorList_carry_false
  hasNonZero_padAtStartToSameLength_fst
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
  lessThanAlignedLists_padded_snd_fst_of_toCardinalNaturalPeano_lt
  padAtStartToSameLength_eq_of_toCardinalNaturalPeano_eq
  subtractAlignedLists_borrow_false_of_toCardinalNaturalPeano_eq
  subtractAlignedLists_borrow_true_of_toCardinalNaturalPeano_lt
  addLists addLists_of_aligned_result addLists_commutative
  addLists_ne_empty hasNonZero_addLists toCardinalNaturalPeano_addLists
  isLessThanLists subtractLists
  isLessThanLists_iff_toCardinalNaturalPeano_lt isLessThanLists_eq_false_iff_not_lt
  subtractLists_spec
  findQuotientDigitAux findQuotientDigit
  findQuotientDigitAux_spec findQuotientDigit_spec findQuotientDigit_nextRem_lt
  divideWithRemainderAux
  divideWithRemainderAux_newQuotient_value divideWithRemainderAux_step_algebra
  divideWithRemainderAux_spec
  empty_of_predecessorList_borrow_true_allZero successorList_spec
  toCardinalNaturalPeano_of_successorList
  not_allZero_normalizeList_of_not_allZero successorList_carry_false_of_allZero
  not_allZero_cons_zero_of_successorList_carry predecessorList_of_successorList_carry
  normalizeList_of_successorList_allZero
  toCardinalNaturalPeano_even_iff_lastElement
  toCardinalNaturalPeano_lt_ten_mul_tenPow
  leadingDigit_ne_zero_of_isNormalizedNonZeroList
  leadingDigit_ne_zero_of_isNormalizedList_ne_zero
  eq_zeroDigit_singleton_of_isNormalizedList_toCardinalNaturalPeano_zero
  toCardinalNaturalPeano_inj_of_leading_ne_zero
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

/-- Absolute magnitude of a decimal integer as a cardinal Peano natural. -/
def absCardinalPeano (a : Decimal) : CardinalNatural.Peano :=
  toCardinalNaturalPeano a.digits.val CardinalNatural.Peano.zero

/-- Convert a decimal integer to its Peano representation. -/
def toPeano (a : Decimal) : Peano :=
  let magnitude := Peano.fromCardinalNatural (absCardinalPeano a)
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

instance : Neg Decimal where
  neg := negate

/-- Absolute value of a decimal integer: drop the sign, keeping the same digits. -/
def absoluteValue (a : Decimal) : Decimal :=
  ⟨none, a.digits⟩

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

theorem toPeano_one : toPeano one = Peano.one := by
  rfl

theorem toPeano_zero : toPeano zero = Peano.zero := by
  rfl

theorem negate_toPeano (x : Decimal) : (-x).toPeano = -(x.toPeano) := by
  simp only [Neg.neg]
  unfold Decimal.negate
  split
  · next h_all =>
    have habs : absCardinalPeano x = CardinalNatural.Peano.zero := by
      simpa [absCardinalPeano] using toCardinalNaturalPeano_zero_of_allZero h_all
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
        simp only [toPeano, absCardinalPeano, hsign]
    | some s =>
        cases s with
        | plus =>
            simp only [toPeano, absCardinalPeano, hsign]
        | minus =>
            simp only [toPeano, absCardinalPeano, hsign]
            exact (Peano.neg_neg _).symm

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
            (toCardinalNaturalPeano a CardinalNatural.Peano.zero))
      | _ =>
          Peano.fromCardinalNatural
            (toCardinalNaturalPeano a CardinalNatural.Peano.zero) := by
  cases sign with
  | none =>
      exact toCardinalNaturalPeano_normalizeList a ha ▸ rfl
  | some s =>
      cases s with
      | plus =>
          exact toCardinalNaturalPeano_normalizeList a ha ▸ rfl
      | minus =>
          exact toCardinalNaturalPeano_normalizeList a ha ▸ rfl

theorem normalize_toPeano (x : Decimal) : x.normalize.toPeano = x.toPeano := by
  unfold normalize
  split
  · next hzero =>
      have hmag := toCardinalNaturalPeano_zero_of_allZero hzero
      rw [toCardinalNaturalPeano_normalizeList] at hmag
      rw [toPeano_zero]
      unfold toPeano absCardinalPeano
      rw [hmag]
      cases x.sign with
      | none => rfl
      | some s =>
          cases s with
          | plus => rfl
          | minus => rfl
  · next _hzero =>
      rw [toPeano_signed_normalizeList]
      unfold toPeano absCardinalPeano
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
theorem absCardinalPeano_lt_of_lessThanAlignedLists_padded {a b : Decimal}
    (h : LessThanAlignedLists
      (Sequences.List.padAtStartToSameLength a.digits.val b.digits.val zeroDigit).1
      (Sequences.List.padAtStartToSameLength a.digits.val b.digits.val zeroDigit).2
      (Sequences.List.padAtStartToSameLength_sameLength a.digits.val b.digits.val
        zeroDigit)) :
    absCardinalPeano a < absCardinalPeano b :=
  toCardinalNaturalPeano_lt_of_lessThanAlignedLists_padded a.digits.val b.digits.val h

theorem lessThanAlignedLists_padded_of_absCardinalPeano_lt {a b : Decimal}
    (h : absCardinalPeano a < absCardinalPeano b) :
    LessThanAlignedLists
      (Sequences.List.padAtStartToSameLength a.digits.val b.digits.val zeroDigit).1
      (Sequences.List.padAtStartToSameLength a.digits.val b.digits.val zeroDigit).2
      (Sequences.List.padAtStartToSameLength_sameLength a.digits.val b.digits.val
        zeroDigit) :=
  lessThanAlignedLists_padded_of_toCardinalNaturalPeano_lt a.digits.val b.digits.val h

theorem isMagnitudeLessThan_iff_abs_lt (x y : Decimal) :
    isMagnitudeLessThan x y ↔ absCardinalPeano x < absCardinalPeano y := by
  unfold isMagnitudeLessThan
  dsimp only
  constructor
  · intro h
    have h_aligned := (isLessThanAlignedLists_iff_lessThanAlignedLists _ _ _).mp h
    exact absCardinalPeano_lt_of_lessThanAlignedLists_padded h_aligned
  · intro h
    exact (isLessThanAlignedLists_iff_lessThanAlignedLists _ _ _).mpr
      (lessThanAlignedLists_padded_of_absCardinalPeano_lt h)

theorem absCardinalPeano_ne_zero_of_not_allZero {a : Decimal}
    (h : ¬ AllZero a.digits.val) :
    absCardinalPeano a ≠ CardinalNatural.Peano.zero := by
  simpa [absCardinalPeano] using toCardinalNaturalPeano_ne_zero_of_not_allZero h

theorem toPeano_eq_fromCardinal_of_not_isNegative (x : Decimal)
    (h : isNegative x = false) :
    x.toPeano = Peano.fromCardinalNatural (absCardinalPeano x) := by
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
              have habs : absCardinalPeano x = CardinalNatural.Peano.zero := by
                simpa [absCardinalPeano] using toCardinalNaturalPeano_zero_of_allZero h_all
              unfold toPeano
              rw [hsign, habs]
              rfl
          · cases h

theorem toPeano_eq_negate_fromCardinal_of_isNegative (x : Decimal)
    (h : isNegative x = true) :
    x.toPeano = -(Peano.fromCardinalNatural (absCardinalPeano x)) ∧
      absCardinalPeano x ≠ CardinalNatural.Peano.zero := by
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
              · exact absCardinalPeano_ne_zero_of_not_allZero h_not_all

theorem toPeano_lt_of_isNegative_not_isNegative {x y : Decimal}
    (hx : isNegative x = true) (hy : isNegative y = false) :
    x.toPeano < y.toPeano := by
  have ⟨hx_eq, hx_ne⟩ := toPeano_eq_negate_fromCardinal_of_isNegative x hx
  have hy_eq := toPeano_eq_fromCardinal_of_not_isNegative y hy
  rw [hx_eq, hy_eq]
  cases hxa : absCardinalPeano x with
  | zero => exact False.elim (hx_ne hxa)
  | successor n =>
      cases absCardinalPeano y with
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
            have habs : absCardinalPeano y < absCardinalPeano x :=
              (isMagnitudeLessThan_iff_abs_lt y x).mp h
            exact (Peano.negate_fromCardinalNatural_lt_iff hx_ne hy_ne).mpr habs
          · intro h
            have habs : absCardinalPeano y < absCardinalPeano x :=
              (Peano.negate_fromCardinalNatural_lt_iff hx_ne hy_ne).mp h
            exact (isMagnitudeLessThan_iff_abs_lt y x).mpr habs
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
              ((isMagnitudeLessThan_iff_abs_lt x y).mp h)
          · intro h
            exact (isMagnitudeLessThan_iff_abs_lt x y).mpr
              ((Peano.fromCardinalNatural_lt_iff _ _).mp h)

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

theorem lt_trans {x y z : Decimal} (h1 : x < y) (h2 : y < z) : x < z :=
  Peano.lt_trans h1 h2
theorem toPeano_absoluteValue_fromCardinal (x : Decimal) :
    x.toPeano.absoluteValue = Peano.fromCardinalNatural (absCardinalPeano x) := by
  unfold toPeano
  cases x.sign with
  | none =>
      cases absCardinalPeano x with
      | zero => rfl
      | successor _ => rfl
  | some s =>
      cases s with
      | plus =>
          cases absCardinalPeano x with
          | zero => rfl
          | successor _ => rfl
      | minus =>
          cases absCardinalPeano x with
          | zero => rfl
          | successor _ => rfl

theorem absCardinalPeano_eq_of_toPeano_eq {a b : Decimal}
    (h : a.toPeano = b.toPeano) : absCardinalPeano a = absCardinalPeano b := by
  apply Peano.fromCardinalNatural_inj
  rw [← toPeano_absoluteValue_fromCardinal a, ← toPeano_absoluteValue_fromCardinal b, h]

theorem absCardinalPeano_ne_zero_of_normalized_minus (d : Decimal)
    (hsign : d.sign = some Sign.minus) (hnorm : d.isNormalized = true) :
    absCardinalPeano d ≠ CardinalNatural.Peano.zero := by
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
              exact absCardinalPeano_ne_zero_of_not_allZero (fun h => hne h.1)

theorem toPeano_ne_negative_of_sign_none (x : Decimal) (h : x.sign = none)
    (n : OrdinalNatural.Peano) : x.toPeano ≠ Peano.negative n := by
  unfold toPeano
  rw [h]
  cases absCardinalPeano x with
  | zero => intro h'; cases h'
  | successor _ => intro h'; cases h'

theorem toPeano_eq_negative_of_normalized_minus (x : Decimal)
    (hsign : x.sign = some Sign.minus) (hnorm : x.isNormalized = true) :
    ∃ n, x.toPeano = Peano.negative n := by
  have hne := absCardinalPeano_ne_zero_of_normalized_minus x hsign hnorm
  cases h : absCardinalPeano x with
  | zero => exact False.elim (hne h)
  | successor m =>
      refine ⟨CardinalNatural.Peano.toOrdinal (CardinalNatural.Peano.successor m)
        (CardinalNatural.Peano.successor_ne_zero m), ?_⟩
      unfold toPeano
      rw [hsign, h]
      rfl

theorem eq_zero_of_normalized_absCardinalPeano_zero {d : Decimal}
    (hd : d.isNormalized = true)
    (h : absCardinalPeano d = CardinalNatural.Peano.zero) : d = zero := by
  cases d with
  | mk sign digits =>
      cases sign with
      | none =>
          cases digits with
          | mk val hprop =>
              have hlist :
                  val = Sequences.List.firstElement zeroDigit Sequences.List.empty := by
                simpa [absCardinalPeano, isNormalized] using
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
                (absCardinalPeano_ne_zero_of_normalized_minus
                  ⟨some Sign.minus, digits⟩ rfl hd h)

theorem leadingDigit_ne_zero_of_normalized_ne_zero_abs
    {sign : Option Sign} {digit : Digit} {rest : Sequences.List Digit}
    {hprop : Sequences.List.firstElement digit rest ≠ Sequences.List.empty}
    (hnorm : isNormalized ⟨sign, ⟨Sequences.List.firstElement digit rest, hprop⟩⟩ = true)
    (hne_abs :
      absCardinalPeano ⟨sign, ⟨Sequences.List.firstElement digit rest, hprop⟩⟩ ≠
        CardinalNatural.Peano.zero) :
    digit.val ≠ CardinalNatural.Peano.zero := by
  cases sign with
  | none =>
      exact leadingDigit_ne_zero_of_isNormalizedList_ne_zero
        (by simpa [isNormalized] using hnorm)
        (by simpa [absCardinalPeano] using hne_abs)
  | some s =>
      cases s with
      | plus =>
          simp only [isNormalized] at hnorm
          cases hnorm
      | minus =>
          exact leadingDigit_ne_zero_of_isNormalizedNonZeroList
            (by simpa [isNormalized] using hnorm)

theorem digits_val_eq_of_normalized_absCardinalPeano_eq
    {a b : Decimal}
    (ha : a.isNormalized = true) (hb : b.isNormalized = true)
    (heq : absCardinalPeano a = absCardinalPeano b)
    (ha0 : absCardinalPeano a ≠ CardinalNatural.Peano.zero) :
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
                          exact toCardinalNaturalPeano_inj_of_leading_ne_zero
                            (leadingDigit_ne_zero_of_normalized_ne_zero_abs ha ha0)
                            (leadingDigit_ne_zero_of_normalized_ne_zero_abs hb
                              (by intro h; exact ha0 (heq.trans h)))
                            (by simpa [absCardinalPeano] using heq)

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

theorem normalize_inj {a b : Decimal}
    (ha : a.isNormalized = true) (hb : b.isNormalized = true)
    (heq : a.toPeano = b.toPeano) : a = b := by
  have habs := absCardinalPeano_eq_of_toPeano_eq heq
  have hsign := sign_eq_of_normalized_toPeano_eq ha hb heq
  by_cases ha0 : absCardinalPeano a = CardinalNatural.Peano.zero
  · have hb0 : absCardinalPeano b = CardinalNatural.Peano.zero :=
      habs.symm.trans ha0
    rw [eq_zero_of_normalized_absCardinalPeano_zero ha ha0,
      eq_zero_of_normalized_absCardinalPeano_zero hb hb0]
  · have hdigits_val :=
      digits_val_eq_of_normalized_absCardinalPeano_eq ha hb habs ha0
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
  exact normalize_inj (normalize_isNormalized a) (normalize_isNormalized b)
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

theorem successor_toPeano_none (x : Decimal) (hsign : x.sign = none) :
    x.successor.toPeano = x.toPeano.successor := by
  have hx : toPeano x = Peano.fromCardinalNatural (absCardinalPeano x) := by
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
              (toCardinalNaturalPeano
                (Sequences.List.firstElement
                  ⟨CardinalNatural.Peano.one, CardinalNatural.Peano.one_lt_ten⟩ digits)
                CardinalNatural.Peano.zero) =
            (Peano.fromCardinalNatural (absCardinalPeano x)).successor
          have habs :
              toCardinalNaturalPeano
                  (Sequences.List.firstElement
                    ⟨CardinalNatural.Peano.one, CardinalNatural.Peano.one_lt_ten⟩ digits)
                  CardinalNatural.Peano.zero =
                (absCardinalPeano x).successor := by
            simpa [absCardinalPeano, toCardinalNaturalPeano,
              CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.zero_add] using h_list
          rw [habs, Peano.fromCardinalNatural_successor]
      · next digits hsucc =>
          have h_list := toCardinalNaturalPeano_of_successorList x.digits.val
          rw [hsucc] at h_list
          dsimp only at h_list
          rw [hx]
          change Peano.fromCardinalNatural
              (toCardinalNaturalPeano digits CardinalNatural.Peano.zero) =
            (Peano.fromCardinalNatural (absCardinalPeano x)).successor
          have habs :
              toCardinalNaturalPeano digits CardinalNatural.Peano.zero =
                (absCardinalPeano x).successor := by
            simpa [absCardinalPeano] using h_list
          rw [habs, Peano.fromCardinalNatural_successor]

theorem successor_toPeano_plus (x : Decimal) (hsign : x.sign = some Sign.plus) :
    x.successor.toPeano = x.toPeano.successor := by
  have hx : toPeano x = Peano.fromCardinalNatural (absCardinalPeano x) := by
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
              (toCardinalNaturalPeano
                (Sequences.List.firstElement
                  ⟨CardinalNatural.Peano.one, CardinalNatural.Peano.one_lt_ten⟩ digits)
                CardinalNatural.Peano.zero) =
            (Peano.fromCardinalNatural (absCardinalPeano x)).successor
          have habs :
              toCardinalNaturalPeano
                  (Sequences.List.firstElement
                    ⟨CardinalNatural.Peano.one, CardinalNatural.Peano.one_lt_ten⟩ digits)
                  CardinalNatural.Peano.zero =
                (absCardinalPeano x).successor := by
            simpa [absCardinalPeano, toCardinalNaturalPeano,
              CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.zero_add] using h_list
          rw [habs, Peano.fromCardinalNatural_successor]
      · next digits hsucc =>
          have h_list := toCardinalNaturalPeano_of_successorList x.digits.val
          rw [hsucc] at h_list
          dsimp only at h_list
          rw [hx]
          change Peano.fromCardinalNatural
              (toCardinalNaturalPeano digits CardinalNatural.Peano.zero) =
            (Peano.fromCardinalNatural (absCardinalPeano x)).successor
          have habs :
              toCardinalNaturalPeano digits CardinalNatural.Peano.zero =
                (absCardinalPeano x).successor := by
            simpa [absCardinalPeano] using h_list
          rw [habs, Peano.fromCardinalNatural_successor]

theorem successor_toPeano_minus (x : Decimal) (hsign : x.sign = some Sign.minus) :
    x.successor.toPeano = x.toPeano.successor := by
  have hx_toPeano :
      toPeano x = Peano.negate (Peano.fromCardinalNatural (absCardinalPeano x)) := by
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
          have habs : absCardinalPeano x = CardinalNatural.Peano.zero := by
            simpa [absCardinalPeano] using toCardinalNaturalPeano_zero_of_allZero h_all
          have hx_peano : toPeano x = Peano.zero := by
            rw [hx_toPeano, habs]; rfl
          rw [toPeano_one, hx_peano]; rfl
      · next digits hpred =>
          have h_succ_pred : successorList digits = ⟨x.digits.val, false⟩ := by
            have h := successorList_predecessorList x.digits.val
            simpa [hpred] using h
          have h_abs :
              absCardinalPeano x =
                (toCardinalNaturalPeano digits CardinalNatural.Peano.zero).successor := by
            have hsucc :=
              successorList_toCardinalNaturalPeano digits CardinalNatural.Peano.zero
            rw [h_succ_pred] at hsucc
            dsimp only at hsucc
            simpa [absCardinalPeano] using hsucc
          split
          · next h_zero =>
              have hdigits0 := toCardinalNaturalPeano_zero_of_allZero h_zero
              have habs : absCardinalPeano x = CardinalNatural.Peano.one := by
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
                        (toCardinalNaturalPeano digits CardinalNatural.Peano.zero)) := by
                simp only [toPeano, absCardinalPeano]
              have hx_peano :
                  toPeano x =
                    Peano.negate
                      (Peano.successor
                        (Peano.fromCardinalNatural
                          (toCardinalNaturalPeano digits CardinalNatural.Peano.zero))) := by
                rw [hx_toPeano, h_abs, Peano.fromCardinalNatural_successor]
              rw [h_left, hx_peano]
              symm
              exact
                (congrArg Peano.successor
                  (Peano.neg_succ
                    (Peano.fromCardinalNatural
                      (toCardinalNaturalPeano digits CardinalNatural.Peano.zero)))).trans
                  (Peano.succ_pred _)
  · next sign h_ne =>
      exact False.elim (h_ne rfl)

theorem successor_toPeano (x : Decimal) :
    x.successor.toPeano = x.toPeano.successor := by
  cases hsign : x.sign with
  | none => exact successor_toPeano_none x hsign
  | some s =>
      cases s with
      | plus => exact successor_toPeano_plus x hsign
      | minus => exact successor_toPeano_minus x hsign

theorem toPeano_minusOne : toPeano minusOne = Peano.minusOne := by
  rfl

theorem predecessor_toPeano_none (x : Decimal) (hsign : x.sign = none) :
    x.predecessor.toPeano = x.toPeano.predecessor := by
  have hx : toPeano x = Peano.fromCardinalNatural (absCardinalPeano x) := by
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
          have habs : absCardinalPeano x = CardinalNatural.Peano.zero := by
            simpa [absCardinalPeano] using toCardinalNaturalPeano_zero_of_allZero h_all
          have hx_peano : toPeano x = Peano.zero := by
            rw [hx, habs]; rfl
          rw [toPeano_minusOne, hx_peano]; rfl
      · next digits hpred =>
          have h_succ_pred : successorList digits = ⟨x.digits.val, false⟩ := by
            have h := successorList_predecessorList x.digits.val
            simpa [hpred] using h
          have h_abs :
              absCardinalPeano x =
                (toCardinalNaturalPeano digits CardinalNatural.Peano.zero).successor := by
            have hsucc :=
              successorList_toCardinalNaturalPeano digits CardinalNatural.Peano.zero
            rw [h_succ_pred] at hsucc
            dsimp only at hsucc
            simpa [absCardinalPeano] using hsucc
          split
          · next h_zero =>
              have hdigits0 := toCardinalNaturalPeano_zero_of_allZero h_zero
              have habs : absCardinalPeano x = CardinalNatural.Peano.one := by
                rw [h_abs, hdigits0]; rfl
              have hx_peano : toPeano x = Peano.one := by
                rw [hx, habs]; rfl
              rw [toPeano_zero, hx_peano]; rfl
          · next h_zero =>
              rw [hx]
              change Peano.fromCardinalNatural
                  (toCardinalNaturalPeano digits CardinalNatural.Peano.zero) =
                (Peano.fromCardinalNatural (absCardinalPeano x)).predecessor
              rw [h_abs, Peano.fromCardinalNatural_successor]
              exact (Peano.pred_succ _).symm

theorem predecessor_toPeano_plus (x : Decimal) (hsign : x.sign = some Sign.plus) :
    x.predecessor.toPeano = x.toPeano.predecessor := by
  have hx : toPeano x = Peano.fromCardinalNatural (absCardinalPeano x) := by
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
          have habs : absCardinalPeano x = CardinalNatural.Peano.zero := by
            simpa [absCardinalPeano] using toCardinalNaturalPeano_zero_of_allZero h_all
          have hx_peano : toPeano x = Peano.zero := by
            rw [hx, habs]; rfl
          rw [toPeano_minusOne, hx_peano]; rfl
      · next digits hpred =>
          have h_succ_pred : successorList digits = ⟨x.digits.val, false⟩ := by
            have h := successorList_predecessorList x.digits.val
            simpa [hpred] using h
          have h_abs :
              absCardinalPeano x =
                (toCardinalNaturalPeano digits CardinalNatural.Peano.zero).successor := by
            have hsucc :=
              successorList_toCardinalNaturalPeano digits CardinalNatural.Peano.zero
            rw [h_succ_pred] at hsucc
            dsimp only at hsucc
            simpa [absCardinalPeano] using hsucc
          split
          · next h_zero =>
              have hdigits0 := toCardinalNaturalPeano_zero_of_allZero h_zero
              have habs : absCardinalPeano x = CardinalNatural.Peano.one := by
                rw [h_abs, hdigits0]; rfl
              have hx_peano : toPeano x = Peano.one := by
                rw [hx, habs]; rfl
              rw [toPeano_zero, hx_peano]; rfl
          · next h_zero =>
              rw [hx]
              change Peano.fromCardinalNatural
                  (toCardinalNaturalPeano digits CardinalNatural.Peano.zero) =
                (Peano.fromCardinalNatural (absCardinalPeano x)).predecessor
              rw [h_abs, Peano.fromCardinalNatural_successor]
              exact (Peano.pred_succ _).symm

theorem predecessor_toPeano_minus (x : Decimal) (hsign : x.sign = some Sign.minus) :
    x.predecessor.toPeano = x.toPeano.predecessor := by
  have hx_toPeano :
      toPeano x = Peano.negate (Peano.fromCardinalNatural (absCardinalPeano x)) := by
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
                (toCardinalNaturalPeano
                  (Sequences.List.firstElement
                    ⟨CardinalNatural.Peano.one, CardinalNatural.Peano.one_lt_ten⟩ digits)
                  CardinalNatural.Peano.zero)) =
            (Peano.negate (Peano.fromCardinalNatural (absCardinalPeano x))).predecessor
          have habs :
              toCardinalNaturalPeano
                  (Sequences.List.firstElement
                    ⟨CardinalNatural.Peano.one, CardinalNatural.Peano.one_lt_ten⟩ digits)
                  CardinalNatural.Peano.zero =
                (absCardinalPeano x).successor := by
            simpa [absCardinalPeano, toCardinalNaturalPeano,
              CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.zero_add] using h_list
          rw [habs, Peano.fromCardinalNatural_successor]
          exact Peano.neg_succ _
      · next digits hsucc =>
          have h_list := toCardinalNaturalPeano_of_successorList x.digits.val
          rw [hsucc] at h_list
          dsimp only at h_list
          rw [hx_toPeano]
          change Peano.negate
              (Peano.fromCardinalNatural
                (toCardinalNaturalPeano digits CardinalNatural.Peano.zero)) =
            (Peano.negate (Peano.fromCardinalNatural (absCardinalPeano x))).predecessor
          have habs :
              toCardinalNaturalPeano digits CardinalNatural.Peano.zero =
                (absCardinalPeano x).successor := by
            simpa [absCardinalPeano] using h_list
          rw [habs, Peano.fromCardinalNatural_successor]
          exact Peano.neg_succ _
  · next sign h_ne =>
      exact False.elim (h_ne rfl)

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

theorem normalize_zero : zero.normalize = zero := rfl
theorem normalize_one : one.normalize = one := rfl
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

theorem absoluteValue_toPeano (x : Decimal) :
    x.absoluteValue.toPeano = x.toPeano.absoluteValue := by
  simp only [Decimal.absoluteValue]
  have hmag : ({ sign := none, digits := x.digits } : Decimal).toPeano =
      Peano.fromCardinalNatural (absCardinalPeano x) := by
    unfold toPeano absCardinalPeano
    rfl
  have hnonneg (n : CardinalNatural.Peano) :
      (Peano.fromCardinalNatural n).absoluteValue = Peano.fromCardinalNatural n := by
    cases n with
    | zero => rfl
    | successor _ => rfl
  rw [hmag]
  cases hsign : x.sign with
  | none =>
      have hx : x.toPeano = Peano.fromCardinalNatural (absCardinalPeano x) := by
        unfold toPeano; rw [hsign]
      rw [hx, hnonneg]
  | some s =>
      cases s with
      | plus =>
          have hx : x.toPeano = Peano.fromCardinalNatural (absCardinalPeano x) := by
            unfold toPeano; rw [hsign]
          rw [hx, hnonneg]
      | minus =>
          have hx : x.toPeano =
              Peano.negate (Peano.fromCardinalNatural (absCardinalPeano x)) := by
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
    (_h : absCardinalPeano smaller < absCardinalPeano larger) : Decimal :=
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
      ((isMagnitudeLessThan_iff_abs_lt nonneg neg).mp h)
  else if h2 : isMagnitudeLessThan neg nonneg then
    subtractMagnitudes none nonneg neg
      ((isMagnitudeLessThan_iff_abs_lt neg nonneg).mp h2)
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
            (toCardinalNaturalPeano a CardinalNatural.Peano.zero +
              toCardinalNaturalPeano b CardinalNatural.Peano.zero))
      | _ =>
          Peano.fromCardinalNatural
            (toCardinalNaturalPeano a CardinalNatural.Peano.zero +
              toCardinalNaturalPeano b CardinalNatural.Peano.zero) := by
  unfold addMagnitudes
  dsimp only
  have hsum := toCardinalNaturalPeano_addLists a b
  split
  · next heq =>
      have h_list :
          toCardinalNaturalPeano Sequences.List.empty CardinalNatural.Peano.zero =
            toCardinalNaturalPeano a CardinalNatural.Peano.zero +
              toCardinalNaturalPeano b CardinalNatural.Peano.zero := by
        simpa [heq] using hsum
      cases sign with
      | none =>
          simp [toPeano_zero, toCardinalNaturalPeano] at h_list ⊢
          exact congrArg Peano.fromCardinalNatural h_list.symm ▸ rfl
      | some s =>
          cases s with
          | plus =>
              simp [toPeano_zero, toCardinalNaturalPeano] at h_list ⊢
              exact congrArg Peano.fromCardinalNatural h_list.symm ▸ rfl
          | minus =>
              simp [toPeano_zero, toCardinalNaturalPeano] at h_list ⊢
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
    (h : absCardinalPeano smaller < absCardinalPeano larger) :
    toPeano (subtractMagnitudes sign larger smaller h) =
      match sign with
      | some Sign.minus =>
          -(Peano.fromCardinalNatural (absCardinalPeano larger)) +
            Peano.fromCardinalNatural (absCardinalPeano smaller)
      | _ =>
          Peano.fromCardinalNatural (absCardinalPeano larger) +
            -(Peano.fromCardinalNatural (absCardinalPeano smaller)) := by
  unfold subtractMagnitudes
  dsimp only
  have hnlt :
      ¬ absCardinalPeano larger < absCardinalPeano smaller :=
    fun hlt => CardinalNatural.Peano.not_lt_self _
      (CardinalNatural.Peano.lt_trans h hlt)
  have h_value :=
    subtractLists_spec larger.digits.val smaller.digits.val hnlt
  have h_sum :
      toCardinalNaturalPeano
          (subtractLists larger.digits.val smaller.digits.val)
          CardinalNatural.Peano.zero +
        absCardinalPeano smaller =
      absCardinalPeano larger := by
    simpa [absCardinalPeano] using h_value
  split
  · next heq =>
      -- empty difference cannot occur under absCardinalPeano smaller < larger.
      have h_eq : absCardinalPeano smaller = absCardinalPeano larger := by
        simp [toCardinalNaturalPeano, heq] at h_sum
        exact h_sum
      exact False.elim (CardinalNatural.Peano.not_lt_self _ (h_eq ▸ h))
  · next hd =>
      split
      · next hzero =>
          -- All-zero difference cannot occur under absCardinalPeano smaller < larger.
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
                  (toCardinalNaturalPeano
                    (subtractLists larger.digits.val smaller.digits.val)
                    CardinalNatural.Peano.zero) +
                Peano.fromCardinalNatural (absCardinalPeano smaller) =
              Peano.fromCardinalNatural (absCardinalPeano larger) := by
            rw [← Peano.fromCardinalNatural_add, h_sum]
          have h_peano :
              Peano.fromCardinalNatural
                  (toCardinalNaturalPeano
                    (subtractLists larger.digits.val smaller.digits.val)
                    CardinalNatural.Peano.zero) =
                Peano.fromCardinalNatural (absCardinalPeano larger) +
                  -(Peano.fromCardinalNatural (absCardinalPeano smaller)) :=
            Peano.eq_add_neg_of_add_eq h_peano_sum
          cases sign with
          | none =>
              exact h_peano
          | some s =>
              cases s with
              | plus =>
                  exact h_peano
              | minus =>
                  have h_neg := congrArg Neg.neg h_peano
                  rw [Peano.neg_add, Peano.neg_neg] at h_neg
                  exact h_neg

theorem addOppositeSigns_toPeano (nonneg neg : Decimal)
    (hnonneg : isNegative nonneg = false) (hneg : isNegative neg = true) :
    (addOppositeSigns nonneg neg).toPeano = nonneg.toPeano + neg.toPeano := by
  have hnonneg_peano := toPeano_eq_fromCardinal_of_not_isNegative nonneg hnonneg
  have ⟨hneg_peano, _⟩ := toPeano_eq_negate_fromCardinal_of_isNegative neg hneg
  unfold addOppositeSigns
  split
  · next hlt =>
      rw [subtractMagnitudes_toPeano, hnonneg_peano, hneg_peano, Peano.add_comm]
  · next hnlt =>
      split
      · next hgt =>
          rw [subtractMagnitudes_toPeano, hnonneg_peano, hneg_peano]
      · next hnge =>
          have h_not_lt : ¬ absCardinalPeano nonneg < absCardinalPeano neg := by
            intro hlt
            exact hnlt ((isMagnitudeLessThan_iff_abs_lt nonneg neg).mpr hlt)
          have h_not_gt : ¬ absCardinalPeano neg < absCardinalPeano nonneg := by
            intro hgt
            exact hnge ((isMagnitudeLessThan_iff_abs_lt neg nonneg).mpr hgt)
          have heq : absCardinalPeano nonneg = absCardinalPeano neg := by
            cases CardinalNatural.Peano.trichotomy_or
                (absCardinalPeano nonneg) (absCardinalPeano neg) with
            | inl hlt => exact False.elim (h_not_lt hlt)
            | inr hrest =>
                cases hrest with
                | inl heq => exact heq
                | inr hgt => exact False.elim (h_not_gt hgt)
          rw [toPeano_zero, hnonneg_peano, hneg_peano, heq, Peano.add_neg_self]

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
          rw [h, Peano.add_comm]
      | true =>
          rw [addMagnitudes_toPeano]
          simp only
          have ⟨hx_peano, _⟩ := toPeano_eq_negate_fromCardinal_of_isNegative x hx
          have ⟨hy_peano, _⟩ := toPeano_eq_negate_fromCardinal_of_isNegative y hy
          rw [hx_peano, hy_peano, ← Peano.neg_add, ← Peano.fromCardinalNatural_add]
          rfl

theorem add_commutative (a b : Decimal) : a + b ≈ b + a := by
  apply equivalent_of_toPeano_eq
  rw [add_toPeano, add_toPeano, Peano.add_comm]

theorem add_associative (a b c : Decimal) : a + b + c ≈ a + (b + c) := by
  apply equivalent_of_toPeano_eq
  rw [add_toPeano, add_toPeano, add_toPeano, add_toPeano, Peano.add_assoc]

theorem subtract_toPeano (x y : Decimal) :
    (x - y).toPeano = x.toPeano - y.toPeano := by
  have h : x - y = x + -y := rfl
  rw [h, add_toPeano, negate_toPeano, ← Peano.sub_eq_add_neg]

theorem add_sub_cancel (a b : Decimal) : a + b - b ≈ a := by
  apply equivalent_of_toPeano_eq
  rw [subtract_toPeano, add_toPeano, Peano.add_sub_cancel]

theorem sub_add_cancel (a b : Decimal) : a - b + b ≈ a := by
  apply equivalent_of_toPeano_eq
  rw [add_toPeano, subtract_toPeano, Peano.sub_add_cancel]

theorem sub_assoc (a b c : Decimal) : a + b - c ≈ a + (b - c) := by
  apply equivalent_of_toPeano_eq
  rw [subtract_toPeano, add_toPeano, add_toPeano, subtract_toPeano, Peano.sub_assoc]

theorem sub_add (a b c : Decimal) : a - b + c ≈ a - (b - c) := by
  apply equivalent_of_toPeano_eq
  rw [add_toPeano, subtract_toPeano, subtract_toPeano, subtract_toPeano, Peano.sub_add]
theorem multiply_toPeano (x y : Decimal) :
    (x * y).toPeano = x.toPeano * y.toPeano := by
  change (multiply x y).toPeano = x.toPeano * y.toPeano
  unfold multiply
  have hmag := (multiplyList_spec x.digits.val y.digits.val).2
  dsimp only
  split
  · next heq =>
      -- empty product digit list: magnitude is zero
      have hmag' := hmag
      rw [heq] at hmag'
      simp [toCardinalNaturalPeano] at hmag'
      rw [toPeano_zero]
      cases hx : isNegative x with
      | false =>
          cases hy : isNegative y with
          | false =>
              rw [toPeano_eq_fromCardinal_of_not_isNegative x hx,
                toPeano_eq_fromCardinal_of_not_isNegative y hy,
                ← Peano.fromCardinalNatural_mul]
              simp [absCardinalPeano, ← hmag']
              rfl
          | true =>
              have ⟨hy_peano, _⟩ := toPeano_eq_negate_fromCardinal_of_isNegative y hy
              rw [toPeano_eq_fromCardinal_of_not_isNegative x hx, hy_peano,
                Peano.mul_neg, ← Peano.fromCardinalNatural_mul]
              simp [absCardinalPeano, ← hmag']
              rfl
      | true =>
          cases hy : isNegative y with
          | false =>
              have ⟨hx_peano, _⟩ := toPeano_eq_negate_fromCardinal_of_isNegative x hx
              rw [hx_peano, toPeano_eq_fromCardinal_of_not_isNegative y hy,
                Peano.neg_mul, ← Peano.fromCardinalNatural_mul]
              simp [absCardinalPeano, ← hmag']
              rfl
          | true =>
              have ⟨hx_peano, _⟩ := toPeano_eq_negate_fromCardinal_of_isNegative x hx
              have ⟨hy_peano, _⟩ := toPeano_eq_negate_fromCardinal_of_isNegative y hy
              rw [hx_peano, hy_peano, Peano.neg_mul_neg, ← Peano.fromCardinalNatural_mul]
              simp [absCardinalPeano, ← hmag']
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
                    ← Peano.fromCardinalNatural_mul]
                  change _ = Peano.fromCardinalNatural
                    (toCardinalNaturalPeano x.digits.val CardinalNatural.Peano.zero *
                      toCardinalNaturalPeano y.digits.val CardinalNatural.Peano.zero)
                  rw [hprod]
                  rfl
              | true =>
                  have ⟨hy_peano, _⟩ := toPeano_eq_negate_fromCardinal_of_isNegative y hy
                  rw [toPeano_eq_fromCardinal_of_not_isNegative x hx, hy_peano,
                    Peano.mul_neg, ← Peano.fromCardinalNatural_mul]
                  change _ = -(Peano.fromCardinalNatural
                    (toCardinalNaturalPeano x.digits.val CardinalNatural.Peano.zero *
                      toCardinalNaturalPeano y.digits.val CardinalNatural.Peano.zero))
                  rw [hprod]
                  rfl
          | true =>
              cases hy : isNegative y with
              | false =>
                  have ⟨hx_peano, _⟩ := toPeano_eq_negate_fromCardinal_of_isNegative x hx
                  rw [hx_peano, toPeano_eq_fromCardinal_of_not_isNegative y hy,
                    Peano.neg_mul, ← Peano.fromCardinalNatural_mul]
                  change _ = -(Peano.fromCardinalNatural
                    (toCardinalNaturalPeano x.digits.val CardinalNatural.Peano.zero *
                      toCardinalNaturalPeano y.digits.val CardinalNatural.Peano.zero))
                  rw [hprod]
                  rfl
              | true =>
                  have ⟨hx_peano, _⟩ := toPeano_eq_negate_fromCardinal_of_isNegative x hx
                  have ⟨hy_peano, _⟩ := toPeano_eq_negate_fromCardinal_of_isNegative y hy
                  rw [hx_peano, hy_peano, Peano.neg_mul_neg, ← Peano.fromCardinalNatural_mul]
                  change _ = Peano.fromCardinalNatural
                    (toCardinalNaturalPeano x.digits.val CardinalNatural.Peano.zero *
                      toCardinalNaturalPeano y.digits.val CardinalNatural.Peano.zero)
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
                    ← Peano.fromCardinalNatural_mul, hmag]
                  rfl
              | true =>
                  simp only
                  have ⟨hy_peano, _⟩ := toPeano_eq_negate_fromCardinal_of_isNegative y hy
                  rw [toPeano_eq_fromCardinal_of_not_isNegative x hx, hy_peano,
                    Peano.mul_neg, ← Peano.fromCardinalNatural_mul, hmag]
                  rfl
          | true =>
              cases hy : isNegative y with
              | false =>
                  simp only
                  have ⟨hx_peano, _⟩ := toPeano_eq_negate_fromCardinal_of_isNegative x hx
                  rw [hx_peano, toPeano_eq_fromCardinal_of_not_isNegative y hy,
                    Peano.neg_mul, ← Peano.fromCardinalNatural_mul, hmag]
                  rfl
              | true =>
                  simp only
                  have ⟨hx_peano, _⟩ := toPeano_eq_negate_fromCardinal_of_isNegative x hx
                  have ⟨hy_peano, _⟩ := toPeano_eq_negate_fromCardinal_of_isNegative y hy
                  rw [hx_peano, hy_peano, Peano.neg_mul_neg, ← Peano.fromCardinalNatural_mul,
                    hmag]
                  rfl

theorem multiply_commutative (a b : Decimal) : a * b ≈ b * a := by
  apply equivalent_of_toPeano_eq
  rw [multiply_toPeano, multiply_toPeano, Peano.mul_comm]

theorem multiply_associative (a b c : Decimal) : a * b * c ≈ a * (b * c) := by
  apply equivalent_of_toPeano_eq
  rw [multiply_toPeano, multiply_toPeano, multiply_toPeano, multiply_toPeano,
    Peano.mul_assoc]

theorem multiply_distributive_over_add_right (a b c : Decimal) :
    a * (b + c) ≈ a * b + a * c := by
  apply equivalent_of_toPeano_eq
  rw [multiply_toPeano, add_toPeano, add_toPeano, multiply_toPeano, multiply_toPeano,
    Peano.mul_add]

theorem multiply_distributive_over_add_left (a b c : Decimal) :
    (a + b) * c ≈ a * c + b * c := by
  apply equivalent_of_toPeano_eq
  rw [multiply_toPeano, add_toPeano, add_toPeano, multiply_toPeano, multiply_toPeano,
    Peano.mul_comm (a.toPeano + b.toPeano), Peano.mul_add,
    Peano.mul_comm c.toPeano a.toPeano, Peano.mul_comm c.toPeano b.toPeano]

theorem multiply_distributive_over_sub_right (a b c : Decimal) :
    a * (b - c) ≈ a * b - a * c := by
  apply equivalent_of_toPeano_eq
  rw [multiply_toPeano, subtract_toPeano, subtract_toPeano, multiply_toPeano, multiply_toPeano,
    Peano.mul_sub]

theorem multiply_distributive_over_sub_left (a b c : Decimal) :
    (a - b) * c ≈ a * c - b * c := by
  apply equivalent_of_toPeano_eq
  rw [multiply_toPeano, subtract_toPeano, subtract_toPeano, multiply_toPeano, multiply_toPeano,
    Peano.sub_mul]

/-- Convert a positive ordinal Peano natural to a non-negative decimal integer. -/
def fromOrdinalPositive : OrdinalNatural.Peano → Decimal
  | .one => one
  | .successor n => successor (fromOrdinalPositive n)

/-- Convert an integer Peano value to a decimal representation. -/
def fromPeano : Peano → Decimal
  | .zero => zero
  | .positive n => fromOrdinalPositive n
  | .negative n => -(fromOrdinalPositive n)

theorem toPeano_fromOrdinalPositive (n : OrdinalNatural.Peano) :
    (fromOrdinalPositive n).toPeano = Peano.positive n := by
  induction n with
  | one =>
    rfl
  | successor n ih =>
    unfold fromOrdinalPositive
    rw [successor_toPeano, ih]
    rfl

theorem toPeano_fromPeano (x : Peano) : (fromPeano x).toPeano = x := by
  cases x with
  | zero => rfl
  | positive n =>
    exact toPeano_fromOrdinalPositive n
  | negative n =>
    unfold fromPeano
    rw [negate_toPeano, toPeano_fromOrdinalPositive]
    rfl

theorem toPeano_ne_zero_of_not_equivalent_zero {x : Decimal} (h : ¬ x ≈ zero) :
    x.toPeano ≠ Peano.zero := by
  intro hx
  exact h (equivalent_of_toPeano_eq (hx.trans toPeano_zero.symm))

/-- `a` is divisible by `b` when `b` is non-zero (up to equivalence) and there is a
decimal quotient `c` with `b * c ≈ a`. -/
def Divisible (a b : Decimal) : Prop := ¬ (b ≈ zero) ∧ ∃ c, b * c ≈ a

theorem divisibleToPeano (a b : Decimal) :
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

theorem magnitude_toPeano (a : Decimal) :
    a.magnitude.toPeano = absCardinalPeano a := rfl

/-- Boolean divisibility on magnitudes via cardinal decimal long division. -/
def isDivisible (a b : Decimal) : Bool :=
  CardinalNatural.Decimal.isDivisible a.magnitude b.magnitude

theorem isDivisible_eq_cardinal_magnitude (a b : Decimal) :
    isDivisible a b =
      CardinalNatural.Decimal.isDivisible a.magnitude b.magnitude := rfl

theorem bool_eq_of_true_iff {x y : Bool} (h : (x = true) ↔ (y = true)) : x = y := by
  cases x <;> cases y <;> simp_all

theorem toPeano_eq_zero_of_absCardinal_zero {a : Decimal}
    (ha : absCardinalPeano a = CardinalNatural.Peano.zero) :
    a.toPeano = Peano.zero := by
  unfold toPeano
  cases a.sign with
  | none => simp only [ha, Peano.fromCardinalNatural]
  | some s =>
    cases s with
    | plus => simp only [ha, Peano.fromCardinalNatural]
    | minus => simp only [ha, Peano.fromCardinalNatural, Peano.negate]

theorem toPeano_eq_signed_toOrdinal_of_absCardinal_successor
    (a : Decimal) (n : CardinalNatural.Peano)
    (ha : absCardinalPeano a = CardinalNatural.Peano.successor n) :
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
    show Peano.fromCardinalNatural (absCardinalPeano a) =
      Peano.positive
        (CardinalNatural.Peano.toOrdinal (CardinalNatural.Peano.successor n)
          (CardinalNatural.Peano.successor_ne_zero n))
    rw [ha]
    rfl
  | some s =>
    cases s with
    | plus =>
      left
      show Peano.fromCardinalNatural (absCardinalPeano a) =
        Peano.positive
          (CardinalNatural.Peano.toOrdinal (CardinalNatural.Peano.successor n)
            (CardinalNatural.Peano.successor_ne_zero n))
      rw [ha]
      rfl
    | minus =>
      right
      show Peano.negate (Peano.fromCardinalNatural (absCardinalPeano a)) =
        Peano.negative
          (CardinalNatural.Peano.toOrdinal (CardinalNatural.Peano.successor n)
            (CardinalNatural.Peano.successor_ne_zero n))
      rw [ha]
      rfl

theorem cardinal_divisible_iff_ordinal_divisible
    (x y : CardinalNatural.Peano)
    (hx : x ≠ CardinalNatural.Peano.zero) (hy : y ≠ CardinalNatural.Peano.zero) :
    CardinalNatural.Peano.Divisible x y ↔
      OrdinalNatural.Peano.Divisible
        (CardinalNatural.Peano.toOrdinal x hx)
        (CardinalNatural.Peano.toOrdinal y hy) := by
  apply Iff.intro
  · intro h
    obtain ⟨_, c, hc⟩ := h
    have hc_ne : c ≠ CardinalNatural.Peano.zero := by
      intro hc0
      simp only [hc0, CardinalNatural.Peano.multiply_zero] at hc
      exact hx hc.symm
    refine ⟨CardinalNatural.Peano.toOrdinal c hc_ne, ?_⟩
    apply CardinalNatural.Peano.eq_of_fromOrdinal_eq
    rw [CardinalNatural.Peano.fromOrdinal_multiply,
      CardinalNatural.Peano.fromOrdinal_toOrdinal y hy,
      CardinalNatural.Peano.fromOrdinal_toOrdinal c hc_ne,
      CardinalNatural.Peano.fromOrdinal_toOrdinal x hx, hc]
  · intro h
    obtain ⟨c, hc⟩ := h
    refine ⟨hy, CardinalNatural.Peano.fromOrdinal c, ?_⟩
    rw [← CardinalNatural.Peano.fromOrdinal_toOrdinal y hy,
      ← CardinalNatural.Peano.fromOrdinal_multiply,
      hc, CardinalNatural.Peano.fromOrdinal_toOrdinal x hx]

theorem cardinal_isDivisible_eq_ordinal_isDivisible
    (x y : CardinalNatural.Peano)
    (hx : x ≠ CardinalNatural.Peano.zero) (hy : y ≠ CardinalNatural.Peano.zero) :
    CardinalNatural.Peano.isDivisible x y =
      OrdinalNatural.Peano.isDivisible
        (CardinalNatural.Peano.toOrdinal x hx)
        (CardinalNatural.Peano.toOrdinal y hy) := by
  apply bool_eq_of_true_iff
  calc
    CardinalNatural.Peano.isDivisible x y = true ↔
        CardinalNatural.Peano.Divisible x y :=
      (CardinalNatural.Peano.isDivisibleCorrect x y).symm
    _ ↔ OrdinalNatural.Peano.Divisible
          (CardinalNatural.Peano.toOrdinal x hx)
          (CardinalNatural.Peano.toOrdinal y hy) :=
      cardinal_divisible_iff_ordinal_divisible x y hx hy
    _ ↔ OrdinalNatural.Peano.isDivisible
          (CardinalNatural.Peano.toOrdinal x hx)
          (CardinalNatural.Peano.toOrdinal y hy) = true :=
      OrdinalNatural.Peano.isDivisibleCorrect
        (CardinalNatural.Peano.toOrdinal x hx)
        (CardinalNatural.Peano.toOrdinal y hy)

theorem peano_isDivisible_eq_absCardinal (a b : Decimal) :
    CardinalNatural.Peano.isDivisible (absCardinalPeano a) (absCardinalPeano b) =
      Peano.isDivisible a.toPeano b.toPeano := by
  cases hb : absCardinalPeano b with
  | zero =>
    have hb_peano := toPeano_eq_zero_of_absCardinal_zero hb
    simp only [CardinalNatural.Peano.isDivisible, hb_peano, Peano.isDivisible]
  | successor b' =>
    cases ha : absCardinalPeano a with
    | zero =>
      have ha_peano := toPeano_eq_zero_of_absCardinal_zero ha
      have hb_ne : b.toPeano ≠ Peano.zero := by
        intro h0
        have habs := absCardinalPeano_eq_of_toPeano_eq (h0.trans toPeano_zero.symm)
        simp only [absCardinalPeano, zero, toCardinalNaturalPeano, zeroDigit] at habs
        exact CardinalNatural.Peano.successor_ne_zero b' (hb.symm.trans habs)
      simp only [CardinalNatural.Peano.isDivisible, ha_peano]
      cases hb_peano : b.toPeano with
      | zero => exact False.elim (hb_ne hb_peano)
      | positive _ => rfl
      | negative _ => rfl
    | successor a' =>
      have ha_pos :=
        toPeano_eq_signed_toOrdinal_of_absCardinal_successor a a' ha
      have hb_pos :=
        toPeano_eq_signed_toOrdinal_of_absCardinal_successor b b' hb
      have hcard_eq_ord :=
        cardinal_isDivisible_eq_ordinal_isDivisible
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
          (absCardinalPeano a) (absCardinalPeano b) := by
            simp only [magnitude_toPeano]
    _ = Peano.isDivisible a.toPeano b.toPeano :=
          peano_isDivisible_eq_absCardinal a b

theorem isDivisibleCorrect (a b : Decimal) : Divisible a b ↔ isDivisible a b := by
  rw [divisibleToPeano, isDivisible_eq_peano]
  exact Peano.isDivisibleCorrect a.toPeano b.toPeano

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

end Decimal

end ZeroMath.Numbers.Integer
