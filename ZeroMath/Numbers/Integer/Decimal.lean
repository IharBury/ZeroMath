import ZeroMath.Numbers.CardinalNatural.Peano
import ZeroMath.Numbers.Integer.Peano
import ZeroMath.Sequences.List

namespace ZeroMath.Numbers.Integer

namespace Decimal

inductive Sign where
  | plus
  | minus

deriving instance DecidableEq for Sign

def Digit := {d : CardinalNatural.Peano // d < CardinalNatural.Peano.ten}

instance : DecidableEq Digit :=
  fun x y =>
    if h : x.val = y.val then
      isTrue (Subtype.ext h)
    else
      isFalse (fun h' => h (congrArg Subtype.val h'))

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

def zeroDigit : Digit := ⟨CardinalNatural.Peano.zero, by decide⟩
def oneDigit : Digit := ⟨CardinalNatural.Peano.one, by decide⟩
def twoDigit : Digit := ⟨CardinalNatural.Peano.two, by decide⟩
def threeDigit : Digit := ⟨CardinalNatural.Peano.three, by decide⟩
def fourDigit : Digit := ⟨CardinalNatural.Peano.four, by decide⟩
def fiveDigit : Digit := ⟨CardinalNatural.Peano.five, by decide⟩
def sixDigit : Digit := ⟨CardinalNatural.Peano.six, by decide⟩
def sevenDigit : Digit := ⟨CardinalNatural.Peano.seven, by decide⟩
def eightDigit : Digit := ⟨CardinalNatural.Peano.eight, by decide⟩
def nineDigit : Digit := ⟨CardinalNatural.Peano.nine, by decide⟩

def zero : Decimal :=
  ⟨none, ⟨Sequences.List.firstElement zeroDigit Sequences.List.empty, by simp⟩⟩

def one : Decimal :=
  ⟨none, ⟨Sequences.List.firstElement oneDigit Sequences.List.empty, by simp⟩⟩

def minusOne : Decimal :=
  ⟨some Sign.minus, ⟨Sequences.List.firstElement oneDigit Sequences.List.empty, by simp⟩⟩

/-- A decimal is normalized when it has no extra leading zeros, and non-negative values
carry no sign (`none` rather than `some Sign.plus`, and not `-0`). -/
def isNormalized (d : Decimal) : Bool :=
  match d.sign, h : d.digits.val with
  | some Sign.plus, _ => false
  | none, .empty => False.elim (d.digits.property h)
  | none, .firstElement _digit .empty => true
  | none, .firstElement digit _ => decide (digit.val ≠ CardinalNatural.Peano.zero)
  | some Sign.minus, .empty => False.elim (d.digits.property h)
  | some Sign.minus, .firstElement digit _ =>
      decide (digit.val ≠ CardinalNatural.Peano.zero)

/-- Strip leading zeros and canonicalize sign: `some Sign.plus` becomes `none`, and
any zero magnitude (including `-0`) becomes `zero`. -/
def normalizeList (sign : Option Sign) (a : Sequences.List Digit) : Decimal :=
  match a with
  | .empty => zero
  | .firstElement d ds =>
      if d.val = CardinalNatural.Peano.zero then
        normalizeList sign ds
      else
        match sign with
        | some Sign.plus | none =>
            ⟨none, ⟨Sequences.List.firstElement d ds, by simp⟩⟩
        | some Sign.minus =>
            ⟨some Sign.minus, ⟨Sequences.List.firstElement d ds, by simp⟩⟩

def normalize (a : Decimal) : Decimal :=
  normalizeList a.sign a.digits.val

/-- Interpret a digit list as a cardinal Peano natural (most-significant digit first). -/
def toCardinalPeanoList (x : Sequences.List Digit) (accumulator : CardinalNatural.Peano) :
    CardinalNatural.Peano :=
  match x with
  | .empty => accumulator
  | .firstElement d ds =>
      toCardinalPeanoList ds (accumulator * CardinalNatural.Peano.ten + d.val)

/-- Absolute magnitude of a decimal integer as a cardinal Peano natural. -/
def absCardinalPeano (a : Decimal) : CardinalNatural.Peano :=
  toCardinalPeanoList a.digits.val CardinalNatural.Peano.zero

/-- Convert a decimal integer to its Peano representation. -/
def toPeano (a : Decimal) : Peano :=
  let magnitude := Peano.fromCardinalNatural (absCardinalPeano a)
  match a.sign with
  | some Sign.minus => Peano.negate magnitude
  | _ => magnitude

/-- Increment a digit list from the least-significant end; `true` means a new leading `1` is needed. -/
def successorList (a : Sequences.List Digit) :
    Sequences.List Digit × Bool :=
  match a with
  | .empty => ⟨Sequences.List.empty, true⟩
  | .firstElement d ds =>
    let ⟨digits, carry⟩ := successorList ds
    if carry then
      if h3 : CardinalNatural.Peano.isLessThan d.val.successor CardinalNatural.Peano.ten then
        ⟨Sequences.List.firstElement
          ⟨d.val.successor, (CardinalNatural.Peano.isLessThan_eq_true_iff_lt _ _).mp h3⟩
          digits, false⟩
      else
        ⟨Sequences.List.firstElement
          ⟨CardinalNatural.Peano.zero, CardinalNatural.Peano.zero_lt_succ CardinalNatural.Peano.nine⟩
          digits, true⟩
    else
      ⟨Sequences.List.firstElement d digits, false⟩

/-- Decrement a digit list from the least-significant end; `true` means the input was all zeros. -/
def predecessorList (a : Sequences.List Digit) :
    Sequences.List Digit × Bool :=
  match a with
  | .empty => ⟨Sequences.List.empty, true⟩
  | .firstElement d ds =>
    let ⟨digits, borrow⟩ := predecessorList ds
    if borrow then
      match d with
      | ⟨.zero, _⟩ =>
        ⟨Sequences.List.firstElement ⟨CardinalNatural.Peano.nine, CardinalNatural.Peano.LessThan.base⟩
          digits, true⟩
      | ⟨.successor d', h⟩ =>
        ⟨Sequences.List.firstElement ⟨d', CardinalNatural.Peano.lt_of_succ_lt h⟩ digits, false⟩
    else
      ⟨Sequences.List.firstElement d digits, false⟩

def AllZero : Sequences.List Digit → Prop
  | .empty => True
  | .firstElement d ds => d.val = CardinalNatural.Peano.zero ∧ AllZero ds

instance decidableAllZero : (a : Sequences.List Digit) → Decidable (AllZero a)
  | .empty => inferInstanceAs (Decidable True)
  | .firstElement d ds =>
      match decidableAllZero ds, decEq d.val CardinalNatural.Peano.zero with
      | isTrue hds, isTrue hd => isTrue ⟨hd, hds⟩
      | isFalse hds, _ => isFalse (fun h => hds h.2)
      | _, isFalse hd => isFalse (fun h => hd h.1)

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

theorem successorList_ne_empty_of_carry_false {a digits : Sequences.List Digit}
    (ha : a ≠ Sequences.List.empty) (h : successorList a = ⟨digits, false⟩) :
    digits ≠ Sequences.List.empty := by
  induction a generalizing digits with
  | empty =>
      exact False.elim (ha rfl)
  | firstElement d ds _ =>
      unfold successorList at h
      dsimp at h
      split at h
      · split at h
        · cases h
          intro h_empty
          cases h_empty
        · cases h
      · cases h
        intro h_empty
        cases h_empty

theorem predecessorList_ne_empty_of_borrow_false {a digits : Sequences.List Digit}
    (ha : a ≠ Sequences.List.empty) (h : predecessorList a = ⟨digits, false⟩) :
    digits ≠ Sequences.List.empty := by
  induction a generalizing digits with
  | empty =>
      exact False.elim (ha rfl)
  | firstElement d ds _ =>
      unfold predecessorList at h
      dsimp at h
      split at h
      · split at h
        · cases h
        · cases h
          intro h_empty
          cases h_empty
      · cases h
        intro h_empty
        cases h_empty

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

theorem digit_val_eq_nine_of_not_successor_lt_ten (d : Digit)
    (h : CardinalNatural.Peano.isLessThan d.val.successor CardinalNatural.Peano.ten = false) :
    d.val = CardinalNatural.Peano.nine := by
  have h_not_lt : ¬ d.val.successor < CardinalNatural.Peano.ten :=
    (CardinalNatural.Peano.isLessThan_eq_false_iff_not_lt _ _).mp h
  cases d with
  | mk val hval =>
      dsimp at h_not_lt hval
      cases val with
      | zero =>
          exact False.elim (h_not_lt CardinalNatural.Peano.one_lt_ten)
      | successor val1 =>
          cases val1 with
          | zero =>
              exact False.elim (h_not_lt (by repeat constructor))
          | successor val2 =>
              cases val2 with
              | zero => exact False.elim (h_not_lt (by repeat constructor))
              | successor val3 =>
                  cases val3 with
                  | zero => exact False.elim (h_not_lt (by repeat constructor))
                  | successor val4 =>
                      cases val4 with
                      | zero => exact False.elim (h_not_lt (by repeat constructor))
                      | successor val5 =>
                          cases val5 with
                          | zero => exact False.elim (h_not_lt (by repeat constructor))
                          | successor val6 =>
                              cases val6 with
                              | zero => exact False.elim (h_not_lt (by repeat constructor))
                              | successor val7 =>
                                  cases val7 with
                                  | zero => exact False.elim (h_not_lt (by repeat constructor))
                                  | successor val8 =>
                                      cases val8 with
                                      | zero => exact False.elim (h_not_lt (by repeat constructor))
                                      | successor val9 =>
                                          cases val9 with
                                          | zero => rfl
                                          | successor val10 =>
                                              have hlt_zero : val10 < CardinalNatural.Peano.zero :=
                                                (CardinalNatural.Peano.lt_of_succ_lt_succ
                                                (CardinalNatural.Peano.lt_of_succ_lt_succ
                                                (CardinalNatural.Peano.lt_of_succ_lt_succ
                                                (CardinalNatural.Peano.lt_of_succ_lt_succ
                                                (CardinalNatural.Peano.lt_of_succ_lt_succ
                                                (CardinalNatural.Peano.lt_of_succ_lt_succ
                                                (CardinalNatural.Peano.lt_of_succ_lt_succ
                                                (CardinalNatural.Peano.lt_of_succ_lt_succ
                                                (CardinalNatural.Peano.lt_of_succ_lt_succ
                                                (CardinalNatural.Peano.lt_of_succ_lt_succ hval))))))))))
                                              exact False.elim
                                                ((CardinalNatural.Peano.not_lt_zero val10) hlt_zero)

theorem successor_carry_accumulator (accumulator : CardinalNatural.Peano) :
    accumulator.successor * CardinalNatural.Peano.ten + CardinalNatural.Peano.zero =
      (accumulator * CardinalNatural.Peano.ten + CardinalNatural.Peano.nine).successor := by
  rw [CardinalNatural.Peano.add_zero, CardinalNatural.Peano.successor_multiply]
  change accumulator * CardinalNatural.Peano.ten + CardinalNatural.Peano.ten =
    (accumulator * CardinalNatural.Peano.ten + CardinalNatural.Peano.nine).successor
  rfl

theorem successorList_toCardinalPeanoList (a : Sequences.List Digit)
    (accumulator : CardinalNatural.Peano) :
    match successorList a with
    | ⟨digits, true⟩ =>
        toCardinalPeanoList digits accumulator.successor =
          (toCardinalPeanoList a accumulator).successor
    | ⟨digits, false⟩ =>
        toCardinalPeanoList digits accumulator =
          (toCardinalPeanoList a accumulator).successor := by
  induction a generalizing accumulator with
  | empty =>
      rfl
  | firstElement d ds ih =>
      unfold successorList
      dsimp only
      cases hds : successorList ds with
      | mk digits carry =>
          have ih' := ih (accumulator * CardinalNatural.Peano.ten + d.val)
          rw [hds] at ih'
          cases carry with
          | false =>
              dsimp only at ih' ⊢
              exact ih'
          | true =>
              dsimp only at ih'
              by_cases hlt :
                  CardinalNatural.Peano.isLessThan d.val.successor CardinalNatural.Peano.ten = true
              · simp [hlt]
                change toCardinalPeanoList digits
                    (accumulator * CardinalNatural.Peano.ten + d.val.successor) =
                  (toCardinalPeanoList ds
                    (accumulator * CardinalNatural.Peano.ten + d.val)).successor
                change toCardinalPeanoList digits
                    (accumulator * CardinalNatural.Peano.ten + d.val).successor =
                  (toCardinalPeanoList ds
                    (accumulator * CardinalNatural.Peano.ten + d.val)).successor at ih'
                exact ih'
              · have hfalse :
                    CardinalNatural.Peano.isLessThan d.val.successor CardinalNatural.Peano.ten =
                      false := by
                  cases h : CardinalNatural.Peano.isLessThan d.val.successor
                      CardinalNatural.Peano.ten with
                  | false => rfl
                  | true => contradiction
                simp [hfalse]
                change toCardinalPeanoList digits
                    (accumulator.successor * CardinalNatural.Peano.ten +
                      CardinalNatural.Peano.zero) =
                  (toCardinalPeanoList ds
                    (accumulator * CardinalNatural.Peano.ten + d.val)).successor
                have hd : d.val = CardinalNatural.Peano.nine :=
                  digit_val_eq_nine_of_not_successor_lt_ten d hfalse
                rw [hd]
                rw [successor_carry_accumulator]
                change toCardinalPeanoList digits
                    (accumulator * CardinalNatural.Peano.ten +
                      CardinalNatural.Peano.nine).successor =
                  (toCardinalPeanoList ds
                    (accumulator * CardinalNatural.Peano.ten +
                      CardinalNatural.Peano.nine)).successor
                rw [hd] at ih'
                exact ih'

theorem allZero_of_predecessorList_borrow_true {a digits : Sequences.List Digit}
    (h : predecessorList a = ⟨digits, true⟩) : AllZero a := by
  induction a generalizing digits with
  | empty => trivial
  | firstElement d ds ih =>
      unfold predecessorList at h
      cases h_rec : predecessorList ds with
      | mk tailDigits borrow =>
          rw [h_rec] at h
          cases borrow with
          | false => cases h
          | true =>
              cases d with
              | mk val hlt =>
                  cases val with
                  | zero =>
                      exact ⟨rfl, ih h_rec⟩
                  | successor d' => cases h

theorem toCardinalPeanoList_zero_of_allZero {a : Sequences.List Digit} (h : AllZero a) :
    toCardinalPeanoList a CardinalNatural.Peano.zero = CardinalNatural.Peano.zero := by
  induction a with
  | empty => rfl
  | firstElement d ds ih =>
      change toCardinalPeanoList ds
          (CardinalNatural.Peano.zero * CardinalNatural.Peano.ten + d.val) = _
      have hd : d.val = CardinalNatural.Peano.zero := h.1
      rw [hd, CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.zero_add]
      exact ih h.2

theorem successorList_predecessorList (a : Sequences.List Digit) :
    successorList (predecessorList a).1 = ⟨a, (predecessorList a).2⟩ := by
  induction a with
  | empty => rfl
  | firstElement d ds ih =>
      unfold predecessorList
      cases h_predecessor : predecessorList ds with
      | mk digits borrow =>
          rw [h_predecessor] at ih
          cases borrow with
          | false =>
              simp_all [successorList]
          | true =>
              cases d with
              | mk val hlt =>
                  cases val
                  · have h_not_lt :=
                      CardinalNatural.Peano.not_lt_self CardinalNatural.Peano.ten
                    simp_all [successorList, CardinalNatural.Peano.ten,
                      CardinalNatural.Peano.isLessThan_eq_true_iff_lt]
                  · simp_all [successorList,
                      CardinalNatural.Peano.isLessThan_eq_true_iff_lt]

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
      simpa [absCardinalPeano] using toCardinalPeanoList_zero_of_allZero h_all
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
            exact (Peano.negate_negate _).symm

theorem normalizeList_plus_eq_none (a : Sequences.List Digit) :
    normalizeList (some Sign.plus) a = normalizeList none a := by
  induction a with
  | empty => rfl
  | firstElement d ds ih =>
      unfold normalizeList
      split
      · exact ih
      · rfl

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

theorem normalizeList_toPeano (sign : Option Sign) (a : Sequences.List Digit) :
    toPeano (normalizeList sign a) =
      match sign with
      | some Sign.minus =>
          Peano.negate (Peano.fromCardinalNatural
            (toCardinalPeanoList a CardinalNatural.Peano.zero))
      | _ =>
          Peano.fromCardinalNatural
            (toCardinalPeanoList a CardinalNatural.Peano.zero) := by
  induction a with
  | empty =>
      cases sign with
      | none => rfl
      | some s =>
          cases s with
          | plus => rfl
          | minus => rfl
  | firstElement d ds ih =>
      unfold normalizeList
      split
      · next hd =>
          rw [ih]
          have hmag :
              toCardinalPeanoList ds CardinalNatural.Peano.zero =
                toCardinalPeanoList (Sequences.List.firstElement d ds)
                  CardinalNatural.Peano.zero := by
            change toCardinalPeanoList ds CardinalNatural.Peano.zero =
              toCardinalPeanoList ds
                (CardinalNatural.Peano.zero * CardinalNatural.Peano.ten + d.val)
            rw [hd, CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.add_zero]
          rw [hmag]
      · next hd =>
          cases sign with
          | none => rfl
          | some s =>
              cases s with
              | plus => rfl
              | minus => rfl

theorem normalize_toPeano (x : Decimal) : x.normalize.toPeano = x.toPeano := by
  unfold normalize toPeano absCardinalPeano
  exact normalizeList_toPeano x.sign x.digits.val

theorem normalizeList_isNormalized (sign : Option Sign) (a : Sequences.List Digit) :
    (normalizeList sign a).isNormalized = true := by
  induction a with
  | empty =>
      rfl
  | firstElement d ds ih =>
      unfold normalizeList
      split
      · exact ih
      · next hd =>
          cases sign with
          | none =>
              cases ds with
              | empty =>
                  rfl
              | firstElement d' ds' =>
                  simp [isNormalized, hd]
          | some s =>
              cases s with
              | plus =>
                  cases ds with
                  | empty =>
                      rfl
                  | firstElement d' ds' =>
                      simp [isNormalized, hd]
              | minus =>
                  simp [isNormalized, hd]

theorem normalize_isNormalized (d : Decimal) : d.normalize.isNormalized = true := by
  unfold normalize
  exact normalizeList_isNormalized d.sign d.digits.val

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

theorem toCardinalPeanoList_of_successorList (a : Sequences.List Digit) :
    match successorList a with
    | ⟨digits, true⟩ =>
        toCardinalPeanoList digits CardinalNatural.Peano.one =
          (toCardinalPeanoList a CardinalNatural.Peano.zero).successor
    | ⟨digits, false⟩ =>
        toCardinalPeanoList digits CardinalNatural.Peano.zero =
          (toCardinalPeanoList a CardinalNatural.Peano.zero).successor := by
  have h := successorList_toCardinalPeanoList a CardinalNatural.Peano.zero
  cases h_succ : successorList a with
  | mk digits carry =>
      rw [h_succ] at h
      cases carry with
      | true =>
          dsimp only at h ⊢
          exact h
      | false =>
          dsimp only at h ⊢
          exact h

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
          have h_list := toCardinalPeanoList_of_successorList x.digits.val
          rw [hsucc] at h_list
          dsimp only at h_list
          rw [hx]
          change Peano.fromCardinalNatural
              (toCardinalPeanoList
                (Sequences.List.firstElement
                  ⟨CardinalNatural.Peano.one, CardinalNatural.Peano.one_lt_ten⟩ digits)
                CardinalNatural.Peano.zero) =
            (Peano.fromCardinalNatural (absCardinalPeano x)).successor
          have habs :
              toCardinalPeanoList
                  (Sequences.List.firstElement
                    ⟨CardinalNatural.Peano.one, CardinalNatural.Peano.one_lt_ten⟩ digits)
                  CardinalNatural.Peano.zero =
                (absCardinalPeano x).successor := by
            simpa [absCardinalPeano, toCardinalPeanoList,
              CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.zero_add] using h_list
          rw [habs, Peano.fromCardinalNatural_successor]
      · next digits hsucc =>
          have h_list := toCardinalPeanoList_of_successorList x.digits.val
          rw [hsucc] at h_list
          dsimp only at h_list
          rw [hx]
          change Peano.fromCardinalNatural
              (toCardinalPeanoList digits CardinalNatural.Peano.zero) =
            (Peano.fromCardinalNatural (absCardinalPeano x)).successor
          have habs :
              toCardinalPeanoList digits CardinalNatural.Peano.zero =
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
          have h_list := toCardinalPeanoList_of_successorList x.digits.val
          rw [hsucc] at h_list
          dsimp only at h_list
          rw [hx]
          change Peano.fromCardinalNatural
              (toCardinalPeanoList
                (Sequences.List.firstElement
                  ⟨CardinalNatural.Peano.one, CardinalNatural.Peano.one_lt_ten⟩ digits)
                CardinalNatural.Peano.zero) =
            (Peano.fromCardinalNatural (absCardinalPeano x)).successor
          have habs :
              toCardinalPeanoList
                  (Sequences.List.firstElement
                    ⟨CardinalNatural.Peano.one, CardinalNatural.Peano.one_lt_ten⟩ digits)
                  CardinalNatural.Peano.zero =
                (absCardinalPeano x).successor := by
            simpa [absCardinalPeano, toCardinalPeanoList,
              CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.zero_add] using h_list
          rw [habs, Peano.fromCardinalNatural_successor]
      · next digits hsucc =>
          have h_list := toCardinalPeanoList_of_successorList x.digits.val
          rw [hsucc] at h_list
          dsimp only at h_list
          rw [hx]
          change Peano.fromCardinalNatural
              (toCardinalPeanoList digits CardinalNatural.Peano.zero) =
            (Peano.fromCardinalNatural (absCardinalPeano x)).successor
          have habs :
              toCardinalPeanoList digits CardinalNatural.Peano.zero =
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
            simpa [absCardinalPeano] using toCardinalPeanoList_zero_of_allZero h_all
          have hx_peano : toPeano x = Peano.zero := by
            rw [hx_toPeano, habs]; rfl
          rw [toPeano_one, hx_peano]; rfl
      · next digits hpred =>
          have h_succ_pred : successorList digits = ⟨x.digits.val, false⟩ := by
            have h := successorList_predecessorList x.digits.val
            simpa [hpred] using h
          have h_abs :
              absCardinalPeano x =
                (toCardinalPeanoList digits CardinalNatural.Peano.zero).successor := by
            have hsucc :=
              successorList_toCardinalPeanoList digits CardinalNatural.Peano.zero
            rw [h_succ_pred] at hsucc
            dsimp only at hsucc
            simpa [absCardinalPeano] using hsucc
          split
          · next h_zero =>
              have hdigits0 := toCardinalPeanoList_zero_of_allZero h_zero
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
                        (toCardinalPeanoList digits CardinalNatural.Peano.zero)) := by
                simp only [toPeano, absCardinalPeano]
              have hx_peano :
                  toPeano x =
                    Peano.negate
                      (Peano.successor
                        (Peano.fromCardinalNatural
                          (toCardinalPeanoList digits CardinalNatural.Peano.zero))) := by
                rw [hx_toPeano, h_abs, Peano.fromCardinalNatural_successor]
              rw [h_left, hx_peano]
              symm
              exact
                (congrArg Peano.successor
                  (Peano.neg_succ
                    (Peano.fromCardinalNatural
                      (toCardinalPeanoList digits CardinalNatural.Peano.zero)))).trans
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
            simpa [absCardinalPeano] using toCardinalPeanoList_zero_of_allZero h_all
          have hx_peano : toPeano x = Peano.zero := by
            rw [hx, habs]; rfl
          rw [toPeano_minusOne, hx_peano]; rfl
      · next digits hpred =>
          have h_succ_pred : successorList digits = ⟨x.digits.val, false⟩ := by
            have h := successorList_predecessorList x.digits.val
            simpa [hpred] using h
          have h_abs :
              absCardinalPeano x =
                (toCardinalPeanoList digits CardinalNatural.Peano.zero).successor := by
            have hsucc :=
              successorList_toCardinalPeanoList digits CardinalNatural.Peano.zero
            rw [h_succ_pred] at hsucc
            dsimp only at hsucc
            simpa [absCardinalPeano] using hsucc
          split
          · next h_zero =>
              have hdigits0 := toCardinalPeanoList_zero_of_allZero h_zero
              have habs : absCardinalPeano x = CardinalNatural.Peano.one := by
                rw [h_abs, hdigits0]; rfl
              have hx_peano : toPeano x = Peano.one := by
                rw [hx, habs]; rfl
              rw [toPeano_zero, hx_peano]; rfl
          · next h_zero =>
              rw [hx]
              change Peano.fromCardinalNatural
                  (toCardinalPeanoList digits CardinalNatural.Peano.zero) =
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
            simpa [absCardinalPeano] using toCardinalPeanoList_zero_of_allZero h_all
          have hx_peano : toPeano x = Peano.zero := by
            rw [hx, habs]; rfl
          rw [toPeano_minusOne, hx_peano]; rfl
      · next digits hpred =>
          have h_succ_pred : successorList digits = ⟨x.digits.val, false⟩ := by
            have h := successorList_predecessorList x.digits.val
            simpa [hpred] using h
          have h_abs :
              absCardinalPeano x =
                (toCardinalPeanoList digits CardinalNatural.Peano.zero).successor := by
            have hsucc :=
              successorList_toCardinalPeanoList digits CardinalNatural.Peano.zero
            rw [h_succ_pred] at hsucc
            dsimp only at hsucc
            simpa [absCardinalPeano] using hsucc
          split
          · next h_zero =>
              have hdigits0 := toCardinalPeanoList_zero_of_allZero h_zero
              have habs : absCardinalPeano x = CardinalNatural.Peano.one := by
                rw [h_abs, hdigits0]; rfl
              have hx_peano : toPeano x = Peano.one := by
                rw [hx, habs]; rfl
              rw [toPeano_zero, hx_peano]; rfl
          · next h_zero =>
              rw [hx]
              change Peano.fromCardinalNatural
                  (toCardinalPeanoList digits CardinalNatural.Peano.zero) =
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
          have h_list := toCardinalPeanoList_of_successorList x.digits.val
          rw [hsucc] at h_list
          dsimp only at h_list
          rw [hx_toPeano]
          change Peano.negate
              (Peano.fromCardinalNatural
                (toCardinalPeanoList
                  (Sequences.List.firstElement
                    ⟨CardinalNatural.Peano.one, CardinalNatural.Peano.one_lt_ten⟩ digits)
                  CardinalNatural.Peano.zero)) =
            (Peano.negate (Peano.fromCardinalNatural (absCardinalPeano x))).predecessor
          have habs :
              toCardinalPeanoList
                  (Sequences.List.firstElement
                    ⟨CardinalNatural.Peano.one, CardinalNatural.Peano.one_lt_ten⟩ digits)
                  CardinalNatural.Peano.zero =
                (absCardinalPeano x).successor := by
            simpa [absCardinalPeano, toCardinalPeanoList,
              CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.zero_add] using h_list
          rw [habs, Peano.fromCardinalNatural_successor]
          exact Peano.neg_succ _
      · next digits hsucc =>
          have h_list := toCardinalPeanoList_of_successorList x.digits.val
          rw [hsucc] at h_list
          dsimp only at h_list
          rw [hx_toPeano]
          change Peano.negate
              (Peano.fromCardinalNatural
                (toCardinalPeanoList digits CardinalNatural.Peano.zero)) =
            (Peano.negate (Peano.fromCardinalNatural (absCardinalPeano x))).predecessor
          have habs :
              toCardinalPeanoList digits CardinalNatural.Peano.zero =
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

theorem predecessorList_successorList (a : Sequences.List Digit) :
    predecessorList (successorList a).1 = ⟨a, (successorList a).2⟩ := by
  induction a with
  | empty => rfl
  | firstElement d ds ih =>
      unfold successorList
      cases h_successor : successorList ds with
      | mk digits carry =>
          rw [h_successor] at ih
          cases carry with
          | false =>
              simp_all [predecessorList]
          | true =>
              by_cases hlt :
                  CardinalNatural.Peano.isLessThan d.val.successor CardinalNatural.Peano.ten = true
              · simp [hlt, predecessorList] at ih ⊢
                simp_all
                exact Subtype.ext rfl
              · have hfalse :
                    CardinalNatural.Peano.isLessThan d.val.successor CardinalNatural.Peano.ten =
                      false := by
                  cases h : CardinalNatural.Peano.isLessThan d.val.successor
                      CardinalNatural.Peano.ten with
                  | false => rfl
                  | true => contradiction
                have hd : d.val = CardinalNatural.Peano.nine :=
                  digit_val_eq_nine_of_not_successor_lt_ten d hfalse
                simp [hfalse, predecessorList] at ih ⊢
                simp_all
                exact Subtype.ext hd.symm

theorem normalizeList_eq_zero_of_allZero (sign : Option Sign) {a : Sequences.List Digit}
    (h : AllZero a) : normalizeList sign a = zero := by
  induction a with
  | empty => rfl
  | firstElement d ds ih =>
      unfold normalizeList
      have hd : d.val = CardinalNatural.Peano.zero := h.1
      rw [if_pos hd]
      exact ih h.2

theorem normalize_eq_zero_of_allZero (a : Decimal) (h : AllZero a.digits.val) :
    a.normalize = zero := by
  unfold normalize
  exact normalizeList_eq_zero_of_allZero a.sign h

theorem normalizeList_cons_zero (sign : Option Sign) (d : Digit) (ds : Sequences.List Digit)
    (hd : d.val = CardinalNatural.Peano.zero) :
    normalizeList sign (Sequences.List.firstElement d ds) = normalizeList sign ds := by
  simp [normalizeList, hd]

theorem successorList_carry_false_of_allZero {a : Sequences.List Digit}
    (ha : a ≠ Sequences.List.empty) (h : AllZero a) :
    (successorList a).2 = false := by
  induction a with
  | empty => exact False.elim (ha rfl)
  | firstElement d ds ih =>
      have hd : d.val = CardinalNatural.Peano.zero := h.1
      cases ds with
      | empty =>
          simp only [successorList, hd]
          have hlt : CardinalNatural.Peano.isLessThan
              CardinalNatural.Peano.zero.successor CardinalNatural.Peano.ten = true := by
            rw [CardinalNatural.Peano.isLessThan_eq_true_iff_lt]
            exact CardinalNatural.Peano.one_lt_ten
          simp [hlt]
      | firstElement d' ds' =>
          have ih' := ih (by intro h; cases h) h.2
          unfold successorList
          cases hds : successorList (Sequences.List.firstElement d' ds') with
          | mk digits carry =>
              have hc : carry = false := by
                simpa [hds] using ih'
              simp [hc]

theorem not_allZero_cons_zero_of_successorList_carry {a digits : Sequences.List Digit}
    (ha : a ≠ Sequences.List.empty) (h : successorList a = ⟨digits, true⟩) :
    ¬ AllZero (Sequences.List.firstElement zeroDigit a) := by
  intro hall
  have hcarry := successorList_carry_false_of_allZero ha hall.2
  rw [h] at hcarry
  cases hcarry

theorem predecessorList_of_successorList_carry {a digits : Sequences.List Digit}
    (h : successorList a = ⟨digits, true⟩) :
    predecessorList (Sequences.List.firstElement oneDigit digits) =
      ⟨Sequences.List.firstElement zeroDigit a, false⟩ := by
  have h_pred : predecessorList digits = ⟨a, true⟩ := by
    have h' := predecessorList_successorList a
    simpa [h] using h'
  unfold predecessorList
  rw [show predecessorList digits = ⟨a, true⟩ from h_pred]
  dsimp only [oneDigit]
  rfl

theorem normalize_zero : zero.normalize = zero := rfl
theorem normalize_minusOne : minusOne.normalize = minusOne := rfl

theorem negate_negate (x : Decimal) : -(-x) ≈ x := by
  change (-(-x)).normalize = x.normalize
  by_cases h : AllZero x.digits.val
  · have hx : (-x) = zero := by
      simp only [Neg.neg]
      unfold Decimal.negate
      simp only [h, ↓reduceIte]
    rw [hx, negate_zero, normalize_zero, normalize_eq_zero_of_allZero x h]
  · cases hsign : x.sign with
    | none =>
        rw [negate_of_not_allZero_none x h hsign, negate_minus_digits x.digits h]
        unfold normalize
        rw [hsign]
    | some s =>
        cases s with
        | plus =>
            rw [negate_of_not_allZero_plus x h hsign, negate_minus_digits x.digits h]
            unfold normalize
            rw [hsign, normalizeList_plus_eq_none]
        | minus =>
            rw [negate_of_not_allZero_minus x h hsign, negate_none_digits x.digits h]
            unfold normalize
            rw [hsign]

theorem predecessor_one : predecessor one = zero := by
  native_decide

theorem predecessor_zero : predecessor zero = minusOne := by
  native_decide

/-- Successor of an all-zero list without overflow normalizes (as negative) to `-1`. -/
theorem normalizeList_minus_of_successorList_allZero
    {digits a : Sequences.List Digit}
    (h : successorList digits = ⟨a, false⟩) (hzero : AllZero digits) :
    normalizeList (some Sign.minus) a = minusOne := by
  induction digits generalizing a with
  | empty =>
      cases h
  | firstElement d ds ih =>
      have hd : d.val = CardinalNatural.Peano.zero := hzero.1
      unfold successorList at h
      cases hds : successorList ds with
      | mk digs carry =>
          cases carry with
          | true =>
              have hlt : CardinalNatural.Peano.isLessThan
                  CardinalNatural.Peano.zero.successor CardinalNatural.Peano.ten = true := by
                rw [CardinalNatural.Peano.isLessThan_eq_true_iff_lt]
                exact CardinalNatural.Peano.one_lt_ten
              simp [hd, hds, hlt] at h
              cases h
              -- a = 1::digs; need digs empty (only empty AllZero has carry true)
              cases ds with
              | empty =>
                  simp [successorList] at hds
                  cases hds
                  rfl
              | firstElement _ _ =>
                  have hc := successorList_carry_false_of_allZero (by intro h; cases h) hzero.2
                  rw [hds] at hc
                  cases hc
          | false =>
              simp [hds] at h
              cases h
              -- a = 0::digs; strip leading zero
              rw [normalizeList_cons_zero (some Sign.minus) d digs hd]
              exact ih hds hzero.2

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
                  unfold normalize
                  rw [hsign, normalizeList_cons_zero none zeroDigit a.digits.val rfl]
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
                      unfold normalize
                      rw [hsign]

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
                  unfold normalize
                  rw [hsign, normalizeList_cons_zero (some Sign.plus) zeroDigit a.digits.val rfl]
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
                      unfold normalize
                      rw [hsign]

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
              unfold normalize
              rw [hsign]
              exact (normalizeList_minus_of_successorList_allZero h_succ hzero).symm
          · -- not AllZero → successor = ⟨minus, digits⟩ → predecessor restores a
            next hzero =>
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
                      unfold normalize
                      rw [hsign]
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
  native_decide

theorem successor_zero : successor zero = one := by
  native_decide

/-- Dual: when successorList of all-zeros has no carry into a leading 1 for the
    non-negative predecessor path that lands on zero. -/
theorem normalizeList_of_successorList_allZero
    (sign : Option Sign) {digits a : Sequences.List Digit}
    (h : successorList digits = ⟨a, false⟩) (hzero : AllZero digits) :
    normalizeList sign a = normalizeList sign (Sequences.List.firstElement oneDigit Sequences.List.empty) := by
  induction digits generalizing a with
  | empty =>
      cases h
  | firstElement d ds ih =>
      have hd : d.val = CardinalNatural.Peano.zero := hzero.1
      unfold successorList at h
      cases hds : successorList ds with
      | mk digs carry =>
          cases carry with
          | true =>
              have hlt : CardinalNatural.Peano.isLessThan
                  CardinalNatural.Peano.zero.successor CardinalNatural.Peano.ten = true := by
                rw [CardinalNatural.Peano.isLessThan_eq_true_iff_lt]
                exact CardinalNatural.Peano.one_lt_ten
              simp [hd, hds, hlt] at h
              cases h
              cases ds with
              | empty =>
                  simp [successorList] at hds
                  cases hds
                  rfl
              | firstElement _ _ =>
                  have hc := successorList_carry_false_of_allZero (by intro h; cases h) hzero.2
                  rw [hds] at hc
                  cases hc
          | false =>
              simp [hds] at h
              cases h
              rw [normalizeList_cons_zero sign d digs hd]
              exact ih hds hzero.2

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
              rw [successor_zero]
              -- one.normalize = one; a.normalize = normalizeList none a.digits = one
              unfold normalize one
              rw [hsign]
              have hnorm := normalizeList_of_successorList_allZero none h_succ hzero
              simpa [normalizeList, oneDigit] using hnorm.symm
          · -- not AllZero: predecessor = ⟨none, digits⟩
            next hzero =>
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
                      unfold normalize
                      rw [hsign]

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
              rw [successor_zero]
              unfold normalize one
              rw [hsign]
              have hnorm := normalizeList_of_successorList_allZero (some Sign.plus) h_succ hzero
              -- normalizeList plus [1] = ⟨none, [1]⟩ = one form
              simpa [normalizeList, oneDigit] using hnorm.symm
          · next hzero =>
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
                      unfold normalize
                      rw [hsign]

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
                  unfold normalize
                  rw [hsign, normalizeList_cons_zero (some Sign.minus) zeroDigit a.digits.val rfl]
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
                      -- But a has minus sign and all-zero digits → a.normalize = zero
                      -- Wait: if AllZero a.digits, can predecessorList digits = ⟨a.digits, false⟩?
                      -- Yes when digits is successor of zeros... 
                      -- Actually digs = a.digits which is AllZero.
                      -- successor = zero. Need zero ≈ a, i.e. a.normalize = zero.
                      have hnorm := normalize_eq_zero_of_allZero a hzero
                      rw [normalize_zero, hnorm]
                  · next hzero =>
                      unfold normalize
                      rw [hsign]
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


end Decimal

end ZeroMath.Numbers.Integer
