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

/-- Absolute value of a decimal integer: drop the sign, keeping the same digits. -/
def absoluteValue (a : Decimal) : Decimal :=
  ⟨none, a.digits⟩

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

/-- Strict order on decimal integers, via their Peano representation. -/
def LessThan (x y : Decimal) : Prop :=
  x.toPeano < y.toPeano

instance : LT Decimal where
  lt := LessThan

/-- Digit-wise MSD-first comparison of equal-length digit lists. -/
def isLessThanAlignedLists (x y : Sequences.List Digit)
    (h : Sequences.List.SameLength x y) : Bool :=
  match x, y with
  | .empty, .empty => false
  | .firstElement dx dxs, .firstElement dy dys =>
      if _ : CardinalNatural.Peano.isLessThan dx.val dy.val then
        true
      else if _ : CardinalNatural.Peano.isLessThan dy.val dx.val then
        false
      else
        isLessThanAlignedLists dxs dys (Sequences.List.sameLength_of_firstElement h)
  | .empty, .firstElement _ _ => False.elim (by cases h)
  | .firstElement _ _, .empty => False.elim (by cases h)

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

/-- Prop-level MSD-first comparison of equal-length digit lists. -/
def LessThanAlignedLists (x y : Sequences.List Digit)
    (h : Sequences.List.SameLength x y) : Prop :=
  match x, y with
  | .empty, .empty => False
  | .firstElement d1 ds1, .firstElement d2 ds2 =>
      d1.val < d2.val ∨
        (d1.val = d2.val ∧
          LessThanAlignedLists ds1 ds2 (Sequences.List.sameLength_of_firstElement h))
  | .empty, .firstElement _ _ => False.elim (by cases h)
  | .firstElement _ _, .empty => False.elim (by cases h)

theorem isLessThanAlignedLists_iff_lessThanAlignedLists (x y : Sequences.List Digit)
    (h : Sequences.List.SameLength x y) :
    isLessThanAlignedLists x y h ↔ LessThanAlignedLists x y h := by
  induction h using Sequences.List.SameLength.induction with
  | empty =>
      simp [isLessThanAlignedLists, LessThanAlignedLists]
  | firstElement htail ih =>
      rename_i dx dy dxs dys
      unfold isLessThanAlignedLists LessThanAlignedLists
      split
      · next h_dx_lt_dy_bool =>
          constructor
          · intro _
            exact Or.inl ((CardinalNatural.Peano.isLessThan_eq_true_iff_lt _ _).mp
              h_dx_lt_dy_bool)
          · intro _
            rfl
      · next h_not_dx_lt_dy_bool =>
          split
          · next h_dy_lt_dx_bool =>
              constructor
              · intro h_false
                cases h_false
              · intro h_less
                have h_not_dx_lt_dy : ¬ dx.val < dy.val :=
                  (CardinalNatural.Peano.isLessThan_eq_false_iff_not_lt _ _).mp
                    (eq_false_of_ne_true h_not_dx_lt_dy_bool)
                have h_dy_lt_dx : dy.val < dx.val :=
                  (CardinalNatural.Peano.isLessThan_eq_true_iff_lt _ _).mp h_dy_lt_dx_bool
                cases h_less with
                | inl h_dx_lt_dy =>
                    exact False.elim (h_not_dx_lt_dy h_dx_lt_dy)
                | inr h_eq_tail =>
                    obtain ⟨h_dx_eq_dy, _⟩ := h_eq_tail
                    rw [h_dx_eq_dy] at h_dy_lt_dx
                    exact False.elim (CardinalNatural.Peano.not_lt_self dy.val h_dy_lt_dx)
          · next h_not_dy_lt_dx_bool =>
              have h_not_dx_lt_dy : ¬ dx.val < dy.val :=
                (CardinalNatural.Peano.isLessThan_eq_false_iff_not_lt _ _).mp
                  (eq_false_of_ne_true h_not_dx_lt_dy_bool)
              have h_not_dy_lt_dx : ¬ dy.val < dx.val :=
                (CardinalNatural.Peano.isLessThan_eq_false_iff_not_lt _ _).mp
                  (eq_false_of_ne_true h_not_dy_lt_dx_bool)
              have h_dx_eq_dy : dx.val = dy.val := by
                cases CardinalNatural.Peano.trichotomy_or dx.val dy.val with
                | inl h_dx_lt_dy =>
                    exact False.elim (h_not_dx_lt_dy h_dx_lt_dy)
                | inr h_eq_or_gt =>
                    cases h_eq_or_gt with
                    | inl h_eq => exact h_eq
                    | inr h_dy_lt_dx =>
                        exact False.elim (h_not_dy_lt_dx h_dy_lt_dx)
              constructor
              · intro h_tail_bool
                exact Or.inr ⟨h_dx_eq_dy, ih.mp h_tail_bool⟩
              · intro h_less
                cases h_less with
                | inl h_dx_lt_dy =>
                    exact False.elim (h_not_dx_lt_dy h_dx_lt_dy)
                | inr h_eq_tail =>
                    exact ih.mpr h_eq_tail.2

theorem toCardinalPeanoList_acc_split (l : Sequences.List Digit)
    (acc : CardinalNatural.Peano) :
    toCardinalPeanoList l acc =
      acc * CardinalNatural.Peano.tenPow l.length +
        toCardinalPeanoList l CardinalNatural.Peano.zero := by
  induction l generalizing acc with
  | empty =>
      simp only [toCardinalPeanoList, Sequences.List.length, CardinalNatural.Peano.tenPow,
        CardinalNatural.Peano.multiply_one, CardinalNatural.Peano.add_zero]
  | firstElement d ds ih =>
      simp only [toCardinalPeanoList, Sequences.List.length,
        CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.zero_add]
      rw [ih (acc * CardinalNatural.Peano.ten + d.val), ih d.val,
        CardinalNatural.Peano.tenPow_add_one,
        CardinalNatural.Peano.multiply_distributive_over_add_left,
        CardinalNatural.Peano.multiply_associative,
        CardinalNatural.Peano.add_associative]

theorem toCardinalPeanoList_firstElement (d : Digit) (ds : Sequences.List Digit) :
    toCardinalPeanoList (Sequences.List.firstElement d ds) CardinalNatural.Peano.zero =
      d.val * CardinalNatural.Peano.tenPow ds.length +
        toCardinalPeanoList ds CardinalNatural.Peano.zero := by
  change toCardinalPeanoList ds
      (CardinalNatural.Peano.zero * CardinalNatural.Peano.ten + d.val) = _
  rw [CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.zero_add]
  exact toCardinalPeanoList_acc_split ds d.val

theorem toCardinalPeanoList_lt_tenPow (l : Sequences.List Digit) :
    toCardinalPeanoList l CardinalNatural.Peano.zero <
      CardinalNatural.Peano.tenPow l.length := by
  induction l with
  | empty =>
      simp only [toCardinalPeanoList, Sequences.List.length, CardinalNatural.Peano.tenPow]
      exact CardinalNatural.Peano.LessThan.base
  | firstElement d ds ih =>
      simp only [toCardinalPeanoList, Sequences.List.length,
        CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.zero_add]
      rw [toCardinalPeanoList_acc_split ds d.val, CardinalNatural.Peano.tenPow_add_one]
      have h1 :
          d.val * CardinalNatural.Peano.tenPow ds.length +
              toCardinalPeanoList ds CardinalNatural.Peano.zero <
            d.val * CardinalNatural.Peano.tenPow ds.length +
              CardinalNatural.Peano.tenPow ds.length :=
        CardinalNatural.Peano.add_lt_add_left ih
          (d.val * CardinalNatural.Peano.tenPow ds.length)
      have h2 :
          d.val * CardinalNatural.Peano.tenPow ds.length +
              CardinalNatural.Peano.tenPow ds.length =
            d.val.successor * CardinalNatural.Peano.tenPow ds.length :=
        (CardinalNatural.Peano.successor_multiply d.val
          (CardinalNatural.Peano.tenPow ds.length)).symm
      have h3 :
          d.val.successor * CardinalNatural.Peano.tenPow ds.length ≤
            CardinalNatural.Peano.ten * CardinalNatural.Peano.tenPow ds.length :=
        CardinalNatural.Peano.multiply_le_mul_left
          (CardinalNatural.Peano.succ_le_of_lt d.property)
          (CardinalNatural.Peano.tenPow ds.length)
      rw [h2] at h1
      cases h3 with
      | inl hlt => exact CardinalNatural.Peano.lt_trans h1 hlt
      | inr heq => rw [← heq]; exact h1

theorem toCardinalPeanoList_padAtStart_zeroDigit (l : Sequences.List Digit)
    (n : CardinalNatural.Peano) :
    toCardinalPeanoList (Sequences.List.padAtStart l zeroDigit n)
        CardinalNatural.Peano.zero =
      toCardinalPeanoList l CardinalNatural.Peano.zero := by
  induction n generalizing l with
  | zero => rfl
  | successor n ih =>
      unfold Sequences.List.padAtStart
      rw [ih]
      rfl

theorem toCardinalPeanoList_padAtStartToSameLength_fst (a b : Sequences.List Digit) :
    toCardinalPeanoList
        (Sequences.List.padAtStartToSameLength a b zeroDigit).1
        CardinalNatural.Peano.zero =
      toCardinalPeanoList a CardinalNatural.Peano.zero := by
  unfold Sequences.List.padAtStartToSameLength
  dsimp only
  split
  · rfl
  · exact toCardinalPeanoList_padAtStart_zeroDigit _ _

theorem toCardinalPeanoList_padAtStartToSameLength_snd (a b : Sequences.List Digit) :
    toCardinalPeanoList
        (Sequences.List.padAtStartToSameLength a b zeroDigit).2
        CardinalNatural.Peano.zero =
      toCardinalPeanoList b CardinalNatural.Peano.zero := by
  unfold Sequences.List.padAtStartToSameLength
  dsimp only
  split
  · exact toCardinalPeanoList_padAtStart_zeroDigit _ _
  · rfl

theorem LessThanAlignedLists_toCardinalPeanoList_lt {x y : Sequences.List Digit}
    (h : Sequences.List.SameLength x y)
    (hlt : LessThanAlignedLists x y h) :
    toCardinalPeanoList x CardinalNatural.Peano.zero <
      toCardinalPeanoList y CardinalNatural.Peano.zero := by
  induction h using Sequences.List.SameLength.induction with
  | empty =>
      cases hlt
  | firstElement htail ih =>
      rename_i dx dy dxs dys
      simp only [toCardinalPeanoList_firstElement]
      cases hlt with
      | inl h_digit =>
          have h_tail_lt :
              toCardinalPeanoList dxs CardinalNatural.Peano.zero <
                CardinalNatural.Peano.tenPow dxs.length :=
            toCardinalPeanoList_lt_tenPow dxs
          have h_lt_next :
              dx.val * CardinalNatural.Peano.tenPow dxs.length +
                  toCardinalPeanoList dxs CardinalNatural.Peano.zero <
                dx.val * CardinalNatural.Peano.tenPow dxs.length +
                  CardinalNatural.Peano.tenPow dxs.length :=
            CardinalNatural.Peano.add_lt_add_left h_tail_lt _
          have h_next_eq :
              dx.val * CardinalNatural.Peano.tenPow dxs.length +
                  CardinalNatural.Peano.tenPow dxs.length =
                dx.val.successor * CardinalNatural.Peano.tenPow dxs.length :=
            (CardinalNatural.Peano.successor_multiply dx.val _).symm
          rw [h_next_eq] at h_lt_next
          have h_le_digit :
              dx.val.successor * CardinalNatural.Peano.tenPow dxs.length ≤
                dy.val * CardinalNatural.Peano.tenPow dxs.length :=
            CardinalNatural.Peano.multiply_le_mul_left
              (CardinalNatural.Peano.succ_le_of_lt h_digit) _
          have h_le_value :
              dy.val * CardinalNatural.Peano.tenPow dxs.length ≤
                dy.val * CardinalNatural.Peano.tenPow dxs.length +
                  toCardinalPeanoList dys CardinalNatural.Peano.zero :=
            CardinalNatural.Peano.le_add_self_left _ _
          rw [← htail]
          exact CardinalNatural.Peano.lt_of_lt_of_le h_lt_next
            (CardinalNatural.Peano.le_trans h_le_digit h_le_value)
      | inr h_eq_tail =>
          obtain ⟨h_digit_eq, h_tail_lt_aligned⟩ := h_eq_tail
          rw [h_digit_eq, htail]
          exact CardinalNatural.Peano.add_lt_add_left (ih h_tail_lt_aligned) _

theorem LessThanAlignedLists_of_toCardinalPeanoList_lt {x y : Sequences.List Digit}
    (h : Sequences.List.SameLength x y)
    (hlt : toCardinalPeanoList x CardinalNatural.Peano.zero <
      toCardinalPeanoList y CardinalNatural.Peano.zero) :
    LessThanAlignedLists x y h := by
  induction h using Sequences.List.SameLength.induction with
  | empty =>
      exact False.elim (CardinalNatural.Peano.not_lt_self _ hlt)
  | firstElement htail ih =>
      rename_i dx dy dxs dys
      simp only [toCardinalPeanoList_firstElement] at hlt
      rw [htail] at hlt
      cases CardinalNatural.Peano.trichotomy_or dx.val dy.val with
      | inl h_digit_lt =>
          exact Or.inl h_digit_lt
      | inr h_eq_or_gt =>
          cases h_eq_or_gt with
          | inl h_digit_eq =>
              apply Or.inr
              constructor
              · exact h_digit_eq
              · apply ih
                have hlt_tail_sum :
                    dy.val * CardinalNatural.Peano.tenPow dys.length +
                        toCardinalPeanoList dxs CardinalNatural.Peano.zero <
                      dy.val * CardinalNatural.Peano.tenPow dys.length +
                        toCardinalPeanoList dys CardinalNatural.Peano.zero := by
                  rwa [h_digit_eq] at hlt
                rw [CardinalNatural.Peano.add_commutative
                      (dy.val * CardinalNatural.Peano.tenPow dys.length),
                    CardinalNatural.Peano.add_commutative
                      (dy.val * CardinalNatural.Peano.tenPow dys.length)] at hlt_tail_sum
                exact CardinalNatural.Peano.add_lt_cancel_right hlt_tail_sum
          | inr h_digit_gt =>
              have h_tail_y_lt :
                  toCardinalPeanoList dys CardinalNatural.Peano.zero <
                    CardinalNatural.Peano.tenPow dys.length :=
                toCardinalPeanoList_lt_tenPow dys
              have h_y_lt_next :
                  dy.val * CardinalNatural.Peano.tenPow dys.length +
                      toCardinalPeanoList dys CardinalNatural.Peano.zero <
                    dy.val * CardinalNatural.Peano.tenPow dys.length +
                      CardinalNatural.Peano.tenPow dys.length :=
                CardinalNatural.Peano.add_lt_add_left h_tail_y_lt _
              have h_next_eq :
                  dy.val * CardinalNatural.Peano.tenPow dys.length +
                      CardinalNatural.Peano.tenPow dys.length =
                    dy.val.successor * CardinalNatural.Peano.tenPow dys.length :=
                (CardinalNatural.Peano.successor_multiply dy.val _).symm
              rw [h_next_eq] at h_y_lt_next
              have h_le_digit :
                  dy.val.successor * CardinalNatural.Peano.tenPow dys.length ≤
                    dx.val * CardinalNatural.Peano.tenPow dys.length :=
                CardinalNatural.Peano.multiply_le_mul_left
                  (CardinalNatural.Peano.succ_le_of_lt h_digit_gt) _
              have h_le_x :
                  dx.val * CardinalNatural.Peano.tenPow dys.length ≤
                    dx.val * CardinalNatural.Peano.tenPow dys.length +
                      toCardinalPeanoList dxs CardinalNatural.Peano.zero :=
                CardinalNatural.Peano.le_add_self_left _ _
              have h_y_lt_x :
                  dy.val * CardinalNatural.Peano.tenPow dys.length +
                      toCardinalPeanoList dys CardinalNatural.Peano.zero <
                    dx.val * CardinalNatural.Peano.tenPow dys.length +
                      toCardinalPeanoList dxs CardinalNatural.Peano.zero :=
                CardinalNatural.Peano.lt_of_lt_of_le h_y_lt_next
                  (CardinalNatural.Peano.le_trans h_le_digit h_le_x)
              exact False.elim
                (CardinalNatural.Peano.not_lt_self _
                  (CardinalNatural.Peano.lt_trans hlt h_y_lt_x))

theorem absCardinalPeano_lt_of_lessThanAlignedLists_padded {a b : Decimal}
    (h : LessThanAlignedLists
      (Sequences.List.padAtStartToSameLength a.digits.val b.digits.val zeroDigit).1
      (Sequences.List.padAtStartToSameLength a.digits.val b.digits.val zeroDigit).2
      (Sequences.List.padAtStartToSameLength_sameLength a.digits.val b.digits.val
        zeroDigit)) :
    absCardinalPeano a < absCardinalPeano b := by
  have h_padded := LessThanAlignedLists_toCardinalPeanoList_lt
    (Sequences.List.padAtStartToSameLength_sameLength a.digits.val b.digits.val
      zeroDigit) h
  change toCardinalPeanoList a.digits.val CardinalNatural.Peano.zero <
    toCardinalPeanoList b.digits.val CardinalNatural.Peano.zero
  rw [← toCardinalPeanoList_padAtStartToSameLength_fst a.digits.val b.digits.val,
    ← toCardinalPeanoList_padAtStartToSameLength_snd a.digits.val b.digits.val]
  exact h_padded

theorem lessThanAlignedLists_padded_of_absCardinalPeano_lt {a b : Decimal}
    (h : absCardinalPeano a < absCardinalPeano b) :
    LessThanAlignedLists
      (Sequences.List.padAtStartToSameLength a.digits.val b.digits.val zeroDigit).1
      (Sequences.List.padAtStartToSameLength a.digits.val b.digits.val zeroDigit).2
      (Sequences.List.padAtStartToSameLength_sameLength a.digits.val b.digits.val
        zeroDigit) := by
  apply LessThanAlignedLists_of_toCardinalPeanoList_lt
  change toCardinalPeanoList
      (Sequences.List.padAtStartToSameLength a.digits.val b.digits.val zeroDigit).1
      CardinalNatural.Peano.zero <
    toCardinalPeanoList
      (Sequences.List.padAtStartToSameLength a.digits.val b.digits.val zeroDigit).2
      CardinalNatural.Peano.zero
  rw [toCardinalPeanoList_padAtStartToSameLength_fst a.digits.val b.digits.val,
    toCardinalPeanoList_padAtStartToSameLength_snd a.digits.val b.digits.val]
  exact h

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

theorem toCardinalPeanoList_ne_zero_of_acc_ne_zero (a : Sequences.List Digit)
    {acc : CardinalNatural.Peano} (hacc : acc ≠ CardinalNatural.Peano.zero) :
    toCardinalPeanoList a acc ≠ CardinalNatural.Peano.zero := by
  induction a generalizing acc with
  | empty => exact hacc
  | firstElement d ds ih =>
      apply ih
      intro heq
      have hten : CardinalNatural.Peano.ten ≠ CardinalNatural.Peano.zero := by
        intro hten; cases hten
      have hmul : acc * CardinalNatural.Peano.ten ≠ CardinalNatural.Peano.zero :=
        CardinalNatural.Peano.multiply_ne_zero acc CardinalNatural.Peano.ten hacc hten
      have hsum := CardinalNatural.Peano.eq_zero_of_add_eq_zero_l heq
      exact hmul hsum

theorem toCardinalPeanoList_ne_zero_of_not_allZero {a : Sequences.List Digit}
    (h : ¬ AllZero a) :
    toCardinalPeanoList a CardinalNatural.Peano.zero ≠ CardinalNatural.Peano.zero := by
  induction a with
  | empty => exact False.elim (h trivial)
  | firstElement d ds ih =>
      change toCardinalPeanoList ds
          (CardinalNatural.Peano.zero * CardinalNatural.Peano.ten + d.val) ≠
        CardinalNatural.Peano.zero
      rw [CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.zero_add]
      by_cases hd : d.val = CardinalNatural.Peano.zero
      · have hds : ¬ AllZero ds := by
          intro hds
          exact h ⟨hd, hds⟩
        rw [hd]
        exact ih hds
      · exact toCardinalPeanoList_ne_zero_of_acc_ne_zero ds hd

theorem absCardinalPeano_ne_zero_of_not_allZero {a : Decimal}
    (h : ¬ AllZero a.digits.val) :
    absCardinalPeano a ≠ CardinalNatural.Peano.zero := by
  simpa [absCardinalPeano] using toCardinalPeanoList_ne_zero_of_not_allZero h

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
                simpa [absCardinalPeano] using toCardinalPeanoList_zero_of_allZero h_all
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

theorem toCardinalPeanoList_inj_sameLength {l1 l2 : Sequences.List Digit}
    (hsl : Sequences.List.SameLength l1 l2)
    (heq : toCardinalPeanoList l1 CardinalNatural.Peano.zero =
      toCardinalPeanoList l2 CardinalNatural.Peano.zero) :
    l1 = l2 := by
  induction hsl using Sequences.List.SameLength.induction with
  | empty => rfl
  | firstElement h_tail ih =>
      rename_i d1 d2 ds1 ds2
      simp only [toCardinalPeanoList, CardinalNatural.Peano.zero_multiply,
        CardinalNatural.Peano.zero_add] at heq
      rw [toCardinalPeanoList_acc_split ds1 d1.val,
        toCardinalPeanoList_acc_split ds2 d2.val] at heq
      have h_len : ds2.length = ds1.length := h_tail.symm
      rw [h_len] at heq
      have hv1_lt :
          toCardinalPeanoList ds1 CardinalNatural.Peano.zero <
            CardinalNatural.Peano.tenPow ds1.length :=
        toCardinalPeanoList_lt_tenPow ds1
      have hv2_lt :
          toCardinalPeanoList ds2 CardinalNatural.Peano.zero <
            CardinalNatural.Peano.tenPow ds1.length := by
        rw [← h_len]; exact toCardinalPeanoList_lt_tenPow ds2
      have hd_eq : d1.val = d2.val := by
        cases CardinalNatural.Peano.trichotomy_or d1.val d2.val with
        | inl hlt =>
            exfalso
            have hchain :
                d1.val * CardinalNatural.Peano.tenPow ds1.length +
                    CardinalNatural.Peano.tenPow ds1.length ≤
                  d1.val * CardinalNatural.Peano.tenPow ds1.length +
                    toCardinalPeanoList ds1 CardinalNatural.Peano.zero := by
              have hstep1 :
                  d1.val * CardinalNatural.Peano.tenPow ds1.length +
                      CardinalNatural.Peano.tenPow ds1.length =
                    d1.val.successor * CardinalNatural.Peano.tenPow ds1.length :=
                (CardinalNatural.Peano.successor_multiply d1.val
                  (CardinalNatural.Peano.tenPow ds1.length)).symm
              have hstep2 :
                  d1.val.successor * CardinalNatural.Peano.tenPow ds1.length ≤
                    d2.val * CardinalNatural.Peano.tenPow ds1.length :=
                CardinalNatural.Peano.multiply_le_mul_left
                  (CardinalNatural.Peano.succ_le_of_lt hlt)
                  (CardinalNatural.Peano.tenPow ds1.length)
              have hstep3 :
                  d2.val * CardinalNatural.Peano.tenPow ds1.length ≤
                    d2.val * CardinalNatural.Peano.tenPow ds1.length +
                      toCardinalPeanoList ds2 CardinalNatural.Peano.zero :=
                CardinalNatural.Peano.le_add_self_left _ _
              rw [hstep1]
              exact CardinalNatural.Peano.le_trans
                (CardinalNatural.Peano.le_trans hstep2 hstep3) (Or.inr heq.symm)
            exact absurd
              (CardinalNatural.Peano.le_lt_trans
                (CardinalNatural.Peano.add_le_cancel_left hchain) hv1_lt)
              (CardinalNatural.Peano.not_lt_self
                (CardinalNatural.Peano.tenPow ds1.length))
        | inr h =>
            cases h with
            | inl heq_d => exact heq_d
            | inr hgt =>
                exfalso
                have hchain :
                    d2.val * CardinalNatural.Peano.tenPow ds1.length +
                        CardinalNatural.Peano.tenPow ds1.length ≤
                      d2.val * CardinalNatural.Peano.tenPow ds1.length +
                        toCardinalPeanoList ds2 CardinalNatural.Peano.zero := by
                  have hstep1 :
                      d2.val * CardinalNatural.Peano.tenPow ds1.length +
                          CardinalNatural.Peano.tenPow ds1.length =
                        d2.val.successor * CardinalNatural.Peano.tenPow ds1.length :=
                    (CardinalNatural.Peano.successor_multiply d2.val
                      (CardinalNatural.Peano.tenPow ds1.length)).symm
                  have hstep2 :
                      d2.val.successor * CardinalNatural.Peano.tenPow ds1.length ≤
                        d1.val * CardinalNatural.Peano.tenPow ds1.length :=
                    CardinalNatural.Peano.multiply_le_mul_left
                      (CardinalNatural.Peano.succ_le_of_lt hgt)
                      (CardinalNatural.Peano.tenPow ds1.length)
                  have hstep3 :
                      d1.val * CardinalNatural.Peano.tenPow ds1.length ≤
                        d1.val * CardinalNatural.Peano.tenPow ds1.length +
                          toCardinalPeanoList ds1 CardinalNatural.Peano.zero :=
                    CardinalNatural.Peano.le_add_self_left _ _
                  rw [hstep1]
                  exact CardinalNatural.Peano.le_trans
                    (CardinalNatural.Peano.le_trans hstep2 hstep3) (Or.inr heq)
                exact absurd
                  (CardinalNatural.Peano.le_lt_trans
                    (CardinalNatural.Peano.add_le_cancel_left hchain) hv2_lt)
                  (CardinalNatural.Peano.not_lt_self
                    (CardinalNatural.Peano.tenPow ds1.length))
      have hv_eq :
          toCardinalPeanoList ds1 CardinalNatural.Peano.zero =
            toCardinalPeanoList ds2 CardinalNatural.Peano.zero := by
        have heq' := heq
        rw [hd_eq] at heq'
        exact CardinalNatural.Peano.add_left_cancel _ _ _ heq'
      rw [Subtype.ext hd_eq, ih hv_eq]

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

theorem toCardinalPeanoList_ge_tenPow_of_ne_zero (d : Digit) (ds : Sequences.List Digit)
    (hd : d.val ≠ CardinalNatural.Peano.zero) :
    CardinalNatural.Peano.tenPow ds.length ≤
      d.val * CardinalNatural.Peano.tenPow ds.length +
        toCardinalPeanoList ds CardinalNatural.Peano.zero := by
  have hd_pos : CardinalNatural.Peano.one ≤ d.val := by
    cases h_d : d.val with
    | zero => exact absurd h_d hd
    | successor v =>
        exact CardinalNatural.Peano.succ_le_of_lt
          (CardinalNatural.Peano.zero_lt_succ v)
  have hge1 :
      CardinalNatural.Peano.one * CardinalNatural.Peano.tenPow ds.length ≤
        d.val * CardinalNatural.Peano.tenPow ds.length :=
    CardinalNatural.Peano.multiply_le_mul_left hd_pos
      (CardinalNatural.Peano.tenPow ds.length)
  rw [CardinalNatural.Peano.one_multiply] at hge1
  exact CardinalNatural.Peano.le_trans hge1
    (CardinalNatural.Peano.le_add_self_left _ _)

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
              simp only [isNormalized] at hnorm
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
              cases val with
              | empty => exact False.elim (hprop rfl)
              | firstElement digit rest =>
                  cases rest with
                  | empty =>
                      have hdig : digit.val = CardinalNatural.Peano.zero := by
                        simp only [absCardinalPeano, toCardinalPeanoList,
                          CardinalNatural.Peano.zero_multiply,
                          CardinalNatural.Peano.zero_add] at h
                        exact h
                      have hdigit : digit = zeroDigit := Subtype.ext hdig
                      subst hdigit
                      rfl
                  | firstElement rest_d rest_ds =>
                      simp only [isNormalized] at hd
                      have hne : digit.val ≠ CardinalNatural.Peano.zero :=
                        of_decide_eq_true hd
                      have hne_abs :
                          absCardinalPeano
                            ⟨none, ⟨Sequences.List.firstElement digit
                              (Sequences.List.firstElement rest_d rest_ds), hprop⟩⟩ ≠
                            CardinalNatural.Peano.zero :=
                        absCardinalPeano_ne_zero_of_not_allZero (fun hall => hne hall.1)
                      exact False.elim (hne_abs h)
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
      cases rest with
      | empty =>
          intro hdig
          apply hne_abs
          simp only [absCardinalPeano, toCardinalPeanoList, hdig,
            CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.zero_add]
      | firstElement _ _ =>
          simp only [isNormalized] at hnorm
          exact of_decide_eq_true hnorm
  | some s =>
      cases s with
      | plus =>
          simp only [isNormalized] at hnorm
          cases hnorm
      | minus =>
          simp only [isNormalized] at hnorm
          exact of_decide_eq_true hnorm

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
                          have hda_ne : da.val ≠ CardinalNatural.Peano.zero :=
                            leadingDigit_ne_zero_of_normalized_ne_zero_abs ha ha0
                          have hdb_ne : db.val ≠ CardinalNatural.Peano.zero :=
                            leadingDigit_ne_zero_of_normalized_ne_zero_abs hb
                              (by intro h; exact ha0 (heq.trans h))
                          have heq_raw :
                              toCardinalPeanoList
                                  (Sequences.List.firstElement da das)
                                  CardinalNatural.Peano.zero =
                                toCardinalPeanoList
                                  (Sequences.List.firstElement db dbs)
                                  CardinalNatural.Peano.zero := by
                            simpa [absCardinalPeano] using heq
                          have heq_split := heq_raw
                          rw [toCardinalPeanoList_firstElement,
                            toCardinalPeanoList_firstElement] at heq_split
                          have h_len : das.length = dbs.length := by
                            cases CardinalNatural.Peano.trichotomy_or das.length dbs.length with
                            | inl hlt =>
                                have hval_lt :
                                    da.val * CardinalNatural.Peano.tenPow das.length +
                                        toCardinalPeanoList das CardinalNatural.Peano.zero <
                                      CardinalNatural.Peano.ten *
                                        CardinalNatural.Peano.tenPow das.length := by
                                  have hstep1 :
                                      da.val * CardinalNatural.Peano.tenPow das.length +
                                          toCardinalPeanoList das CardinalNatural.Peano.zero <
                                        da.val * CardinalNatural.Peano.tenPow das.length +
                                          CardinalNatural.Peano.tenPow das.length :=
                                    CardinalNatural.Peano.add_lt_add_left
                                      (toCardinalPeanoList_lt_tenPow das) _
                                  have hstep2 :
                                      da.val * CardinalNatural.Peano.tenPow das.length +
                                          CardinalNatural.Peano.tenPow das.length =
                                        da.val.successor *
                                          CardinalNatural.Peano.tenPow das.length :=
                                    (CardinalNatural.Peano.successor_multiply da.val _).symm
                                  have hstep3 :
                                      da.val.successor *
                                          CardinalNatural.Peano.tenPow das.length ≤
                                        CardinalNatural.Peano.ten *
                                          CardinalNatural.Peano.tenPow das.length :=
                                    CardinalNatural.Peano.multiply_le_mul_left
                                      (CardinalNatural.Peano.succ_le_of_lt da.property) _
                                  rw [hstep2] at hstep1
                                  cases hstep3 with
                                  | inl hlt3 =>
                                      exact CardinalNatural.Peano.lt_trans hstep1 hlt3
                                  | inr heq3 =>
                                      rw [← heq3]; exact hstep1
                                have htenPow_le :
                                    CardinalNatural.Peano.tenPow das.length.successor ≤
                                      CardinalNatural.Peano.tenPow dbs.length :=
                                  CardinalNatural.Peano.tenPow_monotone
                                    (CardinalNatural.Peano.succ_le_of_lt hlt)
                                have hval_ge :
                                    CardinalNatural.Peano.tenPow dbs.length ≤
                                      db.val * CardinalNatural.Peano.tenPow dbs.length +
                                        toCardinalPeanoList dbs
                                          CardinalNatural.Peano.zero :=
                                  toCardinalPeanoList_ge_tenPow_of_ne_zero db dbs hdb_ne
                                exact absurd
                                  (CardinalNatural.Peano.le_lt_trans
                                    (CardinalNatural.Peano.le_trans htenPow_le
                                      (CardinalNatural.Peano.le_trans hval_ge
                                        (Or.inr heq_split.symm)))
                                    hval_lt)
                                  (CardinalNatural.Peano.not_lt_self _)
                            | inr h =>
                                cases h with
                                | inl heq_l => exact heq_l
                                | inr hgt =>
                                    have hval_lt :
                                        db.val * CardinalNatural.Peano.tenPow dbs.length +
                                            toCardinalPeanoList dbs
                                              CardinalNatural.Peano.zero <
                                          CardinalNatural.Peano.ten *
                                            CardinalNatural.Peano.tenPow dbs.length := by
                                      have hstep1 :
                                          db.val * CardinalNatural.Peano.tenPow dbs.length +
                                              toCardinalPeanoList dbs
                                                CardinalNatural.Peano.zero <
                                            db.val * CardinalNatural.Peano.tenPow dbs.length +
                                              CardinalNatural.Peano.tenPow dbs.length :=
                                        CardinalNatural.Peano.add_lt_add_left
                                          (toCardinalPeanoList_lt_tenPow dbs) _
                                      have hstep2 :
                                          db.val * CardinalNatural.Peano.tenPow dbs.length +
                                              CardinalNatural.Peano.tenPow dbs.length =
                                            db.val.successor *
                                              CardinalNatural.Peano.tenPow dbs.length :=
                                        (CardinalNatural.Peano.successor_multiply
                                          db.val _).symm
                                      have hstep3 :
                                          db.val.successor *
                                              CardinalNatural.Peano.tenPow dbs.length ≤
                                            CardinalNatural.Peano.ten *
                                              CardinalNatural.Peano.tenPow dbs.length :=
                                        CardinalNatural.Peano.multiply_le_mul_left
                                          (CardinalNatural.Peano.succ_le_of_lt
                                            db.property) _
                                      rw [hstep2] at hstep1
                                      cases hstep3 with
                                      | inl hlt3 =>
                                          exact CardinalNatural.Peano.lt_trans hstep1 hlt3
                                      | inr heq3 =>
                                          rw [← heq3]; exact hstep1
                                    have htenPow_le :
                                        CardinalNatural.Peano.tenPow dbs.length.successor ≤
                                          CardinalNatural.Peano.tenPow das.length :=
                                      CardinalNatural.Peano.tenPow_monotone
                                        (CardinalNatural.Peano.succ_le_of_lt hgt)
                                    have hval_ge :
                                        CardinalNatural.Peano.tenPow das.length ≤
                                          da.val * CardinalNatural.Peano.tenPow das.length +
                                            toCardinalPeanoList das
                                              CardinalNatural.Peano.zero :=
                                      toCardinalPeanoList_ge_tenPow_of_ne_zero da das hda_ne
                                    exact absurd
                                      (CardinalNatural.Peano.le_lt_trans
                                        (CardinalNatural.Peano.le_trans htenPow_le
                                          (CardinalNatural.Peano.le_trans hval_ge
                                            (Or.inr heq_split)))
                                        hval_lt)
                                      (CardinalNatural.Peano.not_lt_self _)
                          have hsl : Sequences.List.SameLength
                              (Sequences.List.firstElement da das)
                              (Sequences.List.firstElement db dbs) :=
                            Sequences.List.sameLength_firstElement h_len
                          exact toCardinalPeanoList_inj_sameLength hsl heq_raw

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

theorem subtract_ten_lt_ten (digit_sum : CardinalNatural.Peano)
    (h_le : CardinalNatural.Peano.ten ≤ digit_sum)
    (h_lt_twenty : digit_sum < CardinalNatural.Peano.ten + CardinalNatural.Peano.ten) :
    CardinalNatural.Peano.subtract digit_sum CardinalNatural.Peano.ten h_le <
      CardinalNatural.Peano.ten :=
  CardinalNatural.Peano.subtract_lt_of_lt_add h_le h_lt_twenty

theorem digit_sum_lt_twenty (da db : CardinalNatural.Peano) (carry : Bool)
    (hda : da < CardinalNatural.Peano.ten) (hdb : db < CardinalNatural.Peano.ten) :
    da + db + (if carry then CardinalNatural.Peano.one else CardinalNatural.Peano.zero) <
      CardinalNatural.Peano.ten + CardinalNatural.Peano.ten := by
  cases carry with
  | false =>
      simp
      exact CardinalNatural.Peano.lt_trans
        (CardinalNatural.Peano.add_lt_add_right hda db)
        (CardinalNatural.Peano.add_lt_add_left hdb CardinalNatural.Peano.ten)
  | true =>
      have h_da_succ_le : da + CardinalNatural.Peano.one ≤ CardinalNatural.Peano.ten := by
        change da.successor ≤ CardinalNatural.Peano.ten
        exact CardinalNatural.Peano.succ_le_of_lt hda
      have h_sum_le :
          (da + CardinalNatural.Peano.one) + db ≤ CardinalNatural.Peano.ten + db :=
        CardinalNatural.Peano.add_le_add_right h_da_succ_le db
      have h_ten_db_lt :
          CardinalNatural.Peano.ten + db <
            CardinalNatural.Peano.ten + CardinalNatural.Peano.ten :=
        CardinalNatural.Peano.add_lt_add_left hdb CardinalNatural.Peano.ten
      simp
      rw [CardinalNatural.Peano.add_associative da db CardinalNatural.Peano.one]
      rw [CardinalNatural.Peano.add_commutative db CardinalNatural.Peano.one]
      rw [← CardinalNatural.Peano.add_associative da CardinalNatural.Peano.one db]
      exact CardinalNatural.Peano.le_lt_trans h_sum_le h_ten_db_lt

/-- Columnar addition of equal-length digit lists (least-significant digit recursion).
    The boolean is the final carry out of the most-significant column. -/
def addAlignedLists (a b : Sequences.List Digit) (h : Sequences.List.SameLength a b) :
    Sequences.List Digit × Bool :=
  match a, b with
  | .empty, .empty => ⟨Sequences.List.empty, false⟩
  | .firstElement da das, .firstElement db dbs =>
      let ⟨digits, carry⟩ :=
        addAlignedLists das dbs (Sequences.List.sameLength_of_firstElement h)
      let digit_sum :=
        da.val + db.val +
          (if carry then CardinalNatural.Peano.one else CardinalNatural.Peano.zero)
      if h2 : CardinalNatural.Peano.isLessThan digit_sum CardinalNatural.Peano.ten then
        ⟨Sequences.List.firstElement
          ⟨digit_sum, (CardinalNatural.Peano.isLessThan_eq_true_iff_lt _ _).mp h2⟩
          digits, false⟩
      else
        have h_le : CardinalNatural.Peano.ten ≤ digit_sum :=
          CardinalNatural.Peano.isLessThan_false_implies_le (eq_false_of_ne_true h2)
        have h_lt_twenty :
            digit_sum < CardinalNatural.Peano.ten + CardinalNatural.Peano.ten :=
          digit_sum_lt_twenty da.val db.val carry da.property db.property
        ⟨Sequences.List.firstElement
          ⟨CardinalNatural.Peano.subtract digit_sum CardinalNatural.Peano.ten h_le,
            subtract_ten_lt_ten digit_sum h_le h_lt_twenty⟩
          digits, true⟩
  | .empty, .firstElement _ _ => False.elim (by cases h)
  | .firstElement _ _, .empty => False.elim (by cases h)

theorem digit_val_successor_le_ten (d : Digit) :
    d.val.successor ≤ CardinalNatural.Peano.ten :=
  CardinalNatural.Peano.succ_le_of_lt d.property

theorem digit_val_le_ten (d : Digit) : d.val ≤ CardinalNatural.Peano.ten :=
  CardinalNatural.Peano.le_of_succ_le (digit_val_successor_le_ten d)

/-- Columnar subtraction of equal-length digit lists (least-significant digit recursion).
    The boolean is the final borrow out of the most-significant column. -/
def subtractAlignedLists (a b : Sequences.List Digit) (h : Sequences.List.SameLength a b) :
    Sequences.List Digit × Bool :=
  match a, b with
  | .empty, .empty => ⟨Sequences.List.empty, false⟩
  | .firstElement da das, .firstElement db dbs =>
      let ⟨digits, borrow⟩ :=
        subtractAlignedLists das dbs (Sequences.List.sameLength_of_firstElement h)
      let withBorrow := if borrow then db.val.successor else db.val
      if h2 : da.val < withBorrow then
        have h_withBorrow_le_ten : withBorrow ≤ CardinalNatural.Peano.ten := by
          dsimp [withBorrow]
          split
          · exact digit_val_successor_le_ten db
          · exact digit_val_le_ten db
        have h_le : withBorrow ≤ da.val + CardinalNatural.Peano.ten :=
          CardinalNatural.Peano.le_trans h_withBorrow_le_ten
            (CardinalNatural.Peano.le_add_self_right da.val CardinalNatural.Peano.ten)
        have h_digit :
            CardinalNatural.Peano.subtract (da.val + CardinalNatural.Peano.ten) withBorrow h_le <
              CardinalNatural.Peano.ten :=
          CardinalNatural.Peano.subtract_lt_of_lt_add h_le
            (CardinalNatural.Peano.add_lt_add_right h2 CardinalNatural.Peano.ten)
        ⟨Sequences.List.firstElement
          ⟨CardinalNatural.Peano.subtract (da.val + CardinalNatural.Peano.ten) withBorrow h_le,
            h_digit⟩
          digits, true⟩
      else
        have h_le : withBorrow ≤ da.val := CardinalNatural.Peano.not_lt_implies_le h2
        have h_digit :
            CardinalNatural.Peano.subtract da.val withBorrow h_le < CardinalNatural.Peano.ten :=
          CardinalNatural.Peano.subtract_lt_of_lt_add h_le
            (CardinalNatural.Peano.lt_le_trans da.property
              (CardinalNatural.Peano.le_add_self_right withBorrow CardinalNatural.Peano.ten))
        ⟨Sequences.List.firstElement
          ⟨CardinalNatural.Peano.subtract da.val withBorrow h_le, h_digit⟩ digits, false⟩
  | .empty, .firstElement _ _ => False.elim (by cases h)
  | .firstElement _ _, .empty => False.elim (by cases h)

theorem LessThanAlignedLists_congr {a b c d : Sequences.List Digit}
    (h₁ : Sequences.List.SameLength a b) (h₂ : Sequences.List.SameLength c d)
    (ha : a = c) (hb : b = d) :
    LessThanAlignedLists a b h₁ → LessThanAlignedLists c d h₂ := by
  subst c
  subst d
  intro h
  exact h

theorem lessThanAlignedLists_padded_snd_fst_of_absCardinalPeano_lt {a b : Decimal}
    (h : absCardinalPeano b < absCardinalPeano a) :
    LessThanAlignedLists
      (Sequences.List.padAtStartToSameLength a.digits.val b.digits.val zeroDigit).2
      (Sequences.List.padAtStartToSameLength a.digits.val b.digits.val zeroDigit).1
      (Sequences.List.sameLength_commutative
        (Sequences.List.padAtStartToSameLength_sameLength a.digits.val b.digits.val
          zeroDigit)) := by
  have h_aligned := lessThanAlignedLists_padded_of_absCardinalPeano_lt h
  have hpad :=
    Sequences.List.padAtStartToSameLength_commutative b.digits.val a.digits.val zeroDigit
  have h_fst := congrArg Prod.fst hpad
  have h_snd := congrArg Prod.snd hpad
  dsimp only at h_fst h_snd ⊢
  exact LessThanAlignedLists_congr _ _ h_snd.symm h_fst.symm h_aligned

theorem subtractAlignedLists_borrow_false_of_lessThan {a b : Sequences.List Digit}
    (h_same : Sequences.List.SameLength a b)
    (h_lt : LessThanAlignedLists b a (Sequences.List.sameLength_commutative h_same)) :
    (subtractAlignedLists a b h_same).2 = false := by
  induction h_same using Sequences.List.SameLength.induction with
  | empty =>
      cases h_lt
  | firstElement htail ih =>
      rename_i da db das dbs
      unfold subtractAlignedLists
      cases h_rec : subtractAlignedLists das dbs htail with
      | mk digits borrow =>
          cases h_lt with
          | inl h_db_lt_da =>
              cases borrow with
              | false =>
                  have h_not : ¬ da.val < db.val :=
                    CardinalNatural.Peano.not_lt_of_lt h_db_lt_da
                  simp [h_not]
              | true =>
                  have h_not : ¬ da.val < db.val.successor :=
                    CardinalNatural.Peano.cardinal_not_lt_of_le
                      (CardinalNatural.Peano.succ_le_of_lt h_db_lt_da)
                  simp [h_not]
          | inr h_eq_tail =>
              obtain ⟨h_digit_eq, h_tail_lt⟩ := h_eq_tail
              have h_borrow := ih h_tail_lt
              rw [h_rec] at h_borrow
              dsimp only at h_borrow
              cases borrow with
              | false =>
                  have h_not : ¬ da.val < db.val := by
                    intro hlt
                    rw [← h_digit_eq] at hlt
                    exact CardinalNatural.Peano.not_lt_self db.val hlt
                  simp [h_not]
              | true =>
                  cases h_borrow

/-- Add two digit lists as magnitudes and attach the given sign (via `normalizeList`). -/
def addMagnitudes (sign : Option Sign) (a b : Sequences.List Digit) : Decimal :=
  let pair := Sequences.List.padAtStartToSameLength a b zeroDigit
  let h_same : Sequences.List.SameLength pair.1 pair.2 :=
    Sequences.List.padAtStartToSameLength_sameLength a b zeroDigit
  match addAlignedLists pair.1 pair.2 h_same with
  | ⟨digits, true⟩ =>
      normalizeList sign
        (Sequences.List.firstElement oneDigit digits)
  | ⟨digits, false⟩ =>
      normalizeList sign digits

/-- Subtract digit magnitudes `|larger| - |smaller|` when `|smaller| < |larger|`,
    attaching the given sign via `normalizeList`. -/
def subtractMagnitudes (sign : Option Sign) (larger smaller : Decimal)
    (h : absCardinalPeano smaller < absCardinalPeano larger) : Decimal :=
  let pair :=
    Sequences.List.padAtStartToSameLength larger.digits.val smaller.digits.val zeroDigit
  let h_same : Sequences.List.SameLength pair.1 pair.2 :=
    Sequences.List.padAtStartToSameLength_sameLength larger.digits.val smaller.digits.val
      zeroDigit
  match h_subtract : subtractAlignedLists pair.1 pair.2 h_same with
  | ⟨digits, borrow⟩ =>
      if hb : borrow then
        False.elim (by
          have h_borrow_false :=
            subtractAlignedLists_borrow_false_of_lessThan h_same
              (lessThanAlignedLists_padded_snd_fst_of_absCardinalPeano_lt h)
          rw [h_subtract] at h_borrow_false
          dsimp only at h_borrow_false
          rw [hb] at h_borrow_false
          cases h_borrow_false)
      else
        normalizeList sign digits

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

theorem digit_carry_lt_twenty (a : Digit) (b : Digit) :
    a.val + b.val < CardinalNatural.Peano.ten + CardinalNatural.Peano.ten := by
  have h := digit_sum_lt_twenty a.val b.val false a.property b.property
  have h2 :
      (if false = true then CardinalNatural.Peano.one else CardinalNatural.Peano.zero) =
        CardinalNatural.Peano.zero := rfl
  rw [h2] at h
  rw [CardinalNatural.Peano.add_zero] at h
  exact h

def addPartialListDigit (a : Sequences.List Digit) (b : Digit) :
    Sequences.List Digit × Digit :=
  match a with
  | .empty => ⟨.empty, b⟩
  | .firstElement d ds =>
    let (ds', carry) := addPartialListDigit ds b
    let sum := d.val + carry.val
    if h : sum < CardinalNatural.Peano.ten then
      (.firstElement ⟨sum, h⟩ ds', zeroDigit)
    else
      have h_false : sum.isLessThan CardinalNatural.Peano.ten = false :=
        (CardinalNatural.Peano.isLessThan_eq_false_iff_not_lt sum _).mpr h
      have h1 : CardinalNatural.Peano.ten ≤ sum :=
        CardinalNatural.Peano.isLessThan_false_implies_le h_false
      have h2 : sum < CardinalNatural.Peano.ten + CardinalNatural.Peano.ten :=
        digit_carry_lt_twenty d carry
      have h3 : CardinalNatural.Peano.subtract sum CardinalNatural.Peano.ten h1 <
          CardinalNatural.Peano.ten :=
        subtract_ten_lt_ten sum h1 h2
      (.firstElement ⟨CardinalNatural.Peano.subtract sum CardinalNatural.Peano.ten h1, h3⟩
        ds', oneDigit)

def addListDigit (a : Sequences.List Digit) (b : Digit) : Sequences.List Digit :=
  let (ds, carry) := addPartialListDigit a b
  if carry.val = .zero then ds else .firstElement carry ds

def multiplyDigitsPeano (a : Digit) (b : CardinalNatural.Peano) : Sequences.List Digit :=
  match b with
  | CardinalNatural.Peano.zero => .firstElement zeroDigit .empty
  | CardinalNatural.Peano.successor b' =>
    let prev := multiplyDigitsPeano a b'
    addListDigit prev a

def multiplyDigits (a b : Digit) : Sequences.List Digit :=
  multiplyDigitsPeano a b.val

theorem digit_cases (d : Digit) :
    d = zeroDigit ∨ d = oneDigit ∨ d = twoDigit ∨ d = threeDigit ∨ d = fourDigit ∨
      d = fiveDigit ∨ d = sixDigit ∨ d = sevenDigit ∨ d = eightDigit ∨ d = nineDigit := by
  cases d with
  | mk val h =>
      cases val with
      | zero =>
          exact Or.inl (Subtype.ext rfl)
      | successor val1 =>
          cases val1 with
          | zero =>
              exact Or.inr (Or.inl (Subtype.ext rfl))
          | successor val2 =>
              cases val2 with
              | zero =>
                  exact Or.inr (Or.inr (Or.inl (Subtype.ext rfl)))
              | successor val3 =>
                  cases val3 with
                  | zero =>
                      exact Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext rfl))))
                  | successor val4 =>
                      cases val4 with
                      | zero =>
                          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext rfl)))))
                      | successor val5 =>
                          cases val5 with
                          | zero =>
                              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext rfl))))))
                          | successor val6 =>
                              cases val6 with
                              | zero =>
                                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext rfl)))))))
                              | successor val7 =>
                                  cases val7 with
                                  | zero =>
                                      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext rfl))))))))
                                  | successor val8 =>
                                      cases val8 with
                                      | zero =>
                                          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext rfl)))))))))
                                      | successor val9 =>
                                          cases val9 with
                                          | zero =>
                                              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Subtype.ext rfl)))))))))
                                          | successor val10 =>
                                              have h1 := CardinalNatural.Peano.lt_of_succ_lt_succ h
                                              have h2 := CardinalNatural.Peano.lt_of_succ_lt_succ h1
                                              have h3 := CardinalNatural.Peano.lt_of_succ_lt_succ h2
                                              have h4 := CardinalNatural.Peano.lt_of_succ_lt_succ h3
                                              have h5 := CardinalNatural.Peano.lt_of_succ_lt_succ h4
                                              have h6 := CardinalNatural.Peano.lt_of_succ_lt_succ h5
                                              have h7 := CardinalNatural.Peano.lt_of_succ_lt_succ h6
                                              have h8 := CardinalNatural.Peano.lt_of_succ_lt_succ h7
                                              have h9 := CardinalNatural.Peano.lt_of_succ_lt_succ h8
                                              have h10 := CardinalNatural.Peano.lt_of_succ_lt_succ h9
                                              exact False.elim (CardinalNatural.Peano.not_lt_zero val10 h10)

theorem addListDigit_multiplyDigits_ne_empty (d b carry : Digit) :
    addListDigit (multiplyDigits d b) carry ≠ Sequences.List.empty := by
  rcases digit_cases d with hd | hd | hd | hd | hd | hd | hd | hd | hd | hd <;>
    subst d <;>
    rcases digit_cases b with hb | hb | hb | hb | hb | hb | hb | hb | hb | hb <;>
    subst b <;>
    rcases digit_cases carry with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc <;>
    subst carry <;>
    decide

theorem addListDigit_multiplyDigits_not_three_or_more
    (d b carry x y z : Digit) (zs : Sequences.List Digit) :
    addListDigit (multiplyDigits d b) carry ≠
      Sequences.List.firstElement x
        (Sequences.List.firstElement y (Sequences.List.firstElement z zs)) := by
  rcases digit_cases d with hd | hd | hd | hd | hd | hd | hd | hd | hd | hd <;>
    subst d <;>
    rcases digit_cases b with hb | hb | hb | hb | hb | hb | hb | hb | hb | hb <;>
    subst b <;>
    rcases digit_cases carry with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc <;>
    subst carry <;>
    intro h <;> cases h

def multiplyPartialListByDigit (a : Sequences.List Digit) (b : Digit) :
    Sequences.List Digit × Digit :=
  match a with
  | .empty => (Sequences.List.empty, zeroDigit)
  | .firstElement d ds =>
    let (ds', carry) := multiplyPartialListByDigit ds b
    let digitProduct := multiplyDigits d b
    let withCarry := addListDigit digitProduct carry
    match h : withCarry with
    | .empty => False.elim (addListDigit_multiplyDigits_ne_empty d b carry h)
    | .firstElement x .empty => ⟨.firstElement x ds', zeroDigit⟩
    | .firstElement x (.firstElement y .empty) => ⟨.firstElement y ds', x⟩
    | .firstElement x (.firstElement y (.firstElement z zs)) =>
        False.elim (addListDigit_multiplyDigits_not_three_or_more d b carry x y z zs h)

def multiplyListByDigit (a : Sequences.List Digit) (b : Digit) : Sequences.List Digit :=
  let (ds, carry) := multiplyPartialListByDigit a b
  if carry.val = .zero then ds else .firstElement carry ds

def multiplyList (a b : Sequences.List Digit) :
    Sequences.List Digit × CardinalNatural.Peano :=
  match b with
  | .empty => ⟨.empty, .zero⟩
  | .firstElement d ds =>
    let (accumulator, shift) := multiplyList a ds
    let digitProduct := multiplyListByDigit a d
    let withShift := Sequences.List.padAtEnd digitProduct zeroDigit shift
    let pair := Sequences.List.padAtStartToSameLength accumulator withShift zeroDigit
    let h_same : Sequences.List.SameLength pair.1 pair.2 :=
      Sequences.List.padAtStartToSameLength_sameLength accumulator withShift zeroDigit
    match addAlignedLists pair.1 pair.2 h_same with
    | ⟨digits, true⟩ =>
      ⟨Sequences.List.firstElement oneDigit digits, shift.successor⟩
    | ⟨digits, false⟩ =>
      ⟨digits, shift.successor⟩

/-- Columnar multiplication of decimal integers: magnitudes multiply digit-wise;
    the result is negative iff exactly one operand is negative. -/
def multiply (a b : Decimal) : Decimal :=
  let sign : Option Sign :=
    match isNegative a, isNegative b with
    | true, false | false, true => some Sign.minus
    | _, _ => none
  normalizeList sign (multiplyList a.digits.val b.digits.val).1

instance : Mul Decimal where
  mul := multiply

theorem addAlignedLists_spec {a b : Sequences.List Digit}
  (h : Sequences.List.SameLength a b) :
  let result := addAlignedLists a b h
  result.1.length = a.length ∧
    toCardinalPeanoList result.1 CardinalNatural.Peano.zero +
        (if result.2 then CardinalNatural.Peano.tenPow a.length else CardinalNatural.Peano.zero) =
      toCardinalPeanoList a CardinalNatural.Peano.zero +
        toCardinalPeanoList b CardinalNatural.Peano.zero := by
  induction h using Sequences.List.SameLength.induction with
  | empty =>
      simp [addAlignedLists, toCardinalPeanoList, Sequences.List.length]
  | @firstElement da db das dbs htail ih =>
      unfold addAlignedLists
      dsimp only
      cases h_rec : addAlignedLists das dbs htail with
      | mk digits carry =>
          rw [h_rec] at ih
          dsimp only at ih
          obtain ⟨h_length, ih_value⟩ := ih
          have h_tail_lengths := htail
          cases carry with
          | false =>
              simp at ih_value ⊢
              split
              · constructor
                · simp [Sequences.List.length, h_length]
                · simp only [toCardinalPeanoList_firstElement]
                  simp only [if_neg Bool.false_ne_true]
                  rw [h_length, ← h_tail_lengths]
                  rw [CardinalNatural.Peano.multiply_distributive_over_add_left, ih_value]
                  simp
                  simp only [CardinalNatural.Peano.add_associative, CardinalNatural.Peano.add_left_commutative]
              · constructor
                · simp [Sequences.List.length, h_length]
                · simp only [toCardinalPeanoList_firstElement, Sequences.List.length,
                    CardinalNatural.Peano.tenPow_add_one]
                  rw [h_length, ← h_tail_lengths]
                  have h_digit := CardinalNatural.Peano.subtract_add_cancel
                    (da.val + db.val) CardinalNatural.Peano.ten
                    (CardinalNatural.Peano.isLessThan_false_implies_le (eq_false_of_ne_true ‹_›))
                  simp only [if_true]
                  calc
                    _ = (CardinalNatural.Peano.subtract
                            (da.val + db.val)
                            CardinalNatural.Peano.ten _ + CardinalNatural.Peano.ten) *
                          CardinalNatural.Peano.tenPow das.length +
                        toCardinalPeanoList digits CardinalNatural.Peano.zero := by
                          rw [CardinalNatural.Peano.multiply_distributive_over_add_left]
                          rw [CardinalNatural.Peano.add_associative,
                            CardinalNatural.Peano.add_commutative
                              (toCardinalPeanoList digits CardinalNatural.Peano.zero)
                              (CardinalNatural.Peano.ten * CardinalNatural.Peano.tenPow das.length),
                            ← CardinalNatural.Peano.add_associative]
                    _ = _ := by
                      rw [h_digit, CardinalNatural.Peano.multiply_distributive_over_add_left, ih_value]
                      simp only [CardinalNatural.Peano.add_associative,
                        CardinalNatural.Peano.add_left_commutative]
          | true =>
              simp at ih_value ⊢
              split
              · constructor
                · simp [Sequences.List.length, h_length]
                · simp only [toCardinalPeanoList_firstElement]
                  simp only [if_neg Bool.false_ne_true]
                  rw [h_length, ← h_tail_lengths]
                  rw [CardinalNatural.Peano.multiply_distributive_over_add_left]
                  rw [CardinalNatural.Peano.multiply_distributive_over_add_left]
                  rw [CardinalNatural.Peano.one_multiply]
                  calc
                    _ = da.val * CardinalNatural.Peano.tenPow das.length +
                          db.val * CardinalNatural.Peano.tenPow das.length +
                          (toCardinalPeanoList digits CardinalNatural.Peano.zero +
                            CardinalNatural.Peano.tenPow das.length) := by
                              simp
                              simp only [CardinalNatural.Peano.add_associative,
                                CardinalNatural.Peano.add_commutative, CardinalNatural.Peano.add_left_commutative]
                    _ = _ := by rw [ih_value]; simp only [CardinalNatural.Peano.add_associative,
                      CardinalNatural.Peano.add_left_commutative]
              · constructor
                · simp [Sequences.List.length, h_length]
                · simp only [toCardinalPeanoList_firstElement, Sequences.List.length,
                    CardinalNatural.Peano.tenPow_add_one]
                  rw [h_length, ← h_tail_lengths]
                  have h_digit := CardinalNatural.Peano.subtract_add_cancel
                    (da.val + db.val + CardinalNatural.Peano.one) CardinalNatural.Peano.ten
                    (CardinalNatural.Peano.isLessThan_false_implies_le (eq_false_of_ne_true ‹_›))
                  simp only [if_true]
                  calc
                    _ = (CardinalNatural.Peano.subtract
                            (da.val + db.val + CardinalNatural.Peano.one)
                            CardinalNatural.Peano.ten _ + CardinalNatural.Peano.ten) *
                          CardinalNatural.Peano.tenPow das.length +
                        toCardinalPeanoList digits CardinalNatural.Peano.zero := by
                          rw [CardinalNatural.Peano.multiply_distributive_over_add_left]
                          simp only [CardinalNatural.Peano.add_commutative,
                            CardinalNatural.Peano.add_left_commutative]
                    _ = _ := by
                      rw [h_digit, CardinalNatural.Peano.multiply_distributive_over_add_left,
                        CardinalNatural.Peano.multiply_distributive_over_add_left,
                        CardinalNatural.Peano.one_multiply]
                      calc
                        _ = da.val * CardinalNatural.Peano.tenPow das.length +
                              db.val * CardinalNatural.Peano.tenPow das.length +
                              (toCardinalPeanoList digits CardinalNatural.Peano.zero +
                                CardinalNatural.Peano.tenPow das.length) := by simp only [
                                  CardinalNatural.Peano.add_associative,
                                  CardinalNatural.Peano.add_commutative,
                                  CardinalNatural.Peano.add_left_commutative]
                        _ = _ := by rw [ih_value]; simp only [CardinalNatural.Peano.add_associative,
                          CardinalNatural.Peano.add_left_commutative]



theorem subtractAlignedLists_spec {a b : Sequences.List Digit}
  (h : Sequences.List.SameLength a b) :
  let result := subtractAlignedLists a b h
  result.1.length = a.length ∧
    toCardinalPeanoList result.1 CardinalNatural.Peano.zero +
        toCardinalPeanoList b CardinalNatural.Peano.zero =
      toCardinalPeanoList a CardinalNatural.Peano.zero +
        (if result.2 then CardinalNatural.Peano.tenPow a.length else CardinalNatural.Peano.zero) := by
  induction h using Sequences.List.SameLength.induction with
  | empty =>
      simp [subtractAlignedLists, toCardinalPeanoList, Sequences.List.length]
  | @firstElement da db das dbs htail ih =>
      unfold subtractAlignedLists
      dsimp only
      cases h_rec : subtractAlignedLists das dbs htail with
      | mk digits borrow =>
          rw [h_rec] at ih
          dsimp only at ih
          obtain ⟨h_length, ih_value⟩ := ih
          have h_tail_lengths := htail
          cases borrow with
          | false =>
              simp at ih_value ⊢
              split
              · next h_da_lt_db =>
                  constructor
                  · simp [Sequences.List.length, h_length]
                  · simp only [toCardinalPeanoList_firstElement, Sequences.List.length,
                      CardinalNatural.Peano.tenPow_add_one, if_true]
                    rw [h_length, ← h_tail_lengths]
                    have h_le : db.val ≤ da.val + CardinalNatural.Peano.ten := by
                      exact CardinalNatural.Peano.le_trans (digit_val_le_ten db)
                        (CardinalNatural.Peano.le_add_self_right da.val CardinalNatural.Peano.ten)
                    have h_digit := CardinalNatural.Peano.subtract_add_cancel
                      (da.val + CardinalNatural.Peano.ten) db.val h_le
                    calc
                      _ = (CardinalNatural.Peano.subtract (da.val + CardinalNatural.Peano.ten) db.val h_le + db.val) *
                            CardinalNatural.Peano.tenPow das.length +
                          (toCardinalPeanoList digits CardinalNatural.Peano.zero +
                            toCardinalPeanoList dbs CardinalNatural.Peano.zero) := by
                            rw [CardinalNatural.Peano.multiply_distributive_over_add_left]
                            exact CardinalNatural.Peano.add_pair_swap _ _ _ _
                      _ = (da.val + CardinalNatural.Peano.ten) * CardinalNatural.Peano.tenPow das.length +
                          toCardinalPeanoList das CardinalNatural.Peano.zero := by
                            rw [h_digit, ih_value]
                      _ = da.val * CardinalNatural.Peano.tenPow das.length +
                          toCardinalPeanoList das CardinalNatural.Peano.zero +
                            CardinalNatural.Peano.ten * CardinalNatural.Peano.tenPow das.length := by
                            rw [CardinalNatural.Peano.multiply_distributive_over_add_left]
                            exact CardinalNatural.Peano.add_right_commutative _ _ _
              · next h_not_lt =>
                  constructor
                  · simp [Sequences.List.length, h_length]
                  · simp only [toCardinalPeanoList_firstElement, Sequences.List.length]
                    simp only [if_neg Bool.false_ne_true]
                    rw [h_length, ← h_tail_lengths]
                    have h_le : db.val ≤ da.val := CardinalNatural.Peano.not_lt_implies_le h_not_lt
                    have h_digit := CardinalNatural.Peano.subtract_add_cancel da.val db.val h_le
                    calc
                      _ = (CardinalNatural.Peano.subtract da.val db.val h_le + db.val) *
                            CardinalNatural.Peano.tenPow das.length +
                          (toCardinalPeanoList digits CardinalNatural.Peano.zero +
                            toCardinalPeanoList dbs CardinalNatural.Peano.zero) := by
                            rw [CardinalNatural.Peano.multiply_distributive_over_add_left]
                            exact CardinalNatural.Peano.add_pair_swap _ _ _ _
                      _ = da.val * CardinalNatural.Peano.tenPow das.length +
                          toCardinalPeanoList das CardinalNatural.Peano.zero := by
                            rw [h_digit, ih_value]
                      _ = da.val * CardinalNatural.Peano.tenPow das.length +
                          toCardinalPeanoList das CardinalNatural.Peano.zero + CardinalNatural.Peano.zero := by
                            rw [CardinalNatural.Peano.add_zero]
          | true =>
              simp at ih_value ⊢
              split
              · next h_da_lt_db_succ =>
                  constructor
                  · simp [Sequences.List.length, h_length]
                  · simp only [toCardinalPeanoList_firstElement, Sequences.List.length,
                      CardinalNatural.Peano.tenPow_add_one, if_true]
                    rw [h_length, ← h_tail_lengths]
                    have h_le : db.val.successor ≤ da.val + CardinalNatural.Peano.ten := by
                      exact CardinalNatural.Peano.le_trans (digit_val_successor_le_ten db)
                        (CardinalNatural.Peano.le_add_self_right da.val CardinalNatural.Peano.ten)
                    have h_digit := CardinalNatural.Peano.subtract_add_cancel
                      (da.val + CardinalNatural.Peano.ten) db.val.successor h_le
                    calc
                      _ = (CardinalNatural.Peano.subtract (da.val + CardinalNatural.Peano.ten) db.val.successor h_le + db.val) *
                            CardinalNatural.Peano.tenPow das.length +
                          (toCardinalPeanoList digits CardinalNatural.Peano.zero +
                            toCardinalPeanoList dbs CardinalNatural.Peano.zero) := by
                            rw [CardinalNatural.Peano.multiply_distributive_over_add_left]
                            exact CardinalNatural.Peano.add_pair_swap _ _ _ _
                      _ = (CardinalNatural.Peano.subtract (da.val + CardinalNatural.Peano.ten) db.val.successor h_le + db.val) *
                            CardinalNatural.Peano.tenPow das.length +
                          (toCardinalPeanoList das CardinalNatural.Peano.zero +
                            CardinalNatural.Peano.tenPow das.length) := by
                            rw [ih_value]
                      _ = (CardinalNatural.Peano.subtract (da.val + CardinalNatural.Peano.ten) db.val.successor h_le + db.val).successor *
                            CardinalNatural.Peano.tenPow das.length +
                          toCardinalPeanoList das CardinalNatural.Peano.zero := by
                            rw [CardinalNatural.Peano.successor_multiply]
                            rw [CardinalNatural.Peano.add_commutative (toCardinalPeanoList das CardinalNatural.Peano.zero)
                              (CardinalNatural.Peano.tenPow das.length)]
                            rw [← CardinalNatural.Peano.add_associative]
                      _ = (da.val + CardinalNatural.Peano.ten) * CardinalNatural.Peano.tenPow das.length +
                          toCardinalPeanoList das CardinalNatural.Peano.zero := by
                            rw [← CardinalNatural.Peano.add_successor]
                            rw [h_digit]
                      _ = da.val * CardinalNatural.Peano.tenPow das.length +
                          toCardinalPeanoList das CardinalNatural.Peano.zero +
                            CardinalNatural.Peano.ten * CardinalNatural.Peano.tenPow das.length := by
                            rw [CardinalNatural.Peano.multiply_distributive_over_add_left]
                            exact CardinalNatural.Peano.add_right_commutative _ _ _
              · next h_not_lt =>
                  constructor
                  · simp [Sequences.List.length, h_length]
                  · simp only [toCardinalPeanoList_firstElement, Sequences.List.length]
                    simp only [if_neg Bool.false_ne_true]
                    rw [h_length, ← h_tail_lengths]
                    have h_le : db.val.successor ≤ da.val := CardinalNatural.Peano.not_lt_implies_le h_not_lt
                    have h_digit := CardinalNatural.Peano.subtract_add_cancel da.val db.val.successor h_le
                    calc
                      _ = (CardinalNatural.Peano.subtract da.val db.val.successor h_le + db.val) *
                            CardinalNatural.Peano.tenPow das.length +
                          (toCardinalPeanoList digits CardinalNatural.Peano.zero +
                            toCardinalPeanoList dbs CardinalNatural.Peano.zero) := by
                            rw [CardinalNatural.Peano.multiply_distributive_over_add_left]
                            exact CardinalNatural.Peano.add_pair_swap _ _ _ _
                      _ = (CardinalNatural.Peano.subtract da.val db.val.successor h_le + db.val) *
                            CardinalNatural.Peano.tenPow das.length +
                          (toCardinalPeanoList das CardinalNatural.Peano.zero +
                            CardinalNatural.Peano.tenPow das.length) := by
                            rw [ih_value]
                      _ = (CardinalNatural.Peano.subtract da.val db.val.successor h_le + db.val).successor *
                            CardinalNatural.Peano.tenPow das.length +
                          toCardinalPeanoList das CardinalNatural.Peano.zero := by
                            rw [CardinalNatural.Peano.successor_multiply]
                            exact CardinalNatural.Peano.add_right_swap _ _ _
                      _ = da.val * CardinalNatural.Peano.tenPow das.length +
                          toCardinalPeanoList das CardinalNatural.Peano.zero := by
                            rw [← CardinalNatural.Peano.add_successor]
                            rw [h_digit]
                      _ = da.val * CardinalNatural.Peano.tenPow das.length +
                          toCardinalPeanoList das CardinalNatural.Peano.zero + CardinalNatural.Peano.zero := by
                            rw [CardinalNatural.Peano.add_zero]


theorem addMagnitudes_toPeano (sign : Option Sign) (a b : Sequences.List Digit) :
    toPeano (addMagnitudes sign a b) =
      match sign with
      | some Sign.minus =>
          -(Peano.fromCardinalNatural
            (toCardinalPeanoList a CardinalNatural.Peano.zero +
              toCardinalPeanoList b CardinalNatural.Peano.zero))
      | _ =>
          Peano.fromCardinalNatural
            (toCardinalPeanoList a CardinalNatural.Peano.zero +
              toCardinalPeanoList b CardinalNatural.Peano.zero) := by
  unfold addMagnitudes
  dsimp only
  have hone : oneDigit.val = CardinalNatural.Peano.one := rfl
  split
  · next digits h_add =>
      have h_spec := addAlignedLists_spec
        (Sequences.List.padAtStartToSameLength_sameLength a b zeroDigit)
      rw [h_add] at h_spec
      dsimp only at h_spec
      obtain ⟨h_length, h_value⟩ := h_spec
      simp at h_value
      have h_norm := normalizeList_toPeano sign
        (Sequences.List.firstElement oneDigit digits)
      rw [h_norm]
      have h_list :
          toCardinalPeanoList
              (Sequences.List.firstElement oneDigit digits)
              CardinalNatural.Peano.zero =
            toCardinalPeanoList a CardinalNatural.Peano.zero +
              toCardinalPeanoList b CardinalNatural.Peano.zero := by
        rw [toCardinalPeanoList_firstElement, hone, h_length,
          CardinalNatural.Peano.one_multiply, CardinalNatural.Peano.add_commutative,
          h_value, toCardinalPeanoList_padAtStartToSameLength_fst,
          toCardinalPeanoList_padAtStartToSameLength_snd]
      cases sign with
      | none =>
          exact congrArg Peano.fromCardinalNatural h_list
      | some s =>
          cases s with
          | plus =>
              exact congrArg Peano.fromCardinalNatural h_list
          | minus =>
              exact congrArg (fun n => -(Peano.fromCardinalNatural n)) h_list
  · next digits h_add =>
      have h_spec := addAlignedLists_spec
        (Sequences.List.padAtStartToSameLength_sameLength a b zeroDigit)
      rw [h_add] at h_spec
      dsimp only at h_spec
      obtain ⟨_, h_value⟩ := h_spec
      simp at h_value
      have h_norm := normalizeList_toPeano sign digits
      rw [h_norm]
      have h_list :
          toCardinalPeanoList digits CardinalNatural.Peano.zero =
            toCardinalPeanoList a CardinalNatural.Peano.zero +
              toCardinalPeanoList b CardinalNatural.Peano.zero := by
        rw [h_value, toCardinalPeanoList_padAtStartToSameLength_fst,
          toCardinalPeanoList_padAtStartToSameLength_snd]
      cases sign with
      | none =>
          exact congrArg Peano.fromCardinalNatural h_list
      | some s =>
          cases s with
          | plus =>
              exact congrArg Peano.fromCardinalNatural h_list
          | minus =>
              exact congrArg (fun n => -(Peano.fromCardinalNatural n)) h_list

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
  let pair :=
    Sequences.List.padAtStartToSameLength larger.digits.val smaller.digits.val zeroDigit
  let h_same : Sequences.List.SameLength pair.1 pair.2 :=
    Sequences.List.padAtStartToSameLength_sameLength larger.digits.val smaller.digits.val
      zeroDigit
  have h_borrow_false :=
    subtractAlignedLists_borrow_false_of_lessThan h_same
      (lessThanAlignedLists_padded_snd_fst_of_absCardinalPeano_lt h)
  simp [pair, h_borrow_false]
  cases h_subtract : subtractAlignedLists pair.1 pair.2 h_same with
  | mk digits borrow =>
      rw [h_subtract] at h_borrow_false
      dsimp only at h_borrow_false
      cases borrow with
      | true =>
          cases h_borrow_false
      | false =>
          have h_spec := subtractAlignedLists_spec h_same
          rw [h_subtract] at h_spec
          dsimp only at h_spec
          obtain ⟨_, h_value⟩ := h_spec
          simp at h_value
          have h_norm := normalizeList_toPeano sign digits
          rw [h_norm]
          have h_sum :
              toCardinalPeanoList digits CardinalNatural.Peano.zero +
                  absCardinalPeano smaller =
                absCardinalPeano larger := by
            unfold absCardinalPeano
            rw [← toCardinalPeanoList_padAtStartToSameLength_fst larger.digits.val
              smaller.digits.val,
              ← toCardinalPeanoList_padAtStartToSameLength_snd larger.digits.val
                smaller.digits.val]
            exact h_value
          have h_peano_sum :
              Peano.fromCardinalNatural
                  (toCardinalPeanoList digits CardinalNatural.Peano.zero) +
                Peano.fromCardinalNatural (absCardinalPeano smaller) =
              Peano.fromCardinalNatural (absCardinalPeano larger) := by
            rw [← Peano.fromCardinalNatural_add, h_sum]
          have h_peano :
              Peano.fromCardinalNatural
                  (toCardinalPeanoList digits CardinalNatural.Peano.zero) =
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

end Decimal

end ZeroMath.Numbers.Integer
