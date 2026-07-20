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
      ⟨sign, ⟨Sequences.List.firstElement
        ⟨CardinalNatural.Peano.one, CardinalNatural.Peano.one_lt_ten⟩ digits, by simp⟩⟩
    | ⟨digits, false⟩ =>
      ⟨sign, ⟨digits, successorList_ne_empty_of_carry_false a.digits.property h⟩⟩

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

end Decimal

end ZeroMath.Numbers.Integer
