import ZeroMath.Numbers.CardinalNatural.Peano
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

end Decimal

end ZeroMath.Numbers.Integer
