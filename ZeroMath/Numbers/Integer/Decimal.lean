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

end Decimal

end ZeroMath.Numbers.Integer
