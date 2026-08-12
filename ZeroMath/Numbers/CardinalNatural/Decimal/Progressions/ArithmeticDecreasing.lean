import ZeroMath.Numbers.CardinalNatural.Decimal
import ZeroMath.Sequences.Progression

namespace ZeroMath.Numbers.CardinalNatural.Decimal.Progressions

/-- An arithmetic progression of Decimal numbers with subtractive common
difference, defined by an optional first element (`none` for the empty
progression), the common difference (subtracted at each step), and a limit
such that no element is less than the limit. The progression is also empty
when the first element is less than the limit. A positive common difference
yields a strictly decreasing finite progression; a zero common difference
would never leave the current element under `toProgression`. -/
structure ArithmeticDecreasing where
  first : Option Decimal
  subtractiveCommonDifference : Decimal
  limit : Decimal

namespace ArithmeticDecreasing

/-- Convert a decreasing arithmetic progression to a general progression by
taking the same optional first element when it is not less than the limit
(otherwise the empty progression) and subtracting the common difference while
the next element is not less than the limit. -/
def toProgression (p : ArithmeticDecreasing) : Sequences.Progression Decimal where
  first :=
    match p.first with
    | none => none
    | some x => if p.limit ≤ x then some x else none
  next := fun x =>
    match trySubtract x p.subtractiveCommonDifference with
    | none => none
    | some y => if p.limit ≤ y then some y else none

end ArithmeticDecreasing

end ZeroMath.Numbers.CardinalNatural.Decimal.Progressions
