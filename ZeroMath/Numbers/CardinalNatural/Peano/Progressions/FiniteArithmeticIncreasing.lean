import ZeroMath.Numbers.CardinalNatural.Peano
import ZeroMath.Sequences.Progression

namespace ZeroMath.Numbers.CardinalNatural.Peano.Progressions

/-- A finite increasing arithmetic progression of Peano numbers with positive
common difference, defined by an optional first element (`none` for the empty
progression), the common difference, and a limit such that no element is
greater than the limit. The progression is also empty when the first element
is greater than the limit. A positive common difference yields a strictly
increasing finite progression; a zero common difference would never leave the
current element under `toProgression`. -/
structure FiniteArithmeticIncreasing where
  first : Option Peano
  commonDifference : Peano
  limit : Peano

namespace FiniteArithmeticIncreasing

/-- Convert a finite increasing arithmetic progression to a general progression
by taking the same optional first element when it does not exceed the limit
(otherwise the empty progression) and advancing by the common difference while
the next element does not exceed the limit. -/
def toProgression (p : FiniteArithmeticIncreasing) : Sequences.Progression Peano where
  first :=
    match p.first with
    | none => none
    | some x => if x ≤ p.limit then some x else none
  next := fun x =>
    let y := x + p.commonDifference
    if y ≤ p.limit then some y else none

end FiniteArithmeticIncreasing

end ZeroMath.Numbers.CardinalNatural.Peano.Progressions
