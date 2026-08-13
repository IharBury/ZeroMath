import ZeroMath.Numbers.CardinalNatural.Decimal
import ZeroMath.Numbers.Integer.Decimal
import ZeroMath.Numbers.Integer.Peano.Progressions.FiniteArithmetic
import ZeroMath.Sequences.Progression

namespace ZeroMath.Numbers.Integer.Decimal.Progressions

/-- A finite arithmetic progression of integer Decimal numbers with nonzero common
difference, defined by an optional first element (`none` for the empty
progression), the common difference, and a limit such that no element lies past
the limit in the direction of travel. When the common difference is positive the
progression is strictly increasing and no element exceeds the limit; when it is
negative the progression is strictly decreasing and no element is less than the
limit. The progression is also empty when the first element already lies past
the limit. -/
structure FiniteArithmetic where
  first : Option Decimal
  commonDifference : Decimal
  limit : Decimal
  commonDifference_ne_zero : ¬ commonDifference ≈ zero

namespace FiniteArithmetic

/-- Include `x` when it does not lie past `limit` for the given common
difference: at most the limit when the difference is positive, at least the
limit when it is negative. Returns `none` for a zero difference. -/
def tryInclude (commonDifference limit x : Decimal) : Option Decimal :=
  match compare commonDifference zero with
  | .greater _ => if x ≤ limit then some x else none
  | .less _ => if limit ≤ x then some x else none
  | .equivalent _ => none

/-- Convert a finite arithmetic progression to a general progression by taking
the same optional first element when it does not lie past the limit (otherwise
the empty progression) and advancing by the common difference while the next
element does not lie past the limit. -/
def toProgression (p : FiniteArithmetic) : Sequences.Progression Decimal where
  first :=
    match p.first with
    | none => none
    | some x => tryInclude p.commonDifference p.limit x
  next := fun x =>
    tryInclude p.commonDifference p.limit (x + p.commonDifference)

/-- The cardinal magnitude of a nonzero decimal integer is a nonzero cardinal
decimal. -/
theorem magnitude_not_equivalent_zero_of_not_equivalent_zero {x : Decimal}
    (h : ¬ x ≈ zero) : ¬ x.magnitude ≈ CardinalNatural.Decimal.zero := by
  intro hm
  have hmag0 : x.magnitude.toPeano = CardinalNatural.Peano.zero := by
    rw [CardinalNatural.Decimal.toPeano_eq_of_equivalent hm,
      CardinalNatural.Decimal.toPeano_zero]
  have habs : absCardinalPeano x = CardinalNatural.Peano.zero := by
    rw [← magnitude_toPeano, hmag0]
  have hx0 : x.toPeano = Peano.zero := toPeano_eq_zero_of_absCardinal_zero habs
  exact h (equivalent_of_toPeano_eq (hx0.trans toPeano_zero.symm))

/-- Length remaining from an element already known to lie in the progression,
given the cardinal gap to the limit in the direction of travel (`none` when the
element equals the limit). Computed with one division by the absolute common
difference instead of comparing each successive term to the limit. -/
def lengthFromGap (diff : CardinalNatural.Decimal)
    (hdiff : ¬ diff ≈ CardinalNatural.Decimal.zero) :
    Option CardinalNatural.Decimal → CardinalNatural.Decimal
  | none => CardinalNatural.Decimal.one
  | some gap =>
    match CardinalNatural.Decimal.divideWithRemainder gap diff hdiff with
    | (q, _) => q.successor

/-- The length of a finite arithmetic progression: the number of elements before
`tryGetElement` first returns `none`. Uses a single comparison of the first
element to the limit and one division by the absolute common difference,
avoiding a comparison at every step of the progression. -/
def getLength (p : FiniteArithmetic) : CardinalNatural.Decimal :=
  match p.first with
  | none => CardinalNatural.Decimal.zero
  | some first =>
    match compare p.commonDifference zero with
    | .equivalent heq => (p.commonDifference_ne_zero heq).elim
    | .greater _ =>
      match compare first p.limit with
      | .greater _ => CardinalNatural.Decimal.zero
      | .equivalent _ => CardinalNatural.Decimal.one
      | .less _ =>
        lengthFromGap p.commonDifference.magnitude
          (magnitude_not_equivalent_zero_of_not_equivalent_zero
            p.commonDifference_ne_zero)
          (some (p.limit - first).magnitude)
    | .less _ =>
      match compare first p.limit with
      | .less _ => CardinalNatural.Decimal.zero
      | .equivalent _ => CardinalNatural.Decimal.one
      | .greater _ =>
        lengthFromGap p.commonDifference.magnitude
          (magnitude_not_equivalent_zero_of_not_equivalent_zero
            p.commonDifference_ne_zero)
          (some (first - p.limit).magnitude)

/-- Convert a Decimal finite arithmetic progression to the corresponding Peano
progression by embedding each field via `toPeano`. -/
def toPeano (p : FiniteArithmetic) : Peano.Progressions.FiniteArithmetic where
  first :=
    match p.first with
    | none => none
    | some x => some x.toPeano
  commonDifference := p.commonDifference.toPeano
  limit := p.limit.toPeano
  commonDifference_ne_zero :=
    toPeano_ne_zero_of_not_equivalent_zero p.commonDifference_ne_zero

end FiniteArithmetic

end ZeroMath.Numbers.Integer.Decimal.Progressions
