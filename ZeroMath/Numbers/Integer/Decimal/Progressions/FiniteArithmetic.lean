import ZeroMath.Numbers.Integer.Decimal
import ZeroMath.Numbers.Integer.Peano.Progressions.FiniteArithmetic
import ZeroMath.Sequences.Progression

namespace ZeroMath.Numbers.Integer.Decimal.Progressions

/-- A finite arithmetic progression of Decimal integers with nonzero common
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
limit when it is negative. Returns `none` for a difference equivalent to
zero. -/
def tryInclude (commonDifference limit x : Decimal) : Option Decimal :=
  match commonDifference.toPeano with
  | .positive _ => if x ≤ limit then some x else none
  | .negative _ => if limit ≤ x then some x else none
  | .zero => none

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

/-- Convert a finite arithmetic progression of Decimal integers to the
corresponding Peano finite arithmetic progression by embedding each field via
`Decimal.toPeano`. -/
def toPeano (p : FiniteArithmetic) : Peano.Progressions.FiniteArithmetic where
  first := p.first.map Decimal.toPeano
  commonDifference := p.commonDifference.toPeano
  limit := p.limit.toPeano
  commonDifference_ne_zero :=
    toPeano_ne_zero_of_not_equivalent_zero p.commonDifference_ne_zero

/-- If `tryInclude` returns a value, that value is the candidate element. -/
theorem eq_of_tryInclude_eq_some (commonDifference limit x y : Decimal)
    (h : tryInclude commonDifference limit x = some y) : y = x := by
  match hdiff : commonDifference.toPeano with
  | .positive _ =>
    simp only [tryInclude, hdiff] at h
    by_cases hle : x ≤ limit
    · simp only [hle, ↓reduceIte] at h
      injection h with heq
      exact heq.symm
    · simp only [hle, ↓reduceIte] at h
      nomatch h
  | .negative _ =>
    simp only [tryInclude, hdiff] at h
    by_cases hle : limit ≤ x
    · simp only [hle, ↓reduceIte] at h
      injection h with heq
      exact heq.symm
    · simp only [hle, ↓reduceIte] at h
      nomatch h
  | .zero =>
    simp only [tryInclude, hdiff] at h
    nomatch h

/-- When `tryInclude` succeeds on `x`, it returns `some x`. -/
theorem tryInclude_eq_some_self (commonDifference limit x y : Decimal)
    (h : tryInclude commonDifference limit x = some y) :
    tryInclude commonDifference limit x = some x := by
  rw [eq_of_tryInclude_eq_some commonDifference limit x y h] at h
  exact h

/-- `tryInclude` commutes with the Peano embedding. -/
theorem tryInclude_toPeano (commonDifference limit x : Decimal) :
    Option.map Decimal.toPeano (tryInclude commonDifference limit x) =
      Peano.Progressions.FiniteArithmetic.tryInclude
        commonDifference.toPeano limit.toPeano x.toPeano := by
  simp only [tryInclude, Peano.Progressions.FiniteArithmetic.tryInclude]
  cases commonDifference.toPeano with
  | zero =>
    rfl
  | positive _ =>
    have hiff := le_iff_toPeano_le x limit
    by_cases hle : x ≤ limit
    · simp only [hle, hiff.mp hle, ↓reduceIte, Option.map]
    · have hle' : ¬ x.toPeano ≤ limit.toPeano := fun h => hle (hiff.mpr h)
      simp only [hle, hle', ↓reduceIte, Option.map]
  | negative _ =>
    have hiff := le_iff_toPeano_le limit x
    by_cases hle : limit ≤ x
    · simp only [hle, hiff.mp hle, ↓reduceIte, Option.map]
    · have hle' : ¬ limit.toPeano ≤ x.toPeano := fun h => hle (hiff.mpr h)
      simp only [hle, hle', ↓reduceIte, Option.map]

/-- The first element of `toProgression` commutes with `toPeano`. -/
theorem first_toPeano (p : FiniteArithmetic) :
    Option.map Decimal.toPeano (toProgression p).first =
      (Peano.Progressions.FiniteArithmetic.toProgression (toPeano p)).first := by
  cases hf : p.first with
  | none =>
    simp only [toProgression, hf, toPeano,
      Peano.Progressions.FiniteArithmetic.toProgression, Option.map]
  | some x =>
    simp only [toProgression, hf, toPeano,
      Peano.Progressions.FiniteArithmetic.toProgression, Option.map]
    exact tryInclude_toPeano p.commonDifference p.limit x

/-- Advancing one step of `toProgression` commutes with `toPeano`. -/
theorem next_toPeano (p : FiniteArithmetic) (x : Decimal) :
    Option.map Decimal.toPeano ((toProgression p).next x) =
      (Peano.Progressions.FiniteArithmetic.toProgression
        (toPeano p)).next x.toPeano := by
  change Option.map Decimal.toPeano
      (tryInclude p.commonDifference p.limit (x + p.commonDifference)) =
    Peano.Progressions.FiniteArithmetic.tryInclude
      p.commonDifference.toPeano p.limit.toPeano
      (x.toPeano + p.commonDifference.toPeano)
  have htry := tryInclude_toPeano p.commonDifference p.limit (x + p.commonDifference)
  rw [add_toPeano] at htry
  exact htry

/-- `tryGetElement` commutes with the Peano embedding. -/
theorem tryGetElement_toPeano (p : FiniteArithmetic)
    (index : OrdinalNatural.Peano) :
    Option.map Decimal.toPeano
      (Sequences.Progression.tryGetElement index (toProgression p)) =
    Sequences.Progression.tryGetElement index
      (Peano.Progressions.FiniteArithmetic.toProgression (toPeano p)) := by
  induction index with
  | one =>
    exact first_toPeano p
  | successor n ih =>
    simp only [Sequences.Progression.tryGetElement]
    cases hp : Sequences.Progression.tryGetElement n (toProgression p) with
    | none =>
      have ih' :
          Sequences.Progression.tryGetElement n
            (Peano.Progressions.FiniteArithmetic.toProgression (toPeano p)) =
            none := by
        simpa [hp, Option.map] using ih.symm
      simp only [ih']
      rfl
    | some x =>
      have ih' :
          Sequences.Progression.tryGetElement n
            (Peano.Progressions.FiniteArithmetic.toProgression (toPeano p)) =
            some x.toPeano := by
        simpa [hp, Option.map] using ih.symm
      simp only [ih']
      exact next_toPeano p x

/-- The progression obtained from a finite arithmetic progression is finite:
`tryGetElement` is `none` at the same witness index as the Peano embedding. -/
theorem toProgression_finite (p : FiniteArithmetic) :
    Sequences.Progression.Finite (toProgression p) := by
  obtain ⟨index, hnone⟩ :=
    Peano.Progressions.FiniteArithmetic.toProgression_finite (toPeano p)
  refine ⟨index, ?_⟩
  have hmap := tryGetElement_toPeano p index
  rw [hnone] at hmap
  cases h : Sequences.Progression.tryGetElement index (toProgression p) with
  | none =>
    rfl
  | some _ =>
    simp only [h, Option.map] at hmap
    nomatch hmap

end FiniteArithmetic

end ZeroMath.Numbers.Integer.Decimal.Progressions
