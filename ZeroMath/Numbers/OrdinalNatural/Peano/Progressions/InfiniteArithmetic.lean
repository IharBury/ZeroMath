import ZeroMath.Numbers.OrdinalNatural.Peano
import ZeroMath.Sequences.Progression

namespace ZeroMath.Numbers.OrdinalNatural.Peano.Progressions

/-- An infinite arithmetic progression of Peano numbers with positive common
difference, defined by the first element and the common difference. Because
every Peano number is at least one, the common difference is always positive. -/
structure InfiniteArithmetic where
  first : Peano
  commonDifference : Peano

namespace InfiniteArithmetic

/-- Convert an infinite arithmetic progression to a general progression by
taking the same first element and advancing by the common difference at each
step (never ending). -/
def toProgression (p : InfiniteArithmetic) : Sequences.Progression Peano where
  first := some p.first
  next := fun x => some (x + p.commonDifference)

/-- The element at the given positive ordinal index. The first element has
index `one`; each successor index advances by the common difference. -/
def getElement (p : InfiniteArithmetic) : Peano → Peano
  | .one => p.first
  | .successor n => getElement p n + p.commonDifference

/-- `tryGetElement` on an infinite arithmetic progression returns
`some (getElement ...)`. -/
theorem tryGetElement_eq_getElement (p : InfiniteArithmetic) (index : Peano) :
    Sequences.Progression.tryGetElement index (toProgression p) =
      some (getElement p index) := by
  induction index with
  | one =>
    rfl
  | successor n ih =>
    simp only [Sequences.Progression.tryGetElement, getElement]
    rw [ih]
    rfl

/-- `tryGetElement` on an infinite arithmetic progression always returns `some`. -/
theorem tryGetElement_eq_some (p : InfiniteArithmetic) (index : Peano) :
    ∃ x, Sequences.Progression.tryGetElement index (toProgression p) = some x :=
  ⟨getElement p index, tryGetElement_eq_getElement p index⟩

/-- The progression obtained from an infinite arithmetic progression is
infinite. -/
theorem toProgression_infinite (p : InfiniteArithmetic) :
    Sequences.Progression.Infinite (toProgression p) := by
  intro ⟨index, hnone⟩
  obtain ⟨_, hx⟩ := tryGetElement_eq_some p index
  rw [hx] at hnone
  nomatch hnone

end InfiniteArithmetic

end ZeroMath.Numbers.OrdinalNatural.Peano.Progressions
