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

/-- `tryGetElement` on an infinite arithmetic progression always returns `some`. -/
theorem tryGetElement_eq_some (p : InfiniteArithmetic) (index : Peano) :
    ∃ x, Sequences.Progression.tryGetElement index (toProgression p) = some x := by
  induction index with
  | one =>
    exact ⟨p.first, rfl⟩
  | successor n ih =>
    obtain ⟨x, hx⟩ := ih
    refine ⟨x + p.commonDifference, ?_⟩
    simp only [Sequences.Progression.tryGetElement]
    rw [hx]
    rfl

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
