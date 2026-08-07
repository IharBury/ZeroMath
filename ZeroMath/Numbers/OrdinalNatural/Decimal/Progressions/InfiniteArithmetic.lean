import ZeroMath.Numbers.OrdinalNatural.Decimal
import ZeroMath.Sequences.Progression

namespace ZeroMath.Numbers.OrdinalNatural.Decimal.Progressions

/-- An infinite arithmetic progression of Decimal numbers with positive common
difference, defined by the first element and the common difference. Because
every Decimal number is at least one, the common difference is always positive. -/
structure InfiniteArithmetic where
  first : Decimal
  commonDifference : Decimal

namespace InfiniteArithmetic

/-- Convert an infinite arithmetic progression to a general progression by
taking the same first element and advancing by the common difference at each
step (never ending). -/
def toProgression (p : InfiniteArithmetic) : Sequences.Progression Decimal where
  first := some p.first
  next := fun x => some (x + p.commonDifference)

/-- The element at the given positive ordinal Decimal index. The first element
has index `one`; each successor index advances by the common difference. -/
def getElement (p : InfiniteArithmetic) (index : Decimal) : Decimal :=
  go index.toPeano
where
  go : Peano → Decimal
    | .one => p.first
    | .successor n => go n + p.commonDifference

/-- `tryGetElement` on an infinite arithmetic progression returns
`some (getElement ...)` at the corresponding Peano index. -/
theorem tryGetElement_eq_getElement (p : InfiniteArithmetic) (index : Decimal) :
    Sequences.Progression.tryGetElement index.toPeano (toProgression p) =
      some (getElement p index) := by
  simp only [getElement]
  induction index.toPeano with
  | one =>
    rfl
  | successor n ih =>
    simp only [Sequences.Progression.tryGetElement, getElement.go]
    rw [ih]
    rfl

/-- `tryGetElement` on an infinite arithmetic progression always returns `some`. -/
theorem tryGetElement_eq_some (p : InfiniteArithmetic) (index : Decimal) :
    ∃ x, Sequences.Progression.tryGetElement index.toPeano (toProgression p) =
      some x :=
  ⟨getElement p index, tryGetElement_eq_getElement p index⟩

/-- The progression obtained from an infinite arithmetic progression is
infinite. -/
theorem toProgression_infinite (p : InfiniteArithmetic) :
    Sequences.Progression.Infinite (toProgression p) := by
  intro ⟨index, hnone⟩
  obtain ⟨_, hx⟩ := tryGetElement_eq_some p (fromPeano index)
  rw [toPeano_fromPeano index] at hx
  rw [hx] at hnone
  nomatch hnone

end InfiniteArithmetic

end ZeroMath.Numbers.OrdinalNatural.Decimal.Progressions
