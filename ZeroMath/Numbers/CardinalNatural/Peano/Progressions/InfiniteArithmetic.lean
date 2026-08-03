import ZeroMath.Numbers.CardinalNatural.Peano
import ZeroMath.Sequences.Progression

namespace ZeroMath.Numbers.CardinalNatural.Peano.Progressions

/-- An infinite arithmetic progression of Peano numbers, defined by the first
element and the common difference. When the common difference is positive the
progression is strictly increasing; when it is zero every element equals the
first. -/
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
def getElement (p : InfiniteArithmetic) : OrdinalNatural.Peano → Peano
  | .one => p.first
  | .successor n => getElement p n + p.commonDifference

/-- `tryGetElement` on an infinite arithmetic progression returns
`some (getElement ...)`. -/
theorem tryGetElement_eq_getElement (p : InfiniteArithmetic)
    (index : OrdinalNatural.Peano) :
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
theorem tryGetElement_eq_some (p : InfiniteArithmetic)
    (index : OrdinalNatural.Peano) :
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

/-- Recover the first element of an infinite arithmetic progression from an
element at the given ordinal index and the common difference. At index `one`
the element is itself the first; otherwise subtract
`(fromOrdinal (predecessor index)) * commonDifference`. Returns `none` when
that subtraction is impossible in the Peano numbers. -/
def tryFirstFromIndexedElement
    (index : OrdinalNatural.Peano) (element commonDifference : Peano) :
    Option Peano :=
  match index with
  | .one => some element
  | .successor n => trySubtract element (fromOrdinal n * commonDifference)

/-- Given two ordered indexed elements (`index < index'`) of a prospective
infinite arithmetic progression, recover the common difference
`(element' - element) / (index' - index)`. Returns `none` when the second
element is smaller than the first or the element gap is not divisible by the
index gap. -/
def tryCommonDifferenceFromOrderedIndexedElements
    (index : OrdinalNatural.Peano) (element : Peano)
    (index' : OrdinalNatural.Peano) (element' : Peano)
    (hlt : index < index') :
    Option Peano :=
  match trySubtract element' element with
  | none => none
  | some elementDiff =>
    tryDivide elementDiff
      (fromOrdinal (OrdinalNatural.Peano.subtract index' index hlt))

/-- Reconstruct an infinite arithmetic progression from two of its elements at
different ordinal indexes. Returns `none` when the values are not consistent
with a non-decreasing infinite arithmetic progression (descending elements, or
an element gap that is not divisible by the index difference). -/
def tryFromTwoElements
    (index1 : OrdinalNatural.Peano) (element1 : Peano)
    (index2 : OrdinalNatural.Peano) (element2 : Peano)
    (hne : index1 ≠ index2) :
    Option InfiniteArithmetic :=
  match OrdinalNatural.Peano.compare index1 index2 with
  | .equal heq => False.elim (hne heq)
  | .less hlt =>
    match tryCommonDifferenceFromOrderedIndexedElements
        index1 element1 index2 element2 hlt with
    | none => none
    | some diff =>
      match tryFirstFromIndexedElement index1 element1 diff with
      | none => none
      | some first =>
        some {
          first := first
          commonDifference := diff
        }
  | .greater hgt =>
    match tryCommonDifferenceFromOrderedIndexedElements
        index2 element2 index1 element1 hgt with
    | none => none
    | some diff =>
      match tryFirstFromIndexedElement index2 element2 diff with
      | none => none
      | some first =>
        some {
          first := first
          commonDifference := diff
        }

end InfiniteArithmetic

end ZeroMath.Numbers.CardinalNatural.Peano.Progressions
