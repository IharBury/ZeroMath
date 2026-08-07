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

/-- The Peano predecessor is structurally smaller than its argument. -/
theorem sizeOf_predecessor_lt (n : Peano) (hne : n ≠ Peano.one) :
    sizeOf (n.predecessor hne) < sizeOf n := by
  cases n with
  | one => exact False.elim (hne rfl)
  | successor n =>
    simp only [Peano.predecessor]
    decreasing_trivial

/-- The element at the given positive ordinal Decimal index. The first element
has index equivalent to `one`; each larger index advances by the common
difference from the predecessor index. -/
def getElement (p : InfiniteArithmetic) (index : Decimal) : Decimal :=
  if h : index ≈ one then
    p.first
  else
    getElement p (index.predecessor h) + p.commonDifference
termination_by index.toPeano
decreasing_by
  obtain ⟨hne, heq⟩ := predecessor_toPeano index h
  simp only [heq]
  exact sizeOf_predecessor_lt _ hne

/-- An index is equivalent to `one` iff its Peano embedding is `one`. -/
theorem toPeano_eq_one_iff_equivalent_one (index : Decimal) :
    index.toPeano = Peano.one ↔ index ≈ one := by
  constructor
  · intro h
    exact equivalent_of_toPeano_eq (h.trans toPeano_one.symm)
  · intro h
    exact (toPeano_eq_of_equivalent h).trans toPeano_one

/-- When the index is not equivalent to `one`, it is the successor of its
predecessor in the Peano embedding. -/
theorem toPeano_eq_succ_predecessor_toPeano (index : Decimal) (h : ¬ index ≈ one) :
    index.toPeano = (index.predecessor h).toPeano.successor := by
  obtain ⟨hne, heq⟩ := predecessor_toPeano index h
  rw [heq, Peano.succ_pred_eq]

/-- `tryGetElement` on an infinite arithmetic progression returns
`some (getElement ...)` at the corresponding Peano index. -/
theorem tryGetElement_eq_getElement (p : InfiniteArithmetic) (index : Decimal) :
    Sequences.Progression.tryGetElement index.toPeano (toProgression p) =
      some (getElement p index) := by
  if h : index ≈ one then
    have hpeano : index.toPeano = Peano.one :=
      (toPeano_eq_one_iff_equivalent_one index).mpr h
    rw [getElement, dif_pos h, hpeano, Sequences.Progression.tryGetElement]
    rfl
  else
    have hpeano := toPeano_eq_succ_predecessor_toPeano index h
    have ih := tryGetElement_eq_getElement p (index.predecessor h)
    rw [getElement, dif_neg h, hpeano, Sequences.Progression.tryGetElement, ih]
    rfl
termination_by index.toPeano
decreasing_by
  obtain ⟨hne, heq⟩ := predecessor_toPeano index h
  simp only [heq]
  exact sizeOf_predecessor_lt _ hne

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
