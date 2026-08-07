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
has index equivalent to `one`; otherwise the value is the closed form
`first + (predecessor index) * commonDifference`, with no iteration on the
index. -/
def getElement (p : InfiniteArithmetic) (index : Decimal) : Decimal :=
  if h : index ≈ one then
    p.first
  else
    p.first + (index.predecessor h) * p.commonDifference

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

/-- Addition on the right respects Decimal equivalence. -/
theorem equivalent_add_right {a b c : Decimal} (h : a ≈ b) : a + c ≈ b + c := by
  apply equivalent_of_toCardinalPeano_eq
  rw [toCardinalPeano_add, toCardinalPeano_add, toCardinalPeano_eq_of_equivalent h]

/-- The Peano embedding of `getElement` at an index equivalent to `one`. -/
theorem getElement_toPeano_of_equivalent_one (p : InfiniteArithmetic)
    (index : Decimal) (h : index ≈ one) :
    (getElement p index).toPeano = p.first.toPeano := by
  simp only [getElement, h, ↓reduceDIte]

/-- The Peano embedding of the closed-form `getElement` away from `one`. -/
theorem getElement_toPeano_of_not_equivalent_one (p : InfiniteArithmetic)
    (index : Decimal) (h : ¬ index ≈ one) :
    (getElement p index).toPeano =
      p.first.toPeano +
        (index.predecessor h).toPeano * p.commonDifference.toPeano := by
  simp only [getElement, h, ↓reduceDIte, add_toPeano, multiplyToPeano]

/-- Advancing one step from the predecessor index matches the closed form up to
Decimal equivalence. -/
theorem getElement_predecessor_add_commonDifference (p : InfiniteArithmetic)
    (index : Decimal) (h : ¬ index ≈ one) :
    getElement p (index.predecessor h) + p.commonDifference ≈
      getElement p index := by
  apply equivalent_of_toPeano_eq
  rw [add_toPeano, getElement_toPeano_of_not_equivalent_one p index h]
  if hpred : index.predecessor h ≈ one then
    rw [getElement_toPeano_of_equivalent_one p _ hpred]
    have hone : (index.predecessor h).toPeano = Peano.one :=
      (toPeano_eq_one_iff_equivalent_one _).mpr hpred
    rw [hone, Peano.one_multiply]
  else
    rw [getElement_toPeano_of_not_equivalent_one p _ hpred]
    have hsucc := toPeano_eq_succ_predecessor_toPeano (index.predecessor h) hpred
    rw [hsucc, Peano.succ_multiply, Peano.add_assoc]

/-- The Peano predecessor is structurally smaller than its argument. -/
theorem sizeOf_predecessor_lt (n : Peano) (hne : n ≠ Peano.one) :
    sizeOf (n.predecessor hne) < sizeOf n := by
  cases n with
  | one => exact False.elim (hne rfl)
  | successor n =>
    simp only [Peano.predecessor]
    decreasing_trivial

/-- `tryGetElement` returns a value equivalent to `getElement` at the
corresponding Peano index. -/
theorem tryGetElement_eq_getElement (p : InfiniteArithmetic) (index : Decimal) :
    Option.Rel (· ≈ ·)
      (Sequences.Progression.tryGetElement index.toPeano (toProgression p))
      (some (getElement p index)) := by
  if h : index ≈ one then
    have hpeano : index.toPeano = Peano.one :=
      (toPeano_eq_one_iff_equivalent_one index).mpr h
    rw [hpeano, Sequences.Progression.tryGetElement, getElement, dif_pos h]
    exact Option.Rel.some (Setoid.refl _)
  else
    have hpeano := toPeano_eq_succ_predecessor_toPeano index h
    have ih := tryGetElement_eq_getElement p (index.predecessor h)
    rw [hpeano, Sequences.Progression.tryGetElement]
    match htry : Sequences.Progression.tryGetElement
        (index.predecessor h).toPeano (toProgression p), ih with
    | none, ih =>
      cases ih
    | some x, ih =>
      cases ih with
      | some hx =>
        simp only [toProgression]
        exact Option.Rel.some
          (Setoid.trans (equivalent_add_right hx)
            (getElement_predecessor_add_commonDifference p index h))
termination_by index.toPeano
decreasing_by
  obtain ⟨hne, heq⟩ := predecessor_toPeano index h
  simp only [heq]
  exact sizeOf_predecessor_lt _ hne

/-- `tryGetElement` on an infinite arithmetic progression always returns `some`. -/
theorem tryGetElement_eq_some (p : InfiniteArithmetic) (index : Decimal) :
    ∃ x, Sequences.Progression.tryGetElement index.toPeano (toProgression p) =
      some x := by
  have hrel := tryGetElement_eq_getElement p index
  match htry : Sequences.Progression.tryGetElement index.toPeano (toProgression p),
      hrel with
  | none, hrel => cases hrel
  | some x, _ => exact ⟨x, rfl⟩

/-- The progression obtained from an infinite arithmetic progression is
infinite. -/
theorem toProgression_infinite (p : InfiniteArithmetic) :
    Sequences.Progression.Infinite (toProgression p) := by
  intro ⟨index, hnone⟩
  obtain ⟨_, hx⟩ := tryGetElement_eq_some p (fromPeano index)
  rw [toPeano_fromPeano index] at hx
  rw [hx] at hnone
  nomatch hnone

/-- Recover the first element of an infinite arithmetic progression from an
element at the given ordinal Decimal index and the common difference. When the
index is equivalent to `one` the element is itself the first; otherwise
subtract `(predecessor index) * commonDifference`. Returns `none` when that
subtraction is impossible in the Decimal numbers. -/
def tryFirstFromIndexedElement (index element commonDifference : Decimal) :
    Option Decimal :=
  if h : index ≈ one then
    some element
  else
    trySubtract element ((index.predecessor h) * commonDifference)

/-- Given two ordered indexed elements (`index < index'`) of a prospective
infinite arithmetic progression, recover the common difference
`(element' - element) / (index' - index)`. Returns `none` when the elements are
not strictly ascending or the element gap is not divisible by the index gap. -/
def tryCommonDifferenceFromOrderedIndexedElements
    (index element index' element' : Decimal) (hlt : index < index') :
    Option Decimal :=
  match trySubtract element' element with
  | none => none
  | some elementDiff =>
    tryDivide elementDiff (subtract index' index hlt)

/-- Reconstruct an infinite arithmetic progression from two of its elements at
different ordinal Decimal indexes. Returns `none` when the values are not
consistent with a strictly increasing infinite arithmetic progression
(non-ascending elements, or an element gap that is not divisible by the index
difference). Indexes are compared up to Decimal equivalence. -/
def tryFromTwoElements
    (index1 : Decimal) (element1 : Decimal)
    (index2 : Decimal) (element2 : Decimal)
    (hne : ¬ index1 ≈ index2) :
    Option InfiniteArithmetic :=
  match compare index1 index2 with
  | .equivalent heq => False.elim (hne heq)
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

end ZeroMath.Numbers.OrdinalNatural.Decimal.Progressions
