import ZeroMath.Numbers.CardinalNatural.Decimal
import ZeroMath.Sequences.Progression

namespace ZeroMath.Numbers.CardinalNatural.Decimal.Progressions

/-- An infinite arithmetic progression of Decimal numbers, defined by the first
element and the common difference. When the common difference is positive the
progression is strictly increasing; when it is zero every element equals the
first. -/
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

/-- The element at the given positive ordinal Decimal index. Always the closed
form `first + (fromOrdinal index - one) * commonDifference`, with no iteration
on the index and no case split on whether the index is `one`. -/
def getElement (p : InfiniteArithmetic) (index : OrdinalNatural.Decimal) :
    Decimal :=
  p.first +
    (subtract (fromOrdinal index) one (one_le_fromOrdinal index)) *
      p.commonDifference

/-- The Peano embedding of `getElement`. -/
theorem getElement_toPeano (p : InfiniteArithmetic)
    (index : OrdinalNatural.Decimal) :
    (getElement p index).toPeano =
      p.first.toPeano +
        (subtract (fromOrdinal index) one (one_le_fromOrdinal index)).toPeano *
          p.commonDifference.toPeano := by
  simp only [getElement, add_toPeano, multiply_toPeano]

/-- At an index equivalent to `one`, `getElement` is equivalent to the first
element. -/
theorem getElement_equivalent_first_of_equivalent_one (p : InfiniteArithmetic)
    (index : OrdinalNatural.Decimal)
    (h : index ≈ OrdinalNatural.Decimal.one) :
    getElement p index ≈ p.first := by
  apply equivalent_of_toPeano_eq
  rw [getElement_toPeano, subtract_fromOrdinal_one_toPeano]
  have hone : index.toPeano = OrdinalNatural.Peano.one :=
    (OrdinalNatural.Decimal.toPeano_eq_one_iff_equivalent_one index).mpr h
  rw [hone]
  change
      p.first.toPeano +
          Peano.subtract Peano.one Peano.one
            (Peano.one_le_fromOrdinal OrdinalNatural.Peano.one) *
            p.commonDifference.toPeano =
        p.first.toPeano
  have hz :
      Peano.subtract Peano.one Peano.one
        (Peano.one_le_fromOrdinal OrdinalNatural.Peano.one) = Peano.zero := by
    change Peano.subtract (Peano.successor Peano.zero)
        (Peano.successor Peano.zero) _ = Peano.zero
    simp only [Peano.subtract]
  rw [hz, Peano.zero_multiply, Peano.add_zero]

/-- The Peano embedding of `getElement` at an index equivalent to `one`. -/
theorem getElement_toPeano_of_equivalent_one (p : InfiniteArithmetic)
    (index : OrdinalNatural.Decimal)
    (h : index ≈ OrdinalNatural.Decimal.one) :
    (getElement p index).toPeano = p.first.toPeano :=
  toPeano_eq_of_equivalent (getElement_equivalent_first_of_equivalent_one p index h)

/-- The Peano embedding of the closed-form `getElement` away from `one`. -/
theorem getElement_toPeano_of_not_equivalent_one (p : InfiniteArithmetic)
    (index : OrdinalNatural.Decimal)
    (h : ¬ index ≈ OrdinalNatural.Decimal.one) :
    (getElement p index).toPeano =
      p.first.toPeano +
        (fromOrdinal (index.predecessor h)).toPeano *
          p.commonDifference.toPeano := by
  rw [getElement_toPeano, subtract_fromOrdinal_one_eq_fromOrdinal_predecessor index h]

/-- Advancing one step from the predecessor index matches the closed form up to
Decimal equivalence. -/
theorem getElement_predecessor_add_commonDifference (p : InfiniteArithmetic)
    (index : OrdinalNatural.Decimal)
    (h : ¬ index ≈ OrdinalNatural.Decimal.one) :
    getElement p (index.predecessor h) + p.commonDifference ≈
      getElement p index := by
  apply equivalent_of_toPeano_eq
  rw [add_toPeano, getElement_toPeano_of_not_equivalent_one p index h]
  if hpred : index.predecessor h ≈ OrdinalNatural.Decimal.one then
    rw [getElement_toPeano_of_equivalent_one p _ hpred]
    have hone : (index.predecessor h).toPeano = OrdinalNatural.Peano.one :=
      (OrdinalNatural.Decimal.toPeano_eq_one_iff_equivalent_one _).mpr hpred
    have hfrom :
        (fromOrdinal (index.predecessor h)).toPeano = Peano.one := by
      rw [fromOrdinal_toPeano_eq_fromOrdinal_peano, hone, Peano.fromOrdinal]
    rw [hfrom, Peano.one_multiply]
  else
    rw [getElement_toPeano_of_not_equivalent_one p _ hpred]
    have hsucc :=
      OrdinalNatural.Decimal.toPeano_eq_succ_predecessor_toPeano
        (index.predecessor h) hpred
    have hfrom :
        (fromOrdinal (index.predecessor h)).toPeano =
          ((fromOrdinal ((index.predecessor h).predecessor hpred)).toPeano).successor := by
      rw [fromOrdinal_toPeano_eq_fromOrdinal_peano,
        fromOrdinal_toPeano_eq_fromOrdinal_peano, hsucc, Peano.fromOrdinal]
    rw [hfrom, Peano.successor_multiply, Peano.add_associative]

/-- `tryGetElement` returns a value equivalent to `getElement` at the
corresponding Peano index. -/
theorem tryGetElement_eq_getElement (p : InfiniteArithmetic)
    (index : OrdinalNatural.Decimal) :
    Option.Rel (· ≈ ·)
      (Sequences.Progression.tryGetElement index.toPeano (toProgression p))
      (some (getElement p index)) := by
  if h : index ≈ OrdinalNatural.Decimal.one then
    have hpeano : index.toPeano = OrdinalNatural.Peano.one :=
      (OrdinalNatural.Decimal.toPeano_eq_one_iff_equivalent_one index).mpr h
    rw [hpeano, Sequences.Progression.tryGetElement]
    exact Option.Rel.some
      (Setoid.symm (getElement_equivalent_first_of_equivalent_one p index h))
  else
    have hpeano :=
      OrdinalNatural.Decimal.toPeano_eq_succ_predecessor_toPeano index h
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
  obtain ⟨hne, heq⟩ := OrdinalNatural.Decimal.predecessor_toPeano index h
  simp only [heq]
  exact OrdinalNatural.Peano.sizeOf_predecessor_lt _ hne

/-- `tryGetElement` on an infinite arithmetic progression always returns `some`. -/
theorem tryGetElement_eq_some (p : InfiniteArithmetic)
    (index : OrdinalNatural.Decimal) :
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
  obtain ⟨_, hx⟩ :=
    tryGetElement_eq_some p (OrdinalNatural.Decimal.fromPeano index)
  rw [OrdinalNatural.Decimal.toPeano_fromPeano index] at hx
  rw [hx] at hnone
  nomatch hnone

end InfiniteArithmetic

end ZeroMath.Numbers.CardinalNatural.Decimal.Progressions
