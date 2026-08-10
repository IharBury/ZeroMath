import ZeroMath.Numbers.CardinalNatural.Decimal
import ZeroMath.Sequences.Progression

namespace ZeroMath.Numbers.CardinalNatural.Decimal.Progressions

/-- A finite increasing arithmetic progression of Decimal numbers with positive
common difference, defined by an optional first element (`none` for the empty
progression), the common difference, and a limit such that no element is
greater than the limit. The progression is also empty when the first element
is greater than the limit. -/
structure FiniteArithmeticIncreasing where
  first : Option Decimal
  commonDifference : Decimal
  limit : Decimal
  commonDifference_ne_zero : ¬ commonDifference ≈ zero

namespace FiniteArithmeticIncreasing

/-- Convert a finite increasing arithmetic progression to a general progression
by taking the same optional first element when it does not exceed the limit
(otherwise the empty progression) and advancing by the common difference while
the next element does not exceed the limit. -/
def toProgression (p : FiniteArithmeticIncreasing) : Sequences.Progression Decimal where
  first :=
    match p.first with
    | none => none
    | some x => if x ≤ p.limit then some x else none
  next := fun x =>
    let y := x + p.commonDifference
    if y ≤ p.limit then some y else none

/-- Every element obtained from `tryGetElement` is at most the limit. -/
theorem tryGetElement_le_limit (p : FiniteArithmeticIncreasing)
    (index : OrdinalNatural.Peano) (x : Decimal)
    (h : Sequences.Progression.tryGetElement index (toProgression p) = some x) :
    x ≤ p.limit := by
  induction index generalizing x with
  | one =>
    simp only [Sequences.Progression.tryGetElement] at h
    have hfirst : (toProgression p).first = some x := h
    match hf : p.first with
    | none =>
      have : (toProgression p).first = none := by
        simp only [toProgression, hf]
      rw [this] at hfirst
      nomatch hfirst
    | some y =>
      have hprog :
          (toProgression p).first =
            if y ≤ p.limit then some y else none := by
        simp only [toProgression, hf]
      rw [hprog] at hfirst
      by_cases hle : y ≤ p.limit
      · simp only [hle, ↓reduceIte] at hfirst
        injection hfirst with heq
        exact heq ▸ hle
      · simp only [hle, ↓reduceIte] at hfirst
        nomatch hfirst
  | successor n _ih =>
    simp only [Sequences.Progression.tryGetElement] at h
    cases hm : Sequences.Progression.tryGetElement n (toProgression p) with
    | none =>
      rw [hm] at h
      nomatch h
    | some y =>
      rw [hm] at h
      have hnext : (toProgression p).next y = some x := h
      have hprog :
          (toProgression p).next y =
            if y + p.commonDifference ≤ p.limit then
              some (y + p.commonDifference)
            else
              none :=
        rfl
      rw [hprog] at hnext
      by_cases hle : y + p.commonDifference ≤ p.limit
      · simp only [hle, ↓reduceIte] at hnext
        injection hnext with heq
        exact heq ▸ hle
      · simp only [hle, ↓reduceIte] at hnext
        nomatch hnext

/-- If `tryGetElement` returns a value, the ordinal index (as a cardinal Peano)
is at most the successor of that value's Peano embedding, because the
progression is strictly increasing with positive common difference. -/
theorem fromOrdinal_le_succ_of_tryGetElement_eq_some
    (p : FiniteArithmeticIncreasing) (index : OrdinalNatural.Peano) (x : Decimal)
    (h : Sequences.Progression.tryGetElement index (toProgression p) = some x) :
    Peano.fromOrdinal index ≤ x.toPeano.successor := by
  induction index generalizing x with
  | one =>
    exact Peano.succ_le_succ (Peano.zero_le x.toPeano)
  | successor n ih =>
    simp only [Sequences.Progression.tryGetElement] at h
    cases hm : Sequences.Progression.tryGetElement n (toProgression p) with
    | none =>
      rw [hm] at h
      nomatch h
    | some y =>
      rw [hm] at h
      have hnext : (toProgression p).next y = some x := h
      have hprog :
          (toProgression p).next y =
            if y + p.commonDifference ≤ p.limit then
              some (y + p.commonDifference)
            else
              none :=
        rfl
      rw [hprog] at hnext
      by_cases hle : y + p.commonDifference ≤ p.limit
      · simp only [hle, ↓reduceIte] at hnext
        injection hnext with heq
        have hn : Peano.fromOrdinal n ≤ y.toPeano.successor := ih y hm
        have hy_lt : y.toPeano < (y + p.commonDifference).toPeano := by
          rw [add_toPeano]
          exact Peano.lt_add_of_right_ne_zero y.toPeano p.commonDifference.toPeano
            (toPeano_ne_zero_of_not_equivalent_zero p.commonDifference_ne_zero)
        have hy_le : y.toPeano.successor ≤ (y + p.commonDifference).toPeano :=
          Peano.succ_le_of_lt hy_lt
        exact Peano.succ_le_succ (Peano.le_trans hn (heq ▸ hy_le))
      · simp only [hle, ↓reduceIte] at hnext
        nomatch hnext

/-- The progression obtained from a finite increasing arithmetic progression is
finite: `tryGetElement` at the ordinal corresponding to
`successor (successor limit.toPeano)` is always `none`, since any returned
value would have to be both ≥ `successor limit.toPeano` and ≤ `limit.toPeano`. -/
theorem toProgression_finite (p : FiniteArithmeticIncreasing) :
    Sequences.Progression.Finite (toProgression p) := by
  have hne : (p.limit.toPeano.successor).successor ≠ Peano.zero :=
    Peano.successor_ne_zero p.limit.toPeano.successor
  refine ⟨Peano.toOrdinal (p.limit.toPeano.successor).successor hne, ?_⟩
  cases h :
      Sequences.Progression.tryGetElement
        (Peano.toOrdinal (p.limit.toPeano.successor).successor hne)
        (toProgression p) with
  | none =>
    rfl
  | some x =>
    have hle_lim :=
      tryGetElement_le_limit p
        (Peano.toOrdinal (p.limit.toPeano.successor).successor hne) x h
    have hle_idx :=
      fromOrdinal_le_succ_of_tryGetElement_eq_some p
        (Peano.toOrdinal (p.limit.toPeano.successor).successor hne) x h
    rw [Peano.fromOrdinal_toOrdinal] at hle_idx
    have hle' : p.limit.toPeano.successor ≤ x.toPeano :=
      Peano.le_of_succ_le_succ hle_idx
    exact (Peano.not_succ_le p.limit.toPeano
      (Peano.le_trans hle' (toPeano_le_of_le hle_lim))).elim

end FiniteArithmeticIncreasing

end ZeroMath.Numbers.CardinalNatural.Decimal.Progressions
