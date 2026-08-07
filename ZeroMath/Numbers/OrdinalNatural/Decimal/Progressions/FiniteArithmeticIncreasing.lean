import ZeroMath.Numbers.OrdinalNatural.Decimal
import ZeroMath.Sequences.Progression

namespace ZeroMath.Numbers.OrdinalNatural.Decimal.Progressions

/-- A finite increasing arithmetic progression of Decimal numbers with positive
common difference, defined by an optional first element (`none` for the empty
progression), the common difference, and a limit such that no element is
greater than the limit. The progression is also empty when the first element
is greater than the limit. Because every Decimal number is at least one, the
common difference is always positive. -/
structure FiniteArithmeticIncreasing where
  first : Option Decimal
  commonDifference : Decimal
  limit : Decimal

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

/-- Decimal order is reflected by the Peano embedding. -/
theorem toPeano_le_of_le {a b : Decimal} (h : a ≤ b) : a.toPeano ≤ b.toPeano := by
  cases h with
  | inl hlt => exact Or.inl hlt
  | inr heq => exact Or.inr (toPeano_eq_of_equivalent heq)

/-- Every element obtained from `tryGetElement` is at most the limit. -/
theorem tryGetElement_le_limit (p : FiniteArithmeticIncreasing)
    (index : Peano) (x : Decimal)
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

/-- If `tryGetElement` returns a value, the Peano index is at most the Peano
embedding of that value, because the progression is strictly increasing with
positive common difference. -/
theorem le_of_tryGetElement_eq_some (p : FiniteArithmeticIncreasing)
    (index : Peano) (x : Decimal)
    (h : Sequences.Progression.tryGetElement index (toProgression p) = some x) :
    index ≤ x.toPeano := by
  induction index generalizing x with
  | one =>
    exact Peano.one_le' x.toPeano
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
        have hn : n ≤ y.toPeano := ih y hm
        have hsucc : Peano.successor n ≤ Peano.successor y.toPeano :=
          Peano.succ_le_succ hn
        have hy_le : Peano.successor y.toPeano ≤
            (y + p.commonDifference).toPeano := by
          rw [add_toPeano, ← Peano.add_one]
          exact Peano.le_add_of_le_right y.toPeano
            (Peano.one_le' p.commonDifference.toPeano)
        exact Peano.le_trans hsucc (heq ▸ hy_le)
      · simp only [hle, ↓reduceIte] at hnext
        nomatch hnext

/-- The progression obtained from a finite increasing arithmetic progression is
finite: `tryGetElement` at `successor limit.toPeano` is always `none`, since any
returned value would have to be both ≥ `successor limit.toPeano` and
≤ `limit.toPeano`. -/
theorem toProgression_finite (p : FiniteArithmeticIncreasing) :
    Sequences.Progression.Finite (toProgression p) := by
  refine ⟨Peano.successor p.limit.toPeano, ?_⟩
  cases h :
      Sequences.Progression.tryGetElement
        (Peano.successor p.limit.toPeano) (toProgression p) with
  | none =>
    rfl
  | some x =>
    have hle_lim :=
      tryGetElement_le_limit p (Peano.successor p.limit.toPeano) x h
    have hle_idx :=
      le_of_tryGetElement_eq_some p (Peano.successor p.limit.toPeano) x h
    exact (Peano.not_succ_le p.limit.toPeano
      (Peano.le_trans hle_idx (toPeano_le_of_le hle_lim))).elim

end FiniteArithmeticIncreasing

end ZeroMath.Numbers.OrdinalNatural.Decimal.Progressions
