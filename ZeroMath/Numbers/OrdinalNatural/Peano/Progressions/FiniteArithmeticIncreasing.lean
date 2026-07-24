import ZeroMath.Numbers.OrdinalNatural.Peano
import ZeroMath.Sequences.Progression

namespace ZeroMath.Numbers.OrdinalNatural.Peano.Progressions

/-- A finite increasing arithmetic progression of Peano numbers with positive
common difference, defined by an optional first element (`none` for the empty
progression), the common difference, and a limit such that no element is
greater than the limit. The progression is also empty when the first element
is greater than the limit. Because every Peano number is at least one, the
common difference is always positive. -/
structure FiniteArithmeticIncreasing where
  first : Option Peano
  commonDifference : Peano
  limit : Peano

namespace FiniteArithmeticIncreasing

/-- Convert a finite increasing arithmetic progression to a general progression
by taking the same optional first element when it does not exceed the limit
(otherwise the empty progression) and advancing by the common difference while
the next element does not exceed the limit. -/
def toProgression (p : FiniteArithmeticIncreasing) : Sequences.Progression Peano where
  first :=
    match p.first with
    | none => none
    | some x => if x ≤ p.limit then some x else none
  next := fun x =>
    let y := x + p.commonDifference
    if y ≤ p.limit then some y else none

/-- Every element obtained from `tryGetElement` is at most the limit. -/
theorem tryGetElement_le_limit (p : FiniteArithmeticIncreasing) (index x : Peano)
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

/-- If `tryGetElement` returns a value, that value is at least the index
(identifying the shared Peano type), because the progression is strictly
increasing with positive common difference. -/
theorem le_of_tryGetElement_eq_some (p : FiniteArithmeticIncreasing)
    (index x : Peano)
    (h : Sequences.Progression.tryGetElement index (toProgression p) = some x) :
    index ≤ x := by
  induction index generalizing x with
  | one =>
    exact one_le' x
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
        have hn : n ≤ y := ih y hm
        have hsucc : successor n ≤ successor y := succ_le_succ hn
        have hy_le : successor y ≤ y + p.commonDifference := by
          rw [← add_one]
          exact le_add_of_le_right y (one_le' p.commonDifference)
        exact le_trans hsucc (heq ▸ hy_le)
      · simp only [hle, ↓reduceIte] at hnext
        nomatch hnext

/-- The progression obtained from a finite increasing arithmetic progression is
finite: `tryGetElement` at `successor limit` is always `none`, since any
returned value would have to be both ≥ `successor limit` and ≤ `limit`. -/
theorem toProgression_finite (p : FiniteArithmeticIncreasing) :
    Sequences.Progression.Finite (toProgression p) := by
  refine ⟨successor p.limit, ?_⟩
  cases h : Sequences.Progression.tryGetElement (successor p.limit) (toProgression p) with
  | none =>
    rfl
  | some x =>
    have hle_lim := tryGetElement_le_limit p (successor p.limit) x h
    have hle_idx := le_of_tryGetElement_eq_some p (successor p.limit) x h
    exact (not_succ_le p.limit (le_trans hle_idx hle_lim)).elim

/-- The length of a finite increasing arithmetic progression: the number of
elements before `tryGetElement` first returns `none`. -/
def getLength (p : FiniteArithmeticIncreasing) : CardinalNatural.Peano :=
  Sequences.Progression.getLength (toProgression p) (toProgression_finite p)

end FiniteArithmeticIncreasing

end ZeroMath.Numbers.OrdinalNatural.Peano.Progressions
