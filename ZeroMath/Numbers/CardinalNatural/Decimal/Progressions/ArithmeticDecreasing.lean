import ZeroMath.Numbers.CardinalNatural.Decimal
import ZeroMath.Sequences.Progression

namespace ZeroMath.Numbers.CardinalNatural.Decimal.Progressions

/-- An arithmetic progression of Decimal numbers with subtractive common
difference, defined by an optional first element (`none` for the empty
progression), the common difference (subtracted at each step), and a limit
such that no element is less than the limit. The progression is also empty
when the first element is less than the limit. -/
structure ArithmeticDecreasing where
  first : Option Decimal
  subtractiveCommonDifference : Decimal
  limit : Decimal
  subtractiveCommonDifference_ne_zero : ¬ subtractiveCommonDifference ≈ zero

namespace ArithmeticDecreasing

/-- Convert a decreasing arithmetic progression to a general progression by
taking the same optional first element when it is not less than the limit
(otherwise the empty progression) and subtracting the common difference while
the next element is not less than the limit. -/
def toProgression (p : ArithmeticDecreasing) : Sequences.Progression Decimal where
  first :=
    match p.first with
    | none => none
    | some x => if p.limit ≤ x then some x else none
  next := fun x =>
    match trySubtract x p.subtractiveCommonDifference with
    | none => none
    | some y => if p.limit ≤ y then some y else none

/-- Every element obtained from `tryGetElement` is at least the limit. -/
theorem limit_le_of_tryGetElement_eq_some (p : ArithmeticDecreasing)
    (index : OrdinalNatural.Peano) (x : Decimal)
    (h : Sequences.Progression.tryGetElement index (toProgression p) = some x) :
    p.limit ≤ x := by
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
            if p.limit ≤ y then some y else none := by
        simp only [toProgression, hf]
      rw [hprog] at hfirst
      by_cases hle : p.limit ≤ y
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
      cases hs : trySubtract y p.subtractiveCommonDifference with
      | none =>
        have : (toProgression p).next y = none := by
          simp only [toProgression, hs]
        rw [this] at hnext
        nomatch hnext
      | some z =>
        have hprog :
            (toProgression p).next y =
              if p.limit ≤ z then some z else none := by
          simp only [toProgression, hs]
        rw [hprog] at hnext
        by_cases hle : p.limit ≤ z
        · simp only [hle, ↓reduceIte] at hnext
          injection hnext with heq
          exact heq ▸ hle
        · simp only [hle, ↓reduceIte] at hnext
          nomatch hnext

/-- If `next` yields a value, that value is strictly less than its predecessor,
since the subtractive common difference is positive. -/
theorem lt_of_next_eq_some (p : ArithmeticDecreasing) (y x : Decimal)
    (h : (toProgression p).next y = some x) :
    x < y := by
  cases hs : trySubtract y p.subtractiveCommonDifference with
  | none =>
    have : (toProgression p).next y = none := by
      simp only [toProgression, hs]
    rw [this] at h
    nomatch h
  | some z =>
    have hprog :
        (toProgression p).next y =
          if p.limit ≤ z then some z else none := by
      simp only [toProgression, hs]
    rw [hprog] at h
    by_cases hle : p.limit ≤ z
    · simp only [hle, ↓reduceIte] at h
      injection h with heq
      obtain ⟨hlt, hsub⟩ := exists_subtract_of_trySubtract hs
      have hadd : z + p.subtractiveCommonDifference ≈ y := by
        rw [← hsub]
        exact subtract_add_cancel y p.subtractiveCommonDifference hlt
      have hpeano :
          z.toPeano + p.subtractiveCommonDifference.toPeano = y.toPeano := by
        rw [← add_toPeano, toPeano_eq_of_equivalent hadd]
      have hone : Peano.one ≤ p.subtractiveCommonDifference.toPeano :=
        Peano.succ_le_of_lt
          (Peano.zero_lt_of_ne_zero _
            (toPeano_ne_zero_of_not_equivalent_zero
              p.subtractiveCommonDifference_ne_zero))
      have hz_le : Peano.successor z.toPeano ≤ y.toPeano := by
        rw [← Peano.add_one, ← hpeano]
        exact Peano.add_le_add_left hone z.toPeano
      exact heq ▸ Peano.lt_of_succ_le hz_le
    · simp only [hle, ↓reduceIte] at h
      nomatch h

/-- If `tryGetElement` returns a value and the progression starts at `first`,
then `fromOrdinal index + x.toPeano ≤ successor first.toPeano`. Each step
decreases the value by at least one while the ordinal index (as a cardinal)
increases by one, so their sum never exceeds that of the first element. -/
theorem fromOrdinal_add_le_succ_first_of_tryGetElement (p : ArithmeticDecreasing)
    (first : Decimal) (index : OrdinalNatural.Peano) (x : Decimal)
    (hf : (toProgression p).first = some first)
    (h : Sequences.Progression.tryGetElement index (toProgression p) = some x) :
    Peano.fromOrdinal index + x.toPeano ≤ first.toPeano.successor := by
  induction index generalizing x with
  | one =>
    simp only [Sequences.Progression.tryGetElement] at h
    have heq : x = first := by
      rw [hf] at h
      injection h with heq
      exact heq.symm
    rw [heq, Peano.fromOrdinal, Peano.one_add]
    exact Or.inr rfl
  | successor n ih =>
    simp only [Sequences.Progression.tryGetElement] at h
    cases hm : Sequences.Progression.tryGetElement n (toProgression p) with
    | none =>
      rw [hm] at h
      nomatch h
    | some y =>
      rw [hm] at h
      have hnext : (toProgression p).next y = some x := h
      have hlt : x < y := lt_of_next_eq_some p y x hnext
      have hx_le : x.toPeano.successor ≤ y.toPeano :=
        Peano.succ_le_of_lt hlt
      have hn : Peano.fromOrdinal n + y.toPeano ≤ first.toPeano.successor :=
        ih y hm
      have hmid :
          Peano.fromOrdinal n + x.toPeano.successor ≤
            Peano.fromOrdinal n + y.toPeano :=
        Peano.add_le_add_left hx_le (Peano.fromOrdinal n)
      have hmid' :
          Peano.fromOrdinal n + x.toPeano.successor ≤ first.toPeano.successor :=
        Peano.le_trans hmid hn
      have heqadd :
          Peano.fromOrdinal n.successor + x.toPeano =
            Peano.fromOrdinal n + x.toPeano.successor := by
        change (Peano.fromOrdinal n).successor + x.toPeano =
          Peano.fromOrdinal n + x.toPeano.successor
        rw [Peano.successor_add, Peano.add_successor]
      exact heqadd ▸ hmid'

/-- The progression obtained from a decreasing arithmetic progression is finite:
if it is empty then `tryGetElement` at `one` is `none`; otherwise, starting from
`first`, `tryGetElement` at the ordinal for `successor (successor first.toPeano)`
cannot return `some`, since that value `x` would need
`successor (successor first.toPeano) + x.toPeano ≤ successor first.toPeano`. -/
theorem toProgression_finite (p : ArithmeticDecreasing) :
    Sequences.Progression.Finite (toProgression p) := by
  match hf : (toProgression p).first with
  | none =>
    refine ⟨OrdinalNatural.Peano.one, ?_⟩
    simp only [Sequences.Progression.tryGetElement, hf]
  | some first =>
    have hne : (first.toPeano.successor).successor ≠ Peano.zero :=
      Peano.successor_ne_zero first.toPeano.successor
    refine ⟨Peano.toOrdinal (first.toPeano.successor).successor hne, ?_⟩
    cases h :
        Sequences.Progression.tryGetElement
          (Peano.toOrdinal (first.toPeano.successor).successor hne)
          (toProgression p) with
    | none =>
      rfl
    | some x =>
      have hle :=
        fromOrdinal_add_le_succ_first_of_tryGetElement p first
          (Peano.toOrdinal (first.toPeano.successor).successor hne) x hf h
      rw [Peano.fromOrdinal_toOrdinal] at hle
      have hle' : (first.toPeano.successor).successor ≤ first.toPeano.successor :=
        Peano.le_trans
          (Peano.le_add_self_left (first.toPeano.successor).successor x.toPeano) hle
      exact (Peano.not_succ_le first.toPeano.successor hle').elim

end ArithmeticDecreasing

end ZeroMath.Numbers.CardinalNatural.Decimal.Progressions
