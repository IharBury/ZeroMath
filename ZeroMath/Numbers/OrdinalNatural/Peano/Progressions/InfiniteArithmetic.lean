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

/-- The element at the given positive ordinal index. The first element has
index `one`; each successor index advances by the common difference. -/
def getElement (p : InfiniteArithmetic) : Peano → Peano
  | .one => p.first
  | .successor n => getElement p n + p.commonDifference

/-- `tryGetElement` on an infinite arithmetic progression returns
`some (getElement ...)`. -/
theorem tryGetElement_eq_getElement (p : InfiniteArithmetic) (index : Peano) :
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
theorem tryGetElement_eq_some (p : InfiniteArithmetic) (index : Peano) :
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
`(predecessor index) * commonDifference`. Returns `none` when that subtraction
is impossible in the Peano numbers. -/
def tryFirstFromIndexedElement (index element commonDifference : Peano) :
    Option Peano :=
  match index with
  | .one => some element
  | .successor n => trySubtract element (n * commonDifference)

/-- Given two ordered indexed elements (`index < index'`) of a prospective
infinite arithmetic progression, recover the common difference
`(element' - element) / (index' - index)`. Returns `none` when the elements are
not strictly ascending or the element gap is not divisible by the index gap. -/
def tryCommonDifferenceFromOrderedIndexedElements
    (index element index' element' : Peano) (hlt : index < index') :
    Option Peano :=
  match trySubtract element' element with
  | none => none
  | some elementDiff =>
    tryDivide elementDiff (subtract index' index hlt)

/-- Reconstruct an infinite arithmetic progression from two of its elements at
different ordinal indexes. Returns `none` when the values are not consistent
with a strictly increasing infinite arithmetic progression (non-ascending
elements, or an element gap that is not divisible by the index difference). -/
def tryFromTwoElements
    (index1 : Peano) (element1 : Peano)
    (index2 : Peano) (element2 : Peano)
    (hne : index1 ≠ index2) :
    Option InfiniteArithmetic :=
  match compare index1 index2 with
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

/-- The closed form of `getElement` at a successor index. -/
theorem getElement_eq_add_mul (p : InfiniteArithmetic) (n : Peano) :
    getElement p n.successor = p.first + n * p.commonDifference := by
  induction n with
  | one =>
    change p.first + p.commonDifference = p.first + one * p.commonDifference
    rw [one_multiply]
  | successor n ih =>
    calc
      getElement p (successor n).successor
          = getElement p (successor n) + p.commonDifference :=
            rfl
      _ = p.first + n * p.commonDifference + p.commonDifference := by rw [ih]
      _ = p.first + (n * p.commonDifference + p.commonDifference) := by
            rw [add_assoc]
      _ = p.first + (successor n) * p.commonDifference := by rw [succ_multiply]

/-- Recovering the first element from an indexed element is left-inverse to
`getElement` at that index. -/
theorem getElement_of_tryFirstFromIndexedElement
    (index element commonDifference first : Peano)
    (h : tryFirstFromIndexedElement index element commonDifference = some first) :
    getElement { first := first, commonDifference := commonDifference } index =
      element := by
  match index with
  | .one =>
    simp only [tryFirstFromIndexedElement] at h
    injection h with heq
    simp only [getElement, heq]
  | .successor n =>
    simp only [tryFirstFromIndexedElement] at h
    have helement : element = n * commonDifference + first :=
      eq_of_trySubtract_add (n * commonDifference) element first h
    rw [getElement_eq_add_mul, add_comm, helement]

/-- Advancing from `index` to a larger `index'` adds
`(index' - index) * commonDifference` to the element. -/
theorem getElement_add_mul_of_lt (p : InfiniteArithmetic) (index index' : Peano)
    (hlt : index < index') :
    getElement p index' =
      getElement p index +
        (subtract index' index hlt) * p.commonDifference := by
  match index, index' with
  | .one, .one =>
    exact (not_lt_self one hlt).elim
  | .one, .successor n =>
    have hsub : subtract n.successor one hlt = n := subtract_succ_one n hlt
    change getElement p n.successor =
      p.first + (subtract n.successor one hlt) * p.commonDifference
    rw [getElement_eq_add_mul, hsub]
  | .successor m, .one =>
    exact (not_lt_one m.successor hlt).elim
  | .successor m, .successor n =>
    have hlt' : m < n := lt_of_succ_lt_succ hlt
    have hsub :
        subtract n.successor m.successor hlt = subtract n m hlt' := by
      change subtract n m (lt_of_succ_lt_succ hlt) = subtract n m hlt'
      exact subtract_eq_of_eq _ _ rfl rfl
    rw [getElement_eq_add_mul, getElement_eq_add_mul, hsub]
    have hsum : m + subtract n m hlt' = n := by
      rw [add_comm]
      exact subtract_add_cancel n m hlt'
    calc
      p.first + n * p.commonDifference
          = p.first + (m + subtract n m hlt') * p.commonDifference := by
            rw [hsum]
      _ = p.first +
            (m * p.commonDifference +
              (subtract n m hlt') * p.commonDifference) := by
            rw [multiply_comm (m + subtract n m hlt'), multiply_add,
              multiply_comm p.commonDifference m,
              multiply_comm p.commonDifference (subtract n m hlt')]
      _ = p.first + m * p.commonDifference +
            (subtract n m hlt') * p.commonDifference := by rw [← add_assoc]

/-- A successful common-difference recovery implies the larger element equals
the smaller plus the index gap times that difference. -/
theorem eq_add_mul_of_tryCommonDifferenceFromOrderedIndexedElements
    (index element index' element' : Peano) (hlt : index < index')
    (diff : Peano)
    (h : tryCommonDifferenceFromOrderedIndexedElements
        index element index' element' hlt = some diff) :
    element' =
      element + (subtract index' index hlt) * diff := by
  simp only [tryCommonDifferenceFromOrderedIndexedElements] at h
  match hs : trySubtract element' element with
  | none =>
    simp only [hs] at h
    nomatch h
  | some elementDiff =>
    simp only [hs] at h
    have hmul : (subtract index' index hlt) * diff = elementDiff :=
      eq_of_tryDivide_mul h
    have hadd : element' = element + elementDiff :=
      eq_of_trySubtract_add element element' elementDiff hs
    rw [hadd, hmul]

/-- When both indexed recoveries succeed, `getElement` returns each original
element. -/
theorem getElement_of_tryFirst_tryCommonDifference
    (index element index' element' : Peano) (hlt : index < index')
    (diff first : Peano)
    (hdiff : tryCommonDifferenceFromOrderedIndexedElements
        index element index' element' hlt = some diff)
    (hfirst : tryFirstFromIndexedElement index element diff = some first) :
    getElement { first := first, commonDifference := diff } index = element ∧
      getElement { first := first, commonDifference := diff } index' =
        element' := by
  have h1 :=
    getElement_of_tryFirstFromIndexedElement index element diff first hfirst
  refine ⟨h1, ?_⟩
  have hgap :=
    eq_add_mul_of_tryCommonDifferenceFromOrderedIndexedElements
      index element index' element' hlt diff hdiff
  rw [getElement_add_mul_of_lt _ index index' hlt, h1, hgap]

/-- A successful `tryFromTwoElements` yields a progression whose `getElement` at
each of the two indexes recovers the corresponding original element. -/
theorem getElement_of_tryFromTwoElements
    (index1 element1 index2 element2 : Peano)
    (hne : index1 ≠ index2)
    (p : InfiniteArithmetic)
    (h : tryFromTwoElements index1 element1 index2 element2 hne = some p) :
    getElement p index1 = element1 ∧
      getElement p index2 = element2 := by
  simp only [tryFromTwoElements] at h
  match hc : compare index1 index2 with
  | .equal heq =>
    exact (hne heq).elim
  | .less hlt =>
    simp only [hc] at h
    match hd : tryCommonDifferenceFromOrderedIndexedElements
        index1 element1 index2 element2 hlt with
    | none =>
      simp only [hd] at h
      nomatch h
    | some diff =>
      simp only [hd] at h
      match hf : tryFirstFromIndexedElement index1 element1 diff with
      | none =>
        simp only [hf] at h
        nomatch h
      | some first =>
        simp only [hf] at h
        injection h with hp
        subst hp
        exact
          getElement_of_tryFirst_tryCommonDifference
            index1 element1 index2 element2 hlt diff first hd hf
  | .greater hgt =>
    simp only [hc] at h
    match hd : tryCommonDifferenceFromOrderedIndexedElements
        index2 element2 index1 element1 hgt with
    | none =>
      simp only [hd] at h
      nomatch h
    | some diff =>
      simp only [hd] at h
      match hf : tryFirstFromIndexedElement index2 element2 diff with
      | none =>
        simp only [hf] at h
        nomatch h
      | some first =>
        simp only [hf] at h
        injection h with hp
        subst hp
        have hget :=
          getElement_of_tryFirst_tryCommonDifference
            index2 element2 index1 element1 hgt diff first hd hf
        exact ⟨hget.2, hget.1⟩

/-- Recovering the common difference from two indexed elements of an infinite
arithmetic progression returns that progression's common difference. -/
theorem tryCommonDifferenceFromOrderedIndexedElements_getElement
    (p : InfiniteArithmetic) (index index' : Peano) (hlt : index < index') :
    tryCommonDifferenceFromOrderedIndexedElements
      index (getElement p index) index' (getElement p index') hlt =
      some p.commonDifference := by
  simp only [tryCommonDifferenceFromOrderedIndexedElements]
  have heq := getElement_add_mul_of_lt p index index' hlt
  have hsub :
      trySubtract (getElement p index') (getElement p index) =
        some ((subtract index' index hlt) * p.commonDifference) := by
    rw [heq]
    exact trySubtract_self_add _ _
  simp only [hsub]
  exact tryDivide_mul p.commonDifference (subtract index' index hlt)

/-- Recovering the first element from an indexed element of an infinite
arithmetic progression returns that progression's first element. -/
theorem tryFirstFromIndexedElement_getElement
    (p : InfiniteArithmetic) (index : Peano) :
    tryFirstFromIndexedElement index (getElement p index) p.commonDifference =
      some p.first := by
  match index with
  | .one =>
    simp only [tryFirstFromIndexedElement, getElement]
  | .successor n =>
    simp only [tryFirstFromIndexedElement, getElement_eq_add_mul]
    exact trySubtract_add_right p.first (n * p.commonDifference)

/-- Reconstructing from any two distinct elements of an infinite arithmetic
progression recovers that same progression. -/
theorem tryFromTwoElements_getElement
    (p : InfiniteArithmetic) (index1 index2 : Peano) (hne : index1 ≠ index2) :
    tryFromTwoElements
      index1 (getElement p index1) index2 (getElement p index2) hne =
      some p := by
  simp only [tryFromTwoElements]
  match compare index1 index2 with
  | .equal heq =>
    exact (hne heq).elim
  | .less hlt =>
    have hdiff :=
      tryCommonDifferenceFromOrderedIndexedElements_getElement p index1 index2 hlt
    have hfirst := tryFirstFromIndexedElement_getElement p index1
    simp only [hdiff, hfirst]
  | .greater hgt =>
    have hdiff :=
      tryCommonDifferenceFromOrderedIndexedElements_getElement p index2 index1 hgt
    have hfirst := tryFirstFromIndexedElement_getElement p index2
    simp only [hdiff, hfirst]

end InfiniteArithmetic

end ZeroMath.Numbers.OrdinalNatural.Peano.Progressions
