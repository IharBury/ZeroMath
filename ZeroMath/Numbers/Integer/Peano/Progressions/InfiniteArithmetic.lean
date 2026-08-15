import ZeroMath.Numbers.Integer.Peano
import ZeroMath.Sequences.Progression

namespace ZeroMath.Numbers.Integer.Peano.Progressions

/-- An infinite arithmetic progression of integer Peano numbers, defined by the
first element and the common difference. When the common difference is positive
the progression is strictly increasing; when it is negative it is strictly
decreasing; when it is zero every element equals the first. -/
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
`(positive (predecessor index)) * commonDifference`. Integer subtraction is
total, so this always succeeds. -/
def tryFirstFromIndexedElement
    (index : OrdinalNatural.Peano) (element commonDifference : Peano) :
    Option Peano :=
  match index with
  | .one => some element
  | .successor n => some (element - (positive n * commonDifference))

/-- Given two ordered indexed elements (`index < index'`) of a prospective
infinite arithmetic progression, recover the common difference
`(element' - element) / (index' - index)`. Returns `none` when the element gap
is not divisible by the index gap. Unlike the natural-number versions, the
element difference may be negative or zero, so the recovered common difference
may be negative or zero as well. -/
def tryCommonDifferenceFromOrderedIndexedElements
    (index : OrdinalNatural.Peano) (element : Peano)
    (index' : OrdinalNatural.Peano) (element' : Peano)
    (hlt : index < index') :
    Option Peano :=
  tryDivide (element' - element)
    (positive (OrdinalNatural.Peano.subtract index' index hlt))

/-- Reconstruct an infinite arithmetic progression from two of its elements at
different ordinal indexes. Returns `none` when the element gap is not
divisible by the index difference. -/
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

/-- The closed form of `getElement` at a successor index. -/
theorem getElement_eq_add_multiply (p : InfiniteArithmetic) (n : OrdinalNatural.Peano) :
    getElement p n.successor = p.first + positive n * p.commonDifference := by
  induction n with
  | one =>
    change p.first + p.commonDifference = p.first + one * p.commonDifference
    rw [one_multiply]
  | successor n ih =>
    have hmul :
        positive n.successor * p.commonDifference =
          positive n * p.commonDifference + p.commonDifference := by
      rw [multiply_commutative, multiply_positive_successor, multiply_commutative (positive n)]
    calc
      getElement p (OrdinalNatural.Peano.successor n).successor
          = getElement p (OrdinalNatural.Peano.successor n) + p.commonDifference :=
            rfl
      _ = p.first + positive n * p.commonDifference + p.commonDifference := by
            rw [ih]
      _ = p.first + (positive n * p.commonDifference + p.commonDifference) := by
            rw [add_associative]
      _ = p.first + positive n.successor * p.commonDifference := by
            rw [hmul]

/-- Recovering the first element from an indexed element is left-inverse to
`getElement` at that index. -/
theorem getElement_of_tryFirstFromIndexedElement
    (index : OrdinalNatural.Peano) (element commonDifference first : Peano)
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
    injection h with heq
    have helement : element = first + positive n * commonDifference := by
      have hsum : first + positive n * commonDifference = element := by
        rw [← heq]
        exact subtract_add_cancel element (positive n * commonDifference)
      exact hsum.symm
    rw [getElement_eq_add_multiply, ← helement]

/-- Advancing from `index` to a larger `index'` adds
`(positive (index' - index)) * commonDifference` to the element. -/
theorem getElement_add_multiply_of_lt (p : InfiniteArithmetic)
    (index index' : OrdinalNatural.Peano)
    (hlt : index < index') :
    getElement p index' =
      getElement p index +
        (positive (OrdinalNatural.Peano.subtract index' index hlt)) *
          p.commonDifference := by
  match index, index' with
  | .one, .one =>
    exact (OrdinalNatural.Peano.not_lt_self OrdinalNatural.Peano.one hlt).elim
  | .one, .successor n =>
    have hsub : OrdinalNatural.Peano.subtract n.successor OrdinalNatural.Peano.one hlt = n :=
      OrdinalNatural.Peano.subtract_successor_one n hlt
    change getElement p n.successor =
      p.first +
        (positive (OrdinalNatural.Peano.subtract n.successor OrdinalNatural.Peano.one hlt)) *
          p.commonDifference
    rw [getElement_eq_add_multiply, hsub]
  | .successor m, .one =>
    exact (OrdinalNatural.Peano.not_lt_one m.successor hlt).elim
  | .successor m, .successor n =>
    have hlt' : m < n := OrdinalNatural.Peano.lt_of_successor_lt_successor hlt
    have hsub :
        OrdinalNatural.Peano.subtract n.successor m.successor hlt =
          OrdinalNatural.Peano.subtract n m hlt' := by
      change OrdinalNatural.Peano.subtract n m (OrdinalNatural.Peano.lt_of_successor_lt_successor hlt) =
        OrdinalNatural.Peano.subtract n m hlt'
      exact OrdinalNatural.Peano.subtract_eq_of_eq _ _ rfl rfl
    rw [getElement_eq_add_multiply, getElement_eq_add_multiply, hsub]
    have hsum : m + OrdinalNatural.Peano.subtract n m hlt' = n := by
      rw [OrdinalNatural.Peano.add_commutative]
      exact OrdinalNatural.Peano.subtract_add_cancel n m hlt'
    have hpos :
        positive n =
          positive m + positive (OrdinalNatural.Peano.subtract n m hlt') := by
      have heq :
          positive n =
            positive (m + OrdinalNatural.Peano.subtract n m hlt') :=
        congrArg positive hsum.symm
      exact heq.trans (add_positive_positive m _).symm
    have hmul :
        (positive m + positive (OrdinalNatural.Peano.subtract n m hlt')) *
            p.commonDifference =
          positive m * p.commonDifference +
            positive (OrdinalNatural.Peano.subtract n m hlt') *
              p.commonDifference := by
      rw [multiply_commutative, multiply_add, multiply_commutative p.commonDifference (positive m),
        multiply_commutative p.commonDifference
          (positive (OrdinalNatural.Peano.subtract n m hlt'))]
    calc
      p.first + positive n * p.commonDifference
          = p.first +
              (positive m + positive (OrdinalNatural.Peano.subtract n m hlt')) *
                p.commonDifference := by
            rw [hpos]
      _ = p.first +
            (positive m * p.commonDifference +
              positive (OrdinalNatural.Peano.subtract n m hlt') *
                p.commonDifference) := by
            rw [hmul]
      _ = p.first + positive m * p.commonDifference +
            positive (OrdinalNatural.Peano.subtract n m hlt') *
              p.commonDifference := by
            rw [← add_associative]

/-- A successful common-difference recovery implies the larger element equals
the smaller plus the index gap times that difference. -/
theorem eq_add_multiply_of_tryCommonDifferenceFromOrderedIndexedElements
    (index : OrdinalNatural.Peano) (element : Peano)
    (index' : OrdinalNatural.Peano) (element' : Peano)
    (hlt : index < index')
    (diff : Peano)
    (h : tryCommonDifferenceFromOrderedIndexedElements
        index element index' element' hlt = some diff) :
    element' =
      element +
        (positive (OrdinalNatural.Peano.subtract index' index hlt)) * diff := by
  simp only [tryCommonDifferenceFromOrderedIndexedElements] at h
  have hmul :
      (positive (OrdinalNatural.Peano.subtract index' index hlt)) * diff =
        element' - element :=
    eq_of_tryDivide_multiply h
  calc
    element'
        = (element' - element) + element := (subtract_add_cancel element' element).symm
    _ = element + (element' - element) := add_commutative _ _
    _ = element +
          (positive (OrdinalNatural.Peano.subtract index' index hlt)) * diff := by
          rw [hmul]

/-- When both indexed recoveries succeed, `getElement` returns each original
element. -/
theorem getElement_of_tryFirst_tryCommonDifference
    (index : OrdinalNatural.Peano) (element : Peano)
    (index' : OrdinalNatural.Peano) (element' : Peano)
    (hlt : index < index')
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
    eq_add_multiply_of_tryCommonDifferenceFromOrderedIndexedElements
      index element index' element' hlt diff hdiff
  rw [getElement_add_multiply_of_lt _ index index' hlt, h1, hgap]

/-- A successful `tryFromTwoElements` yields a progression whose `getElement` at
each of the two indexes recovers the corresponding original element. -/
theorem getElement_of_tryFromTwoElements
    (index1 : OrdinalNatural.Peano) (element1 : Peano)
    (index2 : OrdinalNatural.Peano) (element2 : Peano)
    (hne : index1 ≠ index2)
    (p : InfiniteArithmetic)
    (h : tryFromTwoElements index1 element1 index2 element2 hne = some p) :
    getElement p index1 = element1 ∧
      getElement p index2 = element2 := by
  simp only [tryFromTwoElements] at h
  match hc : OrdinalNatural.Peano.compare index1 index2 with
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
    (p : InfiniteArithmetic) (index index' : OrdinalNatural.Peano)
    (hlt : index < index') :
    tryCommonDifferenceFromOrderedIndexedElements
      index (getElement p index) index' (getElement p index') hlt =
      some p.commonDifference := by
  simp only [tryCommonDifferenceFromOrderedIndexedElements]
  have heq := getElement_add_multiply_of_lt p index index' hlt
  have hsub :
      getElement p index' - getElement p index =
        (positive (OrdinalNatural.Peano.subtract index' index hlt)) *
          p.commonDifference := by
    rw [heq, add_subtract_cancel_left]
  rw [hsub]
  exact
    tryDivide_multiply p.commonDifference
      (positive (OrdinalNatural.Peano.subtract index' index hlt))
      (positive_ne_zero _)

/-- Recovering the first element from an indexed element of an infinite
arithmetic progression returns that progression's first element. -/
theorem tryFirstFromIndexedElement_getElement
    (p : InfiniteArithmetic) (index : OrdinalNatural.Peano) :
    tryFirstFromIndexedElement index (getElement p index) p.commonDifference =
      some p.first := by
  match index with
  | .one =>
    simp only [tryFirstFromIndexedElement, getElement]
  | .successor n =>
    simp only [tryFirstFromIndexedElement, getElement_eq_add_multiply, add_subtract_cancel]

/-- Reconstructing from any two distinct elements of an infinite arithmetic
progression recovers that same progression. -/
theorem tryFromTwoElements_getElement
    (p : InfiniteArithmetic) (index1 index2 : OrdinalNatural.Peano)
    (hne : index1 ≠ index2) :
    tryFromTwoElements
      index1 (getElement p index1) index2 (getElement p index2) hne =
      some p := by
  simp only [tryFromTwoElements]
  match OrdinalNatural.Peano.compare index1 index2 with
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

end ZeroMath.Numbers.Integer.Peano.Progressions
