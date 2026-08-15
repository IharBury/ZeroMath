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
      OrdinalNatural.Decimal.toPeano_eq_successor_predecessor_toPeano
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
      OrdinalNatural.Decimal.toPeano_eq_successor_predecessor_toPeano index h
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

/-- Recover the first element of an infinite arithmetic progression from an
element at the given ordinal Decimal index and the common difference by
subtracting `(fromOrdinal index - one) * commonDifference`. Returns `none`
when that subtraction is impossible in the Decimal numbers. -/
def tryFirstFromIndexedElement
    (index : OrdinalNatural.Decimal) (element commonDifference : Decimal) :
    Option Decimal :=
  trySubtract element
    ((subtract (fromOrdinal index) one (one_le_fromOrdinal index)) *
      commonDifference)

/-- Given two ordered indexed elements (`index < index'`) of a prospective
infinite arithmetic progression, recover the common difference
`(element' - element) / (index' - index)`. Returns `none` when the second
element is smaller than the first or the element gap is not divisible by the
index gap. -/
def tryCommonDifferenceFromOrderedIndexedElements
    (index : OrdinalNatural.Decimal) (element : Decimal)
    (index' : OrdinalNatural.Decimal) (element' : Decimal)
    (hlt : index < index') :
    Option Decimal :=
  match trySubtract element' element with
  | none => none
  | some elementDiff =>
    tryDivide elementDiff
      (fromOrdinal (OrdinalNatural.Decimal.subtract index' index hlt))

/-- Reconstruct an infinite arithmetic progression from two of its elements at
different ordinal Decimal indexes. Returns `none` when the values are not
consistent with a non-decreasing infinite arithmetic progression (descending
elements, or an element gap that is not divisible by the index difference).
Indexes are compared up to Decimal equivalence. Zero common difference is
allowed when the two elements agree. -/
def tryFromTwoElements
    (index1 : OrdinalNatural.Decimal) (element1 : Decimal)
    (index2 : OrdinalNatural.Decimal) (element2 : Decimal)
    (hne : ¬ index1 ≈ index2) :
    Option InfiniteArithmetic :=
  match OrdinalNatural.Decimal.compare index1 index2 with
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

/-- Recovering the first element from an indexed element is left-inverse to
`getElement` at that index, up to Decimal equivalence. -/
theorem getElement_of_tryFirstFromIndexedElement
    (index : OrdinalNatural.Decimal) (element commonDifference first : Decimal)
    (h : tryFirstFromIndexedElement index element commonDifference = some first) :
    getElement { first := first, commonDifference := commonDifference } index ≈
      element := by
  simp only [tryFirstFromIndexedElement] at h
  have helement :
      element ≈
        (subtract (fromOrdinal index) one (one_le_fromOrdinal index)) *
            commonDifference +
          first :=
    eq_of_trySubtract_add
      ((subtract (fromOrdinal index) one (one_le_fromOrdinal index)) *
        commonDifference)
      element first h
  simp only [getElement]
  exact
    Setoid.trans (equivalent_add_commutative _ _) (Setoid.symm helement)

/-- Advancing from `index` to a larger `index'` adds
`(fromOrdinal (index' - index)) * commonDifference` to the element, up to
Decimal equivalence. -/
theorem getElement_add_multiply_of_lt (p : InfiniteArithmetic)
    (index index' : OrdinalNatural.Decimal)
    (hlt : index < index') :
    getElement p index' ≈
      getElement p index +
        (fromOrdinal (OrdinalNatural.Decimal.subtract index' index hlt)) *
          p.commonDifference := by
  apply equivalent_of_toPeano_eq
  rw [getElement_toPeano, add_toPeano, getElement_toPeano, multiply_toPeano,
    subtract_fromOrdinal_one_add_of_lt index index' hlt,
    Peano.multiply_distributive_over_add_left, ← Peano.add_associative]

/-- A successful common-difference recovery implies the larger element is
equivalent to the smaller plus the index gap times that difference. -/
theorem eq_add_multiply_of_tryCommonDifferenceFromOrderedIndexedElements
    (index : OrdinalNatural.Decimal) (element : Decimal)
    (index' : OrdinalNatural.Decimal) (element' : Decimal)
    (hlt : index < index')
    (diff : Decimal)
    (h : tryCommonDifferenceFromOrderedIndexedElements
        index element index' element' hlt = some diff) :
    element' ≈
      element +
        (fromOrdinal (OrdinalNatural.Decimal.subtract index' index hlt)) *
          diff := by
  simp only [tryCommonDifferenceFromOrderedIndexedElements] at h
  match hs : trySubtract element' element with
  | none =>
    simp only [hs] at h
    nomatch h
  | some elementDiff =>
    simp only [hs] at h
    have hmul :
        (fromOrdinal (OrdinalNatural.Decimal.subtract index' index hlt)) *
            diff ≈
          elementDiff :=
      eq_of_tryDivide_multiply h
    have hadd : element' ≈ element + elementDiff :=
      eq_of_trySubtract_add element element' elementDiff hs
    exact Setoid.trans hadd (equivalent_add_left (Setoid.symm hmul))

/-- When both indexed recoveries succeed, `getElement` returns values equivalent
to each original element. -/
theorem getElement_of_tryFirst_tryCommonDifference
    (index : OrdinalNatural.Decimal) (element : Decimal)
    (index' : OrdinalNatural.Decimal) (element' : Decimal)
    (hlt : index < index')
    (diff first : Decimal)
    (hdiff : tryCommonDifferenceFromOrderedIndexedElements
        index element index' element' hlt = some diff)
    (hfirst : tryFirstFromIndexedElement index element diff = some first) :
    getElement { first := first, commonDifference := diff } index ≈ element ∧
      getElement { first := first, commonDifference := diff } index' ≈
        element' := by
  have h1 :=
    getElement_of_tryFirstFromIndexedElement index element diff first hfirst
  refine ⟨h1, ?_⟩
  have hgap :=
    eq_add_multiply_of_tryCommonDifferenceFromOrderedIndexedElements
      index element index' element' hlt diff hdiff
  exact
    Setoid.trans
      (Setoid.trans
        (getElement_add_multiply_of_lt
          { first := first, commonDifference := diff } index index' hlt)
        (equivalent_add_right h1))
      (Setoid.symm hgap)

/-- A successful `tryFromTwoElements` yields a progression whose `getElement` at
each of the two indexes recovers the corresponding original element, up to
Decimal equivalence. -/
theorem getElement_of_tryFromTwoElements
    (index1 : OrdinalNatural.Decimal) (element1 : Decimal)
    (index2 : OrdinalNatural.Decimal) (element2 : Decimal)
    (hne : ¬ index1 ≈ index2)
    (p : InfiniteArithmetic)
    (h : tryFromTwoElements index1 element1 index2 element2 hne = some p) :
    getElement p index1 ≈ element1 ∧
      getElement p index2 ≈ element2 := by
  simp only [tryFromTwoElements] at h
  match hc : OrdinalNatural.Decimal.compare index1 index2 with
  | .equivalent heq =>
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

/-- Two infinite arithmetic progressions are equivalent when their underlying
progressions yield related elements (Decimal setoid `≈`) at every positive
ordinal index. -/
def Equivalence (p q : InfiniteArithmetic) : Prop :=
  Sequences.Progression.Equivalence (toProgression p) (toProgression q)

instance : HasEquiv InfiniteArithmetic where
  Equiv := Equivalence

/-- Progressions with the same first element and common difference are
equivalent. -/
theorem equivalence_of_same_params (p q : InfiniteArithmetic)
    (hfirst : p.first = q.first)
    (hdiff : p.commonDifference = q.commonDifference) :
    Equivalence p q := by
  have hpq : toProgression p = toProgression q := by
    simp only [toProgression, hfirst, hdiff]
  intro index
  rw [hpq]
  cases Sequences.Progression.tryGetElement index (toProgression q) with
  | none => exact Option.Rel.none
  | some x => exact Option.Rel.some (Setoid.refl x)

/-- Progressions with equivalent first elements and common differences are
equivalent. -/
theorem equivalence_of_equivalent_params (p q : InfiniteArithmetic)
    (hfirst : p.first ≈ q.first)
    (hdiff : p.commonDifference ≈ q.commonDifference) :
    Equivalence p q := by
  intro index
  induction index with
  | one =>
    simp only [Sequences.Progression.tryGetElement, toProgression]
    exact Option.Rel.some hfirst
  | successor n ih =>
    simp only [Sequences.Progression.tryGetElement]
    match hp : Sequences.Progression.tryGetElement n (toProgression p),
        hq : Sequences.Progression.tryGetElement n (toProgression q), ih with
    | none, none, Option.Rel.none =>
      exact Option.Rel.none
    | some x, some y, Option.Rel.some hxy =>
      simp only [toProgression]
      exact Option.Rel.some (equivalent_add hxy hdiff)
    | none, some _, ih =>
      cases ih
    | some _, none, ih =>
      cases ih

/-- Equivalence of infinite arithmetic progressions implies equivalence of their
first elements. -/
theorem first_equivalent_of_equivalence (p q : InfiniteArithmetic)
    (h : Equivalence p q) : p.first ≈ q.first := by
  have h1 := h OrdinalNatural.Peano.one
  simp only [Sequences.Progression.tryGetElement, toProgression] at h1
  cases h1 with
  | some heq => exact heq

/-- Equivalence of infinite arithmetic progressions implies equivalence of their
common differences. -/
theorem commonDifference_equivalent_of_equivalence (p q : InfiniteArithmetic)
    (h : Equivalence p q) : p.commonDifference ≈ q.commonDifference := by
  have hfirst := first_equivalent_of_equivalence p q h
  have h2 := h OrdinalNatural.Peano.one.successor
  simp only [Sequences.Progression.tryGetElement, toProgression] at h2
  cases h2 with
  | some hadd =>
    apply equivalent_of_toPeano_eq
    have hp := toPeano_eq_of_equivalent hadd
    rw [add_toPeano, add_toPeano, toPeano_eq_of_equivalent hfirst] at hp
    exact Peano.add_left_cancel _ _ _ hp

/-- Equivalence of infinite arithmetic progressions is decidable by comparing
first elements and common differences up to Decimal equivalence. -/
instance (p q : InfiniteArithmetic) : Decidable (p ≈ q) :=
  if hF : p.first ≈ q.first then
    if hD : p.commonDifference ≈ q.commonDifference then
      isTrue (equivalence_of_equivalent_params p q hF hD)
    else
      isFalse fun heq =>
        hD (commonDifference_equivalent_of_equivalence p q heq)
  else
    isFalse fun heq =>
      hF (first_equivalent_of_equivalence p q heq)

/-- Convert an `Option.Rel (· ≈ ·)` fact against `some y` into an explicit
witness. -/
theorem exists_of_option_rel_some {α : Type} [Setoid α] {x : Option α} {y : α}
    (h : Option.Rel (· ≈ ·) x (some y)) :
    ∃ z, x = some z ∧ z ≈ y := by
  cases h with
  | some hz => exact ⟨_, rfl, hz⟩

/-- Recovering the common difference from two indexed elements of an infinite
arithmetic progression returns a value equivalent to that progression's common
difference. -/
theorem tryCommonDifferenceFromOrderedIndexedElements_getElement
    (p : InfiniteArithmetic) (index index' : OrdinalNatural.Decimal)
    (hlt : index < index') :
    ∃ d,
      tryCommonDifferenceFromOrderedIndexedElements
        index (getElement p index) index' (getElement p index') hlt = some d ∧
      d ≈ p.commonDifference := by
  have heq := getElement_add_multiply_of_lt p index index' hlt
  obtain ⟨elementDiff, hsub_eq, hsub_approx⟩ :=
    exists_of_option_rel_some (trySubtract_of_equivalent_add heq)
  have hgap_ne :
      ¬ fromOrdinal (OrdinalNatural.Decimal.subtract index' index hlt) ≈ zero :=
    fromOrdinal_not_equivalent_zero _
  obtain ⟨d, hdiv_eq, hdiv_approx⟩ :=
    exists_of_option_rel_some
      (tryDivide_of_equivalent_multiply hgap_ne hsub_approx)
  refine ⟨d, ?_, hdiv_approx⟩
  simp only [tryCommonDifferenceFromOrderedIndexedElements, hsub_eq, hdiv_eq]

/-- Recovering the first element from an indexed element of an infinite
arithmetic progression, using a common difference equivalent to the
progression's, returns a value equivalent to that progression's first element. -/
theorem tryFirstFromIndexedElement_getElement_of_equivalent_diff
    (p : InfiniteArithmetic) (index : OrdinalNatural.Decimal) (d : Decimal)
    (hd : d ≈ p.commonDifference) :
    ∃ first,
      tryFirstFromIndexedElement index (getElement p index) d = some first ∧
      first ≈ p.first := by
  have hget : getElement p index =
      p.first +
        (subtract (fromOrdinal index) one (one_le_fromOrdinal index)) *
          p.commonDifference :=
    rfl
  have hrel :=
    trySubtract_add_right_of_equivalent p.first
      ((subtract (fromOrdinal index) one (one_le_fromOrdinal index)) *
        p.commonDifference)
      ((subtract (fromOrdinal index) one (one_le_fromOrdinal index)) * d)
      (equivalent_multiply (Setoid.refl _) (Setoid.symm hd))
  obtain ⟨first, hsub_eq, hsub_approx⟩ := exists_of_option_rel_some hrel
  refine ⟨first, ?_, hsub_approx⟩
  simp only [tryFirstFromIndexedElement, hget, hsub_eq]

/-- Recovering the first element from an indexed element of an infinite
arithmetic progression returns a value equivalent to that progression's first
element. -/
theorem tryFirstFromIndexedElement_getElement
    (p : InfiniteArithmetic) (index : OrdinalNatural.Decimal) :
    ∃ first,
      tryFirstFromIndexedElement index (getElement p index) p.commonDifference =
        some first ∧
      first ≈ p.first :=
  tryFirstFromIndexedElement_getElement_of_equivalent_diff p index
    p.commonDifference (Setoid.refl _)

/-- Reconstructing from any two inequivalent indexed elements of an infinite
arithmetic progression recovers a progression equivalent to the original. -/
theorem tryFromTwoElements_getElement
    (p : InfiniteArithmetic) (index1 index2 : OrdinalNatural.Decimal)
    (hne : ¬ index1 ≈ index2) :
    ∃ q,
      tryFromTwoElements
        index1 (getElement p index1) index2 (getElement p index2) hne = some q ∧
      q ≈ p := by
  cases hcomp : OrdinalNatural.Decimal.compare index1 index2 with
  | equivalent heq =>
    exact (hne heq).elim
  | less hlt =>
    obtain ⟨diff, hdiff_eq, hdiff_approx⟩ :=
      tryCommonDifferenceFromOrderedIndexedElements_getElement p index1 index2 hlt
    obtain ⟨first, hfirst_eq, hfirst_approx⟩ :=
      tryFirstFromIndexedElement_getElement_of_equivalent_diff p index1 diff
        hdiff_approx
    refine ⟨{ first := first, commonDifference := diff }, ?_, ?_⟩
    · simp only [tryFromTwoElements, hcomp, hdiff_eq, hfirst_eq]
    · exact equivalence_of_equivalent_params _ p hfirst_approx hdiff_approx
  | greater hgt =>
    obtain ⟨diff, hdiff_eq, hdiff_approx⟩ :=
      tryCommonDifferenceFromOrderedIndexedElements_getElement p index2 index1 hgt
    obtain ⟨first, hfirst_eq, hfirst_approx⟩ :=
      tryFirstFromIndexedElement_getElement_of_equivalent_diff p index2 diff
        hdiff_approx
    refine ⟨{ first := first, commonDifference := diff }, ?_, ?_⟩
    · simp only [tryFromTwoElements, hcomp, hdiff_eq, hfirst_eq]
    · exact equivalence_of_equivalent_params _ p hfirst_approx hdiff_approx

end InfiniteArithmetic

end ZeroMath.Numbers.CardinalNatural.Decimal.Progressions
