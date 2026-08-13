import ZeroMath.Numbers.Integer.Decimal
import ZeroMath.Numbers.Integer.Peano.Progressions.InfiniteArithmetic
import ZeroMath.Sequences.Progression

namespace ZeroMath.Numbers.Integer.Decimal.Progressions

/-- An infinite arithmetic progression of Decimal integers, defined by the
first element and the common difference. When the common difference is positive
the progression is strictly increasing; when it is negative it is strictly
decreasing; when it is zero every element is equivalent to the first. -/
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

/-- Convert an infinite arithmetic progression of Decimal integers to the
corresponding Peano infinite arithmetic progression by embedding the first
element and common difference via `Decimal.toPeano`. -/
def toPeano (p : InfiniteArithmetic) : Peano.Progressions.InfiniteArithmetic where
  first := p.first.toPeano
  commonDifference := p.commonDifference.toPeano

/-- The coefficient `fromOrdinalPositive index - one` used by the closed-form
element at a positive ordinal Decimal index. -/
def indexCoefficient (index : OrdinalNatural.Decimal) : Decimal :=
  fromOrdinalPositive index.toPeano - one

/-- The element at the given positive ordinal Decimal index. Always the closed
form `first + (fromOrdinalPositive index - one) * commonDifference`, with no
iteration on the index and no case split on whether the index is `one`. -/
def getElement (p : InfiniteArithmetic) (index : OrdinalNatural.Decimal) :
    Decimal :=
  p.first + indexCoefficient index * p.commonDifference

/-- The Peano embedding of `indexCoefficient`. -/
theorem indexCoefficient_toPeano (index : OrdinalNatural.Decimal) :
    (indexCoefficient index).toPeano =
      Peano.positive index.toPeano - Peano.one :=
  fromOrdinalPositive_sub_one_toPeano index.toPeano

/-- The Peano embedding of `getElement`. -/
theorem getElement_toPeano (p : InfiniteArithmetic)
    (index : OrdinalNatural.Decimal) :
    (getElement p index).toPeano =
      p.first.toPeano +
        (indexCoefficient index).toPeano * p.commonDifference.toPeano := by
  simp only [getElement, add_toPeano, multiply_toPeano]

/-- At an index equivalent to `one`, `getElement` is equivalent to the first
element. -/
theorem getElement_equivalent_first_of_equivalent_one (p : InfiniteArithmetic)
    (index : OrdinalNatural.Decimal)
    (h : index ≈ OrdinalNatural.Decimal.one) :
    getElement p index ≈ p.first := by
  apply equivalent_of_toPeano_eq
  rw [getElement_toPeano, indexCoefficient_toPeano]
  have hone : index.toPeano = OrdinalNatural.Peano.one :=
    (OrdinalNatural.Decimal.toPeano_eq_one_iff_equivalent_one index).mpr h
  rw [hone, Peano.sub_one]
  change
      p.first.toPeano + Peano.zero * p.commonDifference.toPeano =
        p.first.toPeano
  rw [Peano.zero_mul, Peano.add_zero]

/-- The Peano embedding of `getElement` at an index equivalent to `one`. -/
theorem getElement_toPeano_of_equivalent_one (p : InfiniteArithmetic)
    (index : OrdinalNatural.Decimal)
    (h : index ≈ OrdinalNatural.Decimal.one) :
    (getElement p index).toPeano = p.first.toPeano :=
  toPeano_eq_of_equivalent (getElement_equivalent_first_of_equivalent_one p index h)

/-- `toPeano` converts each element: the Peano progression's element at
`index.toPeano` is the Peano embedding of the Decimal element at `index`. -/
theorem getElement_toPeano_eq_peano (p : InfiniteArithmetic)
    (index : OrdinalNatural.Decimal) :
    (getElement p index).toPeano =
      Peano.Progressions.InfiniteArithmetic.getElement (toPeano p)
        index.toPeano := by
  cases hι : index.toPeano with
  | one =>
    have heq : index ≈ OrdinalNatural.Decimal.one :=
      (OrdinalNatural.Decimal.toPeano_eq_one_iff_equivalent_one index).mp hι
    simp only [Peano.Progressions.InfiniteArithmetic.getElement, toPeano]
    exact getElement_toPeano_of_equivalent_one p index heq
  | successor n =>
    rw [getElement_toPeano, indexCoefficient_toPeano, hι,
      Peano.sub_one]
    rw [Peano.Progressions.InfiniteArithmetic.getElement_eq_add_mul]
    rfl

/-- Advancing one step from the predecessor index matches the closed form up to
Decimal equivalence. -/
theorem getElement_predecessor_add_commonDifference (p : InfiniteArithmetic)
    (index : OrdinalNatural.Decimal)
    (h : ¬ index ≈ OrdinalNatural.Decimal.one) :
    getElement p (index.predecessor h) + p.commonDifference ≈
      getElement p index := by
  apply equivalent_of_toPeano_eq
  rw [add_toPeano, getElement_toPeano, getElement_toPeano]
  have hsucc :=
    OrdinalNatural.Decimal.toPeano_eq_succ_predecessor_toPeano index h
  rw [indexCoefficient_toPeano, indexCoefficient_toPeano, hsucc]
  have hr :
      Peano.positive (index.predecessor h).toPeano.successor - Peano.one =
        Peano.positive (index.predecessor h).toPeano :=
    Peano.positive_succ_sub_one _
  rw [hr, Peano.add_assoc, Peano.sub_one_mul_add]

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

/-- Recover the first element of an infinite arithmetic progression from an
element at the given ordinal Decimal index and the common difference by
subtracting `(fromOrdinalPositive index - one) * commonDifference`. Integer
subtraction is total, so this always succeeds. -/
def tryFirstFromIndexedElement
    (index : OrdinalNatural.Decimal) (element commonDifference : Decimal) :
    Option Decimal :=
  some (element - indexCoefficient index * commonDifference)

/-- Given two ordered indexed elements (`index < index'`) of a prospective
infinite arithmetic progression, recover the common difference
`(element' - element) / (index' - index)`. Returns `none` when the element gap
is not divisible by the index gap. Unlike the natural-number versions, the
element difference may be negative or zero, so the recovered common difference
may be negative or zero as well. -/
def tryCommonDifferenceFromOrderedIndexedElements
    (index : OrdinalNatural.Decimal) (element : Decimal)
    (index' : OrdinalNatural.Decimal) (element' : Decimal)
    (hlt : index < index') :
    Option Decimal :=
  tryDivide (element' - element)
    (fromOrdinalPositive
      (OrdinalNatural.Decimal.subtract index' index hlt).toPeano)

/-- Reconstruct an infinite arithmetic progression from two of its elements at
different ordinal Decimal indexes. Returns `none` when the element gap is not
divisible by the index difference. Indexes are compared up to Decimal
equivalence. Zero and negative common differences are allowed. -/
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
  injection h with heq
  simp only [getElement]
  rw [← heq]
  exact sub_add_cancel element (indexCoefficient index * commonDifference)

/-- The Peano form of the arithmetic-progression step identity. -/
theorem getElement_toPeano_add_mul_of_lt (p : InfiniteArithmetic)
    (index index' : OrdinalNatural.Decimal)
    (hlt : index.toPeano < index'.toPeano) :
    (getElement p index').toPeano =
      (getElement p index).toPeano +
        (Peano.positive
          (OrdinalNatural.Peano.subtract index'.toPeano index.toPeano hlt)) *
          p.commonDifference.toPeano := by
  rw [getElement_toPeano_eq_peano, getElement_toPeano_eq_peano]
  simpa [toPeano] using
    Peano.Progressions.InfiniteArithmetic.getElement_add_mul_of_lt
      (toPeano p) index.toPeano index'.toPeano hlt

/-- Advancing from `index` to a larger `index'` adds
`(fromOrdinalPositive (index' - index)) * commonDifference` to the element, up
to Decimal equivalence. -/
theorem getElement_add_mul_of_lt (p : InfiniteArithmetic)
    (index index' : OrdinalNatural.Decimal)
    (hlt : index < index') :
    getElement p index' ≈
      getElement p index +
        (fromOrdinalPositive
          (OrdinalNatural.Decimal.subtract index' index hlt).toPeano) *
          p.commonDifference := by
  apply equivalent_of_toPeano_eq
  rw [add_toPeano, multiply_toPeano, toPeano_fromOrdinalPositive]
  obtain ⟨hlt_peano, hsub_peano⟩ :=
    OrdinalNatural.Decimal.subtract_toPeano index' index hlt
  have hpos :
      Peano.positive
          (OrdinalNatural.Decimal.subtract index' index hlt).toPeano =
        Peano.positive
          (OrdinalNatural.Peano.subtract index'.toPeano index.toPeano
            hlt_peano) :=
    congrArg Peano.positive hsub_peano
  rw [hpos]
  exact getElement_toPeano_add_mul_of_lt p index index' hlt_peano

/-- A successful common-difference recovery implies the larger element is
equivalent to the smaller plus the index gap times that difference. -/
theorem eq_add_mul_of_tryCommonDifferenceFromOrderedIndexedElements
    (index : OrdinalNatural.Decimal) (element : Decimal)
    (index' : OrdinalNatural.Decimal) (element' : Decimal)
    (hlt : index < index')
    (diff : Decimal)
    (h : tryCommonDifferenceFromOrderedIndexedElements
        index element index' element' hlt = some diff) :
    element' ≈
      element +
        (fromOrdinalPositive
          (OrdinalNatural.Decimal.subtract index' index hlt).toPeano) *
          diff := by
  simp only [tryCommonDifferenceFromOrderedIndexedElements] at h
  have hmul :
      (fromOrdinalPositive
          (OrdinalNatural.Decimal.subtract index' index hlt).toPeano) *
          diff ≈
        element' - element :=
    eq_of_tryDivide_mul h
  exact
    Setoid.trans
      (Setoid.symm (sub_add_cancel element' element))
      (Setoid.trans (add_commutative (element' - element) element)
        (equivalent_add_left (Setoid.symm hmul)))

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
    eq_add_mul_of_tryCommonDifferenceFromOrderedIndexedElements
      index element index' element' hlt diff hdiff
  exact
    Setoid.trans
      (Setoid.trans
        (getElement_add_mul_of_lt
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
  have heq := getElement_add_mul_of_lt p index index' hlt
  have hsub :
      getElement p index' - getElement p index ≈
        (fromOrdinalPositive
            (OrdinalNatural.Decimal.subtract index' index hlt).toPeano) *
          p.commonDifference := by
    apply equivalent_of_toPeano_eq
    rw [subtract_toPeano, toPeano_eq_of_equivalent heq, add_toPeano,
      multiply_toPeano, Peano.add_sub_cancel_left]
  have hgap_ne :
      ¬ fromOrdinalPositive
          (OrdinalNatural.Decimal.subtract index' index hlt).toPeano ≈ zero :=
    fromOrdinalPositive_not_equivalent_zero _
  exact Sequences.Progression.exists_of_option_rel_some
    (tryDivide_of_equivalent_mul hgap_ne hsub)

/-- Recovering the first element from an indexed element of an infinite
arithmetic progression, using a common difference equivalent to the
progression's, returns a value equivalent to that progression's first element. -/
theorem tryFirstFromIndexedElement_getElement_of_equivalent_diff
    (p : InfiniteArithmetic) (index : OrdinalNatural.Decimal) (d : Decimal)
    (hd : d ≈ p.commonDifference) :
    ∃ first,
      tryFirstFromIndexedElement index (getElement p index) d = some first ∧
      first ≈ p.first := by
  refine ⟨getElement p index - indexCoefficient index * d, rfl, ?_⟩
  apply equivalent_of_toPeano_eq
  rw [subtract_toPeano, getElement_toPeano, multiply_toPeano,
    toPeano_eq_of_equivalent hd, Peano.add_sub_cancel]

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

end ZeroMath.Numbers.Integer.Decimal.Progressions
