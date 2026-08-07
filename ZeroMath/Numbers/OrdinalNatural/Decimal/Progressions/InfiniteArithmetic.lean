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

/-- Two infinite arithmetic progressions are equivalent when their underlying
progressions yield related elements (Decimal setoid `≈`) at every positive
ordinal index. -/
def Equivalence (p q : InfiniteArithmetic) : Prop :=
  Sequences.Progression.Equivalence (toProgression p) (toProgression q)

instance : HasEquiv InfiniteArithmetic where
  Equiv := Equivalence

/-- `getElement` depends only on the first element and common difference. -/
theorem getElement_eq_of_same_params (p q : InfiniteArithmetic)
    (hfirst : p.first = q.first)
    (hdiff : p.commonDifference = q.commonDifference)
    (index : Decimal) :
    getElement p index = getElement q index := by
  simp only [getElement, hfirst, hdiff]

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
  have h1 := h Peano.one
  simp only [Sequences.Progression.tryGetElement, toProgression] at h1
  cases h1 with
  | some heq => exact heq

/-- Equivalence of infinite arithmetic progressions implies equivalence of their
common differences. -/
theorem commonDifference_equivalent_of_equivalence (p q : InfiniteArithmetic)
    (h : Equivalence p q) : p.commonDifference ≈ q.commonDifference := by
  have hfirst := first_equivalent_of_equivalence p q h
  have h2 := h Peano.one.successor
  simp only [Sequences.Progression.tryGetElement, toProgression] at h2
  cases h2 with
  | some hadd =>
    apply equivalent_of_toPeano_eq
    have hp := toPeano_eq_of_equivalent hadd
    rw [add_toPeano, add_toPeano, toPeano_eq_of_equivalent hfirst] at hp
    exact Peano.add_cancel_comm' hp

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

/-- Strict inequality is preserved when the left side is replaced by an
equivalent Decimal. -/
theorem lt_of_equivalent_of_lt {a b c : Decimal} (hab : a ≈ b) (hlt : b < c) :
    a < c := by
  apply lt_of_toCardinalPeano_lt
  rw [toCardinalPeano_eq_of_equivalent hab]
  exact toCardinalPeano_lt_of_lt hlt

/-- Strict inequality is preserved when the right side is replaced by an
equivalent Decimal. -/
theorem lt_of_lt_of_equivalent {a b c : Decimal} (hlt : a < b) (hbc : b ≈ c) :
    a < c := by
  apply lt_of_toCardinalPeano_lt
  rw [← toCardinalPeano_eq_of_equivalent hbc]
  exact toCardinalPeano_lt_of_lt hlt

/-- Multiplication respects Decimal equivalence in both arguments. -/
theorem equivalent_multiply {a b c d : Decimal} (hab : a ≈ b) (hcd : c ≈ d) :
    a * c ≈ b * d := by
  apply equivalent_of_toPeano_eq
  rw [multiplyToPeano, multiplyToPeano, toPeano_eq_of_equivalent hab,
    toPeano_eq_of_equivalent hcd]

/-- `trySubtract (x + d) d'` recovers a value equivalent to `x` when
`d ≈ d'`. -/
theorem trySubtract_add_right_of_equivalent (x d d' : Decimal) (hd : d ≈ d') :
    Option.Rel (· ≈ ·) (trySubtract (x + d) d') (some x) := by
  have hlt' : d' < x + d :=
    lt_of_equivalent_of_lt (Setoid.symm hd) (lt_add_right x d)
  have hsub_eq : subtract (x + d) d' hlt' ≈ x := by
    apply equivalent_of_toCardinalPeano_eq
    apply CardinalNatural.Peano.add_cancel_right
      (toCardinalPeano (subtract (x + d) d' hlt')) (toCardinalPeano x)
      (toCardinalPeano d')
    rw [toCardinalPeano_subtract, toCardinalPeano_add,
      toCardinalPeano_eq_of_equivalent hd,
      CardinalNatural.Peano.add_commutative (toCardinalPeano x)]
  have htry : trySubtract (x + d) d' = some (subtract (x + d) d' hlt') :=
    trySubtract_of_subtract ⟨hlt', rfl⟩
  rw [htry]
  exact Option.Rel.some hsub_eq

/-- When `y ≈ x + d`, `trySubtract y x` recovers a value equivalent to `d`. -/
theorem trySubtract_of_equivalent_add {x y d : Decimal} (h : y ≈ x + d) :
    Option.Rel (· ≈ ·) (trySubtract y x) (some d) := by
  have hlt_add : x < x + d := by
    rw [add_commutative]
    exact lt_add_right d x
  have hlt : x < y := lt_of_lt_of_equivalent hlt_add (Setoid.symm h)
  have hsub_eq : subtract y x hlt ≈ d := by
    apply equivalent_of_toCardinalPeano_eq
    apply CardinalNatural.Peano.add_cancel_right
      (toCardinalPeano (subtract y x hlt)) (toCardinalPeano d) (toCardinalPeano x)
    rw [toCardinalPeano_subtract, toCardinalPeano_eq_of_equivalent h,
      toCardinalPeano_add,
      CardinalNatural.Peano.add_commutative (toCardinalPeano d)]
  have htry : trySubtract y x = some (subtract y x hlt) :=
    trySubtract_of_subtract ⟨hlt, rfl⟩
  rw [htry]
  exact Option.Rel.some hsub_eq

/-- When `a ≈ b * q`, `tryDivide a b` recovers a value equivalent to `q`. -/
theorem tryDivide_of_equivalent_mul {a b q : Decimal} (h : a ≈ b * q) :
    Option.Rel (· ≈ ·) (tryDivide a b) (some q) := by
  let hdiv : Divisible a b := ⟨q, Setoid.symm h⟩
  have hquot : divide a b hdiv ≈ q := by
    have hcorrect := divide_correct a b hdiv
    apply equivalent_of_toPeano_eq
    have hp := toPeano_eq_of_equivalent hcorrect
    have hq := toPeano_eq_of_equivalent h
    rw [multiplyToPeano] at hp hq
    exact Peano.multiply_cancel_left b.toPeano _ _ (hp.trans hq)
  have htry : tryDivide a b = some (divide a b hdiv) :=
    tryDivide_of_divide ⟨hdiv, rfl⟩
  rw [htry]
  exact Option.Rel.some hquot

/-- The Peano embedding of `getElement` at a successor index. -/
theorem getElement_toPeano_of_toPeano_succ (p : InfiniteArithmetic)
    (index : Decimal) (n : Peano) (h : index.toPeano = n.successor) :
    (getElement p index).toPeano =
      p.first.toPeano + n * p.commonDifference.toPeano := by
  have hne : ¬ index ≈ one := by
    intro heq
    have hone := (toPeano_eq_one_iff_equivalent_one index).mpr heq
    rw [hone] at h
    cases h
  have hget := getElement_toPeano_of_not_equivalent_one p index hne
  have hsucc :
      index.toPeano = (index.predecessor hne).toPeano.successor := by
    rw [← successor_toPeano (index.predecessor hne)]
    exact congrArg toPeano (successor_predecessor index hne).symm
  have hn : (index.predecessor hne).toPeano = n := by
    injection hsucc.symm.trans h
  rw [hget, hn]

/-- Closed Peano form used by arithmetic-progression step identities. -/
def peanoClosedForm (first diff ι : Peano) : Peano :=
  match ι with
  | .one => first
  | .successor n => first + n * diff

/-- Pure Peano identity underlying the arithmetic-progression step. -/
theorem peano_match_add_mul_of_lt (first diff ι ι' : Peano) (hlt : ι < ι') :
    peanoClosedForm first diff ι' =
      peanoClosedForm first diff ι + (Peano.subtract ι' ι hlt) * diff := by
  cases ι with
  | one =>
    cases ι' with
    | one =>
      exact (Peano.not_lt_self Peano.one hlt).elim
    | successor n =>
      change first + n * diff =
        first + (Peano.subtract n.successor Peano.one hlt) * diff
      rw [Peano.subtract_succ_one n hlt]
  | successor m =>
    cases ι' with
    | one =>
      exact (Peano.not_lt_one m.successor hlt).elim
    | successor n =>
      have hlt' : m < n := Peano.lt_of_succ_lt_succ hlt
      have hsub :
          Peano.subtract n.successor m.successor hlt = Peano.subtract n m hlt' := by
        change Peano.subtract n m (Peano.lt_of_succ_lt_succ hlt) =
          Peano.subtract n m hlt'
        exact Peano.subtract_eq_of_eq _ _ rfl rfl
      change
        first + n * diff =
          first + m * diff + (Peano.subtract n.successor m.successor hlt) * diff
      rw [hsub]
      have hsum : m + Peano.subtract n m hlt' = n := by
        rw [Peano.add_comm]
        exact Peano.subtract_add_cancel n m hlt'
      calc
        first + n * diff
            = first + (m + Peano.subtract n m hlt') * diff := by rw [hsum]
        _ = first + (m * diff + (Peano.subtract n m hlt') * diff) := by
              rw [Peano.multiply_comm (m + Peano.subtract n m hlt'),
                Peano.multiply_add,
                Peano.multiply_comm diff m,
                Peano.multiply_comm diff (Peano.subtract n m hlt')]
        _ = first + m * diff + (Peano.subtract n m hlt') * diff := by
              rw [← Peano.add_assoc]

/-- Closed-form Peano embedding of `getElement` in terms of the index embedding. -/
theorem getElement_toPeano (p : InfiniteArithmetic) (index : Decimal) :
    (getElement p index).toPeano =
      peanoClosedForm p.first.toPeano p.commonDifference.toPeano index.toPeano := by
  cases hι : index.toPeano with
  | one =>
    exact getElement_toPeano_of_equivalent_one p index
      ((toPeano_eq_one_iff_equivalent_one index).mp hι)
  | successor n =>
    exact getElement_toPeano_of_toPeano_succ p index n hι

/-- Peano form of the arithmetic-progression step identity. -/
theorem getElement_toPeano_add_mul_of_lt (p : InfiniteArithmetic)
    (index index' : Decimal) (hlt : index.toPeano < index'.toPeano) :
    (getElement p index').toPeano =
      (getElement p index).toPeano +
        (Peano.subtract index'.toPeano index.toPeano hlt) *
          p.commonDifference.toPeano := by
  rw [getElement_toPeano, getElement_toPeano]
  exact peano_match_add_mul_of_lt p.first.toPeano p.commonDifference.toPeano
    index.toPeano index'.toPeano hlt

/-- Advancing from `index` to a larger `index'` adds
`(index' - index) * commonDifference` to the element, up to Decimal
equivalence. -/
theorem getElement_add_mul_of_lt (p : InfiniteArithmetic) (index index' : Decimal)
    (hlt : index < index') :
    getElement p index' ≈
      getElement p index +
        (subtract index' index hlt) * p.commonDifference := by
  apply equivalent_of_toPeano_eq
  rw [add_toPeano, multiplyToPeano]
  obtain ⟨hlt_peano, hsub_peano⟩ := subtract_toPeano index' index hlt
  rw [hsub_peano]
  exact getElement_toPeano_add_mul_of_lt p index index' hlt_peano

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
    (p : InfiniteArithmetic) (index index' : Decimal) (hlt : index < index') :
    ∃ d,
      tryCommonDifferenceFromOrderedIndexedElements
        index (getElement p index) index' (getElement p index') hlt = some d ∧
      d ≈ p.commonDifference := by
  have heq := getElement_add_mul_of_lt p index index' hlt
  obtain ⟨elementDiff, hsub_eq, hsub_approx⟩ :=
    exists_of_option_rel_some (trySubtract_of_equivalent_add heq)
  obtain ⟨d, hdiv_eq, hdiv_approx⟩ :=
    exists_of_option_rel_some (tryDivide_of_equivalent_mul hsub_approx)
  refine ⟨d, ?_, hdiv_approx⟩
  simp only [tryCommonDifferenceFromOrderedIndexedElements, hsub_eq, hdiv_eq]

/-- Recovering the first element from an indexed element of an infinite
arithmetic progression, using a common difference equivalent to the
progression's, returns a value equivalent to that progression's first element. -/
theorem tryFirstFromIndexedElement_getElement_of_equivalent_diff
    (p : InfiniteArithmetic) (index d : Decimal)
    (hd : d ≈ p.commonDifference) :
    ∃ first,
      tryFirstFromIndexedElement index (getElement p index) d = some first ∧
      first ≈ p.first := by
  if hone : index ≈ one then
    refine ⟨getElement p index, ?_, ?_⟩
    · simp only [tryFirstFromIndexedElement, hone, ↓reduceDIte]
    · simp only [getElement, hone, ↓reduceDIte]
      exact Setoid.refl _
  else
    have hget : getElement p index =
        p.first + (index.predecessor hone) * p.commonDifference := by
      simp only [getElement, hone, ↓reduceDIte]
    have hrel :=
      trySubtract_add_right_of_equivalent p.first
        ((index.predecessor hone) * p.commonDifference)
        ((index.predecessor hone) * d)
        (equivalent_multiply (Setoid.refl _) (Setoid.symm hd))
    obtain ⟨first, hsub_eq, hsub_approx⟩ := exists_of_option_rel_some hrel
    refine ⟨first, ?_, hsub_approx⟩
    simp only [tryFirstFromIndexedElement, hone, ↓reduceDIte, hget, hsub_eq]

/-- Recovering the first element from an indexed element of an infinite
arithmetic progression returns a value equivalent to that progression's first
element. -/
theorem tryFirstFromIndexedElement_getElement
    (p : InfiniteArithmetic) (index : Decimal) :
    ∃ first,
      tryFirstFromIndexedElement index (getElement p index) p.commonDifference =
        some first ∧
      first ≈ p.first :=
  tryFirstFromIndexedElement_getElement_of_equivalent_diff p index
    p.commonDifference (Setoid.refl _)

/-- Reconstructing from any two inequivalent indexed elements of an infinite
arithmetic progression recovers a progression equivalent to the original. -/
theorem tryFromTwoElements_getElement
    (p : InfiniteArithmetic) (index1 index2 : Decimal) (hne : ¬ index1 ≈ index2) :
    ∃ q,
      tryFromTwoElements
        index1 (getElement p index1) index2 (getElement p index2) hne = some q ∧
      q ≈ p := by
  cases hcomp : compare index1 index2 with
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

end ZeroMath.Numbers.OrdinalNatural.Decimal.Progressions
