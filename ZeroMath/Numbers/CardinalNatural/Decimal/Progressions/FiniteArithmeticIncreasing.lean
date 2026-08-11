import ZeroMath.Numbers.CardinalNatural.Decimal
import ZeroMath.Numbers.CardinalNatural.Decimal.Progressions.InfiniteArithmetic
import ZeroMath.Numbers.CardinalNatural.Peano.Progressions.FiniteArithmeticIncreasing
import ZeroMath.Sequences.List
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

/-- Length remaining from an element already known to lie in the progression,
given the room above that element up to the limit (`none` when the element
equals the limit). Computed with one division by the common difference instead
of comparing each successive term to the limit. -/
def lengthFromGap (diff : Decimal) (hdiff : ¬ diff ≈ zero) :
    Option Decimal → Decimal
  | none => one
  | some gap =>
    match divideWithRemainder gap diff hdiff with
    | (q, _) => q.successor

/-- The length of a finite increasing arithmetic progression: the number of
elements before `tryGetElement` first returns `none`. Uses a single comparison
of the first element to the limit and one division, avoiding a comparison at
every step of the progression. -/
def getLength (p : FiniteArithmeticIncreasing) : Decimal :=
  match p.first with
  | none => zero
  | some first =>
    match compare first p.limit with
    | .greater _ => zero
    | .equivalent _ => one
    | .less hlt =>
      lengthFromGap p.commonDifference p.commonDifference_ne_zero
        (some (subtract p.limit first (Or.inl hlt)))

/-- Convert a Decimal finite increasing arithmetic progression to the
corresponding Peano progression by embedding each field via `toPeano`. -/
def toPeano (p : FiniteArithmeticIncreasing) :
    Peano.Progressions.FiniteArithmeticIncreasing where
  first :=
    match p.first with
    | none => none
    | some x => some x.toPeano
  commonDifference := p.commonDifference.toPeano
  limit := p.limit.toPeano
  commonDifference_ne_zero :=
    toPeano_ne_zero_of_not_equivalent_zero p.commonDifference_ne_zero

/-- Decimal `≤` is reflected and reflected by the Peano embedding. -/
theorem le_iff_toPeano_le (a b : Decimal) : a ≤ b ↔ a.toPeano ≤ b.toPeano :=
  ⟨toPeano_le_of_le, le_of_toPeano_le⟩

/-- `lengthFromGap` agrees with the Peano `lengthFromGap` on embeddings. -/
theorem lengthFromGap_toPeano (diff : Decimal) (hdiff : ¬ diff ≈ zero)
    (gap : Option Decimal) :
    (lengthFromGap diff hdiff gap).toPeano =
      Peano.Progressions.FiniteArithmeticIncreasing.lengthFromGap
        diff.toPeano (toPeano_ne_zero_of_not_equivalent_zero hdiff)
        (gap.map Decimal.toPeano) := by
  match gap with
  | none =>
    simp only [lengthFromGap, Option.map, toPeano_one,
      Peano.Progressions.FiniteArithmeticIncreasing.lengthFromGap]
  | some g =>
    match hdiv : divideWithRemainder g diff hdiff with
    | (q, r) =>
      obtain ⟨hdiff', hpeano⟩ := divideWithRemainder_toPeano g diff hdiff hdiv
      simp only [lengthFromGap, hdiv, Option.map,
        Peano.Progressions.FiniteArithmeticIncreasing.lengthFromGap]
      rw [show toPeano_ne_zero_of_not_equivalent_zero hdiff = hdiff' from rfl,
        hpeano, successor_toPeano]

/-- `getLength` agrees with Peano `getLength` on the embedded progression. -/
theorem getLength_toPeano (p : FiniteArithmeticIncreasing) :
    (getLength p).toPeano =
      Peano.Progressions.FiniteArithmeticIncreasing.getLength (toPeano p) := by
  cases hf : p.first with
  | none =>
    simp only [getLength, hf, toPeano,
      Peano.Progressions.FiniteArithmeticIncreasing.getLength, toPeano_zero]
  | some first =>
    have hto : toPeano p =
        {
          first := some first.toPeano
          commonDifference := p.commonDifference.toPeano
          limit := p.limit.toPeano
          commonDifference_ne_zero :=
            toPeano_ne_zero_of_not_equivalent_zero p.commonDifference_ne_zero
        } := by
      simp only [toPeano, hf]
    rw [hto]
    unfold getLength Peano.Progressions.FiniteArithmeticIncreasing.getLength
    simp only [hf]
    cases hcmp : Peano.compare first.toPeano p.limit.toPeano with
    | less hlt =>
      have hdec : compare first p.limit = .less hlt := by
        simp only [compare, hcmp]
      simp only [hdec]
      obtain ⟨_, hsub_eq⟩ := subtract_toPeano p.limit first (Or.inl hlt)
      have hlen :=
        lengthFromGap_toPeano p.commonDifference p.commonDifference_ne_zero
          (some (subtract p.limit first (Or.inl hlt)))
      simpa [Option.map, hsub_eq] using hlen
    | equal heq =>
      have hdec : compare first p.limit =
          .equivalent (equivalent_of_toPeano_eq heq) := by
        simp only [compare, hcmp]
      simp only [hdec, toPeano_one]
    | greater hgt =>
      have hdec : compare first p.limit = .greater hgt := by
        simp only [compare, hcmp]
      simp only [hdec, toPeano_zero]

/-- Advancing one step of `toProgression` commutes with `toPeano`. -/
theorem next_toPeano (p : FiniteArithmeticIncreasing) (x : Decimal) :
    Option.map Decimal.toPeano ((toProgression p).next x) =
      (Peano.Progressions.FiniteArithmeticIncreasing.toProgression
        (toPeano p)).next x.toPeano := by
  change Option.map Decimal.toPeano
      (if x + p.commonDifference ≤ p.limit then
        some (x + p.commonDifference) else none) =
    (if x.toPeano + p.commonDifference.toPeano ≤ p.limit.toPeano then
      some (x.toPeano + p.commonDifference.toPeano) else none)
  have hiff := le_iff_toPeano_le (x + p.commonDifference) p.limit
  have hadd : (x + p.commonDifference).toPeano =
      x.toPeano + p.commonDifference.toPeano := add_toPeano x p.commonDifference
  by_cases hle : x + p.commonDifference ≤ p.limit
  · have hle' : x.toPeano + p.commonDifference.toPeano ≤ p.limit.toPeano := by
      rw [← hadd]
      exact hiff.mp hle
    simp only [hle, hle', ↓reduceIte, Option.map, hadd]
  · have hle' : ¬ x.toPeano + p.commonDifference.toPeano ≤ p.limit.toPeano := by
      intro h
      apply hle
      exact hiff.mpr (by rwa [hadd])
    simp only [hle, hle', ↓reduceIte, Option.map]

/-- The first element of `toProgression` commutes with `toPeano`. -/
theorem first_toPeano (p : FiniteArithmeticIncreasing) :
    Option.map Decimal.toPeano (toProgression p).first =
      (Peano.Progressions.FiniteArithmeticIncreasing.toProgression
        (toPeano p)).first := by
  cases hf : p.first with
  | none =>
    simp only [toProgression, hf, toPeano,
      Peano.Progressions.FiniteArithmeticIncreasing.toProgression, Option.map]
  | some x =>
    have hprog :
        (toProgression p).first = if x ≤ p.limit then some x else none := by
      simp only [toProgression, hf]
    have hprog' :
        (Peano.Progressions.FiniteArithmeticIncreasing.toProgression
          (toPeano p)).first =
          if x.toPeano ≤ p.limit.toPeano then some x.toPeano else none := by
      simp only [toPeano, hf,
        Peano.Progressions.FiniteArithmeticIncreasing.toProgression]
    rw [hprog, hprog']
    have hiff := le_iff_toPeano_le x p.limit
    by_cases hle : x ≤ p.limit
    · simp only [hle, hiff.mp hle, ↓reduceIte, Option.map]
    · have hle' : ¬ x.toPeano ≤ p.limit.toPeano := fun h => hle (hiff.mpr h)
      simp only [hle, hle', ↓reduceIte, Option.map]

/-- Accessibility is preserved by embedding the current state via `toPeano`. -/
theorem acc_map_toPeano (p : FiniteArithmeticIncreasing) (current : Option Decimal)
    (hAcc : Acc (Sequences.Progression.OptionStep (toProgression p).next) current) :
    Acc (Sequences.Progression.OptionStep
      (Peano.Progressions.FiniteArithmeticIncreasing.toProgression
        (toPeano p)).next)
      (current.map Decimal.toPeano) := by
  refine Acc.rec
    (motive := fun current _ =>
      Acc (Sequences.Progression.OptionStep
        (Peano.Progressions.FiniteArithmeticIncreasing.toProgression
          (toPeano p)).next)
        (current.map Decimal.toPeano))
    (fun current hcurr ih => by
      match current with
      | none =>
        exact Sequences.Progression.acc_none _
      | some x =>
        have hnext := next_toPeano p x
        have hAcc_next := ih ((toProgression p).next x)
          (Sequences.Progression.OptionStep.step x)
        have hAcc_next' :
            Acc (Sequences.Progression.OptionStep
              (Peano.Progressions.FiniteArithmeticIncreasing.toProgression
                (toPeano p)).next)
              ((Peano.Progressions.FiniteArithmeticIncreasing.toProgression
                (toPeano p)).next x.toPeano) :=
          hnext ▸ hAcc_next
        exact Sequences.Progression.acc_step hAcc_next')
    hAcc

/-- Walking length from an accessible Decimal state equals the Peano walk from
its embedding. -/
theorem getLengthFrom_toPeano (p : FiniteArithmeticIncreasing)
    (current : Option Decimal)
    (hAcc : Acc (Sequences.Progression.OptionStep (toProgression p).next) current) :
    Sequences.Progression.getLengthFrom (toProgression p).next current hAcc =
      Sequences.Progression.getLengthFrom
        (Peano.Progressions.FiniteArithmeticIncreasing.toProgression
          (toPeano p)).next
        (current.map Decimal.toPeano)
        (acc_map_toPeano p current hAcc) := by
  refine Acc.rec
    (motive := fun current hAcc =>
      Sequences.Progression.getLengthFrom (toProgression p).next current hAcc =
        Sequences.Progression.getLengthFrom
          (Peano.Progressions.FiniteArithmeticIncreasing.toProgression
            (toPeano p)).next
          (current.map Decimal.toPeano)
          (acc_map_toPeano p current hAcc))
    (fun current hcurr ih => by
      match current with
      | none =>
        exact
          (Sequences.Progression.getLengthFrom_none _ (Acc.intro _ hcurr)).trans
            (Sequences.Progression.getLengthFrom_none _ _).symm
      | some x =>
        have hAccx :
            Acc (Sequences.Progression.OptionStep (toProgression p).next)
              (some x) := Acc.intro _ hcurr
        rw [Sequences.Progression.getLengthFrom_some (toProgression p).next x hAccx]
        have hmap : Option.map Decimal.toPeano (some x) = some x.toPeano := rfl
        have hAcc_map := acc_map_toPeano p (some x) hAccx
        rw [Sequences.Progression.getLengthFrom_eq_of_current_eq _ hmap hAcc_map]
        rw [Sequences.Progression.getLengthFrom_some
          (Peano.Progressions.FiniteArithmeticIncreasing.toProgression
            (toPeano p)).next
          x.toPeano (hmap ▸ hAcc_map)]
        have hnext := next_toPeano p x
        have ih' := ih ((toProgression p).next x)
          (Sequences.Progression.OptionStep.step x)
        refine congrArg Peano.successor (ih'.trans ?_)
        exact
          (Sequences.Progression.getLengthFrom_eq_of_current_eq _
            hnext
            (acc_map_toPeano p ((toProgression p).next x)
              (hAccx.inv (Sequences.Progression.OptionStep.step x)))).trans
            (Sequences.Progression.getLengthFrom_eq_of_acc_eq _ _ _ _))
    hAcc

/-- `Progression.getLength` of a Decimal finite arithmetic progression equals
that of its Peano embedding. -/
theorem progression_getLength_toPeano (p : FiniteArithmeticIncreasing) :
    Sequences.Progression.getLength (toProgression p) (toProgression_finite p) =
      Sequences.Progression.getLength
        (Peano.Progressions.FiniteArithmeticIncreasing.toProgression (toPeano p))
        (Peano.Progressions.FiniteArithmeticIncreasing.toProgression_finite
          (toPeano p)) := by
  simp only [Sequences.Progression.getLength]
  have hwalk :=
    getLengthFrom_toPeano p (toProgression p).first
      (Sequences.Progression.acc_first_of_finite (toProgression p)
        (toProgression_finite p))
  have hfirst := first_toPeano p
  refine hwalk.trans ?_
  exact
    (Sequences.Progression.getLengthFrom_eq_of_current_eq _
      hfirst
      (acc_map_toPeano p (toProgression p).first
        (Sequences.Progression.acc_first_of_finite (toProgression p)
          (toProgression_finite p)))).trans
      (Sequences.Progression.getLengthFrom_eq_of_acc_eq _ _ _ _)

/-- `getLength` agrees with walking `toProgression` via `Progression.getLength`. -/
theorem getLength_eq (p : FiniteArithmeticIncreasing) :
    getLength p ≈
      fromPeano
        (Sequences.Progression.getLength (toProgression p)
          (toProgression_finite p)) := by
  apply equivalent_of_toPeano_eq
  rw [toPeano_fromPeano, getLength_toPeano,
    Peano.Progressions.FiniteArithmeticIncreasing.getLength_eq (toPeano p),
    progression_getLength_toPeano]

/-- Element at a positive ordinal index starting from a known first value, using
the closed form with no limit comparisons. Always
`first + (fromOrdinal index - one) * commonDifference`. -/
def getElementFrom (first commonDifference : Decimal)
    (index : OrdinalNatural.Decimal) : Decimal :=
  first +
    (subtract (fromOrdinal index) one (one_le_fromOrdinal index)) *
      commonDifference

/-- Closed-form `getElementFrom` matches `InfiniteArithmetic.getElement`. -/
theorem getElementFrom_eq_InfiniteArithmetic_getElement
    (first commonDifference : Decimal) (index : OrdinalNatural.Decimal) :
    getElementFrom first commonDifference index =
      InfiniteArithmetic.getElement
        { first := first, commonDifference := commonDifference } index :=
  rfl

/-- If there is no first element, the length is zero. -/
theorem getLength_eq_zero_of_first_none (p : FiniteArithmeticIncreasing)
    (h : p.first = none) :
    getLength p = zero := by
  simp only [getLength, h]

/-- If the first element is greater than the limit, the length is zero. -/
theorem getLength_eq_zero_of_first_gt_limit (p : FiniteArithmeticIncreasing)
    (first : Decimal) (hf : p.first = some first) (hgt : p.limit < first) :
    getLength p = zero := by
  unfold getLength
  simp only [hf]
  match hcmp : compare first p.limit with
  | .less hlt =>
    exact (not_lt_of_lt hgt hlt).elim
  | .equivalent heq =>
    have hself : p.limit.toPeano < p.limit.toPeano := by
      have hlt : p.limit.toPeano < first.toPeano := hgt
      rwa [toPeano_eq_of_equivalent heq] at hlt
    exact (Peano.not_lt_self _ hself).elim
  | .greater _ =>
    rfl

/-- The length bound is impossible when there is no first element. -/
theorem not_fromOrdinal_le_getLength_of_first_none
    (p : FiniteArithmeticIncreasing) (index : OrdinalNatural.Decimal)
    (hle : fromOrdinal index ≤ getLength p)
    (h : p.first = none) : False := by
  have hle' : fromOrdinal index ≤ zero :=
    (getLength_eq_zero_of_first_none p h) ▸ hle
  exact fromOrdinal_not_equivalent_zero index (eq_zero_of_le_zero _ hle')

/-- The length bound is impossible when the first element exceeds the limit. -/
theorem not_fromOrdinal_le_getLength_of_first_gt_limit
    (p : FiniteArithmeticIncreasing) (index : OrdinalNatural.Decimal)
    (first : Decimal)
    (hle : fromOrdinal index ≤ getLength p)
    (hf : p.first = some first) (hgt : p.limit < first) : False := by
  have hle' : fromOrdinal index ≤ zero :=
    (getLength_eq_zero_of_first_gt_limit p first hf hgt) ▸ hle
  exact fromOrdinal_not_equivalent_zero index (eq_zero_of_le_zero _ hle')

/-- The element at the given positive ordinal index, when that index does not
exceed the progression's length. The first element has index equivalent to
`one`. Uses a single `compare` of the first element to the limit (as in
`getLength`), then the closed form of the arithmetic progression — avoiding
`toProgression` and a limit comparison at every step. -/
def getElement (p : FiniteArithmeticIncreasing) (index : OrdinalNatural.Decimal)
    (hle : fromOrdinal index ≤ getLength p) : Decimal :=
  match hf : p.first with
  | none =>
    (not_fromOrdinal_le_getLength_of_first_none p index hle hf).elim
  | some first =>
    match compare first p.limit with
    | .greater hgt =>
      (not_fromOrdinal_le_getLength_of_first_gt_limit p index first hle hf
        hgt).elim
    | .equivalent _ =>
      getElementFrom first p.commonDifference index
    | .less _ =>
      getElementFrom first p.commonDifference index

/-- A Decimal length bound on `fromOrdinal index` yields the corresponding Peano
bound for walking `toProgression`. -/
theorem fromOrdinal_le_progression_getLength
    (p : FiniteArithmeticIncreasing) (index : OrdinalNatural.Decimal)
    (hle : fromOrdinal index ≤ getLength p) :
    Peano.fromOrdinal index.toPeano ≤
      Sequences.Progression.getLength (toProgression p)
        (toProgression_finite p) := by
  have hle' :
      fromOrdinal index ≤
        fromPeano
          (Sequences.Progression.getLength (toProgression p)
            (toProgression_finite p)) :=
    le_trans hle (Or.inr (getLength_eq p))
  have hpeano := toPeano_le_of_le hle'
  rw [fromOrdinal_toPeano_eq_fromOrdinal_peano, toPeano_fromPeano] at hpeano
  exact hpeano

/-- When the first element does not exceed the limit, `toProgression.first` is
that element. -/
theorem toProgression_first_eq_some_of_le (p : FiniteArithmeticIncreasing)
    (start : Decimal) (hf : p.first = some start) (hle : start ≤ p.limit) :
    (toProgression p).first = some start := by
  simp only [toProgression, hf, hle, ↓reduceIte]

/-- When `tryGetElement` succeeds from a known first element, the value is
equivalent to the closed-form `getElementFrom` at the Decimal index. -/
theorem eq_getElementFrom_of_tryGetElement_eq_some
    (p : FiniteArithmeticIncreasing) (start : Decimal)
    (hf : (toProgression p).first = some start)
    (index : OrdinalNatural.Decimal) (x : Decimal)
    (h : Sequences.Progression.tryGetElement index.toPeano (toProgression p) =
      some x) :
    x ≈ getElementFrom start p.commonDifference index := by
  if hone : index ≈ OrdinalNatural.Decimal.one then
    have hpeano : index.toPeano = OrdinalNatural.Peano.one :=
      (OrdinalNatural.Decimal.toPeano_eq_one_iff_equivalent_one index).mpr hone
    rw [hpeano, Sequences.Progression.tryGetElement, hf] at h
    injection h with heq
    rw [← heq, getElementFrom_eq_InfiniteArithmetic_getElement]
    exact Setoid.symm
      (InfiniteArithmetic.getElement_equivalent_first_of_equivalent_one
        { first := start, commonDifference := p.commonDifference } index hone)
  else
    have hpeano :=
      OrdinalNatural.Decimal.toPeano_eq_succ_predecessor_toPeano index hone
    rw [hpeano, Sequences.Progression.tryGetElement] at h
    match htry : Sequences.Progression.tryGetElement
        (index.predecessor hone).toPeano (toProgression p) with
    | none =>
      rw [htry] at h
      nomatch h
    | some y =>
      rw [htry] at h
      have hy :=
        eq_getElementFrom_of_tryGetElement_eq_some p start hf
          (index.predecessor hone) y htry
      have hnext : (toProgression p).next y = some x := h
      have hprog :
          (toProgression p).next y =
            if y + p.commonDifference ≤ p.limit then
              some (y + p.commonDifference)
            else
              none :=
        rfl
      rw [hprog] at hnext
      by_cases hle_add : y + p.commonDifference ≤ p.limit
      · simp only [hle_add, ↓reduceIte] at hnext
        injection hnext with heq
        have hadd :
            y + p.commonDifference ≈
              getElementFrom start p.commonDifference
                (index.predecessor hone) + p.commonDifference :=
          equivalent_add_right hy
        have hclosed :
            getElementFrom start p.commonDifference
                (index.predecessor hone) + p.commonDifference ≈
              getElementFrom start p.commonDifference index := by
          rw [getElementFrom_eq_InfiniteArithmetic_getElement,
            getElementFrom_eq_InfiniteArithmetic_getElement]
          exact InfiniteArithmetic.getElement_predecessor_add_commonDifference
            { first := start, commonDifference := p.commonDifference }
            index hone
        exact heq ▸ Setoid.trans hadd hclosed
      · simp only [hle_add, ↓reduceIte] at hnext
        nomatch hnext
termination_by index.toPeano
decreasing_by
  obtain ⟨hne, heq⟩ := OrdinalNatural.Decimal.predecessor_toPeano index hone
  simp only [heq]
  exact OrdinalNatural.Peano.sizeOf_predecessor_lt _ hne

/-- `getElement` agrees with walking `toProgression` via `Progression.getElement`
up to Decimal equivalence. -/
theorem getElement_eq (p : FiniteArithmeticIncreasing)
    (index : OrdinalNatural.Decimal)
    (hle : fromOrdinal index ≤ getLength p) :
    getElement p index hle ≈
      Sequences.Progression.getElement (toProgression p) (toProgression_finite p)
        index.toPeano (fromOrdinal_le_progression_getLength p index hle) := by
  have hle_peano := fromOrdinal_le_progression_getLength p index hle
  have htry :=
    Sequences.Progression.tryGetElement_eq_some_getElement
      (toProgression p) (toProgression_finite p) index.toPeano hle_peano
  dsimp only [getElement]
  split
  · next hf =>
    exact (not_fromOrdinal_le_getLength_of_first_none p index hle hf).elim
  · next start hf =>
    cases hcmp : compare start p.limit with
    | greater hgt =>
      exact (not_fromOrdinal_le_getLength_of_first_gt_limit p index start hle hf
        hgt).elim
    | equivalent heq =>
      have hle_start : start ≤ p.limit := Or.inr heq
      have hfirst := toProgression_first_eq_some_of_le p start hf hle_start
      exact Setoid.symm
        (eq_getElementFrom_of_tryGetElement_eq_some p start hfirst index _
          htry)
    | less hlt =>
      have hle_start : start ≤ p.limit := Or.inl hlt
      have hfirst := toProgression_first_eq_some_of_le p start hf hle_start
      exact Setoid.symm
        (eq_getElementFrom_of_tryGetElement_eq_some p start hfirst index _
          htry)

/-- Two finite increasing arithmetic progressions are equivalent when their
underlying progressions yield related elements (Decimal setoid `≈`) at every
positive ordinal index. -/
def Equivalence (p q : FiniteArithmeticIncreasing) : Prop :=
  Sequences.Progression.Equivalence (toProgression p) (toProgression q)

instance : HasEquiv FiniteArithmeticIncreasing where
  Equiv := Equivalence

/-- The optional first element after applying the limit filter, without building
a `Progression`. -/
def effectiveFirst (p : FiniteArithmeticIncreasing) : Option Decimal :=
  match p.first with
  | none => none
  | some x => if x ≤ p.limit then some x else none

theorem effectiveFirst_eq (p : FiniteArithmeticIncreasing) :
    effectiveFirst p = (toProgression p).first :=
  rfl

/-- `effectiveFirst` commutes with the Peano embedding. -/
theorem effectiveFirst_toPeano (p : FiniteArithmeticIncreasing) :
    Option.map Decimal.toPeano (effectiveFirst p) =
      Peano.Progressions.FiniteArithmeticIncreasing.effectiveFirst (toPeano p) := by
  rw [effectiveFirst_eq, Peano.Progressions.FiniteArithmeticIncreasing.effectiveFirst_eq]
  exact first_toPeano p

/-- `tryGetElement` commutes with the Peano embedding. -/
theorem tryGetElement_toPeano (p : FiniteArithmeticIncreasing)
    (index : OrdinalNatural.Peano) :
    Option.map Decimal.toPeano
      (Sequences.Progression.tryGetElement index (toProgression p)) =
    Sequences.Progression.tryGetElement index
      (Peano.Progressions.FiniteArithmeticIncreasing.toProgression (toPeano p)) := by
  induction index with
  | one =>
    exact first_toPeano p
  | successor n ih =>
    simp only [Sequences.Progression.tryGetElement]
    cases hp : Sequences.Progression.tryGetElement n (toProgression p) with
    | none =>
      have ih' :
          Sequences.Progression.tryGetElement n
            (Peano.Progressions.FiniteArithmeticIncreasing.toProgression
              (toPeano p)) = none := by
        simpa [hp, Option.map] using ih.symm
      simp only [ih']
      rfl
    | some x =>
      have ih' :
          Sequences.Progression.tryGetElement n
            (Peano.Progressions.FiniteArithmeticIncreasing.toProgression
              (toPeano p)) = some x.toPeano := by
        simpa [hp, Option.map] using ih.symm
      simp only [ih']
      exact next_toPeano p x

/-- Decimal progression equivalence matches Peano equivalence of the embeddings. -/
theorem equivalence_iff_toPeano (p q : FiniteArithmeticIncreasing) :
    Equivalence p q ↔
      Peano.Progressions.FiniteArithmeticIncreasing.Equivalence
        (toPeano p) (toPeano q) := by
  constructor
  · intro h index
    have hp := tryGetElement_toPeano p index
    have hq := tryGetElement_toPeano q index
    have hrel := h index
    match hdp : Sequences.Progression.tryGetElement index (toProgression p),
        hdq : Sequences.Progression.tryGetElement index (toProgression q), hrel with
    | none, none, Option.Rel.none =>
      have hpp :
          Sequences.Progression.tryGetElement index
            (Peano.Progressions.FiniteArithmeticIncreasing.toProgression
              (toPeano p)) = none := by
        simpa [hdp, Option.map] using hp.symm
      have hqq :
          Sequences.Progression.tryGetElement index
            (Peano.Progressions.FiniteArithmeticIncreasing.toProgression
              (toPeano q)) = none := by
        simpa [hdq, Option.map] using hq.symm
      simp only [hpp, hqq]
      exact Option.Rel.none
    | some x, some y, Option.Rel.some heq =>
      have hpp :
          Sequences.Progression.tryGetElement index
            (Peano.Progressions.FiniteArithmeticIncreasing.toProgression
              (toPeano p)) = some x.toPeano := by
        simpa [hdp, Option.map] using hp.symm
      have hqq :
          Sequences.Progression.tryGetElement index
            (Peano.Progressions.FiniteArithmeticIncreasing.toProgression
              (toPeano q)) = some y.toPeano := by
        simpa [hdq, Option.map] using hq.symm
      simp only [hpp, hqq]
      exact Option.Rel.some (toPeano_eq_of_equivalent heq)
    | none, some _, hbad =>
      cases hbad
    | some _, none, hbad =>
      cases hbad
  · intro h index
    have hp := tryGetElement_toPeano p index
    have hq := tryGetElement_toPeano q index
    have hrel := h index
    match hdp : Sequences.Progression.tryGetElement index (toProgression p) with
    | none =>
      have hpp :
          Sequences.Progression.tryGetElement index
            (Peano.Progressions.FiniteArithmeticIncreasing.toProgression
              (toPeano p)) = none := by
        simpa [hdp, Option.map] using hp.symm
      match hdq : Sequences.Progression.tryGetElement index (toProgression q) with
      | none =>
        exact Option.Rel.none
      | some y =>
        have hqq :
            Sequences.Progression.tryGetElement index
              (Peano.Progressions.FiniteArithmeticIncreasing.toProgression
                (toPeano q)) = some y.toPeano := by
          simpa [hdq, Option.map] using hq.symm
        simp only [hpp, hqq] at hrel
        cases hrel
    | some x =>
      have hpp :
          Sequences.Progression.tryGetElement index
            (Peano.Progressions.FiniteArithmeticIncreasing.toProgression
              (toPeano p)) = some x.toPeano := by
        simpa [hdp, Option.map] using hp.symm
      match hdq : Sequences.Progression.tryGetElement index (toProgression q) with
      | none =>
        have hqq :
            Sequences.Progression.tryGetElement index
              (Peano.Progressions.FiniteArithmeticIncreasing.toProgression
                (toPeano q)) = none := by
          simpa [hdq, Option.map] using hq.symm
        simp only [hpp, hqq] at hrel
        cases hrel
      | some y =>
        have hqq :
            Sequences.Progression.tryGetElement index
              (Peano.Progressions.FiniteArithmeticIncreasing.toProgression
                (toPeano q)) = some y.toPeano := by
          simpa [hdq, Option.map] using hq.symm
        simp only [hpp, hqq] at hrel
        cases hrel with
        | some heq =>
          exact Option.Rel.some (equivalent_of_toPeano_eq heq)

theorem getLength_eq_zero_iff_effectiveFirst_none (p : FiniteArithmeticIncreasing) :
    getLength p ≈ zero ↔ effectiveFirst p = none := by
  constructor
  · intro hlen
    have hpeano :
        Peano.Progressions.FiniteArithmeticIncreasing.getLength (toPeano p) =
          Peano.zero := by
      rw [← getLength_toPeano]
      exact (toPeano_eq_of_equivalent hlen).trans toPeano_zero
    have hf :=
      (Peano.Progressions.FiniteArithmeticIncreasing.getLength_eq_zero_iff_effectiveFirst_none
        (toPeano p)).mp hpeano
    have hmap := effectiveFirst_toPeano p
    simp only [hf, Option.map] at hmap
    match heff : effectiveFirst p with
    | none =>
      rfl
    | some _ =>
      simp only [heff] at hmap
      nomatch hmap
  · intro hfirst
    match hf : p.first with
    | none =>
      simp only [getLength, hf]
      exact Setoid.refl _
    | some first =>
      simp only [effectiveFirst, hf] at hfirst
      by_cases hle : first ≤ p.limit
      · simp only [hle, ↓reduceIte] at hfirst
        nomatch hfirst
      · simp only [getLength, hf]
        match hc : compare first p.limit with
        | .greater _ =>
          exact Setoid.refl _
        | .equivalent heq =>
          exact (hle (Or.inr heq)).elim
        | .less hlt =>
          exact (hle (Or.inl hlt)).elim

theorem effectiveFirst_eq_some_of_pos_length (p : FiniteArithmeticIncreasing)
    (h : ¬ getLength p ≈ zero) :
    ∃ first, effectiveFirst p = some first := by
  cases hf : effectiveFirst p with
  | none =>
    exact False.elim (h ((getLength_eq_zero_iff_effectiveFirst_none p).mpr hf))
  | some first =>
    exact ⟨first, rfl⟩

/-- Empty progressions (length zero) are equivalent. -/
theorem equivalence_of_length_zero (p q : FiniteArithmeticIncreasing)
    (hp : getLength p ≈ zero) (hq : getLength q ≈ zero) :
    Equivalence p q := by
  have hp' :
      Peano.Progressions.FiniteArithmeticIncreasing.getLength (toPeano p) =
        Peano.zero := by
    rw [← getLength_toPeano]
    exact (toPeano_eq_of_equivalent hp).trans toPeano_zero
  have hq' :
      Peano.Progressions.FiniteArithmeticIncreasing.getLength (toPeano q) =
        Peano.zero := by
    rw [← getLength_toPeano]
    exact (toPeano_eq_of_equivalent hq).trans toPeano_zero
  exact (equivalence_iff_toPeano p q).mpr
    (Peano.Progressions.FiniteArithmeticIncreasing.equivalence_of_length_zero
      (toPeano p) (toPeano q) hp' hq')

/-- Length-one progressions with equivalent first elements are equivalent. -/
theorem equivalence_of_length_one (p q : FiniteArithmeticIncreasing)
    (firstP firstQ : Decimal)
    (hp : effectiveFirst p = some firstP) (hq : effectiveFirst q = some firstQ)
    (hfirst : firstP ≈ firstQ)
    (hlenP : getLength p ≈ one) (hlenQ : getLength q ≈ one) :
    Equivalence p q := by
  have hfirstPeano : firstP.toPeano = firstQ.toPeano :=
    toPeano_eq_of_equivalent hfirst
  have hp' :
      Peano.Progressions.FiniteArithmeticIncreasing.effectiveFirst (toPeano p) =
        some firstP.toPeano := by
    simpa [hp, Option.map] using (effectiveFirst_toPeano p).symm
  have hq' :
      Peano.Progressions.FiniteArithmeticIncreasing.effectiveFirst (toPeano q) =
        some firstP.toPeano := by
    have hq0 :
        Peano.Progressions.FiniteArithmeticIncreasing.effectiveFirst (toPeano q) =
          some firstQ.toPeano := by
      simpa [hq, Option.map] using (effectiveFirst_toPeano q).symm
    exact hq0.trans (congrArg some hfirstPeano.symm)
  have hlenP' :
      Peano.Progressions.FiniteArithmeticIncreasing.getLength (toPeano p) =
        Peano.one := by
    rw [← getLength_toPeano]
    exact (toPeano_eq_of_equivalent hlenP).trans toPeano_one
  have hlenQ' :
      Peano.Progressions.FiniteArithmeticIncreasing.getLength (toPeano q) =
        Peano.one := by
    rw [← getLength_toPeano]
    exact (toPeano_eq_of_equivalent hlenQ).trans toPeano_one
  exact (equivalence_iff_toPeano p q).mpr
    (Peano.Progressions.FiniteArithmeticIncreasing.equivalence_of_length_one
      (toPeano p) (toPeano q) firstP.toPeano hp' hq' hlenP' hlenQ')

/-- Progressions with equivalent first elements and common differences and
equivalent lengths are equivalent. -/
theorem equivalence_of_equivalent_params (p q : FiniteArithmeticIncreasing)
    (firstP firstQ : Decimal)
    (hp : effectiveFirst p = some firstP) (hq : effectiveFirst q = some firstQ)
    (hfirst : firstP ≈ firstQ)
    (hdiff : p.commonDifference ≈ q.commonDifference)
    (hlen : getLength p ≈ getLength q) :
    Equivalence p q := by
  have hfirstPeano : firstP.toPeano = firstQ.toPeano :=
    toPeano_eq_of_equivalent hfirst
  have hp' :
      Peano.Progressions.FiniteArithmeticIncreasing.effectiveFirst (toPeano p) =
        some firstP.toPeano := by
    simpa [hp, Option.map] using (effectiveFirst_toPeano p).symm
  have hq' :
      Peano.Progressions.FiniteArithmeticIncreasing.effectiveFirst (toPeano q) =
        some firstP.toPeano := by
    have hq0 :
        Peano.Progressions.FiniteArithmeticIncreasing.effectiveFirst (toPeano q) =
          some firstQ.toPeano := by
      simpa [hq, Option.map] using (effectiveFirst_toPeano q).symm
    exact hq0.trans (congrArg some hfirstPeano.symm)
  have hdiff' :
      (toPeano p).commonDifference = (toPeano q).commonDifference := by
    simp only [toPeano]
    exact toPeano_eq_of_equivalent hdiff
  have hlen' :
      Peano.Progressions.FiniteArithmeticIncreasing.getLength (toPeano p) =
        Peano.Progressions.FiniteArithmeticIncreasing.getLength (toPeano q) := by
    rw [← getLength_toPeano, ← getLength_toPeano]
    exact toPeano_eq_of_equivalent hlen
  exact (equivalence_iff_toPeano p q).mpr
    (Peano.Progressions.FiniteArithmeticIncreasing.equivalence_of_same_params
      (toPeano p) (toPeano q) firstP.toPeano hp' hq' hdiff' hlen')

theorem effectiveFirst_rel_of_equivalence (p q : FiniteArithmeticIncreasing)
    (h : Equivalence p q) :
    Option.Rel (· ≈ ·) (effectiveFirst p) (effectiveFirst q) := by
  have h1 := h OrdinalNatural.Peano.one
  simp only [Sequences.Progression.tryGetElement, ← effectiveFirst_eq] at h1
  exact h1

theorem getLength_equivalent_of_equivalence (p q : FiniteArithmeticIncreasing)
    (h : Equivalence p q) : getLength p ≈ getLength q := by
  have hpeano :=
    Peano.Progressions.FiniteArithmeticIncreasing.getLength_eq_of_equivalence
      (toPeano p) (toPeano q) ((equivalence_iff_toPeano p q).mp h)
  apply equivalent_of_toPeano_eq
  rw [getLength_toPeano, getLength_toPeano, hpeano]

theorem commonDifference_equivalent_of_equivalence_of_length_ge_two
    (p q : FiniteArithmeticIncreasing) (firstP firstQ : Decimal)
    (hp : effectiveFirst p = some firstP) (hq : effectiveFirst q = some firstQ)
    (hfirst : firstP ≈ firstQ)
    (hne0 : ¬ getLength p ≈ zero) (hne1 : ¬ getLength p ≈ one)
    (hlen : getLength p ≈ getLength q) (h : Equivalence p q) :
    p.commonDifference ≈ q.commonDifference := by
  have h0 :
      Peano.Progressions.FiniteArithmeticIncreasing.getLength (toPeano p) ≠
        Peano.zero := by
    intro hz
    apply hne0
    apply equivalent_of_toPeano_eq
    rw [getLength_toPeano, hz, toPeano_zero]
  have h1 :
      Peano.Progressions.FiniteArithmeticIncreasing.getLength (toPeano p) ≠
        Peano.one := by
    intro hone
    apply hne1
    apply equivalent_of_toPeano_eq
    rw [getLength_toPeano, hone, toPeano_one]
  obtain ⟨n, hlenP⟩ :=
    Peano.Progressions.FiniteArithmeticIncreasing.getLength_ge_two_of_ne_zero_ne_one
      (toPeano p) h0 h1
  have hfirstPeano : firstP.toPeano = firstQ.toPeano :=
    toPeano_eq_of_equivalent hfirst
  have hp' :
      Peano.Progressions.FiniteArithmeticIncreasing.effectiveFirst (toPeano p) =
        some firstP.toPeano := by
    simpa [hp, Option.map] using (effectiveFirst_toPeano p).symm
  have hq' :
      Peano.Progressions.FiniteArithmeticIncreasing.effectiveFirst (toPeano q) =
        some firstP.toPeano := by
    have hq0 :
        Peano.Progressions.FiniteArithmeticIncreasing.effectiveFirst (toPeano q) =
          some firstQ.toPeano := by
      simpa [hq, Option.map] using (effectiveFirst_toPeano q).symm
    exact hq0.trans (congrArg some hfirstPeano.symm)
  have hlen' :
      Peano.Progressions.FiniteArithmeticIncreasing.getLength (toPeano p) =
        Peano.Progressions.FiniteArithmeticIncreasing.getLength (toPeano q) := by
    rw [← getLength_toPeano, ← getLength_toPeano]
    exact toPeano_eq_of_equivalent hlen
  have hdiff :=
    Peano.Progressions.FiniteArithmeticIncreasing.commonDifference_eq_of_equivalence_of_length_ge_two
      (toPeano p) (toPeano q) firstP.toPeano n hp' hq' hlenP hlen'
      ((equivalence_iff_toPeano p q).mp h)
  exact equivalent_of_toPeano_eq hdiff

/-- Extract an underlying `≈` witness from `Option.Rel (· ≈ ·)` on `some`s. -/
theorem equivalent_of_option_rel_some {x y : Decimal}
    (h : Option.Rel (· ≈ ·) (some x) (some y)) : x ≈ y := by
  cases h with
  | some heq => exact heq

/-- Equivalence of finite increasing arithmetic progressions is decidable by
comparing lengths, effective first elements, and (when the length is at least
two) common differences — without converting to `Progression` or walking
successive terms against the limit. -/
instance (p q : FiniteArithmeticIncreasing) : Decidable (p ≈ q) :=
  let lenP := getLength p
  if hL : lenP ≈ getLength q then
    if hZ : lenP ≈ zero then
      isTrue (equivalence_of_length_zero p q hZ (Setoid.trans (Setoid.symm hL) hZ))
    else if hF : Option.Rel (· ≈ ·) (effectiveFirst p) (effectiveFirst q) then
      if hOne : lenP ≈ one then
        match hf : effectiveFirst p with
        | none =>
          False.elim (hZ ((getLength_eq_zero_iff_effectiveFirst_none p).mpr hf))
        | some firstP =>
          match hq : effectiveFirst q with
          | none =>
            False.elim (by
              rw [hf, hq] at hF
              cases hF)
          | some firstQ =>
            isTrue (equivalence_of_length_one p q firstP firstQ hf hq
              (by
                rw [hf, hq] at hF
                exact equivalent_of_option_rel_some hF)
              hOne (Setoid.trans (Setoid.symm hL) hOne))
      else if hD : p.commonDifference ≈ q.commonDifference then
        match hf : effectiveFirst p with
        | none =>
          False.elim (hZ ((getLength_eq_zero_iff_effectiveFirst_none p).mpr hf))
        | some firstP =>
          match hq : effectiveFirst q with
          | none =>
            False.elim (by
              rw [hf, hq] at hF
              cases hF)
          | some firstQ =>
            isTrue (equivalence_of_equivalent_params p q firstP firstQ hf hq
              (by
                rw [hf, hq] at hF
                exact equivalent_of_option_rel_some hF)
              hD hL)
      else
        isFalse fun heq => by
          obtain ⟨firstP, hf⟩ := effectiveFirst_eq_some_of_pos_length p hZ
          have hrel := effectiveFirst_rel_of_equivalence p q heq
          simp only [hf] at hrel
          match hq : effectiveFirst q with
          | none =>
            rw [hq] at hrel
            cases hrel
          | some firstQ =>
            rw [hq] at hrel
            exact hD
              (commonDifference_equivalent_of_equivalence_of_length_ge_two
                p q firstP firstQ hf hq (equivalent_of_option_rel_some hrel)
                hZ hOne hL heq)
    else
      isFalse fun heq => hF (effectiveFirst_rel_of_equivalence p q heq)
  else
    isFalse fun heq => hL (getLength_equivalent_of_equivalence p q heq)

/-- The Peano predecessor is structurally smaller than its argument. -/
theorem sizeOf_peano_predecessor_lt (n : Peano) (hne : n ≠ Peano.zero) :
    sizeOf (n.predecessor hne) < sizeOf n := by
  cases n with
  | zero => exact False.elim (hne rfl)
  | successor n =>
    have hpred : (Peano.successor n).predecessor hne = n := rfl
    rw [hpred]
    exact Nat.lt_add_of_pos_left (k := 1) Nat.zero_lt_one

/-- Elements from a known start for the given remaining length, advancing by the
common difference with no limit comparisons. -/
def getElementsFrom (first commonDifference : Decimal) :
    Decimal → Sequences.List Decimal
  | n =>
    if h : n ≈ zero then
      .empty
    else
      .firstElement first
        (getElementsFrom (first + commonDifference) commonDifference
          (n.predecessor h))
termination_by n => n.toPeano
decreasing_by
  obtain ⟨hne, heq⟩ := predecessor_toPeano n h
  rw [heq]
  exact sizeOf_peano_predecessor_lt _ hne

/-- The ordered list of all elements of a finite increasing arithmetic
progression. Empty when there is no in-range first element. Uses the effective
first element and `getLength`, then advances by repeated addition of the common
difference — avoiding a limit comparison at every step. -/
def getElements (p : FiniteArithmeticIncreasing) : Sequences.List Decimal :=
  match effectiveFirst p with
  | none => .empty
  | some first =>
    getElementsFrom first p.commonDifference (getLength p)

/-- If `rest` continues an arithmetic progression after `prev` with common
difference `diff`, return the last element of that progression (which is `prev`
when `rest` is empty). Returns `none` when a consecutive pair does not advance
by a difference equivalent to `diff`. -/
def tryLastOfArithmeticContinuation (prev diff : Decimal) :
    Sequences.List Decimal → Option Decimal
  | .empty => some prev
  | .firstElement x xs =>
    match trySubtract x prev with
    | none => none
    | some d =>
      if d ≈ diff then
        tryLastOfArithmeticContinuation x diff xs
      else
        none

/-- Reconstruct a finite increasing arithmetic progression from the ordered list
of all its elements. Requires a proof that at least two elements are given.
Returns `none` when the list is not strictly ascending with a constant positive
common difference (compared up to Decimal equivalence).

Uses the first element, the common difference between consecutive terms, and
the last element as the limit. -/
def tryFromElements :
    (elements : Sequences.List Decimal) →
    Peano.two ≤ elements.length →
    Option FiniteArithmeticIncreasing
  | .empty, hge =>
    False.elim (Peano.not_two_le_zero (by
      change Peano.two ≤ Peano.zero
      exact hge))
  | .firstElement _ .empty, hge =>
    False.elim (Peano.not_two_le_one (by
      change Peano.two ≤ Peano.one
      exact hge))
  | .firstElement x (.firstElement y ys), _ =>
    match trySubtract y x with
    | none => none
    | some diff =>
      if hdiff : diff ≈ zero then
        none
      else
        match tryLastOfArithmeticContinuation y diff ys with
        | none => none
        | some last =>
          some {
            first := some x
            commonDifference := diff
            limit := last
            commonDifference_ne_zero := hdiff
          }

/-- A Decimal whose Peano embedding is nonzero is not equivalent to zero. -/
theorem not_equivalent_zero_of_toPeano_ne_zero (n : Decimal)
    (hne : n.toPeano ≠ Peano.zero) :
    ¬ n ≈ zero := by
  intro heq
  exact hne ((toPeano_eq_of_equivalent heq).trans toPeano_zero)

/-- Last element of a non-empty arithmetic walk of length `n`, starting at
`first` with common difference `commonDifference`. Defined via the Peano
embedding so that length and order facts transport directly. For `n ≈ zero` the
value is unused (`fromPeano` of the Peano placeholder). -/
def lastElementFrom (first commonDifference : Decimal) (n : Decimal) : Decimal :=
  fromPeano
    (Peano.Progressions.FiniteArithmeticIncreasing.lastElementFrom
      first.toPeano commonDifference.toPeano n.toPeano)

/-- `lastElementFrom` agrees with the Peano embedding on the nose. -/
theorem lastElementFrom_toPeano (first commonDifference : Decimal) (n : Decimal) :
    (lastElementFrom first commonDifference n).toPeano =
      Peano.Progressions.FiniteArithmeticIncreasing.lastElementFrom
        first.toPeano commonDifference.toPeano n.toPeano := by
  simpa [lastElementFrom] using toPeano_fromPeano
    (Peano.Progressions.FiniteArithmeticIncreasing.lastElementFrom
      first.toPeano commonDifference.toPeano n.toPeano)

/-- `getElementsFrom` produces a list whose length equals the Peano embedding of
the length argument. -/
theorem getElementsFrom_length (first commonDifference : Decimal) (n : Decimal) :
    (getElementsFrom first commonDifference n).length = n.toPeano := by
  have hgen :
      ∀ k : Peano, ∀ (first : Decimal) (n : Decimal),
        n.toPeano = k →
          (getElementsFrom first commonDifference n).length = k := by
    intro k
    induction k with
    | zero =>
      intro first n hn
      have hz : n ≈ zero :=
        equivalent_of_toPeano_eq (hn.trans toPeano_zero.symm)
      have hexpand :
          getElementsFrom first commonDifference n = Sequences.List.empty := by
        conv => lhs; unfold getElementsFrom
        simp only [hz, ↓reduceDIte]
      rw [hexpand, Sequences.List.length]
    | successor k ih =>
      intro first n hn
      have hne0 : n.toPeano ≠ Peano.zero := by
        rw [hn]
        exact Peano.successor_ne_zero k
      have hne : ¬ n ≈ zero :=
        not_equivalent_zero_of_toPeano_ne_zero n hne0
      obtain ⟨hne_peano, hpred⟩ := predecessor_toPeano n hne
      have hpred_k : (n.predecessor hne).toPeano = k := by
        rw [hpred]
        apply Eq.symm
        apply Peano.successor_injective
        rw [Peano.successor_predecessor n.toPeano hne_peano, hn]
      have hexpand :
          getElementsFrom first commonDifference n =
            Sequences.List.firstElement first
              (getElementsFrom (first + commonDifference) commonDifference
                (n.predecessor hne)) := by
        conv => lhs; unfold getElementsFrom
        simp only [hne, ↓reduceDIte]
      rw [hexpand, Sequences.List.length_firstElement]
      have ih' := ih (first + commonDifference) (n.predecessor hne) hpred_k
      rw [ih']
  exact hgen n.toPeano first n rfl

theorem getElementsFrom_ge_two_length (first commonDifference : Decimal)
    (n : Decimal) (hge : Peano.two ≤ n.toPeano) :
    Peano.two ≤ (getElementsFrom first commonDifference n).length := by
  rw [getElementsFrom_length]
  exact hge

/-- Expanding `getElementsFrom` at length at least two. -/
theorem getElementsFrom_of_two_le (first commonDifference : Decimal) (n : Decimal)
    (hge : Peano.two ≤ n.toPeano) :
    ∃ (hne : ¬ n ≈ zero)
      (hne' : ¬ n.predecessor hne ≈ zero),
      getElementsFrom first commonDifference n =
        Sequences.List.firstElement first
          (Sequences.List.firstElement (first + commonDifference)
            (getElementsFrom (first + commonDifference + commonDifference)
              commonDifference
              ((n.predecessor hne).predecessor hne'))) := by
  have hne0 : n.toPeano ≠ Peano.zero := by
    intro heq
    rw [heq] at hge
    exact Peano.not_two_le_zero hge
  have hne : ¬ n ≈ zero :=
    not_equivalent_zero_of_toPeano_ne_zero n hne0
  obtain ⟨hne_peano, hpred⟩ := predecessor_toPeano n hne
  have hne1 : (n.predecessor hne).toPeano ≠ Peano.zero := by
    intro heq
    have hn_one : n.toPeano = Peano.one := by
      have hsucc := Peano.successor_predecessor n.toPeano hne_peano
      rw [← hsucc, ← hpred, heq]
      rfl
    rw [hn_one] at hge
    exact Peano.not_two_le_one hge
  have hne' : ¬ n.predecessor hne ≈ zero :=
    not_equivalent_zero_of_toPeano_ne_zero _ hne1
  refine ⟨hne, hne', ?_⟩
  have hexpand1 :
      getElementsFrom first commonDifference n =
        Sequences.List.firstElement first
          (getElementsFrom (first + commonDifference) commonDifference
            (n.predecessor hne)) := by
    conv => lhs; unfold getElementsFrom
    simp only [hne, ↓reduceDIte]
  have hexpand2 :
      getElementsFrom (first + commonDifference) commonDifference
          (n.predecessor hne) =
        Sequences.List.firstElement (first + commonDifference)
          (getElementsFrom (first + commonDifference + commonDifference)
            commonDifference ((n.predecessor hne).predecessor hne')) := by
    conv => lhs; unfold getElementsFrom
    simp only [hne', ↓reduceDIte]
  rw [hexpand1, hexpand2]

/-- `trySubtract (x + d) x` recovers a value equivalent to `d`. -/
theorem trySubtract_self_add (x d : Decimal) :
    Option.Rel (· ≈ ·) (trySubtract (x + d) x) (some d) :=
  trySubtract_of_equivalent_add (Setoid.refl (x + d))

/-- Helper: predecessor Peano embedding equals `k` when `n.toPeano = successor k`. -/
theorem predecessor_toPeano_eq_of_succ (n : Decimal) (hne : ¬ n ≈ zero)
    (k : Peano) (hn : n.toPeano = Peano.successor k)
    (hne_peano : n.toPeano ≠ Peano.zero)
    (hpred : (n.predecessor hne).toPeano = n.toPeano.predecessor hne_peano) :
    (n.predecessor hne).toPeano = k := by
  rw [hpred]
  apply Eq.symm
  apply Peano.successor_injective
  rw [Peano.successor_predecessor n.toPeano hne_peano, hn]

/-- Continuing an arithmetic walk from `prev` by `getElementsFrom` recovers a
last element equivalent to `lastElementFrom`. -/
theorem tryLastOfArithmeticContinuation_getElementsFrom
    (prev commonDifference diff : Decimal) (n : Decimal)
    (hd : diff ≈ commonDifference) :
    Option.Rel (· ≈ ·)
      (tryLastOfArithmeticContinuation prev diff
        (getElementsFrom (prev + commonDifference) commonDifference n))
      (some (lastElementFrom prev commonDifference n.successor)) := by
  have hgen :
      ∀ k : Peano, ∀ (prev : Decimal) (n : Decimal),
        n.toPeano = k →
          Option.Rel (· ≈ ·)
            (tryLastOfArithmeticContinuation prev diff
              (getElementsFrom (prev + commonDifference) commonDifference n))
            (some (lastElementFrom prev commonDifference n.successor)) := by
    intro k
    induction k with
    | zero =>
      intro prev n hn
      have hz : n ≈ zero :=
        equivalent_of_toPeano_eq (hn.trans toPeano_zero.symm)
      have hexpand :
          getElementsFrom (prev + commonDifference) commonDifference n =
            Sequences.List.empty := by
        conv => lhs; unfold getElementsFrom
        simp only [hz, ↓reduceDIte]
      rw [hexpand, tryLastOfArithmeticContinuation]
      apply Option.Rel.some
      apply equivalent_of_toPeano_eq
      rw [lastElementFrom_toPeano, successor_toPeano, hn]
      change prev.toPeano =
        Peano.Progressions.FiniteArithmeticIncreasing.lastElementFrom
          prev.toPeano commonDifference.toPeano
          (Peano.successor Peano.zero)
      rfl
    | successor k ih =>
      intro prev n hn
      have hne0 : n.toPeano ≠ Peano.zero := by
        rw [hn]
        exact Peano.successor_ne_zero k
      have hne : ¬ n ≈ zero :=
        not_equivalent_zero_of_toPeano_ne_zero n hne0
      obtain ⟨hne_peano, hpred⟩ := predecessor_toPeano n hne
      have hpred_k :=
        predecessor_toPeano_eq_of_succ n hne k hn hne_peano hpred
      have hexpand :
          getElementsFrom (prev + commonDifference) commonDifference n =
            Sequences.List.firstElement (prev + commonDifference)
              (getElementsFrom (prev + commonDifference + commonDifference)
                commonDifference (n.predecessor hne)) := by
        conv => lhs; unfold getElementsFrom
        simp only [hne, ↓reduceDIte]
      rw [hexpand, tryLastOfArithmeticContinuation]
      have hrel := trySubtract_self_add prev commonDifference
      obtain ⟨d, hd_eq, hd_approx⟩ :=
        InfiniteArithmetic.exists_of_option_rel_some hrel
      simp only [hd_eq]
      have hd' : d ≈ diff := Setoid.trans hd_approx (Setoid.symm hd)
      simp only [hd', ↓reduceIte]
      have ih' :=
        ih (prev + commonDifference) (n.predecessor hne) hpred_k
      obtain ⟨last', hlast_eq, hlast_approx⟩ :=
        InfiniteArithmetic.exists_of_option_rel_some ih'
      rw [hlast_eq]
      apply Option.Rel.some
      refine Setoid.trans hlast_approx ?_
      apply equivalent_of_toPeano_eq
      rw [lastElementFrom_toPeano, lastElementFrom_toPeano, add_toPeano,
        successor_toPeano, successor_toPeano, hpred_k, hn]
      exact
        (Peano.Progressions.FiniteArithmeticIncreasing.lastElementFrom_succ_succ
          prev.toPeano commonDifference.toPeano k).symm
  exact hgen n.toPeano prev n rfl

/-- Reconstructing from `getElementsFrom` of Peano-length at least two recovers
a progression with the same start, an equivalent common difference, and a limit
equivalent to `lastElementFrom`. -/
theorem tryFromElements_getElementsFrom_ge_two (first commonDifference : Decimal)
    (hdiff0 : ¬ commonDifference ≈ zero) (n : Decimal)
    (hge : Peano.two ≤ n.toPeano)
    (hLen : Peano.two ≤
        (getElementsFrom first commonDifference n).length :=
      getElementsFrom_ge_two_length first commonDifference n hge) :
    ∃ (q : FiniteArithmeticIncreasing),
      tryFromElements (getElementsFrom first commonDifference n) hLen = some q ∧
        q.first = some first ∧
        q.commonDifference ≈ commonDifference ∧
        q.limit ≈ lastElementFrom first commonDifference n := by
  obtain ⟨hne, hne', hget⟩ := getElementsFrom_of_two_le first commonDifference n hge
  obtain ⟨hne_peano, hpred⟩ := predecessor_toPeano n hne
  obtain ⟨hne_peano', hpred'⟩ :=
    predecessor_toPeano (n.predecessor hne) hne'
  revert hLen
  rw [hget]
  intro hLen
  simp only [tryFromElements]
  have hrel := trySubtract_self_add first commonDifference
  obtain ⟨diff, hdiff_eq, hdiff_approx⟩ :=
    InfiniteArithmetic.exists_of_option_rel_some hrel
  simp only [hdiff_eq]
  have hdiff_ne : ¬ diff ≈ zero := fun heq =>
    hdiff0 (Setoid.trans (Setoid.symm hdiff_approx) heq)
  split
  · next heq => exact (hdiff_ne heq).elim
  · next hdiff =>
    have hlast_rel :=
      tryLastOfArithmeticContinuation_getElementsFrom
        (first + commonDifference) commonDifference diff
        ((n.predecessor hne).predecessor hne') hdiff_approx
    obtain ⟨last, hlast_eq, hlast_approx⟩ :=
      InfiniteArithmetic.exists_of_option_rel_some hlast_rel
    simp only [hlast_eq]
    refine ⟨({
        first := some first
        commonDifference := diff
        limit := last
        commonDifference_ne_zero := hdiff
      } : FiniteArithmeticIncreasing), rfl, rfl, hdiff_approx, ?_⟩
    refine Setoid.trans hlast_approx ?_
    apply equivalent_of_toPeano_eq
    rw [lastElementFrom_toPeano, lastElementFrom_toPeano, add_toPeano,
      successor_toPeano]
    have hn_shape :
        n.toPeano =
          Peano.successor
            (Peano.successor
              ((n.predecessor hne).predecessor hne').toPeano) := by
      have h1 := Peano.successor_predecessor n.toPeano hne_peano
      have h2 :=
        Peano.successor_predecessor (n.predecessor hne).toPeano hne_peano'
      rw [← h1]
      apply congrArg Peano.successor
      rw [← hpred]
      rw [← h2]
      apply congrArg Peano.successor
      exact hpred'.symm
    rw [hn_shape]
    exact
      (Peano.Progressions.FiniteArithmeticIncreasing.lastElementFrom_succ_succ
        first.toPeano commonDifference.toPeano
        ((n.predecessor hne).predecessor hne').toPeano).symm

/-- Length of a progression whose limit is equivalent to `lastElementFrom` of
its positive length, with an equivalent common difference. -/
theorem getLength_of_equivalent_lastElementFrom (first commonDifference diff last :
    Decimal) (n : Decimal)
    (hne : ¬ n ≈ zero)
    (hd : diff ≈ commonDifference)
    (hdiff : ¬ diff ≈ zero)
    (hl : last ≈ lastElementFrom first commonDifference n) :
    getLength {
      first := some first
      commonDifference := diff
      limit := last
      commonDifference_ne_zero := hdiff
    } ≈ n := by
  apply equivalent_of_toPeano_eq
  have hstruct :
      toPeano {
        first := some first
        commonDifference := diff
        limit := last
        commonDifference_ne_zero := hdiff
      } =
        {
          first := some first.toPeano
          commonDifference := diff.toPeano
          limit := last.toPeano
          commonDifference_ne_zero :=
            toPeano_ne_zero_of_not_equivalent_zero hdiff
        } := by
    simp only [toPeano]
  rw [getLength_toPeano, hstruct]
  have hlim :
      last.toPeano =
        Peano.Progressions.FiniteArithmeticIncreasing.lastElementFrom
          first.toPeano diff.toPeano n.toPeano := by
    rw [toPeano_eq_of_equivalent hl, lastElementFrom_toPeano,
      toPeano_eq_of_equivalent hd]
  rw [hlim]
  exact
    Peano.Progressions.FiniteArithmeticIncreasing.getLength_lastElementFrom
      first.toPeano diff.toPeano (toPeano_ne_zero_of_not_equivalent_zero hdiff)
      n.toPeano (toPeano_ne_zero_of_not_equivalent_zero hne)

/-- When the limit is equivalent to `lastElementFrom` of a positive length, the
effective first element is `some first`. -/
theorem effectiveFirst_of_equivalent_lastElementFrom (first commonDifference diff
    last : Decimal) (n : Decimal)
    (hne : ¬ n ≈ zero)
    (hd : diff ≈ commonDifference)
    (hdiff : ¬ diff ≈ zero)
    (hl : last ≈ lastElementFrom first commonDifference n) :
    effectiveFirst {
      first := some first
      commonDifference := diff
      limit := last
      commonDifference_ne_zero := hdiff
    } = some first := by
  simp only [effectiveFirst]
  have hcd_ne : commonDifference.toPeano ≠ Peano.zero := by
    rw [← toPeano_eq_of_equivalent hd]
    exact toPeano_ne_zero_of_not_equivalent_zero hdiff
  have hle_peano :
      first.toPeano ≤
        Peano.Progressions.FiniteArithmeticIncreasing.lastElementFrom
          first.toPeano commonDifference.toPeano n.toPeano :=
    Peano.Progressions.FiniteArithmeticIncreasing.first_le_lastElementFrom_of_pos
      first.toPeano commonDifference.toPeano hcd_ne n.toPeano
      (toPeano_ne_zero_of_not_equivalent_zero hne)
  have hle : first ≤ last := by
    apply (le_iff_toPeano_le first last).mpr
    rw [toPeano_eq_of_equivalent hl, lastElementFrom_toPeano]
    exact hle_peano
  simp only [hle, ↓reduceIte]

/-- `tryFromElements` recovers a progression equivalent to `p` from
`getElements p` when `p` has length at least two. -/
theorem tryFromElements_getElements (p : FiniteArithmeticIncreasing)
    (hge : Peano.two ≤ (getLength p).toPeano) :
    ∃ (hLen : Peano.two ≤ (getElements p).length)
      (q : FiniteArithmeticIncreasing),
      tryFromElements (getElements p) hLen = some q ∧ p ≈ q := by
  have hne0 : (getLength p).toPeano ≠ Peano.zero := by
    intro heq
    rw [heq] at hge
    exact Peano.not_two_le_zero hge
  have hne0' : ¬ getLength p ≈ zero :=
    not_equivalent_zero_of_toPeano_ne_zero (getLength p) hne0
  obtain ⟨first, hf⟩ := effectiveFirst_eq_some_of_pos_length p hne0'
  have hget :
      getElements p =
        getElementsFrom first p.commonDifference (getLength p) := by
    simp only [getElements, hf]
  have hLen : Peano.two ≤ (getElements p).length := by
    rw [hget, getElementsFrom_length]
    exact hge
  have hLen' : Peano.two ≤
      (getElementsFrom first p.commonDifference (getLength p)).length := by
    rw [getElementsFrom_length]
    exact hge
  obtain ⟨q, htry, hfirst_q, hdiff_q, hlast_q⟩ :=
    tryFromElements_getElementsFrom_ge_two first p.commonDifference
      p.commonDifference_ne_zero (getLength p) hge hLen'
  refine ⟨hLen, q, ?_⟩
  constructor
  · revert hLen
    rw [hget]
    intro hLen
    exact htry
  · have hq_rewrite :
        q = {
          first := some first
          commonDifference := q.commonDifference
          limit := q.limit
          commonDifference_ne_zero := q.commonDifference_ne_zero
        } := by
      cases q with
      | mk f d l h =>
        cases hfirst_q
        rfl
    have hf_q :
        effectiveFirst q = some first := by
      rw [hq_rewrite]
      exact effectiveFirst_of_equivalent_lastElementFrom first
        p.commonDifference q.commonDifference q.limit (getLength p) hne0'
        hdiff_q q.commonDifference_ne_zero hlast_q
    have hlen_q :
        getLength q ≈ getLength p := by
      rw [hq_rewrite]
      exact getLength_of_equivalent_lastElementFrom first p.commonDifference
        q.commonDifference q.limit (getLength p) hne0' hdiff_q
        q.commonDifference_ne_zero hlast_q
    exact equivalence_of_equivalent_params p q first first hf hf_q
      (Setoid.refl first) (Setoid.symm hdiff_q) (Setoid.symm hlen_q)

/-- `getElementsFrom` depends on the length argument only through its Peano
embedding. -/
theorem getElementsFrom_eq_of_toPeano_eq (first commonDifference : Decimal)
    (n m : Decimal) (h : n.toPeano = m.toPeano) :
    getElementsFrom first commonDifference n =
      getElementsFrom first commonDifference m := by
  have hgen :
      ∀ k : Peano, ∀ (first : Decimal) (n m : Decimal),
        n.toPeano = k → m.toPeano = k →
          getElementsFrom first commonDifference n =
            getElementsFrom first commonDifference m := by
    intro k
    induction k with
    | zero =>
      intro first n m hn hm
      have hnz : n ≈ zero :=
        equivalent_of_toPeano_eq (hn.trans toPeano_zero.symm)
      have hmz : m ≈ zero :=
        equivalent_of_toPeano_eq (hm.trans toPeano_zero.symm)
      have hn_empty :
          getElementsFrom first commonDifference n = Sequences.List.empty := by
        conv => lhs; unfold getElementsFrom
        simp only [hnz, ↓reduceDIte]
      have hm_empty :
          getElementsFrom first commonDifference m = Sequences.List.empty := by
        conv => lhs; unfold getElementsFrom
        simp only [hmz, ↓reduceDIte]
      rw [hn_empty, hm_empty]
    | successor k ih =>
      intro first n m hn hm
      have hne0 : n.toPeano ≠ Peano.zero := by
        rw [hn]
        exact Peano.successor_ne_zero k
      have hme0 : m.toPeano ≠ Peano.zero := by
        rw [hm]
        exact Peano.successor_ne_zero k
      have hne : ¬ n ≈ zero :=
        not_equivalent_zero_of_toPeano_ne_zero n hne0
      have hme : ¬ m ≈ zero :=
        not_equivalent_zero_of_toPeano_ne_zero m hme0
      obtain ⟨hne_peano, hpred_n⟩ := predecessor_toPeano n hne
      obtain ⟨hme_peano, hpred_m⟩ := predecessor_toPeano m hme
      have hpred_n_k : (n.predecessor hne).toPeano = k := by
        rw [hpred_n]
        apply Eq.symm
        apply Peano.successor_injective
        rw [Peano.successor_predecessor n.toPeano hne_peano, hn]
      have hpred_m_k : (m.predecessor hme).toPeano = k := by
        rw [hpred_m]
        apply Eq.symm
        apply Peano.successor_injective
        rw [Peano.successor_predecessor m.toPeano hme_peano, hm]
      have hn_expand :
          getElementsFrom first commonDifference n =
            Sequences.List.firstElement first
              (getElementsFrom (first + commonDifference) commonDifference
                (n.predecessor hne)) := by
        conv => lhs; unfold getElementsFrom
        simp only [hne, ↓reduceDIte]
      have hm_expand :
          getElementsFrom first commonDifference m =
            Sequences.List.firstElement first
              (getElementsFrom (first + commonDifference) commonDifference
                (m.predecessor hme)) := by
        conv => lhs; unfold getElementsFrom
        simp only [hme, ↓reduceDIte]
      rw [hn_expand, hm_expand]
      exact congrArg (Sequences.List.firstElement first)
        (ih (first + commonDifference) (n.predecessor hne) (m.predecessor hme)
          hpred_n_k hpred_m_k)
  exact hgen n.toPeano first n m rfl h.symm

/-- Equivalent starting points yield pointwise-equivalent `getElementsFrom`
walks of the same length. -/
theorem getElementsFrom_rel_of_equivalent_first (first first' commonDifference :
    Decimal) (n : Decimal) (h : first ≈ first') :
    Sequences.List.SameLengthElementwiseRelation (· ≈ ·)
      (getElementsFrom first commonDifference n)
      (getElementsFrom first' commonDifference n) := by
  have hgen :
      ∀ k : Peano, ∀ (first first' : Decimal) (n : Decimal),
        n.toPeano = k → first ≈ first' →
          Sequences.List.SameLengthElementwiseRelation (· ≈ ·)
            (getElementsFrom first commonDifference n)
            (getElementsFrom first' commonDifference n) := by
    intro k
    induction k with
    | zero =>
      intro first first' n hn _hfirst
      have hz : n ≈ zero :=
        equivalent_of_toPeano_eq (hn.trans toPeano_zero.symm)
      have hexpand :
          getElementsFrom first commonDifference n = Sequences.List.empty := by
        conv => lhs; unfold getElementsFrom
        simp only [hz, ↓reduceDIte]
      have hexpand' :
          getElementsFrom first' commonDifference n = Sequences.List.empty := by
        conv => lhs; unfold getElementsFrom
        simp only [hz, ↓reduceDIte]
      rw [hexpand, hexpand']
      exact Sequences.List.SameLengthElementwiseRelation.empty
    | successor k ih =>
      intro first first' n hn hfirst
      have hne0 : n.toPeano ≠ Peano.zero := by
        rw [hn]
        exact Peano.successor_ne_zero k
      have hne : ¬ n ≈ zero :=
        not_equivalent_zero_of_toPeano_ne_zero n hne0
      obtain ⟨hne_peano, hpred⟩ := predecessor_toPeano n hne
      have hpred_k : (n.predecessor hne).toPeano = k := by
        rw [hpred]
        apply Eq.symm
        apply Peano.successor_injective
        rw [Peano.successor_predecessor n.toPeano hne_peano, hn]
      have hexpand :
          getElementsFrom first commonDifference n =
            Sequences.List.firstElement first
              (getElementsFrom (first + commonDifference) commonDifference
                (n.predecessor hne)) := by
        conv => lhs; unfold getElementsFrom
        simp only [hne, ↓reduceDIte]
      have hexpand' :
          getElementsFrom first' commonDifference n =
            Sequences.List.firstElement first'
              (getElementsFrom (first' + commonDifference) commonDifference
                (n.predecessor hne)) := by
        conv => lhs; unfold getElementsFrom
        simp only [hne, ↓reduceDIte]
      rw [hexpand, hexpand']
      exact Sequences.List.SameLengthElementwiseRelation.firstElement hfirst
        (ih (first + commonDifference) (first' + commonDifference)
          (n.predecessor hne) hpred_k
          (equivalent_add hfirst (Setoid.refl commonDifference)))
  exact hgen n.toPeano first first' n rfl h

/-- Expanding `getElementsFrom` at a positive Peano length. -/
theorem getElementsFrom_of_toPeano_successor (first commonDifference : Decimal)
    (n : Decimal) (k : Peano) (hn : n.toPeano = Peano.successor k) :
    ∃ (hne : ¬ n ≈ zero),
      getElementsFrom first commonDifference n =
        Sequences.List.firstElement first
          (getElementsFrom (first + commonDifference) commonDifference
            (n.predecessor hne)) ∧
      (n.predecessor hne).toPeano = k := by
  have hne0 : n.toPeano ≠ Peano.zero := by
    rw [hn]
    exact Peano.successor_ne_zero k
  have hne : ¬ n ≈ zero :=
    not_equivalent_zero_of_toPeano_ne_zero n hne0
  obtain ⟨hne_peano, hpred⟩ := predecessor_toPeano n hne
  refine ⟨hne, ?_, ?_⟩
  · conv => lhs; unfold getElementsFrom
    simp only [hne, ↓reduceDIte]
  · rw [hpred]
    apply Eq.symm
    apply Peano.successor_injective
    rw [Peano.successor_predecessor n.toPeano hne_peano, hn]

/-- If a list continues arithmetically after `prev`, it is pointwise equivalent
to the corresponding `getElementsFrom` walk, and the recovered last element is
equivalent to `lastElementFrom`. -/
theorem rel_getElementsFrom_of_tryLastOfArithmeticContinuation
    (prev diff : Decimal) (rest : Sequences.List Decimal) (last : Decimal)
    (h : tryLastOfArithmeticContinuation prev diff rest = some last) :
    Sequences.List.SameLengthElementwiseRelation (· ≈ ·)
        (getElementsFrom (prev + diff) diff (fromPeano rest.length))
        rest ∧
      last ≈
        lastElementFrom prev diff (fromPeano rest.length).successor := by
  induction rest generalizing prev last with
  | empty =>
    simp only [tryLastOfArithmeticContinuation] at h
    injection h with heq
    constructor
    · have hz : fromPeano Peano.zero ≈ zero :=
        equivalent_of_toPeano_eq
          ((toPeano_fromPeano Peano.zero).trans toPeano_zero.symm)
      have hexpand :
          getElementsFrom (prev + diff) diff (fromPeano Peano.zero) =
            Sequences.List.empty := by
        conv => lhs; unfold getElementsFrom
        simp only [hz, ↓reduceDIte]
      change Sequences.List.SameLengthElementwiseRelation (· ≈ ·)
        (getElementsFrom (prev + diff) diff
          (fromPeano
            (Sequences.List.empty : Sequences.List Decimal).length))
        Sequences.List.empty
      rw [show (Sequences.List.empty : Sequences.List Decimal).length =
          Peano.zero from rfl, hexpand]
      exact Sequences.List.SameLengthElementwiseRelation.empty
    · subst heq
      apply equivalent_of_toPeano_eq
      rw [lastElementFrom_toPeano, successor_toPeano, toPeano_fromPeano]
      change prev.toPeano =
        Peano.Progressions.FiniteArithmeticIncreasing.lastElementFrom
          prev.toPeano diff.toPeano Peano.one
      rfl
  | firstElement x xs ih =>
    simp only [tryLastOfArithmeticContinuation] at h
    match hs : trySubtract x prev with
    | none =>
      simp only [hs] at h
      nomatch h
    | some d =>
      simp only [hs] at h
      by_cases hd : d ≈ diff
      · rw [show (if d ≈ diff then
              tryLastOfArithmeticContinuation x diff xs
            else none) =
            tryLastOfArithmeticContinuation x diff xs from by
              simp only [hd, ↓reduceIte]] at h
        obtain ⟨hxs, hlast⟩ := ih x last h
        have hx : x ≈ prev + diff :=
          Setoid.trans (eq_of_trySubtract_add prev x d hs)
            (equivalent_add (Setoid.refl prev) hd)
        have hlen := Sequences.List.length_firstElement x xs
        constructor
        · have hn :
              (fromPeano (Sequences.List.firstElement x xs).length).toPeano =
                Peano.successor xs.length := by
            rw [toPeano_fromPeano, hlen]
          obtain ⟨hne, hexpand, hpred⟩ :=
            getElementsFrom_of_toPeano_successor (prev + diff) diff
              (fromPeano (Sequences.List.firstElement x xs).length)
              xs.length hn
          have hpred_eq :
              getElementsFrom (prev + diff + diff) diff
                  ((fromPeano
                      (Sequences.List.firstElement x xs).length).predecessor
                    hne) =
                getElementsFrom (prev + diff + diff) diff
                  (fromPeano xs.length) :=
            getElementsFrom_eq_of_toPeano_eq (prev + diff + diff) diff _ _
              (hpred.trans (toPeano_fromPeano _).symm)
          have hstart : prev + diff + diff ≈ x + diff :=
            equivalent_add (Setoid.symm hx) (Setoid.refl diff)
          have hmid :
              Sequences.List.SameLengthElementwiseRelation (· ≈ ·)
                (getElementsFrom (prev + diff + diff) diff
                  (fromPeano xs.length))
                (getElementsFrom (x + diff) diff (fromPeano xs.length)) :=
            getElementsFrom_rel_of_equivalent_first (prev + diff + diff)
              (x + diff) diff (fromPeano xs.length) hstart
          have htail :
              Sequences.List.SameLengthElementwiseRelation (· ≈ ·)
                (getElementsFrom (prev + diff + diff) diff
                  (fromPeano xs.length))
                xs :=
            Sequences.List.SameLengthElementwiseRelation.trans
              (r := (· ≈ ·)) (s := (· ≈ ·)) (t := (· ≈ ·))
              (fun h1 h2 => Setoid.trans h1 h2) hmid hxs
          rw [hexpand, hpred_eq]
          exact Sequences.List.SameLengthElementwiseRelation.firstElement
            (Setoid.symm hx) htail
        · have h1 :
              last ≈
                lastElementFrom (prev + diff) diff
                  (fromPeano xs.length).successor := by
            refine Setoid.trans hlast ?_
            apply equivalent_of_toPeano_eq
            rw [lastElementFrom_toPeano, lastElementFrom_toPeano,
              toPeano_eq_of_equivalent hx]
          have h2 :
              lastElementFrom (prev + diff) diff
                  (fromPeano xs.length).successor ≈
                lastElementFrom prev diff
                  (fromPeano
                    (Sequences.List.firstElement x xs).length).successor := by
            apply equivalent_of_toPeano_eq
            rw [lastElementFrom_toPeano, lastElementFrom_toPeano, add_toPeano,
              successor_toPeano, successor_toPeano, toPeano_fromPeano,
              toPeano_fromPeano, hlen]
            exact
              (Peano.Progressions.FiniteArithmeticIncreasing.lastElementFrom_succ_succ
                prev.toPeano diff.toPeano xs.length).symm
          exact Setoid.trans h1 h2
      · simp only [hd, ↓reduceIte] at h
        nomatch h

/-- `getElements` recovers a list pointwise equivalent to the original from a
successful `tryFromElements`. Exact equality may fail because Decimal
subtraction recovers steps only up to representation. -/
theorem getElements_tryFromElements (elements : Sequences.List Decimal)
    (hge : Peano.two ≤ elements.length)
    (p : FiniteArithmeticIncreasing)
    (h : tryFromElements elements hge = some p) :
    Sequences.List.SameLengthElementwiseRelation (· ≈ ·) (getElements p) elements := by
  match helem : elements with
  | .empty =>
    subst helem
    exact (Peano.not_two_le_zero (by
      change Peano.two ≤ Peano.zero
      exact hge)).elim
  | .firstElement _ .empty =>
    subst helem
    exact (Peano.not_two_le_one (by
      change Peano.two ≤ Peano.one
      exact hge)).elim
  | .firstElement x (.firstElement y ys) =>
    subst helem
    simp only [tryFromElements] at h
    match hs : trySubtract y x with
    | none =>
      simp only [hs] at h
      nomatch h
    | some diff =>
      simp only [hs] at h
      by_cases hdiff0 : diff ≈ zero
      · simp only [hdiff0, ↓reduceDIte] at h
        nomatch h
      · simp only [hdiff0, ↓reduceDIte] at h
        match hl : tryLastOfArithmeticContinuation y diff ys with
        | none =>
          simp only [hl] at h
          nomatch h
        | some last =>
          simp only [hl] at h
          injection h with heq
          subst heq
          have hcont :
              tryLastOfArithmeticContinuation x diff
                  (Sequences.List.firstElement y ys) =
                some last := by
            simp only [tryLastOfArithmeticContinuation, hs]
            have hdrefl : diff ≈ diff := Setoid.refl _
            simp only [hdrefl, ↓reduceIte, hl]
          obtain ⟨hrest, hlast⟩ :=
            rel_getElementsFrom_of_tryLastOfArithmeticContinuation x diff
              (Sequences.List.firstElement y ys) last hcont
          let n : Decimal :=
            (fromPeano (Sequences.List.firstElement y ys).length).successor
          have hne : ¬ n ≈ zero := by
            intro heq
            have hpeano := toPeano_eq_of_equivalent heq
            rw [successor_toPeano, toPeano_fromPeano, toPeano_zero] at hpeano
            exact Peano.successor_ne_zero _ hpeano
          have hf : effectiveFirst
              {
                first := some x
                commonDifference := diff
                limit := last
                commonDifference_ne_zero := hdiff0
              } = some x :=
            effectiveFirst_of_equivalent_lastElementFrom x diff diff last n hne
              (Setoid.refl diff) hdiff0 hlast
          have hlenp :
              getLength
                  {
                    first := some x
                    commonDifference := diff
                    limit := last
                    commonDifference_ne_zero := hdiff0
                  } ≈ n :=
            getLength_of_equivalent_lastElementFrom x diff diff last n hne
              (Setoid.refl diff) hdiff0 hlast
          have hget :
              getElements
                  {
                    first := some x
                    commonDifference := diff
                    limit := last
                    commonDifference_ne_zero := hdiff0
                  } =
                getElementsFrom x diff
                  (getLength
                    {
                      first := some x
                      commonDifference := diff
                      limit := last
                      commonDifference_ne_zero := hdiff0
                    }) := by
            simp only [getElements, hf]
          rw [hget]
          have hlen_toPeano :
              (getLength
                  {
                    first := some x
                    commonDifference := diff
                    limit := last
                    commonDifference_ne_zero := hdiff0
                  }).toPeano =
                n.toPeano :=
            toPeano_eq_of_equivalent hlenp
          have hget' :
              getElementsFrom x diff
                  (getLength
                    {
                      first := some x
                      commonDifference := diff
                      limit := last
                      commonDifference_ne_zero := hdiff0
                    }) =
                getElementsFrom x diff n :=
            getElementsFrom_eq_of_toPeano_eq x diff _ _ hlen_toPeano
          rw [hget']
          have hn :
              n.toPeano =
                Peano.successor
                  (Sequences.List.firstElement y ys).length := by
            rw [successor_toPeano, toPeano_fromPeano]
          obtain ⟨hne_n, hexpand, hpred⟩ :=
            getElementsFrom_of_toPeano_successor x diff n
              (Sequences.List.firstElement y ys).length hn
          have hpred_eq :
              getElementsFrom (x + diff) diff (n.predecessor hne_n) =
                getElementsFrom (x + diff) diff
                  (fromPeano
                    (Sequences.List.firstElement y ys).length) :=
            getElementsFrom_eq_of_toPeano_eq (x + diff) diff _ _
              (hpred.trans (toPeano_fromPeano _).symm)
          rw [hexpand, hpred_eq]
          exact Sequences.List.SameLengthElementwiseRelation.firstElement
            (Setoid.refl x) hrest

/-- Recover the first element of an arithmetic progression from an element at the
given ordinal Decimal index and the common difference by subtracting
`(fromOrdinal index - one) * commonDifference`. Returns `none` when that
subtraction is impossible in the Decimal numbers. -/
def tryFirstFromIndexedElement
    (index : OrdinalNatural.Decimal) (element commonDifference : Decimal) :
    Option Decimal :=
  trySubtract element
    ((subtract (fromOrdinal index) one (one_le_fromOrdinal index)) *
      commonDifference)

/-- Given two ordered indexed elements (`index < index'`) of a prospective
increasing arithmetic progression, recover the common difference
`(element' - element) / (index' - index)`. Returns `none` when the elements are
not strictly ascending or the element gap is not divisible by the index gap. -/
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

/-- Reconstruct a finite increasing arithmetic progression from two of its
elements at different ordinal Decimal indexes together with the progression
length. Returns `none` when either index exceeds the length, when the recovered
common difference is equivalent to zero, or when the values are not consistent
with a strictly increasing arithmetic progression of that length. Indexes are
compared up to Decimal equivalence.

The reconstructed progression uses the recovered first element and common
difference, and takes the last element of an arithmetic walk of the given
length as the limit. -/
def tryFromTwoElementsAndLength
    (index1 : OrdinalNatural.Decimal) (element1 : Decimal)
    (index2 : OrdinalNatural.Decimal) (element2 : Decimal)
    (length : Decimal)
    (hne : ¬ index1 ≈ index2) :
    Option FiniteArithmeticIncreasing :=
  if fromOrdinal index1 ≤ length then
    if fromOrdinal index2 ≤ length then
      match OrdinalNatural.Decimal.compare index1 index2 with
      | .equivalent heq => False.elim (hne heq)
      | .less hlt =>
        match tryCommonDifferenceFromOrderedIndexedElements
            index1 element1 index2 element2 hlt with
        | none => none
        | some diff =>
          if hdiff : diff ≈ zero then
            none
          else
            match tryFirstFromIndexedElement index1 element1 diff with
            | none => none
            | some first =>
              some {
                first := some first
                commonDifference := diff
                limit := lastElementFrom first diff length
                commonDifference_ne_zero := hdiff
              }
      | .greater hgt =>
        match tryCommonDifferenceFromOrderedIndexedElements
            index2 element2 index1 element1 hgt with
        | none => none
        | some diff =>
          if hdiff : diff ≈ zero then
            none
          else
            match tryFirstFromIndexedElement index2 element2 diff with
            | none => none
            | some first =>
              some {
                first := some first
                commonDifference := diff
                limit := lastElementFrom first diff length
                commonDifference_ne_zero := hdiff
              }
    else
      none
  else
    none

end FiniteArithmeticIncreasing

end ZeroMath.Numbers.CardinalNatural.Decimal.Progressions
