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

end FiniteArithmeticIncreasing

end ZeroMath.Numbers.CardinalNatural.Decimal.Progressions
