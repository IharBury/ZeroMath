import ZeroMath.Numbers.CardinalNatural.Decimal
import ZeroMath.Numbers.CardinalNatural.Decimal.Progressions.InfiniteArithmetic
import ZeroMath.Numbers.CardinalNatural.Peano.Progressions.FiniteArithmeticIncreasing
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

end FiniteArithmeticIncreasing

end ZeroMath.Numbers.CardinalNatural.Decimal.Progressions
