import ZeroMath.Numbers.CardinalNatural.Decimal
import ZeroMath.Numbers.OrdinalNatural.Decimal
import ZeroMath.Numbers.OrdinalNatural.Decimal.Progressions.InfiniteArithmetic
import ZeroMath.Numbers.OrdinalNatural.Peano.Progressions.FiniteArithmeticIncreasing
import ZeroMath.Sequences.List
import ZeroMath.Sequences.Progression

namespace ZeroMath.Numbers.OrdinalNatural.Decimal.Progressions

/-- A finite increasing arithmetic progression of Decimal numbers with positive
common difference, defined by an optional first element (`none` for the empty
progression), the common difference, and a limit such that no element is
greater than the limit. The progression is also empty when the first element
is greater than the limit. Because every Decimal number is at least one, the
common difference is always positive. -/
structure FiniteArithmeticIncreasing where
  first : Option Decimal
  commonDifference : Decimal
  limit : Decimal

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

/-- Decimal order is reflected by the Peano embedding. -/
theorem toPeano_le_of_le {a b : Decimal} (h : a ≤ b) : a.toPeano ≤ b.toPeano := by
  cases h with
  | inl hlt => exact Or.inl hlt
  | inr heq => exact Or.inr (toPeano_eq_of_equivalent heq)

/-- Every element obtained from `tryGetElement` is at most the limit. -/
theorem tryGetElement_le_limit (p : FiniteArithmeticIncreasing)
    (index : Peano) (x : Decimal)
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

/-- If `tryGetElement` returns a value, the Peano index is at most the Peano
embedding of that value, because the progression is strictly increasing with
positive common difference. -/
theorem le_of_tryGetElement_eq_some (p : FiniteArithmeticIncreasing)
    (index : Peano) (x : Decimal)
    (h : Sequences.Progression.tryGetElement index (toProgression p) = some x) :
    index ≤ x.toPeano := by
  induction index generalizing x with
  | one =>
    exact Peano.one_le' x.toPeano
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
        have hn : n ≤ y.toPeano := ih y hm
        have hsucc : Peano.successor n ≤ Peano.successor y.toPeano :=
          Peano.succ_le_succ hn
        have hy_le : Peano.successor y.toPeano ≤
            (y + p.commonDifference).toPeano := by
          rw [add_toPeano, ← Peano.add_one]
          exact Peano.le_add_of_le_right y.toPeano
            (Peano.one_le' p.commonDifference.toPeano)
        exact Peano.le_trans hsucc (heq ▸ hy_le)
      · simp only [hle, ↓reduceIte] at hnext
        nomatch hnext

/-- The progression obtained from a finite increasing arithmetic progression is
finite: `tryGetElement` at `successor limit.toPeano` is always `none`, since any
returned value would have to be both ≥ `successor limit.toPeano` and
≤ `limit.toPeano`. -/
theorem toProgression_finite (p : FiniteArithmeticIncreasing) :
    Sequences.Progression.Finite (toProgression p) := by
  refine ⟨Peano.successor p.limit.toPeano, ?_⟩
  cases h :
      Sequences.Progression.tryGetElement
        (Peano.successor p.limit.toPeano) (toProgression p) with
  | none =>
    rfl
  | some x =>
    have hle_lim :=
      tryGetElement_le_limit p (Peano.successor p.limit.toPeano) x h
    have hle_idx :=
      le_of_tryGetElement_eq_some p (Peano.successor p.limit.toPeano) x h
    exact (Peano.not_succ_le p.limit.toPeano
      (Peano.le_trans hle_idx (toPeano_le_of_le hle_lim))).elim

/-- Length remaining from an element already known to lie in the progression,
given the room above that element up to the limit (`none` when the element
equals the limit). Computed with one division by the common difference instead
of comparing each successive term to the limit. -/
def lengthFromGap (diff : Decimal) : Option Decimal → CardinalNatural.Decimal
  | none => CardinalNatural.Decimal.one
  | some gap =>
    match divideWithRemainder gap diff with
    | (none, _) => CardinalNatural.Decimal.one
    | (some q, _) =>
      CardinalNatural.Decimal.successor (CardinalNatural.Decimal.fromOrdinal q)

/-- The length of a finite increasing arithmetic progression: the number of
elements before `tryGetElement` first returns `none`. Uses a single comparison
of the first element to the limit and one division, avoiding a comparison at
every step of the progression. -/
def getLength (p : FiniteArithmeticIncreasing) : CardinalNatural.Decimal :=
  match p.first with
  | none => CardinalNatural.Decimal.zero
  | some first =>
    match compare first p.limit with
    | .greater _ => CardinalNatural.Decimal.zero
    | .equivalent _ => CardinalNatural.Decimal.one
    | .less hlt =>
      lengthFromGap p.commonDifference (some (subtract p.limit first hlt))

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

/-- Decimal `≤` is reflected and reflected by the Peano embedding. -/
theorem le_iff_toPeano_le (a b : Decimal) : a ≤ b ↔ a.toPeano ≤ b.toPeano := by
  constructor
  · exact toPeano_le_of_le
  · intro h
    cases h with
    | inl hlt => exact Or.inl hlt
    | inr heq => exact Or.inr (equivalent_of_toPeano_eq heq)

/-- `lengthFromGap` agrees with the Peano `lengthFromGap` on embeddings. -/
theorem lengthFromGap_toPeano (diff : Decimal) (gap : Option Decimal) :
    (lengthFromGap diff gap).toPeano =
      Peano.Progressions.FiniteArithmeticIncreasing.lengthFromGap
        diff.toPeano (gap.map Decimal.toPeano) := by
  match gap with
  | none =>
    simp only [lengthFromGap, Option.map, CardinalNatural.Decimal.toPeano_one,
      Peano.Progressions.FiniteArithmeticIncreasing.lengthFromGap]
  | some g =>
    match hdiv : divideWithRemainder g diff with
    | (none, r) =>
      have hp := divideWithRemainder_toPeano g diff hdiv
      simp only [lengthFromGap, hdiv, Option.map, hp,
        Peano.Progressions.FiniteArithmeticIncreasing.lengthFromGap,
        CardinalNatural.Decimal.toPeano_one]
    | (some q, r) =>
      have hp := divideWithRemainder_toPeano g diff hdiv
      simp only [lengthFromGap, hdiv, Option.map, hp,
        Peano.Progressions.FiniteArithmeticIncreasing.lengthFromGap]
      rw [CardinalNatural.Decimal.successor_toPeano,
        CardinalNatural.Decimal.fromOrdinal_toPeano_eq_fromOrdinal_peano,
        CardinalNatural.Peano.fromOrdinal]

/-- `getLength` agrees with Peano `getLength` on the embedded progression. -/
theorem getLength_toPeano (p : FiniteArithmeticIncreasing) :
    (getLength p).toPeano =
      Peano.Progressions.FiniteArithmeticIncreasing.getLength (toPeano p) := by
  cases hf : p.first with
  | none =>
    simp only [getLength, hf, toPeano,
      Peano.Progressions.FiniteArithmeticIncreasing.getLength,
      CardinalNatural.Decimal.toPeano_zero]
  | some first =>
    have hto : toPeano p =
        {
          first := some first.toPeano
          commonDifference := p.commonDifference.toPeano
          limit := p.limit.toPeano
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
      obtain ⟨_, hsub_eq⟩ := subtract_toPeano p.limit first hlt
      have hlen :=
        lengthFromGap_toPeano p.commonDifference (some (subtract p.limit first hlt))
      simpa [Option.map, hsub_eq] using hlen
    | equal heq =>
      have hdec : compare first p.limit =
          .equivalent (equivalent_of_toPeano_eq heq) := by
        simp only [compare, hcmp]
      simp only [hdec, CardinalNatural.Decimal.toPeano_one]
    | greater hgt =>
      have hdec : compare first p.limit = .greater hgt := by
        simp only [compare, hcmp]
      simp only [hdec, CardinalNatural.Decimal.toPeano_zero]

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

theorem getLengthFrom_eq_of_acc_eq {α : Type _} (next : α → Option α)
    (current : Option α)
    (h1 h2 : Acc (Sequences.Progression.OptionStep next) current) :
    Sequences.Progression.getLengthFrom next current h1 =
      Sequences.Progression.getLengthFrom next current h2 :=
  rfl

theorem getLengthFrom_eq_of_current_eq {α : Type _} (next : α → Option α)
    {c1 c2 : Option α} (hEq : c1 = c2)
    (h1 : Acc (Sequences.Progression.OptionStep next) c1) :
    Sequences.Progression.getLengthFrom next c1 h1 =
      Sequences.Progression.getLengthFrom next c2 (hEq ▸ h1) := by
  cases hEq
  rfl

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
        rw [getLengthFrom_eq_of_current_eq _ hmap hAcc_map]
        rw [Sequences.Progression.getLengthFrom_some
          (Peano.Progressions.FiniteArithmeticIncreasing.toProgression
            (toPeano p)).next
          x.toPeano (hmap ▸ hAcc_map)]
        have hnext := next_toPeano p x
        have ih' := ih ((toProgression p).next x)
          (Sequences.Progression.OptionStep.step x)
        refine congrArg CardinalNatural.Peano.successor (ih'.trans ?_)
        exact
          (getLengthFrom_eq_of_current_eq _
            hnext
            (acc_map_toPeano p ((toProgression p).next x)
              (hAccx.inv (Sequences.Progression.OptionStep.step x)))).trans
            (getLengthFrom_eq_of_acc_eq _ _ _ _))
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
    (getLengthFrom_eq_of_current_eq _
      hfirst
      (acc_map_toPeano p (toProgression p).first
        (Sequences.Progression.acc_first_of_finite (toProgression p)
          (toProgression_finite p)))).trans
      (getLengthFrom_eq_of_acc_eq _ _ _ _)

/-- `getLength` agrees with walking `toProgression` via `Progression.getLength`. -/
theorem getLength_eq (p : FiniteArithmeticIncreasing) :
    getLength p ≈
      CardinalNatural.Decimal.fromPeano
        (Sequences.Progression.getLength (toProgression p)
          (toProgression_finite p)) := by
  apply CardinalNatural.Decimal.equivalent_of_toPeano_eq
  rw [CardinalNatural.Decimal.toPeano_fromPeano, getLength_toPeano,
    Peano.Progressions.FiniteArithmeticIncreasing.getLength_eq (toPeano p),
    progression_getLength_toPeano]

/-- Element at a positive ordinal index starting from a known first value, using
the closed form with no limit comparisons. The first element has index
equivalent to `one`; otherwise the value is
`first + (predecessor index) * commonDifference`. -/
def getElementFrom (first commonDifference : Decimal) (index : Decimal) : Decimal :=
  if h : index ≈ one then
    first
  else
    first + (index.predecessor h) * commonDifference

/-- If there is no first element, the length is zero. -/
theorem getLength_eq_zero_of_first_none (p : FiniteArithmeticIncreasing)
    (h : p.first = none) :
    getLength p = CardinalNatural.Decimal.zero := by
  simp only [getLength, h]

/-- If the first element is greater than the limit, the length is zero. -/
theorem getLength_eq_zero_of_first_gt_limit (p : FiniteArithmeticIncreasing)
    (first : Decimal) (hf : p.first = some first) (hgt : p.limit < first) :
    getLength p = CardinalNatural.Decimal.zero := by
  unfold getLength
  simp only [hf]
  match hcmp : compare first p.limit with
  | .less hlt =>
    exact (Peano.not_lt_of_lt (toPeano_lt_of_lt hgt) (toPeano_lt_of_lt hlt)).elim
  | .equivalent heq =>
    have hself : p.limit.toPeano < p.limit.toPeano := by
      have hlt := toPeano_lt_of_lt hgt
      rwa [toPeano_eq_of_equivalent heq] at hlt
    exact (Peano.not_lt_self _ hself).elim
  | .greater _ =>
    rfl

/-- The length bound is impossible when there is no first element. -/
theorem not_fromOrdinal_le_getLength_of_first_none
    (p : FiniteArithmeticIncreasing) (index : Decimal)
    (hle : CardinalNatural.Decimal.fromOrdinal index ≤ getLength p)
    (h : p.first = none) : False := by
  have hle' : CardinalNatural.Decimal.fromOrdinal index ≤
      CardinalNatural.Decimal.zero :=
    (getLength_eq_zero_of_first_none p h) ▸ hle
  exact CardinalNatural.Decimal.fromOrdinal_not_equivalent_zero index
    (CardinalNatural.Decimal.eq_zero_of_le_zero _ hle')

/-- The length bound is impossible when the first element exceeds the limit. -/
theorem not_fromOrdinal_le_getLength_of_first_gt_limit
    (p : FiniteArithmeticIncreasing) (index first : Decimal)
    (hle : CardinalNatural.Decimal.fromOrdinal index ≤ getLength p)
    (hf : p.first = some first) (hgt : p.limit < first) : False := by
  have hle' : CardinalNatural.Decimal.fromOrdinal index ≤
      CardinalNatural.Decimal.zero :=
    (getLength_eq_zero_of_first_gt_limit p first hf hgt) ▸ hle
  exact CardinalNatural.Decimal.fromOrdinal_not_equivalent_zero index
    (CardinalNatural.Decimal.eq_zero_of_le_zero _ hle')

/-- The element at the given positive ordinal index, when that index does not
exceed the progression's length. The first element has index equivalent to
`one`. Uses a single `compare` of the first element to the limit (as in
`getLength`), then the closed form of the arithmetic progression — avoiding
`toProgression` and a limit comparison at every step. -/
def getElement (p : FiniteArithmeticIncreasing) (index : Decimal)
    (hle : CardinalNatural.Decimal.fromOrdinal index ≤ getLength p) : Decimal :=
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

/-- Closed-form `getElementFrom` matches `InfiniteArithmetic.getElement`. -/
theorem getElementFrom_eq_InfiniteArithmetic_getElement
    (first commonDifference index : Decimal) :
    getElementFrom first commonDifference index =
      InfiniteArithmetic.getElement
        { first := first, commonDifference := commonDifference } index :=
  rfl

/-- A Decimal length bound on `fromOrdinal index` yields the corresponding Peano
bound for walking `toProgression`. -/
theorem fromOrdinal_le_progression_getLength
    (p : FiniteArithmeticIncreasing) (index : Decimal)
    (hle : CardinalNatural.Decimal.fromOrdinal index ≤ getLength p) :
    CardinalNatural.Peano.fromOrdinal index.toPeano ≤
      Sequences.Progression.getLength (toProgression p)
        (toProgression_finite p) := by
  have hle' :
      CardinalNatural.Decimal.fromOrdinal index ≤
        CardinalNatural.Decimal.fromPeano
          (Sequences.Progression.getLength (toProgression p)
            (toProgression_finite p)) :=
    CardinalNatural.Decimal.le_trans hle (Or.inr (getLength_eq p))
  have hpeano := CardinalNatural.Decimal.toPeano_le_of_le hle'
  rw [CardinalNatural.Decimal.fromOrdinal_toPeano_eq_fromOrdinal_peano,
    CardinalNatural.Decimal.toPeano_fromPeano] at hpeano
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
    (index : Decimal) (x : Decimal)
    (h : Sequences.Progression.tryGetElement index.toPeano (toProgression p) =
      some x) :
    x ≈ getElementFrom start p.commonDifference index := by
  if hone : index ≈ one then
    have hpeano : index.toPeano = Peano.one :=
      (InfiniteArithmetic.toPeano_eq_one_iff_equivalent_one index).mpr hone
    rw [hpeano, Sequences.Progression.tryGetElement, hf] at h
    injection h with heq
    rw [getElementFrom, dif_pos hone, heq]
    exact Setoid.refl _
  else
    have hpeano :=
      InfiniteArithmetic.toPeano_eq_succ_predecessor_toPeano index hone
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
          InfiniteArithmetic.equivalent_add_right hy
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
  obtain ⟨hne, heq⟩ := predecessor_toPeano index hone
  simp only [heq]
  exact InfiniteArithmetic.sizeOf_predecessor_lt _ hne

/-- `getElement` agrees with walking `toProgression` via `Progression.getElement`
up to Decimal equivalence. -/
theorem getElement_eq (p : FiniteArithmeticIncreasing) (index : Decimal)
    (hle : CardinalNatural.Decimal.fromOrdinal index ≤ getLength p) :
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
theorem tryGetElement_toPeano (p : FiniteArithmeticIncreasing) (index : Peano) :
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

theorem lengthFromGap_ne_zero (diff : Decimal) (gap : Option Decimal)
    (h : lengthFromGap diff gap ≈ CardinalNatural.Decimal.zero) : False := by
  have hpeano :
      (lengthFromGap diff gap).toPeano = CardinalNatural.Peano.zero :=
    (CardinalNatural.Decimal.toPeano_eq_of_equivalent h).trans
      CardinalNatural.Decimal.toPeano_zero
  rw [lengthFromGap_toPeano] at hpeano
  exact Peano.Progressions.FiniteArithmeticIncreasing.lengthFromGap_ne_zero
    diff.toPeano _ hpeano

theorem getLength_eq_zero_iff_effectiveFirst_none (p : FiniteArithmeticIncreasing) :
    getLength p ≈ CardinalNatural.Decimal.zero ↔ effectiveFirst p = none := by
  constructor
  · intro hlen
    have hpeano :
        Peano.Progressions.FiniteArithmeticIncreasing.getLength (toPeano p) =
          CardinalNatural.Peano.zero := by
      rw [← getLength_toPeano]
      exact (CardinalNatural.Decimal.toPeano_eq_of_equivalent hlen).trans
        CardinalNatural.Decimal.toPeano_zero
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
    (h : ¬ getLength p ≈ CardinalNatural.Decimal.zero) :
    ∃ first, effectiveFirst p = some first := by
  cases hf : effectiveFirst p with
  | none =>
    exact False.elim (h ((getLength_eq_zero_iff_effectiveFirst_none p).mpr hf))
  | some first =>
    exact ⟨first, rfl⟩

/-- Empty progressions (length zero) are equivalent. -/
theorem equivalence_of_length_zero (p q : FiniteArithmeticIncreasing)
    (hp : getLength p ≈ CardinalNatural.Decimal.zero)
    (hq : getLength q ≈ CardinalNatural.Decimal.zero) :
    Equivalence p q := by
  have hp' :
      Peano.Progressions.FiniteArithmeticIncreasing.getLength (toPeano p) =
        CardinalNatural.Peano.zero := by
    rw [← getLength_toPeano]
    exact (CardinalNatural.Decimal.toPeano_eq_of_equivalent hp).trans
      CardinalNatural.Decimal.toPeano_zero
  have hq' :
      Peano.Progressions.FiniteArithmeticIncreasing.getLength (toPeano q) =
        CardinalNatural.Peano.zero := by
    rw [← getLength_toPeano]
    exact (CardinalNatural.Decimal.toPeano_eq_of_equivalent hq).trans
      CardinalNatural.Decimal.toPeano_zero
  exact (equivalence_iff_toPeano p q).mpr
    (Peano.Progressions.FiniteArithmeticIncreasing.equivalence_of_length_zero
      (toPeano p) (toPeano q) hp' hq')

/-- Length-one progressions with equivalent first elements are equivalent. -/
theorem equivalence_of_length_one (p q : FiniteArithmeticIncreasing)
    (firstP firstQ : Decimal)
    (hp : effectiveFirst p = some firstP) (hq : effectiveFirst q = some firstQ)
    (hfirst : firstP ≈ firstQ)
    (hlenP : getLength p ≈ CardinalNatural.Decimal.one)
    (hlenQ : getLength q ≈ CardinalNatural.Decimal.one) :
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
        CardinalNatural.Peano.one := by
    rw [← getLength_toPeano]
    exact (CardinalNatural.Decimal.toPeano_eq_of_equivalent hlenP).trans
      CardinalNatural.Decimal.toPeano_one
  have hlenQ' :
      Peano.Progressions.FiniteArithmeticIncreasing.getLength (toPeano q) =
        CardinalNatural.Peano.one := by
    rw [← getLength_toPeano]
    exact (CardinalNatural.Decimal.toPeano_eq_of_equivalent hlenQ).trans
      CardinalNatural.Decimal.toPeano_one
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
    exact CardinalNatural.Decimal.toPeano_eq_of_equivalent hlen
  exact (equivalence_iff_toPeano p q).mpr
    (Peano.Progressions.FiniteArithmeticIncreasing.equivalence_of_same_params
      (toPeano p) (toPeano q) firstP.toPeano hp' hq' hdiff' hlen')

theorem effectiveFirst_rel_of_equivalence (p q : FiniteArithmeticIncreasing)
    (h : Equivalence p q) :
    Option.Rel (· ≈ ·) (effectiveFirst p) (effectiveFirst q) := by
  have h1 := h Peano.one
  simp only [Sequences.Progression.tryGetElement, ← effectiveFirst_eq] at h1
  exact h1

theorem getLength_equivalent_of_equivalence (p q : FiniteArithmeticIncreasing)
    (h : Equivalence p q) : getLength p ≈ getLength q := by
  have hpeano :=
    Peano.Progressions.FiniteArithmeticIncreasing.getLength_eq_of_equivalence
      (toPeano p) (toPeano q) ((equivalence_iff_toPeano p q).mp h)
  apply CardinalNatural.Decimal.equivalent_of_toPeano_eq
  rw [getLength_toPeano, getLength_toPeano, hpeano]

theorem commonDifference_equivalent_of_equivalence_of_length_ge_two
    (p q : FiniteArithmeticIncreasing) (firstP firstQ : Decimal)
    (hp : effectiveFirst p = some firstP) (hq : effectiveFirst q = some firstQ)
    (hfirst : firstP ≈ firstQ)
    (hne0 : ¬ getLength p ≈ CardinalNatural.Decimal.zero)
    (hne1 : ¬ getLength p ≈ CardinalNatural.Decimal.one)
    (hlen : getLength p ≈ getLength q) (h : Equivalence p q) :
    p.commonDifference ≈ q.commonDifference := by
  have h0 :
      Peano.Progressions.FiniteArithmeticIncreasing.getLength (toPeano p) ≠
        CardinalNatural.Peano.zero := by
    intro hz
    apply hne0
    apply CardinalNatural.Decimal.equivalent_of_toPeano_eq
    rw [getLength_toPeano, hz, CardinalNatural.Decimal.toPeano_zero]
  have h1 :
      Peano.Progressions.FiniteArithmeticIncreasing.getLength (toPeano p) ≠
        CardinalNatural.Peano.one := by
    intro hone
    apply hne1
    apply CardinalNatural.Decimal.equivalent_of_toPeano_eq
    rw [getLength_toPeano, hone, CardinalNatural.Decimal.toPeano_one]
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
    exact CardinalNatural.Decimal.toPeano_eq_of_equivalent hlen
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
    if hZ : lenP ≈ CardinalNatural.Decimal.zero then
      isTrue (equivalence_of_length_zero p q hZ (Setoid.trans (Setoid.symm hL) hZ))
    else if hF : Option.Rel (· ≈ ·) (effectiveFirst p) (effectiveFirst q) then
      if hOne : lenP ≈ CardinalNatural.Decimal.one then
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
theorem sizeOf_cardinal_peano_predecessor_lt (n : CardinalNatural.Peano)
    (hne : n ≠ CardinalNatural.Peano.zero) :
    sizeOf (n.predecessor hne) < sizeOf n := by
  cases n with
  | zero => exact False.elim (hne rfl)
  | successor n =>
    have hpred : (CardinalNatural.Peano.successor n).predecessor hne = n := rfl
    rw [hpred]
    exact Nat.lt_add_of_pos_left (k := 1) Nat.zero_lt_one

/-- Elements from a known start for the given remaining length, advancing by the
common difference with no limit comparisons. -/
def getElementsFrom (first commonDifference : Decimal) :
    CardinalNatural.Decimal → Sequences.List Decimal
  | n =>
    if h : n ≈ CardinalNatural.Decimal.zero then
      .empty
    else
      .firstElement first
        (getElementsFrom (first + commonDifference) commonDifference
          (n.predecessor h))
termination_by n => n.toPeano
decreasing_by
  obtain ⟨hne, heq⟩ := CardinalNatural.Decimal.predecessor_toPeano n h
  rw [heq]
  exact sizeOf_cardinal_peano_predecessor_lt _ hne

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
    CardinalNatural.Peano.two ≤ elements.length →
    Option FiniteArithmeticIncreasing
  | .empty, hge =>
    False.elim (CardinalNatural.Peano.not_two_le_zero (by
      change CardinalNatural.Peano.two ≤ CardinalNatural.Peano.zero
      exact hge))
  | .firstElement _ .empty, hge =>
    False.elim (CardinalNatural.Peano.not_two_le_one (by
      change CardinalNatural.Peano.two ≤ CardinalNatural.Peano.one
      exact hge))
  | .firstElement x (.firstElement y ys), _ =>
    match trySubtract y x with
    | none => none
    | some diff =>
      match tryLastOfArithmeticContinuation y diff ys with
      | none => none
      | some last =>
        some { first := some x, commonDifference := diff, limit := last }

/-- A cardinal Decimal whose Peano embedding is nonzero is not equivalent to
zero. -/
theorem not_equivalent_zero_of_toPeano_ne_zero (n : CardinalNatural.Decimal)
    (hne : n.toPeano ≠ CardinalNatural.Peano.zero) :
    ¬ n ≈ CardinalNatural.Decimal.zero := by
  intro heq
  exact hne ((CardinalNatural.Decimal.toPeano_eq_of_equivalent heq).trans
    CardinalNatural.Decimal.toPeano_zero)

/-- Last element of a non-empty arithmetic walk of cardinal length `n`, starting
at `first` with common difference `commonDifference`. Defined via the Peano
embedding so that length and order facts transport directly. For `n ≈ zero` the
value is unused (`fromPeano` of the Peano placeholder). -/
def lastElementFrom (first commonDifference : Decimal)
    (n : CardinalNatural.Decimal) : Decimal :=
  fromPeano
    (Peano.Progressions.FiniteArithmeticIncreasing.lastElementFrom
      first.toPeano commonDifference.toPeano n.toPeano)

/-- `lastElementFrom` agrees with the Peano embedding on the nose. -/
theorem lastElementFrom_toPeano (first commonDifference : Decimal)
    (n : CardinalNatural.Decimal) :
    (lastElementFrom first commonDifference n).toPeano =
      Peano.Progressions.FiniteArithmeticIncreasing.lastElementFrom
        first.toPeano commonDifference.toPeano n.toPeano := by
  simpa [lastElementFrom] using toPeano_fromPeano
    (Peano.Progressions.FiniteArithmeticIncreasing.lastElementFrom
      first.toPeano commonDifference.toPeano n.toPeano)

/-- `x < x + y` for Decimal addition. -/
theorem lt_add_left (x y : Decimal) : x < x + y := by
  have h := lt_add_right y x
  rwa [add_commutative y x] at h

/-- `getElementsFrom` produces a list whose length equals the Peano embedding of
the length argument. -/
theorem getElementsFrom_length (first commonDifference : Decimal)
    (n : CardinalNatural.Decimal) :
    (getElementsFrom first commonDifference n).length = n.toPeano := by
  have hgen :
      ∀ k : CardinalNatural.Peano, ∀ (first : Decimal) (n : CardinalNatural.Decimal),
        n.toPeano = k →
          (getElementsFrom first commonDifference n).length = k := by
    intro k
    induction k with
    | zero =>
      intro first n hn
      have hz : n ≈ CardinalNatural.Decimal.zero :=
        CardinalNatural.Decimal.equivalent_of_toPeano_eq
          (hn.trans CardinalNatural.Decimal.toPeano_zero.symm)
      have hexpand :
          getElementsFrom first commonDifference n = Sequences.List.empty := by
        conv => lhs; unfold getElementsFrom
        simp only [hz, ↓reduceDIte]
      rw [hexpand, Sequences.List.length]
    | successor k ih =>
      intro first n hn
      have hne0 : n.toPeano ≠ CardinalNatural.Peano.zero := by
        rw [hn]
        exact CardinalNatural.Peano.successor_ne_zero k
      have hne : ¬ n ≈ CardinalNatural.Decimal.zero :=
        not_equivalent_zero_of_toPeano_ne_zero n hne0
      obtain ⟨hne_peano, hpred⟩ :=
        CardinalNatural.Decimal.predecessor_toPeano n hne
      have hpred_k : (n.predecessor hne).toPeano = k := by
        rw [hpred]
        apply Eq.symm
        apply CardinalNatural.Peano.successor_injective
        rw [CardinalNatural.Peano.successor_predecessor n.toPeano hne_peano, hn]
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
    (n : CardinalNatural.Decimal)
    (hge : CardinalNatural.Peano.two ≤ n.toPeano) :
    CardinalNatural.Peano.two ≤
      (getElementsFrom first commonDifference n).length := by
  rw [getElementsFrom_length]
  exact hge

/-- Expanding `getElementsFrom` at length at least two. -/
theorem getElementsFrom_of_two_le (first commonDifference : Decimal)
    (n : CardinalNatural.Decimal)
    (hge : CardinalNatural.Peano.two ≤ n.toPeano) :
    ∃ (hne : ¬ n ≈ CardinalNatural.Decimal.zero)
      (hne' : ¬ n.predecessor hne ≈ CardinalNatural.Decimal.zero),
      getElementsFrom first commonDifference n =
        Sequences.List.firstElement first
          (Sequences.List.firstElement (first + commonDifference)
            (getElementsFrom (first + commonDifference + commonDifference)
              commonDifference
              ((n.predecessor hne).predecessor hne'))) := by
  have hne0 : n.toPeano ≠ CardinalNatural.Peano.zero := by
    intro heq
    rw [heq] at hge
    exact CardinalNatural.Peano.not_two_le_zero hge
  have hne : ¬ n ≈ CardinalNatural.Decimal.zero :=
    not_equivalent_zero_of_toPeano_ne_zero n hne0
  obtain ⟨hne_peano, hpred⟩ := CardinalNatural.Decimal.predecessor_toPeano n hne
  have hne1 : (n.predecessor hne).toPeano ≠ CardinalNatural.Peano.zero := by
    intro heq
    have hn_one : n.toPeano = CardinalNatural.Peano.one := by
      have hsucc :=
        CardinalNatural.Peano.successor_predecessor n.toPeano hne_peano
      rw [← hsucc, ← hpred, heq]
      rfl
    rw [hn_one] at hge
    exact CardinalNatural.Peano.not_two_le_one hge
  have hne' : ¬ n.predecessor hne ≈ CardinalNatural.Decimal.zero :=
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
  InfiniteArithmetic.trySubtract_of_equivalent_add (Setoid.refl (x + d))

/-- Helper: predecessor Peano embedding equals `k` when `n.toPeano = successor k`. -/
theorem predecessor_toPeano_eq_of_succ (n : CardinalNatural.Decimal)
    (hne : ¬ n ≈ CardinalNatural.Decimal.zero) (k : CardinalNatural.Peano)
    (hn : n.toPeano = CardinalNatural.Peano.successor k)
    (hne_peano : n.toPeano ≠ CardinalNatural.Peano.zero)
    (hpred : (n.predecessor hne).toPeano = n.toPeano.predecessor hne_peano) :
    (n.predecessor hne).toPeano = k := by
  rw [hpred]
  apply Eq.symm
  apply CardinalNatural.Peano.successor_injective
  rw [CardinalNatural.Peano.successor_predecessor n.toPeano hne_peano, hn]

/-- Continuing an arithmetic walk from `prev` by `getElementsFrom` recovers a
last element equivalent to `lastElementFrom`. -/
theorem tryLastOfArithmeticContinuation_getElementsFrom
    (prev commonDifference diff : Decimal) (n : CardinalNatural.Decimal)
    (hd : diff ≈ commonDifference) :
    Option.Rel (· ≈ ·)
      (tryLastOfArithmeticContinuation prev diff
        (getElementsFrom (prev + commonDifference) commonDifference n))
      (some (lastElementFrom prev commonDifference n.successor)) := by
  have hgen :
      ∀ k : CardinalNatural.Peano, ∀ (prev : Decimal) (n : CardinalNatural.Decimal),
        n.toPeano = k →
          Option.Rel (· ≈ ·)
            (tryLastOfArithmeticContinuation prev diff
              (getElementsFrom (prev + commonDifference) commonDifference n))
            (some (lastElementFrom prev commonDifference n.successor)) := by
    intro k
    induction k with
    | zero =>
      intro prev n hn
      have hz : n ≈ CardinalNatural.Decimal.zero :=
        CardinalNatural.Decimal.equivalent_of_toPeano_eq
          (hn.trans CardinalNatural.Decimal.toPeano_zero.symm)
      have hexpand :
          getElementsFrom (prev + commonDifference) commonDifference n =
            Sequences.List.empty := by
        conv => lhs; unfold getElementsFrom
        simp only [hz, ↓reduceDIte]
      rw [hexpand, tryLastOfArithmeticContinuation]
      apply Option.Rel.some
      apply equivalent_of_toPeano_eq
      rw [lastElementFrom_toPeano, CardinalNatural.Decimal.successor_toPeano, hn]
      change prev.toPeano =
        Peano.Progressions.FiniteArithmeticIncreasing.lastElementFrom
          prev.toPeano commonDifference.toPeano
          (CardinalNatural.Peano.successor CardinalNatural.Peano.zero)
      rfl
    | successor k ih =>
      intro prev n hn
      have hne0 : n.toPeano ≠ CardinalNatural.Peano.zero := by
        rw [hn]
        exact CardinalNatural.Peano.successor_ne_zero k
      have hne : ¬ n ≈ CardinalNatural.Decimal.zero :=
        not_equivalent_zero_of_toPeano_ne_zero n hne0
      obtain ⟨hne_peano, hpred⟩ :=
        CardinalNatural.Decimal.predecessor_toPeano n hne
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
        CardinalNatural.Decimal.successor_toPeano,
        CardinalNatural.Decimal.successor_toPeano, hpred_k, hn]
      exact
        (Peano.Progressions.FiniteArithmeticIncreasing.lastElementFrom_succ_succ
          prev.toPeano commonDifference.toPeano k).symm
  exact hgen n.toPeano prev n rfl

/-- Reconstructing from `getElementsFrom` of Peano-length at least two recovers
a progression with the same start, an equivalent common difference, and a limit
equivalent to `lastElementFrom`. -/
theorem tryFromElements_getElementsFrom_ge_two (first commonDifference : Decimal)
    (n : CardinalNatural.Decimal)
    (hge : CardinalNatural.Peano.two ≤ n.toPeano)
    (hLen : CardinalNatural.Peano.two ≤
        (getElementsFrom first commonDifference n).length :=
      getElementsFrom_ge_two_length first commonDifference n hge) :
    ∃ (q : FiniteArithmeticIncreasing),
      tryFromElements (getElementsFrom first commonDifference n) hLen = some q ∧
        q.first = some first ∧
        q.commonDifference ≈ commonDifference ∧
        q.limit ≈ lastElementFrom first commonDifference n := by
  obtain ⟨hne, hne', hget⟩ := getElementsFrom_of_two_le first commonDifference n hge
  obtain ⟨hne_peano, hpred⟩ := CardinalNatural.Decimal.predecessor_toPeano n hne
  obtain ⟨hne_peano', hpred'⟩ :=
    CardinalNatural.Decimal.predecessor_toPeano (n.predecessor hne) hne'
  revert hLen
  rw [hget]
  intro hLen
  simp only [tryFromElements]
  have hrel := trySubtract_self_add first commonDifference
  obtain ⟨diff, hdiff_eq, hdiff_approx⟩ :=
    InfiniteArithmetic.exists_of_option_rel_some hrel
  simp only [hdiff_eq]
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
    } : FiniteArithmeticIncreasing), rfl, rfl, hdiff_approx, ?_⟩
  refine Setoid.trans hlast_approx ?_
  apply equivalent_of_toPeano_eq
  rw [lastElementFrom_toPeano, lastElementFrom_toPeano, add_toPeano,
    CardinalNatural.Decimal.successor_toPeano]
  have hn_shape :
      n.toPeano =
        CardinalNatural.Peano.successor
          (CardinalNatural.Peano.successor
            ((n.predecessor hne).predecessor hne').toPeano) := by
    have h1 :=
      CardinalNatural.Peano.successor_predecessor n.toPeano hne_peano
    have h2 :=
      CardinalNatural.Peano.successor_predecessor (n.predecessor hne).toPeano
        hne_peano'
    -- n.toPeano = succ (pred n.toPeano)
    rw [← h1]
    apply congrArg CardinalNatural.Peano.successor
    -- pred n.toPeano = (n.predecessor).toPeano
    rw [← hpred]
    -- (n.predecessor).toPeano = succ (pred (n.predecessor).toPeano)
    rw [← h2]
    apply congrArg CardinalNatural.Peano.successor
    exact hpred'.symm
  rw [hn_shape]
  exact
    (Peano.Progressions.FiniteArithmeticIncreasing.lastElementFrom_succ_succ
      first.toPeano commonDifference.toPeano
      ((n.predecessor hne).predecessor hne').toPeano).symm

/-- Length of a progression whose limit is equivalent to `lastElementFrom` of
its positive length, with an equivalent common difference. -/
theorem getLength_of_equivalent_lastElementFrom (first commonDifference diff last :
    Decimal) (n : CardinalNatural.Decimal)
    (hne : ¬ n ≈ CardinalNatural.Decimal.zero)
    (hd : diff ≈ commonDifference)
    (hl : last ≈ lastElementFrom first commonDifference n) :
    getLength {
      first := some first
      commonDifference := diff
      limit := last
    } ≈ n := by
  apply CardinalNatural.Decimal.equivalent_of_toPeano_eq
  have hstruct :
      toPeano {
        first := some first
        commonDifference := diff
        limit := last
      } =
        {
          first := some first.toPeano
          commonDifference := diff.toPeano
          limit := last.toPeano
        } := by
    simp only [toPeano]
  rw [getLength_toPeano, hstruct]
  have hlim :
      last.toPeano =
        Peano.Progressions.FiniteArithmeticIncreasing.lastElementFrom
          first.toPeano commonDifference.toPeano n.toPeano := by
    rw [toPeano_eq_of_equivalent hl, lastElementFrom_toPeano]
  have hdiff : diff.toPeano = commonDifference.toPeano :=
    toPeano_eq_of_equivalent hd
  rw [hlim, hdiff]
  exact
    Peano.Progressions.FiniteArithmeticIncreasing.getLength_lastElementFrom
      first.toPeano commonDifference.toPeano n.toPeano
      (CardinalNatural.Decimal.toPeano_ne_zero_of_not_equivalent_zero hne)

/-- When the limit is equivalent to `lastElementFrom` of a positive length, the
effective first element is `some first`. -/
theorem effectiveFirst_of_equivalent_lastElementFrom (first commonDifference diff
    last : Decimal) (n : CardinalNatural.Decimal)
    (hne : ¬ n ≈ CardinalNatural.Decimal.zero)
    (hl : last ≈ lastElementFrom first commonDifference n) :
    effectiveFirst {
      first := some first
      commonDifference := diff
      limit := last
    } = some first := by
  simp only [effectiveFirst]
  have hle_peano :
      first.toPeano ≤
        Peano.Progressions.FiniteArithmeticIncreasing.lastElementFrom
          first.toPeano commonDifference.toPeano n.toPeano :=
    Peano.Progressions.FiniteArithmeticIncreasing.first_le_lastElementFrom_of_pos
      first.toPeano commonDifference.toPeano n.toPeano
      (CardinalNatural.Decimal.toPeano_ne_zero_of_not_equivalent_zero hne)
  have hle : first ≤ last := by
    apply (le_iff_toPeano_le first last).mpr
    rw [toPeano_eq_of_equivalent hl, lastElementFrom_toPeano]
    exact hle_peano
  simp only [hle, ↓reduceIte]

/-- `tryFromElements` recovers a progression equivalent to `p` from
`getElements p` when `p` has length at least two. -/
theorem tryFromElements_getElements (p : FiniteArithmeticIncreasing)
    (hge : CardinalNatural.Peano.two ≤ (getLength p).toPeano) :
    ∃ (hLen : CardinalNatural.Peano.two ≤ (getElements p).length)
      (q : FiniteArithmeticIncreasing),
      tryFromElements (getElements p) hLen = some q ∧ p ≈ q := by
  have hne0 : (getLength p).toPeano ≠ CardinalNatural.Peano.zero := by
    intro heq
    rw [heq] at hge
    exact CardinalNatural.Peano.not_two_le_zero hge
  have hne0' : ¬ getLength p ≈ CardinalNatural.Decimal.zero :=
    not_equivalent_zero_of_toPeano_ne_zero (getLength p) hne0
  obtain ⟨first, hf⟩ := effectiveFirst_eq_some_of_pos_length p hne0'
  have hget :
      getElements p =
        getElementsFrom first p.commonDifference (getLength p) := by
    simp only [getElements, hf]
  have hLen : CardinalNatural.Peano.two ≤ (getElements p).length := by
    rw [hget, getElementsFrom_length]
    exact hge
  have hLen' : CardinalNatural.Peano.two ≤
      (getElementsFrom first p.commonDifference (getLength p)).length := by
    rw [getElementsFrom_length]
    exact hge
  obtain ⟨q, htry, hfirst_q, hdiff_q, hlast_q⟩ :=
    tryFromElements_getElementsFrom_ge_two first p.commonDifference
      (getLength p) hge hLen'
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
        } := by
      cases q with
      | mk f d l =>
        cases hfirst_q
        rfl
    have hf_q :
        effectiveFirst q = some first := by
      rw [hq_rewrite]
      exact effectiveFirst_of_equivalent_lastElementFrom first
        p.commonDifference q.commonDifference q.limit (getLength p) hne0'
        hlast_q
    have hlen_q :
        getLength q ≈ getLength p := by
      rw [hq_rewrite]
      exact getLength_of_equivalent_lastElementFrom first p.commonDifference
        q.commonDifference q.limit (getLength p) hne0' hdiff_q hlast_q
    exact equivalence_of_equivalent_params p q first first hf hf_q
      (Setoid.refl first) (Setoid.symm hdiff_q) (Setoid.symm hlen_q)

/-- A successful subtraction `trySubtract y x = some d` means `y ≈ x + d`. -/
theorem equivalent_of_trySubtract_add (x y d : Decimal)
    (h : trySubtract y x = some d) : y ≈ x + d := by
  obtain ⟨hlt, hsub⟩ := exists_subtract_of_trySubtract h
  have hsum := subtract_add_cancel y x hlt
  rw [hsub] at hsum
  exact Setoid.trans (Setoid.symm hsum) (add_commutative d x ▸ Setoid.refl _)

/-- `getElementsFrom` depends on the length argument only through its Peano
embedding. -/
theorem getElementsFrom_eq_of_toPeano_eq (first commonDifference : Decimal)
    (n m : CardinalNatural.Decimal) (h : n.toPeano = m.toPeano) :
    getElementsFrom first commonDifference n =
      getElementsFrom first commonDifference m := by
  have hgen :
      ∀ k : CardinalNatural.Peano, ∀ (first : Decimal)
        (n m : CardinalNatural.Decimal),
        n.toPeano = k → m.toPeano = k →
          getElementsFrom first commonDifference n =
            getElementsFrom first commonDifference m := by
    intro k
    induction k with
    | zero =>
      intro first n m hn hm
      have hnz : n ≈ CardinalNatural.Decimal.zero :=
        CardinalNatural.Decimal.equivalent_of_toPeano_eq
          (hn.trans CardinalNatural.Decimal.toPeano_zero.symm)
      have hmz : m ≈ CardinalNatural.Decimal.zero :=
        CardinalNatural.Decimal.equivalent_of_toPeano_eq
          (hm.trans CardinalNatural.Decimal.toPeano_zero.symm)
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
      have hne0 : n.toPeano ≠ CardinalNatural.Peano.zero := by
        rw [hn]
        exact CardinalNatural.Peano.successor_ne_zero k
      have hme0 : m.toPeano ≠ CardinalNatural.Peano.zero := by
        rw [hm]
        exact CardinalNatural.Peano.successor_ne_zero k
      have hne : ¬ n ≈ CardinalNatural.Decimal.zero :=
        not_equivalent_zero_of_toPeano_ne_zero n hne0
      have hme : ¬ m ≈ CardinalNatural.Decimal.zero :=
        not_equivalent_zero_of_toPeano_ne_zero m hme0
      obtain ⟨hne_peano, hpred_n⟩ :=
        CardinalNatural.Decimal.predecessor_toPeano n hne
      obtain ⟨hme_peano, hpred_m⟩ :=
        CardinalNatural.Decimal.predecessor_toPeano m hme
      have hpred_n_k : (n.predecessor hne).toPeano = k := by
        rw [hpred_n]
        apply Eq.symm
        apply CardinalNatural.Peano.successor_injective
        rw [CardinalNatural.Peano.successor_predecessor n.toPeano hne_peano, hn]
      have hpred_m_k : (m.predecessor hme).toPeano = k := by
        rw [hpred_m]
        apply Eq.symm
        apply CardinalNatural.Peano.successor_injective
        rw [CardinalNatural.Peano.successor_predecessor m.toPeano hme_peano, hm]
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
    Decimal) (n : CardinalNatural.Decimal) (h : first ≈ first') :
    Sequences.List.SameLengthElementwiseRelation (· ≈ ·)
      (getElementsFrom first commonDifference n)
      (getElementsFrom first' commonDifference n) := by
  have hgen :
      ∀ k : CardinalNatural.Peano, ∀ (first first' : Decimal)
        (n : CardinalNatural.Decimal),
        n.toPeano = k → first ≈ first' →
          Sequences.List.SameLengthElementwiseRelation (· ≈ ·)
            (getElementsFrom first commonDifference n)
            (getElementsFrom first' commonDifference n) := by
    intro k
    induction k with
    | zero =>
      intro first first' n hn _hfirst
      have hz : n ≈ CardinalNatural.Decimal.zero :=
        CardinalNatural.Decimal.equivalent_of_toPeano_eq
          (hn.trans CardinalNatural.Decimal.toPeano_zero.symm)
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
      have hne0 : n.toPeano ≠ CardinalNatural.Peano.zero := by
        rw [hn]
        exact CardinalNatural.Peano.successor_ne_zero k
      have hne : ¬ n ≈ CardinalNatural.Decimal.zero :=
        not_equivalent_zero_of_toPeano_ne_zero n hne0
      obtain ⟨hne_peano, hpred⟩ :=
        CardinalNatural.Decimal.predecessor_toPeano n hne
      have hpred_k : (n.predecessor hne).toPeano = k := by
        rw [hpred]
        apply Eq.symm
        apply CardinalNatural.Peano.successor_injective
        rw [CardinalNatural.Peano.successor_predecessor n.toPeano hne_peano, hn]
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
    (n : CardinalNatural.Decimal) (k : CardinalNatural.Peano)
    (hn : n.toPeano = CardinalNatural.Peano.successor k) :
    ∃ (hne : ¬ n ≈ CardinalNatural.Decimal.zero),
      getElementsFrom first commonDifference n =
        Sequences.List.firstElement first
          (getElementsFrom (first + commonDifference) commonDifference
            (n.predecessor hne)) ∧
      (n.predecessor hne).toPeano = k := by
  have hne0 : n.toPeano ≠ CardinalNatural.Peano.zero := by
    rw [hn]
    exact CardinalNatural.Peano.successor_ne_zero k
  have hne : ¬ n ≈ CardinalNatural.Decimal.zero :=
    not_equivalent_zero_of_toPeano_ne_zero n hne0
  obtain ⟨hne_peano, hpred⟩ := CardinalNatural.Decimal.predecessor_toPeano n hne
  refine ⟨hne, ?_, ?_⟩
  · conv => lhs; unfold getElementsFrom
    simp only [hne, ↓reduceDIte]
  · rw [hpred]
    apply Eq.symm
    apply CardinalNatural.Peano.successor_injective
    rw [CardinalNatural.Peano.successor_predecessor n.toPeano hne_peano, hn]

/-- If a list continues arithmetically after `prev`, it is pointwise equivalent
to the corresponding `getElementsFrom` walk, and the recovered last element is
equivalent to `lastElementFrom`. -/
theorem rel_getElementsFrom_of_tryLastOfArithmeticContinuation
    (prev diff : Decimal) (rest : Sequences.List Decimal) (last : Decimal)
    (h : tryLastOfArithmeticContinuation prev diff rest = some last) :
    Sequences.List.SameLengthElementwiseRelation (· ≈ ·)
        (getElementsFrom (prev + diff) diff
          (CardinalNatural.Decimal.fromPeano rest.length))
        rest ∧
      last ≈
        lastElementFrom prev diff
          (CardinalNatural.Decimal.fromPeano rest.length).successor := by
  induction rest generalizing prev last with
  | empty =>
    simp only [tryLastOfArithmeticContinuation] at h
    injection h with heq
    constructor
    · have hz :
          CardinalNatural.Decimal.fromPeano
              (CardinalNatural.Peano.zero) ≈
            CardinalNatural.Decimal.zero :=
        CardinalNatural.Decimal.equivalent_of_toPeano_eq
          ((CardinalNatural.Decimal.toPeano_fromPeano
              CardinalNatural.Peano.zero).trans
            CardinalNatural.Decimal.toPeano_zero.symm)
      have hexpand :
          getElementsFrom (prev + diff) diff
              (CardinalNatural.Decimal.fromPeano CardinalNatural.Peano.zero) =
            Sequences.List.empty := by
        conv => lhs; unfold getElementsFrom
        simp only [hz, ↓reduceDIte]
      change Sequences.List.SameLengthElementwiseRelation (· ≈ ·)
        (getElementsFrom (prev + diff) diff
          (CardinalNatural.Decimal.fromPeano
            (Sequences.List.empty : Sequences.List Decimal).length))
        Sequences.List.empty
      rw [show (Sequences.List.empty : Sequences.List Decimal).length =
          CardinalNatural.Peano.zero from rfl, hexpand]
      exact Sequences.List.SameLengthElementwiseRelation.empty
    · subst heq
      apply equivalent_of_toPeano_eq
      rw [lastElementFrom_toPeano, CardinalNatural.Decimal.successor_toPeano,
        CardinalNatural.Decimal.toPeano_fromPeano]
      change prev.toPeano =
        Peano.Progressions.FiniteArithmeticIncreasing.lastElementFrom
          prev.toPeano diff.toPeano CardinalNatural.Peano.one
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
          Setoid.trans (equivalent_of_trySubtract_add prev x d hs)
            (equivalent_add (Setoid.refl prev) hd)
        have hlen := Sequences.List.length_firstElement x xs
        constructor
        · have hn :
              (CardinalNatural.Decimal.fromPeano
                  (Sequences.List.firstElement x xs).length).toPeano =
                CardinalNatural.Peano.successor xs.length := by
            rw [CardinalNatural.Decimal.toPeano_fromPeano, hlen]
          obtain ⟨hne, hexpand, hpred⟩ :=
            getElementsFrom_of_toPeano_successor (prev + diff) diff
              (CardinalNatural.Decimal.fromPeano
                (Sequences.List.firstElement x xs).length)
              xs.length hn
          have hpred_eq :
              getElementsFrom (prev + diff + diff) diff
                  ((CardinalNatural.Decimal.fromPeano
                      (Sequences.List.firstElement x xs).length).predecessor
                    hne) =
                getElementsFrom (prev + diff + diff) diff
                  (CardinalNatural.Decimal.fromPeano xs.length) :=
            getElementsFrom_eq_of_toPeano_eq (prev + diff + diff) diff _ _
              (hpred.trans (CardinalNatural.Decimal.toPeano_fromPeano _).symm)
          have hstart : prev + diff + diff ≈ x + diff :=
            equivalent_add (Setoid.symm hx) (Setoid.refl diff)
          have hmid :
              Sequences.List.SameLengthElementwiseRelation (· ≈ ·)
                (getElementsFrom (prev + diff + diff) diff
                  (CardinalNatural.Decimal.fromPeano xs.length))
                (getElementsFrom (x + diff) diff
                  (CardinalNatural.Decimal.fromPeano xs.length)) :=
            getElementsFrom_rel_of_equivalent_first (prev + diff + diff)
              (x + diff) diff (CardinalNatural.Decimal.fromPeano xs.length)
              hstart
          have htail :
              Sequences.List.SameLengthElementwiseRelation (· ≈ ·)
                (getElementsFrom (prev + diff + diff) diff
                  (CardinalNatural.Decimal.fromPeano xs.length))
                xs :=
            Sequences.List.SameLengthElementwiseRelation.trans
              (r := (· ≈ ·)) (s := (· ≈ ·)) (t := (· ≈ ·))
              (fun h1 h2 => Setoid.trans h1 h2) hmid hxs
          rw [hexpand, hpred_eq]
          exact Sequences.List.SameLengthElementwiseRelation.firstElement (Setoid.symm hx) htail
        · have h1 :
              last ≈
                lastElementFrom (prev + diff) diff
                  (CardinalNatural.Decimal.fromPeano xs.length).successor := by
            refine Setoid.trans hlast ?_
            apply equivalent_of_toPeano_eq
            rw [lastElementFrom_toPeano, lastElementFrom_toPeano,
              toPeano_eq_of_equivalent hx]
          have h2 :
              lastElementFrom (prev + diff) diff
                  (CardinalNatural.Decimal.fromPeano xs.length).successor ≈
                lastElementFrom prev diff
                  (CardinalNatural.Decimal.fromPeano
                    (Sequences.List.firstElement x xs).length).successor := by
            apply equivalent_of_toPeano_eq
            rw [lastElementFrom_toPeano, lastElementFrom_toPeano, add_toPeano,
              CardinalNatural.Decimal.successor_toPeano,
              CardinalNatural.Decimal.successor_toPeano,
              CardinalNatural.Decimal.toPeano_fromPeano,
              CardinalNatural.Decimal.toPeano_fromPeano, hlen]
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
    (hge : CardinalNatural.Peano.two ≤ elements.length)
    (p : FiniteArithmeticIncreasing)
    (h : tryFromElements elements hge = some p) :
    Sequences.List.SameLengthElementwiseRelation (· ≈ ·) (getElements p) elements := by
  match helem : elements with
  | .empty =>
    subst helem
    exact (CardinalNatural.Peano.not_two_le_zero (by
      change CardinalNatural.Peano.two ≤ CardinalNatural.Peano.zero
      exact hge)).elim
  | .firstElement _ .empty =>
    subst helem
    exact (CardinalNatural.Peano.not_two_le_one (by
      change CardinalNatural.Peano.two ≤ CardinalNatural.Peano.one
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
        let n : CardinalNatural.Decimal :=
          (CardinalNatural.Decimal.fromPeano
            (Sequences.List.firstElement y ys).length).successor
        have hne : ¬ n ≈ CardinalNatural.Decimal.zero := by
          intro heq
          have hpeano := CardinalNatural.Decimal.toPeano_eq_of_equivalent heq
          rw [CardinalNatural.Decimal.successor_toPeano,
            CardinalNatural.Decimal.toPeano_fromPeano,
            CardinalNatural.Decimal.toPeano_zero] at hpeano
          exact CardinalNatural.Peano.successor_ne_zero _ hpeano
        have hf : effectiveFirst
            {
              first := some x
              commonDifference := diff
              limit := last
            } = some x :=
          effectiveFirst_of_equivalent_lastElementFrom x diff diff last n hne
            hlast
        have hlenp :
            getLength
                {
                  first := some x
                  commonDifference := diff
                  limit := last
                } ≈ n :=
          getLength_of_equivalent_lastElementFrom x diff diff last n hne
            (Setoid.refl diff) hlast
        have hget :
            getElements
                {
                  first := some x
                  commonDifference := diff
                  limit := last
                } =
              getElementsFrom x diff
                (getLength
                  {
                    first := some x
                    commonDifference := diff
                    limit := last
                  }) := by
          simp only [getElements, hf]
        rw [hget]
        have hlen_toPeano :
            (getLength
                {
                  first := some x
                  commonDifference := diff
                  limit := last
                }).toPeano =
              n.toPeano :=
          CardinalNatural.Decimal.toPeano_eq_of_equivalent hlenp
        have hget' :
            getElementsFrom x diff
                (getLength
                  {
                    first := some x
                    commonDifference := diff
                    limit := last
                  }) =
              getElementsFrom x diff n :=
          getElementsFrom_eq_of_toPeano_eq x diff _ _ hlen_toPeano
        rw [hget']
        have hn :
            n.toPeano =
              CardinalNatural.Peano.successor
                (Sequences.List.firstElement y ys).length := by
          rw [CardinalNatural.Decimal.successor_toPeano,
            CardinalNatural.Decimal.toPeano_fromPeano]
        obtain ⟨hne_n, hexpand, hpred⟩ :=
          getElementsFrom_of_toPeano_successor x diff n
            (Sequences.List.firstElement y ys).length hn
        have hpred_eq :
            getElementsFrom (x + diff) diff (n.predecessor hne_n) =
              getElementsFrom (x + diff) diff
                (CardinalNatural.Decimal.fromPeano
                  (Sequences.List.firstElement y ys).length) :=
          getElementsFrom_eq_of_toPeano_eq (x + diff) diff _ _
            (hpred.trans (CardinalNatural.Decimal.toPeano_fromPeano _).symm)
        rw [hexpand, hpred_eq]
        exact Sequences.List.SameLengthElementwiseRelation.firstElement (Setoid.refl x) hrest

/-- Recover the first element of an arithmetic progression from an element at the
given ordinal Decimal index and the common difference. When the index is
equivalent to `one` the element is itself the first; otherwise subtract
`(predecessor index) * commonDifference`. Returns `none` when that subtraction
is impossible in the Decimal numbers. -/
def tryFirstFromIndexedElement (index element commonDifference : Decimal) :
    Option Decimal :=
  if h : index ≈ one then
    some element
  else
    trySubtract element ((index.predecessor h) * commonDifference)

/-- Given two ordered indexed elements (`index < index'`) of a prospective
increasing arithmetic progression, recover the common difference
`(element' - element) / (index' - index)`. Returns `none` when the elements are
not strictly ascending or the element gap is not divisible by the index gap. -/
def tryCommonDifferenceFromOrderedIndexedElements
    (index element index' element' : Decimal) (hlt : index < index') :
    Option Decimal :=
  match trySubtract element' element with
  | none => none
  | some elementDiff =>
    tryDivide elementDiff (subtract index' index hlt)

/-- Reconstruct a finite increasing arithmetic progression from two of its
elements at different ordinal Decimal indexes together with the progression
length. Returns `none` when either index exceeds the length, or when the values
are not consistent with a strictly increasing arithmetic progression of that
length. Indexes are compared up to Decimal equivalence.

The reconstructed progression uses the recovered first element and common
difference, and takes the last element of an arithmetic walk of the given
length as the limit. -/
def tryFromTwoElementsAndLength
    (index1 : Decimal) (element1 : Decimal)
    (index2 : Decimal) (element2 : Decimal)
    (length : CardinalNatural.Decimal)
    (hne : ¬ index1 ≈ index2) :
    Option FiniteArithmeticIncreasing :=
  if CardinalNatural.Decimal.fromOrdinal index1 ≤ length then
    if CardinalNatural.Decimal.fromOrdinal index2 ≤ length then
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
              first := some first
              commonDifference := diff
              limit := lastElementFrom first diff length
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
              first := some first
              commonDifference := diff
              limit := lastElementFrom first diff length
            }
    else
      none
  else
    none

/-- Recovering the first element from an indexed element is left-inverse to
`getElementFrom` at that index, up to Decimal equivalence. -/
theorem getElementFrom_of_tryFirstFromIndexedElement
    (index element commonDifference first : Decimal)
    (h : tryFirstFromIndexedElement index element commonDifference = some first) :
    getElementFrom first commonDifference index ≈ element := by
  if hone : index ≈ one then
    simp only [tryFirstFromIndexedElement, hone, ↓reduceDIte] at h
    injection h with heq
    simp only [getElementFrom, hone, ↓reduceDIte, heq]
    exact Setoid.refl _
  else
    simp only [tryFirstFromIndexedElement, hone, ↓reduceDIte] at h
    have helement :
        element ≈
          (index.predecessor hone) * commonDifference + first :=
      equivalent_of_trySubtract_add
        ((index.predecessor hone) * commonDifference) element first h
    simp only [getElementFrom, hone, ↓reduceDIte]
    refine Setoid.trans ?_ (Setoid.symm helement)
    rw [add_commutative]
    exact Setoid.refl _

/-- Advancing from `index` to a larger `index'` adds
`(index' - index) * commonDifference` to the element, up to Decimal
equivalence. -/
theorem getElementFrom_add_mul_of_lt (first commonDifference index index' : Decimal)
    (hlt : index < index') :
    getElementFrom first commonDifference index' ≈
      getElementFrom first commonDifference index +
        (subtract index' index hlt) * commonDifference := by
  rw [getElementFrom_eq_InfiniteArithmetic_getElement,
    getElementFrom_eq_InfiniteArithmetic_getElement]
  exact InfiniteArithmetic.getElement_add_mul_of_lt
    { first := first, commonDifference := commonDifference } index index' hlt

/-- A successful common-difference recovery implies the larger element is
equivalent to the smaller plus the index gap times that difference. -/
theorem eq_add_mul_of_tryCommonDifferenceFromOrderedIndexedElements
    (index element index' element' : Decimal) (hlt : index < index')
    (diff : Decimal)
    (h : tryCommonDifferenceFromOrderedIndexedElements
        index element index' element' hlt = some diff) :
    element' ≈
      element + (subtract index' index hlt) * diff := by
  simp only [tryCommonDifferenceFromOrderedIndexedElements] at h
  match hs : trySubtract element' element with
  | none =>
    simp only [hs] at h
    nomatch h
  | some elementDiff =>
    simp only [hs] at h
    have hmul : elementDiff ≈ (subtract index' index hlt) * diff :=
      equivalent_of_tryDivide_mul elementDiff (subtract index' index hlt) diff h
    have hadd : element' ≈ element + elementDiff :=
      equivalent_of_trySubtract_add element element' elementDiff hs
    refine Setoid.trans hadd ?_
    apply equivalent_of_toPeano_eq
    rw [add_toPeano, add_toPeano, toPeano_eq_of_equivalent hmul]

/-- When both indexed recoveries succeed, `getElementFrom` recovers each original
element up to Decimal equivalence. -/
theorem getElementFrom_of_tryFirst_tryCommonDifference
    (index element index' element' : Decimal) (hlt : index < index')
    (diff first : Decimal)
    (hdiff : tryCommonDifferenceFromOrderedIndexedElements
        index element index' element' hlt = some diff)
    (hfirst : tryFirstFromIndexedElement index element diff = some first) :
    getElementFrom first diff index ≈ element ∧
      getElementFrom first diff index' ≈ element' := by
  have h1 :=
    getElementFrom_of_tryFirstFromIndexedElement index element diff first hfirst
  refine ⟨h1, ?_⟩
  have hgap :=
    eq_add_mul_of_tryCommonDifferenceFromOrderedIndexedElements
      index element index' element' hlt diff hdiff
  have hstep := getElementFrom_add_mul_of_lt first diff index index' hlt
  refine Setoid.trans hstep (Setoid.trans ?_ (Setoid.symm hgap))
  apply equivalent_of_toPeano_eq
  rw [add_toPeano, add_toPeano, toPeano_eq_of_equivalent h1]

/-- Length of a progression whose limit is exactly `lastElementFrom` of its
positive length. -/
theorem getLength_lastElementFrom (first commonDifference : Decimal)
    (n : CardinalNatural.Decimal) (hne : ¬ n ≈ CardinalNatural.Decimal.zero) :
    getLength {
      first := some first
      commonDifference := commonDifference
      limit := lastElementFrom first commonDifference n
    } ≈ n :=
  getLength_of_equivalent_lastElementFrom first commonDifference
    commonDifference (lastElementFrom first commonDifference n) n hne
    (Setoid.refl _) (Setoid.refl _)

/-- `getElement` on a progression whose limit is `lastElementFrom` of positive
length agrees with `getElementFrom`. -/
theorem getElement_lastElementFrom (first commonDifference : Decimal)
    (n : CardinalNatural.Decimal) (hne : ¬ n ≈ CardinalNatural.Decimal.zero)
    (index : Decimal)
    (hle : CardinalNatural.Decimal.fromOrdinal index ≤
      getLength {
        first := some first
        commonDifference := commonDifference
        limit := lastElementFrom first commonDifference n
      }) :
    getElement
      {
        first := some first
        commonDifference := commonDifference
        limit := lastElementFrom first commonDifference n
      }
      index hle =
      getElementFrom first commonDifference index := by
  have hle_first :
      first ≤ lastElementFrom first commonDifference n := by
    apply (le_iff_toPeano_le first _).mpr
    rw [lastElementFrom_toPeano]
    exact
      Peano.Progressions.FiniteArithmeticIncreasing.first_le_lastElementFrom_of_pos
        first.toPeano commonDifference.toPeano n.toPeano
        (CardinalNatural.Decimal.toPeano_ne_zero_of_not_equivalent_zero hne)
  dsimp only [getElement]
  match hcmp : compare first (lastElementFrom first commonDifference n) with
  | .greater hgt =>
    cases hle_first with
    | inl hlt =>
      exact (Peano.not_lt_of_lt (toPeano_lt_of_lt hgt) (toPeano_lt_of_lt hlt)).elim
    | inr heq =>
      have hself :
          (lastElementFrom first commonDifference n).toPeano <
            (lastElementFrom first commonDifference n).toPeano := by
        have hlt := toPeano_lt_of_lt hgt
        rwa [toPeano_eq_of_equivalent heq] at hlt
      exact (Peano.not_lt_self _ hself).elim
  | .equivalent _ =>
    rfl
  | .less _ =>
    rfl

theorem length_ne_zero_of_tryFromTwoElementsAndLength
    (index1 element1 index2 element2 : Decimal)
    (length : CardinalNatural.Decimal)
    (hne : ¬ index1 ≈ index2)
    (p : FiniteArithmeticIncreasing)
    (h : tryFromTwoElementsAndLength index1 element1 index2 element2 length hne =
      some p) :
    ¬ length ≈ CardinalNatural.Decimal.zero := by
  intro hzero
  simp only [tryFromTwoElementsAndLength] at h
  by_cases hle1 : CardinalNatural.Decimal.fromOrdinal index1 ≤ length
  · have :
        CardinalNatural.Decimal.fromOrdinal index1 ≤
          CardinalNatural.Decimal.zero :=
      CardinalNatural.Decimal.le_of_le_of_equivalent hle1 hzero
    exact CardinalNatural.Decimal.fromOrdinal_not_equivalent_zero index1
      (CardinalNatural.Decimal.eq_zero_of_le_zero _ this)
  · simp only [hle1, ↓reduceIte] at h
    nomatch h

/-- A successful `tryFromTwoElementsAndLength` yields a progression whose
`getLength` is equivalent to the given length and whose `getElement` at each of
the two indexes recovers a value equivalent to the corresponding original
element. -/
theorem getLength_getElement_of_tryFromTwoElementsAndLength
    (index1 element1 index2 element2 : Decimal)
    (length : CardinalNatural.Decimal)
    (hne : ¬ index1 ≈ index2)
    (p : FiniteArithmeticIncreasing)
    (h : tryFromTwoElementsAndLength index1 element1 index2 element2 length hne =
      some p) :
    getLength p ≈ length ∧
      (∃ (hle1 : CardinalNatural.Decimal.fromOrdinal index1 ≤ getLength p),
        getElement p index1 hle1 ≈ element1) ∧
      (∃ (hle2 : CardinalNatural.Decimal.fromOrdinal index2 ≤ getLength p),
        getElement p index2 hle2 ≈ element2) := by
  have hlen_ne :=
    length_ne_zero_of_tryFromTwoElementsAndLength
      index1 element1 index2 element2 length hne p h
  simp only [tryFromTwoElementsAndLength] at h
  by_cases hle1 : CardinalNatural.Decimal.fromOrdinal index1 ≤ length
  · simp only [hle1, ↓reduceIte] at h
    by_cases hle2 : CardinalNatural.Decimal.fromOrdinal index2 ≤ length
    · simp only [hle2, ↓reduceIte] at h
      match hc : compare index1 index2 with
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
            have hget :=
              getElementFrom_of_tryFirst_tryCommonDifference
                index1 element1 index2 element2 hlt diff first hd hf
            have hlenp := getLength_lastElementFrom first diff length hlen_ne
            have hle1p :
                CardinalNatural.Decimal.fromOrdinal index1 ≤
                  getLength {
                    first := some first
                    commonDifference := diff
                    limit := lastElementFrom first diff length
                  } :=
              CardinalNatural.Decimal.le_of_le_of_equivalent hle1 (Setoid.symm hlenp)
            have hle2p :
                CardinalNatural.Decimal.fromOrdinal index2 ≤
                  getLength {
                    first := some first
                    commonDifference := diff
                    limit := lastElementFrom first diff length
                  } :=
              CardinalNatural.Decimal.le_of_le_of_equivalent hle2 (Setoid.symm hlenp)
            refine ⟨hlenp, ⟨hle1p, ?_⟩, ⟨hle2p, ?_⟩⟩
            · exact
                (getElement_lastElementFrom first diff length hlen_ne
                  index1 hle1p) ▸ hget.1
            · exact
                (getElement_lastElementFrom first diff length hlen_ne
                  index2 hle2p) ▸ hget.2
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
              getElementFrom_of_tryFirst_tryCommonDifference
                index2 element2 index1 element1 hgt diff first hd hf
            have hlenp := getLength_lastElementFrom first diff length hlen_ne
            have hle1p :
                CardinalNatural.Decimal.fromOrdinal index1 ≤
                  getLength {
                    first := some first
                    commonDifference := diff
                    limit := lastElementFrom first diff length
                  } :=
              CardinalNatural.Decimal.le_of_le_of_equivalent hle1 (Setoid.symm hlenp)
            have hle2p :
                CardinalNatural.Decimal.fromOrdinal index2 ≤
                  getLength {
                    first := some first
                    commonDifference := diff
                    limit := lastElementFrom first diff length
                  } :=
              CardinalNatural.Decimal.le_of_le_of_equivalent hle2 (Setoid.symm hlenp)
            refine ⟨hlenp, ⟨hle1p, ?_⟩, ⟨hle2p, ?_⟩⟩
            · exact
                (getElement_lastElementFrom first diff length hlen_ne
                  index1 hle1p) ▸ hget.2
            · exact
                (getElement_lastElementFrom first diff length hlen_ne
                  index2 hle2p) ▸ hget.1
    · simp only [hle2, ↓reduceIte] at h
      nomatch h
  · simp only [hle1, ↓reduceIte] at h
    nomatch h

/-- In-range `getElement` agrees with `getElementFrom` on the effective first. -/
theorem getElement_eq_getElementFrom (p : FiniteArithmeticIncreasing)
    (start : Decimal) (hf : effectiveFirst p = some start) (index : Decimal)
    (hle : CardinalNatural.Decimal.fromOrdinal index ≤ getLength p) :
    getElement p index hle = getElementFrom start p.commonDifference index := by
  have hfirst_eq : p.first = some start := by
    match h : p.first with
    | none =>
      simp only [effectiveFirst, h] at hf
      nomatch hf
    | some start' =>
      simp only [effectiveFirst, h] at hf
      by_cases hle' : start' ≤ p.limit
      · simp only [hle', ↓reduceIte] at hf
        injection hf with heq
        exact congrArg some heq
      · simp only [hle', ↓reduceIte] at hf
        nomatch hf
  have hle_start : start ≤ p.limit := by
    simp only [effectiveFirst, hfirst_eq] at hf
    by_cases hle' : start ≤ p.limit
    · exact hle'
    · simp only [hle', ↓reduceIte] at hf
      nomatch hf
  dsimp only [getElement]
  split
  · next hf_none =>
    rw [hfirst_eq] at hf_none
    nomatch hf_none
  · next start' hf_some =>
    have heq : some start = some start' := hfirst_eq.symm.trans hf_some
    injection heq with heq'
    subst heq'
    match hcmp : compare start p.limit with
    | .greater hgt =>
      cases hle_start with
      | inl hlt =>
        exact (Peano.not_lt_of_lt (toPeano_lt_of_lt hgt) (toPeano_lt_of_lt hlt)).elim
      | inr heq =>
        have hself : p.limit.toPeano < p.limit.toPeano := by
          have hlt := toPeano_lt_of_lt hgt
          rwa [toPeano_eq_of_equivalent heq] at hlt
        exact (Peano.not_lt_self _ hself).elim
    | .equivalent _ =>
      rfl
    | .less _ =>
      rfl

/-- Recovering the common difference from two indexed elements of an arithmetic
walk returns a value equivalent to the walk's common difference. -/
theorem tryCommonDifferenceFromOrderedIndexedElements_getElementFrom
    (first commonDifference index index' : Decimal) (hlt : index < index') :
    ∃ d,
      tryCommonDifferenceFromOrderedIndexedElements
        index (getElementFrom first commonDifference index)
        index' (getElementFrom first commonDifference index') hlt = some d ∧
      d ≈ commonDifference := by
  have heq := getElementFrom_add_mul_of_lt first commonDifference index index' hlt
  obtain ⟨elementDiff, hsub_eq, hsub_approx⟩ :=
    InfiniteArithmetic.exists_of_option_rel_some
      (InfiniteArithmetic.trySubtract_of_equivalent_add heq)
  obtain ⟨d, hdiv_eq, hdiv_approx⟩ :=
    InfiniteArithmetic.exists_of_option_rel_some
      (InfiniteArithmetic.tryDivide_of_equivalent_mul hsub_approx)
  refine ⟨d, ?_, hdiv_approx⟩
  simp only [tryCommonDifferenceFromOrderedIndexedElements, hsub_eq, hdiv_eq]

/-- Recovering the first element from an indexed element of an arithmetic walk,
using a common difference equivalent to the walk's, returns a value equivalent
to that walk's start. -/
theorem tryFirstFromIndexedElement_getElementFrom_of_equivalent_diff
    (first commonDifference index d : Decimal)
    (hd : d ≈ commonDifference) :
    ∃ first',
      tryFirstFromIndexedElement index
        (getElementFrom first commonDifference index) d = some first' ∧
      first' ≈ first := by
  if hone : index ≈ one then
    refine ⟨getElementFrom first commonDifference index, ?_, ?_⟩
    · simp only [tryFirstFromIndexedElement, hone, ↓reduceDIte]
    · simp only [getElementFrom, hone, ↓reduceDIte]
      exact Setoid.refl _
  else
    have hget : getElementFrom first commonDifference index =
        first + (index.predecessor hone) * commonDifference := by
      simp only [getElementFrom, hone, ↓reduceDIte]
    have hrel :=
      InfiniteArithmetic.trySubtract_add_right_of_equivalent first
        ((index.predecessor hone) * commonDifference)
        ((index.predecessor hone) * d)
        (InfiniteArithmetic.equivalent_multiply (Setoid.refl _) (Setoid.symm hd))
    obtain ⟨first', hsub_eq, hsub_approx⟩ :=
      InfiniteArithmetic.exists_of_option_rel_some hrel
    refine ⟨first', ?_, hsub_approx⟩
    simp only [tryFirstFromIndexedElement, hone, ↓reduceDIte, hget, hsub_eq]

/-- Reconstructing from any two inequivalent in-range elements of `p`, together
with `getLength p`, yields a progression equivalent to `p`. -/
theorem tryFromTwoElementsAndLength_getElement
    (p : FiniteArithmeticIncreasing)
    (index1 index2 : Decimal)
    (hne : ¬ index1 ≈ index2)
    (hle1 : CardinalNatural.Decimal.fromOrdinal index1 ≤ getLength p)
    (hle2 : CardinalNatural.Decimal.fromOrdinal index2 ≤ getLength p) :
    ∃ (q : FiniteArithmeticIncreasing),
      tryFromTwoElementsAndLength
        index1 (getElement p index1 hle1)
        index2 (getElement p index2 hle2)
        (getLength p) hne = some q ∧
      p ≈ q := by
  have hne0 : ¬ getLength p ≈ CardinalNatural.Decimal.zero := by
    intro hzero
    have :
        CardinalNatural.Decimal.fromOrdinal index1 ≤
          CardinalNatural.Decimal.zero :=
      CardinalNatural.Decimal.le_of_le_of_equivalent hle1 hzero
    exact CardinalNatural.Decimal.fromOrdinal_not_equivalent_zero index1
      (CardinalNatural.Decimal.eq_zero_of_le_zero _ this)
  obtain ⟨first, hf⟩ := effectiveFirst_eq_some_of_pos_length p hne0
  have hget1 := getElement_eq_getElementFrom p first hf index1 hle1
  have hget2 := getElement_eq_getElementFrom p first hf index2 hle2
  match hcomp : compare index1 index2 with
  | .equivalent heq =>
    exact (hne heq).elim
  | .less hlt =>
    obtain ⟨diff, hdiff_eq, hdiff_approx⟩ :=
      tryCommonDifferenceFromOrderedIndexedElements_getElementFrom
        first p.commonDifference index1 index2 hlt
    obtain ⟨first', hfirst_eq, hfirst_approx⟩ :=
      tryFirstFromIndexedElement_getElementFrom_of_equivalent_diff
        first p.commonDifference index1 diff hdiff_approx
    refine
      ⟨{
          first := some first'
          commonDifference := diff
          limit := lastElementFrom first' diff (getLength p)
        }, ?_, ?_⟩
    · simp only [tryFromTwoElementsAndLength, hle1, hle2, ↓reduceIte, hget1,
        hget2, hcomp, hdiff_eq, hfirst_eq]
    · have hf_q :
          effectiveFirst
            {
              first := some first'
              commonDifference := diff
              limit := lastElementFrom first' diff (getLength p)
            } =
            some first' :=
        effectiveFirst_of_equivalent_lastElementFrom first' diff diff
          (lastElementFrom first' diff (getLength p)) (getLength p) hne0
          (Setoid.refl _)
      have hlen_q :=
        getLength_lastElementFrom first' diff (getLength p) hne0
      exact equivalence_of_equivalent_params p _ first first' hf hf_q
        (Setoid.symm hfirst_approx) (Setoid.symm hdiff_approx)
        (Setoid.symm hlen_q)
  | .greater hgt =>
    obtain ⟨diff, hdiff_eq, hdiff_approx⟩ :=
      tryCommonDifferenceFromOrderedIndexedElements_getElementFrom
        first p.commonDifference index2 index1 hgt
    obtain ⟨first', hfirst_eq, hfirst_approx⟩ :=
      tryFirstFromIndexedElement_getElementFrom_of_equivalent_diff
        first p.commonDifference index2 diff hdiff_approx
    refine
      ⟨{
          first := some first'
          commonDifference := diff
          limit := lastElementFrom first' diff (getLength p)
        }, ?_, ?_⟩
    · simp only [tryFromTwoElementsAndLength, hle1, hle2, ↓reduceIte, hget1,
        hget2, hcomp, hdiff_eq, hfirst_eq]
    · have hf_q :
          effectiveFirst
            {
              first := some first'
              commonDifference := diff
              limit := lastElementFrom first' diff (getLength p)
            } =
            some first' :=
        effectiveFirst_of_equivalent_lastElementFrom first' diff diff
          (lastElementFrom first' diff (getLength p)) (getLength p) hne0
          (Setoid.refl _)
      have hlen_q :=
        getLength_lastElementFrom first' diff (getLength p) hne0
      exact equivalence_of_equivalent_params p _ first first' hf hf_q
        (Setoid.symm hfirst_approx) (Setoid.symm hdiff_approx)
        (Setoid.symm hlen_q)

/-- Advance one step from an optional current element of a finite increasing
arithmetic progression: add the common difference while it does not exceed the
limit; stay at `none` once past the end. -/
def nextMaskedWalkElement (commonDifference limit : Decimal) :
    Option Decimal → Option Decimal
  | none => none
  | some x =>
    let y := x + commonDifference
    if y ≤ limit then some y else none

/-- Whether every unmasked entry agrees with a progression walk that is already
positioned at `current` (the value of `tryGetElement` at the corresponding
index). Masked (`none`) entries are skipped after advancing the walk. Avoids
recomputing `tryGetElement` from the start at each unmasked entry. Elements are
compared up to Decimal equivalence. -/
def agreesWithMaskedElementsFromCurrent
    (commonDifference limit : Decimal) (current : Option Decimal) :
    Sequences.List (Option Decimal) → Bool
  | .empty => true
  | .firstElement none rest =>
      agreesWithMaskedElementsFromCurrent commonDifference limit
        (nextMaskedWalkElement commonDifference limit current) rest
  | .firstElement (some x) rest =>
      match current with
      | none => false
      | some y =>
        if y ≈ x then
          agreesWithMaskedElementsFromCurrent commonDifference limit
            (nextMaskedWalkElement commonDifference limit current) rest
        else
          false

/-- Whether every unmasked entry agrees with `tryGetElement` on `p`, scanning
from the given ordinal Decimal index. Masked (`none`) entries are ignored.

Seeks the starting element once via `effectiveFirst` / `getElementFrom` (or
`none` when out of range), then walks by successive addition of the common
difference — avoiding a fresh `tryGetElement` walk at every unmasked entry.
Unmasked entries are compared up to Decimal equivalence. -/
def agreesWithMaskedElementsFrom (p : FiniteArithmeticIncreasing)
    (index : Decimal) (elements : Sequences.List (Option Decimal)) : Bool :=
  match effectiveFirst p with
  | none =>
    agreesWithMaskedElementsFromCurrent p.commonDifference p.limit none elements
  | some first =>
    if CardinalNatural.Decimal.fromOrdinal index ≤ getLength p then
      agreesWithMaskedElementsFromCurrent p.commonDifference p.limit
        (some (getElementFrom first p.commonDifference index)) elements
    else
      agreesWithMaskedElementsFromCurrent p.commonDifference p.limit none
        elements

/-- After one unmasked element at `index1` is known, find a second unmasked
element at a strictly larger index and reconstruct via
`tryFromTwoElementsAndLength`, then check that every later unmasked entry
agrees with the result. -/
def tryFromMaskedElementsGivenOne
    (index1 : Decimal) (element1 : Decimal) (length : CardinalNatural.Decimal)
    (index : Decimal) (hlt : index1 < index) :
    (elements : Sequences.List (Option Decimal)) →
    CardinalNatural.Peano.one ≤ elements.unmaskedCount →
    Option FiniteArithmeticIncreasing
  | .empty, hge =>
      False.elim (CardinalNatural.Peano.not_succ_le_zero (by
        simpa only [Sequences.List.unmaskedCount, CardinalNatural.Peano.one]
          using hge))
  | .firstElement none rest, hge =>
      tryFromMaskedElementsGivenOne index1 element1 length
        index.successor (lt_trans hlt (x_lt_succ_x index)) rest (by
          simpa only [Sequences.List.unmaskedCount] using hge)
  | .firstElement (some element2) rest, _ =>
      match
        tryFromTwoElementsAndLength index1 element1 index element2 length
          (not_equivalent_of_lt hlt) with
      | none => none
      | some p =>
        if agreesWithMaskedElementsFrom p index.successor rest then
          some p
        else
          none

/-- Scan a masked element list from the given ordinal Decimal index until the
first unmasked entry is found, then continue with
`tryFromMaskedElementsGivenOne`. -/
def tryFromMaskedElementsFrom (index : Decimal)
    (length : CardinalNatural.Decimal) :
    (elements : Sequences.List (Option Decimal)) →
    CardinalNatural.Peano.two ≤ elements.unmaskedCount →
    Option FiniteArithmeticIncreasing
  | .empty, hge =>
      False.elim (CardinalNatural.Peano.not_two_le_zero (by
        simpa only [Sequences.List.unmaskedCount] using hge))
  | .firstElement none rest, hge =>
      tryFromMaskedElementsFrom index.successor length rest (by
        simpa only [Sequences.List.unmaskedCount] using hge)
  | .firstElement (some x) rest, hge =>
      tryFromMaskedElementsGivenOne index x length
        index.successor (x_lt_succ_x index) rest (by
          have h :
              CardinalNatural.Peano.two ≤
                rest.unmaskedCount + CardinalNatural.Peano.one := by
            simpa only [Sequences.List.unmaskedCount] using hge
          have h' :
              CardinalNatural.Peano.two ≤
                rest.unmaskedCount.successor := by
            simpa only [CardinalNatural.Peano.add_one] using h
          exact CardinalNatural.Peano.le_of_succ_le_succ (by
            simpa only [CardinalNatural.Peano.two, CardinalNatural.Peano.one]
              using h'))

/-- Reconstruct a finite increasing arithmetic progression from an ordered list
of its elements in which some entries may be masked as `none`. Requires a proof
that at least two entries are unmasked. Returns `none` when the unmasked entries
are not consistent with a strictly increasing arithmetic progression whose
length equals that of the list (compared up to Decimal equivalence).

Uses the first two unmasked entries (together with their ordinal Decimal indexes
and the list length) via `tryFromTwoElementsAndLength`, then checks that every
remaining unmasked entry agrees with the reconstructed progression. -/
def tryFromMaskedElements
    (elements : Sequences.List (Option Decimal))
    (hge : CardinalNatural.Peano.two ≤ elements.unmaskedCount) :
    Option FiniteArithmeticIncreasing :=
  tryFromMaskedElementsFrom one
    (CardinalNatural.Decimal.fromPeano elements.length) elements hge

/-- Prop counterpart of `agreesWithMaskedElementsFrom`: every unmasked entry is
Decimal-equivalent to `tryGetElement` at the corresponding ordinal index. -/
inductive AgreesWithMaskedElementsFrom (p : FiniteArithmeticIncreasing) :
    Decimal → Sequences.List (Option Decimal) → Prop where
  | empty (index : Decimal) :
      AgreesWithMaskedElementsFrom p index .empty
  | masked (index : Decimal) (rest : Sequences.List (Option Decimal)) :
      AgreesWithMaskedElementsFrom p index.successor rest →
        AgreesWithMaskedElementsFrom p index (.firstElement none rest)
  | unmasked (index y x : Decimal) (rest : Sequences.List (Option Decimal)) :
      Sequences.Progression.tryGetElement index.toPeano (toProgression p) =
          some y →
        y ≈ x →
          AgreesWithMaskedElementsFrom p index.successor rest →
            AgreesWithMaskedElementsFrom p index (.firstElement (some x) rest)

/-- One walk step matches `toProgression.next` on a present element. -/
theorem nextMaskedWalkElement_eq_toProgression_next
    (p : FiniteArithmeticIncreasing) (x : Decimal) :
    nextMaskedWalkElement p.commonDifference p.limit (some x) =
      (toProgression p).next x :=
  rfl

/-- Advancing the masked walk from `tryGetElement index` yields
`tryGetElement index.successor`. -/
theorem nextMaskedWalkElement_tryGetElement (p : FiniteArithmeticIncreasing)
    (index : Peano) :
    nextMaskedWalkElement p.commonDifference p.limit
      (Sequences.Progression.tryGetElement index (toProgression p)) =
      Sequences.Progression.tryGetElement index.successor (toProgression p) := by
  match h : Sequences.Progression.tryGetElement index (toProgression p) with
  | none =>
    simp only [nextMaskedWalkElement, Sequences.Progression.tryGetElement, h]
  | some x =>
    simp only [Sequences.Progression.tryGetElement, h,
      nextMaskedWalkElement_eq_toProgression_next]

theorem tryGetElement_none_of_effectiveFirst_none
    (p : FiniteArithmeticIncreasing) (index : Peano)
    (hf : effectiveFirst p = none) :
    Sequences.Progression.tryGetElement index (toProgression p) = none := by
  have hfirst : (toProgression p).first = none := effectiveFirst_eq p ▸ hf
  change
      Sequences.Progression.tryGetElement index
        ⟨(toProgression p).first, (toProgression p).next⟩ =
      none
  rw [hfirst]
  exact Sequences.Progression.tryGetElement_none_of_first_none
    (toProgression p).next index

/-- In-range `tryGetElement` is related by Decimal equivalence to
`getElementFrom` on the effective first. -/
theorem tryGetElement_rel_getElementFrom_of_le (p : FiniteArithmeticIncreasing)
    (first : Decimal) (hf : effectiveFirst p = some first) (index : Decimal)
    (hle : CardinalNatural.Decimal.fromOrdinal index ≤ getLength p) :
    Option.Rel (· ≈ ·)
      (Sequences.Progression.tryGetElement index.toPeano (toProgression p))
      (some (getElementFrom first p.commonDifference index)) := by
  have htry :=
    Sequences.Progression.tryGetElement_eq_some_getElement
      (toProgression p) (toProgression_finite p) index.toPeano
      (fromOrdinal_le_progression_getLength p index hle)
  rw [htry]
  exact Option.Rel.some
    (Setoid.trans (Setoid.symm (getElement_eq p index hle))
      (by
        rw [getElement_eq_getElementFrom p first hf index hle]
        exact Setoid.refl _))

/-- Out-of-range `tryGetElement` is `none`. -/
theorem tryGetElement_eq_none_of_length_lt (p : FiniteArithmeticIncreasing)
    (index : Decimal)
    (hlt : getLength p < CardinalNatural.Decimal.fromOrdinal index) :
    Sequences.Progression.tryGetElement index.toPeano (toProgression p) = none := by
  have hlt_peano :
      Sequences.Progression.getLength (toProgression p) (toProgression_finite p) <
        CardinalNatural.Peano.fromOrdinal index.toPeano := by
    have hlen_eq := getLength_eq p
    have hto :
        (getLength p).toPeano =
          Sequences.Progression.getLength (toProgression p)
            (toProgression_finite p) := by
      have h := CardinalNatural.Decimal.toPeano_eq_of_equivalent hlen_eq
      rwa [CardinalNatural.Decimal.toPeano_fromPeano] at h
    have hlt' :
        (getLength p).toPeano <
          (CardinalNatural.Decimal.fromOrdinal index).toPeano :=
      hlt
    rwa [hto, CardinalNatural.Decimal.fromOrdinal_toPeano_eq_fromOrdinal_peano]
      at hlt'
  exact Sequences.Progression.tryGetElement_eq_none_of_getLength_lt
    (toProgression p) (toProgression_finite p) index.toPeano hlt_peano

/-- Masked walk steps preserve Decimal `Option.Rel (· ≈ ·)`. -/
theorem nextMaskedWalkElement_rel_of_rel (commonDifference limit : Decimal)
    {c1 c2 : Option Decimal} (h : Option.Rel (· ≈ ·) c1 c2) :
    Option.Rel (· ≈ ·)
      (nextMaskedWalkElement commonDifference limit c1)
      (nextMaskedWalkElement commonDifference limit c2) := by
  cases h with
  | none =>
    exact Option.Rel.none
  | some hxy =>
    rename_i x y
    have hadd : x + commonDifference ≈ y + commonDifference :=
      InfiniteArithmetic.equivalent_add_right hxy
    have hle_iff :
        (x + commonDifference ≤ limit) ↔ (y + commonDifference ≤ limit) := by
      constructor
      · intro hle
        exact (le_iff_toPeano_le _ _).mpr
          (toPeano_eq_of_equivalent hadd ▸ (le_iff_toPeano_le _ _).mp hle)
      · intro hle
        exact (le_iff_toPeano_le _ _).mpr
          ((toPeano_eq_of_equivalent hadd).symm ▸
            (le_iff_toPeano_le _ _).mp hle)
    change Option.Rel (· ≈ ·)
      (if x + commonDifference ≤ limit then some (x + commonDifference) else none)
      (if y + commonDifference ≤ limit then some (y + commonDifference) else none)
    by_cases hle_x : x + commonDifference ≤ limit
    · have hle_y : y + commonDifference ≤ limit := hle_iff.mp hle_x
      simp only [hle_x, hle_y, ↓reduceIte]
      exact Option.Rel.some hadd
    · have hle_y : ¬ y + commonDifference ≤ limit := fun h' =>
        hle_x (hle_iff.mpr h')
      simp only [hle_x, hle_y, ↓reduceIte]
      exact Option.Rel.none

/-- The current-position agreement walk is invariant under replacing `current` by
an `Option.Rel (· ≈ ·)`-related value. -/
theorem agreesWithMaskedElementsFromCurrent_eq_of_current_rel
    (commonDifference limit : Decimal) {c1 c2 : Option Decimal}
    (h : Option.Rel (· ≈ ·) c1 c2)
    (elements : Sequences.List (Option Decimal)) :
    agreesWithMaskedElementsFromCurrent commonDifference limit c1 elements =
      agreesWithMaskedElementsFromCurrent commonDifference limit c2 elements := by
  induction elements generalizing c1 c2 with
  | empty =>
    rfl
  | firstElement head rest ih =>
    cases head with
    | none =>
      exact ih (nextMaskedWalkElement_rel_of_rel commonDifference limit h)
    | some x =>
      cases h with
      | none =>
        rfl
      | some hy =>
        rename_i y1 y2
        simp only [agreesWithMaskedElementsFromCurrent]
        by_cases h1 : y1 ≈ x
        · have h2 : y2 ≈ x := Setoid.trans (Setoid.symm hy) h1
          simp only [h1, h2, ↓reduceIte]
          exact ih (nextMaskedWalkElement_rel_of_rel commonDifference limit
            (Option.Rel.some hy))
        · have h2 : ¬ y2 ≈ x := fun h' => h1 (Setoid.trans hy h')
          simp only [h1, h2, ↓reduceIte]

/-- `agreesWithMaskedElementsFrom` starts its walk at `tryGetElement` on the
Peano embedding of the Decimal index. -/
theorem agreesWithMaskedElementsFrom_eq_fromCurrent_tryGetElement
    (p : FiniteArithmeticIncreasing) (index : Decimal)
    (elements : Sequences.List (Option Decimal)) :
    agreesWithMaskedElementsFrom p index elements =
      agreesWithMaskedElementsFromCurrent p.commonDifference p.limit
        (Sequences.Progression.tryGetElement index.toPeano (toProgression p))
        elements := by
  match hf : effectiveFirst p with
  | none =>
    have htry := tryGetElement_none_of_effectiveFirst_none p index.toPeano hf
    simp only [agreesWithMaskedElementsFrom, hf, htry]
  | some first =>
    by_cases hle : CardinalNatural.Decimal.fromOrdinal index ≤ getLength p
    · have hrel :=
        tryGetElement_rel_getElementFrom_of_le p first hf index hle
      have hcongr :=
        agreesWithMaskedElementsFromCurrent_eq_of_current_rel
          p.commonDifference p.limit hrel elements
      simp only [agreesWithMaskedElementsFrom, hf, hle, ↓reduceIte]
      exact hcongr.symm
    · have hlt : getLength p < CardinalNatural.Decimal.fromOrdinal index := by
        cases CardinalNatural.Decimal.trichotomy_or (getLength p)
            (CardinalNatural.Decimal.fromOrdinal index) with
        | inl hlt => exact hlt
        | inr h =>
          cases h with
          | inl heq => exact False.elim (hle (Or.inr heq.symm))
          | inr hgt => exact False.elim (hle (Or.inl hgt))
      have htry := tryGetElement_eq_none_of_length_lt p index hlt
      simp only [agreesWithMaskedElementsFrom, hf, hle, ↓reduceIte, htry]

/-- The current-position walk agrees with the Prop when `current` is
`tryGetElement` at the corresponding Decimal index. -/
theorem agreesWithMaskedElementsFromCurrent_eq_true_iff
    (p : FiniteArithmeticIncreasing) (index : Decimal) (current : Option Decimal)
    (elements : Sequences.List (Option Decimal))
    (hcur : current =
      Sequences.Progression.tryGetElement index.toPeano (toProgression p)) :
    agreesWithMaskedElementsFromCurrent p.commonDifference p.limit current
        elements = true ↔
      AgreesWithMaskedElementsFrom p index elements := by
  induction elements generalizing index current with
  | empty =>
    constructor
    · intro _
      exact AgreesWithMaskedElementsFrom.empty index
    · intro _
      rfl
  | firstElement head rest ih =>
    cases head with
    | none =>
      have hnext :
          nextMaskedWalkElement p.commonDifference p.limit current =
            Sequences.Progression.tryGetElement index.successor.toPeano
              (toProgression p) := by
        rw [hcur, nextMaskedWalkElement_tryGetElement, successor_toPeano]
      constructor
      · intro h
        exact AgreesWithMaskedElementsFrom.masked index rest
          ((ih index.successor
            (nextMaskedWalkElement p.commonDifference p.limit current)
            hnext).mp (by
            simpa only [agreesWithMaskedElementsFromCurrent] using h))
      · intro h
        cases h with
        | masked _ _ hrest =>
          exact (ih index.successor
            (nextMaskedWalkElement p.commonDifference p.limit current)
            hnext).mpr hrest
    | some x =>
      simp only [agreesWithMaskedElementsFromCurrent]
      match hcur' : current with
      | none =>
        have htry :
            Sequences.Progression.tryGetElement index.toPeano (toProgression p) =
              none := hcur.symm
        constructor
        · intro h
          exact False.elim (Bool.false_ne_true h)
        · intro h
          cases h with
          | unmasked _ _ _ _ htry' _ _ =>
            rw [htry] at htry'
            nomatch htry'
      | some y =>
        have htry :
            Sequences.Progression.tryGetElement index.toPeano (toProgression p) =
              some y := hcur.symm
        simp only
        split
        · next heq =>
          have hnext :
              nextMaskedWalkElement p.commonDifference p.limit (some y) =
                Sequences.Progression.tryGetElement index.successor.toPeano
                  (toProgression p) := by
            rw [← htry, nextMaskedWalkElement_tryGetElement, successor_toPeano]
          constructor
          · intro h
            exact AgreesWithMaskedElementsFrom.unmasked index y x rest htry heq
              ((ih index.successor
                (nextMaskedWalkElement p.commonDifference p.limit (some y))
                hnext).mp h)
          · intro h
            cases h with
            | unmasked _ y' _ _ htry' _ hrest =>
              have hy : some y = some y' := htry.symm.trans htry'
              injection hy with hy'
              subst hy'
              exact (ih index.successor
                (nextMaskedWalkElement p.commonDifference p.limit (some y))
                hnext).mpr hrest
        · next hne =>
          constructor
          · intro h
            exact False.elim (Bool.false_ne_true h)
          · intro h
            cases h with
            | unmasked _ y' _ _ htry' heq' _ =>
              have hy : some y = some y' := htry.symm.trans htry'
              injection hy with hy'
              exact False.elim (hne (hy' ▸ heq'))

theorem agreesWithMaskedElementsFrom_eq_true_iff
    (p : FiniteArithmeticIncreasing) (index : Decimal)
    (elements : Sequences.List (Option Decimal)) :
    agreesWithMaskedElementsFrom p index elements = true ↔
      AgreesWithMaskedElementsFrom p index elements := by
  rw [agreesWithMaskedElementsFrom_eq_fromCurrent_tryGetElement]
  exact agreesWithMaskedElementsFromCurrent_eq_true_iff p index
    (Sequences.Progression.tryGetElement index.toPeano (toProgression p))
    elements rfl

theorem agreesWithMaskedElementsFrom_unmasked_eq_true
    (p : FiniteArithmeticIncreasing) (index x : Decimal)
    (rest : Sequences.List (Option Decimal)) (y : Decimal)
    (hx : Sequences.Progression.tryGetElement index.toPeano (toProgression p) =
      some y)
    (heq : y ≈ x)
    (hrest : agreesWithMaskedElementsFrom p index.successor rest = true) :
    agreesWithMaskedElementsFrom p index (.firstElement (some x) rest) = true := by
  rw [agreesWithMaskedElementsFrom_eq_fromCurrent_tryGetElement, hx]
  rw [agreesWithMaskedElementsFrom_eq_fromCurrent_tryGetElement] at hrest
  simp only [agreesWithMaskedElementsFromCurrent, heq, ↓reduceIte]
  rwa [show nextMaskedWalkElement p.commonDifference p.limit (some y) =
      Sequences.Progression.tryGetElement index.successor.toPeano
        (toProgression p) from
    by
      rw [← hx, nextMaskedWalkElement_tryGetElement, successor_toPeano]]

/-- A successful `tryFromMaskedElementsGivenOne` recovers a value equivalent to
the given first unmasked element, has length equivalent to the requested length,
and agrees with every unmasked entry in the scanned suffix. -/
theorem getLength_agreesWithMaskedElementsFrom_of_tryFromMaskedElementsGivenOne
    (index1 element1 : Decimal) (length : CardinalNatural.Decimal)
    (index : Decimal) (hlt : index1 < index)
    (elements : Sequences.List (Option Decimal))
    (hge : CardinalNatural.Peano.one ≤ elements.unmaskedCount)
    (p : FiniteArithmeticIncreasing)
    (h : tryFromMaskedElementsGivenOne index1 element1 length index hlt
        elements hge = some p) :
    getLength p ≈ length ∧
      (∃ (hle1 : CardinalNatural.Decimal.fromOrdinal index1 ≤ getLength p),
        getElement p index1 hle1 ≈ element1) ∧
      agreesWithMaskedElementsFrom p index elements = true := by
  match elements with
  | .empty =>
    exact (CardinalNatural.Peano.not_succ_le_zero (by
      simpa only [Sequences.List.unmaskedCount, CardinalNatural.Peano.one]
        using hge)).elim
  | .firstElement none rest =>
    have ih :=
      getLength_agreesWithMaskedElementsFrom_of_tryFromMaskedElementsGivenOne
        index1 element1 length index.successor
        (lt_trans hlt (x_lt_succ_x index)) rest (by
          simpa only [Sequences.List.unmaskedCount] using hge) p (by
          simpa only [tryFromMaskedElementsGivenOne] using h)
    refine ⟨ih.1, ih.2.1, ?_⟩
    rw [agreesWithMaskedElementsFrom_eq_fromCurrent_tryGetElement]
    rw [agreesWithMaskedElementsFrom_eq_fromCurrent_tryGetElement] at ih
    simpa only [agreesWithMaskedElementsFromCurrent,
      nextMaskedWalkElement_tryGetElement, successor_toPeano] using ih.2.2
  | .firstElement (some element2) rest =>
    simp only [tryFromMaskedElementsGivenOne] at h
    match hs : tryFromTwoElementsAndLength index1 element1 index element2 length
        (not_equivalent_of_lt hlt) with
    | none =>
      simp only [hs] at h
      nomatch h
    | some q =>
      simp only [hs] at h
      split at h
      · next hAgree =>
        have hq : q = p := by injection h
        rw [hq] at hs hAgree
        have hsound :=
          getLength_getElement_of_tryFromTwoElementsAndLength
            index1 element1 index element2 length (not_equivalent_of_lt hlt) p hs
        refine ⟨hsound.1, hsound.2.1, ?_⟩
        obtain ⟨hle2, hget2⟩ := hsound.2.2
        have htry2 :=
          Sequences.Progression.tryGetElement_eq_some_getElement
            (toProgression p) (toProgression_finite p) index.toPeano
            (fromOrdinal_le_progression_getLength p index hle2)
        have hy :
            Sequences.Progression.getElement (toProgression p)
                (toProgression_finite p) index.toPeano
                (fromOrdinal_le_progression_getLength p index hle2) ≈
              element2 :=
          Setoid.trans (Setoid.symm (getElement_eq p index hle2)) hget2
        exact agreesWithMaskedElementsFrom_unmasked_eq_true p index element2 rest
          _ htry2 hy hAgree
      · next =>
        nomatch h

/-- A successful `tryFromMaskedElementsFrom` has length equivalent to the
requested length and agrees with every unmasked entry from the given starting
index. -/
theorem getLength_agreesWithMaskedElementsFrom_of_tryFromMaskedElementsFrom
    (index : Decimal) (length : CardinalNatural.Decimal)
    (elements : Sequences.List (Option Decimal))
    (hge : CardinalNatural.Peano.two ≤ elements.unmaskedCount)
    (p : FiniteArithmeticIncreasing)
    (h : tryFromMaskedElementsFrom index length elements hge = some p) :
    getLength p ≈ length ∧
      agreesWithMaskedElementsFrom p index elements = true := by
  match elements with
  | .empty =>
    exact (CardinalNatural.Peano.not_two_le_zero (by
      simpa only [Sequences.List.unmaskedCount] using hge)).elim
  | .firstElement none rest =>
    have ih :=
      getLength_agreesWithMaskedElementsFrom_of_tryFromMaskedElementsFrom
        index.successor length rest (by
          simpa only [Sequences.List.unmaskedCount] using hge) p (by
          simpa only [tryFromMaskedElementsFrom] using h)
    refine ⟨ih.1, ?_⟩
    rw [agreesWithMaskedElementsFrom_eq_fromCurrent_tryGetElement]
    rw [agreesWithMaskedElementsFrom_eq_fromCurrent_tryGetElement] at ih
    simpa only [agreesWithMaskedElementsFromCurrent,
      nextMaskedWalkElement_tryGetElement, successor_toPeano] using ih.2
  | .firstElement (some x) rest =>
    have hgeRest :
        CardinalNatural.Peano.one ≤ rest.unmaskedCount := by
      have h' :
          CardinalNatural.Peano.two ≤
            rest.unmaskedCount + CardinalNatural.Peano.one := by
        simpa only [Sequences.List.unmaskedCount] using hge
      have h'' :
          CardinalNatural.Peano.two ≤ rest.unmaskedCount.successor := by
        simpa only [CardinalNatural.Peano.add_one] using h'
      exact CardinalNatural.Peano.le_of_succ_le_succ (by
        simpa only [CardinalNatural.Peano.two, CardinalNatural.Peano.one]
          using h'')
    have hGiven :=
      getLength_agreesWithMaskedElementsFrom_of_tryFromMaskedElementsGivenOne
        index x length index.successor (x_lt_succ_x index) rest hgeRest p (by
          simpa only [tryFromMaskedElementsFrom] using h)
    refine ⟨hGiven.1, ?_⟩
    obtain ⟨hle1, hget1⟩ := hGiven.2.1
    have htry :=
      Sequences.Progression.tryGetElement_eq_some_getElement
        (toProgression p) (toProgression_finite p) index.toPeano
        (fromOrdinal_le_progression_getLength p index hle1)
    have hy :
        Sequences.Progression.getElement (toProgression p)
            (toProgression_finite p) index.toPeano
            (fromOrdinal_le_progression_getLength p index hle1) ≈
          x :=
      Setoid.trans (Setoid.symm (getElement_eq p index hle1)) hget1
    exact agreesWithMaskedElementsFrom_unmasked_eq_true p index x rest
      _ htry hy hGiven.2.2

/-- A successful `tryFromMaskedElements` yields a progression whose length is
equivalent to the list length and whose `tryGetElement` recovers every unmasked
entry at the same ordinal index up to Decimal equivalence. -/
theorem getLength_agreesWithMaskedElements_of_tryFromMaskedElements
    (elements : Sequences.List (Option Decimal))
    (hge : CardinalNatural.Peano.two ≤ elements.unmaskedCount)
    (p : FiniteArithmeticIncreasing)
    (h : tryFromMaskedElements elements hge = some p) :
    getLength p ≈ CardinalNatural.Decimal.fromPeano elements.length ∧
      AgreesWithMaskedElementsFrom p one elements := by
  have h' :
      tryFromMaskedElementsFrom one
        (CardinalNatural.Decimal.fromPeano elements.length) elements hge =
        some p := by
    simpa only [tryFromMaskedElements] using h
  have hsound :=
    getLength_agreesWithMaskedElementsFrom_of_tryFromMaskedElementsFrom
      one (CardinalNatural.Decimal.fromPeano elements.length) elements hge p h'
  refine ⟨hsound.1, ?_⟩
  exact (agreesWithMaskedElementsFrom_eq_true_iff p one elements).mp hsound.2

/-- Extend a finite increasing arithmetic progression of length at least two to
an infinite arithmetic progression with the same effective first element and
common difference. The infinite progression begins with every element of the
original finite progression. -/
def extendToInfinite (p : FiniteArithmeticIncreasing)
    (hge : CardinalNatural.Peano.two ≤ (getLength p).toPeano) :
    InfiniteArithmetic :=
  match hf : effectiveFirst p with
  | none =>
    False.elim
      (CardinalNatural.Peano.not_two_le_zero
        (((CardinalNatural.Decimal.toPeano_eq_of_equivalent
            ((getLength_eq_zero_iff_effectiveFirst_none p).mpr hf)).trans
          CardinalNatural.Decimal.toPeano_zero) ▸ hge))
  | some first =>
    { first := first, commonDifference := p.commonDifference }

/-- In-range elements of a finite increasing arithmetic progression agree with
the corresponding elements of its infinite extension. -/
theorem getElement_extendToInfinite (p : FiniteArithmeticIncreasing)
    (hge : CardinalNatural.Peano.two ≤ (getLength p).toPeano)
    (index : Decimal)
    (hle : CardinalNatural.Decimal.fromOrdinal index ≤ getLength p) :
    InfiniteArithmetic.getElement (extendToInfinite p hge) index =
      getElement p index hle := by
  unfold extendToInfinite
  split
  · next hf =>
    exact (CardinalNatural.Peano.not_two_le_zero
      (((CardinalNatural.Decimal.toPeano_eq_of_equivalent
          ((getLength_eq_zero_iff_effectiveFirst_none p).mpr hf)).trans
        CardinalNatural.Decimal.toPeano_zero) ▸ hge)).elim
  · next first hf =>
    rw [getElement_eq_getElementFrom p first hf index hle]
    exact (getElementFrom_eq_InfiniteArithmetic_getElement
      first p.commonDifference index).symm

/-- Extend a finite increasing arithmetic progression of length at least two to
a finite increasing arithmetic progression of a given length at least that of
the original, with the same effective first element and common difference. The
extended progression begins with every element of the original progression. -/
def extendToLength (p : FiniteArithmeticIncreasing)
    (hge : CardinalNatural.Peano.two ≤ (getLength p).toPeano)
    (length : CardinalNatural.Decimal)
    (_hle : getLength p ≤ length) :
    FiniteArithmeticIncreasing :=
  match hf : effectiveFirst p with
  | none =>
    False.elim
      (CardinalNatural.Peano.not_two_le_zero
        (((CardinalNatural.Decimal.toPeano_eq_of_equivalent
            ((getLength_eq_zero_iff_effectiveFirst_none p).mpr hf)).trans
          CardinalNatural.Decimal.toPeano_zero) ▸ hge))
  | some first =>
    {
      first := some first
      commonDifference := p.commonDifference
      limit := lastElementFrom first p.commonDifference length
    }

/-- Extending to a longer length yields a progression whose length is equivalent
to that requested length. -/
theorem getLength_extendToLength (p : FiniteArithmeticIncreasing)
    (hge : CardinalNatural.Peano.two ≤ (getLength p).toPeano)
    (length : CardinalNatural.Decimal)
    (hleLen : getLength p ≤ length) :
    getLength (extendToLength p hge length hleLen) ≈ length := by
  unfold extendToLength
  split
  · next hf =>
    exact (CardinalNatural.Peano.not_two_le_zero
      (((CardinalNatural.Decimal.toPeano_eq_of_equivalent
          ((getLength_eq_zero_iff_effectiveFirst_none p).mpr hf)).trans
        CardinalNatural.Decimal.toPeano_zero) ▸ hge)).elim
  · next first hf =>
    have hne : ¬ length ≈ CardinalNatural.Decimal.zero := by
      intro hzero
      have hp0 : getLength p ≈ CardinalNatural.Decimal.zero :=
        CardinalNatural.Decimal.eq_zero_of_le_zero _
          (CardinalNatural.Decimal.le_of_le_of_equivalent hleLen hzero)
      exact CardinalNatural.Peano.not_two_le_zero
        (((CardinalNatural.Decimal.toPeano_eq_of_equivalent hp0).trans
          CardinalNatural.Decimal.toPeano_zero) ▸ hge)
    exact getLength_lastElementFrom first p.commonDifference length hne

/-- The extended progression keeps the original effective first element. -/
theorem effectiveFirst_extendToLength (p : FiniteArithmeticIncreasing)
    (hge : CardinalNatural.Peano.two ≤ (getLength p).toPeano)
    (length : CardinalNatural.Decimal)
    (hleLen : getLength p ≤ length)
    (first : Decimal) (hf : effectiveFirst p = some first) :
    effectiveFirst (extendToLength p hge length hleLen) = some first := by
  have hne : ¬ length ≈ CardinalNatural.Decimal.zero := by
    intro hzero
    have hp0 : getLength p ≈ CardinalNatural.Decimal.zero :=
      CardinalNatural.Decimal.eq_zero_of_le_zero _
        (CardinalNatural.Decimal.le_of_le_of_equivalent hleLen hzero)
    exact CardinalNatural.Peano.not_two_le_zero
      (((CardinalNatural.Decimal.toPeano_eq_of_equivalent hp0).trans
        CardinalNatural.Decimal.toPeano_zero) ▸ hge)
  unfold extendToLength
  split
  · next hf' =>
    rw [hf'] at hf
    nomatch hf
  · next first' hf' =>
    have heq : some first = some first' := hf.symm.trans hf'
    injection heq with heq'
    rw [← heq']
    exact effectiveFirst_of_equivalent_lastElementFrom first
      p.commonDifference p.commonDifference
      (lastElementFrom first p.commonDifference length) length hne
      (Setoid.refl _)

/-- In-range elements of a finite increasing arithmetic progression agree with
the corresponding elements of its length extension. -/
theorem getElement_extendToLength (p : FiniteArithmeticIncreasing)
    (hge : CardinalNatural.Peano.two ≤ (getLength p).toPeano)
    (length : CardinalNatural.Decimal)
    (hleLen : getLength p ≤ length)
    (index : Decimal)
    (hle : CardinalNatural.Decimal.fromOrdinal index ≤ getLength p) :
    ∃ (hle' : CardinalNatural.Decimal.fromOrdinal index ≤
        getLength (extendToLength p hge length hleLen)),
      getElement (extendToLength p hge length hleLen) index hle' =
        getElement p index hle := by
  have hlenExt := getLength_extendToLength p hge length hleLen
  have hle' :
      CardinalNatural.Decimal.fromOrdinal index ≤
        getLength (extendToLength p hge length hleLen) :=
    CardinalNatural.Decimal.le_of_le_of_equivalent
      (CardinalNatural.Decimal.le_trans hle hleLen) (Setoid.symm hlenExt)
  refine ⟨hle', ?_⟩
  match hf : effectiveFirst p with
  | none =>
    exact (CardinalNatural.Peano.not_two_le_zero
      (((CardinalNatural.Decimal.toPeano_eq_of_equivalent
          ((getLength_eq_zero_iff_effectiveFirst_none p).mpr hf)).trans
        CardinalNatural.Decimal.toPeano_zero) ▸ hge)).elim
  | some first =>
    have hfExt :=
      effectiveFirst_extendToLength p hge length hleLen first hf
    rw [getElement_eq_getElementFrom (extendToLength p hge length hleLen)
      first hfExt index hle']
    rw [getElement_eq_getElementFrom p first hf index hle]
    have hdiff :
        (extendToLength p hge length hleLen).commonDifference =
          p.commonDifference := by
      unfold extendToLength
      split
      · next hf' =>
        rw [hf'] at hf
        nomatch hf
      · rfl
    rw [hdiff]

/-- Truncate a finite increasing arithmetic progression of length at least two to
a finite increasing arithmetic progression of a given length at most that of
the original, with the same effective first element (when non-empty) and common
difference. The truncated progression contains the initial elements of the
original progression. -/
def truncateToLength (p : FiniteArithmeticIncreasing)
    (hge : CardinalNatural.Peano.two ≤ (getLength p).toPeano)
    (length : CardinalNatural.Decimal)
    (_hle : length ≤ getLength p) :
    FiniteArithmeticIncreasing :=
  if length ≈ CardinalNatural.Decimal.zero then
    {
      first := none
      commonDifference := p.commonDifference
      limit := p.limit
    }
  else
    match hf : effectiveFirst p with
    | none =>
      False.elim
        (CardinalNatural.Peano.not_two_le_zero
          (((CardinalNatural.Decimal.toPeano_eq_of_equivalent
              ((getLength_eq_zero_iff_effectiveFirst_none p).mpr hf)).trans
            CardinalNatural.Decimal.toPeano_zero) ▸ hge))
    | some first =>
      {
        first := some first
        commonDifference := p.commonDifference
        limit := lastElementFrom first p.commonDifference length
      }

end FiniteArithmeticIncreasing

end ZeroMath.Numbers.OrdinalNatural.Decimal.Progressions
