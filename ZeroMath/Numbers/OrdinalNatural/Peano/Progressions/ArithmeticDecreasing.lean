import ZeroMath.Numbers.OrdinalNatural.Peano
import ZeroMath.Sequences.Progression

namespace ZeroMath.Numbers.OrdinalNatural.Peano.Progressions

/-- An arithmetic progression of Peano numbers with subtractive common
difference, defined by an optional first element (`none` for the empty
progression), the common difference (subtracted at each step), and a limit
such that no element is less than the limit. The progression is also empty
when the first element is less than the limit. Because every Peano number is
at least one, the common difference is always positive. -/
structure ArithmeticDecreasing where
  first : Option Peano
  subtractiveCommonDifference : Peano
  limit : Peano

namespace ArithmeticDecreasing

/-- Convert a decreasing arithmetic progression to a general progression by
taking the same optional first element when it is not less than the limit
(otherwise the empty progression) and subtracting the common difference while
the next element is not less than the limit. -/
def toProgression (p : ArithmeticDecreasing) : Sequences.Progression Peano where
  first :=
    match p.first with
    | none => none
    | some x => if p.limit ≤ x then some x else none
  next := fun x =>
    match trySubtract x p.subtractiveCommonDifference with
    | none => none
    | some y => if p.limit ≤ y then some y else none

/-- Every element obtained from `tryGetElement` is at least the limit. -/
theorem limit_le_of_tryGetElement_eq_some (p : ArithmeticDecreasing) (index x : Peano)
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
since the subtractive common difference is at least one. -/
theorem lt_of_next_eq_some (p : ArithmeticDecreasing) (y x : Peano)
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
      have hadd : z + p.subtractiveCommonDifference = y := by
        rw [← hsub]
        exact subtract_add_cancel y p.subtractiveCommonDifference hlt
      have hz_le : successor z ≤ y := by
        rw [← add_one, ← hadd]
        exact le_add_of_le_right z (one_le' p.subtractiveCommonDifference)
      exact heq ▸ lt_of_succ_le hz_le
    · simp only [hle, ↓reduceIte] at h
      nomatch h

/-- If `tryGetElement` returns a value and the progression starts at `first`,
then `index + x ≤ successor first`. Each step decreases the value by at least
one while the index increases by one, so their sum never exceeds that of the
first element. -/
theorem add_le_succ_first_of_tryGetElement (p : ArithmeticDecreasing)
    (first index x : Peano)
    (hf : (toProgression p).first = some first)
    (h : Sequences.Progression.tryGetElement index (toProgression p) = some x) :
    index + x ≤ successor first := by
  induction index generalizing x with
  | one =>
    simp only [Sequences.Progression.tryGetElement] at h
    have heq : x = first := by
      rw [hf] at h
      injection h with heq
      exact heq.symm
    rw [heq, one_add]
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
      have hx_le : successor x ≤ y := succ_le_of_lt hlt
      have hn : n + y ≤ successor first := ih y hm
      have hmid : n + successor x ≤ n + y := le_add_of_le_right n hx_le
      have hmid' : n + successor x ≤ successor first := le_trans hmid hn
      have heqadd : successor n + x = n + successor x := by
        rw [succ_add, add_succ]
      exact heqadd ▸ hmid'

/-- The progression obtained from a decreasing arithmetic progression is finite:
if it is empty then `tryGetElement` at `one` is `none`; otherwise, starting from
`first`, `tryGetElement` at `successor first` cannot return `some`, since that
value `x` would need `successor first + x ≤ successor first`. -/
theorem toProgression_finite (p : ArithmeticDecreasing) :
    Sequences.Progression.Finite (toProgression p) := by
  match hf : (toProgression p).first with
  | none =>
    refine ⟨one, ?_⟩
    simp only [Sequences.Progression.tryGetElement, hf]
  | some first =>
    refine ⟨successor first, ?_⟩
    cases h : Sequences.Progression.tryGetElement (successor first) (toProgression p) with
    | none =>
      rfl
    | some x =>
      have hle := add_le_succ_first_of_tryGetElement p first (successor first) x hf h
      exact (not_le_of_gt (lt_add_left (successor first) x) hle).elim

/-- Length remaining from an element already known to lie in the progression,
given the room below that element down to the limit (`none` when the element
equals the limit). Computed with one division by the subtractive common
difference instead of comparing each successive term to the limit. -/
def lengthFromGap (diff : Peano) : Option Peano → CardinalNatural.Peano
  | none => CardinalNatural.Peano.one
  | some gap =>
    match divideWithRemainder gap diff with
    | (none, _) => CardinalNatural.Peano.one
    | (some q, _) => CardinalNatural.Peano.fromOrdinal (successor q)

/-- The length of a decreasing arithmetic progression: the number of elements
before `tryGetElement` first returns `none`. Uses a single comparison of the
first element to the limit and one division, avoiding a comparison at every
step of the progression. -/
def getLength (p : ArithmeticDecreasing) : CardinalNatural.Peano :=
  match p.first with
  | none => CardinalNatural.Peano.zero
  | some first =>
    match compare first p.limit with
    | .less _ => CardinalNatural.Peano.zero
    | .equal _ => CardinalNatural.Peano.one
    | .greater hlt =>
      lengthFromGap p.subtractiveCommonDifference (some (subtract first p.limit hlt))

/-- `lengthFromGap` on `gap` is the successor of `lengthFromGap` on `gap - diff`
when `diff < gap`. -/
theorem lengthFromGap_succ_of_lt (diff gap : Peano) (hlt : diff < gap) :
    lengthFromGap diff (some gap) =
      (lengthFromGap diff (some (subtract gap diff hlt))).successor := by
  have hsum : subtract gap diff hlt + diff = gap :=
    subtract_add_cancel gap diff hlt
  have hdiv := divideWithRemainder_add_right (subtract gap diff hlt) diff
  rw [hsum] at hdiv
  unfold lengthFromGap
  match hrem : divideWithRemainder (subtract gap diff hlt) diff with
  | (none, r) =>
    simp only [hrem] at hdiv
    simp only [hrem, hdiv, CardinalNatural.Peano.fromOrdinal,
      CardinalNatural.Peano.one]
  | (some q, r) =>
    simp only [hrem] at hdiv
    simp only [hrem, hdiv, CardinalNatural.Peano.fromOrdinal]

theorem next_eq_none_of_trySubtract_none (p : ArithmeticDecreasing) (x : Peano)
    (h : trySubtract x p.subtractiveCommonDifference = none) :
    (toProgression p).next x = none := by
  simp only [toProgression, h]

theorem next_eq_none_of_not_limit_le (p : ArithmeticDecreasing) (x y : Peano)
    (hs : trySubtract x p.subtractiveCommonDifference = some y)
    (h : ¬ p.limit ≤ y) :
    (toProgression p).next x = none := by
  simp only [toProgression, hs, h, ↓reduceIte]

theorem next_eq_some_of_limit_le (p : ArithmeticDecreasing) (x y : Peano)
    (hs : trySubtract x p.subtractiveCommonDifference = some y)
    (hle : p.limit ≤ y) :
    (toProgression p).next x = some y := by
  simp only [toProgression, hs, hle, ↓reduceIte]

theorem diff_lt_of_le_gap (p : ArithmeticDecreasing) (x : Peano)
    (hlt : p.limit < x)
    (hd : p.subtractiveCommonDifference ≤ subtract x p.limit hlt) :
    p.subtractiveCommonDifference < x := by
  have hsum : subtract x p.limit hlt + p.limit = x :=
    subtract_add_cancel x p.limit hlt
  have hgap_lt : subtract x p.limit hlt < subtract x p.limit hlt + p.limit :=
    lt_add_left (subtract x p.limit hlt) p.limit
  have hgap_lt' : subtract x p.limit hlt < x := by
    rw [hsum] at hgap_lt
    exact hgap_lt
  exact lt_of_le_lt hd hgap_lt'

theorem le_iff_limit_le_sub_of_lt (p : ArithmeticDecreasing) (x : Peano)
    (hlt : p.limit < x) :
    p.subtractiveCommonDifference ≤ subtract x p.limit hlt ↔
      ∃ hdiff : p.subtractiveCommonDifference < x,
        p.limit ≤ subtract x p.subtractiveCommonDifference hdiff := by
  have hsum : subtract x p.limit hlt + p.limit = x :=
    subtract_add_cancel x p.limit hlt
  have hsum' : p.limit + subtract x p.limit hlt = x :=
    (add_comm _ _).trans hsum
  constructor
  · intro hd
    refine ⟨diff_lt_of_le_gap p x hlt hd, ?_⟩
    have hle_mid := le_add_of_le_right p.limit hd
    have hle_add : p.limit + p.subtractiveCommonDifference ≤ x :=
      le_trans hle_mid (Or.inr hsum')
    have hdiff := diff_lt_of_le_gap p x hlt hd
    have hsub :
        subtract x p.subtractiveCommonDifference hdiff +
          p.subtractiveCommonDifference = x :=
      subtract_add_cancel x p.subtractiveCommonDifference hdiff
    have hrew :
        p.limit + p.subtractiveCommonDifference ≤
          subtract x p.subtractiveCommonDifference hdiff +
            p.subtractiveCommonDifference := by
      have h := hle_add
      rw [← hsub] at h
      exact h
    cases hrew with
    | inl hlt' => exact Or.inl (lt_of_add_lt_add_right hlt')
    | inr heq => exact Or.inr (add_cancel_right _ _ p.subtractiveCommonDifference heq)
  · intro ⟨hdiff, hle⟩
    have hsub :
        subtract x p.subtractiveCommonDifference hdiff +
          p.subtractiveCommonDifference = x :=
      subtract_add_cancel x p.subtractiveCommonDifference hdiff
    have hsub' :
        p.subtractiveCommonDifference +
          subtract x p.subtractiveCommonDifference hdiff = x :=
      (add_comm _ _).trans hsub
    have hle_mid := le_add_of_le_right p.subtractiveCommonDifference hle
    have hle_add : p.subtractiveCommonDifference + p.limit ≤ x :=
      le_trans hle_mid (Or.inr hsub')
    have hle_add' : p.limit + p.subtractiveCommonDifference ≤ x := by
      have h := hle_add
      rw [add_comm] at h
      exact h
    have hrew :
        p.subtractiveCommonDifference + p.limit ≤
          subtract x p.limit hlt + p.limit := by
      have h : p.subtractiveCommonDifference + p.limit ≤ x := hle_add
      rw [← hsum] at h
      exact h
    cases hrew with
    | inl hlt' => exact Or.inl (lt_of_add_lt_add_right hlt')
    | inr heq => exact Or.inr (add_cancel_right _ _ p.limit heq)

theorem limit_lt_sub_of_lt_gap (p : ArithmeticDecreasing) (x : Peano)
    (hlt : p.limit < x)
    (hdiff : p.subtractiveCommonDifference < subtract x p.limit hlt)
    (hdiff_x : p.subtractiveCommonDifference < x) :
    p.limit < subtract x p.subtractiveCommonDifference hdiff_x := by
  have hsum : subtract x p.limit hlt + p.limit = x :=
    subtract_add_cancel x p.limit hlt
  have hsum' : p.limit + subtract x p.limit hlt = x :=
    (add_comm _ _).trans hsum
  have hsub :
      subtract x p.subtractiveCommonDifference hdiff_x +
        p.subtractiveCommonDifference = x :=
    subtract_add_cancel _ _ _
  have hlt_sum : p.limit + p.subtractiveCommonDifference <
      p.limit + subtract x p.limit hlt :=
    add_lt_add_left p.limit hdiff
  have hlt_x : p.limit + p.subtractiveCommonDifference < x := by
    have h := hlt_sum
    rw [hsum'] at h
    exact h
  have hlt_sub :
      p.limit + p.subtractiveCommonDifference <
        subtract x p.subtractiveCommonDifference hdiff_x +
          p.subtractiveCommonDifference := by
    have h := hlt_x
    rw [← hsub] at h
    exact h
  exact lt_of_add_lt_add_right hlt_sub

theorem subtract_gap_eq_sub_limit (p : ArithmeticDecreasing) (x : Peano)
    (hlt : p.limit < x)
    (hdiff : p.subtractiveCommonDifference < subtract x p.limit hlt)
    (hdiff_x : p.subtractiveCommonDifference < x)
    (hlt' : p.limit < subtract x p.subtractiveCommonDifference hdiff_x) :
    subtract (subtract x p.subtractiveCommonDifference hdiff_x) p.limit hlt' =
      subtract (subtract x p.limit hlt) p.subtractiveCommonDifference hdiff := by
  have hsum : subtract x p.limit hlt + p.limit = x :=
    subtract_add_cancel x p.limit hlt
  have h1 :=
    subtract_add_cancel
      (subtract x p.subtractiveCommonDifference hdiff_x) p.limit hlt'
  have h2 :=
    subtract_add_cancel (subtract x p.limit hlt) p.subtractiveCommonDifference hdiff
  have hsub :
      subtract x p.subtractiveCommonDifference hdiff_x +
        p.subtractiveCommonDifference = x :=
    subtract_add_cancel _ _ _
  apply add_cancel_right _ _ (p.limit + p.subtractiveCommonDifference)
  have hleft :
      subtract (subtract x p.subtractiveCommonDifference hdiff_x) p.limit hlt' +
        (p.limit + p.subtractiveCommonDifference) = x := by
    rw [← add_assoc, h1, hsub]
  have hright :
      subtract (subtract x p.limit hlt) p.subtractiveCommonDifference hdiff +
        (p.limit + p.subtractiveCommonDifference) = x := by
    have h :
        subtract (subtract x p.limit hlt) p.subtractiveCommonDifference hdiff +
          (p.subtractiveCommonDifference + p.limit) = x := by
      rw [← add_assoc, h2, hsum]
    have hcomm :
        p.limit + p.subtractiveCommonDifference =
          p.subtractiveCommonDifference + p.limit :=
      add_comm _ _
    rw [hcomm]
    exact h
  exact hleft.trans hright.symm

/-- Gap below `x` down to `limit`, or `none` when `x = limit`. -/
def gapFromLimit (limit x : Peano) (hx : limit ≤ x) : Option Peano :=
  match compare x limit with
  | .less hlt => (not_le_of_gt hlt hx).elim
  | .equal _ => none
  | .greater hgt => some (subtract x limit hgt)

theorem gapFromLimit_equal {limit x : Peano} (hx : limit ≤ x) (heq : x = limit) :
    gapFromLimit limit x hx = none := by
  unfold gapFromLimit
  match hc : compare x limit with
  | .less hlt => exact (not_le_of_gt hlt hx).elim
  | .equal _ => rfl
  | .greater hgt =>
    rw [heq] at hgt
    exact (not_lt_self limit hgt).elim

theorem gapFromLimit_greater {limit x : Peano} (hx : limit ≤ x) (hlt : limit < x) :
    gapFromLimit limit x hx = some (subtract x limit hlt) := by
  unfold gapFromLimit
  match hc : compare x limit with
  | .less hlt' => exact (not_le_of_gt hlt' hx).elim
  | .equal heq =>
    rw [heq] at hlt
    exact (not_lt_self limit hlt).elim
  | .greater hgt =>
    exact congrArg some (subtract_eq_of_eq hgt hlt rfl rfl)

theorem getLengthFrom_eq_of_acc_eq {α : Type _} (next : α → Option α)
    (current : Option α) (h1 h2 : Acc (Sequences.Progression.OptionStep next) current) :
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

/-- Walking the progression from an accessible state matches `lengthFromGap` on
in-range elements, and yields zero from `none`. -/
theorem getLengthFrom_eq_lengthFromGap (p : ArithmeticDecreasing)
    (current : Option Peano)
    (hAcc : Acc (Sequences.Progression.OptionStep (toProgression p).next) current) :
    (current = none →
      Sequences.Progression.getLengthFrom (toProgression p).next current hAcc =
        CardinalNatural.Peano.zero) ∧
    (∀ x, current = some x → ∀ hx : p.limit ≤ x,
      Sequences.Progression.getLengthFrom (toProgression p).next current hAcc =
        lengthFromGap p.subtractiveCommonDifference (gapFromLimit p.limit x hx)) := by
  refine Acc.rec
    (motive := fun current hAcc =>
      (current = none →
        Sequences.Progression.getLengthFrom (toProgression p).next current hAcc =
          CardinalNatural.Peano.zero) ∧
      (∀ x, current = some x → ∀ hx : p.limit ≤ x,
        Sequences.Progression.getLengthFrom (toProgression p).next current hAcc =
          lengthFromGap p.subtractiveCommonDifference (gapFromLimit p.limit x hx)))
    (fun current hcurr ih => by
      refine ⟨?none, ?some⟩
      case none =>
        intro hnone
        subst hnone
        exact Sequences.Progression.getLengthFrom_none _ (Acc.intro _ hcurr)
      case some =>
        intro x hx_eq hx
        subst hx_eq
        have hAccx : Acc (Sequences.Progression.OptionStep (toProgression p).next)
            (some x) := Acc.intro _ hcurr
        rw [Sequences.Progression.getLengthFrom_some (toProgression p).next x hAccx]
        match hc : compare x p.limit with
        | .less hlt => exact (not_le_of_gt hlt hx).elim
        | .equal heq =>
          have hnext : (toProgression p).next x = none := by
            cases hs : trySubtract x p.subtractiveCommonDifference with
            | none =>
              exact next_eq_none_of_trySubtract_none p x hs
            | some y =>
              apply next_eq_none_of_not_limit_le p x y hs
              intro hle
              obtain ⟨hlt_diff, hsub⟩ := exists_subtract_of_trySubtract hs
              have hadd : y + p.subtractiveCommonDifference = x := by
                rw [← hsub]
                exact subtract_add_cancel x p.subtractiveCommonDifference hlt_diff
              have hlt_y : y < x := by
                rw [← hadd]
                exact lt_add_left y p.subtractiveCommonDifference
              have : p.limit < p.limit := by
                have := lt_of_le_lt hle hlt_y
                rwa [heq] at this
              exact not_lt_self p.limit this
          have hgap := gapFromLimit_equal hx heq
          have hnil := (ih ((toProgression p).next x)
            (Sequences.Progression.OptionStep.step x)).1 hnext
          have hnil' :
              Sequences.Progression.getLengthFrom (toProgression p).next
                ((toProgression p).next x)
                (hAccx.inv (Sequences.Progression.OptionStep.step x)) =
                CardinalNatural.Peano.zero := by
            rw [getLengthFrom_eq_of_acc_eq _ _ _
              (hcurr _ (Sequences.Progression.OptionStep.step x))]
            exact hnil
          simp only [hgap, lengthFromGap, hnil', CardinalNatural.Peano.one]
        | .greater hgt =>
          have hgap := gapFromLimit_greater hx hgt
          rw [hgap]
          match hd : compare p.subtractiveCommonDifference (subtract x p.limit hgt) with
          | .greater hgt' =>
            have hnext : (toProgression p).next x = none := by
              cases hs : trySubtract x p.subtractiveCommonDifference with
              | none =>
                exact next_eq_none_of_trySubtract_none p x hs
              | some y =>
                apply next_eq_none_of_not_limit_le p x y hs
                intro hle
                obtain ⟨hlt_diff, hsub⟩ := exists_subtract_of_trySubtract hs
                have hle_gap :
                    p.subtractiveCommonDifference ≤ subtract x p.limit hgt :=
                  (le_iff_limit_le_sub_of_lt p x hgt).mpr ⟨hlt_diff, by
                    rwa [hsub]⟩
                exact not_le_of_gt hgt' hle_gap
            have hnil := (ih ((toProgression p).next x)
              (Sequences.Progression.OptionStep.step x)).1 hnext
            have hnil' :
                Sequences.Progression.getLengthFrom (toProgression p).next
                  ((toProgression p).next x)
                  (hAccx.inv (Sequences.Progression.OptionStep.step x)) =
                  CardinalNatural.Peano.zero := by
              rw [getLengthFrom_eq_of_acc_eq _ _ _
                (hcurr _ (Sequences.Progression.OptionStep.step x))]
              exact hnil
            have hdiv :=
              divideWithRemainder_eq_of_none_some
                (subtract x p.limit hgt) p.subtractiveCommonDifference
                (subtract x p.limit hgt) hgt' rfl
            simp only [lengthFromGap, hnil', hdiv, CardinalNatural.Peano.one]
          | .equal heq =>
            have hle_diff :
                p.subtractiveCommonDifference ≤ subtract x p.limit hgt := Or.inr heq
            obtain ⟨hdiff, hle_y⟩ :=
              (le_iff_limit_le_sub_of_lt p x hgt).mp hle_diff
            have hs := trySubtract_of_subtract
              (z := subtract x p.subtractiveCommonDifference hdiff)
              ⟨hdiff, rfl⟩
            have hnext := next_eq_some_of_limit_le p x
              (subtract x p.subtractiveCommonDifference hdiff) hs hle_y
            have hx_next :
                subtract x p.subtractiveCommonDifference hdiff = p.limit := by
              have hsum : subtract x p.limit hgt + p.limit = x :=
                subtract_add_cancel x p.limit hgt
              have hsub :
                  subtract x p.subtractiveCommonDifference hdiff +
                    p.subtractiveCommonDifference = x :=
                subtract_add_cancel x p.subtractiveCommonDifference hdiff
              apply add_cancel_right _ _ p.subtractiveCommonDifference
              calc
                subtract x p.subtractiveCommonDifference hdiff +
                    p.subtractiveCommonDifference =
                  x := hsub
                _ = subtract x p.limit hgt + p.limit := hsum.symm
                _ = p.subtractiveCommonDifference + p.limit := by rw [← heq]
                _ = p.limit + p.subtractiveCommonDifference := add_comm _ _
            have hx_le' :
                p.limit ≤ subtract x p.subtractiveCommonDifference hdiff :=
              Or.inr hx_next.symm
            have hstep : Sequences.Progression.OptionStep (toProgression p).next
                (some (subtract x p.subtractiveCommonDifference hdiff)) (some x) :=
              hnext ▸ Sequences.Progression.OptionStep.step x
            have ih' :=
              (ih _ hstep).2 (subtract x p.subtractiveCommonDifference hdiff) rfl hx_le'
            have hgap' := gapFromLimit_equal hx_le' hx_next
            have hdiv :=
              divideWithRemainder_eq_of_some_none
                (subtract x p.limit hgt) p.subtractiveCommonDifference one (by
                  rw [← heq, multiply_one])
            have hnext_len :
                Sequences.Progression.getLengthFrom (toProgression p).next
                  ((toProgression p).next x)
                  (hAccx.inv (Sequences.Progression.OptionStep.step x)) =
                  CardinalNatural.Peano.one := by
              have htmp := ih'
              simp only [hgap', lengthFromGap] at htmp
              rw [getLengthFrom_eq_of_acc_eq _ _ _
                (hcurr _ (Sequences.Progression.OptionStep.step x))]
              simpa [hnext] using htmp
            simp only [hnext_len, lengthFromGap, hdiv,
              CardinalNatural.Peano.fromOrdinal, CardinalNatural.Peano.one]
          | .less hdiff =>
            have hle_diff :
                p.subtractiveCommonDifference ≤ subtract x p.limit hgt :=
              Or.inl hdiff
            obtain ⟨hdiff_x, hle_y⟩ :=
              (le_iff_limit_le_sub_of_lt p x hgt).mp hle_diff
            have hlt' := limit_lt_sub_of_lt_gap p x hgt hdiff hdiff_x
            have hsub := subtract_gap_eq_sub_limit p x hgt hdiff hdiff_x hlt'
            have hs := trySubtract_of_subtract
              (z := subtract x p.subtractiveCommonDifference hdiff_x)
              ⟨hdiff_x, rfl⟩
            have hnext := next_eq_some_of_limit_le p x
              (subtract x p.subtractiveCommonDifference hdiff_x) hs hle_y
            have hx_le' :
                p.limit ≤ subtract x p.subtractiveCommonDifference hdiff_x :=
              Or.inl hlt'
            have hstep : Sequences.Progression.OptionStep (toProgression p).next
                (some (subtract x p.subtractiveCommonDifference hdiff_x)) (some x) :=
              hnext ▸ Sequences.Progression.OptionStep.step x
            have ih' :=
              (ih _ hstep).2 (subtract x p.subtractiveCommonDifference hdiff_x) rfl hx_le'
            have hgap' := gapFromLimit_greater hx_le' hlt'
            have hlen :=
              lengthFromGap_succ_of_lt p.subtractiveCommonDifference
                (subtract x p.limit hgt) hdiff
            have hnext_len :
                Sequences.Progression.getLengthFrom (toProgression p).next
                  ((toProgression p).next x)
                  (hAccx.inv (Sequences.Progression.OptionStep.step x)) =
                  lengthFromGap p.subtractiveCommonDifference
                    (some (subtract (subtract x p.limit hgt)
                      p.subtractiveCommonDifference hdiff)) := by
              have htmp := ih'
              simp only [hgap'] at htmp
              rw [getLengthFrom_eq_of_acc_eq _ _ _
                (hcurr _ (Sequences.Progression.OptionStep.step x))]
              simpa [hnext, hsub] using htmp
            simp only [hnext_len, hlen])
    hAcc

/-- `getLength` agrees with walking `toProgression` via `Progression.getLength`. -/
theorem getLength_eq (p : ArithmeticDecreasing) :
    getLength p =
      Sequences.Progression.getLength (toProgression p) (toProgression_finite p) := by
  cases hf : p.first with
  | none =>
    have hfirst : (toProgression p).first = none := by
      simp only [toProgression, hf]
    change getLength p =
      Sequences.Progression.getLengthFrom (toProgression p).next (toProgression p).first
        (Sequences.Progression.acc_first_of_finite (toProgression p) (toProgression_finite p))
    simp only [getLength, hf, hfirst, Sequences.Progression.getLengthFrom_none]
  | some first =>
    cases hc : compare first p.limit with
    | less hlt =>
      have hnot : ¬ p.limit ≤ first := not_le_of_gt hlt
      have hfirst : (toProgression p).first = none := by
        simp only [toProgression, hf, hnot, ↓reduceIte]
      change getLength p =
        Sequences.Progression.getLengthFrom (toProgression p).next (toProgression p).first
          (Sequences.Progression.acc_first_of_finite (toProgression p) (toProgression_finite p))
      simp only [getLength, hf, hc, hfirst, Sequences.Progression.getLengthFrom_none]
    | equal heq =>
      have hle : p.limit ≤ first := Or.inr heq.symm
      have hfirst : (toProgression p).first = some first := by
        simp only [toProgression, hf, hle, ↓reduceIte]
      have hAcc :=
        Sequences.Progression.acc_first_of_finite (toProgression p) (toProgression_finite p)
      have hAcc' : Acc (Sequences.Progression.OptionStep (toProgression p).next)
          (some first) := hfirst ▸ hAcc
      have hx := (getLengthFrom_eq_lengthFromGap p (some first) hAcc').2 first rfl hle
      simp only [getLength, hf, hc, Sequences.Progression.getLength]
      have hwalk :
          Sequences.Progression.getLengthFrom (toProgression p).next
            (toProgression p).first hAcc =
            CardinalNatural.Peano.one := by
        rw [getLengthFrom_eq_of_current_eq _ hfirst hAcc]
        rw [getLengthFrom_eq_of_acc_eq _ _ _ hAcc']
        simpa [gapFromLimit_equal hle heq, lengthFromGap] using hx
      exact hwalk.symm
    | greater hgt =>
      have hle : p.limit ≤ first := Or.inl hgt
      have hfirst : (toProgression p).first = some first := by
        simp only [toProgression, hf, hle, ↓reduceIte]
      have hAcc :=
        Sequences.Progression.acc_first_of_finite (toProgression p) (toProgression_finite p)
      have hAcc' : Acc (Sequences.Progression.OptionStep (toProgression p).next)
          (some first) := hfirst ▸ hAcc
      have hx := (getLengthFrom_eq_lengthFromGap p (some first) hAcc').2 first rfl hle
      simp only [getLength, hf, hc, Sequences.Progression.getLength]
      have hwalk :
          Sequences.Progression.getLengthFrom (toProgression p).next
            (toProgression p).first hAcc =
            lengthFromGap p.subtractiveCommonDifference
              (some (subtract first p.limit hgt)) := by
        rw [getLengthFrom_eq_of_current_eq _ hfirst hAcc]
        rw [getLengthFrom_eq_of_acc_eq _ _ _ hAcc']
        simpa [gapFromLimit_greater hle hgt] using hx
      exact hwalk.symm

end ArithmeticDecreasing

end ZeroMath.Numbers.OrdinalNatural.Peano.Progressions
