import ZeroMath.Numbers.OrdinalNatural.Peano
import ZeroMath.Sequences.List
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

/-- Element at a positive ordinal index starting from a known first value,
retreating by the subtractive common difference with no limit comparisons. -/
def getElementFrom (first subtractiveCommonDifference : Peano) : Peano → Peano
  | .one => first
  | .successor n =>
    match trySubtract (getElementFrom first subtractiveCommonDifference n)
        subtractiveCommonDifference with
    | none => getElementFrom first subtractiveCommonDifference n
    | some y => y

/-- Shifting the start by one subtractive common difference decreases the index
by one, when that subtraction is defined. -/
theorem getElementFrom_succ (first subtractiveCommonDifference y : Peano)
    (n : Peano) (h : trySubtract first subtractiveCommonDifference = some y) :
    getElementFrom first subtractiveCommonDifference n.successor =
      getElementFrom y subtractiveCommonDifference n := by
  induction n with
  | one =>
    simp only [getElementFrom, h]
  | successor n ih =>
    change
      (match trySubtract
          (getElementFrom first subtractiveCommonDifference n.successor)
          subtractiveCommonDifference with
      | none => getElementFrom first subtractiveCommonDifference n.successor
      | some z => z) =
        (match trySubtract
          (getElementFrom y subtractiveCommonDifference n)
          subtractiveCommonDifference with
        | none => getElementFrom y subtractiveCommonDifference n
        | some z => z)
    rw [ih]

/-- If `toProgression` has no first element, the length is zero. -/
theorem getLength_eq_zero_of_toProgression_first_none
    (p : ArithmeticDecreasing)
    (h : (toProgression p).first = none) :
    getLength p = CardinalNatural.Peano.zero := by
  rw [getLength_eq]
  have hAcc :=
    Sequences.Progression.acc_first_of_finite (toProgression p) (toProgression_finite p)
  have hEq :=
    getLengthFrom_eq_of_current_eq (toProgression p).next h hAcc
  simp only [Sequences.Progression.getLength]
  rw [hEq, Sequences.Progression.getLengthFrom_none]

/-- The length bound is impossible when `toProgression` is empty. -/
theorem not_fromOrdinal_le_getLength_of_first_none
    (p : ArithmeticDecreasing) (index : Peano)
    (hle : CardinalNatural.Peano.fromOrdinal index ≤ getLength p)
    (h : (toProgression p).first = none) : False := by
  have hlen := getLength_eq_zero_of_toProgression_first_none p h
  have hle' : CardinalNatural.Peano.fromOrdinal index ≤ CardinalNatural.Peano.zero :=
    hlen ▸ hle
  exact CardinalNatural.Peano.fromOrdinal_ne_zero index
    (CardinalNatural.Peano.eq_zero_of_le_zero _ hle')

/-- A successor index within the remaining length forces a next term equal to
the current element minus the subtractive common difference. -/
theorem next_eq_some_of_succ_le_getLengthFrom (p : ArithmeticDecreasing)
    (x : Peano) (n : Peano)
    (hAcc : Acc (Sequences.Progression.OptionStep (toProgression p).next) (some x))
    (hle : CardinalNatural.Peano.fromOrdinal n.successor ≤
      Sequences.Progression.getLengthFrom (toProgression p).next (some x) hAcc) :
    ∃ y, trySubtract x p.subtractiveCommonDifference = some y ∧
      (toProgression p).next x = some y := by
  have hlen :=
    Sequences.Progression.getLengthFrom_some (toProgression p).next x hAcc
  have hle' :
      CardinalNatural.Peano.successor (CardinalNatural.Peano.fromOrdinal n) ≤
        CardinalNatural.Peano.successor
          (Sequences.Progression.getLengthFrom (toProgression p).next
            ((toProgression p).next x)
            (hAcc.inv (Sequences.Progression.OptionStep.step x))) := by
    simpa [hlen, CardinalNatural.Peano.fromOrdinal] using hle
  have hle_n := CardinalNatural.Peano.le_of_succ_le_succ hle'
  cases hnext : (toProgression p).next x with
  | none =>
    have hAcc' := hAcc.inv (Sequences.Progression.OptionStep.step x)
    have hzero :
        Sequences.Progression.getLengthFrom (toProgression p).next
          ((toProgression p).next x) hAcc' =
          CardinalNatural.Peano.zero := by
      have hEq := getLengthFrom_eq_of_current_eq (toProgression p).next hnext hAcc'
      rw [hEq, Sequences.Progression.getLengthFrom_none]
    have hle0 : CardinalNatural.Peano.fromOrdinal n ≤ CardinalNatural.Peano.zero := by
      rwa [hzero] at hle_n
    exact (CardinalNatural.Peano.fromOrdinal_ne_zero n
      (CardinalNatural.Peano.eq_zero_of_le_zero _ hle0)).elim
  | some y =>
    cases hs : trySubtract x p.subtractiveCommonDifference with
    | none =>
      have : (toProgression p).next x = none :=
        next_eq_none_of_trySubtract_none p x hs
      rw [this] at hnext
      nomatch hnext
    | some z =>
      have hprog :
          (toProgression p).next x =
            if p.limit ≤ z then some z else none := by
        simp only [toProgression, hs]
      rw [hprog] at hnext
      by_cases hle_lim : p.limit ≤ z
      · simp only [hle_lim, ↓reduceIte] at hnext
        exact ⟨z, rfl, hnext.symm⟩
      · simp only [hle_lim, ↓reduceIte] at hnext
        nomatch hnext

theorem progression_getElementFrom_eq_of_current_eq {α : Type _}
    (next : α → Option α) {c1 c2 : Option α} (hEq : c1 = c2)
    (h1 : Acc (Sequences.Progression.OptionStep next) c1)
    (index : Peano)
    (hle : CardinalNatural.Peano.fromOrdinal index ≤
      Sequences.Progression.getLengthFrom next c1 h1) :
    Sequences.Progression.getElementFrom next c1 h1 index hle =
      Sequences.Progression.getElementFrom next c2 (hEq ▸ h1) index
        (by
          have hlen := getLengthFrom_eq_of_current_eq next hEq h1
          exact hlen ▸ hle) := by
  cases hEq
  rfl

theorem progression_getElementFrom_eq_of_acc_eq {α : Type _}
    (next : α → Option α) (current : Option α)
    (h1 h2 : Acc (Sequences.Progression.OptionStep next) current)
    (index : Peano)
    (hle1 : CardinalNatural.Peano.fromOrdinal index ≤
      Sequences.Progression.getLengthFrom next current h1)
    (hle2 : CardinalNatural.Peano.fromOrdinal index ≤
      Sequences.Progression.getLengthFrom next current h2) :
    Sequences.Progression.getElementFrom next current h1 index hle1 =
      Sequences.Progression.getElementFrom next current h2 index hle2 :=
  rfl

/-- Walking `Progression.getElementFrom` from an in-range element matches
`getElementFrom` (subtractions only, no further limit comparisons). -/
theorem getElementFrom_eq_progression (p : ArithmeticDecreasing)
    (x : Peano)
    (hAcc : Acc (Sequences.Progression.OptionStep (toProgression p).next) (some x))
    (index : Peano)
    (hle : CardinalNatural.Peano.fromOrdinal index ≤
      Sequences.Progression.getLengthFrom (toProgression p).next (some x) hAcc) :
    getElementFrom x p.subtractiveCommonDifference index =
      Sequences.Progression.getElementFrom (toProgression p).next (some x) hAcc
        index hle := by
  induction index generalizing x hAcc with
  | one =>
    rfl
  | successor n ih =>
    obtain ⟨y, hs, hnext⟩ :=
      next_eq_some_of_succ_le_getLengthFrom p x n hAcc hle
    have hlen :=
      Sequences.Progression.getLengthFrom_some (toProgression p).next x hAcc
    have hle_tail :
        CardinalNatural.Peano.fromOrdinal n ≤
          Sequences.Progression.getLengthFrom (toProgression p).next
            ((toProgression p).next x)
            (hAcc.inv (Sequences.Progression.OptionStep.step x)) := by
      have hle' :
          CardinalNatural.Peano.successor
              (CardinalNatural.Peano.fromOrdinal n) ≤
            CardinalNatural.Peano.successor
              (Sequences.Progression.getLengthFrom (toProgression p).next
                ((toProgression p).next x)
                (hAcc.inv (Sequences.Progression.OptionStep.step x))) := by
        simpa [hlen, CardinalNatural.Peano.fromOrdinal] using hle
      exact CardinalNatural.Peano.le_of_succ_le_succ hle'
    have hAcc_next :
        Acc (Sequences.Progression.OptionStep (toProgression p).next) (some y) :=
      hnext ▸ hAcc.inv (Sequences.Progression.OptionStep.step x)
    have hle_next :
        CardinalNatural.Peano.fromOrdinal n ≤
          Sequences.Progression.getLengthFrom (toProgression p).next
            (some y) hAcc_next := by
      have hEq :=
        getLengthFrom_eq_of_current_eq (toProgression p).next hnext
          (hAcc.inv (Sequences.Progression.OptionStep.step x))
      rwa [← hEq]
    have ih' := ih y hAcc_next hle_next
    rw [getElementFrom_succ x p.subtractiveCommonDifference y n hs]
    change
        getElementFrom y p.subtractiveCommonDifference n =
          Sequences.Progression.getElementFrom (toProgression p).next
            ((toProgression p).next x)
            (hAcc.inv (Sequences.Progression.OptionStep.step x)) n hle_tail
    have hwalk :=
      progression_getElementFrom_eq_of_current_eq (toProgression p).next hnext
        (hAcc.inv (Sequences.Progression.OptionStep.step x)) n hle_tail
    exact ih'.trans hwalk.symm

/-- The element at the given positive ordinal index, when that index does not
exceed the progression's length. The first element has index `one`. Computed
by taking the (at most one) comparison already performed in `toProgression.first`,
then retreating by repeated subtraction of the common difference — avoiding a
limit comparison at every step of the walk. -/
def getElement (p : ArithmeticDecreasing) (index : Peano)
    (hle : CardinalNatural.Peano.fromOrdinal index ≤ getLength p) : Peano :=
  match hf : (toProgression p).first with
  | none =>
    (not_fromOrdinal_le_getLength_of_first_none p index hle hf).elim
  | some first =>
    getElementFrom first p.subtractiveCommonDifference index

/-- `getElement` agrees with walking `toProgression` via `Progression.getElement`. -/
theorem getElement_eq (p : ArithmeticDecreasing) (index : Peano)
    (hle : CardinalNatural.Peano.fromOrdinal index ≤ getLength p) :
    getElement p index hle =
      Sequences.Progression.getElement (toProgression p) (toProgression_finite p)
        index (getLength_eq p ▸ hle) := by
  dsimp only [getElement, Sequences.Progression.getElement]
  split
  · next hf =>
    exact (not_fromOrdinal_le_getLength_of_first_none p index hle hf).elim
  · next first hf =>
    have hAcc :=
      Sequences.Progression.acc_first_of_finite (toProgression p) (toProgression_finite p)
    have hAcc' :
        Acc (Sequences.Progression.OptionStep (toProgression p).next) (some first) :=
      hf ▸ hAcc
    have hle_prog :
        CardinalNatural.Peano.fromOrdinal index ≤
          Sequences.Progression.getLength (toProgression p) (toProgression_finite p) :=
      getLength_eq p ▸ hle
    have hle' :
        CardinalNatural.Peano.fromOrdinal index ≤
          Sequences.Progression.getLengthFrom (toProgression p).next (some first)
            hAcc' := by
      dsimp only [Sequences.Progression.getLength] at hle_prog
      have hEq := getLengthFrom_eq_of_current_eq (toProgression p).next hf hAcc
      rwa [hEq] at hle_prog
    have hwalk := getElementFrom_eq_progression p first hAcc' index hle'
    refine hwalk.trans ?_
    have hcur :=
      progression_getElementFrom_eq_of_current_eq (toProgression p).next hf hAcc index
        (by
          dsimp only [Sequences.Progression.getLength] at hle_prog
          exact hle_prog)
    exact (progression_getElementFrom_eq_of_acc_eq (toProgression p).next (some first)
      hAcc' (hf ▸ hAcc) index hle' _).trans hcur.symm

/-- Two decreasing arithmetic progressions are equivalent when their underlying
progressions yield related elements (equality for Peano) at every positive
ordinal index. -/
def Equivalence (p q : ArithmeticDecreasing) : Prop :=
  Sequences.Progression.Equivalence (toProgression p) (toProgression q)

instance : HasEquiv ArithmeticDecreasing where
  Equiv := Equivalence

/-- The optional first element after applying the limit filter, without building
a `Progression`. -/
def effectiveFirst (p : ArithmeticDecreasing) : Option Peano :=
  match p.first with
  | none => none
  | some x => if p.limit ≤ x then some x else none

theorem effectiveFirst_eq (p : ArithmeticDecreasing) :
    effectiveFirst p = (toProgression p).first :=
  rfl

theorem lt_of_not_le_cardinal {a b : CardinalNatural.Peano} (h : ¬ a ≤ b) : b < a := by
  cases CardinalNatural.Peano.trichotomy_or a b with
  | inl hlt =>
    exact False.elim (h (Or.inl hlt))
  | inr hrest =>
    cases hrest with
    | inl heq =>
      exact False.elim (h (Or.inr heq))
    | inr hgt =>
      exact hgt

theorem lengthFromGap_ne_zero (diff : Peano) (gap : Option Peano)
    (h : lengthFromGap diff gap = CardinalNatural.Peano.zero) : False := by
  unfold lengthFromGap at h
  match gap with
  | none =>
    change CardinalNatural.Peano.one = CardinalNatural.Peano.zero at h
    exact (CardinalNatural.Peano.successor_ne_zero _).elim h
  | some g =>
    match hdiv : divideWithRemainder g diff with
    | (none, _) =>
      change (match divideWithRemainder g diff with
        | (none, _) => CardinalNatural.Peano.one
        | (some q, _) => CardinalNatural.Peano.fromOrdinal (successor q)) =
          CardinalNatural.Peano.zero at h
      simp only [hdiv] at h
      exact (CardinalNatural.Peano.successor_ne_zero _).elim h
    | (some q, _) =>
      change (match divideWithRemainder g diff with
        | (none, _) => CardinalNatural.Peano.one
        | (some q, _) => CardinalNatural.Peano.fromOrdinal (successor q)) =
          CardinalNatural.Peano.zero at h
      simp only [hdiv] at h
      exact (CardinalNatural.Peano.successor_ne_zero _).elim h

theorem getLength_eq_zero_iff_effectiveFirst_none (p : ArithmeticDecreasing) :
    getLength p = CardinalNatural.Peano.zero ↔ effectiveFirst p = none := by
  constructor
  · intro hlen
    match hf : p.first with
    | none =>
      simp only [effectiveFirst, hf]
    | some first =>
      simp only [getLength, hf] at hlen
      match hc : compare first p.limit with
      | .less hlt =>
        simp only [effectiveFirst, hf]
        have : ¬ p.limit ≤ first := not_le_of_gt hlt
        simp only [this, ↓reduceIte]
      | .equal heq =>
        simp only [hc] at hlen
        change CardinalNatural.Peano.one = CardinalNatural.Peano.zero at hlen
        exact False.elim ((CardinalNatural.Peano.successor_ne_zero _).elim hlen)
      | .greater hgt =>
        simp only [hc] at hlen
        exact (lengthFromGap_ne_zero p.subtractiveCommonDifference _ hlen).elim
  · intro hfirst
    match hf : p.first with
    | none =>
      simp only [getLength, hf]
    | some first =>
      simp only [effectiveFirst, hf] at hfirst
      by_cases hle : p.limit ≤ first
      · simp only [hle, ↓reduceIte] at hfirst
        nomatch hfirst
      · simp only [getLength, hf]
        match hc : compare first p.limit with
        | .less _ =>
          rfl
        | .equal heq =>
          exact (hle (Or.inr heq.symm)).elim
        | .greater hgt =>
          exact (hle (Or.inl hgt)).elim

theorem not_getLength_zero_of_effectiveFirst_some (p : ArithmeticDecreasing)
    (first : Peano) (hf : effectiveFirst p = some first)
    (hlen : getLength p = CardinalNatural.Peano.zero) : False := by
  have : effectiveFirst p = none :=
    (getLength_eq_zero_iff_effectiveFirst_none p).mp hlen
  rw [this] at hf
  cases hf

/-- In-range `tryGetElement` matches `getElementFrom` on the effective first. -/
theorem tryGetElement_eq_some_getElementFrom_of_le (p : ArithmeticDecreasing)
    (first : Peano) (hf : effectiveFirst p = some first) (index : Peano)
    (hle : CardinalNatural.Peano.fromOrdinal index ≤ getLength p) :
    Sequences.Progression.tryGetElement index (toProgression p) =
      some (getElementFrom first p.subtractiveCommonDifference index) := by
  have hf' : (toProgression p).first = some first := effectiveFirst_eq p ▸ hf
  have hle' :
      CardinalNatural.Peano.fromOrdinal index ≤
        Sequences.Progression.getLength (toProgression p) (toProgression_finite p) :=
    getLength_eq p ▸ hle
  have htry :=
    Sequences.Progression.tryGetElement_eq_some_getElement (toProgression p)
      (toProgression_finite p) index hle'
  rw [htry, ← getElement_eq p index hle]
  unfold getElement
  split
  · next hfnone =>
    rw [hf'] at hfnone
    cases hfnone
  · next first' hfsome =>
    have : first' = first := by
      rw [hf'] at hfsome
      injection hfsome with hfeq
      exact hfeq.symm
    rw [this]

/-- Out-of-range `tryGetElement` is `none`. -/
theorem tryGetElement_eq_none_of_length_lt (p : ArithmeticDecreasing)
    (index : Peano)
    (hlt : getLength p < CardinalNatural.Peano.fromOrdinal index) :
    Sequences.Progression.tryGetElement index (toProgression p) = none := by
  have hlt' :
      Sequences.Progression.getLength (toProgression p) (toProgression_finite p) <
        CardinalNatural.Peano.fromOrdinal index :=
    getLength_eq p ▸ hlt
  exact Sequences.Progression.tryGetElement_eq_none_of_getLength_lt
    (toProgression p) (toProgression_finite p) index hlt'

theorem effectiveFirst_eq_some_of_pos_length (p : ArithmeticDecreasing)
    (h : getLength p ≠ CardinalNatural.Peano.zero) :
    ∃ first, effectiveFirst p = some first := by
  cases hf : effectiveFirst p with
  | none =>
    exact False.elim (h ((getLength_eq_zero_iff_effectiveFirst_none p).mpr hf))
  | some first =>
    exact ⟨first, rfl⟩

theorem le_succ_of_lt_cardinal {a b : CardinalNatural.Peano} (h : a < b) :
    a.successor ≤ b := by
  cases CardinalNatural.Peano.lt_successor_cases h with
  | inl heq =>
    exact Or.inr heq.symm
  | inr hlt =>
    exact Or.inl hlt

/-- Empty progressions are equivalent. -/
theorem equivalence_of_both_empty (p q : ArithmeticDecreasing)
    (hp : effectiveFirst p = none) (hq : effectiveFirst q = none) :
    Equivalence p q := by
  intro index
  have hp' : (toProgression p).first = none := effectiveFirst_eq p ▸ hp
  have hq' : (toProgression q).first = none := effectiveFirst_eq q ▸ hq
  change Option.Rel Eq
      (Sequences.Progression.tryGetElement index
        ⟨(toProgression p).first, (toProgression p).next⟩)
      (Sequences.Progression.tryGetElement index
        ⟨(toProgression q).first, (toProgression q).next⟩)
  simp only [hp', hq']
  have htp :=
    Sequences.Progression.tryGetElement_none_of_first_none
      (toProgression p).next index
  have htq :=
    Sequences.Progression.tryGetElement_none_of_first_none
      (toProgression q).next index
  simp only [htp, htq]
  exact Option.Rel.none

/-- Empty progressions (length zero) are equivalent. -/
theorem equivalence_of_length_zero (p q : ArithmeticDecreasing)
    (hp : getLength p = CardinalNatural.Peano.zero)
    (hq : getLength q = CardinalNatural.Peano.zero) :
    Equivalence p q :=
  equivalence_of_both_empty p q
    ((getLength_eq_zero_iff_effectiveFirst_none p).mp hp)
    ((getLength_eq_zero_iff_effectiveFirst_none q).mp hq)

/-- Length-one progressions with the same first element are equivalent. -/
theorem equivalence_of_length_one (p q : ArithmeticDecreasing) (first : Peano)
    (hp : effectiveFirst p = some first) (hq : effectiveFirst q = some first)
    (hlenP : getLength p = CardinalNatural.Peano.one)
    (hlenQ : getLength q = CardinalNatural.Peano.one) :
    Equivalence p q := by
  intro index
  match index with
  | .one =>
    have hp' : (toProgression p).first = some first := effectiveFirst_eq p ▸ hp
    have hq' : (toProgression q).first = some first := effectiveFirst_eq q ▸ hq
    change Option.Rel Eq (toProgression p).first (toProgression q).first
    simp only [hp', hq']
    exact Option.Rel.some rfl
  | .successor n =>
    have hltP :
        getLength p < CardinalNatural.Peano.fromOrdinal n.successor := by
      rw [hlenP]
      change CardinalNatural.Peano.one <
        CardinalNatural.Peano.successor (CardinalNatural.Peano.fromOrdinal n)
      exact CardinalNatural.Peano.succ_lt_succ
        (CardinalNatural.Peano.zero_lt_of_ne_zero _
          (CardinalNatural.Peano.fromOrdinal_ne_zero n))
    have hltQ :
        getLength q < CardinalNatural.Peano.fromOrdinal n.successor := by
      rw [hlenQ]
      change CardinalNatural.Peano.one <
        CardinalNatural.Peano.successor (CardinalNatural.Peano.fromOrdinal n)
      exact CardinalNatural.Peano.succ_lt_succ
        (CardinalNatural.Peano.zero_lt_of_ne_zero _
          (CardinalNatural.Peano.fromOrdinal_ne_zero n))
    have htp := tryGetElement_eq_none_of_length_lt p n.successor hltP
    have htq := tryGetElement_eq_none_of_length_lt q n.successor hltQ
    simp only [htp, htq]
    exact Option.Rel.none

/-- Progressions with the same first element, subtractive common difference, and
length are equivalent. -/
theorem equivalence_of_same_params (p q : ArithmeticDecreasing) (first : Peano)
    (hp : effectiveFirst p = some first) (hq : effectiveFirst q = some first)
    (hdiff : p.subtractiveCommonDifference = q.subtractiveCommonDifference)
    (hlen : getLength p = getLength q) :
    Equivalence p q := by
  intro index
  match (inferInstance : Decidable
      (CardinalNatural.Peano.fromOrdinal index ≤ getLength p)) with
  | isTrue hleP =>
    have hleQ :
        CardinalNatural.Peano.fromOrdinal index ≤ getLength q := hlen ▸ hleP
    have htp := tryGetElement_eq_some_getElementFrom_of_le p first hp index hleP
    have htq := tryGetElement_eq_some_getElementFrom_of_le q first hq index hleQ
    simp only [htp, htq, hdiff]
    exact Option.Rel.some rfl
  | isFalse nhleP =>
    have hltP :
        getLength p < CardinalNatural.Peano.fromOrdinal index :=
      lt_of_not_le_cardinal nhleP
    have hltQ :
        getLength q < CardinalNatural.Peano.fromOrdinal index := hlen ▸ hltP
    have htp := tryGetElement_eq_none_of_length_lt p index hltP
    have htq := tryGetElement_eq_none_of_length_lt q index hltQ
    simp only [htp, htq]
    exact Option.Rel.none

theorem effectiveFirst_eq_of_equivalence (p q : ArithmeticDecreasing)
    (h : Equivalence p q) : effectiveFirst p = effectiveFirst q := by
  generalize hfp : effectiveFirst p = fp
  generalize hfq : effectiveFirst q = fq
  have h1 := h Peano.one
  simp only [Sequences.Progression.tryGetElement, ← effectiveFirst_eq, hfp, hfq] at h1
  match fp, fq, h1 with
  | none, none, Option.Rel.none =>
    rfl
  | some x, some y, Option.Rel.some heq =>
    exact congrArg some heq

theorem getLength_eq_of_equivalence (p q : ArithmeticDecreasing)
    (h : Equivalence p q) : getLength p = getLength q := by
  cases CardinalNatural.Peano.trichotomy_or (getLength p) (getLength q) with
  | inl hlt =>
    have hne : getLength q ≠ CardinalNatural.Peano.zero := by
      intro hq0
      rw [hq0] at hlt
      exact CardinalNatural.Peano.not_lt_zero _ hlt
    obtain ⟨firstQ, hfQ⟩ := effectiveFirst_eq_some_of_pos_length q hne
    let index : Peano :=
      CardinalNatural.Peano.toOrdinal (getLength p).successor
        (CardinalNatural.Peano.successor_ne_zero _)
    have hfrom :
        CardinalNatural.Peano.fromOrdinal index = (getLength p).successor :=
      CardinalNatural.Peano.fromOrdinal_toOrdinal _ _
    have hnoneP :
        Sequences.Progression.tryGetElement index (toProgression p) = none := by
      refine tryGetElement_eq_none_of_length_lt p index ?_
      rw [hfrom]
      exact CardinalNatural.Peano.lt_successor_of_le (Or.inr rfl)
    have hleQ :
        CardinalNatural.Peano.fromOrdinal index ≤ getLength q := by
      rw [hfrom]
      exact le_succ_of_lt_cardinal hlt
    have hsomeQ :=
      tryGetElement_eq_some_getElementFrom_of_le q firstQ hfQ index hleQ
    have hrel := h index
    simp only [hnoneP, hsomeQ] at hrel
    cases hrel
  | inr hrest =>
    cases hrest with
    | inl heq =>
      exact heq
    | inr hgt =>
      have hne : getLength p ≠ CardinalNatural.Peano.zero := by
        intro hp0
        rw [hp0] at hgt
        exact CardinalNatural.Peano.not_lt_zero _ hgt
      obtain ⟨firstP, hfP⟩ := effectiveFirst_eq_some_of_pos_length p hne
      let index : Peano :=
        CardinalNatural.Peano.toOrdinal (getLength q).successor
          (CardinalNatural.Peano.successor_ne_zero _)
      have hfrom :
          CardinalNatural.Peano.fromOrdinal index = (getLength q).successor :=
        CardinalNatural.Peano.fromOrdinal_toOrdinal _ _
      have hnoneQ :
          Sequences.Progression.tryGetElement index (toProgression q) = none := by
        refine tryGetElement_eq_none_of_length_lt q index ?_
        rw [hfrom]
        exact CardinalNatural.Peano.lt_successor_of_le (Or.inr rfl)
      have hleP :
          CardinalNatural.Peano.fromOrdinal index ≤ getLength p := by
        rw [hfrom]
        exact le_succ_of_lt_cardinal hgt
      have hsomeP :=
        tryGetElement_eq_some_getElementFrom_of_le p firstP hfP index hleP
      have hrel := h index
      simp only [hsomeP, hnoneQ] at hrel
      cases hrel

theorem getElementFrom_one_succ_of_trySubtract (first diff y : Peano)
    (h : trySubtract first diff = some y) :
    getElementFrom first diff Peano.one.successor = y := by
  simp only [getElementFrom, h]

theorem subtractiveCommonDifference_eq_of_equivalence_of_length_ge_two
    (p q : ArithmeticDecreasing) (first : Peano) (n : CardinalNatural.Peano)
    (hp : effectiveFirst p = some first) (hq : effectiveFirst q = some first)
    (hlenP : getLength p =
      CardinalNatural.Peano.successor (CardinalNatural.Peano.successor n))
    (hlen : getLength p = getLength q) (h : Equivalence p q) :
    p.subtractiveCommonDifference = q.subtractiveCommonDifference := by
  have hleP :
      CardinalNatural.Peano.fromOrdinal Peano.one.successor ≤ getLength p := by
    rw [hlenP]
    change CardinalNatural.Peano.successor CardinalNatural.Peano.one ≤
      CardinalNatural.Peano.successor (CardinalNatural.Peano.successor n)
    exact CardinalNatural.Peano.succ_le_succ
      (CardinalNatural.Peano.succ_le_succ (CardinalNatural.Peano.zero_le n))
  have hleQ :
      CardinalNatural.Peano.fromOrdinal Peano.one.successor ≤ getLength q :=
    hlen ▸ hleP
  have hfP : (toProgression p).first = some first := effectiveFirst_eq p ▸ hp
  have hfQ : (toProgression q).first = some first := effectiveFirst_eq q ▸ hq
  have hAccP :=
    Sequences.Progression.acc_first_of_finite (toProgression p) (toProgression_finite p)
  have hAccQ :=
    Sequences.Progression.acc_first_of_finite (toProgression q) (toProgression_finite q)
  have hAccP' :
      Acc (Sequences.Progression.OptionStep (toProgression p).next) (some first) :=
    hfP ▸ hAccP
  have hAccQ' :
      Acc (Sequences.Progression.OptionStep (toProgression q).next) (some first) :=
    hfQ ▸ hAccQ
  have hleFromP :
      CardinalNatural.Peano.fromOrdinal Peano.one.successor ≤
        Sequences.Progression.getLengthFrom (toProgression p).next (some first)
          hAccP' := by
    have hle' :
        CardinalNatural.Peano.fromOrdinal Peano.one.successor ≤
          Sequences.Progression.getLength (toProgression p) (toProgression_finite p) :=
      getLength_eq p ▸ hleP
    dsimp only [Sequences.Progression.getLength] at hle'
    have hEq := getLengthFrom_eq_of_current_eq (toProgression p).next hfP hAccP
    rwa [hEq] at hle'
  have hleFromQ :
      CardinalNatural.Peano.fromOrdinal Peano.one.successor ≤
        Sequences.Progression.getLengthFrom (toProgression q).next (some first)
          hAccQ' := by
    have hle' :
        CardinalNatural.Peano.fromOrdinal Peano.one.successor ≤
          Sequences.Progression.getLength (toProgression q) (toProgression_finite q) :=
      getLength_eq q ▸ hleQ
    dsimp only [Sequences.Progression.getLength] at hle'
    have hEq := getLengthFrom_eq_of_current_eq (toProgression q).next hfQ hAccQ
    rwa [hEq] at hle'
  obtain ⟨yP, hsP, _⟩ :=
    next_eq_some_of_succ_le_getLengthFrom p first Peano.one hAccP' hleFromP
  obtain ⟨yQ, hsQ, _⟩ :=
    next_eq_some_of_succ_le_getLengthFrom q first Peano.one hAccQ' hleFromQ
  have htp :=
    tryGetElement_eq_some_getElementFrom_of_le p first hp Peano.one.successor hleP
  have htq :=
    tryGetElement_eq_some_getElementFrom_of_le q first hq Peano.one.successor hleQ
  have hrel := h Peano.one.successor
  simp only [htp, htq, getElementFrom_one_succ_of_trySubtract first
    p.subtractiveCommonDifference yP hsP,
    getElementFrom_one_succ_of_trySubtract first
    q.subtractiveCommonDifference yQ hsQ] at hrel
  cases hrel with
  | some heq =>
    obtain ⟨hltP, hsubP⟩ := exists_subtract_of_trySubtract hsP
    obtain ⟨hltQ, hsubQ⟩ := exists_subtract_of_trySubtract hsQ
    have hsumP :
        yP + p.subtractiveCommonDifference = first := by
      have := subtract_add_cancel first p.subtractiveCommonDifference hltP
      rw [hsubP] at this
      exact this
    have hsumQ :
        yQ + q.subtractiveCommonDifference = first := by
      have := subtract_add_cancel first q.subtractiveCommonDifference hltQ
      rw [hsubQ] at this
      exact this
    have hcancel :
        yP + p.subtractiveCommonDifference = yP + q.subtractiveCommonDifference := by
      rw [hsumP, heq, hsumQ]
    exact add_cancel_comm' hcancel

theorem getLength_ge_two_of_ne_zero_ne_one (p : ArithmeticDecreasing)
    (hne0 : getLength p ≠ CardinalNatural.Peano.zero)
    (hne1 : getLength p ≠ CardinalNatural.Peano.one) :
    ∃ n, getLength p =
      CardinalNatural.Peano.successor (CardinalNatural.Peano.successor n) := by
  revert hne0 hne1
  generalize hlen : getLength p = len
  intro hne0 hne1
  cases len with
  | zero =>
    exact (hne0 rfl).elim
  | successor m =>
    cases m with
    | zero =>
      exact (hne1 (by simp only [CardinalNatural.Peano.one])).elim
    | successor n =>
      exact ⟨n, rfl⟩

/-- Equivalence of decreasing arithmetic progressions is decidable by comparing
lengths, effective first elements, and (when the length is at least two)
subtractive common differences — without converting to `Progression` or walking
successive terms against the limit. -/
instance (p q : ArithmeticDecreasing) : Decidable (p ≈ q) :=
  let lenP := getLength p
  if hL : lenP = getLength q then
    if hZ : lenP = CardinalNatural.Peano.zero then
      isTrue (equivalence_of_length_zero p q hZ (hL ▸ hZ))
    else if hF : effectiveFirst p = effectiveFirst q then
      if hOne : lenP = CardinalNatural.Peano.one then
        match hf : effectiveFirst p with
        | none =>
          False.elim (hZ ((getLength_eq_zero_iff_effectiveFirst_none p).mpr hf))
        | some first =>
          isTrue (equivalence_of_length_one p q first hf (hF ▸ hf) hOne (hL ▸ hOne))
      else if hD : p.subtractiveCommonDifference = q.subtractiveCommonDifference then
        match hf : effectiveFirst p with
        | none =>
          False.elim (hZ ((getLength_eq_zero_iff_effectiveFirst_none p).mpr hf))
        | some first =>
          isTrue (equivalence_of_same_params p q first hf (hF ▸ hf) hD hL)
      else
        isFalse fun heq => by
          obtain ⟨first, hf⟩ := effectiveFirst_eq_some_of_pos_length p hZ
          obtain ⟨n, hlenP⟩ := getLength_ge_two_of_ne_zero_ne_one p hZ hOne
          exact hD (subtractiveCommonDifference_eq_of_equivalence_of_length_ge_two
            p q first n hf (hF ▸ hf) hlenP hL heq)
    else
      isFalse fun heq => hF (effectiveFirst_eq_of_equivalence p q heq)
  else
    isFalse fun heq => hL (getLength_eq_of_equivalence p q heq)

/-- Elements from a known start for the given remaining length, retreating by the
subtractive common difference with no limit comparisons. -/
def getElementsFrom (first subtractiveCommonDifference : Peano) :
    CardinalNatural.Peano → Sequences.List Peano
  | .zero => .empty
  | .successor n =>
    .firstElement first
      (match trySubtract first subtractiveCommonDifference with
       | none => .empty
       | some next =>
         getElementsFrom next subtractiveCommonDifference n)

/-- The ordered list of all elements of a decreasing arithmetic progression.
Empty when there is no in-range first element. Uses the effective first element
and `getLength`, then retreats by repeated subtraction of the subtractive common
difference — avoiding a limit comparison at every step. -/
def getElements (p : ArithmeticDecreasing) : Sequences.List Peano :=
  match effectiveFirst p with
  | none => .empty
  | some first =>
    getElementsFrom first p.subtractiveCommonDifference (getLength p)

/-- If `rest` continues a decreasing arithmetic progression after `prev` with
subtractive common difference `diff`, return the last element of that
progression (which is `prev` when `rest` is empty). Returns `none` when a
consecutive pair does not decrease by exactly `diff`. -/
def tryLastOfArithmeticContinuation (prev diff : Peano) :
    Sequences.List Peano → Option Peano
  | .empty => some prev
  | .firstElement x xs =>
    match trySubtract prev x with
    | none => none
    | some d =>
      if d = diff then
        tryLastOfArithmeticContinuation x diff xs
      else
        none

/-- Reconstruct a decreasing arithmetic progression from the ordered list of all
its elements. Requires a proof that at least two elements are given. Returns
`none` when the list is not strictly descending with a constant positive
subtractive common difference.

Uses the first element, the subtractive common difference between consecutive
terms, and the last element as the limit. -/
def tryFromElements :
    (elements : Sequences.List Peano) →
    CardinalNatural.Peano.two ≤ elements.length →
    Option ArithmeticDecreasing
  | .empty, hge =>
    False.elim (CardinalNatural.Peano.not_two_le_zero (by
      change CardinalNatural.Peano.two ≤ CardinalNatural.Peano.zero
      exact hge))
  | .firstElement _ .empty, hge =>
    False.elim (CardinalNatural.Peano.not_two_le_one (by
      change CardinalNatural.Peano.two ≤ CardinalNatural.Peano.one
      exact hge))
  | .firstElement x (.firstElement y ys), _ =>
    match trySubtract x y with
    | none => none
    | some diff =>
      match tryLastOfArithmeticContinuation y diff ys with
      | none => none
      | some last =>
        some {
          first := some x
          subtractiveCommonDifference := diff
          limit := last
        }

/-- Last element of a non-empty decreasing arithmetic walk of cardinal length `n`,
starting at `first` with subtractive common difference `subtractiveCommonDifference`.
For `n = zero` the value is unused (`first`). When an intermediate subtraction is
undefined the walk stops and returns the current element. -/
def lastElementFrom (first subtractiveCommonDifference : Peano) :
    CardinalNatural.Peano → Peano
  | .zero => first
  | .successor n =>
    match n with
    | .zero => first
    | .successor _ =>
      match trySubtract first subtractiveCommonDifference with
      | none => first
      | some next => lastElementFrom next subtractiveCommonDifference n

theorem lastElementFrom_one (first subtractiveCommonDifference : Peano) :
    lastElementFrom first subtractiveCommonDifference CardinalNatural.Peano.one =
      first :=
  rfl

theorem lastElementFrom_succ_succ_of_trySubtract (first subtractiveCommonDifference
    next : Peano) (n : CardinalNatural.Peano)
    (h : trySubtract first subtractiveCommonDifference = some next) :
    lastElementFrom first subtractiveCommonDifference
        (CardinalNatural.Peano.successor
          (CardinalNatural.Peano.successor n)) =
      lastElementFrom next subtractiveCommonDifference
        (CardinalNatural.Peano.successor n) := by
  simp only [lastElementFrom, h]

theorem eq_add_of_trySubtract (x y d : Peano)
    (h : trySubtract x y = some d) : x = y + d := by
  obtain ⟨hlt, hsub⟩ := exists_subtract_of_trySubtract h
  have hsum := subtract_add_cancel x y hlt
  rw [hsub] at hsum
  exact (add_comm d y) ▸ hsum.symm

theorem trySubtract_eq_diff_of_trySubtract_diff (prev diff next : Peano)
    (h : trySubtract prev diff = some next) :
    trySubtract prev next = some diff := by
  have hadd : prev = next + diff := by
    rw [add_comm]
    exact eq_add_of_trySubtract prev diff next h
  rw [hadd]
  exact trySubtract_self_add next diff

theorem getElementsFrom_succ_of_trySubtract (first subtractiveCommonDifference
    next : Peano) (n : CardinalNatural.Peano)
    (h : trySubtract first subtractiveCommonDifference = some next) :
    getElementsFrom first subtractiveCommonDifference n.successor =
      .firstElement first
        (getElementsFrom next subtractiveCommonDifference n) := by
  simp only [getElementsFrom, h]

theorem trySubtract_eq_some_of_getElementsFrom_ge_two
    (first subtractiveCommonDifference : Peano) (n : CardinalNatural.Peano)
    (hge : CardinalNatural.Peano.two ≤
      (getElementsFrom first subtractiveCommonDifference
        (CardinalNatural.Peano.successor
          (CardinalNatural.Peano.successor n))).length) :
    ∃ next, trySubtract first subtractiveCommonDifference = some next := by
  match hs : trySubtract first subtractiveCommonDifference with
  | none =>
    have hlen :
        (getElementsFrom first subtractiveCommonDifference
          (CardinalNatural.Peano.successor
            (CardinalNatural.Peano.successor n))).length =
          CardinalNatural.Peano.one := by
      simp only [getElementsFrom, hs]
      change
          Sequences.List.empty.length + CardinalNatural.Peano.one =
            CardinalNatural.Peano.one
      rfl
    rw [hlen] at hge
    exact (CardinalNatural.Peano.not_two_le_one hge).elim
  | some next =>
    exact ⟨next, rfl⟩

theorem lastElementFrom_le (first subtractiveCommonDifference : Peano)
    (n : CardinalNatural.Peano) :
    lastElementFrom first subtractiveCommonDifference n ≤ first := by
  induction n generalizing first with
  | zero =>
    exact Or.inr rfl
  | successor n ih =>
    match n with
    | .zero =>
      exact Or.inr rfl
    | .successor k =>
      match hs : trySubtract first subtractiveCommonDifference with
      | none =>
        simp only [lastElementFrom, hs]
        exact Or.inr rfl
      | some next =>
        simp only [lastElementFrom, hs]
        have hle_next := ih next
        have hadd :=
          eq_add_of_trySubtract first subtractiveCommonDifference next hs
        have hlt : next < first := by
          rw [hadd]
          exact lt_add_right subtractiveCommonDifference next
        exact le_trans hle_next (Or.inl hlt)

theorem lastElementFrom_lt_first_of_ge_two (first subtractiveCommonDifference :
    Peano) (n : CardinalNatural.Peano)
    (hge : CardinalNatural.Peano.two ≤
      (getElementsFrom first subtractiveCommonDifference
        (CardinalNatural.Peano.successor
          (CardinalNatural.Peano.successor n))).length) :
    lastElementFrom first subtractiveCommonDifference
        (CardinalNatural.Peano.successor
          (CardinalNatural.Peano.successor n)) <
      first := by
  obtain ⟨next, hs⟩ :=
    trySubtract_eq_some_of_getElementsFrom_ge_two first
      subtractiveCommonDifference n hge
  rw [lastElementFrom_succ_succ_of_trySubtract first
    subtractiveCommonDifference next _ hs]
  have hle :=
    lastElementFrom_le next subtractiveCommonDifference
      (CardinalNatural.Peano.successor n)
  have hadd :=
    eq_add_of_trySubtract first subtractiveCommonDifference next hs
  have hlt : next < first := by
    rw [hadd]
    exact lt_add_right subtractiveCommonDifference next
  exact lt_of_le_lt hle hlt

/-- Continuing a decreasing arithmetic walk from `prev` by `getElementsFrom`
recovers the last element of that walk, when the first step from `prev` is
defined. -/
theorem tryLastOfArithmeticContinuation_getElementsFrom
    (prev subtractiveCommonDifference next : Peano)
    (n : CardinalNatural.Peano)
    (h : trySubtract prev subtractiveCommonDifference = some next) :
    tryLastOfArithmeticContinuation prev subtractiveCommonDifference
        (getElementsFrom next subtractiveCommonDifference n) =
      some (lastElementFrom prev subtractiveCommonDifference n.successor) := by
  induction n generalizing prev next with
  | zero =>
    simp only [getElementsFrom, tryLastOfArithmeticContinuation]
    rfl
  | successor n ih =>
    simp only [getElementsFrom]
    match hs : trySubtract next subtractiveCommonDifference with
    | none =>
      simp only [tryLastOfArithmeticContinuation,
        trySubtract_eq_diff_of_trySubtract_diff prev
          subtractiveCommonDifference next h, ↓reduceIte]
      have hlast :
          lastElementFrom prev subtractiveCommonDifference
              (CardinalNatural.Peano.successor n.successor) =
            next := by
        rw [lastElementFrom_succ_succ_of_trySubtract prev
          subtractiveCommonDifference next _ h]
        simp only [lastElementFrom, hs]
        match n with
        | .zero => rfl
        | .successor _ => rfl
      exact congrArg some hlast.symm
    | some next' =>
      simp only [tryLastOfArithmeticContinuation,
        trySubtract_eq_diff_of_trySubtract_diff prev
          subtractiveCommonDifference next h, ↓reduceIte]
      have ih' := ih next next' hs
      rw [ih']
      have hlast :
          lastElementFrom next subtractiveCommonDifference n.successor =
            lastElementFrom prev subtractiveCommonDifference
              (CardinalNatural.Peano.successor n.successor) :=
        (lastElementFrom_succ_succ_of_trySubtract prev
          subtractiveCommonDifference next n h).symm
      exact congrArg some hlast

/-- When `getElementsFrom` yields a list of length at least two, reconstructing
recovers the start, subtractive common difference, and last element. -/
theorem tryFromElements_getElementsFrom_ge_two (first subtractiveCommonDifference :
    Peano) (n : CardinalNatural.Peano)
    (hge : CardinalNatural.Peano.two ≤
        (getElementsFrom first subtractiveCommonDifference
          (CardinalNatural.Peano.successor
            (CardinalNatural.Peano.successor n))).length) :
    tryFromElements
        (getElementsFrom first subtractiveCommonDifference
          (CardinalNatural.Peano.successor
            (CardinalNatural.Peano.successor n)))
        hge =
      some ({
        first := some first
        subtractiveCommonDifference := subtractiveCommonDifference
        limit :=
          lastElementFrom first subtractiveCommonDifference
            (CardinalNatural.Peano.successor
              (CardinalNatural.Peano.successor n))
      } : ArithmeticDecreasing) := by
  obtain ⟨next, hs⟩ :=
    trySubtract_eq_some_of_getElementsFrom_ge_two first
      subtractiveCommonDifference n hge
  have hget :
      getElementsFrom first subtractiveCommonDifference
          (CardinalNatural.Peano.successor
            (CardinalNatural.Peano.successor n)) =
        .firstElement first
          (getElementsFrom next subtractiveCommonDifference
            (CardinalNatural.Peano.successor n)) :=
    getElementsFrom_succ_of_trySubtract first subtractiveCommonDifference
      next _ hs
  revert hge
  rw [hget]
  intro hge
  simp only [getElementsFrom, tryFromElements,
    trySubtract_eq_diff_of_trySubtract_diff first
      subtractiveCommonDifference next hs]
  match hs' : trySubtract next subtractiveCommonDifference with
  | none =>
    simp only [tryLastOfArithmeticContinuation]
    have hlast :
        lastElementFrom first subtractiveCommonDifference
            (CardinalNatural.Peano.successor
              (CardinalNatural.Peano.successor n)) =
          next := by
      rw [lastElementFrom_succ_succ_of_trySubtract first
        subtractiveCommonDifference next _ hs]
      simp only [lastElementFrom, hs']
      match n with
      | .zero => rfl
      | .successor _ => rfl
    simp only [hlast]
  | some next' =>
    have hcont :=
      tryLastOfArithmeticContinuation_getElementsFrom next
        subtractiveCommonDifference next' n hs'
    simp only [hcont]
    have hlast :
        lastElementFrom next subtractiveCommonDifference n.successor =
          lastElementFrom first subtractiveCommonDifference
            (CardinalNatural.Peano.successor
              (CardinalNatural.Peano.successor n)) :=
      (lastElementFrom_succ_succ_of_trySubtract first
        subtractiveCommonDifference next n hs).symm
    simp only [hlast]

theorem list_length_firstElement {α : Type _} (x : α) (xs : Sequences.List α) :
    (Sequences.List.firstElement x xs).length = xs.length.successor :=
  CardinalNatural.Peano.add_one xs.length

/-- If a list continues a decreasing arithmetic progression after `prev`, the
recovered last element matches `lastElementFrom`, and when the first subtractive
step is defined the list equals the corresponding `getElementsFrom` walk. -/
theorem eq_getElementsFrom_of_tryLastOfArithmeticContinuation
    (prev diff : Peano) (rest : Sequences.List Peano) (last : Peano)
    (h : tryLastOfArithmeticContinuation prev diff rest = some last) :
    last =
        lastElementFrom prev diff rest.length.successor ∧
      ∀ next, trySubtract prev diff = some next →
        rest = getElementsFrom next diff rest.length := by
  induction rest generalizing prev last with
  | empty =>
    simp only [tryLastOfArithmeticContinuation] at h
    injection h with heq
    constructor
    · exact heq.symm
    · intro next _hs
      rfl
  | firstElement x xs ih =>
    simp only [tryLastOfArithmeticContinuation] at h
    match hs : trySubtract prev x with
    | none =>
      simp only [hs] at h
      nomatch h
    | some d =>
      simp only [hs] at h
      by_cases hd : d = diff
      · rw [show (if d = diff then
              tryLastOfArithmeticContinuation x diff xs
            else none) =
            tryLastOfArithmeticContinuation x diff xs from by
              simp only [hd, ↓reduceIte]] at h
        obtain ⟨hlast, hxs⟩ := ih x last h
        have hx : prev = x + diff := by
          have := eq_add_of_trySubtract prev x d hs
          rwa [hd] at this
        have hs_diff : trySubtract prev diff = some x := by
          rw [hx]
          exact trySubtract_add_right x diff
        have hlen := list_length_firstElement x xs
        constructor
        · have h1 :
              last = lastElementFrom x diff xs.length.successor :=
            hlast
          have h2 :
              lastElementFrom x diff xs.length.successor =
                lastElementFrom prev diff
                  (CardinalNatural.Peano.successor xs.length.successor) :=
            (lastElementFrom_succ_succ_of_trySubtract prev diff x
              xs.length hs_diff).symm
          have h3 :
              lastElementFrom prev diff
                  (CardinalNatural.Peano.successor xs.length.successor) =
                lastElementFrom prev diff
                  (Sequences.List.firstElement x xs).length.successor := by
            rw [hlen]
          exact h1.trans (h2.trans h3)
        · intro next hs_next
          have h1 := hs_next
          rw [hs_diff] at h1
          injection h1 with heq
          cases heq.symm
          match hsx : trySubtract x diff with
          | none =>
            have hxs_empty : xs = .empty := by
              match xs with
              | .empty => rfl
              | .firstElement y ys =>
                match hsy : trySubtract x y with
                | none =>
                  simp only [tryLastOfArithmeticContinuation, hsy] at h
                  nomatch h
                | some d' =>
                  simp only [tryLastOfArithmeticContinuation, hsy] at h
                  by_cases hd' : d' = diff
                  · have : trySubtract x diff = some y := by
                      have hx' : x = y + diff := by
                        have := eq_add_of_trySubtract x y d' hsy
                        rwa [hd'] at this
                      rw [hx']
                      exact trySubtract_add_right y diff
                    rw [hsx] at this
                    nomatch this
                  · rw [if_neg hd'] at h
                    nomatch h
            cases hxs_empty
            rw [list_length_firstElement]
            have hget :
                getElementsFrom x diff CardinalNatural.Peano.one =
                  Sequences.List.firstElement x Sequences.List.empty := by
              change
                  Sequences.List.firstElement x
                    (match trySubtract x diff with
                     | none => Sequences.List.empty
                     | some next =>
                       getElementsFrom next diff CardinalNatural.Peano.zero) =
                    Sequences.List.firstElement x Sequences.List.empty
              rw [hsx]
            exact hget.symm
          | some next' =>
            have hxs' := hxs next' hsx
            rw [list_length_firstElement]
            have hget :
                getElementsFrom x diff xs.length.successor =
                  Sequences.List.firstElement x
                    (getElementsFrom next' diff xs.length) :=
              getElementsFrom_succ_of_trySubtract x diff next' xs.length hsx
            rw [hget]
            exact congrArg (Sequences.List.firstElement x) hxs'
      · rw [if_neg hd] at h
        nomatch h

theorem lengthFromGap_self (diff : Peano) :
    lengthFromGap diff (some diff) =
      CardinalNatural.Peano.successor CardinalNatural.Peano.one := by
  unfold lengthFromGap
  simp only [divideWithRemainder_self, CardinalNatural.Peano.fromOrdinal,
    CardinalNatural.Peano.one]

theorem getLength_eq_lengthFromGap_of_gt (first subtractiveCommonDifference
    limit : Peano) (hlt : limit < first) :
    getLength {
      first := some first
      subtractiveCommonDifference := subtractiveCommonDifference
      limit := limit
    } =
      lengthFromGap subtractiveCommonDifference
        (some (subtract first limit hlt)) := by
  simp only [getLength]
  match hc : compare first limit with
  | .less hlt' => exact (not_le_of_gt hlt' (Or.inl hlt)).elim
  | .equal heq =>
    rw [heq] at hlt
    exact (not_lt_self limit hlt).elim
  | .greater hgt =>
    exact congrArg (fun g => lengthFromGap subtractiveCommonDifference (some g))
      (subtract_eq_of_eq hgt hlt rfl rfl)

theorem subtract_eq_diff_of_trySubtract (first diff next : Peano)
    (h : trySubtract first diff = some next) :
    subtract first next
        (by
          have hadd := eq_add_of_trySubtract first diff next h
          rw [hadd]
          exact lt_add_right diff next) =
      diff := by
  have hadd : first = diff + next := eq_add_of_trySubtract first diff next h
  have hlt : next < first := by
    rw [hadd]
    exact lt_add_right diff next
  apply add_cancel_right _ _ next
  have h1 := subtract_add_cancel first next hlt
  exact h1.trans hadd

theorem getElementsFrom_length_succ_of_trySubtract
    (first diff next : Peano) (n : CardinalNatural.Peano)
    (h : trySubtract first diff = some next)
    (hlen : (getElementsFrom first diff n.successor).length = n.successor) :
    (getElementsFrom next diff n).length = n := by
  have hget := getElementsFrom_succ_of_trySubtract first diff next n h
  have hlen' :
      (getElementsFrom first diff n.successor).length =
        (getElementsFrom next diff n).length.successor := by
    rw [hget]
    exact CardinalNatural.Peano.add_one _
  have hsucc :
      n.successor = (getElementsFrom next diff n).length.successor := by
    rw [← hlen', hlen]
  exact (CardinalNatural.Peano.successor_injective hsucc).symm

/-- Length of a progression whose limit is exactly `lastElementFrom` of a
full-length decreasing walk. -/
theorem getLength_lastElementFrom (first diff : Peano)
    (n : CardinalNatural.Peano) (hne : n ≠ CardinalNatural.Peano.zero)
    (hlen : (getElementsFrom first diff n).length = n) :
    getLength {
      first := some first
      subtractiveCommonDifference := diff
      limit := lastElementFrom first diff n
    } = n := by
  revert hne hlen
  induction n generalizing first with
  | zero =>
    intro hne _hlen
    exact (hne rfl).elim
  | successor n ih =>
    intro _hne hlen
    cases n with
    | zero =>
      change
          getLength {
            first := some first
            subtractiveCommonDifference := diff
            limit := first
          } =
            CardinalNatural.Peano.one
      simp only [getLength]
      match hc : compare first first with
      | .greater hgt => exact (not_lt_self first hgt).elim
      | .equal _ => rfl
      | .less hlt => exact (not_lt_self first hlt).elim
    | successor m =>
      have hge : CardinalNatural.Peano.two ≤
          (getElementsFrom first diff
            (CardinalNatural.Peano.successor
              (CardinalNatural.Peano.successor m))).length := by
        rw [hlen]
        change
            CardinalNatural.Peano.two ≤
              CardinalNatural.Peano.successor
                (CardinalNatural.Peano.successor m)
        simpa only [CardinalNatural.Peano.two, CardinalNatural.Peano.one] using
          (CardinalNatural.Peano.succ_le_succ
            (CardinalNatural.Peano.succ_le_succ
              (CardinalNatural.Peano.zero_le m)))
      obtain ⟨next, hs⟩ :=
        trySubtract_eq_some_of_getElementsFrom_ge_two first diff m hge
      have hlast_eq :=
        lastElementFrom_succ_succ_of_trySubtract first diff next m hs
      have hlen_tail :
          (getElementsFrom next diff
            (CardinalNatural.Peano.successor m)).length =
            CardinalNatural.Peano.successor m :=
        getElementsFrom_length_succ_of_trySubtract first diff next
          (CardinalNatural.Peano.successor m) hs hlen
      cases m with
      | zero =>
        have hlt : next < first := by
          have hadd := eq_add_of_trySubtract first diff next hs
          rw [hadd]
          exact lt_add_right diff next
        have hget :=
          getLength_eq_lengthFromGap_of_gt first diff next hlt
        have hgap : subtract first next hlt = diff :=
          subtract_eq_diff_of_trySubtract first diff next hs
        change
            getLength {
              first := some first
              subtractiveCommonDifference := diff
              limit :=
                lastElementFrom first diff
                  (CardinalNatural.Peano.successor
                    (CardinalNatural.Peano.successor CardinalNatural.Peano.zero))
            } =
              CardinalNatural.Peano.successor CardinalNatural.Peano.one
        rw [hlast_eq]
        change
            getLength {
              first := some first
              subtractiveCommonDifference := diff
              limit := next
            } =
              CardinalNatural.Peano.successor CardinalNatural.Peano.one
        rw [hget, hgap, lengthFromGap_self]
      | successor k =>
        have hlt_last :
            lastElementFrom next diff
                (CardinalNatural.Peano.successor
                  (CardinalNatural.Peano.successor k)) <
              next :=
          lastElementFrom_lt_first_of_ge_two next diff k (by
            rw [hlen_tail]
            change
                CardinalNatural.Peano.two ≤
                  CardinalNatural.Peano.successor
                    (CardinalNatural.Peano.successor k)
            simpa only [CardinalNatural.Peano.two, CardinalNatural.Peano.one] using
              (CardinalNatural.Peano.succ_le_succ
                (CardinalNatural.Peano.succ_le_succ
                  (CardinalNatural.Peano.zero_le k))))
        have hlt_first : next < first := by
          have hadd := eq_add_of_trySubtract first diff next hs
          rw [hadd]
          exact lt_add_right diff next
        have hlt : lastElementFrom first diff
            (CardinalNatural.Peano.successor
              (CardinalNatural.Peano.successor k.successor)) <
            first := by
          rw [hlast_eq]
          exact lt_trans hlt_last hlt_first
        have hget :=
          getLength_eq_lengthFromGap_of_gt first diff
            (lastElementFrom first diff
              (CardinalNatural.Peano.successor
                (CardinalNatural.Peano.successor k.successor)))
            hlt
        have hlen' :
            getLength {
              first := some next
              subtractiveCommonDifference := diff
              limit :=
                lastElementFrom next diff
                  (CardinalNatural.Peano.successor
                    (CardinalNatural.Peano.successor k))
            } =
              CardinalNatural.Peano.successor
                (CardinalNatural.Peano.successor k) :=
          ih next (CardinalNatural.Peano.successor_ne_zero _) hlen_tail
        have hlt_next :
            lastElementFrom next diff
                (CardinalNatural.Peano.successor
                  (CardinalNatural.Peano.successor k)) <
              first :=
          lt_trans hlt_last hlt_first
        -- gap first - last = (next - last) + diff, so lengthFromGap succ
        have hdiff_lt :
            diff <
              subtract first
                (lastElementFrom first diff
                  (CardinalNatural.Peano.successor
                    (CardinalNatural.Peano.successor k.successor)))
                hlt := by
          have hlast' :
              lastElementFrom first diff
                  (CardinalNatural.Peano.successor
                    (CardinalNatural.Peano.successor k.successor)) =
                lastElementFrom next diff
                  (CardinalNatural.Peano.successor
                    (CardinalNatural.Peano.successor k)) :=
            hlast_eq
          have hsum :
              subtract first
                  (lastElementFrom first diff
                    (CardinalNatural.Peano.successor
                      (CardinalNatural.Peano.successor k.successor)))
                  hlt +
                lastElementFrom first diff
                  (CardinalNatural.Peano.successor
                    (CardinalNatural.Peano.successor k.successor)) =
              first :=
            subtract_add_cancel _ _ _
          have hadd := eq_add_of_trySubtract first diff next hs
          -- first = diff + next > diff + last, so diff < first - last
          have : diff +
              lastElementFrom first diff
                (CardinalNatural.Peano.successor
                  (CardinalNatural.Peano.successor k.successor)) <
              first := by
            rw [hlast', hadd]
            exact add_lt_add_left diff hlt_last
          have hrew :
              diff +
                  lastElementFrom first diff
                    (CardinalNatural.Peano.successor
                      (CardinalNatural.Peano.successor k.successor)) <
                subtract first
                    (lastElementFrom first diff
                      (CardinalNatural.Peano.successor
                        (CardinalNatural.Peano.successor k.successor)))
                    hlt +
                  lastElementFrom first diff
                    (CardinalNatural.Peano.successor
                      (CardinalNatural.Peano.successor k.successor)) :=
            hsum.symm ▸ this
          exact lt_of_add_lt_add_right hrew
        have hgap_succ :=
          lengthFromGap_succ_of_lt diff
            (subtract first
              (lastElementFrom first diff
                (CardinalNatural.Peano.successor
                  (CardinalNatural.Peano.successor k.successor)))
              hlt)
            hdiff_lt
        have hdiff_first : diff < first := by
          have hadd := eq_add_of_trySubtract first diff next hs
          rw [hadd]
          exact lt_add_left diff next
        have hsub_next : subtract first diff hdiff_first = next := by
          have hadd := eq_add_of_trySubtract first diff next hs
          have h1 := subtract_add_cancel first diff hdiff_first
          have h2 : next + diff = first := by
            rw [hadd, add_comm]
          exact add_cancel_right _ _ diff (h1.trans h2.symm)
        have hlt_sub :
            lastElementFrom first diff
                (CardinalNatural.Peano.successor
                  (CardinalNatural.Peano.successor k.successor)) <
              subtract first diff hdiff_first := by
          rw [hsub_next, hlast_eq]
          exact hlt_last
        let pTmp : ArithmeticDecreasing :=
          {
            first := some first
            subtractiveCommonDifference := diff
            limit :=
              lastElementFrom first diff
                (CardinalNatural.Peano.successor
                  (CardinalNatural.Peano.successor k.successor))
          }
        have hsub_eq :=
          subtract_gap_eq_sub_limit pTmp first hlt hdiff_lt hdiff_first hlt_sub
        have hget_next :=
          getLength_eq_lengthFromGap_of_gt next diff
            (lastElementFrom next diff
              (CardinalNatural.Peano.successor
                (CardinalNatural.Peano.successor k)))
            hlt_last
        change
            getLength {
              first := some first
              subtractiveCommonDifference := diff
              limit :=
                lastElementFrom first diff
                  (CardinalNatural.Peano.successor
                    (CardinalNatural.Peano.successor k.successor))
            } =
              CardinalNatural.Peano.successor
                (CardinalNatural.Peano.successor
                  (CardinalNatural.Peano.successor k))
        rw [hget, hgap_succ]
        have htail :
            lengthFromGap diff
                (some
                  (subtract
                    (subtract first
                      (lastElementFrom first diff
                        (CardinalNatural.Peano.successor
                          (CardinalNatural.Peano.successor k.successor)))
                      hlt)
                    diff hdiff_lt)) =
              getLength {
                first := some next
                subtractiveCommonDifference := diff
                limit :=
                  lastElementFrom next diff
                    (CardinalNatural.Peano.successor
                      (CardinalNatural.Peano.successor k))
              } := by
          rw [hget_next]
          apply congrArg (lengthFromGap diff)
          apply congrArg some
          have hlt_sub' :
              lastElementFrom first diff
                  (CardinalNatural.Peano.successor
                    (CardinalNatural.Peano.successor k.successor)) <
                next := by
            have := hlt_sub
            rwa [hsub_next] at this
          have hmid :
              subtract
                  (subtract first
                    (lastElementFrom first diff
                      (CardinalNatural.Peano.successor
                        (CardinalNatural.Peano.successor k.successor)))
                    hlt)
                  diff hdiff_lt =
                subtract (subtract first diff hdiff_first)
                  (lastElementFrom first diff
                    (CardinalNatural.Peano.successor
                      (CardinalNatural.Peano.successor k.successor)))
                  hlt_sub :=
            hsub_eq.symm
          have hmid' :
              subtract (subtract first diff hdiff_first)
                  (lastElementFrom first diff
                    (CardinalNatural.Peano.successor
                      (CardinalNatural.Peano.successor k.successor)))
                  hlt_sub =
                subtract next
                  (lastElementFrom first diff
                    (CardinalNatural.Peano.successor
                      (CardinalNatural.Peano.successor k.successor)))
                  hlt_sub' :=
            subtract_eq_of_eq hlt_sub hlt_sub' hsub_next rfl
          have hend :
              subtract next
                  (lastElementFrom first diff
                    (CardinalNatural.Peano.successor
                      (CardinalNatural.Peano.successor k.successor)))
                  hlt_sub' =
                subtract next
                  (lastElementFrom next diff
                    (CardinalNatural.Peano.successor
                      (CardinalNatural.Peano.successor k)))
                  hlt_last :=
            subtract_eq_of_eq hlt_sub' hlt_last rfl hlast_eq
          exact hmid.trans (hmid'.trans hend)
        rw [htail, hlen']

theorem effectiveFirst_lastElementFrom (first diff : Peano)
    (n : CardinalNatural.Peano) (_hne : n ≠ CardinalNatural.Peano.zero) :
    effectiveFirst {
      first := some first
      subtractiveCommonDifference := diff
      limit := lastElementFrom first diff n
    } = some first := by
  simp only [effectiveFirst]
  have hle := lastElementFrom_le first diff n
  simp only [hle, ↓reduceIte]

/-- `getElements` recovers the original list from a successful
`tryFromElements`. -/
theorem getElements_tryFromElements (elements : Sequences.List Peano)
    (hge : CardinalNatural.Peano.two ≤ elements.length)
    (p : ArithmeticDecreasing)
    (h : tryFromElements elements hge = some p) :
    getElements p = elements := by
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
    match hs : trySubtract x y with
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
          simp only [tryLastOfArithmeticContinuation, hs, ↓reduceIte, hl]
        obtain ⟨hlast, hrest_forall⟩ :=
          eq_getElementsFrom_of_tryLastOfArithmeticContinuation x diff
            (Sequences.List.firstElement y ys) last hcont
        have hs_diff : trySubtract x diff = some y := by
          rw [eq_add_of_trySubtract x y diff hs]
          exact trySubtract_add_right y diff
        have hrest := hrest_forall y hs_diff
        have hne :
            (Sequences.List.firstElement y ys).length.successor ≠
              CardinalNatural.Peano.zero :=
          CardinalNatural.Peano.successor_ne_zero _
        have hle : last ≤ x := by
          have :=
            lastElementFrom_le x diff
              (Sequences.List.firstElement y ys).length.successor
          rwa [← hlast] at this
        have hf : effectiveFirst
            {
              first := some x
              subtractiveCommonDifference := diff
              limit := last
            } = some x := by
          simp only [effectiveFirst, hle, ↓reduceIte]
        have hlen_walk :
            (getElementsFrom x diff
              (Sequences.List.firstElement y ys).length.successor).length =
              (Sequences.List.firstElement y ys).length.successor := by
          have hget :
              getElementsFrom x diff
                  (Sequences.List.firstElement y ys).length.successor =
                Sequences.List.firstElement x
                  (getElementsFrom y diff
                    (Sequences.List.firstElement y ys).length) :=
            getElementsFrom_succ_of_trySubtract x diff y _ hs_diff
          rw [hget, ← hrest]
          exact list_length_firstElement x _
        have hlenp :
            getLength
                {
                  first := some x
                  subtractiveCommonDifference := diff
                  limit := last
                } =
              (Sequences.List.firstElement y ys).length.successor := by
          rw [hlast]
          exact getLength_lastElementFrom x diff
            (Sequences.List.firstElement y ys).length.successor hne hlen_walk
        simp only [getElements, hf, hlenp]
        have hget :
            getElementsFrom x diff
                (Sequences.List.firstElement y ys).length.successor =
              Sequences.List.firstElement x
                (Sequences.List.firstElement y ys) := by
          have h1 :=
            getElementsFrom_succ_of_trySubtract x diff y
              (Sequences.List.firstElement y ys).length hs_diff
          exact h1.trans (congrArg (Sequences.List.firstElement x) hrest.symm)
        exact hget

/-- A length of at least two forces a defined subtractive step from the effective
first element that stays at least the limit. -/
theorem trySubtract_eq_some_of_getLength_ge_two (p : ArithmeticDecreasing)
    (first : Peano) (hf : effectiveFirst p = some first)
    (hge : CardinalNatural.Peano.two ≤ getLength p) :
    ∃ next, trySubtract first p.subtractiveCommonDifference = some next ∧
      p.limit ≤ next := by
  have hf' : (toProgression p).first = some first := effectiveFirst_eq p ▸ hf
  have hAcc :=
    Sequences.Progression.acc_first_of_finite (toProgression p) (toProgression_finite p)
  have hAcc' :
      Acc (Sequences.Progression.OptionStep (toProgression p).next) (some first) :=
    hf' ▸ hAcc
  have hleP :
      CardinalNatural.Peano.fromOrdinal Peano.one.successor ≤ getLength p := by
    simpa only [CardinalNatural.Peano.fromOrdinal, CardinalNatural.Peano.two,
      CardinalNatural.Peano.one] using hge
  have hleFrom :
      CardinalNatural.Peano.fromOrdinal Peano.one.successor ≤
        Sequences.Progression.getLengthFrom (toProgression p).next (some first)
          hAcc' := by
    have hle' :
        CardinalNatural.Peano.fromOrdinal Peano.one.successor ≤
          Sequences.Progression.getLength (toProgression p) (toProgression_finite p) :=
      getLength_eq p ▸ hleP
    dsimp only [Sequences.Progression.getLength] at hle'
    have hEq := getLengthFrom_eq_of_current_eq (toProgression p).next hf' hAcc
    rwa [hEq] at hle'
  obtain ⟨y, hs, hnext⟩ :=
    next_eq_some_of_succ_le_getLengthFrom p first Peano.one hAcc' hleFrom
  refine ⟨y, hs, ?_⟩
  have hprog :
      (toProgression p).next first =
        if p.limit ≤ y then some y else none := by
    simp only [toProgression, hs]
  rw [hprog] at hnext
  by_cases hle : p.limit ≤ y
  · exact hle
  · simp only [hle, ↓reduceIte] at hnext
    nomatch hnext

/-- Stepping from the effective first to the next in-range term decreases
`getLength` by one. -/
theorem getLength_succ_of_next (p : ArithmeticDecreasing) (first next : Peano)
    (hf : effectiveFirst p = some first)
    (hs : trySubtract first p.subtractiveCommonDifference = some next)
    (hle_lim : p.limit ≤ next) :
    getLength p =
      (getLength {
        first := some next
        subtractiveCommonDifference := p.subtractiveCommonDifference
        limit := p.limit
      }).successor := by
  let p' : ArithmeticDecreasing :=
    {
      first := some next
      subtractiveCommonDifference := p.subtractiveCommonDifference
      limit := p.limit
    }
  have hf' : (toProgression p).first = some first := effectiveFirst_eq p ▸ hf
  have hnext : (toProgression p).next first = some next :=
    next_eq_some_of_limit_le p first next hs hle_lim
  have hf_p' : (toProgression p').first = some next := by
    simp only [toProgression, p', hle_lim, ↓reduceIte]
  have hAcc :=
    Sequences.Progression.acc_first_of_finite (toProgression p) (toProgression_finite p)
  have hAcc' :
      Acc (Sequences.Progression.OptionStep (toProgression p).next) (some first) :=
    hf' ▸ hAcc
  have hAcc_p' :=
    Sequences.Progression.acc_first_of_finite (toProgression p') (toProgression_finite p')
  have hAcc_p'' :
      Acc (Sequences.Progression.OptionStep (toProgression p').next) (some next) :=
    hf_p' ▸ hAcc_p'
  rw [getLength_eq p, getLength_eq p']
  dsimp only [Sequences.Progression.getLength]
  have hwalk :
      Sequences.Progression.getLengthFrom (toProgression p).next
          (toProgression p).first hAcc =
        Sequences.Progression.getLengthFrom (toProgression p).next (some first)
          hAcc' :=
    getLengthFrom_eq_of_current_eq (toProgression p).next hf' hAcc
  have hwalk' :
      Sequences.Progression.getLengthFrom (toProgression p').next
          (toProgression p').first hAcc_p' =
        Sequences.Progression.getLengthFrom (toProgression p').next (some next)
          hAcc_p'' :=
    getLengthFrom_eq_of_current_eq (toProgression p').next hf_p' hAcc_p'
  rw [hwalk, hwalk']
  have hlen_succ :=
    Sequences.Progression.getLengthFrom_some (toProgression p).next first hAcc'
  rw [hlen_succ]
  apply congrArg CardinalNatural.Peano.successor
  have hAcc_step := hAcc'.inv (Sequences.Progression.OptionStep.step first)
  have hEq_cur :
      Sequences.Progression.getLengthFrom (toProgression p).next
          ((toProgression p).next first) hAcc_step =
        Sequences.Progression.getLengthFrom (toProgression p).next (some next)
          (hnext ▸ hAcc_step) :=
    getLengthFrom_eq_of_current_eq (toProgression p).next hnext hAcc_step
  rw [hEq_cur]
  have hnext_fun :
      (toProgression p').next = (toProgression p).next := by
    funext x
    simp only [toProgression, p']
  cases hnext_fun
  exact getLengthFrom_eq_of_acc_eq (toProgression p).next (some next)
    (hnext ▸ hAcc_step) hAcc_p''

/-- `getElementsFrom` of an in-range initial segment has the requested length. -/
theorem getElementsFrom_length_of_le_getLength (p : ArithmeticDecreasing)
    (first : Peano) (hf : effectiveFirst p = some first)
    (n : CardinalNatural.Peano) (hle : n ≤ getLength p) :
    (getElementsFrom first p.subtractiveCommonDifference n).length = n := by
  induction n generalizing p first with
  | zero =>
    rfl
  | successor n ih =>
    cases n with
    | zero =>
      have hget :
          getElementsFrom first p.subtractiveCommonDifference
              (CardinalNatural.Peano.successor CardinalNatural.Peano.zero) =
            Sequences.List.firstElement first
              (match trySubtract first p.subtractiveCommonDifference with
               | none => Sequences.List.empty
               | some next =>
                 getElementsFrom next p.subtractiveCommonDifference
                   CardinalNatural.Peano.zero) :=
        rfl
      rw [hget]
      match trySubtract first p.subtractiveCommonDifference with
      | none => rfl
      | some _ => rfl
    | successor m =>
      have hge : CardinalNatural.Peano.two ≤ getLength p :=
        CardinalNatural.Peano.le_trans
          (by
            change
                CardinalNatural.Peano.two ≤
                  CardinalNatural.Peano.successor
                    (CardinalNatural.Peano.successor m)
            simpa only [CardinalNatural.Peano.two, CardinalNatural.Peano.one] using
              (CardinalNatural.Peano.succ_le_succ
                (CardinalNatural.Peano.succ_le_succ
                  (CardinalNatural.Peano.zero_le m))))
          hle
      obtain ⟨next, hs, hle_lim⟩ :=
        trySubtract_eq_some_of_getLength_ge_two p first hf hge
      have hget :=
        getElementsFrom_succ_of_trySubtract first p.subtractiveCommonDifference
          next (CardinalNatural.Peano.successor m) hs
      let p' : ArithmeticDecreasing :=
        {
          first := some next
          subtractiveCommonDifference := p.subtractiveCommonDifference
          limit := p.limit
        }
      have hf' : effectiveFirst p' = some next := by
        simp only [effectiveFirst, p', hle_lim, ↓reduceIte]
      have hlen_succ := getLength_succ_of_next p first next hf hs hle_lim
      have hle' :
          CardinalNatural.Peano.successor m ≤ getLength p' := by
        have : CardinalNatural.Peano.successor
            (CardinalNatural.Peano.successor m) ≤ getLength p := hle
        have hform :
            getLength p = (getLength p').successor := hlen_succ
        rw [hform] at this
        exact CardinalNatural.Peano.le_of_succ_le_succ this
      have ih' := ih p' next hf' hle'
      rw [hget]
      change
          (getElementsFrom next p.subtractiveCommonDifference
            (CardinalNatural.Peano.successor m)).length +
              CardinalNatural.Peano.one =
            CardinalNatural.Peano.successor
              (CardinalNatural.Peano.successor m)
      -- `p'` and `p` share the subtractive common difference.
      have ih'' :
          (getElementsFrom next p.subtractiveCommonDifference
            (CardinalNatural.Peano.successor m)).length =
            CardinalNatural.Peano.successor m := by
        change
            (getElementsFrom next p'.subtractiveCommonDifference
              (CardinalNatural.Peano.successor m)).length =
              CardinalNatural.Peano.successor m at ih'
        exact ih'
      rw [ih'', CardinalNatural.Peano.add_one]

theorem getElements_length (p : ArithmeticDecreasing) :
    (getElements p).length = getLength p := by
  match hf : effectiveFirst p with
  | none =>
    have hlen : getLength p = CardinalNatural.Peano.zero :=
      (getLength_eq_zero_iff_effectiveFirst_none p).mpr hf
    simp only [getElements, hf, hlen]
    rfl
  | some first =>
    simp only [getElements, hf]
    exact getElementsFrom_length_of_le_getLength p first hf (getLength p)
      (Or.inr rfl)

/-- `tryFromElements` recovers a progression equivalent to `p` from
`getElements p` when `p` has length at least two. -/
theorem tryFromElements_getElements (p : ArithmeticDecreasing)
    (hge : CardinalNatural.Peano.two ≤ getLength p) :
    ∃ (hLen : CardinalNatural.Peano.two ≤ (getElements p).length)
      (q : ArithmeticDecreasing),
      tryFromElements (getElements p) hLen = some q ∧ p ≈ q := by
  obtain ⟨m, hlen⟩ :=
    CardinalNatural.Peano.eq_succ_succ_of_two_le (getLength p) hge
  have hne0 : getLength p ≠ CardinalNatural.Peano.zero := by
    intro heq
    rw [heq] at hge
    exact CardinalNatural.Peano.not_two_le_zero hge
  obtain ⟨first, hf⟩ := effectiveFirst_eq_some_of_pos_length p hne0
  have hget :
      getElements p =
        getElementsFrom first p.subtractiveCommonDifference (getLength p) := by
    simp only [getElements, hf]
  have hLen : CardinalNatural.Peano.two ≤ (getElements p).length := by
    rw [getElements_length]
    exact hge
  let last :=
    lastElementFrom first p.subtractiveCommonDifference
      (CardinalNatural.Peano.successor
        (CardinalNatural.Peano.successor m))
  let q : ArithmeticDecreasing :=
    {
      first := some first
      subtractiveCommonDifference := p.subtractiveCommonDifference
      limit := last
    }
  refine ⟨hLen, q, ?_⟩
  constructor
  · have hlen_walk :
        (getElementsFrom first p.subtractiveCommonDifference
          (CardinalNatural.Peano.successor
            (CardinalNatural.Peano.successor m))).length =
          CardinalNatural.Peano.successor
            (CardinalNatural.Peano.successor m) := by
      have := getElementsFrom_length_of_le_getLength p first hf
        (CardinalNatural.Peano.successor
          (CardinalNatural.Peano.successor m))
        (by rw [hlen]; exact Or.inr rfl)
      exact this
    have hge' : CardinalNatural.Peano.two ≤
        (getElementsFrom first p.subtractiveCommonDifference
          (CardinalNatural.Peano.successor
            (CardinalNatural.Peano.successor m))).length := by
      rw [hlen_walk]
      change
          CardinalNatural.Peano.two ≤
            CardinalNatural.Peano.successor
              (CardinalNatural.Peano.successor m)
      simpa only [CardinalNatural.Peano.two, CardinalNatural.Peano.one] using
        (CardinalNatural.Peano.succ_le_succ
          (CardinalNatural.Peano.succ_le_succ
            (CardinalNatural.Peano.zero_le m)))
    have htry :=
      tryFromElements_getElementsFrom_ge_two first
        p.subtractiveCommonDifference m hge'
    have hget' :
        getElements p =
          getElementsFrom first p.subtractiveCommonDifference
            (CardinalNatural.Peano.successor
              (CardinalNatural.Peano.successor m)) := by
      rw [hget, hlen]
    revert hLen
    rw [hget']
    intro hLen
    exact htry
  · have hfq :=
      effectiveFirst_lastElementFrom first p.subtractiveCommonDifference
        (CardinalNatural.Peano.successor
          (CardinalNatural.Peano.successor m))
        (CardinalNatural.Peano.successor_ne_zero _)
    have hlen_walk :
        (getElementsFrom first p.subtractiveCommonDifference
          (CardinalNatural.Peano.successor
            (CardinalNatural.Peano.successor m))).length =
          CardinalNatural.Peano.successor
            (CardinalNatural.Peano.successor m) := by
      have := getElementsFrom_length_of_le_getLength p first hf
        (CardinalNatural.Peano.successor
          (CardinalNatural.Peano.successor m))
        (by rw [hlen]; exact Or.inr rfl)
      exact this
    have hlenq :=
      getLength_lastElementFrom first p.subtractiveCommonDifference
        (CardinalNatural.Peano.successor
          (CardinalNatural.Peano.successor m))
        (CardinalNatural.Peano.successor_ne_zero _) hlen_walk
    exact equivalence_of_same_params p q first hf hfq rfl
      (by rw [hlen, hlenq])

/-- Recover the first element of a decreasing arithmetic progression from an
element at the given ordinal index and the subtractive common difference. At
index `one` the element is itself the first; otherwise add
`(predecessor index) * subtractiveCommonDifference`. Always succeeds. -/
def tryFirstFromIndexedElement (index element subtractiveCommonDifference : Peano) :
    Option Peano :=
  match index with
  | .one => some element
  | .successor n => some (element + n * subtractiveCommonDifference)

/-- Given two ordered indexed elements (`index < index'`) of a prospective
decreasing arithmetic progression, recover the subtractive common difference
`(element - element') / (index' - index)`. Returns `none` when the elements are
not strictly descending or the element gap is not divisible by the index gap. -/
def tryCommonDifferenceFromOrderedIndexedElements
    (index element index' element' : Peano) (hlt : index < index') :
    Option Peano :=
  match trySubtract element element' with
  | none => none
  | some elementDiff =>
    tryDivide elementDiff (subtract index' index hlt)

/-- Reconstruct a decreasing arithmetic progression from two of its elements at
different ordinal indexes together with the progression length. Returns `none`
when either index exceeds the length, when the arithmetic walk of that length
cannot be carried out (an intermediate subtraction fails), or when the values
are not consistent with a strictly decreasing arithmetic progression of that
length.

The reconstructed progression uses the recovered first element and subtractive
common difference, and takes the last element of an arithmetic walk of the given
length as the limit. -/
def tryFromTwoElementsAndLength
    (index1 : Peano) (element1 : Peano)
    (index2 : Peano) (element2 : Peano)
    (length : CardinalNatural.Peano)
    (hne : index1 ≠ index2) :
    Option ArithmeticDecreasing :=
  if CardinalNatural.Peano.fromOrdinal index1 ≤ length then
    if CardinalNatural.Peano.fromOrdinal index2 ≤ length then
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
            if (getElementsFrom first diff length).length = length then
              some {
                first := some first
                subtractiveCommonDifference := diff
                limit := lastElementFrom first diff length
              }
            else
              none
      | .greater hgt =>
        match tryCommonDifferenceFromOrderedIndexedElements
            index2 element2 index1 element1 hgt with
        | none => none
        | some diff =>
          match tryFirstFromIndexedElement index2 element2 diff with
          | none => none
          | some first =>
            if (getElementsFrom first diff length).length = length then
              some {
                first := some first
                subtractiveCommonDifference := diff
                limit := lastElementFrom first diff length
              }
            else
              none
    else
      none
  else
    none

theorem getElementFrom_one (first subtractiveCommonDifference : Peano) :
    getElementFrom first subtractiveCommonDifference one = first :=
  rfl

/-- The closed form of `getElementFrom` at a successor index, when
`(predecessor index) * subtractiveCommonDifference` can be subtracted from
`first`. -/
theorem getElementFrom_eq_sub_mul (first subtractiveCommonDifference n y : Peano)
    (h : trySubtract first (n * subtractiveCommonDifference) = some y) :
    getElementFrom first subtractiveCommonDifference n.successor = y := by
  induction n generalizing y with
  | one =>
    have h' : trySubtract first subtractiveCommonDifference = some y := by
      simpa [one_multiply] using h
    simp only [getElementFrom, h']
  | successor m ih =>
    have hadd :
        first = m.successor * subtractiveCommonDifference + y :=
      eq_add_of_trySubtract first (m.successor * subtractiveCommonDifference) y h
    have hadd_comm :
        first = y + m.successor * subtractiveCommonDifference := by
      rw [hadd, add_comm]
    have hmul :
        m.successor * subtractiveCommonDifference =
          m * subtractiveCommonDifference + subtractiveCommonDifference := by
      rw [succ_multiply]
    have hadd' :
        first =
          (y + subtractiveCommonDifference) +
            (m * subtractiveCommonDifference) := by
      rw [hadd_comm, hmul, add_comm (m * subtractiveCommonDifference),
        ← add_assoc]
    have hmid :
        trySubtract first (m * subtractiveCommonDifference) =
          some (y + subtractiveCommonDifference) := by
      rw [hadd']
      exact trySubtract_add_right (y + subtractiveCommonDifference)
        (m * subtractiveCommonDifference)
    have ih' := ih (y + subtractiveCommonDifference) hmid
    have hs :
        trySubtract (y + subtractiveCommonDifference) subtractiveCommonDifference =
          some y :=
      trySubtract_add_right y subtractiveCommonDifference
    change
      (match trySubtract
          (getElementFrom first subtractiveCommonDifference m.successor)
          subtractiveCommonDifference with
      | none => getElementFrom first subtractiveCommonDifference m.successor
      | some z => z) =
        y
    rw [ih', hs]

/-- Recovering the first element from an indexed element is left-inverse to
`getElementFrom` at that index. -/
theorem getElementFrom_of_tryFirstFromIndexedElement
    (index element subtractiveCommonDifference first : Peano)
    (h : tryFirstFromIndexedElement index element subtractiveCommonDifference =
      some first) :
    getElementFrom first subtractiveCommonDifference index = element := by
  match index with
  | .one =>
    simp only [tryFirstFromIndexedElement] at h
    injection h with heq
    rw [getElementFrom_one, ← heq]
  | .successor n =>
    simp only [tryFirstFromIndexedElement] at h
    injection h with heq
    have hs :
        trySubtract (element + n * subtractiveCommonDifference)
          (n * subtractiveCommonDifference) =
          some element :=
      trySubtract_add_right element (n * subtractiveCommonDifference)
    rw [← heq]
    exact getElementFrom_eq_sub_mul
      (element + n * subtractiveCommonDifference)
      subtractiveCommonDifference n element hs

/-- A successful common-difference recovery implies the earlier element equals
the later plus the index gap times that difference. -/
theorem eq_sub_mul_of_tryCommonDifferenceFromOrderedIndexedElements
    (index element index' element' : Peano) (hlt : index < index')
    (diff : Peano)
    (h : tryCommonDifferenceFromOrderedIndexedElements
        index element index' element' hlt = some diff) :
    element =
      element' + (subtract index' index hlt) * diff := by
  simp only [tryCommonDifferenceFromOrderedIndexedElements] at h
  match hs : trySubtract element element' with
  | none =>
    simp only [hs] at h
    nomatch h
  | some elementDiff =>
    simp only [hs] at h
    have hmul : (subtract index' index hlt) * diff = elementDiff :=
      eq_of_tryDivide_mul h
    have hadd : element = element' + elementDiff :=
      eq_add_of_trySubtract element element' elementDiff hs
    rw [hadd, hmul]

/-- When both indexed recoveries succeed, `getElementFrom` returns each original
element. -/
theorem getElementFrom_of_tryFirst_tryCommonDifference
    (index element index' element' : Peano) (hlt : index < index')
    (diff first : Peano)
    (hdiff : tryCommonDifferenceFromOrderedIndexedElements
        index element index' element' hlt = some diff)
    (hfirst : tryFirstFromIndexedElement index element diff = some first) :
    getElementFrom first diff index = element ∧
      getElementFrom first diff index' = element' := by
  have h1 :=
    getElementFrom_of_tryFirstFromIndexedElement index element diff first hfirst
  refine ⟨h1, ?_⟩
  have hgap :=
    eq_sub_mul_of_tryCommonDifferenceFromOrderedIndexedElements
      index element index' element' hlt diff hdiff
  match index, index' with
  | .one, .one =>
    exact (not_lt_self one hlt).elim
  | .one, .successor n =>
    simp only [tryFirstFromIndexedElement] at hfirst
    injection hfirst with heq
    have hsub : subtract n.successor one hlt = n := subtract_succ_one n hlt
    have hs :
        trySubtract first (n * diff) = some element' := by
      rw [← heq, hgap, hsub]
      exact trySubtract_add_right element' (n * diff)
    exact getElementFrom_eq_sub_mul first diff n element' hs
  | .successor m, .one =>
    exact (not_lt_one m.successor hlt).elim
  | .successor m, .successor n =>
    simp only [tryFirstFromIndexedElement] at hfirst
    injection hfirst with heq
    have hlt' : m < n := lt_of_succ_lt_succ hlt
    have hsub :
        subtract n.successor m.successor hlt = subtract n m hlt' := by
      change subtract n m (lt_of_succ_lt_succ hlt) = subtract n m hlt'
      exact subtract_eq_of_eq _ _ rfl rfl
    have hsum : m + subtract n m hlt' = n := by
      rw [add_comm]
      exact subtract_add_cancel n m hlt'
    have hmul :
        (subtract n.successor m.successor hlt) * diff + m * diff =
          n * diff := by
      rw [hsub]
      have hdist :
          (m + subtract n m hlt') * diff =
            m * diff + (subtract n m hlt') * diff := by
        rw [multiply_comm (m + subtract n m hlt') diff, multiply_add,
          multiply_comm diff m, multiply_comm diff (subtract n m hlt')]
      calc
        (subtract n m hlt') * diff + m * diff
            = m * diff + (subtract n m hlt') * diff := by rw [add_comm]
        _ = (m + subtract n m hlt') * diff := by rw [← hdist]
        _ = n * diff := by rw [hsum]
    have hs :
        trySubtract first (n * diff) = some element' := by
      rw [← heq, hgap]
      have hadd :
          element' + (subtract n.successor m.successor hlt) * diff +
              m * diff =
            element' + n * diff := by
        rw [add_assoc, hmul]
      rw [hadd]
      exact trySubtract_add_right element' (n * diff)
    exact getElementFrom_eq_sub_mul first diff n element' hs

/-- `getElement` on a progression whose limit is `lastElementFrom` of positive
length (with a full arithmetic walk) agrees with `getElementFrom`. -/
theorem getElement_lastElementFrom (first subtractiveCommonDifference : Peano)
    (n : CardinalNatural.Peano) (hne : n ≠ CardinalNatural.Peano.zero)
    (_hlen : (getElementsFrom first subtractiveCommonDifference n).length = n)
    (index : Peano)
    (hle : CardinalNatural.Peano.fromOrdinal index ≤
      getLength {
        first := some first
        subtractiveCommonDifference := subtractiveCommonDifference
        limit := lastElementFrom first subtractiveCommonDifference n
      }) :
    getElement
      {
        first := some first
        subtractiveCommonDifference := subtractiveCommonDifference
        limit := lastElementFrom first subtractiveCommonDifference n
      }
      index hle =
      getElementFrom first subtractiveCommonDifference index := by
  have hfirst :
      (toProgression
        {
          first := some first
          subtractiveCommonDifference := subtractiveCommonDifference
          limit := lastElementFrom first subtractiveCommonDifference n
        }).first =
        some first := by
    change effectiveFirst
        {
          first := some first
          subtractiveCommonDifference := subtractiveCommonDifference
          limit := lastElementFrom first subtractiveCommonDifference n
        } =
      some first
    exact effectiveFirst_lastElementFrom first subtractiveCommonDifference n hne
  dsimp only [getElement]
  split
  · next hf =>
    rw [hfirst] at hf
    nomatch hf
  · next first' hf =>
    have heq : some first = some first' := hfirst.symm.trans hf
    injection heq with heq'
    rw [← heq']

theorem length_ne_zero_of_tryFromTwoElementsAndLength
    (index1 element1 index2 element2 : Peano)
    (length : CardinalNatural.Peano)
    (hne : index1 ≠ index2)
    (p : ArithmeticDecreasing)
    (h : tryFromTwoElementsAndLength index1 element1 index2 element2 length hne =
      some p) :
    length ≠ CardinalNatural.Peano.zero := by
  intro hzero
  simp only [tryFromTwoElementsAndLength] at h
  by_cases hle1 : CardinalNatural.Peano.fromOrdinal index1 ≤ length
  · have : CardinalNatural.Peano.fromOrdinal index1 ≤ CardinalNatural.Peano.zero :=
      hzero ▸ hle1
    exact CardinalNatural.Peano.fromOrdinal_ne_zero index1
      (CardinalNatural.Peano.eq_zero_of_le_zero _ this)
  · simp only [hle1, ↓reduceIte] at h
    nomatch h

/-- A successful `tryFromTwoElementsAndLength` yields a progression whose
`getLength` is the given length and whose `getElement` at each of the two
indexes recovers the corresponding original element. -/
theorem getLength_getElement_of_tryFromTwoElementsAndLength
    (index1 element1 index2 element2 : Peano)
    (length : CardinalNatural.Peano)
    (hne : index1 ≠ index2)
    (p : ArithmeticDecreasing)
    (h : tryFromTwoElementsAndLength index1 element1 index2 element2 length hne =
      some p) :
    getLength p = length ∧
      (∃ (hle1 : CardinalNatural.Peano.fromOrdinal index1 ≤ getLength p),
        getElement p index1 hle1 = element1) ∧
      (∃ (hle2 : CardinalNatural.Peano.fromOrdinal index2 ≤ getLength p),
        getElement p index2 hle2 = element2) := by
  have hlen_ne :=
    length_ne_zero_of_tryFromTwoElementsAndLength
      index1 element1 index2 element2 length hne p h
  simp only [tryFromTwoElementsAndLength] at h
  by_cases hle1 : CardinalNatural.Peano.fromOrdinal index1 ≤ length
  · simp only [hle1, ↓reduceIte] at h
    by_cases hle2 : CardinalNatural.Peano.fromOrdinal index2 ≤ length
    · simp only [hle2, ↓reduceIte] at h
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
            by_cases hwalk :
                (getElementsFrom first diff length).length = length
            · simp only [hwalk, ↓reduceIte] at h
              injection h with hp
              subst hp
              have hget :=
                getElementFrom_of_tryFirst_tryCommonDifference
                  index1 element1 index2 element2 hlt diff first hd hf
              have hlenp :=
                getLength_lastElementFrom first diff length hlen_ne hwalk
              have hle1p :
                  CardinalNatural.Peano.fromOrdinal index1 ≤
                    getLength {
                      first := some first
                      subtractiveCommonDifference := diff
                      limit := lastElementFrom first diff length
                    } := by
                rwa [hlenp]
              have hle2p :
                  CardinalNatural.Peano.fromOrdinal index2 ≤
                    getLength {
                      first := some first
                      subtractiveCommonDifference := diff
                      limit := lastElementFrom first diff length
                    } := by
                rwa [hlenp]
              refine ⟨hlenp, ⟨hle1p, ?_⟩, ⟨hle2p, ?_⟩⟩
              · exact
                  (getElement_lastElementFrom first diff length hlen_ne hwalk
                    index1 hle1p).trans hget.1
              · exact
                  (getElement_lastElementFrom first diff length hlen_ne hwalk
                    index2 hle2p).trans hget.2
            · simp only [hwalk, ↓reduceIte] at h
              nomatch h
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
            by_cases hwalk :
                (getElementsFrom first diff length).length = length
            · simp only [hwalk, ↓reduceIte] at h
              injection h with hp
              subst hp
              have hget :=
                getElementFrom_of_tryFirst_tryCommonDifference
                  index2 element2 index1 element1 hgt diff first hd hf
              have hlenp :=
                getLength_lastElementFrom first diff length hlen_ne hwalk
              have hle1p :
                  CardinalNatural.Peano.fromOrdinal index1 ≤
                    getLength {
                      first := some first
                      subtractiveCommonDifference := diff
                      limit := lastElementFrom first diff length
                    } := by
                rwa [hlenp]
              have hle2p :
                  CardinalNatural.Peano.fromOrdinal index2 ≤
                    getLength {
                      first := some first
                      subtractiveCommonDifference := diff
                      limit := lastElementFrom first diff length
                    } := by
                rwa [hlenp]
              refine ⟨hlenp, ⟨hle1p, ?_⟩, ⟨hle2p, ?_⟩⟩
              · exact
                  (getElement_lastElementFrom first diff length hlen_ne hwalk
                    index1 hle1p).trans hget.2
              · exact
                  (getElement_lastElementFrom first diff length hlen_ne hwalk
                    index2 hle2p).trans hget.1
            · simp only [hwalk, ↓reduceIte] at h
              nomatch h
    · simp only [hle2, ↓reduceIte] at h
      nomatch h
  · simp only [hle1, ↓reduceIte] at h
    nomatch h

/-- In-range `getElement` agrees with `getElementFrom` on the effective first. -/
theorem getElement_eq_getElementFrom (p : ArithmeticDecreasing)
    (first : Peano) (hf : effectiveFirst p = some first) (index : Peano)
    (hle : CardinalNatural.Peano.fromOrdinal index ≤ getLength p) :
    getElement p index hle =
      getElementFrom first p.subtractiveCommonDifference index := by
  dsimp only [getElement]
  split
  · next hfnone =>
    have hf' : (toProgression p).first = some first := effectiveFirst_eq p ▸ hf
    rw [hf'] at hfnone
    nomatch hfnone
  · next first' hfsome =>
    have hf' : (toProgression p).first = some first := effectiveFirst_eq p ▸ hf
    have heq : some first = some first' := hf'.symm.trans hfsome
    injection heq with heq'
    rw [← heq']

/-- Consecutive in-range elements differ by exactly the subtractive common
difference. -/
theorem trySubtract_getElementFrom_succ_of_le (p : ArithmeticDecreasing)
    (first : Peano) (hf : effectiveFirst p = some first) (index : Peano)
    (hle : CardinalNatural.Peano.fromOrdinal index.successor ≤ getLength p) :
    trySubtract
        (getElementFrom first p.subtractiveCommonDifference index)
        p.subtractiveCommonDifference =
      some (getElementFrom first p.subtractiveCommonDifference index.successor) := by
  induction index generalizing p first with
  | one =>
    have hf' : (toProgression p).first = some first := effectiveFirst_eq p ▸ hf
    have hAcc :=
      Sequences.Progression.acc_first_of_finite (toProgression p)
        (toProgression_finite p)
    have hAcc' :
        Acc (Sequences.Progression.OptionStep (toProgression p).next)
          (some first) :=
      hf' ▸ hAcc
    have hleFrom :
        CardinalNatural.Peano.fromOrdinal Peano.one.successor ≤
          Sequences.Progression.getLengthFrom (toProgression p).next
            (some first) hAcc' := by
      have hle' :
          CardinalNatural.Peano.fromOrdinal Peano.one.successor ≤
            Sequences.Progression.getLength (toProgression p)
              (toProgression_finite p) :=
        getLength_eq p ▸ hle
      dsimp only [Sequences.Progression.getLength] at hle'
      have hEq :=
        getLengthFrom_eq_of_current_eq (toProgression p).next hf' hAcc
      rwa [hEq] at hle'
    obtain ⟨y, hs, _hnext⟩ :=
      next_eq_some_of_succ_le_getLengthFrom p first Peano.one hAcc' hleFrom
    simp only [getElementFrom_one, getElementFrom_one_succ_of_trySubtract first
      p.subtractiveCommonDifference y hs, hs]
  | successor n ih =>
    have hge : CardinalNatural.Peano.two ≤ getLength p := by
      refine CardinalNatural.Peano.le_trans ?_ hle
      change
          CardinalNatural.Peano.two ≤
            CardinalNatural.Peano.fromOrdinal n.successor.successor
      simpa only [CardinalNatural.Peano.fromOrdinal, CardinalNatural.Peano.two,
        CardinalNatural.Peano.one] using
        (CardinalNatural.Peano.succ_le_succ
          (CardinalNatural.Peano.succ_le_succ
            (CardinalNatural.Peano.zero_le
              (CardinalNatural.Peano.fromOrdinal n))))
    obtain ⟨next, hs, hle_lim⟩ :=
      trySubtract_eq_some_of_getLength_ge_two p first hf hge
    let p' : ArithmeticDecreasing :=
      {
        first := some next
        subtractiveCommonDifference := p.subtractiveCommonDifference
        limit := p.limit
      }
    have hf' : effectiveFirst p' = some next := by
      simp only [effectiveFirst, p', hle_lim, ↓reduceIte]
    have hlen_succ := getLength_succ_of_next p first next hf hs hle_lim
    have hle' :
        CardinalNatural.Peano.fromOrdinal n.successor ≤ getLength p' := by
      have hform : getLength p = (getLength p').successor := hlen_succ
      have :
          CardinalNatural.Peano.fromOrdinal n.successor.successor ≤
            getLength p :=
        hle
      rw [hform] at this
      change
          CardinalNatural.Peano.successor
              (CardinalNatural.Peano.fromOrdinal n.successor) ≤
            (getLength p').successor at this
      exact CardinalNatural.Peano.le_of_succ_le_succ this
    have ih' := ih p' next hf' hle'
    have hget_n :=
      getElementFrom_succ first p.subtractiveCommonDifference next n hs
    have hget_ns :=
      getElementFrom_succ first p.subtractiveCommonDifference next n.successor hs
    rw [hget_n, hget_ns]
    exact ih'

/-- `fromOrdinal` is monotone. -/
theorem fromOrdinal_le_of_lt {a b : Peano} (h : a < b) :
    CardinalNatural.Peano.fromOrdinal a ≤
      CardinalNatural.Peano.fromOrdinal b := by
  induction h with
  | base =>
    exact Or.inl CardinalNatural.Peano.LessThan.base
  | step _ ih =>
    exact CardinalNatural.Peano.le_trans ih
      (Or.inl CardinalNatural.Peano.LessThan.base)

/-- Closed form: an in-range successor index is the start minus
`(predecessor index) * subtractiveCommonDifference`. -/
theorem trySubtract_mul_eq_getElementFrom_succ (p : ArithmeticDecreasing)
    (first : Peano) (hf : effectiveFirst p = some first) (n : Peano)
    (hle : CardinalNatural.Peano.fromOrdinal n.successor ≤ getLength p) :
    trySubtract first (n * p.subtractiveCommonDifference) =
      some (getElementFrom first p.subtractiveCommonDifference n.successor) := by
  induction n with
  | one =>
    have hstep :=
      trySubtract_getElementFrom_succ_of_le p first hf Peano.one hle
    simpa [getElementFrom_one, one_multiply] using hstep
  | successor m ih =>
    have hle_m :
        CardinalNatural.Peano.fromOrdinal m.successor ≤ getLength p := by
      refine CardinalNatural.Peano.le_trans ?_ hle
      exact fromOrdinal_le_of_lt LessThan.base
    have ih' := ih hle_m
    have hstep :=
      trySubtract_getElementFrom_succ_of_le p first hf m.successor hle
    let mid := getElementFrom first p.subtractiveCommonDifference m.successor
    let last :=
      getElementFrom first p.subtractiveCommonDifference m.successor.successor
    have hadd_mid : first = mid + m * p.subtractiveCommonDifference :=
      (eq_add_of_trySubtract first (m * p.subtractiveCommonDifference) mid ih').trans
        (add_comm _ _)
    have hadd_step : mid = last + p.subtractiveCommonDifference :=
      (eq_add_of_trySubtract mid p.subtractiveCommonDifference last hstep).trans
        (add_comm _ _)
    have hadd_last :
        first = last + m.successor * p.subtractiveCommonDifference := by
      calc
        first = mid + m * p.subtractiveCommonDifference := hadd_mid
        _ = (last + p.subtractiveCommonDifference) +
              m * p.subtractiveCommonDifference := by rw [hadd_step]
        _ = last + (p.subtractiveCommonDifference +
              m * p.subtractiveCommonDifference) := by rw [add_assoc]
        _ = last + (m * p.subtractiveCommonDifference +
              p.subtractiveCommonDifference) := by
                rw [add_comm p.subtractiveCommonDifference]
        _ = last + m.successor * p.subtractiveCommonDifference := by
                rw [← succ_multiply]
    show trySubtract first (m.successor * p.subtractiveCommonDifference) =
      some last
    rw [hadd_last]
    exact trySubtract_add_right last (m.successor * p.subtractiveCommonDifference)

/-- Advancing from `index` to a larger in-range `index'` subtracts
`(index' - index) * subtractiveCommonDifference` from the element. -/
theorem getElementFrom_eq_add_mul_of_lt (p : ArithmeticDecreasing)
    (first : Peano) (hf : effectiveFirst p = some first)
    (index index' : Peano) (hlt : index < index')
    (hle' : CardinalNatural.Peano.fromOrdinal index' ≤ getLength p) :
    getElementFrom first p.subtractiveCommonDifference index =
      getElementFrom first p.subtractiveCommonDifference index' +
        (subtract index' index hlt) * p.subtractiveCommonDifference := by
  match index, index' with
  | .one, .one =>
    exact (not_lt_self one hlt).elim
  | .one, .successor n =>
    have hsub : subtract n.successor one hlt = n := subtract_succ_one n hlt
    have hclosed :=
      trySubtract_mul_eq_getElementFrom_succ p first hf n hle'
    have hadd :
        first =
          getElementFrom first p.subtractiveCommonDifference n.successor +
            n * p.subtractiveCommonDifference :=
      (eq_add_of_trySubtract first (n * p.subtractiveCommonDifference)
          (getElementFrom first p.subtractiveCommonDifference n.successor)
          hclosed).trans
        (add_comm _ _)
    rw [getElementFrom_one, hsub]
    exact hadd
  | .successor m, .one =>
    exact (not_lt_one m.successor hlt).elim
  | .successor m, .successor n =>
    have hlt' : m < n := lt_of_succ_lt_succ hlt
    have hsub :
        subtract n.successor m.successor hlt = subtract n m hlt' := by
      change subtract n m (lt_of_succ_lt_succ hlt) = subtract n m hlt'
      exact subtract_eq_of_eq _ _ rfl rfl
    have hle_m :
        CardinalNatural.Peano.fromOrdinal m.successor ≤ getLength p :=
      CardinalNatural.Peano.le_trans
        (by
          change
              (CardinalNatural.Peano.fromOrdinal m).successor ≤
                (CardinalNatural.Peano.fromOrdinal n).successor
          exact CardinalNatural.Peano.succ_le_succ
            (fromOrdinal_le_of_lt hlt'))
        hle'
    have hclosed_m :=
      trySubtract_mul_eq_getElementFrom_succ p first hf m hle_m
    have hclosed_n :=
      trySubtract_mul_eq_getElementFrom_succ p first hf n hle'
    have hadd_m :
        first =
          getElementFrom first p.subtractiveCommonDifference m.successor +
            m * p.subtractiveCommonDifference :=
      (eq_add_of_trySubtract first (m * p.subtractiveCommonDifference)
          (getElementFrom first p.subtractiveCommonDifference m.successor)
          hclosed_m).trans
        (add_comm _ _)
    have hadd_n :
        first =
          getElementFrom first p.subtractiveCommonDifference n.successor +
            n * p.subtractiveCommonDifference :=
      (eq_add_of_trySubtract first (n * p.subtractiveCommonDifference)
          (getElementFrom first p.subtractiveCommonDifference n.successor)
          hclosed_n).trans
        (add_comm _ _)
    have hsum : m + subtract n m hlt' = n := by
      rw [add_comm]
      exact subtract_add_cancel n m hlt'
    have hdist :
        (m + subtract n m hlt') * p.subtractiveCommonDifference =
          m * p.subtractiveCommonDifference +
            (subtract n m hlt') * p.subtractiveCommonDifference := by
      rw [multiply_comm (m + subtract n m hlt'), multiply_add,
        multiply_comm p.subtractiveCommonDifference m,
        multiply_comm p.subtractiveCommonDifference (subtract n m hlt')]
    have hcancel :
        getElementFrom first p.subtractiveCommonDifference m.successor +
            m * p.subtractiveCommonDifference =
          getElementFrom first p.subtractiveCommonDifference n.successor +
            n * p.subtractiveCommonDifference :=
      hadd_m.symm.trans hadd_n
    have hgoal :
        getElementFrom first p.subtractiveCommonDifference m.successor =
          getElementFrom first p.subtractiveCommonDifference n.successor +
            (subtract n m hlt') * p.subtractiveCommonDifference := by
      apply add_cancel_right _ _
        (m * p.subtractiveCommonDifference)
      calc
        getElementFrom first p.subtractiveCommonDifference m.successor +
              m * p.subtractiveCommonDifference
            = getElementFrom first p.subtractiveCommonDifference n.successor +
                n * p.subtractiveCommonDifference := hcancel
        _ = getElementFrom first p.subtractiveCommonDifference n.successor +
              (m + subtract n m hlt') * p.subtractiveCommonDifference := by
                rw [hsum]
        _ = getElementFrom first p.subtractiveCommonDifference n.successor +
              (m * p.subtractiveCommonDifference +
                (subtract n m hlt') * p.subtractiveCommonDifference) := by
                rw [hdist]
        _ =
          (getElementFrom first p.subtractiveCommonDifference n.successor +
              (subtract n m hlt') * p.subtractiveCommonDifference) +
            m * p.subtractiveCommonDifference := by
          rw [add_assoc, add_comm (m * p.subtractiveCommonDifference),
            ← add_assoc]
    rw [hsub]
    exact hgoal

/-- Recovering the common difference from two in-range indexed elements of a
decreasing arithmetic progression returns its subtractive common difference. -/
theorem tryCommonDifferenceFromOrderedIndexedElements_getElementFrom
    (p : ArithmeticDecreasing) (first : Peano)
    (hf : effectiveFirst p = some first)
    (index index' : Peano) (hlt : index < index')
    (hle' : CardinalNatural.Peano.fromOrdinal index' ≤ getLength p) :
    tryCommonDifferenceFromOrderedIndexedElements
      index (getElementFrom first p.subtractiveCommonDifference index)
      index' (getElementFrom first p.subtractiveCommonDifference index') hlt =
      some p.subtractiveCommonDifference := by
  simp only [tryCommonDifferenceFromOrderedIndexedElements]
  have heq :=
    getElementFrom_eq_add_mul_of_lt p first hf index index' hlt hle'
  have hsub :
      trySubtract
        (getElementFrom first p.subtractiveCommonDifference index)
        (getElementFrom first p.subtractiveCommonDifference index') =
      some ((subtract index' index hlt) * p.subtractiveCommonDifference) := by
    rw [heq]
    exact trySubtract_self_add _ _
  simp only [hsub]
  exact tryDivide_mul p.subtractiveCommonDifference (subtract index' index hlt)

/-- Recovering the first element from an in-range indexed element of a decreasing
arithmetic progression returns its effective first element. -/
theorem tryFirstFromIndexedElement_getElementFrom
    (p : ArithmeticDecreasing) (first : Peano)
    (hf : effectiveFirst p = some first) (index : Peano)
    (hle : CardinalNatural.Peano.fromOrdinal index ≤ getLength p) :
    tryFirstFromIndexedElement index
      (getElementFrom first p.subtractiveCommonDifference index)
      p.subtractiveCommonDifference =
      some first := by
  match index with
  | .one =>
    simp only [tryFirstFromIndexedElement, getElementFrom_one]
  | .successor n =>
    simp only [tryFirstFromIndexedElement]
    have hclosed :=
      trySubtract_mul_eq_getElementFrom_succ p first hf n hle
    have hadd :
        getElementFrom first p.subtractiveCommonDifference n.successor +
            n * p.subtractiveCommonDifference =
          first :=
      ((eq_add_of_trySubtract first (n * p.subtractiveCommonDifference)
            (getElementFrom first p.subtractiveCommonDifference n.successor)
            hclosed).trans
          (add_comm _ _)).symm
    exact congrArg some hadd

/-- Reconstructing from any two distinct in-range elements of `p`, together with
`getLength p`, yields a progression equivalent to `p`. -/
theorem tryFromTwoElementsAndLength_getElement
    (p : ArithmeticDecreasing)
    (index1 index2 : Peano)
    (hne : index1 ≠ index2)
    (hle1 : CardinalNatural.Peano.fromOrdinal index1 ≤ getLength p)
    (hle2 : CardinalNatural.Peano.fromOrdinal index2 ≤ getLength p) :
    ∃ (q : ArithmeticDecreasing),
      tryFromTwoElementsAndLength
        index1 (getElement p index1 hle1)
        index2 (getElement p index2 hle2)
        (getLength p) hne = some q ∧
      p ≈ q := by
  have hne0 : getLength p ≠ CardinalNatural.Peano.zero := by
    intro hzero
    have : CardinalNatural.Peano.fromOrdinal index1 ≤ CardinalNatural.Peano.zero :=
      hzero ▸ hle1
    exact CardinalNatural.Peano.fromOrdinal_ne_zero index1
      (CardinalNatural.Peano.eq_zero_of_le_zero _ this)
  obtain ⟨first, hf⟩ := effectiveFirst_eq_some_of_pos_length p hne0
  have hget1 := getElement_eq_getElementFrom p first hf index1 hle1
  have hget2 := getElement_eq_getElementFrom p first hf index2 hle2
  have hwalk :
      (getElementsFrom first p.subtractiveCommonDifference
        (getLength p)).length =
        getLength p :=
    getElementsFrom_length_of_le_getLength p first hf (getLength p) (Or.inr rfl)
  let q : ArithmeticDecreasing :=
    {
      first := some first
      subtractiveCommonDifference := p.subtractiveCommonDifference
      limit := lastElementFrom first p.subtractiveCommonDifference (getLength p)
    }
  refine ⟨q, ?_, ?_⟩
  · simp only [tryFromTwoElementsAndLength, hle1, hle2, ↓reduceIte, hget1, hget2]
    match compare index1 index2 with
    | .equal heq =>
      exact (hne heq).elim
    | .less hlt =>
      have hdiff :=
        tryCommonDifferenceFromOrderedIndexedElements_getElementFrom
          p first hf index1 index2 hlt hle2
      have hfirst :=
        tryFirstFromIndexedElement_getElementFrom p first hf index1 hle1
      simp only [hdiff, hfirst, hwalk, ↓reduceIte]
      rfl
    | .greater hgt =>
      have hdiff :=
        tryCommonDifferenceFromOrderedIndexedElements_getElementFrom
          p first hf index2 index1 hgt hle1
      have hfirst :=
        tryFirstFromIndexedElement_getElementFrom p first hf index2 hle2
      simp only [hdiff, hfirst, hwalk, ↓reduceIte]
      rfl
  · have hfq :=
      effectiveFirst_lastElementFrom first p.subtractiveCommonDifference
        (getLength p) hne0
    have hlenq :=
      getLength_lastElementFrom first p.subtractiveCommonDifference
        (getLength p) hne0 hwalk
    exact equivalence_of_same_params p q first hf hfq rfl hlenq.symm

/-- Extend a decreasing arithmetic progression of length at least two to a
decreasing arithmetic progression of a given length at least that of the
original, with the same effective first element and subtractive common
difference, when a full arithmetic walk of that length is possible. Returns
`none` when an intermediate subtraction fails. When successful, the extended
progression begins with every element of the original progression. -/
def tryExtendToLength (p : ArithmeticDecreasing)
    (hge : CardinalNatural.Peano.two ≤ getLength p)
    (length : CardinalNatural.Peano)
    (_hle : getLength p ≤ length) :
    Option ArithmeticDecreasing :=
  match hf : effectiveFirst p with
  | none =>
    False.elim
      (CardinalNatural.Peano.not_two_le_zero
        ((getLength_eq_zero_iff_effectiveFirst_none p).mpr hf ▸ hge))
  | some first =>
    if (getElementsFrom first p.subtractiveCommonDifference length).length =
        length then
      some {
        first := some first
        subtractiveCommonDifference := p.subtractiveCommonDifference
        limit := lastElementFrom first p.subtractiveCommonDifference length
      }
    else
      none

/-- A successful `tryExtendToLength` yields a progression of exactly the
requested length. -/
theorem getLength_of_tryExtendToLength (p : ArithmeticDecreasing)
    (hge : CardinalNatural.Peano.two ≤ getLength p)
    (length : CardinalNatural.Peano)
    (hleLen : getLength p ≤ length)
    (q : ArithmeticDecreasing)
    (h : tryExtendToLength p hge length hleLen = some q) :
    getLength q = length := by
  unfold tryExtendToLength at h
  split at h
  · next hf =>
    exact (CardinalNatural.Peano.not_two_le_zero
      ((getLength_eq_zero_iff_effectiveFirst_none p).mpr hf ▸ hge)).elim
  · next first hf =>
    split at h
    · next hwalk =>
      injection h with heq
      subst heq
      have hne : length ≠ CardinalNatural.Peano.zero := by
        intro hzero
        exact CardinalNatural.Peano.not_two_le_zero
          (CardinalNatural.Peano.eq_zero_of_le_zero _
            (hzero ▸ hleLen) ▸ hge)
      exact getLength_lastElementFrom first p.subtractiveCommonDifference
        length hne hwalk
    · nomatch h

/-- A successful `tryExtendToLength` keeps the original effective first
element. -/
theorem effectiveFirst_of_tryExtendToLength (p : ArithmeticDecreasing)
    (hge : CardinalNatural.Peano.two ≤ getLength p)
    (length : CardinalNatural.Peano)
    (hleLen : getLength p ≤ length)
    (q : ArithmeticDecreasing)
    (h : tryExtendToLength p hge length hleLen = some q)
    (first : Peano) (hf : effectiveFirst p = some first) :
    effectiveFirst q = some first := by
  have hne : length ≠ CardinalNatural.Peano.zero := by
    intro hzero
    exact CardinalNatural.Peano.not_two_le_zero
      (CardinalNatural.Peano.eq_zero_of_le_zero _
        (hzero ▸ hleLen) ▸ hge)
  unfold tryExtendToLength at h
  split at h
  · next hf' =>
    rw [hf'] at hf
    nomatch hf
  · next first' hf' =>
    have heq : some first = some first' := hf.symm.trans hf'
    injection heq with heq'
    split at h
    · next _hwalk =>
      injection h with hq
      subst hq
      rw [← heq']
      exact effectiveFirst_lastElementFrom first p.subtractiveCommonDifference
        length hne
    · nomatch h

/-- In-range elements of a decreasing arithmetic progression agree with the
corresponding elements of a successful length extension. -/
theorem getElement_of_tryExtendToLength (p : ArithmeticDecreasing)
    (hge : CardinalNatural.Peano.two ≤ getLength p)
    (length : CardinalNatural.Peano)
    (hleLen : getLength p ≤ length)
    (q : ArithmeticDecreasing)
    (h : tryExtendToLength p hge length hleLen = some q)
    (index : Peano)
    (hle : CardinalNatural.Peano.fromOrdinal index ≤ getLength p) :
    ∃ (hle' : CardinalNatural.Peano.fromOrdinal index ≤ getLength q),
      getElement q index hle' = getElement p index hle := by
  have hlenq := getLength_of_tryExtendToLength p hge length hleLen q h
  have hle' :
      CardinalNatural.Peano.fromOrdinal index ≤ getLength q :=
    CardinalNatural.Peano.le_trans hle (hlenq.symm ▸ hleLen)
  refine ⟨hle', ?_⟩
  match hf : effectiveFirst p with
  | none =>
    exact (CardinalNatural.Peano.not_two_le_zero
      ((getLength_eq_zero_iff_effectiveFirst_none p).mpr hf ▸ hge)).elim
  | some first =>
    have hfExt :=
      effectiveFirst_of_tryExtendToLength p hge length hleLen q h first hf
    rw [getElement_eq_getElementFrom q first hfExt index hle']
    rw [getElement_eq_getElementFrom p first hf index hle]
    have hdiff :
        q.subtractiveCommonDifference = p.subtractiveCommonDifference := by
      unfold tryExtendToLength at h
      split at h
      · next hf' =>
        rw [hf'] at hf
        nomatch hf
      · next first' hf' =>
        split at h
        · next _hwalk =>
          injection h with hq
          subst hq
          rfl
        · nomatch h
    rw [hdiff]

end ArithmeticDecreasing

end ZeroMath.Numbers.OrdinalNatural.Peano.Progressions
