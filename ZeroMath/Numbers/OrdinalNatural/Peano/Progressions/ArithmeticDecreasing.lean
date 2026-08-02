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

end ArithmeticDecreasing

end ZeroMath.Numbers.OrdinalNatural.Peano.Progressions
