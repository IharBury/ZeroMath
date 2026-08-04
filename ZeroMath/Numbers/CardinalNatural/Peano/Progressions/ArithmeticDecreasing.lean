import ZeroMath.Numbers.CardinalNatural.Peano
import ZeroMath.Sequences.List
import ZeroMath.Sequences.Progression

namespace ZeroMath.Numbers.CardinalNatural.Peano.Progressions

/-- An arithmetic progression of Peano numbers with positive subtractive common
difference, defined by an optional first element (`none` for the empty
progression), the common difference (subtracted at each step), and a limit
such that no element is less than the limit. The progression is also empty
when the first element is less than the limit. -/
structure ArithmeticDecreasing where
  first : Option Peano
  subtractiveCommonDifference : Peano
  limit : Peano
  subtractiveCommonDifference_ne_zero : subtractiveCommonDifference ≠ zero

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
theorem limit_le_of_tryGetElement_eq_some (p : ArithmeticDecreasing)
    (index : OrdinalNatural.Peano) (x : Peano)
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
since the subtractive common difference is positive. -/
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
      have hone : one ≤ p.subtractiveCommonDifference :=
        succ_le_of_lt (zero_lt_of_ne_zero _ p.subtractiveCommonDifference_ne_zero)
      have hz_le : z.successor ≤ y := by
        rw [← add_one, ← hadd]
        exact add_le_add_left hone z
      exact heq ▸ lt_of_succ_le hz_le
    · simp only [hle, ↓reduceIte] at h
      nomatch h

/-- If `tryGetElement` returns a value and the progression starts at `first`,
then `fromOrdinal index + x ≤ successor first`. Each step decreases the value
by at least one while the ordinal index (as a cardinal) increases by one, so
their sum never exceeds that of the first element. -/
theorem fromOrdinal_add_le_succ_first_of_tryGetElement (p : ArithmeticDecreasing)
    (first : Peano) (index : OrdinalNatural.Peano) (x : Peano)
    (hf : (toProgression p).first = some first)
    (h : Sequences.Progression.tryGetElement index (toProgression p) = some x) :
    fromOrdinal index + x ≤ first.successor := by
  induction index generalizing x with
  | one =>
    simp only [Sequences.Progression.tryGetElement] at h
    have heq : x = first := by
      rw [hf] at h
      injection h with heq
      exact heq.symm
    rw [heq, fromOrdinal, one_add]
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
      have hx_le : x.successor ≤ y := succ_le_of_lt hlt
      have hn : fromOrdinal n + y ≤ first.successor := ih y hm
      have hmid : fromOrdinal n + x.successor ≤ fromOrdinal n + y :=
        add_le_add_left hx_le (fromOrdinal n)
      have hmid' : fromOrdinal n + x.successor ≤ first.successor :=
        le_trans hmid hn
      have heqadd :
          fromOrdinal n.successor + x = fromOrdinal n + x.successor := by
        change (fromOrdinal n).successor + x = fromOrdinal n + x.successor
        rw [successor_add, add_successor]
      exact heqadd ▸ hmid'

/-- The progression obtained from a decreasing arithmetic progression is finite:
if it is empty then `tryGetElement` at `one` is `none`; otherwise, starting from
`first`, `tryGetElement` at the ordinal for `successor (successor first)` cannot
return `some`, since that value `x` would need
`successor (successor first) + x ≤ successor first`. -/
theorem toProgression_finite (p : ArithmeticDecreasing) :
    Sequences.Progression.Finite (toProgression p) := by
  match hf : (toProgression p).first with
  | none =>
    refine ⟨OrdinalNatural.Peano.one, ?_⟩
    simp only [Sequences.Progression.tryGetElement, hf]
  | some first =>
    have hne : (first.successor).successor ≠ zero :=
      successor_ne_zero first.successor
    refine ⟨toOrdinal (first.successor).successor hne, ?_⟩
    cases h :
        Sequences.Progression.tryGetElement
          (toOrdinal (first.successor).successor hne) (toProgression p) with
    | none =>
      rfl
    | some x =>
      have hle :=
        fromOrdinal_add_le_succ_first_of_tryGetElement p first
          (toOrdinal (first.successor).successor hne) x hf h
      rw [fromOrdinal_toOrdinal] at hle
      have hle' : (first.successor).successor ≤ first.successor :=
        le_trans (le_add_self_left (first.successor).successor x) hle
      exact (not_succ_le first.successor hle').elim

/-- Length remaining from an element already known to lie in the progression,
given the room below that element down to the limit (`none` when the element
equals the limit). Computed with one division by the subtractive common
difference instead of comparing each successive term to the limit. -/
def lengthFromGap (diff : Peano) (hdiff : diff ≠ zero) : Option Peano → Peano
  | none => one
  | some gap =>
    match divideWithRemainder gap diff hdiff with
    | (q, _) => q.successor

/-- The length of a decreasing arithmetic progression: the number of elements
before `tryGetElement` first returns `none`. Uses a single comparison of the
first element to the limit and one division, avoiding a comparison at every
step of the progression. -/
def getLength (p : ArithmeticDecreasing) : Peano :=
  match p.first with
  | none => zero
  | some first =>
    match compare first p.limit with
    | .less _ => zero
    | .equal _ => one
    | .greater hlt =>
      lengthFromGap p.subtractiveCommonDifference
        p.subtractiveCommonDifference_ne_zero
        (some (subtract first p.limit (Or.inl hlt)))

/-- `lengthFromGap` on `gap` is the successor of `lengthFromGap` on `gap - diff`
when `diff < gap`. -/
theorem lengthFromGap_succ_of_lt (diff : Peano) (hdiff : diff ≠ zero) (gap : Peano)
    (hlt : diff < gap) :
    lengthFromGap diff hdiff (some gap) =
      (lengthFromGap diff hdiff
        (some (subtract gap diff (Or.inl hlt)))).successor := by
  have hsum : subtract gap diff (Or.inl hlt) + diff = gap :=
    subtract_add_cancel gap diff (Or.inl hlt)
  have hdiv :=
    divideWithRemainder_add_right (subtract gap diff (Or.inl hlt)) diff hdiff
  rw [hsum] at hdiv
  unfold lengthFromGap
  match hrem : divideWithRemainder (subtract gap diff (Or.inl hlt)) diff hdiff with
  | (q, r) =>
    simp only [hrem] at hdiv
    simp only [hrem, hdiv]

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

theorem diff_le_of_le_gap (p : ArithmeticDecreasing) (x : Peano)
    (hlt : p.limit < x)
    (hd : p.subtractiveCommonDifference ≤ subtract x p.limit (Or.inl hlt)) :
    p.subtractiveCommonDifference ≤ x := by
  have hsum : subtract x p.limit (Or.inl hlt) + p.limit = x :=
    subtract_add_cancel x p.limit (Or.inl hlt)
  have hgap_le : subtract x p.limit (Or.inl hlt) ≤ x := by
    have h := le_add_self_left (subtract x p.limit (Or.inl hlt)) p.limit
    rwa [hsum] at h
  exact le_trans hd hgap_le

theorem le_iff_limit_le_sub_of_lt (p : ArithmeticDecreasing) (x : Peano)
    (hlt : p.limit < x) :
    p.subtractiveCommonDifference ≤ subtract x p.limit (Or.inl hlt) ↔
      ∃ hdiff : p.subtractiveCommonDifference ≤ x,
        p.limit ≤ subtract x p.subtractiveCommonDifference hdiff := by
  have hsum : subtract x p.limit (Or.inl hlt) + p.limit = x :=
    subtract_add_cancel x p.limit (Or.inl hlt)
  have hsum' : p.limit + subtract x p.limit (Or.inl hlt) = x :=
    (add_commutative _ _).trans hsum
  constructor
  · intro hd
    refine ⟨diff_le_of_le_gap p x hlt hd, ?_⟩
    have hle_mid := add_le_add_left hd p.limit
    have hle_add : p.limit + p.subtractiveCommonDifference ≤ x :=
      le_trans hle_mid (Or.inr hsum')
    have hdiff := diff_le_of_le_gap p x hlt hd
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
    | inl hlt' => exact Or.inl (add_lt_cancel_right hlt')
    | inr heq => exact Or.inr (add_cancel_right _ _ p.subtractiveCommonDifference heq)
  · intro ⟨hdiff, hle⟩
    have hsub :
        subtract x p.subtractiveCommonDifference hdiff +
          p.subtractiveCommonDifference = x :=
      subtract_add_cancel x p.subtractiveCommonDifference hdiff
    have hsub' :
        p.subtractiveCommonDifference +
          subtract x p.subtractiveCommonDifference hdiff = x :=
      (add_commutative _ _).trans hsub
    have hle_mid := add_le_add_left hle p.subtractiveCommonDifference
    have hle_add : p.subtractiveCommonDifference + p.limit ≤ x :=
      le_trans hle_mid (Or.inr hsub')
    have hrew :
        p.subtractiveCommonDifference + p.limit ≤
          subtract x p.limit (Or.inl hlt) + p.limit := by
      have h : p.subtractiveCommonDifference + p.limit ≤ x := hle_add
      rw [← hsum] at h
      exact h
    cases hrew with
    | inl hlt' => exact Or.inl (add_lt_cancel_right hlt')
    | inr heq => exact Or.inr (add_cancel_right _ _ p.limit heq)

theorem limit_lt_sub_of_lt_gap (p : ArithmeticDecreasing) (x : Peano)
    (hlt : p.limit < x)
    (hdiff : p.subtractiveCommonDifference < subtract x p.limit (Or.inl hlt))
    (hdiff_x : p.subtractiveCommonDifference ≤ x) :
    p.limit < subtract x p.subtractiveCommonDifference hdiff_x := by
  have hsum : subtract x p.limit (Or.inl hlt) + p.limit = x :=
    subtract_add_cancel x p.limit (Or.inl hlt)
  have hsum' : p.limit + subtract x p.limit (Or.inl hlt) = x :=
    (add_commutative _ _).trans hsum
  have hsub :
      subtract x p.subtractiveCommonDifference hdiff_x +
        p.subtractiveCommonDifference = x :=
    subtract_add_cancel _ _ _
  have hlt_sum : p.limit + p.subtractiveCommonDifference <
      p.limit + subtract x p.limit (Or.inl hlt) :=
    add_lt_add_left hdiff p.limit
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
  exact add_lt_cancel_right hlt_sub

theorem subtract_gap_eq_sub_limit (p : ArithmeticDecreasing) (x : Peano)
    (hlt : p.limit < x)
    (hdiff : p.subtractiveCommonDifference < subtract x p.limit (Or.inl hlt))
    (hdiff_x : p.subtractiveCommonDifference ≤ x)
    (hlt' : p.limit < subtract x p.subtractiveCommonDifference hdiff_x) :
    subtract (subtract x p.subtractiveCommonDifference hdiff_x) p.limit (Or.inl hlt') =
      subtract (subtract x p.limit (Or.inl hlt)) p.subtractiveCommonDifference
        (Or.inl hdiff) := by
  have hsum : subtract x p.limit (Or.inl hlt) + p.limit = x :=
    subtract_add_cancel x p.limit (Or.inl hlt)
  have h1 :=
    subtract_add_cancel
      (subtract x p.subtractiveCommonDifference hdiff_x) p.limit (Or.inl hlt')
  have h2 :=
    subtract_add_cancel (subtract x p.limit (Or.inl hlt)) p.subtractiveCommonDifference
      (Or.inl hdiff)
  have hsub :
      subtract x p.subtractiveCommonDifference hdiff_x +
        p.subtractiveCommonDifference = x :=
    subtract_add_cancel _ _ _
  apply add_cancel_right _ _ (p.limit + p.subtractiveCommonDifference)
  have hleft :
      subtract (subtract x p.subtractiveCommonDifference hdiff_x) p.limit (Or.inl hlt') +
        (p.limit + p.subtractiveCommonDifference) = x := by
    rw [← add_associative, h1, hsub]
  have hright :
      subtract (subtract x p.limit (Or.inl hlt)) p.subtractiveCommonDifference
          (Or.inl hdiff) +
        (p.limit + p.subtractiveCommonDifference) = x := by
    have h :
        subtract (subtract x p.limit (Or.inl hlt)) p.subtractiveCommonDifference
            (Or.inl hdiff) +
          (p.subtractiveCommonDifference + p.limit) = x := by
      rw [← add_associative, h2, hsum]
    have hcomm :
        p.limit + p.subtractiveCommonDifference =
          p.subtractiveCommonDifference + p.limit :=
      add_commutative _ _
    rw [hcomm]
    exact h
  exact hleft.trans hright.symm

/-- Gap below `x` down to `limit`, or `none` when `x = limit`. -/
def gapFromLimit (limit x : Peano) (hx : limit ≤ x) : Option Peano :=
  match compare x limit with
  | .less hlt => (not_le_of_gt hlt hx).elim
  | .equal _ => none
  | .greater hgt => some (subtract x limit (Or.inl hgt))

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
    gapFromLimit limit x hx = some (subtract x limit (Or.inl hlt)) := by
  unfold gapFromLimit
  match hc : compare x limit with
  | .less hlt' => exact (not_le_of_gt hlt' hx).elim
  | .equal heq =>
    rw [heq] at hlt
    exact (not_lt_self limit hlt).elim
  | .greater hgt =>
    exact congrArg some
      (subtract_eq_of_eq (Or.inl hgt) (Or.inl hlt) rfl rfl)

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

/-- Walking the progression from an accessible state matches `lengthFromGap` on
in-range elements, and yields zero from `none`. -/
theorem getLengthFrom_eq_lengthFromGap (p : ArithmeticDecreasing)
    (current : Option Peano)
    (hAcc : Acc (Sequences.Progression.OptionStep (toProgression p).next) current) :
    (current = none →
      Sequences.Progression.getLengthFrom (toProgression p).next current hAcc =
        zero) ∧
    (∀ x, current = some x → ∀ hx : p.limit ≤ x,
      Sequences.Progression.getLengthFrom (toProgression p).next current hAcc =
        lengthFromGap p.subtractiveCommonDifference
          p.subtractiveCommonDifference_ne_zero
          (gapFromLimit p.limit x hx)) := by
  refine Acc.rec
    (motive := fun current hAcc =>
      (current = none →
        Sequences.Progression.getLengthFrom (toProgression p).next current hAcc =
          zero) ∧
      (∀ x, current = some x → ∀ hx : p.limit ≤ x,
        Sequences.Progression.getLengthFrom (toProgression p).next current hAcc =
          lengthFromGap p.subtractiveCommonDifference
            p.subtractiveCommonDifference_ne_zero
            (gapFromLimit p.limit x hx)))
    (fun current hcurr ih => by
      refine ⟨?none, ?some⟩
      case none =>
        intro hnone
        subst hnone
        exact Sequences.Progression.getLengthFrom_none _ (Acc.intro _ hcurr)
      case some =>
        intro x hx_eq hx
        subst hx_eq
        have hAccx :
            Acc (Sequences.Progression.OptionStep (toProgression p).next)
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
                exact lt_add_of_right_ne_zero y p.subtractiveCommonDifference
                  p.subtractiveCommonDifference_ne_zero
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
                zero := by
            rw [getLengthFrom_eq_of_acc_eq _ _ _
              (hcurr _ (Sequences.Progression.OptionStep.step x))]
            exact hnil
          simp only [hgap, lengthFromGap, hnil', one]
        | .greater hgt =>
          have hgap := gapFromLimit_greater hx hgt
          rw [hgap]
          match hd : compare p.subtractiveCommonDifference
              (subtract x p.limit (Or.inl hgt)) with
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
                    p.subtractiveCommonDifference ≤
                      subtract x p.limit (Or.inl hgt) :=
                  (le_iff_limit_le_sub_of_lt p x hgt).mpr ⟨hlt_diff, by
                    rwa [hsub]⟩
                exact not_le_of_gt hgt' hle_gap
            have hnil := (ih ((toProgression p).next x)
              (Sequences.Progression.OptionStep.step x)).1 hnext
            have hnil' :
                Sequences.Progression.getLengthFrom (toProgression p).next
                  ((toProgression p).next x)
                  (hAccx.inv (Sequences.Progression.OptionStep.step x)) =
                  zero := by
              rw [getLengthFrom_eq_of_acc_eq _ _ _
                (hcurr _ (Sequences.Progression.OptionStep.step x))]
              exact hnil
            have hdiv :=
              divideWithRemainder_eq_of_mul_add
                (subtract x p.limit (Or.inl hgt)) p.subtractiveCommonDifference
                p.subtractiveCommonDifference_ne_zero zero
                (subtract x p.limit (Or.inl hgt)) hgt' (by
                  rw [multiply_zero, zero_add])
            simp only [lengthFromGap, hnil', hdiv]
          | .equal heq =>
            have hle_diff :
                p.subtractiveCommonDifference ≤
                  subtract x p.limit (Or.inl hgt) :=
              Or.inr heq
            obtain ⟨hdiff, hle_y⟩ :=
              (le_iff_limit_le_sub_of_lt p x hgt).mp hle_diff
            have hs := trySubtract_of_subtract
              (z := subtract x p.subtractiveCommonDifference hdiff)
              ⟨hdiff, rfl⟩
            have hnext := next_eq_some_of_limit_le p x
              (subtract x p.subtractiveCommonDifference hdiff) hs hle_y
            have hx_next :
                subtract x p.subtractiveCommonDifference hdiff = p.limit := by
              have hsum : subtract x p.limit (Or.inl hgt) + p.limit = x :=
                subtract_add_cancel x p.limit (Or.inl hgt)
              have hsub :
                  subtract x p.subtractiveCommonDifference hdiff +
                    p.subtractiveCommonDifference = x :=
                subtract_add_cancel x p.subtractiveCommonDifference hdiff
              apply add_cancel_right _ _ p.subtractiveCommonDifference
              calc
                subtract x p.subtractiveCommonDifference hdiff +
                    p.subtractiveCommonDifference =
                  x := hsub
                _ = subtract x p.limit (Or.inl hgt) + p.limit := hsum.symm
                _ = p.subtractiveCommonDifference + p.limit := by rw [← heq]
                _ = p.limit + p.subtractiveCommonDifference := add_commutative _ _
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
              divideWithRemainder_eq_of_mul
                (subtract x p.limit (Or.inl hgt)) p.subtractiveCommonDifference
                p.subtractiveCommonDifference_ne_zero one (by
                  rw [← heq, multiply_one])
            have hnext_len :
                Sequences.Progression.getLengthFrom (toProgression p).next
                  ((toProgression p).next x)
                  (hAccx.inv (Sequences.Progression.OptionStep.step x)) =
                  one := by
              have htmp := ih'
              simp only [hgap', lengthFromGap] at htmp
              rw [getLengthFrom_eq_of_acc_eq _ _ _
                (hcurr _ (Sequences.Progression.OptionStep.step x))]
              simpa [hnext] using htmp
            simp only [hnext_len, lengthFromGap, hdiv, one]
          | .less hdiff =>
            have hle_diff :
                p.subtractiveCommonDifference ≤
                  subtract x p.limit (Or.inl hgt) :=
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
                p.subtractiveCommonDifference_ne_zero
                (subtract x p.limit (Or.inl hgt)) hdiff
            have hnext_len :
                Sequences.Progression.getLengthFrom (toProgression p).next
                  ((toProgression p).next x)
                  (hAccx.inv (Sequences.Progression.OptionStep.step x)) =
                  lengthFromGap p.subtractiveCommonDifference
                    p.subtractiveCommonDifference_ne_zero
                    (some (subtract (subtract x p.limit (Or.inl hgt))
                      p.subtractiveCommonDifference (Or.inl hdiff))) := by
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
      Sequences.Progression.getLengthFrom (toProgression p).next
        (toProgression p).first
        (Sequences.Progression.acc_first_of_finite (toProgression p)
          (toProgression_finite p))
    simp only [getLength, hf, hfirst, Sequences.Progression.getLengthFrom_none]
  | some first =>
    cases hc : compare first p.limit with
    | less hlt =>
      have hnot : ¬ p.limit ≤ first := not_le_of_gt hlt
      have hfirst : (toProgression p).first = none := by
        simp only [toProgression, hf, hnot, ↓reduceIte]
      change getLength p =
        Sequences.Progression.getLengthFrom (toProgression p).next
          (toProgression p).first
          (Sequences.Progression.acc_first_of_finite (toProgression p)
            (toProgression_finite p))
      simp only [getLength, hf, hc, hfirst,
        Sequences.Progression.getLengthFrom_none]
    | equal heq =>
      have hle : p.limit ≤ first := Or.inr heq.symm
      have hfirst : (toProgression p).first = some first := by
        simp only [toProgression, hf, hle, ↓reduceIte]
      have hAcc :=
        Sequences.Progression.acc_first_of_finite (toProgression p)
          (toProgression_finite p)
      have hAcc' :
          Acc (Sequences.Progression.OptionStep (toProgression p).next)
            (some first) := hfirst ▸ hAcc
      have hx :=
        (getLengthFrom_eq_lengthFromGap p (some first) hAcc').2 first rfl hle
      simp only [getLength, hf, hc, Sequences.Progression.getLength]
      have hwalk :
          Sequences.Progression.getLengthFrom (toProgression p).next
            (toProgression p).first hAcc = one := by
        rw [getLengthFrom_eq_of_current_eq _ hfirst hAcc]
        rw [getLengthFrom_eq_of_acc_eq _ _ _ hAcc']
        simpa [gapFromLimit_equal hle heq, lengthFromGap] using hx
      exact hwalk.symm
    | greater hgt =>
      have hle : p.limit ≤ first := Or.inl hgt
      have hfirst : (toProgression p).first = some first := by
        simp only [toProgression, hf, hle, ↓reduceIte]
      have hAcc :=
        Sequences.Progression.acc_first_of_finite (toProgression p)
          (toProgression_finite p)
      have hAcc' :
          Acc (Sequences.Progression.OptionStep (toProgression p).next)
            (some first) := hfirst ▸ hAcc
      have hx :=
        (getLengthFrom_eq_lengthFromGap p (some first) hAcc').2 first rfl hle
      simp only [getLength, hf, hc, Sequences.Progression.getLength]
      have hwalk :
          Sequences.Progression.getLengthFrom (toProgression p).next
            (toProgression p).first hAcc =
            lengthFromGap p.subtractiveCommonDifference
              p.subtractiveCommonDifference_ne_zero
              (some (subtract first p.limit (Or.inl hgt))) := by
        rw [getLengthFrom_eq_of_current_eq _ hfirst hAcc]
        rw [getLengthFrom_eq_of_acc_eq _ _ _ hAcc']
        simpa [gapFromLimit_greater hle hgt] using hx
      exact hwalk.symm

/-- Element at a positive ordinal index starting from a known first value,
retreating by the subtractive common difference with no limit comparisons. -/
def getElementFrom (first subtractiveCommonDifference : Peano) :
    OrdinalNatural.Peano → Peano
  | .one => first
  | .successor n =>
    match trySubtract (getElementFrom first subtractiveCommonDifference n)
        subtractiveCommonDifference with
    | none => getElementFrom first subtractiveCommonDifference n
    | some y => y

/-- Shifting the start by one subtractive common difference decreases the index
by one, when that subtraction is defined. -/
theorem getElementFrom_succ (first subtractiveCommonDifference y : Peano)
    (n : OrdinalNatural.Peano)
    (h : trySubtract first subtractiveCommonDifference = some y) :
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
    getLength p = zero := by
  rw [getLength_eq]
  have hAcc :=
    Sequences.Progression.acc_first_of_finite (toProgression p)
      (toProgression_finite p)
  have hEq :=
    getLengthFrom_eq_of_current_eq (toProgression p).next h hAcc
  simp only [Sequences.Progression.getLength]
  rw [hEq, Sequences.Progression.getLengthFrom_none]

/-- The length bound is impossible when `toProgression` is empty. -/
theorem not_fromOrdinal_le_getLength_of_first_none
    (p : ArithmeticDecreasing) (index : OrdinalNatural.Peano)
    (hle : fromOrdinal index ≤ getLength p)
    (h : (toProgression p).first = none) : False := by
  have hlen := getLength_eq_zero_of_toProgression_first_none p h
  have hle' : fromOrdinal index ≤ zero := hlen ▸ hle
  exact fromOrdinal_ne_zero index (eq_zero_of_le_zero _ hle')

/-- A successor index within the remaining length forces a next term equal to
the current element minus the subtractive common difference. -/
theorem next_eq_some_of_succ_le_getLengthFrom (p : ArithmeticDecreasing)
    (x : Peano) (n : OrdinalNatural.Peano)
    (hAcc : Acc (Sequences.Progression.OptionStep (toProgression p).next)
      (some x))
    (hle : fromOrdinal n.successor ≤
      Sequences.Progression.getLengthFrom (toProgression p).next (some x)
        hAcc) :
    ∃ y, trySubtract x p.subtractiveCommonDifference = some y ∧
      (toProgression p).next x = some y := by
  have hlen :=
    Sequences.Progression.getLengthFrom_some (toProgression p).next x hAcc
  have hle' :
      successor (fromOrdinal n) ≤
        successor
          (Sequences.Progression.getLengthFrom (toProgression p).next
            ((toProgression p).next x)
            (hAcc.inv (Sequences.Progression.OptionStep.step x))) := by
    simpa [hlen, fromOrdinal] using hle
  have hle_n := le_of_succ_le_succ hle'
  cases hnext : (toProgression p).next x with
  | none =>
    have hAcc' := hAcc.inv (Sequences.Progression.OptionStep.step x)
    have hzero :
        Sequences.Progression.getLengthFrom (toProgression p).next
          ((toProgression p).next x) hAcc' =
          zero := by
      have hEq :=
        getLengthFrom_eq_of_current_eq (toProgression p).next hnext hAcc'
      rw [hEq, Sequences.Progression.getLengthFrom_none]
    have hle0 : fromOrdinal n ≤ zero := by
      rwa [hzero] at hle_n
    exact (fromOrdinal_ne_zero n (eq_zero_of_le_zero _ hle0)).elim
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
    (index : OrdinalNatural.Peano)
    (hle : fromOrdinal index ≤
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
    (index : OrdinalNatural.Peano)
    (hle1 : fromOrdinal index ≤
      Sequences.Progression.getLengthFrom next current h1)
    (hle2 : fromOrdinal index ≤
      Sequences.Progression.getLengthFrom next current h2) :
    Sequences.Progression.getElementFrom next current h1 index hle1 =
      Sequences.Progression.getElementFrom next current h2 index hle2 :=
  rfl

/-- Walking `Progression.getElementFrom` from an in-range element matches
`getElementFrom` (subtractions only, no further limit comparisons). -/
theorem getElementFrom_eq_progression (p : ArithmeticDecreasing)
    (x : Peano)
    (hAcc : Acc (Sequences.Progression.OptionStep (toProgression p).next)
      (some x))
    (index : OrdinalNatural.Peano)
    (hle : fromOrdinal index ≤
      Sequences.Progression.getLengthFrom (toProgression p).next (some x)
        hAcc) :
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
        fromOrdinal n ≤
          Sequences.Progression.getLengthFrom (toProgression p).next
            ((toProgression p).next x)
            (hAcc.inv (Sequences.Progression.OptionStep.step x)) := by
      have hle' :
          successor (fromOrdinal n) ≤
            successor
              (Sequences.Progression.getLengthFrom (toProgression p).next
                ((toProgression p).next x)
                (hAcc.inv (Sequences.Progression.OptionStep.step x))) := by
        simpa [hlen, fromOrdinal] using hle
      exact le_of_succ_le_succ hle'
    have hAcc_next :
        Acc (Sequences.Progression.OptionStep (toProgression p).next)
          (some y) :=
      hnext ▸ hAcc.inv (Sequences.Progression.OptionStep.step x)
    have hle_next :
        fromOrdinal n ≤
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
def getElement (p : ArithmeticDecreasing) (index : OrdinalNatural.Peano)
    (hle : fromOrdinal index ≤ getLength p) : Peano :=
  match hf : (toProgression p).first with
  | none =>
    (not_fromOrdinal_le_getLength_of_first_none p index hle hf).elim
  | some first =>
    getElementFrom first p.subtractiveCommonDifference index

/-- `getElement` agrees with walking `toProgression` via `Progression.getElement`. -/
theorem getElement_eq (p : ArithmeticDecreasing)
    (index : OrdinalNatural.Peano)
    (hle : fromOrdinal index ≤ getLength p) :
    getElement p index hle =
      Sequences.Progression.getElement (toProgression p) (toProgression_finite p)
        index (getLength_eq p ▸ hle) := by
  dsimp only [getElement, Sequences.Progression.getElement]
  split
  · next hf =>
    exact (not_fromOrdinal_le_getLength_of_first_none p index hle hf).elim
  · next first hf =>
    have hAcc :=
      Sequences.Progression.acc_first_of_finite (toProgression p)
        (toProgression_finite p)
    have hAcc' :
        Acc (Sequences.Progression.OptionStep (toProgression p).next)
          (some first) :=
      hf ▸ hAcc
    have hle_prog :
        fromOrdinal index ≤
          Sequences.Progression.getLength (toProgression p)
            (toProgression_finite p) :=
      getLength_eq p ▸ hle
    have hle' :
        fromOrdinal index ≤
          Sequences.Progression.getLengthFrom (toProgression p).next
            (some first) hAcc' := by
      dsimp only [Sequences.Progression.getLength] at hle_prog
      have hEq :=
        getLengthFrom_eq_of_current_eq (toProgression p).next hf hAcc
      rwa [hEq] at hle_prog
    have hwalk := getElementFrom_eq_progression p first hAcc' index hle'
    refine hwalk.trans ?_
    have hcur :=
      progression_getElementFrom_eq_of_current_eq (toProgression p).next hf
        hAcc index
        (by
          dsimp only [Sequences.Progression.getLength] at hle_prog
          exact hle_prog)
    exact (progression_getElementFrom_eq_of_acc_eq (toProgression p).next
        (some first) hAcc' (hf ▸ hAcc) index hle' _).trans hcur.symm

/-- Two decreasing arithmetic progressions are equivalent when their underlying
progressions yield related elements (equality for Peano) at every positive
ordinal index. -/
def Equivalence (p q : ArithmeticDecreasing) : Prop :=
  Sequences.Progression.Equivalence (toProgression p) (toProgression q)

instance : HasEquiv ArithmeticDecreasing where
  Equiv := Equivalence

/-- Equivalence of decreasing arithmetic progressions is decidable by walking
both underlying progressions in lockstep. -/
instance (p q : ArithmeticDecreasing) : Decidable (p ≈ q) :=
  Sequences.Progression.decidableEquivalenceOfFinite
    (toProgression p) (toProgression q)
    (toProgression_finite p) (toProgression_finite q)

/-- Elements from a known start for the given remaining length, retreating by the
subtractive common difference with no limit comparisons. -/
def getElementsFrom (first subtractiveCommonDifference : Peano) :
    Peano → Sequences.List Peano
  | .zero => .empty
  | .successor n =>
    .firstElement first
      (match trySubtract first subtractiveCommonDifference with
       | none => .empty
       | some next =>
         getElementsFrom next subtractiveCommonDifference n)

/-- The ordered list of all elements of a decreasing arithmetic progression.
Empty when there is no in-range first element. Uses `(toProgression p).first`
and `getLength`, then retreats by repeated subtraction of the subtractive common
difference — avoiding a limit comparison at every step. -/
def getElements (p : ArithmeticDecreasing) : Sequences.List Peano :=
  match (toProgression p).first with
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
    two ≤ elements.length →
    Option ArithmeticDecreasing
  | .empty, hge =>
    False.elim (not_two_le_zero (by
      change two ≤ zero
      exact hge))
  | .firstElement _ .empty, hge =>
    False.elim (not_two_le_one (by
      change two ≤ one
      exact hge))
  | .firstElement x (.firstElement y ys), _ =>
    match trySubtract x y with
    | none => none
    | some diff =>
      if hdiff : diff = zero then
        none
      else
        match tryLastOfArithmeticContinuation y diff ys with
        | none => none
        | some last =>
          some {
            first := some x
            subtractiveCommonDifference := diff
            limit := last
            subtractiveCommonDifference_ne_zero := hdiff
          }

/-- Last element of a non-empty decreasing arithmetic walk of length `n`,
starting at `first` with subtractive common difference `subtractiveCommonDifference`.
For `n = zero` the value is unused (`first`). When an intermediate subtraction is
undefined the walk stops and returns the current element. -/
def lastElementFrom (first subtractiveCommonDifference : Peano) :
    Peano → Peano
  | .zero => first
  | .successor n =>
    match n with
    | .zero => first
    | .successor _ =>
      match trySubtract first subtractiveCommonDifference with
      | none => first
      | some next => lastElementFrom next subtractiveCommonDifference n

theorem lastElementFrom_one (first subtractiveCommonDifference : Peano) :
    lastElementFrom first subtractiveCommonDifference one = first :=
  rfl

theorem lastElementFrom_succ_succ_of_trySubtract (first subtractiveCommonDifference
    next : Peano) (n : Peano)
    (h : trySubtract first subtractiveCommonDifference = some next) :
    lastElementFrom first subtractiveCommonDifference
        (successor (successor n)) =
      lastElementFrom next subtractiveCommonDifference (successor n) := by
  simp only [lastElementFrom, h]

theorem getElementsFrom_succ_of_trySubtract (first subtractiveCommonDifference
    next : Peano) (n : Peano)
    (h : trySubtract first subtractiveCommonDifference = some next) :
    getElementsFrom first subtractiveCommonDifference n.successor =
      .firstElement first
        (getElementsFrom next subtractiveCommonDifference n) := by
  simp only [getElementsFrom, h]

theorem trySubtract_eq_some_of_getElementsFrom_ge_two
    (first subtractiveCommonDifference : Peano) (n : Peano)
    (hge : two ≤
      (getElementsFrom first subtractiveCommonDifference
        (successor (successor n))).length) :
    ∃ next, trySubtract first subtractiveCommonDifference = some next := by
  match hs : trySubtract first subtractiveCommonDifference with
  | none =>
    have hlen :
        (getElementsFrom first subtractiveCommonDifference
          (successor (successor n))).length = one := by
      simp only [getElementsFrom, hs]
      change Sequences.List.empty.length + one = one
      rfl
    rw [hlen] at hge
    exact (not_two_le_one hge).elim
  | some next =>
    exact ⟨next, rfl⟩

theorem lastElementFrom_le (first subtractiveCommonDifference : Peano)
    (n : Peano) :
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
          eq_of_trySubtract_add subtractiveCommonDifference first next hs
        have hle : next ≤ first := by
          rw [hadd, add_commutative]
          exact le_add_self_left next subtractiveCommonDifference
        exact le_trans hle_next hle

theorem lastElementFrom_lt_first_of_ge_two (first subtractiveCommonDifference :
    Peano) (hdiff : subtractiveCommonDifference ≠ zero) (n : Peano)
    (hge : two ≤
      (getElementsFrom first subtractiveCommonDifference
        (successor (successor n))).length) :
    lastElementFrom first subtractiveCommonDifference
        (successor (successor n)) < first := by
  obtain ⟨next, hs⟩ :=
    trySubtract_eq_some_of_getElementsFrom_ge_two first
      subtractiveCommonDifference n hge
  rw [lastElementFrom_succ_succ_of_trySubtract first
    subtractiveCommonDifference next _ hs]
  have hle :=
    lastElementFrom_le next subtractiveCommonDifference (successor n)
  have hadd :=
    eq_of_trySubtract_add subtractiveCommonDifference first next hs
  have hlt : next < first := by
    rw [hadd, add_commutative]
    exact lt_add_of_right_ne_zero next subtractiveCommonDifference hdiff
  exact lt_of_le_lt hle hlt

/-- Continuing a decreasing arithmetic walk from `prev` by `getElementsFrom`
recovers the last element of that walk, when the first step from `prev` is
defined. -/
theorem tryLastOfArithmeticContinuation_getElementsFrom
    (prev subtractiveCommonDifference next : Peano)
    (n : Peano)
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
        trySubtract_comm subtractiveCommonDifference prev next h, ↓reduceIte]
      have hlast :
          lastElementFrom prev subtractiveCommonDifference
              (successor n.successor) = next := by
        rw [lastElementFrom_succ_succ_of_trySubtract prev
          subtractiveCommonDifference next _ h]
        simp only [lastElementFrom, hs]
        match n with
        | .zero => rfl
        | .successor _ => rfl
      exact congrArg some hlast.symm
    | some next' =>
      simp only [tryLastOfArithmeticContinuation,
        trySubtract_comm subtractiveCommonDifference prev next h, ↓reduceIte]
      have ih' := ih next next' hs
      rw [ih']
      have hlast :
          lastElementFrom next subtractiveCommonDifference n.successor =
            lastElementFrom prev subtractiveCommonDifference
              (successor n.successor) :=
        (lastElementFrom_succ_succ_of_trySubtract prev
          subtractiveCommonDifference next n h).symm
      exact congrArg some hlast

/-- When `getElementsFrom` yields a list of length at least two, reconstructing
recovers the start, subtractive common difference, and last element. -/
theorem tryFromElements_getElementsFrom_ge_two (first subtractiveCommonDifference :
    Peano) (hdiff : subtractiveCommonDifference ≠ zero) (n : Peano)
    (hge : two ≤
        (getElementsFrom first subtractiveCommonDifference
          (successor (successor n))).length) :
    tryFromElements
        (getElementsFrom first subtractiveCommonDifference
          (successor (successor n)))
        hge =
      some ({
        first := some first
        subtractiveCommonDifference := subtractiveCommonDifference
        limit :=
          lastElementFrom first subtractiveCommonDifference
            (successor (successor n))
        subtractiveCommonDifference_ne_zero := hdiff
      } : ArithmeticDecreasing) := by
  obtain ⟨next, hs⟩ :=
    trySubtract_eq_some_of_getElementsFrom_ge_two first
      subtractiveCommonDifference n hge
  have hget :
      getElementsFrom first subtractiveCommonDifference
          (successor (successor n)) =
        .firstElement first
          (getElementsFrom next subtractiveCommonDifference (successor n)) :=
    getElementsFrom_succ_of_trySubtract first subtractiveCommonDifference
      next _ hs
  revert hge
  rw [hget]
  intro hge
  simp only [getElementsFrom, tryFromElements,
    trySubtract_comm subtractiveCommonDifference first next hs]
  split
  · next heq => exact (hdiff heq).elim
  · next _hne =>
    match hs' : trySubtract next subtractiveCommonDifference with
    | none =>
      simp only [tryLastOfArithmeticContinuation]
      have hlast :
          lastElementFrom first subtractiveCommonDifference
              (successor (successor n)) = next := by
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
              (successor (successor n)) :=
        (lastElementFrom_succ_succ_of_trySubtract first
          subtractiveCommonDifference next n hs).symm
      simp only [hlast]

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
          have := eq_of_trySubtract_add x prev d hs
          rwa [hd] at this
        have hs_diff : trySubtract prev diff = some x := by
          rw [hx]
          exact trySubtract_add_right x diff
        have hlen := Sequences.List.length_firstElement x xs
        constructor
        · have h1 :
              last = lastElementFrom x diff xs.length.successor :=
            hlast
          have h2 :
              lastElementFrom x diff xs.length.successor =
                lastElementFrom prev diff
                  (successor xs.length.successor) :=
            (lastElementFrom_succ_succ_of_trySubtract prev diff x
              xs.length hs_diff).symm
          have h3 :
              lastElementFrom prev diff
                  (successor xs.length.successor) =
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
                        have := eq_of_trySubtract_add y x d' hsy
                        rwa [hd'] at this
                      rw [hx']
                      exact trySubtract_add_right y diff
                    rw [hsx] at this
                    nomatch this
                  · rw [if_neg hd'] at h
                    nomatch h
            cases hxs_empty
            rw [Sequences.List.length_firstElement]
            have hget :
                getElementsFrom x diff one =
                  Sequences.List.firstElement x Sequences.List.empty := by
              change
                  Sequences.List.firstElement x
                    (match trySubtract x diff with
                     | none => Sequences.List.empty
                     | some next =>
                       getElementsFrom next diff zero) =
                    Sequences.List.firstElement x Sequences.List.empty
              rw [hsx]
            exact hget.symm
          | some next' =>
            have hxs' := hxs next' hsx
            rw [Sequences.List.length_firstElement]
            have hget :
                getElementsFrom x diff xs.length.successor =
                  Sequences.List.firstElement x
                    (getElementsFrom next' diff xs.length) :=
              getElementsFrom_succ_of_trySubtract x diff next' xs.length hsx
            rw [hget]
            exact congrArg (Sequences.List.firstElement x) hxs'
      · rw [if_neg hd] at h
        nomatch h

theorem lengthFromGap_self (diff : Peano) (hdiff : diff ≠ zero) :
    lengthFromGap diff hdiff (some diff) = successor one := by
  unfold lengthFromGap
  have hdiv :=
    divideWithRemainder_eq_of_mul diff diff hdiff one (multiply_one diff).symm
  simp only [hdiv]

theorem getLength_eq_lengthFromGap_of_gt (first subtractiveCommonDifference
    limit : Peano) (hdiff : subtractiveCommonDifference ≠ zero)
    (hlt : limit < first) :
    getLength {
      first := some first
      subtractiveCommonDifference := subtractiveCommonDifference
      limit := limit
      subtractiveCommonDifference_ne_zero := hdiff
    } =
      lengthFromGap subtractiveCommonDifference hdiff
        (some (subtract first limit (Or.inl hlt))) := by
  simp only [getLength]
  match hc : compare first limit with
  | .less hlt' => exact (not_le_of_gt hlt' (Or.inl hlt)).elim
  | .equal heq =>
    rw [heq] at hlt
    exact (not_lt_self limit hlt).elim
  | .greater hgt =>
    exact congrArg
      (fun g => lengthFromGap subtractiveCommonDifference hdiff (some g))
      (subtract_eq_of_eq (Or.inl hgt) (Or.inl hlt) rfl rfl)

theorem getElementsFrom_length_succ_of_trySubtract
    (first diff next : Peano) (n : Peano)
    (h : trySubtract first diff = some next)
    (hlen : (getElementsFrom first diff n.successor).length = n.successor) :
    (getElementsFrom next diff n).length = n := by
  have hget := getElementsFrom_succ_of_trySubtract first diff next n h
  have hlen' :
      (getElementsFrom first diff n.successor).length =
        (getElementsFrom next diff n).length.successor := by
    rw [hget]
    exact add_one _
  have hsucc :
      n.successor = (getElementsFrom next diff n).length.successor := by
    rw [← hlen', hlen]
  exact (successor_injective hsucc).symm

/-- Length of a progression whose limit is exactly `lastElementFrom` of a
full-length decreasing walk. -/
theorem getLength_lastElementFrom (first diff : Peano)
    (hdiff : diff ≠ zero) (n : Peano) (hne : n ≠ zero)
    (hlen : (getElementsFrom first diff n).length = n) :
    getLength {
      first := some first
      subtractiveCommonDifference := diff
      limit := lastElementFrom first diff n
      subtractiveCommonDifference_ne_zero := hdiff
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
            subtractiveCommonDifference_ne_zero := hdiff
          } = one
      simp only [getLength]
      match hc : compare first first with
      | .greater hgt => exact (not_lt_self first hgt).elim
      | .equal _ => rfl
      | .less hlt => exact (not_lt_self first hlt).elim
    | successor m =>
      have hge : two ≤
          (getElementsFrom first diff
            (successor (successor m))).length := by
        rw [hlen]
        change two ≤ successor (successor m)
        simpa only [two, one] using
          (succ_le_succ (succ_le_succ (zero_le m)))
      obtain ⟨next, hs⟩ :=
        trySubtract_eq_some_of_getElementsFrom_ge_two first diff m hge
      have hlast_eq :=
        lastElementFrom_succ_succ_of_trySubtract first diff next m hs
      have hlen_tail :
          (getElementsFrom next diff (successor m)).length =
            successor m :=
        getElementsFrom_length_succ_of_trySubtract first diff next
          (successor m) hs hlen
      cases m with
      | zero =>
        have hlt : next < first := by
          have hadd := eq_of_trySubtract_add diff first next hs
          rw [hadd, add_commutative]
          exact lt_add_of_right_ne_zero next diff hdiff
        have hget :=
          getLength_eq_lengthFromGap_of_gt first diff next hdiff hlt
        have hgap : subtract first next (Or.inl hlt) = diff :=
          (subtract_eq_of_eq (Or.inl hlt)
              (le_of_trySubtract_eq_some first diff next hs) rfl rfl).trans
            (subtract_eq_diff_of_trySubtract first diff next hs)
        change
            getLength {
              first := some first
              subtractiveCommonDifference := diff
              limit :=
                lastElementFrom first diff
                  (successor (successor zero))
              subtractiveCommonDifference_ne_zero := hdiff
            } =
              successor one
        rw [hlast_eq]
        change
            getLength {
              first := some first
              subtractiveCommonDifference := diff
              limit := next
              subtractiveCommonDifference_ne_zero := hdiff
            } =
              successor one
        rw [hget, hgap, lengthFromGap_self]
      | successor k =>
        have hlt_last :
            lastElementFrom next diff
                (successor (successor k)) < next :=
          lastElementFrom_lt_first_of_ge_two next diff hdiff k (by
            rw [hlen_tail]
            change two ≤ successor (successor k)
            simpa only [two, one] using
              (succ_le_succ (succ_le_succ (zero_le k))))
        have hlt_first : next < first := by
          have hadd := eq_of_trySubtract_add diff first next hs
          rw [hadd, add_commutative]
          exact lt_add_of_right_ne_zero next diff hdiff
        have hlt : lastElementFrom first diff
            (successor (successor k.successor)) < first := by
          rw [hlast_eq]
          exact lt_trans hlt_last hlt_first
        have hget :=
          getLength_eq_lengthFromGap_of_gt first diff
            (lastElementFrom first diff
              (successor (successor k.successor)))
            hdiff hlt
        have hlen' :
            getLength {
              first := some next
              subtractiveCommonDifference := diff
              limit :=
                lastElementFrom next diff
                  (successor (successor k))
              subtractiveCommonDifference_ne_zero := hdiff
            } =
              successor (successor k) :=
          ih next (successor_ne_zero _) hlen_tail
        have hdiff_lt :
            diff <
              subtract first
                (lastElementFrom first diff
                  (successor (successor k.successor)))
                (Or.inl hlt) := by
          have hlast' :
              lastElementFrom first diff
                  (successor (successor k.successor)) =
                lastElementFrom next diff
                  (successor (successor k)) :=
            hlast_eq
          have hsum :
              subtract first
                  (lastElementFrom first diff
                    (successor (successor k.successor)))
                  (Or.inl hlt) +
                lastElementFrom first diff
                  (successor (successor k.successor)) =
              first :=
            subtract_add_cancel _ _ _
          have hadd := eq_of_trySubtract_add diff first next hs
          have : diff +
              lastElementFrom first diff
                (successor (successor k.successor)) < first := by
            rw [hlast', hadd]
            exact add_lt_add_left hlt_last diff
          have hrew :
              diff +
                  lastElementFrom first diff
                    (successor (successor k.successor)) <
                subtract first
                    (lastElementFrom first diff
                      (successor (successor k.successor)))
                    (Or.inl hlt) +
                  lastElementFrom first diff
                    (successor (successor k.successor)) :=
            hsum.symm ▸ this
          exact add_lt_cancel_right hrew
        have hgap_succ :=
          lengthFromGap_succ_of_lt diff hdiff
            (subtract first
              (lastElementFrom first diff
                (successor (successor k.successor)))
              (Or.inl hlt))
            hdiff_lt
        have hdiff_first : diff ≤ first := by
          have hadd := eq_of_trySubtract_add diff first next hs
          rw [hadd]
          exact le_add_self_left diff next
        have hsub_next : subtract first diff hdiff_first = next := by
          have hadd := eq_of_trySubtract_add diff first next hs
          have h1 := subtract_add_cancel first diff hdiff_first
          have h2 : next + diff = first := by
            rw [hadd, add_commutative]
          exact add_cancel_right _ _ diff (h1.trans h2.symm)
        have hlt_sub :
            lastElementFrom first diff
                (successor (successor k.successor)) <
              subtract first diff hdiff_first := by
          rw [hsub_next, hlast_eq]
          exact hlt_last
        let pTmp : ArithmeticDecreasing :=
          {
            first := some first
            subtractiveCommonDifference := diff
            limit :=
              lastElementFrom first diff
                (successor (successor k.successor))
            subtractiveCommonDifference_ne_zero := hdiff
          }
        have hsub_eq :=
          subtract_gap_eq_sub_limit pTmp first hlt hdiff_lt hdiff_first hlt_sub
        have hget_next :=
          getLength_eq_lengthFromGap_of_gt next diff
            (lastElementFrom next diff
              (successor (successor k)))
            hdiff hlt_last
        change
            getLength {
              first := some first
              subtractiveCommonDifference := diff
              limit :=
                lastElementFrom first diff
                  (successor (successor k.successor))
              subtractiveCommonDifference_ne_zero := hdiff
            } =
              successor (successor (successor k))
        rw [hget, hgap_succ]
        have htail :
            lengthFromGap diff hdiff
                (some
                  (subtract
                    (subtract first
                      (lastElementFrom first diff
                        (successor (successor k.successor)))
                      (Or.inl hlt))
                    diff (Or.inl hdiff_lt))) =
              getLength {
                first := some next
                subtractiveCommonDifference := diff
                limit :=
                  lastElementFrom next diff
                    (successor (successor k))
                subtractiveCommonDifference_ne_zero := hdiff
              } := by
          rw [hget_next]
          apply congrArg (lengthFromGap diff hdiff)
          apply congrArg some
          have hlt_sub' :
              lastElementFrom first diff
                  (successor (successor k.successor)) < next := by
            have := hlt_sub
            rwa [hsub_next] at this
          have hmid :
              subtract
                  (subtract first
                    (lastElementFrom first diff
                      (successor (successor k.successor)))
                    (Or.inl hlt))
                  diff (Or.inl hdiff_lt) =
                subtract (subtract first diff hdiff_first)
                  (lastElementFrom first diff
                    (successor (successor k.successor)))
                  (Or.inl hlt_sub) :=
            hsub_eq.symm
          have hmid' :
              subtract (subtract first diff hdiff_first)
                  (lastElementFrom first diff
                    (successor (successor k.successor)))
                  (Or.inl hlt_sub) =
                subtract next
                  (lastElementFrom first diff
                    (successor (successor k.successor)))
                  (Or.inl hlt_sub') :=
            subtract_eq_of_eq (Or.inl hlt_sub) (Or.inl hlt_sub') hsub_next rfl
          have hend :
              subtract next
                  (lastElementFrom first diff
                    (successor (successor k.successor)))
                  (Or.inl hlt_sub') =
                subtract next
                  (lastElementFrom next diff
                    (successor (successor k)))
                  (Or.inl hlt_last) :=
            subtract_eq_of_eq (Or.inl hlt_sub') (Or.inl hlt_last) rfl hlast_eq
          exact hmid.trans (hmid'.trans hend)
        rw [htail, hlen']

/-- `getElements` recovers the original list from a successful
`tryFromElements`. -/
theorem getElements_tryFromElements (elements : Sequences.List Peano)
    (hge : two ≤ elements.length)
    (p : ArithmeticDecreasing)
    (h : tryFromElements elements hge = some p) :
    getElements p = elements := by
  match helem : elements with
  | .empty =>
    subst helem
    exact (not_two_le_zero (by
      change two ≤ zero
      exact hge)).elim
  | .firstElement _ .empty =>
    subst helem
    exact (not_two_le_one (by
      change two ≤ one
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
      by_cases hdiff0 : diff = zero
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
            simp only [tryLastOfArithmeticContinuation, hs, ↓reduceIte, hl]
          obtain ⟨hlast, hrest_forall⟩ :=
            eq_getElementsFrom_of_tryLastOfArithmeticContinuation x diff
              (Sequences.List.firstElement y ys) last hcont
          have hs_diff : trySubtract x diff = some y := by
            rw [eq_of_trySubtract_add y x diff hs]
            exact trySubtract_add_right y diff
          have hrest := hrest_forall y hs_diff
          have hne :
              (Sequences.List.firstElement y ys).length.successor ≠ zero :=
            successor_ne_zero _
          have hle : last ≤ x := by
            have :=
              lastElementFrom_le x diff
                (Sequences.List.firstElement y ys).length.successor
            rwa [← hlast] at this
          have hf : (toProgression
              {
                first := some x
                subtractiveCommonDifference := diff
                limit := last
                subtractiveCommonDifference_ne_zero := hdiff0
              }).first = some x := by
            simp only [toProgression, hle, ↓reduceIte]
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
            exact Sequences.List.length_firstElement x _
          have hlenp :
              getLength
                  {
                    first := some x
                    subtractiveCommonDifference := diff
                    limit := last
                    subtractiveCommonDifference_ne_zero := hdiff0
                  } =
                (Sequences.List.firstElement y ys).length.successor := by
            rw [hlast]
            exact getLength_lastElementFrom x diff hdiff0
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

theorem toProgression_first_lastElementFrom (first diff : Peano)
    (hdiff : diff ≠ zero) (n : Peano) (_hne : n ≠ zero) :
    (toProgression {
      first := some first
      subtractiveCommonDifference := diff
      limit := lastElementFrom first diff n
      subtractiveCommonDifference_ne_zero := hdiff
    }).first = some first := by
  simp only [toProgression]
  have hle := lastElementFrom_le first diff n
  simp only [hle, ↓reduceIte]

/-- In-range `tryGetElement` matches `getElementFrom` on the progression first. -/
theorem tryGetElement_eq_some_getElementFrom_of_le (p : ArithmeticDecreasing)
    (first : Peano) (hf : (toProgression p).first = some first)
    (index : OrdinalNatural.Peano)
    (hle : fromOrdinal index ≤ getLength p) :
    Sequences.Progression.tryGetElement index (toProgression p) =
      some (getElementFrom first p.subtractiveCommonDifference index) := by
  have hle' :
      fromOrdinal index ≤
        Sequences.Progression.getLength (toProgression p) (toProgression_finite p) :=
    getLength_eq p ▸ hle
  have htry :=
    Sequences.Progression.tryGetElement_eq_some_getElement (toProgression p)
      (toProgression_finite p) index hle'
  rw [htry, ← getElement_eq p index hle]
  unfold getElement
  split
  · next hfnone =>
    rw [hf] at hfnone
    cases hfnone
  · next first' hfsome =>
    have : first' = first := by
      rw [hf] at hfsome
      injection hfsome with hfeq
      exact hfeq.symm
    rw [this]

/-- Out-of-range `tryGetElement` is `none`. -/
theorem tryGetElement_eq_none_of_length_lt (p : ArithmeticDecreasing)
    (index : OrdinalNatural.Peano)
    (hlt : getLength p < fromOrdinal index) :
    Sequences.Progression.tryGetElement index (toProgression p) = none := by
  have hlt' :
      Sequences.Progression.getLength (toProgression p) (toProgression_finite p) <
        fromOrdinal index :=
    getLength_eq p ▸ hlt
  exact Sequences.Progression.tryGetElement_eq_none_of_getLength_lt
    (toProgression p) (toProgression_finite p) index hlt'

theorem toProgression_first_eq_some_of_pos_length (p : ArithmeticDecreasing)
    (h : getLength p ≠ zero) :
    ∃ first, (toProgression p).first = some first := by
  cases hf : (toProgression p).first with
  | none =>
    exact False.elim (h (getLength_eq_zero_of_toProgression_first_none p hf))
  | some first =>
    exact ⟨first, rfl⟩

/-- Progressions with the same first element, subtractive common difference, and
length are equivalent. -/
theorem equivalence_of_same_params (p q : ArithmeticDecreasing) (first : Peano)
    (hp : (toProgression p).first = some first)
    (hq : (toProgression q).first = some first)
    (hdiff : p.subtractiveCommonDifference = q.subtractiveCommonDifference)
    (hlen : getLength p = getLength q) :
    Equivalence p q := by
  intro index
  match (inferInstance : Decidable (fromOrdinal index ≤ getLength p)) with
  | isTrue hleP =>
    have hleQ : fromOrdinal index ≤ getLength q := hlen ▸ hleP
    have htp := tryGetElement_eq_some_getElementFrom_of_le p first hp index hleP
    have htq := tryGetElement_eq_some_getElementFrom_of_le q first hq index hleQ
    simp only [htp, htq, hdiff]
    exact Option.Rel.some rfl
  | isFalse nhleP =>
    have hltP : getLength p < fromOrdinal index := lt_of_not_le nhleP
    have hltQ : getLength q < fromOrdinal index := hlen ▸ hltP
    have htp := tryGetElement_eq_none_of_length_lt p index hltP
    have htq := tryGetElement_eq_none_of_length_lt q index hltQ
    simp only [htp, htq]
    exact Option.Rel.none

/-- A length of at least two forces a defined subtractive step from the
progression first that stays at least the limit. -/
theorem trySubtract_eq_some_of_getLength_ge_two (p : ArithmeticDecreasing)
    (first : Peano) (hf : (toProgression p).first = some first)
    (hge : two ≤ getLength p) :
    ∃ next, trySubtract first p.subtractiveCommonDifference = some next ∧
      p.limit ≤ next := by
  have hAcc :=
    Sequences.Progression.acc_first_of_finite (toProgression p)
      (toProgression_finite p)
  have hAcc' :
      Acc (Sequences.Progression.OptionStep (toProgression p).next)
        (some first) :=
    hf ▸ hAcc
  have hleP : fromOrdinal OrdinalNatural.Peano.one.successor ≤ getLength p := by
    simpa only [fromOrdinal, two, one] using hge
  have hleFrom :
      fromOrdinal OrdinalNatural.Peano.one.successor ≤
        Sequences.Progression.getLengthFrom (toProgression p).next (some first)
          hAcc' := by
    have hle' :
        fromOrdinal OrdinalNatural.Peano.one.successor ≤
          Sequences.Progression.getLength (toProgression p)
            (toProgression_finite p) :=
      getLength_eq p ▸ hleP
    dsimp only [Sequences.Progression.getLength] at hle'
    have hEq :=
      getLengthFrom_eq_of_current_eq (toProgression p).next hf hAcc
    rwa [hEq] at hle'
  obtain ⟨y, hs, hnext⟩ :=
    next_eq_some_of_succ_le_getLengthFrom p first OrdinalNatural.Peano.one
      hAcc' hleFrom
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

/-- Stepping from the progression first to the next in-range term decreases
`getLength` by one. -/
theorem getLength_succ_of_next (p : ArithmeticDecreasing) (first next : Peano)
    (hf : (toProgression p).first = some first)
    (hs : trySubtract first p.subtractiveCommonDifference = some next)
    (hle_lim : p.limit ≤ next) :
    getLength p =
      (getLength {
        first := some next
        subtractiveCommonDifference := p.subtractiveCommonDifference
        limit := p.limit
        subtractiveCommonDifference_ne_zero :=
          p.subtractiveCommonDifference_ne_zero
      }).successor := by
  let p' : ArithmeticDecreasing :=
    {
      first := some next
      subtractiveCommonDifference := p.subtractiveCommonDifference
      limit := p.limit
      subtractiveCommonDifference_ne_zero :=
        p.subtractiveCommonDifference_ne_zero
    }
  have hnext : (toProgression p).next first = some next :=
    next_eq_some_of_limit_le p first next hs hle_lim
  have hf_p' : (toProgression p').first = some next := by
    simp only [toProgression, p', hle_lim, ↓reduceIte]
  have hAcc :=
    Sequences.Progression.acc_first_of_finite (toProgression p)
      (toProgression_finite p)
  have hAcc' :
      Acc (Sequences.Progression.OptionStep (toProgression p).next)
        (some first) :=
    hf ▸ hAcc
  have hAcc_p' :=
    Sequences.Progression.acc_first_of_finite (toProgression p')
      (toProgression_finite p')
  have hAcc_p'' :
      Acc (Sequences.Progression.OptionStep (toProgression p').next)
        (some next) :=
    hf_p' ▸ hAcc_p'
  rw [getLength_eq p, getLength_eq p']
  dsimp only [Sequences.Progression.getLength]
  have hwalk :
      Sequences.Progression.getLengthFrom (toProgression p).next
          (toProgression p).first hAcc =
        Sequences.Progression.getLengthFrom (toProgression p).next (some first)
          hAcc' :=
    getLengthFrom_eq_of_current_eq (toProgression p).next hf hAcc
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
  apply congrArg successor
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
    (first : Peano) (hf : (toProgression p).first = some first)
    (n : Peano) (hle : n ≤ getLength p) :
    (getElementsFrom first p.subtractiveCommonDifference n).length = n := by
  induction n generalizing p first with
  | zero =>
    rfl
  | successor n ih =>
    cases n with
    | zero =>
      have hget :
          getElementsFrom first p.subtractiveCommonDifference
              (successor zero) =
            Sequences.List.firstElement first
              (match trySubtract first p.subtractiveCommonDifference with
               | none => Sequences.List.empty
               | some next =>
                 getElementsFrom next p.subtractiveCommonDifference zero) :=
        rfl
      rw [hget]
      match trySubtract first p.subtractiveCommonDifference with
      | none => rfl
      | some _ => rfl
    | successor m =>
      have hge : two ≤ getLength p :=
        le_trans
          (by
            change two ≤ successor (successor m)
            simpa only [two, one] using
              (succ_le_succ (succ_le_succ (zero_le m))))
          hle
      obtain ⟨next, hs, hle_lim⟩ :=
        trySubtract_eq_some_of_getLength_ge_two p first hf hge
      have hget :=
        getElementsFrom_succ_of_trySubtract first p.subtractiveCommonDifference
          next (successor m) hs
      let p' : ArithmeticDecreasing :=
        {
          first := some next
          subtractiveCommonDifference := p.subtractiveCommonDifference
          limit := p.limit
          subtractiveCommonDifference_ne_zero :=
            p.subtractiveCommonDifference_ne_zero
        }
      have hf' : (toProgression p').first = some next := by
        simp only [toProgression, p', hle_lim, ↓reduceIte]
      have hlen_succ := getLength_succ_of_next p first next hf hs hle_lim
      have hle' : successor m ≤ getLength p' := by
        have : successor (successor m) ≤ getLength p := hle
        have hform : getLength p = (getLength p').successor := hlen_succ
        rw [hform] at this
        exact le_of_succ_le_succ this
      have ih' := ih p' next hf' hle'
      rw [hget]
      change
          (getElementsFrom next p.subtractiveCommonDifference
            (successor m)).length + one =
            successor (successor m)
      have ih'' :
          (getElementsFrom next p.subtractiveCommonDifference
            (successor m)).length =
            successor m := by
        change
            (getElementsFrom next p'.subtractiveCommonDifference
              (successor m)).length =
              successor m at ih'
        exact ih'
      rw [ih'', add_one]

theorem getElements_length (p : ArithmeticDecreasing) :
    (getElements p).length = getLength p := by
  match hf : (toProgression p).first with
  | none =>
    have hlen : getLength p = zero :=
      getLength_eq_zero_of_toProgression_first_none p hf
    simp only [getElements, hf, hlen]
    rfl
  | some first =>
    simp only [getElements, hf]
    exact getElementsFrom_length_of_le_getLength p first hf (getLength p)
      (Or.inr rfl)

/-- `tryFromElements` recovers a progression equivalent to `p` from
`getElements p` when `p` has length at least two. -/
theorem tryFromElements_getElements (p : ArithmeticDecreasing)
    (hge : two ≤ getLength p) :
    ∃ (hLen : two ≤ (getElements p).length)
      (q : ArithmeticDecreasing),
      tryFromElements (getElements p) hLen = some q ∧ p ≈ q := by
  obtain ⟨m, hlen⟩ := eq_succ_succ_of_two_le (getLength p) hge
  have hne0 : getLength p ≠ zero := by
    intro heq
    rw [heq] at hge
    exact not_two_le_zero hge
  obtain ⟨first, hf⟩ := toProgression_first_eq_some_of_pos_length p hne0
  have hget :
      getElements p =
        getElementsFrom first p.subtractiveCommonDifference (getLength p) := by
    simp only [getElements, hf]
  have hLen : two ≤ (getElements p).length := by
    rw [getElements_length]
    exact hge
  let last :=
    lastElementFrom first p.subtractiveCommonDifference
      (successor (successor m))
  let q : ArithmeticDecreasing :=
    {
      first := some first
      subtractiveCommonDifference := p.subtractiveCommonDifference
      limit := last
      subtractiveCommonDifference_ne_zero :=
        p.subtractiveCommonDifference_ne_zero
    }
  refine ⟨hLen, q, ?_⟩
  constructor
  · have hlen_walk :
        (getElementsFrom first p.subtractiveCommonDifference
          (successor (successor m))).length =
          successor (successor m) := by
      have := getElementsFrom_length_of_le_getLength p first hf
        (successor (successor m))
        (by rw [hlen]; exact Or.inr rfl)
      exact this
    have hge' : two ≤
        (getElementsFrom first p.subtractiveCommonDifference
          (successor (successor m))).length := by
      rw [hlen_walk]
      change two ≤ successor (successor m)
      simpa only [two, one] using
        (succ_le_succ (succ_le_succ (zero_le m)))
    have htry :=
      tryFromElements_getElementsFrom_ge_two first
        p.subtractiveCommonDifference p.subtractiveCommonDifference_ne_zero m
        hge'
    have hget' :
        getElements p =
          getElementsFrom first p.subtractiveCommonDifference
            (successor (successor m)) := by
      rw [hget, hlen]
    revert hLen
    rw [hget']
    intro hLen
    exact htry
  · have hfq :=
      toProgression_first_lastElementFrom first p.subtractiveCommonDifference
        p.subtractiveCommonDifference_ne_zero (successor (successor m))
        (successor_ne_zero _)
    have hlen_walk :
        (getElementsFrom first p.subtractiveCommonDifference
          (successor (successor m))).length =
          successor (successor m) := by
      have := getElementsFrom_length_of_le_getLength p first hf
        (successor (successor m))
        (by rw [hlen]; exact Or.inr rfl)
      exact this
    have hlenq :=
      getLength_lastElementFrom first p.subtractiveCommonDifference
        p.subtractiveCommonDifference_ne_zero (successor (successor m))
        (successor_ne_zero _) hlen_walk
    exact equivalence_of_same_params p q first hf hfq rfl
      (by rw [hlen, hlenq])

end ArithmeticDecreasing

end ZeroMath.Numbers.CardinalNatural.Peano.Progressions
