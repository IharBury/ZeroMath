import ZeroMath.Numbers.CardinalNatural.Peano
import ZeroMath.Sequences.List
import ZeroMath.Sequences.Progression

namespace ZeroMath.Numbers.CardinalNatural.Peano.Progressions

/-- A finite increasing arithmetic progression of Peano numbers with positive
common difference, defined by an optional first element (`none` for the empty
progression), the common difference, and a limit such that no element is
greater than the limit. The progression is also empty when the first element
is greater than the limit. -/
structure FiniteArithmeticIncreasing where
  first : Option Peano
  commonDifference : Peano
  limit : Peano
  commonDifference_ne_zero : commonDifference ≠ zero

namespace FiniteArithmeticIncreasing

/-- Convert a finite increasing arithmetic progression to a general progression
by taking the same optional first element when it does not exceed the limit
(otherwise the empty progression) and advancing by the common difference while
the next element does not exceed the limit. -/
def toProgression (p : FiniteArithmeticIncreasing) : Sequences.Progression Peano where
  first :=
    match p.first with
    | none => none
    | some x => if x ≤ p.limit then some x else none
  next := fun x =>
    let y := x + p.commonDifference
    if y ≤ p.limit then some y else none

/-- Every element obtained from `tryGetElement` is at most the limit. -/
theorem tryGetElement_le_limit (p : FiniteArithmeticIncreasing)
    (index : OrdinalNatural.Peano) (x : Peano)
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

/-- If `tryGetElement` returns a value, the ordinal index (as a cardinal) is at
most the successor of that value, because the progression is strictly
increasing with positive common difference. -/
theorem fromOrdinal_le_succ_of_tryGetElement_eq_some
    (p : FiniteArithmeticIncreasing) (index : OrdinalNatural.Peano) (x : Peano)
    (h : Sequences.Progression.tryGetElement index (toProgression p) = some x) :
    fromOrdinal index ≤ x.successor := by
  induction index generalizing x with
  | one =>
    exact succ_le_succ (zero_le x)
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
        have hn : fromOrdinal n ≤ y.successor := ih y hm
        have hy_lt : y < y + p.commonDifference :=
          lt_add_of_right_ne_zero y p.commonDifference p.commonDifference_ne_zero
        have hy_le : y.successor ≤ y + p.commonDifference := succ_le_of_lt hy_lt
        exact succ_le_succ (le_trans hn (heq ▸ hy_le))
      · simp only [hle, ↓reduceIte] at hnext
        nomatch hnext

/-- The progression obtained from a finite increasing arithmetic progression is
finite: `tryGetElement` at the ordinal corresponding to
`successor (successor limit)` is always `none`, since any returned value would
have to be both ≥ `successor limit` and ≤ `limit`. -/
theorem toProgression_finite (p : FiniteArithmeticIncreasing) :
    Sequences.Progression.Finite (toProgression p) := by
  have hne : (p.limit.successor).successor ≠ zero :=
    successor_ne_zero p.limit.successor
  refine ⟨toOrdinal (p.limit.successor).successor hne, ?_⟩
  cases h :
      Sequences.Progression.tryGetElement
        (toOrdinal (p.limit.successor).successor hne) (toProgression p) with
  | none =>
    rfl
  | some x =>
    have hle_lim :=
      tryGetElement_le_limit p (toOrdinal (p.limit.successor).successor hne) x h
    have hle_idx :=
      fromOrdinal_le_succ_of_tryGetElement_eq_some p
        (toOrdinal (p.limit.successor).successor hne) x h
    rw [fromOrdinal_toOrdinal] at hle_idx
    have hle' : p.limit.successor ≤ x := le_of_succ_le_succ hle_idx
    exact (not_succ_le p.limit (le_trans hle' hle_lim)).elim

/-- Length remaining from an element already known to lie in the progression,
given the room above that element up to the limit (`none` when the element
equals the limit). Computed with one division by the common difference instead
of comparing each successive term to the limit. -/
def lengthFromGap (diff : Peano) (hdiff : diff ≠ zero) : Option Peano → Peano
  | none => one
  | some gap =>
    match divideWithRemainder gap diff hdiff with
    | (q, _) => q.successor

/-- The length of a finite increasing arithmetic progression: the number of
elements before `tryGetElement` first returns `none`. Uses a single comparison
of the first element to the limit and one division, avoiding a comparison at
every step of the progression. -/
def getLength (p : FiniteArithmeticIncreasing) : Peano :=
  match p.first with
  | none => zero
  | some first =>
    match compare first p.limit with
    | .greater _ => zero
    | .equal _ => one
    | .less hlt =>
      lengthFromGap p.commonDifference p.commonDifference_ne_zero
        (some (subtract p.limit first (Or.inl hlt)))

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

theorem next_eq_none_of_add_not_le (p : FiniteArithmeticIncreasing) (x : Peano)
    (h : ¬ x + p.commonDifference ≤ p.limit) :
    (toProgression p).next x = none := by
  change (if x + p.commonDifference ≤ p.limit then some (x + p.commonDifference)
      else none) = none
  simp only [h, ↓reduceIte]

theorem next_eq_some_of_add_le (p : FiniteArithmeticIncreasing) (x : Peano)
    (h : x + p.commonDifference ≤ p.limit) :
    (toProgression p).next x = some (x + p.commonDifference) := by
  change (if x + p.commonDifference ≤ p.limit then some (x + p.commonDifference)
      else none) = some (x + p.commonDifference)
  simp only [h, ↓reduceIte]

theorem le_iff_add_le_of_lt_limit (p : FiniteArithmeticIncreasing) (x : Peano)
    (hlt : x < p.limit) :
    p.commonDifference ≤ subtract p.limit x (Or.inl hlt) ↔
      x + p.commonDifference ≤ p.limit := by
  have hsum : subtract p.limit x (Or.inl hlt) + x = p.limit :=
    subtract_add_cancel p.limit x (Or.inl hlt)
  have hsum' : x + subtract p.limit x (Or.inl hlt) = p.limit := by
    rw [add_commutative, hsum]
  constructor
  · intro hd
    have := add_le_add_left hd x
    rwa [← hsum']
  · intro hxd
    have hrew :
        p.commonDifference + x ≤ subtract p.limit x (Or.inl hlt) + x := by
      rw [add_commutative p.commonDifference, hsum]
      exact hxd
    cases hrew with
    | inl hlt' => exact Or.inl (add_lt_cancel_right hlt')
    | inr heq => exact Or.inr (add_cancel_right _ _ x heq)

theorem add_commonDifference_lt_limit_of_lt_gap (p : FiniteArithmeticIncreasing)
    (x : Peano) (hlt : x < p.limit)
    (hdiff : p.commonDifference < subtract p.limit x (Or.inl hlt)) :
    x + p.commonDifference < p.limit := by
  have hsum : subtract p.limit x (Or.inl hlt) + x = p.limit :=
    subtract_add_cancel p.limit x (Or.inl hlt)
  have : p.commonDifference + x < subtract p.limit x (Or.inl hlt) + x :=
    add_lt_add_right hdiff x
  rwa [add_commutative p.commonDifference, hsum] at this

theorem subtract_limit_add_commonDifference (p : FiniteArithmeticIncreasing)
    (x : Peano) (hlt : x < p.limit)
    (hdiff : p.commonDifference < subtract p.limit x (Or.inl hlt))
    (hlt' : x + p.commonDifference < p.limit) :
    subtract p.limit (x + p.commonDifference) (Or.inl hlt') =
      subtract (subtract p.limit x (Or.inl hlt)) p.commonDifference
        (Or.inl hdiff) := by
  have hsum : subtract p.limit x (Or.inl hlt) + x = p.limit :=
    subtract_add_cancel p.limit x (Or.inl hlt)
  apply add_cancel_right _ _ (x + p.commonDifference)
  have h1 :=
    subtract_add_cancel p.limit (x + p.commonDifference) (Or.inl hlt')
  have h2 :=
    subtract_add_cancel (subtract p.limit x (Or.inl hlt)) p.commonDifference
      (Or.inl hdiff)
  rw [h1, add_commutative x, ← add_associative, h2, hsum]

/-- Gap above `x` up to `limit`, or `none` when `x = limit`. -/
def gapToLimit (x limit : Peano) (hx : x ≤ limit) : Option Peano :=
  match compare x limit with
  | .greater hgt => (not_le_of_gt hgt hx).elim
  | .equal _ => none
  | .less hlt => some (subtract limit x (Or.inl hlt))

theorem gapToLimit_equal {x limit : Peano} (hx : x ≤ limit) (heq : x = limit) :
    gapToLimit x limit hx = none := by
  unfold gapToLimit
  match hc : compare x limit with
  | .greater hgt => exact (not_le_of_gt hgt hx).elim
  | .equal _ => rfl
  | .less hlt =>
    rw [heq] at hlt
    exact (not_lt_self limit hlt).elim

theorem gapToLimit_less {x limit : Peano} (hx : x ≤ limit) (hlt : x < limit) :
    gapToLimit x limit hx = some (subtract limit x (Or.inl hlt)) := by
  unfold gapToLimit
  match hc : compare x limit with
  | .greater hgt => exact (not_le_of_gt hgt hx).elim
  | .equal heq =>
    rw [heq] at hlt
    exact (not_lt_self limit hlt).elim
  | .less hlt' =>
    exact congrArg some
      (subtract_eq_of_eq (Or.inl hlt') (Or.inl hlt) rfl rfl)

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
theorem getLengthFrom_eq_lengthFromGap (p : FiniteArithmeticIncreasing)
    (current : Option Peano)
    (hAcc : Acc (Sequences.Progression.OptionStep (toProgression p).next) current) :
    (current = none →
      Sequences.Progression.getLengthFrom (toProgression p).next current hAcc =
        zero) ∧
    (∀ x, current = some x → ∀ hx : x ≤ p.limit,
      Sequences.Progression.getLengthFrom (toProgression p).next current hAcc =
        lengthFromGap p.commonDifference p.commonDifference_ne_zero
          (gapToLimit x p.limit hx)) := by
  refine Acc.rec
    (motive := fun current hAcc =>
      (current = none →
        Sequences.Progression.getLengthFrom (toProgression p).next current hAcc =
          zero) ∧
      (∀ x, current = some x → ∀ hx : x ≤ p.limit,
        Sequences.Progression.getLengthFrom (toProgression p).next current hAcc =
          lengthFromGap p.commonDifference p.commonDifference_ne_zero
            (gapToLimit x p.limit hx)))
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
        | .greater hgt => exact (not_le_of_gt hgt hx).elim
        | .equal heq =>
          have hnext : (toProgression p).next x = none := by
            apply next_eq_none_of_add_not_le
            intro hle
            have hlt : x < x + p.commonDifference :=
              lt_add_of_right_ne_zero x p.commonDifference
                p.commonDifference_ne_zero
            have : x < p.limit := lt_of_lt_of_le hlt hle
            rw [heq] at this
            exact not_lt_self p.limit this
          have hgap := gapToLimit_equal hx heq
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
        | .less hlt =>
          have hgap := gapToLimit_less hx hlt
          rw [hgap]
          match hd : compare p.commonDifference
              (subtract p.limit x (Or.inl hlt)) with
          | .greater hgt =>
            have hnot : ¬ x + p.commonDifference ≤ p.limit := by
              intro hle
              exact not_le_of_gt hgt
                ((le_iff_add_le_of_lt_limit p x hlt).mpr hle)
            have hnext := next_eq_none_of_add_not_le p x hnot
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
                (subtract p.limit x (Or.inl hlt)) p.commonDifference
                p.commonDifference_ne_zero zero
                (subtract p.limit x (Or.inl hlt)) hgt (by
                  rw [multiply_zero, zero_add])
            simp only [lengthFromGap, hnil', hdiv]
          | .equal heq =>
            have hle_diff :
                p.commonDifference ≤ subtract p.limit x (Or.inl hlt) :=
              Or.inr heq
            have hle_add := (le_iff_add_le_of_lt_limit p x hlt).mp hle_diff
            have hnext := next_eq_some_of_add_le p x hle_add
            have hsum : subtract p.limit x (Or.inl hlt) + x = p.limit :=
              subtract_add_cancel p.limit x (Or.inl hlt)
            have hx_next : x + p.commonDifference = p.limit := by
              rw [← hsum, ← heq, add_commutative]
            have hx_le' : x + p.commonDifference ≤ p.limit := Or.inr hx_next
            have hstep :
                Sequences.Progression.OptionStep (toProgression p).next
                  (some (x + p.commonDifference)) (some x) :=
              hnext ▸ Sequences.Progression.OptionStep.step x
            have ih' := (ih _ hstep).2 (x + p.commonDifference) rfl hx_le'
            have hgap' := gapToLimit_equal hx_le' hx_next
            have hdiv :=
              divideWithRemainder_eq_of_mul
                (subtract p.limit x (Or.inl hlt)) p.commonDifference
                p.commonDifference_ne_zero one (by
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
            have hlt' :=
              add_commonDifference_lt_limit_of_lt_gap p x hlt hdiff
            have hsub :=
              subtract_limit_add_commonDifference p x hlt hdiff hlt'
            have hle_diff :
                p.commonDifference ≤ subtract p.limit x (Or.inl hlt) :=
              Or.inl hdiff
            have hle_add := (le_iff_add_le_of_lt_limit p x hlt).mp hle_diff
            have hnext := next_eq_some_of_add_le p x hle_add
            have hx_le' : x + p.commonDifference ≤ p.limit := Or.inl hlt'
            have hstep :
                Sequences.Progression.OptionStep (toProgression p).next
                  (some (x + p.commonDifference)) (some x) :=
              hnext ▸ Sequences.Progression.OptionStep.step x
            have ih' := (ih _ hstep).2 (x + p.commonDifference) rfl hx_le'
            have hgap' := gapToLimit_less hx_le' hlt'
            have hlen :=
              lengthFromGap_succ_of_lt p.commonDifference
                p.commonDifference_ne_zero
                (subtract p.limit x (Or.inl hlt)) hdiff
            have hnext_len :
                Sequences.Progression.getLengthFrom (toProgression p).next
                  ((toProgression p).next x)
                  (hAccx.inv (Sequences.Progression.OptionStep.step x)) =
                  lengthFromGap p.commonDifference
                    p.commonDifference_ne_zero
                    (some (subtract (subtract p.limit x (Or.inl hlt))
                      p.commonDifference (Or.inl hdiff))) := by
              have htmp := ih'
              simp only [hgap'] at htmp
              rw [getLengthFrom_eq_of_acc_eq _ _ _
                (hcurr _ (Sequences.Progression.OptionStep.step x))]
              simpa [hnext, hsub] using htmp
            simp only [hnext_len, hlen])
    hAcc

/-- `getLength` agrees with walking `toProgression` via `Progression.getLength`. -/
theorem getLength_eq (p : FiniteArithmeticIncreasing) :
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
    | greater hgt =>
      have hnot : ¬ first ≤ p.limit := not_le_of_gt hgt
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
      have hle : first ≤ p.limit := Or.inr heq
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
        simpa [gapToLimit_equal hle heq, lengthFromGap] using hx
      exact hwalk.symm
    | less hlt =>
      have hle : first ≤ p.limit := Or.inl hlt
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
            lengthFromGap p.commonDifference p.commonDifference_ne_zero
              (some (subtract p.limit first (Or.inl hlt))) := by
        rw [getLengthFrom_eq_of_current_eq _ hfirst hAcc]
        rw [getLengthFrom_eq_of_acc_eq _ _ _ hAcc']
        simpa [gapToLimit_less hle hlt] using hx
      exact hwalk.symm

/-- Element at a positive ordinal index starting from a known first value,
advancing by the common difference with no limit comparisons. -/
def getElementFrom (first commonDifference : Peano) :
    OrdinalNatural.Peano → Peano
  | .one => first
  | .successor n => getElementFrom first commonDifference n + commonDifference

/-- Shifting the start by one common difference decreases the index by one. -/
theorem getElementFrom_succ (first commonDifference : Peano)
    (n : OrdinalNatural.Peano) :
    getElementFrom first commonDifference n.successor =
      getElementFrom (first + commonDifference) commonDifference n := by
  induction n with
  | one =>
    rfl
  | successor n ih =>
    calc
      getElementFrom first commonDifference
            (OrdinalNatural.Peano.successor n).successor
          = getElementFrom first commonDifference
              (OrdinalNatural.Peano.successor n) + commonDifference :=
            rfl
      _ = getElementFrom (first + commonDifference) commonDifference n +
            commonDifference := by rw [ih]
      _ = getElementFrom (first + commonDifference) commonDifference
            (OrdinalNatural.Peano.successor n) := rfl

/-- If `toProgression` has no first element, the length is zero. -/
theorem getLength_eq_zero_of_toProgression_first_none
    (p : FiniteArithmeticIncreasing)
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
    (p : FiniteArithmeticIncreasing) (index : OrdinalNatural.Peano)
    (hle : fromOrdinal index ≤ getLength p)
    (h : (toProgression p).first = none) : False := by
  have hlen := getLength_eq_zero_of_toProgression_first_none p h
  have hle' : fromOrdinal index ≤ zero := hlen ▸ hle
  exact fromOrdinal_ne_zero index (eq_zero_of_le_zero _ hle')

/-- A successor index within the remaining length forces a next term equal to
the current element plus the common difference. -/
theorem next_eq_some_of_succ_le_getLengthFrom (p : FiniteArithmeticIncreasing)
    (x : Peano) (n : OrdinalNatural.Peano)
    (hAcc : Acc (Sequences.Progression.OptionStep (toProgression p).next)
      (some x))
    (hle : fromOrdinal n.successor ≤
      Sequences.Progression.getLengthFrom (toProgression p).next (some x)
        hAcc) :
    (toProgression p).next x = some (x + p.commonDifference) ∧
      x + p.commonDifference ≤ p.limit := by
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
    have hprog :
        (toProgression p).next x =
          if x + p.commonDifference ≤ p.limit then
            some (x + p.commonDifference)
          else
            none :=
      rfl
    rw [hprog] at hnext
    by_cases hle_add : x + p.commonDifference ≤ p.limit
    · simp only [hle_add, ↓reduceIte] at hnext
      exact ⟨hnext.symm, hle_add⟩
    · simp only [hle_add, ↓reduceIte] at hnext
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
`getElementFrom` (additions only, no further limit comparisons). -/
theorem getElementFrom_eq_progression (p : FiniteArithmeticIncreasing)
    (x : Peano)
    (hAcc : Acc (Sequences.Progression.OptionStep (toProgression p).next)
      (some x))
    (index : OrdinalNatural.Peano)
    (hle : fromOrdinal index ≤
      Sequences.Progression.getLengthFrom (toProgression p).next (some x)
        hAcc) :
    getElementFrom x p.commonDifference index =
      Sequences.Progression.getElementFrom (toProgression p).next (some x) hAcc
        index hle := by
  induction index generalizing x hAcc with
  | one =>
    rfl
  | successor n ih =>
    obtain ⟨hnext, _hx_next⟩ :=
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
          (some (x + p.commonDifference)) :=
      hnext ▸ hAcc.inv (Sequences.Progression.OptionStep.step x)
    have hle_next :
        fromOrdinal n ≤
          Sequences.Progression.getLengthFrom (toProgression p).next
            (some (x + p.commonDifference)) hAcc_next := by
      have hEq :=
        getLengthFrom_eq_of_current_eq (toProgression p).next hnext
          (hAcc.inv (Sequences.Progression.OptionStep.step x))
      rwa [← hEq]
    have ih' := ih (x + p.commonDifference) hAcc_next hle_next
    rw [getElementFrom_succ]
    change
        getElementFrom (x + p.commonDifference) p.commonDifference n =
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
then advancing by repeated addition of the common difference — avoiding a
limit comparison at every step of the walk. -/
def getElement (p : FiniteArithmeticIncreasing) (index : OrdinalNatural.Peano)
    (hle : fromOrdinal index ≤ getLength p) : Peano :=
  match hf : (toProgression p).first with
  | none =>
    (not_fromOrdinal_le_getLength_of_first_none p index hle hf).elim
  | some first =>
    getElementFrom first p.commonDifference index

/-- `getElement` agrees with walking `toProgression` via `Progression.getElement`. -/
theorem getElement_eq (p : FiniteArithmeticIncreasing)
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

/-- Two finite increasing arithmetic progressions are equivalent when their
underlying progressions yield related elements (equality for Peano) at every
positive ordinal index. -/
def Equivalence (p q : FiniteArithmeticIncreasing) : Prop :=
  Sequences.Progression.Equivalence (toProgression p) (toProgression q)

instance : HasEquiv FiniteArithmeticIncreasing where
  Equiv := Equivalence

/-- Equivalence of finite increasing arithmetic progressions is decidable by
walking both underlying progressions in lockstep. -/
instance (p q : FiniteArithmeticIncreasing) : Decidable (p ≈ q) :=
  Sequences.Progression.decidableEquivalenceOfFinite
    (toProgression p) (toProgression q)
    (toProgression_finite p) (toProgression_finite q)

/-- Elements from a known start for the given remaining length, advancing by the
common difference with no limit comparisons. -/
def getElementsFrom (first commonDifference : Peano) :
    Peano → Sequences.List Peano
  | .zero => .empty
  | .successor n =>
    .firstElement first
      (getElementsFrom (first + commonDifference) commonDifference n)

/-- The ordered list of all elements of a finite increasing arithmetic
progression. Empty when there is no in-range first element. Uses
`(toProgression p).first` and `getLength`, then advances by repeated addition
of the common difference — avoiding a limit comparison at every step. -/
def getElements (p : FiniteArithmeticIncreasing) : Sequences.List Peano :=
  match (toProgression p).first with
  | none => .empty
  | some first =>
    getElementsFrom first p.commonDifference (getLength p)

/-- If `rest` continues an arithmetic progression after `prev` with common
difference `diff`, return the last element of that progression (which is `prev`
when `rest` is empty). Returns `none` when a consecutive pair does not advance
by exactly `diff`. -/
def tryLastOfArithmeticContinuation (prev diff : Peano) :
    Sequences.List Peano → Option Peano
  | .empty => some prev
  | .firstElement x xs =>
    match trySubtract x prev with
    | none => none
    | some d =>
      if d = diff then
        tryLastOfArithmeticContinuation x diff xs
      else
        none

/-- Reconstruct a finite increasing arithmetic progression from the ordered list
of all its elements. Requires a proof that at least two elements are given.
Returns `none` when the list is not strictly ascending with a constant positive
common difference.

Uses the first element, the common difference between consecutive terms, and
the last element as the limit. -/
def tryFromElements :
    (elements : Sequences.List Peano) →
    two ≤ elements.length →
    Option FiniteArithmeticIncreasing
  | .empty, hge =>
    False.elim (not_two_le_zero (by
      change two ≤ zero
      exact hge))
  | .firstElement _ .empty, hge =>
    False.elim (not_two_le_one (by
      change two ≤ one
      exact hge))
  | .firstElement x (.firstElement y ys), _ =>
    match trySubtract y x with
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
            commonDifference := diff
            limit := last
            commonDifference_ne_zero := hdiff
          }

/-- Last element of a non-empty arithmetic walk of length `n`, starting at
`first` with common difference `commonDifference`. For `n = zero` the value is
unused (`first`). -/
def lastElementFrom (first commonDifference : Peano) : Peano → Peano
  | .zero => first
  | .successor n =>
    match n with
    | .zero => first
    | .successor _ =>
      lastElementFrom (first + commonDifference) commonDifference n

theorem lastElementFrom_one (first commonDifference : Peano) :
    lastElementFrom first commonDifference one = first :=
  rfl

theorem lastElementFrom_succ_succ (first commonDifference : Peano) (n : Peano) :
    lastElementFrom first commonDifference (successor (successor n)) =
      lastElementFrom (first + commonDifference) commonDifference (successor n) :=
  rfl

theorem first_lt_lastElementFrom_of_ge_two (first commonDifference : Peano)
    (hdiff : commonDifference ≠ zero) (n : Peano) :
    first <
      lastElementFrom first commonDifference (successor (successor n)) := by
  induction n generalizing first with
  | zero =>
    change first < first + commonDifference
    exact lt_add_of_right_ne_zero first commonDifference hdiff
  | successor n ih =>
    rw [lastElementFrom_succ_succ]
    exact lt_trans (lt_add_of_right_ne_zero first commonDifference hdiff)
      (ih (first + commonDifference))

theorem first_le_lastElementFrom_of_pos (first commonDifference : Peano)
    (hdiff : commonDifference ≠ zero) (n : Peano) (hne : n ≠ zero) :
    first ≤ lastElementFrom first commonDifference n := by
  cases n with
  | zero => exact (hne rfl).elim
  | successor m =>
    cases m with
    | zero => exact Or.inr rfl
    | successor k =>
      exact Or.inl (first_lt_lastElementFrom_of_ge_two first commonDifference hdiff k)

/-- Continuing an arithmetic walk from `prev` by `getElementsFrom` recovers the
last element of that walk. -/
theorem tryLastOfArithmeticContinuation_getElementsFrom
    (prev commonDifference : Peano) (n : Peano) :
    tryLastOfArithmeticContinuation prev commonDifference
        (getElementsFrom (prev + commonDifference) commonDifference n) =
      some (lastElementFrom prev commonDifference n.successor) := by
  induction n generalizing prev with
  | zero =>
    rfl
  | successor n ih =>
    simp only [getElementsFrom, tryLastOfArithmeticContinuation,
      trySubtract_self_add, ↓reduceIte]
    have ih' := ih (prev + commonDifference)
    rw [ih']
    cases n <;> rfl

theorem getElementsFrom_succ_succ (first commonDifference : Peano) (n : Peano) :
    getElementsFrom first commonDifference (successor (successor n)) =
      .firstElement first
        (.firstElement (first + commonDifference)
          (getElementsFrom (first + commonDifference + commonDifference)
            commonDifference n)) :=
  rfl

/-- `getElementsFrom` produces a list whose length equals the length argument. -/
theorem getElementsFrom_length (first commonDifference : Peano) (n : Peano) :
    (getElementsFrom first commonDifference n).length = n := by
  induction n generalizing first with
  | zero => rfl
  | successor n ih =>
    change
      (getElementsFrom (first + commonDifference) commonDifference n).length +
          one =
        n.successor
    rw [ih, add_one]

theorem getElementsFrom_ge_two_length (first commonDifference : Peano)
    (n : Peano) :
    two ≤
      (getElementsFrom first commonDifference
        (successor (successor n))).length := by
  rw [getElementsFrom_length]
  change two ≤ successor (successor n)
  simpa only [two, one] using
    (succ_le_succ (succ_le_succ (zero_le n)))

/-- Reconstructing from `getElementsFrom` of length at least two recovers the
start, common difference, and last element. -/
theorem tryFromElements_getElementsFrom_ge_two (first commonDifference : Peano)
    (hdiff : commonDifference ≠ zero) (n : Peano)
    (hge : two ≤
        (getElementsFrom first commonDifference
          (successor (successor n))).length :=
      getElementsFrom_ge_two_length first commonDifference n) :
    tryFromElements
        (getElementsFrom first commonDifference
          (successor (successor n)))
        hge =
      some ({
        first := some first
        commonDifference := commonDifference
        limit :=
          lastElementFrom first commonDifference (successor (successor n))
        commonDifference_ne_zero := hdiff
      } : FiniteArithmeticIncreasing) := by
  simp only [getElementsFrom, tryFromElements, trySubtract_self_add]
  split
  · next heq => exact (hdiff heq).elim
  · next _hne =>
    have hlast :=
      tryLastOfArithmeticContinuation_getElementsFrom
        (first + commonDifference) commonDifference n
    simp only [hlast]
    rfl

theorem lengthFromGap_self (diff : Peano) (hdiff : diff ≠ zero) :
    lengthFromGap diff hdiff (some diff) = successor one := by
  unfold lengthFromGap
  have hdiv :=
    divideWithRemainder_eq_of_mul diff diff hdiff one (multiply_one diff).symm
  simp only [hdiv]

theorem getLength_eq_lengthFromGap_of_lt (first commonDifference limit : Peano)
    (hdiff : commonDifference ≠ zero) (hlt : first < limit) :
    getLength {
      first := some first
      commonDifference := commonDifference
      limit := limit
      commonDifference_ne_zero := hdiff
    } =
      lengthFromGap commonDifference hdiff
        (some (subtract limit first (Or.inl hlt))) := by
  simp only [getLength]
  match hc : compare first limit with
  | .greater hgt => exact (not_le_of_gt hgt (Or.inl hlt)).elim
  | .equal heq =>
    rw [heq] at hlt
    exact (not_lt_self limit hlt).elim
  | .less hlt' =>
    exact congrArg (fun g => lengthFromGap commonDifference hdiff (some g))
      (subtract_eq_of_eq (Or.inl hlt') (Or.inl hlt) rfl rfl)

theorem commonDifference_lt_gap_of_add_lt (first commonDifference limit : Peano)
    (hlt : first < limit) (hlt_add : first + commonDifference < limit) :
    commonDifference < subtract limit first (Or.inl hlt) := by
  have hsum : subtract limit first (Or.inl hlt) + first = limit :=
    subtract_add_cancel limit first (Or.inl hlt)
  have : commonDifference + first <
      subtract limit first (Or.inl hlt) + first := by
    rw [add_commutative commonDifference, hsum]
    exact hlt_add
  exact add_lt_cancel_right this

/-- Length of a progression whose limit is exactly `lastElementFrom` of its
positive length. -/
theorem getLength_lastElementFrom (first commonDifference : Peano)
    (hdiff : commonDifference ≠ zero) (n : Peano) (hne : n ≠ zero) :
    getLength {
      first := some first
      commonDifference := commonDifference
      limit := lastElementFrom first commonDifference n
      commonDifference_ne_zero := hdiff
    } = n := by
  revert hne
  induction n generalizing first with
  | zero =>
    intro hne
    exact (hne rfl).elim
  | successor n ih =>
    intro _hne
    cases n with
    | zero =>
      change
          getLength {
            first := some first
            commonDifference := commonDifference
            limit := first
            commonDifference_ne_zero := hdiff
          } =
            one
      simp only [getLength]
      match hc : compare first first with
      | .greater hgt => exact (not_lt_self first hgt).elim
      | .equal _ => rfl
      | .less hlt => exact (not_lt_self first hlt).elim
    | successor m =>
      cases m with
      | zero =>
        have hlt : first < first + commonDifference :=
          lt_add_of_right_ne_zero first commonDifference hdiff
        have hget :=
          getLength_eq_lengthFromGap_of_lt first commonDifference
            (first + commonDifference) hdiff hlt
        have hgap :
            subtract (first + commonDifference) first (Or.inl hlt) =
              commonDifference := by
          have hgap' := subtract_add_left first commonDifference
          exact subtract_eq_of_eq (Or.inl hlt) (le_add_self_left first
            commonDifference) rfl rfl ▸ hgap'
        change
            getLength {
              first := some first
              commonDifference := commonDifference
              limit := first + commonDifference
              commonDifference_ne_zero := hdiff
            } =
              successor one
        rw [hget, hgap, lengthFromGap_self]
      | successor k =>
        have hlt : first <
            lastElementFrom first commonDifference
              (successor (successor k.successor)) :=
          first_lt_lastElementFrom_of_ge_two first commonDifference hdiff
            k.successor
        have hget :=
          getLength_eq_lengthFromGap_of_lt first commonDifference
            (lastElementFrom first commonDifference
              (successor (successor k.successor)))
            hdiff hlt
        have hlast_eq :
            lastElementFrom first commonDifference
                (successor (successor k.successor)) =
              lastElementFrom (first + commonDifference) commonDifference
                (successor k.successor) :=
          lastElementFrom_succ_succ first commonDifference k.successor
        have hlen' :
            getLength {
              first := some (first + commonDifference)
              commonDifference := commonDifference
              limit :=
                lastElementFrom (first + commonDifference) commonDifference
                  (successor k.successor)
              commonDifference_ne_zero := hdiff
            } =
              successor k.successor :=
          ih (first + commonDifference) (successor_ne_zero k.successor)
        have hlt_add : first + commonDifference <
            lastElementFrom first commonDifference
              (successor (successor k.successor)) := by
          have := first_lt_lastElementFrom_of_ge_two
            (first + commonDifference) commonDifference hdiff k
          rwa [← hlast_eq] at this
        have hdiff_lt :=
          commonDifference_lt_gap_of_add_lt first commonDifference
            (lastElementFrom first commonDifference
              (successor (successor k.successor)))
            hlt hlt_add
        have hgap_succ :=
          lengthFromGap_succ_of_lt commonDifference hdiff
            (subtract
              (lastElementFrom first commonDifference
                (successor (successor k.successor)))
              first (Or.inl hlt))
            hdiff_lt
        have hsub_eq :
            subtract
                (subtract
                  (lastElementFrom first commonDifference
                    (successor (successor k.successor)))
                  first (Or.inl hlt))
                commonDifference (Or.inl hdiff_lt) =
              subtract
                (lastElementFrom first commonDifference
                  (successor (successor k.successor)))
                (first + commonDifference) (Or.inl hlt_add) :=
          (subtract_limit_add_commonDifference
            {
              first := some first
              commonDifference := commonDifference
              limit :=
                lastElementFrom first commonDifference
                  (successor (successor k.successor))
              commonDifference_ne_zero := hdiff
            }
            first hlt hdiff_lt hlt_add).symm
        have hlt_shift : first + commonDifference <
            lastElementFrom (first + commonDifference) commonDifference
              (successor k.successor) := by
          have := hlt_add
          rwa [hlast_eq] at this
        have hget' :=
          getLength_eq_lengthFromGap_of_lt (first + commonDifference)
            commonDifference
            (lastElementFrom (first + commonDifference) commonDifference
              (successor k.successor))
            hdiff hlt_shift
        change
            getLength {
              first := some first
              commonDifference := commonDifference
              limit :=
                lastElementFrom first commonDifference
                  (successor (successor k.successor))
              commonDifference_ne_zero := hdiff
            } =
              successor (successor (successor k))
        rw [hget, hgap_succ]
        have htail :
            lengthFromGap commonDifference hdiff
                (some
                  (subtract
                    (subtract
                      (lastElementFrom first commonDifference
                        (successor (successor k.successor)))
                      first (Or.inl hlt))
                    commonDifference (Or.inl hdiff_lt))) =
              getLength {
                first := some (first + commonDifference)
                commonDifference := commonDifference
                limit :=
                  lastElementFrom (first + commonDifference) commonDifference
                    (successor k.successor)
                commonDifference_ne_zero := hdiff
              } := by
          rw [hget', hsub_eq]
          apply congrArg (lengthFromGap commonDifference hdiff)
          apply congrArg some
          exact subtract_eq_of_eq (Or.inl hlt_add) (Or.inl hlt_shift) hlast_eq
            rfl
        rw [htail, hlen']

theorem toProgression_first_lastElementFrom (first commonDifference : Peano)
    (hdiff : commonDifference ≠ zero) (n : Peano) (hne : n ≠ zero) :
    (toProgression {
      first := some first
      commonDifference := commonDifference
      limit := lastElementFrom first commonDifference n
      commonDifference_ne_zero := hdiff
    }).first = some first := by
  simp only [toProgression]
  have hle := first_le_lastElementFrom_of_pos first commonDifference hdiff n hne
  simp only [hle, ↓reduceIte]

/-- In-range `tryGetElement` matches `getElementFrom` on the progression first. -/
theorem tryGetElement_eq_some_getElementFrom_of_le (p : FiniteArithmeticIncreasing)
    (first : Peano) (hf : (toProgression p).first = some first)
    (index : OrdinalNatural.Peano)
    (hle : fromOrdinal index ≤ getLength p) :
    Sequences.Progression.tryGetElement index (toProgression p) =
      some (getElementFrom first p.commonDifference index) := by
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
theorem tryGetElement_eq_none_of_length_lt (p : FiniteArithmeticIncreasing)
    (index : OrdinalNatural.Peano)
    (hlt : getLength p < fromOrdinal index) :
    Sequences.Progression.tryGetElement index (toProgression p) = none := by
  have hlt' :
      Sequences.Progression.getLength (toProgression p) (toProgression_finite p) <
        fromOrdinal index :=
    getLength_eq p ▸ hlt
  exact Sequences.Progression.tryGetElement_eq_none_of_getLength_lt
    (toProgression p) (toProgression_finite p) index hlt'

theorem toProgression_first_eq_some_of_pos_length (p : FiniteArithmeticIncreasing)
    (h : getLength p ≠ zero) :
    ∃ first, (toProgression p).first = some first := by
  cases hf : (toProgression p).first with
  | none =>
    exact False.elim (h (getLength_eq_zero_of_toProgression_first_none p hf))
  | some first =>
    exact ⟨first, rfl⟩

/-- Progressions with the same first element, common difference, and length are
equivalent. -/
theorem equivalence_of_same_params (p q : FiniteArithmeticIncreasing) (first : Peano)
    (hp : (toProgression p).first = some first)
    (hq : (toProgression q).first = some first)
    (hdiff : p.commonDifference = q.commonDifference)
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

/-- `tryFromElements` recovers a progression equivalent to `p` from
`getElements p` when `p` has length at least two. -/
theorem tryFromElements_getElements (p : FiniteArithmeticIncreasing)
    (hge : two ≤ getLength p) :
    ∃ (hLen : two ≤ (getElements p).length)
      (q : FiniteArithmeticIncreasing),
      tryFromElements (getElements p) hLen = some q ∧ p ≈ q := by
  obtain ⟨m, hlen⟩ := eq_succ_succ_of_two_le (getLength p) hge
  have hne0 : getLength p ≠ zero := by
    intro heq
    rw [heq] at hge
    exact not_two_le_zero hge
  obtain ⟨first, hf⟩ := toProgression_first_eq_some_of_pos_length p hne0
  have hget :
      getElements p =
        getElementsFrom first p.commonDifference (getLength p) := by
    simp only [getElements, hf]
  have hLen : two ≤ (getElements p).length := by
    rw [hget, getElementsFrom_length]
    exact hge
  let last :=
    lastElementFrom first p.commonDifference (successor (successor m))
  let q : FiniteArithmeticIncreasing :=
    {
      first := some first
      commonDifference := p.commonDifference
      limit := last
      commonDifference_ne_zero := p.commonDifference_ne_zero
    }
  refine ⟨hLen, q, ?_⟩
  constructor
  · have htry :=
      tryFromElements_getElementsFrom_ge_two first p.commonDifference
        p.commonDifference_ne_zero m
        (getElementsFrom_ge_two_length first p.commonDifference m)
    have hget' :
        getElements p =
          getElementsFrom first p.commonDifference
            (successor (successor m)) := by
      rw [hget, hlen]
    revert hLen
    rw [hget']
    intro hLen
    exact htry
  · have hfq :=
      toProgression_first_lastElementFrom first p.commonDifference
        p.commonDifference_ne_zero (successor (successor m))
        (successor_ne_zero _)
    have hlenq :=
      getLength_lastElementFrom first p.commonDifference
        p.commonDifference_ne_zero (successor (successor m))
        (successor_ne_zero _)
    exact equivalence_of_same_params p q first hf hfq rfl
      (by rw [hlen, hlenq])

theorem list_length_firstElement {α : Type _} (x : α) (xs : Sequences.List α) :
    (Sequences.List.firstElement x xs).length = xs.length.successor :=
  add_one xs.length

/-- If a list continues arithmetically after `prev`, it equals the corresponding
`getElementsFrom` walk, and the recovered last element matches
`lastElementFrom`. -/
theorem eq_getElementsFrom_of_tryLastOfArithmeticContinuation
    (prev diff : Peano) (rest : Sequences.List Peano) (last : Peano)
    (h : tryLastOfArithmeticContinuation prev diff rest = some last) :
    rest =
        getElementsFrom (prev + diff) diff rest.length ∧
      last =
        lastElementFrom prev diff rest.length.successor := by
  induction rest generalizing prev last with
  | empty =>
    simp only [tryLastOfArithmeticContinuation] at h
    injection h with heq
    constructor
    · rfl
    · exact heq.symm
  | firstElement x xs ih =>
    simp only [tryLastOfArithmeticContinuation] at h
    match hs : trySubtract x prev with
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
        obtain ⟨hxs, hlast⟩ := ih x last h
        have hx : x = prev + diff := by
          have := eq_of_trySubtract_add prev x d hs
          rwa [hd] at this
        have hlen := list_length_firstElement x xs
        constructor
        · have htail :
              xs = getElementsFrom (prev + diff + diff) diff xs.length :=
            hxs.trans (by rw [hx])
          have h1 :
              Sequences.List.firstElement x xs =
                Sequences.List.firstElement (prev + diff)
                  (getElementsFrom (prev + diff + diff) diff xs.length) := by
            rw [hx]
            exact congrArg (Sequences.List.firstElement (prev + diff)) htail
          have h2 :
              getElementsFrom (prev + diff) diff
                  (Sequences.List.firstElement x xs).length =
                Sequences.List.firstElement (prev + diff)
                  (getElementsFrom (prev + diff + diff) diff xs.length) := by
            rw [hlen]
            rfl
          exact h1.trans h2.symm
        · have h1 :
              last = lastElementFrom (prev + diff) diff xs.length.successor := by
            rw [hlast, hx]
          have h2 :
              lastElementFrom (prev + diff) diff xs.length.successor =
                lastElementFrom prev diff (xs.length.successor.successor) := by
            cases xs.length with
            | zero => rfl
            | successor _ => rfl
          have h3 :
              lastElementFrom prev diff (xs.length.successor.successor) =
                lastElementFrom prev diff
                  (Sequences.List.firstElement x xs).length.successor := by
            rw [hlen]
          exact h1.trans (h2.trans h3)
      · simp only [hd, ↓reduceIte] at h
        nomatch h

/-- `getElements` recovers the original list from a successful
`tryFromElements`. -/
theorem getElements_tryFromElements (elements : Sequences.List Peano)
    (hge : two ≤ elements.length)
    (p : FiniteArithmeticIncreasing)
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
    match hs : trySubtract y x with
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
          obtain ⟨hrest, hlast⟩ :=
            eq_getElementsFrom_of_tryLastOfArithmeticContinuation x diff
              (Sequences.List.firstElement y ys) last hcont
          have hne :
              (Sequences.List.firstElement y ys).length.successor ≠ zero :=
            successor_ne_zero _
          have hle : x ≤ last := by
            have :=
              first_le_lastElementFrom_of_pos x diff hdiff0
                (Sequences.List.firstElement y ys).length.successor hne
            rwa [← hlast] at this
          have hf : (toProgression
              {
                first := some x
                commonDifference := diff
                limit := last
                commonDifference_ne_zero := hdiff0
              }).first = some x := by
            simp only [toProgression, hle, ↓reduceIte]
          have hlenp :
              getLength
                  {
                    first := some x
                    commonDifference := diff
                    limit := last
                    commonDifference_ne_zero := hdiff0
                  } =
                (Sequences.List.firstElement y ys).length.successor := by
            rw [hlast]
            exact getLength_lastElementFrom x diff hdiff0
              (Sequences.List.firstElement y ys).length.successor hne
          simp only [getElements, hf, hlenp]
          calc
            getElementsFrom x diff
                (Sequences.List.firstElement y ys).length.successor
                = Sequences.List.firstElement x
                    (getElementsFrom (x + diff) diff
                      (Sequences.List.firstElement y ys).length) :=
                  rfl
            _ = Sequences.List.firstElement x
                  (Sequences.List.firstElement y ys) := by
                  rw [← hrest]

/-- Recover the first element of an arithmetic progression from an element at the
given ordinal index and the common difference. At index `one` the element is
itself the first; otherwise subtract
`(fromOrdinal (predecessor index)) * commonDifference`. Returns `none` when
that subtraction is impossible in the Peano numbers. -/
def tryFirstFromIndexedElement
    (index : OrdinalNatural.Peano) (element commonDifference : Peano) :
    Option Peano :=
  match index with
  | .one => some element
  | .successor n => trySubtract element (fromOrdinal n * commonDifference)

/-- Given two ordered indexed elements (`index < index'`) of a prospective
increasing arithmetic progression, recover the common difference
`(element' - element) / (index' - index)`. Returns `none` when the elements are
not strictly ascending or the element gap is not divisible by the index gap. -/
def tryCommonDifferenceFromOrderedIndexedElements
    (index : OrdinalNatural.Peano) (element : Peano)
    (index' : OrdinalNatural.Peano) (element' : Peano)
    (hlt : index < index') :
    Option Peano :=
  match trySubtract element' element with
  | none => none
  | some elementDiff =>
    tryDivide elementDiff
      (fromOrdinal (OrdinalNatural.Peano.subtract index' index hlt))

/-- Reconstruct a finite increasing arithmetic progression from two of its
elements at different ordinal indexes together with the progression length.
Returns `none` when either index exceeds the length, when the recovered common
difference is zero, or when the values are not consistent with a strictly
increasing arithmetic progression of that length.

The reconstructed progression uses the recovered first element and common
difference, and takes the last element of an arithmetic walk of the given
length as the limit. -/
def tryFromTwoElementsAndLength
    (index1 : OrdinalNatural.Peano) (element1 : Peano)
    (index2 : OrdinalNatural.Peano) (element2 : Peano)
    (length : Peano)
    (hne : index1 ≠ index2) :
    Option FiniteArithmeticIncreasing :=
  if fromOrdinal index1 ≤ length then
    if fromOrdinal index2 ≤ length then
      match OrdinalNatural.Peano.compare index1 index2 with
      | .equal heq => False.elim (hne heq)
      | .less hlt =>
        match tryCommonDifferenceFromOrderedIndexedElements
            index1 element1 index2 element2 hlt with
        | none => none
        | some diff =>
          if hdiff : diff = zero then
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
          if hdiff : diff = zero then
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

theorem getElementFrom_one (first commonDifference : Peano) :
    getElementFrom first commonDifference OrdinalNatural.Peano.one = first :=
  rfl

/-- The closed form of `getElementFrom` at a successor index. -/
theorem getElementFrom_eq_add_mul (first commonDifference : Peano)
    (n : OrdinalNatural.Peano) :
    getElementFrom first commonDifference n.successor =
      first + fromOrdinal n * commonDifference := by
  induction n with
  | one =>
    change first + commonDifference = first + one * commonDifference
    rw [one_multiply]
  | successor n ih =>
    calc
      getElementFrom first commonDifference
            (OrdinalNatural.Peano.successor n).successor
          = getElementFrom first commonDifference
              (OrdinalNatural.Peano.successor n) + commonDifference :=
            rfl
      _ = first + fromOrdinal n * commonDifference + commonDifference := by
            rw [ih]
      _ = first + (fromOrdinal n * commonDifference + commonDifference) := by
            rw [add_associative]
      _ = first + (fromOrdinal n).successor * commonDifference := by
            rw [successor_multiply]
      _ = first + fromOrdinal n.successor * commonDifference :=
            rfl

/-- Recovering the first element from an indexed element is left-inverse to
`getElementFrom` at that index. -/
theorem getElementFrom_of_tryFirstFromIndexedElement
    (index : OrdinalNatural.Peano) (element commonDifference first : Peano)
    (h : tryFirstFromIndexedElement index element commonDifference = some first) :
    getElementFrom first commonDifference index = element := by
  match index with
  | .one =>
    simp only [tryFirstFromIndexedElement] at h
    injection h with heq
    rw [getElementFrom_one, heq]
  | .successor n =>
    simp only [tryFirstFromIndexedElement] at h
    have helement : element = fromOrdinal n * commonDifference + first :=
      eq_of_trySubtract_add (fromOrdinal n * commonDifference) element first h
    rw [getElementFrom_eq_add_mul, add_commutative, helement]

/-- Advancing from `index` to a larger `index'` adds
`(fromOrdinal (index' - index)) * commonDifference` to the element. -/
theorem getElementFrom_add_mul_of_lt (first commonDifference : Peano)
    (index index' : OrdinalNatural.Peano)
    (hlt : index < index') :
    getElementFrom first commonDifference index' =
      getElementFrom first commonDifference index +
        (fromOrdinal (OrdinalNatural.Peano.subtract index' index hlt)) *
          commonDifference := by
  match index, index' with
  | .one, .one =>
    exact (OrdinalNatural.Peano.not_lt_self OrdinalNatural.Peano.one hlt).elim
  | .one, .successor n =>
    have hsub :
        OrdinalNatural.Peano.subtract n.successor OrdinalNatural.Peano.one hlt =
          n :=
      OrdinalNatural.Peano.subtract_succ_one n hlt
    change getElementFrom first commonDifference n.successor =
      first +
        (fromOrdinal
          (OrdinalNatural.Peano.subtract n.successor OrdinalNatural.Peano.one
            hlt)) *
          commonDifference
    rw [getElementFrom_eq_add_mul, hsub]
  | .successor m, .one =>
    exact (OrdinalNatural.Peano.not_lt_one m.successor hlt).elim
  | .successor m, .successor n =>
    have hlt' : m < n := OrdinalNatural.Peano.lt_of_succ_lt_succ hlt
    have hsub :
        OrdinalNatural.Peano.subtract n.successor m.successor hlt =
          OrdinalNatural.Peano.subtract n m hlt' := by
      change
          OrdinalNatural.Peano.subtract n m
              (OrdinalNatural.Peano.lt_of_succ_lt_succ hlt) =
            OrdinalNatural.Peano.subtract n m hlt'
      exact OrdinalNatural.Peano.subtract_eq_of_eq _ _ rfl rfl
    rw [getElementFrom_eq_add_mul, getElementFrom_eq_add_mul, hsub]
    have hsum : m + OrdinalNatural.Peano.subtract n m hlt' = n := by
      rw [OrdinalNatural.Peano.add_comm]
      exact OrdinalNatural.Peano.subtract_add_cancel n m hlt'
    have hfrom :
        fromOrdinal n =
          fromOrdinal m +
            fromOrdinal (OrdinalNatural.Peano.subtract n m hlt') := by
      rw [← fromOrdinal_add, hsum]
    calc
      first + fromOrdinal n * commonDifference
          = first +
              (fromOrdinal m +
                fromOrdinal (OrdinalNatural.Peano.subtract n m hlt')) *
                commonDifference := by
            rw [hfrom]
      _ = first +
            (fromOrdinal m * commonDifference +
              fromOrdinal (OrdinalNatural.Peano.subtract n m hlt') *
                commonDifference) := by
            rw [multiply_distributive_over_add_left]
      _ = first + fromOrdinal m * commonDifference +
            fromOrdinal (OrdinalNatural.Peano.subtract n m hlt') *
              commonDifference := by
            rw [← add_associative]

/-- A successful common-difference recovery implies the larger element equals
the smaller plus the index gap times that difference. -/
theorem eq_add_mul_of_tryCommonDifferenceFromOrderedIndexedElements
    (index : OrdinalNatural.Peano) (element : Peano)
    (index' : OrdinalNatural.Peano) (element' : Peano)
    (hlt : index < index')
    (diff : Peano)
    (h : tryCommonDifferenceFromOrderedIndexedElements
        index element index' element' hlt = some diff) :
    element' =
      element +
        (fromOrdinal (OrdinalNatural.Peano.subtract index' index hlt)) *
          diff := by
  simp only [tryCommonDifferenceFromOrderedIndexedElements] at h
  match hs : trySubtract element' element with
  | none =>
    simp only [hs] at h
    nomatch h
  | some elementDiff =>
    simp only [hs] at h
    have hmul :
        (fromOrdinal (OrdinalNatural.Peano.subtract index' index hlt)) * diff =
          elementDiff :=
      eq_of_tryDivide_mul h
    have hadd : element' = element + elementDiff :=
      eq_of_trySubtract_add element element' elementDiff hs
    rw [hadd, hmul]

/-- When both indexed recoveries succeed, `getElementFrom` returns each original
element. -/
theorem getElementFrom_of_tryFirst_tryCommonDifference
    (index : OrdinalNatural.Peano) (element : Peano)
    (index' : OrdinalNatural.Peano) (element' : Peano)
    (hlt : index < index')
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
    eq_add_mul_of_tryCommonDifferenceFromOrderedIndexedElements
      index element index' element' hlt diff hdiff
  rw [getElementFrom_add_mul_of_lt first diff index index' hlt, h1, hgap]

/-- `getElement` on a progression whose limit is `lastElementFrom` of positive
length agrees with `getElementFrom`. -/
theorem getElement_lastElementFrom (first commonDifference : Peano)
    (hdiff : commonDifference ≠ zero) (n : Peano) (hne : n ≠ zero)
    (index : OrdinalNatural.Peano)
    (hle : fromOrdinal index ≤
      getLength {
        first := some first
        commonDifference := commonDifference
        limit := lastElementFrom first commonDifference n
        commonDifference_ne_zero := hdiff
      }) :
    getElement
      {
        first := some first
        commonDifference := commonDifference
        limit := lastElementFrom first commonDifference n
        commonDifference_ne_zero := hdiff
      }
      index hle =
      getElementFrom first commonDifference index := by
  have hfirst :
      (toProgression
        {
          first := some first
          commonDifference := commonDifference
          limit := lastElementFrom first commonDifference n
          commonDifference_ne_zero := hdiff
        }).first =
        some first :=
    toProgression_first_lastElementFrom first commonDifference hdiff n hne
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
    (index1 : OrdinalNatural.Peano) (element1 : Peano)
    (index2 : OrdinalNatural.Peano) (element2 : Peano)
    (length : Peano)
    (hne : index1 ≠ index2)
    (p : FiniteArithmeticIncreasing)
    (h : tryFromTwoElementsAndLength index1 element1 index2 element2 length hne =
      some p) :
    length ≠ zero := by
  intro hzero
  simp only [tryFromTwoElementsAndLength] at h
  by_cases hle1 : fromOrdinal index1 ≤ length
  · have : fromOrdinal index1 ≤ zero := hzero ▸ hle1
    exact fromOrdinal_ne_zero index1 (eq_zero_of_le_zero _ this)
  · simp only [hle1, ↓reduceIte] at h
    nomatch h

/-- A successful `tryFromTwoElementsAndLength` yields a progression whose
`getLength` is the given length and whose `getElement` at each of the two
indexes recovers the corresponding original element. -/
theorem getLength_getElement_of_tryFromTwoElementsAndLength
    (index1 : OrdinalNatural.Peano) (element1 : Peano)
    (index2 : OrdinalNatural.Peano) (element2 : Peano)
    (length : Peano)
    (hne : index1 ≠ index2)
    (p : FiniteArithmeticIncreasing)
    (h : tryFromTwoElementsAndLength index1 element1 index2 element2 length hne =
      some p) :
    getLength p = length ∧
      (∃ (hle1 : fromOrdinal index1 ≤ getLength p),
        getElement p index1 hle1 = element1) ∧
      (∃ (hle2 : fromOrdinal index2 ≤ getLength p),
        getElement p index2 hle2 = element2) := by
  have hlen_ne :=
    length_ne_zero_of_tryFromTwoElementsAndLength
      index1 element1 index2 element2 length hne p h
  simp only [tryFromTwoElementsAndLength] at h
  by_cases hle1 : fromOrdinal index1 ≤ length
  · simp only [hle1, ↓reduceIte] at h
    by_cases hle2 : fromOrdinal index2 ≤ length
    · simp only [hle2, ↓reduceIte] at h
      match hc : OrdinalNatural.Peano.compare index1 index2 with
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
          by_cases hdiff0 : diff = zero
          · simp only [hdiff0, ↓reduceDIte] at h
            nomatch h
          · simp only [hdiff0, ↓reduceDIte] at h
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
              have hlenp :=
                getLength_lastElementFrom first diff hdiff0 length hlen_ne
              have hle1p :
                  fromOrdinal index1 ≤
                    getLength {
                      first := some first
                      commonDifference := diff
                      limit := lastElementFrom first diff length
                      commonDifference_ne_zero := hdiff0
                    } := by
                rwa [hlenp]
              have hle2p :
                  fromOrdinal index2 ≤
                    getLength {
                      first := some first
                      commonDifference := diff
                      limit := lastElementFrom first diff length
                      commonDifference_ne_zero := hdiff0
                    } := by
                rwa [hlenp]
              refine ⟨hlenp, ⟨hle1p, ?_⟩, ⟨hle2p, ?_⟩⟩
              · exact
                  (getElement_lastElementFrom first diff hdiff0 length hlen_ne
                    index1 hle1p).trans hget.1
              · exact
                  (getElement_lastElementFrom first diff hdiff0 length hlen_ne
                    index2 hle2p).trans hget.2
      | .greater hgt =>
        simp only [hc] at h
        match hd : tryCommonDifferenceFromOrderedIndexedElements
            index2 element2 index1 element1 hgt with
        | none =>
          simp only [hd] at h
          nomatch h
        | some diff =>
          simp only [hd] at h
          by_cases hdiff0 : diff = zero
          · simp only [hdiff0, ↓reduceDIte] at h
            nomatch h
          · simp only [hdiff0, ↓reduceDIte] at h
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
              have hlenp :=
                getLength_lastElementFrom first diff hdiff0 length hlen_ne
              have hle1p :
                  fromOrdinal index1 ≤
                    getLength {
                      first := some first
                      commonDifference := diff
                      limit := lastElementFrom first diff length
                      commonDifference_ne_zero := hdiff0
                    } := by
                rwa [hlenp]
              have hle2p :
                  fromOrdinal index2 ≤
                    getLength {
                      first := some first
                      commonDifference := diff
                      limit := lastElementFrom first diff length
                      commonDifference_ne_zero := hdiff0
                    } := by
                rwa [hlenp]
              refine ⟨hlenp, ⟨hle1p, ?_⟩, ⟨hle2p, ?_⟩⟩
              · exact
                  (getElement_lastElementFrom first diff hdiff0 length hlen_ne
                    index1 hle1p).trans hget.2
              · exact
                  (getElement_lastElementFrom first diff hdiff0 length hlen_ne
                    index2 hle2p).trans hget.1
    · simp only [hle2, ↓reduceIte] at h
      nomatch h
  · simp only [hle1, ↓reduceIte] at h
    nomatch h

end FiniteArithmeticIncreasing

end ZeroMath.Numbers.CardinalNatural.Peano.Progressions
