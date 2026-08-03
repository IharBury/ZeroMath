import ZeroMath.Numbers.CardinalNatural.Peano
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
            simp only [lengthFromGap, hnil', hdiv, one]
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

end FiniteArithmeticIncreasing

end ZeroMath.Numbers.CardinalNatural.Peano.Progressions
