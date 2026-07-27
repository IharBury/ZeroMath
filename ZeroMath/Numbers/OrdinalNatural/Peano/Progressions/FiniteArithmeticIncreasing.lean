import ZeroMath.Numbers.OrdinalNatural.Peano
import ZeroMath.Sequences.Progression

namespace ZeroMath.Numbers.OrdinalNatural.Peano.Progressions

/-- A finite increasing arithmetic progression of Peano numbers with positive
common difference, defined by an optional first element (`none` for the empty
progression), the common difference, and a limit such that no element is
greater than the limit. The progression is also empty when the first element
is greater than the limit. Because every Peano number is at least one, the
common difference is always positive. -/
structure FiniteArithmeticIncreasing where
  first : Option Peano
  commonDifference : Peano
  limit : Peano

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
theorem tryGetElement_le_limit (p : FiniteArithmeticIncreasing) (index x : Peano)
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

/-- If `tryGetElement` returns a value, that value is at least the index
(identifying the shared Peano type), because the progression is strictly
increasing with positive common difference. -/
theorem le_of_tryGetElement_eq_some (p : FiniteArithmeticIncreasing)
    (index x : Peano)
    (h : Sequences.Progression.tryGetElement index (toProgression p) = some x) :
    index ≤ x := by
  induction index generalizing x with
  | one =>
    exact one_le' x
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
        have hn : n ≤ y := ih y hm
        have hsucc : successor n ≤ successor y := succ_le_succ hn
        have hy_le : successor y ≤ y + p.commonDifference := by
          rw [← add_one]
          exact le_add_of_le_right y (one_le' p.commonDifference)
        exact le_trans hsucc (heq ▸ hy_le)
      · simp only [hle, ↓reduceIte] at hnext
        nomatch hnext

/-- The progression obtained from a finite increasing arithmetic progression is
finite: `tryGetElement` at `successor limit` is always `none`, since any
returned value would have to be both ≥ `successor limit` and ≤ `limit`. -/
theorem toProgression_finite (p : FiniteArithmeticIncreasing) :
    Sequences.Progression.Finite (toProgression p) := by
  refine ⟨successor p.limit, ?_⟩
  cases h : Sequences.Progression.tryGetElement (successor p.limit) (toProgression p) with
  | none =>
    rfl
  | some x =>
    have hle_lim := tryGetElement_le_limit p (successor p.limit) x h
    have hle_idx := le_of_tryGetElement_eq_some p (successor p.limit) x h
    exact (not_succ_le p.limit (le_trans hle_idx hle_lim)).elim

/-- Length remaining from an element already known to lie in the progression,
given the room above that element up to the limit (`none` when the element
equals the limit). Computed with one division by the common difference instead
of comparing each successive term to the limit. -/
def lengthFromGap (diff : Peano) : Option Peano → CardinalNatural.Peano
  | none => CardinalNatural.Peano.one
  | some gap =>
    match divideWithRemainder gap diff with
    | (none, _) => CardinalNatural.Peano.one
    | (some q, _) => CardinalNatural.Peano.fromOrdinal (successor q)

/-- The length of a finite increasing arithmetic progression: the number of
elements before `tryGetElement` first returns `none`. Uses a single comparison
of the first element to the limit and one division, avoiding a comparison at
every step of the progression. -/
def getLength (p : FiniteArithmeticIncreasing) : CardinalNatural.Peano :=
  match p.first with
  | none => CardinalNatural.Peano.zero
  | some first =>
    match compare first p.limit with
    | .greater _ => CardinalNatural.Peano.zero
    | .equal _ => CardinalNatural.Peano.one
    | .less hlt =>
      lengthFromGap p.commonDifference (some (subtract p.limit first hlt))

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

theorem next_eq_none_of_add_not_le (p : FiniteArithmeticIncreasing) (x : Peano)
    (h : ¬ x + p.commonDifference ≤ p.limit) :
    (toProgression p).next x = none := by
  change (if x + p.commonDifference ≤ p.limit then some (x + p.commonDifference) else none) = none
  simp only [h, ↓reduceIte]

theorem next_eq_some_of_add_le (p : FiniteArithmeticIncreasing) (x : Peano)
    (h : x + p.commonDifference ≤ p.limit) :
    (toProgression p).next x = some (x + p.commonDifference) := by
  change (if x + p.commonDifference ≤ p.limit then some (x + p.commonDifference) else none) =
    some (x + p.commonDifference)
  simp only [h, ↓reduceIte]

theorem le_iff_add_le_of_lt_limit (p : FiniteArithmeticIncreasing) (x : Peano)
    (hlt : x < p.limit) :
    p.commonDifference ≤ subtract p.limit x hlt ↔
      x + p.commonDifference ≤ p.limit := by
  have hsum : subtract p.limit x hlt + x = p.limit :=
    subtract_add_cancel p.limit x hlt
  have hsum' : x + subtract p.limit x hlt = p.limit := by
    rw [add_comm, hsum]
  constructor
  · intro hd
    have := le_add_of_le_right x hd
    rwa [← hsum']
  · intro hxd
    have hrew : p.commonDifference + x ≤ subtract p.limit x hlt + x := by
      rw [add_comm p.commonDifference, hsum]
      exact hxd
    cases hrew with
    | inl hlt' => exact Or.inl (lt_of_add_lt_add_right hlt')
    | inr heq => exact Or.inr (add_cancel_right _ _ x heq)

theorem add_commonDifference_lt_limit_of_lt_gap (p : FiniteArithmeticIncreasing)
    (x : Peano) (hlt : x < p.limit)
    (hdiff : p.commonDifference < subtract p.limit x hlt) :
    x + p.commonDifference < p.limit := by
  have hsum : subtract p.limit x hlt + x = p.limit :=
    subtract_add_cancel p.limit x hlt
  have : p.commonDifference + x < subtract p.limit x hlt + x :=
    add_lt_add_right x hdiff
  rwa [add_comm p.commonDifference, hsum] at this

theorem subtract_limit_add_commonDifference (p : FiniteArithmeticIncreasing)
    (x : Peano) (hlt : x < p.limit)
    (hdiff : p.commonDifference < subtract p.limit x hlt)
    (hlt' : x + p.commonDifference < p.limit) :
    subtract p.limit (x + p.commonDifference) hlt' =
      subtract (subtract p.limit x hlt) p.commonDifference hdiff := by
  have hsum : subtract p.limit x hlt + x = p.limit :=
    subtract_add_cancel p.limit x hlt
  apply add_cancel_right _ _ (x + p.commonDifference)
  have h1 := subtract_add_cancel p.limit (x + p.commonDifference) hlt'
  have h2 :=
    subtract_add_cancel (subtract p.limit x hlt) p.commonDifference hdiff
  rw [h1, add_comm x, ← add_assoc, h2, hsum]

/-- Gap above `x` up to `limit`, or `none` when `x = limit`. -/
def gapToLimit (x limit : Peano) (hx : x ≤ limit) : Option Peano :=
  match compare x limit with
  | .greater hgt => (not_le_of_gt hgt hx).elim
  | .equal _ => none
  | .less hlt => some (subtract limit x hlt)

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
    gapToLimit x limit hx = some (subtract limit x hlt) := by
  unfold gapToLimit
  match hc : compare x limit with
  | .greater hgt => exact (not_le_of_gt hgt hx).elim
  | .equal heq =>
    rw [heq] at hlt
    exact (not_lt_self limit hlt).elim
  | .less hlt' =>
    exact congrArg some (subtract_eq_of_eq hlt' hlt rfl rfl)

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
theorem getLengthFrom_eq_lengthFromGap (p : FiniteArithmeticIncreasing)
    (current : Option Peano)
    (hAcc : Acc (Sequences.Progression.OptionStep (toProgression p).next) current) :
    (current = none →
      Sequences.Progression.getLengthFrom (toProgression p).next current hAcc =
        CardinalNatural.Peano.zero) ∧
    (∀ x, current = some x → ∀ hx : x ≤ p.limit,
      Sequences.Progression.getLengthFrom (toProgression p).next current hAcc =
        lengthFromGap p.commonDifference (gapToLimit x p.limit hx)) := by
  refine Acc.rec
    (motive := fun current hAcc =>
      (current = none →
        Sequences.Progression.getLengthFrom (toProgression p).next current hAcc =
          CardinalNatural.Peano.zero) ∧
      (∀ x, current = some x → ∀ hx : x ≤ p.limit,
        Sequences.Progression.getLengthFrom (toProgression p).next current hAcc =
          lengthFromGap p.commonDifference (gapToLimit x p.limit hx)))
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
        | .greater hgt => exact (not_le_of_gt hgt hx).elim
        | .equal heq =>
          have hnext : (toProgression p).next x = none := by
            apply next_eq_none_of_add_not_le
            intro hle
            have hlt : x < x + p.commonDifference := lt_add_left x p.commonDifference
            have : x < p.limit := lt_of_lt_le hlt hle
            rw [heq] at this
            exact not_lt_self p.limit this
          have hgap := gapToLimit_equal hx heq
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
        | .less hlt =>
          have hgap := gapToLimit_less hx hlt
          rw [hgap]
          match hd : compare p.commonDifference (subtract p.limit x hlt) with
          | .greater hgt =>
            have hnot : ¬ x + p.commonDifference ≤ p.limit := by
              intro hle
              exact not_le_of_gt hgt ((le_iff_add_le_of_lt_limit p x hlt).mpr hle)
            have hnext := next_eq_none_of_add_not_le p x hnot
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
                (subtract p.limit x hlt) p.commonDifference
                (subtract p.limit x hlt) hgt rfl
            simp only [lengthFromGap, hnil', hdiv, CardinalNatural.Peano.one]
          | .equal heq =>
            have hle_diff : p.commonDifference ≤ subtract p.limit x hlt := Or.inr heq
            have hle_add := (le_iff_add_le_of_lt_limit p x hlt).mp hle_diff
            have hnext := next_eq_some_of_add_le p x hle_add
            have hsum : subtract p.limit x hlt + x = p.limit :=
              subtract_add_cancel p.limit x hlt
            have hx_next : x + p.commonDifference = p.limit := by
              rw [← hsum, ← heq, add_comm]
            have hx_le' : x + p.commonDifference ≤ p.limit := Or.inr hx_next
            have hstep : Sequences.Progression.OptionStep (toProgression p).next
                (some (x + p.commonDifference)) (some x) :=
              hnext ▸ Sequences.Progression.OptionStep.step x
            have ih' := (ih _ hstep).2 (x + p.commonDifference) rfl hx_le'
            have hgap' := gapToLimit_equal hx_le' hx_next
            have hdiv :=
              divideWithRemainder_eq_of_some_none
                (subtract p.limit x hlt) p.commonDifference one (by
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
            have hlt' := add_commonDifference_lt_limit_of_lt_gap p x hlt hdiff
            have hsub := subtract_limit_add_commonDifference p x hlt hdiff hlt'
            have hle_diff : p.commonDifference ≤ subtract p.limit x hlt := Or.inl hdiff
            have hle_add := (le_iff_add_le_of_lt_limit p x hlt).mp hle_diff
            have hnext := next_eq_some_of_add_le p x hle_add
            have hx_le' : x + p.commonDifference ≤ p.limit := Or.inl hlt'
            have hstep : Sequences.Progression.OptionStep (toProgression p).next
                (some (x + p.commonDifference)) (some x) :=
              hnext ▸ Sequences.Progression.OptionStep.step x
            have ih' := (ih _ hstep).2 (x + p.commonDifference) rfl hx_le'
            have hgap' := gapToLimit_less hx_le' hlt'
            have hlen :=
              lengthFromGap_succ_of_lt p.commonDifference
                (subtract p.limit x hlt) hdiff
            have hnext_len :
                Sequences.Progression.getLengthFrom (toProgression p).next
                  ((toProgression p).next x)
                  (hAccx.inv (Sequences.Progression.OptionStep.step x)) =
                  lengthFromGap p.commonDifference
                    (some (subtract (subtract p.limit x hlt) p.commonDifference
                      hdiff)) := by
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
      Sequences.Progression.getLengthFrom (toProgression p).next (toProgression p).first
        (Sequences.Progression.acc_first_of_finite (toProgression p) (toProgression_finite p))
    simp only [getLength, hf, hfirst, Sequences.Progression.getLengthFrom_none]
  | some first =>
    cases hc : compare first p.limit with
    | greater hgt =>
      have hnot : ¬ first ≤ p.limit := not_le_of_gt hgt
      have hfirst : (toProgression p).first = none := by
        simp only [toProgression, hf, hnot, ↓reduceIte]
      change getLength p =
        Sequences.Progression.getLengthFrom (toProgression p).next (toProgression p).first
          (Sequences.Progression.acc_first_of_finite (toProgression p) (toProgression_finite p))
      simp only [getLength, hf, hc, hfirst, Sequences.Progression.getLengthFrom_none]
    | equal heq =>
      have hle : first ≤ p.limit := Or.inr heq
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
        simpa [gapToLimit_equal hle heq, lengthFromGap] using hx
      exact hwalk.symm
    | less hlt =>
      have hle : first ≤ p.limit := Or.inl hlt
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
            lengthFromGap p.commonDifference (some (subtract p.limit first hlt)) := by
        rw [getLengthFrom_eq_of_current_eq _ hfirst hAcc]
        rw [getLengthFrom_eq_of_acc_eq _ _ _ hAcc']
        simpa [gapToLimit_less hle hlt] using hx
      exact hwalk.symm

/-- Element at a positive ordinal index starting from a known first value,
advancing by the common difference with no limit comparisons. -/
def getElementFrom (first commonDifference : Peano) : Peano → Peano
  | .one => first
  | .successor n => getElementFrom first commonDifference n + commonDifference

/-- Shifting the start by one common difference decreases the index by one. -/
theorem getElementFrom_succ (first commonDifference : Peano) (n : Peano) :
    getElementFrom first commonDifference n.successor =
      getElementFrom (first + commonDifference) commonDifference n := by
  induction n with
  | one =>
    rfl
  | successor n ih =>
    calc
      getElementFrom first commonDifference (successor n).successor
          = getElementFrom first commonDifference (successor n) + commonDifference :=
            rfl
      _ = getElementFrom (first + commonDifference) commonDifference n +
            commonDifference := by rw [ih]
      _ = getElementFrom (first + commonDifference) commonDifference
            (successor n) := rfl

/-- If `toProgression` has no first element, the length is zero. -/
theorem getLength_eq_zero_of_toProgression_first_none
    (p : FiniteArithmeticIncreasing)
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
    (p : FiniteArithmeticIncreasing) (index : Peano)
    (hle : CardinalNatural.Peano.fromOrdinal index ≤ getLength p)
    (h : (toProgression p).first = none) : False := by
  have hlen := getLength_eq_zero_of_toProgression_first_none p h
  have hle' : CardinalNatural.Peano.fromOrdinal index ≤ CardinalNatural.Peano.zero :=
    hlen ▸ hle
  exact CardinalNatural.Peano.fromOrdinal_ne_zero index
    (CardinalNatural.Peano.eq_zero_of_le_zero _ hle')

/-- A successor index within the remaining length forces a next term equal to
the current element plus the common difference. -/
theorem next_eq_some_of_succ_le_getLengthFrom (p : FiniteArithmeticIncreasing)
    (x : Peano) (n : Peano)
    (hAcc : Acc (Sequences.Progression.OptionStep (toProgression p).next) (some x))
    (hle : CardinalNatural.Peano.fromOrdinal n.successor ≤
      Sequences.Progression.getLengthFrom (toProgression p).next (some x) hAcc) :
    (toProgression p).next x = some (x + p.commonDifference) ∧
      x + p.commonDifference ≤ p.limit := by
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
`getElementFrom` (additions only, no further limit comparisons). -/
theorem getElementFrom_eq_progression (p : FiniteArithmeticIncreasing)
    (x : Peano)
    (hAcc : Acc (Sequences.Progression.OptionStep (toProgression p).next) (some x))
    (index : Peano)
    (hle : CardinalNatural.Peano.fromOrdinal index ≤
      Sequences.Progression.getLengthFrom (toProgression p).next (some x) hAcc) :
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
        Acc (Sequences.Progression.OptionStep (toProgression p).next)
          (some (x + p.commonDifference)) :=
      hnext ▸ hAcc.inv (Sequences.Progression.OptionStep.step x)
    have hle_next :
        CardinalNatural.Peano.fromOrdinal n ≤
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
def getElement (p : FiniteArithmeticIncreasing) (index : Peano)
    (hle : CardinalNatural.Peano.fromOrdinal index ≤ getLength p) : Peano :=
  match hf : (toProgression p).first with
  | none =>
    (not_fromOrdinal_le_getLength_of_first_none p index hle hf).elim
  | some first =>
    getElementFrom first p.commonDifference index

/-- `getElement` agrees with walking `toProgression` via `Progression.getElement`. -/
theorem getElement_eq (p : FiniteArithmeticIncreasing) (index : Peano)
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

end FiniteArithmeticIncreasing

end ZeroMath.Numbers.OrdinalNatural.Peano.Progressions
