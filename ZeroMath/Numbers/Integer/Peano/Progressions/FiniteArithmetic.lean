import ZeroMath.Numbers.Integer.Peano
import ZeroMath.Sequences.Progression

namespace ZeroMath.Numbers.Integer.Peano.Progressions

/-- A finite arithmetic progression of integer Peano numbers with nonzero common
difference, defined by an optional first element (`none` for the empty
progression), the common difference, and a limit such that no element lies past
the limit in the direction of travel. When the common difference is positive the
progression is strictly increasing and no element exceeds the limit; when it is
negative the progression is strictly decreasing and no element is less than the
limit. The progression is also empty when the first element already lies past
the limit. -/
structure FiniteArithmetic where
  first : Option Peano
  commonDifference : Peano
  limit : Peano
  commonDifference_ne_zero : commonDifference ≠ zero

namespace FiniteArithmetic

/-- Include `x` when it does not lie past `limit` for the given common
difference: at most the limit when the difference is positive, at least the
limit when it is negative. Returns `none` for a zero difference. -/
def tryInclude (commonDifference limit x : Peano) : Option Peano :=
  match commonDifference with
  | positive _ => if x ≤ limit then some x else none
  | negative _ => if limit ≤ x then some x else none
  | zero => none

/-- Convert a finite arithmetic progression to a general progression by taking
the same optional first element when it does not lie past the limit (otherwise
the empty progression) and advancing by the common difference while the next
element does not lie past the limit. -/
def toProgression (p : FiniteArithmetic) : Sequences.Progression Peano where
  first :=
    match p.first with
    | none => none
    | some x => tryInclude p.commonDifference p.limit x
  next := fun x =>
    tryInclude p.commonDifference p.limit (x + p.commonDifference)

/-- If `tryInclude` returns a value, that value is the candidate element. -/
theorem eq_of_tryInclude_eq_some (commonDifference limit x y : Peano)
    (h : tryInclude commonDifference limit x = some y) : y = x := by
  match commonDifference with
  | positive _ =>
    simp only [tryInclude] at h
    by_cases hle : x ≤ limit
    · simp only [hle, ↓reduceIte] at h
      injection h with heq
      exact heq.symm
    · simp only [hle, ↓reduceIte] at h
      nomatch h
  | negative _ =>
    simp only [tryInclude] at h
    by_cases hle : limit ≤ x
    · simp only [hle, ↓reduceIte] at h
      injection h with heq
      exact heq.symm
    · simp only [hle, ↓reduceIte] at h
      nomatch h
  | zero =>
    simp only [tryInclude] at h
    nomatch h

/-- When `tryInclude` succeeds on `x`, it returns `some x`. -/
theorem tryInclude_eq_some_self (commonDifference limit x y : Peano)
    (h : tryInclude commonDifference limit x = some y) :
    tryInclude commonDifference limit x = some x := by
  rw [eq_of_tryInclude_eq_some commonDifference limit x y h] at h
  exact h

/-- Distance from an included element to the limit along the direction of
travel, as a natural number. Used as a well-founded measure for finiteness. -/
def gapToLimit (commonDifference limit x : Peano) : Nat :=
  match commonDifference with
  | positive _ =>
    if x ≤ limit then absNat (limit - x) else 0
  | negative _ =>
    if limit ≤ x then absNat (x - limit) else 0
  | zero => 0

/-- Extract the inclusion side-condition from a successful positive `tryInclude`. -/
theorem le_of_tryInclude_positive_eq_some (limit x y : Peano) (n : OrdinalNatural.Peano)
    (h : tryInclude (positive n) limit x = some y) : x ≤ limit := by
  simp only [tryInclude] at h
  by_cases hle : x ≤ limit
  · exact hle
  · simp only [hle, ↓reduceIte] at h
    cases h

/-- Extract the inclusion side-condition from a successful negative `tryInclude`. -/
theorem le_of_tryInclude_negative_eq_some (limit x y : Peano) (n : OrdinalNatural.Peano)
    (h : tryInclude (negative n) limit x = some y) : limit ≤ x := by
  simp only [tryInclude] at h
  by_cases hle : limit ≤ x
  · exact hle
  · simp only [hle, ↓reduceIte] at h
    cases h

/-- Advancing by a nonzero common difference strictly decreases `gapToLimit`
when both the current and next elements are included. -/
theorem gapToLimit_lt_of_tryInclude_add (p : FiniteArithmetic) (x : Peano)
    (hx : tryInclude p.commonDifference p.limit x = some x)
    (hy : tryInclude p.commonDifference p.limit (x + p.commonDifference) =
      some (x + p.commonDifference)) :
    gapToLimit p.commonDifference p.limit (x + p.commonDifference) <
      gapToLimit p.commonDifference p.limit x := by
  cases hdiff : p.commonDifference with
  | zero =>
    exact False.elim (p.commonDifference_ne_zero hdiff)
  | positive n =>
    rw [hdiff] at hx hy
    have hle_x : x ≤ p.limit := le_of_tryInclude_positive_eq_some p.limit x x n hx
    have hle_y : x + positive n ≤ p.limit :=
      le_of_tryInclude_positive_eq_some p.limit (x + positive n) (x + positive n) n hy
    simp only [gapToLimit, hle_x, hle_y, ↓reduceIte]
    rw [← absNat_toInt (p.limit - (x + positive n)), ← absNat_toInt (p.limit - x)]
    rw [toInt_subtract, toInt_subtract, toInt_add]
    have hx_int : x.toInt ≤ p.limit.toInt := toInt_le_of_le hle_x
    have hy_int : x.toInt + (positive n).toInt ≤ p.limit.toInt := by
      have := toInt_le_of_le hle_y
      rw [toInt_add] at this
      exact this
    have hn_pos : 0 < (positive n).toInt := by
      simp only [toInt]
      exact Int.natCast_pos.mpr
        (Nat.pos_of_ne_zero (OrdinalNatural.Peano.toNat_ne_zero n))
    have hnonneg_old : 0 ≤ p.limit.toInt - x.toInt := by omega
    have hnonneg_new :
        0 ≤ p.limit.toInt - (x.toInt + (positive n).toInt) := by omega
    have hlt :
        p.limit.toInt - (x.toInt + (positive n).toInt) <
          p.limit.toInt - x.toInt := by omega
    have h1 :
        ((p.limit.toInt - (x.toInt + (positive n).toInt)).natAbs : Int) =
          p.limit.toInt - (x.toInt + (positive n).toInt) :=
      Int.natAbs_of_nonneg hnonneg_new
    have h2 :
        ((p.limit.toInt - x.toInt).natAbs : Int) = p.limit.toInt - x.toInt :=
      Int.natAbs_of_nonneg hnonneg_old
    have hlt_nat :
        ((p.limit.toInt - (x.toInt + (positive n).toInt)).natAbs : Int) <
          ((p.limit.toInt - x.toInt).natAbs : Int) := by
      rw [h1, h2]
      exact hlt
    exact Int.ofNat_lt.mp hlt_nat
  | negative n =>
    rw [hdiff] at hx hy
    have hle_x : p.limit ≤ x := le_of_tryInclude_negative_eq_some p.limit x x n hx
    have hle_y : p.limit ≤ x + negative n :=
      le_of_tryInclude_negative_eq_some p.limit (x + negative n) (x + negative n) n hy
    simp only [gapToLimit, hle_x, hle_y, ↓reduceIte]
    rw [← absNat_toInt (x + negative n - p.limit), ← absNat_toInt (x - p.limit)]
    rw [toInt_subtract, toInt_subtract, toInt_add]
    have hx_int : p.limit.toInt ≤ x.toInt := toInt_le_of_le hle_x
    have hy_int : p.limit.toInt ≤ x.toInt + (negative n).toInt := by
      have := toInt_le_of_le hle_y
      rw [toInt_add] at this
      exact this
    have hn_neg : (negative n).toInt < 0 := by
      simp only [toInt]
      exact Int.neg_neg_of_pos
        (Int.natCast_pos.mpr
          (Nat.pos_of_ne_zero (OrdinalNatural.Peano.toNat_ne_zero n)))
    have hnonneg_old : 0 ≤ x.toInt - p.limit.toInt := by omega
    have hnonneg_new :
        0 ≤ x.toInt + (negative n).toInt - p.limit.toInt := by omega
    have hlt :
        x.toInt + (negative n).toInt - p.limit.toInt <
          x.toInt - p.limit.toInt := by omega
    have h1 :
        ((x.toInt + (negative n).toInt - p.limit.toInt).natAbs : Int) =
          x.toInt + (negative n).toInt - p.limit.toInt :=
      Int.natAbs_of_nonneg hnonneg_new
    have h2 :
        ((x.toInt - p.limit.toInt).natAbs : Int) = x.toInt - p.limit.toInt :=
      Int.natAbs_of_nonneg hnonneg_old
    have hlt_nat :
        ((x.toInt + (negative n).toInt - p.limit.toInt).natAbs : Int) <
          ((x.toInt - p.limit.toInt).natAbs : Int) := by
      rw [h1, h2]
      exact hlt
    exact Int.ofNat_lt.mp hlt_nat

/-- Every included element is accessible under `next`, by strong induction on
`gapToLimit`. -/
theorem acc_some_of_tryInclude (p : FiniteArithmetic) (x : Peano)
    (hx : tryInclude p.commonDifference p.limit x = some x) :
    Acc (Sequences.Progression.OptionStep (toProgression p).next) (some x) := by
  let motive : Nat → Prop := fun n =>
    ∀ (y : Peano),
      tryInclude p.commonDifference p.limit y = some y →
        gapToLimit p.commonDifference p.limit y = n →
          Acc (Sequences.Progression.OptionStep (toProgression p).next) (some y)
  have hmotive : motive (gapToLimit p.commonDifference p.limit x) := by
    refine Nat.strongRecOn (gapToLimit p.commonDifference p.limit x)
      fun n ih => ?_
    intro y hy hgapy
    refine Acc.intro (some y) fun z hz => ?_
    cases hz with
    | step =>
      cases hnext :
          tryInclude p.commonDifference p.limit (y + p.commonDifference) with
      | none =>
        have : (toProgression p).next y = none := by
          simp only [toProgression, hnext]
        exact this ▸ Sequences.Progression.acc_none (toProgression p).next
      | some w =>
        have hw_eq : w = y + p.commonDifference :=
          eq_of_tryInclude_eq_some p.commonDifference p.limit
            (y + p.commonDifference) w hnext
        have hw : tryInclude p.commonDifference p.limit
            (y + p.commonDifference) = some (y + p.commonDifference) :=
          hw_eq ▸ hnext
        have hgap_lt :
            gapToLimit p.commonDifference p.limit (y + p.commonDifference) < n :=
          hgapy ▸ gapToLimit_lt_of_tryInclude_add p y hy hw
        have hAcc :=
          ih (gapToLimit p.commonDifference p.limit (y + p.commonDifference))
            hgap_lt (y + p.commonDifference) hw rfl
        have hnext' : (toProgression p).next y = some (y + p.commonDifference) := by
          simp only [toProgression, hw]
        exact hnext' ▸ hAcc
  exact hmotive x hx rfl

/-- The starting option of `toProgression` is accessible under `next`. -/
theorem acc_first (p : FiniteArithmetic) :
    Acc (Sequences.Progression.OptionStep (toProgression p).next)
      (toProgression p).first := by
  match hf : (toProgression p).first with
  | none =>
    exact hf ▸ Sequences.Progression.acc_none (toProgression p).next
  | some x =>
    have hx : tryInclude p.commonDifference p.limit x = some x := by
      match hp : p.first with
      | none =>
        have : (toProgression p).first = none := by
          simp only [toProgression, hp]
        rw [this] at hf
        nomatch hf
      | some y =>
        have hfirst :
            (toProgression p).first =
              tryInclude p.commonDifference p.limit y := by
          simp only [toProgression, hp]
        rw [hfirst] at hf
        have hy : y = x :=
          (eq_of_tryInclude_eq_some p.commonDifference p.limit y x hf).symm
        rw [← hy]
        exact tryInclude_eq_some_self p.commonDifference p.limit y x hf
    exact hf ▸ acc_some_of_tryInclude p x hx

/-- The progression obtained from a finite arithmetic progression is finite:
accessibility of the start (via the well-founded gap-to-limit measure) yields a
length, and `tryGetElement` past that length is `none`. -/
theorem toProgression_finite (p : FiniteArithmetic) :
    Sequences.Progression.Finite (toProgression p) := by
  have hAcc := acc_first p
  let n :=
    Sequences.Progression.getLengthFrom (toProgression p).next
      (toProgression p).first hAcc
  have hne : n.successor ≠ CardinalNatural.Peano.zero :=
    CardinalNatural.Peano.successor_ne_zero n
  refine ⟨CardinalNatural.Peano.toOrdinal n.successor hne, ?_⟩
  have hprog :
      toProgression p = ⟨(toProgression p).first, (toProgression p).next⟩ := rfl
  rw [hprog]
  exact Sequences.Progression.tryGetElement_eq_none_of_lengthFrom_lt
    (toProgression p).next (toProgression p).first hAcc
    (CardinalNatural.Peano.toOrdinal n.successor hne)
    (by
      rw [CardinalNatural.Peano.fromOrdinal_toOrdinal]
      exact CardinalNatural.Peano.lt_successor_of_le (Or.inr rfl))

/-- Length remaining from an element already known to lie in the progression,
given the ordinal gap to the limit in the direction of travel (`none` when the
element equals the limit). Computed with one division by the absolute common
difference instead of comparing each successive term to the limit. -/
def lengthFromGap (diff : OrdinalNatural.Peano) :
    Option OrdinalNatural.Peano → CardinalNatural.Peano
  | none => CardinalNatural.Peano.one
  | some gap =>
    match OrdinalNatural.Peano.divideWithRemainder gap diff with
    | (none, _) => CardinalNatural.Peano.one
    | (some q, _) => CardinalNatural.Peano.fromOrdinal (OrdinalNatural.Peano.successor q)

/-- The length of a finite arithmetic progression: the number of elements before
`tryGetElement` first returns `none`. Uses a single comparison of the first
element to the limit and one division by the absolute common difference,
avoiding a comparison at every step of the progression. -/
def getLength (p : FiniteArithmetic) : CardinalNatural.Peano :=
  match p.first with
  | none => CardinalNatural.Peano.zero
  | some first =>
    match hdiff : p.commonDifference with
    | positive d =>
      match compare first p.limit with
      | .greater _ => CardinalNatural.Peano.zero
      | .equal _ => CardinalNatural.Peano.one
      | .less hlt =>
        lengthFromGap d (some (ordinalDistance first p.limit hlt))
    | negative d =>
      match compare first p.limit with
      | .less _ => CardinalNatural.Peano.zero
      | .equal _ => CardinalNatural.Peano.one
      | .greater hgt =>
        lengthFromGap d (some (ordinalDistance p.limit first hgt))
    | zero =>
      (p.commonDifference_ne_zero hdiff).elim

/-- `lengthFromGap` on `gap` is the successor of `lengthFromGap` on `gap - diff`
when `diff < gap`. -/
theorem lengthFromGap_succ_of_lt (diff gap : OrdinalNatural.Peano)
    (hlt : diff < gap) :
    lengthFromGap diff (some gap) =
      (lengthFromGap diff
        (some (OrdinalNatural.Peano.subtract gap diff hlt))).successor := by
  have hsum : OrdinalNatural.Peano.subtract gap diff hlt + diff = gap :=
    OrdinalNatural.Peano.subtract_add_cancel gap diff hlt
  have hdiv :=
    OrdinalNatural.Peano.divideWithRemainder_add_right
      (OrdinalNatural.Peano.subtract gap diff hlt) diff
  rw [hsum] at hdiv
  unfold lengthFromGap
  match hrem : OrdinalNatural.Peano.divideWithRemainder
      (OrdinalNatural.Peano.subtract gap diff hlt) diff with
  | (none, r) =>
    simp only [hrem] at hdiv
    simp only [hrem, hdiv, CardinalNatural.Peano.fromOrdinal,
      CardinalNatural.Peano.one]
  | (some q, r) =>
    simp only [hrem] at hdiv
    simp only [hrem, hdiv, CardinalNatural.Peano.fromOrdinal]

/-- Gap above `x` up to `limit`, or `none` when `x = limit`. -/
def gapAboveToLimit (x limit : Peano) (hx : x ≤ limit) :
    Option OrdinalNatural.Peano :=
  match compare x limit with
  | .greater hgt => (not_le_of_gt hgt hx).elim
  | .equal _ => none
  | .less hlt => some (ordinalDistance x limit hlt)

theorem gapAboveToLimit_equal {x limit : Peano} (hx : x ≤ limit)
    (heq : x = limit) : gapAboveToLimit x limit hx = none := by
  unfold gapAboveToLimit
  match hc : compare x limit with
  | .greater hgt => exact (not_le_of_gt hgt hx).elim
  | .equal _ => rfl
  | .less hlt =>
    rw [heq] at hlt
    exact (not_lt_self limit hlt).elim

theorem gapAboveToLimit_less {x limit : Peano} (hx : x ≤ limit)
    (hlt : x < limit) :
    gapAboveToLimit x limit hx = some (ordinalDistance x limit hlt) := by
  unfold gapAboveToLimit
  match hc : compare x limit with
  | .greater hgt => exact (not_le_of_gt hgt hx).elim
  | .equal heq =>
    rw [heq] at hlt
    exact (not_lt_self limit hlt).elim
  | .less hlt' =>
    exact congrArg some
      (positive_injective
        ((ordinalDistance_sub hlt').symm.trans (ordinalDistance_sub hlt)))

/-- Gap below `x` down to `limit`, or `none` when `x = limit`. -/
def gapBelowFromLimit (limit x : Peano) (hx : limit ≤ x) :
    Option OrdinalNatural.Peano :=
  match compare x limit with
  | .less hlt => (not_le_of_gt hlt hx).elim
  | .equal _ => none
  | .greater hgt => some (ordinalDistance limit x hgt)

theorem gapBelowFromLimit_equal {limit x : Peano} (hx : limit ≤ x)
    (heq : x = limit) : gapBelowFromLimit limit x hx = none := by
  unfold gapBelowFromLimit
  match hc : compare x limit with
  | .less hlt => exact (not_le_of_gt hlt hx).elim
  | .equal _ => rfl
  | .greater hgt =>
    rw [heq] at hgt
    exact (not_lt_self limit hgt).elim

theorem gapBelowFromLimit_greater {limit x : Peano} (hx : limit ≤ x)
    (hlt : limit < x) :
    gapBelowFromLimit limit x hx = some (ordinalDistance limit x hlt) := by
  unfold gapBelowFromLimit
  match hc : compare x limit with
  | .less hlt' => exact (not_le_of_gt hlt' hx).elim
  | .equal heq =>
    rw [heq] at hlt
    exact (not_lt_self limit hlt).elim
  | .greater hgt =>
    exact congrArg some
      (positive_injective
        ((ordinalDistance_sub hgt).symm.trans (ordinalDistance_sub hlt)))

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

theorem next_eq_none_of_tryInclude_none (p : FiniteArithmetic) (x : Peano)
    (h : tryInclude p.commonDifference p.limit (x + p.commonDifference) = none) :
    (toProgression p).next x = none := by
  simp only [toProgression, h]

theorem next_eq_some_of_tryInclude_some (p : FiniteArithmetic) (x : Peano)
    (h : tryInclude p.commonDifference p.limit (x + p.commonDifference) =
      some (x + p.commonDifference)) :
    (toProgression p).next x = some (x + p.commonDifference) := by
  simp only [toProgression, h]

theorem next_eq_none_of_add_positive_not_le (p : FiniteArithmetic)
    (d : OrdinalNatural.Peano) (hdiff : p.commonDifference = positive d)
    (x : Peano) (h : ¬ x + positive d ≤ p.limit) :
    (toProgression p).next x = none := by
  have htry :
      tryInclude p.commonDifference p.limit (x + p.commonDifference) = none := by
    simp only [tryInclude, hdiff, h, ↓reduceIte]
  exact next_eq_none_of_tryInclude_none p x htry

theorem next_eq_some_of_add_positive_le (p : FiniteArithmetic)
    (d : OrdinalNatural.Peano) (hdiff : p.commonDifference = positive d)
    (x : Peano) (h : x + positive d ≤ p.limit) :
    (toProgression p).next x = some (x + positive d) := by
  have htry :
      tryInclude p.commonDifference p.limit (x + p.commonDifference) =
        some (x + p.commonDifference) := by
    simp only [tryInclude, hdiff, h, ↓reduceIte]
  have hnext := next_eq_some_of_tryInclude_some p x htry
  simpa [hdiff] using hnext

theorem next_eq_none_of_add_negative_not_ge (p : FiniteArithmetic)
    (d : OrdinalNatural.Peano) (hdiff : p.commonDifference = negative d)
    (x : Peano) (h : ¬ p.limit ≤ x + negative d) :
    (toProgression p).next x = none := by
  have htry :
      tryInclude p.commonDifference p.limit (x + p.commonDifference) = none := by
    simp only [tryInclude, hdiff, h, ↓reduceIte]
  exact next_eq_none_of_tryInclude_none p x htry

theorem next_eq_some_of_add_negative_ge (p : FiniteArithmetic)
    (d : OrdinalNatural.Peano) (hdiff : p.commonDifference = negative d)
    (x : Peano) (h : p.limit ≤ x + negative d) :
    (toProgression p).next x = some (x + negative d) := by
  have htry :
      tryInclude p.commonDifference p.limit (x + p.commonDifference) =
        some (x + p.commonDifference) := by
    simp only [tryInclude, hdiff, h, ↓reduceIte]
  have hnext := next_eq_some_of_tryInclude_some p x htry
  simpa [hdiff] using hnext

/-- Walking a positive-difference progression from an accessible state matches
`lengthFromGap` on in-range elements, and yields zero from `none`. -/
theorem getLengthFrom_eq_lengthFromGap_positive (p : FiniteArithmetic)
    (d : OrdinalNatural.Peano) (hdiff : p.commonDifference = positive d)
    (current : Option Peano)
    (hAcc : Acc (Sequences.Progression.OptionStep (toProgression p).next)
      current) :
    (current = none →
      Sequences.Progression.getLengthFrom (toProgression p).next current hAcc =
        CardinalNatural.Peano.zero) ∧
    (∀ x, current = some x → ∀ hx : x ≤ p.limit,
      Sequences.Progression.getLengthFrom (toProgression p).next current hAcc =
        lengthFromGap d (gapAboveToLimit x p.limit hx)) := by
  refine Acc.rec
    (motive := fun current hAcc =>
      (current = none →
        Sequences.Progression.getLengthFrom (toProgression p).next current hAcc =
          CardinalNatural.Peano.zero) ∧
      (∀ x, current = some x → ∀ hx : x ≤ p.limit,
        Sequences.Progression.getLengthFrom (toProgression p).next current hAcc =
          lengthFromGap d (gapAboveToLimit x p.limit hx)))
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
        rw [Sequences.Progression.getLengthFrom_some (toProgression p).next x
          hAccx]
        match hc : compare x p.limit with
        | .greater hgt => exact (not_le_of_gt hgt hx).elim
        | .equal heq =>
          have hnext : (toProgression p).next x = none := by
            apply next_eq_none_of_add_positive_not_le p d hdiff
            intro hle
            have hlt : x < x + positive d := lt_add_of_positive x d
            have : x < p.limit := lt_of_lt_of_le hlt hle
            rw [heq] at this
            exact not_lt_self p.limit this
          have hgap := gapAboveToLimit_equal hx heq
          have hnil :=
            (ih ((toProgression p).next x)
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
          have hgap := gapAboveToLimit_less hx hlt
          rw [hgap]
          match hd : OrdinalNatural.Peano.compare d
              (ordinalDistance x p.limit hlt) with
          | .greater hgt =>
            have hnot : ¬ x + positive d ≤ p.limit := by
              intro hle
              exact OrdinalNatural.Peano.not_le_of_gt hgt
                ((le_iff_add_positive_le d hlt).mpr hle)
            have hnext :=
              next_eq_none_of_add_positive_not_le p d hdiff x hnot
            have hnil :=
              (ih ((toProgression p).next x)
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
              OrdinalNatural.Peano.divideWithRemainder_eq_of_none_some
                (ordinalDistance x p.limit hlt) d
                (ordinalDistance x p.limit hlt) hgt rfl
            simp only [lengthFromGap, hnil', hdiv, CardinalNatural.Peano.one]
          | .equal heq =>
            have hle_diff : d ≤ ordinalDistance x p.limit hlt := Or.inr heq
            have hle_add := (le_iff_add_positive_le d hlt).mp hle_diff
            have hnext := next_eq_some_of_add_positive_le p d hdiff x hle_add
            have hx_next : x + positive d = p.limit := by
              have hgap_sub := ordinalDistance_sub hlt
              have hsum : (x + positive d) + (p.limit - (x + positive d)) =
                  p.limit := by
                rw [add_comm, sub_add_cancel]
              have hdiff_sub : p.limit - (x + positive d) =
                  (p.limit - x) - positive d :=
                sub_add_positive_eq_sub_sub_positive p.limit x d
              rw [hdiff_sub, hgap_sub, ← heq, sub_self, add_zero] at hsum
              exact hsum
            have hx_le' : x + positive d ≤ p.limit := Or.inr hx_next
            have hstep :
                Sequences.Progression.OptionStep (toProgression p).next
                  (some (x + positive d)) (some x) :=
              hnext ▸ Sequences.Progression.OptionStep.step x
            have ih' := (ih _ hstep).2 (x + positive d) rfl hx_le'
            have hgap' := gapAboveToLimit_equal hx_le' hx_next
            have hdiv :=
              OrdinalNatural.Peano.divideWithRemainder_eq_of_some_none
                (ordinalDistance x p.limit hlt) d OrdinalNatural.Peano.one (by
                  rw [← heq, OrdinalNatural.Peano.multiply_one])
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
          | .less hdiff_gap =>
            have hlt' :=
              add_positive_lt_of_lt_gap x p.limit d hlt hdiff_gap
            have hsub :=
              ordinalDistance_add_positive x p.limit d hlt hdiff_gap hlt'
            have hle_diff : d ≤ ordinalDistance x p.limit hlt :=
              Or.inl hdiff_gap
            have hle_add := (le_iff_add_positive_le d hlt).mp hle_diff
            have hnext := next_eq_some_of_add_positive_le p d hdiff x hle_add
            have hx_le' : x + positive d ≤ p.limit := Or.inl hlt'
            have hstep :
                Sequences.Progression.OptionStep (toProgression p).next
                  (some (x + positive d)) (some x) :=
              hnext ▸ Sequences.Progression.OptionStep.step x
            have ih' := (ih _ hstep).2 (x + positive d) rfl hx_le'
            have hgap' := gapAboveToLimit_less hx_le' hlt'
            have hlen :=
              lengthFromGap_succ_of_lt d (ordinalDistance x p.limit hlt)
                hdiff_gap
            have hnext_len :
                Sequences.Progression.getLengthFrom (toProgression p).next
                  ((toProgression p).next x)
                  (hAccx.inv (Sequences.Progression.OptionStep.step x)) =
                  lengthFromGap d
                    (some (OrdinalNatural.Peano.subtract
                      (ordinalDistance x p.limit hlt) d hdiff_gap)) := by
              have htmp := ih'
              simp only [hgap'] at htmp
              rw [getLengthFrom_eq_of_acc_eq _ _ _
                (hcurr _ (Sequences.Progression.OptionStep.step x))]
              simpa [hnext, hsub] using htmp
            simp only [hnext_len, hlen])
    hAcc

/-- Walking a negative-difference progression from an accessible state matches
`lengthFromGap` on in-range elements, and yields zero from `none`. -/
theorem getLengthFrom_eq_lengthFromGap_negative (p : FiniteArithmetic)
    (d : OrdinalNatural.Peano) (hdiff : p.commonDifference = negative d)
    (current : Option Peano)
    (hAcc : Acc (Sequences.Progression.OptionStep (toProgression p).next)
      current) :
    (current = none →
      Sequences.Progression.getLengthFrom (toProgression p).next current hAcc =
        CardinalNatural.Peano.zero) ∧
    (∀ x, current = some x → ∀ hx : p.limit ≤ x,
      Sequences.Progression.getLengthFrom (toProgression p).next current hAcc =
        lengthFromGap d (gapBelowFromLimit p.limit x hx)) := by
  refine Acc.rec
    (motive := fun current hAcc =>
      (current = none →
        Sequences.Progression.getLengthFrom (toProgression p).next current hAcc =
          CardinalNatural.Peano.zero) ∧
      (∀ x, current = some x → ∀ hx : p.limit ≤ x,
        Sequences.Progression.getLengthFrom (toProgression p).next current hAcc =
          lengthFromGap d (gapBelowFromLimit p.limit x hx)))
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
        rw [Sequences.Progression.getLengthFrom_some (toProgression p).next x
          hAccx]
        match hc : compare x p.limit with
        | .less hlt => exact (not_le_of_gt hlt hx).elim
        | .equal heq =>
          have hnext : (toProgression p).next x = none := by
            apply next_eq_none_of_add_negative_not_ge p d hdiff
            intro hle
            have hlt : x + negative d < x := add_negative_lt x d
            have : p.limit < p.limit := by
              have hmid := lt_of_le_of_lt hle hlt
              rwa [heq] at hmid
            exact not_lt_self p.limit this
          have hgap := gapBelowFromLimit_equal hx heq
          have hnil :=
            (ih ((toProgression p).next x)
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
          have hgap := gapBelowFromLimit_greater hx hgt
          rw [hgap]
          match hd : OrdinalNatural.Peano.compare d
              (ordinalDistance p.limit x hgt) with
          | .greater hgt' =>
            have hnot : ¬ p.limit ≤ x + negative d := by
              intro hle
              exact OrdinalNatural.Peano.not_le_of_gt hgt'
                ((le_iff_add_negative_ge d hgt).mpr hle)
            have hnext :=
              next_eq_none_of_add_negative_not_ge p d hdiff x hnot
            have hnil :=
              (ih ((toProgression p).next x)
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
              OrdinalNatural.Peano.divideWithRemainder_eq_of_none_some
                (ordinalDistance p.limit x hgt) d
                (ordinalDistance p.limit x hgt) hgt' rfl
            simp only [lengthFromGap, hnil', hdiv, CardinalNatural.Peano.one]
          | .equal heq =>
            have hle_diff : d ≤ ordinalDistance p.limit x hgt := Or.inr heq
            have hle_add := (le_iff_add_negative_ge d hgt).mp hle_diff
            have hnext := next_eq_some_of_add_negative_ge p d hdiff x hle_add
            have hx_next : x + negative d = p.limit := by
              have hgap_sub := ordinalDistance_sub hgt
              have hsum :
                  p.limit + (x + negative d - p.limit) = x + negative d := by
                rw [add_comm, sub_add_cancel]
              have hdiff_sub : x + negative d - p.limit =
                  (x - p.limit) - positive d :=
                sub_add_negative_eq_sub_sub_positive x p.limit d
              rw [hdiff_sub, hgap_sub, ← heq, sub_self, add_zero] at hsum
              exact hsum.symm
            have hx_le' : p.limit ≤ x + negative d := Or.inr hx_next.symm
            have hstep :
                Sequences.Progression.OptionStep (toProgression p).next
                  (some (x + negative d)) (some x) :=
              hnext ▸ Sequences.Progression.OptionStep.step x
            have ih' := (ih _ hstep).2 (x + negative d) rfl hx_le'
            have hgap' := gapBelowFromLimit_equal hx_le' hx_next
            have hdiv :=
              OrdinalNatural.Peano.divideWithRemainder_eq_of_some_none
                (ordinalDistance p.limit x hgt) d OrdinalNatural.Peano.one (by
                  rw [← heq, OrdinalNatural.Peano.multiply_one])
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
          | .less hdiff_gap =>
            have hlt' :=
              add_negative_gt_of_lt_gap x p.limit d hgt hdiff_gap
            have hsub :=
              ordinalDistance_add_negative x p.limit d hgt hdiff_gap hlt'
            have hle_diff : d ≤ ordinalDistance p.limit x hgt :=
              Or.inl hdiff_gap
            have hle_add := (le_iff_add_negative_ge d hgt).mp hle_diff
            have hnext := next_eq_some_of_add_negative_ge p d hdiff x hle_add
            have hx_le' : p.limit ≤ x + negative d := Or.inl hlt'
            have hstep :
                Sequences.Progression.OptionStep (toProgression p).next
                  (some (x + negative d)) (some x) :=
              hnext ▸ Sequences.Progression.OptionStep.step x
            have ih' := (ih _ hstep).2 (x + negative d) rfl hx_le'
            have hgap' := gapBelowFromLimit_greater hx_le' hlt'
            have hlen :=
              lengthFromGap_succ_of_lt d (ordinalDistance p.limit x hgt)
                hdiff_gap
            have hnext_len :
                Sequences.Progression.getLengthFrom (toProgression p).next
                  ((toProgression p).next x)
                  (hAccx.inv (Sequences.Progression.OptionStep.step x)) =
                  lengthFromGap d
                    (some (OrdinalNatural.Peano.subtract
                      (ordinalDistance p.limit x hgt) d hdiff_gap)) := by
              have htmp := ih'
              simp only [hgap'] at htmp
              rw [getLengthFrom_eq_of_acc_eq _ _ _
                (hcurr _ (Sequences.Progression.OptionStep.step x))]
              simpa [hnext, hsub] using htmp
            simp only [hnext_len, hlen])
    hAcc

theorem getLength_mk_none (commonDifference limit : Peano)
    (hne : commonDifference ≠ zero) :
    getLength ⟨none, commonDifference, limit, hne⟩ =
      CardinalNatural.Peano.zero :=
  rfl

theorem getLength_mk_positive_gt (first limit : Peano) (d : OrdinalNatural.Peano)
    (hne : (positive d : Peano) ≠ zero) {hgt : limit < first}
    (hc : compare first limit = .greater hgt) :
    getLength ⟨some first, positive d, limit, hne⟩ =
      CardinalNatural.Peano.zero := by
  simp only [getLength]
  rw [hc]

theorem getLength_mk_positive_eq (first limit : Peano) (d : OrdinalNatural.Peano)
    (hne : (positive d : Peano) ≠ zero) {heq : first = limit}
    (hc : compare first limit = .equal heq) :
    getLength ⟨some first, positive d, limit, hne⟩ =
      CardinalNatural.Peano.one := by
  simp only [getLength]
  rw [hc]

theorem getLength_mk_positive_lt (first limit : Peano) (d : OrdinalNatural.Peano)
    (hne : (positive d : Peano) ≠ zero) {hlt : first < limit}
    (hc : compare first limit = .less hlt) :
    getLength ⟨some first, positive d, limit, hne⟩ =
      lengthFromGap d (some (ordinalDistance first limit hlt)) := by
  simp only [getLength]
  rw [hc]

theorem getLength_mk_negative_lt (first limit : Peano) (d : OrdinalNatural.Peano)
    (hne : (negative d : Peano) ≠ zero) {hlt : first < limit}
    (hc : compare first limit = .less hlt) :
    getLength ⟨some first, negative d, limit, hne⟩ =
      CardinalNatural.Peano.zero := by
  simp only [getLength]
  rw [hc]

theorem getLength_mk_negative_eq (first limit : Peano) (d : OrdinalNatural.Peano)
    (hne : (negative d : Peano) ≠ zero) {heq : first = limit}
    (hc : compare first limit = .equal heq) :
    getLength ⟨some first, negative d, limit, hne⟩ =
      CardinalNatural.Peano.one := by
  simp only [getLength]
  rw [hc]

theorem getLength_mk_negative_gt (first limit : Peano) (d : OrdinalNatural.Peano)
    (hne : (negative d : Peano) ≠ zero) {hgt : limit < first}
    (hc : compare first limit = .greater hgt) :
    getLength ⟨some first, negative d, limit, hne⟩ =
      lengthFromGap d (some (ordinalDistance limit first hgt)) := by
  simp only [getLength]
  rw [hc]

/-- `getLength` agrees with walking `toProgression` via `Progression.getLength`. -/
theorem getLength_eq (p : FiniteArithmetic) :
    getLength p =
      Sequences.Progression.getLength (toProgression p)
        (toProgression_finite p) := by
  rcases p with ⟨first, commonDifference, limit, hne⟩
  cases first with
  | none =>
    change
      getLength ⟨none, commonDifference, limit, hne⟩ =
        Sequences.Progression.getLengthFrom
          (toProgression ⟨none, commonDifference, limit, hne⟩).next
          (toProgression ⟨none, commonDifference, limit, hne⟩).first
          (Sequences.Progression.acc_first_of_finite _
            (toProgression_finite _))
    rw [getLength_mk_none]
    have hfirst :
        (toProgression ⟨none, commonDifference, limit, hne⟩).first = none :=
      rfl
    simp only [hfirst, Sequences.Progression.getLengthFrom_none]
  | some first =>
    cases commonDifference with
    | zero =>
      exact (hne rfl).elim
    | positive d =>
      match hc : compare first limit with
      | .greater hgt =>
        have hnot : ¬ first ≤ limit := not_le_of_gt hgt
        have hfirst :
            (toProgression ⟨some first, positive d, limit, hne⟩).first =
              none := by
          change tryInclude (positive d) limit first = none
          simp only [tryInclude, hnot, ↓reduceIte]
        change
          getLength ⟨some first, positive d, limit, hne⟩ =
            Sequences.Progression.getLengthFrom
              (toProgression ⟨some first, positive d, limit, hne⟩).next
              (toProgression ⟨some first, positive d, limit, hne⟩).first
              (Sequences.Progression.acc_first_of_finite _
                (toProgression_finite _))
        rw [getLength_mk_positive_gt first limit d hne hc]
        simp only [hfirst, Sequences.Progression.getLengthFrom_none]
      | .equal heq =>
        have hle : first ≤ limit := Or.inr heq
        have hfirst :
            (toProgression ⟨some first, positive d, limit, hne⟩).first =
              some first := by
          change tryInclude (positive d) limit first = some first
          simp only [tryInclude, hle, ↓reduceIte]
        have hAcc :=
          Sequences.Progression.acc_first_of_finite
            (toProgression ⟨some first, positive d, limit, hne⟩)
            (toProgression_finite _)
        have hAcc' :
            Acc (Sequences.Progression.OptionStep
              (toProgression ⟨some first, positive d, limit, hne⟩).next)
              (some first) := hfirst ▸ hAcc
        have hx :=
          (getLengthFrom_eq_lengthFromGap_positive
            ⟨some first, positive d, limit, hne⟩ d rfl (some first)
            hAcc').2 first rfl hle
        have hgap := gapAboveToLimit_equal hle heq
        have hwalk :
            Sequences.Progression.getLengthFrom
              (toProgression ⟨some first, positive d, limit, hne⟩).next
              (toProgression ⟨some first, positive d, limit, hne⟩).first hAcc =
              CardinalNatural.Peano.one := by
          rw [getLengthFrom_eq_of_current_eq _ hfirst hAcc]
          rw [getLengthFrom_eq_of_acc_eq _ _ _ hAcc']
          have hx' := hx
          rw [hgap, lengthFromGap] at hx'
          exact hx'
        simp only [Sequences.Progression.getLength]
        exact (getLength_mk_positive_eq first limit d hne hc).trans hwalk.symm
      | .less hlt =>
        have hle : first ≤ limit := Or.inl hlt
        have hfirst :
            (toProgression ⟨some first, positive d, limit, hne⟩).first =
              some first := by
          change tryInclude (positive d) limit first = some first
          simp only [tryInclude, hle, ↓reduceIte]
        have hAcc :=
          Sequences.Progression.acc_first_of_finite
            (toProgression ⟨some first, positive d, limit, hne⟩)
            (toProgression_finite _)
        have hAcc' :
            Acc (Sequences.Progression.OptionStep
              (toProgression ⟨some first, positive d, limit, hne⟩).next)
              (some first) := hfirst ▸ hAcc
        have hx :=
          (getLengthFrom_eq_lengthFromGap_positive
            ⟨some first, positive d, limit, hne⟩ d rfl (some first)
            hAcc').2 first rfl hle
        have hgap := gapAboveToLimit_less hle hlt
        have hwalk :
            Sequences.Progression.getLengthFrom
              (toProgression ⟨some first, positive d, limit, hne⟩).next
              (toProgression ⟨some first, positive d, limit, hne⟩).first hAcc =
              lengthFromGap d
                (some (ordinalDistance first limit hlt)) := by
          rw [getLengthFrom_eq_of_current_eq _ hfirst hAcc]
          rw [getLengthFrom_eq_of_acc_eq _ _ _ hAcc']
          have hx' := hx
          rw [hgap] at hx'
          exact hx'
        simp only [Sequences.Progression.getLength]
        exact (getLength_mk_positive_lt first limit d hne hc).trans hwalk.symm
    | negative d =>
      match hc : compare first limit with
      | .less hlt =>
        have hnot : ¬ limit ≤ first := not_le_of_gt hlt
        have hfirst :
            (toProgression ⟨some first, negative d, limit, hne⟩).first =
              none := by
          change tryInclude (negative d) limit first = none
          simp only [tryInclude, hnot, ↓reduceIte]
        change
          getLength ⟨some first, negative d, limit, hne⟩ =
            Sequences.Progression.getLengthFrom
              (toProgression ⟨some first, negative d, limit, hne⟩).next
              (toProgression ⟨some first, negative d, limit, hne⟩).first
              (Sequences.Progression.acc_first_of_finite _
                (toProgression_finite _))
        rw [getLength_mk_negative_lt first limit d hne hc]
        simp only [hfirst, Sequences.Progression.getLengthFrom_none]
      | .equal heq =>
        have hle : limit ≤ first := Or.inr heq.symm
        have hfirst :
            (toProgression ⟨some first, negative d, limit, hne⟩).first =
              some first := by
          change tryInclude (negative d) limit first = some first
          simp only [tryInclude, hle, ↓reduceIte]
        have hAcc :=
          Sequences.Progression.acc_first_of_finite
            (toProgression ⟨some first, negative d, limit, hne⟩)
            (toProgression_finite _)
        have hAcc' :
            Acc (Sequences.Progression.OptionStep
              (toProgression ⟨some first, negative d, limit, hne⟩).next)
              (some first) := hfirst ▸ hAcc
        have hx :=
          (getLengthFrom_eq_lengthFromGap_negative
            ⟨some first, negative d, limit, hne⟩ d rfl (some first)
            hAcc').2 first rfl hle
        have hgap := gapBelowFromLimit_equal hle heq
        have hwalk :
            Sequences.Progression.getLengthFrom
              (toProgression ⟨some first, negative d, limit, hne⟩).next
              (toProgression ⟨some first, negative d, limit, hne⟩).first hAcc =
              CardinalNatural.Peano.one := by
          rw [getLengthFrom_eq_of_current_eq _ hfirst hAcc]
          rw [getLengthFrom_eq_of_acc_eq _ _ _ hAcc']
          have hx' := hx
          rw [hgap, lengthFromGap] at hx'
          exact hx'
        simp only [Sequences.Progression.getLength]
        exact (getLength_mk_negative_eq first limit d hne hc).trans hwalk.symm
      | .greater hgt =>
        have hle : limit ≤ first := Or.inl hgt
        have hfirst :
            (toProgression ⟨some first, negative d, limit, hne⟩).first =
              some first := by
          change tryInclude (negative d) limit first = some first
          simp only [tryInclude, hle, ↓reduceIte]
        have hAcc :=
          Sequences.Progression.acc_first_of_finite
            (toProgression ⟨some first, negative d, limit, hne⟩)
            (toProgression_finite _)
        have hAcc' :
            Acc (Sequences.Progression.OptionStep
              (toProgression ⟨some first, negative d, limit, hne⟩).next)
              (some first) := hfirst ▸ hAcc
        have hx :=
          (getLengthFrom_eq_lengthFromGap_negative
            ⟨some first, negative d, limit, hne⟩ d rfl (some first)
            hAcc').2 first rfl hle
        have hgap := gapBelowFromLimit_greater hle hgt
        have hwalk :
            Sequences.Progression.getLengthFrom
              (toProgression ⟨some first, negative d, limit, hne⟩).next
              (toProgression ⟨some first, negative d, limit, hne⟩).first hAcc =
              lengthFromGap d
                (some (ordinalDistance limit first hgt)) := by
          rw [getLengthFrom_eq_of_current_eq _ hfirst hAcc]
          rw [getLengthFrom_eq_of_acc_eq _ _ _ hAcc']
          have hx' := hx
          rw [hgap] at hx'
          exact hx'
        simp only [Sequences.Progression.getLength]
        exact (getLength_mk_negative_gt first limit d hne hc).trans hwalk.symm

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
    (p : FiniteArithmetic)
    (h : (toProgression p).first = none) :
    getLength p = CardinalNatural.Peano.zero := by
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
    (p : FiniteArithmetic) (index : OrdinalNatural.Peano)
    (hle : CardinalNatural.Peano.fromOrdinal index ≤ getLength p)
    (h : (toProgression p).first = none) : False := by
  have hlen := getLength_eq_zero_of_toProgression_first_none p h
  have hle' :
      CardinalNatural.Peano.fromOrdinal index ≤ CardinalNatural.Peano.zero :=
    hlen ▸ hle
  exact CardinalNatural.Peano.fromOrdinal_ne_zero index
    (CardinalNatural.Peano.eq_zero_of_le_zero _ hle')

/-- A successor index within the remaining length forces a next term equal to
the current element plus the common difference. -/
theorem next_eq_some_of_succ_le_getLengthFrom (p : FiniteArithmetic)
    (x : Peano) (n : OrdinalNatural.Peano)
    (hAcc : Acc (Sequences.Progression.OptionStep (toProgression p).next)
      (some x))
    (hle : CardinalNatural.Peano.fromOrdinal n.successor ≤
      Sequences.Progression.getLengthFrom (toProgression p).next (some x)
        hAcc) :
    (toProgression p).next x = some (x + p.commonDifference) := by
  have hlen :=
    Sequences.Progression.getLengthFrom_some (toProgression p).next x hAcc
  have hle' :
      CardinalNatural.Peano.successor
          (CardinalNatural.Peano.fromOrdinal n) ≤
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
      have hEq :=
        getLengthFrom_eq_of_current_eq (toProgression p).next hnext hAcc'
      rw [hEq, Sequences.Progression.getLengthFrom_none]
    have hle0 :
        CardinalNatural.Peano.fromOrdinal n ≤ CardinalNatural.Peano.zero := by
      rwa [hzero] at hle_n
    exact (CardinalNatural.Peano.fromOrdinal_ne_zero n
      (CardinalNatural.Peano.eq_zero_of_le_zero _ hle0)).elim
  | some y =>
    have htry :
        tryInclude p.commonDifference p.limit (x + p.commonDifference) =
          some y := by
      simpa [toProgression] using hnext
    have hy : y = x + p.commonDifference :=
      eq_of_tryInclude_eq_some p.commonDifference p.limit
        (x + p.commonDifference) y htry
    exact congrArg some hy

theorem progression_getElementFrom_eq_of_current_eq {α : Type _}
    (next : α → Option α) {c1 c2 : Option α} (hEq : c1 = c2)
    (h1 : Acc (Sequences.Progression.OptionStep next) c1)
    (index : OrdinalNatural.Peano)
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
    (index : OrdinalNatural.Peano)
    (hle1 : CardinalNatural.Peano.fromOrdinal index ≤
      Sequences.Progression.getLengthFrom next current h1)
    (hle2 : CardinalNatural.Peano.fromOrdinal index ≤
      Sequences.Progression.getLengthFrom next current h2) :
    Sequences.Progression.getElementFrom next current h1 index hle1 =
      Sequences.Progression.getElementFrom next current h2 index hle2 :=
  rfl

/-- Walking `Progression.getElementFrom` from an in-range element matches
`getElementFrom` (additions only, no further limit comparisons). -/
theorem getElementFrom_eq_progression (p : FiniteArithmetic)
    (x : Peano)
    (hAcc : Acc (Sequences.Progression.OptionStep (toProgression p).next)
      (some x))
    (index : OrdinalNatural.Peano)
    (hle : CardinalNatural.Peano.fromOrdinal index ≤
      Sequences.Progression.getLengthFrom (toProgression p).next (some x)
        hAcc) :
    getElementFrom x p.commonDifference index =
      Sequences.Progression.getElementFrom (toProgression p).next (some x) hAcc
        index hle := by
  induction index generalizing x hAcc with
  | one =>
    rfl
  | successor n ih =>
    have hnext :=
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
def getElement (p : FiniteArithmetic) (index : OrdinalNatural.Peano)
    (hle : CardinalNatural.Peano.fromOrdinal index ≤ getLength p) : Peano :=
  match hf : (toProgression p).first with
  | none =>
    (not_fromOrdinal_le_getLength_of_first_none p index hle hf).elim
  | some first =>
    getElementFrom first p.commonDifference index

/-- `getElement` agrees with walking `toProgression` via `Progression.getElement`. -/
theorem getElement_eq (p : FiniteArithmetic)
    (index : OrdinalNatural.Peano)
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
      Sequences.Progression.acc_first_of_finite (toProgression p)
        (toProgression_finite p)
    have hAcc' :
        Acc (Sequences.Progression.OptionStep (toProgression p).next)
          (some first) :=
      hf ▸ hAcc
    have hle_prog :
        CardinalNatural.Peano.fromOrdinal index ≤
          Sequences.Progression.getLength (toProgression p)
            (toProgression_finite p) :=
      getLength_eq p ▸ hle
    have hle' :
        CardinalNatural.Peano.fromOrdinal index ≤
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

/-- Two finite arithmetic progressions are equivalent when their underlying
progressions yield related elements (equality for Peano) at every positive
ordinal index. -/
def Equivalence (p q : FiniteArithmetic) : Prop :=
  Sequences.Progression.Equivalence (toProgression p) (toProgression q)

instance : HasEquiv FiniteArithmetic where
  Equiv := Equivalence

/-- The optional first element after applying the limit filter, without building
a `Progression`. -/
def effectiveFirst (p : FiniteArithmetic) : Option Peano :=
  match p.first with
  | none => none
  | some x => tryInclude p.commonDifference p.limit x

theorem effectiveFirst_eq (p : FiniteArithmetic) :
    effectiveFirst p = (toProgression p).first :=
  rfl

theorem lengthFromGap_ne_zero (diff : OrdinalNatural.Peano)
    (gap : Option OrdinalNatural.Peano)
    (h : lengthFromGap diff gap = CardinalNatural.Peano.zero) : False := by
  unfold lengthFromGap at h
  match gap with
  | none =>
    change CardinalNatural.Peano.one = CardinalNatural.Peano.zero at h
    exact (CardinalNatural.Peano.successor_ne_zero _).elim h
  | some g =>
    match hdiv : OrdinalNatural.Peano.divideWithRemainder g diff with
    | (none, _) =>
      change (match OrdinalNatural.Peano.divideWithRemainder g diff with
        | (none, _) => CardinalNatural.Peano.one
        | (some q, _) =>
          CardinalNatural.Peano.fromOrdinal (OrdinalNatural.Peano.successor q)) =
          CardinalNatural.Peano.zero at h
      simp only [hdiv] at h
      exact (CardinalNatural.Peano.successor_ne_zero _).elim h
    | (some q, _) =>
      change (match OrdinalNatural.Peano.divideWithRemainder g diff with
        | (none, _) => CardinalNatural.Peano.one
        | (some q, _) =>
          CardinalNatural.Peano.fromOrdinal (OrdinalNatural.Peano.successor q)) =
          CardinalNatural.Peano.zero at h
      simp only [hdiv] at h
      exact (CardinalNatural.Peano.successor_ne_zero _).elim h

theorem getLength_eq_zero_iff_effectiveFirst_none (p : FiniteArithmetic) :
    getLength p = CardinalNatural.Peano.zero ↔ effectiveFirst p = none := by
  cases p with
  | mk first commonDifference limit commonDifference_ne_zero =>
    constructor
    · intro hlen
      match first with
      | none =>
        rfl
      | some first =>
        match commonDifference with
        | positive d =>
          simp only [getLength] at hlen
          match hc : compare first limit with
          | .greater hgt =>
            simp only [effectiveFirst, tryInclude]
            have : ¬ first ≤ limit := not_le_of_gt hgt
            simp only [this, ↓reduceIte]
          | .equal heq =>
            simp only [hc] at hlen
            change CardinalNatural.Peano.one = CardinalNatural.Peano.zero at hlen
            exact False.elim ((CardinalNatural.Peano.successor_ne_zero _).elim hlen)
          | .less hlt =>
            simp only [hc] at hlen
            exact (lengthFromGap_ne_zero d _ hlen).elim
        | negative d =>
          simp only [getLength] at hlen
          match hc : compare first limit with
          | .less hlt =>
            simp only [effectiveFirst, tryInclude]
            have : ¬ limit ≤ first := not_le_of_gt hlt
            simp only [this, ↓reduceIte]
          | .equal heq =>
            simp only [hc] at hlen
            change CardinalNatural.Peano.one = CardinalNatural.Peano.zero at hlen
            exact False.elim ((CardinalNatural.Peano.successor_ne_zero _).elim hlen)
          | .greater hgt =>
            simp only [hc] at hlen
            exact (lengthFromGap_ne_zero d _ hlen).elim
        | zero =>
          exact (commonDifference_ne_zero rfl).elim
    · intro hfirst
      match first with
      | none =>
        rfl
      | some first =>
        match commonDifference with
        | positive d =>
          simp only [effectiveFirst, tryInclude] at hfirst
          by_cases hle : first ≤ limit
          · simp only [hle, ↓reduceIte] at hfirst
            nomatch hfirst
          · simp only [getLength]
            match hc : compare first limit with
            | .greater _ =>
              rfl
            | .equal heq =>
              exact (hle (Or.inr heq)).elim
            | .less hlt =>
              exact (hle (Or.inl hlt)).elim
        | negative d =>
          simp only [effectiveFirst, tryInclude] at hfirst
          by_cases hle : limit ≤ first
          · simp only [hle, ↓reduceIte] at hfirst
            nomatch hfirst
          · simp only [getLength]
            match hc : compare first limit with
            | .less _ =>
              rfl
            | .equal heq =>
              exact (hle (Or.inr heq.symm)).elim
            | .greater hgt =>
              exact (hle (Or.inl hgt)).elim
        | zero =>
          exact (commonDifference_ne_zero rfl).elim

theorem not_getLength_zero_of_effectiveFirst_some (p : FiniteArithmetic)
    (first : Peano) (hf : effectiveFirst p = some first)
    (hlen : getLength p = CardinalNatural.Peano.zero) : False := by
  have : effectiveFirst p = none :=
    (getLength_eq_zero_iff_effectiveFirst_none p).mp hlen
  rw [this] at hf
  cases hf

/-- In-range `tryGetElement` matches `getElementFrom` on the effective first. -/
theorem tryGetElement_eq_some_getElementFrom_of_le (p : FiniteArithmetic)
    (first : Peano) (hf : effectiveFirst p = some first)
    (index : OrdinalNatural.Peano)
    (hle : CardinalNatural.Peano.fromOrdinal index ≤ getLength p) :
    Sequences.Progression.tryGetElement index (toProgression p) =
      some (getElementFrom first p.commonDifference index) := by
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
theorem tryGetElement_eq_none_of_length_lt (p : FiniteArithmetic)
    (index : OrdinalNatural.Peano)
    (hlt : getLength p < CardinalNatural.Peano.fromOrdinal index) :
    Sequences.Progression.tryGetElement index (toProgression p) = none := by
  have hlt' :
      Sequences.Progression.getLength (toProgression p) (toProgression_finite p) <
        CardinalNatural.Peano.fromOrdinal index :=
    getLength_eq p ▸ hlt
  exact Sequences.Progression.tryGetElement_eq_none_of_getLength_lt
    (toProgression p) (toProgression_finite p) index hlt'

theorem effectiveFirst_eq_some_of_pos_length (p : FiniteArithmetic)
    (h : getLength p ≠ CardinalNatural.Peano.zero) :
    ∃ first, effectiveFirst p = some first := by
  cases hf : effectiveFirst p with
  | none =>
    exact False.elim (h ((getLength_eq_zero_iff_effectiveFirst_none p).mpr hf))
  | some first =>
    exact ⟨first, rfl⟩

/-- Empty progressions are equivalent. -/
theorem equivalence_of_both_empty (p q : FiniteArithmetic)
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
theorem equivalence_of_length_zero (p q : FiniteArithmetic)
    (hp : getLength p = CardinalNatural.Peano.zero)
    (hq : getLength q = CardinalNatural.Peano.zero) :
    Equivalence p q :=
  equivalence_of_both_empty p q
    ((getLength_eq_zero_iff_effectiveFirst_none p).mp hp)
    ((getLength_eq_zero_iff_effectiveFirst_none q).mp hq)

/-- Length-one progressions with the same first element are equivalent. -/
theorem equivalence_of_length_one (p q : FiniteArithmetic) (first : Peano)
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

/-- Progressions with the same first element, common difference, and length are
equivalent. -/
theorem equivalence_of_same_params (p q : FiniteArithmetic) (first : Peano)
    (hp : effectiveFirst p = some first) (hq : effectiveFirst q = some first)
    (hdiff : p.commonDifference = q.commonDifference)
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
      CardinalNatural.Peano.lt_of_not_le nhleP
    have hltQ :
        getLength q < CardinalNatural.Peano.fromOrdinal index := hlen ▸ hltP
    have htp := tryGetElement_eq_none_of_length_lt p index hltP
    have htq := tryGetElement_eq_none_of_length_lt q index hltQ
    simp only [htp, htq]
    exact Option.Rel.none

theorem effectiveFirst_eq_of_equivalence (p q : FiniteArithmetic)
    (h : Equivalence p q) : effectiveFirst p = effectiveFirst q := by
  generalize hfp : effectiveFirst p = fp
  generalize hfq : effectiveFirst q = fq
  have h1 := h OrdinalNatural.Peano.one
  simp only [Sequences.Progression.tryGetElement, ← effectiveFirst_eq, hfp, hfq]
    at h1
  match fp, fq, h1 with
  | none, none, Option.Rel.none =>
    rfl
  | some x, some y, Option.Rel.some heq =>
    exact congrArg some heq

theorem getLength_eq_of_equivalence (p q : FiniteArithmetic)
    (h : Equivalence p q) : getLength p = getLength q := by
  cases CardinalNatural.Peano.trichotomy_or (getLength p) (getLength q) with
  | inl hlt =>
    have hne : getLength q ≠ CardinalNatural.Peano.zero := by
      intro hq0
      rw [hq0] at hlt
      exact CardinalNatural.Peano.not_lt_zero _ hlt
    obtain ⟨firstQ, hfQ⟩ := effectiveFirst_eq_some_of_pos_length q hne
    let index : OrdinalNatural.Peano :=
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
      exact CardinalNatural.Peano.succ_le_of_lt hlt
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
      let index : OrdinalNatural.Peano :=
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
        exact CardinalNatural.Peano.succ_le_of_lt hgt
      have hsomeP :=
        tryGetElement_eq_some_getElementFrom_of_le p firstP hfP index hleP
      have hrel := h index
      simp only [hsomeP, hnoneQ] at hrel
      cases hrel

theorem commonDifference_eq_of_equivalence_of_length_ge_two
    (p q : FiniteArithmetic) (first : Peano) (n : CardinalNatural.Peano)
    (hp : effectiveFirst p = some first) (hq : effectiveFirst q = some first)
    (hlenP : getLength p =
      CardinalNatural.Peano.successor (CardinalNatural.Peano.successor n))
    (hlen : getLength p = getLength q) (h : Equivalence p q) :
    p.commonDifference = q.commonDifference := by
  have hleP :
      CardinalNatural.Peano.fromOrdinal OrdinalNatural.Peano.one.successor ≤
        getLength p := by
    rw [hlenP]
    change CardinalNatural.Peano.successor CardinalNatural.Peano.one ≤
      CardinalNatural.Peano.successor (CardinalNatural.Peano.successor n)
    exact CardinalNatural.Peano.succ_le_succ
      (CardinalNatural.Peano.succ_le_succ (CardinalNatural.Peano.zero_le n))
  have hleQ :
      CardinalNatural.Peano.fromOrdinal OrdinalNatural.Peano.one.successor ≤
        getLength q :=
    hlen ▸ hleP
  have htp :=
    tryGetElement_eq_some_getElementFrom_of_le p first hp
      OrdinalNatural.Peano.one.successor hleP
  have htq :=
    tryGetElement_eq_some_getElementFrom_of_le q first hq
      OrdinalNatural.Peano.one.successor hleQ
  have hrel := h OrdinalNatural.Peano.one.successor
  simp only [htp, htq, getElementFrom] at hrel
  cases hrel with
  | some heq =>
    have hcancel :
        (first + p.commonDifference) - first =
          (first + q.commonDifference) - first :=
      congrArg (fun x => x - first) heq
    rw [add_sub_cancel_left, add_sub_cancel_left] at hcancel
    exact hcancel

theorem getLength_ge_two_of_ne_zero_ne_one (p : FiniteArithmetic)
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

/-- Equivalence of finite arithmetic progressions is decidable by comparing
lengths, effective first elements, and (when the length is at least two) common
differences — without converting to `Progression` or walking successive terms
against the limit. -/
instance (p q : FiniteArithmetic) : Decidable (p ≈ q) :=
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
      else if hD : p.commonDifference = q.commonDifference then
        match hf : effectiveFirst p with
        | none =>
          False.elim (hZ ((getLength_eq_zero_iff_effectiveFirst_none p).mpr hf))
        | some first =>
          isTrue (equivalence_of_same_params p q first hf (hF ▸ hf) hD hL)
      else
        isFalse fun heq => by
          obtain ⟨first, hf⟩ := effectiveFirst_eq_some_of_pos_length p hZ
          obtain ⟨n, hlenP⟩ := getLength_ge_two_of_ne_zero_ne_one p hZ hOne
          exact hD (commonDifference_eq_of_equivalence_of_length_ge_two
            p q first n hf (hF ▸ hf) hlenP hL heq)
    else
      isFalse fun heq => hF (effectiveFirst_eq_of_equivalence p q heq)
  else
    isFalse fun heq => hL (getLength_eq_of_equivalence p q heq)

end FiniteArithmetic

end ZeroMath.Numbers.Integer.Peano.Progressions
