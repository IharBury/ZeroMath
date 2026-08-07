import ZeroMath.Numbers.Integer.Peano
import ZeroMath.Numbers.Integer.Peano.Progressions.InfiniteArithmetic
import ZeroMath.Sequences.List
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

/-- Elements from a known start for the given remaining length, advancing by the
common difference with no limit comparisons. -/
def getElementsFrom (first commonDifference : Peano) :
    CardinalNatural.Peano → Sequences.List Peano
  | .zero => .empty
  | .successor n =>
    .firstElement first
      (getElementsFrom (first + commonDifference) commonDifference n)

/-- The ordered list of all elements of a finite arithmetic progression. Empty
when there is no in-range first element. Uses the effective first element and
`getLength`, then advances by repeated addition of the common difference —
avoiding a limit comparison at every step. -/
def getElements (p : FiniteArithmetic) : Sequences.List Peano :=
  match effectiveFirst p with
  | none => .empty
  | some first =>
    getElementsFrom first p.commonDifference (getLength p)

/-- If `rest` continues an arithmetic progression after `prev` with common
difference `diff`, return the last element of that progression (which is `prev`
when `rest` is empty). Returns `none` when a consecutive pair does not advance
by exactly `diff`. Integer subtraction is total, so each step compares
`x - prev` with `diff` (which may be positive or negative). -/
def tryLastOfArithmeticContinuation (prev diff : Peano) :
    Sequences.List Peano → Option Peano
  | .empty => some prev
  | .firstElement x xs =>
    if x - prev = diff then
      tryLastOfArithmeticContinuation x diff xs
    else
      none

/-- Reconstruct a finite arithmetic progression from the ordered list of all its
elements. Requires a proof that at least two elements are given. Returns `none`
when consecutive steps are not a constant nonzero common difference.

Uses the first element, the common difference between consecutive terms
(positive or negative), and the last element as the limit. -/
def tryFromElements :
    (elements : Sequences.List Peano) →
    CardinalNatural.Peano.two ≤ elements.length →
    Option FiniteArithmetic
  | .empty, hge =>
    False.elim (CardinalNatural.Peano.not_two_le_zero (by
      change CardinalNatural.Peano.two ≤ CardinalNatural.Peano.zero
      exact hge))
  | .firstElement _ .empty, hge =>
    False.elim (CardinalNatural.Peano.not_two_le_one (by
      change CardinalNatural.Peano.two ≤ CardinalNatural.Peano.one
      exact hge))
  | .firstElement x (.firstElement y ys), _ =>
    let diff := y - x
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

/-- Last element of a non-empty arithmetic walk of cardinal length `n`, starting
at `first` with common difference `commonDifference` (of either sign). For
`n = zero` the value is unused (`first`). -/
def lastElementFrom (first commonDifference : Peano) :
    CardinalNatural.Peano → Peano
  | .zero => first
  | .successor n =>
    match n with
    | .zero => first
    | .successor _ =>
      lastElementFrom (first + commonDifference) commonDifference n

theorem lastElementFrom_one (first commonDifference : Peano) :
    lastElementFrom first commonDifference CardinalNatural.Peano.one = first :=
  rfl

theorem lastElementFrom_succ_succ (first commonDifference : Peano)
    (n : CardinalNatural.Peano) :
    lastElementFrom first commonDifference
        (CardinalNatural.Peano.successor
          (CardinalNatural.Peano.successor n)) =
      lastElementFrom (first + commonDifference) commonDifference
        (CardinalNatural.Peano.successor n) :=
  rfl

/-- The last element of a walk of length `n.successor` is `first` advanced by
`n` steps of `commonDifference`. -/
theorem lastElementFrom_eq_add_mul (first commonDifference : Peano)
    (n : CardinalNatural.Peano) :
    lastElementFrom first commonDifference n.successor =
      first + fromCardinalNatural n * commonDifference := by
  induction n generalizing first with
  | zero =>
    change first = first + fromCardinalNatural CardinalNatural.Peano.zero *
      commonDifference
    rw [show fromCardinalNatural CardinalNatural.Peano.zero = zero from rfl,
      zero_mul, add_zero]
  | successor n ih =>
    rw [lastElementFrom_succ_succ, ih]
    have hmul :
        fromCardinalNatural n.successor * commonDifference =
          fromCardinalNatural n * commonDifference + commonDifference := by
      rw [fromCardinalNatural_successor, mul_comm, mul_succ, mul_comm]
    rw [hmul, add_assoc,
      add_comm commonDifference (fromCardinalNatural n * commonDifference)]

/-- Continuing an arithmetic walk from `prev` by `getElementsFrom` recovers the
last element of that walk. -/
theorem tryLastOfArithmeticContinuation_getElementsFrom
    (prev commonDifference : Peano) (n : CardinalNatural.Peano) :
    tryLastOfArithmeticContinuation prev commonDifference
        (getElementsFrom (prev + commonDifference) commonDifference n) =
      some (lastElementFrom prev commonDifference n.successor) := by
  induction n generalizing prev with
  | zero =>
    rfl
  | successor n ih =>
    simp only [getElementsFrom, tryLastOfArithmeticContinuation,
      add_sub_cancel_left, ↓reduceIte]
    have ih' := ih (prev + commonDifference)
    rw [ih']
    cases n <;> rfl

theorem getElementsFrom_succ_succ (first commonDifference : Peano)
    (n : CardinalNatural.Peano) :
    getElementsFrom first commonDifference
        (CardinalNatural.Peano.successor
          (CardinalNatural.Peano.successor n)) =
      .firstElement first
        (.firstElement (first + commonDifference)
          (getElementsFrom (first + commonDifference + commonDifference)
            commonDifference n)) :=
  rfl

/-- `getElementsFrom` produces a list whose length equals the length argument. -/
theorem getElementsFrom_length (first commonDifference : Peano)
    (n : CardinalNatural.Peano) :
    (getElementsFrom first commonDifference n).length = n := by
  induction n generalizing first with
  | zero => rfl
  | successor n ih =>
    change
      (getElementsFrom (first + commonDifference) commonDifference n).length +
          CardinalNatural.Peano.one =
        n.successor
    rw [ih, CardinalNatural.Peano.add_one]

theorem getElementsFrom_ge_two_length (first commonDifference : Peano)
    (n : CardinalNatural.Peano) :
    CardinalNatural.Peano.two ≤
      (getElementsFrom first commonDifference
        (CardinalNatural.Peano.successor
          (CardinalNatural.Peano.successor n))).length := by
  rw [getElementsFrom_length]
  change
    CardinalNatural.Peano.two ≤
      CardinalNatural.Peano.successor
        (CardinalNatural.Peano.successor n)
  simpa only [CardinalNatural.Peano.two, CardinalNatural.Peano.one] using
    (CardinalNatural.Peano.succ_le_succ
      (CardinalNatural.Peano.succ_le_succ
        (CardinalNatural.Peano.zero_le n)))

/-- Reconstructing from `getElementsFrom` of length at least two recovers the
start, common difference, and last element. -/
theorem tryFromElements_getElementsFrom_ge_two (first commonDifference : Peano)
    (hne : commonDifference ≠ zero) (n : CardinalNatural.Peano)
    (hge : CardinalNatural.Peano.two ≤
        (getElementsFrom first commonDifference
          (CardinalNatural.Peano.successor
            (CardinalNatural.Peano.successor n))).length :=
      getElementsFrom_ge_two_length first commonDifference n) :
    tryFromElements
        (getElementsFrom first commonDifference
          (CardinalNatural.Peano.successor
            (CardinalNatural.Peano.successor n)))
        hge =
      some ({
        first := some first
        commonDifference := commonDifference
        limit :=
          lastElementFrom first commonDifference
            (CardinalNatural.Peano.successor
              (CardinalNatural.Peano.successor n))
        commonDifference_ne_zero := hne
      } : FiniteArithmetic) := by
  simp only [getElementsFrom, tryFromElements, add_sub_cancel_left]
  split
  · next heq => exact (hne heq).elim
  · next _hne =>
    have hlast :=
      tryLastOfArithmeticContinuation_getElementsFrom
        (first + commonDifference) commonDifference n
    simp only [hlast]
    rfl

theorem lengthFromGap_self (diff : OrdinalNatural.Peano) :
    lengthFromGap diff (some diff) =
      CardinalNatural.Peano.successor CardinalNatural.Peano.one := by
  unfold lengthFromGap
  simp only [OrdinalNatural.Peano.divideWithRemainder_self,
    CardinalNatural.Peano.fromOrdinal, CardinalNatural.Peano.one]

theorem ordinalDistance_self_add_positive (first : Peano)
    (d : OrdinalNatural.Peano) :
    ordinalDistance first (first + positive d) (lt_add_of_positive first d) =
      d :=
  positive_injective
    ((ordinalDistance_sub (lt_add_of_positive first d)).symm.trans
      (add_sub_cancel_left first (positive d)))

theorem sub_self_add (a b : Peano) : a - (a + b) = -b := by
  rw [sub_eq_add_neg, neg_add, ← add_assoc, add_neg_self, zero_add]

theorem ordinalDistance_self_add_negative (first : Peano)
    (d : OrdinalNatural.Peano) :
    ordinalDistance (first + negative d) first (add_negative_lt first d) =
      d :=
  positive_injective
    ((ordinalDistance_sub (add_negative_lt first d)).symm.trans (by
      rw [sub_self_add, show (-negative d : Peano) = positive d from rfl]))

/-- Length of a progression whose limit is exactly `lastElementFrom` of its
positive length. -/
theorem getLength_lastElementFrom (first commonDifference : Peano)
    (hne_diff : commonDifference ≠ zero) (n : CardinalNatural.Peano)
    (hne : n ≠ CardinalNatural.Peano.zero) :
    getLength {
      first := some first
      commonDifference := commonDifference
      limit := lastElementFrom first commonDifference n
      commonDifference_ne_zero := hne_diff
    } = n := by
  cases n with
  | zero => exact (hne rfl).elim
  | successor k =>
    have hlast := lastElementFrom_eq_add_mul first commonDifference k
    rw [hlast]
    match commonDifference with
    | zero => exact (hne_diff rfl).elim
    | positive d =>
      cases k with
      | zero =>
        rw [show fromCardinalNatural CardinalNatural.Peano.zero = zero from rfl,
          zero_mul, add_zero]
        simp only [getLength]
        match hc : compare first first with
        | .greater hgt => exact (not_lt_self first hgt).elim
        | .equal _ => rfl
        | .less hlt => exact (not_lt_self first hlt).elim
      | successor m =>
        let q :=
          CardinalNatural.Peano.toOrdinal
            (CardinalNatural.Peano.successor m)
            (CardinalNatural.Peano.successor_ne_zero m)
        have hfrom :
            fromCardinalNatural (CardinalNatural.Peano.successor m) =
              positive q := rfl
        have hmul :
            fromCardinalNatural (CardinalNatural.Peano.successor m) *
                positive d =
              positive (q * d) := by
          rw [hfrom, mul_pos_pos]
        rw [hmul]
        have hlt := lt_add_of_positive first (q * d)
        simp only [getLength]
        match hc : compare first (first + positive (q * d)) with
        | .greater hgt => exact (not_le_of_gt hgt (Or.inl hlt)).elim
        | .equal heq =>
          rw [heq.symm] at hlt
          exact (not_lt_self first hlt).elim
        | .less hlt' =>
          have hdist :
              ordinalDistance first (first + positive (q * d)) hlt' =
                q * d :=
            positive_injective
              ((ordinalDistance_sub hlt').symm.trans
                (add_sub_cancel_left first (positive (q * d))))
          have hdiv :
              OrdinalNatural.Peano.divideWithRemainder (q * d) d =
                (some q, none) :=
            OrdinalNatural.Peano.divideWithRemainder_eq_of_some_none
              (q * d) d q (OrdinalNatural.Peano.multiply_comm q d)
          simp only [hdist, lengthFromGap, hdiv,
            CardinalNatural.Peano.fromOrdinal]
          change
              CardinalNatural.Peano.successor
                  (CardinalNatural.Peano.fromOrdinal q) =
                CardinalNatural.Peano.successor
                  (CardinalNatural.Peano.successor m)
          exact congrArg CardinalNatural.Peano.successor
            (CardinalNatural.Peano.fromOrdinal_toOrdinal
              (CardinalNatural.Peano.successor m)
              (CardinalNatural.Peano.successor_ne_zero m))
    | negative d =>
      cases k with
      | zero =>
        rw [show fromCardinalNatural CardinalNatural.Peano.zero = zero from rfl,
          zero_mul, add_zero]
        simp only [getLength]
        match hc : compare first first with
        | .greater hgt => exact (not_lt_self first hgt).elim
        | .equal _ => rfl
        | .less hlt => exact (not_lt_self first hlt).elim
      | successor m =>
        let q :=
          CardinalNatural.Peano.toOrdinal
            (CardinalNatural.Peano.successor m)
            (CardinalNatural.Peano.successor_ne_zero m)
        have hfrom :
            fromCardinalNatural (CardinalNatural.Peano.successor m) =
              positive q := rfl
        have hmul :
            fromCardinalNatural (CardinalNatural.Peano.successor m) *
                negative d =
              negative (q * d) := by
          rw [hfrom, mul_pos_neg]
        rw [hmul]
        have hgt := add_negative_lt first (q * d)
        simp only [getLength]
        match hc : compare first (first + negative (q * d)) with
        | .less hlt => exact (not_le_of_gt hlt (Or.inl hgt)).elim
        | .equal heq =>
          rw [heq.symm] at hgt
          exact (not_lt_self first hgt).elim
        | .greater hgt' =>
          have hdist :
              ordinalDistance (first + negative (q * d)) first hgt' =
                q * d :=
            positive_injective
              ((ordinalDistance_sub hgt').symm.trans (by
                rw [sub_self_add,
                  show (-negative (q * d) : Peano) = positive (q * d) from rfl]))
          have hdiv :
              OrdinalNatural.Peano.divideWithRemainder (q * d) d =
                (some q, none) :=
            OrdinalNatural.Peano.divideWithRemainder_eq_of_some_none
              (q * d) d q (OrdinalNatural.Peano.multiply_comm q d)
          simp only [hdist, lengthFromGap, hdiv,
            CardinalNatural.Peano.fromOrdinal]
          change
              CardinalNatural.Peano.successor
                  (CardinalNatural.Peano.fromOrdinal q) =
                CardinalNatural.Peano.successor
                  (CardinalNatural.Peano.successor m)
          exact congrArg CardinalNatural.Peano.successor
            (CardinalNatural.Peano.fromOrdinal_toOrdinal
              (CardinalNatural.Peano.successor m)
              (CardinalNatural.Peano.successor_ne_zero m))

theorem first_le_lastElementFrom_of_positive (first : Peano)
    (d : OrdinalNatural.Peano) (n : CardinalNatural.Peano)
    (hne : n ≠ CardinalNatural.Peano.zero) :
    first ≤ lastElementFrom first (positive d) n := by
  cases n with
  | zero => exact (hne rfl).elim
  | successor k =>
    rw [lastElementFrom_eq_add_mul]
    cases k with
    | zero =>
      rw [show fromCardinalNatural CardinalNatural.Peano.zero = zero from rfl,
        zero_mul, add_zero]
      exact Or.inr rfl
    | successor m =>
      have hmul :
          fromCardinalNatural (CardinalNatural.Peano.successor m) *
              positive d =
            positive
              (CardinalNatural.Peano.toOrdinal
                  (CardinalNatural.Peano.successor m)
                  (CardinalNatural.Peano.successor_ne_zero m) * d) := by
        rw [show fromCardinalNatural (CardinalNatural.Peano.successor m) =
            positive
              (CardinalNatural.Peano.toOrdinal
                (CardinalNatural.Peano.successor m)
                (CardinalNatural.Peano.successor_ne_zero m)) from rfl,
          mul_pos_pos]
      rw [hmul]
      exact Or.inl (lt_add_of_positive first _)

theorem last_le_firstElementFrom_of_negative (first : Peano)
    (d : OrdinalNatural.Peano) (n : CardinalNatural.Peano)
    (hne : n ≠ CardinalNatural.Peano.zero) :
    lastElementFrom first (negative d) n ≤ first := by
  cases n with
  | zero => exact (hne rfl).elim
  | successor k =>
    rw [lastElementFrom_eq_add_mul]
    cases k with
    | zero =>
      rw [show fromCardinalNatural CardinalNatural.Peano.zero = zero from rfl,
        zero_mul, add_zero]
      exact Or.inr rfl
    | successor m =>
      have hmul :
          fromCardinalNatural (CardinalNatural.Peano.successor m) *
              negative d =
            negative
              (CardinalNatural.Peano.toOrdinal
                  (CardinalNatural.Peano.successor m)
                  (CardinalNatural.Peano.successor_ne_zero m) * d) := by
        rw [show fromCardinalNatural (CardinalNatural.Peano.successor m) =
            positive
              (CardinalNatural.Peano.toOrdinal
                (CardinalNatural.Peano.successor m)
                (CardinalNatural.Peano.successor_ne_zero m)) from rfl,
          mul_pos_neg]
      rw [hmul]
      exact Or.inl (add_negative_lt first _)

theorem effectiveFirst_lastElementFrom (first commonDifference : Peano)
    (hne_diff : commonDifference ≠ zero) (n : CardinalNatural.Peano)
    (hne : n ≠ CardinalNatural.Peano.zero) :
    effectiveFirst {
      first := some first
      commonDifference := commonDifference
      limit := lastElementFrom first commonDifference n
      commonDifference_ne_zero := hne_diff
    } = some first := by
  simp only [effectiveFirst, tryInclude]
  match commonDifference with
  | zero => exact (hne_diff rfl).elim
  | positive d =>
    have hle := first_le_lastElementFrom_of_positive first d n hne
    simp only [hle, ↓reduceIte]
  | negative d =>
    have hle := last_le_firstElementFrom_of_negative first d n hne
    simp only [hle, ↓reduceIte]

/-- `tryFromElements` recovers a progression equivalent to `p` from
`getElements p` when `p` has length at least two. -/
theorem tryFromElements_getElements (p : FiniteArithmetic)
    (hge : CardinalNatural.Peano.two ≤ getLength p) :
    ∃ (hLen : CardinalNatural.Peano.two ≤ (getElements p).length)
      (q : FiniteArithmetic),
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
        getElementsFrom first p.commonDifference (getLength p) := by
    simp only [getElements, hf]
  have hLen : CardinalNatural.Peano.two ≤ (getElements p).length := by
    rw [hget, getElementsFrom_length]
    exact hge
  let last :=
    lastElementFrom first p.commonDifference
      (CardinalNatural.Peano.successor
        (CardinalNatural.Peano.successor m))
  let q : FiniteArithmetic :=
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
            (CardinalNatural.Peano.successor
              (CardinalNatural.Peano.successor m)) := by
      rw [hget, hlen]
    revert hLen
    rw [hget']
    intro hLen
    exact htry
  · have hfq :=
      effectiveFirst_lastElementFrom first p.commonDifference
        p.commonDifference_ne_zero
        (CardinalNatural.Peano.successor
          (CardinalNatural.Peano.successor m))
        (CardinalNatural.Peano.successor_ne_zero _)
    have hlenq :=
      getLength_lastElementFrom first p.commonDifference
        p.commonDifference_ne_zero
        (CardinalNatural.Peano.successor
          (CardinalNatural.Peano.successor m))
        (CardinalNatural.Peano.successor_ne_zero _)
    exact equivalence_of_same_params p q first hf hfq rfl
      (by rw [hlen, hlenq])

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
    by_cases hx : x - prev = diff
    · simp only [hx, ↓reduceIte] at h
      obtain ⟨hxs, hlast⟩ := ih x last h
      have hxeq : x = prev + diff :=
        (sub_add_cancel x prev).symm.trans (by rw [hx, add_comm])
      have hlen := Sequences.List.length_firstElement x xs
      constructor
      · have htail :
            xs = getElementsFrom (prev + diff + diff) diff xs.length :=
          hxs.trans (by rw [hxeq])
        have h1 :
            Sequences.List.firstElement x xs =
              Sequences.List.firstElement (prev + diff)
                (getElementsFrom (prev + diff + diff) diff xs.length) := by
          rw [hxeq]
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
          rw [hlast, hxeq]
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
    · simp only [hx, ↓reduceIte] at h
      nomatch h

/-- `getElements` recovers the original list from a successful
`tryFromElements`. -/
theorem getElements_tryFromElements (elements : Sequences.List Peano)
    (hge : CardinalNatural.Peano.two ≤ elements.length)
    (p : FiniteArithmetic)
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
    by_cases hdiff0 : y - x = zero
    · simp only [hdiff0, ↓reduceDIte] at h
      nomatch h
    · simp only [hdiff0, ↓reduceDIte] at h
      match hl : tryLastOfArithmeticContinuation y (y - x) ys with
      | none =>
        simp only [hl] at h
        nomatch h
      | some last =>
        simp only [hl] at h
        injection h with heq
        subst heq
        have hcont :
            tryLastOfArithmeticContinuation x (y - x)
                (Sequences.List.firstElement y ys) =
              some last := by
          simp only [tryLastOfArithmeticContinuation, ↓reduceIte, hl]
        obtain ⟨hrest, hlast⟩ :=
          eq_getElementsFrom_of_tryLastOfArithmeticContinuation x (y - x)
            (Sequences.List.firstElement y ys) last hcont
        have hne :
            (Sequences.List.firstElement y ys).length.successor ≠
              CardinalNatural.Peano.zero :=
          CardinalNatural.Peano.successor_ne_zero _
        have hf : effectiveFirst
            {
              first := some x
              commonDifference := y - x
              limit := last
              commonDifference_ne_zero := hdiff0
            } = some x := by
          rw [hlast]
          exact effectiveFirst_lastElementFrom x (y - x) hdiff0
            (Sequences.List.firstElement y ys).length.successor hne
        have hlenp :
            getLength
                {
                  first := some x
                  commonDifference := y - x
                  limit := last
                  commonDifference_ne_zero := hdiff0
                } =
              (Sequences.List.firstElement y ys).length.successor := by
          rw [hlast]
          exact getLength_lastElementFrom x (y - x) hdiff0
            (Sequences.List.firstElement y ys).length.successor hne
        simp only [getElements, hf, hlenp]
        calc
          getElementsFrom x (y - x)
              (Sequences.List.firstElement y ys).length.successor
              = Sequences.List.firstElement x
                  (getElementsFrom (x + (y - x)) (y - x)
                    (Sequences.List.firstElement y ys).length) :=
                rfl
          _ = Sequences.List.firstElement x
                (Sequences.List.firstElement y ys) := by
                rw [← hrest]

/-- Recover the first element of an arithmetic progression from an element at the
given ordinal index and the common difference. At index `one` the element is
itself the first; otherwise subtract
`(positive (predecessor index)) * commonDifference`. Integer subtraction is
total, so this always succeeds. -/
def tryFirstFromIndexedElement
    (index : OrdinalNatural.Peano) (element commonDifference : Peano) :
    Option Peano :=
  match index with
  | .one => some element
  | .successor n => some (element - (positive n * commonDifference))

/-- Given two ordered indexed elements (`index < index'`) of a prospective
finite arithmetic progression, recover the common difference
`(element' - element) / (index' - index)`. Returns `none` when the element gap
is not divisible by the index gap. Unlike the natural-number increasing
versions, the element difference may be negative, so the recovered common
difference may be negative as well. -/
def tryCommonDifferenceFromOrderedIndexedElements
    (index : OrdinalNatural.Peano) (element : Peano)
    (index' : OrdinalNatural.Peano) (element' : Peano)
    (hlt : index < index') :
    Option Peano :=
  tryDivide (element' - element)
    (positive (OrdinalNatural.Peano.subtract index' index hlt))

/-- Reconstruct a finite arithmetic progression from two of its elements at
different ordinal indexes together with the progression length. Returns `none`
when either index exceeds the length, when the recovered common difference is
zero, or when the values are not consistent with an arithmetic progression of
that length (element gap not divisible by the index gap).

The reconstructed progression uses the recovered first element and common
difference (of either sign), and takes the last element of an arithmetic walk
of the given length as the limit. -/
def tryFromTwoElementsAndLength
    (index1 : OrdinalNatural.Peano) (element1 : Peano)
    (index2 : OrdinalNatural.Peano) (element2 : Peano)
    (length : CardinalNatural.Peano)
    (hne : index1 ≠ index2) :
    Option FiniteArithmetic :=
  if CardinalNatural.Peano.fromOrdinal index1 ≤ length then
    if CardinalNatural.Peano.fromOrdinal index2 ≤ length then
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
      first + positive n * commonDifference := by
  induction n with
  | one =>
    change first + commonDifference = first + one * commonDifference
    rw [one_mul]
  | successor n ih =>
    have hmul :
        positive n.successor * commonDifference =
          positive n * commonDifference + commonDifference := by
      rw [mul_comm, mul_pos_succ, mul_comm (positive n)]
    calc
      getElementFrom first commonDifference
            (OrdinalNatural.Peano.successor n).successor
          = getElementFrom first commonDifference
              (OrdinalNatural.Peano.successor n) + commonDifference :=
            rfl
      _ = first + positive n * commonDifference + commonDifference := by
            rw [ih]
      _ = first + (positive n * commonDifference + commonDifference) := by
            rw [add_assoc]
      _ = first + positive n.successor * commonDifference := by
            rw [hmul]

/-- Advancing from `index` to a larger `index'` adds
`(positive (index' - index)) * commonDifference` to the element. -/
theorem getElementFrom_add_mul_of_lt (first commonDifference : Peano)
    (index index' : OrdinalNatural.Peano)
    (hlt : index < index') :
    getElementFrom first commonDifference index' =
      getElementFrom first commonDifference index +
        (positive (OrdinalNatural.Peano.subtract index' index hlt)) *
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
        (positive
            (OrdinalNatural.Peano.subtract n.successor
              OrdinalNatural.Peano.one hlt)) *
          commonDifference
    rw [getElementFrom_eq_add_mul, hsub]
  | .successor m, .one =>
    exact (OrdinalNatural.Peano.not_lt_one m.successor hlt).elim
  | .successor m, .successor n =>
    have hlt' : m < n := OrdinalNatural.Peano.lt_of_succ_lt_succ hlt
    have hsub :
        OrdinalNatural.Peano.subtract n.successor m.successor hlt =
          OrdinalNatural.Peano.subtract n m hlt' := by
      change OrdinalNatural.Peano.subtract n m
          (OrdinalNatural.Peano.lt_of_succ_lt_succ hlt) =
        OrdinalNatural.Peano.subtract n m hlt'
      exact OrdinalNatural.Peano.subtract_eq_of_eq _ _ rfl rfl
    rw [getElementFrom_eq_add_mul, getElementFrom_eq_add_mul, hsub]
    have hsum : m + OrdinalNatural.Peano.subtract n m hlt' = n := by
      rw [OrdinalNatural.Peano.add_comm]
      exact OrdinalNatural.Peano.subtract_add_cancel n m hlt'
    have hpos :
        positive n =
          positive m + positive (OrdinalNatural.Peano.subtract n m hlt') := by
      have heq :
          positive n =
            positive (m + OrdinalNatural.Peano.subtract n m hlt') :=
        congrArg positive hsum.symm
      exact heq.trans (add_pos_pos m _).symm
    have hmul :
        (positive m + positive (OrdinalNatural.Peano.subtract n m hlt')) *
            commonDifference =
          positive m * commonDifference +
            positive (OrdinalNatural.Peano.subtract n m hlt') *
              commonDifference := by
      rw [mul_comm, mul_add, mul_comm commonDifference (positive m),
        mul_comm commonDifference
          (positive (OrdinalNatural.Peano.subtract n m hlt'))]
    calc
      first + positive n * commonDifference
          = first +
              (positive m + positive (OrdinalNatural.Peano.subtract n m hlt')) *
                commonDifference := by
            rw [hpos]
      _ = first +
            (positive m * commonDifference +
              positive (OrdinalNatural.Peano.subtract n m hlt') *
                commonDifference) := by
            rw [hmul]
      _ = first + positive m * commonDifference +
            positive (OrdinalNatural.Peano.subtract n m hlt') *
              commonDifference := by
            rw [← add_assoc]

/-- In-range `getElement` agrees with `getElementFrom` on the effective first. -/
theorem getElement_eq_getElementFrom (p : FiniteArithmetic)
    (first : Peano) (hf : effectiveFirst p = some first)
    (index : OrdinalNatural.Peano)
    (hle : CardinalNatural.Peano.fromOrdinal index ≤ getLength p) :
    getElement p index hle = getElementFrom first p.commonDifference index := by
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

/-- Recovering the common difference from two indexed elements of an arithmetic
walk returns the walk's common difference. -/
theorem tryCommonDifferenceFromOrderedIndexedElements_getElementFrom
    (first commonDifference : Peano) (index index' : OrdinalNatural.Peano)
    (hlt : index < index') :
    tryCommonDifferenceFromOrderedIndexedElements
      index (getElementFrom first commonDifference index)
      index' (getElementFrom first commonDifference index') hlt =
      some commonDifference := by
  simp only [tryCommonDifferenceFromOrderedIndexedElements]
  have heq :=
    getElementFrom_add_mul_of_lt first commonDifference index index' hlt
  have hsub :
      getElementFrom first commonDifference index' -
          getElementFrom first commonDifference index =
        (positive (OrdinalNatural.Peano.subtract index' index hlt)) *
          commonDifference := by
    rw [heq, add_sub_cancel_left]
  rw [hsub]
  exact
    tryDivide_mul commonDifference
      (positive (OrdinalNatural.Peano.subtract index' index hlt))
      (positive_ne_zero _)

/-- Recovering the first element from an indexed element of an arithmetic walk
returns the walk's start. -/
theorem tryFirstFromIndexedElement_getElementFrom
    (first commonDifference : Peano) (index : OrdinalNatural.Peano) :
    tryFirstFromIndexedElement index
      (getElementFrom first commonDifference index) commonDifference =
      some first := by
  match index with
  | .one =>
    simp only [tryFirstFromIndexedElement, getElementFrom_one]
  | .successor n =>
    simp only [tryFirstFromIndexedElement, getElementFrom_eq_add_mul,
      add_sub_cancel]

/-- Reconstructing from any two distinct in-range elements of `p`, together with
`getLength p`, yields a progression equivalent to `p`. -/
theorem tryFromTwoElementsAndLength_getElement
    (p : FiniteArithmetic)
    (index1 index2 : OrdinalNatural.Peano)
    (hne : index1 ≠ index2)
    (hle1 : CardinalNatural.Peano.fromOrdinal index1 ≤ getLength p)
    (hle2 : CardinalNatural.Peano.fromOrdinal index2 ≤ getLength p) :
    ∃ (q : FiniteArithmetic),
      tryFromTwoElementsAndLength
        index1 (getElement p index1 hle1)
        index2 (getElement p index2 hle2)
        (getLength p) hne = some q ∧
      p ≈ q := by
  have hne0 : getLength p ≠ CardinalNatural.Peano.zero := by
    intro hzero
    have :
        CardinalNatural.Peano.fromOrdinal index1 ≤
          CardinalNatural.Peano.zero :=
      hzero ▸ hle1
    exact CardinalNatural.Peano.fromOrdinal_ne_zero index1
      (CardinalNatural.Peano.eq_zero_of_le_zero _ this)
  obtain ⟨first, hf⟩ := effectiveFirst_eq_some_of_pos_length p hne0
  have hget1 := getElement_eq_getElementFrom p first hf index1 hle1
  have hget2 := getElement_eq_getElementFrom p first hf index2 hle2
  let q : FiniteArithmetic :=
    {
      first := some first
      commonDifference := p.commonDifference
      limit := lastElementFrom first p.commonDifference (getLength p)
      commonDifference_ne_zero := p.commonDifference_ne_zero
    }
  refine ⟨q, ?_, ?_⟩
  · simp only [tryFromTwoElementsAndLength, hle1, hle2, ↓reduceIte, hget1,
      hget2]
    match OrdinalNatural.Peano.compare index1 index2 with
    | .equal heq =>
      exact (hne heq).elim
    | .less hlt =>
      have hdiff :=
        tryCommonDifferenceFromOrderedIndexedElements_getElementFrom
          first p.commonDifference index1 index2 hlt
      have hfirst :=
        tryFirstFromIndexedElement_getElementFrom
          first p.commonDifference index1
      simp only [hdiff, hfirst]
      have hdiff0 : p.commonDifference ≠ zero := p.commonDifference_ne_zero
      simp only [hdiff0, ↓reduceDIte]
      rfl
    | .greater hgt =>
      have hdiff :=
        tryCommonDifferenceFromOrderedIndexedElements_getElementFrom
          first p.commonDifference index2 index1 hgt
      have hfirst :=
        tryFirstFromIndexedElement_getElementFrom
          first p.commonDifference index2
      simp only [hdiff, hfirst]
      have hdiff0 : p.commonDifference ≠ zero := p.commonDifference_ne_zero
      simp only [hdiff0, ↓reduceDIte]
      rfl
  · have hfq :=
      effectiveFirst_lastElementFrom first p.commonDifference
        p.commonDifference_ne_zero (getLength p) hne0
    have hlenq :=
      getLength_lastElementFrom first p.commonDifference
        p.commonDifference_ne_zero (getLength p) hne0
    exact equivalence_of_same_params p q first hf hfq rfl hlenq.symm

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
    injection h with heq
    have helement : element = first + positive n * commonDifference := by
      have hsum : first + positive n * commonDifference = element := by
        rw [← heq]
        exact sub_add_cancel element (positive n * commonDifference)
      exact hsum.symm
    rw [getElementFrom_eq_add_mul, ← helement]

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
        (positive (OrdinalNatural.Peano.subtract index' index hlt)) * diff := by
  simp only [tryCommonDifferenceFromOrderedIndexedElements] at h
  have hmul :
      (positive (OrdinalNatural.Peano.subtract index' index hlt)) * diff =
        element' - element :=
    eq_of_tryDivide_mul h
  calc
    element'
        = (element' - element) + element := (sub_add_cancel element' element).symm
    _ = element + (element' - element) := add_comm _ _
    _ = element +
          (positive (OrdinalNatural.Peano.subtract index' index hlt)) * diff := by
          rw [hmul]

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
    (hne_diff : commonDifference ≠ zero) (n : CardinalNatural.Peano)
    (hne : n ≠ CardinalNatural.Peano.zero)
    (index : OrdinalNatural.Peano)
    (hle : CardinalNatural.Peano.fromOrdinal index ≤
      getLength {
        first := some first
        commonDifference := commonDifference
        limit := lastElementFrom first commonDifference n
        commonDifference_ne_zero := hne_diff
      }) :
    getElement
      {
        first := some first
        commonDifference := commonDifference
        limit := lastElementFrom first commonDifference n
        commonDifference_ne_zero := hne_diff
      }
      index hle =
      getElementFrom first commonDifference index := by
  have hfirst :
      effectiveFirst
        {
          first := some first
          commonDifference := commonDifference
          limit := lastElementFrom first commonDifference n
          commonDifference_ne_zero := hne_diff
        } =
        some first :=
    effectiveFirst_lastElementFrom first commonDifference hne_diff n hne
  exact getElement_eq_getElementFrom _ first hfirst index hle

theorem length_ne_zero_of_tryFromTwoElementsAndLength
    (index1 : OrdinalNatural.Peano) (element1 : Peano)
    (index2 : OrdinalNatural.Peano) (element2 : Peano)
    (length : CardinalNatural.Peano)
    (hne : index1 ≠ index2)
    (p : FiniteArithmetic)
    (h : tryFromTwoElementsAndLength index1 element1 index2 element2 length hne =
      some p) :
    length ≠ CardinalNatural.Peano.zero := by
  intro hzero
  simp only [tryFromTwoElementsAndLength] at h
  by_cases hle1 : CardinalNatural.Peano.fromOrdinal index1 ≤ length
  · have :
        CardinalNatural.Peano.fromOrdinal index1 ≤
          CardinalNatural.Peano.zero :=
      hzero ▸ hle1
    exact CardinalNatural.Peano.fromOrdinal_ne_zero index1
      (CardinalNatural.Peano.eq_zero_of_le_zero _ this)
  · simp only [hle1, ↓reduceIte] at h
    nomatch h

/-- A successful `tryFromTwoElementsAndLength` yields a progression whose
`getLength` is the given length and whose `getElement` at each of the two
indexes recovers the corresponding original element. -/
theorem getLength_getElement_of_tryFromTwoElementsAndLength
    (index1 : OrdinalNatural.Peano) (element1 : Peano)
    (index2 : OrdinalNatural.Peano) (element2 : Peano)
    (length : CardinalNatural.Peano)
    (hne : index1 ≠ index2)
    (p : FiniteArithmetic)
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
                  CardinalNatural.Peano.fromOrdinal index1 ≤
                    getLength {
                      first := some first
                      commonDifference := diff
                      limit := lastElementFrom first diff length
                      commonDifference_ne_zero := hdiff0
                    } := by
                rwa [hlenp]
              have hle2p :
                  CardinalNatural.Peano.fromOrdinal index2 ≤
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
                  CardinalNatural.Peano.fromOrdinal index1 ≤
                    getLength {
                      first := some first
                      commonDifference := diff
                      limit := lastElementFrom first diff length
                      commonDifference_ne_zero := hdiff0
                    } := by
                rwa [hlenp]
              have hle2p :
                  CardinalNatural.Peano.fromOrdinal index2 ≤
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

/-- Advance one step from an optional current element of a finite arithmetic
progression: add the common difference while the result does not lie past the
limit; stay at `none` once past the end. -/
def nextMaskedWalkElement (commonDifference limit : Peano) :
    Option Peano → Option Peano
  | none => none
  | some x =>
    tryInclude commonDifference limit (x + commonDifference)

/-- Whether every unmasked entry agrees with a progression walk that is already
positioned at `current` (the value of `tryGetElement` at the corresponding
index). Masked (`none`) entries are skipped after advancing the walk. Avoids
recomputing `tryGetElement` from the start at each unmasked entry. -/
def agreesWithMaskedElementsFromCurrent
    (commonDifference limit : Peano) (current : Option Peano) :
    Sequences.List (Option Peano) → Bool
  | .empty => true
  | .firstElement none rest =>
      agreesWithMaskedElementsFromCurrent commonDifference limit
        (nextMaskedWalkElement commonDifference limit current) rest
  | .firstElement (some x) rest =>
      match current with
      | none => false
      | some y =>
        if y = x then
          agreesWithMaskedElementsFromCurrent commonDifference limit
            (nextMaskedWalkElement commonDifference limit current) rest
        else
          false

/-- Whether every unmasked entry agrees with `tryGetElement` on `p`, scanning
from the given ordinal index. Masked (`none`) entries are ignored.

Seeks the starting element once via `effectiveFirst` / `getElementFrom` (or
`none` when out of range), then walks by successive addition of the common
difference — avoiding a fresh `tryGetElement` walk at every unmasked entry. -/
def agreesWithMaskedElementsFrom (p : FiniteArithmetic)
    (index : OrdinalNatural.Peano) (elements : Sequences.List (Option Peano)) :
    Bool :=
  match effectiveFirst p with
  | none =>
    agreesWithMaskedElementsFromCurrent p.commonDifference p.limit
      none elements
  | some first =>
    if CardinalNatural.Peano.fromOrdinal index ≤ getLength p then
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
    (index1 : OrdinalNatural.Peano) (element1 : Peano)
    (length : CardinalNatural.Peano)
    (index : OrdinalNatural.Peano) (hlt : index1 < index) :
    (elements : Sequences.List (Option Peano)) →
    CardinalNatural.Peano.one ≤ elements.unmaskedCount →
    Option FiniteArithmetic
  | .empty, hge =>
      False.elim (CardinalNatural.Peano.not_succ_le_zero (by
        simpa only [Sequences.List.unmaskedCount, CardinalNatural.Peano.one]
          using hge))
  | .firstElement none rest, hge =>
      tryFromMaskedElementsGivenOne index1 element1 length
        index.successor
        (OrdinalNatural.Peano.lt_trans hlt
          (OrdinalNatural.Peano.x_lt_succ_x index))
        rest (by
          simpa only [Sequences.List.unmaskedCount] using hge)
  | .firstElement (some element2) rest, _ =>
      match
        tryFromTwoElementsAndLength index1 element1 index element2 length
          (OrdinalNatural.Peano.ne_of_lt hlt) with
      | none => none
      | some p =>
        if agreesWithMaskedElementsFrom p index.successor rest then
          some p
        else
          none

/-- Scan a masked element list from the given ordinal index until the first
unmasked entry is found, then continue with `tryFromMaskedElementsGivenOne`. -/
def tryFromMaskedElementsFrom (index : OrdinalNatural.Peano)
    (length : CardinalNatural.Peano) :
    (elements : Sequences.List (Option Peano)) →
    CardinalNatural.Peano.two ≤ elements.unmaskedCount →
    Option FiniteArithmetic
  | .empty, hge =>
      False.elim (CardinalNatural.Peano.not_two_le_zero (by
        simpa only [Sequences.List.unmaskedCount] using hge))
  | .firstElement none rest, hge =>
      tryFromMaskedElementsFrom index.successor length rest (by
        simpa only [Sequences.List.unmaskedCount] using hge)
  | .firstElement (some x) rest, hge =>
      tryFromMaskedElementsGivenOne index x length
        index.successor (OrdinalNatural.Peano.x_lt_succ_x index) rest (by
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

/-- Reconstruct a finite arithmetic progression from an ordered list of its
elements in which some entries may be masked as `none`. Requires a proof that
at least two entries are unmasked. Returns `none` when the unmasked entries are
not consistent with a finite arithmetic progression whose length equals that of
the list.

Uses the first two unmasked entries (together with their ordinal indexes and the
list length) via `tryFromTwoElementsAndLength`, then checks that every remaining
unmasked entry agrees with the reconstructed progression. -/
def tryFromMaskedElements
    (elements : Sequences.List (Option Peano))
    (hge : CardinalNatural.Peano.two ≤ elements.unmaskedCount) :
    Option FiniteArithmetic :=
  tryFromMaskedElementsFrom OrdinalNatural.Peano.one elements.length elements hge

/-- Prop counterpart of `agreesWithMaskedElementsFrom`: every unmasked entry
equals `tryGetElement` at the corresponding ordinal index. -/
inductive AgreesWithMaskedElementsFrom (p : FiniteArithmetic) :
    OrdinalNatural.Peano → Sequences.List (Option Peano) → Prop where
  | empty (index : OrdinalNatural.Peano) :
      AgreesWithMaskedElementsFrom p index .empty
  | masked (index : OrdinalNatural.Peano) (rest : Sequences.List (Option Peano)) :
      AgreesWithMaskedElementsFrom p index.successor rest →
        AgreesWithMaskedElementsFrom p index (.firstElement none rest)
  | unmasked (index : OrdinalNatural.Peano) (x : Peano)
      (rest : Sequences.List (Option Peano)) :
      Sequences.Progression.tryGetElement index (toProgression p) = some x →
        AgreesWithMaskedElementsFrom p index.successor rest →
          AgreesWithMaskedElementsFrom p index (.firstElement (some x) rest)

/-- One walk step matches `toProgression.next` on a present element. -/
theorem nextMaskedWalkElement_eq_toProgression_next
    (p : FiniteArithmetic) (x : Peano) :
    nextMaskedWalkElement p.commonDifference p.limit (some x) =
      (toProgression p).next x :=
  rfl

/-- Advancing the masked walk from `tryGetElement index` yields
`tryGetElement index.successor`. -/
theorem nextMaskedWalkElement_tryGetElement (p : FiniteArithmetic)
    (index : OrdinalNatural.Peano) :
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
    (p : FiniteArithmetic) (index : OrdinalNatural.Peano)
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

/-- `agreesWithMaskedElementsFrom` starts its walk at `tryGetElement index`. -/
theorem agreesWithMaskedElementsFrom_eq_fromCurrent_tryGetElement
    (p : FiniteArithmetic) (index : OrdinalNatural.Peano)
    (elements : Sequences.List (Option Peano)) :
    agreesWithMaskedElementsFrom p index elements =
      agreesWithMaskedElementsFromCurrent p.commonDifference p.limit
        (Sequences.Progression.tryGetElement index (toProgression p))
        elements := by
  match hf : effectiveFirst p with
  | none =>
    have htry := tryGetElement_none_of_effectiveFirst_none p index hf
    simp only [agreesWithMaskedElementsFrom, hf, htry]
  | some first =>
    by_cases hle : CardinalNatural.Peano.fromOrdinal index ≤ getLength p
    · have htry :=
        tryGetElement_eq_some_getElementFrom_of_le p first hf index hle
      simp only [agreesWithMaskedElementsFrom, hf, hle, ↓reduceIte, htry]
    · have hlt : getLength p < CardinalNatural.Peano.fromOrdinal index := by
        cases CardinalNatural.Peano.trichotomy_or (getLength p)
            (CardinalNatural.Peano.fromOrdinal index) with
        | inl hlt => exact hlt
        | inr h =>
          cases h with
          | inl heq => exact False.elim (hle (Or.inr heq.symm))
          | inr hgt => exact False.elim (hle (Or.inl hgt))
      have htry := tryGetElement_eq_none_of_length_lt p index hlt
      simp only [agreesWithMaskedElementsFrom, hf, hle, ↓reduceIte, htry]

/-- The current-position walk agrees with the Prop when `current` is
`tryGetElement` at the corresponding index. -/
theorem agreesWithMaskedElementsFromCurrent_eq_true_iff
    (p : FiniteArithmetic) (index : OrdinalNatural.Peano) (current : Option Peano)
    (elements : Sequences.List (Option Peano))
    (hcur : current =
      Sequences.Progression.tryGetElement index (toProgression p)) :
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
            Sequences.Progression.tryGetElement index.successor
              (toProgression p) := by
        rw [hcur, nextMaskedWalkElement_tryGetElement]
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
            Sequences.Progression.tryGetElement index (toProgression p) =
              none := hcur.symm
        constructor
        · intro h
          exact False.elim (Bool.false_ne_true h)
        · intro h
          cases h with
          | unmasked _ _ _ htry' _ =>
            rw [htry] at htry'
            nomatch htry'
      | some y =>
        have htry :
            Sequences.Progression.tryGetElement index (toProgression p) =
              some y := hcur.symm
        simp only
        split
        · next heq =>
          cases heq
          have hnext :
              nextMaskedWalkElement p.commonDifference p.limit (some x) =
                Sequences.Progression.tryGetElement index.successor
                  (toProgression p) := by
            rw [← htry, nextMaskedWalkElement_tryGetElement]
          constructor
          · intro h
            exact AgreesWithMaskedElementsFrom.unmasked index x rest htry
              ((ih index.successor
                (nextMaskedWalkElement p.commonDifference p.limit (some x))
                hnext).mp h)
          · intro h
            cases h with
            | unmasked _ _ _ _ hrest =>
              exact (ih index.successor
                (nextMaskedWalkElement p.commonDifference p.limit (some x))
                hnext).mpr hrest
        · next hne =>
          constructor
          · intro h
            exact False.elim (Bool.false_ne_true h)
          · intro h
            cases h with
            | unmasked _ _ _ htry' _ =>
              have : some y = some x := htry.symm.trans htry'
              injection this with hy
              exact False.elim (hne hy)

theorem agreesWithMaskedElementsFrom_eq_true_iff
    (p : FiniteArithmetic) (index : OrdinalNatural.Peano)
    (elements : Sequences.List (Option Peano)) :
    agreesWithMaskedElementsFrom p index elements = true ↔
      AgreesWithMaskedElementsFrom p index elements := by
  rw [agreesWithMaskedElementsFrom_eq_fromCurrent_tryGetElement]
  exact agreesWithMaskedElementsFromCurrent_eq_true_iff p index
    (Sequences.Progression.tryGetElement index (toProgression p)) elements rfl

/-- In-range `tryGetElement` returns `some` of the corresponding `getElement`. -/
theorem tryGetElement_eq_some_getElement (p : FiniteArithmetic)
    (index : OrdinalNatural.Peano)
    (hle : CardinalNatural.Peano.fromOrdinal index ≤ getLength p) :
    Sequences.Progression.tryGetElement index (toProgression p) =
      some (getElement p index hle) := by
  have h :=
    Sequences.Progression.tryGetElement_eq_some_getElement
      (toProgression p) (toProgression_finite p) index (getLength_eq p ▸ hle)
  rwa [← getElement_eq p index hle] at h

theorem agreesWithMaskedElementsFrom_unmasked_eq_true
    (p : FiniteArithmetic) (index : OrdinalNatural.Peano) (x : Peano)
    (rest : Sequences.List (Option Peano))
    (hx : Sequences.Progression.tryGetElement index (toProgression p) = some x)
    (hrest : agreesWithMaskedElementsFrom p index.successor rest = true) :
    agreesWithMaskedElementsFrom p index (.firstElement (some x) rest) = true := by
  rw [agreesWithMaskedElementsFrom_eq_fromCurrent_tryGetElement, hx]
  rw [agreesWithMaskedElementsFrom_eq_fromCurrent_tryGetElement] at hrest
  simp only [agreesWithMaskedElementsFromCurrent, ↓reduceIte]
  rwa [show nextMaskedWalkElement p.commonDifference p.limit (some x) =
      Sequences.Progression.tryGetElement index.successor (toProgression p) from
    by rw [← hx, nextMaskedWalkElement_tryGetElement]]

/-- A successful `tryFromMaskedElementsGivenOne` recovers the given first
unmasked element, has the requested length, and agrees with every unmasked entry
in the scanned suffix. -/
theorem getLength_agreesWithMaskedElementsFrom_of_tryFromMaskedElementsGivenOne
    (index1 : OrdinalNatural.Peano) (element1 : Peano)
    (length : CardinalNatural.Peano)
    (index : OrdinalNatural.Peano) (hlt : index1 < index)
    (elements : Sequences.List (Option Peano))
    (hge : CardinalNatural.Peano.one ≤ elements.unmaskedCount)
    (p : FiniteArithmetic)
    (h : tryFromMaskedElementsGivenOne index1 element1 length index hlt
        elements hge = some p) :
    getLength p = length ∧
      Sequences.Progression.tryGetElement index1 (toProgression p) =
        some element1 ∧
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
        (OrdinalNatural.Peano.lt_trans hlt
          (OrdinalNatural.Peano.x_lt_succ_x index)) rest (by
          simpa only [Sequences.List.unmaskedCount] using hge) p (by
          simpa only [tryFromMaskedElementsGivenOne] using h)
    refine ⟨ih.1, ih.2.1, ?_⟩
    rw [agreesWithMaskedElementsFrom_eq_fromCurrent_tryGetElement]
    rw [agreesWithMaskedElementsFrom_eq_fromCurrent_tryGetElement] at ih
    simpa only [agreesWithMaskedElementsFromCurrent,
      nextMaskedWalkElement_tryGetElement] using ih.2.2
  | .firstElement (some element2) rest =>
    simp only [tryFromMaskedElementsGivenOne] at h
    match hs : tryFromTwoElementsAndLength index1 element1 index element2 length
        (OrdinalNatural.Peano.ne_of_lt hlt) with
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
            index1 element1 index element2 length
            (OrdinalNatural.Peano.ne_of_lt hlt) p hs
        have htry1 :
            Sequences.Progression.tryGetElement index1 (toProgression p) =
              some element1 := by
          obtain ⟨hle1, hget1⟩ := hsound.2.1
          exact (tryGetElement_eq_some_getElement p index1 hle1).trans
            (congrArg some hget1)
        have htry2 :
            Sequences.Progression.tryGetElement index (toProgression p) =
              some element2 := by
          obtain ⟨hle2, hget2⟩ := hsound.2.2
          exact (tryGetElement_eq_some_getElement p index hle2).trans
            (congrArg some hget2)
        refine ⟨hsound.1, htry1, ?_⟩
        exact agreesWithMaskedElementsFrom_unmasked_eq_true p index element2 rest
          htry2 hAgree
      · next =>
        nomatch h

/-- A successful `tryFromMaskedElementsFrom` has the requested length and agrees
with every unmasked entry from the given starting index. -/
theorem getLength_agreesWithMaskedElementsFrom_of_tryFromMaskedElementsFrom
    (index : OrdinalNatural.Peano) (length : CardinalNatural.Peano)
    (elements : Sequences.List (Option Peano))
    (hge : CardinalNatural.Peano.two ≤ elements.unmaskedCount)
    (p : FiniteArithmetic)
    (h : tryFromMaskedElementsFrom index length elements hge = some p) :
    getLength p = length ∧
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
      nextMaskedWalkElement_tryGetElement] using ih.2
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
        index x length index.successor
        (OrdinalNatural.Peano.x_lt_succ_x index) rest hgeRest p (by
          simpa only [tryFromMaskedElementsFrom] using h)
    refine ⟨hGiven.1, ?_⟩
    exact agreesWithMaskedElementsFrom_unmasked_eq_true p index x rest
      hGiven.2.1 hGiven.2.2

/-- A successful `tryFromMaskedElements` yields a progression whose length equals
the list length and whose `tryGetElement` recovers every unmasked entry at the
same ordinal index. -/
theorem getLength_agreesWithMaskedElements_of_tryFromMaskedElements
    (elements : Sequences.List (Option Peano))
    (hge : CardinalNatural.Peano.two ≤ elements.unmaskedCount)
    (p : FiniteArithmetic)
    (h : tryFromMaskedElements elements hge = some p) :
    getLength p = elements.length ∧
      AgreesWithMaskedElementsFrom p OrdinalNatural.Peano.one elements := by
  have h' :
      tryFromMaskedElementsFrom OrdinalNatural.Peano.one elements.length
        elements hge = some p := by
    simpa only [tryFromMaskedElements] using h
  have hsound :=
    getLength_agreesWithMaskedElementsFrom_of_tryFromMaskedElementsFrom
      OrdinalNatural.Peano.one elements.length elements hge p h'
  refine ⟨hsound.1, ?_⟩
  exact (agreesWithMaskedElementsFrom_eq_true_iff p OrdinalNatural.Peano.one
    elements).mp hsound.2

/-- Extend a finite arithmetic progression of length at least two to an infinite
arithmetic progression with the same effective first element and common
difference. The infinite progression begins with every element of the original
finite progression. -/
def extendToInfinite (p : FiniteArithmetic)
    (hge : CardinalNatural.Peano.two ≤ getLength p) :
    InfiniteArithmetic :=
  match hf : effectiveFirst p with
  | none =>
    False.elim
      (CardinalNatural.Peano.not_two_le_zero
        ((getLength_eq_zero_iff_effectiveFirst_none p).mpr hf ▸ hge))
  | some first =>
    { first := first, commonDifference := p.commonDifference }

/-- `InfiniteArithmetic.getElement` is the same recursive walk as
`getElementFrom`. -/
theorem InfiniteArithmetic_getElement_eq_getElementFrom
    (first commonDifference : Peano) (index : OrdinalNatural.Peano) :
    InfiniteArithmetic.getElement
      { first := first, commonDifference := commonDifference } index =
      getElementFrom first commonDifference index := by
  induction index with
  | one =>
    rfl
  | successor n ih =>
    simp only [InfiniteArithmetic.getElement, getElementFrom]
    rw [ih]

/-- In-range elements of a finite arithmetic progression agree with the
corresponding elements of its infinite extension. -/
theorem getElement_extendToInfinite (p : FiniteArithmetic)
    (hge : CardinalNatural.Peano.two ≤ getLength p)
    (index : OrdinalNatural.Peano)
    (hle : CardinalNatural.Peano.fromOrdinal index ≤ getLength p) :
    InfiniteArithmetic.getElement (extendToInfinite p hge) index =
      getElement p index hle := by
  unfold extendToInfinite
  split
  · next hf =>
    exact (CardinalNatural.Peano.not_two_le_zero
      ((getLength_eq_zero_iff_effectiveFirst_none p).mpr hf ▸ hge)).elim
  · next first hf =>
    rw [getElement_eq_getElementFrom p first hf index hle]
    exact InfiniteArithmetic_getElement_eq_getElementFrom
      first p.commonDifference index

end FiniteArithmetic

end ZeroMath.Numbers.Integer.Peano.Progressions

