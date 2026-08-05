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

end FiniteArithmetic

end ZeroMath.Numbers.Integer.Peano.Progressions
