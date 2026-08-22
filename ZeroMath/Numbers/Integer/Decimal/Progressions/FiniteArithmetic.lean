import ZeroMath.Numbers.CardinalNatural.Decimal
import ZeroMath.Numbers.Integer.Decimal
import ZeroMath.Numbers.Integer.Decimal.Progressions.InfiniteArithmetic
import ZeroMath.Numbers.Integer.Peano.Progressions.FiniteArithmetic
import ZeroMath.Sequences.List
import ZeroMath.Sequences.Progression

namespace ZeroMath.Numbers.Integer.Decimal.Progressions

/-- A finite arithmetic progression of Decimal integers with nonzero common
difference, defined by an optional first element (`none` for the empty
progression), the common difference, and a limit such that no element lies past
the limit in the direction of travel. When the common difference is positive the
progression is strictly increasing and no element exceeds the limit; when it is
negative the progression is strictly decreasing and no element is less than the
limit. The progression is also empty when the first element already lies past
the limit. -/
structure FiniteArithmetic where
  first : Option Decimal
  commonDifference : Decimal
  limit : Decimal
  commonDifference_ne_zero : ¬ commonDifference ≈ zero

namespace FiniteArithmetic

/-- Include `x` when it does not lie past `limit` for the given common
difference: at most the limit when the difference is positive, at least the
limit when it is negative. Returns `none` for a difference equivalent to
zero. -/
def tryInclude (commonDifference limit x : Decimal) : Option Decimal :=
  match commonDifference.toPeano with
  | .positive _ => if x ≤ limit then some x else none
  | .negative _ => if limit ≤ x then some x else none
  | .zero => none

/-- Convert a finite arithmetic progression to a general progression by taking
the same optional first element when it does not lie past the limit (otherwise
the empty progression) and advancing by the common difference while the next
element does not lie past the limit. -/
def toProgression (p : FiniteArithmetic) : Sequences.Progression Decimal where
  first :=
    match p.first with
    | none => none
    | some x => tryInclude p.commonDifference p.limit x
  next := fun x =>
    tryInclude p.commonDifference p.limit (x + p.commonDifference)

/-- Convert a finite arithmetic progression of Decimal integers to the
corresponding Peano finite arithmetic progression by embedding each field via
`Decimal.toPeano`. -/
def toPeano (p : FiniteArithmetic) : Peano.Progressions.FiniteArithmetic where
  first := p.first.map Decimal.toPeano
  commonDifference := p.commonDifference.toPeano
  limit := p.limit.toPeano
  commonDifference_ne_zero :=
    toPeano_ne_zero_of_not_equivalent_zero p.commonDifference_ne_zero

/-- If `tryInclude` returns a value, that value is the candidate element. -/
theorem eq_of_tryInclude_eq_some (commonDifference limit x y : Decimal)
    (h : tryInclude commonDifference limit x = some y) : y = x := by
  match hdiff : commonDifference.toPeano with
  | .positive _ =>
    simp only [tryInclude, hdiff] at h
    by_cases hle : x ≤ limit
    · simp only [hle, ↓reduceIte] at h
      injection h with heq
      exact heq.symm
    · simp only [hle, ↓reduceIte] at h
      nomatch h
  | .negative _ =>
    simp only [tryInclude, hdiff] at h
    by_cases hle : limit ≤ x
    · simp only [hle, ↓reduceIte] at h
      injection h with heq
      exact heq.symm
    · simp only [hle, ↓reduceIte] at h
      nomatch h
  | .zero =>
    simp only [tryInclude, hdiff] at h
    nomatch h

/-- When `tryInclude` succeeds on `x`, it returns `some x`. -/
theorem tryInclude_eq_some_self (commonDifference limit x y : Decimal)
    (h : tryInclude commonDifference limit x = some y) :
    tryInclude commonDifference limit x = some x := by
  rw [eq_of_tryInclude_eq_some commonDifference limit x y h] at h
  exact h

/-- `tryInclude` commutes with the Peano embedding. -/
theorem tryInclude_toPeano (commonDifference limit x : Decimal) :
    Option.map Decimal.toPeano (tryInclude commonDifference limit x) =
      Peano.Progressions.FiniteArithmetic.tryInclude
        commonDifference.toPeano limit.toPeano x.toPeano := by
  simp only [tryInclude, Peano.Progressions.FiniteArithmetic.tryInclude]
  cases commonDifference.toPeano with
  | zero =>
    rfl
  | positive _ =>
    have hiff := le_iff_toPeano_le x limit
    by_cases hle : x ≤ limit
    · simp only [hle, hiff.mp hle, ↓reduceIte, Option.map]
    · have hle' : ¬ x.toPeano ≤ limit.toPeano := fun h => hle (hiff.mpr h)
      simp only [hle, hle', ↓reduceIte, Option.map]
  | negative _ =>
    have hiff := le_iff_toPeano_le limit x
    by_cases hle : limit ≤ x
    · simp only [hle, hiff.mp hle, ↓reduceIte, Option.map]
    · have hle' : ¬ limit.toPeano ≤ x.toPeano := fun h => hle (hiff.mpr h)
      simp only [hle, hle', ↓reduceIte, Option.map]

/-- The first element of `toProgression` commutes with `toPeano`. -/
theorem first_toPeano (p : FiniteArithmetic) :
    Option.map Decimal.toPeano (toProgression p).first =
      (Peano.Progressions.FiniteArithmetic.toProgression (toPeano p)).first := by
  cases hf : p.first with
  | none =>
    simp only [toProgression, hf, toPeano,
      Peano.Progressions.FiniteArithmetic.toProgression, Option.map]
  | some x =>
    simp only [toProgression, hf, toPeano,
      Peano.Progressions.FiniteArithmetic.toProgression, Option.map]
    exact tryInclude_toPeano p.commonDifference p.limit x

/-- Advancing one step of `toProgression` commutes with `toPeano`. -/
theorem next_toPeano (p : FiniteArithmetic) (x : Decimal) :
    Option.map Decimal.toPeano ((toProgression p).next x) =
      (Peano.Progressions.FiniteArithmetic.toProgression
        (toPeano p)).next x.toPeano := by
  change Option.map Decimal.toPeano
      (tryInclude p.commonDifference p.limit (x + p.commonDifference)) =
    Peano.Progressions.FiniteArithmetic.tryInclude
      p.commonDifference.toPeano p.limit.toPeano
      (x.toPeano + p.commonDifference.toPeano)
  have htry := tryInclude_toPeano p.commonDifference p.limit (x + p.commonDifference)
  rw [add_toPeano] at htry
  exact htry

/-- `tryGetElement` commutes with the Peano embedding. -/
theorem tryGetElement_toPeano (p : FiniteArithmetic)
    (index : OrdinalNatural.Peano) :
    Option.map Decimal.toPeano
      (Sequences.Progression.tryGetElement index (toProgression p)) =
    Sequences.Progression.tryGetElement index
      (Peano.Progressions.FiniteArithmetic.toProgression (toPeano p)) := by
  induction index with
  | one =>
    exact first_toPeano p
  | successor n ih =>
    simp only [Sequences.Progression.tryGetElement]
    cases hp : Sequences.Progression.tryGetElement n (toProgression p) with
    | none =>
      have ih' :
          Sequences.Progression.tryGetElement n
            (Peano.Progressions.FiniteArithmetic.toProgression (toPeano p)) =
            none := by
        simpa [hp, Option.map] using ih.symm
      simp only [ih']
      rfl
    | some x =>
      have ih' :
          Sequences.Progression.tryGetElement n
            (Peano.Progressions.FiniteArithmetic.toProgression (toPeano p)) =
            some x.toPeano := by
        simpa [hp, Option.map] using ih.symm
      simp only [ih']
      exact next_toPeano p x

/-- The progression obtained from a finite arithmetic progression is finite:
`tryGetElement` is `none` at the same witness index as the Peano embedding. -/
theorem toProgression_finite (p : FiniteArithmetic) :
    Sequences.Progression.Finite (toProgression p) := by
  obtain ⟨index, hnone⟩ :=
    Peano.Progressions.FiniteArithmetic.toProgression_finite (toPeano p)
  refine ⟨index, ?_⟩
  have hmap := tryGetElement_toPeano p index
  rw [hnone] at hmap
  cases h : Sequences.Progression.tryGetElement index (toProgression p) with
  | none =>
    rfl
  | some _ =>
    simp only [h, Option.map] at hmap
    nomatch hmap

/-- Length remaining from an element already known to lie in the progression,
given the cardinal gap to the limit in the direction of travel (`none` when the
element equals the limit). Computed with one division by the absolute common
difference instead of comparing each successive term to the limit. -/
def lengthFromGap (diff : CardinalNatural.Decimal)
    (hdiff : ¬ diff ≈ CardinalNatural.Decimal.zero) :
    Option CardinalNatural.Decimal → CardinalNatural.Decimal
  | none => CardinalNatural.Decimal.one
  | some gap =>
    match CardinalNatural.Decimal.divideWithRemainder gap diff hdiff with
    | (q, _) => q.successor

/-- The length of a finite arithmetic progression: the number of elements before
`tryGetElement` first returns `none`. Uses a single comparison of the first
element to the limit and one division by the absolute common difference,
avoiding a comparison at every step of the progression. -/
def getLength (p : FiniteArithmetic) : CardinalNatural.Decimal :=
  match p.first with
  | none => CardinalNatural.Decimal.zero
  | some first =>
    match hdiff : p.commonDifference.toPeano with
    | .positive _ =>
      match compare first p.limit with
      | .greater _ => CardinalNatural.Decimal.zero
      | .equivalent _ => CardinalNatural.Decimal.one
      | .less _ =>
        lengthFromGap p.commonDifference.magnitude
          (magnitude_not_equivalent_zero_of_not_equivalent_zero
            p.commonDifference_ne_zero)
          (some (p.limit - first).magnitude)
    | .negative _ =>
      match compare first p.limit with
      | .less _ => CardinalNatural.Decimal.zero
      | .equivalent _ => CardinalNatural.Decimal.one
      | .greater _ =>
        lengthFromGap p.commonDifference.magnitude
          (magnitude_not_equivalent_zero_of_not_equivalent_zero
            p.commonDifference_ne_zero)
          (some (first - p.limit).magnitude)
    | .zero =>
      (p.commonDifference_ne_zero
        (equivalent_of_toPeano_eq (hdiff.trans toPeano_zero.symm))).elim

/-- Decimal `lengthFromGap` agrees with Peano `lengthFromGap` on matching
cardinal/ordinal embeddings of the common difference and gap. -/
theorem lengthFromGap_toPeano (diff : CardinalNatural.Decimal)
    (hdiff : ¬ diff ≈ CardinalNatural.Decimal.zero)
    (gap : Option CardinalNatural.Decimal)
    (d : OrdinalNatural.Peano)
    (hd : diff.toPeano = CardinalNatural.Peano.fromOrdinal d)
    (g : Option OrdinalNatural.Peano)
    (hg : gap.map CardinalNatural.Decimal.toPeano =
      g.map CardinalNatural.Peano.fromOrdinal) :
    (lengthFromGap diff hdiff gap).toPeano =
      Peano.Progressions.FiniteArithmetic.lengthFromGap d g := by
  cases gap with
  | none =>
    cases g with
    | none =>
      simp only [lengthFromGap,
        CardinalNatural.Decimal.toPeano_one,
        Peano.Progressions.FiniteArithmetic.lengthFromGap]
    | some _ =>
      simp only [Option.map] at hg
      nomatch hg
  | some gap =>
    cases g with
    | none =>
      simp only [Option.map] at hg
      nomatch hg
    | some g =>
      have hg' : gap.toPeano = CardinalNatural.Peano.fromOrdinal g := by
        simp only [Option.map] at hg
        injection hg
      match hdiv : CardinalNatural.Decimal.divideWithRemainder gap diff hdiff with
      | (q, r) =>
        have hspec := CardinalNatural.Decimal.divideWithRemainder_specification gap diff hdiff
        simp only [hdiv] at hspec
        obtain ⟨heq, hlt⟩ := hspec
        rw [hg', hd] at heq
        rw [hd] at hlt
        simp only [lengthFromGap, hdiv,
          Peano.Progressions.FiniteArithmetic.lengthFromGap]
        match hord : OrdinalNatural.Peano.divideWithRemainder g d with
        | (none, none) =>
          exact False.elim
            (OrdinalNatural.Peano.divideWithRemainder_not_none_none g d hord)
        | (none, some r_ord) =>
          have ha : g = r_ord :=
            OrdinalNatural.Peano.divideWithRemainder_none_some g d r_ord hord
          have hrlt : r_ord < d :=
            OrdinalNatural.Peano.divideWithRemainder_remainder_lt_b g d none r_ord hord
          have hexp :
              CardinalNatural.Peano.fromOrdinal g =
                CardinalNatural.Peano.fromOrdinal d * CardinalNatural.Peano.zero +
                  CardinalNatural.Peano.fromOrdinal r_ord := by
            rw [CardinalNatural.Peano.multiply_zero, CardinalNatural.Peano.zero_add, ha]
          obtain ⟨hq, _⟩ :=
            CardinalNatural.Peano.divide_remainder_unique
              (CardinalNatural.Peano.fromOrdinal d)
              q.toPeano r.toPeano CardinalNatural.Peano.zero
              (CardinalNatural.Peano.fromOrdinal r_ord)
              hlt (CardinalNatural.Peano.fromOrdinal_lt_of_lt hrlt) (heq.symm.trans hexp)
          rw [CardinalNatural.Decimal.successor_toPeano, hq]
          rfl
        | (some q_ord, none) =>
          have ha : g = d * q_ord :=
            OrdinalNatural.Peano.divideWithRemainder_some_none g d q_ord hord
          have hexp :
              CardinalNatural.Peano.fromOrdinal g =
                CardinalNatural.Peano.fromOrdinal d *
                  CardinalNatural.Peano.fromOrdinal q_ord +
                  CardinalNatural.Peano.zero := by
            rw [CardinalNatural.Peano.add_zero,
              ← CardinalNatural.Peano.fromOrdinal_multiply, ha]
          obtain ⟨hq, _⟩ :=
            CardinalNatural.Peano.divide_remainder_unique
              (CardinalNatural.Peano.fromOrdinal d)
              q.toPeano r.toPeano
              (CardinalNatural.Peano.fromOrdinal q_ord)
              CardinalNatural.Peano.zero
              hlt
              (CardinalNatural.Peano.zero_lt_of_ne_zero _
                (CardinalNatural.Peano.fromOrdinal_ne_zero d))
              (heq.symm.trans hexp)
          rw [CardinalNatural.Decimal.successor_toPeano, hq]
          rfl
        | (some q_ord, some r_ord) =>
          have ha : g = d * q_ord + r_ord :=
            OrdinalNatural.Peano.divideWithRemainder_some_some g d q_ord r_ord hord
          have hrlt : r_ord < d :=
            OrdinalNatural.Peano.divideWithRemainder_remainder_lt_b g d
              (some q_ord) r_ord hord
          have hexp :
              CardinalNatural.Peano.fromOrdinal g =
                CardinalNatural.Peano.fromOrdinal d *
                  CardinalNatural.Peano.fromOrdinal q_ord +
                  CardinalNatural.Peano.fromOrdinal r_ord := by
            rw [← CardinalNatural.Peano.fromOrdinal_multiply,
              ← CardinalNatural.Peano.fromOrdinal_add, ha]
          obtain ⟨hq, _⟩ :=
            CardinalNatural.Peano.divide_remainder_unique
              (CardinalNatural.Peano.fromOrdinal d)
              q.toPeano r.toPeano
              (CardinalNatural.Peano.fromOrdinal q_ord)
              (CardinalNatural.Peano.fromOrdinal r_ord)
              hlt (CardinalNatural.Peano.fromOrdinal_lt_of_lt hrlt) (heq.symm.trans hexp)
          rw [CardinalNatural.Decimal.successor_toPeano, hq]
          rfl

/-- `getLength` agrees with Peano `getLength` on the embedded progression. -/
theorem getLength_toPeano (p : FiniteArithmetic) :
    (getLength p).toPeano =
      Peano.Progressions.FiniteArithmetic.getLength (toPeano p) := by
  cases hf : p.first with
  | none =>
    simp only [getLength, hf, toPeano,
      Peano.Progressions.FiniteArithmetic.getLength,
      CardinalNatural.Decimal.toPeano_zero, Option.map]
  | some first =>
    match hdiff : p.commonDifference.toPeano with
    | .zero =>
      exact (p.commonDifference_ne_zero
        (equivalent_of_toPeano_eq (hdiff.trans toPeano_zero.symm))).elim
    | .positive d =>
      cases hcmp : Peano.compare first.toPeano p.limit.toPeano with
      | less hlt =>
        have hdec : compare first p.limit = .less hlt := by
          simp only [compare, hcmp]
        have hlen :
            getLength p =
              lengthFromGap p.commonDifference.magnitude
                (magnitude_not_equivalent_zero_of_not_equivalent_zero
                  p.commonDifference_ne_zero)
                (some (p.limit - first).magnitude) := by
          simp only [getLength, hf]
          split
          · next _ hdiff' =>
            rw [hdec]
          · next _ hdiff' =>
            nomatch hdiff.symm.trans hdiff'
          · next hdiff' =>
            exact (Peano.positive_ne_zero d (hdiff.symm.trans hdiff')).elim
        have hlenP :
            Peano.Progressions.FiniteArithmetic.getLength (toPeano p) =
              Peano.Progressions.FiniteArithmetic.lengthFromGap d
                (some (Peano.ordinalDistance first.toPeano p.limit.toPeano hlt)) := by
          simp only [toPeano, hf, Peano.Progressions.FiniteArithmetic.getLength,
            Option.map]
          split
          · next d' hdiff' =>
            have hd_eq : d = d' := by
              injection hdiff.symm.trans hdiff'
            subst hd_eq
            rw [hcmp]
          · next _ hdiff' =>
            nomatch hdiff.symm.trans hdiff'
          · next hdiff' =>
            exact (Peano.positive_ne_zero d (hdiff.symm.trans hdiff')).elim
        rw [hlen, hlenP]
        have hd :
            p.commonDifference.magnitude.toPeano =
              CardinalNatural.Peano.fromOrdinal d := by
          rw [magnitude_toPeano]
          exact absoluteCardinalPeano_eq_fromOrdinal_of_toPeano_positive
            p.commonDifference d hdiff
        have hsub : (p.limit - first).toPeano =
            p.limit.toPeano - first.toPeano := subtract_toPeano p.limit first
        have hpos : p.limit.toPeano - first.toPeano =
            Peano.positive (Peano.ordinalDistance first.toPeano p.limit.toPeano hlt) :=
          Peano.ordinalDistance_subtract hlt
        have hg :
            (p.limit - first).magnitude.toPeano =
              CardinalNatural.Peano.fromOrdinal
                (Peano.ordinalDistance first.toPeano p.limit.toPeano hlt) := by
          rw [magnitude_toPeano]
          exact absoluteCardinalPeano_eq_fromOrdinal_of_toPeano_positive
            (p.limit - first)
            (Peano.ordinalDistance first.toPeano p.limit.toPeano hlt)
            (hsub.trans hpos)
        exact
          lengthFromGap_toPeano p.commonDifference.magnitude
            (magnitude_not_equivalent_zero_of_not_equivalent_zero
              p.commonDifference_ne_zero)
            (some (p.limit - first).magnitude) d hd
            (some (Peano.ordinalDistance first.toPeano p.limit.toPeano hlt))
            (by simp only [Option.map, hg])
      | equal heq =>
        have hdec : compare first p.limit =
            .equivalent (equivalent_of_toPeano_eq heq) := by
          simp only [compare, hcmp]
        have hlen : getLength p = CardinalNatural.Decimal.one := by
          simp only [getLength, hf]
          split
          · next _ hdiff' =>
            rw [hdec]
          · next _ hdiff' =>
            nomatch hdiff.symm.trans hdiff'
          · next hdiff' =>
            nomatch hdiff.symm.trans hdiff'
        have hlenP :
            Peano.Progressions.FiniteArithmetic.getLength (toPeano p) =
              CardinalNatural.Peano.one := by
          simp only [toPeano, hf, Peano.Progressions.FiniteArithmetic.getLength,
            Option.map]
          split
          · next _ hdiff' =>
            rw [hcmp]
          · next _ hdiff' =>
            nomatch hdiff.symm.trans hdiff'
          · next hdiff' =>
            nomatch hdiff.symm.trans hdiff'
        rw [hlen, hlenP, CardinalNatural.Decimal.toPeano_one]
      | greater hgt =>
        have hdec : compare first p.limit = .greater hgt := by
          simp only [compare, hcmp]
        have hlen : getLength p = CardinalNatural.Decimal.zero := by
          simp only [getLength, hf]
          split
          · next _ hdiff' =>
            rw [hdec]
          · next _ hdiff' =>
            nomatch hdiff.symm.trans hdiff'
          · next hdiff' =>
            nomatch hdiff.symm.trans hdiff'
        have hlenP :
            Peano.Progressions.FiniteArithmetic.getLength (toPeano p) =
              CardinalNatural.Peano.zero := by
          simp only [toPeano, hf, Peano.Progressions.FiniteArithmetic.getLength,
            Option.map]
          split
          · next _ hdiff' =>
            rw [hcmp]
          · next _ hdiff' =>
            nomatch hdiff.symm.trans hdiff'
          · next hdiff' =>
            nomatch hdiff.symm.trans hdiff'
        rw [hlen, hlenP, CardinalNatural.Decimal.toPeano_zero]
    | .negative d =>
      cases hcmp : Peano.compare first.toPeano p.limit.toPeano with
      | greater hgt =>
        have hdec : compare first p.limit = .greater hgt := by
          simp only [compare, hcmp]
        have hlen :
            getLength p =
              lengthFromGap p.commonDifference.magnitude
                (magnitude_not_equivalent_zero_of_not_equivalent_zero
                  p.commonDifference_ne_zero)
                (some (first - p.limit).magnitude) := by
          simp only [getLength, hf]
          split
          · next _ hdiff' =>
            nomatch hdiff.symm.trans hdiff'
          · next _ hdiff' =>
            rw [hdec]
          · next hdiff' =>
            nomatch hdiff.symm.trans hdiff'
        have hlenP :
            Peano.Progressions.FiniteArithmetic.getLength (toPeano p) =
              Peano.Progressions.FiniteArithmetic.lengthFromGap d
                (some (Peano.ordinalDistance p.limit.toPeano first.toPeano hgt)) := by
          simp only [toPeano, hf, Peano.Progressions.FiniteArithmetic.getLength,
            Option.map]
          split
          · next _ hdiff' =>
            nomatch hdiff.symm.trans hdiff'
          · next d' hdiff' =>
            have hd_eq : d = d' := by
              injection hdiff.symm.trans hdiff'
            subst hd_eq
            rw [hcmp]
          · next hdiff' =>
            nomatch hdiff.symm.trans hdiff'
        rw [hlen, hlenP]
        have hd :
            p.commonDifference.magnitude.toPeano =
              CardinalNatural.Peano.fromOrdinal d := by
          rw [magnitude_toPeano]
          exact absoluteCardinalPeano_eq_fromOrdinal_of_toPeano_negative
            p.commonDifference d hdiff
        have hsub : (first - p.limit).toPeano =
            first.toPeano - p.limit.toPeano := subtract_toPeano first p.limit
        have hpos : first.toPeano - p.limit.toPeano =
            Peano.positive (Peano.ordinalDistance p.limit.toPeano first.toPeano hgt) :=
          Peano.ordinalDistance_subtract hgt
        have hg :
            (first - p.limit).magnitude.toPeano =
              CardinalNatural.Peano.fromOrdinal
                (Peano.ordinalDistance p.limit.toPeano first.toPeano hgt) := by
          rw [magnitude_toPeano]
          exact absoluteCardinalPeano_eq_fromOrdinal_of_toPeano_positive
            (first - p.limit)
            (Peano.ordinalDistance p.limit.toPeano first.toPeano hgt)
            (hsub.trans hpos)
        exact
          lengthFromGap_toPeano p.commonDifference.magnitude
            (magnitude_not_equivalent_zero_of_not_equivalent_zero
              p.commonDifference_ne_zero)
            (some (first - p.limit).magnitude) d hd
            (some (Peano.ordinalDistance p.limit.toPeano first.toPeano hgt))
            (by simp only [Option.map, hg])
      | equal heq =>
        have hdec : compare first p.limit =
            .equivalent (equivalent_of_toPeano_eq heq) := by
          simp only [compare, hcmp]
        have hlen : getLength p = CardinalNatural.Decimal.one := by
          simp only [getLength, hf]
          split
          · next _ hdiff' =>
            nomatch hdiff.symm.trans hdiff'
          · next _ hdiff' =>
            rw [hdec]
          · next hdiff' =>
            nomatch hdiff.symm.trans hdiff'
        have hlenP :
            Peano.Progressions.FiniteArithmetic.getLength (toPeano p) =
              CardinalNatural.Peano.one := by
          simp only [toPeano, hf, Peano.Progressions.FiniteArithmetic.getLength,
            Option.map]
          split
          · next _ hdiff' =>
            nomatch hdiff.symm.trans hdiff'
          · next _ hdiff' =>
            rw [hcmp]
          · next hdiff' =>
            nomatch hdiff.symm.trans hdiff'
        rw [hlen, hlenP, CardinalNatural.Decimal.toPeano_one]
      | less hlt =>
        have hdec : compare first p.limit = .less hlt := by
          simp only [compare, hcmp]
        have hlen : getLength p = CardinalNatural.Decimal.zero := by
          simp only [getLength, hf]
          split
          · next _ hdiff' =>
            nomatch hdiff.symm.trans hdiff'
          · next _ hdiff' =>
            rw [hdec]
          · next hdiff' =>
            nomatch hdiff.symm.trans hdiff'
        have hlenP :
            Peano.Progressions.FiniteArithmetic.getLength (toPeano p) =
              CardinalNatural.Peano.zero := by
          simp only [toPeano, hf, Peano.Progressions.FiniteArithmetic.getLength,
            Option.map]
          split
          · next _ hdiff' =>
            nomatch hdiff.symm.trans hdiff'
          · next _ hdiff' =>
            rw [hcmp]
          · next hdiff' =>
            nomatch hdiff.symm.trans hdiff'
        rw [hlen, hlenP, CardinalNatural.Decimal.toPeano_zero]

/-- Accessibility is preserved by embedding the current state via `toPeano`. -/
theorem acc_map_toPeano (p : FiniteArithmetic) (current : Option Decimal)
    (hAcc : Acc (Sequences.Progression.OptionStep (toProgression p).next) current) :
    Acc (Sequences.Progression.OptionStep
      (Peano.Progressions.FiniteArithmetic.toProgression (toPeano p)).next)
      (current.map Decimal.toPeano) := by
  refine Acc.rec
    (motive := fun current _ =>
      Acc (Sequences.Progression.OptionStep
        (Peano.Progressions.FiniteArithmetic.toProgression (toPeano p)).next)
        (current.map Decimal.toPeano))
    (fun current hcurr ih => by
      match current with
      | none =>
        exact Sequences.Progression.acc_none _
      | some x =>
        have hnext := next_toPeano p x
        have hAcc_next := ih ((toProgression p).next x)
          (Sequences.Progression.OptionStep.step x)
        have hAcc_next' :
            Acc (Sequences.Progression.OptionStep
              (Peano.Progressions.FiniteArithmetic.toProgression
                (toPeano p)).next)
              ((Peano.Progressions.FiniteArithmetic.toProgression
                (toPeano p)).next x.toPeano) :=
          hnext ▸ hAcc_next
        exact Sequences.Progression.acc_step hAcc_next')
    hAcc

/-- Walking length from an accessible Decimal state equals the Peano walk from
its embedding. -/
theorem getLengthFrom_toPeano (p : FiniteArithmetic)
    (current : Option Decimal)
    (hAcc : Acc (Sequences.Progression.OptionStep (toProgression p).next) current) :
    Sequences.Progression.getLengthFrom (toProgression p).next current hAcc =
      Sequences.Progression.getLengthFrom
        (Peano.Progressions.FiniteArithmetic.toProgression (toPeano p)).next
        (current.map Decimal.toPeano)
        (acc_map_toPeano p current hAcc) := by
  refine Acc.rec
    (motive := fun current hAcc =>
      Sequences.Progression.getLengthFrom (toProgression p).next current hAcc =
        Sequences.Progression.getLengthFrom
          (Peano.Progressions.FiniteArithmetic.toProgression (toPeano p)).next
          (current.map Decimal.toPeano)
          (acc_map_toPeano p current hAcc))
    (fun current hcurr ih => by
      match current with
      | none =>
        exact
          (Sequences.Progression.getLengthFrom_none _ (Acc.intro _ hcurr)).trans
            (Sequences.Progression.getLengthFrom_none _ _).symm
      | some x =>
        have hAccx :
            Acc (Sequences.Progression.OptionStep (toProgression p).next)
              (some x) := Acc.intro _ hcurr
        rw [Sequences.Progression.getLengthFrom_some (toProgression p).next x hAccx]
        have hmap : Option.map Decimal.toPeano (some x) = some x.toPeano := rfl
        have hAcc_map := acc_map_toPeano p (some x) hAccx
        rw [Sequences.Progression.getLengthFrom_eq_of_current_eq _ hmap hAcc_map]
        rw [Sequences.Progression.getLengthFrom_some
          (Peano.Progressions.FiniteArithmetic.toProgression (toPeano p)).next
          x.toPeano (hmap ▸ hAcc_map)]
        have hnext := next_toPeano p x
        have ih' := ih ((toProgression p).next x)
          (Sequences.Progression.OptionStep.step x)
        refine congrArg CardinalNatural.Peano.successor (ih'.trans ?_)
        exact
          (Sequences.Progression.getLengthFrom_eq_of_current_eq _
            hnext
            (acc_map_toPeano p ((toProgression p).next x)
              (hAccx.inv (Sequences.Progression.OptionStep.step x)))).trans
            (Sequences.Progression.getLengthFrom_eq_of_acc_eq _ _ _ _))
    hAcc

/-- `Progression.getLength` of a Decimal finite arithmetic progression equals
that of its Peano embedding. -/
theorem progression_getLength_toPeano (p : FiniteArithmetic) :
    Sequences.Progression.getLength (toProgression p) (toProgression_finite p) =
      Sequences.Progression.getLength
        (Peano.Progressions.FiniteArithmetic.toProgression (toPeano p))
        (Peano.Progressions.FiniteArithmetic.toProgression_finite
          (toPeano p)) := by
  simp only [Sequences.Progression.getLength]
  have hwalk :=
    getLengthFrom_toPeano p (toProgression p).first
      (Sequences.Progression.acc_first_of_finite (toProgression p)
        (toProgression_finite p))
  have hfirst := first_toPeano p
  refine hwalk.trans ?_
  exact
    (Sequences.Progression.getLengthFrom_eq_of_current_eq _
      hfirst
      (acc_map_toPeano p (toProgression p).first
        (Sequences.Progression.acc_first_of_finite (toProgression p)
          (toProgression_finite p)))).trans
      (Sequences.Progression.getLengthFrom_eq_of_acc_eq _ _ _ _)

/-- `getLength` agrees with walking `toProgression` via `Progression.getLength`. -/
theorem getLength_eq (p : FiniteArithmetic) :
    getLength p ≈
      CardinalNatural.Decimal.fromPeano
        (Sequences.Progression.getLength (toProgression p)
          (toProgression_finite p)) := by
  apply CardinalNatural.Decimal.equivalent_of_toPeano_eq
  rw [CardinalNatural.Decimal.toPeano_fromPeano, getLength_toPeano,
    Peano.Progressions.FiniteArithmetic.getLength_eq (toPeano p),
    progression_getLength_toPeano]

/-- If `toProgression` has no first element, the length is equivalent to zero. -/
theorem getLength_eq_zero_of_toProgression_first_none
    (p : FiniteArithmetic)
    (h : (toProgression p).first = none) :
    getLength p ≈ CardinalNatural.Decimal.zero := by
  have hAcc :=
    Sequences.Progression.acc_first_of_finite (toProgression p)
      (toProgression_finite p)
  have hEq :=
    Sequences.Progression.getLengthFrom_eq_of_current_eq (toProgression p).next h hAcc
  have hlen :
      Sequences.Progression.getLength (toProgression p) (toProgression_finite p) =
        CardinalNatural.Peano.zero := by
    simp only [Sequences.Progression.getLength]
    rw [hEq, Sequences.Progression.getLengthFrom_none]
  have heq := getLength_eq p
  rw [hlen] at heq
  exact heq

/-- The length bound is impossible when `toProgression` is empty. -/
theorem not_fromOrdinal_le_getLength_of_first_none
    (p : FiniteArithmetic) (index : OrdinalNatural.Decimal)
    (hle : CardinalNatural.Decimal.fromOrdinal index ≤ getLength p)
    (h : (toProgression p).first = none) : False := by
  have hle' :
      CardinalNatural.Decimal.fromOrdinal index ≤ CardinalNatural.Decimal.zero :=
    CardinalNatural.Decimal.le_trans hle
      (Or.inr (getLength_eq_zero_of_toProgression_first_none p h))
  exact CardinalNatural.Decimal.fromOrdinal_not_equivalent_zero index
    (CardinalNatural.Decimal.eq_zero_of_le_zero _ hle')

/-- Element at a positive ordinal index starting from a known first value, using
the closed form with no limit comparisons. Always
`first + (fromOrdinalNaturalPeano index - one) * commonDifference`. -/
def getElementFrom (first commonDifference : Decimal)
    (index : OrdinalNatural.Decimal) : Decimal :=
  InfiniteArithmetic.getElement
    { first := first, commonDifference := commonDifference } index

/-- Closed-form `getElementFrom` matches `InfiniteArithmetic.getElement`. -/
theorem getElementFrom_eq_InfiniteArithmetic_getElement
    (first commonDifference : Decimal) (index : OrdinalNatural.Decimal) :
    getElementFrom first commonDifference index =
      InfiniteArithmetic.getElement
        { first := first, commonDifference := commonDifference } index :=
  rfl

/-- The element at the given positive ordinal index, when that index does not
exceed the progression's length. The first element has index equivalent to
`one`. Computed by taking the (at most one) comparison already performed in
`toProgression.first`, then the closed form of the arithmetic progression —
avoiding a limit comparison at every step of the walk. -/
def getElement (p : FiniteArithmetic) (index : OrdinalNatural.Decimal)
    (hle : CardinalNatural.Decimal.fromOrdinal index ≤ getLength p) :
    Decimal :=
  match hf : (toProgression p).first with
  | none =>
    (not_fromOrdinal_le_getLength_of_first_none p index hle hf).elim
  | some first =>
    getElementFrom first p.commonDifference index

/-- A Decimal length bound on `fromOrdinal index` yields the corresponding Peano
bound for walking `toProgression`. -/
theorem fromOrdinal_le_progression_getLength
    (p : FiniteArithmetic) (index : OrdinalNatural.Decimal)
    (hle : CardinalNatural.Decimal.fromOrdinal index ≤ getLength p) :
    CardinalNatural.Peano.fromOrdinal index.toPeano ≤
      Sequences.Progression.getLength (toProgression p)
        (toProgression_finite p) := by
  have hle' :
      CardinalNatural.Decimal.fromOrdinal index ≤
        CardinalNatural.Decimal.fromPeano
          (Sequences.Progression.getLength (toProgression p)
            (toProgression_finite p)) :=
    CardinalNatural.Decimal.le_trans hle (Or.inr (getLength_eq p))
  have hpeano := CardinalNatural.Decimal.toPeano_le_of_le hle'
  rw [CardinalNatural.Decimal.fromOrdinal_toPeano_eq_fromOrdinal_peano,
    CardinalNatural.Decimal.toPeano_fromPeano] at hpeano
  exact hpeano

/-- When `tryGetElement` succeeds from a known first element, the value is
equivalent to the closed-form `getElementFrom` at the Decimal index. -/
theorem eq_getElementFrom_of_tryGetElement_eq_some
    (p : FiniteArithmetic) (start : Decimal)
    (hf : (toProgression p).first = some start)
    (index : OrdinalNatural.Decimal) (x : Decimal)
    (h : Sequences.Progression.tryGetElement index.toPeano (toProgression p) =
      some x) :
    x ≈ getElementFrom start p.commonDifference index := by
  if hone : index ≈ OrdinalNatural.Decimal.one then
    have hpeano : index.toPeano = OrdinalNatural.Peano.one :=
      (OrdinalNatural.Decimal.toPeano_eq_one_iff_equivalent_one index).mpr hone
    rw [hpeano, Sequences.Progression.tryGetElement, hf] at h
    injection h with heq
    rw [← heq, getElementFrom_eq_InfiniteArithmetic_getElement]
    exact Setoid.symm
      (InfiniteArithmetic.getElement_equivalent_first_of_equivalent_one
        { first := start, commonDifference := p.commonDifference } index hone)
  else
    have hpeano :=
      OrdinalNatural.Decimal.toPeano_eq_successor_predecessor_toPeano index hone
    rw [hpeano, Sequences.Progression.tryGetElement] at h
    match htry : Sequences.Progression.tryGetElement
        (index.predecessor hone).toPeano (toProgression p) with
    | none =>
      rw [htry] at h
      nomatch h
    | some y =>
      rw [htry] at h
      have hy :=
        eq_getElementFrom_of_tryGetElement_eq_some p start hf
          (index.predecessor hone) y htry
      have hnext : (toProgression p).next y = some x := h
      have htry_next :
          tryInclude p.commonDifference p.limit (y + p.commonDifference) =
            some x := by
        simpa [toProgression] using hnext
      have hxeq : x = y + p.commonDifference :=
        eq_of_tryInclude_eq_some p.commonDifference p.limit
          (y + p.commonDifference) x htry_next
      have hadd :
          y + p.commonDifference ≈
            getElementFrom start p.commonDifference
              (index.predecessor hone) + p.commonDifference :=
        equivalent_add_right hy
      have hclosed :
          getElementFrom start p.commonDifference
              (index.predecessor hone) + p.commonDifference ≈
            getElementFrom start p.commonDifference index := by
        rw [getElementFrom_eq_InfiniteArithmetic_getElement,
          getElementFrom_eq_InfiniteArithmetic_getElement]
        exact InfiniteArithmetic.getElement_predecessor_add_commonDifference
          { first := start, commonDifference := p.commonDifference }
          index hone
      exact hxeq ▸ Setoid.trans hadd hclosed
termination_by index.toPeano
decreasing_by
  obtain ⟨hne, heq⟩ := OrdinalNatural.Decimal.predecessor_toPeano index hone
  simp only [heq]
  exact OrdinalNatural.Peano.sizeOf_predecessor_lt _ hne

/-- `getElement` agrees with walking `toProgression` via `Progression.getElement`
up to Decimal equivalence. -/
theorem getElement_eq (p : FiniteArithmetic)
    (index : OrdinalNatural.Decimal)
    (hle : CardinalNatural.Decimal.fromOrdinal index ≤ getLength p) :
    getElement p index hle ≈
      Sequences.Progression.getElement (toProgression p) (toProgression_finite p)
        index.toPeano (fromOrdinal_le_progression_getLength p index hle) := by
  have hle_peano := fromOrdinal_le_progression_getLength p index hle
  have htry :=
    Sequences.Progression.tryGetElement_eq_some_getElement
      (toProgression p) (toProgression_finite p) index.toPeano hle_peano
  dsimp only [getElement]
  split
  · next hf =>
    exact (not_fromOrdinal_le_getLength_of_first_none p index hle hf).elim
  · next start hf =>
    exact Setoid.symm
      (eq_getElementFrom_of_tryGetElement_eq_some p start hf index _ htry)

/-- The optional first element after applying the limit filter, without building
a `Progression`. -/
def effectiveFirst (p : FiniteArithmetic) : Option Decimal :=
  match p.first with
  | none => none
  | some x => tryInclude p.commonDifference p.limit x

theorem effectiveFirst_eq (p : FiniteArithmetic) :
    effectiveFirst p = (toProgression p).first :=
  rfl

/-- `effectiveFirst` commutes with the Peano embedding. -/
theorem effectiveFirst_toPeano (p : FiniteArithmetic) :
    Option.map Decimal.toPeano (effectiveFirst p) =
      Peano.Progressions.FiniteArithmetic.effectiveFirst (toPeano p) := by
  rw [effectiveFirst_eq, Peano.Progressions.FiniteArithmetic.effectiveFirst_eq]
  exact first_toPeano p

/-- Two finite arithmetic progressions are equivalent when their underlying
progressions yield related elements (Decimal setoid `≈`) at every positive
ordinal index. -/
def Equivalence (p q : FiniteArithmetic) : Prop :=
  Sequences.Progression.Equivalence (toProgression p) (toProgression q)

instance : HasEquiv FiniteArithmetic where
  Equiv := Equivalence

/-- Decimal progression equivalence matches Peano equivalence of the embeddings. -/
theorem equivalence_iff_toPeano (p q : FiniteArithmetic) :
    Equivalence p q ↔
      Peano.Progressions.FiniteArithmetic.Equivalence (toPeano p) (toPeano q) := by
  constructor
  · intro h index
    have hp := tryGetElement_toPeano p index
    have hq := tryGetElement_toPeano q index
    have hrel := h index
    match hdp : Sequences.Progression.tryGetElement index (toProgression p),
        hdq : Sequences.Progression.tryGetElement index (toProgression q), hrel with
    | none, none, Option.Rel.none =>
      have hpp :
          Sequences.Progression.tryGetElement index
            (Peano.Progressions.FiniteArithmetic.toProgression (toPeano p)) =
            none := by
        simpa [hdp, Option.map] using hp.symm
      have hqq :
          Sequences.Progression.tryGetElement index
            (Peano.Progressions.FiniteArithmetic.toProgression (toPeano q)) =
            none := by
        simpa [hdq, Option.map] using hq.symm
      simp only [hpp, hqq]
      exact Option.Rel.none
    | some x, some y, Option.Rel.some heq =>
      have hpp :
          Sequences.Progression.tryGetElement index
            (Peano.Progressions.FiniteArithmetic.toProgression (toPeano p)) =
            some x.toPeano := by
        simpa [hdp, Option.map] using hp.symm
      have hqq :
          Sequences.Progression.tryGetElement index
            (Peano.Progressions.FiniteArithmetic.toProgression (toPeano q)) =
            some y.toPeano := by
        simpa [hdq, Option.map] using hq.symm
      simp only [hpp, hqq]
      exact Option.Rel.some (toPeano_eq_of_equivalent heq)
    | none, some _, hbad =>
      cases hbad
    | some _, none, hbad =>
      cases hbad
  · intro h index
    have hp := tryGetElement_toPeano p index
    have hq := tryGetElement_toPeano q index
    have hrel := h index
    match hdp : Sequences.Progression.tryGetElement index (toProgression p) with
    | none =>
      have hpp :
          Sequences.Progression.tryGetElement index
            (Peano.Progressions.FiniteArithmetic.toProgression (toPeano p)) =
            none := by
        simpa [hdp, Option.map] using hp.symm
      match hdq : Sequences.Progression.tryGetElement index (toProgression q) with
      | none =>
        exact Option.Rel.none
      | some y =>
        have hqq :
            Sequences.Progression.tryGetElement index
              (Peano.Progressions.FiniteArithmetic.toProgression (toPeano q)) =
              some y.toPeano := by
          simpa [hdq, Option.map] using hq.symm
        simp only [hpp, hqq] at hrel
        cases hrel
    | some x =>
      have hpp :
          Sequences.Progression.tryGetElement index
            (Peano.Progressions.FiniteArithmetic.toProgression (toPeano p)) =
            some x.toPeano := by
        simpa [hdp, Option.map] using hp.symm
      match hdq : Sequences.Progression.tryGetElement index (toProgression q) with
      | none =>
        have hqq :
            Sequences.Progression.tryGetElement index
              (Peano.Progressions.FiniteArithmetic.toProgression (toPeano q)) =
              none := by
          simpa [hdq, Option.map] using hq.symm
        simp only [hpp, hqq] at hrel
        cases hrel
      | some y =>
        have hqq :
            Sequences.Progression.tryGetElement index
              (Peano.Progressions.FiniteArithmetic.toProgression (toPeano q)) =
              some y.toPeano := by
          simpa [hdq, Option.map] using hq.symm
        simp only [hpp, hqq] at hrel
        cases hrel with
        | some heq =>
          exact Option.Rel.some (equivalent_of_toPeano_eq heq)

theorem getLength_eq_zero_iff_effectiveFirst_none (p : FiniteArithmetic) :
    getLength p ≈ CardinalNatural.Decimal.zero ↔ effectiveFirst p = none := by
  constructor
  · intro hlen
    have hpeano :
        Peano.Progressions.FiniteArithmetic.getLength (toPeano p) =
          CardinalNatural.Peano.zero := by
      rw [← getLength_toPeano]
      exact (CardinalNatural.Decimal.toPeano_eq_of_equivalent hlen).trans
        CardinalNatural.Decimal.toPeano_zero
    have hf :=
      (Peano.Progressions.FiniteArithmetic.getLength_eq_zero_iff_effectiveFirst_none
        (toPeano p)).mp hpeano
    have hmap := effectiveFirst_toPeano p
    simp only [hf, Option.map] at hmap
    match heff : effectiveFirst p with
    | none =>
      rfl
    | some _ =>
      simp only [heff] at hmap
      nomatch hmap
  · intro hfirst
    have hf :
        Peano.Progressions.FiniteArithmetic.effectiveFirst (toPeano p) = none := by
      have hmap := effectiveFirst_toPeano p
      simp only [hfirst, Option.map] at hmap
      exact hmap.symm
    have hpeano :=
      (Peano.Progressions.FiniteArithmetic.getLength_eq_zero_iff_effectiveFirst_none
        (toPeano p)).mpr hf
    apply CardinalNatural.Decimal.equivalent_of_toPeano_eq
    rw [getLength_toPeano, hpeano, CardinalNatural.Decimal.toPeano_zero]

theorem effectiveFirst_eq_some_of_positive_length (p : FiniteArithmetic)
    (h : ¬ getLength p ≈ CardinalNatural.Decimal.zero) :
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
  have hp' :
      Peano.Progressions.FiniteArithmetic.effectiveFirst (toPeano p) = none := by
    simpa [hp, Option.map] using (effectiveFirst_toPeano p).symm
  have hq' :
      Peano.Progressions.FiniteArithmetic.effectiveFirst (toPeano q) = none := by
    simpa [hq, Option.map] using (effectiveFirst_toPeano q).symm
  exact (equivalence_iff_toPeano p q).mpr
    (Peano.Progressions.FiniteArithmetic.equivalence_of_both_empty
      (toPeano p) (toPeano q) hp' hq')

/-- Empty progressions (length zero) are equivalent. -/
theorem equivalence_of_length_zero (p q : FiniteArithmetic)
    (hp : getLength p ≈ CardinalNatural.Decimal.zero)
    (hq : getLength q ≈ CardinalNatural.Decimal.zero) :
    Equivalence p q :=
  equivalence_of_both_empty p q
    ((getLength_eq_zero_iff_effectiveFirst_none p).mp hp)
    ((getLength_eq_zero_iff_effectiveFirst_none q).mp hq)

/-- Length-one progressions with equivalent first elements are equivalent. -/
theorem equivalence_of_length_one (p q : FiniteArithmetic)
    (firstP firstQ : Decimal)
    (hp : effectiveFirst p = some firstP) (hq : effectiveFirst q = some firstQ)
    (hfirst : firstP ≈ firstQ)
    (hlenP : getLength p ≈ CardinalNatural.Decimal.one)
    (hlenQ : getLength q ≈ CardinalNatural.Decimal.one) :
    Equivalence p q := by
  have hfirstPeano : firstP.toPeano = firstQ.toPeano :=
    toPeano_eq_of_equivalent hfirst
  have hp' :
      Peano.Progressions.FiniteArithmetic.effectiveFirst (toPeano p) =
        some firstP.toPeano := by
    simpa [hp, Option.map] using (effectiveFirst_toPeano p).symm
  have hq' :
      Peano.Progressions.FiniteArithmetic.effectiveFirst (toPeano q) =
        some firstP.toPeano := by
    have hq0 :
        Peano.Progressions.FiniteArithmetic.effectiveFirst (toPeano q) =
          some firstQ.toPeano := by
      simpa [hq, Option.map] using (effectiveFirst_toPeano q).symm
    exact hq0.trans (congrArg some hfirstPeano.symm)
  have hlenP' :
      Peano.Progressions.FiniteArithmetic.getLength (toPeano p) =
        CardinalNatural.Peano.one := by
    rw [← getLength_toPeano]
    exact (CardinalNatural.Decimal.toPeano_eq_of_equivalent hlenP).trans
      CardinalNatural.Decimal.toPeano_one
  have hlenQ' :
      Peano.Progressions.FiniteArithmetic.getLength (toPeano q) =
        CardinalNatural.Peano.one := by
    rw [← getLength_toPeano]
    exact (CardinalNatural.Decimal.toPeano_eq_of_equivalent hlenQ).trans
      CardinalNatural.Decimal.toPeano_one
  exact (equivalence_iff_toPeano p q).mpr
    (Peano.Progressions.FiniteArithmetic.equivalence_of_length_one
      (toPeano p) (toPeano q) firstP.toPeano hp' hq' hlenP' hlenQ')

/-- Progressions with equivalent first elements and common differences and
equivalent lengths are equivalent. -/
theorem equivalence_of_equivalent_params (p q : FiniteArithmetic)
    (firstP firstQ : Decimal)
    (hp : effectiveFirst p = some firstP) (hq : effectiveFirst q = some firstQ)
    (hfirst : firstP ≈ firstQ)
    (hdiff : p.commonDifference ≈ q.commonDifference)
    (hlen : getLength p ≈ getLength q) :
    Equivalence p q := by
  have hfirstPeano : firstP.toPeano = firstQ.toPeano :=
    toPeano_eq_of_equivalent hfirst
  have hp' :
      Peano.Progressions.FiniteArithmetic.effectiveFirst (toPeano p) =
        some firstP.toPeano := by
    simpa [hp, Option.map] using (effectiveFirst_toPeano p).symm
  have hq' :
      Peano.Progressions.FiniteArithmetic.effectiveFirst (toPeano q) =
        some firstP.toPeano := by
    have hq0 :
        Peano.Progressions.FiniteArithmetic.effectiveFirst (toPeano q) =
          some firstQ.toPeano := by
      simpa [hq, Option.map] using (effectiveFirst_toPeano q).symm
    exact hq0.trans (congrArg some hfirstPeano.symm)
  have hdiff' :
      (toPeano p).commonDifference = (toPeano q).commonDifference := by
    simp only [toPeano]
    exact toPeano_eq_of_equivalent hdiff
  have hlen' :
      Peano.Progressions.FiniteArithmetic.getLength (toPeano p) =
        Peano.Progressions.FiniteArithmetic.getLength (toPeano q) := by
    rw [← getLength_toPeano, ← getLength_toPeano]
    exact CardinalNatural.Decimal.toPeano_eq_of_equivalent hlen
  exact (equivalence_iff_toPeano p q).mpr
    (Peano.Progressions.FiniteArithmetic.equivalence_of_same_params
      (toPeano p) (toPeano q) firstP.toPeano hp' hq' hdiff' hlen')

/-- Progressions with the same first element, common difference, and length are
equivalent. -/
theorem equivalence_of_same_params (p q : FiniteArithmetic) (first : Decimal)
    (hp : effectiveFirst p = some first) (hq : effectiveFirst q = some first)
    (hdiff : p.commonDifference = q.commonDifference)
    (hlen : getLength p = getLength q) :
    Equivalence p q :=
  equivalence_of_equivalent_params p q first first hp hq (Setoid.refl _)
    (hdiff ▸ Setoid.refl _) (hlen ▸ Setoid.refl _)

theorem effectiveFirst_rel_of_equivalence (p q : FiniteArithmetic)
    (h : Equivalence p q) :
    Option.Rel (· ≈ ·) (effectiveFirst p) (effectiveFirst q) := by
  have h1 := h OrdinalNatural.Peano.one
  simp only [Sequences.Progression.tryGetElement, ← effectiveFirst_eq] at h1
  exact h1

theorem getLength_equivalent_of_equivalence (p q : FiniteArithmetic)
    (h : Equivalence p q) : getLength p ≈ getLength q := by
  have hpeano :=
    Peano.Progressions.FiniteArithmetic.getLength_eq_of_equivalence
      (toPeano p) (toPeano q) ((equivalence_iff_toPeano p q).mp h)
  apply CardinalNatural.Decimal.equivalent_of_toPeano_eq
  rw [getLength_toPeano, getLength_toPeano, hpeano]

theorem commonDifference_equivalent_of_equivalence_of_length_ge_two
    (p q : FiniteArithmetic) (firstP firstQ : Decimal)
    (hp : effectiveFirst p = some firstP) (hq : effectiveFirst q = some firstQ)
    (hfirst : firstP ≈ firstQ)
    (hne0 : ¬ getLength p ≈ CardinalNatural.Decimal.zero)
    (hne1 : ¬ getLength p ≈ CardinalNatural.Decimal.one)
    (hlen : getLength p ≈ getLength q) (h : Equivalence p q) :
    p.commonDifference ≈ q.commonDifference := by
  have h0 :
      Peano.Progressions.FiniteArithmetic.getLength (toPeano p) ≠
        CardinalNatural.Peano.zero := by
    intro hz
    apply hne0
    apply CardinalNatural.Decimal.equivalent_of_toPeano_eq
    rw [getLength_toPeano, hz, CardinalNatural.Decimal.toPeano_zero]
  have h1 :
      Peano.Progressions.FiniteArithmetic.getLength (toPeano p) ≠
        CardinalNatural.Peano.one := by
    intro hone
    apply hne1
    apply CardinalNatural.Decimal.equivalent_of_toPeano_eq
    rw [getLength_toPeano, hone, CardinalNatural.Decimal.toPeano_one]
  obtain ⟨n, hlenP⟩ :=
    Peano.Progressions.FiniteArithmetic.getLength_ge_two_of_ne_zero_ne_one
      (toPeano p) h0 h1
  have hfirstPeano : firstP.toPeano = firstQ.toPeano :=
    toPeano_eq_of_equivalent hfirst
  have hp' :
      Peano.Progressions.FiniteArithmetic.effectiveFirst (toPeano p) =
        some firstP.toPeano := by
    simpa [hp, Option.map] using (effectiveFirst_toPeano p).symm
  have hq' :
      Peano.Progressions.FiniteArithmetic.effectiveFirst (toPeano q) =
        some firstP.toPeano := by
    have hq0 :
        Peano.Progressions.FiniteArithmetic.effectiveFirst (toPeano q) =
          some firstQ.toPeano := by
      simpa [hq, Option.map] using (effectiveFirst_toPeano q).symm
    exact hq0.trans (congrArg some hfirstPeano.symm)
  have hlen' :
      Peano.Progressions.FiniteArithmetic.getLength (toPeano p) =
        Peano.Progressions.FiniteArithmetic.getLength (toPeano q) := by
    rw [← getLength_toPeano, ← getLength_toPeano]
    exact CardinalNatural.Decimal.toPeano_eq_of_equivalent hlen
  have hdiff :=
    Peano.Progressions.FiniteArithmetic.commonDifference_eq_of_equivalence_of_length_ge_two
      (toPeano p) (toPeano q) firstP.toPeano n hp' hq' hlenP hlen'
      ((equivalence_iff_toPeano p q).mp h)
  exact equivalent_of_toPeano_eq hdiff

/-- Equivalence of finite arithmetic progressions is decidable by comparing
lengths, effective first elements, and (when the length is at least two) common
differences — transferring the Peano decision procedure through `toPeano`. -/
instance (p q : FiniteArithmetic) : Decidable (p ≈ q) :=
  let lenP := getLength p
  if hL : lenP ≈ getLength q then
    if hZ : lenP ≈ CardinalNatural.Decimal.zero then
      isTrue (equivalence_of_length_zero p q hZ (Setoid.trans (Setoid.symm hL) hZ))
    else if hF : Option.Rel (· ≈ ·) (effectiveFirst p) (effectiveFirst q) then
      if hOne : lenP ≈ CardinalNatural.Decimal.one then
        match hf : effectiveFirst p with
        | none =>
          False.elim (hZ ((getLength_eq_zero_iff_effectiveFirst_none p).mpr hf))
        | some firstP =>
          match hq : effectiveFirst q with
          | none =>
            False.elim (by
              rw [hf, hq] at hF
              cases hF)
          | some firstQ =>
            isTrue (equivalence_of_length_one p q firstP firstQ hf hq
              (by
                rw [hf, hq] at hF
                exact Sequences.Progression.equivalent_of_option_rel_some hF)
              hOne (Setoid.trans (Setoid.symm hL) hOne))
      else if hD : p.commonDifference ≈ q.commonDifference then
        match hf : effectiveFirst p with
        | none =>
          False.elim (hZ ((getLength_eq_zero_iff_effectiveFirst_none p).mpr hf))
        | some firstP =>
          match hq : effectiveFirst q with
          | none =>
            False.elim (by
              rw [hf, hq] at hF
              cases hF)
          | some firstQ =>
            isTrue (equivalence_of_equivalent_params p q firstP firstQ hf hq
              (by
                rw [hf, hq] at hF
                exact Sequences.Progression.equivalent_of_option_rel_some hF)
              hD hL)
      else
        isFalse fun heq => by
          obtain ⟨firstP, hf⟩ := effectiveFirst_eq_some_of_positive_length p hZ
          have hrel := effectiveFirst_rel_of_equivalence p q heq
          simp only [hf] at hrel
          match hq : effectiveFirst q with
          | none =>
            rw [hq] at hrel
            cases hrel
          | some firstQ =>
            rw [hq] at hrel
            exact hD
              (commonDifference_equivalent_of_equivalence_of_length_ge_two
                p q firstP firstQ hf hq (Sequences.Progression.equivalent_of_option_rel_some hrel)
                hZ hOne hL heq)
    else
      isFalse fun heq => hF (effectiveFirst_rel_of_equivalence p q heq)
  else
    isFalse fun heq => hL (getLength_equivalent_of_equivalence p q heq)

/-- Elements from a known start for the given remaining length, advancing by the
common difference with no limit comparisons. -/
def getElementsFrom (first commonDifference : Decimal) :
    CardinalNatural.Decimal → Sequences.List Decimal
  | n =>
    if h : n ≈ CardinalNatural.Decimal.zero then
      .empty
    else
      .firstElement first
        (getElementsFrom (first + commonDifference) commonDifference
          (n.predecessor h))
termination_by n => n.toPeano
decreasing_by
  obtain ⟨hne, heq⟩ := CardinalNatural.Decimal.predecessor_toPeano n h
  rw [heq]
  exact CardinalNatural.Peano.sizeOf_predecessor_lt _ hne

/-- The ordered list of all elements of a finite arithmetic progression. Empty
when there is no in-range first element. Uses the effective first element and
`getLength`, then advances by repeated addition of the common difference —
avoiding a limit comparison at every step. -/
def getElements (p : FiniteArithmetic) : Sequences.List Decimal :=
  match effectiveFirst p with
  | none => .empty
  | some first =>
    getElementsFrom first p.commonDifference (getLength p)

/-- If `rest` continues an arithmetic progression after `prev` with common
difference `diff`, return the last element of that progression (which is `prev`
when `rest` is empty). Returns `none` when a consecutive pair does not advance
by a difference equivalent to `diff`. Integer subtraction is total, so each
step compares `x - prev` with `diff` (which may be positive or negative). -/
def tryLastOfArithmeticContinuation (prev diff : Decimal) :
    Sequences.List Decimal → Option Decimal
  | .empty => some prev
  | .firstElement x xs =>
    if x - prev ≈ diff then
      tryLastOfArithmeticContinuation x diff xs
    else
      none

/-- Reconstruct a finite arithmetic progression from the ordered list of all its
elements. Requires a proof that at least two elements are given. Returns `none`
when consecutive steps are not a constant nonzero common difference (compared
up to Decimal equivalence).

Uses the first element, the common difference between consecutive terms
(positive or negative), and the last element as the limit. -/
def tryFromElements :
    (elements : Sequences.List Decimal) →
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
    if hdiff : diff ≈ zero then
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
at `first` with common difference `commonDifference` (of either sign). Defined
via the Peano embedding so that length and order facts transport directly. For
`n ≈ zero` the value is unused (`fromPeano` of the Peano placeholder). -/
def lastElementFrom (first commonDifference : Decimal)
    (n : CardinalNatural.Decimal) : Decimal :=
  fromPeano
    (Peano.Progressions.FiniteArithmetic.lastElementFrom
      first.toPeano commonDifference.toPeano n.toPeano)

/-- `lastElementFrom` agrees with the Peano embedding on the nose. -/
theorem lastElementFrom_toPeano (first commonDifference : Decimal)
    (n : CardinalNatural.Decimal) :
    (lastElementFrom first commonDifference n).toPeano =
      Peano.Progressions.FiniteArithmetic.lastElementFrom
        first.toPeano commonDifference.toPeano n.toPeano :=
  toPeano_fromPeano _

/-- `getElementsFrom` produces a list whose length equals the Peano embedding of
the length argument. -/
theorem getElementsFrom_length (first commonDifference : Decimal)
    (n : CardinalNatural.Decimal) :
    (getElementsFrom first commonDifference n).length = n.toPeano := by
  have hgen :
      ∀ k : CardinalNatural.Peano, ∀ (first : Decimal) (n : CardinalNatural.Decimal),
        n.toPeano = k →
          (getElementsFrom first commonDifference n).length = k := by
    intro k
    induction k with
    | zero =>
      intro first n hn
      have hz : n ≈ CardinalNatural.Decimal.zero :=
        CardinalNatural.Decimal.equivalent_of_toPeano_eq
          (hn.trans CardinalNatural.Decimal.toPeano_zero.symm)
      have hexpand :
          getElementsFrom first commonDifference n = Sequences.List.empty := by
        conv => lhs; unfold getElementsFrom
        simp only [hz, ↓reduceDIte]
      rw [hexpand, Sequences.List.length]
    | successor k ih =>
      intro first n hn
      have hne0 : n.toPeano ≠ CardinalNatural.Peano.zero := by
        rw [hn]
        exact CardinalNatural.Peano.successor_ne_zero k
      have hne : ¬ n ≈ CardinalNatural.Decimal.zero :=
        CardinalNatural.Decimal.not_equivalent_zero_of_toPeano_ne_zero n hne0
      obtain ⟨hne_peano, hpred⟩ :=
        CardinalNatural.Decimal.predecessor_toPeano n hne
      have hpred_k : (n.predecessor hne).toPeano = k := by
        rw [hpred]
        apply Eq.symm
        apply CardinalNatural.Peano.successor_injective
        rw [CardinalNatural.Peano.successor_predecessor n.toPeano hne_peano, hn]
      have hexpand :
          getElementsFrom first commonDifference n =
            Sequences.List.firstElement first
              (getElementsFrom (first + commonDifference) commonDifference
                (n.predecessor hne)) := by
        conv => lhs; unfold getElementsFrom
        simp only [hne, ↓reduceDIte]
      rw [hexpand, Sequences.List.length_firstElement]
      have ih' := ih (first + commonDifference) (n.predecessor hne) hpred_k
      rw [ih']
  exact hgen n.toPeano first n rfl

theorem getElementsFrom_ge_two_length (first commonDifference : Decimal)
    (n : CardinalNatural.Decimal)
    (hge : CardinalNatural.Peano.two ≤ n.toPeano) :
    CardinalNatural.Peano.two ≤
      (getElementsFrom first commonDifference n).length := by
  rw [getElementsFrom_length]
  exact hge

/-- Expanding `getElementsFrom` at length at least two. -/
theorem getElementsFrom_of_two_le (first commonDifference : Decimal)
    (n : CardinalNatural.Decimal)
    (hge : CardinalNatural.Peano.two ≤ n.toPeano) :
    ∃ (hne : ¬ n ≈ CardinalNatural.Decimal.zero)
      (hne' : ¬ n.predecessor hne ≈ CardinalNatural.Decimal.zero),
      getElementsFrom first commonDifference n =
        Sequences.List.firstElement first
          (Sequences.List.firstElement (first + commonDifference)
            (getElementsFrom (first + commonDifference + commonDifference)
              commonDifference
              ((n.predecessor hne).predecessor hne'))) := by
  have hne0 : n.toPeano ≠ CardinalNatural.Peano.zero := by
    intro heq
    rw [heq] at hge
    exact CardinalNatural.Peano.not_two_le_zero hge
  have hne : ¬ n ≈ CardinalNatural.Decimal.zero :=
    CardinalNatural.Decimal.not_equivalent_zero_of_toPeano_ne_zero n hne0
  obtain ⟨hne_peano, hpred⟩ := CardinalNatural.Decimal.predecessor_toPeano n hne
  have hne1 : (n.predecessor hne).toPeano ≠ CardinalNatural.Peano.zero := by
    intro heq
    have hn_one : n.toPeano = CardinalNatural.Peano.one := by
      have hsucc :=
        CardinalNatural.Peano.successor_predecessor n.toPeano hne_peano
      rw [← hsucc, ← hpred, heq]
      rfl
    rw [hn_one] at hge
    exact CardinalNatural.Peano.not_two_le_one hge
  have hne' : ¬ n.predecessor hne ≈ CardinalNatural.Decimal.zero :=
    CardinalNatural.Decimal.not_equivalent_zero_of_toPeano_ne_zero _ hne1
  refine ⟨hne, hne', ?_⟩
  have hexpand1 :
      getElementsFrom first commonDifference n =
        Sequences.List.firstElement first
          (getElementsFrom (first + commonDifference) commonDifference
            (n.predecessor hne)) := by
    conv => lhs; unfold getElementsFrom
    simp only [hne, ↓reduceDIte]
  have hexpand2 :
      getElementsFrom (first + commonDifference) commonDifference
          (n.predecessor hne) =
        Sequences.List.firstElement (first + commonDifference)
          (getElementsFrom (first + commonDifference + commonDifference)
            commonDifference ((n.predecessor hne).predecessor hne')) := by
    conv => lhs; unfold getElementsFrom
    simp only [hne', ↓reduceDIte]
  rw [hexpand1, hexpand2]

/-- Continuing an arithmetic walk from `prev` by `getElementsFrom` recovers a
last element equivalent to `lastElementFrom`. -/
theorem tryLastOfArithmeticContinuation_getElementsFrom
    (prev commonDifference diff : Decimal) (n : CardinalNatural.Decimal)
    (hd : diff ≈ commonDifference) :
    Option.Rel (· ≈ ·)
      (tryLastOfArithmeticContinuation prev diff
        (getElementsFrom (prev + commonDifference) commonDifference n))
      (some (lastElementFrom prev commonDifference n.successor)) := by
  have hgen :
      ∀ k : CardinalNatural.Peano, ∀ (prev : Decimal) (n : CardinalNatural.Decimal),
        n.toPeano = k →
          Option.Rel (· ≈ ·)
            (tryLastOfArithmeticContinuation prev diff
              (getElementsFrom (prev + commonDifference) commonDifference n))
            (some (lastElementFrom prev commonDifference n.successor)) := by
    intro k
    induction k with
    | zero =>
      intro prev n hn
      have hz : n ≈ CardinalNatural.Decimal.zero :=
        CardinalNatural.Decimal.equivalent_of_toPeano_eq
          (hn.trans CardinalNatural.Decimal.toPeano_zero.symm)
      have hexpand :
          getElementsFrom (prev + commonDifference) commonDifference n =
            Sequences.List.empty := by
        conv => lhs; unfold getElementsFrom
        simp only [hz, ↓reduceDIte]
      rw [hexpand, tryLastOfArithmeticContinuation]
      apply Option.Rel.some
      apply equivalent_of_toPeano_eq
      rw [lastElementFrom_toPeano, CardinalNatural.Decimal.successor_toPeano, hn]
      change prev.toPeano =
        Peano.Progressions.FiniteArithmetic.lastElementFrom
          prev.toPeano commonDifference.toPeano
          (CardinalNatural.Peano.successor CardinalNatural.Peano.zero)
      rfl
    | successor k ih =>
      intro prev n hn
      have hne0 : n.toPeano ≠ CardinalNatural.Peano.zero := by
        rw [hn]
        exact CardinalNatural.Peano.successor_ne_zero k
      have hne : ¬ n ≈ CardinalNatural.Decimal.zero :=
        CardinalNatural.Decimal.not_equivalent_zero_of_toPeano_ne_zero n hne0
      obtain ⟨hne_peano, hpred⟩ :=
        CardinalNatural.Decimal.predecessor_toPeano n hne
      have hpred_k :=
        CardinalNatural.Decimal.predecessor_toPeano_eq_of_successor n hne k hn hne_peano hpred
      have hexpand :
          getElementsFrom (prev + commonDifference) commonDifference n =
            Sequences.List.firstElement (prev + commonDifference)
              (getElementsFrom (prev + commonDifference + commonDifference)
                commonDifference (n.predecessor hne)) := by
        conv => lhs; unfold getElementsFrom
        simp only [hne, ↓reduceDIte]
      rw [hexpand, tryLastOfArithmeticContinuation]
      have hstep : (prev + commonDifference) - prev ≈ diff :=
        Setoid.trans (add_subtract_cancel_left prev commonDifference) (Setoid.symm hd)
      simp only [hstep, ↓reduceIte]
      have ih' :=
        ih (prev + commonDifference) (n.predecessor hne) hpred_k
      obtain ⟨last', hlast_eq, hlast_approx⟩ :=
        Sequences.Progression.exists_of_option_rel_some ih'
      rw [hlast_eq]
      apply Option.Rel.some
      refine Setoid.trans hlast_approx ?_
      apply equivalent_of_toPeano_eq
      rw [lastElementFrom_toPeano, lastElementFrom_toPeano, add_toPeano,
        CardinalNatural.Decimal.successor_toPeano,
        CardinalNatural.Decimal.successor_toPeano, hpred_k, hn]
      exact
        (Peano.Progressions.FiniteArithmetic.lastElementFrom_successor_successor
          prev.toPeano commonDifference.toPeano k).symm
  exact hgen n.toPeano prev n rfl

/-- Reconstructing from `getElementsFrom` of Peano-length at least two recovers
a progression with the same start, an equivalent common difference, and a limit
equivalent to `lastElementFrom`. -/
theorem tryFromElements_getElementsFrom_ge_two (first commonDifference : Decimal)
    (hne : ¬ commonDifference ≈ zero) (n : CardinalNatural.Decimal)
    (hge : CardinalNatural.Peano.two ≤ n.toPeano)
    (hLen : CardinalNatural.Peano.two ≤
        (getElementsFrom first commonDifference n).length :=
      getElementsFrom_ge_two_length first commonDifference n hge) :
    ∃ (q : FiniteArithmetic),
      tryFromElements (getElementsFrom first commonDifference n) hLen = some q ∧
        q.first = some first ∧
        q.commonDifference ≈ commonDifference ∧
        q.limit ≈ lastElementFrom first commonDifference n := by
  obtain ⟨hne0, hne', hget⟩ := getElementsFrom_of_two_le first commonDifference n hge
  obtain ⟨hne_peano, hpred⟩ := CardinalNatural.Decimal.predecessor_toPeano n hne0
  obtain ⟨hne_peano', hpred'⟩ :=
    CardinalNatural.Decimal.predecessor_toPeano (n.predecessor hne0) hne'
  revert hLen
  rw [hget]
  intro hLen
  simp only [tryFromElements]
  have hdiff_approx : (first + commonDifference) - first ≈ commonDifference :=
    add_subtract_cancel_left first commonDifference
  have hdiff0 : ¬ (first + commonDifference) - first ≈ zero :=
    fun hz => hne (Setoid.trans (Setoid.symm hdiff_approx) hz)
  simp only [hdiff0, ↓reduceDIte]
  have hlast_rel :=
    tryLastOfArithmeticContinuation_getElementsFrom
      (first + commonDifference) commonDifference
      ((first + commonDifference) - first)
      ((n.predecessor hne0).predecessor hne') hdiff_approx
  obtain ⟨last, hlast_eq, hlast_approx⟩ :=
    Sequences.Progression.exists_of_option_rel_some hlast_rel
  simp only [hlast_eq]
  refine ⟨({
      first := some first
      commonDifference := (first + commonDifference) - first
      limit := last
      commonDifference_ne_zero := hdiff0
    } : FiniteArithmetic), rfl, rfl, hdiff_approx, ?_⟩
  refine Setoid.trans hlast_approx ?_
  apply equivalent_of_toPeano_eq
  rw [lastElementFrom_toPeano, lastElementFrom_toPeano, add_toPeano,
    CardinalNatural.Decimal.successor_toPeano]
  have hn_shape :
      n.toPeano =
        CardinalNatural.Peano.successor
          (CardinalNatural.Peano.successor
            ((n.predecessor hne0).predecessor hne').toPeano) := by
    have h1 :=
      CardinalNatural.Peano.successor_predecessor n.toPeano hne_peano
    have h2 :=
      CardinalNatural.Peano.successor_predecessor (n.predecessor hne0).toPeano
        hne_peano'
    rw [← h1]
    apply congrArg CardinalNatural.Peano.successor
    rw [← hpred]
    rw [← h2]
    apply congrArg CardinalNatural.Peano.successor
    exact hpred'.symm
  rw [hn_shape]
  exact
    (Peano.Progressions.FiniteArithmetic.lastElementFrom_successor_successor
      first.toPeano commonDifference.toPeano
      ((n.predecessor hne0).predecessor hne').toPeano).symm

/-- Length of a progression whose limit is equivalent to `lastElementFrom` of
its positive length, with an equivalent common difference. -/
theorem getLength_of_equivalent_lastElementFrom (first commonDifference diff last :
    Decimal) (n : CardinalNatural.Decimal)
    (hne : ¬ n ≈ CardinalNatural.Decimal.zero)
    (hdiff_ne : ¬ diff ≈ zero)
    (hd : diff ≈ commonDifference)
    (hl : last ≈ lastElementFrom first commonDifference n) :
    getLength {
      first := some first
      commonDifference := diff
      limit := last
      commonDifference_ne_zero := hdiff_ne
    } ≈ n := by
  apply CardinalNatural.Decimal.equivalent_of_toPeano_eq
  rw [getLength_toPeano]
  simp only [toPeano, Option.map]
  have hlim :
      last.toPeano =
        Peano.Progressions.FiniteArithmetic.lastElementFrom
          first.toPeano commonDifference.toPeano n.toPeano := by
    rw [toPeano_eq_of_equivalent hl, lastElementFrom_toPeano]
  have hdiff : diff.toPeano = commonDifference.toPeano :=
    toPeano_eq_of_equivalent hd
  simp [hlim, hdiff]
  exact
    Peano.Progressions.FiniteArithmetic.getLength_lastElementFrom
      first.toPeano commonDifference.toPeano
      (toPeano_ne_zero_of_not_equivalent_zero
        (fun hz => hdiff_ne (Setoid.trans hd hz)))
      n.toPeano
      (CardinalNatural.Decimal.toPeano_ne_zero_of_not_equivalent_zero hne)

/-- When the limit is equivalent to `lastElementFrom` of a positive length, the
effective first element is `some first`. -/
theorem effectiveFirst_of_equivalent_lastElementFrom (first commonDifference diff
    last : Decimal) (n : CardinalNatural.Decimal)
    (hne : ¬ n ≈ CardinalNatural.Decimal.zero)
    (hdiff_ne : ¬ diff ≈ zero)
    (hd : diff ≈ commonDifference)
    (hl : last ≈ lastElementFrom first commonDifference n) :
    effectiveFirst {
      first := some first
      commonDifference := diff
      limit := last
      commonDifference_ne_zero := hdiff_ne
    } = some first := by
  simp only [effectiveFirst, tryInclude]
  have hne_n :=
    CardinalNatural.Decimal.toPeano_ne_zero_of_not_equivalent_zero hne
  have hlast_peano :
      last.toPeano =
        Peano.Progressions.FiniteArithmetic.lastElementFrom
          first.toPeano commonDifference.toPeano n.toPeano := by
    rw [toPeano_eq_of_equivalent hl, lastElementFrom_toPeano]
  have hdiff_peano : diff.toPeano = commonDifference.toPeano :=
    toPeano_eq_of_equivalent hd
  match hsign : diff.toPeano with
  | .zero =>
    exact (toPeano_ne_zero_of_not_equivalent_zero hdiff_ne hsign).elim
  | .positive d =>
    have hpos : commonDifference.toPeano = Peano.positive d :=
      hdiff_peano.symm.trans hsign
    have hle_peano :
        first.toPeano ≤
          Peano.Progressions.FiniteArithmetic.lastElementFrom
            first.toPeano (Peano.positive d) n.toPeano :=
      Peano.Progressions.FiniteArithmetic.first_le_lastElementFrom_of_positive
        first.toPeano d n.toPeano hne_n
    have hle : first ≤ last := by
      apply (le_iff_toPeano_le first last).mpr
      rw [hlast_peano, hpos]
      exact hle_peano
    simp only [hle, ↓reduceIte]
  | .negative d =>
    have hneg : commonDifference.toPeano = Peano.negative d :=
      hdiff_peano.symm.trans hsign
    have hle_peano :
        Peano.Progressions.FiniteArithmetic.lastElementFrom
            first.toPeano (Peano.negative d) n.toPeano ≤
          first.toPeano :=
      Peano.Progressions.FiniteArithmetic.last_le_firstElementFrom_of_negative
        first.toPeano d n.toPeano hne_n
    have hle : last ≤ first := by
      apply (le_iff_toPeano_le last first).mpr
      rw [hlast_peano, hneg]
      exact hle_peano
    simp only [hle, ↓reduceIte]

/-- `tryFromElements` recovers a progression equivalent to `p` from
`getElements p` when `p` has length at least two. -/
theorem tryFromElements_getElements (p : FiniteArithmetic)
    (hge : CardinalNatural.Peano.two ≤ (getLength p).toPeano) :
    ∃ (hLen : CardinalNatural.Peano.two ≤ (getElements p).length)
      (q : FiniteArithmetic),
      tryFromElements (getElements p) hLen = some q ∧ p ≈ q := by
  have hne0 : (getLength p).toPeano ≠ CardinalNatural.Peano.zero := by
    intro heq
    rw [heq] at hge
    exact CardinalNatural.Peano.not_two_le_zero hge
  have hne0' : ¬ getLength p ≈ CardinalNatural.Decimal.zero :=
    CardinalNatural.Decimal.not_equivalent_zero_of_toPeano_ne_zero (getLength p) hne0
  obtain ⟨first, hf⟩ := effectiveFirst_eq_some_of_positive_length p hne0'
  have hget :
      getElements p =
        getElementsFrom first p.commonDifference (getLength p) := by
    simp only [getElements, hf]
  have hLen : CardinalNatural.Peano.two ≤ (getElements p).length := by
    rw [hget, getElementsFrom_length]
    exact hge
  have hLen' : CardinalNatural.Peano.two ≤
      (getElementsFrom first p.commonDifference (getLength p)).length := by
    rw [getElementsFrom_length]
    exact hge
  obtain ⟨q, htry, hfirst_q, hdiff_q, hlast_q⟩ :=
    tryFromElements_getElementsFrom_ge_two first p.commonDifference
      p.commonDifference_ne_zero (getLength p) hge hLen'
  refine ⟨hLen, q, ?_⟩
  constructor
  · revert hLen
    rw [hget]
    intro hLen
    exact htry
  · have hq_rewrite :
        q = {
          first := some first
          commonDifference := q.commonDifference
          limit := q.limit
          commonDifference_ne_zero := q.commonDifference_ne_zero
        } := by
      cases q with
      | mk f d l hne =>
        cases hfirst_q
        rfl
    have hf_q :
        effectiveFirst q = some first := by
      rw [hq_rewrite]
      exact effectiveFirst_of_equivalent_lastElementFrom first
        p.commonDifference q.commonDifference q.limit (getLength p) hne0'
        q.commonDifference_ne_zero hdiff_q hlast_q
    have hlen_q :
        getLength q ≈ getLength p := by
      rw [hq_rewrite]
      exact getLength_of_equivalent_lastElementFrom first p.commonDifference
        q.commonDifference q.limit (getLength p) hne0'
        q.commonDifference_ne_zero hdiff_q hlast_q
    exact equivalence_of_equivalent_params p q first first hf hf_q
      (Setoid.refl first) (Setoid.symm hdiff_q) (Setoid.symm hlen_q)

/-- `getElementsFrom` depends on the length argument only through its Peano
embedding. -/
theorem getElementsFrom_eq_of_toPeano_eq (first commonDifference : Decimal)
    (n m : CardinalNatural.Decimal) (h : n.toPeano = m.toPeano) :
    getElementsFrom first commonDifference n =
      getElementsFrom first commonDifference m := by
  have hgen :
      ∀ k : CardinalNatural.Peano, ∀ (first : Decimal)
        (n m : CardinalNatural.Decimal),
        n.toPeano = k → m.toPeano = k →
          getElementsFrom first commonDifference n =
            getElementsFrom first commonDifference m := by
    intro k
    induction k with
    | zero =>
      intro first n m hn hm
      have hnz : n ≈ CardinalNatural.Decimal.zero :=
        CardinalNatural.Decimal.equivalent_of_toPeano_eq
          (hn.trans CardinalNatural.Decimal.toPeano_zero.symm)
      have hmz : m ≈ CardinalNatural.Decimal.zero :=
        CardinalNatural.Decimal.equivalent_of_toPeano_eq
          (hm.trans CardinalNatural.Decimal.toPeano_zero.symm)
      have hn_empty :
          getElementsFrom first commonDifference n = Sequences.List.empty := by
        conv => lhs; unfold getElementsFrom
        simp only [hnz, ↓reduceDIte]
      have hm_empty :
          getElementsFrom first commonDifference m = Sequences.List.empty := by
        conv => lhs; unfold getElementsFrom
        simp only [hmz, ↓reduceDIte]
      rw [hn_empty, hm_empty]
    | successor k ih =>
      intro first n m hn hm
      have hne0 : n.toPeano ≠ CardinalNatural.Peano.zero := by
        rw [hn]
        exact CardinalNatural.Peano.successor_ne_zero k
      have hme0 : m.toPeano ≠ CardinalNatural.Peano.zero := by
        rw [hm]
        exact CardinalNatural.Peano.successor_ne_zero k
      have hne : ¬ n ≈ CardinalNatural.Decimal.zero :=
        CardinalNatural.Decimal.not_equivalent_zero_of_toPeano_ne_zero n hne0
      have hme : ¬ m ≈ CardinalNatural.Decimal.zero :=
        CardinalNatural.Decimal.not_equivalent_zero_of_toPeano_ne_zero m hme0
      obtain ⟨hne_peano, hpred_n⟩ :=
        CardinalNatural.Decimal.predecessor_toPeano n hne
      obtain ⟨hme_peano, hpred_m⟩ :=
        CardinalNatural.Decimal.predecessor_toPeano m hme
      have hpred_n_k : (n.predecessor hne).toPeano = k := by
        rw [hpred_n]
        apply Eq.symm
        apply CardinalNatural.Peano.successor_injective
        rw [CardinalNatural.Peano.successor_predecessor n.toPeano hne_peano, hn]
      have hpred_m_k : (m.predecessor hme).toPeano = k := by
        rw [hpred_m]
        apply Eq.symm
        apply CardinalNatural.Peano.successor_injective
        rw [CardinalNatural.Peano.successor_predecessor m.toPeano hme_peano, hm]
      have hn_expand :
          getElementsFrom first commonDifference n =
            Sequences.List.firstElement first
              (getElementsFrom (first + commonDifference) commonDifference
                (n.predecessor hne)) := by
        conv => lhs; unfold getElementsFrom
        simp only [hne, ↓reduceDIte]
      have hm_expand :
          getElementsFrom first commonDifference m =
            Sequences.List.firstElement first
              (getElementsFrom (first + commonDifference) commonDifference
                (m.predecessor hme)) := by
        conv => lhs; unfold getElementsFrom
        simp only [hme, ↓reduceDIte]
      rw [hn_expand, hm_expand]
      exact congrArg (Sequences.List.firstElement first)
        (ih (first + commonDifference) (n.predecessor hne) (m.predecessor hme)
          hpred_n_k hpred_m_k)
  exact hgen n.toPeano first n m rfl h.symm

/-- Equivalent starting points yield pointwise-equivalent `getElementsFrom`
walks of the same length. -/
theorem getElementsFrom_rel_of_equivalent_first (first first' commonDifference :
    Decimal) (n : CardinalNatural.Decimal) (h : first ≈ first') :
    Sequences.List.SameLengthElementwiseRelation (· ≈ ·)
      (getElementsFrom first commonDifference n)
      (getElementsFrom first' commonDifference n) := by
  have hgen :
      ∀ k : CardinalNatural.Peano, ∀ (first first' : Decimal)
        (n : CardinalNatural.Decimal),
        n.toPeano = k → first ≈ first' →
          Sequences.List.SameLengthElementwiseRelation (· ≈ ·)
            (getElementsFrom first commonDifference n)
            (getElementsFrom first' commonDifference n) := by
    intro k
    induction k with
    | zero =>
      intro first first' n hn _hfirst
      have hz : n ≈ CardinalNatural.Decimal.zero :=
        CardinalNatural.Decimal.equivalent_of_toPeano_eq
          (hn.trans CardinalNatural.Decimal.toPeano_zero.symm)
      have hexpand :
          getElementsFrom first commonDifference n = Sequences.List.empty := by
        conv => lhs; unfold getElementsFrom
        simp only [hz, ↓reduceDIte]
      have hexpand' :
          getElementsFrom first' commonDifference n = Sequences.List.empty := by
        conv => lhs; unfold getElementsFrom
        simp only [hz, ↓reduceDIte]
      rw [hexpand, hexpand']
      exact Sequences.List.SameLengthElementwiseRelation.empty
    | successor k ih =>
      intro first first' n hn hfirst
      have hne0 : n.toPeano ≠ CardinalNatural.Peano.zero := by
        rw [hn]
        exact CardinalNatural.Peano.successor_ne_zero k
      have hne : ¬ n ≈ CardinalNatural.Decimal.zero :=
        CardinalNatural.Decimal.not_equivalent_zero_of_toPeano_ne_zero n hne0
      obtain ⟨hne_peano, hpred⟩ :=
        CardinalNatural.Decimal.predecessor_toPeano n hne
      have hpred_k : (n.predecessor hne).toPeano = k := by
        rw [hpred]
        apply Eq.symm
        apply CardinalNatural.Peano.successor_injective
        rw [CardinalNatural.Peano.successor_predecessor n.toPeano hne_peano, hn]
      have hexpand :
          getElementsFrom first commonDifference n =
            Sequences.List.firstElement first
              (getElementsFrom (first + commonDifference) commonDifference
                (n.predecessor hne)) := by
        conv => lhs; unfold getElementsFrom
        simp only [hne, ↓reduceDIte]
      have hexpand' :
          getElementsFrom first' commonDifference n =
            Sequences.List.firstElement first'
              (getElementsFrom (first' + commonDifference) commonDifference
                (n.predecessor hne)) := by
        conv => lhs; unfold getElementsFrom
        simp only [hne, ↓reduceDIte]
      rw [hexpand, hexpand']
      exact Sequences.List.SameLengthElementwiseRelation.firstElement hfirst
        (ih (first + commonDifference) (first' + commonDifference)
          (n.predecessor hne) hpred_k
          (equivalent_add hfirst (Setoid.refl commonDifference)))
  exact hgen n.toPeano first first' n rfl h

/-- Expanding `getElementsFrom` at a positive Peano length. -/
theorem getElementsFrom_of_toPeano_successor (first commonDifference : Decimal)
    (n : CardinalNatural.Decimal) (k : CardinalNatural.Peano)
    (hn : n.toPeano = CardinalNatural.Peano.successor k) :
    ∃ (hne : ¬ n ≈ CardinalNatural.Decimal.zero),
      getElementsFrom first commonDifference n =
        Sequences.List.firstElement first
          (getElementsFrom (first + commonDifference) commonDifference
            (n.predecessor hne)) ∧
      (n.predecessor hne).toPeano = k := by
  have hne0 : n.toPeano ≠ CardinalNatural.Peano.zero := by
    rw [hn]
    exact CardinalNatural.Peano.successor_ne_zero k
  have hne : ¬ n ≈ CardinalNatural.Decimal.zero :=
    CardinalNatural.Decimal.not_equivalent_zero_of_toPeano_ne_zero n hne0
  obtain ⟨hne_peano, hpred⟩ := CardinalNatural.Decimal.predecessor_toPeano n hne
  refine ⟨hne, ?_, ?_⟩
  · conv => lhs; unfold getElementsFrom
    simp only [hne, ↓reduceDIte]
  · rw [hpred]
    apply Eq.symm
    apply CardinalNatural.Peano.successor_injective
    rw [CardinalNatural.Peano.successor_predecessor n.toPeano hne_peano, hn]

/-- If a list continues arithmetically after `prev`, it is pointwise equivalent
to the corresponding `getElementsFrom` walk, and the recovered last element is
equivalent to `lastElementFrom`. -/
theorem rel_getElementsFrom_of_tryLastOfArithmeticContinuation
    (prev diff : Decimal) (rest : Sequences.List Decimal) (last : Decimal)
    (h : tryLastOfArithmeticContinuation prev diff rest = some last) :
    Sequences.List.SameLengthElementwiseRelation (· ≈ ·)
        (getElementsFrom (prev + diff) diff
          (CardinalNatural.Decimal.fromPeano rest.length))
        rest ∧
      last ≈
        lastElementFrom prev diff
          (CardinalNatural.Decimal.fromPeano rest.length).successor := by
  induction rest generalizing prev last with
  | empty =>
    simp only [tryLastOfArithmeticContinuation] at h
    injection h with heq
    constructor
    · have hz :
          CardinalNatural.Decimal.fromPeano
              CardinalNatural.Peano.zero ≈
            CardinalNatural.Decimal.zero :=
        CardinalNatural.Decimal.equivalent_of_toPeano_eq
          ((CardinalNatural.Decimal.toPeano_fromPeano
              CardinalNatural.Peano.zero).trans
            CardinalNatural.Decimal.toPeano_zero.symm)
      have hexpand :
          getElementsFrom (prev + diff) diff
              (CardinalNatural.Decimal.fromPeano CardinalNatural.Peano.zero) =
            Sequences.List.empty := by
        conv => lhs; unfold getElementsFrom
        simp only [hz, ↓reduceDIte]
      change Sequences.List.SameLengthElementwiseRelation (· ≈ ·)
        (getElementsFrom (prev + diff) diff
          (CardinalNatural.Decimal.fromPeano
            (Sequences.List.empty : Sequences.List Decimal).length))
        Sequences.List.empty
      rw [show (Sequences.List.empty : Sequences.List Decimal).length =
          CardinalNatural.Peano.zero from rfl, hexpand]
      exact Sequences.List.SameLengthElementwiseRelation.empty
    · subst heq
      apply equivalent_of_toPeano_eq
      rw [lastElementFrom_toPeano, CardinalNatural.Decimal.successor_toPeano,
        CardinalNatural.Decimal.toPeano_fromPeano]
      change prev.toPeano =
        Peano.Progressions.FiniteArithmetic.lastElementFrom
          prev.toPeano diff.toPeano CardinalNatural.Peano.one
      rfl
  | firstElement x xs ih =>
    simp only [tryLastOfArithmeticContinuation] at h
    by_cases hd : x - prev ≈ diff
    · rw [show (if x - prev ≈ diff then
            tryLastOfArithmeticContinuation x diff xs
          else none) =
          tryLastOfArithmeticContinuation x diff xs from by
            simp only [hd, ↓reduceIte]] at h
      obtain ⟨hxs, hlast⟩ := ih x last h
      have hx : x ≈ prev + diff := equivalent_add_of_subtract x prev diff hd
      have hlen := Sequences.List.length_firstElement x xs
      constructor
      · have hn :
            (CardinalNatural.Decimal.fromPeano
                (Sequences.List.firstElement x xs).length).toPeano =
              CardinalNatural.Peano.successor xs.length := by
          rw [CardinalNatural.Decimal.toPeano_fromPeano, hlen]
        obtain ⟨hne, hexpand, hpred⟩ :=
          getElementsFrom_of_toPeano_successor (prev + diff) diff
            (CardinalNatural.Decimal.fromPeano
              (Sequences.List.firstElement x xs).length)
            xs.length hn
        have hpred_eq :
            getElementsFrom (prev + diff + diff) diff
                ((CardinalNatural.Decimal.fromPeano
                    (Sequences.List.firstElement x xs).length).predecessor
                  hne) =
              getElementsFrom (prev + diff + diff) diff
                (CardinalNatural.Decimal.fromPeano xs.length) :=
          getElementsFrom_eq_of_toPeano_eq (prev + diff + diff) diff _ _
            (hpred.trans (CardinalNatural.Decimal.toPeano_fromPeano _).symm)
        have hstart : prev + diff + diff ≈ x + diff :=
          equivalent_add (Setoid.symm hx) (Setoid.refl diff)
        have hmid :
            Sequences.List.SameLengthElementwiseRelation (· ≈ ·)
              (getElementsFrom (prev + diff + diff) diff
                (CardinalNatural.Decimal.fromPeano xs.length))
              (getElementsFrom (x + diff) diff
                (CardinalNatural.Decimal.fromPeano xs.length)) :=
          getElementsFrom_rel_of_equivalent_first (prev + diff + diff)
            (x + diff) diff (CardinalNatural.Decimal.fromPeano xs.length)
            hstart
        have htail :
            Sequences.List.SameLengthElementwiseRelation (· ≈ ·)
              (getElementsFrom (prev + diff + diff) diff
                (CardinalNatural.Decimal.fromPeano xs.length))
              xs :=
          Sequences.List.SameLengthElementwiseRelation.trans
            (r := (· ≈ ·)) (s := (· ≈ ·)) (t := (· ≈ ·))
            (fun h1 h2 => Setoid.trans h1 h2) hmid hxs
        rw [hexpand, hpred_eq]
        exact Sequences.List.SameLengthElementwiseRelation.firstElement
          (Setoid.symm hx) htail
      · have h1 :
            last ≈
              lastElementFrom (prev + diff) diff
                (CardinalNatural.Decimal.fromPeano xs.length).successor := by
          refine Setoid.trans hlast ?_
          apply equivalent_of_toPeano_eq
          rw [lastElementFrom_toPeano, lastElementFrom_toPeano,
            toPeano_eq_of_equivalent hx]
        have h2 :
            lastElementFrom (prev + diff) diff
                (CardinalNatural.Decimal.fromPeano xs.length).successor ≈
              lastElementFrom prev diff
                (CardinalNatural.Decimal.fromPeano
                  (Sequences.List.firstElement x xs).length).successor := by
          apply equivalent_of_toPeano_eq
          rw [lastElementFrom_toPeano, lastElementFrom_toPeano, add_toPeano,
            CardinalNatural.Decimal.successor_toPeano,
            CardinalNatural.Decimal.successor_toPeano,
            CardinalNatural.Decimal.toPeano_fromPeano,
            CardinalNatural.Decimal.toPeano_fromPeano, hlen]
          exact
            (Peano.Progressions.FiniteArithmetic.lastElementFrom_successor_successor
              prev.toPeano diff.toPeano xs.length).symm
        exact Setoid.trans h1 h2
    · simp only [hd, ↓reduceIte] at h
      nomatch h

/-- `getElements` recovers a list pointwise equivalent to the original from a
successful `tryFromElements`. Exact equality may fail because Decimal
subtraction recovers steps only up to representation. -/
theorem getElements_tryFromElements (elements : Sequences.List Decimal)
    (hge : CardinalNatural.Peano.two ≤ elements.length)
    (p : FiniteArithmetic)
    (h : tryFromElements elements hge = some p) :
    Sequences.List.SameLengthElementwiseRelation (· ≈ ·) (getElements p) elements := by
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
    by_cases hdiff0 : y - x ≈ zero
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
          simp only [tryLastOfArithmeticContinuation]
          have hdrefl : y - x ≈ y - x := Setoid.refl _
          simp only [hdrefl, ↓reduceIte, hl]
        obtain ⟨hrest, hlast⟩ :=
          rel_getElementsFrom_of_tryLastOfArithmeticContinuation x (y - x)
            (Sequences.List.firstElement y ys) last hcont
        let n : CardinalNatural.Decimal :=
          (CardinalNatural.Decimal.fromPeano
            (Sequences.List.firstElement y ys).length).successor
        have hne : ¬ n ≈ CardinalNatural.Decimal.zero := by
          intro heq
          have hpeano := CardinalNatural.Decimal.toPeano_eq_of_equivalent heq
          rw [CardinalNatural.Decimal.successor_toPeano,
            CardinalNatural.Decimal.toPeano_fromPeano,
            CardinalNatural.Decimal.toPeano_zero] at hpeano
          exact CardinalNatural.Peano.successor_ne_zero _ hpeano
        have hf : effectiveFirst
            {
              first := some x
              commonDifference := y - x
              limit := last
              commonDifference_ne_zero := hdiff0
            } = some x :=
          effectiveFirst_of_equivalent_lastElementFrom x (y - x) (y - x) last n
            hne hdiff0 (Setoid.refl _) hlast
        have hlenp :
            getLength
                {
                  first := some x
                  commonDifference := y - x
                  limit := last
                  commonDifference_ne_zero := hdiff0
                } ≈ n :=
          getLength_of_equivalent_lastElementFrom x (y - x) (y - x) last n hne
            hdiff0 (Setoid.refl _) hlast
        have hget :
            getElements
                {
                  first := some x
                  commonDifference := y - x
                  limit := last
                  commonDifference_ne_zero := hdiff0
                } =
              getElementsFrom x (y - x)
                (getLength
                  {
                    first := some x
                    commonDifference := y - x
                    limit := last
                    commonDifference_ne_zero := hdiff0
                  }) := by
          simp only [getElements, hf]
        rw [hget]
        have hlen_toPeano :
            (getLength
                {
                  first := some x
                  commonDifference := y - x
                  limit := last
                  commonDifference_ne_zero := hdiff0
                }).toPeano =
              n.toPeano :=
          CardinalNatural.Decimal.toPeano_eq_of_equivalent hlenp
        have hget' :
            getElementsFrom x (y - x)
                (getLength
                  {
                    first := some x
                    commonDifference := y - x
                    limit := last
                    commonDifference_ne_zero := hdiff0
                  }) =
              getElementsFrom x (y - x) n :=
          getElementsFrom_eq_of_toPeano_eq x (y - x) _ _ hlen_toPeano
        rw [hget']
        have hn :
            n.toPeano =
              CardinalNatural.Peano.successor
                (Sequences.List.firstElement y ys).length := by
          rw [CardinalNatural.Decimal.successor_toPeano,
            CardinalNatural.Decimal.toPeano_fromPeano]
        obtain ⟨hne_n, hexpand, hpred⟩ :=
          getElementsFrom_of_toPeano_successor x (y - x) n
            (Sequences.List.firstElement y ys).length hn
        have hpred_eq :
            getElementsFrom (x + (y - x)) (y - x) (n.predecessor hne_n) =
              getElementsFrom (x + (y - x)) (y - x)
                (CardinalNatural.Decimal.fromPeano
                  (Sequences.List.firstElement y ys).length) :=
          getElementsFrom_eq_of_toPeano_eq (x + (y - x)) (y - x) _ _
            (hpred.trans (CardinalNatural.Decimal.toPeano_fromPeano _).symm)
        rw [hexpand, hpred_eq]
        exact Sequences.List.SameLengthElementwiseRelation.firstElement
          (Setoid.refl x) hrest

/-- Recover the first element of an arithmetic progression from an element at the
given ordinal Decimal index and the common difference by subtracting
`(fromOrdinalNaturalPeano index - one) * commonDifference`. Integer subtraction is
total, so this always succeeds. -/
def tryFirstFromIndexedElement
    (index : OrdinalNatural.Decimal) (element commonDifference : Decimal) :
    Option Decimal :=
  InfiniteArithmetic.tryFirstFromIndexedElement index element commonDifference

/-- Given two ordered indexed elements (`index < index'`) of a prospective
finite arithmetic progression, recover the common difference
`(element' - element) / (index' - index)`. Returns `none` when the element gap
is not divisible by the index gap. Unlike the natural-number increasing
versions, the element difference may be negative, so the recovered common
difference may be negative as well. -/
def tryCommonDifferenceFromOrderedIndexedElements
    (index : OrdinalNatural.Decimal) (element : Decimal)
    (index' : OrdinalNatural.Decimal) (element' : Decimal)
    (hlt : index < index') :
    Option Decimal :=
  InfiniteArithmetic.tryCommonDifferenceFromOrderedIndexedElements
    index element index' element' hlt

/-- Reconstruct a finite arithmetic progression from two of its elements at
different ordinal Decimal indexes together with the progression length. Returns
`none` when either index exceeds the length, when the recovered common
difference is equivalent to zero, or when the values are not consistent with an
arithmetic progression of that length (element gap not divisible by the index
gap). Indexes are compared up to Decimal equivalence.

The reconstructed progression uses the recovered first element and common
difference (of either sign), and takes the last element of an arithmetic walk
of the given length as the limit. -/
def tryFromTwoElementsAndLength
    (index1 : OrdinalNatural.Decimal) (element1 : Decimal)
    (index2 : OrdinalNatural.Decimal) (element2 : Decimal)
    (length : CardinalNatural.Decimal)
    (hne : ¬ index1 ≈ index2) :
    Option FiniteArithmetic :=
  if CardinalNatural.Decimal.fromOrdinal index1 ≤ length then
    if CardinalNatural.Decimal.fromOrdinal index2 ≤ length then
      match OrdinalNatural.Decimal.compare index1 index2 with
      | .equivalent heq => False.elim (hne heq)
      | .less hlt =>
        match tryCommonDifferenceFromOrderedIndexedElements
            index1 element1 index2 element2 hlt with
        | none => none
        | some diff =>
          if hdiff : diff ≈ zero then
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
          if hdiff : diff ≈ zero then
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

/-- Recovering the first element from an indexed element is left-inverse to
`getElementFrom` at that index, up to Decimal equivalence. -/
theorem getElementFrom_of_tryFirstFromIndexedElement
    (index : OrdinalNatural.Decimal) (element commonDifference first : Decimal)
    (h : tryFirstFromIndexedElement index element commonDifference = some first) :
    getElementFrom first commonDifference index ≈ element := by
  simp only [tryFirstFromIndexedElement, getElementFrom] at h ⊢
  exact InfiniteArithmetic.getElement_of_tryFirstFromIndexedElement
    index element commonDifference first h

/-- Advancing from `index` to a larger `index'` adds
`(fromOrdinalNaturalPeano (index' - index)) * commonDifference` to the element, up
to Decimal equivalence. -/
theorem getElementFrom_add_multiply_of_lt (first commonDifference : Decimal)
    (index index' : OrdinalNatural.Decimal)
    (hlt : index < index') :
    getElementFrom first commonDifference index' ≈
      getElementFrom first commonDifference index +
        (fromOrdinalNaturalPeano
          (OrdinalNatural.Decimal.subtract index' index hlt).toPeano) *
          commonDifference := by
  rw [getElementFrom_eq_InfiniteArithmetic_getElement,
    getElementFrom_eq_InfiniteArithmetic_getElement]
  exact InfiniteArithmetic.getElement_add_multiply_of_lt
    { first := first, commonDifference := commonDifference } index index' hlt

/-- A successful common-difference recovery implies the larger element is
equivalent to the smaller plus the index gap times that difference. -/
theorem eq_add_multiply_of_tryCommonDifferenceFromOrderedIndexedElements
    (index : OrdinalNatural.Decimal) (element : Decimal)
    (index' : OrdinalNatural.Decimal) (element' : Decimal)
    (hlt : index < index')
    (diff : Decimal)
    (h : tryCommonDifferenceFromOrderedIndexedElements
        index element index' element' hlt = some diff) :
    element' ≈
      element +
        (fromOrdinalNaturalPeano
          (OrdinalNatural.Decimal.subtract index' index hlt).toPeano) *
          diff := by
  simp only [tryCommonDifferenceFromOrderedIndexedElements] at h
  exact InfiniteArithmetic.eq_add_multiply_of_tryCommonDifferenceFromOrderedIndexedElements
    index element index' element' hlt diff h

/-- When both indexed recoveries succeed, `getElementFrom` recovers each original
element up to Decimal equivalence. -/
theorem getElementFrom_of_tryFirst_tryCommonDifference
    (index : OrdinalNatural.Decimal) (element : Decimal)
    (index' : OrdinalNatural.Decimal) (element' : Decimal)
    (hlt : index < index')
    (diff first : Decimal)
    (hdiff : tryCommonDifferenceFromOrderedIndexedElements
        index element index' element' hlt = some diff)
    (hfirst : tryFirstFromIndexedElement index element diff = some first) :
    getElementFrom first diff index ≈ element ∧
      getElementFrom first diff index' ≈ element' := by
  have h1 :=
    getElementFrom_of_tryFirstFromIndexedElement index element diff first hfirst
  refine ⟨h1, ?_⟩
  have hgap :=
    eq_add_multiply_of_tryCommonDifferenceFromOrderedIndexedElements
      index element index' element' hlt diff hdiff
  exact
    Setoid.trans
      (Setoid.trans
        (getElementFrom_add_multiply_of_lt first diff index index' hlt)
        (equivalent_add_right h1))
      (Setoid.symm hgap)

/-- Length of a progression whose limit is exactly `lastElementFrom` of its
positive length. -/
theorem getLength_lastElementFrom (first commonDifference : Decimal)
    (hdiff : ¬ commonDifference ≈ zero) (n : CardinalNatural.Decimal)
    (hne : ¬ n ≈ CardinalNatural.Decimal.zero) :
    getLength {
      first := some first
      commonDifference := commonDifference
      limit := lastElementFrom first commonDifference n
      commonDifference_ne_zero := hdiff
    } ≈ n :=
  getLength_of_equivalent_lastElementFrom first commonDifference
    commonDifference (lastElementFrom first commonDifference n) n hne
    hdiff (Setoid.refl _) (Setoid.refl _)

/-- In-range `getElement` agrees with `getElementFrom` on the effective first. -/
theorem getElement_eq_getElementFrom (p : FiniteArithmetic)
    (first : Decimal) (hf : effectiveFirst p = some first)
    (index : OrdinalNatural.Decimal)
    (hle : CardinalNatural.Decimal.fromOrdinal index ≤ getLength p) :
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

/-- `getElement` on a progression whose limit is `lastElementFrom` of positive
length agrees with `getElementFrom`. -/
theorem getElement_lastElementFrom (first commonDifference : Decimal)
    (hdiff : ¬ commonDifference ≈ zero) (n : CardinalNatural.Decimal)
    (hne : ¬ n ≈ CardinalNatural.Decimal.zero)
    (index : OrdinalNatural.Decimal)
    (hle : CardinalNatural.Decimal.fromOrdinal index ≤
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
      effectiveFirst
        {
          first := some first
          commonDifference := commonDifference
          limit := lastElementFrom first commonDifference n
          commonDifference_ne_zero := hdiff
        } =
        some first :=
    effectiveFirst_of_equivalent_lastElementFrom first commonDifference
      commonDifference (lastElementFrom first commonDifference n) n hne
      hdiff (Setoid.refl _) (Setoid.refl _)
  exact getElement_eq_getElementFrom _ first hfirst index hle

theorem length_ne_zero_of_tryFromTwoElementsAndLength
    (index1 : OrdinalNatural.Decimal) (element1 : Decimal)
    (index2 : OrdinalNatural.Decimal) (element2 : Decimal)
    (length : CardinalNatural.Decimal)
    (hne : ¬ index1 ≈ index2)
    (p : FiniteArithmetic)
    (h : tryFromTwoElementsAndLength index1 element1 index2 element2 length hne =
      some p) :
    ¬ length ≈ CardinalNatural.Decimal.zero := by
  intro hzero
  simp only [tryFromTwoElementsAndLength] at h
  by_cases hle1 : CardinalNatural.Decimal.fromOrdinal index1 ≤ length
  · have :
        CardinalNatural.Decimal.fromOrdinal index1 ≤
          CardinalNatural.Decimal.zero :=
      CardinalNatural.Decimal.le_of_le_of_equivalent hle1 hzero
    exact CardinalNatural.Decimal.fromOrdinal_not_equivalent_zero index1
      (CardinalNatural.Decimal.eq_zero_of_le_zero _ this)
  · simp only [hle1, ↓reduceIte] at h
    nomatch h

/-- A successful `tryFromTwoElementsAndLength` yields a progression whose
`getLength` is equivalent to the given length and whose `getElement` at each of
the two indexes recovers a value equivalent to the corresponding original
element. -/
theorem getLength_getElement_of_tryFromTwoElementsAndLength
    (index1 : OrdinalNatural.Decimal) (element1 : Decimal)
    (index2 : OrdinalNatural.Decimal) (element2 : Decimal)
    (length : CardinalNatural.Decimal)
    (hne : ¬ index1 ≈ index2)
    (p : FiniteArithmetic)
    (h : tryFromTwoElementsAndLength index1 element1 index2 element2 length hne =
      some p) :
    getLength p ≈ length ∧
      (∃ (hle1 : CardinalNatural.Decimal.fromOrdinal index1 ≤ getLength p),
        getElement p index1 hle1 ≈ element1) ∧
      (∃ (hle2 : CardinalNatural.Decimal.fromOrdinal index2 ≤ getLength p),
        getElement p index2 hle2 ≈ element2) := by
  have hlen_ne :=
    length_ne_zero_of_tryFromTwoElementsAndLength
      index1 element1 index2 element2 length hne p h
  simp only [tryFromTwoElementsAndLength] at h
  by_cases hle1 : CardinalNatural.Decimal.fromOrdinal index1 ≤ length
  · simp only [hle1, ↓reduceIte] at h
    by_cases hle2 : CardinalNatural.Decimal.fromOrdinal index2 ≤ length
    · simp only [hle2, ↓reduceIte] at h
      match hc : OrdinalNatural.Decimal.compare index1 index2 with
      | .equivalent heq =>
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
          by_cases hdiff0 : diff ≈ zero
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
                  CardinalNatural.Decimal.fromOrdinal index1 ≤
                    getLength {
                      first := some first
                      commonDifference := diff
                      limit := lastElementFrom first diff length
                      commonDifference_ne_zero := hdiff0
                    } :=
                CardinalNatural.Decimal.le_of_le_of_equivalent hle1
                  (Setoid.symm hlenp)
              have hle2p :
                  CardinalNatural.Decimal.fromOrdinal index2 ≤
                    getLength {
                      first := some first
                      commonDifference := diff
                      limit := lastElementFrom first diff length
                      commonDifference_ne_zero := hdiff0
                    } :=
                CardinalNatural.Decimal.le_of_le_of_equivalent hle2
                  (Setoid.symm hlenp)
              refine ⟨hlenp, ⟨hle1p, ?_⟩, ⟨hle2p, ?_⟩⟩
              · exact
                  (getElement_lastElementFrom first diff hdiff0 length hlen_ne
                    index1 hle1p) ▸ hget.1
              · exact
                  (getElement_lastElementFrom first diff hdiff0 length hlen_ne
                    index2 hle2p) ▸ hget.2
      | .greater hgt =>
        simp only [hc] at h
        match hd : tryCommonDifferenceFromOrderedIndexedElements
            index2 element2 index1 element1 hgt with
        | none =>
          simp only [hd] at h
          nomatch h
        | some diff =>
          simp only [hd] at h
          by_cases hdiff0 : diff ≈ zero
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
                  CardinalNatural.Decimal.fromOrdinal index1 ≤
                    getLength {
                      first := some first
                      commonDifference := diff
                      limit := lastElementFrom first diff length
                      commonDifference_ne_zero := hdiff0
                    } :=
                CardinalNatural.Decimal.le_of_le_of_equivalent hle1
                  (Setoid.symm hlenp)
              have hle2p :
                  CardinalNatural.Decimal.fromOrdinal index2 ≤
                    getLength {
                      first := some first
                      commonDifference := diff
                      limit := lastElementFrom first diff length
                      commonDifference_ne_zero := hdiff0
                    } :=
                CardinalNatural.Decimal.le_of_le_of_equivalent hle2
                  (Setoid.symm hlenp)
              refine ⟨hlenp, ⟨hle1p, ?_⟩, ⟨hle2p, ?_⟩⟩
              · exact
                  (getElement_lastElementFrom first diff hdiff0 length hlen_ne
                    index1 hle1p) ▸ hget.2
              · exact
                  (getElement_lastElementFrom first diff hdiff0 length hlen_ne
                    index2 hle2p) ▸ hget.1
    · simp only [hle2, ↓reduceIte] at h
      nomatch h
  · simp only [hle1, ↓reduceIte] at h
    nomatch h

/-- Recovering the common difference from two indexed elements of an arithmetic
walk returns a value equivalent to the walk's common difference. -/
theorem tryCommonDifferenceFromOrderedIndexedElements_getElementFrom
    (first commonDifference : Decimal)
    (index index' : OrdinalNatural.Decimal) (hlt : index < index') :
    ∃ d,
      tryCommonDifferenceFromOrderedIndexedElements
        index (getElementFrom first commonDifference index)
        index' (getElementFrom first commonDifference index') hlt = some d ∧
      d ≈ commonDifference := by
  simp only [tryCommonDifferenceFromOrderedIndexedElements, getElementFrom]
  exact InfiniteArithmetic.tryCommonDifferenceFromOrderedIndexedElements_getElement
    { first := first, commonDifference := commonDifference } index index' hlt

/-- Recovering the first element from an indexed element of an arithmetic walk,
using a common difference equivalent to the walk's, returns a value equivalent
to that walk's start. -/
theorem tryFirstFromIndexedElement_getElementFrom_of_equivalent_diff
    (first commonDifference : Decimal) (index : OrdinalNatural.Decimal)
    (d : Decimal) (hd : d ≈ commonDifference) :
    ∃ first',
      tryFirstFromIndexedElement index
        (getElementFrom first commonDifference index) d = some first' ∧
      first' ≈ first := by
  simp only [tryFirstFromIndexedElement, getElementFrom]
  exact InfiniteArithmetic.tryFirstFromIndexedElement_getElement_of_equivalent_diff
    { first := first, commonDifference := commonDifference } index d hd

/-- Reconstructing from any two inequivalent in-range elements of `p`, together
with `getLength p`, yields a progression equivalent to `p`. -/
theorem tryFromTwoElementsAndLength_getElement
    (p : FiniteArithmetic)
    (index1 index2 : OrdinalNatural.Decimal)
    (hne : ¬ index1 ≈ index2)
    (hle1 : CardinalNatural.Decimal.fromOrdinal index1 ≤ getLength p)
    (hle2 : CardinalNatural.Decimal.fromOrdinal index2 ≤ getLength p) :
    ∃ (q : FiniteArithmetic),
      tryFromTwoElementsAndLength
        index1 (getElement p index1 hle1)
        index2 (getElement p index2 hle2)
        (getLength p) hne = some q ∧
      p ≈ q := by
  have hne0 : ¬ getLength p ≈ CardinalNatural.Decimal.zero := by
    intro hzero
    have :
        CardinalNatural.Decimal.fromOrdinal index1 ≤
          CardinalNatural.Decimal.zero :=
      CardinalNatural.Decimal.le_of_le_of_equivalent hle1 hzero
    exact CardinalNatural.Decimal.fromOrdinal_not_equivalent_zero index1
      (CardinalNatural.Decimal.eq_zero_of_le_zero _ this)
  obtain ⟨first, hf⟩ := effectiveFirst_eq_some_of_positive_length p hne0
  have hget1 := getElement_eq_getElementFrom p first hf index1 hle1
  have hget2 := getElement_eq_getElementFrom p first hf index2 hle2
  match hcomp : OrdinalNatural.Decimal.compare index1 index2 with
  | .equivalent heq =>
    exact (hne heq).elim
  | .less hlt =>
    obtain ⟨diff, hdiff_eq, hdiff_approx⟩ :=
      tryCommonDifferenceFromOrderedIndexedElements_getElementFrom
        first p.commonDifference index1 index2 hlt
    obtain ⟨first', hfirst_eq, hfirst_approx⟩ :=
      tryFirstFromIndexedElement_getElementFrom_of_equivalent_diff
        first p.commonDifference index1 diff hdiff_approx
    have hdiff0 : ¬ diff ≈ zero := by
      intro hz
      exact p.commonDifference_ne_zero
        (Setoid.trans (Setoid.symm hdiff_approx) hz)
    refine
      ⟨{
          first := some first'
          commonDifference := diff
          limit := lastElementFrom first' diff (getLength p)
          commonDifference_ne_zero := hdiff0
        }, ?_, ?_⟩
    · simp only [tryFromTwoElementsAndLength, hle1, hle2, ↓reduceIte, hget1,
        hget2, hcomp, hdiff_eq, hdiff0, ↓reduceDIte, hfirst_eq]
    · have hf_q :
          effectiveFirst
            {
              first := some first'
              commonDifference := diff
              limit := lastElementFrom first' diff (getLength p)
              commonDifference_ne_zero := hdiff0
            } =
            some first' :=
        effectiveFirst_of_equivalent_lastElementFrom first' diff diff
          (lastElementFrom first' diff (getLength p)) (getLength p) hne0
          hdiff0 (Setoid.refl _) (Setoid.refl _)
      have hlen_q :=
        getLength_lastElementFrom first' diff hdiff0 (getLength p) hne0
      exact equivalence_of_equivalent_params p _ first first' hf hf_q
        (Setoid.symm hfirst_approx) (Setoid.symm hdiff_approx)
        (Setoid.symm hlen_q)
  | .greater hgt =>
    obtain ⟨diff, hdiff_eq, hdiff_approx⟩ :=
      tryCommonDifferenceFromOrderedIndexedElements_getElementFrom
        first p.commonDifference index2 index1 hgt
    obtain ⟨first', hfirst_eq, hfirst_approx⟩ :=
      tryFirstFromIndexedElement_getElementFrom_of_equivalent_diff
        first p.commonDifference index2 diff hdiff_approx
    have hdiff0 : ¬ diff ≈ zero := by
      intro hz
      exact p.commonDifference_ne_zero
        (Setoid.trans (Setoid.symm hdiff_approx) hz)
    refine
      ⟨{
          first := some first'
          commonDifference := diff
          limit := lastElementFrom first' diff (getLength p)
          commonDifference_ne_zero := hdiff0
        }, ?_, ?_⟩
    · simp only [tryFromTwoElementsAndLength, hle1, hle2, ↓reduceIte, hget1,
        hget2, hcomp, hdiff_eq, hdiff0, ↓reduceDIte, hfirst_eq]
    · have hf_q :
          effectiveFirst
            {
              first := some first'
              commonDifference := diff
              limit := lastElementFrom first' diff (getLength p)
              commonDifference_ne_zero := hdiff0
            } =
            some first' :=
        effectiveFirst_of_equivalent_lastElementFrom first' diff diff
          (lastElementFrom first' diff (getLength p)) (getLength p) hne0
          hdiff0 (Setoid.refl _) (Setoid.refl _)
      have hlen_q :=
        getLength_lastElementFrom first' diff hdiff0 (getLength p) hne0
      exact equivalence_of_equivalent_params p _ first first' hf hf_q
        (Setoid.symm hfirst_approx) (Setoid.symm hdiff_approx)
        (Setoid.symm hlen_q)

/-- Advance one step from an optional current element of a finite arithmetic
progression: add the common difference while the result does not lie past the
limit; stay at `none` once past the end. -/
def nextMaskedWalkElement (commonDifference limit : Decimal) :
    Option Decimal → Option Decimal
  | none => none
  | some x =>
    tryInclude commonDifference limit (x + commonDifference)

/-- Whether every unmasked entry agrees with a progression walk that is already
positioned at `current` (the value of `tryGetElement` at the corresponding
index). Masked (`none`) entries are skipped after advancing the walk. Avoids
recomputing `tryGetElement` from the start at each unmasked entry. Elements are
compared up to Decimal equivalence. -/
def agreesWithMaskedElementsFromCurrent
    (commonDifference limit : Decimal) (current : Option Decimal) :
    Sequences.List (Option Decimal) → Bool
  | .empty => true
  | .firstElement none rest =>
      agreesWithMaskedElementsFromCurrent commonDifference limit
        (nextMaskedWalkElement commonDifference limit current) rest
  | .firstElement (some x) rest =>
      match current with
      | none => false
      | some y =>
        if y ≈ x then
          agreesWithMaskedElementsFromCurrent commonDifference limit
            (nextMaskedWalkElement commonDifference limit current) rest
        else
          false

/-- Whether every unmasked entry agrees with `tryGetElement` on `p`, scanning
from the given ordinal Decimal index. Masked (`none`) entries are ignored.

Seeks the starting element once via `effectiveFirst` / `getElementFrom` (or
`none` when out of range), then walks by successive addition of the common
difference — avoiding a fresh `tryGetElement` walk at every unmasked entry.
Unmasked entries are compared up to Decimal equivalence. -/
def agreesWithMaskedElementsFrom (p : FiniteArithmetic)
    (index : OrdinalNatural.Decimal) (elements : Sequences.List (Option Decimal)) :
    Bool :=
  match effectiveFirst p with
  | none =>
    agreesWithMaskedElementsFromCurrent p.commonDifference p.limit none elements
  | some first =>
    if CardinalNatural.Decimal.fromOrdinal index ≤ getLength p then
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
    (index1 : OrdinalNatural.Decimal) (element1 : Decimal)
    (length : CardinalNatural.Decimal)
    (index : OrdinalNatural.Decimal) (hlt : index1 < index) :
    (elements : Sequences.List (Option Decimal)) →
    CardinalNatural.Peano.one ≤ elements.unmaskedCount →
    Option FiniteArithmetic
  | .empty, hge =>
      False.elim (CardinalNatural.Peano.not_successor_le_zero (by
        simpa only [Sequences.List.unmaskedCount, CardinalNatural.Peano.one]
          using hge))
  | .firstElement none rest, hge =>
      tryFromMaskedElementsGivenOne index1 element1 length
        index.successor
        (OrdinalNatural.Decimal.lt_trans hlt
          (OrdinalNatural.Decimal.x_lt_successor_x index))
        rest (by
          simpa only [Sequences.List.unmaskedCount] using hge)
  | .firstElement (some element2) rest, _ =>
      match
        tryFromTwoElementsAndLength index1 element1 index element2 length
          (OrdinalNatural.Decimal.not_equivalent_of_lt hlt) with
      | none => none
      | some p =>
        if agreesWithMaskedElementsFrom p index.successor rest then
          some p
        else
          none

/-- Scan a masked element list from the given ordinal Decimal index until the
first unmasked entry is found, then continue with
`tryFromMaskedElementsGivenOne`. -/
def tryFromMaskedElementsFrom (index : OrdinalNatural.Decimal)
    (length : CardinalNatural.Decimal) :
    (elements : Sequences.List (Option Decimal)) →
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
        index.successor (OrdinalNatural.Decimal.x_lt_successor_x index) rest (by
          have h :
              CardinalNatural.Peano.two ≤
                rest.unmaskedCount + CardinalNatural.Peano.one := by
            simpa only [Sequences.List.unmaskedCount] using hge
          have h' :
              CardinalNatural.Peano.two ≤
                rest.unmaskedCount.successor := by
            simpa only [CardinalNatural.Peano.add_one] using h
          exact CardinalNatural.Peano.le_of_successor_le_successor (by
            simpa only [CardinalNatural.Peano.two, CardinalNatural.Peano.one]
              using h'))

/-- Reconstruct a finite arithmetic progression from an ordered list of its
elements in which some entries may be masked as `none`. Requires a proof that
at least two entries are unmasked. Returns `none` when the unmasked entries are
not consistent with a finite arithmetic progression whose length equals that of
the list (compared up to Decimal equivalence).

Uses the first two unmasked entries (together with their ordinal Decimal indexes
and the list length) via `tryFromTwoElementsAndLength`, then checks that every
remaining unmasked entry agrees with the reconstructed progression. -/
def tryFromMaskedElements
    (elements : Sequences.List (Option Decimal))
    (hge : CardinalNatural.Peano.two ≤ elements.unmaskedCount) :
    Option FiniteArithmetic :=
  tryFromMaskedElementsFrom OrdinalNatural.Decimal.one
    (CardinalNatural.Decimal.fromPeano elements.length) elements hge

/-- Prop counterpart of `agreesWithMaskedElementsFrom`: every unmasked entry is
Decimal-equivalent to `tryGetElement` at the corresponding ordinal index. -/
inductive AgreesWithMaskedElementsFrom (p : FiniteArithmetic) :
    OrdinalNatural.Decimal → Sequences.List (Option Decimal) → Prop where
  | empty (index : OrdinalNatural.Decimal) :
      AgreesWithMaskedElementsFrom p index .empty
  | masked (index : OrdinalNatural.Decimal)
      (rest : Sequences.List (Option Decimal)) :
      AgreesWithMaskedElementsFrom p index.successor rest →
        AgreesWithMaskedElementsFrom p index (.firstElement none rest)
  | unmasked (index : OrdinalNatural.Decimal) (y x : Decimal)
      (rest : Sequences.List (Option Decimal)) :
      Sequences.Progression.tryGetElement index.toPeano (toProgression p) =
          some y →
        y ≈ x →
          AgreesWithMaskedElementsFrom p index.successor rest →
            AgreesWithMaskedElementsFrom p index (.firstElement (some x) rest)

/-- One walk step matches `toProgression.next` on a present element. -/
theorem nextMaskedWalkElement_eq_toProgression_next
    (p : FiniteArithmetic) (x : Decimal) :
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

/-- In-range `tryGetElement` is related by Decimal equivalence to
`getElementFrom` on the effective first. -/
theorem tryGetElement_rel_getElementFrom_of_le (p : FiniteArithmetic)
    (first : Decimal) (hf : effectiveFirst p = some first)
    (index : OrdinalNatural.Decimal)
    (hle : CardinalNatural.Decimal.fromOrdinal index ≤ getLength p) :
    Option.Rel (· ≈ ·)
      (Sequences.Progression.tryGetElement index.toPeano (toProgression p))
      (some (getElementFrom first p.commonDifference index)) := by
  have htry :=
    Sequences.Progression.tryGetElement_eq_some_getElement
      (toProgression p) (toProgression_finite p) index.toPeano
      (fromOrdinal_le_progression_getLength p index hle)
  rw [htry]
  exact Option.Rel.some
    (Setoid.trans (Setoid.symm (getElement_eq p index hle))
      (by
        rw [getElement_eq_getElementFrom p first hf index hle]
        exact Setoid.refl _))

/-- Out-of-range `tryGetElement` is `none`. -/
theorem tryGetElement_eq_none_of_length_lt (p : FiniteArithmetic)
    (index : OrdinalNatural.Decimal)
    (hlt : getLength p < CardinalNatural.Decimal.fromOrdinal index) :
    Sequences.Progression.tryGetElement index.toPeano (toProgression p) = none := by
  have hlt_peano :
      Sequences.Progression.getLength (toProgression p) (toProgression_finite p) <
        CardinalNatural.Peano.fromOrdinal index.toPeano := by
    have hlen_eq := getLength_eq p
    have hto :
        (getLength p).toPeano =
          Sequences.Progression.getLength (toProgression p)
            (toProgression_finite p) := by
      have h := CardinalNatural.Decimal.toPeano_eq_of_equivalent hlen_eq
      rwa [CardinalNatural.Decimal.toPeano_fromPeano] at h
    have hlt' :
        (getLength p).toPeano <
          (CardinalNatural.Decimal.fromOrdinal index).toPeano :=
      hlt
    rwa [hto, CardinalNatural.Decimal.fromOrdinal_toPeano_eq_fromOrdinal_peano]
      at hlt'
  exact Sequences.Progression.tryGetElement_eq_none_of_getLength_lt
    (toProgression p) (toProgression_finite p) index.toPeano hlt_peano

/-- `tryInclude` preserves Decimal `Option.Rel (· ≈ ·)` on equivalent candidates. -/
theorem tryInclude_rel_of_equivalent (commonDifference limit a b : Decimal)
    (h : a ≈ b) :
    Option.Rel (· ≈ ·)
      (tryInclude commonDifference limit a)
      (tryInclude commonDifference limit b) := by
  have hle_ab : (a ≤ limit) ↔ (b ≤ limit) := by
    constructor
    · intro hle
      exact (le_iff_toPeano_le _ _).mpr
        (toPeano_eq_of_equivalent h ▸ (le_iff_toPeano_le _ _).mp hle)
    · intro hle
      exact (le_iff_toPeano_le _ _).mpr
        ((toPeano_eq_of_equivalent h).symm ▸
          (le_iff_toPeano_le _ _).mp hle)
  have hle_ba : (limit ≤ a) ↔ (limit ≤ b) := by
    constructor
    · intro hle
      exact (le_iff_toPeano_le _ _).mpr
        (toPeano_eq_of_equivalent h ▸ (le_iff_toPeano_le _ _).mp hle)
    · intro hle
      exact (le_iff_toPeano_le _ _).mpr
        ((toPeano_eq_of_equivalent h).symm ▸
          (le_iff_toPeano_le _ _).mp hle)
  match hdiff : commonDifference.toPeano with
  | .positive _ =>
    simp only [tryInclude, hdiff]
    by_cases hle_a : a ≤ limit
    · have hle_b : b ≤ limit := hle_ab.mp hle_a
      simp only [hle_a, hle_b, ↓reduceIte]
      exact Option.Rel.some h
    · have hle_b : ¬ b ≤ limit := fun h' => hle_a (hle_ab.mpr h')
      simp only [hle_a, hle_b, ↓reduceIte]
      exact Option.Rel.none
  | .negative _ =>
    simp only [tryInclude, hdiff]
    by_cases hle_a : limit ≤ a
    · have hle_b : limit ≤ b := hle_ba.mp hle_a
      simp only [hle_a, hle_b, ↓reduceIte]
      exact Option.Rel.some h
    · have hle_b : ¬ limit ≤ b := fun h' => hle_a (hle_ba.mpr h')
      simp only [hle_a, hle_b, ↓reduceIte]
      exact Option.Rel.none
  | .zero =>
    simp only [tryInclude, hdiff]
    exact Option.Rel.none

/-- Masked walk steps preserve Decimal `Option.Rel (· ≈ ·)`. -/
theorem nextMaskedWalkElement_rel_of_rel (commonDifference limit : Decimal)
    {c1 c2 : Option Decimal} (h : Option.Rel (· ≈ ·) c1 c2) :
    Option.Rel (· ≈ ·)
      (nextMaskedWalkElement commonDifference limit c1)
      (nextMaskedWalkElement commonDifference limit c2) := by
  cases h with
  | none =>
    exact Option.Rel.none
  | some hxy =>
    rename_i x y
    exact tryInclude_rel_of_equivalent commonDifference limit
      (x + commonDifference) (y + commonDifference)
      (equivalent_add_right hxy)

/-- The current-position agreement walk is invariant under replacing `current` by
an `Option.Rel (· ≈ ·)`-related value. -/
theorem agreesWithMaskedElementsFromCurrent_eq_of_current_rel
    (commonDifference limit : Decimal) {c1 c2 : Option Decimal}
    (h : Option.Rel (· ≈ ·) c1 c2)
    (elements : Sequences.List (Option Decimal)) :
    agreesWithMaskedElementsFromCurrent commonDifference limit c1 elements =
      agreesWithMaskedElementsFromCurrent commonDifference limit c2 elements := by
  induction elements generalizing c1 c2 with
  | empty =>
    rfl
  | firstElement head rest ih =>
    cases head with
    | none =>
      exact ih (nextMaskedWalkElement_rel_of_rel commonDifference limit h)
    | some x =>
      cases h with
      | none =>
        rfl
      | some hy =>
        rename_i y1 y2
        simp only [agreesWithMaskedElementsFromCurrent]
        by_cases h1 : y1 ≈ x
        · have h2 : y2 ≈ x := Setoid.trans (Setoid.symm hy) h1
          simp only [h1, h2, ↓reduceIte]
          exact ih (nextMaskedWalkElement_rel_of_rel commonDifference limit
            (Option.Rel.some hy))
        · have h2 : ¬ y2 ≈ x := fun h' => h1 (Setoid.trans hy h')
          simp only [h1, h2, ↓reduceIte]

/-- `agreesWithMaskedElementsFrom` starts its walk at `tryGetElement` on the
Peano embedding of the Decimal index. -/
theorem agreesWithMaskedElementsFrom_eq_fromCurrent_tryGetElement
    (p : FiniteArithmetic) (index : OrdinalNatural.Decimal)
    (elements : Sequences.List (Option Decimal)) :
    agreesWithMaskedElementsFrom p index elements =
      agreesWithMaskedElementsFromCurrent p.commonDifference p.limit
        (Sequences.Progression.tryGetElement index.toPeano (toProgression p))
        elements := by
  match hf : effectiveFirst p with
  | none =>
    have htry := tryGetElement_none_of_effectiveFirst_none p index.toPeano hf
    simp only [agreesWithMaskedElementsFrom, hf, htry]
  | some first =>
    by_cases hle : CardinalNatural.Decimal.fromOrdinal index ≤ getLength p
    · have hrel :=
        tryGetElement_rel_getElementFrom_of_le p first hf index hle
      have hcongr :=
        agreesWithMaskedElementsFromCurrent_eq_of_current_rel
          p.commonDifference p.limit hrel elements
      simp only [agreesWithMaskedElementsFrom, hf, hle, ↓reduceIte]
      exact hcongr.symm
    · have hlt : getLength p < CardinalNatural.Decimal.fromOrdinal index := by
        cases CardinalNatural.Decimal.trichotomy_or (getLength p)
            (CardinalNatural.Decimal.fromOrdinal index) with
        | inl hlt => exact hlt
        | inr h =>
          cases h with
          | inl heq => exact False.elim (hle (Or.inr heq.symm))
          | inr hgt => exact False.elim (hle (Or.inl hgt))
      have htry := tryGetElement_eq_none_of_length_lt p index hlt
      simp only [agreesWithMaskedElementsFrom, hf, hle, ↓reduceIte, htry]

/-- The current-position walk agrees with the Prop when `current` is
`tryGetElement` at the corresponding Decimal index. -/
theorem agreesWithMaskedElementsFromCurrent_eq_true_iff
    (p : FiniteArithmetic) (index : OrdinalNatural.Decimal)
    (current : Option Decimal)
    (elements : Sequences.List (Option Decimal))
    (hcur : current =
      Sequences.Progression.tryGetElement index.toPeano (toProgression p)) :
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
            Sequences.Progression.tryGetElement index.successor.toPeano
              (toProgression p) := by
        rw [hcur, nextMaskedWalkElement_tryGetElement,
          OrdinalNatural.Decimal.successor_toPeano]
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
            Sequences.Progression.tryGetElement index.toPeano (toProgression p) =
              none := hcur.symm
        constructor
        · intro h
          exact False.elim (Bool.false_ne_true h)
        · intro h
          cases h with
          | unmasked _ _ _ _ htry' _ _ =>
            rw [htry] at htry'
            nomatch htry'
      | some y =>
        have htry :
            Sequences.Progression.tryGetElement index.toPeano (toProgression p) =
              some y := hcur.symm
        simp only
        split
        · next heq =>
          have hnext :
              nextMaskedWalkElement p.commonDifference p.limit (some y) =
                Sequences.Progression.tryGetElement index.successor.toPeano
                  (toProgression p) := by
            rw [← htry, nextMaskedWalkElement_tryGetElement,
              OrdinalNatural.Decimal.successor_toPeano]
          constructor
          · intro h
            exact AgreesWithMaskedElementsFrom.unmasked index y x rest htry heq
              ((ih index.successor
                (nextMaskedWalkElement p.commonDifference p.limit (some y))
                hnext).mp h)
          · intro h
            cases h with
            | unmasked _ y' _ _ htry' _ hrest =>
              have hy : some y = some y' := htry.symm.trans htry'
              injection hy with hy'
              subst hy'
              exact (ih index.successor
                (nextMaskedWalkElement p.commonDifference p.limit (some y))
                hnext).mpr hrest
        · next hne =>
          constructor
          · intro h
            exact False.elim (Bool.false_ne_true h)
          · intro h
            cases h with
            | unmasked _ y' _ _ htry' heq' _ =>
              have hy : some y = some y' := htry.symm.trans htry'
              injection hy with hy'
              exact False.elim (hne (hy' ▸ heq'))

theorem agreesWithMaskedElementsFrom_eq_true_iff
    (p : FiniteArithmetic) (index : OrdinalNatural.Decimal)
    (elements : Sequences.List (Option Decimal)) :
    agreesWithMaskedElementsFrom p index elements = true ↔
      AgreesWithMaskedElementsFrom p index elements := by
  rw [agreesWithMaskedElementsFrom_eq_fromCurrent_tryGetElement]
  exact agreesWithMaskedElementsFromCurrent_eq_true_iff p index
    (Sequences.Progression.tryGetElement index.toPeano (toProgression p))
    elements rfl

theorem agreesWithMaskedElementsFrom_unmasked_eq_true
    (p : FiniteArithmetic) (index : OrdinalNatural.Decimal)
    (x : Decimal) (rest : Sequences.List (Option Decimal)) (y : Decimal)
    (hx : Sequences.Progression.tryGetElement index.toPeano (toProgression p) =
      some y)
    (heq : y ≈ x)
    (hrest : agreesWithMaskedElementsFrom p index.successor rest = true) :
    agreesWithMaskedElementsFrom p index (.firstElement (some x) rest) = true := by
  rw [agreesWithMaskedElementsFrom_eq_fromCurrent_tryGetElement, hx]
  rw [agreesWithMaskedElementsFrom_eq_fromCurrent_tryGetElement] at hrest
  simp only [agreesWithMaskedElementsFromCurrent, heq, ↓reduceIte]
  rwa [show nextMaskedWalkElement p.commonDifference p.limit (some y) =
      Sequences.Progression.tryGetElement index.successor.toPeano
        (toProgression p) from
    by
      rw [← hx, nextMaskedWalkElement_tryGetElement,
        OrdinalNatural.Decimal.successor_toPeano]]

/-- A successful `tryFromMaskedElementsGivenOne` recovers a value equivalent to
the given first unmasked element, has length equivalent to the requested length,
and agrees with every unmasked entry in the scanned suffix. -/
theorem getLength_agreesWithMaskedElementsFrom_of_tryFromMaskedElementsGivenOne
    (index1 : OrdinalNatural.Decimal) (element1 : Decimal)
    (length : CardinalNatural.Decimal)
    (index : OrdinalNatural.Decimal) (hlt : index1 < index)
    (elements : Sequences.List (Option Decimal))
    (hge : CardinalNatural.Peano.one ≤ elements.unmaskedCount)
    (p : FiniteArithmetic)
    (h : tryFromMaskedElementsGivenOne index1 element1 length index hlt
        elements hge = some p) :
    getLength p ≈ length ∧
      (∃ (hle1 : CardinalNatural.Decimal.fromOrdinal index1 ≤ getLength p),
        getElement p index1 hle1 ≈ element1) ∧
      agreesWithMaskedElementsFrom p index elements = true := by
  match elements with
  | .empty =>
    exact (CardinalNatural.Peano.not_successor_le_zero (by
      simpa only [Sequences.List.unmaskedCount, CardinalNatural.Peano.one]
        using hge)).elim
  | .firstElement none rest =>
    have ih :=
      getLength_agreesWithMaskedElementsFrom_of_tryFromMaskedElementsGivenOne
        index1 element1 length index.successor
        (OrdinalNatural.Decimal.lt_trans hlt
          (OrdinalNatural.Decimal.x_lt_successor_x index)) rest (by
          simpa only [Sequences.List.unmaskedCount] using hge) p (by
          simpa only [tryFromMaskedElementsGivenOne] using h)
    refine ⟨ih.1, ih.2.1, ?_⟩
    rw [agreesWithMaskedElementsFrom_eq_fromCurrent_tryGetElement]
    rw [agreesWithMaskedElementsFrom_eq_fromCurrent_tryGetElement] at ih
    simpa only [agreesWithMaskedElementsFromCurrent,
      nextMaskedWalkElement_tryGetElement,
      OrdinalNatural.Decimal.successor_toPeano] using ih.2.2
  | .firstElement (some element2) rest =>
    simp only [tryFromMaskedElementsGivenOne] at h
    match hs : tryFromTwoElementsAndLength index1 element1 index element2 length
        (OrdinalNatural.Decimal.not_equivalent_of_lt hlt) with
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
            (OrdinalNatural.Decimal.not_equivalent_of_lt hlt) p hs
        refine ⟨hsound.1, hsound.2.1, ?_⟩
        obtain ⟨hle2, hget2⟩ := hsound.2.2
        have htry2 :=
          Sequences.Progression.tryGetElement_eq_some_getElement
            (toProgression p) (toProgression_finite p) index.toPeano
            (fromOrdinal_le_progression_getLength p index hle2)
        have hy :
            Sequences.Progression.getElement (toProgression p)
                (toProgression_finite p) index.toPeano
                (fromOrdinal_le_progression_getLength p index hle2) ≈
              element2 :=
          Setoid.trans (Setoid.symm (getElement_eq p index hle2)) hget2
        exact agreesWithMaskedElementsFrom_unmasked_eq_true p index element2 rest
          _ htry2 hy hAgree
      · next =>
        nomatch h

/-- A successful `tryFromMaskedElementsFrom` has length equivalent to the
requested length and agrees with every unmasked entry from the given starting
index. -/
theorem getLength_agreesWithMaskedElementsFrom_of_tryFromMaskedElementsFrom
    (index : OrdinalNatural.Decimal) (length : CardinalNatural.Decimal)
    (elements : Sequences.List (Option Decimal))
    (hge : CardinalNatural.Peano.two ≤ elements.unmaskedCount)
    (p : FiniteArithmetic)
    (h : tryFromMaskedElementsFrom index length elements hge = some p) :
    getLength p ≈ length ∧
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
      nextMaskedWalkElement_tryGetElement,
      OrdinalNatural.Decimal.successor_toPeano] using ih.2
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
      exact CardinalNatural.Peano.le_of_successor_le_successor (by
        simpa only [CardinalNatural.Peano.two, CardinalNatural.Peano.one]
          using h'')
    have hGiven :=
      getLength_agreesWithMaskedElementsFrom_of_tryFromMaskedElementsGivenOne
        index x length index.successor
        (OrdinalNatural.Decimal.x_lt_successor_x index) rest hgeRest p (by
          simpa only [tryFromMaskedElementsFrom] using h)
    refine ⟨hGiven.1, ?_⟩
    obtain ⟨hle1, hget1⟩ := hGiven.2.1
    have htry :=
      Sequences.Progression.tryGetElement_eq_some_getElement
        (toProgression p) (toProgression_finite p) index.toPeano
        (fromOrdinal_le_progression_getLength p index hle1)
    have hy :
        Sequences.Progression.getElement (toProgression p)
            (toProgression_finite p) index.toPeano
            (fromOrdinal_le_progression_getLength p index hle1) ≈
          x :=
      Setoid.trans (Setoid.symm (getElement_eq p index hle1)) hget1
    exact agreesWithMaskedElementsFrom_unmasked_eq_true p index x rest
      _ htry hy hGiven.2.2

/-- A successful `tryFromMaskedElements` yields a progression whose length is
equivalent to the list length and whose `tryGetElement` recovers every unmasked
entry at the same ordinal index up to Decimal equivalence. -/
theorem getLength_agreesWithMaskedElements_of_tryFromMaskedElements
    (elements : Sequences.List (Option Decimal))
    (hge : CardinalNatural.Peano.two ≤ elements.unmaskedCount)
    (p : FiniteArithmetic)
    (h : tryFromMaskedElements elements hge = some p) :
    getLength p ≈ CardinalNatural.Decimal.fromPeano elements.length ∧
      AgreesWithMaskedElementsFrom p OrdinalNatural.Decimal.one elements := by
  have h' :
      tryFromMaskedElementsFrom OrdinalNatural.Decimal.one
        (CardinalNatural.Decimal.fromPeano elements.length) elements hge =
        some p := by
    simpa only [tryFromMaskedElements] using h
  have hsound :=
    getLength_agreesWithMaskedElementsFrom_of_tryFromMaskedElementsFrom
      OrdinalNatural.Decimal.one
      (CardinalNatural.Decimal.fromPeano elements.length) elements hge p h'
  refine ⟨hsound.1, ?_⟩
  exact (agreesWithMaskedElementsFrom_eq_true_iff p OrdinalNatural.Decimal.one
    elements).mp hsound.2

/-- Extend a finite arithmetic progression of length at least two to an infinite
arithmetic progression with the same effective first element and common
difference. The infinite progression begins with every element of the original
finite progression. -/
def extendToInfinite (p : FiniteArithmetic)
    (hge : CardinalNatural.Peano.two ≤ (getLength p).toPeano) :
    InfiniteArithmetic :=
  match hf : effectiveFirst p with
  | none =>
    False.elim
      (CardinalNatural.Peano.not_two_le_zero
        (((CardinalNatural.Decimal.toPeano_eq_of_equivalent
            ((getLength_eq_zero_iff_effectiveFirst_none p).mpr hf)).trans
          CardinalNatural.Decimal.toPeano_zero) ▸ hge))
  | some first =>
    { first := first, commonDifference := p.commonDifference }

/-- In-range elements of a finite arithmetic progression agree with the
corresponding elements of its infinite extension. -/
theorem getElement_extendToInfinite (p : FiniteArithmetic)
    (hge : CardinalNatural.Peano.two ≤ (getLength p).toPeano)
    (index : OrdinalNatural.Decimal)
    (hle : CardinalNatural.Decimal.fromOrdinal index ≤ getLength p) :
    InfiniteArithmetic.getElement (extendToInfinite p hge) index =
      getElement p index hle := by
  unfold extendToInfinite
  split
  · next hf =>
    exact (CardinalNatural.Peano.not_two_le_zero
      (((CardinalNatural.Decimal.toPeano_eq_of_equivalent
          ((getLength_eq_zero_iff_effectiveFirst_none p).mpr hf)).trans
        CardinalNatural.Decimal.toPeano_zero) ▸ hge)).elim
  · next first hf =>
    rw [getElement_eq_getElementFrom p first hf index hle]
    exact (getElementFrom_eq_InfiniteArithmetic_getElement
      first p.commonDifference index).symm

/-- Extend a finite arithmetic progression of length at least two to a finite
arithmetic progression of a given length at least that of the original, with the
same effective first element and common difference. The extended progression
begins with every element of the original progression. -/
def extendToLength (p : FiniteArithmetic)
    (hge : CardinalNatural.Peano.two ≤ (getLength p).toPeano)
    (length : CardinalNatural.Decimal)
    (_hle : getLength p ≤ length) :
    FiniteArithmetic :=
  match hf : effectiveFirst p with
  | none =>
    False.elim
      (CardinalNatural.Peano.not_two_le_zero
        (((CardinalNatural.Decimal.toPeano_eq_of_equivalent
            ((getLength_eq_zero_iff_effectiveFirst_none p).mpr hf)).trans
          CardinalNatural.Decimal.toPeano_zero) ▸ hge))
  | some first =>
    {
      first := some first
      commonDifference := p.commonDifference
      limit := lastElementFrom first p.commonDifference length
      commonDifference_ne_zero := p.commonDifference_ne_zero
    }

/-- Extending to a longer length yields a progression whose length is equivalent
to that requested length. -/
theorem getLength_extendToLength (p : FiniteArithmetic)
    (hge : CardinalNatural.Peano.two ≤ (getLength p).toPeano)
    (length : CardinalNatural.Decimal)
    (hleLen : getLength p ≤ length) :
    getLength (extendToLength p hge length hleLen) ≈ length := by
  unfold extendToLength
  split
  · next hf =>
    exact (CardinalNatural.Peano.not_two_le_zero
      (((CardinalNatural.Decimal.toPeano_eq_of_equivalent
          ((getLength_eq_zero_iff_effectiveFirst_none p).mpr hf)).trans
        CardinalNatural.Decimal.toPeano_zero) ▸ hge)).elim
  · next first hf =>
    have hne : ¬ length ≈ CardinalNatural.Decimal.zero := by
      intro hzero
      have hp0 : getLength p ≈ CardinalNatural.Decimal.zero :=
        CardinalNatural.Decimal.eq_zero_of_le_zero _
          (CardinalNatural.Decimal.le_of_le_of_equivalent hleLen hzero)
      exact CardinalNatural.Peano.not_two_le_zero
        (((CardinalNatural.Decimal.toPeano_eq_of_equivalent hp0).trans
          CardinalNatural.Decimal.toPeano_zero) ▸ hge)
    exact getLength_lastElementFrom first p.commonDifference
      p.commonDifference_ne_zero length hne

/-- The extended progression keeps the original effective first element. -/
theorem effectiveFirst_extendToLength (p : FiniteArithmetic)
    (hge : CardinalNatural.Peano.two ≤ (getLength p).toPeano)
    (length : CardinalNatural.Decimal)
    (hleLen : getLength p ≤ length)
    (first : Decimal) (hf : effectiveFirst p = some first) :
    effectiveFirst (extendToLength p hge length hleLen) = some first := by
  have hne : ¬ length ≈ CardinalNatural.Decimal.zero := by
    intro hzero
    have hp0 : getLength p ≈ CardinalNatural.Decimal.zero :=
      CardinalNatural.Decimal.eq_zero_of_le_zero _
        (CardinalNatural.Decimal.le_of_le_of_equivalent hleLen hzero)
    exact CardinalNatural.Peano.not_two_le_zero
      (((CardinalNatural.Decimal.toPeano_eq_of_equivalent hp0).trans
        CardinalNatural.Decimal.toPeano_zero) ▸ hge)
  unfold extendToLength
  split
  · next hf' =>
    rw [hf'] at hf
    nomatch hf
  · next first' hf' =>
    have heq : some first = some first' := hf.symm.trans hf'
    injection heq with heq'
    rw [← heq']
    exact effectiveFirst_of_equivalent_lastElementFrom first
      p.commonDifference p.commonDifference
      (lastElementFrom first p.commonDifference length) length hne
      p.commonDifference_ne_zero (Setoid.refl _) (Setoid.refl _)

/-- In-range elements of a finite arithmetic progression agree with the
corresponding elements of its length extension. -/
theorem getElement_extendToLength (p : FiniteArithmetic)
    (hge : CardinalNatural.Peano.two ≤ (getLength p).toPeano)
    (length : CardinalNatural.Decimal)
    (hleLen : getLength p ≤ length)
    (index : OrdinalNatural.Decimal)
    (hle : CardinalNatural.Decimal.fromOrdinal index ≤ getLength p) :
    ∃ (hle' : CardinalNatural.Decimal.fromOrdinal index ≤
        getLength (extendToLength p hge length hleLen)),
      getElement (extendToLength p hge length hleLen) index hle' =
        getElement p index hle := by
  have hlenExt := getLength_extendToLength p hge length hleLen
  have hle' :
      CardinalNatural.Decimal.fromOrdinal index ≤
        getLength (extendToLength p hge length hleLen) :=
    CardinalNatural.Decimal.le_of_le_of_equivalent
      (CardinalNatural.Decimal.le_trans hle hleLen) (Setoid.symm hlenExt)
  refine ⟨hle', ?_⟩
  match hf : effectiveFirst p with
  | none =>
    exact (CardinalNatural.Peano.not_two_le_zero
      (((CardinalNatural.Decimal.toPeano_eq_of_equivalent
          ((getLength_eq_zero_iff_effectiveFirst_none p).mpr hf)).trans
        CardinalNatural.Decimal.toPeano_zero) ▸ hge)).elim
  | some first =>
    have hfExt :=
      effectiveFirst_extendToLength p hge length hleLen first hf
    rw [getElement_eq_getElementFrom (extendToLength p hge length hleLen)
      first hfExt index hle']
    rw [getElement_eq_getElementFrom p first hf index hle]
    have hdiff :
        (extendToLength p hge length hleLen).commonDifference =
          p.commonDifference := by
      unfold extendToLength
      split
      · next hf' =>
        rw [hf'] at hf
        nomatch hf
      · rfl
    rw [hdiff]

/-- Truncate a finite arithmetic progression of length at least two to a finite
arithmetic progression of a given length at most that of the original, with the
same effective first element (when non-empty) and common difference. The
truncated progression contains the initial elements of the original
progression. -/
def truncateToLength (p : FiniteArithmetic)
    (hge : CardinalNatural.Peano.two ≤ (getLength p).toPeano)
    (length : CardinalNatural.Decimal)
    (_hle : length ≤ getLength p) :
    FiniteArithmetic :=
  if length ≈ CardinalNatural.Decimal.zero then
    {
      first := none
      commonDifference := p.commonDifference
      limit := p.limit
      commonDifference_ne_zero := p.commonDifference_ne_zero
    }
  else
    match hf : effectiveFirst p with
    | none =>
      False.elim
        (CardinalNatural.Peano.not_two_le_zero
          (((CardinalNatural.Decimal.toPeano_eq_of_equivalent
              ((getLength_eq_zero_iff_effectiveFirst_none p).mpr hf)).trans
            CardinalNatural.Decimal.toPeano_zero) ▸ hge))
    | some first =>
      {
        first := some first
        commonDifference := p.commonDifference
        limit := lastElementFrom first p.commonDifference length
        commonDifference_ne_zero := p.commonDifference_ne_zero
      }

/-- Truncating to a shorter length yields a progression whose length is
equivalent to that requested length. -/
theorem getLength_truncateToLength (p : FiniteArithmetic)
    (hge : CardinalNatural.Peano.two ≤ (getLength p).toPeano)
    (length : CardinalNatural.Decimal)
    (hleLen : length ≤ getLength p) :
    getLength (truncateToLength p hge length hleLen) ≈ length := by
  unfold truncateToLength
  split
  · next hzero =>
    simp only [getLength]
    exact Setoid.symm hzero
  · next hne =>
    split
    · next hf =>
      exact (CardinalNatural.Peano.not_two_le_zero
        (((CardinalNatural.Decimal.toPeano_eq_of_equivalent
            ((getLength_eq_zero_iff_effectiveFirst_none p).mpr hf)).trans
          CardinalNatural.Decimal.toPeano_zero) ▸ hge)).elim
    · next first hf =>
      exact getLength_lastElementFrom first p.commonDifference
        p.commonDifference_ne_zero length hne

/-- The truncated progression keeps the original effective first element when the
target length is positive. -/
theorem effectiveFirst_truncateToLength (p : FiniteArithmetic)
    (hge : CardinalNatural.Peano.two ≤ (getLength p).toPeano)
    (length : CardinalNatural.Decimal)
    (hleLen : length ≤ getLength p)
    (hne : ¬ length ≈ CardinalNatural.Decimal.zero)
    (first : Decimal) (hf : effectiveFirst p = some first) :
    effectiveFirst (truncateToLength p hge length hleLen) = some first := by
  unfold truncateToLength
  split
  · next hzero =>
    exact (hne hzero).elim
  · next _ =>
    split
    · next hf' =>
      rw [hf'] at hf
      nomatch hf
    · next first' hf' =>
      have heq : some first = some first' := hf.symm.trans hf'
      injection heq with heq'
      rw [← heq']
      exact effectiveFirst_of_equivalent_lastElementFrom first
        p.commonDifference p.commonDifference
        (lastElementFrom first p.commonDifference length) length hne
        p.commonDifference_ne_zero (Setoid.refl _) (Setoid.refl _)

/-- In-range elements of a truncated finite arithmetic progression agree with
the corresponding elements of the original progression. -/
theorem getElement_truncateToLength (p : FiniteArithmetic)
    (hge : CardinalNatural.Peano.two ≤ (getLength p).toPeano)
    (length : CardinalNatural.Decimal)
    (hleLen : length ≤ getLength p)
    (index : OrdinalNatural.Decimal)
    (hle : CardinalNatural.Decimal.fromOrdinal index ≤ length) :
    ∃ (hle' : CardinalNatural.Decimal.fromOrdinal index ≤
        getLength (truncateToLength p hge length hleLen)),
      getElement (truncateToLength p hge length hleLen) index hle' =
        getElement p index
          (CardinalNatural.Decimal.le_trans hle hleLen) := by
  have hlenTrunc := getLength_truncateToLength p hge length hleLen
  have hleOrig : CardinalNatural.Decimal.fromOrdinal index ≤ getLength p :=
    CardinalNatural.Decimal.le_trans hle hleLen
  have hle' :
      CardinalNatural.Decimal.fromOrdinal index ≤
        getLength (truncateToLength p hge length hleLen) :=
    CardinalNatural.Decimal.le_of_le_of_equivalent hle (Setoid.symm hlenTrunc)
  refine ⟨hle', ?_⟩
  have hne : ¬ length ≈ CardinalNatural.Decimal.zero := by
    intro hzero
    exact CardinalNatural.Decimal.fromOrdinal_not_equivalent_zero index
      (CardinalNatural.Decimal.eq_zero_of_le_zero _
        (CardinalNatural.Decimal.le_of_le_of_equivalent hle hzero))
  match hf : effectiveFirst p with
  | none =>
    exact (CardinalNatural.Peano.not_two_le_zero
      (((CardinalNatural.Decimal.toPeano_eq_of_equivalent
          ((getLength_eq_zero_iff_effectiveFirst_none p).mpr hf)).trans
        CardinalNatural.Decimal.toPeano_zero) ▸ hge)).elim
  | some first =>
    have hfTrunc :=
      effectiveFirst_truncateToLength p hge length hleLen hne first hf
    rw [getElement_eq_getElementFrom (truncateToLength p hge length hleLen)
      first hfTrunc index hle']
    rw [getElement_eq_getElementFrom p first hf index hleOrig]
    have hdiff :
        (truncateToLength p hge length hleLen).commonDifference =
          p.commonDifference := by
      unfold truncateToLength
      split
      · next hzero =>
        exact (hne hzero).elim
      · next _ =>
        split
        · next hf' =>
          rw [hf'] at hf
          nomatch hf
        · rfl
    rw [hdiff]

/-- Truncate an infinite arithmetic progression with nonzero common difference
to a finite arithmetic progression of a given length, with the same first
element (when non-empty) and common difference. The truncated progression
contains the initial elements of the original progression. -/
def truncateInfiniteToLength (p : InfiniteArithmetic)
    (hdiff : ¬ p.commonDifference ≈ zero)
    (length : CardinalNatural.Decimal) :
    FiniteArithmetic :=
  if length ≈ CardinalNatural.Decimal.zero then
    {
      first := none
      commonDifference := p.commonDifference
      limit := p.first
      commonDifference_ne_zero := hdiff
    }
  else
    {
      first := some p.first
      commonDifference := p.commonDifference
      limit := lastElementFrom p.first p.commonDifference length
      commonDifference_ne_zero := hdiff
    }

/-- Truncating an infinite arithmetic progression yields a progression whose
length is equivalent to the requested length. -/
theorem getLength_truncateInfiniteToLength (p : InfiniteArithmetic)
    (hdiff : ¬ p.commonDifference ≈ zero)
    (length : CardinalNatural.Decimal) :
    getLength (truncateInfiniteToLength p hdiff length) ≈ length := by
  unfold truncateInfiniteToLength
  split
  · next hzero =>
    simp only [getLength]
    exact Setoid.symm hzero
  · next hne =>
    exact getLength_lastElementFrom p.first p.commonDifference
      hdiff length hne

/-- Truncating a non-empty prefix of an infinite arithmetic progression keeps
the original first element as the effective first. -/
theorem effectiveFirst_truncateInfiniteToLength (p : InfiniteArithmetic)
    (hdiff : ¬ p.commonDifference ≈ zero)
    (length : CardinalNatural.Decimal)
    (hne : ¬ length ≈ CardinalNatural.Decimal.zero) :
    effectiveFirst (truncateInfiniteToLength p hdiff length) = some p.first := by
  unfold truncateInfiniteToLength
  split
  · next hzero =>
    exact (hne hzero).elim
  · next _ =>
    exact effectiveFirst_of_equivalent_lastElementFrom p.first
      p.commonDifference p.commonDifference
      (lastElementFrom p.first p.commonDifference length) length hne
      hdiff (Setoid.refl _) (Setoid.refl _)

/-- In-range elements of a truncated infinite arithmetic progression agree with
the corresponding elements of the original infinite progression. -/
theorem getElement_truncateInfiniteToLength (p : InfiniteArithmetic)
    (hdiff : ¬ p.commonDifference ≈ zero)
    (length : CardinalNatural.Decimal)
    (index : OrdinalNatural.Decimal)
    (hle : CardinalNatural.Decimal.fromOrdinal index ≤ length) :
    ∃ (hle' : CardinalNatural.Decimal.fromOrdinal index ≤
        getLength (truncateInfiniteToLength p hdiff length)),
      getElement (truncateInfiniteToLength p hdiff length) index hle' =
        InfiniteArithmetic.getElement p index := by
  have hlenTrunc := getLength_truncateInfiniteToLength p hdiff length
  have hle' :
      CardinalNatural.Decimal.fromOrdinal index ≤
        getLength (truncateInfiniteToLength p hdiff length) :=
    CardinalNatural.Decimal.le_of_le_of_equivalent hle (Setoid.symm hlenTrunc)
  refine ⟨hle', ?_⟩
  have hne : ¬ length ≈ CardinalNatural.Decimal.zero := by
    intro hzero
    exact CardinalNatural.Decimal.fromOrdinal_not_equivalent_zero index
      (CardinalNatural.Decimal.eq_zero_of_le_zero _
        (CardinalNatural.Decimal.le_of_le_of_equivalent hle hzero))
  have hf := effectiveFirst_truncateInfiniteToLength p hdiff length hne
  rw [getElement_eq_getElementFrom (truncateInfiniteToLength p hdiff length)
    p.first hf index hle']
  have hdiff' :
      (truncateInfiniteToLength p hdiff length).commonDifference =
        p.commonDifference := by
    unfold truncateInfiniteToLength
    split
    · next hzero =>
      exact (hne hzero).elim
    · rfl
  rw [hdiff']
  exact (getElementFrom_eq_InfiniteArithmetic_getElement
    p.first p.commonDifference index).symm

end FiniteArithmetic

end ZeroMath.Numbers.Integer.Decimal.Progressions
