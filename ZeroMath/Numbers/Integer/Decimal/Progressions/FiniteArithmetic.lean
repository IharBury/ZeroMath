import ZeroMath.Numbers.CardinalNatural.Decimal
import ZeroMath.Numbers.Integer.Decimal
import ZeroMath.Numbers.Integer.Decimal.Progressions.InfiniteArithmetic
import ZeroMath.Numbers.Integer.Peano.Progressions.FiniteArithmetic
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
        have hspec := CardinalNatural.Decimal.divideWithRemainder_spec gap diff hdiff
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
            CardinalNatural.Peano.div_rem_unique
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
            CardinalNatural.Peano.div_rem_unique
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
            CardinalNatural.Peano.div_rem_unique
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
          exact absCardinalPeano_eq_fromOrdinal_of_toPeano_positive
            p.commonDifference d hdiff
        have hsub : (p.limit - first).toPeano =
            p.limit.toPeano - first.toPeano := subtract_toPeano p.limit first
        have hpos : p.limit.toPeano - first.toPeano =
            Peano.positive (Peano.ordinalDistance first.toPeano p.limit.toPeano hlt) :=
          Peano.ordinalDistance_sub hlt
        have hg :
            (p.limit - first).magnitude.toPeano =
              CardinalNatural.Peano.fromOrdinal
                (Peano.ordinalDistance first.toPeano p.limit.toPeano hlt) := by
          rw [magnitude_toPeano]
          exact absCardinalPeano_eq_fromOrdinal_of_toPeano_positive
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
          exact absCardinalPeano_eq_fromOrdinal_of_toPeano_negative
            p.commonDifference d hdiff
        have hsub : (first - p.limit).toPeano =
            first.toPeano - p.limit.toPeano := subtract_toPeano first p.limit
        have hpos : first.toPeano - p.limit.toPeano =
            Peano.positive (Peano.ordinalDistance p.limit.toPeano first.toPeano hgt) :=
          Peano.ordinalDistance_sub hgt
        have hg :
            (first - p.limit).magnitude.toPeano =
              CardinalNatural.Peano.fromOrdinal
                (Peano.ordinalDistance p.limit.toPeano first.toPeano hgt) := by
          rw [magnitude_toPeano]
          exact absCardinalPeano_eq_fromOrdinal_of_toPeano_positive
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
`first + (fromOrdinalPositive index - one) * commonDifference`. -/
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
      OrdinalNatural.Decimal.toPeano_eq_succ_predecessor_toPeano index hone
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

end FiniteArithmetic

end ZeroMath.Numbers.Integer.Decimal.Progressions
