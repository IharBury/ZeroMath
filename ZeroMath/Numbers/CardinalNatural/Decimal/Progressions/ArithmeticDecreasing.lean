import ZeroMath.Numbers.CardinalNatural.Decimal
import ZeroMath.Numbers.CardinalNatural.Decimal.Progressions.InfiniteArithmetic
import ZeroMath.Numbers.CardinalNatural.Peano.Progressions.ArithmeticDecreasing
import ZeroMath.Sequences.List
import ZeroMath.Sequences.Progression

namespace ZeroMath.Numbers.CardinalNatural.Decimal.Progressions

/-- An arithmetic progression of Decimal numbers with subtractive common
difference, defined by an optional first element (`none` for the empty
progression), the common difference (subtracted at each step), and a limit
such that no element is less than the limit. The progression is also empty
when the first element is less than the limit. -/
structure ArithmeticDecreasing where
  first : Option Decimal
  subtractiveCommonDifference : Decimal
  limit : Decimal
  subtractiveCommonDifference_ne_zero : ¬ subtractiveCommonDifference ≈ zero

namespace ArithmeticDecreasing

/-- Convert a decreasing arithmetic progression to a general progression by
taking the same optional first element when it is not less than the limit
(otherwise the empty progression) and subtracting the common difference while
the next element is not less than the limit. -/
def toProgression (p : ArithmeticDecreasing) : Sequences.Progression Decimal where
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
    (index : OrdinalNatural.Peano) (x : Decimal)
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
theorem lt_of_next_eq_some (p : ArithmeticDecreasing) (y x : Decimal)
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
      have hadd : z + p.subtractiveCommonDifference ≈ y := by
        rw [← hsub]
        exact subtract_add_cancel y p.subtractiveCommonDifference hlt
      have hpeano :
          z.toPeano + p.subtractiveCommonDifference.toPeano = y.toPeano := by
        rw [← add_toPeano, toPeano_eq_of_equivalent hadd]
      have hone : Peano.one ≤ p.subtractiveCommonDifference.toPeano :=
        Peano.succ_le_of_lt
          (Peano.zero_lt_of_ne_zero _
            (toPeano_ne_zero_of_not_equivalent_zero
              p.subtractiveCommonDifference_ne_zero))
      have hz_le : Peano.successor z.toPeano ≤ y.toPeano := by
        rw [← Peano.add_one, ← hpeano]
        exact Peano.add_le_add_left hone z.toPeano
      exact heq ▸ Peano.lt_of_succ_le hz_le
    · simp only [hle, ↓reduceIte] at h
      nomatch h

/-- If `tryGetElement` returns a value and the progression starts at `first`,
then `fromOrdinal index + x.toPeano ≤ successor first.toPeano`. Each step
decreases the value by at least one while the ordinal index (as a cardinal)
increases by one, so their sum never exceeds that of the first element. -/
theorem fromOrdinal_add_le_succ_first_of_tryGetElement (p : ArithmeticDecreasing)
    (first : Decimal) (index : OrdinalNatural.Peano) (x : Decimal)
    (hf : (toProgression p).first = some first)
    (h : Sequences.Progression.tryGetElement index (toProgression p) = some x) :
    Peano.fromOrdinal index + x.toPeano ≤ first.toPeano.successor := by
  induction index generalizing x with
  | one =>
    simp only [Sequences.Progression.tryGetElement] at h
    have heq : x = first := by
      rw [hf] at h
      injection h with heq
      exact heq.symm
    rw [heq, Peano.fromOrdinal, Peano.one_add]
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
      have hx_le : x.toPeano.successor ≤ y.toPeano :=
        Peano.succ_le_of_lt hlt
      have hn : Peano.fromOrdinal n + y.toPeano ≤ first.toPeano.successor :=
        ih y hm
      have hmid :
          Peano.fromOrdinal n + x.toPeano.successor ≤
            Peano.fromOrdinal n + y.toPeano :=
        Peano.add_le_add_left hx_le (Peano.fromOrdinal n)
      have hmid' :
          Peano.fromOrdinal n + x.toPeano.successor ≤ first.toPeano.successor :=
        Peano.le_trans hmid hn
      have heqadd :
          Peano.fromOrdinal n.successor + x.toPeano =
            Peano.fromOrdinal n + x.toPeano.successor := by
        change (Peano.fromOrdinal n).successor + x.toPeano =
          Peano.fromOrdinal n + x.toPeano.successor
        rw [Peano.successor_add, Peano.add_successor]
      exact heqadd ▸ hmid'

/-- The progression obtained from a decreasing arithmetic progression is finite:
if it is empty then `tryGetElement` at `one` is `none`; otherwise, starting from
`first`, `tryGetElement` at the ordinal for `successor (successor first.toPeano)`
cannot return `some`, since that value `x` would need
`successor (successor first.toPeano) + x.toPeano ≤ successor first.toPeano`. -/
theorem toProgression_finite (p : ArithmeticDecreasing) :
    Sequences.Progression.Finite (toProgression p) := by
  match hf : (toProgression p).first with
  | none =>
    refine ⟨OrdinalNatural.Peano.one, ?_⟩
    simp only [Sequences.Progression.tryGetElement, hf]
  | some first =>
    have hne : (first.toPeano.successor).successor ≠ Peano.zero :=
      Peano.successor_ne_zero first.toPeano.successor
    refine ⟨Peano.toOrdinal (first.toPeano.successor).successor hne, ?_⟩
    cases h :
        Sequences.Progression.tryGetElement
          (Peano.toOrdinal (first.toPeano.successor).successor hne)
          (toProgression p) with
    | none =>
      rfl
    | some x =>
      have hle :=
        fromOrdinal_add_le_succ_first_of_tryGetElement p first
          (Peano.toOrdinal (first.toPeano.successor).successor hne) x hf h
      rw [Peano.fromOrdinal_toOrdinal] at hle
      have hle' : (first.toPeano.successor).successor ≤ first.toPeano.successor :=
        Peano.le_trans
          (Peano.le_add_self_left (first.toPeano.successor).successor x.toPeano) hle
      exact (Peano.not_succ_le first.toPeano.successor hle').elim

/-- Length remaining from an element already known to lie in the progression,
given the room below that element down to the limit (`none` when the element
equals the limit). Computed with one division by the subtractive common
difference instead of comparing each successive term to the limit. -/
def lengthFromGap (diff : Decimal) (hdiff : ¬ diff ≈ zero) :
    Option Decimal → Decimal
  | none => one
  | some gap =>
    match divideWithRemainder gap diff hdiff with
    | (q, _) => q.successor

/-- The length of a decreasing arithmetic progression: the number of elements
before `tryGetElement` first returns `none`. Uses a single comparison of the
first element to the limit and one division, avoiding a comparison at every
step of the progression. -/
def getLength (p : ArithmeticDecreasing) : Decimal :=
  match p.first with
  | none => zero
  | some first =>
    match compare first p.limit with
    | .less _ => zero
    | .equivalent _ => one
    | .greater hlt =>
      lengthFromGap p.subtractiveCommonDifference
        p.subtractiveCommonDifference_ne_zero
        (some (subtract first p.limit (Or.inl hlt)))

/-- Convert a Decimal decreasing arithmetic progression to the corresponding
Peano progression by embedding each field via `toPeano`. -/
def toPeano (p : ArithmeticDecreasing) :
    Peano.Progressions.ArithmeticDecreasing where
  first :=
    match p.first with
    | none => none
    | some x => some x.toPeano
  subtractiveCommonDifference := p.subtractiveCommonDifference.toPeano
  limit := p.limit.toPeano
  subtractiveCommonDifference_ne_zero :=
    toPeano_ne_zero_of_not_equivalent_zero p.subtractiveCommonDifference_ne_zero

/-- Decimal `≤` is reflected and reflected by the Peano embedding. -/
theorem le_iff_toPeano_le (a b : Decimal) : a ≤ b ↔ a.toPeano ≤ b.toPeano :=
  ⟨toPeano_le_of_le, le_of_toPeano_le⟩

/-- `lengthFromGap` agrees with the Peano `lengthFromGap` on embeddings. -/
theorem lengthFromGap_toPeano (diff : Decimal) (hdiff : ¬ diff ≈ zero)
    (gap : Option Decimal) :
    (lengthFromGap diff hdiff gap).toPeano =
      Peano.Progressions.ArithmeticDecreasing.lengthFromGap
        diff.toPeano (toPeano_ne_zero_of_not_equivalent_zero hdiff)
        (gap.map Decimal.toPeano) := by
  match gap with
  | none =>
    simp only [lengthFromGap, Option.map, toPeano_one,
      Peano.Progressions.ArithmeticDecreasing.lengthFromGap]
  | some g =>
    match hdiv : divideWithRemainder g diff hdiff with
    | (q, r) =>
      obtain ⟨hdiff', hpeano⟩ := divideWithRemainder_toPeano g diff hdiff hdiv
      simp only [lengthFromGap, hdiv, Option.map,
        Peano.Progressions.ArithmeticDecreasing.lengthFromGap]
      rw [show toPeano_ne_zero_of_not_equivalent_zero hdiff = hdiff' from rfl,
        hpeano, successor_toPeano]

/-- `getLength` agrees with Peano `getLength` on the embedded progression. -/
theorem getLength_toPeano (p : ArithmeticDecreasing) :
    (getLength p).toPeano =
      Peano.Progressions.ArithmeticDecreasing.getLength (toPeano p) := by
  cases hf : p.first with
  | none =>
    simp only [getLength, hf, toPeano,
      Peano.Progressions.ArithmeticDecreasing.getLength, toPeano_zero]
  | some first =>
    have hto : toPeano p =
        {
          first := some first.toPeano
          subtractiveCommonDifference := p.subtractiveCommonDifference.toPeano
          limit := p.limit.toPeano
          subtractiveCommonDifference_ne_zero :=
            toPeano_ne_zero_of_not_equivalent_zero
              p.subtractiveCommonDifference_ne_zero
        } := by
      simp only [toPeano, hf]
    rw [hto]
    unfold getLength Peano.Progressions.ArithmeticDecreasing.getLength
    simp only [hf]
    cases hcmp : Peano.compare first.toPeano p.limit.toPeano with
    | less hlt =>
      have hdec : compare first p.limit = .less hlt := by
        simp only [compare, hcmp]
      simp only [hdec, toPeano_zero]
    | equal heq =>
      have hdec : compare first p.limit =
          .equivalent (equivalent_of_toPeano_eq heq) := by
        simp only [compare, hcmp]
      simp only [hdec, toPeano_one]
    | greater hgt =>
      have hdec : compare first p.limit = .greater hgt := by
        simp only [compare, hcmp]
      simp only [hdec]
      obtain ⟨_, hsub_eq⟩ := subtract_toPeano first p.limit (Or.inl hgt)
      have hlen :=
        lengthFromGap_toPeano p.subtractiveCommonDifference
          p.subtractiveCommonDifference_ne_zero
          (some (subtract first p.limit (Or.inl hgt)))
      simpa [Option.map, hsub_eq] using hlen

/-- `trySubtract` commutes with the Peano embedding. -/
theorem trySubtract_map_toPeano (x y : Decimal) :
    Option.map Decimal.toPeano (trySubtract x y) =
      Peano.trySubtract x.toPeano y.toPeano := by
  match h : trySubtract x y with
  | some z =>
    obtain ⟨hle, hsub⟩ := exists_subtract_of_trySubtract h
    obtain ⟨hle2, hsub_eq⟩ := subtract_toPeano x y hle
    have hp :
        Peano.trySubtract x.toPeano y.toPeano = some z.toPeano :=
      Peano.trySubtract_of_subtract
        (x := x.toPeano) (y := y.toPeano) (z := z.toPeano)
        ⟨hle2, by rw [← hsub_eq, hsub]⟩
    simp only [Option.map, hp]
  | none =>
    match htry : Peano.trySubtract x.toPeano y.toPeano with
    | none =>
      simp only [Option.map]
    | some z =>
      have hex := Peano.exists_subtract_of_trySubtract htry
      have hle' : y ≤ x := le_of_toPeano_le hex.choose
      have hsome :=
        trySubtract_of_subtract (z := subtract x y hle') ⟨hle', rfl⟩
      rw [hsome] at h
      nomatch h

/-- Advancing one step of `toProgression` commutes with `toPeano`. -/
theorem next_toPeano (p : ArithmeticDecreasing) (x : Decimal) :
    Option.map Decimal.toPeano ((toProgression p).next x) =
      (Peano.Progressions.ArithmeticDecreasing.toProgression
        (toPeano p)).next x.toPeano := by
  have hsub := trySubtract_map_toPeano x p.subtractiveCommonDifference
  cases hs : trySubtract x p.subtractiveCommonDifference with
  | none =>
    have hs' : Peano.trySubtract x.toPeano
        p.subtractiveCommonDifference.toPeano = none := by
      simpa [hs, Option.map] using hsub.symm
    simp only [toProgression, hs, toPeano,
      Peano.Progressions.ArithmeticDecreasing.toProgression, hs', Option.map]
  | some y =>
    have hs' : Peano.trySubtract x.toPeano
        p.subtractiveCommonDifference.toPeano = some y.toPeano := by
      simpa [hs, Option.map] using hsub.symm
    have hiff := le_iff_toPeano_le p.limit y
    by_cases hle : p.limit ≤ y
    · have hle' : p.limit.toPeano ≤ y.toPeano := hiff.mp hle
      simp only [toProgression, hs, hle, ↓reduceIte, toPeano,
        Peano.Progressions.ArithmeticDecreasing.toProgression, hs', hle',
        ↓reduceIte, Option.map]
    · have hle' : ¬ p.limit.toPeano ≤ y.toPeano := fun h => hle (hiff.mpr h)
      simp only [toProgression, hs, hle, ↓reduceIte, toPeano,
        Peano.Progressions.ArithmeticDecreasing.toProgression, hs', hle',
        ↓reduceIte, Option.map]

/-- The first element of `toProgression` commutes with `toPeano`. -/
theorem first_toPeano (p : ArithmeticDecreasing) :
    Option.map Decimal.toPeano (toProgression p).first =
      (Peano.Progressions.ArithmeticDecreasing.toProgression
        (toPeano p)).first := by
  cases hf : p.first with
  | none =>
    simp only [toProgression, hf, toPeano,
      Peano.Progressions.ArithmeticDecreasing.toProgression, Option.map]
  | some x =>
    have hprog :
        (toProgression p).first =
          if p.limit ≤ x then some x else none := by
      simp only [toProgression, hf]
    have hprog' :
        (Peano.Progressions.ArithmeticDecreasing.toProgression
          (toPeano p)).first =
          if p.limit.toPeano ≤ x.toPeano then some x.toPeano else none := by
      simp only [toPeano, hf,
        Peano.Progressions.ArithmeticDecreasing.toProgression]
    rw [hprog, hprog']
    have hiff := le_iff_toPeano_le p.limit x
    by_cases hle : p.limit ≤ x
    · simp only [hle, hiff.mp hle, ↓reduceIte, Option.map]
    · have hle' : ¬ p.limit.toPeano ≤ x.toPeano := fun h => hle (hiff.mpr h)
      simp only [hle, hle', ↓reduceIte, Option.map]

/-- Accessibility is preserved by embedding the current state via `toPeano`. -/
theorem acc_map_toPeano (p : ArithmeticDecreasing) (current : Option Decimal)
    (hAcc : Acc (Sequences.Progression.OptionStep (toProgression p).next) current) :
    Acc (Sequences.Progression.OptionStep
      (Peano.Progressions.ArithmeticDecreasing.toProgression
        (toPeano p)).next)
      (current.map Decimal.toPeano) := by
  refine Acc.rec
    (motive := fun current _ =>
      Acc (Sequences.Progression.OptionStep
        (Peano.Progressions.ArithmeticDecreasing.toProgression
          (toPeano p)).next)
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
              (Peano.Progressions.ArithmeticDecreasing.toProgression
                (toPeano p)).next)
              ((Peano.Progressions.ArithmeticDecreasing.toProgression
                (toPeano p)).next x.toPeano) :=
          hnext ▸ hAcc_next
        exact Sequences.Progression.acc_step hAcc_next')
    hAcc

/-- Walking length from an accessible Decimal state equals the Peano walk from
its embedding. -/
theorem getLengthFrom_toPeano (p : ArithmeticDecreasing)
    (current : Option Decimal)
    (hAcc : Acc (Sequences.Progression.OptionStep (toProgression p).next) current) :
    Sequences.Progression.getLengthFrom (toProgression p).next current hAcc =
      Sequences.Progression.getLengthFrom
        (Peano.Progressions.ArithmeticDecreasing.toProgression
          (toPeano p)).next
        (current.map Decimal.toPeano)
        (acc_map_toPeano p current hAcc) := by
  refine Acc.rec
    (motive := fun current hAcc =>
      Sequences.Progression.getLengthFrom (toProgression p).next current hAcc =
        Sequences.Progression.getLengthFrom
          (Peano.Progressions.ArithmeticDecreasing.toProgression
            (toPeano p)).next
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
          (Peano.Progressions.ArithmeticDecreasing.toProgression
            (toPeano p)).next
          x.toPeano (hmap ▸ hAcc_map)]
        have hnext := next_toPeano p x
        have ih' := ih ((toProgression p).next x)
          (Sequences.Progression.OptionStep.step x)
        refine congrArg Peano.successor (ih'.trans ?_)
        exact
          (Sequences.Progression.getLengthFrom_eq_of_current_eq _
            hnext
            (acc_map_toPeano p ((toProgression p).next x)
              (hAccx.inv (Sequences.Progression.OptionStep.step x)))).trans
            (Sequences.Progression.getLengthFrom_eq_of_acc_eq _ _ _ _))
    hAcc

/-- `Progression.getLength` of a Decimal decreasing arithmetic progression equals
that of its Peano embedding. -/
theorem progression_getLength_toPeano (p : ArithmeticDecreasing) :
    Sequences.Progression.getLength (toProgression p) (toProgression_finite p) =
      Sequences.Progression.getLength
        (Peano.Progressions.ArithmeticDecreasing.toProgression (toPeano p))
        (Peano.Progressions.ArithmeticDecreasing.toProgression_finite
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
theorem getLength_eq (p : ArithmeticDecreasing) :
    getLength p ≈
      fromPeano
        (Sequences.Progression.getLength (toProgression p)
          (toProgression_finite p)) := by
  apply equivalent_of_toPeano_eq
  rw [toPeano_fromPeano, getLength_toPeano,
    Peano.Progressions.ArithmeticDecreasing.getLength_eq (toPeano p),
    progression_getLength_toPeano]

/-- Element at a positive ordinal index starting from a known first value, using
the closed form with no limit comparisons. The first element has index
equivalent to `one`; otherwise the value is
`first` minus `(fromOrdinal (predecessor index)) * subtractiveCommonDifference`
when that subtraction is defined, and `first` otherwise. -/
def getElementFrom (first subtractiveCommonDifference : Decimal)
    (index : OrdinalNatural.Decimal) : Decimal :=
  if h : index ≈ OrdinalNatural.Decimal.one then
    first
  else
    match trySubtract first
        ((fromOrdinal (index.predecessor h)) * subtractiveCommonDifference) with
    | none => first
    | some y => y

/-- If there is no first element, the length is zero. -/
theorem getLength_eq_zero_of_first_none (p : ArithmeticDecreasing)
    (h : p.first = none) :
    getLength p = zero := by
  simp only [getLength, h]

/-- If the first element is less than the limit, the length is zero. -/
theorem getLength_eq_zero_of_first_lt_limit (p : ArithmeticDecreasing)
    (first : Decimal) (hf : p.first = some first) (hlt : first < p.limit) :
    getLength p = zero := by
  unfold getLength
  simp only [hf]
  match hcmp : compare first p.limit with
  | .greater hgt =>
    exact (not_lt_of_lt hlt hgt).elim
  | .equivalent heq =>
    have hself : p.limit.toPeano < p.limit.toPeano := by
      have hlt' : first.toPeano < p.limit.toPeano := hlt
      rwa [toPeano_eq_of_equivalent heq] at hlt'
    exact (Peano.not_lt_self _ hself).elim
  | .less _ =>
    rfl

/-- The length bound is impossible when there is no first element. -/
theorem not_fromOrdinal_le_getLength_of_first_none
    (p : ArithmeticDecreasing) (index : OrdinalNatural.Decimal)
    (hle : fromOrdinal index ≤ getLength p)
    (h : p.first = none) : False := by
  have hle' : fromOrdinal index ≤ zero :=
    (getLength_eq_zero_of_first_none p h) ▸ hle
  exact fromOrdinal_not_equivalent_zero index (eq_zero_of_le_zero _ hle')

/-- The length bound is impossible when the first element is below the limit. -/
theorem not_fromOrdinal_le_getLength_of_first_lt_limit
    (p : ArithmeticDecreasing) (index : OrdinalNatural.Decimal)
    (first : Decimal)
    (hle : fromOrdinal index ≤ getLength p)
    (hf : p.first = some first) (hlt : first < p.limit) : False := by
  have hle' : fromOrdinal index ≤ zero :=
    (getLength_eq_zero_of_first_lt_limit p first hf hlt) ▸ hle
  exact fromOrdinal_not_equivalent_zero index (eq_zero_of_le_zero _ hle')

/-- The element at the given positive ordinal index, when that index does not
exceed the progression's length. The first element has index equivalent to
`one`. Uses a single `compare` of the first element to the limit (as in
`getLength`), then the closed form of the arithmetic progression — avoiding
`toProgression` and a limit comparison at every step. -/
def getElement (p : ArithmeticDecreasing) (index : OrdinalNatural.Decimal)
    (hle : fromOrdinal index ≤ getLength p) : Decimal :=
  match hf : p.first with
  | none =>
    (not_fromOrdinal_le_getLength_of_first_none p index hle hf).elim
  | some first =>
    match compare first p.limit with
    | .less hlt =>
      (not_fromOrdinal_le_getLength_of_first_lt_limit p index first hle hf
        hlt).elim
    | .equivalent _ =>
      getElementFrom first p.subtractiveCommonDifference index
    | .greater _ =>
      getElementFrom first p.subtractiveCommonDifference index

/-- A Decimal length bound on `fromOrdinal index` yields the corresponding Peano
bound for walking `toProgression`. -/
theorem fromOrdinal_le_progression_getLength
    (p : ArithmeticDecreasing) (index : OrdinalNatural.Decimal)
    (hle : fromOrdinal index ≤ getLength p) :
    Peano.fromOrdinal index.toPeano ≤
      Sequences.Progression.getLength (toProgression p)
        (toProgression_finite p) := by
  have hle' :
      fromOrdinal index ≤
        fromPeano
          (Sequences.Progression.getLength (toProgression p)
            (toProgression_finite p)) :=
    le_trans hle (Or.inr (getLength_eq p))
  have hpeano := toPeano_le_of_le hle'
  rw [fromOrdinal_toPeano_eq_fromOrdinal_peano, toPeano_fromPeano] at hpeano
  exact hpeano

/-- When the first element is at least the limit, `toProgression.first` is that
element. -/
theorem toProgression_first_eq_some_of_le (p : ArithmeticDecreasing)
    (start : Decimal) (hf : p.first = some start) (hle : p.limit ≤ start) :
    (toProgression p).first = some start := by
  simp only [toProgression, hf, hle, ↓reduceIte]

/-- `trySubtract` respects Decimal equivalence in the minuend. -/
theorem trySubtract_rel_of_equivalent_left (a b c : Decimal) (hab : a ≈ b) :
    Option.Rel (· ≈ ·) (trySubtract a c) (trySubtract b c) := by
  have ha := trySubtract_map_toPeano a c
  have hb := trySubtract_map_toPeano b c
  have hpeano : a.toPeano = b.toPeano := toPeano_eq_of_equivalent hab
  have htry :
      Peano.trySubtract a.toPeano c.toPeano =
        Peano.trySubtract b.toPeano c.toPeano := by
    rw [hpeano]
  match hsa : trySubtract a c, hsb : trySubtract b c with
  | none, none =>
    exact Option.Rel.none
  | some x, some y =>
    have hx : Peano.trySubtract a.toPeano c.toPeano = some x.toPeano := by
      simpa [hsa, Option.map] using ha.symm
    have hy : Peano.trySubtract b.toPeano c.toPeano = some y.toPeano := by
      simpa [hsb, Option.map] using hb.symm
    have heq : x.toPeano = y.toPeano := by
      rw [htry] at hx
      injection hx.symm.trans hy
    exact Option.Rel.some (equivalent_of_toPeano_eq heq)
  | none, some y =>
    have hx : Peano.trySubtract a.toPeano c.toPeano = none := by
      simpa [hsa, Option.map] using ha.symm
    have hy : Peano.trySubtract b.toPeano c.toPeano = some y.toPeano := by
      simpa [hsb, Option.map] using hb.symm
    rw [htry, hy] at hx
    nomatch hx
  | some x, none =>
    have hx : Peano.trySubtract a.toPeano c.toPeano = some x.toPeano := by
      simpa [hsa, Option.map] using ha.symm
    have hy : Peano.trySubtract b.toPeano c.toPeano = none := by
      simpa [hsb, Option.map] using hb.symm
    rw [htry, hy] at hx
    nomatch hx

/-- Left-multiplication by `one` is the identity up to Decimal equivalence. -/
theorem one_multiply_equivalent (x : Decimal) : one * x ≈ x := by
  apply equivalent_of_toPeano_eq
  rw [multiply_toPeano, toPeano_one, Peano.one_multiply]

/-- For a non-`one` ordinal index, `fromOrdinal` of the predecessor times `diff`
is one step larger than `fromOrdinal` of the predecessor-of-predecessor times
`diff`, when that second predecessor exists. -/
theorem fromOrdinal_predecessor_multiply_eq_add
    (index : OrdinalNatural.Decimal) (diff : Decimal)
    (hne : ¬ index ≈ OrdinalNatural.Decimal.one)
    (hpred : ¬ index.predecessor hne ≈ OrdinalNatural.Decimal.one) :
    fromOrdinal (index.predecessor hne) * diff ≈
      fromOrdinal ((index.predecessor hne).predecessor hpred) * diff + diff := by
  apply equivalent_of_toPeano_eq
  rw [multiply_toPeano, add_toPeano, multiply_toPeano]
  have hfrom :
      (fromOrdinal (index.predecessor hne)).toPeano =
        ((fromOrdinal
            ((index.predecessor hne).predecessor hpred)).toPeano).successor := by
    rw [fromOrdinal_toPeano_eq_fromOrdinal_peano,
      fromOrdinal_toPeano_eq_fromOrdinal_peano]
    have hsucc :=
      OrdinalNatural.Decimal.toPeano_eq_succ_predecessor_toPeano
        (index.predecessor hne) hpred
    rw [hsucc, Peano.fromOrdinal]
  rw [hfrom, Peano.successor_multiply]

/-- When `start ≈ x + d`, `trySubtract start d` recovers a value equivalent to
`x`. -/
theorem trySubtract_of_equivalent_add_right {start x d : Decimal}
    (h : start ≈ x + d) :
    Option.Rel (· ≈ ·) (trySubtract start d) (some x) := by
  have hrel :=
    trySubtract_add_right_of_equivalent x d d (Setoid.refl _)
  have hleft := trySubtract_rel_of_equivalent_left start (x + d) d h
  obtain ⟨w, hw, hwx⟩ := InfiniteArithmetic.exists_of_option_rel_some hrel
  have hleft' : Option.Rel (· ≈ ·) (trySubtract start d) (some w) := by
    rw [← hw]
    exact hleft
  obtain ⟨z, hz, hzw⟩ := InfiniteArithmetic.exists_of_option_rel_some hleft'
  rw [hz]
  exact Option.Rel.some (Setoid.trans hzw hwx)

/-- Successful `tryGetElement` implies the closed-form cumulative subtraction
from the first element recovers an equivalent value. -/
theorem trySubtract_mul_of_tryGetElement_eq_some
    (p : ArithmeticDecreasing) (start : Decimal)
    (hf : (toProgression p).first = some start)
    (index : OrdinalNatural.Decimal) (x : Decimal)
    (hne : ¬ index ≈ OrdinalNatural.Decimal.one)
    (h : Sequences.Progression.tryGetElement index.toPeano (toProgression p) =
      some x) :
    Option.Rel (· ≈ ·)
      (trySubtract start
        (fromOrdinal (index.predecessor hne) * p.subtractiveCommonDifference))
      (some x) := by
  have hpeano :=
    OrdinalNatural.Decimal.toPeano_eq_succ_predecessor_toPeano index hne
  rw [hpeano, Sequences.Progression.tryGetElement] at h
  match htry : Sequences.Progression.tryGetElement
      (index.predecessor hne).toPeano (toProgression p) with
  | none =>
    rw [htry] at h
    nomatch h
  | some y =>
    rw [htry] at h
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
      by_cases hle_lim : p.limit ≤ z
      · simp only [hle_lim, ↓reduceIte] at hnext
        injection hnext with hx
        have hy_add : y ≈ z + p.subtractiveCommonDifference := by
          obtain ⟨hlt, hsub⟩ := exists_subtract_of_trySubtract hs
          have hadd :=
            subtract_add_cancel y p.subtractiveCommonDifference hlt
          rw [hsub] at hadd
          exact Setoid.symm hadd
        if hpred : index.predecessor hne ≈ OrdinalNatural.Decimal.one then
          have hpeano_pred :
              (index.predecessor hne).toPeano = OrdinalNatural.Peano.one :=
            (OrdinalNatural.Decimal.toPeano_eq_one_iff_equivalent_one _).mpr
              hpred
          rw [hpeano_pred, Sequences.Progression.tryGetElement, hf] at htry
          injection htry with heq_y
          have hstart_add :
              start ≈ z + p.subtractiveCommonDifference := by
            rw [heq_y]
            exact hy_add
          have hfrom_one :
              fromOrdinal (index.predecessor hne) ≈ one := by
            apply equivalent_of_toPeano_eq
            rw [fromOrdinal_toPeano_eq_fromOrdinal_peano, hpeano_pred,
              Peano.fromOrdinal, toPeano_one]
          have hmul :
              fromOrdinal (index.predecessor hne) *
                  p.subtractiveCommonDifference ≈
                p.subtractiveCommonDifference :=
            Setoid.trans
              (equivalent_multiply hfrom_one (Setoid.refl _))
              (one_multiply_equivalent _)
          have hstart_mul :
              start ≈
                z + (fromOrdinal (index.predecessor hne) *
                  p.subtractiveCommonDifference) :=
            Setoid.trans hstart_add
              (Setoid.symm (equivalent_add_left hmul))
          have hrel := trySubtract_of_equivalent_add_right hstart_mul
          rw [← hx]
          exact hrel
        else
          have ih :=
            trySubtract_mul_of_tryGetElement_eq_some p start hf
              (index.predecessor hne) y hpred htry
          obtain ⟨w, hw, hwy⟩ :=
            InfiniteArithmetic.exists_of_option_rel_some ih
          have hstart_w :
              start ≈
                w + fromOrdinal
                    ((index.predecessor hne).predecessor hpred) *
                  p.subtractiveCommonDifference := by
            obtain ⟨hlt, hsub⟩ := exists_subtract_of_trySubtract hw
            have hadd :=
              subtract_add_cancel start
                (fromOrdinal
                    ((index.predecessor hne).predecessor hpred) *
                  p.subtractiveCommonDifference)
                hlt
            rw [hsub] at hadd
            exact Setoid.symm hadd
          have hstart_y :
              start ≈
                y + fromOrdinal
                    ((index.predecessor hne).predecessor hpred) *
                  p.subtractiveCommonDifference :=
            Setoid.trans hstart_w (equivalent_add_right hwy)
          have hmul :=
            fromOrdinal_predecessor_multiply_eq_add index
              p.subtractiveCommonDifference hne hpred
          have hstart_z :
              start ≈
                z + (fromOrdinal (index.predecessor hne) *
                  p.subtractiveCommonDifference) := by
            apply equivalent_of_toPeano_eq
            have hp := toPeano_eq_of_equivalent hstart_y
            have hy := toPeano_eq_of_equivalent hy_add
            rw [add_toPeano] at hp hy
            rw [add_toPeano, toPeano_eq_of_equivalent hmul, add_toPeano,
              Peano.add_commutative
                (fromOrdinal
                    ((index.predecessor hne).predecessor hpred) *
                  p.subtractiveCommonDifference).toPeano
                p.subtractiveCommonDifference.toPeano,
              ← Peano.add_associative, ← hy, ← hp]
          have hrel := trySubtract_of_equivalent_add_right hstart_z
          rw [← hx]
          exact hrel
      · simp only [hle_lim, ↓reduceIte] at hnext
        nomatch hnext
termination_by index.toPeano
decreasing_by
  obtain ⟨hne', heq⟩ := OrdinalNatural.Decimal.predecessor_toPeano index hne
  simp only [heq]
  exact OrdinalNatural.Peano.sizeOf_predecessor_lt _ hne'

/-- When `tryGetElement` succeeds from a known first element, the value is
equivalent to the closed-form `getElementFrom` at the Decimal index. -/
theorem eq_getElementFrom_of_tryGetElement_eq_some
    (p : ArithmeticDecreasing) (start : Decimal)
    (hf : (toProgression p).first = some start)
    (index : OrdinalNatural.Decimal) (x : Decimal)
    (h : Sequences.Progression.tryGetElement index.toPeano (toProgression p) =
      some x) :
    x ≈ getElementFrom start p.subtractiveCommonDifference index := by
  if hone : index ≈ OrdinalNatural.Decimal.one then
    have hpeano : index.toPeano = OrdinalNatural.Peano.one :=
      (OrdinalNatural.Decimal.toPeano_eq_one_iff_equivalent_one index).mpr hone
    rw [hpeano, Sequences.Progression.tryGetElement, hf] at h
    injection h with heq
    rw [getElementFrom, dif_pos hone, heq]
    exact Setoid.refl _
  else
    have hrel :=
      trySubtract_mul_of_tryGetElement_eq_some p start hf index x hone h
    unfold getElementFrom
    simp only [hone, ↓reduceDIte]
    match htry : trySubtract start
        (fromOrdinal (index.predecessor hone) * p.subtractiveCommonDifference),
        hrel with
    | none, hrel =>
      cases hrel
    | some z, hrel =>
      cases hrel with
      | some hz =>
        exact Setoid.symm hz

/-- `getElement` agrees with walking `toProgression` via `Progression.getElement`
up to Decimal equivalence. -/
theorem getElement_eq (p : ArithmeticDecreasing)
    (index : OrdinalNatural.Decimal)
    (hle : fromOrdinal index ≤ getLength p) :
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
    cases hcmp : compare start p.limit with
    | less hlt =>
      exact (not_fromOrdinal_le_getLength_of_first_lt_limit p index start hle hf
        hlt).elim
    | equivalent heq =>
      have hle_start : p.limit ≤ start := Or.inr (Setoid.symm heq)
      have hfirst := toProgression_first_eq_some_of_le p start hf hle_start
      exact Setoid.symm
        (eq_getElementFrom_of_tryGetElement_eq_some p start hfirst index _
          htry)
    | greater hgt =>
      have hle_start : p.limit ≤ start := Or.inl hgt
      have hfirst := toProgression_first_eq_some_of_le p start hf hle_start
      exact Setoid.symm
        (eq_getElementFrom_of_tryGetElement_eq_some p start hfirst index _
          htry)

/-- Two decreasing arithmetic progressions are equivalent when their underlying
progressions yield related elements (Decimal setoid `≈`) at every positive
ordinal index. -/
def Equivalence (p q : ArithmeticDecreasing) : Prop :=
  Sequences.Progression.Equivalence (toProgression p) (toProgression q)

instance : HasEquiv ArithmeticDecreasing where
  Equiv := Equivalence

/-- The optional first element after applying the limit filter, without building
a `Progression`. -/
def effectiveFirst (p : ArithmeticDecreasing) : Option Decimal :=
  match p.first with
  | none => none
  | some x => if p.limit ≤ x then some x else none

theorem effectiveFirst_eq (p : ArithmeticDecreasing) :
    effectiveFirst p = (toProgression p).first :=
  rfl

/-- `effectiveFirst` commutes with the Peano embedding. -/
theorem effectiveFirst_toPeano (p : ArithmeticDecreasing) :
    Option.map Decimal.toPeano (effectiveFirst p) =
      Peano.Progressions.ArithmeticDecreasing.effectiveFirst (toPeano p) := by
  rw [effectiveFirst_eq, Peano.Progressions.ArithmeticDecreasing.effectiveFirst_eq]
  exact first_toPeano p

/-- `tryGetElement` commutes with the Peano embedding. -/
theorem tryGetElement_toPeano (p : ArithmeticDecreasing)
    (index : OrdinalNatural.Peano) :
    Option.map Decimal.toPeano
      (Sequences.Progression.tryGetElement index (toProgression p)) =
    Sequences.Progression.tryGetElement index
      (Peano.Progressions.ArithmeticDecreasing.toProgression (toPeano p)) := by
  induction index with
  | one =>
    exact first_toPeano p
  | successor n ih =>
    simp only [Sequences.Progression.tryGetElement]
    cases hp : Sequences.Progression.tryGetElement n (toProgression p) with
    | none =>
      have ih' :
          Sequences.Progression.tryGetElement n
            (Peano.Progressions.ArithmeticDecreasing.toProgression
              (toPeano p)) = none := by
        simpa [hp, Option.map] using ih.symm
      simp only [ih']
      rfl
    | some x =>
      have ih' :
          Sequences.Progression.tryGetElement n
            (Peano.Progressions.ArithmeticDecreasing.toProgression
              (toPeano p)) = some x.toPeano := by
        simpa [hp, Option.map] using ih.symm
      simp only [ih']
      exact next_toPeano p x

/-- Decimal progression equivalence matches Peano equivalence of the embeddings. -/
theorem equivalence_iff_toPeano (p q : ArithmeticDecreasing) :
    Equivalence p q ↔
      Peano.Progressions.ArithmeticDecreasing.Equivalence
        (toPeano p) (toPeano q) := by
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
            (Peano.Progressions.ArithmeticDecreasing.toProgression
              (toPeano p)) = none := by
        simpa [hdp, Option.map] using hp.symm
      have hqq :
          Sequences.Progression.tryGetElement index
            (Peano.Progressions.ArithmeticDecreasing.toProgression
              (toPeano q)) = none := by
        simpa [hdq, Option.map] using hq.symm
      simp only [hpp, hqq]
      exact Option.Rel.none
    | some x, some y, Option.Rel.some heq =>
      have hpp :
          Sequences.Progression.tryGetElement index
            (Peano.Progressions.ArithmeticDecreasing.toProgression
              (toPeano p)) = some x.toPeano := by
        simpa [hdp, Option.map] using hp.symm
      have hqq :
          Sequences.Progression.tryGetElement index
            (Peano.Progressions.ArithmeticDecreasing.toProgression
              (toPeano q)) = some y.toPeano := by
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
            (Peano.Progressions.ArithmeticDecreasing.toProgression
              (toPeano p)) = none := by
        simpa [hdp, Option.map] using hp.symm
      match hdq : Sequences.Progression.tryGetElement index (toProgression q) with
      | none =>
        exact Option.Rel.none
      | some y =>
        have hqq :
            Sequences.Progression.tryGetElement index
              (Peano.Progressions.ArithmeticDecreasing.toProgression
                (toPeano q)) = some y.toPeano := by
          simpa [hdq, Option.map] using hq.symm
        simp only [hpp, hqq] at hrel
        cases hrel
    | some x =>
      have hpp :
          Sequences.Progression.tryGetElement index
            (Peano.Progressions.ArithmeticDecreasing.toProgression
              (toPeano p)) = some x.toPeano := by
        simpa [hdp, Option.map] using hp.symm
      match hdq : Sequences.Progression.tryGetElement index (toProgression q) with
      | none =>
        have hqq :
            Sequences.Progression.tryGetElement index
              (Peano.Progressions.ArithmeticDecreasing.toProgression
                (toPeano q)) = none := by
          simpa [hdq, Option.map] using hq.symm
        simp only [hpp, hqq] at hrel
        cases hrel
      | some y =>
        have hqq :
            Sequences.Progression.tryGetElement index
              (Peano.Progressions.ArithmeticDecreasing.toProgression
                (toPeano q)) = some y.toPeano := by
          simpa [hdq, Option.map] using hq.symm
        simp only [hpp, hqq] at hrel
        cases hrel with
        | some heq =>
          exact Option.Rel.some (equivalent_of_toPeano_eq heq)

theorem getLength_eq_zero_iff_effectiveFirst_none (p : ArithmeticDecreasing) :
    getLength p ≈ zero ↔ effectiveFirst p = none := by
  constructor
  · intro hlen
    have hpeano :
        Peano.Progressions.ArithmeticDecreasing.getLength (toPeano p) =
          Peano.zero := by
      rw [← getLength_toPeano]
      exact (toPeano_eq_of_equivalent hlen).trans toPeano_zero
    have hf :=
      (Peano.Progressions.ArithmeticDecreasing.getLength_eq_zero_iff_effectiveFirst_none
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
    match hf : p.first with
    | none =>
      simp only [getLength, hf]
      exact Setoid.refl _
    | some first =>
      simp only [effectiveFirst, hf] at hfirst
      by_cases hle : p.limit ≤ first
      · simp only [hle, ↓reduceIte] at hfirst
        nomatch hfirst
      · simp only [getLength, hf]
        match hc : compare first p.limit with
        | .less _ =>
          exact Setoid.refl _
        | .equivalent heq =>
          exact (hle (Or.inr (Setoid.symm heq))).elim
        | .greater hgt =>
          exact (hle (Or.inl hgt)).elim

theorem effectiveFirst_eq_some_of_pos_length (p : ArithmeticDecreasing)
    (h : ¬ getLength p ≈ zero) :
    ∃ first, effectiveFirst p = some first := by
  cases hf : effectiveFirst p with
  | none =>
    exact False.elim (h ((getLength_eq_zero_iff_effectiveFirst_none p).mpr hf))
  | some first =>
    exact ⟨first, rfl⟩

/-- Empty progressions (length zero) are equivalent. -/
theorem equivalence_of_length_zero (p q : ArithmeticDecreasing)
    (hp : getLength p ≈ zero) (hq : getLength q ≈ zero) :
    Equivalence p q := by
  have hp' :
      Peano.Progressions.ArithmeticDecreasing.getLength (toPeano p) =
        Peano.zero := by
    rw [← getLength_toPeano]
    exact (toPeano_eq_of_equivalent hp).trans toPeano_zero
  have hq' :
      Peano.Progressions.ArithmeticDecreasing.getLength (toPeano q) =
        Peano.zero := by
    rw [← getLength_toPeano]
    exact (toPeano_eq_of_equivalent hq).trans toPeano_zero
  exact (equivalence_iff_toPeano p q).mpr
    (Peano.Progressions.ArithmeticDecreasing.equivalence_of_length_zero
      (toPeano p) (toPeano q) hp' hq')

/-- Length-one progressions with equivalent first elements are equivalent. -/
theorem equivalence_of_length_one (p q : ArithmeticDecreasing)
    (firstP firstQ : Decimal)
    (hp : effectiveFirst p = some firstP) (hq : effectiveFirst q = some firstQ)
    (hfirst : firstP ≈ firstQ)
    (hlenP : getLength p ≈ one) (hlenQ : getLength q ≈ one) :
    Equivalence p q := by
  have hfirstPeano : firstP.toPeano = firstQ.toPeano :=
    toPeano_eq_of_equivalent hfirst
  have hp' :
      Peano.Progressions.ArithmeticDecreasing.effectiveFirst (toPeano p) =
        some firstP.toPeano := by
    simpa [hp, Option.map] using (effectiveFirst_toPeano p).symm
  have hq' :
      Peano.Progressions.ArithmeticDecreasing.effectiveFirst (toPeano q) =
        some firstP.toPeano := by
    have hq0 :
        Peano.Progressions.ArithmeticDecreasing.effectiveFirst (toPeano q) =
          some firstQ.toPeano := by
      simpa [hq, Option.map] using (effectiveFirst_toPeano q).symm
    exact hq0.trans (congrArg some hfirstPeano.symm)
  have hlenP' :
      Peano.Progressions.ArithmeticDecreasing.getLength (toPeano p) =
        Peano.one := by
    rw [← getLength_toPeano]
    exact (toPeano_eq_of_equivalent hlenP).trans toPeano_one
  have hlenQ' :
      Peano.Progressions.ArithmeticDecreasing.getLength (toPeano q) =
        Peano.one := by
    rw [← getLength_toPeano]
    exact (toPeano_eq_of_equivalent hlenQ).trans toPeano_one
  exact (equivalence_iff_toPeano p q).mpr
    (Peano.Progressions.ArithmeticDecreasing.equivalence_of_length_one
      (toPeano p) (toPeano q) firstP.toPeano hp' hq' hlenP' hlenQ')

/-- Progressions with equivalent first elements and subtractive common differences
and equivalent lengths are equivalent. -/
theorem equivalence_of_equivalent_params (p q : ArithmeticDecreasing)
    (firstP firstQ : Decimal)
    (hp : effectiveFirst p = some firstP) (hq : effectiveFirst q = some firstQ)
    (hfirst : firstP ≈ firstQ)
    (hdiff : p.subtractiveCommonDifference ≈ q.subtractiveCommonDifference)
    (hlen : getLength p ≈ getLength q) :
    Equivalence p q := by
  have hfirstPeano : firstP.toPeano = firstQ.toPeano :=
    toPeano_eq_of_equivalent hfirst
  have hp' :
      Peano.Progressions.ArithmeticDecreasing.effectiveFirst (toPeano p) =
        some firstP.toPeano := by
    simpa [hp, Option.map] using (effectiveFirst_toPeano p).symm
  have hq' :
      Peano.Progressions.ArithmeticDecreasing.effectiveFirst (toPeano q) =
        some firstP.toPeano := by
    have hq0 :
        Peano.Progressions.ArithmeticDecreasing.effectiveFirst (toPeano q) =
          some firstQ.toPeano := by
      simpa [hq, Option.map] using (effectiveFirst_toPeano q).symm
    exact hq0.trans (congrArg some hfirstPeano.symm)
  have hdiff' :
      (toPeano p).subtractiveCommonDifference =
        (toPeano q).subtractiveCommonDifference := by
    simp only [toPeano]
    exact toPeano_eq_of_equivalent hdiff
  have hlen' :
      Peano.Progressions.ArithmeticDecreasing.getLength (toPeano p) =
        Peano.Progressions.ArithmeticDecreasing.getLength (toPeano q) := by
    rw [← getLength_toPeano, ← getLength_toPeano]
    exact toPeano_eq_of_equivalent hlen
  exact (equivalence_iff_toPeano p q).mpr
    (Peano.Progressions.ArithmeticDecreasing.equivalence_of_same_params
      (toPeano p) (toPeano q) firstP.toPeano hp' hq' hdiff' hlen')

theorem effectiveFirst_rel_of_equivalence (p q : ArithmeticDecreasing)
    (h : Equivalence p q) :
    Option.Rel (· ≈ ·) (effectiveFirst p) (effectiveFirst q) := by
  have h1 := h OrdinalNatural.Peano.one
  simp only [Sequences.Progression.tryGetElement, ← effectiveFirst_eq] at h1
  exact h1

theorem getLength_equivalent_of_equivalence (p q : ArithmeticDecreasing)
    (h : Equivalence p q) : getLength p ≈ getLength q := by
  have hpeano :=
    Peano.Progressions.ArithmeticDecreasing.getLength_eq_of_equivalence
      (toPeano p) (toPeano q) ((equivalence_iff_toPeano p q).mp h)
  apply equivalent_of_toPeano_eq
  rw [getLength_toPeano, getLength_toPeano, hpeano]

theorem subtractiveCommonDifference_equivalent_of_equivalence_of_length_ge_two
    (p q : ArithmeticDecreasing) (firstP firstQ : Decimal)
    (hp : effectiveFirst p = some firstP) (hq : effectiveFirst q = some firstQ)
    (hfirst : firstP ≈ firstQ)
    (hne0 : ¬ getLength p ≈ zero) (hne1 : ¬ getLength p ≈ one)
    (hlen : getLength p ≈ getLength q) (h : Equivalence p q) :
    p.subtractiveCommonDifference ≈ q.subtractiveCommonDifference := by
  have h0 :
      Peano.Progressions.ArithmeticDecreasing.getLength (toPeano p) ≠
        Peano.zero := by
    intro hz
    apply hne0
    apply equivalent_of_toPeano_eq
    rw [getLength_toPeano, hz, toPeano_zero]
  have h1 :
      Peano.Progressions.ArithmeticDecreasing.getLength (toPeano p) ≠
        Peano.one := by
    intro hone
    apply hne1
    apply equivalent_of_toPeano_eq
    rw [getLength_toPeano, hone, toPeano_one]
  obtain ⟨n, hlenP⟩ :=
    Peano.Progressions.ArithmeticDecreasing.getLength_ge_two_of_ne_zero_ne_one
      (toPeano p) h0 h1
  have hfirstPeano : firstP.toPeano = firstQ.toPeano :=
    toPeano_eq_of_equivalent hfirst
  have hp' :
      Peano.Progressions.ArithmeticDecreasing.effectiveFirst (toPeano p) =
        some firstP.toPeano := by
    simpa [hp, Option.map] using (effectiveFirst_toPeano p).symm
  have hq' :
      Peano.Progressions.ArithmeticDecreasing.effectiveFirst (toPeano q) =
        some firstP.toPeano := by
    have hq0 :
        Peano.Progressions.ArithmeticDecreasing.effectiveFirst (toPeano q) =
          some firstQ.toPeano := by
      simpa [hq, Option.map] using (effectiveFirst_toPeano q).symm
    exact hq0.trans (congrArg some hfirstPeano.symm)
  have hlen' :
      Peano.Progressions.ArithmeticDecreasing.getLength (toPeano p) =
        Peano.Progressions.ArithmeticDecreasing.getLength (toPeano q) := by
    rw [← getLength_toPeano, ← getLength_toPeano]
    exact toPeano_eq_of_equivalent hlen
  have hdiff :=
    Peano.Progressions.ArithmeticDecreasing.subtractiveCommonDifference_eq_of_equivalence_of_length_ge_two
      (toPeano p) (toPeano q) firstP.toPeano n hp' hq' hlenP hlen'
      ((equivalence_iff_toPeano p q).mp h)
  exact equivalent_of_toPeano_eq hdiff

/-- Extract an underlying `≈` witness from `Option.Rel (· ≈ ·)` on `some`s. -/
theorem equivalent_of_option_rel_some {x y : Decimal}
    (h : Option.Rel (· ≈ ·) (some x) (some y)) : x ≈ y := by
  cases h with
  | some heq => exact heq

/-- Equivalence of decreasing arithmetic progressions is decidable by comparing
lengths, effective first elements, and (when the length is at least two)
subtractive common differences — without converting to `Progression` or walking
successive terms against the limit. -/
instance (p q : ArithmeticDecreasing) : Decidable (p ≈ q) :=
  let lenP := getLength p
  if hL : lenP ≈ getLength q then
    if hZ : lenP ≈ zero then
      isTrue (equivalence_of_length_zero p q hZ (Setoid.trans (Setoid.symm hL) hZ))
    else if hF : Option.Rel (· ≈ ·) (effectiveFirst p) (effectiveFirst q) then
      if hOne : lenP ≈ one then
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
                exact equivalent_of_option_rel_some hF)
              hOne (Setoid.trans (Setoid.symm hL) hOne))
      else if hD : p.subtractiveCommonDifference ≈ q.subtractiveCommonDifference then
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
                exact equivalent_of_option_rel_some hF)
              hD hL)
      else
        isFalse fun heq => by
          obtain ⟨firstP, hf⟩ := effectiveFirst_eq_some_of_pos_length p hZ
          have hrel := effectiveFirst_rel_of_equivalence p q heq
          simp only [hf] at hrel
          match hq : effectiveFirst q with
          | none =>
            rw [hq] at hrel
            cases hrel
          | some firstQ =>
            rw [hq] at hrel
            exact hD
              (subtractiveCommonDifference_equivalent_of_equivalence_of_length_ge_two
                p q firstP firstQ hf hq (equivalent_of_option_rel_some hrel)
                hZ hOne hL heq)
    else
      isFalse fun heq => hF (effectiveFirst_rel_of_equivalence p q heq)
  else
    isFalse fun heq => hL (getLength_equivalent_of_equivalence p q heq)

/-- The Peano predecessor is structurally smaller than its argument. -/
theorem sizeOf_peano_predecessor_lt (n : Peano) (hne : n ≠ Peano.zero) :
    sizeOf (n.predecessor hne) < sizeOf n := by
  cases n with
  | zero => exact False.elim (hne rfl)
  | successor n =>
    have hpred : (Peano.successor n).predecessor hne = n := rfl
    rw [hpred]
    exact Nat.lt_add_of_pos_left (k := 1) Nat.zero_lt_one

/-- Elements from a known start for the given remaining length, retreating by the
subtractive common difference with no limit comparisons. -/
def getElementsFrom (first subtractiveCommonDifference : Decimal) :
    Decimal → Sequences.List Decimal
  | n =>
    if h : n ≈ zero then
      .empty
    else
      .firstElement first
        (match trySubtract first subtractiveCommonDifference with
         | none => .empty
         | some next =>
           getElementsFrom next subtractiveCommonDifference
             (n.predecessor h))
termination_by n => n.toPeano
decreasing_by
  obtain ⟨hne, heq⟩ := predecessor_toPeano n h
  rw [heq]
  exact sizeOf_peano_predecessor_lt _ hne

/-- The ordered list of all elements of a decreasing arithmetic progression.
Empty when there is no in-range first element. Uses the effective first element
and `getLength`, then retreats by repeated subtraction of the subtractive common
difference — avoiding a limit comparison at every step. -/
def getElements (p : ArithmeticDecreasing) : Sequences.List Decimal :=
  match effectiveFirst p with
  | none => .empty
  | some first =>
    getElementsFrom first p.subtractiveCommonDifference (getLength p)

end ArithmeticDecreasing

end ZeroMath.Numbers.CardinalNatural.Decimal.Progressions
