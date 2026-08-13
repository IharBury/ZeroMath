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

/-- If `rest` continues a decreasing arithmetic progression after `prev` with
subtractive common difference `diff`, return the last element of that
progression (which is `prev` when `rest` is empty). Returns `none` when a
consecutive pair does not decrease by a difference equivalent to `diff`. -/
def tryLastOfArithmeticContinuation (prev diff : Decimal) :
    Sequences.List Decimal → Option Decimal
  | .empty => some prev
  | .firstElement x xs =>
    match trySubtract prev x with
    | none => none
    | some d =>
      if d ≈ diff then
        tryLastOfArithmeticContinuation x diff xs
      else
        none

/-- Reconstruct a decreasing arithmetic progression from the ordered list of all
its elements. Requires a proof that at least two elements are given. Returns
`none` when the list is not strictly descending with a constant positive
subtractive common difference (compared up to Decimal equivalence).

Uses the first element, the subtractive common difference between consecutive
terms, and the last element as the limit. -/
def tryFromElements :
    (elements : Sequences.List Decimal) →
    Peano.two ≤ elements.length →
    Option ArithmeticDecreasing
  | .empty, hge =>
    False.elim (Peano.not_two_le_zero (by
      change Peano.two ≤ Peano.zero
      exact hge))
  | .firstElement _ .empty, hge =>
    False.elim (Peano.not_two_le_one (by
      change Peano.two ≤ Peano.one
      exact hge))
  | .firstElement x (.firstElement y ys), _ =>
    match trySubtract x y with
    | none => none
    | some diff =>
      if hdiff : diff ≈ zero then
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

/-- A Decimal whose Peano embedding is nonzero is not equivalent to zero. -/
theorem not_equivalent_zero_of_toPeano_ne_zero (n : Decimal)
    (hne : n.toPeano ≠ Peano.zero) :
    ¬ n ≈ zero := by
  intro heq
  exact hne ((toPeano_eq_of_equivalent heq).trans toPeano_zero)

/-- Last element of a non-empty decreasing arithmetic walk of cardinal length `n`,
starting at `first` with subtractive common difference
`subtractiveCommonDifference`. Defined via the Peano embedding so that length
and order facts transport directly. For `n ≈ zero` the value is unused
(`fromPeano` of the Peano placeholder). -/
def lastElementFrom (first subtractiveCommonDifference : Decimal)
    (n : Decimal) : Decimal :=
  fromPeano
    (Peano.Progressions.ArithmeticDecreasing.lastElementFrom
      first.toPeano subtractiveCommonDifference.toPeano n.toPeano)

/-- `lastElementFrom` agrees with the Peano embedding on the nose. -/
theorem lastElementFrom_toPeano (first subtractiveCommonDifference : Decimal)
    (n : Decimal) :
    (lastElementFrom first subtractiveCommonDifference n).toPeano =
      Peano.Progressions.ArithmeticDecreasing.lastElementFrom
        first.toPeano subtractiveCommonDifference.toPeano n.toPeano := by
  simpa [lastElementFrom] using toPeano_fromPeano
    (Peano.Progressions.ArithmeticDecreasing.lastElementFrom
      first.toPeano subtractiveCommonDifference.toPeano n.toPeano)

/-- Pointwise-related lists have equal length. -/
theorem length_eq_of_SameLengthElementwiseRelation {α : Type} {β : Type}
    {r : α → β → Prop} {as : Sequences.List α} {bs : Sequences.List β}
    (h : Sequences.List.SameLengthElementwiseRelation r as bs) :
    as.length = bs.length := by
  induction h with
  | empty => rfl
  | firstElement _ _ ih =>
    rw [Sequences.List.length_firstElement, Sequences.List.length_firstElement, ih]

/-- `getElementsFrom` depends on the length argument only through its Peano
embedding. -/
theorem getElementsFrom_eq_of_toPeano_eq (first subtractiveCommonDifference : Decimal)
    (n m : Decimal) (h : n.toPeano = m.toPeano) :
    getElementsFrom first subtractiveCommonDifference n =
      getElementsFrom first subtractiveCommonDifference m := by
  have hgen :
      ∀ k : Peano, ∀ (first : Decimal)
        (n m : Decimal),
        n.toPeano = k → m.toPeano = k →
          getElementsFrom first subtractiveCommonDifference n =
            getElementsFrom first subtractiveCommonDifference m := by
    intro k
    induction k with
    | zero =>
      intro first n m hn hm
      have hnz : n ≈ zero :=
        equivalent_of_toPeano_eq
          (hn.trans toPeano_zero.symm)
      have hmz : m ≈ zero :=
        equivalent_of_toPeano_eq
          (hm.trans toPeano_zero.symm)
      have hn_empty :
          getElementsFrom first subtractiveCommonDifference n =
            Sequences.List.empty := by
        conv => lhs; unfold getElementsFrom
        simp only [hnz, ↓reduceDIte]
      have hm_empty :
          getElementsFrom first subtractiveCommonDifference m =
            Sequences.List.empty := by
        conv => lhs; unfold getElementsFrom
        simp only [hmz, ↓reduceDIte]
      rw [hn_empty, hm_empty]
    | successor k ih =>
      intro first n m hn hm
      have hne0 : n.toPeano ≠ Peano.zero := by
        rw [hn]
        exact Peano.successor_ne_zero k
      have hme0 : m.toPeano ≠ Peano.zero := by
        rw [hm]
        exact Peano.successor_ne_zero k
      have hne : ¬ n ≈ zero :=
        not_equivalent_zero_of_toPeano_ne_zero n hne0
      have hme : ¬ m ≈ zero :=
        not_equivalent_zero_of_toPeano_ne_zero m hme0
      obtain ⟨hne_peano, hpred_n⟩ :=
        predecessor_toPeano n hne
      obtain ⟨hme_peano, hpred_m⟩ :=
        predecessor_toPeano m hme
      have hpred_n_k : (n.predecessor hne).toPeano = k := by
        rw [hpred_n]
        apply Eq.symm
        apply Peano.successor_injective
        rw [Peano.successor_predecessor n.toPeano hne_peano, hn]
      have hpred_m_k : (m.predecessor hme).toPeano = k := by
        rw [hpred_m]
        apply Eq.symm
        apply Peano.successor_injective
        rw [Peano.successor_predecessor m.toPeano hme_peano, hm]
      have hn_expand :
          getElementsFrom first subtractiveCommonDifference n =
            Sequences.List.firstElement first
              (match trySubtract first subtractiveCommonDifference with
               | none => Sequences.List.empty
               | some next =>
                 getElementsFrom next subtractiveCommonDifference
                   (n.predecessor hne)) := by
        conv => lhs; unfold getElementsFrom
        simp only [hne, ↓reduceDIte]
      have hm_expand :
          getElementsFrom first subtractiveCommonDifference m =
            Sequences.List.firstElement first
              (match trySubtract first subtractiveCommonDifference with
               | none => Sequences.List.empty
               | some next =>
                 getElementsFrom next subtractiveCommonDifference
                   (m.predecessor hme)) := by
        conv => lhs; unfold getElementsFrom
        simp only [hme, ↓reduceDIte]
      rw [hn_expand, hm_expand]
      match hs : trySubtract first subtractiveCommonDifference with
      | none => rfl
      | some next =>
        exact congrArg (Sequences.List.firstElement first)
          (ih next (n.predecessor hne) (m.predecessor hme)
            hpred_n_k hpred_m_k)
  exact hgen n.toPeano first n m rfl h.symm

/-- Equivalent starting points yield pointwise-equivalent `getElementsFrom`
walks of the same length. -/
theorem getElementsFrom_rel_of_equivalent_first (first first'
    subtractiveCommonDifference : Decimal) (n : Decimal)
    (h : first ≈ first') :
    Sequences.List.SameLengthElementwiseRelation (· ≈ ·)
      (getElementsFrom first subtractiveCommonDifference n)
      (getElementsFrom first' subtractiveCommonDifference n) := by
  have hgen :
      ∀ k : Peano, ∀ (first first' : Decimal)
        (n : Decimal),
        n.toPeano = k → first ≈ first' →
          Sequences.List.SameLengthElementwiseRelation (· ≈ ·)
            (getElementsFrom first subtractiveCommonDifference n)
            (getElementsFrom first' subtractiveCommonDifference n) := by
    intro k
    induction k with
    | zero =>
      intro first first' n hn _hfirst
      have hz : n ≈ zero :=
        equivalent_of_toPeano_eq
          (hn.trans toPeano_zero.symm)
      have hexpand :
          getElementsFrom first subtractiveCommonDifference n =
            Sequences.List.empty := by
        conv => lhs; unfold getElementsFrom
        simp only [hz, ↓reduceDIte]
      have hexpand' :
          getElementsFrom first' subtractiveCommonDifference n =
            Sequences.List.empty := by
        conv => lhs; unfold getElementsFrom
        simp only [hz, ↓reduceDIte]
      rw [hexpand, hexpand']
      exact Sequences.List.SameLengthElementwiseRelation.empty
    | successor k ih =>
      intro first first' n hn hfirst
      have hne0 : n.toPeano ≠ Peano.zero := by
        rw [hn]
        exact Peano.successor_ne_zero k
      have hne : ¬ n ≈ zero :=
        not_equivalent_zero_of_toPeano_ne_zero n hne0
      obtain ⟨hne_peano, hpred⟩ :=
        predecessor_toPeano n hne
      have hpred_k : (n.predecessor hne).toPeano = k := by
        rw [hpred]
        apply Eq.symm
        apply Peano.successor_injective
        rw [Peano.successor_predecessor n.toPeano hne_peano, hn]
      have hexpand :
          getElementsFrom first subtractiveCommonDifference n =
            Sequences.List.firstElement first
              (match trySubtract first subtractiveCommonDifference with
               | none => Sequences.List.empty
               | some next =>
                 getElementsFrom next subtractiveCommonDifference
                   (n.predecessor hne)) := by
        conv => lhs; unfold getElementsFrom
        simp only [hne, ↓reduceDIte]
      have hexpand' :
          getElementsFrom first' subtractiveCommonDifference n =
            Sequences.List.firstElement first'
              (match trySubtract first' subtractiveCommonDifference with
               | none => Sequences.List.empty
               | some next =>
                 getElementsFrom next subtractiveCommonDifference
                   (n.predecessor hne)) := by
        conv => lhs; unfold getElementsFrom
        simp only [hne, ↓reduceDIte]
      rw [hexpand, hexpand']
      have hrel :=
        trySubtract_rel_of_equivalent_left first first'
          subtractiveCommonDifference hfirst
      match hs : trySubtract first subtractiveCommonDifference,
            hs' : trySubtract first' subtractiveCommonDifference with
      | none, none =>
        exact Sequences.List.SameLengthElementwiseRelation.firstElement hfirst
          Sequences.List.SameLengthElementwiseRelation.empty
      | some next, some next' =>
        have hrel' : Option.Rel (· ≈ ·) (some next) (some next') := by
          rw [← hs, ← hs']
          exact hrel
        have hnext : next ≈ next' := by
          cases hrel' with
          | some hxy => exact hxy
        exact Sequences.List.SameLengthElementwiseRelation.firstElement hfirst
          (ih next next' (n.predecessor hne) hpred_k hnext)
      | none, some next' =>
        have hrel' : Option.Rel (· ≈ ·) none (some next') := by
          rw [← hs, ← hs']
          exact hrel
        cases hrel'
      | some next, none =>
        have hrel' : Option.Rel (· ≈ ·) (some next) none := by
          rw [← hs, ← hs']
          exact hrel
        cases hrel'
  exact hgen n.toPeano first first' n rfl h

/-- Expanding `getElementsFrom` at a positive Peano length. -/
theorem getElementsFrom_of_toPeano_successor (first subtractiveCommonDifference :
    Decimal) (n : Decimal) (k : Peano)
    (hn : n.toPeano = Peano.successor k) :
    ∃ (hne : ¬ n ≈ zero),
      getElementsFrom first subtractiveCommonDifference n =
        Sequences.List.firstElement first
          (match trySubtract first subtractiveCommonDifference with
           | none => Sequences.List.empty
           | some next =>
             getElementsFrom next subtractiveCommonDifference
               (n.predecessor hne)) ∧
      (n.predecessor hne).toPeano = k := by
  have hne0 : n.toPeano ≠ Peano.zero := by
    rw [hn]
    exact Peano.successor_ne_zero k
  have hne : ¬ n ≈ zero :=
    not_equivalent_zero_of_toPeano_ne_zero n hne0
  obtain ⟨hne_peano, hpred⟩ := predecessor_toPeano n hne
  refine ⟨hne, ?_, ?_⟩
  · conv => lhs; unfold getElementsFrom
    simp only [hne, ↓reduceDIte]
  · rw [hpred]
    apply Eq.symm
    apply Peano.successor_injective
    rw [Peano.successor_predecessor n.toPeano hne_peano, hn]

/-- Expanding `getElementsFrom` when the subtractive step succeeds. -/
theorem getElementsFrom_succ_of_trySubtract (first subtractiveCommonDifference
    next : Decimal) (n : Decimal) (k : Peano)
    (hn : n.toPeano = Peano.successor k)
    (h : trySubtract first subtractiveCommonDifference = some next) :
    ∃ (hne : ¬ n ≈ zero),
      getElementsFrom first subtractiveCommonDifference n =
        Sequences.List.firstElement first
          (getElementsFrom next subtractiveCommonDifference
            (n.predecessor hne)) ∧
      (n.predecessor hne).toPeano = k := by
  obtain ⟨hne, hexpand, hpred⟩ :=
    getElementsFrom_of_toPeano_successor first subtractiveCommonDifference n k hn
  refine ⟨hne, ?_, hpred⟩
  rw [hexpand, h]

/-- Decimal and Peano `getElementsFrom` walks have the same length. -/
theorem getElementsFrom_length_eq_peano_getElementsFrom
    (first subtractiveCommonDifference : Decimal)
    (n : Decimal) :
    (getElementsFrom first subtractiveCommonDifference n).length =
      (Peano.Progressions.ArithmeticDecreasing.getElementsFrom
        first.toPeano subtractiveCommonDifference.toPeano n.toPeano).length := by
  have hgen :
      ∀ k : Peano, ∀ (first : Decimal)
        (n : Decimal),
        n.toPeano = k →
          (getElementsFrom first subtractiveCommonDifference n).length =
            (Peano.Progressions.ArithmeticDecreasing.getElementsFrom
              first.toPeano subtractiveCommonDifference.toPeano k).length := by
    intro k
    induction k with
    | zero =>
      intro first n hn
      have hz : n ≈ zero :=
        equivalent_of_toPeano_eq
          (hn.trans toPeano_zero.symm)
      have hexpand :
          getElementsFrom first subtractiveCommonDifference n =
            Sequences.List.empty := by
        conv => lhs; unfold getElementsFrom
        simp only [hz, ↓reduceDIte]
      rw [hexpand]
      change
          Sequences.List.empty.length =
            (Peano.Progressions.ArithmeticDecreasing.getElementsFrom
              first.toPeano subtractiveCommonDifference.toPeano
              Peano.zero).length
      rfl
    | successor k ih =>
      intro first n hn
      have hne0 : n.toPeano ≠ Peano.zero := by
        rw [hn]
        exact Peano.successor_ne_zero k
      have hne : ¬ n ≈ zero :=
        not_equivalent_zero_of_toPeano_ne_zero n hne0
      obtain ⟨hne_peano, hpred⟩ :=
        predecessor_toPeano n hne
      have hpred_k : (n.predecessor hne).toPeano = k := by
        rw [hpred]
        apply Eq.symm
        apply Peano.successor_injective
        rw [Peano.successor_predecessor n.toPeano hne_peano, hn]
      have hexpand :
          getElementsFrom first subtractiveCommonDifference n =
            Sequences.List.firstElement first
              (match trySubtract first subtractiveCommonDifference with
               | none => Sequences.List.empty
               | some next =>
                 getElementsFrom next subtractiveCommonDifference
                   (n.predecessor hne)) := by
        conv => lhs; unfold getElementsFrom
        simp only [hne, ↓reduceDIte]
      have hmap := trySubtract_map_toPeano first subtractiveCommonDifference
      match hs : trySubtract first subtractiveCommonDifference with
      | none =>
        have hs_peano :
            Peano.trySubtract first.toPeano
              subtractiveCommonDifference.toPeano = none := by
          simpa [hs, Option.map] using hmap.symm
        have hexpand' :
            getElementsFrom first subtractiveCommonDifference n =
              Sequences.List.firstElement first Sequences.List.empty := by
          rw [hexpand, hs]
        rw [hexpand', Sequences.List.length_firstElement]
        change
            Sequences.List.empty.length.successor =
              (Peano.Progressions.ArithmeticDecreasing.getElementsFrom
                first.toPeano subtractiveCommonDifference.toPeano
                (Peano.successor k)).length
        simp only [Peano.Progressions.ArithmeticDecreasing.getElementsFrom,
          hs_peano]
        change
            Peano.one =
              (Sequences.List.firstElement first.toPeano
                Sequences.List.empty).length
        rw [Sequences.List.length_firstElement]
        rfl
      | some next =>
        have hs_peano :
            Peano.trySubtract first.toPeano
              subtractiveCommonDifference.toPeano = some next.toPeano := by
          simpa [hs, Option.map] using hmap.symm
        have hexpand' :
            getElementsFrom first subtractiveCommonDifference n =
              Sequences.List.firstElement first
                (getElementsFrom next subtractiveCommonDifference
                  (n.predecessor hne)) := by
          rw [hexpand, hs]
        rw [hexpand', Sequences.List.length_firstElement]
        have ih' := ih next (n.predecessor hne) hpred_k
        have hpeano_expand :
            Peano.Progressions.ArithmeticDecreasing.getElementsFrom
                first.toPeano subtractiveCommonDifference.toPeano
                (Peano.successor k) =
              Sequences.List.firstElement first.toPeano
                (Peano.Progressions.ArithmeticDecreasing.getElementsFrom
                  next.toPeano subtractiveCommonDifference.toPeano k) := by
          simp only [Peano.Progressions.ArithmeticDecreasing.getElementsFrom,
            hs_peano]
        rw [hpeano_expand, Sequences.List.length_firstElement, ih']
  exact hgen n.toPeano first n rfl

/-- If a list continues decreasing-arithmetically after `prev`, the recovered
last element is equivalent to `lastElementFrom`, and whenever subtracting the
common difference from `prev` succeeds the continuation is pointwise equivalent
to the corresponding `getElementsFrom` walk. -/
theorem rel_getElementsFrom_of_tryLastOfArithmeticContinuation
    (prev diff : Decimal) (rest : Sequences.List Decimal) (last : Decimal)
    (h : tryLastOfArithmeticContinuation prev diff rest = some last) :
    last ≈
        lastElementFrom prev diff
          (fromPeano rest.length).successor ∧
      ∀ next, trySubtract prev diff = some next →
        Sequences.List.SameLengthElementwiseRelation (· ≈ ·)
          (getElementsFrom next diff
            (fromPeano rest.length))
          rest := by
  induction rest generalizing prev last with
  | empty =>
    simp only [tryLastOfArithmeticContinuation] at h
    injection h with heq
    constructor
    · subst heq
      apply equivalent_of_toPeano_eq
      rw [lastElementFrom_toPeano, successor_toPeano,
        toPeano_fromPeano]
      change prev.toPeano =
        Peano.Progressions.ArithmeticDecreasing.lastElementFrom
          prev.toPeano diff.toPeano Peano.one
      rfl
    · intro next _hs
      have hz :
          fromPeano Peano.zero ≈
            zero :=
        equivalent_of_toPeano_eq
          ((toPeano_fromPeano
              Peano.zero).trans
            toPeano_zero.symm)
      have hexpand :
          getElementsFrom next diff
              (fromPeano Peano.zero) =
            Sequences.List.empty := by
        conv => lhs; unfold getElementsFrom
        simp only [hz, ↓reduceDIte]
      change Sequences.List.SameLengthElementwiseRelation (· ≈ ·)
        (getElementsFrom next diff
          (fromPeano
            (Sequences.List.empty : Sequences.List Decimal).length))
        Sequences.List.empty
      rw [show (Sequences.List.empty : Sequences.List Decimal).length =
          Peano.zero from rfl, hexpand]
      exact Sequences.List.SameLengthElementwiseRelation.empty
  | firstElement x xs ih =>
    simp only [tryLastOfArithmeticContinuation] at h
    match hs : trySubtract prev x with
    | none =>
      simp only [hs] at h
      nomatch h
    | some d =>
      simp only [hs] at h
      by_cases hd : d ≈ diff
      · rw [show (if d ≈ diff then
              tryLastOfArithmeticContinuation x diff xs
            else none) =
            tryLastOfArithmeticContinuation x diff xs from by
              simp only [hd, ↓reduceIte]] at h
        obtain ⟨hlast, hxs⟩ := ih x last h
        have hx : prev ≈ x + diff :=
          Setoid.trans (eq_of_trySubtract_add x prev d hs)
            (equivalent_add (Setoid.refl x) hd)
        have hlen := Sequences.List.length_firstElement x xs
        constructor
        · have h1 :
              last ≈
                lastElementFrom x diff
                  (fromPeano xs.length).successor :=
            hlast
          have h2 :
              lastElementFrom x diff
                  (fromPeano xs.length).successor ≈
                lastElementFrom prev diff
                  (fromPeano
                    (Sequences.List.firstElement x xs).length).successor := by
            apply equivalent_of_toPeano_eq
            rw [lastElementFrom_toPeano, lastElementFrom_toPeano,
              successor_toPeano,
              successor_toPeano,
              toPeano_fromPeano,
              toPeano_fromPeano, hlen]
            have hs_peano :
                Peano.trySubtract prev.toPeano diff.toPeano =
                  some x.toPeano := by
              have hadd : prev.toPeano = x.toPeano + diff.toPeano := by
                rw [← add_toPeano, toPeano_eq_of_equivalent hx]
              rw [hadd]
              exact Peano.trySubtract_add_right x.toPeano diff.toPeano
            exact
              (Peano.Progressions.ArithmeticDecreasing.lastElementFrom_succ_succ_of_trySubtract
                prev.toPeano diff.toPeano x.toPeano xs.length hs_peano).symm
          exact Setoid.trans h1 h2
        · intro next hs_next
          have hnext_x : next ≈ x := by
            have hrel := trySubtract_of_equivalent_add_right hx
            have hrel' : Option.Rel (· ≈ ·) (some next) (some x) := by
              rw [← hs_next]
              exact hrel
            cases hrel' with
            | some hxy => exact hxy
          have hn :
              (fromPeano
                  (Sequences.List.firstElement x xs).length).toPeano =
                Peano.successor xs.length := by
            rw [toPeano_fromPeano, hlen]
          have hmid :
              Sequences.List.SameLengthElementwiseRelation (· ≈ ·)
                (getElementsFrom next diff
                  (fromPeano
                    (Sequences.List.firstElement x xs).length))
                (getElementsFrom x diff
                  (fromPeano
                    (Sequences.List.firstElement x xs).length)) :=
            getElementsFrom_rel_of_equivalent_first next x diff
              (fromPeano
                (Sequences.List.firstElement x xs).length)
              hnext_x
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
                  by_cases hd' : d' ≈ diff
                  · have hx' : x ≈ y + diff :=
                      Setoid.trans (eq_of_trySubtract_add y x d' hsy)
                        (equivalent_add (Setoid.refl y) hd')
                    have hrel := trySubtract_of_equivalent_add_right hx'
                    obtain ⟨z, hz, _⟩ :=
                      InfiniteArithmetic.exists_of_option_rel_some hrel
                    rw [hsx] at hz
                    nomatch hz
                  · simp only [hd', ↓reduceIte] at h
                    nomatch h
            cases hxs_empty
            obtain ⟨hne, hexpand, _⟩ :=
              getElementsFrom_of_toPeano_successor x diff
                (fromPeano
                  (Sequences.List.firstElement x Sequences.List.empty).length)
                Peano.zero hn
            have hexpand' :
                getElementsFrom x diff
                    (fromPeano
                      (Sequences.List.firstElement x
                        Sequences.List.empty).length) =
                  Sequences.List.firstElement x Sequences.List.empty := by
              rw [hexpand, hsx]
            have htail :
                Sequences.List.SameLengthElementwiseRelation (· ≈ ·)
                  (getElementsFrom x diff
                    (fromPeano
                      (Sequences.List.firstElement x
                        Sequences.List.empty).length))
                  (Sequences.List.firstElement x Sequences.List.empty) := by
              rw [hexpand']
              exact Sequences.List.SameLengthElementwiseRelation.firstElement
                (Setoid.refl x)
                Sequences.List.SameLengthElementwiseRelation.empty
            exact Sequences.List.SameLengthElementwiseRelation.trans
              (r := (· ≈ ·)) (s := (· ≈ ·)) (t := (· ≈ ·))
              (fun h1 h2 => Setoid.trans h1 h2) hmid htail
          | some next' =>
            have hxs' := hxs next' hsx
            obtain ⟨hne, hexpand, hpred⟩ :=
              getElementsFrom_succ_of_trySubtract x diff next'
                (fromPeano
                  (Sequences.List.firstElement x xs).length)
                xs.length hn hsx
            have hpred_eq :
                getElementsFrom next' diff
                    ((fromPeano
                        (Sequences.List.firstElement x xs).length).predecessor
                      hne) =
                  getElementsFrom next' diff
                    (fromPeano xs.length) :=
              getElementsFrom_eq_of_toPeano_eq next' diff _ _
                (hpred.trans (toPeano_fromPeano _).symm)
            have htail :
                Sequences.List.SameLengthElementwiseRelation (· ≈ ·)
                  (getElementsFrom x diff
                    (fromPeano
                      (Sequences.List.firstElement x xs).length))
                  (Sequences.List.firstElement x xs) := by
              rw [hexpand, hpred_eq]
              exact Sequences.List.SameLengthElementwiseRelation.firstElement
                (Setoid.refl x) hxs'
            exact Sequences.List.SameLengthElementwiseRelation.trans
              (r := (· ≈ ·)) (s := (· ≈ ·)) (t := (· ≈ ·))
              (fun h1 h2 => Setoid.trans h1 h2) hmid htail
      · simp only [hd, ↓reduceIte] at h
        nomatch h

/-- Length of a progression whose limit is equivalent to `lastElementFrom` of a
full-length decreasing walk. -/
theorem getLength_of_equivalent_lastElementFrom (first
    subtractiveCommonDifference diff last : Decimal)
    (n : Decimal)
    (hne : ¬ n ≈ zero)
    (hd : diff ≈ subtractiveCommonDifference)
    (hdiff : ¬ diff ≈ zero)
    (hl : last ≈ lastElementFrom first subtractiveCommonDifference n)
    (hlen : (getElementsFrom first subtractiveCommonDifference n).length =
      n.toPeano) :
    getLength {
      first := some first
      subtractiveCommonDifference := diff
      limit := last
      subtractiveCommonDifference_ne_zero := hdiff
    } ≈ n := by
  apply equivalent_of_toPeano_eq
  have hstruct :
      toPeano {
        first := some first
        subtractiveCommonDifference := diff
        limit := last
        subtractiveCommonDifference_ne_zero := hdiff
      } =
        {
          first := some first.toPeano
          subtractiveCommonDifference := diff.toPeano
          limit := last.toPeano
          subtractiveCommonDifference_ne_zero :=
            toPeano_ne_zero_of_not_equivalent_zero hdiff
        } := by
    simp only [toPeano]
  rw [getLength_toPeano, hstruct]
  have hlim :
      last.toPeano =
        Peano.Progressions.ArithmeticDecreasing.lastElementFrom
          first.toPeano diff.toPeano n.toPeano := by
    rw [toPeano_eq_of_equivalent hl, lastElementFrom_toPeano,
      toPeano_eq_of_equivalent hd]
  have hlen_peano :
      (Peano.Progressions.ArithmeticDecreasing.getElementsFrom
          first.toPeano diff.toPeano n.toPeano).length =
        n.toPeano := by
    have hlen' :
        (Peano.Progressions.ArithmeticDecreasing.getElementsFrom
            first.toPeano subtractiveCommonDifference.toPeano
            n.toPeano).length =
          n.toPeano := by
      rw [← getElementsFrom_length_eq_peano_getElementsFrom first
        subtractiveCommonDifference n, hlen]
    have hdiff_peano : diff.toPeano = subtractiveCommonDifference.toPeano :=
      toPeano_eq_of_equivalent hd
    rw [hdiff_peano]
    exact hlen'
  rw [hlim]
  exact
    Peano.Progressions.ArithmeticDecreasing.getLength_lastElementFrom
      first.toPeano diff.toPeano
      (toPeano_ne_zero_of_not_equivalent_zero hdiff)
      n.toPeano
      (toPeano_ne_zero_of_not_equivalent_zero hne)
      hlen_peano

/-- When the limit is equivalent to `lastElementFrom` of a positive length, the
effective first element is `some first`. -/
theorem effectiveFirst_of_equivalent_lastElementFrom (first
    subtractiveCommonDifference diff last : Decimal)
    (n : Decimal)
    (_hne : ¬ n ≈ zero)
    (hdiff : ¬ diff ≈ zero)
    (hl : last ≈ lastElementFrom first subtractiveCommonDifference n) :
    effectiveFirst {
      first := some first
      subtractiveCommonDifference := diff
      limit := last
      subtractiveCommonDifference_ne_zero := hdiff
    } = some first := by
  simp only [effectiveFirst]
  have hle_peano :
      Peano.Progressions.ArithmeticDecreasing.lastElementFrom
          first.toPeano subtractiveCommonDifference.toPeano n.toPeano ≤
        first.toPeano :=
    Peano.Progressions.ArithmeticDecreasing.lastElementFrom_le
      first.toPeano subtractiveCommonDifference.toPeano n.toPeano
  have hle : last ≤ first := by
    apply (le_iff_toPeano_le last first).mpr
    rw [toPeano_eq_of_equivalent hl, lastElementFrom_toPeano]
    exact hle_peano
  simp only [hle, ↓reduceIte]

/-- `getElements` recovers a list pointwise equivalent to the original from a
successful `tryFromElements`. Exact equality may fail because Decimal
subtraction recovers steps only up to representation. -/
theorem getElements_tryFromElements (elements : Sequences.List Decimal)
    (hge : Peano.two ≤ elements.length)
    (p : ArithmeticDecreasing)
    (h : tryFromElements elements hge = some p) :
    Sequences.List.SameLengthElementwiseRelation (· ≈ ·) (getElements p) elements := by
  match helem : elements with
  | .empty =>
    subst helem
    exact (Peano.not_two_le_zero (by
      change Peano.two ≤ Peano.zero
      exact hge)).elim
  | .firstElement _ .empty =>
    subst helem
    exact (Peano.not_two_le_one (by
      change Peano.two ≤ Peano.one
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
      by_cases hdiff0 : diff ≈ zero
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
            simp only [tryLastOfArithmeticContinuation, hs]
            have hdrefl : diff ≈ diff := Setoid.refl _
            simp only [hdrefl, ↓reduceIte, hl]
          obtain ⟨hlast, hrest_forall⟩ :=
            rel_getElementsFrom_of_tryLastOfArithmeticContinuation x diff
              (Sequences.List.firstElement y ys) last hcont
          have hx : x ≈ y + diff :=
            eq_of_trySubtract_add y x diff hs
          have hrel := trySubtract_of_equivalent_add_right hx
          obtain ⟨y', hy_eq, hy_rel⟩ :=
            InfiniteArithmetic.exists_of_option_rel_some hrel
          have hrest := hrest_forall y' hy_eq
          let n : Decimal :=
            (fromPeano (Sequences.List.firstElement y ys).length).successor
          have hne : ¬ n ≈ zero := by
            intro heq
            have hpeano := toPeano_eq_of_equivalent heq
            rw [successor_toPeano, toPeano_fromPeano, toPeano_zero] at hpeano
            exact Peano.successor_ne_zero _ hpeano
          have hf : effectiveFirst
              {
                first := some x
                subtractiveCommonDifference := diff
                limit := last
                subtractiveCommonDifference_ne_zero := hdiff0
              } = some x :=
            effectiveFirst_of_equivalent_lastElementFrom x diff diff last n hne
              hdiff0 hlast
          have hn :
              n.toPeano =
                Peano.successor
                  (Sequences.List.firstElement y ys).length := by
            rw [successor_toPeano, toPeano_fromPeano]
          obtain ⟨hne_n, hexpand, hpred⟩ :=
            getElementsFrom_succ_of_trySubtract x diff y' n
              (Sequences.List.firstElement y ys).length hn hy_eq
          have hpred_eq :
              getElementsFrom y' diff (n.predecessor hne_n) =
                getElementsFrom y' diff
                  (fromPeano
                    (Sequences.List.firstElement y ys).length) :=
            getElementsFrom_eq_of_toPeano_eq y' diff _ _
              (hpred.trans (toPeano_fromPeano _).symm)
          have hlen_walk :
              (getElementsFrom x diff n).length = n.toPeano := by
            rw [hexpand, hpred_eq, Sequences.List.length_firstElement, hn]
            have hlen_tail :=
              length_eq_of_SameLengthElementwiseRelation (r := (· ≈ ·)) hrest
            rw [hlen_tail]
          have hlenp :
              getLength
                  {
                    first := some x
                    subtractiveCommonDifference := diff
                    limit := last
                    subtractiveCommonDifference_ne_zero := hdiff0
                  } ≈ n :=
            getLength_of_equivalent_lastElementFrom x diff diff last n hne
              (Setoid.refl diff) hdiff0 hlast hlen_walk
          have hget :
              getElements
                  {
                    first := some x
                    subtractiveCommonDifference := diff
                    limit := last
                    subtractiveCommonDifference_ne_zero := hdiff0
                  } =
                getElementsFrom x diff
                  (getLength
                    {
                      first := some x
                      subtractiveCommonDifference := diff
                      limit := last
                      subtractiveCommonDifference_ne_zero := hdiff0
                    }) := by
            simp only [getElements, hf]
          rw [hget]
          have hlen_toPeano :
              (getLength
                  {
                    first := some x
                    subtractiveCommonDifference := diff
                    limit := last
                    subtractiveCommonDifference_ne_zero := hdiff0
                  }).toPeano =
                n.toPeano :=
            toPeano_eq_of_equivalent hlenp
          have hget' :
              getElementsFrom x diff
                  (getLength
                    {
                      first := some x
                      subtractiveCommonDifference := diff
                      limit := last
                      subtractiveCommonDifference_ne_zero := hdiff0
                    }) =
                getElementsFrom x diff n :=
            getElementsFrom_eq_of_toPeano_eq x diff _ _ hlen_toPeano
          rw [hget', hexpand, hpred_eq]
          have hmid :
              Sequences.List.SameLengthElementwiseRelation (· ≈ ·)
                (getElementsFrom y' diff
                  (fromPeano
                    (Sequences.List.firstElement y ys).length))
                (Sequences.List.firstElement y ys) :=
            hrest
          exact Sequences.List.SameLengthElementwiseRelation.firstElement
            (Setoid.refl x) hmid

/-- If `trySubtract first diff = some next`, then `trySubtract first next`
recovers a value equivalent to `diff`. -/
theorem trySubtract_rel_comm (diff first next : Decimal)
    (h : trySubtract first diff = some next) :
    Option.Rel (· ≈ ·) (trySubtract first next) (some diff) :=
  trySubtract_of_equivalent_add_right
    (eq_of_trySubtract_add diff first next h)

/-- A `getElementsFrom` walk of length at least two has a defined first
subtractive step. -/
theorem trySubtract_eq_some_of_getElementsFrom_length_ge_two
    (first subtractiveCommonDifference : Decimal) (n : Decimal)
    (hge : Peano.two ≤
      (getElementsFrom first subtractiveCommonDifference n).length) :
    ∃ next, trySubtract first subtractiveCommonDifference = some next := by
  by_cases hz : n ≈ zero
  · have hexpand :
        getElementsFrom first subtractiveCommonDifference n =
          Sequences.List.empty := by
      conv => lhs; unfold getElementsFrom
      simp only [hz, ↓reduceDIte]
    rw [hexpand] at hge
    exact (Peano.not_two_le_zero (by
      change Peano.two ≤ Peano.zero
      exact hge)).elim
  · have hexpand :
        getElementsFrom first subtractiveCommonDifference n =
          Sequences.List.firstElement first
            (match trySubtract first subtractiveCommonDifference with
             | none => Sequences.List.empty
             | some next =>
               getElementsFrom next subtractiveCommonDifference
                 (n.predecessor hz)) := by
      conv => lhs; unfold getElementsFrom
      simp only [hz, ↓reduceDIte]
    match hs : trySubtract first subtractiveCommonDifference with
    | none =>
      have hexpand' :
          getElementsFrom first subtractiveCommonDifference n =
            Sequences.List.firstElement first Sequences.List.empty := by
        rw [hexpand, hs]
      have hlen :
          (getElementsFrom first subtractiveCommonDifference n).length =
            Peano.one := by
        rw [hexpand', Sequences.List.length_firstElement]
        rfl
      rw [hlen] at hge
      exact (Peano.not_two_le_one hge).elim
    | some next =>
      exact ⟨next, rfl⟩

/-- Continuing a decreasing arithmetic walk from `prev` by `getElementsFrom`
recovers a last element equivalent to `lastElementFrom`, when the first step
from `prev` is defined and the reconstructed difference is equivalent to the
walk difference. -/
theorem tryLastOfArithmeticContinuation_getElementsFrom
    (prev subtractiveCommonDifference diff next : Decimal)
    (n : Decimal)
    (hd : diff ≈ subtractiveCommonDifference)
    (h : trySubtract prev subtractiveCommonDifference = some next) :
    Option.Rel (· ≈ ·)
      (tryLastOfArithmeticContinuation prev diff
        (getElementsFrom next subtractiveCommonDifference n))
      (some (lastElementFrom prev subtractiveCommonDifference n.successor)) := by
  have hgen :
      ∀ k : Peano, ∀ (prev next : Decimal)
        (n : Decimal),
        n.toPeano = k →
          trySubtract prev subtractiveCommonDifference = some next →
            Option.Rel (· ≈ ·)
              (tryLastOfArithmeticContinuation prev diff
                (getElementsFrom next subtractiveCommonDifference n))
              (some (lastElementFrom prev subtractiveCommonDifference
                n.successor)) := by
    intro k
    induction k with
    | zero =>
      intro prev next n hn hs
      have hz : n ≈ zero :=
        equivalent_of_toPeano_eq (hn.trans toPeano_zero.symm)
      have hexpand :
          getElementsFrom next subtractiveCommonDifference n =
            Sequences.List.empty := by
        conv => lhs; unfold getElementsFrom
        simp only [hz, ↓reduceDIte]
      rw [hexpand, tryLastOfArithmeticContinuation]
      apply Option.Rel.some
      apply equivalent_of_toPeano_eq
      rw [lastElementFrom_toPeano, successor_toPeano, hn]
      change prev.toPeano =
        Peano.Progressions.ArithmeticDecreasing.lastElementFrom
          prev.toPeano subtractiveCommonDifference.toPeano
          (Peano.successor Peano.zero)
      rfl
    | successor k ih =>
      intro prev next n hn hs
      have hne0 : n.toPeano ≠ Peano.zero := by
        rw [hn]
        exact Peano.successor_ne_zero k
      have hne : ¬ n ≈ zero :=
        not_equivalent_zero_of_toPeano_ne_zero n hne0
      obtain ⟨hne_peano, hpred⟩ := predecessor_toPeano n hne
      have hpred_k : (n.predecessor hne).toPeano = k := by
        rw [hpred]
        apply Eq.symm
        apply Peano.successor_injective
        rw [Peano.successor_predecessor n.toPeano hne_peano, hn]
      have hexpand :
          getElementsFrom next subtractiveCommonDifference n =
            Sequences.List.firstElement next
              (match trySubtract next subtractiveCommonDifference with
               | none => Sequences.List.empty
               | some next' =>
                 getElementsFrom next' subtractiveCommonDifference
                   (n.predecessor hne)) := by
        conv => lhs; unfold getElementsFrom
        simp only [hne, ↓reduceDIte]
      have hrel := trySubtract_rel_comm subtractiveCommonDifference prev next hs
      obtain ⟨d, hd_eq, hd_approx⟩ :=
        InfiniteArithmetic.exists_of_option_rel_some hrel
      have hd' : d ≈ diff := Setoid.trans hd_approx (Setoid.symm hd)
      match hs' : trySubtract next subtractiveCommonDifference with
      | none =>
        have hexpand' :
            getElementsFrom next subtractiveCommonDifference n =
              Sequences.List.firstElement next Sequences.List.empty := by
          rw [hexpand, hs']
        rw [hexpand', tryLastOfArithmeticContinuation, hd_eq]
        simp only [hd', ↓reduceIte, tryLastOfArithmeticContinuation]
        apply Option.Rel.some
        apply equivalent_of_toPeano_eq
        rw [lastElementFrom_toPeano, successor_toPeano, hn]
        have hs_peano :
            Peano.trySubtract prev.toPeano
              subtractiveCommonDifference.toPeano = some next.toPeano := by
          simpa [hs, Option.map] using
            (trySubtract_map_toPeano prev subtractiveCommonDifference).symm
        have hs'_peano :
            Peano.trySubtract next.toPeano
              subtractiveCommonDifference.toPeano = none := by
          simpa [hs', Option.map] using
            (trySubtract_map_toPeano next subtractiveCommonDifference).symm
        have hlast :
            Peano.Progressions.ArithmeticDecreasing.lastElementFrom
                prev.toPeano subtractiveCommonDifference.toPeano
                (Peano.successor (Peano.successor k)) =
              next.toPeano := by
          rw [Peano.Progressions.ArithmeticDecreasing.lastElementFrom_succ_succ_of_trySubtract
            prev.toPeano subtractiveCommonDifference.toPeano next.toPeano k
            hs_peano]
          simp only [Peano.Progressions.ArithmeticDecreasing.lastElementFrom,
            hs'_peano]
          match k with
          | .zero => rfl
          | .successor _ => rfl
        exact hlast.symm
      | some next' =>
        have hexpand' :
            getElementsFrom next subtractiveCommonDifference n =
              Sequences.List.firstElement next
                (getElementsFrom next' subtractiveCommonDifference
                  (n.predecessor hne)) := by
          rw [hexpand, hs']
        rw [hexpand', tryLastOfArithmeticContinuation, hd_eq]
        simp only [hd', ↓reduceIte]
        have ih' := ih next next' (n.predecessor hne) hpred_k hs'
        obtain ⟨last', hlast_eq, hlast_approx⟩ :=
          InfiniteArithmetic.exists_of_option_rel_some ih'
        rw [hlast_eq]
        apply Option.Rel.some
        refine Setoid.trans hlast_approx ?_
        apply equivalent_of_toPeano_eq
        rw [lastElementFrom_toPeano, lastElementFrom_toPeano,
          successor_toPeano, successor_toPeano, hpred_k, hn]
        have hs_peano :
            Peano.trySubtract prev.toPeano
              subtractiveCommonDifference.toPeano = some next.toPeano := by
          simpa [hs, Option.map] using
            (trySubtract_map_toPeano prev subtractiveCommonDifference).symm
        exact
          (Peano.Progressions.ArithmeticDecreasing.lastElementFrom_succ_succ_of_trySubtract
            prev.toPeano subtractiveCommonDifference.toPeano next.toPeano k
            hs_peano).symm
  exact hgen n.toPeano prev next n rfl h

/-- Reconstructing from `getElementsFrom` of Peano-length at least two recovers
a progression with the same start, an equivalent subtractive common difference,
and a limit equivalent to `lastElementFrom`. -/
theorem tryFromElements_getElementsFrom_ge_two
    (first subtractiveCommonDifference : Decimal)
    (hdiff0 : ¬ subtractiveCommonDifference ≈ zero) (n : Decimal)
    (hge : Peano.two ≤ n.toPeano)
    (hLen : Peano.two ≤
        (getElementsFrom first subtractiveCommonDifference n).length) :
    ∃ (q : ArithmeticDecreasing),
      tryFromElements (getElementsFrom first subtractiveCommonDifference n) hLen =
        some q ∧
      q.first = some first ∧
      q.subtractiveCommonDifference ≈ subtractiveCommonDifference ∧
      q.limit ≈ lastElementFrom first subtractiveCommonDifference n := by
  obtain ⟨m, hm⟩ := Peano.eq_succ_succ_of_two_le n.toPeano hge
  obtain ⟨next, hs⟩ :=
    trySubtract_eq_some_of_getElementsFrom_length_ge_two first
      subtractiveCommonDifference n hLen
  obtain ⟨hne, hexpand, hpred⟩ :=
    getElementsFrom_succ_of_trySubtract first subtractiveCommonDifference next n
      (Peano.successor m) hm hs
  have hne' : ¬ n.predecessor hne ≈ zero :=
    not_equivalent_zero_of_toPeano_ne_zero _ (by
      rw [hpred]
      exact Peano.successor_ne_zero m)
  obtain ⟨hne_peano', hpred'⟩ := predecessor_toPeano (n.predecessor hne) hne'
  have hpred_m : ((n.predecessor hne).predecessor hne').toPeano = m := by
    rw [hpred']
    apply Eq.symm
    apply Peano.successor_injective
    rw [Peano.successor_predecessor (n.predecessor hne).toPeano
      hne_peano', hpred]
  revert hLen
  rw [hexpand]
  intro hLen
  -- Expand the second step so `tryFromElements` sees two leading elements.
  have hexpand2 :
      getElementsFrom next subtractiveCommonDifference (n.predecessor hne) =
        Sequences.List.firstElement next
          (match trySubtract next subtractiveCommonDifference with
           | none => Sequences.List.empty
           | some next' =>
             getElementsFrom next' subtractiveCommonDifference
               ((n.predecessor hne).predecessor hne')) := by
    conv => lhs; unfold getElementsFrom
    simp only [hne', ↓reduceDIte]
  revert hLen
  rw [hexpand2]
  intro hLen
  simp only [tryFromElements]
  have hrel := trySubtract_rel_comm subtractiveCommonDifference first next hs
  obtain ⟨diff, hdiff_eq, hdiff_approx⟩ :=
    InfiniteArithmetic.exists_of_option_rel_some hrel
  simp only [hdiff_eq]
  have hdiff_ne : ¬ diff ≈ zero := fun heq =>
    hdiff0 (Setoid.trans (Setoid.symm hdiff_approx) heq)
  split
  · next heq => exact (hdiff_ne heq).elim
  · next hdiff =>
    match hs' : trySubtract next subtractiveCommonDifference with
    | none =>
      simp only [tryLastOfArithmeticContinuation]
      refine ⟨({
          first := some first
          subtractiveCommonDifference := diff
          limit := next
          subtractiveCommonDifference_ne_zero := hdiff
        } : ArithmeticDecreasing), rfl, rfl, hdiff_approx, ?_⟩
      apply equivalent_of_toPeano_eq
      rw [lastElementFrom_toPeano, hm]
      have hs_peano :
          Peano.trySubtract first.toPeano
            subtractiveCommonDifference.toPeano = some next.toPeano := by
        simpa [hs, Option.map] using
          (trySubtract_map_toPeano first subtractiveCommonDifference).symm
      have hs'_peano :
          Peano.trySubtract next.toPeano
            subtractiveCommonDifference.toPeano = none := by
        simpa [hs', Option.map] using
          (trySubtract_map_toPeano next subtractiveCommonDifference).symm
      have hlast :
          Peano.Progressions.ArithmeticDecreasing.lastElementFrom
              first.toPeano subtractiveCommonDifference.toPeano
              (Peano.successor (Peano.successor m)) =
            next.toPeano := by
        rw [Peano.Progressions.ArithmeticDecreasing.lastElementFrom_succ_succ_of_trySubtract
          first.toPeano subtractiveCommonDifference.toPeano next.toPeano m
          hs_peano]
        simp only [Peano.Progressions.ArithmeticDecreasing.lastElementFrom,
          hs'_peano]
        match m with
        | .zero => rfl
        | .successor _ => rfl
      exact hlast.symm
    | some next' =>
      have hlast_rel :=
        tryLastOfArithmeticContinuation_getElementsFrom next
          subtractiveCommonDifference diff next'
          ((n.predecessor hne).predecessor hne') hdiff_approx hs'
      obtain ⟨last, hlast_eq, hlast_approx⟩ :=
        InfiniteArithmetic.exists_of_option_rel_some hlast_rel
      simp only [hlast_eq]
      refine ⟨({
          first := some first
          subtractiveCommonDifference := diff
          limit := last
          subtractiveCommonDifference_ne_zero := hdiff
        } : ArithmeticDecreasing), rfl, rfl, hdiff_approx, ?_⟩
      refine Setoid.trans hlast_approx ?_
      apply equivalent_of_toPeano_eq
      rw [lastElementFrom_toPeano, lastElementFrom_toPeano,
        successor_toPeano, hpred_m, hm]
      have hs_peano :
          Peano.trySubtract first.toPeano
            subtractiveCommonDifference.toPeano = some next.toPeano := by
        simpa [hs, Option.map] using
          (trySubtract_map_toPeano first subtractiveCommonDifference).symm
      exact
        (Peano.Progressions.ArithmeticDecreasing.lastElementFrom_succ_succ_of_trySubtract
          first.toPeano subtractiveCommonDifference.toPeano next.toPeano m
          hs_peano).symm

/-- `getElementsFrom` of an in-range initial segment of a decreasing progression
has Peano length equal to the Peano embedding of the requested length. -/
theorem getElementsFrom_length_of_le_getLength (p : ArithmeticDecreasing)
    (first : Decimal) (hf : effectiveFirst p = some first)
    (n : Decimal)
    (hle : n.toPeano ≤ (getLength p).toPeano) :
    (getElementsFrom first p.subtractiveCommonDifference n).length =
      n.toPeano := by
  have hf_peano :
      Peano.Progressions.ArithmeticDecreasing.effectiveFirst (toPeano p) =
        some first.toPeano := by
    simpa [hf, Option.map] using (effectiveFirst_toPeano p).symm
  have hle' : n.toPeano ≤
      Peano.Progressions.ArithmeticDecreasing.getLength (toPeano p) := by
    rwa [← getLength_toPeano]
  have hf_prog :
      (Peano.Progressions.ArithmeticDecreasing.toProgression
          (toPeano p)).first =
        some first.toPeano :=
    Peano.Progressions.ArithmeticDecreasing.effectiveFirst_eq (toPeano p) ▸
      hf_peano
  have hlen_peano :=
    Peano.Progressions.ArithmeticDecreasing.getElementsFrom_length_of_le_getLength
      (toPeano p) first.toPeano hf_prog n.toPeano hle'
  rw [getElementsFrom_length_eq_peano_getElementsFrom]
  simpa [toPeano] using hlen_peano

/-- The list of elements of a decreasing progression has Peano length equal to
the Peano embedding of `getLength`. -/
theorem getElements_length (p : ArithmeticDecreasing) :
    (getElements p).length = (getLength p).toPeano := by
  match hf : effectiveFirst p with
  | none =>
    have hlen : getLength p ≈ zero :=
      (getLength_eq_zero_iff_effectiveFirst_none p).mpr hf
    simp only [getElements, hf]
    change Peano.zero = (getLength p).toPeano
    exact ((toPeano_eq_of_equivalent hlen).trans toPeano_zero).symm
  | some first =>
    simp only [getElements, hf]
    exact getElementsFrom_length_of_le_getLength p first hf (getLength p)
      (Or.inr rfl)

/-- `tryFromElements` recovers a progression equivalent to `p` from
`getElements p` when `p` has length at least two. -/
theorem tryFromElements_getElements (p : ArithmeticDecreasing)
    (hge : Peano.two ≤ (getLength p).toPeano) :
    ∃ (hLen : Peano.two ≤ (getElements p).length)
      (q : ArithmeticDecreasing),
      tryFromElements (getElements p) hLen = some q ∧ p ≈ q := by
  have hne0 : (getLength p).toPeano ≠ Peano.zero := by
    intro heq
    rw [heq] at hge
    exact Peano.not_two_le_zero hge
  have hne0' : ¬ getLength p ≈ zero :=
    not_equivalent_zero_of_toPeano_ne_zero (getLength p) hne0
  obtain ⟨first, hf⟩ := effectiveFirst_eq_some_of_pos_length p hne0'
  have hget :
      getElements p =
        getElementsFrom first p.subtractiveCommonDifference (getLength p) := by
    simp only [getElements, hf]
  have hLen : Peano.two ≤ (getElements p).length := by
    rw [getElements_length]
    exact hge
  have hLen' : Peano.two ≤
      (getElementsFrom first p.subtractiveCommonDifference
        (getLength p)).length := by
    rw [← hget]
    exact hLen
  obtain ⟨q, htry, hfirst_q, hdiff_q, hlast_q⟩ :=
    tryFromElements_getElementsFrom_ge_two first p.subtractiveCommonDifference
      p.subtractiveCommonDifference_ne_zero (getLength p) hge hLen'
  refine ⟨hLen, q, ?_⟩
  constructor
  · revert hLen
    rw [hget]
    intro hLen
    exact htry
  · have hq_rewrite :
        q = {
          first := some first
          subtractiveCommonDifference := q.subtractiveCommonDifference
          limit := q.limit
          subtractiveCommonDifference_ne_zero :=
            q.subtractiveCommonDifference_ne_zero
        } := by
      cases q with
      | mk f d l h =>
        cases hfirst_q
        rfl
    have hlen_walk :
        (getElementsFrom first p.subtractiveCommonDifference
          (getLength p)).length =
          (getLength p).toPeano :=
      getElementsFrom_length_of_le_getLength p first hf (getLength p)
        (Or.inr rfl)
    have hf_q :
        effectiveFirst q = some first := by
      rw [hq_rewrite]
      exact effectiveFirst_of_equivalent_lastElementFrom first
        p.subtractiveCommonDifference q.subtractiveCommonDifference q.limit
        (getLength p) hne0' q.subtractiveCommonDifference_ne_zero hlast_q
    have hlen_q :
        getLength q ≈ getLength p := by
      rw [hq_rewrite]
      exact getLength_of_equivalent_lastElementFrom first
        p.subtractiveCommonDifference q.subtractiveCommonDifference q.limit
        (getLength p) hne0' hdiff_q q.subtractiveCommonDifference_ne_zero
        hlast_q hlen_walk
    exact equivalence_of_equivalent_params p q first first hf hf_q
      (Setoid.refl first) (Setoid.symm hdiff_q) (Setoid.symm hlen_q)

/-- Recover the first element of a decreasing arithmetic progression from an
element at the given ordinal Decimal index and the subtractive common
difference. At an index equivalent to `one` the element is itself the first;
otherwise add `(fromOrdinal (predecessor index)) * subtractiveCommonDifference`.
Always succeeds. -/
def tryFirstFromIndexedElement
    (index : OrdinalNatural.Decimal) (element subtractiveCommonDifference : Decimal) :
    Option Decimal :=
  if h : index ≈ OrdinalNatural.Decimal.one then
    some element
  else
    some (element + (fromOrdinal (index.predecessor h)) * subtractiveCommonDifference)

/-- Given two ordered indexed elements (`index < index'`) of a prospective
decreasing arithmetic progression, recover the subtractive common difference
`(element - element') / (index' - index)`. Returns `none` when the elements are
not strictly descending or the element gap is not divisible by the index gap. -/
def tryCommonDifferenceFromOrderedIndexedElements
    (index : OrdinalNatural.Decimal) (element : Decimal)
    (index' : OrdinalNatural.Decimal) (element' : Decimal)
    (hlt : index < index') :
    Option Decimal :=
  match trySubtract element element' with
  | none => none
  | some elementDiff =>
    tryDivide elementDiff
      (fromOrdinal (OrdinalNatural.Decimal.subtract index' index hlt))

/-- Reconstruct a decreasing arithmetic progression from two of its elements at
different ordinal Decimal indexes together with the progression length. Returns
`none` when either index exceeds the length, when the recovered subtractive
common difference is equivalent to zero, when the arithmetic walk of that length
cannot be carried out (an intermediate subtraction fails), or when the values
are not consistent with a strictly decreasing arithmetic progression of that
length. Indexes are compared up to Decimal equivalence.

The reconstructed progression uses the recovered first element and subtractive
common difference, and takes the last element of an arithmetic walk of the given
length as the limit. -/
def tryFromTwoElementsAndLength
    (index1 : OrdinalNatural.Decimal) (element1 : Decimal)
    (index2 : OrdinalNatural.Decimal) (element2 : Decimal)
    (length : Decimal)
    (hne : ¬ index1 ≈ index2) :
    Option ArithmeticDecreasing :=
  if fromOrdinal index1 ≤ length then
    if fromOrdinal index2 ≤ length then
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
              if (getElementsFrom first diff length).length = length.toPeano then
                some {
                  first := some first
                  subtractiveCommonDifference := diff
                  limit := lastElementFrom first diff length
                  subtractiveCommonDifference_ne_zero := hdiff
                }
              else
                none
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
              if (getElementsFrom first diff length).length = length.toPeano then
                some {
                  first := some first
                  subtractiveCommonDifference := diff
                  limit := lastElementFrom first diff length
                  subtractiveCommonDifference_ne_zero := hdiff
                }
              else
                none
    else
      none
  else
    none

/-- `fromOrdinal` is monotone with respect to the ordinal Decimal order. -/
theorem fromOrdinal_le_of_lt {a b : OrdinalNatural.Decimal} (h : a < b) :
    fromOrdinal a ≤ fromOrdinal b := by
  apply le_of_toPeano_le
  rw [fromOrdinal_toPeano_eq_fromOrdinal_peano,
    fromOrdinal_toPeano_eq_fromOrdinal_peano]
  exact Peano.fromOrdinal_le_of_lt (OrdinalNatural.Decimal.toPeano_lt_of_lt h)

/-- In-range `getElement` agrees with `getElementFrom` on the effective first. -/
theorem getElement_eq_getElementFrom (p : ArithmeticDecreasing)
    (first : Decimal) (hf : effectiveFirst p = some first)
    (index : OrdinalNatural.Decimal)
    (hle : fromOrdinal index ≤ getLength p) :
    getElement p index hle =
      getElementFrom first p.subtractiveCommonDifference index := by
  have hfirst_eq : p.first = some first := by
    match h : p.first with
    | none =>
      simp only [effectiveFirst, h] at hf
      nomatch hf
    | some first' =>
      simp only [effectiveFirst, h] at hf
      by_cases hle' : p.limit ≤ first'
      · simp only [hle', ↓reduceIte] at hf
        injection hf with heq
        exact congrArg some heq
      · simp only [hle', ↓reduceIte] at hf
        nomatch hf
  have hle_start : p.limit ≤ first := by
    simp only [effectiveFirst, hfirst_eq] at hf
    by_cases hle' : p.limit ≤ first
    · exact hle'
    · simp only [hle', ↓reduceIte] at hf
      nomatch hf
  dsimp only [getElement]
  split
  · next hf_none =>
    rw [hfirst_eq] at hf_none
    nomatch hf_none
  · next start hf_some =>
    have heq : some first = some start := hfirst_eq.symm.trans hf_some
    injection heq with heq'
    subst heq'
    match hcmp : compare first p.limit with
    | .less hlt =>
      cases hle_start with
      | inl hgt =>
        exact (not_lt_of_lt hlt hgt).elim
      | inr heq =>
        have hself : first.toPeano < first.toPeano := by
          have hlt' : first.toPeano < p.limit.toPeano := hlt
          rwa [toPeano_eq_of_equivalent heq] at hlt'
        exact (Peano.not_lt_self _ hself).elim
    | .equivalent _ =>
      rfl
    | .greater _ =>
      rfl

/-- In-range `getElementFrom` agrees with the Peano embedding of `getElementFrom`. -/
theorem getElementFrom_toPeano_of_le (p : ArithmeticDecreasing)
    (first : Decimal) (hf : effectiveFirst p = some first)
    (index : OrdinalNatural.Decimal)
    (hle : fromOrdinal index ≤ getLength p) :
    (getElementFrom first p.subtractiveCommonDifference index).toPeano =
      Peano.Progressions.ArithmeticDecreasing.getElementFrom
        first.toPeano p.subtractiveCommonDifference.toPeano index.toPeano := by
  have hget := getElement_eq_getElementFrom p first hf index hle
  rw [← hget]
  have happrox := getElement_eq p index hle
  have hle_prog := fromOrdinal_le_progression_getLength p index hle
  have htry :=
    Sequences.Progression.tryGetElement_eq_some_getElement
      (toProgression p) (toProgression_finite p) index.toPeano hle_prog
  have hmap := tryGetElement_toPeano p index.toPeano
  rw [htry, Option.map] at hmap
  have hf_peano :
      (Peano.Progressions.ArithmeticDecreasing.toProgression
          (toPeano p)).first =
        some first.toPeano := by
    have heff :
        Peano.Progressions.ArithmeticDecreasing.effectiveFirst (toPeano p) =
          some first.toPeano := by
      simpa [hf, Option.map] using (effectiveFirst_toPeano p).symm
    exact
      Peano.Progressions.ArithmeticDecreasing.effectiveFirst_eq (toPeano p) ▸
        heff
  have hle_peano :
      Peano.fromOrdinal index.toPeano ≤
        Peano.Progressions.ArithmeticDecreasing.getLength (toPeano p) := by
    have hle' := toPeano_le_of_le hle
    rw [fromOrdinal_toPeano_eq_fromOrdinal_peano, getLength_toPeano] at hle'
    exact hle'
  have hpeano_get :=
    Peano.Progressions.ArithmeticDecreasing.getElement_eq_getElementFrom
      (toPeano p) first.toPeano hf_peano index.toPeano hle_peano
  have hpeano_eq :=
    Peano.Progressions.ArithmeticDecreasing.getElement_eq
      (toPeano p) index.toPeano hle_peano
  have hlen_peano :
      Peano.Progressions.ArithmeticDecreasing.getLength (toPeano p) =
        Sequences.Progression.getLength
          (Peano.Progressions.ArithmeticDecreasing.toProgression (toPeano p))
          (Peano.Progressions.ArithmeticDecreasing.toProgression_finite
            (toPeano p)) :=
    Peano.Progressions.ArithmeticDecreasing.getLength_eq (toPeano p)
  have htry_peano :=
    Sequences.Progression.tryGetElement_eq_some_getElement
      (Peano.Progressions.ArithmeticDecreasing.toProgression (toPeano p))
      (Peano.Progressions.ArithmeticDecreasing.toProgression_finite (toPeano p))
      index.toPeano (hlen_peano ▸ hle_peano)
  rw [htry_peano] at hmap
  injection hmap with hmap'
  have hprog_toPeano :
      (Sequences.Progression.getElement (toProgression p)
          (toProgression_finite p) index.toPeano hle_prog).toPeano =
        Sequences.Progression.getElement
          (Peano.Progressions.ArithmeticDecreasing.toProgression (toPeano p))
          (Peano.Progressions.ArithmeticDecreasing.toProgression_finite
            (toPeano p))
          index.toPeano (hlen_peano ▸ hle_peano) :=
    hmap'
  exact
    (toPeano_eq_of_equivalent happrox).trans
      (hprog_toPeano.trans (hpeano_eq.symm.trans hpeano_get))

/-- Advancing from `index` to a larger in-range `index'` subtracts
`(fromOrdinal (index' - index)) * subtractiveCommonDifference` from the element,
up to Decimal equivalence. -/
theorem getElementFrom_eq_add_mul_of_lt (p : ArithmeticDecreasing)
    (first : Decimal) (hf : effectiveFirst p = some first)
    (index index' : OrdinalNatural.Decimal) (hlt : index < index')
    (hle' : fromOrdinal index' ≤ getLength p) :
    getElementFrom first p.subtractiveCommonDifference index ≈
      getElementFrom first p.subtractiveCommonDifference index' +
        (fromOrdinal (OrdinalNatural.Decimal.subtract index' index hlt)) *
          p.subtractiveCommonDifference := by
  have hle : fromOrdinal index ≤ getLength p :=
    le_trans (fromOrdinal_le_of_lt hlt) hle'
  apply equivalent_of_toPeano_eq
  have hindex := getElementFrom_toPeano_of_le p first hf index hle
  have hindex' := getElementFrom_toPeano_of_le p first hf index' hle'
  rw [hindex, add_toPeano, multiply_toPeano, hindex',
    fromOrdinal_toPeano_eq_fromOrdinal_peano]
  obtain ⟨hlt_peano, hsub⟩ :=
    OrdinalNatural.Decimal.subtract_toPeano index' index hlt
  rw [hsub]
  have hf_peano :
      (Peano.Progressions.ArithmeticDecreasing.toProgression
          (toPeano p)).first =
        some first.toPeano := by
    have heff :
        Peano.Progressions.ArithmeticDecreasing.effectiveFirst (toPeano p) =
          some first.toPeano := by
      simpa [hf, Option.map] using (effectiveFirst_toPeano p).symm
    exact
      Peano.Progressions.ArithmeticDecreasing.effectiveFirst_eq (toPeano p) ▸
        heff
  have hle_peano :
      Peano.fromOrdinal index'.toPeano ≤
        Peano.Progressions.ArithmeticDecreasing.getLength (toPeano p) := by
    have hle'' := toPeano_le_of_le hle'
    rw [fromOrdinal_toPeano_eq_fromOrdinal_peano, getLength_toPeano] at hle''
    exact hle''
  exact
    Peano.Progressions.ArithmeticDecreasing.getElementFrom_eq_add_mul_of_lt
      (toPeano p) first.toPeano hf_peano index.toPeano index'.toPeano
      hlt_peano hle_peano

/-- Length of a progression whose limit is exactly `lastElementFrom` of its
positive length and whose walk has Peano length equal to the requested length. -/
theorem getLength_lastElementFrom (first subtractiveCommonDifference : Decimal)
    (hdiff : ¬ subtractiveCommonDifference ≈ zero) (n : Decimal)
    (hne : ¬ n ≈ zero)
    (hlen : (getElementsFrom first subtractiveCommonDifference n).length =
      n.toPeano) :
    getLength {
      first := some first
      subtractiveCommonDifference := subtractiveCommonDifference
      limit := lastElementFrom first subtractiveCommonDifference n
      subtractiveCommonDifference_ne_zero := hdiff
    } ≈ n :=
  getLength_of_equivalent_lastElementFrom first subtractiveCommonDifference
    subtractiveCommonDifference
    (lastElementFrom first subtractiveCommonDifference n) n hne
    (Setoid.refl _) hdiff (Setoid.refl _) hlen

/-- Recovering the first element from an indexed element is left-inverse to
`getElementFrom` at that index, up to Decimal equivalence. -/
theorem getElementFrom_of_tryFirstFromIndexedElement
    (index : OrdinalNatural.Decimal) (element subtractiveCommonDifference
      first : Decimal)
    (h : tryFirstFromIndexedElement index element subtractiveCommonDifference =
      some first) :
    getElementFrom first subtractiveCommonDifference index ≈ element := by
  if hone : index ≈ OrdinalNatural.Decimal.one then
    simp only [tryFirstFromIndexedElement, hone, ↓reduceDIte] at h
    injection h with heq
    simp only [getElementFrom, hone, ↓reduceDIte, heq]
    exact Setoid.refl _
  else
    simp only [tryFirstFromIndexedElement, hone, ↓reduceDIte] at h
    injection h with heq
    have hrel :=
      trySubtract_add_right_of_equivalent element
        ((fromOrdinal (index.predecessor hone)) * subtractiveCommonDifference)
        ((fromOrdinal (index.predecessor hone)) * subtractiveCommonDifference)
        (Setoid.refl _)
    obtain ⟨el', hel', hel_approx⟩ :=
      InfiniteArithmetic.exists_of_option_rel_some hrel
    simp only [getElementFrom, hone, ↓reduceDIte, ← heq, hel']
    exact hel_approx

/-- A successful common-difference recovery implies the earlier element is
equivalent to the later plus the index gap times that difference. -/
theorem eq_sub_mul_of_tryCommonDifferenceFromOrderedIndexedElements
    (index : OrdinalNatural.Decimal) (element : Decimal)
    (index' : OrdinalNatural.Decimal) (element' : Decimal)
    (hlt : index < index')
    (diff : Decimal)
    (h : tryCommonDifferenceFromOrderedIndexedElements
        index element index' element' hlt = some diff) :
    element ≈
      element' +
        (fromOrdinal (OrdinalNatural.Decimal.subtract index' index hlt)) *
          diff := by
  simp only [tryCommonDifferenceFromOrderedIndexedElements] at h
  match hs : trySubtract element element' with
  | none =>
    simp only [hs] at h
    nomatch h
  | some elementDiff =>
    simp only [hs] at h
    have hmul :
        (fromOrdinal (OrdinalNatural.Decimal.subtract index' index hlt)) *
            diff ≈
          elementDiff :=
      eq_of_tryDivide_mul h
    have hadd : element ≈ element' + elementDiff :=
      eq_of_trySubtract_add element' element elementDiff hs
    exact Setoid.trans hadd (equivalent_add_left (Setoid.symm hmul))

/-- When both indexed recoveries succeed and the reconstructed walk of the given
length is complete, `getElementFrom` recovers each original element up to Decimal
equivalence. -/
theorem getElementFrom_of_tryFirst_tryCommonDifference
    (index : OrdinalNatural.Decimal) (element : Decimal)
    (index' : OrdinalNatural.Decimal) (element' : Decimal)
    (hlt : index < index')
    (diff first : Decimal) (hdiff : ¬ diff ≈ zero) (length : Decimal)
    (hne : ¬ length ≈ zero)
    (hlen : (getElementsFrom first diff length).length = length.toPeano)
    (hle' : fromOrdinal index' ≤ length)
    (hcd : tryCommonDifferenceFromOrderedIndexedElements
        index element index' element' hlt = some diff)
    (hfirst : tryFirstFromIndexedElement index element diff = some first) :
    getElementFrom first diff index ≈ element ∧
      getElementFrom first diff index' ≈ element' := by
  have h1 :=
    getElementFrom_of_tryFirstFromIndexedElement index element diff first hfirst
  refine ⟨h1, ?_⟩
  have hgap :=
    eq_sub_mul_of_tryCommonDifferenceFromOrderedIndexedElements
      index element index' element' hlt diff hcd
  let p : ArithmeticDecreasing :=
    {
      first := some first
      subtractiveCommonDifference := diff
      limit := lastElementFrom first diff length
      subtractiveCommonDifference_ne_zero := hdiff
    }
  have hf :
      effectiveFirst p = some first :=
    effectiveFirst_of_equivalent_lastElementFrom first diff diff
      (lastElementFrom first diff length) length hne hdiff (Setoid.refl _)
  have hlenp := getLength_lastElementFrom first diff hdiff length hne hlen
  have hle2p : fromOrdinal index' ≤ getLength p :=
    le_of_le_of_equivalent hle' (Setoid.symm hlenp)
  have hstep :=
    getElementFrom_eq_add_mul_of_lt p first hf index index' hlt hle2p
  apply equivalent_of_toPeano_eq
  have hleft :=
    toPeano_eq_of_equivalent (Setoid.trans (Setoid.symm hstep) h1)
  have hright := toPeano_eq_of_equivalent hgap
  have hcancel :
      (getElementFrom first diff index').toPeano +
          ((fromOrdinal
              (OrdinalNatural.Decimal.subtract index' index hlt)) *
            diff).toPeano =
        element'.toPeano +
          ((fromOrdinal
              (OrdinalNatural.Decimal.subtract index' index hlt)) *
            diff).toPeano := by
    calc
      (getElementFrom first diff index').toPeano +
          ((fromOrdinal
              (OrdinalNatural.Decimal.subtract index' index hlt)) *
            diff).toPeano
          = (getElementFrom first diff index' +
              (fromOrdinal
                (OrdinalNatural.Decimal.subtract index' index hlt)) *
                diff).toPeano := by
            rw [add_toPeano]
      _ = element.toPeano := hleft
      _ = (element' +
            (fromOrdinal
              (OrdinalNatural.Decimal.subtract index' index hlt)) *
              diff).toPeano := hright
      _ = element'.toPeano +
            ((fromOrdinal
                (OrdinalNatural.Decimal.subtract index' index hlt)) *
              diff).toPeano := by
            rw [add_toPeano]
  exact Peano.add_cancel_right _ _ _ hcancel

/-- `getElement` on a progression whose limit is `lastElementFrom` of positive
length agrees with `getElementFrom`. -/
theorem getElement_lastElementFrom (first subtractiveCommonDifference : Decimal)
    (hdiff : ¬ subtractiveCommonDifference ≈ zero) (n : Decimal)
    (hne : ¬ n ≈ zero)
    (_hlen : (getElementsFrom first subtractiveCommonDifference n).length =
      n.toPeano)
    (index : OrdinalNatural.Decimal)
    (hle : fromOrdinal index ≤
      getLength {
        first := some first
        subtractiveCommonDifference := subtractiveCommonDifference
        limit := lastElementFrom first subtractiveCommonDifference n
        subtractiveCommonDifference_ne_zero := hdiff
      }) :
    getElement
      {
        first := some first
        subtractiveCommonDifference := subtractiveCommonDifference
        limit := lastElementFrom first subtractiveCommonDifference n
        subtractiveCommonDifference_ne_zero := hdiff
      }
      index hle =
      getElementFrom first subtractiveCommonDifference index := by
  have hf :=
    effectiveFirst_of_equivalent_lastElementFrom first
      subtractiveCommonDifference subtractiveCommonDifference
      (lastElementFrom first subtractiveCommonDifference n) n hne hdiff
      (Setoid.refl _)
  exact getElement_eq_getElementFrom _ first hf index hle

theorem length_ne_zero_of_tryFromTwoElementsAndLength
    (index1 : OrdinalNatural.Decimal) (element1 : Decimal)
    (index2 : OrdinalNatural.Decimal) (element2 : Decimal)
    (length : Decimal)
    (hne : ¬ index1 ≈ index2)
    (p : ArithmeticDecreasing)
    (h : tryFromTwoElementsAndLength index1 element1 index2 element2 length hne =
      some p) :
    ¬ length ≈ zero := by
  intro hzero
  simp only [tryFromTwoElementsAndLength] at h
  by_cases hle1 : fromOrdinal index1 ≤ length
  · have : fromOrdinal index1 ≤ zero :=
      le_of_le_of_equivalent hle1 hzero
    exact fromOrdinal_not_equivalent_zero index1 (eq_zero_of_le_zero _ this)
  · simp only [hle1, ↓reduceIte] at h
    nomatch h

/-- A successful `tryFromTwoElementsAndLength` yields a progression whose
`getLength` is equivalent to the given length and whose `getElement` at each of
the two indexes recovers a value equivalent to the corresponding original
element. -/
theorem getLength_getElement_of_tryFromTwoElementsAndLength
    (index1 : OrdinalNatural.Decimal) (element1 : Decimal)
    (index2 : OrdinalNatural.Decimal) (element2 : Decimal)
    (length : Decimal)
    (hne : ¬ index1 ≈ index2)
    (p : ArithmeticDecreasing)
    (h : tryFromTwoElementsAndLength index1 element1 index2 element2 length hne =
      some p) :
    getLength p ≈ length ∧
      (∃ (hle1 : fromOrdinal index1 ≤ getLength p),
        getElement p index1 hle1 ≈ element1) ∧
      (∃ (hle2 : fromOrdinal index2 ≤ getLength p),
        getElement p index2 hle2 ≈ element2) := by
  have hlen_ne :=
    length_ne_zero_of_tryFromTwoElementsAndLength
      index1 element1 index2 element2 length hne p h
  simp only [tryFromTwoElementsAndLength] at h
  by_cases hle1 : fromOrdinal index1 ≤ length
  · simp only [hle1, ↓reduceIte] at h
    by_cases hle2 : fromOrdinal index2 ≤ length
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
              by_cases hwalk :
                  (getElementsFrom first diff length).length = length.toPeano
              · simp only [hwalk, ↓reduceIte] at h
                injection h with hp
                subst hp
                have hget :=
                  getElementFrom_of_tryFirst_tryCommonDifference
                    index1 element1 index2 element2 hlt diff first hdiff0
                    length hlen_ne hwalk hle2 hd hf
                have hlenp :=
                  getLength_lastElementFrom first diff hdiff0 length hlen_ne
                    hwalk
                have hle1p :
                    fromOrdinal index1 ≤
                      getLength {
                        first := some first
                        subtractiveCommonDifference := diff
                        limit := lastElementFrom first diff length
                        subtractiveCommonDifference_ne_zero := hdiff0
                      } :=
                  le_of_le_of_equivalent hle1 (Setoid.symm hlenp)
                have hle2p :
                    fromOrdinal index2 ≤
                      getLength {
                        first := some first
                        subtractiveCommonDifference := diff
                        limit := lastElementFrom first diff length
                        subtractiveCommonDifference_ne_zero := hdiff0
                      } :=
                  le_of_le_of_equivalent hle2 (Setoid.symm hlenp)
                refine ⟨hlenp, ⟨hle1p, ?_⟩, ⟨hle2p, ?_⟩⟩
                · exact
                    (getElement_lastElementFrom first diff hdiff0 length
                      hlen_ne hwalk index1 hle1p) ▸ hget.1
                · exact
                    (getElement_lastElementFrom first diff hdiff0 length
                      hlen_ne hwalk index2 hle2p) ▸ hget.2
              · simp only [hwalk, ↓reduceIte] at h
                nomatch h
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
              by_cases hwalk :
                  (getElementsFrom first diff length).length = length.toPeano
              · simp only [hwalk, ↓reduceIte] at h
                injection h with hp
                subst hp
                have hget :=
                  getElementFrom_of_tryFirst_tryCommonDifference
                    index2 element2 index1 element1 hgt diff first hdiff0
                    length hlen_ne hwalk hle1 hd hf
                have hlenp :=
                  getLength_lastElementFrom first diff hdiff0 length hlen_ne
                    hwalk
                have hle1p :
                    fromOrdinal index1 ≤
                      getLength {
                        first := some first
                        subtractiveCommonDifference := diff
                        limit := lastElementFrom first diff length
                        subtractiveCommonDifference_ne_zero := hdiff0
                      } :=
                  le_of_le_of_equivalent hle1 (Setoid.symm hlenp)
                have hle2p :
                    fromOrdinal index2 ≤
                      getLength {
                        first := some first
                        subtractiveCommonDifference := diff
                        limit := lastElementFrom first diff length
                        subtractiveCommonDifference_ne_zero := hdiff0
                      } :=
                  le_of_le_of_equivalent hle2 (Setoid.symm hlenp)
                refine ⟨hlenp, ⟨hle1p, ?_⟩, ⟨hle2p, ?_⟩⟩
                · exact
                    (getElement_lastElementFrom first diff hdiff0 length
                      hlen_ne hwalk index1 hle1p) ▸ hget.2
                · exact
                    (getElement_lastElementFrom first diff hdiff0 length
                      hlen_ne hwalk index2 hle2p) ▸ hget.1
              · simp only [hwalk, ↓reduceIte] at h
                nomatch h
    · simp only [hle2, ↓reduceIte] at h
      nomatch h
  · simp only [hle1, ↓reduceIte] at h
    nomatch h

/-- Walk length depends on the start and difference only through their Peano
embeddings. -/
theorem getElementsFrom_length_eq_of_toPeano_eq
    (first first' diff diff' : Decimal) (n : Decimal)
    (hf : first.toPeano = first'.toPeano) (hd : diff.toPeano = diff'.toPeano) :
    (getElementsFrom first diff n).length =
      (getElementsFrom first' diff' n).length := by
  rw [getElementsFrom_length_eq_peano_getElementsFrom,
    getElementsFrom_length_eq_peano_getElementsFrom, hf, hd]

/-- Recovering the common difference from two in-range indexed elements of a
decreasing arithmetic progression returns a value equivalent to its subtractive
common difference. -/
theorem tryCommonDifferenceFromOrderedIndexedElements_getElementFrom
    (p : ArithmeticDecreasing) (first : Decimal)
    (hf : effectiveFirst p = some first)
    (index index' : OrdinalNatural.Decimal) (hlt : index < index')
    (hle' : fromOrdinal index' ≤ getLength p) :
    ∃ d,
      tryCommonDifferenceFromOrderedIndexedElements
        index (getElementFrom first p.subtractiveCommonDifference index)
        index' (getElementFrom first p.subtractiveCommonDifference index') hlt =
          some d ∧
        d ≈ p.subtractiveCommonDifference := by
  have heq :=
    getElementFrom_eq_add_mul_of_lt p first hf index index' hlt hle'
  obtain ⟨elementDiff, hsub_eq, hsub_approx⟩ :=
    InfiniteArithmetic.exists_of_option_rel_some
      (trySubtract_of_equivalent_add heq)
  have hgap_ne :
      ¬ fromOrdinal (OrdinalNatural.Decimal.subtract index' index hlt) ≈ zero :=
    fromOrdinal_not_equivalent_zero _
  obtain ⟨d, hdiv_eq, hdiv_approx⟩ :=
    InfiniteArithmetic.exists_of_option_rel_some
      (tryDivide_of_equivalent_mul hgap_ne hsub_approx)
  refine ⟨d, ?_, hdiv_approx⟩
  simp only [tryCommonDifferenceFromOrderedIndexedElements, hsub_eq, hdiv_eq]

/-- Recovering the first element from an in-range indexed element of a
decreasing arithmetic progression, using an equivalent subtractive common
difference, returns a value equivalent to the effective first. -/
theorem tryFirstFromIndexedElement_getElementFrom_of_equivalent_diff
    (p : ArithmeticDecreasing) (first : Decimal)
    (hf : effectiveFirst p = some first) (index : OrdinalNatural.Decimal)
    (d : Decimal) (hd : d ≈ p.subtractiveCommonDifference)
    (hle : fromOrdinal index ≤ getLength p) :
    ∃ first',
      tryFirstFromIndexedElement index
        (getElementFrom first p.subtractiveCommonDifference index) d =
          some first' ∧
      first' ≈ first := by
  if hone : index ≈ OrdinalNatural.Decimal.one then
    refine ⟨getElementFrom first p.subtractiveCommonDifference index, ?_, ?_⟩
    · simp only [tryFirstFromIndexedElement, hone, ↓reduceDIte]
    · simp only [getElementFrom, hone, ↓reduceDIte]
      exact Setoid.refl _
  else
    refine
      ⟨getElementFrom first p.subtractiveCommonDifference index +
          (fromOrdinal (index.predecessor hone)) * d, ?_, ?_⟩
    · simp only [tryFirstFromIndexedElement, hone, ↓reduceDIte]
    · have hfirst_prog : (toProgression p).first = some first := by
        rw [← effectiveFirst_eq, hf]
      have hle_prog := fromOrdinal_le_progression_getLength p index hle
      have htry :=
        Sequences.Progression.tryGetElement_eq_some_getElement
          (toProgression p) (toProgression_finite p) index.toPeano hle_prog
      have hrel :=
        trySubtract_mul_of_tryGetElement_eq_some p first hfirst_prog index
          (Sequences.Progression.getElement (toProgression p)
            (toProgression_finite p) index.toPeano hle_prog)
          hone htry
      obtain ⟨y, hy, _hyx⟩ :=
        InfiniteArithmetic.exists_of_option_rel_some hrel
      have hget :
          getElementFrom first p.subtractiveCommonDifference index = y := by
        simp only [getElementFrom, hone, ↓reduceDIte, hy]
      have hfirst_add :
          first ≈
            (fromOrdinal (index.predecessor hone)) *
                p.subtractiveCommonDifference +
              y :=
        eq_of_trySubtract_add
          ((fromOrdinal (index.predecessor hone)) *
            p.subtractiveCommonDifference)
          first y hy
      have hfirst_add' :
          first ≈
            y +
              (fromOrdinal (index.predecessor hone)) *
                p.subtractiveCommonDifference :=
        Setoid.trans hfirst_add
          (equivalent_add_commutative
            ((fromOrdinal (index.predecessor hone)) *
              p.subtractiveCommonDifference)
            y)
      rw [hget]
      refine Setoid.trans ?_ (Setoid.symm hfirst_add')
      exact
        equivalent_add_left
          (equivalent_multiply (Setoid.refl _) hd)

/-- Reconstructing from any two inequivalent in-range elements of `p`, together
with `getLength p`, yields a progression equivalent to `p`. -/
theorem tryFromTwoElementsAndLength_getElement
    (p : ArithmeticDecreasing)
    (index1 index2 : OrdinalNatural.Decimal)
    (hne : ¬ index1 ≈ index2)
    (hle1 : fromOrdinal index1 ≤ getLength p)
    (hle2 : fromOrdinal index2 ≤ getLength p) :
    ∃ (q : ArithmeticDecreasing),
      tryFromTwoElementsAndLength
        index1 (getElement p index1 hle1)
        index2 (getElement p index2 hle2)
        (getLength p) hne = some q ∧
      p ≈ q := by
  have hne0 : ¬ getLength p ≈ zero := by
    intro hzero
    have : fromOrdinal index1 ≤ zero :=
      le_of_le_of_equivalent hle1 hzero
    exact fromOrdinal_not_equivalent_zero index1 (eq_zero_of_le_zero _ this)
  obtain ⟨first, hf⟩ := effectiveFirst_eq_some_of_pos_length p hne0
  have hget1 := getElement_eq_getElementFrom p first hf index1 hle1
  have hget2 := getElement_eq_getElementFrom p first hf index2 hle2
  have hwalk :
      (getElementsFrom first p.subtractiveCommonDifference
        (getLength p)).length =
        (getLength p).toPeano :=
    getElementsFrom_length_of_le_getLength p first hf (getLength p) (Or.inr rfl)
  match hcomp : OrdinalNatural.Decimal.compare index1 index2 with
  | .equivalent heq =>
    exact (hne heq).elim
  | .less hlt =>
    obtain ⟨diff, hdiff_eq, hdiff_approx⟩ :=
      tryCommonDifferenceFromOrderedIndexedElements_getElementFrom
        p first hf index1 index2 hlt hle2
    obtain ⟨first', hfirst_eq, hfirst_approx⟩ :=
      tryFirstFromIndexedElement_getElementFrom_of_equivalent_diff
        p first hf index1 diff hdiff_approx hle1
    have hdiff0 : ¬ diff ≈ zero := by
      intro hz
      exact p.subtractiveCommonDifference_ne_zero
        (Setoid.trans (Setoid.symm hdiff_approx) hz)
    have hwalk' :
        (getElementsFrom first' diff (getLength p)).length =
          (getLength p).toPeano := by
      rw [← hwalk]
      exact
        (getElementsFrom_length_eq_of_toPeano_eq first first'
            p.subtractiveCommonDifference diff (getLength p)
            (toPeano_eq_of_equivalent (Setoid.symm hfirst_approx))
            (toPeano_eq_of_equivalent (Setoid.symm hdiff_approx))).symm
    refine
      ⟨{
          first := some first'
          subtractiveCommonDifference := diff
          limit := lastElementFrom first' diff (getLength p)
          subtractiveCommonDifference_ne_zero := hdiff0
        }, ?_, ?_⟩
    · simp only [tryFromTwoElementsAndLength, hle1, hle2, ↓reduceIte, hget1,
        hget2, hcomp, hdiff_eq, hdiff0, ↓reduceDIte, hfirst_eq, hwalk',
        ↓reduceIte]
    · have hf_q :
          effectiveFirst
            {
              first := some first'
              subtractiveCommonDifference := diff
              limit := lastElementFrom first' diff (getLength p)
              subtractiveCommonDifference_ne_zero := hdiff0
            } =
            some first' :=
        effectiveFirst_of_equivalent_lastElementFrom first' diff diff
          (lastElementFrom first' diff (getLength p)) (getLength p) hne0
          hdiff0 (Setoid.refl _)
      have hlen_q :=
        getLength_lastElementFrom first' diff hdiff0 (getLength p) hne0 hwalk'
      exact equivalence_of_equivalent_params p _ first first' hf hf_q
        (Setoid.symm hfirst_approx) (Setoid.symm hdiff_approx)
        (Setoid.symm hlen_q)
  | .greater hgt =>
    obtain ⟨diff, hdiff_eq, hdiff_approx⟩ :=
      tryCommonDifferenceFromOrderedIndexedElements_getElementFrom
        p first hf index2 index1 hgt hle1
    obtain ⟨first', hfirst_eq, hfirst_approx⟩ :=
      tryFirstFromIndexedElement_getElementFrom_of_equivalent_diff
        p first hf index2 diff hdiff_approx hle2
    have hdiff0 : ¬ diff ≈ zero := by
      intro hz
      exact p.subtractiveCommonDifference_ne_zero
        (Setoid.trans (Setoid.symm hdiff_approx) hz)
    have hwalk' :
        (getElementsFrom first' diff (getLength p)).length =
          (getLength p).toPeano := by
      rw [← hwalk]
      exact
        (getElementsFrom_length_eq_of_toPeano_eq first first'
            p.subtractiveCommonDifference diff (getLength p)
            (toPeano_eq_of_equivalent (Setoid.symm hfirst_approx))
            (toPeano_eq_of_equivalent (Setoid.symm hdiff_approx))).symm
    refine
      ⟨{
          first := some first'
          subtractiveCommonDifference := diff
          limit := lastElementFrom first' diff (getLength p)
          subtractiveCommonDifference_ne_zero := hdiff0
        }, ?_, ?_⟩
    · simp only [tryFromTwoElementsAndLength, hle1, hle2, ↓reduceIte, hget1,
        hget2, hcomp, hdiff_eq, hdiff0, ↓reduceDIte, hfirst_eq, hwalk',
        ↓reduceIte]
    · have hf_q :
          effectiveFirst
            {
              first := some first'
              subtractiveCommonDifference := diff
              limit := lastElementFrom first' diff (getLength p)
              subtractiveCommonDifference_ne_zero := hdiff0
            } =
            some first' :=
        effectiveFirst_of_equivalent_lastElementFrom first' diff diff
          (lastElementFrom first' diff (getLength p)) (getLength p) hne0
          hdiff0 (Setoid.refl _)
      have hlen_q :=
        getLength_lastElementFrom first' diff hdiff0 (getLength p) hne0 hwalk'
      exact equivalence_of_equivalent_params p _ first first' hf hf_q
        (Setoid.symm hfirst_approx) (Setoid.symm hdiff_approx)
        (Setoid.symm hlen_q)

/-- Advance one step from an optional current element of a decreasing
arithmetic progression: subtract the common difference while the result is not
less than the limit; stay at `none` once past the end. -/
def nextMaskedWalkElement (subtractiveCommonDifference limit : Decimal) :
    Option Decimal → Option Decimal
  | none => none
  | some x =>
    match trySubtract x subtractiveCommonDifference with
    | none => none
    | some y => if limit ≤ y then some y else none

/-- Whether every unmasked entry agrees with a progression walk that is already
positioned at `current` (the value of `tryGetElement` at the corresponding
index). Masked (`none`) entries are skipped after advancing the walk. Avoids
recomputing `tryGetElement` from the start at each unmasked entry. Elements are
compared up to Decimal equivalence. -/
def agreesWithMaskedElementsFromCurrent
    (subtractiveCommonDifference limit : Decimal) (current : Option Decimal) :
    Sequences.List (Option Decimal) → Bool
  | .empty => true
  | .firstElement none rest =>
      agreesWithMaskedElementsFromCurrent subtractiveCommonDifference limit
        (nextMaskedWalkElement subtractiveCommonDifference limit current) rest
  | .firstElement (some x) rest =>
      match current with
      | none => false
      | some y =>
        if y ≈ x then
          agreesWithMaskedElementsFromCurrent subtractiveCommonDifference limit
            (nextMaskedWalkElement subtractiveCommonDifference limit current)
            rest
        else
          false

/-- Whether every unmasked entry agrees with `tryGetElement` on `p`, scanning
from the given ordinal Decimal index. Masked (`none`) entries are ignored.

Seeks the starting element once via `effectiveFirst` / `getElementFrom` (or
`none` when out of range), then walks by successive subtraction of the common
difference — avoiding a fresh `tryGetElement` walk at every unmasked entry.
Unmasked entries are compared up to Decimal equivalence. -/
def agreesWithMaskedElementsFrom (p : ArithmeticDecreasing)
    (index : OrdinalNatural.Decimal) (elements : Sequences.List (Option Decimal)) :
    Bool :=
  match effectiveFirst p with
  | none =>
    agreesWithMaskedElementsFromCurrent p.subtractiveCommonDifference p.limit
      none elements
  | some first =>
    if fromOrdinal index ≤ getLength p then
      agreesWithMaskedElementsFromCurrent p.subtractiveCommonDifference p.limit
        (some (getElementFrom first p.subtractiveCommonDifference index))
        elements
    else
      agreesWithMaskedElementsFromCurrent p.subtractiveCommonDifference p.limit
        none elements

/-- After one unmasked element at `index1` is known, find a second unmasked
element at a strictly larger index and reconstruct via
`tryFromTwoElementsAndLength`, then check that every later unmasked entry
agrees with the result. -/
def tryFromMaskedElementsGivenOne
    (index1 : OrdinalNatural.Decimal) (element1 : Decimal) (length : Decimal)
    (index : OrdinalNatural.Decimal) (hlt : index1 < index) :
    (elements : Sequences.List (Option Decimal)) →
    Peano.one ≤ elements.unmaskedCount →
    Option ArithmeticDecreasing
  | .empty, hge =>
      False.elim (Peano.not_succ_le_zero (by
        simpa only [Sequences.List.unmaskedCount, Peano.one] using hge))
  | .firstElement none rest, hge =>
      tryFromMaskedElementsGivenOne index1 element1 length
        index.successor
        (OrdinalNatural.Decimal.lt_trans hlt
          (OrdinalNatural.Decimal.x_lt_succ_x index))
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
    (length : Decimal) :
    (elements : Sequences.List (Option Decimal)) →
    Peano.two ≤ elements.unmaskedCount →
    Option ArithmeticDecreasing
  | .empty, hge =>
      False.elim (Peano.not_two_le_zero (by
        simpa only [Sequences.List.unmaskedCount] using hge))
  | .firstElement none rest, hge =>
      tryFromMaskedElementsFrom index.successor length rest (by
        simpa only [Sequences.List.unmaskedCount] using hge)
  | .firstElement (some x) rest, hge =>
      tryFromMaskedElementsGivenOne index x length
        index.successor (OrdinalNatural.Decimal.x_lt_succ_x index) rest (by
          have h :
              Peano.two ≤ rest.unmaskedCount + Peano.one := by
            simpa only [Sequences.List.unmaskedCount] using hge
          have h' :
              Peano.two ≤ rest.unmaskedCount.successor := by
            simpa only [Peano.add_one] using h
          exact Peano.le_of_succ_le_succ (by
            simpa only [Peano.two, Peano.one] using h'))

/-- Reconstruct a decreasing arithmetic progression from an ordered list of its
elements in which some entries may be masked as `none`. Requires a proof that
at least two entries are unmasked. Returns `none` when the unmasked entries are
not consistent with a strictly decreasing arithmetic progression whose length
equals that of the list (compared up to Decimal equivalence).

Uses the first two unmasked entries (together with their ordinal Decimal indexes
and the list length) via `tryFromTwoElementsAndLength`, then checks that every
remaining unmasked entry agrees with the reconstructed progression. -/
def tryFromMaskedElements
    (elements : Sequences.List (Option Decimal))
    (hge : Peano.two ≤ elements.unmaskedCount) :
    Option ArithmeticDecreasing :=
  tryFromMaskedElementsFrom OrdinalNatural.Decimal.one
    (fromPeano elements.length) elements hge

/-- Prop counterpart of `agreesWithMaskedElementsFrom`: every unmasked entry is
Decimal-equivalent to `tryGetElement` at the corresponding ordinal index. -/
inductive AgreesWithMaskedElementsFrom (p : ArithmeticDecreasing) :
    OrdinalNatural.Decimal → Sequences.List (Option Decimal) → Prop where
  | empty (index : OrdinalNatural.Decimal) :
      AgreesWithMaskedElementsFrom p index .empty
  | masked (index : OrdinalNatural.Decimal) (rest : Sequences.List (Option Decimal)) :
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
    (p : ArithmeticDecreasing) (x : Decimal) :
    nextMaskedWalkElement p.subtractiveCommonDifference p.limit (some x) =
      (toProgression p).next x :=
  rfl

/-- Advancing the masked walk from `tryGetElement index` yields
`tryGetElement index.successor`. -/
theorem nextMaskedWalkElement_tryGetElement (p : ArithmeticDecreasing)
    (index : OrdinalNatural.Peano) :
    nextMaskedWalkElement p.subtractiveCommonDifference p.limit
      (Sequences.Progression.tryGetElement index (toProgression p)) =
      Sequences.Progression.tryGetElement index.successor (toProgression p) := by
  match h : Sequences.Progression.tryGetElement index (toProgression p) with
  | none =>
    simp only [nextMaskedWalkElement, Sequences.Progression.tryGetElement, h]
  | some x =>
    simp only [Sequences.Progression.tryGetElement, h,
      nextMaskedWalkElement_eq_toProgression_next]

theorem tryGetElement_none_of_effectiveFirst_none
    (p : ArithmeticDecreasing) (index : OrdinalNatural.Peano)
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
theorem tryGetElement_rel_getElementFrom_of_le (p : ArithmeticDecreasing)
    (first : Decimal) (hf : effectiveFirst p = some first)
    (index : OrdinalNatural.Decimal)
    (hle : fromOrdinal index ≤ getLength p) :
    Option.Rel (· ≈ ·)
      (Sequences.Progression.tryGetElement index.toPeano (toProgression p))
      (some (getElementFrom first p.subtractiveCommonDifference index)) := by
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
theorem tryGetElement_eq_none_of_length_lt (p : ArithmeticDecreasing)
    (index : OrdinalNatural.Decimal)
    (hlt : getLength p < fromOrdinal index) :
    Sequences.Progression.tryGetElement index.toPeano (toProgression p) = none := by
  have hlt_peano :
      Sequences.Progression.getLength (toProgression p) (toProgression_finite p) <
        Peano.fromOrdinal index.toPeano := by
    have hlen_eq := getLength_eq p
    have hto :
        (getLength p).toPeano =
          Sequences.Progression.getLength (toProgression p)
            (toProgression_finite p) := by
      have h := toPeano_eq_of_equivalent hlen_eq
      rwa [toPeano_fromPeano] at h
    have hlt' :
        (getLength p).toPeano <
          (fromOrdinal index).toPeano :=
      hlt
    rwa [hto, fromOrdinal_toPeano_eq_fromOrdinal_peano]
      at hlt'
  exact Sequences.Progression.tryGetElement_eq_none_of_getLength_lt
    (toProgression p) (toProgression_finite p) index.toPeano hlt_peano

/-- Masked walk steps preserve Decimal `Option.Rel (· ≈ ·)`. -/
theorem nextMaskedWalkElement_rel_of_rel
    (subtractiveCommonDifference limit : Decimal)
    {c1 c2 : Option Decimal} (h : Option.Rel (· ≈ ·) c1 c2) :
    Option.Rel (· ≈ ·)
      (nextMaskedWalkElement subtractiveCommonDifference limit c1)
      (nextMaskedWalkElement subtractiveCommonDifference limit c2) := by
  cases h with
  | none =>
    exact Option.Rel.none
  | some hxy =>
    rename_i x y
    have hsub :=
      trySubtract_rel_of_equivalent_left x y subtractiveCommonDifference hxy
    match hsx : trySubtract x subtractiveCommonDifference,
          hsy : trySubtract y subtractiveCommonDifference with
    | none, none =>
      simp only [nextMaskedWalkElement, hsx, hsy]
      exact Option.Rel.none
    | some x', some y' =>
      have heq : x' ≈ y' := by
        have hsub' : Option.Rel (· ≈ ·) (some x') (some y') := by
          simpa only [hsx, hsy] using hsub
        exact equivalent_of_option_rel_some hsub'
      have hle_iff : (limit ≤ x') ↔ (limit ≤ y') := by
        constructor
        · intro hle
          exact (le_iff_toPeano_le _ _).mpr
            (toPeano_eq_of_equivalent heq ▸ (le_iff_toPeano_le _ _).mp hle)
        · intro hle
          exact (le_iff_toPeano_le _ _).mpr
            ((toPeano_eq_of_equivalent heq).symm ▸
              (le_iff_toPeano_le _ _).mp hle)
      simp only [nextMaskedWalkElement, hsx, hsy]
      by_cases hle_x : limit ≤ x'
      · have hle_y : limit ≤ y' := hle_iff.mp hle_x
        simp only [hle_x, hle_y, ↓reduceIte]
        exact Option.Rel.some heq
      · have hle_y : ¬ limit ≤ y' := fun h' =>
          hle_x (hle_iff.mpr h')
        simp only [hle_x, hle_y, ↓reduceIte]
        exact Option.Rel.none
    | none, some _ =>
      simp only [hsx, hsy] at hsub
      cases hsub
    | some _, none =>
      simp only [hsx, hsy] at hsub
      cases hsub

/-- The current-position agreement walk is invariant under replacing `current` by
an `Option.Rel (· ≈ ·)`-related value. -/
theorem agreesWithMaskedElementsFromCurrent_eq_of_current_rel
    (subtractiveCommonDifference limit : Decimal) {c1 c2 : Option Decimal}
    (h : Option.Rel (· ≈ ·) c1 c2)
    (elements : Sequences.List (Option Decimal)) :
    agreesWithMaskedElementsFromCurrent subtractiveCommonDifference limit c1
        elements =
      agreesWithMaskedElementsFromCurrent subtractiveCommonDifference limit c2
        elements := by
  induction elements generalizing c1 c2 with
  | empty =>
    rfl
  | firstElement head rest ih =>
    cases head with
    | none =>
      exact ih (nextMaskedWalkElement_rel_of_rel subtractiveCommonDifference
        limit h)
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
          exact ih (nextMaskedWalkElement_rel_of_rel
            subtractiveCommonDifference limit (Option.Rel.some hy))
        · have h2 : ¬ y2 ≈ x := fun h' => h1 (Setoid.trans hy h')
          simp only [h1, h2, ↓reduceIte]

/-- `agreesWithMaskedElementsFrom` starts its walk at `tryGetElement` on the
Peano embedding of the Decimal index. -/
theorem agreesWithMaskedElementsFrom_eq_fromCurrent_tryGetElement
    (p : ArithmeticDecreasing) (index : OrdinalNatural.Decimal)
    (elements : Sequences.List (Option Decimal)) :
    agreesWithMaskedElementsFrom p index elements =
      agreesWithMaskedElementsFromCurrent p.subtractiveCommonDifference p.limit
        (Sequences.Progression.tryGetElement index.toPeano (toProgression p))
        elements := by
  match hf : effectiveFirst p with
  | none =>
    have htry := tryGetElement_none_of_effectiveFirst_none p index.toPeano hf
    simp only [agreesWithMaskedElementsFrom, hf, htry]
  | some first =>
    by_cases hle : fromOrdinal index ≤ getLength p
    · have hrel :=
        tryGetElement_rel_getElementFrom_of_le p first hf index hle
      have hcongr :=
        agreesWithMaskedElementsFromCurrent_eq_of_current_rel
          p.subtractiveCommonDifference p.limit hrel elements
      simp only [agreesWithMaskedElementsFrom, hf, hle, ↓reduceIte]
      exact hcongr.symm
    · have hlt : getLength p < fromOrdinal index := by
        cases trichotomy_or (getLength p)
            (fromOrdinal index) with
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
    (p : ArithmeticDecreasing) (index : OrdinalNatural.Decimal)
    (current : Option Decimal)
    (elements : Sequences.List (Option Decimal))
    (hcur : current =
      Sequences.Progression.tryGetElement index.toPeano (toProgression p)) :
    agreesWithMaskedElementsFromCurrent p.subtractiveCommonDifference p.limit
        current elements = true ↔
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
          nextMaskedWalkElement p.subtractiveCommonDifference p.limit current =
            Sequences.Progression.tryGetElement index.successor.toPeano
              (toProgression p) := by
        rw [hcur, nextMaskedWalkElement_tryGetElement, OrdinalNatural.Decimal.successor_toPeano]
      constructor
      · intro h
        exact AgreesWithMaskedElementsFrom.masked index rest
          ((ih index.successor
            (nextMaskedWalkElement p.subtractiveCommonDifference p.limit
              current)
            hnext).mp (by
            simpa only [agreesWithMaskedElementsFromCurrent] using h))
      · intro h
        cases h with
        | masked _ _ hrest =>
          exact (ih index.successor
            (nextMaskedWalkElement p.subtractiveCommonDifference p.limit
              current)
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
              nextMaskedWalkElement p.subtractiveCommonDifference p.limit
                  (some y) =
                Sequences.Progression.tryGetElement index.successor.toPeano
                  (toProgression p) := by
            rw [← htry, nextMaskedWalkElement_tryGetElement, OrdinalNatural.Decimal.successor_toPeano]
          constructor
          · intro h
            exact AgreesWithMaskedElementsFrom.unmasked index y x rest htry heq
              ((ih index.successor
                (nextMaskedWalkElement p.subtractiveCommonDifference p.limit
                  (some y))
                hnext).mp h)
          · intro h
            cases h with
            | unmasked _ y' _ _ htry' _ hrest =>
              have hy : some y = some y' := htry.symm.trans htry'
              injection hy with hy'
              subst hy'
              exact (ih index.successor
                (nextMaskedWalkElement p.subtractiveCommonDifference p.limit
                  (some y))
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
    (p : ArithmeticDecreasing) (index : OrdinalNatural.Decimal)
    (elements : Sequences.List (Option Decimal)) :
    agreesWithMaskedElementsFrom p index elements = true ↔
      AgreesWithMaskedElementsFrom p index elements := by
  rw [agreesWithMaskedElementsFrom_eq_fromCurrent_tryGetElement]
  exact agreesWithMaskedElementsFromCurrent_eq_true_iff p index
    (Sequences.Progression.tryGetElement index.toPeano (toProgression p))
    elements rfl

theorem agreesWithMaskedElementsFrom_unmasked_eq_true
    (p : ArithmeticDecreasing) (index : OrdinalNatural.Decimal) (x : Decimal)
    (rest : Sequences.List (Option Decimal)) (y : Decimal)
    (hx : Sequences.Progression.tryGetElement index.toPeano (toProgression p) =
      some y)
    (heq : y ≈ x)
    (hrest : agreesWithMaskedElementsFrom p index.successor rest = true) :
    agreesWithMaskedElementsFrom p index (.firstElement (some x) rest) = true := by
  rw [agreesWithMaskedElementsFrom_eq_fromCurrent_tryGetElement, hx]
  rw [agreesWithMaskedElementsFrom_eq_fromCurrent_tryGetElement] at hrest
  simp only [agreesWithMaskedElementsFromCurrent, heq, ↓reduceIte]
  rwa [show nextMaskedWalkElement p.subtractiveCommonDifference p.limit
      (some y) =
      Sequences.Progression.tryGetElement index.successor.toPeano
        (toProgression p) from
    by
      rw [← hx, nextMaskedWalkElement_tryGetElement, OrdinalNatural.Decimal.successor_toPeano]]

/-- A successful `tryFromMaskedElementsGivenOne` recovers a value equivalent to
the given first unmasked element, has length equivalent to the requested length,
and agrees with every unmasked entry in the scanned suffix. -/
theorem getLength_agreesWithMaskedElementsFrom_of_tryFromMaskedElementsGivenOne
    (index1 : OrdinalNatural.Decimal) (element1 : Decimal) (length : Decimal)
    (index : OrdinalNatural.Decimal) (hlt : index1 < index)
    (elements : Sequences.List (Option Decimal))
    (hge : Peano.one ≤ elements.unmaskedCount)
    (p : ArithmeticDecreasing)
    (h : tryFromMaskedElementsGivenOne index1 element1 length index hlt
        elements hge = some p) :
    getLength p ≈ length ∧
      (∃ (hle1 : fromOrdinal index1 ≤ getLength p),
        getElement p index1 hle1 ≈ element1) ∧
      agreesWithMaskedElementsFrom p index elements = true := by
  match elements with
  | .empty =>
    exact (Peano.not_succ_le_zero (by
      simpa only [Sequences.List.unmaskedCount, Peano.one]
        using hge)).elim
  | .firstElement none rest =>
    have ih :=
      getLength_agreesWithMaskedElementsFrom_of_tryFromMaskedElementsGivenOne
        index1 element1 length index.successor
        (OrdinalNatural.Decimal.lt_trans hlt (OrdinalNatural.Decimal.x_lt_succ_x index)) rest (by
          simpa only [Sequences.List.unmaskedCount] using hge) p (by
          simpa only [tryFromMaskedElementsGivenOne] using h)
    refine ⟨ih.1, ih.2.1, ?_⟩
    rw [agreesWithMaskedElementsFrom_eq_fromCurrent_tryGetElement]
    rw [agreesWithMaskedElementsFrom_eq_fromCurrent_tryGetElement] at ih
    simpa only [agreesWithMaskedElementsFromCurrent,
      nextMaskedWalkElement_tryGetElement, OrdinalNatural.Decimal.successor_toPeano] using ih.2.2
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
            index1 element1 index element2 length (OrdinalNatural.Decimal.not_equivalent_of_lt hlt) p hs
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
    (index : OrdinalNatural.Decimal) (length : Decimal)
    (elements : Sequences.List (Option Decimal))
    (hge : Peano.two ≤ elements.unmaskedCount)
    (p : ArithmeticDecreasing)
    (h : tryFromMaskedElementsFrom index length elements hge = some p) :
    getLength p ≈ length ∧
      agreesWithMaskedElementsFrom p index elements = true := by
  match elements with
  | .empty =>
    exact (Peano.not_two_le_zero (by
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
      nextMaskedWalkElement_tryGetElement, OrdinalNatural.Decimal.successor_toPeano] using ih.2
  | .firstElement (some x) rest =>
    have hgeRest :
        Peano.one ≤ rest.unmaskedCount := by
      have h' :
          Peano.two ≤
            rest.unmaskedCount + Peano.one := by
        simpa only [Sequences.List.unmaskedCount] using hge
      have h'' :
          Peano.two ≤ rest.unmaskedCount.successor := by
        simpa only [Peano.add_one] using h'
      exact Peano.le_of_succ_le_succ (by
        simpa only [Peano.two, Peano.one]
          using h'')
    have hGiven :=
      getLength_agreesWithMaskedElementsFrom_of_tryFromMaskedElementsGivenOne
        index x length index.successor (OrdinalNatural.Decimal.x_lt_succ_x index) rest hgeRest p (by
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
    (hge : Peano.two ≤ elements.unmaskedCount)
    (p : ArithmeticDecreasing)
    (h : tryFromMaskedElements elements hge = some p) :
    getLength p ≈ fromPeano elements.length ∧
      AgreesWithMaskedElementsFrom p OrdinalNatural.Decimal.one elements := by
  have h' :
      tryFromMaskedElementsFrom OrdinalNatural.Decimal.one
        (fromPeano elements.length) elements hge =
        some p := by
    simpa only [tryFromMaskedElements] using h
  have hsound :=
    getLength_agreesWithMaskedElementsFrom_of_tryFromMaskedElementsFrom
      OrdinalNatural.Decimal.one (fromPeano elements.length) elements hge p h'
  refine ⟨hsound.1, ?_⟩
  exact (agreesWithMaskedElementsFrom_eq_true_iff p OrdinalNatural.Decimal.one
    elements).mp hsound.2

/-- Extend a decreasing arithmetic progression of length at least two to a
decreasing arithmetic progression of a given length at least that of the
original, with the same effective first element and subtractive common
difference, when a full arithmetic walk of that length is possible. Returns
`none` when an intermediate subtraction fails. When successful, the extended
progression begins with every element of the original progression.

Uses a single closed-form subtraction of `(length - 1) * subtractiveCommonDifference`
rather than building the intermediate element list. -/
def tryExtendToLength (p : ArithmeticDecreasing)
    (hge : Peano.two ≤ (getLength p).toPeano)
    (length : Decimal)
    (hle : getLength p ≤ length) :
    Option ArithmeticDecreasing :=
  match hf : effectiveFirst p with
  | none =>
    False.elim
      (Peano.not_two_le_zero
        (((toPeano_eq_of_equivalent
            ((getLength_eq_zero_iff_effectiveFirst_none p).mpr hf)).trans
          toPeano_zero) ▸ hge))
  | some first =>
    if hz : length ≈ zero then
      False.elim
        (Peano.not_two_le_zero
          (((toPeano_eq_of_equivalent
              (eq_zero_of_le_zero _
                (le_of_le_of_equivalent hle hz))).trans
            toPeano_zero) ▸ hge))
    else if h1 : length.predecessor hz ≈ zero then
      False.elim
        (Peano.not_two_le_one (by
          have hgeLen : Peano.two ≤ length.toPeano :=
            Peano.le_trans hge (toPeano_le_of_le hle)
          obtain ⟨hne_peano, hpred⟩ := predecessor_toPeano length hz
          have hn_one : length.toPeano = Peano.one := by
            have hsucc :=
              Peano.successor_predecessor length.toPeano hne_peano
            have hpred0 :
                (length.predecessor hz).toPeano = Peano.zero :=
              (toPeano_eq_of_equivalent h1).trans toPeano_zero
            rw [← hsucc, ← hpred, hpred0]
            rfl
          exact hn_one ▸ hgeLen))
    else
      match trySubtract first
          ((length.predecessor hz) * p.subtractiveCommonDifference) with
      | none => none
      | some last =>
        some {
          first := some first
          subtractiveCommonDifference := p.subtractiveCommonDifference
          limit := last
          subtractiveCommonDifference_ne_zero :=
            p.subtractiveCommonDifference_ne_zero
        }

/-- Length of a progression whose limit is the closed-form last element
`first - n * diff` of a decreasing arithmetic walk of length `n.successor`. -/
theorem getLength_of_trySubtract_mul (first diff n last : Decimal)
    (hdiff : ¬ diff ≈ zero) (hne : ¬ n ≈ zero)
    (h : trySubtract first (n * diff) = some last) :
    getLength {
      first := some first
      subtractiveCommonDifference := diff
      limit := last
      subtractiveCommonDifference_ne_zero := hdiff
    } ≈ n.successor := by
  apply equivalent_of_toPeano_eq
  have hstruct :
      toPeano {
        first := some first
        subtractiveCommonDifference := diff
        limit := last
        subtractiveCommonDifference_ne_zero := hdiff
      } =
        {
          first := some first.toPeano
          subtractiveCommonDifference := diff.toPeano
          limit := last.toPeano
          subtractiveCommonDifference_ne_zero :=
            toPeano_ne_zero_of_not_equivalent_zero hdiff
        } := by
    simp only [toPeano]
  rw [getLength_toPeano, hstruct]
  have hs_peano :
      Peano.trySubtract first.toPeano (n.toPeano * diff.toPeano) =
        some last.toPeano := by
    have hmap := trySubtract_map_toPeano first (n * diff)
    simp only [h, Option.map, multiply_toPeano] at hmap
    exact hmap.symm
  have hlen :=
    Peano.Progressions.ArithmeticDecreasing.getLength_of_trySubtract_mul
      first.toPeano diff.toPeano n.toPeano last.toPeano
      (toPeano_ne_zero_of_not_equivalent_zero hdiff)
      (toPeano_ne_zero_of_not_equivalent_zero hne)
      hs_peano
  rw [hlen, successor_toPeano]

/-- A successful `tryExtendToLength` yields a progression whose length is
equivalent to the requested length. -/
theorem getLength_of_tryExtendToLength (p : ArithmeticDecreasing)
    (hge : Peano.two ≤ (getLength p).toPeano)
    (length : Decimal)
    (hleLen : getLength p ≤ length)
    (q : ArithmeticDecreasing)
    (h : tryExtendToLength p hge length hleLen = some q) :
    getLength q ≈ length := by
  unfold tryExtendToLength at h
  split at h
  · next hf =>
    exact (Peano.not_two_le_zero
      (((toPeano_eq_of_equivalent
          ((getLength_eq_zero_iff_effectiveFirst_none p).mpr hf)).trans
        toPeano_zero) ▸ hge)).elim
  · next first hf =>
    split at h
    · next hz =>
      exact (Peano.not_two_le_zero
        (((toPeano_eq_of_equivalent
            (eq_zero_of_le_zero _
              (le_of_le_of_equivalent hleLen hz))).trans
          toPeano_zero) ▸ hge)).elim
    · next hz =>
      split at h
      · next h1 =>
        exact (Peano.not_two_le_one (by
          have hgeLen : Peano.two ≤ length.toPeano :=
            Peano.le_trans hge (toPeano_le_of_le hleLen)
          obtain ⟨hne_peano, hpred⟩ := predecessor_toPeano length hz
          have hn_one : length.toPeano = Peano.one := by
            have hsucc :=
              Peano.successor_predecessor length.toPeano hne_peano
            have hpred0 :
                (length.predecessor hz).toPeano = Peano.zero :=
              (toPeano_eq_of_equivalent h1).trans toPeano_zero
            rw [← hsucc, ← hpred, hpred0]
            rfl
          exact hn_one ▸ hgeLen)).elim
      · next h1 =>
        split at h
        · next => nomatch h
        · next last hs =>
          injection h with heq
          subst heq
          have hlen :=
            getLength_of_trySubtract_mul first p.subtractiveCommonDifference
              (length.predecessor hz) last
              p.subtractiveCommonDifference_ne_zero h1 hs
          rw [successor_predecessor length hz] at hlen
          exact hlen

/-- A successful `tryExtendToLength` keeps the original effective first
element. -/
theorem effectiveFirst_of_tryExtendToLength (p : ArithmeticDecreasing)
    (hge : Peano.two ≤ (getLength p).toPeano)
    (length : Decimal)
    (hleLen : getLength p ≤ length)
    (q : ArithmeticDecreasing)
    (h : tryExtendToLength p hge length hleLen = some q)
    (first : Decimal) (hf : effectiveFirst p = some first) :
    effectiveFirst q = some first := by
  unfold tryExtendToLength at h
  split at h
  · next hf' =>
    rw [hf'] at hf
    nomatch hf
  · next first' hf' =>
    have heq : some first = some first' := hf.symm.trans hf'
    injection heq with heq'
    split at h
    · next hz =>
      exact (Peano.not_two_le_zero
        (((toPeano_eq_of_equivalent
            (eq_zero_of_le_zero _
              (le_of_le_of_equivalent hleLen hz))).trans
          toPeano_zero) ▸ hge)).elim
    · next hz =>
      split at h
      · next h1 =>
        exact (Peano.not_two_le_one (by
          have hgeLen : Peano.two ≤ length.toPeano :=
            Peano.le_trans hge (toPeano_le_of_le hleLen)
          obtain ⟨hne_peano, hpred⟩ := predecessor_toPeano length hz
          have hn_one : length.toPeano = Peano.one := by
            have hsucc :=
              Peano.successor_predecessor length.toPeano hne_peano
            have hpred0 :
                (length.predecessor hz).toPeano = Peano.zero :=
              (toPeano_eq_of_equivalent h1).trans toPeano_zero
            rw [← hsucc, ← hpred, hpred0]
            rfl
          exact hn_one ▸ hgeLen)).elim
      · next h1 =>
        split at h
        · next => nomatch h
        · next last hs =>
          injection h with hq
          subst hq
          let mul : Decimal :=
            (length.predecessor hz) * p.subtractiveCommonDifference
          have hadd : first' ≈ mul + last :=
            eq_of_trySubtract_add mul first' last hs
          have hmul_ne : mul.toPeano ≠ Peano.zero := by
            rw [multiply_toPeano]
            exact Peano.multiply_ne_zero
              (length.predecessor hz).toPeano
              p.subtractiveCommonDifference.toPeano
              (toPeano_ne_zero_of_not_equivalent_zero h1)
              (toPeano_ne_zero_of_not_equivalent_zero
                p.subtractiveCommonDifference_ne_zero)
          have hle_lim : last ≤ first' := by
            apply (le_iff_toPeano_le last first').mpr
            have hlt : last.toPeano < first'.toPeano := by
              rw [toPeano_eq_of_equivalent hadd, add_toPeano]
              rw [Peano.add_commutative]
              exact Peano.lt_add_of_right_ne_zero last.toPeano mul.toPeano
                hmul_ne
            exact Or.inl hlt
          simp only [effectiveFirst, hle_lim, ↓reduceIte, heq']

/-- In-range elements of a decreasing arithmetic progression agree with the
corresponding elements of a successful length extension. -/
theorem getElement_of_tryExtendToLength (p : ArithmeticDecreasing)
    (hge : Peano.two ≤ (getLength p).toPeano)
    (length : Decimal)
    (hleLen : getLength p ≤ length)
    (q : ArithmeticDecreasing)
    (h : tryExtendToLength p hge length hleLen = some q)
    (index : OrdinalNatural.Decimal)
    (hle : fromOrdinal index ≤ getLength p) :
    ∃ (hle' : fromOrdinal index ≤ getLength q),
      getElement q index hle' = getElement p index hle := by
  have hlenq := getLength_of_tryExtendToLength p hge length hleLen q h
  have hle' :
      fromOrdinal index ≤ getLength q :=
    le_of_le_of_equivalent (le_trans hle hleLen) (Setoid.symm hlenq)
  refine ⟨hle', ?_⟩
  match hf : effectiveFirst p with
  | none =>
    exact (Peano.not_two_le_zero
      (((toPeano_eq_of_equivalent
          ((getLength_eq_zero_iff_effectiveFirst_none p).mpr hf)).trans
        toPeano_zero) ▸ hge)).elim
  | some first =>
    have hfExt :=
      effectiveFirst_of_tryExtendToLength p hge length hleLen q h first hf
    rw [getElement_eq_getElementFrom q first hfExt index hle']
    rw [getElement_eq_getElementFrom p first hf index hle]
    have hdiff :
        q.subtractiveCommonDifference = p.subtractiveCommonDifference := by
      unfold tryExtendToLength at h
      split at h
      · next hf' =>
        rw [hf'] at hf
        nomatch hf
      · next first' hf' =>
        split at h
        · next hz =>
          exact (Peano.not_two_le_zero
            (((toPeano_eq_of_equivalent
                (eq_zero_of_le_zero _
                  (le_of_le_of_equivalent hleLen hz))).trans
              toPeano_zero) ▸ hge)).elim
        · next hz =>
          split at h
          · next h1 =>
            exact (Peano.not_two_le_one (by
              have hgeLen : Peano.two ≤ length.toPeano :=
                Peano.le_trans hge (toPeano_le_of_le hleLen)
              obtain ⟨hne_peano, hpred⟩ := predecessor_toPeano length hz
              have hn_one : length.toPeano = Peano.one := by
                have hsucc :=
                  Peano.successor_predecessor length.toPeano hne_peano
                have hpred0 :
                    (length.predecessor hz).toPeano = Peano.zero :=
                  (toPeano_eq_of_equivalent h1).trans toPeano_zero
                rw [← hsucc, ← hpred, hpred0]
                rfl
              exact hn_one ▸ hgeLen)).elim
          · next h1 =>
            split at h
            · next => nomatch h
            · next last hs =>
              injection h with hq
              subst hq
              rfl
    rw [hdiff]

/-- Truncate a decreasing arithmetic progression of length at least two to a
decreasing arithmetic progression of a given length at most that of the
original, with the same effective first element (when non-empty) and subtractive
common difference. The truncated progression contains the initial elements of
the original progression. -/
def truncateToLength (p : ArithmeticDecreasing)
    (hge : Peano.two ≤ (getLength p).toPeano)
    (length : Decimal)
    (_hle : length ≤ getLength p) :
    ArithmeticDecreasing :=
  if length ≈ zero then
    {
      first := none
      subtractiveCommonDifference := p.subtractiveCommonDifference
      limit := p.limit
      subtractiveCommonDifference_ne_zero :=
        p.subtractiveCommonDifference_ne_zero
    }
  else
    match hf : effectiveFirst p with
    | none =>
      False.elim
        (Peano.not_two_le_zero
          (((toPeano_eq_of_equivalent
              ((getLength_eq_zero_iff_effectiveFirst_none p).mpr hf)).trans
            toPeano_zero) ▸ hge))
    | some first =>
      {
        first := some first
        subtractiveCommonDifference := p.subtractiveCommonDifference
        limit := lastElementFrom first p.subtractiveCommonDifference length
        subtractiveCommonDifference_ne_zero :=
          p.subtractiveCommonDifference_ne_zero
      }

/-- Truncating to a shorter length yields a progression whose length is
equivalent to that requested length. -/
theorem getLength_truncateToLength (p : ArithmeticDecreasing)
    (hge : Peano.two ≤ (getLength p).toPeano)
    (length : Decimal)
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
      exact (Peano.not_two_le_zero
        (((toPeano_eq_of_equivalent
            ((getLength_eq_zero_iff_effectiveFirst_none p).mpr hf)).trans
          toPeano_zero) ▸ hge)).elim
    · next first hf =>
      exact getLength_lastElementFrom first p.subtractiveCommonDifference
        p.subtractiveCommonDifference_ne_zero length hne
        (getElementsFrom_length_of_le_getLength p first hf length
          (toPeano_le_of_le hleLen))

/-- The truncated progression keeps the original effective first element when the
target length is positive. -/
theorem effectiveFirst_truncateToLength (p : ArithmeticDecreasing)
    (hge : Peano.two ≤ (getLength p).toPeano)
    (length : Decimal)
    (hleLen : length ≤ getLength p)
    (hne : ¬ length ≈ zero)
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
        p.subtractiveCommonDifference p.subtractiveCommonDifference
        (lastElementFrom first p.subtractiveCommonDifference length) length hne
        p.subtractiveCommonDifference_ne_zero (Setoid.refl _)

/-- In-range elements of a truncated decreasing arithmetic progression agree with
the corresponding elements of the original progression. -/
theorem getElement_truncateToLength (p : ArithmeticDecreasing)
    (hge : Peano.two ≤ (getLength p).toPeano)
    (length : Decimal)
    (hleLen : length ≤ getLength p)
    (index : OrdinalNatural.Decimal)
    (hle : fromOrdinal index ≤ length) :
    ∃ (hle' : fromOrdinal index ≤
        getLength (truncateToLength p hge length hleLen)),
      getElement (truncateToLength p hge length hleLen) index hle' =
        getElement p index
          (le_trans hle hleLen) := by
  have hlenTrunc := getLength_truncateToLength p hge length hleLen
  have hleOrig : fromOrdinal index ≤ getLength p :=
    le_trans hle hleLen
  have hle' :
      fromOrdinal index ≤
        getLength (truncateToLength p hge length hleLen) :=
    le_of_le_of_equivalent hle (Setoid.symm hlenTrunc)
  refine ⟨hle', ?_⟩
  have hne : ¬ length ≈ zero := by
    intro hzero
    exact fromOrdinal_not_equivalent_zero index
      (eq_zero_of_le_zero _
        (le_of_le_of_equivalent hle hzero))
  match hf : effectiveFirst p with
  | none =>
    exact (Peano.not_two_le_zero
      (((toPeano_eq_of_equivalent
          ((getLength_eq_zero_iff_effectiveFirst_none p).mpr hf)).trans
        toPeano_zero) ▸ hge)).elim
  | some first =>
    have hfTrunc :=
      effectiveFirst_truncateToLength p hge length hleLen hne first hf
    rw [getElement_eq_getElementFrom (truncateToLength p hge length hleLen)
      first hfTrunc index hle']
    rw [getElement_eq_getElementFrom p first hf index hleOrig]
    have hdiff :
        (truncateToLength p hge length hleLen).subtractiveCommonDifference =
          p.subtractiveCommonDifference := by
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

end ArithmeticDecreasing

end ZeroMath.Numbers.CardinalNatural.Decimal.Progressions
