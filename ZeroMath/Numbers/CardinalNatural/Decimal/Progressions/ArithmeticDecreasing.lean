import ZeroMath.Numbers.CardinalNatural.Decimal
import ZeroMath.Numbers.CardinalNatural.Peano.Progressions.ArithmeticDecreasing
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

end ArithmeticDecreasing

end ZeroMath.Numbers.CardinalNatural.Decimal.Progressions
