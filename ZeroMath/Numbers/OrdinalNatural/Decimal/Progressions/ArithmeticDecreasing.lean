import ZeroMath.Numbers.CardinalNatural.Decimal
import ZeroMath.Numbers.OrdinalNatural.Decimal
import ZeroMath.Numbers.OrdinalNatural.Decimal.Progressions.InfiniteArithmetic
import ZeroMath.Numbers.OrdinalNatural.Peano.Progressions.ArithmeticDecreasing
import ZeroMath.Sequences.List
import ZeroMath.Sequences.Progression

namespace ZeroMath.Numbers.OrdinalNatural.Decimal.Progressions

/-- An arithmetic progression of Decimal numbers with subtractive common
difference, defined by an optional first element (`none` for the empty
progression), the common difference (subtracted at each step), and a limit
such that no element is less than the limit. The progression is also empty
when the first element is less than the limit. Because every Decimal number is
at least one, the common difference is always positive. -/
structure ArithmeticDecreasing where
  first : Option Decimal
  subtractiveCommonDifference : Decimal
  limit : Decimal

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
theorem limit_le_of_tryGetElement_eq_some (p : ArithmeticDecreasing) (index : Peano)
    (x : Decimal)
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
since the subtractive common difference is at least one. -/
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
      have hz_le : Peano.successor z.toPeano ≤ y.toPeano := by
        rw [← Peano.add_one, ← hpeano]
        exact Peano.le_add_of_le_right z.toPeano
          (Peano.one_le' p.subtractiveCommonDifference.toPeano)
      exact heq ▸ Peano.lt_of_succ_le hz_le
    · simp only [hle, ↓reduceIte] at h
      nomatch h

/-- If `tryGetElement` returns a value and the progression starts at `first`,
then `index + x.toPeano ≤ successor first.toPeano`. Each step decreases the
value by at least one while the Peano index increases by one, so their sum
never exceeds that of the first element. -/
theorem add_le_succ_first_of_tryGetElement (p : ArithmeticDecreasing)
    (first : Decimal) (index : Peano) (x : Decimal)
    (hf : (toProgression p).first = some first)
    (h : Sequences.Progression.tryGetElement index (toProgression p) = some x) :
    index + x.toPeano ≤ Peano.successor first.toPeano := by
  induction index generalizing x with
  | one =>
    simp only [Sequences.Progression.tryGetElement] at h
    have heq : x = first := by
      rw [hf] at h
      injection h with heq
      exact heq.symm
    rw [heq, Peano.one_add]
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
      have hx_le : Peano.successor x.toPeano ≤ y.toPeano :=
        Peano.succ_le_of_lt hlt
      have hn : n + y.toPeano ≤ Peano.successor first.toPeano := ih y hm
      have hmid : n + Peano.successor x.toPeano ≤ n + y.toPeano :=
        Peano.le_add_of_le_right n hx_le
      have hmid' : n + Peano.successor x.toPeano ≤ Peano.successor first.toPeano :=
        Peano.le_trans hmid hn
      have heqadd :
          Peano.successor n + x.toPeano = n + Peano.successor x.toPeano := by
        rw [Peano.succ_add, Peano.add_succ]
      exact heqadd ▸ hmid'

/-- The progression obtained from a decreasing arithmetic progression is finite:
if it is empty then `tryGetElement` at `one` is `none`; otherwise, starting from
`first`, `tryGetElement` at `successor first.toPeano` cannot return `some`, since
that value `x` would need `successor first.toPeano + x.toPeano ≤
successor first.toPeano`. -/
theorem toProgression_finite (p : ArithmeticDecreasing) :
    Sequences.Progression.Finite (toProgression p) := by
  match hf : (toProgression p).first with
  | none =>
    refine ⟨Peano.one, ?_⟩
    simp only [Sequences.Progression.tryGetElement, hf]
  | some first =>
    refine ⟨Peano.successor first.toPeano, ?_⟩
    cases h :
        Sequences.Progression.tryGetElement
          (Peano.successor first.toPeano) (toProgression p) with
    | none =>
      rfl
    | some x =>
      have hle :=
        add_le_succ_first_of_tryGetElement p first
          (Peano.successor first.toPeano) x hf h
      exact (Peano.not_le_of_gt
        (Peano.lt_add_left (Peano.successor first.toPeano) x.toPeano) hle).elim

/-- Length remaining from an element already known to lie in the progression,
given the room below that element down to the limit (`none` when the element
equals the limit). Computed with one division by the subtractive common
difference instead of comparing each successive term to the limit. -/
def lengthFromGap (diff : Decimal) : Option Decimal → CardinalNatural.Decimal
  | none => CardinalNatural.Decimal.one
  | some gap =>
    match divideWithRemainder gap diff with
    | (none, _) => CardinalNatural.Decimal.one
    | (some q, _) =>
      CardinalNatural.Decimal.successor (CardinalNatural.Decimal.fromOrdinal q)

/-- The length of a decreasing arithmetic progression: the number of elements
before `tryGetElement` first returns `none`. Uses a single comparison of the
first element to the limit and one division, avoiding a comparison at every
step of the progression. -/
def getLength (p : ArithmeticDecreasing) : CardinalNatural.Decimal :=
  match p.first with
  | none => CardinalNatural.Decimal.zero
  | some first =>
    match compare first p.limit with
    | .less _ => CardinalNatural.Decimal.zero
    | .equivalent _ => CardinalNatural.Decimal.one
    | .greater hlt =>
      lengthFromGap p.subtractiveCommonDifference (some (subtract first p.limit hlt))

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

/-- Decimal `≤` is reflected and reflected by the Peano embedding. -/
theorem le_iff_toPeano_le (a b : Decimal) : a ≤ b ↔ a.toPeano ≤ b.toPeano := by
  constructor
  · intro h
    cases h with
    | inl hlt => exact Or.inl hlt
    | inr heq => exact Or.inr (toPeano_eq_of_equivalent heq)
  · intro h
    cases h with
    | inl hlt => exact Or.inl hlt
    | inr heq => exact Or.inr (equivalent_of_toPeano_eq heq)

/-- `lengthFromGap` agrees with the Peano `lengthFromGap` on embeddings. -/
theorem lengthFromGap_toPeano (diff : Decimal) (gap : Option Decimal) :
    (lengthFromGap diff gap).toPeano =
      Peano.Progressions.ArithmeticDecreasing.lengthFromGap
        diff.toPeano (gap.map Decimal.toPeano) := by
  match gap with
  | none =>
    simp only [lengthFromGap, Option.map, CardinalNatural.Decimal.toPeano_one,
      Peano.Progressions.ArithmeticDecreasing.lengthFromGap]
  | some g =>
    match hdiv : divideWithRemainder g diff with
    | (none, r) =>
      have hp := divideWithRemainder_toPeano g diff hdiv
      simp only [lengthFromGap, hdiv, Option.map, hp,
        Peano.Progressions.ArithmeticDecreasing.lengthFromGap,
        CardinalNatural.Decimal.toPeano_one]
    | (some q, r) =>
      have hp := divideWithRemainder_toPeano g diff hdiv
      simp only [lengthFromGap, hdiv, Option.map, hp,
        Peano.Progressions.ArithmeticDecreasing.lengthFromGap]
      rw [CardinalNatural.Decimal.successor_toPeano,
        CardinalNatural.Decimal.fromOrdinal_toPeano_eq_fromOrdinal_peano,
        CardinalNatural.Peano.fromOrdinal]

/-- `getLength` agrees with Peano `getLength` on the embedded progression. -/
theorem getLength_toPeano (p : ArithmeticDecreasing) :
    (getLength p).toPeano =
      Peano.Progressions.ArithmeticDecreasing.getLength (toPeano p) := by
  cases hf : p.first with
  | none =>
    simp only [getLength, hf, toPeano,
      Peano.Progressions.ArithmeticDecreasing.getLength,
      CardinalNatural.Decimal.toPeano_zero]
  | some first =>
    have hto : toPeano p =
        {
          first := some first.toPeano
          subtractiveCommonDifference := p.subtractiveCommonDifference.toPeano
          limit := p.limit.toPeano
        } := by
      simp only [toPeano, hf]
    rw [hto]
    unfold getLength Peano.Progressions.ArithmeticDecreasing.getLength
    simp only [hf]
    cases hcmp : Peano.compare first.toPeano p.limit.toPeano with
    | less hlt =>
      have hdec : compare first p.limit = .less hlt := by
        simp only [compare, hcmp]
      simp only [hdec, CardinalNatural.Decimal.toPeano_zero]
    | equal heq =>
      have hdec : compare first p.limit =
          .equivalent (equivalent_of_toPeano_eq heq) := by
        simp only [compare, hcmp]
      simp only [hdec, CardinalNatural.Decimal.toPeano_one]
    | greater hgt =>
      have hdec : compare first p.limit = .greater hgt := by
        simp only [compare, hcmp]
      simp only [hdec]
      obtain ⟨_, hsub_eq⟩ := subtract_toPeano first p.limit hgt
      have hlen :=
        lengthFromGap_toPeano p.subtractiveCommonDifference
          (some (subtract first p.limit hgt))
      simpa [Option.map, hsub_eq] using hlen

/-- `trySubtract` commutes with the Peano embedding. -/
theorem trySubtract_map_toPeano (x y : Decimal) :
    Option.map Decimal.toPeano (trySubtract x y) =
      Peano.trySubtract x.toPeano y.toPeano := by
  match h : trySubtract x y with
  | some z =>
    have hex := exists_subtract_of_trySubtract h
    have hlt : y < x := hex.choose
    have hsub : subtract x y hlt = z := hex.choose_spec
    have hsub_peano := subtract_toPeano x y hlt
    have h2 : y.toPeano < x.toPeano := hsub_peano.choose
    have hsub_eq :
        (subtract x y hlt).toPeano = Peano.subtract x.toPeano y.toPeano h2 :=
      hsub_peano.choose_spec
    have hp :
        Peano.trySubtract x.toPeano y.toPeano = some z.toPeano :=
      Peano.trySubtract_of_subtract
        (x := x.toPeano) (y := y.toPeano) (z := z.toPeano)
        ⟨h2, by rw [← hsub_eq, hsub]⟩
    simp only [Option.map, hp]
  | none =>
    match htry : Peano.trySubtract x.toPeano y.toPeano with
    | none =>
      simp only [Option.map]
    | some z =>
      have hex := Peano.exists_subtract_of_trySubtract htry
      have hlt' : y < x := hex.choose
      have hsome :=
        trySubtract_of_subtract (z := subtract x y hlt') ⟨hlt', rfl⟩
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
        rw [getLengthFrom_eq_of_current_eq _ hmap hAcc_map]
        rw [Sequences.Progression.getLengthFrom_some
          (Peano.Progressions.ArithmeticDecreasing.toProgression
            (toPeano p)).next
          x.toPeano (hmap ▸ hAcc_map)]
        have hnext := next_toPeano p x
        have ih' := ih ((toProgression p).next x)
          (Sequences.Progression.OptionStep.step x)
        refine congrArg CardinalNatural.Peano.successor (ih'.trans ?_)
        exact
          (getLengthFrom_eq_of_current_eq _
            hnext
            (acc_map_toPeano p ((toProgression p).next x)
              (hAccx.inv (Sequences.Progression.OptionStep.step x)))).trans
            (getLengthFrom_eq_of_acc_eq _ _ _ _))
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
    (getLengthFrom_eq_of_current_eq _
      hfirst
      (acc_map_toPeano p (toProgression p).first
        (Sequences.Progression.acc_first_of_finite (toProgression p)
          (toProgression_finite p)))).trans
      (getLengthFrom_eq_of_acc_eq _ _ _ _)

/-- `getLength` agrees with walking `toProgression` via `Progression.getLength`. -/
theorem getLength_eq (p : ArithmeticDecreasing) :
    getLength p ≈
      CardinalNatural.Decimal.fromPeano
        (Sequences.Progression.getLength (toProgression p)
          (toProgression_finite p)) := by
  apply CardinalNatural.Decimal.equivalent_of_toPeano_eq
  rw [CardinalNatural.Decimal.toPeano_fromPeano, getLength_toPeano,
    Peano.Progressions.ArithmeticDecreasing.getLength_eq (toPeano p),
    progression_getLength_toPeano]

/-- Element at a positive ordinal index starting from a known first value, using
the closed form with no limit comparisons. The first element has index
equivalent to `one`; otherwise the value is
`first` minus `(predecessor index) * subtractiveCommonDifference` when that
subtraction is defined, and `first` otherwise. -/
def getElementFrom (first subtractiveCommonDifference : Decimal)
    (index : Decimal) : Decimal :=
  if h : index ≈ one then
    first
  else
    match trySubtract first
        ((index.predecessor h) * subtractiveCommonDifference) with
    | none => first
    | some y => y

/-- If there is no first element, the length is zero. -/
theorem getLength_eq_zero_of_first_none (p : ArithmeticDecreasing)
    (h : p.first = none) :
    getLength p = CardinalNatural.Decimal.zero := by
  simp only [getLength, h]

/-- If the first element is less than the limit, the length is zero. -/
theorem getLength_eq_zero_of_first_lt_limit (p : ArithmeticDecreasing)
    (first : Decimal) (hf : p.first = some first) (hlt : first < p.limit) :
    getLength p = CardinalNatural.Decimal.zero := by
  unfold getLength
  simp only [hf]
  match hcmp : compare first p.limit with
  | .greater hgt =>
    exact (Peano.not_lt_of_lt (toPeano_lt_of_lt hlt) (toPeano_lt_of_lt hgt)).elim
  | .equivalent heq =>
    have hself : p.limit.toPeano < p.limit.toPeano := by
      have hlt' := toPeano_lt_of_lt hlt
      rwa [toPeano_eq_of_equivalent heq] at hlt'
    exact (Peano.not_lt_self _ hself).elim
  | .less _ =>
    rfl

/-- The length bound is impossible when there is no first element. -/
theorem not_fromOrdinal_le_getLength_of_first_none
    (p : ArithmeticDecreasing) (index : Decimal)
    (hle : CardinalNatural.Decimal.fromOrdinal index ≤ getLength p)
    (h : p.first = none) : False := by
  have hle' : CardinalNatural.Decimal.fromOrdinal index ≤
      CardinalNatural.Decimal.zero :=
    (getLength_eq_zero_of_first_none p h) ▸ hle
  exact CardinalNatural.Decimal.fromOrdinal_not_equivalent_zero index
    (CardinalNatural.Decimal.eq_zero_of_le_zero _ hle')

/-- The length bound is impossible when the first element is below the limit. -/
theorem not_fromOrdinal_le_getLength_of_first_lt_limit
    (p : ArithmeticDecreasing) (index first : Decimal)
    (hle : CardinalNatural.Decimal.fromOrdinal index ≤ getLength p)
    (hf : p.first = some first) (hlt : first < p.limit) : False := by
  have hle' : CardinalNatural.Decimal.fromOrdinal index ≤
      CardinalNatural.Decimal.zero :=
    (getLength_eq_zero_of_first_lt_limit p first hf hlt) ▸ hle
  exact CardinalNatural.Decimal.fromOrdinal_not_equivalent_zero index
    (CardinalNatural.Decimal.eq_zero_of_le_zero _ hle')

/-- The element at the given positive ordinal index, when that index does not
exceed the progression's length. The first element has index equivalent to
`one`. Uses a single `compare` of the first element to the limit (as in
`getLength`), then the closed form of the arithmetic progression — avoiding
`toProgression` and a limit comparison at every step. -/
def getElement (p : ArithmeticDecreasing) (index : Decimal)
    (hle : CardinalNatural.Decimal.fromOrdinal index ≤ getLength p) : Decimal :=
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
    (p : ArithmeticDecreasing) (index : Decimal)
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
  rw [multiplyToPeano, toPeano_one, Peano.one_multiply]

/-- For a non-`one` index, multiplying the predecessor by `diff` is the Peano
successor multiplication: one step larger than multiplying the
predecessor-of-predecessor, when that exists. -/
theorem predecessor_multiply_eq_add_of_not_one (index diff : Decimal)
    (hne : ¬ index ≈ one) (hpred : ¬ index.predecessor hne ≈ one) :
    (index.predecessor hne) * diff ≈
      ((index.predecessor hne).predecessor hpred) * diff + diff := by
  apply equivalent_of_toPeano_eq
  rw [multiplyToPeano, add_toPeano, multiplyToPeano]
  have hsucc :=
    InfiniteArithmetic.toPeano_eq_succ_predecessor_toPeano
      (index.predecessor hne) hpred
  rw [hsucc, Peano.succ_multiply]

/-- Addition respects Decimal equivalence in the right argument. -/
theorem equivalent_add_left_of_equivalent_right {a b c : Decimal}
    (h : b ≈ c) : a + b ≈ a + c := by
  apply equivalent_of_toPeano_eq
  rw [add_toPeano, add_toPeano, toPeano_eq_of_equivalent h]

/-- When `start ≈ x + d`, `trySubtract start d` recovers a value equivalent to
`x`. -/
theorem trySubtract_of_equivalent_add_right {start x d : Decimal}
    (h : start ≈ x + d) :
    Option.Rel (· ≈ ·) (trySubtract start d) (some x) := by
  have hrel :=
    InfiniteArithmetic.trySubtract_add_right_of_equivalent x d d (Setoid.refl _)
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
    (index : Decimal) (x : Decimal)
    (hne : ¬ index ≈ one)
    (h : Sequences.Progression.tryGetElement index.toPeano (toProgression p) =
      some x) :
    Option.Rel (· ≈ ·)
      (trySubtract start
        ((index.predecessor hne) * p.subtractiveCommonDifference))
      (some x) := by
  have hpeano :=
    InfiniteArithmetic.toPeano_eq_succ_predecessor_toPeano index hne
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
        if hpred : index.predecessor hne ≈ one then
          have hpeano_pred : (index.predecessor hne).toPeano = Peano.one :=
            (InfiniteArithmetic.toPeano_eq_one_iff_equivalent_one _).mpr hpred
          rw [hpeano_pred, Sequences.Progression.tryGetElement, hf] at htry
          injection htry with heq_y
          have hstart_add :
              start ≈ z + p.subtractiveCommonDifference := by
            rw [heq_y]
            exact hy_add
          have hmul :
              (index.predecessor hne) * p.subtractiveCommonDifference ≈
                p.subtractiveCommonDifference :=
            Setoid.trans
              (InfiniteArithmetic.equivalent_multiply hpred (Setoid.refl _))
              (one_multiply_equivalent _)
          have hstart_mul :
              start ≈
                z + ((index.predecessor hne) * p.subtractiveCommonDifference) :=
            Setoid.trans hstart_add
              (Setoid.symm
                (equivalent_add_left_of_equivalent_right hmul))
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
                w + ((index.predecessor hne).predecessor hpred) *
                  p.subtractiveCommonDifference := by
            obtain ⟨hlt, hsub⟩ := exists_subtract_of_trySubtract hw
            have hadd :=
              subtract_add_cancel start
                (((index.predecessor hne).predecessor hpred) *
                  p.subtractiveCommonDifference)
                hlt
            rw [hsub] at hadd
            exact Setoid.symm hadd
          have hstart_y :
              start ≈
                y + ((index.predecessor hne).predecessor hpred) *
                  p.subtractiveCommonDifference :=
            Setoid.trans hstart_w
              (InfiniteArithmetic.equivalent_add_right hwy)
          have hmul :=
            predecessor_multiply_eq_add_of_not_one index
              p.subtractiveCommonDifference hne hpred
          have hstart_z :
              start ≈
                z + ((index.predecessor hne) * p.subtractiveCommonDifference) := by
            apply equivalent_of_toPeano_eq
            have hp := toPeano_eq_of_equivalent hstart_y
            have hy := toPeano_eq_of_equivalent hy_add
            rw [add_toPeano] at hp hy
            rw [add_toPeano, toPeano_eq_of_equivalent hmul, add_toPeano,
              Peano.add_comm
                (((index.predecessor hne).predecessor hpred) *
                    p.subtractiveCommonDifference).toPeano
                p.subtractiveCommonDifference.toPeano,
              ← Peano.add_assoc, ← hy, ← hp]
          have hrel := trySubtract_of_equivalent_add_right hstart_z
          rw [← hx]
          exact hrel
      · simp only [hle_lim, ↓reduceIte] at hnext
        nomatch hnext
termination_by index.toPeano
decreasing_by
  obtain ⟨hne', heq⟩ := predecessor_toPeano index hne
  simp only [heq]
  exact InfiniteArithmetic.sizeOf_predecessor_lt _ hne'

/-- When `tryGetElement` succeeds from a known first element, the value is
equivalent to the closed-form `getElementFrom` at the Decimal index. -/
theorem eq_getElementFrom_of_tryGetElement_eq_some
    (p : ArithmeticDecreasing) (start : Decimal)
    (hf : (toProgression p).first = some start)
    (index : Decimal) (x : Decimal)
    (h : Sequences.Progression.tryGetElement index.toPeano (toProgression p) =
      some x) :
    x ≈ getElementFrom start p.subtractiveCommonDifference index := by
  if hone : index ≈ one then
    have hpeano : index.toPeano = Peano.one :=
      (InfiniteArithmetic.toPeano_eq_one_iff_equivalent_one index).mpr hone
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
        ((index.predecessor hone) * p.subtractiveCommonDifference), hrel with
    | none, hrel =>
      cases hrel
    | some z, hrel =>
      cases hrel with
      | some hz =>
        exact Setoid.symm hz

/-- `getElement` agrees with walking `toProgression` via `Progression.getElement`
up to Decimal equivalence. -/
theorem getElement_eq (p : ArithmeticDecreasing) (index : Decimal)
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
theorem tryGetElement_toPeano (p : ArithmeticDecreasing) (index : Peano) :
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

theorem lengthFromGap_ne_zero (diff : Decimal) (gap : Option Decimal)
    (h : lengthFromGap diff gap ≈ CardinalNatural.Decimal.zero) : False := by
  have hpeano :
      (lengthFromGap diff gap).toPeano = CardinalNatural.Peano.zero :=
    (CardinalNatural.Decimal.toPeano_eq_of_equivalent h).trans
      CardinalNatural.Decimal.toPeano_zero
  rw [lengthFromGap_toPeano] at hpeano
  exact Peano.Progressions.ArithmeticDecreasing.lengthFromGap_ne_zero
    diff.toPeano _ hpeano

theorem getLength_eq_zero_iff_effectiveFirst_none (p : ArithmeticDecreasing) :
    getLength p ≈ CardinalNatural.Decimal.zero ↔ effectiveFirst p = none := by
  constructor
  · intro hlen
    have hpeano :
        Peano.Progressions.ArithmeticDecreasing.getLength (toPeano p) =
          CardinalNatural.Peano.zero := by
      rw [← getLength_toPeano]
      exact (CardinalNatural.Decimal.toPeano_eq_of_equivalent hlen).trans
        CardinalNatural.Decimal.toPeano_zero
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
    (h : ¬ getLength p ≈ CardinalNatural.Decimal.zero) :
    ∃ first, effectiveFirst p = some first := by
  cases hf : effectiveFirst p with
  | none =>
    exact False.elim (h ((getLength_eq_zero_iff_effectiveFirst_none p).mpr hf))
  | some first =>
    exact ⟨first, rfl⟩

/-- Empty progressions (length zero) are equivalent. -/
theorem equivalence_of_length_zero (p q : ArithmeticDecreasing)
    (hp : getLength p ≈ CardinalNatural.Decimal.zero)
    (hq : getLength q ≈ CardinalNatural.Decimal.zero) :
    Equivalence p q := by
  have hp' :
      Peano.Progressions.ArithmeticDecreasing.getLength (toPeano p) =
        CardinalNatural.Peano.zero := by
    rw [← getLength_toPeano]
    exact (CardinalNatural.Decimal.toPeano_eq_of_equivalent hp).trans
      CardinalNatural.Decimal.toPeano_zero
  have hq' :
      Peano.Progressions.ArithmeticDecreasing.getLength (toPeano q) =
        CardinalNatural.Peano.zero := by
    rw [← getLength_toPeano]
    exact (CardinalNatural.Decimal.toPeano_eq_of_equivalent hq).trans
      CardinalNatural.Decimal.toPeano_zero
  exact (equivalence_iff_toPeano p q).mpr
    (Peano.Progressions.ArithmeticDecreasing.equivalence_of_length_zero
      (toPeano p) (toPeano q) hp' hq')

/-- Length-one progressions with equivalent first elements are equivalent. -/
theorem equivalence_of_length_one (p q : ArithmeticDecreasing)
    (firstP firstQ : Decimal)
    (hp : effectiveFirst p = some firstP) (hq : effectiveFirst q = some firstQ)
    (hfirst : firstP ≈ firstQ)
    (hlenP : getLength p ≈ CardinalNatural.Decimal.one)
    (hlenQ : getLength q ≈ CardinalNatural.Decimal.one) :
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
        CardinalNatural.Peano.one := by
    rw [← getLength_toPeano]
    exact (CardinalNatural.Decimal.toPeano_eq_of_equivalent hlenP).trans
      CardinalNatural.Decimal.toPeano_one
  have hlenQ' :
      Peano.Progressions.ArithmeticDecreasing.getLength (toPeano q) =
        CardinalNatural.Peano.one := by
    rw [← getLength_toPeano]
    exact (CardinalNatural.Decimal.toPeano_eq_of_equivalent hlenQ).trans
      CardinalNatural.Decimal.toPeano_one
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
    exact CardinalNatural.Decimal.toPeano_eq_of_equivalent hlen
  exact (equivalence_iff_toPeano p q).mpr
    (Peano.Progressions.ArithmeticDecreasing.equivalence_of_same_params
      (toPeano p) (toPeano q) firstP.toPeano hp' hq' hdiff' hlen')

theorem effectiveFirst_rel_of_equivalence (p q : ArithmeticDecreasing)
    (h : Equivalence p q) :
    Option.Rel (· ≈ ·) (effectiveFirst p) (effectiveFirst q) := by
  have h1 := h Peano.one
  simp only [Sequences.Progression.tryGetElement, ← effectiveFirst_eq] at h1
  exact h1

theorem getLength_equivalent_of_equivalence (p q : ArithmeticDecreasing)
    (h : Equivalence p q) : getLength p ≈ getLength q := by
  have hpeano :=
    Peano.Progressions.ArithmeticDecreasing.getLength_eq_of_equivalence
      (toPeano p) (toPeano q) ((equivalence_iff_toPeano p q).mp h)
  apply CardinalNatural.Decimal.equivalent_of_toPeano_eq
  rw [getLength_toPeano, getLength_toPeano, hpeano]

theorem subtractiveCommonDifference_equivalent_of_equivalence_of_length_ge_two
    (p q : ArithmeticDecreasing) (firstP firstQ : Decimal)
    (hp : effectiveFirst p = some firstP) (hq : effectiveFirst q = some firstQ)
    (hfirst : firstP ≈ firstQ)
    (hne0 : ¬ getLength p ≈ CardinalNatural.Decimal.zero)
    (hne1 : ¬ getLength p ≈ CardinalNatural.Decimal.one)
    (hlen : getLength p ≈ getLength q) (h : Equivalence p q) :
    p.subtractiveCommonDifference ≈ q.subtractiveCommonDifference := by
  have h0 :
      Peano.Progressions.ArithmeticDecreasing.getLength (toPeano p) ≠
        CardinalNatural.Peano.zero := by
    intro hz
    apply hne0
    apply CardinalNatural.Decimal.equivalent_of_toPeano_eq
    rw [getLength_toPeano, hz, CardinalNatural.Decimal.toPeano_zero]
  have h1 :
      Peano.Progressions.ArithmeticDecreasing.getLength (toPeano p) ≠
        CardinalNatural.Peano.one := by
    intro hone
    apply hne1
    apply CardinalNatural.Decimal.equivalent_of_toPeano_eq
    rw [getLength_toPeano, hone, CardinalNatural.Decimal.toPeano_one]
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
    exact CardinalNatural.Decimal.toPeano_eq_of_equivalent hlen
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
theorem sizeOf_cardinal_peano_predecessor_lt (n : CardinalNatural.Peano)
    (hne : n ≠ CardinalNatural.Peano.zero) :
    sizeOf (n.predecessor hne) < sizeOf n := by
  cases n with
  | zero => exact False.elim (hne rfl)
  | successor n =>
    have hpred : (CardinalNatural.Peano.successor n).predecessor hne = n := rfl
    rw [hpred]
    exact Nat.lt_add_of_pos_left (k := 1) Nat.zero_lt_one

/-- Elements from a known start for the given remaining length, retreating by the
subtractive common difference with no limit comparisons. -/
def getElementsFrom (first subtractiveCommonDifference : Decimal) :
    CardinalNatural.Decimal → Sequences.List Decimal
  | n =>
    if h : n ≈ CardinalNatural.Decimal.zero then
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
  obtain ⟨hne, heq⟩ := CardinalNatural.Decimal.predecessor_toPeano n h
  rw [heq]
  exact sizeOf_cardinal_peano_predecessor_lt _ hne

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
    CardinalNatural.Peano.two ≤ elements.length →
    Option ArithmeticDecreasing
  | .empty, hge =>
    False.elim (CardinalNatural.Peano.not_two_le_zero (by
      change CardinalNatural.Peano.two ≤ CardinalNatural.Peano.zero
      exact hge))
  | .firstElement _ .empty, hge =>
    False.elim (CardinalNatural.Peano.not_two_le_one (by
      change CardinalNatural.Peano.two ≤ CardinalNatural.Peano.one
      exact hge))
  | .firstElement x (.firstElement y ys), _ =>
    match trySubtract x y with
    | none => none
    | some diff =>
      match tryLastOfArithmeticContinuation y diff ys with
      | none => none
      | some last =>
        some {
          first := some x
          subtractiveCommonDifference := diff
          limit := last
        }

/-- A cardinal Decimal with non-zero Peano embedding is not equivalent to zero. -/
theorem not_equivalent_zero_of_toPeano_ne_zero (n : CardinalNatural.Decimal)
    (hne : n.toPeano ≠ CardinalNatural.Peano.zero) :
    ¬ n ≈ CardinalNatural.Decimal.zero := by
  intro heq
  exact hne ((CardinalNatural.Decimal.toPeano_eq_of_equivalent heq).trans
    CardinalNatural.Decimal.toPeano_zero)

/-- Last element of a non-empty decreasing arithmetic walk of cardinal length `n`,
starting at `first` with subtractive common difference
`subtractiveCommonDifference`. Defined via the Peano embedding so that length
and order facts transport directly. For `n ≈ zero` the value is unused
(`fromPeano` of the Peano placeholder). -/
def lastElementFrom (first subtractiveCommonDifference : Decimal)
    (n : CardinalNatural.Decimal) : Decimal :=
  fromPeano
    (Peano.Progressions.ArithmeticDecreasing.lastElementFrom
      first.toPeano subtractiveCommonDifference.toPeano n.toPeano)

/-- `lastElementFrom` agrees with the Peano embedding on the nose. -/
theorem lastElementFrom_toPeano (first subtractiveCommonDifference : Decimal)
    (n : CardinalNatural.Decimal) :
    (lastElementFrom first subtractiveCommonDifference n).toPeano =
      Peano.Progressions.ArithmeticDecreasing.lastElementFrom
        first.toPeano subtractiveCommonDifference.toPeano n.toPeano := by
  simpa [lastElementFrom] using toPeano_fromPeano
    (Peano.Progressions.ArithmeticDecreasing.lastElementFrom
      first.toPeano subtractiveCommonDifference.toPeano n.toPeano)

/-- A successful subtraction `trySubtract y x = some d` means `y ≈ x + d`. -/
theorem equivalent_of_trySubtract_add (x y d : Decimal)
    (h : trySubtract y x = some d) : y ≈ x + d := by
  obtain ⟨hlt, hsub⟩ := exists_subtract_of_trySubtract h
  have hsum := subtract_add_cancel y x hlt
  rw [hsub] at hsum
  exact Setoid.trans (Setoid.symm hsum) (add_commutative d x ▸ Setoid.refl _)

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
    (n m : CardinalNatural.Decimal) (h : n.toPeano = m.toPeano) :
    getElementsFrom first subtractiveCommonDifference n =
      getElementsFrom first subtractiveCommonDifference m := by
  have hgen :
      ∀ k : CardinalNatural.Peano, ∀ (first : Decimal)
        (n m : CardinalNatural.Decimal),
        n.toPeano = k → m.toPeano = k →
          getElementsFrom first subtractiveCommonDifference n =
            getElementsFrom first subtractiveCommonDifference m := by
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
      have hne0 : n.toPeano ≠ CardinalNatural.Peano.zero := by
        rw [hn]
        exact CardinalNatural.Peano.successor_ne_zero k
      have hme0 : m.toPeano ≠ CardinalNatural.Peano.zero := by
        rw [hm]
        exact CardinalNatural.Peano.successor_ne_zero k
      have hne : ¬ n ≈ CardinalNatural.Decimal.zero :=
        not_equivalent_zero_of_toPeano_ne_zero n hne0
      have hme : ¬ m ≈ CardinalNatural.Decimal.zero :=
        not_equivalent_zero_of_toPeano_ne_zero m hme0
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
    subtractiveCommonDifference : Decimal) (n : CardinalNatural.Decimal)
    (h : first ≈ first') :
    Sequences.List.SameLengthElementwiseRelation (· ≈ ·)
      (getElementsFrom first subtractiveCommonDifference n)
      (getElementsFrom first' subtractiveCommonDifference n) := by
  have hgen :
      ∀ k : CardinalNatural.Peano, ∀ (first first' : Decimal)
        (n : CardinalNatural.Decimal),
        n.toPeano = k → first ≈ first' →
          Sequences.List.SameLengthElementwiseRelation (· ≈ ·)
            (getElementsFrom first subtractiveCommonDifference n)
            (getElementsFrom first' subtractiveCommonDifference n) := by
    intro k
    induction k with
    | zero =>
      intro first first' n hn _hfirst
      have hz : n ≈ CardinalNatural.Decimal.zero :=
        CardinalNatural.Decimal.equivalent_of_toPeano_eq
          (hn.trans CardinalNatural.Decimal.toPeano_zero.symm)
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
      have hne0 : n.toPeano ≠ CardinalNatural.Peano.zero := by
        rw [hn]
        exact CardinalNatural.Peano.successor_ne_zero k
      have hne : ¬ n ≈ CardinalNatural.Decimal.zero :=
        not_equivalent_zero_of_toPeano_ne_zero n hne0
      obtain ⟨hne_peano, hpred⟩ :=
        CardinalNatural.Decimal.predecessor_toPeano n hne
      have hpred_k : (n.predecessor hne).toPeano = k := by
        rw [hpred]
        apply Eq.symm
        apply CardinalNatural.Peano.successor_injective
        rw [CardinalNatural.Peano.successor_predecessor n.toPeano hne_peano, hn]
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
    Decimal) (n : CardinalNatural.Decimal) (k : CardinalNatural.Peano)
    (hn : n.toPeano = CardinalNatural.Peano.successor k) :
    ∃ (hne : ¬ n ≈ CardinalNatural.Decimal.zero),
      getElementsFrom first subtractiveCommonDifference n =
        Sequences.List.firstElement first
          (match trySubtract first subtractiveCommonDifference with
           | none => Sequences.List.empty
           | some next =>
             getElementsFrom next subtractiveCommonDifference
               (n.predecessor hne)) ∧
      (n.predecessor hne).toPeano = k := by
  have hne0 : n.toPeano ≠ CardinalNatural.Peano.zero := by
    rw [hn]
    exact CardinalNatural.Peano.successor_ne_zero k
  have hne : ¬ n ≈ CardinalNatural.Decimal.zero :=
    not_equivalent_zero_of_toPeano_ne_zero n hne0
  obtain ⟨hne_peano, hpred⟩ := CardinalNatural.Decimal.predecessor_toPeano n hne
  refine ⟨hne, ?_, ?_⟩
  · conv => lhs; unfold getElementsFrom
    simp only [hne, ↓reduceDIte]
  · rw [hpred]
    apply Eq.symm
    apply CardinalNatural.Peano.successor_injective
    rw [CardinalNatural.Peano.successor_predecessor n.toPeano hne_peano, hn]

/-- Expanding `getElementsFrom` when the subtractive step succeeds. -/
theorem getElementsFrom_succ_of_trySubtract (first subtractiveCommonDifference
    next : Decimal) (n : CardinalNatural.Decimal) (k : CardinalNatural.Peano)
    (hn : n.toPeano = CardinalNatural.Peano.successor k)
    (h : trySubtract first subtractiveCommonDifference = some next) :
    ∃ (hne : ¬ n ≈ CardinalNatural.Decimal.zero),
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
    (n : CardinalNatural.Decimal) :
    (getElementsFrom first subtractiveCommonDifference n).length =
      (Peano.Progressions.ArithmeticDecreasing.getElementsFrom
        first.toPeano subtractiveCommonDifference.toPeano n.toPeano).length := by
  have hgen :
      ∀ k : CardinalNatural.Peano, ∀ (first : Decimal)
        (n : CardinalNatural.Decimal),
        n.toPeano = k →
          (getElementsFrom first subtractiveCommonDifference n).length =
            (Peano.Progressions.ArithmeticDecreasing.getElementsFrom
              first.toPeano subtractiveCommonDifference.toPeano k).length := by
    intro k
    induction k with
    | zero =>
      intro first n hn
      have hz : n ≈ CardinalNatural.Decimal.zero :=
        CardinalNatural.Decimal.equivalent_of_toPeano_eq
          (hn.trans CardinalNatural.Decimal.toPeano_zero.symm)
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
              CardinalNatural.Peano.zero).length
      rfl
    | successor k ih =>
      intro first n hn
      have hne0 : n.toPeano ≠ CardinalNatural.Peano.zero := by
        rw [hn]
        exact CardinalNatural.Peano.successor_ne_zero k
      have hne : ¬ n ≈ CardinalNatural.Decimal.zero :=
        not_equivalent_zero_of_toPeano_ne_zero n hne0
      obtain ⟨hne_peano, hpred⟩ :=
        CardinalNatural.Decimal.predecessor_toPeano n hne
      have hpred_k : (n.predecessor hne).toPeano = k := by
        rw [hpred]
        apply Eq.symm
        apply CardinalNatural.Peano.successor_injective
        rw [CardinalNatural.Peano.successor_predecessor n.toPeano hne_peano, hn]
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
                (CardinalNatural.Peano.successor k)).length
        simp only [Peano.Progressions.ArithmeticDecreasing.getElementsFrom,
          hs_peano]
        change
            CardinalNatural.Peano.one =
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
                (CardinalNatural.Peano.successor k) =
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
          (CardinalNatural.Decimal.fromPeano rest.length).successor ∧
      ∀ next, trySubtract prev diff = some next →
        Sequences.List.SameLengthElementwiseRelation (· ≈ ·)
          (getElementsFrom next diff
            (CardinalNatural.Decimal.fromPeano rest.length))
          rest := by
  induction rest generalizing prev last with
  | empty =>
    simp only [tryLastOfArithmeticContinuation] at h
    injection h with heq
    constructor
    · subst heq
      apply equivalent_of_toPeano_eq
      rw [lastElementFrom_toPeano, CardinalNatural.Decimal.successor_toPeano,
        CardinalNatural.Decimal.toPeano_fromPeano]
      change prev.toPeano =
        Peano.Progressions.ArithmeticDecreasing.lastElementFrom
          prev.toPeano diff.toPeano CardinalNatural.Peano.one
      rfl
    · intro next _hs
      have hz :
          CardinalNatural.Decimal.fromPeano CardinalNatural.Peano.zero ≈
            CardinalNatural.Decimal.zero :=
        CardinalNatural.Decimal.equivalent_of_toPeano_eq
          ((CardinalNatural.Decimal.toPeano_fromPeano
              CardinalNatural.Peano.zero).trans
            CardinalNatural.Decimal.toPeano_zero.symm)
      have hexpand :
          getElementsFrom next diff
              (CardinalNatural.Decimal.fromPeano CardinalNatural.Peano.zero) =
            Sequences.List.empty := by
        conv => lhs; unfold getElementsFrom
        simp only [hz, ↓reduceDIte]
      change Sequences.List.SameLengthElementwiseRelation (· ≈ ·)
        (getElementsFrom next diff
          (CardinalNatural.Decimal.fromPeano
            (Sequences.List.empty : Sequences.List Decimal).length))
        Sequences.List.empty
      rw [show (Sequences.List.empty : Sequences.List Decimal).length =
          CardinalNatural.Peano.zero from rfl, hexpand]
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
          Setoid.trans (equivalent_of_trySubtract_add x prev d hs)
            (equivalent_add (Setoid.refl x) hd)
        have hlen := Sequences.List.length_firstElement x xs
        constructor
        · have h1 :
              last ≈
                lastElementFrom x diff
                  (CardinalNatural.Decimal.fromPeano xs.length).successor :=
            hlast
          have h2 :
              lastElementFrom x diff
                  (CardinalNatural.Decimal.fromPeano xs.length).successor ≈
                lastElementFrom prev diff
                  (CardinalNatural.Decimal.fromPeano
                    (Sequences.List.firstElement x xs).length).successor := by
            apply equivalent_of_toPeano_eq
            rw [lastElementFrom_toPeano, lastElementFrom_toPeano,
              CardinalNatural.Decimal.successor_toPeano,
              CardinalNatural.Decimal.successor_toPeano,
              CardinalNatural.Decimal.toPeano_fromPeano,
              CardinalNatural.Decimal.toPeano_fromPeano, hlen]
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
              (CardinalNatural.Decimal.fromPeano
                  (Sequences.List.firstElement x xs).length).toPeano =
                CardinalNatural.Peano.successor xs.length := by
            rw [CardinalNatural.Decimal.toPeano_fromPeano, hlen]
          have hmid :
              Sequences.List.SameLengthElementwiseRelation (· ≈ ·)
                (getElementsFrom next diff
                  (CardinalNatural.Decimal.fromPeano
                    (Sequences.List.firstElement x xs).length))
                (getElementsFrom x diff
                  (CardinalNatural.Decimal.fromPeano
                    (Sequences.List.firstElement x xs).length)) :=
            getElementsFrom_rel_of_equivalent_first next x diff
              (CardinalNatural.Decimal.fromPeano
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
                      Setoid.trans (equivalent_of_trySubtract_add y x d' hsy)
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
                (CardinalNatural.Decimal.fromPeano
                  (Sequences.List.firstElement x Sequences.List.empty).length)
                CardinalNatural.Peano.zero hn
            have hexpand' :
                getElementsFrom x diff
                    (CardinalNatural.Decimal.fromPeano
                      (Sequences.List.firstElement x
                        Sequences.List.empty).length) =
                  Sequences.List.firstElement x Sequences.List.empty := by
              rw [hexpand, hsx]
            have htail :
                Sequences.List.SameLengthElementwiseRelation (· ≈ ·)
                  (getElementsFrom x diff
                    (CardinalNatural.Decimal.fromPeano
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
                (CardinalNatural.Decimal.fromPeano
                  (Sequences.List.firstElement x xs).length)
                xs.length hn hsx
            have hpred_eq :
                getElementsFrom next' diff
                    ((CardinalNatural.Decimal.fromPeano
                        (Sequences.List.firstElement x xs).length).predecessor
                      hne) =
                  getElementsFrom next' diff
                    (CardinalNatural.Decimal.fromPeano xs.length) :=
              getElementsFrom_eq_of_toPeano_eq next' diff _ _
                (hpred.trans (CardinalNatural.Decimal.toPeano_fromPeano _).symm)
            have htail :
                Sequences.List.SameLengthElementwiseRelation (· ≈ ·)
                  (getElementsFrom x diff
                    (CardinalNatural.Decimal.fromPeano
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
    (n : CardinalNatural.Decimal)
    (hne : ¬ n ≈ CardinalNatural.Decimal.zero)
    (hd : diff ≈ subtractiveCommonDifference)
    (hl : last ≈ lastElementFrom first subtractiveCommonDifference n)
    (hlen : (getElementsFrom first subtractiveCommonDifference n).length =
      n.toPeano) :
    getLength {
      first := some first
      subtractiveCommonDifference := diff
      limit := last
    } ≈ n := by
  apply CardinalNatural.Decimal.equivalent_of_toPeano_eq
  have hstruct :
      toPeano {
        first := some first
        subtractiveCommonDifference := diff
        limit := last
      } =
        {
          first := some first.toPeano
          subtractiveCommonDifference := diff.toPeano
          limit := last.toPeano
        } := by
    simp only [toPeano]
  rw [getLength_toPeano, hstruct]
  have hlim :
      last.toPeano =
        Peano.Progressions.ArithmeticDecreasing.lastElementFrom
          first.toPeano subtractiveCommonDifference.toPeano n.toPeano := by
    rw [toPeano_eq_of_equivalent hl, lastElementFrom_toPeano]
  have hdiff : diff.toPeano = subtractiveCommonDifference.toPeano :=
    toPeano_eq_of_equivalent hd
  have hlen_peano :
      (Peano.Progressions.ArithmeticDecreasing.getElementsFrom
          first.toPeano subtractiveCommonDifference.toPeano n.toPeano).length =
        n.toPeano := by
    rw [← getElementsFrom_length_eq_peano_getElementsFrom first
      subtractiveCommonDifference n, hlen]
  rw [hlim, hdiff]
  exact
    Peano.Progressions.ArithmeticDecreasing.getLength_lastElementFrom
      first.toPeano subtractiveCommonDifference.toPeano n.toPeano
      (CardinalNatural.Decimal.toPeano_ne_zero_of_not_equivalent_zero hne)
      hlen_peano

/-- When the limit is equivalent to `lastElementFrom` of a positive length, the
effective first element is `some first`. -/
theorem effectiveFirst_of_equivalent_lastElementFrom (first
    subtractiveCommonDifference diff last : Decimal)
    (n : CardinalNatural.Decimal)
    (_hne : ¬ n ≈ CardinalNatural.Decimal.zero)
    (hl : last ≈ lastElementFrom first subtractiveCommonDifference n) :
    effectiveFirst {
      first := some first
      subtractiveCommonDifference := diff
      limit := last
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
    (hge : CardinalNatural.Peano.two ≤ elements.length)
    (p : ArithmeticDecreasing)
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
    match hs : trySubtract x y with
    | none =>
      simp only [hs] at h
      nomatch h
    | some diff =>
      simp only [hs] at h
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
          equivalent_of_trySubtract_add y x diff hs
        have hrel := trySubtract_of_equivalent_add_right hx
        obtain ⟨y', hy_eq, hy_rel⟩ :=
          InfiniteArithmetic.exists_of_option_rel_some hrel
        have hrest := hrest_forall y' hy_eq
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
              subtractiveCommonDifference := diff
              limit := last
            } = some x :=
          effectiveFirst_of_equivalent_lastElementFrom x diff diff last n hne
            hlast
        have hn :
            n.toPeano =
              CardinalNatural.Peano.successor
                (Sequences.List.firstElement y ys).length := by
          rw [CardinalNatural.Decimal.successor_toPeano,
            CardinalNatural.Decimal.toPeano_fromPeano]
        obtain ⟨hne_n, hexpand, hpred⟩ :=
          getElementsFrom_succ_of_trySubtract x diff y' n
            (Sequences.List.firstElement y ys).length hn hy_eq
        have hpred_eq :
            getElementsFrom y' diff (n.predecessor hne_n) =
              getElementsFrom y' diff
                (CardinalNatural.Decimal.fromPeano
                  (Sequences.List.firstElement y ys).length) :=
          getElementsFrom_eq_of_toPeano_eq y' diff _ _
            (hpred.trans (CardinalNatural.Decimal.toPeano_fromPeano _).symm)
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
                } ≈ n :=
          getLength_of_equivalent_lastElementFrom x diff diff last n hne
            (Setoid.refl diff) hlast hlen_walk
        have hget :
            getElements
                {
                  first := some x
                  subtractiveCommonDifference := diff
                  limit := last
                } =
              getElementsFrom x diff
                (getLength
                  {
                    first := some x
                    subtractiveCommonDifference := diff
                    limit := last
                  }) := by
          simp only [getElements, hf]
        rw [hget]
        have hlen_toPeano :
            (getLength
                {
                  first := some x
                  subtractiveCommonDifference := diff
                  limit := last
                }).toPeano =
              n.toPeano :=
          CardinalNatural.Decimal.toPeano_eq_of_equivalent hlenp
        have hget' :
            getElementsFrom x diff
                (getLength
                  {
                    first := some x
                    subtractiveCommonDifference := diff
                    limit := last
                  }) =
              getElementsFrom x diff n :=
          getElementsFrom_eq_of_toPeano_eq x diff _ _ hlen_toPeano
        rw [hget', hexpand, hpred_eq]
        have hmid :
            Sequences.List.SameLengthElementwiseRelation (· ≈ ·)
              (getElementsFrom y' diff
                (CardinalNatural.Decimal.fromPeano
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
    (equivalent_of_trySubtract_add diff first next h)

/-- A `getElementsFrom` walk of length at least two has a defined first
subtractive step. -/
theorem trySubtract_eq_some_of_getElementsFrom_length_ge_two
    (first subtractiveCommonDifference : Decimal) (n : CardinalNatural.Decimal)
    (hge : CardinalNatural.Peano.two ≤
      (getElementsFrom first subtractiveCommonDifference n).length) :
    ∃ next, trySubtract first subtractiveCommonDifference = some next := by
  by_cases hz : n ≈ CardinalNatural.Decimal.zero
  · have hexpand :
        getElementsFrom first subtractiveCommonDifference n =
          Sequences.List.empty := by
      conv => lhs; unfold getElementsFrom
      simp only [hz, ↓reduceDIte]
    rw [hexpand] at hge
    exact (CardinalNatural.Peano.not_two_le_zero (by
      change CardinalNatural.Peano.two ≤ CardinalNatural.Peano.zero
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
            CardinalNatural.Peano.one := by
        rw [hexpand', Sequences.List.length_firstElement]
        rfl
      rw [hlen] at hge
      exact (CardinalNatural.Peano.not_two_le_one hge).elim
    | some next =>
      exact ⟨next, rfl⟩

/-- Continuing a decreasing arithmetic walk from `prev` by `getElementsFrom`
recovers a last element equivalent to `lastElementFrom`, when the first step
from `prev` is defined and the reconstructed difference is equivalent to the
walk difference. -/
theorem tryLastOfArithmeticContinuation_getElementsFrom
    (prev subtractiveCommonDifference diff next : Decimal)
    (n : CardinalNatural.Decimal)
    (hd : diff ≈ subtractiveCommonDifference)
    (h : trySubtract prev subtractiveCommonDifference = some next) :
    Option.Rel (· ≈ ·)
      (tryLastOfArithmeticContinuation prev diff
        (getElementsFrom next subtractiveCommonDifference n))
      (some (lastElementFrom prev subtractiveCommonDifference n.successor)) := by
  have hgen :
      ∀ k : CardinalNatural.Peano, ∀ (prev next : Decimal)
        (n : CardinalNatural.Decimal),
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
      have hz : n ≈ CardinalNatural.Decimal.zero :=
        CardinalNatural.Decimal.equivalent_of_toPeano_eq
          (hn.trans CardinalNatural.Decimal.toPeano_zero.symm)
      have hexpand :
          getElementsFrom next subtractiveCommonDifference n =
            Sequences.List.empty := by
        conv => lhs; unfold getElementsFrom
        simp only [hz, ↓reduceDIte]
      rw [hexpand, tryLastOfArithmeticContinuation]
      apply Option.Rel.some
      apply equivalent_of_toPeano_eq
      rw [lastElementFrom_toPeano, CardinalNatural.Decimal.successor_toPeano, hn]
      change prev.toPeano =
        Peano.Progressions.ArithmeticDecreasing.lastElementFrom
          prev.toPeano subtractiveCommonDifference.toPeano
          (CardinalNatural.Peano.successor CardinalNatural.Peano.zero)
      rfl
    | successor k ih =>
      intro prev next n hn hs
      have hne0 : n.toPeano ≠ CardinalNatural.Peano.zero := by
        rw [hn]
        exact CardinalNatural.Peano.successor_ne_zero k
      have hne : ¬ n ≈ CardinalNatural.Decimal.zero :=
        not_equivalent_zero_of_toPeano_ne_zero n hne0
      obtain ⟨hne_peano, hpred⟩ :=
        CardinalNatural.Decimal.predecessor_toPeano n hne
      have hpred_k : (n.predecessor hne).toPeano = k := by
        rw [hpred]
        apply Eq.symm
        apply CardinalNatural.Peano.successor_injective
        rw [CardinalNatural.Peano.successor_predecessor n.toPeano hne_peano, hn]
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
        rw [lastElementFrom_toPeano, CardinalNatural.Decimal.successor_toPeano,
          hn]
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
                (CardinalNatural.Peano.successor
                  (CardinalNatural.Peano.successor k)) =
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
          CardinalNatural.Decimal.successor_toPeano,
          CardinalNatural.Decimal.successor_toPeano, hpred_k, hn]
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
    (n : CardinalNatural.Decimal)
    (hge : CardinalNatural.Peano.two ≤ n.toPeano)
    (hLen : CardinalNatural.Peano.two ≤
        (getElementsFrom first subtractiveCommonDifference n).length) :
    ∃ (q : ArithmeticDecreasing),
      tryFromElements (getElementsFrom first subtractiveCommonDifference n) hLen =
        some q ∧
      q.first = some first ∧
      q.subtractiveCommonDifference ≈ subtractiveCommonDifference ∧
      q.limit ≈ lastElementFrom first subtractiveCommonDifference n := by
  obtain ⟨m, hm⟩ := CardinalNatural.Peano.eq_succ_succ_of_two_le n.toPeano hge
  obtain ⟨next, hs⟩ :=
    trySubtract_eq_some_of_getElementsFrom_length_ge_two first
      subtractiveCommonDifference n hLen
  obtain ⟨hne, hexpand, hpred⟩ :=
    getElementsFrom_succ_of_trySubtract first subtractiveCommonDifference next n
      (CardinalNatural.Peano.successor m) hm hs
  have hne' : ¬ n.predecessor hne ≈ CardinalNatural.Decimal.zero :=
    not_equivalent_zero_of_toPeano_ne_zero _ (by
      rw [hpred]
      exact CardinalNatural.Peano.successor_ne_zero m)
  obtain ⟨hne_peano', hpred'⟩ :=
    CardinalNatural.Decimal.predecessor_toPeano (n.predecessor hne) hne'
  have hpred_m : ((n.predecessor hne).predecessor hne').toPeano = m := by
    rw [hpred']
    apply Eq.symm
    apply CardinalNatural.Peano.successor_injective
    rw [CardinalNatural.Peano.successor_predecessor (n.predecessor hne).toPeano
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
  match hs' : trySubtract next subtractiveCommonDifference with
  | none =>
    simp only [tryLastOfArithmeticContinuation]
    refine ⟨({
        first := some first
        subtractiveCommonDifference := diff
        limit := next
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
            (CardinalNatural.Peano.successor
              (CardinalNatural.Peano.successor m)) =
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
      } : ArithmeticDecreasing), rfl, rfl, hdiff_approx, ?_⟩
    refine Setoid.trans hlast_approx ?_
    apply equivalent_of_toPeano_eq
    rw [lastElementFrom_toPeano, lastElementFrom_toPeano,
      CardinalNatural.Decimal.successor_toPeano, hpred_m, hm]
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
    (n : CardinalNatural.Decimal)
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
  have hlen_peano :=
    Peano.Progressions.ArithmeticDecreasing.getElementsFrom_length_of_le_getLength
      (toPeano p) first.toPeano hf_peano n.toPeano hle'
  rw [getElementsFrom_length_eq_peano_getElementsFrom]
  simpa [toPeano] using hlen_peano

/-- The list of elements of a decreasing progression has Peano length equal to
the Peano embedding of `getLength`. -/
theorem getElements_length (p : ArithmeticDecreasing) :
    (getElements p).length = (getLength p).toPeano := by
  match hf : effectiveFirst p with
  | none =>
    have hlen : getLength p ≈ CardinalNatural.Decimal.zero :=
      (getLength_eq_zero_iff_effectiveFirst_none p).mpr hf
    simp only [getElements, hf]
    change CardinalNatural.Peano.zero = (getLength p).toPeano
    exact
      ((CardinalNatural.Decimal.toPeano_eq_of_equivalent hlen).trans
        CardinalNatural.Decimal.toPeano_zero).symm
  | some first =>
    simp only [getElements, hf]
    exact getElementsFrom_length_of_le_getLength p first hf (getLength p)
      (Or.inr rfl)

/-- `tryFromElements` recovers a progression equivalent to `p` from
`getElements p` when `p` has length at least two. -/
theorem tryFromElements_getElements (p : ArithmeticDecreasing)
    (hge : CardinalNatural.Peano.two ≤ (getLength p).toPeano) :
    ∃ (hLen : CardinalNatural.Peano.two ≤ (getElements p).length)
      (q : ArithmeticDecreasing),
      tryFromElements (getElements p) hLen = some q ∧ p ≈ q := by
  have hne0 : (getLength p).toPeano ≠ CardinalNatural.Peano.zero := by
    intro heq
    rw [heq] at hge
    exact CardinalNatural.Peano.not_two_le_zero hge
  have hne0' : ¬ getLength p ≈ CardinalNatural.Decimal.zero :=
    not_equivalent_zero_of_toPeano_ne_zero (getLength p) hne0
  obtain ⟨first, hf⟩ := effectiveFirst_eq_some_of_pos_length p hne0'
  have hget :
      getElements p =
        getElementsFrom first p.subtractiveCommonDifference (getLength p) := by
    simp only [getElements, hf]
  have hLen : CardinalNatural.Peano.two ≤ (getElements p).length := by
    rw [getElements_length]
    exact hge
  have hLen' : CardinalNatural.Peano.two ≤
      (getElementsFrom first p.subtractiveCommonDifference
        (getLength p)).length := by
    rw [← hget]
    exact hLen
  obtain ⟨q, htry, hfirst_q, hdiff_q, hlast_q⟩ :=
    tryFromElements_getElementsFrom_ge_two first p.subtractiveCommonDifference
      (getLength p) hge hLen'
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
        } := by
      cases q with
      | mk f d l =>
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
        (getLength p) hne0' hlast_q
    have hlen_q :
        getLength q ≈ getLength p := by
      rw [hq_rewrite]
      exact getLength_of_equivalent_lastElementFrom first
        p.subtractiveCommonDifference q.subtractiveCommonDifference q.limit
        (getLength p) hne0' hdiff_q hlast_q hlen_walk
    exact equivalence_of_equivalent_params p q first first hf hf_q
      (Setoid.refl first) (Setoid.symm hdiff_q) (Setoid.symm hlen_q)

/-- Recover the first element of a decreasing arithmetic progression from an
element at the given ordinal Decimal index and the subtractive common
difference. At an index equivalent to `one` the element is itself the first;
otherwise add `(predecessor index) * subtractiveCommonDifference`. Always
succeeds. -/
def tryFirstFromIndexedElement (index element subtractiveCommonDifference : Decimal) :
    Option Decimal :=
  if h : index ≈ one then
    some element
  else
    some (element + (index.predecessor h) * subtractiveCommonDifference)

/-- Given two ordered indexed elements (`index < index'`) of a prospective
decreasing arithmetic progression, recover the subtractive common difference
`(element - element') / (index' - index)`. Returns `none` when the elements are
not strictly descending or the element gap is not divisible by the index gap. -/
def tryCommonDifferenceFromOrderedIndexedElements
    (index element index' element' : Decimal) (hlt : index < index') :
    Option Decimal :=
  match trySubtract element element' with
  | none => none
  | some elementDiff =>
    tryDivide elementDiff (subtract index' index hlt)

/-- Reconstruct a decreasing arithmetic progression from two of its elements at
different ordinal Decimal indexes together with the progression length. Returns
`none` when either index exceeds the length, when the arithmetic walk of that
length cannot be carried out (an intermediate subtraction fails), or when the
values are not consistent with a strictly decreasing arithmetic progression of
that length. Indexes are compared up to Decimal equivalence.

The reconstructed progression uses the recovered first element and subtractive
common difference, and takes the last element of an arithmetic walk of the given
length as the limit. -/
def tryFromTwoElementsAndLength
    (index1 : Decimal) (element1 : Decimal)
    (index2 : Decimal) (element2 : Decimal)
    (length : CardinalNatural.Decimal)
    (hne : ¬ index1 ≈ index2) :
    Option ArithmeticDecreasing :=
  if CardinalNatural.Decimal.fromOrdinal index1 ≤ length then
    if CardinalNatural.Decimal.fromOrdinal index2 ≤ length then
      match compare index1 index2 with
      | .equivalent heq => False.elim (hne heq)
      | .less hlt =>
        match tryCommonDifferenceFromOrderedIndexedElements
            index1 element1 index2 element2 hlt with
        | none => none
        | some diff =>
          match tryFirstFromIndexedElement index1 element1 diff with
          | none => none
          | some first =>
            if (getElementsFrom first diff length).length = length.toPeano then
              some {
                first := some first
                subtractiveCommonDifference := diff
                limit := lastElementFrom first diff length
              }
            else
              none
      | .greater hgt =>
        match tryCommonDifferenceFromOrderedIndexedElements
            index2 element2 index1 element1 hgt with
        | none => none
        | some diff =>
          match tryFirstFromIndexedElement index2 element2 diff with
          | none => none
          | some first =>
            if (getElementsFrom first diff length).length = length.toPeano then
              some {
                first := some first
                subtractiveCommonDifference := diff
                limit := lastElementFrom first diff length
              }
            else
              none
    else
      none
  else
    none

/-- `fromOrdinal` is monotone with respect to the Decimal ordinal order. -/
theorem fromOrdinal_le_of_lt {a b : Decimal} (h : a < b) :
    CardinalNatural.Decimal.fromOrdinal a ≤
      CardinalNatural.Decimal.fromOrdinal b := by
  apply CardinalNatural.Decimal.le_of_toPeano_le
  rw [CardinalNatural.Decimal.fromOrdinal_toPeano_eq_fromOrdinal_peano,
    CardinalNatural.Decimal.fromOrdinal_toPeano_eq_fromOrdinal_peano]
  exact CardinalNatural.Peano.fromOrdinal_le_of_lt (toPeano_lt_of_lt h)

/-- In-range `getElement` agrees with `getElementFrom` on the effective first. -/
theorem getElement_eq_getElementFrom (p : ArithmeticDecreasing)
    (first : Decimal) (hf : effectiveFirst p = some first) (index : Decimal)
    (hle : CardinalNatural.Decimal.fromOrdinal index ≤ getLength p) :
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
        exact (Peano.not_lt_of_lt (toPeano_lt_of_lt hlt) (toPeano_lt_of_lt hgt)).elim
      | inr heq =>
        have hlt' := toPeano_lt_of_lt hlt
        rw [toPeano_eq_of_equivalent heq] at hlt'
        exact (Peano.not_lt_self _ hlt').elim
    | .equivalent _ =>
      rfl
    | .greater _ =>
      rfl

/-- In-range `getElementFrom` agrees with the Peano embedding of `getElementFrom`. -/
theorem getElementFrom_toPeano_of_le (p : ArithmeticDecreasing)
    (first : Decimal) (hf : effectiveFirst p = some first) (index : Decimal)
    (hle : CardinalNatural.Decimal.fromOrdinal index ≤ getLength p) :
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
      Peano.Progressions.ArithmeticDecreasing.effectiveFirst (toPeano p) =
        some first.toPeano := by
    simpa [hf, Option.map] using (effectiveFirst_toPeano p).symm
  have hle_peano :
      CardinalNatural.Peano.fromOrdinal index.toPeano ≤
        Peano.Progressions.ArithmeticDecreasing.getLength (toPeano p) := by
    have hle' := CardinalNatural.Decimal.toPeano_le_of_le hle
    rw [CardinalNatural.Decimal.fromOrdinal_toPeano_eq_fromOrdinal_peano,
      getLength_toPeano] at hle'
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
`(index' - index) * subtractiveCommonDifference` from the element, up to Decimal
equivalence. -/
theorem getElementFrom_eq_add_mul_of_lt (p : ArithmeticDecreasing)
    (first : Decimal) (hf : effectiveFirst p = some first)
    (index index' : Decimal) (hlt : index < index')
    (hle' : CardinalNatural.Decimal.fromOrdinal index' ≤ getLength p) :
    getElementFrom first p.subtractiveCommonDifference index ≈
      getElementFrom first p.subtractiveCommonDifference index' +
        (subtract index' index hlt) * p.subtractiveCommonDifference := by
  have hle :
      CardinalNatural.Decimal.fromOrdinal index ≤ getLength p :=
    CardinalNatural.Decimal.le_trans (fromOrdinal_le_of_lt hlt) hle'
  apply equivalent_of_toPeano_eq
  have hindex := getElementFrom_toPeano_of_le p first hf index hle
  have hindex' := getElementFrom_toPeano_of_le p first hf index' hle'
  rw [hindex, add_toPeano, multiplyToPeano, hindex']
  obtain ⟨hlt_peano, hsub⟩ := subtract_toPeano index' index hlt
  rw [hsub]
  have hf_peano :
      Peano.Progressions.ArithmeticDecreasing.effectiveFirst (toPeano p) =
        some first.toPeano := by
    simpa [hf, Option.map] using (effectiveFirst_toPeano p).symm
  have hle_peano :
      CardinalNatural.Peano.fromOrdinal index'.toPeano ≤
        Peano.Progressions.ArithmeticDecreasing.getLength (toPeano p) := by
    have hle'' := CardinalNatural.Decimal.toPeano_le_of_le hle'
    rw [CardinalNatural.Decimal.fromOrdinal_toPeano_eq_fromOrdinal_peano,
      getLength_toPeano] at hle''
    exact hle''
  exact
    Peano.Progressions.ArithmeticDecreasing.getElementFrom_eq_add_mul_of_lt
      (toPeano p) first.toPeano hf_peano index.toPeano index'.toPeano
      hlt_peano hle_peano

/-- Length of a progression whose limit is exactly `lastElementFrom` of its
positive length and whose walk has Peano length equal to the requested length. -/
theorem getLength_lastElementFrom (first subtractiveCommonDifference : Decimal)
    (n : CardinalNatural.Decimal) (hne : ¬ n ≈ CardinalNatural.Decimal.zero)
    (hlen : (getElementsFrom first subtractiveCommonDifference n).length =
      n.toPeano) :
    getLength {
      first := some first
      subtractiveCommonDifference := subtractiveCommonDifference
      limit := lastElementFrom first subtractiveCommonDifference n
    } ≈ n :=
  getLength_of_equivalent_lastElementFrom first subtractiveCommonDifference
    subtractiveCommonDifference
    (lastElementFrom first subtractiveCommonDifference n) n hne
    (Setoid.refl _) (Setoid.refl _) hlen

/-- Walk length depends on the start and difference only through their Peano
embeddings. -/
theorem getElementsFrom_length_eq_of_toPeano_eq
    (first first' diff diff' : Decimal) (n : CardinalNatural.Decimal)
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
    (index index' : Decimal) (hlt : index < index')
    (hle' : CardinalNatural.Decimal.fromOrdinal index' ≤ getLength p) :
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
      (InfiniteArithmetic.trySubtract_of_equivalent_add heq)
  obtain ⟨d, hdiv_eq, hdiv_approx⟩ :=
    InfiniteArithmetic.exists_of_option_rel_some
      (InfiniteArithmetic.tryDivide_of_equivalent_mul hsub_approx)
  refine ⟨d, ?_, hdiv_approx⟩
  simp only [tryCommonDifferenceFromOrderedIndexedElements, hsub_eq, hdiv_eq]

/-- Recovering the first element from an in-range indexed element of a
decreasing arithmetic progression, using an equivalent subtractive common
difference, returns a value equivalent to the effective first. -/
theorem tryFirstFromIndexedElement_getElementFrom_of_equivalent_diff
    (p : ArithmeticDecreasing) (first : Decimal)
    (hf : effectiveFirst p = some first) (index : Decimal)
    (d : Decimal) (hd : d ≈ p.subtractiveCommonDifference)
    (hle : CardinalNatural.Decimal.fromOrdinal index ≤ getLength p) :
    ∃ first',
      tryFirstFromIndexedElement index
        (getElementFrom first p.subtractiveCommonDifference index) d =
          some first' ∧
      first' ≈ first := by
  if hone : index ≈ one then
    refine ⟨getElementFrom first p.subtractiveCommonDifference index, ?_, ?_⟩
    · simp only [tryFirstFromIndexedElement, hone, ↓reduceDIte]
    · simp only [getElementFrom, hone, ↓reduceDIte]
      exact Setoid.refl _
  else
    refine
      ⟨getElementFrom first p.subtractiveCommonDifference index +
          (index.predecessor hone) * d, ?_, ?_⟩
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
            (index.predecessor hone) * p.subtractiveCommonDifference + y :=
        equivalent_of_trySubtract_add
          ((index.predecessor hone) * p.subtractiveCommonDifference) first y hy
      have hfirst_add' :
          first ≈
            y + (index.predecessor hone) * p.subtractiveCommonDifference :=
        Setoid.trans hfirst_add
          (equivalent_add_commutative
            ((index.predecessor hone) * p.subtractiveCommonDifference) y)
      rw [hget]
      refine Setoid.trans ?_ (Setoid.symm hfirst_add')
      exact
        equivalent_add_left_of_equivalent_right
          (InfiniteArithmetic.equivalent_multiply (Setoid.refl _) hd)

/-- Reconstructing from any two inequivalent in-range elements of `p`, together
with `getLength p`, yields a progression equivalent to `p`. -/
theorem tryFromTwoElementsAndLength_getElement
    (p : ArithmeticDecreasing)
    (index1 index2 : Decimal)
    (hne : ¬ index1 ≈ index2)
    (hle1 : CardinalNatural.Decimal.fromOrdinal index1 ≤ getLength p)
    (hle2 : CardinalNatural.Decimal.fromOrdinal index2 ≤ getLength p) :
    ∃ (q : ArithmeticDecreasing),
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
  obtain ⟨first, hf⟩ := effectiveFirst_eq_some_of_pos_length p hne0
  have hget1 := getElement_eq_getElementFrom p first hf index1 hle1
  have hget2 := getElement_eq_getElementFrom p first hf index2 hle2
  have hwalk :
      (getElementsFrom first p.subtractiveCommonDifference
        (getLength p)).length =
        (getLength p).toPeano :=
    getElementsFrom_length_of_le_getLength p first hf (getLength p) (Or.inr rfl)
  match hcomp : compare index1 index2 with
  | .equivalent heq =>
    exact (hne heq).elim
  | .less hlt =>
    obtain ⟨diff, hdiff_eq, hdiff_approx⟩ :=
      tryCommonDifferenceFromOrderedIndexedElements_getElementFrom
        p first hf index1 index2 hlt hle2
    obtain ⟨first', hfirst_eq, hfirst_approx⟩ :=
      tryFirstFromIndexedElement_getElementFrom_of_equivalent_diff
        p first hf index1 diff hdiff_approx hle1
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
        }, ?_, ?_⟩
    · simp only [tryFromTwoElementsAndLength, hle1, hle2, ↓reduceIte, hget1,
        hget2, hcomp, hdiff_eq, hfirst_eq, hwalk', ↓reduceIte]
    · have hf_q :
          effectiveFirst
            {
              first := some first'
              subtractiveCommonDifference := diff
              limit := lastElementFrom first' diff (getLength p)
            } =
            some first' :=
        effectiveFirst_of_equivalent_lastElementFrom first' diff diff
          (lastElementFrom first' diff (getLength p)) (getLength p) hne0
          (Setoid.refl _)
      have hlen_q :=
        getLength_lastElementFrom first' diff (getLength p) hne0 hwalk'
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
        }, ?_, ?_⟩
    · simp only [tryFromTwoElementsAndLength, hle1, hle2, ↓reduceIte, hget1,
        hget2, hcomp, hdiff_eq, hfirst_eq, hwalk', ↓reduceIte]
    · have hf_q :
          effectiveFirst
            {
              first := some first'
              subtractiveCommonDifference := diff
              limit := lastElementFrom first' diff (getLength p)
            } =
            some first' :=
        effectiveFirst_of_equivalent_lastElementFrom first' diff diff
          (lastElementFrom first' diff (getLength p)) (getLength p) hne0
          (Setoid.refl _)
      have hlen_q :=
        getLength_lastElementFrom first' diff (getLength p) hne0 hwalk'
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
    (index : Decimal) (elements : Sequences.List (Option Decimal)) : Bool :=
  match effectiveFirst p with
  | none =>
    agreesWithMaskedElementsFromCurrent p.subtractiveCommonDifference p.limit
      none elements
  | some first =>
    if CardinalNatural.Decimal.fromOrdinal index ≤ getLength p then
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
    (index1 : Decimal) (element1 : Decimal) (length : CardinalNatural.Decimal)
    (index : Decimal) (hlt : index1 < index) :
    (elements : Sequences.List (Option Decimal)) →
    CardinalNatural.Peano.one ≤ elements.unmaskedCount →
    Option ArithmeticDecreasing
  | .empty, hge =>
      False.elim (CardinalNatural.Peano.not_succ_le_zero (by
        simpa only [Sequences.List.unmaskedCount, CardinalNatural.Peano.one]
          using hge))
  | .firstElement none rest, hge =>
      tryFromMaskedElementsGivenOne index1 element1 length
        index.successor (lt_trans hlt (x_lt_succ_x index)) rest (by
          simpa only [Sequences.List.unmaskedCount] using hge)
  | .firstElement (some element2) rest, _ =>
      match
        tryFromTwoElementsAndLength index1 element1 index element2 length
          (not_equivalent_of_lt hlt) with
      | none => none
      | some p =>
        if agreesWithMaskedElementsFrom p index.successor rest then
          some p
        else
          none

/-- Scan a masked element list from the given ordinal Decimal index until the
first unmasked entry is found, then continue with
`tryFromMaskedElementsGivenOne`. -/
def tryFromMaskedElementsFrom (index : Decimal)
    (length : CardinalNatural.Decimal) :
    (elements : Sequences.List (Option Decimal)) →
    CardinalNatural.Peano.two ≤ elements.unmaskedCount →
    Option ArithmeticDecreasing
  | .empty, hge =>
      False.elim (CardinalNatural.Peano.not_two_le_zero (by
        simpa only [Sequences.List.unmaskedCount] using hge))
  | .firstElement none rest, hge =>
      tryFromMaskedElementsFrom index.successor length rest (by
        simpa only [Sequences.List.unmaskedCount] using hge)
  | .firstElement (some x) rest, hge =>
      tryFromMaskedElementsGivenOne index x length
        index.successor (x_lt_succ_x index) rest (by
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
    (hge : CardinalNatural.Peano.two ≤ elements.unmaskedCount) :
    Option ArithmeticDecreasing :=
  tryFromMaskedElementsFrom one
    (CardinalNatural.Decimal.fromPeano elements.length) elements hge

end ArithmeticDecreasing

end ZeroMath.Numbers.OrdinalNatural.Decimal.Progressions
