import ZeroMath.Numbers.CardinalNatural.Decimal

namespace ZeroMath.Numbers.CardinalNatural.Decimal

/-- A written two-digit number: a normalized decimal with exactly two digits. -/
def TwoDigit (d : Decimal) : Prop :=
  d.isNormalized = true ∧ d.val.length = Peano.two

def isTwoDigit (d : Decimal) : Bool :=
  d.isNormalized && decide (d.val.length = Peano.two)

theorem isTwoDigit_eq_true_iff (d : Decimal) :
    isTwoDigit d = true ↔ TwoDigit d := by
  simp [isTwoDigit, TwoDigit, Bool.and_eq_true, decide_eq_true_eq]

instance decidableTwoDigit (d : Decimal) : Decidable (TwoDigit d) :=
  decidable_of_iff' (isTwoDigit d = true) (isTwoDigit_eq_true_iff d).symm

theorem length_singleton {α : Type} (x : α) :
    (Sequences.List.firstElement x Sequences.List.empty).length = Peano.one :=
  Sequences.List.length_firstElement x Sequences.List.empty

theorem length_two_digits {α : Type} (a b : α) :
    (Sequences.List.firstElement a
      (Sequences.List.firstElement b Sequences.List.empty)).length = Peano.two := by
  rw [Sequences.List.length_firstElement, length_singleton]
  rfl

theorem eq_two_digits_of_length_two {α : Type} (l : Sequences.List α)
    (h : l.length = Peano.two) :
    ∃ a b, l = Sequences.List.firstElement a
      (Sequences.List.firstElement b Sequences.List.empty) := by
  cases l with
  | empty =>
    cases h
  | firstElement a rest =>
    cases rest with
    | empty =>
      have hlen : Peano.one = Peano.two := by
        simpa [length_singleton] using h
      cases hlen
    | firstElement b rest2 =>
      cases rest2 with
      | empty => exact ⟨a, b, rfl⟩
      | firstElement _ cs =>
        have hlen :
            Peano.successor (Peano.successor (Peano.successor cs.length)) = Peano.two := by
          simpa [Sequences.List.length_firstElement] using h
        have hzero : cs.length.successor = Peano.zero :=
          Peano.successor_injective (Peano.successor_injective hlen)
        exact (Peano.successor_ne_zero _ hzero).elim

theorem twoDigit_eq_digits (d : Decimal) (h : TwoDigit d) :
    ∃ tens ones, d.val = Sequences.List.firstElement tens
        (Sequences.List.firstElement ones Sequences.List.empty) ∧
      DigitIsNonZero tens := by
  obtain ⟨tens, ones, hval⟩ := eq_two_digits_of_length_two d.val h.2
  refine ⟨tens, ones, hval, ?_⟩
  have hnorm : d.isNormalized = true := h.1
  unfold isNormalized isNormalizedList at hnorm
  rw [hval] at hnorm
  simpa [DigitIsNonZero, decide_eq_true_eq] using hnorm

/-- The tens digit of a two-digit number. -/
def getTensDigit (d : Decimal) (_h : TwoDigit d) : Digit :=
  match hval : d.val with
  | .empty => False.elim (d.property hval)
  | .firstElement tens _ => tens

/-- The ones digit of a two-digit number. -/
def getOnesDigit (d : Decimal) (_h : TwoDigit d) : Digit :=
  lastDigit d

theorem getTensDigit_eq (d : Decimal) (h : TwoDigit d)
    {tens ones : Digit}
    (hval : d.val = Sequences.List.firstElement tens
      (Sequences.List.firstElement ones Sequences.List.empty)) :
    getTensDigit d h = tens := by
  unfold getTensDigit
  split
  · next heq =>
      exact False.elim (d.property heq)
  · next tens' rest heq =>
      injection heq.symm.trans hval with htens

theorem lastElement_congr {α : Type} {l1 l2 : Sequences.List α}
    (h1 : l1 ≠ Sequences.List.empty) (heq : l1 = l2) :
    Sequences.List.lastElement l1 h1 =
      Sequences.List.lastElement l2 (heq ▸ h1) := by
  cases heq
  rfl

theorem getOnesDigit_eq (d : Decimal) (h : TwoDigit d)
    {tens ones : Digit}
    (hval : d.val = Sequences.List.firstElement tens
      (Sequences.List.firstElement ones Sequences.List.empty)) :
    getOnesDigit d h = ones := by
  unfold getOnesDigit lastDigit
  rw [lastElement_congr d.property hval]
  rfl

/-- Construct a two-digit number from a nonzero tens digit and an ones digit. -/
def fromTwoDigits (tens ones : Digit) (_h : DigitIsNonZero tens) : Decimal :=
  ⟨Sequences.List.firstElement tens
    (Sequences.List.firstElement ones Sequences.List.empty), by simp⟩

theorem fromTwoDigits_isNormalized (tens ones : Digit) (h : DigitIsNonZero tens) :
    (fromTwoDigits tens ones h).isNormalized = true := by
  unfold fromTwoDigits isNormalized isNormalizedList DigitIsNonZero at *
  simpa [decide_eq_true_eq] using h

theorem fromTwoDigits_twoDigit (tens ones : Digit) (h : DigitIsNonZero tens) :
    TwoDigit (fromTwoDigits tens ones h) :=
  ⟨fromTwoDigits_isNormalized tens ones h, length_two_digits tens ones⟩

theorem getTensDigit_fromTwoDigits (tens ones : Digit) (h : DigitIsNonZero tens) :
    getTensDigit (fromTwoDigits tens ones h) (fromTwoDigits_twoDigit tens ones h) = tens :=
  getTensDigit_eq _ _ rfl

theorem getOnesDigit_fromTwoDigits (tens ones : Digit) (h : DigitIsNonZero tens) :
    getOnesDigit (fromTwoDigits tens ones h) (fromTwoDigits_twoDigit tens ones h) = ones :=
  getOnesDigit_eq _ _ rfl

/-- The tens place-value addend: the tens digit followed by a zero, for example `40` from `47`. -/
def tensPlaceAddend (d : Decimal) (h : TwoDigit d) : Decimal :=
  fromTwoDigits (getTensDigit d h) zeroDigit (by
    obtain ⟨tens, ones, hval, hnz⟩ := twoDigit_eq_digits d h
    simpa [getTensDigit_eq d h hval] using hnz)

/-- The ones place-value addend: the ones digit as a one-digit number, for example `7` from `47`. -/
def onesPlaceAddend (d : Decimal) (h : TwoDigit d) : Decimal :=
  ⟨Sequences.List.firstElement (getOnesDigit d h) Sequences.List.empty, by simp⟩

/-- The pair of place-value addends of a two-digit number. -/
def placeAddends (d : Decimal) (h : TwoDigit d) : Decimal × Decimal :=
  (tensPlaceAddend d h, onesPlaceAddend d h)

def tryPlaceAddends (d : Decimal) : Option (Decimal × Decimal) :=
  if h : isTwoDigit d then
    some (placeAddends d ((isTwoDigit_eq_true_iff d).mp h))
  else
    none

theorem tensPlaceAddend_val (d : Decimal) (h : TwoDigit d)
    {tens ones : Digit}
    (hval : d.val = Sequences.List.firstElement tens
      (Sequences.List.firstElement ones Sequences.List.empty)) :
    (tensPlaceAddend d h).val =
      Sequences.List.firstElement tens
        (Sequences.List.firstElement zeroDigit Sequences.List.empty) := by
  unfold tensPlaceAddend fromTwoDigits
  simp only [getTensDigit_eq d h hval]

theorem onesPlaceAddend_val (d : Decimal) (h : TwoDigit d)
    {tens ones : Digit}
    (hval : d.val = Sequences.List.firstElement tens
      (Sequences.List.firstElement ones Sequences.List.empty)) :
    (onesPlaceAddend d h).val =
      Sequences.List.firstElement ones Sequences.List.empty := by
  unfold onesPlaceAddend
  simp only [getOnesDigit_eq d h hval]

theorem tenPower_one : Peano.tenPower Peano.one = Peano.ten := by
  rw [show Peano.one = Peano.zero + Peano.one from (Peano.zero_add Peano.one).symm,
    Peano.tenPower_add_one, Peano.tenPower, Peano.multiply_one]

theorem toCardinalNaturalPeano_two_digits (tens ones : Digit) :
    toCardinalNaturalPeano
      (Sequences.List.firstElement tens
        (Sequences.List.firstElement ones Sequences.List.empty)) Peano.zero =
      tens.val * Peano.ten + ones.val := by
  rw [toCardinalNaturalPeano_firstElement, length_singleton, tenPower_one,
    toCardinalNaturalPeano_firstElement, Sequences.List.length, Peano.tenPower,
    Peano.multiply_one]
  change tens.val * Peano.ten + (ones.val + Peano.zero) = tens.val * Peano.ten + ones.val
  rw [Peano.add_zero]

theorem toPeano_of_twoDigit (d : Decimal) (h : TwoDigit d) :
    d.toPeano = (getTensDigit d h).val * Peano.ten + (getOnesDigit d h).val := by
  obtain ⟨tens, ones, hval, _⟩ := twoDigit_eq_digits d h
  unfold toPeano
  rw [hval, toCardinalNaturalPeano_two_digits, getTensDigit_eq d h hval,
    getOnesDigit_eq d h hval]

theorem tensPlaceAddend_toPeano (d : Decimal) (h : TwoDigit d) :
    (tensPlaceAddend d h).toPeano = (getTensDigit d h).val * Peano.ten := by
  obtain ⟨tens, ones, hval, _⟩ := twoDigit_eq_digits d h
  unfold toPeano
  rw [tensPlaceAddend_val d h hval, toCardinalNaturalPeano_two_digits,
    getTensDigit_eq d h hval, zeroDigit, Peano.add_zero]

theorem onesPlaceAddend_toPeano (d : Decimal) (h : TwoDigit d) :
    (onesPlaceAddend d h).toPeano = (getOnesDigit d h).val := by
  obtain ⟨tens, ones, hval, _⟩ := twoDigit_eq_digits d h
  unfold toPeano
  rw [onesPlaceAddend_val d h hval, toCardinalNaturalPeano_firstElement,
    Sequences.List.length, Peano.tenPower, Peano.multiply_one]
  change ones.val + Peano.zero = (getOnesDigit d h).val
  rw [Peano.add_zero, getOnesDigit_eq d h hval]

theorem toPeano_eq_placeAddends_add (d : Decimal) (h : TwoDigit d) :
    d.toPeano = (tensPlaceAddend d h + onesPlaceAddend d h).toPeano := by
  rw [add_toPeano, toPeano_of_twoDigit d h, tensPlaceAddend_toPeano,
    onesPlaceAddend_toPeano]

theorem addLists_tens_zero_ones (tens ones : Digit) :
    addLists
      (Sequences.List.firstElement tens
        (Sequences.List.firstElement zeroDigit Sequences.List.empty))
      (Sequences.List.firstElement ones Sequences.List.empty) =
      Sequences.List.firstElement tens
        (Sequences.List.firstElement ones Sequences.List.empty) := by
  rcases digit_cases tens with h | h | h | h | h | h | h | h | h | h <;>
    subst h <;>
  rcases digit_cases ones with h | h | h | h | h | h | h | h | h | h <;>
    subst h <;>
    rfl

/-- A two-digit number equals the sum of its place-value addends. -/
theorem eq_tensPlaceAddend_add_onesPlaceAddend (d : Decimal) (h : TwoDigit d) :
    d = tensPlaceAddend d h + onesPlaceAddend d h := by
  obtain ⟨tens, ones, hval, _⟩ := twoDigit_eq_digits d h
  apply Subtype.ext
  change d.val = addLists (tensPlaceAddend d h).val (onesPlaceAddend d h).val
  rw [hval, tensPlaceAddend_val d h hval, onesPlaceAddend_val d h hval,
    addLists_tens_zero_ones]

theorem tryPlaceAddends_eq_some_of_twoDigit (d : Decimal) (h : TwoDigit d) :
    tryPlaceAddends d = some (placeAddends d h) := by
  unfold tryPlaceAddends
  have htrue : isTwoDigit d = true := (isTwoDigit_eq_true_iff d).mpr h
  simp only [htrue, ↓reduceDIte]

theorem tryPlaceAddends_eq_none_of_not_twoDigit (d : Decimal) (h : ¬ TwoDigit d) :
    tryPlaceAddends d = none := by
  unfold tryPlaceAddends
  split
  · next ht =>
      exact False.elim (h ((isTwoDigit_eq_true_iff d).mp ht))
  · rfl

example : isTwoDigit (fromTwoDigits fourDigit sevenDigit (by decide)) = true := rfl

example :
    (tensPlaceAddend (fromTwoDigits fourDigit sevenDigit (by decide))
      (fromTwoDigits_twoDigit fourDigit sevenDigit (by decide))).val =
      (fromTwoDigits fourDigit zeroDigit (by decide)).val :=
  tensPlaceAddend_val (fromTwoDigits fourDigit sevenDigit (by decide))
    (fromTwoDigits_twoDigit fourDigit sevenDigit (by decide)) rfl

example :
    (onesPlaceAddend (fromTwoDigits fourDigit sevenDigit (by decide))
      (fromTwoDigits_twoDigit fourDigit sevenDigit (by decide))).val =
      Sequences.List.firstElement sevenDigit Sequences.List.empty :=
  onesPlaceAddend_val (fromTwoDigits fourDigit sevenDigit (by decide))
    (fromTwoDigits_twoDigit fourDigit sevenDigit (by decide)) rfl

example :
    let n := fromTwoDigits fourDigit sevenDigit (by decide)
    n = tensPlaceAddend n (fromTwoDigits_twoDigit fourDigit sevenDigit (by decide)) +
      onesPlaceAddend n (fromTwoDigits_twoDigit fourDigit sevenDigit (by decide)) :=
  eq_tensPlaceAddend_add_onesPlaceAddend _
    (fromTwoDigits_twoDigit fourDigit sevenDigit (by decide))

end ZeroMath.Numbers.CardinalNatural.Decimal
