import ZeroMath.Numbers.CardinalNatural.Decimal

namespace ZeroMath.Numbers.CardinalNatural.Decimal

/-- A one-digit decimal number. -/
def fromDigit (d : Digit) : Decimal :=
  ⟨Sequences.List.firstElement d Sequences.List.empty, by simp⟩

theorem fromDigit_toPeano (d : Digit) : (fromDigit d).toPeano = d.val := by
  unfold toPeano fromDigit
  rw [toCardinalNaturalPeano_firstElement, Sequences.List.length, Peano.tenPower,
    Peano.multiply_one]
  change d.val + Peano.zero = d.val
  rw [Peano.add_zero]

theorem fromDigit_isNormalized (d : Digit) : (fromDigit d).isNormalized = true :=
  rfl

/-- The place-value addend of a digit followed by `trailingZeros` zeros.
    A zero digit is the number `0` at every place, so `1005` yields `[1000, 0, 0, 5]`.
    A nonzero digit `4` with one trailing zero is `40`. -/
def placeAddend (d : Digit) (trailingZeros : Peano) : Decimal :=
  if d.val = Peano.zero then
    fromDigit zeroDigit
  else
    ⟨Sequences.List.padAtEnd (Sequences.List.firstElement d Sequences.List.empty)
        zeroDigit trailingZeros,
      Sequences.List.padAtEnd_ne_empty _ _ _ (by simp)⟩

theorem placeAddend_zero_digit (n : Peano) :
    placeAddend zeroDigit n = fromDigit zeroDigit := by
  simp [placeAddend, zeroDigit]

theorem placeAddend_of_val_zero {d : Digit} (n : Peano) (h : d.val = Peano.zero) :
    placeAddend d n = fromDigit zeroDigit := by
  simp [placeAddend, h]

theorem placeAddend_of_val_ne_zero {d : Digit} (n : Peano) (h : d.val ≠ Peano.zero) :
    (placeAddend d n).val =
      Sequences.List.padAtEnd (Sequences.List.firstElement d Sequences.List.empty)
        zeroDigit n := by
  simp [placeAddend, h]

theorem placeAddend_no_trailing (d : Digit) :
    placeAddend d Peano.zero = fromDigit d := by
  unfold placeAddend
  split
  · next hz =>
      apply Subtype.ext
      have hd : d = zeroDigit := Subtype.ext hz
      rw [hd]
  · next _ =>
      apply Subtype.ext
      simp [fromDigit, Sequences.List.padAtEnd]

theorem placeAddend_toPeano (d : Digit) (n : Peano) :
    (placeAddend d n).toPeano = d.val * Peano.tenPower n := by
  unfold placeAddend
  split
  · next hz =>
      rw [fromDigit_toPeano, hz, Peano.zero_multiply]
      rfl
  · next _ =>
      unfold toPeano
      rw [toCardinalNaturalPeano_padAtEnd, toCardinalNaturalPeano_firstElement,
        Sequences.List.length, Peano.tenPower, Peano.multiply_one]
      change (d.val + Peano.zero) * Peano.tenPower n = d.val * Peano.tenPower n
      rw [Peano.add_zero]

theorem placeAddend_isNormalized (d : Digit) (n : Peano) :
    (placeAddend d n).isNormalized = true := by
  unfold placeAddend
  split
  · next _ =>
      exact fromDigit_isNormalized zeroDigit
  · next hnz =>
      unfold isNormalized isNormalizedList
      simp only [Sequences.List.padAtEnd]
      cases n with
      | zero =>
          simp [Sequences.List.padAtEnd]
      | successor n' =>
          simp [Sequences.List.padAtEnd, hnz]

/-- Place-value addends of a digit list, most-significant first.
    For `[3, 4, 7]` this is `[300, 40, 7]`. -/
def placeAddendsOfList : Sequences.List Digit → Sequences.List Decimal
  | .empty => .empty
  | .firstElement d ds =>
      .firstElement (placeAddend d ds.length) (placeAddendsOfList ds)

/-- Place-value addends of a written decimal, one number per digit.
    For `347` this is `[300, 40, 7]`; for `1005` this is `[1000, 0, 0, 5]`. -/
def placeAddends (d : Decimal) : Sequences.List Decimal :=
  placeAddendsOfList d.val

theorem placeAddendsOfList_length (l : Sequences.List Digit) :
    (placeAddendsOfList l).length = l.length := by
  induction l with
  | empty => rfl
  | firstElement _ ds ih =>
    simp only [placeAddendsOfList, Sequences.List.length, ih]

theorem placeAddends_length (d : Decimal) :
    (placeAddends d).length = d.val.length :=
  placeAddendsOfList_length d.val

theorem placeAddendsOfList_ne_empty {l : Sequences.List Digit}
    (h : l ≠ Sequences.List.empty) :
    placeAddendsOfList l ≠ Sequences.List.empty := by
  cases l with
  | empty => exact False.elim (h rfl)
  | firstElement _ _ =>
    intro heq
    cases heq

theorem placeAddends_ne_empty (d : Decimal) :
    placeAddends d ≠ Sequences.List.empty :=
  placeAddendsOfList_ne_empty d.property

/-- Sum of a non-empty list of decimals, left to right. -/
def addAll : (l : Sequences.List Decimal) → l ≠ Sequences.List.empty → Decimal
  | .empty, h => False.elim (h rfl)
  | .firstElement x .empty, _ => x
  | .firstElement x (.firstElement y ys), _ =>
      x + addAll (.firstElement y ys) (by intro heq; cases heq)

theorem addAll_singleton (x : Decimal) :
    addAll (.firstElement x .empty) (by simp) = x :=
  rfl

theorem addAll_firstElement_firstElement (x y : Decimal)
    (ys : Sequences.List Decimal) :
    addAll (.firstElement x (.firstElement y ys)) (by simp) =
      x + addAll (.firstElement y ys) (by intro heq; cases heq) :=
  rfl

def sumToPeano : Sequences.List Decimal → Peano
  | .empty => Peano.zero
  | .firstElement x xs => x.toPeano + sumToPeano xs

theorem addAll_toPeano (l : Sequences.List Decimal) (h : l ≠ Sequences.List.empty) :
    (addAll l h).toPeano = sumToPeano l := by
  match l with
  | .empty => exact False.elim (h rfl)
  | .firstElement x .empty =>
    simp only [addAll, sumToPeano, Peano.add_zero]
  | .firstElement x (.firstElement y ys) =>
    rw [addAll_firstElement_firstElement, add_toPeano, sumToPeano]
    exact congrArg (fun s => x.toPeano + s)
      (addAll_toPeano (.firstElement y ys) (by intro heq; cases heq))

theorem sumToPeano_placeAddendsOfList (l : Sequences.List Digit) :
    sumToPeano (placeAddendsOfList l) = toCardinalNaturalPeano l Peano.zero := by
  induction l with
  | empty =>
    simp only [placeAddendsOfList, sumToPeano, toCardinalNaturalPeano]
  | firstElement d ds ih =>
    simp only [placeAddendsOfList, sumToPeano, placeAddend_toPeano,
      toCardinalNaturalPeano_firstElement, ih]

theorem toPeano_eq_sumToPeano_placeAddends (d : Decimal) :
    d.toPeano = sumToPeano (placeAddends d) := by
  unfold toPeano placeAddends
  exact (sumToPeano_placeAddendsOfList d.val).symm

theorem toPeano_eq_addAll_placeAddends (d : Decimal) :
    d.toPeano = (addAll (placeAddends d) (placeAddends_ne_empty d)).toPeano := by
  rw [addAll_toPeano, toPeano_eq_sumToPeano_placeAddends]

/-- A decimal has the same value as the sum of its place-value addends. -/
theorem equivalent_addAll_placeAddends (d : Decimal) :
    d ≈ addAll (placeAddends d) (placeAddends_ne_empty d) :=
  equivalent_of_toPeano_eq (toPeano_eq_addAll_placeAddends d)

theorem normalize_eq_self_of_isNormalized (d : Decimal) (h : d.isNormalized = true) :
    d.normalize = d :=
  normalize_injective (normalize_isNormalized d) h (normalize_toPeano d)

/-- The written (normalized) form of a number equals the written form of the
    sum of its place-value addends. -/
theorem eq_addAll_placeAddends (d : Decimal) :
    d.normalize = (addAll (placeAddends d) (placeAddends_ne_empty d)).normalize :=
  equivalent_addAll_placeAddends d

/-- A normalized decimal equals the sum of its place-value addends when that
    sum is also a normalized writing. -/
theorem eq_addAll_placeAddends_of_isNormalized (d : Decimal)
    (hd : d.isNormalized = true)
    (hs : (addAll (placeAddends d) (placeAddends_ne_empty d)).isNormalized = true) :
    d = addAll (placeAddends d) (placeAddends_ne_empty d) :=
  normalize_injective hd hs (toPeano_eq_addAll_placeAddends d)

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
  fromDigit (getOnesDigit d h)

/-- The pair of place-value addends of a two-digit number. -/
def twoDigitPlaceAddends (d : Decimal) (h : TwoDigit d) : Decimal × Decimal :=
  (tensPlaceAddend d h, onesPlaceAddend d h)

def tryTwoDigitPlaceAddends (d : Decimal) : Option (Decimal × Decimal) :=
  if h : isTwoDigit d then
    some (twoDigitPlaceAddends d ((isTwoDigit_eq_true_iff d).mp h))
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
  unfold onesPlaceAddend fromDigit
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

theorem toPeano_eq_twoDigitPlaceAddends_add (d : Decimal) (h : TwoDigit d) :
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

theorem tryTwoDigitPlaceAddends_eq_some_of_twoDigit (d : Decimal) (h : TwoDigit d) :
    tryTwoDigitPlaceAddends d = some (twoDigitPlaceAddends d h) := by
  unfold tryTwoDigitPlaceAddends
  have htrue : isTwoDigit d = true := (isTwoDigit_eq_true_iff d).mpr h
  simp only [htrue, ↓reduceDIte]

theorem tryTwoDigitPlaceAddends_eq_none_of_not_twoDigit (d : Decimal) (h : ¬ TwoDigit d) :
    tryTwoDigitPlaceAddends d = none := by
  unfold tryTwoDigitPlaceAddends
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

example :
    (fromTwoDigits fourDigit sevenDigit (by decide)).toPeano =
      (addAll (placeAddends (fromTwoDigits fourDigit sevenDigit (by decide)))
        (placeAddends_ne_empty _)).toPeano :=
  toPeano_eq_addAll_placeAddends _

example :
    (placeAddend threeDigit Peano.two).val =
      Sequences.List.firstElement threeDigit
        (Sequences.List.firstElement zeroDigit
          (Sequences.List.firstElement zeroDigit Sequences.List.empty)) := by
  rw [placeAddend_of_val_ne_zero (d := threeDigit) Peano.two (by decide)]
  simp [Sequences.List.padAtEnd, Peano.two, Peano.one]

example :
    placeAddend zeroDigit Peano.two = fromDigit zeroDigit :=
  placeAddend_zero_digit Peano.two

example :
    (placeAddends
      ⟨Sequences.List.firstElement threeDigit
        (Sequences.List.firstElement fourDigit
          (Sequences.List.firstElement sevenDigit Sequences.List.empty)), by simp⟩).length =
      Peano.three := by
  rw [placeAddends_length]
  rfl

example :
    (placeAddends
      ⟨Sequences.List.firstElement oneDigit
        (Sequences.List.firstElement zeroDigit
          (Sequences.List.firstElement zeroDigit
            (Sequences.List.firstElement fiveDigit Sequences.List.empty))), by simp⟩).length =
      Peano.four := by
  rw [placeAddends_length]
  rfl

end ZeroMath.Numbers.CardinalNatural.Decimal
