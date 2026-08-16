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
    let n : Decimal :=
      ⟨Sequences.List.firstElement fourDigit
        (Sequences.List.firstElement sevenDigit Sequences.List.empty), by simp⟩
    n.toPeano =
      (addAll (placeAddends n) (placeAddends_ne_empty n)).toPeano :=
  toPeano_eq_addAll_placeAddends _

example :
    (placeAddends
      ⟨Sequences.List.firstElement fourDigit
        (Sequences.List.firstElement sevenDigit Sequences.List.empty), by simp⟩).length =
      Peano.two := by
  rw [placeAddends_length]
  rfl

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
