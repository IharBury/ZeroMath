import ZeroMath.Numbers.CardinalNatural.Decimal.PlaceValue
import ZeroMath.Sequences.List

namespace ZeroMath.Numbers.CardinalNatural.Decimal

/-- The Peano value of the sum of `n` copies of `a` equals `a.toPeano * n`. -/
theorem sumToPeano_repeatElement (n : Peano) (a : Decimal) :
    sumToPeano (Sequences.List.repeatElement n a) = a.toPeano * n := by
  induction n with
  | zero =>
    rw [Sequences.List.repeatElement_zero, sumToPeano, Peano.multiply_zero]
  | successor n ih =>
    rw [Sequences.List.repeatElement_successor, sumToPeano, ih,
      Peano.multiply_successor, Peano.add_commutative]

/-- A list of identical decimal addends `a` has Peano sum `a.toPeano` times
    the number of addends. -/
theorem sumToPeano_eq_multiply_of_AllElements {l : Sequences.List Decimal}
    {a : Decimal} (h : Sequences.List.AllElements (fun x => x = a) l) :
    sumToPeano l = a.toPeano * l.length := by
  have hsum := congrArg sumToPeano (Sequences.List.eq_repeatElement_of_AllElements h)
  rw [sumToPeano_repeatElement] at hsum
  exact hsum

/-- The written sum of `n` copies of `a` has the same Peano value as `a * n`. -/
theorem addAll_repeatElement_toPeano (n : Peano) (a : Decimal)
    (hn : n ≠ Peano.zero) :
    (addAll (Sequences.List.repeatElement n a)
      (Sequences.List.repeatElement_ne_empty n a hn)).toPeano =
      a.toPeano * n := by
  rw [addAll_toPeano, sumToPeano_repeatElement]

/-- The written sum of `n` copies of `a` is equivalent to the product
    `a * fromPeano n`. -/
theorem equivalent_addAll_repeatElement (n : Peano) (a : Decimal)
    (hn : n ≠ Peano.zero) :
    addAll (Sequences.List.repeatElement n a)
      (Sequences.List.repeatElement_ne_empty n a hn) ≈
      a * fromPeano n := by
  apply equivalent_of_toPeano_eq
  rw [addAll_repeatElement_toPeano n a hn, multiply_toPeano, toPeano_fromPeano]

/-- The written sum of `n` copies of `a` is equivalent to the product
    `fromPeano n * a`. -/
theorem equivalent_addAll_repeatElement_count_left (n : Peano) (a : Decimal)
    (hn : n ≠ Peano.zero) :
    addAll (Sequences.List.repeatElement n a)
      (Sequences.List.repeatElement_ne_empty n a hn) ≈
      fromPeano n * a :=
  Setoid.trans (equivalent_addAll_repeatElement n a hn)
    (equivalent_multiply_commutative a (fromPeano n))

/-- The normalized writing of the sum of `n` copies of `a` equals the
    normalized writing of `a * fromPeano n`. -/
theorem eq_addAll_repeatElement (n : Peano) (a : Decimal) (hn : n ≠ Peano.zero) :
    (addAll (Sequences.List.repeatElement n a)
      (Sequences.List.repeatElement_ne_empty n a hn)).normalize =
      (a * fromPeano n).normalize :=
  equivalent_addAll_repeatElement n a hn

/-- A non-empty list of identical decimal addends `a` sums to a number
    equivalent to `a` times the number of addends. -/
theorem equivalent_addAll_eq_multiply_of_AllElements {l : Sequences.List Decimal}
    {a : Decimal} (hAll : Sequences.List.AllElements (fun x => x = a) l)
    (hne : l ≠ Sequences.List.empty) :
    addAll l hne ≈ a * fromPeano l.length := by
  apply equivalent_of_toPeano_eq
  rw [addAll_toPeano, sumToPeano_eq_multiply_of_AllElements hAll,
    multiply_toPeano, toPeano_fromPeano]

example :
    let two : Decimal := fromPeano Peano.two
    (addAll (Sequences.List.repeatElement Peano.four two)
      (Sequences.List.repeatElement_ne_empty Peano.four two
        (Peano.successor_ne_zero _))).toPeano =
      two.toPeano * Peano.four :=
  addAll_repeatElement_toPeano Peano.four (fromPeano Peano.two)
    (Peano.successor_ne_zero _)

example :
    let two : Decimal := fromPeano Peano.two
    addAll (Sequences.List.repeatElement Peano.four two)
      (Sequences.List.repeatElement_ne_empty Peano.four two
        (Peano.successor_ne_zero _)) ≈
      two * fromPeano Peano.four :=
  equivalent_addAll_repeatElement Peano.four (fromPeano Peano.two)
    (Peano.successor_ne_zero _)

end ZeroMath.Numbers.CardinalNatural.Decimal
