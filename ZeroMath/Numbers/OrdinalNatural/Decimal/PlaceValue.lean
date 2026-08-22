import ZeroMath.Numbers.CardinalNatural.Decimal
import ZeroMath.Numbers.OrdinalNatural.Decimal

namespace ZeroMath.Numbers.OrdinalNatural.Decimal

/-- Cardinal place-value addends that are nonzero, reinterpreted as ordinal
decimals. Zero addends are omitted because ordinals have no zero. -/
def fromCardinalPlaceAddends :
    Sequences.List Numbers.CardinalNatural.Decimal → Sequences.List Decimal
  | Sequences.List.empty => Sequences.List.empty
  | Sequences.List.firstElement x xs =>
    if h : x.toPeano = Numbers.CardinalNatural.Peano.zero then
      fromCardinalPlaceAddends xs
    else
      Sequences.List.firstElement
        (Numbers.CardinalNatural.Decimal.toOrdinal x
          (Numbers.CardinalNatural.Decimal.not_equivalent_zero_of_toPeano_ne_zero x h))
        (fromCardinalPlaceAddends xs)

/-- Place-value addends of an ordinal decimal. Zero place addends are omitted.
For `347` this is `[300, 40, 7]`; for `1005` this is `[1000, 5]`. -/
def placeAddends (d : Decimal) : Sequences.List Decimal :=
  fromCardinalPlaceAddends
    (Numbers.CardinalNatural.Decimal.placeAddends
      (Numbers.CardinalNatural.Decimal.fromOrdinal d))

theorem fromCardinalPlaceAddends_eq_empty_sumToPeano :
    (l : Sequences.List Numbers.CardinalNatural.Decimal) →
    fromCardinalPlaceAddends l = Sequences.List.empty →
      Numbers.CardinalNatural.Decimal.sumToPeano l =
        Numbers.CardinalNatural.Peano.zero
  | Sequences.List.empty, _ => rfl
  | Sequences.List.firstElement x xs, h => by
      unfold fromCardinalPlaceAddends at h
      split at h
      · next hx =>
        have hxs := fromCardinalPlaceAddends_eq_empty_sumToPeano xs h
        unfold Numbers.CardinalNatural.Decimal.sumToPeano
        rw [hx, Numbers.CardinalNatural.Peano.zero_add, hxs]
      · nomatch h

theorem placeAddends_ne_empty (d : Decimal) :
    placeAddends d ≠ Sequences.List.empty := by
  intro h
  have hsum :
      Numbers.CardinalNatural.Decimal.sumToPeano
        (Numbers.CardinalNatural.Decimal.placeAddends
          (Numbers.CardinalNatural.Decimal.fromOrdinal d)) =
        Numbers.CardinalNatural.Peano.zero :=
    fromCardinalPlaceAddends_eq_empty_sumToPeano _ h
  have hpeano :
      (Numbers.CardinalNatural.Decimal.fromOrdinal d).toPeano =
        Numbers.CardinalNatural.Peano.zero :=
    (Numbers.CardinalNatural.Decimal.toPeano_eq_sumToPeano_placeAddends _).trans hsum
  exact Numbers.CardinalNatural.Decimal.fromOrdinal_not_equivalent_zero d
    (Numbers.CardinalNatural.Decimal.equivalent_of_toPeano_eq
      (hpeano.trans Numbers.CardinalNatural.Decimal.toPeano_zero.symm))

theorem toCardinalPeano_toOrdinal (a : Numbers.CardinalNatural.Decimal)
    (h : ¬ a ≈ Numbers.CardinalNatural.Decimal.zero) :
    (Numbers.CardinalNatural.Decimal.toOrdinal a h).toCardinalPeano =
      a.toPeano :=
  rfl

/-- Cardinal Peano sum of a list of ordinal decimals. -/
def sumToCardinalPeano : Sequences.List Decimal → Numbers.CardinalNatural.Peano
  | Sequences.List.empty => Numbers.CardinalNatural.Peano.zero
  | Sequences.List.firstElement x xs => x.toCardinalPeano + sumToCardinalPeano xs

theorem fromCardinalPlaceAddends_sumToCardinalPeano :
    (l : Sequences.List Numbers.CardinalNatural.Decimal) →
    sumToCardinalPeano (fromCardinalPlaceAddends l) =
      Numbers.CardinalNatural.Decimal.sumToPeano l
  | Sequences.List.empty => rfl
  | Sequences.List.firstElement x xs => by
      unfold fromCardinalPlaceAddends
      split
      · next hz =>
          rw [Numbers.CardinalNatural.Decimal.sumToPeano, hz,
            Numbers.CardinalNatural.Peano.zero_add]
          exact fromCardinalPlaceAddends_sumToCardinalPeano xs
      · next _hnz =>
          simp only [sumToCardinalPeano, toCardinalPeano_toOrdinal,
            Numbers.CardinalNatural.Decimal.sumToPeano,
            fromCardinalPlaceAddends_sumToCardinalPeano xs]

theorem toCardinalPeano_eq_sumToCardinalPeano_placeAddends (d : Decimal) :
    toCardinalPeano d = sumToCardinalPeano (placeAddends d) := by
  unfold placeAddends
  rw [fromCardinalPlaceAddends_sumToCardinalPeano]
  exact
    (Numbers.CardinalNatural.Decimal.fromOrdinal_toPeano d).symm.trans
      (Numbers.CardinalNatural.Decimal.toPeano_eq_sumToPeano_placeAddends
        (Numbers.CardinalNatural.Decimal.fromOrdinal d))

/-- Sum of a non-empty list of ordinal decimals, left to right. -/
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

theorem addAll_toCardinalPeano (l : Sequences.List Decimal)
    (h : l ≠ Sequences.List.empty) :
    toCardinalPeano (addAll l h) = sumToCardinalPeano l := by
  match l with
  | .empty => exact False.elim (h rfl)
  | .firstElement x .empty =>
    simp only [addAll, sumToCardinalPeano, Numbers.CardinalNatural.Peano.add_zero]
  | .firstElement x (.firstElement y ys) =>
    rw [addAll_firstElement_firstElement, toCardinalPeano_add, sumToCardinalPeano]
    exact congrArg (fun s => toCardinalPeano x + s)
      (addAll_toCardinalPeano (.firstElement y ys) (by intro heq; cases heq))

theorem toCardinalPeano_eq_addAll_placeAddends (d : Decimal) :
    toCardinalPeano d =
      toCardinalPeano (addAll (placeAddends d) (placeAddends_ne_empty d)) := by
  rw [addAll_toCardinalPeano, toCardinalPeano_eq_sumToCardinalPeano_placeAddends]

theorem toPeano_eq_addAll_placeAddends (d : Decimal) :
    d.toPeano = (addAll (placeAddends d) (placeAddends_ne_empty d)).toPeano := by
  apply Numbers.CardinalNatural.Peano.eq_of_fromOrdinal_eq
  simp only [toPeano, Numbers.CardinalNatural.Peano.fromOrdinal_toOrdinal]
  exact toCardinalPeano_eq_addAll_placeAddends d

/-- An ordinal decimal has the same value as the sum of its place-value
addends. -/
theorem equivalent_addAll_placeAddends (d : Decimal) :
    d ≈ addAll (placeAddends d) (placeAddends_ne_empty d) :=
  equivalent_of_toPeano_eq (toPeano_eq_addAll_placeAddends d)

/-- The written (normalized) form of an ordinal equals the written form of the
sum of its place-value addends. -/
theorem eq_addAll_placeAddends (d : Decimal) :
    d.normalize = (addAll (placeAddends d) (placeAddends_ne_empty d)).normalize :=
  equivalent_addAll_placeAddends d

/-- A normalized ordinal decimal equals the sum of its place-value addends when
that sum is also a normalized writing. -/
theorem eq_addAll_placeAddends_of_isNormalized (d : Decimal)
    (hd : d.isNormalized = true)
    (hs : (addAll (placeAddends d) (placeAddends_ne_empty d)).isNormalized = true) :
    d = addAll (placeAddends d) (placeAddends_ne_empty d) :=
  normalize_injective hd hs (toCardinalPeano_eq_addAll_placeAddends d)

end ZeroMath.Numbers.OrdinalNatural.Decimal
