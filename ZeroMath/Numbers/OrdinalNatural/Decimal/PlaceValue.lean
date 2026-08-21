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

end ZeroMath.Numbers.OrdinalNatural.Decimal
