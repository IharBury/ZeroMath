import ZeroMath.Numbers.CardinalNatural.Decimal.PlaceValue
import ZeroMath.Numbers.OrdinalNatural.Decimal
import ZeroMath.Terms.Homogeneous.Tree

namespace ZeroMath.Numbers.OrdinalNatural.Decimal.Terms.Homogeneous.Trees

open ZeroMath.Terms.Homogeneous.Tree

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

/-- The place-value addends of `d` as a homogeneous sum term under addition
operation `add`. `getArgumentCount add` must equal the number of addends. -/
def placeAddendsTerm {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano} (add : Operation)
    (d : Decimal)
    (h : (placeAddends d).length = getArgumentCount add) :
    ZeroMath.Terms.Homogeneous.Tree Decimal Operation Variable getArgumentCount :=
  operationFromValues add (placeAddends d) h

theorem placeAddendsTerm_eq_operationFromValues {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano} (add : Operation)
    (d : Decimal)
    (h : (placeAddends d).length = getArgumentCount add) :
    placeAddendsTerm (Variable := Variable) add d h =
      operationFromValues (Variable := Variable) add (placeAddends d) h :=
  rfl

theorem placeAddendsTerm_valueList {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano} (add : Operation)
    (d : Decimal)
    (h : (placeAddends d).length = getArgumentCount add) :
    ∃ args,
      placeAddendsTerm (Variable := Variable) add d h = operation add args ∧
        ArgumentList.toList args =
          valueList (Variable := Variable) (getArgumentCount := getArgumentCount)
            (placeAddends d) :=
  ⟨ArgumentList.fromList (Variable := Variable) (getArgumentCount add)
      (valueList (Variable := Variable) (getArgumentCount := getArgumentCount)
        (placeAddends d))
      (Eq.trans
        (valueList_length (Variable := Variable) (getArgumentCount := getArgumentCount)
          (placeAddends d))
        h),
    rfl,
    operationFromValues_toList (Variable := Variable) add (placeAddends d) h⟩

end ZeroMath.Numbers.OrdinalNatural.Decimal.Terms.Homogeneous.Trees
