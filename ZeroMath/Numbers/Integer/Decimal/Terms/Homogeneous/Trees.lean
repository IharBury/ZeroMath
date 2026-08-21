import ZeroMath.Numbers.CardinalNatural.Decimal
import ZeroMath.Numbers.Integer.Decimal
import ZeroMath.Terms.Homogeneous.Tree

namespace ZeroMath.Numbers.Integer.Decimal.Terms.Homogeneous.Trees

open Numbers.Digits (threeDigit fourDigit sevenDigit)
open ZeroMath.Terms.Homogeneous.Tree

/-- The place-value addends of `d` as a homogeneous sum term under binary
addition operation `add`. `getArgumentCount add` must be two. A one-digit
number is a value leaf; longer writings nest as `(... + y) + z`. Zero addends
are omitted unless `d` is zero. -/
def placeAddendsTerm {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano} (add : Operation)
    (h : getArgumentCount add = Numbers.CardinalNatural.Peano.two) (d : Decimal) :
    ZeroMath.Terms.Homogeneous.Tree Decimal Operation Variable getArgumentCount :=
  binaryOperationFromValues add h (placeAddends d) (placeAddends_ne_empty d)

theorem placeAddendsTerm_eq_binaryOperationFromValues {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano} (add : Operation)
    (h : getArgumentCount add = Numbers.CardinalNatural.Peano.two) (d : Decimal) :
    placeAddendsTerm (Variable := Variable) add h d =
      binaryOperationFromValues (Variable := Variable) add h
        (placeAddends d) (placeAddends_ne_empty d) :=
  rfl

example :
    let n : Decimal :=
      fromCardinalNatural
        ⟨Sequences.List.firstElement threeDigit
          (Sequences.List.firstElement fourDigit
            (Sequences.List.firstElement sevenDigit Sequences.List.empty)), by simp⟩
    let expected :
        ZeroMath.Terms.Homogeneous.Tree Decimal Numbers.CardinalNatural.Peano Empty
          (fun k => k) :=
      operation Numbers.CardinalNatural.Peano.two
        (ArgumentList.twoElements
          (operation Numbers.CardinalNatural.Peano.two
            (ArgumentList.twoElements
              (value (fromCardinalNatural
                (Numbers.CardinalNatural.Decimal.placeAddend threeDigit
                  Numbers.CardinalNatural.Peano.two)))
              (value (fromCardinalNatural
                (Numbers.CardinalNatural.Decimal.placeAddend fourDigit
                  Numbers.CardinalNatural.Peano.one)))))
          (value (fromCardinalNatural
            (Numbers.CardinalNatural.Decimal.placeAddend sevenDigit
              Numbers.CardinalNatural.Peano.zero))))
    placeAddendsTerm (Variable := Empty) (getArgumentCount := fun k => k)
      Numbers.CardinalNatural.Peano.two rfl n =
      expected :=
  rfl

example :
    let n : Decimal :=
      ⟨some Sign.minus,
        ⟨Sequences.List.firstElement threeDigit
          (Sequences.List.firstElement fourDigit
            (Sequences.List.firstElement sevenDigit Sequences.List.empty)), by simp⟩⟩
    let expected :
        ZeroMath.Terms.Homogeneous.Tree Decimal Numbers.CardinalNatural.Peano Empty
          (fun k => k) :=
      operation Numbers.CardinalNatural.Peano.two
        (ArgumentList.twoElements
          (operation Numbers.CardinalNatural.Peano.two
            (ArgumentList.twoElements
              (value (-fromCardinalNatural
                (Numbers.CardinalNatural.Decimal.placeAddend threeDigit
                  Numbers.CardinalNatural.Peano.two)))
              (value (-fromCardinalNatural
                (Numbers.CardinalNatural.Decimal.placeAddend fourDigit
                  Numbers.CardinalNatural.Peano.one)))))
          (value (-fromCardinalNatural
            (Numbers.CardinalNatural.Decimal.placeAddend sevenDigit
              Numbers.CardinalNatural.Peano.zero))))
    placeAddendsTerm (Variable := Empty) (getArgumentCount := fun k => k)
      Numbers.CardinalNatural.Peano.two rfl n =
      expected :=
  rfl

end ZeroMath.Numbers.Integer.Decimal.Terms.Homogeneous.Trees
