import ZeroMath.Numbers.CardinalNatural.Decimal.PlaceValue
import ZeroMath.Terms.Homogeneous.Tree

namespace ZeroMath.Numbers.CardinalNatural.Decimal.Terms.Homogeneous.Trees

open CardinalNatural (Peano)
open Decimal (placeAddends placeAddend fromDigit placeAddends_ne_empty)
open Numbers.Digits (zeroDigit oneDigit threeDigit fourDigit fiveDigit sevenDigit)
open ZeroMath.Terms.Homogeneous.Tree

/-- The place-value addends of `d` as a homogeneous sum term under binary
addition operation `add`. `getArgumentCount add` must be two. A one-digit
number is a value leaf; longer writings nest as `x + (y + ...)`. For `347`
this is the term `300 + (40 + 7)`. -/
def placeAddendsTerm {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Peano} (add : Operation)
    (h : getArgumentCount add = Peano.two) (d : Decimal) :
    ZeroMath.Terms.Homogeneous.Tree Decimal Operation Variable getArgumentCount :=
  binaryOperationFromValues add h (placeAddends d) (placeAddends_ne_empty d)

theorem placeAddendsTerm_eq_binaryOperationFromValues {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Peano} (add : Operation)
    (h : getArgumentCount add = Peano.two) (d : Decimal) :
    placeAddendsTerm (Variable := Variable) add h d =
      binaryOperationFromValues (Variable := Variable) add h
        (placeAddends d) (placeAddends_ne_empty d) :=
  rfl

example :
    let n : Decimal := fromDigit sevenDigit
    let expected :
        ZeroMath.Terms.Homogeneous.Tree Decimal Peano Empty (fun k => k) :=
      value (placeAddend sevenDigit Peano.zero)
    placeAddendsTerm (Variable := Empty) (getArgumentCount := fun k => k)
      Peano.two rfl n =
      expected :=
  rfl

example :
    let n : Decimal :=
      ⟨Sequences.List.firstElement threeDigit
        (Sequences.List.firstElement fourDigit
          (Sequences.List.firstElement sevenDigit Sequences.List.empty)), by simp⟩
    let expected :
        ZeroMath.Terms.Homogeneous.Tree Decimal Peano Empty (fun k => k) :=
      operation Peano.two
        (ArgumentList.twoElements
          (value (placeAddend threeDigit Peano.two))
          (operation Peano.two
            (ArgumentList.twoElements
              (value (placeAddend fourDigit Peano.one))
              (value (placeAddend sevenDigit Peano.zero)))))
    placeAddendsTerm (Variable := Empty) (getArgumentCount := fun k => k)
      Peano.two rfl n =
      expected :=
  rfl

example :
    let n : Decimal :=
      ⟨Sequences.List.firstElement oneDigit
        (Sequences.List.firstElement zeroDigit
          (Sequences.List.firstElement zeroDigit
            (Sequences.List.firstElement fiveDigit Sequences.List.empty))), by simp⟩
    let expected :
        ZeroMath.Terms.Homogeneous.Tree Decimal Peano Empty (fun k => k) :=
      operation Peano.two
        (ArgumentList.twoElements
          (value (placeAddend oneDigit Peano.three))
          (operation Peano.two
            (ArgumentList.twoElements
              (value (placeAddend zeroDigit Peano.two))
              (operation Peano.two
                (ArgumentList.twoElements
                  (value (placeAddend zeroDigit Peano.one))
                  (value (placeAddend fiveDigit Peano.zero)))))))
    placeAddendsTerm (Variable := Empty) (getArgumentCount := fun k => k)
      Peano.two rfl n =
      expected :=
  rfl

end ZeroMath.Numbers.CardinalNatural.Decimal.Terms.Homogeneous.Trees
