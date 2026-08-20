import ZeroMath.Numbers.CardinalNatural.Decimal.PlaceValue
import ZeroMath.Terms.Homogeneous.Tree

namespace ZeroMath.Numbers.CardinalNatural.Decimal.Terms.HomogeneousTerms

open CardinalNatural (Peano)
open Decimal (placeAddends placeAddend fromDigit)
open Numbers.Digits (zeroDigit oneDigit threeDigit fourDigit fiveDigit sevenDigit)
open ZeroMath.Terms.Homogeneous.Tree

/-- The place-value addends of `d` as a homogeneous sum term under addition
operation `add`. `getArgumentCount add` must equal the number of addends. For
`347` and a three-argument `add` this is the term `300 + 40 + 7`. -/
def placeAddendsTerm {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Peano} (add : Operation)
    (d : Decimal)
    (h : (placeAddends d).length = getArgumentCount add) :
    ZeroMath.Terms.Homogeneous.Tree Decimal Operation Variable getArgumentCount :=
  operationFromValues add (placeAddends d) h

theorem placeAddendsTerm_eq_operationFromValues {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Peano} (add : Operation)
    (d : Decimal)
    (h : (placeAddends d).length = getArgumentCount add) :
    placeAddendsTerm (Variable := Variable) add d h =
      operationFromValues (Variable := Variable) add (placeAddends d) h :=
  rfl

theorem placeAddendsTerm_valueList {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Peano} (add : Operation)
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

example :
    let n : Decimal :=
      ⟨Sequences.List.firstElement threeDigit
        (Sequences.List.firstElement fourDigit
          (Sequences.List.firstElement sevenDigit Sequences.List.empty)), by simp⟩
    let expected :
        ZeroMath.Terms.Homogeneous.Tree Decimal Peano Empty (fun k => k) :=
      operation Peano.three
        (ArgumentList.firstElement (value (placeAddend threeDigit Peano.two))
          (ArgumentList.firstElement (value (placeAddend fourDigit Peano.one))
            (ArgumentList.firstElement (value (placeAddend sevenDigit Peano.zero))
              ArgumentList.empty)))
    placeAddendsTerm (Variable := Empty) (getArgumentCount := fun k => k)
      Peano.three n rfl =
      expected :=
  rfl

example :
    let n : Decimal := fromDigit sevenDigit
    let expected :
        ZeroMath.Terms.Homogeneous.Tree Decimal Peano Empty (fun k => k) :=
      operation Peano.one
        (ArgumentList.firstElement (value (placeAddend sevenDigit Peano.zero))
          ArgumentList.empty)
    placeAddendsTerm (Variable := Empty) (getArgumentCount := fun k => k)
      Peano.one n rfl =
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
      operation Peano.four
        (ArgumentList.firstElement (value (placeAddend oneDigit Peano.three))
          (ArgumentList.firstElement (value (placeAddend zeroDigit Peano.two))
            (ArgumentList.firstElement (value (placeAddend zeroDigit Peano.one))
              (ArgumentList.firstElement (value (placeAddend fiveDigit Peano.zero))
                ArgumentList.empty))))
    placeAddendsTerm (Variable := Empty) (getArgumentCount := fun k => k)
      Peano.four n rfl =
      expected :=
  rfl

end ZeroMath.Numbers.CardinalNatural.Decimal.Terms.HomogeneousTerms
