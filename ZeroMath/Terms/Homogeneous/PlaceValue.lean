import ZeroMath.Numbers.CardinalNatural.Decimal.PlaceValue
import ZeroMath.Terms.Homogeneous.Tree

namespace ZeroMath.Terms.Homogeneous

/-- n-ary addition. The arity is part of the operation so sums of different
lengths inhabit one homogeneous `Tree` type. -/
structure Addition where
  argumentCount : Numbers.CardinalNatural.Peano

deriving instance DecidableEq for Addition

open Numbers.CardinalNatural (Decimal Peano)
open Numbers.Digits (zeroDigit oneDigit threeDigit fourDigit fiveDigit sevenDigit)
open Tree

abbrev PlaceAddendsTree := Tree Decimal Addition Empty Addition.argumentCount

/-- The place-value addends of `d` as a homogeneous sum term: n-ary `Addition` of
those addends as value leaves. For `347` this is the term `300 + 40 + 7`. -/
def placeAddendsTerm (d : Decimal) : PlaceAddendsTree :=
  operationFromValues { argumentCount := (Decimal.placeAddends d).length }
    (Decimal.placeAddends d) rfl

theorem placeAddendsTerm_eq_operationFromValues (d : Decimal) :
    placeAddendsTerm d =
      operationFromValues { argumentCount := (Decimal.placeAddends d).length }
        (Decimal.placeAddends d) rfl :=
  rfl

theorem placeAddendsTerm_valueList (d : Decimal) :
    ∃ args,
      placeAddendsTerm d = operation { argumentCount := (Decimal.placeAddends d).length } args ∧
        ArgumentList.toList args =
          valueList (Operation := Addition) (Variable := Empty)
            (getArgumentCount := Addition.argumentCount) (Decimal.placeAddends d) :=
  ⟨ArgumentList.fromList (Operation := Addition) (Variable := Empty)
      (getArgumentCount := Addition.argumentCount) (Decimal.placeAddends d).length
      (valueList (Operation := Addition) (Variable := Empty)
        (getArgumentCount := Addition.argumentCount) (Decimal.placeAddends d))
      (Eq.trans
        (valueList_length (Operation := Addition) (Variable := Empty)
          (getArgumentCount := Addition.argumentCount) (Decimal.placeAddends d))
        rfl),
    rfl,
    operationFromValues_toList (Variable := Empty)
      ({ argumentCount := (Decimal.placeAddends d).length } : Addition)
      (Decimal.placeAddends d) rfl⟩

example :
    let n : Decimal :=
      ⟨Sequences.List.firstElement threeDigit
        (Sequences.List.firstElement fourDigit
          (Sequences.List.firstElement sevenDigit Sequences.List.empty)), by simp⟩
    let expected : PlaceAddendsTree :=
      operation ⟨Peano.three⟩
        (ArgumentList.firstElement (value (Decimal.placeAddend threeDigit Peano.two))
          (ArgumentList.firstElement (value (Decimal.placeAddend fourDigit Peano.one))
            (ArgumentList.firstElement (value (Decimal.placeAddend sevenDigit Peano.zero))
              ArgumentList.empty)))
    placeAddendsTerm n = expected :=
  rfl

example :
    let n : Decimal := Decimal.fromDigit sevenDigit
    let expected : PlaceAddendsTree :=
      operation ⟨Peano.one⟩
        (ArgumentList.firstElement (value (Decimal.placeAddend sevenDigit Peano.zero))
          ArgumentList.empty)
    placeAddendsTerm n = expected :=
  rfl

example :
    let n : Decimal :=
      ⟨Sequences.List.firstElement oneDigit
        (Sequences.List.firstElement zeroDigit
          (Sequences.List.firstElement zeroDigit
            (Sequences.List.firstElement fiveDigit Sequences.List.empty))), by simp⟩
    let expected : PlaceAddendsTree :=
      operation ⟨Peano.four⟩
        (ArgumentList.firstElement (value (Decimal.placeAddend oneDigit Peano.three))
          (ArgumentList.firstElement (value (Decimal.placeAddend zeroDigit Peano.two))
            (ArgumentList.firstElement (value (Decimal.placeAddend zeroDigit Peano.one))
              (ArgumentList.firstElement (value (Decimal.placeAddend fiveDigit Peano.zero))
                ArgumentList.empty))))
    placeAddendsTerm n = expected :=
  rfl

end ZeroMath.Terms.Homogeneous
