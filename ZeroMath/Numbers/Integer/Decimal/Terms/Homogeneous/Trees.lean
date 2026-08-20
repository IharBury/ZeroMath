import ZeroMath.Numbers.CardinalNatural.Decimal.PlaceValue
import ZeroMath.Numbers.Integer.Decimal
import ZeroMath.Terms.Homogeneous.Tree

namespace ZeroMath.Numbers.Integer.Decimal.Terms.Homogeneous.Trees

open Numbers.Digits (zeroDigit oneDigit threeDigit fourDigit fiveDigit sevenDigit)
open ZeroMath.Terms.Homogeneous.Tree

/-- Cardinal place-value addends reinterpreted as non-negative integer decimals,
negated when `negative` is true. -/
def fromCardinalPlaceAddends (negative : Bool) :
    Sequences.List Numbers.CardinalNatural.Decimal → Sequences.List Decimal
  | Sequences.List.empty => Sequences.List.empty
  | Sequences.List.firstElement x xs =>
    Sequences.List.firstElement
      (if negative then -(fromCardinalNatural x) else fromCardinalNatural x)
      (fromCardinalPlaceAddends negative xs)

theorem fromCardinalPlaceAddends_length (negative : Bool) :
    (l : Sequences.List Numbers.CardinalNatural.Decimal) →
      (fromCardinalPlaceAddends negative l).length = l.length
  | Sequences.List.empty => rfl
  | Sequences.List.firstElement _ xs =>
    congrArg (fun n => n + Numbers.CardinalNatural.Peano.one)
      (fromCardinalPlaceAddends_length negative xs)

theorem zero_le_absoluteValue (d : Decimal) : zero ≤ d.absoluteValue := by
  apply le_of_toPeano_le
  rw [toPeano_zero, absoluteValue_toPeano]
  cases d.toPeano with
  | zero =>
    simp only [Integer.Peano.absoluteValue]
    exact Or.inr rfl
  | positive _ =>
    simp only [Integer.Peano.absoluteValue]
    exact Or.inl Integer.Peano.LessThan.zero_less_than_positive
  | negative _ =>
    simp only [Integer.Peano.absoluteValue]
    exact Or.inl Integer.Peano.LessThan.zero_less_than_positive

/-- Place-value addends of an integer decimal, one integer per digit of the
absolute value, with the original sign. For `-347` this is `[-300, -40, -7]`. -/
def placeAddends (d : Decimal) : Sequences.List Decimal :=
  fromCardinalPlaceAddends (isNegative d)
    (Numbers.CardinalNatural.Decimal.placeAddends
      (toCardinalNatural d.absoluteValue (zero_le_absoluteValue d)))

theorem placeAddends_length (d : Decimal) :
    (placeAddends d).length = d.digits.val.length := by
  unfold placeAddends
  rw [fromCardinalPlaceAddends_length,
    Numbers.CardinalNatural.Decimal.placeAddends_length]
  rfl

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

example :
    let n : Decimal :=
      fromCardinalNatural
        ⟨Sequences.List.firstElement threeDigit
          (Sequences.List.firstElement fourDigit
            (Sequences.List.firstElement sevenDigit Sequences.List.empty)), by simp⟩
    let expected :
        ZeroMath.Terms.Homogeneous.Tree Decimal Numbers.CardinalNatural.Peano Empty
          (fun k => k) :=
      operation Numbers.CardinalNatural.Peano.three
        (ArgumentList.firstElement
          (value (fromCardinalNatural
            (Numbers.CardinalNatural.Decimal.placeAddend threeDigit
              Numbers.CardinalNatural.Peano.two)))
          (ArgumentList.firstElement
            (value (fromCardinalNatural
              (Numbers.CardinalNatural.Decimal.placeAddend fourDigit
                Numbers.CardinalNatural.Peano.one)))
            (ArgumentList.firstElement
              (value (fromCardinalNatural
                (Numbers.CardinalNatural.Decimal.placeAddend sevenDigit
                  Numbers.CardinalNatural.Peano.zero)))
              ArgumentList.empty)))
    placeAddendsTerm (Variable := Empty) (getArgumentCount := fun k => k)
      Numbers.CardinalNatural.Peano.three n rfl =
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
      operation Numbers.CardinalNatural.Peano.three
        (ArgumentList.firstElement
          (value (-fromCardinalNatural
            (Numbers.CardinalNatural.Decimal.placeAddend threeDigit
              Numbers.CardinalNatural.Peano.two)))
          (ArgumentList.firstElement
            (value (-fromCardinalNatural
              (Numbers.CardinalNatural.Decimal.placeAddend fourDigit
                Numbers.CardinalNatural.Peano.one)))
            (ArgumentList.firstElement
              (value (-fromCardinalNatural
                (Numbers.CardinalNatural.Decimal.placeAddend sevenDigit
                  Numbers.CardinalNatural.Peano.zero)))
              ArgumentList.empty)))
    placeAddendsTerm (Variable := Empty) (getArgumentCount := fun k => k)
      Numbers.CardinalNatural.Peano.three n rfl =
      expected :=
  rfl

end ZeroMath.Numbers.Integer.Decimal.Terms.Homogeneous.Trees
