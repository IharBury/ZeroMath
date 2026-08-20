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

theorem placeAddends_ne_empty (d : Decimal) :
    placeAddends d ≠ Sequences.List.empty :=
  fun h =>
    Sequences.List.length_ne_zero_of_ne_empty d.digits.property
      ((placeAddends_length d).symm.trans (h ▸ rfl))

/-- The place-value addends of `d` as a homogeneous sum term under binary
addition operation `add`. `getArgumentCount add` must be two. A one-digit
number is a value leaf; longer writings nest as `x + (y + ...)`. -/
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
          (value (fromCardinalNatural
            (Numbers.CardinalNatural.Decimal.placeAddend threeDigit
              Numbers.CardinalNatural.Peano.two)))
          (operation Numbers.CardinalNatural.Peano.two
            (ArgumentList.twoElements
              (value (fromCardinalNatural
                (Numbers.CardinalNatural.Decimal.placeAddend fourDigit
                  Numbers.CardinalNatural.Peano.one)))
              (value (fromCardinalNatural
                (Numbers.CardinalNatural.Decimal.placeAddend sevenDigit
                  Numbers.CardinalNatural.Peano.zero))))))
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
          (value (-fromCardinalNatural
            (Numbers.CardinalNatural.Decimal.placeAddend threeDigit
              Numbers.CardinalNatural.Peano.two)))
          (operation Numbers.CardinalNatural.Peano.two
            (ArgumentList.twoElements
              (value (-fromCardinalNatural
                (Numbers.CardinalNatural.Decimal.placeAddend fourDigit
                  Numbers.CardinalNatural.Peano.one)))
              (value (-fromCardinalNatural
                (Numbers.CardinalNatural.Decimal.placeAddend sevenDigit
                  Numbers.CardinalNatural.Peano.zero))))))
    placeAddendsTerm (Variable := Empty) (getArgumentCount := fun k => k)
      Numbers.CardinalNatural.Peano.two rfl n =
      expected :=
  rfl

end ZeroMath.Numbers.Integer.Decimal.Terms.Homogeneous.Trees
