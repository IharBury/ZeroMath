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

/-- Left-associated addition of integer decimals, matching
`binaryOperationFromValues.go`. -/
theorem toPeano_goValue_add (acc : Decimal) (xs : Sequences.List Decimal) :
    (binaryOperationFromValues.goValue (fun a b => a + b) acc xs).toPeano =
      acc.toPeano + sumToPeano xs := by
  induction xs generalizing acc with
  | empty =>
      rw [binaryOperationFromValues.goValue_empty, sumToPeano, Integer.Peano.add_zero]
  | firstElement x xs ih =>
      rw [binaryOperationFromValues.goValue_firstElement, ih, add_toPeano,
        sumToPeano, Integer.Peano.add_associative]

/-- Computing a left-associated addition tree recovers the Peano sum of the
value list. -/
theorem toPeano_compute_binaryOperationFromValues_add {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (add : Operation)
    (h : getArgumentCount add = Numbers.CardinalNatural.Peano.two)
    (getVariableValue : Variable → Decimal)
    (computeOperation : (op : Operation) → (operands : Sequences.List Decimal) →
      operands.length = getArgumentCount op → Decimal)
    (hAdd : ∀ (x y : Decimal)
        (hlen : (Sequences.List.firstElement x
          (Sequences.List.firstElement y Sequences.List.empty)).length =
            getArgumentCount add),
      computeOperation add
        (Sequences.List.firstElement x
          (Sequences.List.firstElement y Sequences.List.empty)) hlen =
        x + y)
    (values : Sequences.List Decimal)
    (hne : values ≠ Sequences.List.empty) :
    (compute getVariableValue computeOperation
        (binaryOperationFromValues (Variable := Variable) add h values hne)).toPeano =
      sumToPeano values := by
  cases values with
  | empty => exact False.elim (hne rfl)
  | firstElement x xs =>
      rw [compute_binaryOperationFromValues_firstElement
        getVariableValue computeOperation add h (fun a b => a + b) hAdd]
      rw [sumToPeano, toPeano_goValue_add]

/-- Computing the place-value sum term under binary addition recovers the
Peano value of `d`. -/
theorem toPeano_eq_compute_placeAddendsTerm {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (add : Operation)
    (h : getArgumentCount add = Numbers.CardinalNatural.Peano.two)
    (getVariableValue : Variable → Decimal)
    (computeOperation : (op : Operation) → (operands : Sequences.List Decimal) →
      operands.length = getArgumentCount op → Decimal)
    (hAdd : ∀ (x y : Decimal)
        (hlen : (Sequences.List.firstElement x
          (Sequences.List.firstElement y Sequences.List.empty)).length =
            getArgumentCount add),
      computeOperation add
        (Sequences.List.firstElement x
          (Sequences.List.firstElement y Sequences.List.empty)) hlen =
        x + y)
    (d : Decimal) :
    d.toPeano =
      (compute getVariableValue computeOperation
        (placeAddendsTerm (Variable := Variable) add h d)).toPeano := by
  rw [placeAddendsTerm_eq_binaryOperationFromValues,
    toPeano_compute_binaryOperationFromValues_add add h getVariableValue
      computeOperation hAdd]
  exact toPeano_eq_sumToPeano_placeAddends d

/-- Computing the place-value sum term under binary addition yields a decimal
equivalent to the original number. -/
theorem equivalent_compute_placeAddendsTerm {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (add : Operation)
    (h : getArgumentCount add = Numbers.CardinalNatural.Peano.two)
    (getVariableValue : Variable → Decimal)
    (computeOperation : (op : Operation) → (operands : Sequences.List Decimal) →
      operands.length = getArgumentCount op → Decimal)
    (hAdd : ∀ (x y : Decimal)
        (hlen : (Sequences.List.firstElement x
          (Sequences.List.firstElement y Sequences.List.empty)).length =
            getArgumentCount add),
      computeOperation add
        (Sequences.List.firstElement x
          (Sequences.List.firstElement y Sequences.List.empty)) hlen =
        x + y)
    (d : Decimal) :
    d ≈ compute getVariableValue computeOperation
      (placeAddendsTerm (Variable := Variable) add h d) :=
  equivalent_of_toPeano_eq (toPeano_eq_compute_placeAddendsTerm
    add h getVariableValue computeOperation hAdd d)

example :
    let n : Decimal :=
      ⟨some Sign.minus,
        ⟨Sequences.List.firstElement threeDigit
          (Sequences.List.firstElement fourDigit
            (Sequences.List.firstElement sevenDigit Sequences.List.empty)), by simp⟩⟩
    n ≈ compute (fun v : Empty => nomatch v)
      (fun _ operands _ =>
        match operands with
        | Sequences.List.firstElement x
            (Sequences.List.firstElement y _) =>
          x + y
        | Sequences.List.firstElement x Sequences.List.empty => x
        | Sequences.List.empty => zero)
      (placeAddendsTerm (Variable := Empty) (getArgumentCount := fun k => k)
        Numbers.CardinalNatural.Peano.two rfl n) :=
  equivalent_compute_placeAddendsTerm (Variable := Empty)
    (getArgumentCount := fun k => k) Numbers.CardinalNatural.Peano.two rfl
    (fun v => nomatch v)
    (fun _ operands _ =>
      match operands with
      | Sequences.List.firstElement x
          (Sequences.List.firstElement y _) =>
        x + y
      | Sequences.List.firstElement x Sequences.List.empty => x
      | Sequences.List.empty => zero)
    (fun _ _ _ => rfl) _

/-- The sum of `count` copies of `addend` as a homogeneous term under binary
addition. `count` must be nonzero. A single addend is a value leaf; longer
lists nest left-associated. -/
def repeatedAddendsTerm {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (add : Operation)
    (h : getArgumentCount add = Numbers.CardinalNatural.Peano.two)
    (addend : Decimal) (count : Numbers.CardinalNatural.Peano)
    (hne : count ≠ Numbers.CardinalNatural.Peano.zero) :
    ZeroMath.Terms.Homogeneous.Tree Decimal Operation Variable getArgumentCount :=
  binaryOperationFromValues add h (repeatedAddends addend count)
    (repeatedAddends_ne_empty addend count hne)

theorem repeatedAddendsTerm_eq_binaryOperationFromValues {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (add : Operation)
    (h : getArgumentCount add = Numbers.CardinalNatural.Peano.two)
    (addend : Decimal) (count : Numbers.CardinalNatural.Peano)
    (hne : count ≠ Numbers.CardinalNatural.Peano.zero) :
    repeatedAddendsTerm (Variable := Variable) add h addend count hne =
      binaryOperationFromValues (Variable := Variable) add h
        (repeatedAddends addend count)
        (repeatedAddends_ne_empty addend count hne) :=
  rfl

/-- The product `addend * fromCardinalNaturalPeano count` as a homogeneous
binary term. -/
def productTerm {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (mul : Operation)
    (h : getArgumentCount mul = Numbers.CardinalNatural.Peano.two)
    (addend : Decimal) (count : Numbers.CardinalNatural.Peano) :
    ZeroMath.Terms.Homogeneous.Tree Decimal Operation Variable getArgumentCount :=
  operationFromValues (Variable := Variable) mul
    (Sequences.List.firstElement addend
      (Sequences.List.firstElement (fromCardinalNaturalPeano count)
        Sequences.List.empty))
    (by
      simp only [Sequences.List.length, h]
      rfl)

theorem toPeano_eq_compute_repeatedAddendsTerm {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (add : Operation)
    (h : getArgumentCount add = Numbers.CardinalNatural.Peano.two)
    (getVariableValue : Variable → Decimal)
    (computeOperation : (op : Operation) → (operands : Sequences.List Decimal) →
      operands.length = getArgumentCount op → Decimal)
    (hAdd : ∀ (x y : Decimal)
        (hlen : (Sequences.List.firstElement x
          (Sequences.List.firstElement y Sequences.List.empty)).length =
            getArgumentCount add),
      computeOperation add
        (Sequences.List.firstElement x
          (Sequences.List.firstElement y Sequences.List.empty)) hlen =
        x + y)
    (addend : Decimal) (count : Numbers.CardinalNatural.Peano)
    (hne : count ≠ Numbers.CardinalNatural.Peano.zero) :
    addend.toPeano * Integer.Peano.fromCardinalNatural count =
      (compute getVariableValue computeOperation
        (repeatedAddendsTerm (Variable := Variable) add h addend count
          hne)).toPeano := by
  rw [repeatedAddendsTerm_eq_binaryOperationFromValues,
    toPeano_compute_binaryOperationFromValues_add add h getVariableValue
      computeOperation hAdd]
  exact (sumToPeano_repeatedAddends addend count).symm

theorem toPeano_eq_compute_productTerm {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (mul : Operation)
    (h : getArgumentCount mul = Numbers.CardinalNatural.Peano.two)
    (getVariableValue : Variable → Decimal)
    (computeOperation : (op : Operation) → (operands : Sequences.List Decimal) →
      operands.length = getArgumentCount op → Decimal)
    (hMul : ∀ (x y : Decimal)
        (hlen : (Sequences.List.firstElement x
          (Sequences.List.firstElement y Sequences.List.empty)).length =
            getArgumentCount mul),
      computeOperation mul
        (Sequences.List.firstElement x
          (Sequences.List.firstElement y Sequences.List.empty)) hlen =
        x * y)
    (addend : Decimal) (count : Numbers.CardinalNatural.Peano) :
    addend.toPeano * Integer.Peano.fromCardinalNatural count =
      (compute getVariableValue computeOperation
        (productTerm (Variable := Variable) mul h addend count)).toPeano := by
  simp only [productTerm, compute_operationFromValues, hMul, multiply_toPeano,
    toPeano_fromCardinalNaturalPeano]

/-- The cardinal count of a non-negative integer decimal; `none` when negative. -/
def tryNonNegativeCount (d : Decimal) :
    Option Numbers.CardinalNatural.Peano :=
  if h : zero ≤ d then some (toCardinalNaturalPeano d h) else none

/-- Replace a sum of at least two identical integer addends with the product
of the addend and `fromCardinalNaturalPeano` of the number of addends. -/
def tryReplaceSumWithProduct {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    [DecidableEq Operation] (add mul : Operation)
    (hMul : getArgumentCount mul = Numbers.CardinalNatural.Peano.two) :
    ZeroMath.Terms.Homogeneous.Tree Decimal Operation Variable getArgumentCount →
      Option (ZeroMath.Terms.Homogeneous.Tree Decimal Operation Variable
        getArgumentCount) :=
  ZeroMath.Terms.Homogeneous.Tree.tryReplaceSumWithProduct add mul hMul
    fromCardinalNaturalPeano

/-- Replace a product of two integer decimals with the sum of the second
factor's non-negative cardinal count copies of the first factor. -/
def tryReplaceProductWithSumOfFirstFactor {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    [DecidableEq Operation] (add mul : Operation)
    (hAdd : getArgumentCount add = Numbers.CardinalNatural.Peano.two) :
    ZeroMath.Terms.Homogeneous.Tree Decimal Operation Variable getArgumentCount →
      Option (ZeroMath.Terms.Homogeneous.Tree Decimal Operation Variable
        getArgumentCount) :=
  ZeroMath.Terms.Homogeneous.Tree.tryReplaceProductWithSumOfFirstFactor add mul
    hAdd tryNonNegativeCount

/-- Replace a product of two integer decimals with the sum of the first
factor's non-negative cardinal count copies of the second factor. -/
def tryReplaceProductWithSumOfSecondFactor {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    [DecidableEq Operation] (add mul : Operation)
    (hAdd : getArgumentCount add = Numbers.CardinalNatural.Peano.two) :
    ZeroMath.Terms.Homogeneous.Tree Decimal Operation Variable getArgumentCount →
      Option (ZeroMath.Terms.Homogeneous.Tree Decimal Operation Variable
        getArgumentCount) :=
  ZeroMath.Terms.Homogeneous.Tree.tryReplaceProductWithSumOfSecondFactor add mul
    hAdd tryNonNegativeCount

theorem tryReplaceSumWithProduct_eq {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    [DecidableEq Operation] (add mul : Operation)
    (hMul : getArgumentCount mul = Numbers.CardinalNatural.Peano.two)
    (t : ZeroMath.Terms.Homogeneous.Tree Decimal Operation Variable
      getArgumentCount) :
    tryReplaceSumWithProduct (Variable := Variable) add mul hMul t =
      ZeroMath.Terms.Homogeneous.Tree.tryReplaceSumWithProduct
        (Variable := Variable) add mul hMul fromCardinalNaturalPeano t :=
  rfl

end ZeroMath.Numbers.Integer.Decimal.Terms.Homogeneous.Trees
