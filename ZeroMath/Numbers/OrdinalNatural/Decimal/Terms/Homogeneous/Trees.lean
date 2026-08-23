import ZeroMath.Numbers.OrdinalNatural.Decimal.PlaceValue
import ZeroMath.Terms.Homogeneous.Tree

namespace ZeroMath.Numbers.OrdinalNatural.Decimal.Terms.Homogeneous.Trees

open ZeroMath.Terms.Homogeneous.Tree

/-- The place-value addends of `d` as a homogeneous sum term under binary
addition operation `add`. `getArgumentCount add` must be two. A one-digit
number is a value leaf; longer writings nest as `(... + y) + z`. Zero addends
are omitted. -/
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

/-- Left-associated addition of ordinal decimals, matching
`binaryOperationFromValues.go`. -/
theorem toCardinalPeano_goValue_add (acc : Decimal)
    (xs : Sequences.List Decimal) :
    toCardinalPeano
        (binaryOperationFromValues.goValue (fun a b => a + b) acc xs) =
      acc.toCardinalPeano + sumToCardinalPeano xs := by
  induction xs generalizing acc with
  | empty =>
      rw [binaryOperationFromValues.goValue_empty, sumToCardinalPeano,
        Numbers.CardinalNatural.Peano.add_zero]
  | firstElement x xs ih =>
      rw [binaryOperationFromValues.goValue_firstElement, ih, toCardinalPeano_add,
        sumToCardinalPeano, Numbers.CardinalNatural.Peano.add_associative]

/-- Computing a left-associated addition tree recovers the cardinal Peano
sum of the value list. -/
theorem toCardinalPeano_compute_binaryOperationFromValues_add {Operation : Type v}
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
    toCardinalPeano
        (compute getVariableValue computeOperation
          (binaryOperationFromValues (Variable := Variable) add h values hne)) =
      sumToCardinalPeano values := by
  cases values with
  | empty => exact False.elim (hne rfl)
  | firstElement x xs =>
      rw [compute_binaryOperationFromValues_firstElement
        getVariableValue computeOperation add h (fun a b => a + b) hAdd]
      rw [sumToCardinalPeano, toCardinalPeano_goValue_add]

/-- Computing the place-value sum term under binary addition recovers the
cardinal Peano value of `d`. -/
theorem toCardinalPeano_eq_compute_placeAddendsTerm {Operation : Type v}
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
    toCardinalPeano d =
      toCardinalPeano
        (compute getVariableValue computeOperation
          (placeAddendsTerm (Variable := Variable) add h d)) := by
  rw [placeAddendsTerm_eq_binaryOperationFromValues,
    toCardinalPeano_compute_binaryOperationFromValues_add add h
      getVariableValue computeOperation hAdd]
  exact toCardinalPeano_eq_sumToCardinalPeano_placeAddends d

/-- Computing the place-value sum term under binary addition recovers the
ordinal Peano value of `d`. -/
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
        (placeAddendsTerm (Variable := Variable) add h d)).toPeano :=
  toPeano_eq_of_equivalent
    (equivalent_of_toCardinalPeano_eq
      (toCardinalPeano_eq_compute_placeAddendsTerm
        add h getVariableValue computeOperation hAdd d))

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
  equivalent_of_toCardinalPeano_eq
    (toCardinalPeano_eq_compute_placeAddendsTerm
      add h getVariableValue computeOperation hAdd d)

example :
    let n : Decimal :=
      Numbers.CardinalNatural.Decimal.toOrdinal
        (Numbers.CardinalNatural.Decimal.fromDigit
          Numbers.Digits.threeDigit)
        (by decide)
    n ≈ compute (fun v : Empty => nomatch v)
      (fun _ operands _ =>
        match operands with
        | Sequences.List.firstElement x
            (Sequences.List.firstElement y _) =>
          x + y
        | Sequences.List.firstElement x Sequences.List.empty => x
        | Sequences.List.empty => one)
      (placeAddendsTerm (Variable := Empty)
        (getArgumentCount := fun k => k)
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
      | Sequences.List.empty => one)
    (fun _ _ _ => rfl) _

/-- The sum of `count` copies of `addend` as a homogeneous term under binary
addition. A single addend is a value leaf; longer lists nest left-associated. -/
def repeatedAddendsTerm {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (add : Operation)
    (h : getArgumentCount add = Numbers.CardinalNatural.Peano.two)
    (addend : Decimal) (count : Peano) :
    ZeroMath.Terms.Homogeneous.Tree Decimal Operation Variable getArgumentCount :=
  binaryOperationFromValues add h (repeatedAddends addend count)
    (repeatedAddends_ne_empty addend count)

theorem repeatedAddendsTerm_eq_binaryOperationFromValues {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (add : Operation)
    (h : getArgumentCount add = Numbers.CardinalNatural.Peano.two)
    (addend : Decimal) (count : Peano) :
    repeatedAddendsTerm (Variable := Variable) add h addend count =
      binaryOperationFromValues (Variable := Variable) add h
        (repeatedAddends addend count)
        (repeatedAddends_ne_empty addend count) :=
  rfl

/-- The product `addend * fromPeano count` as a homogeneous binary term. -/
def productTerm {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (mul : Operation)
    (h : getArgumentCount mul = Numbers.CardinalNatural.Peano.two)
    (addend : Decimal) (count : Peano) :
    ZeroMath.Terms.Homogeneous.Tree Decimal Operation Variable getArgumentCount :=
  operationFromValues (Variable := Variable) mul
    (Sequences.List.firstElement addend
      (Sequences.List.firstElement (fromPeano count) Sequences.List.empty))
    (by
      simp only [Sequences.List.length, h]
      rfl)

theorem toCardinalPeano_eq_compute_repeatedAddendsTerm {Operation : Type v}
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
    (addend : Decimal) (count : Peano) :
    addend.toCardinalPeano *
        Numbers.CardinalNatural.Peano.fromOrdinal count =
      toCardinalPeano
        (compute getVariableValue computeOperation
          (repeatedAddendsTerm (Variable := Variable) add h addend count)) := by
  rw [repeatedAddendsTerm_eq_binaryOperationFromValues,
    toCardinalPeano_compute_binaryOperationFromValues_add add h
      getVariableValue computeOperation hAdd]
  exact (sumToCardinalPeano_repeatedAddends addend count).symm

theorem toCardinalPeano_eq_compute_productTerm {Operation : Type v}
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
    (addend : Decimal) (count : Peano) :
    addend.toCardinalPeano *
        Numbers.CardinalNatural.Peano.fromOrdinal count =
      toCardinalPeano
        (compute getVariableValue computeOperation
          (productTerm (Variable := Variable) mul h addend count)) := by
  simp only [productTerm, compute_operationFromValues, hMul,
    multiply_toCardinalPeano, toCardinalPeano_fromPeano]

/-- Write a cardinal count as an ordinal decimal. Zero is written as `one`
because ordinals have no zero; `tryReplaceSumWithProduct` only uses this on
counts of at least two. -/
def fromCardinalCount (n : Numbers.CardinalNatural.Peano) : Decimal :=
  if h : n = Numbers.CardinalNatural.Peano.zero then
    one
  else
    fromCardinalPeano n h

/-- Replace a sum of at least two identical ordinal addends with the product
of the addend and the written cardinal count of addends. Addition and
multiplication must both be binary. -/
def tryReplaceSumWithProduct {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    [DecidableEq Operation] (add mul : Operation)
    (hAdd : getArgumentCount add = Numbers.CardinalNatural.Peano.two)
    (hMul : getArgumentCount mul = Numbers.CardinalNatural.Peano.two) :
    ZeroMath.Terms.Homogeneous.Tree Decimal Operation Variable getArgumentCount →
      Option (ZeroMath.Terms.Homogeneous.Tree Decimal Operation Variable
        getArgumentCount) :=
  ZeroMath.Terms.Homogeneous.Tree.tryReplaceSumWithProduct add mul hAdd hMul
    fromCardinalCount

/-- Replace a product of two ordinal decimals with the sum of
`toCardinalPeano` copies of the first factor. -/
def tryReplaceProductWithSumOfFirstFactor {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    [DecidableEq Operation] (add mul : Operation)
    (hAdd : getArgumentCount add = Numbers.CardinalNatural.Peano.two) :
    ZeroMath.Terms.Homogeneous.Tree Decimal Operation Variable getArgumentCount →
      Option (ZeroMath.Terms.Homogeneous.Tree Decimal Operation Variable
        getArgumentCount) :=
  ZeroMath.Terms.Homogeneous.Tree.tryReplaceProductWithSumOfFirstFactor add mul
    hAdd (fun d => some (toCardinalPeano d))

/-- Replace a product of two ordinal decimals with the sum of
`toCardinalPeano` copies of the second factor. -/
def tryReplaceProductWithSumOfSecondFactor {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    [DecidableEq Operation] (add mul : Operation)
    (hAdd : getArgumentCount add = Numbers.CardinalNatural.Peano.two) :
    ZeroMath.Terms.Homogeneous.Tree Decimal Operation Variable getArgumentCount →
      Option (ZeroMath.Terms.Homogeneous.Tree Decimal Operation Variable
        getArgumentCount) :=
  ZeroMath.Terms.Homogeneous.Tree.tryReplaceProductWithSumOfSecondFactor add mul
    hAdd (fun d => some (toCardinalPeano d))

theorem tryReplaceSumWithProduct_eq {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    [DecidableEq Operation] (add mul : Operation)
    (hAdd : getArgumentCount add = Numbers.CardinalNatural.Peano.two)
    (hMul : getArgumentCount mul = Numbers.CardinalNatural.Peano.two)
    (t : ZeroMath.Terms.Homogeneous.Tree Decimal Operation Variable
      getArgumentCount) :
    tryReplaceSumWithProduct (Variable := Variable) add mul hAdd hMul t =
      ZeroMath.Terms.Homogeneous.Tree.tryReplaceSumWithProduct
        (Variable := Variable) add mul hAdd hMul fromCardinalCount t :=
  rfl

end ZeroMath.Numbers.OrdinalNatural.Decimal.Terms.Homogeneous.Trees
