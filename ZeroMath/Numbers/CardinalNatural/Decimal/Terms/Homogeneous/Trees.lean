import ZeroMath.Numbers.CardinalNatural.Decimal
import ZeroMath.Terms.Homogeneous.Tree

namespace ZeroMath.Numbers.CardinalNatural.Decimal.Terms.Homogeneous.Trees

open CardinalNatural (Peano)
open Decimal (placeAddends placeAddend fromDigit placeAddends_ne_empty)
open Numbers.Digits (zeroDigit oneDigit threeDigit fourDigit fiveDigit sevenDigit)
open ZeroMath.Terms.Homogeneous.Tree

/-- The place-value addends of `d` as a homogeneous sum term under binary
addition operation `add`. `getArgumentCount add` must be two. A one-digit
number is a value leaf; longer writings nest as `(... + y) + z`. Zero addends
are omitted unless `d` is zero. For `347` this is `(300 + 40) + 7`; for `1005`
this is `1000 + 5`. -/
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
    let n : Decimal := fromDigit zeroDigit
    let expected :
        ZeroMath.Terms.Homogeneous.Tree Decimal Peano Empty (fun k => k) :=
      value (fromDigit zeroDigit)
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
          (operation Peano.two
            (ArgumentList.twoElements
              (value (placeAddend threeDigit Peano.two))
              (value (placeAddend fourDigit Peano.one))))
          (value (placeAddend sevenDigit Peano.zero)))
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
          (value (placeAddend fiveDigit Peano.zero)))
    placeAddendsTerm (Variable := Empty) (getArgumentCount := fun k => k)
      Peano.two rfl n =
      expected :=
  rfl

/-- Left-associated addition of decimals, matching `binaryOperationFromValues.go`. -/
theorem toPeano_goValue_add (acc : Decimal) (xs : Sequences.List Decimal) :
    (binaryOperationFromValues.goValue (fun a b => a + b) acc xs).toPeano =
      acc.toPeano + sumToPeano xs := by
  induction xs generalizing acc with
  | empty =>
      rw [binaryOperationFromValues.goValue_empty, sumToPeano, Peano.add_zero]
  | firstElement x xs ih =>
      rw [binaryOperationFromValues.goValue_firstElement, ih, add_toPeano,
        sumToPeano, Peano.add_associative]

/-- Computing a left-associated addition tree recovers the Peano sum of the
value list. -/
theorem toPeano_compute_binaryOperationFromValues_add {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Peano} (add : Operation)
    (h : getArgumentCount add = Peano.two)
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
    {getArgumentCount : Operation → Peano} (add : Operation)
    (h : getArgumentCount add = Peano.two)
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
    {getArgumentCount : Operation → Peano} (add : Operation)
    (h : getArgumentCount add = Peano.two)
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
      ⟨Sequences.List.firstElement threeDigit
        (Sequences.List.firstElement fourDigit
          (Sequences.List.firstElement sevenDigit Sequences.List.empty)), by simp⟩
    n ≈ compute (fun v : Empty => nomatch v)
      (fun _ operands _ =>
        match operands with
        | Sequences.List.firstElement x
            (Sequences.List.firstElement y _) =>
          x + y
        | Sequences.List.firstElement x Sequences.List.empty => x
        | Sequences.List.empty => fromDigit zeroDigit)
      (placeAddendsTerm (Variable := Empty) (getArgumentCount := fun k => k)
        Peano.two rfl n) :=
  equivalent_compute_placeAddendsTerm (Variable := Empty)
    (getArgumentCount := fun k => k) Peano.two rfl
    (fun v => nomatch v)
    (fun _ operands _ =>
      match operands with
      | Sequences.List.firstElement x
          (Sequences.List.firstElement y _) =>
        x + y
      | Sequences.List.firstElement x Sequences.List.empty => x
      | Sequences.List.empty => fromDigit zeroDigit)
    (fun _ _ _ => rfl) _

/-- The sum of `count` copies of `addend` as a homogeneous term under binary
addition. `count` must be nonzero. A single addend is a value leaf; longer
lists nest left-associated as `(... + a) + a`. For `addend = 5` and
`count = 4` this is `((5 + 5) + 5) + 5`. -/
def repeatedAddendsTerm {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Peano} (add : Operation)
    (h : getArgumentCount add = Peano.two) (addend : Decimal) (count : Peano)
    (hne : count ≠ Peano.zero) :
    ZeroMath.Terms.Homogeneous.Tree Decimal Operation Variable getArgumentCount :=
  binaryOperationFromValues add h (repeatedAddends addend count)
    (repeatedAddends_ne_empty addend count hne)

theorem repeatedAddendsTerm_eq_binaryOperationFromValues {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Peano} (add : Operation)
    (h : getArgumentCount add = Peano.two) (addend : Decimal) (count : Peano)
    (hne : count ≠ Peano.zero) :
    repeatedAddendsTerm (Variable := Variable) add h addend count hne =
      binaryOperationFromValues (Variable := Variable) add h
        (repeatedAddends addend count)
        (repeatedAddends_ne_empty addend count hne) :=
  rfl

/-- The product `addend * fromPeano count` as a homogeneous binary term. -/
def productTerm {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Peano} (mul : Operation)
    (h : getArgumentCount mul = Peano.two) (addend : Decimal) (count : Peano) :
    ZeroMath.Terms.Homogeneous.Tree Decimal Operation Variable getArgumentCount :=
  operationFromValues (Variable := Variable) mul
    (Sequences.List.firstElement addend
      (Sequences.List.firstElement (fromPeano count) Sequences.List.empty))
    (by
      simp only [Sequences.List.length, h]
      rfl)

theorem productTerm_eq_operationFromValues {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Peano} (mul : Operation)
    (h : getArgumentCount mul = Peano.two) (addend : Decimal) (count : Peano) :
    productTerm (Variable := Variable) mul h addend count =
      operationFromValues (Variable := Variable) mul
        (Sequences.List.firstElement addend
          (Sequences.List.firstElement (fromPeano count) Sequences.List.empty))
        (by
          simp only [Sequences.List.length, h]
          rfl) :=
  rfl

/-- Computing the repeated-addends sum term under binary addition recovers
`addend * count`. -/
theorem toPeano_eq_compute_repeatedAddendsTerm {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Peano} (add : Operation)
    (h : getArgumentCount add = Peano.two)
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
    (addend : Decimal) (count : Peano) (hne : count ≠ Peano.zero) :
    addend.toPeano * count =
      (compute getVariableValue computeOperation
        (repeatedAddendsTerm (Variable := Variable) add h addend count hne)).toPeano := by
  rw [repeatedAddendsTerm_eq_binaryOperationFromValues,
    toPeano_compute_binaryOperationFromValues_add add h getVariableValue
      computeOperation hAdd]
  exact (sumToPeano_repeatedAddends addend count).symm

/-- Computing the product term under binary multiplication recovers
`addend * count`. -/
theorem toPeano_eq_compute_productTerm {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Peano} (mul : Operation)
    (h : getArgumentCount mul = Peano.two)
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
    addend.toPeano * count =
      (compute getVariableValue computeOperation
        (productTerm (Variable := Variable) mul h addend count)).toPeano := by
  rw [productTerm_eq_operationFromValues, compute_operationFromValues,
    hMul, multiply_toPeano, toPeano_fromPeano]

/-- The repeated-addends sum term and the product term have the same value. -/
theorem toPeano_compute_repeatedAddendsTerm_eq_productTerm {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Peano}
    (add mul : Operation)
    (hAddArity : getArgumentCount add = Peano.two)
    (hMulArity : getArgumentCount mul = Peano.two)
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
    (hMul : ∀ (x y : Decimal)
        (hlen : (Sequences.List.firstElement x
          (Sequences.List.firstElement y Sequences.List.empty)).length =
            getArgumentCount mul),
      computeOperation mul
        (Sequences.List.firstElement x
          (Sequences.List.firstElement y Sequences.List.empty)) hlen =
        x * y)
    (addend : Decimal) (count : Peano) (hne : count ≠ Peano.zero) :
    (compute getVariableValue computeOperation
        (repeatedAddendsTerm (Variable := Variable) add hAddArity addend count
          hne)).toPeano =
      (compute getVariableValue computeOperation
        (productTerm (Variable := Variable) mul hMulArity addend count)).toPeano :=
  (toPeano_eq_compute_repeatedAddendsTerm add hAddArity getVariableValue
      computeOperation hAdd addend count hne).symm.trans
    (toPeano_eq_compute_productTerm mul hMulArity getVariableValue
      computeOperation hMul addend count)

example :
    let addend : Decimal := fromDigit fiveDigit
    let expected :
        ZeroMath.Terms.Homogeneous.Tree Decimal Peano Empty (fun k => k) :=
      operation Peano.two
        (ArgumentList.twoElements
          (operation Peano.two
            (ArgumentList.twoElements
              (operation Peano.two
                (ArgumentList.twoElements
                  (value addend) (value addend)))
              (value addend)))
          (value addend))
    repeatedAddendsTerm (Variable := Empty) (getArgumentCount := fun k => k)
      Peano.two rfl addend Peano.four (Peano.successor_ne_zero Peano.three) =
      expected :=
  rfl

/-- Replace a sum of at least two identical decimal addends with the product
of the addend and `fromPeano` of the number of addends. -/
def tryReplaceSumWithProduct {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Peano}
    [DecidableEq Operation] (add mul : Operation)
    (hMul : getArgumentCount mul = Peano.two) :
    ZeroMath.Terms.Homogeneous.Tree Decimal Operation Variable getArgumentCount →
      Option (ZeroMath.Terms.Homogeneous.Tree Decimal Operation Variable
        getArgumentCount) :=
  ZeroMath.Terms.Homogeneous.Tree.tryReplaceSumWithProduct add mul hMul fromPeano

/-- Replace a product of two decimals with the sum of `toPeano` copies of the
first factor. -/
def tryReplaceProductWithSumOfFirstFactor {Operation : Type v}
    {Variable : Type w} {getArgumentCount : Operation → Peano}
    [DecidableEq Operation] (add mul : Operation)
    (hAdd : getArgumentCount add = Peano.two) :
    ZeroMath.Terms.Homogeneous.Tree Decimal Operation Variable getArgumentCount →
      Option (ZeroMath.Terms.Homogeneous.Tree Decimal Operation Variable
        getArgumentCount) :=
  ZeroMath.Terms.Homogeneous.Tree.tryReplaceProductWithSumOfFirstFactor add mul
    hAdd (fun d => some d.toPeano)

/-- Replace a product of two decimals with the sum of `toPeano` copies of the
second factor. -/
def tryReplaceProductWithSumOfSecondFactor {Operation : Type v}
    {Variable : Type w} {getArgumentCount : Operation → Peano}
    [DecidableEq Operation] (add mul : Operation)
    (hAdd : getArgumentCount add = Peano.two) :
    ZeroMath.Terms.Homogeneous.Tree Decimal Operation Variable getArgumentCount →
      Option (ZeroMath.Terms.Homogeneous.Tree Decimal Operation Variable
        getArgumentCount) :=
  ZeroMath.Terms.Homogeneous.Tree.tryReplaceProductWithSumOfSecondFactor add mul
    hAdd (fun d => some d.toPeano)

theorem tryReplaceSumWithProduct_eq {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Peano}
    [DecidableEq Operation] (add mul : Operation)
    (hMul : getArgumentCount mul = Peano.two)
    (t : ZeroMath.Terms.Homogeneous.Tree Decimal Operation Variable
      getArgumentCount) :
    tryReplaceSumWithProduct (Variable := Variable) add mul hMul t =
      ZeroMath.Terms.Homogeneous.Tree.tryReplaceSumWithProduct
        (Variable := Variable) add mul hMul fromPeano t :=
  rfl

theorem tryReplaceProductWithSumOfFirstFactor_eq {Operation : Type v}
    {Variable : Type w} {getArgumentCount : Operation → Peano}
    [DecidableEq Operation] (add mul : Operation)
    (hAdd : getArgumentCount add = Peano.two)
    (t : ZeroMath.Terms.Homogeneous.Tree Decimal Operation Variable
      getArgumentCount) :
    tryReplaceProductWithSumOfFirstFactor (Variable := Variable) add mul hAdd t =
      ZeroMath.Terms.Homogeneous.Tree.tryReplaceProductWithSumOfFirstFactor
        (Variable := Variable) add mul hAdd (fun d => some d.toPeano) t :=
  rfl

theorem tryReplaceProductWithSumOfSecondFactor_eq {Operation : Type v}
    {Variable : Type w} {getArgumentCount : Operation → Peano}
    [DecidableEq Operation] (add mul : Operation)
    (hAdd : getArgumentCount add = Peano.two)
    (t : ZeroMath.Terms.Homogeneous.Tree Decimal Operation Variable
      getArgumentCount) :
    tryReplaceProductWithSumOfSecondFactor (Variable := Variable) add mul hAdd
        t =
      ZeroMath.Terms.Homogeneous.Tree.tryReplaceProductWithSumOfSecondFactor
        (Variable := Variable) add mul hAdd (fun d => some d.toPeano) t :=
  rfl

example :
    let addend : Decimal := fromDigit fiveDigit
    tryReplaceSumWithProduct (Variable := Empty)
        (getArgumentCount := fun _ : Bool => Peano.two) false true rfl
        (repeatedAddendsTerm (Variable := Empty)
          (getArgumentCount := fun _ : Bool => Peano.two) false rfl addend
          Peano.two (Peano.successor_ne_zero Peano.one)) =
      some (productTerm (Variable := Empty)
        (getArgumentCount := fun _ : Bool => Peano.two) true rfl addend
        Peano.two) :=
  rfl

example :
    let addend : Decimal := fromDigit fiveDigit
    tryReplaceProductWithSumOfFirstFactor (Variable := Empty)
        (getArgumentCount := fun _ : Bool => Peano.two) false true rfl
        (productTerm (Variable := Empty)
          (getArgumentCount := fun _ : Bool => Peano.two) true rfl addend
          Peano.two) =
      some (repeatedAddendsTerm (Variable := Empty)
        (getArgumentCount := fun _ : Bool => Peano.two) false rfl addend
        Peano.two (Peano.successor_ne_zero Peano.one)) :=
  rfl

example :
    let addend : Decimal := fromDigit twoDigit
    tryReplaceProductWithSumOfSecondFactor (Variable := Empty)
        (getArgumentCount := fun _ : Bool => Peano.two) false true rfl
        (productTerm (Variable := Empty)
          (getArgumentCount := fun _ : Bool => Peano.two) true rfl addend
          Peano.three) =
      some (repeatedAddendsTerm (Variable := Empty)
        (getArgumentCount := fun _ : Bool => Peano.two) false rfl
        (fromPeano Peano.three) addend.toPeano
        (Peano.successor_ne_zero Peano.one)) :=
  rfl

end ZeroMath.Numbers.CardinalNatural.Decimal.Terms.Homogeneous.Trees
