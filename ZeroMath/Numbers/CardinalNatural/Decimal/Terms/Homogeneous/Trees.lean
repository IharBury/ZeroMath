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

end ZeroMath.Numbers.CardinalNatural.Decimal.Terms.Homogeneous.Trees
