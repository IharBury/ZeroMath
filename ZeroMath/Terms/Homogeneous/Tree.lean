import ZeroMath.Logic.DerivedEquivalence
import ZeroMath.Sequences.List

namespace ZeroMath.Terms.Homogeneous

mutual
  /-- A homogeneous term tree: value and variable leaves, and operation nodes whose
  number of arguments is given by `getArgumentCount`. Values have type `Value`, operations
  have type `Operation`, and variables have type `Variable`. Each of those types is compared by
  decidable setoid equivalence when a `Setoid` is available, and by decidable
  equality otherwise. -/
  inductive Tree (Value : Type u) (Operation : Type v) (Variable : Type w)
      (getArgumentCount : Operation → Numbers.CardinalNatural.Peano) where
    /-- A value leaf. -/
    | value : Value → Tree Value Operation Variable getArgumentCount
    /-- A variable leaf. Named `variableLeaf` because `variable` is a Lean keyword. -/
    | variableLeaf : Variable → Tree Value Operation Variable getArgumentCount
    /-- An operation node with exactly `getArgumentCount op` argument trees. -/
    | operation (op : Operation) :
        Tree.ArgumentList Value Operation Variable getArgumentCount (getArgumentCount op) →
        Tree Value Operation Variable getArgumentCount

  /-- Exactly `count` argument trees, matching the operation's `getArgumentCount`. -/
  inductive Tree.ArgumentList (Value : Type u) (Operation : Type v) (Variable : Type w)
      (getArgumentCount : Operation → Numbers.CardinalNatural.Peano) :
      Numbers.CardinalNatural.Peano → Type (max u v w) where
    | empty : Tree.ArgumentList Value Operation Variable getArgumentCount Numbers.CardinalNatural.Peano.zero
    | firstElement {count : Numbers.CardinalNatural.Peano} :
        Tree Value Operation Variable getArgumentCount →
        Tree.ArgumentList Value Operation Variable getArgumentCount count →
        Tree.ArgumentList Value Operation Variable getArgumentCount count.successor
end

namespace Tree

namespace ArgumentList

def toList {Value : Type u} {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    {count : Numbers.CardinalNatural.Peano} :
    ArgumentList Value Operation Variable getArgumentCount count →
      Sequences.List (Tree Value Operation Variable getArgumentCount)
  | empty => Sequences.List.empty
  | firstElement t ts => Sequences.List.firstElement t (toList ts)

theorem toList_length {Value : Type u} {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    {count : Numbers.CardinalNatural.Peano} :
    (arguments : ArgumentList Value Operation Variable getArgumentCount count) →
      (toList arguments).length = count
  | empty => rfl
  | firstElement _ ts => by
      simp only [toList, Sequences.List.length, toList_length ts,
        Numbers.CardinalNatural.Peano.add_one]

def tryFromList {Value : Type u} {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano} :
    (count : Numbers.CardinalNatural.Peano) →
    Sequences.List (Tree Value Operation Variable getArgumentCount) →
      Option (ArgumentList Value Operation Variable getArgumentCount count)
  | Numbers.CardinalNatural.Peano.zero, Sequences.List.empty => some empty
  | Numbers.CardinalNatural.Peano.zero, Sequences.List.firstElement _ _ => none
  | Numbers.CardinalNatural.Peano.successor _, Sequences.List.empty => none
  | Numbers.CardinalNatural.Peano.successor count, Sequences.List.firstElement t ts =>
    match tryFromList count ts with
    | some arguments => some (firstElement t arguments)
    | none => none

theorem tryFromList_eq_some_iff {Value : Type u} {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano} :
    {count : Numbers.CardinalNatural.Peano} →
    (arguments : ArgumentList Value Operation Variable getArgumentCount count) →
    (l : Sequences.List (Tree Value Operation Variable getArgumentCount)) →
    (tryFromList count l = some arguments ↔ toList arguments = l)
  | _, empty, Sequences.List.empty => by
      simp only [tryFromList, toList]
  | _, empty, Sequences.List.firstElement _ _ => by
      simp only [tryFromList, toList]
      constructor
      · intro h
        cases h
      · intro h
        cases h
  | _, firstElement t ts, Sequences.List.empty => by
      simp only [tryFromList, toList]
      constructor
      · intro h
        nomatch h
      · intro h
        cases h
  | _, firstElement t ts, Sequences.List.firstElement t' ts' => by
      simp only [tryFromList, toList, Sequences.List.firstElement.injEq]
      constructor
      · intro h
        split at h
        · next hts =>
          cases Option.some.inj h
          exact ⟨rfl, (tryFromList_eq_some_iff ts ts').mp hts⟩
        · next =>
          cases h
      · intro ⟨ht, hts⟩
        cases ht
        have htyped := (tryFromList_eq_some_iff ts ts').mpr hts
        simp only [htyped]

def fromList {Value : Type u} {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano} :
    (count : Numbers.CardinalNatural.Peano) →
    (l : Sequences.List (Tree Value Operation Variable getArgumentCount)) →
    l.length = count →
    ArgumentList Value Operation Variable getArgumentCount count
  | Numbers.CardinalNatural.Peano.zero, Sequences.List.empty, _ => empty
  | Numbers.CardinalNatural.Peano.successor count, Sequences.List.firstElement t ts, h =>
    firstElement t (fromList count ts
      (Numbers.CardinalNatural.Peano.successor_injective (by
        rw [← Sequences.List.length_firstElement t ts]
        exact h)))
  | Numbers.CardinalNatural.Peano.zero, Sequences.List.firstElement _ _, h =>
    False.elim (Sequences.List.length_ne_zero_of_ne_empty (by intro heq; cases heq) h)
  | Numbers.CardinalNatural.Peano.successor count, Sequences.List.empty, h =>
    False.elim (Numbers.CardinalNatural.Peano.successor_ne_zero count h.symm)

theorem fromList_toList {Value : Type u} {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano} :
    (count : Numbers.CardinalNatural.Peano) →
    (l : Sequences.List (Tree Value Operation Variable getArgumentCount)) →
    (h : l.length = count) →
    toList (fromList count l h) = l
  | Numbers.CardinalNatural.Peano.zero, Sequences.List.empty, _ => rfl
  | Numbers.CardinalNatural.Peano.successor count, Sequences.List.firstElement t ts, h => by
      simp only [fromList, toList,
        fromList_toList count ts
          (Numbers.CardinalNatural.Peano.successor_injective (by
            rw [← Sequences.List.length_firstElement t ts]
            exact h))]
  | Numbers.CardinalNatural.Peano.zero, Sequences.List.firstElement _ _, h =>
    False.elim (Sequences.List.length_ne_zero_of_ne_empty (by intro heq; cases heq) h)
  | Numbers.CardinalNatural.Peano.successor count, Sequences.List.empty, h =>
    False.elim (Numbers.CardinalNatural.Peano.successor_ne_zero count h.symm)

theorem tryFromList_eq_some_fromList {Value : Type u} {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (count : Numbers.CardinalNatural.Peano)
    (l : Sequences.List (Tree Value Operation Variable getArgumentCount))
    (h : l.length = count) :
    tryFromList count l = some (fromList count l h) :=
  (tryFromList_eq_some_iff (fromList count l h) l).mpr (fromList_toList count l h)

/-- Two argument trees, matching an operation of arity `Peano.two`. -/
def twoElements {Value : Type u} {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (t1 t2 : Tree Value Operation Variable getArgumentCount) :
    ArgumentList Value Operation Variable getArgumentCount
      Numbers.CardinalNatural.Peano.two :=
  firstElement t1 (firstElement t2 empty)

/-- The two argument trees of an arity-`two` argument list. -/
def twoTrees {Value : Type u} {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (arguments : ArgumentList Value Operation Variable getArgumentCount
      Numbers.CardinalNatural.Peano.two) :
    Tree Value Operation Variable getArgumentCount ×
      Tree Value Operation Variable getArgumentCount :=
  match arguments with
  | firstElement t1 (firstElement t2 empty) => (t1, t2)

theorem twoTrees_twoElements {Value : Type u} {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (t1 t2 : Tree Value Operation Variable getArgumentCount) :
    twoTrees (twoElements t1 t2) = (t1, t2) :=
  rfl

theorem toList_eq_rec {Value : Type u} {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    {count1 count2 : Numbers.CardinalNatural.Peano}
    (hcount : count1 = count2)
    (arguments : ArgumentList Value Operation Variable getArgumentCount count1) :
    toList (hcount ▸ arguments) = toList arguments := by
  cases hcount
  rfl

end ArgumentList

open Logic (DerivedEquivalence)

/-- Build an operation node when `arguments` has exactly `getArgumentCount op`
elements. -/
def tryOperation {Value : Type u} {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano} (op : Operation)
    (arguments : Sequences.List (Tree Value Operation Variable getArgumentCount)) :
    Option (Tree Value Operation Variable getArgumentCount) :=
  match ArgumentList.tryFromList (getArgumentCount op) arguments with
  | some typedArguments => some (operation op typedArguments)
  | none => none

theorem tryOperation_eq_some_iff {Value : Type u} {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano} (op : Operation)
    (arguments : Sequences.List (Tree Value Operation Variable getArgumentCount))
    (t : Tree Value Operation Variable getArgumentCount) :
    tryOperation op arguments = some t ↔
      ∃ typedArguments,
        ArgumentList.toList typedArguments = arguments ∧
          t = operation op typedArguments := by
  dsimp only [tryOperation]
  constructor
  · intro h
    split at h
    · next typedArguments htyped =>
      exact ⟨typedArguments,
        (ArgumentList.tryFromList_eq_some_iff typedArguments arguments).mp htyped,
        (Option.some.inj h).symm⟩
    · next =>
      cases h
  · intro ⟨typedArguments, hlist, ht⟩
    have htyped :=
      (ArgumentList.tryFromList_eq_some_iff typedArguments arguments).mpr hlist
    simp only [htyped, ht]

/-- Value leaves in the same order as `values`. -/
def valueList {Value : Type u} {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano} :
    Sequences.List Value →
      Sequences.List (Tree Value Operation Variable getArgumentCount)
  | Sequences.List.empty => Sequences.List.empty
  | Sequences.List.firstElement x xs =>
    Sequences.List.firstElement (Tree.value x) (valueList xs)

theorem valueList_length {Value : Type u} {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (values : Sequences.List Value) :
    (valueList (Variable := Variable) (getArgumentCount := getArgumentCount) values).length =
      values.length :=
  match values with
  | Sequences.List.empty => rfl
  | Sequences.List.firstElement _ xs =>
    congrArg (fun n => n + Numbers.CardinalNatural.Peano.one)
      (valueList_length (Variable := Variable) (getArgumentCount := getArgumentCount) xs)

/-- An operation node whose arguments are the value leaves of `values`. -/
def operationFromValues {Value : Type u} {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (op : Operation) (values : Sequences.List Value)
    (h : values.length = getArgumentCount op) :
    Tree Value Operation Variable getArgumentCount :=
  operation op (ArgumentList.fromList (getArgumentCount op)
    (valueList (Variable := Variable) (getArgumentCount := getArgumentCount) values)
    (Eq.trans
      (valueList_length (Variable := Variable) (getArgumentCount := getArgumentCount) values)
      h))

theorem operationFromValues_toList {Value : Type u} {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (op : Operation) (values : Sequences.List Value)
    (h : values.length = getArgumentCount op) :
    ArgumentList.toList
        (ArgumentList.fromList (getArgumentCount op)
          (valueList (Variable := Variable) (getArgumentCount := getArgumentCount) values)
          (Eq.trans
            (valueList_length (Variable := Variable) (getArgumentCount := getArgumentCount)
              values)
            h)) =
      valueList (Variable := Variable) (getArgumentCount := getArgumentCount) values :=
  ArgumentList.fromList_toList (getArgumentCount op)
    (valueList (Variable := Variable) (getArgumentCount := getArgumentCount) values)
    (Eq.trans
      (valueList_length (Variable := Variable) (getArgumentCount := getArgumentCount) values)
      h)

/-- Left-associated binary tree over a nonempty value list, using an operation
of arity two. A singleton is a value leaf; longer lists nest as
`(... + y) + z`. -/
def binaryOperationFromValues.go {Value : Type u} {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (op : Operation) (hArity : getArgumentCount op = Numbers.CardinalNatural.Peano.two)
    (acc : Tree Value Operation Variable getArgumentCount) :
    Sequences.List Value → Tree Value Operation Variable getArgumentCount
  | Sequences.List.empty => acc
  | Sequences.List.firstElement x xs =>
      binaryOperationFromValues.go op hArity
        (Tree.operation op
          (hArity.symm ▸ ArgumentList.twoElements acc (Tree.value x)))
        xs

def binaryOperationFromValues {Value : Type u} {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (op : Operation) (hArity : getArgumentCount op = Numbers.CardinalNatural.Peano.two) :
    (values : Sequences.List Value) → values ≠ Sequences.List.empty →
      Tree Value Operation Variable getArgumentCount
  | Sequences.List.empty, h => False.elim (h rfl)
  | Sequences.List.firstElement x xs, _ =>
      binaryOperationFromValues.go op hArity (Tree.value x) xs

theorem binaryOperationFromValues.go_empty {Value : Type u} {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (op : Operation) (hArity : getArgumentCount op = Numbers.CardinalNatural.Peano.two)
    (acc : Tree Value Operation Variable getArgumentCount) :
    binaryOperationFromValues.go (Variable := Variable) op hArity acc
        Sequences.List.empty =
      acc :=
  rfl

theorem binaryOperationFromValues.go_firstElement {Value : Type u} {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (op : Operation) (hArity : getArgumentCount op = Numbers.CardinalNatural.Peano.two)
    (acc : Tree Value Operation Variable getArgumentCount) (x : Value)
    (xs : Sequences.List Value) :
    binaryOperationFromValues.go (Variable := Variable) op hArity acc
        (Sequences.List.firstElement x xs) =
      binaryOperationFromValues.go (Variable := Variable) op hArity
        (Tree.operation op
          (hArity.symm ▸ ArgumentList.twoElements acc (Tree.value x)))
        xs :=
  rfl

theorem binaryOperationFromValues_singleton {Value : Type u} {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (op : Operation) (hArity : getArgumentCount op = Numbers.CardinalNatural.Peano.two)
    (x : Value) :
    binaryOperationFromValues (Variable := Variable) op hArity
        (Sequences.List.firstElement x Sequences.List.empty) (by intro heq; cases heq) =
      Tree.value x :=
  rfl

theorem binaryOperationFromValues_eq_go {Value : Type u} {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (op : Operation) (hArity : getArgumentCount op = Numbers.CardinalNatural.Peano.two)
    (x : Value) (xs : Sequences.List Value)
    (hne : Sequences.List.firstElement x xs ≠ Sequences.List.empty) :
    binaryOperationFromValues (Variable := Variable) op hArity
        (Sequences.List.firstElement x xs) hne =
      binaryOperationFromValues.go (Variable := Variable) op hArity
        (Tree.value x) xs :=
  rfl

theorem binaryOperationFromValues_firstElement_firstElement {Value : Type u}
    {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (op : Operation) (hArity : getArgumentCount op = Numbers.CardinalNatural.Peano.two)
    (x y : Value) (ys : Sequences.List Value) :
    binaryOperationFromValues (Variable := Variable) op hArity
        (Sequences.List.firstElement x (Sequences.List.firstElement y ys))
        (by intro heq; cases heq) =
      binaryOperationFromValues.go (Variable := Variable) op hArity
        (Tree.operation op
          (hArity.symm ▸ ArgumentList.twoElements (Tree.value x) (Tree.value y)))
        ys :=
  rfl

example {Value : Type} {Operation : Type} {Variable : Type}
    (getArgumentCount : Operation → Numbers.CardinalNatural.Peano) (x : Value) :
    (Tree.value x : Tree Value Operation Variable getArgumentCount) = Tree.value x := rfl

example {Value : Type} {Operation : Type} {Variable : Type}
    (getArgumentCount : Operation → Numbers.CardinalNatural.Peano) (x : Variable) :
    (Tree.variableLeaf x : Tree Value Operation Variable getArgumentCount) = Tree.variableLeaf x := rfl

example :
    tryOperation (Value := Bool) (Variable := Bool) (getArgumentCount := fun _ =>
      Numbers.CardinalNatural.Peano.zero) false Sequences.List.empty =
      some (operation false ArgumentList.empty) :=
  rfl

example :
    tryOperation (Value := Bool) (Variable := Bool) (getArgumentCount := fun _ =>
      Numbers.CardinalNatural.Peano.one) false Sequences.List.empty =
      none :=
  rfl

example :
    tryOperation (Value := Bool) (Variable := Bool)
      (getArgumentCount := fun _ => Numbers.CardinalNatural.Peano.two) true
      (Sequences.List.firstElement (Tree.value true)
        (Sequences.List.firstElement (Tree.variableLeaf false) Sequences.List.empty)) =
      some (operation true
        (ArgumentList.firstElement (Tree.value true)
          (ArgumentList.firstElement (Tree.variableLeaf false) ArgumentList.empty))) :=
  rfl

mutual
  /-- Compute the value of a term. A value leaf is returned as-is. A variable
  leaf is interpreted with `getVariableValue`. An operation node is interpreted
  with `computeOperation` applied to the operation and the values of its
  operands, which have length `getArgumentCount op`. -/
  def compute {Value : Type u} {Operation : Type v} {Variable : Type w}
      {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
      (getVariableValue : Variable → Value)
      (computeOperation : (op : Operation) → (operands : Sequences.List Value) →
        operands.length = getArgumentCount op → Value) :
      Tree Value Operation Variable getArgumentCount → Value
    | value x => x
    | variableLeaf x => getVariableValue x
    | operation op arguments =>
        let operands := computeArgumentList getVariableValue computeOperation arguments
        computeOperation op operands.val operands.property

  /-- Compute the value of each argument tree, in order. The resulting list has
  the same length as the argument list. -/
  def computeArgumentList {Value : Type u} {Operation : Type v} {Variable : Type w}
      {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
      (getVariableValue : Variable → Value)
      (computeOperation : (op : Operation) → (operands : Sequences.List Value) →
        operands.length = getArgumentCount op → Value)
      {count : Numbers.CardinalNatural.Peano} :
      ArgumentList Value Operation Variable getArgumentCount count →
        { operands : Sequences.List Value // operands.length = count }
    | ArgumentList.empty => ⟨Sequences.List.empty, rfl⟩
    | ArgumentList.firstElement t ts =>
        ⟨Sequences.List.firstElement
          (compute getVariableValue computeOperation t)
          (computeArgumentList getVariableValue computeOperation ts).val,
         by
           rw [Sequences.List.length_firstElement]
           exact congrArg Numbers.CardinalNatural.Peano.successor
             (computeArgumentList getVariableValue computeOperation ts).property⟩
end

theorem compute_value {Value : Type u} {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (getVariableValue : Variable → Value)
    (computeOperation : (op : Operation) → (operands : Sequences.List Value) →
      operands.length = getArgumentCount op → Value)
    (x : Value) :
    compute (Variable := Variable) (getArgumentCount := getArgumentCount)
        getVariableValue computeOperation (value x) =
      x :=
  rfl

theorem compute_variableLeaf {Value : Type u} {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (getVariableValue : Variable → Value)
    (computeOperation : (op : Operation) → (operands : Sequences.List Value) →
      operands.length = getArgumentCount op → Value)
    (x : Variable) :
    compute (getArgumentCount := getArgumentCount)
        getVariableValue computeOperation (variableLeaf x) =
      getVariableValue x :=
  rfl

theorem compute_operation {Value : Type u} {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (getVariableValue : Variable → Value)
    (computeOperation : (op : Operation) → (operands : Sequences.List Value) →
      operands.length = getArgumentCount op → Value)
    (op : Operation)
    (arguments : ArgumentList Value Operation Variable getArgumentCount
      (getArgumentCount op)) :
    compute getVariableValue computeOperation (operation op arguments) =
      computeOperation op
        (computeArgumentList getVariableValue computeOperation arguments).val
        (computeArgumentList getVariableValue computeOperation arguments).property :=
  rfl

theorem computeArgumentList_empty {Value : Type u} {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (getVariableValue : Variable → Value)
    (computeOperation : (op : Operation) → (operands : Sequences.List Value) →
      operands.length = getArgumentCount op → Value) :
    (computeArgumentList (getArgumentCount := getArgumentCount)
        (count := Numbers.CardinalNatural.Peano.zero)
        getVariableValue computeOperation ArgumentList.empty).val =
      Sequences.List.empty :=
  rfl

theorem computeArgumentList_firstElement {Value : Type u} {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (getVariableValue : Variable → Value)
    (computeOperation : (op : Operation) → (operands : Sequences.List Value) →
      operands.length = getArgumentCount op → Value)
    (t : Tree Value Operation Variable getArgumentCount)
    {count : Numbers.CardinalNatural.Peano}
    (ts : ArgumentList Value Operation Variable getArgumentCount count) :
    (computeArgumentList getVariableValue computeOperation
        (ArgumentList.firstElement t ts)).val =
      Sequences.List.firstElement
        (compute getVariableValue computeOperation t)
        (computeArgumentList getVariableValue computeOperation ts).val :=
  rfl

theorem computeArgumentList_length {Value : Type u} {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (getVariableValue : Variable → Value)
    (computeOperation : (op : Operation) → (operands : Sequences.List Value) →
      operands.length = getArgumentCount op → Value)
    {count : Numbers.CardinalNatural.Peano}
    (arguments : ArgumentList Value Operation Variable getArgumentCount count) :
    (computeArgumentList getVariableValue computeOperation arguments).val.length =
      count :=
  (computeArgumentList getVariableValue computeOperation arguments).property

theorem computeArgumentList_fromList_valueList {Value : Type u}
    {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (getVariableValue : Variable → Value)
    (computeOperation : (op : Operation) → (operands : Sequences.List Value) →
      operands.length = getArgumentCount op → Value) :
    (count : Numbers.CardinalNatural.Peano) →
    (values : Sequences.List Value) →
    (h : (valueList (Variable := Variable) (getArgumentCount := getArgumentCount)
      values).length = count) →
      (computeArgumentList getVariableValue computeOperation
          (ArgumentList.fromList count
            (valueList (Variable := Variable) (getArgumentCount := getArgumentCount)
              values)
            h)).val =
        values
  | Numbers.CardinalNatural.Peano.zero, Sequences.List.empty, _ => rfl
  | Numbers.CardinalNatural.Peano.successor count, Sequences.List.firstElement x xs, h => by
      simp only [valueList, ArgumentList.fromList, computeArgumentList, compute]
      exact congrArg (Sequences.List.firstElement x)
        (computeArgumentList_fromList_valueList getVariableValue computeOperation
          count xs
          (Numbers.CardinalNatural.Peano.successor_injective (by
            rw [← Sequences.List.length_firstElement
              (value (Variable := Variable) (getArgumentCount := getArgumentCount) x)
              (valueList (Variable := Variable) (getArgumentCount := getArgumentCount)
                xs)]
            exact h)))
  | Numbers.CardinalNatural.Peano.zero, Sequences.List.firstElement _ _, h =>
    False.elim (Sequences.List.length_ne_zero_of_ne_empty (by intro heq; cases heq) h)
  | Numbers.CardinalNatural.Peano.successor count, Sequences.List.empty, h =>
    False.elim (Numbers.CardinalNatural.Peano.successor_ne_zero count h.symm)

theorem compute_operationFromValues {Value : Type u} {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (getVariableValue : Variable → Value)
    (computeOperation : (op : Operation) → (operands : Sequences.List Value) →
      operands.length = getArgumentCount op → Value)
    (op : Operation) (values : Sequences.List Value)
    (h : values.length = getArgumentCount op) :
    compute (Variable := Variable) getVariableValue computeOperation
        (operationFromValues (Variable := Variable) op values h) =
      computeOperation op values h := by
  simp only [operationFromValues, compute]
  have hlist :=
    computeArgumentList_fromList_valueList getVariableValue computeOperation
      (getArgumentCount op) values
      (Eq.trans
        (valueList_length (Variable := Variable) (getArgumentCount := getArgumentCount)
          values)
        h)
  simp only [hlist]

theorem compute_binaryOperationFromValues_singleton {Value : Type u}
    {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (getVariableValue : Variable → Value)
    (computeOperation : (op : Operation) → (operands : Sequences.List Value) →
      operands.length = getArgumentCount op → Value)
    (op : Operation) (hArity : getArgumentCount op = Numbers.CardinalNatural.Peano.two)
    (x : Value) :
    compute (Variable := Variable) getVariableValue computeOperation
        (binaryOperationFromValues (Variable := Variable) op hArity
          (Sequences.List.firstElement x Sequences.List.empty)
          (by intro heq; cases heq)) =
      x :=
  rfl

theorem computeArgumentList_twoElements {Value : Type u} {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (getVariableValue : Variable → Value)
    (computeOperation : (op : Operation) → (operands : Sequences.List Value) →
      operands.length = getArgumentCount op → Value)
    (t1 t2 : Tree Value Operation Variable getArgumentCount) :
    (computeArgumentList getVariableValue computeOperation
        (ArgumentList.twoElements t1 t2)).val =
      Sequences.List.firstElement
        (compute getVariableValue computeOperation t1)
        (Sequences.List.firstElement
          (compute getVariableValue computeOperation t2)
          Sequences.List.empty) :=
  rfl

theorem computeArgumentList_eq_rec {Value : Type u} {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (getVariableValue : Variable → Value)
    (computeOperation : (op : Operation) → (operands : Sequences.List Value) →
      operands.length = getArgumentCount op → Value)
    {count1 count2 : Numbers.CardinalNatural.Peano}
    (hcount : count1 = count2)
    (arguments : ArgumentList Value Operation Variable getArgumentCount count1) :
    (computeArgumentList getVariableValue computeOperation
        (hcount ▸ arguments)).val =
      (computeArgumentList getVariableValue computeOperation arguments).val := by
  cases hcount
  rfl

/-- Left fold of a binary function over a value list, matching
`binaryOperationFromValues.go`. -/
def binaryOperationFromValues.goValue {Value : Type u}
    (f : Value → Value → Value) (acc : Value) :
    Sequences.List Value → Value
  | Sequences.List.empty => acc
  | Sequences.List.firstElement x xs =>
      binaryOperationFromValues.goValue f (f acc x) xs

theorem binaryOperationFromValues.goValue_empty {Value : Type u}
    (f : Value → Value → Value) (acc : Value) :
    binaryOperationFromValues.goValue f acc Sequences.List.empty = acc :=
  rfl

theorem binaryOperationFromValues.goValue_firstElement {Value : Type u}
    (f : Value → Value → Value) (acc : Value) (x : Value)
    (xs : Sequences.List Value) :
    binaryOperationFromValues.goValue f acc (Sequences.List.firstElement x xs) =
      binaryOperationFromValues.goValue f (f acc x) xs :=
  rfl

theorem computeOperation_eq_of_eq {Value : Type u} {Operation : Type v}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (computeOperation : (op : Operation) → (operands : Sequences.List Value) →
      operands.length = getArgumentCount op → Value)
    (op : Operation) {l1 l2 : Sequences.List Value}
    (h1 : l1.length = getArgumentCount op) (heq : l1 = l2) :
    computeOperation op l1 h1 = computeOperation op l2 (heq ▸ h1) := by
  cases heq
  rfl

theorem compute_operation_twoElements {Value : Type u} {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (getVariableValue : Variable → Value)
    (computeOperation : (op : Operation) → (operands : Sequences.List Value) →
      operands.length = getArgumentCount op → Value)
    (op : Operation)
    (hArity : getArgumentCount op = Numbers.CardinalNatural.Peano.two)
    (f : Value → Value → Value)
    (hf : ∀ (x y : Value)
        (hlen : (Sequences.List.firstElement x
          (Sequences.List.firstElement y Sequences.List.empty)).length =
            getArgumentCount op),
      computeOperation op
        (Sequences.List.firstElement x
          (Sequences.List.firstElement y Sequences.List.empty)) hlen =
        f x y)
    (t1 t2 : Tree Value Operation Variable getArgumentCount) :
    compute getVariableValue computeOperation
        (operation op (hArity.symm ▸ ArgumentList.twoElements t1 t2)) =
      f (compute getVariableValue computeOperation t1)
        (compute getVariableValue computeOperation t2) := by
  rw [compute_operation]
  have hval :
      (computeArgumentList getVariableValue computeOperation
          (hArity.symm ▸ ArgumentList.twoElements t1 t2)).val =
        Sequences.List.firstElement
          (compute getVariableValue computeOperation t1)
          (Sequences.List.firstElement
            (compute getVariableValue computeOperation t2)
            Sequences.List.empty) := by
    rw [computeArgumentList_eq_rec getVariableValue computeOperation hArity.symm,
      computeArgumentList_twoElements]
  exact
    (computeOperation_eq_of_eq computeOperation op
        (computeArgumentList getVariableValue computeOperation
          (hArity.symm ▸ ArgumentList.twoElements t1 t2)).property
        hval).trans
      (hf _ _ _)

theorem compute_binaryOperationFromValues_go {Value : Type u}
    {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (getVariableValue : Variable → Value)
    (computeOperation : (op : Operation) → (operands : Sequences.List Value) →
      operands.length = getArgumentCount op → Value)
    (op : Operation)
    (hArity : getArgumentCount op = Numbers.CardinalNatural.Peano.two)
    (f : Value → Value → Value)
    (hf : ∀ (x y : Value)
        (hlen : (Sequences.List.firstElement x
          (Sequences.List.firstElement y Sequences.List.empty)).length =
            getArgumentCount op),
      computeOperation op
        (Sequences.List.firstElement x
          (Sequences.List.firstElement y Sequences.List.empty)) hlen =
        f x y)
    (acc : Tree Value Operation Variable getArgumentCount)
    (xs : Sequences.List Value) :
    compute (Variable := Variable) getVariableValue computeOperation
        (binaryOperationFromValues.go (Variable := Variable) op hArity acc xs) =
      binaryOperationFromValues.goValue f
        (compute getVariableValue computeOperation acc) xs := by
  induction xs generalizing acc with
  | empty => rfl
  | firstElement x xs ih =>
      rw [binaryOperationFromValues.go_firstElement,
        binaryOperationFromValues.goValue_firstElement, ih]
      rw [compute_operation_twoElements getVariableValue computeOperation
        op hArity f hf, compute_value]

theorem compute_binaryOperationFromValues_firstElement {Value : Type u}
    {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (getVariableValue : Variable → Value)
    (computeOperation : (op : Operation) → (operands : Sequences.List Value) →
      operands.length = getArgumentCount op → Value)
    (op : Operation)
    (hArity : getArgumentCount op = Numbers.CardinalNatural.Peano.two)
    (f : Value → Value → Value)
    (hf : ∀ (x y : Value)
        (hlen : (Sequences.List.firstElement x
          (Sequences.List.firstElement y Sequences.List.empty)).length =
            getArgumentCount op),
      computeOperation op
        (Sequences.List.firstElement x
          (Sequences.List.firstElement y Sequences.List.empty)) hlen =
        f x y)
    (x : Value) (xs : Sequences.List Value)
    (hne : Sequences.List.firstElement x xs ≠ Sequences.List.empty) :
    compute (Variable := Variable) getVariableValue computeOperation
        (binaryOperationFromValues (Variable := Variable) op hArity
          (Sequences.List.firstElement x xs) hne) =
      binaryOperationFromValues.goValue f x xs := by
  rw [binaryOperationFromValues_eq_go, compute_binaryOperationFromValues_go
    getVariableValue computeOperation op hArity f hf, compute_value]

example {Value : Type} {Operation : Type} {Variable : Type}
    (getArgumentCount : Operation → Numbers.CardinalNatural.Peano)
    (getVariableValue : Variable → Value)
    (computeOperation : (op : Operation) → (operands : Sequences.List Value) →
      operands.length = getArgumentCount op → Value)
    (x : Value) :
    compute (getArgumentCount := getArgumentCount)
        getVariableValue computeOperation (Tree.value x) =
      x :=
  rfl

example :
    compute (getArgumentCount := fun _ => Numbers.CardinalNatural.Peano.zero)
        (fun v : Bool => !v)
        (fun op _ _ => op)
        (Tree.variableLeaf true) =
      false :=
  rfl

example :
    compute (Value := Bool) (Variable := Bool)
        (getArgumentCount := fun _ => Numbers.CardinalNatural.Peano.zero)
        (fun v => v)
        (fun op _ _ => op)
        (operation true ArgumentList.empty) =
      true :=
  rfl

example :
    compute (getArgumentCount := fun _ => Numbers.CardinalNatural.Peano.two)
        (fun v : Bool => v)
        (fun _ operands h =>
          match operands, h with
          | Sequences.List.firstElement x
              (Sequences.List.firstElement y Sequences.List.empty), rfl =>
            x && y)
        (operation true
          (ArgumentList.twoElements (Tree.value true) (Tree.variableLeaf false))) =
      false :=
  rfl

mutual
  /-- Compute the value of a term, or `none` if a variable or operation cannot
  be evaluated. A value leaf is returned as-is. A variable leaf uses
  `tryGetVariable`. An operation node is interpreted with
  `tryComputeOperation` applied to the operation and the values of its
  operands, which have length `getArgumentCount op`. -/
  def tryCompute {Value : Type u} {Operation : Type v} {Variable : Type w}
      {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
      (tryGetVariable : Variable → Option Value)
      (tryComputeOperation : (op : Operation) → (operands : Sequences.List Value) →
        operands.length = getArgumentCount op → Option Value) :
      Tree Value Operation Variable getArgumentCount → Option Value
    | Tree.value x => some x
    | Tree.variableLeaf x => tryGetVariable x
    | Tree.operation op arguments =>
      match tryComputeArgumentList tryGetVariable tryComputeOperation arguments with
      | some operands => tryComputeOperation op operands.val operands.property
      | none => none

  /-- Compute the value of each argument tree, in order, or `none` if any
  argument fails. The resulting list has the same length as the argument list. -/
  def tryComputeArgumentList {Value : Type u} {Operation : Type v} {Variable : Type w}
      {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
      (tryGetVariable : Variable → Option Value)
      (tryComputeOperation : (op : Operation) → (operands : Sequences.List Value) →
        operands.length = getArgumentCount op → Option Value)
      {count : Numbers.CardinalNatural.Peano} :
      ArgumentList Value Operation Variable getArgumentCount count →
        Option { operands : Sequences.List Value // operands.length = count }
    | ArgumentList.empty => some ⟨Sequences.List.empty, rfl⟩
    | ArgumentList.firstElement t ts =>
      match tryCompute tryGetVariable tryComputeOperation t with
      | some v =>
        match tryComputeArgumentList tryGetVariable tryComputeOperation ts with
        | some vs =>
          some ⟨Sequences.List.firstElement v vs.val, by
            rw [Sequences.List.length_firstElement]
            exact congrArg Numbers.CardinalNatural.Peano.successor vs.property⟩
        | none => none
      | none => none
end

theorem tryCompute_value {Value : Type u} {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (tryGetVariable : Variable → Option Value)
    (tryComputeOperation : (op : Operation) → (operands : Sequences.List Value) →
      operands.length = getArgumentCount op → Option Value)
    (x : Value) :
    tryCompute (Variable := Variable) (getArgumentCount := getArgumentCount)
        tryGetVariable tryComputeOperation (Tree.value x) =
      some x :=
  rfl

theorem tryCompute_variableLeaf {Value : Type u} {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (tryGetVariable : Variable → Option Value)
    (tryComputeOperation : (op : Operation) → (operands : Sequences.List Value) →
      operands.length = getArgumentCount op → Option Value)
    (x : Variable) :
    tryCompute (getArgumentCount := getArgumentCount)
        tryGetVariable tryComputeOperation (Tree.variableLeaf x) =
      tryGetVariable x :=
  rfl

theorem tryCompute_operation {Value : Type u} {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (tryGetVariable : Variable → Option Value)
    (tryComputeOperation : (op : Operation) → (operands : Sequences.List Value) →
      operands.length = getArgumentCount op → Option Value)
    (op : Operation)
    (arguments : ArgumentList Value Operation Variable getArgumentCount
      (getArgumentCount op)) :
    tryCompute tryGetVariable tryComputeOperation (Tree.operation op arguments) =
      match tryComputeArgumentList tryGetVariable tryComputeOperation arguments with
      | some operands => tryComputeOperation op operands.val operands.property
      | none => none :=
  rfl

theorem tryComputeArgumentList_empty {Value : Type u} {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (tryGetVariable : Variable → Option Value)
    (tryComputeOperation : (op : Operation) → (operands : Sequences.List Value) →
      operands.length = getArgumentCount op → Option Value) :
    (tryComputeArgumentList (getArgumentCount := getArgumentCount)
        (count := Numbers.CardinalNatural.Peano.zero)
        tryGetVariable tryComputeOperation ArgumentList.empty).map Subtype.val =
      some Sequences.List.empty :=
  rfl

theorem tryComputeArgumentList_firstElement {Value : Type u} {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (tryGetVariable : Variable → Option Value)
    (tryComputeOperation : (op : Operation) → (operands : Sequences.List Value) →
      operands.length = getArgumentCount op → Option Value)
    (t : Tree Value Operation Variable getArgumentCount)
    {count : Numbers.CardinalNatural.Peano}
    (ts : ArgumentList Value Operation Variable getArgumentCount count) :
    (tryComputeArgumentList tryGetVariable tryComputeOperation
        (ArgumentList.firstElement t ts)).map Subtype.val =
      match tryCompute tryGetVariable tryComputeOperation t with
      | some v =>
        (tryComputeArgumentList tryGetVariable tryComputeOperation ts).map
          (fun vs => Sequences.List.firstElement v vs.val)
      | none => none := by
  cases ht : tryCompute tryGetVariable tryComputeOperation t with
  | none =>
    simp only [tryComputeArgumentList, ht, Option.map]
  | some v =>
    cases hts : tryComputeArgumentList tryGetVariable tryComputeOperation ts with
    | none =>
      simp only [tryComputeArgumentList, ht, hts, Option.map]
    | some vs =>
      simp only [tryComputeArgumentList, ht, hts, Option.map]

theorem tryComputeArgumentList_length {Value : Type u} {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (tryGetVariable : Variable → Option Value)
    (tryComputeOperation : (op : Operation) → (operands : Sequences.List Value) →
      operands.length = getArgumentCount op → Option Value)
    {count : Numbers.CardinalNatural.Peano}
    (arguments : ArgumentList Value Operation Variable getArgumentCount count)
    {operands : { operands : Sequences.List Value // operands.length = count }}
    (_h : tryComputeArgumentList tryGetVariable tryComputeOperation arguments =
      some operands) :
    operands.val.length = count :=
  operands.property

theorem tryCompute_operation_eq_some_iff {Value : Type u} {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (tryGetVariable : Variable → Option Value)
    (tryComputeOperation : (op : Operation) → (operands : Sequences.List Value) →
      operands.length = getArgumentCount op → Option Value)
    (op : Operation)
    (arguments : ArgumentList Value Operation Variable getArgumentCount
      (getArgumentCount op))
    (x : Value) :
    tryCompute tryGetVariable tryComputeOperation (Tree.operation op arguments) =
        some x ↔
      ∃ operands,
        tryComputeArgumentList tryGetVariable tryComputeOperation arguments =
          some operands ∧
          tryComputeOperation op operands.val operands.property = some x := by
  dsimp only [tryCompute]
  constructor
  · intro h
    split at h
    · next operands hoperands =>
      exact ⟨operands, hoperands, h⟩
    · next =>
      cases h
  · intro ⟨operands, hoperands, hx⟩
    simp only [hoperands, hx]

mutual
  /-- `compute` is the special case of `tryCompute` in which every variable has a
  value and every operation succeeds: wrap those total interpreters in `some`. -/
  theorem tryCompute_eq_some_compute {Value : Type u} {Operation : Type v}
      {Variable : Type w}
      {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
      (getVariableValue : Variable → Value)
      (computeOperation : (op : Operation) → (operands : Sequences.List Value) →
        operands.length = getArgumentCount op → Value) :
      (t : Tree Value Operation Variable getArgumentCount) →
      tryCompute (fun x => some (getVariableValue x))
          (fun op operands h => some (computeOperation op operands h)) t =
        some (compute getVariableValue computeOperation t)
    | Tree.value x => rfl
    | Tree.variableLeaf x => rfl
    | Tree.operation op arguments => by
        have hargs :=
          tryComputeArgumentList_eq_some_computeArgumentList getVariableValue
            computeOperation arguments
        simp only [tryCompute, hargs, compute]

  theorem tryComputeArgumentList_eq_some_computeArgumentList {Value : Type u}
      {Operation : Type v} {Variable : Type w}
      {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
      (getVariableValue : Variable → Value)
      (computeOperation : (op : Operation) → (operands : Sequences.List Value) →
        operands.length = getArgumentCount op → Value)
      {count : Numbers.CardinalNatural.Peano} :
      (arguments : ArgumentList Value Operation Variable getArgumentCount count) →
      tryComputeArgumentList (fun x => some (getVariableValue x))
          (fun op operands h => some (computeOperation op operands h))
          arguments =
        some (computeArgumentList getVariableValue computeOperation arguments)
    | ArgumentList.empty => rfl
    | ArgumentList.firstElement t ts => by
        have ht := tryCompute_eq_some_compute getVariableValue computeOperation t
        have hts :=
          tryComputeArgumentList_eq_some_computeArgumentList getVariableValue
            computeOperation ts
        simp only [tryComputeArgumentList, ht, hts, computeArgumentList]
end

example :
    tryCompute (Value := Bool) (Operation := Bool) (Variable := Bool)
        (getArgumentCount := fun _ => Numbers.CardinalNatural.Peano.zero)
        (fun v => some (!v)) (fun op _ _ => some op) (Tree.value true) =
      some (compute (getArgumentCount := fun _ => Numbers.CardinalNatural.Peano.zero)
        (fun v : Bool => !v) (fun op _ _ => op) (Tree.value true)) :=
  tryCompute_eq_some_compute (fun v : Bool => !v) (fun op _ _ => op) (Tree.value true)

example :
    tryCompute (Value := Bool) (Operation := Bool) (Variable := Bool)
        (getArgumentCount := fun _ => Numbers.CardinalNatural.Peano.zero)
        (fun _ => none) (fun _ _ _ => none)
        (Tree.value true) =
      some true :=
  rfl

example :
    tryCompute (getArgumentCount := fun _ => Numbers.CardinalNatural.Peano.zero)
        (fun x : Bool => if x then some false else none)
        (fun (_ : Bool) _ _ => none)
        (Tree.variableLeaf true) =
      some false :=
  rfl

example :
    tryCompute (getArgumentCount := fun _ => Numbers.CardinalNatural.Peano.zero)
        (fun x : Bool => if x then some false else none)
        (fun (_ : Bool) _ _ => none)
        (Tree.variableLeaf false) =
      none :=
  rfl

example :
    tryCompute (getArgumentCount := fun _ => Numbers.CardinalNatural.Peano.two)
        (fun _ : Bool => none)
        (fun (_ : Bool) operands h =>
          match operands, h with
          | Sequences.List.firstElement a
              (Sequences.List.firstElement b Sequences.List.empty), rfl =>
            some (a && b))
        (operation true
          (ArgumentList.twoElements (Tree.value true) (Tree.value false))) =
      some false :=
  rfl

example :
    tryCompute (getArgumentCount := fun _ => Numbers.CardinalNatural.Peano.two)
        (fun x : Bool => some x)
        (fun (_ : Bool) operands h =>
          match operands, h with
          | Sequences.List.firstElement a
              (Sequences.List.firstElement b Sequences.List.empty), rfl =>
            some (a && b))
        (operation true
          (ArgumentList.twoElements (Tree.variableLeaf true) (Tree.value true))) =
      some true :=
  rfl

example :
    tryCompute (getArgumentCount := fun _ => Numbers.CardinalNatural.Peano.two)
        (fun _ : Bool => none)
        (fun (_ : Bool) operands h =>
          match operands, h with
          | Sequences.List.firstElement a
              (Sequences.List.firstElement b Sequences.List.empty), rfl =>
            some (a && b))
        (operation true
          (ArgumentList.twoElements (Tree.variableLeaf true) (Tree.value true))) =
      none :=
  rfl

example :
    tryCompute (getArgumentCount := fun _ => Numbers.CardinalNatural.Peano.two)
        (fun _ : Bool => none)
        (fun (_ : Bool) _ _ => none)
        (operation true
          (ArgumentList.twoElements (Tree.value true) (Tree.value false))) =
      none :=
  rfl

example :
    let inner : Tree Bool Bool Bool (fun _ => Numbers.CardinalNatural.Peano.two) :=
      operation true
        (ArgumentList.twoElements (Tree.value true) (Tree.value true))
    let t : Tree Bool Bool Bool (fun _ => Numbers.CardinalNatural.Peano.two) :=
      operation true
        (ArgumentList.twoElements inner (Tree.value false))
    tryCompute (getArgumentCount := fun _ => Numbers.CardinalNatural.Peano.two)
        (fun _ : Bool => none)
        (fun (_ : Bool) operands h =>
          match operands, h with
          | Sequences.List.firstElement a
              (Sequences.List.firstElement b Sequences.List.empty), rfl =>
            some (a && b))
        t =
      some false :=
  rfl

example :
    tryCompute (Value := Bool) (Variable := Bool)
        (getArgumentCount := fun _ => Numbers.CardinalNatural.Peano.zero)
        (fun _ => none)
        (fun op _ _ => some op)
        (operation true ArgumentList.empty) =
      some true :=
  rfl

mutual
  def decidableEq {Value : Type u} {Operation : Type v} {Variable : Type w}
      {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
      [DecidableEq Value] [DecidableEq Operation] [DecidableEq Variable] :
      (t1 t2 : Tree Value Operation Variable getArgumentCount) → Decidable (t1 = t2)
    | Tree.value x, Tree.value y =>
      if h : x = y then
        isTrue (h ▸ rfl)
      else
        isFalse fun heq => by
          cases heq
          exact h rfl
    | Tree.variableLeaf x, Tree.variableLeaf y =>
      if h : x = y then
        isTrue (h ▸ rfl)
      else
        isFalse fun heq => by
          cases heq
          exact h rfl
    | Tree.operation op1 args1, Tree.operation op2 args2 =>
      if hop : op1 = op2 then
        match decidableEqArgumentList (hop ▸ args1) args2 with
        | isTrue hargs =>
          isTrue (by
            cases hop
            cases hargs
            rfl)
        | isFalse hargs =>
          isFalse fun heq => by
            cases hop
            cases heq
            exact hargs rfl
      else
        isFalse fun heq => by
          cases heq
          exact hop rfl
    | Tree.value _, Tree.variableLeaf _ => isFalse fun heq => by cases heq
    | Tree.value _, Tree.operation _ _ => isFalse fun heq => by cases heq
    | Tree.variableLeaf _, Tree.value _ => isFalse fun heq => by cases heq
    | Tree.variableLeaf _, Tree.operation _ _ => isFalse fun heq => by cases heq
    | Tree.operation _ _, Tree.value _ => isFalse fun heq => by cases heq
    | Tree.operation _ _, Tree.variableLeaf _ => isFalse fun heq => by cases heq

  def decidableEqArgumentList {Value : Type u} {Operation : Type v} {Variable : Type w}
      {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
      [DecidableEq Value] [DecidableEq Operation] [DecidableEq Variable]
      {count : Numbers.CardinalNatural.Peano} :
      (args1 args2 : ArgumentList Value Operation Variable getArgumentCount count) → Decidable (args1 = args2)
    | ArgumentList.empty, ArgumentList.empty => isTrue rfl
    | ArgumentList.firstElement t1 ts1, ArgumentList.firstElement t2 ts2 =>
      match decidableEq t1 t2, decidableEqArgumentList ts1 ts2 with
      | isTrue ht, isTrue hts =>
        isTrue (by
          cases ht
          cases hts
          rfl)
      | isFalse ht, _ =>
        isFalse fun heq => by
          cases heq
          exact ht rfl
      | _, isFalse hts =>
        isFalse fun heq => by
          cases heq
          exact hts rfl
end

instance {Value : Type u} {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    [DecidableEq Value] [DecidableEq Operation] [DecidableEq Variable] :
    DecidableEq (Tree Value Operation Variable getArgumentCount) :=
  decidableEq

instance {Value : Type u} {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    [DecidableEq Value] [DecidableEq Operation] [DecidableEq Variable]
    {count : Numbers.CardinalNatural.Peano} :
    DecidableEq (ArgumentList Value Operation Variable getArgumentCount count) :=
  decidableEqArgumentList

mutual
  /-- Two trees are equivalent when corresponding leaves and operation symbols are
  related by `DerivedEquivalence` (setoid `≈` when present, otherwise equality) and
  corresponding argument lists are equivalent elementwise. -/
  inductive Equivalence {Value : Type u} {Operation : Type v} {Variable : Type w}
      {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
      [DerivedEquivalence Value] [DerivedEquivalence Operation] [DerivedEquivalence Variable] :
      Tree Value Operation Variable getArgumentCount → Tree Value Operation Variable getArgumentCount → Prop where
    | value {x y : Value} :
        DerivedEquivalence.relation x y → Equivalence (Tree.value x) (Tree.value y)
    | variableLeaf {x y : Variable} :
        DerivedEquivalence.relation x y →
          Equivalence (Tree.variableLeaf x) (Tree.variableLeaf y)
    | operation {op1 op2 : Operation}
        {args1 : ArgumentList Value Operation Variable getArgumentCount (getArgumentCount op1)}
        {args2 : ArgumentList Value Operation Variable getArgumentCount (getArgumentCount op2)} :
        DerivedEquivalence.relation op1 op2 →
        ArgumentListEquivalence args1 args2 →
        Equivalence (Tree.operation op1 args1) (Tree.operation op2 args2)

  inductive ArgumentListEquivalence {Value : Type u} {Operation : Type v} {Variable : Type w}
      {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
      [DerivedEquivalence Value] [DerivedEquivalence Operation] [DerivedEquivalence Variable] :
      {count1 count2 : Numbers.CardinalNatural.Peano} →
      ArgumentList Value Operation Variable getArgumentCount count1 →
      ArgumentList Value Operation Variable getArgumentCount count2 → Prop where
    | empty : ArgumentListEquivalence ArgumentList.empty ArgumentList.empty
    | firstElement {t1 t2 : Tree Value Operation Variable getArgumentCount}
        {count1 count2 : Numbers.CardinalNatural.Peano}
        {ts1 : ArgumentList Value Operation Variable getArgumentCount count1}
        {ts2 : ArgumentList Value Operation Variable getArgumentCount count2} :
        Equivalence t1 t2 →
        ArgumentListEquivalence ts1 ts2 →
        ArgumentListEquivalence (ArgumentList.firstElement t1 ts1)
          (ArgumentList.firstElement t2 ts2)
end

mutual
  theorem equivalence_reflexive {Value : Type u} {Operation : Type v} {Variable : Type w}
      {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
      [DerivedEquivalence Value] [DerivedEquivalence Operation] [DerivedEquivalence Variable] :
      (t : Tree Value Operation Variable getArgumentCount) → Equivalence t t
    | Tree.value x => Equivalence.value (DerivedEquivalence.reflexive x)
    | Tree.variableLeaf x => Equivalence.variableLeaf (DerivedEquivalence.reflexive x)
    | Tree.operation op args =>
      Equivalence.operation (DerivedEquivalence.reflexive op)
        (argumentListEquivalence_reflexive args)

  theorem argumentListEquivalence_reflexive {Value : Type u} {Operation : Type v} {Variable : Type w}
      {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
      [DerivedEquivalence Value] [DerivedEquivalence Operation] [DerivedEquivalence Variable]
      {count : Numbers.CardinalNatural.Peano} :
      (arguments : ArgumentList Value Operation Variable getArgumentCount count) →
        ArgumentListEquivalence arguments arguments
    | ArgumentList.empty => ArgumentListEquivalence.empty
    | ArgumentList.firstElement t ts =>
      ArgumentListEquivalence.firstElement (equivalence_reflexive t)
        (argumentListEquivalence_reflexive ts)
end

mutual
  theorem equivalence_symmetric {Value : Type u} {Operation : Type v} {Variable : Type w}
      {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
      [DerivedEquivalence Value] [DerivedEquivalence Operation] [DerivedEquivalence Variable]
      {t1 t2 : Tree Value Operation Variable getArgumentCount} :
      Equivalence t1 t2 → Equivalence t2 t1
    | Equivalence.value h => Equivalence.value (DerivedEquivalence.symmetric h)
    | Equivalence.variableLeaf h => Equivalence.variableLeaf (DerivedEquivalence.symmetric h)
    | Equivalence.operation hop hargs =>
      Equivalence.operation (DerivedEquivalence.symmetric hop)
        (argumentListEquivalence_symmetric hargs)

  theorem argumentListEquivalence_symmetric {Value : Type u} {Operation : Type v} {Variable : Type w}
      {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
      [DerivedEquivalence Value] [DerivedEquivalence Operation] [DerivedEquivalence Variable]
      {count1 count2 : Numbers.CardinalNatural.Peano}
      {args1 : ArgumentList Value Operation Variable getArgumentCount count1}
      {args2 : ArgumentList Value Operation Variable getArgumentCount count2} :
      ArgumentListEquivalence args1 args2 → ArgumentListEquivalence args2 args1
    | ArgumentListEquivalence.empty => ArgumentListEquivalence.empty
    | ArgumentListEquivalence.firstElement ht hts =>
      ArgumentListEquivalence.firstElement (equivalence_symmetric ht)
        (argumentListEquivalence_symmetric hts)
end

mutual
  theorem equivalence_transitive {Value : Type u} {Operation : Type v} {Variable : Type w}
      {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
      [DerivedEquivalence Value] [DerivedEquivalence Operation] [DerivedEquivalence Variable]
      {t1 t2 t3 : Tree Value Operation Variable getArgumentCount} :
      Equivalence t1 t2 → Equivalence t2 t3 → Equivalence t1 t3
    | Equivalence.value hxy, Equivalence.value hyz =>
      Equivalence.value (DerivedEquivalence.transitive hxy hyz)
    | Equivalence.variableLeaf hxy, Equivalence.variableLeaf hyz =>
      Equivalence.variableLeaf (DerivedEquivalence.transitive hxy hyz)
    | Equivalence.operation hop hargs, Equivalence.operation hop' hargs' =>
      Equivalence.operation (DerivedEquivalence.transitive hop hop')
        (argumentListEquivalence_transitive hargs hargs')

  theorem argumentListEquivalence_transitive {Value : Type u} {Operation : Type v} {Variable : Type w}
      {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
      [DerivedEquivalence Value] [DerivedEquivalence Operation] [DerivedEquivalence Variable]
      {count1 count2 count3 : Numbers.CardinalNatural.Peano}
      {args1 : ArgumentList Value Operation Variable getArgumentCount count1}
      {args2 : ArgumentList Value Operation Variable getArgumentCount count2}
      {args3 : ArgumentList Value Operation Variable getArgumentCount count3} :
      ArgumentListEquivalence args1 args2 → ArgumentListEquivalence args2 args3 →
        ArgumentListEquivalence args1 args3
    | ArgumentListEquivalence.empty, ArgumentListEquivalence.empty =>
      ArgumentListEquivalence.empty
    | ArgumentListEquivalence.firstElement ht hts,
      ArgumentListEquivalence.firstElement ht' hts' =>
      ArgumentListEquivalence.firstElement (equivalence_transitive ht ht')
        (argumentListEquivalence_transitive hts hts')
end

theorem equivalence_of_eq {Value : Type u} {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    [DerivedEquivalence Value] [DerivedEquivalence Operation] [DerivedEquivalence Variable]
    {t1 t2 : Tree Value Operation Variable getArgumentCount} (h : t1 = t2) :
    Equivalence t1 t2 :=
  h ▸ equivalence_reflexive t1

instance {Value : Type u} {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    [DerivedEquivalence Value] [DerivedEquivalence Operation] [DerivedEquivalence Variable] :
    Setoid (Tree Value Operation Variable getArgumentCount) where
  r := Equivalence
  iseqv := {
    refl := equivalence_reflexive
    symm := equivalence_symmetric
    trans := equivalence_transitive
  }

mutual
  def decidableEquivalence {Value : Type u} {Operation : Type v} {Variable : Type w}
      {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
      [DerivedEquivalence Value] [DerivedEquivalence Operation] [DerivedEquivalence Variable]
      [DecidableRel (DerivedEquivalence.relation (α := Value))]
      [DecidableRel (DerivedEquivalence.relation (α := Operation))]
      [DecidableRel (DerivedEquivalence.relation (α := Variable))] :
      (t1 t2 : Tree Value Operation Variable getArgumentCount) → Decidable (Equivalence t1 t2)
    | Tree.value x, Tree.value y =>
      match ‹DecidableRel (DerivedEquivalence.relation (α := Value))› x y with
      | isTrue h => isTrue (Equivalence.value h)
      | isFalse h => isFalse fun heq => by
          cases heq with
          | value hx => exact h hx
    | Tree.variableLeaf x, Tree.variableLeaf y =>
      match ‹DecidableRel (DerivedEquivalence.relation (α := Variable))› x y with
      | isTrue h => isTrue (Equivalence.variableLeaf h)
      | isFalse h => isFalse fun heq => by
          cases heq with
          | variableLeaf hx => exact h hx
    | Tree.operation op1 args1, Tree.operation op2 args2 =>
      match ‹DecidableRel (DerivedEquivalence.relation (α := Operation))› op1 op2,
          decidableArgumentListEquivalence args1 args2 with
      | isTrue hop, isTrue hargs =>
        isTrue (Equivalence.operation hop hargs)
      | isFalse hop, _ =>
        isFalse fun heq => by
          cases heq with
          | operation hop' _ => exact hop hop'
      | _, isFalse hargs =>
        isFalse fun heq => by
          cases heq with
          | operation _ hargs' => exact hargs hargs'
    | Tree.value _, Tree.variableLeaf _ => isFalse fun heq => by cases heq
    | Tree.value _, Tree.operation _ _ => isFalse fun heq => by cases heq
    | Tree.variableLeaf _, Tree.value _ => isFalse fun heq => by cases heq
    | Tree.variableLeaf _, Tree.operation _ _ => isFalse fun heq => by cases heq
    | Tree.operation _ _, Tree.value _ => isFalse fun heq => by cases heq
    | Tree.operation _ _, Tree.variableLeaf _ => isFalse fun heq => by cases heq

  def decidableArgumentListEquivalence {Value : Type u} {Operation : Type v} {Variable : Type w}
      {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
      [DerivedEquivalence Value] [DerivedEquivalence Operation] [DerivedEquivalence Variable]
      [DecidableRel (DerivedEquivalence.relation (α := Value))]
      [DecidableRel (DerivedEquivalence.relation (α := Operation))]
      [DecidableRel (DerivedEquivalence.relation (α := Variable))]
      {count1 count2 : Numbers.CardinalNatural.Peano} :
      (args1 : ArgumentList Value Operation Variable getArgumentCount count1) →
      (args2 : ArgumentList Value Operation Variable getArgumentCount count2) →
        Decidable (ArgumentListEquivalence args1 args2)
    | ArgumentList.empty, ArgumentList.empty =>
      isTrue ArgumentListEquivalence.empty
    | ArgumentList.empty, ArgumentList.firstElement _ _ =>
      isFalse fun heq => by cases heq
    | ArgumentList.firstElement _ _, ArgumentList.empty =>
      isFalse fun heq => by cases heq
    | ArgumentList.firstElement t1 ts1, ArgumentList.firstElement t2 ts2 =>
      match decidableEquivalence t1 t2, decidableArgumentListEquivalence ts1 ts2 with
      | isTrue ht, isTrue hts =>
        isTrue (ArgumentListEquivalence.firstElement ht hts)
      | isFalse ht, _ =>
        isFalse fun heq => by
          cases heq with
          | firstElement ht' _ => exact ht ht'
      | _, isFalse hts =>
        isFalse fun heq => by
          cases heq with
          | firstElement _ hts' => exact hts hts'
end

instance decidableEquivalenceRel {Value : Type u} {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    [DerivedEquivalence Value] [DerivedEquivalence Operation] [DerivedEquivalence Variable]
    [DecidableRel (DerivedEquivalence.relation (α := Value))]
    [DecidableRel (DerivedEquivalence.relation (α := Operation))]
    [DecidableRel (DerivedEquivalence.relation (α := Variable))]
    (t1 t2 : Tree Value Operation Variable getArgumentCount) :
    Decidable (Equivalence t1 t2) :=
  decidableEquivalence t1 t2

instance decidableHasEquiv {Value : Type u} {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    [DerivedEquivalence Value] [DerivedEquivalence Operation] [DerivedEquivalence Variable]
    [DecidableRel (DerivedEquivalence.relation (α := Value))]
    [DecidableRel (DerivedEquivalence.relation (α := Operation))]
    [DecidableRel (DerivedEquivalence.relation (α := Variable))]
    (t1 t2 : Tree Value Operation Variable getArgumentCount) :
    Decidable (t1 ≈ t2) :=
  decidableEquivalence t1 t2

example : decide ((Tree.value true : Tree Bool Bool Bool fun _ =>
      Numbers.CardinalNatural.Peano.zero) = Tree.value true) = true :=
  rfl

example : decide ((Tree.value true : Tree Bool Bool Bool fun _ =>
      Numbers.CardinalNatural.Peano.zero) = Tree.value false) = false :=
  rfl

example : decide ((Tree.value true : Tree Bool Bool Bool fun _ =>
      Numbers.CardinalNatural.Peano.zero) ≈ Tree.value true) = true :=
  rfl

mutual
  /-- Collect value leaves from a tree built only from operation `op` and
  values. A value leaf is a singleton list. An `op` node concatenates the
  collections of its arguments. Any other operation or a variable yields
  `none`. -/
  def tryCollectOperationValues {Value : Type u} {Operation : Type v}
      {Variable : Type w}
      {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
      [DecidableEq Operation] (op : Operation) :
      Tree Value Operation Variable getArgumentCount →
        Option (Sequences.List Value)
    | value x => some (Sequences.List.firstElement x Sequences.List.empty)
    | variableLeaf _ => none
    | operation op' arguments =>
      if op' = op then
        tryCollectOperationValues.goArgs op arguments
      else
        none

  def tryCollectOperationValues.goArgs {Value : Type u} {Operation : Type v}
      {Variable : Type w}
      {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
      [DecidableEq Operation] (op : Operation)
      {count : Numbers.CardinalNatural.Peano} :
      ArgumentList Value Operation Variable getArgumentCount count →
        Option (Sequences.List Value)
    | ArgumentList.empty => some Sequences.List.empty
    | ArgumentList.firstElement t ts =>
      match tryCollectOperationValues op t with
      | none => none
      | some vs =>
        match tryCollectOperationValues.goArgs op ts with
        | none => none
        | some ws => some (Sequences.List.concatenate vs ws)
end

theorem tryCollectOperationValues_value {Value : Type u} {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    [DecidableEq Operation] (op : Operation) (x : Value) :
    tryCollectOperationValues (Value := Value) (Variable := Variable)
        (getArgumentCount := getArgumentCount) op (value x) =
      some (Sequences.List.firstElement x Sequences.List.empty) :=
  rfl

theorem tryCollectOperationValues_variableLeaf {Value : Type u}
    {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    [DecidableEq Operation] (op : Operation) (x : Variable) :
    tryCollectOperationValues (Value := Value) (Variable := Variable)
        (getArgumentCount := getArgumentCount) op (variableLeaf x) =
      none :=
  rfl

theorem tryCollectOperationValues.goArgs_empty {Value : Type u}
    {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    [DecidableEq Operation] (op : Operation) :
    tryCollectOperationValues.goArgs (Value := Value) (Variable := Variable)
        (getArgumentCount := getArgumentCount)
        (count := Numbers.CardinalNatural.Peano.zero) op ArgumentList.empty =
      some Sequences.List.empty :=
  rfl

theorem tryCollectOperationValues.goArgs_firstElement {Value : Type u}
    {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    [DecidableEq Operation] (op : Operation)
    (t : Tree Value Operation Variable getArgumentCount)
    {count : Numbers.CardinalNatural.Peano}
    (ts : ArgumentList Value Operation Variable getArgumentCount count) :
    tryCollectOperationValues.goArgs (Value := Value) op
        (ArgumentList.firstElement t ts) =
      match tryCollectOperationValues (Value := Value) op t with
      | none => none
      | some vs =>
        match tryCollectOperationValues.goArgs (Value := Value) op ts with
        | none => none
        | some ws => some (Sequences.List.concatenate vs ws) :=
  rfl

/-- The two value operands of a list of trees, when it is exactly two value
leaves. -/
def tryTwoValueLeaves {Value : Type u} {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano} :
    Sequences.List (Tree Value Operation Variable getArgumentCount) →
      Option (Value × Value)
  | Sequences.List.firstElement (value a)
      (Sequences.List.firstElement (value b) Sequences.List.empty) =>
    some (a, b)
  | _ => none

/-- The two value operands of a binary `op` node, when both arguments are
value leaves. -/
def tryBinaryValueOperands {Value : Type u} {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    [DecidableEq Operation] (op : Operation) :
    Tree Value Operation Variable getArgumentCount → Option (Value × Value)
  | operation op' arguments =>
    if op' = op then
      tryTwoValueLeaves (ArgumentList.toList arguments)
    else
      none
  | _ => none

theorem tryBinaryValueOperands_value {Value : Type u} {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    [DecidableEq Operation] (op : Operation) (x : Value) :
    tryBinaryValueOperands (Value := Value) (Variable := Variable)
        (getArgumentCount := getArgumentCount) op (value x) =
      none :=
  rfl

/-- A binary product node whose operands are value leaves `left` and `right`. -/
def productFromValues {Value : Type u} {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    (mul : Operation)
    (hMul : getArgumentCount mul = Numbers.CardinalNatural.Peano.two)
    (left right : Value) :
    Tree Value Operation Variable getArgumentCount :=
  operationFromValues (Variable := Variable) mul
    (Sequences.List.firstElement left
      (Sequences.List.firstElement right Sequences.List.empty))
    (by
      simp only [Sequences.List.length, hMul]
      rfl)

/-- Replace a sum of at least two identical value addends with the product of
the addend and the number of addends. `fromCount` writes that count as a
value. Returns `none` when the term is not a sum of identical addends. -/
def tryReplaceSumWithProduct {Value : Type u} {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    [DecidableEq Value] [DecidableEq Operation] (add mul : Operation)
    (hMul : getArgumentCount mul = Numbers.CardinalNatural.Peano.two)
    (fromCount : Numbers.CardinalNatural.Peano → Value)
    (t : Tree Value Operation Variable getArgumentCount) :
    Option (Tree Value Operation Variable getArgumentCount) :=
  match tryCollectOperationValues add t with
  | none => none
  | some values =>
    match values with
    | Sequences.List.empty => none
    | Sequences.List.firstElement _ Sequences.List.empty => none
    | Sequences.List.firstElement _ (Sequences.List.firstElement _ _) =>
      match Sequences.List.tryRepeatedValue values with
      | none => none
      | some addend =>
        some (productFromValues (Variable := Variable) mul hMul addend
          (fromCount values.length))

/-- Replace a product of two values with the sum of `count` copies of the
first factor, where `count` is `toCount` of the second factor. Returns
`none` when the term is not such a product or the count is zero. -/
def tryReplaceProductWithSumOfFirstFactor {Value : Type u} {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    [DecidableEq Operation] (add mul : Operation)
    (hAdd : getArgumentCount add = Numbers.CardinalNatural.Peano.two)
    (toCount : Value → Option Numbers.CardinalNatural.Peano)
    (t : Tree Value Operation Variable getArgumentCount) :
    Option (Tree Value Operation Variable getArgumentCount) :=
  match tryBinaryValueOperands mul t with
  | none => none
  | some (addend, countValue) =>
    match toCount countValue with
    | none => none
    | some count =>
      if h : count = Numbers.CardinalNatural.Peano.zero then
        none
      else
        some (binaryOperationFromValues (Variable := Variable) add hAdd
          (Sequences.List.repeatValue addend count)
          (Sequences.List.repeatValue_ne_empty addend count h))

/-- Replace a product of two values with the sum of `count` copies of the
second factor, where `count` is `toCount` of the first factor. Returns
`none` when the term is not such a product or the count is zero. -/
def tryReplaceProductWithSumOfSecondFactor {Value : Type u} {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    [DecidableEq Operation] (add mul : Operation)
    (hAdd : getArgumentCount add = Numbers.CardinalNatural.Peano.two)
    (toCount : Value → Option Numbers.CardinalNatural.Peano)
    (t : Tree Value Operation Variable getArgumentCount) :
    Option (Tree Value Operation Variable getArgumentCount) :=
  match tryBinaryValueOperands mul t with
  | none => none
  | some (countValue, addend) =>
    match toCount countValue with
    | none => none
    | some count =>
      if h : count = Numbers.CardinalNatural.Peano.zero then
        none
      else
        some (binaryOperationFromValues (Variable := Variable) add hAdd
          (Sequences.List.repeatValue addend count)
          (Sequences.List.repeatValue_ne_empty addend count h))

theorem tryReplaceSumWithProduct_value {Value : Type u} {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    [DecidableEq Value] [DecidableEq Operation] (add mul : Operation)
    (hMul : getArgumentCount mul = Numbers.CardinalNatural.Peano.two)
    (fromCount : Numbers.CardinalNatural.Peano → Value) (x : Value) :
    tryReplaceSumWithProduct (Value := Value) (Variable := Variable)
        (getArgumentCount := getArgumentCount) add mul hMul fromCount
        (value x) =
      none :=
  rfl

theorem tryReplaceProductWithSumOfFirstFactor_value {Value : Type u}
    {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    [DecidableEq Operation] (add mul : Operation)
    (hAdd : getArgumentCount add = Numbers.CardinalNatural.Peano.two)
    (toCount : Value → Option Numbers.CardinalNatural.Peano) (x : Value) :
    tryReplaceProductWithSumOfFirstFactor (Value := Value) (Variable := Variable)
        (getArgumentCount := getArgumentCount) add mul hAdd toCount
        (value x) =
      none :=
  rfl

theorem tryReplaceProductWithSumOfSecondFactor_value {Value : Type u}
    {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    [DecidableEq Operation] (add mul : Operation)
    (hAdd : getArgumentCount add = Numbers.CardinalNatural.Peano.two)
    (toCount : Value → Option Numbers.CardinalNatural.Peano) (x : Value) :
    tryReplaceProductWithSumOfSecondFactor (Value := Value)
        (Variable := Variable) (getArgumentCount := getArgumentCount)
        add mul hAdd toCount (value x) =
      none :=
  rfl

theorem tryBinaryValueOperands_productFromValues {Value : Type u}
    {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    [DecidableEq Operation] (mul : Operation)
    (hMul : getArgumentCount mul = Numbers.CardinalNatural.Peano.two)
    (left right : Value) :
    tryBinaryValueOperands (Value := Value) (Variable := Variable) mul
        (productFromValues (Variable := Variable) mul hMul left right) =
      some (left, right) := by
  simp only [productFromValues, tryBinaryValueOperands, operationFromValues]
  rw [ArgumentList.fromList_toList]
  simp only [valueList, tryTwoValueLeaves]
  simp

theorem tryReplaceProductWithSumOfFirstFactor_productFromValues
    {Value : Type u} {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    [DecidableEq Operation] (add mul : Operation)
    (hAdd : getArgumentCount add = Numbers.CardinalNatural.Peano.two)
    (hMul : getArgumentCount mul = Numbers.CardinalNatural.Peano.two)
    (toCount : Value → Option Numbers.CardinalNatural.Peano)
    (left right : Value) (count : Numbers.CardinalNatural.Peano)
    (hto : toCount right = some count)
    (hne : count ≠ Numbers.CardinalNatural.Peano.zero) :
    tryReplaceProductWithSumOfFirstFactor (Variable := Variable) add mul hAdd
        toCount (productFromValues (Variable := Variable) mul hMul left right) =
      some (binaryOperationFromValues (Variable := Variable) add hAdd
        (Sequences.List.repeatValue left count)
        (Sequences.List.repeatValue_ne_empty left count hne)) := by
  simp only [tryReplaceProductWithSumOfFirstFactor,
    tryBinaryValueOperands_productFromValues, hto]
  split
  · next hzero => exact False.elim (hne hzero)
  · next => rfl

theorem tryReplaceProductWithSumOfSecondFactor_productFromValues
    {Value : Type u} {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Numbers.CardinalNatural.Peano}
    [DecidableEq Operation] (add mul : Operation)
    (hAdd : getArgumentCount add = Numbers.CardinalNatural.Peano.two)
    (hMul : getArgumentCount mul = Numbers.CardinalNatural.Peano.two)
    (toCount : Value → Option Numbers.CardinalNatural.Peano)
    (left right : Value) (count : Numbers.CardinalNatural.Peano)
    (hto : toCount left = some count)
    (hne : count ≠ Numbers.CardinalNatural.Peano.zero) :
    tryReplaceProductWithSumOfSecondFactor (Variable := Variable) add mul hAdd
        toCount (productFromValues (Variable := Variable) mul hMul left right) =
      some (binaryOperationFromValues (Variable := Variable) add hAdd
        (Sequences.List.repeatValue right count)
        (Sequences.List.repeatValue_ne_empty right count hne)) := by
  simp only [tryReplaceProductWithSumOfSecondFactor,
    tryBinaryValueOperands_productFromValues, hto]
  split
  · next hzero => exact False.elim (hne hzero)
  · next => rfl

example :
    tryReplaceSumWithProduct (Value := Bool) (Variable := Empty)
        (getArgumentCount := fun _ : Bool => Numbers.CardinalNatural.Peano.two)
        false true rfl (fun _ => false)
        (binaryOperationFromValues (Variable := Empty) false rfl
          (Sequences.List.repeatValue true Numbers.CardinalNatural.Peano.two)
          (Sequences.List.repeatValue_ne_empty true
            Numbers.CardinalNatural.Peano.two
            (Numbers.CardinalNatural.Peano.successor_ne_zero
              Numbers.CardinalNatural.Peano.one))) =
      some (productFromValues (Variable := Empty)
        (getArgumentCount := fun _ : Bool => Numbers.CardinalNatural.Peano.two)
        true rfl true false) :=
  rfl

example :
    tryReplaceProductWithSumOfFirstFactor (Value := Bool) (Variable := Empty)
        (getArgumentCount := fun _ : Bool => Numbers.CardinalNatural.Peano.two)
        false true rfl (fun _ => some Numbers.CardinalNatural.Peano.two)
        (productFromValues (Variable := Empty) true rfl true false) =
      some (binaryOperationFromValues (Variable := Empty) false rfl
        (Sequences.List.repeatValue true Numbers.CardinalNatural.Peano.two)
        (Sequences.List.repeatValue_ne_empty true
          Numbers.CardinalNatural.Peano.two
          (Numbers.CardinalNatural.Peano.successor_ne_zero
            Numbers.CardinalNatural.Peano.one))) :=
  rfl

example :
    tryReplaceProductWithSumOfSecondFactor (Value := Bool) (Variable := Empty)
        (getArgumentCount := fun _ : Bool => Numbers.CardinalNatural.Peano.two)
        false true rfl (fun _ => some Numbers.CardinalNatural.Peano.two)
        (productFromValues (Variable := Empty) true rfl false true) =
      some (binaryOperationFromValues (Variable := Empty) false rfl
        (Sequences.List.repeatValue true Numbers.CardinalNatural.Peano.two)
        (Sequences.List.repeatValue_ne_empty true
          Numbers.CardinalNatural.Peano.two
          (Numbers.CardinalNatural.Peano.successor_ne_zero
            Numbers.CardinalNatural.Peano.one))) :=
  rfl

example :
    tryReplaceSumWithProduct (Value := Bool) (Variable := Empty)
        (getArgumentCount := fun _ : Bool => Numbers.CardinalNatural.Peano.two)
        false true rfl (fun _ => false)
        (binaryOperationFromValues (Variable := Empty) false rfl
          (Sequences.List.firstElement true
            (Sequences.List.firstElement false Sequences.List.empty))
          (by intro heq; cases heq)) =
      none :=
  rfl

end Tree

end ZeroMath.Terms.Homogeneous
