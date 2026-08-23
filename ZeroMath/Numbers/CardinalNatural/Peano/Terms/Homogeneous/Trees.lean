import ZeroMath.Numbers.CardinalNatural.Peano.Lists
import ZeroMath.Terms.Homogeneous.Tree

namespace ZeroMath.Numbers.CardinalNatural.Peano.Terms.Homogeneous.Trees

open ZeroMath.Numbers.CardinalNatural (Peano)
open ZeroMath.Terms.Homogeneous.Tree

/-- The sum of `count` copies of `addend` as a homogeneous term under binary
addition. `count` must be nonzero. A single addend is a value leaf; longer
lists nest left-associated as `(... + a) + a`. For `addend = 5` and
`count = 4` this is `((5 + 5) + 5) + 5`. -/
def repeatedAddendsTerm {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Peano} (add : Operation)
    (h : getArgumentCount add = Peano.two) (addend : Peano) (count : Peano)
    (hne : count ≠ Peano.zero) :
    ZeroMath.Terms.Homogeneous.Tree Peano Operation Variable getArgumentCount :=
  binaryOperationFromValues add h (repeatedAddends addend count)
    (repeatedAddends_ne_empty addend count hne)

theorem repeatedAddendsTerm_eq_binaryOperationFromValues {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Peano} (add : Operation)
    (h : getArgumentCount add = Peano.two) (addend : Peano) (count : Peano)
    (hne : count ≠ Peano.zero) :
    repeatedAddendsTerm (Variable := Variable) add h addend count hne =
      binaryOperationFromValues (Variable := Variable) add h
        (repeatedAddends addend count)
        (repeatedAddends_ne_empty addend count hne) :=
  rfl

/-- The product `addend * count` as a homogeneous binary term. -/
def productTerm {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Peano} (mul : Operation)
    (h : getArgumentCount mul = Peano.two) (addend : Peano) (count : Peano) :
    ZeroMath.Terms.Homogeneous.Tree Peano Operation Variable getArgumentCount :=
  operationFromValues (Variable := Variable) mul
    (Sequences.List.firstElement addend
      (Sequences.List.firstElement count Sequences.List.empty))
    (by
      simp only [Sequences.List.length, h]
      rfl)

theorem productTerm_eq_operationFromValues {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Peano} (mul : Operation)
    (h : getArgumentCount mul = Peano.two) (addend : Peano) (count : Peano) :
    productTerm (Variable := Variable) mul h addend count =
      operationFromValues (Variable := Variable) mul
        (Sequences.List.firstElement addend
          (Sequences.List.firstElement count Sequences.List.empty))
        (by
          simp only [Sequences.List.length, h]
          rfl) :=
  rfl

/-- Left-associated addition of Peano numbers, matching
`binaryOperationFromValues.go`. -/
theorem goValue_add (acc : Peano) (xs : Sequences.List Peano) :
    binaryOperationFromValues.goValue (fun a b => a + b) acc xs =
      acc + sum xs := by
  induction xs generalizing acc with
  | empty =>
      rw [binaryOperationFromValues.goValue_empty, sum, add_zero]
  | firstElement x xs ih =>
      rw [binaryOperationFromValues.goValue_firstElement, ih, sum,
        add_associative]

/-- Computing a left-associated addition tree recovers the sum of the value
list. -/
theorem compute_binaryOperationFromValues_add {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Peano} (add : Operation)
    (h : getArgumentCount add = Peano.two)
    (getVariableValue : Variable → Peano)
    (computeOperation : (op : Operation) → (operands : Sequences.List Peano) →
      operands.length = getArgumentCount op → Peano)
    (hAdd : ∀ (x y : Peano)
        (hlen : (Sequences.List.firstElement x
          (Sequences.List.firstElement y Sequences.List.empty)).length =
            getArgumentCount add),
      computeOperation add
        (Sequences.List.firstElement x
          (Sequences.List.firstElement y Sequences.List.empty)) hlen =
        x + y)
    (values : Sequences.List Peano)
    (hne : values ≠ Sequences.List.empty) :
    compute getVariableValue computeOperation
        (binaryOperationFromValues (Variable := Variable) add h values hne) =
      sum values := by
  cases values with
  | empty => exact False.elim (hne rfl)
  | firstElement x xs =>
      rw [compute_binaryOperationFromValues_firstElement
        getVariableValue computeOperation add h (fun a b => a + b) hAdd]
      rw [sum, goValue_add]

/-- Computing the repeated-addends sum term under binary addition recovers
`addend * count`. -/
theorem compute_repeatedAddendsTerm {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Peano} (add : Operation)
    (h : getArgumentCount add = Peano.two)
    (getVariableValue : Variable → Peano)
    (computeOperation : (op : Operation) → (operands : Sequences.List Peano) →
      operands.length = getArgumentCount op → Peano)
    (hAdd : ∀ (x y : Peano)
        (hlen : (Sequences.List.firstElement x
          (Sequences.List.firstElement y Sequences.List.empty)).length =
            getArgumentCount add),
      computeOperation add
        (Sequences.List.firstElement x
          (Sequences.List.firstElement y Sequences.List.empty)) hlen =
        x + y)
    (addend : Peano) (count : Peano) (hne : count ≠ Peano.zero) :
    compute getVariableValue computeOperation
        (repeatedAddendsTerm (Variable := Variable) add h addend count hne) =
      addend * count := by
  rw [repeatedAddendsTerm_eq_binaryOperationFromValues,
    compute_binaryOperationFromValues_add add h getVariableValue
      computeOperation hAdd]
  exact sum_repeatedAddends addend count

/-- Computing the product term under binary multiplication recovers
`addend * count`. -/
theorem compute_productTerm {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Peano} (mul : Operation)
    (h : getArgumentCount mul = Peano.two)
    (getVariableValue : Variable → Peano)
    (computeOperation : (op : Operation) → (operands : Sequences.List Peano) →
      operands.length = getArgumentCount op → Peano)
    (hMul : ∀ (x y : Peano)
        (hlen : (Sequences.List.firstElement x
          (Sequences.List.firstElement y Sequences.List.empty)).length =
            getArgumentCount mul),
      computeOperation mul
        (Sequences.List.firstElement x
          (Sequences.List.firstElement y Sequences.List.empty)) hlen =
        x * y)
    (addend : Peano) (count : Peano) :
    compute getVariableValue computeOperation
        (productTerm (Variable := Variable) mul h addend count) =
      addend * count := by
  rw [productTerm_eq_operationFromValues, compute_operationFromValues, hMul]

/-- The repeated-addends sum term and the product term compute to the same
number. -/
theorem compute_repeatedAddendsTerm_eq_productTerm {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Peano}
    (add mul : Operation)
    (hAddArity : getArgumentCount add = Peano.two)
    (hMulArity : getArgumentCount mul = Peano.two)
    (getVariableValue : Variable → Peano)
    (computeOperation : (op : Operation) → (operands : Sequences.List Peano) →
      operands.length = getArgumentCount op → Peano)
    (hAdd : ∀ (x y : Peano)
        (hlen : (Sequences.List.firstElement x
          (Sequences.List.firstElement y Sequences.List.empty)).length =
            getArgumentCount add),
      computeOperation add
        (Sequences.List.firstElement x
          (Sequences.List.firstElement y Sequences.List.empty)) hlen =
        x + y)
    (hMul : ∀ (x y : Peano)
        (hlen : (Sequences.List.firstElement x
          (Sequences.List.firstElement y Sequences.List.empty)).length =
            getArgumentCount mul),
      computeOperation mul
        (Sequences.List.firstElement x
          (Sequences.List.firstElement y Sequences.List.empty)) hlen =
        x * y)
    (addend : Peano) (count : Peano) (hne : count ≠ Peano.zero) :
    compute getVariableValue computeOperation
        (repeatedAddendsTerm (Variable := Variable) add hAddArity addend count
          hne) =
      compute getVariableValue computeOperation
        (productTerm (Variable := Variable) mul hMulArity addend count) :=
  (compute_repeatedAddendsTerm add hAddArity getVariableValue
      computeOperation hAdd addend count hne).trans
    (compute_productTerm mul hMulArity getVariableValue
      computeOperation hMul addend count).symm

example :
    let addend : Peano := five
    let expected :
        ZeroMath.Terms.Homogeneous.Tree Peano Peano Empty (fun k => k) :=
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

/-- Replace a sum of at least two identical Peano addends with the product of
the addend and the number of addends. Addition and multiplication must both
be binary. -/
def tryReplaceSumWithProduct {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Peano}
    [DecidableEq Operation] (add mul : Operation)
    (hAdd : getArgumentCount add = Peano.two)
    (hMul : getArgumentCount mul = Peano.two) :
    ZeroMath.Terms.Homogeneous.Tree Peano Operation Variable getArgumentCount →
      Option (ZeroMath.Terms.Homogeneous.Tree Peano Operation Variable
        getArgumentCount) :=
  ZeroMath.Terms.Homogeneous.Tree.tryReplaceSumWithProduct add mul hAdd hMul
    id

/-- Replace a product of two Peano numbers with the sum of the second factor
copies of the first factor. -/
def tryReplaceProductWithSumOfFirstFactor {Operation : Type v}
    {Variable : Type w} {getArgumentCount : Operation → Peano}
    [DecidableEq Operation] (add mul : Operation)
    (hAdd : getArgumentCount add = Peano.two) :
    ZeroMath.Terms.Homogeneous.Tree Peano Operation Variable getArgumentCount →
      Option (ZeroMath.Terms.Homogeneous.Tree Peano Operation Variable
        getArgumentCount) :=
  ZeroMath.Terms.Homogeneous.Tree.tryReplaceProductWithSumOfFirstFactor add mul
    hAdd some

/-- Replace a product of two Peano numbers with the sum of the first factor
copies of the second factor. -/
def tryReplaceProductWithSumOfSecondFactor {Operation : Type v}
    {Variable : Type w} {getArgumentCount : Operation → Peano}
    [DecidableEq Operation] (add mul : Operation)
    (hAdd : getArgumentCount add = Peano.two) :
    ZeroMath.Terms.Homogeneous.Tree Peano Operation Variable getArgumentCount →
      Option (ZeroMath.Terms.Homogeneous.Tree Peano Operation Variable
        getArgumentCount) :=
  ZeroMath.Terms.Homogeneous.Tree.tryReplaceProductWithSumOfSecondFactor add mul
    hAdd some

theorem tryReplaceSumWithProduct_eq {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Peano}
    [DecidableEq Operation] (add mul : Operation)
    (hAdd : getArgumentCount add = Peano.two)
    (hMul : getArgumentCount mul = Peano.two)
    (t : ZeroMath.Terms.Homogeneous.Tree Peano Operation Variable
      getArgumentCount) :
    tryReplaceSumWithProduct (Variable := Variable) add mul hAdd hMul t =
      ZeroMath.Terms.Homogeneous.Tree.tryReplaceSumWithProduct
        (Variable := Variable) add mul hAdd hMul id t :=
  rfl

theorem tryReplaceProductWithSumOfFirstFactor_eq {Operation : Type v}
    {Variable : Type w} {getArgumentCount : Operation → Peano}
    [DecidableEq Operation] (add mul : Operation)
    (hAdd : getArgumentCount add = Peano.two)
    (t : ZeroMath.Terms.Homogeneous.Tree Peano Operation Variable
      getArgumentCount) :
    tryReplaceProductWithSumOfFirstFactor (Variable := Variable) add mul hAdd t =
      ZeroMath.Terms.Homogeneous.Tree.tryReplaceProductWithSumOfFirstFactor
        (Variable := Variable) add mul hAdd some t :=
  rfl

theorem tryReplaceProductWithSumOfSecondFactor_eq {Operation : Type v}
    {Variable : Type w} {getArgumentCount : Operation → Peano}
    [DecidableEq Operation] (add mul : Operation)
    (hAdd : getArgumentCount add = Peano.two)
    (t : ZeroMath.Terms.Homogeneous.Tree Peano Operation Variable
      getArgumentCount) :
    tryReplaceProductWithSumOfSecondFactor (Variable := Variable) add mul hAdd
        t =
      ZeroMath.Terms.Homogeneous.Tree.tryReplaceProductWithSumOfSecondFactor
        (Variable := Variable) add mul hAdd some t :=
  rfl

/-- Computing a tree of binary additions recovers the sum of the collected
addends. -/
theorem compute_of_tryCollectOperationValues {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Peano}
    [DecidableEq Operation] (add : Operation)
    (hAddArity : getArgumentCount add = Peano.two)
    (getVariableValue : Variable → Peano)
    (computeOperation : (op : Operation) →
      (operands : Sequences.List Peano) →
      operands.length = getArgumentCount op → Peano)
    (hAdd : ∀ (x y : Peano)
        (hlen : (Sequences.List.firstElement x
          (Sequences.List.firstElement y Sequences.List.empty)).length =
            getArgumentCount add),
      computeOperation add
        (Sequences.List.firstElement x
          (Sequences.List.firstElement y Sequences.List.empty)) hlen =
        x + y)
    (t : ZeroMath.Terms.Homogeneous.Tree Peano Operation Variable
      getArgumentCount)
    (values : Sequences.List Peano)
    (h : tryCollectOperationValues add t = some values) :
    compute getVariableValue computeOperation t = sum values :=
  match t with
  | value x => by
    simp only [tryCollectOperationValues] at h
    cases h
    simp only [compute, sum, add_zero]
  | variableLeaf _ => by
    simp only [tryCollectOperationValues] at h
    cases h
  | operation op' arguments => by
    simp only [tryCollectOperationValues] at h
    split at h
    · next hop =>
      have hArity : getArgumentCount op' = Peano.two :=
        hop ▸ hAddArity
      have hgo :
          tryCollectOperationValues.goArgs add (hArity ▸ arguments) =
            some values := by
        rw [tryCollectOperationValues.goArgs_eq_rec add hArity arguments]
        exact h
      have hargs := ArgumentList.eq_twoElements_twoTrees (hArity ▸ arguments)
      let t1 := (ArgumentList.twoTrees (hArity ▸ arguments)).1
      let t2 := (ArgumentList.twoTrees (hArity ▸ arguments)).2
      have hgo' :
          tryCollectOperationValues.goArgs add
              (ArgumentList.twoElements t1 t2) = some values :=
        hargs ▸ hgo
      rw [tryCollectOperationValues.goArgs_twoElements] at hgo'
      cases h1 : tryCollectOperationValues add t1 with
      | none =>
        simp only [h1] at hgo'
        cases hgo'
      | some vs =>
        cases h2 : tryCollectOperationValues add t2 with
        | none =>
          simp only [h1, h2] at hgo'
          cases hgo'
        | some ws =>
          simp only [h1, h2] at hgo'
          cases hgo'
          have hlt1 : treeWeight t1 < treeWeight (operation op' arguments) := by
            rw [treeWeight_operation,
              ← argumentListWeight_eq_rec hArity arguments]
            refine Nat.lt_trans ?_
              (Nat.lt_add_of_pos_left (Nat.succ_pos 0))
            have :=
              treeWeight_fst_lt_argumentListWeight_twoElements t1 t2
            rw [← hargs] at this
            exact this
          have hlt2 : treeWeight t2 < treeWeight (operation op' arguments) := by
            rw [treeWeight_operation,
              ← argumentListWeight_eq_rec hArity arguments]
            refine Nat.lt_trans ?_
              (Nat.lt_add_of_pos_left (Nat.succ_pos 0))
            have :=
              treeWeight_snd_lt_argumentListWeight_twoElements t1 t2
            rw [← hargs] at this
            exact this
          have ht1 :=
            compute_of_tryCollectOperationValues add hAddArity
              getVariableValue computeOperation hAdd t1 vs h1
          have ht2 :=
            compute_of_tryCollectOperationValues add hAddArity
              getVariableValue computeOperation hAdd t2 ws h2
          cases hop
          rw [compute_operation]
          have hvals :
              (computeArgumentList getVariableValue computeOperation
                  (hArity ▸ arguments)).val =
                Sequences.List.firstElement
                  (compute getVariableValue computeOperation t1)
                  (Sequences.List.firstElement
                    (compute getVariableValue computeOperation t2)
                    Sequences.List.empty) := by
            rw [hargs, computeArgumentList_twoElements]
          have hvals0 :
              (computeArgumentList getVariableValue computeOperation
                  arguments).val =
                Sequences.List.firstElement
                  (compute getVariableValue computeOperation t1)
                  (Sequences.List.firstElement
                    (compute getVariableValue computeOperation t2)
                    Sequences.List.empty) := by
            rw [← computeArgumentList_eq_rec getVariableValue computeOperation
              hArity arguments]
            exact hvals
          rw [computeOperation_eq_of_eq computeOperation add
              (computeArgumentList getVariableValue computeOperation
                arguments).property
              hvals0, hAdd, ht1, ht2, sum_concatenate]
    · next => cases h
termination_by treeWeight t

/-- A successful sum-to-product rewrite computes to the same number. -/
theorem compute_tryReplaceSumWithProduct {Operation : Type v}
    {Variable : Type w}
    {getArgumentCount : Operation → Peano}
    [DecidableEq Operation] (add mul : Operation)
    (hAddArity : getArgumentCount add = Peano.two)
    (hMulArity : getArgumentCount mul = Peano.two)
    (getVariableValue : Variable → Peano)
    (computeOperation : (op : Operation) → (operands : Sequences.List Peano) →
      operands.length = getArgumentCount op → Peano)
    (hAdd : ∀ (x y : Peano)
        (hlen : (Sequences.List.firstElement x
          (Sequences.List.firstElement y Sequences.List.empty)).length =
            getArgumentCount add),
      computeOperation add
        (Sequences.List.firstElement x
          (Sequences.List.firstElement y Sequences.List.empty)) hlen =
        x + y)
    (hMul : ∀ (x y : Peano)
        (hlen : (Sequences.List.firstElement x
          (Sequences.List.firstElement y Sequences.List.empty)).length =
            getArgumentCount mul),
      computeOperation mul
        (Sequences.List.firstElement x
          (Sequences.List.firstElement y Sequences.List.empty)) hlen =
        x * y)
    (t t' : ZeroMath.Terms.Homogeneous.Tree Peano Operation Variable
      getArgumentCount)
    (h : tryReplaceSumWithProduct (Variable := Variable) add mul hAddArity
      hMulArity t = some t') :
    compute getVariableValue computeOperation t =
      compute getVariableValue computeOperation t' := by
  simp only [tryReplaceSumWithProduct] at h
  unfold ZeroMath.Terms.Homogeneous.Tree.tryReplaceSumWithProduct at h
  split at h
  · next =>
    cases hcol : tryCollectOperationValues add t with
    | none =>
      simp only [hcol] at h
      cases h
    | some values =>
      simp only [hcol] at h
      match values with
      | Sequences.List.empty =>
        cases h
      | Sequences.List.firstElement _ Sequences.List.empty =>
        cases h
      | Sequences.List.firstElement x
          (Sequences.List.firstElement y ys) =>
        cases htry : Sequences.List.tryRepeatedValue
            (Sequences.List.firstElement x
              (Sequences.List.firstElement y ys)) with
        | none =>
          simp only [htry] at h
          cases h
        | some addend =>
          simp only [htry] at h
          cases h
          rw [compute_productFromValues getVariableValue computeOperation mul
            hMulArity (fun a b => a * b) hMul]
          have hsum :=
            compute_of_tryCollectOperationValues add hAddArity
              getVariableValue computeOperation hAdd t
              (Sequences.List.firstElement x
                (Sequences.List.firstElement y ys)) hcol
          rw [hsum]
          have hall :=
            (Sequences.List.tryRepeatedValue_eq_some_iff addend
              (Sequences.List.firstElement x
                (Sequences.List.firstElement y ys))).mp htry
          exact sum_eq_multiply_of_AllElements addend _ hall.2
  · next hne => exact False.elim (hne hAddArity)

/-- A successful product-to-sum rewrite on the first factor computes to the
same number. -/
theorem compute_tryReplaceProductWithSumOfFirstFactor
    {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Peano}
    [DecidableEq Operation] (add mul : Operation)
    (hAddArity : getArgumentCount add = Peano.two)
    (getVariableValue : Variable → Peano)
    (computeOperation : (op : Operation) → (operands : Sequences.List Peano) →
      operands.length = getArgumentCount op → Peano)
    (hAdd : ∀ (x y : Peano)
        (hlen : (Sequences.List.firstElement x
          (Sequences.List.firstElement y Sequences.List.empty)).length =
            getArgumentCount add),
      computeOperation add
        (Sequences.List.firstElement x
          (Sequences.List.firstElement y Sequences.List.empty)) hlen =
        x + y)
    (hMul : ∀ (x y : Peano)
        (hlen : (Sequences.List.firstElement x
          (Sequences.List.firstElement y Sequences.List.empty)).length =
            getArgumentCount mul),
      computeOperation mul
        (Sequences.List.firstElement x
          (Sequences.List.firstElement y Sequences.List.empty)) hlen =
        x * y)
    (t t' : ZeroMath.Terms.Homogeneous.Tree Peano Operation Variable
      getArgumentCount)
    (h : tryReplaceProductWithSumOfFirstFactor (Variable := Variable) add mul
      hAddArity t = some t') :
    compute getVariableValue computeOperation t =
      compute getVariableValue computeOperation t' := by
  simp only [tryReplaceProductWithSumOfFirstFactor] at h
  unfold ZeroMath.Terms.Homogeneous.Tree.tryReplaceProductWithSumOfFirstFactor
    at h
  cases hbin : tryBinaryValueOperands mul t with
  | none =>
    simp only [hbin] at h
    cases h
  | some pair =>
    obtain ⟨addend, countValue⟩ := pair
    simp only [hbin] at h
    split at h
    · next => cases h
    · next hne =>
      cases h
      rw [compute_of_tryBinaryValueOperands getVariableValue computeOperation
        mul (fun a b => a * b) hMul t addend countValue hbin]
      rw [compute_binaryOperationFromValues_add add hAddArity
        getVariableValue computeOperation hAdd
        (Sequences.List.repeatValue addend countValue)
        (Sequences.List.repeatValue_ne_empty addend countValue hne)]
      exact (sum_repeatedAddends addend countValue).symm

/-- A successful product-to-sum rewrite on the second factor computes to the
same number. -/
theorem compute_tryReplaceProductWithSumOfSecondFactor
    {Operation : Type v} {Variable : Type w}
    {getArgumentCount : Operation → Peano}
    [DecidableEq Operation] (add mul : Operation)
    (hAddArity : getArgumentCount add = Peano.two)
    (getVariableValue : Variable → Peano)
    (computeOperation : (op : Operation) → (operands : Sequences.List Peano) →
      operands.length = getArgumentCount op → Peano)
    (hAdd : ∀ (x y : Peano)
        (hlen : (Sequences.List.firstElement x
          (Sequences.List.firstElement y Sequences.List.empty)).length =
            getArgumentCount add),
      computeOperation add
        (Sequences.List.firstElement x
          (Sequences.List.firstElement y Sequences.List.empty)) hlen =
        x + y)
    (hMul : ∀ (x y : Peano)
        (hlen : (Sequences.List.firstElement x
          (Sequences.List.firstElement y Sequences.List.empty)).length =
            getArgumentCount mul),
      computeOperation mul
        (Sequences.List.firstElement x
          (Sequences.List.firstElement y Sequences.List.empty)) hlen =
        x * y)
    (t t' : ZeroMath.Terms.Homogeneous.Tree Peano Operation Variable
      getArgumentCount)
    (h : tryReplaceProductWithSumOfSecondFactor (Variable := Variable) add mul
      hAddArity t = some t') :
    compute getVariableValue computeOperation t =
      compute getVariableValue computeOperation t' := by
  simp only [tryReplaceProductWithSumOfSecondFactor] at h
  unfold ZeroMath.Terms.Homogeneous.Tree.tryReplaceProductWithSumOfSecondFactor
    at h
  cases hbin : tryBinaryValueOperands mul t with
  | none =>
    simp only [hbin] at h
    cases h
  | some pair =>
    obtain ⟨countValue, addend⟩ := pair
    simp only [hbin] at h
    split at h
    · next => cases h
    · next hne =>
      cases h
      rw [compute_of_tryBinaryValueOperands getVariableValue computeOperation
        mul (fun a b => a * b) hMul t countValue addend hbin]
      rw [compute_binaryOperationFromValues_add add hAddArity
        getVariableValue computeOperation hAdd
        (Sequences.List.repeatValue addend countValue)
        (Sequences.List.repeatValue_ne_empty addend countValue hne)]
      rw [show Sequences.List.repeatValue addend countValue =
          repeatedAddends addend countValue from rfl,
        sum_repeatedAddends, multiply_commutative]

example :
    let addend : Peano := five
    tryReplaceSumWithProduct (Variable := Empty)
        (getArgumentCount := fun _ : Bool => Peano.two) false true rfl rfl
        (repeatedAddendsTerm (Variable := Empty)
          (getArgumentCount := fun _ : Bool => Peano.two) false rfl addend
          Peano.two (Peano.successor_ne_zero Peano.one)) =
      some (productTerm (Variable := Empty)
        (getArgumentCount := fun _ : Bool => Peano.two) true rfl addend
        Peano.two) :=
  rfl

example :
    let addend : Peano := five
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
    let addend : Peano := two
    tryReplaceProductWithSumOfSecondFactor (Variable := Empty)
        (getArgumentCount := fun _ : Bool => Peano.two) false true rfl
        (productTerm (Variable := Empty)
          (getArgumentCount := fun _ : Bool => Peano.two) true rfl addend
          Peano.three) =
      some (repeatedAddendsTerm (Variable := Empty)
        (getArgumentCount := fun _ : Bool => Peano.two) false rfl
        Peano.three addend (Peano.successor_ne_zero Peano.one)) :=
  rfl

end ZeroMath.Numbers.CardinalNatural.Peano.Terms.Homogeneous.Trees
