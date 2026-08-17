import ZeroMath.Logic.DerivedEquivalence
import ZeroMath.Sequences.List

namespace ZeroMath.Terms.Homogeneous

mutual
  /-- A homogeneous term tree: value and variable leaves, and operation nodes whose
  number of arguments is given by `argumentCount`. Values have type `α`, operations
  have type `β`, and variables have type `γ`. Each of those types is compared by
  decidable setoid equivalence when a `Setoid` is available, and by decidable
  equality otherwise. -/
  inductive Tree (α : Type u) (β : Type v) (γ : Type w)
      (argumentCount : β → Numbers.CardinalNatural.Peano) where
    /-- A value leaf. -/
    | value : α → Tree α β γ argumentCount
    /-- A variable leaf. Named `variableLeaf` because `variable` is a Lean keyword. -/
    | variableLeaf : γ → Tree α β γ argumentCount
    /-- An operation node with exactly `argumentCount op` argument trees. -/
    | operation (op : β) :
        ArgumentList α β γ argumentCount (argumentCount op) →
        Tree α β γ argumentCount

  /-- Exactly `count` argument trees, matching the operation's `argumentCount`. -/
  inductive ArgumentList (α : Type u) (β : Type v) (γ : Type w)
      (argumentCount : β → Numbers.CardinalNatural.Peano) :
      Numbers.CardinalNatural.Peano → Type (max u v w) where
    | empty : ArgumentList α β γ argumentCount Numbers.CardinalNatural.Peano.zero
    | firstElement {count : Numbers.CardinalNatural.Peano} :
        Tree α β γ argumentCount →
        ArgumentList α β γ argumentCount count →
        ArgumentList α β γ argumentCount count.successor
end

namespace ArgumentList

def toList {α : Type u} {β : Type v} {γ : Type w}
    {argumentCount : β → Numbers.CardinalNatural.Peano}
    {count : Numbers.CardinalNatural.Peano} :
    ArgumentList α β γ argumentCount count →
      Sequences.List (Tree α β γ argumentCount)
  | empty => Sequences.List.empty
  | firstElement t ts => Sequences.List.firstElement t (toList ts)

theorem toList_length {α : Type u} {β : Type v} {γ : Type w}
    {argumentCount : β → Numbers.CardinalNatural.Peano}
    {count : Numbers.CardinalNatural.Peano} :
    (arguments : ArgumentList α β γ argumentCount count) →
      (toList arguments).length = count
  | empty => rfl
  | firstElement _ ts => by
      simp only [toList, Sequences.List.length, toList_length ts,
        Numbers.CardinalNatural.Peano.add_one]

def tryFromList {α : Type u} {β : Type v} {γ : Type w}
    {argumentCount : β → Numbers.CardinalNatural.Peano} :
    (count : Numbers.CardinalNatural.Peano) →
    Sequences.List (Tree α β γ argumentCount) →
      Option (ArgumentList α β γ argumentCount count)
  | Numbers.CardinalNatural.Peano.zero, Sequences.List.empty => some empty
  | Numbers.CardinalNatural.Peano.zero, Sequences.List.firstElement _ _ => none
  | Numbers.CardinalNatural.Peano.successor _, Sequences.List.empty => none
  | Numbers.CardinalNatural.Peano.successor count, Sequences.List.firstElement t ts =>
    match tryFromList count ts with
    | some arguments => some (firstElement t arguments)
    | none => none

theorem tryFromList_eq_some_iff {α : Type u} {β : Type v} {γ : Type w}
    {argumentCount : β → Numbers.CardinalNatural.Peano} :
    {count : Numbers.CardinalNatural.Peano} →
    (arguments : ArgumentList α β γ argumentCount count) →
    (l : Sequences.List (Tree α β γ argumentCount)) →
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

end ArgumentList

namespace Tree

open Logic (DerivedEquivalence)

/-- Build an operation node when `arguments` has exactly `argumentCount op`
elements. -/
def tryOperation {α : Type u} {β : Type v} {γ : Type w}
    {argumentCount : β → Numbers.CardinalNatural.Peano} (op : β)
    (arguments : Sequences.List (Tree α β γ argumentCount)) :
    Option (Tree α β γ argumentCount) :=
  match ArgumentList.tryFromList (argumentCount op) arguments with
  | some typedArguments => some (operation op typedArguments)
  | none => none

theorem tryOperation_eq_some_iff {α : Type u} {β : Type v} {γ : Type w}
    {argumentCount : β → Numbers.CardinalNatural.Peano} (op : β)
    (arguments : Sequences.List (Tree α β γ argumentCount))
    (t : Tree α β γ argumentCount) :
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

example {α : Type} {β : Type} {γ : Type}
    (argumentCount : β → Numbers.CardinalNatural.Peano) (x : α) :
    (Tree.value x : Tree α β γ argumentCount) = Tree.value x := rfl

example {α : Type} {β : Type} {γ : Type}
    (argumentCount : β → Numbers.CardinalNatural.Peano) (x : γ) :
    (Tree.variableLeaf x : Tree α β γ argumentCount) = Tree.variableLeaf x := rfl

example :
    tryOperation (α := Bool) (γ := Bool) (argumentCount := fun _ =>
      Numbers.CardinalNatural.Peano.zero) false Sequences.List.empty =
      some (operation false ArgumentList.empty) :=
  rfl

example :
    tryOperation (α := Bool) (γ := Bool) (argumentCount := fun _ =>
      Numbers.CardinalNatural.Peano.one) false Sequences.List.empty =
      none :=
  rfl

example :
    tryOperation (α := Bool) (γ := Bool)
      (argumentCount := fun _ => Numbers.CardinalNatural.Peano.two) true
      (Sequences.List.firstElement (Tree.value true)
        (Sequences.List.firstElement (Tree.variableLeaf false) Sequences.List.empty)) =
      some (operation true
        (ArgumentList.firstElement (Tree.value true)
          (ArgumentList.firstElement (Tree.variableLeaf false) ArgumentList.empty))) :=
  rfl

mutual
  def decidableEq {α : Type u} {β : Type v} {γ : Type w}
      {argumentCount : β → Numbers.CardinalNatural.Peano}
      [DecidableEq α] [DecidableEq β] [DecidableEq γ] :
      (t1 t2 : Tree α β γ argumentCount) → Decidable (t1 = t2)
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

  def decidableEqArgumentList {α : Type u} {β : Type v} {γ : Type w}
      {argumentCount : β → Numbers.CardinalNatural.Peano}
      [DecidableEq α] [DecidableEq β] [DecidableEq γ]
      {count : Numbers.CardinalNatural.Peano} :
      (args1 args2 : ArgumentList α β γ argumentCount count) → Decidable (args1 = args2)
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

instance {α : Type u} {β : Type v} {γ : Type w}
    {argumentCount : β → Numbers.CardinalNatural.Peano}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] :
    DecidableEq (Tree α β γ argumentCount) :=
  decidableEq

instance {α : Type u} {β : Type v} {γ : Type w}
    {argumentCount : β → Numbers.CardinalNatural.Peano}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {count : Numbers.CardinalNatural.Peano} :
    DecidableEq (ArgumentList α β γ argumentCount count) :=
  decidableEqArgumentList

mutual
  /-- Two trees are equivalent when corresponding leaves and operation symbols are
  related by `DerivedEquivalence` (setoid `≈` when present, otherwise equality) and
  corresponding argument lists are equivalent elementwise. -/
  inductive Equivalence {α : Type u} {β : Type v} {γ : Type w}
      {argumentCount : β → Numbers.CardinalNatural.Peano}
      [DerivedEquivalence α] [DerivedEquivalence β] [DerivedEquivalence γ] :
      Tree α β γ argumentCount → Tree α β γ argumentCount → Prop where
    | value {x y : α} :
        DerivedEquivalence.relation x y → Equivalence (Tree.value x) (Tree.value y)
    | variableLeaf {x y : γ} :
        DerivedEquivalence.relation x y →
          Equivalence (Tree.variableLeaf x) (Tree.variableLeaf y)
    | operation {op1 op2 : β}
        {args1 : ArgumentList α β γ argumentCount (argumentCount op1)}
        {args2 : ArgumentList α β γ argumentCount (argumentCount op2)} :
        DerivedEquivalence.relation op1 op2 →
        ArgumentListEquivalence args1 args2 →
        Equivalence (Tree.operation op1 args1) (Tree.operation op2 args2)

  inductive ArgumentListEquivalence {α : Type u} {β : Type v} {γ : Type w}
      {argumentCount : β → Numbers.CardinalNatural.Peano}
      [DerivedEquivalence α] [DerivedEquivalence β] [DerivedEquivalence γ] :
      {count1 count2 : Numbers.CardinalNatural.Peano} →
      ArgumentList α β γ argumentCount count1 →
      ArgumentList α β γ argumentCount count2 → Prop where
    | empty : ArgumentListEquivalence ArgumentList.empty ArgumentList.empty
    | firstElement {t1 t2 : Tree α β γ argumentCount}
        {count1 count2 : Numbers.CardinalNatural.Peano}
        {ts1 : ArgumentList α β γ argumentCount count1}
        {ts2 : ArgumentList α β γ argumentCount count2} :
        Equivalence t1 t2 →
        ArgumentListEquivalence ts1 ts2 →
        ArgumentListEquivalence (ArgumentList.firstElement t1 ts1)
          (ArgumentList.firstElement t2 ts2)
end

mutual
  theorem equivalence_reflexive {α : Type u} {β : Type v} {γ : Type w}
      {argumentCount : β → Numbers.CardinalNatural.Peano}
      [DerivedEquivalence α] [DerivedEquivalence β] [DerivedEquivalence γ] :
      (t : Tree α β γ argumentCount) → Equivalence t t
    | Tree.value x => Equivalence.value (DerivedEquivalence.reflexive x)
    | Tree.variableLeaf x => Equivalence.variableLeaf (DerivedEquivalence.reflexive x)
    | Tree.operation op args =>
      Equivalence.operation (DerivedEquivalence.reflexive op)
        (argumentListEquivalence_reflexive args)

  theorem argumentListEquivalence_reflexive {α : Type u} {β : Type v} {γ : Type w}
      {argumentCount : β → Numbers.CardinalNatural.Peano}
      [DerivedEquivalence α] [DerivedEquivalence β] [DerivedEquivalence γ]
      {count : Numbers.CardinalNatural.Peano} :
      (arguments : ArgumentList α β γ argumentCount count) →
        ArgumentListEquivalence arguments arguments
    | ArgumentList.empty => ArgumentListEquivalence.empty
    | ArgumentList.firstElement t ts =>
      ArgumentListEquivalence.firstElement (equivalence_reflexive t)
        (argumentListEquivalence_reflexive ts)
end

mutual
  theorem equivalence_symmetric {α : Type u} {β : Type v} {γ : Type w}
      {argumentCount : β → Numbers.CardinalNatural.Peano}
      [DerivedEquivalence α] [DerivedEquivalence β] [DerivedEquivalence γ]
      {t1 t2 : Tree α β γ argumentCount} :
      Equivalence t1 t2 → Equivalence t2 t1
    | Equivalence.value h => Equivalence.value (DerivedEquivalence.symmetric h)
    | Equivalence.variableLeaf h => Equivalence.variableLeaf (DerivedEquivalence.symmetric h)
    | Equivalence.operation hop hargs =>
      Equivalence.operation (DerivedEquivalence.symmetric hop)
        (argumentListEquivalence_symmetric hargs)

  theorem argumentListEquivalence_symmetric {α : Type u} {β : Type v} {γ : Type w}
      {argumentCount : β → Numbers.CardinalNatural.Peano}
      [DerivedEquivalence α] [DerivedEquivalence β] [DerivedEquivalence γ]
      {count1 count2 : Numbers.CardinalNatural.Peano}
      {args1 : ArgumentList α β γ argumentCount count1}
      {args2 : ArgumentList α β γ argumentCount count2} :
      ArgumentListEquivalence args1 args2 → ArgumentListEquivalence args2 args1
    | ArgumentListEquivalence.empty => ArgumentListEquivalence.empty
    | ArgumentListEquivalence.firstElement ht hts =>
      ArgumentListEquivalence.firstElement (equivalence_symmetric ht)
        (argumentListEquivalence_symmetric hts)
end

mutual
  theorem equivalence_transitive {α : Type u} {β : Type v} {γ : Type w}
      {argumentCount : β → Numbers.CardinalNatural.Peano}
      [DerivedEquivalence α] [DerivedEquivalence β] [DerivedEquivalence γ]
      {t1 t2 t3 : Tree α β γ argumentCount} :
      Equivalence t1 t2 → Equivalence t2 t3 → Equivalence t1 t3
    | Equivalence.value hxy, Equivalence.value hyz =>
      Equivalence.value (DerivedEquivalence.transitive hxy hyz)
    | Equivalence.variableLeaf hxy, Equivalence.variableLeaf hyz =>
      Equivalence.variableLeaf (DerivedEquivalence.transitive hxy hyz)
    | Equivalence.operation hop hargs, Equivalence.operation hop' hargs' =>
      Equivalence.operation (DerivedEquivalence.transitive hop hop')
        (argumentListEquivalence_transitive hargs hargs')

  theorem argumentListEquivalence_transitive {α : Type u} {β : Type v} {γ : Type w}
      {argumentCount : β → Numbers.CardinalNatural.Peano}
      [DerivedEquivalence α] [DerivedEquivalence β] [DerivedEquivalence γ]
      {count1 count2 count3 : Numbers.CardinalNatural.Peano}
      {args1 : ArgumentList α β γ argumentCount count1}
      {args2 : ArgumentList α β γ argumentCount count2}
      {args3 : ArgumentList α β γ argumentCount count3} :
      ArgumentListEquivalence args1 args2 → ArgumentListEquivalence args2 args3 →
        ArgumentListEquivalence args1 args3
    | ArgumentListEquivalence.empty, ArgumentListEquivalence.empty =>
      ArgumentListEquivalence.empty
    | ArgumentListEquivalence.firstElement ht hts,
      ArgumentListEquivalence.firstElement ht' hts' =>
      ArgumentListEquivalence.firstElement (equivalence_transitive ht ht')
        (argumentListEquivalence_transitive hts hts')
end

theorem equivalence_of_eq {α : Type u} {β : Type v} {γ : Type w}
    {argumentCount : β → Numbers.CardinalNatural.Peano}
    [DerivedEquivalence α] [DerivedEquivalence β] [DerivedEquivalence γ]
    {t1 t2 : Tree α β γ argumentCount} (h : t1 = t2) :
    Equivalence t1 t2 :=
  h ▸ equivalence_reflexive t1

instance {α : Type u} {β : Type v} {γ : Type w}
    {argumentCount : β → Numbers.CardinalNatural.Peano}
    [DerivedEquivalence α] [DerivedEquivalence β] [DerivedEquivalence γ] :
    Setoid (Tree α β γ argumentCount) where
  r := Equivalence
  iseqv := {
    refl := equivalence_reflexive
    symm := equivalence_symmetric
    trans := equivalence_transitive
  }

mutual
  def decidableEquivalence {α : Type u} {β : Type v} {γ : Type w}
      {argumentCount : β → Numbers.CardinalNatural.Peano}
      [DerivedEquivalence α] [DerivedEquivalence β] [DerivedEquivalence γ]
      [DecidableRel (DerivedEquivalence.relation (α := α))]
      [DecidableRel (DerivedEquivalence.relation (α := β))]
      [DecidableRel (DerivedEquivalence.relation (α := γ))] :
      (t1 t2 : Tree α β γ argumentCount) → Decidable (Equivalence t1 t2)
    | Tree.value x, Tree.value y =>
      match ‹DecidableRel (DerivedEquivalence.relation (α := α))› x y with
      | isTrue h => isTrue (Equivalence.value h)
      | isFalse h => isFalse fun heq => by
          cases heq with
          | value hx => exact h hx
    | Tree.variableLeaf x, Tree.variableLeaf y =>
      match ‹DecidableRel (DerivedEquivalence.relation (α := γ))› x y with
      | isTrue h => isTrue (Equivalence.variableLeaf h)
      | isFalse h => isFalse fun heq => by
          cases heq with
          | variableLeaf hx => exact h hx
    | Tree.operation op1 args1, Tree.operation op2 args2 =>
      match ‹DecidableRel (DerivedEquivalence.relation (α := β))› op1 op2,
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

  def decidableArgumentListEquivalence {α : Type u} {β : Type v} {γ : Type w}
      {argumentCount : β → Numbers.CardinalNatural.Peano}
      [DerivedEquivalence α] [DerivedEquivalence β] [DerivedEquivalence γ]
      [DecidableRel (DerivedEquivalence.relation (α := α))]
      [DecidableRel (DerivedEquivalence.relation (α := β))]
      [DecidableRel (DerivedEquivalence.relation (α := γ))]
      {count1 count2 : Numbers.CardinalNatural.Peano} :
      (args1 : ArgumentList α β γ argumentCount count1) →
      (args2 : ArgumentList α β γ argumentCount count2) →
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

instance decidableEquivalenceRel {α : Type u} {β : Type v} {γ : Type w}
    {argumentCount : β → Numbers.CardinalNatural.Peano}
    [DerivedEquivalence α] [DerivedEquivalence β] [DerivedEquivalence γ]
    [DecidableRel (DerivedEquivalence.relation (α := α))]
    [DecidableRel (DerivedEquivalence.relation (α := β))]
    [DecidableRel (DerivedEquivalence.relation (α := γ))]
    (t1 t2 : Tree α β γ argumentCount) :
    Decidable (Equivalence t1 t2) :=
  decidableEquivalence t1 t2

instance decidableHasEquiv {α : Type u} {β : Type v} {γ : Type w}
    {argumentCount : β → Numbers.CardinalNatural.Peano}
    [DerivedEquivalence α] [DerivedEquivalence β] [DerivedEquivalence γ]
    [DecidableRel (DerivedEquivalence.relation (α := α))]
    [DecidableRel (DerivedEquivalence.relation (α := β))]
    [DecidableRel (DerivedEquivalence.relation (α := γ))]
    (t1 t2 : Tree α β γ argumentCount) :
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

end Tree

end ZeroMath.Terms.Homogeneous
