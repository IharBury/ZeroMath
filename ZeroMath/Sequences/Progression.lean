import ZeroMath.Numbers.CardinalNatural.Peano

namespace ZeroMath.Sequences

/-- A (possibly empty, finite, or infinite) progression of a given type, defined
by an optional first element (`none` for the empty progression) and a function
returning the next element after the given element (or none if the given
element was the last one). -/
structure Progression (α : Type u) where
  first : Option α
  next : α → Option α

namespace Progression

/-- The empty progression: no first element, and `next` never yields a value. -/
def empty {α : Type u} : Progression α where
  first := none
  next := fun _ => none

/-- The element at the given positive ordinal index, or `none` if the index is
out of bounds. The first element has index `one`. -/
def tryGetElement {α : Type u} (index : Numbers.OrdinalNatural.Peano)
    (p : Progression α) : Option α :=
  match index with
  | Numbers.OrdinalNatural.Peano.one => p.first
  | Numbers.OrdinalNatural.Peano.successor n =>
    match tryGetElement n p with
    | none => none
    | some x => p.next x

/-- A progression is finite when there is some positive ordinal index at which
`tryGetElement` returns `none`. -/
def Finite {α : Type u} (p : Progression α) : Prop :=
  ∃ (index : Numbers.OrdinalNatural.Peano), tryGetElement index p = none

/-- A progression is infinite when it is not finite — that is, when
`tryGetElement` never returns `none`. -/
def Infinite {α : Type u} (p : Progression α) : Prop :=
  ¬ Finite p

/-- A progression `p` has length `n` when the least positive ordinal index at
which `tryGetElement` returns `none` is `n` plus one. -/
def Length {α : Type u} (p : Progression α) (n : Numbers.CardinalNatural.Peano) :
    Prop :=
  Numbers.CardinalNatural.Peano.Minimal n.successor fun k =>
    ∃ (hk : k ≠ Numbers.CardinalNatural.Peano.zero),
      tryGetElement (Numbers.CardinalNatural.Peano.toOrdinal k hk) p = none

/-- The length of a finite progression: the number of elements before
`tryGetElement` first returns `none`. -/
noncomputable def getLength {α : Type u} (p : Progression α) (h : Finite p) :
    Numbers.CardinalNatural.Peano :=
  let rec aux : Option α → Numbers.CardinalNatural.Peano → Numbers.CardinalNatural.Peano
    | none, _ => Numbers.CardinalNatural.Peano.zero
    | some _, Numbers.CardinalNatural.Peano.zero =>
        Numbers.CardinalNatural.Peano.zero
    | some x, Numbers.CardinalNatural.Peano.successor fuel =>
        Numbers.CardinalNatural.Peano.successor (aux (p.next x) fuel)
  aux p.first
    (Numbers.CardinalNatural.Peano.fromOrdinal (Classical.choose h))

/-- The element relation used by `Equivalence`: setoid `≈` when a `Setoid` is
available, and equality otherwise. -/
class ElementRel (α : Type u) where
  Rel : α → α → Prop

instance (priority := low) (α : Type u) : ElementRel α where
  Rel := Eq

instance {α : Type u} [Setoid α] : ElementRel α where
  Rel := (· ≈ ·)

/-- Two progressions are equivalent when, for every positive ordinal index, the
results of `tryGetElement` are equivalent — via the element setoid when one
exists, and via equality otherwise. -/
def Equivalence {α : Type u} [ElementRel α] (p q : Progression α) : Prop :=
  ∀ (index : Numbers.OrdinalNatural.Peano),
    Option.Rel ElementRel.Rel (tryGetElement index p) (tryGetElement index q)

instance {α : Type u} [ElementRel α] : HasEquiv (Progression α) where
  Equiv := Equivalence

end Progression

end ZeroMath.Sequences
