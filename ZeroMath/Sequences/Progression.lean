import ZeroMath.Numbers.OrdinalNatural.Peano

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

end Progression

end ZeroMath.Sequences
