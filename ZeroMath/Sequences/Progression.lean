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

end Progression

end ZeroMath.Sequences
