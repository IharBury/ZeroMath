namespace ZeroMath.Sequences

/-- A (finite or infinite) progression of a given type, defined by the first
element and a function returning the next element after the given element
(or none if the given element was the last one). -/
structure Progression (α : Type u) where
  first : α
  next : α → Option α

namespace Progression

end Progression

end ZeroMath.Sequences
