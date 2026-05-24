import ZeroMath.Basic

namespace ZeroMath.Sequences

inductive List (α : Type u) where
  | empty : List α
  | firstElement : α → List α → List α

namespace List

def HasAtLeastOne {α : Type u} : List α → Prop
  | empty => False
  | firstElement _ _ => True

end List

end ZeroMath.Sequences
