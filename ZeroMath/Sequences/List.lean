import ZeroMath.Basic
import ZeroMath.Numbers.CardinalNatural.Peano

namespace ZeroMath.Sequences

inductive List (α : Type u) where
  | empty : List α
  | firstElement : α → List α → List α

namespace List

def HasAtLeastOne {α : Type u} : List α → Prop
  | empty => False
  | firstElement _ _ => True

def length {α : Type u} : List α → ZeroMath.Numbers.CardinalNatural.Peano
  | empty => ZeroMath.Numbers.CardinalNatural.Peano.zero
  | firstElement _ ds => ds.length + ZeroMath.Numbers.CardinalNatural.Peano.successor ZeroMath.Numbers.CardinalNatural.Peano.zero

end List

end ZeroMath.Sequences
