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

def padAtStart {α : Type u} (l : List α) (paddingValue : α) (n : ZeroMath.Numbers.CardinalNatural.Peano) : List α :=
  match n with
  | ZeroMath.Numbers.CardinalNatural.Peano.zero => l
  | ZeroMath.Numbers.CardinalNatural.Peano.successor n' => padAtStart (.firstElement paddingValue l) paddingValue n'

def padAtStartToSameLength {α : Type u} (l1 l2 : List α) (paddingValue : α) :
  (List α × List α) :=
  let len1 := l1.length
  let len2 := l2.length
  if ZeroMath.Numbers.CardinalNatural.Peano.isLessThan len2 len1 then
    have h_le : len2 ≤ len1 := sorry
    (l1, padAtStart l2 paddingValue (ZeroMath.Numbers.CardinalNatural.Peano.subtract len1 len2 h_le))
  else
    have h_le : len1 ≤ len2 := sorry
    (padAtStart l1 paddingValue (ZeroMath.Numbers.CardinalNatural.Peano.subtract len2 len1 h_le), l2)

end List

end ZeroMath.Sequences
