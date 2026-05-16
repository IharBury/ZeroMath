import ZeroMath.Basic

namespace ZeroMath.Sequences

def List := _root_.List

namespace List

def empty {α : Type u} : List α := _root_.List.nil

def firstElement {α : Type u} : α → List α → List α := _root_.List.cons

def HasAtLeastOne {α : Type u} : List α → Prop
  | _root_.List.nil => False
  | _root_.List.cons _ _ => True

end List

end ZeroMath.Sequences
