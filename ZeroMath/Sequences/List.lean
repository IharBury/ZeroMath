import ZeroMath.Numbers.CardinalNatural.Peano

namespace ZeroMath.Sequences

inductive List (α : Type u) where
  | empty : List α
  | firstElement : α → List α → List α

namespace List

def HasAtLeastOne {α : Type u} : List α → Prop
  | empty => False
  | firstElement _ _ => True

def length {α : Type u} : List α → Numbers.CardinalNatural.Peano
  | empty => Numbers.CardinalNatural.Peano.zero
  | firstElement _ ds => ds.length + Numbers.CardinalNatural.Peano.one

def padAtStart {α : Type u} (l : List α) (paddingValue : α) (n : Numbers.CardinalNatural.Peano) : List α :=
  match n with
  | Numbers.CardinalNatural.Peano.zero => l
  | Numbers.CardinalNatural.Peano.successor n' => padAtStart (.firstElement paddingValue l) paddingValue n'

def padAtStartToSameLength {α : Type u} (l1 l2 : List α) (paddingValue : α) :
  (List α × List α) :=
  let len1 := l1.length
  let len2 := l2.length
  match h : ZeroMath.Numbers.CardinalNatural.Peano.isLessThan len2 len1 with
  | true =>
    have h_le : len2 ≤ len1 := Numbers.CardinalNatural.Peano.isLessThan_true_implies_le h
    (l1, padAtStart l2 paddingValue (Numbers.CardinalNatural.Peano.subtract len1 len2 h_le))
  | false =>
    have h_le : len1 ≤ len2 := Numbers.CardinalNatural.Peano.isLessThan_false_implies_le h
    (padAtStart l1 paddingValue (Numbers.CardinalNatural.Peano.subtract len2 len1 h_le), l2)

inductive SameLength {α : Type u} : List α → List α → Prop where
  | empty : SameLength empty empty
  | firstElement {da db : α} {das dbs : List α} :
      SameLength das dbs → SameLength (firstElement da das) (firstElement db dbs)

theorem sameLength_of_length_eq {α : Type u} {a b : Sequences.List α}
  (h : a.length = b.length) : SameLength a b := by
  induction a generalizing b with
  | empty =>
    cases b with
    | empty => exact SameLength.empty
    | firstElement _ _ =>
      unfold length at h
      cases h
  | firstElement _ das ih =>
    cases b with
    | empty =>
      unfold length at h
      cases h
    | firstElement _ dbs =>
      apply SameLength.firstElement
      apply ih
      unfold length at h
      exact Numbers.CardinalNatural.Peano.add_right_cancel Numbers.CardinalNatural.Peano.one _ _ h

theorem padAtStart_length {α : Type u} (l : Sequences.List α)
  (paddingValue : α) (n : Numbers.CardinalNatural.Peano) :
  length (padAtStart l paddingValue n) = length l + n := by
  induction n generalizing l with
  | zero => rfl
  | successor n' ih =>
    unfold padAtStart
    rw [ih]
    change (length l + Numbers.CardinalNatural.Peano.one) + n' = length l + n'.successor
    rw [Numbers.CardinalNatural.Peano.add_associative]
    have h_one_add : Numbers.CardinalNatural.Peano.one + n' = n'.successor := by
      rw [Numbers.CardinalNatural.Peano.one, Numbers.CardinalNatural.Peano.successor_add, Numbers.CardinalNatural.Peano.zero_add]
    rw [h_one_add]

theorem padAtStartToSameLength_sameLength {α : Type u} (a b : Sequences.List α) (paddingValue : α) :
  Sequences.List.SameLength (Sequences.List.padAtStartToSameLength a b paddingValue).1
    (Sequences.List.padAtStartToSameLength a b paddingValue).2 := by
  unfold Sequences.List.padAtStartToSameLength
  dsimp only
  split
  · next h_less =>
    apply Sequences.List.sameLength_of_length_eq
    dsimp only
    have h_le : Sequences.List.length b ≤ Sequences.List.length a := Numbers.CardinalNatural.Peano.isLessThan_true_implies_le h_less
    rw [padAtStart_length]
    have h_cancel := Numbers.CardinalNatural.Peano.subtract_add_cancel (Sequences.List.length a) (Sequences.List.length b) h_le
    rw [Numbers.CardinalNatural.Peano.add_commutative]
    exact h_cancel.symm
  · next h_less =>
    apply Sequences.List.sameLength_of_length_eq
    dsimp only
    have h_le : Sequences.List.length a ≤ Sequences.List.length b := Numbers.CardinalNatural.Peano.isLessThan_false_implies_le h_less
    rw [padAtStart_length]
    have h_cancel := Numbers.CardinalNatural.Peano.subtract_add_cancel (Sequences.List.length b) (Sequences.List.length a) h_le
    rw [Numbers.CardinalNatural.Peano.add_commutative]
    exact h_cancel

end List

end ZeroMath.Sequences
