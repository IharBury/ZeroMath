import ZeroMath.Numbers.CardinalNatural.Peano

namespace ZeroMath.Sequences

inductive List (α : Type u) where
  | empty : List α
  | firstElement : α → List α → List α

namespace List

inductive AnyElement {α : Type u} (p : α → Prop) : List α → Prop where
  | first d ds : p d → AnyElement p (firstElement d ds)
  | notFirst d ds : AnyElement p ds → AnyElement p (firstElement d ds)

def anyElement {α : Type u} (p : α → Bool) (a : List α) : Bool :=
  match a with
  | empty => false
  | firstElement d ds =>
    if p d then
      true
    else
      anyElement p ds

def isEmpty {α : Type u} : List α → Bool
  | empty => true
  | firstElement _ _ => false

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

theorem padAtStart_zero {α : Type u} (l : List α) (paddingValue : α) :
  padAtStart l paddingValue Numbers.CardinalNatural.Peano.zero = l := by
  rfl

theorem padAtStart_anyElement {α : Type u} {p : α → Prop} {l : List α}
  (h : AnyElement p l) (paddingValue : α) (n : Numbers.CardinalNatural.Peano) :
  AnyElement p (padAtStart l paddingValue n) := by
  induction n generalizing l with
  | zero =>
      exact h
  | successor n' ih =>
      unfold padAtStart
      exact ih (AnyElement.notFirst paddingValue l h)

theorem padAtStartToSameLength_commutative {α : Type u} (a b : List α) (paddingValue : α) :
  padAtStartToSameLength b a paddingValue =
    ((padAtStartToSameLength a b paddingValue).2, (padAtStartToSameLength a b paddingValue).1) := by
  unfold padAtStartToSameLength
  dsimp only
  split
  · next h_a_lt_b =>
    split
    · next h_b_lt_a =>
      have hlt_ab := (Numbers.CardinalNatural.Peano.isLessThan_eq_true_iff_lt _ _).mp h_a_lt_b
      have hlt_ba := (Numbers.CardinalNatural.Peano.isLessThan_eq_true_iff_lt _ _).mp h_b_lt_a
      exact False.elim (Numbers.CardinalNatural.Peano.not_lt_of_lt hlt_ab hlt_ba)
    · next _ => rfl
  · next h_not_a_lt_b =>
    split
    · next _ => rfl
    · next h_not_b_lt_a =>
      have h_len_eq : length a = length b := by
        have h_not_ab : ¬ length a < length b := (Numbers.CardinalNatural.Peano.isLessThan_eq_false_iff_not_lt _ _).mp h_not_a_lt_b
        have h_not_ba : ¬ length b < length a := (Numbers.CardinalNatural.Peano.isLessThan_eq_false_iff_not_lt _ _).mp h_not_b_lt_a
        cases Numbers.CardinalNatural.Peano.trichotomy_or (length a) (length b) with
        | inl hlt => contradiction
        | inr h =>
          cases h with
          | inl heq => exact heq
          | inr hlt => contradiction
      have h_sub_ab : Numbers.CardinalNatural.Peano.subtract (length a) (length b) (Numbers.CardinalNatural.Peano.isLessThan_false_implies_le h_not_a_lt_b) = Numbers.CardinalNatural.Peano.zero := by
        exact Numbers.CardinalNatural.Peano.subtract_eq_zero_of_eq _ h_len_eq
      have h_sub_ba : Numbers.CardinalNatural.Peano.subtract (length b) (length a) (Numbers.CardinalNatural.Peano.isLessThan_false_implies_le h_not_b_lt_a) = Numbers.CardinalNatural.Peano.zero := by
        exact Numbers.CardinalNatural.Peano.subtract_eq_zero_of_eq _ h_len_eq.symm
      rw [h_sub_ab, h_sub_ba]
      rfl

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

theorem sameLength_length_eq {α : Type u} {l1 l2 : Sequences.List α}
    (h : Sequences.List.SameLength l1 l2) : l1.length = l2.length := by
  induction h with
  | empty => rfl
  | firstElement _ ih =>
    simp [Sequences.List.length, ih]

end List

end ZeroMath.Sequences
