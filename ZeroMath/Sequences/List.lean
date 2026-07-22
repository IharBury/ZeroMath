import ZeroMath.Numbers.CardinalNatural.Peano

namespace ZeroMath.Sequences

inductive List (α : Type u) where
  | empty : List α
  | firstElement : α → List α → List α

deriving instance DecidableEq for List

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

theorem anyElement_eq_true_iff {α : Type u} (p : α → Bool) (l : List α) :
    anyElement p l = true ↔ AnyElement (fun x => p x = true) l := by
  induction l with
  | empty =>
    constructor
    · intro h
      simp only [anyElement] at h
      exact False.elim (Bool.false_ne_true h)
    · intro h
      cases h
  | firstElement d ds ih =>
    simp only [anyElement]
    split
    · next hp =>
      constructor
      · intro _
        exact AnyElement.first d ds hp
      · intro _
        rfl
    · next hnp =>
      constructor
      · intro h
        exact AnyElement.notFirst d ds (ih.mp h)
      · intro h
        cases h with
        | first _ _ hp => exact absurd hp hnp
        | notFirst _ _ hds => exact ih.mpr hds

theorem anyElement_decide_eq_true_iff {α : Type u} (p : α → Prop) [DecidablePred p]
    (l : List α) :
    anyElement (fun x => decide (p x)) l = true ↔ AnyElement p l := by
  rw [anyElement_eq_true_iff]
  constructor
  · intro hAny
    induction hAny with
    | first d ds hp =>
      exact AnyElement.first d ds (decide_eq_true_iff.mp hp)
    | notFirst d ds _ ih =>
      exact AnyElement.notFirst d ds ih
  · intro hAny
    induction hAny with
    | first d ds hp =>
      exact AnyElement.first d ds (decide_eq_true_iff.mpr hp)
    | notFirst d ds _ ih =>
      exact AnyElement.notFirst d ds ih

instance decidableAnyElement {α : Type u} (p : α → Prop) [DecidablePred p]
    (l : List α) : Decidable (AnyElement p l) := by
  cases h : anyElement (fun x => decide (p x)) l with
  | false =>
    exact isFalse (fun hAny =>
      Bool.noConfusion (Eq.trans h.symm ((anyElement_decide_eq_true_iff p l).mpr hAny)))
  | true =>
    exact isTrue ((anyElement_decide_eq_true_iff p l).mp h)

def In {α : Type u} (x : α) (l : List α) : Prop :=
  AnyElement (fun y => y = x) l

instance decidableIn {α : Type u} [DecidableEq α] (x : α) (l : List α) :
    Decidable (In x l) :=
  decidableAnyElement (fun y => y = x) l

inductive Before {α : Type u} (x y : α) : List α → Prop where
  | first ds : In y ds → Before x y (firstElement x ds)
  | notFirst d ds : Before x y ds → Before x y (firstElement d ds)

def After {α : Type u} (x y : α) (l : List α) : Prop :=
  Before y x l

def isEmpty {α : Type u} : List α → Bool
  | empty => true
  | firstElement _ _ => false

def append {α : Type u} (l : List α) (x : α) : List α :=
  match l with
  | empty => firstElement x empty
  | firstElement y ys => firstElement y (append ys x)

def length {α : Type u} : List α → Numbers.CardinalNatural.Peano
  | empty => Numbers.CardinalNatural.Peano.zero
  | firstElement _ ds => ds.length + Numbers.CardinalNatural.Peano.one

def padAtStart {α : Type u} (l : List α) (paddingValue : α) (n : Numbers.CardinalNatural.Peano) : List α :=
  match n with
  | .zero => l
  | .successor n' => padAtStart (.firstElement paddingValue l) paddingValue n'

def padAtEnd {α : Type u} (l : List α) (paddingValue : α) (n : Numbers.CardinalNatural.Peano) : List α :=
  match l with
  | .empty =>
    match n with
    | .zero => .empty
    | .successor n' => .firstElement paddingValue (padAtEnd .empty paddingValue n')
  | .firstElement d ds => .firstElement d (padAtEnd ds paddingValue n)

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

abbrev SameLength {α : Type u} (a b : List α) : Prop := a.length = b.length

theorem sameLength_commutative {α : Type u} {a b : List α}
    (h : SameLength a b) : SameLength b a :=
  h.symm

theorem sameLength_firstElement {α : Type u} {da db : α} {das dbs : List α}
    (h : SameLength das dbs) :
    SameLength (firstElement da das) (firstElement db dbs) := by
  simp only [SameLength, length, h]

theorem sameLength_of_firstElement {α : Type u} {da db : α} {das dbs : List α}
    (h : SameLength (firstElement da das) (firstElement db dbs)) :
    SameLength das dbs :=
  Numbers.CardinalNatural.Peano.add_right_cancel
    Numbers.CardinalNatural.Peano.one _ _ h

/-- Induction principle matching the former inductive `SameLength`. -/
theorem SameLength.induction {α : Type u}
    {motive : (a b : List α) → SameLength a b → Prop}
    (empty : motive empty empty rfl)
    (firstElement : ∀ {da db : α} {das dbs : List α} (h : SameLength das dbs),
      motive das dbs h →
      motive (firstElement da das) (firstElement db dbs) (sameLength_firstElement h))
    {a b : List α} (h : SameLength a b) : motive a b h := by
  induction a generalizing b with
  | empty =>
    cases b with
    | empty => exact empty
    | firstElement _ _ => cases h
  | firstElement da das ih =>
    cases b with
    | empty => cases h
    | firstElement db dbs =>
      exact firstElement (sameLength_of_firstElement h)
        (ih (sameLength_of_firstElement h))

@[simp]
theorem padAtStart_length {α : Type u} (l : Sequences.List α)
  (paddingValue : α) (n : Numbers.CardinalNatural.Peano) :
  length (padAtStart l paddingValue n) = length l + n := by
  induction n generalizing l with
  | zero => rfl
  | successor n' ih =>
    simp only [padAtStart, ih, length, Numbers.CardinalNatural.Peano.add_associative,
      Numbers.CardinalNatural.Peano.one_add]

@[simp]
theorem padAtStart_zero {α : Type u} (l : List α) (paddingValue : α) :
  padAtStart l paddingValue Numbers.CardinalNatural.Peano.zero = l := rfl

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
    change length a = length (padAtStart b paddingValue _)
    have h_le : Sequences.List.length b ≤ Sequences.List.length a := Numbers.CardinalNatural.Peano.isLessThan_true_implies_le h_less
    rw [padAtStart_length]
    have h_cancel := Numbers.CardinalNatural.Peano.subtract_add_cancel (Sequences.List.length a) (Sequences.List.length b) h_le
    rw [Numbers.CardinalNatural.Peano.add_commutative]
    exact h_cancel.symm
  · next h_less =>
    change length (padAtStart a paddingValue _) = length b
    have h_le : Sequences.List.length a ≤ Sequences.List.length b := Numbers.CardinalNatural.Peano.isLessThan_false_implies_le h_less
    rw [padAtStart_length]
    have h_cancel := Numbers.CardinalNatural.Peano.subtract_add_cancel (Sequences.List.length b) (Sequences.List.length a) h_le
    rw [Numbers.CardinalNatural.Peano.add_commutative]
    exact h_cancel

@[simp]
theorem padAtEnd_length {α : Type u} (l : List α) (paddingValue : α) (n : Numbers.CardinalNatural.Peano) :
    (padAtEnd l paddingValue n).length = l.length + n := by
  induction l with
  | empty =>
    induction n with
    | zero =>
      simp only [padAtEnd, length, Numbers.CardinalNatural.Peano.add_zero]
    | successor n ih =>
      simp only [padAtEnd, length, Numbers.CardinalNatural.Peano.zero_add, ih,
        Numbers.CardinalNatural.Peano.add_one]
  | firstElement d ds ih =>
    simp only [padAtEnd, length, ih, Numbers.CardinalNatural.Peano.add_one,
      Numbers.CardinalNatural.Peano.successor_add]

@[simp]
theorem append_length {α : Type u} (l : List α) (x : α) :
    (append l x).length = l.length + Numbers.CardinalNatural.Peano.one := by
  induction l with
  | empty =>
      simp only [append, length, Numbers.CardinalNatural.Peano.zero_add]
  | firstElement y ys ih =>
      simp only [append, length, ih, Numbers.CardinalNatural.Peano.add_one]

def lastElement {α : Type u} : (l : List α) → l ≠ empty → α
  | empty, h => False.elim (h rfl)
  | firstElement d empty, _ => d
  | firstElement _ (firstElement d' ds'), _ =>
      lastElement (firstElement d' ds') (fun h => by cases h)

end List

end ZeroMath.Sequences
