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

def EquivalentIn {α : Type u} [Setoid α] (x : α) (l : List α) : Prop :=
  AnyElement (fun y => y ≈ x) l

instance decidableEquivalentIn {α : Type u} [Setoid α]
    [∀ (a b : α), Decidable (a ≈ b)] (x : α) (l : List α) :
    Decidable (EquivalentIn x l) :=
  decidableAnyElement (fun y => y ≈ x) l

inductive Before {α : Type u} (x y : α) : List α → Prop where
  | first ds : In y ds → Before x y (firstElement x ds)
  | notFirst d ds : Before x y ds → Before x y (firstElement d ds)

theorem before_implies_In {α : Type u} {x y : α} {l : List α}
    (h : Before x y l) : In y l := by
  induction h with
  | first ds hin => exact AnyElement.notFirst x ds hin
  | notFirst d ds _ ih => exact AnyElement.notFirst d ds ih

instance decidableBefore {α : Type u} [DecidableEq α] (x y : α) :
    (l : List α) → Decidable (Before x y l)
  | empty => isFalse fun h => by cases h
  | firstElement d ds =>
    match decEq d x, decidableIn y ds, decidableBefore x y ds with
    | isTrue hdx, isTrue hin, _ =>
      isTrue (hdx ▸ Before.first ds hin)
    | isTrue hdx, isFalse hnin, _ =>
      isFalse fun hB => by
        cases hdx
        cases hB with
        | first _ hin => exact hnin hin
        | notFirst _ _ hb => exact hnin (before_implies_In hb)
    | isFalse hndx, _, isTrue hb =>
      isTrue (Before.notFirst d ds hb)
    | isFalse hndx, _, isFalse hnb =>
      isFalse fun hB => by
        cases hB with
        | first _ _ => exact hndx rfl
        | notFirst _ _ hb => exact hnb hb

def After {α : Type u} (x y : α) (l : List α) : Prop :=
  Before y x l

instance decidableAfter {α : Type u} [DecidableEq α] (x y : α) (l : List α) :
    Decidable (After x y l) :=
  decidableBefore y x l

def Between {α : Type u} (x y z : α) (l : List α) : Prop :=
  (After x y l ∧ Before x z l) ∨ (After x z l ∧ Before x y l)

instance decidableBetween {α : Type u} [DecidableEq α] (x y z : α) (l : List α) :
    Decidable (Between x y z l) :=
  inferInstanceAs (Decidable ((After x y l ∧ Before x z l) ∨ (After x z l ∧ Before x y l)))

inductive EquivalentBefore {α : Type u} [Setoid α] (x y : α) : List α → Prop where
  | first d ds : d ≈ x → EquivalentIn y ds → EquivalentBefore x y (firstElement d ds)
  | notFirst d ds : EquivalentBefore x y ds → EquivalentBefore x y (firstElement d ds)

theorem equivalentBefore_implies_EquivalentIn {α : Type u} [Setoid α] {x y : α}
    {l : List α} (h : EquivalentBefore x y l) : EquivalentIn y l := by
  induction h with
  | first d ds _ hin => exact AnyElement.notFirst d ds hin
  | notFirst d ds _ ih => exact AnyElement.notFirst d ds ih

instance decidableEquivalentBefore {α : Type u} [Setoid α]
    [∀ (a b : α), Decidable (a ≈ b)] (x y : α) :
    (l : List α) → Decidable (EquivalentBefore x y l)
  | empty => isFalse fun h => by cases h
  | firstElement d ds =>
    match (inferInstance : Decidable (d ≈ x)), decidableEquivalentIn y ds,
        decidableEquivalentBefore x y ds with
    | isTrue hdx, isTrue hin, _ =>
      isTrue (EquivalentBefore.first d ds hdx hin)
    | isTrue _, isFalse hnin, _ =>
      isFalse fun hB => by
        cases hB with
        | first _ _ _ hin => exact hnin hin
        | notFirst _ _ hb => exact hnin (equivalentBefore_implies_EquivalentIn hb)
    | isFalse _, _, isTrue hb =>
      isTrue (EquivalentBefore.notFirst d ds hb)
    | isFalse hndx, _, isFalse hnb =>
      isFalse fun hB => by
        cases hB with
        | first _ _ heq _ => exact hndx heq
        | notFirst _ _ hb => exact hnb hb

def EquivalentAfter {α : Type u} [Setoid α] (x y : α) (l : List α) : Prop :=
  EquivalentBefore y x l

instance decidableEquivalentAfter {α : Type u} [Setoid α]
    [∀ (a b : α), Decidable (a ≈ b)] (x y : α) (l : List α) :
    Decidable (EquivalentAfter x y l) :=
  decidableEquivalentBefore y x l

def EquivalentBetween {α : Type u} [Setoid α] (x y z : α) (l : List α) : Prop :=
  (EquivalentAfter x y l ∧ EquivalentBefore x z l) ∨
    (EquivalentAfter x z l ∧ EquivalentBefore x y l)

instance decidableEquivalentBetween {α : Type u} [Setoid α]
    [∀ (a b : α), Decidable (a ≈ b)] (x y z : α) (l : List α) :
    Decidable (EquivalentBetween x y z l) :=
  inferInstanceAs
    (Decidable
      ((EquivalentAfter x y l ∧ EquivalentBefore x z l) ∨
        (EquivalentAfter x z l ∧ EquivalentBefore x y l)))

/-- There are no two equal elements in the list. -/
inductive Unique {α : Type u} : List α → Prop where
  | empty : Unique empty
  | firstElement (d : α) (ds : List α) : ¬ In d ds → Unique ds → Unique (firstElement d ds)

instance decidableUnique {α : Type u} [DecidableEq α] :
    (l : List α) → Decidable (Unique l)
  | empty => isTrue Unique.empty
  | firstElement d ds =>
    match decidableIn d ds, decidableUnique ds with
    | isFalse hnin, isTrue huniq =>
      isTrue (Unique.firstElement d ds hnin huniq)
    | isTrue hin, _ =>
      isFalse fun h => by
        cases h with
        | firstElement _ _ hnin _ => exact hnin hin
    | _, isFalse hnuniq =>
      isFalse fun h => by
        cases h with
        | firstElement _ _ _ huniq => exact hnuniq huniq

theorem Unique.not_in_head {α : Type u} {x : α} {xs : List α}
    (h : Unique (List.firstElement x xs)) : ¬ In x xs := by
  cases h with
  | firstElement _ _ hnin _ => exact hnin

theorem Unique.tail {α : Type u} {x : α} {xs : List α}
    (h : Unique (List.firstElement x xs)) : Unique xs := by
  cases h with
  | firstElement _ _ _ huniq => exact huniq

/-- There are no two equivalent elements in the list. -/
inductive UniqueUpToEquivalence {α : Type u} [Setoid α] : List α → Prop where
  | empty : UniqueUpToEquivalence empty
  | firstElement (d : α) (ds : List α) :
      ¬ EquivalentIn d ds → UniqueUpToEquivalence ds →
        UniqueUpToEquivalence (firstElement d ds)

instance decidableUniqueUpToEquivalence {α : Type u} [Setoid α]
    [∀ (a b : α), Decidable (a ≈ b)] :
    (l : List α) → Decidable (UniqueUpToEquivalence l)
  | empty => isTrue UniqueUpToEquivalence.empty
  | firstElement d ds =>
    match decidableEquivalentIn d ds, decidableUniqueUpToEquivalence ds with
    | isFalse hnin, isTrue huniq =>
      isTrue (UniqueUpToEquivalence.firstElement d ds hnin huniq)
    | isTrue hin, _ =>
      isFalse fun h => by
        cases h with
        | firstElement _ _ hnin _ => exact hnin hin
    | _, isFalse hnuniq =>
      isFalse fun h => by
        cases h with
        | firstElement _ _ _ huniq => exact hnuniq huniq

/-- `RemoveFirst x l l'` means `l'` is `l` with the first occurrence of `x` removed. -/
inductive RemoveFirst {α : Type u} (x : α) : List α → List α → Prop where
  | here (ys : List α) : RemoveFirst x (firstElement x ys) ys
  | there (y : α) (ys ys' : List α) :
      x ≠ y → RemoveFirst x ys ys' →
        RemoveFirst x (firstElement y ys) (firstElement y ys')

/-- Remove the first occurrence of `x`, if any. -/
def removeFirst {α : Type u} [DecidableEq α] (x : α) : List α → Option (List α)
  | empty => none
  | firstElement y ys =>
    if x = y then
      some ys
    else
      match removeFirst x ys with
      | none => none
      | some ys' => some (firstElement y ys')

theorem removeFirst_eq_some_iff {α : Type u} [DecidableEq α] (x : α) (l l' : List α) :
    removeFirst x l = some l' ↔ RemoveFirst x l l' := by
  induction l generalizing l' with
  | empty =>
    constructor
    · intro h
      simp only [removeFirst] at h
      nomatch h
    · intro h
      cases h
  | firstElement y ys ih =>
    simp only [removeFirst]
    split
    · next heq =>
      cases heq
      constructor
      · intro h
        injection h with hl'
        cases hl'
        exact RemoveFirst.here _
      · intro h
        cases h with
        | here => rfl
        | there _ _ _ hne _ => exact absurd rfl hne
    · next hne =>
      constructor
      · intro h
        cases hys : removeFirst x ys with
        | none =>
          simp only [hys] at h
          nomatch h
        | some ys'' =>
          simp only [hys] at h
          injection h with hl'
          cases hl'
          exact RemoveFirst.there y ys _ hne ((ih _).mp hys)
      · intro h
        cases h with
        | here => exact absurd rfl hne
        | there _ _ ys' _ hR =>
          simp only [(ih ys').mpr hR]

theorem RemoveFirst.unique {α : Type u} {x : α} {l l₁ l₂ : List α}
    (h₁ : RemoveFirst x l l₁) (h₂ : RemoveFirst x l l₂) : l₁ = l₂ := by
  induction h₁ generalizing l₂ with
  | here ys =>
    cases h₂ with
    | here => rfl
    | there _ _ _ hne _ => exact absurd rfl hne
  | there y ys ys' hne hR ih =>
    cases h₂ with
    | here => exact absurd rfl hne
    | there _ _ ys₂ _ hR₂ => exact congrArg (firstElement y) (ih hR₂)

instance decidableRemoveFirst {α : Type u} [DecidableEq α] (x : α) (l l' : List α) :
    Decidable (RemoveFirst x l l') := by
  cases h : removeFirst x l with
  | none =>
    exact isFalse fun hR => by
      have hsome := (removeFirst_eq_some_iff x l l').mpr hR
      rw [h] at hsome
      nomatch hsome
  | some l'' =>
    match decEq l' l'' with
    | isTrue heq =>
      exact isTrue (heq ▸ (removeFirst_eq_some_iff x l l'').mp h)
    | isFalse hne =>
      exact isFalse fun hR =>
        hne (RemoveFirst.unique hR ((removeFirst_eq_some_iff x l l'').mp h))

/-- Two lists contain the same elements, possibly in a different order. -/
inductive Reordering {α : Type u} : List α → List α → Prop where
  | empty : Reordering empty empty
  | cons (x : α) (xs ys ys' : List α) :
      RemoveFirst x ys ys' → Reordering xs ys' →
        Reordering (firstElement x xs) ys

instance decidableReordering {α : Type u} [DecidableEq α] :
    (a b : List α) → Decidable (Reordering a b)
  | empty, empty => isTrue Reordering.empty
  | empty, firstElement _ _ => isFalse fun h => by cases h
  | firstElement x xs, ys =>
    match hrem : removeFirst x ys with
    | none =>
      isFalse fun h => by
        cases h with
        | cons _x _xs _ys ysRem hR _hr =>
          have hsome := (removeFirst_eq_some_iff x ys ysRem).mpr hR
          rw [hrem] at hsome
          nomatch hsome
    | some ys' =>
      match decidableReordering xs ys' with
      | isTrue hr =>
        isTrue (Reordering.cons x xs ys ys' ((removeFirst_eq_some_iff x ys ys').mp hrem) hr)
      | isFalse hnr =>
        isFalse fun h => by
          cases h with
          | cons _x _xs _ys ysRem hR hr =>
            have heq : ysRem = ys' :=
              RemoveFirst.unique hR ((removeFirst_eq_some_iff x ys ys').mp hrem)
            exact hnr (heq ▸ hr)

def isEmpty {α : Type u} : List α → Bool
  | empty => true
  | firstElement _ _ => false

def append {α : Type u} (l : List α) (x : α) : List α :=
  match l with
  | empty => firstElement x empty
  | firstElement y ys => firstElement y (append ys x)

/-- Concatenate two lists: the elements of `a` followed by the elements of `b`. -/
def concatenate {α : Type u} (a b : List α) : List α :=
  match a with
  | empty => b
  | firstElement x xs => firstElement x (concatenate xs b)

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

@[simp]
theorem concatenate_length {α : Type u} (a b : List α) :
    (concatenate a b).length = a.length + b.length := by
  induction a with
  | empty =>
      simp only [concatenate, length, Numbers.CardinalNatural.Peano.zero_add]
  | firstElement x xs ih =>
      simp only [concatenate, length, ih, Numbers.CardinalNatural.Peano.add_one,
        Numbers.CardinalNatural.Peano.successor_add]

def lastElement {α : Type u} : (l : List α) → l ≠ empty → α
  | empty, h => False.elim (h rfl)
  | firstElement d empty, _ => d
  | firstElement _ (firstElement d' ds'), _ =>
      lastElement (firstElement d' ds') (fun h => by cases h)

end List

end ZeroMath.Sequences
