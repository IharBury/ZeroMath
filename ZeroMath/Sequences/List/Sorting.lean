import ZeroMath.Sequences.List

namespace ZeroMath.Sequences.List

set_option linter.unusedSectionVars false

variable {α : Type u} [LT α] [LE α]
variable [∀ (a b : α), Decidable (a < b)]
variable [∀ (a b : α), Decidable (a ≤ b)]

/-- The list is sorted in strictly ascending order (equal elements are not allowed). -/
inductive SortedStrictlyAscending : List α → Prop where
  | empty : SortedStrictlyAscending .empty
  | single (x : α) : SortedStrictlyAscending (.firstElement x .empty)
  | cons {x y : α} {ys : List α}
      (hlt : x < y)
      (hrest : SortedStrictlyAscending (.firstElement y ys)) :
      SortedStrictlyAscending (.firstElement x (.firstElement y ys))

instance decidableSortedStrictlyAscending :
    (l : List α) → Decidable (SortedStrictlyAscending l)
  | .empty => isTrue SortedStrictlyAscending.empty
  | .firstElement x .empty => isTrue (SortedStrictlyAscending.single x)
  | .firstElement x (.firstElement y ys) =>
      match (inferInstance : Decidable (x < y)),
          decidableSortedStrictlyAscending (.firstElement y ys) with
      | isTrue hlt, isTrue hrest =>
          isTrue (SortedStrictlyAscending.cons hlt hrest)
      | isFalse hnlt, _ =>
          isFalse fun h => by
            cases h with
            | cons hlt _ => exact hnlt hlt
      | _, isFalse hnrest =>
          isFalse fun h => by
            cases h with
            | cons _ hrest => exact hnrest hrest

/-- The list is sorted in strictly descending order (equal elements are not allowed). -/
inductive SortedStrictlyDescending : List α → Prop where
  | empty : SortedStrictlyDescending .empty
  | single (x : α) : SortedStrictlyDescending (.firstElement x .empty)
  | cons {x y : α} {ys : List α}
      (hgt : x > y)
      (hrest : SortedStrictlyDescending (.firstElement y ys)) :
      SortedStrictlyDescending (.firstElement x (.firstElement y ys))

instance decidableSortedStrictlyDescending :
    (l : List α) → Decidable (SortedStrictlyDescending l)
  | .empty => isTrue SortedStrictlyDescending.empty
  | .firstElement x .empty => isTrue (SortedStrictlyDescending.single x)
  | .firstElement x (.firstElement y ys) =>
      match (inferInstance : Decidable (x > y)),
          decidableSortedStrictlyDescending (.firstElement y ys) with
      | isTrue hgt, isTrue hrest =>
          isTrue (SortedStrictlyDescending.cons hgt hrest)
      | isFalse hngt, _ =>
          isFalse fun h => by
            cases h with
            | cons hgt _ => exact hngt hgt
      | _, isFalse hnrest =>
          isFalse fun h => by
            cases h with
            | cons _ hrest => exact hnrest hrest

/-- The list is sorted in non-descending order (equal elements are allowed). -/
inductive SortedNonDescending : List α → Prop where
  | empty : SortedNonDescending .empty
  | single (x : α) : SortedNonDescending (.firstElement x .empty)
  | cons {x y : α} {ys : List α}
      (hle : x ≤ y)
      (hrest : SortedNonDescending (.firstElement y ys)) :
      SortedNonDescending (.firstElement x (.firstElement y ys))

instance decidableSortedNonDescending :
    (l : List α) → Decidable (SortedNonDescending l)
  | .empty => isTrue SortedNonDescending.empty
  | .firstElement x .empty => isTrue (SortedNonDescending.single x)
  | .firstElement x (.firstElement y ys) =>
      match (inferInstance : Decidable (x ≤ y)),
          decidableSortedNonDescending (.firstElement y ys) with
      | isTrue hle, isTrue hrest =>
          isTrue (SortedNonDescending.cons hle hrest)
      | isFalse hnle, _ =>
          isFalse fun h => by
            cases h with
            | cons hle _ => exact hnle hle
      | _, isFalse hnrest =>
          isFalse fun h => by
            cases h with
            | cons _ hrest => exact hnrest hrest

/-- The list is sorted in non-ascending order (equal elements are allowed). -/
inductive SortedNonAscending : List α → Prop where
  | empty : SortedNonAscending .empty
  | single (x : α) : SortedNonAscending (.firstElement x .empty)
  | cons {x y : α} {ys : List α}
      (hge : x ≥ y)
      (hrest : SortedNonAscending (.firstElement y ys)) :
      SortedNonAscending (.firstElement x (.firstElement y ys))

instance decidableSortedNonAscending :
    (l : List α) → Decidable (SortedNonAscending l)
  | .empty => isTrue SortedNonAscending.empty
  | .firstElement x .empty => isTrue (SortedNonAscending.single x)
  | .firstElement x (.firstElement y ys) =>
      match (inferInstance : Decidable (x ≥ y)),
          decidableSortedNonAscending (.firstElement y ys) with
      | isTrue hge, isTrue hrest =>
          isTrue (SortedNonAscending.cons hge hrest)
      | isFalse hnge, _ =>
          isFalse fun h => by
            cases h with
            | cons hge _ => exact hnge hge
      | _, isFalse hnrest =>
          isFalse fun h => by
            cases h with
            | cons _ hrest => exact hnrest hrest

theorem SortedStrictlyAscending.tail {x : α} {xs : List α}
    (h : SortedStrictlyAscending (.firstElement x xs)) :
    SortedStrictlyAscending xs := by
  cases h with
  | single => exact SortedStrictlyAscending.empty
  | cons _ hrest => exact hrest

theorem SortedStrictlyDescending.tail {x : α} {xs : List α}
    (h : SortedStrictlyDescending (.firstElement x xs)) :
    SortedStrictlyDescending xs := by
  cases h with
  | single => exact SortedStrictlyDescending.empty
  | cons _ hrest => exact hrest

theorem SortedNonDescending.tail {x : α} {xs : List α}
    (h : SortedNonDescending (.firstElement x xs)) : SortedNonDescending xs := by
  cases h with
  | single => exact SortedNonDescending.empty
  | cons _ hrest => exact hrest

theorem SortedNonAscending.tail {x : α} {xs : List α}
    (h : SortedNonAscending (.firstElement x xs)) : SortedNonAscending xs := by
  cases h with
  | single => exact SortedNonAscending.empty
  | cons _ hrest => exact hrest

theorem SortedNonDescending.cons_of {x : α} {xs : List α}
    (hxs : SortedNonDescending xs)
    (hle : ∀ y ys, xs = .firstElement y ys → x ≤ y) :
    SortedNonDescending (.firstElement x xs) := by
  match xs with
  | .empty => exact SortedNonDescending.single x
  | .firstElement y ys => exact SortedNonDescending.cons (hle y ys rfl) hxs

theorem SortedNonAscending.cons_of {x : α} {xs : List α}
    (hxs : SortedNonAscending xs)
    (hge : ∀ y ys, xs = .firstElement y ys → x ≥ y) :
    SortedNonAscending (.firstElement x xs) := by
  match xs with
  | .empty => exact SortedNonAscending.single x
  | .firstElement y ys => exact SortedNonAscending.cons (hge y ys rfl) hxs

theorem SortedStrictlyAscending.cons_of {x : α} {xs : List α}
    (hxs : SortedStrictlyAscending xs)
    (hlt : ∀ y ys, xs = .firstElement y ys → x < y) :
    SortedStrictlyAscending (.firstElement x xs) := by
  match xs with
  | .empty => exact SortedStrictlyAscending.single x
  | .firstElement y ys => exact SortedStrictlyAscending.cons (hlt y ys rfl) hxs

theorem SortedStrictlyDescending.cons_of {x : α} {xs : List α}
    (hxs : SortedStrictlyDescending xs)
    (hgt : ∀ y ys, xs = .firstElement y ys → x > y) :
    SortedStrictlyDescending (.firstElement x xs) := by
  match xs with
  | .empty => exact SortedStrictlyDescending.single x
  | .firstElement y ys => exact SortedStrictlyDescending.cons (hgt y ys rfl) hxs

/-- Insert `x` into a list, placing it before the first element that is at least `x`. -/
def insertSortedNonDescending (x : α) : List α → List α
  | .empty => .firstElement x .empty
  | .firstElement y ys =>
    if x ≤ y then
      .firstElement x (.firstElement y ys)
    else
      .firstElement y (insertSortedNonDescending x ys)

/-- Insert `x` into a list, placing it before the first element that is at most `x`. -/
def insertSortedNonAscending (x : α) : List α → List α
  | .empty => .firstElement x .empty
  | .firstElement y ys =>
    if x ≥ y then
      .firstElement x (.firstElement y ys)
    else
      .firstElement y (insertSortedNonAscending x ys)

/-- Insert `x` into a list, placing it before the first strictly greater element. -/
def insertSortedStrictlyAscending (x : α) : List α → List α
  | .empty => .firstElement x .empty
  | .firstElement y ys =>
    if x < y then
      .firstElement x (.firstElement y ys)
    else
      .firstElement y (insertSortedStrictlyAscending x ys)

/-- Insert `x` into a list, placing it before the first strictly smaller element. -/
def insertSortedStrictlyDescending (x : α) : List α → List α
  | .empty => .firstElement x .empty
  | .firstElement y ys =>
    if x > y then
      .firstElement x (.firstElement y ys)
    else
      .firstElement y (insertSortedStrictlyDescending x ys)

/-- Sort a list into non-descending order using insertion sort. -/
def insertionSortNonDescending : List α → List α
  | .empty => .empty
  | .firstElement x xs =>
      insertSortedNonDescending x (insertionSortNonDescending xs)

/-- Sort a list into non-ascending order using insertion sort. -/
def insertionSortNonAscending : List α → List α
  | .empty => .empty
  | .firstElement x xs =>
      insertSortedNonAscending x (insertionSortNonAscending xs)

/-- Sort a list into strictly ascending order using insertion sort. -/
def insertionSortStrictlyAscending : List α → List α
  | .empty => .empty
  | .firstElement x xs =>
      insertSortedStrictlyAscending x (insertionSortStrictlyAscending xs)

/-- Sort a list into strictly descending order using insertion sort. -/
def insertionSortStrictlyDescending : List α → List α
  | .empty => .empty
  | .firstElement x xs =>
      insertSortedStrictlyDescending x (insertionSortStrictlyDescending xs)

theorem insertSortedNonDescending_sorted
    (le_of_not_le : ∀ {a b : α}, ¬ a ≤ b → b ≤ a)
    (x : α) : (l : List α) → SortedNonDescending l →
      SortedNonDescending (insertSortedNonDescending x l)
  | .empty, _ => SortedNonDescending.single x
  | .firstElement y ys, h => by
    unfold insertSortedNonDescending
    split
    · next hxy => exact SortedNonDescending.cons hxy h
    · next hnxy =>
      have ih := insertSortedNonDescending_sorted le_of_not_le x ys h.tail
      refine SortedNonDescending.cons_of ih ?_
      intro z zs heq
      have : y ≤ z := by
        match ys with
        | .empty =>
          simp only [insertSortedNonDescending] at heq
          injection heq with hz _
          exact hz ▸ le_of_not_le hnxy
        | .firstElement w ws =>
          simp only [insertSortedNonDescending] at heq
          split at heq
          · next hxw =>
            injection heq with hz _
            exact hz ▸ le_of_not_le hnxy
          · next _ =>
            injection heq with hz _
            cases h with
            | cons hyw _ => exact hz ▸ hyw
      exact this

theorem insertSortedNonAscending_sorted
    (le_of_not_le : ∀ {a b : α}, ¬ a ≤ b → b ≤ a)
    (x : α) : (l : List α) → SortedNonAscending l →
      SortedNonAscending (insertSortedNonAscending x l)
  | .empty, _ => SortedNonAscending.single x
  | .firstElement y ys, h => by
    unfold insertSortedNonAscending
    split
    · next hxy => exact SortedNonAscending.cons hxy h
    · next hnxy =>
      have ih := insertSortedNonAscending_sorted le_of_not_le x ys h.tail
      refine SortedNonAscending.cons_of ih ?_
      intro z zs heq
      have : y ≥ z := by
        match ys with
        | .empty =>
          simp only [insertSortedNonAscending] at heq
          injection heq with hz _
          exact hz ▸ le_of_not_le hnxy
        | .firstElement w ws =>
          simp only [insertSortedNonAscending] at heq
          split at heq
          · next hxw =>
            injection heq with hz _
            exact hz ▸ le_of_not_le hnxy
          · next _ =>
            injection heq with hz _
            cases h with
            | cons hyw _ => exact hz ▸ hyw
      exact this

theorem insertSortedStrictlyAscending_sorted
    (lt_of_not_lt_ne : ∀ {a b : α}, ¬ a < b → a ≠ b → b < a)
    (x : α) : (l : List α) → SortedStrictlyAscending l → ¬ In x l →
      SortedStrictlyAscending (insertSortedStrictlyAscending x l)
  | .empty, _, _ => SortedStrictlyAscending.single x
  | .firstElement y ys, h, hnin => by
    unfold insertSortedStrictlyAscending
    split
    · next hxy => exact SortedStrictlyAscending.cons hxy h
    · next hnxy =>
      have ih := insertSortedStrictlyAscending_sorted lt_of_not_lt_ne x ys h.tail
        (not_in_tail hnin)
      refine SortedStrictlyAscending.cons_of ih ?_
      intro z zs heq
      have hyx : y < x :=
        lt_of_not_lt_ne hnxy (ne_of_not_in_firstElement hnin)
      have : y < z := by
        match ys with
        | .empty =>
          simp only [insertSortedStrictlyAscending] at heq
          injection heq with hz _
          exact hz ▸ hyx
        | .firstElement w ws =>
          simp only [insertSortedStrictlyAscending] at heq
          split at heq
          · next hxw =>
            injection heq with hz _
            exact hz ▸ hyx
          · next _ =>
            injection heq with hz _
            cases h with
            | cons hyw _ => exact hz ▸ hyw
      exact this

theorem insertSortedStrictlyDescending_sorted
    (lt_of_not_lt_ne : ∀ {a b : α}, ¬ a < b → a ≠ b → b < a)
    (x : α) : (l : List α) → SortedStrictlyDescending l → ¬ In x l →
      SortedStrictlyDescending (insertSortedStrictlyDescending x l)
  | .empty, _, _ => SortedStrictlyDescending.single x
  | .firstElement y ys, h, hnin => by
    unfold insertSortedStrictlyDescending
    split
    · next hxy => exact SortedStrictlyDescending.cons hxy h
    · next hnxy =>
      have ih := insertSortedStrictlyDescending_sorted lt_of_not_lt_ne x ys h.tail
        (not_in_tail hnin)
      refine SortedStrictlyDescending.cons_of ih ?_
      intro z zs heq
      have hyx : y > x :=
        lt_of_not_lt_ne (a := y) (b := x) hnxy (ne_of_not_in_firstElement hnin).symm
      have : y > z := by
        match ys with
        | .empty =>
          simp only [insertSortedStrictlyDescending] at heq
          injection heq with hz _
          exact hz ▸ hyx
        | .firstElement w ws =>
          simp only [insertSortedStrictlyDescending] at heq
          split at heq
          · next hxw =>
            injection heq with hz _
            exact hz ▸ hyx
          · next _ =>
            injection heq with hz _
            cases h with
            | cons hyw _ => exact hz ▸ hyw
      exact this

theorem insertSortedStrictlyAscending_equivalent_sorted
    [Setoid α] (lt_of_not_lt_not_equivalent : ∀ {a b : α}, ¬ a < b → ¬ a ≈ b → b < a)
    (x : α) : (l : List α) → SortedStrictlyAscending l → ¬ EquivalentIn x l →
      SortedStrictlyAscending (insertSortedStrictlyAscending x l)
  | .empty, _, _ => SortedStrictlyAscending.single x
  | .firstElement y ys, h, hnin => by
    unfold insertSortedStrictlyAscending
    split
    · next hxy => exact SortedStrictlyAscending.cons hxy h
    · next hnxy =>
      have ih := insertSortedStrictlyAscending_equivalent_sorted
        lt_of_not_lt_not_equivalent x ys h.tail (not_equivalentIn_tail hnin)
      refine SortedStrictlyAscending.cons_of ih ?_
      intro z zs heq
      have hyx : y < x :=
        lt_of_not_lt_not_equivalent hnxy
          (not_equivalent_of_not_equivalentIn_firstElement hnin)
      have : y < z := by
        match ys with
        | .empty =>
          simp only [insertSortedStrictlyAscending] at heq
          injection heq with hz _
          exact hz ▸ hyx
        | .firstElement w ws =>
          simp only [insertSortedStrictlyAscending] at heq
          split at heq
          · next hxw =>
            injection heq with hz _
            exact hz ▸ hyx
          · next _ =>
            injection heq with hz _
            cases h with
            | cons hyw _ => exact hz ▸ hyw
      exact this

theorem insertSortedStrictlyDescending_equivalent_sorted
    [Setoid α] (lt_of_not_lt_not_equivalent : ∀ {a b : α}, ¬ a < b → ¬ a ≈ b → b < a)
    (x : α) : (l : List α) → SortedStrictlyDescending l → ¬ EquivalentIn x l →
      SortedStrictlyDescending (insertSortedStrictlyDescending x l)
  | .empty, _, _ => SortedStrictlyDescending.single x
  | .firstElement y ys, h, hnin => by
    unfold insertSortedStrictlyDescending
    split
    · next hxy => exact SortedStrictlyDescending.cons hxy h
    · next hnxy =>
      have ih := insertSortedStrictlyDescending_equivalent_sorted
        lt_of_not_lt_not_equivalent x ys h.tail (not_equivalentIn_tail hnin)
      refine SortedStrictlyDescending.cons_of ih ?_
      intro z zs heq
      have hyx : y > x :=
        lt_of_not_lt_not_equivalent (a := y) (b := x) hnxy
          (fun heq => not_equivalent_of_not_equivalentIn_firstElement hnin (Setoid.symm heq))
      have : y > z := by
        match ys with
        | .empty =>
          simp only [insertSortedStrictlyDescending] at heq
          injection heq with hz _
          exact hz ▸ hyx
        | .firstElement w ws =>
          simp only [insertSortedStrictlyDescending] at heq
          split at heq
          · next hxw =>
            injection heq with hz _
            exact hz ▸ hyx
          · next _ =>
            injection heq with hz _
            cases h with
            | cons hyw _ => exact hz ▸ hyw
      exact this

theorem insertionSortNonDescending_sorted
    (le_of_not_le : ∀ {a b : α}, ¬ a ≤ b → b ≤ a)
    (l : List α) : SortedNonDescending (insertionSortNonDescending l) := by
  induction l with
  | empty => exact SortedNonDescending.empty
  | firstElement x xs ih =>
    exact insertSortedNonDescending_sorted le_of_not_le x _ ih

theorem insertionSortNonAscending_sorted
    (le_of_not_le : ∀ {a b : α}, ¬ a ≤ b → b ≤ a)
    (l : List α) : SortedNonAscending (insertionSortNonAscending l) := by
  induction l with
  | empty => exact SortedNonAscending.empty
  | firstElement x xs ih =>
    exact insertSortedNonAscending_sorted le_of_not_le x _ ih

def insertionSortNonDescendingWithProof
    (le_of_not_le : ∀ {a b : α}, ¬ a ≤ b → b ≤ a)
    (l : List α) : { l' : List α // SortedNonDescending l' } :=
  ⟨insertionSortNonDescending l, insertionSortNonDescending_sorted le_of_not_le l⟩

def insertionSortNonAscendingWithProof
    (le_of_not_le : ∀ {a b : α}, ¬ a ≤ b → b ≤ a)
    (l : List α) : { l' : List α // SortedNonAscending l' } :=
  ⟨insertionSortNonAscending l, insertionSortNonAscending_sorted le_of_not_le l⟩

theorem in_of_in_insertSortedStrictlyAscending (x : α) :
    (l : List α) → {z : α} → In z (insertSortedStrictlyAscending x l) →
      z = x ∨ In z l
  | .empty, z, hin => by
    simp only [insertSortedStrictlyAscending] at hin
    cases hin with
    | first _ _ heq => exact Or.inl heq.symm
    | notFirst _ _ h => cases h
  | .firstElement y ys, z, hin => by
    unfold insertSortedStrictlyAscending at hin
    split at hin
    · next _ =>
      cases hin with
      | first _ _ heq => exact Or.inl heq.symm
      | notFirst _ _ hin' => exact Or.inr hin'
    · next _ =>
      cases hin with
      | first _ _ heq =>
        exact Or.inr (AnyElement.first y ys heq)
      | notFirst _ _ hin' =>
        match in_of_in_insertSortedStrictlyAscending x ys hin' with
        | Or.inl heq => exact Or.inl heq
        | Or.inr hinys => exact Or.inr (AnyElement.notFirst y ys hinys)

theorem in_of_in_insertSortedStrictlyDescending (x : α) :
    (l : List α) → {z : α} → In z (insertSortedStrictlyDescending x l) →
      z = x ∨ In z l
  | .empty, z, hin => by
    simp only [insertSortedStrictlyDescending] at hin
    cases hin with
    | first _ _ heq => exact Or.inl heq.symm
    | notFirst _ _ h => cases h
  | .firstElement y ys, z, hin => by
    unfold insertSortedStrictlyDescending at hin
    split at hin
    · next _ =>
      cases hin with
      | first _ _ heq => exact Or.inl heq.symm
      | notFirst _ _ hin' => exact Or.inr hin'
    · next _ =>
      cases hin with
      | first _ _ heq =>
        exact Or.inr (AnyElement.first y ys heq)
      | notFirst _ _ hin' =>
        match in_of_in_insertSortedStrictlyDescending x ys hin' with
        | Or.inl heq => exact Or.inl heq
        | Or.inr hinys => exact Or.inr (AnyElement.notFirst y ys hinys)

theorem insertionSortStrictlyAscending_subset (l : List α) {z : α}
    (hin : In z (insertionSortStrictlyAscending l)) : In z l := by
  induction l with
  | empty => cases hin
  | firstElement x xs ih =>
    match in_of_in_insertSortedStrictlyAscending x (insertionSortStrictlyAscending xs) hin with
    | Or.inl heq => exact AnyElement.first x xs heq.symm
    | Or.inr hinys => exact AnyElement.notFirst x xs (ih hinys)

theorem insertionSortStrictlyDescending_subset (l : List α) {z : α}
    (hin : In z (insertionSortStrictlyDescending l)) : In z l := by
  induction l with
  | empty => cases hin
  | firstElement x xs ih =>
    match in_of_in_insertSortedStrictlyDescending x (insertionSortStrictlyDescending xs) hin with
    | Or.inl heq => exact AnyElement.first x xs heq.symm
    | Or.inr hinys => exact AnyElement.notFirst x xs (ih hinys)

theorem insertionSortStrictlyAscending_sorted
    (lt_of_not_lt_ne : ∀ {a b : α}, ¬ a < b → a ≠ b → b < a)
    (l : List α) (h : Unique l) :
    SortedStrictlyAscending (insertionSortStrictlyAscending l) := by
  induction l with
  | empty => exact SortedStrictlyAscending.empty
  | firstElement x xs ih =>
    have hnin : ¬ In x (insertionSortStrictlyAscending xs) :=
      fun hin => h.not_in_head (insertionSortStrictlyAscending_subset xs hin)
    exact insertSortedStrictlyAscending_sorted lt_of_not_lt_ne x _
      (ih h.tail) hnin

theorem insertionSortStrictlyDescending_sorted
    (lt_of_not_lt_ne : ∀ {a b : α}, ¬ a < b → a ≠ b → b < a)
    (l : List α) (h : Unique l) :
    SortedStrictlyDescending (insertionSortStrictlyDescending l) := by
  induction l with
  | empty => exact SortedStrictlyDescending.empty
  | firstElement x xs ih =>
    have hnin : ¬ In x (insertionSortStrictlyDescending xs) :=
      fun hin => h.not_in_head (insertionSortStrictlyDescending_subset xs hin)
    exact insertSortedStrictlyDescending_sorted lt_of_not_lt_ne x _
      (ih h.tail) hnin

theorem insertionSortStrictlyAscending_equivalent_sorted
    [Setoid α] (lt_of_not_lt_not_equivalent : ∀ {a b : α}, ¬ a < b → ¬ a ≈ b → b < a)
    (l : List α) (h : UniqueUpToEquivalence l) :
    SortedStrictlyAscending (insertionSortStrictlyAscending l) := by
  induction l with
  | empty => exact SortedStrictlyAscending.empty
  | firstElement x xs ih =>
    have hnin : ¬ EquivalentIn x (insertionSortStrictlyAscending xs) :=
      fun hin => h.not_in_head (equivalentIn_of_subset
        (fun z hz => insertionSortStrictlyAscending_subset xs hz) hin)
    exact insertSortedStrictlyAscending_equivalent_sorted
      lt_of_not_lt_not_equivalent x _ (ih h.tail) hnin

theorem insertionSortStrictlyDescending_equivalent_sorted
    [Setoid α] (lt_of_not_lt_not_equivalent : ∀ {a b : α}, ¬ a < b → ¬ a ≈ b → b < a)
    (l : List α) (h : UniqueUpToEquivalence l) :
    SortedStrictlyDescending (insertionSortStrictlyDescending l) := by
  induction l with
  | empty => exact SortedStrictlyDescending.empty
  | firstElement x xs ih =>
    have hnin : ¬ EquivalentIn x (insertionSortStrictlyDescending xs) :=
      fun hin => h.not_in_head (equivalentIn_of_subset
        (fun z hz => insertionSortStrictlyDescending_subset xs hz) hin)
    exact insertSortedStrictlyDescending_equivalent_sorted
      lt_of_not_lt_not_equivalent x _ (ih h.tail) hnin

def insertionSortStrictlyAscendingWithProof
    (lt_of_not_lt_ne : ∀ {a b : α}, ¬ a < b → a ≠ b → b < a)
    (l : List α) (h : Unique l) :
    { l' : List α // SortedStrictlyAscending l' } :=
  ⟨insertionSortStrictlyAscending l, insertionSortStrictlyAscending_sorted lt_of_not_lt_ne l h⟩

def insertionSortStrictlyDescendingWithProof
    (lt_of_not_lt_ne : ∀ {a b : α}, ¬ a < b → a ≠ b → b < a)
    (l : List α) (h : Unique l) :
    { l' : List α // SortedStrictlyDescending l' } :=
  ⟨insertionSortStrictlyDescending l,
    insertionSortStrictlyDescending_sorted lt_of_not_lt_ne l h⟩

def insertionSortStrictlyAscendingEquivalentWithProof
    [Setoid α] (lt_of_not_lt_not_equivalent : ∀ {a b : α}, ¬ a < b → ¬ a ≈ b → b < a)
    (l : List α) (h : UniqueUpToEquivalence l) :
    { l' : List α // SortedStrictlyAscending l' } :=
  ⟨insertionSortStrictlyAscending l,
    insertionSortStrictlyAscending_equivalent_sorted lt_of_not_lt_not_equivalent l h⟩

def insertionSortStrictlyDescendingEquivalentWithProof
    [Setoid α] (lt_of_not_lt_not_equivalent : ∀ {a b : α}, ¬ a < b → ¬ a ≈ b → b < a)
    (l : List α) (h : UniqueUpToEquivalence l) :
    { l' : List α // SortedStrictlyDescending l' } :=
  ⟨insertionSortStrictlyDescending l,
    insertionSortStrictlyDescending_equivalent_sorted lt_of_not_lt_not_equivalent l h⟩

theorem RemoveFirst_insertSortedNonDescending
    (ne_of_not_le : ∀ {a b : α}, ¬ a ≤ b → a ≠ b)
    (x : α) : (l : List α) →
      RemoveFirst x (insertSortedNonDescending x l) l
  | .empty => RemoveFirst.here _
  | .firstElement y ys => by
    unfold insertSortedNonDescending
    split
    · next _ => exact RemoveFirst.here _
    · next hnxy =>
      exact RemoveFirst.there y
        (insertSortedNonDescending x ys) ys
        (ne_of_not_le hnxy)
        (RemoveFirst_insertSortedNonDescending ne_of_not_le x ys)

theorem RemoveFirst_insertSortedNonAscending
    (ne_of_not_le : ∀ {a b : α}, ¬ a ≤ b → a ≠ b)
    (x : α) : (l : List α) →
      RemoveFirst x (insertSortedNonAscending x l) l
  | .empty => RemoveFirst.here _
  | .firstElement y ys => by
    unfold insertSortedNonAscending
    split
    · next _ => exact RemoveFirst.here _
    · next hnxy =>
      exact RemoveFirst.there y
        (insertSortedNonAscending x ys) ys
        (ne_of_not_le (a := y) (b := x) hnxy).symm
        (RemoveFirst_insertSortedNonAscending ne_of_not_le x ys)

theorem RemoveFirst_insertSortedStrictlyAscending (x : α) :
    (l : List α) → ¬ In x l →
      RemoveFirst x (insertSortedStrictlyAscending x l) l
  | .empty, _ => RemoveFirst.here _
  | .firstElement y ys, hnin => by
    unfold insertSortedStrictlyAscending
    split
    · next _ => exact RemoveFirst.here _
    · next _ =>
      exact RemoveFirst.there y
        (insertSortedStrictlyAscending x ys) ys
        (ne_of_not_in_firstElement hnin)
        (RemoveFirst_insertSortedStrictlyAscending x ys (not_in_tail hnin))

theorem RemoveFirst_insertSortedStrictlyDescending (x : α) :
    (l : List α) → ¬ In x l →
      RemoveFirst x (insertSortedStrictlyDescending x l) l
  | .empty, _ => RemoveFirst.here _
  | .firstElement y ys, hnin => by
    unfold insertSortedStrictlyDescending
    split
    · next _ => exact RemoveFirst.here _
    · next _ =>
      exact RemoveFirst.there y
        (insertSortedStrictlyDescending x ys) ys
        (ne_of_not_in_firstElement hnin)
        (RemoveFirst_insertSortedStrictlyDescending x ys (not_in_tail hnin))

theorem RemoveFirst_insertSortedStrictlyAscending_of_not_equivalent
    [Setoid α] (x : α) : (l : List α) → ¬ EquivalentIn x l →
      RemoveFirst x (insertSortedStrictlyAscending x l) l
  | .empty, _ => RemoveFirst.here _
  | .firstElement y ys, hnin => by
    unfold insertSortedStrictlyAscending
    split
    · next _ => exact RemoveFirst.here _
    · next _ =>
      exact RemoveFirst.there y
        (insertSortedStrictlyAscending x ys) ys
        (fun heq => by
          cases heq
          exact not_equivalent_of_not_equivalentIn_firstElement hnin (Setoid.refl _))
        (RemoveFirst_insertSortedStrictlyAscending_of_not_equivalent x ys
          (not_equivalentIn_tail hnin))

theorem RemoveFirst_insertSortedStrictlyDescending_of_not_equivalent
    [Setoid α] (x : α) : (l : List α) → ¬ EquivalentIn x l →
      RemoveFirst x (insertSortedStrictlyDescending x l) l
  | .empty, _ => RemoveFirst.here _
  | .firstElement y ys, hnin => by
    unfold insertSortedStrictlyDescending
    split
    · next _ => exact RemoveFirst.here _
    · next _ =>
      exact RemoveFirst.there y
        (insertSortedStrictlyDescending x ys) ys
        (fun heq => by
          cases heq
          exact not_equivalent_of_not_equivalentIn_firstElement hnin (Setoid.refl _))
        (RemoveFirst_insertSortedStrictlyDescending_of_not_equivalent x ys
          (not_equivalentIn_tail hnin))

theorem insertionSortNonDescending_eq_insert (x : α) (xs : List α) :
    insertionSortNonDescending (.firstElement x xs) =
      insertSortedNonDescending x (insertionSortNonDescending xs) :=
  rfl

theorem insertionSortNonAscending_eq_insert (x : α) (xs : List α) :
    insertionSortNonAscending (.firstElement x xs) =
      insertSortedNonAscending x (insertionSortNonAscending xs) :=
  rfl

theorem insertionSortNonDescending_reordering
    (ne_of_not_le : ∀ {a b : α}, ¬ a ≤ b → a ≠ b)
    (l : List α) : Reordering l (insertionSortNonDescending l) := by
  induction l with
  | empty => exact Reordering.empty
  | firstElement x xs ih =>
    exact Reordering.cons x xs
      (insertSortedNonDescending x (insertionSortNonDescending xs))
      (insertionSortNonDescending xs)
      (RemoveFirst_insertSortedNonDescending ne_of_not_le x _)
      ih

theorem insertionSortNonAscending_reordering
    (ne_of_not_le : ∀ {a b : α}, ¬ a ≤ b → a ≠ b)
    (l : List α) : Reordering l (insertionSortNonAscending l) := by
  induction l with
  | empty => exact Reordering.empty
  | firstElement x xs ih =>
    exact Reordering.cons x xs
      (insertSortedNonAscending x (insertionSortNonAscending xs))
      (insertionSortNonAscending xs)
      (RemoveFirst_insertSortedNonAscending ne_of_not_le x _)
      ih

theorem insertionSortStrictlyAscending_reordering (l : List α) (h : Unique l) :
    Reordering l (insertionSortStrictlyAscending l) := by
  induction l with
  | empty => exact Reordering.empty
  | firstElement x xs ih =>
    have hnin : ¬ In x (insertionSortStrictlyAscending xs) :=
      fun hin => h.not_in_head (insertionSortStrictlyAscending_subset xs hin)
    exact Reordering.cons x xs
      (insertSortedStrictlyAscending x (insertionSortStrictlyAscending xs))
      (insertionSortStrictlyAscending xs)
      (RemoveFirst_insertSortedStrictlyAscending x _ hnin)
      (ih h.tail)

theorem insertionSortStrictlyDescending_reordering (l : List α) (h : Unique l) :
    Reordering l (insertionSortStrictlyDescending l) := by
  induction l with
  | empty => exact Reordering.empty
  | firstElement x xs ih =>
    have hnin : ¬ In x (insertionSortStrictlyDescending xs) :=
      fun hin => h.not_in_head (insertionSortStrictlyDescending_subset xs hin)
    exact Reordering.cons x xs
      (insertSortedStrictlyDescending x (insertionSortStrictlyDescending xs))
      (insertionSortStrictlyDescending xs)
      (RemoveFirst_insertSortedStrictlyDescending x _ hnin)
      (ih h.tail)

theorem insertionSortStrictlyAscending_equivalent_reordering
    [Setoid α] (l : List α) (h : UniqueUpToEquivalence l) :
    Reordering l (insertionSortStrictlyAscending l) := by
  induction l with
  | empty => exact Reordering.empty
  | firstElement x xs ih =>
    have hnin : ¬ EquivalentIn x (insertionSortStrictlyAscending xs) :=
      fun hin => h.not_in_head (equivalentIn_of_subset
        (fun z hz => insertionSortStrictlyAscending_subset xs hz) hin)
    exact Reordering.cons x xs
      (insertSortedStrictlyAscending x (insertionSortStrictlyAscending xs))
      (insertionSortStrictlyAscending xs)
      (RemoveFirst_insertSortedStrictlyAscending_of_not_equivalent x _ hnin)
      (ih h.tail)

theorem insertionSortStrictlyDescending_equivalent_reordering
    [Setoid α] (l : List α) (h : UniqueUpToEquivalence l) :
    Reordering l (insertionSortStrictlyDescending l) := by
  induction l with
  | empty => exact Reordering.empty
  | firstElement x xs ih =>
    have hnin : ¬ EquivalentIn x (insertionSortStrictlyDescending xs) :=
      fun hin => h.not_in_head (equivalentIn_of_subset
        (fun z hz => insertionSortStrictlyDescending_subset xs hz) hin)
    exact Reordering.cons x xs
      (insertSortedStrictlyDescending x (insertionSortStrictlyDescending xs))
      (insertionSortStrictlyDescending xs)
      (RemoveFirst_insertSortedStrictlyDescending_of_not_equivalent x _ hnin)
      (ih h.tail)

end ZeroMath.Sequences.List
