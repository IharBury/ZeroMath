import ZeroMath.Numbers.OrdinalNatural.Peano
import ZeroMath.Sequences.List

namespace ZeroMath.Numbers.OrdinalNatural.Peano

namespace Lists

private abbrev List := Sequences.List

/-- The list is sorted in strictly ascending order (equal elements are not allowed). -/
inductive SortedStrictlyAscending : List Peano → Prop where
  | empty : SortedStrictlyAscending .empty
  | single (x : Peano) : SortedStrictlyAscending (.firstElement x .empty)
  | cons {x y : Peano} {ys : List Peano}
      (hlt : x < y)
      (hrest : SortedStrictlyAscending (.firstElement y ys)) :
      SortedStrictlyAscending (.firstElement x (.firstElement y ys))

instance decidableSortedStrictlyAscending :
    (l : List Peano) → Decidable (SortedStrictlyAscending l)
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
inductive SortedStrictlyDescending : List Peano → Prop where
  | empty : SortedStrictlyDescending .empty
  | single (x : Peano) : SortedStrictlyDescending (.firstElement x .empty)
  | cons {x y : Peano} {ys : List Peano}
      (hgt : x > y)
      (hrest : SortedStrictlyDescending (.firstElement y ys)) :
      SortedStrictlyDescending (.firstElement x (.firstElement y ys))

instance decidableSortedStrictlyDescending :
    (l : List Peano) → Decidable (SortedStrictlyDescending l)
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
inductive SortedNonDescending : List Peano → Prop where
  | empty : SortedNonDescending .empty
  | single (x : Peano) : SortedNonDescending (.firstElement x .empty)
  | cons {x y : Peano} {ys : List Peano}
      (hle : x ≤ y)
      (hrest : SortedNonDescending (.firstElement y ys)) :
      SortedNonDescending (.firstElement x (.firstElement y ys))

instance decidableSortedNonDescending :
    (l : List Peano) → Decidable (SortedNonDescending l)
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
inductive SortedNonAscending : List Peano → Prop where
  | empty : SortedNonAscending .empty
  | single (x : Peano) : SortedNonAscending (.firstElement x .empty)
  | cons {x y : Peano} {ys : List Peano}
      (hge : x ≥ y)
      (hrest : SortedNonAscending (.firstElement y ys)) :
      SortedNonAscending (.firstElement x (.firstElement y ys))

instance decidableSortedNonAscending :
    (l : List Peano) → Decidable (SortedNonAscending l)
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

theorem SortedStrictlyAscending.tail {x : Peano} {xs : List Peano}
    (h : SortedStrictlyAscending (.firstElement x xs)) : SortedStrictlyAscending xs := by
  cases h with
  | single => exact SortedStrictlyAscending.empty
  | cons _ hrest => exact hrest

theorem SortedStrictlyDescending.tail {x : Peano} {xs : List Peano}
    (h : SortedStrictlyDescending (.firstElement x xs)) : SortedStrictlyDescending xs := by
  cases h with
  | single => exact SortedStrictlyDescending.empty
  | cons _ hrest => exact hrest

theorem SortedNonDescending.tail {x : Peano} {xs : List Peano}
    (h : SortedNonDescending (.firstElement x xs)) : SortedNonDescending xs := by
  cases h with
  | single => exact SortedNonDescending.empty
  | cons _ hrest => exact hrest

theorem SortedNonAscending.tail {x : Peano} {xs : List Peano}
    (h : SortedNonAscending (.firstElement x xs)) : SortedNonAscending xs := by
  cases h with
  | single => exact SortedNonAscending.empty
  | cons _ hrest => exact hrest

theorem not_in_tail {x y : Peano} {ys : List Peano}
    (h : ¬ Sequences.List.In x (.firstElement y ys)) :
    ¬ Sequences.List.In x ys :=
  fun hin => h (Sequences.List.AnyElement.notFirst y ys hin)

/-- Insert `x` into a non-descending sorted list, preserving non-descending order. -/
def insertSortedNonDescending (x : Peano) :
    (l : List Peano) → SortedNonDescending l → List Peano
  | .empty, _ => .firstElement x .empty
  | .firstElement y ys, h =>
    if _ : x ≤ y then
      .firstElement x (.firstElement y ys)
    else
      .firstElement y (insertSortedNonDescending x ys h.tail)

/-- Insert `x` into a non-ascending sorted list, preserving non-ascending order. -/
def insertSortedNonAscending (x : Peano) :
    (l : List Peano) → SortedNonAscending l → List Peano
  | .empty, _ => .firstElement x .empty
  | .firstElement y ys, h =>
    if _ : x ≥ y then
      .firstElement x (.firstElement y ys)
    else
      .firstElement y (insertSortedNonAscending x ys h.tail)

/-- Insert `x` into a strictly ascending sorted list that does not yet contain `x`. -/
def insertSortedStrictlyAscending (x : Peano) :
    (l : List Peano) → SortedStrictlyAscending l → ¬ Sequences.List.In x l → List Peano
  | .empty, _, _ => .firstElement x .empty
  | .firstElement y ys, h, hnin =>
    if _ : x < y then
      .firstElement x (.firstElement y ys)
    else
      .firstElement y (insertSortedStrictlyAscending x ys h.tail (not_in_tail hnin))

/-- Insert `x` into a strictly descending sorted list that does not yet contain `x`. -/
def insertSortedStrictlyDescending (x : Peano) :
    (l : List Peano) → SortedStrictlyDescending l → ¬ Sequences.List.In x l → List Peano
  | .empty, _, _ => .firstElement x .empty
  | .firstElement y ys, h, hnin =>
    if _ : x > y then
      .firstElement x (.firstElement y ys)
    else
      .firstElement y (insertSortedStrictlyDescending x ys h.tail (not_in_tail hnin))

theorem le_of_not_le {a b : Peano} (h : ¬ a ≤ b) : b ≤ a := by
  cases trichotomy_or a b with
  | inl hlt => exact absurd (Or.inl hlt : a ≤ b) h
  | inr h' =>
    cases h' with
    | inl heq => exact absurd (Or.inr heq : a ≤ b) h
    | inr hlt => exact Or.inl hlt

theorem lt_of_not_lt_ne {a b : Peano} (hnlt : ¬ a < b) (hne : a ≠ b) : b < a := by
  cases trichotomy_or a b with
  | inl hlt => exact absurd hlt hnlt
  | inr h' =>
    cases h' with
    | inl heq => exact absurd heq hne
    | inr hlt => exact hlt

theorem ne_of_not_in_firstElement {x y : Peano} {ys : List Peano}
    (h : ¬ Sequences.List.In x (.firstElement y ys)) : x ≠ y :=
  fun heq => h (Sequences.List.AnyElement.first y ys heq.symm)

theorem SortedNonDescending.cons_of {x : Peano} {xs : List Peano}
    (hxs : SortedNonDescending xs)
    (hle : ∀ y ys, xs = .firstElement y ys → x ≤ y) :
    SortedNonDescending (.firstElement x xs) := by
  match xs with
  | .empty => exact SortedNonDescending.single x
  | .firstElement y ys => exact SortedNonDescending.cons (hle y ys rfl) hxs

theorem SortedNonAscending.cons_of {x : Peano} {xs : List Peano}
    (hxs : SortedNonAscending xs)
    (hge : ∀ y ys, xs = .firstElement y ys → x ≥ y) :
    SortedNonAscending (.firstElement x xs) := by
  match xs with
  | .empty => exact SortedNonAscending.single x
  | .firstElement y ys => exact SortedNonAscending.cons (hge y ys rfl) hxs

theorem SortedStrictlyAscending.cons_of {x : Peano} {xs : List Peano}
    (hxs : SortedStrictlyAscending xs)
    (hlt : ∀ y ys, xs = .firstElement y ys → x < y) :
    SortedStrictlyAscending (.firstElement x xs) := by
  match xs with
  | .empty => exact SortedStrictlyAscending.single x
  | .firstElement y ys => exact SortedStrictlyAscending.cons (hlt y ys rfl) hxs

theorem SortedStrictlyDescending.cons_of {x : Peano} {xs : List Peano}
    (hxs : SortedStrictlyDescending xs)
    (hgt : ∀ y ys, xs = .firstElement y ys → x > y) :
    SortedStrictlyDescending (.firstElement x xs) := by
  match xs with
  | .empty => exact SortedStrictlyDescending.single x
  | .firstElement y ys => exact SortedStrictlyDescending.cons (hgt y ys rfl) hxs

theorem insertSortedNonDescending_sorted (x : Peano) :
    (l : List Peano) → (h : SortedNonDescending l) →
      SortedNonDescending (insertSortedNonDescending x l h)
  | .empty, _ => SortedNonDescending.single x
  | .firstElement y ys, h => by
    unfold insertSortedNonDescending
    split
    · next hxy => exact SortedNonDescending.cons hxy h
    · next hnxy =>
      have ih := insertSortedNonDescending_sorted x ys h.tail
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

theorem insertSortedNonAscending_sorted (x : Peano) :
    (l : List Peano) → (h : SortedNonAscending l) →
      SortedNonAscending (insertSortedNonAscending x l h)
  | .empty, _ => SortedNonAscending.single x
  | .firstElement y ys, h => by
    unfold insertSortedNonAscending
    split
    · next hxy => exact SortedNonAscending.cons hxy h
    · next hnxy =>
      have ih := insertSortedNonAscending_sorted x ys h.tail
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

theorem insertSortedStrictlyAscending_sorted (x : Peano) :
    (l : List Peano) → (h : SortedStrictlyAscending l) → (hnin : ¬ Sequences.List.In x l) →
      SortedStrictlyAscending (insertSortedStrictlyAscending x l h hnin)
  | .empty, _, _ => SortedStrictlyAscending.single x
  | .firstElement y ys, h, hnin => by
    unfold insertSortedStrictlyAscending
    split
    · next hxy => exact SortedStrictlyAscending.cons hxy h
    · next hnxy =>
      have ih := insertSortedStrictlyAscending_sorted x ys h.tail (not_in_tail hnin)
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

theorem insertSortedStrictlyDescending_sorted (x : Peano) :
    (l : List Peano) → (h : SortedStrictlyDescending l) → (hnin : ¬ Sequences.List.In x l) →
      SortedStrictlyDescending (insertSortedStrictlyDescending x l h hnin)
  | .empty, _, _ => SortedStrictlyDescending.single x
  | .firstElement y ys, h, hnin => by
    unfold insertSortedStrictlyDescending
    split
    · next hxy => exact SortedStrictlyDescending.cons hxy h
    · next hnxy =>
      have ih := insertSortedStrictlyDescending_sorted x ys h.tail (not_in_tail hnin)
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

/-- Auxiliary insertion sort returning a non-descending sorted list with proof. -/
def insertionSortNonDescendingWithProof :
    List Peano → { l : List Peano // SortedNonDescending l }
  | .empty => ⟨.empty, SortedNonDescending.empty⟩
  | .firstElement x xs =>
    match insertionSortNonDescendingWithProof xs with
    | ⟨ys, hys⟩ =>
      ⟨insertSortedNonDescending x ys hys, insertSortedNonDescending_sorted x ys hys⟩

/-- Sort a list into non-descending order using insertion sort. -/
def insertionSortNonDescending (l : List Peano) : List Peano :=
  (insertionSortNonDescendingWithProof l).val

/-- The result of `insertionSortNonDescending` is sorted in non-descending order. -/
theorem insertionSortNonDescending_sorted (l : List Peano) :
    SortedNonDescending (insertionSortNonDescending l) :=
  (insertionSortNonDescendingWithProof l).property

/-- Auxiliary insertion sort returning a non-ascending sorted list with proof. -/
def insertionSortNonAscendingWithProof :
    List Peano → { l : List Peano // SortedNonAscending l }
  | .empty => ⟨.empty, SortedNonAscending.empty⟩
  | .firstElement x xs =>
    match insertionSortNonAscendingWithProof xs with
    | ⟨ys, hys⟩ =>
      ⟨insertSortedNonAscending x ys hys, insertSortedNonAscending_sorted x ys hys⟩

/-- Sort a list into non-ascending order using insertion sort. -/
def insertionSortNonAscending (l : List Peano) : List Peano :=
  (insertionSortNonAscendingWithProof l).val

/-- The result of `insertionSortNonAscending` is sorted in non-ascending order. -/
theorem insertionSortNonAscending_sorted (l : List Peano) :
    SortedNonAscending (insertionSortNonAscending l) :=
  (insertionSortNonAscendingWithProof l).property

theorem in_of_in_insertSortedStrictlyAscending (x : Peano) :
    (l : List Peano) → (h : SortedStrictlyAscending l) →
      (hnin : ¬ Sequences.List.In x l) →
      {z : Peano} → Sequences.List.In z (insertSortedStrictlyAscending x l h hnin) →
        z = x ∨ Sequences.List.In z l
  | .empty, _, _, z, hin => by
    simp only [insertSortedStrictlyAscending] at hin
    cases hin with
    | first _ _ heq => exact Or.inl heq.symm
    | notFirst _ _ h => cases h
  | .firstElement y ys, h, hnin, z, hin => by
    unfold insertSortedStrictlyAscending at hin
    split at hin
    · next _ =>
      cases hin with
      | first _ _ heq => exact Or.inl heq.symm
      | notFirst _ _ hin' => exact Or.inr hin'
    · next _ =>
      cases hin with
      | first _ _ heq =>
        exact Or.inr (Sequences.List.AnyElement.first y ys heq)
      | notFirst _ _ hin' =>
        match in_of_in_insertSortedStrictlyAscending x ys h.tail (not_in_tail hnin) hin' with
        | Or.inl heq => exact Or.inl heq
        | Or.inr hinys => exact Or.inr (Sequences.List.AnyElement.notFirst y ys hinys)

theorem in_of_in_insertSortedStrictlyDescending (x : Peano) :
    (l : List Peano) → (h : SortedStrictlyDescending l) →
      (hnin : ¬ Sequences.List.In x l) →
      {z : Peano} → Sequences.List.In z (insertSortedStrictlyDescending x l h hnin) →
        z = x ∨ Sequences.List.In z l
  | .empty, _, _, z, hin => by
    simp only [insertSortedStrictlyDescending] at hin
    cases hin with
    | first _ _ heq => exact Or.inl heq.symm
    | notFirst _ _ h => cases h
  | .firstElement y ys, h, hnin, z, hin => by
    unfold insertSortedStrictlyDescending at hin
    split at hin
    · next _ =>
      cases hin with
      | first _ _ heq => exact Or.inl heq.symm
      | notFirst _ _ hin' => exact Or.inr hin'
    · next _ =>
      cases hin with
      | first _ _ heq =>
        exact Or.inr (Sequences.List.AnyElement.first y ys heq)
      | notFirst _ _ hin' =>
        match in_of_in_insertSortedStrictlyDescending x ys h.tail (not_in_tail hnin) hin' with
        | Or.inl heq => exact Or.inl heq
        | Or.inr hinys => exact Or.inr (Sequences.List.AnyElement.notFirst y ys hinys)

/-- Internal helper that also tracks membership so the unique-element precondition
    can be discharged when inserting into the recursively sorted tail. -/
def insertionSortStrictlyAscendingAux :
    (l : List Peano) → Sequences.List.Unique l →
      { l' : List Peano //
        SortedStrictlyAscending l' ∧
          (∀ z, Sequences.List.In z l' → Sequences.List.In z l) }
  | .empty, _ =>
    ⟨.empty, SortedStrictlyAscending.empty, fun _ hin => by cases hin⟩
  | .firstElement x xs, huniq =>
    match insertionSortStrictlyAscendingAux xs huniq.tail with
    | ⟨ys, hys, hsubset⟩ =>
      have hnin_ys : ¬ Sequences.List.In x ys :=
        fun hin => huniq.not_in_head (hsubset x hin)
      ⟨insertSortedStrictlyAscending x ys hys hnin_ys,
        insertSortedStrictlyAscending_sorted x ys hys hnin_ys,
        fun z hin =>
          match in_of_in_insertSortedStrictlyAscending x ys hys hnin_ys hin with
          | Or.inl heq =>
            Sequences.List.AnyElement.first x xs (heq.symm)
          | Or.inr hinys =>
            Sequences.List.AnyElement.notFirst x xs (hsubset z hinys)⟩

/-- Auxiliary insertion sort returning a strictly ascending sorted list with proof.
    Requires that all elements of the input are unique. -/
def insertionSortStrictlyAscendingWithProof (l : List Peano)
    (h : Sequences.List.Unique l) :
    { l' : List Peano // SortedStrictlyAscending l' } :=
  match insertionSortStrictlyAscendingAux l h with
  | ⟨ys, hys, _⟩ => ⟨ys, hys⟩

/-- Sort a list with unique elements into strictly ascending order using insertion sort. -/
def insertionSortStrictlyAscending (l : List Peano) (h : Sequences.List.Unique l) :
    List Peano :=
  (insertionSortStrictlyAscendingWithProof l h).val

/-- The result of `insertionSortStrictlyAscending` is sorted in strictly ascending order. -/
theorem insertionSortStrictlyAscending_sorted (l : List Peano)
    (h : Sequences.List.Unique l) :
    SortedStrictlyAscending (insertionSortStrictlyAscending l h) :=
  (insertionSortStrictlyAscendingWithProof l h).property

/-- Internal helper that also tracks membership so the unique-element precondition
    can be discharged when inserting into the recursively sorted tail. -/
def insertionSortStrictlyDescendingAux :
    (l : List Peano) → Sequences.List.Unique l →
      { l' : List Peano //
        SortedStrictlyDescending l' ∧
          (∀ z, Sequences.List.In z l' → Sequences.List.In z l) }
  | .empty, _ =>
    ⟨.empty, SortedStrictlyDescending.empty, fun _ hin => by cases hin⟩
  | .firstElement x xs, huniq =>
    match insertionSortStrictlyDescendingAux xs huniq.tail with
    | ⟨ys, hys, hsubset⟩ =>
      have hnin_ys : ¬ Sequences.List.In x ys :=
        fun hin => huniq.not_in_head (hsubset x hin)
      ⟨insertSortedStrictlyDescending x ys hys hnin_ys,
        insertSortedStrictlyDescending_sorted x ys hys hnin_ys,
        fun z hin =>
          match in_of_in_insertSortedStrictlyDescending x ys hys hnin_ys hin with
          | Or.inl heq =>
            Sequences.List.AnyElement.first x xs (heq.symm)
          | Or.inr hinys =>
            Sequences.List.AnyElement.notFirst x xs (hsubset z hinys)⟩

/-- Auxiliary insertion sort returning a strictly descending sorted list with proof.
    Requires that all elements of the input are unique. -/
def insertionSortStrictlyDescendingWithProof (l : List Peano)
    (h : Sequences.List.Unique l) :
    { l' : List Peano // SortedStrictlyDescending l' } :=
  match insertionSortStrictlyDescendingAux l h with
  | ⟨ys, hys, _⟩ => ⟨ys, hys⟩

/-- Sort a list with unique elements into strictly descending order using insertion sort. -/
def insertionSortStrictlyDescending (l : List Peano) (h : Sequences.List.Unique l) :
    List Peano :=
  (insertionSortStrictlyDescendingWithProof l h).val

/-- The result of `insertionSortStrictlyDescending` is sorted in strictly descending order. -/
theorem insertionSortStrictlyDescending_sorted (l : List Peano)
    (h : Sequences.List.Unique l) :
    SortedStrictlyDescending (insertionSortStrictlyDescending l h) :=
  (insertionSortStrictlyDescendingWithProof l h).property

end Lists

end ZeroMath.Numbers.OrdinalNatural.Peano
