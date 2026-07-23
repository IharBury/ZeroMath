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

end Lists

end ZeroMath.Numbers.OrdinalNatural.Peano
