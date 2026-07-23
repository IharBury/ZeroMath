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

end Lists

end ZeroMath.Numbers.OrdinalNatural.Peano
