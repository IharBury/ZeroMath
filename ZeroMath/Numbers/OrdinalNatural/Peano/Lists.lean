import ZeroMath.Numbers.OrdinalNatural.Peano
import ZeroMath.Sequences.List

namespace ZeroMath.Numbers.OrdinalNatural.Peano

namespace Lists

private abbrev List := Sequences.List

/-- The list is sorted in strictly ascending order (equal elements are not allowed). -/
inductive SortedAscending : List Peano → Prop where
  | empty : SortedAscending .empty
  | single (x : Peano) : SortedAscending (.firstElement x .empty)
  | cons {x y : Peano} {ys : List Peano}
      (hlt : x < y)
      (hrest : SortedAscending (.firstElement y ys)) :
      SortedAscending (.firstElement x (.firstElement y ys))

instance decidableSortedAscending :
    (l : List Peano) → Decidable (SortedAscending l)
  | .empty => isTrue SortedAscending.empty
  | .firstElement x .empty => isTrue (SortedAscending.single x)
  | .firstElement x (.firstElement y ys) =>
      match (inferInstance : Decidable (x < y)),
          decidableSortedAscending (.firstElement y ys) with
      | isTrue hlt, isTrue hrest =>
          isTrue (SortedAscending.cons hlt hrest)
      | isFalse hnlt, _ =>
          isFalse fun h => by
            cases h with
            | cons hlt _ => exact hnlt hlt
      | _, isFalse hnrest =>
          isFalse fun h => by
            cases h with
            | cons _ hrest => exact hnrest hrest

end Lists

end ZeroMath.Numbers.OrdinalNatural.Peano
