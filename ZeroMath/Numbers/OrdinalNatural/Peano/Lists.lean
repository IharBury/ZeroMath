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

end Lists

end ZeroMath.Numbers.OrdinalNatural.Peano
