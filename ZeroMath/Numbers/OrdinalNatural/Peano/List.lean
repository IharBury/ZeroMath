import ZeroMath.Numbers.OrdinalNatural.Peano
import ZeroMath.Sequences.List

namespace ZeroMath.Numbers.OrdinalNatural.Peano

namespace List

/-- The list is sorted in non-decreasing (ascending) order. -/
inductive SortedAscending : Sequences.List Peano → Prop where
  | empty : SortedAscending Sequences.List.empty
  | single (x : Peano) : SortedAscending (Sequences.List.firstElement x Sequences.List.empty)
  | cons {x y : Peano} {ys : Sequences.List Peano}
      (hle : x ≤ y)
      (hrest : SortedAscending (Sequences.List.firstElement y ys)) :
      SortedAscending (Sequences.List.firstElement x (Sequences.List.firstElement y ys))

instance decidableSortedAscending :
    (l : Sequences.List Peano) → Decidable (SortedAscending l)
  | .empty => isTrue SortedAscending.empty
  | .firstElement x .empty => isTrue (SortedAscending.single x)
  | .firstElement x (.firstElement y ys) =>
      match (inferInstance : Decidable (x ≤ y)),
          decidableSortedAscending (.firstElement y ys) with
      | isTrue hle, isTrue hrest =>
          isTrue (SortedAscending.cons hle hrest)
      | isFalse hnle, _ =>
          isFalse fun h => by
            cases h with
            | cons hle _ => exact hnle hle
      | _, isFalse hnrest =>
          isFalse fun h => by
            cases h with
            | cons _ hrest => exact hnrest hrest

end List

end ZeroMath.Numbers.OrdinalNatural.Peano
