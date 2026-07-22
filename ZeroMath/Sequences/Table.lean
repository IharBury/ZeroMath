import ZeroMath.Sequences.List

namespace ZeroMath.Sequences

namespace Table

/-- Every row in a list of rows has the same length. -/
inductive AllSameLength {α : Type u} : List (List α) → Prop where
  | empty : AllSameLength List.empty
  | singleton (row : List α) : AllSameLength (List.firstElement row List.empty)
  | cons {row1 row2 : List α} {rest : List (List α)}
      (hSame : List.SameLength row1 row2)
      (hRest : AllSameLength (List.firstElement row2 rest)) :
      AllSameLength (List.firstElement row1 (List.firstElement row2 rest))

instance decidableAllSameLength {α : Type u} :
    (rows : List (List α)) → Decidable (AllSameLength rows)
  | .empty => isTrue AllSameLength.empty
  | .firstElement row .empty => isTrue (AllSameLength.singleton row)
  | .firstElement row1 (.firstElement row2 rest) =>
      match (inferInstance : Decidable (List.SameLength row1 row2)),
          decidableAllSameLength (List.firstElement row2 rest) with
      | isTrue hSame, isTrue hRest =>
          isTrue (AllSameLength.cons hSame hRest)
      | isFalse hNotSame, _ =>
          isFalse fun h => by
            cases h with
            | cons hSame _ => exact hNotSame hSame
      | _, isFalse hNotRest =>
          isFalse fun h => by
            cases h with
            | cons _ hRest => exact hNotRest hRest

end Table

/-- A table is a list of rows where each row is a list of cells, and every row
has the same length. -/
structure Table (α : Type u) where
  rows : List (List α)
  allSameLength : Table.AllSameLength rows

namespace Table

instance decidableEq {α : Type u} [DecidableEq α] : DecidableEq (Table α) :=
  fun a b =>
    if h : a.rows = b.rows then
      isTrue (by
        cases a
        cases b
        cases h
        rfl)
    else
      isFalse (fun hEq => by
        cases hEq
        exact h rfl)

def empty {α : Type u} : Table α :=
  ⟨List.empty, AllSameLength.empty⟩

def singleton {α : Type u} (row : List α) : Table α :=
  ⟨List.firstElement row List.empty, AllSameLength.singleton row⟩

end Table

end ZeroMath.Sequences
