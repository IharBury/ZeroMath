import ZeroMath.Sequences.List

namespace ZeroMath.Sequences

namespace Table

/-- Every row in a list of rows has the same length. -/
inductive AllRowsHaveSameLength {α : Type u} : List (List α) → Prop where
  | empty : AllRowsHaveSameLength List.empty
  | singleRow (row : List α) : AllRowsHaveSameLength (List.firstElement row List.empty)
  | firstRow {row1 row2 : List α} {rest : List (List α)}
      (hSame : List.SameLength row1 row2)
      (hRest : AllRowsHaveSameLength (List.firstElement row2 rest)) :
      AllRowsHaveSameLength (List.firstElement row1 (List.firstElement row2 rest))

instance decidableAllRowsHaveSameLength {α : Type u} :
    (rows : List (List α)) → Decidable (AllRowsHaveSameLength rows)
  | .empty => isTrue AllRowsHaveSameLength.empty
  | .firstElement row .empty => isTrue (AllRowsHaveSameLength.singleRow row)
  | .firstElement row1 (.firstElement row2 rest) =>
      match (inferInstance : Decidable (List.SameLength row1 row2)),
          decidableAllRowsHaveSameLength (List.firstElement row2 rest) with
      | isTrue hSame, isTrue hRest =>
          isTrue (AllRowsHaveSameLength.firstRow hSame hRest)
      | isFalse hNotSame, _ =>
          isFalse fun h => by
            cases h with
            | firstRow hSame _ => exact hNotSame hSame
      | _, isFalse hNotRest =>
          isFalse fun h => by
            cases h with
            | firstRow _ hRest => exact hNotRest hRest

end Table

/-- A table is a list of rows where each row is a list of cells, and every row
has the same length. -/
structure Table (α : Type u) where
  rows : List (List α)
  allRowsHaveSameLength : Table.AllRowsHaveSameLength rows

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
  ⟨List.empty, AllRowsHaveSameLength.empty⟩

def singleRow {α : Type u} (row : List α) : Table α :=
  ⟨List.firstElement row List.empty, AllRowsHaveSameLength.singleRow row⟩

end Table

end ZeroMath.Sequences
