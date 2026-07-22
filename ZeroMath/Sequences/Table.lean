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

/-- Rows of a one-column table built from `col` (top to bottom). -/
def singleColumnRows {α : Type u} : List α → List (List α)
  | .empty => .empty
  | .firstElement x xs => .firstElement (.firstElement x .empty) (singleColumnRows xs)

theorem allRowsHaveSameLength_singleColumnRows {α : Type u} (col : List α) :
    AllRowsHaveSameLength (singleColumnRows col) := by
  induction col with
  | empty => exact AllRowsHaveSameLength.empty
  | firstElement x xs ih =>
    cases xs with
    | empty => exact AllRowsHaveSameLength.singleRow _
    | firstElement _ _ => exact AllRowsHaveSameLength.firstRow rfl ih

/-- A table consisting of a single column whose cells are `col` (top to bottom).
The empty list yields the empty table. -/
def singleColumn {α : Type u} (col : List α) : Table α :=
  ⟨singleColumnRows col, allRowsHaveSameLength_singleColumnRows col⟩

/-- Some row in the table satisfies `p`. -/
def AnyRow {α : Type u} (p : List α → Prop) (t : Table α) : Prop :=
  List.AnyElement p t.rows

/-- Some cell in the table satisfies `p`. -/
def AnyElement {α : Type u} (p : α → Prop) (t : Table α) : Prop :=
  AnyRow (fun row => List.AnyElement p row) t

/-- `row` is length-compatible with the rows of `t`: vacuously true when `t` is
empty; otherwise `row` has the same length as the first existing row. -/
def CompatibleRowLengthWithTable {α : Type u} (row : List α) (t : Table α) : Prop :=
  match t.rows with
  | List.empty => True
  | List.firstElement firstRow _ => List.SameLength row firstRow

/-- Prepend `row` to the front of `t`.
When `t` is empty this always succeeds (and yields `singleRow row`).
When `t` is non-empty, `hSame` must show that `row` has the same length as the
first existing row. -/
def prependRow {α : Type u} :
    (row : List α) → (t : Table α) → CompatibleRowLengthWithTable row t → Table α
  | row, ⟨List.empty, _⟩, _ =>
      singleRow row
  | row, ⟨List.firstElement firstRow rest, hRest⟩, hSame =>
      ⟨List.firstElement row (List.firstElement firstRow rest),
       AllRowsHaveSameLength.firstRow hSame hRest⟩

/-- `col` is height-compatible with `t`: vacuously true when `t` is empty;
otherwise `col` has the same length as the list of rows. -/
def CompatibleColumnLengthWithTable {α : Type u} (col : List α) (t : Table α) : Prop :=
  match t.rows with
  | List.empty => True
  | List.firstElement firstRow rest =>
      col.length = (List.firstElement firstRow rest).length

/-- Prepend each cell of `col` (top to bottom) to the front of the corresponding
row of `rows`. Requires `col` and `rows` to have the same length. -/
def prependColumnToRows {α : Type u} :
    (col : List α) → (rows : List (List α)) → col.length = rows.length → List (List α)
  | .empty, .empty, _ => .empty
  | .firstElement c cs, .firstElement r rs, h =>
      .firstElement (.firstElement c r)
        (prependColumnToRows cs rs
          (Numbers.CardinalNatural.Peano.add_right_cancel
            Numbers.CardinalNatural.Peano.one cs.length rs.length h))
  | .empty, .firstElement _ rs, h =>
      False.elim (Numbers.CardinalNatural.Peano.successor_ne_zero rs.length h.symm)
  | .firstElement _ cs, .empty, h =>
      False.elim (Numbers.CardinalNatural.Peano.successor_ne_zero cs.length h)

theorem allRowsHaveSameLength_prependColumnToRows {α : Type u} :
    (col : List α) → (rows : List (List α)) →
    (hLen : col.length = rows.length) →
    AllRowsHaveSameLength rows →
    AllRowsHaveSameLength (prependColumnToRows col rows hLen)
  | .empty, .empty, _, _ => AllRowsHaveSameLength.empty
  | .empty, .firstElement _ rs, hLen, _ =>
      False.elim (Numbers.CardinalNatural.Peano.successor_ne_zero rs.length hLen.symm)
  | .firstElement _ cs, .empty, hLen, _ =>
      False.elim (Numbers.CardinalNatural.Peano.successor_ne_zero cs.length hLen)
  | .firstElement c cs, .firstElement r rs, hLen, hRows => by
    cases hRows with
    | singleRow row =>
      cases cs with
      | empty => exact AllRowsHaveSameLength.singleRow _
      | firstElement _ cs' =>
        exact False.elim
          (Numbers.CardinalNatural.Peano.successor_ne_zero cs'.length
            (Numbers.CardinalNatural.Peano.add_right_cancel
              Numbers.CardinalNatural.Peano.one _ _ hLen))
    | firstRow hSame hRest =>
      rename_i row2 rest
      cases cs with
      | empty =>
        exact False.elim
          (Numbers.CardinalNatural.Peano.successor_ne_zero rest.length
            (Numbers.CardinalNatural.Peano.add_right_cancel
              Numbers.CardinalNatural.Peano.one _ _ hLen).symm)
      | firstElement c' cs' =>
        exact AllRowsHaveSameLength.firstRow
          (List.sameLength_firstElement hSame)
          (allRowsHaveSameLength_prependColumnToRows
            (List.firstElement c' cs') (List.firstElement row2 rest)
            (Numbers.CardinalNatural.Peano.add_right_cancel
              Numbers.CardinalNatural.Peano.one _ _ hLen)
            hRest)

/-- Prepend `col` to the left of `t`.
When `t` is empty this always succeeds (and yields `singleColumn col`).
When `t` is non-empty, `hSame` must show that `col` has the same length as the
list of rows. -/
def prependColumn {α : Type u} :
    (col : List α) → (t : Table α) → CompatibleColumnLengthWithTable col t → Table α
  | col, ⟨List.empty, _⟩, _ =>
      singleColumn col
  | col, ⟨List.firstElement firstRow rest, hRest⟩, hSame =>
      ⟨prependColumnToRows col (List.firstElement firstRow rest) hSame,
       allRowsHaveSameLength_prependColumnToRows col
         (List.firstElement firstRow rest) hSame hRest⟩

end Table

end ZeroMath.Sequences
