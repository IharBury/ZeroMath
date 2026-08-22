import ZeroMath.Numbers.Integer.Peano
import ZeroMath.Sequences.List.Sorting

namespace ZeroMath.Numbers.Integer.Peano

namespace Lists

abbrev SortedStrictlyAscending := Sequences.List.SortedStrictlyAscending (α := Peano)
abbrev SortedStrictlyDescending := Sequences.List.SortedStrictlyDescending (α := Peano)
abbrev SortedNonDescending := Sequences.List.SortedNonDescending (α := Peano)
abbrev SortedNonAscending := Sequences.List.SortedNonAscending (α := Peano)

def insertSortedNonDescending (x : Peano) (l : Sequences.List Peano) :
    Sequences.List Peano :=
  Sequences.List.insertSortedNonDescending x l

def insertSortedNonAscending (x : Peano) (l : Sequences.List Peano) :
    Sequences.List Peano :=
  Sequences.List.insertSortedNonAscending x l

def insertSortedStrictlyAscending (x : Peano) (l : Sequences.List Peano) :
    Sequences.List Peano :=
  Sequences.List.insertSortedStrictlyAscending x l

def insertSortedStrictlyDescending (x : Peano) (l : Sequences.List Peano) :
    Sequences.List Peano :=
  Sequences.List.insertSortedStrictlyDescending x l

def insertionSortNonDescending (l : Sequences.List Peano) : Sequences.List Peano :=
  Sequences.List.insertionSortNonDescending l

def insertionSortNonAscending (l : Sequences.List Peano) : Sequences.List Peano :=
  Sequences.List.insertionSortNonAscending l

def insertionSortStrictlyAscending (l : Sequences.List Peano)
    (h : Sequences.List.Unique l) : Sequences.List Peano :=
  (Sequences.List.insertionSortStrictlyAscendingWithProof lt_of_not_lt_ne l h).val

def insertionSortStrictlyDescending (l : Sequences.List Peano)
    (h : Sequences.List.Unique l) : Sequences.List Peano :=
  (Sequences.List.insertionSortStrictlyDescendingWithProof lt_of_not_lt_ne l h).val

theorem insertSortedNonDescending_sorted (x : Peano) (l : Sequences.List Peano)
    (h : SortedNonDescending l) :
    SortedNonDescending (insertSortedNonDescending x l) :=
  Sequences.List.insertSortedNonDescending_sorted le_of_not_le x l h

theorem insertSortedNonAscending_sorted (x : Peano) (l : Sequences.List Peano)
    (h : SortedNonAscending l) :
    SortedNonAscending (insertSortedNonAscending x l) :=
  Sequences.List.insertSortedNonAscending_sorted le_of_not_le x l h

theorem insertSortedStrictlyAscending_sorted (x : Peano) (l : Sequences.List Peano)
    (h : SortedStrictlyAscending l) (hnin : ¬ Sequences.List.In x l) :
    SortedStrictlyAscending (insertSortedStrictlyAscending x l) :=
  Sequences.List.insertSortedStrictlyAscending_sorted lt_of_not_lt_ne x l h hnin

theorem insertSortedStrictlyDescending_sorted (x : Peano) (l : Sequences.List Peano)
    (h : SortedStrictlyDescending l) (hnin : ¬ Sequences.List.In x l) :
    SortedStrictlyDescending (insertSortedStrictlyDescending x l) :=
  Sequences.List.insertSortedStrictlyDescending_sorted lt_of_not_lt_ne x l h hnin

theorem insertionSortNonDescending_sorted (l : Sequences.List Peano) :
    SortedNonDescending (insertionSortNonDescending l) :=
  Sequences.List.insertionSortNonDescending_sorted le_of_not_le l

theorem insertionSortNonAscending_sorted (l : Sequences.List Peano) :
    SortedNonAscending (insertionSortNonAscending l) :=
  Sequences.List.insertionSortNonAscending_sorted le_of_not_le l

theorem insertionSortStrictlyAscending_sorted (l : Sequences.List Peano)
    (h : Sequences.List.Unique l) :
    SortedStrictlyAscending (insertionSortStrictlyAscending l h) :=
  Sequences.List.insertionSortStrictlyAscending_sorted lt_of_not_lt_ne l h

theorem insertionSortStrictlyDescending_sorted (l : Sequences.List Peano)
    (h : Sequences.List.Unique l) :
    SortedStrictlyDescending (insertionSortStrictlyDescending l h) :=
  Sequences.List.insertionSortStrictlyDescending_sorted lt_of_not_lt_ne l h

theorem insertionSortNonDescending_reordering (l : Sequences.List Peano) :
    Sequences.List.Reordering l (insertionSortNonDescending l) :=
  Sequences.List.insertionSortNonDescending_reordering ne_of_not_le l

theorem insertionSortNonAscending_reordering (l : Sequences.List Peano) :
    Sequences.List.Reordering l (insertionSortNonAscending l) :=
  Sequences.List.insertionSortNonAscending_reordering ne_of_not_le l

theorem insertionSortStrictlyAscending_reordering (l : Sequences.List Peano)
    (h : Sequences.List.Unique l) :
    Sequences.List.Reordering l (insertionSortStrictlyAscending l h) :=
  Sequences.List.insertionSortStrictlyAscending_reordering l h

theorem insertionSortStrictlyDescending_reordering (l : Sequences.List Peano)
    (h : Sequences.List.Unique l) :
    Sequences.List.Reordering l (insertionSortStrictlyDescending l h) :=
  Sequences.List.insertionSortStrictlyDescending_reordering l h

example : insertionSortNonDescending .empty = .empty := rfl

example : insertionSortNonDescending (.firstElement one (.firstElement minusOne .empty)) =
  .firstElement minusOne (.firstElement one .empty) := rfl

example : insertionSortNonDescending
    (.firstElement two (.firstElement minusOne (.firstElement zero .empty))) =
  .firstElement minusOne (.firstElement zero (.firstElement two .empty)) := rfl

end Lists

end ZeroMath.Numbers.Integer.Peano
