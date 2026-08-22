import ZeroMath.Numbers.CardinalNatural.Decimal
import ZeroMath.Sequences.List.Sorting

namespace ZeroMath.Numbers.CardinalNatural.Decimal

namespace Lists

abbrev SortedStrictlyAscending := Sequences.List.SortedStrictlyAscending (α := Decimal)
abbrev SortedStrictlyDescending := Sequences.List.SortedStrictlyDescending (α := Decimal)
abbrev SortedNonDescending := Sequences.List.SortedNonDescending (α := Decimal)
abbrev SortedNonAscending := Sequences.List.SortedNonAscending (α := Decimal)

def insertSortedNonDescending (x : Decimal) (l : Sequences.List Decimal) :
    Sequences.List Decimal :=
  Sequences.List.insertSortedNonDescending x l

def insertSortedNonAscending (x : Decimal) (l : Sequences.List Decimal) :
    Sequences.List Decimal :=
  Sequences.List.insertSortedNonAscending x l

def insertSortedStrictlyAscending (x : Decimal) (l : Sequences.List Decimal) :
    Sequences.List Decimal :=
  Sequences.List.insertSortedStrictlyAscending x l

def insertSortedStrictlyDescending (x : Decimal) (l : Sequences.List Decimal) :
    Sequences.List Decimal :=
  Sequences.List.insertSortedStrictlyDescending x l

def insertionSortNonDescending (l : Sequences.List Decimal) : Sequences.List Decimal :=
  Sequences.List.insertionSortNonDescending l

def insertionSortNonAscending (l : Sequences.List Decimal) : Sequences.List Decimal :=
  Sequences.List.insertionSortNonAscending l

def insertionSortStrictlyAscending (l : Sequences.List Decimal)
    (h : Sequences.List.UniqueUpToEquivalence l) : Sequences.List Decimal :=
  (Sequences.List.insertionSortStrictlyAscendingEquivalentWithProof
    lt_of_not_lt_not_equivalent l h).val

def insertionSortStrictlyDescending (l : Sequences.List Decimal)
    (h : Sequences.List.UniqueUpToEquivalence l) : Sequences.List Decimal :=
  (Sequences.List.insertionSortStrictlyDescendingEquivalentWithProof
    lt_of_not_lt_not_equivalent l h).val

theorem insertSortedNonDescending_sorted (x : Decimal) (l : Sequences.List Decimal)
    (h : SortedNonDescending l) :
    SortedNonDescending (insertSortedNonDescending x l) :=
  Sequences.List.insertSortedNonDescending_sorted le_of_not_le x l h

theorem insertSortedNonAscending_sorted (x : Decimal) (l : Sequences.List Decimal)
    (h : SortedNonAscending l) :
    SortedNonAscending (insertSortedNonAscending x l) :=
  Sequences.List.insertSortedNonAscending_sorted le_of_not_le x l h

theorem insertSortedStrictlyAscending_sorted (x : Decimal)
    (l : Sequences.List Decimal) (h : SortedStrictlyAscending l)
    (hnin : ¬ Sequences.List.EquivalentIn x l) :
    SortedStrictlyAscending (insertSortedStrictlyAscending x l) :=
  Sequences.List.insertSortedStrictlyAscending_equivalent_sorted
    lt_of_not_lt_not_equivalent x l h hnin

theorem insertSortedStrictlyDescending_sorted (x : Decimal)
    (l : Sequences.List Decimal) (h : SortedStrictlyDescending l)
    (hnin : ¬ Sequences.List.EquivalentIn x l) :
    SortedStrictlyDescending (insertSortedStrictlyDescending x l) :=
  Sequences.List.insertSortedStrictlyDescending_equivalent_sorted
    lt_of_not_lt_not_equivalent x l h hnin

theorem insertionSortNonDescending_sorted (l : Sequences.List Decimal) :
    SortedNonDescending (insertionSortNonDescending l) :=
  Sequences.List.insertionSortNonDescending_sorted le_of_not_le l

theorem insertionSortNonAscending_sorted (l : Sequences.List Decimal) :
    SortedNonAscending (insertionSortNonAscending l) :=
  Sequences.List.insertionSortNonAscending_sorted le_of_not_le l

theorem insertionSortStrictlyAscending_sorted (l : Sequences.List Decimal)
    (h : Sequences.List.UniqueUpToEquivalence l) :
    SortedStrictlyAscending (insertionSortStrictlyAscending l h) :=
  Sequences.List.insertionSortStrictlyAscending_equivalent_sorted
    lt_of_not_lt_not_equivalent l h

theorem insertionSortStrictlyDescending_sorted (l : Sequences.List Decimal)
    (h : Sequences.List.UniqueUpToEquivalence l) :
    SortedStrictlyDescending (insertionSortStrictlyDescending l h) :=
  Sequences.List.insertionSortStrictlyDescending_equivalent_sorted
    lt_of_not_lt_not_equivalent l h

theorem insertionSortNonDescending_reordering (l : Sequences.List Decimal) :
    Sequences.List.Reordering l (insertionSortNonDescending l) :=
  Sequences.List.insertionSortNonDescending_reordering ne_of_not_le l

theorem insertionSortNonAscending_reordering (l : Sequences.List Decimal) :
    Sequences.List.Reordering l (insertionSortNonAscending l) :=
  Sequences.List.insertionSortNonAscending_reordering ne_of_not_le l

theorem insertionSortStrictlyAscending_reordering (l : Sequences.List Decimal)
    (h : Sequences.List.UniqueUpToEquivalence l) :
    Sequences.List.Reordering l (insertionSortStrictlyAscending l h) :=
  Sequences.List.insertionSortStrictlyAscending_equivalent_reordering l h

theorem insertionSortStrictlyDescending_reordering (l : Sequences.List Decimal)
    (h : Sequences.List.UniqueUpToEquivalence l) :
    Sequences.List.Reordering l (insertionSortStrictlyDescending l h) :=
  Sequences.List.insertionSortStrictlyDescending_equivalent_reordering l h

example : insertionSortNonDescending .empty = .empty := rfl

example : insertionSortNonDescending (.firstElement one (.firstElement zero .empty)) =
  .firstElement zero (.firstElement one .empty) := rfl

example : insertionSortNonDescending (.firstElement two (.firstElement zero (.firstElement one .empty))) =
  .firstElement zero (.firstElement one (.firstElement two .empty)) := rfl

end Lists

end ZeroMath.Numbers.CardinalNatural.Decimal
