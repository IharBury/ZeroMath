import ZeroMath.Numbers.OrdinalNatural.Peano
import ZeroMath.Sequences.List.Sorting

namespace ZeroMath.Numbers.OrdinalNatural.Peano

/-- Sum of a non-empty list of ordinal Peano numbers, left to right. -/
def addAll : (l : Sequences.List Peano) → l ≠ Sequences.List.empty → Peano
  | .empty, h => False.elim (h rfl)
  | .firstElement x .empty, _ => x
  | .firstElement x (.firstElement y ys), _ =>
      x + addAll (.firstElement y ys) (by intro heq; cases heq)

theorem addAll_singleton (x : Peano) :
    addAll (.firstElement x .empty) (by intro heq; cases heq) = x :=
  rfl

theorem addAll_firstElement_firstElement (x y : Peano)
    (ys : Sequences.List Peano) :
    addAll (.firstElement x (.firstElement y ys)) (by intro heq; cases heq) =
      x + addAll (.firstElement y ys) (by intro heq; cases heq) :=
  rfl

theorem addAll_firstElement_of_ne_empty (x : Peano) (xs : Sequences.List Peano)
    (hxs : xs ≠ Sequences.List.empty)
    (h : Sequences.List.firstElement x xs ≠ Sequences.List.empty) :
    addAll (.firstElement x xs) h = x + addAll xs hxs := by
  match xs with
  | .empty => exact False.elim (hxs rfl)
  | .firstElement y ys =>
    rfl

/-- `count` copies of `addend`. Their sum is the product `addend * count`. -/
def repeatedAddends (addend count : Peano) : Sequences.List Peano :=
  Sequences.List.repeatValue addend
    (Numbers.CardinalNatural.Peano.fromOrdinal count)

theorem repeatedAddends_one (addend : Peano) :
    repeatedAddends addend one =
      Sequences.List.firstElement addend Sequences.List.empty :=
  rfl

theorem repeatedAddends_successor (addend count : Peano) :
    repeatedAddends addend count.successor =
      Sequences.List.firstElement addend (repeatedAddends addend count) :=
  rfl

theorem repeatedAddends_ne_empty (addend count : Peano) :
    repeatedAddends addend count ≠ Sequences.List.empty :=
  Sequences.List.repeatValue_ne_empty addend
    (Numbers.CardinalNatural.Peano.fromOrdinal count)
    (Numbers.CardinalNatural.Peano.fromOrdinal_ne_zero count)

theorem repeatedAddends_length (addend count : Peano) :
    (repeatedAddends addend count).length =
      Numbers.CardinalNatural.Peano.fromOrdinal count :=
  Sequences.List.repeatValue_length addend
    (Numbers.CardinalNatural.Peano.fromOrdinal count)

/-- Replacing a sum of identical addends with a product. -/
theorem addAll_repeatedAddends (addend count : Peano) :
    addAll (repeatedAddends addend count)
      (repeatedAddends_ne_empty addend count) = addend * count := by
  induction count with
  | one =>
    rfl
  | successor n ih =>
    have hrest := repeatedAddends_ne_empty addend n
    have hsucc := repeatedAddends_ne_empty addend n.successor
    calc
      addAll (repeatedAddends addend n.successor) hsucc
          = addAll (.firstElement addend (repeatedAddends addend n)) hsucc :=
        rfl
      _ = addend + addAll (repeatedAddends addend n) hrest :=
        addAll_firstElement_of_ne_empty addend _ hrest hsucc
      _ = addend + addend * n := by rw [ih]
      _ = addend * n + addend := add_commutative addend (addend * n)
      _ = addend * n.successor := (multiply_successor addend n).symm

/-- The commutative reading: `addend * count` is also the sum of `addend`
copies of `count`. -/
theorem addAll_repeatedAddends_commutative (addend count : Peano) :
    addAll (repeatedAddends count addend)
      (repeatedAddends_ne_empty count addend) = addend * count := by
  rw [addAll_repeatedAddends, multiply_commutative]

/-- Recover a product from a non-empty list of identical addends. -/
def tryProductFromAddends (l : Sequences.List Peano) : Option Peano :=
  match Sequences.List.tryRepeatedValue l with
  | some addend =>
    if h : l.length = Numbers.CardinalNatural.Peano.zero then
      none
    else
      some (addend * Numbers.CardinalNatural.Peano.toOrdinal l.length h)
  | none => none

theorem tryProductFromAddends_repeatedAddends (addend count : Peano) :
    tryProductFromAddends (repeatedAddends addend count) =
      some (addend * count) := by
  have hlen := repeatedAddends_length addend count
  have htry :
      Sequences.List.tryRepeatedValue (repeatedAddends addend count) =
        some addend :=
    Sequences.List.tryRepeatedValue_repeatValue addend
      (Numbers.CardinalNatural.Peano.fromOrdinal count)
      (Numbers.CardinalNatural.Peano.fromOrdinal_ne_zero count)
  simp only [tryProductFromAddends, htry]
  split
  · next hz =>
    exact False.elim
      (Numbers.CardinalNatural.Peano.fromOrdinal_ne_zero count (hlen.symm.trans hz))
  · next hnz =>
    apply congrArg some
    apply congrArg (fun n => addend * n)
    rw [Numbers.CardinalNatural.Peano.toOrdinal_congr hlen hnz
      (Numbers.CardinalNatural.Peano.fromOrdinal_ne_zero count)]
    exact Numbers.CardinalNatural.Peano.toOrdinal_fromOrdinal_helper count
      (Numbers.CardinalNatural.Peano.fromOrdinal_ne_zero count)

example : addAll (repeatedAddends two two)
    (repeatedAddends_ne_empty two two) = two * two :=
  rfl

example : tryProductFromAddends (repeatedAddends two two) = some (two * two) :=
  tryProductFromAddends_repeatedAddends two two

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

example :
  insertSortedNonDescending (successor one)
    (.firstElement one (.firstElement (successor (successor one)) .empty)) =
  .firstElement one (.firstElement (successor one) (.firstElement (successor (successor one)) .empty)) :=
  rfl

example : insertionSortNonDescending .empty = .empty := rfl

example : insertionSortNonDescending (.firstElement one (.firstElement two .empty)) =
  .firstElement one (.firstElement two .empty) := rfl

example : insertionSortNonDescending (.firstElement (successor two) (.firstElement one (.firstElement two .empty))) =
  .firstElement one (.firstElement two (.firstElement (successor two) .empty)) := rfl

end Lists

end ZeroMath.Numbers.OrdinalNatural.Peano
