import ZeroMath.Numbers.Integer.Peano
import ZeroMath.Sequences.List.Sorting

namespace ZeroMath.Numbers.Integer.Peano

/-- Sum of a list of integer Peano numbers, left to right. The empty sum is
zero. -/
def sum : Sequences.List Peano → Peano
  | .empty => zero
  | .firstElement x xs => x + sum xs

theorem sum_empty : sum .empty = zero :=
  rfl

theorem sum_firstElement (x : Peano) (xs : Sequences.List Peano) :
    sum (.firstElement x xs) = x + sum xs :=
  rfl

theorem sum_concatenate (a b : Sequences.List Peano) :
    sum (Sequences.List.concatenate a b) = sum a + sum b := by
  induction a with
  | empty =>
    simp only [Sequences.List.concatenate, sum, zero_add]
  | firstElement x xs ih =>
    simp only [Sequences.List.concatenate, sum, ih, add_associative]

/-- `count` copies of `addend`. Their sum is `addend * fromCardinalNatural count`. -/
def repeatedAddends (addend : Peano) (count : CardinalNatural.Peano) :
    Sequences.List Peano :=
  Sequences.List.repeatValue addend count

theorem repeatedAddends_eq_repeatValue (addend : Peano)
    (count : CardinalNatural.Peano) :
    repeatedAddends addend count = Sequences.List.repeatValue addend count :=
  rfl

theorem repeatedAddends_length (addend : Peano) (count : CardinalNatural.Peano) :
    (repeatedAddends addend count).length = count :=
  Sequences.List.repeatValue_length addend count

theorem repeatedAddends_AllElements (addend : Peano)
    (count : CardinalNatural.Peano) :
    Sequences.List.AllElements (fun x => x = addend)
      (repeatedAddends addend count) :=
  Sequences.List.repeatValue_AllElements addend count

theorem repeatedAddends_ne_empty (addend : Peano)
    (count : CardinalNatural.Peano) (h : count ≠ CardinalNatural.Peano.zero) :
    repeatedAddends addend count ≠ Sequences.List.empty :=
  Sequences.List.repeatValue_ne_empty addend count h

/-- A sum of identical addends equals the product of the addend and the
cardinal number of addends. -/
theorem sum_eq_multiply_of_AllElements (addend : Peano)
    (l : Sequences.List Peano)
    (h : Sequences.List.AllElements (fun x => x = addend) l) :
    sum l = addend * fromCardinalNatural l.length := by
  induction l with
  | empty =>
    simp only [sum, Sequences.List.length, fromCardinalNatural, multiply_zero]
  | firstElement x xs ih =>
    have hx : x = addend :=
      Sequences.List.AllElements.head (p := fun y => y = addend) h
    have hxs := Sequences.List.AllElements.tail (p := fun y => y = addend) h
    rw [sum_firstElement, ih hxs, hx, Sequences.List.length_firstElement,
      fromCardinalNatural_successor, multiply_successor, add_commutative]

/-- Replacing a sum of identical addends with a product. -/
theorem sum_repeatedAddends (addend : Peano) (count : CardinalNatural.Peano) :
    sum (repeatedAddends addend count) =
      addend * fromCardinalNatural count := by
  rw [sum_eq_multiply_of_AllElements addend _
        (repeatedAddends_AllElements addend count),
      repeatedAddends_length]

/-- Recover a product from a non-empty list of identical addends. -/
def tryProductFromAddends (l : Sequences.List Peano) : Option Peano :=
  match Sequences.List.tryRepeatedValue l with
  | some addend => some (addend * fromCardinalNatural l.length)
  | none => none

theorem tryProductFromAddends_repeatedAddends (addend : Peano)
    (count : CardinalNatural.Peano) (h : count ≠ CardinalNatural.Peano.zero) :
    tryProductFromAddends (repeatedAddends addend count) =
      some (addend * fromCardinalNatural count) := by
  have htry :
      Sequences.List.tryRepeatedValue (repeatedAddends addend count) =
        some addend :=
    Sequences.List.tryRepeatedValue_repeatValue addend count h
  simp only [tryProductFromAddends, htry]
  exact congrArg some (congrArg (fun n => addend * fromCardinalNatural n)
    (repeatedAddends_length addend count))

example : sum (repeatedAddends minusOne CardinalNatural.Peano.three) =
    minusOne * fromCardinalNatural CardinalNatural.Peano.three :=
  sum_repeatedAddends minusOne CardinalNatural.Peano.three

example : tryProductFromAddends
    (repeatedAddends two CardinalNatural.Peano.two) =
      some (two * fromCardinalNatural CardinalNatural.Peano.two) :=
  tryProductFromAddends_repeatedAddends two CardinalNatural.Peano.two
    CardinalNatural.Peano.two_ne_zero

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
