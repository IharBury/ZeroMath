import ZeroMath.Numbers.CardinalNatural.Peano
import ZeroMath.Sequences.List

namespace ZeroMath.Numbers.CardinalNatural.Peano

/-- Sum of a list of cardinal Peano numbers, left to right. The empty list
    sums to zero. -/
def addAll : Sequences.List Peano → Peano
  | .empty => zero
  | .firstElement x xs => x + addAll xs

@[simp]
theorem addAll_empty : addAll .empty = zero :=
  rfl

@[simp]
theorem addAll_firstElement (x : Peano) (xs : Sequences.List Peano) :
    addAll (.firstElement x xs) = x + addAll xs :=
  rfl

theorem addAll_singleton (x : Peano) :
    addAll (.firstElement x .empty) = x := by
  rw [addAll_firstElement, addAll_empty, add_zero]

/-- The sum of `n` copies of `a` equals the product `a * n`. -/
theorem addAll_repeatElement (n a : Peano) :
    addAll (Sequences.List.repeatElement n a) = a * n := by
  induction n with
  | zero =>
    rw [Sequences.List.repeatElement_zero, addAll_empty, multiply_zero]
  | successor n ih =>
    rw [Sequences.List.repeatElement_successor, addAll_firstElement, ih,
      multiply_successor, add_commutative]

/-- The sum of `n` copies of `a` equals the product `n * a`. -/
theorem addAll_repeatElement_eq_count_multiply (n a : Peano) :
    addAll (Sequences.List.repeatElement n a) = n * a := by
  rw [addAll_repeatElement, multiply_commutative]

/-- A list of identical addends `a` sums to `a` times the number of addends. -/
theorem addAll_eq_multiply_of_AllElements {l : Sequences.List Peano} {a : Peano}
    (h : Sequences.List.AllElements (fun x => x = a) l) :
    addAll l = a * l.length := by
  have hsum := congrArg addAll (Sequences.List.eq_repeatElement_of_AllElements h)
  rw [addAll_repeatElement] at hsum
  exact hsum

/-- A list of identical addends `a` sums to the number of addends times `a`. -/
theorem addAll_eq_count_multiply_of_AllElements {l : Sequences.List Peano}
    {a : Peano} (h : Sequences.List.AllElements (fun x => x = a) l) :
    addAll l = l.length * a := by
  rw [addAll_eq_multiply_of_AllElements h, multiply_commutative]

example : addAll (Sequences.List.repeatElement four two) = two * four :=
  addAll_repeatElement four two

example : addAll (Sequences.List.repeatElement four two) = four * two :=
  addAll_repeatElement_eq_count_multiply four two

example :
    addAll
      (Sequences.List.firstElement two
        (Sequences.List.firstElement two
          (Sequences.List.firstElement two
            (Sequences.List.firstElement two Sequences.List.empty)))) =
      two * four :=
  addAll_eq_multiply_of_AllElements
    (Sequences.List.repeatElement_AllElements four two)

end ZeroMath.Numbers.CardinalNatural.Peano
