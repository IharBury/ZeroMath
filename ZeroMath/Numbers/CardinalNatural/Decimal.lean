import ZeroMath.Numbers.CardinalNatural.Peano
import ZeroMath.Sequences.List

namespace ZeroMath.Numbers.CardinalNatural

namespace Decimal

def Digit := {d : CardinalNatural.Peano // d < CardinalNatural.Peano.ten}

end Decimal

def Decimal := { l : Sequences.List Decimal.Digit // l ≠ Sequences.List.empty }

namespace Decimal

def isNormalized (d : Decimal) : Bool :=
  match d with
  | ⟨.empty, _⟩ => by contradiction
  | ⟨.firstElement digit .empty, _⟩ => true
  | ⟨.firstElement digit _, _⟩ => decide (digit.val ≠ CardinalNatural.Peano.zero)

def toPeanoList (x : Sequences.List Digit) (accumulator : Peano) : Peano :=
  match x with
  | .empty => accumulator
  | .firstElement d ds => toPeanoList ds (accumulator * Peano.ten + d.val)

def toPeano (d : Decimal) : Peano :=
  toPeanoList d.val Peano.zero

def successorList (a : Sequences.List Digit) :
  Sequences.List Digit × Bool :=
  match a with
  | .empty => ⟨Sequences.List.empty, true⟩
  | .firstElement d ds =>
    let ⟨digits, carry⟩ := successorList ds
    if carry then
      if h3 : CardinalNatural.Peano.isLessThan d.val.successor CardinalNatural.Peano.ten then
        ⟨Sequences.List.firstElement ⟨d.val.successor, (CardinalNatural.Peano.isLessThan_eq_true_iff_lt _ _).mp h3⟩ digits, false⟩
      else
        ⟨Sequences.List.firstElement ⟨CardinalNatural.Peano.zero, CardinalNatural.Peano.zero_lt_succ CardinalNatural.Peano.nine⟩ digits, true⟩
    else
      ⟨Sequences.List.firstElement d digits, false⟩

theorem successorList_ne_empty_of_carry_false {a digits : Sequences.List Digit}
  (ha : a ≠ Sequences.List.empty) (h : successorList a = ⟨digits, false⟩) :
  digits ≠ Sequences.List.empty := by
  induction a generalizing digits with
  | empty =>
      exact False.elim (ha rfl)
  | firstElement d ds _ =>
      unfold successorList at h
      dsimp at h
      split at h
      · split at h
        · cases h
          intro h_empty
          cases h_empty
        · cases h
      · cases h
        intro h_empty
        cases h_empty

def successor (a : Decimal) : Decimal :=
  match h : successorList a.val with
  | ⟨digits, true⟩ =>
    ⟨Sequences.List.firstElement ⟨CardinalNatural.Peano.one, CardinalNatural.Peano.one_lt_ten⟩ digits, by simp⟩
  | ⟨digits, false⟩ =>
    ⟨digits, successorList_ne_empty_of_carry_false a.property h⟩

end Decimal

end ZeroMath.Numbers.CardinalNatural
