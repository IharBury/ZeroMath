import ZeroMath.Numbers.CardinalNatural.Peano
import ZeroMath.Sequences.List

namespace ZeroMath.Numbers.CardinalNatural

namespace Decimal

def Digit := {d : CardinalNatural.Peano // d < CardinalNatural.Peano.ten}

end Decimal

def Decimal := { l : Sequences.List Decimal.Digit // l ≠ Sequences.List.empty }

namespace Decimal

def zeroDigit : Digit := ⟨CardinalNatural.Peano.zero, by decide⟩
def oneDigit : Digit := ⟨CardinalNatural.Peano.one, by decide⟩
def twoDigit : Digit := ⟨CardinalNatural.Peano.two, by decide⟩
def threeDigit : Digit := ⟨CardinalNatural.Peano.three, by decide⟩
def fourDigit : Digit := ⟨CardinalNatural.Peano.four, by decide⟩
def fiveDigit : Digit := ⟨CardinalNatural.Peano.five, by decide⟩
def sixDigit : Digit := ⟨CardinalNatural.Peano.six, by decide⟩
def sevenDigit : Digit := ⟨CardinalNatural.Peano.seven, by decide⟩
def eightDigit : Digit := ⟨CardinalNatural.Peano.eight, by decide⟩
def nineDigit : Digit := ⟨CardinalNatural.Peano.nine, by decide⟩

def zero : Decimal := ⟨Sequences.List.firstElement zeroDigit Sequences.List.empty, by simp⟩
def one : Decimal := ⟨Sequences.List.firstElement oneDigit Sequences.List.empty, by simp⟩

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

theorem digit_val_successor_le_ten (d : Digit) : d.val.successor ≤ CardinalNatural.Peano.ten :=
  CardinalNatural.Peano.succ_le_of_lt d.property

theorem digit_val_le_ten (d : Digit) : d.val ≤ CardinalNatural.Peano.ten :=
  Or.inl d.property

def subtractAlignedLists (a b : Sequences.List Digit) (h : Sequences.List.SameLength a b) :
  Sequences.List Digit × Bool :=
  match a, b with
  | .empty, .empty => ⟨Sequences.List.empty, false⟩
  | .firstElement da das, .firstElement db dbs =>
    let ⟨digits, borrow⟩ := subtractAlignedLists das dbs (by cases h; assumption)
    let withBorrow := if borrow then db.val.successor else db.val
    if h2 : da.val < withBorrow then
      have h_withBorrow_le_ten : withBorrow ≤ CardinalNatural.Peano.ten := by
        dsimp [withBorrow]
        split
        · exact digit_val_successor_le_ten db
        · exact digit_val_le_ten db
      have h_le : withBorrow ≤ da.val + CardinalNatural.Peano.ten :=
        CardinalNatural.Peano.le_trans h_withBorrow_le_ten
          (CardinalNatural.Peano.le_add_self_right da.val CardinalNatural.Peano.ten)
      have h_digit :
          CardinalNatural.Peano.subtract (da.val + CardinalNatural.Peano.ten) withBorrow h_le <
            CardinalNatural.Peano.ten :=
        CardinalNatural.Peano.subtract_lt_of_lt_add h_le (CardinalNatural.Peano.add_lt_add_right h2 CardinalNatural.Peano.ten)
      ⟨Sequences.List.firstElement
        ⟨CardinalNatural.Peano.subtract (da.val + CardinalNatural.Peano.ten) withBorrow h_le, h_digit⟩
        digits, true⟩
    else
      have h_le : withBorrow ≤ da.val := CardinalNatural.Peano.not_lt_implies_le h2
      have h_digit :
          CardinalNatural.Peano.subtract da.val withBorrow h_le < CardinalNatural.Peano.ten :=
        CardinalNatural.Peano.subtract_lt_of_lt_add h_le
          (CardinalNatural.Peano.lt_le_trans da.property
            (CardinalNatural.Peano.le_add_self_right withBorrow CardinalNatural.Peano.ten))
      ⟨Sequences.List.firstElement
        ⟨CardinalNatural.Peano.subtract da.val withBorrow h_le, h_digit⟩ digits, false⟩
  | .empty, .firstElement _ _ => False.elim (by cases h)
  | .firstElement _ _, .empty => False.elim (by cases h)

theorem digit_val_eq_nine_of_not_successor_lt_ten (d : Digit)
  (h : CardinalNatural.Peano.isLessThan d.val.successor CardinalNatural.Peano.ten = false) :
  d.val = CardinalNatural.Peano.nine := by
  have h_not_lt : ¬ d.val.successor < CardinalNatural.Peano.ten :=
    (CardinalNatural.Peano.isLessThan_eq_false_iff_not_lt _ _).mp h
  cases d with
  | mk val hval =>
      dsimp at h_not_lt hval
      cases val with
      | zero =>
          exact False.elim (h_not_lt CardinalNatural.Peano.one_lt_ten)
      | successor val1 =>
          cases val1 with
          | zero =>
              exact False.elim (h_not_lt (by repeat constructor))
          | successor val2 =>
              cases val2 with
              | zero => exact False.elim (h_not_lt (by repeat constructor))
              | successor val3 =>
                  cases val3 with
                  | zero => exact False.elim (h_not_lt (by repeat constructor))
                  | successor val4 =>
                      cases val4 with
                      | zero => exact False.elim (h_not_lt (by repeat constructor))
                      | successor val5 =>
                          cases val5 with
                          | zero => exact False.elim (h_not_lt (by repeat constructor))
                          | successor val6 =>
                              cases val6 with
                              | zero => exact False.elim (h_not_lt (by repeat constructor))
                              | successor val7 =>
                                  cases val7 with
                                  | zero => exact False.elim (h_not_lt (by repeat constructor))
                                  | successor val8 =>
                                      cases val8 with
                                      | zero => exact False.elim (h_not_lt (by repeat constructor))
                                      | successor val9 =>
                                          cases val9 with
                                          | zero => rfl
                                          | successor val10 =>
                                              have hlt_zero : val10 < CardinalNatural.Peano.zero :=
                                                (CardinalNatural.Peano.lt_of_succ_lt_succ
                                                (CardinalNatural.Peano.lt_of_succ_lt_succ
                                                (CardinalNatural.Peano.lt_of_succ_lt_succ
                                                (CardinalNatural.Peano.lt_of_succ_lt_succ
                                                (CardinalNatural.Peano.lt_of_succ_lt_succ
                                                (CardinalNatural.Peano.lt_of_succ_lt_succ
                                                (CardinalNatural.Peano.lt_of_succ_lt_succ
                                                (CardinalNatural.Peano.lt_of_succ_lt_succ
                                                (CardinalNatural.Peano.lt_of_succ_lt_succ
                                                (CardinalNatural.Peano.lt_of_succ_lt_succ hval))))))))))
                                              exact False.elim ((CardinalNatural.Peano.not_lt_zero val10) hlt_zero)

theorem successor_carry_accumulator (accumulator : Peano) :
  accumulator.successor * Peano.ten + Peano.zero =
    (accumulator * Peano.ten + Peano.nine).successor := by
  rw [Peano.add_zero, Peano.successor_multiply]
  change accumulator * Peano.ten + Peano.ten =
    (accumulator * Peano.ten + Peano.nine).successor
  rfl

theorem successorList_toPeanoList (a : Sequences.List Digit) (accumulator : Peano) :
  match successorList a with
  | ⟨digits, true⟩ =>
      toPeanoList digits accumulator.successor = (toPeanoList a accumulator).successor
  | ⟨digits, false⟩ =>
      toPeanoList digits accumulator = (toPeanoList a accumulator).successor := by
  induction a generalizing accumulator with
  | empty =>
      rfl
  | firstElement d ds ih =>
      unfold successorList
      dsimp only
      cases hds : successorList ds with
      | mk digits carry =>
          have ih' := ih (accumulator * Peano.ten + d.val)
          rw [hds] at ih'
          cases carry with
          | false =>
              dsimp only at ih' ⊢
              exact ih'
          | true =>
              dsimp only at ih'
              by_cases hlt : CardinalNatural.Peano.isLessThan d.val.successor CardinalNatural.Peano.ten = true
              · simp [hlt]
                change toPeanoList digits (accumulator * Peano.ten + d.val.successor) =
                  (toPeanoList ds (accumulator * Peano.ten + d.val)).successor
                change toPeanoList digits (accumulator * Peano.ten + d.val).successor =
                  (toPeanoList ds (accumulator * Peano.ten + d.val)).successor at ih'
                exact ih'
              · have hfalse : CardinalNatural.Peano.isLessThan d.val.successor CardinalNatural.Peano.ten = false := by
                  cases h : CardinalNatural.Peano.isLessThan d.val.successor CardinalNatural.Peano.ten with
                  | false => rfl
                  | true => contradiction
                simp [hfalse]
                change toPeanoList digits (accumulator.successor * Peano.ten + Peano.zero) =
                  (toPeanoList ds (accumulator * Peano.ten + d.val)).successor
                have hd : d.val = Peano.nine := digit_val_eq_nine_of_not_successor_lt_ten d hfalse
                rw [hd]
                rw [successor_carry_accumulator]
                change toPeanoList digits (accumulator * Peano.ten + Peano.nine).successor =
                  (toPeanoList ds (accumulator * Peano.ten + Peano.nine)).successor
                rw [hd] at ih'
                exact ih'

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


theorem successor_toPeano (d : Decimal) :
  toPeano d.successor = d.toPeano.successor := by
  unfold successor
  unfold toPeano
  split
  · next digits h =>
      have hsucc := successorList_toPeanoList d.val Peano.zero
      rw [h] at hsucc
      dsimp only at hsucc
      exact hsucc
  · next digits h =>
      have hsucc := successorList_toPeanoList d.val Peano.zero
      rw [h] at hsucc
      dsimp only at hsucc
      exact hsucc

def fromPeano : Peano → Decimal
  | .zero => Decimal.zero
  | .successor p => successor (fromPeano p)

theorem fromPeano_toPeano (x : Peano) :
  toPeano (fromPeano x) = x := by
  induction x with
  | zero =>
    rfl
  | successor x ih =>
    unfold fromPeano
    rw [successor_toPeano]
    rw [ih]

end Decimal

end ZeroMath.Numbers.CardinalNatural
