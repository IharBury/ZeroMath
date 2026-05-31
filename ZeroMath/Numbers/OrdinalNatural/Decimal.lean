import ZeroMath.Numbers.CardinalNatural.Peano
import ZeroMath.Sequences.List

namespace ZeroMath.Numbers.OrdinalNatural

namespace Decimal

def AllLessThanTen : Sequences.List CardinalNatural.Peano → Prop
  | .empty => True
  | .firstElement d ds => d < CardinalNatural.Peano.ten ∧ AllLessThanTen ds

def HasNonZero : Sequences.List CardinalNatural.Peano → Prop
  | .empty => False
  | .firstElement d ds => d ≠ CardinalNatural.Peano.zero ∨ HasNonZero ds

end Decimal

def Decimal := { l : Sequences.List CardinalNatural.Peano // Decimal.AllLessThanTen l ∧ Decimal.HasNonZero l }

namespace Decimal

def hasNonZero : Sequences.List CardinalNatural.Peano → Bool
  | .empty => false
  | .firstElement d ds => if d = CardinalNatural.Peano.zero then hasNonZero ds else true

def isNormalized (d : Decimal) : Bool :=
  match d.val with
  | .empty => false
  | .firstElement digit _ => decide (digit ≠ CardinalNatural.Peano.zero)

theorem padAtStart_allLessThanTen (l : Sequences.List CardinalNatural.Peano) (h : AllLessThanTen l) (paddingValue : CardinalNatural.Peano)
  (h_pad : paddingValue < CardinalNatural.Peano.ten) (n : CardinalNatural.Peano) :
  AllLessThanTen (Sequences.List.padAtStart l paddingValue n) := by
  induction n generalizing l with
  | zero => exact h
  | successor n' ih =>
    unfold Sequences.List.padAtStart
    apply ih
    unfold AllLessThanTen
    constructor
    · exact h_pad
    · exact h

theorem padAtStart_hasNonZero (l : Sequences.List CardinalNatural.Peano) (h : HasNonZero l) (paddingValue : CardinalNatural.Peano) (n : CardinalNatural.Peano) :
  HasNonZero (Sequences.List.padAtStart l paddingValue n) := by
  induction n generalizing l with
  | zero => exact h
  | successor n' ih =>
    unfold Sequences.List.padAtStart
    apply ih
    unfold HasNonZero
    right
    exact h

theorem subtract_ten_lt_ten (digit_sum : CardinalNatural.Peano)
  (h_le : CardinalNatural.Peano.ten ≤ digit_sum)
  (h_lt_twenty : digit_sum < CardinalNatural.Peano.ten + CardinalNatural.Peano.ten) :
  CardinalNatural.Peano.subtract digit_sum CardinalNatural.Peano.ten h_le < CardinalNatural.Peano.ten := by
  exact CardinalNatural.Peano.subtract_lt_of_lt_add h_le h_lt_twenty

theorem digit_sum_lt_twenty (da db : CardinalNatural.Peano) (carry : Bool)
  (hda : da < CardinalNatural.Peano.ten) (hdb : db < CardinalNatural.Peano.ten) :
  da + db + (if carry then CardinalNatural.Peano.one else CardinalNatural.Peano.zero) <
    CardinalNatural.Peano.ten + CardinalNatural.Peano.ten := by
  cases carry with
  | false =>
    simp
    exact CardinalNatural.Peano.lt_trans (CardinalNatural.Peano.add_lt_add_right hda db) (CardinalNatural.Peano.add_lt_add_left hdb CardinalNatural.Peano.ten)
  | true =>
    have h_da_succ_le : da + CardinalNatural.Peano.one ≤ CardinalNatural.Peano.ten := by
      change da.successor ≤ CardinalNatural.Peano.ten
      exact CardinalNatural.Peano.succ_le_of_lt hda
    have h_sum_le : (da + CardinalNatural.Peano.one) + db ≤ CardinalNatural.Peano.ten + db :=
      CardinalNatural.Peano.add_le_add_right h_da_succ_le db
    have h_ten_db_lt : CardinalNatural.Peano.ten + db < CardinalNatural.Peano.ten + CardinalNatural.Peano.ten :=
      CardinalNatural.Peano.add_lt_add_left hdb CardinalNatural.Peano.ten
    simp
    rw [CardinalNatural.Peano.add_associative da db CardinalNatural.Peano.one]
    rw [CardinalNatural.Peano.add_commutative db CardinalNatural.Peano.one]
    rw [← CardinalNatural.Peano.add_associative da CardinalNatural.Peano.one db]
    exact CardinalNatural.Peano.le_lt_trans h_sum_le h_ten_db_lt

theorem cardinal_lt_toNat {a b : CardinalNatural.Peano} (h : a < b) :
  a.toNat < b.toNat := by
  induction h with
  | base =>
    simp [CardinalNatural.Peano.toNat]
  | step _ ih =>
    exact Nat.lt_succ_of_lt ih

theorem fromOrdinal_add (x y : Peano) :
  CardinalNatural.Peano.fromOrdinal (x + y) =
    CardinalNatural.Peano.fromOrdinal x + CardinalNatural.Peano.fromOrdinal y := by
  induction y with
  | one =>
    rw [Peano.add_one]
    change CardinalNatural.Peano.successor (CardinalNatural.Peano.fromOrdinal x) =
      CardinalNatural.Peano.fromOrdinal x + CardinalNatural.Peano.one
    rw [CardinalNatural.Peano.one, CardinalNatural.Peano.add_successor, CardinalNatural.Peano.add_zero]
  | successor y ih =>
    rw [Peano.add_succ]
    change CardinalNatural.Peano.successor (CardinalNatural.Peano.fromOrdinal (x + y)) =
      CardinalNatural.Peano.fromOrdinal x + CardinalNatural.Peano.successor (CardinalNatural.Peano.fromOrdinal y)
    rw [CardinalNatural.Peano.add_successor, ih]

theorem peano_eq_of_fromOrdinal_eq {x y : Peano}
  (h : CardinalNatural.Peano.fromOrdinal x = CardinalNatural.Peano.fromOrdinal y) : x = y := by
  obtain ⟨hx_nonzero, hx⟩ := CardinalNatural.Peano.toOrdinal_fromOrdinal x
  obtain ⟨hy_nonzero, hy⟩ := CardinalNatural.Peano.toOrdinal_fromOrdinal y
  exact hx.symm.trans ((CardinalNatural.Peano.toOrdinal_congr h hx_nonzero hy_nonzero).trans hy)

theorem nine_lt_ten : CardinalNatural.Peano.nine < CardinalNatural.Peano.ten := CardinalNatural.Peano.LessThan.base

theorem peano_predecessor_congr {a b : OrdinalNatural.Peano}
  (ha : a ≠ OrdinalNatural.Peano.one) (hb : b ≠ OrdinalNatural.Peano.one)
  (h_eq : a = b) : a.predecessor ha = b.predecessor hb := by
  cases h_eq
  rfl

end Decimal

end ZeroMath.Numbers.OrdinalNatural
