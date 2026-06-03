import ZeroMath.Numbers.CardinalNatural.Peano
import ZeroMath.Sequences.List

namespace ZeroMath.Numbers.OrdinalNatural

namespace Decimal

def Digit := {d : CardinalNatural.Peano // d < CardinalNatural.Peano.ten}

def DigitIsNonZero (d : Digit) : Prop := d.val ≠ CardinalNatural.Peano.zero

deriving instance Decidable for DigitIsNonZero

def HasNonZero := Sequences.List.AnyElement DigitIsNonZero

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

end Decimal

def Decimal := { l : Sequences.List Decimal.Digit // Decimal.HasNonZero l }

namespace Decimal

theorem hasNonZero_ne_empty {l : Sequences.List Digit} (h : HasNonZero l) : l ≠ Sequences.List.empty := by
  intro h_empty
  cases h with
  | first _ _ _ => cases h_empty
  | notFirst _ _ _ => cases h_empty

def isNormalized (d : Decimal) : Bool :=
  match h : d.val with
  | .empty => False.elim (hasNonZero_ne_empty d.property h)
  | .firstElement digit _ => decide (digit.val ≠ CardinalNatural.Peano.zero)

def hasNonZero (a : Sequences.List Digit) : Bool := Sequences.List.anyElement DigitIsNonZero a

theorem hasNonZero_tail_of_zero_first {d : Digit} {ds : Sequences.List Digit}
  (h : HasNonZero (Sequences.List.firstElement d ds))
  (hd : d.val = CardinalNatural.Peano.zero) : HasNonZero ds := by
  cases h with
  | first _ _ hd_nonzero =>
      exact False.elim (hd_nonzero hd)
  | notFirst _ _ hds =>
      exact hds

def normalizeList (a : Sequences.List Digit) (h : HasNonZero a) : Decimal :=
  match a with
  | .empty => False.elim (hasNonZero_ne_empty h rfl)
  | .firstElement d ds =>
      if h2 : d.val = CardinalNatural.Peano.zero then
        normalizeList ds (hasNonZero_tail_of_zero_first h h2)
      else
        ⟨Sequences.List.firstElement d ds, h⟩

def normalize (a : Decimal) : Decimal :=
  normalizeList a.val a.property


def Equivalent (a b : Decimal) : Prop := a.normalize = b.normalize

instance : Setoid Decimal where
  r := Equivalent
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h1 h2 => h1.trans h2
  }
def toCardinalList (a : Sequences.List Digit) (acc : CardinalNatural.Peano) : CardinalNatural.Peano :=
  match a with
  | .empty => acc
  | .firstElement d ds => toCardinalList ds (acc * CardinalNatural.Peano.ten + d.val)

def toCardinalPeano (a : Decimal) : CardinalNatural.Peano :=
  toCardinalList a.val CardinalNatural.Peano.zero

theorem normalizeList_toCardinalPeano (a : Sequences.List Digit) (h : HasNonZero a) :
  toCardinalPeano (normalizeList a h) = toCardinalList a CardinalNatural.Peano.zero := by
  induction a with
  | empty =>
      exact False.elim (hasNonZero_ne_empty h rfl)
  | firstElement d ds ih =>
      unfold normalizeList
      split
      · next hd =>
          rw [ih (hasNonZero_tail_of_zero_first h hd)]
          change toCardinalList ds CardinalNatural.Peano.zero =
            toCardinalList ds (CardinalNatural.Peano.zero * CardinalNatural.Peano.ten + d.val)
          rw [hd, CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.add_zero]
      · rfl

theorem toCardinalList_ne_zero_of_acc_ne_zero (a : Sequences.List Digit)
  (acc : CardinalNatural.Peano) (h_acc : acc ≠ CardinalNatural.Peano.zero) :
  toCardinalList a acc ≠ CardinalNatural.Peano.zero := by
  induction a generalizing acc with
  | empty =>
      exact h_acc
  | firstElement d ds ih =>
      exact ih (acc * CardinalNatural.Peano.ten + d.val)
        (CardinalNatural.Peano.add_ne_zero_of_left_ne_zero
          (acc * CardinalNatural.Peano.ten) d.val
          (CardinalNatural.Peano.multiply_ne_zero acc CardinalNatural.Peano.ten h_acc
            (CardinalNatural.Peano.successor_ne_zero CardinalNatural.Peano.nine)))

theorem toCardinalList_ne_zero_of_hasNonZero (a : Sequences.List Digit)
  (acc : CardinalNatural.Peano) (h : HasNonZero a) :
  toCardinalList a acc ≠ CardinalNatural.Peano.zero := by
  induction h generalizing acc with
  | first d ds hd =>
      exact toCardinalList_ne_zero_of_acc_ne_zero ds (acc * CardinalNatural.Peano.ten + d.val)
        (CardinalNatural.Peano.add_ne_zero_of_right_ne_zero (acc * CardinalNatural.Peano.ten) d.val hd)
  | notFirst d ds _ ih =>
      exact ih (acc * CardinalNatural.Peano.ten + d.val)

theorem toCardinalPeano_ne_zero (a : Decimal) :
  toCardinalPeano a ≠ CardinalNatural.Peano.zero := by
  exact toCardinalList_ne_zero_of_hasNonZero a.val CardinalNatural.Peano.zero a.property

def toPeano (a : Decimal) : OrdinalNatural.Peano :=
  (toCardinalPeano a).toOrdinal (toCardinalPeano_ne_zero a)

theorem normalize_toPeano (x : Decimal) : x.normalize.toPeano = x.toPeano := by
  unfold toPeano
  apply CardinalNatural.Peano.toOrdinal_congr
  unfold normalize
  exact normalizeList_toCardinalPeano x.val x.property

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

theorem toPeano_eq_of_equivalent {a b : Decimal} (h : a ≈ b) :
  a.toPeano = b.toPeano := by
  have h_eq : a.normalize = b.normalize := h
  rw [← normalize_toPeano a, ← normalize_toPeano b, h_eq]


theorem one_lt_ten : CardinalNatural.Peano.one < CardinalNatural.Peano.ten := by
  apply CardinalNatural.Peano.LessThan.step
  apply CardinalNatural.Peano.LessThan.step
  apply CardinalNatural.Peano.LessThan.step
  apply CardinalNatural.Peano.LessThan.step
  apply CardinalNatural.Peano.LessThan.step
  apply CardinalNatural.Peano.LessThan.step
  apply CardinalNatural.Peano.LessThan.step
  apply CardinalNatural.Peano.LessThan.step
  apply CardinalNatural.Peano.LessThan.base

theorem hasNonZero_of_carry_true {a : Sequences.List Digit} {digits : Sequences.List Digit} (_ : successorList a = ⟨digits, true⟩) :
  HasNonZero (Sequences.List.firstElement ⟨CardinalNatural.Peano.one, one_lt_ten⟩ digits) := by
  apply Sequences.List.AnyElement.first
  intro h1
  cases h1

theorem hasNonZero_of_carry_false {a : Sequences.List Digit} {digits : Sequences.List Digit} (h_nonzero: HasNonZero a) (h : successorList a = ⟨digits, false⟩) :
  HasNonZero digits := by
  induction a generalizing digits with
  | empty =>
    unfold successorList at h
    cases h
  | firstElement d ds ih =>
    unfold successorList at h
    dsimp at h
    split at h
    · next h1 =>
      split at h
      · next h2 =>
        cases h
        apply Sequences.List.AnyElement.first
        intro hc
        cases hc
      · next h2 =>
        cases h
    · next h1 =>
      cases h
      cases h_nonzero with
      | first _ _ hd_nonzero =>
        apply Sequences.List.AnyElement.first
        exact hd_nonzero
      | notFirst _ _ hds =>
        apply Sequences.List.AnyElement.notFirst
        have h_eq : successorList ds = ⟨(successorList ds).fst, false⟩ := by
          cases h_succ : successorList ds with
          | mk fst snd =>
            have h2 : ¬snd = true := by
              intro hs
              rw [hs] at h_succ
              have h3 : (successorList ds).snd = true := by rw [h_succ]
              contradiction
            cases snd
            · rfl
            · contradiction
        exact ih hds h_eq

def successor (a : Decimal) : Decimal :=
  match h : successorList a.val with
  | ⟨digits, true⟩ =>
    ⟨Sequences.List.firstElement ⟨CardinalNatural.Peano.one, one_lt_ten⟩ digits, hasNonZero_of_carry_true h⟩
  | ⟨digits, false⟩ =>
    ⟨digits, hasNonZero_of_carry_false a.property h⟩


def one : Decimal :=
  ⟨Sequences.List.firstElement ⟨CardinalNatural.Peano.one, one_lt_ten⟩ Sequences.List.empty, by
    apply Sequences.List.AnyElement.first
    intro h
    cases h⟩

def addAlignedLists (a b : Sequences.List Digit) (h : Sequences.List.SameLength a b) :
  Sequences.List Digit × Bool :=
  match a, b with
  | .empty, .empty => ⟨Sequences.List.empty, false⟩
  | .firstElement da das, .firstElement db dbs =>
    let ⟨digits, carry⟩ := addAlignedLists das dbs (by cases h; assumption)
    let digit_sum := da.val + db.val + (if carry then CardinalNatural.Peano.one else CardinalNatural.Peano.zero)
    if h2 : CardinalNatural.Peano.isLessThan digit_sum CardinalNatural.Peano.ten then
      ⟨Sequences.List.firstElement ⟨digit_sum, (CardinalNatural.Peano.isLessThan_eq_true_iff_lt _ _).mp h2⟩ digits, false⟩
    else
      have h_le : CardinalNatural.Peano.ten ≤ digit_sum := CardinalNatural.Peano.isLessThan_false_implies_le (eq_false_of_ne_true h2)
      have h_lt_twenty : digit_sum < CardinalNatural.Peano.ten + CardinalNatural.Peano.ten :=
        digit_sum_lt_twenty da.val db.val carry da.property db.property
      ⟨Sequences.List.firstElement ⟨CardinalNatural.Peano.subtract digit_sum CardinalNatural.Peano.ten h_le, subtract_ten_lt_ten digit_sum h_le h_lt_twenty⟩ digits, true⟩
  | .empty, .firstElement _ _ => False.elim (by cases h)
  | .firstElement _ _, .empty => False.elim (by cases h)

theorem hasNonZero_of_addAlignedLists_carry_true {a b digits : Sequences.List Digit}
  {h : Sequences.List.SameLength a b} (_ : addAlignedLists a b h = ⟨digits, true⟩) :
  HasNonZero (Sequences.List.firstElement ⟨CardinalNatural.Peano.one, one_lt_ten⟩ digits) := by
  apply Sequences.List.AnyElement.first
  exact CardinalNatural.Peano.successor_ne_zero CardinalNatural.Peano.zero

theorem addAlignedLists_digit_sum_ne_zero_of_left_ne_zero
  (da db : CardinalNatural.Peano) (carry : Bool) (hda : da ≠ CardinalNatural.Peano.zero) :
  da + db + (if carry then CardinalNatural.Peano.one else CardinalNatural.Peano.zero) ≠
    CardinalNatural.Peano.zero := by
  apply CardinalNatural.Peano.add_ne_zero_of_left_ne_zero
  exact CardinalNatural.Peano.add_ne_zero_of_left_ne_zero da db hda

theorem addAlignedLists_digit_sum_ne_zero_of_carry_true
  (da db : CardinalNatural.Peano) :
  da + db + CardinalNatural.Peano.one ≠ CardinalNatural.Peano.zero := by
  exact CardinalNatural.Peano.add_ne_zero_of_right_ne_zero (da + db) CardinalNatural.Peano.one
    (CardinalNatural.Peano.successor_ne_zero CardinalNatural.Peano.zero)

theorem hasNonZero_of_addAlignedLists_carry_false {a b digits : Sequences.List Digit}
  (h : Sequences.List.SameLength a b) (h_nonzero : HasNonZero a)
  (h_add : addAlignedLists a b h = ⟨digits, false⟩) :
  HasNonZero digits := by
  induction h generalizing digits with
  | empty =>
      cases h_nonzero
  | firstElement htail ih =>
      rename_i da db das dbs
      unfold addAlignedLists at h_add
      simp at h_add
      cases h_rec : addAlignedLists das dbs htail with
      | mk tailDigits tailCarry =>
          rw [h_rec] at h_add
          cases tailCarry with
          | false =>
              simp at h_add
              split at h_add
              · injection h_add with h_digits _
                subst digits
                cases h_nonzero with
                | first _ _ hda_nonzero =>
                    apply Sequences.List.AnyElement.first
                    exact addAlignedLists_digit_sum_ne_zero_of_left_ne_zero da.val db.val false hda_nonzero
                | notFirst _ _ hdas_nonzero =>
                    apply Sequences.List.AnyElement.notFirst
                    exact ih hdas_nonzero h_rec
              · injection h_add with _ h_carry
                cases h_carry
          | true =>
              simp at h_add
              split at h_add
              · injection h_add with h_digits _
                subst digits
                apply Sequences.List.AnyElement.first
                cases h_nonzero with
                | first _ _ hda_nonzero =>
                    exact addAlignedLists_digit_sum_ne_zero_of_left_ne_zero da.val db.val true hda_nonzero
                | notFirst _ _ _ =>
                    exact addAlignedLists_digit_sum_ne_zero_of_carry_true da.val db.val
              · injection h_add with _ h_carry
                cases h_carry

theorem hasNonZero_padAtStartToSameLength_fst (a b : Sequences.List Digit) (paddingValue : Digit)
  (h : HasNonZero a) :
  HasNonZero (Sequences.List.padAtStartToSameLength a b paddingValue).1 := by
  unfold Sequences.List.padAtStartToSameLength
  dsimp only
  split
  · exact h
  · exact Sequences.List.padAtStart_anyElement h paddingValue _

def zeroDigit : Digit :=
  ⟨CardinalNatural.Peano.zero, CardinalNatural.Peano.zero_lt_succ CardinalNatural.Peano.nine⟩

def add (a b : Decimal) : Decimal :=
  let pair := Sequences.List.padAtStartToSameLength a.val b.val zeroDigit
  let h_same : Sequences.List.SameLength pair.1 pair.2 :=
    Sequences.List.padAtStartToSameLength_sameLength a.val b.val zeroDigit
  match h_add : addAlignedLists pair.1 pair.2 h_same with
  | ⟨digits, true⟩ =>
      ⟨Sequences.List.firstElement ⟨CardinalNatural.Peano.one, one_lt_ten⟩ digits,
        hasNonZero_of_addAlignedLists_carry_true h_add⟩
  | ⟨digits, false⟩ =>
      ⟨digits, by
        apply hasNonZero_of_addAlignedLists_carry_false h_same
        · exact hasNonZero_padAtStartToSameLength_fst a.val b.val zeroDigit a.property
        · exact h_add
      ⟩

instance : Add Decimal where
  add := add

end Decimal

end ZeroMath.Numbers.OrdinalNatural
