import ZeroMath.Numbers.CardinalNatural.Peano
import ZeroMath.Sequences.List

namespace ZeroMath.Numbers.OrdinalNatural

namespace Decimal

def Digit := {d : CardinalNatural.Peano // d < CardinalNatural.Peano.ten}

deriving instance DecidableEq for Digit

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

def predecessorList (a : Sequences.List Digit) :
  Sequences.List Digit × Bool :=
  match a with
  | .empty => ⟨Sequences.List.empty, true⟩
  | .firstElement d ds =>
    let ⟨digits, borrow⟩ := predecessorList ds
    if borrow then
      match d with
      | ⟨.zero, _⟩ =>
        ⟨Sequences.List.firstElement ⟨CardinalNatural.Peano.nine, CardinalNatural.Peano.LessThan.base⟩ digits, true⟩
      | ⟨.successor d', h⟩ =>
        ⟨Sequences.List.firstElement ⟨d', CardinalNatural.Peano.lt_of_succ_lt h⟩ digits, false⟩
    else
      ⟨Sequences.List.firstElement d digits, false⟩



end Decimal

def Decimal := { l : Sequences.List Decimal.Digit // Decimal.HasNonZero l }

instance : DecidableEq Decimal :=
  fun a b =>
    match decEq a.val b.val with
    | isTrue h => isTrue (Subtype.ext h)
    | isFalse h => isFalse (fun h' => h (congrArg Subtype.val h'))

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

theorem digit_val_successor_le_ten (d : Digit) : d.val.successor ≤ CardinalNatural.Peano.ten :=
  CardinalNatural.Peano.succ_le_of_lt d.property

theorem digit_val_le_ten (d : Digit) : d.val ≤ CardinalNatural.Peano.ten :=
  CardinalNatural.Peano.le_of_succ_le (digit_val_successor_le_ten d)

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
        CardinalNatural.Peano.subtract_lt_of_lt_add h_le
          (CardinalNatural.Peano.add_lt_add_right h2 CardinalNatural.Peano.ten)
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

def one : Decimal :=
  ⟨Sequences.List.firstElement ⟨CardinalNatural.Peano.one, CardinalNatural.Peano.one_lt_ten⟩ Sequences.List.empty, by
    apply Sequences.List.AnyElement.first
    intro h
    cases h⟩

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
instance (x y : Decimal) : Decidable (x ≈ y) :=

  inferInstanceAs (Decidable (x.normalize = y.normalize))


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

theorem hasNonZero_of_carry_true {a : Sequences.List Digit} {digits : Sequences.List Digit} (_ : successorList a = ⟨digits, true⟩) :
  HasNonZero (Sequences.List.firstElement ⟨CardinalNatural.Peano.one, CardinalNatural.Peano.one_lt_ten⟩ digits) := by
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
    ⟨Sequences.List.firstElement ⟨CardinalNatural.Peano.one, CardinalNatural.Peano.one_lt_ten⟩ digits, hasNonZero_of_carry_true h⟩
  | ⟨digits, false⟩ =>
    ⟨digits, hasNonZero_of_carry_false a.property h⟩

def AllZero : Sequences.List Digit → Prop
  | .empty => True
  | .firstElement d ds => d.val = CardinalNatural.Peano.zero ∧ AllZero ds

inductive RepresentsOne : Sequences.List Digit → Prop where
  | one : RepresentsOne (Sequences.List.firstElement
      ⟨CardinalNatural.Peano.one, CardinalNatural.Peano.one_lt_ten⟩ Sequences.List.empty)
  | leadingZero {ds : Sequences.List Digit} : RepresentsOne ds →
      RepresentsOne (Sequences.List.firstElement
        ⟨CardinalNatural.Peano.zero, CardinalNatural.Peano.zero_lt_ten⟩ ds)

theorem allZero_of_predecessorList_borrow_true {a digits : Sequences.List Digit}
  (h : predecessorList a = ⟨digits, true⟩) : AllZero a := by
  induction a generalizing digits with
  | empty => trivial
  | firstElement d ds ih =>
      unfold predecessorList at h
      cases h_rec : predecessorList ds with
      | mk tailDigits borrow =>
          rw [h_rec] at h
          cases borrow with
          | false => cases h
          | true =>
              cases d with
              | mk val hlt =>
                  cases val with
                  | zero =>
                      exact ⟨rfl, ih h_rec⟩
                  | successor d' => cases h

theorem empty_of_predecessorList_borrow_true_allZero {a digits : Sequences.List Digit}
  (h : predecessorList a = ⟨digits, true⟩) (h_digits : AllZero digits) :
  a = Sequences.List.empty := by
  induction a generalizing digits with
  | empty => rfl
  | firstElement d ds ih =>
      unfold predecessorList at h
      cases h_rec : predecessorList ds with
      | mk tailDigits borrow =>
          rw [h_rec] at h
          cases borrow with
          | false => cases h
          | true =>
              cases d with
              | mk val hlt =>
                  cases val with
                  | zero =>
                      cases h
                      exact False.elim (CardinalNatural.Peano.successor_ne_zero _ h_digits.1)
                  | successor d' => cases h

theorem representsOne_of_predecessorList_borrow_false_allZero
  {a digits : Sequences.List Digit}
  (h : predecessorList a = ⟨digits, false⟩) (h_digits : AllZero digits) :
  RepresentsOne a := by
  induction a generalizing digits with
  | empty => cases h
  | firstElement d ds ih =>
      unfold predecessorList at h
      cases h_rec : predecessorList ds with
      | mk tailDigits borrow =>
          rw [h_rec] at h
          cases borrow with
          | false =>
              cases h
              cases d with
              | mk val hlt =>
                  cases val with
                  | zero =>
                      exact RepresentsOne.leadingZero (ih h_rec h_digits.2)
                  | successor d' =>
                      exact False.elim (CardinalNatural.Peano.successor_ne_zero _ h_digits.1)
          | true =>
              cases d with
              | mk val hlt =>
                  cases val with
                  | zero => cases h
                  | successor d' =>
                      cases h
                      cases d' with
                      | zero =>
                          have h_ds_empty := empty_of_predecessorList_borrow_true_allZero h_rec h_digits.2
                          subst ds
                          exact RepresentsOne.one
                      | successor d'' =>
                          exact False.elim (CardinalNatural.Peano.successor_ne_zero _ h_digits.1)

theorem allZero_or_hasNonZero (a : Sequences.List Digit) : AllZero a ∨ HasNonZero a := by
  induction a with
  | empty => exact Or.inl trivial
  | firstElement d ds ih =>
      cases d with
      | mk val hlt =>
          cases val with
          | zero =>
              cases ih with
              | inl hzero => exact Or.inl ⟨rfl, hzero⟩
              | inr hnz => exact Or.inr (Sequences.List.AnyElement.notFirst _ _ hnz)
          | successor d' =>
              exact Or.inr (Sequences.List.AnyElement.first _ _
                (CardinalNatural.Peano.successor_ne_zero d'))

theorem not_allZero_of_hasNonZero {a : Sequences.List Digit} (h : HasNonZero a) : ¬ AllZero a := by
  intro h_zero
  induction h with
  | first d ds hd => exact hd h_zero.1
  | notFirst d ds _ ih => exact ih h_zero.2

theorem normalizeList_eq_one_of_representsOne {a : Sequences.List Digit}
  (h : RepresentsOne a) : normalizeList a (by
    induction h with
    | one =>
        exact Sequences.List.AnyElement.first _ _
          (CardinalNatural.Peano.successor_ne_zero CardinalNatural.Peano.zero)
    | leadingZero _ ih => exact Sequences.List.AnyElement.notFirst _ _ ih) = one := by
  induction h with
  | one => rfl
  | leadingZero h ih =>
      unfold normalizeList
      rw [dif_pos rfl]
      exact ih

theorem equivalent_one_of_representsOne {a : Sequences.List Digit} (h_nonzero : HasNonZero a)
  (h : RepresentsOne a) : Equivalent ⟨a, h_nonzero⟩ one := by
  unfold Equivalent normalize
  exact normalizeList_eq_one_of_representsOne h

theorem hasNonZero_of_predecessorList_borrow_false {a digits : Sequences.List Digit}
  (h_nonzero : HasNonZero a) (h_not_one : ¬ Equivalent ⟨a, h_nonzero⟩ one)
  (h : predecessorList a = ⟨digits, false⟩) : HasNonZero digits := by
  cases allZero_or_hasNonZero digits with
  | inl h_zero =>
      exact False.elim (h_not_one (equivalent_one_of_representsOne h_nonzero
        (representsOne_of_predecessorList_borrow_false_allZero h h_zero)))
  | inr h_digits_nonzero => exact h_digits_nonzero

def predecessor (a : Decimal) (h : ¬ a ≈ one) : Decimal :=
  match h_result : predecessorList a.val with
  | ⟨_, true⟩ =>
      False.elim (not_allZero_of_hasNonZero a.property
        (allZero_of_predecessorList_borrow_true h_result))
  | ⟨digits, false⟩ =>
      ⟨digits, hasNonZero_of_predecessorList_borrow_false a.property h h_result⟩

theorem successorList_predecessorList (a : Sequences.List Digit) :
  successorList (predecessorList a).1 = ⟨a, (predecessorList a).2⟩ := by
  induction a with
  | empty => rfl
  | firstElement d ds ih =>
      unfold predecessorList
      cases h_predecessor : predecessorList ds with
      | mk digits borrow =>
          rw [h_predecessor] at ih
          cases borrow with
          | false =>
              simp_all [successorList]
          | true =>
              cases d with
              | mk val hlt =>
                  cases val
                  · have h_not_lt := CardinalNatural.Peano.not_lt_self CardinalNatural.Peano.ten
                    simp_all [successorList, CardinalNatural.Peano.ten,
                      CardinalNatural.Peano.isLessThan_eq_true_iff_lt]
                  · simp_all [successorList,
                      CardinalNatural.Peano.isLessThan_eq_true_iff_lt]

theorem successor_predecessor (d : Decimal) (h : ¬ d ≈ one) :
  (d.predecessor h).successor = d := by
  cases h_predecessor : predecessorList d.val with
  | mk digits borrow =>
      cases borrow with
      | true =>
          exact False.elim (not_allZero_of_hasNonZero d.property
            (allZero_of_predecessorList_borrow_true h_predecessor))
      | false =>
          apply Subtype.ext
          have h_predecessor_val : (d.predecessor h).val = digits := by
            unfold predecessor
            split
            · next _ h_result =>
                rw [h_predecessor] at h_result
                cases h_result
            · next resultDigits h_result =>
                rw [h_predecessor] at h_result
                injection h_result with h_digits
                exact h_digits.symm
          have h_successor := successorList_predecessorList d.val
          rw [h_predecessor] at h_successor
          dsimp only at h_successor
          have h_successor_predecessor :
              successorList (d.predecessor h).val = ⟨d.val, false⟩ := by
            rw [h_predecessor_val, h_successor]
          unfold successor
          split
          · next _ h_result =>
              rw [h_successor_predecessor] at h_result
              cases h_result
          · next resultDigits h_result =>
              rw [h_successor_predecessor] at h_result
              injection h_result with h_digits
              exact h_digits.symm

def LessThanAlignedLists (x y : Sequences.List Digit)
  (h : Sequences.List.SameLength x y) : Prop :=
  match x, y with
  | .empty, .empty => False
  | .firstElement d1 ds1, .firstElement d2 ds2 =>
      d1.val < d2.val ∨
        (d1.val = d2.val ∧ LessThanAlignedLists ds1 ds2 (by cases h; assumption))
  | .empty, .firstElement _ _ => False.elim (by cases h)
  | .firstElement _ _, .empty => False.elim (by cases h)

def isLessThanAlignedLists (x y : Sequences.List Digit)
  (h : Sequences.List.SameLength x y) : Bool :=
  match x, y with
  | .empty, .empty => false
  | .firstElement dx dxs, .firstElement dy dys =>
      if _ : CardinalNatural.Peano.isLessThan dx.val dy.val then
        true
      else if _ : CardinalNatural.Peano.isLessThan dy.val dx.val then
        false
      else
        isLessThanAlignedLists dxs dys (by cases h; assumption)
  | .empty, .firstElement _ _ => False.elim (by cases h)
  | .firstElement _ _, .empty => False.elim (by cases h)

theorem isLessThanAlignedLists_iff_lessThanAlignedLists (x y : Sequences.List Digit)
  (h : Sequences.List.SameLength x y) :
  isLessThanAlignedLists x y h ↔ LessThanAlignedLists x y h := by
  induction h with
  | empty =>
      simp [isLessThanAlignedLists, LessThanAlignedLists]
  | firstElement htail ih =>
      rename_i dx dy dxs dys
      unfold isLessThanAlignedLists LessThanAlignedLists
      split
      · next h_dx_lt_dy_bool =>
          constructor
          · intro _
            exact Or.inl ((CardinalNatural.Peano.isLessThan_eq_true_iff_lt _ _).mp h_dx_lt_dy_bool)
          · intro _
            rfl
      · next h_not_dx_lt_dy_bool =>
          split
          · next h_dy_lt_dx_bool =>
              constructor
              · intro h_false
                cases h_false
              · intro h_less
                have h_not_dx_lt_dy : ¬ dx.val < dy.val :=
                  (CardinalNatural.Peano.isLessThan_eq_false_iff_not_lt _ _).mp
                    (eq_false_of_ne_true h_not_dx_lt_dy_bool)
                have h_dy_lt_dx : dy.val < dx.val :=
                  (CardinalNatural.Peano.isLessThan_eq_true_iff_lt _ _).mp h_dy_lt_dx_bool
                cases h_less with
                | inl h_dx_lt_dy =>
                    exact False.elim (h_not_dx_lt_dy h_dx_lt_dy)
                | inr h_eq_tail =>
                    obtain ⟨h_dx_eq_dy, _⟩ := h_eq_tail
                    rw [h_dx_eq_dy] at h_dy_lt_dx
                    exact False.elim (CardinalNatural.Peano.not_lt_self dy.val h_dy_lt_dx)
          · next h_not_dy_lt_dx_bool =>
              have h_not_dx_lt_dy : ¬ dx.val < dy.val :=
                (CardinalNatural.Peano.isLessThan_eq_false_iff_not_lt _ _).mp
                  (eq_false_of_ne_true h_not_dx_lt_dy_bool)
              have h_not_dy_lt_dx : ¬ dy.val < dx.val :=
                (CardinalNatural.Peano.isLessThan_eq_false_iff_not_lt _ _).mp
                  (eq_false_of_ne_true h_not_dy_lt_dx_bool)
              have h_dx_eq_dy : dx.val = dy.val := by
                cases CardinalNatural.Peano.trichotomy_or dx.val dy.val with
                | inl h_dx_lt_dy =>
                    exact False.elim (h_not_dx_lt_dy h_dx_lt_dy)
                | inr h_eq_or_gt =>
                    cases h_eq_or_gt with
                    | inl h_eq => exact h_eq
                    | inr h_dy_lt_dx =>
                        exact False.elim (h_not_dy_lt_dx h_dy_lt_dx)
              constructor
              · intro h_tail_bool
                exact Or.inr ⟨h_dx_eq_dy, ih.mp h_tail_bool⟩
              · intro h_less
                cases h_less with
                | inl h_dx_lt_dy =>
                    exact False.elim (h_not_dx_lt_dy h_dx_lt_dy)
                | inr h_eq_tail =>
                    exact ih.mpr h_eq_tail.2


theorem digit_carry_lt_twenty (a : Digit) (b : Digit) :
  a.val + b.val < CardinalNatural.Peano.ten + CardinalNatural.Peano.ten := by
  have h := digit_sum_lt_twenty a.val b.val false a.property b.property
  have h2 : (if false = true then CardinalNatural.Peano.one else CardinalNatural.Peano.zero) = CardinalNatural.Peano.zero := rfl
  rw [h2] at h
  rw [CardinalNatural.Peano.add_zero] at h
  exact h

def addPartialListDigit (a : Sequences.List Digit) (b : Digit) : Sequences.List Digit × Digit :=
  match a with
  | .empty => ⟨.empty, b⟩
  | .firstElement d ds =>
    let (ds', carry) := addPartialListDigit ds b
    let sum := d.val + carry.val
    if h : sum < CardinalNatural.Peano.ten then
      (.firstElement ⟨sum, h⟩ ds', zeroDigit)
    else
      have h_false : sum.isLessThan CardinalNatural.Peano.ten = false := by
        exact (CardinalNatural.Peano.isLessThan_eq_false_iff_not_lt sum _).mpr h
      have h1 : CardinalNatural.Peano.ten ≤ sum := CardinalNatural.Peano.isLessThan_false_implies_le h_false
      have h2 : sum < CardinalNatural.Peano.ten + CardinalNatural.Peano.ten := by
        exact digit_carry_lt_twenty d carry
      have h3 : CardinalNatural.Peano.subtract sum CardinalNatural.Peano.ten h1 < CardinalNatural.Peano.ten := by
        exact subtract_ten_lt_ten sum h1 h2
      (.firstElement ⟨CardinalNatural.Peano.subtract sum CardinalNatural.Peano.ten h1, h3⟩ ds', oneDigit)

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

theorem addAlignedLists_commutative (a b : Sequences.List Digit)
  (h : Sequences.List.SameLength a b) :
  addAlignedLists a b h = addAlignedLists b a (Sequences.List.sameLength_commutative h) := by
  induction h with
  | empty => rfl
  | firstElement htail ih =>
      unfold addAlignedLists
      rw [ih]
      simp only [CardinalNatural.Peano.add_commutative]

theorem hasNonZero_of_addAlignedLists_carry_true {a b digits : Sequences.List Digit}
  {h : Sequences.List.SameLength a b} (_ : addAlignedLists a b h = ⟨digits, true⟩) :
  HasNonZero (Sequences.List.firstElement ⟨CardinalNatural.Peano.one, CardinalNatural.Peano.one_lt_ten⟩ digits) := by
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

def isLessThan (x y : Decimal) : Bool :=
  let pair := Sequences.List.padAtStartToSameLength x.val y.val zeroDigit
  isLessThanAlignedLists pair.1 pair.2
    (Sequences.List.padAtStartToSameLength_sameLength x.val y.val zeroDigit)

def LessThan (x y : Decimal) : Prop :=
  let pair := Sequences.List.padAtStartToSameLength x.val y.val zeroDigit
  LessThanAlignedLists pair.1 pair.2
    (Sequences.List.padAtStartToSameLength_sameLength x.val y.val zeroDigit)

theorem isLessThan_iff_lessThan (x y : Decimal) :
  isLessThan x y ↔ LessThan x y := by
  unfold isLessThan LessThan
  dsimp only
  exact isLessThanAlignedLists_iff_lessThanAlignedLists _ _ _

theorem hasNonZero_of_subtractAlignedLists_borrow_true {a b digits : Sequences.List Digit}
  (h_same : Sequences.List.SameLength a b)
  (h_subtract : subtractAlignedLists a b h_same = ⟨digits, true⟩) :
  HasNonZero digits := by
  induction h_same generalizing digits with
  | empty =>
      unfold subtractAlignedLists at h_subtract
      cases h_subtract
  | firstElement htail ih =>
      rename_i da db das dbs
      unfold subtractAlignedLists at h_subtract
      cases h_rec : subtractAlignedLists das dbs htail with
      | mk tailDigits tailBorrow =>
          rw [h_rec] at h_subtract
          cases tailBorrow with
          | false =>
              simp at h_subtract
              split at h_subtract
              · next h_da_lt_db =>
                  injection h_subtract with h_digits _
                  subst digits
                  apply Sequences.List.AnyElement.first
                  apply CardinalNatural.Peano.subtract_ne_zero_of_lt
                  exact CardinalNatural.Peano.lt_le_trans db.property
                    (CardinalNatural.Peano.le_add_self_right da.val CardinalNatural.Peano.ten)
              · cases h_subtract
          | true =>
              simp at h_subtract
              split at h_subtract
              · injection h_subtract with h_digits _
                subst digits
                by_cases h_digit_nonzero :
                    CardinalNatural.Peano.subtract (da.val + CardinalNatural.Peano.ten) db.val.successor
                      (by
                        exact CardinalNatural.Peano.le_trans (digit_val_successor_le_ten db)
                          (CardinalNatural.Peano.le_add_self_right da.val CardinalNatural.Peano.ten)) ≠ CardinalNatural.Peano.zero
                · apply Sequences.List.AnyElement.first
                  exact h_digit_nonzero
                · apply Sequences.List.AnyElement.notFirst
                  exact ih h_rec
              · cases h_subtract

theorem subtractAlignedLists_borrow_false_of_lessThan {a b : Sequences.List Digit}
  (h_same : Sequences.List.SameLength a b)
  (h_lt : LessThanAlignedLists b a (Sequences.List.sameLength_commutative h_same)) :
  (subtractAlignedLists a b h_same).2 = false := by
  induction h_same with
  | empty =>
      cases h_lt
  | firstElement htail ih =>
      rename_i da db das dbs
      unfold subtractAlignedLists
      cases h_rec : subtractAlignedLists das dbs htail with
      | mk digits borrow =>
          cases h_lt with
          | inl h_db_lt_da =>
              cases borrow with
              | false =>
                  have h_not : ¬ da.val < db.val := CardinalNatural.Peano.not_lt_of_lt h_db_lt_da
                  simp [h_not]
              | true =>
                  have h_not : ¬ da.val < db.val.successor :=
                    CardinalNatural.Peano.cardinal_not_lt_of_le (CardinalNatural.Peano.succ_le_of_lt h_db_lt_da)
                  simp [h_not]
          | inr h_eq_tail =>
              obtain ⟨h_digit_eq, h_tail_lt⟩ := h_eq_tail
              have h_borrow := ih h_tail_lt
              rw [h_rec] at h_borrow
              dsimp only at h_borrow
              cases borrow with
              | false =>
                  have h_not : ¬ da.val < db.val := by
                    intro hlt
                    rw [← h_digit_eq] at hlt
                    exact CardinalNatural.Peano.not_lt_self db.val hlt
                  simp [h_not]
              | true =>
                  cases h_borrow


theorem hasNonZero_of_subtractAlignedLists_borrow_false_of_lessThan {a b digits : Sequences.List Digit}
  (h_same : Sequences.List.SameLength a b)
  (h_lt : LessThanAlignedLists b a (Sequences.List.sameLength_commutative h_same))
  (h_subtract : subtractAlignedLists a b h_same = ⟨digits, false⟩) :
  HasNonZero digits := by
  induction h_same generalizing digits with
  | empty =>
      cases h_lt
  | firstElement htail ih =>
      rename_i da db das dbs
      unfold subtractAlignedLists at h_subtract
      cases h_rec : subtractAlignedLists das dbs htail with
      | mk tailDigits tailBorrow =>
          rw [h_rec] at h_subtract
          cases h_lt with
          | inl h_db_lt_da =>
              cases tailBorrow with
              | false =>
                  simp at h_subtract
                  split at h_subtract
                  · cases h_subtract
                  · next h_not_lt =>
                      injection h_subtract with h_digits _
                      subst digits
                      apply Sequences.List.AnyElement.first
                      exact CardinalNatural.Peano.subtract_ne_zero_of_lt
                        (CardinalNatural.Peano.not_lt_implies_le h_not_lt) h_db_lt_da
              | true =>
                  simp at h_subtract
                  split at h_subtract
                  · cases h_subtract
                  · next h_not_lt =>
                      injection h_subtract with h_digits _
                      subst digits
                      cases CardinalNatural.Peano.trichotomy_or db.val.successor da.val with
                      | inl h_withBorrow_lt =>
                          apply Sequences.List.AnyElement.first
                          exact CardinalNatural.Peano.subtract_ne_zero_of_lt
                            (CardinalNatural.Peano.not_lt_implies_le h_not_lt) h_withBorrow_lt
                      | inr h_eq_or_gt =>
                          cases h_eq_or_gt with
                          | inl _ =>
                              apply Sequences.List.AnyElement.notFirst
                              exact hasNonZero_of_subtractAlignedLists_borrow_true htail h_rec
                          | inr h_da_lt_withBorrow =>
                              exact False.elim (h_not_lt h_da_lt_withBorrow)
          | inr h_eq_tail =>
              obtain ⟨h_digit_eq, h_tail_lt⟩ := h_eq_tail
              cases tailBorrow with
              | false =>
                  simp at h_subtract
                  split at h_subtract
                  · next h_da_lt_db =>
                      rw [h_digit_eq] at h_da_lt_db
                      exact False.elim (CardinalNatural.Peano.not_lt_self da.val h_da_lt_db)
                  · injection h_subtract with h_digits _
                    subst digits
                    apply Sequences.List.AnyElement.notFirst
                    exact ih h_tail_lt h_rec
              | true =>
                  simp at h_subtract
                  split at h_subtract
                  · cases h_subtract
                  · next h_not_lt =>
                      rw [h_digit_eq] at h_not_lt
                      exact False.elim (h_not_lt CardinalNatural.Peano.LessThan.base)

instance : LT Decimal where
  lt := LessThan

instance (x y : Decimal) : Decidable (x < y) :=
  if h : isLessThan x y then
    isTrue (isLessThan_iff_lessThan x y |>.mp h)
  else
    isFalse (fun h''' => h (isLessThan_iff_lessThan x y |>.mpr h'''))

def LessThanOrEquivalent (x y : Decimal) : Prop := x < y ∨ x ≈ y

instance : LE Decimal where
  le := LessThanOrEquivalent

theorem LessThanAlignedLists_congr {a b c d : Sequences.List Digit}
  (h₁ : Sequences.List.SameLength a b) (h₂ : Sequences.List.SameLength c d)
  (ha : a = c) (hb : b = d) :
  LessThanAlignedLists a b h₁ → LessThanAlignedLists c d h₂ := by
  subst c
  subst d
  intro h
  exact h

theorem lessThanAlignedLists_padded_of_lt {a b : Decimal} (h : b < a) :
  let pair := Sequences.List.padAtStartToSameLength a.val b.val zeroDigit
  LessThanAlignedLists pair.2 pair.1
    (Sequences.List.sameLength_commutative
      (Sequences.List.padAtStartToSameLength_sameLength a.val b.val zeroDigit)) := by
  change LessThan b a at h
  unfold LessThan at h
  dsimp only at h ⊢
  have hpad := Sequences.List.padAtStartToSameLength_commutative b.val a.val zeroDigit
  have h_fst := congrArg Prod.fst hpad
  have h_snd := congrArg Prod.snd hpad
  dsimp only at h_fst h_snd
  exact LessThanAlignedLists_congr _ _ h_snd.symm h_fst.symm h

def subtract (a b : Decimal) (h : b < a) : Decimal :=
  let pair := Sequences.List.padAtStartToSameLength a.val b.val zeroDigit
  let h_same : Sequences.List.SameLength pair.1 pair.2 :=
    Sequences.List.padAtStartToSameLength_sameLength a.val b.val zeroDigit
  match h_subtract : Decimal.subtractAlignedLists pair.1 pair.2 h_same with
  | ⟨digits, borrow⟩ =>
      if h2 : borrow then
        False.elim (by
          have h_borrow_false := subtractAlignedLists_borrow_false_of_lessThan
            h_same (lessThanAlignedLists_padded_of_lt h)
          rw [h_subtract] at h_borrow_false
          dsimp only at h_borrow_false
          rw [h2] at h_borrow_false
          cases h_borrow_false)
      else
        ⟨digits, by
          exact hasNonZero_of_subtractAlignedLists_borrow_false_of_lessThan
            h_same (lessThanAlignedLists_padded_of_lt h)
            (by
              rw [h_subtract]
              cases borrow with
              | false => rfl
              | true => exact False.elim (h2 rfl))
        ⟩

def add (a b : Decimal) : Decimal :=
  let pair := Sequences.List.padAtStartToSameLength a.val b.val zeroDigit
  let h_same : Sequences.List.SameLength pair.1 pair.2 :=
    Sequences.List.padAtStartToSameLength_sameLength a.val b.val zeroDigit
  match h_add : addAlignedLists pair.1 pair.2 h_same with
  | ⟨digits, true⟩ =>
      ⟨Sequences.List.firstElement ⟨CardinalNatural.Peano.one, CardinalNatural.Peano.one_lt_ten⟩ digits,
        hasNonZero_of_addAlignedLists_carry_true h_add⟩
  | ⟨digits, false⟩ =>
      ⟨digits, by
        apply hasNonZero_of_addAlignedLists_carry_false h_same
        · exact hasNonZero_padAtStartToSameLength_fst a.val b.val zeroDigit a.property
        · exact h_add
      ⟩

instance : Add Decimal where
  add := add

theorem addAlignedLists_eq_of_swapped {a b c d : Sequences.List Digit}
  (h₁ : Sequences.List.SameLength a b) (h₂ : Sequences.List.SameLength c d)
  (hc : c = b) (hd : d = a) :
  addAlignedLists a b h₁ = addAlignedLists c d h₂ := by
  subst c
  subst d
  exact addAlignedLists_commutative a b h₁

theorem addAlignedLists_after_padding_commutative (a b : Sequences.List Digit) :
  addAlignedLists
      (Sequences.List.padAtStartToSameLength a b zeroDigit).1
      (Sequences.List.padAtStartToSameLength a b zeroDigit).2
      (Sequences.List.padAtStartToSameLength_sameLength a b zeroDigit) =
    addAlignedLists
      (Sequences.List.padAtStartToSameLength b a zeroDigit).1
      (Sequences.List.padAtStartToSameLength b a zeroDigit).2
      (Sequences.List.padAtStartToSameLength_sameLength b a zeroDigit) := by
  have hpad := Sequences.List.padAtStartToSameLength_commutative a b zeroDigit
  exact addAlignedLists_eq_of_swapped _ _
    (congrArg Prod.fst hpad) (congrArg Prod.snd hpad)

theorem add_val_of_aligned_result (a b : Decimal) (digits : Sequences.List Digit) (carry : Bool)
  (h : addAlignedLists
    (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).1
    (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).2
    (Sequences.List.padAtStartToSameLength_sameLength a.val b.val zeroDigit) = ⟨digits, carry⟩) :
  (a + b).val = if carry then
    Sequences.List.firstElement ⟨CardinalNatural.Peano.one, CardinalNatural.Peano.one_lt_ten⟩ digits
  else digits := by
  change (add a b).val = _
  unfold add
  dsimp only
  split
  · next resultDigits h_result =>
      rw [h_result] at h
      cases carry with
      | false => cases h
      | true =>
          injection h with h_digits
          subst resultDigits
          rfl
  · next resultDigits h_result =>
      rw [h_result] at h
      cases carry with
      | false => injection h
      | true => cases h

theorem add_commutative (a b : Decimal) : a + b = b + a := by
  have hcomm := addAlignedLists_after_padding_commutative a.val b.val
  cases hab : addAlignedLists
      (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).1
      (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).2
      (Sequences.List.padAtStartToSameLength_sameLength a.val b.val zeroDigit) with
  | mk digits carry =>
      have hba : addAlignedLists
          (Sequences.List.padAtStartToSameLength b.val a.val zeroDigit).1
          (Sequences.List.padAtStartToSameLength b.val a.val zeroDigit).2
          (Sequences.List.padAtStartToSameLength_sameLength b.val a.val zeroDigit) =
          ⟨digits, carry⟩ := hcomm.symm.trans hab
      apply Subtype.ext
      rw [add_val_of_aligned_result a b digits carry hab,
        add_val_of_aligned_result b a digits carry hba]

theorem equivalent_add_commutative (a b : Decimal) : a + b ≈ b + a := by
  rw [add_commutative]
  rfl

-- toCardinalList l acc = acc * 10^len(l) + toCardinalList l 0
theorem toCardinalList_acc_split (l : Sequences.List Digit)
    (acc : CardinalNatural.Peano) :
    toCardinalList l acc =
      acc * CardinalNatural.Peano.tenPow l.length + toCardinalList l CardinalNatural.Peano.zero := by
  induction l generalizing acc with
  | empty =>
    simp only [toCardinalList, Sequences.List.length, CardinalNatural.Peano.tenPow,
               CardinalNatural.Peano.multiply_one, CardinalNatural.Peano.add_zero]
  | firstElement d ds ih =>
    simp only [toCardinalList, Sequences.List.length,
               CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.zero_add]
    rw [ih (acc * CardinalNatural.Peano.ten + d.val), ih d.val, CardinalNatural.Peano.tenPow_add_one,
        CardinalNatural.Peano.multiply_distributive_over_add_left,
        CardinalNatural.Peano.multiply_associative,
        CardinalNatural.Peano.add_associative]

theorem toCardinalList_firstElement (d : Digit) (ds : Sequences.List Digit) :
  toCardinalList (Sequences.List.firstElement d ds) CardinalNatural.Peano.zero =
    d.val * CardinalNatural.Peano.tenPow ds.length +
      toCardinalList ds CardinalNatural.Peano.zero := by
  change toCardinalList ds (CardinalNatural.Peano.zero * CardinalNatural.Peano.ten + d.val) = _
  rw [CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.zero_add]
  exact toCardinalList_acc_split ds d.val

theorem successorList_spec (a : Sequences.List Digit) :
  let result := successorList a
  result.1.length = a.length ∧
    toCardinalList result.1 CardinalNatural.Peano.zero +
        (if result.2 then CardinalNatural.Peano.tenPow a.length else CardinalNatural.Peano.zero) =
      toCardinalList a CardinalNatural.Peano.zero + CardinalNatural.Peano.one := by
  induction a with
  | empty =>
      simp [successorList, toCardinalList, Sequences.List.length, CardinalNatural.Peano.tenPow]
  | firstElement d ds ih =>
      unfold successorList
      dsimp only
      cases h_rec : successorList ds with
      | mk digits carry =>
          rw [h_rec] at ih
          dsimp only at ih
          obtain ⟨h_length, ih_value⟩ := ih
          cases carry with
          | false =>
              simp at ih_value ⊢
              constructor
              · simp [Sequences.List.length, h_length]
              · simp only [toCardinalList_firstElement]
                rw [h_length, ih_value, CardinalNatural.Peano.add_associative]
          | true =>
              simp at ih_value ⊢
              split
              · constructor
                · simp [Sequences.List.length, h_length]
                · simp only [toCardinalList_firstElement, if_neg Bool.false_ne_true]
                  rw [h_length, CardinalNatural.Peano.successor_multiply]
                  calc
                    _ = d.val * CardinalNatural.Peano.tenPow ds.length +
                          (toCardinalList digits CardinalNatural.Peano.zero +
                            CardinalNatural.Peano.tenPow ds.length) := by
                              simp only [CardinalNatural.Peano.zero_add,
                                CardinalNatural.Peano.add_associative,
                                CardinalNatural.Peano.add_commutative,
                                CardinalNatural.Peano.add_left_commutative]
                    _ = _ := by rw [ih_value, CardinalNatural.Peano.add_associative]
              · constructor
                · simp [Sequences.List.length, h_length]
                · simp only [toCardinalList_firstElement, Sequences.List.length,
                    CardinalNatural.Peano.tenPow_add_one, if_true]
                  rw [h_length, CardinalNatural.Peano.zero_multiply,
                    CardinalNatural.Peano.zero_add]
                  have h_digit : d.val.successor = CardinalNatural.Peano.ten := by
                    cases CardinalNatural.Peano.succ_le_of_lt d.property with
                    | inl hlt =>
                        exact False.elim (‹¬d.val.successor.isLessThan CardinalNatural.Peano.ten = true›
                          ((CardinalNatural.Peano.isLessThan_eq_true_iff_lt _ _).mpr hlt))
                    | inr heq => exact heq
                  calc
                    _ = CardinalNatural.Peano.ten * CardinalNatural.Peano.tenPow ds.length +
                          toCardinalList digits CardinalNatural.Peano.zero :=
                            CardinalNatural.Peano.add_commutative _ _
                    _ = d.val.successor * CardinalNatural.Peano.tenPow ds.length +
                          toCardinalList digits CardinalNatural.Peano.zero := by rw [h_digit]
                    _ = d.val * CardinalNatural.Peano.tenPow ds.length +
                          (toCardinalList digits CardinalNatural.Peano.zero +
                            CardinalNatural.Peano.tenPow ds.length) := by
                              rw [CardinalNatural.Peano.successor_multiply]
                              simp only [CardinalNatural.Peano.add_associative,
                                CardinalNatural.Peano.add_commutative,
                                CardinalNatural.Peano.add_left_commutative]
                    _ = _ := by rw [ih_value, CardinalNatural.Peano.add_associative]

theorem toCardinalPeano_successor (a : Decimal) :
  toCardinalPeano (successor a) = (toCardinalPeano a).successor := by
  unfold successor toCardinalPeano
  split
  · next digits h_successor =>
      have h_spec := successorList_spec a.val
      rw [h_successor] at h_spec
      dsimp only at h_spec
      obtain ⟨h_length, h_value⟩ := h_spec
      simp at h_value
      rw [toCardinalList_firstElement, h_length, CardinalNatural.Peano.one_multiply]
      calc
        _ = toCardinalList digits CardinalNatural.Peano.zero +
              CardinalNatural.Peano.tenPow a.val.length := CardinalNatural.Peano.add_commutative _ _
        _ = toCardinalList a.val CardinalNatural.Peano.zero + CardinalNatural.Peano.one := h_value
        _ = (toCardinalList a.val CardinalNatural.Peano.zero).successor := rfl
  · next digits h_successor =>
      have h_spec := successorList_spec a.val
      rw [h_successor] at h_spec
      dsimp only at h_spec
      simpa using h_spec.2

theorem successor_toPeano (x : Decimal) :
  x.successor.toPeano = x.toPeano.successor := by
  unfold toPeano
  calc
    _ = CardinalNatural.Peano.toOrdinal (toCardinalPeano x).successor
        (CardinalNatural.Peano.successor_ne_zero _) :=
      CardinalNatural.Peano.toOrdinal_congr (toCardinalPeano_successor x) _ _
    _ = _ := CardinalNatural.Peano.toOrdinal_successor _ _ (toCardinalPeano_ne_zero x)

theorem predecessor_toPeano (x : Decimal) (h : ¬ x ≈ one) :
  ∃ h2, toPeano (x.predecessor h) = x.toPeano.predecessor h2 := by
  let y := toPeano (x.predecessor h)
  have h_successor : x.toPeano = OrdinalNatural.Peano.successor y := by
    rw [← successor_toPeano (x.predecessor h)]
    exact congrArg toPeano (successor_predecessor x h).symm
  cases h_toPeano : x.toPeano with
  | one =>
      rw [h_toPeano] at h_successor
      cases h_successor
  | successor p =>
      have h2 : OrdinalNatural.Peano.successor p ≠ OrdinalNatural.Peano.one := by
        intro h_one
        cases h_one
      exists h2
      have h_y : y = p := by
        rw [h_toPeano] at h_successor
        injection h_successor with h_p
        exact h_p.symm
      exact h_y

theorem successor_ne_one (x : Decimal) : ¬ x.successor ≈ one := by
  intro h_one
  have h_toPeano := toPeano_eq_of_equivalent h_one
  rw [successor_toPeano] at h_toPeano
  cases h_toPeano

theorem toCardinalList_padAtStart_zeroDigit (l : Sequences.List Digit)
  (n : CardinalNatural.Peano) :
  toCardinalList (Sequences.List.padAtStart l zeroDigit n) CardinalNatural.Peano.zero =
    toCardinalList l CardinalNatural.Peano.zero := by
  induction n generalizing l with
  | zero => rfl
  | successor n ih =>
      unfold Sequences.List.padAtStart
      rw [ih]
      rfl

theorem toCardinalList_padAtStartToSameLength_fst (a b : Sequences.List Digit) :
  toCardinalList (Sequences.List.padAtStartToSameLength a b zeroDigit).1
      CardinalNatural.Peano.zero =
    toCardinalList a CardinalNatural.Peano.zero := by
  unfold Sequences.List.padAtStartToSameLength
  dsimp only
  split
  · rfl
  · exact toCardinalList_padAtStart_zeroDigit _ _

theorem toCardinalList_padAtStartToSameLength_snd (a b : Sequences.List Digit) :
  toCardinalList (Sequences.List.padAtStartToSameLength a b zeroDigit).2
      CardinalNatural.Peano.zero =
    toCardinalList b CardinalNatural.Peano.zero := by
  unfold Sequences.List.padAtStartToSameLength
  dsimp only
  split
  · exact toCardinalList_padAtStart_zeroDigit _ _
  · rfl

theorem addAlignedLists_spec {a b : Sequences.List Digit}
  (h : Sequences.List.SameLength a b) :
  let result := addAlignedLists a b h
  result.1.length = a.length ∧
    toCardinalList result.1 CardinalNatural.Peano.zero +
        (if result.2 then CardinalNatural.Peano.tenPow a.length else CardinalNatural.Peano.zero) =
      toCardinalList a CardinalNatural.Peano.zero +
        toCardinalList b CardinalNatural.Peano.zero := by
  induction h with
  | empty =>
      simp [addAlignedLists, toCardinalList, Sequences.List.length]
  | @firstElement da db das dbs htail ih =>
      unfold addAlignedLists
      dsimp only
      cases h_rec : addAlignedLists das dbs htail with
      | mk digits carry =>
          rw [h_rec] at ih
          dsimp only at ih
          obtain ⟨h_length, ih_value⟩ := ih
          have h_tail_lengths := Sequences.List.sameLength_length_eq htail
          cases carry with
          | false =>
              simp at ih_value ⊢
              split
              · constructor
                · simp [Sequences.List.length, h_length]
                · simp only [toCardinalList_firstElement]
                  simp only [if_neg Bool.false_ne_true]
                  rw [h_length, ← h_tail_lengths]
                  rw [CardinalNatural.Peano.multiply_distributive_over_add_left, ih_value]
                  simp
                  simp only [CardinalNatural.Peano.add_associative, CardinalNatural.Peano.add_left_commutative]
              · constructor
                · simp [Sequences.List.length, h_length]
                · simp only [toCardinalList_firstElement, Sequences.List.length,
                    CardinalNatural.Peano.tenPow_add_one]
                  rw [h_length, ← h_tail_lengths]
                  have h_digit := CardinalNatural.Peano.subtract_add_cancel
                    (da.val + db.val) CardinalNatural.Peano.ten
                    (CardinalNatural.Peano.isLessThan_false_implies_le (eq_false_of_ne_true ‹_›))
                  simp only [if_true]
                  calc
                    _ = (CardinalNatural.Peano.subtract
                            (da.val + db.val)
                            CardinalNatural.Peano.ten _ + CardinalNatural.Peano.ten) *
                          CardinalNatural.Peano.tenPow das.length +
                        toCardinalList digits CardinalNatural.Peano.zero := by
                          rw [CardinalNatural.Peano.multiply_distributive_over_add_left]
                          rw [CardinalNatural.Peano.add_associative,
                            CardinalNatural.Peano.add_commutative
                              (toCardinalList digits CardinalNatural.Peano.zero)
                              (CardinalNatural.Peano.ten * CardinalNatural.Peano.tenPow das.length),
                            ← CardinalNatural.Peano.add_associative]
                    _ = _ := by
                      rw [h_digit, CardinalNatural.Peano.multiply_distributive_over_add_left, ih_value]
                      simp only [CardinalNatural.Peano.add_associative,
                        CardinalNatural.Peano.add_left_commutative]
          | true =>
              simp at ih_value ⊢
              split
              · constructor
                · simp [Sequences.List.length, h_length]
                · simp only [toCardinalList_firstElement]
                  simp only [if_neg Bool.false_ne_true]
                  rw [h_length, ← h_tail_lengths]
                  rw [CardinalNatural.Peano.multiply_distributive_over_add_left]
                  rw [CardinalNatural.Peano.multiply_distributive_over_add_left]
                  rw [CardinalNatural.Peano.one_multiply]
                  calc
                    _ = da.val * CardinalNatural.Peano.tenPow das.length +
                          db.val * CardinalNatural.Peano.tenPow das.length +
                          (toCardinalList digits CardinalNatural.Peano.zero +
                            CardinalNatural.Peano.tenPow das.length) := by
                              simp
                              simp only [CardinalNatural.Peano.add_associative,
                                CardinalNatural.Peano.add_commutative, CardinalNatural.Peano.add_left_commutative]
                    _ = _ := by rw [ih_value]; simp only [CardinalNatural.Peano.add_associative,
                      CardinalNatural.Peano.add_left_commutative]
              · constructor
                · simp [Sequences.List.length, h_length]
                · simp only [toCardinalList_firstElement, Sequences.List.length,
                    CardinalNatural.Peano.tenPow_add_one]
                  rw [h_length, ← h_tail_lengths]
                  have h_digit := CardinalNatural.Peano.subtract_add_cancel
                    (da.val + db.val + CardinalNatural.Peano.one) CardinalNatural.Peano.ten
                    (CardinalNatural.Peano.isLessThan_false_implies_le (eq_false_of_ne_true ‹_›))
                  simp only [if_true]
                  calc
                    _ = (CardinalNatural.Peano.subtract
                            (da.val + db.val + CardinalNatural.Peano.one)
                            CardinalNatural.Peano.ten _ + CardinalNatural.Peano.ten) *
                          CardinalNatural.Peano.tenPow das.length +
                        toCardinalList digits CardinalNatural.Peano.zero := by
                          rw [CardinalNatural.Peano.multiply_distributive_over_add_left]
                          simp only [CardinalNatural.Peano.add_commutative,
                            CardinalNatural.Peano.add_left_commutative]
                    _ = _ := by
                      rw [h_digit, CardinalNatural.Peano.multiply_distributive_over_add_left,
                        CardinalNatural.Peano.multiply_distributive_over_add_left,
                        CardinalNatural.Peano.one_multiply]
                      calc
                        _ = da.val * CardinalNatural.Peano.tenPow das.length +
                              db.val * CardinalNatural.Peano.tenPow das.length +
                              (toCardinalList digits CardinalNatural.Peano.zero +
                                CardinalNatural.Peano.tenPow das.length) := by simp only [
                                  CardinalNatural.Peano.add_associative,
                                  CardinalNatural.Peano.add_commutative,
                                  CardinalNatural.Peano.add_left_commutative]
                        _ = _ := by rw [ih_value]; simp only [CardinalNatural.Peano.add_associative,
                          CardinalNatural.Peano.add_left_commutative]



theorem subtractAlignedLists_spec {a b : Sequences.List Digit}
  (h : Sequences.List.SameLength a b) :
  let result := subtractAlignedLists a b h
  result.1.length = a.length ∧
    toCardinalList result.1 CardinalNatural.Peano.zero +
        toCardinalList b CardinalNatural.Peano.zero =
      toCardinalList a CardinalNatural.Peano.zero +
        (if result.2 then CardinalNatural.Peano.tenPow a.length else CardinalNatural.Peano.zero) := by
  induction h with
  | empty =>
      simp [subtractAlignedLists, toCardinalList, Sequences.List.length]
  | @firstElement da db das dbs htail ih =>
      unfold subtractAlignedLists
      dsimp only
      cases h_rec : subtractAlignedLists das dbs htail with
      | mk digits borrow =>
          rw [h_rec] at ih
          dsimp only at ih
          obtain ⟨h_length, ih_value⟩ := ih
          have h_tail_lengths := Sequences.List.sameLength_length_eq htail
          cases borrow with
          | false =>
              simp at ih_value ⊢
              split
              · next h_da_lt_db =>
                  constructor
                  · simp [Sequences.List.length, h_length]
                  · simp only [toCardinalList_firstElement, Sequences.List.length,
                      CardinalNatural.Peano.tenPow_add_one, if_true]
                    rw [h_length, ← h_tail_lengths]
                    have h_le : db.val ≤ da.val + CardinalNatural.Peano.ten := by
                      exact CardinalNatural.Peano.le_trans (digit_val_le_ten db)
                        (CardinalNatural.Peano.le_add_self_right da.val CardinalNatural.Peano.ten)
                    have h_digit := CardinalNatural.Peano.subtract_add_cancel
                      (da.val + CardinalNatural.Peano.ten) db.val h_le
                    calc
                      _ = (CardinalNatural.Peano.subtract (da.val + CardinalNatural.Peano.ten) db.val h_le + db.val) *
                            CardinalNatural.Peano.tenPow das.length +
                          (toCardinalList digits CardinalNatural.Peano.zero +
                            toCardinalList dbs CardinalNatural.Peano.zero) := by
                            rw [CardinalNatural.Peano.multiply_distributive_over_add_left]
                            exact CardinalNatural.Peano.add_pair_swap _ _ _ _
                      _ = (da.val + CardinalNatural.Peano.ten) * CardinalNatural.Peano.tenPow das.length +
                          toCardinalList das CardinalNatural.Peano.zero := by
                            rw [h_digit, ih_value]
                      _ = da.val * CardinalNatural.Peano.tenPow das.length +
                          toCardinalList das CardinalNatural.Peano.zero +
                            CardinalNatural.Peano.ten * CardinalNatural.Peano.tenPow das.length := by
                            rw [CardinalNatural.Peano.multiply_distributive_over_add_left]
                            exact CardinalNatural.Peano.add_right_commutative _ _ _
              · next h_not_lt =>
                  constructor
                  · simp [Sequences.List.length, h_length]
                  · simp only [toCardinalList_firstElement, Sequences.List.length]
                    simp only [if_neg Bool.false_ne_true]
                    rw [h_length, ← h_tail_lengths]
                    have h_le : db.val ≤ da.val := CardinalNatural.Peano.not_lt_implies_le h_not_lt
                    have h_digit := CardinalNatural.Peano.subtract_add_cancel da.val db.val h_le
                    calc
                      _ = (CardinalNatural.Peano.subtract da.val db.val h_le + db.val) *
                            CardinalNatural.Peano.tenPow das.length +
                          (toCardinalList digits CardinalNatural.Peano.zero +
                            toCardinalList dbs CardinalNatural.Peano.zero) := by
                            rw [CardinalNatural.Peano.multiply_distributive_over_add_left]
                            exact CardinalNatural.Peano.add_pair_swap _ _ _ _
                      _ = da.val * CardinalNatural.Peano.tenPow das.length +
                          toCardinalList das CardinalNatural.Peano.zero := by
                            rw [h_digit, ih_value]
                      _ = da.val * CardinalNatural.Peano.tenPow das.length +
                          toCardinalList das CardinalNatural.Peano.zero + CardinalNatural.Peano.zero := by
                            rw [CardinalNatural.Peano.add_zero]
          | true =>
              simp at ih_value ⊢
              split
              · next h_da_lt_db_succ =>
                  constructor
                  · simp [Sequences.List.length, h_length]
                  · simp only [toCardinalList_firstElement, Sequences.List.length,
                      CardinalNatural.Peano.tenPow_add_one, if_true]
                    rw [h_length, ← h_tail_lengths]
                    have h_le : db.val.successor ≤ da.val + CardinalNatural.Peano.ten := by
                      exact CardinalNatural.Peano.le_trans (digit_val_successor_le_ten db)
                        (CardinalNatural.Peano.le_add_self_right da.val CardinalNatural.Peano.ten)
                    have h_digit := CardinalNatural.Peano.subtract_add_cancel
                      (da.val + CardinalNatural.Peano.ten) db.val.successor h_le
                    calc
                      _ = (CardinalNatural.Peano.subtract (da.val + CardinalNatural.Peano.ten) db.val.successor h_le + db.val) *
                            CardinalNatural.Peano.tenPow das.length +
                          (toCardinalList digits CardinalNatural.Peano.zero +
                            toCardinalList dbs CardinalNatural.Peano.zero) := by
                            rw [CardinalNatural.Peano.multiply_distributive_over_add_left]
                            exact CardinalNatural.Peano.add_pair_swap _ _ _ _
                      _ = (CardinalNatural.Peano.subtract (da.val + CardinalNatural.Peano.ten) db.val.successor h_le + db.val) *
                            CardinalNatural.Peano.tenPow das.length +
                          (toCardinalList das CardinalNatural.Peano.zero +
                            CardinalNatural.Peano.tenPow das.length) := by
                            rw [ih_value]
                      _ = (CardinalNatural.Peano.subtract (da.val + CardinalNatural.Peano.ten) db.val.successor h_le + db.val).successor *
                            CardinalNatural.Peano.tenPow das.length +
                          toCardinalList das CardinalNatural.Peano.zero := by
                            rw [CardinalNatural.Peano.successor_multiply]
                            rw [CardinalNatural.Peano.add_commutative (toCardinalList das CardinalNatural.Peano.zero)
                              (CardinalNatural.Peano.tenPow das.length)]
                            rw [← CardinalNatural.Peano.add_associative]
                      _ = (da.val + CardinalNatural.Peano.ten) * CardinalNatural.Peano.tenPow das.length +
                          toCardinalList das CardinalNatural.Peano.zero := by
                            rw [← CardinalNatural.Peano.add_successor]
                            rw [h_digit]
                      _ = da.val * CardinalNatural.Peano.tenPow das.length +
                          toCardinalList das CardinalNatural.Peano.zero +
                            CardinalNatural.Peano.ten * CardinalNatural.Peano.tenPow das.length := by
                            rw [CardinalNatural.Peano.multiply_distributive_over_add_left]
                            exact CardinalNatural.Peano.add_right_commutative _ _ _
              · next h_not_lt =>
                  constructor
                  · simp [Sequences.List.length, h_length]
                  · simp only [toCardinalList_firstElement, Sequences.List.length]
                    simp only [if_neg Bool.false_ne_true]
                    rw [h_length, ← h_tail_lengths]
                    have h_le : db.val.successor ≤ da.val := CardinalNatural.Peano.not_lt_implies_le h_not_lt
                    have h_digit := CardinalNatural.Peano.subtract_add_cancel da.val db.val.successor h_le
                    calc
                      _ = (CardinalNatural.Peano.subtract da.val db.val.successor h_le + db.val) *
                            CardinalNatural.Peano.tenPow das.length +
                          (toCardinalList digits CardinalNatural.Peano.zero +
                            toCardinalList dbs CardinalNatural.Peano.zero) := by
                            rw [CardinalNatural.Peano.multiply_distributive_over_add_left]
                            exact CardinalNatural.Peano.add_pair_swap _ _ _ _
                      _ = (CardinalNatural.Peano.subtract da.val db.val.successor h_le + db.val) *
                            CardinalNatural.Peano.tenPow das.length +
                          (toCardinalList das CardinalNatural.Peano.zero +
                            CardinalNatural.Peano.tenPow das.length) := by
                            rw [ih_value]
                      _ = (CardinalNatural.Peano.subtract da.val db.val.successor h_le + db.val).successor *
                            CardinalNatural.Peano.tenPow das.length +
                          toCardinalList das CardinalNatural.Peano.zero := by
                            rw [CardinalNatural.Peano.successor_multiply]
                            exact CardinalNatural.Peano.add_right_swap _ _ _
                      _ = da.val * CardinalNatural.Peano.tenPow das.length +
                          toCardinalList das CardinalNatural.Peano.zero := by
                            rw [← CardinalNatural.Peano.add_successor]
                            rw [h_digit]
                      _ = da.val * CardinalNatural.Peano.tenPow das.length +
                          toCardinalList das CardinalNatural.Peano.zero + CardinalNatural.Peano.zero := by
                            rw [CardinalNatural.Peano.add_zero]

theorem toCardinalPeano_add (x y : Decimal) :
  toCardinalPeano (x + y) = toCardinalPeano x + toCardinalPeano y := by
  change toCardinalList (add x y).val CardinalNatural.Peano.zero =
    toCardinalList x.val CardinalNatural.Peano.zero +
      toCardinalList y.val CardinalNatural.Peano.zero
  unfold add
  dsimp only
  split
  · next digits h_add =>
      have h_spec := addAlignedLists_spec
        (Sequences.List.padAtStartToSameLength_sameLength x.val y.val zeroDigit)
      rw [h_add] at h_spec
      dsimp only at h_spec
      obtain ⟨h_length, h_value⟩ := h_spec
      simp at h_value
      change toCardinalList
        (Sequences.List.firstElement ⟨CardinalNatural.Peano.one, CardinalNatural.Peano.one_lt_ten⟩ digits)
        CardinalNatural.Peano.zero = _
      rw [toCardinalList_firstElement, h_length, CardinalNatural.Peano.one_multiply,
        CardinalNatural.Peano.add_commutative, h_value,
        toCardinalList_padAtStartToSameLength_fst,
        toCardinalList_padAtStartToSameLength_snd]
  · next digits h_add =>
      have h_spec := addAlignedLists_spec
        (Sequences.List.padAtStartToSameLength_sameLength x.val y.val zeroDigit)
      rw [h_add] at h_spec
      dsimp only at h_spec
      obtain ⟨_, h_value⟩ := h_spec
      simp at h_value
      rw [h_value, toCardinalList_padAtStartToSameLength_fst,
        toCardinalList_padAtStartToSameLength_snd]


theorem toCardinalPeano_subtract (x y : Decimal) (h : y < x) :
  toCardinalPeano (subtract x y h) + toCardinalPeano y = toCardinalPeano x := by
  change toCardinalList (subtract x y h).val CardinalNatural.Peano.zero +
      toCardinalList y.val CardinalNatural.Peano.zero =
    toCardinalList x.val CardinalNatural.Peano.zero
  unfold subtract
  dsimp only
  let pair := Sequences.List.padAtStartToSameLength x.val y.val zeroDigit
  let h_same : Sequences.List.SameLength pair.1 pair.2 :=
    Sequences.List.padAtStartToSameLength_sameLength x.val y.val zeroDigit
  by_cases h_borrow : (subtractAlignedLists pair.1 pair.2 h_same).2 = true
  · simp [pair, h_borrow]
    have h_borrow_false := subtractAlignedLists_borrow_false_of_lessThan
      h_same (lessThanAlignedLists_padded_of_lt h)
    exact False.elim (by
      rw [h_borrow] at h_borrow_false
      cases h_borrow_false)
  · simp [pair, h_borrow]
    cases h_subtract : subtractAlignedLists pair.1 pair.2 h_same with
    | mk digits borrow =>
        have h_spec := subtractAlignedLists_spec h_same
        rw [h_subtract] at h_spec
        dsimp only at h_spec
        obtain ⟨_, h_value⟩ := h_spec
        cases borrow with
        | false =>
            simp at h_value
            rw [← toCardinalList_padAtStartToSameLength_fst x.val y.val,
              ← toCardinalList_padAtStartToSameLength_snd x.val y.val]
            change toCardinalList digits CardinalNatural.Peano.zero +
                toCardinalList pair.2 CardinalNatural.Peano.zero =
              toCardinalList pair.1 CardinalNatural.Peano.zero
            exact h_value
        | true =>
            rw [h_subtract] at h_borrow
            exact False.elim (h_borrow rfl)

theorem add_toPeano (x y : Decimal) :
  (x + y).toPeano = x.toPeano + y.toPeano := by
  apply peano_eq_of_fromOrdinal_eq
  rw [fromOrdinal_add]
  simp only [toPeano, CardinalNatural.Peano.fromOrdinal_toOrdinal]
  exact toCardinalPeano_add x y

-- toCardinalList l 0 < 10^len(l)
theorem toCardinalList_lt_tenPow (l : Sequences.List Digit) :
    toCardinalList l CardinalNatural.Peano.zero < CardinalNatural.Peano.tenPow l.length := by
  induction l with
  | empty =>
    simp only [toCardinalList, Sequences.List.length, CardinalNatural.Peano.tenPow]
    exact CardinalNatural.Peano.LessThan.base
  | firstElement d ds ih =>
    simp only [toCardinalList, Sequences.List.length,
               CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.zero_add]
    rw [toCardinalList_acc_split ds d.val, CardinalNatural.Peano.tenPow_add_one]
    have h1 : d.val * CardinalNatural.Peano.tenPow ds.length + toCardinalList ds CardinalNatural.Peano.zero <
              d.val * CardinalNatural.Peano.tenPow ds.length + CardinalNatural.Peano.tenPow ds.length :=
      CardinalNatural.Peano.add_lt_add_left ih (d.val * CardinalNatural.Peano.tenPow ds.length)
    have h2 : d.val * CardinalNatural.Peano.tenPow ds.length + CardinalNatural.Peano.tenPow ds.length = d.val.successor * CardinalNatural.Peano.tenPow ds.length :=
      (CardinalNatural.Peano.successor_multiply d.val (CardinalNatural.Peano.tenPow ds.length)).symm
    have h3 : d.val.successor * CardinalNatural.Peano.tenPow ds.length ≤ CardinalNatural.Peano.ten * CardinalNatural.Peano.tenPow ds.length :=
      CardinalNatural.Peano.multiply_le_mul_left (CardinalNatural.Peano.succ_le_of_lt d.property) (CardinalNatural.Peano.tenPow ds.length)
    rw [h2] at h1
    cases h3 with
    | inl hlt => exact CardinalNatural.Peano.lt_trans h1 hlt
    | inr heq => rw [← heq]; exact h1

theorem LessThanAlignedLists_toCardinalList_lt {x y : Sequences.List Digit}
    (h : Sequences.List.SameLength x y)
    (hlt : LessThanAlignedLists x y h) :
    toCardinalList x CardinalNatural.Peano.zero <
      toCardinalList y CardinalNatural.Peano.zero := by
  induction h with
  | empty =>
      cases hlt
  | firstElement htail ih =>
      rename_i dx dy dxs dys
      simp only [toCardinalList_firstElement]
      cases hlt with
      | inl h_digit =>
          have h_tail_lt : toCardinalList dxs CardinalNatural.Peano.zero <
              CardinalNatural.Peano.tenPow dxs.length :=
            toCardinalList_lt_tenPow dxs
          have h_lt_next :
              dx.val * CardinalNatural.Peano.tenPow dxs.length +
                toCardinalList dxs CardinalNatural.Peano.zero <
              dx.val * CardinalNatural.Peano.tenPow dxs.length +
                CardinalNatural.Peano.tenPow dxs.length :=
            CardinalNatural.Peano.add_lt_add_left h_tail_lt _
          have h_next_eq :
              dx.val * CardinalNatural.Peano.tenPow dxs.length +
                CardinalNatural.Peano.tenPow dxs.length =
              dx.val.successor * CardinalNatural.Peano.tenPow dxs.length :=
            (CardinalNatural.Peano.successor_multiply dx.val _).symm
          rw [h_next_eq] at h_lt_next
          have h_le_digit :
              dx.val.successor * CardinalNatural.Peano.tenPow dxs.length ≤
                dy.val * CardinalNatural.Peano.tenPow dxs.length :=
            CardinalNatural.Peano.multiply_le_mul_left
              (CardinalNatural.Peano.succ_le_of_lt h_digit) _
          have h_le_value :
              dy.val * CardinalNatural.Peano.tenPow dxs.length ≤
                dy.val * CardinalNatural.Peano.tenPow dxs.length +
                  toCardinalList dys CardinalNatural.Peano.zero :=
            CardinalNatural.Peano.le_add_self_left _ _
          rw [← Sequences.List.sameLength_length_eq htail]
          exact CardinalNatural.Peano.lt_of_lt_of_le h_lt_next
            (CardinalNatural.Peano.le_trans h_le_digit h_le_value)
      | inr h_eq_tail =>
          obtain ⟨h_digit_eq, h_tail_lt_aligned⟩ := h_eq_tail
          rw [h_digit_eq, Sequences.List.sameLength_length_eq htail]
          exact CardinalNatural.Peano.add_lt_add_left
            (ih h_tail_lt_aligned) _

theorem LessThanAlignedLists_of_toCardinalList_lt {x y : Sequences.List Digit}
    (h : Sequences.List.SameLength x y)
    (hlt : toCardinalList x CardinalNatural.Peano.zero <
      toCardinalList y CardinalNatural.Peano.zero) :
    LessThanAlignedLists x y h := by
  induction h with
  | empty =>
      exact False.elim (CardinalNatural.Peano.not_lt_self _ hlt)
  | firstElement htail ih =>
      rename_i dx dy dxs dys
      simp only [toCardinalList_firstElement] at hlt
      rw [Sequences.List.sameLength_length_eq htail] at hlt
      cases CardinalNatural.Peano.trichotomy_or dx.val dy.val with
      | inl h_digit_lt =>
          exact Or.inl h_digit_lt
      | inr h_eq_or_gt =>
          cases h_eq_or_gt with
          | inl h_digit_eq =>
              apply Or.inr
              constructor
              · exact h_digit_eq
              · apply ih
                have hlt_tail_sum :
                    dy.val * CardinalNatural.Peano.tenPow dys.length +
                      toCardinalList dxs CardinalNatural.Peano.zero <
                    dy.val * CardinalNatural.Peano.tenPow dys.length +
                      toCardinalList dys CardinalNatural.Peano.zero := by
                  rwa [h_digit_eq] at hlt
                rw [CardinalNatural.Peano.add_commutative
                      (dy.val * CardinalNatural.Peano.tenPow dys.length),
                    CardinalNatural.Peano.add_commutative
                      (dy.val * CardinalNatural.Peano.tenPow dys.length)] at hlt_tail_sum
                exact CardinalNatural.Peano.add_lt_cancel_right hlt_tail_sum
          | inr h_digit_gt =>
              have h_tail_y_lt : toCardinalList dys CardinalNatural.Peano.zero <
                  CardinalNatural.Peano.tenPow dys.length :=
                toCardinalList_lt_tenPow dys
              have h_y_lt_next :
                  dy.val * CardinalNatural.Peano.tenPow dys.length +
                    toCardinalList dys CardinalNatural.Peano.zero <
                  dy.val * CardinalNatural.Peano.tenPow dys.length +
                    CardinalNatural.Peano.tenPow dys.length :=
                CardinalNatural.Peano.add_lt_add_left h_tail_y_lt _
              have h_next_eq :
                  dy.val * CardinalNatural.Peano.tenPow dys.length +
                    CardinalNatural.Peano.tenPow dys.length =
                  dy.val.successor * CardinalNatural.Peano.tenPow dys.length :=
                (CardinalNatural.Peano.successor_multiply dy.val _).symm
              rw [h_next_eq] at h_y_lt_next
              have h_le_digit :
                  dy.val.successor * CardinalNatural.Peano.tenPow dys.length ≤
                    dx.val * CardinalNatural.Peano.tenPow dys.length :=
                CardinalNatural.Peano.multiply_le_mul_left
                  (CardinalNatural.Peano.succ_le_of_lt h_digit_gt) _
              have h_le_x :
                  dx.val * CardinalNatural.Peano.tenPow dys.length ≤
                    dx.val * CardinalNatural.Peano.tenPow dys.length +
                      toCardinalList dxs CardinalNatural.Peano.zero :=
                CardinalNatural.Peano.le_add_self_left _ _
              have h_y_lt_x :
                  dy.val * CardinalNatural.Peano.tenPow dys.length +
                    toCardinalList dys CardinalNatural.Peano.zero <
                  dx.val * CardinalNatural.Peano.tenPow dys.length +
                    toCardinalList dxs CardinalNatural.Peano.zero :=
                CardinalNatural.Peano.lt_of_lt_of_le h_y_lt_next
                  (CardinalNatural.Peano.le_trans h_le_digit h_le_x)
              exact False.elim (CardinalNatural.Peano.not_lt_self _
                (CardinalNatural.Peano.lt_trans hlt h_y_lt_x))

theorem toCardinalPeano_lt_of_lt {a b : Decimal} (h : a < b) :
    toCardinalPeano a < toCardinalPeano b := by
  change LessThan a b at h
  unfold LessThan at h
  dsimp only at h
  have h_padded := LessThanAlignedLists_toCardinalList_lt
    (Sequences.List.padAtStartToSameLength_sameLength a.val b.val zeroDigit) h
  change toCardinalList a.val CardinalNatural.Peano.zero <
    toCardinalList b.val CardinalNatural.Peano.zero
  rw [← toCardinalList_padAtStartToSameLength_fst a.val b.val,
    ← toCardinalList_padAtStartToSameLength_snd a.val b.val]
  exact h_padded


theorem toPeano_lt_of_lt {a b : Decimal} (h : a < b) : a.toPeano < b.toPeano := by
  unfold toPeano
  exact CardinalNatural.Peano.toOrdinal_lt_of_lt _ _ (toCardinalPeano_lt_of_lt h)

theorem lt_of_toCardinalPeano_lt {a b : Decimal}
    (h : toCardinalPeano a < toCardinalPeano b) : a < b := by
  change LessThan a b
  unfold LessThan
  dsimp only
  apply LessThanAlignedLists_of_toCardinalList_lt
  change toCardinalList (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).1
      CardinalNatural.Peano.zero <
    toCardinalList (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).2
      CardinalNatural.Peano.zero
  rw [toCardinalList_padAtStartToSameLength_fst a.val b.val,
    toCardinalList_padAtStartToSameLength_snd a.val b.val]
  exact h

theorem toCardinalPeano_eq_of_equivalent {a b : Decimal} (h : a ≈ b) :
    toCardinalPeano a = toCardinalPeano b := by
  have ha : toCardinalPeano a.normalize = toCardinalPeano a := by
    unfold toCardinalPeano normalize
    exact normalizeList_toCardinalPeano a.val a.property
  have hb : toCardinalPeano b.normalize = toCardinalPeano b := by
    unfold toCardinalPeano normalize
    exact normalizeList_toCardinalPeano b.val b.property
  rw [← ha, ← hb, h]

theorem lt_trans {a b c : Decimal} (h1 : a < b) (h2 : b < c) : a < c := by
  exact lt_of_toCardinalPeano_lt
    (CardinalNatural.Peano.lt_trans (toCardinalPeano_lt_of_lt h1)
      (toCardinalPeano_lt_of_lt h2))

theorem le_trans {a b c : Decimal} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  cases h1 with
  | inl hlt1 =>
      cases h2 with
      | inl hlt2 => exact Or.inl (lt_trans hlt1 hlt2)
      | inr heq2 =>
          apply Or.inl
          apply lt_of_toCardinalPeano_lt
          rw [← toCardinalPeano_eq_of_equivalent heq2]
          exact toCardinalPeano_lt_of_lt hlt1
  | inr heq1 =>
      cases h2 with
      | inl hlt2 =>
          apply Or.inl
          apply lt_of_toCardinalPeano_lt
          rw [toCardinalPeano_eq_of_equivalent heq1]
          exact toCardinalPeano_lt_of_lt hlt2
      | inr heq2 =>
          exact Or.inr (Setoid.trans heq1 heq2)

-- Key injectivity lemma: same-length lists with same toCardinalList value are equal
theorem toCardinalList_inj_sameLength {l1 l2 : Sequences.List Digit}
    (hsl : Sequences.List.SameLength l1 l2)
    (heq : toCardinalList l1 CardinalNatural.Peano.zero =
           toCardinalList l2 CardinalNatural.Peano.zero) :
    l1 = l2 := by
  induction hsl with
  | empty => rfl
  | firstElement h_tail ih =>
    rename_i d1 d2 ds1 ds2
    simp only [toCardinalList,
               CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.zero_add] at heq
    rw [toCardinalList_acc_split ds1 d1.val,
        toCardinalList_acc_split ds2 d2.val] at heq
    have h_len : ds2.length = ds1.length := (Sequences.List.sameLength_length_eq h_tail).symm
    rw [h_len] at heq
    have hv1_lt : toCardinalList ds1 CardinalNatural.Peano.zero < CardinalNatural.Peano.tenPow ds1.length :=
      toCardinalList_lt_tenPow ds1
    have hv2_lt : toCardinalList ds2 CardinalNatural.Peano.zero < CardinalNatural.Peano.tenPow ds1.length := by
      rw [← h_len]; exact toCardinalList_lt_tenPow ds2
    have hd_eq : d1.val = d2.val := by
      cases CardinalNatural.Peano.trichotomy_or d1.val d2.val with
      | inl hlt =>
        exfalso
        have hchain : d1.val * CardinalNatural.Peano.tenPow ds1.length + CardinalNatural.Peano.tenPow ds1.length ≤
                      d1.val * CardinalNatural.Peano.tenPow ds1.length + toCardinalList ds1 CardinalNatural.Peano.zero := by
          have hstep1 : d1.val * CardinalNatural.Peano.tenPow ds1.length + CardinalNatural.Peano.tenPow ds1.length =
                        d1.val.successor * CardinalNatural.Peano.tenPow ds1.length :=
            (CardinalNatural.Peano.successor_multiply d1.val (CardinalNatural.Peano.tenPow ds1.length)).symm
          have hstep2 : d1.val.successor * CardinalNatural.Peano.tenPow ds1.length ≤ d2.val * CardinalNatural.Peano.tenPow ds1.length :=
            CardinalNatural.Peano.multiply_le_mul_left (CardinalNatural.Peano.succ_le_of_lt hlt) (CardinalNatural.Peano.tenPow ds1.length)
          have hstep3 : d2.val * CardinalNatural.Peano.tenPow ds1.length ≤
                        d2.val * CardinalNatural.Peano.tenPow ds1.length + toCardinalList ds2 CardinalNatural.Peano.zero :=
            CardinalNatural.Peano.le_add_self_left _ _
          rw [hstep1]
          exact CardinalNatural.Peano.le_trans (CardinalNatural.Peano.le_trans hstep2 hstep3)
            (Or.inr heq.symm)
        exact absurd (CardinalNatural.Peano.le_lt_trans (CardinalNatural.Peano.add_le_cancel_left hchain) hv1_lt)
          (CardinalNatural.Peano.not_lt_self (CardinalNatural.Peano.tenPow ds1.length))
      | inr h =>
        cases h with
        | inl heq_d => exact heq_d
        | inr hgt =>
          exfalso
          have hchain : d2.val * CardinalNatural.Peano.tenPow ds1.length + CardinalNatural.Peano.tenPow ds1.length ≤
                        d2.val * CardinalNatural.Peano.tenPow ds1.length + toCardinalList ds2 CardinalNatural.Peano.zero := by
            have hstep1 : d2.val * CardinalNatural.Peano.tenPow ds1.length + CardinalNatural.Peano.tenPow ds1.length =
                          d2.val.successor * CardinalNatural.Peano.tenPow ds1.length :=
              (CardinalNatural.Peano.successor_multiply d2.val (CardinalNatural.Peano.tenPow ds1.length)).symm
            have hstep2 : d2.val.successor * CardinalNatural.Peano.tenPow ds1.length ≤ d1.val * CardinalNatural.Peano.tenPow ds1.length :=
              CardinalNatural.Peano.multiply_le_mul_left (CardinalNatural.Peano.succ_le_of_lt hgt) (CardinalNatural.Peano.tenPow ds1.length)
            have hstep3 : d1.val * CardinalNatural.Peano.tenPow ds1.length ≤
                          d1.val * CardinalNatural.Peano.tenPow ds1.length + toCardinalList ds1 CardinalNatural.Peano.zero :=
              CardinalNatural.Peano.le_add_self_left _ _
            rw [hstep1]
            exact CardinalNatural.Peano.le_trans (CardinalNatural.Peano.le_trans hstep2 hstep3)
              (Or.inr heq)
          exact absurd (CardinalNatural.Peano.le_lt_trans (CardinalNatural.Peano.add_le_cancel_left hchain) hv2_lt)
            (CardinalNatural.Peano.not_lt_self (CardinalNatural.Peano.tenPow ds1.length))
    have hv_eq : toCardinalList ds1 CardinalNatural.Peano.zero =
                 toCardinalList ds2 CardinalNatural.Peano.zero := by
      have heq' := heq
      rw [hd_eq] at heq'
      exact CardinalNatural.Peano.add_left_cancel _ _ _ heq'
    rw [Subtype.ext hd_eq, ih hv_eq]

-- Normalized Decimals with same toCardinalPeano are equal
theorem normalize_inj {a b : Decimal}
    (ha : a.isNormalized = true) (hb : b.isNormalized = true)
    (heq : toCardinalPeano a = toCardinalPeano b) : a = b := by
  obtain ⟨val_a, prop_a⟩ := a
  obtain ⟨val_b, prop_b⟩ := b
  cases val_a with
  | empty => exact absurd rfl (hasNonZero_ne_empty prop_a)
  | firstElement da das =>
    cases val_b with
    | empty => exact absurd rfl (hasNonZero_ne_empty prop_b)
    | firstElement db dbs =>
      simp only [isNormalized] at ha hb
      simp only [toCardinalPeano, toCardinalList,
                 CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.zero_add] at heq
      have heq_raw : toCardinalList das da.val = toCardinalList dbs db.val := heq
      rw [toCardinalList_acc_split das da.val, toCardinalList_acc_split dbs db.val] at heq
      have hda_ne : da.val ≠ CardinalNatural.Peano.zero := by simp at ha; exact ha
      have hdb_ne : db.val ≠ CardinalNatural.Peano.zero := by simp at hb; exact hb
      have h_len : das.length = dbs.length := by
        cases CardinalNatural.Peano.trichotomy_or das.length dbs.length with
        | inl hlt =>
          have hval_lt : da.val * CardinalNatural.Peano.tenPow das.length + toCardinalList das CardinalNatural.Peano.zero <
              CardinalNatural.Peano.ten * CardinalNatural.Peano.tenPow das.length := by
            have hstep1 : da.val * CardinalNatural.Peano.tenPow das.length + toCardinalList das CardinalNatural.Peano.zero <
                          da.val * CardinalNatural.Peano.tenPow das.length + CardinalNatural.Peano.tenPow das.length :=
              CardinalNatural.Peano.add_lt_add_left (toCardinalList_lt_tenPow das) _
            have hstep2 : da.val * CardinalNatural.Peano.tenPow das.length + CardinalNatural.Peano.tenPow das.length =
                          da.val.successor * CardinalNatural.Peano.tenPow das.length :=
              (CardinalNatural.Peano.successor_multiply da.val _).symm
            have hstep3 : da.val.successor * CardinalNatural.Peano.tenPow das.length ≤
                          CardinalNatural.Peano.ten * CardinalNatural.Peano.tenPow das.length :=
              CardinalNatural.Peano.multiply_le_mul_left (CardinalNatural.Peano.succ_le_of_lt da.property) _
            rw [hstep2] at hstep1
            cases hstep3 with
            | inl hlt3 => exact CardinalNatural.Peano.lt_trans hstep1 hlt3
            | inr heq3 => rw [← heq3]; exact hstep1
          have htenPow_le : CardinalNatural.Peano.tenPow das.length.successor ≤ CardinalNatural.Peano.tenPow dbs.length :=
            CardinalNatural.Peano.tenPow_monotone (CardinalNatural.Peano.succ_le_of_lt hlt)
          have hval_ge : CardinalNatural.Peano.tenPow dbs.length ≤
              db.val * CardinalNatural.Peano.tenPow dbs.length + toCardinalList dbs CardinalNatural.Peano.zero := by
            have hdb_pos : CardinalNatural.Peano.one ≤ db.val := by
              cases h_db : db.val with
              | zero => exact absurd h_db hdb_ne
              | successor v => exact CardinalNatural.Peano.succ_le_of_lt (CardinalNatural.Peano.zero_lt_succ v)
            have hge1 : CardinalNatural.Peano.one * CardinalNatural.Peano.tenPow dbs.length ≤
                        db.val * CardinalNatural.Peano.tenPow dbs.length :=
              CardinalNatural.Peano.multiply_le_mul_left hdb_pos (CardinalNatural.Peano.tenPow dbs.length)
            rw [CardinalNatural.Peano.one_multiply] at hge1
            exact CardinalNatural.Peano.le_trans hge1 (CardinalNatural.Peano.le_add_self_left _ _)
          exact absurd
            (CardinalNatural.Peano.le_lt_trans
              (CardinalNatural.Peano.le_trans htenPow_le
                (CardinalNatural.Peano.le_trans hval_ge (Or.inr heq.symm)))
              hval_lt)
            (CardinalNatural.Peano.not_lt_self _)
        | inr h =>
          cases h with
          | inl heq_l => exact heq_l
          | inr hgt =>
            have hval_lt : db.val * CardinalNatural.Peano.tenPow dbs.length + toCardinalList dbs CardinalNatural.Peano.zero <
                CardinalNatural.Peano.ten * CardinalNatural.Peano.tenPow dbs.length := by
              have hstep1 : db.val * CardinalNatural.Peano.tenPow dbs.length + toCardinalList dbs CardinalNatural.Peano.zero <
                            db.val * CardinalNatural.Peano.tenPow dbs.length + CardinalNatural.Peano.tenPow dbs.length :=
                CardinalNatural.Peano.add_lt_add_left (toCardinalList_lt_tenPow dbs) _
              have hstep2 : db.val * CardinalNatural.Peano.tenPow dbs.length + CardinalNatural.Peano.tenPow dbs.length =
                            db.val.successor * CardinalNatural.Peano.tenPow dbs.length :=
                (CardinalNatural.Peano.successor_multiply db.val _).symm
              have hstep3 : db.val.successor * CardinalNatural.Peano.tenPow dbs.length ≤
                            CardinalNatural.Peano.ten * CardinalNatural.Peano.tenPow dbs.length :=
                CardinalNatural.Peano.multiply_le_mul_left (CardinalNatural.Peano.succ_le_of_lt db.property) _
              rw [hstep2] at hstep1
              cases hstep3 with
              | inl hlt3 => exact CardinalNatural.Peano.lt_trans hstep1 hlt3
              | inr heq3 => rw [← heq3]; exact hstep1
            have htenPow_le : CardinalNatural.Peano.tenPow dbs.length.successor ≤ CardinalNatural.Peano.tenPow das.length :=
              CardinalNatural.Peano.tenPow_monotone (CardinalNatural.Peano.succ_le_of_lt hgt)
            have hval_ge : CardinalNatural.Peano.tenPow das.length ≤
                da.val * CardinalNatural.Peano.tenPow das.length + toCardinalList das CardinalNatural.Peano.zero := by
              have hda_pos : CardinalNatural.Peano.one ≤ da.val := by
                cases h_da : da.val with
                | zero => exact absurd h_da hda_ne
                | successor v => exact CardinalNatural.Peano.succ_le_of_lt (CardinalNatural.Peano.zero_lt_succ v)
              have hge1 : CardinalNatural.Peano.one * CardinalNatural.Peano.tenPow das.length ≤
                          da.val * CardinalNatural.Peano.tenPow das.length :=
                CardinalNatural.Peano.multiply_le_mul_left hda_pos (CardinalNatural.Peano.tenPow das.length)
              rw [CardinalNatural.Peano.one_multiply] at hge1
              exact CardinalNatural.Peano.le_trans hge1 (CardinalNatural.Peano.le_add_self_left _ _)
            exact absurd
              (CardinalNatural.Peano.le_lt_trans
                (CardinalNatural.Peano.le_trans htenPow_le
                  (CardinalNatural.Peano.le_trans hval_ge (Or.inr heq)))
                hval_lt)
              (CardinalNatural.Peano.not_lt_self _)
      have hsl : Sequences.List.SameLength
          (Sequences.List.firstElement da das) (Sequences.List.firstElement db dbs) :=
        Sequences.List.sameLength_of_length_eq (by simp [Sequences.List.length, h_len])
      have hlist_eq : Sequences.List.firstElement da das = Sequences.List.firstElement db dbs :=
        toCardinalList_inj_sameLength hsl (by
          simp only [toCardinalList,
                     CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.zero_add]
          exact heq_raw)
      exact Subtype.ext hlist_eq

-- normalize produces a normalized Decimal
theorem normalize_isNormalized (d : Decimal) : d.normalize.isNormalized = true := by
  obtain ⟨l, h⟩ := d
  show (normalizeList l h).isNormalized = true
  induction l with
  | empty => exact False.elim (hasNonZero_ne_empty h rfl)
  | firstElement digit rest ih =>
    unfold normalizeList
    by_cases hd : digit.val = CardinalNatural.Peano.zero
    · rw [dif_pos hd]
      exact ih (hasNonZero_tail_of_zero_first h hd)
    · rw [dif_neg hd]
      simp only [isNormalized]
      exact decide_eq_true hd

theorem equivalent_of_toPeano_eq {a b : Decimal} (h : a.toPeano = b.toPeano) : a ≈ b := by
  have h_card : toCardinalPeano a = toCardinalPeano b := by
    have := congrArg CardinalNatural.Peano.fromOrdinal h
    simp only [toPeano] at this
    rwa [CardinalNatural.Peano.fromOrdinal_toOrdinal,
         CardinalNatural.Peano.fromOrdinal_toOrdinal] at this
  show a.normalize = b.normalize
  have ha_norm : toCardinalPeano a.normalize = toCardinalPeano a := by
    unfold toCardinalPeano normalize
    exact normalizeList_toCardinalPeano a.val a.property
  have hb_norm : toCardinalPeano b.normalize = toCardinalPeano b := by
    unfold toCardinalPeano normalize
    exact normalizeList_toCardinalPeano b.val b.property
  have h_norm_card : toCardinalPeano a.normalize = toCardinalPeano b.normalize := by
    rw [ha_norm, hb_norm, h_card]
  exact normalize_inj (normalize_isNormalized a) (normalize_isNormalized b) h_norm_card

theorem predecessor_successor (x : Decimal) :
  ∃ h, predecessor x.successor h ≈ x := by
  have h : ¬ x.successor ≈ one := successor_ne_one x
  refine ⟨h, ?_⟩
  apply equivalent_of_toPeano_eq
  obtain ⟨h2, h_predecessor_toPeano⟩ := predecessor_toPeano x.successor h
  have h_successor_toPeano : x.successor.toPeano = x.toPeano.successor := successor_toPeano x
  have h2' : x.toPeano.successor ≠ OrdinalNatural.Peano.one := by
    intro h_one
    exact h2 (h_successor_toPeano.trans h_one)
  have h_predecessor_toPeano' :
      (predecessor x.successor h).toPeano = (x.toPeano.successor).predecessor h2' := by
    exact h_predecessor_toPeano.trans (peano_predecessor_congr h2 h2' h_successor_toPeano)
  obtain ⟨h3, h_predecessor_successor⟩ := OrdinalNatural.Peano.pred_succ_eq x.toPeano
  have h_predecessor_congr :
      (x.toPeano.successor).predecessor h2' = (x.toPeano.successor).predecessor h3 :=
    peano_predecessor_congr h2' h3 rfl
  exact h_predecessor_toPeano'.trans (h_predecessor_congr.trans h_predecessor_successor)

theorem equivalent_of_toCardinalPeano_eq {a b : Decimal}
    (h : toCardinalPeano a = toCardinalPeano b) : a ≈ b := by
  show a.normalize = b.normalize
  have ha_norm : toCardinalPeano a.normalize = toCardinalPeano a := by
    unfold toCardinalPeano normalize
    exact normalizeList_toCardinalPeano a.val a.property
  have hb_norm : toCardinalPeano b.normalize = toCardinalPeano b := by
    unfold toCardinalPeano normalize
    exact normalizeList_toCardinalPeano b.val b.property
  have h_norm_card : toCardinalPeano a.normalize = toCardinalPeano b.normalize := by
    rw [ha_norm, hb_norm, h]
  exact normalize_inj (normalize_isNormalized a) (normalize_isNormalized b) h_norm_card

theorem add_associative (a b c : Decimal) : a + b + c ≈ a + (b + c) := by
  apply equivalent_of_toCardinalPeano_eq
  rw [toCardinalPeano_add, toCardinalPeano_add, toCardinalPeano_add,
    toCardinalPeano_add, CardinalNatural.Peano.add_associative]

theorem lt_add_right (a b : Decimal) : b < a + b := by
  apply lt_of_toCardinalPeano_lt
  rw [toCardinalPeano_add, CardinalNatural.Peano.add_commutative
    (toCardinalPeano a) (toCardinalPeano b)]
  exact CardinalNatural.Peano.lt_add_of_right_ne_zero
    (toCardinalPeano b) (toCardinalPeano a) (toCardinalPeano_ne_zero a)

theorem subtract_add_cancel (a b : Decimal) (h : b < a) :
  subtract a b h + b ≈ a := by
  apply equivalent_of_toCardinalPeano_eq
  rw [toCardinalPeano_add, toCardinalPeano_subtract a b h]

theorem add_subtract_cancel (a b : Decimal) :
  ∃ h, subtract (a + b) b h ≈ a := by
  let h : b < a + b := lt_add_right a b
  refine ⟨h, ?_⟩
  apply equivalent_of_toCardinalPeano_eq
  apply CardinalNatural.Peano.add_cancel_right
    (toCardinalPeano (subtract (a + b) b h)) (toCardinalPeano a) (toCardinalPeano b)
  rw [toCardinalPeano_subtract (a + b) b h, toCardinalPeano_add]

theorem trichotomy (a b : Decimal) :
    ZeroMath.Logic.Trichotomy (a < b) (a ≈ b) (b < a) := by
  cases CardinalNatural.Peano.trichotomy (toCardinalPeano a) (toCardinalPeano b) with
  | first hlt hne hnlt_reverse =>
      exact ZeroMath.Logic.Trichotomy.first
        (lt_of_toCardinalPeano_lt hlt)
        (fun heq => hne (toCardinalPeano_eq_of_equivalent heq))
        (fun h_reverse => hnlt_reverse (toCardinalPeano_lt_of_lt h_reverse))
  | second heq hnlt_forward hnlt_reverse =>
      exact ZeroMath.Logic.Trichotomy.second
        (equivalent_of_toCardinalPeano_eq heq)
        (fun h_forward => hnlt_forward (toCardinalPeano_lt_of_lt h_forward))
        (fun h_reverse => hnlt_reverse (toCardinalPeano_lt_of_lt h_reverse))
  | third hlt_reverse hnlt_forward hne =>
      exact ZeroMath.Logic.Trichotomy.third
        (lt_of_toCardinalPeano_lt hlt_reverse)
        (fun h_forward => hnlt_forward (toCardinalPeano_lt_of_lt h_forward))
        (fun heq => hne (toCardinalPeano_eq_of_equivalent heq))

def fromPeano : Peano → Decimal
  | Peano.one => Decimal.one
  | Peano.successor p => successor (fromPeano p)

theorem toPeano_fromPeano (x : Peano) :
  toPeano (fromPeano x) = x := by
  induction x with
  | one => rfl
  | successor x ih =>
      have ih_card := congrArg CardinalNatural.Peano.fromOrdinal ih
      simp only [toPeano, CardinalNatural.Peano.fromOrdinal_toOrdinal] at ih_card
      unfold fromPeano
      apply peano_eq_of_fromOrdinal_eq
      simp only [toPeano, CardinalNatural.Peano.fromOrdinal_toOrdinal,
        CardinalNatural.Peano.fromOrdinal, toCardinalPeano_successor]
      exact congrArg CardinalNatural.Peano.successor ih_card


theorem subtract_toPeano (x y : Decimal) (h : y < x) :
  ∃ h2, toPeano (subtract x y h) = Peano.subtract x.toPeano y.toPeano h2 := by
  let h2 := toPeano_lt_of_lt h
  exists h2
  have h_decimal_add : (subtract x y h + y).toPeano = x.toPeano := by
    apply toPeano_eq_of_equivalent
    apply equivalent_of_toCardinalPeano_eq
    rw [toCardinalPeano_add]
    exact toCardinalPeano_subtract x y h
  rw [add_toPeano] at h_decimal_add
  have h_peano_add : Peano.subtract x.toPeano y.toPeano h2 + y.toPeano = x.toPeano :=
    Peano.subtract_add_cancel x.toPeano y.toPeano h2
  exact Peano.add_cancel_right (toPeano (subtract x y h))
    (Peano.subtract x.toPeano y.toPeano h2) y.toPeano
    (h_decimal_add.trans h_peano_add.symm)

theorem fromPeano_toPeano (x : Decimal) : fromPeano (toPeano x) ≈ x := by
  apply equivalent_of_toPeano_eq
  exact toPeano_fromPeano (toPeano x)


theorem add_subtract_associative (a b c : Decimal) (h : c < b) :
    ∃ h2, subtract (a + b) c h2 ≈ a + subtract b c h := by
  have hc_lt_ab : c < a + b := by
    apply lt_of_toCardinalPeano_lt
    have hb_card : toCardinalPeano c < toCardinalPeano b := toCardinalPeano_lt_of_lt h
    have h_add_card : toCardinalPeano b < toCardinalPeano (a + b) := by
      rw [toCardinalPeano_add, CardinalNatural.Peano.add_commutative]
      apply CardinalNatural.Peano.lt_add_of_right_ne_zero
      apply toCardinalPeano_ne_zero
    exact CardinalNatural.Peano.lt_trans hb_card h_add_card
  let h2 : c < a + b := hc_lt_ab
  refine ⟨h2, ?_⟩
  apply equivalent_of_toCardinalPeano_eq
  apply CardinalNatural.Peano.add_cancel_right
    (toCardinalPeano (subtract (a + b) c h2))
    (toCardinalPeano (a + subtract b c h))
    (toCardinalPeano c)
  rw [toCardinalPeano_subtract]
  rw [toCardinalPeano_add]
  have h_add_sub : toCardinalPeano (a + subtract b c h) + toCardinalPeano c = toCardinalPeano a + toCardinalPeano b := by
    rw [toCardinalPeano_add]
    rw [CardinalNatural.Peano.add_associative]
    rw [toCardinalPeano_subtract]
  rw [h_add_sub]



theorem subtract_subtract_associative (a b c : Decimal) (h : b < a) (h2 : c < subtract a b h) :
    ∃ h3, subtract (subtract a b h) c h2 ≈ subtract a (b + c) h3 := by
  have hbc_lt_a : b + c < a := by
    apply lt_of_toCardinalPeano_lt
    have h_sub : toCardinalPeano c < toCardinalPeano (subtract a b h) :=
      toCardinalPeano_lt_of_lt h2
    have h_add : toCardinalPeano c + toCardinalPeano b < toCardinalPeano (subtract a b h) + toCardinalPeano b := by
      apply ZeroMath.Numbers.CardinalNatural.Peano.add_lt_add_right h_sub
    rw [toCardinalPeano_subtract a b h] at h_add
    rw [toCardinalPeano_add]
    rw [ZeroMath.Numbers.CardinalNatural.Peano.add_commutative (toCardinalPeano b) (toCardinalPeano c)]
    exact h_add
  let h3 : b + c < a := hbc_lt_a
  refine ⟨h3, ?_⟩
  apply equivalent_of_toCardinalPeano_eq
  apply ZeroMath.Numbers.CardinalNatural.Peano.add_cancel_right
    (toCardinalPeano (subtract (subtract a b h) c h2))
    (toCardinalPeano (subtract a (b + c) h3))
    (toCardinalPeano (b + c))
  rw [toCardinalPeano_subtract a (b + c) h3]
  rw [toCardinalPeano_add]
  rw [ZeroMath.Numbers.CardinalNatural.Peano.add_commutative (toCardinalPeano b) (toCardinalPeano c)]
  rw [← ZeroMath.Numbers.CardinalNatural.Peano.add_associative]
  rw [toCardinalPeano_subtract (subtract a b h) c h2]
  rw [toCardinalPeano_subtract a b h]

def addListDigit (a : Sequences.List Digit) (b : Digit) : Sequences.List Digit :=
  let (ds, carry) := addPartialListDigit a b
  if carry.val = .zero then ds else .firstElement carry ds

def multiplyDigitsPeano (a : Digit) (b : CardinalNatural.Peano) : Sequences.List Digit :=
  match b with
  | CardinalNatural.Peano.zero => .firstElement zeroDigit .empty
  | CardinalNatural.Peano.successor b' =>
    let prev := multiplyDigitsPeano a b'
    addListDigit prev a

def multiplyDigits (a b : Digit) : Sequences.List Digit :=
  multiplyDigitsPeano a b.val

theorem digit_cases (d : Digit) :
  d = zeroDigit ∨ d = oneDigit ∨ d = twoDigit ∨ d = threeDigit ∨ d = fourDigit ∨
    d = fiveDigit ∨ d = sixDigit ∨ d = sevenDigit ∨ d = eightDigit ∨ d = nineDigit := by
  cases d with
  | mk val h =>
      cases val with
      | zero =>
          exact Or.inl (Subtype.ext rfl)
      | successor val1 =>
          cases val1 with
          | zero =>
              exact Or.inr (Or.inl (Subtype.ext rfl))
          | successor val2 =>
              cases val2 with
              | zero =>
                  exact Or.inr (Or.inr (Or.inl (Subtype.ext rfl)))
              | successor val3 =>
                  cases val3 with
                  | zero =>
                      exact Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext rfl))))
                  | successor val4 =>
                      cases val4 with
                      | zero =>
                          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext rfl)))))
                      | successor val5 =>
                          cases val5 with
                          | zero =>
                              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext rfl))))))
                          | successor val6 =>
                              cases val6 with
                              | zero =>
                                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext rfl)))))))
                              | successor val7 =>
                                  cases val7 with
                                  | zero =>
                                      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext rfl))))))))
                                  | successor val8 =>
                                      cases val8 with
                                      | zero =>
                                          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext rfl)))))))))
                                      | successor val9 =>
                                          cases val9 with
                                          | zero =>
                                              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Subtype.ext rfl)))))))))
                                          | successor val10 =>
                                              have h1 := CardinalNatural.Peano.lt_of_succ_lt_succ h
                                              have h2 := CardinalNatural.Peano.lt_of_succ_lt_succ h1
                                              have h3 := CardinalNatural.Peano.lt_of_succ_lt_succ h2
                                              have h4 := CardinalNatural.Peano.lt_of_succ_lt_succ h3
                                              have h5 := CardinalNatural.Peano.lt_of_succ_lt_succ h4
                                              have h6 := CardinalNatural.Peano.lt_of_succ_lt_succ h5
                                              have h7 := CardinalNatural.Peano.lt_of_succ_lt_succ h6
                                              have h8 := CardinalNatural.Peano.lt_of_succ_lt_succ h7
                                              have h9 := CardinalNatural.Peano.lt_of_succ_lt_succ h8
                                              have h10 := CardinalNatural.Peano.lt_of_succ_lt_succ h9
                                              exact False.elim (CardinalNatural.Peano.not_lt_zero val10 h10)

theorem addListDigit_multiplyDigits_ne_empty (d b carry : Digit) :
  addListDigit (multiplyDigits d b) carry ≠ Sequences.List.empty := by
  rcases digit_cases d with hd | hd | hd | hd | hd | hd | hd | hd | hd | hd <;>
    subst d <;>
    rcases digit_cases b with hb | hb | hb | hb | hb | hb | hb | hb | hb | hb <;>
    subst b <;>
    rcases digit_cases carry with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc <;>
    subst carry <;>
    decide

theorem addListDigit_multiplyDigits_not_three_or_more
  (d b carry x y z : Digit) (zs : Sequences.List Digit) :
  addListDigit (multiplyDigits d b) carry ≠
    Sequences.List.firstElement x (Sequences.List.firstElement y (Sequences.List.firstElement z zs)) := by
  rcases digit_cases d with hd | hd | hd | hd | hd | hd | hd | hd | hd | hd <;>
    subst d <;>
    rcases digit_cases b with hb | hb | hb | hb | hb | hb | hb | hb | hb | hb <;>
    subst b <;>
    rcases digit_cases carry with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc <;>
    subst carry <;>
    intro h <;> cases h

def multiplyPartialListByDigit (a : Sequences.List Digit) (b : Digit) : Sequences.List Digit × Digit :=
  match a with
  | .empty => (Sequences.List.empty, zeroDigit)
  | .firstElement d ds =>
    let (ds', carry) := multiplyPartialListByDigit ds b
    let digitProduct := multiplyDigits d b
    let withCarry := addListDigit digitProduct carry
    match h : withCarry with
    | .empty => False.elim (addListDigit_multiplyDigits_ne_empty d b carry h)
    | .firstElement x .empty => ⟨.firstElement x ds', zeroDigit⟩
    | .firstElement x (.firstElement y .empty) => ⟨.firstElement y ds', x⟩
    | .firstElement x (.firstElement y (.firstElement z zs)) =>
        False.elim (addListDigit_multiplyDigits_not_three_or_more d b carry x y z zs h)

def multiplyListByDigit (a : Sequences.List Digit) (b : Digit) : Sequences.List Digit :=
  let (ds, carry) := multiplyPartialListByDigit a b
  if carry.val = .zero then ds else .firstElement carry ds

def multiplyList (a b : Sequences.List Digit) : Sequences.List Digit × CardinalNatural.Peano :=
  match b with
  | .empty => ⟨.empty, .zero⟩
  | .firstElement d ds =>
    let (accumulator, shift) := multiplyList a ds
    let digitProduct := multiplyListByDigit a d
    let withShift := Sequences.List.padAtEnd digitProduct zeroDigit shift
    let pair := Sequences.List.padAtStartToSameLength accumulator withShift zeroDigit
    let h_same : Sequences.List.SameLength pair.1 pair.2 :=
      Sequences.List.padAtStartToSameLength_sameLength accumulator withShift zeroDigit
    let ⟨digits, carry⟩ := addAlignedLists pair.1 pair.2 h_same
    if carry then
      ⟨Sequences.List.firstElement oneDigit digits, shift.successor⟩
    else
      ⟨digits, shift.successor⟩

theorem allZero_toCardinalList_zero {l : Sequences.List Digit}
    (h : AllZero l) :
    toCardinalList l CardinalNatural.Peano.zero = CardinalNatural.Peano.zero := by
  induction l with
  | empty => rfl
  | firstElement d ds ih =>
    simp only [toCardinalList]
    rw [h.1, CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.add_zero]
    exact ih h.2

theorem hasNonZero_of_toCardinalList_ne_zero {l : Sequences.List Digit}
    (h : toCardinalList l CardinalNatural.Peano.zero ≠ CardinalNatural.Peano.zero) :
    HasNonZero l := by
  cases allZero_or_hasNonZero l with
  | inl h_zero => exact absurd (allZero_toCardinalList_zero h_zero) h
  | inr h_nz => exact h_nz

theorem tenPow_add (m n : CardinalNatural.Peano) :
    CardinalNatural.Peano.tenPow (m + n) =
      CardinalNatural.Peano.tenPow m * CardinalNatural.Peano.tenPow n := by
  induction n with
  | zero =>
    rw [CardinalNatural.Peano.add_zero, CardinalNatural.Peano.tenPow,
        CardinalNatural.Peano.multiply_one]
  | successor n ih =>
    rw [CardinalNatural.Peano.add_successor, CardinalNatural.Peano.tenPow, ih,
        CardinalNatural.Peano.tenPow,
        ← CardinalNatural.Peano.multiply_associative,
        CardinalNatural.Peano.multiply_commutative CardinalNatural.Peano.ten _,
        CardinalNatural.Peano.multiply_associative]

theorem padAtEnd_length (l : Sequences.List Digit) (n : CardinalNatural.Peano) :
    (Sequences.List.padAtEnd l zeroDigit n).length = l.length + n := by
  induction l with
  | empty =>
    induction n with
    | zero => rfl
    | successor n ih =>
      simp only [Sequences.List.padAtEnd, Sequences.List.length,
                 CardinalNatural.Peano.zero_add, ih,
                 CardinalNatural.Peano.successor_add]
  | firstElement d ds ih =>
    simp only [Sequences.List.padAtEnd, Sequences.List.length, ih,
               CardinalNatural.Peano.add_associative]
    rw [CardinalNatural.Peano.add_commutative CardinalNatural.Peano.one n,
        ← CardinalNatural.Peano.add_associative]

theorem toCardinalList_padAtEnd (l : Sequences.List Digit) (n : CardinalNatural.Peano) :
    toCardinalList (Sequences.List.padAtEnd l zeroDigit n) CardinalNatural.Peano.zero =
      toCardinalList l CardinalNatural.Peano.zero * CardinalNatural.Peano.tenPow n := by
  induction l with
  | empty =>
    induction n with
    | zero =>
      simp [Sequences.List.padAtEnd, toCardinalList, CardinalNatural.Peano.tenPow,
            CardinalNatural.Peano.multiply_one]
    | successor n ih =>
      simp only [Sequences.List.padAtEnd, toCardinalList_firstElement, zeroDigit,
                 CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.zero_add]
      rw [ih, CardinalNatural.Peano.zero_multiply]
  | firstElement d ds ih =>
    simp only [Sequences.List.padAtEnd, toCardinalList_firstElement, padAtEnd_length]
    rw [tenPow_add, ← CardinalNatural.Peano.multiply_associative, ih,
        ← CardinalNatural.Peano.multiply_distributive_over_add_left, ← toCardinalList_firstElement]

theorem addPartialListDigit_spec (a : Sequences.List Digit) (b : Digit) :
    (addPartialListDigit a b).1.length = a.length ∧
    toCardinalList (addPartialListDigit a b).1 CardinalNatural.Peano.zero +
        (addPartialListDigit a b).2.val * CardinalNatural.Peano.tenPow a.length =
      toCardinalList a CardinalNatural.Peano.zero + b.val := by
  induction a generalizing b with
  | empty =>
    simp only [addPartialListDigit, Sequences.List.length, toCardinalList,
               CardinalNatural.Peano.tenPow, CardinalNatural.Peano.multiply_one,
               CardinalNatural.Peano.zero_add, and_self, zeroDigit]
  | firstElement d ds ih =>
    unfold addPartialListDigit
    dsimp only
    obtain ⟨h_len, h_val⟩ := ih b
    cases h_rec : addPartialListDigit ds b with
    | mk ds' carry' =>
      rw [h_rec] at h_len h_val; dsimp only at h_len h_val
      split
      · next h_lt =>
        refine ⟨by simp [Sequences.List.length, h_len], ?_⟩
        rw [toCardinalList_firstElement, h_len, Sequences.List.length,
            CardinalNatural.Peano.tenPow_add_one,
            CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.add_zero,
            CardinalNatural.Peano.multiply_distributive_over_add_left,
            toCardinalList_firstElement]
        simp only [CardinalNatural.Peano.add_associative,
                   CardinalNatural.Peano.add_left_commutative]
        rw [CardinalNatural.Peano.add_commutative (toCardinalList ds' _)
              (carry'.val * _), h_val]
        simp only [CardinalNatural.Peano.add_associative]
      · next h_not_lt =>
        have h_le : CardinalNatural.Peano.ten ≤ d.val + carry'.val :=
          CardinalNatural.Peano.isLessThan_false_implies_le (eq_false_of_ne_true h_not_lt)
        refine ⟨by simp [Sequences.List.length, h_len], ?_⟩
        rw [toCardinalList_firstElement, h_len, Sequences.List.length,
            CardinalNatural.Peano.one_multiply, CardinalNatural.Peano.tenPow_add_one,
            toCardinalList_firstElement]
        have h_cancel := CardinalNatural.Peano.subtract_add_cancel
          (d.val + carry'.val) CardinalNatural.Peano.ten h_le
        calc CardinalNatural.Peano.subtract (d.val + carry'.val)
                CardinalNatural.Peano.ten h_le * CardinalNatural.Peano.tenPow ds.length +
              toCardinalList ds' CardinalNatural.Peano.zero +
              CardinalNatural.Peano.ten * CardinalNatural.Peano.tenPow ds.length
            = (CardinalNatural.Peano.subtract (d.val + carry'.val)
                CardinalNatural.Peano.ten h_le + CardinalNatural.Peano.ten) *
                CardinalNatural.Peano.tenPow ds.length +
              toCardinalList ds' CardinalNatural.Peano.zero := by
                rw [CardinalNatural.Peano.multiply_distributive_over_add_left]
                simp only [CardinalNatural.Peano.add_associative,
                           CardinalNatural.Peano.add_left_commutative]
          _ = (d.val + carry'.val) * CardinalNatural.Peano.tenPow ds.length +
              toCardinalList ds' CardinalNatural.Peano.zero := by
                rw [CardinalNatural.Peano.add_commutative
                      (CardinalNatural.Peano.subtract _ _ _) _, h_cancel]
          _ = d.val * CardinalNatural.Peano.tenPow ds.length +
              (toCardinalList ds' CardinalNatural.Peano.zero +
                carry'.val * CardinalNatural.Peano.tenPow ds.length) := by
                rw [CardinalNatural.Peano.multiply_distributive_over_add_left]
                simp only [CardinalNatural.Peano.add_associative,
                           CardinalNatural.Peano.add_left_commutative]
          _ = d.val * CardinalNatural.Peano.tenPow ds.length +
              (toCardinalList ds CardinalNatural.Peano.zero + b.val) := by
                rw [CardinalNatural.Peano.add_commutative (toCardinalList ds' _)
                      (carry'.val * _), h_val]
          _ = d.val * CardinalNatural.Peano.tenPow ds.length +
              toCardinalList ds CardinalNatural.Peano.zero + b.val := by
                rw [← CardinalNatural.Peano.add_associative]

theorem toCardinalList_addListDigit (a : Sequences.List Digit) (b : Digit) :
    toCardinalList (addListDigit a b) CardinalNatural.Peano.zero =
      toCardinalList a CardinalNatural.Peano.zero + b.val := by
  obtain ⟨h_len, h_val⟩ := addPartialListDigit_spec a b
  cases h_rec : addPartialListDigit a b with
  | mk ds carry =>
    rw [h_rec] at h_len h_val; dsimp only at h_len h_val
    unfold addListDigit; rw [h_rec]; dsimp only
    by_cases h_carry : carry.val = CardinalNatural.Peano.zero
    · rw [if_pos h_carry, h_carry, CardinalNatural.Peano.zero_multiply,
          CardinalNatural.Peano.add_zero] at h_val
      exact h_val
    · rw [if_neg h_carry, toCardinalList_firstElement, h_len,
          CardinalNatural.Peano.add_commutative (carry.val * _)]
      exact h_val

theorem toCardinalList_multiplyDigitsPeano (d : Digit) (n : CardinalNatural.Peano) :
    toCardinalList (multiplyDigitsPeano d n) CardinalNatural.Peano.zero =
      d.val * n := by
  induction n with
  | zero =>
    simp [multiplyDigitsPeano, toCardinalList_firstElement, toCardinalList, zeroDigit,
          Sequences.List.length, CardinalNatural.Peano.tenPow, CardinalNatural.Peano.multiply_zero,
          CardinalNatural.Peano.multiply_one]
  | successor n ih =>
    unfold multiplyDigitsPeano
    rw [toCardinalList_addListDigit, ih, CardinalNatural.Peano.multiply_successor]

theorem multiplyPartialListByDigit_spec (a : Sequences.List Digit) (d : Digit) :
    (multiplyPartialListByDigit a d).1.length = a.length ∧
    toCardinalList (multiplyPartialListByDigit a d).1 CardinalNatural.Peano.zero +
        (multiplyPartialListByDigit a d).2.val * CardinalNatural.Peano.tenPow a.length =
      toCardinalList a CardinalNatural.Peano.zero * d.val := by
  induction a with
  | empty =>
    simp [multiplyPartialListByDigit, toCardinalList, Sequences.List.length,
          CardinalNatural.Peano.tenPow, CardinalNatural.Peano.multiply_one, zeroDigit,
          CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.multiply_zero]
  | firstElement da das ih =>
    unfold multiplyPartialListByDigit; dsimp only
    obtain ⟨h_len, h_val⟩ := ih
    cases h_rec : multiplyPartialListByDigit das d with
    | mk ds' carry' =>
      rw [h_rec] at h_len h_val; dsimp only at h_len h_val
      have h_wc_val : toCardinalList (addListDigit (multiplyDigits da d) carry')
          CardinalNatural.Peano.zero = da.val * d.val + carry'.val := by
        unfold multiplyDigits
        rw [toCardinalList_addListDigit, toCardinalList_multiplyDigitsPeano]
      set withCarry := addListDigit (multiplyDigits da d) carry' with h_wc_def
      have core : toCardinalList withCarry CardinalNatural.Peano.zero *
            CardinalNatural.Peano.tenPow das.length +
            toCardinalList ds' CardinalNatural.Peano.zero =
          (da.val * CardinalNatural.Peano.tenPow das.length +
            toCardinalList das CardinalNatural.Peano.zero) * d.val := by
        rw [h_wc_val, toCardinalList_firstElement,
            CardinalNatural.Peano.multiply_distributive_over_add_left,
            CardinalNatural.Peano.multiply_distributive_over_add_left]
        have : da.val * d.val * CardinalNatural.Peano.tenPow das.length =
            da.val * CardinalNatural.Peano.tenPow das.length * d.val := by
          rw [CardinalNatural.Peano.multiply_associative,
              CardinalNatural.Peano.multiply_commutative d.val _,
              ← CardinalNatural.Peano.multiply_associative]
        rw [this]
        simp only [CardinalNatural.Peano.add_associative,
                   CardinalNatural.Peano.add_left_commutative]
        rw [CardinalNatural.Peano.add_commutative (toCardinalList ds' _)
              (carry'.val * _), h_val]
      cases h_wc : withCarry with
      | empty => exact False.elim (addListDigit_multiplyDigits_ne_empty da d carry' h_wc)
      | firstElement x rest =>
        cases rest with
        | empty =>
          -- 1-digit case
          simp only [h_wc]
          refine ⟨by simp [Sequences.List.length, h_len], ?_⟩
          have hx : x.val = toCardinalList withCarry CardinalNatural.Peano.zero := by
            rw [h_wc, toCardinalList_firstElement, toCardinalList, Sequences.List.length,
                CardinalNatural.Peano.tenPow, CardinalNatural.Peano.multiply_one,
                CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.add_zero]
          rw [toCardinalList_firstElement, h_len, Sequences.List.length,
              CardinalNatural.Peano.tenPow_add_one,
              zeroDigit, CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.add_zero,
              hx, ← toCardinalList_firstElement, core]
        | firstElement y rest' =>
          cases rest' with
          | empty =>
            -- 2-digit case
            simp only [h_wc]
            refine ⟨by simp [Sequences.List.length, h_len], ?_⟩
            have hxy : x.val * CardinalNatural.Peano.ten + y.val =
                toCardinalList withCarry CardinalNatural.Peano.zero := by
              rw [h_wc, toCardinalList_firstElement, toCardinalList_firstElement, toCardinalList,
                  Sequences.List.length, CardinalNatural.Peano.zero_add,
                  CardinalNatural.Peano.tenPow, CardinalNatural.Peano.multiply_one,
                  CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.add_zero,
                  CardinalNatural.Peano.tenPow, CardinalNatural.Peano.multiply_one]
            rw [toCardinalList_firstElement, h_len, Sequences.List.length,
                CardinalNatural.Peano.tenPow_add_one]
            calc y.val * CardinalNatural.Peano.tenPow das.length +
                  toCardinalList ds' CardinalNatural.Peano.zero +
                  x.val * (CardinalNatural.Peano.ten * CardinalNatural.Peano.tenPow das.length)
                = (x.val * CardinalNatural.Peano.ten + y.val) *
                    CardinalNatural.Peano.tenPow das.length +
                  toCardinalList ds' CardinalNatural.Peano.zero := by
                    rw [CardinalNatural.Peano.multiply_distributive_over_add_left,
                        ← CardinalNatural.Peano.multiply_associative]
                    simp only [CardinalNatural.Peano.add_associative,
                               CardinalNatural.Peano.add_left_commutative]
              _ = toCardinalList withCarry CardinalNatural.Peano.zero *
                    CardinalNatural.Peano.tenPow das.length +
                  toCardinalList ds' CardinalNatural.Peano.zero := by rw [hxy]
              _ = (da.val * CardinalNatural.Peano.tenPow das.length +
                    toCardinalList das CardinalNatural.Peano.zero) * d.val := core
          | firstElement _ _ =>
            exact False.elim (addListDigit_multiplyDigits_not_three_or_more da d carry' x y _ _ h_wc)

theorem toCardinalList_multiplyListByDigit (a : Sequences.List Digit) (d : Digit) :
    toCardinalList (multiplyListByDigit a d) CardinalNatural.Peano.zero =
      toCardinalList a CardinalNatural.Peano.zero * d.val := by
  obtain ⟨h_len, h_val⟩ := multiplyPartialListByDigit_spec a d
  cases h_rec : multiplyPartialListByDigit a d with
  | mk ds carry =>
    rw [h_rec] at h_len h_val; dsimp only at h_len h_val
    unfold multiplyListByDigit; rw [h_rec]; dsimp only
    by_cases h_carry : carry.val = CardinalNatural.Peano.zero
    · rw [if_pos h_carry, h_carry, CardinalNatural.Peano.zero_multiply,
          CardinalNatural.Peano.add_zero] at h_val
      exact h_val
    · rw [if_neg h_carry, toCardinalList_firstElement, h_len,
          CardinalNatural.Peano.add_commutative (carry.val * _)]
      exact h_val

theorem multiplyList_spec (a b : Sequences.List Digit) :
    (multiplyList a b).2 = b.length ∧
    toCardinalList (multiplyList a b).1 CardinalNatural.Peano.zero =
      toCardinalList a CardinalNatural.Peano.zero * toCardinalList b CardinalNatural.Peano.zero := by
  induction b with
  | empty =>
    simp [multiplyList, toCardinalList, Sequences.List.length,
          CardinalNatural.Peano.multiply_zero]
  | firstElement d ds ih =>
    obtain ⟨h_shift, h_acc⟩ := ih
    unfold multiplyList; dsimp only
    cases h_rec : multiplyList a ds with
    | mk acc shift =>
      rw [h_rec] at h_shift h_acc; dsimp only at h_shift h_acc
      refine ⟨by simp [Sequences.List.length, h_shift], ?_⟩
      set digitProduct := multiplyListByDigit a d
      set withShift := Sequences.List.padAtEnd digitProduct zeroDigit shift
      set pair := Sequences.List.padAtStartToSameLength acc withShift zeroDigit
      have h_dp : toCardinalList digitProduct CardinalNatural.Peano.zero =
          toCardinalList a CardinalNatural.Peano.zero * d.val :=
        toCardinalList_multiplyListByDigit a d
      have h_ws : toCardinalList withShift CardinalNatural.Peano.zero =
          toCardinalList a CardinalNatural.Peano.zero * d.val *
          CardinalNatural.Peano.tenPow shift := by
        simp only [withShift, toCardinalList_padAtEnd, h_dp]
      have h_sum : toCardinalList pair.1 CardinalNatural.Peano.zero +
          toCardinalList pair.2 CardinalNatural.Peano.zero =
          toCardinalList a CardinalNatural.Peano.zero *
          toCardinalList (Sequences.List.firstElement d ds) CardinalNatural.Peano.zero := by
        rw [toCardinalList_padAtStartToSameLength_fst,
            toCardinalList_padAtStartToSameLength_snd, h_acc, h_ws, h_shift,
            toCardinalList_firstElement,
            CardinalNatural.Peano.multiply_distributive_over_add_right,
            CardinalNatural.Peano.multiply_associative]
      have h_same := Sequences.List.padAtStartToSameLength_sameLength acc withShift zeroDigit
      cases h_add : addAlignedLists pair.1 pair.2 h_same with
      | mk digits carry =>
        have h_spec := addAlignedLists_spec h_same
        rw [h_add] at h_spec; dsimp only at h_spec
        obtain ⟨h_dlen, h_dval⟩ := h_spec
        cases carry with
        | true =>
          simp only [ite_true]
          rw [toCardinalList_firstElement, h_dlen,
              CardinalNatural.Peano.one_multiply]
          simp only [if_true] at h_dval
          rw [CardinalNatural.Peano.add_commutative
                (CardinalNatural.Peano.tenPow _) _, h_dval, h_sum]
        | false =>
          simp only [ite_false]
          simp only [if_false, CardinalNatural.Peano.add_zero] at h_dval
          rw [h_dval, h_sum]

theorem hasNonZero_multiplyList (a b : Sequences.List Digit)
    (ha : HasNonZero a) (hb : HasNonZero b) :
    HasNonZero (multiplyList a b).1 := by
  apply hasNonZero_of_toCardinalList_ne_zero
  rw [(multiplyList_spec a b).2]
  exact CardinalNatural.Peano.multiply_ne_zero _ _
    (toCardinalList_ne_zero_of_hasNonZero a CardinalNatural.Peano.zero ha)
    (toCardinalList_ne_zero_of_hasNonZero b CardinalNatural.Peano.zero hb)

def multiply (a b : Decimal) : Decimal :=
  let (digits, shift) := multiplyList a.val b.val
  ⟨digits, hasNonZero_multiplyList a.val b.val a.property b.property⟩

end Decimal

end ZeroMath.Numbers.OrdinalNatural
