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


def one : Decimal :=
  ⟨Sequences.List.firstElement ⟨CardinalNatural.Peano.one, CardinalNatural.Peano.one_lt_ten⟩ Sequences.List.empty, by
    apply Sequences.List.AnyElement.first
    intro h
    cases h⟩

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

def zeroDigit : Digit :=
  ⟨CardinalNatural.Peano.zero, CardinalNatural.Peano.zero_lt_succ CardinalNatural.Peano.nine⟩

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

instance : LT Decimal where
  lt := LessThan

def LessThanOrEquivalent (x y : Decimal) : Prop := x < y ∨ x ≈ y

instance : LE Decimal where
  le := LessThanOrEquivalent

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

theorem fromPeano_toPeano (x : Decimal) : fromPeano (toPeano x) ≈ x := by
  apply equivalent_of_toPeano_eq
  exact toPeano_fromPeano (toPeano x)

end Decimal

end ZeroMath.Numbers.OrdinalNatural
