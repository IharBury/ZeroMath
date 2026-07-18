import ZeroMath.Numbers.CardinalNatural.Peano
import ZeroMath.Sequences.List

namespace ZeroMath.Numbers.CardinalNatural

namespace Decimal

def Digit := {d : CardinalNatural.Peano // d < CardinalNatural.Peano.ten}

instance : DecidableEq Digit :=
  fun x y =>
    if h : x.val = y.val then
      isTrue (Subtype.ext h)
    else
      isFalse (fun h' => h (congrArg Subtype.val h'))

end Decimal

def Decimal := { l : Sequences.List Decimal.Digit // l ≠ Sequences.List.empty }

namespace Decimal

instance : DecidableEq Decimal :=
  fun x y =>
    if h : x.val = y.val then
      isTrue (Subtype.ext h)
    else
      isFalse (fun h' => h (congrArg Subtype.val h'))

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

def normalizeList (a : Sequences.List Digit) : Decimal :=
  match a with
  | .empty => zero
  | .firstElement d ds =>
      if d.val = CardinalNatural.Peano.zero then
        normalizeList ds
      else
        ⟨Sequences.List.firstElement d ds, by simp⟩

def normalize (a : Decimal) : Decimal :=
  normalizeList a.val

def toPeanoList (x : Sequences.List Digit) (accumulator : Peano) : Peano :=
  match x with
  | .empty => accumulator
  | .firstElement d ds => toPeanoList ds (accumulator * Peano.ten + d.val)

def toPeano (d : Decimal) : Peano :=
  toPeanoList d.val Peano.zero

theorem normalizeList_toPeano (a : Sequences.List Digit) :
  toPeano (normalizeList a) = toPeanoList a Peano.zero := by
  induction a with
  | empty =>
      rfl
  | firstElement d ds ih =>
      unfold normalizeList
      split
      · next hd =>
          rw [ih]
          change toPeanoList ds Peano.zero =
            toPeanoList ds (Peano.zero * Peano.ten + d.val)
          rw [hd, Peano.zero_multiply, Peano.add_zero]
      · rfl

theorem normalize_toPeano (x : Decimal) : x.normalize.toPeano = x.toPeano := by
  unfold normalize toPeano
  exact normalizeList_toPeano x.val

theorem normalizeList_isNormalized (a : Sequences.List Digit) :
  (normalizeList a).isNormalized = true := by
  induction a with
  | empty =>
      rfl
  | firstElement d ds ih =>
      unfold normalizeList
      split
      · exact ih
      · next hd =>
          cases ds with
          | empty =>
              rfl
          | firstElement d' ds' =>
              simp [isNormalized, hd]

theorem normalize_isNormalized (d : Decimal) : d.normalize.isNormalized = true := by
  unfold normalize
  exact normalizeList_isNormalized d.val

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

theorem toPeano_fromPeano (x : Peano) :
  toPeano (fromPeano x) = x := by
  induction x with
  | zero =>
    rfl
  | successor x ih =>
    unfold fromPeano
    rw [successor_toPeano]
    rw [ih]

-- toPeanoList l acc = acc * 10^len(l) + toPeanoList l 0
theorem toPeanoList_acc_split (l : Sequences.List Digit) (acc : Peano) :
    toPeanoList l acc =
      acc * Peano.tenPow l.length + toPeanoList l Peano.zero := by
  induction l generalizing acc with
  | empty =>
    simp only [toPeanoList, Sequences.List.length, Peano.tenPow,
               Peano.multiply_one, Peano.add_zero]
  | firstElement d ds ih =>
    simp only [toPeanoList, Sequences.List.length,
               Peano.zero_multiply, Peano.zero_add]
    rw [ih (acc * Peano.ten + d.val), ih d.val, Peano.tenPow_add_one,
        Peano.multiply_distributive_over_add_left,
        Peano.multiply_associative,
        Peano.add_associative]

theorem toPeanoList_firstElement (d : Digit) (ds : Sequences.List Digit) :
  toPeanoList (Sequences.List.firstElement d ds) Peano.zero =
    d.val * Peano.tenPow ds.length + toPeanoList ds Peano.zero := by
  change toPeanoList ds (Peano.zero * Peano.ten + d.val) = _
  rw [Peano.zero_multiply, Peano.zero_add]
  exact toPeanoList_acc_split ds d.val

-- toPeanoList l 0 < 10^len(l)
theorem toPeanoList_lt_tenPow (l : Sequences.List Digit) :
    toPeanoList l Peano.zero < Peano.tenPow l.length := by
  induction l with
  | empty =>
    simp only [toPeanoList, Sequences.List.length, Peano.tenPow]
    exact Peano.LessThan.base
  | firstElement d ds ih =>
    simp only [toPeanoList, Sequences.List.length,
               Peano.zero_multiply, Peano.zero_add]
    rw [toPeanoList_acc_split ds d.val, Peano.tenPow_add_one]
    have h1 : d.val * Peano.tenPow ds.length + toPeanoList ds Peano.zero <
              d.val * Peano.tenPow ds.length + Peano.tenPow ds.length :=
      Peano.add_lt_add_left ih (d.val * Peano.tenPow ds.length)
    have h2 : d.val * Peano.tenPow ds.length + Peano.tenPow ds.length =
              d.val.successor * Peano.tenPow ds.length :=
      (Peano.successor_multiply d.val (Peano.tenPow ds.length)).symm
    have h3 : d.val.successor * Peano.tenPow ds.length ≤
              Peano.ten * Peano.tenPow ds.length :=
      Peano.multiply_le_mul_left (Peano.succ_le_of_lt d.property)
        (Peano.tenPow ds.length)
    rw [h2] at h1
    cases h3 with
    | inl hlt => exact Peano.lt_trans h1 hlt
    | inr heq => rw [← heq]; exact h1

-- Same-length digit lists with the same toPeanoList value are equal
theorem toPeanoList_inj_sameLength {l1 l2 : Sequences.List Digit}
    (hsl : Sequences.List.SameLength l1 l2)
    (heq : toPeanoList l1 Peano.zero = toPeanoList l2 Peano.zero) :
    l1 = l2 := by
  induction hsl with
  | empty => rfl
  | firstElement h_tail ih =>
    rename_i d1 d2 ds1 ds2
    simp only [toPeanoList, Peano.zero_multiply, Peano.zero_add] at heq
    rw [toPeanoList_acc_split ds1 d1.val,
        toPeanoList_acc_split ds2 d2.val] at heq
    have h_len : ds2.length = ds1.length :=
      (Sequences.List.sameLength_length_eq h_tail).symm
    rw [h_len] at heq
    have hv1_lt : toPeanoList ds1 Peano.zero < Peano.tenPow ds1.length :=
      toPeanoList_lt_tenPow ds1
    have hv2_lt : toPeanoList ds2 Peano.zero < Peano.tenPow ds1.length := by
      rw [← h_len]; exact toPeanoList_lt_tenPow ds2
    have hd_eq : d1.val = d2.val := by
      cases Peano.trichotomy_or d1.val d2.val with
      | inl hlt =>
        exfalso
        have hchain :
            d1.val * Peano.tenPow ds1.length + Peano.tenPow ds1.length ≤
            d1.val * Peano.tenPow ds1.length +
              toPeanoList ds1 Peano.zero := by
          have hstep1 :
              d1.val * Peano.tenPow ds1.length + Peano.tenPow ds1.length =
              d1.val.successor * Peano.tenPow ds1.length :=
            (Peano.successor_multiply d1.val (Peano.tenPow ds1.length)).symm
          have hstep2 :
              d1.val.successor * Peano.tenPow ds1.length ≤
              d2.val * Peano.tenPow ds1.length :=
            Peano.multiply_le_mul_left (Peano.succ_le_of_lt hlt)
              (Peano.tenPow ds1.length)
          have hstep3 :
              d2.val * Peano.tenPow ds1.length ≤
              d2.val * Peano.tenPow ds1.length +
                toPeanoList ds2 Peano.zero :=
            Peano.le_add_self_left _ _
          rw [hstep1]
          exact Peano.le_trans (Peano.le_trans hstep2 hstep3) (Or.inr heq.symm)
        exact absurd
          (Peano.le_lt_trans (Peano.add_le_cancel_left hchain) hv1_lt)
          (Peano.not_lt_self (Peano.tenPow ds1.length))
      | inr h =>
        cases h with
        | inl heq_d => exact heq_d
        | inr hgt =>
          exfalso
          have hchain :
              d2.val * Peano.tenPow ds1.length + Peano.tenPow ds1.length ≤
              d2.val * Peano.tenPow ds1.length +
                toPeanoList ds2 Peano.zero := by
            have hstep1 :
                d2.val * Peano.tenPow ds1.length + Peano.tenPow ds1.length =
                d2.val.successor * Peano.tenPow ds1.length :=
              (Peano.successor_multiply d2.val (Peano.tenPow ds1.length)).symm
            have hstep2 :
                d2.val.successor * Peano.tenPow ds1.length ≤
                d1.val * Peano.tenPow ds1.length :=
              Peano.multiply_le_mul_left (Peano.succ_le_of_lt hgt)
                (Peano.tenPow ds1.length)
            have hstep3 :
                d1.val * Peano.tenPow ds1.length ≤
                d1.val * Peano.tenPow ds1.length +
                  toPeanoList ds1 Peano.zero :=
              Peano.le_add_self_left _ _
            rw [hstep1]
            exact Peano.le_trans (Peano.le_trans hstep2 hstep3) (Or.inr heq)
          exact absurd
            (Peano.le_lt_trans (Peano.add_le_cancel_left hchain) hv2_lt)
            (Peano.not_lt_self (Peano.tenPow ds1.length))
    have hv_eq : toPeanoList ds1 Peano.zero = toPeanoList ds2 Peano.zero := by
      have heq' := heq
      rw [hd_eq] at heq'
      exact Peano.add_left_cancel _ _ _ heq'
    rw [Subtype.ext hd_eq, ih hv_eq]

theorem toPeano_zero : toPeano zero = Peano.zero := rfl

theorem tenPow_pos (n : Peano) : Peano.zero < Peano.tenPow n := by
  induction n with
  | zero => exact Peano.LessThan.base
  | successor n ih => exact Peano.lt_trans ih (Peano.tenPow_lt_succ n)

theorem toPeanoList_ge_tenPow_of_ne_zero (d : Digit) (ds : Sequences.List Digit)
    (hd : d.val ≠ Peano.zero) :
    Peano.tenPow ds.length ≤
      d.val * Peano.tenPow ds.length + toPeanoList ds Peano.zero := by
  have hd_pos : Peano.one ≤ d.val := by
    cases h_d : d.val with
    | zero => exact absurd h_d hd
    | successor v => exact Peano.succ_le_of_lt (Peano.zero_lt_succ v)
  have hge1 : Peano.one * Peano.tenPow ds.length ≤ d.val * Peano.tenPow ds.length :=
    Peano.multiply_le_mul_left hd_pos (Peano.tenPow ds.length)
  rw [Peano.one_multiply] at hge1
  exact Peano.le_trans hge1 (Peano.le_add_self_left _ _)

theorem eq_zero_of_normalized_toPeano_zero {d : Decimal}
    (hd : d.isNormalized = true) (h : toPeano d = Peano.zero) : d = zero := by
  obtain ⟨val, prop⟩ := d
  cases val with
  | empty => exact absurd rfl prop
  | firstElement digit rest =>
    cases rest with
    | empty =>
      simp only [toPeano, toPeanoList, Peano.zero_multiply, Peano.zero_add] at h
      apply Subtype.ext
      show Sequences.List.firstElement digit Sequences.List.empty =
        Sequences.List.firstElement zeroDigit Sequences.List.empty
      exact congrArg (fun v => Sequences.List.firstElement v Sequences.List.empty)
        (Subtype.ext h)
    | firstElement d' ds' =>
      simp only [isNormalized, decide_eq_true_eq] at hd
      have h' :
          toPeanoList
            (Sequences.List.firstElement digit (Sequences.List.firstElement d' ds'))
            Peano.zero = Peano.zero := by
        simpa [toPeano] using h
      rw [toPeanoList_firstElement] at h'
      let rest := Sequences.List.firstElement d' ds'
      have hge := toPeanoList_ge_tenPow_of_ne_zero digit rest hd
      have hlt : Peano.zero <
          digit.val * Peano.tenPow rest.length + toPeanoList rest Peano.zero :=
        Peano.lt_of_lt_of_le (tenPow_pos rest.length) hge
      exact absurd (Peano.le_lt_trans (Or.inr h') hlt) (Peano.not_lt_self _)

theorem leadingDigit_ne_zero_of_normalized_ne_zero
    {digit : Digit} {rest : Sequences.List Digit} {hprop : Sequences.List.firstElement digit rest ≠ Sequences.List.empty}
    (hd : isNormalized ⟨Sequences.List.firstElement digit rest, hprop⟩ = true)
    (hne : (⟨Sequences.List.firstElement digit rest, hprop⟩ : Decimal) ≠ zero) :
    digit.val ≠ Peano.zero := by
  cases rest with
  | empty =>
    intro hdigit
    apply hne
    apply Subtype.ext
    have hdigit' : digit = zeroDigit := Subtype.ext hdigit
    simp only [hdigit']
    rfl
  | firstElement _ _ =>
    simpa [isNormalized, decide_eq_true_eq] using hd

-- Normalized Decimals with the same toPeano value are equal
theorem normalize_inj {a b : Decimal}
    (ha : a.isNormalized = true) (hb : b.isNormalized = true)
    (heq : toPeano a = toPeano b) : a = b := by
  by_cases ha0 : toPeano a = Peano.zero
  · rw [eq_zero_of_normalized_toPeano_zero ha ha0,
        eq_zero_of_normalized_toPeano_zero hb (heq.symm.trans ha0)]
  · have hb0 : toPeano b ≠ Peano.zero := by
      intro h; exact ha0 (heq.trans h)
    have ha_ne_zero : a ≠ zero := by
      intro h; apply ha0; rw [h]; exact toPeano_zero
    have hb_ne_zero : b ≠ zero := by
      intro h; apply hb0; rw [h]; exact toPeano_zero
    obtain ⟨val_a, prop_a⟩ := a
    obtain ⟨val_b, prop_b⟩ := b
    cases val_a with
    | empty => exact absurd rfl prop_a
    | firstElement da das =>
      cases val_b with
      | empty => exact absurd rfl prop_b
      | firstElement db dbs =>
        have hda_ne : da.val ≠ Peano.zero :=
          leadingDigit_ne_zero_of_normalized_ne_zero ha ha_ne_zero
        have hdb_ne : db.val ≠ Peano.zero :=
          leadingDigit_ne_zero_of_normalized_ne_zero hb hb_ne_zero
        simp only [toPeano] at heq
        have heq_raw :
            toPeanoList (Sequences.List.firstElement da das) Peano.zero =
            toPeanoList (Sequences.List.firstElement db dbs) Peano.zero := heq
        rw [toPeanoList_firstElement, toPeanoList_firstElement] at heq
        have h_len : das.length = dbs.length := by
          cases Peano.trichotomy_or das.length dbs.length with
          | inl hlt =>
            have hval_lt :
                da.val * Peano.tenPow das.length + toPeanoList das Peano.zero <
                Peano.ten * Peano.tenPow das.length := by
              have hstep1 :
                  da.val * Peano.tenPow das.length + toPeanoList das Peano.zero <
                  da.val * Peano.tenPow das.length + Peano.tenPow das.length :=
                Peano.add_lt_add_left (toPeanoList_lt_tenPow das) _
              have hstep2 :
                  da.val * Peano.tenPow das.length + Peano.tenPow das.length =
                  da.val.successor * Peano.tenPow das.length :=
                (Peano.successor_multiply da.val _).symm
              have hstep3 :
                  da.val.successor * Peano.tenPow das.length ≤
                  Peano.ten * Peano.tenPow das.length :=
                Peano.multiply_le_mul_left (Peano.succ_le_of_lt da.property) _
              rw [hstep2] at hstep1
              cases hstep3 with
              | inl hlt3 => exact Peano.lt_trans hstep1 hlt3
              | inr heq3 => rw [← heq3]; exact hstep1
            have htenPow_le :
                Peano.tenPow das.length.successor ≤ Peano.tenPow dbs.length :=
              Peano.tenPow_monotone (Peano.succ_le_of_lt hlt)
            have hval_ge :
                Peano.tenPow dbs.length ≤
                db.val * Peano.tenPow dbs.length + toPeanoList dbs Peano.zero :=
              toPeanoList_ge_tenPow_of_ne_zero db dbs hdb_ne
            exact absurd
              (Peano.le_lt_trans
                (Peano.le_trans htenPow_le
                  (Peano.le_trans hval_ge (Or.inr heq.symm)))
                hval_lt)
              (Peano.not_lt_self _)
          | inr h =>
            cases h with
            | inl heq_l => exact heq_l
            | inr hgt =>
              have hval_lt :
                  db.val * Peano.tenPow dbs.length + toPeanoList dbs Peano.zero <
                  Peano.ten * Peano.tenPow dbs.length := by
                have hstep1 :
                    db.val * Peano.tenPow dbs.length + toPeanoList dbs Peano.zero <
                    db.val * Peano.tenPow dbs.length + Peano.tenPow dbs.length :=
                  Peano.add_lt_add_left (toPeanoList_lt_tenPow dbs) _
                have hstep2 :
                    db.val * Peano.tenPow dbs.length + Peano.tenPow dbs.length =
                    db.val.successor * Peano.tenPow dbs.length :=
                  (Peano.successor_multiply db.val _).symm
                have hstep3 :
                    db.val.successor * Peano.tenPow dbs.length ≤
                    Peano.ten * Peano.tenPow dbs.length :=
                  Peano.multiply_le_mul_left (Peano.succ_le_of_lt db.property) _
                rw [hstep2] at hstep1
                cases hstep3 with
                | inl hlt3 => exact Peano.lt_trans hstep1 hlt3
                | inr heq3 => rw [← heq3]; exact hstep1
              have htenPow_le :
                  Peano.tenPow dbs.length.successor ≤ Peano.tenPow das.length :=
                Peano.tenPow_monotone (Peano.succ_le_of_lt hgt)
              have hval_ge :
                  Peano.tenPow das.length ≤
                  da.val * Peano.tenPow das.length + toPeanoList das Peano.zero :=
                toPeanoList_ge_tenPow_of_ne_zero da das hda_ne
              exact absurd
                (Peano.le_lt_trans
                  (Peano.le_trans htenPow_le
                    (Peano.le_trans hval_ge (Or.inr heq)))
                  hval_lt)
                (Peano.not_lt_self _)
        have hsl : Sequences.List.SameLength
            (Sequences.List.firstElement da das)
            (Sequences.List.firstElement db dbs) :=
          Sequences.List.sameLength_of_length_eq
            (by simp [Sequences.List.length, h_len])
        have hlist_eq :
            Sequences.List.firstElement da das =
            Sequences.List.firstElement db dbs :=
          toPeanoList_inj_sameLength hsl heq_raw
        exact Subtype.ext hlist_eq

theorem equivalent_of_toPeano_eq {a b : Decimal} (h : a.toPeano = b.toPeano) :
    a ≈ b := by
  show a.normalize = b.normalize
  have ha_norm : toPeano a.normalize = toPeano a := normalize_toPeano a
  have hb_norm : toPeano b.normalize = toPeano b := normalize_toPeano b
  have h_norm : toPeano a.normalize = toPeano b.normalize := by
    rw [ha_norm, hb_norm, h]
  exact normalize_inj (normalize_isNormalized a) (normalize_isNormalized b) h_norm

theorem fromPeano_toPeano (x : Decimal) : fromPeano (toPeano x) ≈ x := by
  apply equivalent_of_toPeano_eq
  exact toPeano_fromPeano (toPeano x)

end Decimal

end ZeroMath.Numbers.CardinalNatural
