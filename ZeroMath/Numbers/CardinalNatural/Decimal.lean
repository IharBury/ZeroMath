import ZeroMath.Numbers.CardinalNatural.Peano
import ZeroMath.Numbers.Digits.Decimal
import ZeroMath.Numbers.Digits.Decimal.Lists
import ZeroMath.Numbers.OrdinalNatural.Decimal
import ZeroMath.Sequences.List

namespace ZeroMath.Numbers.CardinalNatural

namespace Decimal

abbrev Digit := Digits.Decimal

end Decimal

def Decimal := Digits.NonEmptyList

namespace Decimal

instance : DecidableEq Decimal :=
  fun x y =>
    if h : x.val = y.val then
      isTrue (Subtype.ext h)
    else
      isFalse (fun h' => h (congrArg Subtype.val h'))

export Digits (
  zeroDigit oneDigit twoDigit threeDigit fourDigit
  fiveDigit sixDigit sevenDigit eightDigit nineDigit
  DigitIsNonZero
  digit_val_successor_le_ten digit_val_le_ten digit_val_eq_nine_of_not_successor_lt_ten
  subtract_ten_lt_ten digit_sum_lt_twenty digit_carry_lt_twenty digit_cases
  successorList predecessorList subtractAlignedLists HasNonZero AllZero decidableAllZero
  allZero_of_predecessorList_borrow_true successorList_predecessorList
  successorList_ne_empty_of_carry_false predecessorList_ne_empty_of_borrow_false
  hasNonZero_ne_empty hasNonZero hasNonZero_tail_of_zero_first NonEmptyList
  normalizeList_eq_empty_of_allZero normalizeList_ne_empty_or_allZero)

def zero : Decimal := ⟨Sequences.List.firstElement zeroDigit Sequences.List.empty, by simp⟩
def one : Decimal := ⟨Sequences.List.firstElement oneDigit Sequences.List.empty, by simp⟩

def isNormalized (d : Decimal) : Bool :=
  match d with
  | ⟨.empty, _⟩ => by contradiction
  | ⟨.firstElement digit .empty, _⟩ => true
  | ⟨.firstElement digit _, _⟩ => decide (digit.val ≠ CardinalNatural.Peano.zero)

/-- Strip leading zeros; empty/all-zero becomes `zero`. -/
def normalizeList (a : Sequences.List Digit) : Decimal :=
  match Digits.normalizeList a with
  | .empty => zero
  | .firstElement d ds => ⟨Sequences.List.firstElement d ds, by simp⟩

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
      by_cases hd : d.val = CardinalNatural.Peano.zero
      · have hnorm : normalizeList (Sequences.List.firstElement d ds) = normalizeList ds := by
          simp [normalizeList, Digits.normalizeList, hd]
        rw [hnorm, ih]
        change toPeanoList ds Peano.zero =
          toPeanoList ds (Peano.zero * Peano.ten + d.val)
        rw [hd, Peano.zero_multiply, Peano.add_zero]
      · have hnorm : normalizeList (Sequences.List.firstElement d ds) =
            ⟨Sequences.List.firstElement d ds, by simp⟩ := by
          simp [normalizeList, Digits.normalizeList, hd]
        rw [hnorm]
        rfl

theorem normalize_toPeano (x : Decimal) : x.normalize.toPeano = x.toPeano := by
  unfold normalize toPeano
  exact normalizeList_toPeano x.val

theorem normalizeList_isNormalized (a : Sequences.List Digit) :
  isNormalized (normalizeList a) = true := by
  induction a with
  | empty =>
      rfl
  | firstElement d ds ih =>
      by_cases hd : d.val = CardinalNatural.Peano.zero
      · have hnorm : normalizeList (Sequences.List.firstElement d ds) = normalizeList ds := by
          simp [normalizeList, Digits.normalizeList, hd]
        rw [hnorm]
        exact ih
      · have hnorm : normalizeList (Sequences.List.firstElement d ds) =
            ⟨Sequences.List.firstElement d ds, by simp⟩ := by
          simp [normalizeList, Digits.normalizeList, hd]
        rw [hnorm]
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

theorem normalizeList_eq_zero_of_allZero {a : Sequences.List Digit} (h : AllZero a) :
  normalizeList a = zero := by
  simp [normalizeList, Digits.normalizeList_eq_empty_of_allZero h]

theorem equivalent_zero_of_allZero {a : Sequences.List Digit}
  (ha : a ≠ Sequences.List.empty) (h : AllZero a) :
  Equivalent ⟨a, ha⟩ zero := by
  unfold Equivalent normalize
  exact normalizeList_eq_zero_of_allZero h

def predecessor (a : Decimal) (h : ¬ a ≈ zero) : Decimal :=
  match h_result : predecessorList a.val with
  | ⟨_, true⟩ =>
      False.elim (h (equivalent_zero_of_allZero a.property
        (allZero_of_predecessorList_borrow_true h_result)))
  | ⟨digits, false⟩ =>
      ⟨digits, predecessorList_ne_empty_of_borrow_false a.property h_result⟩

theorem successor_predecessor (d : Decimal) (h : ¬ d ≈ zero) :
  (d.predecessor h).successor = d := by
  cases h_predecessor : predecessorList d.val with
  | mk digits borrow =>
      cases borrow with
      | true =>
          exact False.elim (h (equivalent_zero_of_allZero d.property
            (allZero_of_predecessorList_borrow_true h_predecessor)))
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
  induction hsl using Sequences.List.SameLength.induction with
  | empty => rfl
  | firstElement h_tail ih =>
    rename_i d1 d2 ds1 ds2
    simp only [toPeanoList, Peano.zero_multiply, Peano.zero_add] at heq
    rw [toPeanoList_acc_split ds1 d1.val,
        toPeanoList_acc_split ds2 d2.val] at heq
    have h_len : ds2.length = ds1.length :=
      h_tail.symm
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
          Sequences.List.sameLength_firstElement h_len
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

theorem toPeano_ne_zero_of_not_equivalent_zero {x : Decimal} (h : ¬ x ≈ zero) :
  x.toPeano ≠ Peano.zero := by
  intro heq
  exact h (equivalent_of_toPeano_eq (heq.trans toPeano_zero.symm))

theorem predecessor_toPeano (x : Decimal) (h : ¬ x ≈ zero) :
  ∃ h2, toPeano (x.predecessor h) = x.toPeano.predecessor h2 := by
  let y := toPeano (x.predecessor h)
  have h_successor : x.toPeano = Peano.successor y := by
    rw [← successor_toPeano (x.predecessor h)]
    exact congrArg toPeano (successor_predecessor x h).symm
  have hx_ne : x.toPeano ≠ Peano.zero := toPeano_ne_zero_of_not_equivalent_zero h
  cases h_toPeano : x.toPeano with
  | zero =>
      exact False.elim (hx_ne h_toPeano)
  | successor p =>
      exists Peano.successor_ne_zero p
      have h_y : y = p := by
        rw [h_toPeano] at h_successor
        injection h_successor with h_p
        exact h_p.symm
      exact h_y

theorem toPeano_eq_of_equivalent {a b : Decimal} (h : a ≈ b) :
  a.toPeano = b.toPeano := by
  have h_eq : a.normalize = b.normalize := h
  rw [← normalize_toPeano a, ← normalize_toPeano b, h_eq]

theorem peano_predecessor_congr {a b : Peano}
  (ha : a ≠ Peano.zero) (hb : b ≠ Peano.zero)
  (h_eq : a = b) : a.predecessor ha = b.predecessor hb := by
  cases h_eq
  rfl

theorem successor_ne_zero (x : Decimal) : ¬ x.successor ≈ zero := by
  intro h_zero
  have h_toPeano := toPeano_eq_of_equivalent h_zero
  rw [successor_toPeano, toPeano_zero] at h_toPeano
  exact (Peano.successor_ne_zero x.toPeano) h_toPeano

theorem predecessor_successor (x : Decimal) :
  ∃ h, predecessor x.successor h ≈ x := by
  have h : ¬ x.successor ≈ zero := successor_ne_zero x
  refine ⟨h, ?_⟩
  apply equivalent_of_toPeano_eq
  obtain ⟨h2, h_predecessor_toPeano⟩ := predecessor_toPeano x.successor h
  have h_successor_toPeano : x.successor.toPeano = x.toPeano.successor := successor_toPeano x
  have h2' : x.toPeano.successor ≠ Peano.zero := by
    intro h_zero
    exact h2 (h_successor_toPeano.trans h_zero)
  have h_predecessor_toPeano' :
      (predecessor x.successor h).toPeano = (x.toPeano.successor).predecessor h2' := by
    exact h_predecessor_toPeano.trans (peano_predecessor_congr h2 h2' h_successor_toPeano)
  obtain ⟨h3, h_predecessor_successor⟩ := Peano.predecessor_successor x.toPeano
  have h_predecessor_congr :
      (x.toPeano.successor).predecessor h2' = (x.toPeano.successor).predecessor h3 :=
    peano_predecessor_congr h2' h3 rfl
  exact h_predecessor_toPeano'.trans (h_predecessor_congr.trans h_predecessor_successor)

def LessThanAlignedLists (x y : Sequences.List Digit)
  (h : Sequences.List.SameLength x y) : Prop :=
  match x, y with
  | .empty, .empty => False
  | .firstElement d1 ds1, .firstElement d2 ds2 =>
      d1.val < d2.val ∨
        (d1.val = d2.val ∧ LessThanAlignedLists ds1 ds2 (Sequences.List.sameLength_of_firstElement h))
  | .empty, .firstElement _ _ => False.elim (by cases h)
  | .firstElement _ _, .empty => False.elim (by cases h)

def isLessThanAlignedLists (x y : Sequences.List Digit)
  (h : Sequences.List.SameLength x y) : Bool :=
  match x, y with
  | .empty, .empty => false
  | .firstElement dx dxs, .firstElement dy dys =>
      if _ : Peano.isLessThan dx.val dy.val then
        true
      else if _ : Peano.isLessThan dy.val dx.val then
        false
      else
        isLessThanAlignedLists dxs dys (Sequences.List.sameLength_of_firstElement h)
  | .empty, .firstElement _ _ => False.elim (by cases h)
  | .firstElement _ _, .empty => False.elim (by cases h)

theorem isLessThanAlignedLists_iff_lessThanAlignedLists (x y : Sequences.List Digit)
  (h : Sequences.List.SameLength x y) :
  isLessThanAlignedLists x y h ↔ LessThanAlignedLists x y h := by
  induction h using Sequences.List.SameLength.induction with
  | empty =>
      simp [isLessThanAlignedLists, LessThanAlignedLists]
  | firstElement htail ih =>
      rename_i dx dy dxs dys
      unfold isLessThanAlignedLists LessThanAlignedLists
      split
      · next h_dx_lt_dy_bool =>
          constructor
          · intro _
            exact Or.inl ((Peano.isLessThan_eq_true_iff_lt _ _).mp h_dx_lt_dy_bool)
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
                  (Peano.isLessThan_eq_false_iff_not_lt _ _).mp
                    (eq_false_of_ne_true h_not_dx_lt_dy_bool)
                have h_dy_lt_dx : dy.val < dx.val :=
                  (Peano.isLessThan_eq_true_iff_lt _ _).mp h_dy_lt_dx_bool
                cases h_less with
                | inl h_dx_lt_dy =>
                    exact False.elim (h_not_dx_lt_dy h_dx_lt_dy)
                | inr h_eq_tail =>
                    obtain ⟨h_dx_eq_dy, _⟩ := h_eq_tail
                    rw [h_dx_eq_dy] at h_dy_lt_dx
                    exact False.elim (Peano.not_lt_self dy.val h_dy_lt_dx)
          · next h_not_dy_lt_dx_bool =>
              have h_not_dx_lt_dy : ¬ dx.val < dy.val :=
                (Peano.isLessThan_eq_false_iff_not_lt _ _).mp
                  (eq_false_of_ne_true h_not_dx_lt_dy_bool)
              have h_not_dy_lt_dx : ¬ dy.val < dx.val :=
                (Peano.isLessThan_eq_false_iff_not_lt _ _).mp
                  (eq_false_of_ne_true h_not_dy_lt_dx_bool)
              have h_dx_eq_dy : dx.val = dy.val := by
                cases Peano.trichotomy_or dx.val dy.val with
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

def isLessThan (x y : Decimal) : Bool :=
  let pair := Sequences.List.padAtStartToSameLength x.val y.val zeroDigit
  isLessThanAlignedLists pair.1 pair.2
    (Sequences.List.padAtStartToSameLength_sameLength x.val y.val zeroDigit)

theorem toPeanoList_padAtStart_zeroDigit (l : Sequences.List Digit)
  (n : Peano) :
  toPeanoList (Sequences.List.padAtStart l zeroDigit n) Peano.zero =
    toPeanoList l Peano.zero := by
  induction n generalizing l with
  | zero => rfl
  | successor n ih =>
      unfold Sequences.List.padAtStart
      rw [ih]
      rfl

theorem toPeanoList_padAtStartToSameLength_fst (a b : Sequences.List Digit) :
  toPeanoList (Sequences.List.padAtStartToSameLength a b zeroDigit).1 Peano.zero =
    toPeanoList a Peano.zero := by
  unfold Sequences.List.padAtStartToSameLength
  dsimp only
  split
  · rfl
  · exact toPeanoList_padAtStart_zeroDigit _ _

theorem toPeanoList_padAtStartToSameLength_snd (a b : Sequences.List Digit) :
  toPeanoList (Sequences.List.padAtStartToSameLength a b zeroDigit).2 Peano.zero =
    toPeanoList b Peano.zero := by
  unfold Sequences.List.padAtStartToSameLength
  dsimp only
  split
  · exact toPeanoList_padAtStart_zeroDigit _ _
  · rfl

theorem LessThanAlignedLists_toPeanoList_lt {x y : Sequences.List Digit}
    (h : Sequences.List.SameLength x y)
    (hlt : LessThanAlignedLists x y h) :
    toPeanoList x Peano.zero < toPeanoList y Peano.zero := by
  induction h using Sequences.List.SameLength.induction with
  | empty =>
      cases hlt
  | firstElement htail ih =>
      rename_i dx dy dxs dys
      simp only [toPeanoList_firstElement]
      cases hlt with
      | inl h_digit =>
          have h_tail_lt : toPeanoList dxs Peano.zero < Peano.tenPow dxs.length :=
            toPeanoList_lt_tenPow dxs
          have h_lt_next :
              dx.val * Peano.tenPow dxs.length + toPeanoList dxs Peano.zero <
              dx.val * Peano.tenPow dxs.length + Peano.tenPow dxs.length :=
            Peano.add_lt_add_left h_tail_lt _
          have h_next_eq :
              dx.val * Peano.tenPow dxs.length + Peano.tenPow dxs.length =
              dx.val.successor * Peano.tenPow dxs.length :=
            (Peano.successor_multiply dx.val _).symm
          rw [h_next_eq] at h_lt_next
          have h_le_digit :
              dx.val.successor * Peano.tenPow dxs.length ≤
                dy.val * Peano.tenPow dxs.length :=
            Peano.multiply_le_mul_left (Peano.succ_le_of_lt h_digit) _
          have h_le_value :
              dy.val * Peano.tenPow dxs.length ≤
                dy.val * Peano.tenPow dxs.length + toPeanoList dys Peano.zero :=
            Peano.le_add_self_left _ _
          rw [← htail]
          exact Peano.lt_of_lt_of_le h_lt_next
            (Peano.le_trans h_le_digit h_le_value)
      | inr h_eq_tail =>
          obtain ⟨h_digit_eq, h_tail_lt_aligned⟩ := h_eq_tail
          rw [h_digit_eq, htail]
          exact Peano.add_lt_add_left (ih h_tail_lt_aligned) _

theorem LessThanAlignedLists_of_toPeanoList_lt {x y : Sequences.List Digit}
    (h : Sequences.List.SameLength x y)
    (hlt : toPeanoList x Peano.zero < toPeanoList y Peano.zero) :
    LessThanAlignedLists x y h := by
  induction h using Sequences.List.SameLength.induction with
  | empty =>
      exact False.elim (Peano.not_lt_self _ hlt)
  | firstElement htail ih =>
      rename_i dx dy dxs dys
      simp only [toPeanoList_firstElement] at hlt
      rw [htail] at hlt
      cases Peano.trichotomy_or dx.val dy.val with
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
                    dy.val * Peano.tenPow dys.length + toPeanoList dxs Peano.zero <
                    dy.val * Peano.tenPow dys.length + toPeanoList dys Peano.zero := by
                  rwa [h_digit_eq] at hlt
                rw [Peano.add_commutative (dy.val * Peano.tenPow dys.length),
                    Peano.add_commutative (dy.val * Peano.tenPow dys.length)] at hlt_tail_sum
                exact Peano.add_lt_cancel_right hlt_tail_sum
          | inr h_digit_gt =>
              have h_tail_y_lt : toPeanoList dys Peano.zero < Peano.tenPow dys.length :=
                toPeanoList_lt_tenPow dys
              have h_y_lt_next :
                  dy.val * Peano.tenPow dys.length + toPeanoList dys Peano.zero <
                  dy.val * Peano.tenPow dys.length + Peano.tenPow dys.length :=
                Peano.add_lt_add_left h_tail_y_lt _
              have h_next_eq :
                  dy.val * Peano.tenPow dys.length + Peano.tenPow dys.length =
                  dy.val.successor * Peano.tenPow dys.length :=
                (Peano.successor_multiply dy.val _).symm
              rw [h_next_eq] at h_y_lt_next
              have h_le_digit :
                  dy.val.successor * Peano.tenPow dys.length ≤
                    dx.val * Peano.tenPow dys.length :=
                Peano.multiply_le_mul_left (Peano.succ_le_of_lt h_digit_gt) _
              have h_le_x :
                  dx.val * Peano.tenPow dys.length ≤
                    dx.val * Peano.tenPow dys.length + toPeanoList dxs Peano.zero :=
                Peano.le_add_self_left _ _
              have h_y_lt_x :
                  dy.val * Peano.tenPow dys.length + toPeanoList dys Peano.zero <
                  dx.val * Peano.tenPow dys.length + toPeanoList dxs Peano.zero :=
                Peano.lt_of_lt_of_le h_y_lt_next
                  (Peano.le_trans h_le_digit h_le_x)
              exact False.elim (Peano.not_lt_self _ (Peano.lt_trans hlt h_y_lt_x))

def LessThan (x y : Decimal) : Prop :=
  x.toPeano < y.toPeano

theorem toPeano_lt_of_lessThanAlignedLists_padded {a b : Decimal}
    (h : LessThanAlignedLists
      (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).1
      (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).2
      (Sequences.List.padAtStartToSameLength_sameLength a.val b.val zeroDigit)) :
    a.toPeano < b.toPeano := by
  have h_padded := LessThanAlignedLists_toPeanoList_lt
    (Sequences.List.padAtStartToSameLength_sameLength a.val b.val zeroDigit) h
  change toPeanoList a.val Peano.zero < toPeanoList b.val Peano.zero
  rw [← toPeanoList_padAtStartToSameLength_fst a.val b.val,
    ← toPeanoList_padAtStartToSameLength_snd a.val b.val]
  exact h_padded

theorem lessThanAlignedLists_padded_of_toPeano_lt {a b : Decimal}
    (h : a.toPeano < b.toPeano) :
    LessThanAlignedLists
      (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).1
      (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).2
      (Sequences.List.padAtStartToSameLength_sameLength a.val b.val zeroDigit) := by
  apply LessThanAlignedLists_of_toPeanoList_lt
  change toPeanoList (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).1
      Peano.zero <
    toPeanoList (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).2
      Peano.zero
  rw [toPeanoList_padAtStartToSameLength_fst a.val b.val,
    toPeanoList_padAtStartToSameLength_snd a.val b.val]
  exact h

theorem isLessThan_iff_lessThan (x y : Decimal) :
  isLessThan x y ↔ LessThan x y := by
  unfold isLessThan LessThan
  dsimp only
  constructor
  · intro h
    have h_aligned := (isLessThanAlignedLists_iff_lessThanAlignedLists _ _ _).mp h
    exact toPeano_lt_of_lessThanAlignedLists_padded h_aligned
  · intro h
    exact (isLessThanAlignedLists_iff_lessThanAlignedLists _ _ _).mpr
      (lessThanAlignedLists_padded_of_toPeano_lt h)

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

instance (x y : Decimal) : Decidable (x ≤ y) :=
  if h_lt : x < y then
    isTrue (Or.inl h_lt)
  else if h_eq : x ≈ y then
    isTrue (Or.inr h_eq)
  else
    isFalse (fun h => match h with
      | Or.inl h_lt' => h_lt h_lt'
      | Or.inr h_eq' => h_eq h_eq')

theorem lt_trans {x y z : Decimal} (h1 : x < y) (h2 : y < z) : x < z :=
  Peano.lt_trans h1 h2

theorem not_lt_self (a : Decimal) : ¬ (a < a) := by
  intro h
  exact Peano.not_lt_self a.toPeano h

theorem not_equivalent_of_lt {a b : Decimal} (h : a < b) : ¬ (a ≈ b) := by
  intro heq
  have hlt : a.toPeano < b.toPeano := h
  rw [toPeano_eq_of_equivalent heq] at hlt
  exact Peano.not_lt_self b.toPeano hlt

theorem not_lt_of_lt {a b : Decimal} (h : a < b) : ¬ (b < a) := fun hba =>
  not_lt_self a (lt_trans h hba)

theorem trichotomy_or (a b : Decimal) : a < b ∨ a ≈ b ∨ b < a := by
  cases Peano.trichotomy_or a.toPeano b.toPeano with
  | inl h =>
      exact Or.inl h
  | inr h =>
      cases h with
      | inl heq =>
          exact Or.inr (Or.inl (equivalent_of_toPeano_eq heq))
      | inr hgt =>
          exact Or.inr (Or.inr hgt)

theorem trichotomy (a b : Decimal) :
    ZeroMath.Logic.Trichotomy (a < b) (a ≈ b) (b < a) := by
  cases trichotomy_or a b with
  | inl h =>
      exact ZeroMath.Logic.Trichotomy.first h (not_equivalent_of_lt h) (not_lt_of_lt h)
  | inr h =>
      cases h with
      | inl heq =>
          exact ZeroMath.Logic.Trichotomy.second heq
            (fun hlt => not_equivalent_of_lt hlt heq)
            (fun hlt => not_equivalent_of_lt hlt heq.symm)
      | inr hgt =>
          exact ZeroMath.Logic.Trichotomy.third hgt (not_lt_of_lt hgt)
            (fun heq => not_equivalent_of_lt hgt heq.symm)

/-- Result of comparing two Decimal numbers, packaged with a proof of the relationship. -/
inductive Comparison (a b : Decimal) where
  | less : a < b → Comparison a b
  | equivalent : a ≈ b → Comparison a b
  | greater : b < a → Comparison a b

/-- Compare two Decimal numbers, returning less, equivalent, or greater together with a proof. -/
def compare (a b : Decimal) : Comparison a b :=
  match Peano.compare a.toPeano b.toPeano with
  | Peano.Comparison.less h => Comparison.less h
  | Peano.Comparison.equal h => Comparison.equivalent (equivalent_of_toPeano_eq h)
  | Peano.Comparison.greater h => Comparison.greater h

theorem le_trans {a b c : Decimal} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  cases h1 with
  | inl hlt1 =>
      cases h2 with
      | inl hlt2 => exact Or.inl (lt_trans hlt1 hlt2)
      | inr heq2 =>
          apply Or.inl
          change a.toPeano < c.toPeano
          rw [← toPeano_eq_of_equivalent heq2]
          exact hlt1
  | inr heq1 =>
      cases h2 with
      | inl hlt2 =>
          apply Or.inl
          change a.toPeano < c.toPeano
          rw [toPeano_eq_of_equivalent heq1]
          exact hlt2
      | inr heq2 =>
          exact Or.inr (Setoid.trans heq1 heq2)

/-- Inequality is preserved when the right side is replaced by an equivalent
Decimal. -/
theorem le_of_le_of_equivalent {a b c : Decimal}
    (hab : a ≤ b) (hbc : b ≈ c) : a ≤ c :=
  le_trans hab (Or.inr hbc)

def addAlignedLists (a b : Sequences.List Digit) (h : Sequences.List.SameLength a b) :
  Sequences.List Digit × Bool :=
  match a, b with
  | .empty, .empty => ⟨Sequences.List.empty, false⟩
  | .firstElement da das, .firstElement db dbs =>
    let ⟨digits, carry⟩ := addAlignedLists das dbs (Sequences.List.sameLength_of_firstElement h)
    let digit_sum := da.val + db.val + (if carry then CardinalNatural.Peano.one else CardinalNatural.Peano.zero)
    if h2 : CardinalNatural.Peano.isLessThan digit_sum CardinalNatural.Peano.ten then
      ⟨Sequences.List.firstElement ⟨digit_sum, (CardinalNatural.Peano.isLessThan_eq_true_iff_lt _ _).mp h2⟩ digits, false⟩
    else
      have h_le : CardinalNatural.Peano.ten ≤ digit_sum :=
        CardinalNatural.Peano.isLessThan_false_implies_le (eq_false_of_ne_true h2)
      have h_lt_twenty : digit_sum < CardinalNatural.Peano.ten + CardinalNatural.Peano.ten :=
        digit_sum_lt_twenty da.val db.val carry da.property db.property
      ⟨Sequences.List.firstElement
        ⟨CardinalNatural.Peano.subtract digit_sum CardinalNatural.Peano.ten h_le,
          subtract_ten_lt_ten digit_sum h_le h_lt_twenty⟩
        digits, true⟩
  | .empty, .firstElement _ _ => False.elim (by cases h)
  | .firstElement _ _, .empty => False.elim (by cases h)

theorem addAlignedLists_commutative (a b : Sequences.List Digit)
  (h : Sequences.List.SameLength a b) :
  addAlignedLists a b h = addAlignedLists b a (Sequences.List.sameLength_commutative h) := by
  induction h using Sequences.List.SameLength.induction with
  | empty => rfl
  | firstElement htail ih =>
      unfold addAlignedLists
      rw [ih]
      simp only [CardinalNatural.Peano.add_commutative]

theorem padAtStart_ne_empty {α : Type} {l : Sequences.List α}
  (hl : l ≠ Sequences.List.empty) (paddingValue : α) (n : CardinalNatural.Peano) :
  Sequences.List.padAtStart l paddingValue n ≠ Sequences.List.empty := by
  induction n generalizing l with
  | zero =>
      exact hl
  | successor n ih =>
      unfold Sequences.List.padAtStart
      exact ih (by simp)

theorem padAtStartToSameLength_fst_ne_empty (a b : Sequences.List Digit) (paddingValue : Digit)
  (ha : a ≠ Sequences.List.empty) :
  (Sequences.List.padAtStartToSameLength a b paddingValue).1 ≠ Sequences.List.empty := by
  unfold Sequences.List.padAtStartToSameLength
  dsimp only
  split
  · exact ha
  · exact padAtStart_ne_empty ha paddingValue _

theorem addAlignedLists_fst_ne_empty {a b : Sequences.List Digit}
  (h : Sequences.List.SameLength a b) (ha : a ≠ Sequences.List.empty) :
  (addAlignedLists a b h).1 ≠ Sequences.List.empty := by
  match a, b with
  | .empty, .empty =>
      exact False.elim (ha rfl)
  | .firstElement da das, .firstElement db dbs =>
      unfold addAlignedLists
      dsimp
      split
      · split
        · intro h_empty
          cases h_empty
        · intro h_empty
          cases h_empty
      · split
        · intro h_empty
          cases h_empty
        · intro h_empty
          cases h_empty
  | .empty, .firstElement _ _ => cases h
  | .firstElement _ _, .empty => cases h

theorem addAlignedLists_ne_empty {a b digits : Sequences.List Digit} {carry : Bool}
  (h : Sequences.List.SameLength a b) (ha : a ≠ Sequences.List.empty)
  (h_add : addAlignedLists a b h = ⟨digits, carry⟩) :
  digits ≠ Sequences.List.empty := by
  have h_fst := addAlignedLists_fst_ne_empty h ha
  rw [h_add] at h_fst
  exact h_fst

def add (a b : Decimal) : Decimal :=
  let pair := Sequences.List.padAtStartToSameLength a.val b.val zeroDigit
  let h_same : Sequences.List.SameLength pair.1 pair.2 :=
    Sequences.List.padAtStartToSameLength_sameLength a.val b.val zeroDigit
  match h_add : addAlignedLists pair.1 pair.2 h_same with
  | ⟨digits, true⟩ =>
      ⟨Sequences.List.firstElement ⟨CardinalNatural.Peano.one, CardinalNatural.Peano.one_lt_ten⟩ digits, by simp⟩
  | ⟨digits, false⟩ =>
      ⟨digits, addAlignedLists_ne_empty h_same
        (padAtStartToSameLength_fst_ne_empty a.val b.val zeroDigit a.property) h_add⟩

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

theorem addAlignedLists_spec {a b : Sequences.List Digit}
  (h : Sequences.List.SameLength a b) :
  let result := addAlignedLists a b h
  result.1.length = a.length ∧
    toPeanoList result.1 Peano.zero +
        (if result.2 then Peano.tenPow a.length else Peano.zero) =
      toPeanoList a Peano.zero +
        toPeanoList b Peano.zero := by
  induction h using Sequences.List.SameLength.induction with
  | empty =>
      simp [addAlignedLists, toPeanoList, Sequences.List.length]
  | @firstElement da db das dbs htail ih =>
      unfold addAlignedLists
      dsimp only
      cases h_rec : addAlignedLists das dbs htail with
      | mk digits carry =>
          rw [h_rec] at ih
          dsimp only at ih
          obtain ⟨h_length, ih_value⟩ := ih
          have h_tail_lengths := htail
          cases carry with
          | false =>
              simp at ih_value ⊢
              split
              · constructor
                · simp [Sequences.List.length, h_length]
                · simp only [toPeanoList_firstElement]
                  simp only [if_neg Bool.false_ne_true]
                  rw [h_length, ← h_tail_lengths]
                  rw [Peano.multiply_distributive_over_add_left, ih_value]
                  simp
                  simp only [Peano.add_associative, Peano.add_left_commutative]
              · constructor
                · simp [Sequences.List.length, h_length]
                · simp only [toPeanoList_firstElement, Sequences.List.length,
                    Peano.tenPow_add_one]
                  rw [h_length, ← h_tail_lengths]
                  have h_digit := Peano.subtract_add_cancel
                    (da.val + db.val) Peano.ten
                    (Peano.isLessThan_false_implies_le (eq_false_of_ne_true ‹_›))
                  simp only [if_true]
                  calc
                    _ = (Peano.subtract
                            (da.val + db.val)
                            Peano.ten _ + Peano.ten) *
                          Peano.tenPow das.length +
                        toPeanoList digits Peano.zero := by
                          rw [Peano.multiply_distributive_over_add_left]
                          rw [Peano.add_associative,
                            Peano.add_commutative
                              (toPeanoList digits Peano.zero)
                              (Peano.ten * Peano.tenPow das.length),
                            ← Peano.add_associative]
                    _ = _ := by
                      rw [h_digit, Peano.multiply_distributive_over_add_left, ih_value]
                      simp only [Peano.add_associative,
                        Peano.add_left_commutative]
          | true =>
              simp at ih_value ⊢
              split
              · constructor
                · simp [Sequences.List.length, h_length]
                · simp only [toPeanoList_firstElement]
                  simp only [if_neg Bool.false_ne_true]
                  rw [h_length, ← h_tail_lengths]
                  rw [Peano.multiply_distributive_over_add_left]
                  rw [Peano.multiply_distributive_over_add_left]
                  rw [Peano.one_multiply]
                  calc
                    _ = da.val * Peano.tenPow das.length +
                          db.val * Peano.tenPow das.length +
                          (toPeanoList digits Peano.zero +
                            Peano.tenPow das.length) := by
                              simp
                              simp only [Peano.add_associative,
                                Peano.add_commutative]
                    _ = _ := by rw [ih_value]; simp only [Peano.add_associative,
                      Peano.add_left_commutative]
              · constructor
                · simp [Sequences.List.length, h_length]
                · simp only [toPeanoList_firstElement, Sequences.List.length,
                    Peano.tenPow_add_one]
                  rw [h_length, ← h_tail_lengths]
                  have h_digit := Peano.subtract_add_cancel
                    (da.val + db.val + Peano.one) Peano.ten
                    (Peano.isLessThan_false_implies_le (eq_false_of_ne_true ‹_›))
                  simp only [if_true]
                  calc
                    _ = (Peano.subtract
                            (da.val + db.val + Peano.one)
                            Peano.ten _ + Peano.ten) *
                          Peano.tenPow das.length +
                        toPeanoList digits Peano.zero := by
                          rw [Peano.multiply_distributive_over_add_left]
                          simp only [Peano.add_commutative,
                            Peano.add_left_commutative]
                    _ = _ := by
                      rw [h_digit, Peano.multiply_distributive_over_add_left,
                        Peano.multiply_distributive_over_add_left,
                        Peano.one_multiply]
                      calc
                        _ = da.val * Peano.tenPow das.length +
                              db.val * Peano.tenPow das.length +
                              (toPeanoList digits Peano.zero +
                                Peano.tenPow das.length) := by simp only [
                                  Peano.add_associative,
                                  Peano.add_commutative]
                        _ = _ := by rw [ih_value]; simp only [Peano.add_associative,
                          Peano.add_left_commutative]

theorem add_toPeano (x y : Decimal) :
  (x + y).toPeano = x.toPeano + y.toPeano := by
  change toPeanoList (add x y).val Peano.zero =
    toPeanoList x.val Peano.zero +
      toPeanoList y.val Peano.zero
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
      change toPeanoList
        (Sequences.List.firstElement ⟨Peano.one, Peano.one_lt_ten⟩ digits)
        Peano.zero = _
      rw [toPeanoList_firstElement, h_length, Peano.one_multiply,
        Peano.add_commutative, h_value,
        toPeanoList_padAtStartToSameLength_fst,
        toPeanoList_padAtStartToSameLength_snd]
  · next digits h_add =>
      have h_spec := addAlignedLists_spec
        (Sequences.List.padAtStartToSameLength_sameLength x.val y.val zeroDigit)
      rw [h_add] at h_spec
      dsimp only at h_spec
      obtain ⟨_, h_value⟩ := h_spec
      simp at h_value
      rw [h_value, toPeanoList_padAtStartToSameLength_fst,
        toPeanoList_padAtStartToSameLength_snd]

theorem add_associative (a b c : Decimal) : a + b + c ≈ a + (b + c) := by
  apply equivalent_of_toPeano_eq
  rw [add_toPeano, add_toPeano, add_toPeano, add_toPeano, Peano.add_associative]

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
  have h_aligned := lessThanAlignedLists_padded_of_toPeano_lt h
  have hpad := Sequences.List.padAtStartToSameLength_commutative b.val a.val zeroDigit
  have h_fst := congrArg Prod.fst hpad
  have h_snd := congrArg Prod.snd hpad
  dsimp only at h_fst h_snd ⊢
  exact LessThanAlignedLists_congr _ _ h_snd.symm h_fst.symm h_aligned

theorem subtractAlignedLists_borrow_false_of_lessThan {a b : Sequences.List Digit}
  (h_same : Sequences.List.SameLength a b)
  (h_lt : LessThanAlignedLists b a (Sequences.List.sameLength_commutative h_same)) :
  (subtractAlignedLists a b h_same).2 = false := by
  induction h_same using Sequences.List.SameLength.induction with
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
                  have h_not : ¬ da.val < db.val := Peano.not_lt_of_lt h_db_lt_da
                  simp [h_not]
              | true =>
                  have h_not : ¬ da.val < db.val.successor :=
                    Peano.cardinal_not_lt_of_le (Peano.succ_le_of_lt h_db_lt_da)
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
                    exact Peano.not_lt_self db.val hlt
                  simp [h_not]
              | true =>
                  cases h_borrow

theorem subtractAlignedLists_fst_ne_empty {a b : Sequences.List Digit}
  (h : Sequences.List.SameLength a b) (ha : a ≠ Sequences.List.empty) :
  (subtractAlignedLists a b h).1 ≠ Sequences.List.empty := by
  match a, b with
  | .empty, .empty =>
      exact False.elim (ha rfl)
  | .firstElement da das, .firstElement db dbs =>
      unfold subtractAlignedLists
      dsimp
      split
      · split
        · intro h_empty
          cases h_empty
        · intro h_empty
          cases h_empty
      · split
        · intro h_empty
          cases h_empty
        · intro h_empty
          cases h_empty
  | .empty, .firstElement _ _ => cases h
  | .firstElement _ _, .empty => cases h

theorem subtractAlignedLists_ne_empty {a b digits : Sequences.List Digit} {borrow : Bool}
  (h : Sequences.List.SameLength a b) (ha : a ≠ Sequences.List.empty)
  (h_subtract : subtractAlignedLists a b h = ⟨digits, borrow⟩) :
  digits ≠ Sequences.List.empty := by
  have h_fst := subtractAlignedLists_fst_ne_empty h ha
  rw [h_subtract] at h_fst
  exact h_fst

theorem subtractAlignedLists_borrow_false_of_eq {a b : Sequences.List Digit}
  (h_same : Sequences.List.SameLength a b) (h_eq : a = b) :
  (subtractAlignedLists a b h_same).2 = false := by
  induction h_same using Sequences.List.SameLength.induction with
  | empty =>
      rfl
  | firstElement htail ih =>
      rename_i da db das dbs
      injection h_eq with h_digit h_tail
      subst db
      subst dbs
      unfold subtractAlignedLists
      cases h_rec : subtractAlignedLists das das htail with
      | mk digits borrow =>
          have h_borrow := ih rfl
          rw [h_rec] at h_borrow
          dsimp only at h_borrow
          cases borrow with
          | false =>
              have h_not : ¬ da.val < da.val := Peano.not_lt_self da.val
              simp [h_not]
          | true =>
              cases h_borrow

theorem padAtStartToSameLength_eq_of_equivalent {a b : Decimal} (h : a ≈ b) :
  (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).1 =
    (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).2 := by
  have heq :
      toPeanoList (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).1 Peano.zero =
        toPeanoList (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).2 Peano.zero := by
    rw [toPeanoList_padAtStartToSameLength_fst, toPeanoList_padAtStartToSameLength_snd]
    exact toPeano_eq_of_equivalent h
  exact toPeanoList_inj_sameLength
    (Sequences.List.padAtStartToSameLength_sameLength a.val b.val zeroDigit) heq

theorem subtractAlignedLists_borrow_false_of_equivalent {a b : Decimal} (h : a ≈ b) :
  (subtractAlignedLists
    (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).1
    (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).2
    (Sequences.List.padAtStartToSameLength_sameLength a.val b.val zeroDigit)).2 = false :=
  subtractAlignedLists_borrow_false_of_eq _
    (padAtStartToSameLength_eq_of_equivalent h)

theorem subtractAlignedLists_borrow_false_of_le {a b : Decimal} (h : b ≤ a) :
  (subtractAlignedLists
    (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).1
    (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).2
    (Sequences.List.padAtStartToSameLength_sameLength a.val b.val zeroDigit)).2 = false := by
  cases h with
  | inl hlt =>
      exact subtractAlignedLists_borrow_false_of_lessThan _
        (lessThanAlignedLists_padded_of_lt hlt)
  | inr heq =>
      exact subtractAlignedLists_borrow_false_of_equivalent heq.symm

def subtract (a b : Decimal) (h : b ≤ a) : Decimal :=
  let pair := Sequences.List.padAtStartToSameLength a.val b.val zeroDigit
  let h_same : Sequences.List.SameLength pair.1 pair.2 :=
    Sequences.List.padAtStartToSameLength_sameLength a.val b.val zeroDigit
  match h_subtract : Decimal.subtractAlignedLists pair.1 pair.2 h_same with
  | ⟨digits, borrow⟩ =>
      if h2 : borrow then
        False.elim (by
          have h_borrow_false := subtractAlignedLists_borrow_false_of_le h
          rw [h_subtract] at h_borrow_false
          dsimp only at h_borrow_false
          rw [h2] at h_borrow_false
          cases h_borrow_false)
      else
        ⟨digits, subtractAlignedLists_ne_empty h_same
          (padAtStartToSameLength_fst_ne_empty a.val b.val zeroDigit a.property) h_subtract⟩

theorem subtractAlignedLists_spec {a b : Sequences.List Digit}
  (h : Sequences.List.SameLength a b) :
  let result := subtractAlignedLists a b h
  result.1.length = a.length ∧
    toPeanoList result.1 Peano.zero +
        toPeanoList b Peano.zero =
      toPeanoList a Peano.zero +
        (if result.2 then Peano.tenPow a.length else Peano.zero) := by
  induction h using Sequences.List.SameLength.induction with
  | empty =>
      simp [subtractAlignedLists, toPeanoList, Sequences.List.length]
  | @firstElement da db das dbs htail ih =>
      unfold subtractAlignedLists
      dsimp only
      cases h_rec : subtractAlignedLists das dbs htail with
      | mk digits borrow =>
          rw [h_rec] at ih
          dsimp only at ih
          obtain ⟨h_length, ih_value⟩ := ih
          have h_tail_lengths := htail
          cases borrow with
          | false =>
              simp at ih_value ⊢
              split
              · next h_da_lt_db =>
                  constructor
                  · simp [Sequences.List.length, h_length]
                  · simp only [toPeanoList_firstElement, Sequences.List.length,
                      Peano.tenPow_add_one, if_true]
                    rw [h_length, ← h_tail_lengths]
                    have h_le : db.val ≤ da.val + Peano.ten := by
                      exact Peano.le_trans (digit_val_le_ten db)
                        (Peano.le_add_self_right da.val Peano.ten)
                    have h_digit := Peano.subtract_add_cancel
                      (da.val + Peano.ten) db.val h_le
                    calc
                      _ = (Peano.subtract (da.val + Peano.ten) db.val h_le + db.val) *
                            Peano.tenPow das.length +
                          (toPeanoList digits Peano.zero +
                            toPeanoList dbs Peano.zero) := by
                            rw [Peano.multiply_distributive_over_add_left]
                            exact Peano.add_pair_swap _ _ _ _
                      _ = (da.val + Peano.ten) * Peano.tenPow das.length +
                          toPeanoList das Peano.zero := by
                            rw [h_digit, ih_value]
                      _ = da.val * Peano.tenPow das.length +
                          toPeanoList das Peano.zero +
                            Peano.ten * Peano.tenPow das.length := by
                            rw [Peano.multiply_distributive_over_add_left]
                            exact Peano.add_right_commutative _ _ _
              · next h_not_lt =>
                  constructor
                  · simp [Sequences.List.length, h_length]
                  · simp only [toPeanoList_firstElement, Sequences.List.length]
                    simp only [if_neg Bool.false_ne_true]
                    rw [h_length, ← h_tail_lengths]
                    have h_le : db.val ≤ da.val := Peano.not_lt_implies_le h_not_lt
                    have h_digit := Peano.subtract_add_cancel da.val db.val h_le
                    calc
                      _ = (Peano.subtract da.val db.val h_le + db.val) *
                            Peano.tenPow das.length +
                          (toPeanoList digits Peano.zero +
                            toPeanoList dbs Peano.zero) := by
                            rw [Peano.multiply_distributive_over_add_left]
                            exact Peano.add_pair_swap _ _ _ _
                      _ = da.val * Peano.tenPow das.length +
                          toPeanoList das Peano.zero := by
                            rw [h_digit, ih_value]
                      _ = da.val * Peano.tenPow das.length +
                          toPeanoList das Peano.zero + Peano.zero := by
                            rw [Peano.add_zero]
          | true =>
              simp at ih_value ⊢
              split
              · next h_da_lt_db_succ =>
                  constructor
                  · simp [Sequences.List.length, h_length]
                  · simp only [toPeanoList_firstElement, Sequences.List.length,
                      Peano.tenPow_add_one, if_true]
                    rw [h_length, ← h_tail_lengths]
                    have h_le : db.val.successor ≤ da.val + Peano.ten := by
                      exact Peano.le_trans (digit_val_successor_le_ten db)
                        (Peano.le_add_self_right da.val Peano.ten)
                    have h_digit := Peano.subtract_add_cancel
                      (da.val + Peano.ten) db.val.successor h_le
                    calc
                      _ = (Peano.subtract (da.val + Peano.ten) db.val.successor h_le + db.val) *
                            Peano.tenPow das.length +
                          (toPeanoList digits Peano.zero +
                            toPeanoList dbs Peano.zero) := by
                            rw [Peano.multiply_distributive_over_add_left]
                            exact Peano.add_pair_swap _ _ _ _
                      _ = (Peano.subtract (da.val + Peano.ten) db.val.successor h_le + db.val) *
                            Peano.tenPow das.length +
                          (toPeanoList das Peano.zero +
                            Peano.tenPow das.length) := by
                            rw [ih_value]
                      _ = (Peano.subtract (da.val + Peano.ten) db.val.successor h_le + db.val).successor *
                            Peano.tenPow das.length +
                          toPeanoList das Peano.zero := by
                            rw [Peano.successor_multiply]
                            rw [Peano.add_commutative (toPeanoList das Peano.zero)
                              (Peano.tenPow das.length)]
                            rw [← Peano.add_associative]
                      _ = (da.val + Peano.ten) * Peano.tenPow das.length +
                          toPeanoList das Peano.zero := by
                            rw [← Peano.add_successor]
                            rw [h_digit]
                      _ = da.val * Peano.tenPow das.length +
                          toPeanoList das Peano.zero +
                            Peano.ten * Peano.tenPow das.length := by
                            rw [Peano.multiply_distributive_over_add_left]
                            exact Peano.add_right_commutative _ _ _
              · next h_not_lt =>
                  constructor
                  · simp [Sequences.List.length, h_length]
                  · simp only [toPeanoList_firstElement, Sequences.List.length]
                    simp only [if_neg Bool.false_ne_true]
                    rw [h_length, ← h_tail_lengths]
                    have h_le : db.val.successor ≤ da.val := Peano.not_lt_implies_le h_not_lt
                    have h_digit := Peano.subtract_add_cancel da.val db.val.successor h_le
                    calc
                      _ = (Peano.subtract da.val db.val.successor h_le + db.val) *
                            Peano.tenPow das.length +
                          (toPeanoList digits Peano.zero +
                            toPeanoList dbs Peano.zero) := by
                            rw [Peano.multiply_distributive_over_add_left]
                            exact Peano.add_pair_swap _ _ _ _
                      _ = (Peano.subtract da.val db.val.successor h_le + db.val) *
                            Peano.tenPow das.length +
                          (toPeanoList das Peano.zero +
                            Peano.tenPow das.length) := by
                            rw [ih_value]
                      _ = (Peano.subtract da.val db.val.successor h_le + db.val).successor *
                            Peano.tenPow das.length +
                          toPeanoList das Peano.zero := by
                            rw [Peano.successor_multiply]
                            exact Peano.add_right_swap _ _ _
                      _ = da.val * Peano.tenPow das.length +
                          toPeanoList das Peano.zero := by
                            rw [← Peano.add_successor]
                            rw [h_digit]
                      _ = da.val * Peano.tenPow das.length +
                          toPeanoList das Peano.zero + Peano.zero := by
                            rw [Peano.add_zero]

theorem toPeano_subtract (x y : Decimal) (h : y ≤ x) :
  toPeano (subtract x y h) + toPeano y = toPeano x := by
  change toPeanoList (subtract x y h).val Peano.zero +
      toPeanoList y.val Peano.zero =
    toPeanoList x.val Peano.zero
  unfold subtract
  dsimp only
  let pair := Sequences.List.padAtStartToSameLength x.val y.val zeroDigit
  let h_same : Sequences.List.SameLength pair.1 pair.2 :=
    Sequences.List.padAtStartToSameLength_sameLength x.val y.val zeroDigit
  by_cases h_borrow : (subtractAlignedLists pair.1 pair.2 h_same).2 = true
  · simp [pair, h_borrow]
    have h_borrow_false := subtractAlignedLists_borrow_false_of_le h
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
            rw [← toPeanoList_padAtStartToSameLength_fst x.val y.val,
              ← toPeanoList_padAtStartToSameLength_snd x.val y.val]
            change toPeanoList digits Peano.zero +
                toPeanoList pair.2 Peano.zero =
              toPeanoList pair.1 Peano.zero
            exact h_value
        | true =>
            rw [h_subtract] at h_borrow
            exact False.elim (h_borrow rfl)

theorem toPeano_le_of_le {a b : Decimal} (h : a ≤ b) : a.toPeano ≤ b.toPeano := by
  cases h with
  | inl hlt => exact Or.inl hlt
  | inr heq => exact Or.inr (toPeano_eq_of_equivalent heq)

theorem subtract_toPeano (x y : Decimal) (h : y ≤ x) :
  ∃ h2, toPeano (subtract x y h) = Peano.subtract x.toPeano y.toPeano h2 := by
  let h2 := toPeano_le_of_le h
  exists h2
  have h_decimal_add : toPeano (subtract x y h) + y.toPeano = x.toPeano :=
    toPeano_subtract x y h
  have h_peano_add : Peano.subtract x.toPeano y.toPeano h2 + y.toPeano = x.toPeano :=
    Peano.subtract_add_cancel x.toPeano y.toPeano h2
  exact Peano.add_cancel_right (toPeano (subtract x y h))
    (Peano.subtract x.toPeano y.toPeano h2) y.toPeano
    (h_decimal_add.trans h_peano_add.symm)

theorem le_of_toPeano_le {a b : Decimal} (h : a.toPeano ≤ b.toPeano) : a ≤ b := by
  cases h with
  | inl hlt => exact Or.inl hlt
  | inr heq => exact Or.inr (equivalent_of_toPeano_eq heq)

theorem le_add_right (a b : Decimal) : b ≤ a + b := by
  apply le_of_toPeano_le
  rw [add_toPeano]
  exact Peano.le_add_self_right a.toPeano b.toPeano

theorem subtract_add_cancel (a b : Decimal) (h : b ≤ a) :
  subtract a b h + b ≈ a := by
  apply equivalent_of_toPeano_eq
  rw [add_toPeano, toPeano_subtract a b h]

theorem add_subtract_cancel (a b : Decimal) :
  ∃ h, subtract (a + b) b h ≈ a := by
  let h : b ≤ a + b := le_add_right a b
  refine ⟨h, ?_⟩
  apply equivalent_of_toPeano_eq
  apply Peano.add_cancel_right
    (toPeano (subtract (a + b) b h)) (toPeano a) (toPeano b)
  rw [toPeano_subtract (a + b) b h, add_toPeano]

theorem add_subtract_assoc (a b c : Decimal) (h : c ≤ b) :
  ∃ h2, subtract (a + b) c h2 ≈ a + subtract b c h := by
  have h2 : c ≤ a + b := le_trans h (le_add_right a b)
  refine ⟨h2, ?_⟩
  apply equivalent_of_toPeano_eq
  apply Peano.add_cancel_right
    (toPeano (subtract (a + b) c h2))
    (toPeano (a + subtract b c h))
    (toPeano c)
  rw [toPeano_subtract (a + b) c h2, add_toPeano]
  have h_right :
      toPeano a + toPeano b = toPeano (a + subtract b c h) + toPeano c := by
    rw [add_toPeano, Peano.add_associative, toPeano_subtract b c h]
  exact h_right

theorem subtract_subtract_assoc (a b c : Decimal) (h : b ≤ a) (h2 : c ≤ subtract a b h) :
  ∃ h3, subtract (subtract a b h) c h2 ≈ subtract a (b + c) h3 := by
  have h3 : b + c ≤ a := by
    apply le_of_toPeano_le
    have h_sub : toPeano c ≤ toPeano (subtract a b h) := toPeano_le_of_le h2
    have h_add : toPeano c + toPeano b ≤ toPeano (subtract a b h) + toPeano b :=
      Peano.add_le_add_right h_sub (toPeano b)
    rw [toPeano_subtract a b h] at h_add
    rw [add_toPeano, Peano.add_commutative (toPeano b) (toPeano c)]
    exact h_add
  refine ⟨h3, ?_⟩
  apply equivalent_of_toPeano_eq
  apply Peano.add_cancel_right
    (toPeano (subtract (subtract a b h) c h2))
    (toPeano (subtract a (b + c) h3))
    (toPeano (b + c))
  rw [toPeano_subtract a (b + c) h3, add_toPeano]
  rw [Peano.add_commutative (toPeano b) (toPeano c)]
  rw [← Peano.add_associative]
  rw [toPeano_subtract (subtract a b h) c h2]
  rw [toPeano_subtract a b h]

def subtractWithRemainder (a b : Decimal) : Decimal × Decimal :=
  let pair := Sequences.List.padAtStartToSameLength a.val b.val zeroDigit
  let h_same : Sequences.List.SameLength pair.1 pair.2 :=
    Sequences.List.padAtStartToSameLength_sameLength a.val b.val zeroDigit
  let subres := subtractAlignedLists pair.1 pair.2 h_same
  if h_borrow : subres.2 = true then
      let digits := subres.1
      have h_lt : a < b := by
        have h_ap : toPeano a = toPeanoList pair.1 Peano.zero := by
          unfold toPeano
          exact (toPeanoList_padAtStartToSameLength_fst a.val b.val).symm
        have h_bp : toPeano b = toPeanoList pair.2 Peano.zero := by
          unfold toPeano
          exact (toPeanoList_padAtStartToSameLength_snd a.val b.val).symm
        have h_d_lt : toPeanoList digits Peano.zero < Peano.tenPow pair.1.length := by
          have h_len : digits.length = pair.1.length := by
            have sp := subtractAlignedLists_spec h_same
            have h_call : subres = subtractAlignedLists pair.1 pair.2 h_same := rfl
            rw [← h_call] at sp
            simp [h_borrow] at sp
            obtain ⟨hlen, _⟩ := sp
            exact hlen
          have t := toPeanoList_lt_tenPow digits
          rw [h_len] at t
          exact t
        have h_list_lt : toPeanoList pair.1 Peano.zero <
            toPeanoList pair.2 Peano.zero := by
          have sp_val := (subtractAlignedLists_spec h_same).2
          have h_call : subres = subtractAlignedLists pair.1 pair.2 h_same := rfl
          rw [← h_call] at sp_val
          simp [h_borrow] at sp_val
          have ineq : toPeanoList pair.1 Peano.zero + Peano.tenPow pair.1.length <
                Peano.tenPow pair.1.length + toPeanoList pair.2 Peano.zero := by
            rw [← sp_val]
            exact Peano.add_lt_add_right h_d_lt _
          rw [Peano.add_commutative (Peano.tenPow _) _] at ineq
          exact Peano.add_lt_cancel_right ineq
        change a.toPeano < b.toPeano
        rw [h_ap, h_bp]
        exact h_list_lt
      ⟨zero, subtract b a (Or.inl h_lt)⟩
  else
      let digits := subres.1
      ⟨⟨digits, subtractAlignedLists_fst_ne_empty h_same
          (padAtStartToSameLength_fst_ne_empty a.val b.val zeroDigit a.property)⟩, zero⟩

theorem subtractAlignedLists_borrow_true_of_lessThan {a b : Decimal} (h : a < b) :
    (subtractAlignedLists
      (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).1
      (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).2
      (Sequences.List.padAtStartToSameLength_sameLength a.val b.val zeroDigit)).2 = true := by
  let h_same := Sequences.List.padAtStartToSameLength_sameLength a.val b.val zeroDigit
  by_cases h_borrow :
      (subtractAlignedLists
        (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).1
        (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).2 h_same).2 = true
  · exact h_borrow
  · have h_false :
        (subtractAlignedLists
          (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).1
          (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).2 h_same).2 = false := by
      cases h_snd :
          (subtractAlignedLists
            (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).1
            (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).2 h_same).2 with
      | true => exact False.elim (h_borrow h_snd)
      | false => rfl
    cases h_sub : subtractAlignedLists
        (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).1
        (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).2 h_same with
    | mk digits borrow =>
        rw [h_sub] at h_false
        cases borrow with
        | true => cases h_false
        | false =>
            have h_spec := subtractAlignedLists_spec h_same
            rw [h_sub] at h_spec
            dsimp only at h_spec
            simp at h_spec
            obtain ⟨_, h_val⟩ := h_spec
            have h_ge : toPeano b ≤ toPeano a := by
              unfold toPeano
              rw [← toPeanoList_padAtStartToSameLength_snd a.val b.val,
                ← toPeanoList_padAtStartToSameLength_fst a.val b.val, ← h_val]
              exact Peano.le_add_self_right _ _
            exact False.elim
              (Peano.cardinal_not_lt_of_le h_ge h)

theorem subtractWithRemainder_of_lt (a b : Decimal) (h : a < b) :
    (subtractWithRemainder a b).1 = zero ∧
      toPeano (subtractWithRemainder a b).2 =
        toPeano (subtract b a (Or.inl h)) := by
  have h_borrow := subtractAlignedLists_borrow_true_of_lessThan h
  constructor
  · unfold subtractWithRemainder
    dsimp only
    rw [dif_pos h_borrow]
  · unfold subtractWithRemainder
    dsimp only
    rw [dif_pos h_borrow]

theorem subtractWithRemainder_of_le (a b : Decimal) (h : b ≤ a) :
    toPeano (subtractWithRemainder a b).1 = toPeano (subtract a b h) ∧
      (subtractWithRemainder a b).2 = zero := by
  have h_borrow := subtractAlignedLists_borrow_false_of_le h
  have h_ne : ¬ (subtractAlignedLists
      (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).1
      (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).2
      (Sequences.List.padAtStartToSameLength_sameLength a.val b.val zeroDigit)).2 = true := by
    intro ht
    rw [h_borrow] at ht
    exact Bool.false_ne_true ht
  constructor
  · have h_add_swr :
        toPeano (subtractWithRemainder a b).1 + toPeano b = toPeano a := by
      unfold subtractWithRemainder toPeano
      dsimp only
      rw [dif_neg h_ne]
      change toPeanoList
          (subtractAlignedLists
            (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).1
            (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).2
            (Sequences.List.padAtStartToSameLength_sameLength a.val b.val zeroDigit)).1
          Peano.zero +
        toPeanoList b.val Peano.zero =
        toPeanoList a.val Peano.zero
      let h_same := Sequences.List.padAtStartToSameLength_sameLength a.val b.val zeroDigit
      cases h_sub : subtractAlignedLists
          (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).1
          (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).2 h_same with
      | mk digits borrow =>
          have h_spec := subtractAlignedLists_spec h_same
          rw [h_sub] at h_spec
          dsimp only at h_spec
          obtain ⟨_, h_value⟩ := h_spec
          have h_borrow' : borrow = false := by
            have := h_borrow
            rw [h_sub] at this
            exact this
          subst h_borrow'
          simp at h_value
          rw [← toPeanoList_padAtStartToSameLength_fst a.val b.val,
            ← toPeanoList_padAtStartToSameLength_snd a.val b.val]
          change toPeanoList digits Peano.zero +
              toPeanoList (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).2
                Peano.zero =
            toPeanoList (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).1
              Peano.zero
          exact h_value
    have h_add_sub : toPeano (subtract a b h) + toPeano b = toPeano a :=
      toPeano_subtract a b h
    exact Peano.add_cancel_right _ _ _ (h_add_swr.trans h_add_sub.symm)
  · unfold subtractWithRemainder
    dsimp only
    rw [dif_neg h_ne]

theorem subtractWithRemainder_fst_toPeano (a b : Decimal) :
    toPeano (subtractWithRemainder a b).1 =
      (Peano.subtractWithRemainder a.toPeano b.toPeano).1 := by
  rcases trichotomy a b with hlt | heq | hgt
  · have h_dec := subtractWithRemainder_of_lt a b hlt
    have h_peano :=
      Peano.subtractWithRemainder_of_lt a.toPeano b.toPeano (Or.inl hlt)
    rw [h_dec.1, congrArg Prod.fst h_peano, toPeano_zero]
  · have h_le : b ≤ a := Or.inr heq.symm
    have h_dec := subtractWithRemainder_of_le a b h_le
    have h_eq_peano := toPeano_eq_of_equivalent heq
    have h_peano :=
      Peano.subtractWithRemainder_of_le a.toPeano b.toPeano (Or.inr h_eq_peano.symm)
    rcases subtract_toPeano a b h_le with ⟨h2, h_sub⟩
    have h_zero : Peano.subtract a.toPeano b.toPeano h2 = Peano.zero :=
      Peano.subtract_eq_zero_of_eq h2 h_eq_peano
    rw [h_dec.1, h_sub, congrArg Prod.fst h_peano, h_zero]
  · have h_le : b ≤ a := Or.inl hgt
    have h_dec := subtractWithRemainder_of_le a b h_le
    have h_peano :=
      Peano.subtractWithRemainder_of_le a.toPeano b.toPeano (Or.inl hgt)
    rcases subtract_toPeano a b h_le with ⟨h2, h_sub⟩
    rw [h_dec.1, h_sub, congrArg Prod.fst h_peano]

theorem subtractWithRemainder_snd_toPeano (a b : Decimal) :
    toPeano (subtractWithRemainder a b).2 =
      (Peano.subtractWithRemainder a.toPeano b.toPeano).2 := by
  rcases trichotomy a b with hlt | heq | hgt
  · have h_dec := subtractWithRemainder_of_lt a b hlt
    have h_peano :=
      Peano.subtractWithRemainder_of_lt a.toPeano b.toPeano (Or.inl hlt)
    rw [h_dec.2, congrArg Prod.snd h_peano]
    rcases subtract_toPeano b a (Or.inl hlt) with ⟨h2, h_sub⟩
    exact h_sub
  · have h_le : b ≤ a := Or.inr heq.symm
    have h_dec := subtractWithRemainder_of_le a b h_le
    have h_eq_peano := toPeano_eq_of_equivalent heq
    have h_peano :=
      Peano.subtractWithRemainder_of_le a.toPeano b.toPeano (Or.inr h_eq_peano.symm)
    rw [h_dec.2, congrArg Prod.snd h_peano, toPeano_zero]
  · have h_le : b ≤ a := Or.inl hgt
    have h_dec := subtractWithRemainder_of_le a b h_le
    have h_peano :=
      Peano.subtractWithRemainder_of_le a.toPeano b.toPeano (Or.inl hgt)
    rw [h_dec.2, congrArg Prod.snd h_peano, toPeano_zero]

def trySubtract (a b : Decimal) : Option Decimal :=
  match subtractWithRemainder a b with
  | ⟨diff, rem⟩ =>
    if rem = zero then some diff else none

theorem subtract_eq_subtractWithRemainder_fst (a b : Decimal) (h : b ≤ a) :
    subtract a b h = (subtractWithRemainder a b).1 := by
  let h_same := Sequences.List.padAtStartToSameLength_sameLength a.val b.val zeroDigit
  have h_borrow := subtractAlignedLists_borrow_false_of_le h
  have h_ne : ¬ (subtractAlignedLists
      (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).1
      (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).2 h_same).2 = true := by
    intro ht
    rw [h_borrow] at ht
    exact Bool.false_ne_true ht
  cases h_sub : subtractAlignedLists
      (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).1
      (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).2 h_same with
  | mk digits borrow =>
      have h_borrow' : borrow = false := by
        have := h_borrow
        rw [h_sub] at this
        exact this
      cases h_borrow'
      apply Subtype.ext
      have h_left : (subtract a b h).val = digits := by
        unfold subtract
        dsimp only
        simp [h_sub]
      have h_right : (subtractWithRemainder a b).1.val = digits := by
        unfold subtractWithRemainder
        dsimp only
        rw [dif_neg h_ne]
        simp [h_sub]
      exact h_left.trans h_right.symm

theorem le_of_trySubtract_eq_some {x y z : Decimal} (h : trySubtract x y = some z) :
    y ≤ x := by
  unfold trySubtract at h
  cases h_swr : subtractWithRemainder x y with
  | mk diff rem =>
      simp only [h_swr] at h
      split at h
      · next h_rem =>
          rcases trichotomy x y with hlt | heq | hgt
          · have h_of_lt := subtractWithRemainder_of_lt x y hlt
            rw [h_swr] at h_of_lt
            have h_add := toPeano_subtract y x (Or.inl hlt)
            rw [← h_of_lt.2, h_rem, toPeano_zero, Peano.zero_add] at h_add
            exact False.elim (not_equivalent_of_lt hlt (equivalent_of_toPeano_eq h_add))
          · exact Or.inr heq.symm
          · exact Or.inl hgt
      · cases h

theorem exists_subtract_of_trySubtract {x y z : Decimal} (h : trySubtract x y = some z) :
    ∃ h', subtract x y h' = z := by
  have hle := le_of_trySubtract_eq_some h
  refine ⟨hle, ?_⟩
  unfold trySubtract at h
  cases h_swr : subtractWithRemainder x y with
  | mk diff rem =>
      simp only [h_swr] at h
      split at h
      · next h_rem =>
          injection h with hz
          subst hz
          have h_fst : (subtractWithRemainder x y).1 = diff := by
            rw [h_swr]
          exact (subtract_eq_subtractWithRemainder_fst x y hle).trans h_fst
      · cases h

theorem trySubtract_of_subtract {x y z : Decimal} (h : ∃ h', subtract x y h' = z) :
    trySubtract x y = some z := by
  obtain ⟨hle, heq⟩ := h
  unfold trySubtract
  cases h_swr : subtractWithRemainder x y with
  | mk diff rem =>
      have h_rem : rem = zero := by
        have := (subtractWithRemainder_of_le x y hle).2
        rw [h_swr] at this
        exact this
      change (if rem = zero then some diff else none) = some z
      rw [if_pos h_rem]
      apply congrArg some
      rw [← heq]
      have h_fst : (subtractWithRemainder x y).1 = diff := by
        rw [h_swr]
      exact Eq.symm ((subtract_eq_subtractWithRemainder_fst x y hle).trans h_fst)

def addPartialListDigit (a : Sequences.List Digit) (b : Digit) : Sequences.List Digit × Digit :=
  match a with
  | .empty => ⟨.empty, b⟩
  | .firstElement d ds =>
    let (ds', carry) := addPartialListDigit ds b
    let sum := d.val + carry.val
    if h : sum < Peano.ten then
      (.firstElement ⟨sum, h⟩ ds', zeroDigit)
    else
      have h_false : sum.isLessThan Peano.ten = false := by
        exact (Peano.isLessThan_eq_false_iff_not_lt sum _).mpr h
      have h1 : Peano.ten ≤ sum := Peano.isLessThan_false_implies_le h_false
      have h2 : sum < Peano.ten + Peano.ten := by
        exact digit_carry_lt_twenty d carry
      have h3 : Peano.subtract sum Peano.ten h1 < Peano.ten := by
        exact subtract_ten_lt_ten sum h1 h2
      (.firstElement ⟨Peano.subtract sum Peano.ten h1, h3⟩ ds', oneDigit)

def addListDigit (a : Sequences.List Digit) (b : Digit) : Sequences.List Digit :=
  let (ds, carry) := addPartialListDigit a b
  if carry.val = .zero then ds else .firstElement carry ds

def multiplyDigitsPeano (a : Digit) (b : Peano) : Sequences.List Digit :=
  match b with
  | Peano.zero => .firstElement zeroDigit .empty
  | Peano.successor b' =>
    let prev := multiplyDigitsPeano a b'
    addListDigit prev a

def multiplyDigits (a b : Digit) : Sequences.List Digit :=
  multiplyDigitsPeano a b.val

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

def multiplyList (a b : Sequences.List Digit) : Sequences.List Digit × Peano :=
  match b with
  | .empty => ⟨.empty, .zero⟩
  | .firstElement d ds =>
    let (accumulator, shift) := multiplyList a ds
    let digitProduct := multiplyListByDigit a d
    let withShift := Sequences.List.padAtEnd digitProduct zeroDigit shift
    let pair := Sequences.List.padAtStartToSameLength accumulator withShift zeroDigit
    let h_same : Sequences.List.SameLength pair.1 pair.2 :=
      Sequences.List.padAtStartToSameLength_sameLength accumulator withShift zeroDigit
    match addAlignedLists pair.1 pair.2 h_same with
    | ⟨digits, true⟩ =>
      ⟨Sequences.List.firstElement oneDigit digits, shift.successor⟩
    | ⟨digits, false⟩ =>
      ⟨digits, shift.successor⟩

theorem padAtEnd_ne_empty {α : Type} (l : Sequences.List α) (paddingValue : α)
    (n : Peano) (hl : l ≠ Sequences.List.empty) :
    Sequences.List.padAtEnd l paddingValue n ≠ Sequences.List.empty := by
  cases l with
  | empty => exact False.elim (hl rfl)
  | firstElement _ _ =>
      simp only [Sequences.List.padAtEnd]
      intro h_empty
      cases h_empty

theorem multiplyPartialListByDigit_fst_ne_empty (a : Sequences.List Digit) (b : Digit)
    (ha : a ≠ Sequences.List.empty) :
    (multiplyPartialListByDigit a b).1 ≠ Sequences.List.empty := by
  cases a with
  | empty => exact False.elim (ha rfl)
  | firstElement d ds =>
      unfold multiplyPartialListByDigit
      dsimp only
      cases h_rec : multiplyPartialListByDigit ds b with
      | mk digits carry =>
          split
          · next h_withCarry =>
              exact False.elim (addListDigit_multiplyDigits_ne_empty d b carry h_withCarry)
          · next x h_withCarry =>
              intro h_empty
              cases h_empty
          · next x y h_withCarry =>
              intro h_empty
              cases h_empty
          · next x y z zs h_withCarry =>
              exact False.elim
                (addListDigit_multiplyDigits_not_three_or_more d b carry x y z zs h_withCarry)

theorem multiplyListByDigit_ne_empty (a : Sequences.List Digit) (b : Digit)
    (ha : a ≠ Sequences.List.empty) :
    multiplyListByDigit a b ≠ Sequences.List.empty := by
  unfold multiplyListByDigit
  dsimp only
  cases h_rec : multiplyPartialListByDigit a b with
  | mk ds carry =>
      have h_ne : ds ≠ Sequences.List.empty := by
        have := multiplyPartialListByDigit_fst_ne_empty a b ha
        rw [h_rec] at this
        exact this
      split
      · exact h_ne
      · intro h_empty
        cases h_empty

theorem padAtStart_empty_ne_empty_of_ne_zero {α : Type} (paddingValue : α)
    (n : Peano) (hn : n ≠ Peano.zero) :
    Sequences.List.padAtStart Sequences.List.empty paddingValue n ≠ Sequences.List.empty := by
  cases n with
  | zero => exact False.elim (hn rfl)
  | successor n' =>
      unfold Sequences.List.padAtStart
      exact padAtStart_ne_empty (by simp) paddingValue n'

theorem padAtStartToSameLength_fst_ne_empty_of_either
    (a b : Sequences.List Digit) (paddingValue : Digit)
    (h : a ≠ Sequences.List.empty ∨ b ≠ Sequences.List.empty) :
    (Sequences.List.padAtStartToSameLength a b paddingValue).1 ≠ Sequences.List.empty := by
  cases h with
  | inl ha =>
      exact padAtStartToSameLength_fst_ne_empty a b paddingValue ha
  | inr hb =>
      unfold Sequences.List.padAtStartToSameLength
      dsimp only
      split
      · next hlt =>
          have hlt' : b.length < a.length := (Peano.isLessThan_eq_true_iff_lt _ _).mp hlt
          cases a with
          | empty => exact False.elim (Peano.not_lt_zero _ hlt')
          | firstElement _ _ => intro h_empty; cases h_empty
      · next hfalse =>
          have h_le : a.length ≤ b.length := Peano.isLessThan_false_implies_le hfalse
          cases a with
          | empty =>
              cases b with
              | empty => exact False.elim (hb rfl)
              | firstElement db dbs =>
                  change Sequences.List.padAtStart Sequences.List.empty paddingValue
                      (Peano.subtract (Sequences.List.firstElement db dbs).length Peano.zero h_le) ≠
                    Sequences.List.empty
                  simp only [Peano.subtract]
                  exact padAtStart_empty_ne_empty_of_ne_zero paddingValue _
                    (Peano.successor_ne_zero _)
          | firstElement _ _ =>
              exact padAtStart_ne_empty (by simp) paddingValue _

theorem multiplyList_fst_ne_empty (a b : Sequences.List Digit)
    (ha : a ≠ Sequences.List.empty) (hb : b ≠ Sequences.List.empty) :
    (multiplyList a b).1 ≠ Sequences.List.empty := by
  cases b with
  | empty => exact False.elim (hb rfl)
  | firstElement d ds =>
      unfold multiplyList
      dsimp only
      cases h_rec : multiplyList a ds with
      | mk accumulator shift =>
          dsimp only
          let digitProduct := multiplyListByDigit a d
          let withShift := Sequences.List.padAtEnd digitProduct zeroDigit shift
          let pair := Sequences.List.padAtStartToSameLength accumulator withShift zeroDigit
          let h_same : Sequences.List.SameLength pair.1 pair.2 :=
            Sequences.List.padAtStartToSameLength_sameLength accumulator withShift zeroDigit
          have h_digitProduct_ne : digitProduct ≠ Sequences.List.empty :=
            multiplyListByDigit_ne_empty a d ha
          have h_withShift_ne : withShift ≠ Sequences.List.empty :=
            padAtEnd_ne_empty digitProduct zeroDigit shift h_digitProduct_ne
          have h_pair1_ne : pair.1 ≠ Sequences.List.empty :=
            padAtStartToSameLength_fst_ne_empty_of_either accumulator withShift zeroDigit
              (Or.inr h_withShift_ne)
          cases h_add : addAlignedLists pair.1 pair.2 h_same with
          | mk digits carry =>
              cases carry with
              | true =>
                  intro h_empty
                  cases h_empty
              | false =>
                  exact addAlignedLists_ne_empty h_same h_pair1_ne h_add

def multiply (a b : Decimal) : Decimal :=
  ⟨(multiplyList a.val b.val).1, multiplyList_fst_ne_empty a.val b.val a.property b.property⟩

instance : Mul Decimal := ⟨multiply⟩

theorem addPartialListDigit_spec (a : Sequences.List Digit) (b : Digit) :
    (addPartialListDigit a b).1.length = a.length ∧
    toPeanoList (addPartialListDigit a b).1 Peano.zero +
        (addPartialListDigit a b).2.val * Peano.tenPow a.length =
      toPeanoList a Peano.zero + b.val := by
  induction a with
  | empty =>
      simp [addPartialListDigit, toPeanoList, Sequences.List.length, Peano.tenPow]
  | firstElement d ds ih =>
      unfold addPartialListDigit
      dsimp only
      cases h_rec : addPartialListDigit ds b with
      | mk digits carry =>
          rw [h_rec] at ih
          dsimp only at ih
          obtain ⟨h_length, ih_value⟩ := ih
          split
          · constructor
            · simp [Sequences.List.length, h_length]
            · simp only [toPeanoList_firstElement, Sequences.List.length, zeroDigit,
                Peano.zero_multiply, Peano.add_zero]
              rw [h_length]
              calc
                _ = d.val * Peano.tenPow ds.length +
                      (carry.val * Peano.tenPow ds.length +
                        toPeanoList digits Peano.zero) := by
                      rw [Peano.multiply_distributive_over_add_left]
                      simp only [Peano.add_associative]
                _ = d.val * Peano.tenPow ds.length +
                      (toPeanoList digits Peano.zero +
                        carry.val * Peano.tenPow ds.length) := by
                      rw [Peano.add_commutative
                        (carry.val * Peano.tenPow ds.length)
                        (toPeanoList digits Peano.zero)]
                _ = d.val * Peano.tenPow ds.length +
                      (toPeanoList ds Peano.zero + b.val) := by
                      rw [ih_value]
                _ = d.val * Peano.tenPow ds.length +
                      toPeanoList ds Peano.zero + b.val := by
                      rw [Peano.add_associative]
          · next h_not_lt =>
            constructor
            · simp [Sequences.List.length, h_length]
            · simp only [toPeanoList_firstElement, Sequences.List.length, oneDigit,
                Peano.one_multiply, Peano.tenPow_add_one]
              rw [h_length]
              have h_false : (d.val + carry.val).isLessThan Peano.ten = false :=
                (Peano.isLessThan_eq_false_iff_not_lt _ _).mpr h_not_lt
              have h_le : Peano.ten ≤ d.val + carry.val :=
                Peano.isLessThan_false_implies_le h_false
              have h_digit := Peano.subtract_add_cancel
                (d.val + carry.val) Peano.ten h_le
              calc
                _ = (Peano.subtract (d.val + carry.val)
                          Peano.ten h_le + Peano.ten) *
                        Peano.tenPow ds.length +
                      toPeanoList digits Peano.zero := by
                      rw [Peano.multiply_distributive_over_add_left]
                      exact Peano.add_right_commutative _ _ _
                _ = (d.val + carry.val) * Peano.tenPow ds.length +
                      toPeanoList digits Peano.zero := by
                      rw [h_digit]
                _ = d.val * Peano.tenPow ds.length +
                      (carry.val * Peano.tenPow ds.length +
                        toPeanoList digits Peano.zero) := by
                      rw [Peano.multiply_distributive_over_add_left]
                      rw [Peano.add_associative]
                _ = d.val * Peano.tenPow ds.length +
                      (toPeanoList digits Peano.zero +
                        carry.val * Peano.tenPow ds.length) := by
                      rw [Peano.add_commutative
                        (carry.val * Peano.tenPow ds.length)
                        (toPeanoList digits Peano.zero)]
                _ = d.val * Peano.tenPow ds.length +
                      (toPeanoList ds Peano.zero + b.val) := by
                      rw [ih_value]
                _ = d.val * Peano.tenPow ds.length +
                      toPeanoList ds Peano.zero + b.val := by
                      rw [Peano.add_associative]

theorem toPeanoList_padAtEnd (l : Sequences.List Digit) (n : Peano) :
    toPeanoList (Sequences.List.padAtEnd l zeroDigit n) Peano.zero =
      toPeanoList l Peano.zero * Peano.tenPow n := by
  induction l with
  | empty =>
    induction n with
    | zero =>
      simp [Sequences.List.padAtEnd, toPeanoList, Peano.tenPow, Peano.multiply_one]
    | successor n ih =>
      simp [Sequences.List.padAtEnd, toPeanoList_firstElement, toPeanoList]
      show Peano.zero * _ + _ = _
      simp only [Peano.zero_multiply, Peano.zero_add]
      rw [ih]
      simp [toPeanoList, Peano.zero_multiply]
  | firstElement d ds ih =>
    simp only [Sequences.List.padAtEnd, toPeanoList_firstElement, Sequences.List.padAtEnd_length]
    rw [Peano.tenPow_add, ← Peano.multiply_associative, ih,
        ← Peano.multiply_distributive_over_add_left, ← toPeanoList_firstElement]

theorem toPeanoList_addListDigit (a : Sequences.List Digit) (b : Digit) :
    toPeanoList (addListDigit a b) Peano.zero =
      toPeanoList a Peano.zero + b.val := by
  obtain ⟨h_len, h_val⟩ := addPartialListDigit_spec a b
  cases h_rec : addPartialListDigit a b with
  | mk ds carry =>
    rw [h_rec] at h_len h_val; dsimp only at h_len h_val
    unfold addListDigit; rw [h_rec]; dsimp only
    by_cases h_carry : carry.val = Peano.zero
    · rw [h_carry, Peano.zero_multiply, Peano.add_zero] at h_val
      rw [if_pos h_carry]
      exact h_val
    · rw [if_neg h_carry, toPeanoList_firstElement, h_len,
          Peano.add_commutative (carry.val * _)]
      exact h_val

theorem toPeanoList_multiplyDigitsPeano (d : Digit) (n : Peano) :
    toPeanoList (multiplyDigitsPeano d n) Peano.zero =
      d.val * n := by
  induction n with
  | zero =>
    simp [multiplyDigitsPeano, toPeanoList_firstElement, toPeanoList, zeroDigit,
          Sequences.List.length, Peano.tenPow, Peano.multiply_zero,
          Peano.multiply_one]
  | successor n ih =>
    unfold multiplyDigitsPeano
    rw [toPeanoList_addListDigit, ih, Peano.multiply_successor]

theorem toPeanoList_multiplyDigits (d b : Digit) :
    toPeanoList (multiplyDigits d b) Peano.zero = d.val * b.val := by
  unfold multiplyDigits
  exact toPeanoList_multiplyDigitsPeano d b.val

theorem toPeanoList_addListDigit_multiplyDigits (d b carry : Digit) :
    toPeanoList (addListDigit (multiplyDigits d b) carry) Peano.zero =
      d.val * b.val + carry.val := by
  rw [toPeanoList_addListDigit, toPeanoList_multiplyDigits]

theorem multiplyPartialListByDigit_spec (a : Sequences.List Digit) (d : Digit) :
    (multiplyPartialListByDigit a d).1.length = a.length ∧
    toPeanoList (multiplyPartialListByDigit a d).1 Peano.zero +
        (multiplyPartialListByDigit a d).2.val * Peano.tenPow a.length =
      toPeanoList a Peano.zero * d.val := by
  induction a with
  | empty =>
      simp [multiplyPartialListByDigit, toPeanoList, Sequences.List.length,
        Peano.tenPow, zeroDigit, Peano.zero_multiply,
        Peano.multiply_one]
  | firstElement digit ds ih =>
      unfold multiplyPartialListByDigit
      dsimp only
      cases h_rec : multiplyPartialListByDigit ds d with
      | mk digits carry =>
          rw [h_rec] at ih
          dsimp only at ih
          obtain ⟨h_length, ih_value⟩ := ih
          have h_withCarry_value := toPeanoList_addListDigit_multiplyDigits digit d carry
          split
          · next h_withCarry =>
              exact False.elim (addListDigit_multiplyDigits_ne_empty digit d carry h_withCarry)
          · next x h_withCarry =>
              constructor
              · simp [Sequences.List.length, h_length]
              · rw [h_withCarry] at h_withCarry_value
                simp only [toPeanoList, Peano.zero_multiply,
                  Peano.zero_add] at h_withCarry_value
                simp only [toPeanoList_firstElement, Sequences.List.length, zeroDigit,
                  Peano.zero_multiply, Peano.add_zero]
                rw [h_length]
                calc
                  _ = (digit.val * d.val + carry.val) * Peano.tenPow ds.length +
                        toPeanoList digits Peano.zero := by
                      rw [h_withCarry_value]
                  _ = digit.val * d.val * Peano.tenPow ds.length +
                        (carry.val * Peano.tenPow ds.length +
                          toPeanoList digits Peano.zero) := by
                      rw [Peano.multiply_distributive_over_add_left]
                      rw [Peano.add_associative]
                  _ = digit.val * d.val * Peano.tenPow ds.length +
                        (toPeanoList digits Peano.zero +
                          carry.val * Peano.tenPow ds.length) := by
                      rw [Peano.add_commutative
                        (carry.val * Peano.tenPow ds.length)
                        (toPeanoList digits Peano.zero)]
                  _ = digit.val * d.val * Peano.tenPow ds.length +
                        (toPeanoList ds Peano.zero * d.val) := by
                      rw [ih_value]
                  _ = (digit.val * Peano.tenPow ds.length +
                        toPeanoList ds Peano.zero) * d.val := by
                      rw [Peano.multiply_distributive_over_add_left]
                      rw [Peano.multiply_associative]
                      rw [Peano.multiply_commutative d.val (Peano.tenPow ds.length)]
                      rw [← Peano.multiply_associative digit.val (Peano.tenPow ds.length) d.val]
          · next x y h_withCarry =>
              constructor
              · simp [Sequences.List.length, h_length]
              · rw [h_withCarry] at h_withCarry_value
                simp only [toPeanoList, Peano.zero_multiply,
                  Peano.zero_add] at h_withCarry_value
                simp only [toPeanoList_firstElement, Sequences.List.length]
                rw [h_length, Peano.tenPow_add_one]
                calc
                  _ = (y.val + x.val * Peano.ten) *
                        Peano.tenPow ds.length +
                        toPeanoList digits Peano.zero := by
                      rw [Peano.multiply_distributive_over_add_left]
                      rw [Peano.multiply_associative]
                      rw [← Peano.multiply_associative x.val]
                      simp only [Peano.add_associative, Peano.add_commutative]
                  _ = (x.val * Peano.ten + y.val) *
                        Peano.tenPow ds.length +
                        toPeanoList digits Peano.zero := by
                      rw [Peano.add_commutative y.val (x.val * Peano.ten)]
                  _ = (digit.val * d.val + carry.val) *
                        Peano.tenPow ds.length +
                        toPeanoList digits Peano.zero := by
                      rw [h_withCarry_value]
                  _ = digit.val * d.val * Peano.tenPow ds.length +
                        (carry.val * Peano.tenPow ds.length +
                          toPeanoList digits Peano.zero) := by
                      rw [Peano.multiply_distributive_over_add_left]
                      rw [Peano.add_associative]
                  _ = digit.val * d.val * Peano.tenPow ds.length +
                        (toPeanoList digits Peano.zero +
                          carry.val * Peano.tenPow ds.length) := by
                      rw [Peano.add_commutative
                        (carry.val * Peano.tenPow ds.length)
                        (toPeanoList digits Peano.zero)]
                  _ = digit.val * d.val * Peano.tenPow ds.length +
                        (toPeanoList ds Peano.zero * d.val) := by
                      rw [ih_value]
                  _ = (digit.val * Peano.tenPow ds.length +
                        toPeanoList ds Peano.zero) * d.val := by
                      rw [Peano.multiply_distributive_over_add_left]
                      rw [Peano.multiply_associative]
                      rw [Peano.multiply_commutative d.val (Peano.tenPow ds.length)]
                      rw [← Peano.multiply_associative digit.val (Peano.tenPow ds.length) d.val]
          · next x y z zs h_withCarry =>
              exact False.elim (addListDigit_multiplyDigits_not_three_or_more digit d carry x y z zs h_withCarry)

theorem toPeanoList_multiplyListByDigit (a : Sequences.List Digit) (d : Digit) :
    toPeanoList (multiplyListByDigit a d) Peano.zero =
      toPeanoList a Peano.zero * d.val := by
  obtain ⟨h_len, h_val⟩ := multiplyPartialListByDigit_spec a d
  cases h_rec : multiplyPartialListByDigit a d with
  | mk ds carry =>
    rw [h_rec] at h_len h_val; dsimp only at h_len h_val
    unfold multiplyListByDigit; rw [h_rec]; dsimp only
    by_cases h_carry : carry.val = Peano.zero
    · rw [h_carry, Peano.zero_multiply, Peano.add_zero] at h_val
      rw [if_pos h_carry]
      exact h_val
    · rw [if_neg h_carry, toPeanoList_firstElement, h_len,
          Peano.add_commutative (carry.val * _)]
      exact h_val

theorem toPeanoList_addAlignedLists_result {a b : Sequences.List Digit}
  (h : Sequences.List.SameLength a b) :
  let result := addAlignedLists a b h
  let digitsWithCarry :=
    if result.2 then Sequences.List.firstElement oneDigit result.1 else result.1
  toPeanoList digitsWithCarry Peano.zero =
    toPeanoList a Peano.zero +
      toPeanoList b Peano.zero := by
  cases h_add : addAlignedLists a b h with
  | mk digits carry =>
      have h_spec := addAlignedLists_spec h
      rw [h_add] at h_spec
      dsimp only at h_spec ⊢
      obtain ⟨h_length, h_value⟩ := h_spec
      cases carry with
      | false =>
          simp only [if_neg Bool.false_ne_true, Peano.add_zero] at h_value ⊢
          exact h_value
      | true =>
          simp only [if_true] at h_value ⊢
          rw [toPeanoList_firstElement, oneDigit, Peano.one_multiply, h_length]
          rw [Peano.add_commutative]
          exact h_value

theorem multiplyList_spec (a b : Sequences.List Digit) :
    (multiplyList a b).2 = b.length ∧
    toPeanoList (multiplyList a b).1 Peano.zero =
      toPeanoList a Peano.zero * toPeanoList b Peano.zero := by
  induction b with
  | empty =>
      simp [multiplyList, toPeanoList, Sequences.List.length, Peano.multiply_zero]
  | firstElement d ds ih =>
      unfold multiplyList
      dsimp only
      cases h_rec : multiplyList a ds with
      | mk accumulator shift =>
          rw [h_rec] at ih
          dsimp only at ih
          obtain ⟨h_shift, ih_value⟩ := ih
          let digitProduct := multiplyListByDigit a d
          let withShift := Sequences.List.padAtEnd digitProduct zeroDigit shift
          let pair := Sequences.List.padAtStartToSameLength accumulator withShift zeroDigit
          let h_same : Sequences.List.SameLength pair.1 pair.2 :=
            Sequences.List.padAtStartToSameLength_sameLength accumulator withShift zeroDigit
          cases h_add : addAlignedLists pair.1 pair.2 h_same with
          | mk digits carry =>
              constructor
              · cases carry <;> simp [Sequences.List.length, h_shift, Peano.one,
                  Peano.add_successor, Peano.add_zero]
              · have h_add_value := toPeanoList_addAlignedLists_result h_same
                rw [h_add] at h_add_value
                dsimp only at h_add_value
                cases carry with
                | false =>
                    simp only [if_neg Bool.false_ne_true] at h_add_value ⊢
                    rw [h_add_value]
                    rw [toPeanoList_padAtStartToSameLength_fst,
                        toPeanoList_padAtStartToSameLength_snd]
                    dsimp only [withShift, digitProduct]
                    rw [toPeanoList_padAtEnd, toPeanoList_multiplyListByDigit, ih_value, h_shift]
                    rw [toPeanoList_firstElement]
                    calc
                      toPeanoList a Peano.zero *
                            toPeanoList ds Peano.zero +
                          toPeanoList a Peano.zero * d.val *
                            Peano.tenPow ds.length =
                        toPeanoList a Peano.zero *
                          (toPeanoList ds Peano.zero +
                            d.val * Peano.tenPow ds.length) := by
                          rw [Peano.multiply_distributive_over_add_right]
                          rw [Peano.multiply_associative]
                      _ = toPeanoList a Peano.zero *
                          (d.val * Peano.tenPow ds.length +
                            toPeanoList ds Peano.zero) := by
                          rw [Peano.add_commutative]
                | true =>
                    simp only [if_true] at h_add_value ⊢
                    rw [h_add_value]
                    rw [toPeanoList_padAtStartToSameLength_fst,
                        toPeanoList_padAtStartToSameLength_snd]
                    dsimp only [withShift, digitProduct]
                    rw [toPeanoList_padAtEnd, toPeanoList_multiplyListByDigit, ih_value, h_shift]
                    rw [toPeanoList_firstElement]
                    calc
                      toPeanoList a Peano.zero *
                            toPeanoList ds Peano.zero +
                          toPeanoList a Peano.zero * d.val *
                            Peano.tenPow ds.length =
                        toPeanoList a Peano.zero *
                          (toPeanoList ds Peano.zero +
                            d.val * Peano.tenPow ds.length) := by
                          rw [Peano.multiply_distributive_over_add_right]
                          rw [Peano.multiply_associative]
                      _ = toPeanoList a Peano.zero *
                          (d.val * Peano.tenPow ds.length +
                            toPeanoList ds Peano.zero) := by
                          rw [Peano.add_commutative]

theorem multiply_toPeano (a b : Decimal) :
    toPeano (a * b) = a.toPeano * b.toPeano := by
  unfold toPeano
  change toPeanoList (multiply a b).val Peano.zero =
    toPeanoList a.val Peano.zero * toPeanoList b.val Peano.zero
  unfold multiply
  exact (multiplyList_spec a.val b.val).2

theorem equivalent_multiply_commutative (a b : Decimal) : a * b ≈ b * a := by
  apply equivalent_of_toPeano_eq
  rw [multiply_toPeano, multiply_toPeano]
  apply Peano.multiply_commutative

theorem equivalent_multiply_associative (a b c : Decimal) : a * b * c ≈ a * (b * c) := by
  apply equivalent_of_toPeano_eq
  rw [multiply_toPeano, multiply_toPeano, multiply_toPeano, multiply_toPeano]
  apply Peano.multiply_associative

theorem equivalent_multiply_distributive_over_add_right (a b c : Decimal) :
    a * (b + c) ≈ a * b + a * c := by
  apply equivalent_of_toPeano_eq
  rw [multiply_toPeano, add_toPeano, add_toPeano, multiply_toPeano, multiply_toPeano]
  apply Peano.multiply_distributive_over_add_right

theorem equivalent_multiply_distributive_over_add_left (a b c : Decimal) :
    (a + b) * c ≈ a * c + b * c := by
  apply equivalent_of_toPeano_eq
  rw [multiply_toPeano, add_toPeano, add_toPeano, multiply_toPeano, multiply_toPeano]
  apply Peano.multiply_distributive_over_add_left

theorem multiply_subtract_distributive (a b c : Decimal) (h : c ≤ b) :
    ∃ h2, a * subtract b c h ≈ subtract (a * b) (a * c) h2 := by
  obtain ⟨h2p, heq⟩ :=
    Peano.multiply_subtract a.toPeano b.toPeano c.toPeano (toPeano_le_of_le h)
  have h2 : a * c ≤ a * b :=
    le_of_toPeano_le (by simpa [multiply_toPeano] using h2p)
  refine ⟨h2, equivalent_of_toPeano_eq ?_⟩
  obtain ⟨_, hsub_bc⟩ := subtract_toPeano b c h
  obtain ⟨_, hsub_ac⟩ := subtract_toPeano (a * b) (a * c) h2
  rw [multiply_toPeano, hsub_bc, hsub_ac, heq]
  exact Peano.subtract_eq_of_eq _ _ (by rw [multiply_toPeano]) (by rw [multiply_toPeano])

theorem subtract_multiply_distributive (a b c : Decimal) (h : b ≤ a) :
    ∃ h2, subtract a b h * c ≈ subtract (a * c) (b * c) h2 := by
  obtain ⟨h2p, heq⟩ :=
    Peano.subtract_multiply c.toPeano a.toPeano b.toPeano (toPeano_le_of_le h)
  have h2 : b * c ≤ a * c :=
    le_of_toPeano_le (by simpa [multiply_toPeano] using h2p)
  refine ⟨h2, equivalent_of_toPeano_eq ?_⟩
  obtain ⟨_, hsub_ab⟩ := subtract_toPeano a b h
  obtain ⟨_, hsub_bc⟩ := subtract_toPeano (a * c) (b * c) h2
  rw [multiply_toPeano, hsub_ab, hsub_bc, heq]
  exact Peano.subtract_eq_of_eq _ _ (by rw [multiply_toPeano]) (by rw [multiply_toPeano])

def Divisible (a b : Decimal) : Prop := ¬ (b ≈ zero) ∧ ∃ c, b * c ≈ a

theorem divisibleToPeano (a b : Decimal) :
    Divisible a b ↔ Peano.Divisible a.toPeano b.toPeano := by
  apply Iff.intro
  · intro h
    unfold Divisible at h
    unfold Peano.Divisible
    obtain ⟨hb, c, hc⟩ := h
    refine ⟨toPeano_ne_zero_of_not_equivalent_zero hb, c.toPeano, ?_⟩
    rw [← multiply_toPeano]
    exact toPeano_eq_of_equivalent hc
  · intro h
    unfold Divisible
    unfold Peano.Divisible at h
    obtain ⟨hb, c_peano, hc⟩ := h
    let c := fromPeano c_peano
    refine ⟨?_, c, ?_⟩
    · intro heq
      exact hb ((toPeano_eq_of_equivalent heq).trans toPeano_zero)
    · apply equivalent_of_toPeano_eq
      rw [multiply_toPeano]
      have h_c_toPeano : c.toPeano = c_peano := toPeano_fromPeano c_peano
      rw [h_c_toPeano]
      exact hc

theorem nine_lt_ten : Peano.nine < Peano.ten := Peano.LessThan.base

/-- Numerical comparison of digit lists (leading zeros via padding are insignificant). -/
def isLessThanLists (x y : Sequences.List Digit) : Bool :=
  let pair := Sequences.List.padAtStartToSameLength x y zeroDigit
  isLessThanAlignedLists pair.1 pair.2
    (Sequences.List.padAtStartToSameLength_sameLength x y zeroDigit)

/-- Columnar subtraction of digit lists, assuming `y ≤ x` numerically. -/
def subtractLists (x y : Sequences.List Digit) : Sequences.List Digit :=
  let pair := Sequences.List.padAtStartToSameLength x y zeroDigit
  let h_same := Sequences.List.padAtStartToSameLength_sameLength x y zeroDigit
  (subtractAlignedLists pair.1 pair.2 h_same).1

/--
Largest digit `q ≤ candidate` such that `divisor * q ≤ remainder`, together with
the columnar difference `remainder - divisor * q`.
-/
def findQuotientDigitAux (remainder divisor : Sequences.List Digit)
    (candidate : Peano) (hc : candidate < Peano.ten) :
    Digit × Sequences.List Digit :=
  let d : Digit := ⟨candidate, hc⟩
  let product := multiplyListByDigit divisor d
  if isLessThanLists remainder product then
    match candidate with
    | .zero => (zeroDigit, remainder)
    | .successor c' =>
        findQuotientDigitAux remainder divisor c' (Peano.lt_of_succ_lt hc)
  else
    (d, subtractLists remainder product)

def findQuotientDigit (remainder divisor : Sequences.List Digit) :
    Digit × Sequences.List Digit :=
  findQuotientDigitAux remainder divisor Peano.nine nine_lt_ten

/--
Columnar (long) division step: process the remaining dividend digits while
accumulating the current remainder and quotient digit lists.
-/
def divideWithRemainderAux (dividend divisor : Sequences.List Digit)
    (remainder quotient : Sequences.List Digit) :
    Sequences.List Digit × Sequences.List Digit :=
  match dividend with
  | .empty => (quotient, remainder)
  | .firstElement d ds =>
      let newRem := Sequences.List.append remainder d
      let (qDigit, nextRem) := findQuotientDigit newRem divisor
      let newQuotient :=
        if Sequences.List.isEmpty quotient then
          if qDigit.val = Peano.zero then
            quotient
          else
            .firstElement qDigit .empty
        else
          Sequences.List.append quotient qDigit
      divideWithRemainderAux ds divisor nextRem newQuotient

/--
Divide `a` by `b` with remainder using the columnar (long) division algorithm.

Requires a non-zero divisor (up to Decimal equivalence), analogous to
`CardinalNatural.Peano.divideWithRemainder`. Returns a quotient and remainder
as Decimals (using `zero` when the corresponding digit list is empty/all-zero),
implemented like `OrdinalNatural.Decimal.divideWithRemainder`.
-/
def divideWithRemainder (a b : Decimal) (_hb : ¬ b ≈ zero) : Decimal × Decimal :=
  let (qDigits, rDigits) := divideWithRemainderAux a.val b.val .empty .empty
  (normalizeList qDigits, normalizeList rDigits)

theorem toPeanoList_append (l : Sequences.List Digit) (d : Digit) :
    toPeanoList (Sequences.List.append l d) Peano.zero =
      toPeanoList l Peano.zero * Peano.ten + d.val := by
  induction l with
  | empty =>
      simp [Sequences.List.append, toPeanoList_firstElement, toPeanoList,
        Sequences.List.length, Peano.tenPow,
        Peano.zero_multiply, Peano.zero_add,
        Peano.multiply_one]
  | firstElement x xs ih =>
      rw [Sequences.List.append, toPeanoList_firstElement, ih,
        Sequences.List.append_length, Peano.tenPow_add_one,
        toPeanoList_firstElement,
        Peano.multiply_distributive_over_add_left,
        Peano.multiply_associative,
        Peano.add_associative,
        Peano.multiply_commutative Peano.ten]

theorem isLessThanLists_iff_toPeanoList_lt (x y : Sequences.List Digit) :
    isLessThanLists x y = true ↔
      toPeanoList x Peano.zero < toPeanoList y Peano.zero := by
  unfold isLessThanLists
  let pair := Sequences.List.padAtStartToSameLength x y zeroDigit
  let h_same := Sequences.List.padAtStartToSameLength_sameLength x y zeroDigit
  have hpad_x := toPeanoList_padAtStartToSameLength_fst x y
  have hpad_y := toPeanoList_padAtStartToSameLength_snd x y
  constructor
  · intro h
    have hlt_aligned :
        LessThanAlignedLists pair.1 pair.2 h_same :=
      (isLessThanAlignedLists_iff_lessThanAlignedLists pair.1 pair.2 h_same).mp h
    have := LessThanAlignedLists_toPeanoList_lt h_same hlt_aligned
    rwa [hpad_x, hpad_y] at this
  · intro hlt
    have hlt_pad :
        toPeanoList pair.1 Peano.zero < toPeanoList pair.2 Peano.zero := by
      rwa [hpad_x, hpad_y]
    have hlt_aligned :=
      LessThanAlignedLists_of_toPeanoList_lt h_same hlt_pad
    exact (isLessThanAlignedLists_iff_lessThanAlignedLists pair.1 pair.2 h_same).mpr
      hlt_aligned

theorem isLessThanLists_eq_false_iff_not_lt (x y : Sequences.List Digit) :
    isLessThanLists x y = false ↔
      ¬ toPeanoList x Peano.zero < toPeanoList y Peano.zero := by
  constructor
  · intro h hlt
    have htrue := (isLessThanLists_iff_toPeanoList_lt x y).mpr hlt
    rw [htrue] at h
    exact Bool.noConfusion h
  · intro hnlt
    cases h : isLessThanLists x y with
    | false => rfl
    | true =>
      exact False.elim (hnlt ((isLessThanLists_iff_toPeanoList_lt x y).mp h))

theorem subtractAlignedLists_borrow_false_of_not_lt {a b : Sequences.List Digit}
    (h_same : Sequences.List.SameLength a b)
    (hnlt : ¬ toPeanoList a Peano.zero < toPeanoList b Peano.zero) :
    (subtractAlignedLists a b h_same).2 = false := by
  cases hres : subtractAlignedLists a b h_same with
  | mk digits borrow =>
    cases borrow with
    | false => rfl
    | true =>
      have hspec := subtractAlignedLists_spec h_same
      rw [hres] at hspec
      dsimp only at hspec
      obtain ⟨h_len, h_val⟩ := hspec
      simp only [if_true] at h_val
      have hdigits_lt := toPeanoList_lt_tenPow digits
      rw [h_len] at hdigits_lt
      have hlt_sum :
          toPeanoList digits Peano.zero + toPeanoList b Peano.zero <
            Peano.tenPow a.length + toPeanoList b Peano.zero :=
        Peano.add_lt_add_right hdigits_lt _
      rw [h_val] at hlt_sum
      have hlt_sum' :
          toPeanoList a Peano.zero + Peano.tenPow a.length <
            toPeanoList b Peano.zero + Peano.tenPow a.length := by
        rwa [Peano.add_commutative
          (Peano.tenPow a.length) (toPeanoList b Peano.zero)] at hlt_sum
      exact False.elim (hnlt (Peano.add_lt_cancel_right hlt_sum'))

theorem subtractLists_spec (x y : Sequences.List Digit)
    (hnlt : ¬ toPeanoList x Peano.zero < toPeanoList y Peano.zero) :
    toPeanoList (subtractLists x y) Peano.zero +
        toPeanoList y Peano.zero =
      toPeanoList x Peano.zero := by
  let h_same := Sequences.List.padAtStartToSameLength_sameLength x y zeroDigit
  have hpad_x := toPeanoList_padAtStartToSameLength_fst x y
  have hpad_y := toPeanoList_padAtStartToSameLength_snd x y
  have hnlt_pad :
      ¬ toPeanoList (Sequences.List.padAtStartToSameLength x y zeroDigit).1
            Peano.zero <
          toPeanoList (Sequences.List.padAtStartToSameLength x y zeroDigit).2
            Peano.zero := by
    intro hlt
    apply hnlt
    rwa [← hpad_x, ← hpad_y]
  have hborrow :=
    subtractAlignedLists_borrow_false_of_not_lt h_same hnlt_pad
  have hspec := subtractAlignedLists_spec h_same
  cases hres :
    subtractAlignedLists (Sequences.List.padAtStartToSameLength x y zeroDigit).1
      (Sequences.List.padAtStartToSameLength x y zeroDigit).2 h_same with
  | mk digits borrow =>
    rw [hres] at hspec hborrow
    dsimp only at hspec hborrow
    obtain ⟨_, h_val⟩ := hspec
    simp only [hborrow, if_neg Bool.false_ne_true, Peano.add_zero] at h_val
    rw [hpad_x, hpad_y] at h_val
    simpa [subtractLists, hres] using h_val

theorem findQuotientDigitAux_spec (remainder divisor : Sequences.List Digit)
    (candidate : Peano) (hc : candidate < Peano.ten) :
    let result := findQuotientDigitAux remainder divisor candidate hc
    let d := result.1
    let nextRem := result.2
    toPeanoList remainder Peano.zero =
        toPeanoList divisor Peano.zero * d.val +
          toPeanoList nextRem Peano.zero ∧
      ¬ toPeanoList remainder Peano.zero <
          toPeanoList divisor Peano.zero * d.val ∧
      (candidate = d.val ∨
        toPeanoList remainder Peano.zero <
          toPeanoList divisor Peano.zero * d.val.successor) := by
  induction candidate with
  | zero =>
    unfold findQuotientDigitAux
    dsimp only
    by_cases hlt : isLessThanLists remainder
        (multiplyListByDigit divisor ⟨Peano.zero, hc⟩) = true
    · have hlt_val :=
        (isLessThanLists_iff_toPeanoList_lt remainder
          (multiplyListByDigit divisor ⟨Peano.zero, hc⟩)).mp hlt
      rw [toPeanoList_multiplyListByDigit] at hlt_val
      simp only [Peano.multiply_zero] at hlt_val
      exact False.elim
        (Peano.cardinal_not_lt_of_le (Peano.zero_le _) hlt_val)
    · have hnlt := (isLessThanLists_eq_false_iff_not_lt remainder
          (multiplyListByDigit divisor ⟨Peano.zero, hc⟩)).mp
        (eq_false_of_ne_true hlt)
      have hsub := subtractLists_spec remainder
        (multiplyListByDigit divisor ⟨Peano.zero, hc⟩) hnlt
      rw [toPeanoList_multiplyListByDigit] at hsub hnlt
      rw [if_neg hlt]
      refine ⟨?_, hnlt, Or.inl rfl⟩
      simpa [Peano.multiply_zero, Peano.zero_add,
        Peano.add_commutative] using hsub.symm
  | successor c ih =>
    unfold findQuotientDigitAux
    dsimp only
    by_cases hlt : isLessThanLists remainder
        (multiplyListByDigit divisor ⟨c.successor, hc⟩) = true
    · rw [if_pos hlt]
      obtain ⟨heq, hle, hmax⟩ := ih (Peano.lt_of_succ_lt hc)
      refine ⟨heq, hle, ?_⟩
      cases hmax with
      | inl heq_d =>
        have hlt_val :=
          (isLessThanLists_iff_toPeanoList_lt remainder
            (multiplyListByDigit divisor ⟨c.successor, hc⟩)).mp hlt
        rw [toPeanoList_multiplyListByDigit] at hlt_val
        rw [← heq_d]
        exact Or.inr hlt_val
      | inr hlt' => exact Or.inr hlt'
    · have hnlt := (isLessThanLists_eq_false_iff_not_lt remainder
          (multiplyListByDigit divisor ⟨c.successor, hc⟩)).mp
        (eq_false_of_ne_true hlt)
      have hsub := subtractLists_spec remainder
        (multiplyListByDigit divisor ⟨c.successor, hc⟩) hnlt
      rw [toPeanoList_multiplyListByDigit] at hsub hnlt
      rw [if_neg hlt]
      refine ⟨?_, hnlt, Or.inl rfl⟩
      simpa [Peano.add_commutative] using hsub.symm

theorem lt_toNat {a b : Peano} (h : a < b) : a.toNat < b.toNat := by
  induction h with
  | base =>
    simp [Peano.toNat]
  | step _ ih =>
    exact Nat.lt_succ_of_lt ih

theorem lt_of_toNat_lt {a b : Peano} (h : a.toNat < b.toNat) : a < b := by
  cases Peano.trichotomy_or a b with
  | inl hlt => exact hlt
  | inr hrest =>
      cases hrest with
      | inl heq =>
          rw [heq] at h
          exact False.elim (Nat.lt_irrefl _ h)
      | inr hgt =>
          have hgt_nat := lt_toNat hgt
          exact False.elim (Nat.lt_asymm h hgt_nat)

theorem findQuotientDigit_nextRem_lt
    {remainder divisor : Sequences.List Digit}
    {qDigit : Digit} {nextRem : Sequences.List Digit}
    (heq : toPeanoList remainder Peano.zero =
        toPeanoList divisor Peano.zero * qDigit.val +
          toPeanoList nextRem Peano.zero)
    (hbound : toPeanoList remainder Peano.zero <
        toPeanoList divisor Peano.zero * qDigit.val.successor) :
    toPeanoList nextRem Peano.zero < toPeanoList divisor Peano.zero := by
  rw [heq, Peano.multiply_successor] at hbound
  rw [Peano.add_commutative
        (toPeanoList divisor Peano.zero * qDigit.val)
        (toPeanoList nextRem Peano.zero),
      Peano.add_commutative
        (toPeanoList divisor Peano.zero * qDigit.val)
        (toPeanoList divisor Peano.zero)] at hbound
  exact Peano.add_lt_cancel_right hbound

theorem findQuotientDigit_spec (remainder divisor : Sequences.List Digit)
    (hrem : toPeanoList remainder Peano.zero <
        toPeanoList divisor Peano.zero * Peano.ten) :
    let result := findQuotientDigit remainder divisor
    let qDigit := result.1
    let nextRem := result.2
    toPeanoList remainder Peano.zero =
        toPeanoList divisor Peano.zero * qDigit.val +
          toPeanoList nextRem Peano.zero ∧
      toPeanoList nextRem Peano.zero < toPeanoList divisor Peano.zero := by
  unfold findQuotientDigit
  obtain ⟨heq, _hnlt, hmax⟩ :=
    findQuotientDigitAux_spec remainder divisor Peano.nine nine_lt_ten
  refine ⟨heq, ?_⟩
  cases hmax with
  | inl h_candidate =>
      apply findQuotientDigit_nextRem_lt heq
      rw [← h_candidate]
      exact hrem
  | inr hbound =>
      exact findQuotientDigit_nextRem_lt heq hbound

theorem toPeanoList_eq_zero_of_isEmpty
    {l : Sequences.List Digit} (h : Sequences.List.isEmpty l = true) :
    toPeanoList l Peano.zero = Peano.zero := by
  cases l with
  | empty => rfl
  | firstElement d ds =>
      unfold Sequences.List.isEmpty at h
      cases h

theorem divideWithRemainderAux_newQuotient_value
    (quotient : Sequences.List Digit) (qDigit : Digit) :
    let newQuotient :=
      if Sequences.List.isEmpty quotient then
        if qDigit.val = Peano.zero then
          quotient
        else
          Sequences.List.firstElement qDigit Sequences.List.empty
      else
        Sequences.List.append quotient qDigit
    toPeanoList newQuotient Peano.zero =
      toPeanoList quotient Peano.zero * Peano.ten + qDigit.val := by
  dsimp only
  by_cases h_empty : Sequences.List.isEmpty quotient = true
  · rw [if_pos h_empty]
    have hq_zero := toPeanoList_eq_zero_of_isEmpty h_empty
    by_cases h_digit_zero : qDigit.val = Peano.zero
    · rw [if_pos h_digit_zero, hq_zero, h_digit_zero,
        Peano.zero_multiply, Peano.add_zero]
    · rw [if_neg h_digit_zero, hq_zero, Peano.zero_multiply,
        Peano.zero_add]
      simp [toPeanoList]
  · rw [if_neg h_empty, toPeanoList_append]

theorem divideWithRemainderAux_step_algebra
    (q div rem qDigit nextRem d pow tail newQ : Peano)
    (hstep : rem * Peano.ten + d = div * qDigit + nextRem)
    (hq : newQ = q * Peano.ten + qDigit) :
    (q * div + rem) * (Peano.ten * pow) + (d * pow + tail) =
      (newQ * div + nextRem) * pow + tail := by
  rw [hq]
  calc
    (q * div + rem) * (Peano.ten * pow) + (d * pow + tail) =
        (q * div) * (Peano.ten * pow) +
          (rem * (Peano.ten * pow) + (d * pow + tail)) := by
      rw [Peano.multiply_distributive_over_add_left,
        Peano.add_associative]
    _ = (q * div) * (Peano.ten * pow) +
          ((rem * Peano.ten) * pow + (d * pow + tail)) := by
      rw [← Peano.multiply_associative rem Peano.ten pow]
    _ = (q * div) * (Peano.ten * pow) +
          ((rem * Peano.ten) * pow + d * pow + tail) := by
      rw [← Peano.add_associative
        ((rem * Peano.ten) * pow) (d * pow) tail]
    _ = (q * div) * (Peano.ten * pow) +
          ((rem * Peano.ten + d) * pow + tail) := by
      rw [← Peano.multiply_distributive_over_add_left
        (rem * Peano.ten) d pow]
    _ = (q * div) * (Peano.ten * pow) +
          ((div * qDigit + nextRem) * pow + tail) := by
      rw [hstep]
    _ = (q * div) * (Peano.ten * pow) +
          ((div * qDigit) * pow + nextRem * pow + tail) := by
      rw [Peano.multiply_distributive_over_add_left,
        ← Peano.add_associative]
    _ = ((q * Peano.ten) * div) * pow +
          ((qDigit * div) * pow + nextRem * pow + tail) := by
      rw [← Peano.multiply_associative (q * div) Peano.ten pow,
        Peano.multiply_associative q div Peano.ten,
        Peano.multiply_commutative div Peano.ten,
        ← Peano.multiply_associative q Peano.ten div,
        Peano.multiply_commutative div qDigit]
    _ = (((q * Peano.ten) * div) * pow +
          (qDigit * div) * pow) + (nextRem * pow + tail) := by
      rw [Peano.add_associative
          ((qDigit * div) * pow) (nextRem * pow) tail,
        ← Peano.add_associative
          (((q * Peano.ten) * div) * pow)
          ((qDigit * div) * pow) (nextRem * pow + tail)]
    _ = (((q * Peano.ten) * div + qDigit * div) * pow) +
          (nextRem * pow + tail) := by
      rw [← Peano.multiply_distributive_over_add_left
        ((q * Peano.ten) * div) (qDigit * div) pow]
    _ = (((q * Peano.ten) * div + qDigit * div) * pow +
          nextRem * pow) + tail := by
      rw [← Peano.add_associative]
    _ = (((q * Peano.ten) * div + qDigit * div) +
          nextRem) * pow + tail := by
      rw [← Peano.multiply_distributive_over_add_left]
    _ = ((q * Peano.ten + qDigit) * div + nextRem) *
          pow + tail := by
      rw [← Peano.multiply_distributive_over_add_left]

theorem divideWithRemainderAux_spec
  (dividend divisor remainder quotient : Sequences.List Digit)
  (hrem : toPeanoList remainder Peano.zero < toPeanoList divisor Peano.zero) :
  let result := divideWithRemainderAux dividend divisor remainder quotient
  let q := result.1
  let r := result.2
  (toPeanoList quotient Peano.zero * toPeanoList divisor Peano.zero +
     toPeanoList remainder Peano.zero) *
      Peano.tenPow dividend.length +
    toPeanoList dividend Peano.zero =
  toPeanoList divisor Peano.zero * toPeanoList q Peano.zero +
    toPeanoList r Peano.zero
  ∧
  toPeanoList r Peano.zero < toPeanoList divisor Peano.zero := by
  induction dividend generalizing remainder quotient with
  | empty =>
      dsimp [divideWithRemainderAux, toPeanoList, Sequences.List.length,
        Peano.tenPow]
      constructor
      · rw [Peano.multiply_one,
          Peano.multiply_commutative
            (toPeanoList quotient Peano.zero)
            (toPeanoList divisor Peano.zero)]
      · exact hrem
  | firstElement d ds ih =>
      unfold divideWithRemainderAux
      dsimp only
      let newRem := Sequences.List.append remainder d
      let qr := findQuotientDigit newRem divisor
      let qDigit := qr.1
      let nextRem := qr.2
      let newQuotient :=
        if Sequences.List.isEmpty quotient then
          if qDigit.val = Peano.zero then quotient
          else Sequences.List.firstElement qDigit Sequences.List.empty
        else Sequences.List.append quotient qDigit
      have h_newRem_value :
          toPeanoList newRem Peano.zero =
            toPeanoList remainder Peano.zero * Peano.ten + d.val := by
        dsimp [newRem]
        exact toPeanoList_append remainder d
      have h_newRem_bound :
          toPeanoList newRem Peano.zero <
            toPeanoList divisor Peano.zero * Peano.ten := by
        rw [h_newRem_value]
        have h1 :
            toPeanoList remainder Peano.zero * Peano.ten + d.val <
              toPeanoList remainder Peano.zero * Peano.ten + Peano.ten :=
          Peano.add_lt_add_left d.property
            (toPeanoList remainder Peano.zero * Peano.ten)
        have h2 :
            toPeanoList remainder Peano.zero * Peano.ten + Peano.ten =
              (toPeanoList remainder Peano.zero).successor * Peano.ten :=
          (Peano.successor_multiply
            (toPeanoList remainder Peano.zero) Peano.ten).symm
        have h3 :
            (toPeanoList remainder Peano.zero).successor * Peano.ten ≤
              toPeanoList divisor Peano.zero * Peano.ten :=
          Peano.multiply_le_mul_left
            (Peano.succ_le_of_lt hrem) Peano.ten
        rw [h2] at h1
        exact Peano.lt_of_lt_of_le h1 h3
      have h_digit_spec := findQuotientDigit_spec newRem divisor h_newRem_bound
      dsimp [qr, qDigit, nextRem] at h_digit_spec
      obtain ⟨h_digit_eq, h_nextRem_lt⟩ := h_digit_spec
      have h_newQuotient_value :
          toPeanoList newQuotient Peano.zero =
            toPeanoList quotient Peano.zero * Peano.ten + qDigit.val := by
        dsimp [newQuotient]
        exact divideWithRemainderAux_newQuotient_value quotient qDigit
      have h_step :
          toPeanoList remainder Peano.zero * Peano.ten + d.val =
            toPeanoList divisor Peano.zero * qDigit.val +
              toPeanoList nextRem Peano.zero := by
        rw [← h_newRem_value]
        exact h_digit_eq
      have ih_spec := ih nextRem newQuotient h_nextRem_lt
      dsimp [newQuotient, nextRem, qDigit, qr] at ih_spec
      obtain ⟨ih_eq, ih_lt⟩ := ih_spec
      constructor
      · rw [toPeanoList_firstElement]
        simp only [Sequences.List.length]
        rw [Peano.tenPow_add_one]
        have h_alg := divideWithRemainderAux_step_algebra
          (toPeanoList quotient Peano.zero)
          (toPeanoList divisor Peano.zero)
          (toPeanoList remainder Peano.zero)
          qDigit.val
          (toPeanoList nextRem Peano.zero)
          d.val
          (Peano.tenPow ds.length)
          (toPeanoList ds Peano.zero)
          (toPeanoList newQuotient Peano.zero)
          h_step h_newQuotient_value
        exact h_alg.trans ih_eq
      · exact ih_lt

theorem divideWithRemainder_spec (x y : Decimal) (hb : ¬ y ≈ zero) :
    let result := divideWithRemainder x y hb
    x.toPeano = y.toPeano * result.1.toPeano + result.2.toPeano ∧
      result.2.toPeano < y.toPeano := by
  unfold divideWithRemainder
  dsimp only
  cases h_aux : divideWithRemainderAux x.val y.val Sequences.List.empty Sequences.List.empty with
  | mk qDigits rDigits =>
      have hdiv : toPeanoList y.val Peano.zero ≠ Peano.zero := by
        change y.toPeano ≠ Peano.zero
        exact toPeano_ne_zero_of_not_equivalent_zero hb
      have hrem : toPeanoList Sequences.List.empty Peano.zero <
          toPeanoList y.val Peano.zero := by
        exact Peano.zero_lt_of_ne_zero _ hdiv
      have hspec := divideWithRemainderAux_spec x.val y.val
        Sequences.List.empty Sequences.List.empty hrem
      rw [h_aux] at hspec
      dsimp only at hspec
      obtain ⟨h_eq_raw, h_lt_raw⟩ := hspec
      have h_eq :
          x.toPeano =
            y.toPeano * toPeanoList qDigits Peano.zero +
              toPeanoList rDigits Peano.zero := by
        unfold toPeano
        simpa [toPeanoList, Peano.zero_multiply, Peano.zero_add] using h_eq_raw
      have h_lt :
          toPeanoList rDigits Peano.zero < y.toPeano := by
        unfold toPeano
        exact h_lt_raw
      simp only [normalizeList_toPeano]
      exact ⟨h_eq, h_lt⟩

theorem divideWithRemainder_toPeano (x y : Decimal) (hb : ¬ y ≈ zero)
    {a b : Decimal}
    (h : divideWithRemainder x y hb = (a, b)) :
    ∃ h2, Peano.divideWithRemainder x.toPeano y.toPeano h2 =
      (a.toPeano, b.toPeano) := by
  have hspec := divideWithRemainder_spec x y hb
  rw [h] at hspec
  dsimp only at hspec
  obtain ⟨h_eq, h_lt⟩ := hspec
  refine ⟨toPeano_ne_zero_of_not_equivalent_zero hb, ?_⟩
  exact Peano.divideWithRemainder_eq_of_mul_add
    x.toPeano y.toPeano
    (toPeano_ne_zero_of_not_equivalent_zero hb)
    a.toPeano b.toPeano h_lt h_eq

def divide (a b : Decimal) (h : Divisible a b) : Decimal :=
  (divideWithRemainder a b h.1).1

theorem divide_toPeano (x y : Decimal) (h : Divisible x y) :
    ∃ h2, (divide x y h).toPeano = Peano.divide x.toPeano y.toPeano h2 := by
  let h2 := (divisibleToPeano x y).mp h
  refine ⟨h2, ?_⟩
  have hspec := divideWithRemainder_spec x y h.1
  dsimp only at hspec
  obtain ⟨heq, hlt⟩ := hspec
  have hx : x.toPeano = y.toPeano * Peano.divide x.toPeano y.toPeano h2 :=
    (Peano.multiply_divide x.toPeano y.toPeano h2).symm
  have hunique := Peano.div_rem_unique y.toPeano
    (Peano.divide x.toPeano y.toPeano h2) Peano.zero
    (divideWithRemainder x y h.1).1.toPeano
    (divideWithRemainder x y h.1).2.toPeano
    (Peano.zero_lt_of_ne_zero y.toPeano h2.1)
    hlt
    (by rw [Peano.add_zero, ← hx, heq])
  change (divideWithRemainder x y h.1).1.toPeano =
    Peano.divide x.toPeano y.toPeano h2
  exact hunique.1.symm

/-- Reinterpret a positive ordinal Decimal as a cardinal Decimal with the same digits. -/
def fromOrdinal (a : OrdinalNatural.Decimal) : Decimal :=
  ⟨a.val, hasNonZero_ne_empty a.property⟩

theorem toPeanoList_eq_toCardinalList (l : Sequences.List Digit) (acc : Peano) :
    toPeanoList l acc = OrdinalNatural.Decimal.toCardinalList l acc := by
  induction l generalizing acc with
  | empty =>
    rfl
  | firstElement _ _ ih =>
    exact ih _

/-- Digit reinterpretation preserves the underlying Peano value. -/
theorem fromOrdinal_toPeano (a : OrdinalNatural.Decimal) :
    (fromOrdinal a).toPeano = a.toCardinalPeano :=
  toPeanoList_eq_toCardinalList a.val Peano.zero

/-- `fromOrdinal` agrees with `Peano.fromOrdinal` on the Peano embedding. -/
theorem fromOrdinal_toPeano_eq_fromOrdinal_peano (a : OrdinalNatural.Decimal) :
    (fromOrdinal a).toPeano = Peano.fromOrdinal a.toPeano := by
  rw [fromOrdinal_toPeano]
  unfold OrdinalNatural.Decimal.toPeano
  exact (Peano.fromOrdinal_toOrdinal (OrdinalNatural.Decimal.toCardinalPeano a)
    (OrdinalNatural.Decimal.toCardinalPeano_ne_zero a)).symm

/-- Reinterpreting a positive ordinal Decimal never yields a cardinal Decimal
equivalent to zero. -/
theorem fromOrdinal_not_equivalent_zero (a : OrdinalNatural.Decimal) :
    ¬ fromOrdinal a ≈ zero := by
  intro h
  have hpeano : Peano.fromOrdinal a.toPeano = Peano.zero := by
    rw [← fromOrdinal_toPeano_eq_fromOrdinal_peano, toPeano_eq_of_equivalent h,
      toPeano_zero]
  exact Peano.fromOrdinal_ne_zero a.toPeano hpeano

/-- Anything ≤ zero is equivalent to zero. -/
theorem eq_zero_of_le_zero (a : Decimal) (h : a ≤ zero) : a ≈ zero := by
  cases h with
  | inl hlt =>
    exact (Peano.not_lt_zero a.toPeano hlt).elim
  | inr heq =>
    exact heq

theorem toPeano_one : toPeano one = Peano.one := by
  simp only [toPeano, toPeanoList, one, oneDigit, Peano.zero_multiply, Peano.zero_add]

end Decimal

end ZeroMath.Numbers.CardinalNatural
