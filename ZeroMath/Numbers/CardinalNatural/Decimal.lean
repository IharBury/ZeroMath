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
  successorList predecessorList subtractAlignedLists
  LessThanAlignedLists isLessThanAlignedLists
  isLessThanAlignedLists_iff_lessThanAlignedLists LessThanAlignedLists_congr
  addAlignedLists addAlignedLists_commutative
  addPartialListDigit addListDigit multiplyDigitsPeano multiplyDigits
  addListDigit_multiplyDigits_ne_empty addListDigit_multiplyDigits_not_three_or_more
  multiplyPartialListByDigit multiplyListByDigit multiplyList
  HasNonZero AllZero decidableAllZero
  allZero_of_predecessorList_borrow_true successorList_predecessorList
  successorList_ne_empty_of_carry_false predecessorList_ne_empty_of_borrow_false
  hasNonZero_ne_empty hasNonZero hasNonZero_tail_of_zero_first NonEmptyList
  normalizeList toCardinalNaturalPeano
  toCardinalNaturalPeano_acc_split toCardinalNaturalPeano_firstElement
  toCardinalNaturalPeano_padAtStart_zeroDigit
  toCardinalNaturalPeano_padAtStartToSameLength_fst
  toCardinalNaturalPeano_padAtStartToSameLength_snd
  toCardinalNaturalPeano_lt_tenPow
  LessThanAlignedLists_toCardinalNaturalPeano_lt
  LessThanAlignedLists_of_toCardinalNaturalPeano_lt
  toCardinalNaturalPeano_inj_sameLength toCardinalNaturalPeano_padAtEnd
  toCardinalNaturalPeano_addAlignedLists_result toCardinalNaturalPeano_addListDigit
  toCardinalNaturalPeano_multiplyDigitsPeano toCardinalNaturalPeano_multiplyDigits
  toCardinalNaturalPeano_addListDigit_multiplyDigits
  toCardinalNaturalPeano_multiplyListByDigit
  addPartialListDigit_spec addAlignedLists_spec
  multiplyPartialListByDigit_spec multiplyList_spec
  addAlignedLists_eq_of_swapped addAlignedLists_after_padding_commutative
  subtractAlignedLists_borrow_false_of_lessThan
  toCardinalNaturalPeano_eq_zero_of_isEmpty
  isLessThanLists subtractLists
  isLessThanLists_iff_toCardinalNaturalPeano_lt isLessThanLists_eq_false_iff_not_lt
  subtractLists_spec
  findQuotientDigitAux findQuotientDigit
  findQuotientDigitAux_spec findQuotientDigit_spec findQuotientDigit_nextRem_lt
  divideWithRemainderAux
  toCardinalNaturalPeano_append
  divideWithRemainderAux_newQuotient_value divideWithRemainderAux_step_algebra
  divideWithRemainderAux_spec
  toCardinalNaturalPeano_ne_zero_of_acc_ne_zero
  toCardinalNaturalPeano_ge_tenPow_of_ne_zero
  toCardinalNaturalPeano_zero_of_allZero toCardinalNaturalPeano_normalizeList
  allZero_or_hasNonZero not_allZero_of_hasNonZero
  toCardinalNaturalPeano_ne_zero_of_hasNonZero
  toCardinalNaturalPeano_ne_zero_of_not_allZero
  hasNonZero_of_toCardinalNaturalPeano_ne_zero
  predecessorList_successorList
  subtractAlignedLists_spec_calc_false_true subtractAlignedLists_spec_calc_false_false
  subtractAlignedLists_spec_calc_true_true subtractAlignedLists_spec_calc_true_false
  subtractAlignedLists_spec subtractAlignedLists_borrow_false_of_not_lt
  successor_carry_accumulator successorList_toCardinalNaturalPeano
  normalizeList_cons_zero
  padAtStartToSameLength_fst_ne_empty padAtStartToSameLength_fst_ne_empty_of_either
  addAlignedLists_fst_ne_empty addAlignedLists_ne_empty
  subtractAlignedLists_fst_ne_empty subtractAlignedLists_ne_empty
  subtractAlignedLists_borrow_false_of_eq
  multiplyPartialListByDigit_fst_ne_empty multiplyListByDigit_ne_empty
  multiplyList_fst_ne_empty
  hasNonZero_of_hasNonZero_bool hasNonZero_bool_eq_true_of_hasNonZero
  allZero_of_not_hasNonZero_bool
  hasNonZero_of_successorList_carry_true hasNonZero_of_successorList_carry_false
  hasNonZero_padAtStartToSameLength_fst
  addAlignedLists_digit_sum_ne_zero_of_left_ne_zero
  addAlignedLists_digit_sum_ne_zero_of_carry_true
  hasNonZero_of_addAlignedLists_carry_true hasNonZero_of_addAlignedLists_carry_false
  hasNonZero_of_subtractAlignedLists_borrow_true
  hasNonZero_of_subtractAlignedLists_borrow_false_of_lessThan
  hasNonZero_multiplyList)

def zero : Decimal := ⟨Sequences.List.firstElement zeroDigit Sequences.List.empty, by simp⟩
def one : Decimal := ⟨Sequences.List.firstElement oneDigit Sequences.List.empty, by simp⟩

def isNormalized (d : Decimal) : Bool :=
  match d with
  | ⟨.empty, _⟩ => by contradiction
  | ⟨.firstElement digit .empty, _⟩ => true
  | ⟨.firstElement digit _, _⟩ => decide (digit.val ≠ CardinalNatural.Peano.zero)

def normalize (a : Decimal) : Decimal :=
  normalizeList a.val a.property

def toPeano (d : Decimal) : Peano :=
  toCardinalNaturalPeano d.val Peano.zero

theorem normalizeList_toPeano (a : Sequences.List Digit) (ha : a ≠ Sequences.List.empty) :
  toPeano (normalizeList a ha) = toCardinalNaturalPeano a Peano.zero :=
  Digits.toCardinalNaturalPeano_normalizeList a ha

theorem normalize_toPeano (x : Decimal) : x.normalize.toPeano = x.toPeano := by
  unfold normalize toPeano
  exact normalizeList_toPeano x.val x.property

theorem normalizeList_isNormalized (a : Sequences.List Digit) (ha : a ≠ Sequences.List.empty) :
  isNormalized (normalizeList a ha) = true := by
  induction a with
  | empty =>
      exact False.elim (ha rfl)
  | firstElement d ds ih =>
      by_cases hd : d.val = CardinalNatural.Peano.zero
      · by_cases hds : ds = Sequences.List.empty
        · subst hds
          simp [normalizeList, hd, isNormalized]
        · rw [normalizeList_cons_zero d ds hd hds]
          exact ih hds
      · have hnorm : normalizeList (Sequences.List.firstElement d ds) (by simp) =
            ⟨Sequences.List.firstElement d ds, by simp⟩ := by
          simp [normalizeList, hd]
        rw [hnorm]
        cases ds with
        | empty =>
            rfl
        | firstElement d' ds' =>
            simp [isNormalized, hd]

theorem normalize_isNormalized (d : Decimal) : d.normalize.isNormalized = true := by
  unfold normalize
  exact normalizeList_isNormalized d.val d.property

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
      have hsucc := successorList_toCardinalNaturalPeano d.val Peano.zero
      rw [h] at hsucc
      dsimp only at hsucc
      exact hsucc
  · next digits h =>
      have hsucc := successorList_toCardinalNaturalPeano d.val Peano.zero
      rw [h] at hsucc
      dsimp only at hsucc
      exact hsucc

theorem normalizeList_eq_zero_of_allZero {a : Sequences.List Digit}
    (ha : a ≠ Sequences.List.empty) (h : AllZero a) :
  normalizeList a ha = zero :=
  Subtype.ext (congrArg Subtype.val (Digits.normalizeList_eq_zero_of_allZero ha h))

theorem equivalent_zero_of_allZero {a : Sequences.List Digit}
  (ha : a ≠ Sequences.List.empty) (h : AllZero a) :
  Equivalent ⟨a, ha⟩ zero := by
  unfold Equivalent normalize
  exact normalizeList_eq_zero_of_allZero ha h

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
theorem toPeano_zero : toPeano zero = Peano.zero := rfl

theorem tenPow_pos (n : Peano) : Peano.zero < Peano.tenPow n := by
  induction n with
  | zero => exact Peano.LessThan.base
  | successor n ih => exact Peano.lt_trans ih (Peano.tenPow_lt_succ n)

theorem eq_zero_of_normalized_toPeano_zero {d : Decimal}
    (hd : d.isNormalized = true) (h : toPeano d = Peano.zero) : d = zero := by
  obtain ⟨val, prop⟩ := d
  cases val with
  | empty => exact absurd rfl prop
  | firstElement digit rest =>
    cases rest with
    | empty =>
      simp only [toPeano, toCardinalNaturalPeano, Peano.zero_multiply, Peano.zero_add] at h
      apply Subtype.ext
      show Sequences.List.firstElement digit Sequences.List.empty =
        Sequences.List.firstElement zeroDigit Sequences.List.empty
      exact congrArg (fun v => Sequences.List.firstElement v Sequences.List.empty)
        (Subtype.ext h)
    | firstElement d' ds' =>
      simp only [isNormalized, decide_eq_true_eq] at hd
      have h' :
          toCardinalNaturalPeano
            (Sequences.List.firstElement digit (Sequences.List.firstElement d' ds'))
            Peano.zero = Peano.zero := by
        simpa [toPeano] using h
      rw [toCardinalNaturalPeano_firstElement] at h'
      let rest := Sequences.List.firstElement d' ds'
      have hge := toCardinalNaturalPeano_ge_tenPow_of_ne_zero digit rest hd
      have hlt : Peano.zero <
          digit.val * Peano.tenPow rest.length + toCardinalNaturalPeano rest Peano.zero :=
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
            toCardinalNaturalPeano (Sequences.List.firstElement da das) Peano.zero =
            toCardinalNaturalPeano (Sequences.List.firstElement db dbs) Peano.zero := heq
        rw [toCardinalNaturalPeano_firstElement, toCardinalNaturalPeano_firstElement] at heq
        have h_len : das.length = dbs.length := by
          cases Peano.trichotomy_or das.length dbs.length with
          | inl hlt =>
            have hval_lt :
                da.val * Peano.tenPow das.length + toCardinalNaturalPeano das Peano.zero <
                Peano.ten * Peano.tenPow das.length := by
              have hstep1 :
                  da.val * Peano.tenPow das.length + toCardinalNaturalPeano das Peano.zero <
                  da.val * Peano.tenPow das.length + Peano.tenPow das.length :=
                Peano.add_lt_add_left (toCardinalNaturalPeano_lt_tenPow das) _
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
                db.val * Peano.tenPow dbs.length + toCardinalNaturalPeano dbs Peano.zero :=
              toCardinalNaturalPeano_ge_tenPow_of_ne_zero db dbs hdb_ne
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
                  db.val * Peano.tenPow dbs.length + toCardinalNaturalPeano dbs Peano.zero <
                  Peano.ten * Peano.tenPow dbs.length := by
                have hstep1 :
                    db.val * Peano.tenPow dbs.length + toCardinalNaturalPeano dbs Peano.zero <
                    db.val * Peano.tenPow dbs.length + Peano.tenPow dbs.length :=
                  Peano.add_lt_add_left (toCardinalNaturalPeano_lt_tenPow dbs) _
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
                  da.val * Peano.tenPow das.length + toCardinalNaturalPeano das Peano.zero :=
                toCardinalNaturalPeano_ge_tenPow_of_ne_zero da das hda_ne
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
          toCardinalNaturalPeano_inj_sameLength hsl heq_raw
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
    exact h_predecessor_toPeano.trans (Peano.predecessor_congr h2 h2' h_successor_toPeano)
  obtain ⟨h3, h_predecessor_successor⟩ := Peano.predecessor_successor x.toPeano
  have h_predecessor_congr :
      (x.toPeano.successor).predecessor h2' = (x.toPeano.successor).predecessor h3 :=
    Peano.predecessor_congr h2' h3 rfl
  exact h_predecessor_toPeano'.trans (h_predecessor_congr.trans h_predecessor_successor)

def isLessThan (x y : Decimal) : Bool :=
  let pair := Sequences.List.padAtStartToSameLength x.val y.val zeroDigit
  isLessThanAlignedLists pair.1 pair.2
    (Sequences.List.padAtStartToSameLength_sameLength x.val y.val zeroDigit)
def LessThan (x y : Decimal) : Prop :=
  x.toPeano < y.toPeano

theorem toPeano_lt_of_lessThanAlignedLists_padded {a b : Decimal}
    (h : LessThanAlignedLists
      (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).1
      (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).2
      (Sequences.List.padAtStartToSameLength_sameLength a.val b.val zeroDigit)) :
    a.toPeano < b.toPeano := by
  have h_padded := LessThanAlignedLists_toCardinalNaturalPeano_lt
    (Sequences.List.padAtStartToSameLength_sameLength a.val b.val zeroDigit) h
  change toCardinalNaturalPeano a.val Peano.zero < toCardinalNaturalPeano b.val Peano.zero
  rw [← toCardinalNaturalPeano_padAtStartToSameLength_fst a.val b.val,
    ← toCardinalNaturalPeano_padAtStartToSameLength_snd a.val b.val]
  exact h_padded

theorem lessThanAlignedLists_padded_of_toPeano_lt {a b : Decimal}
    (h : a.toPeano < b.toPeano) :
    LessThanAlignedLists
      (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).1
      (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).2
      (Sequences.List.padAtStartToSameLength_sameLength a.val b.val zeroDigit) := by
  apply LessThanAlignedLists_of_toCardinalNaturalPeano_lt
  change toCardinalNaturalPeano (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).1
      Peano.zero <
    toCardinalNaturalPeano (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).2
      Peano.zero
  rw [toCardinalNaturalPeano_padAtStartToSameLength_fst a.val b.val,
    toCardinalNaturalPeano_padAtStartToSameLength_snd a.val b.val]
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
theorem add_toPeano (x y : Decimal) :
  (x + y).toPeano = x.toPeano + y.toPeano := by
  change toCardinalNaturalPeano (add x y).val Peano.zero =
    toCardinalNaturalPeano x.val Peano.zero +
      toCardinalNaturalPeano y.val Peano.zero
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
      change toCardinalNaturalPeano
        (Sequences.List.firstElement ⟨Peano.one, Peano.one_lt_ten⟩ digits)
        Peano.zero = _
      rw [toCardinalNaturalPeano_firstElement, h_length, Peano.one_multiply,
        Peano.add_commutative, h_value,
        toCardinalNaturalPeano_padAtStartToSameLength_fst,
        toCardinalNaturalPeano_padAtStartToSameLength_snd]
  · next digits h_add =>
      have h_spec := addAlignedLists_spec
        (Sequences.List.padAtStartToSameLength_sameLength x.val y.val zeroDigit)
      rw [h_add] at h_spec
      dsimp only at h_spec
      obtain ⟨_, h_value⟩ := h_spec
      simp at h_value
      rw [h_value, toCardinalNaturalPeano_padAtStartToSameLength_fst,
        toCardinalNaturalPeano_padAtStartToSameLength_snd]

theorem add_associative (a b c : Decimal) : a + b + c ≈ a + (b + c) := by
  apply equivalent_of_toPeano_eq
  rw [add_toPeano, add_toPeano, add_toPeano, add_toPeano, Peano.add_associative]

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

theorem padAtStartToSameLength_eq_of_equivalent {a b : Decimal} (h : a ≈ b) :
  (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).1 =
    (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).2 := by
  have heq :
      toCardinalNaturalPeano (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).1 Peano.zero =
        toCardinalNaturalPeano (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).2 Peano.zero := by
    rw [toCardinalNaturalPeano_padAtStartToSameLength_fst, toCardinalNaturalPeano_padAtStartToSameLength_snd]
    exact toPeano_eq_of_equivalent h
  exact toCardinalNaturalPeano_inj_sameLength
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

theorem toPeano_subtract (x y : Decimal) (h : y ≤ x) :
  toPeano (subtract x y h) + toPeano y = toPeano x := by
  change toCardinalNaturalPeano (subtract x y h).val Peano.zero +
      toCardinalNaturalPeano y.val Peano.zero =
    toCardinalNaturalPeano x.val Peano.zero
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
            rw [← toCardinalNaturalPeano_padAtStartToSameLength_fst x.val y.val,
              ← toCardinalNaturalPeano_padAtStartToSameLength_snd x.val y.val]
            change toCardinalNaturalPeano digits Peano.zero +
                toCardinalNaturalPeano pair.2 Peano.zero =
              toCardinalNaturalPeano pair.1 Peano.zero
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
        have h_ap : toPeano a = toCardinalNaturalPeano pair.1 Peano.zero := by
          unfold toPeano
          exact (toCardinalNaturalPeano_padAtStartToSameLength_fst a.val b.val).symm
        have h_bp : toPeano b = toCardinalNaturalPeano pair.2 Peano.zero := by
          unfold toPeano
          exact (toCardinalNaturalPeano_padAtStartToSameLength_snd a.val b.val).symm
        have h_d_lt : toCardinalNaturalPeano digits Peano.zero < Peano.tenPow pair.1.length := by
          have h_len : digits.length = pair.1.length := by
            have sp := subtractAlignedLists_spec h_same
            have h_call : subres = subtractAlignedLists pair.1 pair.2 h_same := rfl
            rw [← h_call] at sp
            simp [h_borrow] at sp
            obtain ⟨hlen, _⟩ := sp
            exact hlen
          have t := toCardinalNaturalPeano_lt_tenPow digits
          rw [h_len] at t
          exact t
        have h_list_lt : toCardinalNaturalPeano pair.1 Peano.zero <
            toCardinalNaturalPeano pair.2 Peano.zero := by
          have sp_val := (subtractAlignedLists_spec h_same).2
          have h_call : subres = subtractAlignedLists pair.1 pair.2 h_same := rfl
          rw [← h_call] at sp_val
          simp [h_borrow] at sp_val
          have ineq : toCardinalNaturalPeano pair.1 Peano.zero + Peano.tenPow pair.1.length <
                Peano.tenPow pair.1.length + toCardinalNaturalPeano pair.2 Peano.zero := by
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
              rw [← toCardinalNaturalPeano_padAtStartToSameLength_snd a.val b.val,
                ← toCardinalNaturalPeano_padAtStartToSameLength_fst a.val b.val, ← h_val]
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
      change toCardinalNaturalPeano
          (subtractAlignedLists
            (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).1
            (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).2
            (Sequences.List.padAtStartToSameLength_sameLength a.val b.val zeroDigit)).1
          Peano.zero +
        toCardinalNaturalPeano b.val Peano.zero =
        toCardinalNaturalPeano a.val Peano.zero
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
          rw [← toCardinalNaturalPeano_padAtStartToSameLength_fst a.val b.val,
            ← toCardinalNaturalPeano_padAtStartToSameLength_snd a.val b.val]
          change toCardinalNaturalPeano digits Peano.zero +
              toCardinalNaturalPeano (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).2
                Peano.zero =
            toCardinalNaturalPeano (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).1
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

def multiply (a b : Decimal) : Decimal :=
  ⟨(multiplyList a.val b.val).1, multiplyList_fst_ne_empty a.val b.val a.property b.property⟩

instance : Mul Decimal := ⟨multiply⟩
theorem multiply_toPeano (a b : Decimal) :
    toPeano (a * b) = a.toPeano * b.toPeano := by
  unfold toPeano
  change toCardinalNaturalPeano (multiply a b).val Peano.zero =
    toCardinalNaturalPeano a.val Peano.zero * toCardinalNaturalPeano b.val Peano.zero
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

def divideWithRemainder (a b : Decimal) (_hb : ¬ b ≈ zero) : Decimal × Decimal :=
  let (qDigits, rDigits) := divideWithRemainderAux a.val b.val .empty .empty
  (if hq : qDigits = Sequences.List.empty then zero else normalizeList qDigits hq,
   if hr : rDigits = Sequences.List.empty then zero else normalizeList rDigits hr)

theorem divideWithRemainder_spec (x y : Decimal) (hb : ¬ y ≈ zero) :
    let result := divideWithRemainder x y hb
    x.toPeano = y.toPeano * result.1.toPeano + result.2.toPeano ∧
      result.2.toPeano < y.toPeano := by
  unfold divideWithRemainder
  dsimp only
  cases h_aux : divideWithRemainderAux x.val y.val Sequences.List.empty Sequences.List.empty with
  | mk qDigits rDigits =>
      have hdiv : toCardinalNaturalPeano y.val Peano.zero ≠ Peano.zero := by
        change y.toPeano ≠ Peano.zero
        exact toPeano_ne_zero_of_not_equivalent_zero hb
      have hrem : toCardinalNaturalPeano Sequences.List.empty Peano.zero <
          toCardinalNaturalPeano y.val Peano.zero := by
        exact Peano.zero_lt_of_ne_zero _ hdiv
      have hspec := divideWithRemainderAux_spec x.val y.val
        Sequences.List.empty Sequences.List.empty hrem
      rw [h_aux] at hspec
      dsimp only at hspec
      obtain ⟨h_eq_raw, h_lt_raw⟩ := hspec
      have h_eq :
          x.toPeano =
            y.toPeano * toCardinalNaturalPeano qDigits Peano.zero +
              toCardinalNaturalPeano rDigits Peano.zero := by
        unfold toPeano
        simpa [toCardinalNaturalPeano, Peano.zero_multiply, Peano.zero_add] using h_eq_raw
      have h_lt :
          toCardinalNaturalPeano rDigits Peano.zero < y.toPeano := by
        unfold toPeano
        exact h_lt_raw
      have hq :
          toPeano (if hq : qDigits = Sequences.List.empty then zero
            else normalizeList qDigits hq) =
            toCardinalNaturalPeano qDigits Peano.zero := by
        by_cases hq : qDigits = Sequences.List.empty
        · simp [hq, toPeano, toCardinalNaturalPeano, zero, zeroDigit]
        · simp [hq]
          exact normalizeList_toPeano qDigits hq
      have hr :
          toPeano (if hr : rDigits = Sequences.List.empty then zero
            else normalizeList rDigits hr) =
            toCardinalNaturalPeano rDigits Peano.zero := by
        by_cases hr : rDigits = Sequences.List.empty
        · simp [hr, toPeano, toCardinalNaturalPeano, zero, zeroDigit]
        · simp [hr]
          exact normalizeList_toPeano rDigits hr
      simp only [hq, hr]
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

/-- Digit reinterpretation preserves the underlying Peano value. -/
theorem fromOrdinal_toPeano (a : OrdinalNatural.Decimal) :
    (fromOrdinal a).toPeano = a.toCardinalPeano :=
  rfl

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
  simp only [toPeano, toCardinalNaturalPeano, one, oneDigit, Peano.zero_multiply, Peano.zero_add]

end Decimal

end ZeroMath.Numbers.CardinalNatural
