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
  hasNonZero_ne_empty length_ne_zero_of_hasNonZero hasNonZero hasNonZero_tail_of_zero_first NonEmptyList
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
  appendRootDigit appendRootDigit_toCardinalNaturalPeano
  listVal listVal_empty listVal_append listVal_append_zeroDigit listVal_appendRootDigit
  firstRootGroupSize firstRootGroupSize_ne_zero firstRootGroupSize_le firstRootGroupSize_mod
  rootPad
  findRootDigitAux findRootDigit rootWithRemainderAux
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
  hasNonZero_multiplyList
  isNormalizedList isNormalizedNonZeroList
  normalizeList_isNormalized normalizeList_isNormalizedNonZero
  toCardinalNaturalPeano_lt_of_lessThanAlignedLists_padded
  lessThanAlignedLists_padded_of_toCardinalNaturalPeano_lt
  lessThanAlignedLists_padded_snd_fst_of_toCardinalNaturalPeano_lt
  padAtStartToSameLength_eq_of_toCardinalNaturalPeano_eq
  subtractAlignedLists_borrow_false_of_toCardinalNaturalPeano_eq
  subtractAlignedLists_borrow_true_of_toCardinalNaturalPeano_lt
  addLists addLists_of_aligned_result addLists_commutative
  addLists_ne_empty hasNonZero_addLists toCardinalNaturalPeano_addLists
  empty_of_predecessorList_borrow_true_allZero successorList_spec
  toCardinalNaturalPeano_of_successorList
  not_allZero_normalizeList_of_not_allZero successorList_carry_false_of_allZero
  not_allZero_cons_zero_of_successorList_carry predecessorList_of_successorList_carry
  normalizeList_of_successorList_allZero
  toCardinalNaturalPeano_even_iff_lastElement
  toCardinalNaturalPeano_lt_ten_mul_tenPow
  leadingDigit_ne_zero_of_isNormalizedNonZeroList
  leadingDigit_ne_zero_of_isNormalizedList_ne_zero
  eq_zeroDigit_singleton_of_isNormalizedList_toCardinalNaturalPeano_zero
  toCardinalNaturalPeano_inj_of_leading_ne_zero
  RepresentsOne decidableRepresentsOne
  representsOne_of_predecessorList_borrow_false_allZero
  hasNonZero_of_representsOne normalizeList_eq_oneDigit_of_representsOne
  hasNonZero_of_predecessorList_borrow_false_of_not_representsOne)

def zero : Decimal := ⟨Sequences.List.firstElement zeroDigit Sequences.List.empty, by simp⟩
def one : Decimal := ⟨Sequences.List.firstElement oneDigit Sequences.List.empty, by simp⟩

def isNormalized (d : Decimal) : Bool := isNormalizedList d.val

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

theorem normalize_isNormalized (d : Decimal) : d.normalize.isNormalized = true := by
  unfold normalize isNormalized
  exact Digits.normalizeList_isNormalized d.val d.property

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

def two : Decimal := successor one

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

theorem toPeano_one : toPeano one = Peano.one := by
  simp only [toPeano, toCardinalNaturalPeano, one, oneDigit, Peano.zero_multiply, Peano.zero_add]

theorem toPeano_two : toPeano two = Peano.two := by
  unfold two Peano.two
  rw [successor_toPeano, toPeano_one]

theorem eq_zero_of_normalized_toPeano_zero {d : Decimal}
    (hd : d.isNormalized = true) (h : toPeano d = Peano.zero) : d = zero := by
  obtain ⟨val, prop⟩ := d
  have hlist :
      val = Sequences.List.firstElement zeroDigit Sequences.List.empty := by
    simpa [toPeano, isNormalized] using
      eq_zeroDigit_singleton_of_isNormalizedList_toCardinalNaturalPeano_zero prop hd h
  exact Subtype.ext hlist

theorem leadingDigit_ne_zero_of_normalized_ne_zero
    {digit : Digit} {rest : Sequences.List Digit}
    {hprop : Sequences.List.firstElement digit rest ≠ Sequences.List.empty}
    (hd : isNormalized ⟨Sequences.List.firstElement digit rest, hprop⟩ = true)
    (hne : (⟨Sequences.List.firstElement digit rest, hprop⟩ : Decimal) ≠ zero) :
    digit.val ≠ Peano.zero := by
  apply leadingDigit_ne_zero_of_isNormalizedList_ne_zero
  · simpa [isNormalized] using hd
  · intro hzero
    apply hne
    exact eq_zero_of_normalized_toPeano_zero hd (by simpa [toPeano] using hzero)

-- Normalized Decimals with the same toPeano value are equal
theorem normalize_inj {a b : Decimal}
    (ha : a.isNormalized = true) (hb : b.isNormalized = true)
    (heq : toPeano a = toPeano b) : a = b := by
  by_cases ha0 : toPeano a = Peano.zero
  · rw [eq_zero_of_normalized_toPeano_zero ha ha0,
        eq_zero_of_normalized_toPeano_zero hb (heq.symm.trans ha0)]
  · have hb0 : toPeano b ≠ Peano.zero := by
      intro h; exact ha0 (heq.trans h)
    obtain ⟨val_a, prop_a⟩ := a
    obtain ⟨val_b, prop_b⟩ := b
    cases val_a with
    | empty => exact absurd rfl prop_a
    | firstElement da das =>
      cases val_b with
      | empty => exact absurd rfl prop_b
      | firstElement db dbs =>
        have hda_ne : da.val ≠ Peano.zero :=
          leadingDigit_ne_zero_of_isNormalizedList_ne_zero
            (by simpa [isNormalized] using ha)
            (by simpa [toPeano] using ha0)
        have hdb_ne : db.val ≠ Peano.zero :=
          leadingDigit_ne_zero_of_isNormalizedList_ne_zero
            (by simpa [isNormalized] using hb)
            (by simpa [toPeano] using hb0)
        exact Subtype.ext
          (toCardinalNaturalPeano_inj_of_leading_ne_zero hda_ne hdb_ne
            (by simpa [toPeano] using heq))

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

/-- The Peano embedding of `n.predecessor` is `k` when `n.toPeano` is
`successor k`. -/
theorem predecessor_toPeano_eq_of_succ (n : Decimal)
    (hne : ¬ n ≈ zero) (k : Peano)
    (hn : n.toPeano = Peano.successor k)
    (hne_peano : n.toPeano ≠ Peano.zero)
    (hpred : (n.predecessor hne).toPeano = n.toPeano.predecessor hne_peano) :
    (n.predecessor hne).toPeano = k := by
  rw [hpred]
  apply Eq.symm
  apply Peano.successor_injective
  rw [Peano.successor_predecessor n.toPeano hne_peano, hn]

theorem toPeano_eq_of_equivalent {a b : Decimal} (h : a ≈ b) :
  a.toPeano = b.toPeano := by
  have h_eq : a.normalize = b.normalize := h
  rw [← normalize_toPeano a, ← normalize_toPeano b, h_eq]

/-- A cardinal Decimal whose Peano embedding is nonzero is not equivalent to
zero. -/
theorem not_equivalent_zero_of_toPeano_ne_zero (n : Decimal)
    (hne : n.toPeano ≠ Peano.zero) :
    ¬ n ≈ zero := by
  intro heq
  exact hne ((toPeano_eq_of_equivalent heq).trans toPeano_zero)

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
    a.toPeano < b.toPeano :=
  toCardinalNaturalPeano_lt_of_lessThanAlignedLists_padded a.val b.val h

theorem lessThanAlignedLists_padded_of_toPeano_lt {a b : Decimal}
    (h : a.toPeano < b.toPeano) :
    LessThanAlignedLists
      (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).1
      (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).2
      (Sequences.List.padAtStartToSameLength_sameLength a.val b.val zeroDigit) :=
  lessThanAlignedLists_padded_of_toCardinalNaturalPeano_lt a.val b.val h

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

/-- Inequality is preserved when the left side is replaced by an equivalent
Decimal. -/
theorem le_of_equivalent_of_le {a b c : Decimal}
    (hab : a ≈ b) (hbc : b ≤ c) : a ≤ c :=
  le_trans (Or.inr hab) hbc

def add (a b : Decimal) : Decimal :=
  ⟨addLists a.val b.val, addLists_ne_empty a.property⟩

instance : Add Decimal where
  add := add

theorem add_val_of_aligned_result (a b : Decimal) (digits : Sequences.List Digit) (carry : Bool)
  (h : addAlignedLists
    (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).1
    (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).2
    (Sequences.List.padAtStartToSameLength_sameLength a.val b.val zeroDigit) = ⟨digits, carry⟩) :
  (a + b).val = if carry then
    Sequences.List.firstElement oneDigit digits
  else digits := by
  change (add a b).val = _
  unfold add
  exact addLists_of_aligned_result a.val b.val digits carry h

theorem add_commutative (a b : Decimal) : a + b = b + a := by
  apply Subtype.ext
  exact addLists_commutative a.val b.val

theorem equivalent_add_commutative (a b : Decimal) : a + b ≈ b + a := by
  rw [add_commutative]
  rfl
theorem add_toPeano (x y : Decimal) :
  (x + y).toPeano = x.toPeano + y.toPeano := by
  change toCardinalNaturalPeano (add x y).val Peano.zero =
    toCardinalNaturalPeano x.val Peano.zero +
      toCardinalNaturalPeano y.val Peano.zero
  unfold add
  exact toCardinalNaturalPeano_addLists x.val y.val

/-- Addition on the right respects Decimal equivalence. -/
theorem equivalent_add_right {a b c : Decimal} (h : a ≈ b) : a + c ≈ b + c := by
  apply equivalent_of_toPeano_eq
  rw [add_toPeano, add_toPeano, toPeano_eq_of_equivalent h]

/-- Addition on the left respects Decimal equivalence. -/
theorem equivalent_add_left {a b c : Decimal} (h : b ≈ c) : a + b ≈ a + c := by
  rw [add_commutative a b, add_commutative a c]
  exact equivalent_add_right h

/-- Addition respects Decimal equivalence in both arguments. -/
theorem equivalent_add {a b c d : Decimal} (hab : a ≈ b) (hcd : c ≈ d) :
    a + c ≈ b + d :=
  Setoid.trans (equivalent_add_right hab) (equivalent_add_left hcd)

theorem add_associative (a b c : Decimal) : a + b + c ≈ a + (b + c) := by
  apply equivalent_of_toPeano_eq
  rw [add_toPeano, add_toPeano, add_toPeano, add_toPeano, Peano.add_associative]

theorem lessThanAlignedLists_padded_of_lt {a b : Decimal} (h : b < a) :
  let pair := Sequences.List.padAtStartToSameLength a.val b.val zeroDigit
  LessThanAlignedLists pair.2 pair.1
    (Sequences.List.sameLength_commutative
      (Sequences.List.padAtStartToSameLength_sameLength a.val b.val zeroDigit)) :=
  lessThanAlignedLists_padded_snd_fst_of_toCardinalNaturalPeano_lt a.val b.val h

theorem padAtStartToSameLength_eq_of_equivalent {a b : Decimal} (h : a ≈ b) :
  (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).1 =
    (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).2 :=
  padAtStartToSameLength_eq_of_toCardinalNaturalPeano_eq (toPeano_eq_of_equivalent h)

theorem subtractAlignedLists_borrow_false_of_equivalent {a b : Decimal} (h : a ≈ b) :
  (subtractAlignedLists
    (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).1
    (Sequences.List.padAtStartToSameLength a.val b.val zeroDigit).2
    (Sequences.List.padAtStartToSameLength_sameLength a.val b.val zeroDigit)).2 = false :=
  subtractAlignedLists_borrow_false_of_toCardinalNaturalPeano_eq (toPeano_eq_of_equivalent h)

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
      (Sequences.List.padAtStartToSameLength_sameLength a.val b.val zeroDigit)).2 = true :=
  subtractAlignedLists_borrow_true_of_toCardinalNaturalPeano_lt h

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

/-- A successful subtraction `trySubtract y x = some d` means `y ≈ x + d`. -/
theorem eq_of_trySubtract_add (x y d : Decimal)
    (h : trySubtract y x = some d) : y ≈ x + d := by
  obtain ⟨hle, hsub⟩ := exists_subtract_of_trySubtract h
  have hsum := subtract_add_cancel y x hle
  rw [hsub, add_commutative] at hsum
  exact Setoid.symm hsum

/-- `trySubtract (x + d) d'` recovers a value equivalent to `x` when
`d ≈ d'`. -/
theorem trySubtract_add_right_of_equivalent (x d d' : Decimal) (hd : d ≈ d') :
    Option.Rel (· ≈ ·) (trySubtract (x + d) d') (some x) := by
  have hle' : d' ≤ x + d :=
    le_of_equivalent_of_le (Setoid.symm hd) (le_add_right x d)
  have hsub_eq : subtract (x + d) d' hle' ≈ x := by
    apply equivalent_of_toPeano_eq
    apply Peano.add_cancel_right
      (toPeano (subtract (x + d) d' hle')) (toPeano x) (toPeano d')
    rw [toPeano_subtract, add_toPeano, toPeano_eq_of_equivalent hd]
  have htry : trySubtract (x + d) d' = some (subtract (x + d) d' hle') :=
    trySubtract_of_subtract ⟨hle', rfl⟩
  rw [htry]
  exact Option.Rel.some hsub_eq

/-- When `y ≈ x + d`, `trySubtract y x` recovers a value equivalent to `d`. -/
theorem trySubtract_of_equivalent_add {x y d : Decimal} (h : y ≈ x + d) :
    Option.Rel (· ≈ ·) (trySubtract y x) (some d) := by
  have hle_add : x ≤ x + d := by
    rw [add_commutative]
    exact le_add_right d x
  have hle : x ≤ y := le_of_le_of_equivalent hle_add (Setoid.symm h)
  have hsub_eq : subtract y x hle ≈ d := by
    apply equivalent_of_toPeano_eq
    apply Peano.add_cancel_right
      (toPeano (subtract y x hle)) (toPeano d) (toPeano x)
    rw [toPeano_subtract, toPeano_eq_of_equivalent h, add_toPeano,
      Peano.add_commutative (toPeano x)]
  have htry : trySubtract y x = some (subtract y x hle) :=
    trySubtract_of_subtract ⟨hle, rfl⟩
  rw [htry]
  exact Option.Rel.some hsub_eq

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

/-- Multiplication respects Decimal equivalence in both arguments. -/
theorem equivalent_multiply {a b c d : Decimal} (hab : a ≈ b) (hcd : c ≈ d) :
    a * c ≈ b * d := by
  apply equivalent_of_toPeano_eq
  rw [multiply_toPeano, multiply_toPeano, toPeano_eq_of_equivalent hab,
    toPeano_eq_of_equivalent hcd]

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

def powerByDigit (x : Decimal) (d : Digit) : Decimal :=
  match d with
  | ⟨val, h⟩ =>
    match val, h with
    | .zero, _ => one
    | .successor v1, h =>
      match v1, h with
      | .zero, _ => x
      | .successor v2, h =>
        match v2, h with
        | .zero, _ => x * x
        | .successor v3, h =>
          match v3, h with
          | .zero, _ =>
            let x2 := x * x
            x2 * x
          | .successor v4, h =>
            match v4, h with
            | .zero, _ =>
              let x2 := x * x
              x2 * x2
            | .successor v5, h =>
              match v5, h with
              | .zero, _ =>
                let x2 := x * x
                let x4 := x2 * x2
                x4 * x
              | .successor v6, h =>
                match v6, h with
                | .zero, _ =>
                  let x2 := x * x
                  let x4 := x2 * x2
                  x4 * x2
                | .successor v7, h =>
                  match v7, h with
                  | .zero, _ =>
                    let x2 := x * x
                    let x4 := x2 * x2
                    let x6 := x4 * x2
                    x6 * x
                  | .successor v8, h =>
                    match v8, h with
                    | .zero, _ =>
                      let x2 := x * x
                      let x4 := x2 * x2
                      x4 * x4
                    | .successor v9, h =>
                      match v9, h with
                      | .zero, _ =>
                        let x2 := x * x
                        let x3 := x2 * x
                        let x6 := x3 * x3
                        x6 * x3
                      | .successor v10, h =>
                        have h1 := Peano.lt_of_succ_lt_succ h
                        have h2 := Peano.lt_of_succ_lt_succ h1
                        have h3 := Peano.lt_of_succ_lt_succ h2
                        have h4 := Peano.lt_of_succ_lt_succ h3
                        have h5 := Peano.lt_of_succ_lt_succ h4
                        have h6 := Peano.lt_of_succ_lt_succ h5
                        have h7 := Peano.lt_of_succ_lt_succ h6
                        have h8 := Peano.lt_of_succ_lt_succ h7
                        have h9 := Peano.lt_of_succ_lt_succ h8
                        have h10 := Peano.lt_of_succ_lt_succ h9
                        False.elim (Peano.not_lt_zero v10 h10)

def powerTen (x : Decimal) : Decimal :=
  let x5 := powerByDigit x fiveDigit
  x5 * x5

def powerContinue (x : Decimal) (acc : Decimal) : Sequences.List Digit → Decimal
  | .empty => acc
  | .firstElement d ds =>
      let raised := powerTen acc
      match d.val with
      | .zero => powerContinue x raised ds
      | .successor _ => powerContinue x (raised * powerByDigit x d) ds

def powerList (x : Decimal) : Sequences.List Digit → Decimal
  | .empty => one
  | .firstElement d ds => powerContinue x (powerByDigit x d) ds

/-- Exponentiation, excluding the undefined case `0 ^ 0`. -/
def power (a b : Decimal) (h : ¬ a ≈ zero ∨ ¬ b ≈ zero) : Decimal :=
  if ha : a ≈ zero then
    if hb : b ≈ zero then
      False.elim (h.elim (fun hna => hna ha) (fun hnb => hnb hb))
    else
      zero
  else
    powerList a b.val

theorem powerByDigit_toPeano (x : Decimal) (d : Digit) (hx : ¬ x ≈ zero) :
    (powerByDigit x d).toPeano =
      Peano.power x.toPeano d.val
        (Or.inl (toPeano_ne_zero_of_not_equivalent_zero hx)) := by
  let cx := x.toPeano
  have hx' : cx ≠ Peano.zero := toPeano_ne_zero_of_not_equivalent_zero hx
  unfold powerByDigit
  match d with
  | ⟨val, h⟩ =>
    match val, h with
    | .zero, _ =>
      change toPeano one = Peano.power cx .zero (Or.inl hx')
      rw [toPeano_one, Peano.power_zero_eq_one]
    | .successor v1, h =>
      match v1, h with
      | .zero, _ =>
        change toPeano x = Peano.power cx .one (Or.inl hx')
        rw [Peano.power_one_eq_self]
      | .successor v2, h =>
        match v2, h with
        | .zero, _ =>
          change toPeano (x * x) = Peano.power cx .two (Or.inl hx')
          rw [multiply_toPeano, Peano.power_two_eq cx hx']
        | .successor v3, h =>
          match v3, h with
          | .zero, _ =>
            change toPeano (let x2 := x * x; x2 * x) =
              Peano.power cx .three (Or.inl hx')
            show toPeano ((x * x) * x) =
              Peano.power cx .three (Or.inl hx')
            rw [multiply_toPeano, multiply_toPeano, Peano.power_three_eq cx hx']
          | .successor v4, h =>
            match v4, h with
            | .zero, _ =>
              change toPeano (let x2 := x * x; x2 * x2) =
                Peano.power cx .four (Or.inl hx')
              show toPeano ((x * x) * (x * x)) =
                Peano.power cx .four (Or.inl hx')
              rw [multiply_toPeano, multiply_toPeano, Peano.power_four_eq cx hx']
            | .successor v5, h =>
              match v5, h with
              | .zero, _ =>
                change toPeano (let x2 := x * x; let x4 := x2 * x2; x4 * x) =
                  Peano.power cx .five (Or.inl hx')
                show toPeano (((x * x) * (x * x)) * x) =
                  Peano.power cx .five (Or.inl hx')
                rw [multiply_toPeano, multiply_toPeano, multiply_toPeano,
                  Peano.power_five_eq cx hx']
              | .successor v6, h =>
                match v6, h with
                | .zero, _ =>
                  change toPeano (let x2 := x * x; let x4 := x2 * x2; x4 * x2) =
                    Peano.power cx .six (Or.inl hx')
                  show toPeano (((x * x) * (x * x)) * (x * x)) =
                    Peano.power cx .six (Or.inl hx')
                  rw [multiply_toPeano, multiply_toPeano, multiply_toPeano,
                    Peano.power_six_eq cx hx']
                | .successor v7, h =>
                  match v7, h with
                  | .zero, _ =>
                    change toPeano
                        (let x2 := x * x; let x4 := x2 * x2; let x6 := x4 * x2; x6 * x) =
                      Peano.power cx .seven (Or.inl hx')
                    show toPeano ((((x * x) * (x * x)) * (x * x)) * x) =
                      Peano.power cx .seven (Or.inl hx')
                    rw [multiply_toPeano, multiply_toPeano, multiply_toPeano,
                      multiply_toPeano, Peano.power_seven_eq cx hx']
                  | .successor v8, h =>
                    match v8, h with
                    | .zero, _ =>
                      change toPeano (let x2 := x * x; let x4 := x2 * x2; x4 * x4) =
                        Peano.power cx .eight (Or.inl hx')
                      show toPeano (((x * x) * (x * x)) * ((x * x) * (x * x))) =
                        Peano.power cx .eight (Or.inl hx')
                      rw [multiply_toPeano, multiply_toPeano, multiply_toPeano,
                        Peano.power_eight_eq cx hx']
                    | .successor v9, h =>
                      match v9, h with
                      | .zero, _ =>
                        change toPeano
                            (let x2 := x * x; let x3 := x2 * x; let x6 := x3 * x3; x6 * x3) =
                          Peano.power cx .nine (Or.inl hx')
                        show toPeano
                            ((((x * x) * x) * ((x * x) * x)) * ((x * x) * x)) =
                          Peano.power cx .nine (Or.inl hx')
                        rw [multiply_toPeano, multiply_toPeano, multiply_toPeano,
                          multiply_toPeano, Peano.power_nine_eq cx hx']
                      | .successor v10, h =>
                        have h1 := Peano.lt_of_succ_lt_succ h
                        have h2 := Peano.lt_of_succ_lt_succ h1
                        have h3 := Peano.lt_of_succ_lt_succ h2
                        have h4 := Peano.lt_of_succ_lt_succ h3
                        have h5 := Peano.lt_of_succ_lt_succ h4
                        have h6 := Peano.lt_of_succ_lt_succ h5
                        have h7 := Peano.lt_of_succ_lt_succ h6
                        have h8 := Peano.lt_of_succ_lt_succ h7
                        have h9 := Peano.lt_of_succ_lt_succ h8
                        have h10 := Peano.lt_of_succ_lt_succ h9
                        exact False.elim (Peano.not_lt_zero v10 h10)

theorem powerTen_toPeano (x : Decimal) (hx : ¬ x ≈ zero) :
    (powerTen x).toPeano =
      Peano.power x.toPeano Peano.ten
        (Or.inl (toPeano_ne_zero_of_not_equivalent_zero hx)) := by
  unfold powerTen
  show toPeano (powerByDigit x fiveDigit * powerByDigit x fiveDigit) = _
  rw [multiply_toPeano, powerByDigit_toPeano x fiveDigit hx]
  have hf : fiveDigit.val = Peano.five := rfl
  rw [hf]
  have hx' := toPeano_ne_zero_of_not_equivalent_zero hx
  have hadd := Peano.power_add_eq x.toPeano Peano.five Peano.five hx'
  have hsum : Peano.five + Peano.five = Peano.ten := rfl
  rw [hsum] at hadd
  exact hadd.symm

theorem powerContinue_toPeano (x acc : Decimal) (ds : Sequences.List Digit)
    (e : Peano) (hx : ¬ x ≈ zero)
    (hacc : acc.toPeano =
      Peano.power x.toPeano e
        (Or.inl (toPeano_ne_zero_of_not_equivalent_zero hx))) :
    (powerContinue x acc ds).toPeano =
      Peano.power x.toPeano
        (e * Peano.tenPow ds.length + toCardinalNaturalPeano ds Peano.zero)
        (Or.inl (toPeano_ne_zero_of_not_equivalent_zero hx)) := by
  induction ds generalizing acc e with
  | empty =>
      change acc.toPeano =
        Peano.power x.toPeano
          (e * Peano.tenPow Peano.zero + Peano.zero)
          (Or.inl (toPeano_ne_zero_of_not_equivalent_zero hx))
      simp only [Peano.tenPow, Peano.multiply_one, Peano.add_zero]
      exact hacc
  | firstElement d rest ih =>
      have hx' := toPeano_ne_zero_of_not_equivalent_zero hx
      have hacc_ne : ¬ acc ≈ zero :=
        not_equivalent_zero_of_toPeano_ne_zero acc (by
          rw [hacc]
          exact Peano.power_ne_zero_of_base_ne_zero x.toPeano e (Or.inl hx') hx')
      have hraised : (powerTen acc).toPeano =
          Peano.power x.toPeano (e * Peano.ten) (Or.inl hx') := by
        rw [powerTen_toPeano acc hacc_ne]
        have hpow_acc :
            Peano.power acc.toPeano Peano.ten
              (Or.inl (toPeano_ne_zero_of_not_equivalent_zero hacc_ne)) =
            Peano.power
              (Peano.power x.toPeano e (Or.inl hx'))
              Peano.ten
              (Or.inl (Peano.power_ne_zero_of_base_ne_zero
                x.toPeano e (Or.inl hx') hx')) :=
          Peano.eq_rec_power _ _ _ hacc _ _
        rw [hpow_acc]
        exact (Peano.power_mul_eq x.toPeano e Peano.ten hx').symm
      have hlen : (Sequences.List.firstElement d rest).length =
          rest.length + Peano.one := rfl
      cases hd : d.val with
      | zero =>
          have ih' := ih (powerTen acc) (e * Peano.ten) hraised
          have hexp :
              (e * Peano.ten) * Peano.tenPow rest.length +
                toCardinalNaturalPeano rest Peano.zero =
              e * Peano.tenPow (rest.length + Peano.one) +
                toCardinalNaturalPeano (Sequences.List.firstElement d rest)
                  Peano.zero := by
            rw [toCardinalNaturalPeano_firstElement, hd, Peano.zero_multiply,
              Peano.zero_add, Peano.tenPow_add_one, Peano.multiply_associative]
          rw [hlen]
          simp only [powerContinue, hd]
          exact (Peano.eq_rec_power_exponent x.toPeano _ _
            hexp.symm (Or.inl hx') (Or.inl hx')) ▸ ih'
      | successor _ =>
          have hnew_acc : (powerTen acc * powerByDigit x d).toPeano =
              Peano.power x.toPeano (e * Peano.ten + d.val) (Or.inl hx') := by
            rw [multiply_toPeano, powerByDigit_toPeano x d hx, hraised]
            exact (Peano.power_add_eq x.toPeano (e * Peano.ten) d.val hx').symm
          have ih' := ih (powerTen acc * powerByDigit x d)
            (e * Peano.ten + d.val) hnew_acc
          have hexp :
              (e * Peano.ten + d.val) * Peano.tenPow rest.length +
                toCardinalNaturalPeano rest Peano.zero =
              e * Peano.tenPow (rest.length + Peano.one) +
                toCardinalNaturalPeano (Sequences.List.firstElement d rest)
                  Peano.zero := by
            rw [toCardinalNaturalPeano_firstElement, Peano.tenPow_add_one,
              Peano.multiply_distributive_over_add_left,
              Peano.multiply_associative, Peano.add_associative]
          rw [hlen]
          simp only [powerContinue, hd]
          exact (Peano.eq_rec_power_exponent x.toPeano _ _
            hexp.symm (Or.inl hx') (Or.inl hx')) ▸ ih'

theorem powerList_toPeano (x : Decimal) (digits : Sequences.List Digit)
    (hx : ¬ x ≈ zero) :
    (powerList x digits).toPeano =
      Peano.power x.toPeano (toCardinalNaturalPeano digits Peano.zero)
        (Or.inl (toPeano_ne_zero_of_not_equivalent_zero hx)) := by
  match digits with
  | .empty =>
      change toPeano one =
        Peano.power x.toPeano Peano.zero
          (Or.inl (toPeano_ne_zero_of_not_equivalent_zero hx))
      rw [toPeano_one, Peano.power_zero_eq_one]
  | .firstElement d ds =>
      change (powerContinue x (powerByDigit x d) ds).toPeano = _
      have hacc := powerByDigit_toPeano x d hx
      have h := powerContinue_toPeano x (powerByDigit x d) ds d.val hx hacc
      rw [toCardinalNaturalPeano_firstElement]
      exact h

theorem power_toPeano (x y : Decimal) (h : ¬ x ≈ zero ∨ ¬ y ≈ zero) :
    ∃ h2, (power x y h).toPeano = Peano.power x.toPeano y.toPeano h2 := by
  by_cases hx : x ≈ zero
  · have hy : ¬ y ≈ zero :=
      h.elim (fun hnx => False.elim (hnx hx)) id
    have hy' := toPeano_ne_zero_of_not_equivalent_zero hy
    refine ⟨Or.inr hy', ?_⟩
    simp only [power, hx, ↓reduceDIte, hy, ↓reduceDIte]
    have hx0 : x.toPeano = Peano.zero :=
      (toPeano_eq_of_equivalent hx).trans toPeano_zero
    rw [toPeano_zero, hx0]
    exact (Peano.zero_power_of_nonzero_exponent y.toPeano hy' (Or.inr hy')).symm
  · refine ⟨Or.inl (toPeano_ne_zero_of_not_equivalent_zero hx), ?_⟩
    simp only [power, hx, ↓reduceDIte]
    exact powerList_toPeano x y.val hx

/-- Transport a Decimal power side-condition across `toPeano`. -/
theorem power_condition_toPeano {x y : Decimal} (h : ¬ x ≈ zero ∨ ¬ y ≈ zero) :
    x.toPeano ≠ Peano.zero ∨ y.toPeano ≠ Peano.zero :=
  h.elim (fun hx => Or.inl (toPeano_ne_zero_of_not_equivalent_zero hx))
    (fun hy => Or.inr (toPeano_ne_zero_of_not_equivalent_zero hy))

/-- Recover a Decimal power side-condition from the Peano embedding. -/
theorem power_condition_of_toPeano {x y : Decimal}
    (h : x.toPeano ≠ Peano.zero ∨ y.toPeano ≠ Peano.zero) :
    ¬ x ≈ zero ∨ ¬ y ≈ zero :=
  h.elim (fun hx => Or.inl (not_equivalent_zero_of_toPeano_ne_zero x hx))
    (fun hy => Or.inr (not_equivalent_zero_of_toPeano_ne_zero y hy))

/-- `power_toPeano` with a chosen Peano-side condition. -/
theorem power_toPeano_eq (x y : Decimal) (h : ¬ x ≈ zero ∨ ¬ y ≈ zero)
    (h2 : x.toPeano ≠ Peano.zero ∨ y.toPeano ≠ Peano.zero) :
    (power x y h).toPeano = Peano.power x.toPeano y.toPeano h2 := by
  obtain ⟨h2', heq⟩ := power_toPeano x y h
  exact heq.trans (Peano.eq_rec_power_exponent _ _ _ rfl h2' h2)

theorem power_add (x y z : Decimal)
    (h : ¬ x ≈ zero ∨ ¬ y ≈ zero) (h2 : ¬ x ≈ zero ∨ ¬ z ≈ zero) :
    ∃ h3, power x (y + z) h3 ≈ power x y h * power x z h2 := by
  have hp := power_condition_toPeano h
  have hp2 := power_condition_toPeano h2
  obtain ⟨h3p, heq⟩ := Peano.power_add x.toPeano y.toPeano z.toPeano hp hp2
  have hsum : x.toPeano ≠ Peano.zero ∨ (y + z).toPeano ≠ Peano.zero := by
    rw [add_toPeano]
    exact h3p
  let h3 := power_condition_of_toPeano hsum
  refine ⟨h3, equivalent_of_toPeano_eq ?_⟩
  have hlhs : (power x (y + z) h3).toPeano =
      Peano.power x.toPeano (y.toPeano + z.toPeano) h3p :=
    (power_toPeano_eq x (y + z) h3 hsum).trans
      (Peano.eq_rec_power_exponent _ _ _ (add_toPeano y z) hsum h3p)
  rw [hlhs, multiply_toPeano, power_toPeano_eq x y h hp, power_toPeano_eq x z h2 hp2]
  exact heq

theorem power_multiply (x y z : Decimal)
    (h : ¬ x ≈ zero ∨ ¬ y ≈ zero)
    (h2 : ¬ power x y h ≈ zero ∨ ¬ z ≈ zero) :
    ∃ h3, power x (y * z) h3 ≈ power (power x y h) z h2 := by
  have hp := power_condition_toPeano h
  have hinner := power_toPeano_eq x y h hp
  have hp2 : Peano.power x.toPeano y.toPeano hp ≠ Peano.zero ∨
      z.toPeano ≠ Peano.zero :=
    h2.elim
      (fun hpow => Or.inl (by
        have : (power x y h).toPeano ≠ Peano.zero :=
          toPeano_ne_zero_of_not_equivalent_zero hpow
        rwa [hinner] at this))
      (fun hz => Or.inr (toPeano_ne_zero_of_not_equivalent_zero hz))
  obtain ⟨h3p, heq⟩ := Peano.power_multiply x.toPeano y.toPeano z.toPeano hp hp2
  have hprod : x.toPeano ≠ Peano.zero ∨ (y * z).toPeano ≠ Peano.zero := by
    rw [multiply_toPeano]
    exact h3p
  let h3 := power_condition_of_toPeano hprod
  refine ⟨h3, equivalent_of_toPeano_eq ?_⟩
  have hlhs : (power x (y * z) h3).toPeano =
      Peano.power x.toPeano (y.toPeano * z.toPeano) h3p :=
    (power_toPeano_eq x (y * z) h3 hprod).trans
      (Peano.eq_rec_power_exponent _ _ _ (multiply_toPeano y z) hprod h3p)
  have hrhs : (power (power x y h) z h2).toPeano =
      Peano.power (Peano.power x.toPeano y.toPeano hp) z.toPeano hp2 :=
    (power_toPeano_eq (power x y h) z h2 (power_condition_toPeano h2)).trans
      (Peano.eq_rec_power _ _ _ hinner _ hp2)
  rw [hlhs, hrhs]
  exact heq

theorem multiply_power (x y z : Decimal)
    (h : ¬ x ≈ zero ∨ ¬ z ≈ zero) (h2 : ¬ y ≈ zero ∨ ¬ z ≈ zero) :
    ∃ h3, power (x * y) z h3 ≈ power x z h * power y z h2 := by
  have hp := power_condition_toPeano h
  have hp2 := power_condition_toPeano h2
  obtain ⟨h3p, heq⟩ :=
    Peano.power_multiply_dist x.toPeano y.toPeano z.toPeano hp hp2
  have hbase : (x * y).toPeano ≠ Peano.zero ∨ z.toPeano ≠ Peano.zero := by
    rw [multiply_toPeano]
    exact h3p
  let h3 := power_condition_of_toPeano hbase
  refine ⟨h3, equivalent_of_toPeano_eq ?_⟩
  have hlhs : (power (x * y) z h3).toPeano =
      Peano.power (x.toPeano * y.toPeano) z.toPeano h3p :=
    (power_toPeano_eq (x * y) z h3 hbase).trans
      (Peano.eq_rec_power _ _ _ (multiply_toPeano x y) hbase h3p)
  rw [hlhs, multiply_toPeano, power_toPeano_eq x z h hp,
    power_toPeano_eq y z h2 hp2]
  exact heq

/-- `a` is an `e`-th power when some allowed base `b` satisfies `power b e ≈ a`. -/
def Power (e a : Decimal) : Prop := ∃ b h, power b e h ≈ a

theorem Power_toPeano (e a : Decimal) :
    Power e a ↔ Peano.Power e.toPeano a.toPeano := by
  constructor
  · intro h
    rcases h with ⟨b, hb, heq⟩
    exact ⟨b.toPeano, power_condition_toPeano hb,
      (power_toPeano_eq b e hb (power_condition_toPeano hb)).symm.trans
        (toPeano_eq_of_equivalent heq)⟩
  · intro h
    rcases h with ⟨b_peano, hb_peano, heq⟩
    let b := fromPeano b_peano
    have hb : ¬ b ≈ zero ∨ ¬ e ≈ zero :=
      power_condition_of_toPeano (toPeano_fromPeano b_peano ▸ hb_peano)
    exact ⟨b, hb, equivalent_of_toPeano_eq
      ((power_toPeano_eq b e hb (power_condition_toPeano hb)).trans
        ((Peano.eq_rec_power b.toPeano b_peano e.toPeano
          (toPeano_fromPeano b_peano)
          (power_condition_toPeano hb) hb_peano).trans heq))⟩

/-- `base ^ e`, treating the empty / all-zero list as cardinal zero.
When the base is nonzero this is `n ^ e` (including `n ^ 0 = 1`).
When the base is zero the result is zero, matching `0 ^ e` for `e ≉ zero`. -/
def powerListOrZero (base : Sequences.List Digit) (e : Decimal) :
    Sequences.List Digit :=
  if h : hasNonZero base then
    let hnz := hasNonZero_of_hasNonZero_bool h
    let baseDec : Decimal := ⟨base, hasNonZero_ne_empty hnz⟩
    (power baseDec e
      (Or.inl (not_equivalent_zero_of_toPeano_ne_zero baseDec
        (toCardinalNaturalPeano_ne_zero_of_hasNonZero base Peano.zero hnz)))).val
  else
    .empty

/--
Integer `e`-th root of `a` with remainder: `(b, r)` satisfies
`a ≈ b ^ e + r` and `a < (b.successor) ^ e`. Requires `e ≉ zero`.
Computed by the schoolbook columnar algorithm (digits grouped from the right
in blocks of `e`).
-/
def rootWithRemainder (a e : Decimal) (he : ¬ e ≈ zero) : Decimal × Decimal :=
  let groupSize := e.toPeano
  let remaining := firstRootGroupSize a.val.length groupSize
    (toPeano_ne_zero_of_not_equivalent_zero he)
  let (rootDigits, remDigits) :=
    rootWithRemainderAux (powerListOrZero · e) a.val groupSize .empty .empty remaining
  (if hq : rootDigits = Sequences.List.empty then zero else normalizeList rootDigits hq,
   if hr : remDigits = Sequences.List.empty then zero else normalizeList remDigits hr)

def powE (base : Peano) (e : Decimal) (he : ¬ e ≈ zero) : Peano :=
  Peano.power base e.toPeano
    (Or.inr (toPeano_ne_zero_of_not_equivalent_zero he))

theorem powE_lt {a b : Peano} (e : Decimal) (he : ¬ e ≈ zero) (h : a < b) :
    powE a e he < powE b e he :=
  Peano.lt_power (toPeano_ne_zero_of_not_equivalent_zero he) h
    (Or.inr (toPeano_ne_zero_of_not_equivalent_zero he)) (Or.inr (toPeano_ne_zero_of_not_equivalent_zero he))

theorem powE_le {a b : Peano} (e : Decimal) (he : ¬ e ≈ zero) (h : a ≤ b) :
    powE a e he ≤ powE b e he :=
  Peano.power_le_of_le (toPeano_ne_zero_of_not_equivalent_zero he) h
    (Or.inr (toPeano_ne_zero_of_not_equivalent_zero he)) (Or.inr (toPeano_ne_zero_of_not_equivalent_zero he))

theorem powE_zero (e : Decimal) (he : ¬ e ≈ zero) :
    powE Peano.zero e he = Peano.zero :=
  Peano.zero_power_of_nonzero_exponent
    (toPeano e) (toPeano_ne_zero_of_not_equivalent_zero he) _

theorem powE_one (e : Decimal) (he : ¬ e ≈ zero) :
    powE Peano.one e he = Peano.one :=
  Peano.one_power (toPeano e)
    (Or.inr (toPeano_ne_zero_of_not_equivalent_zero he))

theorem powE_mul (x y : Peano) (e : Decimal) (he : ¬ e ≈ zero) :
    powE (x * y) e he = powE x e he * powE y e he := by
  obtain ⟨h3, heq⟩ :=
    Peano.power_multiply_dist x y (toPeano e)
      (Or.inr (toPeano_ne_zero_of_not_equivalent_zero he))
      (Or.inr (toPeano_ne_zero_of_not_equivalent_zero he))
  exact (Peano.eq_rec_power (x * y) (x * y) (toPeano e)
    rfl h3 (Or.inr (toPeano_ne_zero_of_not_equivalent_zero he))).symm.trans heq

theorem powE_mul_ten (Y : Peano) (e : Decimal) (he : ¬ e ≈ zero) :
    powE (Y * Peano.ten) e he =
      powE Y e he * Peano.tenPow (toPeano e) := by
  rw [powE_mul]
  have hten : powE Peano.ten e he = Peano.tenPow e.toPeano :=
    (Peano.eq_rec_power Peano.ten Peano.ten e.toPeano rfl
      (Or.inr (toPeano_ne_zero_of_not_equivalent_zero he))
      (Or.inl (Peano.successor_ne_zero Peano.nine))).trans
      (Peano.tenPow_eq_power e.toPeano).symm
  rw [hten]

theorem powerListOrZero_toCardinal (base : Sequences.List Digit) (e : Decimal) (he : ¬ e ≈ zero) :
    listVal (powerListOrZero base e) = powE (listVal base) e he := by
  unfold powerListOrZero
  by_cases h : hasNonZero base = true
  · rw [dif_pos h]
    let hnz := hasNonZero_of_hasNonZero_bool h
    let baseDec : Decimal := ⟨base, hasNonZero_ne_empty hnz⟩
    have hb : ¬ baseDec ≈ zero ∨ ¬ e ≈ zero :=
      Or.inl (not_equivalent_zero_of_toPeano_ne_zero baseDec
        (toCardinalNaturalPeano_ne_zero_of_hasNonZero base Peano.zero hnz))
    exact power_toPeano_eq baseDec e hb
      (Or.inr (toPeano_ne_zero_of_not_equivalent_zero he))
  · have hz : listVal base = Peano.zero :=
      toCardinalNaturalPeano_zero_of_allZero (allZero_of_not_hasNonZero_bool h)
    rw [dif_neg h, listVal_empty, hz]
    exact (powE_zero e he).symm

theorem powE_shifted_le_trial (currentRoot : Sequences.List Digit) (e : Decimal) (he : ¬ e ≈ zero)
    (d : Digit) :
    powE (listVal (Sequences.List.append currentRoot zeroDigit)) e he ≤
      powE (listVal (Sequences.List.append currentRoot d)) e he := by
  apply powE_le
  rw [listVal_append_zeroDigit, listVal_append]
  exact Peano.le_add_self_left _ _

theorem increment_add_shifted (currentRoot : Sequences.List Digit) (e : Decimal) (he : ¬ e ≈ zero)
    (d : Digit) :
    listVal (subtractLists (powerListOrZero (Sequences.List.append currentRoot d) e)
        (powerListOrZero (Sequences.List.append currentRoot zeroDigit) e)) +
      powE (listVal (Sequences.List.append currentRoot zeroDigit)) e he =
    powE (listVal (Sequences.List.append currentRoot d)) e he := by
  have hnlt :
      ¬ listVal (powerListOrZero (Sequences.List.append currentRoot d) e) <
        listVal (powerListOrZero (Sequences.List.append currentRoot zeroDigit) e) := by
    rw [powerListOrZero_toCardinal (Sequences.List.append currentRoot d) e he,
        powerListOrZero_toCardinal (Sequences.List.append currentRoot zeroDigit) e he]
    exact Peano.cardinal_not_lt_of_le
      (powE_shifted_le_trial currentRoot e he d)
  have hsub :=
    subtractLists_spec
      (powerListOrZero (Sequences.List.append currentRoot d) e)
      (powerListOrZero (Sequences.List.append currentRoot zeroDigit) e) hnlt
  rw [← powerListOrZero_toCardinal (Sequences.List.append currentRoot d) e he,
      ← powerListOrZero_toCardinal (Sequences.List.append currentRoot zeroDigit) e he]
  exact hsub

theorem rootDigit_taken_spec (remainder currentRoot : Sequences.List Digit)
    (e : Decimal) (he : ¬ e ≈ zero) (d : Digit)
    (hnlt : ¬ listVal remainder <
      listVal (subtractLists
        (powerListOrZero (Sequences.List.append currentRoot d) e)
        (powerListOrZero (Sequences.List.append currentRoot zeroDigit) e))) :
    let increment :=
      subtractLists (powerListOrZero (Sequences.List.append currentRoot d) e)
        (powerListOrZero (Sequences.List.append currentRoot zeroDigit) e)
    let nextRem := subtractLists remainder increment
    listVal remainder + powE (listVal currentRoot * Peano.ten) e he =
      powE (listVal currentRoot * Peano.ten + d.val) e he +
        listVal nextRem ∧
    powE (listVal currentRoot * Peano.ten + d.val) e he ≤
      listVal remainder + powE (listVal currentRoot * Peano.ten) e he := by
  have hsub := subtractLists_spec remainder
    (subtractLists (powerListOrZero (Sequences.List.append currentRoot d) e)
      (powerListOrZero (Sequences.List.append currentRoot zeroDigit) e)) hnlt
  have hadd := increment_add_shifted currentRoot e he d
  have hshift := listVal_append_zeroDigit currentRoot
  have htrial := listVal_append currentRoot d
  constructor
  · calc listVal remainder + powE (listVal currentRoot * Peano.ten) e he
        = (listVal (subtractLists remainder
              (subtractLists (powerListOrZero (Sequences.List.append currentRoot d) e)
                (powerListOrZero (Sequences.List.append currentRoot zeroDigit) e))) +
            listVal (subtractLists
              (powerListOrZero (Sequences.List.append currentRoot d) e)
              (powerListOrZero (Sequences.List.append currentRoot zeroDigit) e))) +
            powE (listVal currentRoot * Peano.ten) e he := hsub.symm ▸ rfl
      _ = listVal (subtractLists remainder
              (subtractLists (powerListOrZero (Sequences.List.append currentRoot d) e)
                (powerListOrZero (Sequences.List.append currentRoot zeroDigit) e))) +
            (listVal (subtractLists
              (powerListOrZero (Sequences.List.append currentRoot d) e)
              (powerListOrZero (Sequences.List.append currentRoot zeroDigit) e)) +
            powE (listVal currentRoot * Peano.ten) e he) := by
          rw [Peano.add_associative]
      _ = listVal (subtractLists remainder
              (subtractLists (powerListOrZero (Sequences.List.append currentRoot d) e)
                (powerListOrZero (Sequences.List.append currentRoot zeroDigit) e))) +
            powE (listVal currentRoot * Peano.ten + d.val) e he := by
          have hadd' := hadd
          rw [hshift, htrial] at hadd'
          rw [hadd']
      _ = powE (listVal currentRoot * Peano.ten + d.val) e he +
            listVal (subtractLists remainder
              (subtractLists (powerListOrZero (Sequences.List.append currentRoot d) e)
                (powerListOrZero (Sequences.List.append currentRoot zeroDigit) e))) :=
          Peano.add_commutative _ _
  · have hle_inc := Peano.not_lt_implies_le hnlt
    have hle_add := Peano.add_le_add_right hle_inc
      (powE (listVal currentRoot * Peano.ten) e he)
    have hadd' := hadd
    rw [hshift, htrial] at hadd'
    rwa [hadd'] at hle_add

theorem remainder_lt_zero_increment_false (remainder currentRoot : Sequences.List Digit)
    (e : Decimal) (he : ¬ e ≈ zero) (hc : Peano.zero < Peano.ten)
    (hlt : listVal remainder <
      listVal (subtractLists
        (powerListOrZero (Sequences.List.append currentRoot ⟨Peano.zero, hc⟩) e)
        (powerListOrZero (Sequences.List.append currentRoot zeroDigit) e))) :
    False := by
  have hadd := increment_add_shifted currentRoot e he ⟨Peano.zero, hc⟩
  have hshift := listVal_append_zeroDigit currentRoot
  have htrial := listVal_append currentRoot ⟨Peano.zero, hc⟩
  rw [hshift, htrial, Peano.add_zero] at hadd
  have hlt_add := Peano.add_lt_add_right hlt
    (powE (listVal currentRoot * Peano.ten) e he)
  rw [hadd] at hlt_add
  have hlt_rem : listVal remainder < Peano.zero :=
    Peano.add_lt_cancel_right (by
      rwa [Peano.zero_add])
  exact Peano.not_lt_zero _ hlt_rem

theorem findRootDigitAux_spec (remainder : Sequences.List Digit) (exponent : Decimal) (he : ¬ exponent ≈ zero)
    (currentRoot : Sequences.List Digit)
    (candidate : Peano) (hc : candidate < Peano.ten) :
    let result := findRootDigitAux (powerListOrZero · exponent) remainder currentRoot candidate hc
    let d := result.1
    let nextRem := result.2
    listVal remainder +
        powE (listVal currentRoot * Peano.ten) exponent he =
      powE (listVal currentRoot * Peano.ten + d.val) exponent he +
        listVal nextRem ∧
    powE (listVal currentRoot * Peano.ten + d.val) exponent he ≤
      listVal remainder +
        powE (listVal currentRoot * Peano.ten) exponent he ∧
    (candidate = d.val ∨
      listVal remainder +
          powE (listVal currentRoot * Peano.ten) exponent he <
        powE (listVal currentRoot * Peano.ten + d.val.successor)
          exponent he) := by
  induction candidate with
  | zero =>
    unfold findRootDigitAux
    dsimp only
    by_cases hlt : isLessThanLists remainder
        (subtractLists
          (powerListOrZero (Sequences.List.append currentRoot ⟨Peano.zero, hc⟩)
            exponent)
          (powerListOrZero (Sequences.List.append currentRoot zeroDigit) exponent)) = true
    · exact False.elim (remainder_lt_zero_increment_false remainder currentRoot exponent he hc
        ((isLessThanLists_iff_toCardinalNaturalPeano_lt _ _).mp hlt))
    · rw [if_neg hlt]
      have hnlt := (isLessThanLists_eq_false_iff_not_lt remainder _).mp
        (eq_false_of_ne_true hlt)
      obtain ⟨heq, hle⟩ := rootDigit_taken_spec remainder currentRoot exponent he
        ⟨Peano.zero, hc⟩ hnlt
      exact ⟨heq, hle, Or.inl rfl⟩
  | successor c ih =>
    unfold findRootDigitAux
    dsimp only
    by_cases hlt : isLessThanLists remainder
        (subtractLists
          (powerListOrZero (Sequences.List.append currentRoot ⟨c.successor, hc⟩) exponent)
          (powerListOrZero (Sequences.List.append currentRoot zeroDigit) exponent)) = true
    · rw [if_pos hlt]
      obtain ⟨heq, hle, hmax⟩ := ih (Peano.lt_of_succ_lt hc)
      refine ⟨heq, hle, ?_⟩
      cases hmax with
      | inl heq_d =>
        have hlt_val := (isLessThanLists_iff_toCardinalNaturalPeano_lt remainder _).mp hlt
        have hadd := increment_add_shifted currentRoot exponent he ⟨c.successor, hc⟩
        have hshift := listVal_append_zeroDigit currentRoot
        have htrial := listVal_append currentRoot ⟨c.successor, hc⟩
        rw [hshift, htrial] at hadd
        have hlt_full := Peano.add_lt_add_right hlt_val
          (powE (listVal currentRoot * Peano.ten) exponent he)
        rw [hadd] at hlt_full
        rw [← heq_d]
        exact Or.inr hlt_full
      | inr hlt' => exact Or.inr hlt'
    · rw [if_neg hlt]
      have hnlt := (isLessThanLists_eq_false_iff_not_lt remainder _).mp
        (eq_false_of_ne_true hlt)
      obtain ⟨heq, hle⟩ := rootDigit_taken_spec remainder currentRoot exponent he
        ⟨c.successor, hc⟩ hnlt
      exact ⟨heq, hle, Or.inl rfl⟩

theorem findRootDigit_spec (remainder : Sequences.List Digit) (exponent : Decimal) (he : ¬ exponent ≈ zero)
    (currentRoot : Sequences.List Digit) :
    let result := findRootDigit (powerListOrZero · exponent) remainder currentRoot
    let d := result.1
    let nextRem := result.2
    listVal remainder +
        powE (listVal currentRoot * Peano.ten) exponent he =
      powE (listVal currentRoot * Peano.ten + d.val) exponent he +
        listVal nextRem ∧
    powE (listVal currentRoot * Peano.ten + d.val) exponent he ≤
      listVal remainder +
        powE (listVal currentRoot * Peano.ten) exponent he ∧
    (d.val = Peano.nine ∨
      listVal remainder +
          powE (listVal currentRoot * Peano.ten) exponent he <
        powE (listVal currentRoot * Peano.ten + d.val.successor)
          exponent he) := by
  unfold findRootDigit
  obtain ⟨heq, hle, hmax⟩ :=
    findRootDigitAux_spec remainder exponent he currentRoot
      Peano.nine Peano.nine_lt_ten
  refine ⟨heq, hle, ?_⟩
  cases hmax with
  | inl h_candidate => exact Or.inl h_candidate.symm
  | inr hbound => exact Or.inr hbound

def rootWindow (currentRoot remainder digits : Sequences.List Digit)
    (exponent : Decimal) (he : ¬ exponent ≈ zero) (groupSize remainingInGroup : Peano)
    (hle : remainingInGroup ≤ groupSize) : Peano :=
  powE (listVal currentRoot) exponent he *
      Peano.tenPow
        (digits.length + rootPad groupSize remainingInGroup hle) +
    listVal remainder * Peano.tenPow digits.length +
    listVal digits

theorem rootWindow_bring_down (currentRoot remainder : Sequences.List Digit)
    (d : Digit) (ds : Sequences.List Digit) (exponent : Decimal) (he : ¬ exponent ≈ zero)
    (groupSize n : Peano)
    (hle : n.successor.successor ≤ groupSize) :
    rootWindow currentRoot remainder (Sequences.List.firstElement d ds)
      exponent he groupSize n.successor.successor hle =
    rootWindow currentRoot (Sequences.List.append remainder d) ds
      exponent he groupSize n.successor (Peano.le_of_succ_le hle) := by
  unfold rootWindow rootPad
  have hpad := Peano.subtract_succ_eq_pred_subtract groupSize n.successor hle
  have hlen : (Sequences.List.firstElement d ds).length =
      ds.length.successor := Sequences.List.length_firstElement d ds
  have hshift :
      (Sequences.List.firstElement d ds).length +
        Peano.subtract groupSize n.successor.successor hle =
      ds.length + Peano.subtract groupSize n.successor
        (Peano.le_of_succ_le hle) := by
    rw [hlen, hpad, Peano.successor_add,
      Peano.add_successor]
  have hrem : listVal (Sequences.List.append remainder d) =
      listVal remainder * Peano.ten + d.val :=
    toCardinalNaturalPeano_append remainder d
  have hdigits : listVal (Sequences.List.firstElement d ds) =
      d.val * Peano.tenPow ds.length + listVal ds :=
    toCardinalNaturalPeano_firstElement d ds
  have hten' : Peano.tenPow ds.length.successor =
      Peano.ten * Peano.tenPow ds.length := by
    rw [show ds.length.successor = ds.length + Peano.one from
      (Peano.add_one ds.length).symm,
      Peano.tenPow_add_one]
  rw [hshift, hrem, hdigits, hlen, hten']
  rw [← Peano.multiply_associative (listVal remainder)
    Peano.ten (Peano.tenPow ds.length)]
  rw [Peano.multiply_distributive_over_add_left]
  let A := powE (listVal currentRoot) exponent he *
    Peano.tenPow (ds.length +
      Peano.subtract groupSize n.successor
        (Peano.le_of_succ_le hle))
  let B := listVal remainder * Peano.ten *
    Peano.tenPow ds.length
  let C := d.val * Peano.tenPow ds.length
  let D := listVal ds
  exact calc (A + B) + (C + D)
      = ((A + B) + C) + D :=
        (Peano.add_associative (A + B) C D).symm
    _ = (A + (B + C)) + D := by rw [Peano.add_associative A B C]

theorem rootWindow_at_choose (currentRoot remainder : Sequences.List Digit)
    (d : Digit) (ds : Sequences.List Digit) (exponent : Decimal) (he : ¬ exponent ≈ zero)
    (groupSize : Peano)
    (hgs : groupSize = toPeano exponent)
    (hle : Peano.one ≤ groupSize) :
    rootWindow currentRoot remainder (Sequences.List.firstElement d ds)
      exponent he groupSize Peano.one hle =
      (listVal (Sequences.List.append remainder d) +
        powE (listVal currentRoot * Peano.ten) exponent he) *
        Peano.tenPow ds.length + listVal ds := by
  have hlen : (Sequences.List.firstElement d ds).length = ds.length.successor :=
    Sequences.List.length_firstElement d ds
  have hshift :
      (Sequences.List.firstElement d ds).length +
        rootPad groupSize Peano.one hle =
      ds.length + groupSize := by
    rw [hlen]
    unfold rootPad
    rw [Peano.succ_add_sub_one]
  have hten : Peano.tenPow ds.length.successor =
      Peano.ten * Peano.tenPow ds.length := by
    rw [show ds.length.successor = ds.length + Peano.one from
      (Peano.add_one ds.length).symm,
      Peano.tenPow_add_one]
  have hnewR : listVal (Sequences.List.append remainder d) =
      listVal remainder * Peano.ten + d.val :=
    toCardinalNaturalPeano_append remainder d
  have hdigits : listVal (Sequences.List.firstElement d ds) =
      d.val * Peano.tenPow ds.length + listVal ds :=
    toCardinalNaturalPeano_firstElement d ds
  have hA :
      powE (listVal currentRoot) exponent he *
        Peano.tenPow groupSize =
      powE (listVal currentRoot * Peano.ten) exponent he := by
    rw [hgs, powE_mul_ten]
  have hB :
      listVal remainder *
          (Peano.ten * Peano.tenPow ds.length) =
        (listVal remainder * Peano.ten) *
          Peano.tenPow ds.length :=
    (Peano.multiply_associative
      (listVal remainder) Peano.ten
      (Peano.tenPow ds.length)).symm
  unfold rootWindow
  rw [hshift, hdigits, hlen, hten, hnewR]
  rw [Peano.tenPow_add,
    Peano.multiply_commutative (Peano.tenPow ds.length),
    ← Peano.multiply_associative
      (powE (listVal currentRoot) exponent he)
      (Peano.tenPow groupSize)]
  rw [hA, hB]
  let A := powE (listVal currentRoot * Peano.ten) exponent he
  let B := listVal remainder * Peano.ten
  let C := d.val
  let N := Peano.tenPow ds.length
  let T := listVal ds
  exact calc A * N + B * N + (C * N + T)
      = A * N + (B * N + (C * N + T)) :=
        Peano.add_associative (A * N) (B * N) (C * N + T)
    _ = A * N + ((B * N + C * N) + T) := by
        rw [← Peano.add_associative (B * N) (C * N) T]
    _ = A * N + ((B + C) * N + T) := by
        rw [← Peano.multiply_distributive_over_add_left B C N]
    _ = (A * N + (B + C) * N) + T :=
        (Peano.add_associative (A * N) ((B + C) * N) T).symm
    _ = (A + (B + C)) * N + T := by
        rw [← Peano.multiply_distributive_over_add_left A (B + C) N]
    _ = ((B + C) + A) * N + T := by
        rw [Peano.add_commutative A (B + C)]

theorem rootWindow_after_choose (currentRoot remainder : Sequences.List Digit)
    (d : Digit) (ds : Sequences.List Digit) (exponent : Decimal) (he : ¬ exponent ≈ zero)
    (groupSize : Peano) (q : Digit) (nextRem : Sequences.List Digit)
    (hgs : groupSize = toPeano exponent)
    (hle : Peano.one ≤ groupSize)
    (heq : listVal (Sequences.List.append remainder d) +
        powE (listVal currentRoot * Peano.ten) exponent he =
      powE (listVal currentRoot * Peano.ten + q.val) exponent he +
        listVal nextRem) :
    rootWindow currentRoot remainder (Sequences.List.firstElement d ds)
      exponent he groupSize Peano.one hle =
    rootWindow (appendRootDigit currentRoot q) nextRem ds exponent he
      groupSize groupSize (Or.inr rfl) := by
  have hpad0 : rootPad groupSize groupSize (Or.inr rfl) = Peano.zero :=
    Peano.subtract_eq_zero_of_eq (Or.inr rfl) rfl
  have hY : listVal (appendRootDigit currentRoot q) =
      listVal currentRoot * Peano.ten + q.val :=
    listVal_appendRootDigit currentRoot q
  rw [rootWindow_at_choose currentRoot remainder d ds exponent he groupSize hgs hle, heq]
  unfold rootWindow
  rw [hY, hpad0, Peano.add_zero]
  rw [Peano.multiply_distributive_over_add_left]

theorem rootWindow_initial (a e : Decimal) (he : ¬ e ≈ zero)
    (remaining : Peano)
    (hle : remaining ≤ toPeano e) :
    rootWindow Sequences.List.empty Sequences.List.empty a.val e he
      (toPeano e) remaining hle = toPeano a := by
  unfold rootWindow toPeano
  rw [listVal_empty, powE_zero, Peano.zero_multiply,
    Peano.zero_add, Peano.zero_multiply,
    Peano.zero_add]

theorem rootWithRemainderAux_spec
    (digits : Sequences.List Digit) (exponent : Decimal) (he : ¬ exponent ≈ zero)
    (groupSize : Peano)
    (hgs : groupSize = toPeano exponent) :
    ∀ (currentRoot remainder : Sequences.List Digit)
      (remainingInGroup : Peano),
      remainingInGroup ≠ Peano.zero →
      ∀ (hle : remainingInGroup ≤ groupSize),
        (digits.length = Peano.zero ∨
          ∃ q, digits.length = groupSize * q + remainingInGroup) →
        (digits.length = Peano.zero →
          remainingInGroup = groupSize) →
        rootWindow currentRoot remainder digits exponent he
            groupSize remainingInGroup hle <
          powE (listVal currentRoot).successor exponent he *
            Peano.tenPow
              (digits.length + rootPad groupSize remainingInGroup hle) →
      let result :=
        rootWithRemainderAux (powerListOrZero · exponent) digits groupSize currentRoot remainder
          remainingInGroup
      rootWindow currentRoot remainder digits exponent he
          groupSize remainingInGroup hle =
        powE (listVal result.1) exponent he + listVal result.2 ∧
      powE (listVal result.1) exponent he + listVal result.2 <
        powE (listVal result.1).successor exponent he := by
  induction digits with
  | empty =>
    intro currentRoot remainder remainingInGroup hk hle hmod hempty hbound
    have hrem_eq : remainingInGroup = groupSize := hempty rfl
    have hpad : rootPad groupSize remainingInGroup hle =
        Peano.zero :=
      Peano.subtract_eq_zero_of_eq hle hrem_eq.symm
    have hwin :
        rootWindow currentRoot remainder Sequences.List.empty exponent he
          groupSize remainingInGroup hle =
          powE (listVal currentRoot) exponent he + listVal remainder := by
      unfold rootWindow
      rw [hpad, listVal_empty]
      change
        powE (listVal currentRoot) exponent he *
            Peano.tenPow
              (Peano.zero + Peano.zero) +
          listVal remainder *
            Peano.tenPow Peano.zero +
          Peano.zero =
        powE (listVal currentRoot) exponent he + listVal remainder
      rw [Peano.add_zero]
      change
        powE (listVal currentRoot) exponent he *
            Peano.tenPow Peano.zero +
          listVal remainder *
            Peano.tenPow Peano.zero +
          Peano.zero =
        powE (listVal currentRoot) exponent he + listVal remainder
      rw [Peano.tenPow, Peano.multiply_one,
        Peano.multiply_one, Peano.add_zero]
    unfold rootWithRemainderAux
    constructor
    · exact hwin
    · have hlen0 :
          (Sequences.List.empty : Sequences.List Digit).length =
            Peano.zero := rfl
      rw [hwin] at hbound
      have hexp0 :
          (Sequences.List.empty : Sequences.List Digit).length +
            rootPad groupSize remainingInGroup hle =
            Peano.zero := by
        rw [hlen0, hpad, Peano.add_zero]
      rw [hexp0, Peano.tenPow, Peano.multiply_one] at hbound
      exact hbound
  | firstElement d ds ih =>
    intro currentRoot remainder remainingInGroup hk hle hmod hempty hbound
    unfold rootWithRemainderAux
    cases remainingInGroup with
    | zero => exact False.elim (hk rfl)
    | successor remaining' =>
      cases remaining' with
      | zero =>
        obtain ⟨heq, _, hmax⟩ :=
          findRootDigit_spec (Sequences.List.append remainder d) exponent he currentRoot
        let qDigit :=
          (findRootDigit (powerListOrZero · exponent) (Sequences.List.append remainder d) currentRoot).1
        let nextRem :=
          (findRootDigit (powerListOrZero · exponent) (Sequences.List.append remainder d) currentRoot).2
        have hlen_ne :
            (Sequences.List.firstElement d ds).length ≠
              Peano.zero := by
          rw [Sequences.List.length_firstElement]
          exact Peano.successor_ne_zero _
        have hmod_ds :
            ds.length = Peano.zero ∨
              ∃ q, ds.length = groupSize * q + groupSize := by
          cases hmod with
          | inl h0 => exact False.elim (hlen_ne h0)
          | inr hex =>
            obtain ⟨q0, hq0⟩ := hex
            rw [Sequences.List.length_firstElement] at hq0
            exact Peano.eq_zero_or_mul_add_self_of_succ_eq_mul_add_one
              ds.length groupSize q0 hq0
        have hk_new : groupSize ≠ Peano.zero := by
          rw [hgs]
          exact toPeano_ne_zero_of_not_equivalent_zero he
        have hle_new : groupSize ≤ groupSize := Or.inr rfl
        have hempty_new :
            ds.length = Peano.zero → groupSize = groupSize :=
          fun _ => rfl
        have hwin :=
          rootWindow_after_choose currentRoot remainder d ds exponent he
            groupSize qDigit nextRem hgs hle heq
        have hY :
            listVal (appendRootDigit currentRoot qDigit) =
              listVal currentRoot * Peano.ten + qDigit.val :=
          listVal_appendRootDigit currentRoot qDigit
        have hexp :
            (Sequences.List.firstElement d ds).length +
              rootPad groupSize Peano.zero.successor hle =
            ds.length + groupSize := by
          rw [Sequences.List.length_firstElement]
          unfold rootPad
          exact Peano.succ_add_sub_one ds.length groupSize hle
        have hbound_new :
            rootWindow (appendRootDigit currentRoot qDigit) nextRem ds exponent he
              groupSize groupSize hle_new <
            powE (listVal (appendRootDigit currentRoot qDigit)).successor exponent he *
              Peano.tenPow
                (ds.length + rootPad groupSize groupSize hle_new) := by
          have hpad0 :
              rootPad groupSize groupSize hle_new = Peano.zero :=
            Peano.subtract_eq_zero_of_eq hle_new rfl
          rw [hpad0, Peano.add_zero]
          rw [← hwin]
          cases hmax with
          | inl hq9 =>
            have hsucc :
                (listVal (appendRootDigit currentRoot qDigit)).successor =
                  (listVal currentRoot).successor * Peano.ten := by
              rw [hY, hq9]
              exact Peano.succ_nine_mul_ten (listVal currentRoot)
            have hbound' := hbound
            rw [hexp, Peano.tenPow_add] at hbound'
            have htenE :
                Peano.tenPow groupSize =
                  Peano.tenPow (toPeano exponent) := by
              rw [hgs]
            rw [htenE] at hbound'
            rw [Peano.multiply_commutative
              (Peano.tenPow ds.length)
              (Peano.tenPow (toPeano exponent))] at hbound'
            rw [← Peano.multiply_associative] at hbound'
            rw [← powE_mul_ten (listVal currentRoot).successor exponent he] at hbound'
            rwa [← hsucc] at hbound'
          | inr hpre =>
            have hexpand :=
              rootWindow_at_choose currentRoot remainder d ds exponent he
                groupSize hgs hle
            have hsucc :
                (listVal (appendRootDigit currentRoot qDigit)).successor =
                  listVal currentRoot * Peano.ten +
                    qDigit.val.successor := by
              rw [hY, Peano.add_successor]
            rw [hexpand]
            rw [hsucc]
            exact Peano.mul_tenPow_add_lt_of_lt
              hpre (toCardinalNaturalPeano_lt_tenPow ds)
        obtain ⟨ih_eq, ih_lt⟩ :=
          ih (appendRootDigit currentRoot qDigit) nextRem groupSize
            hk_new hle_new hmod_ds hempty_new hbound_new
        constructor
        · exact hwin.trans ih_eq
        · exact ih_lt
      | successor n =>
        have hle_new :
            n.successor ≤ groupSize := Peano.le_of_succ_le hle
        have hk_new : n.successor ≠ Peano.zero :=
          Peano.successor_ne_zero n
        have hlen_ne :
            (Sequences.List.firstElement d ds).length ≠
              Peano.zero := by
          rw [Sequences.List.length_firstElement]
          exact Peano.successor_ne_zero _
        have hds_ne : ds.length ≠ Peano.zero := by
          intro hz
          cases hmod with
          | inl h0 => exact hlen_ne h0
          | inr hex =>
            obtain ⟨q, hq⟩ := hex
            have hlen1 :
                (Sequences.List.firstElement d ds).length =
                  Peano.one := by
              rw [Sequences.List.length_firstElement, hz]
              rfl
            rw [hlen1] at hq
            exact Peano.one_ne_mul_add_of_two_le
              groupSize n.successor.successor q
              (Peano.two_le_succ_succ n) hle hq
        have hmod_ds :
            ds.length = Peano.zero ∨
              ∃ q, ds.length = groupSize * q + n.successor := by
          cases hmod with
          | inl h0 => exact False.elim (hlen_ne h0)
          | inr hex =>
            obtain ⟨q, hq⟩ := hex
            refine Or.inr ⟨q, ?_⟩
            apply Peano.successor_injective
            rw [← Sequences.List.length_firstElement, hq,
              Peano.add_successor]
        have hempty_new :
            ds.length = Peano.zero → n.successor = groupSize :=
          fun h0 => False.elim (hds_ne h0)
        have hwin :=
          rootWindow_bring_down currentRoot remainder d ds exponent he
            groupSize n hle
        have hexp :
            (Sequences.List.firstElement d ds).length +
              rootPad groupSize n.successor.successor hle =
            ds.length + rootPad groupSize n.successor hle_new := by
          unfold rootPad
          rw [Sequences.List.length_firstElement,
            Peano.subtract_succ_eq_pred_subtract groupSize n.successor hle,
            Peano.successor_add, Peano.add_successor]
        have hbound_new :
            rootWindow currentRoot (Sequences.List.append remainder d) ds
              exponent he groupSize n.successor hle_new <
            powE (listVal currentRoot).successor exponent he *
              Peano.tenPow
                (ds.length + rootPad groupSize n.successor hle_new) := by
          rw [← hwin, ← hexp]
          exact hbound
        obtain ⟨ih_eq, ih_lt⟩ :=
          ih currentRoot (Sequences.List.append remainder d) n.successor
            hk_new hle_new hmod_ds hempty_new hbound_new
        constructor
        · exact hwin.trans ih_eq
        · exact ih_lt

theorem toPeano_of_maybeEmpty (digits : Sequences.List Digit) :
    toPeano (if h : digits = Sequences.List.empty then zero
      else normalizeList digits h) = listVal digits := by
  by_cases h : digits = Sequences.List.empty
  · rw [dif_pos h, h, toPeano_zero, listVal_empty]
  · rw [dif_neg h]
    exact normalizeList_toPeano digits h

theorem rootWithRemainder_spec (a e : Decimal) (he : ¬ e ≈ zero) :
    let result := rootWithRemainder a e he
    a.toPeano =
      powE result.1.toPeano e he + result.2.toPeano ∧
    a.toPeano <
      powE result.1.toPeano.successor e he := by
  unfold rootWithRemainder
  dsimp only
  cases h_aux : rootWithRemainderAux (powerListOrZero · e) a.val e.toPeano
      Sequences.List.empty Sequences.List.empty
      (firstRootGroupSize a.val.length e.toPeano
        (toPeano_ne_zero_of_not_equivalent_zero he)) with
  | mk rootDigits remDigits =>
    have hlen_ne := Sequences.List.length_ne_zero_of_ne_empty a.property
    have hk :=
      firstRootGroupSize_ne_zero a.val.length e.toPeano
        (toPeano_ne_zero_of_not_equivalent_zero he)
    have hle :=
      firstRootGroupSize_le a.val.length e.toPeano
        (toPeano_ne_zero_of_not_equivalent_zero he)
    have hmod :
        a.val.length = Peano.zero ∨
          ∃ q, a.val.length =
            e.toPeano * q +
              firstRootGroupSize a.val.length e.toPeano
                (toPeano_ne_zero_of_not_equivalent_zero he) :=
      Or.inr (firstRootGroupSize_mod a.val.length e.toPeano
        (toPeano_ne_zero_of_not_equivalent_zero he) hlen_ne)
    have hempty :
        a.val.length = Peano.zero →
          firstRootGroupSize a.val.length e.toPeano
            (toPeano_ne_zero_of_not_equivalent_zero he) = e.toPeano :=
      fun h0 => False.elim (hlen_ne h0)
    have hwin0 := rootWindow_initial a e he
      (firstRootGroupSize a.val.length e.toPeano
        (toPeano_ne_zero_of_not_equivalent_zero he)) hle
    have hbound :
        rootWindow Sequences.List.empty Sequences.List.empty a.val e he
          e.toPeano
          (firstRootGroupSize a.val.length e.toPeano
            (toPeano_ne_zero_of_not_equivalent_zero he)) hle <
        powE (listVal Sequences.List.empty).successor e he *
          Peano.tenPow
            (a.val.length +
              rootPad e.toPeano
                (firstRootGroupSize a.val.length e.toPeano
                  (toPeano_ne_zero_of_not_equivalent_zero he)) hle) := by
      rw [hwin0]
      have hsucc0 :
          (listVal Sequences.List.empty).successor = Peano.one := rfl
      rw [hsucc0, powE_one, Peano.one_multiply]
      have hlt := toCardinalNaturalPeano_lt_tenPow a.val
      have hle_pow :
          Peano.tenPow a.val.length ≤
            Peano.tenPow
              (a.val.length +
                rootPad e.toPeano
                  (firstRootGroupSize a.val.length e.toPeano
                    (toPeano_ne_zero_of_not_equivalent_zero he)) hle) :=
        Peano.tenPow_monotone
          (Peano.le_add_self_left _ _)
      exact Peano.lt_of_lt_of_le hlt hle_pow
    have hspec :=
      rootWithRemainderAux_spec a.val e he e.toPeano rfl
        Sequences.List.empty Sequences.List.empty
        (firstRootGroupSize a.val.length e.toPeano
          (toPeano_ne_zero_of_not_equivalent_zero he))
        hk hle hmod hempty hbound
    rw [h_aux] at hspec
    dsimp only at hspec
    rw [hwin0] at hspec
    obtain ⟨heq, hlt⟩ := hspec
    constructor
    · rw [toPeano_of_maybeEmpty, toPeano_of_maybeEmpty]
      exact heq
    · rw [toPeano_of_maybeEmpty, heq]
      exact hlt

theorem rootWithRemainder_toPeano (a e : Decimal) (he : ¬ e ≈ zero)
    {b r : Decimal}
    (h : rootWithRemainder a e he = (b, r)) :
    ∃ h2, Peano.rootWithRemainder a.toPeano e.toPeano h2 =
      (b.toPeano, r.toPeano) := by
  have hspec := rootWithRemainder_spec a e he
  rw [h] at hspec
  dsimp only at hspec
  obtain ⟨h_eq, h_lt⟩ := hspec
  refine ⟨toPeano_ne_zero_of_not_equivalent_zero he, ?_⟩
  exact Peano.rootWithRemainder_eq_of a.toPeano e.toPeano
    (toPeano_ne_zero_of_not_equivalent_zero he)
    b.toPeano r.toPeano h_eq h_lt

/-- A nonzero remainder cannot occur when `a` is an exact `e`-th power. -/
theorem rootWithRemainder_nonzero_power (a e b r : Decimal)
    (he : ¬ e ≈ zero) (h : Power e a)
    (hres : rootWithRemainder a e he = (b, r)) (hr : ¬ r ≈ zero) : False := by
  obtain ⟨h2, hp⟩ := rootWithRemainder_toPeano a e he hres
  have hr_ne : r.toPeano ≠ Peano.zero :=
    toPeano_ne_zero_of_not_equivalent_zero hr
  cases hr_peano : r.toPeano with
  | zero => exact hr_ne hr_peano
  | successor rem =>
    have hp' : Peano.rootWithRemainder a.toPeano e.toPeano h2 =
        (b.toPeano, rem.successor) := by
      rw [← hr_peano]
      exact hp
    exact Peano.rootWithRemainder_succ_power a.toPeano e.toPeano h2
      b.toPeano rem ((Power_toPeano e a).mp h) hp'

/-- Integer `e`-th root, or `none` when `e ≈ zero` or `a` is not an exact power. -/
def tryRoot (e a : Decimal) : Option Decimal :=
  if h : e ≈ zero then
    none
  else
    match rootWithRemainder a e h with
    | (b, r) => if r ≈ zero then some b else none

/-- Integer `e`-th root of an exact power `a`, for nonzero exponent `e`. -/
def root (e a : Decimal) (h : ¬ e ≈ zero ∧ Power e a) : Decimal :=
  match hres : rootWithRemainder a e h.1 with
  | (b, r) =>
    if hr : r ≈ zero then b
    else False.elim (rootWithRemainder_nonzero_power a e b r h.1 h.2 hres hr)

theorem root_toPeano (e a : Decimal) (h : ¬ e ≈ zero ∧ Power e a) :
    ∃ h2, (root e a h).toPeano = Peano.root e.toPeano a.toPeano h2 := by
  let h2 : e.toPeano ≠ Peano.zero ∧ Peano.Power e.toPeano a.toPeano :=
    ⟨toPeano_ne_zero_of_not_equivalent_zero h.1, (Power_toPeano e a).mp h.2⟩
  refine ⟨h2, ?_⟩
  cases hres : rootWithRemainder a e h.1 with
  | mk b r =>
    unfold root
    simp only [hres]
    by_cases hr : r ≈ zero
    · simp only [hr, ↓reduceDIte]
      obtain ⟨_, hp⟩ := rootWithRemainder_toPeano a e h.1 hres
      have hr0 : r.toPeano = Peano.zero :=
        (toPeano_eq_of_equivalent hr).trans toPeano_zero
      have hp' : Peano.rootWithRemainder a.toPeano e.toPeano h2.1 =
          (b.toPeano, Peano.zero) := by
        rwa [hr0] at hp
      unfold Peano.root
      split
      · next b' hres' =>
        have heq : (b', Peano.zero) = (b.toPeano, Peano.zero) :=
          hres'.symm.trans hp'
        exact (congrArg Prod.fst heq).symm
      · next b' rem hres' =>
        exact False.elim
          (Peano.rootWithRemainder_succ_power a.toPeano e.toPeano h2.1
            b' rem h2.2 hres')
    · simp only [hr, ↓reduceDIte]
      exact False.elim (rootWithRemainder_nonzero_power a e b r h.1 h.2 hres hr)

/-- Raising the extracted root to the exponent recovers `a`. -/
theorem root_correct (e a : Decimal) (h : ¬ e ≈ zero ∧ Power e a) :
    ∃ hroot : ¬ root e a h ≈ zero ∨ ¬ e ≈ zero,
      power (root e a h) e hroot ≈ a := by
  refine ⟨Or.inr h.1, equivalent_of_toPeano_eq ?_⟩
  obtain ⟨h2, hroot_peano⟩ := root_toPeano e a h
  obtain ⟨hrootP, hpow⟩ := Peano.root_is_power e.toPeano a.toPeano h2
  have hcond : (root e a h).toPeano ≠ Peano.zero ∨ e.toPeano ≠ Peano.zero :=
    Or.inr (toPeano_ne_zero_of_not_equivalent_zero h.1)
  rw [power_toPeano_eq (root e a h) e (Or.inr h.1) hcond]
  exact (Peano.eq_rec_power _ _ _ hroot_peano hcond hrootP).trans hpow

/-- The `e`-th root of `x ^ e` is equivalent to `x` when `e` is nonzero. -/
theorem root_power_eq (e x : Decimal) (he : ¬ e ≈ zero)
    (h2 : ¬ x ≈ zero ∨ ¬ e ≈ zero) :
    ∃ h, root e (power x e h2) h ≈ x := by
  let h : ¬ e ≈ zero ∧ Power e (power x e h2) :=
    ⟨he, ⟨x, h2, rfl⟩⟩
  refine ⟨h, equivalent_of_toPeano_eq ?_⟩
  obtain ⟨hroot, hpow⟩ := root_correct e (power x e h2) h
  have hcorrect := toPeano_eq_of_equivalent hpow
  have hp_root :=
    power_toPeano_eq (root e (power x e h2) h) e hroot
      (power_condition_toPeano hroot)
  have hp_x := power_toPeano_eq x e h2 (power_condition_toPeano h2)
  exact Peano.power_injective_base
    (root e (power x e h2) h).toPeano x.toPeano e.toPeano
    (toPeano_ne_zero_of_not_equivalent_zero he)
    (power_condition_toPeano hroot) (power_condition_toPeano h2)
    (hp_root.symm.trans (hcorrect.trans hp_x))

theorem tryRoot_toPeano (e a : Decimal) :
    Option.map toPeano (tryRoot e a) = Peano.tryRoot e.toPeano a.toPeano := by
  by_cases he : e ≈ zero
  · have he_peano : e.toPeano = Peano.zero :=
      (toPeano_eq_of_equivalent he).trans toPeano_zero
    rw [he_peano]
    simp only [tryRoot, he, ↓reduceDIte, Peano.tryRoot]
    rfl
  · have he_ne : e.toPeano ≠ Peano.zero :=
      toPeano_ne_zero_of_not_equivalent_zero he
    cases hres : rootWithRemainder a e he with
    | mk b r =>
      by_cases hr : r ≈ zero
      · have htry : tryRoot e a = some b := by
          simp only [tryRoot, he, ↓reduceDIte, hres, hr, ↓reduceIte]
        rw [htry]
        cases he_peano : e.toPeano with
        | zero => exact False.elim (he_ne he_peano)
        | successor e' =>
          obtain ⟨_, hp⟩ := rootWithRemainder_toPeano a e he hres
          have hr0 : r.toPeano = Peano.zero :=
            (toPeano_eq_of_equivalent hr).trans toPeano_zero
          have hp0 :
              Peano.rootWithRemainder a.toPeano e'.successor
                (Peano.successor_ne_zero e') = (b.toPeano, Peano.zero) := by
            simp only [he_peano] at hp
            rwa [hr0] at hp
          simp only [Peano.tryRoot, hp0]
          rfl
      · have htry : tryRoot e a = none := by
          simp only [tryRoot, he, ↓reduceDIte, hres, hr, ↓reduceIte]
        rw [htry]
        cases he_peano : e.toPeano with
        | zero => exact False.elim (he_ne he_peano)
        | successor e' =>
          obtain ⟨_, hp⟩ := rootWithRemainder_toPeano a e he hres
          have hr_ne : r.toPeano ≠ Peano.zero :=
            toPeano_ne_zero_of_not_equivalent_zero hr
          cases hr_peano : r.toPeano with
          | zero => exact False.elim (hr_ne hr_peano)
          | successor rem =>
            have hp_succ :
                Peano.rootWithRemainder a.toPeano e'.successor
                  (Peano.successor_ne_zero e') = (b.toPeano, rem.successor) := by
              simp only [he_peano] at hp
              rwa [hr_peano] at hp
            simp only [Peano.tryRoot, hp_succ]
            rfl

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

def isDivisible (a b : Decimal) : Bool :=
  if h : b ≈ zero then
    false
  else
    decide ((divideWithRemainder a b h).2 ≈ zero)

theorem isDivisible_eq_peano (a b : Decimal) :
    isDivisible a b = Peano.isDivisible a.toPeano b.toPeano := by
  unfold isDivisible Peano.isDivisible
  by_cases hb : b ≈ zero
  · have hb_peano : b.toPeano = Peano.zero :=
      (toPeano_eq_of_equivalent hb).trans toPeano_zero
    simp only [hb, ↓reduceDIte, hb_peano]
  · simp only [hb, ↓reduceDIte]
    have hb_ne : b.toPeano ≠ Peano.zero :=
      toPeano_ne_zero_of_not_equivalent_zero hb
    cases hb_peano : b.toPeano with
    | zero => exact False.elim (hb_ne hb_peano)
    | successor b' =>
      cases hres : divideWithRemainder a b hb with
      | mk q r =>
        obtain ⟨h2, hpeano⟩ := divideWithRemainder_toPeano a b hb hres
        have hpeano' :
            Peano.divideWithRemainder a.toPeano b'.successor
              (Peano.successor_ne_zero b') = (q.toPeano, r.toPeano) := by
          simp only [hb_peano] at hpeano
          exact hpeano
        simp only [hpeano']
        cases hr_peano : r.toPeano with
        | zero =>
          have heq : r ≈ zero :=
            equivalent_of_toPeano_eq (hr_peano.trans toPeano_zero.symm)
          simp only [heq, decide_true]
        | successor r' =>
          have hne : ¬ r ≈ zero := by
            intro heq
            have hr0 : r.toPeano = Peano.zero :=
              (toPeano_eq_of_equivalent heq).trans toPeano_zero
            exact Peano.successor_ne_zero r' (hr_peano.symm.trans hr0)
          simp only [hne, decide_false]

theorem isDivisibleCorrect (a b : Decimal) : Divisible a b ↔ isDivisible a b := by
  rw [divisibleToPeano, isDivisible_eq_peano]
  exact Peano.isDivisibleCorrect a.toPeano b.toPeano

def tryDivide (a b : Decimal) : Option Decimal :=
  if h : b ≈ zero then
    none
  else
    match divideWithRemainder a b h with
    | (q, r) => if r ≈ zero then some q else none

theorem exists_divide_of_tryDivide {x y z : Decimal} (h : tryDivide x y = some z) :
    ∃ h', divide x y h' = z := by
  unfold tryDivide at h
  split at h
  · next => cases h
  · next hb =>
    cases hres : divideWithRemainder x y hb with
    | mk q r =>
      simp only [hres] at h
      split at h
      · next hr =>
        injection h with hz
        have hspec := divideWithRemainder_spec x y hb
        rw [hres] at hspec
        dsimp only at hspec
        obtain ⟨heq, _⟩ := hspec
        have hr0 : r.toPeano = Peano.zero :=
          (toPeano_eq_of_equivalent hr).trans toPeano_zero
        have hx : y * q ≈ x := by
          apply equivalent_of_toPeano_eq
          rw [multiply_toPeano, heq, hr0, Peano.add_zero]
        let hdiv : Divisible x y := ⟨hb, q, hx⟩
        refine ⟨hdiv, ?_⟩
        simp only [divide, hres, hz]
      · next => cases h

theorem tryDivide_of_divide {x y z : Decimal} (h : ∃ h', divide x y h' = z) :
    tryDivide x y = some z := by
  obtain ⟨hdiv, heq⟩ := h
  unfold tryDivide
  simp only [dif_neg hdiv.1]
  cases hres : divideWithRemainder x y hdiv.1 with
  | mk q r =>
    have hqz : q = z := by
      simp only [divide, hres] at heq
      exact heq
    have hr0 : r ≈ zero := by
      have hspec := divideWithRemainder_spec x y hdiv.1
      rw [hres] at hspec
      dsimp only at hspec
      obtain ⟨heq_peano, _⟩ := hspec
      obtain ⟨h2, hdiv_eq⟩ := divide_toPeano x y hdiv
      have hz_peano : z.toPeano = Peano.divide x.toPeano y.toPeano h2 := by
        rw [← heq]
        exact hdiv_eq
      have hx : x.toPeano = y.toPeano * q.toPeano := by
        calc
          x.toPeano
              = y.toPeano * Peano.divide x.toPeano y.toPeano h2 :=
                (Peano.multiply_divide x.toPeano y.toPeano h2).symm
          _ = y.toPeano * z.toPeano := by rw [hz_peano]
          _ = y.toPeano * q.toPeano := by rw [hqz]
      have hadd :
          y.toPeano * q.toPeano + r.toPeano =
            y.toPeano * q.toPeano + Peano.zero := by
        rw [← heq_peano, hx, Peano.add_zero]
      have hr_peano : r.toPeano = Peano.zero :=
        Peano.add_left_cancel (y.toPeano * q.toPeano) r.toPeano Peano.zero hadd
      exact equivalent_of_toPeano_eq (hr_peano.trans toPeano_zero.symm)
    simp [hr0, hqz]

/-- A successful `tryDivide` recovers the multiplicative relation `y * q ≈ x`. -/
theorem eq_of_tryDivide_mul {x y q : Decimal} (h : tryDivide x y = some q) :
    y * q ≈ x := by
  obtain ⟨hdiv, heq⟩ := exists_divide_of_tryDivide h
  obtain ⟨h2, hdiv_eq⟩ := divide_toPeano x y hdiv
  apply equivalent_of_toPeano_eq
  rw [← heq, multiply_toPeano, hdiv_eq]
  exact Peano.multiply_divide x.toPeano y.toPeano h2

/-- When `a ≈ b * q` and `b` is nonzero, `tryDivide a b` recovers a value
equivalent to `q`. -/
theorem tryDivide_of_equivalent_mul {a b q : Decimal} (hb : ¬ b ≈ zero)
    (h : a ≈ b * q) :
    Option.Rel (· ≈ ·) (tryDivide a b) (some q) := by
  let hdiv : Divisible a b := ⟨hb, q, Setoid.symm h⟩
  have hquot : divide a b hdiv ≈ q := by
    apply equivalent_of_toPeano_eq
    obtain ⟨h2, hdiv_eq⟩ := divide_toPeano a b hdiv
    have hq := toPeano_eq_of_equivalent h
    rw [hdiv_eq]
    apply Peano.multiply_left_cancel b.toPeano
      (Peano.divide a.toPeano b.toPeano h2) q.toPeano
      (toPeano_ne_zero_of_not_equivalent_zero hb)
    rw [Peano.multiply_divide a.toPeano b.toPeano h2, hq, multiply_toPeano]
  have htry : tryDivide a b = some (divide a b hdiv) :=
    tryDivide_of_divide ⟨hdiv, rfl⟩
  rw [htry]
  exact Option.Rel.some hquot

/-- Dividing a left product by its nonzero left factor recovers the right factor. -/
theorem divide_multiply_eq (x y : Decimal) (hy : ¬ y ≈ zero) :
    ∃ h, divide (y * x) y h ≈ x := by
  let h : Divisible (y * x) y := ⟨hy, x, rfl⟩
  refine ⟨h, ?_⟩
  apply equivalent_of_toPeano_eq
  obtain ⟨h2, hdiv⟩ := divide_toPeano (y * x) y h
  rw [hdiv]
  exact Peano.multiply_left_cancel y.toPeano
    (Peano.divide (y * x).toPeano y.toPeano h2) x.toPeano
    (toPeano_ne_zero_of_not_equivalent_zero hy)
    (by
      rw [Peano.multiply_divide (y * x).toPeano y.toPeano h2, multiply_toPeano])

theorem divide_add (x y z : Decimal) (h : Divisible x z) (h2 : Divisible y z) :
    ∃ h3, divide x z h + divide y z h2 ≈ divide (x + y) z h3 := by
  let h3 : Divisible (x + y) z :=
    ⟨h.1, divide x z h + divide y z h2, by
      apply equivalent_of_toPeano_eq
      obtain ⟨hx_div, hx⟩ := divide_toPeano x z h
      obtain ⟨hy_div, hy⟩ := divide_toPeano y z h2
      rw [multiply_toPeano, add_toPeano, add_toPeano,
        Peano.multiply_distributive_over_add_right, hx, hy,
        Peano.multiply_divide x.toPeano z.toPeano hx_div,
        Peano.multiply_divide y.toPeano z.toPeano hy_div]⟩
  refine ⟨h3, ?_⟩
  apply equivalent_of_toPeano_eq
  obtain ⟨hx_div, hx⟩ := divide_toPeano x z h
  obtain ⟨hy_div, hy⟩ := divide_toPeano y z h2
  obtain ⟨hxy_div, hxy⟩ := divide_toPeano (x + y) z h3
  exact Peano.multiply_left_cancel z.toPeano
    (divide x z h + divide y z h2).toPeano
    (divide (x + y) z h3).toPeano
    (toPeano_ne_zero_of_not_equivalent_zero h.1)
    (by
      rw [add_toPeano, Peano.multiply_distributive_over_add_right, hx, hy, hxy,
        Peano.multiply_divide x.toPeano z.toPeano hx_div,
        Peano.multiply_divide y.toPeano z.toPeano hy_div,
        Peano.multiply_divide (x + y).toPeano z.toPeano hxy_div, add_toPeano])

/-- Division distributes over subtraction up to Decimal equivalence. -/
theorem divide_subtract_distrib {x y z : Decimal}
    (h1 : Divisible x z) (h2 : Divisible y z) (h3 : y ≤ x) :
    ∃ h4 h5, divide (subtract x y h3) z h4 ≈
      subtract (divide x z h1) (divide y z h2) h5 := by
  let qx := divide x z h1
  let qy := divide y z h2
  obtain ⟨hx_div, hx⟩ := divide_toPeano x z h1
  obtain ⟨hy_div, hy⟩ := divide_toPeano y z h2
  have h3p : y.toPeano ≤ x.toPeano := toPeano_le_of_le h3
  have hmul_le : z.toPeano * qy.toPeano ≤ z.toPeano * qx.toPeano := by
    rw [hy, hx, Peano.multiply_divide y.toPeano z.toPeano hy_div,
      Peano.multiply_divide x.toPeano z.toPeano hx_div]
    exact h3p
  have h5 : qy ≤ qx :=
    le_of_toPeano_le
      (Peano.le_of_multiply_le_multiply_left z.toPeano qy.toPeano qx.toPeano
        (toPeano_ne_zero_of_not_equivalent_zero h1.1) hmul_le)
  have h_wit : z * subtract qx qy h5 ≈ subtract x y h3 := by
    apply equivalent_of_toPeano_eq
    obtain ⟨hmul_le', hdist⟩ := multiply_subtract_distributive z qx qy h5
    have hdist_peano := toPeano_eq_of_equivalent hdist
    obtain ⟨h_peano_lt, h_sub_mul⟩ := subtract_toPeano (z * qx) (z * qy) hmul_le'
    obtain ⟨h_peano_xy, h_sub_xy⟩ := subtract_toPeano x y h3
    have h_eq_sub :=
      Peano.subtract_eq_of_eq h_peano_lt h_peano_xy
        (by
          rw [multiply_toPeano, hx]
          exact Peano.multiply_divide x.toPeano z.toPeano hx_div)
        (by
          rw [multiply_toPeano, hy]
          exact Peano.multiply_divide y.toPeano z.toPeano hy_div)
    calc (z * subtract qx qy h5).toPeano
        = (subtract (z * qx) (z * qy) hmul_le').toPeano := hdist_peano
      _ = Peano.subtract (z * qx).toPeano (z * qy).toPeano h_peano_lt := h_sub_mul
      _ = Peano.subtract x.toPeano y.toPeano h_peano_xy := h_eq_sub
      _ = (subtract x y h3).toPeano := h_sub_xy.symm
  let h4 : Divisible (subtract x y h3) z := ⟨h1.1, subtract qx qy h5, h_wit⟩
  refine ⟨h4, h5, ?_⟩
  apply equivalent_of_toPeano_eq
  obtain ⟨h4_div, hdiv⟩ := divide_toPeano (subtract x y h3) z h4
  have hw := toPeano_eq_of_equivalent h_wit
  rw [multiply_toPeano] at hw
  exact Peano.multiply_left_cancel z.toPeano
    (divide (subtract x y h3) z h4).toPeano
    (subtract qx qy h5).toPeano
    (toPeano_ne_zero_of_not_equivalent_zero h1.1)
    (by
      rw [hdiv, Peano.multiply_divide (subtract x y h3).toPeano z.toPeano h4_div]
      exact hw.symm)

/-- Multiplying before dividing by a divisor of the second factor is equivalent to
dividing the product by that same divisor. -/
theorem multiply_divide_assoc (x y z : Decimal) (h : Divisible y z) :
    ∃ h2, x * divide y z h ≈ divide (x * y) z h2 := by
  let h2 : Divisible (x * y) z :=
    ⟨h.1, x * divide y z h, by
      apply equivalent_of_toPeano_eq
      obtain ⟨hy_div, hy⟩ := divide_toPeano y z h
      rw [multiply_toPeano, multiply_toPeano, multiply_toPeano, hy,
        ← Peano.multiply_associative, Peano.multiply_commutative z.toPeano x.toPeano,
        Peano.multiply_associative, Peano.multiply_divide y.toPeano z.toPeano hy_div]⟩
  refine ⟨h2, ?_⟩
  apply equivalent_of_toPeano_eq
  obtain ⟨hy_div, hy⟩ := divide_toPeano y z h
  obtain ⟨hxy_div, hxy⟩ := divide_toPeano (x * y) z h2
  exact Peano.multiply_left_cancel z.toPeano
    (x * divide y z h).toPeano
    (divide (x * y) z h2).toPeano
    (toPeano_ne_zero_of_not_equivalent_zero h.1)
    (by
      rw [multiply_toPeano, hxy, ← Peano.multiply_associative,
        Peano.multiply_commutative z.toPeano x.toPeano, Peano.multiply_associative, hy,
        Peano.multiply_divide y.toPeano z.toPeano hy_div,
        Peano.multiply_divide (x * y).toPeano z.toPeano hxy_div, multiply_toPeano])

theorem divide_divide_eq_divide_multiply_h2 {x y z : Decimal}
    (h1 : Divisible x (y * z)) : Divisible x y := by
  rcases h1 with ⟨hyz, c, hc⟩
  have hy : ¬ y ≈ zero := by
    intro heq
    apply hyz
    apply equivalent_of_toPeano_eq
    rw [multiply_toPeano, toPeano_eq_of_equivalent heq, toPeano_zero, Peano.zero_multiply]
  exact ⟨hy, z * c, by
    apply equivalent_of_toPeano_eq
    have hc' := toPeano_eq_of_equivalent hc
    rw [multiply_toPeano, multiply_toPeano] at hc' ⊢
    rw [← Peano.multiply_associative, hc']⟩

/-- Dividing by a product is equivalent to dividing by each factor in turn. -/
theorem divide_divide_eq_divide_multiply (x y z : Decimal) (h1 : Divisible x (y * z)) :
    ∃ h2 h3, divide x (y * z) h1 ≈ divide (divide x y h2) z h3 := by
  let h2 : Divisible x y := divide_divide_eq_divide_multiply_h2 h1
  let q : Decimal := divide x (y * z) h1
  let r : Decimal := divide x y h2
  have hz : ¬ z ≈ zero := by
    intro heq
    apply h1.1
    apply equivalent_of_toPeano_eq
    rw [multiply_toPeano, toPeano_eq_of_equivalent heq, toPeano_zero, Peano.multiply_zero]
  have hzq_eq_r : z * q ≈ r := by
    apply equivalent_of_toPeano_eq
    obtain ⟨hxyz_div, hxyz⟩ := divide_toPeano x (y * z) h1
    obtain ⟨hxy_div, hxy⟩ := divide_toPeano x y h2
    have hyzq_eq_yr :
        y.toPeano * (z * q).toPeano = y.toPeano * r.toPeano := by
      rw [multiply_toPeano, ← Peano.multiply_associative, ← multiply_toPeano, hxyz, hxy,
        Peano.multiply_divide x.toPeano (y * z).toPeano hxyz_div,
        Peano.multiply_divide x.toPeano y.toPeano hxy_div]
    exact Peano.multiply_left_cancel y.toPeano (z * q).toPeano r.toPeano
      (toPeano_ne_zero_of_not_equivalent_zero h2.1) hyzq_eq_yr
  let h3 : Divisible r z := ⟨hz, q, hzq_eq_r⟩
  refine ⟨h2, h3, ?_⟩
  apply equivalent_of_toPeano_eq
  obtain ⟨hrz_div, hdiv⟩ := divide_toPeano r z h3
  have hw := toPeano_eq_of_equivalent hzq_eq_r
  rw [multiply_toPeano] at hw
  exact Peano.multiply_left_cancel z.toPeano q.toPeano (divide r z h3).toPeano
    (toPeano_ne_zero_of_not_equivalent_zero hz)
    (by
      rw [hdiv, Peano.multiply_divide r.toPeano z.toPeano hrz_div]
      exact hw)

def Even (a : Decimal) : Prop := Divisible a two

def Odd (a : Decimal) : Prop := ¬ Even a

theorem evenToPeano (a : Decimal) : Even a ↔ Peano.Even a.toPeano := by
  unfold Even Peano.Even
  rw [divisibleToPeano, toPeano_two]

theorem oddToPeano (a : Decimal) : Odd a ↔ Peano.Odd a.toPeano := by
  unfold Odd Peano.Odd
  rw [evenToPeano]

def lastDigit (a : Decimal) : Digit :=
  Sequences.List.lastElement a.val a.property

def isEven (a : Decimal) : Bool :=
  Peano.isEven (lastDigit a).val

def isOdd (a : Decimal) : Bool := !isEven a

theorem even_toPeano_iff_lastDigit (a : Decimal) :
    Peano.Even a.toPeano ↔ Peano.Even (lastDigit a).val := by
  unfold toPeano lastDigit
  exact toCardinalNaturalPeano_even_iff_lastElement a.val a.property

theorem isEven_correct (x : Decimal) : Even x ↔ isEven x := by
  rw [evenToPeano, even_toPeano_iff_lastDigit]
  unfold isEven
  exact Peano.isEven_correct (lastDigit x).val

theorem isOdd_correct (x : Decimal) : Odd x ↔ isOdd x := by
  unfold Odd isOdd
  rw [isEven_correct]
  cases isEven x <;> simp

instance decidableEven (x : Decimal) : Decidable (Even x) :=
  decidable_of_iff' (isEven x) (isEven_correct x)

instance decidableOdd (x : Decimal) : Decidable (Odd x) :=
  decidable_of_iff' (isOdd x) (isOdd_correct x)

theorem even_succ {x : Decimal} (h : Even x) : Odd (successor x) := by
  rw [oddToPeano, successor_toPeano]
  exact Peano.isEven_successor x.toPeano ((evenToPeano x).mp h)

theorem odd_succ {x : Decimal} (h : Odd x) : Even (successor x) := by
  rw [evenToPeano, successor_toPeano]
  exact Peano.isEven_successor_of_isOdd x.toPeano ((oddToPeano x).mp h)

theorem even_pred {x : Decimal} (h : Even x) (h_ne : ¬ x ≈ zero) :
    Odd (predecessor x h_ne) := by
  rw [oddToPeano]
  obtain ⟨h2, hpred⟩ := predecessor_toPeano x h_ne
  rw [hpred]
  exact Peano.isOdd_predecessor x.toPeano h2 ((evenToPeano x).mp h)

theorem odd_pred {x : Decimal} (h_odd : Odd x) :
    ∃ h_ne, Even (predecessor x h_ne) := by
  have h_peano_odd := (oddToPeano x).mp h_odd
  obtain ⟨h_ne_peano, h_even_peano⟩ :=
    Peano.isEven_predecessor_of_isOdd x.toPeano h_peano_odd
  have h_ne : ¬ x ≈ zero := by
    intro heq
    exact h_ne_peano ((toPeano_eq_of_equivalent heq).trans toPeano_zero)
  refine ⟨h_ne, ?_⟩
  rw [evenToPeano]
  obtain ⟨h2, hpred⟩ := predecessor_toPeano x h_ne
  rw [hpred, Peano.predecessor_congr h2 h_ne_peano rfl]
  exact h_even_peano

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

/-- `fromOrdinal` of any positive ordinal Decimal is at least `one`. -/
theorem one_le_fromOrdinal (index : OrdinalNatural.Decimal) :
    one ≤ fromOrdinal index := by
  apply le_of_toPeano_le
  rw [toPeano_one, fromOrdinal_toPeano_eq_fromOrdinal_peano]
  exact Peano.one_le_fromOrdinal index.toPeano

/-- Peano form of the coefficient `fromOrdinal index - one`. -/
theorem subtract_fromOrdinal_one_toPeano (index : OrdinalNatural.Decimal) :
    (subtract (fromOrdinal index) one (one_le_fromOrdinal index)).toPeano =
      Peano.subtract (Peano.fromOrdinal index.toPeano) Peano.one
        (Peano.one_le_fromOrdinal index.toPeano) := by
  obtain ⟨hle, hsub⟩ :=
    subtract_toPeano (fromOrdinal index) one (one_le_fromOrdinal index)
  refine hsub.trans ?_
  exact Peano.subtract_eq_of_eq hle (Peano.one_le_fromOrdinal index.toPeano)
    (fromOrdinal_toPeano_eq_fromOrdinal_peano index) toPeano_one

/-- Away from `one`, `fromOrdinal index - one` equals `fromOrdinal` of the
ordinal predecessor. -/
theorem subtract_fromOrdinal_one_eq_fromOrdinal_predecessor
    (index : OrdinalNatural.Decimal)
    (h : ¬ index ≈ OrdinalNatural.Decimal.one) :
    (subtract (fromOrdinal index) one (one_le_fromOrdinal index)).toPeano =
      (fromOrdinal (index.predecessor h)).toPeano := by
  rw [subtract_fromOrdinal_one_toPeano, fromOrdinal_toPeano_eq_fromOrdinal_peano]
  have hsucc := OrdinalNatural.Decimal.toPeano_eq_succ_predecessor_toPeano index h
  rw [hsucc]
  change
      Peano.subtract
          (Peano.fromOrdinal (index.predecessor h).toPeano).successor Peano.one
          (Peano.one_le_fromOrdinal
            ((index.predecessor h).toPeano.successor)) =
        Peano.fromOrdinal (index.predecessor h).toPeano
  rw [Peano.subtract_successor_one]

/-- Advancing an ordinal Decimal index adds the corresponding `fromOrdinal` gap
to the Peano coefficient `fromOrdinal index - one`. -/
theorem subtract_fromOrdinal_one_add_of_lt
    (index index' : OrdinalNatural.Decimal) (hlt : index < index') :
    (subtract (fromOrdinal index') one (one_le_fromOrdinal index')).toPeano =
      (subtract (fromOrdinal index) one (one_le_fromOrdinal index)).toPeano +
        (fromOrdinal (OrdinalNatural.Decimal.subtract index' index hlt)).toPeano := by
  let gap := OrdinalNatural.Decimal.subtract index' index hlt
  obtain ⟨hlt_peano, hsub_peano⟩ :=
    OrdinalNatural.Decimal.subtract_toPeano index' index hlt
  have hsum : index'.toPeano = gap.toPeano + index.toPeano := by
    have hcancel :=
      OrdinalNatural.Peano.subtract_add_cancel index'.toPeano index.toPeano
        hlt_peano
    -- `subtract + index = index'`; rewrite the subtract term via `hsub_peano`.
    have hcancel' :
        (index'.subtract index hlt).toPeano + index.toPeano = index'.toPeano := by
      rw [hsub_peano]
      exact hcancel
    simpa [gap] using hcancel'.symm
  have hfrom :
      Peano.fromOrdinal index'.toPeano =
        Peano.fromOrdinal gap.toPeano + Peano.fromOrdinal index.toPeano := by
    rw [hsum, Peano.fromOrdinal_add]
  have hleft_peano := subtract_fromOrdinal_one_toPeano index'
  have hright_peano := subtract_fromOrdinal_one_toPeano index
  have hgap_peano := fromOrdinal_toPeano_eq_fromOrdinal_peano gap
  rw [hleft_peano, hright_peano, hgap_peano]
  -- Goal is now purely in `Peano.fromOrdinal` / `Peano.subtract`.
  obtain ⟨hle_sum, hassoc⟩ :=
    Peano.add_subtract_assoc (Peano.fromOrdinal gap.toPeano)
      (Peano.fromOrdinal index.toPeano) Peano.one
      (Peano.one_le_fromOrdinal index.toPeano)
  have hleft :
      Peano.subtract (Peano.fromOrdinal index'.toPeano) Peano.one
          (Peano.one_le_fromOrdinal index'.toPeano) =
        Peano.subtract
          (Peano.fromOrdinal gap.toPeano + Peano.fromOrdinal index.toPeano)
          Peano.one hle_sum :=
    Peano.subtract_eq_of_eq _ hle_sum hfrom rfl
  exact
    (hleft.trans hassoc).trans
      (Peano.add_commutative
        (Peano.fromOrdinal gap.toPeano)
        (Peano.subtract (Peano.fromOrdinal index.toPeano) Peano.one
          (Peano.one_le_fromOrdinal index.toPeano)))

/-- Anything ≤ zero is equivalent to zero. -/
theorem eq_zero_of_le_zero (a : Decimal) (h : a ≤ zero) : a ≈ zero := by
  cases h with
  | inl hlt =>
    exact (Peano.not_lt_zero a.toPeano hlt).elim
  | inr heq =>
    exact heq

end Decimal

end ZeroMath.Numbers.CardinalNatural
