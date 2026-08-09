import ZeroMath.Numbers.Digits.Decimal
import ZeroMath.Sequences.List

namespace ZeroMath.Numbers.Digits

/-- Increment a digit list from the least-significant end; `true` means a new leading `1` is needed. -/
def successorList (a : Sequences.List Decimal) :
    Sequences.List Decimal × Bool :=
  match a with
  | .empty => ⟨Sequences.List.empty, true⟩
  | .firstElement d ds =>
    let ⟨digits, carry⟩ := successorList ds
    if carry then
      if h3 : CardinalNatural.Peano.isLessThan d.val.successor CardinalNatural.Peano.ten then
        ⟨Sequences.List.firstElement
          ⟨d.val.successor, (CardinalNatural.Peano.isLessThan_eq_true_iff_lt _ _).mp h3⟩
          digits, false⟩
      else
        ⟨Sequences.List.firstElement
          ⟨CardinalNatural.Peano.zero, CardinalNatural.Peano.zero_lt_succ CardinalNatural.Peano.nine⟩
          digits, true⟩
    else
      ⟨Sequences.List.firstElement d digits, false⟩

/-- Decrement a digit list from the least-significant end; `true` means the input was all zeros. -/
def predecessorList (a : Sequences.List Decimal) :
    Sequences.List Decimal × Bool :=
  match a with
  | .empty => ⟨Sequences.List.empty, true⟩
  | .firstElement d ds =>
    let ⟨digits, borrow⟩ := predecessorList ds
    if borrow then
      match d with
      | ⟨.zero, _⟩ =>
        ⟨Sequences.List.firstElement ⟨CardinalNatural.Peano.nine, CardinalNatural.Peano.LessThan.base⟩
          digits, true⟩
      | ⟨.successor d', h⟩ =>
        ⟨Sequences.List.firstElement ⟨d', CardinalNatural.Peano.lt_of_succ_lt h⟩ digits, false⟩
    else
      ⟨Sequences.List.firstElement d digits, false⟩

/-- Columnar subtraction of equal-length digit lists (least-significant digit recursion).
    The boolean is the final borrow out of the most-significant column. -/
def subtractAlignedLists (a b : Sequences.List Decimal) (h : Sequences.List.SameLength a b) :
    Sequences.List Decimal × Bool :=
  match a, b with
  | .empty, .empty => ⟨Sequences.List.empty, false⟩
  | .firstElement da das, .firstElement db dbs =>
    let ⟨digits, borrow⟩ :=
      subtractAlignedLists das dbs (Sequences.List.sameLength_of_firstElement h)
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
        ⟨CardinalNatural.Peano.subtract (da.val + CardinalNatural.Peano.ten) withBorrow h_le,
          h_digit⟩
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

/-- Prop-level MSD-first comparison of equal-length digit lists. -/
def LessThanAlignedLists (x y : Sequences.List Decimal)
  (h : Sequences.List.SameLength x y) : Prop :=
  match x, y with
  | .empty, .empty => False
  | .firstElement d1 ds1, .firstElement d2 ds2 =>
      d1.val < d2.val ∨
        (d1.val = d2.val ∧ LessThanAlignedLists ds1 ds2 (Sequences.List.sameLength_of_firstElement h))
  | .empty, .firstElement _ _ => False.elim (by cases h)
  | .firstElement _ _, .empty => False.elim (by cases h)

/-- Boolean MSD-first comparison of equal-length digit lists. -/
def isLessThanAlignedLists (x y : Sequences.List Decimal)
  (h : Sequences.List.SameLength x y) : Bool :=
  match x, y with
  | .empty, .empty => false
  | .firstElement dx dxs, .firstElement dy dys =>
      if _ : CardinalNatural.Peano.isLessThan dx.val dy.val then
        true
      else if _ : CardinalNatural.Peano.isLessThan dy.val dx.val then
        false
      else
        isLessThanAlignedLists dxs dys (Sequences.List.sameLength_of_firstElement h)
  | .empty, .firstElement _ _ => False.elim (by cases h)
  | .firstElement _ _, .empty => False.elim (by cases h)

theorem isLessThanAlignedLists_iff_lessThanAlignedLists (x y : Sequences.List Decimal)
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

theorem LessThanAlignedLists_congr {a b c d : Sequences.List Decimal}
  (h₁ : Sequences.List.SameLength a b) (h₂ : Sequences.List.SameLength c d)
  (ha : a = c) (hb : b = d) :
  LessThanAlignedLists a b h₁ → LessThanAlignedLists c d h₂ := by
  subst c
  subst d
  intro h
  exact h

/-- Columnar addition of equal-length digit lists (least-significant digit recursion).
    The boolean is the final carry out of the most-significant column. -/
def addAlignedLists (a b : Sequences.List Decimal) (h : Sequences.List.SameLength a b) :
  Sequences.List Decimal × Bool :=
  match a, b with
  | .empty, .empty => ⟨Sequences.List.empty, false⟩
  | .firstElement da das, .firstElement db dbs =>
    let ⟨digits, carry⟩ := addAlignedLists das dbs (Sequences.List.sameLength_of_firstElement h)
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

theorem addAlignedLists_commutative (a b : Sequences.List Decimal)
  (h : Sequences.List.SameLength a b) :
  addAlignedLists a b h = addAlignedLists b a (Sequences.List.sameLength_commutative h) := by
  induction h using Sequences.List.SameLength.induction with
  | empty => rfl
  | firstElement htail ih =>
      unfold addAlignedLists
      rw [ih]
      simp only [CardinalNatural.Peano.add_commutative]

def HasNonZero := Sequences.List.AnyElement DigitIsNonZero

theorem hasNonZero_ne_empty {l : Sequences.List Decimal} (h : HasNonZero l) :
    l ≠ Sequences.List.empty := by
  intro h_empty
  cases h with
  | first _ _ _ => cases h_empty
  | notFirst _ _ _ => cases h_empty

def hasNonZero (a : Sequences.List Decimal) : Bool :=
  Sequences.List.anyElement DigitIsNonZero a

theorem hasNonZero_tail_of_zero_first {d : Decimal} {ds : Sequences.List Decimal}
    (h : HasNonZero (Sequences.List.firstElement d ds))
    (hd : d.val = CardinalNatural.Peano.zero) : HasNonZero ds := by
  cases h with
  | first _ _ hd_nonzero =>
      exact False.elim (hd_nonzero hd)
  | notFirst _ _ hds =>
      exact hds

/-- A digit list that contains at least one non-zero digit. -/
def NonZeroList := { l : Sequences.List Decimal // HasNonZero l }

/-- A non-empty digit list (may be all zeros). -/
def NonEmptyList := { l : Sequences.List Decimal // l ≠ Sequences.List.empty }

/-- Interpret a digit list as a cardinal Peano natural (most-significant digit first). -/
def toCardinalNaturalPeano (a : Sequences.List Decimal) (acc : CardinalNatural.Peano) :
    CardinalNatural.Peano :=
  match a with
  | .empty => acc
  | .firstElement d ds =>
      toCardinalNaturalPeano ds (acc * CardinalNatural.Peano.ten + d.val)

def AllZero : Sequences.List Decimal → Prop
  | .empty => True
  | .firstElement d ds => d.val = CardinalNatural.Peano.zero ∧ AllZero ds

instance decidableAllZero : (a : Sequences.List Decimal) → Decidable (AllZero a)
  | .empty => inferInstanceAs (Decidable True)
  | .firstElement d ds =>
      match decidableAllZero ds, decEq d.val CardinalNatural.Peano.zero with
      | isTrue hds, isTrue hd => isTrue ⟨hd, hds⟩
      | isFalse hds, _ => isFalse (fun h => hds h.2)
      | _, isFalse hd => isFalse (fun h => hd h.1)

/-- Strip leading zeros from a non-empty digit list. All-zero yields a single zero digit. -/
def normalizeList (a : Sequences.List Decimal) (ha : a ≠ Sequences.List.empty) : NonEmptyList :=
  match a with
  | .empty => False.elim (ha rfl)
  | .firstElement d ds =>
      if hd : d.val = CardinalNatural.Peano.zero then
        if hds : ds = Sequences.List.empty then
          ⟨Sequences.List.firstElement d ds, by simp⟩
        else
          normalizeList ds hds
      else
        ⟨Sequences.List.firstElement d ds, by simp⟩

theorem normalizeList_eq_zero_of_allZero {a : Sequences.List Decimal}
    (ha : a ≠ Sequences.List.empty) (h : AllZero a) :
    normalizeList a ha =
      ⟨Sequences.List.firstElement zeroDigit Sequences.List.empty, by simp⟩ := by
  induction a with
  | empty =>
      exact False.elim (ha rfl)
  | firstElement d ds ih =>
      unfold normalizeList
      have hd : d.val = CardinalNatural.Peano.zero := h.1
      rw [dif_pos hd]
      split
      · next heq =>
          apply Subtype.ext
          simp [heq, zeroDigit]
          exact Subtype.ext hd
      · next hne =>
          exact ih hne h.2

theorem hasNonZero_normalizeList {a : Sequences.List Decimal} (h : HasNonZero a) :
    HasNonZero (normalizeList a (hasNonZero_ne_empty h)).val := by
  induction a with
  | empty =>
      exact False.elim (hasNonZero_ne_empty h rfl)
  | firstElement d ds ih =>
      unfold normalizeList
      split
      · next hd =>
          split
          · next heq =>
              cases h with
              | first _ _ hd_nonzero => exact False.elim (hd_nonzero hd)
              | notFirst _ _ hds =>
                  rw [heq] at hds
                  cases hds
          · next hne =>
              exact ih (hasNonZero_tail_of_zero_first h hd)
      · exact h

theorem successorList_ne_empty_of_carry_false {a digits : Sequences.List Decimal}
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

theorem predecessorList_ne_empty_of_borrow_false {a digits : Sequences.List Decimal}
    (ha : a ≠ Sequences.List.empty) (h : predecessorList a = ⟨digits, false⟩) :
    digits ≠ Sequences.List.empty := by
  induction a generalizing digits with
  | empty =>
      exact False.elim (ha rfl)
  | firstElement d ds _ =>
      unfold predecessorList at h
      dsimp at h
      split at h
      · split at h
        · cases h
        · cases h
          intro h_empty
          cases h_empty
      · cases h
        intro h_empty
        cases h_empty

theorem allZero_of_predecessorList_borrow_true {a digits : Sequences.List Decimal}
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

theorem successorList_predecessorList (a : Sequences.List Decimal) :
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
                  · have h_not_lt :=
                      CardinalNatural.Peano.not_lt_self CardinalNatural.Peano.ten
                    simp_all [successorList, CardinalNatural.Peano.ten,
                      CardinalNatural.Peano.isLessThan_eq_true_iff_lt]
                  · simp_all [successorList,
                      CardinalNatural.Peano.isLessThan_eq_true_iff_lt]

end ZeroMath.Numbers.Digits
