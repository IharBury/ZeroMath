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

/-- Add a digit into a list from the least-significant end, returning `(digits, carryDigit)`. -/
def addPartialListDigit (a : Sequences.List Decimal) (b : Decimal) : Sequences.List Decimal × Decimal :=
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

/-- Add a single digit into a digit list, discarding a final zero carry. -/
def addListDigit (a : Sequences.List Decimal) (b : Decimal) : Sequences.List Decimal :=
  let (ds, carry) := addPartialListDigit a b
  if carry.val = .zero then ds else .firstElement carry ds

/-- Multiply a digit by a cardinal Peano natural, producing a short digit list. -/
def multiplyDigitsPeano (a : Decimal) (b : CardinalNatural.Peano) : Sequences.List Decimal :=
  match b with
  | CardinalNatural.Peano.zero => .firstElement zeroDigit .empty
  | CardinalNatural.Peano.successor b' =>
    let prev := multiplyDigitsPeano a b'
    addListDigit prev a

/-- Multiply two digits, producing a one- or two-digit list. -/
def multiplyDigits (a b : Decimal) : Sequences.List Decimal :=
  multiplyDigitsPeano a b.val

theorem addListDigit_multiplyDigits_ne_empty (d b carry : Decimal) :
  addListDigit (multiplyDigits d b) carry ≠ Sequences.List.empty := by
  rcases digit_cases d with hd | hd | hd | hd | hd | hd | hd | hd | hd | hd <;>
    subst d <;>
    rcases digit_cases b with hb | hb | hb | hb | hb | hb | hb | hb | hb | hb <;>
    subst b <;>
    rcases digit_cases carry with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc <;>
    subst carry <;>
    decide

theorem addListDigit_multiplyDigits_not_three_or_more
  (d b carry x y z : Decimal) (zs : Sequences.List Decimal) :
  addListDigit (multiplyDigits d b) carry ≠
    Sequences.List.firstElement x (Sequences.List.firstElement y (Sequences.List.firstElement z zs)) := by
  rcases digit_cases d with hd | hd | hd | hd | hd | hd | hd | hd | hd | hd <;>
    subst d <;>
    rcases digit_cases b with hb | hb | hb | hb | hb | hb | hb | hb | hb | hb <;>
    subst b <;>
    rcases digit_cases carry with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc <;>
    subst carry <;>
    intro h <;> cases h

/-- Multiply a digit list by a digit with incoming carry, returning `(digits, carryDigit)`. -/
def multiplyPartialListByDigit (a : Sequences.List Decimal) (b : Decimal) : Sequences.List Decimal × Decimal :=
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

/-- Multiply a digit list by a single digit. -/
def multiplyListByDigit (a : Sequences.List Decimal) (b : Decimal) : Sequences.List Decimal :=
  let (ds, carry) := multiplyPartialListByDigit a b
  if carry.val = .zero then ds else .firstElement carry ds

/-- Schoolbook multiplication of digit lists; the `Peano` component is the next shift amount. -/
def multiplyList (a b : Sequences.List Decimal) : Sequences.List Decimal × CardinalNatural.Peano :=
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

-- toCardinalNaturalPeano l acc = acc * 10^len(l) + toCardinalNaturalPeano l 0
theorem toCardinalNaturalPeano_acc_split (l : Sequences.List Decimal)
    (acc : CardinalNatural.Peano) :
    toCardinalNaturalPeano l acc =
      acc * CardinalNatural.Peano.tenPow l.length + toCardinalNaturalPeano l CardinalNatural.Peano.zero := by
  induction l generalizing acc with
  | empty =>
    simp only [toCardinalNaturalPeano, Sequences.List.length, CardinalNatural.Peano.tenPow,
               CardinalNatural.Peano.multiply_one, CardinalNatural.Peano.add_zero]
  | firstElement d ds ih =>
    simp only [toCardinalNaturalPeano, Sequences.List.length,
               CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.zero_add]
    rw [ih (acc * CardinalNatural.Peano.ten + d.val), ih d.val, CardinalNatural.Peano.tenPow_add_one,
        CardinalNatural.Peano.multiply_distributive_over_add_left,
        CardinalNatural.Peano.multiply_associative,
        CardinalNatural.Peano.add_associative]

theorem toCardinalNaturalPeano_firstElement (d : Decimal) (ds : Sequences.List Decimal) :
  toCardinalNaturalPeano (Sequences.List.firstElement d ds) CardinalNatural.Peano.zero =
    d.val * CardinalNatural.Peano.tenPow ds.length +
      toCardinalNaturalPeano ds CardinalNatural.Peano.zero := by
  change toCardinalNaturalPeano ds (CardinalNatural.Peano.zero * CardinalNatural.Peano.ten + d.val) = _
  rw [CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.zero_add]
  exact toCardinalNaturalPeano_acc_split ds d.val

theorem toCardinalNaturalPeano_padAtStart_zeroDigit (l : Sequences.List Decimal)
  (n : CardinalNatural.Peano) :
  toCardinalNaturalPeano (Sequences.List.padAtStart l zeroDigit n) CardinalNatural.Peano.zero =
    toCardinalNaturalPeano l CardinalNatural.Peano.zero := by
  induction n generalizing l with
  | zero => rfl
  | successor n ih =>
      unfold Sequences.List.padAtStart
      rw [ih]
      rfl

theorem toCardinalNaturalPeano_padAtStartToSameLength_fst (a b : Sequences.List Decimal) :
  toCardinalNaturalPeano (Sequences.List.padAtStartToSameLength a b zeroDigit).1
      CardinalNatural.Peano.zero =
    toCardinalNaturalPeano a CardinalNatural.Peano.zero := by
  unfold Sequences.List.padAtStartToSameLength
  dsimp only
  split
  · rfl
  · exact toCardinalNaturalPeano_padAtStart_zeroDigit _ _

theorem toCardinalNaturalPeano_padAtStartToSameLength_snd (a b : Sequences.List Decimal) :
  toCardinalNaturalPeano (Sequences.List.padAtStartToSameLength a b zeroDigit).2
      CardinalNatural.Peano.zero =
    toCardinalNaturalPeano b CardinalNatural.Peano.zero := by
  unfold Sequences.List.padAtStartToSameLength
  dsimp only
  split
  · exact toCardinalNaturalPeano_padAtStart_zeroDigit _ _
  · rfl

-- toCardinalNaturalPeano l 0 < 10^len(l)
theorem toCardinalNaturalPeano_lt_tenPow (l : Sequences.List Decimal) :
    toCardinalNaturalPeano l CardinalNatural.Peano.zero < CardinalNatural.Peano.tenPow l.length := by
  induction l with
  | empty =>
    simp only [toCardinalNaturalPeano, Sequences.List.length, CardinalNatural.Peano.tenPow]
    exact CardinalNatural.Peano.LessThan.base
  | firstElement d ds ih =>
    simp only [toCardinalNaturalPeano, Sequences.List.length,
               CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.zero_add]
    rw [toCardinalNaturalPeano_acc_split ds d.val, CardinalNatural.Peano.tenPow_add_one]
    have h1 : d.val * CardinalNatural.Peano.tenPow ds.length + toCardinalNaturalPeano ds CardinalNatural.Peano.zero <
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

theorem LessThanAlignedLists_toCardinalNaturalPeano_lt {x y : Sequences.List Decimal}
    (h : Sequences.List.SameLength x y)
    (hlt : LessThanAlignedLists x y h) :
    toCardinalNaturalPeano x CardinalNatural.Peano.zero <
      toCardinalNaturalPeano y CardinalNatural.Peano.zero := by
  induction h using Sequences.List.SameLength.induction with
  | empty =>
      cases hlt
  | firstElement htail ih =>
      rename_i dx dy dxs dys
      simp only [toCardinalNaturalPeano_firstElement]
      cases hlt with
      | inl h_digit =>
          have h_tail_lt : toCardinalNaturalPeano dxs CardinalNatural.Peano.zero <
              CardinalNatural.Peano.tenPow dxs.length :=
            toCardinalNaturalPeano_lt_tenPow dxs
          have h_lt_next :
              dx.val * CardinalNatural.Peano.tenPow dxs.length +
                toCardinalNaturalPeano dxs CardinalNatural.Peano.zero <
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
                  toCardinalNaturalPeano dys CardinalNatural.Peano.zero :=
            CardinalNatural.Peano.le_add_self_left _ _
          rw [← htail]
          exact CardinalNatural.Peano.lt_of_lt_of_le h_lt_next
            (CardinalNatural.Peano.le_trans h_le_digit h_le_value)
      | inr h_eq_tail =>
          obtain ⟨h_digit_eq, h_tail_lt_aligned⟩ := h_eq_tail
          rw [h_digit_eq, htail]
          exact CardinalNatural.Peano.add_lt_add_left
            (ih h_tail_lt_aligned) _

theorem LessThanAlignedLists_of_toCardinalNaturalPeano_lt {x y : Sequences.List Decimal}
    (h : Sequences.List.SameLength x y)
    (hlt : toCardinalNaturalPeano x CardinalNatural.Peano.zero <
      toCardinalNaturalPeano y CardinalNatural.Peano.zero) :
    LessThanAlignedLists x y h := by
  induction h using Sequences.List.SameLength.induction with
  | empty =>
      exact False.elim (CardinalNatural.Peano.not_lt_self _ hlt)
  | firstElement htail ih =>
      rename_i dx dy dxs dys
      simp only [toCardinalNaturalPeano_firstElement] at hlt
      rw [htail] at hlt
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
                      toCardinalNaturalPeano dxs CardinalNatural.Peano.zero <
                    dy.val * CardinalNatural.Peano.tenPow dys.length +
                      toCardinalNaturalPeano dys CardinalNatural.Peano.zero := by
                  rwa [h_digit_eq] at hlt
                rw [CardinalNatural.Peano.add_commutative
                      (dy.val * CardinalNatural.Peano.tenPow dys.length),
                    CardinalNatural.Peano.add_commutative
                      (dy.val * CardinalNatural.Peano.tenPow dys.length)] at hlt_tail_sum
                exact CardinalNatural.Peano.add_lt_cancel_right hlt_tail_sum
          | inr h_digit_gt =>
              have h_tail_y_lt : toCardinalNaturalPeano dys CardinalNatural.Peano.zero <
                  CardinalNatural.Peano.tenPow dys.length :=
                toCardinalNaturalPeano_lt_tenPow dys
              have h_y_lt_next :
                  dy.val * CardinalNatural.Peano.tenPow dys.length +
                    toCardinalNaturalPeano dys CardinalNatural.Peano.zero <
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
                      toCardinalNaturalPeano dxs CardinalNatural.Peano.zero :=
                CardinalNatural.Peano.le_add_self_left _ _
              have h_y_lt_x :
                  dy.val * CardinalNatural.Peano.tenPow dys.length +
                    toCardinalNaturalPeano dys CardinalNatural.Peano.zero <
                  dx.val * CardinalNatural.Peano.tenPow dys.length +
                    toCardinalNaturalPeano dxs CardinalNatural.Peano.zero :=
                CardinalNatural.Peano.lt_of_lt_of_le h_y_lt_next
                  (CardinalNatural.Peano.le_trans h_le_digit h_le_x)
              exact False.elim (CardinalNatural.Peano.not_lt_self _
                (CardinalNatural.Peano.lt_trans hlt h_y_lt_x))

theorem addPartialListDigit_spec (a : Sequences.List Decimal) (b : Decimal) :
    (addPartialListDigit a b).1.length = a.length ∧
    toCardinalNaturalPeano (addPartialListDigit a b).1 CardinalNatural.Peano.zero +
        (addPartialListDigit a b).2.val * CardinalNatural.Peano.tenPow a.length =
      toCardinalNaturalPeano a CardinalNatural.Peano.zero + b.val := by
  induction a with
  | empty =>
      simp [addPartialListDigit, toCardinalNaturalPeano, Sequences.List.length,
        CardinalNatural.Peano.tenPow]
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
            · simp only [toCardinalNaturalPeano_firstElement, Sequences.List.length, zeroDigit,
                CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.add_zero]
              rw [h_length]
              calc
                _ = d.val * CardinalNatural.Peano.tenPow ds.length +
                      (carry.val * CardinalNatural.Peano.tenPow ds.length +
                        toCardinalNaturalPeano digits CardinalNatural.Peano.zero) := by
                      rw [CardinalNatural.Peano.multiply_distributive_over_add_left]
                      simp only [CardinalNatural.Peano.add_associative]
                _ = d.val * CardinalNatural.Peano.tenPow ds.length +
                      (toCardinalNaturalPeano digits CardinalNatural.Peano.zero +
                        carry.val * CardinalNatural.Peano.tenPow ds.length) := by
                      rw [CardinalNatural.Peano.add_commutative
                        (carry.val * CardinalNatural.Peano.tenPow ds.length)
                        (toCardinalNaturalPeano digits CardinalNatural.Peano.zero)]
                _ = d.val * CardinalNatural.Peano.tenPow ds.length +
                      (toCardinalNaturalPeano ds CardinalNatural.Peano.zero + b.val) := by
                      rw [ih_value]
                _ = d.val * CardinalNatural.Peano.tenPow ds.length +
                      toCardinalNaturalPeano ds CardinalNatural.Peano.zero + b.val := by
                      rw [CardinalNatural.Peano.add_associative]
          · next h_not_lt =>
            constructor
            · simp [Sequences.List.length, h_length]
            · simp only [toCardinalNaturalPeano_firstElement, Sequences.List.length, oneDigit,
                CardinalNatural.Peano.one_multiply, CardinalNatural.Peano.tenPow_add_one]
              rw [h_length]
              have h_false : (d.val + carry.val).isLessThan CardinalNatural.Peano.ten = false :=
                (CardinalNatural.Peano.isLessThan_eq_false_iff_not_lt _ _).mpr h_not_lt
              have h_le : CardinalNatural.Peano.ten ≤ d.val + carry.val :=
                CardinalNatural.Peano.isLessThan_false_implies_le h_false
              have h_digit := CardinalNatural.Peano.subtract_add_cancel
                (d.val + carry.val) CardinalNatural.Peano.ten h_le
              calc
                _ = (CardinalNatural.Peano.subtract (d.val + carry.val)
                          CardinalNatural.Peano.ten h_le + CardinalNatural.Peano.ten) *
                        CardinalNatural.Peano.tenPow ds.length +
                      toCardinalNaturalPeano digits CardinalNatural.Peano.zero := by
                      rw [CardinalNatural.Peano.multiply_distributive_over_add_left]
                      exact CardinalNatural.Peano.add_right_commutative _ _ _
                _ = (d.val + carry.val) * CardinalNatural.Peano.tenPow ds.length +
                      toCardinalNaturalPeano digits CardinalNatural.Peano.zero := by
                      rw [h_digit]
                _ = d.val * CardinalNatural.Peano.tenPow ds.length +
                      (carry.val * CardinalNatural.Peano.tenPow ds.length +
                        toCardinalNaturalPeano digits CardinalNatural.Peano.zero) := by
                      rw [CardinalNatural.Peano.multiply_distributive_over_add_left]
                      rw [CardinalNatural.Peano.add_associative]
                _ = d.val * CardinalNatural.Peano.tenPow ds.length +
                      (toCardinalNaturalPeano digits CardinalNatural.Peano.zero +
                        carry.val * CardinalNatural.Peano.tenPow ds.length) := by
                      rw [CardinalNatural.Peano.add_commutative
                        (carry.val * CardinalNatural.Peano.tenPow ds.length)
                        (toCardinalNaturalPeano digits CardinalNatural.Peano.zero)]
                _ = d.val * CardinalNatural.Peano.tenPow ds.length +
                      (toCardinalNaturalPeano ds CardinalNatural.Peano.zero + b.val) := by
                      rw [ih_value]
                _ = d.val * CardinalNatural.Peano.tenPow ds.length +
                      toCardinalNaturalPeano ds CardinalNatural.Peano.zero + b.val := by
                      rw [CardinalNatural.Peano.add_associative]

theorem addAlignedLists_spec {a b : Sequences.List Decimal}
  (h : Sequences.List.SameLength a b) :
  let result := addAlignedLists a b h
  result.1.length = a.length ∧
    toCardinalNaturalPeano result.1 CardinalNatural.Peano.zero +
        (if result.2 then CardinalNatural.Peano.tenPow a.length else CardinalNatural.Peano.zero) =
      toCardinalNaturalPeano a CardinalNatural.Peano.zero +
        toCardinalNaturalPeano b CardinalNatural.Peano.zero := by
  induction h using Sequences.List.SameLength.induction with
  | empty =>
      simp [addAlignedLists, toCardinalNaturalPeano, Sequences.List.length]
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
                · simp only [toCardinalNaturalPeano_firstElement]
                  simp only [if_neg Bool.false_ne_true]
                  rw [h_length, ← h_tail_lengths]
                  rw [CardinalNatural.Peano.multiply_distributive_over_add_left, ih_value]
                  simp
                  simp only [CardinalNatural.Peano.add_associative, CardinalNatural.Peano.add_left_commutative]
              · constructor
                · simp [Sequences.List.length, h_length]
                · simp only [toCardinalNaturalPeano_firstElement, Sequences.List.length,
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
                        toCardinalNaturalPeano digits CardinalNatural.Peano.zero := by
                          rw [CardinalNatural.Peano.multiply_distributive_over_add_left]
                          rw [CardinalNatural.Peano.add_associative,
                            CardinalNatural.Peano.add_commutative
                              (toCardinalNaturalPeano digits CardinalNatural.Peano.zero)
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
                · simp only [toCardinalNaturalPeano_firstElement]
                  simp only [if_neg Bool.false_ne_true]
                  rw [h_length, ← h_tail_lengths]
                  rw [CardinalNatural.Peano.multiply_distributive_over_add_left]
                  rw [CardinalNatural.Peano.multiply_distributive_over_add_left]
                  rw [CardinalNatural.Peano.one_multiply]
                  calc
                    _ = da.val * CardinalNatural.Peano.tenPow das.length +
                          db.val * CardinalNatural.Peano.tenPow das.length +
                          (toCardinalNaturalPeano digits CardinalNatural.Peano.zero +
                            CardinalNatural.Peano.tenPow das.length) := by
                              simp
                              simp only [CardinalNatural.Peano.add_associative,
                                CardinalNatural.Peano.add_commutative]
                    _ = _ := by rw [ih_value]; simp only [CardinalNatural.Peano.add_associative,
                      CardinalNatural.Peano.add_left_commutative]
              · constructor
                · simp [Sequences.List.length, h_length]
                · simp only [toCardinalNaturalPeano_firstElement, Sequences.List.length,
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
                        toCardinalNaturalPeano digits CardinalNatural.Peano.zero := by
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
                              (toCardinalNaturalPeano digits CardinalNatural.Peano.zero +
                                CardinalNatural.Peano.tenPow das.length) := by simp only [
                                  CardinalNatural.Peano.add_associative,
                                  CardinalNatural.Peano.add_commutative]
                        _ = _ := by rw [ih_value]; simp only [CardinalNatural.Peano.add_associative,
                          CardinalNatural.Peano.add_left_commutative]

-- Key injectivity lemma: same-length lists with same toCardinalNaturalPeano value are equal
theorem toCardinalNaturalPeano_inj_sameLength {l1 l2 : Sequences.List Decimal}
    (hsl : Sequences.List.SameLength l1 l2)
    (heq : toCardinalNaturalPeano l1 CardinalNatural.Peano.zero =
           toCardinalNaturalPeano l2 CardinalNatural.Peano.zero) :
    l1 = l2 := by
  induction hsl using Sequences.List.SameLength.induction with
  | empty => rfl
  | firstElement h_tail ih =>
    rename_i d1 d2 ds1 ds2
    simp only [toCardinalNaturalPeano,
               CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.zero_add] at heq
    rw [toCardinalNaturalPeano_acc_split ds1 d1.val,
        toCardinalNaturalPeano_acc_split ds2 d2.val] at heq
    have h_len : ds2.length = ds1.length := h_tail.symm
    rw [h_len] at heq
    have hv1_lt : toCardinalNaturalPeano ds1 CardinalNatural.Peano.zero < CardinalNatural.Peano.tenPow ds1.length :=
      toCardinalNaturalPeano_lt_tenPow ds1
    have hv2_lt : toCardinalNaturalPeano ds2 CardinalNatural.Peano.zero < CardinalNatural.Peano.tenPow ds1.length := by
      rw [← h_len]; exact toCardinalNaturalPeano_lt_tenPow ds2
    have hd_eq : d1.val = d2.val := by
      cases CardinalNatural.Peano.trichotomy_or d1.val d2.val with
      | inl hlt =>
        exfalso
        have hchain : d1.val * CardinalNatural.Peano.tenPow ds1.length + CardinalNatural.Peano.tenPow ds1.length ≤
                      d1.val * CardinalNatural.Peano.tenPow ds1.length + toCardinalNaturalPeano ds1 CardinalNatural.Peano.zero := by
          have hstep1 : d1.val * CardinalNatural.Peano.tenPow ds1.length + CardinalNatural.Peano.tenPow ds1.length =
                        d1.val.successor * CardinalNatural.Peano.tenPow ds1.length :=
            (CardinalNatural.Peano.successor_multiply d1.val (CardinalNatural.Peano.tenPow ds1.length)).symm
          have hstep2 : d1.val.successor * CardinalNatural.Peano.tenPow ds1.length ≤ d2.val * CardinalNatural.Peano.tenPow ds1.length :=
            CardinalNatural.Peano.multiply_le_mul_left (CardinalNatural.Peano.succ_le_of_lt hlt) (CardinalNatural.Peano.tenPow ds1.length)
          have hstep3 : d2.val * CardinalNatural.Peano.tenPow ds1.length ≤
                        d2.val * CardinalNatural.Peano.tenPow ds1.length + toCardinalNaturalPeano ds2 CardinalNatural.Peano.zero :=
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
                        d2.val * CardinalNatural.Peano.tenPow ds1.length + toCardinalNaturalPeano ds2 CardinalNatural.Peano.zero := by
            have hstep1 : d2.val * CardinalNatural.Peano.tenPow ds1.length + CardinalNatural.Peano.tenPow ds1.length =
                          d2.val.successor * CardinalNatural.Peano.tenPow ds1.length :=
              (CardinalNatural.Peano.successor_multiply d2.val (CardinalNatural.Peano.tenPow ds1.length)).symm
            have hstep2 : d2.val.successor * CardinalNatural.Peano.tenPow ds1.length ≤ d1.val * CardinalNatural.Peano.tenPow ds1.length :=
              CardinalNatural.Peano.multiply_le_mul_left (CardinalNatural.Peano.succ_le_of_lt hgt) (CardinalNatural.Peano.tenPow ds1.length)
            have hstep3 : d1.val * CardinalNatural.Peano.tenPow ds1.length ≤
                          d1.val * CardinalNatural.Peano.tenPow ds1.length + toCardinalNaturalPeano ds1 CardinalNatural.Peano.zero :=
              CardinalNatural.Peano.le_add_self_left _ _
            rw [hstep1]
            exact CardinalNatural.Peano.le_trans (CardinalNatural.Peano.le_trans hstep2 hstep3)
              (Or.inr heq)
          exact absurd (CardinalNatural.Peano.le_lt_trans (CardinalNatural.Peano.add_le_cancel_left hchain) hv2_lt)
            (CardinalNatural.Peano.not_lt_self (CardinalNatural.Peano.tenPow ds1.length))
    have hv_eq : toCardinalNaturalPeano ds1 CardinalNatural.Peano.zero =
                 toCardinalNaturalPeano ds2 CardinalNatural.Peano.zero := by
      have heq' := heq
      rw [hd_eq] at heq'
      exact CardinalNatural.Peano.add_left_cancel _ _ _ heq'
    rw [Subtype.ext hd_eq, ih hv_eq]

theorem toCardinalNaturalPeano_padAtEnd (l : Sequences.List Decimal) (n : CardinalNatural.Peano) :
    toCardinalNaturalPeano (Sequences.List.padAtEnd l zeroDigit n) CardinalNatural.Peano.zero =
      toCardinalNaturalPeano l CardinalNatural.Peano.zero * CardinalNatural.Peano.tenPow n := by
  induction l with
  | empty =>
    induction n with
    | zero =>
      simp [Sequences.List.padAtEnd, toCardinalNaturalPeano, CardinalNatural.Peano.tenPow,
            CardinalNatural.Peano.multiply_one]
    | successor n ih =>
      simp [Sequences.List.padAtEnd, toCardinalNaturalPeano_firstElement, toCardinalNaturalPeano]
      show CardinalNatural.Peano.zero * _ + _ = _
      simp only [CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.zero_add]
      rw [ih]
      simp [toCardinalNaturalPeano, CardinalNatural.Peano.zero_multiply]
  | firstElement d ds ih =>
    simp only [Sequences.List.padAtEnd, toCardinalNaturalPeano_firstElement, Sequences.List.padAtEnd_length]
    rw [CardinalNatural.Peano.tenPow_add, ← CardinalNatural.Peano.multiply_associative, ih,
        ← CardinalNatural.Peano.multiply_distributive_over_add_left, ← toCardinalNaturalPeano_firstElement]

theorem toCardinalNaturalPeano_addListDigit (a : Sequences.List Decimal) (b : Decimal) :
    toCardinalNaturalPeano (addListDigit a b) CardinalNatural.Peano.zero =
      toCardinalNaturalPeano a CardinalNatural.Peano.zero + b.val := by
  obtain ⟨h_len, h_val⟩ := addPartialListDigit_spec a b
  cases h_rec : addPartialListDigit a b with
  | mk ds carry =>
    rw [h_rec] at h_len h_val; dsimp only at h_len h_val
    unfold addListDigit; rw [h_rec]; dsimp only
    by_cases h_carry : carry.val = CardinalNatural.Peano.zero
    · rw [h_carry, CardinalNatural.Peano.zero_multiply,
          CardinalNatural.Peano.add_zero] at h_val
      rw [if_pos h_carry]
      exact h_val
    · rw [if_neg h_carry, toCardinalNaturalPeano_firstElement, h_len,
          CardinalNatural.Peano.add_commutative (carry.val * _)]
      exact h_val

theorem toCardinalNaturalPeano_multiplyDigitsPeano (d : Decimal) (n : CardinalNatural.Peano) :
    toCardinalNaturalPeano (multiplyDigitsPeano d n) CardinalNatural.Peano.zero =
      d.val * n := by
  induction n with
  | zero =>
    simp [multiplyDigitsPeano, toCardinalNaturalPeano_firstElement, toCardinalNaturalPeano, zeroDigit,
          Sequences.List.length, CardinalNatural.Peano.tenPow, CardinalNatural.Peano.multiply_zero,
          CardinalNatural.Peano.multiply_one]
  | successor n ih =>
    unfold multiplyDigitsPeano
    rw [toCardinalNaturalPeano_addListDigit, ih, CardinalNatural.Peano.multiply_successor]

theorem toCardinalNaturalPeano_multiplyDigits (d b : Decimal) :
    toCardinalNaturalPeano (multiplyDigits d b) CardinalNatural.Peano.zero = d.val * b.val := by
  unfold multiplyDigits
  exact toCardinalNaturalPeano_multiplyDigitsPeano d b.val

theorem toCardinalNaturalPeano_addListDigit_multiplyDigits (d b carry : Decimal) :
    toCardinalNaturalPeano (addListDigit (multiplyDigits d b) carry) CardinalNatural.Peano.zero =
      d.val * b.val + carry.val := by
  rw [toCardinalNaturalPeano_addListDigit, toCardinalNaturalPeano_multiplyDigits]

theorem multiplyPartialListByDigit_spec (a : Sequences.List Decimal) (d : Decimal) :
    (multiplyPartialListByDigit a d).1.length = a.length ∧
    toCardinalNaturalPeano (multiplyPartialListByDigit a d).1 CardinalNatural.Peano.zero +
        (multiplyPartialListByDigit a d).2.val * CardinalNatural.Peano.tenPow a.length =
      toCardinalNaturalPeano a CardinalNatural.Peano.zero * d.val := by
  induction a with
  | empty =>
      simp [multiplyPartialListByDigit, toCardinalNaturalPeano, Sequences.List.length,
        CardinalNatural.Peano.tenPow, zeroDigit, CardinalNatural.Peano.zero_multiply,
        CardinalNatural.Peano.multiply_one]
  | firstElement digit ds ih =>
      unfold multiplyPartialListByDigit
      dsimp only
      cases h_rec : multiplyPartialListByDigit ds d with
      | mk digits carry =>
          rw [h_rec] at ih
          dsimp only at ih
          obtain ⟨h_length, ih_value⟩ := ih
          have h_withCarry_value := toCardinalNaturalPeano_addListDigit_multiplyDigits digit d carry
          split
          · next h_withCarry =>
              exact False.elim (addListDigit_multiplyDigits_ne_empty digit d carry h_withCarry)
          · next x h_withCarry =>
              constructor
              · simp [Sequences.List.length, h_length]
              · rw [h_withCarry] at h_withCarry_value
                simp only [toCardinalNaturalPeano, CardinalNatural.Peano.zero_multiply,
                  CardinalNatural.Peano.zero_add] at h_withCarry_value
                simp only [toCardinalNaturalPeano_firstElement, Sequences.List.length, zeroDigit,
                  CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.add_zero]
                rw [h_length]
                calc
                  _ = (digit.val * d.val + carry.val) * CardinalNatural.Peano.tenPow ds.length +
                        toCardinalNaturalPeano digits CardinalNatural.Peano.zero := by
                      rw [h_withCarry_value]
                  _ = digit.val * d.val * CardinalNatural.Peano.tenPow ds.length +
                        (carry.val * CardinalNatural.Peano.tenPow ds.length +
                          toCardinalNaturalPeano digits CardinalNatural.Peano.zero) := by
                      rw [CardinalNatural.Peano.multiply_distributive_over_add_left]
                      rw [CardinalNatural.Peano.add_associative]
                  _ = digit.val * d.val * CardinalNatural.Peano.tenPow ds.length +
                        (toCardinalNaturalPeano digits CardinalNatural.Peano.zero +
                          carry.val * CardinalNatural.Peano.tenPow ds.length) := by
                      rw [CardinalNatural.Peano.add_commutative
                        (carry.val * CardinalNatural.Peano.tenPow ds.length)
                        (toCardinalNaturalPeano digits CardinalNatural.Peano.zero)]
                  _ = digit.val * d.val * CardinalNatural.Peano.tenPow ds.length +
                        (toCardinalNaturalPeano ds CardinalNatural.Peano.zero * d.val) := by
                      rw [ih_value]
                  _ = (digit.val * CardinalNatural.Peano.tenPow ds.length +
                        toCardinalNaturalPeano ds CardinalNatural.Peano.zero) * d.val := by
                      rw [CardinalNatural.Peano.multiply_distributive_over_add_left]
                      rw [CardinalNatural.Peano.multiply_associative]
                      rw [CardinalNatural.Peano.multiply_commutative d.val (CardinalNatural.Peano.tenPow ds.length)]
                      rw [← CardinalNatural.Peano.multiply_associative digit.val (CardinalNatural.Peano.tenPow ds.length) d.val]
          · next x y h_withCarry =>
              constructor
              · simp [Sequences.List.length, h_length]
              · rw [h_withCarry] at h_withCarry_value
                simp only [toCardinalNaturalPeano, CardinalNatural.Peano.zero_multiply,
                  CardinalNatural.Peano.zero_add] at h_withCarry_value
                simp only [toCardinalNaturalPeano_firstElement, Sequences.List.length]
                rw [h_length, CardinalNatural.Peano.tenPow_add_one]
                calc
                  _ = (y.val + x.val * CardinalNatural.Peano.ten) *
                        CardinalNatural.Peano.tenPow ds.length +
                        toCardinalNaturalPeano digits CardinalNatural.Peano.zero := by
                      rw [CardinalNatural.Peano.multiply_distributive_over_add_left]
                      rw [CardinalNatural.Peano.multiply_associative]
                      rw [← CardinalNatural.Peano.multiply_associative x.val]
                      simp only [CardinalNatural.Peano.add_associative,
                        CardinalNatural.Peano.add_commutative]
                  _ = (x.val * CardinalNatural.Peano.ten + y.val) *
                        CardinalNatural.Peano.tenPow ds.length +
                        toCardinalNaturalPeano digits CardinalNatural.Peano.zero := by
                      rw [CardinalNatural.Peano.add_commutative y.val (x.val * CardinalNatural.Peano.ten)]
                  _ = (digit.val * d.val + carry.val) *
                        CardinalNatural.Peano.tenPow ds.length +
                        toCardinalNaturalPeano digits CardinalNatural.Peano.zero := by
                      rw [h_withCarry_value]
                  _ = digit.val * d.val * CardinalNatural.Peano.tenPow ds.length +
                        (carry.val * CardinalNatural.Peano.tenPow ds.length +
                          toCardinalNaturalPeano digits CardinalNatural.Peano.zero) := by
                      rw [CardinalNatural.Peano.multiply_distributive_over_add_left]
                      rw [CardinalNatural.Peano.add_associative]
                  _ = digit.val * d.val * CardinalNatural.Peano.tenPow ds.length +
                        (toCardinalNaturalPeano digits CardinalNatural.Peano.zero +
                          carry.val * CardinalNatural.Peano.tenPow ds.length) := by
                      rw [CardinalNatural.Peano.add_commutative
                        (carry.val * CardinalNatural.Peano.tenPow ds.length)
                        (toCardinalNaturalPeano digits CardinalNatural.Peano.zero)]
                  _ = digit.val * d.val * CardinalNatural.Peano.tenPow ds.length +
                        (toCardinalNaturalPeano ds CardinalNatural.Peano.zero * d.val) := by
                      rw [ih_value]
                  _ = (digit.val * CardinalNatural.Peano.tenPow ds.length +
                        toCardinalNaturalPeano ds CardinalNatural.Peano.zero) * d.val := by
                      rw [CardinalNatural.Peano.multiply_distributive_over_add_left]
                      rw [CardinalNatural.Peano.multiply_associative]
                      rw [CardinalNatural.Peano.multiply_commutative d.val (CardinalNatural.Peano.tenPow ds.length)]
                      rw [← CardinalNatural.Peano.multiply_associative digit.val (CardinalNatural.Peano.tenPow ds.length) d.val]
          · next x y z zs h_withCarry =>
              exact False.elim (addListDigit_multiplyDigits_not_three_or_more digit d carry x y z zs h_withCarry)

theorem toCardinalNaturalPeano_multiplyListByDigit (a : Sequences.List Decimal) (d : Decimal) :
    toCardinalNaturalPeano (multiplyListByDigit a d) CardinalNatural.Peano.zero =
      toCardinalNaturalPeano a CardinalNatural.Peano.zero * d.val := by
  obtain ⟨h_len, h_val⟩ := multiplyPartialListByDigit_spec a d
  cases h_rec : multiplyPartialListByDigit a d with
  | mk ds carry =>
    rw [h_rec] at h_len h_val; dsimp only at h_len h_val
    unfold multiplyListByDigit; rw [h_rec]; dsimp only
    by_cases h_carry : carry.val = CardinalNatural.Peano.zero
    · rw [h_carry, CardinalNatural.Peano.zero_multiply,
          CardinalNatural.Peano.add_zero] at h_val
      rw [if_pos h_carry]
      exact h_val
    · rw [if_neg h_carry, toCardinalNaturalPeano_firstElement, h_len,
          CardinalNatural.Peano.add_commutative (carry.val * _)]
      exact h_val

theorem toCardinalNaturalPeano_addAlignedLists_result {a b : Sequences.List Decimal}
  (h : Sequences.List.SameLength a b) :
  let result := addAlignedLists a b h
  let digitsWithCarry :=
    if result.2 then Sequences.List.firstElement oneDigit result.1 else result.1
  toCardinalNaturalPeano digitsWithCarry CardinalNatural.Peano.zero =
    toCardinalNaturalPeano a CardinalNatural.Peano.zero +
      toCardinalNaturalPeano b CardinalNatural.Peano.zero := by
  cases h_add : addAlignedLists a b h with
  | mk digits carry =>
      have h_spec := addAlignedLists_spec h
      rw [h_add] at h_spec
      dsimp only at h_spec ⊢
      obtain ⟨h_length, h_value⟩ := h_spec
      cases carry with
      | false =>
          simp only [if_neg Bool.false_ne_true, CardinalNatural.Peano.add_zero] at h_value ⊢
          exact h_value
      | true =>
          simp only [if_true] at h_value ⊢
          rw [toCardinalNaturalPeano_firstElement, oneDigit, CardinalNatural.Peano.one_multiply, h_length]
          rw [CardinalNatural.Peano.add_commutative]
          exact h_value

theorem multiplyList_spec (a b : Sequences.List Decimal) :
    (multiplyList a b).2 = b.length ∧
    toCardinalNaturalPeano (multiplyList a b).1 CardinalNatural.Peano.zero =
      toCardinalNaturalPeano a CardinalNatural.Peano.zero * toCardinalNaturalPeano b CardinalNatural.Peano.zero := by
  induction b with
  | empty =>
      simp [multiplyList, toCardinalNaturalPeano, Sequences.List.length, CardinalNatural.Peano.multiply_zero]
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
              · cases carry <;> simp [Sequences.List.length, h_shift, CardinalNatural.Peano.one,
                  CardinalNatural.Peano.add_successor, CardinalNatural.Peano.add_zero]
              · have h_add_value := toCardinalNaturalPeano_addAlignedLists_result h_same
                rw [h_add] at h_add_value
                dsimp only at h_add_value
                cases carry with
                | false =>
                    simp only [if_neg Bool.false_ne_true] at h_add_value ⊢
                    rw [h_add_value]
                    rw [toCardinalNaturalPeano_padAtStartToSameLength_fst,
                        toCardinalNaturalPeano_padAtStartToSameLength_snd]
                    dsimp only [withShift, digitProduct]
                    rw [toCardinalNaturalPeano_padAtEnd, toCardinalNaturalPeano_multiplyListByDigit, ih_value, h_shift]
                    rw [toCardinalNaturalPeano_firstElement]
                    calc
                      toCardinalNaturalPeano a CardinalNatural.Peano.zero *
                            toCardinalNaturalPeano ds CardinalNatural.Peano.zero +
                          toCardinalNaturalPeano a CardinalNatural.Peano.zero * d.val *
                            CardinalNatural.Peano.tenPow ds.length =
                        toCardinalNaturalPeano a CardinalNatural.Peano.zero *
                          (toCardinalNaturalPeano ds CardinalNatural.Peano.zero +
                            d.val * CardinalNatural.Peano.tenPow ds.length) := by
                          rw [CardinalNatural.Peano.multiply_distributive_over_add_right]
                          rw [CardinalNatural.Peano.multiply_associative]
                      _ = toCardinalNaturalPeano a CardinalNatural.Peano.zero *
                          (d.val * CardinalNatural.Peano.tenPow ds.length +
                            toCardinalNaturalPeano ds CardinalNatural.Peano.zero) := by
                          rw [CardinalNatural.Peano.add_commutative]
                | true =>
                    simp only [if_true] at h_add_value ⊢
                    rw [h_add_value]
                    rw [toCardinalNaturalPeano_padAtStartToSameLength_fst,
                        toCardinalNaturalPeano_padAtStartToSameLength_snd]
                    dsimp only [withShift, digitProduct]
                    rw [toCardinalNaturalPeano_padAtEnd, toCardinalNaturalPeano_multiplyListByDigit, ih_value, h_shift]
                    rw [toCardinalNaturalPeano_firstElement]
                    calc
                      toCardinalNaturalPeano a CardinalNatural.Peano.zero *
                            toCardinalNaturalPeano ds CardinalNatural.Peano.zero +
                          toCardinalNaturalPeano a CardinalNatural.Peano.zero * d.val *
                            CardinalNatural.Peano.tenPow ds.length =
                        toCardinalNaturalPeano a CardinalNatural.Peano.zero *
                          (toCardinalNaturalPeano ds CardinalNatural.Peano.zero +
                            d.val * CardinalNatural.Peano.tenPow ds.length) := by
                          rw [CardinalNatural.Peano.multiply_distributive_over_add_right]
                          rw [CardinalNatural.Peano.multiply_associative]
                      _ = toCardinalNaturalPeano a CardinalNatural.Peano.zero *
                          (d.val * CardinalNatural.Peano.tenPow ds.length +
                            toCardinalNaturalPeano ds CardinalNatural.Peano.zero) := by
                          rw [CardinalNatural.Peano.add_commutative]

theorem addAlignedLists_eq_of_swapped {a b c d : Sequences.List Decimal}
  (h₁ : Sequences.List.SameLength a b) (h₂ : Sequences.List.SameLength c d)
  (hc : c = b) (hd : d = a) :
  addAlignedLists a b h₁ = addAlignedLists c d h₂ := by
  subst c
  subst d
  exact addAlignedLists_commutative a b h₁

theorem addAlignedLists_after_padding_commutative (a b : Sequences.List Decimal) :
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

theorem subtractAlignedLists_borrow_false_of_lessThan {a b : Sequences.List Decimal}
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

theorem toCardinalNaturalPeano_eq_zero_of_isEmpty
    {l : Sequences.List Decimal} (h : Sequences.List.isEmpty l = true) :
    toCardinalNaturalPeano l CardinalNatural.Peano.zero = CardinalNatural.Peano.zero := by
  cases l with
  | empty => rfl
  | firstElement d ds =>
      unfold Sequences.List.isEmpty at h
      cases h

theorem toCardinalNaturalPeano_append (l : Sequences.List Decimal) (d : Decimal) :
    toCardinalNaturalPeano (Sequences.List.append l d) CardinalNatural.Peano.zero =
      toCardinalNaturalPeano l CardinalNatural.Peano.zero * CardinalNatural.Peano.ten + d.val := by
  induction l with
  | empty =>
      simp [Sequences.List.append, toCardinalNaturalPeano_firstElement, toCardinalNaturalPeano,
        Sequences.List.length, CardinalNatural.Peano.tenPow,
        CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.zero_add,
        CardinalNatural.Peano.multiply_one]
  | firstElement x xs ih =>
      rw [Sequences.List.append, toCardinalNaturalPeano_firstElement, ih,
        Sequences.List.append_length, CardinalNatural.Peano.tenPow_add_one,
        toCardinalNaturalPeano_firstElement,
        CardinalNatural.Peano.multiply_distributive_over_add_left,
        CardinalNatural.Peano.multiply_associative,
        CardinalNatural.Peano.add_associative,
        CardinalNatural.Peano.multiply_commutative CardinalNatural.Peano.ten]

theorem toCardinalNaturalPeano_ne_zero_of_acc_ne_zero (a : Sequences.List Decimal)
    (acc : CardinalNatural.Peano) (h_acc : acc ≠ CardinalNatural.Peano.zero) :
    toCardinalNaturalPeano a acc ≠ CardinalNatural.Peano.zero := by
  induction a generalizing acc with
  | empty =>
      exact h_acc
  | firstElement d ds ih =>
      exact ih (acc * CardinalNatural.Peano.ten + d.val)
        (CardinalNatural.Peano.add_ne_zero_of_left_ne_zero
          (acc * CardinalNatural.Peano.ten) d.val
          (CardinalNatural.Peano.multiply_ne_zero acc CardinalNatural.Peano.ten h_acc
            (CardinalNatural.Peano.successor_ne_zero CardinalNatural.Peano.nine)))

theorem toCardinalNaturalPeano_ge_tenPow_of_ne_zero (d : Decimal) (ds : Sequences.List Decimal)
    (hd : d.val ≠ CardinalNatural.Peano.zero) :
    CardinalNatural.Peano.tenPow ds.length ≤
      d.val * CardinalNatural.Peano.tenPow ds.length +
        toCardinalNaturalPeano ds CardinalNatural.Peano.zero := by
  have hd_pos : CardinalNatural.Peano.one ≤ d.val := by
    cases h_d : d.val with
    | zero => exact absurd h_d hd
    | successor v =>
        exact CardinalNatural.Peano.succ_le_of_lt
          (CardinalNatural.Peano.zero_lt_succ v)
  have hge1 :
      CardinalNatural.Peano.one * CardinalNatural.Peano.tenPow ds.length ≤
        d.val * CardinalNatural.Peano.tenPow ds.length :=
    CardinalNatural.Peano.multiply_le_mul_left hd_pos
      (CardinalNatural.Peano.tenPow ds.length)
  rw [CardinalNatural.Peano.one_multiply] at hge1
  exact CardinalNatural.Peano.le_trans hge1
    (CardinalNatural.Peano.le_add_self_left _ _)

/-- Numerical comparison of digit lists (leading zeros via padding are insignificant). -/
def isLessThanLists (x y : Sequences.List Decimal) : Bool :=
  let pair := Sequences.List.padAtStartToSameLength x y zeroDigit
  isLessThanAlignedLists pair.1 pair.2
    (Sequences.List.padAtStartToSameLength_sameLength x y zeroDigit)

/-- Columnar subtraction of digit lists, assuming `y ≤ x` numerically. -/
def subtractLists (x y : Sequences.List Decimal) : Sequences.List Decimal :=
  let pair := Sequences.List.padAtStartToSameLength x y zeroDigit
  let h_same := Sequences.List.padAtStartToSameLength_sameLength x y zeroDigit
  (subtractAlignedLists pair.1 pair.2 h_same).1

theorem isLessThanLists_iff_toCardinalNaturalPeano_lt (x y : Sequences.List Decimal) :
    isLessThanLists x y = true ↔
      toCardinalNaturalPeano x CardinalNatural.Peano.zero <
        toCardinalNaturalPeano y CardinalNatural.Peano.zero := by
  unfold isLessThanLists
  let pair := Sequences.List.padAtStartToSameLength x y zeroDigit
  let h_same := Sequences.List.padAtStartToSameLength_sameLength x y zeroDigit
  have hpad_x := toCardinalNaturalPeano_padAtStartToSameLength_fst x y
  have hpad_y := toCardinalNaturalPeano_padAtStartToSameLength_snd x y
  constructor
  · intro h
    have hlt_aligned :
        LessThanAlignedLists pair.1 pair.2 h_same :=
      (isLessThanAlignedLists_iff_lessThanAlignedLists pair.1 pair.2 h_same).mp h
    have := LessThanAlignedLists_toCardinalNaturalPeano_lt h_same hlt_aligned
    rwa [hpad_x, hpad_y] at this
  · intro hlt
    have hlt_pad :
        toCardinalNaturalPeano pair.1 CardinalNatural.Peano.zero <
          toCardinalNaturalPeano pair.2 CardinalNatural.Peano.zero := by
      rwa [hpad_x, hpad_y]
    have hlt_aligned :=
      LessThanAlignedLists_of_toCardinalNaturalPeano_lt h_same hlt_pad
    exact (isLessThanAlignedLists_iff_lessThanAlignedLists pair.1 pair.2 h_same).mpr
      hlt_aligned

theorem isLessThanLists_eq_false_iff_not_lt (x y : Sequences.List Decimal) :
    isLessThanLists x y = false ↔
      ¬ toCardinalNaturalPeano x CardinalNatural.Peano.zero <
          toCardinalNaturalPeano y CardinalNatural.Peano.zero := by
  constructor
  · intro h hlt
    have htrue := (isLessThanLists_iff_toCardinalNaturalPeano_lt x y).mpr hlt
    rw [htrue] at h
    exact Bool.noConfusion h
  · intro hnlt
    cases h : isLessThanLists x y with
    | false => rfl
    | true =>
      exact False.elim (hnlt ((isLessThanLists_iff_toCardinalNaturalPeano_lt x y).mp h))

theorem subtractAlignedLists_spec_calc_false_true (da db L digits dbs das : CardinalNatural.Peano)
  (h_le : db ≤ da + CardinalNatural.Peano.ten)
  (ih_value : digits + dbs = das) :
  (CardinalNatural.Peano.subtract (da + CardinalNatural.Peano.ten) db h_le + db) *
      CardinalNatural.Peano.tenPow L +
    (digits + dbs) =
  da * CardinalNatural.Peano.tenPow L + das +
    CardinalNatural.Peano.ten * CardinalNatural.Peano.tenPow L := by
  have h_digit := CardinalNatural.Peano.subtract_add_cancel (da + CardinalNatural.Peano.ten) db h_le
  calc
    _ = (CardinalNatural.Peano.subtract (da + CardinalNatural.Peano.ten) db h_le + db) *
          CardinalNatural.Peano.tenPow L +
        (digits + dbs) := rfl
    _ = (da + CardinalNatural.Peano.ten) * CardinalNatural.Peano.tenPow L + das := by
          rw [h_digit, ih_value]
    _ = da * CardinalNatural.Peano.tenPow L + das +
        CardinalNatural.Peano.ten * CardinalNatural.Peano.tenPow L := by
          rw [CardinalNatural.Peano.multiply_distributive_over_add_left]
          exact CardinalNatural.Peano.add_right_commutative _ _ _

theorem subtractAlignedLists_spec_calc_false_false (da db L digits dbs das : CardinalNatural.Peano)
  (h_le : db ≤ da)
  (ih_value : digits + dbs = das) :
  (CardinalNatural.Peano.subtract da db h_le + db) *
      CardinalNatural.Peano.tenPow L +
    (digits + dbs) =
  da * CardinalNatural.Peano.tenPow L + das + CardinalNatural.Peano.zero := by
  have h_digit := CardinalNatural.Peano.subtract_add_cancel da db h_le
  calc
    _ = (CardinalNatural.Peano.subtract da db h_le + db) *
          CardinalNatural.Peano.tenPow L +
        (digits + dbs) := rfl
    _ = da * CardinalNatural.Peano.tenPow L + das := by
          rw [h_digit, ih_value]
    _ = da * CardinalNatural.Peano.tenPow L + das + CardinalNatural.Peano.zero := by
          rw [CardinalNatural.Peano.add_zero]

theorem subtractAlignedLists_spec_calc_true_true (da db L digits dbs das : CardinalNatural.Peano)
  (h_le : db.successor ≤ da + CardinalNatural.Peano.ten)
  (ih_value : digits + dbs = das + CardinalNatural.Peano.tenPow L) :
  (CardinalNatural.Peano.subtract (da + CardinalNatural.Peano.ten) db.successor h_le + db) *
      CardinalNatural.Peano.tenPow L +
    (digits + dbs) =
  da * CardinalNatural.Peano.tenPow L + das +
    CardinalNatural.Peano.ten * CardinalNatural.Peano.tenPow L := by
  have h_digit := CardinalNatural.Peano.subtract_add_cancel (da + CardinalNatural.Peano.ten) db.successor h_le
  calc
    _ = (CardinalNatural.Peano.subtract (da + CardinalNatural.Peano.ten) db.successor h_le + db) *
          CardinalNatural.Peano.tenPow L +
        (digits + dbs) := rfl
    _ = (CardinalNatural.Peano.subtract (da + CardinalNatural.Peano.ten) db.successor h_le + db) *
          CardinalNatural.Peano.tenPow L +
        (das + CardinalNatural.Peano.tenPow L) := by
          rw [ih_value]
    _ = (CardinalNatural.Peano.subtract (da + CardinalNatural.Peano.ten) db.successor h_le + db).successor *
          CardinalNatural.Peano.tenPow L +
        das := by
          rw [CardinalNatural.Peano.successor_multiply]
          rw [CardinalNatural.Peano.add_commutative das (CardinalNatural.Peano.tenPow L)]
          rw [← CardinalNatural.Peano.add_associative]
    _ = (da + CardinalNatural.Peano.ten) * CardinalNatural.Peano.tenPow L + das := by
          rw [← CardinalNatural.Peano.add_successor]
          rw [h_digit]
    _ = da * CardinalNatural.Peano.tenPow L + das +
        CardinalNatural.Peano.ten * CardinalNatural.Peano.tenPow L := by
          rw [CardinalNatural.Peano.multiply_distributive_over_add_left]
          exact CardinalNatural.Peano.add_right_commutative _ _ _

theorem subtractAlignedLists_spec_calc_true_false (da db L digits dbs das : CardinalNatural.Peano)
  (h_le : db.successor ≤ da)
  (ih_value : digits + dbs = das + CardinalNatural.Peano.tenPow L) :
  (CardinalNatural.Peano.subtract da db.successor h_le + db) *
      CardinalNatural.Peano.tenPow L +
    (digits + dbs) =
  da * CardinalNatural.Peano.tenPow L + das + CardinalNatural.Peano.zero := by
  have h_digit := CardinalNatural.Peano.subtract_add_cancel da db.successor h_le
  calc
    _ = (CardinalNatural.Peano.subtract da db.successor h_le + db) *
          CardinalNatural.Peano.tenPow L +
        (digits + dbs) := rfl
    _ = (CardinalNatural.Peano.subtract da db.successor h_le + db) *
          CardinalNatural.Peano.tenPow L +
        (das + CardinalNatural.Peano.tenPow L) := by
          rw [ih_value]
    _ = (CardinalNatural.Peano.subtract da db.successor h_le + db).successor *
          CardinalNatural.Peano.tenPow L +
        das := by
          rw [CardinalNatural.Peano.successor_multiply]
          exact CardinalNatural.Peano.add_right_swap _ _ _
    _ = da * CardinalNatural.Peano.tenPow L + das := by
          rw [← CardinalNatural.Peano.add_successor]
          rw [h_digit]
    _ = da * CardinalNatural.Peano.tenPow L + das + CardinalNatural.Peano.zero := by
          rw [CardinalNatural.Peano.add_zero]

theorem subtractAlignedLists_spec {a b : Sequences.List Decimal}
  (h : Sequences.List.SameLength a b) :
  let result := subtractAlignedLists a b h
  result.1.length = a.length ∧
    toCardinalNaturalPeano result.1 CardinalNatural.Peano.zero +
        toCardinalNaturalPeano b CardinalNatural.Peano.zero =
      toCardinalNaturalPeano a CardinalNatural.Peano.zero +
        (if result.2 then CardinalNatural.Peano.tenPow a.length else CardinalNatural.Peano.zero) := by
  induction h using Sequences.List.SameLength.induction with
  | empty =>
      simp [subtractAlignedLists, toCardinalNaturalPeano, Sequences.List.length]
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
                  · simp only [toCardinalNaturalPeano_firstElement, Sequences.List.length,
                      CardinalNatural.Peano.tenPow_add_one, if_true]
                    rw [h_length, ← h_tail_lengths]
                    have h_le : db.val ≤ da.val + CardinalNatural.Peano.ten := by
                      exact CardinalNatural.Peano.le_trans (digit_val_le_ten db)
                        (CardinalNatural.Peano.le_add_self_right da.val CardinalNatural.Peano.ten)
                    calc
                      _ = (CardinalNatural.Peano.subtract (da.val + CardinalNatural.Peano.ten) db.val h_le + db.val) *
                            CardinalNatural.Peano.tenPow das.length +
                          (toCardinalNaturalPeano digits CardinalNatural.Peano.zero +
                            toCardinalNaturalPeano dbs CardinalNatural.Peano.zero) := by
                            rw [CardinalNatural.Peano.multiply_distributive_over_add_left]
                            exact CardinalNatural.Peano.add_pair_swap _ _ _ _
                      _ = _ := subtractAlignedLists_spec_calc_false_true da.val db.val das.length
                                (toCardinalNaturalPeano digits CardinalNatural.Peano.zero)
                                (toCardinalNaturalPeano dbs CardinalNatural.Peano.zero)
                                (toCardinalNaturalPeano das CardinalNatural.Peano.zero)
                                h_le ih_value
              · next h_not_lt =>
                  constructor
                  · simp [Sequences.List.length, h_length]
                  · simp only [toCardinalNaturalPeano_firstElement, Sequences.List.length]
                    simp only [if_neg Bool.false_ne_true]
                    rw [h_length, ← h_tail_lengths]
                    have h_le : db.val ≤ da.val := CardinalNatural.Peano.not_lt_implies_le h_not_lt
                    calc
                      _ = (CardinalNatural.Peano.subtract da.val db.val h_le + db.val) *
                            CardinalNatural.Peano.tenPow das.length +
                          (toCardinalNaturalPeano digits CardinalNatural.Peano.zero +
                            toCardinalNaturalPeano dbs CardinalNatural.Peano.zero) := by
                            rw [CardinalNatural.Peano.multiply_distributive_over_add_left]
                            exact CardinalNatural.Peano.add_pair_swap _ _ _ _
                      _ = _ := subtractAlignedLists_spec_calc_false_false da.val db.val das.length
                                (toCardinalNaturalPeano digits CardinalNatural.Peano.zero)
                                (toCardinalNaturalPeano dbs CardinalNatural.Peano.zero)
                                (toCardinalNaturalPeano das CardinalNatural.Peano.zero)
                                h_le ih_value
          | true =>
              simp at ih_value ⊢
              split
              · next h_da_lt_db_succ =>
                  constructor
                  · simp [Sequences.List.length, h_length]
                  · simp only [toCardinalNaturalPeano_firstElement, Sequences.List.length,
                      CardinalNatural.Peano.tenPow_add_one, if_true]
                    rw [h_length, ← h_tail_lengths]
                    have h_le : db.val.successor ≤ da.val + CardinalNatural.Peano.ten := by
                      exact CardinalNatural.Peano.le_trans (digit_val_successor_le_ten db)
                        (CardinalNatural.Peano.le_add_self_right da.val CardinalNatural.Peano.ten)
                    calc
                      _ = (CardinalNatural.Peano.subtract (da.val + CardinalNatural.Peano.ten) db.val.successor h_le + db.val) *
                            CardinalNatural.Peano.tenPow das.length +
                          (toCardinalNaturalPeano digits CardinalNatural.Peano.zero +
                            toCardinalNaturalPeano dbs CardinalNatural.Peano.zero) := by
                            rw [CardinalNatural.Peano.multiply_distributive_over_add_left]
                            exact CardinalNatural.Peano.add_pair_swap _ _ _ _
                      _ = _ := subtractAlignedLists_spec_calc_true_true da.val db.val das.length
                                (toCardinalNaturalPeano digits CardinalNatural.Peano.zero)
                                (toCardinalNaturalPeano dbs CardinalNatural.Peano.zero)
                                (toCardinalNaturalPeano das CardinalNatural.Peano.zero)
                                h_le ih_value
              · next h_not_lt =>
                  constructor
                  · simp [Sequences.List.length, h_length]
                  · simp only [toCardinalNaturalPeano_firstElement, Sequences.List.length]
                    simp only [if_neg Bool.false_ne_true]
                    rw [h_length, ← h_tail_lengths]
                    have h_le : db.val.successor ≤ da.val := CardinalNatural.Peano.not_lt_implies_le h_not_lt
                    calc
                      _ = (CardinalNatural.Peano.subtract da.val db.val.successor h_le + db.val) *
                            CardinalNatural.Peano.tenPow das.length +
                          (toCardinalNaturalPeano digits CardinalNatural.Peano.zero +
                            toCardinalNaturalPeano dbs CardinalNatural.Peano.zero) := by
                            rw [CardinalNatural.Peano.multiply_distributive_over_add_left]
                            exact CardinalNatural.Peano.add_pair_swap _ _ _ _
                      _ = _ := subtractAlignedLists_spec_calc_true_false da.val db.val das.length
                                (toCardinalNaturalPeano digits CardinalNatural.Peano.zero)
                                (toCardinalNaturalPeano dbs CardinalNatural.Peano.zero)
                                (toCardinalNaturalPeano das CardinalNatural.Peano.zero)
                                h_le ih_value

theorem subtractAlignedLists_borrow_false_of_not_lt {a b : Sequences.List Decimal}
    (h_same : Sequences.List.SameLength a b)
    (hnlt : ¬ toCardinalNaturalPeano a CardinalNatural.Peano.zero <
      toCardinalNaturalPeano b CardinalNatural.Peano.zero) :
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
      have hdigits_lt := toCardinalNaturalPeano_lt_tenPow digits
      rw [h_len] at hdigits_lt
      have hlt_sum :
          toCardinalNaturalPeano digits CardinalNatural.Peano.zero +
              toCardinalNaturalPeano b CardinalNatural.Peano.zero <
            CardinalNatural.Peano.tenPow a.length +
              toCardinalNaturalPeano b CardinalNatural.Peano.zero :=
        CardinalNatural.Peano.add_lt_add_right hdigits_lt _
      rw [h_val] at hlt_sum
      have hlt_sum' :
          toCardinalNaturalPeano a CardinalNatural.Peano.zero +
              CardinalNatural.Peano.tenPow a.length <
            toCardinalNaturalPeano b CardinalNatural.Peano.zero +
              CardinalNatural.Peano.tenPow a.length := by
        rwa [CardinalNatural.Peano.add_commutative
          (CardinalNatural.Peano.tenPow a.length)
          (toCardinalNaturalPeano b CardinalNatural.Peano.zero)] at hlt_sum
      exact False.elim (hnlt (CardinalNatural.Peano.add_lt_cancel_right hlt_sum'))

theorem subtractLists_spec (x y : Sequences.List Decimal)
    (hnlt : ¬ toCardinalNaturalPeano x CardinalNatural.Peano.zero <
      toCardinalNaturalPeano y CardinalNatural.Peano.zero) :
    toCardinalNaturalPeano (subtractLists x y) CardinalNatural.Peano.zero +
        toCardinalNaturalPeano y CardinalNatural.Peano.zero =
      toCardinalNaturalPeano x CardinalNatural.Peano.zero := by
  let h_same := Sequences.List.padAtStartToSameLength_sameLength x y zeroDigit
  have hpad_x := toCardinalNaturalPeano_padAtStartToSameLength_fst x y
  have hpad_y := toCardinalNaturalPeano_padAtStartToSameLength_snd x y
  have hnlt_pad :
      ¬ toCardinalNaturalPeano (Sequences.List.padAtStartToSameLength x y zeroDigit).1
            CardinalNatural.Peano.zero <
          toCardinalNaturalPeano (Sequences.List.padAtStartToSameLength x y zeroDigit).2
            CardinalNatural.Peano.zero := by
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
    simp only [hborrow, if_neg Bool.false_ne_true, CardinalNatural.Peano.add_zero] at h_val
    rw [hpad_x, hpad_y] at h_val
    simpa [subtractLists, hres] using h_val

/--
Largest digit `q ≤ candidate` such that `divisor * q ≤ remainder`, together with
the columnar difference `remainder - divisor * q`.
-/
def findQuotientDigitAux (remainder divisor : Sequences.List Decimal)
    (candidate : CardinalNatural.Peano) (hc : candidate < CardinalNatural.Peano.ten) :
    Decimal × Sequences.List Decimal :=
  let d : Decimal := ⟨candidate, hc⟩
  let product := multiplyListByDigit divisor d
  if isLessThanLists remainder product then
    match candidate with
    | .zero => (zeroDigit, remainder)
    | .successor c' =>
        findQuotientDigitAux remainder divisor c'
          (CardinalNatural.Peano.lt_of_succ_lt hc)
  else
    (d, subtractLists remainder product)

def findQuotientDigit (remainder divisor : Sequences.List Decimal) :
    Decimal × Sequences.List Decimal :=
  findQuotientDigitAux remainder divisor CardinalNatural.Peano.nine
    CardinalNatural.Peano.nine_lt_ten

theorem findQuotientDigitAux_spec (remainder divisor : Sequences.List Decimal)
    (candidate : CardinalNatural.Peano) (hc : candidate < CardinalNatural.Peano.ten) :
    let result := findQuotientDigitAux remainder divisor candidate hc
    let d := result.1
    let nextRem := result.2
    toCardinalNaturalPeano remainder CardinalNatural.Peano.zero =
        toCardinalNaturalPeano divisor CardinalNatural.Peano.zero * d.val +
          toCardinalNaturalPeano nextRem CardinalNatural.Peano.zero ∧
      ¬ toCardinalNaturalPeano remainder CardinalNatural.Peano.zero <
          toCardinalNaturalPeano divisor CardinalNatural.Peano.zero * d.val ∧
      (candidate = d.val ∨
        toCardinalNaturalPeano remainder CardinalNatural.Peano.zero <
          toCardinalNaturalPeano divisor CardinalNatural.Peano.zero * d.val.successor) := by
  induction candidate with
  | zero =>
    unfold findQuotientDigitAux
    dsimp only
    by_cases hlt : isLessThanLists remainder
        (multiplyListByDigit divisor ⟨CardinalNatural.Peano.zero, hc⟩) = true
    · have hlt_val :=
        (isLessThanLists_iff_toCardinalNaturalPeano_lt remainder
          (multiplyListByDigit divisor ⟨CardinalNatural.Peano.zero, hc⟩)).mp hlt
      rw [toCardinalNaturalPeano_multiplyListByDigit] at hlt_val
      simp only [CardinalNatural.Peano.multiply_zero] at hlt_val
      exact False.elim
        (CardinalNatural.Peano.cardinal_not_lt_of_le
          (CardinalNatural.Peano.zero_le _) hlt_val)
    · have hnlt := (isLessThanLists_eq_false_iff_not_lt remainder
          (multiplyListByDigit divisor ⟨CardinalNatural.Peano.zero, hc⟩)).mp
        (eq_false_of_ne_true hlt)
      have hsub := subtractLists_spec remainder
        (multiplyListByDigit divisor ⟨CardinalNatural.Peano.zero, hc⟩) hnlt
      rw [toCardinalNaturalPeano_multiplyListByDigit] at hsub hnlt
      rw [if_neg hlt]
      refine ⟨?_, hnlt, Or.inl rfl⟩
      simpa [CardinalNatural.Peano.multiply_zero, CardinalNatural.Peano.zero_add,
        CardinalNatural.Peano.add_commutative] using hsub.symm
  | successor c ih =>
    unfold findQuotientDigitAux
    dsimp only
    by_cases hlt : isLessThanLists remainder
        (multiplyListByDigit divisor ⟨c.successor, hc⟩) = true
    · rw [if_pos hlt]
      obtain ⟨heq, hle, hmax⟩ := ih (CardinalNatural.Peano.lt_of_succ_lt hc)
      refine ⟨heq, hle, ?_⟩
      cases hmax with
      | inl heq_d =>
        have hlt_val :=
          (isLessThanLists_iff_toCardinalNaturalPeano_lt remainder
            (multiplyListByDigit divisor ⟨c.successor, hc⟩)).mp hlt
        rw [toCardinalNaturalPeano_multiplyListByDigit] at hlt_val
        rw [← heq_d]
        exact Or.inr hlt_val
      | inr hlt' => exact Or.inr hlt'
    · have hnlt := (isLessThanLists_eq_false_iff_not_lt remainder
          (multiplyListByDigit divisor ⟨c.successor, hc⟩)).mp
        (eq_false_of_ne_true hlt)
      have hsub := subtractLists_spec remainder
        (multiplyListByDigit divisor ⟨c.successor, hc⟩) hnlt
      rw [toCardinalNaturalPeano_multiplyListByDigit] at hsub hnlt
      rw [if_neg hlt]
      refine ⟨?_, hnlt, Or.inl rfl⟩
      simpa [CardinalNatural.Peano.add_commutative] using hsub.symm

theorem findQuotientDigit_nextRem_lt
    {remainder divisor : Sequences.List Decimal}
    {qDigit : Decimal} {nextRem : Sequences.List Decimal}
    (heq : toCardinalNaturalPeano remainder CardinalNatural.Peano.zero =
        toCardinalNaturalPeano divisor CardinalNatural.Peano.zero * qDigit.val +
          toCardinalNaturalPeano nextRem CardinalNatural.Peano.zero)
    (hbound : toCardinalNaturalPeano remainder CardinalNatural.Peano.zero <
        toCardinalNaturalPeano divisor CardinalNatural.Peano.zero * qDigit.val.successor) :
    toCardinalNaturalPeano nextRem CardinalNatural.Peano.zero <
      toCardinalNaturalPeano divisor CardinalNatural.Peano.zero := by
  rw [heq, CardinalNatural.Peano.multiply_successor] at hbound
  rw [CardinalNatural.Peano.add_commutative
        (toCardinalNaturalPeano divisor CardinalNatural.Peano.zero * qDigit.val)
        (toCardinalNaturalPeano nextRem CardinalNatural.Peano.zero),
      CardinalNatural.Peano.add_commutative
        (toCardinalNaturalPeano divisor CardinalNatural.Peano.zero * qDigit.val)
        (toCardinalNaturalPeano divisor CardinalNatural.Peano.zero)] at hbound
  exact CardinalNatural.Peano.add_lt_cancel_right hbound

theorem findQuotientDigit_spec (remainder divisor : Sequences.List Decimal)
    (hrem : toCardinalNaturalPeano remainder CardinalNatural.Peano.zero <
        toCardinalNaturalPeano divisor CardinalNatural.Peano.zero * CardinalNatural.Peano.ten) :
    let result := findQuotientDigit remainder divisor
    let qDigit := result.1
    let nextRem := result.2
    toCardinalNaturalPeano remainder CardinalNatural.Peano.zero =
        toCardinalNaturalPeano divisor CardinalNatural.Peano.zero * qDigit.val +
          toCardinalNaturalPeano nextRem CardinalNatural.Peano.zero ∧
      toCardinalNaturalPeano nextRem CardinalNatural.Peano.zero <
        toCardinalNaturalPeano divisor CardinalNatural.Peano.zero := by
  unfold findQuotientDigit
  obtain ⟨heq, _hnlt, hmax⟩ :=
    findQuotientDigitAux_spec remainder divisor CardinalNatural.Peano.nine
      CardinalNatural.Peano.nine_lt_ten
  refine ⟨heq, ?_⟩
  cases hmax with
  | inl h_candidate =>
      apply findQuotientDigit_nextRem_lt heq
      rw [← h_candidate]
      exact hrem
  | inr hbound =>
      exact findQuotientDigit_nextRem_lt heq hbound

/--
Columnar (long) division step: process the remaining dividend digits while
accumulating the current remainder and quotient digit lists.
-/
def divideWithRemainderAux (dividend divisor : Sequences.List Decimal)
    (remainder quotient : Sequences.List Decimal) :
    Sequences.List Decimal × Sequences.List Decimal :=
  match dividend with
  | .empty => (quotient, remainder)
  | .firstElement d ds =>
      let newRem := Sequences.List.append remainder d
      let (qDigit, nextRem) := findQuotientDigit newRem divisor
      let newQuotient :=
        if Sequences.List.isEmpty quotient then
          if qDigit.val = CardinalNatural.Peano.zero then
            quotient
          else
            .firstElement qDigit .empty
        else
          Sequences.List.append quotient qDigit
      divideWithRemainderAux ds divisor nextRem newQuotient

theorem divideWithRemainderAux_newQuotient_value
    (quotient : Sequences.List Decimal) (qDigit : Decimal) :
    let newQuotient :=
      if Sequences.List.isEmpty quotient then
        if qDigit.val = CardinalNatural.Peano.zero then
          quotient
        else
          Sequences.List.firstElement qDigit Sequences.List.empty
      else
        Sequences.List.append quotient qDigit
    toCardinalNaturalPeano newQuotient CardinalNatural.Peano.zero =
      toCardinalNaturalPeano quotient CardinalNatural.Peano.zero *
        CardinalNatural.Peano.ten + qDigit.val := by
  dsimp only
  by_cases h_empty : Sequences.List.isEmpty quotient = true
  · rw [if_pos h_empty]
    have hq_zero := toCardinalNaturalPeano_eq_zero_of_isEmpty h_empty
    by_cases h_digit_zero : qDigit.val = CardinalNatural.Peano.zero
    · rw [if_pos h_digit_zero, hq_zero, h_digit_zero,
        CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.add_zero]
    · rw [if_neg h_digit_zero, hq_zero, CardinalNatural.Peano.zero_multiply,
        CardinalNatural.Peano.zero_add]
      simp [toCardinalNaturalPeano]
  · rw [if_neg h_empty, toCardinalNaturalPeano_append]

theorem divideWithRemainderAux_step_algebra
    (q div rem qDigit nextRem d pow tail newQ : CardinalNatural.Peano)
    (hstep : rem * CardinalNatural.Peano.ten + d = div * qDigit + nextRem)
    (hq : newQ = q * CardinalNatural.Peano.ten + qDigit) :
    (q * div + rem) * (CardinalNatural.Peano.ten * pow) +
        (d * pow + tail) =
      (newQ * div + nextRem) * pow + tail := by
  rw [hq]
  calc
    (q * div + rem) * (CardinalNatural.Peano.ten * pow) + (d * pow + tail) =
        (q * div) * (CardinalNatural.Peano.ten * pow) +
          (rem * (CardinalNatural.Peano.ten * pow) + (d * pow + tail)) := by
      rw [CardinalNatural.Peano.multiply_distributive_over_add_left,
        CardinalNatural.Peano.add_associative]
    _ = (q * div) * (CardinalNatural.Peano.ten * pow) +
          ((rem * CardinalNatural.Peano.ten) * pow + (d * pow + tail)) := by
      rw [← CardinalNatural.Peano.multiply_associative rem
        CardinalNatural.Peano.ten pow]
    _ = (q * div) * (CardinalNatural.Peano.ten * pow) +
          ((rem * CardinalNatural.Peano.ten) * pow + d * pow + tail) := by
      rw [← CardinalNatural.Peano.add_associative
        ((rem * CardinalNatural.Peano.ten) * pow) (d * pow) tail]
    _ = (q * div) * (CardinalNatural.Peano.ten * pow) +
          ((rem * CardinalNatural.Peano.ten + d) * pow + tail) := by
      rw [← CardinalNatural.Peano.multiply_distributive_over_add_left
        (rem * CardinalNatural.Peano.ten) d pow]
    _ = (q * div) * (CardinalNatural.Peano.ten * pow) +
          ((div * qDigit + nextRem) * pow + tail) := by
      rw [hstep]
    _ = (q * div) * (CardinalNatural.Peano.ten * pow) +
          ((div * qDigit) * pow + nextRem * pow + tail) := by
      rw [CardinalNatural.Peano.multiply_distributive_over_add_left,
        ← CardinalNatural.Peano.add_associative]
    _ = ((q * CardinalNatural.Peano.ten) * div) * pow +
          ((qDigit * div) * pow + nextRem * pow + tail) := by
      rw [← CardinalNatural.Peano.multiply_associative (q * div)
          CardinalNatural.Peano.ten pow,
        CardinalNatural.Peano.multiply_associative q div
          CardinalNatural.Peano.ten,
        CardinalNatural.Peano.multiply_commutative div
          CardinalNatural.Peano.ten,
        ← CardinalNatural.Peano.multiply_associative q
          CardinalNatural.Peano.ten div,
        CardinalNatural.Peano.multiply_commutative div qDigit]
    _ = (((q * CardinalNatural.Peano.ten) * div) * pow +
          (qDigit * div) * pow) + (nextRem * pow + tail) := by
      rw [CardinalNatural.Peano.add_associative
          ((qDigit * div) * pow) (nextRem * pow) tail,
        ← CardinalNatural.Peano.add_associative
          (((q * CardinalNatural.Peano.ten) * div) * pow)
          ((qDigit * div) * pow) (nextRem * pow + tail)]
    _ = (((q * CardinalNatural.Peano.ten) * div + qDigit * div) * pow) +
          (nextRem * pow + tail) := by
      rw [← CardinalNatural.Peano.multiply_distributive_over_add_left
        ((q * CardinalNatural.Peano.ten) * div) (qDigit * div) pow]
    _ = (((q * CardinalNatural.Peano.ten) * div + qDigit * div) * pow +
          nextRem * pow) + tail := by
      rw [← CardinalNatural.Peano.add_associative]
    _ = (((q * CardinalNatural.Peano.ten) * div + qDigit * div) +
          nextRem) * pow + tail := by
      rw [← CardinalNatural.Peano.multiply_distributive_over_add_left]
    _ = ((q * CardinalNatural.Peano.ten + qDigit) * div + nextRem) *
          pow + tail := by
      rw [← CardinalNatural.Peano.multiply_distributive_over_add_left]

theorem divideWithRemainderAux_spec
  (dividend divisor remainder quotient : Sequences.List Decimal)
  (hrem : toCardinalNaturalPeano remainder CardinalNatural.Peano.zero <
            toCardinalNaturalPeano divisor CardinalNatural.Peano.zero) :
  let result := divideWithRemainderAux dividend divisor remainder quotient
  let q := result.1
  let r := result.2
  (toCardinalNaturalPeano quotient CardinalNatural.Peano.zero *
      toCardinalNaturalPeano divisor CardinalNatural.Peano.zero +
     toCardinalNaturalPeano remainder CardinalNatural.Peano.zero) *
      CardinalNatural.Peano.tenPow dividend.length +
    toCardinalNaturalPeano dividend CardinalNatural.Peano.zero =
  toCardinalNaturalPeano divisor CardinalNatural.Peano.zero *
      toCardinalNaturalPeano q CardinalNatural.Peano.zero +
    toCardinalNaturalPeano r CardinalNatural.Peano.zero
  ∧
  toCardinalNaturalPeano r CardinalNatural.Peano.zero <
    toCardinalNaturalPeano divisor CardinalNatural.Peano.zero := by
  induction dividend generalizing remainder quotient with
  | empty =>
      dsimp [divideWithRemainderAux, toCardinalNaturalPeano, Sequences.List.length,
        CardinalNatural.Peano.tenPow]
      constructor
      · rw [CardinalNatural.Peano.multiply_one,
          CardinalNatural.Peano.multiply_commutative
            (toCardinalNaturalPeano quotient CardinalNatural.Peano.zero)
            (toCardinalNaturalPeano divisor CardinalNatural.Peano.zero)]
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
          if qDigit.val = CardinalNatural.Peano.zero then quotient
          else Sequences.List.firstElement qDigit Sequences.List.empty
        else Sequences.List.append quotient qDigit
      have h_newRem_value :
          toCardinalNaturalPeano newRem CardinalNatural.Peano.zero =
            toCardinalNaturalPeano remainder CardinalNatural.Peano.zero *
              CardinalNatural.Peano.ten + d.val := by
        dsimp [newRem]
        exact toCardinalNaturalPeano_append remainder d
      have h_newRem_bound :
          toCardinalNaturalPeano newRem CardinalNatural.Peano.zero <
            toCardinalNaturalPeano divisor CardinalNatural.Peano.zero *
              CardinalNatural.Peano.ten := by
        rw [h_newRem_value]
        have h1 :
            toCardinalNaturalPeano remainder CardinalNatural.Peano.zero *
                CardinalNatural.Peano.ten + d.val <
              toCardinalNaturalPeano remainder CardinalNatural.Peano.zero *
                CardinalNatural.Peano.ten + CardinalNatural.Peano.ten :=
          CardinalNatural.Peano.add_lt_add_left d.property
            (toCardinalNaturalPeano remainder CardinalNatural.Peano.zero *
              CardinalNatural.Peano.ten)
        have h2 :
            toCardinalNaturalPeano remainder CardinalNatural.Peano.zero *
                CardinalNatural.Peano.ten + CardinalNatural.Peano.ten =
              (toCardinalNaturalPeano remainder CardinalNatural.Peano.zero).successor *
                CardinalNatural.Peano.ten :=
          (CardinalNatural.Peano.successor_multiply
            (toCardinalNaturalPeano remainder CardinalNatural.Peano.zero)
            CardinalNatural.Peano.ten).symm
        have h3 :
            (toCardinalNaturalPeano remainder CardinalNatural.Peano.zero).successor *
                CardinalNatural.Peano.ten ≤
              toCardinalNaturalPeano divisor CardinalNatural.Peano.zero *
                CardinalNatural.Peano.ten :=
          CardinalNatural.Peano.multiply_le_mul_left
            (CardinalNatural.Peano.succ_le_of_lt hrem)
            CardinalNatural.Peano.ten
        rw [h2] at h1
        exact CardinalNatural.Peano.lt_of_lt_of_le h1 h3
      have h_digit_spec := findQuotientDigit_spec newRem divisor h_newRem_bound
      dsimp [qr, qDigit, nextRem] at h_digit_spec
      obtain ⟨h_digit_eq, h_nextRem_lt⟩ := h_digit_spec
      have h_newQuotient_value :
          toCardinalNaturalPeano newQuotient CardinalNatural.Peano.zero =
            toCardinalNaturalPeano quotient CardinalNatural.Peano.zero *
              CardinalNatural.Peano.ten + qDigit.val := by
        dsimp [newQuotient]
        exact divideWithRemainderAux_newQuotient_value quotient qDigit
      have h_step :
          toCardinalNaturalPeano remainder CardinalNatural.Peano.zero *
              CardinalNatural.Peano.ten + d.val =
            toCardinalNaturalPeano divisor CardinalNatural.Peano.zero * qDigit.val +
              toCardinalNaturalPeano nextRem CardinalNatural.Peano.zero := by
        rw [← h_newRem_value]
        exact h_digit_eq
      have ih_spec := ih nextRem newQuotient h_nextRem_lt
      dsimp [newQuotient, nextRem, qDigit, qr] at ih_spec
      obtain ⟨ih_eq, ih_lt⟩ := ih_spec
      constructor
      · rw [toCardinalNaturalPeano_firstElement]
        simp only [Sequences.List.length]
        rw [CardinalNatural.Peano.tenPow_add_one]
        have h_alg := divideWithRemainderAux_step_algebra
          (toCardinalNaturalPeano quotient CardinalNatural.Peano.zero)
          (toCardinalNaturalPeano divisor CardinalNatural.Peano.zero)
          (toCardinalNaturalPeano remainder CardinalNatural.Peano.zero)
          qDigit.val
          (toCardinalNaturalPeano nextRem CardinalNatural.Peano.zero)
          d.val
          (CardinalNatural.Peano.tenPow ds.length)
          (toCardinalNaturalPeano ds CardinalNatural.Peano.zero)
          (toCardinalNaturalPeano newQuotient CardinalNatural.Peano.zero)
          h_step h_newQuotient_value
        exact h_alg.trans ih_eq
      · exact ih_lt

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

theorem normalizeList_cons_zero (d : Decimal) (ds : Sequences.List Decimal)
    (hd : d.val = CardinalNatural.Peano.zero) (hds : ds ≠ Sequences.List.empty) :
    normalizeList (Sequences.List.firstElement d ds) (by simp) = normalizeList ds hds := by
  cases ds with
  | empty =>
      exact False.elim (hds rfl)
  | firstElement d' ds' =>
      simp [normalizeList, hd]

theorem toCardinalNaturalPeano_zero_of_allZero {a : Sequences.List Decimal}
    (h : AllZero a) :
    toCardinalNaturalPeano a CardinalNatural.Peano.zero = CardinalNatural.Peano.zero := by
  induction a with
  | empty => rfl
  | firstElement d ds ih =>
      change toCardinalNaturalPeano ds
          (CardinalNatural.Peano.zero * CardinalNatural.Peano.ten + d.val) = _
      have hd : d.val = CardinalNatural.Peano.zero := h.1
      rw [hd, CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.zero_add]
      exact ih h.2

theorem toCardinalNaturalPeano_normalizeList (a : Sequences.List Decimal)
    (ha : a ≠ Sequences.List.empty) :
    toCardinalNaturalPeano (normalizeList a ha).val CardinalNatural.Peano.zero =
      toCardinalNaturalPeano a CardinalNatural.Peano.zero := by
  induction a with
  | empty =>
      exact False.elim (ha rfl)
  | firstElement d ds ih =>
      by_cases hd : d.val = CardinalNatural.Peano.zero
      · by_cases hds : ds = Sequences.List.empty
        · subst hds
          simp [normalizeList, hd, toCardinalNaturalPeano,
            CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.add_zero]
        · have hnorm :
              normalizeList (Sequences.List.firstElement d ds) (by simp) =
                normalizeList ds hds := by
            simp [normalizeList, hd, hds]
          rw [hnorm, ih hds]
          change toCardinalNaturalPeano ds CardinalNatural.Peano.zero =
            toCardinalNaturalPeano ds
              (CardinalNatural.Peano.zero * CardinalNatural.Peano.ten + d.val)
          rw [hd, CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.add_zero]
      · have hnorm :
            normalizeList (Sequences.List.firstElement d ds) (by simp) =
              ⟨Sequences.List.firstElement d ds, by simp⟩ := by
          simp [normalizeList, hd]
        rw [hnorm]

theorem allZero_or_hasNonZero (a : Sequences.List Decimal) : AllZero a ∨ HasNonZero a := by
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

theorem not_allZero_of_hasNonZero {a : Sequences.List Decimal} (h : HasNonZero a) :
    ¬ AllZero a := by
  intro h_zero
  induction h with
  | first d ds hd => exact hd h_zero.1
  | notFirst d ds _ ih => exact ih h_zero.2

theorem toCardinalNaturalPeano_ne_zero_of_hasNonZero (a : Sequences.List Decimal)
    (acc : CardinalNatural.Peano) (h : HasNonZero a) :
    toCardinalNaturalPeano a acc ≠ CardinalNatural.Peano.zero := by
  induction h generalizing acc with
  | first d ds hd =>
      exact toCardinalNaturalPeano_ne_zero_of_acc_ne_zero ds
        (acc * CardinalNatural.Peano.ten + d.val)
        (CardinalNatural.Peano.add_ne_zero_of_right_ne_zero
          (acc * CardinalNatural.Peano.ten) d.val hd)
  | notFirst d ds _ ih =>
      exact ih (acc * CardinalNatural.Peano.ten + d.val)

theorem toCardinalNaturalPeano_ne_zero_of_not_allZero {a : Sequences.List Decimal}
    (h : ¬ AllZero a) :
    toCardinalNaturalPeano a CardinalNatural.Peano.zero ≠ CardinalNatural.Peano.zero := by
  induction a with
  | empty => exact False.elim (h trivial)
  | firstElement d ds ih =>
      change toCardinalNaturalPeano ds
          (CardinalNatural.Peano.zero * CardinalNatural.Peano.ten + d.val) ≠
        CardinalNatural.Peano.zero
      rw [CardinalNatural.Peano.zero_multiply, CardinalNatural.Peano.zero_add]
      by_cases hd : d.val = CardinalNatural.Peano.zero
      · have hds : ¬ AllZero ds := by
          intro hds
          exact h ⟨hd, hds⟩
        rw [hd]
        exact ih hds
      · exact toCardinalNaturalPeano_ne_zero_of_acc_ne_zero ds d.val hd

theorem hasNonZero_of_toCardinalNaturalPeano_ne_zero {l : Sequences.List Decimal}
    (h : toCardinalNaturalPeano l CardinalNatural.Peano.zero ≠ CardinalNatural.Peano.zero) :
    HasNonZero l := by
  cases allZero_or_hasNonZero l with
  | inl h_zero => exact absurd (toCardinalNaturalPeano_zero_of_allZero h_zero) h
  | inr h_nz => exact h_nz

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

theorem predecessorList_successorList (a : Sequences.List Decimal) :
    predecessorList (successorList a).1 = ⟨a, (successorList a).2⟩ := by
  induction a with
  | empty => rfl
  | firstElement d ds ih =>
      unfold successorList
      cases h_successor : successorList ds with
      | mk digits carry =>
          rw [h_successor] at ih
          cases carry with
          | false =>
              simp_all [predecessorList]
          | true =>
              by_cases hlt :
                  CardinalNatural.Peano.isLessThan d.val.successor CardinalNatural.Peano.ten = true
              · simp [hlt, predecessorList] at ih ⊢
                simp_all
                exact Subtype.ext rfl
              · have hfalse :
                    CardinalNatural.Peano.isLessThan d.val.successor CardinalNatural.Peano.ten =
                      false := by
                  cases h : CardinalNatural.Peano.isLessThan d.val.successor
                      CardinalNatural.Peano.ten with
                  | false => rfl
                  | true => contradiction
                have hd : d.val = CardinalNatural.Peano.nine :=
                  digit_val_eq_nine_of_not_successor_lt_ten d hfalse
                simp [hfalse, predecessorList] at ih ⊢
                simp_all
                exact Subtype.ext hd.symm

theorem successor_carry_accumulator (accumulator : CardinalNatural.Peano) :
    accumulator.successor * CardinalNatural.Peano.ten + CardinalNatural.Peano.zero =
      (accumulator * CardinalNatural.Peano.ten + CardinalNatural.Peano.nine).successor := by
  rw [CardinalNatural.Peano.add_zero, CardinalNatural.Peano.successor_multiply]
  change accumulator * CardinalNatural.Peano.ten + CardinalNatural.Peano.ten =
    (accumulator * CardinalNatural.Peano.ten + CardinalNatural.Peano.nine).successor
  rfl

theorem successorList_toCardinalNaturalPeano (a : Sequences.List Decimal)
    (accumulator : CardinalNatural.Peano) :
    match successorList a with
    | ⟨digits, true⟩ =>
        toCardinalNaturalPeano digits accumulator.successor =
          (toCardinalNaturalPeano a accumulator).successor
    | ⟨digits, false⟩ =>
        toCardinalNaturalPeano digits accumulator =
          (toCardinalNaturalPeano a accumulator).successor := by
  induction a generalizing accumulator with
  | empty =>
      rfl
  | firstElement d ds ih =>
      unfold successorList
      dsimp only
      cases hds : successorList ds with
      | mk digits carry =>
          have ih' := ih (accumulator * CardinalNatural.Peano.ten + d.val)
          rw [hds] at ih'
          cases carry with
          | false =>
              dsimp only at ih' ⊢
              exact ih'
          | true =>
              dsimp only at ih'
              by_cases hlt :
                  CardinalNatural.Peano.isLessThan d.val.successor CardinalNatural.Peano.ten = true
              · simp [hlt]
                change toCardinalNaturalPeano digits
                    (accumulator * CardinalNatural.Peano.ten + d.val.successor) =
                  (toCardinalNaturalPeano ds
                    (accumulator * CardinalNatural.Peano.ten + d.val)).successor
                change toCardinalNaturalPeano digits
                    (accumulator * CardinalNatural.Peano.ten + d.val).successor =
                  (toCardinalNaturalPeano ds
                    (accumulator * CardinalNatural.Peano.ten + d.val)).successor at ih'
                exact ih'
              · have hfalse :
                    CardinalNatural.Peano.isLessThan d.val.successor CardinalNatural.Peano.ten =
                      false := by
                  cases h : CardinalNatural.Peano.isLessThan d.val.successor
                      CardinalNatural.Peano.ten with
                  | false => rfl
                  | true => contradiction
                simp [hfalse]
                change toCardinalNaturalPeano digits
                    (accumulator.successor * CardinalNatural.Peano.ten +
                      CardinalNatural.Peano.zero) =
                  (toCardinalNaturalPeano ds
                    (accumulator * CardinalNatural.Peano.ten + d.val)).successor
                have hd : d.val = CardinalNatural.Peano.nine :=
                  digit_val_eq_nine_of_not_successor_lt_ten d hfalse
                rw [hd]
                rw [successor_carry_accumulator]
                change toCardinalNaturalPeano digits
                    (accumulator * CardinalNatural.Peano.ten +
                      CardinalNatural.Peano.nine).successor =
                  (toCardinalNaturalPeano ds
                    (accumulator * CardinalNatural.Peano.ten +
                      CardinalNatural.Peano.nine)).successor
                rw [hd] at ih'
                exact ih'


theorem padAtStartToSameLength_fst_ne_empty (a b : Sequences.List Decimal) (paddingValue : Decimal)
    (ha : a ≠ Sequences.List.empty) :
    (Sequences.List.padAtStartToSameLength a b paddingValue).1 ≠ Sequences.List.empty :=
  Sequences.List.padAtStartToSameLength_fst_ne_empty a b paddingValue ha

theorem padAtStartToSameLength_fst_ne_empty_of_either
    (a b : Sequences.List Decimal) (paddingValue : Decimal)
    (h : a ≠ Sequences.List.empty ∨ b ≠ Sequences.List.empty) :
    (Sequences.List.padAtStartToSameLength a b paddingValue).1 ≠ Sequences.List.empty :=
  Sequences.List.padAtStartToSameLength_fst_ne_empty_of_either a b paddingValue h

theorem addAlignedLists_fst_ne_empty {a b : Sequences.List Decimal}
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

theorem addAlignedLists_ne_empty {a b digits : Sequences.List Decimal} {carry : Bool}
    (h : Sequences.List.SameLength a b) (ha : a ≠ Sequences.List.empty)
    (h_add : addAlignedLists a b h = ⟨digits, carry⟩) :
    digits ≠ Sequences.List.empty := by
  have h_fst := addAlignedLists_fst_ne_empty h ha
  rw [h_add] at h_fst
  exact h_fst

theorem subtractAlignedLists_fst_ne_empty {a b : Sequences.List Decimal}
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

theorem subtractAlignedLists_ne_empty {a b digits : Sequences.List Decimal} {borrow : Bool}
    (h : Sequences.List.SameLength a b) (ha : a ≠ Sequences.List.empty)
    (h_subtract : subtractAlignedLists a b h = ⟨digits, borrow⟩) :
    digits ≠ Sequences.List.empty := by
  have h_fst := subtractAlignedLists_fst_ne_empty h ha
  rw [h_subtract] at h_fst
  exact h_fst

theorem subtractAlignedLists_borrow_false_of_eq {a b : Sequences.List Decimal}
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
              have h_not : ¬ da.val < da.val := CardinalNatural.Peano.not_lt_self da.val
              simp [h_not]
          | true =>
              cases h_borrow

theorem multiplyPartialListByDigit_fst_ne_empty (a : Sequences.List Decimal) (b : Decimal)
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

theorem multiplyListByDigit_ne_empty (a : Sequences.List Decimal) (b : Decimal)
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

theorem multiplyList_fst_ne_empty (a b : Sequences.List Decimal)
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
            Sequences.List.padAtEnd_ne_empty digitProduct zeroDigit shift h_digitProduct_ne
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

theorem hasNonZero_of_hasNonZero_bool {digits : Sequences.List Decimal}
    (h : hasNonZero digits = true) : HasNonZero digits :=
  (Sequences.List.anyElement_decide_eq_true_iff DigitIsNonZero digits).mp h

theorem hasNonZero_bool_eq_true_of_hasNonZero {digits : Sequences.List Decimal}
    (h : HasNonZero digits) : hasNonZero digits = true :=
  (Sequences.List.anyElement_decide_eq_true_iff DigitIsNonZero digits).mpr h

theorem allZero_of_not_hasNonZero_bool {l : Sequences.List Decimal}
    (h : ¬ hasNonZero l = true) : AllZero l := by
  cases allZero_or_hasNonZero l with
  | inl h_zero => exact h_zero
  | inr h_nonzero =>
      exact False.elim (h (hasNonZero_bool_eq_true_of_hasNonZero h_nonzero))

theorem hasNonZero_of_successorList_carry_true {a digits : Sequences.List Decimal}
    (_ : successorList a = ⟨digits, true⟩) :
    HasNonZero (Sequences.List.firstElement
      ⟨CardinalNatural.Peano.one, CardinalNatural.Peano.one_lt_ten⟩ digits) := by
  apply Sequences.List.AnyElement.first
  intro h1
  cases h1

theorem hasNonZero_of_successorList_carry_false {a digits : Sequences.List Decimal}
    (h_nonzero : HasNonZero a) (h : successorList a = ⟨digits, false⟩) :
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

theorem hasNonZero_padAtStartToSameLength_fst (a b : Sequences.List Decimal)
    (paddingValue : Decimal) (h : HasNonZero a) :
    HasNonZero (Sequences.List.padAtStartToSameLength a b paddingValue).1 := by
  unfold Sequences.List.padAtStartToSameLength
  dsimp only
  split
  · exact h
  · exact Sequences.List.padAtStart_anyElement h paddingValue _

theorem addAlignedLists_digit_sum_ne_zero_of_left_ne_zero
    (da db : CardinalNatural.Peano) (carry : Bool)
    (hda : da ≠ CardinalNatural.Peano.zero) :
    da + db + (if carry then CardinalNatural.Peano.one else CardinalNatural.Peano.zero) ≠
      CardinalNatural.Peano.zero := by
  apply CardinalNatural.Peano.add_ne_zero_of_left_ne_zero
  exact CardinalNatural.Peano.add_ne_zero_of_left_ne_zero da db hda

theorem addAlignedLists_digit_sum_ne_zero_of_carry_true
    (da db : CardinalNatural.Peano) :
    da + db + CardinalNatural.Peano.one ≠ CardinalNatural.Peano.zero := by
  exact CardinalNatural.Peano.add_ne_zero_of_right_ne_zero (da + db) CardinalNatural.Peano.one
    (CardinalNatural.Peano.successor_ne_zero CardinalNatural.Peano.zero)

theorem hasNonZero_of_addAlignedLists_carry_true {a b digits : Sequences.List Decimal}
    {h : Sequences.List.SameLength a b} (_ : addAlignedLists a b h = ⟨digits, true⟩) :
    HasNonZero (Sequences.List.firstElement
      ⟨CardinalNatural.Peano.one, CardinalNatural.Peano.one_lt_ten⟩ digits) := by
  apply Sequences.List.AnyElement.first
  exact CardinalNatural.Peano.successor_ne_zero CardinalNatural.Peano.zero

theorem hasNonZero_of_addAlignedLists_carry_false {a b digits : Sequences.List Decimal}
    (h : Sequences.List.SameLength a b) (h_nonzero : HasNonZero a)
    (h_add : addAlignedLists a b h = ⟨digits, false⟩) :
    HasNonZero digits := by
  induction h using Sequences.List.SameLength.induction generalizing digits with
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


theorem hasNonZero_of_subtractAlignedLists_borrow_true {a b digits : Sequences.List Decimal}
    (h_same : Sequences.List.SameLength a b)
    (h_subtract : subtractAlignedLists a b h_same = ⟨digits, true⟩) :
    HasNonZero digits := by
  induction h_same using Sequences.List.SameLength.induction generalizing digits with
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

theorem hasNonZero_of_subtractAlignedLists_borrow_false_of_lessThan {a b digits : Sequences.List Decimal}
    (h_same : Sequences.List.SameLength a b)
    (h_lt : LessThanAlignedLists b a (Sequences.List.sameLength_commutative h_same))
    (h_subtract : subtractAlignedLists a b h_same = ⟨digits, false⟩) :
    HasNonZero digits := by
  induction h_same using Sequences.List.SameLength.induction generalizing digits with
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

theorem hasNonZero_multiplyList (a b : Sequences.List Decimal)
    (ha : HasNonZero a) (hb : HasNonZero b) :
    HasNonZero (multiplyList a b).1 := by
  apply hasNonZero_of_toCardinalNaturalPeano_ne_zero
  rw [(multiplyList_spec a b).2]
  exact CardinalNatural.Peano.multiply_ne_zero _ _
    (toCardinalNaturalPeano_ne_zero_of_hasNonZero a CardinalNatural.Peano.zero ha)
    (toCardinalNaturalPeano_ne_zero_of_hasNonZero b CardinalNatural.Peano.zero hb)

end ZeroMath.Numbers.Digits
