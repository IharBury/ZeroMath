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

def normalizeList (a : Sequences.List CardinalNatural.Peano) (h : AllLessThanTen a ∧ HasNonZero a) : Decimal :=
  match a with
  | .empty => False.elim sorry
  | .firstElement d ds =>
    if h2 : d = CardinalNatural.Peano.zero then
      normalizeList ds sorry
    else
      ⟨Sequences.List.firstElement d ds, h⟩

def normalize (a : Decimal) : Decimal :=
  normalizeList a.val a.property

theorem normalize_isNormalized (d : Decimal) :
  isNormalized (normalize d) = true := by
  sorry

def toCardinalList (a : Sequences.List CardinalNatural.Peano) (h : AllLessThanTen a) (acc : CardinalNatural.Peano) : CardinalNatural.Peano :=
  match a with
  | .empty => acc
  | .firstElement d ds => toCardinalList ds sorry (acc * CardinalNatural.Peano.ten + d)

def toCardinalPeano (a : Decimal) : CardinalNatural.Peano :=
  toCardinalList a.val a.property.1 CardinalNatural.Peano.zero

def toPeano (a : Decimal) : OrdinalNatural.Peano :=
  (toCardinalPeano a).toOrdinal sorry

theorem normalize_toPeano (x : Decimal) : x.normalize.toPeano = x.toPeano := by
  sorry

def Equivalent (a b : Decimal) : Prop :=
  normalize a = normalize b

instance instSetoid : Setoid Decimal where
  r := Equivalent
  iseqv := {
    refl := by
      intro a
      rfl
    symm := by
      intro a b h
      exact h.symm
    trans := by
      intro a b c hab hbc
      exact Eq.trans hab hbc
  }

theorem Equivalent_iff_normalize_eq (a b : Decimal) :
  Equivalent a b ↔ normalize a = normalize b := by
  rfl

theorem equivalent_of_normalize_eq {a b : Decimal}
  (h : normalize a = normalize b) : a ≈ b := by
  exact h

theorem normalize_eq_of_equivalent {a b : Decimal}
  (h : instSetoid.r a b) : normalize a = normalize b := by
  exact h

theorem toPeano_eq_of_equivalent {a b : Decimal} (h : a ≈ b) :
  a.toPeano = b.toPeano := by
  rw [← normalize_toPeano a, ← normalize_toPeano b]
  have h_norm : normalize a = normalize b := h
  rw [h_norm]

def successorList (a : Sequences.List CardinalNatural.Peano) (h : AllLessThanTen a) :
  { b : Sequences.List CardinalNatural.Peano // AllLessThanTen b} × Bool :=
  match a with
  | .empty => ⟨⟨Sequences.List.empty, sorry⟩, true⟩
  | .firstElement d ds =>
    let ⟨⟨digits, h2⟩, carry⟩ := successorList ds sorry
    if h2 : carry then
      if h3 : CardinalNatural.Peano.isLessThan d.successor CardinalNatural.Peano.ten then
        ⟨⟨Sequences.List.firstElement d.successor digits, sorry⟩, false⟩
      else
        ⟨⟨Sequences.List.firstElement CardinalNatural.Peano.zero digits, sorry⟩, true⟩
    else
      ⟨⟨Sequences.List.firstElement d digits, sorry⟩, false⟩

def successor (a : Decimal) : Decimal :=
  let ⟨⟨digits, h⟩, carry⟩ := successorList a.1 a.2.1
  if h2 : carry then
    ⟨Sequences.List.firstElement CardinalNatural.Peano.one digits, sorry⟩
  else
    ⟨digits, sorry⟩

def one : Decimal :=
  ⟨Sequences.List.firstElement CardinalNatural.Peano.one Sequences.List.empty, ⟨by
    unfold AllLessThanTen
    constructor
    · exact CardinalNatural.Peano.LessThan.step (CardinalNatural.Peano.LessThan.step (CardinalNatural.Peano.LessThan.step
        (CardinalNatural.Peano.LessThan.step (CardinalNatural.Peano.LessThan.step (CardinalNatural.Peano.LessThan.step (CardinalNatural.Peano.LessThan.step
          (CardinalNatural.Peano.LessThan.step (CardinalNatural.Peano.LessThan.base))))))))
    · exact trivial
  , by
    unfold HasNonZero
    left
    intro contra
    cases contra
  ⟩⟩

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

def addAlignedLists (a b : Sequences.List CardinalNatural.Peano) (h : Sequences.List.SameLength a b ∧ AllLessThanTen a ∧ AllLessThanTen b) :
  {c : Sequences.List CardinalNatural.Peano // AllLessThanTen c} × Bool :=
  match a, b with
  | .empty, .empty => ⟨⟨Sequences.List.empty, sorry⟩, false⟩
  | .firstElement da das, .firstElement db dbs =>
    let ⟨⟨digits, h2⟩, carry⟩ := addAlignedLists das dbs sorry
    let digit_sum := da + db + (if carry then CardinalNatural.Peano.one else CardinalNatural.Peano.zero)
    if h2 : CardinalNatural.Peano.isLessThan digit_sum CardinalNatural.Peano.ten then
      ⟨⟨Sequences.List.firstElement digit_sum digits, sorry⟩, false⟩
    else
      ⟨⟨Sequences.List.firstElement (CardinalNatural.Peano.subtract digit_sum CardinalNatural.Peano.ten sorry) digits, sorry⟩, true⟩
  | _, _ => False.elim sorry

def add (a b : Decimal) : Decimal :=
  let pair := Sequences.List.padAtStartToSameLength a.val b.val CardinalNatural.Peano.zero
  let ⟨⟨digits, h⟩, carry⟩ := addAlignedLists pair.1 pair.2 sorry
  if carry then
    ⟨Sequences.List.firstElement CardinalNatural.Peano.one digits, sorry⟩
  else
    ⟨digits, sorry⟩

instance : Add Decimal where
  add := add

theorem cardinal_lt_toNat {a b : CardinalNatural.Peano} (h : a < b) :
  a.toNat < b.toNat := by
  induction h with
  | base =>
    simp [CardinalNatural.Peano.toNat]
  | step _ ih =>
    exact Nat.lt_succ_of_lt ih

theorem equivalent_of_toPeano_eq {a b : Decimal} (h : a.toPeano = b.toPeano) : a ≈ b := by
  sorry

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

theorem add_toPeano (x y : Decimal) :
  (x + y).toPeano = x.toPeano + y.toPeano := by
  sorry

theorem add_commutative (a b : Decimal) : a + b = b + a := by
  sorry

theorem equivalent_add_commutative (a b : Decimal) : a + b ≈ b + a := by
  rw [add_commutative]
  rfl

def fromPeano : Peano → Decimal
  | Peano.one => Decimal.one
  | Peano.successor p => successor (fromPeano p)

theorem toPeano_fromPeano (x : Peano) :
  toPeano (fromPeano x) = x := by
  sorry

theorem nine_lt_ten : CardinalNatural.Peano.nine < CardinalNatural.Peano.ten := CardinalNatural.Peano.LessThan.base

def predecessorList (a : Sequences.List CardinalNatural.Peano) (h : AllLessThanTen a) :
  {b : Sequences.List CardinalNatural.Peano // AllLessThanTen b} × Bool :=
  match a with
  | .empty => ⟨⟨Sequences.List.empty, sorry⟩, true⟩
  | .firstElement d ds =>
    let ⟨⟨digits, h2⟩, borrow⟩ := predecessorList ds sorry
    if borrow then
      match d with
      | .zero => ⟨⟨Sequences.List.firstElement CardinalNatural.Peano.nine digits, sorry⟩, true⟩
      | .successor d' => ⟨⟨Sequences.List.firstElement d' digits, sorry⟩, false⟩
    else
      ⟨⟨Sequences.List.firstElement d digits, sorry⟩, false⟩

def predecessor (a : Decimal) (h : ¬ a ≈ one) : Decimal :=
  let ⟨⟨digits, h2⟩, borrow⟩ := predecessorList a.val a.property.1
  if h3: borrow then
    False.elim sorry
  else
    ⟨digits, sorry⟩

theorem successor_predecessor_val (d : Decimal) (h : ¬ Equivalent d Decimal.one) :
  (d.predecessor h).successor.val = d.val := by
  sorry

theorem successor_toPeano (x : Decimal) :
  x.successor.toPeano = x.toPeano.successor := by
  sorry

theorem peano_predecessor_congr {a b : OrdinalNatural.Peano}
  (ha : a ≠ OrdinalNatural.Peano.one) (hb : b ≠ OrdinalNatural.Peano.one)
  (h_eq : a = b) : a.predecessor ha = b.predecessor hb := by
  cases h_eq
  rfl

theorem predecessor_toPeano (x : Decimal) (h : ¬ Equivalent x Decimal.one) :
  ∃ h2, (x.predecessor h).toPeano = x.toPeano.predecessor h2 := by
  sorry

def LessThan (x y : Decimal) : Prop := x.toPeano < y.toPeano

instance : LT Decimal where
  lt := LessThan

def LessThanOrEquivalent (x y : Decimal) : Prop := x < y ∨ x ≈ y

instance : LE Decimal where
  le := LessThanOrEquivalent

theorem lt_trans {a b c : Decimal} (h1 : a < b) (h2 : b < c) : a < c := by
  have h1' : a.toPeano < b.toPeano := h1
  have h2' : b.toPeano < c.toPeano := h2
  exact Peano.lt_trans h1' h2'

theorem le_trans {a b c : Decimal} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  have h1' : a < b ∨ a ≈ b := h1
  have h2' : b < c ∨ b ≈ c := h2
  cases h1' with
  | inl h1_lt =>
    cases h2' with
    | inl h2_lt =>
      left
      exact Decimal.lt_trans h1_lt h2_lt
    | inr h2_eq =>
      left
      have hab : a.toPeano < b.toPeano := h1_lt
      have hbc : b.toPeano = c.toPeano := by
        rw [← normalize_toPeano b, ← normalize_toPeano c]
        have heq : normalize b = normalize c := h2_eq
        rw [heq]
      have hac : a.toPeano < c.toPeano := by
        rw [← hbc]
        exact hab
      exact hac
  | inr h1_eq =>
    cases h2' with
    | inl h2_lt =>
      left
      have hab : a.toPeano = b.toPeano := by
        rw [← normalize_toPeano a, ← normalize_toPeano b]
        have heq : normalize a = normalize b := h1_eq
        rw [heq]
      have hbc : b.toPeano < c.toPeano := h2_lt
      have hac : a.toPeano < c.toPeano := by
        rw [hab]
        exact hbc
      exact hac
    | inr h2_eq =>
      right
      have hab : normalize a = normalize b := h1_eq
      have hbc : normalize b = normalize c := h2_eq
      exact Eq.trans hab hbc

theorem not_lt_of_equivalent {a b : Decimal} (h : a ≈ b) : ¬ a < b := by
  intro hlt
  have h_eq := toPeano_eq_of_equivalent h
  have hlt_peano : a.toPeano < b.toPeano := hlt
  rw [h_eq] at hlt_peano
  exact Peano.not_lt_self b.toPeano hlt_peano

theorem not_equivalent_of_lt {a b : Decimal} (h : a < b) : ¬ a ≈ b := by
  intro h_eq
  exact not_lt_of_equivalent h_eq h

theorem not_gt_of_lt {a b : Decimal} (h : a < b) : ¬ b < a := by
  intro hba
  exact Peano.not_lt_of_lt h hba

theorem trichotomy (a b : Decimal) : ZeroMath.Logic.Trichotomy (a < b) (a ≈ b) (b < a) := by
  cases Peano.trichotomy a.toPeano b.toPeano with
  | first h_lt h_ne h_not_gt =>
    exact ZeroMath.Logic.Trichotomy.first h_lt (not_equivalent_of_lt h_lt) h_not_gt
  | second h_eq h_not_lt h_not_gt =>
    have h_equiv : a ≈ b := equivalent_of_toPeano_eq h_eq
    exact ZeroMath.Logic.Trichotomy.second h_equiv h_not_lt h_not_gt
  | third h_gt h_not_lt h_ne =>
    have h_not_equiv : ¬ a ≈ b := by
      intro h_equiv
      exact not_equivalent_of_lt h_gt h_equiv.symm
    exact ZeroMath.Logic.Trichotomy.third h_gt h_not_lt h_not_equiv

theorem add_associative (a b c : Decimal) : a + b + c ≈ a + (b + c) := by
  apply equivalent_of_toPeano_eq
  rw [add_toPeano, add_toPeano, add_toPeano, add_toPeano]
  exact ZeroMath.Numbers.OrdinalNatural.Peano.add_associative a.toPeano b.toPeano c.toPeano

theorem fromPeano_toPeano (x : Decimal) : fromPeano (toPeano x) ≈ x := by
  apply equivalent_of_toPeano_eq
  rw [toPeano_fromPeano]

def isLessThanAlignedLists (x y : Sequences.List CardinalNatural.Peano) (h : Sequences.List.SameLength x y) : Bool :=
  match x, y with
  | .empty, .empty => false
  | .firstElement dx dxs, .firstElement dy dys =>
    if CardinalNatural.Peano.isLessThan dx dy then
      true
    else if CardinalNatural.Peano.isLessThan dy dx then
      false
    else
      isLessThanAlignedLists dxs dys sorry
  | _, _ => False.elim sorry

def isLessThan (x y : Decimal) : Bool :=
  let pair := Sequences.List.padAtStartToSameLength x.val y.val CardinalNatural.Peano.zero
  isLessThanAlignedLists pair.1 pair.2 sorry

theorem cardinal_lt_of_toNat_lt {a b : CardinalNatural.Peano}
  (h : a.toNat < b.toNat) : a < b := by
  cases CardinalNatural.Peano.trichotomy_or a b with
  | inl hlt => exact hlt
  | inr hrest =>
    cases hrest with
    | inl heq =>
      rw [heq] at h
      exact False.elim (Nat.lt_irrefl _ h)
    | inr hgt =>
      have hgt_nat := cardinal_lt_toNat hgt
      exact False.elim (Nat.lt_asymm h hgt_nat)

theorem cardinal_lt_toOrdinal_iff {a b : CardinalNatural.Peano}
  (ha : a ≠ CardinalNatural.Peano.zero) (hb : b ≠ CardinalNatural.Peano.zero) :
  CardinalNatural.Peano.toOrdinal a ha < CardinalNatural.Peano.toOrdinal b hb ↔ a < b := by
  constructor
  · intro h
    cases a with
    | zero => contradiction
    | successor a' =>
      cases b with
      | zero => contradiction
      | successor b' =>
        cases a' with
        | zero =>
          cases b' with
          | zero =>
            unfold CardinalNatural.Peano.toOrdinal at h
            exact False.elim (Peano.not_lt_self Peano.one h)
          | successor b'' =>
            exact CardinalNatural.Peano.succ_lt_succ (CardinalNatural.Peano.zero_lt_succ _)
        | successor a'' =>
          cases b' with
          | zero =>
            unfold CardinalNatural.Peano.toOrdinal at h
            exact False.elim (Peano.not_lt_one _ h)
          | successor b'' =>
            unfold CardinalNatural.Peano.toOrdinal at h
            exact CardinalNatural.Peano.succ_lt_succ ((cardinal_lt_toOrdinal_iff _ _).mp (Peano.lt_of_succ_lt_succ h))
  · intro h
    cases a with
    | zero => contradiction
    | successor a' =>
      cases b with
      | zero => exact False.elim (CardinalNatural.Peano.not_lt_zero _ h)
      | successor b' =>
        cases a' with
        | zero =>
          cases b' with
          | zero =>
            exact False.elim (CardinalNatural.Peano.not_lt_self _ h)
          | successor b'' =>
            unfold CardinalNatural.Peano.toOrdinal
            exact Peano.one_lt_succ _
        | successor a'' =>
          cases b' with
          | zero =>
            have h_opp : CardinalNatural.Peano.zero.successor < a''.successor.successor := CardinalNatural.Peano.succ_lt_succ (CardinalNatural.Peano.zero_lt_succ _)
            exact False.elim (CardinalNatural.Peano.not_lt_of_lt h_opp h)
          | successor b'' =>
            unfold CardinalNatural.Peano.toOrdinal
            apply Peano.succ_lt_succ
            apply (cardinal_lt_toOrdinal_iff _ _).mpr
            exact CardinalNatural.Peano.lt_of_succ_lt_succ h

theorem isLessThan_eq_true_iff_lessThan (x y : Decimal) :
  isLessThan x y = true ↔ LessThan x y := by
  sorry

theorem isLessThan_iff_lessThan (x y : Decimal) :
  isLessThan x y ↔ LessThan x y := by
  exact isLessThan_eq_true_iff_lessThan x y

end Decimal

end ZeroMath.Numbers.OrdinalNatural
