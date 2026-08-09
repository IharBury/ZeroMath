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

def HasNonZero := Sequences.List.AnyElement DigitIsNonZero

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
