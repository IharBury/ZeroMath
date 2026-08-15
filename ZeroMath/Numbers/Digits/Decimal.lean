import ZeroMath.Numbers.CardinalNatural.Peano

namespace ZeroMath.Numbers.Digits

/-- A base-10 digit: a cardinal Peano natural strictly less than ten. -/
def Decimal := { d : CardinalNatural.Peano // d < CardinalNatural.Peano.ten }

deriving instance DecidableEq for Decimal

def DigitIsNonZero (d : Decimal) : Prop := d.val ≠ CardinalNatural.Peano.zero

deriving instance Decidable for DigitIsNonZero

def zeroDigit : Decimal := ⟨CardinalNatural.Peano.zero, by decide⟩
def oneDigit : Decimal := ⟨CardinalNatural.Peano.one, by decide⟩
def twoDigit : Decimal := ⟨CardinalNatural.Peano.two, by decide⟩
def threeDigit : Decimal := ⟨CardinalNatural.Peano.three, by decide⟩
def fourDigit : Decimal := ⟨CardinalNatural.Peano.four, by decide⟩
def fiveDigit : Decimal := ⟨CardinalNatural.Peano.five, by decide⟩
def sixDigit : Decimal := ⟨CardinalNatural.Peano.six, by decide⟩
def sevenDigit : Decimal := ⟨CardinalNatural.Peano.seven, by decide⟩
def eightDigit : Decimal := ⟨CardinalNatural.Peano.eight, by decide⟩
def nineDigit : Decimal := ⟨CardinalNatural.Peano.nine, by decide⟩

theorem digit_val_successor_le_ten (d : Decimal) :
    d.val.successor ≤ CardinalNatural.Peano.ten :=
  CardinalNatural.Peano.successor_le_of_lt d.property

theorem digit_val_le_ten (d : Decimal) : d.val ≤ CardinalNatural.Peano.ten :=
  CardinalNatural.Peano.le_of_successor_le (digit_val_successor_le_ten d)

theorem digit_val_eq_nine_of_not_successor_lt_ten (d : Decimal)
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
                                                (CardinalNatural.Peano.lt_of_successor_lt_successor
                                                (CardinalNatural.Peano.lt_of_successor_lt_successor
                                                (CardinalNatural.Peano.lt_of_successor_lt_successor
                                                (CardinalNatural.Peano.lt_of_successor_lt_successor
                                                (CardinalNatural.Peano.lt_of_successor_lt_successor
                                                (CardinalNatural.Peano.lt_of_successor_lt_successor
                                                (CardinalNatural.Peano.lt_of_successor_lt_successor
                                                (CardinalNatural.Peano.lt_of_successor_lt_successor
                                                (CardinalNatural.Peano.lt_of_successor_lt_successor
                                                (CardinalNatural.Peano.lt_of_successor_lt_successor hval))))))))))
                                              exact False.elim
                                                ((CardinalNatural.Peano.not_lt_zero val10) hlt_zero)

theorem subtract_ten_lt_ten (digit_sum : CardinalNatural.Peano)
    (h_le : CardinalNatural.Peano.ten ≤ digit_sum)
    (h_lt_twenty : digit_sum < CardinalNatural.Peano.ten + CardinalNatural.Peano.ten) :
    CardinalNatural.Peano.subtract digit_sum CardinalNatural.Peano.ten h_le <
      CardinalNatural.Peano.ten :=
  CardinalNatural.Peano.subtract_lt_of_lt_add h_le h_lt_twenty

theorem digit_sum_lt_twenty (da db : CardinalNatural.Peano) (carry : Bool)
    (hda : da < CardinalNatural.Peano.ten) (hdb : db < CardinalNatural.Peano.ten) :
    da + db + (if carry then CardinalNatural.Peano.one else CardinalNatural.Peano.zero) <
      CardinalNatural.Peano.ten + CardinalNatural.Peano.ten := by
  cases carry with
  | false =>
      simp
      exact CardinalNatural.Peano.lt_trans
        (CardinalNatural.Peano.add_lt_add_right hda db)
        (CardinalNatural.Peano.add_lt_add_left hdb CardinalNatural.Peano.ten)
  | true =>
      have h_da_succ_le : da + CardinalNatural.Peano.one ≤ CardinalNatural.Peano.ten := by
        change da.successor ≤ CardinalNatural.Peano.ten
        exact CardinalNatural.Peano.successor_le_of_lt hda
      have h_sum_le :
          (da + CardinalNatural.Peano.one) + db ≤ CardinalNatural.Peano.ten + db :=
        CardinalNatural.Peano.add_le_add_right h_da_succ_le db
      have h_ten_db_lt :
          CardinalNatural.Peano.ten + db <
            CardinalNatural.Peano.ten + CardinalNatural.Peano.ten :=
        CardinalNatural.Peano.add_lt_add_left hdb CardinalNatural.Peano.ten
      simp
      rw [CardinalNatural.Peano.add_associative da db CardinalNatural.Peano.one]
      rw [CardinalNatural.Peano.add_commutative db CardinalNatural.Peano.one]
      rw [← CardinalNatural.Peano.add_associative da CardinalNatural.Peano.one db]
      exact CardinalNatural.Peano.le_lt_trans h_sum_le h_ten_db_lt

theorem digit_carry_lt_twenty (a : Decimal) (b : Decimal) :
    a.val + b.val < CardinalNatural.Peano.ten + CardinalNatural.Peano.ten := by
  have h := digit_sum_lt_twenty a.val b.val false a.property b.property
  have h2 :
      (if false = true then CardinalNatural.Peano.one else CardinalNatural.Peano.zero) =
        CardinalNatural.Peano.zero := rfl
  rw [h2] at h
  rw [CardinalNatural.Peano.add_zero] at h
  exact h

theorem digit_cases (d : Decimal) :
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
                                              have h1 := CardinalNatural.Peano.lt_of_successor_lt_successor h
                                              have h2 := CardinalNatural.Peano.lt_of_successor_lt_successor h1
                                              have h3 := CardinalNatural.Peano.lt_of_successor_lt_successor h2
                                              have h4 := CardinalNatural.Peano.lt_of_successor_lt_successor h3
                                              have h5 := CardinalNatural.Peano.lt_of_successor_lt_successor h4
                                              have h6 := CardinalNatural.Peano.lt_of_successor_lt_successor h5
                                              have h7 := CardinalNatural.Peano.lt_of_successor_lt_successor h6
                                              have h8 := CardinalNatural.Peano.lt_of_successor_lt_successor h7
                                              have h9 := CardinalNatural.Peano.lt_of_successor_lt_successor h8
                                              have h10 := CardinalNatural.Peano.lt_of_successor_lt_successor h9
                                              exact False.elim (CardinalNatural.Peano.not_lt_zero val10 h10)

end ZeroMath.Numbers.Digits
