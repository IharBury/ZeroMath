import ZeroMath

open ZeroMath.Numbers.OrdinalNatural

theorem divide_add (x y z : Peano) (h : Peano.isDivisible x z) (h2 : Peano.isDivisible y z) :
  ∃ h3, Peano.divide x z h + Peano.divide y z h2 = Peano.divide (x + y) z h3 := by
  have h3 : Peano.isDivisible (x + y) z := by
    cases h with
    | intro c1 hc1 =>
      cases h2 with
      | intro c2 hc2 =>
        exists c1 + c2
        rw [Peano.multiply_add, hc1, hc2]
  exists h3
  have h4 : z * (Peano.divide x z h + Peano.divide y z h2) = z * Peano.divide (x + y) z h3 := by
    rw [Peano.multiply_add, Peano.divide_correct, Peano.divide_correct, Peano.divide_correct]
  exact Peano.multiply_cancel_left z _ _ h4
