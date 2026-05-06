import ZeroMath.Numbers.OrdinalNatural

open ZeroMath.Numbers.OrdinalNatural.Peano
open ZeroMath.Numbers.OrdinalNatural

theorem add_subtract_assoc (a b c : Peano) (h : b > c) : ∃ h2, subtract (a + b) c h2 = a + subtract b c h := by
  have h2 : c < a + b := lt_trans h (lt_add_right (a) b)
  refine ⟨h2, ?_⟩
  have h3 : subtract (a + b) c h2 + c = (a + subtract b c h) + c := by
    rw [subtract_add_cancel (a + b) c h2, add_assoc a (subtract b c h) c, subtract_add_cancel b c h]
  exact add_cancel_right (subtract (a + b) c h2) (a + subtract b c h) c h3
