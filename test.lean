import ZeroMath.Numbers.OrdinalNatural
open ZeroMath.Numbers.OrdinalNatural
open ZeroMath.Numbers.OrdinalNatural.Peano

theorem divide_add_distrib_h (x y z : Peano) (h1 : isDivisible x z) (h2 : isDivisible y z) :
  isDivisible (x + y) z := by
  rcases h1 with ⟨c1, hc1⟩
  rcases h2 with ⟨c2, hc2⟩
  exact ⟨c1 + c2, by rw [multiply_add, hc1, hc2]⟩

theorem divide_add_distrib (x y z : Peano) (h1 : isDivisible x z) (h2 : isDivisible y z) :
  ∃ h3, divide (x + y) z h3 = divide x z h1 + divide y z h2 := by
  have h3 := divide_add_distrib_h x y z h1 h2
  refine ⟨h3, ?_⟩
  have H1 := divide_correct x z h1
  have H2 := divide_correct y z h2
  have H3 := divide_correct (x + y) z h3

  have H4 : z * (divide x z h1 + divide y z h2) = z * divide x z h1 + z * divide y z h2 := multiply_add z _ _
  rw [H1, H2] at H4
  have H5 : z * divide (x + y) z h3 = z * (divide x z h1 + divide y z h2) := by
    rw [H3, ←H4]
  exact multiply_cancel_left z _ _ H5
