import ZeroMath.Numbers.OrdinalNatural

namespace ZeroMath.Numbers.OrdinalNatural.Peano

theorem div_mul_eq_thm (x y : Peano) : ∃ h, div (y * x) y h = x :=
  ⟨⟨x, rfl⟩, by
    have h_div_correct := div_correct (y * x) y ⟨x, rfl⟩
    exact mul_cancel_left y _ x h_div_correct⟩

end ZeroMath.Numbers.OrdinalNatural.Peano
