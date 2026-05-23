import ZeroMath.Numbers.Integer
import ZeroMath.Numbers.OrdinalNatural

open ZeroMath.Numbers.Integer

theorem Peano.isLessThan_eq_true_iff_lt (a b : Peano) : Peano.isLessThan a b = true ↔ a < b := by
  constructor
  · intro h
    cases a
    case negative n =>
      cases b
      case negative m =>
        apply Peano.LessThan.negative_less_than_negative
        apply (ZeroMath.Numbers.OrdinalNatural.Peano.isLessThan_eq_true_iff_lt m n).mp
        exact h
      case zero => exact Peano.LessThan.negative_less_than_zero
      case positive m => exact Peano.LessThan.negative_less_than_positive
    case zero =>
      cases b
      case negative m => contradiction
      case zero => contradiction
      case positive m => exact Peano.LessThan.zero_less_than_positive
    case positive n =>
      cases b
      case negative m => contradiction
      case zero => contradiction
      case positive m =>
        apply Peano.LessThan.positive_less_than_positive
        apply (ZeroMath.Numbers.OrdinalNatural.Peano.isLessThan_eq_true_iff_lt n m).mp
        exact h
  · intro h
    cases h
    case negative_less_than_zero => rfl
    case zero_less_than_positive => rfl
    case negative_less_than_positive => rfl
    case positive_less_than_positive hlt =>
      dsimp [Peano.isLessThan]
      exact (ZeroMath.Numbers.OrdinalNatural.Peano.isLessThan_eq_true_iff_lt _ _).mpr hlt
    case negative_less_than_negative hlt =>
      dsimp [Peano.isLessThan]
      exact (ZeroMath.Numbers.OrdinalNatural.Peano.isLessThan_eq_true_iff_lt _ _).mpr hlt
