import ZeroMath.Logic.Trichotomy
import ZeroMath.Logic.Dichotomy
import ZeroMath.Logic.ElementRelation

namespace ZeroMath

theorem bool_eq_of_true_iff {x y : Bool} (h : (x = true) ↔ (y = true)) : x = y := by
  cases x <;> cases y <;> simp_all

theorem option_map_eq_some {α β : Type} {f : α → β} {o : Option α} {b : β}
    (h : Option.map f o = some b) : ∃ a, o = some a ∧ f a = b := by
  cases o with
  | none => cases h
  | some a =>
    exact ⟨a, rfl, Option.some.inj h⟩

theorem option_map_eq_none {α β : Type} {f : α → β} {o : Option α}
    (h : Option.map f o = none) : o = none := by
  cases o with
  | none => rfl
  | some _ => cases h

end ZeroMath
