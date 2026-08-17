namespace ZeroMath.Logic

/-- The relation used by structural `Equivalence`: setoid `≈` when a `Setoid` is
available, and equality otherwise. -/
class ElementRelation (α : Type u) where
  relation : α → α → Prop
  reflexive : ∀ (x : α), relation x x
  symmetric : ∀ {x y : α}, relation x y → relation y x
  transitive : ∀ {x y z : α}, relation x y → relation y z → relation x z

instance (priority := low) (α : Type u) : ElementRelation α where
  relation := Eq
  reflexive := fun _ => rfl
  symmetric := Eq.symm
  transitive := Eq.trans

instance {α : Type u} [Setoid α] : ElementRelation α where
  relation := (· ≈ ·)
  reflexive := Setoid.refl
  symmetric := fun h => Setoid.symm h
  transitive := fun h₁ h₂ => Setoid.trans h₁ h₂

/-- When there is no setoid, `ElementRelation.relation` is equality, so `DecidableEq`
decides it. -/
instance (priority := low) {α : Type u} [DecidableEq α] :
    DecidableRel (ElementRelation.relation (α := α)) :=
  fun a b => inferInstanceAs (Decidable (a = b))

/-- When a setoid is present, `ElementRelation.relation` is `≈`. -/
instance {α : Type u} [Setoid α] [∀ (a b : α), Decidable (a ≈ b)] :
    DecidableRel (ElementRelation.relation (α := α)) :=
  fun a b => inferInstanceAs (Decidable (a ≈ b))

end ZeroMath.Logic
