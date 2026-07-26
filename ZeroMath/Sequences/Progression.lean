import ZeroMath.Numbers.CardinalNatural.Peano

namespace ZeroMath.Sequences

/-- A (possibly empty, finite, or infinite) progression of a given type, defined
by an optional first element (`none` for the empty progression) and a function
returning the next element after the given element (or none if the given
element was the last one). -/
structure Progression (α : Type u) where
  first : Option α
  next : α → Option α

namespace Progression

/-- The empty progression: no first element, and `next` never yields a value. -/
def empty {α : Type u} : Progression α where
  first := none
  next := fun _ => none

/-- The element at the given positive ordinal index, or `none` if the index is
out of bounds. The first element has index `one`. -/
def tryGetElement {α : Type u} (index : Numbers.OrdinalNatural.Peano)
    (p : Progression α) : Option α :=
  match index with
  | Numbers.OrdinalNatural.Peano.one => p.first
  | Numbers.OrdinalNatural.Peano.successor n =>
    match tryGetElement n p with
    | none => none
    | some x => p.next x

/-- A progression is finite when there is some positive ordinal index at which
`tryGetElement` returns `none`. -/
def Finite {α : Type u} (p : Progression α) : Prop :=
  ∃ (index : Numbers.OrdinalNatural.Peano), tryGetElement index p = none

/-- A progression is infinite when it is not finite — that is, when
`tryGetElement` never returns `none`. -/
def Infinite {α : Type u} (p : Progression α) : Prop :=
  ¬ Finite p

/-- A progression `p` has length `n` when the least positive ordinal index at
which `tryGetElement` returns `none` is `n` plus one. -/
def Length {α : Type u} (p : Progression α) (n : Numbers.CardinalNatural.Peano) :
    Prop :=
  Numbers.CardinalNatural.Peano.Minimal n.successor fun k =>
    ∃ (hk : k ≠ Numbers.CardinalNatural.Peano.zero),
      tryGetElement (Numbers.CardinalNatural.Peano.toOrdinal k hk) p = none

/-- One step while walking a progression: from `some x` to `next x`. -/
inductive OptionStep {α : Type u} (next : α → Option α) :
    Option α → Option α → Prop where
  | step (x : α) : OptionStep next (next x) (some x)

theorem acc_none {α : Type u} (next : α → Option α) :
    Acc (OptionStep next) none :=
  Acc.intro none fun _ h => nomatch h

theorem acc_step {α : Type u} {next : α → Option α} {x : α}
    (h : Acc (OptionStep next) (next x)) :
    Acc (OptionStep next) (some x) :=
  Acc.intro (some x) fun y hy => by
    cases hy with
    | step => exact h

/-- Accessibility propagates from `tryGetElement index` back to `p.first`. -/
theorem acc_of_acc_tryGetElement {α : Type u} (p : Progression α) :
    (index : Numbers.OrdinalNatural.Peano) →
    Acc (OptionStep p.next) (tryGetElement index p) →
    Acc (OptionStep p.next) p.first
  | Numbers.OrdinalNatural.Peano.one, h => by
      simpa [tryGetElement] using h
  | Numbers.OrdinalNatural.Peano.successor n, h => by
      have hmid : Acc (OptionStep p.next) (tryGetElement n p) := by
        cases hm : tryGetElement n p with
        | none =>
          exact acc_none p.next
        | some x =>
          have hsucc : tryGetElement n.successor p = p.next x := by
            simp only [tryGetElement, hm]
          exact acc_step (hsucc ▸ h)
      exact acc_of_acc_tryGetElement p n hmid

theorem acc_first_of_finite {α : Type u} (p : Progression α) (h : Finite p) :
    Acc (OptionStep p.next) p.first := by
  obtain ⟨index, hnone⟩ := h
  exact acc_of_acc_tryGetElement p index (hnone ▸ acc_none p.next)

/-- Count elements from `current` using accessibility for termination. -/
def getLengthFrom {α : Type u} (next : α → Option α) (current : Option α)
    (h : Acc (OptionStep next) current) : Numbers.CardinalNatural.Peano :=
  Acc.rec (motive := fun _ _ => Numbers.CardinalNatural.Peano)
    (fun y _ ih =>
      match y with
      | none => Numbers.CardinalNatural.Peano.zero
      | some x =>
          Numbers.CardinalNatural.Peano.successor (ih (next x) (OptionStep.step x)))
    h

/-- The length of a finite progression: the number of elements before
`tryGetElement` first returns `none`. -/
def getLength {α : Type u} (p : Progression α) (h : Finite p) :
    Numbers.CardinalNatural.Peano :=
  getLengthFrom p.next p.first (acc_first_of_finite p h)

/-- The element relation used by `Equivalence`: setoid `≈` when a `Setoid` is
available, and equality otherwise. -/
class ElementRel (α : Type u) where
  Rel : α → α → Prop

instance (priority := low) (α : Type u) : ElementRel α where
  Rel := Eq

instance {α : Type u} [Setoid α] : ElementRel α where
  Rel := (· ≈ ·)

/-- Two progressions are equivalent when, for every positive ordinal index, the
results of `tryGetElement` are equivalent — via the element setoid when one
exists, and via equality otherwise. -/
def Equivalence {α : Type u} [ElementRel α] (p q : Progression α) : Prop :=
  ∀ (index : Numbers.OrdinalNatural.Peano),
    Option.Rel ElementRel.Rel (tryGetElement index p) (tryGetElement index q)

instance {α : Type u} [ElementRel α] : HasEquiv (Progression α) where
  Equiv := Equivalence

end Progression

end ZeroMath.Sequences
