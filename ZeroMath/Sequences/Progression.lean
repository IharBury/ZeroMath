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

theorem getLengthFrom_none {α : Type u} (next : α → Option α)
    (h : Acc (OptionStep next) none) :
    getLengthFrom next none h = Numbers.CardinalNatural.Peano.zero := by
  cases h with
  | intro _ _ => rfl

theorem getLengthFrom_some {α : Type u} (next : α → Option α) (x : α)
    (h : Acc (OptionStep next) (some x)) :
    getLengthFrom next (some x) h =
      Numbers.CardinalNatural.Peano.successor
        (getLengthFrom next (next x) (h.inv (OptionStep.step x))) := by
  cases h with
  | intro _ _ => rfl

theorem getLengthFrom_eq_of_acc_eq {α : Type u} (next : α → Option α)
    (current : Option α)
    (h1 h2 : Acc (OptionStep next) current) :
    getLengthFrom next current h1 = getLengthFrom next current h2 :=
  rfl

theorem getLengthFrom_eq_of_current_eq {α : Type u} (next : α → Option α)
    {c1 c2 : Option α} (hEq : c1 = c2)
    (h1 : Acc (OptionStep next) c1) :
    getLengthFrom next c1 h1 = getLengthFrom next c2 (hEq ▸ h1) := by
  cases hEq
  rfl

/-- The element at a positive ordinal index counted from `current`, when that
index does not exceed the remaining length from `current`. -/
def getElementFrom {α : Type u} (next : α → Option α) (current : Option α)
    (hAcc : Acc (OptionStep next) current)
    (index : Numbers.OrdinalNatural.Peano)
    (hle : Numbers.CardinalNatural.Peano.fromOrdinal index ≤
      getLengthFrom next current hAcc) : α :=
  match index with
  | Numbers.OrdinalNatural.Peano.one =>
    match current, hAcc with
    | none, hAcc' =>
      False.elim
        (Numbers.CardinalNatural.Peano.successor_not_le_zero
          Numbers.CardinalNatural.Peano.zero
          (by
            simpa [getLengthFrom_none, Numbers.CardinalNatural.Peano.fromOrdinal,
              Numbers.CardinalNatural.Peano.one] using hle))
    | some x, _ => x
  | Numbers.OrdinalNatural.Peano.successor n =>
    match current, hAcc with
    | none, hAcc' =>
      False.elim
        (Numbers.CardinalNatural.Peano.successor_not_le_zero
          (Numbers.CardinalNatural.Peano.fromOrdinal n)
          (by
            simpa [getLengthFrom_none, Numbers.CardinalNatural.Peano.fromOrdinal]
              using hle))
    | some x, hAcc' =>
      getElementFrom next (next x) (hAcc'.inv (OptionStep.step x)) n
        (by
          have hlen := getLengthFrom_some next x hAcc'
          have hle' :
              Numbers.CardinalNatural.Peano.successor
                  (Numbers.CardinalNatural.Peano.fromOrdinal n) ≤
                Numbers.CardinalNatural.Peano.successor
                  (getLengthFrom next (next x)
                    (hAcc'.inv (OptionStep.step x))) := by
            simpa [hlen, Numbers.CardinalNatural.Peano.fromOrdinal] using hle
          exact Numbers.CardinalNatural.Peano.le_of_succ_le_succ hle')

/-- The element at the given positive ordinal index of a finite progression,
when that index does not exceed the progression's length. The first element
has index `one`. -/
def getElement {α : Type u} (p : Progression α) (hFinite : Finite p)
    (index : Numbers.OrdinalNatural.Peano)
    (hle : Numbers.CardinalNatural.Peano.fromOrdinal index ≤ getLength p hFinite) :
    α :=
  getElementFrom p.next p.first (acc_first_of_finite p hFinite) index hle

theorem getElementFrom_eq_of_current_eq {α : Type u}
    (next : α → Option α) {c1 c2 : Option α} (hEq : c1 = c2)
    (h1 : Acc (OptionStep next) c1)
    (index : Numbers.OrdinalNatural.Peano)
    (hle : Numbers.CardinalNatural.Peano.fromOrdinal index ≤
      getLengthFrom next c1 h1) :
    getElementFrom next c1 h1 index hle =
      getElementFrom next c2 (hEq ▸ h1) index
        (by
          have hlen := getLengthFrom_eq_of_current_eq next hEq h1
          exact hlen ▸ hle) := by
  cases hEq
  rfl

theorem getElementFrom_eq_of_acc_eq {α : Type u}
    (next : α → Option α) (current : Option α)
    (h1 h2 : Acc (OptionStep next) current)
    (index : Numbers.OrdinalNatural.Peano)
    (hle1 : Numbers.CardinalNatural.Peano.fromOrdinal index ≤
      getLengthFrom next current h1)
    (hle2 : Numbers.CardinalNatural.Peano.fromOrdinal index ≤
      getLengthFrom next current h2) :
    getElementFrom next current h1 index hle1 =
      getElementFrom next current h2 index hle2 :=
  rfl

theorem finite_of_length {α : Type u} {p : Progression α}
    {n : Numbers.CardinalNatural.Peano} (h : Length p n) : Finite p := by
  obtain ⟨⟨hk, hnone⟩, _⟩ := h
  exact ⟨Numbers.CardinalNatural.Peano.toOrdinal n.successor hk, hnone⟩

/-- A progression has some finite length if and only if it is finite. -/
theorem exists_length_iff_finite {α : Type u} (x : Progression α) :
    (∃ n, Length x n) ↔ Finite x := by
  constructor
  · intro ⟨_, hLength⟩
    exact finite_of_length hLength
  · intro hFinite
    obtain ⟨index, hnone⟩ := hFinite
    let condition : Numbers.CardinalNatural.Peano → Prop := fun k =>
      ∃ (hk : k ≠ Numbers.CardinalNatural.Peano.zero),
        tryGetElement (Numbers.CardinalNatural.Peano.toOrdinal k hk) x = none
    obtain ⟨hk, hto⟩ := Numbers.CardinalNatural.Peano.toOrdinal_fromOrdinal index
    have hex : ∃ k, condition k :=
      ⟨Numbers.CardinalNatural.Peano.fromOrdinal index, hk, by
        rw [hto]; exact hnone⟩
    obtain ⟨m, hm⟩ := Numbers.CardinalNatural.Peano.exists_minimal condition hex
    have hm_ne : m ≠ Numbers.CardinalNatural.Peano.zero := by
      intro hm0
      have hEnds := hm.1
      rw [hm0] at hEnds
      obtain ⟨hk0, _⟩ := hEnds
      exact hk0 rfl
    refine ⟨Numbers.CardinalNatural.Peano.predecessor m hm_ne, ?_⟩
    change Numbers.CardinalNatural.Peano.Minimal
        (Numbers.CardinalNatural.Peano.predecessor m hm_ne).successor condition
    rw [Numbers.CardinalNatural.Peano.successor_predecessor m hm_ne]
    exact hm

/-- The element relation used by `Equivalence`: setoid `≈` when a `Setoid` is
available, and equality otherwise. -/
class ElementRel (α : Type u) where
  Rel : α → α → Prop

instance (priority := low) (α : Type u) : ElementRel α where
  Rel := Eq

instance {α : Type u} [Setoid α] : ElementRel α where
  Rel := (· ≈ ·)

/-- When there is no setoid, `ElementRel.Rel` is equality, so `DecidableEq`
decides it. -/
instance (priority := low) {α : Type u} [DecidableEq α] :
    DecidableRel (ElementRel.Rel (α := α)) :=
  fun a b => inferInstanceAs (Decidable (a = b))

/-- When a setoid is present, `ElementRel.Rel` is `≈`. -/
instance {α : Type u} [Setoid α] [∀ (a b : α), Decidable (a ≈ b)] :
    DecidableRel (ElementRel.Rel (α := α)) :=
  fun a b => inferInstanceAs (Decidable (a ≈ b))

/-- Two progressions are equivalent when, for every positive ordinal index, the
results of `tryGetElement` are equivalent — via the element setoid when one
exists, and via equality otherwise. -/
def Equivalence {α : Type u} [ElementRel α] (p q : Progression α) : Prop :=
  ∀ (index : Numbers.OrdinalNatural.Peano),
    Option.Rel ElementRel.Rel (tryGetElement index p) (tryGetElement index q)

instance {α : Type u} [ElementRel α] : HasEquiv (Progression α) where
  Equiv := Equivalence

/-- If a progression has no first element, `tryGetElement` is always `none`. -/
theorem tryGetElement_none_of_first_none {α : Type u} (next : α → Option α)
    (index : Numbers.OrdinalNatural.Peano) :
    tryGetElement index ⟨none, next⟩ = none := by
  induction index with
  | one =>
    rfl
  | successor n ih =>
    simp only [tryGetElement, ih]

/-- Stepping past a known first element shifts `tryGetElement` by one index. -/
theorem tryGetElement_tail {α : Type u} (next : α → Option α) (x : α)
    (index : Numbers.OrdinalNatural.Peano) :
    tryGetElement index ⟨next x, next⟩ =
      tryGetElement index.successor ⟨some x, next⟩ := by
  induction index with
  | one =>
    rfl
  | successor n ih =>
    simp only [tryGetElement, ih]

/-- `Option.Rel` is decidable when the underlying relation is. -/
instance decidableOptionRel {α : Type u} {β : Type v} (r : α → β → Prop)
    [DecidableRel r] (a : Option α) (b : Option β) :
    Decidable (Option.Rel r a b) :=
  match a, b with
  | some x, some y =>
    match ‹DecidableRel r› x y with
    | isTrue h => isTrue (Option.Rel.some h)
    | isFalse nh =>
      isFalse fun h => by
        cases h with
        | some hxy => exact nh hxy
  | none, none => isTrue Option.Rel.none
  | some _, none =>
    isFalse fun h => by
      cases h
  | none, some _ =>
    isFalse fun h => by
      cases h

/-- Convert an `Option.Rel (· ≈ ·)` fact against `some y` into an explicit
witness. -/
theorem exists_of_option_rel_some {α : Type u} [Setoid α] {x : Option α} {y : α}
    (h : Option.Rel (· ≈ ·) x (some y)) :
    ∃ z, x = some z ∧ z ≈ y := by
  cases h with
  | some hz => exact ⟨_, rfl, hz⟩

/-- Decide equivalence of two progressions from accessible starting points by
walking both in lockstep. -/
def decidableEquivalenceFrom {α : Type u} [ElementRel α]
    [DecidableRel (ElementRel.Rel (α := α))]
    (nextP nextQ : α → Option α)
    (curP : Option α) (hP : Acc (OptionStep nextP) curP)
    (curQ : Option α) (hQ : Acc (OptionStep nextQ) curQ) :
    Decidable (Equivalence (⟨curP, nextP⟩ : Progression α) ⟨curQ, nextQ⟩) :=
  Acc.rec
    (motive := fun y _ =>
      (z : Option α) → Acc (OptionStep nextQ) z →
        Decidable (Equivalence (⟨y, nextP⟩ : Progression α) ⟨z, nextQ⟩))
    (fun y _ ih z hz =>
      match y, z, hz with
      | none, none, _ =>
        isTrue fun index => by
          have hp := tryGetElement_none_of_first_none nextP index
          have hq := tryGetElement_none_of_first_none nextQ index
          simp only [hp, hq]
          exact Option.Rel.none
      | some x, some w, Acc.intro _ hzw =>
        match ‹DecidableRel (ElementRel.Rel (α := α))› x w with
        | isTrue hxw =>
          match ih (nextP x) (OptionStep.step x) (nextQ w)
              (hzw (nextQ w) (OptionStep.step w)) with
          | isTrue htails =>
            isTrue fun index => by
              match index with
              | Numbers.OrdinalNatural.Peano.one =>
                exact Option.Rel.some hxw
              | Numbers.OrdinalNatural.Peano.successor n =>
                have h := htails n
                rw [tryGetElement_tail nextP x n, tryGetElement_tail nextQ w n] at h
                exact h
          | isFalse ntails =>
            isFalse fun hall =>
              ntails fun n => by
                have h := hall n.successor
                rw [← tryGetElement_tail nextP x n, ← tryGetElement_tail nextQ w n] at h
                exact h
        | isFalse nxw =>
          isFalse fun hall =>
            nxw <| by
              have h := hall Numbers.OrdinalNatural.Peano.one
              cases h with
              | some hxw => exact hxw
      | none, some _, _ =>
        isFalse fun hall => by
          have h := hall Numbers.OrdinalNatural.Peano.one
          cases h
      | some _, none, _ =>
        isFalse fun hall => by
          have h := hall Numbers.OrdinalNatural.Peano.one
          cases h)
    hP curQ hQ

/-- Decide equivalence of two finite progressions. -/
def decidableEquivalenceOfFinite {α : Type u} [ElementRel α]
    [DecidableRel (ElementRel.Rel (α := α))]
    (p q : Progression α) (hp : Finite p) (hq : Finite q) :
    Decidable (Equivalence p q) :=
  decidableEquivalenceFrom p.next q.next p.first (acc_first_of_finite p hp)
    q.first (acc_first_of_finite q hq)

/-- In-range `tryGetElement` returns `some` of the corresponding `getElementFrom`. -/
theorem tryGetElement_eq_some_getElementFrom {α : Type u} (next : α → Option α)
    (current : Option α) (hAcc : Acc (OptionStep next) current)
    (index : Numbers.OrdinalNatural.Peano)
    (hle : Numbers.CardinalNatural.Peano.fromOrdinal index ≤
      getLengthFrom next current hAcc) :
    tryGetElement index ⟨current, next⟩ =
      some (getElementFrom next current hAcc index hle) := by
  induction index generalizing current hAcc with
  | one =>
    match current, hAcc with
    | none, hAcc' =>
      exact False.elim
        (Numbers.CardinalNatural.Peano.successor_not_le_zero
          Numbers.CardinalNatural.Peano.zero
          (by
            simpa [getLengthFrom_none, Numbers.CardinalNatural.Peano.fromOrdinal,
              Numbers.CardinalNatural.Peano.one] using hle))
    | some x, _ =>
      rfl
  | successor n ih =>
    match current, hAcc with
    | none, hAcc' =>
      exact False.elim
        (Numbers.CardinalNatural.Peano.successor_not_le_zero
          (Numbers.CardinalNatural.Peano.fromOrdinal n)
          (by
            simpa [getLengthFrom_none, Numbers.CardinalNatural.Peano.fromOrdinal]
              using hle))
    | some x, hAcc' =>
      have hlen := getLengthFrom_some next x hAcc'
      have hle' :
          Numbers.CardinalNatural.Peano.fromOrdinal n ≤
            getLengthFrom next (next x) (hAcc'.inv (OptionStep.step x)) := by
        have hle_succ :
            Numbers.CardinalNatural.Peano.successor
                (Numbers.CardinalNatural.Peano.fromOrdinal n) ≤
              Numbers.CardinalNatural.Peano.successor
                (getLengthFrom next (next x)
                  (hAcc'.inv (OptionStep.step x))) := by
          simpa [hlen, Numbers.CardinalNatural.Peano.fromOrdinal] using hle
        exact Numbers.CardinalNatural.Peano.le_of_succ_le_succ hle_succ
      have ih' := ih (next x) (hAcc'.inv (OptionStep.step x)) hle'
      have htail := tryGetElement_tail next x n
      rw [← htail, ih']
      rfl

/-- In-range `tryGetElement` returns `some` of the corresponding `getElement`. -/
theorem tryGetElement_eq_some_getElement {α : Type u} (p : Progression α)
    (hFinite : Finite p) (index : Numbers.OrdinalNatural.Peano)
    (hle : Numbers.CardinalNatural.Peano.fromOrdinal index ≤ getLength p hFinite) :
    tryGetElement index p = some (getElement p hFinite index hle) :=
  tryGetElement_eq_some_getElementFrom p.next p.first
    (acc_first_of_finite p hFinite) index hle

/-- Out-of-range `tryGetElement` is `none` when the remaining length is strictly
smaller than the ordinal index. -/
theorem tryGetElement_eq_none_of_lengthFrom_lt {α : Type u} (next : α → Option α)
    (current : Option α) (hAcc : Acc (OptionStep next) current)
    (index : Numbers.OrdinalNatural.Peano)
    (hlt : getLengthFrom next current hAcc <
      Numbers.CardinalNatural.Peano.fromOrdinal index) :
    tryGetElement index ⟨current, next⟩ = none := by
  induction index generalizing current hAcc with
  | one =>
    match current, hAcc with
    | none, hAcc' =>
      rfl
    | some x, hAcc' =>
      have hlen := getLengthFrom_some next x hAcc'
      rw [hlen] at hlt
      exact False.elim
        (Numbers.CardinalNatural.Peano.not_lt_zero _
          (Numbers.CardinalNatural.Peano.lt_of_succ_lt_succ
            (by
              simpa [Numbers.CardinalNatural.Peano.fromOrdinal,
                Numbers.CardinalNatural.Peano.one] using hlt)))
  | successor n ih =>
    match current, hAcc with
    | none, hAcc' =>
      exact tryGetElement_none_of_first_none next n.successor
    | some x, hAcc' =>
      have hlen := getLengthFrom_some next x hAcc'
      have hlt' :
          getLengthFrom next (next x) (hAcc'.inv (OptionStep.step x)) <
            Numbers.CardinalNatural.Peano.fromOrdinal n := by
        have : Numbers.CardinalNatural.Peano.successor
              (getLengthFrom next (next x) (hAcc'.inv (OptionStep.step x))) <
            Numbers.CardinalNatural.Peano.successor
              (Numbers.CardinalNatural.Peano.fromOrdinal n) := by
          simpa [hlen, Numbers.CardinalNatural.Peano.fromOrdinal] using hlt
        exact Numbers.CardinalNatural.Peano.lt_of_succ_lt_succ this
      have ih' := ih (next x) (hAcc'.inv (OptionStep.step x)) hlt'
      exact (tryGetElement_tail next x n).symm.trans ih'

/-- Out-of-range `tryGetElement` on a finite progression is `none`. -/
theorem tryGetElement_eq_none_of_getLength_lt {α : Type u} (p : Progression α)
    (hFinite : Finite p) (index : Numbers.OrdinalNatural.Peano)
    (hlt : getLength p hFinite <
      Numbers.CardinalNatural.Peano.fromOrdinal index) :
    tryGetElement index p = none :=
  tryGetElement_eq_none_of_lengthFrom_lt p.next p.first
    (acc_first_of_finite p hFinite) index hlt

end Progression

end ZeroMath.Sequences
