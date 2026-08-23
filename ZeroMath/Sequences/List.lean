import ZeroMath.Numbers.CardinalNatural.Peano

namespace ZeroMath.Sequences

inductive List (α : Type u) where
  | empty : List α
  | firstElement : α → List α → List α

deriving instance DecidableEq for List

namespace List

inductive AnyElement {α : Type u} (p : α → Prop) : List α → Prop where
  | first d ds : p d → AnyElement p (firstElement d ds)
  | notFirst d ds : AnyElement p ds → AnyElement p (firstElement d ds)

def anyElement {α : Type u} (p : α → Bool) (a : List α) : Bool :=
  match a with
  | empty => false
  | firstElement d ds =>
    if p d then
      true
    else
      anyElement p ds


example {α : Type} (p : α → Bool) : anyElement p empty = false := rfl
example : anyElement (fun x => x) (firstElement true empty) = true := rfl
example : anyElement (fun x => x) (firstElement false empty) = false := rfl
example : anyElement (fun x => x) (firstElement false (firstElement true empty)) = true := rfl
example : anyElement (fun x => x) (firstElement false (firstElement false empty)) = false := rfl

theorem anyElement_eq_true_iff {α : Type u} (p : α → Bool) (l : List α) :
    anyElement p l = true ↔ AnyElement (fun x => p x = true) l := by
  induction l with
  | empty =>
    constructor
    · intro h
      simp only [anyElement] at h
      exact False.elim (Bool.false_ne_true h)
    · intro h
      cases h
  | firstElement d ds ih =>
    simp only [anyElement]
    split
    · next hp =>
      constructor
      · intro _
        exact AnyElement.first d ds hp
      · intro _
        rfl
    · next hnp =>
      constructor
      · intro h
        exact AnyElement.notFirst d ds (ih.mp h)
      · intro h
        cases h with
        | first _ _ hp => exact absurd hp hnp
        | notFirst _ _ hds => exact ih.mpr hds

theorem anyElement_decide_eq_true_iff {α : Type u} (p : α → Prop) [DecidablePred p]
    (l : List α) :
    anyElement (fun x => decide (p x)) l = true ↔ AnyElement p l := by
  rw [anyElement_eq_true_iff]
  constructor
  · intro hAny
    induction hAny with
    | first d ds hp =>
      exact AnyElement.first d ds (decide_eq_true_iff.mp hp)
    | notFirst d ds _ ih =>
      exact AnyElement.notFirst d ds ih
  · intro hAny
    induction hAny with
    | first d ds hp =>
      exact AnyElement.first d ds (decide_eq_true_iff.mpr hp)
    | notFirst d ds _ ih =>
      exact AnyElement.notFirst d ds ih

instance decidableAnyElement {α : Type u} (p : α → Prop) [DecidablePred p]
    (l : List α) : Decidable (AnyElement p l) := by
  cases h : anyElement (fun x => decide (p x)) l with
  | false =>
    exact isFalse (fun hAny =>
      Bool.noConfusion (Eq.trans h.symm ((anyElement_decide_eq_true_iff p l).mpr hAny)))
  | true =>
    exact isTrue ((anyElement_decide_eq_true_iff p l).mp h)

inductive AllElements {α : Type u} (p : α → Prop) : List α → Prop where
  | empty : AllElements p empty
  | firstElement (d : α) (ds : List α) :
      p d → AllElements p ds → AllElements p (firstElement d ds)

def allElements {α : Type u} (p : α → Bool) (a : List α) : Bool :=
  match a with
  | empty => true
  | firstElement d ds =>
    if p d then
      allElements p ds
    else
      false

example {α : Type} (p : α → Bool) : allElements p empty = true := rfl
example : allElements (fun x => x) (firstElement true empty) = true := rfl
example : allElements (fun x => x) (firstElement false empty) = false := rfl
example : allElements (fun x => x)
    (firstElement true (firstElement true empty)) = true := rfl
example : allElements (fun x => x)
    (firstElement true (firstElement false empty)) = false := rfl

theorem allElements_eq_true_iff {α : Type u} (p : α → Bool) (l : List α) :
    allElements p l = true ↔ AllElements (fun x => p x = true) l := by
  induction l with
  | empty =>
    constructor
    · intro _
      exact AllElements.empty
    · intro _
      rfl
  | firstElement d ds ih =>
    simp only [allElements]
    split
    · next hp =>
      constructor
      · intro h
        exact AllElements.firstElement d ds hp (ih.mp h)
      · intro h
        cases h with
        | firstElement _ _ _ hds => exact ih.mpr hds
    · next hnp =>
      constructor
      · intro h
        exact False.elim (Bool.false_ne_true h)
      · intro h
        cases h with
        | firstElement _ _ hp _ => exact absurd hp hnp

theorem allElements_decide_eq_true_iff {α : Type u} (p : α → Prop) [DecidablePred p]
    (l : List α) :
    allElements (fun x => decide (p x)) l = true ↔ AllElements p l := by
  rw [allElements_eq_true_iff]
  constructor
  · intro hAll
    induction hAll with
    | empty => exact AllElements.empty
    | firstElement d ds hp _ ih =>
      exact AllElements.firstElement d ds (decide_eq_true_iff.mp hp) ih
  · intro hAll
    induction hAll with
    | empty => exact AllElements.empty
    | firstElement d ds hp _ ih =>
      exact AllElements.firstElement d ds (decide_eq_true_iff.mpr hp) ih

instance decidableAllElements {α : Type u} (p : α → Prop) [DecidablePred p]
    (l : List α) : Decidable (AllElements p l) := by
  cases h : allElements (fun x => decide (p x)) l with
  | false =>
    exact isFalse (fun hAll =>
      Bool.noConfusion (Eq.trans h.symm ((allElements_decide_eq_true_iff p l).mpr hAll)))
  | true =>
    exact isTrue ((allElements_decide_eq_true_iff p l).mp h)

theorem AllElements.head {α : Type u} {p : α → Prop} {x : α} {xs : List α}
    (h : AllElements p (List.firstElement x xs)) : p x := by
  cases h with
  | firstElement _ _ hp _ => exact hp

theorem AllElements.tail {α : Type u} {p : α → Prop} {x : α} {xs : List α}
    (h : AllElements p (List.firstElement x xs)) : AllElements p xs := by
  cases h with
  | firstElement _ _ _ hds => exact hds

def In {α : Type u} (x : α) (l : List α) : Prop :=
  AnyElement (fun y => y = x) l

instance decidableIn {α : Type u} [DecidableEq α] (x : α) (l : List α) :
    Decidable (In x l) :=
  decidableAnyElement (fun y => y = x) l

theorem AllElements.of_In {α : Type u} {p : α → Prop} {x : α} {l : List α}
    (hAll : AllElements p l) (hIn : In x l) : p x := by
  induction hAll with
  | empty => cases hIn
  | firstElement d ds hp _ ih =>
    cases hIn with
    | first _ _ heq => exact heq ▸ hp
    | notFirst _ _ hds => exact ih hds

theorem AllElements.not_In {α : Type u} {p : α → Prop} {x : α} {l : List α}
    (hAll : AllElements p l) (hn : ¬ p x) : ¬ In x l :=
  fun hIn => hn (AllElements.of_In hAll hIn)

def EquivalentIn {α : Type u} [Setoid α] (x : α) (l : List α) : Prop :=
  AnyElement (fun y => y ≈ x) l

instance decidableEquivalentIn {α : Type u} [Setoid α]
    [∀ (a b : α), Decidable (a ≈ b)] (x : α) (l : List α) :
    Decidable (EquivalentIn x l) :=
  decidableAnyElement (fun y => y ≈ x) l

inductive Before {α : Type u} (x y : α) : List α → Prop where
  | first ds : In y ds → Before x y (firstElement x ds)
  | notFirst d ds : Before x y ds → Before x y (firstElement d ds)

theorem before_implies_In {α : Type u} {x y : α} {l : List α}
    (h : Before x y l) : In y l := by
  induction h with
  | first ds hin => exact AnyElement.notFirst x ds hin
  | notFirst d ds _ ih => exact AnyElement.notFirst d ds ih

instance decidableBefore {α : Type u} [DecidableEq α] (x y : α) :
    (l : List α) → Decidable (Before x y l)
  | empty => isFalse fun h => by cases h
  | firstElement d ds =>
    match decEq d x, decidableIn y ds, decidableBefore x y ds with
    | isTrue hdx, isTrue hin, _ =>
      isTrue (hdx ▸ Before.first ds hin)
    | isTrue hdx, isFalse hnin, _ =>
      isFalse fun hB => by
        cases hdx
        cases hB with
        | first _ hin => exact hnin hin
        | notFirst _ _ hb => exact hnin (before_implies_In hb)
    | isFalse hndx, _, isTrue hb =>
      isTrue (Before.notFirst d ds hb)
    | isFalse hndx, _, isFalse hnb =>
      isFalse fun hB => by
        cases hB with
        | first _ _ => exact hndx rfl
        | notFirst _ _ hb => exact hnb hb

def After {α : Type u} (x y : α) (l : List α) : Prop :=
  Before y x l

instance decidableAfter {α : Type u} [DecidableEq α] (x y : α) (l : List α) :
    Decidable (After x y l) :=
  decidableBefore y x l

def Between {α : Type u} (x y z : α) (l : List α) : Prop :=
  (After x y l ∧ Before x z l) ∨ (After x z l ∧ Before x y l)

instance decidableBetween {α : Type u} [DecidableEq α] (x y z : α) (l : List α) :
    Decidable (Between x y z l) :=
  inferInstanceAs (Decidable ((After x y l ∧ Before x z l) ∨ (After x z l ∧ Before x y l)))

inductive EquivalentBefore {α : Type u} [Setoid α] (x y : α) : List α → Prop where
  | first d ds : d ≈ x → EquivalentIn y ds → EquivalentBefore x y (firstElement d ds)
  | notFirst d ds : EquivalentBefore x y ds → EquivalentBefore x y (firstElement d ds)

theorem equivalentBefore_implies_EquivalentIn {α : Type u} [Setoid α] {x y : α}
    {l : List α} (h : EquivalentBefore x y l) : EquivalentIn y l := by
  induction h with
  | first d ds _ hin => exact AnyElement.notFirst d ds hin
  | notFirst d ds _ ih => exact AnyElement.notFirst d ds ih

instance decidableEquivalentBefore {α : Type u} [Setoid α]
    [∀ (a b : α), Decidable (a ≈ b)] (x y : α) :
    (l : List α) → Decidable (EquivalentBefore x y l)
  | empty => isFalse fun h => by cases h
  | firstElement d ds =>
    match (inferInstance : Decidable (d ≈ x)), decidableEquivalentIn y ds,
        decidableEquivalentBefore x y ds with
    | isTrue hdx, isTrue hin, _ =>
      isTrue (EquivalentBefore.first d ds hdx hin)
    | isTrue _, isFalse hnin, _ =>
      isFalse fun hB => by
        cases hB with
        | first _ _ _ hin => exact hnin hin
        | notFirst _ _ hb => exact hnin (equivalentBefore_implies_EquivalentIn hb)
    | isFalse _, _, isTrue hb =>
      isTrue (EquivalentBefore.notFirst d ds hb)
    | isFalse hndx, _, isFalse hnb =>
      isFalse fun hB => by
        cases hB with
        | first _ _ heq _ => exact hndx heq
        | notFirst _ _ hb => exact hnb hb

def EquivalentAfter {α : Type u} [Setoid α] (x y : α) (l : List α) : Prop :=
  EquivalentBefore y x l

instance decidableEquivalentAfter {α : Type u} [Setoid α]
    [∀ (a b : α), Decidable (a ≈ b)] (x y : α) (l : List α) :
    Decidable (EquivalentAfter x y l) :=
  decidableEquivalentBefore y x l

def EquivalentBetween {α : Type u} [Setoid α] (x y z : α) (l : List α) : Prop :=
  (EquivalentAfter x y l ∧ EquivalentBefore x z l) ∨
    (EquivalentAfter x z l ∧ EquivalentBefore x y l)

instance decidableEquivalentBetween {α : Type u} [Setoid α]
    [∀ (a b : α), Decidable (a ≈ b)] (x y z : α) (l : List α) :
    Decidable (EquivalentBetween x y z l) :=
  inferInstanceAs
    (Decidable
      ((EquivalentAfter x y l ∧ EquivalentBefore x z l) ∨
        (EquivalentAfter x z l ∧ EquivalentBefore x y l)))

/-- There are no two equal elements in the list. -/
inductive Unique {α : Type u} : List α → Prop where
  | empty : Unique empty
  | firstElement (d : α) (ds : List α) : ¬ In d ds → Unique ds → Unique (firstElement d ds)

instance decidableUnique {α : Type u} [DecidableEq α] :
    (l : List α) → Decidable (Unique l)
  | empty => isTrue Unique.empty
  | firstElement d ds =>
    match decidableIn d ds, decidableUnique ds with
    | isFalse hnin, isTrue huniq =>
      isTrue (Unique.firstElement d ds hnin huniq)
    | isTrue hin, _ =>
      isFalse fun h => by
        cases h with
        | firstElement _ _ hnin _ => exact hnin hin
    | _, isFalse hnuniq =>
      isFalse fun h => by
        cases h with
        | firstElement _ _ _ huniq => exact hnuniq huniq

theorem Unique.not_in_head {α : Type u} {x : α} {xs : List α}
    (h : Unique (List.firstElement x xs)) : ¬ In x xs := by
  cases h with
  | firstElement _ _ hnin _ => exact hnin

theorem Unique.tail {α : Type u} {x : α} {xs : List α}
    (h : Unique (List.firstElement x xs)) : Unique xs := by
  cases h with
  | firstElement _ _ _ huniq => exact huniq

theorem not_in_tail {α : Type u} {x y : α} {ys : List α}
    (h : ¬ In x (firstElement y ys)) : ¬ In x ys :=
  fun hin => h (AnyElement.notFirst y ys hin)

theorem ne_of_not_in_firstElement {α : Type u} {x y : α} {ys : List α}
    (h : ¬ In x (firstElement y ys)) : x ≠ y :=
  fun heq => h (AnyElement.first y ys heq.symm)

theorem AnyElement.of_In {α : Type u} {p : α → Prop} {x : α} {l : List α}
    (hin : In x l) (hp : p x) : AnyElement p l := by
  induction hin with
  | first d ds heq => exact AnyElement.first d ds (heq ▸ hp)
  | notFirst d ds _ ih => exact AnyElement.notFirst d ds ih

/-- There are no two equivalent elements in the list. -/
inductive UniqueUpToEquivalence {α : Type u} [Setoid α] : List α → Prop where
  | empty : UniqueUpToEquivalence empty
  | firstElement (d : α) (ds : List α) :
      ¬ EquivalentIn d ds → UniqueUpToEquivalence ds →
        UniqueUpToEquivalence (firstElement d ds)

instance decidableUniqueUpToEquivalence {α : Type u} [Setoid α]
    [∀ (a b : α), Decidable (a ≈ b)] :
    (l : List α) → Decidable (UniqueUpToEquivalence l)
  | empty => isTrue UniqueUpToEquivalence.empty
  | firstElement d ds =>
    match decidableEquivalentIn d ds, decidableUniqueUpToEquivalence ds with
    | isFalse hnin, isTrue huniq =>
      isTrue (UniqueUpToEquivalence.firstElement d ds hnin huniq)
    | isTrue hin, _ =>
      isFalse fun h => by
        cases h with
        | firstElement _ _ hnin _ => exact hnin hin
    | _, isFalse hnuniq =>
      isFalse fun h => by
        cases h with
        | firstElement _ _ _ huniq => exact hnuniq huniq

theorem UniqueUpToEquivalence.not_in_head {α : Type u} [Setoid α] {x : α}
    {xs : List α} (h : UniqueUpToEquivalence (List.firstElement x xs)) :
    ¬ EquivalentIn x xs := by
  cases h with
  | firstElement _ _ hnin _ => exact hnin

theorem UniqueUpToEquivalence.tail {α : Type u} [Setoid α] {x : α} {xs : List α}
    (h : UniqueUpToEquivalence (List.firstElement x xs)) :
    UniqueUpToEquivalence xs := by
  cases h with
  | firstElement _ _ _ huniq => exact huniq

theorem not_equivalentIn_tail {α : Type u} [Setoid α] {x y : α} {ys : List α}
    (h : ¬ EquivalentIn x (firstElement y ys)) : ¬ EquivalentIn x ys :=
  fun hin => h (AnyElement.notFirst y ys hin)

theorem not_equivalent_of_not_equivalentIn_firstElement {α : Type u} [Setoid α]
    {x y : α} {ys : List α}
    (h : ¬ EquivalentIn x (firstElement y ys)) : ¬ x ≈ y :=
  fun heq => h (AnyElement.first y ys (Setoid.symm heq))

theorem equivalentIn_of_subset {α : Type u} [Setoid α] {x : α} {l l' : List α}
    (hsubset : ∀ z, In z l' → In z l) (h : EquivalentIn x l') :
    EquivalentIn x l := by
  induction h with
  | first d ds heq =>
    exact AnyElement.of_In (hsubset d (AnyElement.first d ds rfl)) heq
  | notFirst d ds _ ih =>
    exact ih (fun z hz => hsubset z (AnyElement.notFirst d ds hz))

/-- `RemoveFirst x l l'` means `l'` is `l` with the first occurrence of `x` removed. -/
inductive RemoveFirst {α : Type u} (x : α) : List α → List α → Prop where
  | here (ys : List α) : RemoveFirst x (firstElement x ys) ys
  | there (y : α) (ys ys' : List α) :
      x ≠ y → RemoveFirst x ys ys' →
        RemoveFirst x (firstElement y ys) (firstElement y ys')

/-- Remove the first occurrence of `x`, if any. -/
def removeFirst {α : Type u} [DecidableEq α] (x : α) : List α → Option (List α)
  | empty => none
  | firstElement y ys =>
    if x = y then
      some ys
    else
      match removeFirst x ys with
      | none => none
      | some ys' => some (firstElement y ys')

theorem removeFirst_eq_some_iff {α : Type u} [DecidableEq α] (x : α) (l l' : List α) :
    removeFirst x l = some l' ↔ RemoveFirst x l l' := by
  induction l generalizing l' with
  | empty =>
    constructor
    · intro h
      simp only [removeFirst] at h
      nomatch h
    · intro h
      cases h
  | firstElement y ys ih =>
    simp only [removeFirst]
    split
    · next heq =>
      cases heq
      constructor
      · intro h
        injection h with hl'
        cases hl'
        exact RemoveFirst.here _
      · intro h
        cases h with
        | here => rfl
        | there _ _ _ hne _ => exact absurd rfl hne
    · next hne =>
      constructor
      · intro h
        cases hys : removeFirst x ys with
        | none =>
          simp only [hys] at h
          nomatch h
        | some ys'' =>
          simp only [hys] at h
          injection h with hl'
          cases hl'
          exact RemoveFirst.there y ys _ hne ((ih _).mp hys)
      · intro h
        cases h with
        | here => exact absurd rfl hne
        | there _ _ ys' _ hR =>
          simp only [(ih ys').mpr hR]

theorem RemoveFirst.unique {α : Type u} {x : α} {l l₁ l₂ : List α}
    (h₁ : RemoveFirst x l l₁) (h₂ : RemoveFirst x l l₂) : l₁ = l₂ := by
  induction h₁ generalizing l₂ with
  | here ys =>
    cases h₂ with
    | here => rfl
    | there _ _ _ hne _ => exact absurd rfl hne
  | there y ys ys' hne hR ih =>
    cases h₂ with
    | here => exact absurd rfl hne
    | there _ _ ys₂ _ hR₂ => exact congrArg (firstElement y) (ih hR₂)

instance decidableRemoveFirst {α : Type u} [DecidableEq α] (x : α) (l l' : List α) :
    Decidable (RemoveFirst x l l') := by
  cases h : removeFirst x l with
  | none =>
    exact isFalse fun hR => by
      have hsome := (removeFirst_eq_some_iff x l l').mpr hR
      rw [h] at hsome
      nomatch hsome
  | some l'' =>
    match decEq l' l'' with
    | isTrue heq =>
      exact isTrue (heq ▸ (removeFirst_eq_some_iff x l l'').mp h)
    | isFalse hne =>
      exact isFalse fun hR =>
        hne (RemoveFirst.unique hR ((removeFirst_eq_some_iff x l l'').mp h))

/-- Two lists contain the same elements, possibly in a different order. -/
inductive Reordering {α : Type u} : List α → List α → Prop where
  | empty : Reordering empty empty
  | cons (x : α) (xs ys ys' : List α) :
      RemoveFirst x ys ys' → Reordering xs ys' →
        Reordering (firstElement x xs) ys

instance decidableReordering {α : Type u} [DecidableEq α] :
    (a b : List α) → Decidable (Reordering a b)
  | empty, empty => isTrue Reordering.empty
  | empty, firstElement _ _ => isFalse fun h => by cases h
  | firstElement x xs, ys =>
    match hrem : removeFirst x ys with
    | none =>
      isFalse fun h => by
        cases h with
        | cons _x _xs _ys ysRem hR _hr =>
          have hsome := (removeFirst_eq_some_iff x ys ysRem).mpr hR
          rw [hrem] at hsome
          nomatch hsome
    | some ys' =>
      match decidableReordering xs ys' with
      | isTrue hr =>
        isTrue (Reordering.cons x xs ys ys' ((removeFirst_eq_some_iff x ys ys').mp hrem) hr)
      | isFalse hnr =>
        isFalse fun h => by
          cases h with
          | cons _x _xs _ys ysRem hR hr =>
            have heq : ysRem = ys' :=
              RemoveFirst.unique hR ((removeFirst_eq_some_iff x ys ys').mp hrem)
            exact hnr (heq ▸ hr)

/-- `Reordering` is reflexive: every list is a reordering of itself. -/
theorem reordering_reflexive {α : Type u} (a : List α) : Reordering a a := by
  induction a with
  | empty => exact Reordering.empty
  | firstElement x xs ih =>
    exact Reordering.cons x xs (firstElement x xs) xs (RemoveFirst.here xs) ih

/-- If `ys'` is `ys` with `x` removed and is a reordering of `xs`, then `ys` is a
reordering of `firstElement x xs`. -/
theorem reordering_of_RemoveFirst_reordering {α : Type u} {x : α}
    {ys ys' xs : List α} (hrem : RemoveFirst x ys ys')
    (hr : Reordering ys' xs) : Reordering ys (firstElement x xs) := by
  induction hrem generalizing xs with
  | here ys' =>
    exact Reordering.cons x ys' (firstElement x xs) xs (RemoveFirst.here xs) hr
  | there y zs zs' hne _hremX ih =>
    cases hr with
    | cons _y _zs' _xs xs' hremY hr' =>
      exact Reordering.cons y zs (firstElement x xs) (firstElement x xs')
        (RemoveFirst.there x xs xs' (Ne.symm hne) hremY) (ih hr')

/-- `Reordering` is commutative: if `a` is a reordering of `b`, then `b` is a
reordering of `a`. -/
theorem reordering_commutative {α : Type u} {a b : List α}
    (h : Reordering a b) : Reordering b a := by
  induction h with
  | empty => exact Reordering.empty
  | cons x xs ys ys' hrem _hr ih =>
    exact reordering_of_RemoveFirst_reordering hrem ih

/-- Removing `x` and then a distinct `y` can be done in the opposite order with
the same final remainder. -/
theorem RemoveFirst.swap {α : Type u} {x y : α} {l lx lxy : List α}
    (hne : x ≠ y) (hx : RemoveFirst x l lx) (hy : RemoveFirst y lx lxy) :
    ∃ ly, RemoveFirst y l ly ∧ RemoveFirst x ly lxy := by
  induction hx generalizing lxy with
  | here lx =>
    exact ⟨firstElement x lxy,
      RemoveFirst.there x lx lxy (Ne.symm hne) hy,
      RemoveFirst.here lxy⟩
  | there z zs zs' hne_xz hremX ih =>
    cases hy with
    | here =>
      exact ⟨zs, RemoveFirst.here zs, hremX⟩
    | there _ _ zs'' hne_yz hremY =>
      obtain ⟨zs_y, hY, hX⟩ := ih hremY
      exact ⟨firstElement z zs_y,
        RemoveFirst.there z zs zs_y hne_yz hY,
        RemoveFirst.there z zs_y zs'' hne_xz hX⟩

/-- If `ys` is a reordering of `c` and `ys'` is `ys` with `x` removed, then there
is a corresponding removal of `x` from `c` whose remainder is a reordering of
`ys'`. -/
theorem exists_RemoveFirst_of_reordering_RemoveFirst {α : Type u} {x : α}
    {ys ys' c : List α} (hrem : RemoveFirst x ys ys') (hr : Reordering ys c) :
    ∃ c', RemoveFirst x c c' ∧ Reordering ys' c' := by
  induction hr generalizing ys' with
  | empty => cases hrem
  | cons y zs c c'' hremY hrZ ih =>
    cases hrem with
    | here =>
      exact ⟨c'', hremY, hrZ⟩
    | there _ _ zs' hne hremX =>
      obtain ⟨c''', hremX', hr'⟩ := ih hremX
      obtain ⟨c_mid, hremX_c, hremY_mid⟩ := RemoveFirst.swap (Ne.symm hne) hremY hremX'
      exact ⟨c_mid, hremX_c, Reordering.cons y zs' c_mid c''' hremY_mid hr'⟩

/-- `Reordering` is transitive: if `a` is a reordering of `b` and `b` is a
reordering of `c`, then `a` is a reordering of `c`. -/
theorem reordering_transitive {α : Type u} {a b c : List α}
    (hab : Reordering a b) (hbc : Reordering b c) : Reordering a c := by
  induction hab generalizing c with
  | empty =>
    cases hbc
    exact Reordering.empty
  | cons x xs _ys ys' hrem _hr ih =>
    obtain ⟨c', hrem', hr'⟩ := exists_RemoveFirst_of_reordering_RemoveFirst hrem hbc
    exact Reordering.cons x xs c c' hrem' (ih hr')

def isEmpty {α : Type u} : List α → Bool
  | empty => true
  | firstElement _ _ => false


example {α : Type} : isEmpty (empty : List α) = true := rfl
example {α : Type} (x : α) : isEmpty (firstElement x empty) = false := rfl
example {α : Type} (x y : α) : isEmpty (firstElement x (firstElement y empty)) = false := rfl

def append {α : Type u} (l : List α) (x : α) : List α :=
  match l with
  | empty => firstElement x empty
  | firstElement y ys => firstElement y (append ys x)

/-- Concatenate two lists: the elements of `a` followed by the elements of `b`. -/
def concatenate {α : Type u} (a b : List α) : List α :=
  match a with
  | empty => b
  | firstElement x xs => firstElement x (concatenate xs b)

def length {α : Type u} : List α → Numbers.CardinalNatural.Peano
  | empty => Numbers.CardinalNatural.Peano.zero
  | firstElement _ ds => ds.length + Numbers.CardinalNatural.Peano.one

theorem length_firstElement {α : Type u} (x : α) (xs : List α) :
    (firstElement x xs).length = xs.length.successor :=
  Numbers.CardinalNatural.Peano.add_one xs.length

theorem length_ne_zero_of_ne_empty {α : Type u} {a : List α}
    (h : a ≠ empty) : a.length ≠ Numbers.CardinalNatural.Peano.zero := by
  cases a with
  | empty => exact False.elim (h rfl)
  | firstElement _ _ =>
    rw [length_firstElement]
    exact Numbers.CardinalNatural.Peano.successor_ne_zero _

/-- Lifts a relation `α → β → Prop` to lists by requiring equal length and
related elements in corresponding positions. -/
inductive SameLengthElementwiseRelation {α : Type u} {β : Type v}
    (r : α → β → Prop) : List α → List β → Prop where
  | empty : SameLengthElementwiseRelation r empty empty
  | firstElement {x : α} {y : β} {xs : List α} {ys : List β} :
      r x y → SameLengthElementwiseRelation r xs ys →
        SameLengthElementwiseRelation r (firstElement x xs) (firstElement y ys)

theorem SameLengthElementwiseRelation.trans {α : Type u} {β : Type v} {γ : Type w}
    {r : α → β → Prop} {s : β → γ → Prop} {t : α → γ → Prop}
    (hcomp : ∀ {x y z}, r x y → s y z → t x z)
    {as : List α} {bs : List β} {cs : List γ}
    (hab : SameLengthElementwiseRelation r as bs)
    (hbc : SameLengthElementwiseRelation s bs cs) :
    SameLengthElementwiseRelation t as cs := by
  induction hab generalizing cs with
  | empty =>
    cases hbc with
    | empty => exact SameLengthElementwiseRelation.empty
  | firstElement hr hxs ih =>
    cases hbc with
    | firstElement hs hys =>
      exact SameLengthElementwiseRelation.firstElement (hcomp hr hs) (ih hys)

theorem SameLengthElementwiseRelation.symm {α : Type u} {β : Type v}
    {r : α → β → Prop} {s : β → α → Prop}
    (hsymm : ∀ {x y}, r x y → s y x)
    {as : List α} {bs : List β} (h : SameLengthElementwiseRelation r as bs) :
    SameLengthElementwiseRelation s bs as := by
  induction h with
  | empty => exact SameLengthElementwiseRelation.empty
  | firstElement hr _ ih =>
    exact SameLengthElementwiseRelation.firstElement (hsymm hr) ih

/-- The number of unmasked (`some`) entries in a list of optional values. -/
def unmaskedCount {α : Type u} : List (Option α) → Numbers.CardinalNatural.Peano
  | empty => Numbers.CardinalNatural.Peano.zero
  | firstElement none rest => unmaskedCount rest
  | firstElement (some _) rest =>
      unmaskedCount rest + Numbers.CardinalNatural.Peano.one

def padAtStart {α : Type u} (l : List α) (paddingValue : α) (n : Numbers.CardinalNatural.Peano) : List α :=
  match n with
  | .zero => l
  | .successor n' => padAtStart (.firstElement paddingValue l) paddingValue n'

example {α : Type} (l : List α) (paddingValue : α) :
  padAtStart l paddingValue Numbers.CardinalNatural.Peano.zero = l := rfl

example {α : Type} (l : List α) (paddingValue : α) :
  padAtStart l paddingValue (Numbers.CardinalNatural.Peano.successor Numbers.CardinalNatural.Peano.zero) = firstElement paddingValue l := rfl

example {α : Type} (l : List α) (paddingValue : α) :
  padAtStart l paddingValue (Numbers.CardinalNatural.Peano.successor (Numbers.CardinalNatural.Peano.successor Numbers.CardinalNatural.Peano.zero)) = firstElement paddingValue (firstElement paddingValue l) := rfl

def padAtEnd {α : Type u} (l : List α) (paddingValue : α) (n : Numbers.CardinalNatural.Peano) : List α :=
  match l with
  | .empty =>
    match n with
    | .zero => .empty
    | .successor n' => .firstElement paddingValue (padAtEnd .empty paddingValue n')
  | .firstElement d ds => .firstElement d (padAtEnd ds paddingValue n)

def padAtStartToSameLength {α : Type u} (l1 l2 : List α) (paddingValue : α) :
  (List α × List α) :=
  let len1 := l1.length
  let len2 := l2.length
  match h : ZeroMath.Numbers.CardinalNatural.Peano.isLessThan len2 len1 with
  | true =>
    have h_le : len2 ≤ len1 := Numbers.CardinalNatural.Peano.isLessThan_true_implies_le h
    (l1, padAtStart l2 paddingValue (Numbers.CardinalNatural.Peano.subtract len1 len2 h_le))
  | false =>
    have h_le : len1 ≤ len2 := Numbers.CardinalNatural.Peano.isLessThan_false_implies_le h
    (padAtStart l1 paddingValue (Numbers.CardinalNatural.Peano.subtract len2 len1 h_le), l2)

abbrev SameLength {α : Type u} (a b : List α) : Prop := a.length = b.length

theorem sameLength_commutative {α : Type u} {a b : List α}
    (h : SameLength a b) : SameLength b a :=
  h.symm

theorem sameLength_firstElement {α : Type u} {da db : α} {das dbs : List α}
    (h : SameLength das dbs) :
    SameLength (firstElement da das) (firstElement db dbs) := by
  simp only [SameLength, length, h]

theorem sameLength_of_firstElement {α : Type u} {da db : α} {das dbs : List α}
    (h : SameLength (firstElement da das) (firstElement db dbs)) :
    SameLength das dbs :=
  Numbers.CardinalNatural.Peano.add_right_cancel
    Numbers.CardinalNatural.Peano.one _ _ h

/-- Induction principle matching the former inductive `SameLength`. -/
theorem SameLength.induction {α : Type u}
    {motive : (a b : List α) → SameLength a b → Prop}
    (empty : motive empty empty rfl)
    (firstElement : ∀ {da db : α} {das dbs : List α} (h : SameLength das dbs),
      motive das dbs h →
      motive (firstElement da das) (firstElement db dbs) (sameLength_firstElement h))
    {a b : List α} (h : SameLength a b) : motive a b h := by
  induction a generalizing b with
  | empty =>
    cases b with
    | empty => exact empty
    | firstElement _ _ => cases h
  | firstElement da das ih =>
    cases b with
    | empty => cases h
    | firstElement db dbs =>
      exact firstElement (sameLength_of_firstElement h)
        (ih (sameLength_of_firstElement h))

@[simp]
theorem padAtStart_length {α : Type u} (l : Sequences.List α)
  (paddingValue : α) (n : Numbers.CardinalNatural.Peano) :
  length (padAtStart l paddingValue n) = length l + n := by
  induction n generalizing l with
  | zero => rfl
  | successor n' ih =>
    simp only [padAtStart, ih, length, Numbers.CardinalNatural.Peano.add_associative,
      Numbers.CardinalNatural.Peano.one_add]

@[simp]
theorem padAtStart_zero {α : Type u} (l : List α) (paddingValue : α) :
  padAtStart l paddingValue Numbers.CardinalNatural.Peano.zero = l := rfl

theorem padAtStart_anyElement {α : Type u} {p : α → Prop} {l : List α}
  (h : AnyElement p l) (paddingValue : α) (n : Numbers.CardinalNatural.Peano) :
  AnyElement p (padAtStart l paddingValue n) := by
  induction n generalizing l with
  | zero =>
      exact h
  | successor n' ih =>
      unfold padAtStart
      exact ih (AnyElement.notFirst paddingValue l h)

theorem padAtStartToSameLength_commutative {α : Type u} (a b : List α) (paddingValue : α) :
  padAtStartToSameLength b a paddingValue =
    ((padAtStartToSameLength a b paddingValue).2, (padAtStartToSameLength a b paddingValue).1) := by
  unfold padAtStartToSameLength
  dsimp only
  split
  · next h_a_lt_b =>
    split
    · next h_b_lt_a =>
      have hlt_ab := (Numbers.CardinalNatural.Peano.isLessThan_eq_true_iff_lt _ _).mp h_a_lt_b
      have hlt_ba := (Numbers.CardinalNatural.Peano.isLessThan_eq_true_iff_lt _ _).mp h_b_lt_a
      exact False.elim (Numbers.CardinalNatural.Peano.not_lt_of_lt hlt_ab hlt_ba)
    · next _ => rfl
  · next h_not_a_lt_b =>
    split
    · next _ => rfl
    · next h_not_b_lt_a =>
      have h_len_eq : length a = length b := by
        have h_not_ab : ¬ length a < length b := (Numbers.CardinalNatural.Peano.isLessThan_eq_false_iff_not_lt _ _).mp h_not_a_lt_b
        have h_not_ba : ¬ length b < length a := (Numbers.CardinalNatural.Peano.isLessThan_eq_false_iff_not_lt _ _).mp h_not_b_lt_a
        cases Numbers.CardinalNatural.Peano.trichotomy_or (length a) (length b) with
        | inl hlt => contradiction
        | inr h =>
          cases h with
          | inl heq => exact heq
          | inr hlt => contradiction
      have h_sub_ab : Numbers.CardinalNatural.Peano.subtract (length a) (length b) (Numbers.CardinalNatural.Peano.isLessThan_false_implies_le h_not_a_lt_b) = Numbers.CardinalNatural.Peano.zero := by
        exact Numbers.CardinalNatural.Peano.subtract_eq_zero_of_eq _ h_len_eq
      have h_sub_ba : Numbers.CardinalNatural.Peano.subtract (length b) (length a) (Numbers.CardinalNatural.Peano.isLessThan_false_implies_le h_not_b_lt_a) = Numbers.CardinalNatural.Peano.zero := by
        exact Numbers.CardinalNatural.Peano.subtract_eq_zero_of_eq _ h_len_eq.symm
      rw [h_sub_ab, h_sub_ba]
      rfl

theorem padAtStartToSameLength_sameLength {α : Type u} (a b : Sequences.List α) (paddingValue : α) :
  Sequences.List.SameLength (Sequences.List.padAtStartToSameLength a b paddingValue).1
    (Sequences.List.padAtStartToSameLength a b paddingValue).2 := by
  unfold Sequences.List.padAtStartToSameLength
  dsimp only
  split
  · next h_less =>
    change length a = length (padAtStart b paddingValue _)
    have h_le : Sequences.List.length b ≤ Sequences.List.length a := Numbers.CardinalNatural.Peano.isLessThan_true_implies_le h_less
    rw [padAtStart_length]
    have h_cancel := Numbers.CardinalNatural.Peano.subtract_add_cancel (Sequences.List.length a) (Sequences.List.length b) h_le
    rw [Numbers.CardinalNatural.Peano.add_commutative]
    exact h_cancel.symm
  · next h_less =>
    change length (padAtStart a paddingValue _) = length b
    have h_le : Sequences.List.length a ≤ Sequences.List.length b := Numbers.CardinalNatural.Peano.isLessThan_false_implies_le h_less
    rw [padAtStart_length]
    have h_cancel := Numbers.CardinalNatural.Peano.subtract_add_cancel (Sequences.List.length b) (Sequences.List.length a) h_le
    rw [Numbers.CardinalNatural.Peano.add_commutative]
    exact h_cancel

@[simp]
theorem padAtEnd_length {α : Type u} (l : List α) (paddingValue : α) (n : Numbers.CardinalNatural.Peano) :
    (padAtEnd l paddingValue n).length = l.length + n := by
  induction l with
  | empty =>
    induction n with
    | zero =>
      simp only [padAtEnd, length, Numbers.CardinalNatural.Peano.add_zero]
    | successor n ih =>
      simp only [padAtEnd, length, Numbers.CardinalNatural.Peano.zero_add, ih,
        Numbers.CardinalNatural.Peano.add_one]
  | firstElement d ds ih =>
    simp only [padAtEnd, length, ih, Numbers.CardinalNatural.Peano.add_one,
      Numbers.CardinalNatural.Peano.successor_add]

@[simp]
theorem append_length {α : Type u} (l : List α) (x : α) :
    (append l x).length = l.length + Numbers.CardinalNatural.Peano.one := by
  induction l with
  | empty =>
      simp only [append, length, Numbers.CardinalNatural.Peano.zero_add]
  | firstElement y ys ih =>
      simp only [append, length, ih, Numbers.CardinalNatural.Peano.add_one]

@[simp]
theorem concatenate_length {α : Type u} (a b : List α) :
    (concatenate a b).length = a.length + b.length := by
  induction a with
  | empty =>
      simp only [concatenate, length, Numbers.CardinalNatural.Peano.zero_add]
  | firstElement x xs ih =>
      simp only [concatenate, length, ih, Numbers.CardinalNatural.Peano.add_one,
        Numbers.CardinalNatural.Peano.successor_add]

theorem concatenate_empty {α : Type u} (l : List α) :
    concatenate l empty = l := by
  induction l with
  | empty => rfl
  | firstElement x xs ih =>
      simp only [concatenate, ih]

theorem concatenate_empty_left {α : Type u} (l : List α) :
    concatenate empty l = l :=
  rfl

theorem concatenate_firstElement {α : Type u} (x : α) (xs ys : List α) :
    concatenate (firstElement x xs) ys = firstElement x (concatenate xs ys) :=
  rfl

theorem concatenate_singleton {α : Type u} (x : α) (ys : List α) :
    concatenate (firstElement x empty) ys = firstElement x ys :=
  rfl

theorem concatenate_assoc {α : Type u} (a b c : List α) :
    concatenate (concatenate a b) c = concatenate a (concatenate b c) := by
  induction a with
  | empty => rfl
  | firstElement x xs ih =>
      simp only [concatenate, ih]

theorem padAtStart_ne_empty {α : Type u} {l : List α}
    (hl : l ≠ empty) (paddingValue : α) (n : Numbers.CardinalNatural.Peano) :
    padAtStart l paddingValue n ≠ empty := by
  induction n generalizing l with
  | zero =>
      exact hl
  | successor n ih =>
      unfold padAtStart
      exact ih (by simp)

theorem padAtEnd_ne_empty {α : Type u} (l : List α) (paddingValue : α)
    (n : Numbers.CardinalNatural.Peano) (hl : l ≠ empty) :
    padAtEnd l paddingValue n ≠ empty := by
  cases l with
  | empty => exact False.elim (hl rfl)
  | firstElement _ _ =>
      simp only [padAtEnd]
      intro h_empty
      cases h_empty

theorem padAtStart_empty_ne_empty_of_ne_zero {α : Type u} (paddingValue : α)
    (n : Numbers.CardinalNatural.Peano) (hn : n ≠ Numbers.CardinalNatural.Peano.zero) :
    padAtStart empty paddingValue n ≠ empty := by
  cases n with
  | zero => exact False.elim (hn rfl)
  | successor n' =>
      unfold padAtStart
      exact padAtStart_ne_empty (by simp) paddingValue n'

theorem padAtStartToSameLength_first_ne_empty {α : Type u}
    (a b : List α) (paddingValue : α) (ha : a ≠ empty) :
    (padAtStartToSameLength a b paddingValue).1 ≠ empty := by
  unfold padAtStartToSameLength
  dsimp only
  split
  · exact ha
  · exact padAtStart_ne_empty ha paddingValue _

theorem padAtStartToSameLength_first_ne_empty_of_either {α : Type u}
    (a b : List α) (paddingValue : α)
    (h : a ≠ empty ∨ b ≠ empty) :
    (padAtStartToSameLength a b paddingValue).1 ≠ empty := by
  cases h with
  | inl ha =>
      exact padAtStartToSameLength_first_ne_empty a b paddingValue ha
  | inr hb =>
      unfold padAtStartToSameLength
      dsimp only
      split
      · next hlt =>
          have hlt' : length b < length a :=
            (Numbers.CardinalNatural.Peano.isLessThan_eq_true_iff_lt _ _).mp hlt
          cases a with
          | empty => exact False.elim (Numbers.CardinalNatural.Peano.not_lt_zero _ hlt')
          | firstElement _ _ => intro h_empty; cases h_empty
      · next hfalse =>
          have h_le : length a ≤ length b :=
            Numbers.CardinalNatural.Peano.isLessThan_false_implies_le hfalse
          cases a with
          | empty =>
              cases b with
              | empty => exact False.elim (hb rfl)
              | firstElement db dbs =>
                  change padAtStart empty paddingValue
                      (Numbers.CardinalNatural.Peano.subtract
                        (firstElement db dbs).length
                        Numbers.CardinalNatural.Peano.zero h_le) ≠ empty
                  simp only [Numbers.CardinalNatural.Peano.subtract]
                  exact padAtStart_empty_ne_empty_of_ne_zero paddingValue _
                    (Numbers.CardinalNatural.Peano.successor_ne_zero _)
          | firstElement _ _ =>
              exact padAtStart_ne_empty (by simp) paddingValue _

def lastElement {α : Type u} : (l : List α) → l ≠ empty → α
  | empty, h => False.elim (h rfl)
  | firstElement d empty, _ => d
  | firstElement _ (firstElement d' ds'), _ =>
      lastElement (firstElement d' ds') (fun h => by cases h)

/-- The element at the given positive ordinal index, or `none` if the index is
out of bounds. The first element has index `one`. -/
def tryGetElement {α : Type u} :
    Numbers.OrdinalNatural.Peano → List α → Option α
  | _, empty => none
  | .one, firstElement x _xs => some x
  | .successor n, firstElement _x xs => tryGetElement n xs

example : tryGetElement Numbers.OrdinalNatural.Peano.one
    (firstElement true (firstElement false empty)) = some true := rfl
example : tryGetElement (Numbers.OrdinalNatural.Peano.successor
      Numbers.OrdinalNatural.Peano.one)
    (firstElement true (firstElement false empty)) = some false := rfl
example : tryGetElement (Numbers.OrdinalNatural.Peano.successor
      (Numbers.OrdinalNatural.Peano.successor Numbers.OrdinalNatural.Peano.one))
    (firstElement true (firstElement false empty)) = none := rfl

theorem tryGetElement_empty {α : Type u} (index : Numbers.OrdinalNatural.Peano) :
    tryGetElement (α := α) index empty = none := by
  cases index with
  | one => rfl
  | successor _ => rfl

theorem tryGetElement_one {α : Type u} (x : α) (xs : List α) :
    tryGetElement Numbers.OrdinalNatural.Peano.one (firstElement x xs) = some x :=
  rfl

theorem tryGetElement_successor {α : Type u}
    (n : Numbers.OrdinalNatural.Peano) (x : α) (xs : List α) :
    tryGetElement n.successor (firstElement x xs) = tryGetElement n xs :=
  rfl

/-- The element at the given positive ordinal index, when that index does not
exceed the list's length. The first element has index `one`. -/
def getElement {α : Type u} (index : Numbers.OrdinalNatural.Peano) (l : List α)
    (hle : Numbers.CardinalNatural.Peano.fromOrdinal index ≤ l.length) : α :=
  match l with
  | empty =>
    False.elim
      (Numbers.CardinalNatural.Peano.fromOrdinal_ne_zero index
        (Numbers.CardinalNatural.Peano.eq_zero_of_le_zero _ hle))
  | firstElement x xs =>
    match index with
    | .one => x
    | .successor n =>
      getElement n xs <| by
        have hle' :
            (Numbers.CardinalNatural.Peano.fromOrdinal n).successor ≤
              xs.length.successor := by
          rw [← length_firstElement x xs]
          exact hle
        exact Numbers.CardinalNatural.Peano.le_of_successor_le_successor hle'

theorem tryGetElement_eq_none_iff_length_lt {α : Type u}
    (index : Numbers.OrdinalNatural.Peano) (l : List α) :
    tryGetElement index l = none ↔
      l.length < Numbers.CardinalNatural.Peano.fromOrdinal index := by
  induction l generalizing index with
  | empty =>
    constructor
    · intro _
      exact Numbers.CardinalNatural.Peano.lt_of_le_of_ne
        (Numbers.CardinalNatural.Peano.zero_le _)
        (Numbers.CardinalNatural.Peano.fromOrdinal_ne_zero index).symm
    · intro _
      exact tryGetElement_empty index
  | firstElement x xs ih =>
    cases index with
    | one =>
      constructor
      · intro h
        cases h
      · intro hlt
        exact False.elim
          (Numbers.CardinalNatural.Peano.not_lt_zero xs.length
            (Numbers.CardinalNatural.Peano.lt_of_successor_lt_successor
              (length_firstElement x xs ▸ hlt)))
    | successor n =>
      have hiff := ih n
      constructor
      · intro hnone
        change (firstElement x xs).length <
          (Numbers.CardinalNatural.Peano.fromOrdinal n).successor
        rw [length_firstElement]
        exact Numbers.CardinalNatural.Peano.successor_lt_successor (hiff.mp hnone)
      · intro hlt
        exact hiff.mpr
          (Numbers.CardinalNatural.Peano.lt_of_successor_lt_successor
            (length_firstElement x xs ▸ hlt))

theorem tryGetElement_isSome_iff_length_le {α : Type u}
    (index : Numbers.OrdinalNatural.Peano) (l : List α) :
    (∃ x, tryGetElement index l = some x) ↔
      Numbers.CardinalNatural.Peano.fromOrdinal index ≤ l.length := by
  constructor
  · intro ⟨_, hx⟩
    have hne : tryGetElement index l ≠ none := by
      intro hnone
      rw [hnone] at hx
      cases hx
    have hnotlt :
        ¬ l.length < Numbers.CardinalNatural.Peano.fromOrdinal index :=
      fun hlt =>
        hne ((tryGetElement_eq_none_iff_length_lt index l).mpr hlt)
    exact Numbers.CardinalNatural.Peano.not_lt_implies_le hnotlt
  · intro hle
    cases h : tryGetElement index l with
    | none =>
      exact False.elim
        (Numbers.CardinalNatural.Peano.not_le_of_gt
          ((tryGetElement_eq_none_iff_length_lt index l).mp h) hle)
    | some x =>
      exact ⟨x, rfl⟩

theorem tryGetElement_eq_some_getElement {α : Type u}
    (index : Numbers.OrdinalNatural.Peano) (l : List α)
    (hle : Numbers.CardinalNatural.Peano.fromOrdinal index ≤ l.length) :
    tryGetElement index l = some (getElement index l hle) := by
  induction l generalizing index with
  | empty =>
    exact False.elim
      (Numbers.CardinalNatural.Peano.fromOrdinal_ne_zero index
        (Numbers.CardinalNatural.Peano.eq_zero_of_le_zero _ hle))
  | firstElement x xs ih =>
    cases index with
    | one =>
      rfl
    | successor n =>
      exact ih n _

theorem in_of_tryGetElement {α : Type u} {index : Numbers.OrdinalNatural.Peano}
    {l : List α} {x : α} (h : tryGetElement index l = some x) : In x l := by
  induction l generalizing index with
  | empty =>
    rw [tryGetElement_empty] at h
    cases h
  | firstElement y ys ih =>
    cases index with
    | one =>
      exact AnyElement.first y ys
        (Option.some.inj (tryGetElement_one y ys ▸ h))
    | successor n =>
      exact AnyElement.notFirst y ys (ih h)

theorem anyElement_of_In {α : Type u} {p : α → Prop} {x : α} {l : List α}
    (hin : AnyElement (fun y => y = x) l) (hp : p x) : AnyElement p l := by
  induction hin with
  | first d ds heq =>
    exact AnyElement.first d ds (heq ▸ hp)
  | notFirst d ds _ ih =>
    exact AnyElement.notFirst d ds ih

/-- Replace the element at the given positive ordinal index, or `none` if the
index is out of bounds. The first element has index `one`. -/
def trySetElement {α : Type u} :
    Numbers.OrdinalNatural.Peano → α → List α → Option (List α)
  | _, _value, empty => none
  | .one, value, firstElement _x xs => some (firstElement value xs)
  | .successor n, value, firstElement x xs =>
    match trySetElement n value xs with
    | none => none
    | some xs' => some (firstElement x xs')

example : trySetElement Numbers.OrdinalNatural.Peano.one false
    (firstElement true (firstElement true empty)) =
      some (firstElement false (firstElement true empty)) := rfl
example : trySetElement (Numbers.OrdinalNatural.Peano.successor
      Numbers.OrdinalNatural.Peano.one) false
    (firstElement true (firstElement true empty)) =
      some (firstElement true (firstElement false empty)) := rfl
example : trySetElement (Numbers.OrdinalNatural.Peano.successor
      (Numbers.OrdinalNatural.Peano.successor Numbers.OrdinalNatural.Peano.one))
    false (firstElement true (firstElement true empty)) = none := rfl

theorem trySetElement_empty {α : Type u}
    (index : Numbers.OrdinalNatural.Peano) (value : α) :
    trySetElement index value empty = none := by
  cases index with
  | one => rfl
  | successor _ => rfl

theorem trySetElement_successor {α : Type u}
    (n : Numbers.OrdinalNatural.Peano) (value : α) (x : α) (xs : List α) :
    trySetElement n.successor value (firstElement x xs) =
      match trySetElement n value xs with
      | none => none
      | some xs' => some (firstElement x xs') :=
  rfl

/-- Replace the element at the given positive ordinal index, when that index
does not exceed the list's length. The first element has index `one`. -/
def setElement {α : Type u} (index : Numbers.OrdinalNatural.Peano) (value : α)
    (l : List α)
    (hle : Numbers.CardinalNatural.Peano.fromOrdinal index ≤ l.length) : List α :=
  match l with
  | empty =>
    False.elim
      (Numbers.CardinalNatural.Peano.fromOrdinal_ne_zero index
        (Numbers.CardinalNatural.Peano.eq_zero_of_le_zero _ hle))
  | firstElement x xs =>
    match index with
    | .one => firstElement value xs
    | .successor n =>
      firstElement x (setElement n value xs <| by
        have hle' :
            (Numbers.CardinalNatural.Peano.fromOrdinal n).successor ≤
              xs.length.successor := by
          rw [← length_firstElement x xs]
          exact hle
        exact Numbers.CardinalNatural.Peano.le_of_successor_le_successor hle')

theorem trySetElement_eq_none_iff_tryGetElement_eq_none {α : Type u}
    (index : Numbers.OrdinalNatural.Peano) (value : α) (l : List α) :
    trySetElement index value l = none ↔ tryGetElement index l = none := by
  induction l generalizing index with
  | empty =>
    constructor
    · intro _
      exact tryGetElement_empty index
    · intro _
      exact trySetElement_empty index value
  | firstElement x xs ih =>
    cases index with
    | one =>
      constructor
      · intro h
        cases h
      · intro h
        cases h
    | successor n =>
      cases hset : trySetElement n value xs with
      | none =>
        constructor
        · intro _
          exact (ih n).mp hset
        · intro _
          rw [trySetElement_successor, hset]
      | some xs' =>
        constructor
        · intro h
          rw [trySetElement_successor, hset] at h
          cases h
        · intro hnone
          have hnone' : trySetElement n value xs = none := (ih n).mpr hnone
          rw [hset] at hnone'
          cases hnone'

theorem trySetElement_eq_some_length {α : Type u}
    (index : Numbers.OrdinalNatural.Peano) (value : α) (l l' : List α)
    (h : trySetElement index value l = some l') :
    l'.length = l.length := by
  induction l generalizing index l' with
  | empty =>
    rw [trySetElement_empty] at h
    cases h
  | firstElement x xs ih =>
    cases index with
    | one =>
      cases h
      rfl
    | successor n =>
      cases hset : trySetElement n value xs with
      | none =>
        rw [trySetElement_successor, hset] at h
        cases h
      | some xs' =>
        rw [trySetElement_successor, hset] at h
        cases h
        exact congrArg (fun n => n + Numbers.CardinalNatural.Peano.one) (ih n xs' hset)

theorem tryGetElement_of_trySetElement {α : Type u}
    (index : Numbers.OrdinalNatural.Peano) (value : α) (l l' : List α)
    (h : trySetElement index value l = some l') :
    tryGetElement index l' = some value := by
  induction l generalizing index l' with
  | empty =>
    rw [trySetElement_empty] at h
    cases h
  | firstElement x xs ih =>
    cases index with
    | one =>
      cases h
      rfl
    | successor n =>
      cases hset : trySetElement n value xs with
      | none =>
        rw [trySetElement_successor, hset] at h
        cases h
      | some xs' =>
        rw [trySetElement_successor, hset] at h
        cases h
        exact ih n xs' hset

theorem exists_tryGetElement_of_trySetElement {α : Type u}
    (index : Numbers.OrdinalNatural.Peano) (value : α) (l l' : List α)
    (h : trySetElement index value l = some l') :
    ∃ old, tryGetElement index l = some old := by
  induction l generalizing index l' with
  | empty =>
    rw [trySetElement_empty] at h
    cases h
  | firstElement x xs ih =>
    cases index with
    | one =>
      exact ⟨x, rfl⟩
    | successor n =>
      cases hset : trySetElement n value xs with
      | none =>
        rw [trySetElement_successor, hset] at h
        cases h
      | some xs' =>
        rw [trySetElement_successor, hset] at h
        cases h
        exact ih n xs' hset

theorem in_trySetElement_of_in {α : Type u}
    (index : Numbers.OrdinalNatural.Peano) (value : α) (l l' : List α)
    (h : trySetElement index value l = some l') {x : α} (hx : In x l') :
    x = value ∨ In x l := by
  induction l generalizing index l' with
  | empty =>
    rw [trySetElement_empty] at h
    cases h
  | firstElement y ys ih =>
    cases index with
    | one =>
      cases h
      cases hx with
      | first _ _ heq =>
        exact Or.inl heq.symm
      | notFirst _ _ hin =>
        exact Or.inr (AnyElement.notFirst y ys hin)
    | successor n =>
      cases hset : trySetElement n value ys with
      | none =>
        rw [trySetElement_successor, hset] at h
        cases h
      | some ys' =>
        rw [trySetElement_successor, hset] at h
        cases h
        cases hx with
        | first _ _ heq =>
          exact Or.inr (AnyElement.first y ys heq)
        | notFirst _ _ hin =>
          cases ih n ys' hset hin with
          | inl hval => exact Or.inl hval
          | inr hinys => exact Or.inr (AnyElement.notFirst y ys hinys)

theorem trySetElement_eq_some_setElement {α : Type u}
    (index : Numbers.OrdinalNatural.Peano) (value : α) (l : List α)
    (hle : Numbers.CardinalNatural.Peano.fromOrdinal index ≤ l.length) :
    trySetElement index value l = some (setElement index value l hle) := by
  induction l generalizing index with
  | empty =>
    exact False.elim
      (Numbers.CardinalNatural.Peano.fromOrdinal_ne_zero index
        (Numbers.CardinalNatural.Peano.eq_zero_of_le_zero _ hle))
  | firstElement x xs ih =>
    cases index with
    | one =>
      rfl
    | successor n =>
      have hle' :
          Numbers.CardinalNatural.Peano.fromOrdinal n ≤ xs.length := by
        have hsucc :
            (Numbers.CardinalNatural.Peano.fromOrdinal n).successor ≤
              xs.length.successor := by
          rw [← length_firstElement x xs]
          exact hle
        exact Numbers.CardinalNatural.Peano.le_of_successor_le_successor hsucc
      rw [trySetElement_successor, ih n hle']
      rfl

theorem setElement_length {α : Type u}
    (index : Numbers.OrdinalNatural.Peano) (value : α) (l : List α)
    (hle : Numbers.CardinalNatural.Peano.fromOrdinal index ≤ l.length) :
    (setElement index value l hle).length = l.length :=
  trySetElement_eq_some_length index value l (setElement index value l hle)
    (trySetElement_eq_some_setElement index value l hle)

theorem tryGetElement_setElement {α : Type u}
    (index : Numbers.OrdinalNatural.Peano) (value : α) (l : List α)
    (hle : Numbers.CardinalNatural.Peano.fromOrdinal index ≤ l.length) :
    tryGetElement index (setElement index value l hle) = some value :=
  tryGetElement_of_trySetElement index value l (setElement index value l hle)
    (trySetElement_eq_some_setElement index value l hle)

/-- A list of `n` copies of `value`. -/
def repeatValue {α : Type u} (value : α) : Numbers.CardinalNatural.Peano → List α
  | Numbers.CardinalNatural.Peano.zero => empty
  | Numbers.CardinalNatural.Peano.successor n =>
    firstElement value (repeatValue value n)

theorem repeatValue_zero {α : Type u} (value : α) :
    repeatValue value Numbers.CardinalNatural.Peano.zero = empty :=
  rfl

theorem repeatValue_successor {α : Type u} (value : α)
    (n : Numbers.CardinalNatural.Peano) :
    repeatValue value n.successor = firstElement value (repeatValue value n) :=
  rfl

theorem repeatValue_length {α : Type u} (value : α)
    (n : Numbers.CardinalNatural.Peano) :
    (repeatValue value n).length = n := by
  induction n with
  | zero => rfl
  | successor n ih =>
    simp only [repeatValue_successor, length_firstElement, ih]

theorem repeatValue_AllElements {α : Type u} (value : α)
    (n : Numbers.CardinalNatural.Peano) :
    AllElements (fun x => x = value) (repeatValue value n) := by
  induction n with
  | zero => exact AllElements.empty
  | successor n ih =>
    exact AllElements.firstElement value (repeatValue value n) rfl ih

theorem repeatValue_eq_empty_iff {α : Type u} (value : α)
    (n : Numbers.CardinalNatural.Peano) :
    repeatValue value n = empty ↔ n = Numbers.CardinalNatural.Peano.zero := by
  constructor
  · intro h
    cases n with
    | zero => rfl
    | successor n => cases h
  · intro h
    cases h
    rfl

theorem repeatValue_ne_empty {α : Type u} (value : α)
    (n : Numbers.CardinalNatural.Peano)
    (h : n ≠ Numbers.CardinalNatural.Peano.zero) :
    repeatValue value n ≠ empty :=
  fun heq => h ((repeatValue_eq_empty_iff value n).mp heq)

/-- The common value of a non-empty list whose elements are all equal. -/
def tryRepeatedValue {α : Type u} [DecidableEq α] : List α → Option α
  | empty => none
  | firstElement x xs =>
    if allElements (fun y => decide (y = x)) xs then some x else none

theorem tryRepeatedValue_eq_some_iff {α : Type u} [DecidableEq α]
    (value : α) : (l : List α) →
    tryRepeatedValue l = some value ↔
      l ≠ empty ∧ AllElements (fun x => x = value) l
  | empty => by
    simp only [tryRepeatedValue]
    constructor
    · intro h
      cases h
    · intro ⟨hne, _⟩
      exact False.elim (hne rfl)
  | firstElement x xs => by
    simp only [tryRepeatedValue]
    constructor
    · intro h
      split at h
      · next hall =>
        have hx : x = value := Option.some.inj h
        refine And.intro (fun hempty => nomatch hempty) ?_
        exact hx ▸ AllElements.firstElement x xs rfl
          ((allElements_decide_eq_true_iff (fun y => y = x) xs).mp hall)
      · next => cases h
    · intro ⟨_, hall⟩
      have hx : x = value :=
        AllElements.head (p := fun y => y = value) hall
      have hxs : AllElements (fun y => y = x) xs :=
        hx.symm ▸ AllElements.tail (p := fun y => y = value) hall
      have htrue : allElements (fun y => decide (y = x)) xs = true :=
        (allElements_decide_eq_true_iff (fun y => y = x) xs).mpr hxs
      rw [htrue]
      exact congrArg some hx

/-- The common value of a non-empty list whose elements are all equivalent. -/
def tryEquivalentRepeatedValue {α : Type u} [Setoid α]
    [DecidableRel (α := α) (· ≈ ·)] : List α → Option α
  | empty => none
  | firstElement x xs =>
    if allElements (fun y => decide (y ≈ x)) xs then some x else none

theorem AllElements_equivalent_of_equivalent {α : Type u} [Setoid α]
    {a b : α} (hab : a ≈ b) {l : List α}
    (h : AllElements (fun x => x ≈ b) l) :
    AllElements (fun x => x ≈ a) l := by
  induction h with
  | empty => exact AllElements.empty
  | firstElement x xs hx _ ih =>
    exact AllElements.firstElement x xs (Setoid.trans hx (Setoid.symm hab)) ih

theorem tryEquivalentRepeatedValue_eq_some_of_AllElements {α : Type u}
    [Setoid α] [DecidableRel (α := α) (· ≈ ·)]
    (value : α) (l : List α) (hne : l ≠ empty)
    (h : AllElements (fun x => x ≈ value) l) :
    ∃ x, x ≈ value ∧ tryEquivalentRepeatedValue l = some x := by
  match l with
  | empty => exact False.elim (hne rfl)
  | firstElement x xs =>
    have hx := AllElements.head h
    have hxs := AllElements.tail h
    have htail : AllElements (fun y => y ≈ x) xs :=
      AllElements_equivalent_of_equivalent hx hxs
    have htrue : allElements (fun y => decide (y ≈ x)) xs = true :=
      (allElements_decide_eq_true_iff (fun y => y ≈ x) xs).mpr htail
    refine ⟨x, hx, ?_⟩
    simp only [tryEquivalentRepeatedValue]
    split
    · rfl
    · next hfalse =>
      exact absurd htrue hfalse

theorem tryRepeatedValue_repeatValue {α : Type u} [DecidableEq α]
    (value : α) (n : Numbers.CardinalNatural.Peano)
    (h : n ≠ Numbers.CardinalNatural.Peano.zero) :
    tryRepeatedValue (repeatValue value n) = some value :=
  (tryRepeatedValue_eq_some_iff value (repeatValue value n)).mpr
    ⟨repeatValue_ne_empty value n h, repeatValue_AllElements value n⟩

example {α : Type} (value : α) :
    repeatValue value Numbers.CardinalNatural.Peano.zero = empty :=
  rfl

example :
    repeatValue true Numbers.CardinalNatural.Peano.one =
      firstElement true empty :=
  rfl

example :
    repeatValue false Numbers.CardinalNatural.Peano.two =
      firstElement false (firstElement false empty) :=
  rfl

example :
    tryRepeatedValue (repeatValue true Numbers.CardinalNatural.Peano.three) =
      some true :=
  rfl

example :
    tryRepeatedValue
      (firstElement true (firstElement false empty)) = (none : Option Bool) :=
  rfl

end List

end ZeroMath.Sequences
