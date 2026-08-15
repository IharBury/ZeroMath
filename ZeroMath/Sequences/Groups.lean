import ZeroMath.Sequences.List

namespace ZeroMath.Sequences

/-- A collection of objects that share a single feature value. -/
structure Group (α : Type u) (β : Type v) where
  feature : β
  objects : List α

deriving instance DecidableEq for Group

namespace List

/-- Objects of `l` whose `feature` equals `key`, in their original order. -/
def elementsWithFeature {α : Type u} {β : Type v} [DecidableEq β]
    (feature : α → β) (key : β) : List α → List α
  | empty => empty
  | firstElement x xs =>
    if feature x = key then
      firstElement x (elementsWithFeature feature key xs)
    else
      elementsWithFeature feature key xs

/-- Objects of `l` whose `feature` differs from `key`, in their original order. -/
def elementsWithoutFeature {α : Type u} {β : Type v} [DecidableEq β]
    (feature : α → β) (key : β) : List α → List α
  | empty => empty
  | firstElement x xs =>
    if feature x = key then
      elementsWithoutFeature feature key xs
    else
      firstElement x (elementsWithoutFeature feature key xs)

example {α : Type} (feature : α → Bool) (key : Bool) :
    elementsWithFeature feature key empty = empty := rfl
example :
    elementsWithFeature (fun b : Bool => b) true
      (firstElement true (firstElement false (firstElement true empty))) =
      firstElement true (firstElement true empty) := rfl
example :
    elementsWithoutFeature (fun b : Bool => b) true
      (firstElement true (firstElement false (firstElement true empty))) =
      firstElement false empty := rfl

/-- `SplitByFeature feature key l matched rest` means `matched` is the objects
of `l` whose feature is `key` and `rest` is the remainder, both in original
order. -/
inductive SplitByFeature {α : Type u} {β : Type v} (feature : α → β) (key : β) :
    List α → List α → List α → Prop where
  | hasFeature (x : α) (xs matched rest : List α) :
      feature x = key →
      SplitByFeature feature key xs matched rest →
      SplitByFeature feature key (firstElement x xs) (firstElement x matched) rest
  | lacksFeature (x : α) (xs matched rest : List α) :
      feature x ≠ key →
      SplitByFeature feature key xs matched rest →
      SplitByFeature feature key (firstElement x xs) matched (firstElement x rest)
  | empty : SplitByFeature feature key empty empty empty

def splitByFeature {α : Type u} {β : Type v} [DecidableEq β]
    (feature : α → β) (key : β) (l : List α) : List α × List α :=
  (elementsWithFeature feature key l, elementsWithoutFeature feature key l)

theorem elements_of_SplitByFeature {α : Type u} {β : Type v} [DecidableEq β]
    {feature : α → β} {key : β} {l matched rest : List α}
    (h : SplitByFeature feature key l matched rest) :
    elementsWithFeature feature key l = matched ∧
      elementsWithoutFeature feature key l = rest := by
  induction h with
  | empty => exact ⟨rfl, rfl⟩
  | hasFeature x xs matched rest heq _ ih =>
    obtain ⟨hs, ho⟩ := ih
    simp only [elementsWithFeature, elementsWithoutFeature]
    split
    · exact ⟨congrArg (firstElement x) hs, ho⟩
    · next hne => exact absurd heq hne
  | lacksFeature x xs matched rest hne _ ih =>
    obtain ⟨hs, ho⟩ := ih
    simp only [elementsWithFeature, elementsWithoutFeature]
    split
    · next heq => exact absurd heq hne
    · exact ⟨hs, congrArg (firstElement x) ho⟩

theorem SplitByFeature_of_elements {α : Type u} {β : Type v} [DecidableEq β]
    (feature : α → β) (key : β) :
    (l matched rest : List α) →
    elementsWithFeature feature key l = matched →
    elementsWithoutFeature feature key l = rest →
    SplitByFeature feature key l matched rest
  | empty, matched, rest, hMatched, hRest => by
    cases hMatched
    cases hRest
    exact SplitByFeature.empty
  | firstElement x xs, matched, rest, hMatched, hRest => by
    simp only [elementsWithFeature, elementsWithoutFeature] at hMatched hRest
    split at hMatched
    · next heq =>
      split at hRest
      · next =>
        cases matched with
        | empty => cases hMatched
        | firstElement y ys =>
          injection hMatched with hy hys
          cases hy
          exact SplitByFeature.hasFeature x xs ys rest heq
            (SplitByFeature_of_elements feature key xs ys rest hys hRest)
      · next hne => exact absurd heq hne
    · next hne =>
      split at hRest
      · next heq => exact absurd heq hne
      · next =>
        cases rest with
        | empty => cases hRest
        | firstElement y ys =>
          injection hRest with hy hys
          cases hy
          exact SplitByFeature.lacksFeature x xs matched ys hne
            (SplitByFeature_of_elements feature key xs matched ys hMatched hys)

theorem splitByFeature_eq_iff {α : Type u} {β : Type v} [DecidableEq β]
    (feature : α → β) (key : β) (l matched rest : List α) :
    SplitByFeature feature key l matched rest ↔
      elementsWithFeature feature key l = matched ∧
        elementsWithoutFeature feature key l = rest := by
  constructor
  · intro h
    exact elements_of_SplitByFeature h
  · intro h
    exact SplitByFeature_of_elements feature key l matched rest h.1 h.2

instance decidableSplitByFeature {α : Type u} {β : Type v}
    [DecidableEq α] [DecidableEq β]
    (feature : α → β) (key : β) (l matched rest : List α) :
    Decidable (SplitByFeature feature key l matched rest) :=
  if h : elementsWithFeature feature key l = matched ∧
      elementsWithoutFeature feature key l = rest then
    isTrue ((splitByFeature_eq_iff feature key l matched rest).mpr h)
  else
    isFalse fun hs => h ((splitByFeature_eq_iff feature key l matched rest).mp hs)

theorem splitByFeature_matched_AllElements {α : Type u} {β : Type v}
    {feature : α → β} {key : β} {l matched rest : List α}
    (h : SplitByFeature feature key l matched rest) :
    AllElements (fun x => feature x = key) matched := by
  induction h with
  | empty => exact AllElements.empty
  | hasFeature x xs matched rest heq _ ih =>
    exact AllElements.firstElement x matched heq ih
  | lacksFeature _ _ _ _ _ _ ih => exact ih

theorem splitByFeature_rest_AllElements {α : Type u} {β : Type v}
    {feature : α → β} {key : β} {l matched rest : List α}
    (h : SplitByFeature feature key l matched rest) :
    AllElements (fun x => feature x ≠ key) rest := by
  induction h with
  | empty => exact AllElements.empty
  | hasFeature _ _ _ _ _ _ ih => exact ih
  | lacksFeature x xs matched rest hne _ ih =>
    exact AllElements.firstElement x rest hne ih

theorem splitByFeature_matched_AllElements_of {α : Type u} {β : Type v}
    {feature : α → β} {key : β} {p : α → Prop} {l matched rest : List α}
    (h : SplitByFeature feature key l matched rest)
    (hAll : AllElements p l) : AllElements p matched := by
  induction h with
  | empty => exact AllElements.empty
  | hasFeature x xs matched rest _ _ ih =>
    exact AllElements.firstElement x matched hAll.head (ih hAll.tail)
  | lacksFeature _ _ _ _ _ _ ih => exact ih hAll.tail

theorem splitByFeature_rest_AllElements_of {α : Type u} {β : Type v}
    {feature : α → β} {key : β} {p : α → Prop} {l matched rest : List α}
    (h : SplitByFeature feature key l matched rest)
    (hAll : AllElements p l) : AllElements p rest := by
  induction h with
  | empty => exact AllElements.empty
  | hasFeature _ _ _ _ _ _ ih => exact ih hAll.tail
  | lacksFeature x xs matched rest _ _ ih =>
    exact AllElements.firstElement x rest hAll.head (ih hAll.tail)

theorem splitByFeature_length {α : Type u} {β : Type v}
    {feature : α → β} {key : β} {l matched rest : List α}
    (h : SplitByFeature feature key l matched rest) :
    matched.length + rest.length = l.length := by
  induction h with
  | empty =>
    simp only [length, Numbers.CardinalNatural.Peano.add_zero]
  | hasFeature x xs matched rest _ _ ih =>
    calc
      (firstElement x matched).length + rest.length
          = (matched.length + Numbers.CardinalNatural.Peano.one) + rest.length := by
            simp only [length]
      _ = (matched.length + rest.length) + Numbers.CardinalNatural.Peano.one :=
            Numbers.CardinalNatural.Peano.add_one_commutative_right matched.length rest.length
      _ = xs.length + Numbers.CardinalNatural.Peano.one := by rw [ih]
      _ = (firstElement x xs).length := by simp only [length]
  | lacksFeature x xs matched rest _ _ ih =>
    calc
      matched.length + (firstElement x rest).length
          = matched.length + (rest.length + Numbers.CardinalNatural.Peano.one) := by
            simp only [length]
      _ = (matched.length + rest.length) + Numbers.CardinalNatural.Peano.one :=
            (Numbers.CardinalNatural.Peano.add_associative _ _ _).symm
      _ = xs.length + Numbers.CardinalNatural.Peano.one := by rw [ih]
      _ = (firstElement x xs).length := by simp only [length]

theorem elementsWithFeature_AllElements {α : Type u} {β : Type v} [DecidableEq β]
    (feature : α → β) (key : β) (l : List α) :
    AllElements (fun x => feature x = key)
      (elementsWithFeature feature key l) :=
  splitByFeature_matched_AllElements
    ((splitByFeature_eq_iff feature key l _ _).mpr ⟨rfl, rfl⟩)

theorem elementsWithoutFeature_AllElements {α : Type u} {β : Type v} [DecidableEq β]
    (feature : α → β) (key : β) (l : List α) :
    AllElements (fun x => feature x ≠ key)
      (elementsWithoutFeature feature key l) :=
  splitByFeature_rest_AllElements
    ((splitByFeature_eq_iff feature key l _ _).mpr ⟨rfl, rfl⟩)

theorem elementsWithoutFeature_length_le {α : Type u} {β : Type v} [DecidableEq β]
    (feature : α → β) (key : β) (l : List α) :
    (elementsWithoutFeature feature key l).length ≤ l.length := by
  induction l with
  | empty => exact Or.inr rfl
  | firstElement x xs ih =>
    simp only [elementsWithoutFeature]
    split
    · exact Numbers.CardinalNatural.Peano.le_trans ih
        (Or.inl Numbers.CardinalNatural.Peano.LessThan.base)
    · simp only [length]
      exact Numbers.CardinalNatural.Peano.successor_le_successor ih

/-- Peel groups using a length bound so the recursion is structural on the
cardinal fuel. The bound must be at least `l.length`. -/
def groupByFrom {α : Type u} {β : Type v} [DecidableEq β]
    (feature : α → β) :
    Numbers.CardinalNatural.Peano → List α → List (Group α β)
  | .zero, _ => empty
  | .successor _, empty => empty
  | .successor n, firstElement x xs =>
    firstElement
      { feature := feature x
        objects := firstElement x (elementsWithFeature feature (feature x) xs) }
      (groupByFrom feature n (elementsWithoutFeature feature (feature x) xs))

/-- `GroupedBy feature l groups` means `groups` partitions `l` by `feature`:
groups appear in first-occurrence order, and objects inside each group keep
their original relative order. -/
inductive GroupedBy {α : Type u} {β : Type v} (feature : α → β) :
    List α → List (Group α β) → Prop where
  | empty : GroupedBy feature empty empty
  | firstGroup (x : α) (xs matched rest : List α) (groups : List (Group α β)) :
      SplitByFeature feature (feature x) xs matched rest →
      GroupedBy feature rest groups →
      GroupedBy feature (firstElement x xs)
        (firstElement
          { feature := feature x, objects := firstElement x matched }
          groups)

theorem groupByFrom_eq_of_length_le {α : Type u} {β : Type v} [DecidableEq β]
    (feature : α → β) :
    (n : Numbers.CardinalNatural.Peano) → (l : List α) →
    l.length ≤ n →
    groupByFrom feature n l = groupByFrom feature l.length l
  | .zero, l, hle => by
    have hl : l.length = Numbers.CardinalNatural.Peano.zero := by
      cases hle with
      | inl hlt => exact False.elim (Numbers.CardinalNatural.Peano.not_lt_zero _ hlt)
      | inr heq => exact heq
    rw [hl]
  | .successor n, empty, _ => by
    simp only [length, groupByFrom]
  | .successor n, firstElement x xs, hle => by
    have hxs : xs.length ≤ n :=
      Numbers.CardinalNatural.Peano.le_of_successor_le_successor
        (by
          simp only [length] at hle
          exact hle)
    have hrest :
        (elementsWithoutFeature feature (feature x) xs).length ≤ n :=
      Numbers.CardinalNatural.Peano.le_trans
        (elementsWithoutFeature_length_le feature (feature x) xs) hxs
    have hrestXs :
        (elementsWithoutFeature feature (feature x) xs).length ≤ xs.length :=
      elementsWithoutFeature_length_le feature (feature x) xs
    simp only [groupByFrom]
    rw [length_firstElement]
    simp only [groupByFrom]
    rw [groupByFrom_eq_of_length_le feature n
          (elementsWithoutFeature feature (feature x) xs) hrest]
    rw [groupByFrom_eq_of_length_le feature xs.length
          (elementsWithoutFeature feature (feature x) xs) hrestXs]
termination_by n _ => n.toNat
decreasing_by
  · exact Nat.lt_succ_self _
  · exact Nat.lt_of_le_of_lt
      (Numbers.CardinalNatural.Peano.toNat_le_of_le hxs)
      (Nat.lt_succ_self _)

/-- Partition `l` into groups of objects that share a `feature` value. -/
def groupBy {α : Type u} {β : Type v} [DecidableEq β]
    (feature : α → β) (l : List α) : List (Group α β) :=
  groupByFrom feature l.length l

theorem groupBy_empty {α : Type u} {β : Type v} [DecidableEq β]
    (feature : α → β) : groupBy feature empty = empty := rfl

theorem groupByFrom_GroupedBy {α : Type u} {β : Type v} [DecidableEq β]
    (feature : α → β) :
    (n : Numbers.CardinalNatural.Peano) → (l : List α) →
    l.length ≤ n →
    GroupedBy feature l (groupByFrom feature n l)
  | .zero, l, hle => by
    have hl : l = empty := by
      cases l with
      | empty => rfl
      | firstElement _ _ =>
        cases hle with
        | inl hlt =>
          exact False.elim (Numbers.CardinalNatural.Peano.not_lt_zero _ hlt)
        | inr heq =>
          exact False.elim (length_ne_zero_of_ne_empty (by intro h; cases h) heq)
    cases hl
    exact GroupedBy.empty
  | .successor n, empty, _ => GroupedBy.empty
  | .successor n, firstElement x xs, hle => by
    have hxs : xs.length ≤ n :=
      Numbers.CardinalNatural.Peano.le_of_successor_le_successor
        (by
          simp only [length] at hle
          exact hle)
    have hrest :
        (elementsWithoutFeature feature (feature x) xs).length ≤ n :=
      Numbers.CardinalNatural.Peano.le_trans
        (elementsWithoutFeature_length_le feature (feature x) xs) hxs
    simp only [groupByFrom]
    exact GroupedBy.firstGroup x xs
      (elementsWithFeature feature (feature x) xs)
      (elementsWithoutFeature feature (feature x) xs)
      (groupByFrom feature n (elementsWithoutFeature feature (feature x) xs))
      ((splitByFeature_eq_iff feature (feature x) xs _ _).mpr ⟨rfl, rfl⟩)
      (groupByFrom_GroupedBy feature n
        (elementsWithoutFeature feature (feature x) xs) hrest)

theorem GroupedBy.eq_groupBy {α : Type u} {β : Type v} [DecidableEq β]
    {feature : α → β} {l : List α} {groups : List (Group α β)}
    (h : GroupedBy feature l groups) : groupBy feature l = groups := by
  induction h with
  | empty => rfl
  | firstGroup x xs matched rest gs hsplit hrest ih =>
    obtain ⟨hs, ho⟩ :=
      (splitByFeature_eq_iff feature (feature x) xs matched rest).mp hsplit
    have hrest_le :
        rest.length ≤ xs.length := by
      rw [← ho]
      exact elementsWithoutFeature_length_le feature (feature x) xs
    simp only [groupBy]
    rw [length_firstElement, groupByFrom]
    rw [hs, ho]
    rw [groupByFrom_eq_of_length_le feature xs.length rest hrest_le]
    exact congrArg _ ih

theorem groupBy_eq_iff {α : Type u} {β : Type v} [DecidableEq β]
    (feature : α → β) (l : List α) (groups : List (Group α β)) :
    groupBy feature l = groups ↔ GroupedBy feature l groups := by
  constructor
  · intro h
    have hg : GroupedBy feature l (groupBy feature l) := by
      simp only [groupBy]
      exact groupByFrom_GroupedBy feature l.length l (Or.inr rfl)
    exact h ▸ hg
  · intro h
    exact GroupedBy.eq_groupBy h

instance decidableGroupedBy {α : Type u} {β : Type v}
    [DecidableEq α] [DecidableEq β]
    (feature : α → β) (l : List α) (groups : List (Group α β)) :
    Decidable (GroupedBy feature l groups) :=
  if h : groupBy feature l = groups then
    isTrue ((groupBy_eq_iff feature l groups).mp h)
  else
    isFalse fun hg => h ((groupBy_eq_iff feature l groups).mpr hg)

/-- Feature values of the groups, in group order. -/
def groupFeatures {α : Type u} {β : Type v} : List (Group α β) → List β
  | empty => empty
  | firstElement g gs => firstElement g.feature (groupFeatures gs)

/-- Distinct feature values of `l`, in order of first appearance. -/
def featureValues {α : Type u} {β : Type v} [DecidableEq β]
    (feature : α → β) (l : List α) : List β :=
  groupFeatures (groupBy feature l)

/-- Flatten groups back into a single list of objects. -/
def concatenateGroups {α : Type u} {β : Type v} : List (Group α β) → List α
  | empty => empty
  | firstElement g gs => concatenate g.objects (concatenateGroups gs)

theorem groupedBy_group_AllElements {α : Type u} {β : Type v}
    {feature : α → β} {l : List α} {g : Group α β} {groups : List (Group α β)}
    (h : GroupedBy feature l groups) (hin : In g groups) :
    AllElements (fun x => feature x = g.feature) g.objects := by
  induction h with
  | empty => cases hin
  | firstGroup x xs matched rest gs hsplit hrest ih =>
    cases hin with
    | first _ _ heq =>
      cases heq
      exact AllElements.firstElement x matched rfl
        (splitByFeature_matched_AllElements hsplit)
    | notFirst _ _ hgs => exact ih hgs

theorem groupedBy_group_objects_ne_empty {α : Type u} {β : Type v}
    {feature : α → β} {l : List α} {g : Group α β} {groups : List (Group α β)}
    (h : GroupedBy feature l groups) (hin : In g groups) :
    g.objects ≠ empty := by
  induction h with
  | empty => cases hin
  | firstGroup x xs matched rest gs hsplit hrest ih =>
    cases hin with
    | first _ _ heq =>
      cases heq
      intro hempty
      cases hempty
    | notFirst _ _ hgs => exact ih hgs

theorem groupedBy_groupFeatures_AllElements {α : Type u} {β : Type v}
    {feature : α → β} {q : β → Prop} {l : List α} {groups : List (Group α β)}
    (h : GroupedBy feature l groups)
    (hAll : AllElements (fun x => q (feature x)) l) :
    AllElements q (groupFeatures groups) := by
  induction h with
  | empty => exact AllElements.empty
  | firstGroup x xs matched rest gs hsplit hrest ih =>
    exact AllElements.firstElement (feature x) (groupFeatures gs) hAll.head
      (ih (splitByFeature_rest_AllElements_of hsplit hAll.tail))

theorem groupedBy_groupFeatures_Unique {α : Type u} {β : Type v}
    {feature : α → β} {l : List α} {groups : List (Group α β)}
    (h : GroupedBy feature l groups) : Unique (groupFeatures groups) := by
  induction h with
  | empty => exact Unique.empty
  | firstGroup x xs matched rest gs hsplit hrest ih =>
    refine Unique.firstElement (feature x) (groupFeatures gs) ?_ ih
    exact AllElements.not_In
      (groupedBy_groupFeatures_AllElements (q := fun k => k ≠ feature x) hrest
        (splitByFeature_rest_AllElements hsplit))
      (fun hne => hne rfl)

theorem groupedBy_concatenate_length {α : Type u} {β : Type v}
    {feature : α → β} {l : List α} {groups : List (Group α β)}
    (h : GroupedBy feature l groups) :
    (concatenateGroups groups).length = l.length := by
  induction h with
  | empty => rfl
  | firstGroup x xs matched rest gs hsplit _ ih =>
    have hsplitLen := splitByFeature_length hsplit
    calc
      (concatenateGroups
          (firstElement
            { feature := feature x, objects := firstElement x matched }
            gs)).length
          = (firstElement x matched).length + (concatenateGroups gs).length := by
            simp only [concatenateGroups, concatenate_length]
      _ = (firstElement x matched).length + rest.length := by rw [ih]
      _ = (matched.length + Numbers.CardinalNatural.Peano.one) + rest.length := by
            simp only [length]
      _ = (matched.length + rest.length) + Numbers.CardinalNatural.Peano.one :=
            Numbers.CardinalNatural.Peano.add_one_commutative_right _ _
      _ = xs.length + Numbers.CardinalNatural.Peano.one := by rw [hsplitLen]
      _ = (firstElement x xs).length := by simp only [length]

theorem reordering_concatenate_right {α : Type u} {a b c : List α}
    (h : Reordering a b) : Reordering (concatenate c a) (concatenate c b) := by
  induction c with
  | empty => exact h
  | firstElement y ys ih =>
    exact Reordering.cons y (concatenate ys a) (firstElement y (concatenate ys b))
      (concatenate ys b) (RemoveFirst.here _) ih

theorem RemoveFirst_concatenate_of_not_In {α : Type u} {x : α}
    {matched rest : List α} (h : ¬ In x matched) :
    RemoveFirst x (concatenate matched (firstElement x rest))
      (concatenate matched rest) := by
  induction matched with
  | empty => exact RemoveFirst.here rest
  | firstElement y ys ih =>
    have hne : x ≠ y := by
      intro heq
      subst heq
      exact h (AnyElement.first x ys rfl)
    have htail : ¬ In x ys := fun hin =>
      h (AnyElement.notFirst y ys hin)
    exact RemoveFirst.there y (concatenate ys (firstElement x rest))
      (concatenate ys rest) hne (ih htail)

theorem splitByFeature_reordering {α : Type u} {β : Type v}
    {feature : α → β} {key : β} {l matched rest : List α}
    (h : SplitByFeature feature key l matched rest) :
    Reordering l (concatenate matched rest) := by
  induction h with
  | empty => exact Reordering.empty
  | hasFeature x xs matched rest _ _ ih =>
    exact Reordering.cons x xs (firstElement x (concatenate matched rest))
      (concatenate matched rest) (RemoveFirst.here _) ih
  | lacksFeature x xs matched rest hne hsplit ih =>
    have hnin : ¬ In x matched :=
      AllElements.not_In (splitByFeature_matched_AllElements hsplit)
        (fun heq => hne heq)
    exact Reordering.cons x xs (concatenate matched (firstElement x rest))
      (concatenate matched rest) (RemoveFirst_concatenate_of_not_In hnin) ih

theorem groupedBy_concatenate_reordering {α : Type u} {β : Type v}
    {feature : α → β} {l : List α} {groups : List (Group α β)}
    (h : GroupedBy feature l groups) :
    Reordering l (concatenateGroups groups) := by
  induction h with
  | empty => exact Reordering.empty
  | firstGroup x xs matched rest gs hsplit hrest ih =>
    have hsplitR := splitByFeature_reordering hsplit
    have hcat := reordering_concatenate_right (c := matched) ih
    have hxs : Reordering xs (concatenate matched (concatenateGroups gs)) :=
      reordering_transitive hsplitR hcat
    exact Reordering.cons x xs
      (firstElement x (concatenate matched (concatenateGroups gs)))
      (concatenate matched (concatenateGroups gs)) (RemoveFirst.here _) hxs

theorem groupBy_concatenate_reordering {α : Type u} {β : Type v} [DecidableEq β]
    (feature : α → β) (l : List α) :
    Reordering l (concatenateGroups (groupBy feature l)) :=
  groupedBy_concatenate_reordering ((groupBy_eq_iff feature l _).mp rfl)

theorem featureValues_Unique {α : Type u} {β : Type v} [DecidableEq β]
    (feature : α → β) (l : List α) :
    Unique (featureValues feature l) :=
  groupedBy_groupFeatures_Unique ((groupBy_eq_iff feature l _).mp rfl)

example : groupBy (fun b : Bool => b) empty = empty := rfl
example :
    groupBy (fun b : Bool => b) (firstElement true empty) =
      firstElement { feature := true, objects := firstElement true empty } empty :=
  rfl
example :
    groupBy (fun b : Bool => b)
      (firstElement true (firstElement false (firstElement true empty))) =
      firstElement
        { feature := true
          objects := firstElement true (firstElement true empty) }
        (firstElement
          { feature := false, objects := firstElement false empty }
          empty) :=
  rfl

end List

end ZeroMath.Sequences
