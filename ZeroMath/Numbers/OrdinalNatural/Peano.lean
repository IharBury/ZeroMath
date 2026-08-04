import ZeroMath.Logic.Trichotomy

namespace ZeroMath.Numbers.OrdinalNatural

inductive Peano where
  | one : Peano
  | successor : Peano → Peano

deriving instance DecidableEq for Peano

namespace Peano

def toNat : Peano → Nat
  | one => 1
  | successor n => n.toNat + 1

def toInt : Peano → Int
  | one => 1
  | successor n => n.toInt + 1

def fromNat : (n : Nat) → n ≠ 0 → Peano
  | 0, h => by contradiction
  | 1, _ => one
  | n + 2, _ => successor (fromNat (n + 1) Nat.noConfusion)

def fromInt (n : Int) (h : n > 0) : Peano :=
  fromNat n.toNat (by
    intro hzero
    exact (Int.not_le_of_gt h) (Int.toNat_eq_zero.mp hzero))

theorem toNat_ne_zero (p : Peano) : p.toNat ≠ 0 := by
  cases p <;> exact Nat.noConfusion

theorem fromNat_toNat_helper (n : Nat) (h : n ≠ 0) (p : Peano) (heq : p.toNat = n) : fromNat n h = p := by
  induction p generalizing n with
  | one =>
    cases n with
    | zero => contradiction
    | succ x =>
      cases x with
      | zero => rfl
      | succ x =>
        have h1 : 1 = x + 2 := heq
        cases h1
  | successor p ih =>
    cases n with
    | zero => contradiction
    | succ x =>
      cases x with
      | zero =>
        have h_contra : p.toNat + 1 = 1 := heq
        have h_p : p.toNat = 0 := Nat.add_right_cancel h_contra
        have h_nz := toNat_ne_zero p
        rw [h_p] at h_nz
        contradiction
      | succ x =>
        unfold fromNat
        have heq' : p.toNat = x + 1 := Nat.add_right_cancel heq
        have ih_applied := ih (x + 1) Nat.noConfusion heq'
        rw [ih_applied]

theorem fromNat_toNat (p : Peano) : ∃ h, fromNat p.toNat h = p := by
  exists toNat_ne_zero p
  exact fromNat_toNat_helper p.toNat (toNat_ne_zero p) p rfl

@[simp]
theorem toNat_fromNat (n : Nat) (h : n ≠ 0) : (fromNat n h).toNat = n := by
  induction n with
  | zero => contradiction
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n =>
      unfold fromNat
      unfold toNat
      have ih' := ih Nat.noConfusion
      rw [ih']

@[simp]
theorem toInt_eq_toNat (p : Peano) : p.toInt = p.toNat := by
  induction p with
  | one => rfl
  | successor p ih =>
    simp [toInt, toNat, ih]

theorem toInt_pos (p : Peano) : p.toInt > 0 := by
  rw [toInt_eq_toNat]
  exact Int.natCast_pos.mpr (Nat.pos_of_ne_zero (toNat_ne_zero p))

theorem fromNat_eq_of_eq (n m : Nat) (hn : n ≠ 0) (hm : m ≠ 0) (h : n = m) :
  fromNat n hn = fromNat m hm := by
  subst h
  rfl

theorem fromInt_toInt (p : Peano) : ∃ h, fromInt p.toInt h = p := by
  exists toInt_pos p
  unfold fromInt
  have htoNat : p.toInt.toNat = p.toNat := by
    rw [toInt_eq_toNat, Int.toNat_natCast]
  obtain ⟨h_toNat_ne_zero, h_fromNat⟩ := fromNat_toNat p
  exact (fromNat_eq_of_eq p.toInt.toNat p.toNat _ h_toNat_ne_zero htoNat).trans
    h_fromNat

@[simp]
theorem toInt_fromInt (x : Int) (h : x > 0) : (fromInt x h).toInt = x := by
  unfold fromInt
  rw [toInt_eq_toNat]
  rw [toNat_fromNat]
  have h2 : 0 ≤ x := Int.le_of_lt h
  exact Int.toNat_of_nonneg h2

inductive LessThan (a : Peano) : Peano → Prop where
  | base : LessThan a (successor a)
  | step {b : Peano} : LessThan a b → LessThan a (successor b)

instance : LT Peano where
  lt := LessThan

def LessThanOrEqual (a b : Peano) : Prop :=
  LessThan a b ∨ a = b

instance : LE Peano where
  le := LessThanOrEqual

def isLessThan : Peano → Peano → Bool
  | _, one => false
  | one, successor _ => true
  | successor a, successor b => isLessThan a b

example : isLessThan one one = false := rfl
example : isLessThan one (successor one) = true := rfl
example : isLessThan (successor one) one = false := rfl
example : isLessThan (successor one) (successor one) = false := rfl
example : isLessThan (successor one) (successor (successor one)) = true := rfl
example : isLessThan (successor (successor one)) (successor one) = false := rfl


def predecessor (a : Peano) (h : a ≠ one) : Peano :=
  match a with
  | one => by contradiction
  | successor b => b

example : predecessor (successor one) Peano.noConfusion = one := rfl
example : predecessor (successor (successor one)) Peano.noConfusion = successor one := rfl


def add (a : Peano) : Peano → Peano
  | one => successor a
  | successor b => successor (add a b)

instance : Add Peano where
  add := add

example : one + one = successor one := rfl
example : successor one + one = successor (successor one) := rfl
example : one + successor one = successor (successor one) := rfl
example : successor one + successor one = successor (successor (successor one)) := rfl

@[simp]
theorem add_one (a : Peano) : a + one = successor a := rfl

@[simp]
theorem add_succ (a b : Peano) : a + successor b = successor (a + b) := rfl

theorem one_add (a : Peano) : one + a = successor a := by
  induction a with
  | one => rfl
  | successor a ih => simp [ih]

@[simp]
theorem toNat_add (a b : Peano) :
  (a + b).toNat = _root_.Nat.add a.toNat b.toNat := by
  induction b with
  | one =>
    rw [add_one]
    cases a <;> rfl
  | successor b ih =>
    rw [add_succ]
    unfold Peano.toNat
    rw [ih]
    cases a <;> simp [Peano.toNat] at * <;> omega

@[simp]
theorem succ_add (a b : Peano) : successor a + b = successor (a + b) := by
  induction b with
  | one => rfl
  | successor b ih => simp [ih]

theorem add_comm (a b : Peano) : a + b = b + a := by
  induction b with
  | one =>
    rw [add_one, one_add]
  | successor b ih =>
    rw [add_succ, succ_add, ih]

theorem succ_lt_succ {x y : Peano} (h : x < y) : successor x < successor y := by
  induction h with
  | base => exact LessThan.base
  | step _ ih => exact LessThan.step ih

theorem succ_le_succ {a b : Peano} (h : a ≤ b) : successor a ≤ successor b := by
  cases h with
  | inl hlt => exact Or.inl (succ_lt_succ hlt)
  | inr heq => exact Or.inr (heq ▸ rfl)

theorem lt_trans {x y z : Peano} (h1 : x < y) (h2 : y < z) : x < z := by
  induction h2 with
  | base => exact LessThan.step h1
  | step _ ih => exact LessThan.step ih

theorem le_trans {x y z : Peano} (h1 : x ≤ y) (h2 : y ≤ z) : x ≤ z := by
  cases h1 with
  | inl hlt1 =>
    cases h2 with
    | inl hlt2 => exact Or.inl (lt_trans hlt1 hlt2)
    | inr heq2 =>
      rw [heq2] at hlt1
      exact Or.inl hlt1
  | inr heq1 =>
    rw [heq1]
    exact h2

theorem lt_of_lt_le {x y z : Peano} (h1 : x < y) (h2 : y ≤ z) : x < z := by
  cases h2 with
  | inl hlt2 => exact lt_trans h1 hlt2
  | inr heq2 =>
    rw [heq2] at h1
    exact h1

theorem lt_of_succ_lt {x y : Peano} (h : successor x < y) : x < y :=
  lt_trans LessThan.base h

theorem lt_of_succ_lt_succ {x y : Peano} (h : successor x < successor y) : x < y := by
  generalize hy : successor y = sy at h
  induction h generalizing y with
  | base =>
    cases hy
    exact LessThan.base
  | step h1 _ =>
    cases hy
    exact lt_of_succ_lt h1

def subtract (a : Peano) : (b : Peano) → b < a → Peano
  | one, h =>
    match a, h with
    | successor a', _ => a'
  | successor b', h =>
    match a, h with
    | successor a', h' => subtract a' b' (lt_of_succ_lt_succ h')

def subtractWithRemainder (a b : Peano) : Peano × Option Peano :=
  match a, b with
  | one, b => ⟨one, b⟩
  | successor a', one => ⟨a', none⟩
  | successor a', successor b' => subtractWithRemainder a' b'

def trySubtract (a b : Peano) : Option Peano :=
  match a, b with
  | one, _ => none
  | successor a', one => a'
  | successor a', successor b' => trySubtract a' b'

example : trySubtract one one = none := rfl
example : trySubtract one (successor one) = none := rfl
example : trySubtract (successor one) one = some one := rfl
example : trySubtract (successor (successor one)) one = some (successor one) := rfl
example : trySubtract (successor one) (successor one) = none := rfl
example : trySubtract (successor (successor one)) (successor one) = some one := rfl

theorem subtract_eq_of_eq {a b c d : Peano} (h1 : b < a) (h2 : d < c) (h3 : a = c) (h4 : b = d) :
  subtract a b h1 = subtract c d h2 := by
  subst h3
  subst h4
  rfl

theorem not_lt_one (x : Peano) : ¬ (x < one) := by
  intro h
  generalize ho : one = o at h
  induction h with
  | base => cases ho
  | step _ _ => cases ho

theorem not_lt_self (x : Peano) : ¬ (x < x) := by
  induction x with
  | one => exact not_lt_one one
  | successor x ih =>
    intro h
    exact ih (lt_of_succ_lt_succ h)

theorem not_lt_of_lt {x y : Peano} (h : x < y) : ¬ (y < x) := fun h2 =>
  not_lt_self x (lt_trans h h2)

theorem ne_of_lt {x y : Peano} (h : x < y) : x ≠ y := by
  rintro rfl
  exact not_lt_self x h

theorem not_succ_le (a : Peano) : ¬ successor a ≤ a := by
  intro h
  cases h with
  | inl hlt => exact not_lt_of_lt LessThan.base hlt
  | inr heq => exact (ne_of_lt LessThan.base) heq.symm

theorem one_lt_succ (x : Peano) : one < successor x := by
  induction x with
  | one => exact LessThan.base
  | successor x ih => exact LessThan.step ih

theorem exists_subtract_of_trySubtract {x y z : Peano} (h : trySubtract x y = some z) :
    ∃ h', subtract x y h' = z := by
  induction y generalizing x z with
  | one =>
    cases x with
    | one =>
      simp [trySubtract] at h
    | successor x' =>
      simp [trySubtract] at h
      subst h
      exact ⟨one_lt_succ x', rfl⟩
  | successor y' ih =>
    cases x with
    | one =>
      simp [trySubtract] at h
    | successor x' =>
      simp [trySubtract] at h
      obtain ⟨h', heq⟩ := ih h
      refine ⟨succ_lt_succ h', ?_⟩
      change subtract x' y' _ = z
      exact (subtract_eq_of_eq _ h' rfl rfl).trans heq

theorem trySubtract_of_subtract {x y z : Peano} (h : ∃ h', subtract x y h' = z) :
    trySubtract x y = some z := by
  induction y generalizing x z with
  | one =>
    obtain ⟨hlt, heq⟩ := h
    cases x with
    | one =>
      exact (not_lt_one one hlt).elim
    | successor x' =>
      simp [trySubtract]
      change x' = z
      exact heq
  | successor y' ih =>
    obtain ⟨hlt, heq⟩ := h
    cases x with
    | one =>
      exact (not_lt_one y'.successor hlt).elim
    | successor x' =>
      simp [trySubtract]
      apply ih
      refine ⟨lt_of_succ_lt_succ hlt, ?_⟩
      change subtract x' y' _ = z
      exact (subtract_eq_of_eq _ (lt_of_succ_lt_succ hlt) rfl rfl).symm.trans heq

theorem one_le (x : Peano) : x = one ∨ one < x := by
  induction x with
  | one => exact Or.inl rfl
  | successor x _ => exact Or.inr (one_lt_succ x)

/-- Every Peano number is at least one. -/
theorem one_le' (x : Peano) : one ≤ x := by
  cases one_le x with
  | inl heq => exact Or.inr heq.symm
  | inr hlt => exact Or.inl hlt

theorem isLessThan_eq_true_iff_lt (a b : Peano) : Peano.isLessThan a b = true ↔ a < b := by
  revert a
  induction b with
  | one =>
    intro a
    cases a with
    | one =>
      simp [Peano.isLessThan]
      intro h; exact False.elim (Peano.not_lt_self _ h)
    | successor a =>
      simp [Peano.isLessThan]
      intro h; exact False.elim (Peano.not_lt_one _ h)
  | successor b ih =>
    intro a
    cases a with
    | one =>
      simp [Peano.isLessThan]
      exact Peano.one_lt_succ b
    | successor a =>
      simp [Peano.isLessThan]
      rw [ih a]
      constructor
      · intro h
        exact Peano.succ_lt_succ h
      · intro h
        exact Peano.lt_of_succ_lt_succ h

theorem isLessThan_eq_false_iff_not_lt (a b : Peano) : Peano.isLessThan a b = false ↔ ¬ (a < b) := by
  constructor
  · intro h hlt
    have h1 := (isLessThan_eq_true_iff_lt a b).mpr hlt
    rw [h] at h1
    contradiction
  · intro h
    cases h2 : Peano.isLessThan a b
    · rfl
    · have h3 := (isLessThan_eq_true_iff_lt a b).mp h2
      contradiction

instance decidableLessThan (a b : Peano) : Decidable (a < b) := by
  cases h : Peano.isLessThan a b with
  | false => exact isFalse ((isLessThan_eq_false_iff_not_lt a b).mp h)
  | true => exact isTrue ((isLessThan_eq_true_iff_lt a b).mp h)

instance decidableLessThanOrEqual (a b : Peano) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a < b ∨ a = b))

theorem trichotomy_or (x y : Peano) : x < y ∨ x = y ∨ y < x := by
  induction x generalizing y with
  | one =>
    cases one_le y with
    | inl h => exact Or.inr (Or.inl h.symm)
    | inr h => exact Or.inl h
  | successor x ihx =>
    cases y with
    | one =>
      exact Or.inr (Or.inr (one_lt_succ x))
    | successor y =>
      cases ihx y with
      | inl h => exact Or.inl (succ_lt_succ h)
      | inr h =>
        cases h with
        | inl h =>
          rw [h]
          exact Or.inr (Or.inl rfl)
        | inr h =>
          exact Or.inr (Or.inr (succ_lt_succ h))

theorem trichotomy (x y : Peano) : ZeroMath.Logic.Trichotomy (x < y) (x = y) (y < x) := by
  cases trichotomy_or x y with
  | inl h =>
    exact ZeroMath.Logic.Trichotomy.first h (ne_of_lt h) (not_lt_of_lt h)
  | inr h =>
    cases h with
    | inl h =>
      subst h
      exact ZeroMath.Logic.Trichotomy.second rfl (not_lt_self x) (not_lt_self x)
    | inr h =>
      exact ZeroMath.Logic.Trichotomy.third h (not_lt_of_lt h) (ne_of_lt h).symm

/-- Result of comparing two Peano numbers, packaged with a proof of the relationship. -/
inductive Comparison (a b : Peano) where
  | less : a < b → Comparison a b
  | equal : a = b → Comparison a b
  | greater : b < a → Comparison a b

/-- Compare two Peano numbers, returning less, equal, or greater together with a proof. -/
def compare (a b : Peano) : Comparison a b :=
  match a, b with
  | one, one => Comparison.equal rfl
  | one, successor b => Comparison.less (one_lt_succ b)
  | successor a, one => Comparison.greater (one_lt_succ a)
  | successor a, successor b =>
    match compare a b with
    | Comparison.less h => Comparison.less (succ_lt_succ h)
    | Comparison.equal h => Comparison.equal (congrArg successor h)
    | Comparison.greater h => Comparison.greater (succ_lt_succ h)

theorem lt_add_left (x y : Peano) : x < x + y := by
  induction y with
  | one => exact LessThan.base
  | successor y ih => exact LessThan.step ih

theorem lt_add_right (x y : Peano) : y < x + y := by
  induction y with
  | one => exact one_lt_succ x
  | successor y ih => exact succ_lt_succ ih

theorem add_subtract_cancel (a b : Peano) : ∃ h, subtract (a + b) b h = a :=
  ⟨lt_add_right a b, by
  induction b with
  | one => rfl
  | successor b ih => exact ih⟩

/-- `trySubtract (x + d) x` recovers the added difference `d`. -/
theorem trySubtract_self_add (x d : Peano) : trySubtract (x + d) x = some d := by
  obtain ⟨h, heq⟩ := add_subtract_cancel d x
  have h' : x < x + d := lt_add_left x d
  refine trySubtract_of_subtract ⟨h', ?_⟩
  exact (subtract_eq_of_eq h' h (add_comm x d) rfl).trans heq

/-- `subtract (a + b) a` recovers `b`. -/
theorem subtract_add_left (a b : Peano) :
    subtract (a + b) a (lt_add_left a b) = b := by
  obtain ⟨h, heq⟩ := add_subtract_cancel b a
  exact (subtract_eq_of_eq (lt_add_left a b) h (add_comm a b) rfl).trans heq

/-- `trySubtract (x + d) d` recovers the left addend `x`. -/
theorem trySubtract_add_right (x d : Peano) : trySubtract (x + d) d = some x := by
  refine trySubtract_of_subtract ⟨lt_add_right x d, ?_⟩
  exact (subtract_eq_of_eq (lt_add_right x d) (lt_add_left d x) (add_comm x d) rfl).trans
    (subtract_add_left d x)

theorem subtract_add_cancel (a b : Peano) (h : b < a) : subtract a b h + b = a := by
  induction b generalizing a with
  | one =>
    cases a with
    | one => cases not_lt_self _ h
    | successor a => rfl
  | successor b ih =>
    cases a with
    | one => cases not_lt_self _ (lt_trans h (one_lt_succ _))
    | successor a =>
      exact congrArg successor (ih a (lt_of_succ_lt_succ h))

/-- A successful subtraction `trySubtract y x = some d` means `y = x + d`. -/
theorem eq_of_trySubtract_add (x y d : Peano)
    (h : trySubtract y x = some d) : y = x + d := by
  obtain ⟨hlt, hsub⟩ := exists_subtract_of_trySubtract h
  have hsum := subtract_add_cancel y x hlt
  rw [hsub] at hsum
  exact (add_comm d x) ▸ hsum.symm

/-- If `trySubtract y x = some d`, then `trySubtract y d = some x`. -/
theorem trySubtract_comm (x y d : Peano)
    (h : trySubtract y x = some d) :
    trySubtract y d = some x := by
  rw [eq_of_trySubtract_add x y d h]
  exact trySubtract_add_right x d

/-- If `trySubtract first diff = some next`, then `subtract first next` recovers
`diff`. -/
theorem subtract_eq_diff_of_trySubtract (first diff next : Peano)
    (h : trySubtract first diff = some next) :
    subtract first next
        (by
          have hadd := eq_of_trySubtract_add diff first next h
          rw [hadd]
          exact lt_add_right diff next) =
      diff := by
  have hadd : first = diff + next := eq_of_trySubtract_add diff first next h
  obtain ⟨hlt', heq⟩ := add_subtract_cancel diff next
  exact (subtract_eq_of_eq _ hlt' hadd rfl).trans heq

def multiply (a : Peano) : Peano → Peano
  | one => a
  | successor b => multiply a b + a

instance : Mul Peano where
  mul := multiply

theorem add_assoc (a b c : Peano) : (a + b) + c = a + (b + c) := by
  induction c with
  | one =>
    rw [add_one, add_one, add_succ]
  | successor c ih =>
    rw [add_succ, add_succ, add_succ, ih]

theorem add_right_comm (a b c : Peano) : (a + b) + c = (a + c) + b := by
  rw [add_assoc, add_comm b c, ←add_assoc]

theorem multiply_one (a : Peano) : a * one = a := by rfl

@[simp]
theorem one_multiply (a : Peano) : one * a = a := by
  induction a with
  | one => rfl
  | successor a ih =>
    show one * a + one = successor a
    rw [ih, add_one]

theorem multiply_succ (a b : Peano) : a * successor b = a * b + a := by rfl

theorem succ_multiply (a b : Peano) : successor a * b = a * b + b := by
  induction b with
  | one =>
    show successor a = a + one
    rw [add_one]
  | successor b ih =>
    show successor a * b + successor a = (a * b + a) + successor b
    rw [ih]
    rw [add_succ, add_succ]
    congr 1
    rw [add_right_comm]

theorem multiply_comm (a b : Peano) : a * b = b * a := by
  induction b with
  | one =>
    rw [multiply_one, one_multiply]
  | successor b ih =>
    rw [multiply_succ, succ_multiply, ih]

theorem multiply_add (a b c : Peano) : a * (b + c) = a * b + a * c := by
  induction c with
  | one =>
    rw [add_one, multiply_succ, multiply_one]
  | successor c ih =>
    rw [add_succ, multiply_succ, ih, multiply_succ, add_assoc]

theorem multiply_assoc (a b c : Peano) : (a * b) * c = a * (b * c) := by
  induction c with
  | one =>
    rw [multiply_one, multiply_one]
  | successor c ih =>
    rw [multiply_succ, multiply_succ, multiply_add, ih]

def Divisible (a b : Peano) : Prop := ∃ c, b * c = a

theorem lt_successor_cases {x y : Peano} (h : x < y) : y = successor x ∨ successor x < y := by
  induction h with
  | base => exact Or.inl rfl
  | step _ ih =>
    cases ih with
    | inl h_eq =>
      rw [h_eq]
      exact Or.inr LessThan.base
    | inr h_lt =>
      exact Or.inr (LessThan.step h_lt)

/-- The successor of a strictly smaller number is still ≤ the larger one. -/
theorem succ_le_of_lt {a b : Peano} (h : a < b) : successor a ≤ b := by
  cases lt_successor_cases h with
  | inl heq => exact Or.inr heq.symm
  | inr hlt => exact Or.inl hlt

theorem le_of_lt_succ {a b : Peano} (h : a < successor b) : a ≤ b := by
  generalize hb : successor b = sb at h
  induction h generalizing b with
  | base =>
    cases hb
    exact Or.inr rfl
  | step hlt _ =>
    cases hb
    exact Or.inl hlt

theorem le_multiply_right (a b : Peano) : a ≤ b * a := by
  induction b with
  | one =>
    rw [one_multiply]
    exact Or.inr rfl
  | successor b _ =>
    rw [succ_multiply]
    exact Or.inl (lt_add_right _ _)

theorem lt_of_succ_le {c b : Peano} (h : successor c ≤ b) : c < b := by
  cases h with
  | inl hlt =>
    cases b with
    | one => exact absurd hlt (not_lt_one (successor c))
    | successor b' => exact lt_trans (lt_of_succ_lt_succ hlt) LessThan.base
  | inr heq => subst heq; exact LessThan.base

theorem le_of_succ_le {c b : Peano} (h : successor c ≤ b) : c ≤ b := by
  cases h with
  | inl hlt =>
    cases b with
    | one => exact absurd hlt (not_lt_one (successor c))
    | successor b' =>
      exact Or.inl (lt_trans (lt_of_succ_lt_succ hlt) LessThan.base)
  | inr heq => subst heq; exact Or.inl LessThan.base

def divideWithRemainderAux (a b : Peano) (d : Option Peano) (c : Peano) (hc : c ≤ b) :
    Option Peano × Option Peano :=
  match a, d, c with
  | successor a, none, one =>
    divideWithRemainderAux a b (some one) b (Or.inr rfl)
  | successor a, some d, one =>
    divideWithRemainderAux a b (some d.successor) b (Or.inr rfl)
  | successor a, d, successor c =>
    divideWithRemainderAux a b d c (le_of_succ_le hc)
  | one, none, one =>
    (some one, none)
  | one, some d, one =>
    (some d.successor, none)
  | one, d, successor c =>
    (d, some (subtract b c (lt_of_succ_le hc)))

def divideWithRemainder (a b : Peano) : Option Peano × Option Peano :=
  divideWithRemainderAux a b none b (Or.inr rfl)

def isDivisible (a b : Peano) : Bool :=
  match divideWithRemainder a b with
  | (_, none) => true
  | (_, some _) => false

def tryDivide (a b : Peano) : Option Peano :=
  match divideWithRemainder a b with
  | (some q, none) => q
  | _ => none

theorem subtract_lt_right (b c : Peano) (h : c < b) : subtract b c h < b := by
  induction c generalizing b with
  | one =>
    cases b with
    | one => cases not_lt_self one h
    | successor b' =>
      rw [subtract]
      exact LessThan.base
  | successor c ih =>
    cases b with
    | one => cases not_lt_one (successor c) h
    | successor b' =>
      rw [subtract]
      exact lt_trans (ih b' (lt_of_succ_lt_succ h)) LessThan.base

theorem subtract_lt_of_succ_le {c b : Peano} (h : successor c ≤ b) :
    subtract b c (lt_of_succ_le h) < b :=
  subtract_lt_right b c (lt_of_succ_le h)

theorem divideWithRemainderAux_ne_none_none (a b : Peano) (d : Option Peano) (c : Peano)
    (hc : c ≤ b) : divideWithRemainderAux a b d c hc ≠ (none, none) := by
  induction a generalizing b d c with
  | one =>
    unfold divideWithRemainderAux
    cases d <;> cases c <;> simp
  | successor a ih =>
    unfold divideWithRemainderAux
    cases d <;> cases c <;> exact ih _ _ _ _

theorem divideWithRemainderAux_remainder_lt_b (a b : Peano) (d : Option Peano) (c : Peano)
    (hc : c ≤ b) (q : Option Peano) (r : Peano)
    (h : divideWithRemainderAux a b d c hc = (q, some r)) : r < b := by
  induction a generalizing b d c hc q with
  | one =>
    unfold divideWithRemainderAux at h
    cases d with
    | none =>
      cases c with
      | one => cases h
      | successor c =>
        cases h
        exact subtract_lt_of_succ_le hc
    | some d =>
      cases c with
      | one => cases h
      | successor c =>
        cases h
        exact subtract_lt_of_succ_le hc
  | successor a ih =>
    unfold divideWithRemainderAux at h
    cases d <;> cases c <;> first
    | exact ih _ _ _ (Or.inr rfl) _ h
    | exact ih _ _ _ (Or.inr rfl) _ h
    | exact ih _ _ _ (le_of_succ_le hc) _ h

theorem add_cancel_right (a b c : Peano) (h : a + c = b + c) : a = b := by
  induction c with
  | one =>
    rw [add_one, add_one] at h
    injection h
  | successor c ih =>
    rw [add_succ, add_succ] at h
    injection h with h'
    exact ih h'

theorem add_subtract_assoc (a b c : Peano) (h : b > c) : ∃ h2, subtract (a + b) c h2 = a + subtract b c h := by
  have h2 : c < a + b := lt_trans h (lt_add_right a b)
  refine ⟨h2, ?_⟩
  have h3 : subtract (a + b) c h2 + c = (a + subtract b c h) + c := by
    rw [subtract_add_cancel (a + b) c h2, add_assoc a (subtract b c h) c, subtract_add_cancel b c h]
  exact add_cancel_right (subtract (a + b) c h2) (a + subtract b c h) c h3

theorem multiply_cancel_left (a b c : Peano) (h : a * b = a * c) : b = c := by
  induction b generalizing c with
  | one =>
    cases c with
    | one => rfl
    | successor c' =>
      rw [multiply_one, multiply_succ] at h
      have h1 : a < a * c' + a := lt_add_right (a * c') a
      rw [←h] at h1
      cases not_lt_self a h1
  | successor b' ih =>
    cases c with
    | one =>
      rw [multiply_succ, multiply_one] at h
      have h1 : a < a * b' + a := lt_add_right (a * b') a
      rw [h] at h1
      cases not_lt_self a h1
    | successor c' =>
      rw [multiply_succ, multiply_succ] at h
      have h1 := add_cancel_right (a * b') (a * c') a h
      exact congrArg successor (ih c' h1)

theorem divide_divide_eq_divide_multiply_h2 {x y z : Peano} (h1 : Divisible x (y * z)) : Divisible x y := by
  cases h1 with
  | intro c hc =>
    exact ⟨z * c, by rw [←multiply_assoc, hc]⟩

theorem multiply_divide_assoc_h {x y z : Peano} (h : Divisible y z) : Divisible (x * y) z := by
  rcases h with ⟨c, hc⟩
  exact ⟨x * c, by
    rw [←multiply_assoc]
    have h1 : z * x = x * z := multiply_comm z x
    rw [h1]
    rw [multiply_assoc]
    rw [hc]⟩

def power (a : Peano) : Peano → Peano
  | one => a
  | successor b => power a b * a

instance : HPow Peano Peano Peano where
  hPow := power

theorem power_one (a : Peano) : a ^ one = a := rfl

theorem power_succ (a b : Peano) : a ^ successor b = a ^ b * a := rfl

theorem one_power (a : Peano) : one ^ a = one := by
  induction a with
  | one => rfl
  | successor a ih =>
    show one ^ a * one = one
    rw [ih, multiply_one]

theorem power_add (x y z : Peano) : x ^ (y + z) = (x ^ y) * (x ^ z) := by
  induction z with
  | one => rw [add_one, power_succ, power_one]
  | successor z ih =>
    rw [add_succ, power_succ, ih, power_succ]
    rw [multiply_assoc]

theorem power_multiply (x y z : Peano) : x ^ (y * z) = (x ^ y) ^ z := by
  induction z with
  | one => rw [multiply_one, power_one]
  | successor z ih => simp [multiply_succ, power_add, power_succ, ih]

theorem multiply_power (x y z : Peano) : (x * y) ^ z = (x ^ z) * (y ^ z) := by
  induction z with
  | one =>
    rw [power_one, power_one, power_one]
  | successor z ih =>
    rw [power_succ, power_succ, power_succ]
    rw [ih, multiply_assoc, ← multiply_assoc (y ^ z), multiply_comm (y ^ z) x,
      multiply_assoc x, ← multiply_assoc (x ^ z)]

def Power (e a : Peano) : Prop := ∃ b, b ^ e = a

theorem add_lt_add_right {a b : Peano} (c : Peano) (h : a < b) : a + c < b + c := by
  induction c with
  | one =>
    show successor a < successor b
    exact succ_lt_succ h
  | successor c ih =>
    show successor (a + c) < successor (b + c)
    exact succ_lt_succ ih

theorem add_lt_add_left (a : Peano) {b c : Peano} (h : b < c) : a + b < a + c := by
  rw [add_comm a b, add_comm a c]
  exact add_lt_add_right a h

theorem le_add_of_le_right (a : Peano) {b c : Peano} (h : b ≤ c) : a + b ≤ a + c := by
  cases h with
  | inl hlt => exact Or.inl (add_lt_add_left a hlt)
  | inr heq => exact Or.inr (heq ▸ rfl)

theorem lt_of_add_lt_add_right {a b c : Peano} (h : a + c < b + c) : a < b := by
  induction c generalizing a b with
  | one =>
    rw [add_one, add_one] at h
    exact lt_of_succ_lt_succ h
  | successor c ih =>
    rw [add_succ, add_succ] at h
    exact ih (lt_of_succ_lt_succ h)

theorem not_le_of_gt {a b : Peano} (h : b < a) : ¬ a ≤ b := by
  intro hle
  cases hle with
  | inl hlt => exact not_lt_of_lt h hlt
  | inr heq =>
    rw [heq] at h
    exact not_lt_self b h

theorem lt_multiply_left {a b c : Peano} (h : a < b) : a * c < b * c := by
  induction c with
  | one =>
    rw [multiply_one, multiply_one]
    exact h
  | successor c ih =>
    rw [multiply_succ, multiply_succ]
    have h1 : a * c + a < b * c + a := add_lt_add_right a ih
    have h2 : b * c + a < b * c + b := by
      rw [add_comm, add_comm (b * c) b]
      exact add_lt_add_right (b * c) h
    exact lt_trans h1 h2

theorem lt_multiply_right_cancel {a b c : Peano} (h : a * c < b * c) : a < b := by
  cases trichotomy a b with
  | first hlt _ _ => exact hlt
  | second heq _ _ =>
    rw [heq] at h
    cases not_lt_self (b * c) h
  | third hlt _ _ =>
    have hcontra : b * c < a * c := by
      have h1 := lt_multiply_left hlt (c := c)
      exact h1
    have htrans := lt_trans h hcontra
    cases not_lt_self (a * c) htrans

theorem multiply_subtract (a b c : Peano) (h : b > c) :
  ∃ h2, a * (subtract b c h) = subtract (a * b) (a * c) h2 := by
  have h2 : a * c < a * b := by
    have hlt : c * a < b * a := lt_multiply_left h
    rw [multiply_comm c a] at hlt
    rw [multiply_comm b a] at hlt
    exact hlt
  refine ⟨h2, ?_⟩
  have h3 : a * (subtract b c h) + a * c = subtract (a * b) (a * c) h2 + a * c := by
    rw [subtract_add_cancel (a * b) (a * c) h2]
    rw [←multiply_add a (subtract b c h) c]
    rw [subtract_add_cancel b c h]
  exact add_cancel_right (a * subtract b c h) (subtract (a * b) (a * c) h2) (a * c) h3

theorem subtract_subtract (x y z : Peano)
  (h : y < x) (h2 : z < subtract x y h) :
  ∃ h3, subtract (subtract x y h) z h2 = subtract x (y + z) h3 := by
  have h3 : y + z < x := by
    have h_lt := add_lt_add_right y h2
    have h_eq : subtract x y h + y = x := subtract_add_cancel x y h
    rw [h_eq] at h_lt
    have h_comm : z + y = y + z := add_comm z y
    rw [h_comm] at h_lt
    exact h_lt
  exact ⟨h3, by
    apply add_cancel_right _ _ (y + z)
    calc
      subtract (subtract x y h) z h2 + (y + z) = subtract (subtract x y h) z h2 + (z + y) := by
        rw [add_comm y z]
      _ = subtract (subtract x y h) z h2 + z + y := by
        rw [←add_assoc]
      _ = subtract x y h + y := by
        rw [subtract_add_cancel (subtract x y h) z h2]
      _ = x := subtract_add_cancel x y h
      _ = subtract x (y + z) h3 + (y + z) := by
        rw [subtract_add_cancel x (y + z) h3]
    ⟩

theorem lt_power {a b e : Peano} (h : a < b) : a ^ e < b ^ e := by
  induction e with
  | one =>
    rw [power_one, power_one]
    exact h
  | successor e ih =>
    rw [power_succ, power_succ]
    have h1 : a ^ e * a < b ^ e * a := lt_multiply_left ih
    have h2 : b ^ e * a < b ^ e * b := by
      rw [multiply_comm, multiply_comm (b ^ e) b]
      exact lt_multiply_left h
    exact lt_trans h1 h2

theorem power_cancel_left (a b c : Peano) (h : b ^ a = c ^ a) : b = c := by
  cases trichotomy b c with
  | first h1 =>
    have h2 : b ^ a < c ^ a := lt_power h1
    rw [h] at h2
    cases not_lt_self _ h2
  | second h1 => exact h1
  | third h1 =>
    have h2 : c ^ a < b ^ a := lt_power h1
    rw [h] at h2
    cases not_lt_self _ h2

theorem le_power (a e : Peano) : a ≤ a ^ e := by
  cases e with
  | one =>
    rw [power_one]
    exact Or.inr rfl
  | successor e =>
    rw [power_succ]
    exact le_multiply_right a (a ^ e)

def two : Peano := successor one

theorem one_lt_two_pow (e : Peano) : one < two ^ e := by
  induction e with
  | one =>
    simp [two, power_one]
    exact lt_add_right one one
  | successor e ih =>
    rw [power_succ, two, multiply_comm]
    exact lt_of_lt_le ih (le_multiply_right (two ^ e) two)

theorem le_of_subtract_lt {x y : Peano} (h : y < x) : subtract x y h ≤ x := by
  exact Or.inl (subtract_lt_right x y h)

theorem rootWithRemainderAux_reset_none_lt {b e : Peano} (hb : b = one) :
    b ^ e < two ^ e := by
  rw [hb, one_power e]
  exact one_lt_two_pow e

theorem rootWithRemainderAux_one_none_succ_false {e c p b : Peano}
    (hc : successor c ≤ p) (hp : p = b ^ e) (hb : b = one) : False := by
  rw [hb, one_power e] at hp
  cases hc with
  | inl hlt =>
    rw [hp] at hlt
    exact not_lt_one (successor c) hlt
  | inr heq =>
    rw [hp] at heq
    cases heq

theorem lt_of_le_lt {x y z : Peano} (h1 : x ≤ y) (h2 : y < z) : x < z := by
  cases h1 with
  | inl hlt => exact lt_trans hlt h2
  | inr heq => rw [heq]; exact h2

theorem rootWithRemainderAux_some_power_lt {k b e : Peano} (hb : b = k.successor) :
    k ^ e < b ^ e := by
  rw [hb]
  exact lt_power LessThan.base

theorem rootWithRemainderAux_advance_lt (b e : Peano) : b ^ e < b.successor ^ e :=
  lt_power LessThan.base

theorem rootWithRemainderAux_gap_lt_p {k p : Peano} (hlt : k < p) :
    subtract p k hlt < p :=
  subtract_lt_right p k hlt

theorem rootWithRemainderAux_c_lt_p {k c p e : Peano} (hlt : k ^ e < p)
    (hc : c ≤ subtract p (k ^ e) hlt) : c < p :=
  lt_of_le_lt hc (rootWithRemainderAux_gap_lt_p hlt)

def rootWithRemainderAux (a e : Peano) (r : Option Peano) (c p b : Peano)
    (hc : c ≤ p) (hp : p = b ^ e) (hnone : r = none → b = one)
    (hsome : ∀ k, r = some k → b = k.successor)
    (hbound : ∀ k, r = some k → ∀ hlt : k ^ e < p, c ≤ subtract p (k ^ e) hlt) :
    Peano × Option Peano :=
  match a, r, c with
  | successor a, none, one =>
    have hlt : p < two ^ e := by
      rw [hp]
      exact rootWithRemainderAux_reset_none_lt (hnone rfl)
    rootWithRemainderAux a e (some one) (subtract (two ^ e) p hlt) (two ^ e) two
      (le_of_subtract_lt hlt) rfl (fun h => nomatch h)
      (fun k hk => by
        injection hk with hk
        rw [← hk]
        rfl)
      (fun k hk hlt' => by
        injection hk with hk
        subst hk
        have hp' : p = one ^ e := by
          rw [hp, hnone rfl, one_power]
        exact Or.inr (subtract_eq_of_eq hlt hlt' rfl hp'))
  | successor a, some r, one =>
    have hb : b = r.successor := hsome r rfl
    have hlt : p < b.successor ^ e := by
      rw [hp]
      exact rootWithRemainderAux_advance_lt b e
    rootWithRemainderAux a e (some b) (subtract (b.successor ^ e) p hlt)
      (b.successor ^ e) b.successor
      (le_of_subtract_lt hlt) rfl (fun h => nomatch h)
      (fun k hk => by
        injection hk with hk
        rw [← hk])
      (fun k hk hlt' => by
        injection hk with hk
        subst hk
        exact Or.inr (subtract_eq_of_eq hlt hlt' rfl hp))
  | successor a, r, successor c =>
    rootWithRemainderAux a e r c p b (le_of_succ_le hc) hp hnone hsome
      (fun k hk hlt => le_of_succ_le (hbound k hk hlt))
  | one, none, one =>
    (one, none)
  | one, some r, one =>
    (r.successor, none)
  | one, none, successor c =>
    False.elim (rootWithRemainderAux_one_none_succ_false hc hp (hnone rfl))
  | one, some r, successor c =>
    have hlt_gap : r ^ e < p := by
      rw [hp, hsome r rfl]
      exact lt_power LessThan.base
    have hc_gap : successor c ≤ subtract p (r ^ e) hlt_gap := hbound r rfl hlt_gap
    have hlt_c : c < subtract p (r ^ e) hlt_gap := lt_of_succ_le hc_gap
    (r, some (subtract (subtract p (r ^ e) hlt_gap) c hlt_c))

def rootWithRemainder (a e : Peano) : Peano × Option Peano :=
  rootWithRemainderAux a e none one one one (Or.inr rfl) (by rw [one_power e])
    (fun _ => rfl) (fun _ hk => by cases hk) (fun _ hk => by cases hk)

def tryRoot (e a : Peano) : Option Peano :=
  match rootWithRemainder a e with
  | (b, none) => b
  | _ => none

theorem one_add_subtract_one (p : Peano) (h : one < p) :
    one + subtract p one h = p := by
  rw [one_add]
  cases p with
  | one => exact absurd h (not_lt_self one)
  | successor p' => rfl

theorem succ_add_subtract_one (a p : Peano) (h : one < p) :
    successor a + subtract p one h = a + p := by
  cases p with
  | one => exact absurd h (not_lt_self one)
  | successor p' =>
    change successor a + p' = a + successor p'
    rw [succ_add, add_succ]

theorem subtract_succ_add_one (b c : Peano) (hlt : successor c < b) :
    subtract b c (lt_of_succ_lt hlt) = one + subtract b (successor c) hlt := by
  induction c generalizing b with
  | one =>
    cases b with
    | one => exact absurd hlt (not_lt_one (successor one))
    | successor b' =>
      cases b' with
      | one => exact absurd hlt (not_lt_self (successor one))
      | successor b'' =>
        simp only [subtract, one_add]
  | successor c ih =>
    cases b with
    | one => exact absurd hlt (not_lt_one (successor (successor c)))
    | successor b' =>
      rw [subtract, subtract]
      exact ih b' (lt_of_succ_lt_succ hlt)

theorem add_subtract_succ_step (a p c : Peano) (hlt : successor c < p) :
    successor a + subtract p (successor c) hlt =
    a + subtract p c (lt_of_succ_lt hlt) := by
  rw [subtract_succ_add_one p c hlt, ← add_assoc, add_one]

theorem subtract_subtract_cancel (x y : Peano) (h : y < x) :
    ∃ h2, subtract x (subtract x y h) h2 = y := by
  have h2 : subtract x y h < x := subtract_lt_right x y h
  refine ⟨h2, ?_⟩
  apply add_cancel_right _ _ (subtract x y h)
  rw [subtract_add_cancel x (subtract x y h) h2, add_comm, subtract_add_cancel x y h]

theorem subtract_eq_add_subtract_gap (p k c : Peano) (hlt_k : k < p)
    (hlt_c : c < subtract p k hlt_k) :
    subtract p c (lt_trans hlt_c (subtract_lt_right p k hlt_k)) =
    k + subtract (subtract p k hlt_k) c hlt_c := by
  apply add_cancel_right _ _ c
  calc
    subtract p c (lt_trans hlt_c (subtract_lt_right p k hlt_k)) + c = p := by
      rw [subtract_add_cancel]
    _ = subtract p k hlt_k + k := by
      rw [subtract_add_cancel]
    _ = k + subtract p k hlt_k := by
      rw [add_comm]
    _ = k + (subtract (subtract p k hlt_k) c hlt_c + c) := by
      rw [subtract_add_cancel]
    _ = (k + subtract (subtract p k hlt_k) c hlt_c) + c := by
      rw [add_assoc]

theorem rootWithRemainderAux_none_succ_c_false {e c p b : Peano}
    (hc : successor c ≤ p) (hp : p = b ^ e) (hb : b = one) : False :=
  rootWithRemainderAux_one_none_succ_false hc hp hb

/-- Original value for a `some`-state: remaining `a` plus how far the counter has advanced into `p`. -/
def rootWithRemainderOrigSome (a c p : Peano) (hlt : c < p) : Peano :=
  a + subtract p c hlt

theorem rootWithRemainderAux_correct (e : Peano) :
    ∀ (a : Peano) (r : Option Peano) (c p b : Peano)
      (hc : c ≤ p) (hp : p = b ^ e) (hnone : r = none → b = one)
      (hsome : ∀ k, r = some k → b = k.successor)
      (hbound : ∀ k, r = some k → ∀ hlt : k ^ e < p, c ≤ subtract p (k ^ e) hlt),
      (r = none →
        (let res := rootWithRemainderAux a e r c p b hc hp hnone hsome hbound
         (res.2 = none → a = res.1 ^ e) ∧
         (∀ rem, res.2 = some rem → a = res.1 ^ e + rem ∧ a < res.1.successor ^ e))) ∧
      (∀ k, r = some k → ∀ (hlt : c < p),
        (let orig := rootWithRemainderOrigSome a c p hlt
         let res := rootWithRemainderAux a e r c p b hc hp hnone hsome hbound
         (res.2 = none → orig = res.1 ^ e) ∧
         (∀ rem, res.2 = some rem → orig = res.1 ^ e + rem ∧ orig < res.1.successor ^ e))) := by
  intro a
  induction a with
  | one =>
    intro r c p b hc hp hnone hsome hbound
    constructor
    · intro hr
      subst hr
      cases c with
      | one =>
        refine ⟨fun _ => by simp [rootWithRemainderAux, one_power], ?_⟩
        intro rem h
        simp [rootWithRemainderAux] at h
      | successor c =>
        exact False.elim (rootWithRemainderAux_none_succ_c_false hc hp (hnone rfl))
    · intro k hr hlt
      subst hr
      cases c with
      | one =>
        have hb : b = k.successor := hsome k rfl
        refine ⟨?_, ?_⟩
        · intro _
          simp only [rootWithRemainderAux, rootWithRemainderOrigSome]
          rw [one_add_subtract_one p hlt, hp, hb]
        · intro rem h
          simp [rootWithRemainderAux] at h
      | successor c =>
        have hlt_gap : k ^ e < p := by
          rw [hp, hsome k rfl]
          exact lt_power LessThan.base
        have hc_gap : successor c ≤ subtract p (k ^ e) hlt_gap := hbound k rfl hlt_gap
        have hlt_c_gap : c < subtract p (k ^ e) hlt_gap := lt_of_succ_le hc_gap
        have hlt_succ : successor c < p := rootWithRemainderAux_c_lt_p hlt_gap hc_gap
        refine ⟨?_, ?_⟩
        · intro h
          simp [rootWithRemainderAux] at h
        · intro rem hres
          have hrem : rem = subtract (subtract p (k ^ e) hlt_gap) c hlt_c_gap := by
            simp only [rootWithRemainderAux] at hres
            injection hres with hr
            exact hr.symm
          subst hrem
          constructor
          · simp only [rootWithRemainderOrigSome, rootWithRemainderAux]
            have hpc : subtract p (successor c) hlt =
                subtract p (successor c) hlt_succ :=
              subtract_eq_of_eq hlt hlt_succ rfl rfl
            rw [hpc]
            have hone : one + subtract p (successor c) hlt_succ =
                subtract p c (lt_of_succ_lt hlt_succ) :=
              (subtract_succ_add_one p c hlt_succ).symm
            rw [hone]
            have hdecomp : subtract p c (lt_of_succ_lt hlt_succ) =
                k ^ e + subtract (subtract p (k ^ e) hlt_gap) c hlt_c_gap := by
              have h1 := subtract_eq_add_subtract_gap p (k ^ e) c hlt_gap hlt_c_gap
              refine Eq.trans ?_ h1
              exact subtract_eq_of_eq _ _ rfl rfl
            exact hdecomp
          · simp only [rootWithRemainderOrigSome, rootWithRemainderAux]
            have hb : b = k.successor := hsome k rfl
            have hpc : subtract p (successor c) hlt =
                subtract p (successor c) hlt_succ :=
              subtract_eq_of_eq hlt hlt_succ rfl rfl
            rw [hpc, (subtract_succ_add_one p c hlt_succ).symm, ← hb, ← hp]
            exact subtract_lt_right p c (lt_of_succ_lt hlt_succ)
  | successor a ih =>
    intro r c p b hc hp hnone hsome hbound
    constructor
    · intro hr
      subst hr
      cases c with
      | one =>
        have hlt : p < two ^ e := by
          rw [hp]
          exact rootWithRemainderAux_reset_none_lt (hnone rfl)
        have hsome' : ∀ k, some one = some k → two = k.successor := fun k hk => by
          injection hk with hk; rw [← hk]; rfl
        have hbound' : ∀ k, some one = some k →
            ∀ hlt' : k ^ e < two ^ e,
              subtract (two ^ e) p hlt ≤ subtract (two ^ e) (k ^ e) hlt' := by
          intro k hk hlt'
          injection hk with hk; subst hk
          have hp' : p = one ^ e := by rw [hp, hnone rfl, one_power]
          exact Or.inr (subtract_eq_of_eq hlt hlt' rfl hp')
        have hc' : subtract (two ^ e) p hlt ≤ two ^ e := le_of_subtract_lt hlt
        have ih_pair := ih (some one) (subtract (two ^ e) p hlt) (two ^ e) two
          hc' rfl (fun h => nomatch h) hsome' hbound'
        have ⟨_, ih_some⟩ := ih_pair
        have hlt_c_new : subtract (two ^ e) p hlt < two ^ e := subtract_lt_right _ _ hlt
        have ih_at := ih_some one rfl hlt_c_new
        have hp_one : p = one := by rw [hp, hnone rfl, one_power]
        have horig_eq : rootWithRemainderOrigSome a (subtract (two ^ e) p hlt) (two ^ e) hlt_c_new =
            successor a := by
          simp only [rootWithRemainderOrigSome]
          rcases subtract_subtract_cancel (two ^ e) p hlt with ⟨h2, hcancel⟩
          rw [subtract_eq_of_eq hlt_c_new h2 rfl rfl, hcancel, hp_one, add_one]
        simp only [rootWithRemainderAux]
        have ⟨ih_none, ih_rem⟩ := ih_at
        refine ⟨?_, ?_⟩
        · intro hnone_res
          rw [← horig_eq]
          exact ih_none hnone_res
        · intro rem hsome_res
          rw [← horig_eq]
          exact ih_rem rem hsome_res
      | successor c =>
        exact False.elim (rootWithRemainderAux_none_succ_c_false hc hp (hnone rfl))
    · intro k hr hlt
      subst hr
      cases c with
      | one =>
        have hb : b = k.successor := hsome k rfl
        have hlt_adv : p < b.successor ^ e := by
          rw [hp]; exact rootWithRemainderAux_advance_lt b e
        have hsome' : ∀ k', some b = some k' → b.successor = k'.successor := fun k' hk => by
          injection hk with hk; rw [← hk]
        have hbound' : ∀ k', some b = some k' →
            ∀ hlt' : k' ^ e < b.successor ^ e,
              subtract (b.successor ^ e) p hlt_adv ≤ subtract (b.successor ^ e) (k' ^ e) hlt' := by
          intro k' hk hlt'
          injection hk with hk; subst hk
          exact Or.inr (subtract_eq_of_eq hlt_adv hlt' rfl hp)
        have hc' : subtract (b.successor ^ e) p hlt_adv ≤ b.successor ^ e :=
          le_of_subtract_lt hlt_adv
        have ih_pair := ih (some b) (subtract (b.successor ^ e) p hlt_adv)
          (b.successor ^ e) b.successor hc' rfl (fun h => nomatch h) hsome' hbound'
        have ⟨_, ih_some⟩ := ih_pair
        have hlt_c_new : subtract (b.successor ^ e) p hlt_adv < b.successor ^ e :=
          subtract_lt_right _ _ hlt_adv
        have ih_at := ih_some b rfl hlt_c_new
        have hone_lt_p : one < p := hlt
        have horig_eq : rootWithRemainderOrigSome a (subtract (b.successor ^ e) p hlt_adv)
              (b.successor ^ e) hlt_c_new =
            rootWithRemainderOrigSome (successor a) one p hlt := by
          simp only [rootWithRemainderOrigSome]
          rcases subtract_subtract_cancel (b.successor ^ e) p hlt_adv with ⟨h2, hcancel⟩
          rw [subtract_eq_of_eq hlt_c_new h2 rfl rfl, hcancel]
          exact (succ_add_subtract_one a p hone_lt_p).symm
        simp only [rootWithRemainderAux]
        have ⟨ih_none, ih_rem⟩ := ih_at
        refine ⟨?_, ?_⟩
        · intro hnone_res
          rw [← horig_eq]
          exact ih_none hnone_res
        · intro rem hsome_res
          rw [← horig_eq]
          exact ih_rem rem hsome_res
      | successor c =>
        have hbound' : ∀ k', some k = some k' →
            ∀ hlt' : k' ^ e < p, c ≤ subtract p (k' ^ e) hlt' :=
          fun k' hk hlt' => le_of_succ_le (hbound k' hk hlt')
        have hc' : c ≤ p := le_of_succ_le hc
        have ih_pair := ih (some k) c p b hc' hp hnone hsome hbound'
        have ⟨_, ih_some⟩ := ih_pair
        have hlt' : c < p := lt_of_succ_lt hlt
        have ih_at := ih_some k rfl hlt'
        have horig_eq : rootWithRemainderOrigSome a c p hlt' =
            rootWithRemainderOrigSome (successor a) (successor c) p hlt := by
          simp only [rootWithRemainderOrigSome]
          exact (add_subtract_succ_step a p c hlt).symm
        simp only [rootWithRemainderAux]
        have ⟨ih_none, ih_rem⟩ := ih_at
        refine ⟨?_, ?_⟩
        · intro hnone_res
          rw [← horig_eq]
          exact ih_none hnone_res
        · intro rem hsome_res
          rw [← horig_eq]
          exact ih_rem rem hsome_res

theorem rootWithRemainder_none (a e b : Peano)
    (h : rootWithRemainder a e = (b, none)) : a = b ^ e := by
  have hcorr := (rootWithRemainderAux_correct e a none one one one
    (Or.inr rfl) (by rw [one_power e]) (fun _ => rfl)
    (fun _ hk => by cases hk) (fun _ hk => by cases hk)).1 rfl
  simp only [rootWithRemainder] at h
  have ⟨hnone, _⟩ := hcorr
  have hb : (rootWithRemainderAux a e none one one one (Or.inr rfl) (by rw [one_power e])
      (fun _ => rfl) (fun _ hk => by cases hk) (fun _ hk => by cases hk)).1 = b := by
    rw [h]
  have hnone' :
      (rootWithRemainderAux a e none one one one (Or.inr rfl) (by rw [one_power e])
        (fun _ => rfl) (fun _ hk => by cases hk) (fun _ hk => by cases hk)).2 = none := by
    rw [h]
  rw [← hb]
  exact hnone hnone'

theorem rootWithRemainder_some_lt (a e b r : Peano)
    (h : rootWithRemainder a e = (b, some r)) : a < b.successor ^ e := by
  have hcorr := (rootWithRemainderAux_correct e a none one one one
    (Or.inr rfl) (by rw [one_power e]) (fun _ => rfl)
    (fun _ hk => by cases hk) (fun _ hk => by cases hk)).1 rfl
  simp only [rootWithRemainder] at h
  have ⟨_, hsome⟩ := hcorr
  have hres := hsome r (by rw [h])
  have hb : (rootWithRemainderAux a e none one one one (Or.inr rfl) (by rw [one_power e])
      (fun _ => rfl) (fun _ hk => by cases hk) (fun _ hk => by cases hk)).1 = b := by
    rw [h]
  rw [← hb]
  exact hres.2

theorem rootWithRemainder_some_add (a e b r : Peano)
    (h : rootWithRemainder a e = (b, some r)) : a = b ^ e + r := by
  have hcorr := (rootWithRemainderAux_correct e a none one one one
    (Or.inr rfl) (by rw [one_power e]) (fun _ => rfl)
    (fun _ hk => by cases hk) (fun _ hk => by cases hk)).1 rfl
  simp only [rootWithRemainder] at h
  have ⟨_, hsome⟩ := hcorr
  have hres := hsome r (by rw [h])
  have hb : (rootWithRemainderAux a e none one one one (Or.inr rfl) (by rw [one_power e])
      (fun _ => rfl) (fun _ hk => by cases hk) (fun _ hk => by cases hk)).1 = b := by
    rw [h]
  rw [← hb]
  exact hres.1

theorem rootWithRemainder_some_power (a e b r : Peano) (h : Power e a)
    (hres : rootWithRemainder a e = (b, some r)) : False := by
  have ha := rootWithRemainder_some_add a e b r hres
  have hlt := rootWithRemainder_some_lt a e b r hres
  rcases h with ⟨c, hc⟩
  have hlt_b : b ^ e < c ^ e := by
    have : b ^ e < a := by
      rw [ha]
      exact lt_add_left (b ^ e) r
    rwa [← hc] at this
  have hlt_c : c ^ e < b.successor ^ e := by
    rwa [← hc] at hlt
  have hbc : b < c := by
    cases trichotomy b c with
    | first h => exact h
    | second h =>
      rw [h] at hlt_b
      exact False.elim (not_lt_self _ hlt_b)
    | third h =>
      exact False.elim (not_lt_of_lt hlt_b (lt_power h))
  have hcs : c < b.successor := by
    cases trichotomy c b.successor with
    | first h => exact h
    | second h =>
      rw [h] at hlt_c
      exact False.elim (not_lt_self _ hlt_c)
    | third h =>
      exact False.elim (not_lt_of_lt hlt_c (lt_power h))
  exact not_lt_self b (lt_of_lt_le hbc (le_of_lt_succ hcs))

def root (e a : Peano) (h : Power e a) : Peano :=
  match hres : rootWithRemainder a e with
  | (b, none) => b
  | (b, some r) => False.elim (rootWithRemainder_some_power a e b r h hres)

theorem root_correct (e a : Peano) (h : Power e a) : (root e a h) ^ e = a := by
  unfold root
  split
  next b hres =>
    exact (rootWithRemainder_none a e b hres).symm
  next b r hres =>
    exact False.elim (rootWithRemainder_some_power a e b r h hres)

theorem root_power_eq (e x : Peano) : ∃ h, root e (x ^ e) h = x := by
  let h : Power e (x ^ e) := ⟨x, rfl⟩
  exists h
  exact power_cancel_left e (root e (x ^ e) h) x (root_correct e (x ^ e) h)

theorem exists_root_of_tryRoot {x y z : Peano} (h : tryRoot x y = some z) :
    ∃ h', root x y h' = z := by
  have hres : rootWithRemainder y x = (z, none) := by
    unfold tryRoot at h
    split at h
    · next b hb =>
      injection h with hz
      rw [← hz]
      exact hb
    · next _ =>
      cases h
  have hpow : Power x y := ⟨z, (rootWithRemainder_none y x z hres).symm⟩
  refine ⟨hpow, ?_⟩
  exact power_cancel_left x (root x y hpow) z (by
    rw [root_correct x y hpow, rootWithRemainder_none y x z hres])

theorem tryRoot_eq_some_root (x y : Peano) (h : Power x y) :
    tryRoot x y = some (root x y h) := by
  unfold root
  split
  · next b hres =>
    simp only [tryRoot, hres]
  · next b r hres =>
    exact False.elim (rootWithRemainder_some_power y x b r h hres)

theorem tryRoot_of_exists_root {x y z : Peano} (h : ∃ h', root x y h' = z) :
    tryRoot x y = some z := by
  rcases h with ⟨hpow, hz⟩
  rw [← hz]
  exact tryRoot_eq_some_root x y hpow

def Even (a : Peano) : Prop := Divisible a two

def Odd (a : Peano) : Prop := ¬ Even a

def isEven : Peano → Bool
  | one => false
  | successor n => !isEven n

def isOdd (a : Peano) : Bool := !isEven a

@[simp]
theorem toNat_multiply (a b : Peano) : (a * b).toNat = a.toNat * b.toNat := by
  induction b with
  | one => simp [multiply_one, toNat]
  | successor b ih =>
    rw [multiply_succ, toNat_add, ih]
    simp [toNat, Nat.mul_add]

@[simp]
theorem two_toNat : two.toNat = 2 := rfl

theorem pred_toNat {x : Peano} (h_neq : x ≠ one) : (predecessor x h_neq).toNat = x.toNat - 1 := by
  cases x with
  | one => contradiction
  | successor x' =>
    change x'.toNat = (x'.toNat + 1) - 1
    omega

theorem even_or_odd (x : Peano) : Even x ∨ Odd x := by
  unfold Odd
  exact Classical.em (Even x)

theorem even_succ {x : Peano} : Even x → Odd (successor x) := by
  intro h
  unfold Odd Even Divisible
  unfold Even Divisible at h
  intro hcontra
  rcases h with ⟨c, hc⟩
  rcases hcontra with ⟨c', hc'⟩
  have hc_symm : x = two * c := hc.symm
  have hc'_symm : successor x = two * c' := hc'.symm
  rw [hc_symm] at hc'_symm
  clear hc hc_symm hc' x
  induction c generalizing c' with
  | one =>
    rw [multiply_one] at hc'_symm
    cases c' with
    | one =>
      rw [multiply_one] at hc'_symm
      have h1 : two ≠ successor two := by
        have hlt : two < two + one := lt_add_left two one
        rw [add_one] at hlt
        exact ne_of_lt hlt
      exact h1 hc'_symm.symm
    | successor c' =>
      rw [multiply_succ] at hc'_symm
      have h_succ_two : successor two = two + one := by rw [add_one]
      rw [h_succ_two] at hc'_symm
      rw [add_comm (two * c') two, add_comm two one, add_comm two (two * c')] at hc'_symm
      have h_eq : one = two * c' := add_cancel_right one (two * c') two hc'_symm
      have h_two_is_succ : two = successor one := rfl
      rw [h_two_is_succ] at h_eq
      rw [succ_multiply] at h_eq
      have hlt1 : one * c' < one * c' + c' := lt_add_left (one * c') c'
      rw [← h_eq] at hlt1
      have hlt2 : c' ≤ one * c' := le_multiply_right c' one
      cases hlt2 with
      | inl hlt2_lt =>
        have h_lt_one := lt_trans hlt2_lt hlt1
        exact not_lt_one c' h_lt_one
      | inr hlt2_eq =>
        rw [← hlt2_eq] at hlt1
        exact not_lt_one c' hlt1
  | successor c ih =>
    rw [multiply_succ] at hc'_symm
    cases c' with
    | one =>
      rw [multiply_one] at hc'_symm
      have h_succ_add : (two * c + two).successor = two * c + two.successor := by rw [add_succ]
      rw [h_succ_add] at hc'_symm
      have hlt1 : two.successor < two * c + two.successor := lt_add_right (two * c) two.successor
      rw [hc'_symm] at hlt1
      have hlt2 : one < one + one := lt_add_left one one
      rw [add_one] at hlt2
      have h_two_is_succ : two = successor one := rfl
      rw [← h_two_is_succ] at hlt2
      have hlt3 : two < two.successor := succ_lt_succ hlt2
      have hlt4 := lt_trans hlt1 hlt3
      exact not_lt_self (successor two) hlt4
    | successor c' =>
      rw [multiply_succ] at hc'_symm
      have h_succ_add : (two * c + two).successor = (two * c).successor + two := by
        have h1 : (two * c + two).successor = two * c + two.successor := by rw [add_succ]
        rw [h1]
        have h2 : two.successor = one + two := by rw [one_add]
        rw [h2]
        have h3 : two * c + (one + two) = (two * c + one) + two := by rw [← add_assoc]
        rw [h3]
        have h4 : two * c + one = (two * c).successor := by rw [add_one]
        rw [h4]
      rw [h_succ_add] at hc'_symm
      have h_eq : (two * c).successor = two * c' := add_cancel_right ((two * c).successor) (two * c') two hc'_symm
      exact ih c' h_eq

theorem odd_succ {x : Peano} : Odd x → Even (successor x) := by
  intro h
  induction x with
  | one =>
    unfold Even Divisible
    exists one
  | successor x ih =>
    cases even_or_odd x with
    | inl h_even =>
      unfold Even Divisible at h_even
      rcases h_even with ⟨c, hc⟩
      unfold Even Divisible
      exists successor c
      rw [multiply_succ]
      have hc_symm : x = two * c := hc.symm
      rw [← hc_symm]
      show successor (successor x) = x + two
      rw [show two = successor one from rfl, add_succ, add_one]
    | inr h_odd =>
      have h_even_succ : Even (successor x) := ih h_odd
      unfold Odd at h
      exact (h h_even_succ).elim

theorem even_pred {x : Peano} (h : Even x) : ∃ h_gt, Odd (predecessor x h_gt) := by
  have h_neq : x ≠ one := by
    intro h_eq
    rw [h_eq] at h
    unfold Even Divisible at h
    rcases h with ⟨c, hc⟩
    cases c with
    | one =>
      rw [multiply_one] at hc
      have hlt : one < two := by exact lt_add_right one one
      rw [hc] at hlt
      exact not_lt_self one hlt
    | successor c' =>
      rw [multiply_succ] at hc
      have hlt : two < two * c' + two := by
        rw [add_comm]
        exact lt_add_left two (two * c')
      have h_one_lt_two : one < two := lt_add_right one one
      have h_one_lt : one < two * c' + two := lt_trans h_one_lt_two hlt
      rw [hc] at h_one_lt
      exact not_lt_self one h_one_lt
  exists h_neq
  intro hcontra
  have h_even_succ : Even (predecessor x h_neq) → Odd (successor (predecessor x h_neq)) := even_succ
  have h_succ_pred : successor (predecessor x h_neq) = x := by
    cases x with
    | one => exact False.elim (h_neq rfl)
    | successor x' => rfl
  have h_odd_x : Odd x := by
    have h1 := h_even_succ hcontra
    rw [h_succ_pred] at h1
    exact h1
  exact (h_odd_x h).elim

theorem odd_pred {x : Peano} (h_odd : Odd x) (h_neq : x ≠ one) : Even (predecessor x h_neq) := by
  have h_succ_pred : successor (predecessor x h_neq) = x := by
    cases x with
    | one => exact False.elim (h_neq rfl)
    | successor x' => rfl
  have h_cases := even_or_odd (predecessor x h_neq)
  cases h_cases with
  | inl h_even => exact h_even
  | inr h_odd_pred =>
    have h_even_succ : Even (successor (predecessor x h_neq)) := odd_succ h_odd_pred
    rw [h_succ_pred] at h_even_succ
    exact (h_odd h_even_succ).elim

theorem not_even_one : ¬ Even one := by
  intro h
  unfold Even Divisible at h
  rcases h with ⟨c, hc⟩
  cases c with
  | one =>
    rw [multiply_one] at hc
    have hlt : one < two := lt_add_right one one
    rw [hc] at hlt
    exact not_lt_self one hlt
  | successor c' =>
    rw [multiply_succ] at hc
    have hlt : one < two * c' + two := by
      have h1 : one < two := lt_add_right one one
      have h2 : two < two + two * c' := lt_add_left two (two * c')
      have h3 : two + two * c' = two * c' + two := add_comm two (two * c')
      rw [h3] at h2
      exact lt_trans h1 h2
    rw [hc] at hlt
    exact not_lt_self one hlt

theorem even_succ_iff (x : Peano) : Even (successor x) ↔ Odd x := by
  constructor
  · intro h
    have hor := even_or_odd x
    cases hor with
    | inl h_even =>
      have h_odd_succ := even_succ h_even
      unfold Odd at h_odd_succ
      exact False.elim (h_odd_succ h)
    | inr h_odd => exact h_odd
  · intro h_odd
    exact odd_succ h_odd

theorem isEven_correct (x : Peano) : Even x ↔ isEven x := by
  induction x with
  | one =>
    constructor
    · intro h
      exact False.elim (not_even_one h)
    · intro h
      exact False.elim (Bool.false_ne_true h)
  | successor x ih =>
    constructor
    · intro h
      have h_odd : Odd x := (even_succ_iff x).mp h
      rw [isEven]
      have : ¬ isEven x := by
        rw [← ih]
        unfold Odd at h_odd
        exact h_odd
      simp [this]
    · intro h
      simp [isEven] at h
      have h_not_even_x : ¬ Even x := by
        intro h_even
        rw [ih] at h_even
        rw [h_even] at h
        simp at h
      have h_odd : Odd x := h_not_even_x
      exact (even_succ_iff x).mpr h_odd

theorem isOdd_correct (x : Peano) : Odd x ↔ isOdd x := by
  unfold Odd isOdd
  rw [isEven_correct]
  cases isEven x <;> simp

instance decidableEven (x : Peano) : Decidable (Even x) :=
  decidable_of_iff' (isEven x) (isEven_correct x)

instance decidableOdd (x : Peano) : Decidable (Odd x) :=
  decidable_of_iff' (isOdd x) (isOdd_correct x)

theorem add_associative (a b c : Peano) : (a + b) + c = a + (b + c) := by
  induction c with
  | one =>
    rw [add_one, add_one, add_succ]
  | successor c ih =>
    rw [add_succ, add_succ, add_succ, ih]


theorem pred_succ_eq (x : Peano) : ∃ h, predecessor (successor x) h = x := by
  exact ⟨fun h => Peano.noConfusion h, rfl⟩

@[simp]
theorem succ_pred_eq (x : Peano) (h : x ≠ one) : successor (predecessor x h) = x := by
  cases x with
  | one => exact False.elim (h rfl)
  | successor x' => rfl


theorem x_lt_succ_x (x : Peano) : x < x.successor := by
  induction x with
  | one => exact one_lt_succ one
  | successor x' ih => exact succ_lt_succ ih

theorem subtractWithRemainderCorrect (a b : Peano) :
  (a ≤ b ∧ ∃ h, subtractWithRemainder a b = ⟨one, subtract b.successor a h⟩) ∨ (a > b ∧ ∃ h, subtractWithRemainder a b = ⟨subtract a b h, none⟩) := by
  induction a generalizing b with
  | one =>
    apply Or.inl
    constructor
    · cases one_le b with
      | inl h => exact Or.inr h.symm
      | inr h => exact Or.inl h
    · exact ⟨one_lt_succ b, rfl⟩
  | successor a ih =>
    cases b with
    | one =>
      apply Or.inr
      constructor
      · exact one_lt_succ a
      · exact ⟨one_lt_succ a, rfl⟩
    | successor b =>
      cases ih b with
      | inl h =>
        apply Or.inl
        constructor
        · cases h.left with
          | inl hlt => exact Or.inl (succ_lt_succ hlt)
          | inr heq => exact Or.inr (congrArg successor heq)
        · rcases h.right with ⟨h_lt, h_eq⟩
          unfold subtractWithRemainder
          exists succ_lt_succ h_lt
      | inr h =>
        apply Or.inr
        constructor
        · exact succ_lt_succ h.left
        · rcases h.right with ⟨h_lt, h_eq⟩
          unfold subtractWithRemainder
          exists succ_lt_succ h_lt

theorem lt_of_le_of_ne {c b : Peano} (hle : c ≤ b) (hne : c ≠ b) : c < b := by
  cases hle with
  | inl hlt => exact hlt
  | inr heq => exact absurd heq hne

def divideWithRemainderOrigNoneLt (b a c : Peano) (hlt : c < b) : Peano :=
  a + subtract b c hlt

def divideWithRemainderOrigSomeBase (b : Peano) (hb : one < b) (q : Peano) : Peano :=
  match q with
  | one => subtract b one hb
  | successor q' => q' * b + subtract b one hb

def divideWithRemainderOrigSomeLt (b : Peano) (hb : one < b) (q a c : Peano) (hlt : c < b) : Peano :=
  divideWithRemainderOrigSomeBase b hb q + successor a + subtract b c hlt

theorem one_add_ne (x : Peano) : one + x ≠ x := by
  induction x with
  | one => intro h; cases h
  | successor x ih =>
    intro h
    rw [add_succ] at h
    injection h with h'
    exact ih h'

theorem subtract_succ_self (c : Peano) :
    subtract (successor c) c LessThan.base = one := by
  induction c with
  | one => rfl
  | successor c ih =>
    simp only [subtract]
    exact ih

theorem subtract_succ_one (n : Peano) (h : one < n.successor) :
    subtract n.successor one h = n :=
  rfl

theorem not_succ_lt (c : Peano) : ¬ successor c < c := by
  intro h
  exact not_lt_self _ (lt_trans h LessThan.base)

theorem subtract_one_of_succ_eq (b c' : Peano) (heq : successor c' = b) :
    subtract b c' (lt_of_succ_le (Or.inr heq)) = one := by
  subst heq
  exact subtract_succ_self c'

def divideWithRemainderOrigNone (b a c : Peano) (hc : c ≤ b) : Peano :=
  if h : c = b then a else
    divideWithRemainderOrigNoneLt b a c (lt_of_le_of_ne hc h)

def divideWithRemainderOrigSome (b : Peano) (hb : one < b) (q a c : Peano) (hc : c ≤ b) : Peano :=
  if h : c = b then
    divideWithRemainderOrigSomeBase b hb q + successor a
  else
    divideWithRemainderOrigSomeLt b hb q a c (lt_of_le_of_ne hc h)

theorem divideWithRemainderOrigOptionSome (b : Peano) (q a c : Peano) (hc : c ≤ b) :
    (match some q with
      | none => divideWithRemainderOrigNone b a c hc
      | some q' =>
        if hone : one < b then
          divideWithRemainderOrigSome b hone q' a c hc
        else
          a + q') =
    if hone : one < b then
      divideWithRemainderOrigSome b hone q a c hc
    else
      a + q := by
  cases q <;> simp

theorem succ_succ_add_balance (x y s : Peano) :
    (x + y).successor.successor + s = x + y + one.successor + s := by
  calc
    (x + y).successor.successor + s
        = ((x + y) + one).successor + s := by rw [add_one]
    _ = (x + y + one).successor + s := by rw [add_assoc]
    _ = x + y + one.successor + s := by rw [add_succ, add_assoc]

theorem succ_self_add_balance (s t : Peano) :
    s.successor.successor + t = s + one.successor + t := by
  calc
    s.successor.successor + t
        = (s + one).successor + t := by rw [add_one]
    _ = s + one.successor + t := by rw [←add_succ, add_assoc]

theorem succ_self_eq (s : Peano) : s.successor.successor = s + one.successor := by
  simp [add_one, add_succ]

theorem add_one_one_split (s : Peano) :
    s + (one + one + s) = (s + one) + (one + s) := by
  simp [add_comm]

theorem orig_some_one_lt (b : Peano) (hb : one < b) :
    subtract b one hb + one.successor + subtract b one hb = b * one.successor := by
  let s := subtract b one hb
  calc
    s + one.successor + s
        = s + (one + one + s) := by rw [←add_one, add_assoc]
    _ = (s + one) + (one + s) := add_one_one_split s
    _ = b + (one + s) := by rw [subtract_add_cancel b one hb]
    _ = b + (s + one) := by rw [add_comm one s]
    _ = b + b := by rw [subtract_add_cancel b one hb]
    _ = b * one.successor := by
          apply Eq.symm
          rw [multiply_succ, multiply_one]

theorem orig_some_one_lt' (b : Peano) (hb : one < b) (x : Peano) :
    x + subtract b one hb + one.successor + subtract b one hb = x + b * one.successor := by
  let s := subtract b one hb
  calc x + s + one.successor + s
      = x + (s + one.successor + s) := by simp [add_assoc]
    _ = x + b * one.successor := by rw [orig_some_one_lt b hb]

theorem orig_some_one_step (b : Peano) (hb : one < b) :
    subtract b one hb + one.successor = b + one := by
  calc subtract b one hb + one.successor
      = subtract b one hb + (one + one) := by rw [←add_one one]
    _ = (subtract b one hb + one) + one := by rw [add_assoc]
    _ = b + one := by rw [subtract_add_cancel b one hb]

theorem orig_some_one_step' (b : Peano) (hb : one < b) (x r : Peano) :
    x + subtract b one hb + one.successor + r = x + (b + one + r) := by
  let s := subtract b one hb
  calc x + s + one.successor + r
      = x + (s + one.successor) + r := by rw [←add_assoc]
    _ = x + (b + one) + r := by rw [orig_some_one_step b hb, ←add_assoc]
    _ = x + (b + one + r) := by rw [add_assoc]

theorem orig_some_q_mul (b : Peano) (q' c' : Peano)
    (hlt' : successor c' < b) :
    q' * b + (b + one + subtract b (successor c') hlt') =
    b * (successor q') + subtract b c' (lt_of_succ_le (Or.inl hlt')) := by
  let rem := subtract b (successor c') hlt'
  have hsub := subtract_succ_add_one b c' hlt'
  calc q' * b + (b + one + rem)
      = (q' * b + (b + one)) + rem := by rw [←add_assoc]
    _ = ((q' * b + b) + one) + rem := by rw [←add_assoc]
    _ = ((b * q' + b) + one) + rem := by rw [multiply_comm]
    _ = (b * (successor q') + one) + rem := by rw [←multiply_succ, add_assoc]
    _ = b * (successor q') + (one + rem) := by rw [add_assoc]
    _ = b * (successor q') + subtract b c' (lt_of_succ_le (Or.inl hlt')) := by rw [hsub]

theorem if_lt_pos_named (b : Peano) (h : one < b) (A B : Peano) :
    (if _ : one < b then A else B) = A := dif_pos h

theorem if_lt_neg_named (b : Peano) (h : ¬ one < b) (A B : Peano) :
    (if _ : one < b then A else B) = B := dif_neg h

theorem divideWithRemainderOrigNoneLt_step (b a c' : Peano) (hlt : successor c' < b) :
    divideWithRemainderOrigNoneLt b (successor a) (successor c') hlt =
    divideWithRemainderOrigNoneLt b a c' (lt_of_succ_lt hlt) := by
  unfold divideWithRemainderOrigNoneLt
  calc
    successor a + subtract b (successor c') hlt
        = a + one + subtract b (successor c') hlt := by rw [←add_one, add_assoc]
    _ = a + subtract b c' (lt_of_succ_lt hlt) := by
          rw [add_assoc, (subtract_succ_add_one b c' hlt).symm]

theorem divideWithRemainderOrigNone_ne (b a c : Peano) (hc : c ≤ b) (hne : c ≠ b) :
    divideWithRemainderOrigNone b a c hc =
    divideWithRemainderOrigNoneLt b a c (lt_of_le_of_ne hc hne) := by
  unfold divideWithRemainderOrigNone
  by_cases h : c = b
  · exact absurd h hne
  · rw [dif_neg h]

theorem divideWithRemainderOrigSome_ne (b : Peano) (hb : one < b) (q a c : Peano) (hc : c ≤ b)
    (hne : c ≠ b) :
    divideWithRemainderOrigSome b hb q a c hc =
    divideWithRemainderOrigSomeLt b hb q a c (lt_of_le_of_ne hc hne) := by
  unfold divideWithRemainderOrigSome
  by_cases h : c = b
  · exact absurd h hne
  · rw [dif_neg h]

theorem divideWithRemainderOrigNone_eq (b a c : Peano) (hc : c = b) :
    divideWithRemainderOrigNone b a c (Or.inr hc) = a := by
  unfold divideWithRemainderOrigNone
  simp [hc]

theorem divideWithRemainderOrigSome_eq (b : Peano) (hb : one < b) (q a c : Peano) (hc : c = b) :
    divideWithRemainderOrigSome b hb q a c (Or.inr hc) =
    divideWithRemainderOrigSomeBase b hb q + successor a := by
  unfold divideWithRemainderOrigSome divideWithRemainderOrigSomeBase
  simp [hc]

theorem divideWithRemainderOrigNone_step (b : Peano) (a c' : Peano)
    (hc : successor c' ≤ b) :
    divideWithRemainderOrigNone b (successor a) (successor c') hc =
    divideWithRemainderOrigNone b a c' (le_of_succ_le hc) := by
  by_cases hcb : successor c' = b
  · cases hc with
    | inl hlt =>
      rw [hcb] at hlt
      exact absurd hlt (not_lt_self b)
    | inr heq =>
      have hne : c' ≠ b := fun h => by rw [h] at heq; cases heq
      have hsub : subtract b c' (lt_of_succ_le (Or.inr heq)) = one := by
        simpa [heq.symm] using subtract_succ_self c'
      calc
        divideWithRemainderOrigNone b (successor a) (successor c') (Or.inr heq)
            = successor a := divideWithRemainderOrigNone_eq _ _ _ heq
        _ = divideWithRemainderOrigNoneLt b a c' (lt_of_succ_le (Or.inr heq)) := by
              rw [divideWithRemainderOrigNoneLt, hsub, add_one]
        _ = divideWithRemainderOrigNone b a c' (le_of_succ_le (Or.inr heq)) :=
              (divideWithRemainderOrigNone_ne _ _ _ _ hne).symm
  · have hlt' := lt_of_le_of_ne hc hcb
    have hne' : c' ≠ b := ne_of_lt (lt_of_succ_le hc)
    calc
      divideWithRemainderOrigNone b (successor a) (successor c') hc
          = divideWithRemainderOrigNoneLt b (successor a) (successor c') hlt' := by
            exact divideWithRemainderOrigNone_ne _ _ _ _ hcb
      _ = divideWithRemainderOrigNoneLt b a c' (lt_of_succ_lt hlt') :=
            divideWithRemainderOrigNoneLt_step b a c' hlt'
      _ = divideWithRemainderOrigNone b a c' (le_of_succ_le hc) := by
            exact (divideWithRemainderOrigNone_ne _ _ _ _ hne').symm

theorem divideWithRemainderOrigNone_reset (b : Peano) (hb : one < b) (a : Peano) :
    divideWithRemainderOrigNone b (successor a) one (Or.inl hb) =
    divideWithRemainderOrigSome b hb one a b (Or.inr rfl) := by
  have hone_ne : one ≠ b := ne_of_lt hb
  simp [divideWithRemainderOrigNone, divideWithRemainderOrigSome,
    divideWithRemainderOrigNoneLt, divideWithRemainderOrigSomeBase, hone_ne]
  rw [add_comm]

theorem divideWithRemainderOrigSomeLt_step (b : Peano) (hb : one < b) (q a c' : Peano)
    (hlt : successor c' < b) :
    divideWithRemainderOrigSomeLt b hb q (successor a) (successor c') hlt =
    divideWithRemainderOrigSomeLt b hb q a c' (lt_of_succ_lt hlt) := by
  unfold divideWithRemainderOrigSomeLt divideWithRemainderOrigSomeBase
  calc
    divideWithRemainderOrigSomeBase b hb q + successor (successor a) +
        subtract b (successor c') hlt
        = divideWithRemainderOrigSomeBase b hb q +
            (successor (successor a) + subtract b (successor c') hlt) := by rw [←add_assoc]
    _ = divideWithRemainderOrigSomeBase b hb q +
            (successor a + subtract b c' (lt_of_succ_lt hlt)) := by
          congr 1
          exact divideWithRemainderOrigNoneLt_step b (successor a) c' hlt
    _ = divideWithRemainderOrigSomeBase b hb q + successor a +
            subtract b c' (lt_of_succ_lt hlt) := by rw [add_assoc]

theorem divideWithRemainderOrigSome_step (b : Peano) (hb : one < b) (q a c' : Peano)
    (hc : successor c' ≤ b) :
    divideWithRemainderOrigSome b hb q (successor a) (successor c') hc =
    divideWithRemainderOrigSome b hb q a c' (le_of_succ_le hc) := by
  by_cases hcb : successor c' = b
  · cases hc with
    | inl hlt =>
      rw [hcb] at hlt
      exact absurd hlt (not_lt_self b)
    | inr heq =>
      have hne : c' ≠ b := fun h => by rw [h] at heq; cases heq
      have hsub : subtract b c' (lt_of_succ_le (Or.inr heq)) = one := by
        simpa [heq.symm] using subtract_succ_self c'
      calc
        divideWithRemainderOrigSome b hb q (successor a) (successor c') (Or.inr heq)
            = divideWithRemainderOrigSomeBase b hb q + successor (successor a) :=
              divideWithRemainderOrigSome_eq _ _ _ (successor a) (successor c') heq
        _ = divideWithRemainderOrigSomeLt b hb q a c' (lt_of_succ_le (Or.inr heq)) := by
              simp [divideWithRemainderOrigSomeLt, divideWithRemainderOrigSomeBase,
                hsub, add_one]
        _ = divideWithRemainderOrigSome b hb q a c' (le_of_succ_le (Or.inr heq)) :=
              (divideWithRemainderOrigSome_ne _ _ _ _ _ _ hne).symm
  · have hlt' := lt_of_le_of_ne hc hcb
    have hne' : c' ≠ b := ne_of_lt (lt_of_succ_le hc)
    calc
      divideWithRemainderOrigSome b hb q (successor a) (successor c') hc
          = divideWithRemainderOrigSomeLt b hb q (successor a) (successor c') hlt' := by
            exact divideWithRemainderOrigSome_ne _ _ _ _ _ _ hcb
      _ = divideWithRemainderOrigSomeLt b hb q a c' (lt_of_succ_lt hlt') :=
            divideWithRemainderOrigSomeLt_step b hb q a c' hlt'
      _ = divideWithRemainderOrigSome b hb q a c' (le_of_succ_le hc) := by
            exact (divideWithRemainderOrigSome_ne _ _ _ _ _ _ hne').symm

theorem divideWithRemainderOrigSome_reset_aux (b a : Peano) (hb : one < b) :
    (a + (subtract b one hb + subtract b one hb)).successor =
    a + (b + subtract b one hb) := by
  let s := subtract b one hb
  calc
    (a + (s + s)).successor
        = (a + (s + s)) + one := by rw [←add_one]
    _ = a + (s + s + one) := by rw [add_assoc]
    _ = a + (s + b) := by
          congr 1
          rw [←subtract_add_cancel b one hb, add_assoc]
    _ = a + (b + s) := by congr 1; exact add_comm s b

theorem double_sub_one (b : Peano) (hb : one < b) :
    subtract b one hb + subtract b one hb + one = b + subtract b one hb := by
  let s := subtract b one hb
  have h := divideWithRemainderOrigSome_reset_aux b one hb
  have h' : one + (s + s + one) = one + (b + s) := by
    calc
      one + (s + s + one)
          = (one + (s + s)) + one := by rw [←add_assoc]
      _ = one + (b + s) := by simpa [←add_one] using h
  exact add_cancel_right (s + s + one) (b + s) one (by
    rw [←add_comm one (s + s + one), ←add_comm one (b + s)]
    exact h')

theorem sub_succ_succ_balance (b a : Peano) (hb : one < b) :
    subtract b one hb + successor (successor a) + subtract b one hb =
    b + subtract b one hb + successor a := by
  let s := subtract b one hb
  have hcancel := double_sub_one b hb
  calc
    s + successor (successor a) + s
        = s + (s + successor (successor a)) := by
          rw [add_comm (s + successor (successor a))]
    _ = s + s + (successor a + one) := by
          rw [add_assoc, ←add_one (successor a)]
    _ = (s + s + one) + successor a := by
          rw [add_assoc, add_assoc, add_comm one (successor a), add_assoc]
    _ = (s + s + one) + successor a := by rw [add_assoc, add_assoc]
    _ = (b + s) + successor a := by rw [hcancel]
    _ = b + s + successor a := by rw [add_assoc]

theorem add_q_orig_shift (q' b s a : Peano) :
    (q' * b + s) + successor (successor a) + s = q' * b + (s + successor (successor a) + s) := by
  simp [add_assoc]

theorem fin_q_balance (q' b s a : Peano) :
    b + (successor a + q' * b + s) = q' * b + b + s + successor a := by
  calc
    b + (successor a + q' * b + s)
        = (b + (successor a + q' * b)) + s := by rw [←add_assoc]
    _ = ((successor a + q' * b) + b) + s := by rw [add_comm b (successor a + q' * b), add_assoc]
    _ = (successor a + q' * b) + (b + s) := by rw [add_assoc]
    _ = successor a + (q' * b + (b + s)) := by rw [add_assoc, ←add_assoc]
    _ = successor a + ((q' * b + b) + s) := by congr 1; rw [add_assoc]
    _ = ((q' * b + b) + s) + successor a := by rw [add_comm (successor a) ((q' * b + b) + s)]

theorem divideWithRemainderOrigSome_reset_mid (b a : Peano) (hb : one < b) :
    subtract b one hb + (successor a + (subtract b one hb + subtract b one hb)).successor =
    subtract b one hb + successor a + (b + subtract b one hb) := by
  let s := subtract b one hb
  calc
    s + (successor a + (s + s)).successor
        = s + (successor a + (b + s)) := by
          rw [divideWithRemainderOrigSome_reset_aux b (successor a) hb]
    _ = s + successor a + (b + s) := by rw [add_assoc]

theorem divideWithRemainderOrigSome_reset (b : Peano) (hb : one < b) (q a : Peano) :
    divideWithRemainderOrigSome b hb q (successor a) one (Or.inl hb) =
    divideWithRemainderOrigSome b hb (successor q) a b (Or.inr rfl) := by
  have hone_ne : one ≠ b := ne_of_lt hb
  let s := subtract b one hb
  cases q with
  | one =>
    calc
      divideWithRemainderOrigSome b hb one (successor a) one (Or.inl hb)
          = divideWithRemainderOrigSomeLt b hb one (successor a) one hb :=
            divideWithRemainderOrigSome_ne _ _ _ _ _ _ hone_ne
      _ = s + successor (successor a) + s := by
            unfold divideWithRemainderOrigSomeLt divideWithRemainderOrigSomeBase
            rw [add_assoc, add_comm s]
      _ = b + s + successor a := sub_succ_succ_balance b a hb
      _ = divideWithRemainderOrigSomeBase b hb (successor one) + successor a := by
            dsimp [divideWithRemainderOrigSomeBase]
            rw [one_multiply b]
      _ = divideWithRemainderOrigSome b hb (successor one) a b (Or.inr rfl) :=
            (divideWithRemainderOrigSome_eq b hb (successor one) a b rfl).symm
  | successor q' =>
    calc
      divideWithRemainderOrigSome b hb (successor q') (successor a) one (Or.inl hb)
          = divideWithRemainderOrigSomeLt b hb (successor q') (successor a) one hb :=
            divideWithRemainderOrigSome_ne _ _ _ _ _ _ hone_ne
      _ = (q' * b + s) + successor (successor a) + s := by
            unfold divideWithRemainderOrigSomeLt divideWithRemainderOrigSomeBase
            rw [add_assoc, add_comm (q' * b + s)]
      _ = (q' * b + b + s) + successor a := by
        calc
          (q' * b + s) + successor (successor a) + s
              = q' * b + (s + successor (successor a) + s) := add_q_orig_shift q' b s a
          _ = q' * b + (b + s + successor a) := by
                congr 1
                exact sub_succ_succ_balance b a hb
          _ = (q' * b + b + s) + successor a := by
            calc
              q' * b + (b + s + successor a)
                  = (q' * b + (b + s)) + successor a :=
                    (add_assoc (q' * b) (b + s) (successor a)).symm
              _ = ((q' * b + b) + s) + successor a := by
                    congr 1
                    exact (add_assoc (q' * b) b s).symm
      _ = (successor q' * b + s) + successor a := by
            rw [←succ_multiply q' b, add_assoc]
      _ = divideWithRemainderOrigSomeBase b hb (successor (successor q')) + successor a := by
            unfold divideWithRemainderOrigSomeBase
            rfl
      _ = divideWithRemainderOrigSome b hb (successor (successor q')) a b (Or.inr rfl) :=
            (divideWithRemainderOrigSome_eq b hb (successor (successor q')) a b rfl).symm

theorem divideWithRemainderAux_correct (b : Peano) :
    ∀ (a : Peano) (d : Option Peano) (c : Peano) (hc : c ≤ b),
      let res := divideWithRemainderAux a b d c hc
      let orig := match d with
        | none => divideWithRemainderOrigNone b a c hc
        | some q =>
          if hone : one < b then
            divideWithRemainderOrigSome b hone q a c hc
          else
            a + q
      (res.1, res.2) ≠ (none, none) ∧
      (∀ r, res.2 = some r → r < b) ∧
      (∀ {r}, res = (none, some r) → orig = r) ∧
      (∀ {q}, res = (some q, none) → orig = b * q) ∧
      (∀ {q r}, res = (some q, some r) → orig = b * q + r) := by
  intro a d c hc
  induction a generalizing d c hc with
  | one =>
    unfold divideWithRemainderAux
    cases d with
    | none =>
      cases c with
      | one =>
        constructor
        · exact divideWithRemainderAux_ne_none_none one b none one hc
        · constructor
          · intro r hr; cases hr
          · constructor
            · intro r hRes; cases hRes
            · constructor
              · intro q hRes
                cases hRes
                cases b with
                | one =>
                  cases hc with
                  | inl hlt => exact absurd hlt (not_lt_one one)
                  | inr heq => simp [divideWithRemainderOrigNone, multiply_one]
                | successor b' =>
                  let b := successor b'
                  have hb := one_lt_succ b'
                  cases hc with
                  | inl hlt =>
                    simp [divideWithRemainderOrigNone, divideWithRemainderOrigNoneLt, multiply_one]
                    calc
                      one + b.subtract one hlt = b.subtract one hlt + one := add_comm _ _
                      _ = successor b' := (subtract_add_cancel b one hlt).symm
                  | inr heq => exact absurd heq (fun h => by cases h)
              · intro q r hRes; cases hRes
      | successor c' =>
        have hlt := subtract_lt_of_succ_le hc
        cases hc with
        | inl hlt' =>
          constructor
          · exact divideWithRemainderAux_ne_none_none one b none (successor c') (Or.inl hlt')
          · constructor
            · intro r hr; cases hr; exact hlt
            · constructor
              · intro r hRes
                cases hRes
                have hne : successor c' ≠ b := fun heq => not_lt_self _ (heq ▸ hlt')
                rw [divideWithRemainderOrigNone_ne _ _ _ _ hne, divideWithRemainderOrigNoneLt,
                  subtract_succ_add_one b c' hlt']
              · constructor
                · intro q hRes; cases hRes
                · intro q r hRes; cases hRes
        | inr heq =>
          constructor
          · exact divideWithRemainderAux_ne_none_none one b none (successor c') (Or.inr heq)
          · constructor
            · intro r hr; cases hr; exact subtract_lt_of_succ_le (Or.inr heq)
            · constructor
              · intro r hRes
                cases hRes
                simp [divideWithRemainderOrigNone, heq, subtract_one_of_succ_eq b c' heq]
              · constructor
                · intro q hRes; cases hRes
                · intro q r hRes; cases hRes
    | some d =>
      cases c with
      | one =>
        cases b with
        | one =>
          constructor
          · exact divideWithRemainderAux_ne_none_none one one (some d) one hc
          · constructor
            · intro r hr; cases hr
            · constructor
              · intro r hRes; cases hRes
              · constructor
                · intro q hRes
                  cases hRes
                  cases hc with
                  | inl hlt => exact absurd hlt (not_lt_one one)
                  | inr heq =>
                    have honef : ¬ (one < one) := fun h => not_lt_one one h
                    simp [honef, add_one, add_comm]
                · intro q r hRes; cases hRes
        | successor b' =>
          let b := successor b'
          have hb := one_lt_succ b'
          constructor
          · exact divideWithRemainderAux_ne_none_none one b (some d) one hc
          · constructor
            · intro r hr; cases hr
            · constructor
              · intro r hRes; cases hRes
              · constructor
                · intro q hRes
                  cases hRes
                  cases d with
                  | one =>
                    have hcone : one ≠ b := ne_of_lt hb
                    rw [divideWithRemainderOrigOptionSome b one one one hc]
                    by_cases hone : one < b
                    · rw [if_lt_pos_named b hone
                        (divideWithRemainderOrigSome b hone one one one hc) (one + one),
                      divideWithRemainderOrigSome_ne b hone one one one hc hcone]
                      dsimp [divideWithRemainderOrigSomeLt, divideWithRemainderOrigSomeBase]
                      rw [succ_self_add_balance (subtract b one hone) (subtract b one hone),
                        orig_some_one_lt b hone]
                    · exact absurd hb hone
                  | successor d' =>
                    have hcone : one ≠ b := ne_of_lt hb
                    rw [divideWithRemainderOrigOptionSome b (successor d') one one hc]
                    by_cases hone : one < b
                    · rw [if_lt_pos_named b hone
                        (divideWithRemainderOrigSome b hone (successor d') one one hc) (one + successor d'),
                      divideWithRemainderOrigSome_ne b hone (successor d') one one hc hcone]
                      dsimp [divideWithRemainderOrigSomeLt, divideWithRemainderOrigSomeBase]
                      calc (d' * b + subtract b one hone).successor.successor
                          + subtract b one hone
                          = d' * b + subtract b one hone + one.successor + subtract b one hone := by
                            rw [succ_self_add_balance (d' * b + subtract b one hone)
                              (subtract b one hone)]
                        _ = d' * b + b * one.successor := orig_some_one_lt' b hone (d' * b)
                        _ = b * successor (successor d') := by
                              calc d' * b + (b + b)
                                  = (d' * b + b) + b := by rw [add_assoc]
                                _ = (b * d' + b) + b := by rw [multiply_comm]
                                _ = b * (successor d') + b := by rw [←multiply_succ]
                                _ = b * (successor (successor d')) := by rw [←multiply_succ]
                    · exact absurd hb hone
                · intro q r hRes; cases hRes
      | successor c' =>
        have hlt := subtract_lt_of_succ_le hc
        cases hc with
        | inl hlt' =>
          cases b with
          | one =>
            exfalso
            exact not_lt_one (successor c') hlt'
          | successor b' =>
            let b := successor b'
            have hb := one_lt_succ b'
            constructor
            · exact divideWithRemainderAux_ne_none_none one b (some d) (successor c') (Or.inl hlt')
            · constructor
              · intro r hr; cases hr; exact hlt
              · constructor
                · intro r hRes; cases hRes
                · constructor
                  · intro q hRes; cases hRes
                  · intro q r hRes
                    cases hRes
                    have hne : successor c' ≠ b := fun heq =>
                      not_lt_self _ (heq ▸ hlt')
                    rw [divideWithRemainderOrigOptionSome b d one (successor c') (Or.inl hlt')]
                    by_cases hone : one < b
                    · rw [if_lt_pos_named b hone
                        (divideWithRemainderOrigSome b hone d one (successor c') (Or.inl hlt')) (one + d),
                      divideWithRemainderOrigSome_ne b hone d one (successor c') (Or.inl hlt') hne]
                      dsimp [divideWithRemainderOrigSomeLt, divideWithRemainderOrigSomeBase]
                      cases d with
                      | one =>
                        rw [succ_self_add_balance (subtract b one hone)
                            (subtract b (successor c') hlt'),
                          orig_some_one_step b hone, add_assoc, ←subtract_succ_add_one b c' hlt',
                          multiply_one]
                      | successor q' =>
                        calc (q' * b + subtract b one hone).successor.successor
                            + subtract b (successor c') hlt'
                            = q' * b + subtract b one hone + one.successor
                                + subtract b (successor c') hlt' := by
                              rw [succ_self_add_balance (q' * b + subtract b one hone)
                                (subtract b (successor c') hlt')]
                          _ = q' * b + (b + one + subtract b (successor c') hlt') := by
                              exact orig_some_one_step' b hone (q' * b) (subtract b (successor c') hlt')
                          _ = b * (successor q') + subtract b c' (lt_of_succ_le (Or.inl hlt')) := by
                              exact orig_some_q_mul b q' c' hlt'
                    · exact absurd hb hone
        | inr heq =>
          cases b with
          | one => exact absurd heq (fun h => by cases h)
          | successor b' =>
            let b := successor b'
            have hb := one_lt_succ b'
            constructor
            · exact divideWithRemainderAux_ne_none_none one b (some d) (successor c') (Or.inr heq)
            · constructor
              · intro r hr; cases hr; exact subtract_lt_of_succ_le (Or.inr heq)
              · constructor
                · intro r hRes; cases hRes
                · constructor
                  · intro q hRes; cases hRes
                  · intro q r hRes
                    cases hRes
                    rw [divideWithRemainderOrigOptionSome b d one (successor c') (Or.inr heq)]
                    by_cases hone : one < b
                    · rw [if_lt_pos_named b hone
                        (divideWithRemainderOrigSome b hone d one (successor c') (Or.inr heq)) (one + d),
                      divideWithRemainderOrigSome_eq b hone d one (successor c') heq]
                      dsimp [divideWithRemainderOrigSomeBase, subtract_one_of_succ_eq b c' heq, add_one]
                      cases d with
                      | one =>
                        rw [succ_self_eq (subtract b one hone), orig_some_one_step b hone, multiply_one,
                          subtract_one_of_succ_eq b c' heq]
                      | successor d' =>
                        have hrem := subtract_one_of_succ_eq b c' heq
                        calc (d' * b + subtract b one hone).successor.successor
                            = d' * b + subtract b one hone + one.successor := by
                              rw [succ_self_eq (d' * b + subtract b one hone)]
                          _ = d' * b + (b + one) := by
                              calc d' * b + subtract b one hone + one.successor
                                  = d' * b + (subtract b one hone + one.successor) := by rw [←add_assoc]
                                _ = d' * b + (b + one) := by rw [orig_some_one_step b hone]
                          _ = b * (successor d') + subtract b c' (lt_of_succ_le (Or.inr heq)) := by
                              calc d' * b + (b + one)
                                  = (d' * b + b) + one := by rw [←add_assoc]
                                _ = (b * d' + b) + one := by rw [multiply_comm]
                                _ = b * (successor d') + one := by rw [←multiply_succ]
                                _ = b * (successor d') + subtract b c' (lt_of_succ_le (Or.inr heq)) := by
                                      rw [hrem]
                    · exact absurd hb hone
  | successor a ih =>
    unfold divideWithRemainderAux
    cases d with
    | none =>
      cases c with
      | one =>
        cases b with
        | one =>
          have hspec := ih (some one) one (Or.inr rfl)
          refine ⟨hspec.1, hspec.2.1, ?_, ?_, ?_⟩
          · intro r hRes
            cases hc with
            | inl hlt => exact absurd hlt (not_lt_one one)
            | inr hcEq =>
              exact (add_one a).trans (hspec.2.2.1 hRes)
          · intro q hRes
            cases hc with
            | inl hlt => exact absurd hlt (not_lt_one one)
            | inr hcEq =>
              exact (add_one a).trans (hspec.2.2.2.1 hRes)
          · intro q r hRes
            cases hc with
            | inl hlt => exact absurd hlt (not_lt_one one)
            | inr hcEq =>
              exact (add_one a).trans (hspec.2.2.2.2 hRes)
        | successor b' =>
          let b := successor b'
          have hb := one_lt_succ b'
          have hspec := ih (some one) b (Or.inr rfl)
          have horig :=
            divideWithRemainderOrigNone_reset b hb a
          refine ⟨hspec.1, hspec.2.1, ?_, ?_, ?_⟩
          · intro r hRes; exact horig.trans (hspec.2.2.1 hRes)
          · intro q hRes; exact horig.trans (hspec.2.2.2.1 hRes)
          · intro q r hRes; exact horig.trans (hspec.2.2.2.2 hRes)
      | successor c' =>
        have hspec := ih none c' (le_of_succ_le hc)
        have horig :=
          divideWithRemainderOrigNone_step b a c' hc
        refine ⟨hspec.1, hspec.2.1, ?_, ?_, ?_⟩
        · intro r hRes; exact horig.trans (hspec.2.2.1 hRes)
        · intro q hRes; exact horig.trans (hspec.2.2.2.1 hRes)
        · intro q r hRes; exact horig.trans (hspec.2.2.2.2 hRes)
    | some d =>
      cases c with
      | one =>
        cases b with
        | one =>
          have hspec := ih (some d.successor) one (Or.inr rfl)
          have horig : successor a + d = a + d.successor := by
            simp [add_succ, add_comm]
          refine ⟨hspec.1, hspec.2.1, ?_, ?_, ?_⟩
          · intro r hRes; exact horig.trans (hspec.2.2.1 hRes)
          · intro q hRes; exact horig.trans (hspec.2.2.2.1 hRes)
          · intro q r hRes; exact horig.trans (hspec.2.2.2.2 hRes)
        | successor b' =>
          let b := successor b'
          have hb := one_lt_succ b'
          have hspec := ih (some d.successor) b (Or.inr rfl)
          have horig :=
            divideWithRemainderOrigSome_reset b hb d a
          refine ⟨hspec.1, hspec.2.1, ?_, ?_, ?_⟩
          · intro r hRes; exact horig.trans (hspec.2.2.1 hRes)
          · intro q hRes; exact horig.trans (hspec.2.2.2.1 hRes)
          · intro q r hRes; exact horig.trans (hspec.2.2.2.2 hRes)
      | successor c' =>
        cases b with
        | one =>
          exfalso
          cases hc with
          | inl hlt => exact not_lt_one (successor c') hlt
          | inr heq => exact absurd heq (fun h => by cases h)
        | successor b' =>
          let b := successor b'
          have hb := one_lt_succ b'
          have hspec := ih (some d) c' (le_of_succ_le hc)
          have horig :=
            divideWithRemainderOrigSome_step b hb d a c' hc
          refine ⟨hspec.1, hspec.2.1, ?_, ?_, ?_⟩
          · intro r hRes; exact horig.trans (hspec.2.2.1 hRes)
          · intro q hRes; exact horig.trans (hspec.2.2.2.1 hRes)
          · intro q r hRes; exact horig.trans (hspec.2.2.2.2 hRes)

theorem divideWithRemainder_not_none_none (a b : Peano) :
    divideWithRemainder a b ≠ (none, none) := by
  intro h
  have hspec := divideWithRemainderAux_correct b a none b (Or.inr rfl)
  rw [divideWithRemainder] at h
  exact hspec.1 h

theorem divideWithRemainder_remainder_lt_b (a b : Peano) (q : Option Peano) (r : Peano)
    (h : divideWithRemainder a b = (q, some r)) : r < b := by
  rw [divideWithRemainder] at h
  exact divideWithRemainderAux_remainder_lt_b a b none b (Or.inr rfl) q r h

theorem divideWithRemainder_none_some (a b : Peano) (r : Peano)
    (h : divideWithRemainder a b = (none, some r)) : a = r := by
  have hspec := divideWithRemainderAux_correct b a none b (Or.inr rfl)
  have horig : divideWithRemainderOrigNone b a b (Or.inr rfl) = a := by
    simp [divideWithRemainderOrigNone]
  rw [divideWithRemainder] at h
  have := hspec.2.2.1 h
  simpa [horig] using this

theorem divideWithRemainder_some_none (a b : Peano) (q : Peano)
    (h : divideWithRemainder a b = (some q, none)) : a = b * q := by
  have hspec := divideWithRemainderAux_correct b a none b (Or.inr rfl)
  have horig : divideWithRemainderOrigNone b a b (Or.inr rfl) = a := by
    simp [divideWithRemainderOrigNone]
  rw [divideWithRemainder] at h
  have := hspec.2.2.2.1 h
  simpa [horig] using this

theorem divideWithRemainder_some_some (a b : Peano) (q r : Peano)
    (h : divideWithRemainder a b = (some q, some r)) : a = b * q + r := by
  have hspec := divideWithRemainderAux_correct b a none b (Or.inr rfl)
  have horig : divideWithRemainderOrigNone b a b (Or.inr rfl) = a := by
    simp [divideWithRemainderOrigNone]
  rw [divideWithRemainder] at h
  have := hspec.2.2.2.2 h
  simpa [horig] using this

theorem add_rot (a b c : Peano) : a + b + c = (a + c) + b := by
  calc a + b + c
      _ = a + (b + c) := by rw [add_assoc]
      _ = a + (c + b) := by rw [add_comm b c]
      _ = (a + c) + b := by rw [←add_assoc]

theorem add_cancel_comm' {a b c : Peano} (h : b + a = b + c) : a = c :=
  add_cancel_right a c b (by rw [add_comm a b, add_comm c b, h])

theorem add_cancel_comm'' {a b c : Peano} (h : a + b = c + b) : a = c :=
  add_cancel_right a c b h

theorem lt_of_add_eq_right {a b c : Peano} (h : a + b = c) : a < c := by
  rw [←h]
  exact lt_add_left a b

theorem add_rot_symm (a b c : Peano) : (a + c) + b = a + b + c := by
  rw [add_rot]

mutual
  theorem not_mult_remainder_eq (b q r c' : Peano) (hlt : r < b)
      (h : b * q + r = b * c') : False := by
    induction q with
    | one =>
      rw [multiply_one] at h
      cases c' with
      | one =>
        rw [multiply_one] at h
        have hgt : b < b + r := lt_add_left b r
        rw [h] at hgt
        exact not_lt_self b hgt
      | successor c'' =>
        rw [multiply_succ, add_comm] at h
        have hb : b + r = b + b * c'' := by
          calc b + r
              _ = r + b := by rw [add_comm]
              _ = b * c'' + b := h
              _ = b + b * c'' := by rw [add_comm (b * c'') b]
        have hr : r = b * c'' := add_cancel_comm' hb
        rw [hr] at hlt
        cases c'' with
        | one => exact not_lt_self b hlt
        | successor c''' =>
          have hgt : b < b + b * c''' := lt_add_left b (b * c''')
          rw [multiply_succ, add_comm] at hlt
          exact not_lt_of_lt hlt hgt
    | successor q' ih =>
      rw [multiply_succ] at h
      cases c' with
      | one =>
        have hzl : b * q' + r < b := lt_of_add_eq_right (by
          rw [add_rot_symm, h, multiply_one])
        cases q' with
        | one =>
          rw [multiply_one] at hzl
          exact not_lt_of_lt (lt_add_left b r) hzl
        | successor q'' =>
          have hgt : b < b * q'' + b := lt_add_right (b * q'') b
          have hmid : b * q'' + b < b * q'' + b + r := lt_add_left (b * q'' + b) r
          have hchain : b < b * q'' + b + r := lt_trans hgt hmid
          rw [multiply_succ, add_comm] at hzl
          rw [add_comm r] at hzl
          exact not_lt_of_lt hchain hzl
      | successor c'' =>
        have hmain : b * q' + r = b * c'' := by
          exact add_cancel_comm'' (by rw [add_rot_symm, h, multiply_succ, add_comm (b * c'') b])
        exact not_mult_remainder_eq b q' r c'' hlt hmain

  theorem not_mult_remainder_eq_add (b q r c' : Peano) (hlt : r < b)
      (h : b * q + r = b + b * c') : False := by
    cases q with
    | one =>
      rw [multiply_one] at h
      have hr : r = b * c' := add_cancel_comm' h
      rw [hr] at hlt
      cases c' with
      | one => exact not_lt_self b hlt
      | successor c'' =>
        have hgt : b < b + b * c'' := lt_add_left b (b * c'')
        rw [multiply_succ, add_comm] at hlt
        exact not_lt_of_lt hlt hgt
    | successor q' =>
      rw [multiply_succ] at h
      cases c' with
      | one =>
        have h' : b * q' + r = b := add_cancel_comm'' (by rw [←add_rot, h, multiply_one])
        cases q' with
        | one =>
          rw [multiply_one] at h'
          have hgt : b < b + r := lt_add_left b r
          rw [h'] at hgt
          exact not_lt_self b hgt
        | successor q'' =>
          have hrest : b * (successor q'') + r = b := add_cancel_comm'' (by
            rw [←add_rot, h, multiply_one])
          have hgt : b < b * q'' + b := lt_add_right (b * q'') b
          have hmid : b * q'' + b < b * q'' + b + r := lt_add_left (b * q'' + b) r
          have hchain : b < b * q'' + b + r := lt_trans hgt hmid
          have hchain' : b < b * (successor q'') + r := by
            simpa [multiply_succ, add_comm] using hchain
          rw [hrest] at hchain'
          exact not_lt_self b hchain'
      | successor c'' =>
        have hrest : b * q' + r = b + b * c'' := by
          exact add_cancel_comm'' (by
            rw [add_rot_symm, h, multiply_succ, add_comm (b * c'') b, add_comm b (b + b * c'')])
        have hmain : b * q' + r = b * (successor c'') := by
          calc b * q' + r
              _ = b + b * c'' := hrest
              _ = b * (successor c'') := by rw [multiply_succ, add_comm]
        exact not_mult_remainder_eq b q' r (successor c'') hlt hmain
end

theorem mul_ge_self (b q : Peano) : b ≤ b * q := by
  cases q with
  | one => exact Or.inr (multiply_one b).symm
  | successor q' =>
    exact Or.inl (by
      rw [multiply_succ, add_comm]
      exact lt_add_left b (b * q'))

theorem mul_add_ge_self (b q r : Peano) : b ≤ b * q + r := by
  cases mul_ge_self b q with
  | inl hlt => exact Or.inl (lt_trans hlt (lt_add_left (b * q) r))
  | inr heq =>
    rw [← heq]
    exact Or.inl (lt_add_left b r)

theorem div_rem_unique (b q r q' r' : Peano) (hr : r < b) (hr' : r' < b)
    (h : b * q + r = b * q' + r') : q = q' ∧ r = r' := by
  induction q generalizing q' with
  | one =>
    cases q' with
    | one =>
      exact ⟨rfl, add_cancel_comm' h⟩
    | successor q'' =>
      have hr_eq : r = b * q'' + r' := by
        have h' : b + r = b + (b * q'' + r') := by
          calc b + r
              _ = b * one + r := by rw [multiply_one]
              _ = b * successor q'' + r' := h
              _ = (b * q'' + b) + r' := by rw [multiply_succ]
              _ = (b + b * q'') + r' := by rw [add_comm (b * q'') b]
              _ = b + (b * q'' + r') := by rw [add_assoc]
        exact add_cancel_comm' h'
      have hge := mul_add_ge_self b q'' r'
      rw [← hr_eq] at hge
      cases hge with
      | inl hlt_rb => exact False.elim (not_lt_of_lt hr hlt_rb)
      | inr heq =>
        rw [heq] at hr
        exact False.elim (not_lt_self r hr)
  | successor q ih =>
    cases q' with
    | one =>
      have hr_eq : r' = b * q + r := by
        have h' : b + r' = b + (b * q + r) := by
          calc b + r'
              _ = b * one + r' := by rw [multiply_one]
              _ = b * successor q + r := h.symm
              _ = (b * q + b) + r := by rw [multiply_succ]
              _ = (b + b * q) + r := by rw [add_comm (b * q) b]
              _ = b + (b * q + r) := by rw [add_assoc]
        exact add_cancel_comm' h'
      have hge := mul_add_ge_self b q r
      rw [← hr_eq] at hge
      cases hge with
      | inl hlt_rb => exact False.elim (not_lt_of_lt hr' hlt_rb)
      | inr heq =>
        rw [heq] at hr'
        exact False.elim (not_lt_self r' hr')
    | successor q'' =>
      have hside : b * q + r + b = b * q'' + r' + b := by
        calc b * q + r + b
            _ = (b * q + b) + r := by rw [add_rot]
            _ = b * successor q + r := by rw [multiply_succ]
            _ = b * successor q'' + r' := h
            _ = (b * q'' + b) + r' := by rw [multiply_succ]
            _ = b * q'' + r' + b := by rw [add_rot]
      have h' : b * q + r = b * q'' + r' := add_cancel_comm'' hside
      obtain ⟨hq, hr_eq⟩ := ih q'' h'
      exact ⟨congrArg successor hq, hr_eq⟩

theorem divideWithRemainder_eq_of_none_some (a b r : Peano) (hlt : a < b)
    (ha : a = r) : divideWithRemainder a b = (none, some r) := by
  match hres : divideWithRemainder a b with
  | (none, none) => exact False.elim (divideWithRemainder_not_none_none a b hres)
  | (none, some r') =>
    have ha' := divideWithRemainder_none_some a b r' hres
    exact congrArg (fun x => (none, some x)) (ha'.symm.trans ha)
  | (some q, none) =>
    have ha' := divideWithRemainder_some_none a b q hres
    cases mul_ge_self b q with
    | inl hlt_bq =>
      have hlt' : b < a := ha' ▸ hlt_bq
      exact False.elim (not_lt_of_lt hlt hlt')
    | inr heq =>
      have heq_ab : b = a := heq.trans ha'.symm
      rw [heq_ab] at hlt
      exact False.elim (not_lt_self a hlt)
  | (some q, some r') =>
    have ha' := divideWithRemainder_some_some a b q r' hres
    cases mul_add_ge_self b q r' with
    | inl hlt_ba =>
      have hlt' : b < a := ha' ▸ hlt_ba
      exact False.elim (not_lt_of_lt hlt hlt')
    | inr heq =>
      have heq_ab : b = a := heq.trans ha'.symm
      rw [heq_ab] at hlt
      exact False.elim (not_lt_self a hlt)

theorem divideWithRemainder_eq_of_some_none (a b q : Peano) (ha : a = b * q) :
    divideWithRemainder a b = (some q, none) := by
  match hres : divideWithRemainder a b with
  | (none, none) => exact False.elim (divideWithRemainder_not_none_none a b hres)
  | (none, some r) =>
    have ha' := divideWithRemainder_none_some a b r hres
    have hlt := divideWithRemainder_remainder_lt_b a b none r hres
    have hlt' : b * q < b := by
      rw [← ha, ha']
      exact hlt
    cases mul_ge_self b q with
    | inl hlt_bq => exact False.elim (not_lt_of_lt hlt_bq hlt')
    | inr heq =>
      rw [← heq] at hlt'
      exact False.elim (not_lt_self b hlt')
  | (some q', none) =>
    have ha' := divideWithRemainder_some_none a b q' hres
    have hq : q' = q := multiply_cancel_left b q' q (ha'.symm.trans ha)
    exact congrArg (fun x => (some x, none)) hq
  | (some q', some r) =>
    have ha' := divideWithRemainder_some_some a b q' r hres
    have hlt := divideWithRemainder_remainder_lt_b a b (some q') r hres
    exact False.elim (not_mult_remainder_eq b q' r q hlt (ha'.symm.trans ha))

theorem divideWithRemainder_self (a : Peano) :
    divideWithRemainder a a = (some one, none) :=
  divideWithRemainder_eq_of_some_none a a one (multiply_one a).symm

theorem isDivisibleCorrect (a b : Peano) : Divisible a b ↔ isDivisible a b := by
  unfold Divisible isDivisible
  apply Iff.intro
  · intro h
    rcases h with ⟨c, hc⟩
    have hres := divideWithRemainder_eq_of_some_none a b c hc.symm
    simp [hres]
  · intro h
    match hres : divideWithRemainder a b with
    | (none, none) =>
      exact False.elim (divideWithRemainder_not_none_none a b hres)
    | (some q, none) =>
      exact ⟨q, (divideWithRemainder_some_none a b q hres).symm⟩
    | (none, some _) =>
      simp [hres] at h
    | (some _, some _) =>
      simp [hres] at h

theorem divideWithRemainder_eq_of_some_some (a b q r : Peano) (hlt : r < b)
    (ha : a = b * q + r) : divideWithRemainder a b = (some q, some r) := by
  match hres : divideWithRemainder a b with
  | (none, none) => exact False.elim (divideWithRemainder_not_none_none a b hres)
  | (none, some r') =>
    have ha' := divideWithRemainder_none_some a b r' hres
    have hlt' := divideWithRemainder_remainder_lt_b a b none r' hres
    have hlt_a : a < b := by
      rw [ha']
      exact hlt'
    cases mul_add_ge_self b q r with
    | inl hlt_ba =>
      have hlt_ba' : b < a := ha ▸ hlt_ba
      exact False.elim (not_lt_of_lt hlt_a hlt_ba')
    | inr heq =>
      have heq_ab : b = a := heq.trans ha.symm
      rw [heq_ab] at hlt_a
      exact False.elim (not_lt_self a hlt_a)
  | (some q', none) =>
    have ha' := divideWithRemainder_some_none a b q' hres
    exact False.elim (not_mult_remainder_eq b q r q' hlt (ha.symm.trans ha'))
  | (some q', some r') =>
    have ha' := divideWithRemainder_some_some a b q' r' hres
    have hlt' := divideWithRemainder_remainder_lt_b a b (some q') r' hres
    obtain ⟨hq, hr⟩ := div_rem_unique b q r q' r' hlt hlt' (ha.symm.trans ha')
    exact Prod.ext (congrArg some hq.symm) (congrArg some hr.symm)

/-- Dividing `a + b` by `b` increments the quotient of `a / b` by one. -/
theorem divideWithRemainder_add_right (a b : Peano) :
    divideWithRemainder (a + b) b =
      match divideWithRemainder a b with
      | (none, r) => (some one, r)
      | (some q, r) => (some (successor q), r) := by
  match ha : divideWithRemainder a b with
  | (none, none) =>
    exact (divideWithRemainder_not_none_none a b ha).elim
  | (none, some r) =>
    have har := divideWithRemainder_none_some a b r ha
    have hlt := divideWithRemainder_remainder_lt_b a b none r ha
    have hab : a + b = b * one + r := by
      rw [har, multiply_one, add_comm]
    have hres := divideWithRemainder_eq_of_some_some (a + b) b one r hlt hab
    simpa [ha] using hres
  | (some q, none) =>
    have haq := divideWithRemainder_some_none a b q ha
    have hab : a + b = b * successor q := by
      rw [haq, multiply_succ]
    have hres := divideWithRemainder_eq_of_some_none (a + b) b (successor q) hab
    simpa [ha] using hres
  | (some q, some r) =>
    have haq := divideWithRemainder_some_some a b q r ha
    have hlt := divideWithRemainder_remainder_lt_b a b (some q) r ha
    have hab : a + b = b * successor q + r := by
      rw [haq, multiply_succ]
      calc
        b * q + r + b = b * q + (r + b) := by rw [add_assoc]
        _ = b * q + (b + r) := by rw [add_comm r b]
        _ = b * q + b + r := by rw [← add_assoc]
    have hres :=
      divideWithRemainder_eq_of_some_some (a + b) b (successor q) r hlt hab
    simpa [ha] using hres

theorem divideWithRemainder_none_some_divisible (a b : Peano) (r : Peano) (h : Divisible a b)
    (hres : divideWithRemainder a b = (none, some r)) : False := by
  have ha := divideWithRemainder_none_some a b r hres
  have hlt := divideWithRemainder_remainder_lt_b a b none r hres
  rw [ha] at h
  rcases h with ⟨c, hc⟩
  cases one_le c with
  | inl hc_one =>
    rw [hc_one, multiply_one] at hc
    rw [hc] at hlt
    exact not_lt_self r hlt
  | inr hc_lt =>
    cases c with
    | one => exact absurd hc_lt (not_lt_self one)
    | successor c' =>
      rw [multiply_succ, add_comm] at hc
      have hgt : b < b + b * c' := lt_add_left b (b * c')
      rw [hc] at hgt
      exact not_lt_of_lt hlt hgt

theorem divideWithRemainder_some_some_divisible (a b : Peano) (q r : Peano) (h : Divisible a b)
    (hres : divideWithRemainder a b = (some q, some r)) : False := by
  have ha := divideWithRemainder_some_some a b q r hres
  have hlt := divideWithRemainder_remainder_lt_b a b (some q) r hres
  rcases h with ⟨c, hc⟩
  rw [ha] at hc
  cases c with
  | one =>
    rw [multiply_one] at hc
    cases q with
    | one =>
      rw [multiply_one] at hc
      have hgt : b < b + r := lt_add_left b r
      rw [←hc] at hgt
      exact not_lt_self b hgt
    | successor q' =>
      rw [multiply_succ] at hc
      have hzl : b * q' + r < b := lt_of_add_eq_right (by rw [add_rot_symm, ←hc])
      cases q' with
      | one =>
        rw [multiply_one] at hzl
        exact not_lt_of_lt (lt_add_left b r) hzl
      | successor q'' =>
        have hgt : b < b * q'' + b := lt_add_right (b * q'') b
        have hmid : b * q'' + b < b * q'' + b + r := lt_add_left (b * q'' + b) r
        have hchain : b < b * q'' + b + r := lt_trans hgt hmid
        rw [multiply_succ, add_comm] at hzl
        rw [add_comm r] at hzl
        exact not_lt_of_lt hchain hzl
  | successor c' =>
    rw [multiply_succ, add_comm] at hc
    exact not_mult_remainder_eq_add b q r c' hlt (by rw [←hc])

def divide (a b : Peano) (h : Divisible a b) : Peano :=
  match hres : divideWithRemainder a b with
  | (some q, none) => q
  | (none, none) => False.elim (divideWithRemainder_not_none_none a b hres)
  | (none, some r) => False.elim (divideWithRemainder_none_some_divisible a b r h hres)
  | (some q, some r) => False.elim (divideWithRemainder_some_some_divisible a b q r h hres)

theorem divide_correct (a b : Peano) (h : Divisible a b) : b * divide a b h = a := by
  unfold divide
  split
  next q hres =>
    rw [divideWithRemainder_some_none a b q hres]
  next hres =>
    exact False.elim (divideWithRemainder_not_none_none a b hres)
  next r hres =>
    exact False.elim (divideWithRemainder_none_some_divisible a b r h hres)
  next q r hres =>
    exact False.elim (divideWithRemainder_some_some_divisible a b q r h hres)

theorem exists_divide_of_tryDivide {x y z : Peano} (h : tryDivide x y = some z) :
    ∃ h', divide x y h' = z := by
  have hres : divideWithRemainder x y = (some z, none) := by
    unfold tryDivide at h
    split at h
    · next q hq =>
      injection h with hz
      rw [← hz]
      exact hq
    · next _ _ =>
      cases h
  have hdiv : Divisible x y := ⟨z, (divideWithRemainder_some_none x y z hres).symm⟩
  refine ⟨hdiv, ?_⟩
  exact multiply_cancel_left y (divide x y hdiv) z (by
    rw [divide_correct x y hdiv, divideWithRemainder_some_none x y z hres])

theorem tryDivide_of_divide {x y z : Peano} (h : ∃ h', divide x y h' = z) :
    tryDivide x y = some z := by
  obtain ⟨hdiv, heq⟩ := h
  have hres : divideWithRemainder x y = (some z, none) := by
    unfold divide at heq
    split at heq
    · next q hq =>
      rw [← heq]
      exact hq
    · next hq =>
      exact False.elim (divideWithRemainder_not_none_none x y hq)
    · next r hq =>
      exact False.elim (divideWithRemainder_none_some_divisible x y r hdiv hq)
    · next q r hq =>
      exact False.elim (divideWithRemainder_some_some_divisible x y q r hdiv hq)
  simp [tryDivide, hres]

/-- A successful `tryDivide` recovers the multiplicative relation `y * q = x`. -/
theorem eq_of_tryDivide_mul {x y q : Peano} (h : tryDivide x y = some q) :
    y * q = x := by
  obtain ⟨hdiv, heq⟩ := exists_divide_of_tryDivide h
  simpa [heq] using divide_correct x y hdiv

theorem divide_multiply_eq (x y : Peano) : ∃ h, divide (y * x) y h = x := by
  let h : Divisible (y * x) y := ⟨x, rfl⟩
  refine ⟨h, ?_⟩
  exact multiply_cancel_left y (divide (y * x) y h) x (divide_correct (y * x) y h)

/-- `tryDivide` inverts left-multiplication: dividing `b * a` by `b` recovers `a`. -/
theorem tryDivide_mul (a b : Peano) : tryDivide (b * a) b = some a :=
  tryDivide_of_divide (divide_multiply_eq a b)

theorem divide_add (x y z : Peano) (h : Divisible x z) (h2 : Divisible y z) :
  ∃ h3, divide x z h + divide y z h2 = divide (x + y) z h3 := by
  let h3 : Divisible (x + y) z :=
    ⟨divide x z h + divide y z h2, by
      rw [multiply_add, divide_correct x z h, divide_correct y z h2]⟩
  refine ⟨h3, ?_⟩
  exact multiply_cancel_left z (divide x z h + divide y z h2) (divide (x + y) z h3) (by
    rw [multiply_add, divide_correct x z h, divide_correct y z h2, divide_correct (x + y) z h3])

theorem multiply_divide_assoc (x y z : Peano) (h : Divisible y z) :
  ∃ h2, x * divide y z h = divide (x * y) z h2 := by
  let h2 : Divisible (x * y) z := multiply_divide_assoc_h h
  refine ⟨h2, ?_⟩
  exact multiply_cancel_left z (x * divide y z h) (divide (x * y) z h2) (by
    rw [←multiply_assoc]
    have hzx : z * x = x * z := multiply_comm z x
    rw [hzx, multiply_assoc, divide_correct y z h, divide_correct (x * y) z h2])

theorem divide_lt_of_lt {x y z : Peano}
  (h1 : Divisible x z) (h2 : Divisible y z) (h3 : x > y) :
  divide y z h2 < divide x z h1 := by
  have hmul : z * divide y z h2 < z * divide x z h1 := by
    rw [divide_correct y z h2, divide_correct x z h1]
    exact h3
  have hmul' : divide y z h2 * z < divide x z h1 * z := by
    rw [multiply_comm (divide y z h2) z]
    rw [multiply_comm (divide x z h1) z]
    exact hmul
  exact lt_multiply_right_cancel hmul'

theorem divide_subtract_distrib {x y z : Peano}
  (h1 : Divisible x z) (h2 : Divisible y z) (h3 : x > y) :
  ∃ h4 h5, divide (subtract x y h3) z h4 = subtract (divide x z h1) (divide y z h2) h5 := by
  let qx : Peano := divide x z h1
  let qy : Peano := divide y z h2
  have h5 : qy < qx := divide_lt_of_lt h1 h2 h3
  have hmul_sub : ∃ hmul_lt, z * subtract qx qy h5 = subtract (z * qx) (z * qy) hmul_lt :=
    multiply_subtract z qx qy h5
  rcases hmul_sub with ⟨hmul_lt, hmul_sub_eq⟩
  have hsub_eq : z * subtract qx qy h5 = subtract x y h3 := by
    rw [hmul_sub_eq]
    exact subtract_eq_of_eq hmul_lt h3 (divide_correct x z h1) (divide_correct y z h2)
  let h4 : Divisible (subtract x y h3) z := ⟨subtract qx qy h5, hsub_eq⟩
  refine ⟨h4, h5, ?_⟩
  exact multiply_cancel_left z (divide (subtract x y h3) z h4) (subtract qx qy h5) (by
    rw [divide_correct (subtract x y h3) z h4, hsub_eq])

theorem divide_divide_eq_divide_multiply (x y z : Peano) (h1 : Divisible x (y * z)) :
  ∃ h2 h3, divide x (y * z) h1 = divide (divide x y h2) z h3 := by
  let h2 : Divisible x y := divide_divide_eq_divide_multiply_h2 h1
  let q : Peano := divide x (y * z) h1
  let r : Peano := divide x y h2
  have hzq_eq_r : z * q = r := by
    have hyzq_eq_yr : y * (z * q) = y * r := by
      rw [← multiply_assoc]
      rw [divide_correct x (y * z) h1]
      rw [divide_correct x y h2]
    exact multiply_cancel_left y (z * q) r hyzq_eq_yr
  let h3 : Divisible r z := ⟨q, hzq_eq_r⟩
  refine ⟨h2, h3, ?_⟩
  have hmul : z * q = z * divide r z h3 := by
    rw [hzq_eq_r]
    rw [divide_correct r z h3]
  exact multiply_cancel_left z q (divide r z h3) hmul

end Peano

end ZeroMath.Numbers.OrdinalNatural
