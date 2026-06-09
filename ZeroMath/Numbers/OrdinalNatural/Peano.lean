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

def predecessor (a : Peano) (h : a ≠ one) : Peano :=
  match a with
  | one => by contradiction
  | successor b => b

def add (a : Peano) : Peano → Peano
  | one => successor a
  | successor b => successor (add a b)

instance : Add Peano where
  add := add

@[simp]
theorem add_one (a : Peano) : a + one = successor a := by rfl

@[simp]
theorem one_add (a : Peano) : one + a = successor a := by
  induction a with
  | one => rfl
  | successor a ih =>
    show successor (one + a) = successor (successor a)
    rw [ih]

@[simp]
theorem add_succ (a b : Peano) : a + successor b = successor (a + b) := by rfl

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
  | one =>
    show successor (successor a) = successor (successor a)
    rfl
  | successor b ih =>
    show successor (successor a + b) = successor (successor (a + b))
    rw [ih]

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

theorem lt_of_succ_lt {x y : Peano} (h : successor x < y) : x < y := by
  exact lt_trans LessThan.base h

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

theorem not_lt_of_lt {x y : Peano} (h : x < y) : ¬ (y < x) := by
  intro h2
  have h3 := lt_trans h h2
  exact not_lt_self x h3

theorem ne_of_lt {x y : Peano} (h : x < y) : x ≠ y := by
  intro heq
  subst heq
  exact not_lt_self x h

theorem one_lt_succ (x : Peano) : one < successor x := by
  induction x with
  | one => exact LessThan.base
  | successor x ih => exact LessThan.step ih

theorem one_le (x : Peano) : x = one ∨ one < x := by
  induction x with
  | one => exact Or.inl rfl
  | successor x _ => exact Or.inr (one_lt_succ x)

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

@[simp]
theorem multiply_one (a : Peano) : a * one = a := by rfl

@[simp]
theorem one_multiply (a : Peano) : one * a = a := by
  induction a with
  | one => rfl
  | successor a ih =>
    show one * a + one = successor a
    rw [ih, add_one]

@[simp]
theorem multiply_succ (a b : Peano) : a * successor b = a * b + a := by rfl

@[simp]
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

def isDivisibleRecursive (x a b : Peano) : Bool :=
  if b * x = a then
    true
  else
    match x with
    | one => false
    | successor x' => isDivisibleRecursive x' a b

def isDivisible (a b : Peano) : Bool :=
  isDivisibleRecursive a a b

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

theorem divide_rec_step_h {a b x : Peano}
  (h : ∀ y, successor x < y → b * y ≠ a)
  (h3 : ¬b * successor x = a) :
  ∀ y, x < y → b * y ≠ a := by
  intro y hy
  cases lt_successor_cases hy with
  | inl h_eq =>
    rw [h_eq]
    exact h3
  | inr h_lt =>
    exact h y h_lt

def divide_rec (a b x : Peano) (h : ∀ y, x < y → b * y ≠ a) (h2 : Divisible a b) : Peano :=
  if h3 : b * x = a then
    x
  else
    match x with
    | one =>
      False.elim (by
        rcases h2 with ⟨y, hy⟩
        cases one_le y with
        | inl h_eq =>
          rw [h_eq] at hy
          exact h3 hy
        | inr h_lt =>
          exact h y h_lt hy)
    | successor x' => divide_rec a b x' (divide_rec_step_h h h3) h2

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

def divide (a b : Peano) (h : Divisible a b) : Peano :=
  divide_rec a b a (by
    intro y hy heq
    have hle : y ≤ b * y := le_multiply_right y b
    have hlt : a < b * y := lt_of_lt_le hy hle
    rw [heq] at hlt
    exact not_lt_self a hlt) h

theorem divide_rec_correct (a b x : Peano)
  (h : ∀ y, x < y → b * y ≠ a) (h2 : Divisible a b) :
  b * divide_rec a b x h h2 = a := by
  induction x with
  | one =>
    unfold divide_rec
    by_cases h3 : b * one = a
    · simp [h3]
    · simp
      exact False.elim (by
        rcases h2 with ⟨y, hy⟩
        cases one_le y with
        | inl h_eq =>
          rw [h_eq] at hy
          exact h3 hy
        | inr h_lt =>
          exact h y h_lt hy)
  | successor x ih =>
    unfold divide_rec
    by_cases h3 : b * x + b = a
    · simp [h3]
    · simp [h3]
      have h3' : ¬b * successor x = a := by
        intro h_eq
        rw [multiply_succ] at h_eq
        exact h3 h_eq
      exact ih (divide_rec_step_h h h3')

theorem divide_correct (a b : Peano) (h : Divisible a b) : b * divide a b h = a := by
  unfold divide
  exact divide_rec_correct a b a (by
    intro y hy heq
    have hle : y ≤ b * y := le_multiply_right y b
    have hlt : a < b * y := lt_of_lt_le hy hle
    rw [heq] at hlt
    exact not_lt_self a hlt) h

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

theorem divide_multiply_eq (x y : Peano) : ∃ h, divide (y * x) y h = x := by
  let h : Divisible (y * x) y := ⟨x, rfl⟩
  refine ⟨h, ?_⟩
  exact multiply_cancel_left y (divide (y * x) y h) x (divide_correct (y * x) y h)

theorem divide_add (x y z : Peano) (h : Divisible x z) (h2 : Divisible y z) :
  ∃ h3, divide x z h + divide y z h2 = divide (x + y) z h3 := by
  let h3 : Divisible (x + y) z :=
    ⟨divide x z h + divide y z h2, by
      rw [multiply_add, divide_correct x z h, divide_correct y z h2]⟩
  refine ⟨h3, ?_⟩
  exact multiply_cancel_left z (divide x z h + divide y z h2) (divide (x + y) z h3) (by
    rw [multiply_add, divide_correct x z h, divide_correct y z h2, divide_correct (x + y) z h3])

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

theorem multiply_divide_assoc (x y z : Peano) (h : Divisible y z) :
  ∃ h2, x * divide y z h = divide (x * y) z h2 := by
  let h2 : Divisible (x * y) z := multiply_divide_assoc_h h
  refine ⟨h2, ?_⟩
  exact multiply_cancel_left z (x * divide y z h) (divide (x * y) z h2) (by
    rw [←multiply_assoc]
    have hzx : z * x = x * z := multiply_comm z x
    rw [hzx, multiply_assoc, divide_correct y z h, divide_correct (x * y) z h2])

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

def power (a : Peano) : Peano → Peano
  | one => a
  | successor b => power a b * a

instance : HPow Peano Peano Peano where
  hPow := power

@[simp]
theorem power_one (a : Peano) : a ^ one = a := rfl

@[simp]
theorem power_succ (a b : Peano) : a ^ successor b = a ^ b * a := rfl

@[simp]
theorem one_power (a : Peano) : one ^ a = one := by
  induction a with
  | one => rfl
  | successor a ih =>
    show one ^ a * one = one
    rw [ih, multiply_one]

theorem power_add (x y z : Peano) : x ^ (y + z) = (x ^ y) * (x ^ z) := by
  induction z with
  | one =>
    show x ^ (y + one) = x ^ y * (x ^ one)
    rw [add_one, power_succ, power_one]
  | successor z ih =>
    show x ^ (y + successor z) = x ^ y * (x ^ successor z)
    rw [add_succ, power_succ, ih, power_succ]
    rw [multiply_assoc]

theorem power_multiply (x y z : Peano) : x ^ (y * z) = (x ^ y) ^ z := by
  induction z with
  | one =>
    show x ^ (y * one) = (x ^ y) ^ one
    rw [multiply_one, power_one]
  | successor z ih =>
    show x ^ (y * successor z) = (x ^ y) ^ successor z
    rw [multiply_succ, power_add, ih, power_succ]

theorem multiply_power (x y z : Peano) : (x * y) ^ z = (x ^ z) * (y ^ z) := by
  induction z with
  | one =>
    rw [power_one, power_one, power_one]
  | successor z ih =>
    rw [power_succ, power_succ, power_succ]
    rw [ih, multiply_assoc, ← multiply_assoc (y ^ z), multiply_comm (y ^ z) x,
      multiply_assoc x, ← multiply_assoc (x ^ z)]

def Power (e a : Peano) : Prop := ∃ b, b ^ e = a

theorem root_rec_step_h {e a x : Peano}
  (h : ∀ b, successor x < b → b ^ e ≠ a)
  (h3 : ¬ successor x ^ e = a) :
  ∀ b, x < b → b ^ e ≠ a := by
  intro b hb
  cases lt_successor_cases hb with
  | inl h_eq =>
    rw [h_eq]
    exact h3
  | inr h_lt =>
    exact h b h_lt

def root_rec (e a x : Peano) (h : ∀ b, x < b → b ^ e ≠ a) (h2 : Power e a) : Peano :=
  if h3 : x ^ e = a then
    x
  else
    match x with
    | one =>
      False.elim (by
        rcases h2 with ⟨b, hb⟩
        cases one_le b with
        | inl h_eq =>
          rw [h_eq] at hb
          exact h3 hb
        | inr h_lt =>
          exact h b h_lt hb)
    | successor x' =>
      root_rec e a x' (root_rec_step_h h h3) h2

theorem add_lt_add_right {a b : Peano} (c : Peano) (h : a < b) : a + c < b + c := by
  induction c with
  | one =>
    show successor a < successor b
    exact succ_lt_succ h
  | successor c ih =>
    show successor (a + c) < successor (b + c)
    exact succ_lt_succ ih

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
    have h_eq1 : subtract (subtract x y h) z h2 + z = subtract x y h := subtract_add_cancel (subtract x y h) z h2
    have h_eq2 : subtract (subtract x y h) z h2 + z + y = subtract x y h + y := by rw [h_eq1]
    rw [subtract_add_cancel x y h] at h_eq2
    have h_eq3 : subtract (subtract x y h) z h2 + (z + y) = x := by
      rw [←add_assoc]
      exact h_eq2
    have h_eq4 : subtract (subtract x y h) z h2 + (y + z) = x := by
      rw [add_comm z y] at h_eq3
      exact h_eq3
    have h_eq5 : subtract x (y + z) h3 + (y + z) = x := subtract_add_cancel x (y + z) h3
    have h_eq6 : subtract (subtract x y h) z h2 + (y + z) = subtract x (y + z) h3 + (y + z) := by
      rw [h_eq4, h_eq5]
    exact add_cancel_right _ _ _ h_eq6⟩

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

theorem root_rec_correct (e a x : Peano)
  (h : ∀ b, x < b → b ^ e ≠ a) (h2 : Power e a) :
  (root_rec e a x h h2) ^ e = a := by
  unfold root_rec
  split
  · assumption
  · rename_i h3
    cases x with
    | one =>
      exfalso
      rcases h2 with ⟨b, hb⟩
      cases one_le b with
      | inl h_eq =>
        rw [h_eq] at hb
        exact h3 hb
      | inr h_lt =>
        exact h b h_lt hb
    | successor x' =>
      exact root_rec_correct e a x' (root_rec_step_h h h3) h2

def root (e a : Peano) (h : Power e a) : Peano :=
  root_rec e a a (by
    intro b hb heq
    have hle : b ≤ b ^ e := le_power b e
    have hlt : a < b ^ e := lt_of_lt_le hb hle
    rw [heq] at hlt
    exact not_lt_self a hlt) h

theorem root_correct (e a : Peano) (h : Power e a) : (root e a h) ^ e = a := by
  unfold root
  apply root_rec_correct

theorem root_power_eq (e x : Peano) : ∃ h, root e (x ^ e) h = x := by
  let h : Power e (x ^ e) := ⟨x, rfl⟩
  exists h
  exact power_cancel_left e (root e (x ^ e) h) x (root_correct e (x ^ e) h)

def two : Peano := successor one

def Even (a : Peano) : Prop := Divisible a two

def Odd (a : Peano) : Prop := ¬ Even a

@[simp]
theorem toNat_multiply (a b : Peano) : (a * b).toNat = a.toNat * b.toNat := by
  induction b with
  | one =>
    rw [multiply_one]
    change a.toNat = a.toNat * 1
    rw [Nat.mul_one]
  | successor b ih =>
    rw [multiply_succ]
    rw [toNat_add]
    rw [ih]
    change a.toNat * b.toNat + a.toNat = a.toNat * (b.toNat + 1)
    rw [Nat.mul_add, Nat.mul_one]

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

theorem add_associative (a b c : Peano) : (a + b) + c = a + (b + c) := by
  induction c with
  | one =>
    rw [add_one, add_one, add_succ]
  | successor c ih =>
    rw [add_succ, add_succ, add_succ, ih]


theorem pred_succ_eq (x : Peano) : ∃ h, predecessor (successor x) h = x := by
  have h : successor x ≠ one := by
    intro h_eq
    exact Peano.noConfusion h_eq
  exact ⟨h, rfl⟩

theorem succ_pred_eq (x : Peano) (h : x ≠ one) : successor (predecessor x h) = x := by
  cases x with
  | one => exact False.elim (h rfl)
  | successor x' => rfl


theorem x_lt_succ_x (x : Peano) : x < x.successor := by
  induction x with
  | one => exact one_lt_succ one
  | successor x' ih => exact succ_lt_succ ih


theorem isDivisibleRecursive_correct (x a b : Peano) :
  isDivisibleRecursive x a b = true ↔ ∃ c, c ≤ x ∧ b * c = a := by
  induction x with
  | one =>
    unfold isDivisibleRecursive
    dsimp
    by_cases h : b * one = a
    · have h_pos : (if b * one = a then true else false) = true := if_pos h
      rw [h_pos]
      exact ⟨fun _ => ⟨one, Or.inr rfl, h⟩, fun _ => rfl⟩
    · have h_neg : (if b * one = a then true else false) = false := if_neg h
      rw [h_neg]
      apply Iff.intro
      · intro h_f
        contradiction
      · intro h_c
        rcases h_c with ⟨c, hc_le, hc_eq⟩
        cases hc_le with
        | inl hlt => exact False.elim (not_lt_one c hlt)
        | inr heq => rw [heq] at hc_eq; exact False.elim (h hc_eq)
  | successor x ih =>
    unfold isDivisibleRecursive
    by_cases h : b * successor x = a
    · have h_pos : (if b * successor x = a then true else isDivisibleRecursive x a b) = true := if_pos h
      rw [h_pos]
      exact ⟨fun _ => ⟨successor x, Or.inr rfl, h⟩, fun _ => rfl⟩
    · have h_neg : (if b * successor x = a then true else isDivisibleRecursive x a b) = isDivisibleRecursive x a b := if_neg h
      rw [h_neg]
      apply Iff.intro
      · intro h_ih
        have ⟨c, hc_le, hc_eq⟩ := ih.mp h_ih
        exists c
        have c_le_succ_x : c ≤ successor x := by
          cases hc_le with
          | inl hlt =>
            have h_x_lt_succ : x < successor x := x_lt_succ_x x
            exact Or.inl (lt_trans hlt h_x_lt_succ)
          | inr heq =>
            rw [heq]
            have h1 : x < one + x := lt_add_right one x
            have h2 : one + x = x + one := add_comm one x
            rw [h2] at h1
            have h3 : x + one = successor x := add_one x
            rw [← h3]
            exact Or.inl h1
        exact ⟨c_le_succ_x, hc_eq⟩
      · intro h_c
        rcases h_c with ⟨c, hc_le, hc_eq⟩
        have h_c_le_x : c ≤ x := by
          cases hc_le with
          | inl hlt => exact le_of_lt_succ hlt
          | inr heq => rw [heq] at hc_eq; exact False.elim (h hc_eq)
        exact ih.mpr ⟨c, h_c_le_x, hc_eq⟩

theorem isDivisibleCorrect (a b : Peano) : Divisible a b ↔ isDivisible a b := by
  unfold Divisible isDivisible
  apply Iff.intro
  · intro h
    rcases h with ⟨c, hc⟩
    have h_is_div : isDivisibleRecursive a a b = true := by
      rw [isDivisibleRecursive_correct]
      exists c
      have h_c_le_a : c ≤ a := by
        rw [← hc]
        exact le_multiply_right c b
      exact ⟨h_c_le_a, hc⟩
    exact h_is_div
  · intro h
    have h_is_div : isDivisibleRecursive a a b = true := h
    rw [isDivisibleRecursive_correct] at h_is_div
    rcases h_is_div with ⟨c, _, hc_eq⟩
    exact ⟨c, hc_eq⟩

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

end Peano

end ZeroMath.Numbers.OrdinalNatural
