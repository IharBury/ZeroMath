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
    · simp [multiply_succ, h3]
    · simp [multiply_succ, h3]
      have h3' : ¬b * successor x = a := by
        intro h_eq
        rw [multiply_succ] at h_eq
        exact h3 h_eq
      exact ih (divide_rec_step_h h h3')

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
    cases d <;> cases c <;> simp [divideWithRemainderAux]
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

theorem ordinal_isEven_iff_natMod (n : Peano) :
    Even n ↔ n.toNat % 2 = 0 := by
  rw [isEven_correct]
  induction n with
  | one =>
    simp [isEven]
    decide
  | successor n ih =>
    simp [isEven]
    have : ((successor n).toNat % 2 = 0) ↔ ¬ (n.toNat % 2 = 0) := by
      have : (successor n).toNat = n.toNat + 1 := rfl
      rw [this]
      omega
    rw [this, ← ih]
    simp

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

theorem subtract_succ_self (c : Peano) :
    subtract (successor c) c LessThan.base = one := by
  induction c with
  | one => rfl
  | successor c ih =>
    simp only [subtract]
    exact ih

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

theorem orig_some_q_mul (b : Peano) (hb : one < b) (q' c' : Peano)
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
    (if hone : one < b then A else B) = A := by
  by_cases hp : one < b
  · simp [hp]
  · exact absurd h hp

theorem if_lt_neg_named (b : Peano) (h : ¬ one < b) (A B : Peano) :
    (if hone : one < b then A else B) = B := by
  by_cases hp : one < b
  · exact absurd hp h
  · simp [hp]

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
                hsub, add_one, add_assoc]
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

theorem double_sub_one (b a : Peano) (hb : one < b) :
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
  have hcancel := double_sub_one b (successor a) hb
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
                              exact orig_some_q_mul b hone q' c' hlt'
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
            simp [succ_add, add_succ, add_comm]
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

def divideFast (a b : Peano) (h : Divisible a b) : Peano :=
  match hres : divideWithRemainder a b with
  | (some q, none) => q
  | (none, none) => False.elim (divideWithRemainder_not_none_none a b hres)
  | (none, some r) => False.elim (divideWithRemainder_none_some_divisible a b r h hres)
  | (some q, some r) => False.elim (divideWithRemainder_some_some_divisible a b q r h hres)

theorem divideFast_correct (a b : Peano) (h : Divisible a b) : b * divideFast a b h = a := by
  unfold divideFast
  split
  next q hres =>
    rw [divideWithRemainder_some_none a b q hres]
  next hres =>
    exact False.elim (divideWithRemainder_not_none_none a b hres)
  next r hres =>
    exact False.elim (divideWithRemainder_none_some_divisible a b r h hres)
  next q r hres =>
    exact False.elim (divideWithRemainder_some_some_divisible a b q r h hres)

theorem divideFast_multiply_eq (x y : Peano) : ∃ h, divideFast (y * x) y h = x := by
  let h : Divisible (y * x) y := ⟨x, rfl⟩
  refine ⟨h, ?_⟩
  exact multiply_cancel_left y (divideFast (y * x) y h) x (divideFast_correct (y * x) y h)

theorem divideFast_add (x y z : Peano) (h : Divisible x z) (h2 : Divisible y z) :
  ∃ h3, divideFast x z h + divideFast y z h2 = divideFast (x + y) z h3 := by
  let h3 : Divisible (x + y) z :=
    ⟨divideFast x z h + divideFast y z h2, by
      rw [multiply_add, divideFast_correct x z h, divideFast_correct y z h2]⟩
  refine ⟨h3, ?_⟩
  exact multiply_cancel_left z (divideFast x z h + divideFast y z h2) (divideFast (x + y) z h3) (by
    rw [multiply_add, divideFast_correct x z h, divideFast_correct y z h2, divideFast_correct (x + y) z h3])

theorem multiply_divideFast_assoc (x y z : Peano) (h : Divisible y z) :
  ∃ h2, x * divideFast y z h = divideFast (x * y) z h2 := by
  let h2 : Divisible (x * y) z := multiply_divide_assoc_h h
  refine ⟨h2, ?_⟩
  exact multiply_cancel_left z (x * divideFast y z h) (divideFast (x * y) z h2) (by
    rw [←multiply_assoc]
    have hzx : z * x = x * z := multiply_comm z x
    rw [hzx, multiply_assoc, divideFast_correct y z h, divideFast_correct (x * y) z h2])

theorem divideFast_lt_of_lt {x y z : Peano}
  (h1 : Divisible x z) (h2 : Divisible y z) (h3 : x > y) :
  divideFast y z h2 < divideFast x z h1 := by
  have hmul : z * divideFast y z h2 < z * divideFast x z h1 := by
    rw [divideFast_correct y z h2, divideFast_correct x z h1]
    exact h3
  have hmul' : divideFast y z h2 * z < divideFast x z h1 * z := by
    rw [multiply_comm (divideFast y z h2) z]
    rw [multiply_comm (divideFast x z h1) z]
    exact hmul
  exact lt_multiply_right_cancel hmul'

theorem divideFast_subtract_distrib {x y z : Peano}
  (h1 : Divisible x z) (h2 : Divisible y z) (h3 : x > y) :
  ∃ h4 h5, divideFast (subtract x y h3) z h4 = subtract (divideFast x z h1) (divideFast y z h2) h5 := by
  let qx : Peano := divideFast x z h1
  let qy : Peano := divideFast y z h2
  have h5 : qy < qx := divideFast_lt_of_lt h1 h2 h3
  have hmul_sub : ∃ hmul_lt, z * subtract qx qy h5 = subtract (z * qx) (z * qy) hmul_lt :=
    multiply_subtract z qx qy h5
  rcases hmul_sub with ⟨hmul_lt, hmul_sub_eq⟩
  have hsub_eq : z * subtract qx qy h5 = subtract x y h3 := by
    rw [hmul_sub_eq]
    exact subtract_eq_of_eq hmul_lt h3 (divideFast_correct x z h1) (divideFast_correct y z h2)
  let h4 : Divisible (subtract x y h3) z := ⟨subtract qx qy h5, hsub_eq⟩
  refine ⟨h4, h5, ?_⟩
  exact multiply_cancel_left z (divideFast (subtract x y h3) z h4) (subtract qx qy h5) (by
    rw [divideFast_correct (subtract x y h3) z h4, hsub_eq])

theorem divideFast_divideFast_eq_divideFast_multiply (x y z : Peano) (h1 : Divisible x (y * z)) :
  ∃ h2 h3, divideFast x (y * z) h1 = divideFast (divideFast x y h2) z h3 := by
  let h2 : Divisible x y := divide_divide_eq_divide_multiply_h2 h1
  let q : Peano := divideFast x (y * z) h1
  let r : Peano := divideFast x y h2
  have hzq_eq_r : z * q = r := by
    have hyzq_eq_yr : y * (z * q) = y * r := by
      rw [← multiply_assoc]
      rw [divideFast_correct x (y * z) h1]
      rw [divideFast_correct x y h2]
    exact multiply_cancel_left y (z * q) r hyzq_eq_yr
  let h3 : Divisible r z := ⟨q, hzq_eq_r⟩
  refine ⟨h2, h3, ?_⟩
  have hmul : z * q = z * divideFast r z h3 := by
    rw [hzq_eq_r]
    rw [divideFast_correct r z h3]
  exact multiply_cancel_left z q (divideFast r z h3) hmul

end Peano

end ZeroMath.Numbers.OrdinalNatural
