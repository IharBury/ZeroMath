import ZeroMath.Logic.Trichotomy
import ZeroMath.Numbers.OrdinalNatural.Peano

namespace ZeroMath.Numbers.CardinalNatural

inductive Peano where
  | zero : Peano
  | successor : Peano → Peano

deriving instance DecidableEq for Peano

namespace Peano

def one : Peano := successor zero
def two : Peano := successor one
def three : Peano := successor two
def four : Peano := successor three
def five : Peano := successor four
def six : Peano := successor five
def seven : Peano := successor six
def eight : Peano := successor seven
def nine : Peano := successor eight
def ten : Peano := successor nine

theorem successor_ne_zero (p : Peano) : successor p ≠ zero := by
  intro h
  cases h

theorem successor_injective : ∀ {p q : Peano}, successor p = successor q → p = q
  | _, _, rfl => rfl

def toNat : Peano → Nat
  | zero => 0
  | successor p => p.toNat.succ

def fromNat : Nat → Peano
  | 0 => zero
  | n + 1 => successor (fromNat n)

@[simp]
theorem fromNat_toNat (p : Peano) : fromNat (toNat p) = p := by
  induction p with
  | zero =>
    rfl
  | successor p ih =>
    simp [toNat, fromNat, ih]

@[simp]
theorem toNat_fromNat (n : Nat) : toNat (fromNat n) = n := by
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    simp [toNat, fromNat, ih]

@[simp]
theorem toNat_eq_zero_iff (p : Peano) : p.toNat = 0 ↔ p = zero := by
  cases p with
  | zero => simp [toNat]
  | successor p' => simp [toNat]

theorem toNat_ne_zero (p : Peano) (h : p ≠ zero) : p.toNat ≠ 0 := by
  intro hp
  exact h ((toNat_eq_zero_iff p).mp hp)

theorem eq_of_toNat_eq {a b : Peano} (h : a.toNat = b.toNat) : a = b := by
  calc a = fromNat (toNat a) := (fromNat_toNat a).symm
       _ = fromNat (toNat b) := by rw [h]
       _ = b := fromNat_toNat b

def toInt (n : Peano) : Int :=
  Int.ofNat n.toNat

def fromInt (n : Int) (_h : n ≥ 0) : Peano :=
  fromNat n.toNat

theorem fromInt_toInt (n : Peano) : ∃ h, fromInt (toInt n) h = n := by
  exact ⟨Int.natCast_nonneg n.toNat, by simp [fromInt, toInt, fromNat_toNat]⟩

@[simp]
theorem toInt_fromInt (x : Int) (h : x ≥ 0) : (fromInt x h).toInt = x := by
  simp [fromInt, toInt]
  simpa using Int.toNat_of_nonneg h

def predecessor (n : Peano) (h : n ≠ zero) : Peano :=
  match n with
  | zero => by contradiction
  | successor n' => n'

theorem predecessor_congr {a b : Peano}
  (ha : a ≠ zero) (hb : b ≠ zero)
  (h_eq : a = b) : a.predecessor ha = b.predecessor hb := by
  cases h_eq
  rfl

theorem predecessor_successor (x : Peano) : ∃ h, predecessor x.successor h = x :=
  ⟨successor_ne_zero x, rfl⟩

@[simp]
theorem successor_predecessor (x : Peano) (h : x ≠ zero) : successor (predecessor x h) = x := by
  cases x with
  | zero => contradiction
  | successor x' => rfl

def add (a : Peano) : Peano → Peano
  | zero => a
  | successor b' => successor (add a b')

instance : Add Peano where
  add := add

def multiply (a : Peano) : Peano → Peano
  | zero => zero
  | successor b' => multiply a b' + a

instance : Mul Peano where
  mul := multiply

theorem power.recursiveCondition (a b : Peano) : a.successor ≠ zero ∨ b ≠ zero :=
  Or.inl (successor_ne_zero a)

def power (a b : Peano) (h : a ≠ zero ∨ b ≠ zero) : Peano :=
  match a, b with
  | zero, zero => by contradiction
  | zero, successor _ => zero
  | successor a', zero => one
  | successor a', successor b' => power (successor a') b' (power.recursiveCondition a' b') * a

@[simp]
theorem add_zero (a : Peano) : a + zero = a := rfl

@[simp]
theorem zero_add (a : Peano) : zero + a = a := by
  induction a with
  | zero => rfl
  | successor a' ih => exact congrArg successor ih

@[simp]
theorem add_successor (a b : Peano) : a + b.successor = (a + b).successor := rfl

@[simp]
theorem successor_add (a b : Peano) : a.successor + b = (a + b).successor := by
  induction b with
  | zero => rfl
  | successor b' ih => exact congrArg successor ih

theorem add_one (a : Peano) : a + one = a.successor := by
  simp [one]

theorem one_add (a : Peano) : one + a = a.successor := by
  simp [one]

theorem add_associative (a b c : Peano) : (a + b) + c = a + (b + c) := by
  induction c with
  | zero => rfl
  | successor c' ih => exact congrArg successor ih

theorem add_commutative (a b : Peano) : a + b = b + a := by
  induction b with
  | zero =>
    show a + zero = zero + a
    rw [add_zero, zero_add]
  | successor b' ih =>
    show a + successor b' = successor b' + a
    rw [add_successor, ih, successor_add]

theorem multiply_zero (a : Peano) : a * zero = zero := rfl

@[simp]
theorem zero_multiply (a : Peano) : zero * a = zero := by
  induction a with
  | zero => rfl
  | successor a' ih =>
    show zero * a' + zero = zero
    rw [ih]
    rfl

theorem multiply_successor (a b : Peano) : a * b.successor = a * b + a := rfl

theorem successor_multiply (a b : Peano) : a.successor * b = a * b + b := by
  induction b with
  | zero => rfl
  | successor b' ih =>
    show (a.successor * b') + a.successor = a * b' + a + successor b'
    rw [ih]
    have h2 : b' + a.successor = a + b'.successor := by
      show successor (b' + a) = successor (a + b')
      rw [add_commutative]
    rw [add_associative, h2, add_associative]

theorem multiply_commutative (a b : Peano) : a * b = b * a := by
  induction b with
  | zero =>
    show a * zero = zero * a
    rw [multiply_zero, zero_multiply]
  | successor b' ih =>
    show a * b'.successor = b'.successor * a
    rw [multiply_successor, successor_multiply]
    show a * b' + a = b' * a + a
    rw [ih]

theorem multiply_distributive_over_add_right (a b c : Peano) : a * (b + c) = a * b + a * c := by
  induction c with
  | zero =>
    rfl
  | successor c' ih =>
    show a * (b + c'.successor) = a * b + a * c'.successor
    have h1 : b + c'.successor = successor (b + c') := rfl
    rw [h1]
    have h2 : a * successor (b + c') = a * (b + c') + a := rfl
    rw [h2, ih]
    have h3 : a * c'.successor = a * c' + a := rfl
    rw [h3, add_associative]

theorem multiply_distributive_over_add_left (a b c : Peano) : (a + b) * c = a * c + b * c := by
  rw [multiply_commutative (a + b), multiply_commutative a, multiply_commutative b, multiply_distributive_over_add_right]

theorem multiply_associative (a b c : Peano) : (a * b) * c = a * (b * c) := by
  induction c with
  | zero =>
    rfl
  | successor c' ih =>
    show multiply (multiply a b) (successor c') = multiply a (multiply b (successor c'))
    have h1 : multiply (multiply a b) (successor c') = add (multiply (multiply a b) c') (multiply a b) := rfl
    rw [h1]
    have h2 : multiply b (successor c') = add (multiply b c') b := rfl
    rw [h2]
    have h3 : multiply a (add (multiply b c') b) = add (multiply a (multiply b c')) (multiply a b) := multiply_distributive_over_add_right a (multiply b c') b
    rw [h3]
    have h4 : multiply (multiply a b) c' = multiply a (multiply b c') := ih
    rw [h4]

@[simp]
theorem add_toNat (a b : Peano) : toNat (a + b) = a.toNat + b.toNat := by
  induction b with
  | zero => rfl
  | successor b ih =>
    show toNat (successor (a + b)) = a.toNat + (b.toNat + 1)
    simp [toNat]
    rw [Nat.add_succ a.toNat, ih]

@[simp]
theorem multiply_toNat (a b : Peano) : toNat (a * b) = a.toNat * b.toNat := by
  induction b with
  | zero => rfl
  | successor b ih =>
    show (a * b + a).toNat = a.toNat * b.toNat + a.toNat
    rw [add_toNat, ih]

theorem add_right_cancel (b q c : Peano) (h : q + b = c + b) : q = c := by
  induction b with
  | zero => exact h
  | successor b' ih =>
    apply ih
    apply successor_injective
    exact h

theorem add_left_cancel (b q c : Peano) (h : b + q = b + c) : q = c := by
  rewrite [add_commutative b, add_commutative b] at h
  apply add_right_cancel b
  exact h

theorem add_successor_ne_zero (a b : Peano) : a + successor b ≠ zero := by
  intro h
  cases h

theorem multiply_right_cancel (b q c : Peano) (hb : b ≠ zero) (h : q * b = c * b) : q = c := by
  induction q generalizing c with
  | zero =>
    cases c with
    | zero => rfl
    | successor c' =>
      cases b with
      | zero => contradiction
      | successor b' =>
        rw [zero_multiply, successor_multiply] at h
        exact False.elim ((add_successor_ne_zero (c' * successor b') b') h.symm)
  | successor q' ih =>
    cases c with
    | zero =>
      cases b with
      | zero => contradiction
      | successor b' =>
        rw [successor_multiply, zero_multiply] at h
        exact False.elim ((add_successor_ne_zero (q' * successor b') b') h)
    | successor c' =>
      rw [successor_multiply, successor_multiply] at h
      have h' : q' * b = c' * b := add_right_cancel b (q' * b) (c' * b) h
      exact congrArg successor (ih c' h')

theorem multiply_left_cancel (b q c : Peano) (hb : b ≠ zero) (h : b * q = b * c) : q = c := by
  rewrite [multiply_commutative b, multiply_commutative b] at h
  exact multiply_right_cancel b _ _ hb h

theorem add_ne_zero_of_left_ne_zero (a b : Peano) (ha : a ≠ zero) : a + b ≠ zero := by
  intro h
  cases b with
  | zero => exact ha h
  | successor _ => cases h

theorem add_ne_zero_of_right_ne_zero (a b : Peano) (hb : b ≠ zero) : a + b ≠ zero := by
  intro h
  cases b with
  | zero => exact hb rfl
  | successor _ => cases h

theorem multiply_ne_zero (x y : Peano) (hx : x ≠ zero) (hy : y ≠ zero) : x * y ≠ zero := by
  intro hxy
  cases x with
  | zero => exact hx rfl
  | successor _ =>
    cases y with
    | zero => exact hy rfl
    | successor _ => cases hxy

@[simp]
theorem power_toNat (a b : Peano) (h : a ≠ zero ∨ b ≠ zero) : toNat (power a b h) = a.toNat ^ b.toNat := by
  induction b with
  | zero =>
    cases a with
    | zero => contradiction
    | successor a' =>
      simp [power, toNat]
      rfl
  | successor b' ih =>
    cases a with
    | zero => rfl
    | successor a' =>
      simp [power]
      show (power a'.successor b' _).toNat * a'.successor.toNat = (a'.successor).toNat ^ b'.toNat.succ
      rw [Nat.pow_succ]
      congr
      apply ih

@[simp]
theorem multiply_one (a : Peano) : a * one = a := by
  rw [one, multiply_successor, multiply_zero, zero_add]

@[simp]
theorem one_multiply (a : Peano) : one * a = a := by
  rw [one, successor_multiply, zero_multiply, zero_add]

theorem power_successor ( x z : Peano) (h : x ≠ zero ∨ z ≠ zero) :
  ∃ h2, power x z.successor h2 = power x z h * x := by
  cases x with
  | zero =>
    simp [power]
    rfl
  | successor x' =>
    have h2 : x'.successor ≠ zero ∨ z.successor ≠ zero := by
      right
      apply successor_ne_zero
    exists h2

theorem eq_rec_power (a b z : Peano) (heq : a = b) (h1 : a ≠ zero ∨ z ≠ zero) (h2 : b ≠ zero ∨ z ≠ zero) :
  power a z h1 = power b z h2 := by
  cases heq
  rfl

theorem eq_rec_power_exponent (a y z : Peano) (heq : y = z) (h1 : a ≠ zero ∨ y ≠ zero) (h2 : a ≠ zero ∨ z ≠ zero) :
  power a y h1 = power a z h2 := by
  cases heq
  rfl

theorem power_add (x y z : Peano) (h : x ≠ zero ∨ y ≠ zero) (h2 : x ≠ zero ∨ z ≠ zero) :
  ∃ h3, power x (y + z) h3 = power x y h * power x z h2 := by
  cases x with
  | zero =>
    cases z with
    | zero =>
      cases h2 with
      | inl hx => cases hx rfl
      | inr hz => cases hz rfl
    | successor z' =>
      cases y with
      | zero =>
        cases h with
        | inl hx => cases hx rfl
        | inr hy => cases hy rfl
      | successor y' =>
        have h3 : zero ≠ zero ∨ successor y' + successor z' ≠ zero := by
          right
          exact add_successor_ne_zero (successor y') z'
        exists h3
  | successor x' =>
    induction z with
    | zero =>
      have h3 : successor x' ≠ zero ∨ y + zero ≠ zero := Or.inl (successor_ne_zero x')
      exists h3
      change power (successor x') y h = power (successor x') y h * one
      rw [multiply_one]
    | successor z' ih =>
      have hz : successor x' ≠ zero ∨ z' ≠ zero := Or.inl (successor_ne_zero x')
      obtain ⟨h3, ih⟩ := ih hz
      have h4 : successor x' ≠ zero ∨ y + successor z' ≠ zero := Or.inr (add_successor_ne_zero y z')
      exists h4
      change
        power (successor x') (y + z') (power.recursiveCondition x' (y + z')) * successor x' =
          power (successor x') y h * (power (successor x') z' (power.recursiveCondition x' z') * successor x')
      have hleft : power (successor x') (y + z') (power.recursiveCondition x' (y + z')) = power (successor x') (y + z') h3 := by
        apply eq_rec_power
        rfl
      have hright : power (successor x') z' (power.recursiveCondition x' z') = power (successor x') z' hz := by
        apply eq_rec_power
        rfl
      rw [hleft, hright, ih, multiply_associative]

theorem power_multiply_dist (x y z : Peano) (h : x ≠ zero ∨ z ≠ zero) (h2 : y ≠ zero ∨ z ≠ zero) :
  ∃ h3, power (x * y) z h3 = power x z h * power y z h2 := by
  have h3 : x * y ≠ zero ∨ z ≠ zero := by
    cases z with
    | zero =>
      cases h with
      | inl hx =>
        cases h2 with
        | inl hy => exact Or.inl (multiply_ne_zero x y hx hy)
        | inr hz => cases hz rfl
      | inr hz => cases hz rfl
    | successor z' => exact Or.inr (successor_ne_zero z')
  exists h3
  revert x y h h2 h3
  induction z with
  | zero =>
    intro x y h h2 h3
    cases x with
    | zero => cases h <;> rename_i hz <;> cases hz rfl
    | successor x' =>
      cases y with
      | zero => cases h2 <;> rename_i hz <;> cases hz rfl
      | successor y' => rfl
  | successor z' ih =>
    intro x y h h2 h3
    cases x with
    | zero =>
      cases y with
      | zero => rfl
      | successor y' =>
        rw [eq_rec_power _ _ _ (zero_multiply _) _ (Or.inr (successor_ne_zero z'))]
        change zero = zero * _
        rw [zero_multiply]
    | successor x' =>
      cases y with
      | zero =>
        rw [eq_rec_power _ _ _ (multiply_zero _) _ (Or.inr (successor_ne_zero z'))]
        change zero = _ * zero
        rw [multiply_zero]
      | successor y' =>
        change power (successor x' * successor y') z' _ * (successor x' * successor y') =
          (power (successor x') z' _ * successor x') * (power (successor y') z' _ * successor y')
        rw [ih]
        rw [multiply_associative,
            ← multiply_associative (power (successor y') z' _),
            multiply_commutative (power (successor y') z' _) (successor x'),
            multiply_associative (successor x'),
            ← multiply_associative (power (successor x') z' _)]

@[simp]
theorem power_zero_eq_one x h : power x zero h = one := by
  cases x with
  | zero => contradiction
  | successor _ => rfl

@[simp]
theorem power_one_eq_self x h : power x one h = x := by
  cases x with
  | zero => rfl
  | successor x' =>
    simp [one, power]
    apply one_multiply

theorem zero_power_of_nonzero_exponent (e : Peano) (he : e ≠ zero) h : power zero e h = zero := by
  cases e with
  | zero => contradiction
  | successor _ => rfl

theorem power_ne_zero_of_base_ne_zero (x y : Peano) (h : x ≠ zero ∨ y ≠ zero) (hx : x ≠ zero) :
  power x y h ≠ zero := by
  cases x with
  | zero => contradiction
  | successor x' =>
    induction y with
    | zero =>
      rw [power_zero_eq_one]
      exact successor_ne_zero zero
    | successor y' ih =>
      change power x'.successor y' (power.recursiveCondition x' y') * x'.successor ≠ zero
      exact multiply_ne_zero _ _ (ih (power.recursiveCondition x' y')) (successor_ne_zero x')

theorem power_multiply (x y z : Peano) (h : x ≠ zero ∨ y ≠ zero) (h2 : power x y h ≠ zero ∨ z ≠ zero) :
  ∃ h3, power x (y * z) h3 = power (power x y h) z h2 := by
  cases x with
  | zero =>
    cases h with
    | inl hx => cases hx rfl
    | inr hy =>
      cases z with
      | zero =>
        cases h2 with
        | inl hp =>
          have hpzero : power zero y (Or.inr hy) = zero := zero_power_of_nonzero_exponent y hy _
          exact False.elim (hp hpzero)
        | inr hz => cases hz rfl
      | successor z' =>
        have hz : successor z' ≠ zero := successor_ne_zero z'
        have hyz : y * successor z' ≠ zero := multiply_ne_zero y (successor z') hy hz
        have h3 : zero ≠ zero ∨ y * successor z' ≠ zero := Or.inr hyz
        exists h3
        have hpzero : power zero y (Or.inr hy) = zero := zero_power_of_nonzero_exponent y hy _
        calc
          power zero (y * successor z') h3 = zero := zero_power_of_nonzero_exponent (y * successor z') hyz _
          _ = power (power zero y (Or.inr hy)) (successor z') h2 := by
            have hrewrite : power (power zero y (Or.inr hy)) (successor z') h2 = power zero (successor z') (Or.inr hz) :=
              eq_rec_power (power zero y (Or.inr hy)) zero (successor z') hpzero h2 (Or.inr hz)
            rw [hrewrite]
            rfl
  | successor x' =>
    have hx : successor x' ≠ zero := successor_ne_zero x'
    revert h2
    induction z with
    | zero =>
      intro h2
      have h3 : successor x' ≠ zero ∨ y * zero ≠ zero := Or.inl hx
      exists h3
      have hleft : power (successor x') (y * zero) h3 = power (successor x') zero (Or.inl hx) :=
        eq_rec_power_exponent (successor x') (y * zero) zero (multiply_zero y) h3 (Or.inl hx)
      rw [hleft]
      rw [power_zero_eq_one, power_zero_eq_one]
    | successor z' ih =>
      intro h2
      have hpow : power (successor x') y h ≠ zero := power_ne_zero_of_base_ne_zero (successor x') y h hx
      have h2prev : power (successor x') y h ≠ zero ∨ z' ≠ zero := Or.inl hpow
      obtain ⟨hih, ih_eq⟩ := ih h2prev
      obtain ⟨hadd, add_eq⟩ := power_add (successor x') (y * z') y hih h
      obtain ⟨hsucc, succ_eq⟩ := power_successor (power (successor x') y h) z' h2prev
      have h3 : successor x' ≠ zero ∨ y * successor z' ≠ zero := Or.inl hx
      exists h3
      calc
        power (successor x') (y * successor z') h3 = power (successor x') (y * z' + y) hadd := rfl
        _ = power (successor x') (y * z') hih * power (successor x') y h := add_eq
        _ = power (power (successor x') y h) z' h2prev * power (successor x') y h := by rw [ih_eq]
        _ = power (power (successor x') y h) (successor z') hsucc := succ_eq.symm
        _ = power (power (successor x') y h) (successor z') h2 := rfl

theorem product_is_zero_if_factor_is_zero x y (h2 : x * y = zero) : x = zero ∨ y = zero := by
  cases x <;> cases y <;> simp [zero_multiply, successor_multiply] at h2 ⊢

theorem power_is_zero_if_base_is_zero x e h (h2 : power x e h = zero) : x = zero := by
  cases x with
  | zero => rfl
  | successor x' =>
    induction e with
    | zero => contradiction
    | successor e' ih =>
      simp [power] at h2
      have h3 : power x'.successor e' (power.recursiveCondition x' e') = zero ∨ x'.successor = zero := product_is_zero_if_factor_is_zero _ _ h2
      cases h3 with
      | inl h_power_zero => exact ih _ h_power_zero
      | inr h_base_zero => exact h_base_zero

inductive LessThan (a : Peano) : Peano → Prop where
  | base : LessThan a a.successor
  | step {b : Peano} : LessThan a b → LessThan a b.successor

instance : LT Peano where
  lt := LessThan

/-- `Minimal n condition` means `n` is the least Peano number satisfying
`condition`. -/
def Minimal (n : Peano) (condition : Peano → Prop) : Prop :=
  condition n ∧ ∀ (m : Peano), m < n → ¬ condition m

/-- `Maximal n condition` means `n` is the greatest Peano number satisfying
`condition`. -/
def Maximal (n : Peano) (condition : Peano → Prop) : Prop :=
  condition n ∧ ∀ (m : Peano), n < m → ¬ condition m

theorem lt_trans {a b c : Peano} (hab : a < b) (hbc : b < c) : a < c := by
  induction hbc with
  | base => exact Peano.LessThan.step hab
  | step _ ih => exact Peano.LessThan.step ih

/-- Strict order is reflected by `toNat`. -/
theorem toNat_lt_of_lt {a b : Peano} (h : a < b) : a.toNat < b.toNat := by
  induction h with
  | base =>
    simp only [toNat]
    exact Nat.lt_succ_self _
  | step _ ih =>
    simp only [toNat]
    exact Nat.lt_succ_of_lt ih

def LessThanOrEqual (a b : Peano) : Prop :=
  a < b ∨ a = b

instance : LE Peano where
  le := LessThanOrEqual

def isLessThan : Peano → Peano → Bool
  | _, zero => false
  | zero, successor _ => true
  | successor a, successor b => isLessThan a b

theorem not_lt_zero (a : Peano) : ¬(a < zero) := by
  intro h
  generalize hz : zero = z at h
  induction h with
  | base => cases hz
  | step _ _ => cases hz

theorem lt_of_succ_lt {a b : Peano} (h : a.successor < b) : a < b :=
  lt_trans LessThan.base h

theorem lt_of_succ_lt_succ {a b : Peano} (h : a.successor < b.successor) : a < b := by
  generalize hz : b.successor = z at h
  induction h generalizing b with
  | base =>
    cases hz
    exact LessThan.base
  | step hlt _ =>
    cases hz
    exact lt_of_succ_lt hlt

theorem not_lt_self (a : Peano) : ¬(a < a) := by
  induction a with
  | zero => exact not_lt_zero zero
  | successor a' ih =>
    intro h
    exact ih (lt_of_succ_lt_succ h)

/-- Accessibility of Peano numbers under `<`, for well-founded induction. -/
theorem acc_lt (n : Peano) : Acc (fun a b : Peano => a < b) n := by
  induction n with
  | zero =>
    exact Acc.intro _ fun m hm => False.elim (not_lt_zero m hm)
  | successor n ih =>
    exact Acc.intro _ fun m hm => by
      cases hm with
      | base => exact ih
      | step hlt => exact Acc.inv ih hlt

/-- If any Peano number satisfies `condition`, then a least such number exists. -/
theorem exists_minimal (condition : Peano → Prop) (h : ∃ n, condition n) :
    ∃ m, Minimal m condition := by
  obtain ⟨n, hn⟩ := h
  revert hn
  induction acc_lt n with
  | intro n _ ih =>
    intro hn
    by_cases hmin : ∀ m, m < n → ¬ condition m
    · exact ⟨n, hn, hmin⟩
    · obtain ⟨m, hm⟩ := Classical.not_forall.mp hmin
      have hlt : m < n := by
        by_cases hlt : m < n
        · exact hlt
        · exact False.elim (hm fun hcontr => (hlt hcontr).elim)
      have hc : condition m := by
        by_cases hc : condition m
        · exact hc
        · exact False.elim (hm fun _ => hc)
      exact ih m hlt hc

theorem zero_lt_succ (x : Peano) : zero < x.successor := by
  induction x with
  | zero => exact LessThan.base
  | successor x' ih => exact LessThan.step ih

theorem predecessor_lt (b : Peano) (hb : b ≠ zero) : predecessor b hb < b := by
  cases b with
  | zero => contradiction
  | successor _ => exact LessThan.base

theorem succ_lt_succ {a b : Peano} (h : a < b) : a.successor < b.successor := by
  induction h with
  | base => exact LessThan.base
  | step _ ih => exact LessThan.step ih

theorem isLessThan_eq_true_iff_lt (a b : Peano) : Peano.isLessThan a b = true ↔ a < b := by
  revert a
  induction b using Peano.recOn with
  | zero =>
    intro a
    cases a with
    | zero =>
      simp [Peano.isLessThan]
      intro h; exact False.elim (not_lt_self _ h)
    | successor a =>
      simp [Peano.isLessThan]
      intro h; exact False.elim (not_lt_zero _ h)
  | successor b ih =>
    intro a
    cases a with
    | zero =>
      simp [Peano.isLessThan]
      exact zero_lt_succ b
    | successor a =>
      simp [Peano.isLessThan]
      rw [ih a]
      constructor
      · exact succ_lt_succ
      · exact lt_of_succ_lt_succ

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

theorem le_trans {a b c : Peano} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  cases hab with
  | inl hab_lt =>
    cases hbc with
    | inl hbc_lt => exact Or.inl (lt_trans hab_lt hbc_lt)
    | inr hbc_eq =>
      rw [← hbc_eq]
      exact Or.inl hab_lt
  | inr hab_eq =>
    rw [hab_eq]
    exact hbc

theorem not_succ_le_zero {a : Peano} (h : a.successor ≤ zero) : False := by
  cases h with
  | inl hlt =>
    generalize hz : zero = z at hlt
    induction hlt with
    | base => cases hz
    | step _ _ => cases hz
  | inr heq => cases heq

theorem succ_le_succ {a b : Peano} (h : a ≤ b) : a.successor ≤ b.successor := by
  cases h with
  | inl hlt => exact Or.inl (succ_lt_succ hlt)
  | inr heq =>
    have : a = b := heq
    rw [this]
    exact Or.inr rfl

theorem le_of_succ_le_succ {a b : Peano} (h : a.successor ≤ b.successor) : a ≤ b := by
  cases h with
  | inl hlt =>
    exact Or.inl (lt_of_succ_lt_succ hlt)
  | inr heq =>
    have : a = b := successor_injective heq
    exact Or.inr this

theorem le_of_succ_le {a b : Peano} (h : a.successor ≤ b) : a ≤ b := by
  cases h with
  | inl hlt =>
    exact Or.inl (lt_of_succ_lt hlt)
  | inr heq =>
    rw [←heq]
    left
    exact LessThan.base

theorem zero_le (x : Peano) : zero ≤ x := by
  cases x with
  | zero => exact Or.inr rfl
  | successor x' => exact Or.inl (zero_lt_succ x')

theorem successor_not_le_zero (x : Peano) : ¬(x.successor ≤ zero) := by
  intro h
  cases h with
  | inl hlt =>
    generalize hz : zero = z at hlt
    induction hlt with
    | base => cases hz
    | step _ _ => cases hz
  | inr heq => cases heq

theorem ne_of_lt {a b : Peano} (h : a < b) : a ≠ b := by
  rintro rfl
  exact not_lt_self a h

theorem not_lt_of_lt {a b : Peano} (h : a < b) : ¬(b < a) := fun hba =>
  not_lt_self a (lt_trans h hba)

theorem not_le_of_gt {a b : Peano} (h : b < a) : ¬ a ≤ b := by
  intro hle
  cases hle with
  | inl hlt => exact not_lt_of_lt h hlt
  | inr heq =>
    rw [heq] at h
    exact not_lt_self b h

theorem not_succ_le (a : Peano) : ¬ a.successor ≤ a := by
  intro h
  cases h with
  | inl hlt => exact not_lt_of_lt LessThan.base hlt
  | inr heq => exact (ne_of_lt LessThan.base) heq.symm


theorem trichotomy_or (x y : Peano) : x < y ∨ x = y ∨ y < x := by
  induction x generalizing y with
  | zero =>
    cases zero_le y with
    | inl h => exact Or.inl h
    | inr h => exact Or.inr (Or.inl h)
  | successor x ihx =>
    cases y with
    | zero =>
      exact Or.inr (Or.inr (zero_lt_succ x))
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

theorem lt_of_not_le {a b : Peano} (h : ¬ a ≤ b) : b < a := by
  cases trichotomy_or a b with
  | inl hlt =>
    exact False.elim (h (Or.inl hlt))
  | inr hrest =>
    cases hrest with
    | inl heq =>
      exact False.elim (h (Or.inr heq))
    | inr hgt =>
      exact hgt

/-- Result of comparing two Peano numbers, packaged with a proof of the relationship. -/
inductive Comparison (a b : Peano) where
  | less : a < b → Comparison a b
  | equal : a = b → Comparison a b
  | greater : b < a → Comparison a b

/-- Compare two Peano numbers, returning less, equal, or greater together with a proof. -/
def compare (a b : Peano) : Comparison a b :=
  match a, b with
  | zero, zero => Comparison.equal rfl
  | zero, successor b => Comparison.less (zero_lt_succ b)
  | successor a, zero => Comparison.greater (zero_lt_succ a)
  | successor a, successor b =>
    match compare a b with
    | Comparison.less h => Comparison.less (succ_lt_succ h)
    | Comparison.equal h => Comparison.equal (congrArg successor h)
    | Comparison.greater h => Comparison.greater (succ_lt_succ h)

theorem not_lt_implies_le {a b : Peano} (h : ¬ a < b) : b ≤ a := by
  cases trichotomy_or a b with
  | inl hlt => exact False.elim (h hlt)
  | inr htri =>
    cases htri with
    | inl heq => exact Or.inr heq.symm
    | inr hlt => exact Or.inl hlt

/-- `toNat` reflects strict order in the converse direction. -/
theorem lt_of_toNat_lt {a b : Peano} (h : a.toNat < b.toNat) : a < b := by
  cases trichotomy_or a b with
  | inl hlt => exact hlt
  | inr hrest =>
      cases hrest with
      | inl heq =>
          rw [heq] at h
          exact False.elim (Nat.lt_irrefl _ h)
      | inr hgt =>
          have hgt_nat := toNat_lt_of_lt hgt
          exact False.elim (Nat.lt_asymm h hgt_nat)

theorem toNat_le_of_le {a b : Peano} (h : a ≤ b) : a.toNat ≤ b.toNat := by
  cases h with
  | inl hlt => exact Nat.le_of_lt (toNat_lt_of_lt hlt)
  | inr heq => exact Nat.le_of_eq (congrArg toNat heq)

def subtract (a : Peano) : (b : Peano) → b ≤ a → Peano
  | zero, _ => a
  | successor b', h =>
    match a, h with
    | zero, h' => False.elim (not_succ_le_zero h')
    | successor a', h' => subtract a' b' (le_of_succ_le_succ h')

def subtractWithRemainder (a b : Peano) : Peano × Peano :=
  match a, b with
  | a, zero => ⟨a, zero⟩
  | zero, successor b' => ⟨zero, b'.successor⟩
  | successor a', successor b' => subtractWithRemainder a' b'

def trySubtract (a b : Peano) : Option Peano :=
  match a, b with
  | a, zero => a
  | zero, _ => none
  | successor a', successor b' => trySubtract a' b'

def divideWithRemainderAux (a b : Peano) (hb : b ≠ zero) (d : Peano) (c : Peano) (hc : c < b) : Peano × Peano :=
  match a, c with
  | zero, _ =>
    (zero, zero)
  | successor zero, zero =>
    (d.successor, zero)
  | successor (successor a), zero =>
    divideWithRemainderAux (successor a) b hb (d.successor) (predecessor b hb) (predecessor_lt b hb)
  | successor zero, successor c =>
    (d, subtract b (successor c) (Or.inl hc))
  | successor (successor a), successor c =>
    divideWithRemainderAux (successor a) b hb d c (lt_of_succ_lt hc)

def divideWithRemainder (a b : Peano) (hb : b ≠ zero) : Peano × Peano :=
  divideWithRemainderAux a b hb zero (predecessor b hb) (predecessor_lt b hb)

def isDivisible (a b : Peano) : Bool :=
  match b with
  | zero => false
  | successor b' =>
    match divideWithRemainder a b'.successor (successor_ne_zero b') with
    | (_, zero) => true
    | (_, successor _) => false

def tryDivide (a b : Peano) : Option Peano :=
  match b with
  | zero => none
  | successor b' =>
    match divideWithRemainder a b'.successor (successor_ne_zero b') with
    | (q, zero) => some q
    | (_, successor _) => none

theorem subtractWithRemainder_of_le (a b : Peano) (h : b ≤ a) :
    subtractWithRemainder a b = ⟨subtract a b h, zero⟩ := by
  induction b generalizing a with
  | zero => simp [subtractWithRemainder, subtract]
  | successor b' ih =>
    cases a with
    | zero => exact absurd h not_succ_le_zero
    | successor a' => exact ih a' (le_of_succ_le_succ h)

theorem subtractWithRemainder_of_lt (a b : Peano) (h : a ≤ b) :
    subtractWithRemainder a b = ⟨zero, subtract b a h⟩ := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => simp [subtractWithRemainder, subtract]
    | successor b' => simp [subtractWithRemainder, subtract]
  | successor a' ih =>
    cases b with
    | zero => exact absurd h not_succ_le_zero
    | successor b' => exact ih b' (le_of_succ_le_succ h)

theorem subtractWithRemainderCorrect (a b : Peano) :
    (a < b ∧ ∃ h, subtractWithRemainder a b = ⟨zero, subtract b a h⟩) ∨
    (a ≥ b ∧ ∃ h, subtractWithRemainder a b = ⟨subtract a b h, zero⟩) := by
  cases trichotomy_or a b with
  | inl h_lt =>
    exact Or.inl ⟨h_lt, Or.inl h_lt, subtractWithRemainder_of_lt a b (Or.inl h_lt)⟩
  | inr h =>
    cases h with
    | inl h_eq =>
      subst h_eq
      exact Or.inr ⟨Or.inr rfl, Or.inr rfl, subtractWithRemainder_of_le a a (Or.inr rfl)⟩
    | inr h_gt =>
      exact Or.inr ⟨Or.inl h_gt, Or.inl h_gt, subtractWithRemainder_of_le a b (Or.inl h_gt)⟩

theorem successor_subtract (a b : Peano) (h : b ≤ a) : ∃ h2, (subtract a b h).successor = subtract a.successor b h2 := by
  induction b generalizing a with
  | zero =>
    exists zero_le a.successor
    simp [subtract]
  | successor b' ih =>
    cases a with
    | zero =>
      have := successor_not_le_zero b'
      contradiction
    | successor a' =>
      simp [subtract]
      have h2 := le_of_succ_le_succ h
      let ⟨h3, ih⟩ := ih a' h2
      exists succ_le_succ h3

@[simp]
theorem subtract_self_zero (a : Peano) (h : a ≤ a) : subtract a a h = zero := by
  induction a with
  | zero => rfl
  | successor a ih =>
    unfold subtract
    exact ih _

theorem subtract_eq_zero_of_eq {a b : Peano} (h_le : b ≤ a) (h_eq : a = b) :
  subtract a b h_le = zero := by
  cases h_eq
  exact subtract_self_zero a h_le

theorem subtract_add_cancel (a b : Peano) (h : b ≤ a) : subtract a b h + b = a := by
  induction b generalizing a with
  | zero => simp [subtract, add_zero]
  | successor b' ih =>
    let ⟨h2, h3⟩ := successor_subtract a b'.successor h
    simp [add_successor]
    rw [add_commutative, ←add_successor, h3, add_commutative]
    apply ih

theorem zero_lt_of_ne_zero (b : Peano) (hb : b ≠ zero) : zero < b := by
  cases b with
  | zero => contradiction
  | successor b' => exact zero_lt_succ b'

theorem le_pred_of_lt (b : Peano) (hb : b ≠ zero) (c : Peano) (hc : c < b) :
    c ≤ predecessor b hb := by
  cases b with
  | zero => contradiction
  | successor b' =>
    cases hc with
    | base =>
      exact Or.inr rfl
    | step hlt =>
      exact Or.inl hlt

theorem lt_of_lt_pred (b : Peano) (hb : b ≠ zero) {c : Peano} (h : c < predecessor b hb) : c < b :=
  lt_trans h (predecessor_lt b hb)

theorem le_of_lt_or_eq_pred (b : Peano) (hb : b ≠ zero) (c : Peano) (hc : c < b) :
    c ≤ b := by
  cases le_pred_of_lt b hb c hc with
  | inl hlt => exact Or.inl (lt_trans hlt (predecessor_lt b hb))
  | inr heq =>
    rw [heq]
    exact Or.inl (predecessor_lt b hb)

theorem pred_add_one (b : Peano) (hb : b ≠ zero) : predecessor b hb + one = b := by
  cases b with
  | zero => contradiction
  | successor b' => simp [predecessor, one]

theorem subtract_pred_succ (b : Peano) (hb : b ≠ zero) (c : Peano)
    (hlt : successor c < predecessor b hb) :
    subtract (predecessor b hb) c
        (le_pred_of_lt b hb c (lt_of_lt_pred b hb (lt_of_succ_lt hlt))) =
      one + subtract (predecessor b hb) (successor c) (Or.inl hlt) := by
  have hle := le_pred_of_lt b hb c (lt_of_lt_pred b hb (lt_of_succ_lt hlt))
  have h1 := subtract_add_cancel (predecessor b hb) c hle
  have h2 := subtract_add_cancel (predecessor b hb) (successor c) (Or.inl hlt)
  apply add_right_cancel (successor c)
  calc subtract (predecessor b hb) c hle + successor c
      _ = (subtract (predecessor b hb) c hle + c) + one := by rw [← add_one c, ← add_associative]
      _ = predecessor b hb + one := by rw [h1]
      _ = one + predecessor b hb := by rw [add_commutative]
      _ = one + (subtract (predecessor b hb) (successor c) (Or.inl hlt) + successor c) := by
            exact congrArg (fun x => one + x) h2.symm
      _ = one + subtract (predecessor b hb) (successor c) (Or.inl hlt) + successor c := by rw [add_associative]

theorem subtract_succ_pred (b : Peano) (hb : b ≠ zero) (c : Peano) (hc : c < b) :
    subtract b c (le_of_lt_or_eq_pred b hb c hc) =
      (subtract (predecessor b hb) c (le_pred_of_lt b hb c hc)).successor := by
  induction c generalizing b hb with
  | zero =>
    cases b with
    | zero => contradiction
    | successor b' => simp [subtract, predecessor]
  | successor c ih =>
    cases b with
    | zero => contradiction
    | successor b' =>
      cases b' with
      | zero => exact absurd hc (fun h => not_lt_zero c (lt_of_succ_lt_succ h))
      | successor b'' =>
        simp only [subtract, predecessor]
        have hc' := lt_of_succ_lt_succ hc
        exact ih (successor b'') (successor_ne_zero b'') hc'

theorem lt_add_of_pos_right (a b : Peano) (hb : zero < b) : a < a + b := by
  cases hb with
  | base => exact LessThan.base
  | step h => exact LessThan.step (lt_add_of_pos_right a _ h)

theorem lt_of_lt_add_right_eq {a b c : Peano} (hlt : a < a + c) (heq : a + c = b) : a < b := by
  rw [← heq]
  exact hlt

theorem subtract_lt_of_succ_lt {b c : Peano} (h : successor c < b) :
    subtract b (successor c) (Or.inl h) < b := by
  have hle : successor c ≤ b := Or.inl h
  have h_cancel := subtract_add_cancel b (successor c) hle
  exact lt_of_lt_add_right_eq
    (lt_add_of_pos_right (subtract b (successor c) hle) (successor c) (zero_lt_succ c)) h_cancel

theorem subtract_ne_zero_of_succ_lt (b c : Peano) (hlt : successor c < b) :
    subtract b (successor c) (Or.inl hlt) ≠ zero := by
  intro hzero
  have h_cancel := subtract_add_cancel b (successor c) (Or.inl hlt)
  have hb_eq : b = successor c := by
    calc b = subtract b (successor c) (Or.inl hlt) + successor c := h_cancel.symm
         _ = zero + successor c := by rw [hzero]
         _ = successor c := zero_add (successor c)
  exact ne_of_lt hlt hb_eq.symm

def divideWithRemainderOrigAux (a b : Peano) (hb : b ≠ zero) (d c : Peano) (hc : c < b) : Peano :=
  a + d * b + subtract (predecessor b hb) c (le_pred_of_lt b hb c hc)

theorem divideWithRemainderOrigAux_top (a b : Peano) (hb : b ≠ zero) :
    divideWithRemainderOrigAux a b hb zero (predecessor b hb) (predecessor_lt b hb) = a := by
  simp [divideWithRemainderOrigAux, add_zero]

theorem lt_of_lt_pred_succ (b : Peano) (hb : b ≠ zero) (c : Peano)
    (hlt : successor c < predecessor b hb) : successor c < b := by
  rw [← successor_predecessor b hb]
  exact LessThan.step hlt

theorem divideWithRemainderOrigAux_step_succ (a b : Peano) (hb : b ≠ zero) (d c : Peano)
    (hc : successor c < b) (hlt : successor c < predecessor b hb) :
    divideWithRemainderOrigAux (successor (successor a)) b hb d (successor c) hc =
      divideWithRemainderOrigAux (successor a) b hb d c (lt_of_succ_lt hc) := by
  unfold divideWithRemainderOrigAux
  calc successor (successor a) + d * b + subtract (predecessor b hb) (successor c) (le_pred_of_lt b hb (successor c) hc)
      _ = successor a + one + d * b + subtract (predecessor b hb) (successor c) (le_pred_of_lt b hb (successor c) hc) := by
            rw [← add_one (successor a)]
      _ = successor a + (one + d * b + subtract (predecessor b hb) (successor c) (Or.inl hlt)) := by
            rw [← add_associative, ← add_associative]
      _ = successor a + (d * b + (one + subtract (predecessor b hb) (successor c) (Or.inl hlt))) := by
            rw [add_commutative one (d * b), add_associative]
      _ = successor a + d * b + subtract (predecessor b hb) c (le_pred_of_lt b hb c (lt_of_succ_lt hc)) := by
            rw [← add_associative, ← subtract_pred_succ b hb c hlt]

theorem add_assoc4 (a b c d : Peano) : a + b + c + d = a + (b + c + d) := by
  rw [← add_associative, ← add_associative]

theorem add_one_comm_right (a b : Peano) : a + one + b = a + b + one := by
  calc a + one + b
      _ = (a + one) + b := rfl
      _ = a + (one + b) := add_associative a one b
      _ = a + (b + one) := by rw [add_commutative one b]
      _ = (a + b) + one := add_associative a b one
      _ = a + b + one := rfl

theorem add_perm_xy (a x y z : Peano) : a + x + y + z = a + y + x + z := by
  calc a + x + y + z
      _ = (a + x + y) + z := rfl
      _ = (a + (x + y)) + z := by rw [← add_associative]
      _ = (a + (y + x)) + z := by rw [add_commutative x y]
      _ = (a + y + x) + z := by rw [← add_associative]
      _ = a + y + x + z := rfl

theorem add_succ_eq_add_one (a b : Peano) : a + b.successor = a + b + one := by
  rw [← add_one b, ← add_associative]

theorem subtract_one (c : Peano) : subtract (successor c) c (Or.inl LessThan.base) = one := by
  induction c with
  | zero => rfl
  | successor c ih =>
    simp [subtract]
    exact ih

theorem divideWithRemainderOrigAux_step_succ_base (a c : Peano) (hb : successor (successor c) ≠ zero) (d : Peano)
    (hc : successor c < successor (successor c)) :
    divideWithRemainderOrigAux (successor (successor a)) (successor (successor c)) hb d (successor c) hc =
      divideWithRemainderOrigAux (successor a) (successor (successor c)) hb d c (lt_of_succ_lt hc) := by
  cases hc with
  | base =>
    calc divideWithRemainderOrigAux (successor (successor a)) (successor (successor c)) hb d (successor c)
            LessThan.base
        _ = successor (successor a) + d * successor (successor c) := by
              unfold divideWithRemainderOrigAux
              simp only [predecessor, subtract_self_zero (successor c) (Or.inr rfl), add_zero]
        _ = successor a + d * successor (successor c) + one :=
              add_one_comm_right (successor a) (d * successor (successor c))
        _ = divideWithRemainderOrigAux (successor a) (successor (successor c)) hb d c
              (lt_of_succ_lt LessThan.base) := by
              unfold divideWithRemainderOrigAux
              simp only [predecessor, subtract_one]
  | step hlt =>
    exact absurd hlt (not_lt_self (successor c))

theorem add_group_tail (d b' : Peano) :
    (one + (d * b' + d) + b') + d + one = (one + (d * b' + d) + b') + (d + one) :=
  add_associative (one + (d * b' + d) + b') d one

theorem one_add_mul_perm (d b' : Peano) :
    one + ((d * b' + d) + d) + b' + one = (one + (d * b' + d) + b') + d + one := by
  calc one + ((d * b' + d) + d) + b' + one
      _ = (one + (d * b' + d) + d) + b' + one := by rw [← add_associative]
      _ = (one + (d * b' + d) + b') + d + one := add_perm_xy (one + (d * b' + d)) d b' one

theorem one_add_mul_succ (d b' : Peano) :
    one + (d * b' + d) + b' = (d + one) * (successor b') := by
  induction b' with
  | zero =>
    simp [one, multiply_zero, zero_add, add_zero, multiply_successor]
  | successor b' ih =>
    calc one + (d * b'.successor + d) + b'.successor
        _ = one + (d * b' + d + d) + b'.successor := by rw [multiply_successor d b']
        _ = (one + (d * b' + d + d)) + b'.successor := rfl
        _ = (one + (d * b' + d + d)) + b' + one := by rw [add_succ_eq_add_one (one + (d * b' + d + d)) b']
        _ = one + (d * b' + d + d) + b' + one := rfl
        _ = one + ((d * b' + d) + d) + b' + one := by rw [← add_associative]
        _ = (one + (d * b' + d) + b') + d + one := one_add_mul_perm d b'
        _ = (one + (d * b' + d) + b') + (d + one) := add_group_tail d b'
        _ = (d + one) * b'.successor + (d + one) := congrArg (fun x => x + (d + one)) ih
        _ = (d + one) * b'.successor.successor := by rw [← multiply_successor (d + one) b'.successor]

theorem divideWithRemainderOrigAux_step_zero (a b : Peano) (hb : b ≠ zero) (d : Peano) :
    divideWithRemainderOrigAux (successor (successor a)) b hb d zero (zero_lt_of_ne_zero b hb) =
      divideWithRemainderOrigAux (successor a) b hb (d + one) (predecessor b hb) (predecessor_lt b hb) := by
  cases b with
  | zero => contradiction
  | successor b' =>
    unfold divideWithRemainderOrigAux
    simp only [subtract, predecessor]
    have hsum := one_add_mul_succ d b'
    calc successor (successor a) + d * (successor b') + b'
        _ = successor a + (one + (d * b' + d) + b') := by
              rw [← add_one (successor a), multiply_successor, add_assoc4]
        _ = successor a + (d + one) * (successor b') := by rw [hsum]
        _ = successor a + (d + one) * (successor b') + subtract b' b' (Or.inr rfl) := by
              rw [subtract_self_zero, add_zero]

theorem divideWithRemainderOrigAux_result_zero (b : Peano) (hb : b ≠ zero) (d : Peano) :
    divideWithRemainderOrigAux one b hb d zero (zero_lt_of_ne_zero b hb) = b * (d + one) := by
  cases b with
  | zero => contradiction
  | successor b' =>
    unfold divideWithRemainderOrigAux one
    simp only [subtract, predecessor]
    calc one + d * (successor b') + b'
        _ = one + (d * b' + d) + b' := by rw [multiply_successor, ← add_associative]
        _ = (d + one) * (successor b') := one_add_mul_succ d b'
        _ = (successor b') * (d + one) := multiply_commutative (d + one) (successor b')

theorem divideWithRemainderOrigAux_result_succ (b : Peano) (hb : b ≠ zero) (d c : Peano)
    (hc : successor c < b) :
    divideWithRemainderOrigAux one b hb d (successor c) hc =
      b * d + subtract b (successor c) (Or.inl hc) := by
  have hsub := subtract_succ_pred b hb (successor c) hc
  unfold divideWithRemainderOrigAux one
  let sub := subtract (predecessor b hb) (successor c) (le_pred_of_lt b hb (successor c) hc)
  calc one + d * b + sub
      _ = one + (d * b + sub) := by rw [← add_associative]
      _ = one + (sub + d * b) := by rw [add_commutative (d * b) sub]
      _ = one + sub + d * b := by rw [← add_associative]
      _ = sub.successor + d * b := by rw [← one_add, add_commutative]
      _ = subtract b (successor c) (Or.inl hc) + d * b := by rw [hsub]
      _ = b * d + subtract b (successor c) (Or.inl hc) := by
            rw [add_commutative (b * d), multiply_commutative]

theorem divideWithRemainderOrigAux_succ_succ_base (a' c' d : Peano) :
    divideWithRemainderOrigAux (successor (successor a')) (successor (successor c'))
        (successor_ne_zero (successor c')) d (successor c') LessThan.base =
      divideWithRemainderOrigAux (successor a') (successor (successor c'))
        (successor_ne_zero (successor c')) d c' (lt_of_succ_lt LessThan.base) :=
  divideWithRemainderOrigAux_step_succ_base a' c' (successor_ne_zero (successor c')) d LessThan.base

theorem divideWithRemainderOrigAux_succ_succ_any (a' c' d : Peano)
    (hc : successor c' < successor (successor c')) :
    divideWithRemainderOrigAux (successor (successor a')) (successor (successor c'))
        (successor_ne_zero (successor c')) d (successor c') hc =
      divideWithRemainderOrigAux (successor a') (successor (successor c'))
        (successor_ne_zero (successor c')) d c' (lt_of_succ_lt hc) := by
  cases hc with
  | base => exact divideWithRemainderOrigAux_succ_succ_base a' c' d
  | step hlt => exact absurd hlt (not_lt_self (successor c'))

theorem divideWithRemainderOrigAux_succ_succ_step (a' c' d : Peano) (b : Peano) (hb : b ≠ zero)
    (hlt : successor c' < predecessor b hb) :
    divideWithRemainderOrigAux (successor (successor a')) b hb d (successor c')
        (lt_of_lt_pred_succ b hb c' hlt) =
      divideWithRemainderOrigAux (successor a') b hb d c'
        (lt_of_succ_lt (lt_of_lt_pred_succ b hb c' hlt)) :=
  divideWithRemainderOrigAux_step_succ a' b hb d c' (lt_of_lt_pred_succ b hb c' hlt) hlt

theorem divideWithRemainderAux_remainder_lt_b (a b : Peano) (hb : b ≠ zero) (d c : Peano)
    (hc : c < b) (q r : Peano)
    (h : divideWithRemainderAux a b hb d c hc = (q, r)) : r < b := by
  induction a generalizing b d c hc q r with
  | zero =>
    unfold divideWithRemainderAux at h
    rcases h with ⟨rfl, rfl⟩
    exact zero_lt_of_ne_zero b hb
  | successor a ih =>
    unfold divideWithRemainderAux at h
    cases a with
    | zero =>
      cases c with
      | zero =>
        rcases h with ⟨rfl, rfl⟩
        exact zero_lt_of_ne_zero b hb
      | successor c' =>
        have hr : subtract b (successor c') (Or.inl hc) = r := congrArg Prod.snd h
        rw [← hr]
        exact subtract_lt_of_succ_lt hc
    | successor a' =>
      cases c with
      | zero =>
        exact ih b hb (d.successor) (predecessor b hb) (predecessor_lt b hb) q r h
      | successor c' =>
        exact ih b hb d c' (lt_of_succ_lt hc) q r h

theorem divideWithRemainderAux_zero_implies_a_zero (a b : Peano) (hb : b ≠ zero) (d c : Peano)
    (hc : c < b) (h : divideWithRemainderAux a b hb d c hc = (zero, zero)) : a = zero := by
  induction a generalizing b d c hc with
  | zero => rfl
  | successor a ih =>
    unfold divideWithRemainderAux at h
    cases a with
    | zero =>
      cases c with
      | zero =>
        cases h
      | successor c' =>
        have hr : subtract b (successor c') (Or.inl hc) = zero := congrArg Prod.snd h
        exact (subtract_ne_zero_of_succ_lt b c' hc hr).elim
    | successor a' =>
      cases c with
      | zero =>
        have h' := ih b hb (d.successor) (predecessor b hb) (predecessor_lt b hb) h
        exact absurd h' (successor_ne_zero a')
      | successor c' =>
        have h' := ih b hb d c' (lt_of_succ_lt hc) h
        exact absurd h' (successor_ne_zero a')

theorem divideWithRemainderAux_preserves_orig (a b : Peano) (hb : b ≠ zero) (d c : Peano)
    (hc : c < b) (q r : Peano)
    (h : divideWithRemainderAux a b hb d c hc = (q, r))
    (hd : a = zero → d = zero)
    (hc0 : a = zero → c = predecessor b hb) :
    divideWithRemainderOrigAux a b hb d c hc = b * q + r := by
  revert h hd hc0
  induction a generalizing b d c hc q r with
  | zero =>
    intro h hd hc0
    have hd0 := hd rfl
    subst hd0
    have hc0' := hc0 rfl
    subst hc0'
    rcases h with ⟨rfl, rfl⟩
    simp [divideWithRemainderOrigAux, multiply_zero]
  | successor a ih =>
    intro h hd hc0
    unfold divideWithRemainderAux at h
    cases a with
    | zero =>
      cases c with
      | zero =>
        replace hf := congrArg Prod.fst h
        replace hs := congrArg Prod.snd h
        subst hf hs
        simpa [one] using divideWithRemainderOrigAux_result_zero b hb d
      | successor c' =>
        replace hf := congrArg Prod.fst h
        replace hs := congrArg Prod.snd h
        subst hf hs
        simpa [one] using divideWithRemainderOrigAux_result_succ b hb d c' hc
    | successor a' =>
      have hd' : successor a' = zero → d.successor = zero := fun h' =>
        absurd h' (successor_ne_zero a')
      cases c with
      | zero =>
        have h' := ih b hb (d.successor) (predecessor b hb) (predecessor_lt b hb) q r h
          (fun h' => absurd h' (successor_ne_zero a')) (fun _ => rfl)
        exact (divideWithRemainderOrigAux_step_zero a' b hb d).trans h'
      | successor c' =>
        cases hc with
        | base =>
          have hrec := ih (successor (successor c')) (successor_ne_zero (successor c')) d c'
              (lt_of_succ_lt LessThan.base) q r h
            (fun h' => absurd h' (successor_ne_zero a'))
            (fun h' => absurd h' (successor_ne_zero a'))
          exact (divideWithRemainderOrigAux_succ_succ_any a' c' d LessThan.base).trans hrec
        | @step b₀ hlt =>
          have hb₀ := successor_ne_zero b₀
          have hrec := ih (successor b₀) hb₀ d c' (lt_of_succ_lt (lt_of_lt_pred_succ (successor b₀) hb₀ c' hlt)) q r h
            (fun h' => absurd h' (successor_ne_zero a'))
            (fun h' => absurd h' (successor_ne_zero a'))
          exact (divideWithRemainderOrigAux_succ_succ_step a' c' d (successor b₀) hb₀ hlt).trans hrec

theorem divideWithRemainder_zero (a b : Peano) (hb : b ≠ zero)
    (h : divideWithRemainder a b hb = (zero, zero)) : a = zero := by
  rw [divideWithRemainder] at h
  exact divideWithRemainderAux_zero_implies_a_zero a b hb zero (predecessor b hb)
    (predecessor_lt b hb) h

theorem divideWithRemainder_remainder_lt_b (a b : Peano) (hb : b ≠ zero) (q r : Peano)
    (h : divideWithRemainder a b hb = (q, r)) : r < b := by
  rw [divideWithRemainder] at h
  exact divideWithRemainderAux_remainder_lt_b a b hb zero (predecessor b hb)
    (predecessor_lt b hb) q r h

theorem divideWithRemainder_correct (a b : Peano) (hb : b ≠ zero) (q r : Peano)
    (h : divideWithRemainder a b hb = (q, r)) : a = b * q + r := by
  have hspec := divideWithRemainderAux_preserves_orig a b hb zero (predecessor b hb)
    (predecessor_lt b hb) q r (by rw [divideWithRemainder] at h; exact h) (fun hzero => rfl)
    (fun hzero => by subst hzero; rfl)
  simpa [divideWithRemainderOrigAux_top] using hspec

theorem le_add_self_left (a b : Peano) : a ≤ a + b := by
  have h_add_def : a + b = add a b := rfl
  rw [h_add_def]
  clear h_add_def
  induction b with
  | zero => exact Or.inr rfl
  | successor b' ih =>
    cases ih with
    | inl h_lt => exact Or.inl (lt_trans h_lt LessThan.base)
    | inr h_eq =>
      have h1 : add a b' < successor (add a b') := LessThan.base
      have h_goal : a < successor (add a b') := by
        calc a = add a b' := h_eq
             _ < successor (add a b') := h1
      exact Or.inl h_goal

theorem le_add_self_right (a b : Peano) : b ≤ a + b := by
  have h1 : a + b = b + a := add_commutative a b
  rw [h1]
  exact le_add_self_left b a

theorem add_cancel_right (a b c : Peano) (h : a + c = b + c) : a = b := by
  have h1 : a + c = add a c := rfl
  have h2 : b + c = add b c := rfl
  rw [h1, h2] at h
  clear h1 h2
  induction c with
  | zero =>
    have h1 : add a zero = a := rfl
    have h2 : add b zero = b := rfl
    rw [← h1, ← h2]
    exact h
  | successor c' ih =>
    have h1 : add a (successor c') = successor (add a c') := rfl
    have h2 : add b (successor c') = successor (add b c') := rfl
    rw [h1, h2] at h
    exact ih (successor_injective h)

theorem add_subtract_cancel (a b : Peano) : ∃ h, subtract (a + b) b h = a := by
  have h_le : b ≤ a + b := le_add_self_right a b
  have h_cancel_add : add (subtract (a + b) b h_le) b = add a b := by
    have h1 : subtract (a + b) b h_le + b = a + b := subtract_add_cancel (a + b) b h_le
    have h2 : subtract (a + b) b h_le + b = add (subtract (a + b) b h_le) b := rfl
    have h3 : a + b = add a b := rfl
    rw [h2] at h1
    calc add (subtract (a + b) b h_le) b = a + b := h1
         _ = add a b := h3
  exact ⟨h_le, add_cancel_right (subtract (a + b) b h_le) a b h_cancel_add⟩

theorem add_subtract_assoc (a b c : Peano) (h : b ≥ c) : ∃ h2, subtract (a + b) c h2 = a + subtract b c h := by
  have h2 : c ≤ a + b := le_trans h (le_add_self_right a b)
  have h3 : subtract (a + b) c h2 + c = (a + subtract b c h) + c := by
    rw [subtract_add_cancel (a + b) c h2, add_associative a (subtract b c h) c, subtract_add_cancel b c h]
  have h_cancel_right : add (subtract (a + b) c h2) c = add (a + subtract b c h) c := by
    have h_left : subtract (a + b) c h2 + c = add (subtract (a + b) c h2) c := rfl
    have h_right : (a + subtract b c h) + c = add (a + subtract b c h) c := rfl
    rw [← h_left, ← h_right]
    exact h3
  exact ⟨h2, add_cancel_right (subtract (a + b) c h2) (a + subtract b c h) c h_cancel_right⟩

theorem subtract_subtract_assoc (x y z : Peano) (h : y ≤ x) (h2 : z ≤ subtract x y h) :
    ∃ h3, subtract (subtract x y h) z h2 = subtract x (y + z) h3 := by
  let yz := y + z
  let left := subtract (subtract x y h) z h2
  have h_left_add_z : left + z = subtract x y h := by
    exact subtract_add_cancel (subtract x y h) z h2
  have h_subtract_add_y : subtract x y h + y = x := by
    exact subtract_add_cancel x y h
  have h_left_add_yz : left + yz = x := by
    change left + (y + z) = x
    rw [add_commutative y z]
    rw [← add_associative left z y]
    rw [h_left_add_z]
    exact h_subtract_add_y
  have h3 : yz ≤ x := by
    rw [← h_left_add_yz]
    exact le_add_self_right left yz
  have h_cancel : left + yz = subtract x yz h3 + yz := by
    rw [h_left_add_yz, subtract_add_cancel x yz h3]
  exact ⟨h3, add_cancel_right left (subtract x yz h3) yz h_cancel⟩

theorem multiply_subtract (x y z : Peano) (h : z ≤ y) :
    ∃ h2, x * subtract y z h = subtract (x * y) (x * z) h2 := by
  let d := subtract y z h
  have h_y : d + z = y := by
    exact subtract_add_cancel y z h
  have h_mul_y : x * d + x * z = x * y := by
    have h_mul_add : x * (d + z) = x * d + x * z := multiply_distributive_over_add_right x d z
    calc x * d + x * z = x * (d + z) := h_mul_add.symm
         _ = x * y := by rw [h_y]
  have h2 : x * z ≤ x * y := by
    rw [← h_mul_y]
    exact le_add_self_right (x * d) (x * z)
  have h_cancel : x * d + x * z = subtract (x * y) (x * z) h2 + x * z := by
    rw [h_mul_y, subtract_add_cancel (x * y) (x * z) h2]
  exact ⟨h2, add_cancel_right (x * d) (subtract (x * y) (x * z) h2) (x * z) h_cancel⟩

theorem subtract_multiply (x y z : Peano) (h : z ≤ y) :
    ∃ h2, subtract y z h * x = subtract (y * x) (z * x) h2 := by
    rw [multiply_commutative (subtract y z h), multiply_commutative y x, multiply_commutative z x]
    apply multiply_subtract

def Divisible (a b : Peano) : Prop := b ≠ zero ∧ ∃ c, b * c = a

def Power (e a : Peano) : Prop := ∃ b h, power b e h = a

theorem lt_successor_cases {x b : Peano} (h : x < b) : b = successor x ∨ successor x < b := by
  induction h with
  | base => exact Or.inl rfl
  | step hlt _ => exact Or.inr (succ_lt_succ hlt)

theorem divide_rec_step_h {a b x : Peano}
  (h : ∀ c, successor x < c → b * c ≠ a)
  (h3 : ¬ b * successor x = a) :
  ∀ c, x < c → b * c ≠ a := by
  intro c hxc hbc
  cases lt_successor_cases hxc with
  | inl h_eq =>
    subst c
    exact h3 hbc
  | inr hsxlt =>
    exact h c hsxlt hbc

def divide_rec (a b x : Peano) (h : Divisible a b) (h2 : ∀ c, x < c → b * c ≠ a) : Peano :=
  if h3 : b * x = a then
    x
  else
    match x with
    | zero =>
      False.elim (by
        rcases h with ⟨_, c, hc⟩
        cases c with
        | zero => exact h3 hc
        | successor c' => exact h2 (successor c') (zero_lt_succ c') hc)
    | successor x' => divide_rec a b x' h (divide_rec_step_h h2 h3)

theorem eq_zero_of_le_zero (a : Peano) (h : a ≤ zero) : a = zero := by
  cases h with
  | inl hlt =>
    generalize hz : zero = z at hlt
    induction hlt with
    | base => cases hz
    | step _ _ => cases hz
  | inr heq => exact heq

theorem le_of_lt_succ {a b : Peano} (h : a < b.successor) : a ≤ b := by
  cases h with
  | base =>
    right
    rfl
  | step h2 =>
    left
    exact h2

theorem lt_of_le_of_ne {a b : Peano} (h_le : a ≤ b) (h_ne : a ≠ b) : a < b := by
  cases h_le with
  | inl h_lt => exact h_lt
  | inr h_eq =>
    have h_contra : a = b := h_eq
    contradiction

theorem root_power_precondition (e x : Peano) (h : e ≠ zero) (h2 : x ≠ zero ∨ e ≠ zero) :
    e ≠ zero ∧ Power e (power x e h2) := by
  exact ⟨h, ⟨x, h2, rfl⟩⟩

theorem root_power_precondition_left (e x : Peano) (h : e ≠ zero) (h2 : x ≠ zero ∨ e ≠ zero) :
    (root_power_precondition e x h h2).left = h := by
  rfl

theorem root_power_precondition_right (e x : Peano) (h : e ≠ zero) (h2 : x ≠ zero ∨ e ≠ zero) :
    (root_power_precondition e x h h2).right = ⟨x, h2, rfl⟩ := by
  rfl

theorem le_add_right (x y : Peano) :x ≤ x + y := by
  induction y with
  | zero => exact Or.inr rfl
  | successor y' ih =>
    have h : x + y' ≤ x + y'.successor := by
      apply Or.inl
      exact LessThan.base
    exact le_trans ih h

theorem le_mul_of_pos_right (x y : Peano) (h : x ≠ zero) : y ≤ y * x := by
  induction x with
  | zero => contradiction
  | successor x' ih =>
    cases x' with
    | zero =>
      simp [multiply_successor, multiply_zero, zero_add]
      exact Or.inr rfl
    | successor x'' =>
      rw [multiply_successor]
      have h2 := le_add_right (y * x''.successor) y
      apply le_trans _ h2
      apply ih
      apply successor_ne_zero

theorem le_mul_of_pos_left (x y : Peano) (h : x ≠ zero) : y ≤ x * y := by
  cases x with
  | zero => contradiction
  | successor x' =>
    induction y with
    | zero => exact Or.inr rfl
    | successor y' =>
      rw [multiply_commutative]
      apply le_mul_of_pos_right
      exact h

theorem power_ne_zero (x e : Peano) (h : x ≠ zero) : ∃ h2, power x e h2 ≠ zero := by
  exists Or.inl h
  cases x with
  | zero => contradiction
  | successor x' =>
    induction e with
    | zero =>
      simp [power]
      intro
      contradiction
    | successor e' ih =>
      simp [power]
      apply multiply_ne_zero _ _ ih
      intro
      contradiction

theorem power_nonzero_of_nonzero_base (x e : Peano) (hx : x ≠ zero) :
  ∃ h2 : x ≠ zero ∨ e ≠ zero, power x e h2 ≠ zero := by
  let ⟨h2, hpow⟩ := power_ne_zero x e hx
  exact ⟨h2, hpow⟩

theorem power_eq_zero_iff_base_zero (x e : Peano) (he : e ≠ zero) (h2 : x ≠ zero ∨ e ≠ zero) :
  power x e h2 = zero ↔ x = zero := by
  constructor
  · intro hpow
    exact power_is_zero_if_base_is_zero x e h2 hpow
  · intro hx
    subst hx
    exact zero_power_of_nonzero_exponent e he h2

theorem le_self_pow (x e : Peano) (h : e ≠ zero) : ∃ h2, x ≤ power x e h2 := by
  exists Or.inr h
  induction e with
  | zero => contradiction
  | successor e' ih =>
    cases x with
    | zero => apply zero_le
    | successor x' =>
      let ⟨h2, h3⟩ := power_successor x'.successor e' (by simp)
      rw [h3]
      apply le_mul_of_pos_left
      let ⟨h4, h5⟩ := power_ne_zero x'.successor e' (by simp)
      exact h5

theorem lt_of_lt_of_le {a b c : Peano} (hab : a < b) (hbc : b ≤ c) : a < c := by
  cases hbc with
  | inl hlt => exact lt_trans hab hlt
  | inr heq =>
    rw [← heq]
    exact hab

theorem divide_rec_initial_h (a b : Peano) (h : Divisible a b) :
    ∀ c, a < c → b * c ≠ a := by
  intro c hac hbc
  have hle : c ≤ b * c := le_mul_of_pos_left b c h.left
  have halt : a < b * c := lt_of_lt_of_le hac hle
  rw [hbc] at halt
  exact not_lt_self a halt

def divide (a b : Peano) (h : Divisible a b) : Peano :=
  divide_rec a b a h (divide_rec_initial_h a b h)

theorem divide_rec_correct (a b x : Peano) (h : Divisible a b)
    (h2 : ∀ c, x < c → b * c ≠ a) :
    b * divide_rec a b x h h2 = a := by
  induction x with
  | zero =>
    unfold divide_rec
    by_cases h3 : b * zero = a
    · simp [h3]
    · simp [h3]
      exact False.elim (by
        rcases h with ⟨_, c, hc⟩
        cases c with
        | zero => exact h3 hc
        | successor c' => exact h2 (successor c') (zero_lt_succ c') hc)
  | successor x ih =>
    unfold divide_rec
    by_cases h3 : b * successor x = a
    · simp [h3]
    · simp [h3]
      exact ih (divide_rec_step_h h2 h3)

theorem multiply_divide (a b : Peano) (h : Divisible a b) : b * divide a b h = a := by
  unfold divide
  exact divide_rec_correct a b a h (divide_rec_initial_h a b h)

theorem exists_divide_of_tryDivide {x y z : Peano} (h : tryDivide x y = some z) :
    ∃ h', divide x y h' = z := by
  unfold tryDivide at h
  split at h
  · next => cases h
  · next y' =>
    split at h
    · next q hq =>
      injection h with hz
      subst hz
      have hx : x = y'.successor * q := by
        have hcorr := divideWithRemainder_correct x y'.successor (successor_ne_zero y') q zero hq
        rw [add_zero] at hcorr
        exact hcorr
      let hdiv : Divisible x y'.successor := ⟨successor_ne_zero y', q, hx.symm⟩
      refine ⟨hdiv, ?_⟩
      exact multiply_left_cancel y'.successor (divide x y'.successor hdiv) q
        (successor_ne_zero y') (by
          rw [multiply_divide x y'.successor hdiv, hx])
    · next _ _ => cases h

theorem divide_multiply_cancel (a b : Peano) (ha : a ≠ zero) :
    ∃ h : Divisible (a * b) a, divide (a * b) a h = b := by
  let h : Divisible (a * b) a := ⟨ha, b, rfl⟩
  exists h
  exact multiply_left_cancel a (divide (a * b) a h) b ha (multiply_divide (a * b) a h)

theorem multiply_divide_assoc_h {x y z : Peano} (h : Divisible y z) : Divisible (x * y) z := by
  rcases h with ⟨hz, c, hc⟩
  exact ⟨hz, x * c, by
    calc
      z * (x * c) = (z * x) * c := (multiply_associative z x c).symm
      _ = (x * z) * c := by rw [multiply_commutative z x]
      _ = x * (z * c) := multiply_associative x z c
      _ = x * y := by rw [hc]⟩

theorem multiply_divide_assoc (x y z : Peano) (h : Divisible y z) :
    ∃ h2 : Divisible (x * y) z, divide (x * y) z h2 = x * divide y z h := by
  let h2 : Divisible (x * y) z := multiply_divide_assoc_h (x := x) h
  exists h2
  apply multiply_left_cancel z
  · exact h.left
  calc
    z * divide (x * y) z h2 = x * y := multiply_divide (x * y) z h2
    _ = z * (x * divide y z h) := by
      calc
        x * y = x * (z * divide y z h) := by rw [multiply_divide y z h]
        _ = (x * z) * divide y z h := (multiply_associative x z (divide y z h)).symm
        _ = (z * x) * divide y z h := by rw [multiply_commutative x z]
        _ = z * (x * divide y z h) := multiply_associative z x (divide y z h)

theorem divide_add_h (x y z : Peano) (h : Divisible x z) (h2 : Divisible y z) :
    Divisible (x + y) z := by
  exact ⟨h.left, divide x z h + divide y z h2, by
    calc
      z * (divide x z h + divide y z h2) = z * divide x z h + z * divide y z h2 :=
        multiply_distributive_over_add_right z (divide x z h) (divide y z h2)
      _ = x + y := by rw [multiply_divide x z h, multiply_divide y z h2]⟩

theorem divide_add (x y z : Peano) (h : Divisible x z) (h2 : Divisible y z) :
    ∃ h3 : Divisible (x + y) z, divide (x + y) z h3 = divide x z h + divide y z h2 := by
  let h3 : Divisible (x + y) z := divide_add_h x y z h h2
  exists h3
  apply multiply_left_cancel z
  · exact h.left
  calc
    z * divide (x + y) z h3 = x + y := multiply_divide (x + y) z h3
    _ = z * (divide x z h + divide y z h2) := by
      rw [multiply_distributive_over_add_right z (divide x z h) (divide y z h2),
        multiply_divide x z h, multiply_divide y z h2]


theorem lt_successor_of_le {a b : Peano} (h : a ≤ b) : a < b.successor := by
  cases h with
  | inl hlt => exact LessThan.step hlt
  | inr heq =>
    rw [heq]
    exact LessThan.base

theorem lt_add_of_right_ne_zero (a b : Peano) (hb : b ≠ zero) : a < a + b := by
  cases b with
  | zero => contradiction
  | successor b' =>
    rw [add_successor]
    exact lt_successor_of_le (le_add_self_left a b')

theorem multiply_lt_of_lt_left (z : Peano) (hz : z ≠ zero) {a b : Peano} (h : a < b) :
    z * a < z * b := by
  induction h with
  | base =>
    rw [multiply_successor]
    exact lt_add_of_right_ne_zero (z * a) z hz
  | step _ ih =>
    rw [multiply_successor]
    exact lt_of_lt_of_le ih (le_add_self_left (z * _) z)

theorem le_of_multiply_le_multiply_left (z a b : Peano) (hz : z ≠ zero) (h : z * a ≤ z * b) :
    a ≤ b := by
  cases trichotomy a b with
  | first hlt _ _ => exact Or.inl hlt
  | second heq _ _ => exact Or.inr heq
  | third hgt _ _ =>
    have hmul : z * b < z * a := multiply_lt_of_lt_left z hz hgt
    cases h with
    | inl hle_lt => exact False.elim (not_lt_self (z * b) (lt_trans hmul hle_lt))
    | inr hle_eq =>
      rw [hle_eq] at hmul
      exact False.elim (not_lt_self (z * b) hmul)

theorem divide_subtract_h (x y z : Peano) (h : Divisible x z) (h2 : Divisible y z) (h4 : y ≤ x) :
    Divisible (subtract x y h4) z := by
  let qx := divide x z h
  let qy := divide y z h2
  have hmul_le : z * qy ≤ z * qx := by
    rw [multiply_divide y z h2, multiply_divide x z h]
    exact h4
  have h5 : qy ≤ qx := le_of_multiply_le_multiply_left z qy qx h.left hmul_le
  let d := subtract qx qy h5
  exact ⟨h.left, d, by
    rcases multiply_subtract z qx qy h5 with ⟨hmul_sub_le, hmul_sub⟩
    calc
      z * d = subtract (z * qx) (z * qy) hmul_sub_le := hmul_sub
      _ = subtract x y h4 := by
        apply add_cancel_right (subtract (z * qx) (z * qy) hmul_sub_le) (subtract x y h4) (z * qy)
        calc
          subtract (z * qx) (z * qy) hmul_sub_le + z * qy = z * qx :=
            subtract_add_cancel (z * qx) (z * qy) hmul_sub_le
          _ = x := multiply_divide x z h
          _ = subtract x y h4 + z * qy := by
            rw [multiply_divide y z h2, subtract_add_cancel x y h4]
  ⟩

theorem divide_subtract (x y z : Peano) (h : Divisible x z) (h2 : Divisible y z) (h4 : y ≤ x) :
  ∃ (h3 : Divisible (subtract x y h4) z) (h5 : divide y z h2 ≤ divide x z h),
  divide (subtract x y h4) z h3 = subtract (divide x z h) (divide y z h2) h5 := by
  let qx := divide x z h
  let qy := divide y z h2
  have hmul_le : z * qy ≤ z * qx := by
    rw [multiply_divide y z h2, multiply_divide x z h]
    exact h4
  have h5 : qy ≤ qx := le_of_multiply_le_multiply_left z qy qx h.left hmul_le
  let d := subtract qx qy h5
  have h3 : Divisible (subtract x y h4) z := by
    exact divide_subtract_h x y z h h2 h4
  exists h3
  exists h5
  apply multiply_left_cancel z
  · exact h.left
  calc
    z * divide (subtract x y h4) z h3 = subtract x y h4 := multiply_divide (subtract x y h4) z h3
    _ = z * d := by
      rcases multiply_subtract z qx qy h5 with ⟨hmul_sub_le, hmul_sub⟩
      calc
        subtract x y h4 = subtract (z * qx) (z * qy) hmul_sub_le := by
          apply add_cancel_right (subtract x y h4) (subtract (z * qx) (z * qy) hmul_sub_le) (z * qy)
          calc
            subtract x y h4 + z * qy = x := by
              rw [multiply_divide y z h2, subtract_add_cancel x y h4]
            _ = z * qx := (multiply_divide x z h).symm
            _ = subtract (z * qx) (z * qy) hmul_sub_le + z * qy :=
              (subtract_add_cancel (z * qx) (z * qy) hmul_sub_le).symm
        _ = z * d := hmul_sub.symm

theorem divide_divide_h (x y z : Peano) (h : Divisible x y)
    (h2 : Divisible (divide x y h) z) : Divisible x (y * z) := by
  exact ⟨multiply_ne_zero y z h.left h2.left, divide (divide x y h) z h2, by
    calc
      (y * z) * divide (divide x y h) z h2 = y * (z * divide (divide x y h) z h2) :=
        multiply_associative y z (divide (divide x y h) z h2)
      _ = y * divide x y h := by rw [multiply_divide (divide x y h) z h2]
      _ = x := multiply_divide x y h⟩

theorem divide_divide (x y z : Peano) (h : Divisible x y)
    (h2 : Divisible (divide x y h) z) :
    ∃ h3 : Divisible x (y * z), divide (divide x y h) z h2 = divide x (y * z) h3 := by
  let h3 : Divisible x (y * z) := divide_divide_h x y z h h2
  exists h3
  apply multiply_left_cancel (y * z)
  · exact h3.left
  calc
    (y * z) * divide (divide x y h) z h2 = y * (z * divide (divide x y h) z h2) :=
      multiply_associative y z (divide (divide x y h) z h2)
    _ = y * divide x y h := by rw [multiply_divide (divide x y h) z h2]
    _ = x := multiply_divide x y h
    _ = (y * z) * divide x (y * z) h3 := (multiply_divide x (y * z) h3).symm

theorem multiply_lt_of_lt_right (z : Peano) (hz : z ≠ zero) {a b : Peano} (h : a < b) :
    a * z < b * z := by
  rw [multiply_commutative a z, multiply_commutative b z]
  exact multiply_lt_of_lt_left z hz h

theorem lt_power {a b e : Peano} (he : e ≠ zero) (h : a < b)
    (ha : a ≠ zero ∨ e ≠ zero) (hb : b ≠ zero ∨ e ≠ zero) :
    power a e ha < power b e hb := by
  cases e with
  | zero => contradiction
  | successor e' =>
    revert ha hb
    clear he
    induction e' generalizing a b with
    | zero =>
      intro ha hb
      have ha' : power a one ha = a := power_one_eq_self a ha
      have hb' : power b one hb = b := power_one_eq_self b hb
      change power a one ha < power b one hb
      rw [ha', hb']
      exact h
    | successor e'' ih =>
      intro ha hb
      have he1 : e''.successor ≠ zero := successor_ne_zero e''
      have hlt : power a e''.successor (Or.inr he1) < power b e''.successor (Or.inr he1) :=
        ih h (Or.inr he1) (Or.inr he1)
      obtain ⟨ha2, haeq⟩ := power_successor a e''.successor (Or.inr he1)
      obtain ⟨hb2, hbeq⟩ := power_successor b e''.successor (Or.inr he1)
      have haeq' : power a (e''.successor.successor) ha =
          power a e''.successor (Or.inr he1) * a := by
        calc power a e''.successor.successor ha
            = power a e''.successor.successor ha2 := rfl
          _ = power a e''.successor (Or.inr he1) * a := haeq
      have hbeq' : power b (e''.successor.successor) hb =
          power b e''.successor (Or.inr he1) * b := by
        calc power b e''.successor.successor hb
            = power b e''.successor.successor hb2 := rfl
          _ = power b e''.successor (Or.inr he1) * b := hbeq
      rw [haeq', hbeq']
      cases a with
      | zero =>
        rw [multiply_zero]
        cases b with
        | zero => exact False.elim (not_lt_zero _ h)
        | successor b' =>
          exact zero_lt_of_ne_zero _
            (multiply_ne_zero _ _ (power_ne_zero_of_base_ne_zero _ _ (Or.inr he1) (successor_ne_zero _))
              (successor_ne_zero _))
      | successor a' =>
        have h1' : power a'.successor e''.successor (Or.inr he1) * a'.successor <
            power b e''.successor (Or.inr he1) * a'.successor :=
          multiply_lt_of_lt_right a'.successor (successor_ne_zero a') hlt
        have hb_ne : b ≠ zero := by
          intro hb0; rw [hb0] at h; exact not_lt_zero _ h
        have h2 : power b e''.successor (Or.inr he1) * a'.successor <
            power b e''.successor (Or.inr he1) * b :=
          multiply_lt_of_lt_left _
            (power_ne_zero_of_base_ne_zero b e''.successor (Or.inr he1) hb_ne) h
        exact lt_trans h1' h2

theorem power_injective_base (a b e : Peano) (he : e ≠ zero)
    (ha : a ≠ zero ∨ e ≠ zero) (hb : b ≠ zero ∨ e ≠ zero)
    (hp : power a e ha = power b e hb) : a = b := by
  cases trichotomy a b with
  | first hlt _ _ =>
    exact False.elim (ne_of_lt (lt_power he hlt ha hb) hp)
  | second heq _ _ =>
    exact heq
  | third hgt _ _ =>
    exact False.elim (ne_of_lt (lt_power he hgt hb ha) hp.symm)

theorem two_ne_zero : (two : Peano) ≠ zero := successor_ne_zero one

/-- Two is not ≤ zero. -/
theorem not_two_le_zero : ¬(two ≤ zero) := by
  intro h
  exact not_succ_le_zero (by simpa only [two] using h)

/-- Two is not ≤ one. -/
theorem not_two_le_one : ¬(two ≤ one) := by
  intro h
  exact not_succ_le_zero
    (le_of_succ_le_succ (by simpa only [two, one] using h))

/-- A cardinal at least two is a double successor. -/
theorem eq_succ_succ_of_two_le (k : Peano) (hge : two ≤ k) :
    ∃ n, k = successor (successor n) := by
  cases k with
  | zero => exact (not_two_le_zero hge).elim
  | successor m =>
    cases m with
    | zero => exact (not_two_le_one hge).elim
    | successor n => exact ⟨n, rfl⟩

theorem one_power (e : Peano) (h : one ≠ zero ∨ e ≠ zero) : power one e h = one := by
  induction e with
  | zero => rfl
  | successor e' ih =>
    change power one e' (power.recursiveCondition zero e') * one = one
    rw [ih (power.recursiveCondition zero e'), multiply_one]

theorem one_lt_two_pow (e : Peano) (he : e ≠ zero) :
    one < power two e (Or.inl two_ne_zero) := by
  cases e with
  | zero => contradiction
  | successor e' =>
    clear he
    induction e' with
    | zero =>
      change one < power two one (Or.inl two_ne_zero)
      rw [power_one_eq_self]
      exact LessThan.base
    | successor e'' ih =>
      change one <
        power two e''.successor (power.recursiveCondition one e''.successor) * two
      have hpow :
          power two e''.successor (power.recursiveCondition one e''.successor) =
          power two e''.successor (Or.inl two_ne_zero) := rfl
      rw [hpow]
      have hle : power two e''.successor (Or.inl two_ne_zero) ≤
          power two e''.successor (Or.inl two_ne_zero) * two :=
        le_mul_of_pos_right two _ two_ne_zero
      exact lt_of_lt_of_le ih hle

theorem subtract_eq_of_eq {a b c d : Peano} (h1 : b ≤ a) (h2 : d ≤ c)
    (h3 : a = c) (h4 : b = d) : subtract a b h1 = subtract c d h2 := by
  subst h3
  subst h4
  rfl

theorem exists_subtract_of_trySubtract {x y z : Peano} (h : trySubtract x y = some z) :
    ∃ h', subtract x y h' = z := by
  induction y generalizing x z with
  | zero =>
    refine ⟨zero_le x, ?_⟩
    have : some x = some z := by simpa [trySubtract] using h
    have hx := Option.some.inj this
    simpa [subtract] using hx
  | successor y' ih =>
    cases x with
    | zero =>
      simp [trySubtract] at h
    | successor x' =>
      simp [trySubtract] at h
      obtain ⟨h', heq⟩ := ih h
      refine ⟨succ_le_succ h', ?_⟩
      change subtract x' y' _ = z
      exact (subtract_eq_of_eq _ h' rfl rfl).trans heq

theorem trySubtract_of_subtract {x y z : Peano} (h : ∃ h', subtract x y h' = z) :
    trySubtract x y = some z := by
  induction y generalizing x z with
  | zero =>
    obtain ⟨_, heq⟩ := h
    have hx : x = z := by simpa [subtract] using heq
    simpa [trySubtract] using congrArg some hx
  | successor y' ih =>
    obtain ⟨hle, heq⟩ := h
    cases x with
    | zero =>
      exact (not_succ_le_zero hle).elim
    | successor x' =>
      simp [trySubtract]
      apply ih
      refine ⟨le_of_succ_le_succ hle, ?_⟩
      change subtract x' y' _ = z
      exact (subtract_eq_of_eq _ (le_of_succ_le_succ hle) rfl rfl).symm.trans heq

/-- A successful subtraction `trySubtract y x = some d` means `y = x + d`. -/
theorem eq_of_trySubtract_add (x y d : Peano)
    (h : trySubtract y x = some d) : y = x + d := by
  obtain ⟨hle, hsub⟩ := exists_subtract_of_trySubtract h
  have hsum := subtract_add_cancel y x hle
  rw [hsub] at hsum
  exact (add_commutative d x) ▸ hsum.symm

/-- `trySubtract (x + d) x` recovers the added difference `d`. -/
theorem trySubtract_self_add (x d : Peano) : trySubtract (x + d) x = some d := by
  obtain ⟨h, heq⟩ := add_subtract_cancel d x
  refine trySubtract_of_subtract ⟨le_add_self_left x d, ?_⟩
  exact (subtract_eq_of_eq (le_add_self_left x d) h (add_commutative x d) rfl).trans heq

/-- `subtract (a + b) a` recovers `b`. -/
theorem subtract_add_left (a b : Peano) :
    subtract (a + b) a (le_add_self_left a b) = b := by
  obtain ⟨h, heq⟩ := add_subtract_cancel b a
  exact (subtract_eq_of_eq (le_add_self_left a b) h (add_commutative a b) rfl).trans
    heq

/-- `trySubtract (x + d) d` recovers the left addend `x`. -/
theorem trySubtract_add_right (x d : Peano) : trySubtract (x + d) d = some x :=
  trySubtract_of_subtract (add_subtract_cancel x d)

/-- If `trySubtract y x = some d`, then `trySubtract y d = some x`. -/
theorem trySubtract_comm (x y d : Peano)
    (h : trySubtract y x = some d) :
    trySubtract y d = some x := by
  rw [eq_of_trySubtract_add x y d h]
  exact trySubtract_add_right x d

/-- A successful `trySubtract first diff = some next` implies `next ≤ first`. -/
theorem le_of_trySubtract_eq_some (first diff next : Peano)
    (h : trySubtract first diff = some next) : next ≤ first := by
  have hadd := eq_of_trySubtract_add diff first next h
  rw [hadd, add_commutative]
  exact le_add_self_left next diff

/-- If `trySubtract first diff = some next`, then `subtract first next` recovers
`diff`. -/
theorem subtract_eq_diff_of_trySubtract (first diff next : Peano)
    (h : trySubtract first diff = some next) :
    subtract first next (le_of_trySubtract_eq_some first diff next h) = diff := by
  have hadd : first = diff + next := eq_of_trySubtract_add diff first next h
  obtain ⟨hle', heq⟩ := add_subtract_cancel diff next
  exact (subtract_eq_of_eq _ hle' hadd rfl).trans heq

theorem subtract_le_self (a b : Peano) (h : b ≤ a) : subtract a b h ≤ a := by
  have hcancel := subtract_add_cancel a b h
  have hle := le_add_self_left (subtract a b h) b
  rw [hcancel] at hle
  exact hle

theorem subtract_ne_zero_of_lt {a b : Peano} (h_le : b ≤ a) (h_lt : b < a) :
    subtract a b h_le ≠ zero := by
  intro h_zero
  have h_cancel := subtract_add_cancel a b h_le
  rw [h_zero, zero_add] at h_cancel
  exact ne_of_lt h_lt h_cancel

theorem div_rem_unique (b q r q' r' : Peano)
    (hr : r < b) (hr' : r' < b)
    (h : b * q + r = b * q' + r') : q = q' ∧ r = r' := by
  cases trichotomy_or q q' with
  | inl hlt_qq' =>
    rcases multiply_subtract b q' q (Or.inl hlt_qq') with ⟨hmul_le, hsub_eq⟩
    have hsub_add := subtract_add_cancel (b * q') (b * q) hmul_le
    have hr_eq : r = subtract (b * q') (b * q) hmul_le + r' := by
      apply add_left_cancel (b * q)
      calc
        b * q + r = b * q' + r' := h
        _ = subtract (b * q') (b * q) hmul_le + b * q + r' := by
              rw [hsub_add]
        _ = b * q + (subtract (b * q') (b * q) hmul_le + r') := by
              rw [add_commutative (subtract (b * q') (b * q) hmul_le) (b * q),
                add_associative]
    have hb_le : b ≤ r := by
      rw [hr_eq, ← hsub_eq]
      exact le_trans
        (le_mul_of_pos_right (subtract q' q (Or.inl hlt_qq')) b
          (subtract_ne_zero_of_lt (Or.inl hlt_qq') hlt_qq'))
        (le_add_self_left (b * subtract q' q (Or.inl hlt_qq')) r')
    exact False.elim (not_lt_self r (lt_of_lt_of_le hr hb_le))
  | inr hrest =>
    cases hrest with
    | inl heq_qq' =>
      subst heq_qq'
      exact ⟨rfl, add_left_cancel (b * q) r r' h⟩
    | inr hlt_q'q =>
      rcases multiply_subtract b q q' (Or.inl hlt_q'q) with ⟨hmul_le, hsub_eq⟩
      have hsub_add := subtract_add_cancel (b * q) (b * q') hmul_le
      have hr'_eq : r' = subtract (b * q) (b * q') hmul_le + r := by
        apply add_left_cancel (b * q')
        calc
          b * q' + r' = b * q + r := h.symm
          _ = subtract (b * q) (b * q') hmul_le + b * q' + r := by
                rw [hsub_add]
          _ = b * q' + (subtract (b * q) (b * q') hmul_le + r) := by
                rw [add_commutative (subtract (b * q) (b * q') hmul_le) (b * q'),
                  add_associative]
      have hb_le : b ≤ r' := by
        rw [hr'_eq, ← hsub_eq]
        exact le_trans
          (le_mul_of_pos_right (subtract q q' (Or.inl hlt_q'q)) b
            (subtract_ne_zero_of_lt (Or.inl hlt_q'q) hlt_q'q))
          (le_add_self_left (b * subtract q q' (Or.inl hlt_q'q)) r)
      exact False.elim (not_lt_self r' (lt_of_lt_of_le hr' hb_le))

theorem divideWithRemainder_eq_of_mul_add (a b : Peano) (hb : b ≠ zero) (q r : Peano)
    (hlt : r < b) (ha : a = b * q + r) :
    divideWithRemainder a b hb = (q, r) := by
  cases hres : divideWithRemainder a b hb with
  | mk q' r' =>
    have hcorr := divideWithRemainder_correct a b hb q' r' hres
    have hlt' := divideWithRemainder_remainder_lt_b a b hb q' r' hres
    obtain ⟨hq, hr⟩ := div_rem_unique b q r q' r' hlt hlt'
      (by rw [← ha, hcorr])
    exact Prod.ext hq.symm hr.symm

theorem divideWithRemainder_eq_of_mul (a b : Peano) (hb : b ≠ zero) (c : Peano)
    (hac : a = b * c) :
    divideWithRemainder a b hb = (c, zero) := by
  apply divideWithRemainder_eq_of_mul_add
  · exact zero_lt_of_ne_zero b hb
  · rw [hac, add_zero]

/-- Dividing `a + b` by `b` increments the quotient of `a / b` by one. -/
theorem divideWithRemainder_add_right (a b : Peano) (hb : b ≠ zero) :
    divideWithRemainder (a + b) b hb =
      match divideWithRemainder a b hb with
      | (q, r) => (q.successor, r) := by
  cases ha : divideWithRemainder a b hb with
  | mk q r =>
    have hcorr := divideWithRemainder_correct a b hb q r ha
    have hlt := divideWithRemainder_remainder_lt_b a b hb q r ha
    have hab : a + b = b * q.successor + r := by
      rw [hcorr, multiply_successor]
      calc
        b * q + r + b = b * q + (r + b) := by rw [add_associative]
        _ = b * q + (b + r) := by rw [add_commutative r b]
        _ = b * q + b + r := by rw [← add_associative]
    have hres :=
      divideWithRemainder_eq_of_mul_add (a + b) b hb q.successor r hlt hab
    simpa [ha] using hres

theorem tryDivide_of_divide {x y z : Peano} (h : ∃ h', divide x y h' = z) :
    tryDivide x y = some z := by
  obtain ⟨hdiv, heq⟩ := h
  have hx : x = y * z := by
    rw [← heq]
    exact (multiply_divide x y hdiv).symm
  cases y with
  | zero => exact absurd rfl hdiv.left
  | successor y' =>
    have hpair : divideWithRemainder x y'.successor (successor_ne_zero y') = (z, zero) :=
      divideWithRemainder_eq_of_mul x y'.successor (successor_ne_zero y') z hx
    simp [tryDivide, hpair]

/-- A successful `tryDivide` recovers the multiplicative relation `y * q = x`. -/
theorem eq_of_tryDivide_mul {x y q : Peano} (h : tryDivide x y = some q) :
    y * q = x := by
  obtain ⟨hdiv, heq⟩ := exists_divide_of_tryDivide h
  simpa [heq] using multiply_divide x y hdiv

/-- `tryDivide` inverts left-multiplication: dividing `b * a` by nonzero `b`
recovers `a`. -/
theorem tryDivide_mul (a b : Peano) (hb : b ≠ zero) :
    tryDivide (b * a) b = some a :=
  tryDivide_of_divide (divide_multiply_cancel b a hb)

theorem not_succ_lt_one (c : Peano) : ¬(successor c < one) := by
  intro h
  have h' : c < zero := by
    simp only [one] at h
    exact lt_of_succ_lt_succ h
  exact not_lt_zero c h'

theorem rootWithRemainderAux_reset_zero_lt {b e : Peano} (he : e ≠ zero) (hb : b = one) :
    power b e (Or.inr he) < power two e (Or.inl two_ne_zero) := by
  rw [hb, one_power]
  exact one_lt_two_pow e he

theorem rootWithRemainderAux_zero_succ_false {e c p b : Peano} (he : e ≠ zero)
    (hc : successor c < p) (hp : p = power b e (Or.inr he)) (hb : b = one) : False := by
  have hp' : p = one := by
    rw [hp, hb, one_power]
  rw [hp'] at hc
  exact not_succ_lt_one c hc

theorem rootWithRemainderAux_advance_lt (e b : Peano) (he : e ≠ zero) :
    power b e (Or.inr he) < power b.successor e (Or.inr he) :=
  lt_power he LessThan.base (Or.inr he) (Or.inr he)

def rootWithRemainderAux (a e : Peano) (he : e ≠ zero) (r c p b : Peano)
    (hc : c < p) (hp : p = power b e (Or.inr he))
    (hzero : r = zero → b = one)
    (hsucc : ∀ k, r = successor k → b = successor k)
    (hbound : ∀ k, r = successor k →
      ∀ hle : power k e (Or.inr he) ≤ p,
        successor c ≤ subtract p (power k e (Or.inr he)) hle) :
    Peano × Peano :=
  match a, r, c with
  | zero, _, _ =>
    (zero, zero)
  | successor a', zero, zero =>
    match a' with
    | zero =>
      (one, zero)
    | successor a =>
      have hlt : p < power two e (Or.inr he) := by
        rw [hp]
        exact rootWithRemainderAux_reset_zero_lt he (hzero rfl)
      have hle : p ≤ power two e (Or.inr he) := Or.inl hlt
      have hgap_ne : subtract (power two e (Or.inr he)) p hle ≠ zero :=
        subtract_ne_zero_of_lt hle hlt
      rootWithRemainderAux (successor a) e he two
        (predecessor (subtract (power two e (Or.inr he)) p hle) hgap_ne)
        (power two e (Or.inr he)) two
        (lt_of_lt_of_le (predecessor_lt _ hgap_ne) (subtract_le_self _ _ hle))
        rfl
        (fun h => nomatch h)
        (fun k hk => by
          injection hk with hk
          rw [← hk]
          rfl)
        (fun k hk hle' => by
          injection hk with hk
          subst hk
          have hp' : p = power one e (Or.inr he) := by
            rw [hp, hzero rfl, one_power]
          rw [successor_predecessor]
          exact Or.inr (subtract_eq_of_eq hle hle' rfl hp'))
  | successor a', successor r, zero =>
    match a' with
    | zero =>
      (successor r, zero)
    | successor a =>
      have hb : b = successor r := hsucc r rfl
      have hlt : p < power b.successor e (Or.inr he) := by
        rw [hp]
        exact rootWithRemainderAux_advance_lt e b he
      have hle : p ≤ power b.successor e (Or.inr he) := Or.inl hlt
      have hgap_ne : subtract (power b.successor e (Or.inr he)) p hle ≠ zero :=
        subtract_ne_zero_of_lt hle hlt
      rootWithRemainderAux (successor a) e he (successor b)
        (predecessor (subtract (power b.successor e (Or.inr he)) p hle) hgap_ne)
        (power b.successor e (Or.inr he)) b.successor
        (lt_of_lt_of_le (predecessor_lt _ hgap_ne) (subtract_le_self _ _ hle))
        rfl
        (fun h => nomatch h)
        (fun k hk => by
          injection hk with hk
          rw [← hk])
        (fun k hk hle' => by
          injection hk with hk
          subst hk
          rw [successor_predecessor]
          exact Or.inr (subtract_eq_of_eq hle hle' rfl hp))
  | successor a', r, successor c =>
    match a', r with
    | zero, zero =>
      False.elim (rootWithRemainderAux_zero_succ_false he hc hp (hzero rfl))
    | zero, successor r =>
      have hlt_gap : power r e (Or.inr he) < p := by
        rw [hp, hsucc r rfl]
        exact rootWithRemainderAux_advance_lt e r he
      have hle_gap : power r e (Or.inr he) ≤ p := Or.inl hlt_gap
      have hc_gap : successor (successor c) ≤ subtract p (power r e (Or.inr he)) hle_gap :=
        hbound r rfl hle_gap
      have hle_c : successor c ≤ subtract p (power r e (Or.inr he)) hle_gap :=
        le_of_succ_le hc_gap
      (r, subtract (subtract p (power r e (Or.inr he)) hle_gap) (successor c) hle_c)
    | successor a, r =>
      rootWithRemainderAux (successor a) e he r c p b (lt_of_succ_lt hc) hp hzero hsucc
        (fun k hk hle => le_of_succ_le (hbound k hk hle))

def rootWithRemainder (a e : Peano) (he : e ≠ zero) : Peano × Peano :=
  rootWithRemainderAux a e he zero zero one one
    (zero_lt_succ zero)
    (by rw [one_power e (Or.inr he)])
    (fun _ => rfl)
    (fun _ hk => by cases hk)
    (fun _ hk => by cases hk)

def tryRoot (e a : Peano) : Option Peano :=
  match e with
  | zero => none
  | successor e' =>
    match rootWithRemainder a e'.successor (successor_ne_zero e') with
    | (b, zero) => some b
    | (_, successor _) => none

theorem lt_of_le_lt {x y z : Peano} (h1 : x ≤ y) (h2 : y < z) : x < z := by
  cases h1 with
  | inl hlt => exact lt_trans hlt h2
  | inr heq => rw [heq]; exact h2

theorem one_add_subtract_one (p : Peano) (h : one < p) :
    one + subtract p one (Or.inl h) = p := by
  rw [one_add]
  cases p with
  | zero => exact False.elim (not_lt_zero one h)
  | successor p' =>
    cases p' with
    | zero => exact False.elim (not_lt_self one h)
    | successor p'' =>
      rfl

theorem succ_add_subtract_one (a p : Peano) (h : one < p) :
    successor a + subtract p one (Or.inl h) = a + p := by
  cases p with
  | zero => exact False.elim (not_lt_zero one h)
  | successor p' =>
    cases p' with
    | zero => exact False.elim (not_lt_self one h)
    | successor p'' =>
      change successor a + successor p'' = a + successor (successor p'')
      rw [successor_add, ← add_successor]

theorem subtract_succ_add_one (b c : Peano) (hlt : successor c < b) :
    subtract b c (Or.inl (lt_of_succ_lt hlt)) =
      one + subtract b (successor c) (Or.inl hlt) := by
  induction c generalizing b with
  | zero =>
    cases b with
    | zero => exact False.elim (not_lt_zero _ hlt)
    | successor b' =>
      cases b' with
      | zero => exact False.elim (not_lt_self one hlt)
      | successor b'' =>
        simp only [subtract, one_add]
  | successor c ih =>
    cases b with
    | zero => exact False.elim (not_lt_zero _ hlt)
    | successor b' =>
      rw [subtract, subtract]
      exact ih b' (lt_of_succ_lt_succ hlt)

theorem add_subtract_succ_step (a p c : Peano) (hlt : successor c < p) :
    successor a + subtract p (successor c) (Or.inl hlt) =
    a + subtract p c (Or.inl (lt_of_succ_lt hlt)) := by
  rw [subtract_succ_add_one p c hlt, ← add_associative, add_one]

theorem subtract_lt_right (x y : Peano) (h : y < x) (hy : y ≠ zero) :
    subtract x y (Or.inl h) < x := by
  have hcancel := subtract_add_cancel x y (Or.inl h)
  exact lt_of_lt_add_right_eq (lt_add_of_right_ne_zero _ y hy) hcancel

theorem subtract_subtract_cancel (x y : Peano) (h : y < x) (hy : y ≠ zero) :
    ∃ h2, subtract x (subtract x y (Or.inl h)) h2 = y := by
  have h2 : subtract x y (Or.inl h) < x := subtract_lt_right x y h hy
  refine ⟨Or.inl h2, ?_⟩
  apply add_cancel_right _ _ (subtract x y (Or.inl h))
  rw [subtract_add_cancel x (subtract x y (Or.inl h)) (Or.inl h2), add_commutative,
    subtract_add_cancel x y (Or.inl h)]

theorem subtract_eq_add_subtract_gap (p k c : Peano) (hlt_k : k < p) (hk : k ≠ zero)
    (hlt_c : c < subtract p k (Or.inl hlt_k)) :
    subtract p c (Or.inl (lt_trans hlt_c (subtract_lt_right p k hlt_k hk))) =
    k + subtract (subtract p k (Or.inl hlt_k)) c (Or.inl hlt_c) := by
  apply add_cancel_right _ _ c
  calc
    subtract p c (Or.inl (lt_trans hlt_c (subtract_lt_right p k hlt_k hk))) + c = p := by
      rw [subtract_add_cancel]
    _ = subtract p k (Or.inl hlt_k) + k := by
      rw [subtract_add_cancel]
    _ = k + subtract p k (Or.inl hlt_k) := by
      rw [add_commutative]
    _ = k + (subtract (subtract p k (Or.inl hlt_k)) c (Or.inl hlt_c) + c) := by
      rw [subtract_add_cancel]
    _ = (k + subtract (subtract p k (Or.inl hlt_k)) c (Or.inl hlt_c)) + c := by
      rw [add_associative]

theorem rootWithRemainderAux_gap_lt_p {k p : Peano} (hlt : k < p) (hk : k ≠ zero) :
    subtract p k (Or.inl hlt) < p :=
  subtract_lt_right p k hlt hk

theorem rootWithRemainderAux_c_lt_p {k c p e : Peano} (he : e ≠ zero)
    (hlt : power k e (Or.inr he) < p) (hk : k ≠ zero)
    (hc : c ≤ subtract p (power k e (Or.inr he)) (Or.inl hlt)) : c < p :=
  lt_of_le_lt hc (rootWithRemainderAux_gap_lt_p hlt (power_ne_zero_of_base_ne_zero k e (Or.inr he) hk))

/-- Original value in a successor-`r` state: remaining `a` plus how far the counter has advanced. -/
def rootWithRemainderOrig (a c p : Peano) (hlt : successor c < p) : Peano :=
  a + subtract p (successor c) (Or.inl hlt)

theorem rootWithRemainderAux_correct (e : Peano) (he : e ≠ zero) :
    ∀ (a : Peano) (r c p b : Peano)
      (hc : c < p) (hp : p = power b e (Or.inr he))
      (hzero : r = zero → b = one)
      (hsucc : ∀ k, r = successor k → b = successor k)
      (hbound : ∀ k, r = successor k →
        ∀ hle : power k e (Or.inr he) ≤ p,
          successor c ≤ subtract p (power k e (Or.inr he)) hle),
      (r = zero →
        (let res := rootWithRemainderAux a e he r c p b hc hp hzero hsucc hbound
         a = power res.1 e (Or.inr he) + res.2 ∧
         a < power res.1.successor e (Or.inr he))) ∧
      (∀ k, r = successor k → a ≠ zero → ∀ (hlt : successor c < p),
        (let orig := rootWithRemainderOrig a c p hlt
         let res := rootWithRemainderAux a e he r c p b hc hp hzero hsucc hbound
         orig = power res.1 e (Or.inr he) + res.2 ∧
         orig < power res.1.successor e (Or.inr he))) := by
  intro a
  induction a with
  | zero =>
    intro r c p b hc hp hzero hsucc hbound
    constructor
    · intro hr
      simp only [rootWithRemainderAux]
      constructor
      · rw [zero_power_of_nonzero_exponent e he (Or.inr he), zero_add]
      · show zero < power one e (Or.inr he)
        rw [one_power]
        exact zero_lt_succ zero
    · intro k hr ha
      exact absurd rfl ha
  | successor a' ih =>
    intro r c p b hc hp hzero hsucc hbound
    constructor
    · -- r = zero branch
      intro hr; subst hr
      have hb_one : b = one := hzero rfl
      have hp_one : p = one := by rw [hp, hb_one, one_power]
      cases c with
      | zero =>
        cases a' with
        | zero =>
          -- a = one; result is (one, zero)
          simp only [rootWithRemainderAux]
          constructor
          · rw [one_power e (Or.inr he), add_zero]; rfl
          · show successor zero < power two e (Or.inr he)
            exact one_lt_two_pow e he
        | successor a_inner =>
          -- a = succ(succ a_inner); reset to two
          have hlt_reset : p < power two e (Or.inr he) :=
            hp_one ▸ one_lt_two_pow e he
          have hle_reset : p ≤ power two e (Or.inr he) := Or.inl hlt_reset
          have hgap_ne : subtract (power two e (Or.inr he)) p hle_reset ≠ zero :=
            subtract_ne_zero_of_lt hle_reset hlt_reset
          have hp_ne : p ≠ zero := hp_one ▸ successor_ne_zero zero
          have hlt_gap : subtract (power two e (Or.inr he)) p (Or.inl hlt_reset) <
              power two e (Or.inr he) :=
            rootWithRemainderAux_gap_lt_p hlt_reset hp_ne
          have hlt_inner : (predecessor (subtract (power two e (Or.inr he)) p hle_reset)
              hgap_ne).successor < power two e (Or.inr he) := by
            rw [successor_predecessor]; exact hlt_gap
          have ih_pair := ih two
            (predecessor (subtract (power two e (Or.inr he)) p hle_reset) hgap_ne)
            (power two e (Or.inr he)) two
            (lt_of_lt_of_le (predecessor_lt _ hgap_ne) (subtract_le_self _ _ hle_reset))
            rfl
            (fun h => nomatch h)
            (fun k' hk' => hk')
            (fun k' hk' hle' => by
              simp only [two] at hk'
              injection hk' with hk'; subst hk'
              have hp' : p = power one e (Or.inr he) := by rw [hp, hb_one, one_power]
              rw [successor_predecessor]
              exact Or.inr (subtract_eq_of_eq hle_reset hle' rfl hp'))
          obtain ⟨_, ih_succ⟩ := ih_pair
          have ih_at := ih_succ one rfl (successor_ne_zero a_inner) hlt_inner
          simp only [rootWithRemainderAux]
          have horig_eq : rootWithRemainderOrig (successor a_inner)
              (predecessor (subtract (power two e (Or.inr he)) p hle_reset) hgap_ne)
              (power two e (Or.inr he)) hlt_inner = successor (successor a_inner) := by
            simp only [rootWithRemainderOrig]
            have key : subtract (power two e (Or.inr he))
                ((predecessor (subtract (power two e (Or.inr he)) p hle_reset) hgap_ne).successor)
                (Or.inl hlt_inner) = p := by
              rw [subtract_eq_of_eq (Or.inl hlt_inner) (Or.inl hlt_gap) rfl
                    (successor_predecessor _ hgap_ne)]
              rcases subtract_subtract_cancel (power two e (Or.inr he)) p hlt_reset hp_ne
                with ⟨h2, hcancel⟩
              rw [subtract_eq_of_eq (Or.inl hlt_gap) h2 rfl rfl]
              exact hcancel
            rw [key, hp_one, add_one]
          rw [horig_eq] at ih_at
          exact ih_at
      | successor c' =>
        -- c < p = one is impossible when c = successor c'
        rw [hp_one] at hc
        exact absurd hc (not_succ_lt_one c')
    · -- r = successor k branch
      intro k hr ha hlt
      subst hr
      cases c with
      | zero =>
        cases a' with
        | zero =>
          -- a = one; c = zero; r = successor k; result (successor k, zero)
          have hb := hsucc k rfl
          have horig_p : (successor zero : Peano) +
              subtract p (successor zero) (Or.inl hlt) = p :=
            one_add_subtract_one p hlt
          show (successor zero + subtract p (successor zero) (Or.inl hlt) =
                  power (successor k) e (Or.inr he) + zero) ∧
               (successor zero + subtract p (successor zero) (Or.inl hlt) <
                  power (successor k).successor e (Or.inr he))
          constructor
          · rw [horig_p, hp, hb, add_zero]
          · have step : p < power (successor k).successor e (Or.inr he) := by
              rw [hp, hb]; exact rootWithRemainderAux_advance_lt e (successor k) he
            exact lt_of_le_lt (Or.inr horig_p) step
        | successor a_inner =>
          -- advance: a = succ(succ a_inner); c = zero; r = successor k
          have hb : b = successor k := hsucc k rfl
          have hlt_advance : p < power b.successor e (Or.inr he) := by
            rw [hp]; exact rootWithRemainderAux_advance_lt e b he
          have hle_advance : p ≤ power b.successor e (Or.inr he) := Or.inl hlt_advance
          have hgap_ne : subtract (power b.successor e (Or.inr he)) p hle_advance ≠ zero :=
            subtract_ne_zero_of_lt hle_advance hlt_advance
          have hp_ne : p ≠ zero := by
            intro h0; rw [h0] at hlt; exact not_lt_zero one hlt
          have hlt_gap : subtract (power b.successor e (Or.inr he)) p (Or.inl hlt_advance) <
              power b.successor e (Or.inr he) :=
            rootWithRemainderAux_gap_lt_p hlt_advance hp_ne
          have hlt_inner : (predecessor (subtract (power b.successor e (Or.inr he)) p hle_advance)
              hgap_ne).successor < power b.successor e (Or.inr he) := by
            rw [successor_predecessor]; exact hlt_gap
          have ih_pair := ih (successor b)
            (predecessor (subtract (power b.successor e (Or.inr he)) p hle_advance) hgap_ne)
            (power b.successor e (Or.inr he)) b.successor
            (lt_of_lt_of_le (predecessor_lt _ hgap_ne) (subtract_le_self _ _ hle_advance))
            rfl
            (fun h => nomatch h)
            (fun k' hk' => by injection hk' with hk'; rw [← hk'])
            (fun k' hk' hle' => by
              injection hk' with hk'; subst hk'
              rw [successor_predecessor]
              exact Or.inr (subtract_eq_of_eq hle_advance hle' rfl hp))
          obtain ⟨_, ih_succ⟩ := ih_pair
          have ih_at := ih_succ b rfl (successor_ne_zero a_inner) hlt_inner
          simp only [rootWithRemainderAux]
          have horig_eq : rootWithRemainderOrig (successor a_inner)
              (predecessor (subtract (power b.successor e (Or.inr he)) p hle_advance) hgap_ne)
              (power b.successor e (Or.inr he)) hlt_inner =
              rootWithRemainderOrig (successor (successor a_inner)) zero p hlt := by
            simp only [rootWithRemainderOrig]
            have key : subtract (power b.successor e (Or.inr he))
                ((predecessor (subtract (power b.successor e (Or.inr he)) p hle_advance)
                  hgap_ne).successor)
                (Or.inl hlt_inner) = p := by
              rw [subtract_eq_of_eq (Or.inl hlt_inner) (Or.inl hlt_gap) rfl
                    (successor_predecessor _ hgap_ne)]
              rcases subtract_subtract_cancel (power b.successor e (Or.inr he)) p hlt_advance hp_ne
                with ⟨h2, hcancel⟩
              rw [subtract_eq_of_eq (Or.inl hlt_gap) h2 rfl rfl]
              exact hcancel
            rw [key]
            exact (succ_add_subtract_one (successor a_inner) p hlt).symm
          rw [← horig_eq]
          exact ih_at
      | successor c' =>
        have hlt' : successor c' < p := lt_of_succ_lt hlt
        cases a' with
        | zero =>
          -- a = one; c = successor c'; r = successor k: remainder case
          simp only [rootWithRemainderAux, rootWithRemainderOrig]
          have hlt_gap : power k e (Or.inr he) < p := by
            rw [hp, hsucc k rfl]; exact rootWithRemainderAux_advance_lt e k he
          have hle_gap : power k e (Or.inr he) ≤ p := Or.inl hlt_gap
          have hc_gap : successor (successor c') ≤
              subtract p (power k e (Or.inr he)) hle_gap :=
            hbound k rfl hle_gap
          have hle_c : successor c' ≤ subtract p (power k e (Or.inr he)) hle_gap :=
            le_of_succ_le hc_gap
          have hlt_c' : successor c' < subtract p (power k e (Or.inr he)) (Or.inl hlt_gap) := by
            cases hc_gap with
            | inl h => exact lt_trans LessThan.base h
            | inr h => rw [← h]; exact LessThan.base
          have hk_ne : k ≠ zero := by
            intro hk0
            subst hk0
            have hb1 : b = one := hsucc zero rfl
            rw [hp, hb1, one_power] at hlt
            exact not_succ_lt_one (successor c') hlt
          have hpow_k_ne : power k e (Or.inr he) ≠ zero :=
            power_ne_zero_of_base_ne_zero k e (Or.inr he) hk_ne
          have horig_val : (successor zero : Peano) +
              subtract p (successor (successor c')) (Or.inl hlt) =
              subtract p (successor c') (Or.inl hlt') :=
            (subtract_succ_add_one p (successor c') hlt).symm
          constructor
          · rw [horig_val]
            exact subtract_eq_add_subtract_gap p (power k e (Or.inr he))
                (successor c') hlt_gap hpow_k_ne hlt_c'
          · rw [horig_val]
            have hp' : p = power k.successor e (Or.inr he) := by rw [hp, hsucc k rfl]
            rw [← hp']
            exact subtract_lt_right p (successor c') hlt' (successor_ne_zero c')
        | successor a_inner =>
          -- decrement: a = succ(succ a_inner); c = successor c'; r = successor k
          have ha_ne : successor a_inner ≠ zero := successor_ne_zero a_inner
          have ih_pair := ih (successor k) c' p b (lt_of_succ_lt hc) hp hzero hsucc
            (fun k' hk' hle' => le_of_succ_le (hbound k' hk' hle'))
          obtain ⟨_, ih_succ⟩ := ih_pair
          have ih_at := ih_succ k rfl ha_ne hlt'
          simp only [rootWithRemainderAux]
          have horig_eq : rootWithRemainderOrig (successor a_inner) c' p hlt' =
              rootWithRemainderOrig (successor (successor a_inner)) (successor c') p hlt := by
            simp only [rootWithRemainderOrig]
            exact (add_subtract_succ_step (successor a_inner) p (successor c') hlt).symm
          rw [← horig_eq]
          exact ih_at

theorem rootWithRemainder_lt (a e : Peano) (he : e ≠ zero) (b r : Peano)
    (h : rootWithRemainder a e he = (b, r)) :
    a < power b.successor e (Or.inr he) := by
  have key := (rootWithRemainderAux_correct e he a zero zero one one
    (zero_lt_succ zero) (by rw [one_power e (Or.inr he)])
    (fun _ => rfl) (fun _ hk => by cases hk) (fun _ hk => by cases hk)).1 rfl
  simp only [rootWithRemainder] at h
  have hb : (rootWithRemainderAux a e he zero zero one one
      (zero_lt_succ zero) (by rw [one_power e (Or.inr he)])
      (fun _ => rfl) (fun _ hk => by cases hk) (fun _ hk => by cases hk)).1 = b :=
    congrArg Prod.fst h
  rw [← hb]; exact key.2

theorem rootWithRemainder_add (a e : Peano) (he : e ≠ zero) (b r : Peano)
    (h : rootWithRemainder a e he = (b, r)) :
    a = power b e (Or.inr he) + r := by
  have key := (rootWithRemainderAux_correct e he a zero zero one one
    (zero_lt_succ zero) (by rw [one_power e (Or.inr he)])
    (fun _ => rfl) (fun _ hk => by cases hk) (fun _ hk => by cases hk)).1 rfl
  simp only [rootWithRemainder] at h
  have hb : (rootWithRemainderAux a e he zero zero one one
      (zero_lt_succ zero) (by rw [one_power e (Or.inr he)])
      (fun _ => rfl) (fun _ hk => by cases hk) (fun _ hk => by cases hk)).1 = b :=
    congrArg Prod.fst h
  have hr : (rootWithRemainderAux a e he zero zero one one
      (zero_lt_succ zero) (by rw [one_power e (Or.inr he)])
      (fun _ => rfl) (fun _ hk => by cases hk) (fun _ hk => by cases hk)).2 = r :=
    congrArg Prod.snd h
  rw [← hb, ← hr]; exact key.1

theorem rootWithRemainder_succ_power (a e : Peano) (he : e ≠ zero) (b r : Peano)
    (h : Power e a) (hres : rootWithRemainder a e he = (b, successor r)) : False := by
  have ha := rootWithRemainder_add a e he b (successor r) hres
  have hlt := rootWithRemainder_lt a e he b (successor r) hres
  rcases h with ⟨c, hc, hc_pow⟩
  have hc' : c ≠ zero ∨ e ≠ zero := Or.inr he
  have hc_pow' : power c e hc' = a := by
    calc power c e hc' = power c e hc := rfl
         _ = a := hc_pow
  have hlt_b : power b e (Or.inr he) < power c e hc' := by
    have : power b e (Or.inr he) < a := by
      rw [ha]
      exact lt_add_of_right_ne_zero (power b e (Or.inr he)) (successor r) (successor_ne_zero r)
    rwa [← hc_pow'] at this
  have hlt_c : power c e hc' < power b.successor e (Or.inr he) := by
    rwa [← hc_pow'] at hlt
  have hbc : b < c := by
    cases trichotomy b c with
    | first h => exact h
    | second h =>
      subst h
      exact False.elim (not_lt_self _ hlt_b)
    | third h =>
      exact False.elim (not_lt_of_lt hlt_b (lt_power he h hc' (Or.inr he)))
  have hcs : c < b.successor := by
    cases trichotomy c b.successor with
    | first h => exact h
    | second h =>
      subst h
      exact False.elim (not_lt_self _ hlt_c)
    | third h =>
      exact False.elim (not_lt_of_lt hlt_c (lt_power he h (Or.inr he) hc'))
  exact not_lt_self b (lt_of_lt_of_le hbc (le_of_lt_succ hcs))

def root (e x : Peano) (h : e ≠ zero ∧ Power e x) : Peano :=
  match hres : rootWithRemainder x e h.1 with
  | (b, zero) => b
  | (b, successor r) => False.elim (rootWithRemainder_succ_power x e h.1 b r h.2 hres)

theorem root_is_power (e x : Peano) (h : e ≠ zero ∧ Power e x) :
    ∃ hroot : root e x h ≠ zero ∨ e ≠ zero,
      power (root e x h) e hroot = x := by
  exists Or.inr h.1
  unfold root
  split
  next b hres =>
    have hadd := rootWithRemainder_add x e h.1 b zero hres
    rw [add_zero] at hadd
    exact hadd.symm
  next b r hres =>
    exact False.elim (rootWithRemainder_succ_power x e h.1 b r h.2 hres)

theorem root_of_power_eq_self (e x : Peano) (h : e ≠ zero) (h2 : x ≠ zero ∨ e ≠ zero) :
    ∃ h3, root e (power x e h2) h3 = x := by
  let h3 := root_power_precondition e x h h2
  exists h3
  rcases root_is_power e (power x e h2) h3 with ⟨hroot, hpow⟩
  exact power_injective_base (root e (power x e h2) h3) x e h hroot h2 hpow

theorem exists_root_of_tryRoot {x y z : Peano} (h : tryRoot x y = some z) :
    ∃ h', root x y h' = z := by
  cases x with
  | zero =>
    simp only [tryRoot] at h
    cases h
  | successor x' =>
    have hx : successor x' ≠ zero := successor_ne_zero x'
    have hres : rootWithRemainder y (successor x') hx = (z, zero) := by
      simp only [tryRoot] at h
      split at h
      · next b hb =>
        injection h with hz
        rw [← hz]
        exact hb
      · next _ =>
        cases h
    have hadd := rootWithRemainder_add y (successor x') hx z zero hres
    rw [add_zero] at hadd
    have hpow : Power (successor x') y := ⟨z, Or.inr hx, hadd.symm⟩
    refine ⟨⟨hx, hpow⟩, ?_⟩
    unfold root
    split
    · next b hres' =>
      have heq : (b, (zero : Peano)) = (z, zero) := by
        rw [← hres', hres]
      exact congrArg Prod.fst heq
    · next b r hres' =>
      exact False.elim (rootWithRemainder_succ_power y (successor x') hx b r hpow hres')

theorem tryRoot_eq_some_root (x y : Peano) (h : x ≠ zero ∧ Power x y) :
    tryRoot x y = some (root x y h) := by
  cases x with
  | zero => exact False.elim (h.1 rfl)
  | successor x' =>
    unfold root
    split
    · next b hres =>
      have hres' : rootWithRemainder y (successor x') (successor_ne_zero x') = (b, zero) := by
        rw [Subsingleton.elim (successor_ne_zero x') h.1]
        exact hres
      change (match rootWithRemainder y (successor x') (successor_ne_zero x') with
        | (b, zero) => some b
        | (_, successor _) => none) = some b
      rw [hres']
    · next b r hres =>
      exact False.elim (rootWithRemainder_succ_power y (successor x') h.1 b r h.2 hres)

theorem tryRoot_of_exists_root {x y z : Peano} (h : ∃ h', root x y h' = z) :
    tryRoot x y = some z := by
  rcases h with ⟨h', hz⟩
  rw [← hz]
  exact tryRoot_eq_some_root x y h'

theorem le_of_lt {a b : Peano} (h : a < b) : a ≤ b := Or.inl h

theorem isDivisibleCorrect (a b : Peano) : Divisible a b ↔ isDivisible a b := by
  unfold Divisible isDivisible
  apply Iff.intro
  · intro h
    rcases h with ⟨hb, c, hc⟩
    cases b with
    | zero => exact False.elim (hb rfl)
    | successor b' =>
      have hres := divideWithRemainder_eq_of_mul a b'.successor
        (successor_ne_zero b') c hc.symm
      simp [hres]
  · intro h
    cases b with
    | zero => contradiction
    | successor b' =>
      match hres : divideWithRemainder a b'.successor (successor_ne_zero b') with
      | (q, zero) =>
        have hcorr := divideWithRemainder_correct a b'.successor
          (successor_ne_zero b') q zero hres
        exact ⟨successor_ne_zero b', q, by rw [hcorr, add_zero]⟩
      | (_, successor _) =>
        simp [hres] at h

def Even (a : Peano) : Prop := Divisible a two

def Odd (a : Peano) : Prop := ¬ Even a

def isEven : Peano → Bool
  | zero => true
  | successor n => !isEven n

def isOdd (a : Peano) : Bool := !isEven a

theorem isEven_successor (x : Peano) (h : Even x) : Odd (successor x) := by
  unfold Odd
  intro hcontra
  unfold Even Divisible at h hcontra
  rcases h with ⟨h2, c, hc⟩
  rcases hcontra with ⟨h2', c', hc'⟩
  have hc_symm : x = two * c := hc.symm
  have hc'_symm : successor x = two * c' := hc'.symm
  rw [hc_symm] at hc'_symm
  clear hc hc_symm hc' x
  induction c generalizing c' with
  | zero =>
    rw [multiply_zero] at hc'_symm
    cases c' with
    | zero =>
      rw [multiply_zero] at hc'_symm
      cases hc'_symm
    | successor c'' =>
      rw [multiply_successor] at hc'_symm
      have h3 : successor zero = two * c'' + successor one := hc'_symm
      rw [add_successor] at h3
      cases h3
  | successor c_prev ih =>
    cases c' with
    | zero =>
      rw [multiply_zero] at hc'_symm
      cases hc'_symm
    | successor c'_prev =>
      rw [multiply_successor, multiply_successor] at hc'_symm
      have h4 : successor (two * c_prev + two) = two * c'_prev + two := hc'_symm
      have h5 : successor (two * c_prev + two) = successor (two * c_prev) + two := by
        have h_add : successor (two * c_prev) + two = successor (successor (two * c_prev) + one) := rfl
        rw [h_add]
        have h_add2 : two * c_prev + two = successor (two * c_prev + one) := rfl
        rw [h_add2]
        have h_add3 : successor (two * c_prev + one) = successor (two * c_prev) + one := rfl
        rw [h_add3]
      rw [h5] at h4
      have h6 : successor (two * c_prev) = two * c'_prev := add_right_cancel _ _ _ h4
      exact ih c'_prev h6

theorem isEven_zero : Even zero := by
  unfold Even Divisible
  apply And.intro
  · intro hz; cases hz
  · exists zero

theorem isEven_add_two (x : Peano) (h : Even x) : Even (successor (successor x)) := by
  unfold Even Divisible at h ⊢
  rcases h with ⟨h_ne, c, hc⟩
  apply And.intro
  · exact h_ne
  · exists successor c
    have hc_symm : x = two * c := hc.symm
    rw [hc_symm]
    rw [multiply_successor]
    rfl

theorem isEven_or_isEven_successor (x : Peano) : Even x ∨ Even (successor x) := by
  induction x with
  | zero => exact Or.inl isEven_zero
  | successor x' ih =>
    cases ih with
    | inl h_even => exact Or.inr (isEven_add_two x' h_even)
    | inr h_even_succ => exact Or.inl h_even_succ

theorem isEven_successor_of_isOdd (x : Peano) (h : Odd x) : Even (successor x) := by
  have h_or := isEven_or_isEven_successor x
  cases h_or with
  | inl h_even =>
    unfold Odd at h
    contradiction
  | inr h_even_succ =>
    exact h_even_succ

theorem isOdd_predecessor (x : Peano) (h : x ≠ zero) (h2 : Even x) : Odd (predecessor x h) := by
  cases x with
  | zero => contradiction
  | successor x' =>
    intro h_even_x'
    have h_odd_succ := isEven_successor x' h_even_x'
    exact h_odd_succ h2

theorem isEven_predecessor_of_isOdd (x : Peano) (h : Odd x) : ∃ h2, Even (predecessor x h2) := by
  cases x with
  | zero =>
    have hz : Even zero := isEven_zero
    contradiction
  | successor x' =>
    have h2 : successor x' ≠ zero := by intro h; contradiction
    exists h2
    change Even x'
    have h_or := isEven_or_isEven_successor x'
    cases h_or with
    | inl h_even => exact h_even
    | inr h_even_succ =>
      unfold Odd at h
      contradiction

theorem even_or_odd (x : Peano) : Even x ∨ Odd x := by
  induction x with
  | zero => exact Or.inl isEven_zero
  | successor x' ih =>
    cases ih with
    | inl h_even =>
      exact Or.inr (isEven_successor x' h_even)
    | inr h_odd =>
      exact Or.inl (isEven_successor_of_isOdd x' h_odd)

theorem even_succ_iff (x : Peano) : Even (successor x) ↔ Odd x := by
  constructor
  · intro h
    have hor := even_or_odd x
    cases hor with
    | inl h_even =>
      have h_odd_succ := isEven_successor x h_even
      unfold Odd at h_odd_succ
      exact False.elim (h_odd_succ h)
    | inr h_odd => exact h_odd
  · intro h_odd
    exact isEven_successor_of_isOdd x h_odd

theorem isEven_correct (x : Peano) : Even x ↔ isEven x := by
  induction x with
  | zero =>
    constructor
    · intro h
      simp [isEven]
    · intro h
      exact isEven_zero
  | successor x ih =>
    constructor
    · intro h
      have h_odd : Odd x := (even_succ_iff x).mp h
      simp [isEven]
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

theorem even_mul_of_even_left {a b : Peano} (ha : Even a) : Even (a * b) := by
  unfold Even Divisible at ha ⊢
  rcases ha with ⟨hne, c, hc⟩
  exact ⟨hne, c * b, by rw [← multiply_associative, hc]⟩

theorem even_add_left_iff (a b : Peano) (ha : Even a) : Even (a + b) ↔ Even b := by
  constructor
  · intro hab
    unfold Even at ha hab ⊢
    have hle : a ≤ a + b := le_add_self_left a b
    have hdiv := divide_subtract_h (a + b) a two hab ha hle
    have h_eq : subtract (a + b) a hle = b := by
      apply add_right_cancel a
      rw [subtract_add_cancel (a + b) a hle, add_commutative]
    rwa [h_eq] at hdiv
  · intro hb
    unfold Even at ha hb ⊢
    exact divide_add_h a b two ha hb

theorem even_ten : Even ten := by
  unfold Even Divisible
  exact ⟨two_ne_zero, five, rfl⟩

def fromOrdinal : OrdinalNatural.Peano → Peano
  | OrdinalNatural.Peano.one => one
  | OrdinalNatural.Peano.successor x => (fromOrdinal x).successor

def toOrdinal (x : Peano) (h : x ≠ zero) : OrdinalNatural.Peano :=
  match x with
  | zero => False.elim (h rfl)
  | successor x' =>
    match x' with
    | zero => OrdinalNatural.Peano.one
    | successor x'' => OrdinalNatural.Peano.successor (toOrdinal x''.successor (by simp))

theorem fromOrdinal_toOrdinal (x : Peano) (h : x ≠ zero) : fromOrdinal (toOrdinal x h) = x := by
  match x with
  | zero => contradiction
  | successor x' =>
    match x' with
    | zero => rfl
    | successor x'' =>
      have h1 : successor x'' ≠ zero := by simp
      have ih := fromOrdinal_toOrdinal (successor x'') h1
      simp [toOrdinal, fromOrdinal, ih]

theorem fromOrdinal_ne_zero (x : OrdinalNatural.Peano) : fromOrdinal x ≠ zero := by
  match x with
  | OrdinalNatural.Peano.one => intro h; contradiction
  | OrdinalNatural.Peano.successor x' => intro h; contradiction

theorem fromOrdinal_add (x y : OrdinalNatural.Peano) :
    fromOrdinal (x + y) = fromOrdinal x + fromOrdinal y := by
  induction y with
  | one =>
    rw [OrdinalNatural.Peano.add_one]
    change successor (fromOrdinal x) = fromOrdinal x + one
    rw [one, add_successor, add_zero]
  | successor y ih =>
    rw [OrdinalNatural.Peano.add_succ]
    change successor (fromOrdinal (x + y)) =
      fromOrdinal x + successor (fromOrdinal y)
    rw [add_successor, ih]

theorem fromOrdinal_multiply (x y : OrdinalNatural.Peano) :
    fromOrdinal (x * y) = fromOrdinal x * fromOrdinal y := by
  induction y with
  | one =>
    rw [OrdinalNatural.Peano.multiply_one]
    change fromOrdinal x = fromOrdinal x * one
    rw [multiply_one]
  | successor y ih =>
    rw [OrdinalNatural.Peano.multiply_succ, fromOrdinal_add, ih]
    change fromOrdinal x * fromOrdinal y + fromOrdinal x =
      fromOrdinal x * (fromOrdinal y).successor
    rw [multiply_successor]

theorem fromOrdinal_power (x y : OrdinalNatural.Peano) :
    fromOrdinal (x ^ y) =
      power (fromOrdinal x) (fromOrdinal y) (Or.inl (fromOrdinal_ne_zero x)) := by
  induction y with
  | one =>
    rw [OrdinalNatural.Peano.power_one]
    change fromOrdinal x =
      power (fromOrdinal x) one (Or.inl (fromOrdinal_ne_zero x))
    rw [power_one_eq_self]
  | successor y ih =>
    rw [OrdinalNatural.Peano.power_succ, fromOrdinal_multiply, ih]
    obtain ⟨h2, hs⟩ := power_successor
      (fromOrdinal x) (fromOrdinal y) (Or.inl (fromOrdinal_ne_zero x))
    exact hs.symm.trans (eq_rec_power_exponent
      (fromOrdinal x)
      (fromOrdinal y).successor
      (fromOrdinal y).successor rfl h2
      (Or.inl (fromOrdinal_ne_zero x)))

theorem toOrdinal_successor (x : Peano) (h : successor x ≠ zero) (h2 : x ≠ zero) :
  toOrdinal (successor x) h = OrdinalNatural.Peano.successor (toOrdinal x h2) := by
  match x with
  | zero => contradiction
  | successor x' =>
    simp [toOrdinal]

theorem toOrdinal_fromOrdinal_helper (x : OrdinalNatural.Peano) (h : fromOrdinal x ≠ zero) : toOrdinal (fromOrdinal x) h = x := by
  match x with
  | OrdinalNatural.Peano.one => rfl
  | OrdinalNatural.Peano.successor x' =>
    have h1 : fromOrdinal x' ≠ zero := fromOrdinal_ne_zero x'
    have ih := toOrdinal_fromOrdinal_helper x' h1
    change toOrdinal (successor (fromOrdinal x')) h = _
    rw [toOrdinal_successor (fromOrdinal x') h h1]
    rw [ih]

theorem toOrdinal_fromOrdinal (x : OrdinalNatural.Peano) : ∃ h, toOrdinal (fromOrdinal x) h = x := by
  have h := fromOrdinal_ne_zero x
  exists h
  exact toOrdinal_fromOrdinal_helper x h

@[simp]
theorem fromOrdinal_toNat (o : OrdinalNatural.Peano) : toNat (fromOrdinal o) = o.toNat := by
  induction o with
  | one => rfl
  | successor o' ih =>
    simp [OrdinalNatural.Peano.toNat, fromOrdinal, toNat, ih]

theorem toOrdinal_congr {a b : Peano} (h_eq : a = b)
  (ha : a ≠ zero) (hb : b ≠ zero) :
  toOrdinal a ha = toOrdinal b hb := by
  cases h_eq
  rfl

theorem eq_of_fromOrdinal_eq {x y : OrdinalNatural.Peano}
  (h : fromOrdinal x = fromOrdinal y) : x = y := by
  obtain ⟨hx_nonzero, hx⟩ := toOrdinal_fromOrdinal x
  obtain ⟨hy_nonzero, hy⟩ := toOrdinal_fromOrdinal y
  exact hx.symm.trans ((toOrdinal_congr h hx_nonzero hy_nonzero).trans hy)

/-- `fromOrdinal` is monotone. -/
theorem fromOrdinal_le_of_lt {a b : OrdinalNatural.Peano} (h : a < b) :
    fromOrdinal a ≤ fromOrdinal b := by
  induction h with
  | base =>
    exact Or.inl LessThan.base
  | step _ ih =>
    exact le_trans ih (Or.inl LessThan.base)

theorem toOrdinal_lt_of_lt {a b : Peano} (ha : a ≠ zero) (hb : b ≠ zero)
  (h : a < b) : toOrdinal a ha < toOrdinal b hb := by
  induction h with
  | base =>
      rw [toOrdinal_successor a hb ha]
      exact OrdinalNatural.Peano.LessThan.base
  | step hlt ih =>
      rename_i c
      have hc : c ≠ zero := by
        intro hzero
        rw [hzero] at hlt
        exact not_lt_zero a hlt
      rw [toOrdinal_successor c hb hc]
      exact OrdinalNatural.Peano.LessThan.step (ih hc)

theorem lt_of_toOrdinal_lt {a b : Peano} (ha : a ≠ zero) (hb : b ≠ zero)
  (h : toOrdinal a ha < toOrdinal b hb) : a < b := by
  cases trichotomy_or a b with
  | inl hlt => exact hlt
  | inr hrest =>
      cases hrest with
      | inl heq =>
          have h_eq : toOrdinal a ha = toOrdinal b hb :=
            toOrdinal_congr heq ha hb
          rw [h_eq] at h
          exact False.elim (OrdinalNatural.Peano.not_lt_self _ h)
      | inr hgt =>
          exact False.elim (OrdinalNatural.Peano.not_lt_self _
            (OrdinalNatural.Peano.lt_trans h (toOrdinal_lt_of_lt hb ha hgt)))

theorem eq_zero_of_add_eq_zero_l {n m : Peano} (h : n + m = zero) : n = zero := by
  cases n with
  | zero => rfl
  | successor n' =>
    cases m with
    | zero => cases h
    | successor m' => cases h

theorem eq_zero_of_add_eq_zero_r {n m : Peano} (h : n + m = zero) : m = zero := by
  cases n with
  | zero =>
    have h1 : zero + m = m := zero_add m
    have h2 : m = zero + m := h1.symm
    have h3 : zero + m = zero := h
    rw [h3] at h2
    exact h2
  | successor n' =>
    cases m with
    | zero => rfl
    | successor m' => cases h

theorem succ_le_of_lt {a b : Peano} (h : a < b) : a.successor ≤ b := by
  induction h with
  | base => exact Or.inr rfl
  | step hlt ih =>
    cases ih with
    | inl h1 => exact Or.inl (LessThan.step h1)
    | inr h2 =>
      rw [h2]
      exact Or.inl LessThan.base

theorem lt_of_succ_le {a b : Peano} (h : a.successor ≤ b) : a < b := by
  cases h with
  | inl hlt => exact lt_of_succ_lt hlt
  | inr heq =>
    rw [← heq]
    exact LessThan.base

theorem isLessThan_true_implies_le {a b : Peano} (h : isLessThan a b = true) : a ≤ b := by
  have h_lt : a < b := (isLessThan_eq_true_iff_lt a b).mp h
  exact Or.inl h_lt

theorem isLessThan_false_implies_le {a b : Peano} (h : isLessThan a b = false) : b ≤ a := by
  have h_not_lt : ¬ (a < b) := (isLessThan_eq_false_iff_not_lt a b).mp h
  have tri := trichotomy_or a b
  cases tri with
  | inl h_lt => exact False.elim (h_not_lt h_lt)
  | inr h_eq_or_gt =>
    cases h_eq_or_gt with
    | inl h_eq => exact Or.inr h_eq.symm
    | inr h_gt => exact Or.inl h_gt

theorem zero_lt_ten : zero < ten := by
  apply LessThan.step
  apply LessThan.step
  apply LessThan.step
  apply LessThan.step
  apply LessThan.step
  apply LessThan.step
  apply LessThan.step
  apply LessThan.step
  apply LessThan.step
  apply LessThan.base

theorem one_lt_ten : one < ten := by
  apply LessThan.step
  apply LessThan.step
  apply LessThan.step
  apply LessThan.step
  apply LessThan.step
  apply LessThan.step
  apply LessThan.step
  apply LessThan.step
  apply LessThan.base

theorem nine_lt_ten : nine < ten := LessThan.base

theorem le_lt_trans {a b c : Peano} (hab : a ≤ b) (hbc : b < c) : a < c := by
  cases hab with
  | inl hab_lt => exact lt_trans hab_lt hbc
  | inr hab_eq =>
    rw [hab_eq]
    exact hbc

theorem add_lt_add_right {a b : Peano} (h : a < b) (c : Peano) :
  a + c < b + c := by
  induction c with
  | zero => exact h
  | successor c' ih =>
    change (a + c').successor < (b + c').successor
    exact succ_lt_succ ih

theorem add_lt_add_left {a b : Peano} (h : a < b) (c : Peano) :
  c + a < c + b := by
  rw [add_commutative c a, add_commutative c b]
  exact add_lt_add_right h c

theorem add_le_add_right {a b : Peano} (h : a ≤ b) (c : Peano) :
  a + c ≤ b + c := by
  induction c with
  | zero => exact h
  | successor c' ih =>
    change (a + c').successor ≤ (b + c').successor
    exact succ_le_succ ih

theorem add_le_add_left {a b : Peano} (h : a ≤ b) (c : Peano) :
  c + a ≤ c + b := by
  rw [add_commutative c a, add_commutative c b]
  exact add_le_add_right h c

theorem add_lt_cancel_right {a b c : Peano} (h : a + c < b + c) : a < b := by
  induction c with
  | zero => exact h
  | successor c' ih =>
    apply ih
    exact lt_of_succ_lt_succ h

theorem subtract_lt_of_lt_add {x y z : Peano}
  (h_le : y ≤ x) (h_lt : x < y + z) :
  subtract x y h_le < z := by
  have h_cancel := subtract_add_cancel x y h_le
  apply add_lt_cancel_right (c := y)
  rw [h_cancel]
  rw [add_commutative z y]
  exact h_lt

-- 10^n
def tenPow : Peano → Peano
  | .zero => one
  | .successor n => ten * tenPow n

theorem tenPow_ne_zero (n : Peano) :
    tenPow n ≠ zero := by
  induction n with
  | zero => exact successor_ne_zero zero
  | successor n ih =>
    exact multiply_ne_zero ten (tenPow n)
      (successor_ne_zero nine) ih

theorem tenPow_pos (n : Peano) : zero < tenPow n :=
  zero_lt_of_ne_zero _ (tenPow_ne_zero n)

theorem tenPow_add_one (n : Peano) :
    tenPow (n + one) = ten * tenPow n := by
  have h : n + one = n.successor := by
    rw [add_commutative, one, successor_add, zero_add]
  simp only [h, tenPow]

theorem tenPow_lt_succ (n : Peano) : tenPow n < tenPow n.successor := by
  show tenPow n < ten * tenPow n
  have h1 : tenPow n * one < tenPow n * ten :=
    multiply_lt_of_lt_left (tenPow n) (tenPow_ne_zero n) one_lt_ten
  rw [multiply_one,
      multiply_commutative (tenPow n) ten] at h1
  exact h1

theorem tenPow_monotone {m n : Peano} (h : m ≤ n) : tenPow m ≤ tenPow n := by
  cases h with
  | inl hlt =>
    induction hlt with
    | base => exact Or.inl (tenPow_lt_succ _)
    | step _ ih => exact le_trans ih (Or.inl (tenPow_lt_succ _))
  | inr heq => subst heq; exact Or.inr rfl

theorem add_le_cancel_left {a b c : Peano} (h : a + b ≤ a + c) : b ≤ c := by
  cases h with
  | inl hlt =>
    rw [add_commutative a b,
        add_commutative a c] at hlt
    exact Or.inl (add_lt_cancel_right hlt)
  | inr heq =>
    exact Or.inr (add_left_cancel a b c heq)

-- a * c ≤ b * c when a ≤ b
theorem multiply_le_mul_left {a b : Peano} (h : a ≤ b)
    (c : Peano) : a * c ≤ b * c := by
  cases c with
  | zero =>
    simp only [multiply_zero]
    exact Or.inr rfl
  | successor c' =>
    cases h with
    | inl hlt =>
      have hmul := multiply_lt_of_lt_left c'.successor
        (successor_ne_zero c') hlt
      rw [multiply_commutative c'.successor a,
          multiply_commutative c'.successor b] at hmul
      exact Or.inl hmul
    | inr heq =>
      rw [heq]
      exact Or.inr rfl

theorem add_left_commutative (a b c : Peano) :
  a + (b + c) = b + (a + c) := by
  rw [←add_associative, add_commutative a b, add_associative]

theorem add_pair_swap (a b c d : Peano) :
  (a + c) + (b + d) = (a + b) + (c + d) := by
  simp only [add_commutative, add_left_commutative]

theorem add_right_swap (a b c : Peano) :
  a + (b + c) = a + c + b := by
  simp only [add_commutative, add_left_commutative]

theorem add_right_commutative (a b c : Peano) :
  a + b + c = a + c + b := by
  simp only [add_commutative, add_left_commutative]

theorem cardinal_not_lt_of_le {a b : Peano} (h : a ≤ b) : ¬ b < a := by
  intro hlt
  exact not_lt_self b (lt_of_lt_of_le hlt h)

theorem tenPow_add (m n : Peano) :
    tenPow (m + n) = tenPow m * tenPow n := by
  induction n with
  | zero =>
    rw [add_zero, tenPow, multiply_one]
  | successor n ih =>
    rw [add_successor, tenPow, ih, tenPow, ←multiply_associative, multiply_commutative ten _, multiply_associative]


/-- Rewrite form of `power_successor` with matching side conditions. -/
theorem power_succ_eq (x e : Peano) (hx : x ≠ zero) :
    power x e.successor (Or.inl hx) = power x e (Or.inl hx) * x := by
  obtain ⟨h2, hs⟩ := power_successor x e (Or.inl hx)
  exact (eq_rec_power_exponent x e.successor e.successor rfl h2 (Or.inl hx)).symm.trans hs

theorem power_add_eq (x y z : Peano) (hx : x ≠ zero) :
    power x (y + z) (Or.inl hx) =
      power x y (Or.inl hx) * power x z (Or.inl hx) := by
  obtain ⟨h3, heq⟩ := power_add x y z (Or.inl hx) (Or.inl hx)
  exact (eq_rec_power_exponent x (y + z) (y + z) rfl h3 (Or.inl hx)).symm.trans heq

theorem power_mul_eq (x y z : Peano) (hx : x ≠ zero) :
    power x (y * z) (Or.inl hx) =
      power (power x y (Or.inl hx)) z
        (Or.inl (power_ne_zero_of_base_ne_zero x y (Or.inl hx) hx)) := by
  obtain ⟨h3, heq⟩ := power_multiply x y z (Or.inl hx)
    (Or.inl (power_ne_zero_of_base_ne_zero x y (Or.inl hx) hx))
  exact (eq_rec_power_exponent x (y * z) (y * z) rfl h3 (Or.inl hx)).symm.trans heq

theorem power_two_eq (x : Peano) (hx : x ≠ zero) :
    power x two (Or.inl hx) = x * x := by
  have h := power_succ_eq x one hx
  change power x two (Or.inl hx) = power x one (Or.inl hx) * x at h
  rw [h, power_one_eq_self]

theorem power_three_eq (x : Peano) (hx : x ≠ zero) :
    power x three (Or.inl hx) = (x * x) * x := by
  have h := power_succ_eq x two hx
  change power x three (Or.inl hx) = power x two (Or.inl hx) * x at h
  rw [h, power_two_eq x hx]

theorem power_four_eq (x : Peano) (hx : x ≠ zero) :
    power x four (Or.inl hx) = (x * x) * (x * x) := by
  have hadd := power_add_eq x two two hx
  have hsum : two + two = four := rfl
  rw [hsum] at hadd
  rw [hadd, power_two_eq x hx]

theorem power_five_eq (x : Peano) (hx : x ≠ zero) :
    power x five (Or.inl hx) = ((x * x) * (x * x)) * x := by
  have h := power_succ_eq x four hx
  change power x five (Or.inl hx) = power x four (Or.inl hx) * x at h
  rw [h, power_four_eq x hx]

theorem power_six_eq (x : Peano) (hx : x ≠ zero) :
    power x six (Or.inl hx) = ((x * x) * (x * x)) * (x * x) := by
  have hadd := power_add_eq x four two hx
  have hsum : four + two = six := rfl
  rw [hsum] at hadd
  rw [hadd, power_four_eq x hx, power_two_eq x hx]

theorem power_seven_eq (x : Peano) (hx : x ≠ zero) :
    power x seven (Or.inl hx) = (((x * x) * (x * x)) * (x * x)) * x := by
  have h := power_succ_eq x six hx
  change power x seven (Or.inl hx) = power x six (Or.inl hx) * x at h
  rw [h, power_six_eq x hx]

theorem power_eight_eq (x : Peano) (hx : x ≠ zero) :
    power x eight (Or.inl hx) = ((x * x) * (x * x)) * ((x * x) * (x * x)) := by
  have hadd := power_add_eq x four four hx
  have hsum : four + four = eight := rfl
  rw [hsum] at hadd
  rw [hadd, power_four_eq x hx]

theorem power_nine_eq (x : Peano) (hx : x ≠ zero) :
    power x nine (Or.inl hx) =
      (((x * x) * x) * ((x * x) * x)) * ((x * x) * x) := by
  have h3 := power_three_eq x hx
  have hadd6 := power_add_eq x three three hx
  have hsum6 : three + three = six := rfl
  rw [hsum6] at hadd6
  have h6 : power x six (Or.inl hx) = ((x * x) * x) * ((x * x) * x) := by
    rw [hadd6, h3]
  have hadd := power_add_eq x six three hx
  have hsum : six + three = nine := rfl
  rw [hsum] at hadd
  rw [hadd, h6, h3]

end Peano

end ZeroMath.Numbers.CardinalNatural
