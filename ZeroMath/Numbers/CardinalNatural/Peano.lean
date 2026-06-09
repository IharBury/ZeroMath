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
  cases p with
  | _ =>
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

theorem fromNat_toNat (p : Peano) : fromNat (toNat p) = p := by
  induction p with
  | zero =>
    rfl
  | successor p ih =>
    simp [toNat, fromNat, ih]

theorem toNat_fromNat (n : Nat) : toNat (fromNat n) = n := by
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    simp [toNat, fromNat, ih]

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
  exists Int.natCast_nonneg n.toNat
  simp [fromInt, toInt]
  apply fromNat_toNat

@[simp]
theorem toInt_fromInt (x : Int) (h : x ≥ 0) : (fromInt x h).toInt = x := by
  simp [fromInt, toInt]
  rw [toNat_fromNat]
  exact Int.toNat_of_nonneg h

def predecessor (n : Peano) (h : n ≠ zero) : Peano :=
  match n with
  | zero => by contradiction
  | successor n' => n'


theorem predecessor_successor (x : Peano) : ∃ h, predecessor x.successor h = x := by
  have h : x.successor ≠ zero := by intro h; contradiction
  exact ⟨h, rfl⟩

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

theorem power.recursiveCondition (a b : Peano) : a.successor ≠ zero ∨ b ≠ zero := by
  left
  apply successor_ne_zero

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
      show toNat (power a'.successor b' _ * a'.successor) = (a'.successor).toNat ^ b'.toNat.succ
      rw [Nat.pow_succ, multiply_toNat]
      congr
      apply ih

theorem power_injective_base (a b e : Peano) (he : e ≠ zero)
    (ha : a ≠ zero ∨ e ≠ zero) (hb : b ≠ zero ∨ e ≠ zero)
    (hp : power a e ha = power b e hb) : a = b := by
  apply eq_of_toNat_eq
  have hpowNat : a.toNat ^ e.toNat = b.toNat ^ e.toNat := by
    calc a.toNat ^ e.toNat = toNat (power a e ha) := (power_toNat a e ha).symm
         _ = toNat (power b e hb) := congrArg toNat hp
         _ = b.toNat ^ e.toNat := power_toNat b e hb
  exact (Nat.pow_left_inj (toNat_ne_zero e he)).mp hpowNat

@[simp]
theorem multiply_one (a : Peano) : a * one = a := by
  induction a with
  | zero => rfl
  | successor a' ih =>
    show a'.successor * one = a'.successor
    rw [successor_multiply, ih]
    rfl

@[simp]
theorem one_multiply (a : Peano) : one * a = a := by
  induction a with
  | zero => rfl
  | successor a' ih =>
    show one * a'.successor = a'.successor
    rw [multiply_successor, ih]
    rfl

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
        have h_eq : zero * successor y' = zero := zero_multiply _
        have h_lhs : power (zero * successor y') (successor z') h3 = power zero (successor z') (Or.inr (successor_ne_zero z')) := eq_rec_power _ _ _ h_eq _ _
        have h_zero : power zero (successor z') (Or.inr (successor_ne_zero z')) = zero := rfl
        rw [h_lhs, h_zero]
        have h_rhs_zero : power zero (successor z') h = zero := rfl
        apply Eq.symm
        exact Eq.trans (congrArg (fun X => X * power (successor y') (successor z') h2) h_rhs_zero) (zero_multiply _)
    | successor x' =>
      cases y with
      | zero =>
        have h_eq : successor x' * zero = zero := multiply_zero _
        have h_lhs : power (successor x' * zero) (successor z') h3 = power zero (successor z') (Or.inr (successor_ne_zero z')) := eq_rec_power _ _ _ h_eq _ _
        have h_zero : power zero (successor z') (Or.inr (successor_ne_zero z')) = zero := rfl
        rw [h_lhs, h_zero]
        have h_rhs_zero : power zero (successor z') h2 = zero := rfl
        apply Eq.symm
        exact Eq.trans (congrArg (fun X => power (successor x') (successor z') h * X) h_rhs_zero) (multiply_zero _)
      | successor y' =>
        have h_lhs_eq : power (successor x' * successor y') (successor z') h3 = power (successor x' * successor y') (successor z') (Or.inr (successor_ne_zero z')) := rfl
        rw [h_lhs_eq]
        have h_lhs_expand : power (successor x' * successor y') (successor z') (Or.inr (successor_ne_zero z')) = power (successor x' * successor y') z' (Or.inl (multiply_ne_zero _ _ (successor_ne_zero x') (successor_ne_zero y'))) * (successor x' * successor y') := rfl
        rw [h_lhs_expand]

        have h_rhs1_eq : power (successor x') (successor z') h = power (successor x') (successor z') (Or.inr (successor_ne_zero z')) := rfl
        have h_rhs2_eq : power (successor y') (successor z') h2 = power (successor y') (successor z') (Or.inr (successor_ne_zero z')) := rfl
        rw [h_rhs1_eq, h_rhs2_eq]
        have h_rhs1_expand : power (successor x') (successor z') (Or.inr (successor_ne_zero z')) = power (successor x') z' (Or.inl (successor_ne_zero x')) * successor x' := rfl
        have h_rhs2_expand : power (successor y') (successor z') (Or.inr (successor_ne_zero z')) = power (successor y') z' (Or.inl (successor_ne_zero y')) * successor y' := rfl
        rw [h_rhs1_expand, h_rhs2_expand]

        have h_ih := ih (successor x') (successor y') (Or.inl (successor_ne_zero x')) (Or.inl (successor_ne_zero y')) (Or.inl (multiply_ne_zero _ _ (successor_ne_zero x') (successor_ne_zero y')))
        rw [h_ih]

        rw [multiply_associative]
        have h1 : power (successor y') z' (Or.inl (successor_ne_zero y')) * (successor x' * successor y') = power (successor y') z' (Or.inl (successor_ne_zero y')) * successor x' * successor y' := by rw [←multiply_associative]
        rw [h1]
        have h2 : power (successor y') z' (Or.inl (successor_ne_zero y')) * successor x' = successor x' * power (successor y') z' (Or.inl (successor_ne_zero y')) := multiply_commutative _ _
        rw [h2]
        have h3 : successor x' * power (successor y') z' (Or.inl (successor_ne_zero y')) * successor y' = successor x' * (power (successor y') z' (Or.inl (successor_ne_zero y')) * successor y') := multiply_associative _ _ _
        rw [h3]
        have h4 : power (successor x') z' (Or.inl (successor_ne_zero x')) * (successor x' * (power (successor y') z' (Or.inl (successor_ne_zero y')) * successor y')) = power (successor x') z' (Or.inl (successor_ne_zero x')) * successor x' * (power (successor y') z' (Or.inl (successor_ne_zero y')) * successor y') := (multiply_associative _ _ _).symm
        rw [h4]

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
  cases x with
  | zero => exact Or.inl rfl
  | successor x' =>
    cases y with
    | zero => exact Or.inr rfl
    | successor y' =>
      have h_eq : successor x' * successor y' = successor x' * successor y' := rfl
      rw [h_eq] at h2
      cases h2

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

theorem lt_trans {a b c : Peano} (hab : a < b) (hbc : b < c) : a < c := by
  induction hbc with
  | base => exact Peano.LessThan.step hab
  | step _ ih => exact Peano.LessThan.step ih

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

theorem lt_of_succ_lt {a b : Peano} (h : a.successor < b) : a < b := by
  exact lt_trans LessThan.base h

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

theorem zero_lt_succ (x : Peano) : zero < x.successor := by
  induction x with
  | zero => exact LessThan.base
  | successor x' ih => exact LessThan.step ih

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
  intro heq
  rw [heq] at h
  exact not_lt_self b h

theorem not_lt_of_lt {a b : Peano} (h : a < b) : ¬(b < a) := by
  intro hba
  exact not_lt_self a (lt_trans h hba)


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

theorem lt_le_trans {a b c : Peano} (hab : a < b) (hbc : b ≤ c) : a < c := by
  cases hbc with
  | inl hbc_lt => exact lt_trans hab hbc_lt
  | inr hbc_eq =>
    rw [← hbc_eq]
    exact hab

theorem not_lt_implies_le {a b : Peano} (h : ¬ a < b) : b ≤ a := by
  cases trichotomy_or a b with
  | inl hlt => exact False.elim (h hlt)
  | inr htri =>
    cases htri with
    | inl heq => exact Or.inr heq.symm
    | inr hlt => exact Or.inl hlt

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

def isDivisibleRecursive (x a b : Peano) (h : b ≠ zero) : Bool :=
  if b * x = a then
    true
  else
    match x with
    | zero => false
    | successor x' => isDivisibleRecursive x' a b h

def isDivisible (a b : Peano) : Bool :=
  match b with
  | zero => false
  | successor b' => isDivisibleRecursive a a b'.successor (successor_ne_zero b')




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

theorem root_rec_step_h {a e x : Peano} (he : e ≠ zero)
  (h : ∀ b hb, successor x < b → power b e hb ≠ a)
  (h3 : ¬ power (successor x) e (Or.inr he) = a) :
  ∀ b hb, x < b → power b e hb ≠ a := by
  intro b hb hxb hpow
  cases lt_successor_cases hxb with
  | inl h_eq =>
    subst b
    have hpow' : power (successor x) e (Or.inr he) = a := by
      calc power (successor x) e (Or.inr he) = power (successor x) e hb := rfl
           _ = a := hpow
    exact h3 hpow'
  | inr hsxlt =>
    exact h b hb hsxlt hpow

def root_rec (a e x : Peano) (h : e ≠ zero) (h2 : ∀ b hb, x < b → power b e hb ≠ a) (h3 : Power e a) : Peano :=
  if h4 : power x e (Or.inr h) = a then
    x
  else
    match x with
    | zero =>
      False.elim (by
        rcases h3 with ⟨b, hb, hpow⟩
        cases b with
        | zero =>
          have hpow' : power zero e (Or.inr h) = a := by
            calc power zero e (Or.inr h) = power zero e hb := rfl
                 _ = a := hpow
          exact h4 hpow'
        | successor b' =>
          exact h2 (successor b') hb (zero_lt_succ b') hpow)
    | successor x' => root_rec a e x' h (root_rec_step_h h h2 h4) h3

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

theorem root_rec_initial_h (e x : Peano) (he : e ≠ zero) :
    ∀ b hb, x < b → power b e hb ≠ x := by
  intro b hb hxb hpow
  rcases le_self_pow b e he with ⟨hpre, hle⟩
  have hsame : power b e hpre = power b e hb := rfl
  rw [hsame] at hle
  have hxltpow : x < power b e hb := lt_of_lt_of_le hxb hle
  rw [hpow] at hxltpow
  exact not_lt_self x hxltpow

def root (e x : Peano) (h : e ≠ zero ∧ Power e x) : Peano :=
  root_rec x e x h.1 (root_rec_initial_h e x h.1) h.2

theorem root_rec_is_power (a e x : Peano) (he : e ≠ zero)
    (hbound : ∀ b hb, x < b → power b e hb ≠ a) (hp : Power e a) :
    power (root_rec a e x he hbound hp) e (Or.inr he) = a := by
  induction x with
  | zero =>
    by_cases hpow : power zero e (Or.inr he) = a
    · rw [root_rec, dif_pos hpow]
      calc power zero e _ = power zero e (Or.inr he) := rfl
           _ = a := hpow
    · have hcontra : False := by
        rcases hp with ⟨b, hb, hbpow⟩
        cases b with
        | zero =>
          have hpow' : power zero e (Or.inr he) = a := by
            calc power zero e (Or.inr he) = power zero e hb := rfl
                 _ = a := hbpow
          exact hpow hpow'
        | successor b' =>
          exact hbound (successor b') hb (zero_lt_succ b') hbpow
      exact False.elim hcontra
  | successor x' ih =>
    by_cases hpow : power (successor x') e (Or.inr he) = a
    · rw [root_rec, dif_pos hpow]
      calc power (successor x') e _ = power (successor x') e (Or.inr he) := rfl
           _ = a := hpow
    · rw [root_rec, dif_neg hpow]
      exact ih (root_rec_step_h he hbound hpow)

theorem root_is_power (e x : Peano) (h : e ≠ zero ∧ Power e x) :
  ∃ hroot : root e x h ≠ zero ∨ e ≠ zero, power (root e x h) e hroot = x := by
  exists Or.inr h.1
  unfold root
  exact root_rec_is_power x e x h.1 (root_rec_initial_h e x h.1) h.2

theorem root_of_power_eq_self (e x : Peano) (h : e ≠ zero) (h2 : x ≠ zero ∨ e ≠ zero) :
    ∃ h3, root e (power x e h2) h3 = x := by
  let h3 := root_power_precondition e x h h2
  exists h3
  rcases root_is_power e (power x e h2) h3 with ⟨hroot, hpow⟩
  exact power_injective_base (root e (power x e h2) h3) x e h hroot h2 hpow

theorem le_of_lt {a b : Peano} (h : a < b) : a ≤ b := Or.inl h

theorem isDivisibleRecursive_correct (x a b : Peano) (h : b ≠ zero) :
  isDivisibleRecursive x a b h = true ↔ ∃ c, c ≤ x ∧ b * c = a := by
  induction x with
  | zero =>
    unfold isDivisibleRecursive
    dsimp
    by_cases h_eq : b * zero = a
    · rw [if_pos h_eq]
      exact ⟨fun _ => ⟨zero, Or.inr rfl, h_eq⟩, fun _ => rfl⟩
    · rw [if_neg h_eq]
      apply Iff.intro
      · intro h_f; contradiction
      · intro h_ex; rcases h_ex with ⟨c, hc_le, hc_eq⟩
        cases hc_le with
        | inl h_lt => exact False.elim (not_lt_zero c h_lt)
        | inr h_eq2 => subst c; exact False.elim (h_eq hc_eq)
  | successor x' ih =>
    unfold isDivisibleRecursive
    dsimp
    by_cases h_eq : b * successor x' = a
    · rw [if_pos h_eq]
      exact ⟨fun _ => ⟨successor x', Or.inr rfl, h_eq⟩, fun _ => rfl⟩
    · rw [if_neg h_eq]
      rw [ih]
      apply Iff.intro
      · intro h_ex; rcases h_ex with ⟨c, hc_le, hc_eq⟩
        exists c
        exact ⟨le_trans hc_le (Or.inl (lt_successor_of_le (Or.inr rfl))), hc_eq⟩
      · intro h_ex; rcases h_ex with ⟨c, hc_le, hc_eq⟩
        exists c
        cases hc_le with
        | inl h_lt =>
          exact ⟨le_of_lt_succ h_lt, hc_eq⟩
        | inr h_eq2 => subst c; contradiction

theorem le_multiply_right_b (c b : Peano) (hb : b ≠ zero) : c ≤ b * c := by
  rw [multiply_commutative]
  cases b with
  | zero => contradiction
  | successor b' =>
    rw [multiply_successor]
    exact le_add_self_right (c * b') c

theorem isDivisibleCorrect (a b : Peano) : Divisible a b ↔ isDivisible a b := by
  unfold Divisible isDivisible
  apply Iff.intro
  · intro h
    rcases h with ⟨hb, c, hc⟩
    cases b with
    | zero => exact False.elim (hb rfl)
    | successor b' =>
      dsimp
      rw [isDivisibleRecursive_correct]
      exists c
      have h_c_le_a : c ≤ a := by
        rw [← hc]
        exact le_multiply_right_b c b'.successor hb
      exact ⟨h_c_le_a, hc⟩
  · intro h
    cases b with
    | zero => contradiction
    | successor b' =>
      dsimp at h
      rw [isDivisibleRecursive_correct] at h
      rcases h with ⟨c, _, hc_eq⟩
      exact ⟨successor_ne_zero b', c, hc_eq⟩

def Even (a : Peano) : Prop := Divisible a two

def Odd (a : Peano) : Prop := ¬ Even a

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

theorem multiply_le_cancel_left (z a b : Peano) (hz : z ≠ zero) (h : z * a ≤ z * b) : a ≤ b := by
  cases trichotomy_or a b with
  | inl h_lt => exact Or.inl h_lt
  | inr h_or =>
    cases h_or with
    | inl h_eq => exact Or.inr h_eq
    | inr h_gt =>
      have hex : ∃ c, b + c = a := ⟨subtract a b (Or.inl h_gt), by
        rw [add_commutative]
        exact subtract_add_cancel a b (Or.inl h_gt)
      ⟩
      rcases hex with ⟨c, hc⟩
      have hc_ne_zero : c ≠ zero := by
        intro h_cz
        subst h_cz
        rw [add_zero] at hc
        have h_na : ¬(b < a) := by
          rw [← hc]
          exact not_lt_self b
        exact h_na h_gt
      have h_za : z * a = z * b + z * c := by
        rw [← hc, multiply_distributive_over_add_right z b c]
      have hzc_ne_zero : z * c ≠ zero := multiply_ne_zero z c hz hc_ne_zero
      have h_za_gt : z * b < z * a := by
        rw [h_za]
        have hd : z * b + z * c = z * c + z * b := add_commutative (z * b) (z * c)
        rw [hd]
        have h_le_add : z * b ≤ z * c + z * b := le_add_self_right (z * c) (z * b)
        have h_ne_add : z * b ≠ z * c + z * b := by
          intro h_eq_add
          have hd2 : z * c + z * b = z * b + z * c := add_commutative (z * c) (z * b)
          rw [hd2] at h_eq_add
          have h_eq_zero : z * b + zero = z * b + z * c := by
            calc z * b + zero = z * b := by rw [add_zero]
                 _ = z * b + z * c := h_eq_add
          have hz_c_zero : zero = z * c := add_cancel_right zero (z * c) (z * b) (by
            rw [add_commutative zero (z * b), add_commutative (z * c) (z * b)]
            exact h_eq_zero
          )
          exact hzc_ne_zero hz_c_zero.symm
        exact lt_of_le_of_ne h_le_add h_ne_add
      cases h with
      | inl h_lt2 =>
        have h_na : ¬(z * b < z * b) := not_lt_self (z * b)
        exact False.elim (h_na (lt_trans h_za_gt h_lt2))
      | inr h_eq2 =>
        rw [h_eq2] at h_za_gt
        exact False.elim (not_lt_self (z * b) h_za_gt)

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

theorem toOrdinal_congr {a b : Peano} (h_eq : a = b)
  (ha : a ≠ zero) (hb : b ≠ zero) :
  toOrdinal a ha = toOrdinal b hb := by
  cases h_eq
  rfl

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
  exact not_lt_self b (lt_le_trans hlt h)

theorem subtract_ne_zero_of_lt {a b : Peano} (h_le : b ≤ a) (h_lt : b < a) :
    subtract a b h_le ≠ zero := by
  intro h_zero
  have h_cancel := subtract_add_cancel a b h_le
  rw [h_zero, zero_add] at h_cancel
  exact ne_of_lt h_lt h_cancel

theorem tenPow_add (m n : Peano) :
    tenPow (m + n) = tenPow m * tenPow n := by
  induction n with
  | zero =>
    rw [add_zero, tenPow, multiply_one]
  | successor n ih =>
    rw [add_successor, tenPow, ih, tenPow, ←multiply_associative, multiply_commutative ten _, multiply_associative]

end Peano

end ZeroMath.Numbers.CardinalNatural
