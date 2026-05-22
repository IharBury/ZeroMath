import ZeroMath.Logic.Trichotomy
import ZeroMath.Numbers.OrdinalNatural
import ZeroMath.Sequences.List

namespace ZeroMath.Numbers.CardinalNatural

def Peano := Nat

namespace Peano

def zero : Peano := Nat.zero

def toInt (n : Peano) : Int :=
  Int.ofNat n

def predecessor (n : Peano) (h : n ≠ zero) : Peano :=
  match n with
  | Nat.zero => by contradiction
  | Nat.succ n' => n'

def add (a : Peano) : Peano → Peano
  | Nat.zero => a
  | Nat.succ b' => Nat.succ (add a b')

instance : Add Peano where
  add := add

def multiply (a : Peano) : Peano → Peano
  | Nat.zero => Nat.zero
  | Nat.succ b' => add (multiply a b') a

instance : Mul Peano where
  mul := multiply

def successor (a : Peano) : Peano := Nat.succ a

def powerCore (a : Peano) : Peano → Peano
  | Nat.zero => successor zero
  | Nat.succ b' => multiply (powerCore a b') a

def power (a b : Peano) (_ : a ≠ zero ∨ b ≠ zero) : Peano :=
  powerCore a b

theorem add_zero (a : Peano) : a + zero = a := rfl

theorem zero_add (a : Peano) : zero + a = a := by
  induction a with
  | zero => rfl
  | succ a' ih => exact congrArg Nat.succ ih

theorem add_succ (a b : Peano) : a + b.successor = (a + b).successor := rfl

theorem succ_add (a b : Peano) : a.successor + b = (a + b).successor := by
  induction b with
  | zero => rfl
  | succ b' ih => exact congrArg Nat.succ ih

theorem add_assoc (a b c : Peano) : (a + b) + c = a + (b + c) := by
  induction c with
  | zero => rfl
  | succ c' ih => exact congrArg Nat.succ ih

theorem add_comm (a b : Peano) : a + b = b + a := by
  show a + b = b + a
  induction b with
  | zero =>
    show a + zero = zero + a
    rw [add_zero, zero_add]
  | succ b' ih =>
    show a + successor b' = successor b' + a
    rw [add_succ, ih, succ_add]

theorem multiply_zero (a : Peano) : a * zero = zero := rfl

theorem zero_multiply (a : Peano) : zero * a = zero := by
  show multiply zero a = zero
  induction a with
  | zero => rfl
  | succ a' ih =>
    show add (multiply zero a') zero = zero
    rw [ih]
    rfl

theorem multiply_succ (a b : Peano) : a * b.successor = a * b + a := rfl

theorem succ_multiply (a b : Peano) : a.successor * b = a * b + b := by
  show multiply a.successor b = add (multiply a b) b
  induction b with
  | zero => rfl
  | succ b' ih =>
    show add (multiply a.successor b') a.successor = add (add (multiply a b') a) (Nat.succ b')
    rw [ih]
    have h1 : add (add (multiply a b') b') a.successor = add (multiply a b') (add b' a.successor) := add_assoc _ _ _
    have h2 : add b' a.successor = add a (Nat.succ b') := by
      have h2a : add b' a.successor = successor (add b' a) := rfl
      have h2b : add a (Nat.succ b') = successor (add a b') := rfl
      rw [h2a, h2b]
      have h2c : add b' a = add a b' := add_comm b' a
      rw [h2c]
    have h3 : add (multiply a b') (add a (Nat.succ b')) = add (add (multiply a b') a) (Nat.succ b') := (add_assoc _ _ _).symm
    rw [h1, h2, h3]

theorem multiply_comm (a b : Peano) : a * b = b * a := by
  show multiply a b = multiply b a
  induction b with
  | zero =>
    show multiply a zero = multiply zero a
    have h1 : multiply a zero = a * zero := rfl
    have h2 : multiply zero a = zero * a := rfl
    rw [h1, h2, multiply_zero, zero_multiply]
  | succ b' ih =>
    show multiply a (Nat.succ b') = multiply (Nat.succ b') a
    have h1 : multiply a (Nat.succ b') = a * (successor b') := rfl
    have h2 : multiply (Nat.succ b') a = (successor b') * a := rfl
    rw [h1, h2, multiply_succ, succ_multiply]
    show add (multiply a b') a = add (multiply b' a) a
    rw [ih]

theorem multiply_add (a b c : Peano) : a * (b + c) = a * b + a * c := by
  induction c with
  | zero =>
    rfl
  | succ c' ih =>
    show multiply a (add b (successor c')) = add (multiply a b) (multiply a (successor c'))
    have h1 : add b (successor c') = successor (add b c') := rfl
    rw [h1]
    have h2 : multiply a (successor (add b c')) = add (multiply a (add b c')) a := rfl
    rw [h2]
    have h3 : multiply a (add b c') = add (multiply a b) (multiply a c') := ih
    rw [h3]
    have h4 : multiply a (successor c') = add (multiply a c') a := rfl
    rw [h4]
    have h5 : add (multiply a b) (add (multiply a c') a) = add (add (multiply a b) (multiply a c')) a := by
      exact (add_assoc (multiply a b) (multiply a c') a).symm
    exact h5.symm

theorem multiply_assoc (a b c : Peano) : (a * b) * c = a * (b * c) := by
  induction c with
  | zero =>
    rfl
  | succ c' ih =>
    show multiply (multiply a b) (successor c') = multiply a (multiply b (successor c'))
    have h1 : multiply (multiply a b) (successor c') = add (multiply (multiply a b) c') (multiply a b) := rfl
    rw [h1]
    have h2 : multiply b (successor c') = add (multiply b c') b := rfl
    rw [h2]
    have h3 : multiply a (add (multiply b c') b) = add (multiply a (multiply b c')) (multiply a b) := multiply_add a (multiply b c') b
    rw [h3]
    have h4 : multiply (multiply a b) c' = multiply a (multiply b c') := ih
    rw [h4]

theorem add_eq_nat_add (a b : Peano) : add a b = Nat.add a b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change Nat.succ (add a b) = Nat.succ (Nat.add a b)
    rw [ih]

theorem multiply_eq_nat_mul (a b : Peano) : multiply a b = Nat.mul a b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change add (multiply a b) a = Nat.mul a (Nat.succ b)
    rw [ih]
    rw [add_eq_nat_add]
    rfl

theorem multiply_left_cancel (b q c : Peano) (hb : b ≠ zero) (h : b * q = b * c) : q = c := by
  have hnat : Nat.mul b q = Nat.mul b c := by
    rw [← multiply_eq_nat_mul b q, ← multiply_eq_nat_mul b c]
    exact h
  exact Nat.mul_left_cancel (Nat.pos_of_ne_zero hb) hnat

theorem add_ne_zero_of_left_ne_zero (a b : Peano) (ha : a ≠ zero) : a + b ≠ zero := by
  intro h
  cases b with
  | zero => exact ha h
  | succ b' => cases h

theorem add_ne_zero_of_right_ne_zero (a b : Peano) (hb : b ≠ zero) : a + b ≠ zero := by
  intro h
  cases b with
  | zero => exact hb rfl
  | succ b' => cases h

theorem multiply_ne_zero (x y : Peano) (hx : x ≠ zero) (hy : y ≠ zero) : x * y ≠ zero := by
  intro hxy
  cases x with
  | zero => exact hx rfl
  | succ x' =>
    cases y with
    | zero => exact hy rfl
    | succ y' => cases hxy

theorem powerCore_eq_nat_pow (x e : Peano) : powerCore x e = Nat.pow (x : Nat) (e : Nat) := by
  induction e with
  | zero => rfl
  | succ e' ih =>
    change multiply (powerCore x e') x = Nat.pow (x : Nat) (Nat.succ e')
    rw [multiply_eq_nat_mul]
    rw [ih]
    change _root_.Nat.mul (Nat.pow x e') (x : Nat) = _root_.Nat.mul (Nat.pow x e') (x : Nat)
    rfl

theorem power_eq_nat_pow (x e : Peano) (h : x ≠ zero ∨ e ≠ zero) : power x e h = Nat.pow (x : Nat) (e : Nat) :=
  powerCore_eq_nat_pow x e

theorem pos_pow_of_pos {a : Nat} (h : 0 < a) (e : Nat) : 0 < Nat.pow a e := by
  induction e with
  | zero =>
    change 0 < 1
    exact Nat.zero_lt_one
  | succ e' ih =>
    change 0 < (Nat.pow a e') * a
    exact Nat.mul_pos ih h

theorem power_ne_zero (x e : Peano) (hx : x ≠ zero) : power x e (Or.inl hx) ≠ zero := by
  intro hpow
  have hnat : Nat.pow (x : Nat) (e : Nat) = 0 := by
    rw [← power_eq_nat_pow x e (Or.inl hx)]
    exact hpow
  have hx_nat : (x : Nat) ≠ Nat.zero := hx
  have xpos : Nat.zero < (x : Nat) := Nat.pos_of_ne_zero hx_nat
  exact Nat.ne_of_gt (pos_pow_of_pos xpos (e : Nat)) hnat

theorem zero_power_of_nonzero_exponent (e : Peano) (he : e ≠ zero) : power zero e (Or.inr he) = zero := by
  cases e with
  | zero => contradiction
  | succ e' => rfl

theorem powerCore_add (x y z : Peano) : powerCore x (y + z) = powerCore x y * powerCore x z := by
  induction z with
  | zero =>
    have h1 : y + zero = y := add_zero y
    change powerCore x (y + zero) = powerCore x y * powerCore x zero
    rw [h1]
    have h2 : powerCore x zero = successor zero := rfl
    rw [h2]
    have h : powerCore x y * successor zero = powerCore x y * zero + powerCore x y := multiply_succ (powerCore x y) zero
    rw [h]
    have hz : powerCore x y * zero = zero := multiply_zero (powerCore x y)
    rw [hz]
    exact (zero_add (powerCore x y)).symm
  | succ z' ih =>
    let z'' : Peano := z'
    have h1 : y + z''.successor = (y + z'').successor := rfl
    change powerCore x (y + z''.successor) = powerCore x y * powerCore x z''.successor
    rw [h1]
    have h2 : powerCore x (y + z'').successor = powerCore x (y + z'') * x := rfl
    rw [h2]
    have ih_core : powerCore x (y + z'') = powerCore x y * powerCore x z'' := ih
    rw [ih_core]
    have h3 : powerCore x z''.successor = powerCore x z'' * x := rfl
    rw [h3]
    exact multiply_assoc (powerCore x y) (powerCore x z'') x

theorem power_add (x y z : Peano) (h : x ≠ zero ∨ y ≠ zero) (h2 : x ≠ zero ∨ z ≠ zero) :
  ∃ h3, power x (y + z) h3 = power x y h * power x z h2 := by
  have h3 : x ≠ zero ∨ y + z ≠ zero := by
    cases h with
    | inl hx => exact Or.inl hx
    | inr hy => exact Or.inr (add_ne_zero_of_left_ne_zero y z hy)
  exact ⟨h3, powerCore_add x y z⟩

theorem powerCore_multiply (x y z : Peano) : powerCore (x * y) z = powerCore x z * powerCore y z := by
  induction z with
  | zero =>
    rfl
  | succ z' ih =>
    let z'' : Peano := z'
    change powerCore (x * y) z'' * (x * y) = (powerCore x z'' * x) * (powerCore y z'' * y)
    have ih' : powerCore (x * y) z'' = powerCore x z'' * powerCore y z'' := ih
    rw [ih']
    have h1 : (powerCore x z'' * powerCore y z'') * (x * y) = powerCore x z'' * (powerCore y z'' * (x * y)) := multiply_assoc (powerCore x z'') (powerCore y z'') (x * y)
    have h2 : powerCore y z'' * (x * y) = (powerCore y z'' * x) * y := (multiply_assoc (powerCore y z'') x y).symm
    have h3 : powerCore y z'' * x = x * powerCore y z'' := multiply_comm (powerCore y z'') x
    have h4 : x * powerCore y z'' * y = x * (powerCore y z'' * y) := multiply_assoc x (powerCore y z'') y
    have h5 : powerCore y z'' * (x * y) = x * (powerCore y z'' * y) := by
      rw [h2, h3, h4]
    have h6 : (powerCore x z'' * powerCore y z'') * (x * y) = powerCore x z'' * (x * (powerCore y z'' * y)) := by
      rw [h1, h5]
    have h7 : powerCore x z'' * (x * (powerCore y z'' * y)) = (powerCore x z'' * x) * (powerCore y z'' * y) := (multiply_assoc (powerCore x z'') x (powerCore y z'' * y)).symm
    rw [h6, h7]

theorem multiply_power (x y z : Peano) (h : x ≠ zero ∨ z ≠ zero) (h2 : y ≠ zero ∨ z ≠ zero) :
  ∃ h3, power (x * y) z h3 = power x z h * power y z h2 := by
  have h3 : x * y ≠ zero ∨ z ≠ zero := by
    cases h with
    | inl hx =>
      cases h2 with
      | inl hy => exact Or.inl (multiply_ne_zero x y hx hy)
      | inr hz => exact Or.inr hz
    | inr hz => exact Or.inr hz
  exact ⟨h3, powerCore_multiply x y z⟩

theorem powerCore_multiply_exponent (x y z : Peano) : powerCore x (y * z) = powerCore (powerCore x y) z := by
  induction z with
  | zero =>
    have h1 : y * zero = zero := multiply_zero y
    change powerCore x (y * zero) = powerCore (powerCore x y) zero
    rw [h1]
    rfl
  | succ z' ih =>
    let z'' : Peano := z'
    have h1 : y * z''.successor = y * z'' + y := multiply_succ y z''
    change powerCore x (y * z''.successor) = powerCore (powerCore x y) z''.successor
    rw [h1]
    have h2 : powerCore x (y * z'' + y) = powerCore x (y * z'') * powerCore x y := powerCore_add x (y * z'') y
    rw [h2]
    have ih_core : powerCore x (y * z'') = powerCore (powerCore x y) z'' := ih
    rw [ih_core]
    rfl

theorem power_multiply (x y z : Peano) (h : x ≠ zero ∨ y ≠ zero) (h2 : power x y h ≠ zero ∨ z ≠ zero) :
  ∃ h3, power x (y * z) h3 = power (power x y h) z h2 := by
  have h3 : x ≠ zero ∨ y * z ≠ zero := by
    by_cases hx : x = zero
    · cases h with
      | inl hx_ne => exact False.elim (hx_ne hx)
      | inr hy =>
        cases h2 with
        | inl hpow =>
          have hzero : power x y (Or.inr hy) = zero := by
            subst hx
            exact zero_power_of_nonzero_exponent y hy
          exact False.elim (hpow hzero)
        | inr hz => exact Or.inr (multiply_ne_zero y z hy hz)
    · exact Or.inl hx
  exact ⟨h3, powerCore_multiply_exponent x y z⟩

end Peano

inductive Peano.LessThan (a : Peano) : Peano → Prop where
  | base : Peano.LessThan a (a.successor)
  | step {b : Peano} : Peano.LessThan a b → Peano.LessThan a (b.successor)

instance : LT Peano where
  lt := Peano.LessThan

namespace Peano

theorem lt_trans {a b c : Peano} (hab : a < b) (hbc : b < c) : a < c := by
  induction hbc with
  | base => exact Peano.LessThan.step hab
  | step _ ih => exact Peano.LessThan.step ih

end Peano

def Peano.LessThanOrEqual (a b : Peano) : Prop :=
  a < b ∨ a = b

instance : LE Peano where
  le := Peano.LessThanOrEqual

namespace Peano

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

theorem succ_le_of_lt {a b : Peano} (h : a < b) : a.successor ≤ b := by
  induction h with
  | base => exact Or.inr rfl
  | step hlt ih =>
    cases ih with
    | inl h1 => exact Or.inl (LessThan.step h1)
    | inr h2 =>
      rw [h2]
      exact Or.inl LessThan.base

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

theorem le_of_succ_le_succ {a b : Peano} (h : a.successor ≤ b.successor) : a ≤ b := by
  cases h with
  | inl hlt =>
    exact Or.inl (lt_of_succ_lt_succ hlt)
  | inr heq =>
    have : a = b := Nat.succ.inj heq
    exact Or.inr this

theorem not_succ_le_zero {a : Peano} (h : a.successor ≤ zero) : False := by
  cases h with
  | inl hlt =>
    generalize hz : zero = z at hlt
    induction hlt with
    | base => cases hz
    | step _ _ => cases hz
  | inr heq => cases heq

theorem eq_zero_of_add_eq_zero_l {n m : Peano} (h : n + m = zero) : n = zero := by
  cases n with
  | zero => rfl
  | succ n' =>
    cases m with
    | zero => cases h
    | succ m' => cases h

theorem eq_zero_of_add_eq_zero_r {n m : Peano} (h : n + m = zero) : m = zero := by
  cases n with
  | zero =>
    have h1 : zero + m = m := zero_add m
    have h2 : m = zero + m := h1.symm
    have h3 : zero + m = zero := h
    rw [h3] at h2
    exact h2
  | succ n' =>
    cases m with
    | zero => rfl
    | succ m' => cases h

theorem succ_ne_zero (a : Peano) : a.successor ≠ zero := by
  intro contra
  cases contra

def subtract (a : Peano) : (b : Peano) → b ≤ a → Peano
  | Nat.zero, _ => a
  | Nat.succ b', h =>
    match a, h with
    | Nat.zero, h' => False.elim (not_succ_le_zero h')
    | Nat.succ a', h' => subtract a' b' (le_of_succ_le_succ h')

theorem le_add_self_left_lemma (a b : Peano) : a ≤ add a b := by
  induction b with
  | zero => exact Or.inr rfl
  | succ b' ih =>
    cases ih with
    | inl h_lt =>
      have h1 : add a b' < successor (add a b') := LessThan.base
      have h2 : add a b' < Nat.succ (add a b') := h1
      exact Or.inl (lt_trans h_lt h2)
    | inr h_eq =>
      have h1 : add a b' < successor (add a b') := LessThan.base
      have h2 : add a b' < Nat.succ (add a b') := h1
      have h_goal : a < Nat.succ (add a b') := by
        calc a = add a b' := h_eq
             _ < Nat.succ (add a b') := h2
      exact Or.inl h_goal

theorem le_add_self_left (a b : Peano) : a ≤ a + b := by
  have h_add_def : a + b = add a b := rfl
  rw [h_add_def]
  exact le_add_self_left_lemma a b

theorem le_add_self_right (a b : Peano) : b ≤ a + b := by
  have h1 : a + b = b + a := add_comm a b
  rw [h1]
  exact le_add_self_left b a

theorem subtract_zero (a : Peano) (h : zero ≤ a) : subtract a zero h = a := by
  cases a with
  | zero => rfl
  | succ a' => rfl

theorem subtract_eq_of_eq {a b c d : Peano} (h1 : b ≤ a) (h2 : d ≤ c) (h3 : a = c) (h4 : b = d) :
    subtract a b h1 = subtract c d h2 := by
  subst h3
  subst h4
  rfl

theorem subtract_add_cancel_lemma (a b : Peano) (h : b ≤ a) : add (subtract a b h) b = a := by
  induction b generalizing a with
  | zero => exact subtract_zero a h
  | succ b' ih =>
    cases a with
    | zero => cases h with | inl h' => cases h' | inr h' => cases h'
    | succ a' =>
      have h1 : subtract (Nat.succ a') (Nat.succ b') h = subtract a' b' (le_of_succ_le_succ h) := rfl
      rw [h1]
      have h2 : add (subtract a' b' (le_of_succ_le_succ h)) (Nat.succ b') = Nat.succ (add (subtract a' b' (le_of_succ_le_succ h)) b') := rfl
      rw [h2]
      have ih_app := ih a' (le_of_succ_le_succ h)
      rw [ih_app]

theorem subtract_add_cancel (a b : Peano) (h : b ≤ a) : subtract a b h + b = a := by
  have h1 : subtract a b h + b = add (subtract a b h) b := rfl
  rw [h1]
  exact subtract_add_cancel_lemma a b h

theorem add_cancel_right_lemma (a b c : Peano) (h : add a c = add b c) : a = b := by
  induction c with
  | zero =>
    have h1 : add a Nat.zero = a := rfl
    have h2 : add b Nat.zero = b := rfl
    rw [← h1, ← h2]
    exact h
  | succ c' ih =>
    have h1 : add a (Nat.succ c') = Nat.succ (add a c') := rfl
    have h2 : add b (Nat.succ c') = Nat.succ (add b c') := rfl
    rw [h1, h2] at h
    exact ih (Nat.succ.inj h)

theorem add_subtract_cancel_lemma (a b : Peano) : ∃ h, subtract (add a b) b h = a := by
  have h_le : b ≤ add a b := by
    have h_rw : a + b = add a b := rfl
    rw [← h_rw]
    exact le_add_self_right a b
  exact ⟨h_le, add_cancel_right_lemma (subtract (add a b) b h_le) a b (subtract_add_cancel_lemma (add a b) b h_le)⟩

theorem add_subtract_cancel (a b : Peano) : ∃ h, subtract (a + b) b h = a := by
  have h_le : b ≤ a + b := le_add_self_right a b
  have h_cancel_add : add (subtract (a + b) b h_le) b = add a b := by
    have h1 : subtract (a + b) b h_le + b = a + b := subtract_add_cancel (a + b) b h_le
    have h2 : subtract (a + b) b h_le + b = add (subtract (a + b) b h_le) b := rfl
    have h3 : a + b = add a b := rfl
    rw [h2] at h1
    calc add (subtract (a + b) b h_le) b = a + b := h1
         _ = add a b := h3
  exact ⟨h_le, add_cancel_right_lemma (subtract (a + b) b h_le) a b h_cancel_add⟩

theorem add_cancel_right (a b c : Peano) (h : a + c = b + c) : a = b := by
  have h1 : a + c = add a c := rfl
  have h2 : b + c = add b c := rfl
  rw [h1, h2] at h
  exact add_cancel_right_lemma a b c h

theorem add_subtract_assoc (a b c : Peano) (h : b ≥ c) : ∃ h2, subtract (a + b) c h2 = a + subtract b c h := by
  have h2 : c ≤ a + b := le_trans h (le_add_self_right a b)
  have h3 : subtract (a + b) c h2 + c = (a + subtract b c h) + c := by
    rw [subtract_add_cancel (a + b) c h2, add_assoc a (subtract b c h) c, subtract_add_cancel b c h]
  have h_cancel_right : add (subtract (a + b) c h2) c = add (a + subtract b c h) c := by
    have h_left : subtract (a + b) c h2 + c = add (subtract (a + b) c h2) c := rfl
    have h_right : (a + subtract b c h) + c = add (a + subtract b c h) c := rfl
    rw [← h_left, ← h_right]
    exact h3
  exact ⟨h2, add_cancel_right_lemma (subtract (a + b) c h2) (a + subtract b c h) c h_cancel_right⟩

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
    rw [add_comm y z]
    rw [← add_assoc left z y]
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
    have h_mul_add : x * (d + z) = x * d + x * z := multiply_add x d z
    calc x * d + x * z = x * (d + z) := h_mul_add.symm
         _ = x * y := by rw [h_y]
  have h2 : x * z ≤ x * y := by
    rw [← h_mul_y]
    exact le_add_self_right (x * d) (x * z)
  have h_cancel : x * d + x * z = subtract (x * y) (x * z) h2 + x * z := by
    rw [h_mul_y, subtract_add_cancel (x * y) (x * z) h2]
  exact ⟨h2, add_cancel_right (x * d) (subtract (x * y) (x * z) h2) (x * z) h_cancel⟩

theorem not_lt_zero (a : Peano) : ¬(a < zero) := by
  intro h
  generalize hz : zero = z at h
  induction h with
  | base => cases hz
  | step _ _ => cases hz

theorem not_lt_self (a : Peano) : ¬(a < a) := by
  induction a with
  | zero => exact not_lt_zero zero
  | succ a' ih =>
    intro h
    exact ih (lt_of_succ_lt_succ h)

theorem succ_lt_succ {a b : Peano} (h : a < b) : a.successor < b.successor := by
  induction h with
  | base => exact LessThan.base
  | step _ ih => exact LessThan.step ih

theorem ne_of_lt {a b : Peano} (h : a < b) : a ≠ b := by
  intro heq
  rw [heq] at h
  exact not_lt_self b h

theorem not_lt_of_lt {a b : Peano} (h : a < b) : ¬(b < a) := by
  intro hba
  exact not_lt_self a (lt_trans h hba)

theorem zero_lt_succ (x : Peano) : zero < x.successor := by
  induction x with
  | zero => exact LessThan.base
  | succ x' ih => exact LessThan.step ih

theorem zero_le (x : Peano) : x = zero ∨ zero < x := by
  cases x with
  | zero => exact Or.inl rfl
  | succ x' => exact Or.inr (zero_lt_succ x')

theorem trichotomy_or (x y : Peano) : x < y ∨ x = y ∨ y < x := by
  induction x generalizing y with
  | zero =>
    cases zero_le y with
    | inl h => exact Or.inr (Or.inl h.symm)
    | inr h => exact Or.inl h
  | succ x ihx =>
    cases y with
    | zero =>
      exact Or.inr (Or.inr (zero_lt_succ x))
    | succ y =>
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

def isDivisible (a b : Peano) : Prop :=
  b ≠ zero ∧ ∃ c : Peano, b * c = a

def isPower (e x : Peano) : Prop :=
  ∃ y : Peano, ∃ h : y ≠ zero ∨ e ≠ zero, power y e h = x

instance : DecidableEq Peano := inferInstanceAs (DecidableEq Nat)

def root_rec (a e orig_x : Peano) : Peano :=
  match a with
  | Nat.zero => zero
  | Nat.succ a' =>
    if power (successor a') e (Or.inl (by intro h; cases h)) = orig_x then
      successor a'
    else
      root_rec a' e orig_x

def root (e x : Peano) (_ : e ≠ zero ∧ isPower e x) : Peano :=
  root_rec x e x

theorem le_pow_self (a : Nat) : ∀ (e : Nat), e ≠ 0 → a ≤ Nat.pow a e := by
  intro e he
  induction e with
  | zero => contradiction
  | succ e' _ =>
    cases e' with
    | zero =>
      change a ≤ Nat.pow a 1
      change a ≤ (Nat.pow a 0) * a
      change a ≤ 1 * a
      rw [Nat.one_mul]
      exact Nat.le_refl a
    | succ e'' =>
      change a ≤ (Nat.pow a (e'' + 1)) * a
      by_cases h : a = 0
      · subst h
        change 0 ≤ 0 * 0
        exact Nat.le_refl 0
      · have h_pos : 0 < a := Nat.pos_of_ne_zero h
        have h_pow_pos : 0 < Nat.pow a (e'' + 1) := pos_pow_of_pos h_pos (e'' + 1)
        exact Nat.le_mul_of_pos_left a h_pow_pos

theorem root_rec_correct (a e orig_x y : Nat) (h1 : Nat.pow y e = orig_x) (h2 : Nat.le y a) (hnonzero : (y : Peano) ≠ zero ∨ (e : Peano) ≠ zero) :
  ∃ h : root_rec (a : Peano) (e : Peano) (orig_x : Peano) ≠ zero ∨ (e : Peano) ≠ zero, power (root_rec (a : Peano) (e : Peano) (orig_x : Peano)) (e : Peano) h = (orig_x : Peano) := by
  induction a with
  | zero =>
    have h3 : y = Nat.zero := Nat.eq_zero_of_le_zero h2
    subst h3
    unfold root_rec
    have he : (e : Peano) ≠ zero := by
      cases hnonzero with
      | inl hy => exact False.elim (hy rfl)
      | inr he => exact he
    exact ⟨Or.inr he, (power_eq_nat_pow (Nat.zero : Peano) (e : Peano) (Or.inr he)).trans h1⟩
  | succ a' ih =>
    unfold root_rec
    split
    · next h_eq => exact ⟨Or.inl (by intro h; cases h), h_eq⟩
    · next h_neq =>
      apply ih
      have h3 : y ≠ Nat.succ a' := by
        intro h4
        subst h4
        have hsucc : (Nat.succ a' : Peano) ≠ zero := by intro h; cases h
        have h_pow_eq : power (Nat.succ a' : Peano) (e : Peano) (Or.inl hsucc) = (orig_x : Peano) := by
          rw [power_eq_nat_pow (Nat.succ a' : Peano) (e : Peano) (Or.inl hsucc)]
          exact h1
        exact h_neq h_pow_eq
      exact Nat.le_of_lt_succ (Nat.lt_of_le_of_ne h2 h3)

theorem root_is_power (e x : Peano) (h : e ≠ zero ∧ isPower e x) :
  ∃ hroot : root e x h ≠ zero ∨ e ≠ zero, power (root e x h) e hroot = x := by
  unfold root
  have he : e ≠ zero := h.left
  cases h.right with | intro y hyex =>
    cases hyex with | intro hy_h hy =>
    have hy' : power y e hy_h = x := hy
    have hy_nat : Nat.pow (y : Nat) (e : Nat) = (x : Nat) := by
      rw [← power_eq_nat_pow y e hy_h]
      exact hy'
    have he_nat : (e : Nat) ≠ Nat.zero := by
      intro h_zero
      have h_zero' : e = zero := h_zero
      exact he h_zero'
    have h_le : Nat.le (y : Nat) (x : Nat) := by
      have h_le_pow := le_pow_self (y : Nat) (e : Nat) he_nat
      rw [hy_nat] at h_le_pow
      exact h_le_pow
    exact root_rec_correct x e x y hy_nat h_le hy_h

theorem nat_pow_inj {a b e : Nat} (he : e ≠ 0) (h : Nat.pow a e = Nat.pow b e) : a = b := by
  have h_pow_a : a ^ e = Nat.pow a e := rfl
  have h_pow_b : b ^ e = Nat.pow b e := rfl
  have h_eq : a ^ e = b ^ e := by
    rw [h_pow_a, h_pow_b]
    exact h
  cases Nat.lt_trichotomy a b with
  | inl hlt =>
    have h1 := Nat.pow_lt_pow_left hlt he
    rw [h_eq] at h1
    exact False.elim (Nat.lt_irrefl _ h1)
  | inr hrest =>
    cases hrest with
    | inl heq => exact heq
    | inr hgt =>
      have h1 := Nat.pow_lt_pow_left hgt he
      rw [← h_eq] at h1
      exact False.elim (Nat.lt_irrefl _ h1)

theorem root_power_cancel (x e : Peano) (h : e ≠ zero) (h2 : x ≠ zero ∨ e ≠ zero) :
  ∃ h3, root e (power x e h2) h3 = x := by
  have h_is_power : isPower e (power x e h2) := by
    exists x
    exists h2
  have h3 : e ≠ zero ∧ isPower e (power x e h2) := ⟨h, h_is_power⟩
  exists h3
  have root_prop := root_is_power e (power x e h2) h3
  cases root_prop with | intro hroot hroot_prop =>
  have hnat : Nat.pow ((root e (power x e h2) h3) : Nat) (e : Nat) = Nat.pow (x : Nat) (e : Nat) := by
    rw [← power_eq_nat_pow (root e (power x e h2) h3) e hroot]
    rw [← power_eq_nat_pow x e h2]
    exact hroot_prop
  have he_nat : (e : Nat) ≠ Nat.zero := h
  exact nat_pow_inj he_nat hnat

def divide_rec (a b orig_a : Peano) : Peano :=
  match a with
  | Nat.zero => zero
  | Nat.succ a' =>
    if b * successor a' = orig_a then
      successor a'
    else
      divide_rec a' b orig_a

def divide (a b : Peano) (_ : isDivisible a b) : Peano :=
  divide_rec a b a

theorem divide_rec_eq_of_multiply_eq (a b orig c : Peano) (hb : b ≠ zero)
    (hc : b * c = orig) (hle : Nat.le c a) : divide_rec a b orig = c := by
  induction a with
  | zero =>
    have hc0 : c = zero := Nat.eq_zero_of_le_zero hle
    rw [hc0]
    rfl
  | succ a ih =>
    by_cases hcandidate : b * successor a = orig
    · simp [divide_rec, hcandidate]
      exact multiply_left_cancel b (successor a) c hb (by rw [hc, hcandidate])
    · simp [divide_rec, hcandidate]
      apply ih
      have hne : c ≠ successor a := by
        intro h_eq
        apply hcandidate
        rw [← h_eq]
        exact hc
      exact Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hle hne)

theorem multiply_divide_cancel (a b : Peano) (h : isDivisible a b) : b * divide a b h = a := by
  cases h with
  | intro hb hexists =>
    cases hexists with
    | intro c hc =>
      unfold divide
      rw [divide_rec_eq_of_multiply_eq a b a c hb hc]
      exact hc
      have hnat : Nat.mul b c = a := by
        rw [← multiply_eq_nat_mul b c]
        exact hc
      rw [← hnat]
      exact Nat.le_mul_of_pos_left c (Nat.pos_of_ne_zero hb)

theorem divide_multiply_cancel (a b : Peano) (ha : a ≠ zero) :
    ∃ h : isDivisible (a * b) a, divide (a * b) a h = b := by
  have h : isDivisible (a * b) a := ⟨ha, ⟨b, rfl⟩⟩
  refine ⟨h, ?_⟩
  unfold divide
  apply divide_rec_eq_of_multiply_eq
  · exact ha
  · rfl
  · change Nat.le b (multiply a b)
    rw [multiply_eq_nat_mul a b]
    exact Nat.le_mul_of_pos_left b (Nat.pos_of_ne_zero ha)

theorem divide_divide (x y z : Peano) (h : isDivisible x y) (h2 : isDivisible (divide x y h) z) :
    ∃ h3, divide (divide x y h) z h2 = divide x (y * z) h3 := by
  have hz : z ≠ zero := h2.1
  have hy : y ≠ zero := h.1
  have hyz : y * z ≠ zero := multiply_ne_zero y z hy hz

  let d1 := divide x y h
  let d2 := divide d1 z h2

  have h_d1 : y * d1 = x := multiply_divide_cancel x y h
  have h_d2 : z * d2 = d1 := multiply_divide_cancel d1 z h2

  have h_mul : (y * z) * d2 = x := by
    calc (y * z) * d2 = y * (z * d2) := by rw [multiply_assoc]
         _ = y * d1 := by rw [h_d2]
         _ = x := h_d1

  have h3 : isDivisible x (y * z) := ⟨hyz, ⟨d2, h_mul⟩⟩
  exists h3

  have h_div_yz : (y * z) * divide x (y * z) h3 = x := multiply_divide_cancel x (y * z) h3
  apply multiply_left_cancel (y * z) (divide (divide x y h) z h2) (divide x (y * z) h3) hyz
  calc (y * z) * divide (divide x y h) z h2 = (y * z) * d2 := rfl
       _ = x := h_mul
       _ = (y * z) * divide x (y * z) h3 := h_div_yz.symm

theorem divide_add (x y z : Peano) (h : isDivisible x z) (h2 : isDivisible y z) :
    ∃ h3, divide (x + y) z h3 = divide x z h + divide y z h2 := by
  have hz : z ≠ zero := h.1
  have h3 : isDivisible (x + y) z := by
    cases h.2 with | intro a ha =>
    cases h2.2 with | intro b hb =>
    constructor
    · exact hz
    · exists a + b
      rw [multiply_add]
      rw [ha, hb]
  exists h3
  apply multiply_left_cancel z (divide (x + y) z h3) (divide x z h + divide y z h2) hz
  rw [multiply_divide_cancel]
  rw [multiply_add]
  rw [multiply_divide_cancel, multiply_divide_cancel]

theorem divide_subtract (x y z : Peano) (h : isDivisible x z) (h2 : isDivisible y z)
    (h3 : divide y z h2 ≤ divide x z h) :
    ∃ h4 h5, divide (subtract x y h4) z h5 = subtract (divide x z h) (divide y z h2) h3 := by
  let dx := divide x z h
  let dy := divide y z h2
  let d := subtract dx dy h3
  have hz : z ≠ zero := h.1
  have Hx : z * dx = x := multiply_divide_cancel x z h
  have Hy : z * dy = y := multiply_divide_cancel y z h2
  have h_dx : d + dy = dx := subtract_add_cancel dx dy h3
  have h_mul_dx : z * d + z * dy = z * dx := by
    calc z * d + z * dy = z * (d + dy) := (multiply_add z d dy).symm
         _ = z * dx := by rw [h_dx]
  have h4 : y ≤ x := by
    rw [← Hy, ← Hx]
    rw [← h_mul_dx]
    exact le_add_self_right (z * d) (z * dy)
  have h_mul_sub := multiply_subtract z dx dy h3
  rcases h_mul_sub with ⟨h_mul_sub_wit, h_mul_sub_eq⟩
  have h_mul_sub_eq2 : z * subtract dx dy h3 = subtract x y h4 := by
    rw [h_mul_sub_eq]
    exact subtract_eq_of_eq h_mul_sub_wit h4 Hx Hy
  have h5 : isDivisible (subtract x y h4) z := by
    constructor
    · exact hz
    · exists subtract dx dy h3
  exists h4, h5
  apply multiply_left_cancel z (divide (subtract x y h4) z h5) (subtract dx dy h3) hz
  have Hleft : z * divide (subtract x y h4) z h5 = subtract x y h4 := multiply_divide_cancel (subtract x y h4) z h5
  rw [Hleft, h_mul_sub_eq2]

theorem multiply_divide_assoc (x y z : Peano) (h : isDivisible y z) :
    ∃ h2, divide (x * y) z h2 = x * divide y z h := by
  have hz : z ≠ zero := h.1
  have hy_div : ∃ c : Peano, z * c = y := h.2
  have h2 : isDivisible (x * y) z := by
    cases hy_div with | intro c hc =>
    constructor
    · exact hz
    · exists x * c
      calc z * (x * c) = x * (z * c) := by
            have h1 : z * (x * c) = (z * x) * c := (multiply_assoc z x c).symm
            have h2 : z * x = x * z := multiply_comm z x
            rw [h1, h2, multiply_assoc]
           _ = x * y := by rw [hc]
  exists h2
  apply multiply_left_cancel z (divide (x * y) z h2) (x * divide y z h) hz
  have Hleft : z * divide (x * y) z h2 = x * y := multiply_divide_cancel (x * y) z h2
  have Hright : z * (x * divide y z h) = x * y := by
    calc z * (x * divide y z h) = (z * x) * divide y z h := (multiply_assoc z x (divide y z h)).symm
         _ = (x * z) * divide y z h := by rw [multiply_comm z x]
         _ = x * (z * divide y z h) := multiply_assoc x z (divide y z h)
         _ = x * y := by rw [multiply_divide_cancel y z h]
  rw [Hleft, Hright]

def fromInt (n : Int) (_h : n ≥ 0) : Peano :=
  n.toNat

theorem fromInt_toInt (n : Peano) : ∃ h, fromInt (toInt n) h = n := by
  exact ⟨Int.natCast_nonneg n, rfl⟩

theorem toInt_fromInt (x : Int) (h : x ≥ 0) : (fromInt x h).toInt = x := by
  unfold fromInt
  unfold toInt
  exact Int.toNat_of_nonneg h

def fromOrdinal : ZeroMath.Numbers.OrdinalNatural.Peano → Peano
  | ZeroMath.Numbers.OrdinalNatural.Peano.one => successor zero
  | ZeroMath.Numbers.OrdinalNatural.Peano.successor n => successor (fromOrdinal n)

def toOrdinal (n : Peano) (h : n ≠ zero) : ZeroMath.Numbers.OrdinalNatural.Peano :=
  match n, h with
  | Nat.zero, h_contra => by exact False.elim (h_contra rfl)
  | Nat.succ Nat.zero, _ => ZeroMath.Numbers.OrdinalNatural.Peano.one
  | Nat.succ (Nat.succ n'), _ => ZeroMath.Numbers.OrdinalNatural.Peano.successor (toOrdinal (Nat.succ n') (by intro h_contra; cases h_contra))

def two : Peano := successor (successor zero)

def isEven (a : Peano) : Prop := isDivisible a two

def isOdd (a : Peano) : Prop := ¬ isEven a

def ten : Peano := (10 : Nat)

def AllLessThanTen : ZeroMath.Sequences.List Peano → Prop
  | _root_.List.nil => True
  | _root_.List.cons d ds => d < ten ∧ AllLessThanTen ds

def HasNonZero : ZeroMath.Sequences.List Peano → Prop
  | _root_.List.nil => False
  | _root_.List.cons d ds => d ≠ zero ∨ HasNonZero ds

end Peano

end ZeroMath.Numbers.CardinalNatural
