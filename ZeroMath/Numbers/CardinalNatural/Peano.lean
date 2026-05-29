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

def successor_ne_zero : ∀ p : Peano, successor p ≠ zero
  | _ => by intro h; cases h

def successor_injective : ∀ {p q : Peano}, successor p = successor q → p = q
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

theorem toInt_fromInt (x : Int) (h : x ≥ 0) : (fromInt x h).toInt = x := by
  simp [fromInt, toInt]
  rw [toNat_fromNat]
  exact Int.toNat_of_nonneg h

def predecessor (n : Peano) (h : n ≠ zero) : Peano :=
  match n with
  | zero => by contradiction
  | successor n' => n'

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

def power.recursiveCondition (a b : Peano) : a.successor ≠ zero ∨ b ≠ zero := by
  left
  apply successor_ne_zero

def power (a b : Peano) (h : a ≠ zero ∨ b ≠ zero) : Peano :=
  match a with
  | zero => zero
  | successor a' =>
    match b with
    | zero => one
    | successor b' => power (successor a') b' (power.recursiveCondition a' b') * a

theorem add_zero (a : Peano) : a + zero = a := rfl

theorem zero_add (a : Peano) : zero + a = a := by
  induction a with
  | zero => rfl
  | successor a' ih => exact congrArg successor ih

theorem add_successor (a b : Peano) : a + b.successor = (a + b).successor := rfl

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

theorem multiply_one (a : Peano) : a * one = a := by
  induction a with
  | zero => rfl
  | successor a' ih =>
    show a'.successor * one = a'.successor
    rw [successor_multiply, ih]
    rfl

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

theorem power_add (x y z : Peano) (h : x ≠ zero ∨ y ≠ zero) (h2 : x ≠ zero ∨ z ≠ zero) :
  ∃ h3, power x (y + z) h3 = power x y h * power x z h2 := by
  have h3 : x ≠ zero ∨ y + z ≠ zero := by
    cases h with
    | inl hx => exact Or.inl hx
    | inr hy => exact Or.inr (add_ne_zero_of_left_ne_zero y z hy)
  exists h3
  cases x with
  | zero => simp [power, multiply_zero]
  | successor x' =>
    induction z with
    | zero => simp [power, add_zero, multiply_one]
    | successor z' ih =>
      show x'.successor.power (successor (y + z')) h3 = x'.successor.power y h * (x'.successor.power z' _ * x'.successor)
      have h4 : x'.successor ≠ zero ∨ y + z' ≠ zero := by
        left
        apply successor_ne_zero
      show x'.successor.power (y + z') h4 * x'.successor = x'.successor.power y h * (x'.successor.power z' _ * x'.successor)
      rw [ih, multiply_associative]

theorem power_proof_irrelevance (x z : Peano) (h1 h2 : x ≠ zero ∨ z ≠ zero) :
  power x z h1 = power x z h2 := by
  cases x with
  | zero =>
    cases z with
    | zero => cases h1 <;> rename_i h <;> cases h rfl
    | successor z' => rfl
  | successor x' =>
    cases z with
    | zero => rfl
    | successor z' => rfl

theorem eq_rec_power (a b z : Peano) (heq : a = b) (h1 : a ≠ zero ∨ z ≠ zero) (h2 : b ≠ zero ∨ z ≠ zero) :
  power a z h1 = power b z h2 := by
  cases heq
  exact power_proof_irrelevance a z h1 h2

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
        have h_lhs_eq : power (successor x' * successor y') (successor z') h3 = power (successor x' * successor y') (successor z') (Or.inr (successor_ne_zero z')) := power_proof_irrelevance _ _ _ _
        rw [h_lhs_eq]
        have h_lhs_expand : power (successor x' * successor y') (successor z') (Or.inr (successor_ne_zero z')) = power (successor x' * successor y') z' (Or.inl (multiply_ne_zero _ _ (successor_ne_zero x') (successor_ne_zero y'))) * (successor x' * successor y') := rfl
        rw [h_lhs_expand]

        have h_rhs1_eq : power (successor x') (successor z') h = power (successor x') (successor z') (Or.inr (successor_ne_zero z')) := power_proof_irrelevance _ _ _ _
        have h_rhs2_eq : power (successor y') (successor z') h2 = power (successor y') (successor z') (Or.inr (successor_ne_zero z')) := power_proof_irrelevance _ _ _ _
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

theorem power_multiply (x y z : Peano) (h : x ≠ zero ∨ y ≠ zero) (h2 : power x y h ≠ zero ∨ z ≠ zero) :
  ∃ h3, power x (y * z) h3 = power (power x y h) z h2 := by
  induction z with
  | zero =>
    simp [multiply_zero]
    cases h2 with
    | inr hz => contradiction
    | inl h_power_ne_zero =>
      have h3 : x ≠ zero := by
        cases h with
        | inl hx => exact hx
        | inr hy =>
          intro hx
          apply h_power_ne_zero
          rw [hx, power]
      exists h3
      cases x with
      | zero => contradiction
      | successor x' => simp [power, power_zero_eq_one]
  | successor z' ih =>
    cases x with
    | zero =>
      cases h with
      | inl hx => contradiction
      | inr hy =>
        have h3 : zero ≠ zero ∨ y * z'.successor ≠ zero := by
          right
          intro h4
          have h5 := product_is_zero_if_factor_is_zero y z'.successor h4
          cases h5 with
          | inl hy_zero => contradiction
          | inr hz_zero => contradiction
        exists h3
        simp [power, multiply_successor]
    | successor x' =>
      simp [multiply_successor]
      let ⟨h3, h_power_add⟩ := power_add x'.successor (y * z') y (by simp) (by simp)
      rw [h_power_add]
      cases z' with
      | successor z'' =>
        have h4 : x'.successor.power y h ≠ zero ∨ z''.successor ≠ zero := by
          right
          apply successor_ne_zero
        let ⟨h4, ih⟩ := ih h4
        rw [ih]
        let ⟨h5, h_power_successor⟩ := power_successor (x'.successor.power y h) z''.successor (by simp)
        rw [h_power_successor]
      | zero =>
        have h4 : x'.successor.power y h ≠ zero ∨ zero ≠ zero := by
          left
          intro h4
          have h5 := power_is_zero_if_base_is_zero _ y h h4
          contradiction
        let ⟨h4, ih⟩ := ih h4
        rw [ih]
        rw [power_zero_eq_one, one_multiply]
        show x'.successor.power y _ = (x'.successor.power y h).power one h2
        rw [power_one_eq_self]

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

def subtract (a : Peano) : (b : Peano) → b ≤ a → Peano
  | zero, _ => a
  | successor b', h =>
    match a, h with
    | zero, h' => False.elim (not_succ_le_zero h')
    | successor a', h' => subtract a' b' (le_of_succ_le_succ h')

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

def isDivisible (a b : Peano) : Prop :=
  b ≠ zero ∧ ∃ c : Peano, b * c = a

def isPower (e x : Peano) : Prop :=
  ∃ y : Peano, ∃ h : y ≠ zero ∨ e ≠ zero, power y e h = x

def root_rec (a e orig_x : Peano) : Peano :=
  match a with
  | zero => zero
  | successor a' =>
    if power (successor a') e (Or.inl (by intro h; cases h)) = orig_x then
      successor a'
    else
      root_rec a' e orig_x

def root (e x : Peano) (_ : e ≠ zero ∧ isPower e x) : Peano :=
  root_rec x e x

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

theorem root_rec_le (a e orig_x : Peano) : root_rec a e orig_x ≤ a := by
  induction a with
  | zero =>
    unfold root_rec
    exact Or.inr rfl
  | successor a' ih =>
    unfold root_rec
    split
    · next _ =>
      exact Or.inr rfl
    · next _ =>
      exact le_trans ih (Or.inl LessThan.base)

theorem root_rec_hit (a e orig_x : Peano)
    (h : power (successor a) e (Or.inl (by intro hz; cases hz)) = orig_x) :
    root_rec (successor a) e orig_x = successor a := by
  unfold root_rec
  exact if_pos h

theorem root_rec_zero (e orig_x : Peano) : root_rec zero e orig_x = zero := by
  rfl

theorem root_rec_successor (a e orig_x : Peano) :
    root_rec (successor a) e orig_x =
      if power (successor a) e (Or.inl (by intro hz; cases hz)) = orig_x then
        successor a
      else
        root_rec a e orig_x := by
  rfl

theorem root_power_precondition (e x : Peano) (h : e ≠ zero) (h2 : x ≠ zero ∨ e ≠ zero) :
    e ≠ zero ∧ isPower e (power x e h2) := by
  exact ⟨h, ⟨x, h2, rfl⟩⟩

theorem root_power_precondition_left (e x : Peano) (h : e ≠ zero) (h2 : x ≠ zero ∨ e ≠ zero) :
    (root_power_precondition e x h h2).left = h := by
  rfl

theorem root_power_precondition_right (e x : Peano) (h : e ≠ zero) (h2 : x ≠ zero ∨ e ≠ zero) :
    (root_power_precondition e x h h2).right = ⟨x, h2, rfl⟩ := by
  rfl

theorem root_rec_correct (a e orig_x y : Peano) (hnonzero : y ≠ zero ∨ e ≠ zero) (h1 : power y e hnonzero = orig_x) (h2 : y ≤ a) :
  ∃ h, power (root_rec a e orig_x) e h = orig_x := by
  induction a with
  | zero =>
    have h3 : y = zero := eq_zero_of_le_zero y h2
    subst h3
    unfold root_rec
    cases hnonzero with
    | inl hy => contradiction
    | inr he => exists Or.inr he
  | successor a' ih =>
    unfold root_rec
    split
    · next h_eq => exact ⟨Or.inl (by intro h; cases h), h_eq⟩
    · next h_neq =>
      apply ih
      have h3 : y ≠ a'.successor := by
        intro h4
        subst h4
        exact h_neq h1
      exact le_of_lt_succ (lt_of_le_of_ne h2 h3)

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

theorem root_is_power (e x : Peano) (h : e ≠ zero ∧ isPower e x) :
  ∃ hroot : root e x h ≠ zero ∨ e ≠ zero, power (root e x h) e hroot = x := by
  unfold root
  let ⟨y, h2, h3⟩ := h.right
  apply root_rec_correct x e x y
  case hnonzero =>
    right
    exact h.left
  case h1 => exact h3
  case h2 =>
    rw [←h3]
    let ⟨h3, h4⟩ := le_self_pow y e h.left
    exact h4

theorem root_of_power_is_power' (e x : Peano) (h : e ≠ zero) (h2 : x ≠ zero ∨ e ≠ zero) :
  ∃ hroot : root e (power x e h2) (root_power_precondition e x h h2) ≠ zero ∨ e ≠ zero,
    power (root e (power x e h2) (root_power_precondition e x h h2)) e hroot = power x e h2 := by
  simpa [root_power_precondition] using root_is_power e (power x e h2) (root_power_precondition e x h h2)

theorem root_of_power_eq_power (e x : Peano) (h : e ≠ zero) (h2 : x ≠ zero ∨ e ≠ zero) :
  ∃ hroot : root e (power x e h2) (root_power_precondition e x h h2) ≠ zero ∨ e ≠ zero,
    power (root e (power x e h2) (root_power_precondition e x h h2)) e hroot = power x e h2 := by
  exact root_of_power_is_power' e x h h2

theorem root_of_power_eq_self (e x : Peano) (h : e ≠ zero) (h2 : x ≠ zero ∨ e ≠ zero) :
    ∃ h3, root e (power x e h2) h3 = x := by
  let h3 := root_power_precondition e x h h2
  refine ⟨h3, ?_⟩
  let ⟨hroot, hpow⟩ := root_of_power_eq_power e x h h2
  exact power_injective_base (root e (power x e h2) h3) x e h hroot h2 hpow

def isEven (a : Peano) : Prop := isDivisible a two

def isOdd (a : Peano) : Prop := ¬ isEven a

theorem isEven_successor (x : Peano) (h : isEven x) : isOdd (successor x) := by
  unfold isOdd
  intro hcontra
  unfold isEven isDivisible at h hcontra
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

theorem isEven_zero : isEven zero := by
  unfold isEven isDivisible
  apply And.intro
  · intro hz; cases hz
  · exists zero

theorem isEven_add_two (x : Peano) (h : isEven x) : isEven (successor (successor x)) := by
  unfold isEven isDivisible at h ⊢
  rcases h with ⟨h_ne, c, hc⟩
  apply And.intro
  · exact h_ne
  · exists successor c
    have hc_symm : x = two * c := hc.symm
    rw [hc_symm]
    rw [multiply_successor]
    rfl

theorem isEven_or_isEven_successor (x : Peano) : isEven x ∨ isEven (successor x) := by
  induction x with
  | zero => exact Or.inl isEven_zero
  | successor x' ih =>
    cases ih with
    | inl h_even => exact Or.inr (isEven_add_two x' h_even)
    | inr h_even_succ => exact Or.inl h_even_succ

theorem isEven_successor_of_isOdd (x : Peano) (h : isOdd x) : isEven (successor x) := by
  have h_or := isEven_or_isEven_successor x
  cases h_or with
  | inl h_even =>
    unfold isOdd at h
    contradiction
  | inr h_even_succ =>
    exact h_even_succ

theorem isOdd_predecessor (x : Peano) (h : x ≠ zero) (h2 : isEven x) : isOdd (predecessor x h) := by
  cases x with
  | zero => contradiction
  | successor x' =>
    intro h_even_x'
    have h_odd_succ := isEven_successor x' h_even_x'
    exact h_odd_succ h2

theorem isEven_predecessor_of_isOdd (x : Peano) (h : isOdd x) : ∃ h2, isEven (predecessor x h2) := by
  cases x with
  | zero =>
    have hz : isEven zero := isEven_zero
    contradiction
  | successor x' =>
    have h2 : successor x' ≠ zero := by intro h; contradiction
    exists h2
    change isEven x'
    have h_or := isEven_or_isEven_successor x'
    cases h_or with
    | inl h_even => exact h_even
    | inr h_even_succ =>
      unfold isOdd at h
      contradiction

def divide_rec (a b orig_a : Peano) : Peano :=
  match a with
  | zero => zero
  | successor a' =>
    if b * successor a' = orig_a then
      successor a'
    else
      divide_rec a' b orig_a

theorem divide_rec_correct (a b orig_a y : Peano) (h1 : b * y = orig_a) (h2 : y ≤ a) :
  b * divide_rec a b orig_a = orig_a := by
  induction a with
  | zero =>
    have h3 : y = zero := eq_zero_of_le_zero y h2
    subst h3
    unfold divide_rec
    exact h1
  | successor a' ih =>
    unfold divide_rec
    split
    · next h_eq => exact h_eq
    · next h_neq =>
      apply ih
      have h3 : y ≠ a'.successor := by
        intro h4
        subst h4
        exact h_neq h1
      exact le_of_lt_succ (lt_of_le_of_ne h2 h3)

def divide (a b : Peano) (_ : isDivisible a b) : Peano :=
  divide_rec a b a

theorem multiply_divide (a b : Peano) (h : isDivisible a b) : b * divide a b h = a := by
  unfold divide
  rcases h with ⟨h_b_ne_zero, c, hc⟩
  apply divide_rec_correct a b a c hc
  rw [←hc]
  exact le_mul_of_pos_left b c h_b_ne_zero

theorem divide_multiply_cancel (a b : Peano) (ha : a ≠ zero) : ∃ h : isDivisible (a * b) a, divide (a * b) a h = b := by
  have h : isDivisible (a * b) a := ⟨ha, ⟨b, rfl⟩⟩
  exists h
  have h1 : a * divide (a * b) a h = a * b := multiply_divide (a * b) a h
  exact multiply_left_cancel a (divide (a * b) a h) b ha h1

theorem divide_multiply_cancel_left (a b : Peano) (ha : a ≠ zero) : ∃ h : isDivisible (a * b) a, divide (a * b) a h = b := divide_multiply_cancel a b ha

theorem multiply_divide_assoc (x y z : Peano) (h : isDivisible y z) :
  ∃ h2 : isDivisible (x * y) z, divide (x * y) z h2 = x * divide y z h := by
  have hz_ne_zero : z ≠ zero := h.left
  have hy : z * divide y z h = y := multiply_divide y z h
  have h_divisible : isDivisible (x * y) z := by
    rcases h with ⟨hz, ⟨c, hc⟩⟩
    exact ⟨hz, ⟨x * c, by
      calc z * (x * c) = (z * x) * c := (multiply_associative z x c).symm
           _ = (x * z) * c := by rw [multiply_commutative z x]
           _ = x * (z * c) := multiply_associative x z c
           _ = x * y := by rw [hc]
      ⟩⟩
  exists h_divisible
  have h_mul_div : z * divide (x * y) z h_divisible = x * y := multiply_divide (x * y) z h_divisible
  have step1 : z * (x * divide y z h) = (z * x) * divide y z h := (multiply_associative z x (divide y z h)).symm
  have step2 : (z * x) * divide y z h = (x * z) * divide y z h := by rw [multiply_commutative z x]
  have step3 : (x * z) * divide y z h = x * (z * divide y z h) := multiply_associative x z (divide y z h)
  have step4 : x * (z * divide y z h) = x * y := by rw [hy]
  have step5 : z * divide (x * y) z h_divisible = z * (x * divide y z h) := by
    calc z * divide (x * y) z h_divisible = x * y := h_mul_div
         _ = x * (z * divide y z h) := step4.symm
         _ = (x * z) * divide y z h := step3.symm
         _ = (z * x) * divide y z h := step2.symm
         _ = z * (x * divide y z h) := step1.symm
  exact multiply_left_cancel z (divide (x * y) z h_divisible) (x * divide y z h) hz_ne_zero step5

theorem divide_add (x y z : Peano) (h : isDivisible x z) (h2 : isDivisible y z) :
  ∃ h3 : isDivisible (x + y) z, divide (x + y) z h3 = divide x z h + divide y z h2 := by
  have hz_ne_zero : z ≠ zero := h.left
  have hx : z * divide x z h = x := multiply_divide x z h
  have hy : z * divide y z h2 = y := multiply_divide y z h2
  have h_add : x + y = z * (divide x z h + divide y z h2) := by
    calc
      x + y = (z * divide x z h) + y := by rw [hx]
      _ = (z * divide x z h) + (z * divide y z h2) := by rw [hy]
      _ = z * (divide x z h + divide y z h2) := (multiply_distributive_over_add_right z (divide x z h) (divide y z h2)).symm
  have h3 : isDivisible (x + y) z := ⟨hz_ne_zero, ⟨divide x z h + divide y z h2, h_add.symm⟩⟩
  exists h3
  have h_div : z * divide (x + y) z h3 = x + y := multiply_divide (x + y) z h3
  have h_eq : z * divide (x + y) z h3 = z * (divide x z h + divide y z h2) := by
    rw [h_div, h_add]
  exact multiply_left_cancel z (divide (x + y) z h3) (divide x z h + divide y z h2) hz_ne_zero h_eq

theorem divide_divide (x y z : Peano) (h : isDivisible x y) (h2 : isDivisible (divide x y h) z) :
  ∃ h3 : isDivisible x (y * z), divide (divide x y h) z h2 = divide x (y * z) h3 := by
  have hz_ne_zero : z ≠ zero := h2.1
  have hy_ne_zero : y ≠ zero := h.1
  have hyz_ne_zero : y * z ≠ zero := multiply_ne_zero y z hy_ne_zero hz_ne_zero
  have h_x : x = y * divide x y h := (multiply_divide x y h).symm
  have h_div : divide x y h = z * divide (divide x y h) z h2 := (multiply_divide (divide x y h) z h2).symm

  have step1 : y * divide x y h = y * (z * divide (divide x y h) z h2) := by
    exact congrArg (fun a => y * a) h_div

  have step2 : y * (z * divide (divide x y h) z h2) = (y * z) * divide (divide x y h) z h2 :=
    (multiply_associative y z _).symm

  have step3 : x = (y * z) * divide (divide x y h) z h2 := Eq.trans (Eq.trans h_x step1) step2

  have h3 : isDivisible x (y * z) := by
    exact ⟨hyz_ne_zero, ⟨divide (divide x y h) z h2, step3.symm⟩⟩

  exists h3

  have h_x3 : x = (y * z) * divide x (y * z) h3 := (multiply_divide x (y * z) h3).symm

  have step4 : (y * z) * divide (divide x y h) z h2 = (y * z) * divide x (y * z) h3 :=
    Eq.trans step3.symm h_x3

  exact multiply_left_cancel (y * z) _ _ hyz_ne_zero step4

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

theorem divide_subtract (x y z : Peano) (h : isDivisible x z) (h2 : isDivisible y z) (h4 : y ≤ x) :
  ∃ (h3 : isDivisible (subtract x y h4) z) (h5 : divide y z h2 ≤ divide x z h),
  divide (subtract x y h4) z h3 = subtract (divide x z h) (divide y z h2) h5 := by
  have hz_ne_zero : z ≠ zero := h.1
  have hx : z * divide x z h = x := multiply_divide x z h
  have hy : z * divide y z h2 = y := multiply_divide y z h2

  have hy_le_hx : z * divide y z h2 ≤ z * divide x z h := by
    calc z * divide y z h2 = y := hy
         _ ≤ x := h4
         _ = z * divide x z h := hx.symm

  have h5 : divide y z h2 ≤ divide x z h := multiply_le_cancel_left z _ _ hz_ne_zero hy_le_hx

  have h_mul_sub : ∃ h_sub, z * subtract (divide x z h) (divide y z h2) h5 = subtract (z * divide x z h) (z * divide y z h2) h_sub :=
    multiply_subtract z (divide x z h) (divide y z h2) h5
  rcases h_mul_sub with ⟨h_sub, h_mul_sub_eq⟩

  have h_sub_eq : subtract (z * divide x z h) (z * divide y z h2) h_sub = subtract x y h4 := by
    have add1 : subtract (z * divide x z h) (z * divide y z h2) h_sub + z * divide y z h2 = z * divide x z h := subtract_add_cancel _ _ _
    have add2 : subtract x y h4 + y = x := subtract_add_cancel _ _ _
    have add1_rw : subtract (z * divide x z h) (z * divide y z h2) h_sub + y = x := by
      have eq1 : subtract (z * divide x z h) (z * divide y z h2) h_sub + z * divide y z h2 = x := by
        calc subtract (z * divide x z h) (z * divide y z h2) h_sub + z * divide y z h2 = z * divide x z h := add1
             _ = x := hx
      have h_eq_y : z * divide y z h2 = y := hy
      have h_congr : subtract (z * divide x z h) (z * divide y z h2) h_sub + z * divide y z h2 = subtract (z * divide x z h) (z * divide y z h2) h_sub + y :=
        congrArg (fun a => subtract (z * divide x z h) (z * divide y z h2) h_sub + a) h_eq_y
      calc subtract (z * divide x z h) (z * divide y z h2) h_sub + y = subtract (z * divide x z h) (z * divide y z h2) h_sub + z * divide y z h2 := h_congr.symm
           _ = x := eq1
    exact add_cancel_right _ _ _ (by
      calc subtract (z * divide x z h) (z * divide y z h2) h_sub + y = x := add1_rw
           _ = subtract x y h4 + y := add2.symm
    )

  have h3 : isDivisible (subtract x y h4) z := by
    exact ⟨hz_ne_zero, ⟨subtract (divide x z h) (divide y z h2) h5, by rw [← h_sub_eq, h_mul_sub_eq]⟩⟩

  exact ⟨h3, h5, by
    have h_div_mul : z * divide (subtract x y h4) z h3 = subtract x y h4 := multiply_divide _ _ _
    have h_div_mul2 : z * subtract (divide x z h) (divide y z h2) h5 = subtract x y h4 := by
      rw [h_mul_sub_eq, h_sub_eq]

    exact multiply_left_cancel _ _ _ hz_ne_zero (by
      rw [h_div_mul, h_div_mul2]
    )
  ⟩

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

end Peano

end ZeroMath.Numbers.CardinalNatural
