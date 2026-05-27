import ZeroMath.Logic.Trichotomy

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

theorem subtract_add_cancel (a b : Peano) (h : b ≤ a) : subtract a b h + b = a := by
  induction b generalizing a with
  | zero => simp [subtract, add_zero]
  | successor b' ih =>
    let ⟨h2, h3⟩ := successor_subtract a b'.successor h
    simp [add_successor]
    rw [add_commutative, ←add_successor, h3, add_commutative]
    apply ih

end Peano

end ZeroMath.Numbers.CardinalNatural
