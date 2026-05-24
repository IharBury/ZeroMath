namespace ZeroMath.Numbers.CardinalNatural

inductive Peano where
  | zero : Peano
  | successor : Peano → Peano

deriving instance DecidableEq for Peano

namespace Peano

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

def power (a b : Peano) (h : a ≠ zero ∨ b ≠ zero) : Peano :=
  match a with
  | zero => zero
  | successor a' =>
    match b with
    | zero => successor zero
    | successor b' => power (successor a') b' (Or.inl (by simp)) * a

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

end Peano

end ZeroMath.Numbers.CardinalNatural
