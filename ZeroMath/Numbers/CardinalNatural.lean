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

def power (a : Peano) : Peano → Peano
  | Nat.zero => successor zero
  | Nat.succ b' => multiply (power a b') a

instance : HPow Peano Peano Peano where
  hPow := power

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

theorem power_add (x y z : Peano) : x ^ (y + z) = x ^ y * x ^ z := by
  induction z with
  | zero =>
    have h1 : y + zero = y := add_zero y
    change x ^ (y + zero) = x ^ y * x ^ zero
    rw [h1]
    have h2 : x ^ zero = successor zero := rfl
    rw [h2]
    have h : x ^ y * successor zero = x ^ y * zero + x ^ y := multiply_succ (x ^ y) zero
    rw [h]
    have hz : x ^ y * zero = zero := multiply_zero (x ^ y)
    rw [hz]
    exact (zero_add (x ^ y)).symm
  | succ z' ih =>
    let z'' : Peano := z'
    have h1 : y + z''.successor = (y + z'').successor := rfl
    change x ^ (y + z''.successor) = x ^ y * x ^ z''.successor
    rw [h1]
    have h2 : x ^ (y + z'').successor = x ^ (y + z'') * x := rfl
    rw [h2]
    rw [ih]
    have h3 : x ^ z''.successor = x ^ z'' * x := rfl
    rw [h3]
    exact multiply_assoc (x ^ y) (x ^ z'') x

theorem power_multiply (x y z : Peano) : x ^ (y * z) = (x ^ y) ^ z := by
  induction z with
  | zero =>
    have h1 : y * zero = zero := multiply_zero y
    change x ^ (y * zero) = (x ^ y) ^ zero
    rw [h1]
    rfl
  | succ z' ih =>
    let z'' : Peano := z'
    have h1 : y * z''.successor = y * z'' + y := multiply_succ y z''
    change x ^ (y * z''.successor) = (x ^ y) ^ z''.successor
    rw [h1]
    have h2 : x ^ (y * z'' + y) = x ^ (y * z'') * x ^ y := power_add x (y * z'') y
    rw [h2]
    rw [ih]
    rfl

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

instance : DecidableEq Peano := inferInstanceAs (DecidableEq Nat)

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

def fromInt (n : Int) (_h : n ≥ 0) : Peano :=
  n.toNat

theorem fromInt_toInt (n : Peano) : ∃ h, fromInt (toInt n) h = n := by
  exact ⟨Int.natCast_nonneg n, rfl⟩

def fromOrdinal : ZeroMath.Numbers.OrdinalNatural.Peano → Peano
  | ZeroMath.Numbers.OrdinalNatural.Peano.one => successor zero
  | ZeroMath.Numbers.OrdinalNatural.Peano.successor n => successor (fromOrdinal n)

def ten : Peano := (10 : Nat)

def AllLessThanTen : ZeroMath.Sequences.List Peano → Prop
  | _root_.List.nil => True
  | _root_.List.cons d ds => d < ten ∧ AllLessThanTen ds

def HasNonZero : ZeroMath.Sequences.List Peano → Prop
  | _root_.List.nil => False
  | _root_.List.cons d ds => d ≠ zero ∨ HasNonZero ds

end Peano

end ZeroMath.Numbers.CardinalNatural
