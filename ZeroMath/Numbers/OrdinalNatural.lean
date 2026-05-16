import ZeroMath.Logic.Trichotomy
namespace ZeroMath.Numbers.OrdinalNatural

inductive Peano where
  | one : Peano
  | successor : Peano → Peano

deriving instance DecidableEq for Peano

def Peano.toNat : Peano → Nat
  | one => 1
  | successor n => n.toNat + 1

def Peano.toInt : Peano → Int
  | one => 1
  | successor n => n.toInt + 1

def Peano.fromNat : (n : Nat) → n ≠ 0 → Peano
  | 0, h => by contradiction
  | 1, _ => Peano.one
  | n + 2, _ => Peano.successor (fromNat (n + 1) Nat.noConfusion)

def Peano.fromInt (n : Int) (h : n > 0) : Peano :=
  fromNat n.toNat (by
    intro hzero
    exact (Int.not_le_of_gt h) (Int.toNat_eq_zero.mp hzero))

theorem Peano.toNat_ne_zero (p : Peano) : p.toNat ≠ 0 := by
  cases p <;> exact Nat.noConfusion

theorem Peano.fromNat_toNat_helper (n : Nat) (h : n ≠ 0) (p : Peano) (heq : p.toNat = n) : fromNat n h = p := by
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

theorem Peano.fromNat_toNat (p : Peano) : ∃ h, fromNat p.toNat h = p := by
  exists Peano.toNat_ne_zero p
  exact fromNat_toNat_helper p.toNat (Peano.toNat_ne_zero p) p rfl

theorem Peano.toNat_fromNat (n : Nat) (h : n ≠ 0) : (fromNat n h).toNat = n := by
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

theorem Peano.toInt_eq_toNat (p : Peano) : p.toInt = p.toNat := by
  induction p with
  | one => rfl
  | successor p ih =>
    simp [Peano.toInt, Peano.toNat, ih]

theorem Peano.toInt_pos (p : Peano) : p.toInt > 0 := by
  rw [Peano.toInt_eq_toNat]
  exact Int.natCast_pos.mpr (Nat.pos_of_ne_zero (Peano.toNat_ne_zero p))

theorem Peano.fromNat_eq_of_eq (n m : Nat) (hn : n ≠ 0) (hm : m ≠ 0) (h : n = m) :
  fromNat n hn = fromNat m hm := by
  subst h
  rfl

theorem Peano.fromInt_toInt (p : Peano) : ∃ h, fromInt p.toInt h = p := by
  exists Peano.toInt_pos p
  unfold fromInt
  have htoNat : p.toInt.toNat = p.toNat := by
    rw [Peano.toInt_eq_toNat, Int.toNat_natCast]
  obtain ⟨h_toNat_ne_zero, h_fromNat⟩ := Peano.fromNat_toNat p
  exact (Peano.fromNat_eq_of_eq p.toInt.toNat p.toNat _ h_toNat_ne_zero htoNat).trans
    h_fromNat

theorem Peano.toInt_fromInt (x : Int) (h : x > 0) : (Peano.fromInt x h).toInt = x := by
  unfold Peano.fromInt
  rw [Peano.toInt_eq_toNat]
  rw [Peano.toNat_fromNat]
  have h2 : 0 ≤ x := Int.le_of_lt h
  exact Int.toNat_of_nonneg h2

inductive Peano.LessThan (a : Peano) : Peano → Prop where
  | base : Peano.LessThan a (Peano.successor a)
  | step {b : Peano} : Peano.LessThan a b → Peano.LessThan a (Peano.successor b)

instance : LT Peano where
  lt := Peano.LessThan

def Peano.LessThanOrEqual (a b : Peano) : Prop :=
  Peano.LessThan a b ∨ a = b

instance : LE Peano where
  le := Peano.LessThanOrEqual



namespace Peano

def predecessor (a : Peano) (h : a ≠ one) : Peano :=
  match a with
  | one => False.elim (h rfl)
  | successor b => b

def add (a : Peano) : Peano → Peano
  | one => successor a
  | successor b => successor (add a b)

instance : Add Peano where
  add := add

theorem add_one (a : Peano) : a + one = successor a := by rfl

theorem one_add (a : Peano) : one + a = successor a := by
  induction a with
  | one => rfl
  | successor a ih =>
    show successor (one + a) = successor (successor a)
    rw [ih]

theorem add_succ (a b : Peano) : a + successor b = successor (a + b) := by rfl

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

def isDivisible (a b : Peano) : Prop := ∃ c, b * c = a

def divide_rec (a b orig_a : Peano) : Peano :=
  match a with
  | one => one
  | successor a' =>
    if b * successor a' = orig_a then
      successor a'
    else
      divide_rec a' b orig_a

def divide (a b : Peano) (_ : isDivisible a b) : Peano :=
  divide_rec a b a

theorem le_of_lt_succ {a b : Peano} (h : a < successor b) : a ≤ b := by
  generalize hb : successor b = sb at h
  induction h generalizing b with
  | base =>
    cases hb
    exact Or.inr rfl
  | step hlt _ =>
    cases hb
    exact Or.inl hlt

theorem divide_rec_correct (a b orig_a c : Peano) (h : b * c = orig_a) (hle : c ≤ a) : b * divide_rec a b orig_a = orig_a := by
  induction a with
  | one =>
    cases hle with
    | inl hlt => cases not_lt_one c hlt
    | inr heq =>
      subst heq
      unfold divide_rec
      exact h
  | successor a' ih =>
    unfold divide_rec
    split
    · assumption
    · next h_neq =>
      have hc : c ≤ a' := by
        cases hle with
        | inl hlt =>
          exact le_of_lt_succ hlt
        | inr heq =>
          subst heq
          contradiction
      exact ih hc

theorem le_multiply_right (a b : Peano) : a ≤ b * a := by
  induction b with
  | one =>
    rw [one_multiply]
    exact Or.inr rfl
  | successor b _ =>
    rw [succ_multiply]
    exact Or.inl (lt_add_right _ _)

theorem divide_correct (a b : Peano) (h : isDivisible a b) : b * divide a b h = a := by
  rcases h with ⟨c, hc⟩
  unfold divide
  have hc_le_a : c ≤ a := by
    have h1 : c ≤ b * c := le_multiply_right c b
    rw [hc] at h1
    exact h1
  exact divide_rec_correct a b a c hc hc_le_a

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

theorem divide_multiply_eq (x y : Peano) : ∃ h, divide (y * x) y h = x :=
  ⟨⟨x, rfl⟩, by
    have h_divide_correct := divide_correct (y * x) y ⟨x, rfl⟩
    exact multiply_cancel_left y _ x h_divide_correct⟩


theorem divide_divide_eq_divide_multiply_h2 {x y z : Peano} (h1 : isDivisible x (y * z)) : isDivisible x y := by
  cases h1 with
  | intro c hc =>
    exact ⟨z * c, by rw [←multiply_assoc, hc]⟩

theorem divide_divide_eq_divide_multiply_h3 {x y z : Peano} (h1 : isDivisible x (y * z)) : ∃ h2, isDivisible (divide x y h2) z := by
  have h2 := divide_divide_eq_divide_multiply_h2 h1
  exact ⟨h2, by
    cases h1 with
    | intro c hc =>
      exact ⟨c, by
        have h_div_y := divide_correct x y h2
        have h_eq : y * (z * c) = y * divide x y h2 := by
          rw [h_div_y, ←multiply_assoc, hc]
        exact multiply_cancel_left y _ _ h_eq⟩⟩

theorem divide_add (x y z : Peano) (h : isDivisible x z) (h2 : isDivisible y z) :
  ∃ h3, divide x z h + divide y z h2 = divide (x + y) z h3 := by
  have h3 : isDivisible (x + y) z := by
    cases h with
    | intro c1 hc1 =>
      cases h2 with
      | intro c2 hc2 =>
        exists c1 + c2
        rw [multiply_add, hc1, hc2]
  exists h3
  have h4 : z * (divide x z h + divide y z h2) = z * divide (x + y) z h3 := by
    rw [multiply_add, divide_correct, divide_correct, divide_correct]
  exact multiply_cancel_left z _ _ h4

theorem divide_divide_eq_divide_multiply (x y z : Peano) (h1 : isDivisible x (y * z)) :
  ∃ h2 h3, divide x (y * z) h1 = divide (divide x y h2) z h3 := by
  have h2 := divide_divide_eq_divide_multiply_h2 h1
  have ⟨_, h3⟩ := divide_divide_eq_divide_multiply_h3 h1
  have H1 := divide_correct x (y * z) h1
  have H2 := divide_correct x y h2
  have H3 := divide_correct (divide x y h2) z h3

  have H4 : y * (z * divide (divide x y h2) z h3) = y * divide x y h2 := by rw [H3]
  have H5 : y * divide x y h2 = x := H2
  have H6 : y * (z * divide (divide x y h2) z h3) = x := by rw [H4, H5]

  have H7 : (y * z) * divide (divide x y h2) z h3 = x := by rw [multiply_assoc y z, H6]

  have H8 : (y * z) * divide x (y * z) h1 = (y * z) * divide (divide x y h2) z h3 := by rw [H1, H7]

  exact ⟨h2, h3, multiply_cancel_left (y * z) _ _ H8⟩

theorem multiply_divide_assoc_h {x y z : Peano} (h : isDivisible y z) : isDivisible (x * y) z := by
  rcases h with ⟨c, hc⟩
  exact ⟨x * c, by
    rw [←multiply_assoc]
    have h1 : z * x = x * z := multiply_comm z x
    rw [h1]
    rw [multiply_assoc]
    rw [hc]⟩

theorem multiply_divide_assoc (x y z : Peano) (h : isDivisible y z) :
  ∃ h2, x * divide y z h = divide (x * y) z h2 := by
  have hc := divide_correct y z h
  have hc2 := divide_correct (x * y) z (multiply_divide_assoc_h h)
  have h1 : z * (x * divide y z h) = x * y := by
    rw [←multiply_assoc]
    have hcomm : z * x = x * z := multiply_comm z x
    rw [hcomm]
    rw [multiply_assoc]
    rw [hc]
  have h2 : z * divide (x * y) z (multiply_divide_assoc_h h) = x * y := hc2
  have h3 : z * (x * divide y z h) = z * divide (x * y) z (multiply_divide_assoc_h h) := by
    rw [h1, h2]
  exact ⟨multiply_divide_assoc_h h, multiply_cancel_left z _ _ h3⟩

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
    rw [ih]
    rw [multiply_assoc]
    have h1 : y ^ z * (x * y) = (y ^ z * x) * y := (multiply_assoc _ _ _).symm
    rw [h1]
    have h2 : y ^ z * x = x * y ^ z := multiply_comm _ _
    rw [h2]
    have h3 : x * y ^ z * y = x * (y ^ z * y) := multiply_assoc _ _ _
    rw [h3]
    have h4 : x ^ z * (x * (y ^ z * y)) = (x ^ z * x) * (y ^ z * y) := (multiply_assoc _ _ _).symm
    rw [h4]

def isPower (e x : Peano) : Prop := ∃ y, y ^ e = x

def root_rec (a e orig_x : Peano) : Peano :=
  match a with
  | one => one
  | successor a' =>
    if (successor a') ^ e = orig_x then
      successor a'
    else
      root_rec a' e orig_x

def root (e x : Peano) (_ : isPower e x) : Peano :=
  root_rec x e x

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

theorem divide_subtract_distrib {x y z : Peano}
  (h1 : isDivisible x z) (h2 : isDivisible y z) (h3 : x > y) :
  ∃ h4 h5, divide (subtract x y h3) z h4 = subtract (divide x z h1) (divide y z h2) h5 := by
  have Hx : z * divide x z h1 = x := divide_correct x z h1
  have Hy : z * divide y z h2 = y := divide_correct y z h2
  have h5 : divide x z h1 > divide y z h2 := by
    have h_lt : z * divide y z h2 < z * divide x z h1 := by
      rw [Hy, Hx]
      exact h3
    have h_lt_comm : divide y z h2 * z < divide x z h1 * z := by
      rw [multiply_comm (divide y z h2) z, multiply_comm (divide x z h1) z]
      exact h_lt
    exact lt_multiply_right_cancel h_lt_comm
  have h_mul_sub := multiply_subtract z (divide x z h1) (divide y z h2) h5
  rcases h_mul_sub with ⟨h_mul_sub_wit, h_mul_sub_eq⟩
  have h_mul_sub_eq2 : z * subtract (divide x z h1) (divide y z h2) h5 = subtract x y h3 := by
    rw [h_mul_sub_eq]
    exact subtract_eq_of_eq h_mul_sub_wit h3 Hx Hy
  have h4 : isDivisible (subtract x y h3) z := by
    exact ⟨subtract (divide x z h1) (divide y z h2) h5, h_mul_sub_eq2⟩
  have h_div_eq : divide (subtract x y h3) z h4 = subtract (divide x z h1) (divide y z h2) h5 := by
    have Hx_sub_y : z * divide (subtract x y h3) z h4 = subtract x y h3 := divide_correct (subtract x y h3) z h4
    have H_mul_eq : z * divide (subtract x y h3) z h4 = z * subtract (divide x z h1) (divide y z h2) h5 := by
      rw [Hx_sub_y, h_mul_sub_eq2]
    exact multiply_cancel_left z _ _ H_mul_eq
  exact ⟨h4, h5, h_div_eq⟩

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

theorem root_rec_correct (a e orig_x y : Peano) (h : y ^ e = orig_x) (hle : y ≤ a) : (root_rec a e orig_x) ^ e = orig_x := by
  induction a with
  | one =>
    cases hle with
    | inl hlt => cases not_lt_one y hlt
    | inr heq =>
      subst heq
      unfold root_rec
      exact h
  | successor a' ih =>
    unfold root_rec
    split
    · assumption
    · next h_neq =>
      have hy : y ≤ a' := by
        cases hle with
        | inl hlt =>
          exact le_of_lt_succ hlt
        | inr heq =>
          subst heq
          contradiction
      exact ih hy

theorem root_correct (e x : Peano) (h : isPower e x) : (root e x h) ^ e = x := by
  rcases h with ⟨y, hy⟩
  unfold root
  have hy_le_x : y ≤ x := by
    have h1 : y ≤ y ^ e := le_power y e
    rw [hy] at h1
    exact h1
  exact root_rec_correct x e x y hy hy_le_x

theorem root_power_eq (e x : Peano) : ∃ h, root e (x ^ e) h = x := by
  have hex : isPower e (x ^ e) := ⟨x, rfl⟩
  exact ⟨hex, by
    have h1 := root_correct e (x ^ e) hex

    exact power_cancel_left e _ x h1⟩

end Peano

end ZeroMath.Numbers.OrdinalNatural
