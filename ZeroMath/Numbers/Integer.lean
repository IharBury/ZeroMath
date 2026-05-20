import ZeroMath.Numbers.OrdinalNatural

namespace ZeroMath.Numbers.Integer

inductive Peano where
  | positive : OrdinalNatural.Peano → Peano
  | zero : Peano
  | negative : OrdinalNatural.Peano → Peano

deriving instance DecidableEq for Peano

def Peano.toInt : Peano → Int
  | positive n => n.toNat
  | zero => 0
  | negative n => - (n.toNat : Int)

def Peano.negate : Peano → Peano
  | positive n => negative n
  | zero => zero
  | negative n => positive n

instance : Neg Peano where
  neg := Peano.negate

inductive Peano.LessThan : Peano → Peano → Prop where
  | negative_less_than_zero {n : OrdinalNatural.Peano} : Peano.LessThan (negative n) zero
  | zero_less_than_positive {n : OrdinalNatural.Peano} : Peano.LessThan zero (positive n)
  | negative_less_than_positive {n m : OrdinalNatural.Peano} : Peano.LessThan (negative n) (positive m)
  | positive_less_than_positive {n m : OrdinalNatural.Peano} : n < m → Peano.LessThan (positive n) (positive m)
  | negative_less_than_negative {n m : OrdinalNatural.Peano} : m < n → Peano.LessThan (negative n) (negative m)

instance : LT Peano where
  lt := Peano.LessThan

def Peano.LessThanOrEqual (a b : Peano) : Prop :=
  Peano.LessThan a b ∨ a = b

instance : LE Peano where
  le := Peano.LessThanOrEqual

def Peano.successor : Peano → Peano
  | negative (OrdinalNatural.Peano.successor n) => negative n
  | negative OrdinalNatural.Peano.one => zero
  | zero => positive OrdinalNatural.Peano.one
  | positive n => positive (OrdinalNatural.Peano.successor n)

def Peano.predecessor : Peano → Peano
  | positive (OrdinalNatural.Peano.successor n) => positive n
  | positive OrdinalNatural.Peano.one => zero
  | zero => negative OrdinalNatural.Peano.one
  | negative n => negative (OrdinalNatural.Peano.successor n)

def Peano.add (a : Peano) : Peano → Peano
  | zero => a
  | positive OrdinalNatural.Peano.one => successor a
  | positive (OrdinalNatural.Peano.successor n) => successor (add a (positive n))
  | negative OrdinalNatural.Peano.one => predecessor a
  | negative (OrdinalNatural.Peano.successor n) => predecessor (add a (negative n))

instance : Add Peano where
  add := Peano.add

def Peano.subtract (a : Peano) : Peano → Peano
  | zero => a
  | positive OrdinalNatural.Peano.one => predecessor a
  | positive (OrdinalNatural.Peano.successor n) => predecessor (subtract a (positive n))
  | negative OrdinalNatural.Peano.one => successor a
  | negative (OrdinalNatural.Peano.successor n) => successor (subtract a (negative n))

instance : Sub Peano where
  sub := Peano.subtract

def Peano.multiply (a : Peano) : Peano → Peano
  | zero => zero
  | positive OrdinalNatural.Peano.one => a
  | positive (OrdinalNatural.Peano.successor n) => multiply a (positive n) + a
  | negative OrdinalNatural.Peano.one => -a
  | negative (OrdinalNatural.Peano.successor n) => multiply a (negative n) - a

instance : Mul Peano where
  mul := Peano.multiply

theorem Peano.sub_zero (a : Peano) : a - zero = a := by
  have h : a - zero = Peano.subtract a zero := rfl
  rw [h]
  rw [Peano.subtract.eq_def]

theorem Peano.sub_pos_one (a : Peano) : a - positive OrdinalNatural.Peano.one = predecessor a := by
  have h : a - positive OrdinalNatural.Peano.one = Peano.subtract a (positive OrdinalNatural.Peano.one) := rfl
  rw [h]
  rw [Peano.subtract.eq_def]

theorem Peano.sub_pos_succ (a : Peano) (n : OrdinalNatural.Peano) : a - positive (OrdinalNatural.Peano.successor n) = predecessor (a - positive n) := by
  have h1 : a - positive (OrdinalNatural.Peano.successor n) = Peano.subtract a (positive (OrdinalNatural.Peano.successor n)) := rfl
  have h2 : a - positive n = Peano.subtract a (positive n) := rfl
  rw [h1, h2]
  rw [Peano.subtract.eq_def]

theorem Peano.sub_neg_one (a : Peano) : a - negative OrdinalNatural.Peano.one = successor a := by
  have h : a - negative OrdinalNatural.Peano.one = Peano.subtract a (negative OrdinalNatural.Peano.one) := rfl
  rw [h]
  rw [Peano.subtract.eq_def]

theorem Peano.sub_neg_succ (a : Peano) (n : OrdinalNatural.Peano) : a - negative (OrdinalNatural.Peano.successor n) = successor (a - negative n) := by
  have h1 : a - negative (OrdinalNatural.Peano.successor n) = Peano.subtract a (negative (OrdinalNatural.Peano.successor n)) := rfl
  have h2 : a - negative n = Peano.subtract a (negative n) := rfl
  rw [h1, h2]
  rw [Peano.subtract.eq_def]

theorem Peano.add_pos_one (a : Peano) : a + positive OrdinalNatural.Peano.one = successor a := by
  have h : a + positive OrdinalNatural.Peano.one = Peano.add a (positive OrdinalNatural.Peano.one) := rfl
  rw [h]
  rw [Peano.add.eq_def]

theorem Peano.add_pos_succ (a : Peano) (n : OrdinalNatural.Peano) : a + positive (OrdinalNatural.Peano.successor n) = successor (a + positive n) := by
  have h1 : a + positive (OrdinalNatural.Peano.successor n) = Peano.add a (positive (OrdinalNatural.Peano.successor n)) := rfl
  have h2 : a + positive n = Peano.add a (positive n) := rfl
  rw [h1, h2]
  rw [Peano.add.eq_def]

theorem Peano.add_neg_one (a : Peano) : a + negative OrdinalNatural.Peano.one = predecessor a := by
  have h : a + negative OrdinalNatural.Peano.one = Peano.add a (negative OrdinalNatural.Peano.one) := rfl
  rw [h]
  rw [Peano.add.eq_def]

theorem Peano.add_neg_succ (a : Peano) (n : OrdinalNatural.Peano) : a + negative (OrdinalNatural.Peano.successor n) = predecessor (a + negative n) := by
  have h1 : a + negative (OrdinalNatural.Peano.successor n) = Peano.add a (negative (OrdinalNatural.Peano.successor n)) := rfl
  have h2 : a + negative n = Peano.add a (negative n) := rfl
  rw [h1, h2]
  rw [Peano.add.eq_def]

theorem Peano.add_zero (a : Peano) : a + zero = a := by
  have h : a + zero = Peano.add a zero := rfl
  rw [h]
  rw [Peano.add.eq_def]

theorem Peano.zero_add (a : Peano) : zero + a = a := by
  cases a with
  | zero =>
    rw [Peano.add_zero]
  | positive n =>
    induction n with
    | one =>
      rw [Peano.add_pos_one, Peano.successor]
    | successor n ih =>
      rw [Peano.add_pos_succ, ih, Peano.successor]
  | negative n =>
    induction n with
    | one =>
      rw [Peano.add_neg_one, Peano.predecessor]
    | successor n ih =>
      rw [Peano.add_neg_succ, ih, Peano.predecessor]

theorem Peano.succ_pred (a : Peano) : successor (predecessor a) = a := by
  cases a with
  | zero => rfl
  | positive n =>
    cases n with
    | one => rfl
    | successor n => rfl
  | negative n =>
    cases n with
    | one => rfl
    | successor n => rfl

theorem Peano.pred_succ (a : Peano) : predecessor (successor a) = a := by
  cases a with
  | zero => rfl
  | positive n =>
    cases n with
    | one => rfl
    | successor n => rfl
  | negative n =>
    cases n with
    | one => rfl
    | successor n => rfl

theorem Peano.succ_add (a b : Peano) : successor a + b = successor (a + b) := by
  cases b with
  | zero =>
    rw [add_zero, add_zero]
  | positive n =>
    induction n with
    | one =>
      rw [add_pos_one, add_pos_one]
    | successor n ih =>
      rw [add_pos_succ, add_pos_succ, ih]
  | negative n =>
    induction n with
    | one =>
      rw [add_neg_one, add_neg_one, succ_pred, pred_succ]
    | successor n ih =>
      rw [add_neg_succ, add_neg_succ, ih, succ_pred, pred_succ]

theorem Peano.pred_add (a b : Peano) : predecessor a + b = predecessor (a + b) := by
  cases b with
  | zero =>
    rw [add_zero, add_zero]
  | positive n =>
    induction n with
    | one =>
      rw [add_pos_one, add_pos_one, pred_succ, succ_pred]
    | successor n ih =>
      rw [add_pos_succ, add_pos_succ, ih, pred_succ, succ_pred]
  | negative n =>
    induction n with
    | one =>
      rw [add_neg_one, add_neg_one]
    | successor n ih =>
      rw [add_neg_succ, add_neg_succ, ih]

theorem Peano.succ_sub (a b : Peano) : successor a - b = successor (a - b) := by
  induction b with
  | zero =>
    rw [Peano.sub_zero, Peano.sub_zero]
  | positive n =>
    induction n with
    | one =>
      rw [Peano.sub_pos_one, Peano.sub_pos_one]
      rw [Peano.pred_succ, Peano.succ_pred]
    | successor n ih =>
      rw [Peano.sub_pos_succ, Peano.sub_pos_succ]
      rw [ih, Peano.pred_succ, Peano.succ_pred]
  | negative n =>
    induction n with
    | one =>
      rw [Peano.sub_neg_one, Peano.sub_neg_one]
    | successor n ih =>
      rw [Peano.sub_neg_succ, Peano.sub_neg_succ]
      rw [ih]

theorem Peano.pred_sub (a b : Peano) : predecessor a - b = predecessor (a - b) := by
  induction b with
  | zero =>
    rw [Peano.sub_zero, Peano.sub_zero]
  | positive n =>
    induction n with
    | one =>
      rw [Peano.sub_pos_one, Peano.sub_pos_one]
    | successor n ih =>
      rw [Peano.sub_pos_succ, Peano.sub_pos_succ]
      rw [ih]
  | negative n =>
    induction n with
    | one =>
      rw [Peano.sub_neg_one, Peano.sub_neg_one]
      rw [Peano.succ_pred, Peano.pred_succ]
    | successor n ih =>
      rw [Peano.sub_neg_succ, Peano.sub_neg_succ]
      rw [ih, Peano.succ_pred, Peano.pred_succ]

theorem Peano.lt_trans {a b c : Peano} (h1 : a < b) (h2 : b < c) : a < c := by
  cases h1 with
  | negative_less_than_zero =>
    cases h2 with
    | zero_less_than_positive => exact Peano.LessThan.negative_less_than_positive
  | zero_less_than_positive =>
    cases h2 with
    | positive_less_than_positive h => exact Peano.LessThan.zero_less_than_positive
  | negative_less_than_positive =>
    cases h2 with
    | positive_less_than_positive h => exact Peano.LessThan.negative_less_than_positive
  | positive_less_than_positive h =>
    cases h2 with
    | positive_less_than_positive h' => exact Peano.LessThan.positive_less_than_positive (OrdinalNatural.Peano.lt_trans h h')
  | negative_less_than_negative h =>
    cases h2 with
    | negative_less_than_zero => exact Peano.LessThan.negative_less_than_zero
    | negative_less_than_positive => exact Peano.LessThan.negative_less_than_positive
    | negative_less_than_negative h' => exact Peano.LessThan.negative_less_than_negative (OrdinalNatural.Peano.lt_trans h' h)

theorem Peano.le_trans {a b c : Peano} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  cases h1 with
  | inl h1_lt =>
    cases h2 with
    | inl h2_lt => exact Or.inl (Peano.lt_trans h1_lt h2_lt)
    | inr h2_eq =>
      rw [← h2_eq]
      exact Or.inl h1_lt
  | inr h1_eq =>
    rw [h1_eq]
    exact h2

theorem Peano.add_comm (a b : Peano) : a + b = b + a := by
  cases b with
  | zero =>
    rw [add_zero, zero_add]
  | positive n =>
    induction n with
    | one =>
      rw [add_pos_one]
      have h1 : positive OrdinalNatural.Peano.one + a = successor (zero + a) := by
        have h_succ : positive OrdinalNatural.Peano.one = successor zero := rfl
        rw [h_succ, succ_add]
      rw [h1, zero_add]
    | successor n ih =>
      rw [add_pos_succ]
      have h1 : positive n.successor + a = successor (positive n + a) := by
        have h_succ : positive n.successor = successor (positive n) := rfl
        rw [h_succ, succ_add]
      rw [h1, ih]
  | negative n =>
    induction n with
    | one =>
      rw [add_neg_one]
      have h1 : negative OrdinalNatural.Peano.one + a = predecessor (zero + a) := by
        have h_pred : negative OrdinalNatural.Peano.one = predecessor zero := rfl
        rw [h_pred, pred_add]
      rw [h1, zero_add]
    | successor n ih =>
      rw [add_neg_succ]
      have h1 : negative n.successor + a = predecessor (negative n + a) := by
        have h_pred : negative n.successor = predecessor (negative n) := rfl
        rw [h_pred, pred_add]
      rw [h1, ih]

theorem Peano.not_lt_self (x : Peano) : ¬ (x < x) := by
  intro h
  cases h with
  | positive_less_than_positive h' =>
    exact OrdinalNatural.Peano.not_lt_self _ h'
  | negative_less_than_negative h' =>
    exact OrdinalNatural.Peano.not_lt_self _ h'

theorem Peano.not_lt_of_lt {x y : Peano} (h : x < y) : ¬ (y < x) := by
  intro h2
  have h3 := lt_trans h h2
  exact not_lt_self x h3

theorem Peano.ne_of_lt {x y : Peano} (h : x < y) : x ≠ y := by
  intro heq
  subst heq
  exact not_lt_self x h

theorem Peano.trichotomy_or (x y : Peano) : x < y ∨ x = y ∨ y < x := by
  cases x with
  | zero =>
    cases y with
    | zero => exact Or.inr (Or.inl rfl)
    | positive m => exact Or.inl LessThan.zero_less_than_positive
    | negative m => exact Or.inr (Or.inr LessThan.negative_less_than_zero)
  | positive n =>
    cases y with
    | zero => exact Or.inr (Or.inr LessThan.zero_less_than_positive)
    | negative m => exact Or.inr (Or.inr LessThan.negative_less_than_positive)
    | positive m =>
      cases OrdinalNatural.Peano.trichotomy_or n m with
      | inl h => exact Or.inl (LessThan.positive_less_than_positive h)
      | inr h =>
        cases h with
        | inl h =>
          subst h
          exact Or.inr (Or.inl rfl)
        | inr h =>
          exact Or.inr (Or.inr (LessThan.positive_less_than_positive h))
  | negative n =>
    cases y with
    | zero => exact Or.inl LessThan.negative_less_than_zero
    | positive m => exact Or.inl LessThan.negative_less_than_positive
    | negative m =>
      cases OrdinalNatural.Peano.trichotomy_or n m with
      | inl h => exact Or.inr (Or.inr (LessThan.negative_less_than_negative h))
      | inr h =>
        cases h with
        | inl h =>
          subst h
          exact Or.inr (Or.inl rfl)
        | inr h =>
          exact Or.inl (LessThan.negative_less_than_negative h)

theorem Peano.add_sub_cancel (a b : Peano) : a + b - b = a := by
  induction b with
  | zero =>
    rw [Peano.add_zero, Peano.sub_zero]
  | positive n =>
    induction n with
    | one =>
      rw [Peano.add_pos_one, Peano.sub_pos_one, Peano.pred_succ]
    | successor n ih =>
      rw [Peano.add_pos_succ, Peano.sub_pos_succ]
      rw [Peano.succ_sub]
      rw [Peano.pred_succ]
      exact ih
  | negative n =>
    induction n with
    | one =>
      rw [Peano.add_neg_one, Peano.sub_neg_one, Peano.succ_pred]
    | successor n ih =>
      rw [Peano.add_neg_succ, Peano.sub_neg_succ]
      rw [Peano.pred_sub]
      rw [Peano.succ_pred]
      exact ih

theorem Peano.sub_add_cancel (a b : Peano) : a - b + b = a := by
  induction b with
  | zero =>
    rw [Peano.sub_zero, Peano.add_zero]
  | positive n =>
    induction n with
    | one =>
      rw [Peano.sub_pos_one, Peano.add_pos_one, Peano.succ_pred]
    | successor n ih =>
      rw [Peano.sub_pos_succ, Peano.add_pos_succ]
      rw [Peano.pred_add]
      rw [Peano.succ_pred]
      exact ih
  | negative n =>
    induction n with
    | one =>
      rw [Peano.sub_neg_one, Peano.add_neg_one, Peano.pred_succ]
    | successor n ih =>
      rw [Peano.sub_neg_succ, Peano.add_neg_succ]
      rw [Peano.succ_add]
      rw [Peano.pred_succ]
      exact ih

theorem Peano.trichotomy (x y : Peano) : ZeroMath.Logic.Trichotomy (x < y) (x = y) (y < x) := by
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

theorem Peano.add_succ (a b : Peano) : a + successor b = successor (a + b) := by
  cases b with
  | zero =>
    have h1 : successor zero = positive OrdinalNatural.Peano.one := rfl
    rw [h1, add_pos_one, add_zero]
  | positive n =>
    cases n with
    | one =>
      have h1 : successor (positive OrdinalNatural.Peano.one) = positive (OrdinalNatural.Peano.successor OrdinalNatural.Peano.one) := rfl
      rw [h1, add_pos_succ, add_pos_one]
    | successor n =>
      have h1 : successor (positive (OrdinalNatural.Peano.successor n)) = positive (OrdinalNatural.Peano.successor (OrdinalNatural.Peano.successor n)) := rfl
      rw [h1, add_pos_succ, add_pos_succ]
  | negative n =>
    cases n with
    | one =>
      have h1 : successor (negative OrdinalNatural.Peano.one) = zero := rfl
      rw [h1, add_zero, add_neg_one, succ_pred]
    | successor n =>
      have h1 : successor (negative (OrdinalNatural.Peano.successor n)) = negative n := rfl
      rw [h1, add_neg_succ, succ_pred]

theorem Peano.add_pred (a b : Peano) : a + predecessor b = predecessor (a + b) := by
  cases b with
  | zero =>
    have h1 : predecessor zero = negative OrdinalNatural.Peano.one := rfl
    rw [h1, add_neg_one, add_zero]
  | positive n =>
    cases n with
    | one =>
      have h1 : predecessor (positive OrdinalNatural.Peano.one) = zero := rfl
      rw [h1, add_zero, add_pos_one, pred_succ]
    | successor n =>
      have h1 : predecessor (positive (OrdinalNatural.Peano.successor n)) = positive n := rfl
      rw [h1, add_pos_succ, pred_succ]
  | negative n =>
    cases n with
    | one =>
      have h1 : predecessor (negative OrdinalNatural.Peano.one) = negative (OrdinalNatural.Peano.successor OrdinalNatural.Peano.one) := rfl
      rw [h1, add_neg_succ, add_neg_one]
    | successor n =>
      have h1 : predecessor (negative (OrdinalNatural.Peano.successor n)) = negative (OrdinalNatural.Peano.successor (OrdinalNatural.Peano.successor n)) := rfl
      rw [h1, add_neg_succ, add_neg_succ]

theorem Peano.add_assoc (a b c : Peano) : a + b + c = a + (b + c) := by
  induction c with
  | zero =>
    rw [add_zero, add_zero]
  | positive n =>
    induction n with
    | one =>
      rw [add_pos_one, add_pos_one]
      rw [add_succ]
    | successor n ih =>
      rw [add_pos_succ, add_pos_succ]
      rw [add_succ, ih]
  | negative n =>
    induction n with
    | one =>
      rw [add_neg_one, add_neg_one]
      rw [add_pred]
    | successor n ih =>
      rw [add_neg_succ, add_neg_succ]
      rw [add_pred, ih]

theorem Peano.add_neg_self (a : Peano) : a + -a = zero := by
  cases a with
  | zero =>
    have h1 : -zero = zero := rfl
    rw [h1, add_zero]
  | positive n =>
    induction n with
    | one =>
      have h1 : -(positive OrdinalNatural.Peano.one) = negative OrdinalNatural.Peano.one := rfl
      rw [h1, add_neg_one]
      rfl
    | successor n ih =>
      have h1 : -(positive n.successor) = negative n.successor := rfl
      rw [h1, add_neg_succ]
      have h2 : positive n.successor + negative n = successor (positive n + negative n) := by
        have h_succ : positive n.successor = successor (positive n) := rfl
        rw [h_succ, succ_add]
      rw [h2, pred_succ]
      have h3 : -(positive n) = negative n := rfl
      have h4 : positive n + negative n = positive n + -(positive n) := by rw [h3]
      rw [h4]
      exact ih
  | negative n =>
    induction n with
    | one =>
      have h1 : -(negative OrdinalNatural.Peano.one) = positive OrdinalNatural.Peano.one := rfl
      rw [h1, add_pos_one]
      rfl
    | successor n ih =>
      have h1 : -(negative n.successor) = positive n.successor := rfl
      rw [h1, add_pos_succ]
      have h2 : negative n.successor + positive n = predecessor (negative n + positive n) := by
        have h_pred : negative n.successor = predecessor (negative n) := rfl
        rw [h_pred, pred_add]
      rw [h2, succ_pred]
      have h3 : -(negative n) = positive n := rfl
      have h4 : negative n + positive n = negative n + -(negative n) := by rw [h3]
      rw [h4]
      exact ih

theorem Peano.neg_add_self (a : Peano) : -a + a = zero := by
  rw [add_comm, add_neg_self]

theorem Peano.mul_pos_one (a : Peano) : a * positive OrdinalNatural.Peano.one = a := by
  have h : a * positive OrdinalNatural.Peano.one = multiply a (positive OrdinalNatural.Peano.one) := rfl
  rw [h]
  rw [Peano.multiply.eq_def]

theorem Peano.mul_pos_succ (a : Peano) (n : OrdinalNatural.Peano) : a * positive n.successor = a * positive n + a := by
  have h1 : a * positive n.successor = multiply a (positive n.successor) := rfl
  have h2 : a * positive n = multiply a (positive n) := rfl
  rw [h1, h2]
  rw [Peano.multiply.eq_def]

theorem Peano.mul_neg_one (a : Peano) : a * negative OrdinalNatural.Peano.one = -a := by
  have h : a * negative OrdinalNatural.Peano.one = multiply a (negative OrdinalNatural.Peano.one) := rfl
  rw [h]
  rw [Peano.multiply.eq_def]

theorem Peano.mul_neg_succ (a : Peano) (n : OrdinalNatural.Peano) : a * negative n.successor = a * negative n - a := by
  have h1 : a * negative n.successor = multiply a (negative n.successor) := rfl
  have h2 : a * negative n = multiply a (negative n) := rfl
  rw [h1, h2]
  rw [Peano.multiply.eq_def]

theorem Peano.mul_zero (a : Peano) : a * zero = zero := by
  have h : a * zero = multiply a zero := rfl
  rw [h]
  rw [Peano.multiply.eq_def]

theorem Peano.zero_mul (a : Peano) : zero * a = zero := by
  cases a with
  | zero =>
    rw [mul_zero]
  | positive n =>
    induction n with
    | one =>
      rw [mul_pos_one]
    | successor n ih =>
      rw [mul_pos_succ]
      rw [ih]
      rw [add_zero]
  | negative n =>
    induction n with
    | one =>
      rw [mul_neg_one]
      have h1 : -zero = zero := rfl
      rw [h1]
    | successor n ih =>
      rw [mul_neg_succ]
      rw [ih]
      rw [sub_zero]

theorem Peano.mul_succ (a b : Peano) : a * successor b = a * b + a := by
  cases b with
  | zero =>
    have h1 : successor zero = positive OrdinalNatural.Peano.one := rfl
    rw [h1, mul_pos_one, mul_zero, zero_add]
  | positive n =>
    cases n with
    | one =>
      have h1 : successor (positive OrdinalNatural.Peano.one) = positive (OrdinalNatural.Peano.successor OrdinalNatural.Peano.one) := rfl
      rw [h1, mul_pos_succ]
    | successor n =>
      have h1 : successor (positive (OrdinalNatural.Peano.successor n)) = positive (OrdinalNatural.Peano.successor (OrdinalNatural.Peano.successor n)) := rfl
      rw [h1, mul_pos_succ]
  | negative n =>
    cases n with
    | one =>
      have h1 : successor (negative OrdinalNatural.Peano.one) = zero := rfl
      rw [h1, mul_zero, mul_neg_one]
      rw [neg_add_self]
    | successor n =>
      have h1 : successor (negative (OrdinalNatural.Peano.successor n)) = negative n := rfl
      rw [h1, mul_neg_succ]
      have hs : a * negative n - a + a = a * negative n := sub_add_cancel (a * negative n) a
      rw [hs]

theorem Peano.sub_eq_add_neg (a b : Peano) : a - b = a + -b := by
  induction b with
  | zero =>
    have h1 : -zero = zero := rfl
    rw [h1, add_zero, sub_zero]
  | positive n =>
    induction n with
    | one =>
      have h1 : -(positive OrdinalNatural.Peano.one) = negative OrdinalNatural.Peano.one := rfl
      rw [h1, sub_pos_one, add_neg_one]
    | successor n ih =>
      have h1 : -(positive n.successor) = negative n.successor := rfl
      rw [h1, sub_pos_succ, add_neg_succ]
      have h2 : -(positive n) = negative n := rfl
      have h3 : a - positive n = a + negative n := by
        rw [← h2]
        exact ih
      rw [h3]
  | negative n =>
    induction n with
    | one =>
      have h1 : -(negative OrdinalNatural.Peano.one) = positive OrdinalNatural.Peano.one := rfl
      rw [h1, sub_neg_one, add_pos_one]
    | successor n ih =>
      have h1 : -(negative n.successor) = positive n.successor := rfl
      rw [h1, sub_neg_succ, add_pos_succ]
      have h2 : -(negative n) = positive n := rfl
      have h3 : a - negative n = a + positive n := by
        rw [← h2]
        exact ih
      rw [h3]

theorem Peano.zero_sub (a : Peano) : zero - a = -a := by
  rw [sub_eq_add_neg, zero_add]

theorem Peano.sub_self (a : Peano) : a - a = zero := by
  rw [sub_eq_add_neg, add_neg_self]

theorem Peano.mul_pred (a b : Peano) : a * predecessor b = a * b - a := by
  cases b with
  | zero =>
    have h1 : predecessor zero = negative OrdinalNatural.Peano.one := rfl
    rw [h1, mul_neg_one, mul_zero]
    have h2 : zero - a = -a := zero_sub a
    rw [h2]
  | positive n =>
    cases n with
    | one =>
      have h1 : predecessor (positive OrdinalNatural.Peano.one) = zero := rfl
      rw [h1, mul_zero, mul_pos_one]
      rw [sub_self]
    | successor n =>
      have h1 : predecessor (positive (OrdinalNatural.Peano.successor n)) = positive n := rfl
      rw [h1, mul_pos_succ]
      have hs : a * positive n + a - a = a * positive n := add_sub_cancel (a * positive n) a
      rw [hs]
  | negative n =>
    cases n with
    | one =>
      have h1 : predecessor (negative OrdinalNatural.Peano.one) = negative (OrdinalNatural.Peano.successor OrdinalNatural.Peano.one) := rfl
      rw [h1, mul_neg_succ]
    | successor n =>
      have h1 : predecessor (negative (OrdinalNatural.Peano.successor n)) = negative (OrdinalNatural.Peano.successor (OrdinalNatural.Peano.successor n)) := rfl
      rw [h1, mul_neg_succ]

def Peano.isDivisible (a b : Peano) : Prop :=
  b ≠ zero ∧ ∃ c, b * c = a

def Peano.divide_rec (a b orig_a : Peano) : Peano :=
  match a with
  | Peano.zero => Peano.zero
  | Peano.positive OrdinalNatural.Peano.one =>
    if b * Peano.positive OrdinalNatural.Peano.one = orig_a then Peano.positive OrdinalNatural.Peano.one
    else if b * Peano.negative OrdinalNatural.Peano.one = orig_a then Peano.negative OrdinalNatural.Peano.one
    else Peano.zero
  | Peano.positive (OrdinalNatural.Peano.successor n) =>
    if b * Peano.positive (OrdinalNatural.Peano.successor n) = orig_a then
      Peano.positive (OrdinalNatural.Peano.successor n)
    else if b * Peano.negative (OrdinalNatural.Peano.successor n) = orig_a then
      Peano.negative (OrdinalNatural.Peano.successor n)
    else
      divide_rec (Peano.positive n) b orig_a
  | Peano.negative OrdinalNatural.Peano.one =>
    if b * Peano.positive OrdinalNatural.Peano.one = orig_a then Peano.positive OrdinalNatural.Peano.one
    else if b * Peano.negative OrdinalNatural.Peano.one = orig_a then Peano.negative OrdinalNatural.Peano.one
    else Peano.zero
  | Peano.negative (OrdinalNatural.Peano.successor n) =>
    if b * Peano.positive (OrdinalNatural.Peano.successor n) = orig_a then
      Peano.positive (OrdinalNatural.Peano.successor n)
    else if b * Peano.negative (OrdinalNatural.Peano.successor n) = orig_a then
      Peano.negative (OrdinalNatural.Peano.successor n)
    else
      divide_rec (Peano.negative n) b orig_a

def Peano.divide (a b : Peano) (_ : isDivisible a b) : Peano :=
  divide_rec a b a

namespace Peano

theorem toInt_successor (a : Peano) : (successor a).toInt = a.toInt + 1 := by
  cases a with
  | zero => rfl
  | positive n => cases n <;> rfl
  | negative n =>
    cases n with
    | one => rfl
    | successor n =>
      simp [successor, toInt, ZeroMath.Numbers.OrdinalNatural.Peano.toNat] <;> omega

theorem toInt_predecessor (a : Peano) : (predecessor a).toInt = a.toInt - 1 := by
  cases a with
  | zero => rfl
  | positive n =>
    cases n with
    | one => rfl
    | successor n =>
      simp [predecessor, toInt, ZeroMath.Numbers.OrdinalNatural.Peano.toNat] <;> omega
  | negative n =>
    cases n with
    | one => rfl
    | successor n =>
      simp [predecessor, toInt, ZeroMath.Numbers.OrdinalNatural.Peano.toNat] <;> omega

theorem toInt_negate (a : Peano) : (-a).toInt = -a.toInt := by
  cases a with
  | zero => rfl
  | positive n => rfl
  | negative n =>
    simp [Neg.neg, Peano.negate, toInt]
    exact (Int.neg_neg (n.toNat : Int)).symm

theorem toInt_add (a b : Peano) : (a + b).toInt = a.toInt + b.toInt := by
  induction b with
  | zero => rw [add_zero]; simp [toInt]
  | positive n =>
    induction n with
    | one => rw [add_pos_one, toInt_successor]; simp [toInt, ZeroMath.Numbers.OrdinalNatural.Peano.toNat]
    | successor n ih =>
      rw [add_pos_succ, toInt_successor, ih]
      simp [toInt, ZeroMath.Numbers.OrdinalNatural.Peano.toNat]
      omega
  | negative n =>
    induction n with
    | one =>
      rw [add_neg_one, toInt_predecessor]
      simp [toInt, ZeroMath.Numbers.OrdinalNatural.Peano.toNat]
      omega
    | successor n ih =>
      rw [add_neg_succ, toInt_predecessor, ih]
      simp [toInt, ZeroMath.Numbers.OrdinalNatural.Peano.toNat]
      omega

theorem toInt_subtract (a b : Peano) : (a - b).toInt = a.toInt - b.toInt := by
  rw [sub_eq_add_neg, toInt_add, toInt_negate]
  omega

theorem toInt_multiply (a b : Peano) : (a * b).toInt = a.toInt * b.toInt := by
  induction b with
  | zero => rw [mul_zero]; simp [toInt]
  | positive n =>
    induction n with
    | one => rw [mul_pos_one]; simp [toInt, ZeroMath.Numbers.OrdinalNatural.Peano.toNat]
    | successor n ih =>
      rw [mul_pos_succ, toInt_add, ih]
      simp [toInt, ZeroMath.Numbers.OrdinalNatural.Peano.toNat]
      rw [Int.mul_add]
      simp [Int.mul_one]
  | negative n =>
    induction n with
    | one =>
      rw [mul_neg_one, toInt_negate]
      simp [toInt, ZeroMath.Numbers.OrdinalNatural.Peano.toNat]
    | successor n ih =>
      rw [mul_neg_succ, toInt_subtract, ih]
      simp [toInt, ZeroMath.Numbers.OrdinalNatural.Peano.toNat]
      rw [Int.neg_add, Int.mul_add]
      simp
      rw [Int.mul_neg]
      omega




theorem ordinal_toNat_injective {a b : OrdinalNatural.Peano} (h : a.toNat = b.toNat) : a = b := by
  obtain ⟨_, ha⟩ := OrdinalNatural.Peano.fromNat_toNat a
  obtain ⟨_, hb⟩ := OrdinalNatural.Peano.fromNat_toNat b
  rw [← ha, ← hb]
  apply OrdinalNatural.Peano.fromNat_eq_of_eq
  exact h

theorem toInt_injective {a b : Peano} (h : a.toInt = b.toInt) : a = b := by
  cases a with
  | zero =>
    cases b with
    | zero => rfl
    | positive n =>
      simp [toInt] at h
      have hn := OrdinalNatural.Peano.toNat_ne_zero n
      omega
    | negative n =>
      simp [toInt] at h
      have hn := OrdinalNatural.Peano.toNat_ne_zero n
      omega
  | positive n =>
    cases b with
    | zero =>
      simp [toInt] at h
      have hn := OrdinalNatural.Peano.toNat_ne_zero n
      omega
    | positive m =>
      apply congrArg positive
      apply ordinal_toNat_injective
      exact Int.ofNat.inj h
    | negative m =>
      simp [toInt] at h
      have hn := OrdinalNatural.Peano.toNat_ne_zero n
      have hm := OrdinalNatural.Peano.toNat_ne_zero m
      omega
  | negative n =>
    cases b with
    | zero =>
      simp [toInt] at h
      have hn := OrdinalNatural.Peano.toNat_ne_zero n
      omega
    | positive m =>
      simp [toInt] at h
      have hn := OrdinalNatural.Peano.toNat_ne_zero n
      have hm := OrdinalNatural.Peano.toNat_ne_zero m
      omega
    | negative m =>
      apply congrArg negative
      apply ordinal_toNat_injective
      simp [toInt] at h
      omega

theorem toInt_ne_zero_of_ne_zero {a : Peano} (h : a ≠ zero) : a.toInt ≠ 0 := by
  intro hz
  apply h
  exact toInt_injective hz

theorem mul_left_cancel (b q c : Peano) (hb : b ≠ zero) (h : b * q = b * c) : q = c := by
  apply toInt_injective
  have hi : (b * q).toInt = (b * c).toInt := by rw [h]
  rw [toInt_multiply, toInt_multiply] at hi
  exact Int.eq_of_mul_eq_mul_left (toInt_ne_zero_of_ne_zero hb) hi


def absNat : Peano → Nat
  | positive n => n.toNat
  | zero => 0
  | negative n => n.toNat

theorem absNat_eq_zero_iff (a : Peano) : absNat a = 0 ↔ a = zero := by
  constructor
  · intro h
    cases a with
    | zero => rfl
    | positive n =>
      simp [absNat] at h
      exact False.elim (OrdinalNatural.Peano.toNat_ne_zero n h)
    | negative n =>
      simp [absNat] at h
      exact False.elim (OrdinalNatural.Peano.toNat_ne_zero n h)
  · intro h
    subst h
    rfl

theorem absNat_le_one_eq (c : Peano)
    (hpos : c ≠ positive OrdinalNatural.Peano.one)
    (hneg : c ≠ negative OrdinalNatural.Peano.one)
    (hle : absNat c ≤ absNat (positive OrdinalNatural.Peano.one)) : c = zero := by
  apply (absNat_eq_zero_iff c).mp
  cases c with
  | zero => rfl
  | positive n =>
    exfalso
    apply hpos
    apply congrArg positive
    apply ordinal_toNat_injective
    simp [absNat, OrdinalNatural.Peano.toNat] at hle ⊢
    have hn := OrdinalNatural.Peano.toNat_ne_zero n
    omega
  | negative n =>
    exfalso
    apply hneg
    apply congrArg negative
    apply ordinal_toNat_injective
    simp [absNat, OrdinalNatural.Peano.toNat] at hle ⊢
    have hn := OrdinalNatural.Peano.toNat_ne_zero n
    omega

theorem absNat_le_of_le_successor_of_ne_candidates (c : Peano) (n : OrdinalNatural.Peano)
    (hpos : c ≠ positive n.successor)
    (hneg : c ≠ negative n.successor)
    (hle : absNat c ≤ absNat (positive n.successor)) : absNat c ≤ absNat (positive n) := by
  cases c with
  | zero => simp [absNat]
  | positive m =>
    simp [absNat, OrdinalNatural.Peano.toNat] at hle ⊢
    apply Nat.le_of_lt_succ
    apply Nat.lt_of_le_of_ne hle
    intro heq
    apply hpos
    apply congrArg positive
    apply ordinal_toNat_injective
    simp [OrdinalNatural.Peano.toNat]
    exact heq
  | negative m =>
    simp [absNat, OrdinalNatural.Peano.toNat] at hle ⊢
    apply Nat.le_of_lt_succ
    apply Nat.lt_of_le_of_ne hle
    intro heq
    apply hneg
    apply congrArg negative
    apply ordinal_toNat_injective
    simp [OrdinalNatural.Peano.toNat]
    exact heq

theorem divide_rec_eq_of_multiply_eq (a b orig c : Peano) (hb : b ≠ zero)
    (hc : b * c = orig) (hle : absNat c ≤ absNat a) : divide_rec a b orig = c := by
  induction a with
  | zero =>
    have hcz : c = zero := (absNat_eq_zero_iff c).mp (Nat.eq_zero_of_le_zero hle)
    subst hcz
    unfold divide_rec
    rfl
  | positive n =>
    induction n with
    | one =>
      unfold divide_rec
      by_cases hpos : b * positive OrdinalNatural.Peano.one = orig
      · rw [if_pos hpos]
        exact mul_left_cancel b (positive OrdinalNatural.Peano.one) c hb (by rw [hc, hpos])
      · rw [if_neg hpos]
        by_cases hneg : b * negative OrdinalNatural.Peano.one = orig
        · rw [if_pos hneg]
          exact mul_left_cancel b (negative OrdinalNatural.Peano.one) c hb (by rw [hc, hneg])
        · rw [if_neg hneg]
          exact (absNat_le_one_eq c
            (fun hcpos => hpos (by rw [← hcpos]; exact hc))
            (fun hcneg => hneg (by rw [← hcneg]; exact hc)) hle).symm
    | successor n ih =>
      unfold divide_rec
      by_cases hpos : b * positive n.successor = orig
      · rw [if_pos hpos]
        exact mul_left_cancel b (positive n.successor) c hb (by rw [hc, hpos])
      · rw [if_neg hpos]
        by_cases hneg : b * negative n.successor = orig
        · rw [if_pos hneg]
          exact mul_left_cancel b (negative n.successor) c hb (by rw [hc, hneg])
        · rw [if_neg hneg]
          apply ih
          exact absNat_le_of_le_successor_of_ne_candidates c n
            (fun hcpos => hpos (by rw [← hcpos]; exact hc))
            (fun hcneg => hneg (by rw [← hcneg]; exact hc)) hle
  | negative n =>
    induction n with
    | one =>
      unfold divide_rec
      by_cases hpos : b * positive OrdinalNatural.Peano.one = orig
      · rw [if_pos hpos]
        exact mul_left_cancel b (positive OrdinalNatural.Peano.one) c hb (by rw [hc, hpos])
      · rw [if_neg hpos]
        by_cases hneg : b * negative OrdinalNatural.Peano.one = orig
        · rw [if_pos hneg]
          exact mul_left_cancel b (negative OrdinalNatural.Peano.one) c hb (by rw [hc, hneg])
        · rw [if_neg hneg]
          exact (absNat_le_one_eq c
            (fun hcpos => hpos (by rw [← hcpos]; exact hc))
            (fun hcneg => hneg (by rw [← hcneg]; exact hc)) hle).symm
    | successor n ih =>
      unfold divide_rec
      by_cases hpos : b * positive n.successor = orig
      · rw [if_pos hpos]
        exact mul_left_cancel b (positive n.successor) c hb (by rw [hc, hpos])
      · rw [if_neg hpos]
        by_cases hneg : b * negative n.successor = orig
        · rw [if_pos hneg]
          exact mul_left_cancel b (negative n.successor) c hb (by rw [hc, hneg])
        · rw [if_neg hneg]
          apply ih
          exact absNat_le_of_le_successor_of_ne_candidates c n
            (fun hcpos => hpos (by rw [← hcpos]; exact hc))
            (fun hcneg => hneg (by rw [← hcneg]; exact hc)) hle


theorem absNat_toInt (a : Peano) : a.toInt.natAbs = absNat a := by
  cases a with
  | zero => rfl
  | positive n => simp [toInt, absNat]
  | negative n => simp [toInt, absNat, Int.natAbs_neg]

theorem absNat_pos_of_ne_zero {a : Peano} (h : a ≠ zero) : 0 < absNat a := by
  cases a with
  | zero => contradiction
  | positive n =>
    simp [absNat]
    exact Nat.pos_of_ne_zero (OrdinalNatural.Peano.toNat_ne_zero n)
  | negative n =>
    simp [absNat]
    exact Nat.pos_of_ne_zero (OrdinalNatural.Peano.toNat_ne_zero n)

theorem absNat_le_absNat_mul_left (x y : Peano) (hy : y ≠ zero) : absNat x ≤ absNat (y * x) := by
  rw [← absNat_toInt x, ← absNat_toInt (y * x), toInt_multiply, Int.natAbs_mul]
  rw [absNat_toInt y, absNat_toInt x]
  exact Nat.le_mul_of_pos_left (absNat x) (absNat_pos_of_ne_zero hy)

theorem division_reverses_multiplication (x y : Peano) (hy : y ≠ zero) :
  ∃ h, divide (y * x) y h = x := by
  have h : isDivisible (y * x) y := by
    constructor
    · exact hy
    · exists x
  refine ⟨h, ?_⟩
  unfold divide
  apply divide_rec_eq_of_multiply_eq
  · exact hy
  · rfl
  · exact absNat_le_absNat_mul_left x y hy

end Peano

def Peano.fromInt : Int → Peano
  | Int.ofNat 0 => Peano.zero
  | Int.ofNat (n + 1) => Peano.positive (OrdinalNatural.Peano.fromNat (n + 1) (Nat.succ_ne_zero n))
  | Int.negSucc n => Peano.negative (OrdinalNatural.Peano.fromNat (n + 1) (Nat.succ_ne_zero n))

theorem Peano.toInt_fromInt (x : Int) : (Peano.fromInt x).toInt = x := by
  cases x with
  | ofNat n =>
    cases n with
    | zero =>
      rfl
    | succ n =>
      unfold Peano.fromInt Peano.toInt
      simp [ZeroMath.Numbers.OrdinalNatural.Peano.toNat_fromNat]
  | negSucc n =>
    unfold Peano.fromInt Peano.toInt
    simp [ZeroMath.Numbers.OrdinalNatural.Peano.toNat_fromNat]
    rfl

theorem Peano.fromInt_toInt (x : Peano) : Peano.fromInt (x.toInt) = x := by
  cases x with
  | zero => rfl
  | positive n =>
    change Peano.fromInt (n.toNat : Int) = Peano.positive n
    cases h_nat : n.toNat with
    | zero =>
      have hne := ZeroMath.Numbers.OrdinalNatural.Peano.toNat_ne_zero n
      rw [h_nat] at hne
      contradiction
    | succ k =>
      change Peano.fromInt (Int.ofNat (k + 1)) = Peano.positive n
      have h1 : Peano.fromInt (Int.ofNat (k + 1)) = Peano.positive (ZeroMath.Numbers.OrdinalNatural.Peano.fromNat (k + 1) (Nat.succ_ne_zero k)) := rfl
      rw [h1]
      congr
      apply ZeroMath.Numbers.OrdinalNatural.Peano.fromNat_toNat_helper
      rw [h_nat]
  | negative n =>
    change Peano.fromInt (- (n.toNat : Int)) = Peano.negative n
    cases h_nat : n.toNat with
    | zero =>
      have hne := ZeroMath.Numbers.OrdinalNatural.Peano.toNat_ne_zero n
      rw [h_nat] at hne
      contradiction
    | succ k =>
      change Peano.fromInt (Int.negSucc k) = Peano.negative n
      have h1 : Peano.fromInt (Int.negSucc k) = Peano.negative (ZeroMath.Numbers.OrdinalNatural.Peano.fromNat (k + 1) (Nat.succ_ne_zero k)) := rfl
      rw [h1]
      congr
      apply ZeroMath.Numbers.OrdinalNatural.Peano.fromNat_toNat_helper
      rw [h_nat]

theorem Peano.mul_add (a b c : Peano) : a * (b + c) = a * b + a * c := by
  induction c with
  | zero =>
    rw [add_zero, mul_zero, add_zero]
  | positive n =>
    induction n with
    | one =>
      rw [add_pos_one, mul_succ, mul_pos_one]
    | successor n ih =>
      rw [add_pos_succ, mul_succ, ih, mul_pos_succ, add_assoc]
  | negative n =>
    induction n with
    | one =>
      rw [add_neg_one, mul_pred, mul_neg_one]
      rw [sub_eq_add_neg]
    | successor n ih =>
      rw [add_neg_succ, mul_pred, ih, mul_neg_succ]
      rw [sub_eq_add_neg (a * b + a * negative n) a]
      rw [sub_eq_add_neg (a * negative n) a]
      rw [add_assoc]

theorem Peano.neg_succ (a : Peano) : -(successor a) = predecessor (-a) := by
  cases a with
  | zero => rfl
  | positive n =>
    cases n with
    | one => rfl
    | successor n => rfl
  | negative n =>
    cases n with
    | one => rfl
    | successor n => rfl

theorem Peano.neg_pred (a : Peano) : -(predecessor a) = successor (-a) := by
  cases a with
  | zero => rfl
  | positive n =>
    cases n with
    | one => rfl
    | successor n => rfl
  | negative n =>
    cases n with
    | one => rfl
    | successor n => rfl

theorem Peano.neg_add (a b : Peano) : -(a + b) = -a + -b := by
  induction b with
  | zero =>
    have h1 : -zero = zero := rfl
    rw [add_zero, h1, add_zero]
  | positive n =>
    induction n with
    | one =>
      have hp : -(positive OrdinalNatural.Peano.one) = negative OrdinalNatural.Peano.one := rfl
      rw [hp, add_pos_one, add_neg_one, neg_succ]
    | successor n ih =>
      have hp : -(positive n.successor) = negative n.successor := rfl
      rw [hp, add_pos_succ, add_neg_succ, neg_succ, ih]
      have hp2 : -(positive n) = negative n := rfl
      rw [hp2]
  | negative n =>
    induction n with
    | one =>
      have hn : -(negative OrdinalNatural.Peano.one) = positive OrdinalNatural.Peano.one := rfl
      rw [hn, add_neg_one, add_pos_one, neg_pred]
    | successor n ih =>
      have hn : -(negative n.successor) = positive n.successor := rfl
      rw [hn, add_neg_succ, add_pos_succ, neg_pred, ih]
      have hn2 : -(negative n) = positive n := rfl
      rw [hn2]

theorem Peano.neg_neg (x : Peano) : -(-x) = x := by
  cases x with
  | zero => rfl
  | positive n => rfl
  | negative n => rfl

theorem Peano.sub_neg (a b : Peano) : a - (-b) = a + b := by
  rw [sub_eq_add_neg, neg_neg]

theorem Peano.neg_sub (a b : Peano) : -(a - b) = -a + b := by
  rw [sub_eq_add_neg, neg_add, neg_neg]

theorem Peano.neg_mul (a b : Peano) : (-a) * b = -(a * b) := by
  induction b with
  | zero =>
    rw [mul_zero, mul_zero]
    rfl
  | positive n =>
    induction n with
    | one =>
      rw [mul_pos_one, mul_pos_one]
    | successor n ih =>
      rw [mul_pos_succ, mul_pos_succ, ih, neg_add]
  | negative n =>
    induction n with
    | one =>
      rw [mul_neg_one, mul_neg_one, neg_neg]
    | successor n ih =>
      rw [mul_neg_succ, mul_neg_succ, ih]
      rw [sub_neg, neg_sub]

theorem Peano.mul_neg (a b : Peano) : a * (-b) = -(a * b) := by
  cases b with
  | zero =>
    have hz : -zero = zero := rfl
    have h1 : a * -zero = a * zero := by rw [hz]
    rw [h1, mul_zero]
    rfl
  | positive n =>
    induction n with
    | one =>
      have hp : -(positive OrdinalNatural.Peano.one) = negative OrdinalNatural.Peano.one := rfl
      rw [hp, mul_neg_one, mul_pos_one]
    | successor n ih =>
      have hp : -(positive n.successor) = negative n.successor := rfl
      rw [hp, mul_neg_succ, mul_pos_succ]
      have hp2 : -(positive n) = negative n := rfl
      have hh : a * -(positive n) = -(a * positive n) := ih
      rw [hp2] at hh
      rw [hh]
      rw [neg_add, sub_eq_add_neg]
  | negative n =>
    induction n with
    | one =>
      have hn : -(negative OrdinalNatural.Peano.one) = positive OrdinalNatural.Peano.one := rfl
      rw [hn, mul_pos_one, mul_neg_one, neg_neg]
    | successor n ih =>
      have hn : -(negative n.successor) = positive n.successor := rfl
      rw [hn, mul_pos_succ, mul_neg_succ]
      have hn2 : -(negative n) = positive n := rfl
      have hh : a * -(negative n) = -(a * negative n) := ih
      rw [hn2] at hh
      rw [hh]
      rw [sub_eq_add_neg, neg_add, neg_neg, add_comm]

theorem Peano.neg_mul_neg (x y : Peano) : (-x) * (-y) = x * y := by
  rw [neg_mul, mul_neg, neg_neg]

theorem Peano.add_right_comm (a b c : Peano) : a + b + c = a + c + b := by
  rw [add_assoc, add_comm b c, ←add_assoc]

theorem Peano.succ_mul (a b : Peano) : successor a * b = a * b + b := by
  induction b with
  | zero => rw [mul_zero, mul_zero, add_zero]
  | positive n =>
    induction n with
    | one =>
      rw [mul_pos_one, mul_pos_one, ←add_pos_one]
    | successor n ih =>
      rw [mul_pos_succ, mul_pos_succ, ih]
      rw [add_succ]
      have h1 : a * positive n + positive n + a = a * positive n + a + positive n := add_right_comm _ _ _
      rw [h1]
      rw [←add_succ]
      rfl
  | negative n =>
    induction n with
    | one =>
      rw [mul_neg_one, mul_neg_one]
      rw [neg_succ]
      rw [←add_neg_one]
    | successor n ih =>
      rw [mul_neg_succ, mul_neg_succ, ih]
      rw [sub_eq_add_neg, sub_eq_add_neg]
      rw [neg_succ]
      rw [add_pred]
      have h1 : a * negative n + negative n + -a = a * negative n + -a + negative n := add_right_comm _ _ _
      rw [h1]
      have h2 : predecessor (a * negative n + -a + negative n) = a * negative n + -a + predecessor (negative n) := by
        rw [←add_pred]
      rw [h2]
      rfl

theorem Peano.pred_mul (a b : Peano) : predecessor a * b = a * b - b := by
  induction b with
  | zero => rw [mul_zero, mul_zero, sub_zero]
  | positive n =>
    induction n with
    | one =>
      rw [mul_pos_one, mul_pos_one, sub_pos_one]
    | successor n ih =>
      rw [mul_pos_succ, ih]
      rw [sub_eq_add_neg, sub_eq_add_neg]
      have h2 : -(positive n) = negative n := rfl
      rw [h2]
      have h0 : a.predecessor = a + negative OrdinalNatural.Peano.one := (add_neg_one a).symm
      rw [h0]
      rw [add_assoc]
      have hc : negative n + (a + negative OrdinalNatural.Peano.one) = a + negative n + negative OrdinalNatural.Peano.one := by
        rw [add_comm (negative n) (a + negative OrdinalNatural.Peano.one)]
        rw [add_assoc, add_comm (negative OrdinalNatural.Peano.one)]
        rw [←add_assoc]
      rw [hc, ←add_assoc]
      have hx : a * positive n + (a + negative n) = a * positive n + a + negative n := (add_assoc _ _ _).symm
      rw [hx]
      have hr : a * positive n + a = a * positive n.successor := (mul_pos_succ a n).symm
      rw [hr]
      rw [add_assoc]
      have h5 : negative n + negative OrdinalNatural.Peano.one = predecessor (negative n) := add_neg_one (negative n)
      rw [h5]
      have h7 : predecessor (negative n) = negative n.successor := rfl
      rw [h7]
      have h6 : -(positive n.successor) = negative n.successor := rfl
      rw [←h6]
  | negative n =>
    induction n with
    | one =>
      rw [mul_neg_one, mul_neg_one]
      rw [sub_neg_one, neg_pred]
    | successor n ih =>
      rw [mul_neg_succ, ih]
      rw [sub_eq_add_neg, sub_eq_add_neg]
      have h2 : -(negative n) = positive n := rfl
      rw [h2]
      have h3 : -(a.predecessor) = -a + positive OrdinalNatural.Peano.one := by
        rw [neg_pred]
        exact (add_pos_one (-a)).symm
      rw [h3]
      rw [add_assoc]
      have hc : positive n + (-a + positive OrdinalNatural.Peano.one) = -a + positive n + positive OrdinalNatural.Peano.one := by
        rw [add_comm (positive n) (-a + positive OrdinalNatural.Peano.one)]
        rw [add_assoc, add_comm (positive OrdinalNatural.Peano.one)]
        rw [←add_assoc]
      rw [hc, ←add_assoc]
      have hx : a * negative n + (-a + positive n) = a * negative n + -a + positive n := (add_assoc _ _ _).symm
      rw [hx]
      have h1 : a * negative n + -a = a * negative n - a := (sub_eq_add_neg _ _).symm
      rw [h1]
      have hm : a * negative n - a = a * negative n.successor := (mul_neg_succ a n).symm
      rw [hm]
      rw [add_assoc]
      have h5 : positive n + positive OrdinalNatural.Peano.one = successor (positive n) := add_pos_one (positive n)
      rw [h5]
      have h7 : successor (positive n) = positive n.successor := rfl
      rw [h7]
      have h6 : -(negative n.successor) = positive n.successor := rfl
      rw [←h6]
      have hsub : a * negative n.successor + -(negative n.successor) = a * negative n.successor - negative n.successor := (sub_eq_add_neg _ _).symm
      rw [hsub]

theorem Peano.mul_comm (a b : Peano) : a * b = b * a := by
  induction a with
  | zero => rw [mul_zero, zero_mul]
  | positive n =>
    induction n with
    | one =>
      induction b with
      | zero => rw [mul_pos_one, mul_zero]
      | positive m =>
        induction m with
        | one => rfl
        | successor m ihm =>
          rw [mul_pos_succ]
          have h1 : positive m * positive OrdinalNatural.Peano.one = positive m := mul_pos_one _
          rw [h1] at ihm
          rw [ihm, add_pos_one]
          have h2 : positive m.successor = successor (positive m) := rfl
          rw [h2, mul_pos_one]
      | negative m =>
        induction m with
        | one =>
          rw [mul_neg_one, mul_pos_one]
          rfl
        | successor m ihm =>
          rw [mul_neg_succ]
          have h1 : negative m * positive OrdinalNatural.Peano.one = negative m := mul_pos_one _
          rw [h1] at ihm
          rw [ihm, sub_pos_one]
          have h2 : negative m.successor = predecessor (negative m) := rfl
          rw [h2, mul_pos_one]
    | successor n ih =>
      have hs : positive n.successor = successor (positive n) := rfl
      rw [hs]
      rw [succ_mul, ih, mul_succ]
  | negative n =>
    induction n with
    | one =>
      induction b with
      | zero => rw [mul_neg_one, mul_zero]; rfl
      | positive m =>
        induction m with
        | one =>
          rw [mul_pos_one, mul_neg_one]
          rfl
        | successor m ihm =>
          rw [mul_pos_succ, ihm]
          have hm : positive m * negative OrdinalNatural.Peano.one = -positive m := mul_neg_one _
          rw [hm]
          have hn : -positive m + negative OrdinalNatural.Peano.one = predecessor (-positive m) := add_neg_one _
          rw [hn]
          have hn2 : -(positive m) = negative m := rfl
          rw [hn2]
          have hx : predecessor (negative m) = negative m.successor := rfl
          rw [hx]
          have h1 : -(positive m.successor) = negative m.successor := rfl
          rw [←h1]
          have hsub : positive m.successor * negative OrdinalNatural.Peano.one = -(positive m.successor) := mul_neg_one _
          rw [hsub]
      | negative m =>
        induction m with
        | one => rfl
        | successor m ihm =>
          rw [mul_neg_succ, ihm]
          have hm2 : negative m * negative OrdinalNatural.Peano.one = -negative m := mul_neg_one _
          rw [hm2]
          have hm : -(negative m) = positive m := rfl
          rw [hm]
          have hn : positive m - negative OrdinalNatural.Peano.one = positive m + positive OrdinalNatural.Peano.one := sub_eq_add_neg _ _
          rw [hn]
          have hn_succ : positive m + positive OrdinalNatural.Peano.one = successor (positive m) := add_pos_one _
          rw [hn_succ]
          have hx : successor (positive m) = positive m.successor := rfl
          rw [hx]
          have h1 : -(negative m.successor) = positive m.successor := rfl
          rw [←h1]
          have hsub : negative m.successor * negative OrdinalNatural.Peano.one = -(negative m.successor) := mul_neg_one _
          rw [hsub]
    | successor n ih =>
      have hs : negative n.successor = predecessor (negative n) := rfl
      rw [hs]
      rw [pred_mul, ih, mul_pred]

theorem Peano.divide_rec_positive_one_positive (x : OrdinalNatural.Peano) :
  divide_rec (positive x) (positive OrdinalNatural.Peano.one) (positive x) = positive x := by
  induction x with
  | one =>
    unfold Peano.divide_rec
    rw [Peano.mul_pos_one]
    rw [if_pos rfl]
  | successor x ih =>
    unfold Peano.divide_rec
    rw [Peano.mul_comm (positive OrdinalNatural.Peano.one) (positive x.successor)]
    rw [Peano.mul_pos_one]
    rw [if_pos rfl]

theorem Peano.divide_multiply_positive_one_eq (x : OrdinalNatural.Peano) :
  ∃ h, divide (positive OrdinalNatural.Peano.one * positive x) (positive OrdinalNatural.Peano.one) h = positive x := by
  have h : isDivisible (positive OrdinalNatural.Peano.one * positive x) (positive OrdinalNatural.Peano.one) := by
    constructor
    · intro hzero
      cases hzero
    · exists positive x
  refine ⟨h, ?_⟩
  unfold Peano.divide
  rw [Peano.mul_comm (positive OrdinalNatural.Peano.one) (positive x)]
  rw [Peano.mul_pos_one]
  exact divide_rec_positive_one_positive x

theorem Peano.divide_rec_negative_one_negative (x : OrdinalNatural.Peano) :
  divide_rec (positive x) (negative OrdinalNatural.Peano.one) (positive x) = negative x := by
  induction x with
  | one =>
    unfold Peano.divide_rec
    have hn : negative OrdinalNatural.Peano.one * positive OrdinalNatural.Peano.one ≠ positive OrdinalNatural.Peano.one := by
      rw [Peano.mul_pos_one]
      intro h
      cases h
    rw [if_neg hn]
    rw [Peano.mul_neg_one]
    have hneg : -negative OrdinalNatural.Peano.one = positive OrdinalNatural.Peano.one := rfl
    rw [hneg]
    rw [if_pos rfl]
  | successor x ih =>
    unfold Peano.divide_rec
    have hn : negative OrdinalNatural.Peano.one * positive x.successor ≠ positive x.successor := by
      rw [Peano.mul_comm (negative OrdinalNatural.Peano.one) (positive x.successor)]
      rw [Peano.mul_neg_one]
      intro h
      cases h
    rw [if_neg hn]
    rw [Peano.mul_comm (negative OrdinalNatural.Peano.one) (negative x.successor)]
    rw [Peano.mul_neg_one]
    have hneg : -negative x.successor = positive x.successor := rfl
    rw [hneg]
    rw [if_pos rfl]

theorem Peano.divide_multiply_negative_one_eq (x : OrdinalNatural.Peano) :
  ∃ h, divide (negative OrdinalNatural.Peano.one * negative x) (negative OrdinalNatural.Peano.one) h = negative x := by
  have h : isDivisible (negative OrdinalNatural.Peano.one * negative x) (negative OrdinalNatural.Peano.one) := by
    constructor
    · intro hzero
      cases hzero
    · exists negative x
  refine ⟨h, ?_⟩
  unfold Peano.divide
  rw [Peano.mul_comm (negative OrdinalNatural.Peano.one) (negative x)]
  rw [Peano.mul_neg_one]
  have hneg : -negative x = positive x := rfl
  rw [hneg]
  exact divide_rec_negative_one_negative x

theorem Peano.divide_multiply_zero_eq (y : Peano) (hy : y ≠ zero) :
  ∃ h, divide (y * zero) y h = zero := by
  have h : isDivisible (y * zero) y := by
    constructor
    · exact hy
    · exists zero
  refine ⟨h, ?_⟩
  unfold Peano.divide
  rw [Peano.mul_zero]
  unfold Peano.divide_rec
  rfl

theorem Peano.divide_zero_multiply_eq (y : Peano) (hy : y ≠ zero) :
  ∃ h, divide (zero * y) y h = zero := by
  have h : isDivisible (zero * y) y := by
    constructor
    · exact hy
    · exists zero
      rw [Peano.mul_zero, Peano.zero_mul]
  refine ⟨h, ?_⟩
  unfold Peano.divide
  rw [Peano.zero_mul]
  unfold Peano.divide_rec
  rfl

theorem Peano.divide_multiply_positive_one_nonnegative_eq (x : Peano)
  (hx : x = zero ∨ ∃ n, x = positive n) :
  ∃ h, divide (positive OrdinalNatural.Peano.one * x) (positive OrdinalNatural.Peano.one) h = x := by
  cases hx with
  | inl hzero =>
    subst hzero
    exact divide_multiply_zero_eq (positive OrdinalNatural.Peano.one) (by intro h; cases h)
  | inr hpos =>
    cases hpos with
    | intro n hn =>
      subst hn
      exact divide_multiply_positive_one_eq n

theorem Peano.divide_multiply_negative_one_nonpositive_eq (x : Peano)
  (hx : x = zero ∨ ∃ n, x = negative n) :
  ∃ h, divide (negative OrdinalNatural.Peano.one * x) (negative OrdinalNatural.Peano.one) h = x := by
  cases hx with
  | inl hzero =>
    subst hzero
    exact divide_multiply_zero_eq (negative OrdinalNatural.Peano.one) (by intro h; cases h)
  | inr hneg =>
    cases hneg with
    | intro n hn =>
      subst hn
      exact divide_multiply_negative_one_eq n

theorem Peano.divide_multiply_unit_same_sign_eq (x y : Peano)
  (hcase : (y = positive OrdinalNatural.Peano.one ∧ (x = zero ∨ ∃ n, x = positive n)) ∨
    (y = negative OrdinalNatural.Peano.one ∧ (x = zero ∨ ∃ n, x = negative n))) :
  ∃ h, divide (y * x) y h = x := by
  cases hcase with
  | inl hpos =>
    cases hpos with
    | intro hy hx =>
      subst hy
      exact divide_multiply_positive_one_nonnegative_eq x hx
  | inr hneg =>
    cases hneg with
    | intro hy hx =>
      subst hy
      exact divide_multiply_negative_one_nonpositive_eq x hx

theorem Peano.divide_rec_positive_one_negative (x : OrdinalNatural.Peano) :
  divide_rec (negative x) (positive OrdinalNatural.Peano.one) (negative x) = negative x := by
  induction x with
  | one =>
    unfold Peano.divide_rec
    have hp : positive OrdinalNatural.Peano.one * positive OrdinalNatural.Peano.one ≠ negative OrdinalNatural.Peano.one := by
      rw [Peano.mul_pos_one]
      intro h
      cases h
    rw [if_neg hp]
    rw [Peano.mul_neg_one]
    have hneg : -positive OrdinalNatural.Peano.one = negative OrdinalNatural.Peano.one := rfl
    rw [hneg]
    rw [if_pos rfl]
  | successor x ih =>
    unfold Peano.divide_rec
    have hp : positive OrdinalNatural.Peano.one * positive x.successor ≠ negative x.successor := by
      rw [Peano.mul_comm (positive OrdinalNatural.Peano.one) (positive x.successor)]
      rw [Peano.mul_pos_one]
      intro h
      cases h
    rw [if_neg hp]
    rw [Peano.mul_comm (positive OrdinalNatural.Peano.one) (negative x.successor)]
    rw [Peano.mul_pos_one]
    rw [if_pos rfl]

theorem Peano.divide_multiply_positive_one_negative_eq (x : OrdinalNatural.Peano) :
  ∃ h, divide (positive OrdinalNatural.Peano.one * negative x) (positive OrdinalNatural.Peano.one) h = negative x := by
  have h : isDivisible (positive OrdinalNatural.Peano.one * negative x) (positive OrdinalNatural.Peano.one) := by
    constructor
    · intro hzero
      cases hzero
    · exists negative x
  refine ⟨h, ?_⟩
  unfold Peano.divide
  rw [Peano.mul_comm (positive OrdinalNatural.Peano.one) (negative x)]
  rw [Peano.mul_pos_one]
  exact divide_rec_positive_one_negative x

theorem Peano.divide_rec_negative_one_positive (x : OrdinalNatural.Peano) :
  divide_rec (negative x) (negative OrdinalNatural.Peano.one) (negative x) = positive x := by
  induction x with
  | one =>
    unfold Peano.divide_rec
    rw [Peano.mul_pos_one]
    rw [if_pos rfl]
  | successor x ih =>
    unfold Peano.divide_rec
    rw [Peano.mul_comm (negative OrdinalNatural.Peano.one) (positive x.successor)]
    rw [Peano.mul_neg_one]
    have hneg : -positive x.successor = negative x.successor := rfl
    rw [hneg]
    rw [if_pos rfl]

theorem Peano.divide_multiply_negative_one_positive_eq (x : OrdinalNatural.Peano) :
  ∃ h, divide (negative OrdinalNatural.Peano.one * positive x) (negative OrdinalNatural.Peano.one) h = positive x := by
  have h : isDivisible (negative OrdinalNatural.Peano.one * positive x) (negative OrdinalNatural.Peano.one) := by
    constructor
    · intro hzero
      cases hzero
    · exists positive x
  refine ⟨h, ?_⟩
  unfold Peano.divide
  rw [Peano.mul_comm (negative OrdinalNatural.Peano.one) (positive x)]
  rw [Peano.mul_neg_one]
  have hneg : -positive x = negative x := rfl
  rw [hneg]
  exact divide_rec_negative_one_positive x

theorem Peano.divide_multiply_positive_one_any_eq (x : Peano) :
  ∃ h, divide (positive OrdinalNatural.Peano.one * x) (positive OrdinalNatural.Peano.one) h = x := by
  cases x with
  | zero =>
    exact divide_multiply_zero_eq (positive OrdinalNatural.Peano.one) (by intro h; cases h)
  | positive n =>
    exact divide_multiply_positive_one_eq n
  | negative n =>
    exact divide_multiply_positive_one_negative_eq n

theorem Peano.divide_multiply_negative_one_any_eq (x : Peano) :
  ∃ h, divide (negative OrdinalNatural.Peano.one * x) (negative OrdinalNatural.Peano.one) h = x := by
  cases x with
  | zero =>
    exact divide_multiply_zero_eq (negative OrdinalNatural.Peano.one) (by intro h; cases h)
  | positive n =>
    exact divide_multiply_negative_one_positive_eq n
  | negative n =>
    exact divide_multiply_negative_one_eq n

theorem Peano.divide_multiply_right_positive_one_any_eq (x : Peano) :
  ∃ h, divide (x * positive OrdinalNatural.Peano.one) (positive OrdinalNatural.Peano.one) h = x := by
  cases x with
  | zero =>
    have h : isDivisible (zero * positive OrdinalNatural.Peano.one) (positive OrdinalNatural.Peano.one) := by
      constructor
      · intro hzero
        cases hzero
      · exists zero
        rw [Peano.mul_zero, Peano.zero_mul]
    refine ⟨h, ?_⟩
    unfold Peano.divide
    rw [Peano.zero_mul]
    unfold Peano.divide_rec
    rfl
  | positive n =>
    have h : isDivisible (positive n * positive OrdinalNatural.Peano.one) (positive OrdinalNatural.Peano.one) := by
      constructor
      · intro hzero
        cases hzero
      · exists positive n
        rw [Peano.mul_comm (positive OrdinalNatural.Peano.one) (positive n)]
    refine ⟨h, ?_⟩
    unfold Peano.divide
    rw [Peano.mul_pos_one]
    exact divide_rec_positive_one_positive n
  | negative n =>
    have h : isDivisible (negative n * positive OrdinalNatural.Peano.one) (positive OrdinalNatural.Peano.one) := by
      constructor
      · intro hzero
        cases hzero
      · exists negative n
        rw [Peano.mul_comm (positive OrdinalNatural.Peano.one) (negative n)]
    refine ⟨h, ?_⟩
    unfold Peano.divide
    rw [Peano.mul_pos_one]
    exact divide_rec_positive_one_negative n

theorem Peano.divide_multiply_right_negative_one_any_eq (x : Peano) :
  ∃ h, divide (x * negative OrdinalNatural.Peano.one) (negative OrdinalNatural.Peano.one) h = x := by
  cases x with
  | zero =>
    have h : isDivisible (zero * negative OrdinalNatural.Peano.one) (negative OrdinalNatural.Peano.one) := by
      constructor
      · intro hzero
        cases hzero
      · exists zero
        rw [Peano.mul_zero, Peano.zero_mul]
    refine ⟨h, ?_⟩
    unfold Peano.divide
    rw [Peano.zero_mul]
    unfold Peano.divide_rec
    rfl
  | positive n =>
    have h : isDivisible (positive n * negative OrdinalNatural.Peano.one) (negative OrdinalNatural.Peano.one) := by
      constructor
      · intro hzero
        cases hzero
      · exists positive n
        rw [Peano.mul_comm (negative OrdinalNatural.Peano.one) (positive n)]
    refine ⟨h, ?_⟩
    unfold Peano.divide
    rw [Peano.mul_neg_one]
    have hneg : -positive n = negative n := rfl
    rw [hneg]
    exact divide_rec_negative_one_positive n
  | negative n =>
    have h : isDivisible (negative n * negative OrdinalNatural.Peano.one) (negative OrdinalNatural.Peano.one) := by
      constructor
      · intro hzero
        cases hzero
      · exists negative n
        rw [Peano.mul_comm (negative OrdinalNatural.Peano.one) (negative n)]
    refine ⟨h, ?_⟩
    unfold Peano.divide
    rw [Peano.mul_neg_one]
    have hneg : -negative n = positive n := rfl
    rw [hneg]
    exact divide_rec_negative_one_negative n

theorem Peano.divide_multiply_unit_any_eq (x y : Peano)
  (hy : y = positive OrdinalNatural.Peano.one ∨ y = negative OrdinalNatural.Peano.one) :
  ∃ h, divide (y * x) y h = x := by
  cases hy with
  | inl hpos =>
    subst hpos
    exact divide_multiply_positive_one_any_eq x
  | inr hneg =>
    subst hneg
    exact divide_multiply_negative_one_any_eq x

theorem Peano.divide_multiply_right_unit_any_eq (x y : Peano)
  (hy : y = positive OrdinalNatural.Peano.one ∨ y = negative OrdinalNatural.Peano.one) :
  ∃ h, divide (x * y) y h = x := by
  cases hy with
  | inl hpos =>
    subst hpos
    exact divide_multiply_right_positive_one_any_eq x
  | inr hneg =>
    subst hneg
    exact divide_multiply_right_negative_one_any_eq x

theorem Peano.divide_multiply_unit_or_zero_eq (x y : Peano)
  (hcase : y = positive OrdinalNatural.Peano.one ∨ y = negative OrdinalNatural.Peano.one ∨ (x = zero ∧ y ≠ zero)) :
  ∃ h, divide (y * x) y h = x := by
  cases hcase with
  | inl hypos =>
    exact divide_multiply_unit_any_eq x y (Or.inl hypos)
  | inr hrest =>
    cases hrest with
    | inl hyneg =>
      exact divide_multiply_unit_any_eq x y (Or.inr hyneg)
    | inr hzero =>
      cases hzero with
      | intro hx hy =>
        subst hx
        exact divide_multiply_zero_eq y hy

theorem Peano.divide_multiply_right_unit_or_zero_eq (x y : Peano)
  (hcase : y = positive OrdinalNatural.Peano.one ∨ y = negative OrdinalNatural.Peano.one ∨ (x = zero ∧ y ≠ zero)) :
  ∃ h, divide (x * y) y h = x := by
  cases hcase with
  | inl hypos =>
    exact divide_multiply_right_unit_any_eq x y (Or.inl hypos)
  | inr hrest =>
    cases hrest with
    | inl hyneg =>
      exact divide_multiply_right_unit_any_eq x y (Or.inr hyneg)
    | inr hzero =>
      cases hzero with
      | intro hx hy =>
        subst hx
        exact divide_zero_multiply_eq y hy

theorem Peano.division_reverses_right_multiplication (x y : Peano) (hy : y ≠ zero) :
  ∃ h, divide (x * y) y h = x := by
  rw [mul_comm x y]
  exact division_reverses_multiplication x y hy

theorem Peano.sub_mul (a b c : Peano) : (a - b) * c = a * c - b * c := by
  rw [Peano.sub_eq_add_neg, Peano.sub_eq_add_neg (a*c)]
  have h_add_mul : (a + -b) * c = a * c + (-b) * c := by
    rw [Peano.mul_comm, Peano.mul_add, Peano.mul_comm, Peano.mul_comm c (-b)]
  rw [h_add_mul, Peano.neg_mul]

theorem Peano.mul_sub (a b c : Peano) : a * (b - c) = a * b - a * c := by
  rw [Peano.mul_comm, Peano.sub_mul, Peano.mul_comm b a, Peano.mul_comm c a]

theorem Peano.mul_assoc (a b c : Peano) : (a * b) * c = a * (b * c) := by
  induction c with
  | zero =>
    rw [Peano.mul_zero, Peano.mul_zero, Peano.mul_zero]
  | positive n =>
    induction n with
    | one =>
      rw [Peano.mul_pos_one, Peano.mul_pos_one]
    | successor m ih =>
      rw [Peano.mul_pos_succ, Peano.mul_pos_succ, Peano.mul_add, ih]
  | negative n =>
    induction n with
    | one =>
      rw [Peano.mul_neg_one, Peano.mul_neg_one, Peano.mul_neg]
    | successor m ih =>
      rw [Peano.mul_neg_succ, Peano.mul_neg_succ, Peano.mul_sub, ih]

theorem Peano.sub_assoc (x y z : Peano) : x + y - z = x + (y - z) := by
  rw [Peano.sub_eq_add_neg, Peano.sub_eq_add_neg, Peano.add_assoc]

theorem Peano.sub_sub (x y z : Peano) : x - y - z = x - (y + z) := by
  rw [Peano.sub_eq_add_neg (x - y) z]
  rw [Peano.sub_eq_add_neg x y]
  rw [Peano.sub_eq_add_neg x (y + z)]
  rw [Peano.neg_add, Peano.add_assoc]

theorem Peano.multiply_divide_cancel (x y : Peano) (h : isDivisible x y) : (divide x y h) * y = x := by
  have ⟨hy, ⟨c, hc⟩⟩ := h
  unfold divide
  have h_mul_eq_x : y * c = x := hc
  have h_le : absNat c ≤ absNat x := by
    rw [← h_mul_eq_x]
    exact absNat_le_absNat_mul_left c y hy
  have h_div_rec := divide_rec_eq_of_multiply_eq x y x c hy hc h_le
  rw [h_div_rec]
  rw [mul_comm]
  exact hc

theorem Peano.divide_add (x y z : Peano) (h : isDivisible x z) (h2 : isDivisible y z) :
  ∃ h3, divide (x + y) z h3 = divide x z h + divide y z h2 := by
  have hz : z ≠ zero := h.1
  have hc : z * (divide x z h + divide y z h2) = x + y := by
    rw [mul_add]
    have hx : z * divide x z h = x := by
      have hh := multiply_divide_cancel x z h
      rw [mul_comm] at hh
      exact hh
    have hy : z * divide y z h2 = y := by
      have hh := multiply_divide_cancel y z h2
      rw [mul_comm] at hh
      exact hh
    rw [hx, hy]
  have h3 : isDivisible (x + y) z := by
    constructor
    · exact hz
    · exists (divide x z h + divide y z h2)
  exists h3
  unfold divide
  apply divide_rec_eq_of_multiply_eq
  · exact hz
  · exact hc
  · rw [← hc]
    exact absNat_le_absNat_mul_left (divide x z h + divide y z h2) z hz

theorem Peano.divide_sub (x y z : Peano) (h : isDivisible x z) (h2 : isDivisible y z) :
  ∃ h3, divide (x - y) z h3 = divide x z h - divide y z h2 := by
  have hz : z ≠ zero := h.1
  have hc : z * (divide x z h - divide y z h2) = x - y := by
    rw [mul_sub]
    have hx : z * divide x z h = x := by
      have hh := multiply_divide_cancel x z h
      rw [mul_comm] at hh
      exact hh
    have hy : z * divide y z h2 = y := by
      have hh := multiply_divide_cancel y z h2
      rw [mul_comm] at hh
      exact hh
    rw [hx, hy]
  have h3 : isDivisible (x - y) z := by
    constructor
    · exact hz
    · exists (divide x z h - divide y z h2)
  exists h3
  unfold divide
  apply divide_rec_eq_of_multiply_eq
  · exact hz
  · exact hc
  · rw [← hc]
    exact absNat_le_absNat_mul_left (divide x z h - divide y z h2) z hz

theorem Peano.mul_eq_zero_iff (x y : Peano) : x * y = zero ↔ x = zero ∨ y = zero := by
  constructor
  · intro h
    cases Decidable.em (x = zero) with
    | inl hx => exact Or.inl hx
    | inr hx =>
      cases Decidable.em (y = zero) with
      | inl hy => exact Or.inr hy
      | inr hy =>
        have hx_int : toInt x ≠ 0 := toInt_ne_zero_of_ne_zero hx
        have hy_int : toInt y ≠ 0 := toInt_ne_zero_of_ne_zero hy
        have hxy_int : toInt (x * y) = 0 := by
          rw [h]
          rfl
        rw [toInt_multiply] at hxy_int
        have hxy_int_2 : toInt x * toInt y ≠ 0 := Int.mul_ne_zero hx_int hy_int
        exact False.elim (hxy_int_2 hxy_int)
  · intro h
    cases h with
    | inl hx =>
      rw [hx, zero_mul]
    | inr hy =>
      rw [hy, mul_zero]

theorem Peano.divide_multiply (x y z : Peano) (h : isDivisible y z) :
  ∃ h2, divide (x * y) z h2 = x * divide y z h := by
  have hz : z ≠ zero := h.1
  have hc : z * (x * divide y z h) = x * y := by
    rw [← mul_assoc, mul_comm z x, mul_assoc]
    have hy : z * divide y z h = y := by
      have hh := multiply_divide_cancel y z h
      rw [mul_comm] at hh
      exact hh
    rw [hy]
  have h2 : isDivisible (x * y) z := by
    constructor
    · exact hz
    · exists (x * divide y z h)
  exists h2
  unfold divide
  apply divide_rec_eq_of_multiply_eq
  · exact hz
  · exact hc
  · rw [← hc]
    exact absNat_le_absNat_mul_left (x * divide y z h) z hz

theorem Peano.divide_divide (x y z : Peano) (h : isDivisible x y) (h2 : isDivisible (divide x y h) z) :
  ∃ h3, divide (divide x y h) z h2 = divide x (y * z) h3 := by
  have hy : y ≠ zero := h.1
  have hz : z ≠ zero := h2.1
  have h_div_x_y : (divide x y h) * y = x := multiply_divide_cancel x y h
  have h_div_z : (divide (divide x y h) z h2) * z = divide x y h := multiply_divide_cancel (divide x y h) z h2

  have hc : (y * z) * (divide (divide x y h) z h2) = x := by
    rw [mul_assoc y z (divide (divide x y h) z h2)]
    have h_tmp : z * divide (divide x y h) z h2 = divide x y h := by
      rw [mul_comm]
      exact h_div_z
    rw [h_tmp]
    rw [mul_comm]
    exact h_div_x_y

  have hyz : y * z ≠ zero := by
    intro hyz_eq
    have h_or := (mul_eq_zero_iff y z).mp hyz_eq
    cases h_or with
    | inl h_y => exact hy h_y
    | inr h_z => exact hz h_z

  have h3 : isDivisible x (y * z) := by
    constructor
    · exact hyz
    · exists divide (divide x y h) z h2

  exists h3
  unfold divide
  have h_le : absNat (divide (divide x y h) z h2) ≤ absNat x := by
    have h_le_tmp := absNat_le_absNat_mul_left (divide (divide x y h) z h2) (y * z) hyz
    have h_tmp_eq : absNat ((y * z) * divide (divide x y h) z h2) = absNat x := by
      rw [hc]
    rw [h_tmp_eq] at h_le_tmp
    exact h_le_tmp

  have hd := divide_rec_eq_of_multiply_eq x (y * z) x (divide (divide x y h) z h2) hyz hc h_le
  exact hd.symm

def Peano.power_pos (a : Peano) : OrdinalNatural.Peano → Peano
  | OrdinalNatural.Peano.one => a
  | OrdinalNatural.Peano.successor n => power_pos a n * a

def Peano.ValidPowerCondition (a b : Peano) : Bool :=
  match a, b with
  | _, Peano.positive _ => true
  | Peano.positive _, Peano.zero => true
  | Peano.negative _, Peano.zero => true
  | Peano.positive OrdinalNatural.Peano.one, Peano.negative _ => true
  | Peano.negative OrdinalNatural.Peano.one, Peano.negative _ => true
  | _, _ => false

def Peano.power : (a b : Peano) → (h : Peano.ValidPowerCondition a b = true) → Peano
  | a, Peano.positive n, _ => power_pos a n
  | Peano.positive _, Peano.zero, _ => Peano.positive OrdinalNatural.Peano.one
  | Peano.negative _, Peano.zero, _ => Peano.positive OrdinalNatural.Peano.one
  | Peano.positive OrdinalNatural.Peano.one, Peano.negative _, _ => Peano.positive OrdinalNatural.Peano.one
  | Peano.negative OrdinalNatural.Peano.one, Peano.negative n, _ => power_pos (Peano.negative OrdinalNatural.Peano.one) n


namespace Peano

abbrev oneInt : Peano := positive OrdinalNatural.Peano.one
abbrev negOneInt : Peano := negative OrdinalNatural.Peano.one

theorem power_pos_add (x : Peano) (y z : OrdinalNatural.Peano) :
    power_pos x (y + z) = power_pos x y * power_pos x z := by
  induction z with
  | one =>
      rw [OrdinalNatural.Peano.add_one]
      rfl
  | successor z ih =>
      rw [OrdinalNatural.Peano.add_succ]
      change power_pos x (y + z) * x = power_pos x y * (power_pos x z * x)
      rw [ih]
      exact Peano.mul_assoc (power_pos x y) (power_pos x z) x

theorem power_pos_multiply (x : Peano) (y z : OrdinalNatural.Peano) :
    power_pos x (y * z) = power_pos (power_pos x y) z := by
  induction z with
  | one =>
      rw [OrdinalNatural.Peano.multiply_one]
      rfl
  | successor z ih =>
      rw [OrdinalNatural.Peano.multiply_succ, power_pos_add, ih]
      rfl

theorem power_pos_mul_base (x y : Peano) (z : OrdinalNatural.Peano) :
    power_pos (x * y) z = power_pos x z * power_pos y z := by
  induction z with
  | one =>
      rfl
  | successor z ih =>
      rw [power_pos, power_pos, power_pos, ih]
      calc
        (power_pos x z * power_pos y z) * (x * y)
            = power_pos x z * (power_pos y z * (x * y)) := by
                rw [mul_assoc]
        _ = power_pos x z * ((power_pos y z * x) * y) := by
              rw [mul_assoc]
        _ = power_pos x z * ((x * power_pos y z) * y) := by
              rw [mul_comm (power_pos y z) x]
        _ = power_pos x z * (x * (power_pos y z * y)) := by
              rw [mul_assoc]
        _ = (power_pos x z * x) * (power_pos y z * y) := by
              rw [← mul_assoc]
        _ = power_pos x z.successor * power_pos y z.successor := by
              rfl



theorem toInt_power_pos (x : Peano) (n : OrdinalNatural.Peano) :
    (power_pos x n).toInt = x.toInt ^ n.toNat := by
  induction n with
  | one =>
      simp [power_pos, toInt, ZeroMath.Numbers.OrdinalNatural.Peano.toNat, Int.pow_one]
  | successor n ih =>
      rw [power_pos, toInt_multiply, ih]
      rw [ZeroMath.Numbers.OrdinalNatural.Peano.toNat, Int.pow_succ]

theorem power_pos_toInt_natAbs (x : Peano) (n : OrdinalNatural.Peano) :
    (power_pos x n).toInt.natAbs = x.toInt.natAbs ^ n.toNat := by
  rw [toInt_power_pos]
  exact Int.natAbs_pow x.toInt n.toNat

theorem power_pos_oneInt (e : OrdinalNatural.Peano) : power_pos oneInt e = oneInt := by
  induction e with
  | one => rfl
  | successor e ih =>
      change power_pos oneInt e * oneInt = oneInt
      rw [ih, mul_pos_one]

def signedPower (a : Peano) : Peano → Peano
  | zero => oneInt
  | positive n => power_pos a n
  | negative n => power_pos a n

theorem signedPower_succ_of_sq_one (a e : Peano) (hsq : a * a = oneInt) :
    signedPower a (successor e) = signedPower a e * a := by
  cases e with
  | zero =>
      change a = oneInt * a
      rw [mul_comm, mul_pos_one]
  | positive n =>
      cases n with
      | one => rfl
      | successor n => rfl
  | negative n =>
      cases n with
      | one =>
          unfold signedPower oneInt
          exact hsq.symm
      | successor n =>
          change power_pos a n = (power_pos a n * a) * a
          rw [mul_assoc, hsq, mul_pos_one]

theorem signedPower_pred_of_sq_one (a e : Peano) (hsq : a * a = oneInt) :
    signedPower a (predecessor e) = signedPower a e * a := by
  cases e with
  | zero =>
      change a = oneInt * a
      rw [mul_comm, mul_pos_one]
  | negative n =>
      cases n with
      | one => rfl
      | successor n => rfl
  | positive n =>
      cases n with
      | one =>
          unfold signedPower oneInt
          exact hsq.symm
      | successor n =>
          change power_pos a n = (power_pos a n * a) * a
          rw [mul_assoc, hsq, mul_pos_one]

theorem signedPower_add_of_sq_one (a y z : Peano) (hsq : a * a = oneInt) :
    signedPower a (y + z) = signedPower a y * signedPower a z := by
  induction z with
  | zero =>
      rw [add_zero]
      unfold signedPower oneInt
      rw [mul_pos_one]
  | positive n =>
      induction n with
      | one =>
          rw [add_pos_one]
          rw [signedPower_succ_of_sq_one a y hsq]
          rfl
      | successor n ih =>
          rw [add_pos_succ]
          rw [signedPower_succ_of_sq_one a (y + positive n) hsq]
          rw [ih]
          change signedPower a y * signedPower a (positive n) * a = signedPower a y * (signedPower a (positive n) * a)
          rw [mul_assoc]
  | negative n =>
      induction n with
      | one =>
          rw [add_neg_one]
          rw [signedPower_pred_of_sq_one a y hsq]
          rfl
      | successor n ih =>
          rw [add_neg_succ]
          rw [signedPower_pred_of_sq_one a (y + negative n) hsq]
          rw [ih]
          change signedPower a y * signedPower a (negative n) * a = signedPower a y * (signedPower a (negative n) * a)
          rw [mul_assoc]

theorem validPowerCondition_oneInt (e : Peano) : ValidPowerCondition oneInt e = true := by
  cases e <;> rfl

theorem validPowerCondition_negOneInt (e : Peano) : ValidPowerCondition negOneInt e = true := by
  cases e <;> rfl

theorem power_oneInt_eq_signedPower (e : Peano) (h : ValidPowerCondition oneInt e = true) :
    power oneInt e h = signedPower oneInt e := by
  cases e with
  | zero => rfl
  | positive n => rfl
  | negative n =>
      change oneInt = power_pos oneInt n
      exact (power_pos_oneInt n).symm

theorem power_negOneInt_eq_signedPower (e : Peano) (h : ValidPowerCondition negOneInt e = true) :
    power negOneInt e h = signedPower negOneInt e := by
  cases e <;> rfl

theorem add_positive_positive (a b : OrdinalNatural.Peano) :
    positive a + positive b = positive (a + b) := by
  induction b with
  | one =>
      rw [add_pos_one, OrdinalNatural.Peano.add_one]
      rfl
  | successor b ih =>
      rw [add_pos_succ, ih, OrdinalNatural.Peano.add_succ]
      rfl

theorem multiply_positive_positive (a b : OrdinalNatural.Peano) :
    positive a * positive b = positive (a * b) := by
  induction b with
  | one =>
      simpa [OrdinalNatural.Peano.multiply_one] using (mul_pos_one (positive a))
  | successor b ih =>
      rw [mul_pos_succ, ih, add_positive_positive]
      simp [OrdinalNatural.Peano.multiply_succ]

theorem negOne_sq : negOneInt * negOneInt = oneInt := by
  rw [mul_neg_one]
  rfl


theorem mul_negOneInt_eq_or (x : Peano) (hx : x = oneInt ∨ x = negOneInt) :
    x * negOneInt = oneInt ∨ x * negOneInt = negOneInt := by
  cases hx with
  | inl hx1 =>
      right
      rw [hx1, mul_neg_one]
      rfl
  | inr hxn1 =>
      left
      rw [hxn1]
      exact negOne_sq

theorem power_pos_negOneInt_eq_or (n : OrdinalNatural.Peano) :
    power_pos negOneInt n = oneInt ∨ power_pos negOneInt n = negOneInt := by
  induction n with
  | one =>
      right
      rfl
  | successor n ih =>
      have hmul : power_pos negOneInt n.successor = power_pos negOneInt n * negOneInt := rfl
      rw [hmul]
      exact mul_negOneInt_eq_or (power_pos negOneInt n) ih

theorem signedPower_negOneInt_eq_or (e : Peano) :
    signedPower negOneInt e = oneInt ∨ signedPower negOneInt e = negOneInt := by
  cases e with
  | zero =>
      left
      rfl
  | positive n =>
      simpa [signedPower] using power_pos_negOneInt_eq_or n
  | negative n =>
      simpa [signedPower] using power_pos_negOneInt_eq_or n

theorem power_negOneInt_eq_or (e : Peano) (h : ValidPowerCondition negOneInt e = true) :
    power negOneInt e h = oneInt ∨ power negOneInt e h = negOneInt := by
  simpa [power_negOneInt_eq_signedPower e h] using (signedPower_negOneInt_eq_or e)

theorem power_add (x y z : Peano) (h : Peano.ValidPowerCondition x y = true) (h2 : Peano.ValidPowerCondition x z = true) :
  ∃ h3, power x (y + z) h3 = power x y h * power x z h2 := by
  cases x with
  | zero =>
      cases y with
      | zero => simp [ValidPowerCondition] at h
      | negative yn => simp [ValidPowerCondition] at h
      | positive yn =>
          cases z with
          | zero => simp [ValidPowerCondition] at h2
          | negative zn => simp [ValidPowerCondition] at h2
          | positive zn =>
              rw [add_positive_positive yn zn]
              refine ⟨?_, ?_⟩
              · rfl
              · change power_pos zero (yn + zn) = power_pos zero yn * power_pos zero zn
                exact power_pos_add zero yn zn
  | positive xn =>
      cases xn with
      | one =>
          refine ⟨validPowerCondition_oneInt (y + z), ?_⟩
          rw [power_oneInt_eq_signedPower, power_oneInt_eq_signedPower, power_oneInt_eq_signedPower]
          exact signedPower_add_of_sq_one oneInt y z (by rw [mul_pos_one])
      | successor xn =>
          cases y with
          | negative yn => simp [ValidPowerCondition] at h
          | zero =>
              cases z with
              | negative zn => simp [ValidPowerCondition] at h2
              | zero =>
                  rw [zero_add]
                  refine ⟨?_, ?_⟩
                  · change ValidPowerCondition (positive xn.successor) zero = true
                    rfl
                  · change oneInt = oneInt * oneInt
                    rw [mul_pos_one]
              | positive zn =>
                  rw [zero_add]
                  refine ⟨?_, ?_⟩
                  · change ValidPowerCondition (positive xn.successor) (positive zn) = true
                    rfl
                  · change power_pos (positive xn.successor) zn = oneInt * power_pos (positive xn.successor) zn
                    rw [mul_comm, mul_pos_one]
          | positive yn =>
              cases z with
              | negative zn => simp [ValidPowerCondition] at h2
              | zero =>
                  rw [add_zero]
                  refine ⟨?_, ?_⟩
                  · rfl
                  · change power_pos (positive xn.successor) yn = power_pos (positive xn.successor) yn * oneInt
                    rw [mul_pos_one]
              | positive zn =>
                  rw [add_positive_positive yn zn]
                  refine ⟨?_, ?_⟩
                  · change ValidPowerCondition (positive xn.successor) (positive (yn + zn)) = true
                    rfl
                  · change power_pos (positive xn.successor) (yn + zn) = power_pos (positive xn.successor) yn * power_pos (positive xn.successor) zn
                    exact power_pos_add (positive xn.successor) yn zn
  | negative xn =>
      cases xn with
      | one =>
          refine ⟨validPowerCondition_negOneInt (y + z), ?_⟩
          rw [power_negOneInt_eq_signedPower, power_negOneInt_eq_signedPower, power_negOneInt_eq_signedPower]
          exact signedPower_add_of_sq_one negOneInt y z negOne_sq
      | successor xn =>
          cases y with
          | negative yn => simp [ValidPowerCondition] at h
          | zero =>
              cases z with
              | negative zn => simp [ValidPowerCondition] at h2
              | zero =>
                  rw [zero_add]
                  refine ⟨?_, ?_⟩
                  · change ValidPowerCondition (negative xn.successor) zero = true
                    rfl
                  · change oneInt = oneInt * oneInt
                    rw [mul_pos_one]
              | positive zn =>
                  rw [zero_add]
                  refine ⟨?_, ?_⟩
                  · change ValidPowerCondition (negative xn.successor) (positive zn) = true
                    rfl
                  · change power_pos (negative xn.successor) zn = oneInt * power_pos (negative xn.successor) zn
                    rw [mul_comm, mul_pos_one]
          | positive yn =>
              cases z with
              | negative zn => simp [ValidPowerCondition] at h2
              | zero =>
                  rw [add_zero]
                  refine ⟨?_, ?_⟩
                  · rfl
                  · change power_pos (negative xn.successor) yn = power_pos (negative xn.successor) yn * oneInt
                    rw [mul_pos_one]
              | positive zn =>
                  rw [add_positive_positive yn zn]
                  refine ⟨?_, ?_⟩
                  · change ValidPowerCondition (negative xn.successor) (positive (yn + zn)) = true
                    rfl
                  · change power_pos (negative xn.successor) (yn + zn) = power_pos (negative xn.successor) yn * power_pos (negative xn.successor) zn
                    exact power_pos_add (negative xn.successor) yn zn

theorem power_multiply (x : Peano) (y z : OrdinalNatural.Peano)
    (h : Peano.ValidPowerCondition x (positive y) = true)
    (h2 : Peano.ValidPowerCondition (power x (positive y) h) (positive z) = true) :
    ∃ h3, power x (positive (y * z)) h3 = power (power x (positive y) h) (positive z) h2 := by
  refine ⟨?_, ?_⟩
  · simp [ValidPowerCondition]
  · change power_pos x (y * z) = power_pos (power_pos x y) z
    exact power_pos_multiply x y z

theorem power_mul_base (x y : Peano) (z : OrdinalNatural.Peano)
    (h : Peano.ValidPowerCondition x (positive z) = true)
    (h2 : Peano.ValidPowerCondition y (positive z) = true) :
    ∃ h3, power (x * y) (positive z) h3 = power x (positive z) h * power y (positive z) h2 := by
  refine ⟨by simp [ValidPowerCondition], ?_⟩
  change power_pos (x * y) z = power_pos x z * power_pos y z
  exact power_pos_mul_base x y z

theorem validPowerCondition_mul (x y z : Peano)
    (hx : ValidPowerCondition x z = true)
    (hy : ValidPowerCondition y z = true) :
    ValidPowerCondition (x * y) z = true := by
  cases z with
  | positive zn => rfl
  | zero =>
      cases x with
      | zero => contradiction
      | positive xn =>
          cases y with
          | zero => contradiction
          | positive yn =>
              change ValidPowerCondition (positive xn * positive yn) zero = true
              have hm : positive xn * positive yn = positive (xn * yn) := multiply_positive_positive xn yn
              rw [hm]
              rfl
          | negative yn =>
              change ValidPowerCondition (positive xn * negative yn) zero = true
              have hm : positive xn * negative yn = -(positive xn * positive yn) := mul_neg (positive xn) (positive yn)
              rw [hm]
              have hmp : positive xn * positive yn = positive (xn * yn) := multiply_positive_positive xn yn
              rw [hmp]
              rfl
      | negative xn =>
          cases y with
          | zero => contradiction
          | positive yn =>
              change ValidPowerCondition (negative xn * positive yn) zero = true
              have hm : negative xn * positive yn = -(positive xn * positive yn) := neg_mul (positive xn) (positive yn)
              rw [hm]
              have hmp : positive xn * positive yn = positive (xn * yn) := multiply_positive_positive xn yn
              rw [hmp]
              rfl
          | negative yn =>
              change ValidPowerCondition (negative xn * negative yn) zero = true
              have hm : negative xn * negative yn = positive xn * positive yn := neg_mul_neg (positive xn) (positive yn)
              rw [hm]
              have hmp : positive xn * positive yn = positive (xn * yn) := multiply_positive_positive xn yn
              rw [hmp]
              rfl
  | negative zn =>
      cases x with
      | zero => contradiction
      | positive xn =>
          cases xn with
          | one =>
              cases y with
              | zero => contradiction
              | positive yn =>
                  cases yn with
                  | one =>
                      change ValidPowerCondition (positive OrdinalNatural.Peano.one * positive OrdinalNatural.Peano.one) (negative zn) = true
                      have hm : positive OrdinalNatural.Peano.one * positive OrdinalNatural.Peano.one = positive OrdinalNatural.Peano.one := mul_pos_one _
                      rw [hm]
                      rfl
                  | successor yn => contradiction
              | negative yn =>
                  cases yn with
                  | one =>
                      change ValidPowerCondition (positive OrdinalNatural.Peano.one * negative OrdinalNatural.Peano.one) (negative zn) = true
                      have hm : positive OrdinalNatural.Peano.one * negative OrdinalNatural.Peano.one = negative OrdinalNatural.Peano.one := mul_neg_one _
                      rw [hm]
                      rfl
                  | successor yn => contradiction
          | successor xn => contradiction
      | negative xn =>
          cases xn with
          | one =>
              cases y with
              | zero => contradiction
              | positive yn =>
                  cases yn with
                  | one =>
                      change ValidPowerCondition (negative OrdinalNatural.Peano.one * positive OrdinalNatural.Peano.one) (negative zn) = true
                      have hm : negative OrdinalNatural.Peano.one * positive OrdinalNatural.Peano.one = negative OrdinalNatural.Peano.one := mul_pos_one _
                      rw [hm]
                      rfl
                  | successor yn => contradiction
              | negative yn =>
                  cases yn with
                  | one =>
                      change ValidPowerCondition (negative OrdinalNatural.Peano.one * negative OrdinalNatural.Peano.one) (negative zn) = true
                      have hm : negative OrdinalNatural.Peano.one * negative OrdinalNatural.Peano.one = positive OrdinalNatural.Peano.one := negOne_sq
                      rw [hm]
                      rfl
                  | successor yn => contradiction
          | successor xn => contradiction

theorem power_mul_base_zero (x y : Peano)
    (h : Peano.ValidPowerCondition x zero = true)
    (h2 : Peano.ValidPowerCondition y zero = true) :
    ∃ h3, power (x * y) zero h3 = power x zero h * power y zero h2 := by
  have power_zero (a : Peano) (ha : ValidPowerCondition a zero = true) : power a zero ha = oneInt := by
    cases a <;> simp [power, ValidPowerCondition] at ha ⊢
  refine ⟨validPowerCondition_mul x y zero h h2, ?_⟩
  rw [power_zero (x * y) (validPowerCondition_mul x y zero h h2)]
  rw [power_zero x h, power_zero y h2]
  rw [mul_pos_one]

theorem power_mul_base_neg_one_one (z : OrdinalNatural.Peano)
    (h : Peano.ValidPowerCondition (positive OrdinalNatural.Peano.one) (negative z) = true)
    (h2 : Peano.ValidPowerCondition (positive OrdinalNatural.Peano.one) (negative z) = true) :
    ∃ h3, power (positive OrdinalNatural.Peano.one * positive OrdinalNatural.Peano.one) (negative z) h3 =
      power (positive OrdinalNatural.Peano.one) (negative z) h *
      power (positive OrdinalNatural.Peano.one) (negative z) h2 := by
  have hm : positive OrdinalNatural.Peano.one * positive OrdinalNatural.Peano.one =
      positive OrdinalNatural.Peano.one := mul_pos_one _
  let h3 : Peano.ValidPowerCondition
      (positive OrdinalNatural.Peano.one * positive OrdinalNatural.Peano.one)
      (negative z) = true := by
        simpa [hm] using h
  refine ⟨h3, ?_⟩
  simp [hm]
  exact (mul_pos_one (positive OrdinalNatural.Peano.one)).symm

theorem power_mul_base_all (x y z : Peano)
    (h : Peano.ValidPowerCondition x z = true)
    (h2 : Peano.ValidPowerCondition y z = true) :
    ∃ h3, power (x * y) z h3 = power x z h * power y z h2 := by
  cases z with
  | positive zn =>
      simpa using power_mul_base x y zn h h2
  | zero =>
      simpa using power_mul_base_zero x y h h2
  | negative zn =>
      cases x with
      | zero =>
          simp [ValidPowerCondition] at h
      | positive xn =>
          cases xn with
          | one =>
              cases y with
              | zero =>
                  simp [ValidPowerCondition] at h2
              | positive yn =>
                  cases yn with
                  | one =>
                      simpa using power_mul_base_neg_one_one zn h h2
                  | successor yn =>
                      simp [ValidPowerCondition] at h2
              | negative yn =>
                  cases yn with
                  | one =>
                      have hxy : positive OrdinalNatural.Peano.one * negative OrdinalNatural.Peano.one =
                          negative OrdinalNatural.Peano.one := mul_neg_one (positive OrdinalNatural.Peano.one)
                      refine ⟨by simpa [hxy] using h, ?_⟩
                      have hone : power (positive OrdinalNatural.Peano.one) (negative zn) h = positive OrdinalNatural.Peano.one := by
                        simp [power, h, power_pos_oneInt]
                      have hmul : power (negative OrdinalNatural.Peano.one) (negative zn) h2 =
                          positive OrdinalNatural.Peano.one * power (negative OrdinalNatural.Peano.one) (negative zn) h2 := by
                        calc
                          power (negative OrdinalNatural.Peano.one) (negative zn) h2
                              = power (negative OrdinalNatural.Peano.one) (negative zn) h2 * positive OrdinalNatural.Peano.one := (mul_pos_one _).symm
                          _ = positive OrdinalNatural.Peano.one * power (negative OrdinalNatural.Peano.one) (negative zn) h2 := by
                                rw [mul_comm]
                      simpa [hxy, hone] using hmul
                  | successor yn =>
                      simp [ValidPowerCondition] at h2
          | successor xn =>
              simp [ValidPowerCondition] at h
      | negative xn =>
          cases xn with
          | one =>
              cases y with
              | zero =>
                  simp [ValidPowerCondition] at h2
              | positive yn =>
                  cases yn with
                  | one =>
                      have hxy : negative OrdinalNatural.Peano.one * positive OrdinalNatural.Peano.one =
                          negative OrdinalNatural.Peano.one := mul_pos_one (negative OrdinalNatural.Peano.one)
                      refine ⟨by simpa [hxy] using h, ?_⟩
                      have hone : power (positive OrdinalNatural.Peano.one) (negative zn) h2 = positive OrdinalNatural.Peano.one := by
                        simp [power, h2, power_pos_oneInt]
                      simpa [hxy, hone, mul_pos_one]
                  | successor yn =>
                      simp [ValidPowerCondition] at h2
              | negative yn =>
                  cases yn with
                  | one =>
                      have hxy : negative OrdinalNatural.Peano.one * negative OrdinalNatural.Peano.one =
                          positive OrdinalNatural.Peano.one := negOne_sq
                      refine ⟨by simpa [hxy] using h, ?_⟩
                      have hx : power (negative OrdinalNatural.Peano.one) (negative zn) h = oneInt ∨
                          power (negative OrdinalNatural.Peano.one) (negative zn) h = negOneInt :=
                        power_negOneInt_eq_or (negative zn) h
                      cases hx with
                      | inl hx1 =>
                          have hone : power (positive OrdinalNatural.Peano.one) (negative zn) (by simp [ValidPowerCondition]) = positive OrdinalNatural.Peano.one := by
                            simp [power, power_pos_oneInt]
                          simpa [hxy, hx1, hone] using (mul_pos_one oneInt).symm
                      | inr hx2 =>
                          have hone : power (positive OrdinalNatural.Peano.one) (negative zn) (by simp [ValidPowerCondition]) = positive OrdinalNatural.Peano.one := by
                            simp [power, power_pos_oneInt]
                          simpa [hxy, hx2, hone] using negOne_sq
                  | successor yn =>
                      simp [ValidPowerCondition] at h2
          | successor xn =>
              simp [ValidPowerCondition] at h

def isPower (e x : Peano) : Prop :=
  ∃ y h, power y e h = x

def principalRoot_pos_rec (orig_x e : Peano) : OrdinalNatural.Peano → Peano
  | OrdinalNatural.Peano.one =>
    if h : ValidPowerCondition (positive OrdinalNatural.Peano.one) e then
      if power (positive OrdinalNatural.Peano.one) e h = orig_x then
        positive OrdinalNatural.Peano.one
      else
        zero
    else
      zero
  | OrdinalNatural.Peano.successor a' =>
    if h : ValidPowerCondition (positive (OrdinalNatural.Peano.successor a')) e then
      if power (positive (OrdinalNatural.Peano.successor a')) e h = orig_x then
        positive (OrdinalNatural.Peano.successor a')
      else
        principalRoot_pos_rec orig_x e a'
    else
      principalRoot_pos_rec orig_x e a'

def principalRoot_neg_rec (orig_x e : Peano) : OrdinalNatural.Peano → Peano
  | OrdinalNatural.Peano.one =>
    if h : ValidPowerCondition (negative OrdinalNatural.Peano.one) e then
      if power (negative OrdinalNatural.Peano.one) e h = orig_x then
        negative OrdinalNatural.Peano.one
      else
        zero
    else
      zero
  | OrdinalNatural.Peano.successor a' =>
    if h : ValidPowerCondition (negative (OrdinalNatural.Peano.successor a')) e then
      if power (negative (OrdinalNatural.Peano.successor a')) e h = orig_x then
        negative (OrdinalNatural.Peano.successor a')
      else
        principalRoot_neg_rec orig_x e a'
    else
      principalRoot_neg_rec orig_x e a'

def principalRoot_rec (orig_x e a : Peano) : Peano :=
  match a with
  | positive n =>
    let pos_res := principalRoot_pos_rec orig_x e n
    if pos_res ≠ zero then pos_res else principalRoot_neg_rec orig_x e n
  | zero => zero
  | negative n =>
    let neg_res := principalRoot_neg_rec orig_x e n
    if neg_res ≠ zero then neg_res else principalRoot_pos_rec orig_x e n

def principalRoot (e x : Peano) (_ : e ≠ zero ∧ isPower e x) : Peano :=
  if h : ValidPowerCondition zero e then
    if power zero e h = x then
      zero
    else
      principalRoot_rec x e x
  else
    principalRoot_rec x e x

end Peano

end ZeroMath.Numbers.Integer
