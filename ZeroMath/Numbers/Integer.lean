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
  | Peano.negative _ => Peano.zero

def Peano.divide (a b : Peano) (_ : isDivisible a b) : Peano :=
  divide_rec a b a

def Peano.fromInt : Int → Peano
  | Int.ofNat 0 => Peano.zero
  | Int.ofNat (n + 1) => Peano.positive (OrdinalNatural.Peano.fromNat (n + 1) (Nat.succ_ne_zero n))
  | Int.negSucc n => Peano.negative (OrdinalNatural.Peano.fromNat (n + 1) (Nat.succ_ne_zero n))

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

theorem Peano.divide_positive_one_multiply_negative_one_eq_zero
  (h : isDivisible (positive OrdinalNatural.Peano.one * negative OrdinalNatural.Peano.one)
    (positive OrdinalNatural.Peano.one)) :
  divide (positive OrdinalNatural.Peano.one * negative OrdinalNatural.Peano.one)
    (positive OrdinalNatural.Peano.one) h = zero := by
  unfold Peano.divide
  rw [Peano.mul_neg_one]
  have hneg : -positive OrdinalNatural.Peano.one = negative OrdinalNatural.Peano.one := rfl
  rw [hneg]
  unfold Peano.divide_rec
  rfl

theorem Peano.divide_positive_one_multiply_negative_one_ne_negative_one :
  ∃ h, divide (positive OrdinalNatural.Peano.one * negative OrdinalNatural.Peano.one)
    (positive OrdinalNatural.Peano.one) h ≠ negative OrdinalNatural.Peano.one := by
  have h : isDivisible (positive OrdinalNatural.Peano.one * negative OrdinalNatural.Peano.one)
    (positive OrdinalNatural.Peano.one) := by
    constructor
    · intro hzero
      cases hzero
    · exists negative OrdinalNatural.Peano.one
  refine ⟨h, ?_⟩
  rw [divide_positive_one_multiply_negative_one_eq_zero h]
  intro hzero
  cases hzero

theorem Peano.divide_negative_one_multiply_positive_one_eq_zero
  (h : isDivisible (negative OrdinalNatural.Peano.one * positive OrdinalNatural.Peano.one)
    (negative OrdinalNatural.Peano.one)) :
  divide (negative OrdinalNatural.Peano.one * positive OrdinalNatural.Peano.one)
    (negative OrdinalNatural.Peano.one) h = zero := by
  unfold Peano.divide
  rw [Peano.mul_pos_one]
  unfold Peano.divide_rec
  rfl

theorem Peano.divide_negative_one_multiply_positive_one_ne_positive_one :
  ∃ h, divide (negative OrdinalNatural.Peano.one * positive OrdinalNatural.Peano.one)
    (negative OrdinalNatural.Peano.one) h ≠ positive OrdinalNatural.Peano.one := by
  have h : isDivisible (negative OrdinalNatural.Peano.one * positive OrdinalNatural.Peano.one)
    (negative OrdinalNatural.Peano.one) := by
    constructor
    · intro hzero
      cases hzero
    · exists positive OrdinalNatural.Peano.one
  refine ⟨h, ?_⟩
  rw [divide_negative_one_multiply_positive_one_eq_zero h]
  intro hzero
  cases hzero

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

end ZeroMath.Numbers.Integer
