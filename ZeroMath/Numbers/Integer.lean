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
  match a with
  | Peano.positive p => divide_rec (Peano.positive p) b a
  | Peano.negative p => divide_rec (Peano.positive p) b a
  | Peano.zero => Peano.zero

end ZeroMath.Numbers.Integer
