import ZeroMath.Numbers.OrdinalNatural

namespace ZeroMath.Numbers.Integer

inductive Peano where
  | positive : OrdinalNatural.Peano → Peano
  | zero : Peano
  | negative : OrdinalNatural.Peano → Peano

def Peano.toInt : Peano → Int
  | positive n => n.toNat
  | zero => 0
  | negative n => - (n.toNat : Int)

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

def Peano.sub (a : Peano) : Peano → Peano
  | zero => a
  | positive OrdinalNatural.Peano.one => predecessor a
  | positive (OrdinalNatural.Peano.successor n) => predecessor (sub a (positive n))
  | negative OrdinalNatural.Peano.one => successor a
  | negative (OrdinalNatural.Peano.successor n) => successor (sub a (negative n))

instance : Sub Peano where
  sub := Peano.sub

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

end ZeroMath.Numbers.Integer
