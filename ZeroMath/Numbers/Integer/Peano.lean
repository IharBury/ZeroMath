import ZeroMath.Numbers.OrdinalNatural.Peano

namespace ZeroMath.Numbers.Integer

inductive Peano where
  | positive : OrdinalNatural.Peano → Peano
  | zero : Peano
  | negative : OrdinalNatural.Peano → Peano

namespace Peano

deriving instance DecidableEq for Peano

def one := positive OrdinalNatural.Peano.one
def two := positive OrdinalNatural.Peano.two
def minusOne := negative OrdinalNatural.Peano.one

def toInt : Peano → Int
  | positive n => n.toNat
  | zero => 0
  | negative n => - (n.toNat : Int)

def negate : Peano → Peano
  | positive n => negative n
  | zero => zero
  | negative n => positive n

def absoluteValue : Peano → Peano
  | positive n => positive n
  | zero => zero
  | negative n => positive n

instance : Neg Peano where
  neg := negate

inductive LessThan : Peano → Peano → Prop where
  | negative_less_than_zero {n : OrdinalNatural.Peano} : LessThan (negative n) zero
  | zero_less_than_positive {n : OrdinalNatural.Peano} : LessThan zero (positive n)
  | negative_less_than_positive {n m : OrdinalNatural.Peano} : LessThan (negative n) (positive m)
  | positive_less_than_positive {n m : OrdinalNatural.Peano} : n < m → LessThan (positive n) (positive m)
  | negative_less_than_negative {n m : OrdinalNatural.Peano} : m < n → LessThan (negative n) (negative m)

instance : LT Peano where
  lt := LessThan

def toOrdinalNatural (x : Peano) (h : zero < x) : OrdinalNatural.Peano :=
  match x, h with
  | positive n, _ => n

def LessThanOrEqual (a b : Peano) : Prop :=
  LessThan a b ∨ a = b

instance : LE Peano where
  le := LessThanOrEqual

def isLessThan : Peano → Peano → Bool
  | negative _, zero => true
  | zero, positive _ => true
  | negative _, positive _ => true
  | positive n, positive m => OrdinalNatural.Peano.isLessThan n m
  | negative n, negative m => OrdinalNatural.Peano.isLessThan m n
  | _, _ => false

theorem isLessThan_eq_true_iff_lt (a b : Peano) : isLessThan a b = true ↔ a < b := by
  constructor
  · intro h
    cases a
    case negative n =>
      cases b
      case negative m =>
        apply LessThan.negative_less_than_negative
        apply (OrdinalNatural.Peano.isLessThan_eq_true_iff_lt m n).mp
        exact h
      case zero => exact LessThan.negative_less_than_zero
      case positive m => exact LessThan.negative_less_than_positive
    case zero =>
      cases b
      case negative m => contradiction
      case zero => contradiction
      case positive m => exact LessThan.zero_less_than_positive
    case positive n =>
      cases b
      case negative m => contradiction
      case zero => contradiction
      case positive m =>
        apply LessThan.positive_less_than_positive
        apply (OrdinalNatural.Peano.isLessThan_eq_true_iff_lt n m).mp
        exact h
  · intro h
    cases h
    case negative_less_than_zero => rfl
    case zero_less_than_positive => rfl
    case negative_less_than_positive => rfl
    case positive_less_than_positive hlt =>
      dsimp [isLessThan]
      exact (OrdinalNatural.Peano.isLessThan_eq_true_iff_lt _ _).mpr hlt
    case negative_less_than_negative hlt =>
      dsimp [isLessThan]
      exact (OrdinalNatural.Peano.isLessThan_eq_true_iff_lt _ _).mpr hlt

theorem isLessThan_eq_false_iff_not_lt (a b : Peano) : isLessThan a b = false ↔ ¬ (a < b) := by
  constructor
  · intro h1 hlt
    have h2 := (isLessThan_eq_true_iff_lt a b).mpr hlt
    rw [h1] at h2
    contradiction
  · intro h1
    cases h2 : isLessThan a b
    · rfl
    · have h3 := (isLessThan_eq_true_iff_lt a b).mp h2
      contradiction

def successor : Peano → Peano
  | negative (OrdinalNatural.Peano.successor n) => negative n
  | negative OrdinalNatural.Peano.one => zero
  | zero => positive OrdinalNatural.Peano.one
  | positive n => positive (OrdinalNatural.Peano.successor n)

def predecessor : Peano → Peano
  | positive (OrdinalNatural.Peano.successor n) => positive n
  | positive OrdinalNatural.Peano.one => zero
  | zero => negative OrdinalNatural.Peano.one
  | negative n => negative (OrdinalNatural.Peano.successor n)

def add (a : Peano) : Peano → Peano
  | zero => a
  | positive OrdinalNatural.Peano.one => successor a
  | positive (OrdinalNatural.Peano.successor n) => successor (add a (positive n))
  | negative OrdinalNatural.Peano.one => predecessor a
  | negative (OrdinalNatural.Peano.successor n) => predecessor (add a (negative n))

instance : Add Peano where
  add := add

def subtract (a : Peano) : Peano → Peano
  | zero => a
  | positive OrdinalNatural.Peano.one => predecessor a
  | positive (OrdinalNatural.Peano.successor n) => predecessor (subtract a (positive n))
  | negative OrdinalNatural.Peano.one => successor a
  | negative (OrdinalNatural.Peano.successor n) => successor (subtract a (negative n))

instance : Sub Peano where
  sub := Peano.subtract

def multiply (a : Peano) : Peano → Peano
  | zero => zero
  | positive OrdinalNatural.Peano.one => a
  | positive (OrdinalNatural.Peano.successor n) => multiply a (positive n) + a
  | negative OrdinalNatural.Peano.one => -a
  | negative (OrdinalNatural.Peano.successor n) => multiply a (negative n) - a

instance : Mul Peano where
  mul := multiply

@[simp]
theorem sub_zero (a : Peano) : a - zero = a := by
  have h : a - zero = subtract a zero := rfl
  rw [h]
  rw [subtract.eq_def]

theorem sub_pos_one (a : Peano) : a - positive OrdinalNatural.Peano.one = predecessor a := by
  have h : a - positive OrdinalNatural.Peano.one = subtract a (positive OrdinalNatural.Peano.one) := rfl
  rw [h]
  rw [subtract.eq_def]

theorem sub_pos_succ (a : Peano) (n : OrdinalNatural.Peano) : a - positive (OrdinalNatural.Peano.successor n) = predecessor (a - positive n) := by
  have h1 : a - positive (OrdinalNatural.Peano.successor n) = subtract a (positive (OrdinalNatural.Peano.successor n)) := rfl
  have h2 : a - positive n = subtract a (positive n) := rfl
  rw [h1, h2]
  rw [subtract.eq_def]

theorem sub_neg_one (a : Peano) : a - negative OrdinalNatural.Peano.one = successor a := by
  have h : a - negative OrdinalNatural.Peano.one = subtract a (negative OrdinalNatural.Peano.one) := rfl
  rw [h]
  rw [Peano.subtract.eq_def]

theorem sub_neg_succ (a : Peano) (n : OrdinalNatural.Peano) : a - negative (OrdinalNatural.Peano.successor n) = successor (a - negative n) := by
  have h1 : a - negative (OrdinalNatural.Peano.successor n) = subtract a (negative (OrdinalNatural.Peano.successor n)) := rfl
  have h2 : a - negative n = subtract a (negative n) := rfl
  rw [h1, h2]
  rw [subtract.eq_def]

theorem add_pos_one (a : Peano) : a + positive OrdinalNatural.Peano.one = successor a := by
  have h : a + positive OrdinalNatural.Peano.one = add a (positive OrdinalNatural.Peano.one) := rfl
  rw [h]
  rw [add.eq_def]

theorem add_pos_succ (a : Peano) (n : OrdinalNatural.Peano) : a + positive (OrdinalNatural.Peano.successor n) = successor (a + positive n) := by
  have h1 : a + positive (OrdinalNatural.Peano.successor n) = add a (positive (OrdinalNatural.Peano.successor n)) := rfl
  have h2 : a + positive n = add a (positive n) := rfl
  rw [h1, h2]
  rw [add.eq_def]

theorem add_neg_one (a : Peano) : a + negative OrdinalNatural.Peano.one = predecessor a := by
  have h : a + negative OrdinalNatural.Peano.one = add a (negative OrdinalNatural.Peano.one) := rfl
  rw [h]
  rw [add.eq_def]

theorem add_neg_succ (a : Peano) (n : OrdinalNatural.Peano) : a + negative (OrdinalNatural.Peano.successor n) = predecessor (a + negative n) := by
  have h1 : a + negative (OrdinalNatural.Peano.successor n) = add a (negative (OrdinalNatural.Peano.successor n)) := rfl
  have h2 : a + negative n = add a (negative n) := rfl
  rw [h1, h2]
  rw [add.eq_def]

@[simp]
theorem add_zero (a : Peano) : a + zero = a := by
  have h : a + zero = add a zero := rfl
  rw [h]
  rw [add.eq_def]

@[simp]
theorem zero_add (a : Peano) : zero + a = a := by
  cases a with
  | zero =>
    rw [add_zero]
  | positive n =>
    induction n with
    | one =>
      rw [add_pos_one, successor]
    | successor n ih =>
      rw [add_pos_succ, ih, successor]
  | negative n =>
    induction n with
    | one =>
      rw [add_neg_one, predecessor]
    | successor n ih =>
      rw [add_neg_succ, ih, predecessor]

@[simp]
theorem succ_pred (a : Peano) : successor (predecessor a) = a := by
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

@[simp]
theorem pred_succ (a : Peano) : predecessor (successor a) = a := by
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

@[simp]
theorem succ_add (a b : Peano) : successor a + b = successor (a + b) := by
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

@[simp]
theorem pred_add (a b : Peano) : predecessor a + b = predecessor (a + b) := by
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

@[simp]
theorem succ_sub (a b : Peano) : successor a - b = successor (a - b) := by
  induction b with
  | zero =>
    rw [sub_zero, sub_zero]
  | positive n =>
    induction n with
    | one =>
      rw [sub_pos_one, sub_pos_one]
      rw [pred_succ, succ_pred]
    | successor n ih =>
      rw [sub_pos_succ, sub_pos_succ]
      rw [ih, pred_succ, succ_pred]
  | negative n =>
    induction n with
    | one =>
      rw [sub_neg_one, sub_neg_one]
    | successor n ih =>
      rw [sub_neg_succ, sub_neg_succ]
      rw [ih]

@[simp]
theorem pred_sub (a b : Peano) : predecessor a - b = predecessor (a - b) := by
  induction b with
  | zero =>
    rw [sub_zero, sub_zero]
  | positive n =>
    induction n with
    | one =>
      rw [sub_pos_one, sub_pos_one]
    | successor n ih =>
      rw [sub_pos_succ, sub_pos_succ]
      rw [ih]
  | negative n =>
    induction n with
    | one =>
      rw [sub_neg_one, sub_neg_one]
      rw [succ_pred, pred_succ]
    | successor n ih =>
      rw [sub_neg_succ, sub_neg_succ]
      rw [ih, succ_pred, pred_succ]

theorem lt_trans {a b c : Peano} (h1 : a < b) (h2 : b < c) : a < c := by
  cases h1 with
  | negative_less_than_zero =>
    cases h2 with
    | zero_less_than_positive => exact LessThan.negative_less_than_positive
  | zero_less_than_positive =>
    cases h2 with
    | positive_less_than_positive h => exact LessThan.zero_less_than_positive
  | negative_less_than_positive =>
    cases h2 with
    | positive_less_than_positive h => exact LessThan.negative_less_than_positive
  | positive_less_than_positive h =>
    cases h2 with
    | positive_less_than_positive h' => exact LessThan.positive_less_than_positive (OrdinalNatural.Peano.lt_trans h h')
  | negative_less_than_negative h =>
    cases h2 with
    | negative_less_than_zero => exact LessThan.negative_less_than_zero
    | negative_less_than_positive => exact LessThan.negative_less_than_positive
    | negative_less_than_negative h' => exact LessThan.negative_less_than_negative (OrdinalNatural.Peano.lt_trans h' h)

theorem le_trans {a b c : Peano} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  cases h1 with
  | inl h1_lt =>
    cases h2 with
    | inl h2_lt => exact Or.inl (lt_trans h1_lt h2_lt)
    | inr h2_eq =>
      rw [← h2_eq]
      exact Or.inl h1_lt
  | inr h1_eq =>
    rw [h1_eq]
    exact h2

theorem add_comm (a b : Peano) : a + b = b + a := by
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

theorem not_lt_self (x : Peano) : ¬ (x < x) := by
  intro h
  cases h with
  | positive_less_than_positive h' =>
    exact OrdinalNatural.Peano.not_lt_self _ h'
  | negative_less_than_negative h' =>
    exact OrdinalNatural.Peano.not_lt_self _ h'

theorem not_lt_of_lt {x y : Peano} (h : x < y) : ¬ (y < x) := by
  intro h2
  have h3 := lt_trans h h2
  exact not_lt_self x h3

theorem ne_of_lt {x y : Peano} (h : x < y) : x ≠ y := by
  intro heq
  subst heq
  exact not_lt_self x h

theorem trichotomy_or (x y : Peano) : x < y ∨ x = y ∨ y < x := by
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

theorem add_sub_cancel (a b : Peano) : a + b - b = a := by
  induction b with
  | zero =>
    rw [add_zero, sub_zero]
  | positive n =>
    induction n with
    | one =>
      rw [add_pos_one, sub_pos_one, pred_succ]
    | successor n ih =>
      rw [add_pos_succ, sub_pos_succ]
      rw [succ_sub]
      rw [pred_succ]
      exact ih
  | negative n =>
    induction n with
    | one =>
      rw [add_neg_one, sub_neg_one, succ_pred]
    | successor n ih =>
      rw [add_neg_succ, sub_neg_succ]
      rw [pred_sub]
      rw [succ_pred]
      exact ih

theorem sub_add_cancel (a b : Peano) : a - b + b = a := by
  induction b with
  | zero =>
    rw [sub_zero, add_zero]
  | positive n =>
    induction n with
    | one =>
      rw [sub_pos_one, add_pos_one, succ_pred]
    | successor n ih =>
      rw [sub_pos_succ, add_pos_succ]
      rw [pred_add]
      rw [succ_pred]
      exact ih
  | negative n =>
    induction n with
    | one =>
      rw [sub_neg_one, add_neg_one, pred_succ]
    | successor n ih =>
      rw [sub_neg_succ, add_neg_succ]
      rw [succ_add]
      rw [pred_succ]
      exact ih

theorem trichotomy (x y : Peano) : Logic.Trichotomy (x < y) (x = y) (y < x) := by
  cases trichotomy_or x y with
  | inl h =>
    exact Logic.Trichotomy.first h (ne_of_lt h) (not_lt_of_lt h)
  | inr h =>
    cases h with
    | inl h =>
      subst h
      exact Logic.Trichotomy.second rfl (not_lt_self x) (not_lt_self x)
    | inr h =>
      exact Logic.Trichotomy.third h (not_lt_of_lt h) (ne_of_lt h).symm

@[simp]
theorem add_succ (a b : Peano) : a + successor b = successor (a + b) := by
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

@[simp]
theorem add_pred (a b : Peano) : a + predecessor b = predecessor (a + b) := by
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

theorem add_assoc (a b c : Peano) : a + b + c = a + (b + c) := by
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

@[simp]
theorem add_neg_self (a : Peano) : a + -a = zero := by
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

@[simp]
theorem neg_add_self (a : Peano) : -a + a = zero := by
  rw [add_comm, add_neg_self]

@[simp]
theorem mul_pos_one (a : Peano) : a * positive OrdinalNatural.Peano.one = a := by
  have h : a * positive OrdinalNatural.Peano.one = multiply a (positive OrdinalNatural.Peano.one) := rfl
  rw [h]
  rw [multiply.eq_def]

theorem mul_pos_succ (a : Peano) (n : OrdinalNatural.Peano) : a * positive n.successor = a * positive n + a := by
  have h1 : a * positive n.successor = multiply a (positive n.successor) := rfl
  have h2 : a * positive n = multiply a (positive n) := rfl
  rw [h1, h2]
  rw [multiply.eq_def]

@[simp]
theorem mul_neg_one (a : Peano) : a * negative OrdinalNatural.Peano.one = -a := by
  have h : a * negative OrdinalNatural.Peano.one = multiply a (negative OrdinalNatural.Peano.one) := rfl
  rw [h]
  rw [multiply.eq_def]

theorem mul_neg_succ (a : Peano) (n : OrdinalNatural.Peano) : a * negative n.successor = a * negative n - a := by
  have h1 : a * negative n.successor = multiply a (negative n.successor) := rfl
  have h2 : a * negative n = multiply a (negative n) := rfl
  rw [h1, h2]
  rw [multiply.eq_def]

theorem mul_zero (a : Peano) : a * zero = zero := by
  have h : a * zero = multiply a zero := rfl
  rw [h]
  rw [multiply.eq_def]

@[simp]
theorem zero_mul (a : Peano) : zero * a = zero := by
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

@[simp]
theorem mul_succ (a b : Peano) : a * successor b = a * b + a := by
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

theorem sub_eq_add_neg (a b : Peano) : a - b = a + -b := by
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

@[simp]
theorem zero_sub (a : Peano) : zero - a = -a := by
  rw [sub_eq_add_neg, zero_add]

@[simp]
theorem sub_self (a : Peano) : a - a = zero := by
  rw [sub_eq_add_neg, add_neg_self]

@[simp]
theorem mul_pred (a b : Peano) : a * predecessor b = a * b - a := by
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

def isDivisible (a b : Peano) : Prop := b ≠ zero ∧ ∃ c, b * c = a

def divide_rec (a b x : OrdinalNatural.Peano) (h : OrdinalNatural.Peano.isDivisible a b) (h2 : ∀ c, x < c → b * c ≠ a) :
  OrdinalNatural.Peano :=
  if h3 : b * x = a then
    x
  else
    match x with
    | .one => False.elim sorry
    | .successor x' => divide_rec a b x' h sorry

def divide (a b : Peano) (h : isDivisible a b) : Peano :=
  match a, b with
  | _, zero => False.elim sorry
  | zero, _ => zero
  | positive a', positive b' => positive (divide_rec a' b' a' sorry sorry)
  | positive a', negative b' => negative (divide_rec a' b' a' sorry sorry)
  | negative a', positive b' => negative (divide_rec a' b' a' sorry sorry)
  | negative a', negative b' => positive (divide_rec a' b' a' sorry sorry)

@[simp]
theorem toInt_successor (a : Peano) : (successor a).toInt = a.toInt + 1 := by
  cases a with
  | zero => rfl
  | positive n => cases n <;> rfl
  | negative n =>
    cases n with
    | one => rfl
    | successor n =>
      simp [successor, toInt, ZeroMath.Numbers.OrdinalNatural.Peano.toNat] <;> omega

@[simp]
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

@[simp]
theorem toInt_negate (a : Peano) : (-a).toInt = -a.toInt := by
  cases a with
  | zero => rfl
  | positive n => rfl
  | negative n =>
    simp [Neg.neg, Peano.negate, toInt]
    exact (Int.neg_neg (n.toNat : Int)).symm

@[simp]
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

@[simp]
theorem toInt_subtract (a b : Peano) : (a - b).toInt = a.toInt - b.toInt := by
  rw [sub_eq_add_neg, toInt_add, toInt_negate]
  omega

@[simp]
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

@[simp]
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
  sorry

def fromInt : Int → Peano
  | Int.ofNat 0 => Peano.zero
  | Int.ofNat (n + 1) => Peano.positive (OrdinalNatural.Peano.fromNat (n + 1) (Nat.succ_ne_zero n))
  | Int.negSucc n => Peano.negative (OrdinalNatural.Peano.fromNat (n + 1) (Nat.succ_ne_zero n))

@[simp]
theorem toInt_fromInt (x : Int) : (fromInt x).toInt = x := by
  cases x with
  | ofNat n =>
    cases n with
    | zero =>
      rfl
    | succ n =>
      unfold fromInt toInt
      simp [OrdinalNatural.Peano.toNat_fromNat]
  | negSucc n =>
    unfold fromInt toInt
    simp [OrdinalNatural.Peano.toNat_fromNat]
    rfl

@[simp]
theorem fromInt_toInt (x : Peano) : fromInt (x.toInt) = x := by
  cases x with
  | zero => rfl
  | positive n =>
    change fromInt (n.toNat : Int) = positive n
    cases h_nat : n.toNat with
    | zero =>
      have hne := OrdinalNatural.Peano.toNat_ne_zero n
      rw [h_nat] at hne
      contradiction
    | succ k =>
      change fromInt (Int.ofNat (k + 1)) = positive n
      have h1 : fromInt (Int.ofNat (k + 1)) = positive (OrdinalNatural.Peano.fromNat (k + 1) (Nat.succ_ne_zero k)) := rfl
      rw [h1]
      congr
      apply OrdinalNatural.Peano.fromNat_toNat_helper
      rw [h_nat]
  | negative n =>
    change fromInt (- (n.toNat : Int)) = negative n
    cases h_nat : n.toNat with
    | zero =>
      have hne := OrdinalNatural.Peano.toNat_ne_zero n
      rw [h_nat] at hne
      contradiction
    | succ k =>
      change fromInt (Int.negSucc k) = negative n
      have h1 : fromInt (Int.negSucc k) = negative (OrdinalNatural.Peano.fromNat (k + 1) (Nat.succ_ne_zero k)) := rfl
      rw [h1]
      congr
      apply OrdinalNatural.Peano.fromNat_toNat_helper
      rw [h_nat]

theorem mul_add (a b c : Peano) : a * (b + c) = a * b + a * c := by
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

@[simp]
theorem neg_succ (a : Peano) : -(successor a) = predecessor (-a) := by
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

@[simp]
theorem neg_pred (a : Peano) : -(predecessor a) = successor (-a) := by
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

@[simp]
theorem neg_add (a b : Peano) : -(a + b) = -a + -b := by
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

@[simp]
theorem neg_neg (x : Peano) : -(-x) = x := by
  cases x with
  | zero => rfl
  | positive n => rfl
  | negative n => rfl

@[simp]
theorem sub_neg (a b : Peano) : a - (-b) = a + b := by
  rw [sub_eq_add_neg, neg_neg]

@[simp]
theorem neg_sub (a b : Peano) : -(a - b) = -a + b := by
  rw [sub_eq_add_neg, neg_add, neg_neg]

@[simp]
theorem neg_mul (a b : Peano) : (-a) * b = -(a * b) := by
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

@[simp]
theorem mul_neg (a b : Peano) : a * (-b) = -(a * b) := by
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

@[simp]
theorem neg_mul_neg (x y : Peano) : (-x) * (-y) = x * y := by
  rw [neg_mul, mul_neg, neg_neg]

theorem add_right_comm (a b c : Peano) : a + b + c = a + c + b := by
  rw [add_assoc, add_comm b c, ←add_assoc]

@[simp]
theorem succ_mul (a b : Peano) : successor a * b = a * b + b := by
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

@[simp]
theorem pred_mul (a b : Peano) : predecessor a * b = a * b - b := by
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

theorem mul_comm (a b : Peano) : a * b = b * a := by
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

theorem divide_multiply_positive_one_eq (x : OrdinalNatural.Peano) :
  ∃ h, divide (positive OrdinalNatural.Peano.one * positive x) (positive OrdinalNatural.Peano.one) h = positive x := by
  sorry

theorem divide_multiply_negative_one_eq (x : OrdinalNatural.Peano) :
  ∃ h, divide (negative OrdinalNatural.Peano.one * negative x) (negative OrdinalNatural.Peano.one) h = negative x := by
  sorry

theorem divide_multiply_zero_eq (y : Peano) (hy : y ≠ zero) :
  ∃ h, divide (y * zero) y h = zero := by
  sorry

theorem divide_zero_multiply_eq (y : Peano) (hy : y ≠ zero) :
  ∃ h, divide (zero * y) y h = zero := by
  sorry

theorem divide_multiply_positive_one_nonnegative_eq (x : Peano)
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

theorem divide_multiply_negative_one_nonpositive_eq (x : Peano)
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

theorem divide_multiply_unit_same_sign_eq (x y : Peano)
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

theorem divide_multiply_positive_one_negative_eq (x : OrdinalNatural.Peano) :
  ∃ h, divide (positive OrdinalNatural.Peano.one * negative x) (positive OrdinalNatural.Peano.one) h = negative x := by
  sorry

theorem divide_multiply_negative_one_positive_eq (x : OrdinalNatural.Peano) :
  ∃ h, divide (negative OrdinalNatural.Peano.one * positive x) (negative OrdinalNatural.Peano.one) h = positive x := by
  sorry

theorem divide_multiply_positive_one_any_eq (x : Peano) :
  ∃ h, divide (positive OrdinalNatural.Peano.one * x) (positive OrdinalNatural.Peano.one) h = x := by
  cases x with
  | zero =>
    exact divide_multiply_zero_eq (positive OrdinalNatural.Peano.one) (by intro h; cases h)
  | positive n =>
    exact divide_multiply_positive_one_eq n
  | negative n =>
    exact divide_multiply_positive_one_negative_eq n

theorem divide_multiply_negative_one_any_eq (x : Peano) :
  ∃ h, divide (negative OrdinalNatural.Peano.one * x) (negative OrdinalNatural.Peano.one) h = x := by
  cases x with
  | zero =>
    exact divide_multiply_zero_eq (negative OrdinalNatural.Peano.one) (by intro h; cases h)
  | positive n =>
    exact divide_multiply_negative_one_positive_eq n
  | negative n =>
    exact divide_multiply_negative_one_eq n

theorem divide_multiply_right_positive_one_any_eq (x : Peano) :
  ∃ h, divide (x * positive OrdinalNatural.Peano.one) (positive OrdinalNatural.Peano.one) h = x := by
  sorry

theorem divide_multiply_right_negative_one_any_eq (x : Peano) :
  ∃ h, divide (x * negative OrdinalNatural.Peano.one) (negative OrdinalNatural.Peano.one) h = x := by
  sorry

theorem divide_multiply_unit_any_eq (x y : Peano)
  (hy : y = positive OrdinalNatural.Peano.one ∨ y = negative OrdinalNatural.Peano.one) :
  ∃ h, divide (y * x) y h = x := by
  cases hy with
  | inl hpos =>
    subst hpos
    exact divide_multiply_positive_one_any_eq x
  | inr hneg =>
    subst hneg
    exact divide_multiply_negative_one_any_eq x

theorem divide_multiply_right_unit_any_eq (x y : Peano)
  (hy : y = positive OrdinalNatural.Peano.one ∨ y = negative OrdinalNatural.Peano.one) :
  ∃ h, divide (x * y) y h = x := by
  cases hy with
  | inl hpos =>
    subst hpos
    exact divide_multiply_right_positive_one_any_eq x
  | inr hneg =>
    subst hneg
    exact divide_multiply_right_negative_one_any_eq x

theorem divide_multiply_unit_or_zero_eq (x y : Peano)
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

theorem divide_multiply_right_unit_or_zero_eq (x y : Peano)
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

theorem division_reverses_right_multiplication (x y : Peano) (hy : y ≠ zero) :
  ∃ h, divide (x * y) y h = x := by
  rw [mul_comm x y]
  exact division_reverses_multiplication x y hy

theorem sub_mul (a b c : Peano) : (a - b) * c = a * c - b * c := by
  rw [sub_eq_add_neg, sub_eq_add_neg (a*c)]
  have h_add_mul : (a + -b) * c = a * c + (-b) * c := by
    rw [mul_comm, mul_add, mul_comm, mul_comm c (-b)]
  rw [h_add_mul, neg_mul]

theorem mul_sub (a b c : Peano) : a * (b - c) = a * b - a * c := by
  rw [mul_comm, sub_mul, mul_comm b a, mul_comm c a]

theorem mul_assoc (a b c : Peano) : (a * b) * c = a * (b * c) := by
  induction c with
  | zero =>
    rw [mul_zero, mul_zero, mul_zero]
  | positive n =>
    induction n with
    | one =>
      rw [mul_pos_one, mul_pos_one]
    | successor m ih =>
      rw [mul_pos_succ, mul_pos_succ, mul_add, ih]
  | negative n =>
    induction n with
    | one =>
      rw [mul_neg_one, mul_neg_one, mul_neg]
    | successor m ih =>
      rw [mul_neg_succ, mul_neg_succ, mul_sub, ih]

theorem sub_assoc (x y z : Peano) : x + y - z = x + (y - z) := by
  rw [sub_eq_add_neg, sub_eq_add_neg, add_assoc]

theorem sub_sub (x y z : Peano) : x - y - z = x - (y + z) := by
  rw [sub_eq_add_neg (x - y) z]
  rw [sub_eq_add_neg x y]
  rw [sub_eq_add_neg x (y + z)]
  rw [neg_add, add_assoc]

theorem multiply_divide_cancel (x y : Peano) (h : isDivisible x y) : (divide x y h) * y = x := by
  sorry

theorem divide_add (x y z : Peano) (h : isDivisible x z) (h2 : isDivisible y z) :
  ∃ h3, divide (x + y) z h3 = divide x z h + divide y z h2 := by
  sorry

theorem divide_sub (x y z : Peano) (h : isDivisible x z) (h2 : isDivisible y z) :
  ∃ h3, divide (x - y) z h3 = divide x z h - divide y z h2 := by
  sorry

theorem mul_eq_zero_iff (x y : Peano) : x * y = zero ↔ x = zero ∨ y = zero := by
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

theorem divide_multiply (x y z : Peano) (h : isDivisible y z) :
  ∃ h2, divide (x * y) z h2 = x * divide y z h := by
  sorry

theorem divide_divide (x y z : Peano) (h : isDivisible x y) (h2 : isDivisible (divide x y h) z) :
  ∃ h3, divide (divide x y h) z h2 = divide x (y * z) h3 := by
  sorry

def power_pos (a : Peano) : OrdinalNatural.Peano → Peano
  | OrdinalNatural.Peano.one => a
  | OrdinalNatural.Peano.successor n => power_pos a n * a

def ValidPowerCondition (a b : Peano) : Bool :=
  match a, b with
  | _, Peano.positive _ => true
  | Peano.positive _, Peano.zero => true
  | Peano.negative _, Peano.zero => true
  | Peano.positive OrdinalNatural.Peano.one, Peano.negative _ => true
  | Peano.negative OrdinalNatural.Peano.one, Peano.negative _ => true
  | _, _ => false

def power : (a b : Peano) → (h : ValidPowerCondition a b = true) → Peano
  | zero, positive _, _ => zero
  | _, zero, _ => one
  | a, positive n, _ => power_pos a n
  | a, negative n, _ => divide one (power_pos a n) sorry

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

theorem power_pos_oneInt (e : OrdinalNatural.Peano) : power_pos one e = one := by
  induction e with
  | one => rfl
  | successor e ih =>
      change power_pos one e * one = one
      rw [ih, one, mul_pos_one]

theorem validPowerCondition_oneInt (e : Peano) : ValidPowerCondition one e = true := by
  cases e <;> rfl

theorem validPowerCondition_negOneInt (e : Peano) : ValidPowerCondition minusOne e = true := by
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
      simp [OrdinalNatural.Peano.multiply_one]
  | successor b ih =>
      rw [mul_pos_succ, ih, add_positive_positive]
      simp [OrdinalNatural.Peano.multiply_succ]

theorem negOne_sq : minusOne * minusOne = one := by
  sorry

theorem mul_negOneInt_eq_or (x : Peano) (hx : x = one ∨ x = minusOne) :
    x * minusOne = one ∨ x * minusOne = minusOne := by
  cases hx with
  | inl hx1 =>
      right
      rw [hx1, minusOne, mul_neg_one]
      rfl
  | inr hxn1 =>
      left
      rw [hxn1]
      exact negOne_sq

theorem power_pos_negOneInt_eq_or (n : OrdinalNatural.Peano) :
    power_pos minusOne n = one ∨ power_pos minusOne n = minusOne := by
  induction n with
  | one =>
      right
      rfl
  | successor n ih =>
      have hmul : power_pos minusOne n.successor = power_pos minusOne n * minusOne := rfl
      rw [hmul]
      exact mul_negOneInt_eq_or (power_pos minusOne n) ih

theorem power_add (x y z : Peano) (h : Peano.ValidPowerCondition x y = true) (h2 : Peano.ValidPowerCondition x z = true) :
  ∃ h3, power x (y + z) h3 = power x y h * power x z h2 := by
  sorry

theorem power_multiply (x : Peano) (y z : OrdinalNatural.Peano)
    (h : Peano.ValidPowerCondition x (positive y) = true)
    (h2 : Peano.ValidPowerCondition (power x (positive y) h) (positive z) = true) :
    ∃ h3, power x (positive (y * z)) h3 = power (power x (positive y) h) (positive z) h2 := by
  sorry

theorem power_mul_base (x y : Peano) (z : OrdinalNatural.Peano)
    (h : Peano.ValidPowerCondition x (positive z) = true)
    (h2 : Peano.ValidPowerCondition y (positive z) = true) :
    ∃ h3, power (x * y) (positive z) h3 = power x (positive z) h * power y (positive z) h2 := by
  sorry

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
  sorry

theorem power_mul_base_neg_one_one (z : OrdinalNatural.Peano)
    (h : Peano.ValidPowerCondition (positive OrdinalNatural.Peano.one) (negative z) = true)
    (h2 : Peano.ValidPowerCondition (positive OrdinalNatural.Peano.one) (negative z) = true) :
    ∃ h3, power (positive OrdinalNatural.Peano.one * positive OrdinalNatural.Peano.one) (negative z) h3 =
      power (positive OrdinalNatural.Peano.one) (negative z) h *
      power (positive OrdinalNatural.Peano.one) (negative z) h2 := by
  sorry

theorem power_mul_base_all (x y z : Peano)
    (h : Peano.ValidPowerCondition x z = true)
    (h2 : Peano.ValidPowerCondition y z = true) :
    ∃ h3, power (x * y) z h3 = power x z h * power y z h2 := by
  sorry

def isPower (e x : Peano) : Prop := ∃ y h, power y e h = x

def principalRoot_rec (e a : Peano) (x : OrdinalNatural.Peano) (h : e ≠ zero) (h2 : isPower e a)
  (h3 : ∀ b hbp hbn, x < b → power (positive b) e hbp ≠ a ∧ power (negative b) e hbn ≠ a) : Peano :=
  if h4 : power (positive x) e sorry = a then
    (positive x)
  else if h5 : power (negative x) e sorry = a then
    (negative x)
  else
    match x with
    | .one => False.elim sorry
    | .successor x' => principalRoot_rec e a x' h h2 sorry

def principalRoot (e a : Peano) (h : e ≠ zero ∧ isPower e a) : Peano :=
  match a with
  | positive a' => principalRoot_rec e (positive a') a' h.1 h.2 sorry
  | negative a' => principalRoot_rec e (negative a') a' h.1 h.2 sorry
  | zero => zero

theorem power_pos_zero_eq (e : OrdinalNatural.Peano) :
    power_pos zero e = zero := by
  induction e with
  | one => rfl
  | successor e ih =>
    show power_pos zero e * zero = zero
    rw [ih]
    exact mul_zero zero

theorem power_pos_positive_eq (y_n e_n : OrdinalNatural.Peano) :
    power_pos (positive y_n) e_n = positive (y_n ^ e_n) := by
  induction e_n with
  | one => rfl
  | successor e_n ih =>
    show power_pos (positive y_n) e_n * positive y_n = positive (y_n ^ e_n.successor)
    rw [ih, multiply_positive_positive, OrdinalNatural.Peano.power_succ]

theorem validPowerCondition_pos (a : Peano) (e : OrdinalNatural.Peano) :
    ValidPowerCondition a (positive e) = true := by
  cases a <;> rfl

theorem principalRoot_isPower (e x : OrdinalNatural.Peano)
    (h : positive e ≠ zero ∧ isPower (positive e) (positive x)) :
    ∃ h2, power (principalRoot (positive e) (positive x) h) (positive e) h2 =
          positive x := by
  sorry

theorem not_validPowerCondition_zero_negative (en : OrdinalNatural.Peano) :
    ¬ ValidPowerCondition zero (negative en) = true :=
  Bool.false_ne_true

theorem principalRoot_isPower_general (e x : Peano) (h : e ≠ zero ∧ isPower e x) :
    ∃ h2, power (principalRoot e x h) e h2 = x := by
  sorry

theorem principalRoot_power_eq (x e : Peano) (hx : zero ≤ x) (he : e ≠ zero)
    (h : ValidPowerCondition x e = true) :
    ∃ h2, principalRoot e (power x e h) h2 = x := by
  sorry

def isEven (a : Peano) : Prop := isDivisible a two

def isOdd (a : Peano) : Prop := ¬ isEven a

theorem isEven_zero : isEven zero := by
  refine ⟨?_, zero, ?_⟩
  · intro h; cases h
  · exact mul_zero two

theorem isOdd_ne_zero {e : Peano} (he : isOdd e) : e ≠ zero := by
  intro hez
  subst hez
  exact he isEven_zero

theorem ordinal_toNat_multiply (a b : OrdinalNatural.Peano) :
    (a * b).toNat = a.toNat * b.toNat := by
  have h := toInt_multiply (positive a) (positive b)
  rw [multiply_positive_positive] at h
  simp only [Peano.toInt] at h
  exact_mod_cast h

theorem ordinal_toNat_power (a b : OrdinalNatural.Peano) :
    (a ^ b).toNat = a.toNat ^ b.toNat := by
  have h := toInt_power_pos (positive a) b
  rw [power_pos_positive_eq] at h
  simp only [Peano.toInt] at h
  exact_mod_cast h

theorem isEven_positive_iff_natMod (e_n : OrdinalNatural.Peano) :
    isEven (positive e_n) ↔ e_n.toNat % 2 = 0 := by
  constructor
  · intro hev
    obtain ⟨_, c, hc⟩ := hev
    cases c with
    | zero =>
      rw [mul_zero] at hc
      cases hc
    | positive cn =>
      have h_eq : positive OrdinalNatural.Peano.two * positive cn = positive e_n := hc
      rw [multiply_positive_positive] at h_eq
      have h_inj : OrdinalNatural.Peano.two * cn = e_n := by injection h_eq
      have h_toNat := congrArg OrdinalNatural.Peano.toNat h_inj
      rw [ordinal_toNat_multiply] at h_toNat
      have htwo : OrdinalNatural.Peano.two.toNat = 2 := rfl
      rw [htwo] at h_toNat
      have h_cn_ne_zero := OrdinalNatural.Peano.toNat_ne_zero cn
      omega
    | negative cn =>
      exfalso
      have h_neg : negative cn = -(positive cn) := rfl
      rw [h_neg, mul_neg] at hc
      have h_compute : two * positive cn = positive (OrdinalNatural.Peano.two * cn) :=
        multiply_positive_positive _ _
      rw [h_compute] at hc
      exact absurd hc (fun heq => by cases heq)
  · intro h
    have h_ne_zero : e_n.toNat ≠ 0 := OrdinalNatural.Peano.toNat_ne_zero e_n
    obtain ⟨k, hk_eq, hk_ne_zero⟩ : ∃ k, e_n.toNat = 2 * k ∧ k ≠ 0 := by
      refine ⟨e_n.toNat / 2, ?_, ?_⟩ <;> omega
    have hcn_toNat : (OrdinalNatural.Peano.fromNat k hk_ne_zero).toNat = k :=
      OrdinalNatural.Peano.toNat_fromNat k hk_ne_zero
    refine ⟨?_, positive (OrdinalNatural.Peano.fromNat k hk_ne_zero), ?_⟩
    · intro hz; cases hz
    · show positive OrdinalNatural.Peano.two * positive (OrdinalNatural.Peano.fromNat k hk_ne_zero) = positive e_n
      rw [multiply_positive_positive]
      apply congrArg positive
      apply ordinal_toNat_injective
      rw [ordinal_toNat_multiply]
      have htwo : OrdinalNatural.Peano.two.toNat = 2 := rfl
      rw [htwo, hcn_toNat]
      omega

theorem isEven_negative_iff_natMod (e_n : OrdinalNatural.Peano) :
    isEven (negative e_n) ↔ e_n.toNat % 2 = 0 := by
  constructor
  · intro hev
    obtain ⟨_, c, hc⟩ := hev
    cases c with
    | zero =>
      rw [mul_zero] at hc
      cases hc
    | positive cn =>
      exfalso
      have h_compute : two * positive cn = positive (OrdinalNatural.Peano.two * cn) :=
        multiply_positive_positive _ _
      rw [h_compute] at hc
      exact absurd hc (fun heq => by cases heq)
    | negative cn =>
      have h_neg : negative cn = -(positive cn) := rfl
      rw [h_neg, mul_neg] at hc
      have h_compute : two * positive cn = positive (OrdinalNatural.Peano.two * cn) :=
        multiply_positive_positive _ _
      rw [h_compute] at hc
      have h_neg_eq : -(positive (OrdinalNatural.Peano.two * cn)) =
          negative (OrdinalNatural.Peano.two * cn) := rfl
      rw [h_neg_eq] at hc
      have h_inj : OrdinalNatural.Peano.two * cn = e_n := by injection hc
      have h_toNat := congrArg OrdinalNatural.Peano.toNat h_inj
      rw [ordinal_toNat_multiply] at h_toNat
      have htwo : OrdinalNatural.Peano.two.toNat = 2 := rfl
      rw [htwo] at h_toNat
      have h_cn_ne_zero := OrdinalNatural.Peano.toNat_ne_zero cn
      omega
  · intro h
    have h_ne_zero : e_n.toNat ≠ 0 := OrdinalNatural.Peano.toNat_ne_zero e_n
    obtain ⟨k, hk_eq, hk_ne_zero⟩ : ∃ k, e_n.toNat = 2 * k ∧ k ≠ 0 := by
      refine ⟨e_n.toNat / 2, ?_, ?_⟩ <;> omega
    have hcn_toNat : (OrdinalNatural.Peano.fromNat k hk_ne_zero).toNat = k :=
      OrdinalNatural.Peano.toNat_fromNat k hk_ne_zero
    refine ⟨?_, negative (OrdinalNatural.Peano.fromNat k hk_ne_zero), ?_⟩
    · intro hz; cases hz
    · have h_neg : negative (OrdinalNatural.Peano.fromNat k hk_ne_zero) =
          -(positive (OrdinalNatural.Peano.fromNat k hk_ne_zero)) := rfl
      rw [h_neg, mul_neg]
      show -(positive OrdinalNatural.Peano.two * positive (OrdinalNatural.Peano.fromNat k hk_ne_zero)) = negative e_n
      rw [multiply_positive_positive]
      have h_neg_eq : -(positive (OrdinalNatural.Peano.two * OrdinalNatural.Peano.fromNat k hk_ne_zero)) =
          negative (OrdinalNatural.Peano.two * OrdinalNatural.Peano.fromNat k hk_ne_zero) := rfl
      rw [h_neg_eq]
      apply congrArg negative
      apply ordinal_toNat_injective
      rw [ordinal_toNat_multiply]
      have htwo : OrdinalNatural.Peano.two.toNat = 2 := rfl
      rw [htwo, hcn_toNat]
      omega

theorem isEven_successor (x : Peano) (h : isEven x) : isOdd (successor x) := by
  intro h_succ
  cases x with
  | zero =>
    have h_succ_is_one : successor zero = positive ZeroMath.Numbers.OrdinalNatural.Peano.one := rfl
    rw [h_succ_is_one] at h_succ
    rw [isEven_positive_iff_natMod] at h_succ
    revert h_succ
    decide
  | positive p =>
    rw [isEven_positive_iff_natMod] at h
    have h_succ_pos : successor (positive p) = positive p.successor := rfl
    rw [h_succ_pos] at h_succ
    rw [isEven_positive_iff_natMod] at h_succ
    have h1 : p.successor.toNat = p.toNat + 1 := rfl
    rw [h1] at h_succ
    omega
  | negative n =>
    rw [isEven_negative_iff_natMod] at h
    cases n with
    | one =>
      have h_succ_neg : successor (negative ZeroMath.Numbers.OrdinalNatural.Peano.one) = zero := rfl
      rw [h_succ_neg] at h_succ
      revert h
      decide
    | successor n' =>
      have h_succ_neg : successor (negative n'.successor) = negative n' := rfl
      rw [h_succ_neg] at h_succ
      rw [isEven_negative_iff_natMod] at h_succ
      have h1 : n'.successor.toNat = n'.toNat + 1 := rfl
      rw [h1] at h
      omega

theorem isOdd_successor (x : Peano) (h : isOdd x) : isEven (successor x) := by
  cases x with
  | zero =>
    have h_even_zero : isEven zero := isEven_zero
    contradiction
  | positive p =>
    have h_not_even : ¬ isEven (positive p) := h
    rw [isEven_positive_iff_natMod] at h_not_even
    have h_succ_pos : successor (positive p) = positive p.successor := rfl
    rw [h_succ_pos]
    rw [isEven_positive_iff_natMod]
    have h1 : p.successor.toNat = p.toNat + 1 := rfl
    rw [h1]
    omega
  | negative n =>
    have h_not_even : ¬ isEven (negative n) := h
    rw [isEven_negative_iff_natMod] at h_not_even
    cases n with
    | one =>
      have h_succ_neg : successor (negative ZeroMath.Numbers.OrdinalNatural.Peano.one) = zero := rfl
      rw [h_succ_neg]
      exact isEven_zero
    | successor n' =>
      have h_succ_neg : successor (negative n'.successor) = negative n' := rfl
      rw [h_succ_neg]
      rw [isEven_negative_iff_natMod]
      have h1 : n'.successor.toNat = n'.toNat + 1 := rfl
      rw [h1] at h_not_even
      omega

theorem isEven_predecessor (x : Peano) (h : isEven x) : isOdd (predecessor x) := by
  intro h_pred
  cases x with
  | zero =>
    have h_pred_is_neg_one : predecessor zero = negative ZeroMath.Numbers.OrdinalNatural.Peano.one := rfl
    rw [h_pred_is_neg_one] at h_pred
    rw [isEven_negative_iff_natMod] at h_pred
    revert h_pred
    decide
  | positive p =>
    rw [isEven_positive_iff_natMod] at h
    cases p with
    | one =>
      have h_pred_pos_one : predecessor (positive ZeroMath.Numbers.OrdinalNatural.Peano.one) = zero := rfl
      rw [h_pred_pos_one] at h_pred
      revert h
      decide
    | successor p' =>
      have h_pred_pos_succ : predecessor (positive p'.successor) = positive p' := rfl
      rw [h_pred_pos_succ] at h_pred
      rw [isEven_positive_iff_natMod] at h_pred
      have h1 : p'.successor.toNat = p'.toNat + 1 := rfl
      rw [h1] at h
      omega
  | negative n =>
    rw [isEven_negative_iff_natMod] at h
    have h_pred_neg : predecessor (negative n) = negative n.successor := rfl
    rw [h_pred_neg] at h_pred
    rw [isEven_negative_iff_natMod] at h_pred
    have h1 : n.successor.toNat = n.toNat + 1 := rfl
    rw [h1] at h_pred
    omega

theorem isOdd_predecessor (x : Peano) (h : isOdd x) : isEven (predecessor x) := by
  cases x with
  | zero =>
    have h_even_zero : isEven zero := isEven_zero
    contradiction
  | positive p =>
    have h_not_even : ¬ isEven (positive p) := h
    rw [isEven_positive_iff_natMod] at h_not_even
    cases p with
    | one =>
      have h_pred_pos_one : predecessor (positive ZeroMath.Numbers.OrdinalNatural.Peano.one) = zero := rfl
      rw [h_pred_pos_one]
      exact isEven_zero
    | successor p' =>
      have h_pred_pos_succ : predecessor (positive p'.successor) = positive p' := rfl
      rw [h_pred_pos_succ]
      rw [isEven_positive_iff_natMod]
      have h1 : p'.successor.toNat = p'.toNat + 1 := rfl
      rw [h1] at h_not_even
      omega
  | negative n =>
    have h_not_even : ¬ isEven (negative n) := h
    rw [isEven_negative_iff_natMod] at h_not_even
    have h_pred_neg : predecessor (negative n) = negative n.successor := rfl
    rw [h_pred_neg]
    rw [isEven_negative_iff_natMod]
    have h1 : n.successor.toNat = n.toNat + 1 := rfl
    rw [h1]
    omega

theorem power_pos_negative_parity (y_n e_n : OrdinalNatural.Peano) :
    (e_n.toNat % 2 = 0 ∧ power_pos (negative y_n) e_n = positive (y_n ^ e_n)) ∨
    (e_n.toNat % 2 = 1 ∧ power_pos (negative y_n) e_n = negative (y_n ^ e_n)) := by
  induction e_n with
  | one =>
    right
    refine ⟨rfl, rfl⟩
  | successor e_n' ih =>
    have h_succ : e_n'.successor.toNat = e_n'.toNat + 1 := rfl
    cases ih with
    | inl h =>
      right
      refine ⟨?_, ?_⟩
      · rw [h_succ]; omega
      · show power_pos (negative y_n) e_n' * negative y_n = negative (y_n ^ e_n'.successor)
        rw [h.2, OrdinalNatural.Peano.power_succ]
        have h1 : negative y_n = -(positive y_n) := rfl
        rw [h1, mul_neg, multiply_positive_positive]
        rfl
    | inr h =>
      left
      refine ⟨?_, ?_⟩
      · rw [h_succ]; omega
      · show power_pos (negative y_n) e_n' * negative y_n = positive (y_n ^ e_n'.successor)
        rw [h.2, OrdinalNatural.Peano.power_succ]
        have h1 : negative (y_n ^ e_n') = -(positive (y_n ^ e_n')) := rfl
        have h2 : negative y_n = -(positive y_n) := rfl
        rw [h1, h2, neg_mul_neg, multiply_positive_positive]

theorem power_pos_negative_inj
    (a b en : OrdinalNatural.Peano)
    (h : power_pos (negative a) en = power_pos (negative b) en) :
    a = b := by
  have h_toInt := congrArg Peano.toInt h
  have h_natAbs := congrArg Int.natAbs h_toInt
  rw [power_pos_toInt_natAbs, power_pos_toInt_natAbs] at h_natAbs
  have h_a : (negative a).toInt.natAbs = a.toNat := by
    rw [absNat_toInt]; rfl
  have h_b : (negative b).toInt.natAbs = b.toNat := by
    rw [absNat_toInt]; rfl
  rw [h_a, h_b] at h_natAbs
  have h_lift : (a ^ en).toNat = (b ^ en).toNat := by
    rw [ordinal_toNat_power, ordinal_toNat_power]
    exact h_natAbs
  exact OrdinalNatural.Peano.power_cancel_left en a b (ordinal_toNat_injective h_lift)

theorem principalRoot_power_eq_of_odd (x e : Peano) (he : isOdd e)
    (h : ValidPowerCondition x e = true) :
    ∃ h2, principalRoot e (power x e h) h2 = x := by
  sorry

theorem principalRoot_power_eq_of_even (x e : Peano) (he : isEven e) (he_ne : e ≠ zero)
    (h : ValidPowerCondition x e = true) :
    ∃ h2, principalRoot e (power x e h) h2 = absoluteValue x := by
  sorry

end Peano

end ZeroMath.Numbers.Integer
