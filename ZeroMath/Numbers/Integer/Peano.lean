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


theorem not_validPowerCondition_zero_zero :
    ¬ ValidPowerCondition zero zero = true :=
  Bool.false_ne_true

theorem isDivisible_one_one : isDivisible one one := by
  refine ⟨?_, one, ?_⟩
  · intro h
    cases h
  · rw [one, mul_pos_one]

theorem minusOne_mul_minusOne : minusOne * minusOne = one := by
  rw [minusOne, mul_neg_one]
  rfl

theorem isDivisible_one_minusOne : isDivisible one minusOne := by
  refine ⟨?_, minusOne, ?_⟩
  · intro h
    cases h
  · exact minusOne_mul_minusOne

theorem power_pos_minusOne_eq_one_or_minusOne (e : OrdinalNatural.Peano) :
    power_pos minusOne e = one ∨ power_pos minusOne e = minusOne := by
  induction e with
  | one =>
      right
      rfl
  | successor e ih =>
      cases ih with
      | inl h =>
          right
          change power_pos minusOne e * minusOne = minusOne
          rw [h, minusOne, mul_neg_one]
          rfl
      | inr h =>
          left
          change power_pos minusOne e * minusOne = one
          rw [h]
          exact minusOne_mul_minusOne

theorem isDivisible_one_power_pos_minusOne (e : OrdinalNatural.Peano) :
    isDivisible one (power_pos minusOne e) := by
  cases power_pos_minusOne_eq_one_or_minusOne e with
  | inl h =>
      rw [h]
      exact isDivisible_one_one
  | inr h =>
      rw [h]
      exact isDivisible_one_minusOne

theorem isDivisible_one_power_pos_of_valid_negative (a : Peano) (e : OrdinalNatural.Peano)
    (h : ValidPowerCondition a (negative e) = true) :
    isDivisible one (power_pos a e) := by
  cases a with
  | zero =>
      contradiction
  | positive n =>
      cases n with
      | one =>
          change isDivisible one (power_pos one e)
          rw [power_pos_oneInt]
          exact isDivisible_one_one
      | successor n =>
          contradiction
  | negative n =>
      cases n with
      | one =>
          change isDivisible one (power_pos minusOne e)
          exact isDivisible_one_power_pos_minusOne e
      | successor n =>
          contradiction


@[simp]
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

theorem multiply_positive_negative (a b : OrdinalNatural.Peano) :
    positive a * negative b = negative (a * b) := by
  change positive a * -(positive b) = negative (a * b)
  rw [mul_neg, multiply_positive_positive]
  rfl

theorem multiply_negative_positive (a b : OrdinalNatural.Peano) :
    negative a * positive b = negative (a * b) := by
  rw [mul_comm, multiply_positive_negative]
  rw [OrdinalNatural.Peano.multiply_comm b a]

theorem multiply_negative_negative (a b : OrdinalNatural.Peano) :
    negative a * negative b = positive (a * b) := by
  change -(positive a) * -(positive b) = positive (a * b)
  rw [neg_mul_neg, multiply_positive_positive]

theorem isDivisible_positive_positive {a b : OrdinalNatural.Peano}
    (h : isDivisible (positive a) (positive b)) :
    OrdinalNatural.Peano.isDivisible a b := by
  rcases h with ⟨_, c, hc⟩
  cases c with
  | zero =>
      rw [mul_zero] at hc
      cases hc
  | positive c =>
      rw [multiply_positive_positive] at hc
      cases hc
      exact ⟨c, rfl⟩
  | negative c =>
      rw [multiply_positive_negative] at hc
      cases hc

theorem isDivisible_positive_negative {a b : OrdinalNatural.Peano}
    (h : isDivisible (positive a) (negative b)) :
    OrdinalNatural.Peano.isDivisible a b := by
  rcases h with ⟨_, c, hc⟩
  cases c with
  | zero =>
      rw [mul_zero] at hc
      cases hc
  | positive c =>
      rw [multiply_negative_positive] at hc
      cases hc
  | negative c =>
      rw [multiply_negative_negative] at hc
      cases hc
      exact ⟨c, rfl⟩

theorem isDivisible_negative_positive {a b : OrdinalNatural.Peano}
    (h : isDivisible (negative a) (positive b)) :
    OrdinalNatural.Peano.isDivisible a b := by
  rcases h with ⟨_, c, hc⟩
  cases c with
  | zero =>
      rw [mul_zero] at hc
      cases hc
  | positive c =>
      rw [multiply_positive_positive] at hc
      cases hc
  | negative c =>
      rw [multiply_positive_negative] at hc
      cases hc
      exact ⟨c, rfl⟩

theorem isDivisible_negative_negative {a b : OrdinalNatural.Peano}
    (h : isDivisible (negative a) (negative b)) :
    OrdinalNatural.Peano.isDivisible a b := by
  rcases h with ⟨_, c, hc⟩
  cases c with
  | zero =>
      rw [mul_zero] at hc
      cases hc
  | positive c =>
      rw [multiply_negative_positive] at hc
      cases hc
      exact ⟨c, rfl⟩
  | negative c =>
      rw [multiply_negative_negative] at hc
      cases hc

theorem ordinal_divide_initial_bound (a b : OrdinalNatural.Peano) :
    ∀ y, a < y → b * y ≠ a := by
  intro y hy heq
  have hle : y ≤ b * y := OrdinalNatural.Peano.le_multiply_right y b
  have hlt : a < b * y := OrdinalNatural.Peano.lt_of_lt_le hy hle
  rw [heq] at hlt
  exact OrdinalNatural.Peano.not_lt_self a hlt

def divide (a b : Peano) (h : isDivisible a b) : Peano :=
  match a, b with
  | _, zero => False.elim (h.left rfl)
  | zero, _ => zero
  | positive a', positive b' => positive (OrdinalNatural.Peano.divide_rec a' b' a'
      (ordinal_divide_initial_bound a' b') (isDivisible_positive_positive h))
  | positive a', negative b' => negative (OrdinalNatural.Peano.divide_rec a' b' a'
      (ordinal_divide_initial_bound a' b') (isDivisible_positive_negative h))
  | negative a', positive b' => negative (OrdinalNatural.Peano.divide_rec a' b' a'
      (ordinal_divide_initial_bound a' b') (isDivisible_negative_positive h))
  | negative a', negative b' => positive (OrdinalNatural.Peano.divide_rec a' b' a'
      (ordinal_divide_initial_bound a' b') (isDivisible_negative_negative h))

def power : (a b : Peano) → (h : ValidPowerCondition a b = true) → Peano
  | zero, positive _, _ => zero
  | zero, zero, h => False.elim (not_validPowerCondition_zero_zero h)
  | _, zero, _ => one
  | a, positive n, _ => power_pos a n
  | a, negative n, h => divide one (power_pos a n) (isDivisible_one_power_pos_of_valid_negative a n h)


theorem divide_correct (a b : Peano) (h : isDivisible a b) :
    b * divide a b h = a := by
  cases b with
  | zero =>
      exact False.elim (h.left rfl)
  | positive b' =>
      cases a with
      | zero =>
          change positive b' * zero = zero
          rw [mul_zero]
      | positive a' =>
          change positive b' * positive (OrdinalNatural.Peano.divide_rec a' b' a'
            (ordinal_divide_initial_bound a' b') (isDivisible_positive_positive h)) = positive a'
          rw [multiply_positive_positive]
          exact congrArg positive (OrdinalNatural.Peano.divide_rec_correct a' b' a'
            (ordinal_divide_initial_bound a' b') (isDivisible_positive_positive h))
      | negative a' =>
          change positive b' * negative (OrdinalNatural.Peano.divide_rec a' b' a'
            (ordinal_divide_initial_bound a' b') (isDivisible_negative_positive h)) = negative a'
          rw [multiply_positive_negative]
          exact congrArg negative (OrdinalNatural.Peano.divide_rec_correct a' b' a'
            (ordinal_divide_initial_bound a' b') (isDivisible_negative_positive h))
  | negative b' =>
      cases a with
      | zero =>
          change negative b' * zero = zero
          rw [mul_zero]
      | positive a' =>
          change negative b' * negative (OrdinalNatural.Peano.divide_rec a' b' a'
            (ordinal_divide_initial_bound a' b') (isDivisible_positive_negative h)) = positive a'
          rw [multiply_negative_negative]
          exact congrArg positive (OrdinalNatural.Peano.divide_rec_correct a' b' a'
            (ordinal_divide_initial_bound a' b') (isDivisible_positive_negative h))
      | negative a' =>
          change negative b' * positive (OrdinalNatural.Peano.divide_rec a' b' a'
            (ordinal_divide_initial_bound a' b') (isDivisible_negative_negative h)) = negative a'
          rw [multiply_negative_positive]
          exact congrArg negative (OrdinalNatural.Peano.divide_rec_correct a' b' a'
            (ordinal_divide_initial_bound a' b') (isDivisible_negative_negative h))

theorem multiply_divide_cancel (x y : Peano) (h : isDivisible x y) :
    (divide x y h) * y = x := by
  rw [mul_comm]
  exact divide_correct x y h

@[simp]
theorem one_mul (a : Peano) : one * a = a := by
  rw [mul_comm, one, mul_pos_one]

theorem power_proof_irrel (x y : Peano)
    (h h' : ValidPowerCondition x y = true) : power x y h = power x y h' := by
  cases x <;> cases y <;> rfl

theorem power_zero (x : Peano) (h : ValidPowerCondition x zero = true) : power x zero h = one := by
  cases x with
  | zero => contradiction
  | positive n => rfl
  | negative n => rfl


theorem divide_one_one_eq (h : isDivisible one one) : divide one one h = one := by
  apply mul_left_cancel one
  · intro hz
    cases hz
  calc
    one * divide one one h = one := divide_correct one one h
    _ = one * one := by rw [one, mul_pos_one]

theorem divide_one_power_pos_one_eq (e : OrdinalNatural.Peano)
    (h : isDivisible one (power_pos one e)) : divide one (power_pos one e) h = one := by
  apply mul_left_cancel (power_pos one e)
  · exact h.left
  calc
    power_pos one e * divide one (power_pos one e) h = one := divide_correct one (power_pos one e) h
    _ = power_pos one e * one := by rw [power_pos_oneInt, one, mul_pos_one]

theorem power_oneInt (e : Peano) (h : ValidPowerCondition one e = true) : power one e h = one := by
  cases e with
  | zero => rfl
  | positive n =>
      change power_pos one n = one
      exact power_pos_oneInt n
  | negative n =>
      change divide one (power_pos one n) (isDivisible_one_power_pos_of_valid_negative one n h) = one
      exact divide_one_power_pos_one_eq n _

theorem power_pos_minusOne_square (e : OrdinalNatural.Peano) : power_pos minusOne e * power_pos minusOne e = one := by
  cases power_pos_minusOne_eq_one_or_minusOne e with
  | inl h => rw [h, one, mul_pos_one]
  | inr h => rw [h, minusOne_mul_minusOne]

theorem divide_one_power_pos_minusOne_eq (e : OrdinalNatural.Peano)
    (h : isDivisible one (power_pos minusOne e)) : divide one (power_pos minusOne e) h = power_pos minusOne e := by
  apply mul_left_cancel (power_pos minusOne e)
  · exact h.left
  calc
    power_pos minusOne e * divide one (power_pos minusOne e) h = one := divide_correct one (power_pos minusOne e) h
    _ = power_pos minusOne e * power_pos minusOne e := (power_pos_minusOne_square e).symm

theorem power_minusOne_negative (e : OrdinalNatural.Peano)
    (h : ValidPowerCondition minusOne (negative e) = true) :
    power minusOne (negative e) h = power_pos minusOne e := by
  change divide one (power_pos minusOne e) (isDivisible_one_power_pos_of_valid_negative minusOne e h) = power_pos minusOne e
  exact divide_one_power_pos_minusOne_eq e _

theorem power_pos_minusOne_successor_mul (e : OrdinalNatural.Peano) :
    power_pos minusOne e.successor * minusOne = power_pos minusOne e := by
  change (power_pos minusOne e * minusOne) * minusOne = power_pos minusOne e
  rw [mul_assoc, minusOne_mul_minusOne, one, mul_pos_one]

theorem power_minusOne_succ (e : Peano)
    (h : ValidPowerCondition minusOne e = true)
    (hs : ValidPowerCondition minusOne (successor e) = true) :
    power minusOne (successor e) hs = power minusOne e h * minusOne := by
  cases e with
  | zero =>
      change minusOne = one * minusOne
      rw [one_mul]
  | positive n =>
      change power_pos minusOne n.successor = power_pos minusOne n * minusOne
      rfl
  | negative n =>
      cases n with
      | one =>
          rw [power_minusOne_negative]
          change one = minusOne * minusOne
          exact minusOne_mul_minusOne.symm
      | successor n =>
          simp [successor]
          rw [power_minusOne_negative n, power_minusOne_negative n.successor h]
          exact (power_pos_minusOne_successor_mul n).symm

theorem power_minusOne_pred (e : Peano)
    (h : ValidPowerCondition minusOne e = true)
    (hp : ValidPowerCondition minusOne (predecessor e) = true) :
    power minusOne (predecessor e) hp = power minusOne e h * minusOne := by
  cases e with
  | zero =>
      change power minusOne (negative OrdinalNatural.Peano.one) hp = one * minusOne
      rw [power_minusOne_negative, one_mul]
      rfl
  | positive n =>
      cases n with
      | one =>
          change one = minusOne * minusOne
          exact minusOne_mul_minusOne.symm
      | successor n =>
          change power_pos minusOne n = power_pos minusOne n.successor * minusOne
          exact (power_pos_minusOne_successor_mul n).symm
  | negative n =>
      simp [predecessor]
      rw [power_minusOne_negative n.successor, power_minusOne_negative n h]
      rfl

theorem power_add_minusOne (y z : Peano)
    (h : ValidPowerCondition minusOne y = true) (h2 : ValidPowerCondition minusOne z = true) :
    ∃ h3, power minusOne (y + z) h3 = power minusOne y h * power minusOne z h2 := by
  cases z with
  | zero =>
      have h3 : ValidPowerCondition minusOne (y + zero) = true := by simpa [add_zero] using h
      refine ⟨h3, ?_⟩
      calc
        power minusOne (y + zero) h3 = power minusOne y h := by simp [add_zero]
        _ = power minusOne y h * one := by rw [one, mul_pos_one]
        _ = power minusOne y h * power minusOne zero h2 := by rfl
  | positive n =>
      induction n with
      | one =>
          have h3 : ValidPowerCondition minusOne (y + positive OrdinalNatural.Peano.one) = true := by rw [add_pos_one]; exact validPowerCondition_negOneInt _
          refine ⟨h3, ?_⟩
          revert h3
          rw [add_pos_one]
          intro h3
          calc
            power minusOne (successor y) h3 = power minusOne y h * minusOne := power_minusOne_succ y h h3
            _ = power minusOne y h * power minusOne (positive OrdinalNatural.Peano.one) h2 := by rfl
      | successor n ih =>
          have hprev : ValidPowerCondition minusOne (positive n) = true := validPowerCondition_negOneInt _
          rcases ih hprev with ⟨hmid, hmid_eq⟩
          have h3 : ValidPowerCondition minusOne (y + positive n.successor) = true := by rw [add_pos_succ]; exact validPowerCondition_negOneInt _
          refine ⟨h3, ?_⟩
          revert h3
          rw [add_pos_succ]
          intro h3
          calc
            power minusOne (successor (y + positive n)) h3 = power minusOne (y + positive n) hmid * minusOne := power_minusOne_succ (y + positive n) hmid h3
            _ = (power minusOne y h * power minusOne (positive n) hprev) * minusOne := by rw [hmid_eq]
            _ = power minusOne y h * (power minusOne (positive n) hprev * minusOne) := by rw [mul_assoc]
            _ = power minusOne y h * power minusOne (positive n.successor) h2 := by rfl
  | negative n =>
      induction n with
      | one =>
          have h3 : ValidPowerCondition minusOne (y + negative OrdinalNatural.Peano.one) = true := by rw [add_neg_one]; exact validPowerCondition_negOneInt _
          refine ⟨h3, ?_⟩
          revert h3
          rw [add_neg_one]
          intro h3
          calc
            power minusOne (predecessor y) h3 = power minusOne y h * minusOne := power_minusOne_pred y h h3
            _ = power minusOne y h * power minusOne (negative OrdinalNatural.Peano.one) h2 := by
              rw [power_minusOne_negative]
              rfl
      | successor n ih =>
          have hprev : ValidPowerCondition minusOne (negative n) = true := validPowerCondition_negOneInt _
          rcases ih hprev with ⟨hmid, hmid_eq⟩
          have h3 : ValidPowerCondition minusOne (y + negative n.successor) = true := by rw [add_neg_succ]; exact validPowerCondition_negOneInt _
          refine ⟨h3, ?_⟩
          revert h3
          rw [add_neg_succ]
          intro h3
          calc
            power minusOne (predecessor (y + negative n)) h3 = power minusOne (y + negative n) hmid * minusOne := power_minusOne_pred (y + negative n) hmid h3
            _ = (power minusOne y h * power minusOne (negative n) hprev) * minusOne := by rw [hmid_eq]
            _ = power minusOne y h * (power minusOne (negative n) hprev * minusOne) := by rw [mul_assoc]
            _ = power minusOne y h * power minusOne (negative n.successor) h2 := by
              rw [power_minusOne_negative, power_minusOne_negative]
              rfl

theorem power_positive_eq_power_pos (a : Peano) (n : OrdinalNatural.Peano)
    (h : ValidPowerCondition a (positive n) = true) :
    power a (positive n) h = power_pos a n := by
  cases a with
  | zero =>
      induction n with
      | one => rfl
      | successor n ih =>
          change zero = power_pos zero n * zero
          rw [mul_zero]
  | positive n => rfl
  | negative n => rfl

theorem power_eq_of_base_eq {a b e : Peano} (hab : a = b)
    (ha : ValidPowerCondition a e = true) (hb : ValidPowerCondition b e = true) :
    power a e ha = power b e hb := by
  subst hab
  exact power_proof_irrel a e ha hb

theorem power_mul_base_all (x y z : Peano)
    (h : Peano.ValidPowerCondition x z = true)
    (h2 : Peano.ValidPowerCondition y z = true) :
    ∃ h3, power (x * y) z h3 = power x z h * power y z h2 := by
  cases z with
  | positive zn =>
      refine ⟨rfl, ?_⟩
      rw [power_positive_eq_power_pos (x * y) zn rfl,
        power_positive_eq_power_pos x zn h,
        power_positive_eq_power_pos y zn h2]
      exact power_pos_mul_base x y zn
  | zero =>
      cases x with
      | zero => contradiction
      | positive xn =>
          cases y with
          | zero => contradiction
          | positive yn =>
              have hxy : positive xn * positive yn = positive (xn * yn) := multiply_positive_positive xn yn
              have h3 : ValidPowerCondition (positive xn * positive yn) zero = true := by
                rw [hxy]
                rfl
              refine ⟨h3, ?_⟩
              rw [power_zero, power_zero, power_zero, one, mul_pos_one]
          | negative yn =>
              have hxy : positive xn * negative yn = negative (xn * yn) := multiply_positive_negative xn yn
              have h3 : ValidPowerCondition (positive xn * negative yn) zero = true := by
                rw [hxy]
                rfl
              refine ⟨h3, ?_⟩
              rw [power_zero, power_zero, power_zero, one, mul_pos_one]
      | negative xn =>
          cases y with
          | zero => contradiction
          | positive yn =>
              have hxy : negative xn * positive yn = negative (xn * yn) := multiply_negative_positive xn yn
              have h3 : ValidPowerCondition (negative xn * positive yn) zero = true := by
                rw [hxy]
                rfl
              refine ⟨h3, ?_⟩
              rw [power_zero, power_zero, power_zero, one, mul_pos_one]
          | negative yn =>
              have hxy : negative xn * negative yn = positive (xn * yn) := multiply_negative_negative xn yn
              have h3 : ValidPowerCondition (negative xn * negative yn) zero = true := by
                rw [hxy]
                rfl
              refine ⟨h3, ?_⟩
              rw [power_zero, power_zero, power_zero, one, mul_pos_one]
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
                      have h3 : ValidPowerCondition (positive OrdinalNatural.Peano.one * positive OrdinalNatural.Peano.one) (negative zn) = true := by
                        rw [multiply_positive_positive]
                        rfl
                      refine ⟨h3, ?_⟩
                      change power (positive OrdinalNatural.Peano.one * positive OrdinalNatural.Peano.one) (negative zn) h3 =
                        power (positive OrdinalNatural.Peano.one) (negative zn) h * power (positive OrdinalNatural.Peano.one) (negative zn) h2
                      calc
                        power (positive OrdinalNatural.Peano.one * positive OrdinalNatural.Peano.one) (negative zn) h3
                            = power one (negative zn) (validPowerCondition_oneInt _) :=
                              power_eq_of_base_eq (multiply_positive_positive _ _) h3 (validPowerCondition_oneInt _)
                        _ = power one (negative zn) h * power one (negative zn) h2 := by
                              rw [power_oneInt, one_mul]
                  | successor yn => contradiction
              | negative yn =>
                  cases yn with
                  | one =>
                      have h3 : ValidPowerCondition (positive OrdinalNatural.Peano.one * negative OrdinalNatural.Peano.one) (negative zn) = true := by
                        rw [multiply_positive_negative]
                        rfl
                      refine ⟨h3, ?_⟩
                      change power (positive OrdinalNatural.Peano.one * negative OrdinalNatural.Peano.one) (negative zn) h3 =
                        power (positive OrdinalNatural.Peano.one) (negative zn) h * power (negative OrdinalNatural.Peano.one) (negative zn) h2
                      calc
                        power (positive OrdinalNatural.Peano.one * negative OrdinalNatural.Peano.one) (negative zn) h3
                            = power minusOne (negative zn) (validPowerCondition_negOneInt _) :=
                              power_eq_of_base_eq (multiply_positive_negative _ _) h3 (validPowerCondition_negOneInt _)
                        _ = power one (negative zn) h * power minusOne (negative zn) h2 := by
                              rw [power_oneInt, one_mul]
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
                      have h3 : ValidPowerCondition (negative OrdinalNatural.Peano.one * positive OrdinalNatural.Peano.one) (negative zn) = true := by
                        rw [multiply_negative_positive]
                        rfl
                      refine ⟨h3, ?_⟩
                      change power (negative OrdinalNatural.Peano.one * positive OrdinalNatural.Peano.one) (negative zn) h3 =
                        power (negative OrdinalNatural.Peano.one) (negative zn) h * power (positive OrdinalNatural.Peano.one) (negative zn) h2
                      calc
                        power (negative OrdinalNatural.Peano.one * positive OrdinalNatural.Peano.one) (negative zn) h3
                            = power minusOne (negative zn) (validPowerCondition_negOneInt _) :=
                              power_eq_of_base_eq (multiply_negative_positive _ _) h3 (validPowerCondition_negOneInt _)
                        _ = power minusOne (negative zn) h * power one (negative zn) h2 := by
                              rw [power_oneInt, one, mul_pos_one]
                  | successor yn => contradiction
              | negative yn =>
                  cases yn with
                  | one =>
                      have h3 : ValidPowerCondition (negative OrdinalNatural.Peano.one * negative OrdinalNatural.Peano.one) (negative zn) = true := by
                        rw [multiply_negative_negative]
                        rfl
                      refine ⟨h3, ?_⟩
                      change power (negative OrdinalNatural.Peano.one * negative OrdinalNatural.Peano.one) (negative zn) h3 =
                        power (negative OrdinalNatural.Peano.one) (negative zn) h * power (negative OrdinalNatural.Peano.one) (negative zn) h2
                      calc
                        power (negative OrdinalNatural.Peano.one * negative OrdinalNatural.Peano.one) (negative zn) h3
                            = power one (negative zn) (validPowerCondition_oneInt _) :=
                              power_eq_of_base_eq (multiply_negative_negative _ _) h3 (validPowerCondition_oneInt _)
                        _ = power minusOne (negative zn) h * power minusOne (negative zn) h2 := by
                              rw [power_oneInt, power_minusOne_negative, power_pos_minusOne_square]
                  | successor yn => contradiction
          | successor xn => contradiction

theorem power_add (x y z : Peano) (h : Peano.ValidPowerCondition x y = true) (h2 : Peano.ValidPowerCondition x z = true) :
  ∃ h3, power x (y + z) h3 = power x y h * power x z h2 := by
  cases y with
  | zero =>
      have h3 : ValidPowerCondition x (zero + z) = true := by simpa [zero_add] using h2
      refine ⟨h3, ?_⟩
      calc
        power x (zero + z) h3 = power x z h2 := by
          simp [zero_add]
        _ = one * power x z h2 := by
          rw [one_mul]
        _ = power x zero h * power x z h2 := by
          rw [power_zero x h]
  | positive yn =>
      cases z with
      | zero =>
          have h3 : ValidPowerCondition x (positive yn + zero) = true := by simpa [add_zero] using h
          refine ⟨h3, ?_⟩
          calc
            power x (positive yn + zero) h3 = power x (positive yn) h := by
              simp [add_zero]
            _ = power x (positive yn) h * one := by
              rw [one, mul_pos_one]
            _ = power x (positive yn) h * power x zero h2 := by
              rw [power_zero x h2]
      | positive zn =>
          have h3 : ValidPowerCondition x (positive yn + positive zn) = true := by
            rw [add_positive_positive]
            rfl
          refine ⟨h3, ?_⟩
          revert h3
          rw [add_positive_positive]
          intro h3
          cases x with
          | zero =>
              change zero = zero * zero
              rw [zero_mul]
          | positive xn =>
              change power_pos (positive xn) (yn + zn) = power_pos (positive xn) yn * power_pos (positive xn) zn
              exact power_pos_add (positive xn) yn zn
          | negative xn =>
              change power_pos (negative xn) (yn + zn) = power_pos (negative xn) yn * power_pos (negative xn) zn
              exact power_pos_add (negative xn) yn zn
      | negative zn =>
          cases x with
          | zero => contradiction
          | positive xn =>
              cases xn with
              | one =>
                  change ∃ h3, power one (positive yn + negative zn) h3 = power one (positive yn) h * power one (negative zn) h2
                  refine ⟨validPowerCondition_oneInt _, ?_⟩
                  rw [power_oneInt, power_oneInt, power_oneInt, one, mul_pos_one]
              | successor xn => contradiction
          | negative xn =>
              cases xn with
              | one =>
                  exact power_add_minusOne (positive yn) (negative zn) h h2
              | successor xn => contradiction
  | negative yn =>
      cases x with
      | zero => contradiction
      | positive xn =>
          cases xn with
          | one =>
              change ∃ h3, power one (negative yn + z) h3 = power one (negative yn) h * power one z h2
              refine ⟨validPowerCondition_oneInt _, ?_⟩
              rw [power_oneInt, power_oneInt, power_oneInt, one, mul_pos_one]
          | successor xn => contradiction
      | negative xn =>
          cases xn with
          | one =>
              exact power_add_minusOne (negative yn) z h h2
          | successor xn => contradiction


theorem division_reverses_multiplication (x y : Peano) (hy : y ≠ zero) :
    ∃ h, divide (y * x) y h = x := by
  let h : isDivisible (y * x) y := ⟨hy, x, rfl⟩
  refine ⟨h, ?_⟩
  exact mul_left_cancel y (divide (y * x) y h) x hy (divide_correct (y * x) y h)

theorem divide_add_h (x y z : Peano) (h : isDivisible x z) (h2 : isDivisible y z) :
    isDivisible (x + y) z := by
  exact ⟨h.left, divide x z h + divide y z h2, by
    calc
      z * (divide x z h + divide y z h2) = z * divide x z h + z * divide y z h2 := by
        rw [mul_add]
      _ = x + y := by rw [divide_correct x z h, divide_correct y z h2]⟩

theorem divide_add (x y z : Peano) (h : isDivisible x z) (h2 : isDivisible y z) :
    ∃ h3 : isDivisible (x + y) z, divide (x + y) z h3 = divide x z h + divide y z h2 := by
  let h3 : isDivisible (x + y) z := divide_add_h x y z h h2
  exists h3
  apply mul_left_cancel z
  · exact h.left
  calc
    z * divide (x + y) z h3 = x + y := divide_correct (x + y) z h3
    _ = z * (divide x z h + divide y z h2) := by
      rw [mul_add, divide_correct x z h, divide_correct y z h2]

theorem divide_sub_h (x y z : Peano) (h : isDivisible x z) (h2 : isDivisible y z) :
    isDivisible (x - y) z := by
  exact ⟨h.left, divide x z h - divide y z h2, by
    calc
      z * (divide x z h - divide y z h2) = z * divide x z h - z * divide y z h2 := by
        rw [mul_sub]
      _ = x - y := by rw [divide_correct x z h, divide_correct y z h2]⟩

theorem divide_sub (x y z : Peano) (h : isDivisible x z) (h2 : isDivisible y z) :
    ∃ h3 : isDivisible (x - y) z, divide (x - y) z h3 = divide x z h - divide y z h2 := by
  let h3 : isDivisible (x - y) z := divide_sub_h x y z h h2
  exists h3
  apply mul_left_cancel z
  · exact h.left
  calc
    z * divide (x - y) z h3 = x - y := divide_correct (x - y) z h3
    _ = z * (divide x z h - divide y z h2) := by
      rw [mul_sub, divide_correct x z h, divide_correct y z h2]

theorem divide_multiply_h (x y z : Peano) (h : isDivisible y z) :
    isDivisible (x * y) z := by
  exact ⟨h.left, x * divide y z h, by
    calc
      z * (x * divide y z h) = z * (divide y z h * x) := by
        rw [mul_comm x (divide y z h)]
      _ = z * divide y z h * x := by
        rw [← mul_assoc]
      _ = y * x := by
        rw [divide_correct y z h]
      _ = x * y := by
        rw [mul_comm]⟩

theorem divide_multiply (x y z : Peano) (h : isDivisible y z) :
    ∃ h2, divide (x * y) z h2 = x * divide y z h := by
  let h2 : isDivisible (x * y) z := divide_multiply_h x y z h
  exists h2
  apply mul_left_cancel z
  · exact h.left
  calc
    z * divide (x * y) z h2 = x * y := divide_correct (x * y) z h2
    _ = y * x := by
      rw [mul_comm]
    _ = z * divide y z h * x := by
      rw [divide_correct y z h]
    _ = z * (divide y z h * x) := by
      rw [← mul_assoc]
    _ = z * (x * divide y z h) := by
      rw [mul_comm (divide y z h) x]

theorem mul_ne_zero {x y : Peano} (hx : x ≠ zero) (hy : y ≠ zero) : x * y ≠ zero := by
  intro hxy
  cases (mul_eq_zero_iff x y).mp hxy with
  | inl hx_zero => exact hx hx_zero
  | inr hy_zero => exact hy hy_zero

theorem divide_divide (x y z : Peano) (h : isDivisible x y) (h2 : isDivisible (divide x y h) z) :
    ∃ h3, divide (divide x y h) z h2 = divide x (y * z) h3 := by
  let q := divide (divide x y h) z h2
  have hyz : y * z ≠ zero := mul_ne_zero h.left h2.left
  let h3 : isDivisible x (y * z) := ⟨hyz, q, by
    calc
      (y * z) * q = y * (z * q) := by
        rw [mul_assoc]
      _ = y * divide x y h := by
        rw [divide_correct (divide x y h) z h2]
      _ = x := divide_correct x y h⟩
  exists h3
  apply mul_left_cancel (y * z)
  · exact hyz
  calc
    (y * z) * divide (divide x y h) z h2 = y * (z * divide (divide x y h) z h2) := by
      rw [mul_assoc]
    _ = y * divide x y h := by
      rw [divide_correct (divide x y h) z h2]
    _ = x := divide_correct x y h
    _ = (y * z) * divide x (y * z) h3 := by
      rw [divide_correct x (y * z) h3]

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

theorem not_validPowerCondition_zero_negative (en : OrdinalNatural.Peano) :
    ¬ ValidPowerCondition zero (negative en) = true :=
  Bool.false_ne_true

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

def isPower (e x : Peano) : Prop := ∃ y h, power y e h = x

theorem principalRoot_rec_step_h {e a : Peano} {x : OrdinalNatural.Peano}
    (hnp : ∀ hp, power (positive x.successor) e hp ≠ a)
    (hnn : ∀ hn, power (negative x.successor) e hn ≠ a)
    (h3 : ∀ b hbp hbn, x.successor < b →
      power (positive b) e hbp ≠ a ∧ power (negative b) e hbn ≠ a) :
    ∀ b hbp hbn, x < b →
      power (positive b) e hbp ≠ a ∧ power (negative b) e hbn ≠ a := by
  intro b hbp hbn hb
  cases OrdinalNatural.Peano.lt_successor_cases hb with
  | inl h_eq =>
      subst h_eq
      exact ⟨hnp hbp, hnn hbn⟩
  | inr h_lt =>
      exact h3 b hbp hbn h_lt

theorem power_zero_base_of_valid_nonzero {e : Peano}
    (h : e ≠ zero) (hv : ValidPowerCondition zero e = true) : power zero e hv = zero := by
  cases e with
  | zero => exact False.elim (h rfl)
  | positive n => rfl
  | negative n => contradiction

theorem principalRoot_rec_one_absurd {e a : Peano}
    (h : e ≠ zero) (h2 : isPower e a) (hnz : a ≠ zero)
    (hnp : ∀ hp, power (positive OrdinalNatural.Peano.one) e hp ≠ a)
    (hnn : ∀ hn, power (negative OrdinalNatural.Peano.one) e hn ≠ a)
    (h3 : ∀ b hbp hbn, OrdinalNatural.Peano.one < b →
      power (positive b) e hbp ≠ a ∧ power (negative b) e hbn ≠ a) : False := by
  rcases h2 with ⟨y, hyv, hypow⟩
  cases y with
  | zero =>
      have hpow_zero : power zero e hyv = zero := power_zero_base_of_valid_nonzero h hyv
      rw [hpow_zero] at hypow
      exact hnz hypow.symm
  | positive b =>
      cases b with
      | one => exact hnp hyv hypow
      | successor b' =>
          cases e with
          | zero => exact False.elim (h rfl)
          | positive en =>
              have hbn : ValidPowerCondition (negative b'.successor) (positive en) = true := rfl
              exact (h3 b'.successor hyv hbn (OrdinalNatural.Peano.one_lt_succ b')).1 hypow
          | negative en => contradiction
  | negative b =>
      cases b with
      | one => exact hnn hyv hypow
      | successor b' =>
          cases e with
          | zero => exact False.elim (h rfl)
          | positive en =>
              have hbp : ValidPowerCondition (positive b'.successor) (positive en) = true := rfl
              exact (h3 b'.successor hbp hyv (OrdinalNatural.Peano.one_lt_succ b')).2 hypow
          | negative en => contradiction


theorem ordinal_lt_power_ne {a b e : OrdinalNatural.Peano} (h : a < b) : b ^ e ≠ a := by
  intro heq
  have hle : b ≤ b ^ e := OrdinalNatural.Peano.le_power b e
  have hlt : a < b ^ e := OrdinalNatural.Peano.lt_of_lt_le h hle
  rw [heq] at hlt
  exact OrdinalNatural.Peano.not_lt_self a hlt

theorem principalRoot_rec_initial_h_positive {e : Peano} (hne : e ≠ zero)
    (a : OrdinalNatural.Peano) :
    ∀ b hbp hbn, a < b →
      power (positive b) e hbp ≠ positive a ∧ power (negative b) e hbn ≠ positive a := by
  intro b hbp hbn hb
  constructor
  · cases e with
    | zero => exact False.elim (hne rfl)
    | positive en =>
        change power_pos (positive b) en ≠ positive a
        rw [power_pos_positive_eq]
        intro heq
        cases heq
        exact ordinal_lt_power_ne hb rfl
    | negative en =>
        cases b with
        | one => exact False.elim (OrdinalNatural.Peano.not_lt_one a hb)
        | successor b' => contradiction
  · cases e with
    | zero => exact False.elim (hne rfl)
    | positive en =>
        change power_pos (negative b) en ≠ positive a
        cases power_pos_negative_parity b en with
        | inl hpar =>
            rw [hpar.2]
            intro heq
            cases heq
            exact ordinal_lt_power_ne hb rfl
        | inr hpar =>
            rw [hpar.2]
            intro heq
            cases heq
    | negative en =>
        cases b with
        | one => exact False.elim (OrdinalNatural.Peano.not_lt_one a hb)
        | successor b' => contradiction

theorem principalRoot_rec_initial_h_negative {e : Peano} (hne : e ≠ zero)
    (a : OrdinalNatural.Peano) :
    ∀ b hbp hbn, a < b →
      power (positive b) e hbp ≠ negative a ∧ power (negative b) e hbn ≠ negative a := by
  intro b hbp hbn hb
  constructor
  · cases e with
    | zero => exact False.elim (hne rfl)
    | positive en =>
        change power_pos (positive b) en ≠ negative a
        rw [power_pos_positive_eq]
        intro heq
        cases heq
    | negative en =>
        cases b with
        | one => exact False.elim (OrdinalNatural.Peano.not_lt_one a hb)
        | successor b' => contradiction
  · cases e with
    | zero => exact False.elim (hne rfl)
    | positive en =>
        change power_pos (negative b) en ≠ negative a
        cases power_pos_negative_parity b en with
        | inl hpar =>
            rw [hpar.2]
            intro heq
            cases heq
        | inr hpar =>
            rw [hpar.2]
            intro heq
            cases heq
            exact ordinal_lt_power_ne hb rfl
    | negative en =>
        cases b with
        | one => exact False.elim (OrdinalNatural.Peano.not_lt_one a hb)
        | successor b' => contradiction

def principalRoot_rec (e a : Peano) (x : OrdinalNatural.Peano)
    (h : e ≠ zero) (h2 : isPower e a) (hnz : a ≠ zero)
    (h3 : ∀ b hbp hbn, x < b → power (positive b) e hbp ≠ a ∧ power (negative b) e hbn ≠ a) : Peano :=
  if hv : ValidPowerCondition (positive x) e = true then
    if hp : power (positive x) e hv = a then
      positive x
    else
      not_positive_power (by
        intro hp'
        intro hpow
        exact hp (by
          rw [power_proof_irrel (positive x) e hv hp']
          exact hpow))
  else
    not_positive_power (by
      intro hp'
      exact False.elim (hv hp'))
  where
    not_positive_power (hnp : ∀ hp, power (positive x) e hp ≠ a) : Peano :=
      if hv : ValidPowerCondition (negative x) e = true then
        if hn : power (negative x) e hv = a then
          negative x
        else
          not_power hnp (by
            intro hn'
            intro hpow
            exact hn (by
              rw [power_proof_irrel (negative x) e hv hn']
              exact hpow))
      else
        not_power hnp (by
          intro hn'
          exact False.elim (hv hn'))

    not_power (hnp : ∀ hp, power (positive x) e hp ≠ a) (hnn : ∀ hn, power (negative x) e hn ≠ a) : Peano :=
      match x with
      | .one => False.elim (principalRoot_rec_one_absurd h h2 hnz hnp hnn h3)
      | .successor x' => principalRoot_rec e a x' h h2 hnz (principalRoot_rec_step_h hnp hnn h3)



theorem principalRoot_rec_isPower {e a : Peano} {x : OrdinalNatural.Peano}
    (h : e ≠ zero) (h2 : isPower e a) (hnz : a ≠ zero)
    (h3 : ∀ b hbp hbn, x < b →
      power (positive b) e hbp ≠ a ∧ power (negative b) e hbn ≠ a) :
    ∃ hroot, power (principalRoot_rec e a x h h2 hnz h3) e hroot = a := by
  induction x with
  | one =>
      unfold principalRoot_rec
      by_cases hvp : ValidPowerCondition (positive OrdinalNatural.Peano.one) e = true
      · by_cases hp : power (positive OrdinalNatural.Peano.one) e hvp = a
        · simp [hvp, hp]
        · unfold principalRoot_rec.not_positive_power
          by_cases hvn : ValidPowerCondition (negative OrdinalNatural.Peano.one) e = true
          · by_cases hn : power (negative OrdinalNatural.Peano.one) e hvn = a
            · simp [hvp, hp, hvn, hn]
            · unfold principalRoot_rec.not_power
              simp [hvp, hp, hvn, hn]
              exact False.elim (principalRoot_rec_one_absurd h h2 hnz
                (by
                  intro hp'
                  intro hpow
                  exact hp (by
                    rw [power_proof_irrel (positive OrdinalNatural.Peano.one) e hvp hp']
                    exact hpow))
                (by
                  intro hn'
                  intro hpow
                  exact hn (by
                    rw [power_proof_irrel (negative OrdinalNatural.Peano.one) e hvn hn']
                    exact hpow))
                h3)
          · unfold principalRoot_rec.not_power
            simp [hvp, hp, hvn]
            exact False.elim (principalRoot_rec_one_absurd h h2 hnz
              (by
                intro hp'
                intro hpow
                exact hp (by
                  rw [power_proof_irrel (positive OrdinalNatural.Peano.one) e hvp hp']
                  exact hpow))
              (by
                intro hn'
                exact False.elim (hvn hn'))
              h3)
      · unfold principalRoot_rec.not_positive_power
        by_cases hvn : ValidPowerCondition (negative OrdinalNatural.Peano.one) e = true
        · by_cases hn : power (negative OrdinalNatural.Peano.one) e hvn = a
          · simp [hvp, hvn, hn]
          · unfold principalRoot_rec.not_power
            simp [hvp, hvn, hn]
            exact False.elim (principalRoot_rec_one_absurd h h2 hnz
              (by
                intro hp'
                exact False.elim (hvp hp'))
              (by
                intro hn'
                intro hpow
                exact hn (by
                  rw [power_proof_irrel (negative OrdinalNatural.Peano.one) e hvn hn']
                  exact hpow))
              h3)
        · unfold principalRoot_rec.not_power
          simp [hvp, hvn]
          exact False.elim (principalRoot_rec_one_absurd h h2 hnz
            (by
              intro hp'
              exact False.elim (hvp hp'))
            (by
              intro hn'
              exact False.elim (hvn hn'))
            h3)
  | successor x ih =>
      unfold principalRoot_rec
      by_cases hvp : ValidPowerCondition (positive x.successor) e = true
      · by_cases hp : power (positive x.successor) e hvp = a
        · simp [hvp, hp]
        · unfold principalRoot_rec.not_positive_power
          by_cases hvn : ValidPowerCondition (negative x.successor) e = true
          · by_cases hn : power (negative x.successor) e hvn = a
            · simp [hvp, hp, hvn, hn]
            · unfold principalRoot_rec.not_power
              simp [hvp, hp, hvn, hn]
              exact ih (principalRoot_rec_step_h
                (by
                  intro hp'
                  intro hpow
                  exact hp (by
                    rw [power_proof_irrel (positive x.successor) e hvp hp']
                    exact hpow))
                (by
                  intro hn'
                  intro hpow
                  exact hn (by
                    rw [power_proof_irrel (negative x.successor) e hvn hn']
                    exact hpow))
                h3)
          · unfold principalRoot_rec.not_power
            simp [hvp, hp, hvn]
            exact ih (principalRoot_rec_step_h
              (by
                intro hp'
                intro hpow
                exact hp (by
                  rw [power_proof_irrel (positive x.successor) e hvp hp']
                  exact hpow))
              (by
                intro hn'
                exact False.elim (hvn hn'))
              h3)
      · unfold principalRoot_rec.not_positive_power
        by_cases hvn : ValidPowerCondition (negative x.successor) e = true
        · by_cases hn : power (negative x.successor) e hvn = a
          · simp [hvp, hvn, hn]
          · unfold principalRoot_rec.not_power
            simp [hvp, hvn, hn]
            exact ih (principalRoot_rec_step_h
              (by
                intro hp'
                exact False.elim (hvp hp'))
              (by
                intro hn'
                intro hpow
                exact hn (by
                  rw [power_proof_irrel (negative x.successor) e hvn hn']
                  exact hpow))
              h3)
        · unfold principalRoot_rec.not_power
          simp [hvp, hvn]
          exact ih (principalRoot_rec_step_h
            (by
              intro hp'
              exact False.elim (hvp hp'))
            (by
              intro hn'
              exact False.elim (hvn hn'))
            h3)


theorem not_isPower_negative_zero (e : OrdinalNatural.Peano) :
    ¬ isPower (negative e) zero := by
  intro hpow
  rcases hpow with ⟨y, hy, hyzero⟩
  cases y with
  | zero => contradiction
  | positive n =>
      cases n with
      | one =>
          change power one (negative e) hy = zero at hyzero
          rw [power_oneInt] at hyzero
          cases hyzero
      | successor n => contradiction
  | negative n =>
      cases n with
      | one =>
          change power minusOne (negative e) hy = zero at hyzero
          rw [power_minusOne_negative] at hyzero
          cases power_pos_minusOne_eq_one_or_minusOne e with
          | inl hone =>
              rw [hone] at hyzero
              cases hyzero
          | inr hminus =>
              rw [hminus] at hyzero
              cases hyzero
      | successor n => contradiction

def principalRoot (e a : Peano) (h : e ≠ zero ∧ isPower e a) : Peano :=
  match a with
  | positive a' => principalRoot_rec e (positive a') a' h.1 h.2 (by intro hz; cases hz)
      (principalRoot_rec_initial_h_positive h.1 a')
  | negative a' => principalRoot_rec e (negative a') a' h.1 h.2 (by intro hz; cases hz)
      (principalRoot_rec_initial_h_negative h.1 a')
  | zero => zero


theorem principalRoot_rec_eq_positive_of_match {e a : Peano} (n z : OrdinalNatural.Peano)
    (hne : e ≠ zero) (his : isPower e a) (hnz : a ≠ zero)
    (hinit : ∀ b hbp hbn, z < b →
      power (positive b) e hbp ≠ a ∧ power (negative b) e hbn ≠ a)
    (hvpos : ValidPowerCondition (positive n) e = true)
    (hpow : power (positive n) e hvpos = a)
    (hle : n ≤ z)
    (hbig : ∀ b hbp hbn, n < b →
      power (positive b) e hbp ≠ a ∧ power (negative b) e hbn ≠ a) :
    principalRoot_rec e a z hne his hnz hinit = positive n := by
  induction z generalizing n with
  | one =>
      cases hle with
      | inl hlt =>
          exact False.elim (OrdinalNatural.Peano.not_lt_one n hlt)
      | inr heq =>
          subst heq
          unfold principalRoot_rec
          by_cases hvp : ValidPowerCondition (positive OrdinalNatural.Peano.one) e = true
          · have hp : power (positive OrdinalNatural.Peano.one) e hvp = a := by
              rw [power_proof_irrel (positive OrdinalNatural.Peano.one) e hvp hvpos]
              exact hpow
            simp [hvp, hp]
          · exact False.elim (hvp hvpos)
  | successor z ih =>
      cases hle with
      | inr heq =>
          subst heq
          unfold principalRoot_rec
          by_cases hvp : ValidPowerCondition (positive z.successor) e = true
          · have hp : power (positive z.successor) e hvp = a := by
              rw [power_proof_irrel (positive z.successor) e hvp hvpos]
              exact hpow
            simp [hvp, hp]
          · exact False.elim (hvp hvpos)
      | inl hnlt =>
          have hnp : ∀ hp, power (positive z.successor) e hp ≠ a := by
            intro hp
            cases e with
            | zero => exact False.elim (hne rfl)
            | positive en =>
                exact (hbig z.successor hp rfl hnlt).1
            | negative en => contradiction
          have hnn : ∀ hn, power (negative z.successor) e hn ≠ a := by
            intro hn
            cases e with
            | zero => exact False.elim (hne rfl)
            | positive en =>
                exact (hbig z.successor rfl hn hnlt).2
            | negative en => contradiction
          have hle_pred : n ≤ z := OrdinalNatural.Peano.le_of_lt_succ hnlt
          unfold principalRoot_rec
          by_cases hvp : ValidPowerCondition (positive z.successor) e = true
          · by_cases hp : power (positive z.successor) e hvp = a
            · exact False.elim (hnp hvp hp)
            · unfold principalRoot_rec.not_positive_power
              by_cases hvn : ValidPowerCondition (negative z.successor) e = true
              · by_cases hn : power (negative z.successor) e hvn = a
                · exact False.elim (hnn hvn hn)
                · unfold principalRoot_rec.not_power
                  simp [hvp, hp, hvn, hn]
                  exact ih n (principalRoot_rec_step_h hnp hnn hinit) hvpos hpow hle_pred hbig
              · unfold principalRoot_rec.not_power
                simp [hvp, hp, hvn]
                exact ih n (principalRoot_rec_step_h hnp hnn hinit) hvpos hpow hle_pred hbig
          · unfold principalRoot_rec.not_positive_power
            by_cases hvn : ValidPowerCondition (negative z.successor) e = true
            · by_cases hn : power (negative z.successor) e hvn = a
              · exact False.elim (hnn hvn hn)
              · unfold principalRoot_rec.not_power
                simp [hvp, hvn, hn]
                exact ih n (principalRoot_rec_step_h hnp hnn hinit) hvpos hpow hle_pred hbig
            · unfold principalRoot_rec.not_power
              simp [hvp, hvn]
              exact ih n (principalRoot_rec_step_h hnp hnn hinit) hvpos hpow hle_pred hbig

theorem principalRoot_rec_eq_negative_of_match {e a : Peano} (n z : OrdinalNatural.Peano)
    (hne : e ≠ zero) (his : isPower e a) (hnz : a ≠ zero)
    (hinit : ∀ b hbp hbn, z < b →
      power (positive b) e hbp ≠ a ∧ power (negative b) e hbn ≠ a)
    (hvneg : ValidPowerCondition (negative n) e = true)
    (hpow : power (negative n) e hvneg = a)
    (hpos : ∀ hp, power (positive n) e hp ≠ a)
    (hle : n ≤ z)
    (hbig : ∀ b hbp hbn, n < b →
      power (positive b) e hbp ≠ a ∧ power (negative b) e hbn ≠ a) :
    principalRoot_rec e a z hne his hnz hinit = negative n := by
  induction z generalizing n with
  | one =>
      cases hle with
      | inl hlt =>
          exact False.elim (OrdinalNatural.Peano.not_lt_one n hlt)
      | inr heq =>
          subst heq
          unfold principalRoot_rec
          by_cases hvp : ValidPowerCondition (positive OrdinalNatural.Peano.one) e = true
          · have hpnot : power (positive OrdinalNatural.Peano.one) e hvp ≠ a := hpos hvp
            unfold principalRoot_rec.not_positive_power
            by_cases hvn : ValidPowerCondition (negative OrdinalNatural.Peano.one) e = true
            · have hn : power (negative OrdinalNatural.Peano.one) e hvn = a := by
                rw [power_proof_irrel (negative OrdinalNatural.Peano.one) e hvn hvneg]
                exact hpow
              simp [hvp, hpnot, hvn, hn]
            · exact False.elim (hvn hvneg)
          · unfold principalRoot_rec.not_positive_power
            by_cases hvn : ValidPowerCondition (negative OrdinalNatural.Peano.one) e = true
            · have hn : power (negative OrdinalNatural.Peano.one) e hvn = a := by
                rw [power_proof_irrel (negative OrdinalNatural.Peano.one) e hvn hvneg]
                exact hpow
              simp [hvp, hvn, hn]
            · exact False.elim (hvn hvneg)
  | successor z ih =>
      cases hle with
      | inr heq =>
          subst heq
          unfold principalRoot_rec
          by_cases hvp : ValidPowerCondition (positive z.successor) e = true
          · have hpnot : power (positive z.successor) e hvp ≠ a := hpos hvp
            unfold principalRoot_rec.not_positive_power
            by_cases hvn : ValidPowerCondition (negative z.successor) e = true
            · have hn : power (negative z.successor) e hvn = a := by
                rw [power_proof_irrel (negative z.successor) e hvn hvneg]
                exact hpow
              simp [hvp, hpnot, hvn, hn]
            · exact False.elim (hvn hvneg)
          · unfold principalRoot_rec.not_positive_power
            by_cases hvn : ValidPowerCondition (negative z.successor) e = true
            · have hn : power (negative z.successor) e hvn = a := by
                rw [power_proof_irrel (negative z.successor) e hvn hvneg]
                exact hpow
              simp [hvp, hvn, hn]
            · exact False.elim (hvn hvneg)
      | inl hnlt =>
          have hnp : ∀ hp, power (positive z.successor) e hp ≠ a := by
            intro hp
            cases e with
            | zero => exact False.elim (hne rfl)
            | positive en =>
                exact (hbig z.successor hp rfl hnlt).1
            | negative en => contradiction
          have hnn : ∀ hn, power (negative z.successor) e hn ≠ a := by
            intro hn
            cases e with
            | zero => exact False.elim (hne rfl)
            | positive en =>
                exact (hbig z.successor rfl hn hnlt).2
            | negative en => contradiction
          have hle_pred : n ≤ z := OrdinalNatural.Peano.le_of_lt_succ hnlt
          unfold principalRoot_rec
          by_cases hvp : ValidPowerCondition (positive z.successor) e = true
          · by_cases hp : power (positive z.successor) e hvp = a
            · exact False.elim (hnp hvp hp)
            · unfold principalRoot_rec.not_positive_power
              by_cases hvn : ValidPowerCondition (negative z.successor) e = true
              · by_cases hn : power (negative z.successor) e hvn = a
                · exact False.elim (hnn hvn hn)
                · unfold principalRoot_rec.not_power
                  simp [hvp, hp, hvn, hn]
                  exact ih n (principalRoot_rec_step_h hnp hnn hinit) hvneg hpow hpos hle_pred hbig
              · unfold principalRoot_rec.not_power
                simp [hvp, hp, hvn]
                exact ih n (principalRoot_rec_step_h hnp hnn hinit) hvneg hpow hpos hle_pred hbig
          · unfold principalRoot_rec.not_positive_power
            by_cases hvn : ValidPowerCondition (negative z.successor) e = true
            · by_cases hn : power (negative z.successor) e hvn = a
              · exact False.elim (hnn hvn hn)
              · unfold principalRoot_rec.not_power
                simp [hvp, hvn, hn]
                exact ih n (principalRoot_rec_step_h hnp hnn hinit) hvneg hpow hpos hle_pred hbig
            · unfold principalRoot_rec.not_power
              simp [hvp, hvn]
              exact ih n (principalRoot_rec_step_h hnp hnn hinit) hvneg hpow hpos hle_pred hbig

theorem power_pos_negative_eq_of_odd {y e : OrdinalNatural.Peano}
    (he : isOdd (positive e)) :
    power_pos (negative y) e = negative (y ^ e) := by
  cases power_pos_negative_parity y e with
  | inl hpar =>
      exact False.elim (he ((isEven_positive_iff_natMod e).mpr hpar.1))
  | inr hpar =>
      exact hpar.2

theorem power_pos_minusOne_eq_of_odd_negative {e : OrdinalNatural.Peano}
    (he : isOdd (negative e)) :
    power_pos minusOne e = minusOne := by
  cases power_pos_negative_parity OrdinalNatural.Peano.one e with
  | inl hpar =>
      exact False.elim (he ((isEven_negative_iff_natMod e).mpr hpar.1))
  | inr hpar =>
      rw [minusOne]
      rw [OrdinalNatural.Peano.one_power] at hpar
      exact hpar.2

theorem principalRoot_eq_of_eq {e a b : Peano} (hab : a = b)
    (ha : e ≠ zero ∧ isPower e a) (hb : e ≠ zero ∧ isPower e b) :
    principalRoot e a ha = principalRoot e b hb := by
  subst hab
  cases a <;> rfl

theorem principalRoot_power_eq (x e : Peano) (hx : zero ≤ x) (he : e ≠ zero)
    (h : ValidPowerCondition x e = true) :
    ∃ h2, principalRoot e (power x e h) h2 = x := by
  let h2 : e ≠ zero ∧ isPower e (power x e h) := ⟨he, ⟨x, h, rfl⟩⟩
  refine ⟨h2, ?_⟩
  cases hx with
  | inl hxlt =>
      cases hxlt with
      | zero_less_than_positive =>
          rename_i xn
          cases e with
          | zero => exact False.elim (he rfl)
          | positive en =>
              have hpower_eq : power (positive xn) (positive en) h = positive (xn ^ en) := by
                change power_pos (positive xn) en = positive (xn ^ en)
                exact power_pos_positive_eq xn en
              have his : isPower (positive en) (positive (xn ^ en)) := by
                rw [← hpower_eq]
                exact h2.2
              let h2pos : (positive en) ≠ zero ∧ isPower (positive en) (positive (xn ^ en)) := ⟨h2.1, his⟩
              have hbig_pos : ∀ b hbp hbn, xn < b →
                  power (positive b) (positive en) hbp ≠ positive (xn ^ en) ∧
                    power (negative b) (positive en) hbn ≠ positive (xn ^ en) := by
                intro b hbp hbn hb
                constructor
                · change power_pos (positive b) en ≠ positive (xn ^ en)
                  rw [power_pos_positive_eq]
                  intro heq
                  have hp : b ^ en = xn ^ en := by injection heq
                  have hbeq : b = xn := OrdinalNatural.Peano.power_cancel_left en b xn hp
                  rw [hbeq] at hb
                  exact OrdinalNatural.Peano.not_lt_self xn hb
                · change power_pos (negative b) en ≠ positive (xn ^ en)
                  cases power_pos_negative_parity b en with
                  | inl hpar =>
                      rw [hpar.2]
                      intro heq
                      have hp : b ^ en = xn ^ en := by injection heq
                      have hbeq : b = xn := OrdinalNatural.Peano.power_cancel_left en b xn hp
                      rw [hbeq] at hb
                      exact OrdinalNatural.Peano.not_lt_self xn hb
                  | inr hpar =>
                      rw [hpar.2]
                      intro heq
                      cases heq
              calc
                principalRoot (positive en) (power (positive xn) (positive en) h) h2
                    = principalRoot (positive en) (positive (xn ^ en)) h2pos :=
                      principalRoot_eq_of_eq hpower_eq h2 h2pos
                _ = positive xn := by
                  change principalRoot_rec (positive en) (positive (xn ^ en)) (xn ^ en) h2pos.1 h2pos.2
                      (by intro hz; cases hz) (principalRoot_rec_initial_h_positive h2pos.1 (xn ^ en)) = positive xn
                  exact principalRoot_rec_eq_positive_of_match xn (xn ^ en) h2pos.1 h2pos.2
                    (by intro hz; cases hz) (principalRoot_rec_initial_h_positive h2pos.1 (xn ^ en))
                    h hpower_eq (OrdinalNatural.Peano.le_power xn en) hbig_pos
          | negative en =>
              cases xn with
              | one =>
                  have hpowone : power one (negative en) h = one := power_oneInt (negative en) h
                  let h2one : (negative en) ≠ zero ∧ isPower (negative en) one := by
                    constructor
                    · exact h2.1
                    · rw [← hpowone]
                      exact h2.2
                  calc
                    principalRoot (negative en) (power one (negative en) h) h2
                        = principalRoot (negative en) one h2one :=
                          principalRoot_eq_of_eq hpowone h2 h2one
                    _ = one := by
                      change principalRoot_rec (negative en) (positive OrdinalNatural.Peano.one) OrdinalNatural.Peano.one h2one.1 h2one.2
                        (by intro hz; cases hz) (principalRoot_rec_initial_h_positive h2one.1 OrdinalNatural.Peano.one) = one
                      exact principalRoot_rec_eq_positive_of_match OrdinalNatural.Peano.one OrdinalNatural.Peano.one h2one.1 h2one.2
                        (by intro hz; cases hz) (principalRoot_rec_initial_h_positive h2one.1 OrdinalNatural.Peano.one)
                        (validPowerCondition_oneInt (negative en)) (power_oneInt (negative en) _) (Or.inr rfl)
                        (principalRoot_rec_initial_h_positive h2one.1 OrdinalNatural.Peano.one)
              | successor xn' => contradiction
  | inr hxeq =>
      subst hxeq
      cases e with
      | zero => exact False.elim (he rfl)
      | positive en =>
          rfl
      | negative en => contradiction

theorem power_pos_negative_eq_of_even {y e : OrdinalNatural.Peano}
    (he : isEven (positive e)) :
    power_pos (negative y) e = positive (y ^ e) := by
  cases power_pos_negative_parity y e with
  | inl hpar =>
      exact hpar.2
  | inr hpar =>
      have hev : e.toNat % 2 = 0 := (isEven_positive_iff_natMod e).mp he
      rw [hpar.1] at hev
      contradiction

theorem power_pos_minusOne_eq_of_even_negative {e : OrdinalNatural.Peano}
    (he : isEven (negative e)) :
    power_pos minusOne e = one := by
  cases power_pos_negative_parity OrdinalNatural.Peano.one e with
  | inl hpar =>
      rw [minusOne]
      rw [OrdinalNatural.Peano.one_power] at hpar
      exact hpar.2
  | inr hpar =>
      have hev : e.toNat % 2 = 0 := (isEven_negative_iff_natMod e).mp he
      rw [hpar.1] at hev
      contradiction

theorem principalRoot_power_eq_of_even (x e : Peano) (he : isEven e) (he_ne : e ≠ zero)
    (h : ValidPowerCondition x e = true) :
    ∃ h2, principalRoot e (power x e h) h2 = absoluteValue x := by
  cases x with
  | zero =>
      simpa [absoluteValue] using principalRoot_power_eq zero e (Or.inr rfl) he_ne h
  | positive xn =>
      simpa [absoluteValue] using
        principalRoot_power_eq (positive xn) e (Or.inl LessThan.zero_less_than_positive) he_ne h
  | negative xn =>
      cases e with
      | zero => exact False.elim (he_ne rfl)
      | positive en =>
          have hpower_eq : power (negative xn) (positive en) h = positive (xn ^ en) := by
            change power_pos (negative xn) en = positive (xn ^ en)
            exact power_pos_negative_eq_of_even he
          let h2 : (positive en) ≠ zero ∧ isPower (positive en) (power (negative xn) (positive en) h) :=
            ⟨he_ne, ⟨negative xn, h, rfl⟩⟩
          refine ⟨h2, ?_⟩
          have his : isPower (positive en) (positive (xn ^ en)) := by
            rw [← hpower_eq]
            exact h2.2
          let h2pos : (positive en) ≠ zero ∧ isPower (positive en) (positive (xn ^ en)) := ⟨h2.1, his⟩
          have hbig_pos : ∀ b hbp hbn, xn < b →
              power (positive b) (positive en) hbp ≠ positive (xn ^ en) ∧
                power (negative b) (positive en) hbn ≠ positive (xn ^ en) := by
            intro b hbp hbn hb
            constructor
            · change power_pos (positive b) en ≠ positive (xn ^ en)
              rw [power_pos_positive_eq]
              intro heq
              have hp : b ^ en = xn ^ en := by injection heq
              have hbeq : b = xn := OrdinalNatural.Peano.power_cancel_left en b xn hp
              rw [hbeq] at hb
              exact OrdinalNatural.Peano.not_lt_self xn hb
            · change power_pos (negative b) en ≠ positive (xn ^ en)
              cases power_pos_negative_parity b en with
              | inl hpar =>
                  rw [hpar.2]
                  intro heq
                  have hp : b ^ en = xn ^ en := by injection heq
                  have hbeq : b = xn := OrdinalNatural.Peano.power_cancel_left en b xn hp
                  rw [hbeq] at hb
                  exact OrdinalNatural.Peano.not_lt_self xn hb
              | inr hpar =>
                  rw [hpar.2]
                  intro heq
                  cases heq
          have hpower_pos_eq : power (positive xn) (positive en)
              (validPowerCondition_pos (positive xn) en) = positive (xn ^ en) := by
            change power_pos (positive xn) en = positive (xn ^ en)
            exact power_pos_positive_eq xn en
          calc
            principalRoot (positive en) (power (negative xn) (positive en) h) h2
                = principalRoot (positive en) (positive (xn ^ en)) h2pos :=
                  principalRoot_eq_of_eq hpower_eq h2 h2pos
            _ = positive xn := by
              change principalRoot_rec (positive en) (positive (xn ^ en)) (xn ^ en) h2pos.1 h2pos.2
                  (by intro hz; cases hz) (principalRoot_rec_initial_h_positive h2pos.1 (xn ^ en)) = positive xn
              exact principalRoot_rec_eq_positive_of_match xn (xn ^ en) h2pos.1 h2pos.2
                (by intro hz; cases hz) (principalRoot_rec_initial_h_positive h2pos.1 (xn ^ en))
                (validPowerCondition_pos (positive xn) en) hpower_pos_eq
                (OrdinalNatural.Peano.le_power xn en) hbig_pos
      | negative en =>
          cases xn with
          | one =>
              have hpower_eq : power minusOne (negative en) h = one := by
                rw [power_minusOne_negative]
                exact power_pos_minusOne_eq_of_even_negative he
              let h2 : (negative en) ≠ zero ∧ isPower (negative en) (power minusOne (negative en) h) :=
                ⟨he_ne, ⟨minusOne, h, rfl⟩⟩
              refine ⟨h2, ?_⟩
              let hone : ValidPowerCondition one (negative en) = true := validPowerCondition_oneInt (negative en)
              rcases principalRoot_power_eq one (negative en)
                  (Or.inl LessThan.zero_less_than_positive) he_ne hone with ⟨h2one, hrootone⟩
              have hpowone : power one (negative en) hone = one := power_oneInt (negative en) hone
              have hpowers : power minusOne (negative en) h = power one (negative en) hone := by
                rw [hpower_eq, hpowone]
              calc
                principalRoot (negative en) (power minusOne (negative en) h) h2
                    = principalRoot (negative en) (power one (negative en) hone) h2one :=
                      principalRoot_eq_of_eq hpowers h2 h2one
                _ = one := hrootone
          | successor xn' =>
              contradiction

theorem principalRoot_power_eq_of_odd (x e : Peano) (he : isOdd e)
    (h : ValidPowerCondition x e = true) :
    ∃ h2, principalRoot e (power x e h) h2 = x := by
  have hne : e ≠ zero := isOdd_ne_zero he
  cases x with
  | zero =>
      exact principalRoot_power_eq zero e (Or.inr rfl) hne h
  | positive xn =>
      exact principalRoot_power_eq (positive xn) e (Or.inl LessThan.zero_less_than_positive) hne h
  | negative xn =>
      cases e with
      | zero =>
          exact False.elim (hne rfl)
      | positive en =>
          have hpower_eq : power (negative xn) (positive en) h = negative (xn ^ en) := by
            change power_pos (negative xn) en = negative (xn ^ en)
            exact power_pos_negative_eq_of_odd he
          let h2 : (positive en) ≠ zero ∧ isPower (positive en) (power (negative xn) (positive en) h) :=
            ⟨hne, ⟨negative xn, h, rfl⟩⟩
          refine ⟨h2, ?_⟩
          have his : isPower (positive en) (negative (xn ^ en)) := by
            rw [← hpower_eq]
            exact h2.2
          let h2neg : (positive en) ≠ zero ∧ isPower (positive en) (negative (xn ^ en)) := ⟨h2.1, his⟩
          have hpos : ∀ hp, power (positive xn) (positive en) hp ≠ negative (xn ^ en) := by
            intro hp
            change power_pos (positive xn) en ≠ negative (xn ^ en)
            rw [power_pos_positive_eq]
            intro heq
            cases heq
          have hbig : ∀ b hbp hbn, xn < b →
              power (positive b) (positive en) hbp ≠ negative (xn ^ en) ∧
                power (negative b) (positive en) hbn ≠ negative (xn ^ en) := by
            intro b hbp hbn hb
            constructor
            · change power_pos (positive b) en ≠ negative (xn ^ en)
              rw [power_pos_positive_eq]
              intro heq
              cases heq
            · change power_pos (negative b) en ≠ negative (xn ^ en)
              cases power_pos_negative_parity b en with
              | inl hpar =>
                  rw [hpar.2]
                  intro heq
                  cases heq
              | inr hpar =>
                  rw [hpar.2]
                  intro heq
                  have hp : b ^ en = xn ^ en := by injection heq
                  have hbeq : b = xn := OrdinalNatural.Peano.power_cancel_left en b xn hp
                  rw [hbeq] at hb
                  exact OrdinalNatural.Peano.not_lt_self xn hb
          calc
            principalRoot (positive en) (power (negative xn) (positive en) h) h2
                = principalRoot (positive en) (negative (xn ^ en)) h2neg :=
                  principalRoot_eq_of_eq hpower_eq h2 h2neg
            _ = negative xn := by
              change principalRoot_rec (positive en) (negative (xn ^ en)) (xn ^ en) h2neg.1 h2neg.2
                  (by intro hz; cases hz) (principalRoot_rec_initial_h_negative h2neg.1 (xn ^ en)) = negative xn
              exact principalRoot_rec_eq_negative_of_match xn (xn ^ en) h2neg.1 h2neg.2
                (by intro hz; cases hz) (principalRoot_rec_initial_h_negative h2neg.1 (xn ^ en))
                h hpower_eq hpos (OrdinalNatural.Peano.le_power xn en) hbig
      | negative en =>
          cases xn with
          | one =>
              have hpower_eq : power minusOne (negative en) h = minusOne := by
                rw [power_minusOne_negative]
                exact power_pos_minusOne_eq_of_odd_negative he
              let h2 : (negative en) ≠ zero ∧ isPower (negative en) (power minusOne (negative en) h) :=
                ⟨hne, ⟨minusOne, h, rfl⟩⟩
              refine ⟨h2, ?_⟩
              have his : isPower (negative en) minusOne := by
                rw [← hpower_eq]
                exact h2.2
              let h2neg : (negative en) ≠ zero ∧ isPower (negative en) minusOne := ⟨h2.1, his⟩
              have hpos : ∀ hp, power one (negative en) hp ≠ minusOne := by
                intro hp
                rw [power_oneInt]
                intro heq
                cases heq
              calc
                principalRoot (negative en) (power minusOne (negative en) h) h2
                    = principalRoot (negative en) minusOne h2neg :=
                      principalRoot_eq_of_eq hpower_eq h2 h2neg
                _ = minusOne := by
                  change principalRoot_rec (negative en) minusOne OrdinalNatural.Peano.one h2neg.1 h2neg.2
                    (by intro hz; cases hz) (principalRoot_rec_initial_h_negative h2neg.1 OrdinalNatural.Peano.one) = negative OrdinalNatural.Peano.one
                  exact principalRoot_rec_eq_negative_of_match OrdinalNatural.Peano.one OrdinalNatural.Peano.one
                    h2neg.1 h2neg.2 (by intro hz; cases hz)
                    (principalRoot_rec_initial_h_negative h2neg.1 OrdinalNatural.Peano.one)
                    (validPowerCondition_negOneInt (negative en)) hpower_eq hpos (Or.inr rfl)
                    (principalRoot_rec_initial_h_negative h2neg.1 OrdinalNatural.Peano.one)
          | successor xn' =>
              contradiction

theorem principalRoot_isPower (e x : Peano) (h : e ≠ zero ∧ isPower e x) :
    ∃ h2, power (principalRoot e x h) e h2 = x := by
  cases x with
  | zero =>
      cases e with
      | zero => exact False.elim (h.1 rfl)
      | positive en =>
          refine ⟨?_, ?_⟩
          · rfl
          · rfl
      | negative en =>
          exact False.elim (not_isPower_negative_zero en h.2)
  | positive xn =>
      change ∃ h2, power (principalRoot_rec e (positive xn) xn h.1 h.2 (by intro hz; cases hz)
        (principalRoot_rec_initial_h_positive h.1 xn)) e h2 = positive xn
      exact principalRoot_rec_isPower h.1 h.2 (by intro hz; cases hz)
        (principalRoot_rec_initial_h_positive h.1 xn)
  | negative xn =>
      change ∃ h2, power (principalRoot_rec e (negative xn) xn h.1 h.2 (by intro hz; cases hz)
        (principalRoot_rec_initial_h_negative h.1 xn)) e h2 = negative xn
      exact principalRoot_rec_isPower h.1 h.2 (by intro hz; cases hz)
        (principalRoot_rec_initial_h_negative h.1 xn)

end Peano

end ZeroMath.Numbers.Integer
