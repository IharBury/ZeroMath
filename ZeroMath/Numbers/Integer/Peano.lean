import ZeroMath.Numbers.CardinalNatural.Peano
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

theorem absoluteValue_negate (x : Peano) : absoluteValue x = absoluteValue (negate x) := by
  cases x <;> rfl

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

def fromCardinalNatural : CardinalNatural.Peano → Peano
  | CardinalNatural.Peano.zero => zero
  | CardinalNatural.Peano.successor n =>
      positive (CardinalNatural.Peano.toOrdinal (CardinalNatural.Peano.successor n) (CardinalNatural.Peano.successor_ne_zero n))

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

instance {a b : Peano} : Decidable (a < b) :=
  match h : isLessThan a b with
  | true => isTrue ((isLessThan_eq_true_iff_lt a b).mp h)
  | false => isFalse ((isLessThan_eq_false_iff_not_lt a b).mp h)

instance {a b : Peano} : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a < b ∨ a = b))

def toCardinalNatural (x : Peano) (h : zero ≤ x) : CardinalNatural.Peano :=
  match x, h with
  | zero, _ => CardinalNatural.Peano.zero
  | positive n, _ => CardinalNatural.Peano.fromOrdinal n
  | negative _, hneg => False.elim (by
      cases hneg with
      | inl hlt => cases hlt
      | inr heq => cases heq)

def toNat (x : Peano) (h : zero ≤ x) : Nat :=
  (toCardinalNatural x h).toNat

theorem toCardinalNatural_fromCardinalNatural (x : CardinalNatural.Peano) : ∃ h, toCardinalNatural (fromCardinalNatural x) h = x := by
  cases x with
  | zero =>
    exists Or.inr rfl
  | successor n =>
    have h_le : zero ≤ fromCardinalNatural (CardinalNatural.Peano.successor n) := Or.inl LessThan.zero_less_than_positive
    exists h_le
    simp [fromCardinalNatural, toCardinalNatural]
    exact CardinalNatural.Peano.fromOrdinal_toOrdinal (CardinalNatural.Peano.successor n) (CardinalNatural.Peano.successor_ne_zero n)

theorem fromCardinalNatural_toCardinalNatural (x : Peano) (h : zero ≤ x) : fromCardinalNatural (toCardinalNatural x h) = x := by
  cases x with
  | negative n =>
      cases h with
      | inl hlt => cases hlt
      | inr heq => cases heq
  | zero =>
      simp [toCardinalNatural, fromCardinalNatural]
  | positive n =>
      simp [toCardinalNatural]
      have h_nz : CardinalNatural.Peano.fromOrdinal n ≠ CardinalNatural.Peano.zero :=
        CardinalNatural.Peano.fromOrdinal_ne_zero n
      cases c : CardinalNatural.Peano.fromOrdinal n with
      | zero => contradiction
      | successor m =>
          simp [fromCardinalNatural]
          -- Goal after simp: positive (toOrdinal (successor m) (snz m)) = positive n
          have h_eq_val : CardinalNatural.Peano.successor m = CardinalNatural.Peano.fromOrdinal n := c.symm
          -- Prove the inner equality using toOrdinal_fromOrdinal_helper and toOrdinal_congr
          have h_to : CardinalNatural.Peano.toOrdinal (CardinalNatural.Peano.successor m) (CardinalNatural.Peano.successor_ne_zero m) = n := by
            -- toOrdinal (fromOrdinal n) h_nz = n
            have h_base := CardinalNatural.Peano.toOrdinal_fromOrdinal_helper n h_nz
            -- Rewrite the argument of toOrdinal using the equality of values; the proofs are both non-zero proofs for equivalent values
            rw [← CardinalNatural.Peano.toOrdinal_congr h_eq_val (CardinalNatural.Peano.successor_ne_zero m) h_nz] at h_base
            exact h_base
          rw [h_to]

theorem fromCardinalNatural_fromOrdinal (n : OrdinalNatural.Peano) :
    fromCardinalNatural (CardinalNatural.Peano.fromOrdinal n) = positive n :=
  fromCardinalNatural_toCardinalNatural (positive n)
    (Or.inl LessThan.zero_less_than_positive)

def successor : Peano → Peano
  | negative (OrdinalNatural.Peano.successor n) => negative n
  | negative OrdinalNatural.Peano.one => zero
  | zero => positive OrdinalNatural.Peano.one
  | positive n => positive (OrdinalNatural.Peano.successor n)

theorem fromCardinalNatural_successor (n : CardinalNatural.Peano) :
    fromCardinalNatural n.successor = (fromCardinalNatural n).successor := by
  cases n with
  | zero =>
      rfl
  | successor n' =>
      have hnz : CardinalNatural.Peano.successor n' ≠ CardinalNatural.Peano.zero :=
        CardinalNatural.Peano.successor_ne_zero n'
      have hnz' : CardinalNatural.Peano.successor (CardinalNatural.Peano.successor n') ≠
          CardinalNatural.Peano.zero :=
        CardinalNatural.Peano.successor_ne_zero _
      simp only [fromCardinalNatural, successor]
      exact congrArg positive
        (CardinalNatural.Peano.toOrdinal_successor
          (CardinalNatural.Peano.successor n') hnz' hnz)

theorem fromCardinalNatural_lt_iff (a b : CardinalNatural.Peano) :
    fromCardinalNatural a < fromCardinalNatural b ↔ a < b := by
  constructor
  · intro h
    cases a with
    | zero =>
      cases b with
      | zero => cases h
      | successor b' => exact CardinalNatural.Peano.zero_lt_successor b'
    | successor a' =>
      cases b with
      | zero => cases h
      | successor b' =>
          cases h with
          | positive_less_than_positive hlt =>
              exact CardinalNatural.Peano.lt_of_toOrdinal_lt
                (CardinalNatural.Peano.successor_ne_zero a')
                (CardinalNatural.Peano.successor_ne_zero b') hlt
  · intro h
    cases a with
    | zero =>
      cases b with
      | zero => exact False.elim (CardinalNatural.Peano.not_lt_self _ h)
      | successor b' =>
          simp only [fromCardinalNatural]
          exact LessThan.zero_less_than_positive
    | successor a' =>
      cases b with
      | zero => exact False.elim (CardinalNatural.Peano.not_lt_zero _ h)
      | successor b' =>
          simp only [fromCardinalNatural]
          exact LessThan.positive_less_than_positive
            (CardinalNatural.Peano.toOrdinal_lt_of_lt
              (CardinalNatural.Peano.successor_ne_zero a')
              (CardinalNatural.Peano.successor_ne_zero b') h)

theorem negate_fromCardinalNatural_lt_iff
    {a b : CardinalNatural.Peano}
    (ha : a ≠ CardinalNatural.Peano.zero) (hb : b ≠ CardinalNatural.Peano.zero) :
    -(fromCardinalNatural a) < -(fromCardinalNatural b) ↔ b < a := by
  cases a with
  | zero => exact False.elim (ha rfl)
  | successor a' =>
      cases b with
      | zero => exact False.elim (hb rfl)
      | successor b' =>
          simp only [fromCardinalNatural, Neg.neg, negate]
          constructor
          · intro h
            cases h with
            | negative_less_than_negative hlt =>
                exact CardinalNatural.Peano.lt_of_toOrdinal_lt
                  (CardinalNatural.Peano.successor_ne_zero b')
                  (CardinalNatural.Peano.successor_ne_zero a') hlt
          · intro h
            exact LessThan.negative_less_than_negative
              (CardinalNatural.Peano.toOrdinal_lt_of_lt
                (CardinalNatural.Peano.successor_ne_zero b')
                (CardinalNatural.Peano.successor_ne_zero a') h)

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
theorem subtract_zero (a : Peano) : a - zero = a := by
  have h : a - zero = subtract a zero := rfl
  rw [h]
  rw [subtract.eq_def]

@[simp]
theorem subtract_positive_one (a : Peano) : a - positive OrdinalNatural.Peano.one = predecessor a := by
  have h : a - positive OrdinalNatural.Peano.one = subtract a (positive OrdinalNatural.Peano.one) := rfl
  rw [h]
  rw [subtract.eq_def]

theorem subtract_one (a : Peano) : a - one = predecessor a := by
  rw [one, subtract_positive_one]

/-- Subtracting one from the successor of a positive integer recovers that
integer. -/
theorem positive_successor_subtract_one (n : OrdinalNatural.Peano) :
    positive n.successor - one = positive n := by
  rw [subtract_one]
  rfl

@[simp]
theorem subtract_positive_successor (a : Peano) (n : OrdinalNatural.Peano) : a - positive (OrdinalNatural.Peano.successor n) = predecessor (a - positive n) := by
  have h1 : a - positive (OrdinalNatural.Peano.successor n) = subtract a (positive (OrdinalNatural.Peano.successor n)) := rfl
  have h2 : a - positive n = subtract a (positive n) := rfl
  rw [h1, h2]
  rw [subtract.eq_def]

@[simp]
theorem subtract_negative_one (a : Peano) : a - negative OrdinalNatural.Peano.one = successor a := by
  have h : a - negative OrdinalNatural.Peano.one = subtract a (negative OrdinalNatural.Peano.one) := rfl
  rw [h]
  rw [Peano.subtract.eq_def]

@[simp]
theorem subtract_negative_successor (a : Peano) (n : OrdinalNatural.Peano) : a - negative (OrdinalNatural.Peano.successor n) = successor (a - negative n) := by
  have h1 : a - negative (OrdinalNatural.Peano.successor n) = subtract a (negative (OrdinalNatural.Peano.successor n)) := rfl
  have h2 : a - negative n = subtract a (negative n) := rfl
  rw [h1, h2]
  rw [subtract.eq_def]

@[simp]
theorem add_positive_one (a : Peano) : a + positive OrdinalNatural.Peano.one = successor a := by
  have h : a + positive OrdinalNatural.Peano.one = add a (positive OrdinalNatural.Peano.one) := rfl
  rw [h]
  rw [add.eq_def]

@[simp]
theorem add_positive_successor (a : Peano) (n : OrdinalNatural.Peano) : a + positive (OrdinalNatural.Peano.successor n) = successor (a + positive n) := by
  have h1 : a + positive (OrdinalNatural.Peano.successor n) = add a (positive (OrdinalNatural.Peano.successor n)) := rfl
  have h2 : a + positive n = add a (positive n) := rfl
  rw [h1, h2]
  rw [add.eq_def]

@[simp]
theorem add_negative_one (a : Peano) : a + negative OrdinalNatural.Peano.one = predecessor a := by
  have h : a + negative OrdinalNatural.Peano.one = add a (negative OrdinalNatural.Peano.one) := rfl
  rw [h]
  rw [add.eq_def]

@[simp]
theorem add_negative_successor (a : Peano) (n : OrdinalNatural.Peano) : a + negative (OrdinalNatural.Peano.successor n) = predecessor (a + negative n) := by
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
      rw [add_positive_one, successor]
    | successor n ih =>
      rw [add_positive_successor, ih, successor]
  | negative n =>
    induction n with
    | one =>
      rw [add_negative_one, predecessor]
    | successor n ih =>
      rw [add_negative_successor, ih, predecessor]

@[simp]
theorem successor_predecessor (a : Peano) : successor (predecessor a) = a := by
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
theorem predecessor_successor (a : Peano) : predecessor (successor a) = a := by
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
theorem successor_add (a b : Peano) : successor a + b = successor (a + b) := by
  cases b with
  | zero =>
    rw [add_zero, add_zero]
  | positive n =>
    induction n with
    | one =>
      rw [add_positive_one, add_positive_one]
    | successor n ih =>
      rw [add_positive_successor, add_positive_successor, ih]
  | negative n =>
    induction n with
    | one =>
      rw [add_negative_one, add_negative_one, successor_predecessor, predecessor_successor]
    | successor n ih =>
      rw [add_negative_successor, add_negative_successor, ih, successor_predecessor, predecessor_successor]

@[simp]
theorem predecessor_add (a b : Peano) : predecessor a + b = predecessor (a + b) := by
  cases b with
  | zero =>
    rw [add_zero, add_zero]
  | positive n =>
    induction n with
    | one =>
      rw [add_positive_one, add_positive_one, predecessor_successor, successor_predecessor]
    | successor n ih =>
      rw [add_positive_successor, add_positive_successor, ih, predecessor_successor, successor_predecessor]
  | negative n =>
    induction n with
    | one =>
      rw [add_negative_one, add_negative_one]
    | successor n ih =>
      rw [add_negative_successor, add_negative_successor, ih]

@[simp]
theorem successor_subtract (a b : Peano) : successor a - b = successor (a - b) := by
  induction b with
  | zero =>
    rw [subtract_zero, subtract_zero]
  | positive n =>
    induction n with
    | one =>
      rw [subtract_positive_one, subtract_positive_one]
      rw [predecessor_successor, successor_predecessor]
    | successor n ih =>
      rw [subtract_positive_successor, subtract_positive_successor]
      rw [ih, predecessor_successor, successor_predecessor]
  | negative n =>
    induction n with
    | one =>
      rw [subtract_negative_one, subtract_negative_one]
    | successor n ih =>
      rw [subtract_negative_successor, subtract_negative_successor]
      rw [ih]

@[simp]
theorem predecessor_subtract (a b : Peano) : predecessor a - b = predecessor (a - b) := by
  induction b with
  | zero =>
    rw [subtract_zero, subtract_zero]
  | positive n =>
    induction n with
    | one =>
      rw [subtract_positive_one, subtract_positive_one]
    | successor n ih =>
      rw [subtract_positive_successor, subtract_positive_successor]
      rw [ih]
  | negative n =>
    induction n with
    | one =>
      rw [subtract_negative_one, subtract_negative_one]
      rw [successor_predecessor, predecessor_successor]
    | successor n ih =>
      rw [subtract_negative_successor, subtract_negative_successor]
      rw [ih, successor_predecessor, predecessor_successor]

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

theorem add_commutative (a b : Peano) : a + b = b + a := by
  cases b with
  | zero =>
    rw [add_zero, zero_add]
  | positive n =>
    induction n with
    | one =>
      rw [add_positive_one]
      have h1 : positive OrdinalNatural.Peano.one + a = successor (zero + a) := by
        have h_succ : positive OrdinalNatural.Peano.one = successor zero := rfl
        rw [h_succ, successor_add]
      rw [h1, zero_add]
    | successor n ih =>
      rw [add_positive_successor]
      have h1 : positive n.successor + a = successor (positive n + a) := by
        have h_succ : positive n.successor = successor (positive n) := rfl
        rw [h_succ, successor_add]
      rw [h1, ih]
  | negative n =>
    induction n with
    | one =>
      rw [add_negative_one]
      have h1 : negative OrdinalNatural.Peano.one + a = predecessor (zero + a) := by
        have h_pred : negative OrdinalNatural.Peano.one = predecessor zero := rfl
        rw [h_pred, predecessor_add]
      rw [h1, zero_add]
    | successor n ih =>
      rw [add_negative_successor]
      have h1 : negative n.successor + a = predecessor (negative n + a) := by
        have h_pred : negative n.successor = predecessor (negative n) := rfl
        rw [h_pred, predecessor_add]
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

theorem fromCardinalNatural_injective {a b : CardinalNatural.Peano}
    (h : fromCardinalNatural a = fromCardinalNatural b) : a = b := by
  cases CardinalNatural.Peano.trichotomy_or a b with
  | inl hlt =>
      have hlt' := (fromCardinalNatural_lt_iff a b).mpr hlt
      rw [h] at hlt'
      exact False.elim (not_lt_self _ hlt')
  | inr h' =>
      cases h' with
      | inl heq => exact heq
      | inr hgt =>
          have hgt' := (fromCardinalNatural_lt_iff b a).mpr hgt
          rw [← h] at hgt'
          exact False.elim (not_lt_self _ hgt')

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

theorem add_subtract_cancel (a b : Peano) : a + b - b = a := by
  induction b with
  | zero =>
    rw [add_zero, subtract_zero]
  | positive n =>
    induction n with
    | one =>
      rw [add_positive_one, subtract_positive_one, predecessor_successor]
    | successor n ih =>
      rw [add_positive_successor, subtract_positive_successor]
      rw [successor_subtract]
      rw [predecessor_successor]
      exact ih
  | negative n =>
    induction n with
    | one =>
      rw [add_negative_one, subtract_negative_one, successor_predecessor]
    | successor n ih =>
      rw [add_negative_successor, subtract_negative_successor]
      rw [predecessor_subtract]
      rw [successor_predecessor]
      exact ih

/-- Subtracting the left addend from a sum recovers the right addend. -/
theorem add_subtract_cancel_left (a b : Peano) : a + b - a = b := by
  rw [add_commutative, add_subtract_cancel]

/-- Addition cancels on the left. -/
theorem add_left_cancel (b q c : Peano) (h : b + q = b + c) : q = c := by
  calc
    q = b + q - b := (add_subtract_cancel_left b q).symm
    _ = b + c - b := by rw [h]
    _ = c := add_subtract_cancel_left b c

theorem subtract_add_cancel (a b : Peano) : a - b + b = a := by
  induction b with
  | zero =>
    rw [subtract_zero, add_zero]
  | positive n =>
    induction n with
    | one =>
      rw [subtract_positive_one, add_positive_one, successor_predecessor]
    | successor n ih =>
      rw [subtract_positive_successor, add_positive_successor]
      rw [predecessor_add]
      rw [successor_predecessor]
      exact ih
  | negative n =>
    induction n with
    | one =>
      rw [subtract_negative_one, add_negative_one, predecessor_successor]
    | successor n ih =>
      rw [subtract_negative_successor, add_negative_successor]
      rw [successor_add]
      rw [predecessor_successor]
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

theorem le_of_not_le {a b : Peano} (h : ¬ a ≤ b) : b ≤ a := by
  cases trichotomy_or a b with
  | inl hlt => exact absurd (Or.inl hlt : a ≤ b) h
  | inr h' =>
    cases h' with
    | inl heq => exact absurd (Or.inr heq : a ≤ b) h
    | inr hlt => exact Or.inl hlt

theorem lt_of_not_lt_ne {a b : Peano} (hnlt : ¬ a < b) (hne : a ≠ b) : b < a := by
  cases trichotomy_or a b with
  | inl hlt => exact absurd hlt hnlt
  | inr h' =>
    cases h' with
    | inl heq => exact absurd heq hne
    | inr hlt => exact hlt

theorem ne_of_not_le {a b : Peano} (h : ¬ a ≤ b) : a ≠ b :=
  fun heq => h (Or.inr heq)

/-- Result of comparing two Peano numbers, packaged with a proof of the relationship. -/
inductive Comparison (a b : Peano) where
  | less : a < b → Comparison a b
  | equal : a = b → Comparison a b
  | greater : b < a → Comparison a b

/-- Compare two Peano numbers, returning less, equal, or greater together with a proof. -/
def compare (a b : Peano) : Comparison a b :=
  match a, b with
  | zero, zero => Comparison.equal rfl
  | zero, positive _ => Comparison.less LessThan.zero_less_than_positive
  | zero, negative _ => Comparison.greater LessThan.negative_less_than_zero
  | positive _, zero => Comparison.greater LessThan.zero_less_than_positive
  | negative _, zero => Comparison.less LessThan.negative_less_than_zero
  | positive _, negative _ => Comparison.greater LessThan.negative_less_than_positive
  | negative _, positive _ => Comparison.less LessThan.negative_less_than_positive
  | positive n, positive m =>
    match OrdinalNatural.Peano.compare n m with
    | OrdinalNatural.Peano.Comparison.less h =>
      Comparison.less (LessThan.positive_less_than_positive h)
    | OrdinalNatural.Peano.Comparison.equal h =>
      Comparison.equal (congrArg positive h)
    | OrdinalNatural.Peano.Comparison.greater h =>
      Comparison.greater (LessThan.positive_less_than_positive h)
  | negative n, negative m =>
    match OrdinalNatural.Peano.compare n m with
    | OrdinalNatural.Peano.Comparison.less h =>
      Comparison.greater (LessThan.negative_less_than_negative h)
    | OrdinalNatural.Peano.Comparison.equal h =>
      Comparison.equal (congrArg negative h)
    | OrdinalNatural.Peano.Comparison.greater h =>
      Comparison.less (LessThan.negative_less_than_negative h)

@[simp]
theorem add_successor (a b : Peano) : a + successor b = successor (a + b) := by
  cases b with
  | zero =>
    have h1 : successor zero = positive OrdinalNatural.Peano.one := rfl
    rw [h1, add_positive_one, add_zero]
  | positive n =>
    cases n with
    | one =>
      have h1 : successor (positive OrdinalNatural.Peano.one) = positive (OrdinalNatural.Peano.successor OrdinalNatural.Peano.one) := rfl
      rw [h1, add_positive_successor, add_positive_one]
    | successor n =>
      have h1 : successor (positive (OrdinalNatural.Peano.successor n)) = positive (OrdinalNatural.Peano.successor (OrdinalNatural.Peano.successor n)) := rfl
      rw [h1, add_positive_successor, add_positive_successor]
  | negative n =>
    cases n with
    | one =>
      have h1 : successor (negative OrdinalNatural.Peano.one) = zero := rfl
      rw [h1, add_zero, add_negative_one, successor_predecessor]
    | successor n =>
      have h1 : successor (negative (OrdinalNatural.Peano.successor n)) = negative n := rfl
      rw [h1, add_negative_successor, successor_predecessor]

@[simp]
theorem add_predecessor (a b : Peano) : a + predecessor b = predecessor (a + b) := by
  cases b with
  | zero =>
    have h1 : predecessor zero = negative OrdinalNatural.Peano.one := rfl
    rw [h1, add_negative_one, add_zero]
  | positive n =>
    cases n with
    | one =>
      have h1 : predecessor (positive OrdinalNatural.Peano.one) = zero := rfl
      rw [h1, add_zero, add_positive_one, predecessor_successor]
    | successor n =>
      have h1 : predecessor (positive (OrdinalNatural.Peano.successor n)) = positive n := rfl
      rw [h1, add_positive_successor, predecessor_successor]
  | negative n =>
    cases n with
    | one =>
      have h1 : predecessor (negative OrdinalNatural.Peano.one) = negative (OrdinalNatural.Peano.successor OrdinalNatural.Peano.one) := rfl
      rw [h1, add_negative_successor, add_negative_one]
    | successor n =>
      have h1 : predecessor (negative (OrdinalNatural.Peano.successor n)) = negative (OrdinalNatural.Peano.successor (OrdinalNatural.Peano.successor n)) := rfl
      rw [h1, add_negative_successor, add_negative_successor]

theorem add_associative (a b c : Peano) : a + b + c = a + (b + c) := by
  induction c with
  | zero =>
    rw [add_zero, add_zero]
  | positive n =>
    induction n with
    | one =>
      rw [add_positive_one, add_positive_one]
      rw [add_successor]
    | successor n ih =>
      rw [add_positive_successor, add_positive_successor]
      rw [add_successor, ih]
  | negative n =>
    induction n with
    | one =>
      rw [add_negative_one, add_negative_one]
      rw [add_predecessor]
    | successor n ih =>
      rw [add_negative_successor, add_negative_successor]
      rw [add_predecessor, ih]

@[simp]
theorem add_negate_self (a : Peano) : a + -a = zero := by
  cases a with
  | zero =>
    have h1 : -zero = zero := rfl
    rw [h1, add_zero]
  | positive n =>
    induction n with
    | one =>
      have h1 : -(positive OrdinalNatural.Peano.one) = negative OrdinalNatural.Peano.one := rfl
      rw [h1, add_negative_one]
      rfl
    | successor n ih =>
      have h1 : -(positive n.successor) = negative n.successor := rfl
      rw [h1, add_negative_successor]
      have h2 : positive n.successor + negative n = successor (positive n + negative n) := by
        have h_succ : positive n.successor = successor (positive n) := rfl
        rw [h_succ, successor_add]
      rw [h2, predecessor_successor]
      have h3 : -(positive n) = negative n := rfl
      have h4 : positive n + negative n = positive n + -(positive n) := by rw [h3]
      rw [h4]
      exact ih
  | negative n =>
    induction n with
    | one =>
      have h1 : -(negative OrdinalNatural.Peano.one) = positive OrdinalNatural.Peano.one := rfl
      rw [h1, add_positive_one]
      rfl
    | successor n ih =>
      have h1 : -(negative n.successor) = positive n.successor := rfl
      rw [h1, add_positive_successor]
      have h2 : negative n.successor + positive n = predecessor (negative n + positive n) := by
        have h_pred : negative n.successor = predecessor (negative n) := rfl
        rw [h_pred, predecessor_add]
      rw [h2, successor_predecessor]
      have h3 : -(negative n) = positive n := rfl
      have h4 : negative n + positive n = negative n + -(negative n) := by rw [h3]
      rw [h4]
      exact ih

theorem fromCardinalNatural_add (a b : CardinalNatural.Peano) :
    fromCardinalNatural (a + b) = fromCardinalNatural a + fromCardinalNatural b := by
  induction b with
  | zero =>
      change fromCardinalNatural (a + CardinalNatural.Peano.zero) =
        fromCardinalNatural a + fromCardinalNatural CardinalNatural.Peano.zero
      rw [CardinalNatural.Peano.add_zero]
      change fromCardinalNatural a = fromCardinalNatural a + zero
      rw [add_zero]
  | successor b ih =>
      rw [CardinalNatural.Peano.add_successor]
      rw [fromCardinalNatural_successor (a + b)]
      rw [ih]
      rw [fromCardinalNatural_successor b]
      rw [add_successor]

theorem fromCardinalNatural_subtract (a b : CardinalNatural.Peano)
    (h : b ≤ a) :
    fromCardinalNatural (CardinalNatural.Peano.subtract a b h) =
      fromCardinalNatural a + -(fromCardinalNatural b) := by
  have h_add :
      fromCardinalNatural (CardinalNatural.Peano.subtract a b h) + fromCardinalNatural b =
        fromCardinalNatural a := by
    rw [← fromCardinalNatural_add, CardinalNatural.Peano.subtract_add_cancel a b h]
  have h0 :
      fromCardinalNatural (CardinalNatural.Peano.subtract a b h) =
        fromCardinalNatural (CardinalNatural.Peano.subtract a b h) + zero :=
    (add_zero _).symm
  have h1 :
      fromCardinalNatural (CardinalNatural.Peano.subtract a b h) + zero =
        fromCardinalNatural (CardinalNatural.Peano.subtract a b h) +
          (fromCardinalNatural b + -(fromCardinalNatural b)) := by
    rw [add_negate_self]
  have h2 :
      fromCardinalNatural (CardinalNatural.Peano.subtract a b h) +
          (fromCardinalNatural b + -(fromCardinalNatural b)) =
        (fromCardinalNatural (CardinalNatural.Peano.subtract a b h) +
          fromCardinalNatural b) + -(fromCardinalNatural b) := by
    rw [← add_associative]
  exact h0.trans (h1.trans (h2.trans (by rw [h_add])))

theorem eq_add_negate_of_add_eq {x y z : Peano} (h : x + y = z) : x = z + -y := by
  have h0 : x = x + zero := (add_zero x).symm
  have h1 : x + zero = x + (y + -y) := by rw [add_negate_self]
  have h2 : x + (y + -y) = (x + y) + -y := by rw [← add_associative]
  exact h0.trans (h1.trans (h2.trans (by rw [h])))

@[simp]
theorem negate_add_self (a : Peano) : -a + a = zero := by
  rw [add_commutative, add_negate_self]

@[simp]
theorem multiply_positive_one (a : Peano) : a * positive OrdinalNatural.Peano.one = a := by
  have h : a * positive OrdinalNatural.Peano.one = multiply a (positive OrdinalNatural.Peano.one) := rfl
  rw [h]
  rw [multiply.eq_def]

@[simp]
theorem multiply_positive_successor (a : Peano) (n : OrdinalNatural.Peano) : a * positive n.successor = a * positive n + a := by
  have h1 : a * positive n.successor = multiply a (positive n.successor) := rfl
  have h2 : a * positive n = multiply a (positive n) := rfl
  rw [h1, h2]
  rw [multiply.eq_def]

@[simp]
theorem multiply_negative_one (a : Peano) : a * negative OrdinalNatural.Peano.one = -a := by
  have h : a * negative OrdinalNatural.Peano.one = multiply a (negative OrdinalNatural.Peano.one) := rfl
  rw [h]
  rw [multiply.eq_def]

@[simp]
theorem multiply_negative_successor (a : Peano) (n : OrdinalNatural.Peano) : a * negative n.successor = a * negative n - a := by
  have h1 : a * negative n.successor = multiply a (negative n.successor) := rfl
  have h2 : a * negative n = multiply a (negative n) := rfl
  rw [h1, h2]
  rw [multiply.eq_def]

@[simp]
theorem multiply_zero (a : Peano) : a * zero = zero := by
  have h : a * zero = multiply a zero := rfl
  rw [h]
  rw [multiply.eq_def]

@[simp]
theorem zero_multiply (a : Peano) : zero * a = zero := by
  cases a with
  | zero =>
    rw [multiply_zero]
  | positive n =>
    induction n with
    | one =>
      rw [multiply_positive_one]
    | successor n ih =>
      rw [multiply_positive_successor]
      rw [ih]
      rw [add_zero]
  | negative n =>
    induction n with
    | one =>
      rw [multiply_negative_one]
      have h1 : -zero = zero := rfl
      rw [h1]
    | successor n ih =>
      rw [multiply_negative_successor]
      rw [ih]
      rw [subtract_zero]

@[simp]
theorem multiply_successor (a b : Peano) : a * successor b = a * b + a := by
  cases b with
  | zero =>
    have h1 : successor zero = positive OrdinalNatural.Peano.one := rfl
    rw [h1, multiply_positive_one, multiply_zero, zero_add]
  | positive n =>
    cases n with
    | one =>
      have h1 : successor (positive OrdinalNatural.Peano.one) = positive (OrdinalNatural.Peano.successor OrdinalNatural.Peano.one) := rfl
      rw [h1, multiply_positive_successor]
    | successor n =>
      have h1 : successor (positive (OrdinalNatural.Peano.successor n)) = positive (OrdinalNatural.Peano.successor (OrdinalNatural.Peano.successor n)) := rfl
      rw [h1, multiply_positive_successor]
  | negative n =>
    cases n with
    | one =>
      have h1 : successor (negative OrdinalNatural.Peano.one) = zero := rfl
      rw [h1, multiply_zero, multiply_negative_one]
      rw [negate_add_self]
    | successor n =>
      have h1 : successor (negative (OrdinalNatural.Peano.successor n)) = negative n := rfl
      rw [h1, multiply_negative_successor]
      have hs : a * negative n - a + a = a * negative n := subtract_add_cancel (a * negative n) a
      rw [hs]

theorem fromCardinalNatural_multiply (a b : CardinalNatural.Peano) :
    fromCardinalNatural (a * b) = fromCardinalNatural a * fromCardinalNatural b := by
  induction b with
  | zero =>
      change fromCardinalNatural (a * CardinalNatural.Peano.zero) =
        fromCardinalNatural a * fromCardinalNatural CardinalNatural.Peano.zero
      rw [CardinalNatural.Peano.multiply_zero]
      change fromCardinalNatural CardinalNatural.Peano.zero =
        fromCardinalNatural a * zero
      rw [multiply_zero]
      rfl
  | successor b ih =>
      rw [CardinalNatural.Peano.multiply_successor, fromCardinalNatural_add, ih,
        fromCardinalNatural_successor, multiply_successor]

theorem subtract_eq_add_negate (a b : Peano) : a - b = a + -b := by
  induction b with
  | zero =>
    have h1 : -zero = zero := rfl
    rw [h1, add_zero, subtract_zero]
  | positive n =>
    induction n with
    | one =>
      have h1 : -(positive OrdinalNatural.Peano.one) = negative OrdinalNatural.Peano.one := rfl
      rw [h1, subtract_positive_one, add_negative_one]
    | successor n ih =>
      have h1 : -(positive n.successor) = negative n.successor := rfl
      rw [h1, subtract_positive_successor, add_negative_successor]
      have h2 : -(positive n) = negative n := rfl
      have h3 : a - positive n = a + negative n := by
        rw [← h2]
        exact ih
      rw [h3]
  | negative n =>
    induction n with
    | one =>
      have h1 : -(negative OrdinalNatural.Peano.one) = positive OrdinalNatural.Peano.one := rfl
      rw [h1, subtract_negative_one, add_positive_one]
    | successor n ih =>
      have h1 : -(negative n.successor) = positive n.successor := rfl
      rw [h1, subtract_negative_successor, add_positive_successor]
      have h2 : -(negative n) = positive n := rfl
      have h3 : a - negative n = a + positive n := by
        rw [← h2]
        exact ih
      rw [h3]

@[simp]
theorem zero_subtract (a : Peano) : zero - a = -a := by
  rw [subtract_eq_add_negate, zero_add]

@[simp]
theorem subtract_self (a : Peano) : a - a = zero := by
  rw [subtract_eq_add_negate, add_negate_self]

@[simp]
theorem multiply_predecessor (a b : Peano) : a * predecessor b = a * b - a := by
  cases b with
  | zero =>
    have h1 : predecessor zero = negative OrdinalNatural.Peano.one := rfl
    rw [h1, multiply_negative_one, multiply_zero]
    have h2 : zero - a = -a := zero_subtract a
    rw [h2]
  | positive n =>
    cases n with
    | one =>
      have h1 : predecessor (positive OrdinalNatural.Peano.one) = zero := rfl
      rw [h1, multiply_zero, multiply_positive_one]
      rw [subtract_self]
    | successor n =>
      have h1 : predecessor (positive (OrdinalNatural.Peano.successor n)) = positive n := rfl
      rw [h1, multiply_positive_successor]
      have hs : a * positive n + a - a = a * positive n := add_subtract_cancel (a * positive n) a
      rw [hs]
  | negative n =>
    cases n with
    | one =>
      have h1 : predecessor (negative OrdinalNatural.Peano.one) = negative (OrdinalNatural.Peano.successor OrdinalNatural.Peano.one) := rfl
      rw [h1, multiply_negative_successor]
    | successor n =>
      have h1 : predecessor (negative (OrdinalNatural.Peano.successor n)) = negative (OrdinalNatural.Peano.successor (OrdinalNatural.Peano.successor n)) := rfl
      rw [h1, multiply_negative_successor]

def Divisible (a b : Peano) : Prop := b ≠ zero ∧ ∃ c, b * c = a

def isDivisible (a b : Peano) : Bool :=
  match a, b with
  | _, zero => false
  | zero, _ => true
  | positive a', positive b' => OrdinalNatural.Peano.isDivisible a' b'
  | negative a', positive b' => OrdinalNatural.Peano.isDivisible a' b'
  | positive a', negative b' => OrdinalNatural.Peano.isDivisible a' b'
  | negative a', negative b' => OrdinalNatural.Peano.isDivisible a' b'

@[simp]
theorem add_positive_positive (b c : OrdinalNatural.Peano) : positive b + positive c = positive (b + c) := by
  induction c with
  | one => rw [add_positive_one]; rfl
  | successor c_ih ih => rw [add_positive_successor, ih]; rfl

theorem add_negative_negative (b c : OrdinalNatural.Peano) : negative b + negative c = negative (b + c) := by
  induction c with
  | one => rw [add_negative_one]; rfl
  | successor c_ih ih => rw [add_negative_successor, ih]; rfl

theorem multiply_positive_positive (b c : OrdinalNatural.Peano) : positive b * positive c = positive (b * c) := by
  induction c with
  | one => rw [multiply_positive_one]; rfl
  | successor c_ih ih => rw [multiply_positive_successor, ih, add_positive_positive]; rfl

theorem multiply_positive_negative (b c : OrdinalNatural.Peano) : positive b * negative c = negative (b * c) := by
  induction c with
  | one => rw [multiply_negative_one]; rfl
  | successor c_ih ih =>
    rw [multiply_negative_successor, ih, subtract_eq_add_negate]
    have h1 : -positive b = negative b := rfl
    rw [h1, add_negative_negative]
    rfl

theorem multiply_negative_positive (b c : OrdinalNatural.Peano) : negative b * positive c = negative (b * c) := by
  induction c with
  | one => rw [multiply_positive_one]; rfl
  | successor c_ih ih => rw [multiply_positive_successor, ih, add_negative_negative]; rfl

theorem multiply_negative_negative (b c : OrdinalNatural.Peano) : negative b * negative c = positive (b * c) := by
  induction c with
  | one => rw [multiply_negative_one]; rfl
  | successor c_ih ih =>
    rw [multiply_negative_successor, ih, subtract_eq_add_negate]
    have h1 : -negative b = positive b := rfl
    rw [h1, add_positive_positive]
    rfl

theorem isDivisible_correct (a b : Peano) : Divisible a b ↔ isDivisible a b := by
  unfold Divisible isDivisible
  apply Iff.intro
  · intro h
    rcases h with ⟨h_ne_zero, c, hc_eq⟩
    cases a with
    | zero =>
      cases b with
      | zero => exact False.elim (h_ne_zero rfl)
      | positive b' => rfl
      | negative b' => rfl
    | positive a' =>
      cases b with
      | zero => exact False.elim (h_ne_zero rfl)
      | positive b' =>
        cases c with
        | zero =>
          have h_eq : positive b' * zero = zero := multiply_zero (positive b')
          rw [h_eq] at hc_eq
          cases hc_eq
        | positive c' =>
          have hc_eq' : b' * c' = a' := by
            have h_eq : positive b' * positive c' = positive (b' * c') := multiply_positive_positive b' c'
            rw [h_eq] at hc_eq
            injection hc_eq
          exact (OrdinalNatural.Peano.isDivisible_correct a' b').mp ⟨c', hc_eq'⟩
        | negative c' =>
          have h_eq : positive b' * negative c' = negative (b' * c') := multiply_positive_negative b' c'
          rw [h_eq] at hc_eq
          cases hc_eq
      | negative b' =>
        cases c with
        | zero =>
          have h_eq : negative b' * zero = zero := multiply_zero (negative b')
          rw [h_eq] at hc_eq
          cases hc_eq
        | positive c' =>
          have h_eq : negative b' * positive c' = negative (b' * c') := multiply_negative_positive b' c'
          rw [h_eq] at hc_eq
          cases hc_eq
        | negative c' =>
          have hc_eq' : b' * c' = a' := by
            have h_eq : negative b' * negative c' = positive (b' * c') := multiply_negative_negative b' c'
            rw [h_eq] at hc_eq
            injection hc_eq
          exact (OrdinalNatural.Peano.isDivisible_correct a' b').mp ⟨c', hc_eq'⟩
    | negative a' =>
      cases b with
      | zero => exact False.elim (h_ne_zero rfl)
      | positive b' =>
        cases c with
        | zero =>
          have h_eq : positive b' * zero = zero := multiply_zero (positive b')
          rw [h_eq] at hc_eq
          cases hc_eq
        | positive c' =>
          have h_eq : positive b' * positive c' = positive (b' * c') := multiply_positive_positive b' c'
          rw [h_eq] at hc_eq
          cases hc_eq
        | negative c' =>
          have hc_eq' : b' * c' = a' := by
            have h_eq : positive b' * negative c' = negative (b' * c') := multiply_positive_negative b' c'
            rw [h_eq] at hc_eq
            injection hc_eq
          exact (OrdinalNatural.Peano.isDivisible_correct a' b').mp ⟨c', hc_eq'⟩
      | negative b' =>
        cases c with
        | zero =>
          have h_eq : negative b' * zero = zero := multiply_zero (negative b')
          rw [h_eq] at hc_eq
          cases hc_eq
        | positive c' =>
          have hc_eq' : b' * c' = a' := by
            have h_eq : negative b' * positive c' = negative (b' * c') := multiply_negative_positive b' c'
            rw [h_eq] at hc_eq
            injection hc_eq
          exact (OrdinalNatural.Peano.isDivisible_correct a' b').mp ⟨c', hc_eq'⟩
        | negative c' =>
          have h_eq : negative b' * negative c' = positive (b' * c') := multiply_negative_negative b' c'
          rw [h_eq] at hc_eq
          cases hc_eq

  · intro h
    cases a with
    | zero =>
      cases b with
      | zero => cases h
      | positive b' =>
        apply And.intro
        · intro h_eq; cases h_eq
        · exact ⟨zero, multiply_zero (positive b')⟩
      | negative b' =>
        apply And.intro
        · intro h_eq; cases h_eq
        · exact ⟨zero, multiply_zero (negative b')⟩
    | positive a' =>
      cases b with
      | zero => cases h
      | positive b' =>
        have ⟨c, hc_eq⟩ := (OrdinalNatural.Peano.isDivisible_correct a' b').mpr h
        apply And.intro
        · intro h_eq; cases h_eq
        · exact ⟨positive c, by rw [multiply_positive_positive, hc_eq]⟩
      | negative b' =>
        have ⟨c, hc_eq⟩ := (OrdinalNatural.Peano.isDivisible_correct a' b').mpr h
        apply And.intro
        · intro h_eq; cases h_eq
        · exact ⟨negative c, by rw [multiply_negative_negative, hc_eq]⟩
    | negative a' =>
      cases b with
      | zero => cases h
      | positive b' =>
        have ⟨c, hc_eq⟩ := (OrdinalNatural.Peano.isDivisible_correct a' b').mpr h
        apply And.intro
        · intro h_eq; cases h_eq
        · exact ⟨negative c, by rw [multiply_positive_negative, hc_eq]⟩
      | negative b' =>
        have ⟨c, hc_eq⟩ := (OrdinalNatural.Peano.isDivisible_correct a' b').mpr h
        apply And.intro
        · intro h_eq; cases h_eq
        · exact ⟨positive c, by rw [multiply_negative_positive, hc_eq]⟩

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
    | one => rw [add_positive_one, toInt_successor]; simp [toInt, ZeroMath.Numbers.OrdinalNatural.Peano.toNat]
    | successor n ih =>
      rw [add_positive_successor, toInt_successor, ih]
      simp [toInt, ZeroMath.Numbers.OrdinalNatural.Peano.toNat]
      omega
  | negative n =>
    induction n with
    | one =>
      rw [add_negative_one, toInt_predecessor]
      simp [toInt, ZeroMath.Numbers.OrdinalNatural.Peano.toNat]
      omega
    | successor n ih =>
      rw [add_negative_successor, toInt_predecessor, ih]
      simp [toInt, ZeroMath.Numbers.OrdinalNatural.Peano.toNat]
      omega

@[simp]
theorem toInt_subtract (a b : Peano) : (a - b).toInt = a.toInt - b.toInt := by
  rw [subtract_eq_add_negate, toInt_add, toInt_negate]
  omega

/-- Strict order is reflected by `toInt`. -/
theorem toInt_lt_of_lt {a b : Peano} (h : a < b) : a.toInt < b.toInt := by
  cases h with
  | @negative_less_than_zero n =>
    simp only [toInt]
    exact Int.neg_neg_of_pos
      (Int.natCast_pos.mpr (Nat.pos_of_ne_zero (OrdinalNatural.Peano.toNat_ne_zero n)))
  | @zero_less_than_positive n =>
    simp only [toInt]
    exact Int.natCast_pos.mpr (Nat.pos_of_ne_zero (OrdinalNatural.Peano.toNat_ne_zero n))
  | @negative_less_than_positive n m =>
    simp only [toInt]
    have hn := OrdinalNatural.Peano.toNat_ne_zero n
    have hm := OrdinalNatural.Peano.toNat_ne_zero m
    omega
  | positive_less_than_positive hlt =>
    simp only [toInt]
    exact Int.ofNat_lt.mpr (OrdinalNatural.Peano.toNat_lt_of_lt hlt)
  | negative_less_than_negative hlt =>
    simp only [toInt]
    have hnat := OrdinalNatural.Peano.toNat_lt_of_lt hlt
    omega

/-- Non-strict order is reflected by `toInt`. -/
theorem toInt_le_of_le {a b : Peano} (h : a ≤ b) : a.toInt ≤ b.toInt := by
  cases h with
  | inl hlt => exact Int.le_of_lt (toInt_lt_of_lt hlt)
  | inr heq => exact heq ▸ Int.le_refl _

@[simp]
theorem toInt_multiply (a b : Peano) : (a * b).toInt = a.toInt * b.toInt := by
  induction b with
  | zero => rw [multiply_zero]; simp [toInt]
  | positive n =>
    induction n with
    | one => rw [multiply_positive_one]; simp [toInt, ZeroMath.Numbers.OrdinalNatural.Peano.toNat]
    | successor n ih =>
      rw [multiply_positive_successor, toInt_add, ih]
      simp [toInt, ZeroMath.Numbers.OrdinalNatural.Peano.toNat]
      rw [Int.mul_add]
      simp [Int.mul_one]
  | negative n =>
    induction n with
    | one =>
      rw [multiply_negative_one, toInt_negate]
      simp [toInt, ZeroMath.Numbers.OrdinalNatural.Peano.toNat]
    | successor n ih =>
      rw [multiply_negative_successor, toInt_subtract, ih]
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

theorem multiply_left_cancel (b q c : Peano) (hb : b ≠ zero) (h : b * q = b * c) : q = c := by
  apply toInt_injective
  have hi : (b * q).toInt = (b * c).toInt := by rw [h]
  rw [toInt_multiply, toInt_multiply] at hi
  exact Int.eq_of_mul_eq_mul_left (toInt_ne_zero_of_ne_zero hb) hi

def absoluteNat : Peano → Nat
  | positive n => n.toNat
  | zero => 0
  | negative n => n.toNat

@[simp]
theorem absoluteNat_eq_zero_iff (a : Peano) : absoluteNat a = 0 ↔ a = zero := by
  constructor
  · intro h
    cases a with
    | zero => rfl
    | positive n =>
      simp [absoluteNat] at h
      exact False.elim (OrdinalNatural.Peano.toNat_ne_zero n h)
    | negative n =>
      simp [absoluteNat] at h
      exact False.elim (OrdinalNatural.Peano.toNat_ne_zero n h)
  · intro h
    subst h
    rfl

theorem absoluteNat_le_one_eq (c : Peano)
    (hpos : c ≠ positive OrdinalNatural.Peano.one)
    (hneg : c ≠ negative OrdinalNatural.Peano.one)
    (hle : absoluteNat c ≤ absoluteNat (positive OrdinalNatural.Peano.one)) : c = zero := by
  apply (absoluteNat_eq_zero_iff c).mp
  cases c with
  | zero => rfl
  | positive n =>
    exfalso
    apply hpos
    apply congrArg positive
    apply ordinal_toNat_injective
    simp [absoluteNat, OrdinalNatural.Peano.toNat] at hle ⊢
    have hn := OrdinalNatural.Peano.toNat_ne_zero n
    omega
  | negative n =>
    exfalso
    apply hneg
    apply congrArg negative
    apply ordinal_toNat_injective
    simp [absoluteNat, OrdinalNatural.Peano.toNat] at hle ⊢
    have hn := OrdinalNatural.Peano.toNat_ne_zero n
    omega

theorem absoluteNat_le_of_le_successor_of_ne_candidates (c : Peano) (n : OrdinalNatural.Peano)
    (hpos : c ≠ positive n.successor)
    (hneg : c ≠ negative n.successor)
    (hle : absoluteNat c ≤ absoluteNat (positive n.successor)) : absoluteNat c ≤ absoluteNat (positive n) := by
  cases c with
  | zero => simp [absoluteNat]
  | positive m =>
    simp [absoluteNat, OrdinalNatural.Peano.toNat] at hle ⊢
    apply Nat.le_of_lt_succ
    apply Nat.lt_of_le_of_ne hle
    intro heq
    apply hpos
    apply congrArg positive
    apply ordinal_toNat_injective
    simp [OrdinalNatural.Peano.toNat]
    exact heq
  | negative m =>
    simp [absoluteNat, OrdinalNatural.Peano.toNat] at hle ⊢
    apply Nat.le_of_lt_succ
    apply Nat.lt_of_le_of_ne hle
    intro heq
    apply hneg
    apply congrArg negative
    apply ordinal_toNat_injective
    simp [OrdinalNatural.Peano.toNat]
    exact heq

theorem absoluteNat_toInt (a : Peano) : a.toInt.natAbs = absoluteNat a := by
  cases a with
  | zero => rfl
  | positive n => simp [toInt, absoluteNat]
  | negative n => simp [toInt, absoluteNat, Int.natAbs_neg]

theorem absoluteNat_positive_of_ne_zero {a : Peano} (h : a ≠ zero) : 0 < absoluteNat a := by
  cases a with
  | zero => contradiction
  | positive n =>
    simp [absoluteNat]
    exact Nat.pos_of_ne_zero (OrdinalNatural.Peano.toNat_ne_zero n)
  | negative n =>
    simp [absoluteNat]
    exact Nat.pos_of_ne_zero (OrdinalNatural.Peano.toNat_ne_zero n)

/-- Absolute difference `larger - smaller` is a positive natural when
`smaller < larger`. -/
theorem absoluteNat_subtract_positive_of_lt {a b : Peano} (h : a < b) : 0 < absoluteNat (b - a) := by
  rw [← absoluteNat_toInt, toInt_subtract]
  have hab : a.toInt < b.toInt := toInt_lt_of_lt h
  have hne : b.toInt - a.toInt ≠ 0 := by omega
  exact Int.natAbs_pos.mpr hne

theorem absoluteNat_subtract_ne_zero_of_lt {a b : Peano} (h : a < b) :
    absoluteNat (b - a) ≠ 0 :=
  Nat.pos_iff_ne_zero.mp (absoluteNat_subtract_positive_of_lt h)

theorem not_le_of_gt {a b : Peano} (h : b < a) : ¬ a ≤ b := by
  intro hle
  cases hle with
  | inl hlt => exact not_lt_of_lt h hlt
  | inr heq => exact (ne_of_lt h) heq.symm

theorem lt_successor (x : Peano) : x < successor x := by
  cases x with
  | zero => exact LessThan.zero_less_than_positive
  | positive n =>
    exact LessThan.positive_less_than_positive OrdinalNatural.Peano.LessThan.base
  | negative n =>
    cases n with
    | one => exact LessThan.negative_less_than_zero
    | successor n' =>
      exact LessThan.negative_less_than_negative OrdinalNatural.Peano.LessThan.base

theorem predecessor_lt (x : Peano) : predecessor x < x := by
  have h := lt_successor (predecessor x)
  rwa [successor_predecessor x] at h

theorem lt_add_of_positive (x : Peano) (d : OrdinalNatural.Peano) :
    x < x + positive d := by
  induction d with
  | one =>
    rw [add_positive_one]
    exact lt_successor x
  | successor d ih =>
    rw [add_positive_successor]
    exact lt_trans ih (lt_successor _)

theorem add_negative_lt (x : Peano) (d : OrdinalNatural.Peano) :
    x + negative d < x := by
  induction d with
  | one =>
    rw [add_negative_one]
    exact predecessor_lt x
  | successor d ih =>
    rw [add_negative_successor]
    exact lt_trans (predecessor_lt _) ih

theorem lt_of_lt_of_le {a b c : Peano} (h1 : a < b) (h2 : b ≤ c) : a < c := by
  cases h2 with
  | inl hlt => exact lt_trans h1 hlt
  | inr heq => exact heq ▸ h1

theorem lt_of_le_of_lt {a b c : Peano} (h1 : a ≤ b) (h2 : b < c) : a < c := by
  cases h1 with
  | inl hlt => exact lt_trans hlt h2
  | inr heq => exact heq ▸ h2

/-- A strictly positive integer is `positive` of its ordinal magnitude. -/
theorem eq_positive_of_positive {a : Peano} (h : zero < a) :
    a = positive (toOrdinalNatural a h) := by
  match a, h with
  | positive n, _ => rfl

theorem absoluteNat_le_absoluteNat_multiply_left (x y : Peano) (hy : y ≠ zero) : absoluteNat x ≤ absoluteNat (y * x) := by
  rw [← absoluteNat_toInt x, ← absoluteNat_toInt (y * x), toInt_multiply, Int.natAbs_mul]
  rw [absoluteNat_toInt y, absoluteNat_toInt x]
  exact Nat.le_mul_of_pos_left (absoluteNat x) (absoluteNat_positive_of_ne_zero hy)

def fromNat : Nat → Peano
  | 0 => zero
  | n + 1 => positive (OrdinalNatural.Peano.fromNat (n + 1) (Nat.succ_ne_zero n))

@[simp]
theorem toInt_fromNat (n : Nat) : (fromNat n).toInt = n := by
  cases n with
  | zero => rfl
  | succ n =>
    unfold fromNat toInt
    simp [OrdinalNatural.Peano.toNat_fromNat]

theorem fromNat_toInt (x : Peano) (h : zero ≤ x) : fromNat (x.toInt.toNat) = x := by
  cases x with
  | negative n =>
      cases h with
      | inl hlt => cases hlt
      | inr heq => cases heq
  | zero =>
      simp [toInt, fromNat]
  | positive n =>
      simp [toInt]
      cases h_nat : n.toNat with
      | zero =>
          have hne := OrdinalNatural.Peano.toNat_ne_zero n
          rw [h_nat] at hne
          contradiction
      | succ k =>
          have h_nz : k + 1 ≠ 0 := Nat.succ_ne_zero k
          have h_eq : OrdinalNatural.Peano.fromNat (k + 1) h_nz = n := by
            apply OrdinalNatural.Peano.fromNat_toNat_helper
            exact h_nat
          rw [← h_eq]
          rfl

theorem fromNat_toNat (x : Peano) (h : zero ≤ x) : fromNat (toNat x h) = x := by
  cases x with
  | negative n =>
      cases h with
      | inl hlt => cases hlt
      | inr heq => cases heq
  | zero =>
      unfold toNat toCardinalNatural fromNat
      rfl
  | positive n =>
      simp [toNat, toCardinalNatural]
      -- simp applies fromOrdinal_toNat (marked @[simp]), so we have fromNat n.toNat = positive n
      cases h_nat : n.toNat with
      | zero =>
          have hne := OrdinalNatural.Peano.toNat_ne_zero n
          rw [h_nat] at hne
          contradiction
      | succ k =>
          have h_nz : k + 1 ≠ 0 := Nat.succ_ne_zero k
          have h_eq : OrdinalNatural.Peano.fromNat (k + 1) h_nz = n := by
            apply OrdinalNatural.Peano.fromNat_toNat_helper
            exact h_nat
          rw [← h_eq]
          rfl

theorem toNat_fromNat (x : Nat) : ∃ h, toNat (fromNat x) h = x := by
  cases x with
  | zero =>
    exists Or.inr rfl
  | succ n =>
    have h_le : zero ≤ fromNat (n + 1) := Or.inl LessThan.zero_less_than_positive
    exists h_le
    simp [fromNat, toNat, toCardinalNatural]

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

theorem multiply_add (a b c : Peano) : a * (b + c) = a * b + a * c := by
  induction c with
  | zero =>
    rw [add_zero, multiply_zero, add_zero]
  | positive n =>
    induction n with
    | one =>
      rw [add_positive_one, multiply_successor, multiply_positive_one]
    | successor n ih =>
      rw [add_positive_successor, multiply_successor, ih, multiply_positive_successor, add_associative]
  | negative n =>
    induction n with
    | one =>
      rw [add_negative_one, multiply_predecessor, multiply_negative_one]
      rw [subtract_eq_add_negate]
    | successor n ih =>
      rw [add_negative_successor, multiply_predecessor, ih, multiply_negative_successor]
      rw [subtract_eq_add_negate (a * b + a * negative n) a]
      rw [subtract_eq_add_negate (a * negative n) a]
      rw [add_associative]

@[simp]
theorem negate_successor (a : Peano) : -(successor a) = predecessor (-a) := by
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
theorem negate_predecessor (a : Peano) : -(predecessor a) = successor (-a) := by
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
theorem negate_add (a b : Peano) : -(a + b) = -a + -b := by
  induction b with
  | zero =>
    have h1 : -zero = zero := rfl
    rw [add_zero, h1, add_zero]
  | positive n =>
    induction n with
    | one =>
      have hp : -(positive OrdinalNatural.Peano.one) = negative OrdinalNatural.Peano.one := rfl
      rw [hp, add_positive_one, add_negative_one, negate_successor]
    | successor n ih =>
      have hp : -(positive n.successor) = negative n.successor := rfl
      rw [hp, add_positive_successor, add_negative_successor, negate_successor, ih]
      have hp2 : -(positive n) = negative n := rfl
      rw [hp2]
  | negative n =>
    induction n with
    | one =>
      have hn : -(negative OrdinalNatural.Peano.one) = positive OrdinalNatural.Peano.one := rfl
      rw [hn, add_negative_one, add_positive_one, negate_predecessor]
    | successor n ih =>
      have hn : -(negative n.successor) = positive n.successor := rfl
      rw [hn, add_negative_successor, add_positive_successor, negate_predecessor, ih]
      have hn2 : -(negative n) = positive n := rfl
      rw [hn2]

@[simp]
theorem negate_negate (x : Peano) : -(-x) = x := by
  cases x with
  | zero => rfl
  | positive n => rfl
  | negative n => rfl

@[simp]
theorem subtract_negate (a b : Peano) : a - (-b) = a + b := by
  rw [subtract_eq_add_negate, negate_negate]

@[simp]
theorem negate_subtract (a b : Peano) : -(a - b) = -a + b := by
  rw [subtract_eq_add_negate, negate_add, negate_negate]

/-- Difference of positives recovers ordinal subtraction when the subtrahend is
strictly smaller. -/
theorem subtract_positive_positive_of_lt (m n : OrdinalNatural.Peano) (h : n < m) :
    positive m - positive n =
      positive (OrdinalNatural.Peano.subtract m n h) := by
  induction n generalizing m with
  | one =>
    cases m with
    | one => exact (OrdinalNatural.Peano.not_lt_self _ h).elim
    | successor m' =>
      rw [subtract_positive_one]
      rfl
  | successor n ih =>
    cases m with
    | one => exact (OrdinalNatural.Peano.not_lt_one _ h).elim
    | successor m' =>
      have h' : n < m' := OrdinalNatural.Peano.lt_of_successor_lt_successor h
      have hstep :
          positive m'.successor - positive n.successor =
            predecessor (positive m'.successor - positive n) := by
        rw [subtract_positive_successor]
      have hsucc :
          positive m'.successor - positive n =
            successor (positive m' - positive n) := by
        change successor (positive m') - positive n =
          successor (positive m' - positive n)
        rw [successor_subtract]
      rw [hstep, hsucc, predecessor_successor, ih m' h']
      rfl

/-- When the subtrahend is larger, the positive difference is negative. -/
theorem subtract_positive_positive_of_gt (m n : OrdinalNatural.Peano) (h : m < n) :
    positive m - positive n =
      negative (OrdinalNatural.Peano.subtract n m h) := by
  have hpos : positive n - positive m =
      positive (OrdinalNatural.Peano.subtract n m h) := subtract_positive_positive_of_lt n m h
  have hneg : positive m - positive n = -(positive n - positive m) := by
    calc
      positive m - positive n = positive m + -positive n := subtract_eq_add_negate _ _
      _ = -positive n + positive m := add_commutative _ _
      _ = -(positive n - positive m) := (negate_subtract (positive n) (positive m)).symm
  rw [hneg, hpos]
  rfl

/-- Adding a negative to a positive recovers ordinal subtraction when
`n < m`. -/
theorem add_positive_negative_of_lt (m n : OrdinalNatural.Peano) (h : n < m) :
    positive m + negative n =
      positive (OrdinalNatural.Peano.subtract m n h) := by
  have hsub : positive m - positive n =
      positive (OrdinalNatural.Peano.subtract m n h) := subtract_positive_positive_of_lt m n h
  rwa [subtract_eq_add_negate] at hsub

/-- Adding a positive to a negative recovers the dual ordinal subtraction when
`n < m`. -/
theorem add_negative_positive_of_lt (m n : OrdinalNatural.Peano) (h : n < m) :
    negative m + positive n =
      negative (OrdinalNatural.Peano.subtract m n h) := by
  have hsub : -(positive m - positive n) =
      -(positive (OrdinalNatural.Peano.subtract m n h)) :=
    congrArg Neg.neg (subtract_positive_positive_of_lt m n h)
  rw [negate_subtract] at hsub
  exact hsub

/-- Strict inequality implies a strictly positive difference. -/
theorem subtract_positive_of_lt {a b : Peano} (h : a < b) : zero < b - a := by
  match a, b, h with
  | negative n, zero, LessThan.negative_less_than_zero =>
    have hneg : -(negative n) = positive n := rfl
    rw [subtract_eq_add_negate, hneg, zero_add]
    exact LessThan.zero_less_than_positive
  | zero, positive m, LessThan.zero_less_than_positive =>
    rw [subtract_zero]
    exact LessThan.zero_less_than_positive
  | negative n, positive m, LessThan.negative_less_than_positive =>
    have hneg : -(negative n) = positive n := rfl
    rw [subtract_eq_add_negate, hneg, add_positive_positive]
    exact LessThan.zero_less_than_positive
  | positive n, positive m, LessThan.positive_less_than_positive hnm =>
    rw [subtract_positive_positive_of_lt m n hnm]
    exact LessThan.zero_less_than_positive
  | negative n, negative m, LessThan.negative_less_than_negative hnm =>
    have hneg : -(negative n) = positive n := rfl
    rw [subtract_eq_add_negate, hneg, add_commutative, add_positive_negative_of_lt n m hnm]
    exact LessThan.zero_less_than_positive

/-- Ordinal distance from `smaller` up to `larger`, as the ordinal magnitude of
their positive integer difference. -/
def ordinalDistance (smaller larger : Peano) (h : smaller < larger) :
    OrdinalNatural.Peano :=
  toOrdinalNatural (larger - smaller) (subtract_positive_of_lt h)

theorem ordinalDistance_subtract {a b : Peano} (h : a < b) :
    b - a = positive (ordinalDistance a b h) :=
  eq_positive_of_positive (subtract_positive_of_lt h)

theorem lt_of_subtract_positive {a b : Peano} (h : zero < b - a) : a < b := by
  have heq : a + (b - a) = b := by rw [add_commutative, subtract_add_cancel]
  rw [eq_positive_of_positive h] at heq
  exact heq ▸ lt_add_of_positive a _

theorem eq_of_subtract_eq_zero {a b : Peano} (h : b - a = zero) : a = b := by
  have heq : a + (b - a) = b := by rw [add_commutative, subtract_add_cancel]
  rw [h, add_zero] at heq
  exact heq

theorem le_of_subtract_nonNegative {a b : Peano} (h : zero ≤ b - a) : a ≤ b := by
  cases h with
  | inl hlt => exact Or.inl (lt_of_subtract_positive hlt)
  | inr heq => exact Or.inr (eq_of_subtract_eq_zero heq.symm)

theorem subtract_nonNegative_of_le {a b : Peano} (h : a ≤ b) : zero ≤ b - a := by
  cases h with
  | inl hlt => exact Or.inl (subtract_positive_of_lt hlt)
  | inr heq =>
    rw [heq, subtract_self]
    exact Or.inr rfl

theorem positive_injective {n m : OrdinalNatural.Peano}
    (h : positive n = positive m) : n = m := by
  injection h

/-- Stepping toward a greater limit by a positive amount strictly less than the
gap reduces the ordinal distance by that amount. -/
theorem subtract_add_positive_eq_subtract_subtract_positive (limit x : Peano)
    (d : OrdinalNatural.Peano) :
    limit - (x + positive d) = (limit - x) - positive d := by
  rw [subtract_eq_add_negate, negate_add, ← add_associative, ← subtract_eq_add_negate, ← subtract_eq_add_negate]

theorem ordinalDistance_add_positive (x limit : Peano) (d : OrdinalNatural.Peano)
    (hlt : x < limit) (hdiff : d < ordinalDistance x limit hlt)
    (hlt' : x + positive d < limit) :
    ordinalDistance (x + positive d) limit hlt' =
      OrdinalNatural.Peano.subtract (ordinalDistance x limit hlt) d hdiff := by
  have hgap := ordinalDistance_subtract hlt
  have hgap' := ordinalDistance_subtract hlt'
  have hcalc : limit - (x + positive d) =
      positive (OrdinalNatural.Peano.subtract (ordinalDistance x limit hlt) d hdiff) := by
    rw [subtract_add_positive_eq_subtract_subtract_positive, hgap, subtract_positive_positive_of_lt _ _ hdiff]
  exact positive_injective (hgap'.symm.trans hcalc)

theorem subtract_add_negative_eq_subtract_subtract_positive (x limit : Peano)
    (d : OrdinalNatural.Peano) :
    x + negative d - limit = (x - limit) - positive d := by
  rw [subtract_eq_add_negate, subtract_eq_add_negate (x - limit), subtract_eq_add_negate x limit,
    add_associative, add_commutative (negative d), ← add_associative]
  rfl

/-- Stepping toward a lesser limit by a negative amount whose absolute value is
strictly less than the gap reduces the ordinal distance by that amount. -/
theorem ordinalDistance_add_negative (x limit : Peano) (d : OrdinalNatural.Peano)
    (hlt : limit < x) (hdiff : d < ordinalDistance limit x hlt)
    (hlt' : limit < x + negative d) :
    ordinalDistance limit (x + negative d) hlt' =
      OrdinalNatural.Peano.subtract (ordinalDistance limit x hlt) d hdiff := by
  have hgap := ordinalDistance_subtract hlt
  have hgap' := ordinalDistance_subtract hlt'
  have hcalc : x + negative d - limit =
      positive (OrdinalNatural.Peano.subtract (ordinalDistance limit x hlt) d hdiff) := by
    rw [subtract_add_negative_eq_subtract_subtract_positive, hgap, subtract_positive_positive_of_lt _ _ hdiff]
  exact positive_injective (hgap'.symm.trans hcalc)

theorem add_positive_lt_of_lt_gap (x limit : Peano) (d : OrdinalNatural.Peano)
    (hlt : x < limit) (hdiff : d < ordinalDistance x limit hlt) :
    x + positive d < limit :=
  lt_of_subtract_positive (by
    rw [subtract_add_positive_eq_subtract_subtract_positive, ordinalDistance_subtract hlt,
      subtract_positive_positive_of_lt _ _ hdiff]
    exact LessThan.zero_less_than_positive)

theorem add_negative_gt_of_lt_gap (x limit : Peano) (d : OrdinalNatural.Peano)
    (hlt : limit < x) (hdiff : d < ordinalDistance limit x hlt) :
    limit < x + negative d :=
  lt_of_subtract_positive (by
    rw [subtract_add_negative_eq_subtract_subtract_positive, ordinalDistance_subtract hlt,
      subtract_positive_positive_of_lt _ _ hdiff]
    exact LessThan.zero_less_than_positive)

theorem le_iff_add_positive_le {x limit : Peano} (d : OrdinalNatural.Peano)
    (hlt : x < limit) :
    d ≤ ordinalDistance x limit hlt ↔ x + positive d ≤ limit := by
  constructor
  · intro hd
    refine le_of_subtract_nonNegative ?_
    rw [subtract_add_positive_eq_subtract_subtract_positive, ordinalDistance_subtract hlt]
    cases hd with
    | inl hlt_d =>
      rw [subtract_positive_positive_of_lt _ _ hlt_d]
      exact Or.inl LessThan.zero_less_than_positive
    | inr heq =>
      rw [← heq, subtract_self]
      exact Or.inr rfl
  · intro hle
    match hd : OrdinalNatural.Peano.compare d (ordinalDistance x limit hlt) with
    | .less hlt_d => exact Or.inl hlt_d
    | .equal heq => exact Or.inr heq
    | .greater hgt =>
      have hneg : limit - (x + positive d) =
          negative (OrdinalNatural.Peano.subtract d (ordinalDistance x limit hlt) hgt) := by
        rw [subtract_add_positive_eq_subtract_subtract_positive, ordinalDistance_subtract hlt,
          subtract_positive_positive_of_gt _ _ hgt]
      have hnonneg := subtract_nonNegative_of_le hle
      rw [hneg] at hnonneg
      cases hnonneg with
      | inl hlt' => cases hlt'
      | inr heq' => cases heq'

theorem le_iff_add_negative_ge {x limit : Peano} (d : OrdinalNatural.Peano)
    (hlt : limit < x) :
    d ≤ ordinalDistance limit x hlt ↔ limit ≤ x + negative d := by
  constructor
  · intro hd
    refine le_of_subtract_nonNegative ?_
    rw [subtract_add_negative_eq_subtract_subtract_positive, ordinalDistance_subtract hlt]
    cases hd with
    | inl hlt_d =>
      rw [subtract_positive_positive_of_lt _ _ hlt_d]
      exact Or.inl LessThan.zero_less_than_positive
    | inr heq =>
      rw [← heq, subtract_self]
      exact Or.inr rfl
  · intro hle
    match hd : OrdinalNatural.Peano.compare d (ordinalDistance limit x hlt) with
    | .less hlt_d => exact Or.inl hlt_d
    | .equal heq => exact Or.inr heq
    | .greater hgt =>
      have hneg : x + negative d - limit =
          negative (OrdinalNatural.Peano.subtract d (ordinalDistance limit x hlt) hgt) := by
        rw [subtract_add_negative_eq_subtract_subtract_positive, ordinalDistance_subtract hlt,
          subtract_positive_positive_of_gt _ _ hgt]
      have hnonneg := subtract_nonNegative_of_le hle
      rw [hneg] at hnonneg
      cases hnonneg with
      | inl hlt' => cases hlt'
      | inr heq' => cases heq'

@[simp]
theorem negate_multiply (a b : Peano) : (-a) * b = -(a * b) := by
  induction b with
  | zero =>
    rw [multiply_zero, multiply_zero]
    rfl
  | positive n =>
    induction n with
    | one =>
      rw [multiply_positive_one, multiply_positive_one]
    | successor n ih =>
      rw [multiply_positive_successor, multiply_positive_successor, ih, negate_add]
  | negative n =>
    induction n with
    | one =>
      rw [multiply_negative_one, multiply_negative_one, negate_negate]
    | successor n ih =>
      rw [multiply_negative_successor, multiply_negative_successor, ih]
      rw [subtract_negate, negate_subtract]

@[simp]
theorem multiply_negate (a b : Peano) : a * (-b) = -(a * b) := by
  cases b with
  | zero =>
    have hz : -zero = zero := rfl
    have h1 : a * -zero = a * zero := by rw [hz]
    rw [h1, multiply_zero]
    rfl
  | positive n =>
    induction n with
    | one =>
      have hp : -(positive OrdinalNatural.Peano.one) = negative OrdinalNatural.Peano.one := rfl
      rw [hp, multiply_negative_one, multiply_positive_one]
    | successor n ih =>
      have hp : -(positive n.successor) = negative n.successor := rfl
      rw [hp, multiply_negative_successor, multiply_positive_successor]
      have hp2 : -(positive n) = negative n := rfl
      have hh : a * -(positive n) = -(a * positive n) := ih
      rw [hp2] at hh
      rw [hh]
      rw [negate_add, subtract_eq_add_negate]
  | negative n =>
    induction n with
    | one =>
      have hn : -(negative OrdinalNatural.Peano.one) = positive OrdinalNatural.Peano.one := rfl
      rw [hn, multiply_positive_one, multiply_negative_one, negate_negate]
    | successor n ih =>
      have hn : -(negative n.successor) = positive n.successor := rfl
      rw [hn, multiply_positive_successor, multiply_negative_successor]
      have hn2 : -(negative n) = positive n := rfl
      have hh : a * -(negative n) = -(a * negative n) := ih
      rw [hn2] at hh
      rw [hh]
      rw [subtract_eq_add_negate, negate_add, negate_negate, add_commutative]

@[simp]
theorem negate_multiply_negate (x y : Peano) : (-x) * (-y) = x * y := by
  rw [negate_multiply, multiply_negate, negate_negate]

theorem add_right_commutative (a b c : Peano) : a + b + c = a + c + b := by
  rw [add_associative, add_commutative b c, ←add_associative]

@[simp]
theorem successor_multiply (a b : Peano) : successor a * b = a * b + b := by
  induction b with
  | zero => rw [multiply_zero, multiply_zero, add_zero]
  | positive n =>
    induction n with
    | one =>
      rw [multiply_positive_one, multiply_positive_one, ←add_positive_one]
    | successor n ih =>
      rw [multiply_positive_successor, multiply_positive_successor, ih]
      rw [add_successor]
      have h1 : a * positive n + positive n + a = a * positive n + a + positive n := add_right_commutative _ _ _
      rw [h1]
      rw [←add_successor]
      rfl
  | negative n =>
    induction n with
    | one =>
      rw [multiply_negative_one, multiply_negative_one]
      rw [negate_successor]
      rw [←add_negative_one]
    | successor n ih =>
      rw [multiply_negative_successor, multiply_negative_successor, ih]
      rw [subtract_eq_add_negate, subtract_eq_add_negate]
      rw [negate_successor]
      rw [add_predecessor]
      have h1 : a * negative n + negative n + -a = a * negative n + -a + negative n := add_right_commutative _ _ _
      rw [h1]
      have h2 : predecessor (a * negative n + -a + negative n) = a * negative n + -a + predecessor (negative n) := by
        rw [←add_predecessor]
      rw [h2]
      rfl

@[simp]
theorem predecessor_multiply (a b : Peano) : predecessor a * b = a * b - b := by
  induction b with
  | zero => rw [multiply_zero, multiply_zero, subtract_zero]
  | positive n =>
    induction n with
    | one =>
      rw [multiply_positive_one, multiply_positive_one, subtract_positive_one]
    | successor n ih =>
      rw [multiply_positive_successor, ih]
      rw [subtract_eq_add_negate, subtract_eq_add_negate]
      have h2 : -(positive n) = negative n := rfl
      rw [h2]
      have h0 : a.predecessor = a + negative OrdinalNatural.Peano.one := (add_negative_one a).symm
      rw [h0]
      rw [add_associative]
      have hc : negative n + (a + negative OrdinalNatural.Peano.one) = a + negative n + negative OrdinalNatural.Peano.one := by
        rw [add_commutative (negative n) (a + negative OrdinalNatural.Peano.one)]
        rw [add_associative, add_commutative (negative OrdinalNatural.Peano.one)]
        rw [←add_associative]
      rw [hc, ←add_associative]
      have hx : a * positive n + (a + negative n) = a * positive n + a + negative n := (add_associative _ _ _).symm
      rw [hx]
      have hr : a * positive n + a = a * positive n.successor := (multiply_positive_successor a n).symm
      rw [hr]
      rw [add_associative]
      have h5 : negative n + negative OrdinalNatural.Peano.one = predecessor (negative n) := add_negative_one (negative n)
      rw [h5]
      have h7 : predecessor (negative n) = negative n.successor := rfl
      rw [h7]
      have h6 : -(positive n.successor) = negative n.successor := rfl
      rw [←h6]
  | negative n =>
    induction n with
    | one =>
      rw [multiply_negative_one, multiply_negative_one]
      rw [subtract_negative_one, negate_predecessor]
    | successor n ih =>
      rw [multiply_negative_successor, ih]
      rw [subtract_eq_add_negate, subtract_eq_add_negate]
      have h2 : -(negative n) = positive n := rfl
      rw [h2]
      have h3 : -(a.predecessor) = -a + positive OrdinalNatural.Peano.one := by
        rw [negate_predecessor]
        exact (add_positive_one (-a)).symm
      rw [h3]
      rw [add_associative]
      have hc : positive n + (-a + positive OrdinalNatural.Peano.one) = -a + positive n + positive OrdinalNatural.Peano.one := by
        rw [add_commutative (positive n) (-a + positive OrdinalNatural.Peano.one)]
        rw [add_associative, add_commutative (positive OrdinalNatural.Peano.one)]
        rw [←add_associative]
      rw [hc, ←add_associative]
      have hx : a * negative n + (-a + positive n) = a * negative n + -a + positive n := (add_associative _ _ _).symm
      rw [hx]
      have h1 : a * negative n + -a = a * negative n - a := (subtract_eq_add_negate _ _).symm
      rw [h1]
      have hm : a * negative n - a = a * negative n.successor := (multiply_negative_successor a n).symm
      rw [hm]
      rw [add_associative]
      have h5 : positive n + positive OrdinalNatural.Peano.one = successor (positive n) := add_positive_one (positive n)
      rw [h5]
      have h7 : successor (positive n) = positive n.successor := rfl
      rw [h7]
      have h6 : -(negative n.successor) = positive n.successor := rfl
      rw [←h6]
      have hsub : a * negative n.successor + -(negative n.successor) = a * negative n.successor - negative n.successor := (subtract_eq_add_negate _ _).symm
      rw [hsub]

theorem multiply_commutative (a b : Peano) : a * b = b * a := by
  induction a with
  | zero => rw [multiply_zero, zero_multiply]
  | positive n =>
    induction n with
    | one =>
      induction b with
      | zero => rw [multiply_positive_one, multiply_zero]
      | positive m =>
        induction m with
        | one => rfl
        | successor m ihm =>
          rw [multiply_positive_successor]
          have h1 : positive m * positive OrdinalNatural.Peano.one = positive m := multiply_positive_one _
          rw [h1] at ihm
          rw [ihm, add_positive_one]
          have h2 : positive m.successor = successor (positive m) := rfl
          rw [h2, multiply_positive_one]
      | negative m =>
        induction m with
        | one =>
          rw [multiply_negative_one, multiply_positive_one]
          rfl
        | successor m ihm =>
          rw [multiply_negative_successor]
          have h1 : negative m * positive OrdinalNatural.Peano.one = negative m := multiply_positive_one _
          rw [h1] at ihm
          rw [ihm, subtract_positive_one]
          have h2 : negative m.successor = predecessor (negative m) := rfl
          rw [h2, multiply_positive_one]
    | successor n ih =>
      have hs : positive n.successor = successor (positive n) := rfl
      rw [hs]
      rw [successor_multiply, ih, multiply_successor]
  | negative n =>
    induction n with
    | one =>
      induction b with
      | zero => rw [multiply_negative_one, multiply_zero]; rfl
      | positive m =>
        induction m with
        | one =>
          rw [multiply_positive_one, multiply_negative_one]
          rfl
        | successor m ihm =>
          rw [multiply_positive_successor, ihm]
          have hm : positive m * negative OrdinalNatural.Peano.one = -positive m := multiply_negative_one _
          rw [hm]
          have hn : -positive m + negative OrdinalNatural.Peano.one = predecessor (-positive m) := add_negative_one _
          rw [hn]
          have hn2 : -(positive m) = negative m := rfl
          rw [hn2]
          have hx : predecessor (negative m) = negative m.successor := rfl
          rw [hx]
          have h1 : -(positive m.successor) = negative m.successor := rfl
          rw [←h1]
          have hsub : positive m.successor * negative OrdinalNatural.Peano.one = -(positive m.successor) := multiply_negative_one _
          rw [hsub]
      | negative m =>
        induction m with
        | one => rfl
        | successor m ihm =>
          rw [multiply_negative_successor, ihm]
          have hm2 : negative m * negative OrdinalNatural.Peano.one = -negative m := multiply_negative_one _
          rw [hm2]
          have hm : -(negative m) = positive m := rfl
          rw [hm]
          have hn : positive m - negative OrdinalNatural.Peano.one = positive m + positive OrdinalNatural.Peano.one := subtract_eq_add_negate _ _
          rw [hn]
          have hn_succ : positive m + positive OrdinalNatural.Peano.one = successor (positive m) := add_positive_one _
          rw [hn_succ]
          have hx : successor (positive m) = positive m.successor := rfl
          rw [hx]
          have h1 : -(negative m.successor) = positive m.successor := rfl
          rw [←h1]
          have hsub : negative m.successor * negative OrdinalNatural.Peano.one = -(negative m.successor) := multiply_negative_one _
          rw [hsub]
    | successor n ih =>
      have hs : negative n.successor = predecessor (negative n) := rfl
      rw [hs]
      rw [predecessor_multiply, ih, multiply_predecessor]

theorem add_multiply (a b c : Peano) : (a + b) * c = a * c + b * c := by
  rw [multiply_commutative, multiply_add, multiply_commutative c a, multiply_commutative c b]

theorem subtract_multiply (a b c : Peano) : (a - b) * c = a * c - b * c := by
  rw [subtract_eq_add_negate, subtract_eq_add_negate (a*c), add_multiply, negate_multiply]

theorem multiply_subtract (a b c : Peano) : a * (b - c) = a * b - a * c := by
  rw [multiply_commutative, subtract_multiply, multiply_commutative b a, multiply_commutative c a]

theorem multiply_associative (a b c : Peano) : (a * b) * c = a * (b * c) := by
  induction c with
  | zero =>
    rw [multiply_zero, multiply_zero, multiply_zero]
  | positive n =>
    induction n with
    | one =>
      rw [multiply_positive_one, multiply_positive_one]
    | successor m ih =>
      rw [multiply_positive_successor, multiply_positive_successor, multiply_add, ih]
  | negative n =>
    induction n with
    | one =>
      rw [multiply_negative_one, multiply_negative_one, multiply_negate]
    | successor m ih =>
      rw [multiply_negative_successor, multiply_negative_successor, multiply_subtract, ih]

theorem subtract_associative (x y z : Peano) : x + y - z = x + (y - z) := by
  rw [subtract_eq_add_negate, subtract_eq_add_negate, add_associative]

theorem subtract_subtract (x y z : Peano) : x - y - z = x - (y + z) := by
  rw [subtract_eq_add_negate (x - y) z]
  rw [subtract_eq_add_negate x y]
  rw [subtract_eq_add_negate x (y + z)]
  rw [negate_add, add_associative]

theorem subtract_add (x y z : Peano) : x - y + z = x - (y - z) := by
  rw [subtract_eq_add_negate, subtract_eq_add_negate x (y - z), negate_subtract, add_associative]

theorem multiply_eq_zero_iff (x y : Peano) : x * y = zero ↔ x = zero ∨ y = zero := by
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
      rw [hx, zero_multiply]
    | inr hy =>
      rw [hy, multiply_zero]

def powerOrdinalExponent (a : Peano) : OrdinalNatural.Peano → Peano
  | OrdinalNatural.Peano.one => a
  | OrdinalNatural.Peano.successor n => powerOrdinalExponent a n * a

def ValidPowerCondition (a b : Peano) : Bool :=
  match a, b with
  | _, Peano.positive _ => true
  | Peano.positive _, Peano.zero => true
  | Peano.negative _, Peano.zero => true
  | Peano.positive OrdinalNatural.Peano.one, Peano.negative _ => true
  | Peano.negative OrdinalNatural.Peano.one, Peano.negative _ => true
  | _, _ => false

theorem powerOrdinalExponent_add (x : Peano) (y z : OrdinalNatural.Peano) :
    powerOrdinalExponent x (y + z) = powerOrdinalExponent x y * powerOrdinalExponent x z := by
  induction z with
  | one =>
      rw [OrdinalNatural.Peano.add_one]
      rfl
  | successor z ih =>
      rw [OrdinalNatural.Peano.add_successor]
      change powerOrdinalExponent x (y + z) * x = powerOrdinalExponent x y * (powerOrdinalExponent x z * x)
      rw [ih]
      exact Peano.multiply_associative (powerOrdinalExponent x y) (powerOrdinalExponent x z) x

theorem powerOrdinalExponent_multiply (x : Peano) (y z : OrdinalNatural.Peano) :
    powerOrdinalExponent x (y * z) = powerOrdinalExponent (powerOrdinalExponent x y) z := by
  induction z with
  | one =>
      rw [OrdinalNatural.Peano.multiply_one]
      rfl
  | successor z ih =>
      rw [OrdinalNatural.Peano.multiply_successor, powerOrdinalExponent_add, ih]
      rfl

theorem powerOrdinalExponent_multiply_base (x y : Peano) (z : OrdinalNatural.Peano) :
    powerOrdinalExponent (x * y) z = powerOrdinalExponent x z * powerOrdinalExponent y z := by
  induction z with
  | one =>
      rfl
  | successor z ih =>
      rw [powerOrdinalExponent, powerOrdinalExponent, powerOrdinalExponent, ih]
      calc
        (powerOrdinalExponent x z * powerOrdinalExponent y z) * (x * y)
            = powerOrdinalExponent x z * (powerOrdinalExponent y z * (x * y)) := by
                rw [multiply_associative]
        _ = powerOrdinalExponent x z * ((powerOrdinalExponent y z * x) * y) := by
              rw [multiply_associative]
        _ = powerOrdinalExponent x z * ((x * powerOrdinalExponent y z) * y) := by
              rw [multiply_commutative (powerOrdinalExponent y z) x]
        _ = powerOrdinalExponent x z * (x * (powerOrdinalExponent y z * y)) := by
              rw [multiply_associative]
        _ = (powerOrdinalExponent x z * x) * (powerOrdinalExponent y z * y) := by
              rw [← multiply_associative]
        _ = powerOrdinalExponent x z.successor * powerOrdinalExponent y z.successor := by
              rfl

theorem toInt_powerOrdinalExponent (x : Peano) (n : OrdinalNatural.Peano) :
    (powerOrdinalExponent x n).toInt = x.toInt ^ n.toNat := by
  induction n with
  | one =>
      simp [powerOrdinalExponent, toInt, ZeroMath.Numbers.OrdinalNatural.Peano.toNat, Int.pow_one]
  | successor n ih =>
      rw [powerOrdinalExponent, toInt_multiply, ih]
      rw [ZeroMath.Numbers.OrdinalNatural.Peano.toNat, Int.pow_succ]

theorem powerOrdinalExponent_toInt_natAbs (x : Peano) (n : OrdinalNatural.Peano) :
    (powerOrdinalExponent x n).toInt.natAbs = x.toInt.natAbs ^ n.toNat := by
  rw [toInt_powerOrdinalExponent]
  exact Int.natAbs_pow x.toInt n.toNat

theorem powerOrdinalExponent_one (e : OrdinalNatural.Peano) : powerOrdinalExponent one e = one := by
  induction e with
  | one => rfl
  | successor e ih =>
      change powerOrdinalExponent one e * one = one
      rw [ih, one, multiply_positive_one]

theorem validPowerCondition_one (e : Peano) : ValidPowerCondition one e = true := by
  cases e <;> rfl

theorem validPowerCondition_minusOne (e : Peano) : ValidPowerCondition minusOne e = true := by
  cases e <;> rfl

theorem not_validPowerCondition_zero_zero :
    ¬ ValidPowerCondition zero zero = true :=
  Bool.false_ne_true

theorem isDivisible_one_one : Divisible one one := by
  refine ⟨?_, one, ?_⟩
  · intro h
    cases h
  · rw [one, multiply_positive_one]

theorem minusOne_multiply_minusOne : minusOne * minusOne = one := by
  rw [minusOne, multiply_negative_one]
  rfl

theorem isDivisible_one_minusOne : Divisible one minusOne := by
  refine ⟨?_, minusOne, ?_⟩
  · intro h
    cases h
  · exact minusOne_multiply_minusOne

theorem powerOrdinalExponent_minusOne_eq_one_or_minusOne (e : OrdinalNatural.Peano) :
    powerOrdinalExponent minusOne e = one ∨ powerOrdinalExponent minusOne e = minusOne := by
  induction e with
  | one =>
      right
      rfl
  | successor e ih =>
      cases ih with
      | inl h =>
          right
          change powerOrdinalExponent minusOne e * minusOne = minusOne
          rw [h, minusOne, multiply_negative_one]
          rfl
      | inr h =>
          left
          change powerOrdinalExponent minusOne e * minusOne = one
          rw [h]
          exact minusOne_multiply_minusOne

theorem isDivisible_one_powerOrdinalExponent_minusOne (e : OrdinalNatural.Peano) :
    Divisible one (powerOrdinalExponent minusOne e) := by
  cases powerOrdinalExponent_minusOne_eq_one_or_minusOne e with
  | inl h =>
      rw [h]
      exact isDivisible_one_one
  | inr h =>
      rw [h]
      exact isDivisible_one_minusOne

theorem isDivisible_one_powerOrdinalExponent_of_valid_negative (a : Peano) (e : OrdinalNatural.Peano)
    (h : ValidPowerCondition a (negative e) = true) :
    Divisible one (powerOrdinalExponent a e) := by
  cases a with
  | zero =>
      contradiction
  | positive n =>
      cases n with
      | one =>
          change Divisible one (powerOrdinalExponent one e)
          rw [powerOrdinalExponent_one]
          exact isDivisible_one_one
      | successor n =>
          contradiction
  | negative n =>
      cases n with
      | one =>
          change Divisible one (powerOrdinalExponent minusOne e)
          exact isDivisible_one_powerOrdinalExponent_minusOne e
      | successor n =>
          contradiction

theorem absoluteValue_multiply (x y : Peano) :
    absoluteValue (x * y) = absoluteValue x * absoluteValue y := by
  cases x with
  | zero =>
    simp [absoluteValue, zero_multiply]
  | positive xn =>
    cases y with
    | zero =>
      simp [absoluteValue, multiply_zero]
    | positive yn =>
      rw [multiply_positive_positive]
      exact (multiply_positive_positive xn yn).symm
    | negative yn =>
      rw [multiply_positive_negative]
      exact (multiply_positive_positive xn yn).symm
  | negative xn =>
    cases y with
    | zero =>
      simp [absoluteValue, multiply_zero]
    | positive yn =>
      rw [multiply_negative_positive]
      exact (multiply_positive_positive xn yn).symm
    | negative yn =>
      rw [multiply_negative_negative]
      exact (multiply_positive_positive xn yn).symm

theorem isDivisible_positive_positive {a b : OrdinalNatural.Peano}
    (h : Divisible (positive a) (positive b)) :
    OrdinalNatural.Peano.Divisible a b := by
  rcases h with ⟨_, c, hc⟩
  cases c with
  | zero =>
      rw [multiply_zero] at hc
      cases hc
  | positive c =>
      rw [multiply_positive_positive] at hc
      cases hc
      exact ⟨c, rfl⟩
  | negative c =>
      rw [multiply_positive_negative] at hc
      cases hc

theorem isDivisible_positive_negative {a b : OrdinalNatural.Peano}
    (h : Divisible (positive a) (negative b)) :
    OrdinalNatural.Peano.Divisible a b := by
  rcases h with ⟨_, c, hc⟩
  cases c with
  | zero =>
      rw [multiply_zero] at hc
      cases hc
  | positive c =>
      rw [multiply_negative_positive] at hc
      cases hc
  | negative c =>
      rw [multiply_negative_negative] at hc
      cases hc
      exact ⟨c, rfl⟩

theorem isDivisible_negative_positive {a b : OrdinalNatural.Peano}
    (h : Divisible (negative a) (positive b)) :
    OrdinalNatural.Peano.Divisible a b := by
  rcases h with ⟨_, c, hc⟩
  cases c with
  | zero =>
      rw [multiply_zero] at hc
      cases hc
  | positive c =>
      rw [multiply_positive_positive] at hc
      cases hc
  | negative c =>
      rw [multiply_positive_negative] at hc
      cases hc
      exact ⟨c, rfl⟩

theorem isDivisible_negative_negative {a b : OrdinalNatural.Peano}
    (h : Divisible (negative a) (negative b)) :
    OrdinalNatural.Peano.Divisible a b := by
  rcases h with ⟨_, c, hc⟩
  cases c with
  | zero =>
      rw [multiply_zero] at hc
      cases hc
  | positive c =>
      rw [multiply_negative_positive] at hc
      cases hc
      exact ⟨c, rfl⟩
  | negative c =>
      rw [multiply_negative_negative] at hc
      cases hc

def tryDivide (a b : Peano) : Option Peano :=
  match a, b with
  | _, zero => none
  | zero, _ => some zero
  | positive a', positive b' =>
      (OrdinalNatural.Peano.tryDivide a' b').map positive
  | positive a', negative b' =>
      (OrdinalNatural.Peano.tryDivide a' b').map negative
  | negative a', positive b' =>
      (OrdinalNatural.Peano.tryDivide a' b').map negative
  | negative a', negative b' =>
      (OrdinalNatural.Peano.tryDivide a' b').map positive

def divide (a b : Peano) (h : Divisible a b) : Peano :=
  match a, b with
  | _, zero => False.elim (h.left rfl)
  | zero, _ => zero
  | positive a', positive b' => positive (OrdinalNatural.Peano.divide a' b'
      (isDivisible_positive_positive h))
  | positive a', negative b' => negative (OrdinalNatural.Peano.divide a' b'
      (isDivisible_positive_negative h))
  | negative a', positive b' => negative (OrdinalNatural.Peano.divide a' b'
      (isDivisible_negative_positive h))
  | negative a', negative b' => positive (OrdinalNatural.Peano.divide a' b'
      (isDivisible_negative_negative h))

def tryPower (a b : Peano) (h : a ≠ zero ∨ b ≠ zero) : Option Peano :=
  match a, b with
  | zero, zero => by contradiction
  | _, zero => some one
  | a, positive n => some (powerOrdinalExponent a n)
  | a, negative n => tryDivide one (powerOrdinalExponent a n)

theorem tryPower_negative (x : Peano) (e : OrdinalNatural.Peano)
    (h : x ≠ zero ∨ negative e ≠ zero) :
    tryPower x (negative e) h = tryDivide one (powerOrdinalExponent x e) := by
  cases x <;> rfl

def power : (a b : Peano) → (h : ValidPowerCondition a b = true) → Peano
  | zero, positive _, _ => zero
  | zero, zero, h => False.elim (not_validPowerCondition_zero_zero h)
  | _, zero, _ => one
  | a, positive n, _ => powerOrdinalExponent a n
  | a, negative n, h => divide one (powerOrdinalExponent a n) (isDivisible_one_powerOrdinalExponent_of_valid_negative a n h)

theorem divide_correct (a b : Peano) (h : Divisible a b) :
    b * divide a b h = a := by
  cases b with
  | zero =>
      exact False.elim (h.left rfl)
  | positive b' =>
      cases a with
      | zero =>
          change positive b' * zero = zero
          rw [multiply_zero]
      | positive a' =>
          change positive b' * positive (OrdinalNatural.Peano.divide a' b'
            (isDivisible_positive_positive h)) = positive a'
          rw [multiply_positive_positive]
          exact congrArg positive (OrdinalNatural.Peano.divide_correct a' b'
            (isDivisible_positive_positive h))
      | negative a' =>
          change positive b' * negative (OrdinalNatural.Peano.divide a' b'
            (isDivisible_negative_positive h)) = negative a'
          rw [multiply_positive_negative]
          exact congrArg negative (OrdinalNatural.Peano.divide_correct a' b'
            (isDivisible_negative_positive h))
  | negative b' =>
      cases a with
      | zero =>
          change negative b' * zero = zero
          rw [multiply_zero]
      | positive a' =>
          change negative b' * negative (OrdinalNatural.Peano.divide a' b'
            (isDivisible_positive_negative h)) = positive a'
          rw [multiply_negative_negative]
          exact congrArg positive (OrdinalNatural.Peano.divide_correct a' b'
            (isDivisible_positive_negative h))
      | negative a' =>
          change negative b' * positive (OrdinalNatural.Peano.divide a' b'
            (isDivisible_negative_negative h)) = negative a'
          rw [multiply_negative_positive]
          exact congrArg negative (OrdinalNatural.Peano.divide_correct a' b'
            (isDivisible_negative_negative h))

theorem exists_divide_of_tryDivide {x y z : Peano} (h : tryDivide x y = some z) :
    ∃ h', divide x y h' = z := by
  unfold tryDivide at h
  split at h
  · next => cases h
  · next hy =>
    injection h with hz
    subst hz
    cases y with
    | zero => exact False.elim (hy rfl)
    | positive b' =>
      have hb : positive b' ≠ zero := fun hz => by cases hz
      let hdiv : Divisible zero (positive b') := ⟨hb, zero, multiply_zero _⟩
      exact ⟨hdiv, rfl⟩
    | negative b' =>
      have hb : negative b' ≠ zero := fun hz => by cases hz
      let hdiv : Divisible zero (negative b') := ⟨hb, zero, multiply_zero _⟩
      exact ⟨hdiv, rfl⟩
  · next a' b' =>
    cases htry : OrdinalNatural.Peano.tryDivide a' b' with
    | none => simp [htry] at h
    | some z' =>
      simp [htry] at h
      obtain ⟨h_ord, heq⟩ := OrdinalNatural.Peano.exists_divide_of_tryDivide htry
      have hmul : b' * z' = a' := by
        rw [← heq]
        exact OrdinalNatural.Peano.divide_correct a' b' h_ord
      have hb : positive b' ≠ zero := fun hz => by cases hz
      have hprod : positive b' * positive z' = positive a' := by
        rw [multiply_positive_positive, hmul]
      let hdiv : Divisible (positive a') (positive b') := ⟨hb, positive z', hprod⟩
      refine ⟨hdiv, ?_⟩
      apply multiply_left_cancel (positive b') _ _ hb
      rw [divide_correct (positive a') (positive b') hdiv, ← h, hprod]
  · next a' b' =>
    cases htry : OrdinalNatural.Peano.tryDivide a' b' with
    | none => simp [htry] at h
    | some z' =>
      simp [htry] at h
      obtain ⟨h_ord, heq⟩ := OrdinalNatural.Peano.exists_divide_of_tryDivide htry
      have hmul : b' * z' = a' := by
        rw [← heq]
        exact OrdinalNatural.Peano.divide_correct a' b' h_ord
      have hb : negative b' ≠ zero := fun hz => by cases hz
      have hprod : negative b' * negative z' = positive a' := by
        rw [multiply_negative_negative, hmul]
      let hdiv : Divisible (positive a') (negative b') := ⟨hb, negative z', hprod⟩
      refine ⟨hdiv, ?_⟩
      apply multiply_left_cancel (negative b') _ _ hb
      rw [divide_correct (positive a') (negative b') hdiv, ← h, hprod]
  · next a' b' =>
    cases htry : OrdinalNatural.Peano.tryDivide a' b' with
    | none => simp [htry] at h
    | some z' =>
      simp [htry] at h
      obtain ⟨h_ord, heq⟩ := OrdinalNatural.Peano.exists_divide_of_tryDivide htry
      have hmul : b' * z' = a' := by
        rw [← heq]
        exact OrdinalNatural.Peano.divide_correct a' b' h_ord
      have hb : positive b' ≠ zero := fun hz => by cases hz
      have hprod : positive b' * negative z' = negative a' := by
        rw [multiply_positive_negative, hmul]
      let hdiv : Divisible (negative a') (positive b') := ⟨hb, negative z', hprod⟩
      refine ⟨hdiv, ?_⟩
      apply multiply_left_cancel (positive b') _ _ hb
      rw [divide_correct (negative a') (positive b') hdiv, ← h, hprod]
  · next a' b' =>
    cases htry : OrdinalNatural.Peano.tryDivide a' b' with
    | none => simp [htry] at h
    | some z' =>
      simp [htry] at h
      obtain ⟨h_ord, heq⟩ := OrdinalNatural.Peano.exists_divide_of_tryDivide htry
      have hmul : b' * z' = a' := by
        rw [← heq]
        exact OrdinalNatural.Peano.divide_correct a' b' h_ord
      have hb : negative b' ≠ zero := fun hz => by cases hz
      have hprod : negative b' * positive z' = negative a' := by
        rw [multiply_negative_positive, hmul]
      let hdiv : Divisible (negative a') (negative b') := ⟨hb, positive z', hprod⟩
      refine ⟨hdiv, ?_⟩
      apply multiply_left_cancel (negative b') _ _ hb
      rw [divide_correct (negative a') (negative b') hdiv, ← h, hprod]

theorem tryDivide_of_divide {x y z : Peano} (h : ∃ h', divide x y h' = z) :
    tryDivide x y = some z := by
  obtain ⟨hdiv, heq⟩ := h
  cases y with
  | zero => exact False.elim (hdiv.left rfl)
  | positive b' =>
    cases x with
    | zero =>
      have hdiv_eq : divide zero (positive b') hdiv = zero := rfl
      calc tryDivide zero (positive b')
          = some zero := rfl
        _ = some z := by rw [← hdiv_eq, heq]
    | positive a' =>
      have hord := isDivisible_positive_positive hdiv
      have hdiv_eq : divide (positive a') (positive b') hdiv =
          positive (OrdinalNatural.Peano.divide a' b' hord) := rfl
      have htry := OrdinalNatural.Peano.tryDivide_of_divide (x := a') (y := b')
        ⟨hord, rfl⟩
      calc tryDivide (positive a') (positive b')
          = (OrdinalNatural.Peano.tryDivide a' b').map positive := rfl
        _ = (some (OrdinalNatural.Peano.divide a' b' hord)).map positive := by rw [htry]
        _ = some (positive (OrdinalNatural.Peano.divide a' b' hord)) := rfl
        _ = some z := by rw [← hdiv_eq, heq]
    | negative a' =>
      have hord := isDivisible_negative_positive hdiv
      have hdiv_eq : divide (negative a') (positive b') hdiv =
          negative (OrdinalNatural.Peano.divide a' b' hord) := rfl
      have htry := OrdinalNatural.Peano.tryDivide_of_divide (x := a') (y := b')
        ⟨hord, rfl⟩
      calc tryDivide (negative a') (positive b')
          = (OrdinalNatural.Peano.tryDivide a' b').map negative := rfl
        _ = (some (OrdinalNatural.Peano.divide a' b' hord)).map negative := by rw [htry]
        _ = some (negative (OrdinalNatural.Peano.divide a' b' hord)) := rfl
        _ = some z := by rw [← hdiv_eq, heq]
  | negative b' =>
    cases x with
    | zero =>
      have hdiv_eq : divide zero (negative b') hdiv = zero := rfl
      calc tryDivide zero (negative b')
          = some zero := rfl
        _ = some z := by rw [← hdiv_eq, heq]
    | positive a' =>
      have hord := isDivisible_positive_negative hdiv
      have hdiv_eq : divide (positive a') (negative b') hdiv =
          negative (OrdinalNatural.Peano.divide a' b' hord) := rfl
      have htry := OrdinalNatural.Peano.tryDivide_of_divide (x := a') (y := b')
        ⟨hord, rfl⟩
      calc tryDivide (positive a') (negative b')
          = (OrdinalNatural.Peano.tryDivide a' b').map negative := rfl
        _ = (some (OrdinalNatural.Peano.divide a' b' hord)).map negative := by rw [htry]
        _ = some (negative (OrdinalNatural.Peano.divide a' b' hord)) := rfl
        _ = some z := by rw [← hdiv_eq, heq]
    | negative a' =>
      have hord := isDivisible_negative_negative hdiv
      have hdiv_eq : divide (negative a') (negative b') hdiv =
          positive (OrdinalNatural.Peano.divide a' b' hord) := rfl
      have htry := OrdinalNatural.Peano.tryDivide_of_divide (x := a') (y := b')
        ⟨hord, rfl⟩
      calc tryDivide (negative a') (negative b')
          = (OrdinalNatural.Peano.tryDivide a' b').map positive := rfl
        _ = (some (OrdinalNatural.Peano.divide a' b' hord)).map positive := by rw [htry]
        _ = some (positive (OrdinalNatural.Peano.divide a' b' hord)) := rfl
        _ = some z := by rw [← hdiv_eq, heq]

theorem multiply_divide_cancel (x y : Peano) (h : Divisible x y) :
    (divide x y h) * y = x := by
  rw [multiply_commutative]
  exact divide_correct x y h

/-- A successful `tryDivide` recovers the multiplicative relation `y * q = x`. -/
theorem eq_of_tryDivide_multiply {x y q : Peano} (h : tryDivide x y = some q) :
    y * q = x := by
  obtain ⟨hdiv, heq⟩ := exists_divide_of_tryDivide h
  rw [← heq]
  exact divide_correct x y hdiv

/-- A positive integer Peano number is never zero. -/
theorem positive_ne_zero (n : OrdinalNatural.Peano) : positive n ≠ zero :=
  fun h => by cases h

@[simp]
theorem one_multiply (a : Peano) : one * a = a := by
  rw [multiply_commutative, one, multiply_positive_one]

/-- Stepping an integer by `c` after scaling the predecessor offset by `c`
recovers scaling the original value. -/
theorem subtract_one_multiply_add (a c : Peano) : (a - one) * c + c = a * c := by
  calc
    (a - one) * c + c
        = (a - one) * c + one * c := by rw [one_multiply]
    _ = ((a - one) + one) * c := (add_multiply _ _ _).symm
    _ = a * c := by rw [subtract_add_cancel]

theorem not_divisible_one_of_positive_gt_one (k : OrdinalNatural.Peano)
    (hlt : OrdinalNatural.Peano.one < k) :
    ¬ Divisible one (positive k) := by
  intro hdiv
  obtain ⟨hne, c, hc⟩ := hdiv
  cases c with
  | zero =>
    rw [multiply_zero] at hc
    cases hc
  | positive cn =>
    rw [multiply_positive_positive] at hc
    injection hc with hc'
    have hle2 : k ≤ OrdinalNatural.Peano.one := by
      have : k ≤ cn * k := OrdinalNatural.Peano.le_multiply_right k cn
      rw [← hc', OrdinalNatural.Peano.multiply_commutative]
      exact this
    cases hle2 with
    | inl hlt3 =>
      exact False.elim (OrdinalNatural.Peano.not_lt_self _
        (OrdinalNatural.Peano.lt_trans hlt hlt3))
    | inr heq =>
      rw [heq] at hlt
      exact False.elim (OrdinalNatural.Peano.not_lt_self _ hlt)
  | negative cn =>
    rw [multiply_positive_negative] at hc
    cases hc

theorem not_divisible_one_of_negative_gt_one (k : OrdinalNatural.Peano)
    (hlt : OrdinalNatural.Peano.one < k) :
    ¬ Divisible one (negative k) := by
  intro hdiv
  obtain ⟨hne, c, hc⟩ := hdiv
  cases c with
  | zero =>
    rw [multiply_zero] at hc
    cases hc
  | positive cn =>
    rw [multiply_negative_positive] at hc
    cases hc
  | negative cn =>
    rw [multiply_negative_negative] at hc
    injection hc with hc'
    have hle2 : k ≤ OrdinalNatural.Peano.one := by
      have : k ≤ cn * k := OrdinalNatural.Peano.le_multiply_right k cn
      rw [← hc', OrdinalNatural.Peano.multiply_commutative]
      exact this
    cases hle2 with
    | inl hlt3 =>
      exact False.elim (OrdinalNatural.Peano.not_lt_self _
        (OrdinalNatural.Peano.lt_trans hlt hlt3))
    | inr heq =>
      rw [heq] at hlt
      exact False.elim (OrdinalNatural.Peano.not_lt_self _ hlt)

theorem one_lt_successor_power (k e : OrdinalNatural.Peano) :
    OrdinalNatural.Peano.one < k.successor ^ e := by
  have hlt : OrdinalNatural.Peano.one < k.successor :=
    OrdinalNatural.Peano.one_lt_successor k
  have hle : k.successor ≤ k.successor ^ e :=
    OrdinalNatural.Peano.le_power k.successor e
  cases hle with
  | inl hlt' => exact OrdinalNatural.Peano.lt_trans hlt hlt'
  | inr heq => rw [← heq]; exact hlt

theorem power_zero (x : Peano) (h : ValidPowerCondition x zero = true) : power x zero h = one := by
  cases x with
  | zero => contradiction
  | positive n => rfl
  | negative n => rfl

theorem divide_one_powerOrdinalExponent_one_eq (e : OrdinalNatural.Peano)
    (h : Divisible one (powerOrdinalExponent one e)) : divide one (powerOrdinalExponent one e) h = one := by
  apply multiply_left_cancel (powerOrdinalExponent one e)
  · exact h.left
  calc
    powerOrdinalExponent one e * divide one (powerOrdinalExponent one e) h = one := divide_correct one (powerOrdinalExponent one e) h
    _ = powerOrdinalExponent one e * one := by rw [powerOrdinalExponent_one, one, multiply_positive_one]

theorem power_one (e : Peano) (h : ValidPowerCondition one e = true) : power one e h = one := by
  cases e with
  | zero => rfl
  | positive n =>
      change powerOrdinalExponent one n = one
      exact powerOrdinalExponent_one n
  | negative n =>
      change divide one (powerOrdinalExponent one n) (isDivisible_one_powerOrdinalExponent_of_valid_negative one n h) = one
      exact divide_one_powerOrdinalExponent_one_eq n _

theorem powerOrdinalExponent_minusOne_square (e : OrdinalNatural.Peano) : powerOrdinalExponent minusOne e * powerOrdinalExponent minusOne e = one := by
  cases powerOrdinalExponent_minusOne_eq_one_or_minusOne e with
  | inl h => rw [h, one, multiply_positive_one]
  | inr h => rw [h, minusOne_multiply_minusOne]

theorem divide_one_powerOrdinalExponent_minusOne_eq (e : OrdinalNatural.Peano)
    (h : Divisible one (powerOrdinalExponent minusOne e)) : divide one (powerOrdinalExponent minusOne e) h = powerOrdinalExponent minusOne e := by
  apply multiply_left_cancel (powerOrdinalExponent minusOne e)
  · exact h.left
  calc
    powerOrdinalExponent minusOne e * divide one (powerOrdinalExponent minusOne e) h = one := divide_correct one (powerOrdinalExponent minusOne e) h
    _ = powerOrdinalExponent minusOne e * powerOrdinalExponent minusOne e := (powerOrdinalExponent_minusOne_square e).symm

theorem power_minusOne_negative (e : OrdinalNatural.Peano)
    (h : ValidPowerCondition minusOne (negative e) = true) :
    power minusOne (negative e) h = powerOrdinalExponent minusOne e := by
  change divide one (powerOrdinalExponent minusOne e) (isDivisible_one_powerOrdinalExponent_of_valid_negative minusOne e h) = powerOrdinalExponent minusOne e
  exact divide_one_powerOrdinalExponent_minusOne_eq e _

theorem powerOrdinalExponent_minusOne_successor_multiply (e : OrdinalNatural.Peano) :
    powerOrdinalExponent minusOne e.successor * minusOne = powerOrdinalExponent minusOne e := by
  change (powerOrdinalExponent minusOne e * minusOne) * minusOne = powerOrdinalExponent minusOne e
  rw [multiply_associative, minusOne_multiply_minusOne, one, multiply_positive_one]

theorem power_minusOne_successor (e : Peano)
    (h : ValidPowerCondition minusOne e = true)
    (hs : ValidPowerCondition minusOne (successor e) = true) :
    power minusOne (successor e) hs = power minusOne e h * minusOne := by
  cases e with
  | zero =>
      change minusOne = one * minusOne
      rw [one_multiply]
  | positive n =>
      change powerOrdinalExponent minusOne n.successor = powerOrdinalExponent minusOne n * minusOne
      rfl
  | negative n =>
      cases n with
      | one =>
          rw [power_minusOne_negative]
          change one = minusOne * minusOne
          exact minusOne_multiply_minusOne.symm
      | successor n =>
          simp [successor]
          rw [power_minusOne_negative n, power_minusOne_negative n.successor h]
          exact (powerOrdinalExponent_minusOne_successor_multiply n).symm

theorem power_minusOne_predecessor (e : Peano)
    (h : ValidPowerCondition minusOne e = true)
    (hp : ValidPowerCondition minusOne (predecessor e) = true) :
    power minusOne (predecessor e) hp = power minusOne e h * minusOne := by
  cases e with
  | zero =>
      change power minusOne (negative OrdinalNatural.Peano.one) hp = one * minusOne
      rw [power_minusOne_negative, one_multiply]
      rfl
  | positive n =>
      cases n with
      | one =>
          change one = minusOne * minusOne
          exact minusOne_multiply_minusOne.symm
      | successor n =>
          change powerOrdinalExponent minusOne n = powerOrdinalExponent minusOne n.successor * minusOne
          exact (powerOrdinalExponent_minusOne_successor_multiply n).symm
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
        _ = power minusOne y h * one := by rw [one, multiply_positive_one]
        _ = power minusOne y h * power minusOne zero h2 := by rfl
  | positive n =>
      induction n with
      | one =>
          have h3 : ValidPowerCondition minusOne (y + positive OrdinalNatural.Peano.one) = true := by rw [add_positive_one]; exact validPowerCondition_minusOne _
          refine ⟨h3, ?_⟩
          revert h3
          rw [add_positive_one]
          intro h3
          calc
            power minusOne (successor y) h3 = power minusOne y h * minusOne := power_minusOne_successor y h h3
            _ = power minusOne y h * power minusOne (positive OrdinalNatural.Peano.one) h2 := by rfl
      | successor n ih =>
          have hprev : ValidPowerCondition minusOne (positive n) = true := validPowerCondition_minusOne _
          rcases ih hprev with ⟨hmid, hmid_eq⟩
          have h3 : ValidPowerCondition minusOne (y + positive n.successor) = true := by rw [add_positive_successor]; exact validPowerCondition_minusOne _
          refine ⟨h3, ?_⟩
          revert h3
          rw [add_positive_successor]
          intro h3
          calc
            power minusOne (successor (y + positive n)) h3 = power minusOne (y + positive n) hmid * minusOne := power_minusOne_successor (y + positive n) hmid h3
            _ = (power minusOne y h * power minusOne (positive n) hprev) * minusOne := by rw [hmid_eq]
            _ = power minusOne y h * (power minusOne (positive n) hprev * minusOne) := by rw [multiply_associative]
            _ = power minusOne y h * power minusOne (positive n.successor) h2 := by rfl
  | negative n =>
      induction n with
      | one =>
          have h3 : ValidPowerCondition minusOne (y + negative OrdinalNatural.Peano.one) = true := by rw [add_negative_one]; exact validPowerCondition_minusOne _
          refine ⟨h3, ?_⟩
          revert h3
          rw [add_negative_one]
          intro h3
          calc
            power minusOne (predecessor y) h3 = power minusOne y h * minusOne := power_minusOne_predecessor y h h3
            _ = power minusOne y h * power minusOne (negative OrdinalNatural.Peano.one) h2 := by
              rw [power_minusOne_negative]
              rfl
      | successor n ih =>
          have hprev : ValidPowerCondition minusOne (negative n) = true := validPowerCondition_minusOne _
          rcases ih hprev with ⟨hmid, hmid_eq⟩
          have h3 : ValidPowerCondition minusOne (y + negative n.successor) = true := by rw [add_negative_successor]; exact validPowerCondition_minusOne _
          refine ⟨h3, ?_⟩
          revert h3
          rw [add_negative_successor]
          intro h3
          calc
            power minusOne (predecessor (y + negative n)) h3 = power minusOne (y + negative n) hmid * minusOne := power_minusOne_predecessor (y + negative n) hmid h3
            _ = (power minusOne y h * power minusOne (negative n) hprev) * minusOne := by rw [hmid_eq]
            _ = power minusOne y h * (power minusOne (negative n) hprev * minusOne) := by rw [multiply_associative]
            _ = power minusOne y h * power minusOne (negative n.successor) h2 := by
              rw [power_minusOne_negative, power_minusOne_negative]
              rfl

theorem power_positive_eq_powerOrdinalExponent (a : Peano) (n : OrdinalNatural.Peano)
    (h : ValidPowerCondition a (positive n) = true) :
    power a (positive n) h = powerOrdinalExponent a n := by
  cases a with
  | zero =>
      induction n with
      | one => rfl
      | successor n ih =>
          change zero = powerOrdinalExponent zero n * zero
          rw [multiply_zero]
  | positive n => rfl
  | negative n => rfl

theorem power_eq_of_base_eq {a b e : Peano} (hab : a = b)
    (ha : ValidPowerCondition a e = true) (hb : ValidPowerCondition b e = true) :
    power a e ha = power b e hb := by
  subst hab
  rfl

theorem power_eq_of_exponent_eq {a e1 e2 : Peano} (he : e1 = e2)
    (h1 : ValidPowerCondition a e1 = true) (h2 : ValidPowerCondition a e2 = true) :
    power a e1 h1 = power a e2 h2 := by
  subst he
  rfl

theorem power_multiply_base_all (x y z : Peano)
    (h : Peano.ValidPowerCondition x z = true)
    (h2 : Peano.ValidPowerCondition y z = true) :
    ∃ h3, power (x * y) z h3 = power x z h * power y z h2 := by
  cases z with
  | positive zn =>
      refine ⟨rfl, ?_⟩
      rw [power_positive_eq_powerOrdinalExponent (x * y) zn rfl,
        power_positive_eq_powerOrdinalExponent x zn h,
        power_positive_eq_powerOrdinalExponent y zn h2]
      exact powerOrdinalExponent_multiply_base x y zn
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
              rw [power_zero, power_zero, power_zero, one, multiply_positive_one]
          | negative yn =>
              have hxy : positive xn * negative yn = negative (xn * yn) := multiply_positive_negative xn yn
              have h3 : ValidPowerCondition (positive xn * negative yn) zero = true := by
                rw [hxy]
                rfl
              refine ⟨h3, ?_⟩
              rw [power_zero, power_zero, power_zero, one, multiply_positive_one]
      | negative xn =>
          cases y with
          | zero => contradiction
          | positive yn =>
              have hxy : negative xn * positive yn = negative (xn * yn) := multiply_negative_positive xn yn
              have h3 : ValidPowerCondition (negative xn * positive yn) zero = true := by
                rw [hxy]
                rfl
              refine ⟨h3, ?_⟩
              rw [power_zero, power_zero, power_zero, one, multiply_positive_one]
          | negative yn =>
              have hxy : negative xn * negative yn = positive (xn * yn) := multiply_negative_negative xn yn
              have h3 : ValidPowerCondition (negative xn * negative yn) zero = true := by
                rw [hxy]
                rfl
              refine ⟨h3, ?_⟩
              rw [power_zero, power_zero, power_zero, one, multiply_positive_one]
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
                            = power one (negative zn) (validPowerCondition_one _) :=
                              power_eq_of_base_eq (multiply_positive_positive _ _) h3 (validPowerCondition_one _)
                        _ = power one (negative zn) h * power one (negative zn) h2 := by
                              rw [power_one, one_multiply]
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
                            = power minusOne (negative zn) (validPowerCondition_minusOne _) :=
                              power_eq_of_base_eq (multiply_positive_negative _ _) h3 (validPowerCondition_minusOne _)
                        _ = power one (negative zn) h * power minusOne (negative zn) h2 := by
                              rw [power_one, one_multiply]
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
                            = power minusOne (negative zn) (validPowerCondition_minusOne _) :=
                              power_eq_of_base_eq (multiply_negative_positive _ _) h3 (validPowerCondition_minusOne _)
                        _ = power minusOne (negative zn) h * power one (negative zn) h2 := by
                              rw [power_one, one, multiply_positive_one]
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
                            = power one (negative zn) (validPowerCondition_one _) :=
                              power_eq_of_base_eq (multiply_negative_negative _ _) h3 (validPowerCondition_one _)
                        _ = power minusOne (negative zn) h * power minusOne (negative zn) h2 := by
                              rw [power_one, power_minusOne_negative, powerOrdinalExponent_minusOne_square]
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
          rw [one_multiply]
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
              rw [one, multiply_positive_one]
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
              rw [zero_multiply]
          | positive xn =>
              change powerOrdinalExponent (positive xn) (yn + zn) = powerOrdinalExponent (positive xn) yn * powerOrdinalExponent (positive xn) zn
              exact powerOrdinalExponent_add (positive xn) yn zn
          | negative xn =>
              change powerOrdinalExponent (negative xn) (yn + zn) = powerOrdinalExponent (negative xn) yn * powerOrdinalExponent (negative xn) zn
              exact powerOrdinalExponent_add (negative xn) yn zn
      | negative zn =>
          cases x with
          | zero => contradiction
          | positive xn =>
              cases xn with
              | one =>
                  change ∃ h3, power one (positive yn + negative zn) h3 = power one (positive yn) h * power one (negative zn) h2
                  refine ⟨validPowerCondition_one _, ?_⟩
                  rw [power_one, power_one, power_one, one, multiply_positive_one]
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
              refine ⟨validPowerCondition_one _, ?_⟩
              rw [power_one, power_one, power_one, one, multiply_positive_one]
          | successor xn => contradiction
      | negative xn =>
          cases xn with
          | one =>
              exact power_add_minusOne (negative yn) z h h2
          | successor xn => contradiction

theorem division_reverses_multiplication (x y : Peano) (hy : y ≠ zero) :
    ∃ h, divide (y * x) y h = x := by
  let h : Divisible (y * x) y := ⟨hy, x, rfl⟩
  refine ⟨h, ?_⟩
  exact multiply_left_cancel y (divide (y * x) y h) x hy (divide_correct (y * x) y h)

/-- `tryDivide (b * a) b` recovers `a` when `b ≠ zero`. -/
theorem tryDivide_multiply (a b : Peano) (hb : b ≠ zero) :
    tryDivide (b * a) b = some a :=
  tryDivide_of_divide (division_reverses_multiplication a b hb)

theorem division_reverses_right_multiplication (x y : Peano) (hy : y ≠ zero) :
    ∃ h, divide (x * y) y h = x := by
  let h : Divisible (x * y) y := ⟨hy, x, multiply_commutative y x⟩
  refine ⟨h, ?_⟩
  apply multiply_left_cancel y (divide (x * y) y h) x hy
  calc
    y * divide (x * y) y h = x * y := divide_correct (x * y) y h
    _ = y * x := multiply_commutative x y

theorem divide_add_h (x y z : Peano) (h : Divisible x z) (h2 : Divisible y z) :
    Divisible (x + y) z := by
  exact ⟨h.left, divide x z h + divide y z h2, by
    calc
      z * (divide x z h + divide y z h2) = z * divide x z h + z * divide y z h2 := by
        rw [multiply_add]
      _ = x + y := by rw [divide_correct x z h, divide_correct y z h2]⟩

theorem divide_add (x y z : Peano) (h : Divisible x z) (h2 : Divisible y z) :
    ∃ h3 : Divisible (x + y) z, divide (x + y) z h3 = divide x z h + divide y z h2 := by
  let h3 : Divisible (x + y) z := divide_add_h x y z h h2
  exists h3
  apply multiply_left_cancel z
  · exact h.left
  calc
    z * divide (x + y) z h3 = x + y := divide_correct (x + y) z h3
    _ = z * (divide x z h + divide y z h2) := by
      rw [multiply_add, divide_correct x z h, divide_correct y z h2]

theorem divide_subtract_h (x y z : Peano) (h : Divisible x z) (h2 : Divisible y z) :
    Divisible (x - y) z := by
  exact ⟨h.left, divide x z h - divide y z h2, by
    calc
      z * (divide x z h - divide y z h2) = z * divide x z h - z * divide y z h2 := by
        rw [multiply_subtract]
      _ = x - y := by rw [divide_correct x z h, divide_correct y z h2]⟩

theorem divide_subtract (x y z : Peano) (h : Divisible x z) (h2 : Divisible y z) :
    ∃ h3 : Divisible (x - y) z, divide (x - y) z h3 = divide x z h - divide y z h2 := by
  let h3 : Divisible (x - y) z := divide_subtract_h x y z h h2
  exists h3
  apply multiply_left_cancel z
  · exact h.left
  calc
    z * divide (x - y) z h3 = x - y := divide_correct (x - y) z h3
    _ = z * (divide x z h - divide y z h2) := by
      rw [multiply_subtract, divide_correct x z h, divide_correct y z h2]

theorem divide_multiply_h (x y z : Peano) (h : Divisible y z) :
    Divisible (x * y) z := by
  exact ⟨h.left, x * divide y z h, by
    calc
      z * (x * divide y z h) = z * (divide y z h * x) := by
        rw [multiply_commutative x (divide y z h)]
      _ = z * divide y z h * x := by
        rw [← multiply_associative]
      _ = y * x := by
        rw [divide_correct y z h]
      _ = x * y := by
        rw [multiply_commutative]⟩

theorem divide_multiply (x y z : Peano) (h : Divisible y z) :
    ∃ h2, divide (x * y) z h2 = x * divide y z h := by
  let h2 : Divisible (x * y) z := divide_multiply_h x y z h
  exists h2
  apply multiply_left_cancel z
  · exact h.left
  calc
    z * divide (x * y) z h2 = x * y := divide_correct (x * y) z h2
    _ = y * x := by
      rw [multiply_commutative]
    _ = z * divide y z h * x := by
      rw [divide_correct y z h]
    _ = z * (divide y z h * x) := by
      rw [← multiply_associative]
    _ = z * (x * divide y z h) := by
      rw [multiply_commutative (divide y z h) x]

theorem multiply_ne_zero {x y : Peano} (hx : x ≠ zero) (hy : y ≠ zero) : x * y ≠ zero := by
  intro hxy
  cases (multiply_eq_zero_iff x y).mp hxy with
  | inl hx_zero => exact hx hx_zero
  | inr hy_zero => exact hy hy_zero

theorem divide_divide (x y z : Peano) (h : Divisible x y) (h2 : Divisible (divide x y h) z) :
    ∃ h3, divide (divide x y h) z h2 = divide x (y * z) h3 := by
  let q := divide (divide x y h) z h2
  have hyz : y * z ≠ zero := multiply_ne_zero h.left h2.left
  let h3 : Divisible x (y * z) := ⟨hyz, q, by
    calc
      (y * z) * q = y * (z * q) := by
        rw [multiply_associative]
      _ = y * divide x y h := by
        rw [divide_correct (divide x y h) z h2]
      _ = x := divide_correct x y h⟩
  exists h3
  apply multiply_left_cancel (y * z)
  · exact hyz
  calc
    (y * z) * divide (divide x y h) z h2 = y * (z * divide (divide x y h) z h2) := by
      rw [multiply_associative]
    _ = y * divide x y h := by
      rw [divide_correct (divide x y h) z h2]
    _ = x := divide_correct x y h
    _ = (y * z) * divide x (y * z) h3 := by
      rw [divide_correct x (y * z) h3]

theorem powerOrdinalExponent_zero_eq (e : OrdinalNatural.Peano) :
    powerOrdinalExponent zero e = zero := by
  induction e with
  | one => rfl
  | successor e ih =>
    show powerOrdinalExponent zero e * zero = zero
    rw [ih]
    exact multiply_zero zero

theorem powerOrdinalExponent_positive_eq (y_n e_n : OrdinalNatural.Peano) :
    powerOrdinalExponent (positive y_n) e_n = positive (y_n ^ e_n) := by
  induction e_n with
  | one => rfl
  | successor e_n ih =>
    show powerOrdinalExponent (positive y_n) e_n * positive y_n = positive (y_n ^ e_n.successor)
    rw [ih, multiply_positive_positive, OrdinalNatural.Peano.power_successor]

theorem fromCardinalNatural_one :
    fromCardinalNatural CardinalNatural.Peano.one = one := rfl

theorem fromCardinalNatural_power_zero_exponent {a : CardinalNatural.Peano}
    (ha : a ≠ CardinalNatural.Peano.zero) :
    fromCardinalNatural
        (CardinalNatural.Peano.power a CardinalNatural.Peano.zero (Or.inl ha)) =
      one := by
  cases a with
  | zero => exact False.elim (ha rfl)
  | successor _ => rfl

theorem fromCardinalNatural_power_zero_base {b : CardinalNatural.Peano}
    (hb : b ≠ CardinalNatural.Peano.zero) :
    fromCardinalNatural
        (CardinalNatural.Peano.power CardinalNatural.Peano.zero b (Or.inr hb)) =
      zero := by
  cases b with
  | zero => exact False.elim (hb rfl)
  | successor _ => rfl

theorem fromCardinalNatural_power_nonzero (a b : CardinalNatural.Peano)
    (ha : a ≠ CardinalNatural.Peano.zero) (hb : b ≠ CardinalNatural.Peano.zero) :
    fromCardinalNatural (CardinalNatural.Peano.power a b (Or.inl ha)) =
      powerOrdinalExponent (fromCardinalNatural a)
        (CardinalNatural.Peano.toOrdinal b hb) := by
  cases a with
  | zero => exact False.elim (ha rfl)
  | successor a' =>
    cases b with
    | zero => exact False.elim (hb rfl)
    | successor b' =>
      let n := CardinalNatural.Peano.toOrdinal a'.successor ha
      let e := CardinalNatural.Peano.toOrdinal b'.successor hb
      have hna : CardinalNatural.Peano.fromOrdinal n = a'.successor :=
        CardinalNatural.Peano.fromOrdinal_toOrdinal a'.successor ha
      have heb : CardinalNatural.Peano.fromOrdinal e = b'.successor :=
        CardinalNatural.Peano.fromOrdinal_toOrdinal b'.successor hb
      have hpow := CardinalNatural.Peano.fromOrdinal_power n e
      have hpow_base :
          CardinalNatural.Peano.power (CardinalNatural.Peano.fromOrdinal n)
              (CardinalNatural.Peano.fromOrdinal e)
              (Or.inl (CardinalNatural.Peano.fromOrdinal_ne_zero n)) =
            CardinalNatural.Peano.power a'.successor
              (CardinalNatural.Peano.fromOrdinal e)
              (Or.inl ha) :=
        CardinalNatural.Peano.eq_rec_power _ _ _ hna _ _
      have hpow_exp :
          CardinalNatural.Peano.power a'.successor
              (CardinalNatural.Peano.fromOrdinal e)
              (Or.inl ha) =
            CardinalNatural.Peano.power a'.successor b'.successor (Or.inl ha) :=
        CardinalNatural.Peano.eq_rec_power_exponent _ _ _ heb _ _
      have hpow' :
          CardinalNatural.Peano.power a'.successor b'.successor (Or.inl ha) =
            CardinalNatural.Peano.fromOrdinal (n ^ e) :=
        (hpow_base.trans hpow_exp).symm.trans hpow.symm
      have habs : fromCardinalNatural a'.successor = positive n := rfl
      rw [hpow', fromCardinalNatural_fromOrdinal, habs]
      exact (powerOrdinalExponent_positive_eq n e).symm

theorem absoluteValue_powerOrdinalExponent_negative (y e : OrdinalNatural.Peano) :
    absoluteValue (powerOrdinalExponent (negative y) e) = positive (y ^ e) := by
  induction e with
  | one => rfl
  | successor e ih =>
    change absoluteValue (powerOrdinalExponent (negative y) e * negative y) = positive (y ^ e.successor)
    rw [absoluteValue_multiply, ih]
    change positive (y ^ e) * positive y = positive (y ^ e.successor)
    rw [multiply_positive_positive, OrdinalNatural.Peano.power_successor]

theorem validPowerCondition_positive (a : Peano) (e : OrdinalNatural.Peano) :
    ValidPowerCondition a (positive e) = true := by
  cases a <;> rfl

theorem not_validPowerCondition_zero_negative (en : OrdinalNatural.Peano) :
    ¬ ValidPowerCondition zero (negative en) = true :=
  Bool.false_ne_true

theorem eq_one_or_minusOne_of_validPowerCondition_negative
    (a : Peano) (e : OrdinalNatural.Peano)
    (h : ValidPowerCondition a (negative e) = true) :
    a = one ∨ a = minusOne := by
  cases a with
  | zero => exact False.elim (not_validPowerCondition_zero_negative e h)
  | positive n =>
      cases n with
      | one => exact Or.inl rfl
      | successor _ => exact False.elim (Bool.false_ne_true h)
  | negative n =>
      cases n with
      | one => exact Or.inr rfl
      | successor _ => exact False.elim (Bool.false_ne_true h)

theorem validPowerCondition_of_one_or_minusOne (a e : Peano)
    (h : a = one ∨ a = minusOne) :
    ValidPowerCondition a e = true := by
  cases h with
  | inl hx =>
      subst hx
      exact validPowerCondition_one e
  | inr hx =>
      subst hx
      exact validPowerCondition_minusOne e

theorem validPowerCondition_zero_of_ne_zero (x : Peano) (hx : x ≠ zero) :
    ValidPowerCondition x zero = true := by
  cases x with
  | zero => exact False.elim (hx rfl)
  | positive _ => rfl
  | negative _ => rfl

theorem eq_one_or_minusOne_of_powerOrdinalExponent_unit (x : Peano) (e : OrdinalNatural.Peano)
    (h : powerOrdinalExponent x e = one ∨ powerOrdinalExponent x e = minusOne) :
    x = one ∨ x = minusOne := by
  cases x with
  | zero =>
      rw [powerOrdinalExponent_zero_eq] at h
      cases h with
      | inl hx => cases hx
      | inr hx => cases hx
  | positive n =>
      cases n with
      | one => exact Or.inl rfl
      | successor n' =>
          rw [powerOrdinalExponent_positive_eq] at h
          cases h with
          | inl hone =>
              injection hone with hpow
              exact False.elim (OrdinalNatural.Peano.not_lt_self _
                (hpow ▸ one_lt_successor_power n' e))
          | inr hminus =>
              cases hminus
  | negative n =>
      cases n with
      | one => exact Or.inr rfl
      | successor n' =>
          have habs : absoluteValue (powerOrdinalExponent (negative n'.successor) e) =
              positive (n'.successor ^ e) :=
            absoluteValue_powerOrdinalExponent_negative n'.successor e
          have hunit : absoluteValue (powerOrdinalExponent (negative n'.successor) e) =
              positive OrdinalNatural.Peano.one := by
            cases h with
            | inl hone => rw [hone]; rfl
            | inr hminus => rw [hminus]; rfl
          have heq : n'.successor ^ e = OrdinalNatural.Peano.one := by
            injection (habs.symm.trans hunit)
          exact False.elim (OrdinalNatural.Peano.not_lt_self _
            (heq ▸ one_lt_successor_power n' e))

theorem power_multiply (x y z : Peano)
    (h : ValidPowerCondition x y = true)
    (h2 : ValidPowerCondition (power x y h) z = true) :
    ∃ h3, power x (y * z) h3 = power (power x y h) z h2 := by
  cases y with
  | zero =>
      have h3 : ValidPowerCondition x (zero * z) = true := by
        simpa [zero_multiply] using h
      refine ⟨h3, ?_⟩
      calc
        power x (zero * z) h3 = power x zero h := by
          simp [zero_multiply]
        _ = one := power_zero x h
        _ = power one z (validPowerCondition_one z) :=
          (power_one z _).symm
        _ = power (power x zero h) z h2 :=
          power_eq_of_base_eq (power_zero x h).symm _ h2
  | positive yn =>
      cases z with
      | zero =>
          have hxne : x ≠ zero := by
            intro hx
            subst hx
            exact not_validPowerCondition_zero_zero h2
          have hz : ValidPowerCondition x zero = true :=
            validPowerCondition_zero_of_ne_zero x hxne
          have h3 : ValidPowerCondition x (positive yn * zero) = true := by
            simpa [multiply_zero] using hz
          refine ⟨h3, ?_⟩
          calc
            power x (positive yn * zero) h3 = power x zero hz := by
              simp [multiply_zero]
            _ = one := power_zero x hz
            _ = power (power x (positive yn) h) zero h2 :=
              (power_zero _ h2).symm
      | positive zn =>
          have h3 : ValidPowerCondition x (positive yn * positive zn) = true := by
            rw [multiply_positive_positive]
            rfl
          refine ⟨h3, ?_⟩
          revert h3
          rw [multiply_positive_positive]
          intro h3
          rw [power_positive_eq_powerOrdinalExponent x (yn * zn) h3,
            power_positive_eq_powerOrdinalExponent x yn h,
            power_positive_eq_powerOrdinalExponent (powerOrdinalExponent x yn) zn h2]
          exact powerOrdinalExponent_multiply x yn zn
      | negative zn =>
          have hunit_x : x = one ∨ x = minusOne :=
            eq_one_or_minusOne_of_powerOrdinalExponent_unit x yn (by
              have hunit :=
                eq_one_or_minusOne_of_validPowerCondition_negative
                  (power x (positive yn) h) zn h2
              rwa [power_positive_eq_powerOrdinalExponent x yn h] at hunit)
          have h3 : ValidPowerCondition x (positive yn * negative zn) = true := by
            rw [multiply_positive_negative]
            exact validPowerCondition_of_one_or_minusOne x (negative (yn * zn))
              hunit_x
          refine ⟨h3, ?_⟩
          cases hunit_x with
          | inl hx =>
              subst hx
              calc
                power one (positive yn * negative zn) h3 = one :=
                  power_one _ _
                _ = power one (negative zn) (validPowerCondition_one _) :=
                  (power_one _ _).symm
                _ = power (power one (positive yn) h) (negative zn) h2 :=
                  power_eq_of_base_eq (power_one (positive yn) h).symm _ h2
          | inr hx =>
              subst hx
              revert h3
              rw [multiply_positive_negative]
              intro h3
              have hinner : power minusOne (positive yn) h = powerOrdinalExponent minusOne yn :=
                power_positive_eq_powerOrdinalExponent minusOne yn h
              rw [power_minusOne_negative, powerOrdinalExponent_multiply]
              cases powerOrdinalExponent_minusOne_eq_one_or_minusOne yn with
              | inl hone =>
                  calc
                    powerOrdinalExponent (powerOrdinalExponent minusOne yn) zn = powerOrdinalExponent one zn := by
                      rw [hone]
                    _ = one := powerOrdinalExponent_one zn
                    _ = power one (negative zn) (validPowerCondition_one _) :=
                      (power_one _ _).symm
                    _ = power (power minusOne (positive yn) h) (negative zn) h2 :=
                      power_eq_of_base_eq (hinner.trans hone).symm _ h2
              | inr hminus =>
                  calc
                    powerOrdinalExponent (powerOrdinalExponent minusOne yn) zn =
                        powerOrdinalExponent minusOne zn := by
                      rw [hminus]
                    _ = power minusOne (negative zn)
                          (validPowerCondition_minusOne _) :=
                      (power_minusOne_negative zn _).symm
                    _ = power (power minusOne (positive yn) h) (negative zn) h2 :=
                      power_eq_of_base_eq (hinner.trans hminus).symm _ h2
  | negative yn =>
      have hunit_x : x = one ∨ x = minusOne :=
        eq_one_or_minusOne_of_validPowerCondition_negative x yn h
      cases z with
      | zero =>
          have hz : ValidPowerCondition x zero = true :=
            validPowerCondition_of_one_or_minusOne x zero hunit_x
          have h3 : ValidPowerCondition x (negative yn * zero) = true := by
            simpa [multiply_zero] using hz
          refine ⟨h3, ?_⟩
          calc
            power x (negative yn * zero) h3 = power x zero hz := by
              simp [multiply_zero]
            _ = one := power_zero x hz
            _ = power (power x (negative yn) h) zero h2 :=
              (power_zero _ h2).symm
      | positive zn =>
          have h3 : ValidPowerCondition x (negative yn * positive zn) = true := by
            rw [multiply_negative_positive]
            exact validPowerCondition_of_one_or_minusOne x (negative (yn * zn))
              hunit_x
          refine ⟨h3, ?_⟩
          cases hunit_x with
          | inl hx =>
              subst hx
              calc
                power one (negative yn * positive zn) h3 = one :=
                  power_one _ _
                _ = power one (positive zn) (validPowerCondition_one _) :=
                  (power_one _ _).symm
                _ = power (power one (negative yn) h) (positive zn) h2 :=
                  power_eq_of_base_eq (power_one (negative yn) h).symm _ h2
          | inr hx =>
              subst hx
              revert h3
              rw [multiply_negative_positive]
              intro h3
              have hinner : power minusOne (negative yn) h = powerOrdinalExponent minusOne yn :=
                power_minusOne_negative yn h
              rw [power_minusOne_negative, powerOrdinalExponent_multiply]
              have hrhs :
                  power (power minusOne (negative yn) h) (positive zn) h2 =
                    powerOrdinalExponent (power minusOne (negative yn) h) zn :=
                power_positive_eq_powerOrdinalExponent _ zn h2
              rw [hrhs, hinner]
      | negative zn =>
          have h3 : ValidPowerCondition x (negative yn * negative zn) = true := by
            rw [multiply_negative_negative]
            rfl
          refine ⟨h3, ?_⟩
          cases hunit_x with
          | inl hx =>
              subst hx
              calc
                power one (negative yn * negative zn) h3 = one :=
                  power_one _ _
                _ = power one (negative zn) (validPowerCondition_one _) :=
                  (power_one _ _).symm
                _ = power (power one (negative yn) h) (negative zn) h2 :=
                  power_eq_of_base_eq (power_one (negative yn) h).symm _ h2
          | inr hx =>
              subst hx
              revert h3
              rw [multiply_negative_negative]
              intro h3
              have hinner : power minusOne (negative yn) h = powerOrdinalExponent minusOne yn :=
                power_minusOne_negative yn h
              rw [power_positive_eq_powerOrdinalExponent, powerOrdinalExponent_multiply]
              cases powerOrdinalExponent_minusOne_eq_one_or_minusOne yn with
              | inl hone =>
                  calc
                    powerOrdinalExponent (powerOrdinalExponent minusOne yn) zn = powerOrdinalExponent one zn := by
                      rw [hone]
                    _ = one := powerOrdinalExponent_one zn
                    _ = power one (negative zn) (validPowerCondition_one _) :=
                      (power_one _ _).symm
                    _ = power (power minusOne (negative yn) h) (negative zn) h2 :=
                      power_eq_of_base_eq (hinner.trans hone).symm _ h2
              | inr hminus =>
                  calc
                    powerOrdinalExponent (powerOrdinalExponent minusOne yn) zn =
                        powerOrdinalExponent minusOne zn := by
                      rw [hminus]
                    _ = power minusOne (negative zn)
                          (validPowerCondition_minusOne _) :=
                      (power_minusOne_negative zn _).symm
                    _ = power (power minusOne (negative yn) h) (negative zn) h2 :=
                      power_eq_of_base_eq (hinner.trans hminus).symm _ h2

theorem multiply_power (x y z : Peano)
    (h : ValidPowerCondition x z = true)
    (h2 : ValidPowerCondition y z = true) :
    ∃ h3, power (x * y) z h3 = power x z h * power y z h2 :=
  power_multiply_base_all x y z h h2

def Even (a : Peano) : Prop := Divisible a two

def Odd (a : Peano) : Prop := ¬ Even a

def isEven : Peano → Bool
  | zero => true
  | positive n => OrdinalNatural.Peano.isEven n
  | negative n => OrdinalNatural.Peano.isEven n

def isOdd (a : Peano) : Bool := !isEven a

theorem isEven_zero : Even zero := by
  refine ⟨?_, zero, ?_⟩
  · intro h; cases h
  · exact multiply_zero two

theorem isOdd_ne_zero {e : Peano} (he : Odd e) : e ≠ zero := by
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
  have h := toInt_powerOrdinalExponent (positive a) b
  rw [powerOrdinalExponent_positive_eq] at h
  simp only [Peano.toInt] at h
  exact_mod_cast h

theorem isEven_successor (x : Peano) (h : Even x) : Odd (successor x) := by
  intro h_succ
  cases x with
  | zero =>
    have h_succ_is_one : successor zero = positive OrdinalNatural.Peano.one := rfl
    rw [h_succ_is_one] at h_succ
    exact OrdinalNatural.Peano.not_even_one (isDivisible_positive_positive h_succ)
  | positive p =>
    have h_ord : OrdinalNatural.Peano.Even p := isDivisible_positive_positive h
    have h_succ_pos : successor (positive p) = positive p.successor := rfl
    rw [h_succ_pos] at h_succ
    have h_ord_succ : OrdinalNatural.Peano.Even p.successor :=
      isDivisible_positive_positive h_succ
    exact OrdinalNatural.Peano.even_successor h_ord h_ord_succ
  | negative n =>
    cases n with
    | one =>
      exact OrdinalNatural.Peano.not_even_one (isDivisible_negative_positive h)
    | successor n' =>
      have h_ord : OrdinalNatural.Peano.Even n'.successor :=
        isDivisible_negative_positive h
      have h_succ_neg : successor (negative n'.successor) = negative n' := rfl
      rw [h_succ_neg] at h_succ
      have h_ord_pred : OrdinalNatural.Peano.Even n' :=
        isDivisible_negative_positive h_succ
      exact (OrdinalNatural.Peano.even_successor_iff n').mp h_ord h_ord_pred

theorem isOdd_successor (x : Peano) (h : Odd x) : Even (successor x) := by
  cases x with
  | zero =>
    have h_even_zero : Even zero := isEven_zero
    contradiction
  | positive p =>
    have h_ord : OrdinalNatural.Peano.Odd p := by
      intro h_even
      rcases h_even with ⟨c, hc⟩
      have h_even_pos : Even (positive p) := by
        refine ⟨?_, positive c, ?_⟩
        · intro hz; cases hz
        · show positive OrdinalNatural.Peano.two * positive c = positive p
          rw [multiply_positive_positive, hc]
      exact h h_even_pos
    have h_succ_pos : successor (positive p) = positive p.successor := rfl
    rw [h_succ_pos]
    have h_ord_succ : OrdinalNatural.Peano.Even p.successor :=
      OrdinalNatural.Peano.odd_successor h_ord
    rcases h_ord_succ with ⟨c, hc⟩
    refine ⟨?_, positive c, ?_⟩
    · intro hz; cases hz
    · show positive OrdinalNatural.Peano.two * positive c = positive p.successor
      rw [multiply_positive_positive, hc]
  | negative n =>
    cases n with
    | one =>
      have h_succ_neg : successor (negative OrdinalNatural.Peano.one) = zero := rfl
      rw [h_succ_neg]
      exact isEven_zero
    | successor n' =>
      have h_ord : OrdinalNatural.Peano.Odd n'.successor := by
        intro h_even
        rcases h_even with ⟨c, hc⟩
        have h_even_neg : Even (negative n'.successor) := by
          refine ⟨?_, negative c, ?_⟩
          · intro hz; cases hz
          · show positive OrdinalNatural.Peano.two * negative c = negative n'.successor
            rw [multiply_positive_negative, hc]
        exact h h_even_neg
      have h_succ_neg : successor (negative n'.successor) = negative n' := rfl
      rw [h_succ_neg]
      have h_ord_pred : OrdinalNatural.Peano.Even n' := by
        cases OrdinalNatural.Peano.even_or_odd n' with
        | inl h_even => exact h_even
        | inr h_odd =>
          exact False.elim (h_ord ((OrdinalNatural.Peano.even_successor_iff n').mpr h_odd))
      rcases h_ord_pred with ⟨c, hc⟩
      refine ⟨?_, negative c, ?_⟩
      · intro hz; cases hz
      · show positive OrdinalNatural.Peano.two * negative c = negative n'
        rw [multiply_positive_negative, hc]

theorem isEven_predecessor (x : Peano) (h : Even x) : Odd (predecessor x) := by
  intro h_pred
  have h_odd_x : Odd x := by
    rw [← successor_predecessor x]
    exact isEven_successor (predecessor x) h_pred
  exact h_odd_x h

theorem isOdd_predecessor (x : Peano) (h : Odd x) : Even (predecessor x) := by
  cases x with
  | zero =>
    have h_even_zero : Even zero := isEven_zero
    contradiction
  | positive p =>
    have h_ord : OrdinalNatural.Peano.Odd p := by
      intro h_even
      rcases h_even with ⟨c, hc⟩
      have h_even_pos : Even (positive p) := by
        refine ⟨?_, positive c, ?_⟩
        · intro hz; cases hz
        · show positive OrdinalNatural.Peano.two * positive c = positive p
          rw [multiply_positive_positive, hc]
      exact h h_even_pos
    cases p with
    | one =>
      have h_pred_pos_one : predecessor (positive OrdinalNatural.Peano.one) = zero := rfl
      rw [h_pred_pos_one]
      exact isEven_zero
    | successor p' =>
      have h_pred_pos_succ : predecessor (positive p'.successor) = positive p' := rfl
      rw [h_pred_pos_succ]
      have h_ord_pred : OrdinalNatural.Peano.Even p' := by
        cases OrdinalNatural.Peano.even_or_odd p' with
        | inl h_even => exact h_even
        | inr h_odd =>
          exact False.elim (h_ord ((OrdinalNatural.Peano.even_successor_iff p').mpr h_odd))
      rcases h_ord_pred with ⟨c, hc⟩
      refine ⟨?_, positive c, ?_⟩
      · intro hz; cases hz
      · show positive OrdinalNatural.Peano.two * positive c = positive p'
        rw [multiply_positive_positive, hc]
  | negative n =>
    have h_ord : OrdinalNatural.Peano.Odd n := by
      intro h_even
      rcases h_even with ⟨c, hc⟩
      have h_even_neg : Even (negative n) := by
        refine ⟨?_, negative c, ?_⟩
        · intro hz; cases hz
        · show positive OrdinalNatural.Peano.two * negative c = negative n
          rw [multiply_positive_negative, hc]
      exact h h_even_neg
    have h_pred_neg : predecessor (negative n) = negative n.successor := rfl
    rw [h_pred_neg]
    have h_ord_succ : OrdinalNatural.Peano.Even n.successor :=
      OrdinalNatural.Peano.odd_successor h_ord
    rcases h_ord_succ with ⟨c, hc⟩
    refine ⟨?_, negative c, ?_⟩
    · intro hz; cases hz
    · show positive OrdinalNatural.Peano.two * negative c = negative n.successor
      rw [multiply_positive_negative, hc]

theorem isEven_correct (x : Peano) : Even x ↔ isEven x := by
  cases x with
  | zero =>
    constructor
    · intro _; rfl
    · intro _; exact isEven_zero
  | positive n =>
    rw [isEven]
    constructor
    · intro h
      exact (OrdinalNatural.Peano.isEven_correct n).mp (isDivisible_positive_positive h)
    · intro h
      have h_ord : OrdinalNatural.Peano.Even n :=
        (OrdinalNatural.Peano.isEven_correct n).mpr h
      rcases h_ord with ⟨c, hc⟩
      refine ⟨?_, positive c, ?_⟩
      · intro hz; cases hz
      · show positive OrdinalNatural.Peano.two * positive c = positive n
        rw [multiply_positive_positive, hc]
  | negative n =>
    rw [isEven]
    constructor
    · intro h
      exact (OrdinalNatural.Peano.isEven_correct n).mp (isDivisible_negative_positive h)
    · intro h
      have h_ord : OrdinalNatural.Peano.Even n :=
        (OrdinalNatural.Peano.isEven_correct n).mpr h
      rcases h_ord with ⟨c, hc⟩
      refine ⟨?_, negative c, ?_⟩
      · intro hz; cases hz
      · show positive OrdinalNatural.Peano.two * negative c = negative n
        rw [multiply_positive_negative, hc]

theorem isOdd_correct (x : Peano) : Odd x ↔ isOdd x := by
  unfold Odd isOdd
  rw [isEven_correct]
  cases isEven x <;> simp

theorem even_negative_iff_even_positive (n : OrdinalNatural.Peano) :
    Even (negative n) ↔ Even (positive n) := by
  rw [isEven_correct, isEven_correct]
  rfl

theorem odd_negative_iff_odd_positive (n : OrdinalNatural.Peano) :
    Odd (negative n) ↔ Odd (positive n) := by
  unfold Odd
  rw [even_negative_iff_even_positive]

instance decidableEven (x : Peano) : Decidable (Even x) :=
  decidable_of_iff' (isEven x) (isEven_correct x)

instance decidableOdd (x : Peano) : Decidable (Odd x) :=
  decidable_of_iff' (isOdd x) (isOdd_correct x)

theorem powerOrdinalExponent_negative_eq_of_even {y e : OrdinalNatural.Peano}
    (he : Even (positive e)) :
    powerOrdinalExponent (negative y) e = positive (y ^ e) := by
  have h_ord : OrdinalNatural.Peano.Even e := isDivisible_positive_positive he
  rcases h_ord with ⟨c, hc⟩
  have hpow :
      powerOrdinalExponent (negative y) e =
        powerOrdinalExponent (powerOrdinalExponent (negative y) OrdinalNatural.Peano.two) c := by
    rw [← hc, powerOrdinalExponent_multiply]
  have htwo :
      powerOrdinalExponent (negative y) OrdinalNatural.Peano.two = positive (y * y) := by
    change negative y * negative y = positive (y * y)
    exact multiply_negative_negative y y
  rw [hpow, htwo, powerOrdinalExponent_positive_eq]
  apply congrArg positive
  have hyy : y ^ OrdinalNatural.Peano.two = y * y := by
    change y ^ OrdinalNatural.Peano.one * y = y * y
    rw [OrdinalNatural.Peano.power_one]
  rw [← hyy, ← OrdinalNatural.Peano.power_multiply, hc]

theorem powerOrdinalExponent_negative_eq_of_odd {y e : OrdinalNatural.Peano}
    (he : Odd (positive e)) :
    powerOrdinalExponent (negative y) e = negative (y ^ e) := by
  have h_ord : OrdinalNatural.Peano.Odd e := by
    intro h_even
    exact he
      ((isEven_correct (positive e)).mpr
        ((OrdinalNatural.Peano.isEven_correct e).mp h_even))
  cases e with
  | one =>
    change negative y = negative (y ^ OrdinalNatural.Peano.one)
    rw [OrdinalNatural.Peano.power_one]
  | successor e' =>
    have h_even_e' : OrdinalNatural.Peano.Even e' := by
      cases OrdinalNatural.Peano.even_or_odd e' with
      | inl h => exact h
      | inr h_odd =>
        exact False.elim (h_ord (OrdinalNatural.Peano.odd_successor h_odd))
    have he_even : Even (positive e') :=
      (isEven_correct (positive e')).mpr
        ((OrdinalNatural.Peano.isEven_correct e').mp h_even_e')
    change powerOrdinalExponent (negative y) e' * negative y = negative (y ^ e'.successor)
    rw [powerOrdinalExponent_negative_eq_of_even he_even, OrdinalNatural.Peano.power_successor,
      multiply_positive_negative]

theorem exists_power_of_tryPower {x y z : Peano} (h : x ≠ zero ∨ y ≠ zero)
    (htry : tryPower x y h = some z) :
    ∃ h2, power x y h2 = z := by
  cases y with
  | zero =>
    cases x with
    | zero =>
      cases h with
      | inl hx => exact False.elim (hx rfl)
      | inr hy => exact False.elim (hy rfl)
    | positive xn =>
      have : tryPower (positive xn) zero h = some one := rfl
      rw [this] at htry
      injection htry with hz
      subst hz
      exact ⟨rfl, rfl⟩
    | negative xn =>
      have : tryPower (negative xn) zero h = some one := rfl
      rw [this] at htry
      injection htry with hz
      subst hz
      exact ⟨rfl, rfl⟩
  | positive yn =>
    have htry' : tryPower x (positive yn) h = some (powerOrdinalExponent x yn) := by
      cases x <;> rfl
    rw [htry'] at htry
    injection htry with hz
    subst hz
    refine ⟨validPowerCondition_positive x yn, ?_⟩
    cases x with
    | zero =>
      change zero = powerOrdinalExponent zero yn
      exact (powerOrdinalExponent_zero_eq yn).symm
    | positive _ => rfl
    | negative _ => rfl
  | negative yn =>
    have htry' : tryPower x (negative yn) h = tryDivide one (powerOrdinalExponent x yn) :=
      tryPower_negative x yn h
    rw [htry'] at htry
    cases x with
    | zero =>
      rw [powerOrdinalExponent_zero_eq] at htry
      cases htry
    | positive xn =>
      cases xn with
      | one =>
        obtain ⟨hdiv, heq⟩ := exists_divide_of_tryDivide htry
        have h2 : ValidPowerCondition one (negative yn) = true :=
          validPowerCondition_one (negative yn)
        refine ⟨h2, ?_⟩
        rw [← heq]
        rfl
      | successor xn' =>
        obtain ⟨hdiv, _⟩ := exists_divide_of_tryDivide htry
        rw [powerOrdinalExponent_positive_eq] at hdiv
        exact False.elim (not_divisible_one_of_positive_gt_one _
          (one_lt_successor_power xn' yn) hdiv)
    | negative xn =>
      cases xn with
      | one =>
        obtain ⟨hdiv, heq⟩ := exists_divide_of_tryDivide htry
        have h2 : ValidPowerCondition minusOne (negative yn) = true :=
          validPowerCondition_minusOne (negative yn)
        refine ⟨h2, ?_⟩
        rw [← heq]
        rfl
      | successor xn' =>
        obtain ⟨hdiv, _⟩ := exists_divide_of_tryDivide htry
        cases OrdinalNatural.Peano.even_or_odd yn with
        | inl heven_ord =>
          have heven : Even (positive yn) :=
            (isEven_correct (positive yn)).mpr
              ((OrdinalNatural.Peano.isEven_correct yn).mp heven_ord)
          rw [powerOrdinalExponent_negative_eq_of_even heven] at hdiv
          exact False.elim (not_divisible_one_of_positive_gt_one _
            (one_lt_successor_power xn' yn) hdiv)
        | inr hodd_ord =>
          have hodd : Odd (positive yn) := by
            intro heven
            exact hodd_ord
              ((OrdinalNatural.Peano.isEven_correct yn).mpr
                ((isEven_correct (positive yn)).mp heven))
          rw [powerOrdinalExponent_negative_eq_of_odd hodd] at hdiv
          exact False.elim (not_divisible_one_of_negative_gt_one _
            (one_lt_successor_power xn' yn) hdiv)

theorem ne_zero_or_of_validPowerCondition {x y : Peano}
    (h : ValidPowerCondition x y = true) : x ≠ zero ∨ y ≠ zero := by
  cases y with
  | zero =>
    cases x with
    | zero => exact False.elim (not_validPowerCondition_zero_zero h)
    | positive _ => exact Or.inl (fun hz => by cases hz)
    | negative _ => exact Or.inl (fun hz => by cases hz)
  | positive _ => exact Or.inr (fun hz => by cases hz)
  | negative yn =>
    cases x with
    | zero => exact False.elim (not_validPowerCondition_zero_negative yn h)
    | positive _ => exact Or.inl (fun hz => by cases hz)
    | negative _ => exact Or.inl (fun hz => by cases hz)

theorem exists_tryPower_of_power {x y z : Peano}
    (hpow : ∃ h, power x y h = z) :
    ∃ h2, tryPower x y h2 = some z := by
  obtain ⟨h, heq⟩ := hpow
  have h2 : x ≠ zero ∨ y ≠ zero := ne_zero_or_of_validPowerCondition h
  refine ⟨h2, ?_⟩
  cases y with
  | zero =>
    have hpow_eq : power x zero h = one := power_zero x h
    have htry_eq : tryPower x zero h2 = some one := by
      cases x with
      | zero =>
        cases h2 with
        | inl hx => exact False.elim (hx rfl)
        | inr hy => exact False.elim (hy rfl)
      | positive _ => rfl
      | negative _ => rfl
    rw [htry_eq, ← hpow_eq, heq]
  | positive yn =>
    have hpow_eq : power x (positive yn) h = powerOrdinalExponent x yn :=
      power_positive_eq_powerOrdinalExponent x yn h
    have htry_eq : tryPower x (positive yn) h2 = some (powerOrdinalExponent x yn) := by
      cases x <;> rfl
    rw [htry_eq, ← hpow_eq, heq]
  | negative yn =>
    have hdiv : Divisible one (powerOrdinalExponent x yn) :=
      isDivisible_one_powerOrdinalExponent_of_valid_negative x yn h
    have hpow_eq : power x (negative yn) h = divide one (powerOrdinalExponent x yn) hdiv := by
      cases x with
      | zero => exact False.elim (not_validPowerCondition_zero_negative yn h)
      | positive xn =>
        cases xn with
        | one => rfl
        | successor _ => contradiction
      | negative xn =>
        cases xn with
        | one => rfl
        | successor _ => contradiction
    have htry_eq : tryPower x (negative yn) h2 = tryDivide one (powerOrdinalExponent x yn) :=
      tryPower_negative x yn h2
    rw [htry_eq, ← heq, hpow_eq]
    exact tryDivide_of_divide ⟨hdiv, rfl⟩

theorem powerOrdinalExponent_negative_injective
    (a b en : OrdinalNatural.Peano)
    (h : powerOrdinalExponent (negative a) en = powerOrdinalExponent (negative b) en) :
    a = b := by
  have habs := congrArg absoluteValue h
  rw [absoluteValue_powerOrdinalExponent_negative, absoluteValue_powerOrdinalExponent_negative] at habs
  injection habs with hpow
  exact OrdinalNatural.Peano.power_cancel_left en a b hpow

def Power (e x : Peano) : Prop := ∃ y h, power y e h = x

theorem not_isPower_negative_zero (e : OrdinalNatural.Peano) :
    ¬ Power (negative e) zero := by
  intro hpow
  rcases hpow with ⟨y, hy, hyzero⟩
  cases y with
  | zero => contradiction
  | positive n =>
      cases n with
      | one =>
          change power one (negative e) hy = zero at hyzero
          rw [power_one] at hyzero
          cases hyzero
      | successor n => contradiction
  | negative n =>
      cases n with
      | one =>
          change power minusOne (negative e) hy = zero at hyzero
          rw [power_minusOne_negative] at hyzero
          cases powerOrdinalExponent_minusOne_eq_one_or_minusOne e with
          | inl hone =>
              rw [hone] at hyzero
              cases hyzero
          | inr hminus =>
              rw [hminus] at hyzero
              cases hyzero
      | successor n => contradiction

theorem powerOrdinalExponent_minusOne_eq_of_even_negative {e : OrdinalNatural.Peano}
    (he : Even (negative e)) :
    powerOrdinalExponent minusOne e = one := by
  have he_pos : Even (positive e) :=
    (isEven_correct (positive e)).mpr ((isEven_correct (negative e)).mp he)
  rw [minusOne, powerOrdinalExponent_negative_eq_of_even he_pos, OrdinalNatural.Peano.one_power]
  rfl

theorem powerOrdinalExponent_minusOne_eq_of_odd_negative {e : OrdinalNatural.Peano}
    (he : Odd (negative e)) :
    powerOrdinalExponent minusOne e = minusOne := by
  have he_pos : Odd (positive e) := by
    intro h_even_pos
    exact he
      ((isEven_correct (negative e)).mpr
        ((isEven_correct (positive e)).mp h_even_pos))
  rw [minusOne, powerOrdinalExponent_negative_eq_of_odd he_pos, OrdinalNatural.Peano.one_power]

theorem ordinalPower_of_Power_positive_positive {e a : OrdinalNatural.Peano}
    (h : Power (positive e) (positive a)) : OrdinalNatural.Peano.Power e a := by
  rcases h with ⟨y, hy, hyeq⟩
  cases y with
  | zero =>
      cases hyeq
  | positive y' =>
      refine ⟨y', ?_⟩
      have hyeq' : positive (y' ^ e) = positive a := by
        rw [← powerOrdinalExponent_positive_eq y' e]
        exact hyeq
      injection hyeq'
  | negative y' =>
      cases OrdinalNatural.Peano.even_or_odd e with
      | inl heven_ord =>
          have heven : Even (positive e) :=
            (isEven_correct (positive e)).mpr
              ((OrdinalNatural.Peano.isEven_correct e).mp heven_ord)
          refine ⟨y', ?_⟩
          have hyeq' : positive (y' ^ e) = positive a := by
            rw [← powerOrdinalExponent_negative_eq_of_even heven]
            exact hyeq
          injection hyeq'
      | inr hodd_ord =>
          have hodd : Odd (positive e) := by
            intro heven
            exact hodd_ord
              ((OrdinalNatural.Peano.isEven_correct e).mpr
                ((isEven_correct (positive e)).mp heven))
          change powerOrdinalExponent (negative y') e = positive a at hyeq
          rw [powerOrdinalExponent_negative_eq_of_odd hodd] at hyeq
          cases hyeq

theorem ordinalPower_of_Power_positive_negative_odd {e a : OrdinalNatural.Peano}
    (h : Power (positive e) (negative a)) (he : Odd (positive e)) :
    OrdinalNatural.Peano.Power e a := by
  rcases h with ⟨y, hy, hyeq⟩
  cases y with
  | zero =>
      cases hyeq
  | positive y' =>
      have : power (positive y') (positive e) hy = positive (y' ^ e) :=
        powerOrdinalExponent_positive_eq y' e
      rw [this] at hyeq
      cases hyeq
  | negative y' =>
      have hpow : powerOrdinalExponent (negative y') e = negative (y' ^ e) :=
        powerOrdinalExponent_negative_eq_of_odd he
      change powerOrdinalExponent (negative y') e = negative a at hyeq
      rw [hpow] at hyeq
      refine ⟨y', ?_⟩
      injection hyeq

theorem not_Power_positive_even_negative {e a : OrdinalNatural.Peano}
    (he : Even (positive e)) : ¬ Power (positive e) (negative a) := by
  intro h
  rcases h with ⟨y, hy, hyeq⟩
  cases y with
  | zero =>
      cases hyeq
  | positive y' =>
      have : power (positive y') (positive e) hy = positive (y' ^ e) :=
        powerOrdinalExponent_positive_eq y' e
      rw [this] at hyeq
      cases hyeq
  | negative y' =>
      have hpow : powerOrdinalExponent (negative y') e = positive (y' ^ e) :=
        powerOrdinalExponent_negative_eq_of_even he
      change powerOrdinalExponent (negative y') e = negative a at hyeq
      rw [hpow] at hyeq
      cases hyeq

theorem not_Power_negative_positive_successor {e a : OrdinalNatural.Peano} :
    ¬ Power (negative e) (positive a.successor) := by
  intro h
  rcases h with ⟨y, hy, hyeq⟩
  cases y with
  | zero =>
      exact False.elim (not_validPowerCondition_zero_negative e hy)
  | positive y' =>
      cases y' with
      | one =>
          change power one (negative e) hy = positive a.successor at hyeq
          rw [power_one] at hyeq
          cases hyeq
      | successor _ =>
          contradiction
  | negative y' =>
      cases y' with
      | one =>
          change power minusOne (negative e) hy = positive a.successor at hyeq
          rw [power_minusOne_negative] at hyeq
          cases powerOrdinalExponent_minusOne_eq_one_or_minusOne e with
          | inl hone =>
              rw [hone] at hyeq
              cases hyeq
          | inr hminus =>
              rw [hminus] at hyeq
              cases hyeq
      | successor _ =>
          contradiction

theorem not_Power_negative_negative_successor {e a : OrdinalNatural.Peano} :
    ¬ Power (negative e) (negative a.successor) := by
  intro h
  rcases h with ⟨y, hy, hyeq⟩
  cases y with
  | zero =>
      exact False.elim (not_validPowerCondition_zero_negative e hy)
  | positive y' =>
      cases y' with
      | one =>
          change power one (negative e) hy = negative a.successor at hyeq
          rw [power_one] at hyeq
          cases hyeq
      | successor _ =>
          contradiction
  | negative y' =>
      cases y' with
      | one =>
          change power minusOne (negative e) hy = negative a.successor at hyeq
          rw [power_minusOne_negative] at hyeq
          cases powerOrdinalExponent_minusOne_eq_one_or_minusOne e with
          | inl hone =>
              rw [hone] at hyeq
              cases hyeq
          | inr hminus =>
              rw [hminus] at hyeq
              cases hyeq
      | successor _ =>
          contradiction

theorem not_Power_minusOne_even_negative {e : OrdinalNatural.Peano}
    (he : Even (negative e)) : ¬ Power (negative e) minusOne := by
  intro h
  rcases h with ⟨y, hy, hyeq⟩
  cases y with
  | zero =>
      exact False.elim (not_validPowerCondition_zero_negative e hy)
  | positive y' =>
      cases y' with
      | one =>
          change power one (negative e) hy = minusOne at hyeq
          rw [power_one] at hyeq
          cases hyeq
      | successor _ =>
          contradiction
  | negative y' =>
      cases y' with
      | one =>
          change power minusOne (negative e) hy = minusOne at hyeq
          rw [power_minusOne_negative] at hyeq
          have hone : powerOrdinalExponent minusOne e = one :=
            powerOrdinalExponent_minusOne_eq_of_even_negative he
          rw [hone] at hyeq
          cases hyeq
      | successor _ =>
          contradiction

theorem even_of_not_isOdd {e : Peano} (h : ¬ isOdd e = true) : Even e := by
  have hev : isEven e = true := by
    simp [isOdd] at h
    cases h_is : isEven e with
    | true => rfl
    | false => simp [h_is] at h
  exact (isEven_correct e).mpr hev

def tryPrincipalRoot (e a : Peano) : Option Peano :=
  match a, e with
  | _, zero => none
  | zero, positive _ => some zero
  | zero, negative _ => none
  | positive a', positive e' =>
      (OrdinalNatural.Peano.tryRoot e' a').map positive
  | negative a', positive e' =>
      if isOdd (positive e') then
        (OrdinalNatural.Peano.tryRoot e' a').map negative
      else
        none
  | positive OrdinalNatural.Peano.one, negative _ => some one
  | negative OrdinalNatural.Peano.one, negative e' =>
      if isOdd (negative e') then
        some minusOne
      else
        none
  | positive (OrdinalNatural.Peano.successor _), negative _ => none
  | negative (OrdinalNatural.Peano.successor _), negative _ => none

def principalRoot (e a : Peano) (h : e ≠ zero ∧ Power e a) : Peano :=
  match a, e with
  | zero, _ => zero
  | positive a', positive e' =>
      positive (OrdinalNatural.Peano.root e' a'
        (ordinalPower_of_Power_positive_positive h.2))
  | negative a', positive e' =>
      if hodd : isOdd (positive e') then
        negative (OrdinalNatural.Peano.root e' a'
          (ordinalPower_of_Power_positive_negative_odd h.2
            ((isOdd_correct (positive e')).mpr hodd)))
      else
        False.elim (not_Power_positive_even_negative (e := e') (a := a')
          (even_of_not_isOdd hodd) h.2)
  | positive OrdinalNatural.Peano.one, negative _ => one
  | negative OrdinalNatural.Peano.one, negative e' =>
      if hodd : isOdd (negative e') then
        minusOne
      else
        False.elim (not_Power_minusOne_even_negative (e := e')
          (even_of_not_isOdd hodd) h.2)
  | positive (OrdinalNatural.Peano.successor a'), negative e' =>
      False.elim (not_Power_negative_positive_successor (e := e') (a := a') h.2)
  | negative (OrdinalNatural.Peano.successor a'), negative e' =>
      False.elim (not_Power_negative_negative_successor (e := e') (a := a') h.2)
  | _, zero => False.elim (h.1 rfl)

theorem exists_principalRoot_of_tryPrincipalRoot {x y z : Peano}
    (h : tryPrincipalRoot x y = some z) :
    ∃ h', principalRoot x y h' = z := by
  cases y with
  | zero =>
      cases x with
      | zero =>
          simp only [tryPrincipalRoot] at h
          cases h
      | positive xn =>
          simp only [tryPrincipalRoot] at h
          injection h with hz
          subst hz
          have hx : positive xn ≠ zero := fun hz => by cases hz
          have hpow : Power (positive xn) zero :=
            ⟨zero, validPowerCondition_positive zero xn, rfl⟩
          exact ⟨⟨hx, hpow⟩, rfl⟩
      | negative xn =>
          simp only [tryPrincipalRoot] at h
          cases h
  | positive yn =>
      cases x with
      | zero =>
          simp only [tryPrincipalRoot] at h
          cases h
      | positive xn =>
          cases htry : OrdinalNatural.Peano.tryRoot xn yn with
          | none =>
              simp only [tryPrincipalRoot, htry, Option.map_none] at h
              cases h
          | some z' =>
              simp only [tryPrincipalRoot, htry, Option.map_some] at h
              injection h with hz
              subst hz
              obtain ⟨hord, hroot⟩ := OrdinalNatural.Peano.exists_root_of_tryRoot htry
              have hx : positive xn ≠ zero := fun hz => by cases hz
              have hzpow : z' ^ xn = yn := by
                rw [← hroot]
                exact OrdinalNatural.Peano.root_correct xn yn hord
              have hpow : Power (positive xn) (positive yn) :=
                ⟨positive z', validPowerCondition_positive (positive z') xn, by
                  change powerOrdinalExponent (positive z') xn = positive yn
                  rw [powerOrdinalExponent_positive_eq, hzpow]⟩
              refine ⟨⟨hx, hpow⟩, ?_⟩
              simp only [principalRoot]
              exact congrArg positive (by
                have hord' : OrdinalNatural.Peano.Power xn yn :=
                  ordinalPower_of_Power_positive_positive hpow
                exact OrdinalNatural.Peano.power_cancel_left xn
                  (OrdinalNatural.Peano.root xn yn hord') z'
                  ((OrdinalNatural.Peano.root_correct xn yn hord').trans hzpow.symm))
      | negative xn =>
          cases yn with
          | one =>
              simp only [tryPrincipalRoot] at h
              injection h with hz
              subst hz
              have hx : negative xn ≠ zero := fun hz => by cases hz
              have hpow : Power (negative xn) one :=
                ⟨one, validPowerCondition_one (negative xn),
                  power_one (negative xn) (validPowerCondition_one _)⟩
              exact ⟨⟨hx, hpow⟩, rfl⟩
          | successor yn' =>
              simp only [tryPrincipalRoot] at h
              cases h
  | negative yn =>
      cases x with
      | zero =>
          simp only [tryPrincipalRoot] at h
          cases h
      | positive xn =>
          by_cases hodd : isOdd (positive xn) = true
          · cases htry : OrdinalNatural.Peano.tryRoot xn yn with
            | none =>
                simp only [tryPrincipalRoot, hodd, ↓reduceIte, htry, Option.map_none] at h
                cases h
            | some z' =>
                simp only [tryPrincipalRoot, hodd, ↓reduceIte, htry, Option.map_some] at h
                injection h with hz
                subst hz
                obtain ⟨hord, hroot⟩ := OrdinalNatural.Peano.exists_root_of_tryRoot htry
                have hx : positive xn ≠ zero := fun hz => by cases hz
                have he_odd : Odd (positive xn) := (isOdd_correct (positive xn)).mpr hodd
                have hzpow : z' ^ xn = yn := by
                  rw [← hroot]
                  exact OrdinalNatural.Peano.root_correct xn yn hord
                have hpow : Power (positive xn) (negative yn) :=
                  ⟨negative z', validPowerCondition_positive (negative z') xn, by
                    change powerOrdinalExponent (negative z') xn = negative yn
                    rw [powerOrdinalExponent_negative_eq_of_odd he_odd, hzpow]⟩
                refine ⟨⟨hx, hpow⟩, ?_⟩
                simp only [principalRoot, hodd, ↓reduceDIte]
                exact congrArg negative (by
                  have hord' : OrdinalNatural.Peano.Power xn yn :=
                    ordinalPower_of_Power_positive_negative_odd hpow he_odd
                  exact OrdinalNatural.Peano.power_cancel_left xn
                    (OrdinalNatural.Peano.root xn yn hord') z'
                    ((OrdinalNatural.Peano.root_correct xn yn hord').trans hzpow.symm))
          · simp only [tryPrincipalRoot, hodd] at h
            cases h
      | negative xn =>
          cases yn with
          | one =>
              by_cases hodd : isOdd (negative xn) = true
              · simp only [tryPrincipalRoot, hodd, ↓reduceIte] at h
                injection h with hz
                subst hz
                have hx : negative xn ≠ zero := fun hz => by cases hz
                have he_odd : Odd (negative xn) := (isOdd_correct (negative xn)).mpr hodd
                have hpow : Power (negative xn) minusOne :=
                  ⟨minusOne, validPowerCondition_minusOne (negative xn), by
                    rw [power_minusOne_negative]
                    exact powerOrdinalExponent_minusOne_eq_of_odd_negative he_odd⟩
                refine ⟨⟨hx, hpow⟩, ?_⟩
                simp only [principalRoot, hodd, ↓reduceDIte]
              · simp only [tryPrincipalRoot, hodd] at h
                cases h
          | successor yn' =>
              simp only [tryPrincipalRoot] at h
              cases h

theorem tryPrincipalRoot_eq_some_principalRoot (x y : Peano)
    (h : x ≠ zero ∧ Power x y) :
    tryPrincipalRoot x y = some (principalRoot x y h) := by
  cases y with
  | zero =>
      cases x with
      | zero => exact False.elim (h.1 rfl)
      | positive xn =>
          simp only [tryPrincipalRoot, principalRoot]
      | negative xn =>
          exact False.elim (not_isPower_negative_zero xn h.2)
  | positive yn =>
      cases x with
      | zero => exact False.elim (h.1 rfl)
      | positive xn =>
          have hord : OrdinalNatural.Peano.Power xn yn :=
            ordinalPower_of_Power_positive_positive h.2
          have htry : OrdinalNatural.Peano.tryRoot xn yn =
              some (OrdinalNatural.Peano.root xn yn hord) :=
            OrdinalNatural.Peano.tryRoot_eq_some_root xn yn hord
          simp only [tryPrincipalRoot, principalRoot, htry, Option.map_some]
      | negative xn =>
          cases yn with
          | one =>
              simp only [tryPrincipalRoot, principalRoot]
          | successor yn' =>
              exact False.elim (not_Power_negative_positive_successor (e := xn) (a := yn') h.2)
  | negative yn =>
      cases x with
      | zero => exact False.elim (h.1 rfl)
      | positive xn =>
          by_cases hodd : isOdd (positive xn) = true
          · have he_odd : Odd (positive xn) := (isOdd_correct (positive xn)).mpr hodd
            have hord : OrdinalNatural.Peano.Power xn yn :=
              ordinalPower_of_Power_positive_negative_odd h.2 he_odd
            have htry : OrdinalNatural.Peano.tryRoot xn yn =
                some (OrdinalNatural.Peano.root xn yn hord) :=
              OrdinalNatural.Peano.tryRoot_eq_some_root xn yn hord
            simp only [tryPrincipalRoot, principalRoot, hodd, ↓reduceIte, ↓reduceDIte,
              htry, Option.map_some]
          · exact False.elim (not_Power_positive_even_negative (e := xn) (a := yn)
                (even_of_not_isOdd hodd) h.2)
      | negative xn =>
          cases yn with
          | one =>
              by_cases hodd : isOdd (negative xn) = true
              · simp only [tryPrincipalRoot, principalRoot, hodd, ↓reduceIte, ↓reduceDIte]
              · exact False.elim (not_Power_minusOne_even_negative (e := xn)
                    (even_of_not_isOdd hodd) h.2)
          | successor yn' =>
              exact False.elim (not_Power_negative_negative_successor (e := xn) (a := yn') h.2)

theorem tryPrincipalRoot_of_exists_principalRoot {x y z : Peano}
    (h : ∃ h', principalRoot x y h' = z) :
    tryPrincipalRoot x y = some z := by
  rcases h with ⟨h', hz⟩
  rw [← hz]
  exact tryPrincipalRoot_eq_some_principalRoot x y h'

theorem principalRoot_isPower (e a : Peano) (h : e ≠ zero ∧ Power e a) :
    ∃ h2, power (principalRoot e a h) e h2 = a := by
  cases a with
  | zero =>
      cases e with
      | zero => exact False.elim (h.1 rfl)
      | positive en =>
          refine ⟨rfl, ?_⟩
          simp only [principalRoot]
          rfl
      | negative en =>
          exact False.elim (not_isPower_negative_zero en h.2)
  | positive an =>
      cases e with
      | zero => exact False.elim (h.1 rfl)
      | positive en =>
          refine ⟨validPowerCondition_positive (positive (OrdinalNatural.Peano.root en an
            (ordinalPower_of_Power_positive_positive h.2))) en, ?_⟩
          simp only [principalRoot]
          change powerOrdinalExponent (positive (OrdinalNatural.Peano.root en an
            (ordinalPower_of_Power_positive_positive h.2))) en = positive an
          rw [powerOrdinalExponent_positive_eq]
          exact congrArg positive (OrdinalNatural.Peano.root_correct en an
            (ordinalPower_of_Power_positive_positive h.2))
      | negative en =>
          cases an with
          | one =>
              refine ⟨validPowerCondition_one (negative en), ?_⟩
              simp only [principalRoot]
              exact power_one (negative en) _
          | successor an' =>
              exact False.elim (not_Power_negative_positive_successor (e := en) (a := an') h.2)
  | negative an =>
      cases e with
      | zero => exact False.elim (h.1 rfl)
      | positive en =>
          by_cases hodd : isOdd (positive en) = true
          · have he_odd : Odd (positive en) := (isOdd_correct (positive en)).mpr hodd
            simp only [principalRoot, hodd, ↓reduceDIte]
            refine ⟨validPowerCondition_positive (negative (OrdinalNatural.Peano.root en an
              (ordinalPower_of_Power_positive_negative_odd h.2
                ((isOdd_correct (positive en)).mpr hodd)))) en, ?_⟩
            change powerOrdinalExponent (negative (OrdinalNatural.Peano.root en an
              (ordinalPower_of_Power_positive_negative_odd h.2
                ((isOdd_correct (positive en)).mpr hodd)))) en = negative an
            rw [powerOrdinalExponent_negative_eq_of_odd he_odd]
            exact congrArg negative (OrdinalNatural.Peano.root_correct en an
              (ordinalPower_of_Power_positive_negative_odd h.2
                ((isOdd_correct (positive en)).mpr hodd)))
          · exact False.elim (not_Power_positive_even_negative (e := en) (a := an)
                (even_of_not_isOdd hodd) h.2)
      | negative en =>
          cases an with
          | one =>
              by_cases hodd : isOdd (negative en) = true
              · simp only [principalRoot, hodd, ↓reduceDIte]
                refine ⟨validPowerCondition_minusOne (negative en), ?_⟩
                rw [power_minusOne_negative]
                exact powerOrdinalExponent_minusOne_eq_of_odd_negative
                  ((isOdd_correct (negative en)).mpr hodd)
              · exact False.elim (not_Power_minusOne_even_negative (e := en)
                    (even_of_not_isOdd hodd) h.2)
          | successor an' =>
              exact False.elim (not_Power_negative_negative_successor (e := en) (a := an') h.2)

theorem principalRoot_eq_of_eq {e a b : Peano} (hab : a = b)
    (ha : e ≠ zero ∧ Power e a) (hb : e ≠ zero ∧ Power e b) :
    principalRoot e a ha = principalRoot e b hb := by
  subst hab
  cases a with
  | zero =>
      cases e with
      | zero => exact False.elim (ha.1 rfl)
      | positive _ => rfl
      | negative en => exact False.elim (not_isPower_negative_zero en ha.2)
  | positive an =>
      cases e with
      | zero => exact False.elim (ha.1 rfl)
      | positive en => rfl
      | negative en =>
          cases an with
          | one => rfl
          | successor an' =>
              exact False.elim (not_Power_negative_positive_successor (e := en) (a := an') ha.2)
  | negative an =>
      cases e with
      | zero => exact False.elim (ha.1 rfl)
      | positive en =>
          by_cases hodd : isOdd (positive en) = true
          · simp only [principalRoot, hodd, ↓reduceDIte]
          · exact False.elim (not_Power_positive_even_negative (e := en) (a := an)
                (even_of_not_isOdd hodd) ha.2)
      | negative en =>
          cases an with
          | one =>
              by_cases hodd : isOdd (negative en) = true
              · simp only [principalRoot, hodd, ↓reduceDIte]
              · exact False.elim (not_Power_minusOne_even_negative (e := en)
                    (even_of_not_isOdd hodd) ha.2)
          | successor an' =>
              exact False.elim (not_Power_negative_negative_successor (e := en) (a := an') ha.2)

theorem principalRoot_eq_of_positive_power (e a p : Peano)
    (he : e ≠ zero)
    (hp : zero < p) (h : ValidPowerCondition p e = true)
    (heq : power p e h = a) :
    ∃ h2, principalRoot e a h2 = p := by
  let h2 : e ≠ zero ∧ Power e a := ⟨he, ⟨p, h, heq⟩⟩
  refine ⟨h2, ?_⟩
  have hpow : e ≠ zero ∧ Power e (power p e h) := ⟨he, ⟨p, h, rfl⟩⟩
  calc
    principalRoot e a h2
        = principalRoot e (power p e h) hpow :=
          principalRoot_eq_of_eq heq.symm h2 hpow
    _ = p := by
      cases hp with
      | zero_less_than_positive =>
          rename_i pn
          cases e with
          | zero => exact False.elim (he rfl)
          | positive en =>
              have hpower_eq : power (positive pn) (positive en) h = positive (pn ^ en) := by
                change powerOrdinalExponent (positive pn) en = positive (pn ^ en)
                exact powerOrdinalExponent_positive_eq pn en
              have his : Power (positive en) (positive (pn ^ en)) := by
                rw [← hpower_eq]
                exact hpow.2
              let h2pos : (positive en) ≠ zero ∧ Power (positive en) (positive (pn ^ en)) :=
                ⟨hpow.1, his⟩
              calc
                principalRoot (positive en) (power (positive pn) (positive en) h) hpow
                    = principalRoot (positive en) (positive (pn ^ en)) h2pos :=
                      principalRoot_eq_of_eq hpower_eq hpow h2pos
                _ = positive pn := by
                  simp only [principalRoot]
                  exact congrArg positive
                    (OrdinalNatural.Peano.power_cancel_left en
                      (OrdinalNatural.Peano.root en (pn ^ en)
                        (ordinalPower_of_Power_positive_positive h2pos.2)) pn
                      (OrdinalNatural.Peano.root_correct en (pn ^ en)
                        (ordinalPower_of_Power_positive_positive h2pos.2)))
          | negative en =>
              cases pn with
              | one =>
                  have hpowone : power one (negative en) h = one := power_one (negative en) h
                  let h2one : (negative en) ≠ zero ∧ Power (negative en) one := by
                    constructor
                    · exact hpow.1
                    · rw [← hpowone]
                      exact hpow.2
                  calc
                    principalRoot (negative en) (power one (negative en) h) hpow
                        = principalRoot (negative en) one h2one :=
                          principalRoot_eq_of_eq hpowone hpow h2one
                    _ = one := rfl
              | successor pn' =>
                  exact False.elim (by cases h)

/-- The principal `e`-th root of `x ^ e` recovers `x` when `x` is non-negative
or the exponent is odd. Even powers of a negative base have a positive
principal root, so this fails without that restriction. -/
theorem principalRoot_power_eq (e x : Peano) (he : e ≠ zero)
    (h : ValidPowerCondition x e = true)
    (hprin : ¬ x < zero ∨ Odd e) :
    ∃ h2, principalRoot e (power x e h) h2 = x := by
  cases x with
  | zero =>
      cases e with
      | zero => exact False.elim (he rfl)
      | positive en =>
          have hne : positive en ≠ zero := fun hz => by cases hz
          have hpow_eq : power zero (positive en) h = zero := rfl
          let h2 : (positive en) ≠ zero ∧
              Power (positive en) (power zero (positive en) h) :=
            ⟨he, ⟨zero, h, rfl⟩⟩
          let h2z : (positive en) ≠ zero ∧ Power (positive en) zero :=
            ⟨hne, ⟨zero, validPowerCondition_positive zero en, rfl⟩⟩
          refine ⟨h2, ?_⟩
          calc
            principalRoot (positive en) (power zero (positive en) h) h2
                = principalRoot (positive en) zero h2z :=
                  principalRoot_eq_of_eq hpow_eq h2 h2z
            _ = zero := rfl
      | negative en =>
          exact False.elim (not_validPowerCondition_zero_negative en h)
  | positive pn =>
      exact principalRoot_eq_of_positive_power e (power (positive pn) e h)
        (positive pn) he LessThan.zero_less_than_positive h rfl
  | negative pn =>
      have he_odd : Odd e :=
        hprin.resolve_left (fun hnn => hnn LessThan.negative_less_than_zero)
      cases e with
      | zero => exact False.elim (he rfl)
      | positive en =>
          have hodd : isOdd (positive en) = true := (isOdd_correct _).mp he_odd
          have hpow_eq :
              power (negative pn) (positive en) h = negative (pn ^ en) := by
            change powerOrdinalExponent (negative pn) en = negative (pn ^ en)
            exact powerOrdinalExponent_negative_eq_of_odd he_odd
          have hne : positive en ≠ zero := fun hz => by cases hz
          have his : Power (positive en) (negative (pn ^ en)) :=
            ⟨negative pn, validPowerCondition_positive (negative pn) en, hpow_eq⟩
          let h2neg : (positive en) ≠ zero ∧
              Power (positive en) (negative (pn ^ en)) :=
            ⟨hne, his⟩
          let h2 : (positive en) ≠ zero ∧
              Power (positive en) (power (negative pn) (positive en) h) :=
            ⟨he, ⟨negative pn, h, rfl⟩⟩
          refine ⟨h2, ?_⟩
          calc
            principalRoot (positive en) (power (negative pn) (positive en) h) h2
                = principalRoot (positive en) (negative (pn ^ en)) h2neg :=
                  principalRoot_eq_of_eq hpow_eq h2 h2neg
            _ = negative pn := by
              simp only [principalRoot, hodd, ↓reduceDIte]
              exact congrArg negative
                (OrdinalNatural.Peano.power_cancel_left en
                  (OrdinalNatural.Peano.root en (pn ^ en)
                    (ordinalPower_of_Power_positive_negative_odd h2neg.2 he_odd))
                  pn
                  (OrdinalNatural.Peano.root_correct en (pn ^ en)
                    (ordinalPower_of_Power_positive_negative_odd h2neg.2 he_odd)))
      | negative en =>
          cases pn with
          | one =>
              have hodd : isOdd (negative en) = true :=
                (isOdd_correct _).mp he_odd
              have hpow_eq : power minusOne (negative en) h = minusOne := by
                rw [power_minusOne_negative]
                exact powerOrdinalExponent_minusOne_eq_of_odd_negative he_odd
              let h2 : (negative en) ≠ zero ∧
                  Power (negative en) (power minusOne (negative en) h) :=
                ⟨he, ⟨minusOne, h, rfl⟩⟩
              let h2m1 : (negative en) ≠ zero ∧ Power (negative en) minusOne :=
                ⟨he, ⟨minusOne, validPowerCondition_minusOne (negative en), by
                  rw [power_minusOne_negative]
                  exact powerOrdinalExponent_minusOne_eq_of_odd_negative he_odd⟩⟩
              refine ⟨h2, ?_⟩
              calc
                principalRoot (negative en) (power minusOne (negative en) h) h2
                    = principalRoot (negative en) minusOne h2m1 :=
                      principalRoot_eq_of_eq hpow_eq h2 h2m1
                _ = minusOne := by
                  simp only [principalRoot, minusOne, hodd, ↓reduceDIte]
          | successor pn' =>
              exact False.elim (by cases h)

instance : OfNat Peano n where
  ofNat := fromNat n

instance : ToString Peano where
  toString n := toString n.toInt

instance : Repr Peano where
  reprPrec n prec :=
    if n.toInt < 0 then Repr.addAppParen (toString n.toInt) prec else toString n.toInt

instance : ReprAtom Peano := ⟨⟩

instance : BEq Peano where
  beq a b := decide (a = b)

instance : Ord Peano where
  compare a b := compareOfLessAndEq a b

example : (0 : Peano) = zero := rfl
example : (1 : Peano) = one := rfl
example : (2 : Peano) = two := rfl
example : toString (3 : Peano) = "3" := rfl
example : toString minusOne = "-1" := rfl
example : ((0 : Peano) == (0 : Peano)) = true := rfl
example : Ord.compare minusOne (0 : Peano) = Ordering.lt := by decide

end Peano

end ZeroMath.Numbers.Integer
