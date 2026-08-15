-- Scratch checks confirming CAPABILITIES.md claims against the library API.
-- Run: lake env lean scripts/verify_capabilities.lean
import ZeroMath

open ZeroMath.Numbers
open ZeroMath.Numbers.CardinalNatural (Peano)
open ZeroMath.Sequences

-- 1. Write / compare / order numbers 0..20
#check Peano.zero
#check Peano.ten
#eval (Peano.fromNat 20).toNat  -- 20
#eval Peano.isLessThan (Peano.fromNat 7) (Peano.fromNat 15)  -- true
#check Peano.compare
#check OrdinalNatural.Peano.Lists.insertionSortNonDescending

-- 2. Count objects; assign ordinal numbers
def sample : ZeroMath.Sequences.List String :=
  .firstElement "a" (.firstElement "b" (.firstElement "c" .empty))
#eval (ZeroMath.Sequences.List.length sample).toNat  -- 3
#check Peano.toOrdinal
#check Progression.tryGetElement

-- 3. Greater / smaller by a given amount
#eval ((Peano.fromNat 8) + (Peano.fromNat 5)).toNat  -- 13
#eval
  match Peano.trySubtract (Peano.fromNat 17) (Peano.fromNat 4) with
  | some n => n.toNat
  | none => 999  -- 13

-- 4. Addition and subtraction within 20
#eval ((Peano.fromNat 9) + (Peano.fromNat 11)).toNat  -- 20
#eval
  match Peano.trySubtract (Peano.fromNat 20) (Peano.fromNat 6) with
  | some n => n.toNat
  | none => 999  -- 14

-- 5. Number vs digit (distinct types)
#check Digits.Decimal
#check Digits.zeroDigit
#check Digits.nineDigit
#check CardinalNatural.Decimal
example : Digits.Decimal := Digits.fiveDigit
example : CardinalNatural.Decimal := CardinalNatural.Decimal.fromPeano Peano.five

-- 6. Left–right and between
#check ZeroMath.Sequences.List.Before
#check ZeroMath.Sequences.List.After
#check ZeroMath.Sequences.List.Between
#check Table.BeforeColumnOf
#check Table.AfterColumnOf
#check Table.BetweenColumnsOf

example : ZeroMath.Sequences.List.Before "a" "c" sample :=
  ZeroMath.Sequences.List.Before.first _
    (ZeroMath.Sequences.List.AnyElement.notFirst _ _
      (ZeroMath.Sequences.List.AnyElement.first _ _ rfl))

example : ZeroMath.Sequences.List.After "c" "a" sample :=
  ZeroMath.Sequences.List.Before.first _
    (ZeroMath.Sequences.List.AnyElement.notFirst _ _
      (ZeroMath.Sequences.List.AnyElement.first _ _ rfl))

example : ZeroMath.Sequences.List.Between "b" "a" "c" sample :=
  Or.inl ⟨
    ZeroMath.Sequences.List.Before.first _ (ZeroMath.Sequences.List.AnyElement.first _ _ rfl),
    ZeroMath.Sequences.List.Before.notFirst _ _
      (ZeroMath.Sequences.List.Before.first _ (ZeroMath.Sequences.List.AnyElement.first _ _ rfl))
  ⟩
