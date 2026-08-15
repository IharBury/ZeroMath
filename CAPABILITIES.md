# ZeroMath library capabilities

ZeroMath is a self-contained Lean 4 library of elementary arithmetic and sequence structure. It has no external dependencies (including Mathlib). All declarations live in the `ZeroMath` namespace.

This document maps common early-mathematics skills to the concrete library support that implements them. The library is general: most number operations are defined for all natural numbers, not only the range 0–20. That range is covered wherever the curriculum uses it.

## Write, compare, and order numbers from 0 to 20

**Supported.** Cardinal natural numbers are the Peano type `ZeroMath.Numbers.CardinalNatural.Peano` (`zero`, `successor`), with named constants `zero` through `ten`. Values 11–20 are obtained by further successors or by `fromNat` (for example `fromNat 20`). Conversion back to Lean’s `Nat` is `toNat`.

Written decimal form uses `ZeroMath.Numbers.CardinalNatural.Decimal` (a non-empty list of digits) with `fromPeano` / `toPeano`.

Comparison is first-class:

- Strict order: `LessThan` / `<`, Boolean `isLessThan`
- Non-strict order: `LessThanOrEqual` / `≤`
- Trichotomy packaging: `compare`, returning a `Comparison`

Ordering collections of numbers is supported on ordinal Peano lists via sorting predicates (`SortedStrictlyAscending`, `SortedStrictlyDescending`, `SortedNonDescending`, `SortedNonAscending`) and insertion-sort functions in `ZeroMath.Numbers.OrdinalNatural.Peano.Lists`.

The same comparison and arithmetic APIs exist for the decimal representation.

## Count objects and assign ordinal numbers

**Supported.** A finite collection of objects is a `ZeroMath.Sequences.List α`. Its cardinality is `length`, which returns a `CardinalNatural.Peano` value (“how many”).

Ordinal numbering (1st, 2nd, …) uses a separate kind, `ZeroMath.Numbers.OrdinalNatural.Peano` (`one`, `successor` — no zero). Cardinal and ordinal forms convert via `toOrdinal` / `fromOrdinal` on nonzero cardinals.

Positions in a sequence are ordinal indices on a `Progression`: `tryGetElement` / `getElement` take an `OrdinalNatural.Peano` index, and the first element has index `one`. Finite progressions also expose `getLength` (a cardinal count of elements).

Together, this separates “how many objects” (cardinal) from “which place an object occupies” (ordinal).

## Find a number greater or smaller than a given number by a given amount

**Supported.** For cardinal Peano numbers:

- Greater by a given amount: `add` / `+` — the number greater than `n` by `k` is `n + k`
- Smaller by a given amount: `subtract` (requires a proof that the subtrahend is `≤` the minuend), or the total `trySubtract` returning `Option`

Cancellation laws such as `subtract_add_cancel`, `add_subtract_cancel`, `trySubtract_self_add`, and `trySubtract_add_right` relate the two directions.

Arithmetic progressions encode families of such steps: `FiniteArithmeticIncreasing` (common difference) and `ArithmeticDecreasing` (subtractive common difference) under `ZeroMath.Numbers.CardinalNatural.Peano.Progressions`. Parallel APIs exist for ordinal and decimal representations.

## Addition and subtraction within 20

**Supported.** Cardinal Peano defines total `add` and guarded `subtract` / `trySubtract`, with the usual algebraic theorems (`add_commutative`, `add_associative`, and the cancellation lemmas above). Any sum or difference whose operands and result lie in 0–20 is therefore expressible and provable.

Decimal arithmetic implements the same operations on digit lists (`add`, `subtract`, `trySubtract`), including aligned digit-list addition and subtraction in `ZeroMath.Numbers.Digits.Decimal.Lists`. Digit carry lemmas such as `digit_sum_lt_twenty` and `digit_carry_lt_twenty` reason explicitly about sums below twenty.

There is no separate “within 20 only” subtype: the curriculum bound is a usage constraint on top of unbounded natural-number arithmetic.

## Distinguish a number from a digit

**Supported.** Digits and numbers are different types.

- A **digit** is `ZeroMath.Numbers.Digits.Decimal`: a cardinal Peano value strictly less than `ten`, with constants `zeroDigit` … `nineDigit` and case analysis `digit_cases`.
- A **decimal number** is `ZeroMath.Numbers.CardinalNatural.Decimal`: a non-empty list of those digits, convertible to/from Peano via `toPeano` / `fromPeano`.

The same Peano value can appear as a digit (for example `fiveDigit`) or as a one-digit number (`fromPeano five`). That type distinction is the library’s formal account of “digit versus number.”

## Establish relations “left–right” and “between” among objects

**Supported** as order along a sequence or grid (not as free-plane geometry).

On `ZeroMath.Sequences.List α`:

- Left-of / earlier: `Before`
- Right-of / later: `After` (defined as `Before` with arguments swapped)
- Between: `Between` (an element lies between two others in either linear order)

All three are decidable when the element type has `DecidableEq`. Setoid-aware variants (`EquivalentBefore`, `EquivalentAfter`, `EquivalentBetween`) exist for equivalence-based comparison (for example decimal leading zeros).

On `ZeroMath.Sequences.Table α` (rows top-to-bottom, columns left-to-right):

- Horizontal: `BeforeColumnOf`, `AfterColumnOf`, `BetweenColumnsOf`
- Vertical: `BeforeRowOf`, `AfterRowOf`, `BetweenRowsOf`

plus equivalence-aware analogues.

## Group objects by a given attribute

**Supported.** A finite collection of objects is a `ZeroMath.Sequences.List α`. An attribute is a function `feature : α → β` that assigns each object a feature value (color, shape, parity, and so on).

On `ZeroMath.Sequences.List α`:

- Select objects with a given feature value: `elementsWithFeature` / `elementsWithoutFeature`
- Relational split of a list into those two parts: `SplitByFeature` / `splitByFeature`
- Partition into groups: `groupBy`, returning a `List` of `ZeroMath.Sequences.Group` values. Each `Group` has a `feature` and the `objects` that have it
- Specification of that partition: `GroupedBy`
- Feature values in first-appearance order: `featureValues` (equivalently `groupFeatures` of the groups)

Groups appear in the order their feature first occurs. Inside a group, objects keep their original relative order. Concatenating the objects of every group (`concatenateGroups`) is a `Reordering` of the original list: no object is lost or duplicated. Every group is non-empty, every object in a group has that group’s feature (`AllElements`), and the group features are `Unique`.

When `α` and `β` have `DecidableEq`, the relations are decidable. Binary attributes are the special case `β = Bool` (for example grouping cardinal Peano numbers by `isEven`).

## Summary

| Capability | Library support |
| --- | --- |
| Write, compare, order 0–20 | `CardinalNatural.Peano` / `Decimal`; `<`, `≤`, `compare`; list sorting |
| Count objects; assign ordinals | `List.length`; `OrdinalNatural`; progression `tryGetElement` |
| Greater/smaller by a given amount | `+`, `subtract` / `trySubtract`; arithmetic progressions |
| Addition and subtraction within 20 | Peano and decimal `add` / `subtract` (unbounded ops covering the range) |
| Number versus digit | Distinct types `Digits.Decimal` and `CardinalNatural.Decimal` |
| Left–right and between | `Before` / `After` / `Between` on lists; column/row analogues on tables |
| Group objects by an attribute | `groupBy` / `GroupedBy`; `Group`; `elementsWithFeature`; `featureValues` |
