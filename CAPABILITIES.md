# ZeroMath library capabilities

ZeroMath is a self-contained Lean 4 library of elementary arithmetic and sequence structure. It has no external dependencies (including Mathlib). All declarations live in the `ZeroMath` namespace.

This document maps common early-mathematics skills to the concrete library support that implements them. The library is general: most number operations are defined for all natural numbers, not only the curriculum ranges 0–20 and 0–100. Those ranges are covered wherever the curriculum uses them.

## Write, compare, and order numbers from 0 to 20

**Supported.** Cardinal natural numbers are the Peano type `ZeroMath.Numbers.CardinalNatural.Peano` (`zero`, `successor`), with named constants `zero` through `ten`. Values 11–20 are obtained by further successors or by `fromNat` (for example `fromNat 20`). Conversion back to Lean’s `Nat` is `toNat`.

Written decimal form uses `ZeroMath.Numbers.CardinalNatural.Decimal` (a non-empty list of digits) with `fromPeano` / `toPeano`.

The same constructors write every natural number, including the later curriculum range 0–100. Peano values use `fromNat` (for example `fromNat 100`) or an `OfNat` literal such as `(100 : Peano)`. Decimal form is the corresponding digit list (`fromPeano` / `OfNat`); `toString` prints the usual base-10 spelling (`"42"`, `"100"`). There is no separate 0–100 subtype.

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

## Establish a pattern in a numerical sequence; continue it or restore missing numbers

**Supported.** The curriculum pattern is a constant step of several units: add the same amount at each place (increase) or subtract the same amount (decrease). That rule is an arithmetic progression.

On cardinal Peano numbers, under `ZeroMath.Numbers.CardinalNatural.Peano.Progressions`:

- Increasing: `FiniteArithmeticIncreasing` (positive `commonDifference`) and `InfiniteArithmetic`
- Decreasing: `ArithmeticDecreasing` (positive `subtractiveCommonDifference`)

Establish the rule from known terms:

- From a complete ordered list of at least two terms: `tryFromElements` (returns `none` when consecutive gaps are not a single positive constant)
- From any two distinct indexed terms: `tryCommonDifferenceFromOrderedIndexedElements` recovers the step as the value gap divided by the index gap (later minus earlier when increasing; earlier minus later when decreasing). `tryFromTwoElements` rebuilds an infinite increasing progression; `tryFromTwoElementsAndLength` rebuilds a finite increasing or decreasing one
- From a list with holes: `tryFromMaskedElements` on `Sequences.List (Option Peano)`, where `none` is a missing entry. At least two unmasked terms are required (`unmaskedCount`); remaining unmasked terms must agree with the recovered rule

Continue a known progression:

- Read further terms: `getElement` / `tryGetElement` (1-based ordinal index) and `getElements` (the finite list)
- Lengthen an increasing progression: `extendToLength` / `extendToInfinite`
- Lengthen a decreasing progression: rebuild it with a lower `limit`, or use integer `FiniteArithmetic.extendToLength` (signed common difference covers both directions)

Restore missing numbers by reconstructing (`tryFromMaskedElements` or `tryFromTwoElementsAndLength`) and then reading `getElements` / `getElement` at the masked indexes.

The same reconstruction, continuation, and masked-fill APIs exist for ordinal Peano numbers and for decimal representations. Integers use a single `FiniteArithmetic` type whose common difference may be positive or negative.

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

## Distinguish rows and columns of a table; enter and extract data

**Supported.** A rectangular table is `ZeroMath.Sequences.Table α`: a list of rows (top to bottom) in which every row is a list of cells of equal length (left to right). Columns are a first-class view of the same grid.

Distinguish rows from columns:

- Rows: field `rows`, constructors `singleRow` / `empty`, predicate `AnyRow`
- Columns: `columns` (each column is a list of cells, top to bottom), constructor `singleColumn`, predicate `AnyColumn`
- Cardinal sizes: `rowCount` and `columnCount`
- Horizontal versus vertical order: `BeforeColumnOf` / `AfterColumnOf` / `BetweenColumnsOf` and `BeforeRowOf` / `AfterRowOf` / `BetweenRowsOf`

Enter a datum into an existing cell, replace a row or column, or grow the table:

- Write one cell at 1-based ordinal indexes: `trySetElement` / `setElement`
- Replace a row: `trySetRow` / `setRow` (the new row must have length `columnCount`)
- Replace a column: `trySetColumn` / `setColumn` (the new column must have length `rowCount`)
- Add a row: `prependRow` / `appendRow` (requires `CompatibleRowLengthWithTable` when the table is non-empty)
- Add a column: `prependColumn` / `appendColumn` (requires `CompatibleColumnLengthWithTable` when the table is non-empty)
- Join tables: `concatenateRows` / `concatenateColumns`

Extract a datum or a whole row or column. Indexes are `OrdinalNatural.Peano` (the first row and first column have index `one`):

- One cell: `tryGetElement` / `getElement`
- One row: `tryGetRow` / `getRow`
- One column: `tryGetColumn` / `getColumn`
- Membership of a cell: `In` / `EquivalentIn` / `AnyElement`

The same 1-based get and set operations exist on `ZeroMath.Sequences.List α` (`tryGetElement` / `getElement` / `trySetElement` / `setElement`), and table lookup is defined in terms of them.

## Replace a number with the sum of its place-value addends

**Supported.** Any written decimal has one place-value addend per digit. The API lives in `ZeroMath.Numbers.CardinalNatural.Decimal.PlaceValue`.

- One addend: `placeAddend digit trailingZeros` (for example digit `4` with one trailing zero is `40`). A zero digit is the number `0` at every place, so `1005` yields `[1000, 0, 0, 5]`.
- The list of addends, most-significant first: `placeAddends` (for example `347` yields `[300, 40, 7]`)
- Their sum: `addAll`
- Value identity: `toPeano_eq_addAll_placeAddends` / `equivalent_addAll_placeAddends` — the number equals that sum
- Written identity: `eq_addAll_placeAddends` proves `n.normalize = (addAll (placeAddends n)).normalize`. When both writings are already normalized, `eq_addAll_placeAddends_of_isNormalized` gives `n = addAll (placeAddends n)`

The same identity on Peano values is `toPeano_eq_sumToPeano_placeAddends`: the number equals the sum of `digit × 10^place` over its digits.

## Summary

| Capability | Library support |
| --- | --- |
| Write, compare, order 0–20 and 0–100 | `CardinalNatural.Peano` / `Decimal`; `fromNat` / `OfNat`; `toString`; `<`, `≤`, `compare`; list sorting |
| Count objects; assign ordinals | `List.length`; `OrdinalNatural`; progression `tryGetElement` |
| Greater/smaller by a given amount | `+`, `subtract` / `trySubtract`; arithmetic progressions |
| Sequence pattern; continue or fill gaps | `tryFromElements`; `tryFromMaskedElements`; `extendToLength`; `getElements` |
| Addition and subtraction within 20 | Peano and decimal `add` / `subtract` (unbounded ops covering the range) |
| Number versus digit | Distinct types `Digits.Decimal` and `CardinalNatural.Decimal` |
| Left–right and between | `Before` / `After` / `Between` on lists; column/row analogues on tables |
| Group objects by an attribute | `groupBy` / `GroupedBy`; `Group`; `elementsWithFeature`; `featureValues` |
| Distinguish table rows/columns; enter and extract data | `Table`; `tryGetElement` / `setElement`; `trySetRow` / `setRow`; `trySetColumn` / `setColumn` |
| Place-value addends (any digits) | `placeAddends`; `addAll`; `n = 300 + 40 + 7` |
