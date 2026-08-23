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

Ordering collections of numbers is supported on every Peano and Decimal kind via sorting predicates (`SortedStrictlyAscending`, `SortedStrictlyDescending`, `SortedNonDescending`, `SortedNonAscending`) and insertion-sort functions in each `…/Lists` module (for example `ZeroMath.Numbers.CardinalNatural.Peano.Lists` and `ZeroMath.Numbers.Integer.Decimal.Lists`). The generic implementations live in `ZeroMath.Sequences.List`. Decimal strict sorts require `UniqueUpToEquivalence`, because order compares values (`01` and `1` are equivalent).

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
- Lengthen a decreasing progression: rebuild it with a lower `limit`, or use integer `FiniteArithmetic.extendToLength` (signed common difference covers both directions). That integer API exists on both Peano and Decimal `FiniteArithmetic`

Restore missing numbers by reconstructing (`tryFromMaskedElements` or `tryFromTwoElementsAndLength`) and then reading `getElements` / `getElement` at the masked indexes.

The same reconstruction, continuation, and masked-fill APIs exist for ordinal Peano numbers and for decimal representations. Integers use a single `FiniteArithmetic` type whose common difference may be positive or negative.

## Addition and subtraction within 20

**Supported.** Cardinal Peano defines total `add` and guarded `subtract` / `trySubtract`, with the usual algebraic theorems (`add_commutative`, `add_associative`, and the cancellation lemmas above). Any sum or difference whose operands and result lie in 0–20 is therefore expressible and provable.

Decimal arithmetic implements the same operations on digit lists (`add`, `subtract`, `trySubtract`), including aligned digit-list addition and subtraction in `ZeroMath.Numbers.Digits.Decimal.Lists`. Digit carry lemmas such as `digit_sum_lt_twenty` and `digit_carry_lt_twenty` reason explicitly about sums below twenty.

There is no separate “within 20 only” subtype: the curriculum bound is a usage constraint on top of unbounded natural-number arithmetic.

A later pattern, addition and subtraction of the form `30 + 5`, `35 − 5`, `35 − 30`, uses the same operations on two-digit tens and ones; see the next section. General addition and subtraction within 100 is documented after that.

## Addition and subtraction of the form 30 + 5, 35 − 5, 35 − 30

**Supported.** This curriculum pattern composes or decomposes a two-digit number from a multiple of ten and a one-digit number:

- `30 + 5` — add a one-digit number to a round ten
- `35 − 5` — subtract the ones from the two-digit number
- `35 − 30` — subtract the tens from the two-digit number

The same unbounded cardinal Peano and decimal `add`, `subtract`, and `trySubtract` that cover addition and subtraction within 20 also compute these sums and differences. Any such calculation whose operands and result lie in 0–100 is therefore expressible and provable. There is no separate “two-digit only” subtype. Decimal columnar subtraction of equal-length writings can keep a leading zero (`35 − 30` is written `05`); `normalize` recovers the usual spelling `5`, and the values are equivalent (`≈`).

The place-value reading of the pattern is first-class on `ZeroMath.Numbers.CardinalNatural.Decimal`:

- A round ten is a place-value addend: `placeAddend threeDigit Peano.one` is the written `30`; a ones digit is `fromDigit fiveDigit` (`5`)
- `placeAddends` of `35` is `[30, 5]`
- `toPeano_eq_addAll_placeAddends` / `equivalent_addAll_placeAddends` prove that the two-digit number equals that sum (`35 = 30 + 5`)
- Cancellation recovers the two subtractions: `add_subtract_cancel` gives `(30 + 5) − 5 = 30`, and `trySubtract_self_add` / `subtract_add_cancel` give `(30 + 5) − 30 = 5`

The full place-value API (any number of digits) is described under “Replace a number with the sum of its place-value addends.”

## Addition and subtraction within 100

**Supported.** The same unbounded cardinal Peano and decimal `add`, `subtract`, and `trySubtract` that cover addition and subtraction within 20 also compute any sum or difference whose operands and result lie in 0–100. Typical calculations in that later curriculum range include:

- Two-digit plus one-digit, including crossing a ten: `47 + 8`
- Two-digit plus two-digit: `47 + 35`
- Round tens: `40 + 30`, `70 − 20`
- Two-digit minus one-digit or two-digit: `52 − 8`, `82 − 47`

Peano values use `fromNat` / `OfNat` (for example `(47 : Peano) + (35 : Peano)`). Decimal form uses the same literals and the columnar digit-list algorithms in `ZeroMath.Numbers.Digits.Decimal.Lists` (`addAlignedLists`, `subtractAlignedLists`) — the written method for two-digit addition and subtraction. `add_toPeano` / `subtract_toPeano` relate the two representations. Decimal columnar subtraction of equal-length writings can keep a leading zero (`100 − 1` is written `099`); `normalize` recovers the usual spelling `99`, and the values are equivalent (`≈`).

The two-digit tens-and-ones pattern `30 + 5`, `35 − 5`, `35 − 30` is a special case of this range; see the previous section. There is no separate “within 100 only” subtype: the curriculum bound is a usage constraint on top of unbounded natural-number arithmetic.

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

**Supported.** Any written decimal has one place-value addend per nonzero digit, or a single `0` when the number is zero. The numeric API lives in `ZeroMath.Numbers.CardinalNatural.Decimal`. Matching non-term helpers (`placeAddends`, `addAll`, and the value/written identities) exist for ordinal decimals in `ZeroMath.Numbers.OrdinalNatural.Decimal.PlaceValue` and for integer decimals in `ZeroMath.Numbers.Integer.Decimal`. The matching sum term is `placeAddendsTerm` in `ZeroMath.Numbers.CardinalNatural.Decimal.Terms.Homogeneous.Trees`, and the same conversion exists for ordinal and integer decimals under `ZeroMath.Numbers.OrdinalNatural.Decimal.Terms.Homogeneous.Trees` and `ZeroMath.Numbers.Integer.Decimal.Terms.Homogeneous.Trees`.

- One addend: `placeAddend digit trailingZeros` (for example digit `4` with one trailing zero is `40`)
- The list of addends, most-significant first: `placeAddends` (for example `347` yields `[300, 40, 7]`). Zero addends are omitted unless the number is zero, so `1005` yields `[1000, 5]` and `0` yields `[0]`
- As a sum term: `placeAddendsTerm` builds a homogeneous `Tree` under a caller-supplied binary addition operation (`getArgumentCount add` must be two). A one-digit number is a value leaf; longer writings nest left-associated as `(... + y) + z`. For cardinal `347` this is the term `(300 + 40) + 7`; for `1005` it is `1000 + 5`. Integer decimals keep the original sign (`-347` is `((-300) + (-40)) + (-7)`; `-1005` is `(-1000) + (-5)`). Ordinal decimals omit zero addends (`1005` is `1000 + 5`)
- Their sum: `addAll` (cardinal, ordinal, and integer decimals)
- Value identity: `toPeano_eq_addAll_placeAddends` / `equivalent_addAll_placeAddends` — the number equals that sum (ordinal also has `toCardinalPeano_eq_addAll_placeAddends`)
- Term evaluation: `toPeano_eq_compute_placeAddendsTerm` / `equivalent_compute_placeAddendsTerm` — computing `placeAddendsTerm` under binary addition recovers the original number (same theorems on the ordinal and integer `placeAddendsTerm`)
- Written identity: `eq_addAll_placeAddends` proves `n.normalize = (addAll (placeAddends n)).normalize`. When both writings are already normalized, `eq_addAll_placeAddends_of_isNormalized` gives `n = addAll (placeAddends n)`

The same identity on Peano values is `toPeano_eq_sumToPeano_placeAddends`: the number equals the sum of `digit × 10^place` over its digits.

## Replace a sum of identical addends with a product, and a product with that sum

**Supported.** Multiplication is the sum of identical addends: `a × n` is `n` copies of `a` added together (`5 + 5 + 5 + 5 = 5 × 4`, and the reverse). The addend is the first factor and the number of addends is the second, matching the Peano definition of `multiply`. Commutativity gives the other reading (`5 × 4` is also four copies of `5` or five copies of `4`).

A generic list of copies lives on `ZeroMath.Sequences.List`:

- `repeatValue value n` — `n` copies of `value`
- `tryRepeatedValue` — the common value when every element is equal (`none` if the list is empty or mixed)
- `tryEquivalentRepeatedValue` — the same test up to setoid equivalence (decimal leading zeros)

On cardinal Peano numbers (`ZeroMath.Numbers.CardinalNatural.Peano`):

- `repeatedAddends addend count` — `count` copies of `addend`
- `sum` — left-to-right sum of a list (empty sum is `0`)
- `sum_repeatedAddends` — `sum (repeatedAddends a n) = a * n`
- `sum_repeatedAddends_commutative` — `sum (repeatedAddends n a) = a * n`
- `sum_eq_multiply_of_AllElements` — any list of identical addends sums to addend times length
- `tryProductFromAddends` — replace such a list with the product (`none` when the addends are not all equal)

The same pair of directions exists for ordinal Peano numbers (`addAll` / `addAll_repeatedAddends`; the count is a positive ordinal) and for integers (`sum` / `sum_repeatedAddends`, with a cardinal count of addends so `(-3) + (-3) + (-3) = (-3) × 3`).

On decimal writings the product is `addend * fromPeano count` (cardinal and ordinal) or `addend * fromCardinalNaturalPeano count` (integer). `addAll` of `repeatedAddends` is equivalent to that product (`equivalent_addAll_multiply`); `sumToPeano_repeatedAddends` / `sumToCardinalPeano_repeatedAddends` is the Peano identity.

As terms, under `…Decimal.Terms.Homogeneous.Trees` on each kind, and under `…Peano.Terms.Homogeneous.Trees` on the matching Peano types:

- `repeatedAddendsTerm` — left-associated sum `(... + a) + a` of `count` copies of `addend` (`count` nonzero on cardinal and integer)
- `productTerm` — the binary product of the addend and the count (a written decimal count, or the Peano count itself)
- Computing either term recovers `addend * count` (`toPeano_eq_compute_repeatedAddendsTerm`, `toPeano_eq_compute_productTerm`, and the matching cardinal-Peano theorems on ordinals; on Peano values, `compute_repeatedAddendsTerm` / `compute_productTerm`)

Term rewrites on `ZeroMath.Terms.Homogeneous.Tree` turn one form into the other or return `none`:

- `tryReplaceSumWithProduct` — a binary sum of at least two identical value addends becomes the product of the addend and `fromCount` of the addend count (`getArgumentCount add` must be two)
- `tryReplaceProductWithSumOfFirstFactor` — `a * n` becomes the sum of `toCount n` copies of `a` (`none` when the count is zero)
- `tryReplaceProductWithSumOfSecondFactor` — `a * n` becomes the sum of `toCount a` copies of `n`

Each decimal kind specializes those with `fromPeano` / `toPeano` (cardinal), `fromCardinalNaturalPeano` / non-negative `toCardinalNaturalPeano` (integer), or `fromCardinalCount` / `toCardinalPeano` (ordinal). Each Peano kind uses the count directly (cardinal `id` / `some`), `fromCardinalNatural` / non-negative `toCardinalNatural` (integer), or `fromCardinalCount` / `fromOrdinal` (ordinal).

When a rewrite succeeds, the original tree and the replacement compute to the same number: `toPeano_compute_tryReplaceSumWithProduct` and the two product-to-sum theorems on cardinal and integer decimals, the matching `toCardinalPeano_compute_tryReplace*` theorems on ordinal decimals, and `compute_tryReplaceSumWithProduct` / `compute_tryReplaceProductWithSumOfFirstFactor` / `compute_tryReplaceProductWithSumOfSecondFactor` on each Peano kind. Addition must compute as `+` and multiplication as `*`.

## Multiply 1 and 0 by a number; multiply and divide by 10

**Supported.** These are special cases of the same unbounded `multiply` / `divide` / `tryDivide` that implement every product and exact quotient. The identities for the factors `0` and `1`, and the factor `10`, are first-class theorems rather than a separate “by 0, 1, or 10 only” API.

Multiply `1` and `0` by a number, on cardinal Peano numbers (`ZeroMath.Numbers.CardinalNatural.Peano`):

- `one_multiply` / `multiply_one` — `1 * n = n` and `n * 1 = n`
- `zero_multiply` / `multiply_zero` — `0 * n = 0` and `n * 0 = 0`

Those are the two readings of the previous section: `n * 1` is one copy of `n`, and `0 * n` is `n` copies of `0` (the empty sum `n * 0` is `0` by the Peano definition of `multiply`). Integers have the same identities (`one_multiply`, `multiply_positive_one`, `zero_multiply`, `multiply_zero`). Ordinal Peano numbers start at `1`, so they have `one_multiply` / `multiply_one` and no zero factor.

Decimal writings use the same operations (`*` / `tryDivide` / `divide`). Cardinal `multiply_toPeano` transports a product to Peano, so `0 * n` and `1 * n` there are the Peano identities above (`fromPeano` / `OfNat` write the factors; `zero` and `one` are named constants). The same transport exists on ordinal and integer decimals.

Multiply and divide by `10`:

- The named cardinal Peano constant `ten` (and decimal `(10 : Decimal)` / `fromPeano ten`)
- Product: `n * ten` (equivalently `ten * n` by `multiply_commutative`)
- Exact quotient: `tryDivide n ten`, or `divide n ten` when `Divisible n ten`. `ten` is never zero, so the only failure is a nonzero remainder
- Cancellation: `divide_multiply_cancel` recovers the other factor — `(n * 10) / 10 = n`
- Powers of ten: `tenPower k` is `10^k` (`tenPower_eq_power`); `tenPower one` is `10`, so multiplying by ten is also `n * tenPower one`

The written decimal method of appending zeros is the digit-list identity `toCardinalNaturalPeano_padAtEnd` in `ZeroMath.Numbers.Digits.Decimal.Lists`: padding `k` zeros on the right multiplies the value by `tenPower k`. One trailing zero is therefore `× 10`. A one-digit place-value addend with one trailing zero is the same fact: `placeAddend_toPeano` gives `(placeAddend d one).toPeano = d.val * tenPower one`. Exact division by ten is the inverse on values that are multiples of ten (`tryDivide` / `divide`).

Typical curriculum calculations (`1 × 7 = 7`, `0 × 5 = 0`, `6 × 10 = 60`, `40 ÷ 10 = 4`) are therefore expressible and provable. There is no separate “by 0, 1, or 10 only” subtype: the curriculum cases are a usage constraint on top of unbounded natural-number arithmetic.

## Summary

| Capability | Library support |
| --- | --- |
| Write, compare, order 0–20 and 0–100 | `CardinalNatural.Peano` / `Decimal`; `fromNat` / `OfNat`; `toString`; `<`, `≤`, `compare`; list sorting on every Peano and Decimal kind |
| Count objects; assign ordinals | `List.length`; `OrdinalNatural`; progression `tryGetElement` |
| Greater/smaller by a given amount | `+`, `subtract` / `trySubtract`; arithmetic progressions |
| Sequence pattern; continue or fill gaps | `tryFromElements`; `tryFromMaskedElements`; `extendToLength`; `getElements` — on every kind × representation (integers: signed `FiniteArithmetic`) |
| Addition and subtraction within 20 | Peano and decimal `add` / `subtract` (unbounded ops covering the range) |
| Addition and subtraction of the form 30 + 5, 35 − 5, 35 − 30 | Same `add` / `subtract` / `trySubtract`; two-digit case of `placeAddends` (`35 = 30 + 5`) |
| Addition and subtraction within 100 | Same Peano and decimal `add` / `subtract` (unbounded ops covering the range) |
| Number versus digit | Distinct types `Digits.Decimal` and `CardinalNatural.Decimal` |
| Left–right and between | `Before` / `After` / `Between` on lists; column/row analogues on tables |
| Group objects by an attribute | `groupBy` / `GroupedBy`; `Group`; `elementsWithFeature`; `featureValues` |
| Distinguish table rows/columns; enter and extract data | `Table`; `tryGetElement` / `setElement`; `trySetRow` / `setRow`; `trySetColumn` / `setColumn` |
| Place-value addends (any digits) | `placeAddends`; `placeAddendsTerm`; `addAll` on cardinal, ordinal, and integer decimals |
| Sum of identical addends ↔ product | `repeatValue`; `repeatedAddends`; `sum` / `addAll`; `sum_repeatedAddends`; `tryProductFromAddends`; `repeatedAddendsTerm` / `productTerm` on Decimal and Peano; `tryReplaceSumWithProduct`; `tryReplaceProductWithSumOfFirstFactor` / `tryReplaceProductWithSumOfSecondFactor`; `toPeano_compute_tryReplace*` / `toCardinalPeano_compute_tryReplace*` / `compute_tryReplace*` |
| Multiply 1 and 0 by a number; multiply and divide by 10 | `one_multiply` / `multiply_one`; `zero_multiply` / `multiply_zero`; `*` / `tryDivide` / `divide` with `ten`; `tenPower`; `toCardinalNaturalPeano_padAtEnd`; `placeAddend_toPeano` |
