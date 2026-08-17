# Naming conventions

This document describes the naming conventions used in ZeroMath. New declarations should follow these patterns.

## Full words

Declaration names use complete English words. Do not abbreviate.

Write `OrdinalNatural`, `commonDifference`, `FiniteArithmeticIncreasing`, `DerivedEquivalence`, and `findQuotientDigitAuxiliary`. Do not invent clipped forms such as `Aux` or `Rel`.

**Exception.** A Lean system library name may be used when the identifier refers to that definition. Conversions and instances that talk about Lean's `Nat`, `Int`, `Eq`, or `DecidableEq` keep those names: `toNat`, `fromInt`, `fromNat_toNat`, `decidableEq`. Theorem connectives that name Lean relations stay in that form too: `eq` for `Eq`, `ne` for `Ne`, `iff` for `Iff`, `lt` for `LT`, `le` for `LE`. Lean's own type and class names may also appear in signatures.

Do not introduce clipped forms. Existing library names use complete words except for Lean system library names.

## Project and modules

All library code lives in the `ZeroMath` namespace, which matches the Lake package and root module.

File paths are PascalCase and mirror the dotted module path. For example, `ZeroMath/Numbers/OrdinalNatural/Peano.lean` is the module `ZeroMath.Numbers.OrdinalNatural.Peano`.

Aggregator files (`ZeroMath.lean`, `Numbers.lean`, `Sequences.lean`) only import children. The number tree is a repeated product of kind × representation × topic:

- kinds: `OrdinalNatural`, `CardinalNatural`, `Integer`
- representations: `Peano`, `Decimal`
- progressions: `InfiniteArithmetic`, `FiniteArithmeticIncreasing`, `ArithmeticDecreasing` (integers use `FiniteArithmetic`)

Scripts sit outside that tree and use snake_case (`scripts/check_axioms.lean`).

## Casing by kind of declaration

**PascalCase** for types, structures, inductives, classes, and propositional predicates: `Peano`, `Decimal`, `Progression`, `FiniteArithmeticIncreasing`, `LessThan`, `AnyElement`, `BeforeColumnOf`, `DigitIsNonZero`, `DerivedEquivalence`.

**camelCase** for computational definitions and structure fields: `toNat`, `isLessThan`, `trySubtract`, `getElement`, `commonDifference`, `zeroDigit`, `prependRow`.

**snake_case** for theorems: `fromNat_toNat`, `isLessThan_eq_true_iff_lt`, `tryGetElement_eq_none_of_getLength_lt`.

There are no `lemma`s and no `private` declarations. Everything public is a `theorem`.

## Prop vs Bool pairs

The same idea often exists twice: PascalCase for the `Prop`, camelCase for the `Bool` (or `Option`) decision procedure.

- `AnyElement` / `anyElement`
- `LessThan` / `isLessThan`
- `BeforeColumnOf` / `beforeColumnOf`
- `RemoveFirst` / `removeFirst`

Setoid variants take an `Equivalent` prefix: `EquivalentIn`, `EquivalentBeforeColumnOf`. Decidability instances are `decidable` plus that Prop name: `decidableLessThan`, `decidableAnyElement`.

## Verb prefixes on functions

- `toX` / `fromX` — conversions (`toNat`, `fromInt`, `toProgression`, `toPeano`)
- `isX` — Boolean tests (`isEmpty`, `isEven`, `isDivisible`)
- `tryX` — partial/`Option` operations (`trySubtract`, `tryGetElement`, `tryFromElements`)
- `getX` — extractors (`getLength`, `getElement`, `getElements`)
- `hasX` — existence-style checks (`hasNonZero`)

Helpers use `From` for recursive or indexed variants (`getElementFrom`) and `Auxiliary` for internals (`findQuotientDigitAuxiliary`). The same API names are reused across Peano and Decimal.

## Theorem names

Theorems compose the names of the functions and relations they talk about. Use full words, except for Lean system library names:

- `X_eq_Y`, `X_eq_true_iff`, `X_iff_Y`
- `X_of_Y`, `X_implies_Y`
- `X_ne_zero`, `eq_of_X`
- `X_commutative`, `X_reflexive`, `X_transitive`

When a theorem mentions a PascalCase Prop, that identifier stays PascalCase: `before_implies_In`, `reordering_of_RemoveFirst_reordering`. Some theorems are dotted under a type: `Unique.not_in_head`, `RemoveFirst.unique`.

## Simp lemmas

Mark `@[simp]` on equalities that `simp` should apply automatically:

- Normalization identities (`normalize_toPeano`, `normalize_isNormalized`, `normalize_zero`)
- Conversion transport that pushes `toPeano` / `toCardinalPeano` / `toNat` / `toInt` inward through operations and constructors (`add_toPeano`, `successor_toPeano`, `toPeano_fromPeano`)
- Computational reductions (`add_zero`, `successor_predecessor`)

Do not mark setoid statements (`≈`), existential transport (`∃ h, …`), or order-reflection lemmas. Extra hypotheses are acceptable when they are already arguments of the left-hand side (`toOrdinal_toPeano`, `power_toNat`).

## Constructors and identifiers

Constructors are usually camelCase English (`one`, `successor`, `firstElement`, `notFirst`, `positive`), not Lean/`List` idioms like `cons`/`nil`. Longer inductive cases use snake_case (`negative_less_than_zero`). Type parameters are Greek (`α`); values are short (`a`, `n`, `p`); hypotheses are `h`-prefixed (`h`, `ha`, `h_eq`, `hFinite`).
