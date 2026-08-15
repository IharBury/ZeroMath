# Naming conventions

This document describes the naming conventions used in ZeroMath. New declarations should follow these patterns.

## Full words

Declaration names use complete English words. Do not abbreviate.

Write `OrdinalNatural`, `commonDifference`, `FiniteArithmeticIncreasing`, `toNatural`, `fromInteger`, `ElementRelation`, `findQuotientDigitAuxiliary`, and `equals`. Do not write clipped forms such as `Nat`, `Int`, `Aux`, `Rel`, `Eq`, `iff`, `lt`, or `ne`.

When a name refers to a Lean type or class, still spell the concept in full in the ZeroMath declaration: `toNatural` for a conversion to `Nat`, `fromInteger` for a conversion from `Int`, `decidableEqual` for a `DecidableEq` instance. Lean's own type and class names may appear in signatures; they must not be copied into ZeroMath identifiers.

Some existing declarations still use short forms. Do not introduce new ones. Expand an abbreviated name when that declaration is next changed.

## Project and modules

All library code lives in the `ZeroMath` namespace, which matches the Lake package and root module.

File paths are PascalCase and mirror the dotted module path. For example, `ZeroMath/Numbers/OrdinalNatural/Peano.lean` is the module `ZeroMath.Numbers.OrdinalNatural.Peano`.

Aggregator files (`ZeroMath.lean`, `Numbers.lean`, `Sequences.lean`) only import children. The number tree is a repeated product of kind × representation × topic:

- kinds: `OrdinalNatural`, `CardinalNatural`, `Integer`
- representations: `Peano`, `Decimal`
- progressions: `InfiniteArithmetic`, `FiniteArithmeticIncreasing`, `ArithmeticDecreasing` (integers use `FiniteArithmetic`)

Scripts sit outside that tree and use snake_case (`scripts/check_axioms.lean`).

## Casing by kind of declaration

**PascalCase** for types, structures, inductives, classes, and propositional predicates: `Peano`, `Decimal`, `Progression`, `FiniteArithmeticIncreasing`, `LessThan`, `AnyElement`, `BeforeColumnOf`, `DigitIsNonZero`, `ElementRelation`.

**camelCase** for computational definitions and structure fields: `toNatural`, `isLessThan`, `trySubtract`, `getElement`, `commonDifference`, `zeroDigit`, `prependRow`.

**snake_case** for theorems: `fromNatural_toNatural`, `isLessThan_equals_true_ifAndOnlyIf_lessThan`, `tryGetElement_equals_none_of_getLength_lessThan`.

There are no `lemma`s and no `private` declarations. Everything public is a `theorem`.

## Prop vs Bool pairs

The same idea often exists twice: PascalCase for the `Prop`, camelCase for the `Bool` (or `Option`) decision procedure.

- `AnyElement` / `anyElement`
- `LessThan` / `isLessThan`
- `BeforeColumnOf` / `beforeColumnOf`
- `RemoveFirst` / `removeFirst`

Setoid variants take an `Equivalent` prefix: `EquivalentIn`, `EquivalentBeforeColumnOf`. Decidability instances are `decidable` plus that Prop name: `decidableLessThan`, `decidableAnyElement`.

## Verb prefixes on functions

- `toX` / `fromX` — conversions (`toNatural`, `fromInteger`, `toProgression`, `toPeano`)
- `isX` — Boolean tests (`isEmpty`, `isEven`, `isDivisible`)
- `tryX` — partial/`Option` operations (`trySubtract`, `tryGetElement`, `tryFromElements`)
- `getX` — extractors (`getLength`, `getElement`, `getElements`)
- `hasX` — existence-style checks (`hasNonZero`)

Helpers use `From` for recursive or indexed variants (`getElementFrom`) and `Auxiliary` for internals (`findQuotientDigitAuxiliary`). The same API names are reused across Peano and Decimal.

## Theorem names

Theorems compose the full words of the functions and relations they talk about:

- `X_equals_Y`, `X_equals_true_ifAndOnlyIf`, `X_ifAndOnlyIf_Y`
- `X_of_Y`, `X_implies_Y`
- `X_notEqual_zero`, `equals_of_X`
- `X_commutative`, `X_reflexive`, `X_transitive`

Use `equals`, `notEqual`, `ifAndOnlyIf`, `lessThan`, `lessThanOrEqual`, `greaterThan`, `greaterThanOrEqual`, `positive`, and `negative` in theorem names. Do not use `eq`, `ne`, `iff`, `lt`, `le`, `gt`, `ge`, `pos`, or `neg`.

When a theorem mentions a PascalCase Prop, that identifier stays PascalCase: `before_implies_In`, `reordering_of_RemoveFirst_reordering`. Some theorems are dotted under a type: `Unique.not_in_head`, `RemoveFirst.unique`.

## Constructors and identifiers

Constructors are usually camelCase English (`one`, `successor`, `firstElement`, `notFirst`, `positive`), not Lean/`List` idioms like `cons`/`nil`. Longer inductive cases use snake_case (`negative_less_than_zero`). Type parameters are Greek (`α`); values are short (`a`, `n`, `p`); hypotheses are `h`-prefixed (`h`, `ha`, `h_equals`, `hFinite`).
