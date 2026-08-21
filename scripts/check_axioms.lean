/-
  Kernel axiom audit for ZeroMath.

  Imports the library root and, for every declaration defined in a `ZeroMath`
  module, collects its transitive axiom footprint (the same data `#print axioms`
  reports). Fails unless every axiom is in the allowlist of Lean's standard
  foundational axioms.

  This catches what a source `grep` cannot:
  - `sorry` / `admit` → `sorryAx`
  - `native_decide` → per-declaration `*.native_decide.ax_*` axioms
    (historically `Lean.ofReduceBool`)
  - home-rolled `axiom` declarations
  and ignores the words "sorry"/"axiom" in comments.

  Run from the project root after a successful build:
    lake env lean scripts/check_axioms.lean
-/
import Lean
import ZeroMath

open Lean

/-- Lean's standard foundational axioms; anything else is a CI failure. -/
def allowedAxioms : NameSet :=
  ({} : NameSet)
    |>.insert ``propext
    |>.insert ``Classical.choice
    |>.insert ``Quot.sound

/-- True when `n` was defined in the ZeroMath library (root or a submodule). -/
def isZeroMathDecl (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | none => false
  | some modIdx =>
      env.allImportedModuleNames[modIdx]!.getRoot == `ZeroMath

#eval show MetaM Unit from do
  let env ← getEnv
  let mut audited : Nat := 0
  let mut axiomsUsed : NameSet := {}
  let mut violations : Array (Name × Array Name) := #[]
  let processDecl (n : Name) (audited : Nat) (axiomsUsed : NameSet) (violations : Array (Name × Array Name)) : MetaM (Nat × NameSet × Array (Name × Array Name)) := do
    unless isZeroMathDecl env n do return (audited, axiomsUsed, violations)
    let audited := audited + 1
    let mut axiomsUsed := axiomsUsed
    let mut violations := violations
    let axioms ← collectAxioms n
    for a in axioms do
      axiomsUsed := axiomsUsed.insert a
    let bad := axioms.filter fun a => !allowedAxioms.contains a
    if !bad.isEmpty then
      violations := violations.push (n, bad)
    return (audited, axiomsUsed, violations)

  for (n, _) in env.constants.map₁ do
    let (a, u, v) ← processDecl n audited axiomsUsed violations
    audited := a
    axiomsUsed := u
    violations := v

  for (n, _) in env.constants.map₂ do
    let (a, u, v) ← processDecl n audited axiomsUsed violations
    audited := a
    axiomsUsed := u
    violations := v
  IO.println s!"Audited {audited} ZeroMath declarations"
  IO.println s!"Axioms used: {axiomsUsed.toList}"
  if violations.isEmpty then
    IO.println "OK: all ZeroMath declarations use only allowed axioms (propext, Classical.choice, Quot.sound)."
  else
    IO.println s!"ERROR: {violations.size} declaration(s) depend on disallowed axioms:"
    for (n, bad) in violations do
      IO.println s!"  {n}: {bad}"
    throwError "axiom check failed: found disallowed axioms (sorryAx, native_decide, or a declared axiom)"
