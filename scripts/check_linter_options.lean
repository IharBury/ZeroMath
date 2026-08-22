/-
  Source audit: Lean files must not change linter options.

  Parses every project `.lean` file and walks the syntax tree for `set_option`
  (command, term, and tactic forms). Fails if any option name is in the `linter`
  namespace (`linter.all`, `linter.unusedVariables`, …). Comments and string
  literals do not count, because they are not `set_option` syntax.

  Skips `.git` and `.lake` so build artifacts and VCS metadata are ignored.

  Run from the project root after a successful build:
    lake env lean scripts/check_linter_options.lean
-/
import Lean

open Lean Parser

/-- True when `name` is a linter option (`linter` or `linter.*`). -/
def isLinterOption (name : Name) : Bool :=
  name.getRoot == `linter

/-- Directories that are not project Lean sources. -/
def skipDirectoryName (name : String) : Bool :=
  name == ".git" || name == ".lake"

/-- Project `.lean` files under `root`, excluding skipped directories. -/
def projectLeanFiles (root : System.FilePath) : IO (Array System.FilePath) := do
  let paths ← System.FilePath.walkDir root fun dir =>
    match dir.fileName with
    | some name => pure !skipDirectoryName name
    | none => pure true
  let files := paths.filter fun path => path.extension == some "lean"
  return files.qsort fun a b => a.toString < b.toString

/-- Option identifier from a `set_option` node, if `stx` is one. -/
def setOptionName? (stx : Syntax) : Option Name :=
  if stx.getNumArgs ≥ 2 && stx[0].isAtom && stx[0].getAtomVal == "set_option" && stx[1].isIdent then
    some stx[1].getId.eraseMacroScopes
  else
    none

/-- Collect `set_option` nodes whose option is in the `linter` namespace. -/
partial def collectLinterSetOptions (stx : Syntax) (acc : Array (Name × Syntax)) :
    Array (Name × Syntax) :=
  let acc :=
    match setOptionName? stx with
    | some name =>
      if isLinterOption name then acc.push (name, stx) else acc
    | none => acc
  stx.getArgs.foldl (init := acc) fun acc child => collectLinterSetOptions child acc

/-- `line:column` of `stx` in `contents`, or `?` when source info is missing. -/
def formatPosition (contents : String) (stx : Syntax) : String :=
  match stx.getPos? with
  | none => "?"
  | some pos =>
    let p := FileMap.ofString contents |>.toPosition pos
    s!"{p.line}:{p.column}"

#eval show MetaM Unit from do
  let env ← getEnv
  let files ← projectLeanFiles "."
  let mut scanned : Nat := 0
  let mut violations : Array String := #[]
  for path in files do
    scanned := scanned + 1
    let contents ← IO.FS.readFile path
    let stx ← testParseModule env path.toString contents
    for (name, hit) in collectLinterSetOptions stx #[] do
      violations := violations.push s!"  {path}:{formatPosition contents hit}: set_option {name}"
  IO.println s!"Scanned {scanned} Lean file(s)"
  if violations.isEmpty then
    IO.println "OK: no Lean file changes a linter option."
  else
    IO.println s!"ERROR: {violations.size} linter option change(s) in Lean files:"
    for v in violations do
      IO.println v
    throwError "linter option check failed: Lean files must not change linter options"
