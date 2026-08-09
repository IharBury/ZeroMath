# Instructions for AI Contributors

* The project is designed with zero external dependencies and must strictly avoid adding any external libraries, including Mathlib.
* The project must strictly use the `ZeroMath` namespace for all code.
* Use the command `lake build` to compile the Lean 4 project.
* The Lean toolchain is pinned to an exact release in `lean-toolchain` (currently `leanprover/lean4:v4.32.2`) so builds and CI stay reproducible. Do not use floating channels such as `leanprover/lean4:stable`.
* Toolchain upgrade cadence: when a new Lean 4 release is worth adopting, bump `lean-toolchain` to that exact `vX.Y.Z` tag in a dedicated PR, run `lake build`, fix any breakage, and update the version noted in this file. Prefer deliberate, infrequent bumps over tracking `stable` automatically.
* If `lake` or `lean` commands are missing, install Elan using `curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y`. In non-interactive bash sessions, prefix commands with `source ~/.profile && ` (e.g., `source ~/.profile && lake build`) to ensure the Lean toolchain is in the PATH.
* Agents must avoid making any theorems private. Always use `theorem` instead of `private theorem`.

## Cursor Cloud specific instructions

* This repo is a single, self-contained Lean 4 library (no external packages; `lake-manifest.json` lists zero dependencies). There is no application server or service to run — "running" the project means compiling it and evaluating library code.
* The startup update script installs Elan (if missing) and pre-installs the toolchain pinned in `lean-toolchain`. Elan lives in `~/.elan/bin`, which is added to PATH via `~/.profile`. In non-interactive shells, prefix commands with `source ~/.profile && ` (per the contributor note above) or call binaries directly from `~/.elan/bin`.
* Build / verify: `lake build` (compiles all modules; this is the primary correctness check).
* Lint / CI gate: there are no unit-test files and no test runner. CI (`.github/workflows/ci.yml`) runs `lake build` then `lake env lean scripts/check_axioms.lean`, which audits the kernel axiom footprint of every `ZeroMath` declaration (same data as `#print axioms`). Only Lean's foundational axioms (`propext`, `Classical.choice`, `Quot.sound`) are allowed — this catches `sorry`/`admit` (`sorryAx`), `native_decide`, and declared `axiom`s.
* To run/evaluate library code at runtime, write a scratch `.lean` file that does `import ZeroMath` plus `#eval`/`#check`, then run `lake env lean <file>.lean` (`lake env` puts the built artifacts on `LEAN_PATH`). Numbers are custom `Peano` types; use `.toNat` to print them as ordinary `Nat`.
