# Instructions for AI Contributors

* The project is designed with zero external dependencies and must strictly avoid adding any external libraries, including Mathlib.
* The project must strictly use the `ZeroMath` namespace for all code.
* Use the command `lake build` to compile the Lean 4 project.
* The project uses the stable Lean toolchain; ensure the `lean-toolchain` file is set to `leanprover/lean4:stable`.
* If `lake` or `lean` commands are missing, install Elan using `curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y`. In non-interactive bash sessions, prefix commands with `source ~/.profile && ` (e.g., `source ~/.profile && lake build`) to ensure the Lean toolchain is in the PATH.
* Agents must avoid making any theorems private. Always use `theorem` instead of `private theorem`.

## Cursor Cloud specific instructions

The cloud update script installs Elan and pre-fetches the pinned toolchain, so `lake`/`lean` are ready on a fresh VM. Remember to `source ~/.profile &&` before `lake`/`lean` in non-interactive shells (already noted above).

* **Build / run**: this is a Lean 4 proof library — building *is* running. Use `source ~/.profile && lake build`. Compilation is the proof check; there is no separate runnable app and no automated test suite.
* **Lint / CI gates** (see `.github/workflows/`): `ci.yml` runs `lake build`; `verify_lean.yml` fails if any `.lean` file contains the words `sorry` or `axiom` (`grep -rnw --include=\*.lean -E '\bsorry\b|\baxiom\b' .`). Both must pass.
* **Known caveat (toolchain drift)**: `lean-toolchain` is pinned to `leanprover/lean4:stable`, which currently resolves to Lean `v4.31.0` (released 2026-06-15, after the last green CI). Under `v4.31.0`, one proof in `ZeroMath/Numbers/OrdinalNatural/Decimal.lean` (`toCardinalPeano_successor`) fails because `+ CardinalNatural.Peano.one` is no longer definitionally `.successor`; all other modules build cleanly. This is an upstream regression, not an environment problem — fixing it requires a code change to that proof (out of scope for env setup).
