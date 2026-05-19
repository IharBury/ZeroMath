# Instructions for AI Contributors

* The project is designed with zero external dependencies and must strictly avoid adding any external libraries, including Mathlib.
* The project must strictly use the `ZeroMath` namespace for all code.
* Use the command `lake build` to compile the Lean 4 project.
* The project uses the stable Lean toolchain; ensure the `lean-toolchain` file is set to `leanprover/lean4:stable`.
* If `lake` or `lean` commands are missing, install Elan using `curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y`. In non-interactive bash sessions, prefix commands with `source ~/.profile && ` (e.g., `source ~/.profile && lake build`) to ensure the Lean toolchain is in the PATH.
