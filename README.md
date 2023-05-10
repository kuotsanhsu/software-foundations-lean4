# Software Foundations in Lean 4

A Lean 4 adaptation of the *Software Foundations* series by Benjamin Pierce et al.

- [*Software Foundations*](https://softwarefoundations.cis.upenn.edu/)
- [Lean 4](https://github.com/leanprover/lean4) and [nightly releases](https://github.com/leanprover/lean4-nightly/releases).
- [Lake](https://github.com/leanprover/lake): build system and package manager for Lean 4; the Lean 4 counterpart of Rust's "cargo".
- [*Lean Manual*](https://leanprover.github.io/lean4/doc/)
- [*Theorem Proving in Lean*](https://leanprover.github.io/theorem_proving_in_lean4/)
- [*Functional Programming in Lean*](https://leanprover.github.io/functional_programming_in_lean/)
- Package [`std`](https://github.com/leanprover/std4): standard library for Lean 4.
- Package [`mathlib`](https://leanprover-community.github.io/mathlib4_docs/): mathematical libarary for Lean 4.

## Project setup

```sh
elan self update
elan update
elan default leanprover/lean4:nightly
elan toolchain list
## leanprover/lean4:nightly (default)
lake --version
## Lake version 4.1.0-pre (Lean version 4.0.0-nightly-2023-05-09)
lake init software-foundations
## lean-toolchain: "leanprover/lean4:nightly-2023-05-09"

# Build and run the target binary `grader`:
lake exe grader
```