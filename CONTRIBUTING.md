# Contributing

Corrections are welcome as focused pull requests. For a mathematical or Lean change:

1. identify the affected Lean declaration;
2. explain the corresponding mathematical change;
3. keep the pinned toolchain unless the pull request is specifically a toolchain upgrade;
4. run `make imports` and `make audit`;
5. run `lake build` and `make axioms`;
6. include the relevant axiom output when a theorem dependency changes.

Equivalently, `make check` runs all verification steps in order.

For exposition changes, preserve mathematical attribution and keep links usable for readers who do not know Lean.
