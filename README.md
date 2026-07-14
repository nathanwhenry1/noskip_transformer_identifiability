# Generic identifiability of no-skip multi-head attention transformers

This repository contains a standalone Lean 4 formalization of generic identifiability for deep causal multi-head softmax-attention transformers **without residual or skip connections**. It is extracted from the larger `any_layer_identifiability_proof_k_heads` development together with exactly the local modules required by the no-skip proof.

## Main result

Let the network have `n + 1` layers, `k ≥ 1` heads per layer, feature dimension `d`, and sequence length `r + 1` with `r ≥ 2`. Under the explicit width condition

```text
d ≥ dStarNS (n + 1) k = max 2 (k * (n + 2)),
```

there is an explicit algebraic exceptional set of parameter choices with Lebesgue measure zero. For every target outside that set, any parameters defining the same transformer on every input differ from the target by exactly:

- a unique permutation of the heads in each layer; and
- a unique boundary-normalized chain of invertible interface gauges.

The formalization also proves the converse: every such permutation and gauge transformation preserves the realization. Consequently, the generic realization fiber is exactly the permutation–gauge orbit, and the orbit parametrization is free. A factor-level theorem additionally recovers the usual inner factorization gauges when attention and value matrices are represented by factors.

The public null-set theorem is:

```lean
theorem identifiability_noSkip_gauge (n k r d : ℕ) (hk : 1 ≤ k) (hr : 2 ≤ r)
    (hd : NLayer.NoSkip.dStarNS (n + 1) k ≤ d) :
    ∃ N : Set (NLayer.NoSkip.Params (n + 1) k d), volume N = 0 ∧
      ∀ θ' ∉ N, ∀ θ : NLayer.NoSkip.Params (n + 1) k d,
        NLayer.NoSkip.TransformerEqualGlobally (r := r) θ θ' →
          Nonempty (NLayer.NoSkip.GenericMatrixIdentifiabilityConclusion θ θ')
```

The conclusion contains the permutation/gauge data, its matrix equations, and a proof that this data is unique.

## Start here

- [`AnyLayerIdentifiabilityProof/Identifiability.lean`](AnyLayerIdentifiabilityProof/Identifiability.lean) — concise public null-set theorem.
- [`AnyLayerIdentifiabilityProof/NLayer/NoSkip/Core.lean`](AnyLayerIdentifiabilityProof/NLayer/NoSkip/Core.lean) — no-skip attention layer and transformer realization.
- [`AnyLayerIdentifiabilityProof/NLayer/NoSkip/IdentifiabilityMain.lean`](AnyLayerIdentifiabilityProof/NLayer/NoSkip/IdentifiabilityMain.lean) — generic matrix identifiability and converse orbit inclusion.
- [`AnyLayerIdentifiabilityProof/NLayer/NoSkip/MatrixFiber.lean`](AnyLayerIdentifiabilityProof/NLayer/NoSkip/MatrixFiber.lean) — exact generic fiber and freeness.
- [`AnyLayerIdentifiabilityProof/NLayer/NoSkip/FactorLevel.lean`](AnyLayerIdentifiabilityProof/NLayer/NoSkip/FactorLevel.lean) — factor-level recovery.
- [`AnyLayerIdentifiabilityProof/NLayer/NoSkip/Audit.lean`](AnyLayerIdentifiabilityProof/NLayer/NoSkip/Audit.lean) — machine-readable checks and axiom reports for the capstone theorems.
- [`problem_statement.md`](problem_statement.md) — mathematical statement in plain language.

The retained `KHead`, `Analytic`, `IDL`, `Foundations`, and genericity modules are shared proof dependencies imported by the no-skip development. The unrelated skip-connection capstone theorem and its public entrypoint are not included.

## Proof architecture

At a high level, the proof combines analytic identification of attention heads, pole-cascade and saturation arguments that transmit information through the composed network, recursive layer peeling, and explicit polynomial certificates showing that all required regularity conditions fail only on a null algebraic set. The final modules package the recovered equations as a unique matching and identify the full realization fiber.

## Verification

The project pins Lean and Mathlib in `lean-toolchain` and `lake-manifest.json`.

```bash
lake exe cache get
make check
```

`make check` verifies that all local imports are present, scans active Lean code for placeholders and project assumptions, builds the full library, and checks the axioms of the advertised theorems. The expected trust boundary is Lean/Mathlib's standard `propext`, `Classical.choice`, and `Quot.sound`; `sorryAx` and project-defined axioms are rejected.
