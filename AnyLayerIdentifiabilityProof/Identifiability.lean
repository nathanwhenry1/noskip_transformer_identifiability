/-
Copyright (c) 2026 Nathan W. Henry. All rights reserved.
Authors: Nathan W. Henry
This file is part of the standalone no-skip transformer identifiability formalization.
It exposes the principal null-set theorem through a compact public entrypoint.
-/
import AnyLayerIdentifiabilityProof.NLayer.NoSkip

/-!
# Public no-skip identifiability theorem

This standalone entrypoint exposes the null-set theorem without importing the unrelated
skip-connection realization theorem from the source development.
-/

set_option autoImplicit false

open MeasureTheory Matrix

namespace TransformerIdentifiability

/-- Public null-set form of generic no-skip identifiability. At depth `n+1`, the only
matrix-level ambiguities are the unique per-layer head permutations and the unique
boundary-normalized interface gauge chain recorded by
`NoSkip.GenericMatrixIdentifiabilityConclusion`. -/
theorem identifiability_noSkip_gauge (n k r d : ℕ) (hk : 1 ≤ k) (hr : 2 ≤ r)
    (hd : NLayer.NoSkip.dStarNS (n + 1) k ≤ d) :
    ∃ N : Set (NLayer.NoSkip.Params (n + 1) k d), volume N = 0 ∧
      ∀ θ' ∉ N, ∀ θ : NLayer.NoSkip.Params (n + 1) k d,
        NLayer.NoSkip.TransformerEqualGlobally (r := r) θ θ' →
          Nonempty (NLayer.NoSkip.GenericMatrixIdentifiabilityConclusion θ θ') := by
  have hk0 : 0 < k := hk
  let N := NLayer.NoSkip.RecursiveGenericExceptionalSet
    r (n + 1) k d hd hk0
  refine ⟨N, NLayer.NoSkip.recursiveGenericExceptionalSet_null hd hk0, ?_⟩
  intro θ' hθ' θ hequal
  apply NLayer.NoSkip.genericMatrixIdentifiability hr hd hk0
  · exact hθ'
  · exact hequal

end TransformerIdentifiability
