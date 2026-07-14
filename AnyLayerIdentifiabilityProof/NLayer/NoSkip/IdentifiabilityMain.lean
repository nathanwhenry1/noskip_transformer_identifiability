import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Induction.InductionStep
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Genericity.Null

set_option autoImplicit false

open Matrix

namespace TransformerIdentifiability.NLayer.NoSkip

noncomputable section

/-!
# Generic matrix identifiability

This is the public matrix-level theorem.  The matching object uses the TeX
target-to-source convention and contains the normalized interface gauge chain,
so its two equation fields are exactly `eq:main-conclusion`.
-/

/-- The unique permutation/gauge data asserted by the main theorem. -/
structure GenericMatrixIdentifiabilityConclusion
    {L k d : Nat} (theta theta' : Params L k d) : Type where
  matching : TargetToSourceMatching theta theta'
  unique : ∀ matching' : TargetToSourceMatching theta theta',
    matching' = matching

namespace GenericMatrixIdentifiabilityConclusion

variable {L k d : Nat} {theta theta' : Params L k d}

/-- TeX attention equation, in target-to-source orientation. -/
theorem attention_eq (C : GenericMatrixIdentifiabilityConclusion theta theta')
    (l : Fin L) (h : Fin k) :
    attentionMatrix theta l (C.matching.headPerm l h) =
      ((C.matching.gauge.get l.castSucc).matrix)ᵀ *
        attentionMatrix theta' l h *
          (C.matching.gauge.get l.castSucc).matrix :=
  C.matching.attention_eq l h

/-- TeX value equation, in target-to-source orientation. -/
theorem value_eq (C : GenericMatrixIdentifiabilityConclusion theta theta')
    (l : Fin L) (h : Fin k) :
    valueMatrix theta l (C.matching.headPerm l h) =
      (C.matching.gauge.get l.succ).invMatrix *
        valueMatrix theta' l h *
          (C.matching.gauge.get l.castSucc).matrix :=
  C.matching.value_eq l h

end GenericMatrixIdentifiabilityConclusion

/-- Recursive-generic form of the main theorem. -/
theorem genericMatrixIdentifiability_of_recursiveGeneric
    {n k d r : Nat} (hr : 2 ≤ r) (hd : dStarNS (n + 1) k ≤ d)
    {theta theta' : Params (n + 1) k d}
    (hgeneric : RecursiveGeneric r (n + 1) k d theta')
    (hequal : TransformerEqualGlobally (r := r) theta theta') :
    Nonempty (GenericMatrixIdentifiabilityConclusion theta theta') := by
  let homega : NonemptyOpenInputSet
      (Set.univ : Set (NetworkInput r d)) :=
    ⟨isOpen_univ, Set.univ_nonempty⟩
  have hequalOn : TransformerEqualOn (r := r) theta theta' Set.univ := by
    intro X _hX
    exact hequal X
  let C : OpenInductionInvariantConclusion r theta theta' :=
    Classical.choice
      (openInductionInvariant theta theta' Set.univ hr hd hgeneric homega hequalOn)
  exact ⟨⟨C.matching, C.matching_unique⟩⟩

/-- TeX `thm:main`: outside the explicit algebraic exceptional set, global
equality determines one unique target-to-source permutation family and one
unique boundary-normalized gauge chain satisfying the displayed equations. -/
theorem genericMatrixIdentifiability
    {n k d r : Nat} (hr : 2 ≤ r) (hd : dStarNS (n + 1) k ≤ d)
    (hk : 0 < k) {theta theta' : Params (n + 1) k d}
    (htarget : theta' ∈
      (RecursiveGenericExceptionalSet r (n + 1) k d hd hk)ᶜ)
    (hequal : TransformerEqualGlobally (r := r) theta theta') :
    Nonempty (GenericMatrixIdentifiabilityConclusion theta theta') := by
  apply genericMatrixIdentifiability_of_recursiveGeneric hr hd
  · exact compl_recursiveGenericExceptionalSet_subset hd hk htarget
  · exact hequal

/-- Converse orbit inclusion: every layerwise permutation followed by every
boundary-normalized gauge action preserves the complete realization. -/
theorem permutationGaugeOrbit_realizes
    {L k d T : Nat} (sigma : Fin L → Equiv.Perm (Fin k))
    (G : GaugeChain L d) (theta : Params L k d)
    (X : Matrix (Fin d) (Fin T) Real) :
    transformer (combinedGaugePermuteAction sigma G theta) X =
      transformer theta X :=
  transformer_permute_gauge_invariant G sigma theta X

end

end TransformerIdentifiability.NLayer.NoSkip
