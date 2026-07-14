import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.LaurentNormalForm
import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.SigmoidLaurent
import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.FormalPolySplit
import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.SelectedTop
import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.PoleArcs
import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.SiblingAvoidance
-- Original external imports retained so downstream `import …DominanceSibling`
-- keeps the same transitive surface (zero-churn aggregator).
import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.ActiveStratification
import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.SigmoidMixtures
import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.WindowAvoidance

set_option autoImplicit false

open Filter Matrix
open scoped BigOperators

/-!
# Dominance towers and sibling avoidance (K04E) — aggregator

The K04E dominance/sibling development was split into focused sub-files, each
independently ownable and buildable (see `K_HEADS_LEAN_PLAN.md`):

* `Analytic/LaurentNormalForm.lean`  — exact-order Laurent normal forms (C0/C0b)
* `Analytic/SigmoidLaurent.lean`     — import-safe sigmoid Laurent wrappers (C1b)
* `Analytic/FormalPolySplit.lean`    — chain/support/degree calculus & splits (C2)
* `Analytic/SelectedTop.lean`        — multi-affine, selected-top, tower-dominance (C3)
* `Analytic/PoleArcs.lean`           — arc-structure & level-preimage (C5)
* `Analytic/SiblingAvoidance.lean`   — sibling-avoidance & sequence-window (C6/C7)

This file re-exports them and keeps the packet-level `DominanceSiblingAPI`
bundle so existing importers are unaffected.
-/

namespace TransformerIdentifiability.NLayer.KHead

/-! ## Packet-level bundle -/

/-- A compact bundle of the six K04E interfaces, useful for downstream packet
dependencies that want to carry one explicit assumption object. -/
structure DominanceSiblingAPI : Prop where
  multi_affine :
    ∀ {L k d : Nat} {θ : Params L k d} {w v : Vec d},
      MultiAffineResult θ w v
  selected_top :
    ∀ {L k d p : Nat} {θ : Params L k d} {w v : Vec d}
      {c : HeadChain L k p},
      SelectedTopResult θ w v c
  tower_dominance :
    ∀ {L k p : Nat} {c : HeadChain L k p} {f : FormalPoly L k}
      (data : DominanceTowerData c f),
      (∀ i : Fin p, 1 ≤ data.degree i) ->
      data.topConstant ≠ 0 ->
      DominanceTowerTopConstant data ->
      DominanceTowerFinalCoeff data ->
      DominanceTowerEvalRecurrence data ->
      (∀ (i : Nat) (hi : i ≤ p), PolynomialInLayersLE i (data.leadingCoeff i hi)) ->
      TowerDominanceResult c f
  arc_structure :
    ∀ {H : ℂ -> ℂ} {ξ : ℂ} {m : Nat},
      1 ≤ m ->
      ∀ {radius : ℝ}, 0 < radius ->
      ∀ {arcs : Fin (2 * m) -> LevelArcData H ξ},
        (∀ τ ∈ puncturedDisc ξ radius, H τ ∈ imaginaryAxis ->
          ∃ q : Fin (2 * m), ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ radius ∧
            (arcs q).gamma ρ = τ) ->
        (∀ q : Fin (2 * m), ∃ _ : LevelArcPiSequence H ξ radius (arcs q), True) ->
        ArcStructureResult H ξ m
  level_preimage :
    ∀ {H : ℂ -> ℂ} {ξ : ℂ} {m : Nat},
      ArcStructureResult H ξ m -> LevelPreimageResult H ξ
  sibling_avoidance :
    ∀ {Ω : Set ℂ} {ξ : ℂ} {ρ0 : ℝ} {K : Nat}
      {H : Fin (K + 1) -> ℂ -> ℂ},
      SiblingAvoidanceResult Ω ξ ρ0 H -> SiblingAvoidanceConclusion ξ H

/-- The available K04E API scaffold with no placeholder proof terms. -/
theorem dominanceSiblingAPI : DominanceSiblingAPI where
  multi_affine := lem_multi_affine
  selected_top := lem_selected_top
  tower_dominance := lem_tower_dominance
  arc_structure := lem_arc_structure
  level_preimage := lem_level_preimage
  sibling_avoidance := lem_sibling_avoidance

end TransformerIdentifiability.NLayer.KHead
