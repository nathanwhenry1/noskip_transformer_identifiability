import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Step1.PoleTransfer
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Induction.Relabel

set_option autoImplicit false

open Matrix

namespace TransformerIdentifiability.NLayer.NoSkip

noncomputable section

/-!
# Step 1 first-attention export

This file packages the unique target-to-source first-layer permutation proved
in `PoleTransfer` and records the relabeled-source interface consumed by the
repaired headwise Step 2.
-/

/-- Relabeling the first-layer heads leaves that layer map unchanged. -/
theorem layer_relabelFirstLayer_zero {m k d T : Nat}
    (theta : Params (m + 1) k d) (sigma : Equiv.Perm (Fin k))
    (X : Matrix (Fin d) (Fin T) ℝ) :
    layer (relabelFirstLayer theta sigma) 0 X = layer theta 0 X := by
  classical
  simp only [layer]
  simpa [relabelFirstLayer, valueMatrix, attentionMatrix] using
    (Equiv.sum_comp sigma fun a : Fin k =>
      valueMatrix theta 0 a * X *
        softmaxColC (Xᵀ * attentionMatrix theta 0 a * X))

/-- First-layer relabeling preserves the complete transformer. -/
theorem transformer_relabelFirstLayer {m k d T : Nat}
    (theta : Params (m + 1) k d) (sigma : Equiv.Perm (Fin k))
    (X : Matrix (Fin d) (Fin T) ℝ) :
    transformer (relabelFirstLayer theta sigma) X = transformer theta X := by
  show transformer (Fin.tail (relabelFirstLayer theta sigma))
      (layer (relabelFirstLayer theta sigma) 0 X) =
    transformer (Fin.tail theta) (layer theta 0 X)
  rw [relabelFirstLayer_tail, layer_relabelFirstLayer_zero]

/-- Consequently, first-layer relabeling preserves every positive-real probe
output. -/
theorem globalProbeOutputEquality_relabelFirstLayer {r m k d : Nat}
    (hr : 0 < r) (theta : Params (m + 1) k d)
    (sigma : Equiv.Perm (Fin k)) :
    GlobalProbeOutputEquality r (relabelFirstLayer theta sigma) theta :=
  globalProbeOutputEquality_of_transformer hr
    (fun X => transformer_relabelFirstLayer theta sigma X)

@[simp] theorem attentionMatrix_relabelFirstLayer_zero {m k d : Nat}
    (theta : Params (m + 1) k d) (sigma : Equiv.Perm (Fin k)) (h : Fin k) :
    attentionMatrix (relabelFirstLayer theta sigma) 0 h =
      attentionMatrix theta 0 (sigma h) := by
  simp only [Params.attentionMatrix_apply, relabelFirstLayer_zero]

@[simp] theorem valueMatrix_relabelFirstLayer_zero {m k d : Nat}
    (theta : Params (m + 1) k d) (sigma : Equiv.Perm (Fin k)) (h : Fin k) :
    valueMatrix (relabelFirstLayer theta sigma) 0 h =
      valueMatrix theta 0 (sigma h) := by
  simp only [Params.valueMatrix_apply, relabelFirstLayer_zero]

/-- Minimal Step-2 export of the Step-1 result. -/
structure Step1CommonFirstGates
    {n k d r : Nat} {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (hr : 1 < r) where
  sigma : Equiv.Perm (Fin k)
  attention_eq : ∀ h : Fin k,
    attentionMatrix theta 0 (sigma h) = attentionMatrix theta' 0 h
  attention_unique : ∀ rho : Equiv.Perm (Fin k),
    (∀ h : Fin k,
      attentionMatrix theta 0 (rho h) = attentionMatrix theta' 0 h) →
    rho = sigma
  source_all_active : ∀ a : Fin k,
    a ∈ activeHeads theta (0 : Fin (n + 2))
  slope_eq : ∀ h : Fin k, ∀ w v : Vec d,
    matrixBilin (attentionMatrix theta 0 (sigma h)) w v =
      matrixBilin (attentionMatrix theta' 0 h) w v

/-- Construct the common-first-gates package from the unique global
permutation and the all-active byproduct of pointwise matching. -/
noncomputable def step1CommonFirstGates
    {n k d r : Nat} {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (hr : 1 < r) :
    Step1CommonFirstGates H hr := by
  classical
  let hperm := step1FirstAttentionPermutation H hr
  let sigma := Classical.choose hperm
  have hsigma := (Classical.choose_spec hperm).1
  have hsigmaUnique := (Classical.choose_spec hperm).2
  let P := step1SeparatedProbePackage H
  let p : ProbePoint d := (P.w, P.v)
  have hp : p ∈ step1SeparatedProbePairs H := by
    change alphaCornerProbeEval P.w P.v ∈ step1SeparatedSet H
    simpa [P, Step1SeparatedProbePackage.w, Step1SeparatedProbePackage.v] using P.mem
  refine
    { sigma := sigma
      attention_eq := hsigma
      attention_unique := hsigmaUnique
      source_all_active := ?_
      slope_eq := ?_ }
  · intro a
    exact step1FirstLayer_allHeadsActive H hr hp a
  · intro h w v
    rw [hsigma h]

namespace Step1CommonFirstGates

variable {n k d r : Nat} {theta theta' : Params (n + 2) k d}
  {H : Step1StandingHypotheses r theta theta'} {hr : 1 < r}

/-- Every source head matched to a target head is active. -/
theorem matched_active (G : Step1CommonFirstGates H hr) (h : Fin k) :
    G.sigma h ∈ activeHeads theta (0 : Fin (n + 2)) :=
  G.source_all_active _

/-- After paired relabeling, first attention matrices agree head by head. -/
theorem relabeled_attention_eq (G : Step1CommonFirstGates H hr) (h : Fin k) :
    attentionMatrix (relabelFirstLayer theta G.sigma) 0 h =
      attentionMatrix theta' 0 h := by
  simpa using G.attention_eq h

/-- Function-valued form consumed by the headwise dial API. -/
theorem relabeled_attention_family_eq (G : Step1CommonFirstGates H hr) :
    attentionMatrix (relabelFirstLayer theta G.sigma) 0 =
      attentionMatrix theta' 0 := by
  funext h
  exact G.relabeled_attention_eq h

/-- The relabeled source retains the standing probe-output equality with the
target. -/
theorem relabeled_probe_equal (G : Step1CommonFirstGates H hr) :
    GlobalProbeOutputEquality r (relabelFirstLayer theta G.sigma) theta' := by
  intro w v tau htau
  exact (globalProbeOutputEquality_relabelFirstLayer H.r_pos theta G.sigma
    w v tau htau).trans (H.probe_equal w v tau htau)

/-- Exact equality of every paired first-layer gate on arbitrary real probes. -/
theorem relabeled_firstGate_eq (G : Step1CommonFirstGates H hr)
    (w v : Vec d) (tau : ℝ) (h : Fin k) :
    actualProbeGate r (relabelFirstLayer theta G.sigma) w v tau
        (0 : Fin (n + 2)) h =
      actualProbeGate r theta' w v tau (0 : Fin (n + 2)) h := by
  rw [actualProbeGate_eq_sig, actualProbeGate_eq_sig]
  change sig (tau * matrixBilin
      (attentionMatrix (relabelFirstLayer theta G.sigma) 0 h) w v + logScale r) =
    sig (tau * matrixBilin (attentionMatrix theta' 0 h) w v + logScale r)
  rw [G.relabeled_attention_eq h]

end Step1CommonFirstGates

/-- Prop-valued first-attention capstone. -/
theorem step1FirstAttentionIdentified
    {n k d r : Nat} {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (hr : 1 < r) :
    Nonempty (Step1CommonFirstGates H hr) :=
  ⟨step1CommonFirstGates H hr⟩

end

end TransformerIdentifiability.NLayer.NoSkip
