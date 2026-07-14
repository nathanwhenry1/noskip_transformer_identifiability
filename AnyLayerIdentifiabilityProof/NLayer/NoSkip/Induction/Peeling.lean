import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Induction.Invariant
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Step2.HeadwiseGaugeExtraction
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Genericity.GaugeStability

set_option autoImplicit false

open Matrix

namespace TransformerIdentifiability.NLayer.NoSkip

noncomputable section

/-!
# Gauged first-layer peeling

The first-layer value gauge changes the target tail's input coordinates.  This
file constructs the exact open reduced pair used by the recursive call.
-/

/-- The two input-gauge implementations used by genericity and induction are
definitionally the same action. -/
theorem inputGaugeTail_eq_cascadeInputGaugeAction
    {n k d : Nat} (G : GaugeMatrix d) (theta : Params (n + 1) k d) :
    inputGaugeTail G theta = cascadeInputGaugeAction G theta := by
  rfl

/-- The paired first layer is the target first layer followed by `G⁻¹`. -/
theorem firstLayer_eq_invGauge_mul
    {n k d r : Nat} {theta theta' : Params (n + 2) k d}
    {H : Step1StandingHypotheses r theta theta'} {hr : 1 < r}
    (I : FirstLayerGaugeIdentification H hr)
    {T : Nat} (X : Matrix (Fin d) (Fin T) Real) :
    layer (relabelFirstLayer theta I.gates.sigma) 0 X =
      I.values.gauge.invMatrix * layer theta' 0 X := by
  classical
  let G := I.values.gauge
  have hvalue : ∀ h : Fin k,
      valueMatrix (relabelFirstLayer theta I.gates.sigma) 0 h =
        G.invMatrix * valueMatrix theta' 0 h := by
    intro h
    have heq := I.values.value_eq h
    have horig : valueMatrix theta 0 (I.gates.sigma h) =
        G.invMatrix * valueMatrix theta' 0 h := by
      calc
        valueMatrix theta 0 (I.gates.sigma h) =
            G.invMatrix * (G.matrix * valueMatrix theta 0 (I.gates.sigma h)) := by
          rw [← Matrix.mul_assoc, GaugeMatrix.invMatrix_mul_matrix]
          simp
        _ = G.invMatrix * valueMatrix theta' 0 h := congrArg
          (fun M : Matrix (Fin d) (Fin d) Real => G.invMatrix * M) heq
    simpa using horig
  rw [layer, layer]
  let f : Fin k → Matrix (Fin d) (Fin T) Real := fun a =>
    valueMatrix theta' 0 a * X *
      softmaxColC (Xᵀ * attentionMatrix theta' 0 a * X)
  have hdist : G.invMatrix * (∑ a, f a) = ∑ a, G.invMatrix * f a := by
    simpa using
      (Matrix.mul_sum Finset.univ f G.invMatrix)
  calc
    (∑ a,
        valueMatrix (relabelFirstLayer theta I.gates.sigma) 0 a * X *
          softmaxColC
            (Xᵀ * attentionMatrix (relabelFirstLayer theta I.gates.sigma) 0 a * X)) =
        ∑ a, G.invMatrix * f a := by
      apply Finset.sum_congr rfl
      intro h _hh
      rw [hvalue h, I.gates.relabeled_attention_eq h]
      simp only [f, Matrix.mul_assoc]
    _ = G.invMatrix * ∑ a, f a := hdist.symm

/-- Concrete Step-3 reduced-pair output, before assembling the recursive
matching into a full gauge chain. -/
structure FirstLayerPeelingResult
    {n k d r : Nat} {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (hr : 1 < r) : Type where
  identification : FirstLayerGaugeIdentification H hr
  tail_relabel_eq :
    Fin.tail (relabelFirstLayer theta identification.gates.sigma) = Fin.tail theta
  firstLayer_eq : ∀ {T : Nat} (X : Matrix (Fin d) (Fin T) Real),
    layer (relabelFirstLayer theta identification.gates.sigma) 0 X =
      identification.values.gauge.invMatrix * layer theta' 0 X
  omegaTail : Set (NetworkInput r d)
  omegaTail_open : IsOpen omegaTail
  omegaTail_nonempty : omegaTail.Nonempty
  tail_equal : TransformerEqualOn (r := r) (Fin.tail theta)
    (inputGaugeTail identification.values.gauge (Fin.tail theta')) omegaTail
  gaugedTail_generic : RecursiveGeneric r (n + 1) k d
    (inputGaugeTail identification.values.gauge (Fin.tail theta'))

/-- Build the reduced pair from global equality, local openness of the target
first layer, and gauge stability of recursive genericity. -/
theorem exists_firstLayerPeelingResult
    {n k d r : Nat} {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (hr : 1 < r)
    (hd : 2 ≤ d)
    (heq : ∀ X : NetworkInput r d,
      transformer theta X = transformer theta' X) :
    Nonempty (FirstLayerPeelingResult H hr) := by
  let I : FirstLayerGaugeIdentification H hr :=
    Classical.choice (exists_firstLayerGaugeIdentification H hr hd heq)
  let G := I.values.gauge
  let O : LocalOpenLayerImage r theta' 0 :=
    Classical.choice (H.targetRegularity.localOpenLayerImage r 0)
  let omegaTail : Set (NetworkInput r d) :=
    (fun Y => G.matrix * Y) ⁻¹' O.imageSet
  have homegaOpen : IsOpen omegaTail := by
    have hcont : Continuous (fun Y : NetworkInput r d => G.matrix * Y) := by
      fun_prop
    exact O.image_open.preimage hcont
  have hzeroOmega : (0 : NetworkInput r d) ∈ omegaTail := by
    change G.matrix * (0 : NetworkInput r d) ∈ O.imageSet
    simpa using O.zero_mem_image
  have htailEq : TransformerEqualOn (r := r) (Fin.tail theta)
      (inputGaugeTail G (Fin.tail theta')) omegaTail := by
    intro Y hY
    let Z : NetworkInput r d := G.matrix * Y
    let X : NetworkInput r d := O.localPreimage Z
    have hZ : Z ∈ O.imageSet := hY
    have htargetLayer : layer theta' 0 X = Z := O.right_inverse Z hZ
    have hsourceLayer :
        layer (relabelFirstLayer theta I.gates.sigma) 0 X = Y := by
      rw [firstLayer_eq_invGauge_mul I X, htargetLayer]
      change G.invMatrix * (G.matrix * Y) = Y
      rw [← Matrix.mul_assoc, GaugeMatrix.invMatrix_mul_matrix]
      simp
    have hglobal : transformer (relabelFirstLayer theta I.gates.sigma) X =
        transformer theta' X :=
      (transformer_relabelFirstLayer theta I.gates.sigma X).trans (heq X)
    change
      transformer (Fin.tail (relabelFirstLayer theta I.gates.sigma))
          (layer (relabelFirstLayer theta I.gates.sigma) 0 X) =
        transformer (Fin.tail theta') (layer theta' 0 X) at hglobal
    rw [hsourceLayer, htargetLayer] at hglobal
    rw [transformer_inputGaugeTail]
    simpa [Z] using hglobal
  have htailGeneric : RecursiveGeneric r (n + 1) k d
      (inputGaugeTail G (Fin.tail theta')) := by
    rw [inputGaugeTail_eq_cascadeInputGaugeAction]
    exact (recursiveGeneric_cascadeInputGaugeAction_iff G (Fin.tail theta')).2
      H.target_generic.tail
  exact ⟨{
    identification := I
    tail_relabel_eq := relabelFirstLayer_tail theta I.gates.sigma
    firstLayer_eq := firstLayer_eq_invGauge_mul I
    omegaTail := omegaTail
    omegaTail_open := homegaOpen
    omegaTail_nonempty := ⟨0, hzeroOmega⟩
    tail_equal := htailEq
    gaugedTail_generic := htailGeneric
  }⟩

namespace FirstLayerPeelingResult

variable {n k d r : Nat} {theta theta' : Params (n + 2) k d}
  {H : Step1StandingHypotheses r theta theta'} {hr : 1 < r}

/-- The reduced pair's open-set package. -/
theorem omegaTail_data (P : FirstLayerPeelingResult H hr) :
    NonemptyOpenInputSet P.omegaTail :=
  ⟨P.omegaTail_open, P.omegaTail_nonempty⟩

end FirstLayerPeelingResult

end

end TransformerIdentifiability.NLayer.NoSkip
