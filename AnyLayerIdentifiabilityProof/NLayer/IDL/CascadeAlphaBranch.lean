import AnyLayerIdentifiabilityProof.NLayer.IDL.CascadeSaturation
import AnyLayerIdentifiabilityProof.NLayer.IDL.CascadeStep
import AnyLayerIdentifiabilityProof.NLayer.IDL.CascadeZeroBranchConnective

set_option autoImplicit false

open Matrix

namespace TransformerIdentifiability.NLayer

/-!
# R3 zero-branch alpha saturation

This file isolates the reusable alpha branch of the cascade argument.  The analytic
estimate is already proved in `CascadeSaturation` as
`eventuallyExpClose_sig_tau_mul_of_eventuallyExpClose_zero`; here we expose it in the
forms needed by actual running gates and by the `TrichotomyData.unprimed_saturates`
field.

The remaining broad estimate in the TeX proof is the Lipschitz/error comparison between
the actual level slope and the formal zero-curve slope after the prior gates have
saturated.  That estimate is packaged as `CascadeAlphaSlopeErrorBound`, so downstream
code can prove the bound separately and immediately obtain the alpha branch.
-/

/-! ## Pure sigmoid wrappers -/

/-- Rate-free alpha wrapper for the zero-slope saturation lemma. -/
noncomputable def eventuallyExpClose_sig_tau_mul_alpha_of_eventuallyExpClose_zero
    {lam : ℝ -> ℝ} {b : ℝ} (h : EventuallyExpClose lam 0) :
    EventuallyExpClose (fun τ => sig (τ * lam τ + b)) (sig b) :=
  eventuallyExpClose_sig_tau_mul_of_eventuallyExpClose_zero
    (lam := lam) (b := b) (c := h.rate / 2) h
    (by linarith [h.rate_pos])
    (by linarith [h.rate_pos])

/-- If a gate is pointwise `sig (τ * lam τ + b)` and `lam` is exponentially close to
zero, then the gate is exponentially close to the constant `sig b`. -/
noncomputable def eventuallyExpClose_gate_alpha_of_slope_zero
    {gate lam : ℝ -> ℝ} {b : ℝ}
    (hgate : ∀ τ : ℝ, gate τ = sig (τ * lam τ + b))
    (hlam : EventuallyExpClose lam 0) :
    EventuallyExpClose gate (sig b) := by
  let hsig :=
    eventuallyExpClose_sig_tau_mul_alpha_of_eventuallyExpClose_zero
      (lam := lam) (b := b) hlam
  refine ⟨hsig.rate, hsig.rate_pos, hsig.coeff, hsig.coeff_nonneg, hsig.start, ?_⟩
  intro τ hτ
  rw [hgate τ]
  exact hsig.bound τ hτ

/-! ## The zero curve from affine `gamma` -/

/-- An affine `gamma` is identically zero once it vanishes at `0` and `1`. -/
theorem cascadeCurveRigidity_gamma_eq_zero_of_eval_zero_one
    {L d : Nat} {θ : Params L d} {A : Matrix (Fin d) (Fin d) ℝ}
    {level : Nat} {tail : Nat -> ℝ}
    (D : CascadeCurveRigidityData θ A level tail)
    (hgamma : D.gamma 0 = 0 ∧ D.gamma 1 = 0) :
    ∀ z : ℂ, D.gamma z = 0 := by
  rcases D.gamma_affine with ⟨gamma0, gamma1, hgamma_affine⟩
  have hgamma0 : gamma0 = 0 := by
    calc
      gamma0 = D.gamma 0 := by simpa using (hgamma_affine 0).symm
      _ = 0 := hgamma.1
  have hsum : gamma0 + gamma1 = 0 := by
    calc
      gamma0 + gamma1 = D.gamma 1 := by simpa using (hgamma_affine 1).symm
      _ = 0 := hgamma.2
  have hgamma1 : gamma1 = 0 := by
    calc
      gamma1 = gamma0 + gamma1 := by simp [hgamma0]
      _ = 0 := hsum
  intro z
  calc
    D.gamma z = gamma0 + gamma1 * z := hgamma_affine z
    _ = 0 := by simp [hgamma0, hgamma1]

/-- Curve-rigidity zero branch: if `gamma` vanishes at `0` and `1`, the specialized
formal slope on the `tail` curve is exactly zero for every first gate and probe. -/
theorem cascadeCurveRigidity_specializedPhi_eq_zero_of_gamma_eval_zero_one
    {L d : Nat} {θ : Params L d} {A : Matrix (Fin d) (Fin d) ℝ}
    {level : Nat} {tail : Nat -> ℝ}
    (D : CascadeCurveRigidityData θ A level tail)
    (hgamma : D.gamma 0 = 0 ∧ D.gamma 1 = 0)
    (z : ℂ) (p : ProbePair d) :
    specializedPhi θ level (complexGateAssignmentOfTail z tail) p = 0 := by
  rw [D.curve_identity z p,
    cascadeCurveRigidity_gamma_eq_zero_of_eval_zero_one D hgamma z]
  simp

/-! ## Packaging the missing Lipschitz/error estimate -/

/-- The auxiliary alpha-branch error estimate.

For each base point `x`, `headGate x τ` is the running first gate on the dial path,
`path x τ` is the running probe pair, and `lam x τ` is the actual level slope.  The field
states the precise missing estimate: once all prior gates are exponentially close to the
prescribed `tail`, the actual slope is exponentially close to the formal tail-curve slope.

When `CascadeCurveRigidityData` has `gamma(0)=gamma(1)=0`, that formal slope is exactly
zero by the theorem above, so this package yields the desired slope-close-to-zero fact. -/
structure CascadeAlphaSlopeErrorBound {L d : Nat}
    (θ : Params L d) (A : Matrix (Fin d) (Fin d) ℝ)
    (level : Nat) (tail : Nat -> ℝ)
    (U : Set (ProbePair d × ℝ)) (gate : GateAlongBase d)
    (headGate : ProbePair d × ℝ -> ℝ -> ℝ)
    (path : ProbePair d × ℝ -> ℝ -> ProbePair d)
    (lam : ProbePair d × ℝ -> ℝ -> ℝ) where
  slope_error :
    (∀ x ∈ U, ∀ n : Nat, 1 ≤ n -> n < level ->
      EventuallyExpClose (fun τ => gate n x τ) (tail (n - 1))) ->
    ∀ x ∈ U,
      EventuallyExpClose
        (fun τ =>
          lam x τ -
            (specializedPhi θ level
              (complexGateAssignmentOfTail ((headGate x τ : ℝ) : ℂ) tail)
              (path x τ)).re)
        0

/-- Curve-rigidity plus the packaged error estimate imply that the actual level slope is
exponentially close to zero. -/
noncomputable def cascadeAlphaSlope_zero_of_curveRigidity
    {L d : Nat} {θ : Params L d} {A : Matrix (Fin d) (Fin d) ℝ}
    {level : Nat} {tail : Nat -> ℝ}
    {U : Set (ProbePair d × ℝ)} {gate : GateAlongBase d}
    {headGate : ProbePair d × ℝ -> ℝ -> ℝ}
    {path : ProbePair d × ℝ -> ℝ -> ProbePair d}
    {lam : ProbePair d × ℝ -> ℝ -> ℝ}
    (D : CascadeCurveRigidityData θ A level tail)
    (hgamma : D.gamma 0 = 0 ∧ D.gamma 1 = 0)
    (E : CascadeAlphaSlopeErrorBound θ A level tail U gate headGate path lam)
    (hprior :
      ∀ x ∈ U, ∀ n : Nat, 1 ≤ n -> n < level ->
        EventuallyExpClose (fun τ => gate n x τ) (tail (n - 1)))
    (x : ProbePair d × ℝ) (hx : x ∈ U) :
    EventuallyExpClose (fun τ => lam x τ) 0 := by
  let herror := E.slope_error hprior x hx
  refine
    ⟨herror.rate, herror.rate_pos, herror.coeff, herror.coeff_nonneg,
      herror.start, ?_⟩
  intro τ hτ
  have hcurve :
      (specializedPhi θ level
        (complexGateAssignmentOfTail ((headGate x τ : ℝ) : ℂ) tail)
        (path x τ)).re = 0 := by
    rw [cascadeCurveRigidity_specializedPhi_eq_zero_of_gamma_eval_zero_one
      D hgamma ((headGate x τ : ℝ) : ℂ) (path x τ)]
    simp
  simpa [hcurve] using herror.bound τ hτ

/-! ## Alpha branch in `TrichotomyData.unprimed_saturates` shape -/

/-- A level-local alpha saturation theorem in exactly the shape needed for the
`TrichotomyData.unprimed_saturates` field once `varsigma level = sig b`. -/
noncomputable def trichotomyData_unprimed_saturates_alphaBranchAt
    {d : Nat} {b : ℝ} {Ustar : Set (ProbePair d × ℝ)}
    {unprimed : GateAlongBase d} {level : Nat} {varsigma : Nat -> ℝ}
    {lam : ProbePair d × ℝ -> ℝ -> ℝ}
    (hvarsigma : varsigma level = sig b)
    (hgate :
      ∀ x ∈ Ustar, ∀ τ : ℝ,
        unprimed level x τ = sig (τ * lam x τ + b))
    (hslope :
      ∀ x ∈ Ustar, EventuallyExpClose (fun τ => lam x τ) 0) :
    ∀ x ∈ Ustar,
      EventuallyExpClose (fun τ => unprimed level x τ) (varsigma level) := by
  intro x hx
  rw [hvarsigma]
  exact
    eventuallyExpClose_gate_alpha_of_slope_zero
      (gate := fun τ => unprimed level x τ)
      (lam := fun τ => lam x τ)
      (b := b)
      (hgate x hx)
      (hslope x hx)

/-- Combined zero-branch theorem: curve-rigidity, the packaged slope error estimate, and
the pointwise sigmoid form of the actual gate produce the alpha saturation obligation for
one unprimed trichotomy level. -/
noncomputable def trichotomyData_unprimed_saturates_alphaBranchAt_of_curveRigidity
    {L d : Nat} {θ : Params L d} {A : Matrix (Fin d) (Fin d) ℝ}
    {b : ℝ} {level : Nat} {tail : Nat -> ℝ}
    {Ustar : Set (ProbePair d × ℝ)} {unprimed : GateAlongBase d}
    {varsigma : Nat -> ℝ}
    {headGate : ProbePair d × ℝ -> ℝ -> ℝ}
    {path : ProbePair d × ℝ -> ℝ -> ProbePair d}
    {lam : ProbePair d × ℝ -> ℝ -> ℝ}
    (hvarsigma : varsigma level = sig b)
    (hgate :
      ∀ x ∈ Ustar, ∀ τ : ℝ,
        unprimed level x τ = sig (τ * lam x τ + b))
    (D : CascadeCurveRigidityData θ A level tail)
    (hgamma : D.gamma 0 = 0 ∧ D.gamma 1 = 0)
    (E : CascadeAlphaSlopeErrorBound θ A level tail Ustar unprimed headGate path lam)
    (hprior :
      ∀ x ∈ Ustar, ∀ n : Nat, 1 ≤ n -> n < level ->
        EventuallyExpClose (fun τ => unprimed n x τ) (tail (n - 1))) :
    ∀ x ∈ Ustar,
      EventuallyExpClose (fun τ => unprimed level x τ) (varsigma level) :=
  trichotomyData_unprimed_saturates_alphaBranchAt
    (b := b) (Ustar := Ustar) (unprimed := unprimed)
    (level := level) (varsigma := varsigma) (lam := lam)
    hvarsigma hgate
    (fun x hx =>
      cascadeAlphaSlope_zero_of_curveRigidity
        (D := D) (hgamma := hgamma) (E := E) hprior x hx)

end TransformerIdentifiability.NLayer
