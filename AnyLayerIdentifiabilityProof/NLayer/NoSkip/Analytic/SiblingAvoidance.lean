import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Analytic.PoleArcs
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Genericity.Regularity

set_option autoImplicit false

open Filter Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.NoSkip

/-!
# Local same-layer sibling separation

This file extracts only the local input required before the later dominance
argument.  The selected head receives its exact NS097 pole arc, while NS049's
all-alpha corner difference proves that no distinct same-layer level is the
same holomorphic function on the current domain.  No sequence-window endgame,
dominance tier, or network evaluation is imported.
-/

noncomputable section

/-- Complex evaluation of a NoSkip formal slope at the constant all-alpha gate
assignment. -/
theorem complexFormalSlope_allAlpha {r L k d : Nat}
    (theta : Params L k d) (w v : Vec d) (l : Fin L) (a : Fin k) :
    complexFormalSlope theta w v (fun _ => (alpha r : ℂ)) (l, a) =
      (matrixBilin (attentionMatrix theta l a)
        (((1 - alpha r) ^ l.1) •
          (alphaCornerCPrefix r theta l.1 (Nat.le_of_lt l.2) *ᵥ w))
        (alphaCornerCPrefix r theta l.1 (Nat.le_of_lt l.2) *ᵥ
          (v + (1 - (1 - alpha r) ^ l.1) • w)) : ℂ) := by
  let rho : FormalAssignment L k :=
    frozenGateAssignment (allAlphaGateFamily r L k)
  have hrho : (fun _ : FormalVar L k => (alpha r : ℂ)) =
      fun x => (rho x : ℂ) := by
    funext x
    rcases x with ⟨l', a'⟩
    simp [rho]
  rw [complexFormalSlope, hrho, evalFormalPolyComplex_ofReal,
    eval_formalSlope]
  have hstreams := alphaCornerStreams r theta l w v
  rw [hstreams.1, hstreams.2]

/-- Difference form of the all-alpha slope evaluation, matching NS049's
`alphaCornerSlopeDiff`. -/
theorem complexFormalSlope_allAlpha_sub {r L k d : Nat}
    (theta : Params L k d) (w v : Vec d) (l : Fin L) (a c : Fin k) :
    complexFormalSlope theta w v (fun _ => (alpha r : ℂ)) (l, a) -
        complexFormalSlope theta w v (fun _ => (alpha r : ℂ)) (l, c) =
      (alphaCornerSlopeDiff r theta l a c w v : ℂ) := by
  rw [complexFormalSlope_allAlpha, complexFormalSlope_allAlpha]
  unfold alphaCornerSlopeDiff
  norm_cast
  symm
  apply TransformerIdentifiability.NLayer.matrixBilin_sub

/-- The derivative at the corner of a formal level is its all-alpha formal
slope. -/
theorem formalLevel_hasDerivAt_zero_allAlpha {r L k d : Nat}
    (theta : Params L k d) (w v : Vec d) (x : FormalVar L k)
    (eta : FormalVar L k → ℂ → ℂ)
    (heta : ∀ y : FormalVar L k, AnalyticAt ℂ (eta y) 0)
    (heta_zero : ∀ y : FormalVar L k, eta y 0 = (alpha r : ℂ)) :
    HasDerivAt
      (fun tau => formalLevel (r := r) theta w v (fun y => eta y tau) x tau)
      (complexFormalSlope theta w v (fun _ => (alpha r : ℂ)) x) 0 := by
  have hslope_analytic : AnalyticAt ℂ
      (fun tau => complexFormalSlope theta w v (fun y => eta y tau) x) 0 := by
    have heta_on : ∀ y : FormalVar L k,
        AnalyticOnNhd ℂ (eta y) ({0} : Set ℂ) := by
      intro y z hz
      simp only [Set.mem_singleton_iff] at hz
      subst z
      exact heta y
    exact complexFormalSlope_analyticOnNhd theta w v x heta_on 0 (by simp)
  have hmul := (hasDerivAt_id (𝕜 := ℂ) (0 : ℂ)).mul
    hslope_analytic.differentiableAt.hasDerivAt
  have hadd := hmul.add_const (logScale r : ℂ)
  simpa [formalLevel, heta_zero] using hadd

/-- Distinct heads have distinct formal level germs at the all-alpha corner
whenever the NS049 corner certificate is nonzero. -/
theorem formalLevel_not_eqOn_of_alphaCornerSlopeDiff_ne_zero
    {r L k d : Nat} (theta : Params L k d) (w v : Vec d)
    (l : Fin L) {a c : Fin k} (Omega : Set ℂ)
    (hOmega : IsOpen Omega) (hzero : (0 : ℂ) ∈ Omega)
    (eta : FormalVar L k → ℂ → ℂ)
    (heta : ∀ y : FormalVar L k, AnalyticAt ℂ (eta y) 0)
    (heta_zero : ∀ y : FormalVar L k, eta y 0 = (alpha r : ℂ))
    (hcorner : alphaCornerSlopeDiff r theta l a c w v ≠ 0) :
    ¬ Set.EqOn
      (fun tau => formalLevel (r := r) theta w v
        (fun y => eta y tau) (l, a) tau)
      (fun tau => formalLevel (r := r) theta w v
        (fun y => eta y tau) (l, c) tau)
      Omega := by
  intro hEqOn
  let Fa : ℂ → ℂ := fun tau => formalLevel (r := r) theta w v
    (fun y => eta y tau) (l, a) tau
  let Fc : ℂ → ℂ := fun tau => formalLevel (r := r) theta w v
    (fun y => eta y tau) (l, c) tau
  have hFa := formalLevel_hasDerivAt_zero_allAlpha
    (r := r) theta w v (l, a) eta heta heta_zero
  have hFc := formalLevel_hasDerivAt_zero_allAlpha
    (r := r) theta w v (l, c) eta heta heta_zero
  have hdiff : HasDerivAt (fun tau => Fa tau - Fc tau)
      ((alphaCornerSlopeDiff r theta l a c w v : ℝ) : ℂ) 0 := by
    have hsub := hFa.sub hFc
    simpa [Fa, Fc, complexFormalSlope_allAlpha_sub] using hsub
  have heq_eventually : (fun tau => Fa tau - Fc tau) =ᶠ[nhds 0]
      fun _ => (0 : ℂ) := by
    filter_upwards [hOmega.mem_nhds hzero] with tau htau
    simp [Fa, Fc, hEqOn htau]
  have hzeroDeriv : HasDerivAt (fun tau => Fa tau - Fc tau) 0 0 :=
    (hasDerivAt_const (x := (0 : ℂ)) (c := (0 : ℂ))).congr_of_eventuallyEq
      heq_eventually
  have hderiv_zero : (((alphaCornerSlopeDiff r theta l a c w v : ℝ) : ℂ)) = 0 :=
    hdiff.unique hzeroDeriv
  exact hcorner (Complex.ofReal_eq_zero.mp hderiv_zero)

/-- Local output consumed by the later selected-top/sibling analysis. -/
structure ActiveSiblingLocalData {r L k d : Nat}
    (theta : Params L k d) (D : ActiveStratificationData L k d)
    (l : Fin L) (selected : Fin k) (xi : ℂ) : Prop where
  selected_active : selected ∈ activeHeads theta l
  center_mem_stratum : xi ∈ D.stratum l.1
  selected_hits_Pi : D.level (l, selected) xi ∈ Pi
  siblings_not_identical :
    ∀ c : Fin k, c ≠ selected →
      ¬ Set.EqOn (D.level (l, selected)) (D.level (l, c)) (D.Omega l.1)
  selected_arc :
    ∃ kappa : Nat, ∃ coeff : ℂ, 1 ≤ kappa ∧ coeff ≠ 0 ∧
      LaurentNormalFormAt
        (fun z => D.level (l, selected) z - D.level (l, selected) xi)
        xi (-(kappa : ℤ)) coeff ∧
      Nonempty (SelectedArcData
        (fun z => csig (D.level (l, selected) z)) xi kappa coeff⁻¹)

/-- NS099 local sibling-avoidance theorem: NS097 supplies the selected pole arc,
and the NS049 corner certificate rules out every distinct sibling germ. -/
theorem activeSiblingLocalData_of_cornerCertificate
    {r L k d : Nat} {theta : Params L k d}
    {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification (r := r) theta D)
    (w v : Vec d) (l : Fin L) (selected : Fin k) {xi : ℂ}
    (hselected : selected ∈ activeHeads theta l)
    (hxi : xi ∈ D.stratum l.1)
    (hxiPi : D.level (l, selected) xi ∈ Pi)
    (eta : FormalVar L k → ℂ → ℂ)
    (heta : ∀ y : FormalVar L k, AnalyticAt ℂ (eta y) 0)
    (heta_zero : ∀ y : FormalVar L k, eta y 0 = (alpha r : ℂ))
    (hlevel : ∀ a : Fin k, D.level (l, a) =
      fun tau => formalLevel (r := r) theta w v
        (fun y => eta y tau) (l, a) tau)
    (hcorner : ∀ c : Fin k, c ≠ selected →
      alphaCornerSlopeDiff r theta l selected c w v ≠ 0) :
    ActiveSiblingLocalData (r := r) theta D l selected xi := by
  have hxiOmega : xi ∈ D.Omega l.1 :=
    (hD.stratum_closedDiscrete l).subset hxi
  obtain ⟨kappa, coeff, hkappa, hcoeff, hNF, hArc⟩ :=
    activeLevel_sigmoid_selectedArcData
      hD l selected hselected hxiOmega hxiPi
  refine
    { selected_active := hselected
      center_mem_stratum := hxi
      selected_hits_Pi := hxiPi
      siblings_not_identical := ?_
      selected_arc := ⟨kappa, coeff, hkappa, hcoeff, hNF, hArc⟩ }
  intro c hc
  rw [hlevel selected, hlevel c]
  exact formalLevel_not_eqOn_of_alphaCornerSlopeDiff_ne_zero
    theta w v l (D.Omega l.1)
      (hD.domain l.1 (Nat.le_of_lt l.2)).isOpen
      (hD.origin_mem l.1 (Nat.le_of_lt l.2))
      eta heta heta_zero (hcorner c hc)

end

end TransformerIdentifiability.NLayer.NoSkip
