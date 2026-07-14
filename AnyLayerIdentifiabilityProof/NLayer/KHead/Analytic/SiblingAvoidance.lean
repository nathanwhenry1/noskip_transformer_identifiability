import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.PoleArcs
import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.WindowAvoidance
import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.ActiveStratification

set_option autoImplicit false

open Filter Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.KHead

/-! ## `lem:sibling-avoidance` -/

/-- Hypotheses for the sibling-avoidance problem at a fixed probe.  The hard
sequence-window argument is kept as a separate result object below; these are
the ambient analytic and separation assumptions that argument consumes. -/
structure SiblingAvoidanceHypotheses (Ω : Set ℂ) (ξ : ℂ) (ρ0 : ℝ)
    {K : Nat} (H : Fin (K + 1) -> ℂ -> ℂ) : Prop where
  omega_domain : PlaneDomain Ω
  nonneg_subset : {τ : ℂ | ∃ t : ℝ, 0 ≤ t ∧ τ = t} ⊆ Ω
  center_notMem : ξ ∉ Ω
  puncturedDisc_subset : puncturedDisc ξ ρ0 ⊆ Ω
  radius_pos : 0 < ρ0
  analytic_on_omega : ∀ c : Fin (K + 1), AnalyticOnNhd ℂ (H c) Ω
  meromorphic_at_center : ∀ c : Fin (K + 1), MeromorphicAt (H c) ξ
  common_real_value :
    ∃ b : ℝ, b ≠ 0 ∧ ∀ c : Fin (K + 1), H c 0 = (b : ℂ)
  real_valued_on_nonnegative :
    ∀ c : Fin (K + 1), IsRealValuedOn (H c) nonnegativeRealAxis
  selected_has_pole : ¬ AnalyticAt ℂ (H 0) ξ
  sibling_not_identical :
    ∀ c : Fin K, ¬ Set.EqOn (H c.succ) (H 0) Ω

/-- Conclusion of the finite sibling-avoidance problem. -/
def SiblingAvoidanceConclusion (ξ : ℂ) {K : Nat} (H : Fin (K + 1) -> ℂ -> ℂ) : Prop :=
  ∀ ρ : ℝ, 0 < ρ ->
    {τ | τ ∈ puncturedDisc ξ ρ ∧ H 0 τ ∈ Pi ∧
      ∀ c : Fin K, H c.succ τ ∉ Pi}.Infinite

/-- Collision points where the selected branch and one sibling both hit `Π`
inside the same punctured disc. -/
def siblingCollisionIn (ξ : ℂ) {K : Nat} (H : Fin (K + 1) -> ℂ -> ℂ)
    (ρ : ℝ) (c : Fin K) : Set ℂ :=
  {τ | τ ∈ puncturedDisc ξ ρ ∧ H 0 τ ∈ Pi ∧ H c.succ τ ∈ Pi}

/-- Ambient selected/sibling collision set, before restricting to a punctured disc. -/
def siblingCollisionSet {K : Nat} (H : Fin (K + 1) -> ℂ -> ℂ) (c : Fin K) :
    Set ℂ :=
  {τ | H 0 τ ∈ Pi ∧ H c.succ τ ∈ Pi}

/-- Domain-restricted selected/sibling collision set. -/
def siblingCollisionInDomain (Ω : Set ℂ) {K : Nat}
    (H : Fin (K + 1) -> ℂ -> ℂ) (c : Fin K) : Set ℂ :=
  Ω ∩ siblingCollisionSet H c

/-- Analytic functions are continuous on their domain of analyticity. -/
theorem continuousOn_of_analyticOnNhd {Ω : Set ℂ} {H : ℂ -> ℂ}
    (hH : AnalyticOnNhd ℂ H Ω) :
    ContinuousOn H Ω := by
  intro τ hτ
  exact (hH τ hτ).continuousAt.continuousWithinAt

/-- A nonconstant holomorphic level function has closed-discrete odd-pi
preimage in its plane domain. -/
theorem closedDiscrete_levelPreimageInDomain {Ω : Set ℂ} {H : ℂ -> ℂ}
    (hΩ : PlaneDomain Ω) (hH : AnalyticOnNhd ℂ H Ω)
    (hHnonconst : ∀ c : ℂ, ¬ Set.EqOn H (fun _ : ℂ => c) Ω) :
    ClosedDiscreteIn (Ω ∩ H ⁻¹' Pi) Ω :=
  closedDiscrete_preimage hΩ.isOpen hΩ.isPreconnected hH hHnonconst Pi_closedDiscrete

/-- Relative closedness of an odd-pi preimage for an analytic function on a
domain.  This does not require the function to be nonconstant. -/
theorem isClosed_rel_levelPreimageInDomain {Ω : Set ℂ} {H : ℂ -> ℂ}
    (hΩopen : IsOpen Ω) (hH : AnalyticOnNhd ℂ H Ω) :
    IsClosed (Ωᶜ ∪ (Ω ∩ H ⁻¹' Pi)) := by
  have hclosedPi : IsClosed Pi := by
    simpa using Pi_closedDiscrete.isClosed_rel
  rw [← isOpen_compl_iff]
  have hopen_compl : IsOpen (Ω ∩ H ⁻¹' Piᶜ) := by
    rw [isOpen_iff_mem_nhds]
    intro τ hτ
    have hΩnhds : Ω ∈ nhds τ := hΩopen.mem_nhds hτ.1
    have hPinhds : H ⁻¹' Piᶜ ∈ nhds τ :=
      (hH τ hτ.1).continuousAt.preimage_mem_nhds
        (hclosedPi.isOpen_compl.mem_nhds hτ.2)
    exact inter_mem hΩnhds hPinhds
  convert hopen_compl using 1
  ext τ
  by_cases hτΩ : τ ∈ Ω
  · by_cases hτPi : H τ ∈ Pi <;> simp [hτΩ, hτPi]
  · simp [hτΩ]

/-- Domain-level selected/sibling collisions are closed-discrete in `Ω` once the
selected branch has a closed-discrete odd-pi preimage. -/
theorem closedDiscrete_siblingCollisionInDomain_of_selected
    {Ω : Set ℂ} {K : Nat} {H : Fin (K + 1) -> ℂ -> ℂ} (c : Fin K)
    (hΩopen : IsOpen Ω)
    (hselected : ClosedDiscreteIn (Ω ∩ (H 0) ⁻¹' Pi) Ω)
    (hsibling : AnalyticOnNhd ℂ (H c.succ) Ω) :
    ClosedDiscreteIn (siblingCollisionInDomain Ω H c) Ω where
  subset := by
    intro τ hτ
    exact hτ.1
  isClosed_rel := by
    have hselected_closed : IsClosed (Ωᶜ ∪ (Ω ∩ (H 0) ⁻¹' Pi)) :=
      hselected.isClosed_rel
    have hsibling_closed : IsClosed (Ωᶜ ∪ (Ω ∩ (H c.succ) ⁻¹' Pi)) :=
      isClosed_rel_levelPreimageInDomain hΩopen hsibling
    have hclosed_inter :
        IsClosed ((Ωᶜ ∪ (Ω ∩ (H 0) ⁻¹' Pi)) ∩
          (Ωᶜ ∪ (Ω ∩ (H c.succ) ⁻¹' Pi))) :=
      hselected_closed.inter hsibling_closed
    have hEq :
        Ωᶜ ∪ siblingCollisionInDomain Ω H c =
          (Ωᶜ ∪ (Ω ∩ (H 0) ⁻¹' Pi)) ∩
            (Ωᶜ ∪ (Ω ∩ (H c.succ) ⁻¹' Pi)) := by
      ext τ
      by_cases hτΩ : τ ∈ Ω
      · simp [siblingCollisionInDomain, siblingCollisionSet, hτΩ]
      · simp [siblingCollisionInDomain, siblingCollisionSet, hτΩ]
    simpa [hEq] using hclosed_inter
  noAccum := by
    intro τ hτΩ hacc
    exact hselected.noAccum τ hτΩ
      (acc_mono (by
        intro z hz
        exact ⟨hz.1, hz.2.1⟩) hacc)

/-- Domain-level selected/sibling collisions are closed-discrete when the
selected level is nonconstant and holomorphic on the plane domain. -/
theorem closedDiscrete_siblingCollisionInDomain {Ω : Set ℂ} {K : Nat}
    {H : Fin (K + 1) -> ℂ -> ℂ} (c : Fin K)
    (hΩ : PlaneDomain Ω)
    (hselected : AnalyticOnNhd ℂ (H 0) Ω)
    (hselected_nonconst :
      ∀ z : ℂ, ¬ Set.EqOn (H 0) (fun _ : ℂ => z) Ω)
    (hsibling : AnalyticOnNhd ℂ (H c.succ) Ω) :
    ClosedDiscreteIn (siblingCollisionInDomain Ω H c) Ω :=
  closedDiscrete_siblingCollisionInDomain_of_selected c
    hΩ.isOpen
    (closedDiscrete_levelPreimageInDomain hΩ hselected hselected_nonconst)
    hsibling

/-- The sibling-avoidance hypothesis package gives domain-level
closed-discreteness of selected/sibling collisions once the selected level is
known to be nonconstant on the domain.  This does not rule out accumulation at
the puncture `ξ`. -/
theorem closedDiscrete_siblingCollisionInDomain_of_hypotheses
    {Ω : Set ℂ} {ξ : ℂ} {ρ0 : ℝ} {K : Nat}
    {H : Fin (K + 1) -> ℂ -> ℂ}
    (hhyp : SiblingAvoidanceHypotheses Ω ξ ρ0 H)
    (hselected_nonconst :
      ∀ z : ℂ, ¬ Set.EqOn (H 0) (fun _ : ℂ => z) Ω)
    (c : Fin K) :
    ClosedDiscreteIn (siblingCollisionInDomain Ω H c) Ω :=
  closedDiscrete_siblingCollisionInDomain c hhyp.omega_domain
    (hhyp.analytic_on_omega 0) hselected_nonconst
    (hhyp.analytic_on_omega c.succ)

/-- A closed-discrete subset of the plane has finite intersection with every
compact set. -/
theorem finite_inter_compact_of_closedDiscreteIn_univ {A K : Set ℂ}
    (hA : ClosedDiscreteIn A Set.univ) (hK : IsCompact K) :
    (A ∩ K).Finite := by
  have hclosed : IsClosed A := by
    simpa using hA.isClosed_rel
  have hdisc : IsDiscrete A := by
    rw [isDiscrete_iff_discreteTopology]
    exact discreteTopology_of_noAccPts fun z hzA => by
      simpa [acc, mem_derivedSet] using hA.noAccum z (by simp)
  have htend : Tendsto ((↑) : A -> ℂ) cofinite (cocompact ℂ) :=
    hclosed.tendsto_coe_cofinite_of_isDiscrete hdisc
  have hpre : (((↑) : A -> ℂ) ⁻¹' K).Finite :=
    (tendsto_cofinite_cocompact_iff.mp htend) K hK
  have himage :
      (((↑) : A -> ℂ) '' (((↑) : A -> ℂ) ⁻¹' K)).Finite :=
    hpre.image ((↑) : A -> ℂ)
  have heq : ((↑) : A -> ℂ) '' (((↑) : A -> ℂ) ⁻¹' K) = A ∩ K := by
    ext z
    constructor
    · rintro ⟨x, hxK, rfl⟩
      exact ⟨x.2, hxK⟩
    · rintro ⟨hzA, hzK⟩
      exact ⟨⟨z, hzA⟩, hzK, rfl⟩
  simpa [heq] using himage

/-- A closed-discrete subset of the plane has finite intersection with every
punctured disc. -/
theorem finite_inter_puncturedDisc_of_closedDiscreteIn_univ {A : Set ℂ}
    (hA : ClosedDiscreteIn A Set.univ) (ξ : ℂ) (ρ : ℝ) :
    (A ∩ puncturedDisc ξ ρ).Finite := by
  have hcompact : IsCompact (Metric.closedBall ξ ρ) :=
    isCompact_closedBall ξ ρ
  have hfinite : (A ∩ Metric.closedBall ξ ρ).Finite :=
    finite_inter_compact_of_closedDiscreteIn_univ hA hcompact
  exact hfinite.subset (by
    intro τ hτ
    exact ⟨hτ.1, by
      exact Metric.mem_closedBall.2 (le_of_lt hτ.2.2)⟩)

/-- Closed-discreteness of each ambient selected/sibling collision set implies
the finite-collision input used by `lem_sibling_avoidance`. -/
theorem finite_siblingCollisions_of_closedDiscrete_collisionSet {ξ : ℂ} {K : Nat}
    {H : Fin (K + 1) -> ℂ -> ℂ}
    (hclosedDiscrete :
      ∀ c : Fin K, ClosedDiscreteIn (siblingCollisionSet H c) Set.univ) :
    ∀ ρ : ℝ, 0 < ρ -> ∀ c : Fin K, (siblingCollisionIn ξ H ρ c).Finite := by
  intro ρ _hρ c
  have hfinite :
      (siblingCollisionSet H c ∩ puncturedDisc ξ ρ).Finite :=
    finite_inter_puncturedDisc_of_closedDiscreteIn_univ (hclosedDiscrete c) ξ ρ
  exact hfinite.subset (by
    intro τ hτ
    exact ⟨⟨hτ.2.1, hτ.2.2⟩, hτ.1⟩)

/-- Finite sibling-collision sets can be removed from the infinite selected
preimage set without losing infinitude. -/
theorem siblingAvoidanceConclusion_of_finite_collisions {ξ : ℂ} {K : Nat}
    {H : Fin (K + 1) -> ℂ -> ℂ}
    (hlevel : LevelPreimageResult (H 0) ξ)
    (hcollisions :
      ∀ ρ : ℝ, 0 < ρ -> ∀ c : Fin K, (siblingCollisionIn ξ H ρ c).Finite) :
    SiblingAvoidanceConclusion ξ H := by
  intro ρ hρ
  let selected : Set ℂ := levelPreimageIn (H 0) ξ ρ
  let collisions : Fin K -> Set ℂ := fun c => siblingCollisionIn ξ H ρ c
  have hselected : selected.Infinite :=
    hlevel.arbitrarily_close_pi_preimages ρ hρ
  have hcollisionFinite : (⋃ c : Fin K, collisions c).Finite :=
    Set.finite_iUnion fun c => hcollisions ρ hρ c
  have hdiff : (selected \ ⋃ c : Fin K, collisions c).Infinite :=
    hselected.diff hcollisionFinite
  refine hdiff.mono ?_
  intro τ hτ
  refine ⟨hτ.1.1, hτ.1.2, ?_⟩
  intro c hcPi
  exact hτ.2 (Set.mem_iUnion.2 ⟨c, hτ.1.1, hτ.1.2, hcPi⟩)

/-- Selected arc-structure plus finite sibling collisions gives the sibling
avoidance conclusion directly. -/
theorem siblingAvoidanceConclusion_of_arcStructure_finite_collisions {ξ : ℂ}
    {K m : Nat} {H : Fin (K + 1) -> ℂ -> ℂ}
    (harc : ArcStructureResult (H 0) ξ m)
    (hcollisions :
      ∀ ρ : ℝ, 0 < ρ -> ∀ c : Fin K, (siblingCollisionIn ξ H ρ c).Finite) :
    SiblingAvoidanceConclusion ξ H :=
  siblingAvoidanceConclusion_of_finite_collisions
    (levelPreimageResult_of_arcStructure harc) hcollisions

/-- Selected arc-structure plus closed-discrete ambient sibling-collision sets
gives the sibling avoidance conclusion. -/
theorem siblingAvoidanceConclusion_of_arcStructure_closedDiscrete_collisions {ξ : ℂ}
    {K m : Nat} {H : Fin (K + 1) -> ℂ -> ℂ}
    (harc : ArcStructureResult (H 0) ξ m)
    (hclosedDiscrete :
      ∀ c : Fin K, ClosedDiscreteIn (siblingCollisionSet H c) Set.univ) :
    SiblingAvoidanceConclusion ξ H :=
  siblingAvoidanceConclusion_of_arcStructure_finite_collisions harc
    (finite_siblingCollisions_of_closedDiscrete_collisionSet hclosedDiscrete)

/-- Output of the sequence-window avoidance argument along one selected arc.
It records the selected odd-pi sequence, its convergence and injectivity, and
the infinitely many indices where every sibling avoids `Π`. -/
structure SelectedSequenceWindowAvoidance (ξ : ℂ) {K : Nat}
    (H : Fin (K + 1) -> ℂ -> ℂ) : Prop where
  exists_sequence :
    ∃ sigma : ℕ -> ℂ,
      Tendsto sigma atTop (nhds ξ) ∧
      (∀ n : ℕ, sigma n ≠ ξ) ∧
      Function.Injective sigma ∧
      (∀ n : ℕ, H 0 (sigma n) ∈ Pi) ∧
      {n : ℕ | ∀ c : Fin K, H c.succ (sigma n) ∉ Pi}.Infinite

/-- A selected sequence with infinitely many good window indices gives good
points in every punctured disc. -/
theorem siblingAvoidanceConclusion_of_sequenceWindowAvoidance {ξ : ℂ} {K : Nat}
    {H : Fin (K + 1) -> ℂ -> ℂ}
    (hseq : SelectedSequenceWindowAvoidance ξ H) :
    SiblingAvoidanceConclusion ξ H := by
  rcases hseq.exists_sequence with
    ⟨sigma, hsigma_tendsto, hsigma_ne, hsigma_inj, hselected_pi, hgood_infinite⟩
  intro ρ hρ
  have heventually_ball :
      ∀ᶠ n in atTop, sigma n ∈ Metric.ball ξ ρ :=
    hsigma_tendsto (Metric.ball_mem_nhds ξ hρ)
  rcases Filter.eventually_atTop.1 heventually_ball with ⟨N, hN⟩
  let good : Set ℕ := {n : ℕ | ∀ c : Fin K, H c.succ (sigma n) ∉ Pi}
  have hfinite_initial : (Set.Iio N : Set ℕ).Finite :=
    Set.Finite.ofFinset (Finset.range N) (by intro n; simp)
  have hgood_tail : (good \ Set.Iio N).Infinite := by
    simpa [good] using hgood_infinite.diff hfinite_initial
  refine Set.infinite_of_injOn_mapsTo
    (s := good \ Set.Iio N)
    (t := {τ | τ ∈ puncturedDisc ξ ρ ∧ H 0 τ ∈ Pi ∧
      ∀ c : Fin K, H c.succ τ ∉ Pi})
    (f := sigma) ?_ ?_ hgood_tail
  · intro n _hn n' _hn' hnn'
    exact hsigma_inj hnn'
  · intro n hn
    have hgood : n ∈ good := hn.1
    have hNle : N ≤ n := not_lt.mp hn.2
    have hball : sigma n ∈ Metric.ball ξ ρ := hN n hNle
    exact ⟨⟨hsigma_ne n, by
        simpa [Metric.mem_ball] using hball⟩,
      hselected_pi n, hgood⟩

/-- Finite sibling collisions along all punctured discs imply the
sequence-window package, using the explicit selected arc sequence.  This keeps
the old finite-collision bridge available, although the main TeX route uses the
window package directly. -/
theorem selectedSequenceWindowAvoidance_of_arcStructure_finite_collisions {ξ : ℂ}
    {K m : Nat} {H : Fin (K + 1) -> ℂ -> ℂ}
    (harc : ArcStructureResult (H 0) ξ m)
    (hcollisions :
      ∀ ρ : ℝ, 0 < ρ -> ∀ c : Fin K, (siblingCollisionIn ξ H ρ c).Finite) :
    SelectedSequenceWindowAvoidance ξ H := by
  rcases harc.arc_data with ⟨radius, hradius_pos, arcs, _hcover, hseq⟩
  have hm_pos : 0 < 2 * m := by
    exact Nat.mul_pos (by norm_num) (lt_of_lt_of_le Nat.zero_lt_one harc.pole_order_pos)
  let q0 : Fin (2 * m) := ⟨0, hm_pos⟩
  rcases hseq q0 with ⟨seq, _hseq⟩
  let sigma : ℕ -> ℂ := fun n => (arcs q0).gamma (seq.rho n)
  have hbad_finite :
      (⋃ c : Fin K, {n : ℕ | H c.succ (sigma n) ∈ Pi}).Finite := by
    refine Set.finite_iUnion ?_
    intro c
    let badc : Set ℕ := {n : ℕ | H c.succ (sigma n) ∈ Pi}
    have himage_finite : (sigma '' badc).Finite :=
      (hcollisions radius hradius_pos c).subset (by
        intro τ hτ
        rcases hτ with ⟨n, hn, rfl⟩
        exact ⟨seq.point_mem_radius n, seq.point_mem_pi n, hn⟩)
    exact Set.Finite.of_finite_image himage_finite (by
      intro n _hn n' _hn' hnn'
      exact seq.point_injective hnn')
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact sigma
  · exact (arcs q0).tends_to_center.comp seq.rho_tendsto_zero
  · intro n
    exact (seq.point_mem_radius n).1
  · exact seq.point_injective
  · exact seq.point_mem_pi
  · have hgood :
        ((⋃ c : Fin K, {n : ℕ | H c.succ (sigma n) ∈ Pi})ᶜ).Infinite :=
      hbad_finite.infinite_compl
    refine hgood.mono ?_
    intro n hn c hcPi
    exact hn (Set.mem_iUnion.2 ⟨c, hcPi⟩)

/-- Selected arc-structure plus the sequence-window output gives the sibling
avoidance conclusion directly. -/
theorem siblingAvoidanceConclusion_of_arcStructure_sequenceWindow {ξ : ℂ}
    {K m : Nat} {H : Fin (K + 1) -> ℂ -> ℂ}
    (_harc : ArcStructureResult (H 0) ξ m)
    (hwindow : SelectedSequenceWindowAvoidance ξ H) :
    SiblingAvoidanceConclusion ξ H :=
  siblingAvoidanceConclusion_of_sequenceWindowAvoidance hwindow

/-- Result interface for **K04E lem-sibling-avoidance**. -/
structure SiblingAvoidanceResult (Ω : Set ℂ) (ξ : ℂ) (ρ0 : ℝ)
    {K : Nat} (H : Fin (K + 1) -> ℂ -> ℂ) : Prop where
  hypotheses : SiblingAvoidanceHypotheses Ω ξ ρ0 H
  selected_arc_structure : ∃ m : Nat, ArcStructureResult (H 0) ξ m
  sequence_window : SelectedSequenceWindowAvoidance ξ H

/-- Constructor for the sibling-avoidance result interface from selected
arc-structure and the sequence-window output. -/
theorem siblingAvoidanceResult_of_arcStructure_sequenceWindow {Ω : Set ℂ}
    {ξ : ℂ} {ρ0 : ℝ} {K m : Nat} {H : Fin (K + 1) -> ℂ -> ℂ}
    (hhyp : SiblingAvoidanceHypotheses Ω ξ ρ0 H)
    (harc : ArcStructureResult (H 0) ξ m)
    (hwindow : SelectedSequenceWindowAvoidance ξ H) :
    SiblingAvoidanceResult Ω ξ ρ0 H where
  hypotheses := hhyp
  selected_arc_structure := ⟨m, harc⟩
  sequence_window := hwindow

/-- Constructor for the sibling-avoidance result interface from selected
arc-structure and finite sibling collisions. -/
theorem siblingAvoidanceResult_of_arcStructure_finite_collisions {Ω : Set ℂ}
    {ξ : ℂ} {ρ0 : ℝ} {K m : Nat} {H : Fin (K + 1) -> ℂ -> ℂ}
    (hhyp : SiblingAvoidanceHypotheses Ω ξ ρ0 H)
    (harc : ArcStructureResult (H 0) ξ m)
    (hcollisions :
      ∀ ρ : ℝ, 0 < ρ -> ∀ c : Fin K, (siblingCollisionIn ξ H ρ c).Finite) :
    SiblingAvoidanceResult Ω ξ ρ0 H :=
  siblingAvoidanceResult_of_arcStructure_sequenceWindow hhyp harc
    (selectedSequenceWindowAvoidance_of_arcStructure_finite_collisions harc hcollisions)

/-- Constructor for the sibling-avoidance result interface from selected
arc-structure and closed-discrete ambient sibling-collision sets. -/
theorem siblingAvoidanceResult_of_arcStructure_closedDiscrete_collisions
    {Ω : Set ℂ} {ξ : ℂ} {ρ0 : ℝ} {K m : Nat}
    {H : Fin (K + 1) -> ℂ -> ℂ}
    (hhyp : SiblingAvoidanceHypotheses Ω ξ ρ0 H)
    (harc : ArcStructureResult (H 0) ξ m)
    (hclosedDiscrete :
      ∀ c : Fin K, ClosedDiscreteIn (siblingCollisionSet H c) Set.univ) :
    SiblingAvoidanceResult Ω ξ ρ0 H :=
  siblingAvoidanceResult_of_arcStructure_finite_collisions hhyp harc
    (finite_siblingCollisions_of_closedDiscrete_collisionSet hclosedDiscrete)

/-- **K04E.E.lem-sibling-avoidance.S/P**.

Sequence-window bridge for the sibling-avoidance interface. -/
theorem lem_sibling_avoidance {Ω : Set ℂ} {ξ : ℂ} {ρ0 : ℝ}
    {K : Nat} {H : Fin (K + 1) -> ℂ -> ℂ}
    (h : SiblingAvoidanceResult Ω ξ ρ0 H) :
    SiblingAvoidanceConclusion ξ H :=
  siblingAvoidanceConclusion_of_sequenceWindowAvoidance h.sequence_window


/-! ## Analytic-bracket arc pullback (prerequisite for `lem:window-avoidance`)

The sequence-window endgame of `lem:window-avoidance` (04e, Steps 7–11) must
*differentiate* the arc pullback: Step 7 bounds `|(F∘γ)'(ρ)| ≤ C₁·ρ^{-m}` and
Step 11 (case `ν ≥ 1`) applies Rolle to the real/imaginary parts of `ρ ↦ F(γ(ρ))`.
The proved `arc_pullback` exposes only `ContinuousOn` of its remainder `B`, which
does not suffice to differentiate `ρ ↦ G(A.arc ρ)`.

The theorem below records the pullback in the sharper form
`G (A.arc ρ) = ρ^{-μ} · Ψ (ρ·e^{iθ})` with `Ψ` **analytic at `0`** and
`Ψ 0 = c·e^{-iμθ}`, so that `ρ ↦ G(A.arc ρ)` is genuinely real-analytic on
`(0, ρ₁]`.  It is the honest analytic input for Steps 7–11 that the current
`SelectedArcData`/`PoleChart` interface does not otherwise provide.  It consumes
only the chart's `beta_analytic_ne` datum and the normal form's factorization,
mirroring the proved `arc_pullback` but keeping the bracket analytic. -/
theorem arc_pullback_analytic {H : ℂ -> ℂ} {ξ : ℂ} {m : Nat} {c0 : ℂ}
    (A : SelectedArcData H ξ m c0)
    {G : ℂ -> ℂ} {μ : ℤ} {c : ℂ} (hG : LaurentNormalFormAt G ξ μ c) :
    ∃ Ψ : ℂ -> ℂ, AnalyticAt ℂ Ψ 0 ∧
      Ψ 0 = c * Complex.exp (-(μ : ℂ) * (A.angle : ℂ) * Complex.I) ∧
      ∃ ρ1 : ℝ, 0 < ρ1 ∧ ρ1 ≤ A.arcRadius ∧
        ∀ ρ : ℝ, 0 < ρ -> ρ ≤ ρ1 ->
          G (A.arc ρ)
            = (ρ : ℂ) ^ (-μ) *
              Ψ ((ρ : ℂ) * Complex.exp ((A.angle : ℂ) * Complex.I)) := by
  classical
  obtain ⟨β, hβ_an, hβ0, hβ_ne, hβ_form⟩ := A.chart.beta_analytic_ne
  obtain ⟨g, hg_an, hgξ, hg_eq⟩ := hG.factored
  set rr : ℝ := A.arcRadius with hrr
  set R : ℝ := A.chart.radius' with hRR
  have hrr_pos : 0 < rr := A.arcRadius_pos
  have hrr_lt : rr < R := A.arcRadius_lt
  have hR_pos : 0 < R := lt_trans hrr_pos hrr_lt
  set ε : ℂ := Complex.exp ((A.angle : ℂ) * Complex.I) with hε_def
  set E : ℂ := Complex.exp (-(μ : ℂ) * (A.angle : ℂ) * Complex.I) with hE_def
  have hε_ne : ε ≠ 0 := by rw [hε_def]; exact Complex.exp_ne_zero _
  have hε_norm : ‖ε‖ = 1 := by
    rw [hε_def, Complex.norm_exp]
    have hre : ((A.angle : ℂ) * Complex.I).re = 0 := by
      rw [Complex.mul_I_re]; simp
    rw [hre, Real.exp_zero]
  have hε_pow : ε ^ (-μ) = E := by
    rw [hε_def, hE_def, ← Complex.exp_int_mul]
    congr 1
    push_cast; ring
  have hmem_ball : ∀ t : ℝ, 0 ≤ t → t < R → (t : ℂ) * ε ∈ Metric.ball (0:ℂ) R := by
    intro t ht0 htR
    rw [Metric.mem_ball, dist_zero_right, norm_mul, hε_norm, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    exact htR
  have hβ0an : AnalyticAt ℂ β 0 := hβ_an 0 (Metric.mem_ball_self hR_pos)
  -- Analyticity data for the bracket `Ψ`.
  have hf1 : AnalyticAt ℂ (fun w : ℂ => ξ + w * β w) 0 :=
    analyticAt_const.add (analyticAt_id.mul hβ0an)
  have hf1val : (fun w : ℂ => ξ + w * β w) 0 = ξ := by simp
  have hbase : AnalyticAt ℂ (fun w : ℂ => ε * β w) 0 := analyticAt_const.mul hβ0an
  have hbase0 : (fun w : ℂ => ε * β w) 0 ≠ 0 := by
    show ε * β 0 ≠ 0
    rw [hβ0, mul_one]; exact hε_ne
  refine ⟨fun w => g (ξ + w * β w) * (ε * β w) ^ (-μ), ?_, ?_, ?_⟩
  · -- `Ψ` is analytic at `0`.
    exact (hg_an.comp_of_eq' hf1 hf1val).mul (hbase.zpow hbase0)
  · -- Value `Ψ 0 = c · e^{-iμθ}`.
    show g (ξ + (0 : ℂ) * β 0) * (ε * β 0) ^ (-μ) = c * E
    rw [zero_mul, add_zero, hgξ, hβ0, mul_one, hε_pow]
  · -- The pullback identity.  Re-derive the arc-minus-centre form and the
    -- eventual Laurent identity, exactly as in `arc_pullback`.
    have harc_sub : ∀ ρ : ℝ, 0 < ρ → ρ ≤ rr →
        A.arc ρ - ξ = (ρ : ℂ) * ε * β ((ρ : ℂ) * ε) := by
      intro ρ hρ hρle
      have hball : (ρ : ℂ) * ε ∈ Metric.ball (0:ℂ) R :=
        hmem_ball ρ hρ.le (lt_of_le_of_lt hρle hrr_lt)
      have hne : (ρ : ℂ) * ε ≠ 0 := mul_ne_zero (by exact_mod_cast hρ.ne') hε_ne
      have hform := hβ_form ((ρ:ℂ)*ε) hball hne
      have harc := A.arc_eq ρ hρ hρle
      rw [← hε_def] at harc
      rw [harc, hform]; ring
    have harc_ne : ∀ ρ : ℝ, 0 < ρ → ρ ≤ rr → A.arc ρ ≠ ξ := by
      intro ρ hρ hρle hEq
      have hsub := harc_sub ρ hρ hρle
      rw [hEq, sub_self] at hsub
      have hne : (ρ : ℂ) * ε * β ((ρ:ℂ)*ε) ≠ 0 :=
        mul_ne_zero (mul_ne_zero (by exact_mod_cast hρ.ne') hε_ne)
          (hβ_ne ((ρ:ℂ)*ε) (hmem_ball ρ hρ.le (lt_of_le_of_lt hρle hrr_lt)))
      exact hne hsub.symm
    set α : ℝ → ℂ := fun t => ξ + (t : ℂ) * ε * β ((t : ℂ) * ε) with hα_def
    have hα0 : α 0 = ξ := by rw [hα_def]; simp
    have hα_arc : ∀ ρ : ℝ, 0 < ρ → ρ ≤ rr → α ρ = A.arc ρ := by
      intro ρ hρ hρle
      rw [hα_def]
      simp only []
      rw [← harc_sub ρ hρ hρle]; ring
    have hα_contAt : ContinuousAt α 0 := by
      rw [hα_def]
      have hin : ContinuousAt (fun t : ℝ => (t:ℂ)*ε) 0 :=
        (Complex.continuous_ofReal.continuousAt).mul continuousAt_const
      have hβ_ca : ContinuousAt β (0 : ℂ) :=
        (hβ_an.continuousOn).continuousAt (Metric.ball_mem_nhds (0:ℂ) hR_pos)
      have hcomp : ContinuousAt (fun t : ℝ => β ((t:ℂ)*ε)) 0 :=
        ContinuousAt.comp_of_eq (g := β) (f := fun t : ℝ => (t:ℂ)*ε) hβ_ca hin (by simp)
      exact continuousAt_const.add (hin.mul hcomp)
    have hα_tend : Tendsto α (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds ξ) := by
      have h : Tendsto α (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (α 0)) :=
        hα_contAt.continuousWithinAt
      rw [hα0] at h; exact h
    have hlt : ∀ᶠ ρ in nhdsWithin (0:ℝ) (Set.Ioi 0), ρ < rr :=
      (Filter.eventually_of_mem (Iio_mem_nhds hrr_pos) fun _ hx => hx).filter_mono
        nhdsWithin_le_nhds
    have harc_tendsto : Tendsto A.arc (nhdsWithin (0:ℝ) (Set.Ioi 0))
        (nhdsWithin ξ ({ξ}ᶜ : Set ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨hα_tend.congr' ?_, ?_⟩
      · filter_upwards [self_mem_nhdsWithin, hlt] with ρ hρpos hρlt
        exact hα_arc ρ hρpos (le_of_lt hρlt)
      · filter_upwards [self_mem_nhdsWithin, hlt] with ρ hρpos hρlt
        exact harc_ne ρ hρpos (le_of_lt hρlt)
    have hLaurev : ∀ᶠ ρ in nhdsWithin (0:ℝ) (Set.Ioi 0),
        G (A.arc ρ) = g (A.arc ρ) * (A.arc ρ - ξ) ^ (-μ) :=
      harc_tendsto.eventually hg_eq
    have hev : ∀ᶠ ρ in nhdsWithin (0:ℝ) (Set.Ioi 0),
        ρ < rr ∧ G (A.arc ρ) = g (A.arc ρ) * (A.arc ρ - ξ) ^ (-μ) :=
      hlt.and hLaurev
    obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.mem_nhdsWithin_iff.mp hev
    refine ⟨min (δ/2) rr, lt_min (by linarith) hrr_pos, min_le_right _ _, ?_⟩
    intro ρ hρ hρρ1
    have hρrr : ρ ≤ rr := le_trans hρρ1 (min_le_right _ _)
    have hρδ : ρ < δ := lt_of_le_of_lt (le_trans hρρ1 (min_le_left _ _)) (by linarith)
    have hmemρ : ρ ∈ Metric.ball (0:ℝ) δ ∩ Set.Ioi 0 := by
      refine ⟨?_, hρ⟩
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hρ]
      exact hρδ
    have hGeq : G (A.arc ρ) = g (A.arc ρ) * (A.arc ρ - ξ) ^ (-μ) := (hδ_sub hmemρ).2
    have hsub := harc_sub ρ hρ hρrr
    have harcval : A.arc ρ = ξ + (ρ:ℂ) * ε * β ((ρ:ℂ)*ε) := by
      linear_combination hsub
    show G (A.arc ρ)
        = (ρ : ℂ) ^ (-μ) *
          (g (ξ + ((ρ : ℂ) * ε) * β ((ρ : ℂ) * ε)) * (ε * β ((ρ : ℂ) * ε)) ^ (-μ))
    rw [hGeq, hsub, harcval]
    simp only [mul_zpow]
    ring


/-! ## Sequence-window endgame helper lemmas (`lem:window-avoidance` Steps 1–11)

The theorems below are the standalone, individually-verifiable analytic and
combinatorial pieces of the sequence-window contradiction.  They are additive and
consume no unproven interface. -/

/-- Explicit membership form of the odd-`π` pole set `Π = (2ℤ+1)π i`. -/
theorem mem_Pi_iff_odd {z : ℂ} :
    z ∈ Pi ↔ ∃ k : ℤ, z = (2 * (k : ℂ) + 1) * (Real.pi : ℂ) * Complex.I := by
  rw [Pi, sigmoidPoleSet_eq_oddPiI]; exact Iff.rfl

/-- The difference of two `Π` points is an even integer multiple of `π i`. -/
theorem Pi_sub_mem_two_pi {z w : ℂ} (hz : z ∈ Pi) (hw : w ∈ Pi) :
    ∃ k : ℤ, z - w = 2 * (k : ℂ) * (Real.pi : ℂ) * Complex.I := by
  obtain ⟨a, ha⟩ := mem_Pi_iff_odd.mp hz
  obtain ⟨b, hb⟩ := mem_Pi_iff_odd.mp hw
  exact ⟨a - b, by rw [ha, hb]; push_cast; ring⟩

/-- **Uniform discreteness ⇒ eventual constancy** (Step 10/11 lattice tool).
A sequence lying in a set whose distinct points are `≥ δ > 0` apart and which
converges is eventually equal to its limit.  Applies to `Π` via
`Pi_dist_ge_two_pi` and to any shifted lattice `Λ`. -/
theorem eventuallyEq_limit_of_pairwise_dist_ge
    {S : Set ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ dist x y)
    {f : ℕ → ℂ} (hfS : ∀ n, f n ∈ S) {L : ℂ}
    (hf : Tendsto f atTop (nhds L)) :
    ∀ᶠ n in atTop, f n = L := by
  have hcauchy : CauchySeq f := hf.cauchySeq
  rw [Metric.cauchySeq_iff] at hcauchy
  obtain ⟨N, hN⟩ := hcauchy δ hδ
  have hconst : ∀ n, N ≤ n → f n = f N := by
    intro n hn
    by_contra hne
    exact absurd (hN n hn N (le_refl N)) (not_lt.mpr (hsep (f n) (hfS n) (f N) (hfS N) hne))
  have hFL : f N = L := by
    have heq : f =ᶠ[atTop] fun _ : ℕ => f N := by
      filter_upwards [Filter.eventually_ge_atTop N] with n hn using hconst n hn
    exact (tendsto_nhds_unique (Tendsto.congr' heq hf) tendsto_const_nhds).symm
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  rw [hconst n hn, hFL]

/-- **Convergent integer sequence is eventually constant** (Step 10).
Specialization of the discreteness principle to `ℤ ↪ ℂ` via `2·k·π·i`
(the `(π i / g)`-lattice generator with `g = 1` scaling absorbed by the caller). -/
theorem eventuallyEq_of_tendsto_intMul
    {a : ℝ} (ha : 0 < a) {u : ℕ → ℤ} {L : ℂ}
    (hu : Tendsto (fun n => (u n : ℂ) * (a : ℂ) * Complex.I) atTop (nhds L)) :
    ∀ᶠ n in atTop, (u n : ℂ) * (a : ℂ) * Complex.I = L := by
  refine eventuallyEq_limit_of_pairwise_dist_ge (S := Set.range (fun k : ℤ => (k : ℂ) * (a : ℂ) * Complex.I))
    (δ := a) ha ?_ (fun n => ⟨u n, rfl⟩) hu
  rintro x ⟨p, rfl⟩ y ⟨q, rfl⟩ hxy
  have hpq : p ≠ q := by
    rintro rfl; exact hxy rfl
  have hdiff : ((p : ℂ) * (a : ℂ) * Complex.I) - ((q : ℂ) * (a : ℂ) * Complex.I)
      = (((p - q : ℤ) : ℝ) : ℂ) * (a : ℂ) * Complex.I := by push_cast; ring
  rw [Complex.dist_eq, hdiff, Complex.norm_mul, Complex.norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ha]
  have h1 : (1 : ℝ) ≤ |((p - q : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hpq)
  nlinarith [abs_nonneg ((p - q : ℤ) : ℝ), ha.le]

/-- **Pigeonhole/window reduction (Steps 1–3).**  If a selected sequence `σ` has
only finitely many indices at which *every* sibling avoids `Π`, then some fixed
sibling `c` collides with `Π` at *both* endpoints of a fixed bounded gap `g` for
infinitely many indices.  This is the forward extraction that the analytic core
(Steps 4–11) then refutes; it is not a restatement of the target. -/
theorem exists_recurring_sibling_collision {K : ℕ} (hK : 0 < K)
    {H : Fin (K + 1) → ℂ → ℂ} {σ : ℕ → ℂ}
    (hfin : ¬ {n : ℕ | ∀ c : Fin K, H c.succ (σ n) ∉ Pi}.Infinite) :
    ∃ (c : Fin K) (g : ℕ), 1 ≤ g ∧ g ≤ K ∧
      {n : ℕ | H c.succ (σ n) ∈ Pi ∧ H c.succ (σ (n + g)) ∈ Pi}.Infinite := by
  classical
  have hfinite : {n : ℕ | ∀ c : Fin K, H c.succ (σ n) ∉ Pi}.Finite :=
    Set.not_infinite.mp hfin
  obtain ⟨M, hM⟩ := hfinite.bddAbove
  have hcol_ex : ∀ n : ℕ, M < n → ∃ c : Fin K, H c.succ (σ n) ∈ Pi := by
    intro n hn
    by_contra hnone
    simp only [not_exists] at hnone
    exact absurd (hM hnone) (not_le.mpr hn)
  set N := M + 1 with hNdef
  have key : ∃ color : ℕ → Fin K, ∀ n, N ≤ n → H (color n).succ (σ n) ∈ Pi := by
    refine ⟨fun n => if h : ∃ c : Fin K, H c.succ (σ n) ∈ Pi then h.choose
      else ⟨0, hK⟩, ?_⟩
    intro n hn
    have hex : ∃ c : Fin K, H c.succ (σ n) ∈ Pi := hcol_ex n (by omega)
    simp only [dif_pos hex]
    exact hex.choose_spec
  obtain ⟨color, hcolor_spec⟩ := key
  obtain ⟨c, g, hg1, hgK, hinf⟩ :=
    infinite_sameColor_boundedGap_of_coloring (K := K) (N := N) hK color
  refine ⟨c, g, hg1, hgK, hinf.mono ?_⟩
  intro n hn
  obtain ⟨hnN, hcn, hcng⟩ := hn
  refine ⟨?_, ?_⟩
  · have hh := hcolor_spec n hnN
    rwa [hcn] at hh
  · have hh := hcolor_spec (n + g) (by omega)
    rwa [hcng] at hh

/-- **Real-analytic pullback regularity** (Step 7 core).  For `Ψ` differentiable
at `t·ε` and `t > 0`, the real function `s ↦ (s:ℂ)^n · Ψ(s·ε)` is differentiable
at `t` with the product-rule derivative.  This is the differentiability that the
plain `arc_pullback` (continuity only) does not provide; combined with
`arc_pullback_analytic` it makes `ρ ↦ G(A.arc ρ)` genuinely `C¹` on `(0,ρ₁]`.
Consumed with `n = -μ` (raw pullback) and `n = s₀ - m` (reduced difference `F`). -/
theorem hasDerivAt_ofRealZpow_mul_comp {Ψ : ℂ → ℂ} {ε : ℂ} (n : ℤ) {t : ℝ}
    (ht : 0 < t) (hΨ : DifferentiableAt ℂ Ψ ((t : ℂ) * ε)) :
    HasDerivAt (fun s : ℝ => (s : ℂ) ^ n * Ψ ((s : ℂ) * ε))
      ((n : ℂ) * (t : ℂ) ^ (n - 1) * Ψ ((t : ℂ) * ε)
        + (t : ℂ) ^ n * (ε * deriv Ψ ((t : ℂ) * ε))) t := by
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hofReal : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using
      Complex.ofRealCLM.hasDerivAt
  have hzpowC : HasDerivAt (fun z : ℂ => z ^ n) ((n : ℂ) * (t : ℂ) ^ (n - 1)) (t : ℂ) :=
    hasDerivAt_zpow n (t : ℂ) (Or.inl htc)
  have hpow : HasDerivAt (fun s : ℝ => (s : ℂ) ^ n) ((n : ℂ) * (t : ℂ) ^ (n - 1)) t := by
    simpa using HasDerivAt.scomp_of_eq (x := t) hzpowC hofReal rfl
  have hlin : HasDerivAt (fun s : ℝ => (s : ℂ) * ε) ε t := by
    simpa using hofReal.mul_const ε
  have hcomp : HasDerivAt (fun s : ℝ => Ψ ((s : ℂ) * ε)) (ε * deriv Ψ ((t : ℂ) * ε)) t := by
    simpa [smul_eq_mul] using HasDerivAt.scomp_of_eq (x := t) (hΨ.hasDerivAt) hlin rfl
  exact hpow.mul hcomp

/-- **FTC/MVT increment bound** (Step 9).  A complex-valued function differentiable
on `[a,b]` with derivative bounded by `C` is `C`-Lipschitz there.  This replaces the
(complex-invalid) mean value theorem by the segment estimate. -/
theorem norm_sub_le_of_hasDerivAt_bound_Icc {f f' : ℝ → ℂ} {a b C : ℝ}
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x)
    (hbound : ∀ x ∈ Set.Icc a b, ‖f' x‖ ≤ C) {x y : ℝ}
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) :
    ‖f y - f x‖ ≤ C * ‖y - x‖ :=
  Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z hz => (hf z hz).hasDerivWithinAt) hbound (convex_Icc a b) hx hy

/-- **Rolle on the real part** (Step 11, `ν ≥ 1` case).  If a complex-valued `C¹`
function on `[a,b]` has equal real parts at the endpoints, its derivative has
vanishing real part at some interior point.  (Applied to `Re` and `Im` of
`ρ ↦ F(γ ρ)`.) -/
theorem exists_mem_Ioo_re_deriv_eq_zero {f f' : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x)
    (hval : (f a).re = (f b).re) :
    ∃ c ∈ Set.Ioo a b, (f' c).re = 0 := by
  have hre : ∀ x ∈ Set.Icc a b, HasDerivAt (fun y => (f y).re) ((f' x).re) x := by
    intro x hx
    simpa [Complex.reCLM_apply, Function.comp] using
      (Complex.reCLM.hasFDerivAt).comp_hasDerivAt x (hf x hx)
  have hcont : ContinuousOn (fun y => (f y).re) (Set.Icc a b) :=
    fun x hx => (hre x hx).continuousAt.continuousWithinAt
  exact exists_hasDerivAt_eq_zero hab hcont hval
    (fun x hx => hre x (Set.Ioo_subset_Icc_self hx))

/-- **Vanishing real part of the leading coefficient** (Step 4).  If a Laurent
pullback `G(A.arc ρ) = ρ^{-μ}·Ψ(ρ·e^{iθ})` (with `Ψ` analytic at `0`) lands in `Π`
for infinitely many selected radii, then `Re (Ψ 0) = 0`; i.e. the pullback leading
coefficient `d = Ψ 0` is purely imaginary.  Order-independent (works for every `μ`),
so it applies to every sibling regardless of its exact order. -/
theorem re_bracket_zero_eq_zero_of_frequently_mem_Pi
    {H : ℂ → ℂ} {ξ : ℂ} {m : ℕ} {c0 : ℂ} (A : SelectedArcData H ξ m c0)
    {G Ψ : ℂ → ℂ} (hΨ : AnalyticAt ℂ Ψ 0) {μ : ℤ} {ρ1 : ℝ} (hρ1 : 0 < ρ1)
    (hpb : ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ1 →
        G (A.arc ρ) = (ρ : ℂ) ^ (-μ) *
          Ψ ((ρ : ℂ) * Complex.exp ((A.angle : ℂ) * Complex.I)))
    (hfreq : ∃ᶠ n in atTop, G (A.arc (A.rho n)) ∈ Pi) :
    (Ψ 0).re = 0 := by
  set ε : ℂ := Complex.exp ((A.angle : ℂ) * Complex.I) with hε
  have hrho0 : Tendsto (fun n => A.rho n) atTop (nhds 0) :=
    A.rho_tendsto_zero.mono_right nhdsWithin_le_nhds
  have hin : Tendsto (fun n => (A.rho n : ℂ) * ε) atTop (nhds 0) := by
    have h0 : Tendsto (fun n => (A.rho n : ℂ)) atTop (nhds 0) := by
      simpa using (Complex.continuous_ofReal.tendsto 0).comp hrho0
    simpa using h0.mul tendsto_const_nhds
  have htend_re : Tendsto (fun n => (Ψ ((A.rho n : ℂ) * ε)).re) atTop (nhds ((Ψ 0).re)) :=
    (Complex.continuous_re.tendsto _).comp ((hΨ.continuousAt.tendsto).comp hin)
  have hev_le : ∀ᶠ n in atTop, A.rho n ≤ ρ1 := by
    filter_upwards [hrho0 (Iio_mem_nhds hρ1)] with n hn using le_of_lt hn
  have hfreq0 : ∃ᶠ n in atTop, (Ψ ((A.rho n : ℂ) * ε)).re = 0 := by
    refine (hfreq.and_eventually hev_le).mono ?_
    rintro n ⟨hcol, hle⟩
    have hpos : 0 < A.rho n := A.rho_pos n
    have hval := hpb (A.rho n) hpos hle
    have hre0 : (G (A.arc (A.rho n))).re = 0 := Pi_re_eq_zero hcol
    rw [hval, ← Complex.ofReal_zpow, Complex.re_ofReal_mul] at hre0
    exact (mul_eq_zero.mp hre0).resolve_left (zpow_ne_zero _ (ne_of_gt hpos))
  have hmem : (Ψ 0).re ∈ ({0} : Set ℝ) :=
    isClosed_singleton.mem_of_frequently_of_tendsto
      (hfreq0.mono fun n hn => Set.mem_singleton_iff.mpr hn) htend_re
  simpa using hmem

/-- **Selected radius identity** (Step 8).  From `A.rho_formula`, the `m`-th power
of the selected radius is `‖c0‖/((2(N_⋆+n)+1)π)`; equivalently `ρ_{(n)}^{-m}` grows
linearly in `n`.  Real-`rpow` inversion of the `1/m` power. -/
theorem rho_pow_m {H : ℂ → ℂ} {ξ : ℂ} {m : ℕ} {c0 : ℂ}
    (A : SelectedArcData H ξ m c0) (hm : 1 ≤ m) (n : ℕ) :
    A.rho n ^ m = ‖c0‖ / (((2 * (A.Nstar + n) + 1 : ℕ) : ℝ) * Real.pi) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hm
  rw [A.rho_formula n]
  set x : ℝ := ‖c0‖ / (((2 * (A.Nstar + n) + 1 : ℕ) : ℝ) * Real.pi) with hx
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  rw [← Real.rpow_natCast (x ^ ((m : ℝ)⁻¹)) m, ← Real.rpow_mul hx0,
    inv_mul_cancel₀ hmR, Real.rpow_one]

/-- **Exact selected-sequence increment** (Step 10).  Along the selected arc
sequence, `H (σ_{n+g}) − H (σ_n) = 2πi·ε·g` exactly (`ε = A.sign`), from
`sigma_value_exact`.  Paired with `Pi_sub_mem_two_pi` (the sibling increment is an
even multiple of `πi`) this drives the `(πi/g)ℤ` lattice rigidity. -/
theorem selected_increment {H : ℂ → ℂ} {ξ : ℂ} {m : ℕ} {c0 : ℂ}
    (A : SelectedArcData H ξ m c0) (n g : ℕ) :
    H (A.arc (A.rho (n + g))) - H (A.arc (A.rho n))
      = (A.sign : ℂ) * (2 * (g : ℂ)) * (Real.pi : ℂ) * Complex.I := by
  rw [A.sigma_value_exact (n + g), A.sigma_value_exact n]
  push_cast
  ring

/-- **Continuous arc limit** (Step 5 prerequisite).  `A.arc ρ → ξ` as `ρ → 0⁺`
(the sequence-only `sigma_tendsto` upgraded to the full one-sided limit), via the
chart's zero-free `β`-form `A.arc ρ = ξ + ρe^{iθ}·β(ρe^{iθ})`. -/
theorem arc_tendsto_center {H : ℂ → ℂ} {ξ : ℂ} {m : ℕ} {c0 : ℂ}
    (A : SelectedArcData H ξ m c0) :
    Tendsto A.arc (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ξ) := by
  obtain ⟨β, hβ_an, hβ0, hβ_ne, hβ_form⟩ := A.chart.beta_analytic_ne
  set rr : ℝ := A.arcRadius with hrr
  set R : ℝ := A.chart.radius' with hRR
  have hrr_pos : 0 < rr := A.arcRadius_pos
  have hrr_lt : rr < R := A.arcRadius_lt
  have hR_pos : 0 < R := lt_trans hrr_pos hrr_lt
  set ε : ℂ := Complex.exp ((A.angle : ℂ) * Complex.I) with hε_def
  have hε_ne : ε ≠ 0 := by rw [hε_def]; exact Complex.exp_ne_zero _
  have hε_norm : ‖ε‖ = 1 := by
    rw [hε_def, Complex.norm_exp]
    have hre : ((A.angle : ℂ) * Complex.I).re = 0 := by rw [Complex.mul_I_re]; simp
    rw [hre, Real.exp_zero]
  have hmem_ball : ∀ t : ℝ, 0 ≤ t → t < R → (t : ℂ) * ε ∈ Metric.ball (0:ℂ) R := by
    intro t ht0 htR
    rw [Metric.mem_ball, dist_zero_right, norm_mul, hε_norm, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    exact htR
  have harc_sub : ∀ ρ : ℝ, 0 < ρ → ρ ≤ rr →
      A.arc ρ - ξ = (ρ : ℂ) * ε * β ((ρ : ℂ) * ε) := by
    intro ρ hρ hρle
    have hball : (ρ : ℂ) * ε ∈ Metric.ball (0:ℂ) R :=
      hmem_ball ρ hρ.le (lt_of_le_of_lt hρle hrr_lt)
    have hne : (ρ : ℂ) * ε ≠ 0 := mul_ne_zero (by exact_mod_cast hρ.ne') hε_ne
    have hform := hβ_form ((ρ:ℂ)*ε) hball hne
    have harc := A.arc_eq ρ hρ hρle
    rw [← hε_def] at harc
    rw [harc, hform]; ring
  set α : ℝ → ℂ := fun t => ξ + (t : ℂ) * ε * β ((t : ℂ) * ε) with hα_def
  have hα0 : α 0 = ξ := by rw [hα_def]; simp
  have hα_arc : ∀ ρ : ℝ, 0 < ρ → ρ ≤ rr → α ρ = A.arc ρ := by
    intro ρ hρ hρle
    rw [hα_def]; simp only []
    rw [← harc_sub ρ hρ hρle]; ring
  have hα_contAt : ContinuousAt α 0 := by
    rw [hα_def]
    have hin : ContinuousAt (fun t : ℝ => (t:ℂ)*ε) 0 :=
      (Complex.continuous_ofReal.continuousAt).mul continuousAt_const
    have hβ_ca : ContinuousAt β (0 : ℂ) :=
      (hβ_an.continuousOn).continuousAt (Metric.ball_mem_nhds (0:ℂ) hR_pos)
    have hcomp : ContinuousAt (fun t : ℝ => β ((t:ℂ)*ε)) 0 :=
      ContinuousAt.comp_of_eq (g := β) (f := fun t : ℝ => (t:ℂ)*ε) hβ_ca hin (by simp)
    exact continuousAt_const.add (hin.mul hcomp)
  have hlt : ∀ᶠ ρ in nhdsWithin (0:ℝ) (Set.Ioi 0), ρ < rr :=
    (Filter.eventually_of_mem (Iio_mem_nhds hrr_pos) fun _ hx => hx).filter_mono
      nhdsWithin_le_nhds
  have hα_tend : Tendsto α (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds ξ) := by
    have h : Tendsto α (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (α 0)) :=
      hα_contAt.continuousWithinAt
    rw [hα0] at h; exact h
  refine hα_tend.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hlt] with ρ hρpos hρlt
  exact hα_arc ρ hρpos (le_of_lt hρlt)

/-- **Arc avoids the center** (Step 5 prerequisite).  For `0 < ρ ≤ arcRadius`,
`A.arc ρ ≠ ξ`, since `A.arc ρ − ξ = ρe^{iθ}·β(ρe^{iθ})` is a product of nonzero
factors. -/
theorem arc_ne_center {H : ℂ → ℂ} {ξ : ℂ} {m : ℕ} {c0 : ℂ}
    (A : SelectedArcData H ξ m c0) {ρ : ℝ} (hρ : 0 < ρ) (hρle : ρ ≤ A.arcRadius) :
    A.arc ρ ≠ ξ := by
  obtain ⟨β, hβ_an, hβ0, hβ_ne, hβ_form⟩ := A.chart.beta_analytic_ne
  set R : ℝ := A.chart.radius' with hRR
  have hrr_lt : A.arcRadius < R := A.arcRadius_lt
  set ε : ℂ := Complex.exp ((A.angle : ℂ) * Complex.I) with hε_def
  have hε_ne : ε ≠ 0 := by rw [hε_def]; exact Complex.exp_ne_zero _
  have hε_norm : ‖ε‖ = 1 := by
    rw [hε_def, Complex.norm_exp]
    have hre : ((A.angle : ℂ) * Complex.I).re = 0 := by rw [Complex.mul_I_re]; simp
    rw [hre, Real.exp_zero]
  have hball : (ρ : ℂ) * ε ∈ Metric.ball (0:ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right, norm_mul, hε_norm, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ.le]
    exact lt_of_le_of_lt hρle hrr_lt
  have hne : (ρ : ℂ) * ε ≠ 0 := mul_ne_zero (by exact_mod_cast hρ.ne') hε_ne
  have hform := hβ_form ((ρ:ℂ)*ε) hball hne
  have harc := A.arc_eq ρ hρ hρle
  rw [← hε_def] at harc
  intro hEq
  rw [harc, hform] at hEq
  have hzero : (ρ:ℂ) * ε * β ((ρ:ℂ)*ε) = 0 := by linear_combination hEq
  exact (mul_ne_zero hne (hβ_ne ((ρ:ℂ)*ε) hball)) hzero

/-- **Arc lands in every punctured disc near `0`** (Step 5 non-degeneracy input).
For `ρ → 0⁺`, `A.arc ρ ∈ D^×(ξ,ρ0)`; combined with `hhyp.puncturedDisc_subset`
this places the arc inside `Ω`, so a function vanishing on the arc vanishes on `Ω`
by the identity theorem. -/
theorem arc_eventually_mem_puncturedDisc {H : ℂ → ℂ} {ξ : ℂ} {m : ℕ} {c0 : ℂ}
    (A : SelectedArcData H ξ m c0) {ρ0 : ℝ} (hρ0 : 0 < ρ0) :
    ∀ᶠ ρ in nhdsWithin (0 : ℝ) (Set.Ioi 0), A.arc ρ ∈ puncturedDisc ξ ρ0 := by
  have hball : ∀ᶠ ρ in nhdsWithin (0:ℝ) (Set.Ioi 0), A.arc ρ ∈ Metric.ball ξ ρ0 :=
    (arc_tendsto_center A) (Metric.ball_mem_nhds ξ hρ0)
  have hlt : ∀ᶠ ρ in nhdsWithin (0:ℝ) (Set.Ioi 0), ρ < A.arcRadius :=
    (Filter.eventually_of_mem (Iio_mem_nhds A.arcRadius_pos) fun _ hx => hx).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [hball, self_mem_nhdsWithin, hlt] with ρ hb hpos hlt'
  exact ⟨arc_ne_center A hpos (le_of_lt hlt'), by rw [Metric.mem_ball] at hb; exact hb⟩

/-- **Arc injectivity** (Step 5 non-degeneracy, L1).  `A.arc` is injective on
`(0, arcRadius]`: it is `ψinv` (a chart biholomorphism, hence injective on its
image ball) composed with the injective ray `ρ ↦ ρ·e^{iθ}`.  No derivative needed. -/
theorem arc_injOn {H : ℂ → ℂ} {ξ : ℂ} {m : ℕ} {c0 : ℂ} (A : SelectedArcData H ξ m c0)
    {ρ ρ' : ℝ} (hρ : 0 < ρ) (hρle : ρ ≤ A.arcRadius)
    (hρ' : 0 < ρ') (hρ'le : ρ' ≤ A.arcRadius) (heq : A.arc ρ = A.arc ρ') : ρ = ρ' := by
  set ε : ℂ := Complex.exp ((A.angle : ℂ) * Complex.I) with hε
  have hε_ne : ε ≠ 0 := by rw [hε]; exact Complex.exp_ne_zero _
  have hε_norm : ‖ε‖ = 1 := by
    rw [hε, Complex.norm_exp]
    have hre : ((A.angle : ℂ) * Complex.I).re = 0 := by rw [Complex.mul_I_re]; simp
    rw [hre, Real.exp_zero]
  have hmem : ∀ s : ℝ, 0 < s → s ≤ A.arcRadius →
      (s : ℂ) * ε ∈ Metric.ball (0:ℂ) A.chart.radius' := by
    intro s hs hsle
    rw [Metric.mem_ball, dist_zero_right, norm_mul, hε_norm, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.le]
    exact lt_of_le_of_lt hsle A.arcRadius_lt
  have h1 := A.arc_eq ρ hρ hρle
  have h2 := A.arc_eq ρ' hρ' hρ'le
  rw [← hε] at h1 h2
  rw [h1, h2] at heq
  have hb1 := (A.chart.biholo_right ((ρ:ℂ)*ε) (hmem ρ hρ hρle)).1
  have hb2 := (A.chart.biholo_right ((ρ':ℂ)*ε) (hmem ρ' hρ' hρ'le)).1
  have hρε : (ρ:ℂ) * ε = (ρ':ℂ) * ε := by rw [← hb1, ← hb2, heq]
  exact_mod_cast mul_right_cancel₀ hε_ne hρε

/-- **Arc continuity at interior radii** (Step 5 non-degeneracy, L1).  `A.arc` is
continuous at each `ρ₀ ∈ (0, arcRadius)` (it equals `ξ + ρe^{iθ}·β(ρe^{iθ})` near
`ρ₀`, with `β` analytic hence continuous). -/
theorem arc_continuousAt {H : ℂ → ℂ} {ξ : ℂ} {m : ℕ} {c0 : ℂ} (A : SelectedArcData H ξ m c0)
    {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₀' : ρ₀ < A.arcRadius) : ContinuousAt A.arc ρ₀ := by
  obtain ⟨β, hβ_an, hβ0, hβ_ne, hβ_form⟩ := A.chart.beta_analytic_ne
  set R : ℝ := A.chart.radius' with hRR
  have hrr_lt : A.arcRadius < R := A.arcRadius_lt
  have hR_pos : 0 < R := lt_trans A.arcRadius_pos hrr_lt
  set ε : ℂ := Complex.exp ((A.angle : ℂ) * Complex.I) with hε
  have hε_ne : ε ≠ 0 := by rw [hε]; exact Complex.exp_ne_zero _
  have hε_norm : ‖ε‖ = 1 := by
    rw [hε, Complex.norm_exp]
    have hre : ((A.angle : ℂ) * Complex.I).re = 0 := by rw [Complex.mul_I_re]; simp
    rw [hre, Real.exp_zero]
  have hmem : ∀ s : ℝ, 0 < s → s ≤ A.arcRadius → (s : ℂ) * ε ∈ Metric.ball (0:ℂ) R := by
    intro s hs hsle
    rw [Metric.mem_ball, dist_zero_right, norm_mul, hε_norm, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.le]
    exact lt_of_le_of_lt hsle hrr_lt
  have harc_sub : ∀ ρ : ℝ, 0 < ρ → ρ ≤ A.arcRadius →
      A.arc ρ = ξ + (ρ:ℂ) * ε * β ((ρ:ℂ) * ε) := by
    intro ρ hρ hρle
    have hne : (ρ:ℂ) * ε ≠ 0 := mul_ne_zero (by exact_mod_cast hρ.ne') hε_ne
    have hform := hβ_form ((ρ:ℂ)*ε) (hmem ρ hρ hρle) hne
    have harc := A.arc_eq ρ hρ hρle
    rw [← hε] at harc
    rw [harc, hform]
  have heq : (fun ρ : ℝ => ξ + (ρ:ℂ) * ε * β ((ρ:ℂ) * ε)) =ᶠ[nhds ρ₀] A.arc := by
    filter_upwards [IsOpen.mem_nhds isOpen_Ioo (Set.mem_Ioo.mpr ⟨hρ₀, hρ₀'⟩)] with ρ hρ
    exact (harc_sub ρ hρ.1 (le_of_lt hρ.2)).symm
  have hin : ContinuousAt (fun ρ : ℝ => (ρ:ℂ) * ε) ρ₀ :=
    (Complex.continuous_ofReal.continuousAt).mul continuousAt_const
  have hβc : ContinuousAt β ((ρ₀:ℂ) * ε) :=
    (hβ_an ((ρ₀:ℂ)*ε) (hmem ρ₀ hρ₀ (le_of_lt hρ₀'))).continuousAt
  have hβcomp : ContinuousAt (fun ρ : ℝ => β ((ρ:ℂ) * ε)) ρ₀ :=
    ContinuousAt.comp_of_eq (g := β) (f := fun ρ : ℝ => (ρ:ℂ) * ε) hβc hin rfl
  exact (continuousAt_const.add (hin.mul hβcomp)).congr heq

/-- **Identity-theorem non-degeneracy** (Step 5, L1 payload).  If `f` is analytic on
a preconnected open `Ω ⊇ D^×(ξ,ρ0)` and vanishes along the selected arc for all small
`ρ>0`, then `f ≡ 0` on `Ω`.  Proof: the arc accumulates at an interior point
`A.arc ρ₀ ∈ Ω` (injectivity `arc_injOn` + continuity `arc_continuousAt`), so `f`
vanishes frequently in `𝓝[≠] (A.arc ρ₀)`; the analytic identity principle finishes.
This is the tool the `μ=m` non-degeneracy (`F∘arc ≢ 0`) consumes. -/
theorem eqOn_zero_of_eventually_arc_eq_zero {H : ℂ → ℂ} {ξ : ℂ} {m : ℕ} {c0 : ℂ}
    (A : SelectedArcData H ξ m c0)
    {Ω : Set ℂ} {ρ0 : ℝ} (hΩconn : IsPreconnected Ω) (hρ0 : 0 < ρ0)
    (hsub : puncturedDisc ξ ρ0 ⊆ Ω) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    (hzero : ∀ᶠ ρ in nhdsWithin (0:ℝ) (Set.Ioi 0), f (A.arc ρ) = 0) :
    Set.EqOn f 0 Ω := by
  have hΩmem : ∀ᶠ ρ in nhdsWithin (0:ℝ) (Set.Ioi 0), A.arc ρ ∈ Ω :=
    (arc_eventually_mem_puncturedDisc A hρ0).mono (fun ρ h => hsub h)
  have hlt : ∀ᶠ ρ in nhdsWithin (0:ℝ) (Set.Ioi 0), ρ < A.arcRadius :=
    (Filter.eventually_of_mem (Iio_mem_nhds A.arcRadius_pos) fun _ hx => hx).filter_mono
      nhdsWithin_le_nhds
  have hgood : ∀ᶠ ρ in nhdsWithin (0:ℝ) (Set.Ioi 0),
      f (A.arc ρ) = 0 ∧ A.arc ρ ∈ Ω ∧ ρ < A.arcRadius :=
    hzero.and (hΩmem.and hlt)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hgood
  obtain ⟨δ, hδpos, hδg⟩ := hgood
  set ρ₀ : ℝ := δ / 2 with hρ₀def
  have hρ₀pos : 0 < ρ₀ := by rw [hρ₀def]; linarith
  have hρ₀dist : dist ρ₀ 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hρ₀pos, hρ₀def]; linarith
  obtain ⟨hf0, hΩ0, hlt0⟩ := hδg hρ₀dist hρ₀pos
  -- `f (A.arc ·) = 0` on a full neighbourhood of `ρ₀`.
  have hnbhd : ∀ᶠ ρ in nhds ρ₀, f (A.arc ρ) = 0 := by
    filter_upwards [IsOpen.mem_nhds isOpen_Ioo
      (show ρ₀ ∈ Set.Ioo (0:ℝ) δ from ⟨hρ₀pos, by rw [hρ₀def]; linarith⟩)] with ρ hρ
    exact (hδg (by rw [Real.dist_eq, sub_zero, abs_of_pos hρ.1]; exact hρ.2) hρ.1).1
  -- accumulation of arc zeros at `A.arc ρ₀`.
  have htend : Tendsto A.arc (nhdsWithin ρ₀ ({ρ₀}ᶜ : Set ℝ))
      (nhdsWithin (A.arc ρ₀) ({A.arc ρ₀}ᶜ : Set ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨(arc_continuousAt A hρ₀pos hlt0).tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    have hIoo : ∀ᶠ ρ in nhdsWithin ρ₀ ({ρ₀}ᶜ : Set ℝ), ρ ∈ Set.Ioo (0:ℝ) A.arcRadius :=
      nhdsWithin_le_nhds (IsOpen.mem_nhds isOpen_Ioo ⟨hρ₀pos, hlt0⟩)
    filter_upwards [hIoo, self_mem_nhdsWithin] with ρ hρIoo hρne
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hcontra
    exact hρne (arc_injOn A hρIoo.1 (le_of_lt hρIoo.2) hρ₀pos (le_of_lt hlt0) hcontra)
  have hfreq_ρ : ∃ᶠ ρ in nhdsWithin ρ₀ ({ρ₀}ᶜ : Set ℝ), f (A.arc ρ) = 0 :=
    (hnbhd.filter_mono nhdsWithin_le_nhds).frequently
  exact hf.eqOn_zero_of_preconnected_of_frequently_eq_zero hΩconn hΩ0
    (htend.frequently hfreq_ρ)

/-- **Radius-gap decay** (Step 8/9, L2).  `(ρ_{(n)} − ρ_{(n+g)}) / ρ_{(n+g)}^m → 0`.
This is the quantity bounding the reduced-difference increment `ΔF` (Step 9) in the
`ν ≥ 1` branch.  Proof avoids `rpow`/MVT: `ρ_k·(2(N⋆+k)+1)` is monotone (its `m`-th
power is `‖c0‖·(2(N⋆+k)+1)^{m-1}/π` by `rho_pow_m`), giving the clean bound
`(ρ_n−ρ_{n+g})/ρ_{n+g}^m ≤ (2gπ/‖c0‖)·ρ_n → 0`. -/
theorem rho_gap_div_tendsto_zero {H : ℂ → ℂ} {ξ : ℂ} {m : ℕ} {c0 : ℂ}
    (A : SelectedArcData H ξ m c0) (hm : 1 ≤ m) (hc0 : c0 ≠ 0) (g : ℕ) :
    Tendsto (fun n => (A.rho n - A.rho (n + g)) / A.rho (n + g) ^ m) atTop (nhds 0) := by
  have hc0n : (0:ℝ) < ‖c0‖ := norm_pos_iff.mpr hc0
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  -- `(ρ_k · a_k)^m = ‖c0‖ · a_k^{m-1} / π`
  have hpk : ∀ k : ℕ, (A.rho k * ((2 * (A.Nstar + k) + 1 : ℕ) : ℝ)) ^ m
      = ‖c0‖ * ((2 * (A.Nstar + k) + 1 : ℕ) : ℝ) ^ (m - 1) / Real.pi := by
    intro k
    have hak : (0:ℝ) < ((2 * (A.Nstar + k) + 1 : ℕ) : ℝ) := by positivity
    have hsplit : ((2 * (A.Nstar + k) + 1 : ℕ) : ℝ) ^ m
        = ((2 * (A.Nstar + k) + 1 : ℕ) : ℝ) ^ (m - 1)
          * ((2 * (A.Nstar + k) + 1 : ℕ) : ℝ) := by
      rw [← pow_succ]; congr 1; omega
    rw [mul_pow, rho_pow_m A hm k, hsplit]
    field_simp
  -- monotonicity of `ρ_k · a_k`
  have hmono : ∀ n : ℕ, A.rho n * ((2 * (A.Nstar + n) + 1 : ℕ) : ℝ)
      ≤ A.rho (n + g) * ((2 * (A.Nstar + (n + g)) + 1 : ℕ) : ℝ) := by
    intro n
    have hpow : (A.rho n * ((2 * (A.Nstar + n) + 1 : ℕ) : ℝ)) ^ m
        ≤ (A.rho (n + g) * ((2 * (A.Nstar + (n + g)) + 1 : ℕ) : ℝ)) ^ m := by
      rw [hpk n, hpk (n + g)]
      gcongr
      omega
    exact le_of_pow_le_pow_left₀ (by omega)
      (mul_nonneg (A.rho_pos _).le (by positivity)) hpow
  -- squeeze
  have hnonneg : ∀ n, 0 ≤ (A.rho n - A.rho (n + g)) / A.rho (n + g) ^ m := by
    intro n
    apply div_nonneg _ (pow_nonneg (A.rho_pos _).le m)
    have := A.rho_strictAnti.antitone (show n ≤ n + g by omega)
    linarith
  have hbd : ∀ n, (A.rho n - A.rho (n + g)) / A.rho (n + g) ^ m
      ≤ (2 * (g : ℝ) * Real.pi / ‖c0‖) * A.rho n := by
    intro n
    have hpmpos : (0:ℝ) < A.rho (n + g) ^ m := by
      rw [rho_pow_m A hm (n + g)]; exact div_pos hc0n (by positivity)
    have hag_pos : (0:ℝ) < ((2 * (A.Nstar + (n + g)) + 1 : ℕ) : ℝ) := by positivity
    have hag : ((2 * (A.Nstar + (n + g)) + 1 : ℕ) : ℝ)
        = ((2 * (A.Nstar + n) + 1 : ℕ) : ℝ) + 2 * g := by push_cast; ring
    have hmn := hmono n
    rw [hag] at hmn
    have hrhs : (2 * (g:ℝ) * Real.pi / ‖c0‖) * A.rho n
          * (‖c0‖ / (((2 * (A.Nstar + (n + g)) + 1 : ℕ) : ℝ) * Real.pi))
        = 2 * g * A.rho n / ((2 * (A.Nstar + (n + g)) + 1 : ℕ) : ℝ) := by
      field_simp
    rw [div_le_iff₀ hpmpos, rho_pow_m A hm (n + g), hrhs, le_div_iff₀ hag_pos, hag]
    nlinarith [hmn]
  refine squeeze_zero hnonneg hbd ?_
  have hrho0 : Tendsto (fun n => A.rho n) atTop (nhds 0) :=
    A.rho_tendsto_zero.mono_right nhdsWithin_le_nhds
  simpa using hrho0.const_mul (2 * (g : ℝ) * Real.pi / ‖c0‖)


/-! ## `lem:window-avoidance` assembly

The final glue composing the 19 endgame helpers into the sequence-window
conclusion.  The combinatorial shell packages the good-index set (indices where
every sibling avoids `Π`) into the record; the analytic core
`no_recurring_collision` refutes a recurring sibling collision. -/

/-- **Local linear bound at a zero** (Step 7 input).  An analytic function
vanishing at `w₀` is dominated by `‖w - w₀‖` on a small ball.  This is the
`|Φ(w)| ≤ L·|w|` estimate (with `Φ(0)=0`) that upgrades the raw arc-pullback to
the `C₁ρ^{-m}` derivative bound. -/
theorem exists_ball_norm_le_of_analyticAt_eq_zero {Φ : ℂ → ℂ} {w₀ : ℂ}
    (hΦ : AnalyticAt ℂ Φ w₀) (hΦ0 : Φ w₀ = 0) :
    ∃ (L r : ℝ), 0 < r ∧ ∀ w ∈ Metric.ball w₀ r, ‖Φ w‖ ≤ L * ‖w - w₀‖ := by
  have hbigO : (fun w => Φ w) =O[nhds w₀] (fun w => w - w₀) := by
    have h := hΦ.differentiableAt.hasDerivAt.isBigO_sub
    simpa [hΦ0] using h
  rw [Asymptotics.isBigO_iff] at hbigO
  obtain ⟨C, hC⟩ := hbigO
  rw [Metric.eventually_nhds_iff_ball] at hC
  obtain ⟨r, hr, hball⟩ := hC
  refine ⟨C, r, hr, ?_⟩
  intro w hw
  exact hball w hw

/-- **Reduced-increment decay** (Steps 7 + 9).  For `Φ` analytic at `0` with
`Φ 0 = 0`, the reduced pullback `f(ρ) = ρ^{-m}·Φ(ρ·e^{iθ})` (`θ = A.angle`) has
`f(ρ_{n+g}) − f(ρ_n) → 0`.  The vanishing `Φ 0 = 0` is what turns the raw
`ρ^{-m-1}` derivative into the `C·ρ^{-m}` bound, and `rho_gap_div_tendsto_zero`
kills `(ρ_n − ρ_{n+g})/ρ_{n+g}^m`. -/
theorem reduced_increment_tendsto_zero {H : ℂ → ℂ} {ξ : ℂ} {m : ℕ} {c0 : ℂ}
    (A : SelectedArcData H ξ m c0) (hm : 1 ≤ m) (hc0 : c0 ≠ 0)
    {Φ : ℂ → ℂ} (hΦ : AnalyticAt ℂ Φ 0) (hΦ0 : Φ 0 = 0) (g : ℕ) :
    Tendsto (fun n : ℕ =>
        ((A.rho (n + g) : ℂ) ^ (-(m : ℤ)) *
            Φ ((A.rho (n + g) : ℂ) * Complex.exp ((A.angle : ℂ) * Complex.I)))
          - ((A.rho n : ℂ) ^ (-(m : ℤ)) *
            Φ ((A.rho n : ℂ) * Complex.exp ((A.angle : ℂ) * Complex.I))))
      atTop (nhds 0) := by
  classical
  set e : ℂ := Complex.exp ((A.angle : ℂ) * Complex.I) with he_def
  have he_ne : e ≠ 0 := by rw [he_def]; exact Complex.exp_ne_zero _
  have he_norm : ‖e‖ = 1 := by
    rw [he_def, Complex.norm_exp]
    have hre : ((A.angle : ℂ) * Complex.I).re = 0 := by rw [Complex.mul_I_re]; simp
    rw [hre, Real.exp_zero]
  set f : ℝ → ℂ := fun s => (s : ℂ) ^ (-(m : ℤ)) * Φ ((s : ℂ) * e) with hf_def
  -- linear bound near 0
  obtain ⟨L, r1, hr1, hL⟩ := exists_ball_norm_le_of_analyticAt_eq_zero hΦ hΦ0
  set Lp : ℝ := max L 0 with hLp
  have hLp0 : 0 ≤ Lp := le_max_right _ _
  have hL' : ∀ w ∈ Metric.ball (0 : ℂ) r1, ‖Φ w‖ ≤ Lp * ‖w‖ := by
    intro w hw
    refine le_trans (hL w hw) ?_
    have : ‖w - 0‖ = ‖w‖ := by rw [sub_zero]
    rw [this]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  -- derivative of Φ is bounded near 0
  have hderiv_an : AnalyticAt ℂ (deriv Φ) 0 := hΦ.deriv
  have hderiv_cont : ContinuousAt (deriv Φ) 0 := hderiv_an.continuousAt
  set M : ℝ := ‖deriv Φ 0‖ + 1 with hM_def
  have hM_pos : 0 < M := by rw [hM_def]; positivity
  have hMbound : ∀ᶠ w in nhds (0 : ℂ), ‖deriv Φ w‖ ≤ M := by
    have : ∀ᶠ w in nhds (0 : ℂ), ‖deriv Φ w‖ < M := by
      have hc : ContinuousAt (fun w => ‖deriv Φ w‖) 0 := hderiv_cont.norm
      have : Tendsto (fun w => ‖deriv Φ w‖) (nhds 0) (nhds ‖deriv Φ 0‖) := hc
      exact this (Iio_mem_nhds (by rw [hM_def]; linarith))
    exact this.mono fun w hw => le_of_lt hw
  rw [Metric.eventually_nhds_iff_ball] at hMbound
  obtain ⟨r2, hr2, hM⟩ := hMbound
  -- Φ differentiable near 0
  have hΦev : ∀ᶠ w in nhds (0 : ℂ), AnalyticAt ℂ Φ w := hΦ.eventually_analyticAt
  rw [Metric.eventually_nhds_iff_ball] at hΦev
  obtain ⟨r3, hr3, hΦdiff⟩ := hΦev
  -- shrink to a common radius, strict
  set R : ℝ := min r1 (min r2 r3) with hR_def
  have hR_pos : 0 < R := by rw [hR_def]; exact lt_min hr1 (lt_min hr2 hr3)
  set r : ℝ := R / 2 with hr_def
  have hr_pos : 0 < r := by rw [hr_def]; linarith
  have hr_lt : r < R := by rw [hr_def]; linarith
  -- membership: ρ·e in balls for ρ ∈ (0, r]
  have hmem : ∀ ρ : ℝ, 0 < ρ → ρ ≤ r → (ρ : ℂ) * e ∈ Metric.ball (0 : ℂ) r1 ∧
      (ρ : ℂ) * e ∈ Metric.ball (0 : ℂ) r2 ∧ (ρ : ℂ) * e ∈ Metric.ball (0 : ℂ) r3 := by
    intro ρ hρ hρr
    have hnorm : ‖(ρ : ℂ) * e‖ = ρ := by
      rw [norm_mul, he_norm, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
    have hlt : ρ < R := lt_of_le_of_lt hρr hr_lt
    refine ⟨?_, ?_, ?_⟩ <;>
      · rw [Metric.mem_ball, dist_zero_right, hnorm]
        first
          | exact lt_of_lt_of_le hlt (le_trans (min_le_right _ _) (min_le_left _ _))
          | exact lt_of_lt_of_le hlt (le_trans (min_le_right _ _) (min_le_right _ _))
          | exact lt_of_lt_of_le hlt (min_le_left _ _)
  -- constant
  set C : ℝ := (m : ℝ) * Lp + M with hC_def
  have hC0 : 0 ≤ C := by rw [hC_def]; positivity
  -- derivative + bound for f on (0, r], phrased via `deriv f`
  have hderivf : ∀ ρ : ℝ, 0 < ρ → ρ ≤ r → HasDerivAt f (deriv f ρ) ρ := by
    intro ρ hρ hρr
    have hdiffΦ : DifferentiableAt ℂ Φ ((ρ : ℂ) * e) :=
      (hΦdiff _ (hmem ρ hρ hρr).2.2).differentiableAt
    exact (hasDerivAt_ofRealZpow_mul_comp (-(m : ℤ)) hρ hdiffΦ).differentiableAt.hasDerivAt
  have hbound : ∀ ρ : ℝ, 0 < ρ → ρ ≤ r → ‖deriv f ρ‖ ≤ C * ρ ^ (-(m : ℤ)) := by
    intro ρ hρ hρr
    have hdiffΦ : DifferentiableAt ℂ Φ ((ρ : ℂ) * e) :=
      (hΦdiff _ (hmem ρ hρ hρr).2.2).differentiableAt
    have hD := hasDerivAt_ofRealZpow_mul_comp (-(m : ℤ)) hρ hdiffΦ
    rw [hD.deriv]
    have hnormrho : ‖(ρ : ℂ)‖ = ρ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
    have hz1 : ‖(ρ : ℂ) ^ (-(m : ℤ) - 1)‖ = ρ ^ (-(m : ℤ) - 1) := by
      rw [norm_zpow, hnormrho]
    have hz2 : ‖(ρ : ℂ) ^ (-(m : ℤ))‖ = ρ ^ (-(m : ℤ)) := by
      rw [norm_zpow, hnormrho]
    have hΦw : ‖Φ ((ρ : ℂ) * e)‖ ≤ Lp * ρ := by
      have := hL' _ (hmem ρ hρ hρr).1
      rwa [show ‖(ρ : ℂ) * e‖ = ρ by
        rw [norm_mul, he_norm, mul_one, hnormrho]] at this
    have hdw : ‖deriv Φ ((ρ : ℂ) * e)‖ ≤ M := hM _ (hmem ρ hρ hρr).2.1
    have hnm : ‖(((-(m : ℤ)) : ℤ) : ℂ)‖ = (m : ℝ) := by
      push_cast; rw [norm_neg, Complex.norm_natCast]
    have hpm : ρ ^ (-(m : ℤ) - 1) * ρ = ρ ^ (-(m : ℤ)) := by
      have h := (zpow_add₀ hρ.ne' (-(m : ℤ) - 1) 1).symm
      simpa using h
    have hstep1 : ‖(((-(m : ℤ)) : ℤ) : ℂ) * (ρ : ℂ) ^ (-(m : ℤ) - 1) * Φ ((ρ : ℂ) * e)‖
        ≤ (m : ℝ) * Lp * ρ ^ (-(m : ℤ)) := by
      rw [norm_mul, norm_mul, hz1, hnm]
      have hρnn : (0:ℝ) ≤ (m : ℝ) * ρ ^ (-(m : ℤ) - 1) := by positivity
      calc (m : ℝ) * ρ ^ (-(m : ℤ) - 1) * ‖Φ ((ρ : ℂ) * e)‖
            ≤ (m : ℝ) * ρ ^ (-(m : ℤ) - 1) * (Lp * ρ) :=
              mul_le_mul_of_nonneg_left hΦw hρnn
        _ = (m : ℝ) * Lp * (ρ ^ (-(m : ℤ) - 1) * ρ) := by ring
        _ = (m : ℝ) * Lp * ρ ^ (-(m : ℤ)) := by rw [hpm]
    have hstep2 : ‖(ρ : ℂ) ^ (-(m : ℤ)) * (e * deriv Φ ((ρ : ℂ) * e))‖
        ≤ M * ρ ^ (-(m : ℤ)) := by
      rw [norm_mul, norm_mul, hz2, he_norm, one_mul]
      have hρnn : (0:ℝ) ≤ ρ ^ (-(m : ℤ)) := le_of_lt (zpow_pos hρ _)
      calc ρ ^ (-(m : ℤ)) * ‖deriv Φ ((ρ : ℂ) * e)‖
            ≤ ρ ^ (-(m : ℤ)) * M := mul_le_mul_of_nonneg_left hdw hρnn
        _ = M * ρ ^ (-(m : ℤ)) := by ring
    calc ‖(((-(m : ℤ)) : ℤ) : ℂ) * (ρ : ℂ) ^ (-(m : ℤ) - 1) * Φ ((ρ : ℂ) * e)
              + (ρ : ℂ) ^ (-(m : ℤ)) * (e * deriv Φ ((ρ : ℂ) * e))‖
          ≤ ‖(((-(m : ℤ)) : ℤ) : ℂ) * (ρ : ℂ) ^ (-(m : ℤ) - 1) * Φ ((ρ : ℂ) * e)‖
            + ‖(ρ : ℂ) ^ (-(m : ℤ)) * (e * deriv Φ ((ρ : ℂ) * e))‖ := norm_add_le _ _
      _ ≤ (m : ℝ) * Lp * ρ ^ (-(m : ℤ)) + M * ρ ^ (-(m : ℤ)) := add_le_add hstep1 hstep2
      _ = C * ρ ^ (-(m : ℤ)) := by rw [hC_def]; ring
  -- Now bound the increment for large n and squeeze.
  have hrho0 : Tendsto (fun n => A.rho n) atTop (nhds 0) :=
    A.rho_tendsto_zero.mono_right nhdsWithin_le_nhds
  have hev_le : ∀ᶠ n in atTop, A.rho n ≤ r := by
    filter_upwards [hrho0 (Iio_mem_nhds hr_pos)] with n hn using le_of_lt hn
  -- pointwise increment bound
  have hincr_bound : ∀ᶠ n in atTop,
      ‖f (A.rho (n + g)) - f (A.rho n)‖
        ≤ C * ((A.rho n - A.rho (n + g)) / A.rho (n + g) ^ m) := by
    filter_upwards [hev_le] with n hn
    have hng_le : A.rho (n + g) ≤ A.rho n := A.rho_strictAnti.antitone (by omega)
    have hng_pos : 0 < A.rho (n + g) := A.rho_pos _
    have hn_le_r : A.rho n ≤ r := hn
    -- Icc [ρ_{n+g}, ρ_n] ⊆ (0, r]
    have hderiv_Icc : ∀ x ∈ Set.Icc (A.rho (n + g)) (A.rho n),
        HasDerivAt f (deriv f x) x := by
      intro x hx
      exact hderivf x (lt_of_lt_of_le hng_pos hx.1) (le_trans hx.2 hn_le_r)
    have hbound_Icc : ∀ x ∈ Set.Icc (A.rho (n + g)) (A.rho n),
        ‖deriv f x‖ ≤ C * A.rho (n + g) ^ (-(m : ℤ)) := by
      intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le hng_pos hx.1
      refine le_trans (hbound x hxpos (le_trans hx.2 hn_le_r)) ?_
      have hmono : x ^ (-(m : ℤ)) ≤ A.rho (n + g) ^ (-(m : ℤ)) := by
        rw [_root_.zpow_neg, _root_.zpow_neg, zpow_natCast, zpow_natCast]
        exact inv_anti₀ (pow_pos hng_pos m) (pow_le_pow_left₀ hng_pos.le hx.1 m)
      exact mul_le_mul_of_nonneg_left hmono hC0
    have hle := norm_sub_le_of_hasDerivAt_bound_Icc hderiv_Icc hbound_Icc
      (Set.left_mem_Icc.2 hng_le) (Set.right_mem_Icc.2 hng_le)
    -- hle : ‖f ρ_n - f ρ_{n+g}‖ ≤ (C * ρ_{n+g}^{-m}) * ‖ρ_n - ρ_{n+g}‖
    have hnormsub : ‖A.rho n - A.rho (n + g)‖ = A.rho n - A.rho (n + g) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    rw [hnormsub] at hle
    rw [norm_sub_rev]
    calc ‖f (A.rho n) - f (A.rho (n + g))‖
          ≤ C * A.rho (n + g) ^ (-(m : ℤ)) * (A.rho n - A.rho (n + g)) := hle
      _ = C * ((A.rho n - A.rho (n + g)) / A.rho (n + g) ^ m) := by
            rw [_root_.zpow_neg, zpow_natCast]; ring
  -- RHS tends to 0
  have hRHS : Tendsto (fun n : ℕ => C * ((A.rho n - A.rho (n + g)) / A.rho (n + g) ^ m))
      atTop (nhds 0) := by
    have := (rho_gap_div_tendsto_zero A hm hc0 g).const_mul C
    simpa using this
  -- squeeze on norms
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall (fun n => norm_nonneg _)) hincr_bound ?_
  simpa using hRHS

/-- **Rolle rigidity of the reduced bracket** (Step 11, `ν ≠ 0`).  If a reduced
pullback `f(ρ) = ρ^{-ν}·Ψ(ρ·e^{iθ})` (`θ = A.angle`, `Ψ` analytic at `0`) takes
equal values at `ρ_{n+g}` and `ρ_n` for infinitely many `n`, then — provided
`ν ≠ 0` — its leading bracket vanishes: `Ψ 0 = 0`.  Rolle on the real and
imaginary parts pins interior zeros of the derivative accumulating at `0`, whose
limit forces `ν · Ψ 0 = 0`. -/
theorem bracket_zero_of_rolle_of_frequently_eq {H : ℂ → ℂ} {ξ : ℂ} {m : ℕ} {c0 : ℂ}
    (A : SelectedArcData H ξ m c0) {g : ℕ} (hg : 1 ≤ g) {ν : ℤ} (hν : ν ≠ 0)
    {Ψ : ℂ → ℂ} (hΨ : AnalyticAt ℂ Ψ 0)
    (hEq : ∃ᶠ n in atTop,
        (A.rho (n + g) : ℂ) ^ (-ν) *
            Ψ ((A.rho (n + g) : ℂ) * Complex.exp ((A.angle : ℂ) * Complex.I))
          = (A.rho n : ℂ) ^ (-ν) *
            Ψ ((A.rho n : ℂ) * Complex.exp ((A.angle : ℂ) * Complex.I))) :
    Ψ 0 = 0 := by
  classical
  set e : ℂ := Complex.exp ((A.angle : ℂ) * Complex.I) with he_def
  have he_ne : e ≠ 0 := by rw [he_def]; exact Complex.exp_ne_zero _
  have he_norm : ‖e‖ = 1 := by
    rw [he_def, Complex.norm_exp]
    have hre : ((A.angle : ℂ) * Complex.I).re = 0 := by rw [Complex.mul_I_re]; simp
    rw [hre, Real.exp_zero]
  set f : ℝ → ℂ := fun s => (s : ℂ) ^ (-ν) * Ψ ((s : ℂ) * e) with hf_def
  -- Ψ differentiable near 0
  have hΨev : ∀ᶠ w in nhds (0 : ℂ), AnalyticAt ℂ Ψ w := hΨ.eventually_analyticAt
  rw [Metric.eventually_nhds_iff_ball] at hΨev
  obtain ⟨r3, hr3, hΨdiff⟩ := hΨev
  set r : ℝ := r3 / 2 with hr_def
  have hr_pos : 0 < r := by rw [hr_def]; linarith
  have hmem : ∀ ρ : ℝ, 0 < ρ → ρ ≤ r → (ρ : ℂ) * e ∈ Metric.ball (0 : ℂ) r3 := by
    intro ρ hρ hρr
    rw [Metric.mem_ball, dist_zero_right, norm_mul, he_norm, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hρ]
    have : ρ ≤ r3 / 2 := by rw [← hr_def]; exact hρr
    linarith
  -- continuous bracket P with P 0 = -ν · Ψ 0
  set P : ℝ → ℂ := fun ρ => ((-ν : ℤ) : ℂ) * Ψ ((ρ : ℂ) * e)
    + (ρ : ℂ) * (e * deriv Ψ ((ρ : ℂ) * e)) with hP_def
  have hP0 : P 0 = ((-ν : ℤ) : ℂ) * Ψ 0 := by simp [hP_def]
  have hPcont : ContinuousAt P 0 := by
    have hin : ContinuousAt (fun ρ : ℝ => (ρ : ℂ) * e) 0 :=
      (Complex.continuous_ofReal.continuousAt).mul continuousAt_const
    have h1 : ContinuousAt (fun ρ : ℝ => Ψ ((ρ : ℂ) * e)) 0 :=
      hΨ.continuousAt.comp_of_eq hin (by simp)
    have h2 : ContinuousAt (fun ρ : ℝ => deriv Ψ ((ρ : ℂ) * e)) 0 :=
      hΨ.deriv.continuousAt.comp_of_eq hin (by simp)
    exact (continuousAt_const.mul h1).add
      ((Complex.continuous_ofReal.continuousAt).mul (continuousAt_const.mul h2))
  -- derivative of f and its factorization on (0, r]
  have hderivf : ∀ ρ : ℝ, 0 < ρ → ρ ≤ r → HasDerivAt f (deriv f ρ) ρ := by
    intro ρ hρ hρr
    exact (hasDerivAt_ofRealZpow_mul_comp (-ν) hρ
      (hΨdiff _ (hmem ρ hρ hρr)).differentiableAt).differentiableAt.hasDerivAt
  have hfact : ∀ ρ : ℝ, 0 < ρ → ρ ≤ r →
      deriv f ρ = ((ρ ^ (-ν - 1) : ℝ) : ℂ) * P ρ := by
    intro ρ hρ hρr
    have hD := hasDerivAt_ofRealZpow_mul_comp (-ν) hρ
      (hΨdiff _ (hmem ρ hρ hρr)).differentiableAt
    rw [hD.deriv, hP_def]
    have hzc : ((ρ ^ (-ν - 1) : ℝ) : ℂ) = (ρ : ℂ) ^ (-ν - 1) := Complex.ofReal_zpow _ _
    rw [hzc]
    have hpow : (ρ : ℂ) ^ (-ν - 1) * (ρ : ℂ) = (ρ : ℂ) ^ (-ν) := by
      have h := (zpow_add₀ (by exact_mod_cast hρ.ne' : (ρ : ℂ) ≠ 0) (-ν - 1) 1).symm
      simpa using h
    rw [mul_add,
      show (ρ : ℂ) ^ (-ν - 1) * ((ρ : ℂ) * (e * deriv Ψ ((ρ : ℂ) * e)))
        = ((ρ : ℂ) ^ (-ν - 1) * (ρ : ℂ)) * (e * deriv Ψ ((ρ : ℂ) * e)) by ring, hpow]
    ring
  -- eventual smallness of ρ_n
  have hrho0 : Tendsto (fun n => A.rho n) atTop (nhds 0) :=
    A.rho_tendsto_zero.mono_right nhdsWithin_le_nhds
  have hev_le : ∀ᶠ n in atTop, A.rho n ≤ r := by
    filter_upwards [hrho0 (Iio_mem_nhds hr_pos)] with n hn using le_of_lt hn
  -- the core: for any rotation `u`, `Re (u * P 0) = 0`
  have claim : ∀ u : ℂ, (u * P 0).re = 0 := by
    intro u
    -- frequently: n large, equal values
    have hfreq2 : ∃ᶠ n in atTop,
        (A.rho (n + g) : ℂ) ^ (-ν) * Ψ ((A.rho (n + g) : ℂ) * e)
            = (A.rho n : ℂ) ^ (-ν) * Ψ ((A.rho n : ℂ) * e)
          ∧ A.rho n ≤ r := hEq.and_eventually hev_le
    obtain ⟨φ, hφ_mono, hφ⟩ := extraction_of_frequently_atTop hfreq2
    -- for each k, Rolle gives c_k with Re(u * P c_k) = 0
    have hc : ∀ k : ℕ, ∃ ck : ℝ, A.rho (φ k + g) < ck ∧ ck < A.rho (φ k)
        ∧ (u * P ck).re = 0 := by
      intro k
      obtain ⟨hEqk, hlek⟩ := hφ k
      have hlt : A.rho (φ k + g) < A.rho (φ k) := A.rho_strictAnti (by omega)
      have hle_r : A.rho (φ k) ≤ r := hlek
      have hderiv_Icc : ∀ x ∈ Set.Icc (A.rho (φ k + g)) (A.rho (φ k)),
          HasDerivAt (fun s => u * f s) (u * deriv f x) x := by
        intro x hx
        exact (hderivf x (lt_of_lt_of_le (A.rho_pos _) hx.1) (le_trans hx.2 hle_r)).const_mul u
      have hval : (u * f (A.rho (φ k + g))).re = (u * f (A.rho (φ k))).re := by
        have : f (A.rho (φ k + g)) = f (A.rho (φ k)) := hEqk
        rw [this]
      obtain ⟨ck, hck_mem, hck_re⟩ :=
        exists_mem_Ioo_re_deriv_eq_zero hlt hderiv_Icc hval
      refine ⟨ck, hck_mem.1, hck_mem.2, ?_⟩
      -- unfold Re(u * deriv f ck) = 0 into Re(u * P ck) = 0
      have hckpos : 0 < ck := lt_trans (A.rho_pos _) hck_mem.1
      have hckle : ck ≤ r := le_trans (le_of_lt hck_mem.2) hle_r
      have hfk := hfact ck hckpos hckle
      rw [hfk] at hck_re
      have hfactor : u * (((ck ^ (-ν - 1) : ℝ) : ℂ) * P ck)
          = ((ck ^ (-ν - 1) : ℝ) : ℂ) * (u * P ck) := by ring
      rw [hfactor, Complex.re_ofReal_mul] at hck_re
      have hzne : ck ^ (-ν - 1) ≠ 0 := (zpow_pos hckpos _).ne'
      exact (mul_eq_zero.mp hck_re).resolve_left hzne
    -- assemble the sequence ck and take the limit
    choose ck hck1 hck2 hck3 using hc
    have hck_tendsto : Tendsto ck atTop (nhds 0) := by
      have hlo : Tendsto (fun k => A.rho (φ k + g)) atTop (nhds 0) :=
        hrho0.comp (tendsto_atTop_mono (fun k => by omega) hφ_mono.tendsto_atTop)
      have hhi : Tendsto (fun k => A.rho (φ k)) atTop (nhds 0) :=
        hrho0.comp hφ_mono.tendsto_atTop
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
        (fun k => le_of_lt (hck1 k)) (fun k => le_of_lt (hck2 k))
    have hcomp : ContinuousAt (fun ρ : ℝ => (u * P ρ).re) 0 :=
      (Complex.continuous_re.continuousAt).comp (continuousAt_const.mul hPcont)
    have hlim : Tendsto (fun k => (u * P (ck k)).re) atTop (nhds ((u * P 0).re)) :=
      hcomp.tendsto.comp hck_tendsto
    exact tendsto_nhds_unique hlim (by simp only [hck3]; exact tendsto_const_nhds)
  -- Re and Im of P 0 vanish, so P 0 = 0, so Ψ 0 = 0.
  have hre : (P 0).re = 0 := by simpa using claim 1
  have him : (P 0).im = 0 := by
    have h := claim (-Complex.I)
    simp only [neg_mul, Complex.neg_re, Complex.I_mul_re, neg_neg] at h
    exact h
  have hP0z : P 0 = 0 := Complex.ext hre him
  rw [hP0] at hP0z
  have hνc : ((-ν : ℤ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Int.cast_eq_zero, neg_eq_zero]
    exact_mod_cast hν
  exact (mul_eq_zero.mp hP0z).resolve_left hνc

/-- **Real-analytic constancy** (Step 11, `ν = 0` subcase).  If the reduced
pullback bracket `ρ ↦ Ψ(ρ·e^{iθ})` has real part vanishing along the selected
radii (frequently) and equal values at `ρ_{n+g}`/`ρ_n` (frequently), then it is
eventually constant near `0⁺` with purely-imaginary value.  The real part gives
`Re(Ψ(ρe))≡0` by the real-analytic identity theorem; the equal values give
`(Im Ψ(ρe))'≡0` by Rolle + the identity theorem; together `ρ ↦ Ψ(ρe)` has zero
derivative hence is locally constant. -/
theorem reduced_const_of_re_zero_and_eq {H : ℂ → ℂ} {ξ : ℂ} {m : ℕ} {c0 : ℂ}
    (A : SelectedArcData H ξ m c0) {g : ℕ} (hg : 1 ≤ g)
    {Ψ : ℂ → ℂ} (hΨ : AnalyticAt ℂ Ψ 0)
    (hre : ∃ᶠ n in atTop,
        (Ψ ((A.rho n : ℂ) * Complex.exp ((A.angle : ℂ) * Complex.I))).re = 0)
    (heq : ∃ᶠ n in atTop,
        Ψ ((A.rho (n + g) : ℂ) * Complex.exp ((A.angle : ℂ) * Complex.I))
          = Ψ ((A.rho n : ℂ) * Complex.exp ((A.angle : ℂ) * Complex.I))) :
    ∃ c : ℂ, c.re = 0 ∧
      ∀ᶠ (ρ : ℝ) in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        Ψ ((ρ : ℂ) * Complex.exp ((A.angle : ℂ) * Complex.I)) = c := by
  classical
  set e : ℂ := Complex.exp ((A.angle : ℂ) * Complex.I) with he_def
  set F : ℂ → ℂ := fun z => Ψ (z * e) with hF_def
  have hF_an : AnalyticAt ℂ F 0 :=
    hΨ.comp_of_eq (analyticAt_id.mul analyticAt_const) (by simp)
  set h : ℝ → ℂ := fun ρ => F (ρ : ℂ) with hh_def
  have hh_val : ∀ ρ : ℝ, h ρ = Ψ ((ρ : ℂ) * e) := fun ρ => rfl
  have hh_an : AnalyticAt ℝ h 0 :=
    hF_an.restrictScalars.comp_of_eq (Complex.ofRealCLM.analyticAt 0) (by simp)
  set uf : ℝ → ℝ := fun ρ => (h ρ).re with huf_def
  set vf : ℝ → ℝ := fun ρ => (h ρ).im with hvf_def
  have huf_an : AnalyticAt ℝ uf 0 := hF_an.re_ofReal
  have hvf_an : AnalyticAt ℝ vf 0 := hF_an.im_ofReal
  have htend : Tendsto A.rho atTop (nhdsWithin (0 : ℝ) ({0}ᶜ)) :=
    A.rho_tendsto_zero.mono_right (nhdsWithin_mono 0 (fun x hx => ne_of_gt hx))
  have hrho0 : Tendsto A.rho atTop (nhds 0) := htend.mono_right nhdsWithin_le_nhds
  -- (1) `uf ≡ 0` near 0
  have huf_ev : uf =ᶠ[nhds 0] 0 := by
    refine huf_an.frequently_zero_iff_eventually_zero.mp (htend.frequently ?_)
    refine hre.mono (fun n hn => ?_)
    simpa [huf_def, hh_val] using hn
  -- (2) `deriv vf ≡ 0` near 0 (Rolle + identity)
  have hvf_diff_ev : ∀ᶠ ρ in nhds (0 : ℝ), DifferentiableAt ℝ vf ρ := by
    filter_upwards [hvf_an.eventually_analyticAt] with ρ hρ using hρ.differentiableAt
  obtain ⟨rv, hrv, hvf_diff⟩ := Metric.eventually_nhds_iff_ball.1 hvf_diff_ev
  have hderiv_vf_ev : deriv vf =ᶠ[nhds 0] 0 := by
    refine (hvf_an.deriv).frequently_zero_iff_eventually_zero.mp ?_
    have hsmall : ∀ᶠ n in atTop, A.rho n < rv := by
      filter_upwards [hrho0 (Iio_mem_nhds hrv)] with n hn using hn
    have hfreq2 : ∃ᶠ n in atTop, vf (A.rho (n + g)) = vf (A.rho n) ∧ A.rho n < rv := by
      refine (heq.and_eventually hsmall).mono (fun n hn => ?_)
      obtain ⟨heqn, hsn⟩ := hn
      exact ⟨by simpa [hvf_def, hh_val] using congrArg Complex.im heqn, hsn⟩
    obtain ⟨φ, hφ_mono, hφ⟩ := extraction_of_frequently_atTop hfreq2
    have hc : ∀ k : ℕ, ∃ ck : ℝ, A.rho (φ k + g) < ck ∧ ck < A.rho (φ k)
        ∧ deriv vf ck = 0 := by
      intro k
      obtain ⟨heqk, hsk⟩ := hφ k
      have hlt : A.rho (φ k + g) < A.rho (φ k) := A.rho_strictAnti (by omega)
      have hsub : Set.Icc (A.rho (φ k + g)) (A.rho (φ k)) ⊆ Metric.ball (0 : ℝ) rv := by
        intro x hx
        rw [Metric.mem_ball, Real.dist_eq, sub_zero,
          abs_of_pos (lt_of_lt_of_le (A.rho_pos _) hx.1)]
        exact lt_of_le_of_lt hx.2 hsk
      have hcont : ContinuousOn vf (Set.Icc (A.rho (φ k + g)) (A.rho (φ k))) :=
        fun x hx => (hvf_diff x (hsub hx)).continuousAt.continuousWithinAt
      obtain ⟨ck, hck_mem, hck⟩ := exists_deriv_eq_zero hlt hcont heqk
      exact ⟨ck, hck_mem.1, hck_mem.2, hck⟩
    choose ck hck1 hck2 hck3 using hc
    have hck_tend : Tendsto ck atTop (nhdsWithin (0 : ℝ) ({0}ᶜ)) := by
      have hlo : Tendsto (fun k => A.rho (φ k + g)) atTop (nhds 0) :=
        hrho0.comp (tendsto_atTop_mono (fun k => by omega) hφ_mono.tendsto_atTop)
      have hhi : Tendsto (fun k => A.rho (φ k)) atTop (nhds 0) :=
        hrho0.comp hφ_mono.tendsto_atTop
      have h0 : Tendsto ck atTop (nhds 0) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
          (fun k => le_of_lt (hck1 k)) (fun k => le_of_lt (hck2 k))
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h0 ?_
      exact Filter.Eventually.of_forall (fun k => ne_of_gt (lt_trans (A.rho_pos _) (hck1 k)))
    exact hck_tend.frequently ((Filter.Eventually.of_forall hck3).frequently)
  -- (3) `deriv h ≡ 0` near 0
  have hderiv_h_ev : ∀ᶠ ρ in nhds (0 : ℝ), deriv h ρ = 0 := by
    have huf_ev2 : ∀ᶠ ρ in nhds (0 : ℝ), uf =ᶠ[nhds ρ] 0 := huf_ev.eventually_nhds
    filter_upwards [huf_ev2, hderiv_vf_ev, hvf_diff_ev,
      (hh_an.eventually_analyticAt)] with ρ huf_ρ hvf'_ρ hvf_ρ hh_ρ
    have hd : HasDerivAt h (deriv h ρ) ρ := hh_ρ.differentiableAt.hasDerivAt
    have hre_d : HasDerivAt uf ((deriv h ρ).re) ρ := by
      have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt ρ hd
      simpa [huf_def, Complex.reCLM_apply] using this
    have hre_0 : HasDerivAt uf 0 ρ :=
      (hasDerivAt_const ρ (0 : ℝ)).congr_of_eventuallyEq huf_ρ
    have hre_eq : (deriv h ρ).re = 0 := hre_d.unique hre_0
    have him_d : HasDerivAt vf ((deriv h ρ).im) ρ := by
      have := Complex.imCLM.hasFDerivAt.comp_hasDerivAt ρ hd
      simpa [hvf_def, Complex.imCLM_apply] using this
    have him_eq : (deriv h ρ).im = 0 := by
      have := him_d.unique hvf_ρ.hasDerivAt
      rw [this]; exact hvf'_ρ
    exact Complex.ext hre_eq him_eq
  -- (4) local constancy of `h`
  obtain ⟨δ1, hδ1, hderiv0⟩ := Metric.eventually_nhds_iff_ball.1 hderiv_h_ev
  obtain ⟨δ2, hδ2, hdiff'⟩ :=
    Metric.eventually_nhds_iff_ball.1 (hh_an.eventually_analyticAt)
  obtain ⟨δ3, hδ3, huf0⟩ := Metric.eventually_nhds_iff_ball.1 huf_ev
  set r0 : ℝ := min δ1 (min δ2 δ3) with hr0
  have hr0pos : 0 < r0 := lt_min hδ1 (lt_min hδ2 hδ3)
  set ρ0 : ℝ := r0 / 2 with hρ0
  have hρ0pos : 0 < ρ0 := by rw [hρ0]; linarith
  have hballsub : Metric.ball (0 : ℝ) r0 ⊆
      Metric.ball 0 δ1 ∩ Metric.ball 0 δ2 ∩ Metric.ball 0 δ3 := by
    intro x hx
    rw [Metric.mem_ball] at hx
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> rw [Metric.mem_ball]
    · exact lt_of_lt_of_le hx (min_le_left _ _)
    · exact lt_of_lt_of_le hx (le_trans (min_le_right _ _) (min_le_left _ _))
    · exact lt_of_lt_of_le hx (le_trans (min_le_right _ _) (min_le_right _ _))
  have hρ0mem : ρ0 ∈ Metric.ball (0 : ℝ) r0 := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hρ0pos, hρ0]; linarith
  refine ⟨h ρ0, ?_, ?_⟩
  · have huf0ρ0 : uf ρ0 = 0 := huf0 ρ0 (hballsub hρ0mem).2
    simpa [huf_def] using huf0ρ0
  · have hconst : ∀ ρ ∈ Set.Ioo (0 : ℝ) r0, h ρ = h ρ0 := by
      intro ρ hρ
      have hIcc : Set.Icc (min ρ ρ0) (max ρ ρ0) ⊆ Metric.ball (0 : ℝ) r0 := by
        intro x hx
        rw [Metric.mem_ball, Real.dist_eq, sub_zero,
          abs_of_pos (lt_of_lt_of_le (lt_min hρ.1 hρ0pos) hx.1)]
        refine lt_of_le_of_lt hx.2 (max_lt hρ.2 ?_)
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hρ0pos] at hρ0mem
        exact hρ0mem
      have hderiv_Icc : ∀ x ∈ Set.Icc (min ρ ρ0) (max ρ ρ0), HasDerivAt h (deriv h x) x :=
        fun x hx => (hdiff' x (hballsub (hIcc hx)).1.2).differentiableAt.hasDerivAt
      have hbound_Icc : ∀ x ∈ Set.Icc (min ρ ρ0) (max ρ ρ0), ‖deriv h x‖ ≤ 0 := by
        intro x hx
        rw [hderiv0 x (hballsub (hIcc hx)).1.1]; simp
      have hle := norm_sub_le_of_hasDerivAt_bound_Icc hderiv_Icc hbound_Icc
        (x := ρ) (y := ρ0) (Set.mem_Icc.2 ⟨min_le_left _ _, le_max_left _ _⟩)
        (Set.mem_Icc.2 ⟨min_le_right _ _, le_max_right _ _⟩)
      have hz : h ρ0 = h ρ := by
        simp only [zero_mul] at hle
        exact sub_eq_zero.1 (norm_eq_zero.1 (le_antisymm hle (norm_nonneg _)))
      exact hz.symm
    have hIoo_mem : Set.Ioo (0 : ℝ) r0 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
      have h1 : Set.Ioi (0 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := self_mem_nhdsWithin
      have h2 : Set.Iio r0 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
        nhdsWithin_le_nhds (Iio_mem_nhds hr0pos)
      have hmem := Filter.inter_mem h1 h2
      rwa [Set.Ioi_inter_Iio] at hmem
    filter_upwards [hIoo_mem] with ρ hρ
    have hcρ := hconst ρ hρ
    rw [hh_val] at hcρ
    exact hcρ

/-- **Sequence-window packaging.**  Given the selected arc data and the set of
"good" indices (at which every sibling avoids `Π`) infinite, produce the
sequence-window record with `σ_n = A.arc (A.rho n)`. -/
theorem selectedSequenceWindowAvoidance_of_arc_goodIndices
    {ξ : ℂ} {K m : Nat} {c0 : ℂ} {H : Fin (K + 1) -> ℂ -> ℂ}
    (A : SelectedArcData (H 0) ξ m c0)
    (hgood : {n : ℕ | ∀ c : Fin K, H c.succ (A.arc (A.rho n)) ∉ Pi}.Infinite) :
    SelectedSequenceWindowAvoidance ξ H :=
  ⟨⟨fun n => A.arc (A.rho n), A.sigma_tendsto, A.sigma_ne_center,
    A.sigma_injective, A.sigma_mem_pi, hgood⟩⟩

set_option maxHeartbeats 1000000 in
/-- Endgame of `no_recurring_collision`: from the reduced pullback
`F(arc ρ) = ρ^{-m}·Φ(ρ·e)` with `Φ 0 = 0`, together with the frequent
equality/reality facts along the selected sequence, derive `False`.  Split off from
`no_recurring_collision` to keep each proof within the heartbeat budget.  `Φ ≡ 0`
gives `F ≡ 0`; otherwise factor `Φ = w^κ·Φ̃` to a reduced form `ρ^{-ν}·Ψ_F` refuted by
`bracket_zero_of_rolle_of_frequently_eq` (`ν ≠ 0`) or `reduced_const_of_re_zero_and_eq`
plus the identity theorem (`ν = 0`). -/
theorem no_recurring_collision_endgame {Ω : Set ℂ} {ξ : ℂ} {ρ0 : ℝ} {m : Nat} {c0 : ℂ}
    {S F Φ : ℂ → ℂ} (A : SelectedArcData S ξ m c0) {g : ℕ} (hg1 : 1 ≤ g)
    (hΦ_an : AnalyticAt ℂ Φ 0) (hΦ0 : Φ 0 = 0)
    {ρ1c : ℝ} (hρ1c_pos : 0 < ρ1c)
    (hFpb : ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ1c →
        F (A.arc ρ) = (ρ : ℂ) ^ (-(m : ℤ)) *
          Φ ((ρ : ℂ) * Complex.exp ((A.angle : ℂ) * Complex.I)))
    (heqFreq : ∃ᶠ n in atTop, F (A.arc (A.rho (n + g))) = F (A.arc (A.rho n)))
    (hreFreq : ∃ᶠ n in atTop, (F (A.arc (A.rho n))).re = 0)
    (hΩconn : IsPreconnected Ω) (hρ0 : 0 < ρ0) (hpd : puncturedDisc ξ ρ0 ⊆ Ω)
    (hF_an_Ω : AnalyticOnNhd ℂ F Ω)
    (hFconst_contra : ∀ c' : ℂ, c'.re = 0 → Set.EqOn F (fun _ => c') Ω → False) :
    False := by
  classical
  set e : ℂ := Complex.exp ((A.angle : ℂ) * Complex.I) with he_def
  have he_ne : e ≠ 0 := by rw [he_def]; exact Complex.exp_ne_zero _
  have htend_ρe : Tendsto (fun ρ : ℝ => (ρ : ℂ) * e) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h1 : Tendsto (fun ρ : ℝ => (ρ : ℂ) * e) (nhds 0) (nhds ((0 : ℂ) * e)) :=
      (Complex.continuous_ofReal.tendsto 0).mul_const e
    simpa using h1.mono_left nhdsWithin_le_nhds
  have hle : ∀ᶠ ρ in nhdsWithin (0 : ℝ) (Set.Ioi 0), ρ ≤ ρ1c := by
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hρ1c_pos)] with ρ hρ using le_of_lt hρ
  by_cases hΦzero : ∀ᶠ w in nhds (0 : ℂ), Φ w = 0
  · -- `F ∘ arc ≡ 0` eventually, so `F ≡ 0` on `Ω`.
    have hFarc0 : ∀ᶠ ρ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)), F (A.arc ρ) = 0 := by
      filter_upwards [hle, htend_ρe.eventually hΦzero, self_mem_nhdsWithin]
        with ρ hρle hΦρ hρpos
      rw [hFpb ρ hρpos hρle, hΦρ, mul_zero]
    have hEqOn0 : Set.EqOn F 0 Ω :=
      eqOn_zero_of_eventually_arc_eq_zero A hΩconn
        hρ0 hpd hF_an_Ω hFarc0
    exact hFconst_contra 0 (by simp) hEqOn0
  · -- `Φ ≢ 0`: factor `Φ = w^κ·Φ̃`, get reduced form `ρ^{-ν}·Ψ_F`.
    obtain ⟨κ, Φt, hΦt_an, hΦt0, hΦfac⟩ :=
      hΦ_an.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hΦzero
    have hκ1 : 1 ≤ κ := by
      by_contra hc
      have hκ0 : κ = 0 := by omega
      have := hΦfac.self_of_nhds
      rw [hκ0, sub_zero, pow_zero, one_smul] at this
      rw [hΦ0] at this
      exact hΦt0 this.symm
    set ν : ℤ := (m : ℤ) - (κ : ℤ) with hν_def
    set Ψ_F : ℂ → ℂ := fun w => e ^ κ * Φt w with hΨF_def
    have hΨF_an : AnalyticAt ℂ Ψ_F 0 := analyticAt_const.mul hΦt_an
    have hΨF0 : Ψ_F 0 ≠ 0 := by
      rw [hΨF_def]; exact mul_ne_zero (pow_ne_zero _ he_ne) hΦt0
    -- reduced pullback on a right neighbourhood of 0
    have hΦfac_ρ : ∀ᶠ (ρ : ℝ) in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        Φ ((ρ : ℂ) * e) = ((ρ : ℂ) * e - 0) ^ κ • Φt ((ρ : ℂ) * e) := htend_ρe.eventually hΦfac
    have hFred : ∀ᶠ (ρ : ℝ) in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        F (A.arc ρ) = (ρ : ℂ) ^ (-ν) * Ψ_F ((ρ : ℂ) * e) := by
      filter_upwards [hΦfac_ρ, hle, self_mem_nhdsWithin] with ρ hΦρ hρle hρpos
      have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast (Set.mem_Ioi.1 hρpos).ne'
      rw [hFpb ρ (Set.mem_Ioi.1 hρpos) hρle, hΦρ, sub_zero, smul_eq_mul, mul_pow]
      have hpowρ : (ρ : ℂ) ^ (-(m : ℤ)) * (ρ : ℂ) ^ κ = (ρ : ℂ) ^ (-ν) := by
        rw [← zpow_natCast (ρ : ℂ) κ, ← zpow_add₀ hρc]; congr 1; rw [hν_def]; ring
      rw [hΨF_def]
      calc (ρ : ℂ) ^ (-(m : ℤ)) * ((ρ : ℂ) ^ κ * e ^ κ * Φt ((ρ : ℂ) * e))
            = ((ρ : ℂ) ^ (-(m : ℤ)) * (ρ : ℂ) ^ κ) * (e ^ κ * Φt ((ρ : ℂ) * e)) := by ring
        _ = (ρ : ℂ) ^ (-ν) * (e ^ κ * Φt ((ρ : ℂ) * e)) := by rw [hpowρ]
    have hred_n : ∀ᶠ n in atTop,
        F (A.arc (A.rho n)) = (A.rho n : ℂ) ^ (-ν) * Ψ_F ((A.rho n : ℂ) * e) :=
      A.rho_tendsto_zero.eventually hFred
    have hred_ng : ∀ᶠ n in atTop,
        F (A.arc (A.rho (n + g)))
          = (A.rho (n + g) : ℂ) ^ (-ν) * Ψ_F ((A.rho (n + g) : ℂ) * e) :=
      (A.rho_tendsto_zero.comp (tendsto_add_atTop_nat g)).eventually hFred
    have heqFreq_red : ∃ᶠ n in atTop,
        (A.rho (n + g) : ℂ) ^ (-ν) * Ψ_F ((A.rho (n + g) : ℂ) * e)
          = (A.rho n : ℂ) ^ (-ν) * Ψ_F ((A.rho n : ℂ) * e) := by
      refine (heqFreq.and_eventually (hred_n.and hred_ng)).mono (fun n hn => ?_)
      obtain ⟨heqn, hrn, hrng⟩ := hn
      rw [← hrng, ← hrn]; exact heqn
    by_cases hν : ν = 0
    · -- `ν = 0`: real-analytic constancy + identity theorem.
      have heqFreq_red_ν0 : ∃ᶠ n in atTop,
          Ψ_F ((A.rho (n + g) : ℂ) * e) = Ψ_F ((A.rho n : ℂ) * e) := by
        refine heqFreq_red.mono (fun n hn => ?_)
        rwa [hν, neg_zero, zpow_zero, one_mul, zpow_zero, one_mul] at hn
      have hreFreq_red : ∃ᶠ n in atTop, (Ψ_F ((A.rho n : ℂ) * e)).re = 0 := by
        refine (hreFreq.and_eventually hred_n).mono (fun n hn => ?_)
        obtain ⟨hre_n, hrn⟩ := hn
        rw [hrn, hν, neg_zero, zpow_zero, one_mul] at hre_n
        exact hre_n
      obtain ⟨cval, hcval_re, hcval_ev⟩ :=
        reduced_const_of_re_zero_and_eq A hg1 hΨF_an hreFreq_red heqFreq_red_ν0
      have hFmc0 : ∀ᶠ ρ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
          (fun z => F z - cval) (A.arc ρ) = 0 := by
        filter_upwards [hFred, hcval_ev] with ρ hFρ hcρ
        show F (A.arc ρ) - cval = 0
        rw [hFρ, hν, neg_zero, zpow_zero, one_mul, hcρ, sub_self]
      have hFmc_an : AnalyticOnNhd ℂ (fun z => F z - cval) Ω :=
        fun z hz => (hF_an_Ω z hz).sub analyticAt_const
      have hEqOnc : Set.EqOn (fun z => F z - cval) 0 Ω :=
        eqOn_zero_of_eventually_arc_eq_zero A hΩconn
          hρ0 hpd hFmc_an hFmc0
      exact hFconst_contra cval hcval_re
        (fun z hz => sub_eq_zero.1 (hEqOnc hz))
    · -- `ν ≠ 0`: Rolle forces the leading bracket to vanish, contradiction.
      exact hΨF0 (bracket_zero_of_rolle_of_frequently_eq A hg1 hν hΨF_an heqFreq_red)

set_option maxHeartbeats 4000000 in
/-- **No recurring collision** (`no_recurring_collision` — the `lem:window-avoidance`
core).  A single sibling `c` colliding with `Π` at both ends of a fixed bounded
gap `g` for infinitely many selected indices is impossible.  Composes the endgame
helpers: the reduced pullback `F = H_{c+1} − ρ̂·H_0` has arc form `ρ^{-m}·Φ`
(`Φ 0 = 0`); `reduced_increment_tendsto_zero` + the `Π`/selected lattice
(`eventuallyEq_of_tendsto_intMul`) force `F(σ_{n+g}) = F(σ_n)` frequently; then the
analytic-order factorization of `Φ` gives a reduced form `ρ^{-ν}·Ψ_F`
(`Ψ_F 0 ≠ 0`, `ν ≤ m−1`), refuted for `ν ≠ 0` by `bracket_zero_of_rolle_of_frequently_eq`
and for `ν = 0` by `reduced_const_of_re_zero_and_eq` + the identity theorem. -/
theorem no_recurring_collision {Ω : Set ℂ} {ξ : ℂ} {ρ0 : ℝ} {K m : Nat} {c0 : ℂ}
    {H : Fin (K + 1) -> ℂ -> ℂ}
    (hhyp : SiblingAvoidanceHypotheses Ω ξ ρ0 H) (hm : 1 ≤ m)
    (hNF : LaurentNormalFormAt (H 0) ξ (m : ℤ) c0)
    (A : SelectedArcData (H 0) ξ m c0)
    (c : Fin K) {μ : ℤ} {cc : ℂ} (hμle : μ ≤ (m : ℤ))
    (hNFc : LaurentNormalFormAt (H c.succ) ξ μ cc)
    {g : ℕ} (hg1 : 1 ≤ g)
    (hB : {n : ℕ | H c.succ (A.arc (A.rho n)) ∈ Pi ∧
        H c.succ (A.arc (A.rho (n + g))) ∈ Pi}.Infinite) :
    False := by
  classical
  have hc0 : c0 ≠ 0 := hNF.coeff_ne_zero
  have hnc0 : (0 : ℝ) < ‖c0‖ := norm_pos_iff.mpr hc0
  set e : ℂ := Complex.exp ((A.angle : ℂ) * Complex.I) with he_def
  have he_ne : e ≠ 0 := by rw [he_def]; exact Complex.exp_ne_zero _
  -- Selected leading arc coefficient `d0` and its reality.
  set d0 : ℂ := (A.sign : ℂ) * Complex.I * (‖c0‖ : ℂ) with hd0
  -- Sibling arc pullback.
  obtain ⟨Ψc, hΨc_an, hΨc0, ρ1c, hρ1c_pos, hρ1c_le, hGpb⟩ := arc_pullback_analytic A hNFc
  -- Frequently the sibling lands in `Π` along the selected arc.
  have hsub : {n : ℕ | H c.succ (A.arc (A.rho n)) ∈ Pi ∧
      H c.succ (A.arc (A.rho (n + g))) ∈ Pi}
      ⊆ {n : ℕ | H c.succ (A.arc (A.rho n)) ∈ Pi} := fun n hn => hn.1
  have hfreqPi : ∃ᶠ n in atTop, H c.succ (A.arc (A.rho n)) ∈ Pi :=
    Nat.frequently_atTop_iff_infinite.mpr (hB.mono hsub)
  have hd_re : (Ψc 0).re = 0 :=
    re_bracket_zero_eq_zero_of_frequently_mem_Pi A hΨc_an hρ1c_pos hGpb hfreqPi
  -- The real ratio `ρ̂`.
  set rhat : ℝ := if μ = (m : ℤ) then (Ψc 0).im / ((A.sign : ℝ) * ‖c0‖) else 0 with hrhat
  -- `ρ̂·d0 = Ψc 0` in the `μ = m` case.
  have hsz : A.sign ≠ 0 := by rintro h; have := A.sign_sq; rw [h] at this; simp at this
  have hsgc : (A.sign : ℂ) ≠ 0 := by exact_mod_cast hsz
  have hn0c : (‖c0‖ : ℂ) ≠ 0 := by exact_mod_cast hnc0.ne'
  have hsign_ne : (A.sign : ℝ) * ‖c0‖ ≠ 0 := by
    have : (A.sign : ℝ) ≠ 0 := by exact_mod_cast hsz
    positivity
  set k : ℕ := ((m : ℤ) - μ).toNat with hk_def
  have hk_cast : ((k : ℤ)) = (m : ℤ) - μ := Int.toNat_of_nonneg (by omega)
  -- The reduced bracket `Φ` with `Φ 0 = 0`.
  set Φ : ℂ → ℂ := fun w =>
      Complex.exp (-((k : ℕ) : ℂ) * (A.angle : ℂ) * Complex.I) * w ^ k * Ψc w
        - (rhat : ℂ) * d0 with hΦ_def
  have hΦ_an : AnalyticAt ℂ Φ 0 :=
    ((analyticAt_const.mul (analyticAt_id.pow k)).mul hΨc_an).sub analyticAt_const
  have hΦ0 : Φ 0 = 0 := by
    rw [hΦ_def]
    by_cases hμm : μ = (m : ℤ)
    · have hk0 : k = 0 := by rw [hk_def, hμm]; simp
      have hrhat_val : (rhat : ℂ) * d0 = Ψc 0 := by
        rw [hrhat, if_pos hμm, hd0]
        refine Complex.ext ?_ ?_
        · simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im]
          rw [hd_re]; ring
        · simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im]
          field_simp
          ring
      simp only [hk0, pow_zero, mul_one, Nat.cast_zero]
      rw [show (-(0 : ℂ) * (A.angle : ℂ) * Complex.I) = 0 by ring, Complex.exp_zero, one_mul,
        hrhat_val, sub_self]
    · have hk1 : 1 ≤ k := by rw [hk_def]; omega
      have hrhat0 : rhat = 0 := by rw [hrhat, if_neg hμm]
      simp [hrhat0, zero_pow (by omega : k ≠ 0)]
  -- Freeze the `if`-body of `rhat` and the `.toNat` body of `k`: past this point they
  -- are only used opaquely (via `hk_cast`), so keep `whnf` from unfolding them.
  clear_value rhat k
  -- The arc pullback of `F = H_{c+1} − ρ̂ H_0` in reduced `ρ^{-m}·Φ` form.
  set F : ℂ → ℂ := fun z => H c.succ z - (rhat : ℂ) * H 0 z with hF_def
  have hFpb : ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ1c →
      F (A.arc ρ) = (ρ : ℂ) ^ (-(m : ℤ)) * Φ ((ρ : ℂ) * e) := by
    intro ρ hρ hρle
    have hG := hGpb ρ hρ hρle
    have hSv := A.arc_value_exact ρ hρ (le_trans hρle hρ1c_le)
    have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
    show H c.succ (A.arc ρ) - (rhat : ℂ) * H 0 (A.arc ρ)
        = (ρ : ℂ) ^ (-(m : ℤ)) * Φ ((ρ : ℂ) * e)
    rw [hG, hSv, hΦ_def]
    have hepow : ((ρ : ℂ) * e) ^ k = (ρ : ℂ) ^ k * e ^ k := mul_pow _ _ _
    have hek : e ^ k = Complex.exp (((k : ℕ) : ℂ) * (A.angle : ℂ) * Complex.I) := by
      rw [he_def, ← Complex.exp_nat_mul]; congr 1; ring
    have hexpcancel :
        Complex.exp (-((k : ℕ) : ℂ) * (A.angle : ℂ) * Complex.I) * e ^ k = 1 := by
      rw [hek, ← Complex.exp_add]
      rw [show (-((k : ℕ) : ℂ) * (A.angle : ℂ) * Complex.I
          + ((k : ℕ) : ℂ) * (A.angle : ℂ) * Complex.I) = 0 by ring, Complex.exp_zero]
    have hzpow : (ρ : ℂ) ^ (-(m : ℤ)) * (ρ : ℂ) ^ k = (ρ : ℂ) ^ (-μ) := by
      rw [← zpow_natCast (ρ : ℂ) k, ← zpow_add₀ hρc]
      congr 1; omega
    -- expand the RHS
    rw [mul_sub]
    congr 1
    · rw [hepow]
      have hreassoc : (ρ : ℂ) ^ (-(m : ℤ)) *
              (Complex.exp (-((k : ℕ) : ℂ) * (A.angle : ℂ) * Complex.I) *
                ((ρ : ℂ) ^ k * e ^ k) * Ψc ((ρ : ℂ) * e))
            = ((ρ : ℂ) ^ (-(m : ℤ)) * (ρ : ℂ) ^ k) *
                (Complex.exp (-((k : ℕ) : ℂ) * (A.angle : ℂ) * Complex.I) * e ^ k) *
                Ψc ((ρ : ℂ) * e) := by ring
      rw [hreassoc, hzpow, hexpcancel]; ring
    · rw [hd0]; ring
  -- Freeze the (nested) bodies of `d0` and `Φ`: `hΦ_an`/`hΦ0`/`hFpb` are established and
  -- everything downstream (including the final `no_recurring_collision_endgame` application)
  -- treats `Φ` abstractly.  Keeping these opaque prevents `whnf` from unfolding the large
  -- `Φ = exp·w^k·Ψc − rhat·d0` term.  (`e` must keep its body for the endgame's defeq check.)
  clear_value d0 Φ
  -- Increment along the gap tends to 0.
  have hrho0 : Tendsto (fun n => A.rho n) atTop (nhds 0) :=
    A.rho_tendsto_zero.mono_right nhdsWithin_le_nhds
  have hev_le : ∀ᶠ n in atTop, A.rho n ≤ ρ1c := by
    filter_upwards [hrho0 (Iio_mem_nhds hρ1c_pos)] with n hn using le_of_lt hn
  have hFinc0 : Tendsto (fun n : ℕ => F (A.arc (A.rho (n + g))) - F (A.arc (A.rho n)))
      atTop (nhds 0) := by
    have hbase := reduced_increment_tendsto_zero A hm hc0 hΦ_an hΦ0 g
    refine hbase.congr' ?_
    filter_upwards [hev_le] with n hn
    have hng : A.rho (n + g) ≤ ρ1c :=
      le_trans (A.rho_strictAnti.antitone (Nat.le_add_right n g)) hn
    rw [hFpb (A.rho (n + g)) (A.rho_pos _) hng, hFpb (A.rho n) (A.rho_pos _) hn]
  -- Lattice: `F(σ_{n+g}) = F(σ_n)` frequently.
  have hcol_freq : ∃ᶠ n in atTop, H c.succ (A.arc (A.rho n)) ∈ Pi ∧
      H c.succ (A.arc (A.rho (n + g))) ∈ Pi :=
    Nat.frequently_atTop_iff_infinite.mpr hB
  obtain ⟨φ, hφ_mono, hφ⟩ := extraction_of_frequently_atTop hcol_freq
  have hkint : ∀ j : ℕ, ∃ q : ℤ,
      H c.succ (A.arc (A.rho (φ j + g))) - H c.succ (A.arc (A.rho (φ j)))
        = (q : ℂ) * (2 * Real.pi) * Complex.I := by
    intro j
    obtain ⟨q, hq⟩ := Pi_sub_mem_two_pi (hφ j).2 (hφ j).1
    exact ⟨q, by rw [hq]; ring⟩
  choose kk hkk using hkint
  set Lc : ℂ := (rhat : ℂ) * ((A.sign : ℂ) * (2 * (g : ℂ)) * (Real.pi : ℂ) * Complex.I) with hLc
  have hwn : ∀ j : ℕ,
      (kk j : ℂ) * (2 * Real.pi) * Complex.I
        = (F (A.arc (A.rho (φ j + g))) - F (A.arc (A.rho (φ j)))) + Lc := by
    intro j
    have hSinc := A.arc_value_exact -- unused direct; use selected_increment
    have hsel : H 0 (A.arc (A.rho (φ j + g))) - H 0 (A.arc (A.rho (φ j)))
        = (A.sign : ℂ) * (2 * (g : ℂ)) * (Real.pi : ℂ) * Complex.I := selected_increment A (φ j) g
    have hgi := hkk j
    rw [hF_def]
    simp only []
    rw [hLc]
    rw [← hgi]
    have : H c.succ (A.arc (A.rho (φ j + g))) - (rhat : ℂ) * H 0 (A.arc (A.rho (φ j + g)))
          - (H c.succ (A.arc (A.rho (φ j))) - (rhat : ℂ) * H 0 (A.arc (A.rho (φ j))))
        = (H c.succ (A.arc (A.rho (φ j + g))) - H c.succ (A.arc (A.rho (φ j))))
          - (rhat : ℂ) * (H 0 (A.arc (A.rho (φ j + g))) - H 0 (A.arc (A.rho (φ j)))) := by ring
    rw [this, hsel]; ring
  -- `Lc`'s body is no longer needed; freeze it so the `tendsto`/`positivity` steps below
  -- treat it opaquely.
  clear_value Lc
  have hwn_tend : Tendsto (fun j => (kk j : ℂ) * (2 * Real.pi) * Complex.I) atTop (nhds Lc) := by
    have h1 : Tendsto (fun j => F (A.arc (A.rho (φ j + g))) - F (A.arc (A.rho (φ j))))
        atTop (nhds 0) := hFinc0.comp hφ_mono.tendsto_atTop
    have := h1.add (tendsto_const_nhds (x := Lc))
    simpa [hwn] using this
  -- Apply the discreteness principle `eventuallyEq_of_tendsto_intMul`.  Its lattice
  -- generator is a *single* real coercion `(a : ℂ)`, whereas `hwn_tend` carries the
  -- constant as the `ℂ`-level product `2 * ↑Real.pi`.  Applying the lemma directly forces
  -- the elaborator to solve `↑?a =?= 2 * ↑Real.pi` by `whnf`, which unfolds `Real.pi`'s
  -- real-arithmetic definition without bound and exhausts the heartbeat budget.  Rewrite
  -- the constant into the `↑(2 * Real.pi)` form and fix `a := 2 * Real.pi` explicitly so the
  -- unification is purely syntactic.
  have hcast : ((2 * Real.pi : ℝ) : ℂ) = 2 * Real.pi := by push_cast; ring
  have hwn_tend' : Tendsto (fun j => (kk j : ℂ) * ((2 * Real.pi : ℝ) : ℂ) * Complex.I)
      atTop (nhds Lc) := by simpa only [← hcast] using hwn_tend
  have hkk0 : ∀ᶠ j in atTop, (kk j : ℂ) * (2 * Real.pi) * Complex.I = Lc := by
    have h := eventuallyEq_of_tendsto_intMul (a := 2 * Real.pi) (by positivity) hwn_tend'
    simpa only [hcast] using h
  have heqFreq : ∃ᶠ n in atTop,
      F (A.arc (A.rho (n + g))) = F (A.arc (A.rho n)) := by
    have hev : ∀ᶠ j in atTop, F (A.arc (A.rho (φ j + g))) = F (A.arc (A.rho (φ j))) := by
      filter_upwards [hkk0] with j hj
      have := (hwn j).symm
      rw [hj] at this
      have hzero : F (A.arc (A.rho (φ j + g))) - F (A.arc (A.rho (φ j))) = 0 := by
        have := this; linear_combination this
      exact sub_eq_zero.1 hzero
    -- push the eventual equality along φ to a frequent one
    rw [Nat.frequently_atTop_iff_infinite]
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    refine Set.infinite_of_injective_forall_mem (f := fun j => φ (N + j)) ?_ ?_
    · intro a b hab
      have := hφ_mono.injective hab
      omega
    · intro j
      exact hN (N + j) (by omega)
  -- Re part vanishes frequently.
  have hreFreq : ∃ᶠ n in atTop, (F (A.arc (A.rho n))).re = 0 := by
    refine hfreqPi.mono (fun n hn => ?_)
    have hGre : (H c.succ (A.arc (A.rho n))).re = 0 := Pi_re_eq_zero hn
    have hSre : (H 0 (A.arc (A.rho n))).re = 0 := Pi_re_eq_zero (A.sigma_mem_pi n)
    rw [hF_def]
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hGre, hSre]
    simp
  -- Endgame: F ≡ const contradiction helper.
  obtain ⟨b, hb0, hbval⟩ := hhyp.common_real_value
  have h0mem : (0 : ℂ) ∈ Ω := hhyp.nonneg_subset ⟨0, le_refl 0, by simp⟩
  have hFconst_contra : ∀ c' : ℂ, c'.re = 0 → Set.EqOn F (fun _ => c') Ω → False := by
    intro c' hc're hEqOn
    have hF0 : F (0 : ℂ) = c' := hEqOn h0mem
    have hFval : F (0 : ℂ) = (b : ℂ) - (rhat : ℂ) * (b : ℂ) := by
      rw [hF_def]; simp only []; rw [hbval c.succ, hbval 0]
    have hc'real : c' = ((b : ℂ) - (rhat : ℂ) * (b : ℂ)) := by rw [← hF0, hFval]
    have hc'im : c'.im = 0 := by rw [hc'real]; push_cast; simp
    have hc'0 : c' = 0 := Complex.ext hc're hc'im
    have hrhat1 : rhat = 1 := by
      have : (b : ℂ) - (rhat : ℂ) * (b : ℂ) = 0 := by rw [← hFval, hF0, hc'0]
      have hb0c : (b : ℂ) ≠ 0 := by exact_mod_cast hb0
      have : (b : ℂ) * (1 - (rhat : ℂ)) = 0 := by ring_nf; linear_combination this
      have hrc : (1 : ℂ) - (rhat : ℂ) = 0 := by
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h hb0c
        · exact h
      have : (rhat : ℂ) = 1 := by linear_combination -hrc
      exact_mod_cast this
    have hEqGS : Set.EqOn (H c.succ) (H 0) Ω := by
      intro z hz
      have := hEqOn hz
      rw [hF_def] at this
      simp only [hc'0, hrhat1, Complex.ofReal_one, one_mul] at this
      linear_combination this
    exact hhyp.sibling_not_identical c hEqGS
  -- Analyticity of `F` on `Ω`, then delegate to the endgame lemma.
  have hF_an_Ω : AnalyticOnNhd ℂ F Ω := fun z hz =>
    ((hhyp.analytic_on_omega c.succ) z hz).sub
      (analyticAt_const.mul ((hhyp.analytic_on_omega 0) z hz))
  exact no_recurring_collision_endgame A hg1 hΦ_an hΦ0 hρ1c_pos hFpb heqFreq hreFreq
    hhyp.omega_domain.isPreconnected hhyp.radius_pos hhyp.puncturedDisc_subset hF_an_Ω
    hFconst_contra

/-- **K06B.C6 / K04E.lem-window-avoidance**.  Sequence-window avoidance from the
selected normal form, arc data and the sibling exact-order bounds.  This is the
`lem:window-avoidance` conclusion assembled from the endgame helpers via
`no_recurring_collision`. -/
theorem lem_window_avoidance {Ω : Set ℂ} {ξ : ℂ} {ρ0 : ℝ} {K m : Nat} {c0 : ℂ}
    {H : Fin (K + 1) -> ℂ -> ℂ}
    (hhyp : SiblingAvoidanceHypotheses Ω ξ ρ0 H) (hm : 1 ≤ m)
    (hNF : LaurentNormalFormAt (H 0) ξ (m : ℤ) c0)
    (A : SelectedArcData (H 0) ξ m c0)
    (hsib : ∀ c : Fin K, ∃ (μ : ℤ) (cc : ℂ),
      μ ≤ (m : ℤ) ∧ LaurentNormalFormAt (H c.succ) ξ μ cc) :
    SelectedSequenceWindowAvoidance ξ H := by
  apply selectedSequenceWindowAvoidance_of_arc_goodIndices A
  rcases Nat.eq_zero_or_pos K with hK0 | hKpos
  · subst hK0
    have huniv : {n : ℕ | ∀ c : Fin 0, H c.succ (A.arc (A.rho n)) ∉ Pi} = Set.univ := by
      ext n; simp
    rw [huniv]; exact Set.infinite_univ
  · by_contra hgood_fin
    obtain ⟨c, g, hg1, hgK, hBcol⟩ :=
      exists_recurring_sibling_collision hKpos (σ := fun n => A.arc (A.rho n)) hgood_fin
    obtain ⟨μ, cc, hμle, hNFc⟩ := hsib c
    exact no_recurring_collision hhyp hm hNF A c hμle hNFc hg1 hBcol

/-- Convenience form: derive the sibling exact-order normal forms from the
meromorphic-order upper bounds recorded in the hypotheses. -/
theorem lem_window_avoidance' {Ω : Set ℂ} {ξ : ℂ} {ρ0 : ℝ} {K m : Nat} {c0 : ℂ}
    {H : Fin (K + 1) -> ℂ -> ℂ}
    (hhyp : SiblingAvoidanceHypotheses Ω ξ ρ0 H) (hm : 1 ≤ m)
    (hNF : LaurentNormalFormAt (H 0) ξ (m : ℤ) c0)
    (A : SelectedArcData (H 0) ξ m c0)
    (hsib : ∀ c : Fin K, ∃ (μ : ℤ) (cc : ℂ),
      μ ≤ (m : ℤ) ∧ LaurentNormalFormAt (H c.succ) ξ μ cc) :
    SelectedSequenceWindowAvoidance ξ H :=
  lem_window_avoidance hhyp hm hNF A hsib

/-- **Option-B packaging**: the sibling-avoidance result record from the selected
normal form and arc package (now that `SelectedArcData.toArcStructureResult` is
available) together with the sibling exact-order bounds. -/
theorem siblingAvoidanceResult_of_normalForm {Ω : Set ℂ} {ξ : ℂ} {ρ0 : ℝ}
    {K m : Nat} {c0 : ℂ} {H : Fin (K + 1) -> ℂ -> ℂ}
    (hhyp : SiblingAvoidanceHypotheses Ω ξ ρ0 H) (hm : 1 ≤ m)
    (hNF : LaurentNormalFormAt (H 0) ξ (m : ℤ) c0)
    (A : SelectedArcData (H 0) ξ m c0)
    (hsib : ∀ c : Fin K, ∃ (μ : ℤ) (cc : ℂ),
      μ ≤ (m : ℤ) ∧ LaurentNormalFormAt (H c.succ) ξ μ cc) :
    SiblingAvoidanceResult Ω ξ ρ0 H :=
  siblingAvoidanceResult_of_arcStructure_sequenceWindow hhyp
    (A.toArcStructureResult hm)
    (lem_window_avoidance hhyp hm hNF A hsib)


end TransformerIdentifiability.NLayer.KHead
