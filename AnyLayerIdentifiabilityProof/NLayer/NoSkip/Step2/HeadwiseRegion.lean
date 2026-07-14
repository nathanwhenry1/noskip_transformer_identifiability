import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Step2.HeadwiseDialLimits

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer.NoSkip

noncomputable section

/-- A chart-stable restriction of one repaired headwise sign region. -/
structure HeadwiseRestrictedRegion {n k d : Nat}
    {theta : Params (n + 1) k d} {h : Fin k}
    (D : HeadwiseSignRegion theta h) where
  source : Set (KHead.SignRegionChartInput d D.pivot)
  region : Set (HeadwiseSignPoint d)
  source_subset : source ⊆ D.source
  source_nonempty : source.Nonempty
  source_open : IsOpen source
  source_preconnected : IsPreconnected source
  region_eq_image :
    region = KHead.signRegionChart theta h D.pivot '' source

namespace HeadwiseRestrictedRegion

variable {n k d : Nat} {theta : Params (n + 1) k d}
  {h : Fin k} {D : HeadwiseSignRegion theta h}

noncomputable def full (D : HeadwiseSignRegion theta h) :
    HeadwiseRestrictedRegion D where
  source := D.source
  region := D.region
  source_subset := Set.Subset.rfl
  source_nonempty := by
    have hp := D.center_mem_region
    rcases D.chart_bijective.2.2 hp with ⟨x, hx, _⟩
    exact ⟨x, hx⟩
  source_open := D.source_open
  source_preconnected := D.source_convex.isPreconnected
  region_eq_image := D.region_eq_chart_image

theorem region_subset (R : HeadwiseRestrictedRegion D) :
    R.region ⊆ D.region := by
  rw [R.region_eq_image, D.region_eq_chart_image]
  exact Set.image_mono R.source_subset

theorem nonempty (R : HeadwiseRestrictedRegion D) : R.region.Nonempty := by
  rcases R.source_nonempty with ⟨x, hx⟩
  exact ⟨KHead.signRegionChart theta h D.pivot x,
    by rw [R.region_eq_image]; exact ⟨x, hx, rfl⟩⟩

theorem isPreconnected (R : HeadwiseRestrictedRegion D) :
    IsPreconnected R.region := by
  rw [R.region_eq_image]
  exact R.source_preconnected.image _
    ((KHead.continuousOn_signRegionChart theta h D.pivot).mono
      (fun x hx => D.source_subset_domain (R.source_subset hx)))

theorem chart_projection_inverse (R : HeadwiseRestrictedRegion D) :
    ∀ p ∈ R.region,
      KHead.signRegionChart theta h D.pivot
        (KHead.signRegionProjection D.pivot p) = p := by
  intro p hp
  exact D.chart_projection_inverse p (R.region_subset hp)

theorem chart_bijOn (R : HeadwiseRestrictedRegion D) :
    Set.BijOn (KHead.signRegionChart theta h D.pivot) R.source R.region := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [R.region_eq_image]
    exact ⟨x, hx, rfl⟩
  · intro x hx y hy hxy
    have heq := congrArg (KHead.signRegionProjection D.pivot) hxy
    simpa using heq
  · intro p hp
    rwa [R.region_eq_image] at hp

theorem region_eq_base_inter_projection (R : HeadwiseRestrictedRegion D) :
    R.region = D.region ∩
      (KHead.signRegionProjection D.pivot) ⁻¹' R.source := by
  ext p
  constructor
  · intro hp
    refine ⟨R.region_subset hp, ?_⟩
    rw [R.region_eq_image] at hp
    rcases hp with ⟨x, hx, rfl⟩
    simpa using hx
  · rintro ⟨hpD, hproj⟩
    rw [R.region_eq_image]
    exact ⟨KHead.signRegionProjection D.pivot p, hproj,
      D.chart_projection_inverse p hpD⟩

theorem relativelyOpen (R : HeadwiseRestrictedRegion D) :
    ∃ O : Set (HeadwiseSignPoint d), IsOpen O ∧
      R.region = KHead.signRegionSlab theta h ∩ O := by
  let ambient :=
    KHead.signRegionAmbientBox D.pivot D.w0 D.vHat D.t0 D.rho
  let O := ambient ∩ (KHead.signRegionProjection D.pivot) ⁻¹' R.source
  have hO : IsOpen O :=
    (KHead.isOpen_signRegionAmbientBox D.pivot D.w0 D.vHat D.t0 D.rho).inter
      (R.source_open.preimage
        (KHead.continuous_signRegionProjection D.pivot))
  refine ⟨O, hO, ?_⟩
  rw [R.region_eq_base_inter_projection, D.ambient_identity]
  ext p
  simp only [Set.mem_inter_iff, Set.mem_preimage, O, ambient]
  tauto

theorem w_ne_zero (R : HeadwiseRestrictedRegion D)
    {p : HeadwiseSignPoint d} (hp : p ∈ R.region) : p.1.1 ≠ 0 := by
  have hpD := R.region_subset hp
  have hmem := hpD
  rw [D.ambient_identity] at hmem
  have hkappa := D.w_ball_subset_chart hmem.2.1
  intro hw
  apply hkappa
  simp [KHead.signRegionKappa, hw]

/-- The chart restriction is relatively open in the nonsingular quadric
cylinder used by the model-neutral one-quadric topology API. -/
theorem relativelyOpenIn_quadricPatchCylinder
    (R : HeadwiseRestrictedRegion D) :
    KHead.RelativelyOpenIn R.region
      (KHead.quadricPatchCylinder (attentionMatrix theta 0) h) := by
  rcases R.relativelyOpen with ⟨O, hO, hRO⟩
  refine ⟨O, hO, ?_⟩
  ext p
  constructor
  · intro hp
    have hpR : p ∈ R.region := hp
    rw [hRO] at hp
    refine ⟨hp.2, ?_⟩
    rcases hp.1 with ⟨hq, ht⟩
    exact ⟨⟨by simpa [KHead.firstHeadQuadric, KHead.firstHeadSlope] using hq,
      R.w_ne_zero hpR⟩, ht.1, ht.2⟩
  · rintro ⟨hpO, hcyl⟩
    rw [hRO]
    rcases hcyl with ⟨⟨hq, _hw⟩, ht0, ht1⟩
    exact ⟨⟨by simpa [KHead.firstHeadQuadric, KHead.firstHeadSlope] using hq,
      ht0, ht1⟩, hpO⟩

theorem timeProjection_infinite (R : HeadwiseRestrictedRegion D) :
    (KHead.timeProjection R.region).Infinite :=
  KHead.timeProjection_infinite_of_nonempty_relativelyOpenIn_quadricPatchCylinder
    R.nonempty R.relativelyOpenIn_quadricPatchCylinder

theorem timeSlice_relativelyOpen (R : HeadwiseRestrictedRegion D) (t : Real) :
    KHead.RelativelyOpenIn (KHead.timeSlice R.region t)
      (KHead.quadricPatch (attentionMatrix theta 0) h) :=
  KHead.timeSlice_relativelyOpenIn_of_relativelyOpenIn_quadricPatchCylinder
    t R.relativelyOpenIn_quadricPatchCylinder

theorem exists_restrict_ambientOpen (R : HeadwiseRestrictedRegion D)
    {O : Set (HeadwiseSignPoint d)} (hO : IsOpen O)
    {p : HeadwiseSignPoint d} (hpR : p ∈ R.region) (hpO : p ∈ O) :
    ∃ R' : HeadwiseRestrictedRegion D,
      p ∈ R'.region ∧ R'.region ⊆ R.region ∩ O := by
  let x := KHead.signRegionProjection D.pivot p
  have hxR : x ∈ R.source := by
    rw [R.region_eq_base_inter_projection] at hpR
    exact hpR.2
  have hpchart : KHead.signRegionChart theta h D.pivot x = p :=
    R.chart_projection_inverse p hpR
  have hxdom : x ∈ KHead.signRegionChartDomain theta h D.pivot :=
    D.source_subset_domain (R.source_subset hxR)
  let S : Set (KHead.SignRegionChartInput d D.pivot) :=
    R.source ∩ (KHead.signRegionChartDomain theta h D.pivot ∩
      (KHead.signRegionChart theta h D.pivot) ⁻¹' O)
  have hchartOpen : IsOpen
      (KHead.signRegionChartDomain theta h D.pivot ∩
        (KHead.signRegionChart theta h D.pivot) ⁻¹' O) :=
    (KHead.continuousOn_signRegionChart theta h D.pivot).isOpen_inter_preimage
      (KHead.isOpen_signRegionChartDomain theta h D.pivot) hO
  have hSopen : IsOpen S := R.source_open.inter hchartOpen
  have hxS : x ∈ S := ⟨hxR, hxdom, by simpa [hpchart] using hpO⟩
  obtain ⟨eps, heps, hball⟩ := Metric.isOpen_iff.mp hSopen x hxS
  let source' := Metric.ball x eps
  let region' := KHead.signRegionChart theta h D.pivot '' source'
  let R' : HeadwiseRestrictedRegion D := {
    source := source'
    region := region'
    source_subset := fun y hy => R.source_subset (hball hy).1
    source_nonempty := ⟨x, Metric.mem_ball_self heps⟩
    source_open := Metric.isOpen_ball
    source_preconnected := (convex_ball x eps).isPreconnected
    region_eq_image := rfl }
  refine ⟨R', ?_, ?_⟩
  · change p ∈ region'
    rw [← hpchart]
    exact ⟨x, Metric.mem_ball_self heps, rfl⟩
  · intro q hq
    change q ∈ region' at hq
    rcases hq with ⟨y, hy, rfl⟩
    have hyS := hball hy
    refine ⟨?_, hyS.2.2⟩
    rw [R.region_eq_image]
    exact ⟨y, hyS.1, rfl⟩

end HeadwiseRestrictedRegion

end

end TransformerIdentifiability.NLayer.NoSkip
