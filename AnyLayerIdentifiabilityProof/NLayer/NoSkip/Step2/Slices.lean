import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Step2.SaturatedLimits
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Analytic.MultiQuadricRigidity

set_option autoImplicit false

open Matrix

namespace TransformerIdentifiability.NLayer.NoSkip

/-!
# Open dial boxes and multi-quadric probe slices
-/

noncomputable section

/-- Probe-pair slice of a restricted tuple-dial region at a fixed dial tuple. -/
def restrictedRegionProbeSlice {n k d : Nat} {theta : Params (n + 1) k d}
    {D : MultiDialSignRegion theta} (R : MultiDialRestrictedRegion D)
    (t : Fin k → Real) : Set (Vec d × Vec d) :=
  {wv | (wv, t) ∈ R.region}

/-- Geometric output consumed by fixed-dial multi-quadric rigidity: an open
dial box and, at every dial in it, an open `w` base with relatively open
nonempty slices in `H_w`. -/
structure MultiDialSliceData {n k d : Nat} {theta : Params (n + 1) k d}
    {D : MultiDialSignRegion theta} (R : MultiDialRestrictedRegion D) where
  dialBox : Set (Fin k → Real)
  dialBox_open : IsOpen dialBox
  dialBox_nonempty : dialBox.Nonempty
  slices : ∀ t, t ∈ dialBox →
    MultiQuadricSliceWitness (attentionMatrix theta 0)
      (restrictedRegionProbeSlice R t)

/-- Every nonempty chart-stable restricted region contains the product box
and slice family required by TeX Lemma `lem:ns-slices`. -/
theorem MultiDialRestrictedRegion.exists_multiDialSliceData
    {n k d : Nat} {theta : Params (n + 1) k d}
    {D : MultiDialSignRegion theta} (R : MultiDialRestrictedRegion D) :
    Nonempty (MultiDialSliceData R) := by
  classical
  rcases R.source_nonempty with ⟨x, hx⟩
  obtain ⟨eps, heps, hball⟩ := Metric.isOpen_iff.mp R.source_open x hx
  let W : Set (Vec d) := Metric.ball x.1.1 eps
  let Vhat : Set (AnchorFreeVec D.pivot) := Metric.ball x.1.2 eps
  let T : Set (Fin k → Real) := Metric.ball x.2 eps
  have hproduct : ∀ {w : Vec d} {vhat : AnchorFreeVec D.pivot}
      {t : Fin k → Real}, w ∈ W → vhat ∈ Vhat → t ∈ T →
      ((w, vhat), t) ∈ R.source := by
    intro w vhat t hw hv ht
    apply hball
    simp only [Metric.mem_ball, Prod.dist_eq, max_lt_iff] at hw hv ht ⊢
    exact ⟨⟨hw, hv⟩, ht⟩
  have hWopen : IsOpen W := Metric.isOpen_ball
  have hWne : W.Nonempty := ⟨x.1.1, Metric.mem_ball_self heps⟩
  have hTopen : IsOpen T := Metric.isOpen_ball
  have hTne : T.Nonempty := ⟨x.2, Metric.mem_ball_self heps⟩
  refine ⟨{
    dialBox := T
    dialBox_open := hTopen
    dialBox_nonempty := hTne
    slices := ?_ }⟩
  intro t ht
  let slice : Vec d → Set (Vec d) := fun w =>
    {v | v ∈ multiQuadricSlice (attentionMatrix theta 0) w ∧
      anchorDelete D.pivot v ∈ Vhat}
  refine {
    W := W
    W_open := hWopen
    W_nonempty := hWne
    slice := slice
    slice_nonempty := ?_
    slice_relativelyOpen := ?_
    slice_subset := ?_ }
  · intro w hw
    have hsrc : ((w, x.1.2), t) ∈ R.source :=
      hproduct hw (Metric.mem_ball_self heps) ht
    have hwdom : w ∈ anchorPivotDomain theta D.pivot :=
      D.ball_subset_domain (R.source_subset hsrc).1
    refine ⟨anchorGamma theta D.pivot w x.1.2, ?_⟩
    constructor
    · intro a
      simpa [multiQuadricForm, anchorRow_eq_dotProduct] using
        anchorRow_gamma_eq_zero theta D.pivot w x.1.2 hwdom a
    · rw [anchorDelete_gamma]
      exact Metric.mem_ball_self heps
  · intro w _hw
    refine ⟨(anchorDelete D.pivot) ⁻¹' Vhat,
      Metric.isOpen_ball.preimage (continuous_anchorDelete D.pivot), ?_⟩
    ext v
    simp [slice, and_comm]
  · intro w hw y hy
    rcases y with ⟨w', v⟩
    rcases hy with ⟨hw', hv⟩
    have hww : w' = w := by simpa using hw'
    subst w'
    have hsrc : ((w, anchorDelete D.pivot v), t) ∈ R.source :=
      hproduct hw hv.2 ht
    have hwdom : w ∈ anchorPivotDomain theta D.pivot :=
      D.ball_subset_domain (R.source_subset hsrc).1
    have hrows : ∀ a, anchorRow theta w a v = 0 := by
      intro a
      simpa [multiQuadricForm, anchorRow_eq_dotProduct] using hv.1 a
    have hgamma : anchorGamma theta D.pivot w (anchorDelete D.pivot v) = v :=
      anchorGamma_eq_of_delete_eq_of_anchorRows_eq_zero theta D.pivot w v
        (anchorDelete D.pivot v) hwdom rfl hrows
    change ((w, v), t) ∈ R.region
    rw [R.region_eq_image]
    refine ⟨((w, anchorDelete D.pivot v), t), hsrc, ?_⟩
    simp [multiSignChart, anchorChart, hgamma]

/-- Fixed-dial rigidity on every member of the extracted open dial box.  This
is the geometric NS144 step, parameterized only by the limit identity that
NS142 supplies. -/
theorem MultiDialSliceData.fixedDial_Xi1_eq_zero
    {n k d : Nat} {theta : Params (n + 1) k d}
    {D : MultiDialSignRegion theta} {R : MultiDialRestrictedRegion D}
    (S : MultiDialSliceData R)
    (Xi0 Xi1 : (Fin k → Real) → Matrix (Fin d) (Fin d) Real)
    (hidentity : ∀ t ∈ S.dialBox, ∀ w v : Vec d,
      ((w, v), t) ∈ R.region → Xi0 t *ᵥ v + Xi1 t *ᵥ w = 0) :
    ∀ t ∈ S.dialBox, Xi1 t = 0 := by
  intro t ht
  let W := S.slices t ht
  have hquad : restrictedRegionProbeSlice R t ⊆
      multiQuadric (attentionMatrix theta 0) := by
    intro wv hwv
    have hDmem := R.region_subset hwv
    have hslab := D.region_subset_slab hDmem
    intro a
    simpa [multiQuadricForm, anchorRow_eq_dotProduct] using hslab.1 a
  exact (multiQuadricRigidity_of_witness W hquad (Xi0 t) (Xi1 t)
    (fun w v hwv => hidentity t ht w v hwv)).1

end

end TransformerIdentifiability.NLayer.NoSkip
