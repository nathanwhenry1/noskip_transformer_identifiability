import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Genericity.HeadwiseCertificate
import AnyLayerIdentifiabilityProof.NLayer.KHead.Genericity.AnchorCertificate

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.NoSkip

noncomputable section

/-! ## The repaired affine center -/

/-- Pin the distinguished anchor to zero and every off-head anchor and deeper
level to `-1`. -/
def headwisePinnedTarget {m k : Nat} (h : Fin k) : MultiDialRow m k → Real
  | Sum.inl a => if a = h then 0 else -1
  | Sum.inr _ => -1

@[simp] theorem headwisePinnedTarget_self {m k : Nat} (h : Fin k) :
    headwisePinnedTarget (m := m) h (MultiDialRow.anchor h) = 0 := by
  simp [headwisePinnedTarget, MultiDialRow.anchor]

@[simp] theorem headwisePinnedTarget_anchor_of_ne {m k : Nat} {h a : Fin k}
    (ha : a ≠ h) :
    headwisePinnedTarget (m := m) h (MultiDialRow.anchor a) = -1 := by
  simp [headwisePinnedTarget, MultiDialRow.anchor, ha]

@[simp] theorem headwisePinnedTarget_level {m k : Nat} (h : Fin k)
    (jb : LevelRowIndex m k) :
    headwisePinnedTarget h (MultiDialRow.level jb) = -1 :=
  rfl

/-- Minimum-norm solution of all repaired affine rows. -/
noncomputable def headwisePinnedCenter {n k d : Nat}
    (theta : Params (n + 1) k d) (h : Fin k) (t : Real) (w : Vec d) : Vec d :=
  let tuple := headwiseDialTuple h t
  let G := multiDialGradientMatrix theta tuple w
  let A : Matrix (MultiDialRow (n + 1) k) (MultiDialRow (n + 1) k) Real := Gᵀ * G
  G *ᵥ (A⁻¹ *ᵥ
    (headwisePinnedTarget h - multiDialConstantVector theta tuple w))

theorem multiDialRowVector_headwisePinnedCenter
    {n k d : Nat} (theta : Params (n + 1) k d) (h : Fin k)
    (t : Real) (w : Vec d)
    (hgram : multiDialGramDet theta (headwiseDialTuple h t) w ≠ 0) :
    multiDialRowVector theta (headwiseDialTuple h t) w
        (headwisePinnedCenter theta h t w) =
      headwisePinnedTarget h := by
  classical
  let tuple := headwiseDialTuple h t
  let G := multiDialGradientMatrix theta tuple w
  let A : Matrix (MultiDialRow (n + 1) k) (MultiDialRow (n + 1) k) Real := Gᵀ * G
  let y : MultiDialRow (n + 1) k → Real :=
    headwisePinnedTarget h - multiDialConstantVector theta tuple w
  have hA_det : A.det ≠ 0 := by
    simpa [multiDialGramDet, multiDialGramMatrix, G, A, tuple] using hgram
  have hA_unit : IsUnit A.det := hA_det.isUnit
  have hA_solve : A *ᵥ (A⁻¹ *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hA_unit,
      Matrix.one_mulVec]
  have hG_solve : Gᵀ *ᵥ headwisePinnedCenter theta h t w = y := by
    change Gᵀ *ᵥ (G *ᵥ (A⁻¹ *ᵥ y)) = y
    rw [Matrix.mulVec_mulVec]
    exact hA_solve
  rw [multiDialRowVector_eq_gradientMatrix_transpose_mulVec_add]
  change Gᵀ *ᵥ headwisePinnedCenter theta h t w +
      multiDialConstantVector theta tuple w = headwisePinnedTarget h
  rw [hG_solve]
  ext row
  simp [y]

theorem headwisePinnedCenter_anchor_self
    {n k d : Nat} (theta : Params (n + 1) k d) (h : Fin k)
    (t : Real) (w : Vec d)
    (hgram : multiDialGramDet theta (headwiseDialTuple h t) w ≠ 0) :
    anchorRow theta w h (headwisePinnedCenter theta h t w) = 0 := by
  have hx := congrFun
    (multiDialRowVector_headwisePinnedCenter theta h t w hgram)
    (MultiDialRow.anchor h)
  simpa [multiDialRowVector] using hx

theorem headwisePinnedCenter_anchor_off
    {n k d : Nat} (theta : Params (n + 1) k d) {h a : Fin k}
    (ha : a ≠ h) (t : Real) (w : Vec d)
    (hgram : multiDialGramDet theta (headwiseDialTuple h t) w ≠ 0) :
    anchorRow theta w a (headwisePinnedCenter theta h t w) = -1 := by
  have hx := congrFun
    (multiDialRowVector_headwisePinnedCenter theta h t w hgram)
    (MultiDialRow.anchor a)
  simpa [multiDialRowVector, ha] using hx

theorem headwisePinnedCenter_level
    {n k d : Nat} (theta : Params (n + 1) k d) (h : Fin k)
    (t : Real) (w : Vec d)
    (hgram : multiDialGramDet theta (headwiseDialTuple h t) w ≠ 0)
    (jb : LevelRowIndex (n + 1) k) :
    levelRow theta (headwiseDialTuple h t) w jb
        (headwisePinnedCenter theta h t w) = -1 := by
  have hx := congrFun
    (multiDialRowVector_headwisePinnedCenter theta h t w hgram)
    (MultiDialRow.level jb)
  simpa [multiDialRowVector] using hx

/-- The distinguished anchor gradient is nonzero at every certified point. -/
theorem headwise_anchorGradient_ne_zero_of_gramDet
    {n k d : Nat} (theta : Params (n + 1) k d) (h : Fin k)
    (t : Real) (w : Vec d)
    (hgram : multiDialGramDet theta (headwiseDialTuple h t) w ≠ 0) :
    anchorGradient theta w h ≠ 0 := by
  have hli := linearIndependent_multiDialRowGradient_of_gramDet_ne_zero
    theta (headwiseDialTuple h t) w hgram
  simpa using hli.ne_zero (MultiDialRow.anchor h)

/-- Select one actual ambient coordinate for the scalar quadric chart. -/
theorem exists_headwiseSignPivot_of_gramDet
    {n k d : Nat} (theta : Params (n + 1) k d) (h : Fin k)
    (t : Real) (w : Vec d)
    (hgram : multiDialGramDet theta (headwiseDialTuple h t) w ≠ 0) :
    ∃ pivot : Fin d, KHead.signRegionKappa theta h pivot w ≠ 0 := by
  classical
  have hgrad := headwise_anchorGradient_ne_zero_of_gramDet theta h t w hgram
  by_contra hnone
  apply hgrad
  funext i
  by_contra hi
  apply hnone
  exact ⟨i, by simpa [KHead.signRegionKappa, anchorGradient] using hi⟩

/-! ## The strict headwise sign locus -/

/-- Points of the repaired scalar sign region, written as `((w,v),t)`. -/
abbrev HeadwiseSignPoint (d : Nat) := KHead.SignRegionPoint d

/-- Off-head anchors and all deeper zero-frozen levels are the strict
inequalities retained by the repaired proof. -/
abbrev HeadwiseStrictIndex (n k : Nat) (h : Fin k) :=
  {a : Fin k // a ≠ h} ⊕ LevelRowIndex (n + 1) k

@[simp] theorem dialValueMatrix_headwiseDialTuple {n k d : Nat}
    (theta : Params (n + 1) k d) (h : Fin k) (t : Real) :
    dialValueMatrix theta (headwiseDialTuple h t) =
      t • valueMatrix theta 0 h := by
  simp [dialValueMatrix, headwiseDialTuple]

/-- Negated row value, so positivity means that the corresponding slope is
strictly negative. -/
noncomputable def headwiseStrictValue {n k d : Nat}
    (theta : Params (n + 1) k d) (h : Fin k) :
    HeadwiseStrictIndex n k h → HeadwiseSignPoint d → Real
  | Sum.inl a, p => -anchorRow theta p.1.1 a.1 p.1.2
  | Sum.inr jb, p =>
      -levelRow theta (headwiseDialTuple h p.2) p.1.1 jb p.1.2

/-- Ambient open locus where all off-head anchors and all target deeper
zero-frozen levels are negative. -/
def headwiseStrictPositiveSet {n k d : Nat}
    (theta : Params (n + 1) k d) (h : Fin k) :
    Set (HeadwiseSignPoint d) :=
  {p | ∀ idx : HeadwiseStrictIndex n k h, 0 < headwiseStrictValue theta h idx p}

theorem continuous_headwiseStrictValue {n k d : Nat}
    (theta : Params (n + 1) k d) (h : Fin k)
    (idx : HeadwiseStrictIndex n k h) :
    Continuous (headwiseStrictValue theta h idx) := by
  rcases idx with a | jb
  · change Continuous fun p : HeadwiseSignPoint d =>
      -anchorRow theta p.1.1 a.1 p.1.2
    apply Continuous.neg
    unfold anchorRow
    exact KHead.continuous_matrixBilin _
      (continuous_fst.comp continuous_fst)
      (continuous_snd.comp continuous_fst)
  · change Continuous fun p : HeadwiseSignPoint d =>
      -levelRow theta (headwiseDialTuple h p.2) p.1.1 jb p.1.2
    apply Continuous.neg
    unfold levelRow
    apply KHead.continuous_matrixBilin
    · dsimp only [zeroFrozenPrefixPoint]
      unfold dialContrast
      simp_rw [dialValueMatrix_headwiseDialTuple]
      fun_prop
    · dsimp only [zeroFrozenPrefixPoint]
      unfold dialRepeated
      simp_rw [dialValueMatrix_headwiseDialTuple]
      fun_prop

theorem isOpen_headwiseStrictPositiveSet {n k d : Nat}
    (theta : Params (n + 1) k d) (h : Fin k) :
    IsOpen (headwiseStrictPositiveSet theta h) :=
  KHead.isOpen_finite_strictPositiveSet (headwiseStrictValue theta h)
    (continuous_headwiseStrictValue theta h)

theorem headwisePinnedCenter_mem_strictPositiveSet
    {n k d : Nat} (theta : Params (n + 1) k d) (h : Fin k)
    (t : Real) (w : Vec d)
    (hgram : multiDialGramDet theta (headwiseDialTuple h t) w ≠ 0) :
    ((w, headwisePinnedCenter theta h t w), t) ∈
      headwiseStrictPositiveSet theta h := by
  intro idx
  rcases idx with a | jb
  · rw [headwiseStrictValue,
      headwisePinnedCenter_anchor_off theta a.2 t w hgram]
    norm_num
  · rw [headwiseStrictValue,
      headwisePinnedCenter_level theta h t w hgram jb]
    norm_num

/-! ## The single-pivot headwise region -/

/-- The complete target sign region for one distinguished first-layer head. -/
structure HeadwiseSignRegion {n k d : Nat}
    (theta : Params (n + 1) k d) (h : Fin k) where
  t0 : Real
  t0_mem_Ioo : t0 ∈ Set.Ioo (0 : Real) 1
  w0 : Vec d
  v0 : Vec d
  gram_ne_zero :
    multiDialGramDet theta (headwiseDialTuple h t0) w0 ≠ 0
  pivot : Fin d
  pivot_nonzero : KHead.signRegionKappa theta h pivot w0 ≠ 0
  vHat : KHead.DeletedVec d pivot
  vHat_eq : vHat = KHead.signRegionHat pivot v0
  rho : Real
  rho_pos : 0 < rho
  interval_subset_Ioo :
    Set.Ioo (t0 - rho) (t0 + rho) ⊆ Set.Ioo (0 : Real) 1
  w_ball_subset_chart :
    Metric.ball w0 rho ⊆
      {w | KHead.signRegionKappa theta h pivot w ≠ 0}
  source : Set (KHead.SignRegionChartInput d pivot)
  source_eq_box : source =
    KHead.signRegionSourceBox pivot w0 vHat t0 rho
  region : Set (HeadwiseSignPoint d)
  region_eq_chart_image :
    region = KHead.signRegionChart theta h pivot '' source
  ambient_identity :
    region = KHead.signRegionSlab theta h ∩
      KHead.signRegionAmbientBox pivot w0 vHat t0 rho
  center_chart :
    KHead.signRegionChart theta h pivot ((w0, vHat), t0) =
      ((w0, v0), t0)
  center_mem_region : ((w0, v0), t0) ∈ region
  source_open : IsOpen source
  source_convex : Convex Real source
  source_subset_domain : source ⊆
    KHead.signRegionChartDomain theta h pivot
  chart_bijective :
    Set.BijOn (KHead.signRegionChart theta h pivot) source region
  chart_projection_inverse :
    ∀ p ∈ region,
      KHead.signRegionChart theta h pivot
        (KHead.signRegionProjection pivot p) = p
  region_connected : IsPreconnected region
  strict_positive : region ⊆ headwiseStrictPositiveSet theta h

namespace HeadwiseSignRegion

variable {n k d : Nat} {theta : Params (n + 1) k d} {h : Fin k}

theorem nonempty (D : HeadwiseSignRegion theta h) : D.region.Nonempty :=
  ⟨((D.w0, D.v0), D.t0), D.center_mem_region⟩

theorem region_subset_slab (D : HeadwiseSignRegion theta h) :
    D.region ⊆ KHead.signRegionSlab theta h := by
  rw [D.ambient_identity]
  exact Set.inter_subset_left

theorem relativelyOpen (D : HeadwiseSignRegion theta h) :
    ∃ O : Set (HeadwiseSignPoint d), IsOpen O ∧
      D.region = KHead.signRegionSlab theta h ∩ O := by
  exact ⟨KHead.signRegionAmbientBox D.pivot D.w0 D.vHat D.t0 D.rho,
    KHead.isOpen_signRegionAmbientBox D.pivot D.w0 D.vHat D.t0 D.rho,
    D.ambient_identity⟩

theorem offHead_negative (D : HeadwiseSignRegion theta h)
    {p : HeadwiseSignPoint d} (hp : p ∈ D.region)
    {a : Fin k} (ha : a ≠ h) :
    anchorRow theta p.1.1 a p.1.2 < 0 := by
  have hs := D.strict_positive hp (Sum.inl ⟨a, ha⟩)
  simpa [headwiseStrictValue] using hs

theorem deeper_negative (D : HeadwiseSignRegion theta h)
    {p : HeadwiseSignPoint d} (hp : p ∈ D.region)
    (jb : LevelRowIndex (n + 1) k) :
    levelRow theta (headwiseDialTuple h p.2) p.1.1 jb p.1.2 < 0 := by
  have hs := D.strict_positive hp (Sum.inr jb)
  simpa [headwiseStrictValue] using hs

theorem anchorGradient_ne_zero (D : HeadwiseSignRegion theta h) :
    anchorGradient theta D.w0 h ≠ 0 :=
  headwise_anchorGradient_ne_zero_of_gramDet theta h D.t0 D.w0
    D.gram_ne_zero

end HeadwiseSignRegion

/-- The repaired headwise certificate produces a chart-stable scalar sign
region for every requested first-layer head. -/
theorem exists_headwiseSignRegion {n k d : Nat}
    (theta : Params (n + 1) k d) (hcert : HeadwiseDialCertificate theta)
    (h : Fin k) : Nonempty (HeadwiseSignRegion theta h) := by
  classical
  rcases hcert.exists_gramDet_ne_zero h with ⟨t0, ht0, w0, hgram⟩
  let v0 : Vec d := headwisePinnedCenter theta h t0 w0
  have hquad : matrixBilin (attentionMatrix theta 0 h) w0 v0 = 0 := by
    simpa [anchorRow] using
      headwisePinnedCenter_anchor_self theta h t0 w0 hgram
  have hstrict0 : ((w0, v0), t0) ∈ headwiseStrictPositiveSet theta h :=
    headwisePinnedCenter_mem_strictPositiveSet theta h t0 w0 hgram
  rcases exists_headwiseSignPivot_of_gramDet theta h t0 w0 hgram with
    ⟨pivot, hpivot⟩
  let vHat : KHead.DeletedVec d pivot := KHead.signRegionHat pivot v0
  let x0 : KHead.SignRegionChartInput d pivot := ((w0, vHat), t0)
  have hx0_domain : x0 ∈ KHead.signRegionChartDomain theta h pivot := by
    simpa [x0, KHead.signRegionChartDomain] using hpivot
  have hcenter_chart :
      KHead.signRegionChart theta h pivot x0 = ((w0, v0), t0) := by
    dsimp [x0, vHat]
    exact KHead.signRegionChart_projection_eq_of_mem_slab
      theta h pivot ((w0, v0), t0) hpivot hquad
  have hstrict_source_nhds :
      (KHead.signRegionChart theta h pivot) ⁻¹'
          headwiseStrictPositiveSet theta h ∈ nhds x0 := by
    have hcont : ContinuousAt (KHead.signRegionChart theta h pivot) x0 :=
      ((KHead.analyticOnNhd_signRegionChart theta h pivot) x0
        hx0_domain).continuousAt
    apply hcont.preimage_mem_nhds
    exact (isOpen_headwiseStrictPositiveSet theta h).mem_nhds
      (by simpa [hcenter_chart] using hstrict0)
  rcases Metric.mem_nhds_iff.mp hstrict_source_nhds with
    ⟨epsStrict, hepsStrict, hepsStrict_subset⟩
  have hwOpen : IsOpen
      {w : Vec d | KHead.signRegionKappa theta h pivot w ≠ 0} := by
    simpa using isOpen_ne.preimage
      (KHead.continuous_signRegionKappa theta h pivot)
  have hwNhd :
      {w : Vec d | KHead.signRegionKappa theta h pivot w ≠ 0} ∈ nhds w0 :=
    hwOpen.mem_nhds hpivot
  rcases Metric.mem_nhds_iff.mp hwNhd with
    ⟨epsW, hepsW, hepsW_subset⟩
  have htNhd : Set.Ioo (0 : Real) 1 ∈ nhds t0 :=
    isOpen_Ioo.mem_nhds ht0
  rcases Metric.mem_nhds_iff.mp htNhd with
    ⟨epsT, hepsT, hepsT_subset⟩
  let rho : Real := min epsStrict (min epsW epsT)
  have hrho : 0 < rho := lt_min hepsStrict (lt_min hepsW hepsT)
  have hrhoStrict : rho ≤ epsStrict := min_le_left _ _
  have hrhoW : rho ≤ epsW :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hrhoT : rho ≤ epsT :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have hinterval :
      Set.Ioo (t0 - rho) (t0 + rho) ⊆ Set.Ioo (0 : Real) 1 := by
    intro t ht
    apply hepsT_subset
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  have hwball : Metric.ball w0 rho ⊆
      {w | KHead.signRegionKappa theta h pivot w ≠ 0} := by
    intro w hw
    apply hepsW_subset
    rw [Metric.mem_ball] at hw ⊢
    exact lt_of_lt_of_le hw hrhoW
  let source : Set (KHead.SignRegionChartInput d pivot) :=
    KHead.signRegionSourceBox pivot w0 vHat t0 rho
  let region : Set (HeadwiseSignPoint d) :=
    KHead.signRegionChart theta h pivot '' source
  have hsourceStrict :
      KHead.signRegionChart theta h pivot '' source ⊆
        headwiseStrictPositiveSet theta h := by
    rintro p ⟨x, hx, rfl⟩
    apply hepsStrict_subset
    apply KHead.signRegionSourceBox_subset_ball pivot w0 vHat t0 rho
      epsStrict hrhoStrict
    simpa [source] using hx
  have hambient :
      region = KHead.signRegionSlab theta h ∩
        KHead.signRegionAmbientBox pivot w0 vHat t0 rho := by
    simpa [region, source] using
      KHead.signRegionChart_image_sourceBox_eq_slab_inter_ambientBox
        theta h pivot w0 vHat t0 rho hwball hinterval
  have hsourceDomain : source ⊆
      KHead.signRegionChartDomain theta h pivot := by
    intro x hx
    exact hwball (by simpa [source] using hx.1)
  have hx0Source : x0 ∈ source := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [x0, source] using (Metric.mem_ball_self hrho : w0 ∈ Metric.ball w0 rho)
    · simpa [x0, source] using
        (Metric.mem_ball_self hrho : vHat ∈ Metric.ball vHat rho)
    · dsimp [x0, source, KHead.signRegionSourceBox]
      exact ⟨sub_lt_self t0 hrho, lt_add_of_pos_right t0 hrho⟩
  have hcenterMem : ((w0, v0), t0) ∈ region :=
    ⟨x0, hx0Source, hcenter_chart⟩
  have hconvex : Convex Real source := by
    simpa [source] using
      KHead.convex_signRegionSourceBox pivot w0 vHat t0 rho
  have hconnected : IsPreconnected region := by
    simpa [region] using hconvex.isPreconnected.image
      (KHead.signRegionChart theta h pivot)
      ((KHead.continuousOn_signRegionChart theta h pivot).mono hsourceDomain)
  have hbij : Set.BijOn (KHead.signRegionChart theta h pivot) source region := by
    simpa [source, region] using
      KHead.signRegionChart_bijOn_sourceBox theta h pivot w0 vHat t0 rho
  have hproj : ∀ p ∈ region,
      KHead.signRegionChart theta h pivot
        (KHead.signRegionProjection pivot p) = p := by
    simpa [region] using
      KHead.signRegionChart_projection_inverse_on_image theta h pivot source
  exact ⟨{
    t0 := t0
    t0_mem_Ioo := ht0
    w0 := w0
    v0 := v0
    gram_ne_zero := hgram
    pivot := pivot
    pivot_nonzero := hpivot
    vHat := vHat
    vHat_eq := rfl
    rho := rho
    rho_pos := hrho
    interval_subset_Ioo := hinterval
    w_ball_subset_chart := hwball
    source := source
    source_eq_box := rfl
    region := region
    region_eq_chart_image := rfl
    ambient_identity := hambient
    center_chart := by simpa [x0] using hcenter_chart
    center_mem_region := hcenterMem
    source_open := by
      simpa [source] using
        KHead.isOpen_signRegionSourceBox pivot w0 vHat t0 rho
    source_convex := hconvex
    source_subset_domain := hsourceDomain
    chart_bijective := hbij
    chart_projection_inverse := hproj
    region_connected := hconnected
    strict_positive := by simpa [region] using hsourceStrict
  }⟩

end

end TransformerIdentifiability.NLayer.NoSkip
