import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Step2.HeadwiseSaturatedLimits
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Step2.SourceTransmission
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Step1.FirstAttention
import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.QuadricRigidity

set_option autoImplicit false

open Matrix

namespace TransformerIdentifiability.NLayer.NoSkip

noncomputable section

/-! # Coefficient extraction from one repaired headwise run -/

/-- The complete algebraic output of one headwise run.  The last two fields
are the synchronization missing from the retired simultaneous proof: source
transmission makes `E=0`, hence the label-dependent `K` equals the common
tail transmission product `M`. -/
structure HeadwiseRunCoefficients {n k d r : Nat}
    (thetaLive thetaDial : Params (n + 1) k d) (h : Fin k)
    (labels : DeeperHead → TrichotomyLabel) : Prop where
  vCoefficient :
    (saturatedData thetaLive r labels).M * collapseMatrix thetaLive 0 =
      (primedZeroSaturatedData thetaDial).M * collapseMatrix thetaDial 0
  error_collapse_zero :
    (saturatedData thetaLive r labels).E * collapseMatrix thetaLive 0 = 0
  headCoefficient :
    (saturatedData thetaLive r labels).K * valueMatrix thetaLive 0 h =
      (primedZeroSaturatedData thetaDial).M * valueMatrix thetaDial 0 h
  error_eq_zero : (saturatedData thetaLive r labels).E = 0
  contrast_eq_transmission :
    (saturatedData thetaLive r labels).K =
      (saturatedData thetaLive r labels).M
  synchronizedHeadCoefficient :
    (saturatedData thetaLive r labels).M * valueMatrix thetaLive 0 h =
      (primedZeroSaturatedData thetaDial).M * valueMatrix thetaDial 0 h

/-- At every admissible time, one-quadric linear rigidity kills both matrix
coefficients of the headwise limit identity. -/
theorem HeadwiseTrichotomyResult.fixedTime_limit_coefficients
    {n k d r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d} {h : Fin k}
    {D : HeadwiseSignRegion thetaDial h}
    (T : HeadwiseTrichotomyResult thetaLive thetaDial h (r := r) (D := D))
    (hd : 2 ≤ d)
    (hdetA : (attentionMatrix thetaDial 0 h).det ≠ 0)
    (hlimits : ∀ p ∈ T.region.region,
      headwiseUnprimedSaturatedLimit r thetaLive h T.labels p =
        headwisePrimedZeroSaturatedLimit thetaDial h p) :
    ∀ t ∈ KHead.timeProjection T.region.region,
      ((saturatedData thetaLive r T.labels).M * collapseMatrix thetaLive 0 -
          (primedZeroSaturatedData thetaDial).M * collapseMatrix thetaDial 0 = 0) ∧
        ((saturatedData thetaLive r T.labels).E * collapseMatrix thetaLive 0 +
          t • ((saturatedData thetaLive r T.labels).K *
            valueMatrix thetaLive 0 h) -
          t • ((primedZeroSaturatedData thetaDial).M *
            valueMatrix thetaDial 0 h) = 0) := by
  intro t ht
  obtain ⟨p0, hp0⟩ := ht
  obtain ⟨O, hOopen, hOeq⟩ := T.region.timeSlice_relativelyOpen t
  have hp0slice : p0 ∈ KHead.timeSlice T.region.region t := hp0
  rw [hOeq] at hp0slice
  let W : Set (ProbePoint d) := O ∩ {p | p.1 ≠ 0}
  have hneOpen : IsOpen ({p : ProbePoint d | p.1 ≠ 0}) := by
    have hzClosed : IsClosed ({(0 : Vec d)}) := isClosed_singleton
    have hzOpen : IsOpen ({(0 : Vec d)}ᶜ) := hzClosed.isOpen_compl
    simpa only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_singleton_iff]
      using hzOpen.preimage continuous_fst
  have hWopen : IsOpen W := hOopen.inter hneOpen
  have hp0W : p0 ∈ W := ⟨hp0slice.1, hp0slice.2.2⟩
  have hquad0 :
      NLayer.matrixBilin (attentionMatrix thetaDial 0 h) p0.1 p0.2 = 0 := by
    have hq := hp0slice.2.1
    simpa [KHead.firstHeadQuadric, KHead.firstHeadSlope] using hq
  let Xi0 :=
    (saturatedData thetaLive r T.labels).M * collapseMatrix thetaLive 0 -
      (primedZeroSaturatedData thetaDial).M * collapseMatrix thetaDial 0
  let Xi1 :=
    (saturatedData thetaLive r T.labels).E * collapseMatrix thetaLive 0 +
      t • ((saturatedData thetaLive r T.labels).K *
        valueMatrix thetaLive 0 h) -
      t • ((primedZeroSaturatedData thetaDial).M *
        valueMatrix thetaDial 0 h)
  have hvanish : ∀ p : ProbePoint d, p ∈ W →
      NLayer.matrixBilin (attentionMatrix thetaDial 0 h) p.1 p.2 = 0 →
        Xi0 *ᵥ p.2 + Xi1 *ᵥ p.1 = 0 := by
    intro p hpW hpquad
    have hpPatch : p ∈ KHead.quadricPatch (attentionMatrix thetaDial 0) h :=
      ⟨by simpa [KHead.firstHeadQuadric, KHead.firstHeadSlope] using hpquad,
        hpW.2⟩
    have hpSlice : p ∈ KHead.timeSlice T.region.region t := by
      rw [hOeq]
      exact ⟨hpW.1, hpPatch⟩
    have heq := hlimits (p, t) hpSlice
    have hrewrite : Xi0 *ᵥ p.2 + Xi1 *ᵥ p.1 =
        headwiseUnprimedSaturatedLimit r thetaLive h T.labels (p, t) -
          headwisePrimedZeroSaturatedLimit thetaDial h (p, t) := by
      simp only [Xi0, Xi1, headwiseUnprimedSaturatedLimit,
        headwisePrimedZeroSaturatedLimit, Matrix.sub_mulVec,
        Matrix.add_mulVec, Matrix.smul_mulVec]
      have hzero : (0 : Fin (n + 1)) = ⟨0, Nat.succ_pos n⟩ := Fin.ext rfl
      simp_rw [hzero]
      abel
    rw [hrewrite, heq, sub_self]
  simpa only [Xi0, Xi1] using
    KHead.lem_linear_quadric_rigidity hd
      (attentionMatrix thetaDial 0 h) Xi0 Xi1 p0.1 p0.2 W
      hdetA hp0slice.2.2 hquad0 hWopen hp0W hvanish

/-- Infinite scalar-time interpolation separates the constant error and the
single dial coefficient. -/
theorem HeadwiseTrichotomyResult.limit_coefficients
    {n k d r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d} {h : Fin k}
    {D : HeadwiseSignRegion thetaDial h}
    (T : HeadwiseTrichotomyResult thetaLive thetaDial h (r := r) (D := D))
    (hd : 2 ≤ d)
    (hdetA : (attentionMatrix thetaDial 0 h).det ≠ 0)
    (hlimits : ∀ p ∈ T.region.region,
      headwiseUnprimedSaturatedLimit r thetaLive h T.labels p =
        headwisePrimedZeroSaturatedLimit thetaDial h p) :
    (saturatedData thetaLive r T.labels).M * collapseMatrix thetaLive 0 =
        (primedZeroSaturatedData thetaDial).M * collapseMatrix thetaDial 0 ∧
      (saturatedData thetaLive r T.labels).E * collapseMatrix thetaLive 0 = 0 ∧
      (saturatedData thetaLive r T.labels).K * valueMatrix thetaLive 0 h =
        (primedZeroSaturatedData thetaDial).M * valueMatrix thetaDial 0 h := by
  have htime := T.region.timeProjection_infinite
  obtain ⟨t1, ht1, _⟩ :=
    htime.exists_notMem_finite (Set.finite_empty : (∅ : Set Real).Finite)
  obtain ⟨t2, ht2, ht2ne⟩ :=
    htime.exists_notMem_finite (Set.finite_singleton t1)
  have htne : t1 - t2 ≠ 0 := by
    apply sub_ne_zero.mpr
    intro heq
    apply ht2ne
    simpa [heq]
  obtain ⟨hv0, hw1⟩ :=
    T.fixedTime_limit_coefficients hd hdetA hlimits t1 ht1
  obtain ⟨_hv0', hw2⟩ :=
    T.fixedTime_limit_coefficients hd hdetA hlimits t2 ht2
  have hv :
      (saturatedData thetaLive r T.labels).M * collapseMatrix thetaLive 0 =
        (primedZeroSaturatedData thetaDial).M * collapseMatrix thetaDial 0 :=
    sub_eq_zero.mp hv0
  let B := (saturatedData thetaLive r T.labels).E *
    collapseMatrix thetaLive 0
  let L := (saturatedData thetaLive r T.labels).K *
      valueMatrix thetaLive 0 h -
    (primedZeroSaturatedData thetaDial).M * valueMatrix thetaDial 0 h
  have hw1' : B + t1 • L = 0 := by
    dsimp only [B, L]
    linear_combination (norm := module) hw1
  have hw2' : B + t2 • L = 0 := by
    dsimp only [B, L]
    linear_combination (norm := module) hw2
  have hscaled : (t1 - t2) • L = 0 := by
    linear_combination (norm := module) hw1' - hw2'
  have hL : L = 0 := (smul_eq_zero.mp hscaled).resolve_left htne
  have hB : B = 0 := by
    rw [hL, smul_zero, add_zero] at hw1'
    exact hw1'
  exact ⟨hv, by simpa only [B] using hB,
    sub_eq_zero.mp (by simpa only [L] using hL)⟩

/-- Source transmission removes the apparent dependence of `K` on the run's
deeper labels. -/
theorem HeadwiseTrichotomyResult.runCoefficients
    {n k d r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d} {h : Fin k}
    {D : HeadwiseSignRegion thetaDial h}
    (T : HeadwiseTrichotomyResult thetaLive thetaDial h (r := r) (D := D))
    (hd : 2 ≤ d)
    (hdetC : (collapseMatrix thetaLive 0).det ≠ 0)
    (hdetA : (attentionMatrix thetaDial 0 h).det ≠ 0)
    (hlimits : ∀ p ∈ T.region.region,
      headwiseUnprimedSaturatedLimit r thetaLive h T.labels p =
        headwisePrimedZeroSaturatedLimit thetaDial h p) :
    HeadwiseRunCoefficients thetaLive thetaDial h T.labels (r := r) := by
  obtain ⟨hv, hEC, hhead⟩ := T.limit_coefficients hd hdetA hlimits
  have hE : (saturatedData thetaLive r T.labels).E = 0 := by
    have hunit : IsUnit (collapseMatrix thetaLive 0).det := hdetC.isUnit
    have h := congrArg (fun X : Matrix (Fin d) (Fin d) Real =>
      X * (collapseMatrix thetaLive 0)⁻¹) hEC
    dsimp only at h
    rw [Matrix.zero_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hunit, Matrix.mul_one] at h
    exact h
  have hK : (saturatedData thetaLive r T.labels).K =
      (saturatedData thetaLive r T.labels).M := by
    rw [(saturatedData thetaLive r T.labels).K_eq, hE]
    simp [noSkipSaturatedK]
  refine ⟨hv, hEC, hhead, hE, hK, ?_⟩
  rw [← hK]
  exact hhead

/-- Concrete coefficient extraction, with finite-time realization equality
discharging the limit identity. -/
theorem HeadwiseTrichotomyResult.runCoefficients_of_probeOutput_eq
    {n k d r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d} {h : Fin k}
    {D : HeadwiseSignRegion thetaDial h}
    (T : HeadwiseTrichotomyResult thetaLive thetaDial h (r := r) (D := D))
    (hd : 2 ≤ d)
    (hdetC : (collapseMatrix thetaLive 0).det ≠ 0)
    (hdetA : (attentionMatrix thetaDial 0 h).det ≠ 0)
    (hEq : ∀ w v : Vec d, ∀ tau : Real, 0 < tau →
      probeOutput r thetaLive w v tau = probeOutput r thetaDial w v tau) :
    HeadwiseRunCoefficients thetaLive thetaDial h T.labels (r := r) :=
  T.runCoefficients hd hdetC hdetA
    (fun p hp => T.saturatedLimits_eq p hp hEq)

/-! ## Synchronizing all headwise runs -/

/-- The common source tail transmission `M=C_{L:2}`.  The dummy labels do not
affect this field. -/
noncomputable def headwiseSourceTailM {n k d : Nat}
    (theta : Params (n + 1) k d) : Matrix (Fin d) (Fin d) Real :=
  (saturatedData theta 0 tupleZeroLabels).M

/-- The common target tail transmission `M'=C'_{L:2}`. -/
noncomputable def headwiseTargetTailM {n k d : Nat}
    (theta : Params (n + 1) k d) : Matrix (Fin d) (Fin d) Real :=
  (primedZeroSaturatedData theta).M

theorem saturatedData_M_eq_headwiseSourceTailM
    {n k d r : Nat} (theta : Params (n + 1) k d)
    (labels : DeeperHead → TrichotomyLabel) :
    (saturatedData theta r labels).M = headwiseSourceTailM theta := by
  rfl

theorem primedZeroSaturatedData_M_eq_headwiseTargetTailM
    {n k d : Nat} (theta : Params (n + 1) k d) :
    (primedZeroSaturatedData theta).M = headwiseTargetTailM theta := by
  rfl

/-- Public algebraic output of the repaired all-head Step 2. -/
structure CommonFirstValueGauge {n k d : Nat}
    (thetaLive thetaDial : Params (n + 1) k d) : Type where
  gauge : GaugeMatrix d
  matrix_eq : gauge.matrix =
    (headwiseTargetTailM thetaDial)⁻¹ * headwiseSourceTailM thetaLive
  value_eq : ∀ h : Fin k,
    gauge.matrix * valueMatrix thetaLive 0 h = valueMatrix thetaDial 0 h
  collapse_eq :
    gauge.matrix * collapseMatrix thetaLive 0 = collapseMatrix thetaDial 0
  unique : ∀ H : GaugeMatrix d,
    (∀ h : Fin k,
      H.matrix * valueMatrix thetaLive 0 h = valueMatrix thetaDial 0 h) →
      H = gauge

/-- Independent headwise coefficient identities all use the same `M`; target
joint surjectivity therefore turns them into one unique invertible gauge. -/
theorem exists_commonFirstValueGauge_of_headwiseCoefficients
    {n k d r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d}
    (hreg : Regularity thetaDial)
    (hcoeff : ∀ h : Fin k,
      ∃ labels : DeeperHead → TrichotomyLabel,
        HeadwiseRunCoefficients thetaLive thetaDial h labels (r := r)) :
    Nonempty (CommonFirstValueGauge thetaLive thetaDial) := by
  let M := headwiseSourceTailM thetaLive
  let Mp := headwiseTargetTailM thetaDial
  have hMp : Mp.det ≠ 0 := by
    simpa [Mp, headwiseTargetTailM] using
      primedZeroSaturatedData_M_det_ne_zero hreg
  have hheads : ∀ h : Fin k,
      M * valueMatrix thetaLive 0 h =
        Mp * valueMatrix thetaDial 0 h := by
    intro h
    obtain ⟨labels, hc⟩ := hcoeff h
    simpa [M, Mp, saturatedData_M_eq_headwiseSourceTailM,
      primedZeroSaturatedData_M_eq_headwiseTargetTailM] using
      hc.synchronizedHeadCoefficient
  obtain ⟨G, hGmatrix, hGvalues⟩ := exists_commonValueGauge
    (theta := thetaLive) (theta' := thetaDial) 0 Mp M hMp hheads
    (hreg.joint_surjective 0)
  have hcollapse : G.matrix * collapseMatrix thetaLive 0 =
      collapseMatrix thetaDial 0 := by
    simpa only [Matrix.one_mul] using
      (aggregate_collapseMatrix_eq_of_head_coefficients
        thetaLive thetaDial 0 G.matrix 1
        (fun h => by simpa using hGvalues h))
  have hunique : ∀ H : GaugeMatrix d,
      (∀ h : Fin k,
        H.matrix * valueMatrix thetaLive 0 h = valueMatrix thetaDial 0 h) →
        H = G := by
    intro H hH
    exact commonValueGauge_unique 0 G H hGvalues hH
      (hreg.joint_surjective 0)
  refine ⟨⟨G, ?_, hGvalues, hcollapse, hunique⟩⟩
  simpa [M, Mp] using hGmatrix

/-- Full repaired Step-2 construction once Step 1 has paired the first
attentions.  Each head receives its own sign region, trichotomy labels, and
scalar run; only their label-independent transmission product is retained. -/
theorem exists_commonFirstValueGauge_of_firstAttention
    {n k d r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d}
    (hd : 2 ≤ d)
    (hreg : Regularity thetaDial)
    (hcert : HeadwiseDialCertificate thetaDial)
    (hA : ∀ h : Fin k,
      attentionMatrix thetaLive 0 h = attentionMatrix thetaDial 0 h)
    (hdetC : (collapseMatrix thetaLive 0).det ≠ 0)
    (hVne : ∀ h : Fin k, valueMatrix thetaLive 0 h ≠ 0)
    (hEq : ∀ w v : Vec d, ∀ tau : Real, 0 < tau →
      probeOutput r thetaLive w v tau = probeOutput r thetaDial w v tau) :
    Nonempty (CommonFirstValueGauge thetaLive thetaDial) := by
  apply exists_commonFirstValueGauge_of_headwiseCoefficients hreg
  intro h
  let D : HeadwiseSignRegion thetaDial h :=
    Classical.choice (exists_headwiseSignRegion thetaDial hcert h)
  let T : HeadwiseTrichotomyResult thetaLive thetaDial h (r := r) (D := D) :=
    Classical.choice (exists_headwiseTrichotomyResult
      (r := r) (D := D) hA hd hdetC
      (hreg.attention_det_ne_zero 0 h)
      (hreg.attention_sym_ne_zero 0 h) (hVne h))
  exact ⟨T.labels,
    T.runCoefficients_of_probeOutput_eq hd hdetC
      (hreg.attention_det_ne_zero 0 h) hEq⟩

/-! ## Step-1/Step-2 integration -/

/-- The complete first-layer output of the repaired proof: one unique
target-to-source head permutation and one common value gauge for the relabeled
source. -/
structure FirstLayerGaugeIdentification
    {n k d r : Nat} {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (hr : 1 < r) : Type where
  gates : Step1CommonFirstGates H hr
  values : CommonFirstValueGauge
    (relabelFirstLayer theta gates.sigma) theta'

/-- Step 1 plus equality-derived source transmission discharge every premise
of the repaired headwise Step 2. -/
theorem exists_firstLayerGaugeIdentification
    {n k d r : Nat} {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (hr : 1 < r)
    (hd : 2 ≤ d)
    (heq : ∀ X : Matrix (Fin d) (Fin (seqLength r)) Real,
      transformer theta X = transformer theta' X) :
    Nonempty (FirstLayerGaugeIdentification H hr) := by
  let G := step1CommonFirstGates H hr
  have hpairedGlobal : ∀ X : Matrix (Fin d) (Fin (seqLength r)) Real,
      transformer (relabelFirstLayer theta G.sigma) X = transformer theta' X := by
    intro X
    exact (transformer_relabelFirstLayer theta G.sigma X).trans (heq X)
  have htrans := source_transmission_of_transformer_eq
    H.targetRegularity hpairedGlobal
  have hdetC : (collapseMatrix (relabelFirstLayer theta G.sigma) 0).det ≠ 0 :=
    htrans.2 0
  have hVne : ∀ h : Fin k,
      valueMatrix (relabelFirstLayer theta G.sigma) 0 h ≠ 0 := by
    intro h
    rw [valueMatrix_relabelFirstLayer_zero]
    simpa [IsActiveHead] using G.matched_active h
  have hvalues := exists_commonFirstValueGauge_of_firstAttention
    hd H.targetRegularity H.targetHeadwiseDialCertificate
    G.relabeled_attention_eq hdetC hVne G.relabeled_probe_equal
  exact ⟨⟨G, Classical.choice hvalues⟩⟩

namespace FirstLayerGaugeIdentification

variable {n k d r : Nat} {theta theta' : Params (n + 2) k d}
  {H : Step1StandingHypotheses r theta theta'} {hr : 1 < r}

/-- Original-orientation first attention equality. -/
theorem attention_eq (I : FirstLayerGaugeIdentification H hr) (h : Fin k) :
    attentionMatrix theta 0 (I.gates.sigma h) = attentionMatrix theta' 0 h :=
  I.gates.attention_eq h

/-- Original-orientation first value relation. -/
theorem value_eq (I : FirstLayerGaugeIdentification H hr) (h : Fin k) :
    I.values.gauge.matrix * valueMatrix theta 0 (I.gates.sigma h) =
      valueMatrix theta' 0 h := by
  simpa using I.values.value_eq h

/-- Uniqueness of the common first value gauge. -/
theorem gauge_unique (I : FirstLayerGaugeIdentification H hr)
    (K : GaugeMatrix d)
    (hK : ∀ h : Fin k,
      K.matrix * valueMatrix theta 0 (I.gates.sigma h) =
        valueMatrix theta' 0 h) :
    K = I.values.gauge := by
  apply I.values.unique
  intro h
  simpa using hK h

end FirstLayerGaugeIdentification

end

end TransformerIdentifiability.NLayer.NoSkip
