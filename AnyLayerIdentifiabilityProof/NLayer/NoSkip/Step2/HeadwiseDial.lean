import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Genericity.HeadwiseSignRegion
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Step2.MultiDial

set_option autoImplicit false

open Matrix Filter

namespace TransformerIdentifiability.NLayer.NoSkip

noncomputable section

/-! # The repaired one-head zero-tail dial -/

/-- A base point in the scalar sign region. -/
structure HeadwiseDialBasePoint {n k d : Nat}
    {theta : Params (n + 1) k d} {h : Fin k}
    (D : HeadwiseSignRegion theta h) where
  point : HeadwiseSignPoint d
  mem : point ∈ D.region

namespace HeadwiseDialBasePoint

variable {n k d : Nat} {theta : Params (n + 1) k d}
  {h : Fin k} {D : HeadwiseSignRegion theta h}

abbrev w (p : HeadwiseDialBasePoint D) : Vec d := p.point.1.1
abbrev v (p : HeadwiseDialBasePoint D) : Vec d := p.point.1.2
abbrev t (p : HeadwiseDialBasePoint D) : Real := p.point.2

theorem anchor_eq_zero (p : HeadwiseDialBasePoint D) :
    anchorRow theta p.w h p.v = 0 := by
  have hs := D.region_subset_slab p.mem
  simpa [anchorRow] using hs.1

theorem t_mem_Ioo (p : HeadwiseDialBasePoint D) :
    p.t ∈ Set.Ioo (0 : Real) 1 :=
  (D.region_subset_slab p.mem).2

theorem pivot_nonzero (p : HeadwiseDialBasePoint D) :
    KHead.signRegionKappa theta h D.pivot p.w ≠ 0 := by
  have hpAmbient : p.point ∈
      KHead.signRegionAmbientBox D.pivot D.w0 D.vHat D.t0 D.rho := by
    have hmem := p.mem
    rw [D.ambient_identity] at hmem
    exact hmem.2
  exact D.w_ball_subset_chart hpAmbient.1

theorem anchorGradient_ne_zero (p : HeadwiseDialBasePoint D) :
    anchorGradient theta p.w h ≠ 0 := by
  intro hz
  have hzcoord := congrFun hz D.pivot
  exact p.pivot_nonzero
    (by simpa [KHead.signRegionKappa, anchorGradient] using hzcoord)

theorem offHead_negative (p : HeadwiseDialBasePoint D)
    {a : Fin k} (ha : a ≠ h) : anchorRow theta p.w a p.v < 0 :=
  D.offHead_negative p.mem ha

theorem deeper_negative (p : HeadwiseDialBasePoint D)
    (jb : LevelRowIndex (n + 1) k) :
    levelRow theta (headwiseDialTuple h p.t) p.w jb p.v < 0 :=
  D.deeper_negative p.mem jb

end HeadwiseDialBasePoint

/-- `c_h(t)=logit(t)-b`. -/
noncomputable def headwiseDialC (r : Nat) (t : Real) : Real :=
  multiDialLogit t - logScale r

/-- The normalized covector direction
`c_h(t) / ‖A_hᵀw‖² • A_hᵀw`. -/
noncomputable def headwiseDialDirection {n k d : Nat} (r : Nat)
    (theta : Params (n + 1) k d) (h : Fin k) (w : Vec d) (t : Real) : Vec d :=
  (headwiseDialC r t *
      (dotProduct (anchorGradient theta w h)
        (anchorGradient theta w h))⁻¹) •
    anchorGradient theta w h

/-- The repaired path fixes `w` and moves only `v`. -/
noncomputable def headwiseDialPath {n k d : Nat} (r : Nat)
    (theta : Params (n + 1) k d) (h : Fin k)
    (p : HeadwiseSignPoint d) (tau : Real) : Vec d × Vec d :=
  (p.1.1, p.1.2 + tau⁻¹ • headwiseDialDirection r theta h p.1.1 p.2)

@[simp] theorem headwiseDialPath_fst {n k d : Nat} (r : Nat)
    (theta : Params (n + 1) k d) (h : Fin k)
    (p : HeadwiseSignPoint d) (tau : Real) :
    (headwiseDialPath r theta h p tau).1 = p.1.1 :=
  rfl

@[simp] theorem headwiseDialPath_snd {n k d : Nat} (r : Nat)
    (theta : Params (n + 1) k d) (h : Fin k)
    (p : HeadwiseSignPoint d) (tau : Real) :
    (headwiseDialPath r theta h p tau).2 =
      p.1.2 + tau⁻¹ • headwiseDialDirection r theta h p.1.1 p.2 :=
  rfl

theorem anchorRow_headwiseDialDirection {n k d : Nat} (r : Nat)
    (theta : Params (n + 1) k d) (h : Fin k) (w : Vec d) (t : Real)
    (hgrad : anchorGradient theta w h ≠ 0) :
    anchorRow theta w h (headwiseDialDirection r theta h w t) =
      headwiseDialC r t := by
  have hdot : dotProduct (anchorGradient theta w h)
      (anchorGradient theta w h) ≠ 0 := by
    exact fun hz => hgrad (dotProduct_self_eq_zero.mp hz)
  rw [anchorRow_eq_dotProduct, headwiseDialDirection, dotProduct_smul]
  change (headwiseDialC r t *
      (dotProduct (anchorGradient theta w h)
        (anchorGradient theta w h))⁻¹) *
      dotProduct (anchorGradient theta w h) (anchorGradient theta w h) = _
  field_simp [hdot]

theorem anchorRow_headwiseDialPath {n k d : Nat} (r : Nat)
    (theta : Params (n + 1) k d) (h : Fin k)
    (p : HeadwiseSignPoint d)
    (hanchor : anchorRow theta p.1.1 h p.1.2 = 0)
    (hgrad : anchorGradient theta p.1.1 h ≠ 0) (tau : Real) :
    anchorRow theta (headwiseDialPath r theta h p tau).1 h
        (headwiseDialPath r theta h p tau).2 =
      tau⁻¹ * headwiseDialC r p.2 := by
  rw [headwiseDialPath_fst, headwiseDialPath_snd, anchorRow_add,
    hanchor, zero_add, anchorRow_smul,
    anchorRow_headwiseDialDirection r theta h p.1.1 p.2 hgrad]

theorem headwiseDial_exact_firstLayer_argument {n k d : Nat} (r : Nat)
    (theta : Params (n + 1) k d) (h : Fin k)
    (p : HeadwiseSignPoint d)
    (hanchor : anchorRow theta p.1.1 h p.1.2 = 0)
    (hgrad : anchorGradient theta p.1.1 h ≠ 0)
    {tau : Real} (htau : tau ≠ 0) :
    tau * anchorRow theta (headwiseDialPath r theta h p tau).1 h
        (headwiseDialPath r theta h p tau).2 + logScale r =
      multiDialLogit p.2 := by
  rw [anchorRow_headwiseDialPath r theta h p hanchor hgrad tau,
    ← mul_assoc, mul_inv_cancel₀ htau, one_mul]
  simp [headwiseDialC]

theorem actualProbeGate_firstLayer_headwiseDialPath
    {n k d : Nat} (r : Nat) (theta : Params (n + 1) k d)
    (h : Fin k) (p : HeadwiseSignPoint d)
    (hanchor : anchorRow theta p.1.1 h p.1.2 = 0)
    (hgrad : anchorGradient theta p.1.1 h ≠ 0)
    (ht : p.2 ∈ Set.Ioo (0 : Real) 1)
    {tau : Real} (htau : tau ≠ 0) :
    actualProbeGate r theta (headwiseDialPath r theta h p tau).1
        (headwiseDialPath r theta h p tau).2 tau
        ⟨0, Nat.succ_pos n⟩ h = p.2 := by
  rw [actualProbeGate_eq_sig]
  change sig (tau * anchorRow theta
      (headwiseDialPath r theta h p tau).1 h
      (headwiseDialPath r theta h p tau).2 + logScale r) = p.2
  rw [headwiseDial_exact_firstLayer_argument r theta h p hanchor hgrad htau]
  exact sig_multiDialLogit ht.1 ht.2

theorem HeadwiseDialBasePoint.firstLayer_gate_eq
    {n k d : Nat} (r : Nat) {theta : Params (n + 1) k d}
    {h : Fin k} {D : HeadwiseSignRegion theta h}
    (p : HeadwiseDialBasePoint D) {tau : Real} (htau : tau ≠ 0) :
    actualProbeGate r theta (headwiseDialPath r theta h p.point tau).1
        (headwiseDialPath r theta h p.point tau).2 tau
        ⟨0, Nat.succ_pos n⟩ h = p.t :=
  actualProbeGate_firstLayer_headwiseDialPath r theta h p.point
    p.anchor_eq_zero p.anchorGradient_ne_zero p.t_mem_Ioo htau

/-- Common first-layer attentions make the dialled target gate exact too. -/
theorem HeadwiseDialBasePoint.paired_firstLayer_gate_eq
    {n k d : Nat} (r : Nat)
    {theta theta' : Params (n + 1) k d} {h : Fin k}
    {D : HeadwiseSignRegion theta' h}
    (hA : ∀ a : Fin k,
      attentionMatrix theta 0 a = attentionMatrix theta' 0 a)
    (p : HeadwiseDialBasePoint D) {tau : Real} (htau : tau ≠ 0) :
    actualProbeGate r theta (headwiseDialPath r theta' h p.point tau).1
          (headwiseDialPath r theta' h p.point tau).2 tau
          ⟨0, Nat.succ_pos n⟩ h = p.t ∧
      actualProbeGate r theta' (headwiseDialPath r theta' h p.point tau).1
          (headwiseDialPath r theta' h p.point tau).2 tau
          ⟨0, Nat.succ_pos n⟩ h = p.t := by
  refine ⟨?_, p.firstLayer_gate_eq r htau⟩
  calc
    actualProbeGate r theta (headwiseDialPath r theta' h p.point tau).1
          (headwiseDialPath r theta' h p.point tau).2 tau
          ⟨0, Nat.succ_pos n⟩ h =
        actualProbeGate r theta' (headwiseDialPath r theta' h p.point tau).1
          (headwiseDialPath r theta' h p.point tau).2 tau
          ⟨0, Nat.succ_pos n⟩ h := by
      have hslope : actualProbeSlope r theta
          (headwiseDialPath r theta' h p.point tau).1
          (headwiseDialPath r theta' h p.point tau).2 tau
          ⟨0, Nat.succ_pos n⟩ h =
          actualProbeSlope r theta'
          (headwiseDialPath r theta' h p.point tau).1
          (headwiseDialPath r theta' h p.point tau).2 tau
          ⟨0, Nat.succ_pos n⟩ h := by
        change anchorRow theta _ h _ = anchorRow theta' _ h _
        simp [anchorRow, hA h]
      simp only [actualProbeGate_eq_sig, hslope]
    _ = p.t := p.firstLayer_gate_eq r htau

/-! ## Compact-uniform motion and off-head saturation -/

theorem continuousAt_headwiseDialDirection
    {n k d : Nat} (r : Nat) {theta : Params (n + 1) k d}
    {h : Fin k} {p : HeadwiseSignPoint d}
    (hgrad0 : anchorGradient theta p.1.1 h ≠ 0)
    (ht : p.2 ∈ Set.Ioo (0 : Real) 1) :
    ContinuousAt (fun q : HeadwiseSignPoint d =>
      headwiseDialDirection r theta h q.1.1 q.2) p := by
  have hdot : dotProduct (anchorGradient theta p.1.1 h)
      (anchorGradient theta p.1.1 h) ≠ 0 :=
    fun hz => hgrad0 (dotProduct_self_eq_zero.mp hz)
  have hlog : ContinuousAt (fun q : HeadwiseSignPoint d =>
      multiDialLogit q.2) p :=
    (continuousAt_multiDialLogit ht.1 ht.2).comp
      (continuousAt_snd : ContinuousAt
        (fun q : HeadwiseSignPoint d => q.2) p)
  unfold headwiseDialDirection headwiseDialC
  have hgrad : ContinuousAt (fun q : HeadwiseSignPoint d =>
      anchorGradient theta q.1.1 h) p := by
    unfold anchorGradient
    fun_prop
  have hnorm : ContinuousAt (fun q : HeadwiseSignPoint d =>
      dotProduct (anchorGradient theta q.1.1 h)
        (anchorGradient theta q.1.1 h)) p := by fun_prop
  exact ((hlog.sub continuousAt_const).mul (hnorm.inv₀ hdot)).smul hgrad

theorem continuousOn_headwiseDialDirection_region
    {n k d : Nat} (r : Nat) {theta : Params (n + 1) k d}
    {h : Fin k} (D : HeadwiseSignRegion theta h) :
    ContinuousOn
      (fun p : HeadwiseSignPoint d =>
        headwiseDialDirection r theta h p.1.1 p.2) D.region := by
  intro p hp
  let bp : HeadwiseDialBasePoint D := ⟨p, hp⟩
  have ht : p.2 ∈ Set.Ioo (0 : Real) 1 :=
    (D.region_subset_slab hp).2
  exact (continuousAt_headwiseDialDirection r
    bp.anchorGradient_ne_zero ht).continuousWithinAt

theorem exists_uniform_headwiseDialDirection_bound
    {n k d : Nat} (r : Nat) {theta : Params (n + 1) k d}
    {h : Fin k} (D : HeadwiseSignRegion theta h)
    {K : Set (HeadwiseSignPoint d)} (hK : IsCompact K)
    (hKD : K ⊆ D.region) :
    ∃ C : Real, 0 ≤ C ∧ ∀ p ∈ K,
      ‖headwiseDialDirection r theta h p.1.1 p.2‖ ≤ C := by
  have hc : ContinuousOn (fun p : HeadwiseSignPoint d =>
      ‖headwiseDialDirection r theta h p.1.1 p.2‖) K :=
    continuous_norm.comp_continuousOn
      ((continuousOn_headwiseDialDirection_region r D).mono hKD)
  rcases hK.bddAbove_image hc with ⟨C, hC⟩
  exact ⟨max C 0, le_max_right _ _, fun p hp =>
    le_trans (hC ⟨p, hp, rfl⟩) (le_max_left _ _)⟩

theorem exists_uniform_headwiseDialPath_motion_bound
    {n k d : Nat} (r : Nat) {theta : Params (n + 1) k d}
    {h : Fin k} (D : HeadwiseSignRegion theta h)
    {K : Set (HeadwiseSignPoint d)} (hK : IsCompact K)
    (hKD : K ⊆ D.region) :
    ∃ C : Real, 0 ≤ C ∧ ∀ p ∈ K, ∀ tau : Real, 1 ≤ tau →
      ‖(headwiseDialPath r theta h p tau).2 - p.1.2‖ ≤ C / tau := by
  rcases exists_uniform_headwiseDialDirection_bound r D hK hKD with
    ⟨C, hC0, hC⟩
  refine ⟨C, hC0, ?_⟩
  intro p hp tau htau
  have htau0 : 0 < tau := lt_of_lt_of_le zero_lt_one htau
  calc
    ‖(headwiseDialPath r theta h p tau).2 - p.1.2‖ =
        tau⁻¹ * ‖headwiseDialDirection r theta h p.1.1 p.2‖ := by
      simp [headwiseDialPath, norm_smul, abs_of_pos htau0]
    _ ≤ tau⁻¹ * C :=
      mul_le_mul_of_nonneg_left (hC p hp) (inv_nonneg.mpr htau0.le)
    _ = C / tau := by rw [div_eq_mul_inv, mul_comm]

theorem continuousOn_headwiseOffHeadCorrection
    {n k d : Nat} (r : Nat) {theta : Params (n + 1) k d}
    {h : Fin k} (D : HeadwiseSignRegion theta h) (a : Fin k) :
    ContinuousOn (fun p : HeadwiseSignPoint d =>
      |anchorRow theta p.1.1 a
        (headwiseDialDirection r theta h p.1.1 p.2)|) D.region := by
  intro p hp
  let bp : HeadwiseDialBasePoint D := ⟨p, hp⟩
  have hdir := continuousAt_headwiseDialDirection r
    bp.anchorGradient_ne_zero bp.t_mem_Ioo
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.abs
  have hgrad : ContinuousAt (fun q : HeadwiseSignPoint d =>
      anchorGradient theta q.1.1 a) p := by
    unfold anchorGradient
    fun_prop
  simpa only [anchorRow_eq_dotProduct] using (show ContinuousAt
      (fun q : HeadwiseSignPoint d =>
        dotProduct (anchorGradient theta q.1.1 a)
          (headwiseDialDirection r theta h q.1.1 q.2)) p by
    unfold dotProduct
    have hterm : ∀ i : Fin d, ContinuousAt (fun q : HeadwiseSignPoint d =>
        anchorGradient theta q.1.1 a i *
          headwiseDialDirection r theta h q.1.1 q.2 i) p := by
      intro i
      have hg := (continuous_apply i).continuousAt.comp hgrad
      have hd := (continuous_apply i).continuousAt.comp hdir
      exact hg.mul hd
    have hsum : ∀ s : Finset (Fin d), ContinuousAt
        (fun q : HeadwiseSignPoint d => ∑ i ∈ s,
          anchorGradient theta q.1.1 a i *
            headwiseDialDirection r theta h q.1.1 q.2 i) p := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using
          (continuousAt_const : ContinuousAt
            (fun _ : HeadwiseSignPoint d => (0 : Real)) p)
      | @insert i s hi ih =>
          simpa [Finset.sum_insert hi] using (hterm i).add ih
    simpa using hsum Finset.univ)

/-- Compact-uniform off-head part of the repaired dial lemma. -/
theorem exists_uniform_headwise_offHead_zero_saturation
    {n k d : Nat} (r : Nat) {theta : Params (n + 1) k d}
    {h : Fin k} (D : HeadwiseSignRegion theta h)
    {K : Set (HeadwiseSignPoint d)} (hK : IsCompact K)
    (hKne : K.Nonempty) (hKD : K ⊆ D.region) :
    ∃ eta C T : Real, 0 < eta ∧ 0 ≤ C ∧ 1 ≤ T ∧
      ∀ p ∈ K, ∀ a : Fin k, a ≠ h → ∀ tau : Real, T ≤ tau →
        anchorRow theta (headwiseDialPath r theta h p tau).1 a
            (headwiseDialPath r theta h p tau).2 ≤ -eta / 2 ∧
          actualProbeGate r theta
              (headwiseDialPath r theta h p tau).1
              (headwiseDialPath r theta h p tau).2 tau
              ⟨0, Nat.succ_pos n⟩ a ≤
            C * Real.exp (-(eta / 2) * tau) := by
  classical
  have hbaseCont (a : Fin k) : ContinuousOn
      (fun p : HeadwiseSignPoint d => anchorRow theta p.1.1 a p.1.2) K := by
    apply Continuous.continuousOn
    unfold anchorRow
    exact KHead.continuous_matrixBilin _
      (continuous_fst.comp continuous_fst)
      (continuous_snd.comp continuous_fst)
  let off : Finset (Fin k) := Finset.univ.filter (· ≠ h)
  have hneg : ∀ a ∈ off, ∀ p ∈ K,
      anchorRow theta p.1.1 a p.1.2 < 0 := by
    intro a ha p hp
    exact D.offHead_negative (hKD hp) (by simpa [off] using ha)
  by_cases hoff : off.Nonempty
  · let OffHead := {a : Fin k // a ∈ off}
    let S : Set Real := ⋃ a : OffHead,
      (fun p : HeadwiseSignPoint d => anchorRow theta p.1.1 a.1 p.1.2) '' K
    have hSc : IsCompact S := by
      apply isCompact_iUnion
      intro a
      exact hK.image_of_continuousOn (hbaseCont a.1)
    have hSne : S.Nonempty := by
      rcases hoff with ⟨a, ha⟩
      rcases hKne with ⟨p, hp⟩
      exact ⟨anchorRow theta p.1.1 a p.1.2,
        Set.mem_iUnion.2 ⟨⟨a, ha⟩, ⟨p, hp, rfl⟩⟩⟩
    obtain ⟨M, hMS, hMmax⟩ := hSc.exists_isGreatest hSne
    have hMneg : M < 0 := by
      rcases Set.mem_iUnion.1 hMS with ⟨a, p, hp, rfl⟩
      exact hneg a.1 a.2 p hp
    let eta : Real := -M
    have heta : 0 < eta := by dsimp [eta]; linarith
    have hmargin : ∀ p ∈ K, ∀ a : Fin k, a ≠ h →
        anchorRow theta p.1.1 a p.1.2 ≤ -eta := by
      intro p hp a ha
      have haoff : a ∈ off := by simp [off, ha]
      have hmem : anchorRow theta p.1.1 a p.1.2 ∈ S :=
        Set.mem_iUnion.2 ⟨⟨a, haoff⟩, ⟨p, hp, rfl⟩⟩
      simpa [eta] using hMmax hmem
    let Corr : Fin k → HeadwiseSignPoint d → Real := fun a p =>
      |anchorRow theta p.1.1 a
        (headwiseDialDirection r theta h p.1.1 p.2)|
    let SB : Set Real := ⋃ a : Fin k, Corr a '' K
    have hSBc : IsCompact SB := by
      apply isCompact_iUnion
      intro a
      exact hK.image_of_continuousOn
        ((continuousOn_headwiseOffHeadCorrection r D a).mono hKD)
    have hSBne : SB.Nonempty := by
      rcases hKne with ⟨p, hp⟩
      exact ⟨Corr h p, Set.mem_iUnion.2 ⟨h, ⟨p, hp, rfl⟩⟩⟩
    obtain ⟨B, hBS, hBmax⟩ := hSBc.exists_isGreatest hSBne
    let B0 : Real := max B 0
    have hB0 : 0 ≤ B0 := le_max_right _ _
    have hcorr : ∀ p ∈ K, ∀ a : Fin k,
        |anchorRow theta p.1.1 a
          (headwiseDialDirection r theta h p.1.1 p.2)| ≤ B0 := by
      intro p hp a
      exact le_trans (hBmax (Set.mem_iUnion.2 ⟨a, ⟨p, hp, rfl⟩⟩))
        (le_max_left _ _)
    let T : Real := max 1 (2 * B0 / eta)
    have hT : 1 ≤ T := le_max_left _ _
    refine ⟨eta, Real.exp (logScale r), T, heta,
      Real.exp_nonneg _, hT, ?_⟩
    intro p hp a ha tau htau
    have htau1 : 1 ≤ tau := le_trans hT htau
    have htau0 : 0 < tau := lt_of_lt_of_le zero_lt_one htau1
    have hratio : 2 * B0 / eta ≤ tau :=
      le_trans (le_max_right _ _) htau
    have htwice : 2 * B0 ≤ tau * eta :=
      (div_le_iff₀ heta).mp (by simpa [mul_comm] using hratio)
    have hBdiv : B0 / tau ≤ eta / 2 := by
      rw [div_le_iff₀ htau0]
      nlinarith
    have hslopeEq : anchorRow theta
        (headwiseDialPath r theta h p tau).1 a
        (headwiseDialPath r theta h p tau).2 =
        anchorRow theta p.1.1 a p.1.2 +
          tau⁻¹ * anchorRow theta p.1.1 a
            (headwiseDialDirection r theta h p.1.1 p.2) := by
      rw [headwiseDialPath_fst, headwiseDialPath_snd,
        anchorRow_add, anchorRow_smul]
    have hpert : tau⁻¹ * anchorRow theta p.1.1 a
        (headwiseDialDirection r theta h p.1.1 p.2) ≤ B0 / tau := by
      calc
        tau⁻¹ * anchorRow theta p.1.1 a
            (headwiseDialDirection r theta h p.1.1 p.2)
            ≤ tau⁻¹ * |anchorRow theta p.1.1 a
                (headwiseDialDirection r theta h p.1.1 p.2)| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (inv_nonneg.mpr htau0.le)
        _ ≤ tau⁻¹ * B0 :=
          mul_le_mul_of_nonneg_left (hcorr p hp a) (inv_nonneg.mpr htau0.le)
        _ = B0 / tau := by rw [div_eq_mul_inv, mul_comm]
    have hslope : anchorRow theta
        (headwiseDialPath r theta h p tau).1 a
        (headwiseDialPath r theta h p tau).2 ≤ -eta / 2 := by
      rw [hslopeEq]
      linarith [hmargin p hp a ha]
    refine ⟨hslope, ?_⟩
    rw [actualProbeGate_eq_sig]
    calc
      sig (tau * actualProbeSlope r theta
          (headwiseDialPath r theta h p tau).1
          (headwiseDialPath r theta h p tau).2 tau
          ⟨0, Nat.succ_pos n⟩ a + logScale r)
          ≤ Real.exp (tau * actualProbeSlope r theta
              (headwiseDialPath r theta h p tau).1
              (headwiseDialPath r theta h p tau).2 tau
              ⟨0, Nat.succ_pos n⟩ a + logScale r) := sig_le_exp _
      _ ≤ Real.exp (tau * (-eta / 2) + logScale r) := by
        apply Real.exp_le_exp.mpr
        have hslopeActual : actualProbeSlope r theta
            (headwiseDialPath r theta h p tau).1
            (headwiseDialPath r theta h p tau).2 tau
            ⟨0, Nat.succ_pos n⟩ a ≤ -eta / 2 := by
          change anchorRow theta (headwiseDialPath r theta h p tau).1 a
            (headwiseDialPath r theta h p tau).2 ≤ -eta / 2
          exact hslope
        exact add_le_add_left
          (mul_le_mul_of_nonneg_left hslopeActual htau0.le) _
      _ = Real.exp (logScale r) * Real.exp (-(eta / 2) * tau) := by
        rw [Real.exp_add]
        ring_nf
  · have hoffEmpty : off = ∅ := Finset.not_nonempty_iff_eq_empty.mp hoff
    refine ⟨1, 0, 1, zero_lt_one, le_rfl, le_rfl, ?_⟩
    intro p hp a ha tau htau
    exfalso
    have : a ∈ off := by simp [off, ha]
    simpa [hoffEmpty] using this

end

end TransformerIdentifiability.NLayer.NoSkip
