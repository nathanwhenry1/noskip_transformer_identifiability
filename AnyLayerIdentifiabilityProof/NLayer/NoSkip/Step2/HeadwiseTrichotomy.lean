import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Step2.HeadwiseFrozen

set_option autoImplicit false

open Filter

namespace TransformerIdentifiability.NLayer.NoSkip

noncomputable section

/-! # The repaired headwise trichotomy -/

/-- The source live assignment along a target-chart headwise path. -/
noncomputable def headwiseLiveAssignment {n k d : Nat} (r : Nat)
    (thetaLive thetaDial : Params (n + 1) k d) (h : Fin k)
    (p : HeadwiseSignPoint d) (tau : Real) :
    FormalAssignment (n + 1) k :=
  actualProbeGateAssignment r thetaLive
    (headwiseDialPath r thetaDial h p tau).1
    (headwiseDialPath r thetaDial h p tau).2 tau

/-- Pointwise exponential closeness. -/
abbrev HeadwiseExpCloseTo (f : Real → Real) (a : Real) : Prop :=
  TupleDialExpCloseTo f a

/-- A source first-layer gate equals the corresponding target gate whenever
the first-layer attention matrices agree. -/
theorem headwiseLive_firstLayer_eq_dial
    {n k d : Nat} (r : Nat)
    (thetaLive thetaDial : Params (n + 1) k d)
    (hA : ∀ a : Fin k,
      attentionMatrix thetaLive 0 a = attentionMatrix thetaDial 0 a)
    (h : Fin k) (p : HeadwiseSignPoint d) (tau : Real) (a : Fin k) :
    headwiseLiveAssignment r thetaLive thetaDial h p tau
        (⟨0, Nat.succ_pos n⟩, a) =
      actualProbeGate r thetaDial
        (headwiseDialPath r thetaDial h p tau).1
        (headwiseDialPath r thetaDial h p tau).2 tau
        ⟨0, Nat.succ_pos n⟩ a := by
  simp only [headwiseLiveAssignment, actualProbeGateAssignment,
    actualProbeGate_eq_sig]
  have hslope : actualProbeSlope r thetaLive
      (headwiseDialPath r thetaDial h p tau).1
      (headwiseDialPath r thetaDial h p tau).2 tau
      ⟨0, Nat.succ_pos n⟩ a =
    actualProbeSlope r thetaDial
      (headwiseDialPath r thetaDial h p tau).1
      (headwiseDialPath r thetaDial h p tau).2 tau
      ⟨0, Nat.succ_pos n⟩ a := by
    change anchorRow thetaLive _ a _ = anchorRow thetaDial _ a _
    simp [anchorRow, hA a]
  rw [hslope]

/-- Every frozen headwise gate has absolute value at most one on a restricted
sign region. -/
theorem abs_headwiseFrozenAssignment_le_one
    {n k d : Nat} {r : Nat}
    {thetaDial : Params (n + 1) k d} {h : Fin k}
    {D : HeadwiseSignRegion thetaDial h}
    (R : HeadwiseRestrictedRegion D)
    (labels : DeeperHead → TrichotomyLabel)
    (p : HeadwiseSignPoint d) (hp : p ∈ R.region)
    (x : FormalVar (n + 1) k) :
    |headwiseFrozenAssignment r h p.2 labels x| ≤ 1 := by
  rcases x with ⟨l, a⟩
  by_cases hl0 : l.1 = 0
  · have hl : l = ⟨0, Nat.succ_pos n⟩ := Fin.ext (by simpa using hl0)
    subst l
    rw [headwiseFrozenAssignment, tupleDialFrozenAssignment_first]
    by_cases ha : a = h
    · subst a
      rw [headwiseDialTuple_self, abs_of_pos]
      exact (D.region_subset_slab (R.region_subset hp)).2.2.le
      exact (D.region_subset_slab (R.region_subset hp)).2.1
    · rw [headwiseDialTuple_of_ne ha, abs_zero]
      norm_num
  · rw [headwiseFrozenAssignment,
      tupleDialFrozenAssignment_deeper r (headwiseDialTuple h p.2)
        labels l a (Nat.pos_of_ne_zero hl0)]
    cases hlabel : labels (formalVarDeeperHead (l, a)) <;>
      change labels { layer := l.1 + 1, head := a.1 + 1 } = _ at hlabel
    · simp [hlabel, trichotomyLabelValue]
    · simp [hlabel, trichotomyLabelValue]
    · rw [hlabel, trichotomyLabelValue_alpha,
        abs_of_nonneg (sig_pos _).le]
      exact sig_le_one _

/-- Live gates are sigmoid values. -/
theorem abs_headwiseLiveAssignment_le_one
    {n k d : Nat} (r : Nat)
    (thetaLive thetaDial : Params (n + 1) k d) (h : Fin k)
    (p : HeadwiseSignPoint d) (tau : Real)
    (x : FormalVar (n + 1) k) :
    |headwiseLiveAssignment r thetaLive thetaDial h p tau x| ≤ 1 := by
  simp only [headwiseLiveAssignment, actualProbeGateAssignment]
  rw [actualProbeGate_eq_sig, abs_of_nonneg (sig_pos _).le]
  exact sig_le_one _

/-- Honest estimates retained by the finite processing fold. -/
structure HeadwiseEstimate {n k d : Nat} (r : Nat)
    (thetaLive thetaDial : Params (n + 1) k d) (h : Fin k)
    {D : HeadwiseSignRegion thetaDial h}
    (order : List DeeperHead) (idx : Nat)
    (R : HeadwiseRestrictedRegion D)
    (labels : DeeperHead → TrichotomyLabel) : Prop where
  firstLayer_gate_expClose :
    ∀ a : Fin k, ∀ p ∈ R.region,
      HeadwiseExpCloseTo
        (fun tau ↦ headwiseLiveAssignment r thetaLive thetaDial h p tau
          (⟨0, Nat.succ_pos n⟩, a))
        (headwiseFrozenAssignment r h p.2 labels
          (⟨0, Nat.succ_pos n⟩, a))
  processed_gate_expClose :
    ∀ x : FormalVar (n + 1) k,
      formalVarDeeperHead x ∈ processedPrefix order idx →
      ∀ p ∈ R.region,
        HeadwiseExpCloseTo
          (fun tau ↦ headwiseLiveAssignment r thetaLive thetaDial h p tau x)
          (headwiseFrozenAssignment r h p.2 labels x)
  /-- One set of exponential constants works for every first-layer coordinate
  and every processed deeper coordinate over an arbitrary compact subset.
  This is the compact-uniform clause required by the repaired TeX proof. -/
  compact_uniform_gate_expClose :
    ∀ K : Set (HeadwiseSignPoint d), IsCompact K → K ⊆ R.region →
      ∃ eta C T : Real, 0 < eta ∧ 0 ≤ C ∧ 1 ≤ T ∧
        ∀ p ∈ K, ∀ tau : Real, T ≤ tau →
          ∀ x : FormalVar (n + 1) k,
            (x.1 = 0 ∨
              formalVarDeeperHead x ∈ processedPrefix order idx) →
            |headwiseLiveAssignment r thetaLive thetaDial h p tau x -
                headwiseFrozenAssignment r h p.2 labels x| ≤
              C * Real.exp (-eta * tau)
  compact_uniform_motion :
    ∀ K : Set (HeadwiseSignPoint d), IsCompact K → K ⊆ R.region →
      ∃ C : Real, 0 ≤ C ∧ ∀ p ∈ K, ∀ tau : Real, 1 ≤ tau →
        ‖(headwiseDialPath r thetaDial h p tau).2 - p.1.2‖ ≤ C / tau

namespace HeadwiseEstimate

variable {n k d r : Nat}
  {thetaLive thetaDial : Params (n + 1) k d} {h : Fin k}
  {D : HeadwiseSignRegion thetaDial h}
  {order : List DeeperHead} {idx : Nat}
  {R S : HeadwiseRestrictedRegion D}
  {labels : DeeperHead → TrichotomyLabel}

theorem restrict (hSR : S.region ⊆ R.region)
    (hEst : HeadwiseEstimate r thetaLive thetaDial h order idx R labels) :
    HeadwiseEstimate r thetaLive thetaDial h order idx S labels where
  firstLayer_gate_expClose := fun a p hp ↦
    hEst.firstLayer_gate_expClose a p (hSR hp)
  processed_gate_expClose := fun x hx p hp ↦
    hEst.processed_gate_expClose x hx p (hSR hp)
  compact_uniform_gate_expClose := by
    intro K hK hKS
    exact hEst.compact_uniform_gate_expClose K hK (hKS.trans hSR)
  compact_uniform_motion := by
    intro K hK hKS
    exact exists_uniform_headwiseDialPath_motion_bound r D hK
      (hKS.trans S.region_subset)

end HeadwiseEstimate

/-- The processing state; region topology is carried by
`HeadwiseRestrictedRegion` itself. -/
structure HeadwiseProcessingState {n k d : Nat} (r : Nat)
    (thetaLive thetaDial : Params (n + 1) k d) (h : Fin k)
    {D : HeadwiseSignRegion thetaDial h}
    (idx : Nat) (R : HeadwiseRestrictedRegion D)
    (labels : DeeperHead → TrichotomyLabel) : Prop where
  estimate : HeadwiseEstimate r thetaLive thetaDial h
    (deeperHeadOrder (n + 1) k) idx R labels

/-- Initial first-layer estimates: the selected gate is exact and every
off-head gate saturates to zero. -/
theorem headwiseEstimate_zero
    {n k d : Nat} (r : Nat)
    {thetaLive thetaDial : Params (n + 1) k d} {h : Fin k}
    {D : HeadwiseSignRegion thetaDial h}
    (hA : ∀ a : Fin k,
      attentionMatrix thetaLive 0 a = attentionMatrix thetaDial 0 a)
    (labels : DeeperHead → TrichotomyLabel) :
    HeadwiseEstimate r thetaLive thetaDial h
      (deeperHeadOrder (n + 1) k) 0
      (HeadwiseRestrictedRegion.full D) labels where
  firstLayer_gate_expClose := by
    intro a p hp
    have hpD : p ∈ D.region :=
      (HeadwiseRestrictedRegion.full D).region_subset hp
    by_cases ha : a = h
    · subst a
      refine ⟨1, 0, 1, by norm_num, by norm_num, ?_⟩
      intro tau htau
      have htau0 : tau ≠ 0 :=
        ne_of_gt (lt_of_lt_of_le zero_lt_one htau)
      let bp : HeadwiseDialBasePoint D := ⟨p, hpD⟩
      have hexact := (bp.paired_firstLayer_gate_eq r hA htau0).1
      rw [headwiseFrozenAssignment, tupleDialFrozenAssignment_first,
        headwiseDialTuple_self]
      change |headwiseLiveAssignment r thetaLive thetaDial h p tau
          (⟨0, Nat.succ_pos n⟩, h) - p.2| ≤ _
      change |actualProbeGate r thetaLive
          (headwiseDialPath r thetaDial h p tau).1
          (headwiseDialPath r thetaDial h p tau).2 tau
          ⟨0, Nat.succ_pos n⟩ h - p.2| ≤ _
      rw [hexact]
      simp [bp]
    · rcases exists_uniform_headwise_offHead_zero_saturation r D
          (K := {p}) isCompact_singleton ⟨p, rfl⟩
          (by
            intro x hx
            have hxp : x = p := by simpa using hx
            simpa [hxp] using hpD) with
        ⟨eta, C, T, heta, hC, hT, hsat⟩
      refine ⟨eta / 2, C, T, by positivity, hC, ?_⟩
      intro tau htau
      have hbound := (hsat p (by simp) a ha tau htau).2
      rw [headwiseFrozenAssignment, tupleDialFrozenAssignment_first,
        headwiseDialTuple_of_ne ha, sub_zero]
      have heq := headwiseLive_firstLayer_eq_dial r thetaLive thetaDial
        hA h p tau a
      change |headwiseLiveAssignment r thetaLive thetaDial h p tau
          (⟨0, Nat.succ_pos n⟩, a)| ≤ _
      rw [heq]
      have hnonneg : 0 ≤ actualProbeGate r thetaDial
          (headwiseDialPath r thetaDial h p tau).1
          (headwiseDialPath r thetaDial h p tau).2 tau
          ⟨0, Nat.succ_pos n⟩ a := by
        rw [actualProbeGate_eq_sig]
        exact (sig_pos _).le
      rw [abs_of_nonneg hnonneg]
      exact hbound
  processed_gate_expClose := by
    intro x hx
    have : False := by
      change formalVarDeeperHead x ∈
        (deeperHeadOrder (n + 1) k).take 0 at hx
      simpa using hx
    exact this.elim
  compact_uniform_gate_expClose := by
    intro K hK hKR
    by_cases hKne : K.Nonempty
    · rcases exists_uniform_headwise_offHead_zero_saturation r D hK hKne
          (hKR.trans (HeadwiseRestrictedRegion.full D).region_subset) with
        ⟨eta, C, T, heta, hC, hT, hsat⟩
      refine ⟨eta / 2, C, T, by positivity, hC, hT, ?_⟩
      intro p hp tau htau x hx
      rcases hx with hx0 | hxprocessed
      · have hl : x.1 = ⟨0, Nat.succ_pos n⟩ := by
          apply Fin.ext
          simpa using congrArg Fin.val hx0
        rcases x with ⟨l, a⟩
        have hl' : l = ⟨0, Nat.succ_pos n⟩ := by simpa using hl
        subst l
        have hpD : p ∈ D.region :=
          (HeadwiseRestrictedRegion.full D).region_subset (hKR hp)
        by_cases ha : a = h
        · subst a
          have htau0 : tau ≠ 0 := by
            positivity [le_trans hT htau]
          let bp : HeadwiseDialBasePoint D := ⟨p, hpD⟩
          have hexact := (bp.paired_firstLayer_gate_eq r hA htau0).1
          rw [headwiseFrozenAssignment, tupleDialFrozenAssignment_first,
            headwiseDialTuple_self]
          change |actualProbeGate r thetaLive
              (headwiseDialPath r thetaDial h p tau).1
              (headwiseDialPath r thetaDial h p tau).2 tau
              ⟨0, Nat.succ_pos n⟩ h - p.2| ≤ _
          rw [hexact]
          rw [sub_self, abs_zero]
          exact mul_nonneg hC (Real.exp_nonneg _)
        · have hbound := (hsat p hp a ha tau htau).2
          rw [headwiseFrozenAssignment, tupleDialFrozenAssignment_first,
            headwiseDialTuple_of_ne ha, sub_zero]
          have heq := headwiseLive_firstLayer_eq_dial r thetaLive thetaDial
            hA h p tau a
          change |headwiseLiveAssignment r thetaLive thetaDial h p tau
              (⟨0, Nat.succ_pos n⟩, a)| ≤ _
          rw [heq, abs_of_nonneg (by
            rw [actualProbeGate_eq_sig]
            exact (sig_pos _).le)]
          exact hbound
      · have : False := by
          change formalVarDeeperHead x ∈
            (deeperHeadOrder (n + 1) k).take 0 at hxprocessed
          simpa using hxprocessed
        exact this.elim
    · refine ⟨1, 0, 1, zero_lt_one, le_rfl, le_rfl, ?_⟩
      intro p hp
      exact (hKne ⟨p, hp⟩).elim
  compact_uniform_motion := by
    intro K hK hKR
    exact exists_uniform_headwiseDialPath_motion_bound r D hK
      (hKR.trans (HeadwiseRestrictedRegion.full D).region_subset)

theorem headwiseProcessingState_zero
    {n k d : Nat} (r : Nat)
    {thetaLive thetaDial : Params (n + 1) k d} {h : Fin k}
    {D : HeadwiseSignRegion thetaDial h}
    (hA : ∀ a : Fin k,
      attentionMatrix thetaLive 0 a = attentionMatrix thetaDial 0 a)
    (labels : DeeperHead → TrichotomyLabel) :
    HeadwiseProcessingState r thetaLive thetaDial h 0
      (HeadwiseRestrictedRegion.full D) labels :=
  ⟨headwiseEstimate_zero r hA labels⟩

/-- The formal-slope Lipschitz bound may belong to the arbitrary source while
the moving headwise path is constructed from the target. -/
theorem exists_uniform_allSlopeBoxLip_headwiseDialPath_pair
    {n k d : Nat} (r : Nat)
    (thetaLive thetaDial : Params (n + 1) k d)
    {h : Fin k} (D : HeadwiseSignRegion thetaDial h)
    {K : Set (HeadwiseSignPoint d)} (hK : IsCompact K)
    (hKD : K ⊆ D.region) :
    ∃ B : Real, 0 ≤ B ∧ ∀ p ∈ K, ∀ tau : Real, 1 ≤ tau →
      allSlopeBoxLip thetaLive (headwiseDialPath r thetaDial h p tau) ≤ B := by
  let S : Set (HeadwiseSignPoint d × Real) := K ×ˢ Set.Icc (0 : Real) 1
  let F : HeadwiseSignPoint d × Real → Vec d × Vec d := fun z =>
    (z.1.1.1, z.1.1.2 + z.2 •
      headwiseDialDirection r thetaDial h z.1.1.1 z.1.2)
  have hdir : ContinuousOn (fun z : HeadwiseSignPoint d × Real =>
      headwiseDialDirection r thetaDial h z.1.1.1 z.1.2) S :=
    (continuousOn_headwiseDialDirection_region r D).comp continuousOn_fst
      (fun z hz => hKD hz.1)
  have hF : ContinuousOn F S := by
    apply ContinuousOn.prodMk
    · exact ((continuous_fst.comp continuous_fst).comp continuous_fst).continuousOn
    · exact (((continuous_snd.comp continuous_fst).comp continuous_fst).continuousOn).add
        (continuousOn_snd.smul hdir)
  have hSc : IsCompact S := hK.prod isCompact_Icc
  have hcont : ContinuousOn (fun z => allSlopeBoxLip thetaLive (F z)) S :=
    (continuous_allSlopeBoxLip thetaLive).comp_continuousOn hF
  rcases hSc.bddAbove_image hcont with ⟨B, hB⟩
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro p hp tau htau
  have htau0 : 0 < tau := lt_of_lt_of_le zero_lt_one htau
  have hinv : tau⁻¹ ∈ Set.Icc (0 : Real) 1 :=
    ⟨inv_nonneg.mpr htau0.le, (inv_le_one₀ htau0).2 htau⟩
  have hz : (p, tau⁻¹) ∈ S := ⟨hp, hinv⟩
  have heq : F (p, tau⁻¹) = headwiseDialPath r thetaDial h p tau := rfl
  rw [← heq]
  exact le_trans (hB ⟨(p, tau⁻¹), hz, rfl⟩) (le_max_left _ _)

/-! ## Convergence supplied by a processing state -/

theorem tendsto_headwiseDialPath_atTop
    {n k d : Nat} (r : Nat)
    (thetaDial : Params (n + 1) k d) (h : Fin k)
    (p : HeadwiseSignPoint d) :
    Tendsto (fun tau ↦ headwiseDialPath r thetaDial h p tau)
      atTop (nhds p.1) := by
  have hzero : Tendsto
      (fun tau : Real ↦ tau⁻¹ •
        headwiseDialDirection r thetaDial h p.1.1 p.2)
      atTop (nhds 0) := by
    simpa using (tendsto_inv_atTop_zero (𝕜 := Real)).smul_const
      (headwiseDialDirection r thetaDial h p.1.1 p.2)
  have hv : Tendsto (fun tau ↦ (headwiseDialPath r thetaDial h p tau).2)
      atTop (nhds p.1.2) := by
    simpa [headwiseDialPath] using hzero.const_add p.1.2
  exact tendsto_const_nhds.prodMk_nhds hv

/-- Gatewise convergence through a prefix implies convergence of the complete
source stream through that prefix. -/
theorem tendsto_actualProbePoint_headwise_to_frozen
    {n k d : Nat} (r : Nat)
    (thetaLive thetaDial : Params (n + 1) k d) (h : Fin k)
    (p : HeadwiseSignPoint d) (labels : DeeperHead → TrichotomyLabel) :
    ∀ (q : Nat) (hq : q ≤ n + 1),
      (∀ (l : Fin (n + 1)), l.1 < q → ∀ a : Fin k,
        Tendsto
          (fun tau ↦ headwiseLiveAssignment r thetaLive thetaDial h p tau (l, a))
          atTop (nhds (headwiseFrozenAssignment r h p.2 labels (l, a)))) →
      Tendsto (fun tau ↦ actualProbePoint r thetaLive
          (headwiseDialPath r thetaDial h p tau).1
          (headwiseDialPath r thetaDial h p tau).2 q hq tau)
        atTop
        (nhds (frozenPoint thetaLive
          (tupleDialFrozenFamily r (headwiseDialTuple h p.2) labels)
          p.1.1 p.1.2 q hq)) := by
  intro q
  induction q with
  | zero =>
      intro hq _
      simpa using tendsto_headwiseDialPath_atTop r thetaDial h p
  | succ q ih =>
      intro hq hgate
      let l : Fin (n + 1) := ⟨q, Nat.lt_of_succ_le hq⟩
      have hprev := ih (Nat.le_of_succ_le hq)
        (fun l' hl' a ↦ hgate l' (lt_trans hl' (Nat.lt_succ_self q)) a)
      have hgates : Tendsto
          (fun tau a ↦ headwiseLiveAssignment r thetaLive thetaDial h p tau (l, a))
          atTop
          (nhds (fun a ↦ headwiseFrozenAssignment r h p.2 labels (l, a))) :=
        tendsto_pi_nhds.mpr (fun a ↦ hgate l (Nat.lt_succ_self q) a)
      have hstep :=
        (continuous_gatedEffectivePoint_data thetaLive l).continuousAt.tendsto.comp
          (hgates.prodMk_nhds hprev)
      simpa [actualProbePoint_succ, frozenPoint_succ, l,
        headwiseLiveAssignment, actualProbeGateAssignment,
        headwiseFrozenAssignment, tupleDialFrozenAssignment,
        frozenGateAssignment] using hstep

/-- Every gate strictly before the current deeper layer converges to its
headwise frozen value. -/
theorem tendsto_prior_headwiseGate_of_state
    {n k d r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d} {h : Fin k}
    {D : HeadwiseSignRegion thetaDial h}
    {R : HeadwiseRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx q : Nat} {a : Fin k}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (hcurrent : (deeperHeadOrder (n + 1) k)[idx] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    (hState : HeadwiseProcessingState r thetaLive thetaDial h idx R labels)
    (p : HeadwiseSignPoint d) (hp : p ∈ R.region)
    (l : Fin (n + 1)) (hl : l.1 < q) (b : Fin k) :
    Tendsto
      (fun tau ↦ headwiseLiveAssignment r thetaLive thetaDial h p tau (l, b))
      atTop (nhds (headwiseFrozenAssignment r h p.2 labels (l, b))) := by
  by_cases hl0 : l.1 = 0
  · have lzero : l = ⟨0, Nat.succ_pos n⟩ := Fin.ext hl0
    subst l
    exact (hState.estimate.firstLayer_gate_expClose b p hp).tendsto
  · have hlpos : 1 ≤ l.1 := Nat.one_le_iff_ne_zero.mpr hl0
    have hprocessed : formalVarDeeperHead (l, b) ∈
        processedPrefix (deeperHeadOrder (n + 1) k) idx :=
      KHead.succ_head_mem_processedPrefix_of_layer_lt_getElem_deeperHeadOrder
        hidx hcurrent hlpos l.2 hl b
    exact (hState.estimate.processed_gate_expClose
      (l, b) hprocessed p hp).tendsto

/-- The live current slope tends to the faithful scalar frozen slope. -/
theorem tendsto_currentHeadwiseSlope_of_state
    {n k d r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d} {h : Fin k}
    {D : HeadwiseSignRegion thetaDial h}
    {R : HeadwiseRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx q : Nat} {a : Fin k}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (hqpos : 1 ≤ q) (hq : q < n + 1)
    (hcurrent : (deeperHeadOrder (n + 1) k)[idx] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    (hState : HeadwiseProcessingState r thetaLive thetaDial h idx R labels)
    (p : HeadwiseSignPoint d) (hp : p ∈ R.region) :
    Tendsto (fun tau ↦ actualProbeSlope r thetaLive
        (headwiseDialPath r thetaDial h p tau).1
        (headwiseDialPath r thetaDial h p tau).2 tau ⟨q, hq⟩ a)
      atTop
      (nhds (headwiseFrozenSlopeAt r thetaLive h (q - 1)
        (by omega) a labels p)) := by
  have hpoint := tendsto_actualProbePoint_headwise_to_frozen
    r thetaLive thetaDial h p labels q (Nat.le_of_lt hq)
    (fun l hl b ↦ tendsto_prior_headwiseGate_of_state
      hidx hcurrent hState p hp l hl b)
  have hcont : Continuous (fun z : ProbePoint d ↦
      matrixBilin (attentionMatrix thetaLive ⟨q, hq⟩ a) z.1 z.2) := by
    unfold matrixBilin KHead.matrixBilin Matrix.mulVec dotProduct
    fun_prop
  have hslope := hcont.continuousAt.tendsto.comp hpoint
  have htarget : headwiseFrozenSlopeAt r thetaLive h (q - 1)
      (by omega) a labels p =
      matrixBilin (attentionMatrix thetaLive ⟨q, hq⟩ a)
        (frozenPoint thetaLive
          (tupleDialFrozenFamily r (headwiseDialTuple h p.2) labels)
          p.1.1 p.1.2 q (Nat.le_of_lt hq)).1
        (frozenPoint thetaLive
          (tupleDialFrozenFamily r (headwiseDialTuple h p.2) labels)
          p.1.1 p.1.2 q (Nat.le_of_lt hq)).2 := by
    rw [headwiseFrozenSlopeAt, headwiseFrozenAssignment, eval_formalSlope]
    have hlayer : (⟨(q - 1) + 1, by omega⟩ : Fin (n + 1)) =
        ⟨q, hq⟩ := Fin.ext (Nat.sub_add_cancel hqpos)
    rw [hlayer]
    change matrixBilin (attentionMatrix thetaLive ⟨q, hq⟩ a)
      (evalFormalVec
        (tupleDialFrozenAssignment r (headwiseDialTuple h p.2) labels)
        (formalPoint thetaLive p.1.1 p.1.2 q (Nat.le_of_lt hq)).1)
      (evalFormalVec
        (tupleDialFrozenAssignment r (headwiseDialTuple h p.2) labels)
        (formalPoint thetaLive p.1.1 p.1.2 q (Nat.le_of_lt hq)).2) = _
    have hfp := eval_formalPoint_tupleDialFrozenAssignment r thetaLive
      (headwiseDialTuple h p.2) labels p.1.1 p.1.2 q (Nat.le_of_lt hq)
    rw [hfp.1, hfp.2]
  rw [htarget]
  simpa [actualProbeSlope, Function.comp_def] using hslope

/-! ## Nonzero sign branches -/

theorem continuous_headwiseFrozenSlopeAt
    {n k d : Nat} (r : Nat)
    (thetaLive : Params (n + 1) k d) (h : Fin k)
    (q : Nat) (hq : q + 1 < n + 1) (a : Fin k)
    (labels : DeeperHead → TrichotomyLabel) :
    Continuous (headwiseFrozenSlopeAt r thetaLive h q hq a labels) := by
  let Phi := scalarDialFormAt r thetaLive h q hq a labels
  have hPhi := Phi.continuous_eval
  apply hPhi.congr
  intro p
  exact (headwiseFrozenSlopeAt_eq_scalarEval
    r thetaLive h q hq a labels p).symm

theorem currentHeadwiseGate_expClose_one_of_frozen_pos
    {n k d r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d} {h : Fin k}
    {D : HeadwiseSignRegion thetaDial h}
    {R : HeadwiseRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx q : Nat} {a : Fin k}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (hqpos : 1 ≤ q) (hq : q < n + 1)
    (hcurrent : (deeperHeadOrder (n + 1) k)[idx] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    (hState : HeadwiseProcessingState r thetaLive thetaDial h idx R labels)
    (p : HeadwiseSignPoint d) (hp : p ∈ R.region)
    (hpos : 0 < headwiseFrozenSlopeAt r thetaLive h (q - 1)
      (by omega) a labels p) :
    HeadwiseExpCloseTo
      (fun tau ↦ headwiseLiveAssignment r thetaLive thetaDial h p tau
        (⟨q, hq⟩, a)) 1 := by
  have hslope := tendsto_currentHeadwiseSlope_of_state
    hidx hqpos hq hcurrent hState p hp
  have hsat := KHead.expCloseTo_sig_of_tendsto_pos
    (b := logScale r) hpos hslope
  simpa [HeadwiseExpCloseTo, TupleDialExpCloseTo, KHead.ExpCloseTo,
    headwiseLiveAssignment, actualProbeGateAssignment,
    actualProbeGate_eq_sig] using hsat

theorem currentHeadwiseGate_expClose_zero_of_frozen_neg
    {n k d r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d} {h : Fin k}
    {D : HeadwiseSignRegion thetaDial h}
    {R : HeadwiseRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx q : Nat} {a : Fin k}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (hqpos : 1 ≤ q) (hq : q < n + 1)
    (hcurrent : (deeperHeadOrder (n + 1) k)[idx] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    (hState : HeadwiseProcessingState r thetaLive thetaDial h idx R labels)
    (p : HeadwiseSignPoint d) (hp : p ∈ R.region)
    (hneg : headwiseFrozenSlopeAt r thetaLive h (q - 1)
      (by omega) a labels p < 0) :
    HeadwiseExpCloseTo
      (fun tau ↦ headwiseLiveAssignment r thetaLive thetaDial h p tau
        (⟨q, hq⟩, a)) 0 := by
  have hslope := tendsto_currentHeadwiseSlope_of_state
    hidx hqpos hq hcurrent hState p hp
  have hsat := KHead.expCloseTo_sig_of_tendsto_neg
    (b := logScale r) hneg hslope
  simpa [HeadwiseExpCloseTo, TupleDialExpCloseTo, KHead.ExpCloseTo,
    headwiseLiveAssignment, actualProbeGateAssignment,
    actualProbeGate_eq_sig] using hsat

theorem exists_headwiseRestriction_of_sign
    {n k d r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d} {h : Fin k}
    {D : HeadwiseSignRegion thetaDial h}
    (R : HeadwiseRestrictedRegion D)
    (q : Nat) (hq : q + 1 < n + 1) (a : Fin k)
    (labels : DeeperHead → TrichotomyLabel)
    (positive : Bool) {p : HeadwiseSignPoint d} (hp : p ∈ R.region)
    (hsign : if positive then
        0 < headwiseFrozenSlopeAt r thetaLive h q hq a labels p
      else headwiseFrozenSlopeAt r thetaLive h q hq a labels p < 0) :
    ∃ S : HeadwiseRestrictedRegion D,
      p ∈ S.region ∧ S.region ⊆ R.region ∧
      ∀ x ∈ S.region, if positive then
          0 < headwiseFrozenSlopeAt r thetaLive h q hq a labels x
        else headwiseFrozenSlopeAt r thetaLive h q hq a labels x < 0 := by
  let phi := headwiseFrozenSlopeAt r thetaLive h q hq a labels
  have hphi : Continuous phi :=
    continuous_headwiseFrozenSlopeAt r thetaLive h q hq a labels
  cases positive with
  | false =>
      let O : Set (HeadwiseSignPoint d) := {x | phi x < 0}
      have hO : IsOpen O := isOpen_Iio.preimage hphi
      have hpO : p ∈ O := hsign
      rcases R.exists_restrict_ambientOpen hO hp hpO with
        ⟨S, hpS, hsub⟩
      refine ⟨S, hpS, fun x hx ↦ (hsub hx).1, ?_⟩
      intro x hx
      exact (hsub hx).2
  | true =>
      let O : Set (HeadwiseSignPoint d) := {x | 0 < phi x}
      have hO : IsOpen O := isOpen_Ioi.preimage hphi
      have hpO : p ∈ O := hsign
      rcases R.exists_restrict_ambientOpen hO hp hpO with
        ⟨S, hpS, hsub⟩
      refine ⟨S, hpS, fun x hx ↦ (hsub hx).1, ?_⟩
      intro x hx
      exact (hsub hx).2

/-! ## Successor estimate -/

theorem HeadwiseEstimate.extend_current
    {n k d r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d} {h : Fin k}
    {D : HeadwiseSignRegion thetaDial h}
    {R S : HeadwiseRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx q : Nat} {a : Fin k}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (hqpos : 1 ≤ q) (hq : q < n + 1)
    (hcurrent : (deeperHeadOrder (n + 1) k)[idx] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    (label : TrichotomyLabel)
    (hSR : S.region ⊆ R.region)
    (hEst : HeadwiseEstimate r thetaLive thetaDial h
      (deeperHeadOrder (n + 1) k) idx R labels)
    (hgate : ∀ p ∈ S.region, HeadwiseExpCloseTo
      (fun tau ↦ headwiseLiveAssignment r thetaLive thetaDial h p tau
        (⟨q, hq⟩, a)) (trichotomyLabelValue r label))
    (hgateUniform : ∀ K : Set (HeadwiseSignPoint d), IsCompact K →
      K ⊆ S.region →
      ∃ eta C T : Real, 0 < eta ∧ 0 ≤ C ∧ 1 ≤ T ∧
        ∀ p ∈ K, ∀ tau : Real, T ≤ tau →
          |headwiseLiveAssignment r thetaLive thetaDial h p tau
              (⟨q, hq⟩, a) - trichotomyLabelValue r label| ≤
            C * Real.exp (-eta * tau)) :
    HeadwiseEstimate r thetaLive thetaDial h
      (deeperHeadOrder (n + 1) k) (idx + 1) S
      (setLabel labels (deeperHeadOrder (n + 1) k)[idx] label) where
  firstLayer_gate_expClose := by
    intro b p hp
    simpa [headwiseFrozenAssignment, tupleDialFrozenAssignment_first] using
      hEst.firstLayer_gate_expClose b p (hSR hp)
  processed_gate_expClose := by
    intro x hx p hp
    rcases (KHead.mem_processedPrefix_succ_iff_getElem hidx).mp hx with hold | hnew
    · have hnot : (deeperHeadOrder (n + 1) k)[idx] ∉
          processedPrefix (deeperHeadOrder (n + 1) k) idx :=
        getElem_not_mem_processedPrefix_of_nodup
          (KHead.deeperHeadOrder_nodup (n + 1) k) hidx
      have hne : formalVarDeeperHead x ≠
          (deeperHeadOrder (n + 1) k)[idx] := by
        intro heq
        exact hnot (heq ▸ hold)
      have holdEst := hEst.processed_gate_expClose x hold p (hSR hp)
      have htarget : headwiseFrozenAssignment r h p.2
          (setLabel labels (deeperHeadOrder (n + 1) k)[idx] label) x =
          headwiseFrozenAssignment r h p.2 labels x := by
        rcases x with ⟨l, b⟩
        by_cases hl0 : l.1 = 0
        · simp [headwiseFrozenAssignment, tupleDialFrozenAssignment,
            tupleDialFrozenFamily, hl0]
        · simp [headwiseFrozenAssignment, tupleDialFrozenAssignment,
            tupleDialFrozenFamily, hl0, setLabel_of_ne labels label hne]
      rw [htarget]
      exact holdEst
    · have hdh : formalVarDeeperHead x =
          ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead) := by
        rw [hnew, hcurrent]
      have hxcoord : x = (⟨q, hq⟩, a) := by
        rcases x with ⟨l, b⟩
        apply Prod.ext
        · apply Fin.ext
          simpa [formalVarDeeperHead] using
            congrArg (fun z : DeeperHead ↦ z.layer) hdh
        · apply Fin.ext
          simpa [formalVarDeeperHead] using
            congrArg (fun z : DeeperHead ↦ z.head) hdh
      subst x
      simpa [headwiseFrozenAssignment, tupleDialFrozenAssignment,
        tupleDialFrozenFamily, Nat.ne_of_gt hqpos, formalVarDeeperHead,
        hcurrent, setLabel_self] using hgate p hp
  compact_uniform_gate_expClose := by
    intro K hK hKS
    rcases hEst.compact_uniform_gate_expClose K hK (hKS.trans hSR) with
      ⟨etaOld, COld, TOld, hetaOld, hCOld, hTOld, hOld⟩
    rcases hgateUniform K hK hKS with
      ⟨etaNew, CNew, TNew, hetaNew, hCNew, hTNew, hNew⟩
    let eta : Real := min etaOld etaNew
    let C : Real := max COld CNew
    let T : Real := max TOld TNew
    have heta : 0 < eta := lt_min hetaOld hetaNew
    have hC : 0 ≤ C := hCOld.trans (le_max_left _ _)
    have hT : 1 ≤ T := hTOld.trans (le_max_left _ _)
    refine ⟨eta, C, T, heta, hC, hT, ?_⟩
    intro p hp tau htau x hx
    have htau0 : 0 ≤ tau := by
      exact zero_le_one.trans (hT.trans htau)
    have holdRate : Real.exp (-etaOld * tau) ≤ Real.exp (-eta * tau) := by
      apply Real.exp_le_exp.mpr
      have hmin := min_le_left etaOld etaNew
      nlinarith
    have hnewRate : Real.exp (-etaNew * tau) ≤ Real.exp (-eta * tau) := by
      apply Real.exp_le_exp.mpr
      have hmin := min_le_right etaOld etaNew
      nlinarith
    have holdCoeff : COld ≤ C := le_max_left _ _
    have hnewCoeff : CNew ≤ C := le_max_right _ _
    have htauOld : TOld ≤ tau := (le_max_left _ _).trans htau
    have htauNew : TNew ≤ tau := (le_max_right _ _).trans htau
    rcases hx with hxzero | hxprocessed
    · have hbound := hOld p hp tau htauOld x (Or.inl hxzero)
      have htarget : headwiseFrozenAssignment r h p.2
          (setLabel labels (deeperHeadOrder (n + 1) k)[idx] label) x =
          headwiseFrozenAssignment r h p.2 labels x := by
        rcases x with ⟨l, b⟩
        have hl0 : l.1 = 0 := by
          simpa using congrArg Fin.val hxzero
        simp [headwiseFrozenAssignment, tupleDialFrozenAssignment,
          tupleDialFrozenFamily, hl0]
      rw [htarget]
      exact hbound.trans (mul_le_mul holdCoeff holdRate
        (Real.exp_nonneg _) hC)
    · rcases (KHead.mem_processedPrefix_succ_iff_getElem hidx).mp hxprocessed with
        hold | hnew
      · have hnot : (deeperHeadOrder (n + 1) k)[idx] ∉
            processedPrefix (deeperHeadOrder (n + 1) k) idx :=
          getElem_not_mem_processedPrefix_of_nodup
            (KHead.deeperHeadOrder_nodup (n + 1) k) hidx
        have hne : formalVarDeeperHead x ≠
            (deeperHeadOrder (n + 1) k)[idx] := by
          intro heq
          exact hnot (heq ▸ hold)
        have hbound := hOld p hp tau htauOld x (Or.inr hold)
        have htarget : headwiseFrozenAssignment r h p.2
            (setLabel labels (deeperHeadOrder (n + 1) k)[idx] label) x =
            headwiseFrozenAssignment r h p.2 labels x := by
          rcases x with ⟨l, b⟩
          by_cases hl0 : l.1 = 0
          · simp [headwiseFrozenAssignment, tupleDialFrozenAssignment,
              tupleDialFrozenFamily, hl0]
          · simp [headwiseFrozenAssignment, tupleDialFrozenAssignment,
              tupleDialFrozenFamily, hl0, setLabel_of_ne labels label hne]
        rw [htarget]
        exact hbound.trans (mul_le_mul holdCoeff holdRate
          (Real.exp_nonneg _) hC)
      · have hdh : formalVarDeeperHead x =
            ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead) := by
          rw [hnew, hcurrent]
        have hxcoord : x = (⟨q, hq⟩, a) := by
          rcases x with ⟨l, b⟩
          apply Prod.ext
          · apply Fin.ext
            simpa [formalVarDeeperHead] using
              congrArg (fun z : DeeperHead ↦ z.layer) hdh
          · apply Fin.ext
            simpa [formalVarDeeperHead] using
              congrArg (fun z : DeeperHead ↦ z.head) hdh
        subst x
        have hbound := hNew p hp tau htauNew
        have htarget : headwiseFrozenAssignment r h p.2
            (setLabel labels (deeperHeadOrder (n + 1) k)[idx] label)
              (⟨q, hq⟩, a) = trichotomyLabelValue r label := by
          simp [headwiseFrozenAssignment, tupleDialFrozenAssignment,
            tupleDialFrozenFamily, Nat.ne_of_gt hqpos,
            formalVarDeeperHead, hcurrent, setLabel_self]
        rw [htarget]
        exact hbound.trans (mul_le_mul hnewCoeff hnewRate
          (Real.exp_nonneg _) hC)
  compact_uniform_motion := by
    intro K hK hKS
    exact exists_uniform_headwiseDialPath_motion_bound r D hK
      (hKS.trans S.region_subset)

theorem headwiseProcessingState_succ
    {n k d r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d} {h : Fin k}
    {D : HeadwiseSignRegion thetaDial h}
    {R S : HeadwiseRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx : Nat}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (label : TrichotomyLabel)
    (hState : HeadwiseProcessingState r thetaLive thetaDial h idx R labels)
    (hSR : S.region ⊆ R.region)
    (hEst : HeadwiseEstimate r thetaLive thetaDial h
      (deeperHeadOrder (n + 1) k) (idx + 1) S
      (setLabel labels (deeperHeadOrder (n + 1) k)[idx] label)) :
    HeadwiseProcessingState r thetaLive thetaDial h (idx + 1) S
      (setLabel labels (deeperHeadOrder (n + 1) k)[idx] label) :=
  ⟨hEst⟩

/-! ## Ambient-zero / alpha branch -/

noncomputable def eventuallyExpClose_of_headwiseExpCloseTo
    {f : Real → Real} {a : Real} (h : HeadwiseExpCloseTo f a) :
    EventuallyExpClose f a :=
  let rate := Classical.choose h
  let hrateData := Classical.choose_spec h
  let coeff := Classical.choose hrateData
  let hcoeffData := Classical.choose_spec hrateData
  let start := Classical.choose hcoeffData
  let hspec := Classical.choose_spec hcoeffData
  ⟨rate, hspec.1, coeff, hspec.2.1, start, hspec.2.2⟩

noncomputable def headwiseExpCloseTo_of_eventuallyExpClose
    {f : Real → Real} {a : Real} (h : EventuallyExpClose f a) :
    HeadwiseExpCloseTo f a :=
  ⟨h.rate, h.coeff, h.start, h.rate_pos, h.coeff_nonneg, h.bound⟩

noncomputable def eventuallyExpClose_prior_headwiseGate
    {n k d r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d} {h : Fin k}
    {D : HeadwiseSignRegion thetaDial h}
    {R : HeadwiseRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx q : Nat} {a : Fin k}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (hcurrent : (deeperHeadOrder (n + 1) k)[idx] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    (hState : HeadwiseProcessingState r thetaLive thetaDial h idx R labels)
    (p : HeadwiseSignPoint d) (hp : p ∈ R.region)
    (x : FormalVar (n + 1) k) (hx : x.1.1 < q) :
    EventuallyExpClose
      (fun tau ↦ headwiseLiveAssignment r thetaLive thetaDial h p tau x)
      (headwiseFrozenAssignment r h p.2 labels x) := by
  by_cases hx0 : x.1.1 = 0
  · rcases x with ⟨l, b⟩
    have hl : l = ⟨0, Nat.succ_pos n⟩ := Fin.ext (by simpa using hx0)
    subst l
    exact eventuallyExpClose_of_headwiseExpCloseTo
      (hState.estimate.firstLayer_gate_expClose b p hp)
  · have hxpos : 1 ≤ x.1.1 := Nat.one_le_iff_ne_zero.mpr hx0
    have hprocessed : formalVarDeeperHead x ∈
        processedPrefix (deeperHeadOrder (n + 1) k) idx :=
      KHead.succ_head_mem_processedPrefix_of_layer_lt_getElem_deeperHeadOrder
        hidx hcurrent hxpos x.1.2 hx x.2
    exact eventuallyExpClose_of_headwiseExpCloseTo
      (hState.estimate.processed_gate_expClose x hprocessed p hp)

/-- Uniform-in-time coordinate Lipschitz constants for the finite assignment
telescope at one base point. -/
theorem exists_headwiseSlopeTelescopeConstants
    {n k d r : Nat}
    (thetaLive thetaDial : Params (n + 1) k d) (h : Fin k)
    (labels : DeeperHead → TrichotomyLabel)
    {D : HeadwiseSignRegion thetaDial h}
    (R : HeadwiseRestrictedRegion D)
    (p : HeadwiseSignPoint d) (hp : p ∈ R.region)
    (q : Nat) (hq : q < n + 1) (a : Fin k) :
    ∃ K T : Nat → Real,
      (∀ i, i < (formalVarsBelow (n + 1) k q).length → 0 ≤ K i) ∧
      ∀ i, (hi : i < (formalVarsBelow (n + 1) k q).length) →
        ∀ tau, T i ≤ tau →
          |MvPolynomial.eval
              (KHead.formalVarPrefixAssignment
                (fun tau ↦ headwiseLiveAssignment
                  r thetaLive thetaDial h p tau)
                (fun _ ↦ headwiseFrozenAssignment r h p.2 labels)
                (formalVarsBelow (n + 1) k q) (i + 1) tau)
              (formalSlope thetaLive
                (headwiseDialPath r thetaDial h p tau).1
                (headwiseDialPath r thetaDial h p tau).2 ⟨q, hq⟩ a) -
            MvPolynomial.eval
              (KHead.formalVarPrefixAssignment
                (fun tau ↦ headwiseLiveAssignment
                  r thetaLive thetaDial h p tau)
                (fun _ ↦ headwiseFrozenAssignment r h p.2 labels)
                (formalVarsBelow (n + 1) k q) i tau)
              (formalSlope thetaLive
                (headwiseDialPath r thetaDial h p tau).1
                (headwiseDialPath r thetaDial h p tau).2 ⟨q, hq⟩ a)|
          ≤ K i *
            |headwiseLiveAssignment r thetaLive thetaDial h p tau
                ((formalVarsBelow (n + 1) k q)[i]'hi) -
              headwiseFrozenAssignment r h p.2 labels
                ((formalVarsBelow (n + 1) k q)[i]'hi)| := by
  classical
  have hpath := tendsto_headwiseDialPath_atTop r thetaDial h p
  have hLipTendsto : Tendsto
      (fun tau ↦ allSlopeBoxLip thetaLive
        (headwiseDialPath r thetaDial h p tau))
      atTop (nhds (allSlopeBoxLip thetaLive p.1)) :=
    (continuous_allSlopeBoxLip thetaLive).continuousAt.tendsto.comp hpath
  let B := KHead.EventuallyBoundedReal.ofTendsto hLipTendsto
  refine ⟨fun _ ↦ B.radius, fun _ ↦ B.start, ?_, ?_⟩
  · intro i hi
    exact B.radius_nonneg
  · intro i hi tau htau
    let P := formalSlope thetaLive
      (headwiseDialPath r thetaDial h p tau).1
      (headwiseDialPath r thetaDial h p tau).2 ⟨q, hq⟩ a
    let X := KHead.formalVarPrefixAssignment
      (fun tau ↦ headwiseLiveAssignment r thetaLive thetaDial h p tau)
      (fun _ ↦ headwiseFrozenAssignment r h p.2 labels)
      (formalVarsBelow (n + 1) k q) (i + 1) tau
    let Y := KHead.formalVarPrefixAssignment
      (fun tau ↦ headwiseLiveAssignment r thetaLive thetaDial h p tau)
      (fun _ ↦ headwiseFrozenAssignment r h p.2 labels)
      (formalVarsBelow (n + 1) k q) i tau
    have hX : ∀ x, |X x| ≤ 1 := by
      intro x
      change |KHead.formalVarPrefixAssignment
        (fun tau ↦ headwiseLiveAssignment r thetaLive thetaDial h p tau)
        (fun _ ↦ headwiseFrozenAssignment r h p.2 labels)
        (formalVarsBelow (n + 1) k q) (i + 1) tau x| ≤ 1
      by_cases hx : x ∈ (formalVarsBelow (n + 1) k q).take (i + 1)
      · rw [KHead.formalVarPrefixAssignment_of_mem_take _ _ _ _ _ hx]
        exact abs_headwiseLiveAssignment_le_one
          r thetaLive thetaDial h p tau x
      · rw [KHead.formalVarPrefixAssignment_of_not_mem_take _ _ _ _ _ hx]
        exact abs_headwiseFrozenAssignment_le_one R labels p hp x
    have hY : ∀ x, |Y x| ≤ 1 := by
      intro x
      change |KHead.formalVarPrefixAssignment
        (fun tau ↦ headwiseLiveAssignment r thetaLive thetaDial h p tau)
        (fun _ ↦ headwiseFrozenAssignment r h p.2 labels)
        (formalVarsBelow (n + 1) k q) i tau x| ≤ 1
      by_cases hx : x ∈ (formalVarsBelow (n + 1) k q).take i
      · rw [KHead.formalVarPrefixAssignment_of_mem_take _ _ _ _ _ hx]
        exact abs_headwiseLiveAssignment_le_one
          r thetaLive thetaDial h p tau x
      · rw [KHead.formalVarPrefixAssignment_of_not_mem_take _ _ _ _ _ hx]
        exact abs_headwiseFrozenAssignment_le_one R labels p hp x
    have hXY : ∀ x, x ≠ (formalVarsBelow (n + 1) k q)[i]'hi → X x = Y x :=
      fun x hx ↦ KHead.formalVarPrefixAssignment_succ_eq_of_ne
        _ _ _ i hi tau hx
    have hslice := KHead.eval_sub_eval_abs_le_realSliceLip P
      ((formalVarsBelow (n + 1) k q)[i]'hi) (fun _ ↦ 1) X Y
      (fun _ ↦ zero_le_one) hX hY hXY
    have hsupp : P.support ⊆ KHead.formalMonomialBox (n + 1) k := by
      intro m hm
      rw [KHead.mem_formalMonomialBox_iff]
      intro x
      exact (MvPolynomial.degreeOf_le_iff.mp
        (formalSlope_blockDegree_two thetaLive
          (headwiseDialPath r thetaDial h p tau).1
          (headwiseDialPath r thetaDial h p tau).2 ⟨q, hq⟩ a x)) m hm
    have hbox := realSliceLip_one_le_formalBoxSliceLip P
      ((formalVarsBelow (n + 1) k q)[i]'hi) hsupp
    have hsingle := formalBoxSliceLip_le_allSlopeBoxLip thetaLive
      (headwiseDialPath r thetaDial h p tau) ⟨q, hq⟩ a
      ((formalVarsBelow (n + 1) k q)[i]'hi)
    have hbound : allSlopeBoxLip thetaLive
        (headwiseDialPath r thetaDial h p tau) ≤ B.radius := by
      have hb := B.bound tau htau
      rw [abs_of_nonneg (allSlopeBoxLip_nonneg thetaLive _)] at hb
      exact hb
    have hcoordX : X ((formalVarsBelow (n + 1) k q)[i]'hi) =
        headwiseLiveAssignment r thetaLive thetaDial h p tau
          ((formalVarsBelow (n + 1) k q)[i]'hi) := by
      apply KHead.formalVarPrefixAssignment_of_mem_take
      rw [List.take_succ_eq_append_getElem hi]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    have hcoordY : Y ((formalVarsBelow (n + 1) k q)[i]'hi) =
        headwiseFrozenAssignment r h p.2 labels
          ((formalVarsBelow (n + 1) k q)[i]'hi) := by
      apply KHead.formalVarPrefixAssignment_of_not_mem_take
      exact KHead.getElem_not_mem_take_of_nodup
        (nodup_formalVarsBelow (n + 1) k q) hi
    calc
      |MvPolynomial.eval X P - MvPolynomial.eval Y P| ≤
          KHead.realSliceLip P ((formalVarsBelow (n + 1) k q)[i]'hi)
              (fun _ ↦ 1) *
            |X ((formalVarsBelow (n + 1) k q)[i]'hi) -
              Y ((formalVarsBelow (n + 1) k q)[i]'hi)| := hslice
      _ ≤ B.radius *
            |X ((formalVarsBelow (n + 1) k q)[i]'hi) -
              Y ((formalVarsBelow (n + 1) k q)[i]'hi)| :=
        mul_le_mul_of_nonneg_right (hbox.trans (hsingle.trans hbound))
          (abs_nonneg _)
      _ = B.radius *
            |headwiseLiveAssignment r thetaLive thetaDial h p tau
                ((formalVarsBelow (n + 1) k q)[i]'hi) -
              headwiseFrozenAssignment r h p.2 labels
                ((formalVarsBelow (n + 1) k q)[i]'hi)| := by
        rw [hcoordX, hcoordY]

/-- Ambient vanishing plus prior gate estimates makes the current live slope
exponentially small.  Both evaluations use the same moving probe, so no
`1/tau` probe-motion term appears. -/
noncomputable def currentHeadwiseSlope_expClose_zero
    {n k d r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d} {h : Fin k}
    {D : HeadwiseSignRegion thetaDial h}
    {R : HeadwiseRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx q : Nat} {a : Fin k}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (hqpos : 1 ≤ q) (hq : q < n + 1)
    (hcurrent : (deeperHeadOrder (n + 1) k)[idx] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    (hState : HeadwiseProcessingState r thetaLive thetaDial h idx R labels)
    (p : HeadwiseSignPoint d) (hp : p ∈ R.region)
    (hzero : headwiseFrozenSlopeAt r thetaLive h (q - 1)
      (by omega) a labels = 0) :
    HeadwiseExpCloseTo (fun tau ↦ actualProbeSlope r thetaLive
      (headwiseDialPath r thetaDial h p tau).1
      (headwiseDialPath r thetaDial h p tau).2 tau ⟨q, hq⟩ a) 0 := by
  classical
  let vars := formalVarsBelow (n + 1) k q
  let rho : Real → FormalAssignment (n + 1) k :=
    fun tau ↦ headwiseLiveAssignment r thetaLive thetaDial h p tau
  let sigma : Real → FormalAssignment (n + 1) k :=
    fun _ ↦ headwiseFrozenAssignment r h p.2 labels
  let P : Real → FormalPoly (n + 1) k := fun tau ↦
    formalSlope thetaLive (headwiseDialPath r thetaDial h p tau).1
      (headwiseDialPath r thetaDial h p tau).2 ⟨q, hq⟩ a
  obtain ⟨K, T, hK, hLip⟩ :=
    exists_headwiseSlopeTelescopeConstants thetaLive thetaDial h labels
      R p hp q hq a
  have hcoord : ∀ i, (hi : i < vars.length) → EventuallyExpClose
      (fun tau ↦ rho tau (vars[i]'hi) - sigma tau (vars[i]'hi)) 0 := by
    intro i hi
    have hxlt : (vars[i]'hi).1.1 < q :=
      (mem_formalVarsBelow (vars[i]'hi)).1 (List.getElem_mem hi)
    exact KHead.eventuallyExpClose_sub_const
      (eventuallyExpClose_prior_headwiseGate
        hidx hcurrent hState p hp (vars[i]'hi) hxlt)
  have htel :=
    KHead.eventuallyExpClose_eval_formalPolyPath_delta_of_formalVarPrefix_lipschitz
      P vars rho sigma K T hcoord (by simpa [vars] using hK)
        (by simpa [vars, rho, sigma, P] using hLip)
  have hLive : ∀ tau,
      MvPolynomial.eval
          (KHead.formalVarPrefixAssignment rho sigma vars vars.length tau)
          (P tau) =
        actualProbeSlope r thetaLive
          (headwiseDialPath r thetaDial h p tau).1
          (headwiseDialPath r thetaDial h p tau).2 tau ⟨q, hq⟩ a := by
    intro tau
    have hagree : MvPolynomial.eval
          (KHead.formalVarPrefixAssignment rho sigma vars vars.length tau)
          (P tau) = MvPolynomial.eval (rho tau) (P tau) := by
      apply MvPolynomial.eval₂_congr
      intro x m hxm hm
      have hxvar : x ∈ (P tau).vars := by
        rw [MvPolynomial.mem_vars_iff_mem_support]
        exact ⟨m, MvPolynomial.mem_support_iff.mpr hm, hxm⟩
      have hxlt : x.1.1 < q := formalSlope_dependsOnLayersBefore thetaLive
        (headwiseDialPath r thetaDial h p tau).1
        (headwiseDialPath r thetaDial h p tau).2 ⟨q, hq⟩ a x hxvar
      exact KHead.formalVarPrefixAssignment_length_of_mem
        rho sigma vars tau ((mem_formalVarsBelow x).2 hxlt)
    rw [hagree]
    exact eval_formalSlope_actualProbeGateAssignment
      r thetaLive _ _ tau ⟨q, hq⟩ a
  have hFrozen : ∀ tau,
      MvPolynomial.eval
          (KHead.formalVarPrefixAssignment rho sigma vars 0 tau)
          (P tau) = 0 := by
    intro tau
    rw [KHead.formalVarPrefixAssignment_zero]
    have hz := congrFun hzero
      (((headwiseDialPath r thetaDial h p tau), p.2) : HeadwiseSignPoint d)
    rw [Pi.zero_apply, headwiseFrozenSlopeAt,
      headwiseFrozenAssignment] at hz
    simpa [P, sigma, Nat.sub_add_cancel hqpos] using hz
  exact headwiseExpCloseTo_of_eventuallyExpClose
    (htel.congr_of_forall_eq
      (fun tau ↦ by rw [hLive tau, hFrozen tau, sub_zero]) rfl)

/-- The sigmoid is Lipschitz at the exponentially small rescaled slope, so
the current gate converges exponentially to `alpha r`. -/
noncomputable def currentHeadwiseGate_expClose_alpha
    {n k d r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d} {h : Fin k}
    {D : HeadwiseSignRegion thetaDial h}
    {R : HeadwiseRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx q : Nat} {a : Fin k}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (hqpos : 1 ≤ q) (hq : q < n + 1)
    (hcurrent : (deeperHeadOrder (n + 1) k)[idx] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    (hState : HeadwiseProcessingState r thetaLive thetaDial h idx R labels)
    (p : HeadwiseSignPoint d) (hp : p ∈ R.region)
    (hzero : headwiseFrozenSlopeAt r thetaLive h (q - 1)
      (by omega) a labels = 0) :
    HeadwiseExpCloseTo
      (fun tau ↦ headwiseLiveAssignment r thetaLive thetaDial h p tau
        (⟨q, hq⟩, a)) (alpha r) := by
  have hslope := currentHeadwiseSlope_expClose_zero
    hidx hqpos hq hcurrent hState p hp hzero
  have hgate := KHead.expCloseTo_gate_alpha_of_expCloseTo_slope_zero r
    (h := by simpa [KHead.ExpCloseTo, HeadwiseExpCloseTo,
      TupleDialExpCloseTo] using hslope)
  simpa [KHead.ExpCloseTo, HeadwiseExpCloseTo, TupleDialExpCloseTo,
    headwiseLiveAssignment, actualProbeGateAssignment,
    actualProbeGate_eq_sig] using hgate

/-! ## Compact-uniform successor bounds -/

/-- On a compact base set, the live current slope is exponentially close to
the frozen assignment evaluated at the same moving probe.  Thus the only
non-exponential error in a sign branch is probe motion; in the ambient-zero
branch the moving frozen value is exactly zero. -/
theorem exists_uniform_currentHeadwiseSlope_to_movingFrozen
    {n k d r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d} {h : Fin k}
    {D : HeadwiseSignRegion thetaDial h}
    {R : HeadwiseRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx q : Nat} {a : Fin k}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (hqpos : 1 ≤ q) (hq : q < n + 1)
    (hcurrent : (deeperHeadOrder (n + 1) k)[idx] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    (hState : HeadwiseProcessingState r thetaLive thetaDial h idx R labels)
    {K : Set (HeadwiseSignPoint d)} (hK : IsCompact K)
    (hKR : K ⊆ R.region) :
    ∃ eta C T : Real, 0 < eta ∧ 0 ≤ C ∧ 1 ≤ T ∧
      ∀ p ∈ K, ∀ tau : Real, T ≤ tau →
        |actualProbeSlope r thetaLive
            (headwiseDialPath r thetaDial h p tau).1
            (headwiseDialPath r thetaDial h p tau).2 tau ⟨q, hq⟩ a -
          headwiseFrozenSlopeAt r thetaLive h (q - 1) (by omega) a labels
            ((headwiseDialPath r thetaDial h p tau), p.2)| ≤
          C * Real.exp (-eta * tau) := by
  classical
  rcases hState.estimate.compact_uniform_gate_expClose K hK hKR with
    ⟨eta, E, T0, heta, hE, hT0, hgate⟩
  rcases exists_uniform_allSlopeBoxLip_headwiseDialPath_pair
      r thetaLive thetaDial D hK (hKR.trans R.region_subset) with
    ⟨B, hB, hLip⟩
  let N : Real := Fintype.card (FormalVar (n + 1) k)
  let C : Real := N * B * (N * E)
  let T : Real := max T0 1
  have hC : 0 ≤ C := by positivity
  have hT : 1 ≤ T := le_max_right _ _
  refine ⟨eta, C, T, heta, hC, hT, ?_⟩
  intro p hp tau htau
  have htau0 : T0 ≤ tau := (le_max_left _ _).trans htau
  have htau1 : 1 ≤ tau := (le_max_right _ _).trans htau
  let live : FormalAssignment (n + 1) k :=
    headwiseLiveAssignment r thetaLive thetaDial h p tau
  let frozen : FormalAssignment (n + 1) k :=
    headwiseFrozenAssignment r h p.2 labels
  have hlive : ∀ x, |live x| ≤ 1 := by
    intro x
    exact abs_headwiseLiveAssignment_le_one r thetaLive thetaDial h p tau x
  have hfrozen : ∀ x, |frozen x| ≤ 1 := by
    intro x
    exact abs_headwiseFrozenAssignment_le_one R labels p (hKR hp) x
  have hcoord : ∀ x : FormalVar (n + 1) k, x.1.1 < q →
      |live x - frozen x| ≤ E * Real.exp (-eta * tau) := by
    intro x hxq
    by_cases hx0 : x.1.1 = 0
    · apply hgate p hp tau htau0 x
      left
      exact Fin.ext hx0
    · have hxpos : 1 ≤ x.1.1 := Nat.one_le_iff_ne_zero.mpr hx0
      have hprocessed : formalVarDeeperHead x ∈
          processedPrefix (deeperHeadOrder (n + 1) k) idx :=
        KHead.succ_head_mem_processedPrefix_of_layer_lt_getElem_deeperHeadOrder
          hidx hcurrent hxpos x.1.2 hxq x.2
      exact hgate p hp tau htau0 x (Or.inr hprocessed)
  have hsum :
      (∑ x ∈ (Finset.univ : Finset (FormalVar (n + 1) k)),
        if x.1.1 < q then |live x - frozen x| else 0) ≤
        N * (E * Real.exp (-eta * tau)) := by
    calc
      _ ≤ ∑ _x ∈ (Finset.univ : Finset (FormalVar (n + 1) k)),
          E * Real.exp (-eta * tau) := by
        refine Finset.sum_le_sum ?_
        intro x _hx
        by_cases hxq : x.1.1 < q
        · rw [if_pos hxq]
          exact hcoord x hxq
        · rw [if_neg hxq]
          positivity
      _ = N * (E * Real.exp (-eta * tau)) := by simp [N]
  have htel := formalSlope_eval_sub_eval_le_telescope thetaLive
    (headwiseDialPath r thetaDial h p tau) ⟨q, hq⟩ a
    live frozen hlive hfrozen
  have hlen : ((formalVarsBelow (n + 1) k q).length : Real) ≤ N := by
    dsimp [N]
    exact_mod_cast
      (nodup_formalVarsBelow (n + 1) k q).length_le_card
  have hpoly :
      |MvPolynomial.eval live
          (formalSlope thetaLive
            (headwiseDialPath r thetaDial h p tau).1
            (headwiseDialPath r thetaDial h p tau).2 ⟨q, hq⟩ a) -
        MvPolynomial.eval frozen
          (formalSlope thetaLive
            (headwiseDialPath r thetaDial h p tau).1
            (headwiseDialPath r thetaDial h p tau).2 ⟨q, hq⟩ a)| ≤
        C * Real.exp (-eta * tau) := by
    calc
      _ ≤ ((formalVarsBelow (n + 1) k q).length : Real) *
          allSlopeBoxLip thetaLive (headwiseDialPath r thetaDial h p tau) *
            (∑ x ∈ (Finset.univ : Finset (FormalVar (n + 1) k)),
              if x.1.1 < q then |live x - frozen x| else 0) := htel
      _ ≤ N * B * (N * (E * Real.exp (-eta * tau))) := by
        have hN : 0 ≤ N := by positivity
        have hP : 0 ≤ allSlopeBoxLip thetaLive
            (headwiseDialPath r thetaDial h p tau) :=
          allSlopeBoxLip_nonneg thetaLive _
        have hS : 0 ≤ (∑ x ∈
            (Finset.univ : Finset (FormalVar (n + 1) k)),
            if x.1.1 < q then |live x - frozen x| else 0) := by
          positivity
        calc
          _ ≤ N * allSlopeBoxLip thetaLive
              (headwiseDialPath r thetaDial h p tau) *
              (∑ x ∈ (Finset.univ : Finset (FormalVar (n + 1) k)),
                if x.1.1 < q then |live x - frozen x| else 0) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hlen hP) hS
          _ ≤ N * B *
              (∑ x ∈ (Finset.univ : Finset (FormalVar (n + 1) k)),
                if x.1.1 < q then |live x - frozen x| else 0) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hLip p hp tau htau1) hN) hS
          _ ≤ N * B * (N * (E * Real.exp (-eta * tau))) :=
            mul_le_mul_of_nonneg_left hsum (mul_nonneg hN hB)
      _ = C * Real.exp (-eta * tau) := by
        simp [C]
        ring
  have hliveEval : MvPolynomial.eval live
      (formalSlope thetaLive
        (headwiseDialPath r thetaDial h p tau).1
        (headwiseDialPath r thetaDial h p tau).2 ⟨q, hq⟩ a) =
      actualProbeSlope r thetaLive
        (headwiseDialPath r thetaDial h p tau).1
        (headwiseDialPath r thetaDial h p tau).2 tau ⟨q, hq⟩ a := by
    exact eval_formalSlope_actualProbeGateAssignment r thetaLive _ _ tau _ _
  have hfrozenEval : MvPolynomial.eval frozen
      (formalSlope thetaLive
        (headwiseDialPath r thetaDial h p tau).1
        (headwiseDialPath r thetaDial h p tau).2 ⟨q, hq⟩ a) =
      headwiseFrozenSlopeAt r thetaLive h (q - 1) (by omega) a labels
        ((headwiseDialPath r thetaDial h p tau), p.2) := by
    simp [frozen, headwiseFrozenSlopeAt, headwiseFrozenAssignment,
      Nat.sub_add_cancel hqpos]
  rw [hliveEval, hfrozenEval] at hpoly
  exact hpoly

/-- Uniform continuity near a compact set, with the second point allowed to
lie outside the compact set. -/
theorem exists_compact_uniform_continuity_radius
    {E : Type*} [PseudoMetricSpace E] {K : Set E}
    (hK : IsCompact K) (f : E → Real) (hf : Continuous f)
    {eps : Real} (heps : 0 < eps) :
    ∃ delta : Real, 0 < delta ∧
      ∀ x ∈ K, ∀ y : E, dist x y < delta → |f y - f x| < eps := by
  have hu := hK.uniformContinuousAt_of_continuousAt f
    (fun _x _hx => hf.continuousAt)
    (Metric.dist_mem_uniformity heps)
  rcases Metric.mem_uniformity_dist.mp hu with ⟨delta, hdelta, hrel⟩
  refine ⟨delta, hdelta, ?_⟩
  intro x hx y hxy
  have hout := hrel hxy hx
  change dist (f x) (f y) < eps at hout
  simpa [Real.dist_eq, abs_sub_comm] using hout

/-- The distance from a base point to the same point with its probe replaced
by the moving headwise probe is exactly the motion of the `v` coordinate. -/
theorem dist_headwiseSignPoint_moving
    {n k d r : Nat} (theta : Params (n + 1) k d) (h : Fin k)
    (p : HeadwiseSignPoint d) (tau : Real) :
    dist p ((headwiseDialPath r theta h p tau), p.2) =
      ‖(headwiseDialPath r theta h p tau).2 - p.1.2‖ := by
  simp [dist_eq_norm, Prod.norm_def, headwiseDialPath]

/-- Compact-uniform positive/negative gate saturation from a strict frozen
sign on the branch region and the uniform prefix estimate. -/
theorem exists_uniform_currentHeadwiseGate_of_frozen_sign
    {n k d r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d} {h : Fin k}
    {D : HeadwiseSignRegion thetaDial h}
    {R : HeadwiseRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx q : Nat} {a : Fin k}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (hqpos : 1 ≤ q) (hq : q < n + 1)
    (hcurrent : (deeperHeadOrder (n + 1) k)[idx] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    (hState : HeadwiseProcessingState r thetaLive thetaDial h idx R labels)
    (positive : Bool)
    (hsign : ∀ p ∈ R.region, if positive then
        0 < headwiseFrozenSlopeAt r thetaLive h (q - 1)
          (by omega) a labels p
      else headwiseFrozenSlopeAt r thetaLive h (q - 1)
          (by omega) a labels p < 0)
    {K : Set (HeadwiseSignPoint d)} (hK : IsCompact K)
    (hKR : K ⊆ R.region) :
    ∃ eta C T : Real, 0 < eta ∧ 0 ≤ C ∧ 1 ≤ T ∧
      ∀ p ∈ K, ∀ tau : Real, T ≤ tau →
        |headwiseLiveAssignment r thetaLive thetaDial h p tau
            (⟨q, hq⟩, a) -
          (if positive then 1 else 0)| ≤ C * Real.exp (-eta * tau) := by
  by_cases hKne : K.Nonempty
  · let phi := headwiseFrozenSlopeAt r thetaLive h (q - 1)
      (by omega) a labels
    have hphi : Continuous phi :=
      continuous_headwiseFrozenSlopeAt r thetaLive h (q - 1)
        (by omega) a labels
    obtain ⟨margin, hmargin, hmarginK⟩ :
        ∃ margin : Real, 0 < margin ∧ ∀ p ∈ K,
          if positive then margin ≤ phi p else phi p ≤ -margin := by
      cases positive with
      | false =>
          obtain ⟨p0, hp0K, hp0max⟩ :=
            hK.exists_isMaxOn hKne hphi.continuousOn
          have hp0neg : phi p0 < 0 := by
            simpa [phi] using hsign p0 (hKR hp0K)
          refine ⟨-(phi p0), by linarith, ?_⟩
          intro p hp
          simpa using hp0max hp
      | true =>
          obtain ⟨p0, hp0K, hp0min⟩ :=
            hK.exists_isMinOn hKne hphi.continuousOn
          refine ⟨phi p0, hsign p0 (hKR hp0K), ?_⟩
          intro p hp
          exact hp0min hp
    obtain ⟨etaSlope, CSlope, TSlope, hetaSlope, hCSlope, hTSlope,
        hslope⟩ := exists_uniform_currentHeadwiseSlope_to_movingFrozen
      hidx hqpos hq hcurrent hState hK hKR
    obtain ⟨delta, hdelta, hcont⟩ :=
      exists_compact_uniform_continuity_radius hK phi hphi
        (show 0 < margin / 4 by positivity)
    obtain ⟨CMotion, hCMotion, hmotion⟩ :=
      hState.estimate.compact_uniform_motion K hK hKR
    have hmotionTend : Tendsto (fun tau : Real => CMotion / tau)
        atTop (nhds 0) := by
      simpa [div_eq_mul_inv] using
        (tendsto_inv_atTop_zero (𝕜 := Real)).const_mul CMotion
    obtain ⟨TMotion, hTMotion⟩ :=
      (Metric.tendsto_atTop.mp hmotionTend) delta hdelta
    have hslopeTend : Tendsto
        (fun tau : Real => CSlope * Real.exp (-etaSlope * tau))
        atTop (nhds 0) := by
      have hexp : Tendsto (fun tau : Real => Real.exp (-etaSlope * tau))
          atTop (nhds 0) := by
        have hs := tendsto_id.const_mul_atTop hetaSlope
        simpa only [neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp hs
      simpa using hexp.const_mul CSlope
    obtain ⟨TErr, hTErr⟩ :=
      (Metric.tendsto_atTop.mp hslopeTend) (margin / 4)
        (by positivity)
    let T : Real := max 1 (max TSlope (max TMotion TErr))
    have hT : 1 ≤ T := le_max_left _ _
    have hTS : TSlope ≤ T :=
      (le_max_left _ _).trans (le_max_right _ _)
    have hTM : TMotion ≤ T :=
      (le_max_left _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _))
    have hTE : TErr ≤ T :=
      (le_max_right _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _))
    let rate : Real := margin / 2
    let coeff : Real := if positive then Real.exp (-(logScale r))
      else Real.exp (logScale r)
    have hrate : 0 < rate := by dsimp [rate]; positivity
    have hcoeff : 0 ≤ coeff := by
      dsimp [coeff]
      split <;> positivity
    refine ⟨rate, coeff, T, hrate, hcoeff, hT, ?_⟩
    intro p hp tau htau
    have htau1 : 1 ≤ tau := hT.trans htau
    have htauS : TSlope ≤ tau := hTS.trans htau
    have htauM : TMotion ≤ tau := hTM.trans htau
    have htauE : TErr ≤ tau := hTE.trans htau
    have hmoveLe := hmotion p hp tau htau1
    have hmoveSmall :
        ‖(headwiseDialPath r thetaDial h p tau).2 - p.1.2‖ < delta := by
      have hd := hTMotion tau htauM
      rw [Real.dist_eq, sub_zero] at hd
      exact lt_of_le_of_lt hmoveLe (lt_of_le_of_lt (le_abs_self _) hd)
    have hphiMove :
        |phi ((headwiseDialPath r thetaDial h p tau), p.2) - phi p| <
          margin / 4 := by
      apply hcont p hp
        ((headwiseDialPath r thetaDial h p tau), p.2)
      rw [dist_headwiseSignPoint_moving]
      exact hmoveSmall
    have hslopeErr := hslope p hp tau htauS
    have hslopeErrSmall :
        |actualProbeSlope r thetaLive
            (headwiseDialPath r thetaDial h p tau).1
            (headwiseDialPath r thetaDial h p tau).2 tau ⟨q, hq⟩ a -
          phi ((headwiseDialPath r thetaDial h p tau), p.2)| <
          margin / 4 := by
      have hd := hTErr tau htauE
      rw [Real.dist_eq, sub_zero] at hd
      exact lt_of_le_of_lt hslopeErr (lt_of_le_of_lt (le_abs_self _) hd)
    have hsigned : if positive then
        margin / 2 ≤ actualProbeSlope r thetaLive
          (headwiseDialPath r thetaDial h p tau).1
          (headwiseDialPath r thetaDial h p tau).2 tau ⟨q, hq⟩ a
      else actualProbeSlope r thetaLive
          (headwiseDialPath r thetaDial h p tau).1
          (headwiseDialPath r thetaDial h p tau).2 tau ⟨q, hq⟩ a ≤
            -(margin / 2) := by
      have hbase := hmarginK p hp
      by_cases hb : positive = true
      · simp [hb] at hbase ⊢
        rw [abs_lt] at hphiMove hslopeErrSmall
        have h1 : margin / 2 ≤ phi p - margin / 2 := by linarith
        have h2 : phi p - margin / 2 <
            phi ((headwiseDialPath r thetaDial h p tau), p.2) - margin / 4 := by
          linarith [hphiMove.1]
        have h3 : phi ((headwiseDialPath r thetaDial h p tau), p.2) -
            margin / 4 < actualProbeSlope r thetaLive
              (headwiseDialPath r thetaDial h p tau).1
              (headwiseDialPath r thetaDial h p tau).2 tau ⟨q, hq⟩ a := by
          linarith [hslopeErrSmall.1]
        exact h1.trans (h2.le.trans h3.le)
      · have hb0 : positive = false := Bool.eq_false_of_not_eq_true hb
        simp [hb0] at hbase ⊢
        rw [abs_lt] at hphiMove hslopeErrSmall
        have h1 : actualProbeSlope r thetaLive
              (headwiseDialPath r thetaDial h p tau).1
              (headwiseDialPath r thetaDial h p tau).2 tau ⟨q, hq⟩ a <
            phi ((headwiseDialPath r thetaDial h p tau), p.2) + margin / 4 := by
          linarith [hslopeErrSmall.2]
        have h2 : phi ((headwiseDialPath r thetaDial h p tau), p.2) +
            margin / 4 < phi p + margin / 2 := by
          linarith [hphiMove.2]
        have h3 : phi p + margin / 2 ≤ -(margin / 2) := by linarith
        exact h1.le.trans (h2.le.trans h3)
    cases positive with
    | false =>
        change |headwiseLiveAssignment r thetaLive thetaDial h p tau
            (⟨q, hq⟩, a) - 0| ≤ _
        rw [sub_zero, headwiseLiveAssignment, actualProbeGateAssignment,
          abs_of_nonneg (by
            rw [actualProbeGate_eq_sig]
            exact (sig_pos _).le)]
        exact actualProbeGate_le_exp_of_slope_le_neg r thetaLive _ _ tau
          (margin / 2) ⟨q, hq⟩ a (by positivity) hsigned
    | true =>
        dsimp [coeff, rate]
        change |headwiseLiveAssignment r thetaLive thetaDial h p tau
            (⟨q, hq⟩, a) - 1| ≤ _
        rw [headwiseLiveAssignment, actualProbeGateAssignment,
          actualProbeGate_eq_sig,
          abs_of_nonpos (sub_nonpos.mpr (sig_le_one _))]
        rw [neg_sub]
        have hsigned' : margin / 2 ≤ actualProbeSlope r thetaLive
            (headwiseDialPath r thetaDial h p tau).1
            (headwiseDialPath r thetaDial h p tau).2 tau ⟨q, hq⟩ a := by
          simpa using hsigned
        have htail := one_sub_sig_le_exp_neg
          (tau * actualProbeSlope r thetaLive
            (headwiseDialPath r thetaDial h p tau).1
            (headwiseDialPath r thetaDial h p tau).2 tau ⟨q, hq⟩ a +
              logScale r)
        calc
          1 - sig _ ≤ Real.exp (-(tau * actualProbeSlope r thetaLive
              (headwiseDialPath r thetaDial h p tau).1
              (headwiseDialPath r thetaDial h p tau).2 tau
                ⟨q, hq⟩ a + logScale r)) := htail
          _ ≤ Real.exp (-(logScale r)) *
              Real.exp (-(margin / 2) * tau) := by
            rw [← Real.exp_add]
            apply Real.exp_le_exp.mpr
            nlinarith
  · refine ⟨1, 0, 1, zero_lt_one, le_rfl, le_rfl, ?_⟩
    intro p hp
    exact (hKne ⟨p, hp⟩).elim

/-- Compact-uniform alpha saturation in the ambient-zero branch. -/
theorem exists_uniform_currentHeadwiseGate_alpha
    {n k d r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d} {h : Fin k}
    {D : HeadwiseSignRegion thetaDial h}
    {R : HeadwiseRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx q : Nat} {a : Fin k}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (hqpos : 1 ≤ q) (hq : q < n + 1)
    (hcurrent : (deeperHeadOrder (n + 1) k)[idx] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    (hState : HeadwiseProcessingState r thetaLive thetaDial h idx R labels)
    (hzero : headwiseFrozenSlopeAt r thetaLive h (q - 1)
      (by omega) a labels = 0)
    {K : Set (HeadwiseSignPoint d)} (hK : IsCompact K)
    (hKR : K ⊆ R.region) :
    ∃ eta C T : Real, 0 < eta ∧ 0 ≤ C ∧ 1 ≤ T ∧
      ∀ p ∈ K, ∀ tau : Real, T ≤ tau →
        |headwiseLiveAssignment r thetaLive thetaDial h p tau
            (⟨q, hq⟩, a) - alpha r| ≤ C * Real.exp (-eta * tau) := by
  rcases exists_uniform_currentHeadwiseSlope_to_movingFrozen
      hidx hqpos hq hcurrent hState hK hKR with
    ⟨eta, C0, T0, heta, hC0, hT0, hslope⟩
  have hpolyTend : Tendsto
      (fun tau : Real => tau * Real.exp (-(eta / 2) * tau))
      atTop (nhds 0) := by
    have hrate : 0 < eta / 2 := by positivity
    have hscaled : Tendsto (fun tau : Real => (eta / 2) * tau)
        atTop atTop := tendsto_id.const_mul_atTop hrate
    have hbase := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hscaled
    have hmul := hbase.const_mul (eta / 2)⁻¹
    have hfun :
        (fun tau : Real => (eta / 2)⁻¹ *
          (((eta / 2) * tau) ^ 1 * Real.exp (-((eta / 2) * tau)))) =
          (fun tau : Real => tau * Real.exp (-(eta / 2) * tau)) := by
      funext tau
      simp only [pow_one]
      field_simp
    simp only [Function.comp_apply] at hmul
    rw [hfun] at hmul
    simpa using hmul
  obtain ⟨Tpoly, hTpoly⟩ :=
    (Metric.tendsto_atTop.mp hpolyTend) 1 zero_lt_one
  let T : Real := max 1 (max T0 Tpoly)
  have hT : 1 ≤ T := le_max_left _ _
  have hT0T : T0 ≤ T :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hTpolyT : Tpoly ≤ T :=
    (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨eta / 2, C0 / 4, T, by positivity, by positivity, hT, ?_⟩
  intro p hp tau htau
  have htau0 : 0 ≤ tau := zero_le_one.trans (hT.trans htau)
  have hs := hslope p hp tau (hT0T.trans htau)
  have hfrozenZero : headwiseFrozenSlopeAt r thetaLive h (q - 1)
      (by omega) a labels
        ((headwiseDialPath r thetaDial h p tau), p.2) = 0 := by
    simpa using congrFun hzero
      (((headwiseDialPath r thetaDial h p tau), p.2) : HeadwiseSignPoint d)
  rw [hfrozenZero, sub_zero] at hs
  have hpoly := hTpoly tau (hTpolyT.trans htau)
  rw [Real.dist_eq, sub_zero] at hpoly
  have hpolyLe : tau * Real.exp (-(eta / 2) * tau) ≤ 1 :=
    le_trans (le_abs_self _) hpoly.le
  rw [headwiseLiveAssignment, actualProbeGateAssignment,
    actualProbeGate_eq_sig, alpha]
  have hsig := abs_sig_sub_sig_le
    (tau * actualProbeSlope r thetaLive
      (headwiseDialPath r thetaDial h p tau).1
      (headwiseDialPath r thetaDial h p tau).2 tau ⟨q, hq⟩ a +
        logScale r) (logScale r)
  calc
    |sig _ - sig (logScale r)| ≤
        |tau * actualProbeSlope r thetaLive
          (headwiseDialPath r thetaDial h p tau).1
          (headwiseDialPath r thetaDial h p tau).2 tau
            ⟨q, hq⟩ a + logScale r - logScale r| / 4 := hsig
    _ = tau * |actualProbeSlope r thetaLive
          (headwiseDialPath r thetaDial h p tau).1
          (headwiseDialPath r thetaDial h p tau).2 tau
            ⟨q, hq⟩ a| / 4 := by
      rw [add_sub_cancel_right, abs_mul, abs_of_nonneg htau0]
    _ ≤ tau * (C0 * Real.exp (-eta * tau)) / 4 := by
      gcongr
    _ ≤ (C0 / 4) * Real.exp (-(eta / 2) * tau) := by
      have hsplit : Real.exp (-eta * tau) =
          Real.exp (-(eta / 2) * tau) *
            Real.exp (-(eta / 2) * tau) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hsplit]
      have hexp0 : 0 ≤ Real.exp (-(eta / 2) * tau) := Real.exp_nonneg _
      calc
        tau * (C0 * (Real.exp (-(eta / 2) * tau) *
              Real.exp (-(eta / 2) * tau))) / 4 =
            (C0 / 4) * (tau * Real.exp (-(eta / 2) * tau)) *
              Real.exp (-(eta / 2) * tau) := by ring
        _ ≤ (C0 / 4) * 1 * Real.exp (-(eta / 2) * tau) := by
          gcongr
        _ = _ := by ring

/-! ## One step and the finite fold -/

theorem exists_headwiseTrichotomyStep
    {n k d r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d} {h : Fin k}
    {D : HeadwiseSignRegion thetaDial h}
    {R : HeadwiseRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx : Nat}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (hState : HeadwiseProcessingState r thetaLive thetaDial h idx R labels)
    (hd : 2 ≤ d)
    (hdetC : (collapseMatrix thetaLive 0).det ≠ 0)
    (hdetA : (attentionMatrix thetaDial 0 h).det ≠ 0)
    (hsymA : sym (attentionMatrix thetaDial 0 h) ≠ 0)
    (hVne : valueMatrix thetaLive 0 h ≠ 0) :
    ∃ S : HeadwiseRestrictedRegion D,
      ∃ nextLabels : DeeperHead → TrichotomyLabel,
        S.region ⊆ R.region ∧
        HeadwiseProcessingState r thetaLive thetaDial h
          (idx + 1) S nextLabels := by
  rcases KHead.exists_decompose_getElem_deeperHeadOrder hidx with
    ⟨q, a, hqpos, hq, hcurrent⟩
  let phi := headwiseFrozenSlopeAt r thetaLive h (q - 1)
    (by omega) a labels
  by_cases hvanish : ∀ p ∈ R.region, phi p = 0
  · have hzero : phi = 0 := by
      exact headwiseFrozenSlopeAt_eq_zero_of_vanishesOn r R
        (q - 1) (by omega) a labels hd hdetC hdetA hsymA hVne hvanish
    have hgate : ∀ p ∈ R.region, HeadwiseExpCloseTo
        (fun tau ↦ headwiseLiveAssignment r thetaLive thetaDial h p tau
          (⟨q, hq⟩, a)) (trichotomyLabelValue r KHead.TrichotomyLabel.alpha) := by
      intro p hp
      simpa using currentHeadwiseGate_expClose_alpha
        hidx hqpos hq hcurrent hState p hp hzero
    have hgateUniform : ∀ K : Set (HeadwiseSignPoint d), IsCompact K →
        K ⊆ R.region →
        ∃ eta C T : Real, 0 < eta ∧ 0 ≤ C ∧ 1 ≤ T ∧
          ∀ p ∈ K, ∀ tau : Real, T ≤ tau →
            |headwiseLiveAssignment r thetaLive thetaDial h p tau
                (⟨q, hq⟩, a) -
              trichotomyLabelValue r KHead.TrichotomyLabel.alpha| ≤
                C * Real.exp (-eta * tau) := by
      intro K hK hKR
      simpa using exists_uniform_currentHeadwiseGate_alpha
        hidx hqpos hq hcurrent hState hzero hK hKR
    have hEst := hState.estimate.extend_current hidx hqpos hq hcurrent
      KHead.TrichotomyLabel.alpha Set.Subset.rfl hgate hgateUniform
    exact ⟨R,
      setLabel labels (deeperHeadOrder (n + 1) k)[idx]
        KHead.TrichotomyLabel.alpha,
      Set.Subset.rfl,
      headwiseProcessingState_succ hidx KHead.TrichotomyLabel.alpha
        hState Set.Subset.rfl hEst⟩
  · push Not at hvanish
    rcases hvanish with ⟨p, hp, hpne⟩
    rcases lt_or_gt_of_ne hpne with hpneg | hppos
    · rcases exists_headwiseRestriction_of_sign R (q - 1) (by omega)
          a labels false hp hpneg with ⟨S, _hpS, hSR, hnegative⟩
      have hgate : ∀ x ∈ S.region, HeadwiseExpCloseTo
          (fun tau ↦ headwiseLiveAssignment r thetaLive thetaDial h x tau
            (⟨q, hq⟩, a))
          (trichotomyLabelValue r KHead.TrichotomyLabel.zero) := by
        intro x hx
        simpa using currentHeadwiseGate_expClose_zero_of_frozen_neg
          hidx hqpos hq hcurrent hState x (hSR hx) (hnegative x hx)
      let hStateS : HeadwiseProcessingState r thetaLive thetaDial h idx S labels :=
        ⟨hState.estimate.restrict hSR⟩
      have hgateUniform : ∀ K : Set (HeadwiseSignPoint d), IsCompact K →
          K ⊆ S.region →
          ∃ eta C T : Real, 0 < eta ∧ 0 ≤ C ∧ 1 ≤ T ∧
            ∀ p ∈ K, ∀ tau : Real, T ≤ tau →
              |headwiseLiveAssignment r thetaLive thetaDial h p tau
                  (⟨q, hq⟩, a) -
                trichotomyLabelValue r KHead.TrichotomyLabel.zero| ≤
                  C * Real.exp (-eta * tau) := by
        intro K hK hKS
        simpa using exists_uniform_currentHeadwiseGate_of_frozen_sign
          hidx hqpos hq hcurrent hStateS false hnegative hK hKS
      have hEst := hState.estimate.extend_current hidx hqpos hq hcurrent
        KHead.TrichotomyLabel.zero hSR hgate hgateUniform
      exact ⟨S,
        setLabel labels (deeperHeadOrder (n + 1) k)[idx]
          KHead.TrichotomyLabel.zero,
        hSR,
        headwiseProcessingState_succ hidx KHead.TrichotomyLabel.zero
          hState hSR hEst⟩
    · rcases exists_headwiseRestriction_of_sign R (q - 1) (by omega)
          a labels true hp hppos with ⟨S, _hpS, hSR, hpositive⟩
      have hgate : ∀ x ∈ S.region, HeadwiseExpCloseTo
          (fun tau ↦ headwiseLiveAssignment r thetaLive thetaDial h x tau
            (⟨q, hq⟩, a))
          (trichotomyLabelValue r KHead.TrichotomyLabel.one) := by
        intro x hx
        simpa using currentHeadwiseGate_expClose_one_of_frozen_pos
          hidx hqpos hq hcurrent hState x (hSR hx) (hpositive x hx)
      let hStateS : HeadwiseProcessingState r thetaLive thetaDial h idx S labels :=
        ⟨hState.estimate.restrict hSR⟩
      have hgateUniform : ∀ K : Set (HeadwiseSignPoint d), IsCompact K →
          K ⊆ S.region →
          ∃ eta C T : Real, 0 < eta ∧ 0 ≤ C ∧ 1 ≤ T ∧
            ∀ p ∈ K, ∀ tau : Real, T ≤ tau →
              |headwiseLiveAssignment r thetaLive thetaDial h p tau
                  (⟨q, hq⟩, a) -
                trichotomyLabelValue r KHead.TrichotomyLabel.one| ≤
                  C * Real.exp (-eta * tau) := by
        intro K hK hKS
        simpa using exists_uniform_currentHeadwiseGate_of_frozen_sign
          hidx hqpos hq hcurrent hStateS true hpositive hK hKS
      have hEst := hState.estimate.extend_current hidx hqpos hq hcurrent
        KHead.TrichotomyLabel.one hSR hgate hgateUniform
      exact ⟨S,
        setLabel labels (deeperHeadOrder (n + 1) k)[idx]
          KHead.TrichotomyLabel.one,
        hSR,
        headwiseProcessingState_succ hidx KHead.TrichotomyLabel.one
          hState hSR hEst⟩

theorem exists_headwiseFiniteFold
    {n k d r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d} {h : Fin k}
    {D : HeadwiseSignRegion thetaDial h}
    {R : HeadwiseRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx : Nat}
    (hidxle : idx ≤ (deeperHeadOrder (n + 1) k).length)
    (hState : HeadwiseProcessingState r thetaLive thetaDial h idx R labels)
    (hd : 2 ≤ d)
    (hdetC : (collapseMatrix thetaLive 0).det ≠ 0)
    (hdetA : (attentionMatrix thetaDial 0 h).det ≠ 0)
    (hsymA : sym (attentionMatrix thetaDial 0 h) ≠ 0)
    (hVne : valueMatrix thetaLive 0 h ≠ 0) :
    ∃ S : HeadwiseRestrictedRegion D,
      ∃ finalLabels : DeeperHead → TrichotomyLabel,
        S.region ⊆ R.region ∧
        HeadwiseProcessingState r thetaLive thetaDial h
          (deeperHeadOrder (n + 1) k).length S finalLabels := by
  by_cases hdone : idx = (deeperHeadOrder (n + 1) k).length
  · subst idx
    exact ⟨R, labels, Set.Subset.rfl, hState⟩
  · have hidx : idx < (deeperHeadOrder (n + 1) k).length :=
      lt_of_le_of_ne hidxle hdone
    rcases exists_headwiseTrichotomyStep hidx hState hd hdetC hdetA
        hsymA hVne with ⟨S, nextLabels, hSR, hnext⟩
    rcases exists_headwiseFiniteFold (idx := idx + 1)
        (Nat.succ_le_iff.mpr hidx) hnext hd hdetC hdetA hsymA hVne with
      ⟨T, finalLabels, hTS, hfinal⟩
    exact ⟨T, finalLabels, hTS.trans hSR, hfinal⟩
termination_by (deeperHeadOrder (n + 1) k).length - idx

/-- Output of one complete headwise run. -/
structure HeadwiseTrichotomyResult
    {n k d r : Nat}
    (thetaLive thetaDial : Params (n + 1) k d) (h : Fin k)
    {D : HeadwiseSignRegion thetaDial h} where
  region : HeadwiseRestrictedRegion D
  labels : DeeperHead → TrichotomyLabel
  region_subset : region.region ⊆ D.region
  finalState : HeadwiseProcessingState r thetaLive thetaDial h
    (deeperHeadOrder (n + 1) k).length region labels

theorem exists_headwiseTrichotomyResult
    {n k d r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d} {h : Fin k}
    {D : HeadwiseSignRegion thetaDial h}
    (hA : ∀ a : Fin k,
      attentionMatrix thetaLive 0 a = attentionMatrix thetaDial 0 a)
    (hd : 2 ≤ d)
    (hdetC : (collapseMatrix thetaLive 0).det ≠ 0)
    (hdetA : (attentionMatrix thetaDial 0 h).det ≠ 0)
    (hsymA : sym (attentionMatrix thetaDial 0 h) ≠ 0)
    (hVne : valueMatrix thetaLive 0 h ≠ 0) :
    Nonempty (HeadwiseTrichotomyResult thetaLive thetaDial h (r := r) (D := D)) := by
  let initialLabels : DeeperHead → TrichotomyLabel :=
    fun _ ↦ KHead.TrichotomyLabel.alpha
  have hinit := headwiseProcessingState_zero r (h := h) (D := D)
    hA initialLabels
  rcases exists_headwiseFiniteFold (Nat.zero_le _) hinit hd hdetC hdetA
      hsymA hVne with ⟨R, labels, hsub, hfinal⟩
  exact ⟨⟨R, labels,
    hsub.trans (HeadwiseRestrictedRegion.full D).region_subset, hfinal⟩⟩

theorem HeadwiseTrichotomyResult.deeper_gate_expClose
    {n k d r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d} {h : Fin k}
    {D : HeadwiseSignRegion thetaDial h}
    (T : HeadwiseTrichotomyResult thetaLive thetaDial h (r := r) (D := D))
    (l : Fin (n + 1)) (hl : l ≠ 0) (a : Fin k)
    (p : HeadwiseSignPoint d) (hp : p ∈ T.region.region) :
    HeadwiseExpCloseTo
      (fun tau ↦ headwiseLiveAssignment r thetaLive thetaDial h p tau (l, a))
      (trichotomyLabelValue r
        (T.labels { layer := l.1 + 1, head := a.1 + 1 })) := by
  have hmem : formalVarDeeperHead (l, a) ∈
      processedPrefix (deeperHeadOrder (n + 1) k)
        (deeperHeadOrder (n + 1) k).length := by
    have hlpos : 0 < l.1 :=
      Nat.pos_of_ne_zero (by simpa using hl)
    simpa [KHead.processedPrefix] using
      (mk_mem_deeperHeadOrder (L := n + 1) (k := k)
        (layer := l.1 + 1) (head := a.1 + 1)
        (by omega) (by omega) (by omega) (by omega))
  have hest := T.finalState.estimate.processed_gate_expClose
    (l, a) hmem p hp
  rw [headwiseFrozenAssignment,
    tupleDialFrozenAssignment_deeper r (headwiseDialTuple h p.2)
      T.labels l a (Nat.pos_of_ne_zero (by simpa using hl))] at hest
  exact hest

/-- Exact compact-uniform export of the repaired headwise trichotomy.  One
coefficient, rate, and threshold work simultaneously for every deeper source
head and every base point in the chosen compact subset. -/
theorem HeadwiseTrichotomyResult.deeper_gates_compact_uniform
    {n k d r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d} {h : Fin k}
    {D : HeadwiseSignRegion thetaDial h}
    (T : HeadwiseTrichotomyResult thetaLive thetaDial h (r := r) (D := D))
    {K : Set (HeadwiseSignPoint d)} (hK : IsCompact K)
    (hKR : K ⊆ T.region.region) :
    ∃ eta C start : Real, 0 < eta ∧ 0 ≤ C ∧ 1 ≤ start ∧
      ∀ p ∈ K, ∀ tau : Real, start ≤ tau →
        ∀ l : Fin (n + 1), l ≠ 0 → ∀ a : Fin k,
          |headwiseLiveAssignment r thetaLive thetaDial h p tau (l, a) -
            trichotomyLabelValue r
              (T.labels { layer := l.1 + 1, head := a.1 + 1 })| ≤
            C * Real.exp (-eta * tau) := by
  rcases T.finalState.estimate.compact_uniform_gate_expClose K hK hKR with
    ⟨eta, C, start, heta, hC, hstart, hbound⟩
  refine ⟨eta, C, start, heta, hC, hstart, ?_⟩
  intro p hp tau htau l hl a
  have hmem : formalVarDeeperHead (l, a) ∈
      processedPrefix (deeperHeadOrder (n + 1) k)
        (deeperHeadOrder (n + 1) k).length := by
    have hlpos : 0 < l.1 := Nat.pos_of_ne_zero (by
      intro hz
      apply hl
      exact Fin.ext (by simpa using hz))
    simpa [KHead.processedPrefix] using
      (mk_mem_deeperHeadOrder (L := n + 1) (k := k)
        (layer := l.1 + 1) (head := a.1 + 1)
        (by omega) (by omega) (by omega) (by omega))
  have hb := hbound p hp tau htau (l, a) (Or.inr hmem)
  rw [headwiseFrozenAssignment,
    tupleDialFrozenAssignment_deeper r (headwiseDialTuple h p.2)
      T.labels l a (Nat.pos_of_ne_zero (by simpa using hl))] at hb
  exact hb

end

end TransformerIdentifiability.NLayer.NoSkip
