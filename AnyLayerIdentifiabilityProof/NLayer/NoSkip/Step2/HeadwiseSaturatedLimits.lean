import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Step2.HeadwiseTrichotomy
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Step2.GaugeExtraction

set_option autoImplicit false

open Filter Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.NoSkip

noncomputable section

/-! # Saturated limits for the repaired headwise dial -/

/-- The source saturated limit in one run.  Only first-layer head `h` is
dialled; all off-head first-layer gates are zero. -/
noncomputable def headwiseUnprimedSaturatedLimit {n k d : Nat} (r : Nat)
    (theta : Params (n + 1) k d) (h : Fin k)
    (labels : DeeperHead → TrichotomyLabel)
    (p : HeadwiseSignPoint d) : Vec d :=
  let S := saturatedData theta r labels
  (S.M * collapseMatrix theta ⟨0, Nat.succ_pos n⟩) *ᵥ p.1.2 +
    (S.E * collapseMatrix theta ⟨0, Nat.succ_pos n⟩ +
      p.2 • (S.K * valueMatrix theta ⟨0, Nat.succ_pos n⟩ h)) *ᵥ p.1.1

/-- The target saturated limit in one run.  Every target deeper gate and all
off-head first-layer gates tend to zero. -/
noncomputable def headwisePrimedZeroSaturatedLimit {n k d : Nat}
    (theta : Params (n + 1) k d) (h : Fin k)
    (p : HeadwiseSignPoint d) : Vec d :=
  let S := primedZeroSaturatedData theta
  (S.M * collapseMatrix theta ⟨0, Nat.succ_pos n⟩) *ᵥ p.1.2 +
    (p.2 • (S.M * valueMatrix theta ⟨0, Nat.succ_pos n⟩ h)) *ᵥ p.1.1

theorem sum_headwiseDialTuple_smul_matrix {k d : Nat}
    (h : Fin k) (t : Real) (B : Fin k → Matrix (Fin d) (Fin d) Real) :
    (∑ a : Fin k, headwiseDialTuple h t a • B a) = t • B h := by
  classical
  rw [Finset.sum_eq_single h]
  · rw [headwiseDialTuple_self]
  · intro a _ ha
    rw [headwiseDialTuple_of_ne ha, zero_smul]
  · simp

theorem multiDialUnprimedSaturatedLimit_headwise {n k d : Nat} (r : Nat)
    (theta : Params (n + 1) k d) (h : Fin k)
    (labels : DeeperHead → TrichotomyLabel)
    (p : HeadwiseSignPoint d) :
    multiDialUnprimedSaturatedLimit r theta labels
        (p.1, headwiseDialTuple h p.2) =
      headwiseUnprimedSaturatedLimit r theta h labels p := by
  simp only [multiDialUnprimedSaturatedLimit,
    headwiseUnprimedSaturatedLimit]
  rw [sum_headwiseDialTuple_smul_matrix]

theorem multiDialPrimedZeroSaturatedLimit_headwise {n k d : Nat}
    (theta : Params (n + 1) k d) (h : Fin k)
    (p : HeadwiseSignPoint d) :
    multiDialPrimedZeroSaturatedLimit theta
        (p.1, headwiseDialTuple h p.2) =
      headwisePrimedZeroSaturatedLimit theta h p := by
  simp only [multiDialPrimedZeroSaturatedLimit,
    headwisePrimedZeroSaturatedLimit]
  rw [sum_headwiseDialTuple_smul_matrix]

/-- Every source gate converges to the frozen family supplied by the completed
headwise trichotomy. -/
theorem HeadwiseTrichotomyResult.source_gate_tendsto
    {n k d r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d} {h : Fin k}
    {D : HeadwiseSignRegion thetaDial h}
    (T : HeadwiseTrichotomyResult thetaLive thetaDial h (r := r) (D := D))
    (p : HeadwiseSignPoint d) (hp : p ∈ T.region.region) :
    ∀ l : Fin (n + 1), ∀ a : Fin k,
      Tendsto (fun tau => actualProbeGate r thetaLive
          (headwiseDialPath r thetaDial h p tau).1
          (headwiseDialPath r thetaDial h p tau).2 tau l a)
        atTop
        (nhds (tupleDialFrozenFamily r (headwiseDialTuple h p.2)
          T.labels l a)) := by
  intro l a
  change Tendsto
    (fun tau => headwiseLiveAssignment r thetaLive thetaDial h p tau (l, a))
    atTop _
  by_cases hl : l = ⟨0, Nat.succ_pos n⟩
  · subst l
    simpa [headwiseFrozenAssignment] using
      (T.finalState.estimate.firstLayer_gate_expClose a p hp).tendsto
  · have hclose := T.deeper_gate_expClose l hl a p hp
    simpa [tupleDialFrozenFamily_deeper r (headwiseDialTuple h p.2)
      T.labels l a (Fin.pos_iff_ne_zero.mpr hl)] using hclose.tendsto

/-- Source output convergence to the explicit headwise saturated formula. -/
theorem HeadwiseTrichotomyResult.tendsto_source_output
    {n k d r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d} {h : Fin k}
    {D : HeadwiseSignRegion thetaDial h}
    (T : HeadwiseTrichotomyResult thetaLive thetaDial h (r := r) (D := D))
    (p : HeadwiseSignPoint d) (hp : p ∈ T.region.region) :
    Tendsto (fun tau => probeOutput r thetaLive
        (headwiseDialPath r thetaDial h p tau).1
        (headwiseDialPath r thetaDial h p tau).2 tau)
      atTop (nhds (headwiseUnprimedSaturatedLimit r thetaLive h T.labels p)) := by
  have hpath := tendsto_headwiseDialPath_atTop r thetaDial h p
  have hout := tendsto_probeOutput_frozen r thetaLive
    (fun tau => (headwiseDialPath r thetaDial h p tau).1)
    (fun tau => (headwiseDialPath r thetaDial h p tau).2) id
    p.1.1 p.1.2
    (tupleDialFrozenFamily r (headwiseDialTuple h p.2) T.labels)
    (continuous_fst.tendsto p.1 |>.comp hpath)
    (continuous_snd.tendsto p.1 |>.comp hpath)
    (T.source_gate_tendsto p hp)
  have hclosed := (frozenPoint_closed thetaLive
    (tupleDialFrozenFamily r (headwiseDialTuple h p.2) T.labels)
    p.1.1 p.1.2 (n + 1) le_rfl).2
  have hformula := frozenPoint_tupleDial_saturated_formula r thetaLive
    (headwiseDialTuple h p.2) T.labels p.1.1 p.1.2
  have hlimit :
      frozenP thetaLive
          (tupleDialFrozenFamily r (headwiseDialTuple h p.2) T.labels)
          (n + 1) le_rfl *ᵥ p.1.2 +
        frozenQ thetaLive
          (tupleDialFrozenFamily r (headwiseDialTuple h p.2) T.labels)
          (n + 1) le_rfl *ᵥ p.1.1 =
        headwiseUnprimedSaturatedLimit r thetaLive h T.labels p := by
    rw [← hclosed, hformula]
    rw [← multiDialUnprimedSaturatedLimit_headwise]
    rfl
  rw [hlimit] at hout
  simpa using hout

/-- Pointwise target gate convergence for the repaired headwise path. -/
theorem tendsto_headwise_primed_all_gates_zeroTail
    {n k d : Nat} (r : Nat)
    {theta : Params (n + 1) k d} {h : Fin k}
    (D : HeadwiseSignRegion theta h)
    (p : HeadwiseSignPoint d) (hp : p ∈ D.region) :
    ∀ l : Fin (n + 1), ∀ a : Fin k,
      Tendsto (fun tau => actualProbeGate r theta
          (headwiseDialPath r theta h p tau).1
          (headwiseDialPath r theta h p tau).2 tau l a)
        atTop (nhds (tupleDialFrozenFamily r (headwiseDialTuple h p.2)
          tupleZeroLabels l a)) := by
  intro l a
  by_cases hl0 : l = ⟨0, Nat.succ_pos n⟩
  · subst l
    by_cases ha : a = h
    · subst a
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ne_atTop (0 : Real)] with tau htau
      let bp : HeadwiseDialBasePoint D := ⟨p, hp⟩
      rw [tupleDialFrozenFamily_first, headwiseDialTuple_self]
      simpa [bp] using (bp.firstLayer_gate_eq r htau).symm
    · obtain ⟨eta, C, T, heta, hC, hT, hbound⟩ :=
        exists_uniform_headwise_offHead_zero_saturation r D
          (K := {p}) isCompact_singleton (Set.singleton_nonempty p) (by simpa)
      have hhalf : 0 < eta / 2 := by linarith
      have henv : Tendsto
          (fun tau : Real => C * Real.exp (-(eta / 2) * tau))
          atTop (nhds 0) := by
        have hexp : Tendsto (fun tau : Real => Real.exp (-(eta / 2) * tau))
            atTop (nhds 0) := by
          have hs : Tendsto (fun tau : Real => (eta / 2) * tau) atTop atTop :=
            tendsto_id.const_mul_atTop hhalf
          simpa only [neg_mul] using
            Real.tendsto_exp_neg_atTop_nhds_zero.comp hs
        simpa using hexp.const_mul C
      rw [tupleDialFrozenFamily_first, headwiseDialTuple_of_ne ha]
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
        tendsto_const_nhds henv
      · filter_upwards with tau
        rw [actualProbeGate_eq_sig]
        exact (sig_pos _).le
      · filter_upwards [eventually_ge_atTop T] with tau htau
        exact (hbound p (Set.mem_singleton p) a ha tau htau).2
  · obtain ⟨eta, T, heta, hT, hbound⟩ :=
      exists_uniform_headwise_primed_zero_saturation r D
        (K := {p}) isCompact_singleton (Set.singleton_nonempty p) (by simpa)
    have hhalf : 0 < eta / 2 := by linarith
    have henv : Tendsto
        (fun tau : Real => Real.exp (logScale r) *
          Real.exp (-(eta / 2) * tau)) atTop (nhds 0) := by
      have hexp : Tendsto (fun tau : Real => Real.exp (-(eta / 2) * tau))
          atTop (nhds 0) := by
        have hs : Tendsto (fun tau : Real => (eta / 2) * tau) atTop atTop :=
          tendsto_id.const_mul_atTop hhalf
        simpa only [neg_mul] using
          Real.tendsto_exp_neg_atTop_nhds_zero.comp hs
      simpa using hexp.const_mul (Real.exp (logScale r))
    have hlne : l ≠ 0 := by simpa using hl0
    rw [tupleDialFrozenFamily_zeroLabels_deeper r
      (headwiseDialTuple h p.2) l a (Fin.pos_iff_ne_zero.mpr hlne)]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds henv
    · filter_upwards with tau
      rw [actualProbeGate_eq_sig]
      exact (sig_pos _).le
    · filter_upwards [eventually_ge_atTop T] with tau htau
      exact hbound p (Set.mem_singleton p) tau htau l hlne a

/-- Target output convergence to its all-zero-tail headwise formula. -/
theorem tendsto_headwise_primedZero_output
    {n k d : Nat} (r : Nat)
    {theta : Params (n + 1) k d} {h : Fin k}
    (D : HeadwiseSignRegion theta h)
    (p : HeadwiseSignPoint d) (hp : p ∈ D.region) :
    Tendsto (fun tau => probeOutput r theta
        (headwiseDialPath r theta h p tau).1
        (headwiseDialPath r theta h p tau).2 tau)
      atTop (nhds (headwisePrimedZeroSaturatedLimit theta h p)) := by
  have hpath := tendsto_headwiseDialPath_atTop r theta h p
  have hout := tendsto_probeOutput_frozen r theta
    (fun tau => (headwiseDialPath r theta h p tau).1)
    (fun tau => (headwiseDialPath r theta h p tau).2) id
    p.1.1 p.1.2
    (tupleDialFrozenFamily r (headwiseDialTuple h p.2) tupleZeroLabels)
    (continuous_fst.tendsto p.1 |>.comp hpath)
    (continuous_snd.tendsto p.1 |>.comp hpath)
    (tendsto_headwise_primed_all_gates_zeroTail r D p hp)
  have hclosed := (frozenPoint_closed theta
    (tupleDialFrozenFamily r (headwiseDialTuple h p.2) tupleZeroLabels)
    p.1.1 p.1.2 (n + 1) le_rfl).2
  have hformula := frozenPoint_tupleDial_saturated_formula r theta
    (headwiseDialTuple h p.2) tupleZeroLabels p.1.1 p.1.2
  have hlimit :
      frozenP theta
          (tupleDialFrozenFamily r (headwiseDialTuple h p.2) tupleZeroLabels)
          (n + 1) le_rfl *ᵥ p.1.2 +
        frozenQ theta
          (tupleDialFrozenFamily r (headwiseDialTuple h p.2) tupleZeroLabels)
          (n + 1) le_rfl *ᵥ p.1.1 =
        headwisePrimedZeroSaturatedLimit theta h p := by
    rw [← hclosed, hformula]
    rw [← multiDialPrimedZeroSaturatedLimit_headwise,
      ← multiDialUnprimed_zeroLabels_eq_primedZero]
    rfl
  rw [hlimit] at hout
  simpa using hout

/-- Equality of the finite realizations identifies the two headwise limits. -/
theorem HeadwiseTrichotomyResult.saturatedLimits_eq
    {n k d r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d} {h : Fin k}
    {D : HeadwiseSignRegion thetaDial h}
    (T : HeadwiseTrichotomyResult thetaLive thetaDial h (r := r) (D := D))
    (p : HeadwiseSignPoint d) (hp : p ∈ T.region.region)
    (hEq : ∀ w v : Vec d, ∀ tau : Real, 0 < tau →
      probeOutput r thetaLive w v tau = probeOutput r thetaDial w v tau) :
    headwiseUnprimedSaturatedLimit r thetaLive h T.labels p =
      headwisePrimedZeroSaturatedLimit thetaDial h p := by
  have hs := T.tendsto_source_output p hp
  have ht := tendsto_headwise_primedZero_output r D p (T.region.region_subset hp)
  apply tendsto_nhds_unique_of_eventuallyEq hs ht
  filter_upwards [eventually_gt_atTop (0 : Real)] with tau htau
  exact hEq _ _ tau htau

end

end TransformerIdentifiability.NLayer.NoSkip
