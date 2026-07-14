import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Step2.HeadwiseDial
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Step2.DialLimits

set_option autoImplicit false

open Matrix Filter
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.NoSkip

noncomputable section

/-! # Polynomial estimates along the repaired scalar dial -/

theorem exists_uniform_allSlopeBoxLip_headwiseDialPath
    {n k d : Nat} (r : Nat) {theta : Params (n + 1) k d}
    {h : Fin k} (D : HeadwiseSignRegion theta h)
    {K : Set (HeadwiseSignPoint d)} (hK : IsCompact K)
    (hKD : K ⊆ D.region) :
    ∃ B : Real, 0 ≤ B ∧ ∀ p ∈ K, ∀ tau : Real, 1 ≤ tau →
      allSlopeBoxLip theta (headwiseDialPath r theta h p tau) ≤ B := by
  let S : Set (HeadwiseSignPoint d × Real) := K ×ˢ Set.Icc (0 : Real) 1
  let F : HeadwiseSignPoint d × Real → Vec d × Vec d := fun z =>
    (z.1.1.1, z.1.1.2 + z.2 •
      headwiseDialDirection r theta h z.1.1.1 z.1.2)
  have hdir : ContinuousOn (fun z : HeadwiseSignPoint d × Real =>
      headwiseDialDirection r theta h z.1.1.1 z.1.2) S :=
    (continuousOn_headwiseDialDirection_region r D).comp continuousOn_fst
      (fun z hz => hKD hz.1)
  have hF : ContinuousOn F S := by
    apply ContinuousOn.prodMk
    · exact ((continuous_fst.comp continuous_fst).comp continuous_fst).continuousOn
    · exact (((continuous_snd.comp continuous_fst).comp continuous_fst).continuousOn).add
        (continuousOn_snd.smul hdir)
  have hSc : IsCompact S := hK.prod isCompact_Icc
  have hcont : ContinuousOn (fun z => allSlopeBoxLip theta (F z)) S :=
    (continuous_allSlopeBoxLip theta).comp_continuousOn hF
  rcases hSc.bddAbove_image hcont with ⟨B, hB⟩
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro p hp tau htau
  have htau0 : 0 < tau := lt_of_lt_of_le zero_lt_one htau
  have hinv : tau⁻¹ ∈ Set.Icc (0 : Real) 1 :=
    ⟨inv_nonneg.mpr htau0.le, (inv_le_one₀ htau0).2 htau⟩
  have hz : (p, tau⁻¹) ∈ S := ⟨hp, hinv⟩
  have heq : F (p, tau⁻¹) = headwiseDialPath r theta h p tau := rfl
  rw [← heq]
  exact le_trans (hB ⟨(p, tau⁻¹), hz, rfl⟩) (le_max_left _ _)

theorem continuous_headwiseLevelGradient {n k d : Nat}
    (theta : Params (n + 1) k d) (h : Fin k)
    (jb : LevelRowIndex (n + 1) k) :
    Continuous (fun p : HeadwiseSignPoint d =>
      levelGradient theta (headwiseDialTuple h p.2) p.1.1 jb) := by
  unfold levelGradient dialContrast
  simp_rw [dialValueMatrix_headwiseDialTuple]
  fun_prop

theorem exists_uniform_levelGradient_bound_headwise
    {n k d : Nat} (theta : Params (n + 1) k d) (h : Fin k)
    {K : Set (HeadwiseSignPoint d)} (hK : IsCompact K) :
    ∃ G : Real, 0 ≤ G ∧ ∀ p ∈ K,
      ∀ jb : LevelRowIndex (n + 1) k,
        ‖levelGradient theta (headwiseDialTuple h p.2) p.1.1 jb‖ ≤ G := by
  let g : HeadwiseSignPoint d → Real := fun p =>
    ∑ jb : LevelRowIndex (n + 1) k,
      ‖levelGradient theta (headwiseDialTuple h p.2) p.1.1 jb‖
  have hg : Continuous g := by
    classical
    unfold g
    exact continuous_finsetSum _ fun jb _ =>
      continuous_norm.comp (continuous_headwiseLevelGradient theta h jb)
  rcases hK.bddAbove_image hg.continuousOn with ⟨G, hG⟩
  refine ⟨max G 0, le_max_right _ _, ?_⟩
  intro p hp jb
  have hsingle :
      ‖levelGradient theta (headwiseDialTuple h p.2) p.1.1 jb‖ ≤ g p := by
    classical
    exact Finset.single_le_sum (fun i _ => norm_nonneg _)
      (Finset.mem_univ jb)
  exact le_trans hsingle
    (le_trans (hG ⟨p, hp, rfl⟩) (le_max_left _ _))

theorem exists_uniform_headwise_levelRow_margin
    {n k d : Nat} {theta : Params (n + 1) k d}
    {h : Fin k} (D : HeadwiseSignRegion theta h)
    {K : Set (HeadwiseSignPoint d)} (hK : IsCompact K)
    (hKne : K.Nonempty) (hKD : K ⊆ D.region) :
    ∃ eta : Real, 0 < eta ∧ ∀ p ∈ K,
      ∀ jb : LevelRowIndex (n + 1) k,
        levelRow theta (headwiseDialTuple h p.2) p.1.1 jb p.1.2 ≤ -eta := by
  by_cases hk : k = 0
  · subst k
    exact Fin.elim0 h
  by_cases hn : n = 0
  · subst n
    exact ⟨1, zero_lt_one, fun _ _ jb => Fin.elim0 jb.1⟩
  let S : Set Real := ⋃ jb : LevelRowIndex (n + 1) k,
    (fun p : HeadwiseSignPoint d =>
      levelRow theta (headwiseDialTuple h p.2) p.1.1 jb p.1.2) '' K
  have hSc : IsCompact S := by
    apply isCompact_iUnion
    intro jb
    have hc : Continuous (fun p : HeadwiseSignPoint d =>
        levelRow theta (headwiseDialTuple h p.2) p.1.1 jb p.1.2) := by
      simpa [headwiseStrictValue] using
        (continuous_headwiseStrictValue theta h (Sum.inr jb)).neg
    exact hK.image hc
  have hSne : S.Nonempty := by
    rcases hKne with ⟨p, hp⟩
    let jb : LevelRowIndex (n + 1) k :=
      (⟨0, Nat.pos_of_ne_zero hn⟩, ⟨0, Nat.pos_of_ne_zero hk⟩)
    exact ⟨_, Set.mem_iUnion.2 ⟨jb, p, hp, rfl⟩⟩
  obtain ⟨M, hMS, hMmax⟩ := hSc.exists_isGreatest hSne
  have hMneg : M < 0 := by
    rcases Set.mem_iUnion.1 hMS with ⟨jb, p, hp, rfl⟩
    exact D.deeper_negative (hKD hp) jb
  refine ⟨-M, by linarith, ?_⟩
  intro p hp jb
  simpa using hMmax (Set.mem_iUnion.2 ⟨jb, p, hp, rfl⟩)

/-! ## Target all-zero saturation -/

/-- Every target deeper slope stays uniformly negative along the repaired
headwise path.  The proof differs from the simultaneous theorem precisely in
the first-layer telescope: head `h` is exact and all off-head coordinates are
exponentially small. -/
theorem exists_uniform_headwise_primed_slope_bound
    {n k d : Nat} (r : Nat) {theta : Params (n + 1) k d}
    {h : Fin k} (D : HeadwiseSignRegion theta h)
    {K : Set (HeadwiseSignPoint d)} (hK : IsCompact K)
    (hKne : K.Nonempty) (hKD : K ⊆ D.region) :
    ∃ eta T : Real, 0 < eta ∧ 1 ≤ T ∧
      ∀ p ∈ K, ∀ tau : Real, T ≤ tau →
        ∀ l : Fin (n + 1), l ≠ 0 → ∀ a : Fin k,
          actualProbeSlope r theta
            (headwiseDialPath r theta h p tau).1
            (headwiseDialPath r theta h p tau).2 tau l a ≤ -(eta / 2) := by
  obtain ⟨eta, heta, hmargin⟩ :=
    exists_uniform_headwise_levelRow_margin D hK hKne hKD
  obtain ⟨etaOff, COff, TOff, hetaOff, hCOff, hTOff, hoff⟩ :=
    exists_uniform_headwise_offHead_zero_saturation r D hK hKne hKD
  obtain ⟨C, hC, hmotion⟩ :=
    exists_uniform_headwiseDialPath_motion_bound r D hK hKD
  obtain ⟨B, hB, hLip⟩ :=
    exists_uniform_allSlopeBoxLip_headwiseDialPath r D hK hKD
  obtain ⟨G, hG, hgrad⟩ :=
    exists_uniform_levelGradient_bound_headwise theta h hK
  let mu : Real := min (eta / 2) (etaOff / 2)
  have hmu : 0 < mu := lt_min (by linarith) (by linarith)
  have hmuEta : mu ≤ eta / 2 := min_le_left _ _
  have hmuOff : mu ≤ etaOff / 2 := min_le_right _ _
  let N : Real := Fintype.card (FormalVar (n + 1) k)
  let E : Real := max (Real.exp (logScale r)) COff
  have hE : 0 ≤ E := le_trans (Real.exp_nonneg _) (le_max_left _ _)
  have hEexp : Real.exp (logScale r) ≤ E := le_max_left _ _
  have hECOff : COff ≤ E := le_max_right _ _
  let A : Real := N * B * (N * E)
  let H : Real := (d : Real) * G * C
  let err : Real → Real := fun tau =>
    A * Real.exp (-mu * tau) + H * tau⁻¹
  have hexp0 : Tendsto (fun tau : Real => Real.exp (-mu * tau))
      atTop (nhds 0) := by
    have hs : Tendsto (fun tau : Real => mu * tau) atTop atTop :=
      tendsto_id.const_mul_atTop hmu
    have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp hs
    simpa only [neg_mul] using hh
  have herr : Tendsto err atTop (nhds 0) := by
    simpa [err] using (hexp0.const_mul A).add
      ((tendsto_inv_atTop_zero (𝕜 := Real)).const_mul H)
  have hetaHalf : 0 < eta / 2 := by linarith
  obtain ⟨TErr, hTErr⟩ :=
    (Metric.tendsto_atTop.mp herr) (eta / 2) hetaHalf
  let T : Real := max 1 (max TOff TErr)
  have hTone : 1 ≤ T := le_max_left _ _
  have hTOffT : TOff ≤ T :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hTErrT : TErr ≤ T :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨eta, T, heta, hTone, ?_⟩
  intro p hp tau htau
  have htau1 : 1 ≤ tau := le_trans hTone htau
  have htau0 : 0 < tau := lt_of_lt_of_le zero_lt_one htau1
  have htauOff : TOff ≤ tau := le_trans hTOffT htau
  have htauErr : TErr ≤ tau := le_trans hTErrT htau
  have herrSmall : err tau < eta / 2 := by
    have hd := hTErr tau htauErr
    rw [Real.dist_eq, sub_zero] at hd
    exact lt_of_le_of_lt (le_abs_self (err tau)) hd
  let live : FormalAssignment (n + 1) k :=
    actualProbeGateAssignment r theta
      (headwiseDialPath r theta h p tau).1
      (headwiseDialPath r theta h p tau).2 tau
  let frozen : FormalAssignment (n + 1) k :=
    tupleDialFrozenAssignment r (headwiseDialTuple h p.2) tupleZeroLabels
  have hlive : ∀ x, |live x| ≤ 1 := by
    intro x
    change |actualProbeGate r theta _ _ tau x.1 x.2| ≤ 1
    rw [actualProbeGate_eq_sig, abs_of_nonneg (sig_pos _).le]
    exact sig_le_one _
  have hfrozen : ∀ x, |frozen x| ≤ 1 := by
    rintro ⟨l, a⟩
    change |tupleDialFrozenFamily r (headwiseDialTuple h p.2)
      tupleZeroLabels l a| ≤ 1
    by_cases hl0 : l.1 = 0
    · have hl : l = ⟨0, Nat.succ_pos n⟩ := Fin.ext (by simpa using hl0)
      subst l
      rw [tupleDialFrozenFamily_first]
      by_cases ha : a = h
      · subst a
        rw [headwiseDialTuple_self, abs_of_pos
          ((D.region_subset_slab (hKD hp)).2).1]
        exact ((D.region_subset_slab (hKD hp)).2).2.le
      · rw [headwiseDialTuple_of_ne ha, abs_zero]
        exact zero_le_one
    · rw [tupleDialFrozenFamily_zeroLabels_deeper r
        (headwiseDialTuple h p.2) l a (Nat.pos_of_ne_zero hl0), abs_zero]
      exact zero_le_one
  suffices hcore : ∀ q : Nat, (hq : q < n) → ∀ a : Fin k,
      actualProbeSlope r theta
        (headwiseDialPath r theta h p tau).1
        (headwiseDialPath r theta h p tau).2 tau
        ⟨q + 1, Nat.succ_lt_succ hq⟩ a ≤ -(eta / 2) by
    intro l hl a
    have hlpos : 0 < l.1 := Nat.pos_of_ne_zero (by
      intro hz
      apply hl
      exact Fin.ext (by simpa using hz))
    obtain ⟨q, hqeq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hlpos)
    have hq : q < n := by omega
    have hlq : l = (⟨q + 1, by omega⟩ : Fin (n + 1)) := Fin.ext hqeq
    rw [hlq]
    exact hcore q hq a
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
    intro hq a
    let lq : Fin (n + 1) := ⟨q + 1, by omega⟩
    let jb : LevelRowIndex (n + 1) k := (⟨q, hq⟩, a)
    have hfirstGate : ∀ b : Fin k,
        |live (⟨0, Nat.succ_pos n⟩, b) -
          frozen (⟨0, Nat.succ_pos n⟩, b)| ≤
          E * Real.exp (-mu * tau) := by
      intro b
      by_cases hb : b = h
      · subst b
        have heq := (⟨p, hKD hp⟩ : HeadwiseDialBasePoint D).firstLayer_gate_eq
          r htau0.ne'
        change |actualProbeGate r theta _ _ tau ⟨0, Nat.succ_pos n⟩ h -
          tupleDialFrozenAssignment r (headwiseDialTuple h p.2)
            tupleZeroLabels (⟨0, Nat.succ_pos n⟩, h)| ≤ _
        rw [heq, tupleDialFrozenAssignment_first,
          headwiseDialTuple_self, sub_self, abs_zero]
        positivity
      · have hgate := (hoff p hp b hb tau htauOff).2
        change |actualProbeGate r theta _ _ tau ⟨0, Nat.succ_pos n⟩ b -
          tupleDialFrozenAssignment r (headwiseDialTuple h p.2)
            tupleZeroLabels (⟨0, Nat.succ_pos n⟩, b)| ≤ _
        rw [tupleDialFrozenAssignment_first, headwiseDialTuple_of_ne hb,
          sub_zero, abs_of_nonneg (by
            rw [actualProbeGate_eq_sig]
            exact (sig_pos _).le)]
        calc
          actualProbeGate r theta _ _ tau ⟨0, Nat.succ_pos n⟩ b
              ≤ COff * Real.exp (-(etaOff / 2) * tau) := hgate
          _ ≤ E * Real.exp (-mu * tau) := by
            apply mul_le_mul hECOff
            · apply Real.exp_le_exp.mpr
              have := hmuOff
              nlinarith
            · exact Real.exp_nonneg _
            · exact hE
    have hpriorGate : ∀ x : FormalVar (n + 1) k,
        0 < x.1.1 → x.1.1 < q + 1 →
        |live x - frozen x| ≤ E * Real.exp (-mu * tau) := by
      rintro ⟨lx, b⟩ hlx hxq
      have hzero : frozen (lx, b) = 0 := by
        change tupleDialFrozenAssignment r (headwiseDialTuple h p.2)
          tupleZeroLabels (lx, b) = 0
        rw [tupleDialFrozenAssignment_deeper r (headwiseDialTuple h p.2)
          tupleZeroLabels lx b hlx]
        rfl
      change |actualProbeGate r theta _ _ tau lx b - frozen (lx, b)| ≤ _
      rw [hzero, sub_zero, abs_of_nonneg (by
        rw [actualProbeGate_eq_sig]
        exact (sig_pos _).le)]
      obtain ⟨u, hueq⟩ :=
        Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hlx)
      have huq : u < q := by omega
      have hun : u < n := lt_trans huq hq
      have hs := ih u huq hun b
      have hlxu : lx = (⟨u + 1, by omega⟩ : Fin (n + 1)) := Fin.ext hueq
      rw [hlxu]
      have hg := actualProbeGate_le_exp_of_slope_le_neg r theta
        (headwiseDialPath r theta h p tau).1
        (headwiseDialPath r theta h p tau).2 tau (eta / 2)
        ⟨u + 1, by omega⟩ b htau0.le hs
      calc
        actualProbeGate r theta _ _ tau ⟨u + 1, by omega⟩ b
            ≤ Real.exp (logScale r) *
              Real.exp (-(eta / 2) * tau) := hg
        _ ≤ E * Real.exp (-mu * tau) := by
          apply mul_le_mul hEexp
          · apply Real.exp_le_exp.mpr
            have := hmuEta
            nlinarith
          · exact Real.exp_nonneg _
          · exact hE
    have hsum :
        (∑ x ∈ (Finset.univ : Finset (FormalVar (n + 1) k)),
          if x.1.1 < lq.1 then |live x - frozen x| else 0) ≤
        N * (E * Real.exp (-mu * tau)) := by
      calc
        _ ≤ ∑ _x ∈ (Finset.univ : Finset (FormalVar (n + 1) k)),
            E * Real.exp (-mu * tau) := by
          refine Finset.sum_le_sum ?_
          intro x _
          by_cases hxl : x.1.1 < lq.1
          · rw [if_pos hxl]
            by_cases hx0 : x.1.1 = 0
            · rcases x with ⟨xl, xb⟩
              have hxl0 : xl = ⟨0, Nat.succ_pos n⟩ :=
                Fin.ext (by simpa using hx0)
              subst xl
              exact hfirstGate xb
            · exact hpriorGate x (Nat.pos_of_ne_zero hx0)
                (by simpa [lq] using hxl)
          · rw [if_neg hxl]
            positivity
        _ = N * (E * Real.exp (-mu * tau)) := by simp [N]
    have htel := formalSlope_eval_sub_eval_le_telescope theta
      (headwiseDialPath r theta h p tau) lq a live frozen hlive hfrozen
    have hlen : ((formalVarsBelow (n + 1) k lq.1).length : Real) ≤ N := by
      dsimp [N]
      exact_mod_cast
        (nodup_formalVarsBelow (n + 1) k lq.1).length_le_card
    have hpoly :
        |MvPolynomial.eval live
            (formalSlope theta (headwiseDialPath r theta h p tau).1
              (headwiseDialPath r theta h p tau).2 lq a) -
          MvPolynomial.eval frozen
            (formalSlope theta (headwiseDialPath r theta h p tau).1
              (headwiseDialPath r theta h p tau).2 lq a)| ≤
          A * Real.exp (-mu * tau) := by
      calc
        _ ≤ ((formalVarsBelow (n + 1) k lq.1).length : Real) *
            allSlopeBoxLip theta (headwiseDialPath r theta h p tau) *
              (∑ x ∈ (Finset.univ : Finset (FormalVar (n + 1) k)),
                if x.1.1 < lq.1 then |live x - frozen x| else 0) := htel
        _ ≤ N * B * (N * (E * Real.exp (-mu * tau))) := by
          have hN : 0 ≤ N := by positivity
          have hP : 0 ≤ allSlopeBoxLip theta
              (headwiseDialPath r theta h p tau) :=
            allSlopeBoxLip_nonneg theta _
          have hS : 0 ≤ (∑ x ∈
              (Finset.univ : Finset (FormalVar (n + 1) k)),
              if x.1.1 < lq.1 then |live x - frozen x| else 0) := by
            positivity
          calc
            _ ≤ N * allSlopeBoxLip theta
                (headwiseDialPath r theta h p tau) *
                (∑ x ∈ (Finset.univ : Finset (FormalVar (n + 1) k)),
                  if x.1.1 < lq.1 then |live x - frozen x| else 0) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hlen hP) hS
            _ ≤ N * B *
                (∑ x ∈ (Finset.univ : Finset (FormalVar (n + 1) k)),
                  if x.1.1 < lq.1 then |live x - frozen x| else 0) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left
                  (hLip p hp tau htau1) hN) hS
            _ ≤ N * B * (N * (E * Real.exp (-mu * tau))) :=
              mul_le_mul_of_nonneg_left hsum (mul_nonneg hN hB)
        _ = A * Real.exp (-mu * tau) := by
          simp [A]
          ring
    have hfrozenEval : MvPolynomial.eval frozen
        (formalSlope theta (headwiseDialPath r theta h p tau).1
          (headwiseDialPath r theta h p tau).2 lq a) =
        levelRow theta (headwiseDialTuple h p.2) p.1.1 jb
          (headwiseDialPath r theta h p tau).2 := by
      simpa [frozen, lq, jb] using
        (eval_formalSlope_tupleDialFrozenAssignment_zero r theta
          (headwiseDialTuple h p.2)
          (headwiseDialPath r theta h p tau).1
          (headwiseDialPath r theta h p tau).2 jb)
    have hactualEval : MvPolynomial.eval live
        (formalSlope theta (headwiseDialPath r theta h p tau).1
          (headwiseDialPath r theta h p tau).2 lq a) =
        actualProbeSlope r theta
          (headwiseDialPath r theta h p tau).1
          (headwiseDialPath r theta h p tau).2 tau lq a :=
      eval_formalSlope_actualProbeGateAssignment r theta _ _ tau lq a
    have hmove :
        |levelRow theta (headwiseDialTuple h p.2) p.1.1 jb
            (headwiseDialPath r theta h p tau).2 -
          levelRow theta (headwiseDialTuple h p.2) p.1.1 jb p.1.2| ≤
          H * tau⁻¹ := by
      rw [levelRow_eq_dotProduct_add_constant,
        levelRow_eq_dotProduct_add_constant]
      have heq :
          dotProduct (levelGradient theta (headwiseDialTuple h p.2) p.1.1 jb)
              (headwiseDialPath r theta h p tau).2 +
                levelConstant theta (headwiseDialTuple h p.2) p.1.1 jb -
            (dotProduct (levelGradient theta (headwiseDialTuple h p.2) p.1.1 jb)
                p.1.2 +
              levelConstant theta (headwiseDialTuple h p.2) p.1.1 jb) =
            dotProduct (levelGradient theta (headwiseDialTuple h p.2) p.1.1 jb)
              ((headwiseDialPath r theta h p tau).2 - p.1.2) := by
        calc
          _ = dotProduct
                (levelGradient theta (headwiseDialTuple h p.2) p.1.1 jb)
                (headwiseDialPath r theta h p tau).2 -
              dotProduct
                (levelGradient theta (headwiseDialTuple h p.2) p.1.1 jb)
                p.1.2 := by ring
          _ = ∑ i : Fin d,
              (levelGradient theta (headwiseDialTuple h p.2) p.1.1 jb i *
                  (headwiseDialPath r theta h p tau).2 i -
                levelGradient theta (headwiseDialTuple h p.2) p.1.1 jb i *
                  p.1.2 i) := by
            simp only [dotProduct, Finset.sum_sub_distrib]
          _ = _ := by
            apply Finset.sum_congr rfl
            intro i _
            simp [Pi.sub_apply]
            ring
      rw [heq]
      calc
        |dotProduct (levelGradient theta (headwiseDialTuple h p.2) p.1.1 jb)
            ((headwiseDialPath r theta h p tau).2 - p.1.2)| ≤
            (d : Real) *
              ‖levelGradient theta (headwiseDialTuple h p.2) p.1.1 jb‖ *
              ‖(headwiseDialPath r theta h p tau).2 - p.1.2‖ :=
          abs_dotProduct_le_card_mul_norm _ _
        _ ≤ (d : Real) * G * (C / tau) := by
          have hd0 : 0 ≤ (d : Real) := by positivity
          have hdelta0 : 0 ≤
              ‖(headwiseDialPath r theta h p tau).2 - p.1.2‖ := norm_nonneg _
          calc
            _ ≤ (d : Real) * G *
                ‖(headwiseDialPath r theta h p tau).2 - p.1.2‖ :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (hgrad p hp jb) hd0) hdelta0
            _ ≤ (d : Real) * G * (C / tau) :=
              mul_le_mul_of_nonneg_left (hmotion p hp tau htau1)
                (mul_nonneg hd0 hG)
        _ = H * tau⁻¹ := by
          simp [H, div_eq_mul_inv]
          ring
    have hbase := hmargin p hp jb
    rw [hactualEval, hfrozenEval] at hpoly
    have htotal : actualProbeSlope r theta
          (headwiseDialPath r theta h p tau).1
          (headwiseDialPath r theta h p tau).2 tau lq a ≤
        levelRow theta (headwiseDialTuple h p.2) p.1.1 jb p.1.2 +
          err tau := by
      have h1 := (le_abs_self
        (actualProbeSlope r theta
          (headwiseDialPath r theta h p tau).1
          (headwiseDialPath r theta h p tau).2 tau lq a -
            levelRow theta (headwiseDialTuple h p.2) p.1.1 jb
              (headwiseDialPath r theta h p tau).2)).trans hpoly
      have h2 := (le_abs_self
        (levelRow theta (headwiseDialTuple h p.2) p.1.1 jb
            (headwiseDialPath r theta h p tau).2 -
          levelRow theta (headwiseDialTuple h p.2) p.1.1 jb p.1.2)).trans hmove
      dsimp [err]
      calc
        actualProbeSlope r theta
            (headwiseDialPath r theta h p tau).1
            (headwiseDialPath r theta h p tau).2 tau lq a =
          levelRow theta (headwiseDialTuple h p.2) p.1.1 jb p.1.2 +
            ((actualProbeSlope r theta
                (headwiseDialPath r theta h p tau).1
                (headwiseDialPath r theta h p tau).2 tau lq a -
              levelRow theta (headwiseDialTuple h p.2) p.1.1 jb
                (headwiseDialPath r theta h p tau).2) +
            (levelRow theta (headwiseDialTuple h p.2) p.1.1 jb
                (headwiseDialPath r theta h p tau).2 -
              levelRow theta (headwiseDialTuple h p.2) p.1.1 jb p.1.2)) := by ring
        _ ≤ levelRow theta (headwiseDialTuple h p.2) p.1.1 jb p.1.2 +
            (A * Real.exp (-mu * tau) + H * tau⁻¹) := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left (add_le_add h1 h2)
              (levelRow theta (headwiseDialTuple h p.2) p.1.1 jb p.1.2)
    have hfinal : actualProbeSlope r theta
        (headwiseDialPath r theta h p tau).1
        (headwiseDialPath r theta h p tau).2 tau lq a ≤ -(eta / 2) := by
      linarith
    simpa [lq] using hfinal

/-- Compact-uniform target deeper gates converge exponentially to zero. -/
theorem exists_uniform_headwise_primed_zero_saturation
    {n k d : Nat} (r : Nat) {theta : Params (n + 1) k d}
    {h : Fin k} (D : HeadwiseSignRegion theta h)
    {K : Set (HeadwiseSignPoint d)} (hK : IsCompact K)
    (hKne : K.Nonempty) (hKD : K ⊆ D.region) :
    ∃ eta T : Real, 0 < eta ∧ 1 ≤ T ∧
      ∀ p ∈ K, ∀ tau : Real, T ≤ tau →
        ∀ l : Fin (n + 1), l ≠ 0 → ∀ a : Fin k,
          actualProbeGate r theta
            (headwiseDialPath r theta h p tau).1
            (headwiseDialPath r theta h p tau).2 tau l a ≤
          Real.exp (logScale r) * Real.exp (-(eta / 2) * tau) := by
  rcases exists_uniform_headwise_primed_slope_bound r D hK hKne hKD with
    ⟨eta, T, heta, hT, hslope⟩
  refine ⟨eta, T, heta, hT, ?_⟩
  intro p hp tau htau l hl a
  exact actualProbeGate_le_exp_of_slope_le_neg r theta _ _ tau (eta / 2)
    l a (by positivity [le_trans hT htau]) (hslope p hp tau htau l hl a)

end

end TransformerIdentifiability.NLayer.NoSkip
