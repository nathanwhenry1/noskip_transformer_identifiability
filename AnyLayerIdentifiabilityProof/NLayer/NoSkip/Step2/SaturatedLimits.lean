import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Step2.SaturatedData
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Step2.DialLimits
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.FormalStreams

/-!
# NS139 — Formal observable polynomial (no-skip Step 2)

This file gives the Step-2 restatement of the NS030 formal-evaluation recovery,
specialized to the observable whose saturated multi-dial limits NS140/NS141 take.

Following the proof of `lem:ns-saturated-limit` (Step 1), the probe output is the
polynomial map `P_θ(z, w, v) := v_L(z; w, v)` of the formal streams — a polynomial
*in the gate variables* `z_{ℓa}` — evaluated at the actual analytic gates:
`F^{(L)}_θ(w, v(τ), τ) = P_θ(s(τ), w, v(τ))`.

`saturatedOutputPoly` names this output polynomial (the full-depth formal last-token
stream `formalV θ w v L`), and the two theorems below express the actual probe
output — both the raw `probeOutput` and the normalized last-column `probeObservable`
— as its evaluation at the actual gate assignment.  This is the finite-time
formal-output-equals-actual-output statement; NS140/NS141 push it to a limit.

No skip term enters: the no-skip constant is `C_1 v` (no `+ I` summand) and the
deeper-layer transmission matrices come from `formalCollapseMatrix = valueSum`.
-/

namespace TransformerIdentifiability.NLayer.NoSkip

open Filter Matrix

/-- **NS139.** The probe output observable as a formal polynomial vector in the gate
variables `z_{ℓa}`: the full-depth formal last-token stream `v_L(z; w, v)`.

This is the no-skip `P_θ(·, w, v)` of `lem:ns-saturated-limit`, Step 1.  NS140/NS141
evaluate it at limiting saturated gate tuples and take multi-dial limits. -/
noncomputable def saturatedOutputPoly {L k d : Nat} (θ : Params L k d)
    (w v : Vec d) : FormalVec L k d :=
  formalV θ w v L le_rfl

/-- Unfolding lemma: `saturatedOutputPoly` is the full-depth formal last-token stream. -/
theorem saturatedOutputPoly_eq {L k d : Nat} (θ : Params L k d) (w v : Vec d) :
    saturatedOutputPoly θ w v = formalV θ w v L le_rfl :=
  rfl

/-- **NS139 (raw output).** The actual probe output is the evaluation of the formal
output polynomial at the actual analytic gate assignment.

This is the no-skip Step-1 identity `F^{(L)}_θ(w, v(τ), τ) = P_θ(s(τ), w, v(τ))`,
repackaged from the NS030 formal-evaluation theorem
`eval_formalV_actualProbeGateAssignment_eq_probeOutput`. -/
theorem probeOutput_eq_eval_saturatedOutputPoly (r : Nat) {L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (τ : ℝ) :
    probeOutput r θ w v τ =
      evalFormalVec (actualProbeGateAssignment r θ w v τ)
        (saturatedOutputPoly θ w v) :=
  (eval_formalV_actualProbeGateAssignment_eq_probeOutput r θ w v τ).symm

/-- **NS139 (normalized observable).** For a positive number of repeats and a positive
scale, the normalized last-column observable equals the evaluation of the formal output
polynomial at the actual analytic gate assignment.

This is the form NS140/NS141 consume: the two saturated limits are limits of this
polynomial-evaluation observable. -/
theorem probeObservable_eq_eval_saturatedOutputPoly {r L k d : Nat} (hr : 0 < r)
    (θ : Params L k d) (w v : Vec d) (τ : ℝ) (hτ : 0 < τ) :
    probeObservable r θ w v τ =
      evalFormalVec (actualProbeGateAssignment r θ w v τ)
        (saturatedOutputPoly θ w v) := by
  rw [probeObservable_eq_probeOutput hr θ w v τ hτ]
  exact probeOutput_eq_eval_saturatedOutputPoly r θ w v τ

/-! ## Generic convergence to a frozen no-skip recursion -/

/-- Joint continuity of one no-skip gated recursion step. -/
theorem continuous_gatedEffectivePoint_noSkip {L k d : Nat}
    (theta : Params L k d) (l : Fin L) :
    Continuous (fun z : (Fin k → Real) × (Vec d × Vec d) =>
      gatedEffectivePoint theta l z.1 z.2.1 z.2.2) := by
  have hfst : Continuous (fun z : (Fin k → Real) × (Vec d × Vec d) =>
      (collapseMatrix theta l - gatedValueSum theta l z.1) *ᵥ z.2.1) := by
    change Continuous (fun z : (Fin k → Real) × (Vec d × Vec d) =>
      (collapseMatrix theta l -
        ∑ a : Fin k, z.1 a • valueMatrix theta l a) *ᵥ z.2.1)
    unfold collapseMatrix valueSum Matrix.mulVec
    fun_prop
  have hsnd : Continuous (fun z : (Fin k → Real) × (Vec d × Vec d) =>
      collapseMatrix theta l *ᵥ z.2.2 + gatedValueSum theta l z.1 *ᵥ z.2.1) := by
    change Continuous (fun z : (Fin k → Real) × (Vec d × Vec d) =>
      collapseMatrix theta l *ᵥ z.2.2 +
        (∑ a : Fin k, z.1 a • valueMatrix theta l a) *ᵥ z.2.1)
    unfold collapseMatrix valueSum Matrix.mulVec
    fun_prop
  exact hfst.prodMk hsnd

/-- If the moving probe converges and every actual gate converges to a frozen
label, then every prefix of the actual no-skip recursion converges to the
corresponding frozen prefix. -/
theorem tendsto_actualProbePoint_frozen
    {X : Type*} [TopologicalSpace X] {F : Filter X}
    {L k d : Nat} (r : Nat) (theta : Params L k d)
    (w v : X → Vec d) (tau : X → Real) (w0 v0 : Vec d)
    (zeta : FrozenGateFamily L k)
    (hw : Tendsto w F (nhds w0)) (hv : Tendsto v F (nhds v0))
    (hgate : ∀ l : Fin L, ∀ a : Fin k,
      Tendsto (fun x => actualProbeGate r theta (w x) (v x) (tau x) l a)
        F (nhds (zeta l a))) :
    ∀ (q : Nat) (hq : q ≤ L),
      Tendsto (fun x => actualProbePoint r theta (w x) (v x) q hq (tau x))
        F (nhds (frozenPoint theta zeta w0 v0 q hq)) := by
  intro q
  induction q with
  | zero =>
      intro hq
      simp only [actualProbePoint_zero, frozenPoint_zero]
      exact hw.prodMk_nhds hv
  | succ q ih =>
      intro hq
      let l : Fin L := ⟨q, Nat.lt_of_succ_le hq⟩
      have hprev := ih (Nat.le_of_succ_le hq)
      have hgates : Tendsto
          (fun x => fun a : Fin k =>
            actualProbeGate r theta (w x) (v x) (tau x) l a)
          F (nhds (zeta l)) := by
        rw [tendsto_pi_nhds]
        exact fun a => hgate l a
      have hstep :=
        ((continuous_gatedEffectivePoint_noSkip theta l).tendsto
          (zeta l, frozenPoint theta zeta w0 v0 q (Nat.le_of_succ_le hq))).comp
          (hgates.prodMk_nhds hprev)
      rw [frozenPoint_succ]
      refine hstep.congr (fun x => ?_)
      rw [actualProbePoint_succ]
      rfl

/-- Output form of frozen-recursion convergence. -/
theorem tendsto_probeOutput_frozen
    {X : Type*} [TopologicalSpace X] {F : Filter X}
    {L k d : Nat} (r : Nat) (theta : Params L k d)
    (w v : X → Vec d) (tau : X → Real) (w0 v0 : Vec d)
    (zeta : FrozenGateFamily L k)
    (hw : Tendsto w F (nhds w0)) (hv : Tendsto v F (nhds v0))
    (hgate : ∀ l : Fin L, ∀ a : Fin k,
      Tendsto (fun x => actualProbeGate r theta (w x) (v x) (tau x) l a)
        F (nhds (zeta l a))) :
    Tendsto (fun x => probeOutput r theta (w x) (v x) (tau x)) F
      (nhds (frozenP theta zeta L le_rfl *ᵥ v0 +
        frozenQ theta zeta L le_rfl *ᵥ w0)) := by
  have hpoint := tendsto_actualProbePoint_frozen r theta w v tau w0 v0 zeta
    hw hv hgate L le_rfl
  have hsnd :=
    (((continuous_snd : Continuous (fun p : ProbePoint d => p.2))).tendsto
      (frozenPoint theta zeta w0 v0 L le_rfl)).comp hpoint
  have hclosed := (frozenPoint_closed theta zeta w0 v0 L le_rfl).2
  rw [hclosed] at hsnd
  simpa [Function.comp_def, probeOutput, actualProbePoint_eq_probeRecursionPoint]
    using hsnd

/-- The all-zero specialization used by the primed simultaneous dial. -/
theorem tendsto_probeOutput_allZero
    {X : Type*} [TopologicalSpace X] {F : Filter X}
    {L k d : Nat} (r : Nat) (theta : Params L k d)
    (w v : X → Vec d) (tau : X → Real) (w0 v0 : Vec d)
    (hw : Tendsto w F (nhds w0)) (hv : Tendsto v F (nhds v0))
    (hgate : ∀ l : Fin L, ∀ a : Fin k,
      Tendsto (fun x => actualProbeGate r theta (w x) (v x) (tau x) l a)
        F (nhds 0)) :
    Tendsto (fun x => probeOutput r theta (w x) (v x) (tau x)) F
      (nhds (frozenP theta (allZeroGateFamily L k) L le_rfl *ᵥ v0)) := by
  have h := tendsto_probeOutput_frozen r theta w v tau w0 v0
    (allZeroGateFamily L k) hw hv hgate
  simpa [frozenQ_allZero_eq_zero] using h

/-! ## Frozen-tail matrices and the TeX saturated data -/

/-- The frozen gate family on the tail (original layers `2,...,n+1`). -/
noncomputable def saturatedTailFrozenFamily {n k : Nat} (r : Nat)
    (labels : DeeperHead → TrichotomyLabel) : FrozenGateFamily n k :=
  fun l a => trichotomyLabelValue r
    (labels { layer := l.1 + 2, head := a.1 + 1 })

theorem tupleDialFrozenFamily_succ_eq_saturatedTail {n k : Nat} (r : Nat)
    (t : Fin k → Real) (labels : DeeperHead → TrichotomyLabel)
    (l : Fin n) (a : Fin k) :
    tupleDialFrozenFamily r t labels l.succ a =
      saturatedTailFrozenFamily r labels l a := by
  rw [tupleDialFrozenFamily_deeper r t labels l.succ a (Nat.succ_pos l.1)]
  rfl

theorem tail_collapse_eq_saturatedC {n k d : Nat}
    (theta : Params (n + 1) k d) (q : Fin n) :
    collapseMatrix (Fin.tail theta) q =
      noSkipSaturatedC (saturatedValueFamily theta) (q.1 + 2) := by
  rw [noSkipSaturatedC_eq_collapseMatrix theta (by omega) (by omega)]
  rfl

theorem tail_frozenD_eq_saturatedD {n k d : Nat} (r : Nat)
    (theta : Params (n + 1) k d) (labels : DeeperHead → TrichotomyLabel)
    (q : Fin n) :
    frozenD (Fin.tail theta) (saturatedTailFrozenFamily r labels) q =
      noSkipSaturatedD (saturatedValueFamily theta)
        (saturatedNumericLabels (L := n + 1) r labels) (q.1 + 2) := by
  rw [frozenD_eq_sum]
  unfold noSkipSaturatedD
  apply Finset.sum_congr rfl
  intro a _
  rw [saturatedNumericLabels_of_mem r labels (by omega) (by omega)]
  rw [saturatedValueFamily_of_mem theta (by omega) (by omega)]
  rfl

theorem tail_frozenK_eq_saturatedKLayer {n k d : Nat} (r : Nat)
    (theta : Params (n + 1) k d) (labels : DeeperHead → TrichotomyLabel)
    (q : Fin n) :
    frozenK (Fin.tail theta) (saturatedTailFrozenFamily r labels) q =
      noSkipSaturatedKLayer (saturatedValueFamily theta)
        (saturatedNumericLabels (L := n + 1) r labels) (q.1 + 2) := by
  rw [frozenK_eq, tail_collapse_eq_saturatedC,
    tail_frozenD_eq_saturatedD]
  rfl

/-- Tail collapsed products are exactly the one-based TeX products. -/
theorem frozenP_tail_eq_layerProduct {n k d : Nat}
    (theta : Params (n + 1) k d) (zeta : FrozenGateFamily n k) :
    ∀ (q : Nat) (hq : q ≤ n),
      frozenP (Fin.tail theta) zeta q hq =
        layerProduct (noSkipSaturatedC (saturatedValueFamily theta)) (q + 1) 2
  | 0, _ => by simp
  | q + 1, hq => by
      rw [frozenP_succ]
      rw [frozenP_tail_eq_layerProduct theta zeta q (Nat.le_of_succ_le hq)]
      rw [tail_collapse_eq_saturatedC]
      by_cases hq0 : q = 0
      · subst q
        simp
      · rw [layerProduct_succ_left_of_le _ (j := q + 1) (i := 2) (by omega)]

/-- Tail contrast products are exactly the TeX products of `K_j`. -/
theorem frozenR_tail_eq_layerProduct {n k d : Nat} (r : Nat)
    (theta : Params (n + 1) k d) (labels : DeeperHead → TrichotomyLabel) :
    ∀ (q : Nat) (hq : q ≤ n),
      frozenR (Fin.tail theta) (saturatedTailFrozenFamily r labels) q hq =
        layerProduct
          (noSkipSaturatedKLayer (saturatedValueFamily theta)
            (saturatedNumericLabels (L := n + 1) r labels)) (q + 1) 2
  | 0, _ => by simp
  | q + 1, hq => by
      rw [frozenR_succ]
      rw [frozenR_tail_eq_layerProduct r theta labels q (Nat.le_of_succ_le hq)]
      rw [tail_frozenK_eq_saturatedKLayer]
      by_cases hq0 : q = 0
      · subst q
        simp
      · rw [layerProduct_succ_left_of_le _ (j := q + 1) (i := 2) (by omega)]

/-- The three frozen tail matrices are precisely `M`, `E`, and `K`. -/
theorem frozenTail_matrices_eq_saturatedData {n k d : Nat} (r : Nat)
    (theta : Params (n + 1) k d) (labels : DeeperHead → TrichotomyLabel) :
    let S := saturatedData theta r labels
    frozenP (Fin.tail theta) (saturatedTailFrozenFamily r labels) n le_rfl = S.M ∧
      frozenQ (Fin.tail theta) (saturatedTailFrozenFamily r labels) n le_rfl = S.E ∧
      frozenR (Fin.tail theta) (saturatedTailFrozenFamily r labels) n le_rfl = S.K := by
  let S := saturatedData theta r labels
  have hP := frozenP_tail_eq_layerProduct theta
    (saturatedTailFrozenFamily r labels) n le_rfl
  have hR := frozenR_tail_eq_layerProduct r theta labels n le_rfl
  have hK := S.K_eq_layerProduct
  have hcon := frozenR_add_Q_eq_P (Fin.tail theta)
    (saturatedTailFrozenFamily r labels) n le_rfl
  have hPm : frozenP (Fin.tail theta) (saturatedTailFrozenFamily r labels) n le_rfl = S.M := by
    simpa [S.M_eq, S.C_eq, noSkipSaturatedM] using hP
  have hRk : frozenR (Fin.tail theta) (saturatedTailFrozenFamily r labels) n le_rfl = S.K := by
    exact hR.trans hK.symm
  refine ⟨hPm, ?_, hRk⟩
  rw [hRk, hPm] at hcon
  have hKdef : S.K = S.M - S.E := by
    simpa [noSkipSaturatedK] using S.K_eq
  apply add_left_cancel (a := S.M - S.E)
  rw [← hKdef, hcon, hKdef]
  abel

/-- Splitting a frozen recursion after layer one agrees with the recursion of
the parameter tail, provided the two frozen families agree under `Fin.succ`. -/
theorem frozenPoint_firstLayer_tail_aux {n k d : Nat}
    (theta : Params (n + 1) k d) (zeta : FrozenGateFamily (n + 1) k)
    (zetaTail : FrozenGateFamily n k)
    (hzeta : ∀ l : Fin n, ∀ a : Fin k, zeta l.succ a = zetaTail l a)
    (w v : Vec d) : ∀ (q : Nat) (hq : q + 1 ≤ n + 1),
      frozenPoint theta zeta w v (q + 1) hq =
        frozenPoint (Fin.tail theta) zetaTail
          (gatedEffectivePoint theta ⟨0, Nat.succ_pos n⟩ (zeta ⟨0, Nat.succ_pos n⟩)
            w v).1
          (gatedEffectivePoint theta ⟨0, Nat.succ_pos n⟩ (zeta ⟨0, Nat.succ_pos n⟩)
            w v).2 q (Nat.succ_le_succ_iff.mp hq)
  | 0, _ => rfl
  | q + 1, hq => by
      conv_lhs => rw [frozenPoint_succ]
      conv_rhs => rw [frozenPoint_succ]
      rw [frozenPoint_firstLayer_tail_aux theta zeta zetaTail hzeta w v q
        (Nat.le_of_succ_le hq)]
      let lTail : Fin n :=
        ⟨q, Nat.lt_of_succ_le (Nat.succ_le_succ_iff.mp hq)⟩
      have hl : (⟨q + 1, Nat.lt_of_succ_le hq⟩ : Fin (n + 1)) = lTail.succ := by
        ext
        rfl
      rw [hl]
      have hg : zeta lTail.succ = zetaTail lTail := funext (hzeta lTail)
      rw [hg]
      rfl

theorem frozenPoint_tupleDial_firstLayer_tail {n k d : Nat} (r : Nat)
    (theta : Params (n + 1) k d) (t : Fin k → Real)
    (labels : DeeperHead → TrichotomyLabel) (w v : Vec d) :
    frozenPoint theta (tupleDialFrozenFamily r t labels) w v (n + 1) le_rfl =
      frozenPoint (Fin.tail theta) (saturatedTailFrozenFamily r labels)
        (gatedEffectivePoint theta ⟨0, Nat.succ_pos n⟩ t w v).1
        (gatedEffectivePoint theta ⟨0, Nat.succ_pos n⟩ t w v).2 n le_rfl := by
  simpa only [tupleDialFrozenFamily_first] using
    frozenPoint_firstLayer_tail_aux theta (tupleDialFrozenFamily r t labels)
      (saturatedTailFrozenFamily r labels)
      (tupleDialFrozenFamily_succ_eq_saturatedTail r t labels) w v n le_rfl

/-- Exact matrix form of the frozen multi-dial output.  This is the algebraic
part of NS140. -/
theorem frozenPoint_tupleDial_saturated_formula {n k d : Nat} (r : Nat)
    (theta : Params (n + 1) k d) (t : Fin k → Real)
    (labels : DeeperHead → TrichotomyLabel) (w v : Vec d) :
    let S := saturatedData theta r labels
    (frozenPoint theta (tupleDialFrozenFamily r t labels) w v
      (n + 1) le_rfl).2 =
      (S.M * collapseMatrix theta ⟨0, Nat.succ_pos n⟩) *ᵥ v +
        (S.E * collapseMatrix theta ⟨0, Nat.succ_pos n⟩ +
          ∑ a : Fin k, t a • (S.K * valueMatrix theta ⟨0, Nat.succ_pos n⟩ a)) *ᵥ w := by
  let S := saturatedData theta r labels
  rw [frozenPoint_tupleDial_firstLayer_tail]
  rw [(frozenPoint_closed (Fin.tail theta) (saturatedTailFrozenFamily r labels)
    _ _ n le_rfl).2]
  obtain ⟨hP, hQ, hR⟩ := frozenTail_matrices_eq_saturatedData r theta labels
  rw [hP, hQ]
  have hKdef : S.K = S.M - S.E := by
    simpa [noSkipSaturatedK] using S.K_eq
  let C := collapseMatrix theta ⟨0, Nat.succ_pos n⟩
  let D := ∑ a : Fin k, t a • valueMatrix theta ⟨0, Nat.succ_pos n⟩ a
  have hsum :
      (∑ a : Fin k, t a • (S.K * valueMatrix theta ⟨0, Nat.succ_pos n⟩ a)) =
        S.K * D := by
    dsimp [D]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Matrix.mul_smul]
  have hmat : S.M * D + S.E * (C - D) = S.E * C + S.K * D := by
    rw [hKdef]
    noncomm_ring
  change S.M *ᵥ (C *ᵥ v + D *ᵥ w) + S.E *ᵥ ((C - D) *ᵥ w) =
    (S.M * C) *ᵥ v + (S.E * C +
      ∑ a : Fin k, t a • (S.K * valueMatrix theta ⟨0, Nat.succ_pos n⟩ a)) *ᵥ w
  rw [hsum]
  simp only [Matrix.mulVec_add, Matrix.sub_mulVec, Matrix.add_mulVec,
    Matrix.mulVec_mulVec]
  have hw := congrArg (fun A => A *ᵥ w) hmat
  simp only [Matrix.add_mulVec] at hw
  rw [← Matrix.sub_mulVec, Matrix.mulVec_mulVec]
  calc
    (S.M * C) *ᵥ v + (S.M * D) *ᵥ w + (S.E * (C - D)) *ᵥ w =
        (S.M * C) *ᵥ v +
          ((S.M * D) *ᵥ w + (S.E * (C - D)) *ᵥ w) := by abel
    _ = _ := by rw [hw]

/-- The TeX unprimed saturated limit, now as an explicit no-skip vector. -/
noncomputable def multiDialUnprimedSaturatedLimit {n k d : Nat} (r : Nat)
    (theta : Params (n + 1) k d) (labels : DeeperHead → TrichotomyLabel)
    (p : MultiSignPoint d k) : Vec d :=
  let S := saturatedData theta r labels
  (S.M * collapseMatrix theta ⟨0, Nat.succ_pos n⟩) *ᵥ p.1.2 +
    (S.E * collapseMatrix theta ⟨0, Nat.succ_pos n⟩ +
      ∑ a : Fin k, p.2 a •
        (S.K * valueMatrix theta ⟨0, Nat.succ_pos n⟩ a)) *ᵥ p.1.1

/-- **NS140, analytic wrapper.** Coordinatewise trichotomy convergence along
an exact multi-dial path (possibly constructed from the paired target network)
implies convergence of `theta` to its explicit saturated matrix vector. -/
theorem tendsto_probeOutput_multiDial_unprimed_along {n k d : Nat} (r : Nat)
    (theta thetaDial : Params (n + 1) k d) (p : MultiSignPoint d k)
    (labels : DeeperHead → TrichotomyLabel)
    (hgate : ∀ l : Fin (n + 1), ∀ a : Fin k,
      Tendsto (fun tau => actualProbeGate r theta
          (multiDialPath r thetaDial p tau).1
          (multiDialPath r thetaDial p tau).2 tau l a)
        atTop (nhds (tupleDialFrozenFamily r p.2 labels l a))) :
    Tendsto (fun tau => probeOutput r theta
        (multiDialPath r thetaDial p tau).1
        (multiDialPath r thetaDial p tau).2 tau)
      atTop (nhds (multiDialUnprimedSaturatedLimit r theta labels p)) := by
  have hpath := tendsto_multiDialPath_atTop r thetaDial p
  have h := tendsto_probeOutput_frozen r theta
    (fun tau => (multiDialPath r thetaDial p tau).1)
    (fun tau => (multiDialPath r thetaDial p tau).2) id
    p.1.1 p.1.2 (tupleDialFrozenFamily r p.2 labels)
    (continuous_fst.tendsto p.1 |>.comp hpath)
    (continuous_snd.tendsto p.1 |>.comp hpath) hgate
  have hclosed := (frozenPoint_closed theta
    (tupleDialFrozenFamily r p.2 labels) p.1.1 p.1.2 (n + 1) le_rfl).2
  have hformula := frozenPoint_tupleDial_saturated_formula r theta p.2 labels
    p.1.1 p.1.2
  have hlimit :
      frozenP theta (tupleDialFrozenFamily r p.2 labels) (n + 1) le_rfl *ᵥ p.1.2 +
        frozenQ theta (tupleDialFrozenFamily r p.2 labels) (n + 1) le_rfl *ᵥ p.1.1 =
      multiDialUnprimedSaturatedLimit r theta labels p := by
    rw [← hclosed, hformula]
    rfl
  rw [hlimit] at h
  simpa using h

theorem tendsto_probeOutput_multiDial_unprimed {n k d : Nat} (r : Nat)
    (theta : Params (n + 1) k d) (p : MultiSignPoint d k)
    (labels : DeeperHead → TrichotomyLabel)
    (hgate : ∀ l : Fin (n + 1), ∀ a : Fin k,
      Tendsto (fun tau => actualProbeGate r theta
          (multiDialPath r theta p tau).1 (multiDialPath r theta p tau).2 tau l a)
        atTop (nhds (tupleDialFrozenFamily r p.2 labels l a))) :
    Tendsto (fun tau => probeOutput r theta
        (multiDialPath r theta p tau).1 (multiDialPath r theta p tau).2 tau)
      atTop (nhds (multiDialUnprimedSaturatedLimit r theta labels p)) :=
  tendsto_probeOutput_multiDial_unprimed_along r theta theta p labels hgate

/-- The primed all-zero saturated limit.  Notice that the first-layer tuple
remains `p.2`; only the deeper gates are zero. -/
noncomputable def multiDialPrimedZeroSaturatedLimit {n k d : Nat}
    (theta : Params (n + 1) k d) (p : MultiSignPoint d k) : Vec d :=
  let S := primedZeroSaturatedData theta
  (S.M * collapseMatrix theta ⟨0, Nat.succ_pos n⟩) *ᵥ p.1.2 +
    (∑ a : Fin k, p.2 a •
      (S.M * valueMatrix theta ⟨0, Nat.succ_pos n⟩ a)) *ᵥ p.1.1

theorem multiDialUnprimed_zeroLabels_eq_primedZero {n k d : Nat} (r : Nat)
    (theta : Params (n + 1) k d) (p : MultiSignPoint d k) :
    multiDialUnprimedSaturatedLimit r theta tupleZeroLabels p =
      multiDialPrimedZeroSaturatedLimit theta p := by
  simp only [multiDialUnprimedSaturatedLimit,
    multiDialPrimedZeroSaturatedLimit]
  have hlabels : saturatedNumericLabels (L := n + 1) r tupleZeroLabels =
      saturatedAllZeroLabels k := by
    funext j a
    by_cases hj : 2 ≤ j ∧ j ≤ n + 1
    · simp [saturatedNumericLabels, saturatedAllZeroLabels, tupleZeroLabels, hj]
    · simp [saturatedNumericLabels, saturatedAllZeroLabels, hj]
  have hE : (saturatedData theta r tupleZeroLabels).E = 0 := by
    rw [(saturatedData theta r tupleZeroLabels).E_eq,
      (saturatedData theta r tupleZeroLabels).C_eq,
      (saturatedData theta r tupleZeroLabels).D_eq,
      (saturatedData theta r tupleZeroLabels).KLayer_eq, hlabels]
    simp [noSkipSaturatedE]
  have hM : (saturatedData theta r tupleZeroLabels).M =
      (primedZeroSaturatedData theta).M := rfl
  have hK : (saturatedData theta r tupleZeroLabels).K =
      (primedZeroSaturatedData theta).M := by
    rw [(saturatedData theta r tupleZeroLabels).K_eq, hE]
    simp [noSkipSaturatedK, hM]
  rw [hE, hM, hK]
  simp

/-- **NS141.** Primed deeper zero-saturation gives the correct no-skip
all-zero saturated limit (with a live first-layer tuple). -/
theorem tendsto_probeOutput_multiDial_primedZero {n k d : Nat} (r : Nat)
    (theta : Params (n + 1) k d) (p : MultiSignPoint d k)
    (hgate : ∀ l : Fin (n + 1), ∀ a : Fin k,
      Tendsto (fun tau => actualProbeGate r theta
          (multiDialPath r theta p tau).1 (multiDialPath r theta p tau).2 tau l a)
        atTop (nhds (tupleDialFrozenFamily r p.2 tupleZeroLabels l a))) :
    Tendsto (fun tau => probeOutput r theta
        (multiDialPath r theta p tau).1 (multiDialPath r theta p tau).2 tau)
      atTop (nhds (multiDialPrimedZeroSaturatedLimit theta p)) := by
  rw [← multiDialUnprimed_zeroLabels_eq_primedZero r theta p]
  exact tendsto_probeOutput_multiDial_unprimed r theta p tupleZeroLabels hgate

/-- NS117 in pointwise `Tendsto` form, including the exact nonzero-time
first-layer tuple. -/
theorem tendsto_multiDial_primed_all_gates_zeroTail {n k d : Nat} (r : Nat)
    {theta : Params (n + 1) k d} (D : MultiDialSignRegion theta)
    (p : MultiSignPoint d k) (hp : p ∈ D.region) :
    ∀ l : Fin (n + 1), ∀ a : Fin k,
      Tendsto (fun tau => actualProbeGate r theta
          (multiDialPath r theta p tau).1 (multiDialPath r theta p tau).2 tau l a)
        atTop (nhds (tupleDialFrozenFamily r p.2 tupleZeroLabels l a)) := by
  intro l a
  by_cases hl0 : l = ⟨0, Nat.succ_pos n⟩
  · subst l
    have hslab := D.region_subset_slab hp
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : Real)] with tau htau
    exact (actualProbeGate_firstLayer_multiDialPath r theta p hslab.1
      (D.anchorGramDet_pos hp).ne' htau.ne' hslab.2 a).symm
  · have hl : l ≠ 0 := by
      simpa using hl0
    obtain ⟨eta, T, heta, hT, hbound⟩ :=
      exists_uniform_multiDial_primed_zero_saturation r D
        (K := {p}) isCompact_singleton (Set.singleton_nonempty p) (by simpa)
    have hhalf : 0 < eta / 2 := by linarith
    have hexp : Tendsto (fun tau : Real => Real.exp (-(eta / 2) * tau))
        atTop (nhds 0) := by
      have hs : Tendsto (fun tau : Real => (eta / 2) * tau) atTop atTop :=
        tendsto_id.const_mul_atTop hhalf
      simpa only [neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp hs
    have henv : Tendsto
        (fun tau : Real => Real.exp (logScale r) *
          Real.exp (-(eta / 2) * tau)) atTop (nhds 0) := by
      simpa using hexp.const_mul (Real.exp (logScale r))
    have hzero : tupleDialFrozenFamily r p.2 tupleZeroLabels l a = 0 :=
      tupleDialFrozenFamily_zeroLabels_deeper r p.2 l a
        (Fin.pos_iff_ne_zero.mpr hl)
    rw [hzero]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds henv
    · filter_upwards with tau
      rw [actualProbeGate_eq_sig]
      exact (sig_pos _).le
    · filter_upwards [eventually_ge_atTop T] with tau htau
      exact hbound p (Set.mem_singleton p) tau htau l hl a

/-- **NS141, concrete form.** The uniform primed negative-slope induction and
zero-saturation theorem discharge every gate-convergence premise. -/
theorem tendsto_probeOutput_multiDial_primedZero_of_signRegion
    {n k d : Nat} (r : Nat) {theta : Params (n + 1) k d}
    (D : MultiDialSignRegion theta) (p : MultiSignPoint d k)
    (hp : p ∈ D.region) :
    Tendsto (fun tau => probeOutput r theta
        (multiDialPath r theta p tau).1 (multiDialPath r theta p tau).2 tau)
      atTop (nhds (multiDialPrimedZeroSaturatedLimit theta p)) :=
  tendsto_probeOutput_multiDial_primedZero r theta p
    (tendsto_multiDial_primed_all_gates_zeroTail r D p hp)

/-- **NS142.** Equality of the finite probe outputs identifies the unprimed
trichotomy limit with the target all-zero limit at every point of the final
region. -/
theorem multiDial_saturatedLimits_eq_of_probeOutput_eq
    {n k d : Nat} (r : Nat)
    {theta theta' : Params (n + 1) k d}
    (D : MultiDialSignRegion theta') (p : MultiSignPoint d k)
    (hp : p ∈ D.region) (labels : DeeperHead → TrichotomyLabel)
    (hsourceGate : ∀ l : Fin (n + 1), ∀ a : Fin k,
      Tendsto (fun tau => actualProbeGate r theta
          (multiDialPath r theta' p tau).1
          (multiDialPath r theta' p tau).2 tau l a)
        atTop (nhds (tupleDialFrozenFamily r p.2 labels l a)))
    (hEq : ∀ w v : Vec d, ∀ tau : Real, 0 < tau →
      probeOutput r theta w v tau = probeOutput r theta' w v tau) :
    multiDialUnprimedSaturatedLimit r theta labels p =
      multiDialPrimedZeroSaturatedLimit theta' p := by
  have hs := tendsto_probeOutput_multiDial_unprimed_along r theta theta' p
    labels hsourceGate
  have ht := tendsto_probeOutput_multiDial_primedZero_of_signRegion r D p hp
  apply tendsto_nhds_unique_of_eventuallyEq hs ht
  filter_upwards [eventually_gt_atTop (0 : Real)] with tau htau
  exact hEq _ _ tau htau

end TransformerIdentifiability.NLayer.NoSkip
