import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Step2.DialLimits

set_option autoImplicit false

open Filter
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.NoSkip

noncomputable section

/-!
# Paired multi-dial zero/alpha branch

The local multi-quadric identity does not imply ambient polynomial vanishing.
The single provider below therefore isolates the missing, equality-derived
rigidity statement.  Everything after it is analytic bookkeeping.
-/

/-- The exact global rigidity obligation left by the paired zero branch.

An implementation must derive this field from equality of the source and
target realizations (and target genericity).  It deliberately cannot be
constructed from a local vanishing hypothesis alone. -/
structure PairedTupleDialZeroRigidityProvider {n k d : Nat} (r : Nat)
    (thetaLive thetaDial : Params (n + 1) k d)
    (D : MultiDialSignRegion thetaDial) : Prop where
  zero_of_vanishes :
    ∀ (R : MultiDialRestrictedRegion D)
      (labels : DeeperHead → TrichotomyLabel) (dh : DeeperHead),
      dh ∈ deeperHeadOrder (n + 1) k →
      (∀ p ∈ R.region, tupleDialFrozenSlopeForm r thetaLive dh labels p = 0) →
      tupleDialFrozenSlopeForm r thetaLive dh labels = 0

/-- Proposition-valued tuple estimates and the reusable K-head exponential
record carry the same data. -/
noncomputable def eventuallyExpClose_of_tupleDialExpCloseTo
    {f : Real → Real} {a : Real} (h : TupleDialExpCloseTo f a) :
    EventuallyExpClose f a :=
  let rate := Classical.choose h
  let hrateData := Classical.choose_spec h
  let coeff := Classical.choose hrateData
  let hcoeffData := Classical.choose_spec hrateData
  let start := Classical.choose hcoeffData
  let hspec := Classical.choose_spec hcoeffData
  ⟨rate, hspec.1, coeff, hspec.2.1, start, hspec.2.2⟩

noncomputable def tupleDialExpCloseTo_of_eventuallyExpClose
    {f : Real → Real} {a : Real} (h : EventuallyExpClose f a) :
    TupleDialExpCloseTo f a :=
  ⟨h.rate, h.coeff, h.start, h.rate_pos, h.coeff_nonneg, h.bound⟩

/-- Every tuple-frozen gate lies in the unit interval on a restricted target
sign region. -/
theorem abs_tupleDialFrozenAssignment_le_one
    {n k d : Nat} {r : Nat} {thetaDial : Params (n + 1) k d}
    {D : MultiDialSignRegion thetaDial} (R : MultiDialRestrictedRegion D)
    (labels : DeeperHead → TrichotomyLabel) (p : MultiSignPoint d k)
    (hp : p ∈ R.region) (x : FormalVar (n + 1) k) :
    |tupleDialFrozenAssignment r p.2 labels x| ≤ 1 := by
  rcases x with ⟨l, a⟩
  by_cases hl0 : l.1 = 0
  · have hslab := D.region_subset_slab (R.region_subset hp)
    have hl : l = ⟨0, Nat.succ_pos n⟩ := Fin.ext (by simpa using hl0)
    subst l
    rw [tupleDialFrozenAssignment_first, abs_of_pos (hslab.2 a).1]
    exact (hslab.2 a).2.le
  · rw [tupleDialFrozenAssignment_deeper r p.2 labels l a
      (Nat.pos_of_ne_zero hl0)]
    cases hlabel : labels (formalVarDeeperHead (l, a)) <;>
      change labels { layer := l.1 + 1, head := a.1 + 1 } = _ at hlabel
    · simp [hlabel, trichotomyLabelValue]
    · simp [hlabel, trichotomyLabelValue]
    · rw [hlabel, trichotomyLabelValue_alpha,
        abs_of_nonneg (sig_pos _).le]
      exact sig_le_one _

/-- All live gates are sigmoid values and hence lie in the unit interval. -/
theorem abs_pairedTupleDialLiveAssignment_le_one
    {n k d : Nat} (r : Nat)
    (thetaLive thetaDial : Params (n + 1) k d)
    (p : MultiSignPoint d k) (tau : Real) (x : FormalVar (n + 1) k) :
    |pairedTupleDialLiveAssignment r thetaLive thetaDial p tau x| ≤ 1 := by
  simp only [pairedTupleDialLiveAssignment, actualProbeGateAssignment]
  rw [actualProbeGate_eq_sig, abs_of_nonneg (sig_pos _).le]
  exact sig_le_one _

/-- A processed prior coordinate is exponentially close to its frozen value;
first-layer coordinates are exact along the paired dial. -/
noncomputable def eventuallyExpClose_prior_pairedTupleGate
    {n k d : Nat} {r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d}
    {D : MultiDialSignRegion thetaDial}
    {baseRegion currentRegion : MultiDialRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx q : Nat} {a : Fin k}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (hcurrent : (deeperHeadOrder (n + 1) k)[idx] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    (hInv : PairedTupleDialProcessingInvariant r thetaLive thetaDial D
      baseRegion currentRegion (deeperHeadOrder (n + 1) k) idx labels)
    (p : MultiSignPoint d k) (hp : p ∈ currentRegion.region)
    (x : FormalVar (n + 1) k) (hx : x.1.1 < q) :
    EventuallyExpClose
      (fun tau => pairedTupleDialLiveAssignment r thetaLive thetaDial p tau x)
      (tupleDialFrozenAssignment r p.2 labels x) := by
  by_cases hx0 : x.1.1 = 0
  · refine {
      rate := 1
      rate_pos := by norm_num
      coeff := 0
      coeff_nonneg := by norm_num
      start := 1
      bound := ?_ }
    intro tau htau
    have htau0 : tau ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one htau)
    rcases x with ⟨l, b⟩
    have hl : l = ⟨0, Nat.succ_pos n⟩ := Fin.ext (by simpa using hx0)
    subst l
    rw [hInv.firstLayer_live_eq_frozen p hp tau htau0 b]
    simp
  · have hxpos : 1 ≤ x.1.1 := Nat.one_le_iff_ne_zero.mpr hx0
    have hprocessed : formalVarDeeperHead x ∈
        processedPrefix (deeperHeadOrder (n + 1) k) idx :=
      KHead.succ_head_mem_processedPrefix_of_layer_lt_getElem_deeperHeadOrder
        hidx hcurrent hxpos x.1.2 hx x.2
    exact eventuallyExpClose_of_tupleDialExpCloseTo
      (hInv.processed_gate_expClose x hprocessed p hp)

/-! ## NS126: honest exponential zero-slope estimate -/

/-- Polynomial slice constants along the paired dial path can be chosen
uniformly in `tau` for every coordinate of the finite telescope. -/
theorem exists_pairedTupleDialSlopeTelescopeConstants
    {n k d : Nat} {r : Nat}
    (thetaLive thetaDial : Params (n + 1) k d)
    (labels : DeeperHead → TrichotomyLabel)
    {D : MultiDialSignRegion thetaDial} (R : MultiDialRestrictedRegion D)
    (p : MultiSignPoint d k) (hp : p ∈ R.region)
    (q : Nat) (hq : q < n + 1) (a : Fin k) :
    ∃ K T : Nat → Real,
      (∀ i, i < (formalVarsBelow (n + 1) k q).length → 0 ≤ K i) ∧
      ∀ i, (hi : i < (formalVarsBelow (n + 1) k q).length) →
        ∀ tau, T i ≤ tau →
          |MvPolynomial.eval
              (KHead.formalVarPrefixAssignment
                (fun tau => pairedTupleDialLiveAssignment r thetaLive thetaDial p tau)
                (fun _ => tupleDialFrozenAssignment r p.2 labels)
                (formalVarsBelow (n + 1) k q) (i + 1) tau)
              (formalSlope thetaLive
                (multiDialPath r thetaDial p tau).1
                (multiDialPath r thetaDial p tau).2 ⟨q, hq⟩ a) -
            MvPolynomial.eval
              (KHead.formalVarPrefixAssignment
                (fun tau => pairedTupleDialLiveAssignment r thetaLive thetaDial p tau)
                (fun _ => tupleDialFrozenAssignment r p.2 labels)
                (formalVarsBelow (n + 1) k q) i tau)
              (formalSlope thetaLive
                (multiDialPath r thetaDial p tau).1
                (multiDialPath r thetaDial p tau).2 ⟨q, hq⟩ a)|
          ≤ K i *
            |pairedTupleDialLiveAssignment r thetaLive thetaDial p tau
                ((formalVarsBelow (n + 1) k q)[i]'hi) -
              tupleDialFrozenAssignment r p.2 labels
                ((formalVarsBelow (n + 1) k q)[i]'hi)| := by
  classical
  have hpath := tendsto_multiDialPath_atTop r thetaDial p
  have hLipTendsto : Tendsto
      (fun tau => allSlopeBoxLip thetaLive (multiDialPath r thetaDial p tau))
      atTop (nhds (allSlopeBoxLip thetaLive p.1)) :=
    (continuous_allSlopeBoxLip thetaLive).continuousAt.tendsto.comp hpath
  let B := KHead.EventuallyBoundedReal.ofTendsto hLipTendsto
  refine ⟨fun _ => B.radius, fun _ => B.start, ?_, ?_⟩
  · intro i hi
    exact B.radius_nonneg
  · intro i hi tau htau
    let P := formalSlope thetaLive
      (multiDialPath r thetaDial p tau).1
      (multiDialPath r thetaDial p tau).2 ⟨q, hq⟩ a
    let X := KHead.formalVarPrefixAssignment
      (fun tau => pairedTupleDialLiveAssignment r thetaLive thetaDial p tau)
      (fun _ => tupleDialFrozenAssignment r p.2 labels)
      (formalVarsBelow (n + 1) k q) (i + 1) tau
    let Y := KHead.formalVarPrefixAssignment
      (fun tau => pairedTupleDialLiveAssignment r thetaLive thetaDial p tau)
      (fun _ => tupleDialFrozenAssignment r p.2 labels)
      (formalVarsBelow (n + 1) k q) i tau
    have hX : ∀ x, |X x| ≤ 1 := by
      intro x
      change |KHead.formalVarPrefixAssignment
        (fun tau => pairedTupleDialLiveAssignment r thetaLive thetaDial p tau)
        (fun _ => tupleDialFrozenAssignment r p.2 labels)
        (formalVarsBelow (n + 1) k q) (i + 1) tau x| ≤ 1
      by_cases hx : x ∈ (formalVarsBelow (n + 1) k q).take (i + 1)
      · rw [KHead.formalVarPrefixAssignment_of_mem_take _ _ _ _ _ hx]
        exact abs_pairedTupleDialLiveAssignment_le_one r thetaLive thetaDial p tau x
      · rw [KHead.formalVarPrefixAssignment_of_not_mem_take _ _ _ _ _ hx]
        exact abs_tupleDialFrozenAssignment_le_one R labels p hp x
    have hY : ∀ x, |Y x| ≤ 1 := by
      intro x
      change |KHead.formalVarPrefixAssignment
        (fun tau => pairedTupleDialLiveAssignment r thetaLive thetaDial p tau)
        (fun _ => tupleDialFrozenAssignment r p.2 labels)
        (formalVarsBelow (n + 1) k q) i tau x| ≤ 1
      by_cases hx : x ∈ (formalVarsBelow (n + 1) k q).take i
      · rw [KHead.formalVarPrefixAssignment_of_mem_take _ _ _ _ _ hx]
        exact abs_pairedTupleDialLiveAssignment_le_one r thetaLive thetaDial p tau x
      · rw [KHead.formalVarPrefixAssignment_of_not_mem_take _ _ _ _ _ hx]
        exact abs_tupleDialFrozenAssignment_le_one R labels p hp x
    have hXY : ∀ x, x ≠ (formalVarsBelow (n + 1) k q)[i]'hi → X x = Y x := by
      intro x hx
      exact KHead.formalVarPrefixAssignment_succ_eq_of_ne _ _ _ i hi tau hx
    have hslice := KHead.eval_sub_eval_abs_le_realSliceLip P
      ((formalVarsBelow (n + 1) k q)[i]'hi) (fun _ => 1) X Y
      (fun _ => zero_le_one) hX hY hXY
    have hsupp : P.support ⊆ KHead.formalMonomialBox (n + 1) k := by
      intro m hm
      rw [KHead.mem_formalMonomialBox_iff]
      intro x
      exact (MvPolynomial.degreeOf_le_iff.mp
        (formalSlope_blockDegree_two thetaLive
          (multiDialPath r thetaDial p tau).1
          (multiDialPath r thetaDial p tau).2 ⟨q, hq⟩ a x)) m hm
    have hbox := realSliceLip_one_le_formalBoxSliceLip P
      ((formalVarsBelow (n + 1) k q)[i]'hi) hsupp
    have hsingle := formalBoxSliceLip_le_allSlopeBoxLip thetaLive
      (multiDialPath r thetaDial p tau) ⟨q, hq⟩ a
      ((formalVarsBelow (n + 1) k q)[i]'hi)
    have hbound : allSlopeBoxLip thetaLive (multiDialPath r thetaDial p tau) ≤
        B.radius := by
      have := B.bound tau htau
      rw [abs_of_nonneg (allSlopeBoxLip_nonneg thetaLive _)] at this
      exact this
    have hcoordX : X ((formalVarsBelow (n + 1) k q)[i]'hi) =
        pairedTupleDialLiveAssignment r thetaLive thetaDial p tau
          ((formalVarsBelow (n + 1) k q)[i]'hi) := by
      change KHead.formalVarPrefixAssignment
        (fun tau => pairedTupleDialLiveAssignment r thetaLive thetaDial p tau)
        (fun _ => tupleDialFrozenAssignment r p.2 labels)
        (formalVarsBelow (n + 1) k q) (i + 1) tau
          ((formalVarsBelow (n + 1) k q)[i]'hi) = _
      apply KHead.formalVarPrefixAssignment_of_mem_take
      rw [List.take_succ_eq_append_getElem hi]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    have hcoordY : Y ((formalVarsBelow (n + 1) k q)[i]'hi) =
        tupleDialFrozenAssignment r p.2 labels
          ((formalVarsBelow (n + 1) k q)[i]'hi) := by
      change KHead.formalVarPrefixAssignment
        (fun tau => pairedTupleDialLiveAssignment r thetaLive thetaDial p tau)
        (fun _ => tupleDialFrozenAssignment r p.2 labels)
        (formalVarsBelow (n + 1) k q) i tau
          ((formalVarsBelow (n + 1) k q)[i]'hi) = _
      apply KHead.formalVarPrefixAssignment_of_not_mem_take
      exact KHead.getElem_not_mem_take_of_nodup
        (nodup_formalVarsBelow (n + 1) k q) hi
    calc
      |MvPolynomial.eval X P - MvPolynomial.eval Y P|
          ≤ KHead.realSliceLip P ((formalVarsBelow (n + 1) k q)[i]'hi)
              (fun _ => 1) *
            |X ((formalVarsBelow (n + 1) k q)[i]'hi) -
              Y ((formalVarsBelow (n + 1) k q)[i]'hi)| := hslice
      _ ≤ B.radius *
            |X ((formalVarsBelow (n + 1) k q)[i]'hi) -
              Y ((formalVarsBelow (n + 1) k q)[i]'hi)| :=
        mul_le_mul_of_nonneg_right (hbox.trans (hsingle.trans hbound)) (abs_nonneg _)
      _ = B.radius *
            |pairedTupleDialLiveAssignment r thetaLive thetaDial p tau
                ((formalVarsBelow (n + 1) k q)[i]'hi) -
              tupleDialFrozenAssignment r p.2 labels
                ((formalVarsBelow (n + 1) k q)[i]'hi)| := by
        rw [hcoordX, hcoordY]

/-- **NS126.** Once the provider has upgraded local vanishing to a global
frozen-slope identity, prior exponential gate estimates imply an exponential
bound for the current live slope.  The moving probe contributes no algebraic
error because the global identity is evaluated at the moving probe itself. -/
noncomputable def currentPairedTupleSlope_expClose_zero
    {n k d : Nat} {r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d}
    {D : MultiDialSignRegion thetaDial}
    {baseRegion currentRegion : MultiDialRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx q : Nat} {a : Fin k}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (hqpos : 1 ≤ q) (hq : q < n + 1)
    (hcurrent : (deeperHeadOrder (n + 1) k)[idx] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    (hInv : PairedTupleDialProcessingInvariant r thetaLive thetaDial D
      baseRegion currentRegion (deeperHeadOrder (n + 1) k) idx labels)
    (p : MultiSignPoint d k) (hp : p ∈ currentRegion.region)
    (hzero : tupleDialFrozenSlopeForm r thetaLive
      (deeperHeadOrder (n + 1) k)[idx] labels = 0) :
    TupleDialExpCloseTo (fun tau => actualProbeSlope r thetaLive
      (multiDialPath r thetaDial p tau).1
      (multiDialPath r thetaDial p tau).2 tau ⟨q, hq⟩ a) 0 := by
  classical
  let vars := formalVarsBelow (n + 1) k q
  let rho : Real → FormalAssignment (n + 1) k :=
    fun tau => pairedTupleDialLiveAssignment r thetaLive thetaDial p tau
  let sigma : Real → FormalAssignment (n + 1) k :=
    fun _ => tupleDialFrozenAssignment r p.2 labels
  let P : Real → FormalPoly (n + 1) k := fun tau =>
    formalSlope thetaLive (multiDialPath r thetaDial p tau).1
      (multiDialPath r thetaDial p tau).2 ⟨q, hq⟩ a
  obtain ⟨K, T, hK, hLip⟩ :=
    exists_pairedTupleDialSlopeTelescopeConstants thetaLive thetaDial labels
      currentRegion p hp q hq a
  have hcoord : ∀ i, (hi : i < vars.length) → EventuallyExpClose
      (fun tau => rho tau (vars[i]'hi) - sigma tau (vars[i]'hi)) 0 := by
    intro i hi
    have hxlt : (vars[i]'hi).1.1 < q :=
      (mem_formalVarsBelow (vars[i]'hi)).1 (List.getElem_mem hi)
    exact KHead.eventuallyExpClose_sub_const
      (eventuallyExpClose_prior_pairedTupleGate hidx hcurrent hInv p hp
        (vars[i]'hi) hxlt)
  have htel := KHead.eventuallyExpClose_eval_formalPolyPath_delta_of_formalVarPrefix_lipschitz
    P vars rho sigma K T hcoord (by simpa [vars] using hK)
      (by simpa [vars, rho, sigma, P] using hLip)
  have hLive : ∀ tau,
      MvPolynomial.eval
          (KHead.formalVarPrefixAssignment rho sigma vars vars.length tau) (P tau) =
        actualProbeSlope r thetaLive (multiDialPath r thetaDial p tau).1
          (multiDialPath r thetaDial p tau).2 tau ⟨q, hq⟩ a := by
    intro tau
    have hagree : MvPolynomial.eval
          (KHead.formalVarPrefixAssignment rho sigma vars vars.length tau) (P tau) =
        MvPolynomial.eval (rho tau) (P tau) := by
      apply MvPolynomial.eval₂_congr
      intro x m hxm hm
      have hxvar : x ∈ (P tau).vars := by
        rw [MvPolynomial.mem_vars_iff_mem_support]
        exact ⟨m, MvPolynomial.mem_support_iff.mpr hm, hxm⟩
      have hxlt : x.1.1 < q := formalSlope_dependsOnLayersBefore thetaLive
        (multiDialPath r thetaDial p tau).1 (multiDialPath r thetaDial p tau).2
        ⟨q, hq⟩ a x hxvar
      exact KHead.formalVarPrefixAssignment_length_of_mem rho sigma vars tau
        ((mem_formalVarsBelow x).2 hxlt)
    rw [hagree]
    exact eval_formalSlope_actualProbeGateAssignment r thetaLive _ _ tau ⟨q, hq⟩ a
  have hFrozen : ∀ tau,
      MvPolynomial.eval
          (KHead.formalVarPrefixAssignment rho sigma vars 0 tau) (P tau) = 0 := by
    intro tau
    rw [KHead.formalVarPrefixAssignment_zero]
    have hvalid : 2 ≤ q + 1 ∧ q + 1 ≤ n + 1 ∧
        1 ≤ (a : Nat) + 1 ∧ (a : Nat) + 1 ≤ k :=
      ⟨by omega, by omega, by omega, Nat.succ_le_of_lt a.2⟩
    have hz := congrFun hzero
      (((multiDialPath r thetaDial p tau), p.2) : MultiSignPoint d k)
    rw [hcurrent, Pi.zero_apply, tupleDialFrozenSlopeForm, dif_pos hvalid] at hz
    exact hz
  exact tupleDialExpCloseTo_of_eventuallyExpClose
    (htel.congr_of_forall_eq (fun tau => by rw [hLive tau, hFrozen tau, sub_zero]) rfl)

/-! ## NS127: alpha gate and successor estimate -/

/-- An exponentially small current slope yields exponential convergence of
the rescaled sigmoid gate to `alpha r`. -/
noncomputable def currentPairedTupleGate_expClose_alpha
    {n k d : Nat} {r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d}
    {D : MultiDialSignRegion thetaDial}
    {baseRegion currentRegion : MultiDialRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx q : Nat} {a : Fin k}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (hqpos : 1 ≤ q) (hq : q < n + 1)
    (hcurrent : (deeperHeadOrder (n + 1) k)[idx] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    (hInv : PairedTupleDialProcessingInvariant r thetaLive thetaDial D
      baseRegion currentRegion (deeperHeadOrder (n + 1) k) idx labels)
    (p : MultiSignPoint d k) (hp : p ∈ currentRegion.region)
    (hzero : tupleDialFrozenSlopeForm r thetaLive
      (deeperHeadOrder (n + 1) k)[idx] labels = 0) :
    TupleDialExpCloseTo
      (fun tau => pairedTupleDialLiveAssignment r thetaLive thetaDial p tau
        (⟨q, hq⟩, a)) (alpha r) := by
  have hslope := currentPairedTupleSlope_expClose_zero hidx hqpos hq hcurrent
    hInv p hp hzero
  have hgate := KHead.expCloseTo_gate_alpha_of_expCloseTo_slope_zero r
    (h := by simpa [KHead.ExpCloseTo, TupleDialExpCloseTo] using hslope)
  simpa [KHead.ExpCloseTo, TupleDialExpCloseTo, pairedTupleDialLiveAssignment,
    actualProbeGateAssignment, actualProbeGate_eq_sig] using hgate

/-- Provider-facing NS126/127 capstone.  Local vanishing is upgraded exactly
once by the equality-derived provider; the resulting gate estimate is then
available at every point of the current region. -/
noncomputable def pairedTupleDialAlphaEstimate_of_zeroRigidity
    {n k d : Nat} {r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d}
    {D : MultiDialSignRegion thetaDial}
    (H : PairedTupleDialZeroRigidityProvider r thetaLive thetaDial D)
    {baseRegion currentRegion : MultiDialRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx q : Nat} {a : Fin k}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (hqpos : 1 ≤ q) (hq : q < n + 1)
    (hcurrent : (deeperHeadOrder (n + 1) k)[idx] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    (hInv : PairedTupleDialProcessingInvariant r thetaLive thetaDial D
      baseRegion currentRegion (deeperHeadOrder (n + 1) k) idx labels)
    (hvanish : ∀ p ∈ currentRegion.region,
      tupleDialFrozenSlopeForm r thetaLive
        (deeperHeadOrder (n + 1) k)[idx] labels p = 0) :
    ∀ p ∈ currentRegion.region, TupleDialExpCloseTo
      (fun tau => pairedTupleDialLiveAssignment r thetaLive thetaDial p tau
        (⟨q, hq⟩, a)) (alpha r) := by
  have hzero := H.zero_of_vanishes currentRegion labels
    (deeperHeadOrder (n + 1) k)[idx] (List.getElem_mem hidx) hvanish
  intro p hp
  exact currentPairedTupleGate_expClose_alpha hidx hqpos hq hcurrent hInv p hp hzero

end

end TransformerIdentifiability.NLayer.NoSkip
