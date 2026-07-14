import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Step1.CascadeClosure

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.NoSkip

noncomputable section

/-!
# Step 1 pole transfer and first-stratum containment

The tier sets below retain exactly the ready-pole payload constructed in
`CascadeClosure`.  Arbitrary-radius adjacent selection supplies local
accumulation, while the final ready payload supplies observable blowup.
-/

/-- A point hit in every punctured metric disc is an accumulation point. -/
theorem mem_acc_of_puncturedDisc_hits {A : Set ℂ} {xi : ℂ}
    (h : ∀ {epsilon : ℝ}, 0 < epsilon →
      ∃ z : ℂ, z ∈ A ∧ z ∈ puncturedDisc xi epsilon) :
    xi ∈ acc A := by
  have hclosure : xi ∈ closure (A \ {xi}) := by
    rw [Metric.mem_closure_iff]
    intro epsilon hepsilon
    rcases h hepsilon with ⟨z, hzA, hznear⟩
    refine ⟨z, ⟨hzA, ?_⟩, ?_⟩
    · simpa using hznear.1
    · simpa [dist_comm] using hznear.2
  rw [acc, mem_derivedSet, accPt_iff_frequently_nhdsNE]
  exact (mem_closure_ne_iff_frequently_within (z := xi) (s := A)).1 hclosure

/-- Tier zero is the selected first affine pole progression.  Tier `j+1`
consists of points carrying the full ready-pole witness for later stage `j`. -/
noncomputable def step1CascadeTierSet
    {n k d r : Nat} {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta')
    (P : Step1SeparatedProbePackage H) (h : Fin k) : Nat → Set ℂ
  | 0 => affineSigmoidPoleSet (logScale r)
      (matrixBilin (attentionMatrix theta' 0 h) P.w P.v)
  | q + 1 => if hq : q < n + 1 then
      {z | ∃ R : Step1SelectedPoleRecord n k d,
        R.point = z ∧ Step1ReadyPoleWitness H P.w P.v h ⟨q, hq⟩ R}
    else ∅

@[simp] theorem step1CascadeTierSet_zero
    {n k d r : Nat} {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta')
    (P : Step1SeparatedProbePackage H) (h : Fin k) :
    step1CascadeTierSet H P h 0 = affineSigmoidPoleSet (logScale r)
      (matrixBilin (attentionMatrix theta' 0 h) P.w P.v) :=
  rfl

@[simp] theorem step1CascadeTierSet_succ
    {n k d r : Nat} {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta')
    (P : Step1SeparatedProbePackage H) (h : Fin k)
    (j : Step1LaterTierIndex n) :
    step1CascadeTierSet H P h (j.1 + 1) =
      {z | ∃ R : Step1SelectedPoleRecord n k d,
        R.point = z ∧ Step1ReadyPoleWitness H P.w P.v h j R} := by
  simp [step1CascadeTierSet, j.2]

/-- A selected-only collision cannot occur at the origin, where every
constructed level has the real value `log r`. -/
theorem step1SelectedOnlyCollision_point_ne_zero
    {n k d r : Nat} (theta : Params (n + 2) k d) (w v : Vec d)
    (C : Step1SelectedChain n k) (j : Step1TierIndex n) {z : ℂ}
    (hcollision : step1SelectedOnlyCollision
      (nsActiveStratificationData (r := r) theta w v) C j z) :
    z ≠ 0 := by
  intro hz
  have hpole := hcollision.selectedLevelPole
  rw [hz] at hpole
  change nsActiveLevel (r := r) theta w v (C.selectedVar j) 0 ∈ Pi at hpole
  rw [nsActiveLevel_zero] at hpole
  exact ofReal_notMem_Pi (logScale r) hpole

/-- Every controlled tier accumulates on the next controlled tier. -/
theorem step1CascadeTier_subset_acc_next
    {n k d r : Nat} {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta')
    (P : Step1SeparatedProbePackage H) (hr : 1 < r)
    (h : Fin k) (stage : Step1LaterTierIndex n) :
    step1CascadeTierSet H P h stage.1 ⊆
      acc (step1CascadeTierSet H P h (stage.1 + 1)) := by
  intro center hcenterTier
  apply mem_acc_of_puncturedDisc_hits
  intro epsilon hepsilon
  let D := nsActiveStratificationData (r := r) theta' P.w P.v
  have hD := nsActiveHeadSingularStratification (r := r) theta' P.w P.v
  by_cases hzero : stage.1 = 0
  · have hbase : center ∈ affineSigmoidPoleSet (logScale r)
        (matrixBilin (attentionMatrix theta' 0 h) P.w P.v) := by
      simpa [hzero] using hcenterTier
    let jcur := step1FirstTierIndex n
    have hcollision : step1SelectedOnlyCollision D
        (step1TargetSelectedChain H h) jcur center :=
      step1FirstSelectedOnlyCollision_nsActive hr H P h hbase
    have hcenterOmega : center ∈ D.Omega jcur.1 := by
      change center ∈ D.Omega 0
      rw [hD.omega_zero]
      exact Set.mem_univ center
    have hcenterNe : center ≠ 0 :=
      step1SelectedOnlyCollision_point_ne_zero theta' P.w P.v
        (step1TargetSelectedChain H h) jcur hcollision
    have hactive : (step1TargetSelectedChain H h).headAt jcur ∈
        activeHeads theta' jcur := step1_head_active H jcur _
    let N := step1SuccessorPoleNormalForm_of_selectedLevelPole hD
      (step1TargetSelectedChain H h) jcur hactive hcenterOmega
        hcollision.selectedLevelPole
    have hfamily : Step1FiniteFamilyDominance H P.w P.v
        P.factorProduct_ne_zero h jcur.1
        (fun x => nsActiveGate (r := r) theta' P.w P.v x center) := by
      simpa [jcur] using step1FiniteFamilyDominance_zero H P.w P.v
        P.factorProduct_ne_zero h
        (fun x => nsActiveGate (r := r) theta' P.w P.v x center)
    have hadj : stage.toTier.1 = jcur.1 + 1 := by
      simp [hzero, jcur, step1FirstTierIndex]
    rcases step1ProduceReadyPole_from_current_nsActive H P hr h stage jcur hadj
        hcenterNe hcenterOmega hcollision N hfamily hepsilon with
      ⟨R, _hhead, _hchain, _htier, hnear, hready⟩
    refine ⟨R.point, ?_, hnear⟩
    rw [step1CascadeTierSet_succ]
    exact ⟨R, rfl, hready⟩
  · have hstagePos : 0 < stage.1 := Nat.pos_of_ne_zero hzero
    let pred : Step1LaterTierIndex n := ⟨stage.1 - 1, by omega⟩
    have hpredSucc : pred.1 + 1 = stage.1 := by
      simp [pred]
      omega
    have hcurrent : center ∈ step1CascadeTierSet H P h (pred.1 + 1) := by
      simpa [hpredSucc] using hcenterTier
    rw [step1CascadeTierSet_succ] at hcurrent
    rcases hcurrent with ⟨Q, hQpoint, hQ⟩
    subst center
    let jcur := pred.toTier
    have hadj : stage.toTier.1 = jcur.1 + 1 := by
      simp [jcur, pred, Step1LaterTierIndex.toTier, laterLayer]
      omega
    have hcenterOmega : Q.point ∈ D.Omega jcur.1 := by
      simpa [jcur, hQ.tier] using hQ.exact.1
    have hcollision : step1SelectedOnlyCollision D
        (step1TargetSelectedChain H h) jcur Q.point := by
      simpa [jcur] using hQ.selectedOnly
    have hcenterNe : Q.point ≠ 0 :=
      step1SelectedOnlyCollision_point_ne_zero theta' P.w P.v
        (step1TargetSelectedChain H h) jcur hcollision
    have hactive : (step1TargetSelectedChain H h).headAt jcur ∈
        activeHeads theta' jcur := step1_head_active H jcur _
    let N := step1SuccessorPoleNormalForm_of_selectedLevelPole hD
      (step1TargetSelectedChain H h) jcur hactive hcenterOmega
        hcollision.selectedLevelPole
    have hfamily : Step1FiniteFamilyDominance H P.w P.v
        P.factorProduct_ne_zero h jcur.1
        (fun x => nsActiveGate (r := r) theta' P.w P.v x Q.point) := by
      simpa [jcur, hpredSucc] using hQ.futureDominance
    rcases step1ProduceReadyPole_from_current_nsActive H P hr h stage jcur hadj
        hcenterNe hcenterOmega hcollision N hfamily hepsilon with
      ⟨R, _hhead, _hchain, _htier, hnear, hready⟩
    refine ⟨R.point, ?_, hnear⟩
    rw [step1CascadeTierSet_succ]
    exact ⟨R, rfl, hready⟩

/-- Point-set composition of a finite adjacent accumulation chain. -/
theorem set_subset_accIter_of_adjacent_chain (T : Nat → Set ℂ) :
    ∀ q : Nat,
      (∀ j : Nat, j < q → T j ⊆ acc (T (j + 1))) →
        T 0 ⊆ accIter q (T q)
  | 0, _hchain => by simp [accIter]
  | q + 1, hchain => by
      have hfirst : T 0 ⊆ acc (T 1) := by
        simpa using hchain 0 (Nat.zero_lt_succ q)
      have htail : ∀ j : Nat, j < q →
          T (j + 1) ⊆ acc (T ((j + 1) + 1)) := by
        intro j hj
        exact hchain (j + 1) (by omega)
      have hind := set_subset_accIter_of_adjacent_chain (fun j => T (j + 1)) q htail
      intro z hz
      have hzacc := hfirst hz
      have hzmono := acc_mono hind hzacc
      simpa [accIter, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hzmono

/-- The first selected pole progression lies in the `(n+1)`-fold
accumulation envelope of the terminal controlled tier. -/
theorem step1FirstPole_subset_finalTier_accIter
    {n k d r : Nat} {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta')
    (P : Step1SeparatedProbePackage H) (hr : 1 < r) (h : Fin k) :
    affineSigmoidPoleSet (logScale r)
        (matrixBilin (attentionMatrix theta' 0 h) P.w P.v) ⊆
      accIter (n + 1) (step1CascadeTierSet H P h (n + 1)) := by
  have hchain : ∀ j : Nat, j < n + 1 →
      step1CascadeTierSet H P h j ⊆
        acc (step1CascadeTierSet H P h (j + 1)) := by
    intro j hj
    simpa using step1CascadeTier_subset_acc_next H P hr h
      (⟨j, hj⟩ : Step1LaterTierIndex n)
  simpa using set_subset_accIter_of_adjacent_chain
    (step1CascadeTierSet H P h) (n + 1) hchain

/-! ## Terminal pole transfer -/

/-- A terminal controlled point carries a final ready-pole witness. -/
theorem step1FinalTier_readyPole
    {n k d r : Nat} {theta theta' : Params (n + 2) k d}
    {H : Step1StandingHypotheses r theta theta'}
    {P : Step1SeparatedProbePackage H} {h : Fin k} {tau : ℂ}
    (htau : tau ∈ step1CascadeTierSet H P h (n + 1)) :
    ∃ R : Step1SelectedPoleRecord n k d,
      R.point = tau ∧
        Step1ReadyPoleWitness H P.w P.v h
          (Fin.last n : Step1LaterTierIndex n) R := by
  have hlast : (Fin.last n : Step1LaterTierIndex n).1 + 1 = n + 1 := by simp
  have htau' : tau ∈ step1CascadeTierSet H P h
      ((Fin.last n : Step1LaterTierIndex n).1 + 1) := by
    simpa [hlast] using htau
  rw [step1CascadeTierSet_succ] at htau'
  exact htau'

/-- Terminal target singularities are isolated in the complete target reduced
singular set. -/
theorem step1FinalReadyPole_isPuncturedIsolated
    {n k d r : Nat} {theta theta' : Params (n + 2) k d}
    {H : Step1StandingHypotheses r theta theta'}
    {P : Step1SeparatedProbePackage H} {h : Fin k}
    {R : Step1SelectedPoleRecord n k d}
    (hR : Step1ReadyPoleWitness H P.w P.v h
      (Fin.last n : Step1LaterTierIndex n) R) :
    IsPuncturedIsolated
      (reducedSingularSet
        (nsActiveStratificationData (r := r) theta' P.w P.v)) R.point := by
  let D := nsActiveStratificationData (r := r) theta' P.w P.v
  have hD := nsActiveHeadSingularStratification (r := r) theta' P.w P.v
  have hfinalTier : Step1LaterTierIndex.toTier
      (Fin.last n : Step1LaterTierIndex n) =
      step1FinalTierIndex n := step1LastLaterTier_toTier
  have hOmega : R.point ∈ D.Omega (n + 1) := by
    simpa [D, hR.tier, hfinalTier, step1FinalTierIndex] using hR.exact.1
  have hnotPrev : R.point ∉ partialUnion D.stratum (n + 1) := by
    have hcomp : R.point ∈ (partialUnion D.stratum (n + 1))ᶜ := by
      rw [← hD.omega_eq_partialUnion_compl (n + 1) (by omega)]
      exact hOmega
    exact hcomp
  have haccSub : acc (partialUnion D.stratum ((n + 1) + 1)) ⊆
      partialUnion D.stratum (n + 1) :=
    acc_partialUnion_succ_subset hD.strataSystem
  apply eventually_notMem_of_not_mem_acc
  intro hacc
  apply hnotPrev
  apply haccSub
  simpa [D, reducedSingularSet,
    show n + 2 = (n + 1) + 1 by omega] using hacc

/-- Every target terminal controlled point transfers to the source reduced
singular set by analytic continuation from the common positive real probe. -/
theorem step1FinalTier_subset_sourceReducedSingularSet
    {n k d r : Nat} {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta')
    (P : Step1SeparatedProbePackage H) (h : Fin k) :
    step1CascadeTierSet H P h (n + 1) ⊆
      reducedSingularSet
        (nsActiveStratificationData (r := r) theta P.w P.v) := by
  intro tau htau
  rcases step1FinalTier_readyPole htau with ⟨R, rfl, hR⟩
  let i : Step1ResidueCoordinateIndex H P.w h :=
    Classical.choice (step1ResidueCoordinateIndex_nonempty H P.w P.v
      P.factorProduct_ne_zero h)
  let Ds := nsActiveStratificationData (r := r) theta P.w P.v
  let Dt := nsActiveStratificationData (r := r) theta' P.w P.v
  have hDs := nsActiveHeadSingularStratification (r := r) theta P.w P.v
  have hDt := nsActiveHeadSingularStratification (r := r) theta' P.w P.v
  have hF : AnalyticOnNhd ℂ (fun z => Ds.observable z i.1)
      (reducedSingularSet Ds)ᶜ := by
    have h := nsActiveStratificationData_observable_holomorphic
      (r := r) theta P.w P.v i.1
    rw [finalOmega_eq_compl_reducedSingularSet hDs] at h
    exact h
  have hG : AnalyticOnNhd ℂ (fun z => Dt.observable z i.1)
      (reducedSingularSet Dt)ᶜ := by
    have h := nsActiveStratificationData_observable_holomorphic
      (r := r) theta' P.w P.v i.1
    rw [finalOmega_eq_compl_reducedSingularSet hDt] at h
    exact h
  refine lem_pole_transfer_of_real_tail_eq
    (E_F := reducedSingularSet Ds) (E_G := reducedSingularSet Dt)
    (F := fun z => Ds.observable z i.1)
    (G := fun z => Dt.observable z i.1)
    (T0 := 0) (x0 := 1) (τ := R.point)
    (reducedSingularSet_closed hDs)
    (reducedSingularSet_countable hDs)
    (reducedSingularSet_countable hDt)
    hF hG (by norm_num) ?_ ?_ ?_
      (step1FinalReadyPole_isPuncturedIsolated hR)
      (step1CascadeClosure_nsActive_of_readyPole H P.w P.v h i R hR)
  · have h1 : ((1 : ℝ) : ℂ) ∈ nonnegativeRealAxis :=
      positiveRealAxis_subset_nonnegativeRealAxis one_mem_positiveRealAxis
    rw [Set.mem_compl_iff, Set.mem_union]
    intro hmem
    rcases hmem with hs | ht
    · have hsnot : ((1 : ℝ) : ℂ) ∉ reducedSingularSet Ds := by
        have hreg := nonnegativeRealAxis_subset_finalOmega hDs h1
        rw [finalOmega_eq_compl_reducedSingularSet hDs] at hreg
        exact hreg
      exact hsnot hs
    · have htnot : ((1 : ℝ) : ℂ) ∉ reducedSingularSet Dt := by
        have hreg := nonnegativeRealAxis_subset_finalOmega hDt h1
        rw [finalOmega_eq_compl_reducedSingularSet hDt] at hreg
        exact hreg
      exact htnot ht
  · intro t ht
    have hs := congrFun
      (nsActiveStratificationData_observable_positive_real_eq_probeOutput
        (r := r) theta P.w P.v t ht) i.1
    have ht' := congrFun
      (nsActiveStratificationData_observable_positive_real_eq_probeOutput
        (r := r) theta' P.w P.v t ht) i.1
    calc
      Ds.observable (t : ℂ) i.1 = (probeOutput r theta P.w P.v t i.1 : ℂ) := hs
      _ = (probeOutput r theta' P.w P.v t i.1 : ℂ) := by
        exact_mod_cast congrFun (H.probe_equal P.w P.v t ht) i.1
      _ = Dt.observable (t : ℂ) i.1 := ht'.symm
  · intro hnot
    exact (hF R.point hnot).continuousAt

/-- Stratified accumulation collapses the transferred terminal envelope to
the source first active stratum. -/
theorem step1FirstLayerPoleContainment
    {n k d r : Nat} {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta')
    (P : Step1SeparatedProbePackage H) (hr : 1 < r) (h : Fin k) :
    affineSigmoidPoleSet (logScale r)
        (matrixBilin (attentionMatrix theta' 0 h) P.w P.v) ⊆
      (nsActiveStratificationData (r := r) theta P.w P.v).stratum 0 := by
  let Ds := nsActiveStratificationData (r := r) theta P.w P.v
  have hDs := nsActiveHeadSingularStratification (r := r) theta P.w P.v
  intro tau htau
  have htarget := step1FirstPole_subset_finalTier_accIter H P hr h htau
  have hsource : tau ∈ accIter (n + 1) (reducedSingularSet Ds) :=
    accIter_mono (step1FinalTier_subset_sourceReducedSingularSet H P h)
      (n + 1) htarget
  have hcollapse := accIter_partialUnion_subset hDs.strataSystem
    (n + 1) (by omega : n + 1 ≤ n + 2)
  have hone : tau ∈ partialUnion Ds.stratum 1 := by
    have hout := hcollapse (by simpa [Ds, reducedSingularSet] using hsource)
    simpa [Ds] using hout
  simpa using hone

/-! ## Slope multiset and global attention matching -/

/-- Probe pairs whose native `Sum` assignment lies in the separated locus. -/
def step1SeparatedProbePairs
    {n k d r : Nat} {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') : Set (ProbePoint d) :=
  {p | alphaCornerProbeEval p.1 p.2 ∈ step1SeparatedSet H}

/-- Decode a separated probe pair into the package consumed by the cascade. -/
noncomputable def step1SeparatedProbePackageOfPair
    {n k d r : Nat} {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') {p : ProbePoint d}
    (hp : p ∈ step1SeparatedProbePairs H) : Step1SeparatedProbePackage H where
  rho := alphaCornerProbeEval p.1 p.2
  mem := hp
  pointwise := step1SeparatedPointwiseData_of_mem H hp

@[simp] theorem step1SeparatedProbePackageOfPair_w
    {n k d r : Nat} {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') {p : ProbePoint d}
    (hp : p ∈ step1SeparatedProbePairs H) :
    (step1SeparatedProbePackageOfPair H hp).w = p.1 := by
  rfl

@[simp] theorem step1SeparatedProbePackageOfPair_v
    {n k d r : Nat} {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') {p : ProbePoint d}
    (hp : p ∈ step1SeparatedProbePairs H) :
    (step1SeparatedProbePackageOfPair H hp).v = p.2 := by
  rfl

/-- Native separated-set Zariski density is exactly bilinear-probe Zariski
density after bundling the two coordinate blocks as a pair. -/
theorem step1SeparatedProbePairs_zariskiDense
    {n k d r : Nat} {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') :
    ProbeZariskiDense (step1SeparatedProbePairs H) := by
  intro Q hQ
  apply (step1SeparatedSetProperties H).zariski_dense Q
  intro rho hrho
  let p : ProbePoint d := (step1AssignmentW rho, step1AssignmentV rho)
  have hp : p ∈ step1SeparatedProbePairs H := by
    change alphaCornerProbeEval (step1AssignmentW rho) (step1AssignmentV rho) ∈
      step1SeparatedSet H
    simpa using hrho
  have hzero := hQ p hp
  have heval : Sum.elim p.1 p.2 = rho := by
    funext x
    rcases x with x | x <;> rfl
  simpa [heval] using hzero

/-- Per target head and separated probe, pole containment forces an active
source head with the same first-layer bilinear slope. -/
theorem step1FirstLayerSlopeMatch
    {n k d r : Nat} {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (hr : 1 < r)
    {p : ProbePoint d} (hp : p ∈ step1SeparatedProbePairs H) (h : Fin k) :
    ∃ a : Fin k, a ∈ activeHeads theta (0 : Fin (n + 2)) ∧
      matrixBilin (attentionMatrix theta 0 a) p.1 p.2 =
        matrixBilin (attentionMatrix theta' 0 h) p.1 p.2 := by
  let P := step1SeparatedProbePackageOfPair H hp
  let tau := affineSigmoidPole (logScale r)
    (matrixBilin (attentionMatrix theta' 0 h) p.1 p.2) 0
  have htau : tau ∈ affineSigmoidPoleSet (logScale r)
      (matrixBilin (attentionMatrix theta' 0 h) p.1 p.2) := by
    exact TransformerIdentifiability.NLayer.sigmoidPole_mem_firstPoleSet _ _ 0
  have hmem : tau ∈
      (nsActiveStratificationData (r := r) theta p.1 p.2).stratum 0 := by
    have hcont := step1FirstLayerPoleContainment H P hr h
    simpa [P] using hcont htau
  have hDs := nsActiveHeadSingularStratification (r := r) theta p.1 p.2
  have hlevel : ∀ a : Fin k,
      (nsActiveStratificationData (r := r) theta p.1 p.2).level
          ((0 : Fin (n + 2)), a) =
        initialActiveLevel (r := r) theta p.1 p.2 (by omega) a := by
    intro a
    funext z
    exact nsActiveLevel_first theta p.1 p.2 a z
  rw [mem_first_stratum_iff hDs p.1 p.2 (by omega) hlevel] at hmem
  rcases hmem with ⟨a, ha, haslope, hatMem⟩
  refine ⟨a, ha, ?_⟩
  by_contra hne
  have htargetSlope : matrixBilin (attentionMatrix theta' 0 h) p.1 p.2 ≠ 0 := by
    simpa [P] using P.firstSlope_ne_zero h
  have hb : logScale r ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hr))
  have hinter := affineSigmoidPoleSet_inter_eq_empty_of_ne hb haslope
    htargetSlope hne
  have hempty : tau ∈ (∅ : Set ℂ) := by
    rw [← hinter]
    exact ⟨hatMem, htau⟩
  exact hempty

/-- Pointwise slope matching is a target-to-source permutation, and every
matched source head is active. -/
theorem step1FirstLayerSlopeMatching
    {n k d r : Nat} {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (hr : 1 < r)
    {p : ProbePoint d} (hp : p ∈ step1SeparatedProbePairs H) :
    ∃ e : Equiv.Perm (Fin k),
      (∀ h : Fin k, matrixBilin (attentionMatrix theta 0 (e h)) p.1 p.2 =
        matrixBilin (attentionMatrix theta' 0 h) p.1 p.2) ∧
      (∀ h : Fin k, e h ∈ activeHeads theta (0 : Fin (n + 2))) := by
  classical
  let P := step1SeparatedProbePackageOfPair H hp
  have htargetInj : Function.Injective (fun h : Fin k =>
      matrixBilin (attentionMatrix theta' 0 h) p.1 p.2) := by
    simpa [P] using P.firstSlope_injective
  choose phi hphiActive hphiSlope using fun h =>
    step1FirstLayerSlopeMatch H hr hp h
  have hphiInj : Function.Injective phi := by
    intro h g heq
    apply htargetInj
    change matrixBilin (attentionMatrix theta' 0 h) p.1 p.2 =
      matrixBilin (attentionMatrix theta' 0 g) p.1 p.2
    calc
      matrixBilin (attentionMatrix theta' 0 h) p.1 p.2 =
          matrixBilin (attentionMatrix theta 0 (phi h)) p.1 p.2 :=
        (hphiSlope h).symm
      _ = matrixBilin (attentionMatrix theta 0 (phi g)) p.1 p.2 := by rw [heq]
      _ = matrixBilin (attentionMatrix theta' 0 g) p.1 p.2 := hphiSlope g
  have hphiBij : Function.Bijective phi :=
    Finite.injective_iff_bijective.mp hphiInj
  exact ⟨Equiv.ofBijective phi hphiBij, hphiSlope, hphiActive⟩

/-- Equality of the first-layer slope multisets on every separated probe. -/
theorem step1FirstLayerSlopeProduct
    {n k d r : Nat} {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (hr : 1 < r)
    {p : ProbePoint d} (hp : p ∈ step1SeparatedProbePairs H) (t : ℝ) :
    ∏ a : Fin k, (t - matrixBilin (attentionMatrix theta 0 a) p.1 p.2) =
      ∏ h : Fin k, (t - matrixBilin (attentionMatrix theta' 0 h) p.1 p.2) := by
  rcases step1FirstLayerSlopeMatching H hr hp with ⟨e, heslope, _⟩
  calc
    ∏ a : Fin k, (t - matrixBilin (attentionMatrix theta 0 a) p.1 p.2) =
        ∏ h : Fin k,
          (t - matrixBilin (attentionMatrix theta 0 (e h)) p.1 p.2) :=
      (Equiv.prod_comp e
        (fun a => t - matrixBilin (attentionMatrix theta 0 a) p.1 p.2)).symm
    _ = ∏ h : Fin k,
          (t - matrixBilin (attentionMatrix theta' 0 h) p.1 p.2) := by
      exact Finset.prod_congr rfl (fun h _ => by rw [heslope h])

/-- Surjectivity of the pointwise matching makes every source first-layer head
active. -/
theorem step1FirstLayer_allHeadsActive
    {n k d r : Nat} {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (hr : 1 < r)
    {p : ProbePoint d} (hp : p ∈ step1SeparatedProbePairs H) (a : Fin k) :
    a ∈ activeHeads theta (0 : Fin (n + 2)) := by
  rcases step1FirstLayerSlopeMatching H hr hp with ⟨e, _heslope, heactive⟩
  obtain ⟨h, rfl⟩ := e.surjective a
  exact heactive h

/-- Target regularity makes the target first attention family injective. -/
theorem step1TargetFirstAttention_injective
    {n k d r : Nat} {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') :
    Function.Injective (attentionMatrix theta' 0) := by
  intro a c heq
  by_contra hne
  exact (H.targetRegularity.attention_ne_of_ne (0 : Fin (n + 2)) hne) heq

/-- The unique global target-to-source first-layer attention permutation. -/
theorem step1FirstAttentionPermutation
    {n k d r : Nat} {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (hr : 1 < r) :
    ∃! sigma : Equiv.Perm (Fin k),
      ∀ h : Fin k, attentionMatrix theta 0 (sigma h) =
        attentionMatrix theta' 0 h := by
  refine global_labeling_algebraic (attentionMatrix theta 0)
    (attentionMatrix theta' 0) (step1SeparatedProbePairs H)
    (step1TargetFirstAttention_injective H)
    (step1SeparatedProbePairs_zariskiDense H) ?_
  intro p hp t
  simpa [matrixBilin] using step1FirstLayerSlopeProduct H hr hp t

end

end TransformerIdentifiability.NLayer.NoSkip
