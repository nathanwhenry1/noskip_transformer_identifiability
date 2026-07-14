import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Step1.FinalBlowup
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Step1.SeparatedTopology
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Analytic.LevelRecurrence
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Analytic.SiblingAvoidance
import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.SiblingAvoidance

set_option autoImplicit false

open Filter

namespace TransformerIdentifiability.NLayer.NoSkip

noncomputable section

variable {r n k d : Nat}

/-! ## Genuine adjacent-tier point selection -/

/-- Canonical number of nonselected siblings of one selected head. -/
noncomputable def step1NSSiblingCount {k : Nat} (a : Fin k) : Nat :=
  Fintype.card {c : Fin k // c ≠ a}

/-- Canonical enumeration of every nonselected sibling. -/
noncomputable def step1NSSiblingEnumeration {k : Nat} (a : Fin k) :
    Fin (step1NSSiblingCount a) → {c : Fin k // c ≠ a} :=
  (Fintype.equivFin {c : Fin k // c ≠ a}).symm

theorem step1NSSiblingEnumeration_cover {k : Nat} (a c : Fin k) (hc : c ≠ a) :
    ∃ q : Fin (step1NSSiblingCount a), (step1NSSiblingEnumeration a q).1 = c := by
  let x : {c : Fin k // c ≠ a} := ⟨c, hc⟩
  refine ⟨(Fintype.equivFin {c : Fin k // c ≠ a}) x, ?_⟩
  simp [step1NSSiblingEnumeration, x]

/-- Selected successor level followed by the canonical list of sibling levels. -/
noncomputable def step1NSSuccessorLevelFamily
    (D : ActiveStratificationData (n + 2) k d) (C : Step1SelectedChain n k)
    (j : Step1TierIndex n) : Fin (step1NSSiblingCount (C.headAt j) + 1) → ℂ → ℂ :=
  Fin.cases (step1SelectedLevelFunction D C j)
    (fun q => D.level (j, (step1NSSiblingEnumeration (C.headAt j) q).1))

@[simp] theorem step1NSSuccessorLevelFamily_zero
    (D : ActiveStratificationData (n + 2) k d) (C : Step1SelectedChain n k)
    (j : Step1TierIndex n) :
    step1NSSuccessorLevelFamily D C j 0 = step1SelectedLevelFunction D C j :=
  rfl

/-- A property which is stable on one punctured disc around the old tier point.
The cascade uses this for the finite tower-dominance inequalities. -/
structure Step1AdjacentDominancePersistence (center : ℂ) (Good : ℂ → Prop) where
  radius : ℝ
  radius_pos : 0 < radius
  holds : ∀ {z : ℂ}, z ∈ puncturedDisc center radius → Good z

/-! ### Complete finite-family dominance and persistence -/

/-- A variable occurring in a polynomial supported through layer `q` lies in
one of those layers. -/
theorem mem_vars_layer_le_of_polynomialInLayersLE {L kk q : Nat}
    {f : FormalPoly L kk} (hf : PolynomialInLayersLE q f)
    {x : FormalVar L kk} (hx : x ∈ f.vars) : x.1.1 ≤ q := by
  rw [MvPolynomial.mem_vars_iff_mem_support] at hx
  rcases hx with ⟨m, hm, hxm⟩
  by_contra hnot
  exact (Finsupp.mem_support_iff.mp hxm) (hf m hm x (by omega))

/-- A tower threshold only reads its lower coefficients and earlier selected
variables.  Hence agreement on those data gives the same threshold. -/
theorem dominanceTowerThreshold_congr_of_agree {L kk p : Nat}
    {c : HeadChain L kk p} {f : FormalPoly L kk}
    (T : DominanceTowerData c f) (i : Fin p)
    {z₁ z₂ : FormalVar L kk → ℂ}
    (hlower : ∀ s, evalFormalPolyComplex z₁ (T.lowerCoeff i s) =
      evalFormalPolyComplex z₂ (T.lowerCoeff i s))
    (hprior : ∀ j : Fin p, j.1 < i.1 →
      z₁ (c.selectedVar j) = z₂ (c.selectedVar j)) :
    dominanceTowerThreshold T i z₁ = dominanceTowerThreshold T i z₂ := by
  have hsum : towerLowerNormSum T i z₁ = towerLowerNormSum T i z₂ := by
    unfold towerLowerNormSum
    exact Finset.sum_congr rfl (fun s _ => by rw [hlower s])
  have hprod : towerPriorNormProduct c T.degree i.1 z₁ =
      towerPriorNormProduct c T.degree i.1 z₂ := by
    unfold towerPriorNormProduct
    refine Finset.prod_congr rfl (fun j hj => ?_)
    rw [hprior j (Finset.mem_filter.mp hj).2]
  unfold dominanceTowerThreshold
  rw [hsum, hprod]

/-- A sufficiently long family prefix contains the complete ignition tower at
the requested later tier. -/
theorem Step1FiniteFamilyDominance.ignition
    {theta theta' : Params (n + 2) k d}
    {H : Step1StandingHypotheses r theta theta'} {w v : Vec d}
    {hsep : (∏ idx : Step1SeparatedFactorIndex n k,
      step1SeparatedFactorValue H w v idx) ≠ 0}
    {h : Fin k} {q : Nat} {z : FormalVar (n + 2) k → ℂ}
    (hdom : Step1FiniteFamilyDominance H w v hsep h q z)
    (j : Step1LaterTierIndex n) (hj : j.1 ≤ q) :
    step1TowerDominance (step1CanonicalIgnitionTower H w v h j) z := by
  intro i
  have hi := hdom (Sum.inl j) i (lt_of_lt_of_le i.2 hj)
  simpa [step1CanonicalDominanceMember] using hi

/-- The full family prefix contains every terminal-residue tower. -/
theorem Step1FiniteFamilyDominance.residue
    {theta theta' : Params (n + 2) k d}
    {H : Step1StandingHypotheses r theta theta'} {w v : Vec d}
    {hsep : (∏ idx : Step1SeparatedFactorIndex n k,
      step1SeparatedFactorValue H w v idx) ≠ 0}
    {h : Fin k} {q : Nat} {z : FormalVar (n + 2) k → ℂ}
    (hdom : Step1FiniteFamilyDominance H w v hsep h q z)
    (i : Step1ResidueCoordinateIndex H w h) (hq : n + 1 ≤ q) :
    step1TowerDominance (step1CanonicalResidueTower H w v h i) z := by
  intro s
  have hs := hdom (Sum.inr i) s (lt_of_lt_of_le s.2 hq)
  simpa [step1CanonicalDominanceMember] using hs

/-- Complete family dominance makes a terminal residue polynomial nonzero at
the actual gate assignment. -/
theorem Step1FiniteFamilyDominance.residue_eval_ne_zero
    {theta theta' : Params (n + 2) k d}
    {H : Step1StandingHypotheses r theta theta'} {w v : Vec d}
    {hsep : (∏ idx : Step1SeparatedFactorIndex n k,
      step1SeparatedFactorValue H w v idx) ≠ 0}
    {h : Fin k} {q : Nat} {z : FormalVar (n + 2) k → ℂ}
    (hdom : Step1FiniteFamilyDominance H w v hsep h q z)
    (i : Step1ResidueCoordinateIndex H w h) (hq : n + 1 ≤ q) :
    evalFormalPolyComplex z (step1CanonicalResiduePoly H w v h i) ≠ 0 := by
  exact step1TowerDominance_eval_ne_zero
    (step1CanonicalResidueTower_degree_pos H w v h i)
    (step1CanonicalResidueTower_topConstant_ne_zero H w v h i)
    (by simpa [DominanceTowerTopConstant, CanonicalTowerTopConstant] using
      step1CanonicalResidueTower_topConstant H w v h i)
    (by simpa [DominanceTowerFinalCoeff, CanonicalTowerFinalCoeff] using
      step1CanonicalResidueTower_finalCoeff H w v h i)
    (by simpa [DominanceTowerEvalRecurrence, CanonicalTowerEvalRecurrence] using
      step1CanonicalResidueTower_evalRecurrence H w v h i)
    (hdom.residue i hq)

/-- **Finite-family dominance persistence.**  At a tier-`j` selected pole,
all old strict inequalities persist by continuity.  For every tower containing
stage `j`, its threshold omits the selected layer-`j` variable, while that gate
blows up; consequently the new stage is cleared on a sufficiently small
punctured disc. -/
noncomputable def step1FiniteFamilyDominancePersistence_nsActive
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w v : Vec d)
    (hsep : (∏ idx : Step1SeparatedFactorIndex n k,
      step1SeparatedFactorValue H w v idx) ≠ 0)
    (h : Fin k) (j : Step1TierIndex n) (hj : j.1 ≤ n)
    {center : ℂ}
    (hcenterOmega : center ∈
      (nsActiveStratificationData (r := r) theta' w v).Omega j.1)
    (hactive : IsActiveVar theta'
      ((step1TargetSelectedChain H h).selectedVar j))
    (hselectedOnly : step1SelectedOnlyCollision
      (nsActiveStratificationData (r := r) theta' w v)
      (step1TargetSelectedChain H h) j center)
    (N : Step1SuccessorPoleNormalForm
      (nsActiveStratificationData (r := r) theta' w v)
      (step1TargetSelectedChain H h) j center)
    (hdom : Step1FiniteFamilyDominance H w v hsep h j.1
      (fun x => nsActiveGate (r := r) theta' w v x center)) :
    Step1AdjacentDominancePersistence center (fun z =>
      Step1FiniteFamilyDominance H w v hsep h (j.1 + 1)
        (fun x => nsActiveGate (r := r) theta' w v x z)) := by
  classical
  let C := step1TargetSelectedChain H h
  let D := nsActiveStratificationData (r := r) theta' w v
  let A : ℂ → FormalVar (n + 2) k → ℂ :=
    fun z x => nsActiveGate (r := r) theta' w v x z
  let bad : FormalVar (n + 2) k := C.selectedVar j
  have hbad_layer : bad.1.1 = j.1 := rfl
  let A' : ℂ → FormalVar (n + 2) k → ℂ := fun z x =>
    if x.1.1 ≤ j.1 ∧ x ≠ bad then A z x else 0
  let Acenter : FormalVar (n + 2) k → ℂ := fun x =>
    if x.1.1 ≤ j.1 ∧ x ≠ bad then A center x else 0
  have hgood_analytic : ∀ x : FormalVar (n + 2) k,
      x.1.1 ≤ j.1 ∧ x ≠ bad → AnalyticAt ℂ (A · x) center := by
    rintro x ⟨hxle, hxne⟩
    rcases lt_or_eq_of_le hxle with hxlt | hxeq
    · exact (nsActiveGate_prior_analyticOnNhd (r := r) theta' w v j hxlt)
        center hcenterOmega
    · have hxlayer : x.1 = j := Fin.ext hxeq
      have hxhead : x.2 ≠ C.headAt j := by
        intro heq
        apply hxne
        exact Prod.ext hxlayer heq
      have homega : center ∈ D.Omega x.1.1 := by
        simpa [D, hxeq] using hcenterOmega
      exact nsActiveGate_analyticAt_of_mem_omega (r := r) theta' w v x homega
        (fun _hxactive => by
          have hav := hselectedOnly.2 x.2 hxhead
          change nsActiveLevel (r := r) theta' w v (j, x.2) center ∉ Pi at hav
          have hxpair : (j, x.2) = x := Prod.ext hxlayer.symm rfl
          rw [hxpair] at hav
          exact hav)
  have hA'tendsto : Tendsto A' (nhdsWithin center ({center}ᶜ : Set ℂ))
      (nhds Acenter) := by
    rw [tendsto_pi_nhds]
    intro x
    by_cases hx : x.1.1 ≤ j.1 ∧ x ≠ bad
    · have ht : Tendsto (fun z => A z x)
          (nhdsWithin center ({center}ᶜ : Set ℂ)) (nhds (A center x)) :=
        (hgood_analytic x hx).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have hxfin : x.1 ≤ j := hx.1
      simpa [A', Acenter, hx, hxfin, A] using ht
    · simp only [A', Acenter]
      have hzero : (if x.1.1 ≤ j.1 ∧ x ≠ bad then A center x else 0) = 0 :=
        if_neg hx
      have hfun : (fun i => if x.1.1 ≤ j.1 ∧ x ≠ bad then A i x else 0) =
          (fun _ => (0 : ℂ)) := by
        funext z
        rw [if_neg hx]
      rw [hfun, hzero]
      exact tendsto_const_nhds
  have hbadBlow : Tendsto (fun z => ‖A z bad‖)
      (nhdsWithin center ({center}ᶜ : Set ℂ)) atTop := by
    have heq : step1SelectedGateFunction D C j = (fun z => A z bad) := by
      funext z
      rw [step1SelectedGateFunction_apply]
      change csig (nsActiveLevel (r := r) theta' w v (C.selectedVar j) z) =
        nsActiveGate (r := r) theta' w v (C.selectedVar j) z
      exact (nsActiveGate_eq_csig_level theta' w v hactive z).symm
    have hblow := N.normalForm.blowsUpAt (by exact_mod_cast N.q_pos)
    rw [heq] at hblow
    exact hblow
  have core : ∀ (idx : Step1TowerMemberIndex H w h)
      (i : Fin (step1TowerMemberChainLength H w h idx)),
      ∀ᶠ z in nhdsWithin center ({center}ᶜ : Set ℂ), i.1 < j.1 + 1 →
        dominanceTowerThreshold
            (step1CanonicalDominanceMember H w v hsep h idx).tower i (A z) <
          ‖A z ((step1TowerMemberHeadChain H w h idx).selectedVar i)‖ := by
    intro idx i
    let M := step1CanonicalDominanceMember H w v hsep h idx
    let c := step1TowerMemberHeadChain H w h idx
    by_cases hij : i.1 < j.1 + 1
    · have hijle : i.1 ≤ j.1 := by omega
      have hselected_eq : i.1 = j.1 → c.selectedVar i = bad := by
        intro heq
        apply Prod.ext
        · exact Fin.ext heq
        · change C.headAt ⟨i.1, _⟩ = C.headAt j
          congr 1
          exact Fin.ext heq
      have hvarGood : ∀ s x, x ∈ (M.tower.lowerCoeff i s).vars →
          x.1.1 ≤ j.1 ∧ x ≠ bad := by
        intro s x hx
        have hxle : x.1.1 ≤ i.1 :=
          mem_vars_layer_le_of_polynomialInLayersLE
            (M.lowerCoeff_support i s) hx
        refine ⟨hxle.trans hijle, ?_⟩
        intro hxbad
        have hijeq : i.1 = j.1 := by
          have : x.1.1 = j.1 := by rw [hxbad, hbad_layer]
          omega
        apply M.lowerCoeff_selectedVar_notMem i s
        rw [hselected_eq hijeq, ← hxbad]
        exact hx
      have hpriorGood : ∀ q : Fin (step1TowerMemberChainLength H w h idx),
          q.1 < i.1 → (c.selectedVar q).1.1 ≤ j.1 ∧ c.selectedVar q ≠ bad := by
        intro q hqi
        have hlayer : (c.selectedVar q).1.1 = q.1 := rfl
        refine ⟨by rw [hlayer]; omega, ?_⟩
        intro hbad
        have : q.1 = j.1 := by rw [← hlayer, hbad, hbad_layer]
        omega
      have hcongr : ∀ z, dominanceTowerThreshold M.tower i (A z) =
          dominanceTowerThreshold M.tower i (A' z) := by
        intro z
        refine dominanceTowerThreshold_congr_of_agree M.tower i ?_ ?_
        · intro s
          apply evalFormalPolyComplex_congr_on_vars
          intro x hx
          have hg := hvarGood s x hx
          simp only [A']
          rw [if_pos hg]
        · intro q hqi
          have hg := hpriorGood q hqi
          simp only [A']
          rw [if_pos hg]
      have hthrTendsto : Tendsto
          (fun z => dominanceTowerThreshold M.tower i (A z))
          (nhdsWithin center ({center}ᶜ : Set ℂ))
          (nhds (dominanceTowerThreshold M.tower i Acenter)) := by
        have ht := ((continuous_dominanceTowerThreshold M.tower
          M.topConstant_ne_zero i).tendsto Acenter).comp hA'tendsto
        exact ht.congr (fun z => (hcongr z).symm)
      rcases lt_or_eq_of_le hijle with hijlt | hijeq
      · have hRHSanalytic : AnalyticAt ℂ (fun z => A z (c.selectedVar i)) center := by
          apply hgood_analytic
          have hlayer : (c.selectedVar i).1.1 = i.1 := rfl
          refine ⟨by rw [hlayer]; exact le_of_lt hijlt, ?_⟩
          intro hbad
          have : i.1 = j.1 := by rw [← hlayer, hbad, hbad_layer]
          omega
        have hRHStend : Tendsto (fun z => ‖A z (c.selectedVar i)‖)
            (nhdsWithin center ({center}ᶜ : Set ℂ))
            (nhds ‖A center (c.selectedVar i)‖) :=
          (hRHSanalytic.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).norm
        have hthrCenter : dominanceTowerThreshold M.tower i Acenter =
            dominanceTowerThreshold M.tower i (A center) := by
          rw [hcongr center]
        have hstrict := hdom idx i hijlt
        have hlimlt : dominanceTowerThreshold M.tower i Acenter <
            ‖A center (c.selectedVar i)‖ := by
          rw [hthrCenter]
          exact hstrict
        exact (hthrTendsto.eventually_lt hRHStend hlimlt).mono
          (fun _ hz _ => hz)
      · have hsel : c.selectedVar i = bad := hselected_eq hijeq
        have hRHSblow : Tendsto (fun z => ‖A z (c.selectedVar i)‖)
            (nhdsWithin center ({center}ᶜ : Set ℂ)) atTop := by
          simpa [hsel] using hbadBlow
        have hevent : ∀ᶠ z in nhdsWithin center ({center}ᶜ : Set ℂ),
            dominanceTowerThreshold M.tower i (A z) <
              ‖A z (c.selectedVar i)‖ := by
          filter_upwards
            [hthrTendsto (Iio_mem_nhds
              (lt_add_one (dominanceTowerThreshold M.tower i Acenter))),
             hRHSblow.eventually
              (eventually_gt_atTop (dominanceTowerThreshold M.tower i Acenter + 1))]
            with z hzthr hzblow
          exact lt_trans hzthr hzblow
        exact hevent.mono (fun _ hz _ => hz)
    · exact Filter.Eventually.of_forall (fun _ hcontra => absurd hcontra hij)
  haveI : Finite (Σ idx : Step1TowerMemberIndex H w h,
      Fin (step1TowerMemberChainLength H w h idx)) := by infer_instance
  have hall : ∀ᶠ z in nhdsWithin center ({center}ᶜ : Set ℂ),
      ∀ q : (Σ idx : Step1TowerMemberIndex H w h,
        Fin (step1TowerMemberChainLength H w h idx)), q.2.1 < j.1 + 1 →
          dominanceTowerThreshold
              (step1CanonicalDominanceMember H w v hsep h q.1).tower q.2 (A z) <
            ‖A z ((step1TowerMemberHeadChain H w h q.1).selectedVar q.2)‖ := by
    rw [Filter.eventually_all]
    rintro ⟨idx, i⟩
    exact core idx i
  have heventually : ∀ᶠ z in nhdsWithin center ({center}ᶜ : Set ℂ),
      Step1FiniteFamilyDominance H w v hsep h (j.1 + 1) (A z) := by
    filter_upwards [hall] with z hz
    intro idx i hi
    exact hz ⟨idx, i⟩ hi
  have hmem := Metric.mem_nhdsWithin_iff.mp heventually
  refine ⟨Classical.choose hmem, (Classical.choose_spec hmem).1, ?_⟩
  intro z hz
  apply (Classical.choose_spec hmem).2
  exact ⟨Metric.mem_ball.mpr hz.2, by simpa using hz.1⟩

/-- Ambient sibling/window data with the selected-pole field deliberately
omitted: the adjacent theorem derives that pole from the current gate normal
form.  Thus this input cannot merely restate existence of the desired next
collision. -/
structure Step1AdjacentSiblingData (Omega : Set ℂ) (center : ℂ) (rho0 : ℝ)
    {K : Nat} (F : Fin (K + 1) → ℂ → ℂ) : Prop where
  omega_domain : KHead.PlaneDomain Omega
  nonneg_subset : {τ : ℂ | ∃ t : ℝ, 0 ≤ t ∧ τ = t} ⊆ Omega
  center_notMem : center ∉ Omega
  puncturedDisc_subset : puncturedDisc center rho0 ⊆ Omega
  radius_pos : 0 < rho0
  analytic_on_omega : ∀ c : Fin (K + 1), AnalyticOnNhd ℂ (F c) Omega
  sibling_meromorphic_at_center : ∀ c : Fin K, MeromorphicAt (F c.succ) center
  common_real_value : ∃ b : ℝ, b ≠ 0 ∧ ∀ c : Fin (K + 1), F c 0 = (b : ℂ)
  real_valued_on_nonnegative :
    ∀ c : Fin (K + 1), IsRealValuedOn (F c) nonnegativeRealAxis
  sibling_not_identical : ∀ c : Fin K, ¬ Set.EqOn (F c.succ) (F 0) Omega

/-! ### Concrete coefficient analyticity and sibling order -/

/-- Polynomial evaluation is analytic when every coordinate assignment is
analytic. -/
theorem evalFormalPolyComplex_analyticAt_of_all_ns {L kk : Nat} {center : ℂ}
    {eta : ℂ → FormalVar L kk → ℂ} (p : FormalPoly L kk)
    (heta : ∀ x, AnalyticAt ℂ (fun z => eta z x) center) :
    AnalyticAt ℂ (fun z => evalFormalPolyComplex (eta z) p) center := by
  simp only [evalFormalPolyComplex]
  induction p using MvPolynomial.induction_on with
  | C a =>
      simp only [MvPolynomial.eval₂_C]
      exact analyticAt_const
  | add p q hp hq =>
      simp only [MvPolynomial.eval₂_add]
      exact hp.add hq
  | mul_X p x hp =>
      simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
      exact hp.mul (heta x)

/-- Although `nsLevelCoeff` is a priori known analytic only on the successor
domain, at a selected-only tier point its coefficient polynomial omits the
singular selected gate.  Replacing that gate and all later gates by zero gives
an analytic assignment with the same coefficient evaluation. -/
theorem nsLevelCoeff_analyticAt_of_selectedOnly
    {theta : Params (n + 2) k d} (w v : Vec d)
    (C : Step1SelectedChain n k) (j jsucc : Step1TierIndex n)
    (hadj : jsucc.1 = j.1 + 1) {center : ℂ}
    (hcenterOmega : center ∈
      (nsActiveStratificationData (r := r) theta w v).Omega j.1)
    (hselectedOnly : step1SelectedOnlyCollision
      (nsActiveStratificationData (r := r) theta w v) C j center)
    (a : Fin k) (s : Nat) :
    AnalyticAt ℂ (nsLevelCoeff (r := r) theta w v jsucc a (C.selectedVar j) s)
      center := by
  classical
  let bad : FormalVar (n + 2) k := C.selectedVar j
  let actual : ℂ → FormalVar (n + 2) k → ℂ :=
    fun z x => nsActiveGate (r := r) theta w v x z
  let eta : ℂ → FormalVar (n + 2) k → ℂ := fun z x =>
    if x.1.1 ≤ j.1 ∧ x ≠ bad then actual z x else 0
  have heta : ∀ x, AnalyticAt ℂ (fun z => eta z x) center := by
    intro x
    by_cases hx : x.1.1 ≤ j.1 ∧ x ≠ bad
    · rcases lt_or_eq_of_le hx.1 with hxlt | hxeq
      · have han := (nsActiveGate_prior_analyticOnNhd (r := r) theta w v j hxlt)
          center hcenterOmega
        simpa [eta, actual, hx, show x.1 ≤ j from hx.1] using han
      · have hxlayer : x.1 = j := Fin.ext hxeq
        have hxhead : x.2 ≠ C.headAt j := by
          intro heq
          apply hx.2
          exact Prod.ext hxlayer heq
        have homega : center ∈
            (nsActiveStratificationData (r := r) theta w v).Omega x.1.1 := by
          simpa [hxeq] using hcenterOmega
        have han := nsActiveGate_analyticAt_of_mem_omega (r := r)
          theta w v x homega (fun _ => by
            have hav := hselectedOnly.2 x.2 hxhead
            change nsActiveLevel (r := r) theta w v (j, x.2) center ∉ Pi at hav
            have hxpair : (j, x.2) = x := Prod.ext hxlayer.symm rfl
            rwa [hxpair] at hav)
        simpa [eta, actual, hx, show x.1 ≤ j from hx.1] using han
    · have heq : (fun z => eta z x) = fun _ => (0 : ℂ) := by
        have hxfin : ¬(x.1 ≤ j ∧ x ≠ bad) := by
          intro h
          exact hx ⟨h.1, h.2⟩
        funext z
        simp [eta, hxfin]
      rw [heq]
      exact analyticAt_const
  let p := coeffOfVar (C.selectedVar j) s (formalSlope theta w v jsucc a)
  have hp_an : AnalyticAt ℂ (fun z => evalFormalPolyComplex (eta z) p) center :=
    evalFormalPolyComplex_analyticAt_of_all_ns p heta
  have heq : nsLevelCoeff (r := r) theta w v jsucc a (C.selectedVar j) s =
      fun z => evalFormalPolyComplex (eta z) p := by
    funext z
    apply evalFormalPolyComplex_congr_on_vars
    intro x hx
    have hxlt : x.1.1 < jsucc.1 :=
      lt_of_mem_vars_of_supportBefore
        (formalSlope_coeffOfVar_supportBefore theta w v jsucc a (C.selectedVar j) s) hx
    have hxle : x.1.1 ≤ j.1 := by omega
    have hxne : x ≠ bad := by
      intro hxbad
      apply coeffOfVar_notMem_vars (x := C.selectedVar j) (s := s)
        (f := formalSlope theta w v jsucc a)
      simpa [bad, hxbad] using hx
    have hxfin : x.1 ≤ j := hxle
    simp [eta, actual, hxfin, hxne]
  rw [heq]
  exact hp_an

/-- A finite meromorphic order yields a Laurent normal form whose pole order
is the negative of that order. -/
theorem laurentNormalFormAt_of_meromorphicOrder_int_ns {f : ℂ → ℂ}
    {center : ℂ} {ord : ℤ} (hmero : MeromorphicAt f center)
    (hord : meromorphicOrderAt f center = (ord : ℤ)) :
    ∃ coeff : ℂ, LaurentNormalFormAt f center (-ord) coeff := by
  rcases (meromorphicOrderAt_eq_int_iff hmero).1 hord with ⟨g, hg, hg0, hfg⟩
  refine ⟨g center, hg0, g, hg, rfl, ?_⟩
  filter_upwards [hfg] with z hz
  rw [hz]
  simp [smul_eq_mul, mul_comm, neg_neg]

theorem laurentNormalFormAt_of_meromorphic_orderBound_ns {f : ℂ → ℂ}
    {center : ℂ} {Nbound : ℤ} (hmero : MeromorphicAt f center)
    (hne : meromorphicOrderAt f center ≠ ⊤)
    (hbound : ((-Nbound : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f center) :
    ∃ (mu : ℤ) (coeff : ℂ), mu ≤ Nbound ∧
      LaurentNormalFormAt f center mu coeff := by
  rcases WithTop.ne_top_iff_exists.mp hne with ⟨ord, hord⟩
  rcases laurentNormalFormAt_of_meromorphicOrder_int_ns hmero hord.symm with
    ⟨coeff, hNF⟩
  refine ⟨-ord, coeff, ?_, hNF⟩
  have hle : ((-Nbound : ℤ) : WithTop ℤ) ≤ ((ord : ℤ) : WithTop ℤ) := hord ▸ hbound
  have : -Nbound ≤ ord := by exact_mod_cast hle
  omega

/-- Identity-theorem finiteness of meromorphic order on a plane domain. -/
theorem meromorphicOrderAt_ne_top_of_domain_ns {f : ℂ → ℂ}
    {U : Set ℂ} {center : ℂ} {rho : ℝ}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsPreconnected U)
    (hzero : (0 : ℂ) ∈ U) (hfzero : f 0 ≠ 0)
    (hrho : 0 < rho) (hsub : puncturedDisc center rho ⊆ U) :
    meromorphicOrderAt f center ≠ ⊤ := by
  intro htop
  have hzeroEventually : ∀ᶠ z in nhdsWithin center ({center}ᶜ : Set ℂ), f z = 0 :=
    meromorphicOrderAt_eq_top_iff.1 htop
  rcases Metric.mem_nhdsWithin_iff.mp hzeroEventually with ⟨eps, heps, hepsZero⟩
  have hzeroNear : ∀ z : ℂ, dist z center < eps → z ≠ center → f z = 0 := by
    intro z hdist hne
    exact hepsZero ⟨Metric.mem_ball.mpr hdist, by simpa using hne⟩
  let rr := min eps rho
  have hrr : 0 < rr := lt_min heps hrho
  let z0 : ℂ := center + ((rr / 2 : ℝ) : ℂ)
  have hzdist : dist z0 center = rr / 2 := by
    rw [show z0 = center + ((rr / 2 : ℝ) : ℂ) from rfl,
      Complex.dist_eq, add_sub_cancel_left, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hz0ne : z0 ≠ center := by
    intro heq
    rw [heq, dist_self] at hzdist
    linarith
  have hz0U : z0 ∈ U := by
    apply hsub
    refine ⟨hz0ne, ?_⟩
    rw [hzdist]
    have hle : rr ≤ rho := min_le_right _ _
    linarith
  have hballZero : ∀ z ∈ Metric.ball z0 (rr / 4), f z = 0 := by
    intro z hz
    have hzz0 : dist z z0 < rr / 4 := Metric.mem_ball.mp hz
    have hzcenter : dist z center < eps := by
      have htri := dist_triangle z z0 center
      rw [hzdist] at htri
      have hle : rr ≤ eps := min_le_left _ _
      linarith
    have hzne : z ≠ center := by
      intro heq
      rw [heq, dist_comm, hzdist] at hzz0
      linarith
    exact hzeroNear z hzcenter hzne
  have hfreq : ∃ᶠ z in nhdsWithin z0 ({z0}ᶜ : Set ℂ), f z = 0 := by
    have hev : ∀ᶠ z in nhds z0, f z = 0 :=
      Metric.eventually_nhds_iff.mpr
        ⟨rr / 4, by positivity, fun {z} hz => hballZero z (Metric.mem_ball.mpr hz)⟩
    exact (hev.filter_mono nhdsWithin_le_nhds).frequently
  have hallzero : Set.EqOn f 0 U :=
    hf.eqOn_zero_of_preconnected_of_frequently_eq_zero hU hz0U hfreq
  exact hfzero (by simpa using hallzero hzero)

/-- Every successor head level is meromorphic at the current selected pole and
has pole order at most twice the selected-gate order. -/
theorem nsSuccessorLevel_meromorphicOrderBound
    {theta : Params (n + 2) k d} (w v : Vec d)
    (C : Step1SelectedChain n k) (j jsucc : Step1TierIndex n)
    (hadj : jsucc.1 = j.1 + 1) {center : ℂ}
    (hcenterOmega : center ∈
      (nsActiveStratificationData (r := r) theta w v).Omega j.1)
    (hselectedOnly : step1SelectedOnlyCollision
      (nsActiveStratificationData (r := r) theta w v) C j center)
    (hactive : IsActiveVar theta (C.selectedVar j))
    (N : Step1SuccessorPoleNormalForm
      (nsActiveStratificationData (r := r) theta w v) C j center)
    (a : Fin k) :
    MeromorphicAt (nsActiveLevel (r := r) theta w v (jsucc, a)) center ∧
      (((-(2 * N.q : ℤ)) : ℤ) : WithTop ℤ) ≤
        meromorphicOrderAt (nsActiveLevel (r := r) theta w v (jsucc, a)) center := by
  let sgate := nsActiveGate (r := r) theta w v (C.selectedVar j)
  let Psi := nsLevelCoeff (r := r) theta w v jsucc a (C.selectedVar j) 2
  let Bet := nsLevelCoeff (r := r) theta w v jsucc a (C.selectedVar j) 1
  let Gam := nsLevelCoeff (r := r) theta w v jsucc a (C.selectedVar j) 0
  have hPsi : AnalyticAt ℂ Psi center :=
    nsLevelCoeff_analyticAt_of_selectedOnly w v C j jsucc hadj hcenterOmega
      hselectedOnly a 2
  have hBet : AnalyticAt ℂ Bet center :=
    nsLevelCoeff_analyticAt_of_selectedOnly w v C j jsucc hadj hcenterOmega
      hselectedOnly a 1
  have hGam : AnalyticAt ℂ Gam center :=
    nsLevelCoeff_analyticAt_of_selectedOnly w v C j jsucc hadj hcenterOmega
      hselectedOnly a 0
  have hsgateNF : LaurentNormalFormAt sgate center (N.q : ℤ) N.coeff := by
    have heq : step1SelectedGateFunction
        (nsActiveStratificationData (r := r) theta w v) C j = sgate := by
      funext z
      rw [step1SelectedGateFunction_apply]
      change csig (nsActiveLevel (r := r) theta w v (C.selectedVar j) z) =
        nsActiveGate (r := r) theta w v (C.selectedVar j) z
      exact (nsActiveGate_eq_csig_level theta w v hactive z).symm
    rw [← heq]
    exact N.normalForm
  have hsmero : MeromorphicAt sgate center := hsgateNF.meromorphicAt
  have hsord : meromorphicOrderAt sgate center =
      ((-(N.q : ℤ) : ℤ) : WithTop ℤ) := hsgateNF.order_eq
  let lead : ℂ → ℂ := fun z => z * Psi z * (sgate z) ^ 2
  let rest : ℂ → ℂ := fun z => z * Bet z * sgate z +
    (z * Gam z + (logScale r : ℂ))
  have hleadMero : MeromorphicAt lead center :=
    (analyticAt_id.mul hPsi).meromorphicAt.mul (hsmero.pow 2)
  have hrestMero : MeromorphicAt rest center :=
    ((analyticAt_id.mul hBet).meromorphicAt.mul hsmero).add
      ((analyticAt_id.mul hGam).add analyticAt_const).meromorphicAt
  have hsquareOrd : meromorphicOrderAt (fun z => (sgate z) ^ 2) center =
      (((-(2 * N.q : ℤ)) : ℤ) : WithTop ℤ) := by
    have heq : (fun z => (sgate z) ^ 2) = sgate * sgate := by
      funext z
      simp [pow_two]
    rw [heq, meromorphicOrderAt_mul hsmero hsmero, hsord, ← WithTop.coe_add]
    congr 2
    ring
  have hleadOrd : (((-(2 * N.q : ℤ)) : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt lead center := by
    have hmul := meromorphicOrderAt_mul
      (f := fun z => z * Psi z) (g := fun z => (sgate z) ^ 2)
      (analyticAt_id.mul hPsi).meromorphicAt (hsmero.pow 2)
    change _ ≤ meromorphicOrderAt ((fun z => z * Psi z) *
      (fun z => (sgate z) ^ 2)) center
    rw [hmul, hsquareOrd]
    exact le_add_of_nonneg_left
      (analyticAt_id.mul hPsi).meromorphicOrderAt_nonneg
  have hlinearOrd : (((-(N.q : ℤ)) : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (fun z => z * Bet z * sgate z) center := by
    have hmul := meromorphicOrderAt_mul
      (f := fun z => z * Bet z) (g := sgate)
      (analyticAt_id.mul hBet).meromorphicAt hsmero
    change _ ≤ meromorphicOrderAt ((fun z => z * Bet z) * sgate) center
    rw [hmul, hsord]
    exact le_add_of_nonneg_left (analyticAt_id.mul hBet).meromorphicOrderAt_nonneg
  have hregularOrd : (0 : WithTop ℤ) ≤
      meromorphicOrderAt (fun z => z * Gam z + (logScale r : ℂ)) center :=
    ((analyticAt_id.mul hGam).add analyticAt_const).meromorphicOrderAt_nonneg
  have hrestOrd : (((-(N.q : ℤ)) : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt rest center := by
    refine le_trans (le_min hlinearOrd ?_)
      (meromorphicOrderAt_add
        ((analyticAt_id.mul hBet).meromorphicAt.mul hsmero)
        ((analyticAt_id.mul hGam).add analyticAt_const).meromorphicAt)
    exact le_trans (WithTop.coe_le_coe.mpr (by omega)) hregularOrd
  have htwice_le : (((-(2 * N.q : ℤ)) : ℤ) : WithTop ℤ) ≤
      (((-(N.q : ℤ)) : ℤ) : WithTop ℤ) := WithTop.coe_le_coe.mpr (by omega)
  have hsumOrd : (((-(2 * N.q : ℤ)) : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (lead + rest) center :=
    le_trans (le_min hleadOrd (htwice_le.trans hrestOrd))
      (meromorphicOrderAt_add hleadMero hrestMero)
  have hlevelEq : nsActiveLevel (r := r) theta w v (jsucc, a) = lead + rest := by
    funext z
    have hquad := nsActiveLevel_quadratic_in_prior_gate (r := r) theta w v
      jsucc a (C.selectedVar j)
      (formalSlope_blockDegree_two theta w v jsucc a (C.selectedVar j)) z
    simp only [lead, rest, sgate, Psi, Bet, Gam, Pi.add_apply]
    rw [hquad]
    ring
  rw [hlevelEq]
  exact ⟨hleadMero.add hrestMero, hsumOrd⟩

/-- The recursively constructed active gate takes the all-alpha value at the
origin whenever its head is active. -/
theorem nsActiveGate_zero_of_active {theta : Params (n + 2) k d}
    (w v : Vec d) {x : FormalVar (n + 2) k} (hx : IsActiveVar theta x) :
    nsActiveGate (r := r) theta w v x 0 = (alpha r : ℂ) := by
  rw [nsActiveGate_eq_csig_level theta w v hx 0, nsActiveLevel_zero]
  simpa [alpha, csig] using
    TransformerIdentifiability.NLayer.csig_ofReal (logScale r)

/-- Concrete successor-domain, sibling, and Laurent-order data consumed by the
adjacent window theorem.  Every field follows from the active stratification,
the selected-only current collision, and the separated probe's all-alpha corner
certificate. -/
theorem exists_step1AdjacentSiblingPackage_nsActive
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta')
    (P : Step1SeparatedProbePackage H) (hr : 1 < r)
    (h : Fin k) (j jsucc : Step1TierIndex n)
    (hadj : jsucc.1 = j.1 + 1) {center : ℂ}
    (hcenterOmega : center ∈
      (nsActiveStratificationData (r := r) theta' P.w P.v).Omega j.1)
    (hselectedOnly : step1SelectedOnlyCollision
      (nsActiveStratificationData (r := r) theta' P.w P.v)
      (step1TargetSelectedChain H h) j center)
    (N : Step1SuccessorPoleNormalForm
      (nsActiveStratificationData (r := r) theta' P.w P.v)
      (step1TargetSelectedChain H h) j center) :
    ∃ rho : ℝ,
      Step1AdjacentSiblingData
        ((nsActiveStratificationData (r := r) theta' P.w P.v).Omega jsucc.1)
        center rho
        (step1NSSuccessorLevelFamily
          (nsActiveStratificationData (r := r) theta' P.w P.v)
          (step1TargetSelectedChain H h) jsucc) ∧
      ∀ c : Fin (step1NSSiblingCount
          ((step1TargetSelectedChain H h).headAt jsucc)),
        ∃ (mu : ℤ) (coeff : ℂ), mu ≤ (2 * N.q : Nat) ∧
          LaurentNormalFormAt
            (step1NSSuccessorLevelFamily
              (nsActiveStratificationData (r := r) theta' P.w P.v)
              (step1TargetSelectedChain H h) jsucc c.succ)
            center mu coeff := by
  classical
  let C := step1TargetSelectedChain H h
  let D := nsActiveStratificationData (r := r) theta' P.w P.v
  have hD := nsActiveHeadSingularStratification (r := r) theta' P.w P.v
  have hactiveCurrent : IsActiveVar theta' (C.selectedVar j) := by
    simpa [C, IsActiveVar, Step1SelectedChain.selectedVar] using
      step1_head_active H j (C.headAt j)
  have hstratum : center ∈ D.stratum j.1 :=
    step1SelectedOnlyCollision_mem_activeStratum hD
      (step1_head_active H j (C.headAt j)) hcenterOmega hselectedOnly
  have hnotacc : center ∉ acc (D.stratum j.1) :=
    (hD.stratum_closedDiscrete j).noAccum center hcenterOmega
  have havoid : ∀ᶠ z in nhdsWithin center ({center}ᶜ : Set ℂ),
      z ∉ D.stratum j.1 :=
    TransformerIdentifiability.NLayer.eventually_notMem_of_not_mem_acc hnotacc
  have hstay : ∀ᶠ z in nhdsWithin center ({center}ᶜ : Set ℂ),
      z ∈ D.Omega j.1 := by
    simpa using (nhdsWithin_le_nhds
      ((hD.domain j.1 (Nat.le_of_lt j.2)).isOpen.mem_nhds hcenterOmega))
  have hsuccEventually : ∀ᶠ z in nhdsWithin center ({center}ᶜ : Set ℂ),
      z ∈ D.Omega jsucc.1 := by
    filter_upwards [hstay, havoid] with z hzOmega hzAvoid
    have hz : z ∈ D.Omega j.1 \ D.stratum j.1 := ⟨hzOmega, hzAvoid⟩
    rw [hadj, hD.omega_succ j]
    exact hz
  rcases Metric.mem_nhdsWithin_iff.mp hsuccEventually with ⟨rho, hrho, hrhoSub⟩
  have hpunc : puncturedDisc center rho ⊆ D.Omega jsucc.1 := by
    intro z hz
    exact hrhoSub ⟨Metric.mem_ball.mpr hz.2, by simpa using hz.1⟩
  have hcenterNot : center ∉ D.Omega jsucc.1 := by
    rw [hadj, hD.omega_succ j]
    exact fun hz => hz.2 hstratum
  let eta : FormalVar (n + 2) k → ℂ → ℂ :=
    fun x z => nsActiveGate (r := r) theta' P.w P.v x z
  have hetaAnalytic : ∀ x, AnalyticAt ℂ (eta x) 0 := by
    intro x
    have hzeroOmega : (0 : ℂ) ∈ D.Omega x.1.1 :=
      hD.origin_mem x.1.1 (Nat.le_of_lt x.1.2)
    exact nsActiveGate_analyticAt_of_mem_omega (r := r) theta' P.w P.v x
      hzeroOmega (fun _ => by
        rw [nsActiveLevel_zero]
        exact ofReal_notMem_Pi (logScale r))
  have hetaZero : ∀ x, eta x 0 = (alpha r : ℂ) := by
    intro x
    apply nsActiveGate_zero_of_active P.w P.v
    simpa [IsActiveVar] using step1_head_active H x.1 x.2
  have hlevel : ∀ a : Fin k, D.level (jsucc, a) =
      fun z => formalLevel (r := r) theta' P.w P.v (fun x => eta x z)
        (jsucc, a) z := by
    intro a
    funext z
    exact nsActiveLevel_eq_formalLevel theta' P.w P.v (jsucc, a) z
  have hnotIdentical : ∀ a : Fin k, a ≠ C.headAt jsucc →
      ¬ Set.EqOn (D.level (jsucc, a)) (D.level (jsucc, C.headAt jsucc))
        (D.Omega jsucc.1) := by
    intro a hane hEq
    have hcorner := P.cornerSibling_ne_zero jsucc (C.headAt jsucc) a (Ne.symm hane)
    have hnot := formalLevel_not_eqOn_of_alphaCornerSlopeDiff_ne_zero
      theta' P.w P.v jsucc (D.Omega jsucc.1)
      (hD.domain jsucc.1 (Nat.le_of_lt jsucc.2)).isOpen
      (hD.origin_mem jsucc.1 (Nat.le_of_lt jsucc.2))
      eta hetaAnalytic hetaZero hcorner
    apply hnot
    intro z hz
    have heq := (hEq hz).symm
    rw [hlevel (C.headAt jsucc), hlevel a] at heq
    exact heq
  have hsiblingMeroOrder : ∀ c : Fin (step1NSSiblingCount (C.headAt jsucc)),
      MeromorphicAt
          (step1NSSuccessorLevelFamily D C jsucc c.succ) center ∧
        (((-(2 * N.q : ℤ)) : ℤ) : WithTop ℤ) ≤
          meromorphicOrderAt
            (step1NSSuccessorLevelFamily D C jsucc c.succ) center := by
    intro c
    simpa [step1NSSuccessorLevelFamily, D] using
      nsSuccessorLevel_meromorphicOrderBound P.w P.v C j jsucc hadj
        hcenterOmega hselectedOnly hactiveCurrent N
        (step1NSSiblingEnumeration (C.headAt jsucc) c).1
  have hsiblingOrder : ∀ c : Fin (step1NSSiblingCount (C.headAt jsucc)),
      ∃ (mu : ℤ) (coeff : ℂ), mu ≤ (2 * N.q : Nat) ∧
        LaurentNormalFormAt (step1NSSuccessorLevelFamily D C jsucc c.succ)
          center mu coeff := by
    intro c
    let a := (step1NSSiblingEnumeration (C.headAt jsucc) c).1
    have hactiveA : a ∈ activeHeads theta' jsucc := step1_head_active H jsucc a
    have hfinite : meromorphicOrderAt (D.level (jsucc, a)) center ≠ ⊤ :=
      meromorphicOrderAt_ne_top_of_domain_ns
        (hD.level_holomorphic jsucc a hactiveA)
        (hD.domain jsucc.1 (Nat.le_of_lt jsucc.2)).isPreconnected
        (hD.origin_mem jsucc.1 (Nat.le_of_lt jsucc.2))
        (by
          rw [hD.level_zero jsucc a hactiveA]
          exact_mod_cast ne_of_gt (KHead.logScale_pos_of_one_lt hr))
        hrho hpunc
    rcases laurentNormalFormAt_of_meromorphic_orderBound_ns
        (Nbound := (2 * N.q : ℤ)) (hsiblingMeroOrder c).1
        (by simpa [step1NSSuccessorLevelFamily, D, a] using hfinite)
        (hsiblingMeroOrder c).2 with ⟨mu, coeff, hmu, hNF⟩
    exact ⟨mu, coeff, by exact_mod_cast hmu, hNF⟩
  have hdata : Step1AdjacentSiblingData (D.Omega jsucc.1) center rho
      (step1NSSuccessorLevelFamily D C jsucc) := by
    refine
      { omega_domain := hD.domain jsucc.1 (Nat.le_of_lt jsucc.2)
        nonneg_subset := hD.nonnegative_axis_subset jsucc.1 (Nat.le_of_lt jsucc.2)
        center_notMem := hcenterNot
        puncturedDisc_subset := hpunc
        radius_pos := hrho
        analytic_on_omega := ?_
        sibling_meromorphic_at_center := fun c => (hsiblingMeroOrder c).1
        common_real_value := ?_
        real_valued_on_nonnegative := ?_
        sibling_not_identical := ?_ }
    · intro c
      refine Fin.cases ?_ (fun q => ?_) c
      · exact hD.level_holomorphic jsucc (C.headAt jsucc)
          (step1_head_active H jsucc (C.headAt jsucc))
      · exact hD.level_holomorphic jsucc
          (step1NSSiblingEnumeration (C.headAt jsucc) q).1
          (step1_head_active H jsucc _)
    · refine ⟨logScale r, ?_, ?_⟩
      · exact_mod_cast ne_of_gt (KHead.logScale_pos_of_one_lt hr)
      intro c
      refine Fin.cases ?_ (fun q => ?_) c
      · exact hD.level_zero jsucc (C.headAt jsucc)
          (step1_head_active H jsucc (C.headAt jsucc))
      · exact hD.level_zero jsucc
          (step1NSSiblingEnumeration (C.headAt jsucc) q).1
          (step1_head_active H jsucc _)
    · intro c
      refine Fin.cases ?_ (fun q => ?_) c
      · exact hD.level_real_on_nonnegative_axis jsucc (C.headAt jsucc)
          (step1_head_active H jsucc (C.headAt jsucc))
      · exact hD.level_real_on_nonnegative_axis jsucc
          (step1NSSiblingEnumeration (C.headAt jsucc) q).1
          (step1_head_active H jsucc _)
    · intro c
      exact hnotIdentical (step1NSSiblingEnumeration (C.headAt jsucc) c).1
        (step1NSSiblingEnumeration (C.headAt jsucc) c).2
  exact ⟨rho, hdata, hsiblingOrder⟩

/-- **Genuine adjacent-tier selection.**  The current selected gate normal form
first produces an exact pole normal form for the *successor selected level* at
the old center.  The neutral window/sibling theorem then selects a new nearby
point where the successor selected level hits `Pi`, every successor sibling
avoids `Pi`, the point lies in the successor recursive domain, and dominance
still holds.

The inputs are local analytic/order data and punctured-disc persistence.  None
asserts existence of a successor collision. -/
theorem step1AdjacentSelectedOnlyPoint_nsActive
    (theta : Params (n + 2) k d) (w v : Vec d) (C : Step1SelectedChain n k)
    (j jsucc : Step1TierIndex n) {center : ℂ}
    (hactiveJ : IsActiveVar theta (C.selectedVar j))
    (hcenter_ne : center ≠ 0)
    (N : Step1SuccessorPoleNormalForm
      (nsActiveStratificationData (r := r) theta w v) C j center)
    (hPsi : AnalyticAt ℂ
      (nsLevelCoeff (r := r) theta w v jsucc (C.headAt jsucc) (C.selectedVar j) 2)
      center)
    (hPsi_ne :
      nsLevelCoeff (r := r) theta w v jsucc (C.headAt jsucc) (C.selectedVar j) 2
        center ≠ 0)
    (hBet : AnalyticAt ℂ
      (nsLevelCoeff (r := r) theta w v jsucc (C.headAt jsucc) (C.selectedVar j) 1)
      center)
    (hGam0 : AnalyticAt ℂ
      (nsLevelCoeff (r := r) theta w v jsucc (C.headAt jsucc) (C.selectedVar j) 0)
      center)
    {rho0 : ℝ}
    (hsiblingData : Step1AdjacentSiblingData
      ((nsActiveStratificationData (r := r) theta w v).Omega jsucc.1) center rho0
      (step1NSSuccessorLevelFamily
        (nsActiveStratificationData (r := r) theta w v) C jsucc))
    (hsiblingOrder : ∀ c : Fin (step1NSSiblingCount (C.headAt jsucc)),
      ∃ (mu : ℤ) (cc : ℂ), mu ≤ (2 * N.q : Nat) ∧
        LaurentNormalFormAt
          (step1NSSuccessorLevelFamily
            (nsActiveStratificationData (r := r) theta w v) C jsucc c.succ)
          center mu cc)
    {Good : ℂ → Prop} (hdominance : Step1AdjacentDominancePersistence center Good)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ z : ℂ,
      z ∈ puncturedDisc center epsilon ∧
      z ∈ (nsActiveStratificationData (r := r) theta w v).Omega jsucc.1 ∧
      z ≠ 0 ∧
      step1SelectedOnlyCollision
        (nsActiveStratificationData (r := r) theta w v) C jsucc z ∧ Good z := by
  let D := nsActiveStratificationData (r := r) theta w v
  let Psi := nsLevelCoeff (r := r) theta w v jsucc (C.headAt jsucc) (C.selectedVar j) 2
  let Bet := nsLevelCoeff (r := r) theta w v jsucc (C.headAt jsucc) (C.selectedVar j) 1
  let Gam0 := nsLevelCoeff (r := r) theta w v jsucc (C.headAt jsucc) (C.selectedVar j) 0
  have hmodel : Step1SuccessorLevelModel D C j jsucc Psi Bet Gam0
      (logScale r : ℂ) center := by
    apply Filter.Eventually.of_forall
    intro z
    have hquad := nsActiveLevel_quadratic_in_prior_gate (r := r) theta w v jsucc
      (C.headAt jsucc) (C.selectedVar j)
      (formalSlope_blockDegree_two theta w v jsucc (C.headAt jsucc) (C.selectedVar j)) z
    have hgate : step1SelectedGateFunction D C j z =
        nsActiveGate (r := r) theta w v (C.selectedVar j) z := by
      rw [step1SelectedGateFunction_apply,
        nsActiveGate_eq_csig_level theta w v hactiveJ z]
      rfl
    simp only [step1SelectedLevelFunction_apply]
    rw [hgate]
    exact hquad.symm.trans rfl
  have hNF : LaurentNormalFormAt (step1SelectedLevelFunction D C jsucc) center
      (2 * (N.q : ℤ)) (center * (N.coeff * (Psi center * N.coeff))) :=
    step1SuccessorLevelNormalForm_of_model N hcenter_ne hPsi hPsi_ne hBet hGam0 hmodel
  have hm : 1 ≤ 2 * N.q := by
    have hq := N.q_pos
    omega
  have hNFfamily : LaurentNormalFormAt
      (step1NSSuccessorLevelFamily D C jsucc 0) center
      ((2 * N.q : Nat) : ℤ) (center * (N.coeff * (Psi center * N.coeff))) := by
    simpa [D] using hNF
  have hselected_notAnalytic :
      ¬ AnalyticAt ℂ (step1NSSuccessorLevelFamily D C jsucc 0) center := by
    exact hNFfamily.not_analyticAt (by
      have hq := N.q_pos
      norm_num
      omega)
  have hmeromorphic : ∀ c : Fin (step1NSSiblingCount (C.headAt jsucc) + 1),
      MeromorphicAt (step1NSSuccessorLevelFamily D C jsucc c) center := by
    intro c
    refine Fin.cases hNFfamily.meromorphicAt ?_ c
    intro q
    exact hsiblingData.sibling_meromorphic_at_center q
  have hsiblingHyp : KHead.SiblingAvoidanceHypotheses (D.Omega jsucc.1) center rho0
      (step1NSSuccessorLevelFamily D C jsucc) := by
    exact ⟨hsiblingData.omega_domain, hsiblingData.nonneg_subset,
      hsiblingData.center_notMem, hsiblingData.puncturedDisc_subset,
      hsiblingData.radius_pos, hsiblingData.analytic_on_omega, hmeromorphic,
      hsiblingData.common_real_value, hsiblingData.real_valued_on_nonnegative,
      hselected_notAnalytic, hsiblingData.sibling_not_identical⟩
  let A : SelectedArcData (step1NSSuccessorLevelFamily D C jsucc 0) center
      (2 * N.q) (center * (N.coeff * (Psi center * N.coeff))) :=
    Classical.choice (selectedArcData_of_normalForm hm hNFfamily)
  have hresult : KHead.SiblingAvoidanceResult (D.Omega jsucc.1) center rho0
      (step1NSSuccessorLevelFamily D C jsucc) :=
    KHead.siblingAvoidanceResult_of_normalForm hsiblingHyp hm hNFfamily A hsiblingOrder
  have havoid : KHead.SiblingAvoidanceConclusion center
      (step1NSSuccessorLevelFamily D C jsucc) :=
    KHead.lem_sibling_avoidance hresult
  let rho : ℝ := min rho0 (min hdominance.radius epsilon)
  have hrho : 0 < rho :=
    lt_min hsiblingHyp.radius_pos (lt_min hdominance.radius_pos hepsilon)
  have hinf := havoid rho hrho
  rcases hinf.nonempty with ⟨z, hzpunct, hzselected, hzsiblings⟩
  have hzrho0 : z ∈ puncturedDisc center rho0 :=
    ⟨hzpunct.1, lt_of_lt_of_le hzpunct.2 (min_le_left _ _)⟩
  have hzdom : z ∈ puncturedDisc center hdominance.radius :=
    ⟨hzpunct.1, lt_of_lt_of_le hzpunct.2
      (le_trans (min_le_right _ _) (min_le_left _ _))⟩
  have hzepsilon : z ∈ puncturedDisc center epsilon :=
    ⟨hzpunct.1, lt_of_lt_of_le hzpunct.2
      (le_trans (min_le_right _ _) (min_le_right _ _))⟩
  have hzOmega : z ∈ D.Omega jsucc.1 := hsiblingHyp.puncturedDisc_subset hzrho0
  have hz_ne : z ≠ 0 := by
    intro hz
    subst z
    rcases hsiblingData.common_real_value with ⟨b, _hb, hbval⟩
    have hb0 : step1NSSuccessorLevelFamily D C jsucc 0 0 = (b : ℂ) := by
      simpa [D] using hbval 0
    have hzeroPi := hzselected
    rw [hb0] at hzeroPi
    exact ofReal_notMem_Pi b hzeroPi
  refine ⟨z, hzepsilon, hzOmega, hz_ne, ?_, hdominance.holds hzdom⟩
  constructor
  · simpa [D, step1NSSuccessorLevelFamily] using hzselected
  · intro c hc
    rcases step1NSSiblingEnumeration_cover (C.headAt jsucc) c hc with ⟨q, hq⟩
    have havoidq := hzsiblings q
    simpa [D, step1NSSuccessorLevelFamily, hq] using havoidq

/-- **Adjacent processing-fold step.**  This is the NS105 induction step in
state form.  Starting from the current exact gate normal form, it constructs a
new successor selected-only collision through window avoidance, then invokes
NS104 at that new point to install the exact successor gate payload in the next
ready processing slot. -/
theorem step1ProcessingFold_adjacent_nsActive
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w v : Vec d)
    {B₀ B : Step1TierBookkeeping n k d}
    (fold : Step1ProcessingFold H
      (nsActiveStratificationData (r := r) theta' w v) w B₀ B)
    (hInv₀ : Step1TierInvariant H
      (nsActiveStratificationData (r := r) theta' w v) w B₀)
    (h : Fin k) (jcur : Step1TierIndex n) (stage : Step1LaterTierIndex n)
    (_hadj : stage.toTier.1 = jcur.1 + 1)
    (hready : Step1ReadyToProcess B.processed (h, .ignition stage))
    {center : ℂ} (hcenter_ne : center ≠ 0)
    (N : Step1SuccessorPoleNormalForm
      (nsActiveStratificationData (r := r) theta' w v) (B.chain h) jcur center)
    (hPsi : AnalyticAt ℂ
      (nsLevelCoeff (r := r) theta' w v stage.toTier
        ((B.chain h).headAt stage.toTier) ((B.chain h).selectedVar jcur) 2) center)
    (hPsi_ne : nsLevelCoeff (r := r) theta' w v stage.toTier
      ((B.chain h).headAt stage.toTier) ((B.chain h).selectedVar jcur) 2 center ≠ 0)
    (hBet : AnalyticAt ℂ
      (nsLevelCoeff (r := r) theta' w v stage.toTier
        ((B.chain h).headAt stage.toTier) ((B.chain h).selectedVar jcur) 1) center)
    (hGam0 : AnalyticAt ℂ
      (nsLevelCoeff (r := r) theta' w v stage.toTier
        ((B.chain h).headAt stage.toTier) ((B.chain h).selectedVar jcur) 0) center)
    {rho0 : ℝ}
    (hsiblingData : Step1AdjacentSiblingData
      ((nsActiveStratificationData (r := r) theta' w v).Omega stage.toTier.1)
      center rho0
      (step1NSSuccessorLevelFamily
        (nsActiveStratificationData (r := r) theta' w v) (B.chain h) stage.toTier))
    (hsiblingOrder : ∀ c : Fin
      (step1NSSiblingCount ((B.chain h).headAt stage.toTier)),
      ∃ (mu : ℤ) (cc : ℂ), mu ≤ (2 * N.q : Nat) ∧
        LaurentNormalFormAt
          (step1NSSuccessorLevelFamily
            (nsActiveStratificationData (r := r) theta' w v)
            (B.chain h) stage.toTier c.succ) center mu cc)
    {Good : ℂ → Prop} (hdominance : Step1AdjacentDominancePersistence center Good) :
    ∃ (z : ℂ) (P : Step1SelectedPoleRecord n k d),
      P.point = z ∧
      z ≠ 0 ∧
      step1SelectedOnlyCollision
        (nsActiveStratificationData (r := r) theta' w v) (B.chain h) stage.toTier z ∧
      Good z ∧
      Step1ProcessingFold H (nsActiveStratificationData (r := r) theta' w v) w B₀
        (step1ProcessIgnition H w B h stage P) ∧
      Step1TierInvariant H (nsActiveStratificationData (r := r) theta' w v) w
        (step1ProcessIgnition H w B h stage P) := by
  let D := nsActiveStratificationData (r := r) theta' w v
  have hactive : IsActiveVar theta' ((B.chain h).selectedVar jcur) := by
    simpa [IsActiveVar, Step1SelectedChain.selectedVar] using
      step1_head_active H jcur ((B.chain h).headAt jcur)
  rcases step1AdjacentSelectedOnlyPoint_nsActive theta' w v (B.chain h) jcur stage.toTier
      hactive hcenter_ne N hPsi hPsi_ne hBet hGam0 hsiblingData hsiblingOrder hdominance
      (epsilon := 1) (by norm_num) with
    ⟨z, _hzNear, hzOmega, hz_ne, hzcollision, hzGood⟩
  have hInv : Step1TierInvariant H D w B := fold.preserves_invariant hInv₀
  rcases step1_processIgnition_of_selectedLevelPole H D
      (nsActiveHeadSingularStratification (r := r) theta' w v) w hInv h stage hready
      hzOmega hzcollision.selectedLevelPole with ⟨P, hP, hInv'⟩
  have hPpoint : P.point = z := by
    rw [hP]
    rfl
  have hPexact : P.IsExact D := by
    rw [hP]
    exact
      (step1SuccessorPoleNormalForm_of_selectedLevelPole
        (nsActiveHeadSingularStratification (r := r) theta' w v)
        (B.chain h) stage.toTier
        (step1_head_active H stage.toTier ((B.chain h).headAt stage.toTier))
        hzOmega hzcollision.selectedLevelPole).selectedPoleRecord_isExact
          h hzOmega hzcollision.selectedLevelPole
  have hfold' : Step1ProcessingFold H D w B₀ (step1ProcessIgnition H w B h stage P) := by
    apply Step1ProcessingFold.ignition fold hready
    · simp [hP, Step1SuccessorPoleNormalForm.toSelectedPoleRecord]
    · simp [hP, Step1SuccessorPoleNormalForm.toSelectedPoleRecord]
    · simp [hP, Step1SuccessorPoleNormalForm.toSelectedPoleRecord]
    · exact hPexact
  exact ⟨z, P, hPpoint, hz_ne, hzcollision, hzGood, hfold', hInv'⟩

/-! ## Strengthened analytic payload retained by the finite fold -/

/-- Canonical tower dominance makes the concrete successor quadratic
coefficient `Ψ` nonzero.  This is the exact bridge from NS103's formal selected
coefficient to NS106's local noncancellation input. -/
theorem step1CanonicalIgnitionPsi_ne_of_dominance
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w v : Vec d)
    (hsep : (∏ idx : Step1SeparatedFactorIndex n k,
      step1SeparatedFactorValue H w v idx) ≠ 0)
    (h : Fin k) (j : Step1LaterTierIndex n) (z : ℂ)
    (hdom : step1TowerDominance (step1CanonicalIgnitionTower H w v h j)
      (fun y => nsActiveGate (r := r) theta' w v y z)) :
    nsLevelCoeff (r := r) theta' w v j.toTier
      ((step1TargetSelectedChain H h).headAt j.toTier)
      ((step1TargetSelectedChain H h).selectedVar ⟨j.1, by omega⟩) 2 z ≠ 0 := by
  let T := step1CanonicalIgnitionTower H w v h j
  have htop : DominanceTowerTopConstant T := by
    simpa [DominanceTowerTopConstant, CanonicalTowerTopConstant] using
      step1CanonicalIgnitionTower_topConstant H w v h j
  have hfinal : DominanceTowerFinalCoeff T := by
    simpa [DominanceTowerFinalCoeff, CanonicalTowerFinalCoeff] using
      step1CanonicalIgnitionTower_finalCoeff H w v h j
  have hrec : DominanceTowerEvalRecurrence T := by
    simpa [DominanceTowerEvalRecurrence, CanonicalTowerEvalRecurrence] using
      step1CanonicalIgnitionTower_evalRecurrence H w v h j
  have hne := step1TowerDominance_eval_ne_zero
    (step1CanonicalIgnitionTower_degree_pos H w v h j)
    (step1CanonicalIgnitionTower_topConstant_ne_zero H w v
      hsep h j)
    htop hfinal hrec hdom
  exact hne

/-- The analytic facts needed by the next adjacent step and by terminal
blowup, attached to the exact pole stored in an ignition slot. -/
structure Step1ReadyPoleWitness
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w v : Vec d)
    (h : Fin k) (j : Step1LaterTierIndex n)
    (P : Step1SelectedPoleRecord n k d) : Prop where
  head : P.firstHead = h
  chain : P.chain = step1TargetSelectedChain H h
  tier : P.tier = j.toTier
  exact : P.IsExact (nsActiveStratificationData (r := r) theta' w v)
  selectedOnly : step1SelectedOnlyCollision
    (nsActiveStratificationData (r := r) theta' w v)
    (step1TargetSelectedChain H h) j.toTier P.point
  separated : (∏ idx : Step1SeparatedFactorIndex n k,
    step1SeparatedFactorValue H w v idx) ≠ 0
  futureDominance : Step1FiniteFamilyDominance H w v separated
    h (j.1 + 1)
    (fun y => nsActiveGate (r := r) theta' w v y P.point)
  dominance : step1TowerDominance (step1CanonicalIgnitionTower H w v h j)
    (fun y => nsActiveGate (r := r) theta' w v y P.point)
  psi_ne : nsLevelCoeff (r := r) theta' w v j.toTier
    ((step1TargetSelectedChain H h).headAt j.toTier)
    ((step1TargetSelectedChain H h).selectedVar ⟨j.1, by omega⟩) 2 P.point ≠ 0
  finalResidue_ne : j = (Fin.last n : Step1LaterTierIndex n) →
    ∀ i : Step1ResidueCoordinateIndex H w h,
      nsFinalObservableResidueFactor (r := r) theta' w v
        (step1TargetSelectedChain H h) i.1 P.point ≠ 0

/-- The pointwise separated package supplies the single finite product used to
index the canonical dominance family. -/
theorem Step1SeparatedProbePackage.factorProduct_ne_zero
    {theta theta' : Params (n + 2) k d}
    {H : Step1StandingHypotheses r theta theta'}
    (P : Step1SeparatedProbePackage H) :
    (∏ idx : Step1SeparatedFactorIndex n k,
      step1SeparatedFactorValue H P.w P.v idx) ≠ 0 := by
  classical
  exact Finset.prod_ne_zero_iff.mpr fun idx _ =>
    (mem_step1SeparatedSet_iff H P.rho).mp P.mem idx

/-- One genuine adjacent construction, starting from a controlled tier-`j`
pole, builds the ready witness for the later-stage slot whose ambient tier is
`j+1`. -/
theorem step1ProduceReadyPole_from_current_nsActive
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta')
    (P : Step1SeparatedProbePackage H) (hr : 1 < r)
    (h : Fin k) (stage : Step1LaterTierIndex n)
    (jcur : Step1TierIndex n) (hadj : stage.toTier.1 = jcur.1 + 1)
    {center : ℂ} (hcenter_ne : center ≠ 0)
    (hcenterOmega : center ∈
      (nsActiveStratificationData (r := r) theta' P.w P.v).Omega jcur.1)
    (hselectedOnly : step1SelectedOnlyCollision
      (nsActiveStratificationData (r := r) theta' P.w P.v)
      (step1TargetSelectedChain H h) jcur center)
    (N : Step1SuccessorPoleNormalForm
      (nsActiveStratificationData (r := r) theta' P.w P.v)
      (step1TargetSelectedChain H h) jcur center)
    (hfamily : Step1FiniteFamilyDominance H P.w P.v P.factorProduct_ne_zero
      h jcur.1 (fun x => nsActiveGate (r := r) theta' P.w P.v x center))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ R : Step1SelectedPoleRecord n k d,
      R.firstHead = h ∧ R.chain = step1TargetSelectedChain H h ∧
      R.tier = stage.toTier ∧ R.point ∈ puncturedDisc center epsilon ∧
      Step1ReadyPoleWitness H P.w P.v h stage R := by
  let C := step1TargetSelectedChain H h
  let D := nsActiveStratificationData (r := r) theta' P.w P.v
  have hactive : IsActiveVar theta' (C.selectedVar jcur) := by
    simpa [C, IsActiveVar, Step1SelectedChain.selectedVar] using
      step1_head_active H jcur (C.headAt jcur)
  have hstageval : stage.1 = jcur.1 := by simpa using hadj
  have hstageDom : step1TowerDominance
      (step1CanonicalIgnitionTower H P.w P.v h stage)
      (fun x => nsActiveGate (r := r) theta' P.w P.v x center) :=
    hfamily.ignition stage (by omega)
  have hPsiNe : nsLevelCoeff (r := r) theta' P.w P.v stage.toTier
      (C.headAt stage.toTier) (C.selectedVar jcur) 2 center ≠ 0 := by
    have hne := step1CanonicalIgnitionPsi_ne_of_dominance H P.w P.v
      P.factorProduct_ne_zero h stage center hstageDom
    simpa [C, hstageval] using hne
  have hPsi : AnalyticAt ℂ
      (nsLevelCoeff (r := r) theta' P.w P.v stage.toTier
        (C.headAt stage.toTier) (C.selectedVar jcur) 2) center :=
    nsLevelCoeff_analyticAt_of_selectedOnly P.w P.v C jcur stage.toTier hadj
      hcenterOmega hselectedOnly _ 2
  have hBet : AnalyticAt ℂ
      (nsLevelCoeff (r := r) theta' P.w P.v stage.toTier
        (C.headAt stage.toTier) (C.selectedVar jcur) 1) center :=
    nsLevelCoeff_analyticAt_of_selectedOnly P.w P.v C jcur stage.toTier hadj
      hcenterOmega hselectedOnly _ 1
  have hGam : AnalyticAt ℂ
      (nsLevelCoeff (r := r) theta' P.w P.v stage.toTier
        (C.headAt stage.toTier) (C.selectedVar jcur) 0) center :=
    nsLevelCoeff_analyticAt_of_selectedOnly P.w P.v C jcur stage.toTier hadj
      hcenterOmega hselectedOnly _ 0
  have hdomPersist := step1FiniteFamilyDominancePersistence_nsActive
    H P.w P.v P.factorProduct_ne_zero h jcur (by omega) hcenterOmega
      hactive hselectedOnly N hfamily
  rcases exists_step1AdjacentSiblingPackage_nsActive H P hr h jcur stage.toTier
      hadj hcenterOmega hselectedOnly N with ⟨rho, hsibling, hsiblingOrder⟩
  rcases step1AdjacentSelectedOnlyPoint_nsActive theta' P.w P.v C jcur stage.toTier
      hactive hcenter_ne N hPsi hPsiNe hBet hGam hsibling hsiblingOrder hdomPersist
      hepsilon with
    ⟨z, hzNear, hzOmega, hzNe, hzCollision, hzFamily⟩
  have hactiveNext : C.headAt stage.toTier ∈ activeHeads theta' stage.toTier :=
    step1_head_active H stage.toTier _
  let Nnext := step1SuccessorPoleNormalForm_of_selectedLevelPole
    (nsActiveHeadSingularStratification (r := r) theta' P.w P.v)
    C stage.toTier hactiveNext hzOmega hzCollision.selectedLevelPole
  let R := Nnext.toSelectedPoleRecord h
  have hRexact : R.IsExact D := by
    exact Nnext.selectedPoleRecord_isExact h hzOmega hzCollision.selectedLevelPole
  have hzFamilyStage : Step1FiniteFamilyDominance H P.w P.v
      P.factorProduct_ne_zero h (stage.1 + 1)
      (fun x => nsActiveGate (r := r) theta' P.w P.v x z) := by
    simpa [hstageval] using hzFamily
  have hdomNext : step1TowerDominance
      (step1CanonicalIgnitionTower H P.w P.v h stage)
      (fun x => nsActiveGate (r := r) theta' P.w P.v x z) :=
    hzFamilyStage.ignition stage (by omega)
  have hpsiNext := step1CanonicalIgnitionPsi_ne_of_dominance H P.w P.v
    P.factorProduct_ne_zero h stage z hdomNext
  have hterminal : stage = (Fin.last n : Step1LaterTierIndex n) →
      ∀ i : Step1ResidueCoordinateIndex H P.w h,
        nsFinalObservableResidueFactor (r := r) theta' P.w P.v C i.1 z ≠ 0 := by
    intro hlast i
    have hfull : n + 1 ≤ stage.1 + 1 := by
      rw [hlast]
      simp
    have heval := hzFamilyStage.residue_eval_ne_zero i hfull
    simpa [nsFinalObservableResidueFactor, step1CanonicalResiduePoly,
      step1FinalTierIndex, C] using heval
  refine ⟨R, rfl, rfl, rfl, ?_, ?_⟩
  · simpa [R, Nnext, Step1SuccessorPoleNormalForm.toSelectedPoleRecord] using hzNear
  exact
    { head := rfl
      chain := rfl
      tier := rfl
      exact := hRexact
      selectedOnly := hzCollision
      separated := P.factorProduct_ne_zero
      futureDominance := by
        simpa [R, Nnext, Step1SuccessorPoleNormalForm.toSelectedPoleRecord] using
          hzFamilyStage
      dominance := hdomNext
      psi_ne := hpsiNext
      finalResidue_ne := hterminal }

/-- Every pole currently retained by the bookkeeping state carries the full
ready-pole analytic payload, rather than only its Laurent record. -/
def Step1CascadeControlled
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w v : Vec d)
    (B : Step1TierBookkeeping n k d) : Prop :=
  ∀ h j P, B.selectedPole h j.toTier = some P →
    Step1ReadyPoleWitness H w v h j P

theorem step1InitialTierBookkeeping_controlled
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w v : Vec d) :
    Step1CascadeControlled H w v
      (step1InitialTierBookkeeping H
        (nsActiveStratificationData (r := r) theta' w v)) := by
  intro h j P hP
  simp [step1InitialTierBookkeeping] at hP

theorem step1ProcessIgnition_preserves_controlled
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w v : Vec d)
    {B : Step1TierBookkeeping n k d} {h : Fin k}
    {j : Step1LaterTierIndex n} {P : Step1SelectedPoleRecord n k d}
    (hcontrol : Step1CascadeControlled H w v B)
    (hP : Step1ReadyPoleWitness H w v h j P) :
    Step1CascadeControlled H w v (step1ProcessIgnition H w B h j P) := by
  intro h' j' P' hslot
  by_cases hh : h' = h
  · subst h'
    by_cases hj : j' = j
    · subst j'
      simp only [step1ProcessIgnition, Function.update_self] at hslot
      cases hslot
      exact hP
    · have hjtier : j'.toTier ≠ j.toTier := by
        intro heq
        apply hj
        apply Fin.ext
        simpa using congrArg Fin.val heq
      simp [step1ProcessIgnition, Function.update, hjtier] at hslot
      exact hcontrol h j' P' hslot
  · simp [step1ProcessIgnition, Function.update, hh] at hslot
    exact hcontrol h' j' P' hslot

theorem step1ProcessResidue_preserves_controlled
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w v : Vec d)
    {B : Step1TierBookkeeping n k d} {h : Fin k} {i : Fin d}
    (hcontrol : Step1CascadeControlled H w v B) :
    Step1CascadeControlled H w v (step1ProcessResidue H w B h i) := by
  simpa [Step1CascadeControlled, step1ProcessResidue] using hcontrol

/-- **Unconditional ready-pole producer.**  A chosen first affine pole for each
head starts that head's chain.  At later ignition slots, readiness guarantees
that the immediately preceding slot is processed; the controlled invariant
recovers its full pole payload.  The adjacent construction then supplies the
new selected-only pole and all finite-family dominance data. -/
theorem step1ReadyPoleProducer_nsActive
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta')
    (P : Step1SeparatedProbePackage H) (hr : 1 < r)
    (basePole : Fin k → ℂ)
    (hbase : ∀ h, basePole h ∈ affineSigmoidPoleSet (logScale r)
      (matrixBilin (attentionMatrix theta' 0 h) P.w P.v)) :
    ∀ (B : Step1TierBookkeeping n k d),
      Step1ProcessingFold H
        (nsActiveStratificationData (r := r) theta' P.w P.v) P.w
        (step1InitialTierBookkeeping H
          (nsActiveStratificationData (r := r) theta' P.w P.v)) B →
      Step1CascadeControlled H P.w P.v B →
      ∀ (h : Fin k) (stage : Step1LaterTierIndex n),
        Step1ReadyToProcess B.processed (h, .ignition stage) →
        ∃ R : Step1SelectedPoleRecord n k d,
          R.firstHead = h ∧ R.chain = B.chain h ∧ R.tier = stage.toTier ∧
          Step1ReadyPoleWitness H P.w P.v h stage R := by
  classical
  intro B fold control h stage hready
  let D := nsActiveStratificationData (r := r) theta' P.w P.v
  let B0 := step1InitialTierBookkeeping H D
  have hInv0 : Step1TierInvariant H D P.w B0 :=
    step1InitialTierInvariant H D P.w
  have hInv : Step1TierInvariant H D P.w B := fold.preserves_invariant hInv0
  have hchain : B.chain h = step1TargetSelectedChain H h := hInv.1 h
  have hD := nsActiveHeadSingularStratification (r := r) theta' P.w P.v
  by_cases hzero : stage.1 = 0
  · let jcur := step1FirstTierIndex n
    have hadj : stage.toTier.1 = jcur.1 + 1 := by
      simp [hzero, jcur, step1FirstTierIndex]
    let center := basePole h
    have hfirstLevel : ∀ a : Fin k,
        nsActiveLevel (r := r) theta' P.w P.v (0, a) center =
          center * (matrixBilin (attentionMatrix theta' 0 a) P.w P.v : ℂ) +
            (logScale r : ℂ) := by
      intro a
      rw [nsActiveLevel_formula]
      congr 2
      simp [formalSlope, formalBilin, formalW, formalV, formalPoint,
        evalFormalPolyComplex, realVecToFormal, realMatrixToFormal, formalConst,
        matrixBilin, Matrix.mulVec, dotProduct]
    have hpole : step1SelectedLevelPole D
        (step1TargetSelectedChain H h) jcur center := by
      change nsActiveLevel (r := r) theta' P.w P.v (0, h) center ∈ Pi
      rw [hfirstLevel h]
      have harg := (mem_affineSigmoidPoleSet_iff (P.firstSlope_ne_zero h) center).1
        (hbase h)
      simpa [mul_comm] using harg
    have hcollision : step1SelectedOnlyCollision D
        (step1TargetSelectedChain H h) jcur center := by
      refine ⟨hpole, ?_⟩
      intro c hc
      change nsActiveLevel (r := r) theta' P.w P.v (0, c) center ∉ Pi
      rw [hfirstLevel c]
      intro hcPi
      let qh := matrixBilin (attentionMatrix theta' 0 h) P.w P.v
      let qc := matrixBilin (attentionMatrix theta' 0 c) P.w P.v
      have hqc : qc ≠ 0 := P.firstSlope_ne_zero c
      have hcenterC : center ∈ affineSigmoidPoleSet (logScale r) qc :=
        (mem_affineSigmoidPoleSet_iff hqc center).2 (by
          simpa [qc, mul_comm] using hcPi)
      have hch : c ≠ h := by simpa using hc
      have hqhqc : qh ≠ qc := fun heq =>
        hch (P.firstSlope_injective (by simpa [qh, qc] using heq)).symm
      have hinter : affineSigmoidPoleSet (logScale r) qh ∩
          affineSigmoidPoleSet (logScale r) qc = ∅ :=
        affineSigmoidPoleSet_inter_eq_empty_of_ne
          (ne_of_gt (Real.log_pos (by exact_mod_cast hr)))
          (P.firstSlope_ne_zero h) hqc hqhqc
      have : center ∈ (∅ : Set ℂ) := by
        rw [← hinter]
        exact ⟨hbase h, hcenterC⟩
      exact this
    have hOmega : center ∈ D.Omega jcur.1 := by
      change center ∈ D.Omega 0
      rw [hD.omega_zero]
      exact Set.mem_univ center
    have hactive : (step1TargetSelectedChain H h).headAt jcur ∈
        activeHeads theta' jcur := step1_head_active H jcur _
    let N := step1SuccessorPoleNormalForm_of_selectedLevelPole hD
      (step1TargetSelectedChain H h) jcur hactive hOmega hpole
    have hcenterNe : center ≠ 0 := by
      intro heq
      have hhits := hcollision.1
      rw [heq] at hhits
      change nsActiveLevel (r := r) theta' P.w P.v
        ((step1TargetSelectedChain H h).selectedVar jcur) 0 ∈ Pi at hhits
      rw [nsActiveLevel_zero] at hhits
      exact ofReal_notMem_Pi (logScale r) hhits
    have hfamily : Step1FiniteFamilyDominance H P.w P.v
        P.factorProduct_ne_zero h jcur.1
        (fun x => nsActiveGate (r := r) theta' P.w P.v x center) := by
      simpa [jcur] using step1FiniteFamilyDominance_zero H P.w P.v
        P.factorProduct_ne_zero h
        (fun x => nsActiveGate (r := r) theta' P.w P.v x center)
    rcases step1ProduceReadyPole_from_current_nsActive H P hr h stage jcur hadj
        hcenterNe hOmega hcollision N hfamily (epsilon := 1) (by norm_num) with
      ⟨R, hhead, hRchain, htier, _hnear, hR⟩
    exact ⟨R, hhead, hRchain.trans hchain.symm, htier, hR⟩
  · have hstagePos : 0 < stage.1 := Nat.pos_of_ne_zero hzero
    let pred : Step1LaterTierIndex n := ⟨stage.1 - 1, by omega⟩
    let jcur : Step1TierIndex n := ⟨stage.1, by omega⟩
    have hpredToTier : pred.toTier = jcur := by
      apply Fin.ext
      simp [pred, jcur]
      omega
    have hadj : stage.toTier.1 = jcur.1 + 1 := by rfl
    have hpredlt : pred.1 < stage.1 := by
      change stage.1 - 1 < stage.1
      exact Nat.sub_lt hstagePos Nat.zero_lt_one
    have hbefore : Step1ProcessedBefore
        (h, (Step1ProcessSlot.ignition pred : Step1ProcessSlot n d))
        (h, (Step1ProcessSlot.ignition stage : Step1ProcessSlot n d)) := by
      unfold Step1ProcessedBefore step1ProcessingRank
      change h.1 * (n + 1 + d) + pred.1 <
        h.1 * (n + 1 + d) + stage.1
      exact Nat.add_lt_add_left hpredlt _
    have hpredProcessed := hready.2
      (h, (Step1ProcessSlot.ignition pred : Step1ProcessSlot n d)) hbefore
    rcases (hInv.2.2.2.2.2 h (.ignition pred)).1 hpredProcessed with
      ⟨_ignition, Q, hQslot⟩
    have hQ := control h pred Q hQslot
    have hOmega : Q.point ∈ D.Omega jcur.1 := by
      simpa [hQ.tier, hpredToTier] using hQ.exact.1
    have hcollision : step1SelectedOnlyCollision D
        (step1TargetSelectedChain H h) jcur Q.point := by
      simpa [hpredToTier] using hQ.selectedOnly
    have hactive : (step1TargetSelectedChain H h).headAt jcur ∈
        activeHeads theta' jcur := step1_head_active H jcur _
    let N := step1SuccessorPoleNormalForm_of_selectedLevelPole hD
      (step1TargetSelectedChain H h) jcur hactive hOmega
      hcollision.selectedLevelPole
    have hcenterNe : Q.point ≠ 0 := by
      intro heq
      have hhits := hcollision.1
      rw [heq] at hhits
      change nsActiveLevel (r := r) theta' P.w P.v
        ((step1TargetSelectedChain H h).selectedVar jcur) 0 ∈ Pi at hhits
      rw [nsActiveLevel_zero] at hhits
      exact ofReal_notMem_Pi (logScale r) hhits
    have hfamily : Step1FiniteFamilyDominance H P.w P.v
        P.factorProduct_ne_zero h jcur.1
        (fun x => nsActiveGate (r := r) theta' P.w P.v x Q.point) := by
      have hpredsucc : stage.1 - 1 + 1 = stage.1 := by omega
      simpa [pred, jcur, hpredsucc] using hQ.futureDominance
    rcases step1ProduceReadyPole_from_current_nsActive H P hr h stage jcur hadj
        hcenterNe hOmega hcollision N hfamily (epsilon := 1) (by norm_num) with
      ⟨R, hhead, hRchain, htier, _hnear, hR⟩
    exact ⟨R, hhead, hRchain.trans hchain.symm, htier, hR⟩

/-- Finite NS105 fold with the strengthened ready-pole payload threaded through
every ignition update. -/
theorem step1_exists_complete_controlledFold_of_readyPoleProducer
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w v : Vec d)
    (produce : ∀ (B : Step1TierBookkeeping n k d),
      Step1ProcessingFold H (nsActiveStratificationData (r := r) theta' w v) w
        (step1InitialTierBookkeeping H
          (nsActiveStratificationData (r := r) theta' w v)) B →
      Step1CascadeControlled H w v B →
      ∀ (h : Fin k) (j : Step1LaterTierIndex n),
        Step1ReadyToProcess B.processed (h, .ignition j) →
        ∃ P : Step1SelectedPoleRecord n k d,
          P.firstHead = h ∧ P.chain = B.chain h ∧ P.tier = j.toTier ∧
          Step1ReadyPoleWitness H w v h j P) :
    ∃ B : Step1TierBookkeeping n k d,
      Step1ProcessingFold H (nsActiveStratificationData (r := r) theta' w v) w
        (step1InitialTierBookkeeping H
          (nsActiveStratificationData (r := r) theta' w v)) B ∧
      Step1ProcessingComplete B ∧ Step1CascadeControlled H w v B := by
  classical
  let D := nsActiveStratificationData (r := r) theta' w v
  let B₀ := step1InitialTierBookkeeping H D
  let rec go (B : Step1TierBookkeeping n k d)
      (fold : Step1ProcessingFold H D w B₀ B)
      (control : Step1CascadeControlled H w v B) :
      ∃ B' : Step1TierBookkeeping n k d,
        Step1ProcessingFold H D w B₀ B' ∧ Step1ProcessingComplete B' ∧
          Step1CascadeControlled H w v B' := by
    by_cases hcomplete : B.processed = Finset.univ
    · exact ⟨B, fold, hcomplete, control⟩
    · rcases step1_exists_ready_of_ne_univ B.processed hcomplete with
        ⟨⟨h, slot⟩, hready⟩
      cases slot with
      | ignition j =>
          rcases produce B fold control h j hready with
            ⟨P, hhead, hchain, htier, hP⟩
          exact go (step1ProcessIgnition H w B h j P)
            (.ignition fold hready hhead hchain htier hP.exact)
            (step1ProcessIgnition_preserves_controlled H w v control hP)
      | residue i =>
          exact go (step1ProcessResidue H w B h i) (.residue fold hready)
            (step1ProcessResidue_preserves_controlled H w v control)
    termination_by (Finset.univ \ B.processed).card
    decreasing_by
      all_goals
        simp only [step1ProcessIgnition, step1ProcessResidue]
        have hnot := hready.1
        simp only [Finset.sdiff_insert]
        apply Finset.card_erase_lt_of_mem
        simp [hnot]
  exact go B₀ (.refl B₀) (step1InitialTierBookkeeping_controlled H w v)

/-! ## Base ignition — a first-layer affine pole starts the selected cascade -/

/-- At layer zero the no-skip formal slope is independent of every gate
assignment and is exactly the first probe bilinear slope. -/
theorem evalFormalPolyComplex_formalSlope_first_ns
    {L k d : Nat} (theta : Params L k d) (w v : Vec d)
    (hL : 0 < L) (a : Fin k) (eta : FormalVar L k → ℂ) :
    evalFormalPolyComplex eta (formalSlope theta w v ⟨0, hL⟩ a) =
      (matrixBilin (attentionMatrix theta ⟨0, hL⟩ a) w v : ℂ) := by
  simp [formalSlope, formalBilin, formalW, formalV, formalPoint,
    evalFormalPolyComplex, realVecToFormal, realMatrixToFormal, formalConst,
    matrixBilin, Matrix.mulVec, dotProduct]

/-- The concrete recursively constructed first level is the affine first-layer
level used to define the initial active stratum and pole progressions. -/
theorem nsActiveLevel_first
    (theta : Params (n + 2) k d) (w v : Vec d) (a : Fin k) (z : ℂ) :
    nsActiveLevel (r := r) theta w v (0, a) z =
      initialActiveLevel (r := r) theta w v (by omega) a z := by
  rw [nsActiveLevel_formula]
  change z * evalFormalPolyComplex (fun y => nsActiveGate (r := r) theta w v y z)
      (formalSlope theta w v ⟨0, by omega⟩ a) + (logScale r : ℂ) = _
  rw [evalFormalPolyComplex_formalSlope_first_ns theta w v (by omega) a]
  rfl

/-- A selected first-head hit of the initial affine pole set is exactly the
base selected-level pole needed by the tier cascade. -/
theorem step1FirstSelectedLevelPole_of_initialHit
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w v : Vec d)
    (h : Fin k) {tau : ℂ}
    (hpole : initialActiveLevel (r := r) theta' w v (by omega) h tau ∈ Pi) :
    step1SelectedLevelPole
      (nsActiveStratificationData (r := r) theta' w v)
      (step1TargetSelectedChain H h) (step1FirstTierIndex n) tau := by
  change nsActiveLevel (r := r) theta' w v
    ((step1TargetSelectedChain H h).selectedVar (step1FirstTierIndex n)) tau ∈ Pi
  simp only [Step1SelectedChain.selectedVar, Step1SelectedChain.headAt_first,
    step1TargetSelectedChain_firstHead]
  change nsActiveLevel (r := r) theta' w v (0, h) tau ∈ Pi
  rw [nsActiveLevel_first]
  exact hpole

/-- **Base ignition from a first-layer selected sigmoid pole.**  Membership in
the selected affine pole progression supplies the initial selected-level pole,
with the nonzero slope furnished by the separated-probe package. -/
theorem step1FirstSelectedLevelPole_nsActive
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta')
    (P : Step1SeparatedProbePackage H) (h : Fin k) {tau : ℂ}
    (hpole : tau ∈ affineSigmoidPoleSet (logScale r)
      (matrixBilin (attentionMatrix theta' 0 h) P.w P.v)) :
    step1SelectedLevelPole
      (nsActiveStratificationData (r := r) theta' P.w P.v)
      (step1TargetSelectedChain H h) (step1FirstTierIndex n) tau := by
  apply step1FirstSelectedLevelPole_of_initialHit H P.w P.v h
  have harg := (mem_affineSigmoidPoleSet_iff (P.firstSlope_ne_zero h) tau).1 hpole
  simpa [initialActiveLevel, mul_comm] using harg

/-- At a separated probe (and the intended nontrivial sequence length), a
selected first-head pole is a selected-only collision: distinct first slopes
have disjoint affine pole progressions, so no sibling head hits `Pi` there. -/
theorem step1FirstSelectedOnlyCollision_nsActive
    {theta theta' : Params (n + 2) k d} (hr : 1 < r)
    (H : Step1StandingHypotheses r theta theta')
    (P : Step1SeparatedProbePackage H) (h : Fin k) {tau : ℂ}
    (hpole : tau ∈ affineSigmoidPoleSet (logScale r)
      (matrixBilin (attentionMatrix theta' 0 h) P.w P.v)) :
    step1SelectedOnlyCollision
      (nsActiveStratificationData (r := r) theta' P.w P.v)
      (step1TargetSelectedChain H h) (step1FirstTierIndex n) tau := by
  refine ⟨step1FirstSelectedLevelPole_nsActive H P h hpole, ?_⟩
  intro c hc
  change nsActiveLevel (r := r) theta' P.w P.v
      ((step1FirstTierIndex n), c) tau ∉ Pi
  change nsActiveLevel (r := r) theta' P.w P.v (0, c) tau ∉ Pi
  rw [nsActiveLevel_first]
  intro hcPi
  let qh := matrixBilin (attentionMatrix theta' 0 h) P.w P.v
  let qc := matrixBilin (attentionMatrix theta' 0 c) P.w P.v
  have hqc : qc ≠ 0 := P.firstSlope_ne_zero c
  have htauc : tau ∈ affineSigmoidPoleSet (logScale r) qc :=
    (mem_affineSigmoidPoleSet_iff hqc tau).2 (by
      simpa [initialActiveLevel, qc, mul_comm] using hcPi)
  have hch : c ≠ h := by simpa using hc
  have hqhqc : qh ≠ qc := fun heq =>
    hch (P.firstSlope_injective (by simpa [qh, qc] using heq)).symm
  have hinter :
      affineSigmoidPoleSet (logScale r) qh ∩
          affineSigmoidPoleSet (logScale r) qc = ∅ :=
    affineSigmoidPoleSet_inter_eq_empty_of_ne
      (ne_of_gt (Real.log_pos (by exact_mod_cast hr)))
      (P.firstSlope_ne_zero h) hqc hqhqc
  have : tau ∈ (∅ : Set ℂ) := by
    rw [← hinter]
    exact ⟨hpole, htauc⟩
  exact this

/-- Base-pole normal-form package.  The initial selected pole lies in the
concrete layer-zero domain, the selected head is active, and the existing
active-level/PoleArcs API therefore supplies its exact sigmoid pole and arc. -/
theorem step1FirstSelectedSigmoidNormalForms_nsActive
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta')
    (P : Step1SeparatedProbePackage H) (h : Fin k) {tau : ℂ}
    (hpole : tau ∈ affineSigmoidPoleSet (logScale r)
      (matrixBilin (attentionMatrix theta' 0 h) P.w P.v)) :
    ∃ kappa : Nat, ∃ c : ℂ, 1 ≤ kappa ∧ c ≠ 0 ∧
      LaurentNormalFormAt
        (fun z => step1SelectedLevelFunction
            (nsActiveStratificationData (r := r) theta' P.w P.v)
            (step1TargetSelectedChain H h) (step1FirstTierIndex n) z -
          step1SelectedLevelFunction
            (nsActiveStratificationData (r := r) theta' P.w P.v)
            (step1TargetSelectedChain H h) (step1FirstTierIndex n) tau)
        tau (-(kappa : ℤ)) c ∧
      LaurentNormalFormAt
        (step1SelectedGateFunction
          (nsActiveStratificationData (r := r) theta' P.w P.v)
          (step1TargetSelectedChain H h) (step1FirstTierIndex n))
        tau (kappa : ℤ) c⁻¹ := by
  let D := nsActiveStratificationData (r := r) theta' P.w P.v
  let C := step1TargetSelectedChain H h
  have hD : ActiveHeadSingularStratification (r := r) theta' D :=
    nsActiveHeadSingularStratification (r := r) theta' P.w P.v
  have hactive : C.headAt (step1FirstTierIndex n) ∈
      activeHeads theta' (step1FirstTierIndex n) :=
    step1_head_active H (step1FirstTierIndex n) _
  have hOmega : tau ∈ D.Omega (step1FirstTierIndex n).1 := by
    change tau ∈ D.Omega 0
    rw [hD.omega_zero]
    exact Set.mem_univ tau
  have hlevelPole : D.level ((step1FirstTierIndex n),
      C.headAt (step1FirstTierIndex n)) tau ∈ Pi :=
    step1FirstSelectedLevelPole_nsActive H P h hpole
  rcases activeLevel_sigmoid_normalForms_at_pole hD
      (step1FirstTierIndex n) (C.headAt (step1FirstTierIndex n))
      hactive hOmega hlevelPole with
    ⟨kappa, c, hkappa, hc, hlevel, hgate⟩
  exact ⟨kappa, c, hkappa, hc, hlevel, hgate⟩

/-! ## Task A — discharging the successor level model at the concrete data

For the concrete recursively-constructed data `D := nsActiveStratificationData θ w v`
the standing `Step1SuccessorLevelModel` (kept opaque in NS106) becomes a theorem:
the selected level at the successor tier is *literally* the quadratic-in-prior-gate
shape, with the analytic coefficients `nsLevelCoeff … 2 / 1 / 0` and bias `log r`.
The gate-degree bound `degreeOf x0 (formalSlope …) ≤ 2` is discharged internally by
`formalSlope_blockDegree_two` (NS100), so this is unconditional apart from the selected
head being active. -/

/-- At the concrete data the selected gate function is exactly the constructed
active gate at the selected variable (needs the selected head active). -/
theorem step1SelectedGateFunction_nsActive
    (θ : Params (n + 2) k d) (w v : Vec d) (C : Step1SelectedChain n k)
    (j : Step1TierIndex n) (hactive : IsActiveVar θ (C.selectedVar j)) (z : ℂ) :
    step1SelectedGateFunction (nsActiveStratificationData (r := r) θ w v) C j z
      = nsActiveGate (r := r) θ w v (C.selectedVar j) z := by
  rw [step1SelectedGateFunction_apply, nsActiveGate_eq_csig_level θ w v hactive z]
  rfl

/-- **Task A — `Step1SuccessorLevelModel` discharged at the concrete data.**  For
`D = nsActiveStratificationData θ w v`, the successor-tier selected level equals
the quadratic-in-prior-gate model with `Ψ = nsLevelCoeff … 2`, `Β = nsLevelCoeff … 1`,
`Γ₀ = nsLevelCoeff … 0`, `L₀ = log r`.  The only standing input is the gate-degree
bound of the successor slope in the prior gate variable. -/
theorem step1SuccessorLevelModel_nsActive
    (θ : Params (n + 2) k d) (w v : Vec d) (C : Step1SelectedChain n k)
    (j jsucc : Step1TierIndex n)
    (hactive : IsActiveVar θ (C.selectedVar j)) (τ : ℂ) :
    Step1SuccessorLevelModel (nsActiveStratificationData (r := r) θ w v) C j jsucc
      (nsLevelCoeff (r := r) θ w v jsucc (C.headAt jsucc) (C.selectedVar j) 2)
      (nsLevelCoeff (r := r) θ w v jsucc (C.headAt jsucc) (C.selectedVar j) 1)
      (nsLevelCoeff (r := r) θ w v jsucc (C.headAt jsucc) (C.selectedVar j) 0)
      (logScale r : ℂ) τ := by
  apply Filter.Eventually.of_forall
  intro z
  have hquad := nsActiveLevel_quadratic_in_prior_gate (r := r) θ w v jsucc
    (C.headAt jsucc) (C.selectedVar j)
    (formalSlope_blockDegree_two θ w v jsucc (C.headAt jsucc) (C.selectedVar j)) z
  simp only [step1SelectedLevelFunction_apply,
    step1SelectedGateFunction_nsActive θ w v C j hactive z]
  exact hquad.symm.trans rfl

/-! ## Task B — local gate-to-level adapter at the concrete data

With the successor level model discharged (Task A), the NS104 successor *gate*
normal form propagates — via NS106's `step1_successorSelectedLevelIsPole_of_model`
— into a genuine successor *level* pole at the concrete data.  This is exactly the
local algebraic adapter: given a gate pole normal form at tier `j`, any modeled
tier `jsucc` whose recursive domain still contains the same center acquires a
selected-level pole (meromorphic, not analytic) at `τ`.

The analytic coefficient inputs (`Ψ,Β,Γ₀` analytic at `τ`) are supplied for free by
`nsLevelCoeff_analyticOnNhd` on the recursive domain, and the gate-degree bound is
discharged by `formalSlope_blockDegree_two`; only the local-noncancellation
`Ψ(τ) ≠ 0` and `τ ≠ 0` stay genericity inputs (exactly as NS106 leaves them). -/

/-- **Task B — concrete tier transition.**  From the NS104 gate pole normal form
`N` at tier `j` of the concrete data, a tier `jsucc` containing the same center
has a selected *level* pole at `τ`.  The successor level model is discharged by
Task A; only the local inputs (`τ ≠ 0`, `Ψ(τ) ≠ 0`) remain.

For the genuine adjacent tier, the same center is removed from the next domain;
`step1SelectedLevelPole_not_mem_nextOmega_nsActive` below records that obstruction.
The actual cascade must choose new nearby collision points from the pole arc. -/
theorem step1SuccessorSelectedLevelIsPole_nsActive
    (θ : Params (n + 2) k d) (w v : Vec d) (C : Step1SelectedChain n k)
    (j jsucc : Step1TierIndex n) {τ : ℂ}
    (hactiveJ : IsActiveVar θ (C.selectedVar j))
    (hτΩsucc : τ ∈ (nsActiveStratificationData (r := r) θ w v).Omega jsucc.1)
    (hτ_ne : τ ≠ 0)
    (hPsiτ :
      nsLevelCoeff (r := r) θ w v jsucc (C.headAt jsucc) (C.selectedVar j) 2 τ ≠ 0)
    (N : Step1SuccessorPoleNormalForm (nsActiveStratificationData (r := r) θ w v)
      C j τ) :
    step1SelectedLevelIsPole (nsActiveStratificationData (r := r) θ w v) C jsucc τ := by
  have hPsi := (nsLevelCoeff_analyticOnNhd (r := r) θ w v jsucc (C.headAt jsucc)
    (C.selectedVar j) 2) τ hτΩsucc
  have hBet := (nsLevelCoeff_analyticOnNhd (r := r) θ w v jsucc (C.headAt jsucc)
    (C.selectedVar j) 1) τ hτΩsucc
  have hGam0 := (nsLevelCoeff_analyticOnNhd (r := r) θ w v jsucc (C.headAt jsucc)
    (C.selectedVar j) 0) τ hτΩsucc
  have hmodel :=
    step1SuccessorLevelModel_nsActive (r := r) θ w v C j jsucc hactiveJ τ
  exact step1_successorSelectedLevelIsPole_of_model N hτ_ne hPsi hPsiτ hBet hGam0 hmodel

/-- A selected collision center is removed from the next recursive domain.
Consequently the adjacent-tier cascade cannot reuse the same `tau`; it must use
the PoleArcs/SiblingAvoidance construction to select nearby successor points. -/
theorem step1SelectedLevelPole_not_mem_nextOmega_nsActive
    (theta : Params (n + 2) k d) (w v : Vec d) (C : Step1SelectedChain n k)
    (j : Step1TierIndex n) {tau : ℂ}
    (hactive : C.headAt j ∈ activeHeads theta j)
    (hTauOmega : tau ∈
      (nsActiveStratificationData (r := r) theta w v).Omega j.1)
    (hpole : step1SelectedLevelPole
      (nsActiveStratificationData (r := r) theta w v) C j tau) :
    tau ∉ (nsActiveStratificationData (r := r) theta w v).Omega (j.1 + 1) := by
  let D := nsActiveStratificationData (r := r) theta w v
  have hD : ActiveHeadSingularStratification (r := r) theta D :=
    nsActiveHeadSingularStratification (r := r) theta w v
  have hstratum : tau ∈ D.stratum j.1 := by
    rw [hD.stratum_eq j]
    exact ⟨C.headAt j, hactive, hTauOmega, hpole⟩
  intro hnext
  rw [hD.omega_succ j] at hnext
  exact hnext.2 hstratum

/-! ## Task C — no-skip singular-cascade closure at the concrete data

The final endpoint (`tra:cascade`, item (ii)).  At the innermost selected pole of
the final tier of the concrete data, the tier-ignition machinery (NS104) produces
the successor gate normal form, which NS107's residue-driven blowup turns into a
non-removable singularity of the observable coordinate: `‖e_ι^⊤ F̂‖ → ∞` on a
punctured neighbourhood of `τ`.  The transferred first-layer pole is therefore
genuinely visible in the output and cannot cancel.

The active-head hypothesis is discharged from target regularity; the concrete
`ActiveHeadSingularStratification` witness is the capstone
`nsActiveHeadSingularStratification`.  NS107's exact last-layer formal-stream
split discharges `Step1FinalObservableModel`, so no transfer/model hypothesis
remains in the concrete endpoint. -/

/-- **Task C — no-skip cascade closure.**  At a selected level pole `τ` (in the
recursive domain) of the final tier of the concrete data, the observable
coordinate at a nonzero residue coordinate `i` blows up: the innermost selected
singular set is non-removable at the transferred pole.  Assembles NS104 tier
ignition and NS107 residue-driven blowup at `D = nsActiveStratificationData θ' w v`.

Standing inputs: the selected level pole `hpole` (the transferred pole) and the
boundedness/limit facts for NS107's explicit remainder and residue factor. -/
theorem step1CascadeClosure_nsActive
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta')
    (w v : Vec d) (h : Fin k) (i : Step1ResidueCoordinateIndex H w h) {τ : ℂ}
    (hτΩ : τ ∈ (nsActiveStratificationData (r := r) theta' w v).Omega
      (step1FinalTierIndex n).1)
    (hpole : step1SelectedLevelPole (nsActiveStratificationData (r := r) theta' w v)
      (step1TargetSelectedChain H h) (step1FinalTierIndex n) τ)
    (hB : PuncturedBoundedAt
      (nsFinalObservableRemainder (r := r) theta' w v
        (step1TargetSelectedChain H h) i.1) τ)
    (hG : Tendsto
      (nsFinalObservableResidueFactor (r := r) theta' w v
        (step1TargetSelectedChain H h) i.1)
      (nhdsWithin τ ({τ}ᶜ : Set ℂ))
      (nhds ((step1ResidueTopConstant H w h i : ℝ) : ℂ))) :
    BlowsUpAt
      (fun z => (nsActiveStratificationData (r := r) theta' w v).observable z i.1) τ := by
  have hD : ActiveHeadSingularStratification (r := r) theta'
      (nsActiveStratificationData (r := r) theta' w v) :=
    nsActiveHeadSingularStratification (r := r) theta' w v
  have hactive :
      (step1TargetSelectedChain H h).headAt (step1FinalTierIndex n)
        ∈ activeHeads theta' (step1FinalTierIndex n) :=
    step1_head_active H (step1FinalTierIndex n) _
  have N : Step1SuccessorPoleNormalForm (nsActiveStratificationData (r := r) theta' w v)
      (step1TargetSelectedChain H h) (step1FinalTierIndex n) τ :=
    step1SuccessorPoleNormalForm_of_selectedLevelPole hD
      (step1TargetSelectedChain H h) (step1FinalTierIndex n) hactive hτΩ hpole
  exact step1FinalResidueCoord_blowup_nsActive_of_analyticData H w v h i N hB hG

/-- Terminal closure using the strengthened fold payload: selected-only
avoidance and evaluated residue noncancellation are read directly from the
retained final ready-pole witness. -/
theorem step1CascadeClosure_nsActive_of_readyPole
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta')
    (w v : Vec d) (h : Fin k) (i : Step1ResidueCoordinateIndex H w h)
    (P : Step1SelectedPoleRecord n k d)
    (hP : Step1ReadyPoleWitness H w v h (Fin.last n) P) :
    BlowsUpAt
      (fun z => (nsActiveStratificationData (r := r) theta' w v).observable z i.1)
      P.point := by
  have hjlast : Step1LaterTierIndex.toTier
      (Fin.last n : Step1LaterTierIndex n) =
      step1FinalTierIndex n := by
    apply Fin.ext
    simp [Step1LaterTierIndex.toTier, laterLayer, step1FinalTierIndex]
  have hOmega : P.point ∈
      (nsActiveStratificationData (r := r) theta' w v).Omega
        (step1FinalTierIndex n).1 := by
    simpa [hP.tier, hjlast] using hP.exact.1
  have hactive :
      (step1TargetSelectedChain H h).headAt (step1FinalTierIndex n) ∈
        activeHeads theta' (step1FinalTierIndex n) :=
    step1_head_active H (step1FinalTierIndex n) _
  have hpole : step1SelectedLevelPole
      (nsActiveStratificationData (r := r) theta' w v)
      (step1TargetSelectedChain H h) (step1FinalTierIndex n) P.point := by
    simpa [hjlast] using hP.selectedOnly.selectedLevelPole
  let N := step1SuccessorPoleNormalForm_of_selectedLevelPole
    (nsActiveHeadSingularStratification (r := r) theta' w v)
    (step1TargetSelectedChain H h) (step1FinalTierIndex n) hactive hOmega hpole
  have hsiblings : ∀ a : Fin k,
      a ≠ (step1TargetSelectedChain H h).headAt (step1FinalTierIndex n) →
      IsActiveVar theta' (step1FinalTierIndex n, a) →
        nsActiveLevel (r := r) theta' w v (step1FinalTierIndex n, a) P.point ∉ Pi := by
    intro a ha _
    have hs := hP.selectedOnly.2 a (by simpa [hjlast] using ha)
    simpa [hjlast] using hs
  exact step1FinalResidueCoord_blowup_nsActive H w v h i N hOmega hsiblings
    (hP.finalResidue_ne rfl i)

/-! ## Completed-fold extraction -/

/-- The last later-tier index embeds as the final complete tier. -/
theorem step1LastLaterTier_toTier {n : Nat} :
    Step1LaterTierIndex.toTier (Fin.last n : Step1LaterTierIndex n) =
      step1FinalTierIndex n := by
  apply Fin.ext
  simp [Step1LaterTierIndex.toTier, laterLayer, step1FinalTierIndex]

/-- **Fold-to-observable integration.**  A completed strengthened NS105 fold
contains an exact final selected-pole record.  NS107's concrete observable
split then turns that record into terminal observable blowup, without a
`Step1FinalObservableModel` or other transfer premise.

The two quantified side conditions are precisely the concrete boundedness and
residue-factor limit facts for the pole retained by the fold; unlike the old
model premise, they mention the explicit no-skip functions. -/
theorem step1CascadeClosure_of_completeFold_nsActive
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta')
    (w v : Vec d) (h : Fin k) (i : Step1ResidueCoordinateIndex H w h)
    (B : Step1TierBookkeeping n k d)
    (hInv : Step1TierInvariant H
      (nsActiveStratificationData (r := r) theta' w v) w B)
    (hcomplete : Step1ProcessingComplete B)
    (hB : ∀ P : Step1SelectedPoleRecord n k d,
      B.selectedPole h (step1FinalTierIndex n) = some P →
      PuncturedBoundedAt
        (nsFinalObservableRemainder (r := r) theta' w v
          (step1TargetSelectedChain H h) i.1) P.point)
    (hG : ∀ P : Step1SelectedPoleRecord n k d,
      B.selectedPole h (step1FinalTierIndex n) = some P →
      Tendsto
        (nsFinalObservableResidueFactor (r := r) theta' w v
          (step1TargetSelectedChain H h) i.1)
        (nhdsWithin P.point ({P.point}ᶜ : Set ℂ))
        (nhds ((step1ResidueTopConstant H w h i : ℝ) : ℂ))) :
    ∃ tau : ℂ,
      tau ∈ (nsActiveStratificationData (r := r) theta' w v).Omega
        (step1FinalTierIndex n).1 ∧
      step1SelectedLevelPole
        (nsActiveStratificationData (r := r) theta' w v)
        (step1TargetSelectedChain H h) (step1FinalTierIndex n) tau ∧
      BlowsUpAt
        (fun z => (nsActiveStratificationData (r := r) theta' w v).observable z i.1)
        tau := by
  let jlast : Step1LaterTierIndex n := Fin.last n
  rcases step1_complete_ignition_payload hInv hcomplete h jlast with
    ⟨_ignition, P, hP, hPhead, hPchain, hPtier, hPexact⟩
  have hjlast : jlast.toTier = step1FinalTierIndex n := by
    simpa [jlast] using step1LastLaterTier_toTier (n := n)
  have hPfin : B.selectedPole h (step1FinalTierIndex n) = some P := by
    simpa [hjlast] using hP
  have hchain : P.chain = step1TargetSelectedChain H h := by
    calc
      P.chain = B.chain h := hPchain
      _ = step1TargetSelectedChain H h := hInv.1 h
  have htier : P.tier = step1FinalTierIndex n := hPtier.trans hjlast
  have hOmega : P.point ∈
      (nsActiveStratificationData (r := r) theta' w v).Omega
        (step1FinalTierIndex n).1 := by
    simpa [htier] using hPexact.1
  have hpole : step1SelectedLevelPole
      (nsActiveStratificationData (r := r) theta' w v)
      (step1TargetSelectedChain H h) (step1FinalTierIndex n) P.point := by
    change (nsActiveStratificationData (r := r) theta' w v).level
      ((step1TargetSelectedChain H h).selectedVar (step1FinalTierIndex n)) P.point ∈ Pi
    simpa [hchain, htier] using hPexact.2.1
  refine ⟨P.point, hOmega, hpole, ?_⟩
  exact step1CascadeClosure_nsActive H w v h i hOmega hpole
    (hB P hPfin) (hG P hPfin)

/-- **NS105/NS108 controlled-fold capstone.**  A completed fold carrying the
ready-pole invariant yields a genuine final selected-only pole and observable
blowup with every terminal analytic side condition discharged from that
payload. -/
theorem step1CascadeClosure_of_completeControlledFold_nsActive
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta')
    (w v : Vec d) (h : Fin k) (i : Step1ResidueCoordinateIndex H w h)
    (B : Step1TierBookkeeping n k d)
    (hInv : Step1TierInvariant H
      (nsActiveStratificationData (r := r) theta' w v) w B)
    (hcomplete : Step1ProcessingComplete B)
    (hcontrol : Step1CascadeControlled H w v B) :
    ∃ tau : ℂ,
      tau ∈ (nsActiveStratificationData (r := r) theta' w v).Omega
        (step1FinalTierIndex n).1 ∧
      step1SelectedOnlyCollision
        (nsActiveStratificationData (r := r) theta' w v)
        (step1TargetSelectedChain H h) (step1FinalTierIndex n) tau ∧
      BlowsUpAt
        (fun z => (nsActiveStratificationData (r := r) theta' w v).observable z i.1)
        tau := by
  let jlast : Step1LaterTierIndex n := Fin.last n
  rcases step1_complete_ignition_payload hInv hcomplete h jlast with
    ⟨_ignition, P, hP, _hhead, _hchain, _htier, hPexact⟩
  have hW := hcontrol h jlast P hP
  have hjlast : jlast.toTier = step1FinalTierIndex n := by
    simpa [jlast] using step1LastLaterTier_toTier (n := n)
  have hOmega : P.point ∈
      (nsActiveStratificationData (r := r) theta' w v).Omega
        (step1FinalTierIndex n).1 := by
    simpa [hW.tier, hjlast] using hPexact.1
  have hcollision : step1SelectedOnlyCollision
      (nsActiveStratificationData (r := r) theta' w v)
      (step1TargetSelectedChain H h) (step1FinalTierIndex n) P.point := by
    simpa [hjlast] using hW.selectedOnly
  exact ⟨P.point, hOmega, hcollision,
    step1CascadeClosure_nsActive_of_readyPole H w v h i P hW⟩

/-- End-to-end finite-fold assembly from the concrete ready-pole producer.
This is the public NS105-to-NS108 interface: the producer is invoked exactly
at ready ignition slots; all residue slots, invariant preservation, completion,
and terminal blowup are discharged here. -/
theorem step1CascadeClosure_of_readyPoleProducer_nsActive
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w v : Vec d)
    (produce : ∀ (B : Step1TierBookkeeping n k d),
      Step1ProcessingFold H (nsActiveStratificationData (r := r) theta' w v) w
        (step1InitialTierBookkeeping H
          (nsActiveStratificationData (r := r) theta' w v)) B →
      Step1CascadeControlled H w v B →
      ∀ (h : Fin k) (j : Step1LaterTierIndex n),
        Step1ReadyToProcess B.processed (h, .ignition j) →
        ∃ P : Step1SelectedPoleRecord n k d,
          P.firstHead = h ∧ P.chain = B.chain h ∧ P.tier = j.toTier ∧
          Step1ReadyPoleWitness H w v h j P) :
    ∀ (h : Fin k) (i : Step1ResidueCoordinateIndex H w h),
      ∃ tau : ℂ,
        tau ∈ (nsActiveStratificationData (r := r) theta' w v).Omega
          (step1FinalTierIndex n).1 ∧
        step1SelectedOnlyCollision
          (nsActiveStratificationData (r := r) theta' w v)
          (step1TargetSelectedChain H h) (step1FinalTierIndex n) tau ∧
        BlowsUpAt
          (fun z => (nsActiveStratificationData (r := r) theta' w v).observable z i.1)
          tau := by
  intro h i
  rcases step1_exists_complete_controlledFold_of_readyPoleProducer H w v produce with
    ⟨B, hfold, hcomplete, hcontrol⟩
  have hInv : Step1TierInvariant H
      (nsActiveStratificationData (r := r) theta' w v) w B :=
    hfold.preserves_invariant
      (step1InitialTierInvariant H
        (nsActiveStratificationData (r := r) theta' w v) w)
  exact step1CascadeClosure_of_completeControlledFold_nsActive
    H w v h i B hInv hcomplete hcontrol

/-- A canonical member of each first affine pole progression. -/
noncomputable def step1CanonicalFirstPole
    {theta theta' : Params (n + 2) k d}
    {H : Step1StandingHypotheses r theta theta'}
    (P : Step1SeparatedProbePackage H) (h : Fin k) : ℂ :=
  affineSigmoidPole (logScale r)
    (matrixBilin (attentionMatrix theta' 0 h) P.w P.v) 0

theorem step1CanonicalFirstPole_mem
    {theta theta' : Params (n + 2) k d}
    {H : Step1StandingHypotheses r theta theta'}
    (P : Step1SeparatedProbePackage H) (h : Fin k) :
    step1CanonicalFirstPole P h ∈ affineSigmoidPoleSet (logScale r)
      (matrixBilin (attentionMatrix theta' 0 h) P.w P.v) := by
  exact TransformerIdentifiability.NLayer.sigmoidPole_mem_firstPoleSet _ _ 0

/-- **Unconditional NS105/NS108 capstone.**  The separated probe and `1 < r`
now construct the ready-pole producer internally; no analytic producer premise
remains. -/
theorem step1CascadeClosure_nsActive_unconditional
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta')
    (P : Step1SeparatedProbePackage H) (hr : 1 < r) :
    ∀ (h : Fin k) (i : Step1ResidueCoordinateIndex H P.w h),
      ∃ tau : ℂ,
        tau ∈ (nsActiveStratificationData (r := r) theta' P.w P.v).Omega
          (step1FinalTierIndex n).1 ∧
        step1SelectedOnlyCollision
          (nsActiveStratificationData (r := r) theta' P.w P.v)
          (step1TargetSelectedChain H h) (step1FinalTierIndex n) tau ∧
        BlowsUpAt
          (fun z => (nsActiveStratificationData (r := r) theta' P.w P.v).observable
            z i.1) tau := by
  exact step1CascadeClosure_of_readyPoleProducer_nsActive H P.w P.v
    (step1ReadyPoleProducer_nsActive H P hr (step1CanonicalFirstPole P)
      (step1CanonicalFirstPole_mem P))

end

end TransformerIdentifiability.NLayer.NoSkip
