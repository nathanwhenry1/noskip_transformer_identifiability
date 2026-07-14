import AnyLayerIdentifiabilityProof.NLayer.NoSkip.FormalStreams
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.SharedToolbox

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.NoSkip

/-!
# Active singular-head stratification scaffold

This file contains the no-skip declaration graph used to begin the Step-1
singular stratification.  Its only model-specific slope input is
`NoSkip.formalSlope`.  Local holomorphic stratification beyond one recursive
step is intentionally deferred.
-/

noncomputable section

/-! ## Active heads -/

/-- A head is active when its value matrix is nonzero. -/
def IsActiveHead {L k d : Nat} (θ : Params L k d)
    (l : Fin L) (a : Fin k) : Prop :=
  valueMatrix θ l a ≠ 0

/-- Finite set of active heads at a layer. -/
noncomputable def activeHeads {L k d : Nat} (θ : Params L k d)
    (l : Fin L) : Finset (Fin k) := by
  classical
  exact Finset.univ.filter fun a => IsActiveHead θ l a

@[simp] theorem mem_activeHeads {L k d : Nat} (θ : Params L k d)
    (l : Fin L) (a : Fin k) :
    a ∈ activeHeads θ l ↔ IsActiveHead θ l a := by
  classical
  simp [activeHeads]

@[simp] theorem mem_activeHeads_iff_valueMatrix_ne_zero {L k d : Nat}
    (θ : Params L k d) (l : Fin L) (a : Fin k) :
    a ∈ activeHeads θ l ↔ valueMatrix θ l a ≠ 0 := by
  simp [IsActiveHead]

@[simp] theorem not_mem_activeHeads_iff_valueMatrix_eq_zero {L k d : Nat}
    (θ : Params L k d) (l : Fin L) (a : Fin k) :
    a ∉ activeHeads θ l ↔ valueMatrix θ l a = 0 := by
  classical
  rw [mem_activeHeads_iff_valueMatrix_ne_zero]
  exact not_not

/-- Active formal gate variables are precisely variables of active heads. -/
def IsActiveVar {L k d : Nat} (θ : Params L k d)
    (x : FormalVar L k) : Prop :=
  IsActiveHead θ x.1 x.2

@[simp] theorem isActiveVar_iff {L k d : Nat} (θ : Params L k d)
    (l : Fin L) (a : Fin k) :
    IsActiveVar θ (l, a) ↔ a ∈ activeHeads θ l := by
  simp [IsActiveVar]

/-! ## Complex formal slopes and levels -/

/-- Complex-valued model vectors. -/
abbrev ComplexVec (d : Nat) := Fin d → ℂ

/-- Evaluate a real formal polynomial at complex gate coordinates. -/
noncomputable def evalFormalPolyComplex {L k : Nat}
    (η : FormalVar L k → ℂ) (p : FormalPoly L k) : ℂ :=
  MvPolynomial.eval₂ (algebraMap ℝ ℂ) η p

/-- Complex evaluation at a real assignment agrees with real evaluation followed
by the scalar embedding. -/
theorem evalFormalPolyComplex_ofReal {L k : Nat}
    (ρ : FormalAssignment L k) (p : FormalPoly L k) :
    evalFormalPolyComplex (fun x => (ρ x : ℂ)) p =
      (MvPolynomial.eval ρ p : ℂ) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [evalFormalPolyComplex]
  | add p q hp hq =>
      simp only [evalFormalPolyComplex, MvPolynomial.eval₂_add, map_add]
      change evalFormalPolyComplex (fun x => (ρ x : ℂ)) p +
          evalFormalPolyComplex (fun x => (ρ x : ℂ)) q =
        ((MvPolynomial.eval ρ p + MvPolynomial.eval ρ q : ℝ) : ℂ)
      rw [hp, hq]
      norm_num
  | mul_X p x hp =>
      simp only [evalFormalPolyComplex, MvPolynomial.eval₂_mul,
        MvPolynomial.eval₂_X, MvPolynomial.eval_X, map_mul]
      change evalFormalPolyComplex (fun x => (ρ x : ℂ)) p * (ρ x : ℂ) =
        ((MvPolynomial.eval ρ p * ρ x : ℝ) : ℂ)
      rw [hp]
      norm_num

/-- Complex evaluation of a formal polynomial is holomorphic when each gate
coordinate is holomorphic.  The polynomial itself is treated opaquely. -/
theorem evalFormalPolyComplex_analyticOnNhd {L k : Nat}
    (p : FormalPoly L k) {U : Set ℂ}
    {η : FormalVar L k → ℂ → ℂ}
    (hη : ∀ x : FormalVar L k, AnalyticOnNhd ℂ (η x) U) :
    AnalyticOnNhd ℂ
      (fun τ => evalFormalPolyComplex (fun x => η x τ) p) U := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      simpa [evalFormalPolyComplex] using
        (analyticOnNhd_const (𝕜 := ℂ) (v := (algebraMap ℝ ℂ a)) (s := U))
  | add p q hp hq =>
      simpa [evalFormalPolyComplex] using hp.add hq
  | mul_X p x hp =>
      simpa [evalFormalPolyComplex] using hp.mul (hη x)

/-- The no-skip formal slope evaluated at complex gate coordinates. -/
noncomputable def complexFormalSlope {L k d : Nat} (θ : Params L k d)
    (w v : Vec d) (η : FormalVar L k → ℂ) (x : FormalVar L k) : ℂ :=
  evalFormalPolyComplex η (formalSlope θ w v x.1 x.2)

/-- Affine sigmoid level `τ φ_{la}(z) + log r` built from the no-skip formal
slope polynomial. -/
noncomputable def formalLevel {r L k d : Nat} (θ : Params L k d)
    (w v : Vec d) (η : FormalVar L k → ℂ)
    (x : FormalVar L k) (τ : ℂ) : ℂ :=
  τ * complexFormalSlope θ w v η x + (logScale r : ℂ)

/-- A no-skip formal slope is holomorphic under any holomorphic gate
assignment.  No realization or collapse formula is used. -/
theorem complexFormalSlope_analyticOnNhd {L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (x : FormalVar L k)
    {U : Set ℂ} {η : FormalVar L k → ℂ → ℂ}
    (hη : ∀ y : FormalVar L k, AnalyticOnNhd ℂ (η y) U) :
    AnalyticOnNhd ℂ
      (fun τ => complexFormalSlope θ w v (fun y => η y τ) x) U := by
  exact evalFormalPolyComplex_analyticOnNhd
    (formalSlope θ w v x.1 x.2) hη

/-- The affine no-skip level is holomorphic under any holomorphic gate
assignment. -/
theorem formalLevel_analyticOnNhd {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (x : FormalVar L k)
    {U : Set ℂ} {η : FormalVar L k → ℂ → ℂ}
    (hη : ∀ y : FormalVar L k, AnalyticOnNhd ℂ (η y) U) :
    AnalyticOnNhd ℂ
      (fun τ => formalLevel (r := r) θ w v (fun y => η y τ) x τ) U := by
  have hid : AnalyticOnNhd ℂ (fun τ : ℂ => τ) U := by
    intro τ _hτ
    simpa using (analyticAt_id : AnalyticAt ℂ (fun τ : ℂ => τ) τ)
  have hslope := complexFormalSlope_analyticOnNhd θ w v x hη
  have hconst : AnalyticOnNhd ℂ (fun _ : ℂ => (logScale r : ℂ)) U :=
    analyticOnNhd_const (𝕜 := ℂ) (v := (logScale r : ℂ)) (s := U)
  simpa [formalLevel] using (hid.mul hslope).add hconst

/-- Local version used at layer `x.1`: prior gates may vary
holomorphically, while all other formal coordinates are set to zero. -/
theorem formalLevel_priorAssignment_analyticOnNhd {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (x : FormalVar L k)
    {U : Set ℂ} {η : FormalVar L k → ℂ → ℂ}
    (hη : ∀ y : FormalVar L k, y.1 < x.1 →
      AnalyticOnNhd ℂ (η y) U) :
    AnalyticOnNhd ℂ
      (fun τ => formalLevel (r := r) θ w v
        (fun y => if y.1 < x.1 then η y τ else 0) x τ) U := by
  apply formalLevel_analyticOnNhd θ w v x
  intro y
  by_cases hy : y.1 < x.1
  · simpa [hy] using hη y hy
  · simpa [hy] using
      (analyticOnNhd_const (𝕜 := ℂ) (v := (0 : ℂ)) (s := U))

/-- Every affine formal level has the common real origin value. -/
@[simp] theorem formalLevel_zero {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d)
    (η : FormalVar L k → ℂ) (x : FormalVar L k) :
    formalLevel (r := r) θ w v η x 0 = (logScale r : ℂ) := by
  simp [formalLevel]

/-- At actual real gates, the complex formal slope is the actual no-skip probe
slope. -/
theorem complexFormalSlope_actualProbeGateAssignment {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (τ : ℝ) (x : FormalVar L k) :
    complexFormalSlope θ w v
        (fun y => (actualProbeGateAssignment r θ w v τ y : ℂ)) x =
      (actualProbeSlope r θ w v τ x.1 x.2 : ℂ) := by
  rw [complexFormalSlope, evalFormalPolyComplex_ofReal,
    eval_formalSlope_actualProbeGateAssignment]

/-- Actual-gate specialization of the affine formal level. -/
theorem formalLevel_actualProbeGateAssignment {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (τ : ℝ) (x : FormalVar L k) :
    formalLevel (r := r) θ w v
        (fun y => (actualProbeGateAssignment r θ w v τ y : ℂ)) x (τ : ℂ) =
      ((τ * actualProbeSlope r θ w v τ x.1 x.2 + logScale r : ℝ) : ℂ) := by
  rw [formalLevel, complexFormalSlope_actualProbeGateAssignment]
  norm_num

/-! ## Singular strata and recursive domains -/

/-- Slots for active-head singular stratification data. -/
structure ActiveStratificationData (L k d : Nat) where
  Omega : Nat → Set ℂ
  stratum : Nat → Set ℂ
  level : FormalVar L k → ℂ → ℂ
  gate : FormalVar L k → ℂ → ℂ
  observable : ℂ → ComplexVec d

def nonnegativeRealAxis : Set ℂ :=
  {z | ∃ t : ℝ, 0 ≤ t ∧ z = t}

def positiveRealAxis : Set ℂ :=
  {z | ∃ t : ℝ, 0 < t ∧ z = t}

theorem ofReal_mem_positiveRealAxis {t : ℝ} (ht : 0 < t) :
    (t : ℂ) ∈ positiveRealAxis :=
  ⟨t, ht, rfl⟩

theorem positiveRealAxis_subset_nonnegativeRealAxis :
    positiveRealAxis ⊆ nonnegativeRealAxis := by
  rintro z ⟨t, ht, rfl⟩
  exact ⟨t, ht.le, rfl⟩

theorem zero_mem_nonnegativeRealAxis : (0 : ℂ) ∈ nonnegativeRealAxis :=
  ⟨0, le_rfl, by simp⟩

/-- A complex-valued function takes real values on a specified set. -/
def IsRealValuedOn (F : ℂ → ℂ) (A : Set ℂ) : Prop :=
  ∀ z ∈ A, ∃ x : ℝ, F z = x

theorem one_mem_positiveRealAxis : (1 : ℂ) ∈ positiveRealAxis :=
  ofReal_mem_positiveRealAxis (by norm_num)

theorem positiveRealAxis_subset_of_nonnegativeRealAxis_subset {U : Set ℂ}
    (hU : nonnegativeRealAxis ⊆ U) :
    positiveRealAxis ⊆ U :=
  fun _ hz => hU (positiveRealAxis_subset_nonnegativeRealAxis hz)

/-- The active reduced singular stratum in the current domain. -/
def reducedStratumAt {L k d : Nat} (θ : Params L k d)
    (D : ActiveStratificationData L k d) (l : Fin L) : Set ℂ :=
  {τ | ∃ a : Fin k, a ∈ activeHeads θ l ∧
    τ ∈ D.Omega l.1 ∧ D.level (l, a) τ ∈ Pi}

/-- Unreduced stratum indexed by all heads. -/
def fullStratumAt {L k d : Nat} (D : ActiveStratificationData L k d)
    (l : Fin L) : Set ℂ :=
  {τ | ∃ a : Fin k, τ ∈ D.Omega l.1 ∧ D.level (l, a) τ ∈ Pi}

@[simp] theorem mem_reducedStratumAt_iff {L k d : Nat}
    (θ : Params L k d) (D : ActiveStratificationData L k d)
    (l : Fin L) (τ : ℂ) :
    τ ∈ reducedStratumAt θ D l ↔
      ∃ a : Fin k, a ∈ activeHeads θ l ∧
        τ ∈ D.Omega l.1 ∧ D.level (l, a) τ ∈ Pi :=
  Iff.rfl

theorem reducedStratumAt_subset_omega {L k d : Nat}
    (θ : Params L k d) (D : ActiveStratificationData L k d) (l : Fin L) :
    reducedStratumAt θ D l ⊆ D.Omega l.1 := by
  rintro τ ⟨_a, _ha, hτ, _hpole⟩
  exact hτ

theorem fullStratumAt_subset_omega {L k d : Nat}
    (D : ActiveStratificationData L k d) (l : Fin L) :
    fullStratumAt D l ⊆ D.Omega l.1 := by
  rintro τ ⟨_a, hτ, _hpole⟩
  exact hτ

theorem reducedStratumAt_subset_fullStratumAt {L k d : Nat}
    (θ : Params L k d) (D : ActiveStratificationData L k d) (l : Fin L) :
    reducedStratumAt θ D l ⊆ fullStratumAt D l := by
  rintro τ ⟨a, _ha, hτ, hpole⟩
  exact ⟨a, hτ, hpole⟩

/-- Holomorphic active levels which are not constantly equal to a pole have a
closed-discrete reduced stratum in the current plane domain. -/
theorem reducedStratumAt_closedDiscrete_of_level_data {L k d : Nat}
    (θ : Params L k d) (D : ActiveStratificationData L k d) (l : Fin L)
    (hOmega : PlaneDomain (D.Omega l.1))
    (hlevel_holomorphic :
      ∀ a : Fin k, a ∈ activeHeads θ l →
        AnalyticOnNhd ℂ (D.level (l, a)) (D.Omega l.1))
    (hlevel_not_constant_pole :
      ∀ a : Fin k, a ∈ activeHeads θ l →
        ∀ c : ℂ, c ∈ Pi →
          ¬ Set.EqOn (D.level (l, a)) (fun _ : ℂ => c) (D.Omega l.1)) :
    ClosedDiscreteIn (reducedStratumAt θ D l) (D.Omega l.1) := by
  classical
  let A : Fin k → Set ℂ :=
    fun a => D.Omega l.1 ∩ (D.level (l, a)) ⁻¹' Pi
  have hA :
      ∀ a, a ∈ activeHeads θ l → ClosedDiscreteIn (A a) (D.Omega l.1) := by
    intro a ha
    by_cases hnonconst :
        ∀ c : ℂ, ¬ Set.EqOn (D.level (l, a)) (fun _ : ℂ => c) (D.Omega l.1)
    · exact KHead.closedDiscrete_preimage hOmega.isOpen
        hOmega.isConnected.isPreconnected (hlevel_holomorphic a ha)
        hnonconst Pi_closedDiscrete
    · have hconst :
          ∃ c : ℂ, Set.EqOn (D.level (l, a)) (fun _ : ℂ => c) (D.Omega l.1) := by
        by_contra hnone
        apply hnonconst
        intro c hc
        exact hnone ⟨c, hc⟩
      rcases hconst with ⟨c, hc⟩
      have hAempty : A a = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.2
        intro τ hτ
        rcases hτ with ⟨hτOmega, hτPi⟩
        have hcPi : c ∈ Pi := by
          simpa [hc hτOmega] using hτPi
        exact (hlevel_not_constant_pole a ha c hcPi) hc
      simpa [hAempty] using
        KHead.closedDiscreteIn_empty (U := D.Omega l.1) hOmega.isOpen
  have hCD : ClosedDiscreteIn (⋃ a ∈ activeHeads θ l, A a) (D.Omega l.1) :=
    KHead.closedDiscreteIn_finset_biUnion
      (activeHeads θ l) hOmega.isOpen hA
  have hEq :
      (⋃ a, ⋃ _ : IsActiveHead θ l a, A a) = reducedStratumAt θ D l := by
    ext τ
    constructor
    · intro hτ
      simp only [A, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage] at hτ
      rcases hτ with ⟨a, ha, hτOmega, hτPi⟩
      exact ⟨a, (mem_activeHeads θ l a).2 ha, hτOmega, hτPi⟩
    · rintro ⟨a, ha, hτOmega, hτPi⟩
      simp only [A, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage]
      exact ⟨a, (mem_activeHeads θ l a).1 ha, hτOmega, hτPi⟩
  simpa [hEq] using hCD

/-- A level taking the real value `logScale r` at the origin cannot be
constantly equal to a sigmoid pole on a domain containing the origin. -/
theorem level_not_constant_pole_of_level_zero {r L k d : Nat}
    (D : ActiveStratificationData L k d) {l : Fin L} {a : Fin k}
    (hzero_mem : (0 : ℂ) ∈ D.Omega l.1)
    (hlevel_zero : D.level (l, a) 0 = (logScale r : ℂ)) :
    ∀ c : ℂ, c ∈ Pi →
      ¬ Set.EqOn (D.level (l, a)) (fun _ : ℂ => c) (D.Omega l.1) := by
  intro c hcPi hconst
  have hc : (logScale r : ℂ) = c := by
    rw [← hlevel_zero]
    exact hconst hzero_mem
  have hlogPi : (logScale r : ℂ) ∈ Pi := by
    simpa [hc.symm] using hcPi
  exact ofReal_notMem_Pi (logScale r) hlogPi

/-- The origin normalization packages the nonconstant-pole side condition for
the local active stratum. -/
theorem reducedStratumAt_closedDiscrete_of_level_zero {r L k d : Nat}
    (θ : Params L k d) (D : ActiveStratificationData L k d) (l : Fin L)
    (hOmega : PlaneDomain (D.Omega l.1))
    (hzero_mem : (0 : ℂ) ∈ D.Omega l.1)
    (hlevel_holomorphic :
      ∀ a : Fin k, a ∈ activeHeads θ l →
        AnalyticOnNhd ℂ (D.level (l, a)) (D.Omega l.1))
    (hlevel_zero :
      ∀ a : Fin k, a ∈ activeHeads θ l →
        D.level (l, a) 0 = (logScale r : ℂ)) :
    ClosedDiscreteIn (reducedStratumAt θ D l) (D.Omega l.1) := by
  refine reducedStratumAt_closedDiscrete_of_level_data
    θ D l hOmega hlevel_holomorphic ?_
  intro a ha c hcPi
  exact level_not_constant_pole_of_level_zero (r := r) D hzero_mem
    (hlevel_zero a ha) c hcPi

/-- Closed-discreteness for a datum whose stored stratum is the active reduced
stratum at this layer. -/
theorem stratum_closedDiscrete_of_level_zero_data {r L k d : Nat}
    (θ : Params L k d) (D : ActiveStratificationData L k d) (l : Fin L)
    (hstratum : D.stratum l.1 = reducedStratumAt θ D l)
    (hOmega : PlaneDomain (D.Omega l.1))
    (hzero_mem : (0 : ℂ) ∈ D.Omega l.1)
    (hlevel_holomorphic :
      ∀ a : Fin k, a ∈ activeHeads θ l →
        AnalyticOnNhd ℂ (D.level (l, a)) (D.Omega l.1))
    (hlevel_zero :
      ∀ a : Fin k, a ∈ activeHeads θ l →
        D.level (l, a) 0 = (logScale r : ℂ)) :
    ClosedDiscreteIn (D.stratum l.1) (D.Omega l.1) := by
  rw [hstratum]
  exact reducedStratumAt_closedDiscrete_of_level_zero
    (r := r) θ D l hOmega hzero_mem hlevel_holomorphic hlevel_zero

/-- Recursive domains obtained by deleting one active reduced stratum per layer. -/
noncomputable def activeRecursiveOmega {L k d : Nat} (θ : Params L k d)
    (level : FormalVar L k → ℂ → ℂ) : Nat → Set ℂ
  | 0 => Set.univ
  | n + 1 =>
      if hn : n < L then
        activeRecursiveOmega θ level n \
          {τ | ∃ a : Fin k, a ∈ activeHeads θ ⟨n, hn⟩ ∧
            τ ∈ activeRecursiveOmega θ level n ∧ level (⟨n, hn⟩, a) τ ∈ Pi}
      else activeRecursiveOmega θ level n

noncomputable def activeRecursiveStratum {L k d : Nat} (θ : Params L k d)
    (level : FormalVar L k → ℂ → ℂ) (n : Nat) : Set ℂ :=
  if hn : n < L then
    {τ | ∃ a : Fin k, a ∈ activeHeads θ ⟨n, hn⟩ ∧
      τ ∈ activeRecursiveOmega θ level n ∧ level (⟨n, hn⟩, a) τ ∈ Pi}
  else ∅

@[simp] theorem activeRecursiveOmega_zero {L k d : Nat} (θ : Params L k d)
    (level : FormalVar L k → ℂ → ℂ) :
    activeRecursiveOmega θ level 0 = Set.univ :=
  rfl

theorem activeRecursiveOmega_succ {L k d : Nat} (θ : Params L k d)
    (level : FormalVar L k → ℂ → ℂ) {n : Nat} (hn : n < L) :
    activeRecursiveOmega θ level (n + 1) =
      activeRecursiveOmega θ level n \ activeRecursiveStratum θ level n := by
  simp [activeRecursiveOmega, activeRecursiveStratum, hn]

/-- Assemble the initial recursive stratum graph from candidate functions. -/
noncomputable def activeStratificationDataOfFunctions {L k d : Nat}
    (θ : Params L k d) (level gate : FormalVar L k → ℂ → ℂ)
    (observable : ℂ → ComplexVec d) : ActiveStratificationData L k d where
  Omega := activeRecursiveOmega θ level
  stratum := activeRecursiveStratum θ level
  level := level
  gate := gate
  observable := observable

@[simp] theorem activeStratificationDataOfFunctions_omega_zero {L k d : Nat}
    (θ : Params L k d) (level gate : FormalVar L k → ℂ → ℂ)
    (observable : ℂ → ComplexVec d) :
    (activeStratificationDataOfFunctions θ level gate observable).Omega 0 =
      Set.univ :=
  rfl

theorem activeStratificationDataOfFunctions_stratum_eq {L k d : Nat}
    (θ : Params L k d) (level gate : FormalVar L k → ℂ → ℂ)
    (observable : ℂ → ComplexVec d) (l : Fin L) :
    (activeStratificationDataOfFunctions θ level gate observable).stratum l.1 =
      reducedStratumAt θ (activeStratificationDataOfFunctions θ level gate observable) l := by
  ext τ
  simp [activeStratificationDataOfFunctions, activeRecursiveStratum,
    reducedStratumAt, l.2]

theorem activeStratificationDataOfFunctions_omega_succ {L k d : Nat}
    (θ : Params L k d) (level gate : FormalVar L k → ℂ → ℂ)
    (observable : ℂ → ComplexVec d) (l : Fin L) :
    (activeStratificationDataOfFunctions θ level gate observable).Omega (l.1 + 1) =
      (activeStratificationDataOfFunctions θ level gate observable).Omega l.1 \
        (activeStratificationDataOfFunctions θ level gate observable).stratum l.1 := by
  simpa [activeStratificationDataOfFunctions] using
    activeRecursiveOmega_succ θ level l.2

theorem reducedStratumAt_eq_empty_of_activeHeads_eq_empty {L k d : Nat}
    {θ : Params L k d} (D : ActiveStratificationData L k d) {l : Fin L}
    (hactive : activeHeads θ l = ∅) :
    reducedStratumAt θ D l = ∅ := by
  ext τ
  simp [reducedStratumAt, hactive]

/-- Union of the reduced strata through all `L` layers. -/
def reducedSingularSet {L k d : Nat} (D : ActiveStratificationData L k d) : Set ℂ :=
  partialUnion D.stratum L

/-- Recursive removal identifies every intermediate domain with the complement of
the strata accumulated so far. -/
theorem omega_eq_partialUnion_compl_of_omega_succ {L k d : Nat}
    (D : ActiveStratificationData L k d)
    (hzero : D.Omega 0 = Set.univ)
    (hsucc : ∀ l : Fin L,
      D.Omega (l.1 + 1) = D.Omega l.1 \ D.stratum l.1) :
    ∀ n : Nat, n ≤ L → D.Omega n = (partialUnion D.stratum n)ᶜ
  | 0, _hn => by
      simp [partialUnion, hzero]
  | n + 1, hn => by
      let l : Fin L := ⟨n, Nat.lt_of_succ_le hn⟩
      have hprev : D.Omega n = (partialUnion D.stratum n)ᶜ :=
        omega_eq_partialUnion_compl_of_omega_succ D hzero hsucc n
          (Nat.le_of_succ_le hn)
      calc
        D.Omega (n + 1) = D.Omega n \ D.stratum n := by
          simpa [l] using hsucc l
        _ = (partialUnion D.stratum n)ᶜ \ D.stratum n := by rw [hprev]
        _ = (partialUnion D.stratum (n + 1))ᶜ := by
          ext τ
          simp [partialUnion_succ, Set.diff_eq]

/-- The recursion-only interface for active singular-head data. -/
structure ActiveHeadRecursiveSkeleton {L k d : Nat} (θ : Params L k d)
    (D : ActiveStratificationData L k d) : Prop where
  omega_zero : D.Omega 0 = Set.univ
  stratum_eq : ∀ l : Fin L, D.stratum l.1 = reducedStratumAt θ D l
  omega_succ : ∀ l : Fin L,
    D.Omega (l.1 + 1) = D.Omega l.1 \ D.stratum l.1
  omega_eq_partialUnion_compl :
    ∀ n : Nat, n ≤ L → D.Omega n = (partialUnion D.stratum n)ᶜ

theorem activeStratificationDataOfFunctions_omega_eq_partialUnion_compl
    {L k d : Nat} (θ : Params L k d)
    (level gate : FormalVar L k → ℂ → ℂ)
    (observable : ℂ → ComplexVec d) :
    ∀ n : Nat, n ≤ L →
      (activeStratificationDataOfFunctions θ level gate observable).Omega n =
        (partialUnion
          (activeStratificationDataOfFunctions θ level gate observable).stratum n)ᶜ :=
  omega_eq_partialUnion_compl_of_omega_succ
    (activeStratificationDataOfFunctions θ level gate observable)
    (activeStratificationDataOfFunctions_omega_zero θ level gate observable)
    (activeStratificationDataOfFunctions_omega_succ θ level gate observable)

theorem activeStratificationDataOfFunctions_recursiveSkeleton {L k d : Nat}
    (θ : Params L k d) (level gate : FormalVar L k → ℂ → ℂ)
    (observable : ℂ → ComplexVec d) :
    ActiveHeadRecursiveSkeleton θ
      (activeStratificationDataOfFunctions θ level gate observable) where
  omega_zero :=
    activeStratificationDataOfFunctions_omega_zero θ level gate observable
  stratum_eq :=
    activeStratificationDataOfFunctions_stratum_eq θ level gate observable
  omega_succ :=
    activeStratificationDataOfFunctions_omega_succ θ level gate observable
  omega_eq_partialUnion_compl :=
    activeStratificationDataOfFunctions_omega_eq_partialUnion_compl
      θ level gate observable

theorem ActiveHeadRecursiveSkeleton.omega_final_eq_reducedSingularSet_compl
    {L k d : Nat} {θ : Params L k d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadRecursiveSkeleton θ D) :
    D.Omega L = (reducedSingularSet D)ᶜ := by
  simpa [reducedSingularSet] using hD.omega_eq_partialUnion_compl L le_rfl

/-- Every active level avoids the pole set on the domain obtained after
removing its layer stratum. -/
theorem ActiveHeadRecursiveSkeleton.level_notMem_Pi_on_nextOmega
    {L k d : Nat} {θ : Params L k d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadRecursiveSkeleton θ D) (l : Fin L)
    {a : Fin k} (ha : a ∈ activeHeads θ l) {τ : ℂ}
    (hτ : τ ∈ D.Omega (l.1 + 1)) :
    D.level (l, a) τ ∉ Pi := by
  intro hPi
  have hτdiff : τ ∈ D.Omega l.1 \ D.stratum l.1 := by
    simpa [hD.omega_succ l] using hτ
  have hτstratum : τ ∈ D.stratum l.1 := by
    rw [hD.stratum_eq l]
    exact ⟨a, ha, hτdiff.1, hPi⟩
  exact hτdiff.2 hτstratum

/-- Outputs of one local active-stratum update. -/
structure ActiveLocalStratumStep {L k d : Nat}
    (D : ActiveStratificationData L k d) (l : Fin L) : Prop where
  stratum_closedDiscrete :
    ClosedDiscreteIn (D.stratum l.1) (D.Omega l.1)
  accumulated_closed : IsClosed (partialUnion D.stratum (l.1 + 1))
  accumulated_countable : (partialUnion D.stratum (l.1 + 1)).Countable
  next_domain : PlaneDomain (D.Omega (l.1 + 1))
  zero_mem_next : (0 : ℂ) ∈ D.Omega (l.1 + 1)

/-- One occurrence of the recursive local stratification step.  It uses only
the abstract level functions and the NS092 recursion skeleton. -/
theorem activeLocalStratumStep_of_level_zero {r L k d : Nat}
    (θ : Params L k d) (D : ActiveStratificationData L k d)
    (hD : ActiveHeadRecursiveSkeleton θ D) (l : Fin L)
    (hprev_countable : (partialUnion D.stratum l.1).Countable)
    (hOmega : PlaneDomain (D.Omega l.1))
    (hzero_mem : (0 : ℂ) ∈ D.Omega l.1)
    (hlevel_holomorphic :
      ∀ a : Fin k, a ∈ activeHeads θ l →
        AnalyticOnNhd ℂ (D.level (l, a)) (D.Omega l.1))
    (hlevel_zero :
      ∀ a : Fin k, a ∈ activeHeads θ l →
        D.level (l, a) 0 = (logScale r : ℂ)) :
    ActiveLocalStratumStep D l := by
  have hCD : ClosedDiscreteIn (D.stratum l.1) (D.Omega l.1) :=
    stratum_closedDiscrete_of_level_zero_data
      (r := r) θ D l (hD.stratum_eq l) hOmega hzero_mem
        hlevel_holomorphic hlevel_zero
  have hclosed_next : IsClosed (partialUnion D.stratum (l.1 + 1)) := by
    have hrel : IsClosed ((D.Omega l.1)ᶜ ∪ D.stratum l.1) :=
      hCD.isClosed_rel
    have hOmega_eq : D.Omega l.1 = (partialUnion D.stratum l.1)ᶜ :=
      hD.omega_eq_partialUnion_compl l.1 (Nat.le_of_lt l.2)
    rw [hOmega_eq] at hrel
    simpa [partialUnion_succ, Set.union_assoc, Set.union_comm,
      Set.union_left_comm] using hrel
  have hcountable_next : (partialUnion D.stratum (l.1 + 1)).Countable := by
    have hUnion :
        (partialUnion D.stratum l.1 ∪ D.stratum l.1).Countable :=
      hprev_countable.union hCD.countable
    simpa [partialUnion_succ, Set.union_assoc, Set.union_comm,
      Set.union_left_comm] using hUnion
  have hdomain_next : PlaneDomain (D.Omega (l.1 + 1)) := by
    have hOmega_eq :
        D.Omega (l.1 + 1) = (partialUnion D.stratum (l.1 + 1))ᶜ :=
      hD.omega_eq_partialUnion_compl (l.1 + 1)
        (Nat.succ_le_of_lt l.2)
    rw [hOmega_eq]
    exact countable_closed_compl_planeDomain hcountable_next hclosed_next
  have hzero_not_stratum : (0 : ℂ) ∉ D.stratum l.1 := by
    rw [hD.stratum_eq l]
    rintro ⟨a, ha, _hzero, hPi⟩
    have hlogPi : (logScale r : ℂ) ∈ Pi := by
      simpa [hlevel_zero a ha] using hPi
    exact ofReal_notMem_Pi (logScale r) hlogPi
  have hzero_next : (0 : ℂ) ∈ D.Omega (l.1 + 1) := by
    rw [hD.omega_succ l]
    exact ⟨hzero_mem, hzero_not_stratum⟩
  exact ⟨hCD, hclosed_next, hcountable_next, hdomain_next, hzero_next⟩

/-! ## Full finite active-stratification tower -/

/-!
### NS094 transfer dictionary

* TeX layers `1,...,L` are represented by `Fin L`, hence layer `j` is stored at
  natural index `j - 1`.
* The active set `A_j` is `activeHeads θ l`, characterized exactly by
  `valueMatrix θ l a ≠ 0`.
* The TeX slope `phi_{ja}` is the NoSkip polynomial `formalSlope θ w v l a`;
  all constant layer actions, including the matrix denoted `C_l` in the TeX
  transfer dictionary, remain encapsulated in that upstream polynomial API.
* A continued level is `formalLevel`, namely complex probe parameter times the
  evaluated NoSkip slope plus `logScale r`.
* The pole target is `Pi`; the reduced stratum keeps only active heads, and the
  next domain is obtained by set difference.
* `partialUnion D.stratum n` is the first `n` TeX strata and
  `reducedSingularSet D` is their full finite union.
* Holomorphy, reality on the nonnegative axis, and the common origin value are
  the only model-facing hypotheses of the finite fold.  Plane topology and
  closed-discrete finite unions are model-neutral shared results.
-/

/-- Geometry-only endpoint of the no-skip active singular-head construction.
The level fields are the complete model-specific dictionary boundary; the
finite fold below never unfolds a formal stream or a layer constant matrix. -/
structure ActiveHeadSingularStratification {r L k d : Nat}
    (θ : Params L k d) (D : ActiveStratificationData L k d) : Prop where
  omega_zero : D.Omega 0 = Set.univ
  omega_succ : ∀ l : Fin L,
    D.Omega (l.1 + 1) = D.Omega l.1 \ D.stratum l.1
  omega_eq_partialUnion_compl :
    ∀ n : Nat, n ≤ L → D.Omega n = (partialUnion D.stratum n)ᶜ
  stratum_eq : ∀ l : Fin L, D.stratum l.1 = reducedStratumAt θ D l
  level_holomorphic : ∀ l : Fin L, ∀ a : Fin k,
    a ∈ activeHeads θ l →
      AnalyticOnNhd ℂ (D.level (l, a)) (D.Omega l.1)
  level_real_on_nonnegative_axis : ∀ l : Fin L, ∀ a : Fin k,
    a ∈ activeHeads θ l →
      IsRealValuedOn (D.level (l, a)) nonnegativeRealAxis
  level_zero : ∀ l : Fin L, ∀ a : Fin k,
    a ∈ activeHeads θ l → D.level (l, a) 0 = (logScale r : ℂ)
  domain : ∀ n : Nat, n ≤ L → PlaneDomain (D.Omega n)
  nonnegative_axis_subset :
    ∀ n : Nat, n ≤ L → nonnegativeRealAxis ⊆ D.Omega n
  origin_mem : ∀ n : Nat, n ≤ L → (0 : ℂ) ∈ D.Omega n
  stratum_closedDiscrete :
    ∀ l : Fin L, ClosedDiscreteIn (D.stratum l.1) (D.Omega l.1)
  partialUnion_closed :
    ∀ n : Nat, n ≤ L → IsClosed (partialUnion D.stratum n)
  partialUnion_countable :
    ∀ n : Nat, n ≤ L → (partialUnion D.stratum n).Countable
  strataSystem : StrataSystem D.stratum L

/-- Recover the recursion-only NS092 interface from the full tower. -/
theorem activeHeadRecursiveSkeleton_of_activeHeadSingularStratification
    {r L k d : Nat} {θ : Params L k d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification (r := r) θ D) :
    ActiveHeadRecursiveSkeleton θ D where
  omega_zero := hD.omega_zero
  stratum_eq := hD.stratum_eq
  omega_succ := hD.omega_succ
  omega_eq_partialUnion_compl := hD.omega_eq_partialUnion_compl

/-- Fold the NS093 one-step theorem through all `L` layers. -/
theorem activeHeadSingularStratification_of_level_data {r L k d : Nat}
    (θ : Params L k d) (D : ActiveStratificationData L k d)
    (hD : ActiveHeadRecursiveSkeleton θ D)
    (hlevel_holomorphic : ∀ l : Fin L, ∀ a : Fin k,
      a ∈ activeHeads θ l →
        AnalyticOnNhd ℂ (D.level (l, a)) (D.Omega l.1))
    (hlevel_real : ∀ l : Fin L, ∀ a : Fin k,
      a ∈ activeHeads θ l →
        IsRealValuedOn (D.level (l, a)) nonnegativeRealAxis)
    (hlevel_zero : ∀ l : Fin L, ∀ a : Fin k,
      a ∈ activeHeads θ l → D.level (l, a) 0 = (logScale r : ℂ)) :
    ActiveHeadSingularStratification (r := r) θ D := by
  have hmain : ∀ n : Nat, n ≤ L →
      IsClosed (partialUnion D.stratum n) ∧
      (partialUnion D.stratum n).Countable ∧
      PlaneDomain (D.Omega n) ∧
      nonnegativeRealAxis ⊆ D.Omega n := by
    intro n hn
    induction n with
    | zero =>
        have hclosed : IsClosed (partialUnion D.stratum 0) := by
          simp [partialUnion]
        have hcountable : (partialUnion D.stratum 0).Countable := by
          simp [partialUnion]
        have hdomain : PlaneDomain (D.Omega 0) := by
          rw [hD.omega_zero]
          simpa using countable_closed_compl_planeDomain
            (E := (∅ : Set ℂ)) Set.countable_empty isClosed_empty
        have haxis : nonnegativeRealAxis ⊆ D.Omega 0 := by
          rw [hD.omega_zero]
          simp
        exact ⟨hclosed, hcountable, hdomain, haxis⟩
    | succ n ih =>
        have hnle : n ≤ L := Nat.le_of_succ_le hn
        have hnL : n < L := Nat.lt_of_succ_le hn
        rcases ih hnle with ⟨_hclosed, hcountable, hdomain, haxis⟩
        let l : Fin L := ⟨n, hnL⟩
        have hzero : (0 : ℂ) ∈ D.Omega n :=
          haxis zero_mem_nonnegativeRealAxis
        have hstep : ActiveLocalStratumStep D l :=
          activeLocalStratumStep_of_level_zero
            (r := r) θ D hD l hcountable hdomain hzero
              (fun a ha => hlevel_holomorphic l a ha)
              (fun a ha => hlevel_zero l a ha)
        have haxis_next : nonnegativeRealAxis ⊆ D.Omega (n + 1) := by
          rw [show n + 1 = l.1 + 1 by rfl, hD.omega_succ l]
          intro τ hτaxis
          refine ⟨haxis hτaxis, ?_⟩
          intro hτstratum
          rw [hD.stratum_eq l] at hτstratum
          rcases hτstratum with ⟨a, ha, _hτOmega, hτPi⟩
          rcases hlevel_real l a ha τ hτaxis with ⟨x, hx⟩
          rw [hx] at hτPi
          exact ofReal_notMem_Pi x hτPi
        exact ⟨hstep.accumulated_closed, hstep.accumulated_countable,
          hstep.next_domain, haxis_next⟩
  have hstratum_closedDiscrete :
      ∀ l : Fin L, ClosedDiscreteIn (D.stratum l.1) (D.Omega l.1) := by
    intro l
    have hcurrent := hmain l.1 (Nat.le_of_lt l.2)
    exact stratum_closedDiscrete_of_level_zero_data
      (r := r) θ D l (hD.stratum_eq l) hcurrent.2.2.1
        (hcurrent.2.2.2 zero_mem_nonnegativeRealAxis)
        (fun a ha => hlevel_holomorphic l a ha)
        (fun a ha => hlevel_zero l a ha)
  have hstrata : StrataSystem D.stratum L := by
    refine
      { closed_partial := fun n hn => (hmain n hn).1
        noAccumIn := ?_ }
    intro j hj
    let l : Fin L := ⟨j, hj⟩
    have hOmega_eq : D.Omega j = (partialUnion D.stratum j)ᶜ :=
      hD.omega_eq_partialUnion_compl j (Nat.le_of_lt hj)
    have hno := (hstratum_closedDiscrete l).noAccum
    simpa [l, hOmega_eq] using hno
  exact
    { omega_zero := hD.omega_zero
      omega_succ := hD.omega_succ
      omega_eq_partialUnion_compl := hD.omega_eq_partialUnion_compl
      stratum_eq := hD.stratum_eq
      level_holomorphic := hlevel_holomorphic
      level_real_on_nonnegative_axis := hlevel_real
      level_zero := hlevel_zero
      domain := fun n hn => (hmain n hn).2.2.1
      nonnegative_axis_subset := fun n hn => (hmain n hn).2.2.2
      origin_mem := fun n hn =>
        (hmain n hn).2.2.2 zero_mem_nonnegativeRealAxis
      stratum_closedDiscrete := hstratum_closedDiscrete
      partialUnion_closed := fun n hn => (hmain n hn).1
      partialUnion_countable := fun n hn => (hmain n hn).2.1
      strataSystem := hstrata }

/-- Capstone constructor for data assembled by the NS092 recursive function
constructor. -/
theorem activeStratificationDataOfFunctions_singularStratification
    {r L k d : Nat} (θ : Params L k d)
    (level gate : FormalVar L k → ℂ → ℂ)
    (observable : ℂ → ComplexVec d)
    (hlevel_holomorphic : ∀ l : Fin L, ∀ a : Fin k,
      a ∈ activeHeads θ l →
        AnalyticOnNhd ℂ
          ((activeStratificationDataOfFunctions θ level gate observable).level (l, a))
          ((activeStratificationDataOfFunctions θ level gate observable).Omega l.1))
    (hlevel_real : ∀ l : Fin L, ∀ a : Fin k,
      a ∈ activeHeads θ l →
        IsRealValuedOn
          ((activeStratificationDataOfFunctions θ level gate observable).level (l, a))
          nonnegativeRealAxis)
    (hlevel_zero : ∀ l : Fin L, ∀ a : Fin k,
      a ∈ activeHeads θ l →
        (activeStratificationDataOfFunctions θ level gate observable).level
          (l, a) 0 = (logScale r : ℂ)) :
    ActiveHeadSingularStratification (r := r) θ
      (activeStratificationDataOfFunctions θ level gate observable) := by
  exact activeHeadSingularStratification_of_level_data
    (r := r) θ (activeStratificationDataOfFunctions θ level gate observable)
      (activeStratificationDataOfFunctions_recursiveSkeleton
        θ level gate observable)
      hlevel_holomorphic hlevel_real hlevel_zero

theorem strataSystem_of_activeHeadSingularStratification
    {r L k d : Nat} {θ : Params L k d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification (r := r) θ D) :
    StrataSystem D.stratum L :=
  hD.strataSystem

@[simp] theorem mem_activeStratum_iff
    {r L k d : Nat} {θ : Params L k d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification (r := r) θ D)
    (l : Fin L) (τ : ℂ) :
    τ ∈ D.stratum l.1 ↔
      ∃ a : Fin k, a ∈ activeHeads θ l ∧
        τ ∈ D.Omega l.1 ∧ D.level (l, a) τ ∈ Pi := by
  rw [hD.stratum_eq l]
  rfl

theorem stratum_subset_omega
    {r L k d : Nat} {θ : Params L k d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification (r := r) θ D) (l : Fin L) :
    D.stratum l.1 ⊆ D.Omega l.1 := by
  rw [hD.stratum_eq l]
  exact reducedStratumAt_subset_omega θ D l

theorem stratum_countable
    {r L k d : Nat} {θ : Params L k d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification (r := r) θ D) (l : Fin L) :
    (D.stratum l.1).Countable :=
  (hD.stratum_closedDiscrete l).countable

theorem stratum_eq_empty_of_activeHeads_eq_empty
    {r L k d : Nat} {θ : Params L k d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification (r := r) θ D) {l : Fin L}
    (hactive : activeHeads θ l = ∅) :
    D.stratum l.1 = ∅ := by
  rw [hD.stratum_eq l]
  exact reducedStratumAt_eq_empty_of_activeHeads_eq_empty D hactive

theorem stratum_closedDiscrete_partialUnion_compl
    {r L k d : Nat} {θ : Params L k d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification (r := r) θ D)
    {j : Nat} (hj : j < L) :
    ClosedDiscreteIn (D.stratum j) (partialUnion D.stratum j)ᶜ := by
  let l : Fin L := ⟨j, hj⟩
  have hOmega : D.Omega j = (partialUnion D.stratum j)ᶜ :=
    hD.omega_eq_partialUnion_compl j (Nat.le_of_lt hj)
  simpa [l, hOmega] using hD.stratum_closedDiscrete l

theorem reducedSingularSet_closed
    {r L k d : Nat} {θ : Params L k d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification (r := r) θ D) :
    IsClosed (reducedSingularSet D) := by
  simpa [reducedSingularSet] using hD.partialUnion_closed L le_rfl

theorem reducedSingularSet_countable
    {r L k d : Nat} {θ : Params L k d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification (r := r) θ D) :
    (reducedSingularSet D).Countable := by
  simpa [reducedSingularSet] using hD.partialUnion_countable L le_rfl

theorem finalOmega_eq_compl_reducedSingularSet
    {r L k d : Nat} {θ : Params L k d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification (r := r) θ D) :
    D.Omega L = (reducedSingularSet D)ᶜ := by
  simpa [reducedSingularSet] using hD.omega_eq_partialUnion_compl L le_rfl

theorem reducedSingularSet_compl_planeDomain
    {r L k d : Nat} {θ : Params L k d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification (r := r) θ D) :
    PlaneDomain (reducedSingularSet D)ᶜ := by
  rw [← finalOmega_eq_compl_reducedSingularSet hD]
  exact hD.domain L le_rfl

theorem nonnegativeRealAxis_subset_finalOmega
    {r L k d : Nat} {θ : Params L k d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification (r := r) θ D) :
    nonnegativeRealAxis ⊆ D.Omega L :=
  hD.nonnegative_axis_subset L le_rfl

theorem positiveRealAxis_subset_finalOmega
    {r L k d : Nat} {θ : Params L k d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification (r := r) θ D) :
    positiveRealAxis ⊆ D.Omega L :=
  positiveRealAxis_subset_of_nonnegativeRealAxis_subset
    (nonnegativeRealAxis_subset_finalOmega hD)

theorem origin_mem_finalOmega
    {r L k d : Nat} {θ : Params L k d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification (r := r) θ D) :
    (0 : ℂ) ∈ D.Omega L :=
  hD.origin_mem L le_rfl

theorem finalOmega_nonempty
    {r L k d : Nat} {θ : Params L k d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification (r := r) θ D) :
    (D.Omega L).Nonempty :=
  ⟨0, origin_mem_finalOmega hD⟩

theorem origin_not_mem_reducedSingularSet
    {r L k d : Nat} {θ : Params L k d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification (r := r) θ D) :
    (0 : ℂ) ∉ reducedSingularSet D := by
  have hzero : (0 : ℂ) ∈ (reducedSingularSet D)ᶜ := by
    simpa [← finalOmega_eq_compl_reducedSingularSet hD] using
      origin_mem_finalOmega hD
  exact hzero

theorem reducedSingularSet_compl_nonempty
    {r L k d : Nat} {θ : Params L k d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification (r := r) θ D) :
    ((reducedSingularSet D)ᶜ).Nonempty :=
  ⟨0, origin_not_mem_reducedSingularSet hD⟩

@[simp] theorem mem_reducedSingularSet_iff
    {r L k d : Nat} {θ : Params L k d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification (r := r) θ D) (τ : ℂ) :
    τ ∈ reducedSingularSet D ↔
      ∃ l : Fin L, ∃ a : Fin k, a ∈ activeHeads θ l ∧
        τ ∈ D.Omega l.1 ∧ D.level (l, a) τ ∈ Pi := by
  constructor
  · rintro ⟨j, hj, hτj⟩
    let l : Fin L := ⟨j, hj⟩
    rw [hD.stratum_eq l] at hτj
    rcases hτj with ⟨a, ha, hτOmega, hτPi⟩
    exact ⟨l, a, ha, hτOmega, hτPi⟩
  · rintro ⟨l, a, ha, hτOmega, hτPi⟩
    exact ⟨l.1, l.2, by
      rw [hD.stratum_eq l]
      exact ⟨a, ha, hτOmega, hτPi⟩⟩

/-! ## First active stratum -/

/-- First-layer affine level, independent of formal gate coordinates. -/
noncomputable def initialActiveLevel {r L k d : Nat} (θ : Params L k d)
    (w v : Vec d) (hL : 0 < L) (a : Fin k) (τ : ℂ) : ℂ :=
  τ * (matrixBilin (attentionMatrix θ ⟨0, hL⟩ a) w v : ℂ) +
    (logScale r : ℂ)

/-- Singular set contributed by active first-layer heads. -/
noncomputable def initialActiveStratum {r L k d : Nat} (θ : Params L k d)
    (w v : Vec d) (hL : 0 < L) : Set ℂ :=
  ⋃ a ∈ activeHeads θ ⟨0, hL⟩,
    {τ | initialActiveLevel (r := r) θ w v hL a τ ∈ Pi}

/-- On the real probe line, the first no-skip formal level specializes to the
first affine active level. -/
theorem formalLevel_actual_first_eq_initialActiveLevel {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (hL : 0 < L)
    (a : Fin k) (τ : ℝ) :
    formalLevel (r := r) θ w v
        (fun y => (actualProbeGateAssignment r θ w v τ y : ℂ))
        (⟨0, hL⟩, a) (τ : ℂ) =
      initialActiveLevel (r := r) θ w v hL a (τ : ℂ) := by
  rw [formalLevel_actualProbeGateAssignment]
  simp [actualProbeSlope, initialActiveLevel]

theorem mem_initialActiveStratum_iff {r L k d : Nat} (θ : Params L k d)
    (w v : Vec d) (hL : 0 < L) (τ : ℂ) :
    τ ∈ initialActiveStratum (r := r) θ w v hL ↔
      ∃ a : Fin k, a ∈ activeHeads θ ⟨0, hL⟩ ∧
        initialActiveLevel (r := r) θ w v hL a τ ∈ Pi := by
  simp [initialActiveStratum]

/-- The initial active stratum is the finite union of the nonzero affine pole
progressions of active first-layer heads. -/
theorem initialActiveStratum_eq_poleProgressions
    {r L k d : Nat} (θ : Params L k d) (w v : Vec d) (hL : 0 < L) :
    initialActiveStratum (r := r) θ w v hL =
      ⋃ a : Fin k,
        ⋃ _ : a ∈ activeHeads θ ⟨0, hL⟩,
          ⋃ _ : matrixBilin (attentionMatrix θ ⟨0, hL⟩ a) w v ≠ 0,
            affineSigmoidPoleSet (logScale r)
              (matrixBilin (attentionMatrix θ ⟨0, hL⟩ a) w v) := by
  classical
  ext τ
  constructor
  · intro hτ
    rw [mem_initialActiveStratum_iff] at hτ
    rcases hτ with ⟨a, ha, hτPi⟩
    let slope : ℝ := matrixBilin (attentionMatrix θ ⟨0, hL⟩ a) w v
    change τ * (slope : ℂ) + (logScale r : ℂ) ∈ Pi at hτPi
    have hslope : slope ≠ 0 := by
      intro hslope
      have hlogPi : (logScale r : ℂ) ∈ Pi := by
        simpa [hslope] using hτPi
      exact ofReal_notMem_Pi (logScale r) hlogPi
    simp only [Set.mem_iUnion]
    refine ⟨a, ha, ?_, ?_⟩
    · simpa [slope] using hslope
    · apply (mem_affineSigmoidPoleSet_iff hslope τ).2
      simpa [initialActiveLevel, slope, mul_comm] using hτPi
  · intro hτ
    simp only [Set.mem_iUnion] at hτ
    rcases hτ with ⟨a, ha, hslope, hτpole⟩
    rw [mem_initialActiveStratum_iff]
    refine ⟨a, ha, ?_⟩
    have harg := (mem_affineSigmoidPoleSet_iff hslope τ).1 hτpole
    simpa [initialActiveLevel, mul_comm] using harg

/-- Any recursive datum with the affine first levels stores exactly the initial
active stratum at layer zero. -/
theorem initialActiveStratum_eq_reducedStratumAt_of_level_first
    {r L k d : Nat} (θ : Params L k d) (w v : Vec d) (hL : 0 < L)
    (D : ActiveStratificationData L k d)
    (hOmega : D.Omega 0 = Set.univ)
    (hlevel : ∀ a : Fin k, D.level (⟨0, hL⟩, a) =
      initialActiveLevel (r := r) θ w v hL a) :
    initialActiveStratum (r := r) θ w v hL =
      reducedStratumAt θ D ⟨0, hL⟩ := by
  ext τ
  simp [mem_initialActiveStratum_iff, reducedStratumAt, hOmega, hlevel]

theorem first_stratum_eq_initialActiveStratum
    {r L k d : Nat} {θ : Params L k d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification (r := r) θ D)
    (w v : Vec d) (hL : 0 < L)
    (hlevel : ∀ a : Fin k, D.level (⟨0, hL⟩, a) =
      initialActiveLevel (r := r) θ w v hL a) :
    D.stratum 0 = initialActiveStratum (r := r) θ w v hL := by
  let l : Fin L := ⟨0, hL⟩
  calc
    D.stratum 0 = reducedStratumAt θ D l := by
      simpa [l] using hD.stratum_eq l
    _ = initialActiveStratum (r := r) θ w v hL :=
      (initialActiveStratum_eq_reducedStratumAt_of_level_first
        (r := r) θ w v hL D hD.omega_zero hlevel).symm

theorem first_stratum_eq_poleProgressions
    {r L k d : Nat} {θ : Params L k d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification (r := r) θ D)
    (w v : Vec d) (hL : 0 < L)
    (hlevel : ∀ a : Fin k, D.level (⟨0, hL⟩, a) =
      initialActiveLevel (r := r) θ w v hL a) :
    D.stratum 0 =
      ⋃ a : Fin k,
        ⋃ _ : a ∈ activeHeads θ ⟨0, hL⟩,
          ⋃ _ : matrixBilin (attentionMatrix θ ⟨0, hL⟩ a) w v ≠ 0,
            affineSigmoidPoleSet (logScale r)
              (matrixBilin (attentionMatrix θ ⟨0, hL⟩ a) w v) := by
  rw [first_stratum_eq_initialActiveStratum hD w v hL hlevel,
    initialActiveStratum_eq_poleProgressions]

theorem mem_first_stratum_iff
    {r L k d : Nat} {θ : Params L k d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification (r := r) θ D)
    (w v : Vec d) (hL : 0 < L)
    (hlevel : ∀ a : Fin k, D.level (⟨0, hL⟩, a) =
      initialActiveLevel (r := r) θ w v hL a) (τ : ℂ) :
    τ ∈ D.stratum 0 ↔
      ∃ a : Fin k, a ∈ activeHeads θ ⟨0, hL⟩ ∧
        matrixBilin (attentionMatrix θ ⟨0, hL⟩ a) w v ≠ 0 ∧
          τ ∈ affineSigmoidPoleSet (logScale r)
            (matrixBilin (attentionMatrix θ ⟨0, hL⟩ a) w v) := by
  rw [first_stratum_eq_poleProgressions hD w v hL hlevel]
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨a, ha, hslope, hτ⟩
    exact ⟨a, ha, hslope, hτ⟩
  · rintro ⟨a, ha, hslope, hτ⟩
    exact ⟨a, ha, hslope, hτ⟩

theorem isClosed_initialActiveStratum {r L k d : Nat} (θ : Params L k d)
    (w v : Vec d) (hL : 0 < L) :
    IsClosed (initialActiveStratum (r := r) θ w v hL) := by
  classical
  apply isClosed_biUnion_finset
  intro a _ha
  change IsClosed ((fun τ : ℂ =>
    τ * (matrixBilin (attentionMatrix θ ⟨0, hL⟩ a) w v : ℂ) +
      (logScale r : ℂ)) ⁻¹' Pi)
  exact Pi_closed.preimage ((continuous_id.mul continuous_const).add continuous_const)

/-- Complement of the initial active singular set is open. -/
theorem isOpen_initialActiveDomain {r L k d : Nat} (θ : Params L k d)
    (w v : Vec d) (hL : 0 < L) :
    IsOpen (initialActiveStratum (r := r) θ w v hL)ᶜ :=
  (isClosed_initialActiveStratum (r := r) θ w v hL).isOpen_compl

end

end TransformerIdentifiability.NLayer.NoSkip
