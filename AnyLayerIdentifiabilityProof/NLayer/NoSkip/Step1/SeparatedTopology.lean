import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Step1.Hypotheses

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.NoSkip

/-!
# Topology of the Step-1 separated probe set

The set is represented in the native polynomial coordinate space
`AlphaCornerProbeVar d → ℝ`, definitionally one `w` block and one `v` block.
This is the precise coordinate space consumed by the NS037 zero-set/null
adapters.  The pointwise package below decodes each assignment back to the two
probe vectors used by the analytic Step-1 pipeline.
-/

/-- Decode the `w` coordinates from a probe-polynomial assignment. -/
def step1AssignmentW {d : Nat} (rho : AlphaCornerProbeVar d → Real) : Vec d :=
  fun i => rho (Sum.inl i)

/-- Decode the `v` coordinates from a probe-polynomial assignment. -/
def step1AssignmentV {d : Nat} (rho : AlphaCornerProbeVar d → Real) : Vec d :=
  fun i => rho (Sum.inr i)

@[simp] theorem alphaCornerProbeEval_step1Assignment {d : Nat}
    (rho : AlphaCornerProbeVar d → Real) :
    alphaCornerProbeEval (step1AssignmentW rho) (step1AssignmentV rho) = rho := by
  funext x
  rcases x with i | i <;> rfl

/-- The target Step-1 separated locus: the principal nonvanishing set of the
NS090 product polynomial. -/
def step1SeparatedSet {n k d r : Nat} {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') :
    Set (AlphaCornerProbeVar d → Real) :=
  mvPolynomialNonvanishingSet (step1SeparatedProbePolynomial H)

@[simp] theorem mem_step1SeparatedSet_iff {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta')
    (rho : AlphaCornerProbeVar d → Real) :
    rho ∈ step1SeparatedSet H ↔
      ∀ idx : Step1SeparatedFactorIndex n k,
        step1SeparatedFactorValue H (step1AssignmentW rho)
          (step1AssignmentV rho) idx ≠ 0 := by
  classical
  change MvPolynomial.eval rho (step1SeparatedProbePolynomial H) ≠ 0 ↔ _
  rw [← alphaCornerProbeEval_step1Assignment rho,
    eval_step1SeparatedProbePolynomial]
  constructor
  · intro hprod idx
    exact (Finset.prod_ne_zero_iff.mp hprod) idx (Finset.mem_univ idx)
  · intro hfactor
    exact Finset.prod_ne_zero_iff.mpr fun idx _ => hfactor idx

/-- The separated locus is open, including before using nonzeroness of its
defining polynomial. -/
theorem isOpen_step1SeparatedSet {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') :
    IsOpen (step1SeparatedSet H) :=
  isOpen_mvPolynomialNonvanishingSet _

/-- NS090 nonzeroness makes the separated locus dense. -/
theorem dense_step1SeparatedSet {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') :
    Dense (step1SeparatedSet H) :=
  dense_mvPolynomialNonvanishingSet _ (step1SeparatedProbePolynomial_ne_zero H)

theorem step1SeparatedSet_nonempty {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') :
    (step1SeparatedSet H).Nonempty := by
  have hdense := dense_step1SeparatedSet H
  rcases hdense.inter_open_nonempty Set.univ isOpen_univ
      (show (Set.univ : Set (AlphaCornerProbeVar d → Real)).Nonempty from
        ⟨0, Set.mem_univ 0⟩) with
    ⟨rho, _hrho_univ, hrho⟩
  exact ⟨rho, hrho⟩

/-- The exceptional complement is exactly the defining polynomial's zero set. -/
theorem compl_step1SeparatedSet_eq_zeroSet {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') :
    (step1SeparatedSet H)ᶜ =
      mvPolynomialZeroSet (step1SeparatedProbePolynomial H) := by
  ext rho
  simp [step1SeparatedSet, mvPolynomialNonvanishingSet, mvPolynomialZeroSet]

/-- The complement of the target separated set is Lebesgue null. -/
theorem volume_compl_step1SeparatedSet {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') :
    MeasureTheory.volume (step1SeparatedSet H)ᶜ = 0 := by
  rw [compl_step1SeparatedSet_eq_zeroSet]
  exact mvPolynomial_zeroSet_null _ (step1SeparatedProbePolynomial_ne_zero H)

/-- Polynomial-vanishing formulation of Zariski density on the native probe
coordinate space. -/
def Step1ProbeZariskiDense {d : Nat}
    (U : Set (AlphaCornerProbeVar d → Real)) : Prop :=
  ∀ P : AlphaCornerProbePoly d,
    (∀ rho ∈ U, MvPolynomial.eval rho P = 0) → P = 0

/-- Every Euclidean-dense probe-coordinate set is Zariski dense. -/
theorem step1ProbeZariskiDense_of_dense {d : Nat}
    {U : Set (AlphaCornerProbeVar d → Real)} (hU : Dense U) :
    Step1ProbeZariskiDense U := by
  intro P hP
  apply MvPolynomial.funext
  intro rho
  have hclosed : IsClosed
      {x : AlphaCornerProbeVar d → Real | MvPolynomial.eval x P = 0} :=
    isClosed_singleton.preimage (MvPolynomial.continuous_eval P)
  have hsubset : U ⊆
      {x : AlphaCornerProbeVar d → Real | MvPolynomial.eval x P = 0} := by
    intro x hx
    exact hP x hx
  have hrho : rho ∈ closure U := by simp [hU.closure_eq]
  exact (closure_minimal hsubset hclosed) hrho

theorem zariskiDense_step1SeparatedSet {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') :
    Step1ProbeZariskiDense (step1SeparatedSet H) :=
  step1ProbeZariskiDense_of_dense (dense_step1SeparatedSet H)

/-- Reversing a sibling pair negates its all-alpha slope difference. -/
theorem alphaCornerSlopeDiff_swap {L k d : Nat} (r : Nat)
    (theta : Params L k d) (l : Fin L) (a c : Fin k) (w v : Vec d) :
    alphaCornerSlopeDiff r theta l c a w v =
      -alphaCornerSlopeDiff r theta l a c w v := by
  have hmat : attentionMatrix theta l c - attentionMatrix theta l a =
      -(attentionMatrix theta l a - attentionMatrix theta l c) := by
    ext i j
    simp
  unfold alphaCornerSlopeDiff
  rw [hmat]
  rw [matrixBilin_apply, matrixBilin_apply, Matrix.neg_mulVec, dotProduct_neg]

/-- Exact semantic inequalities available at every point of the separated
locus.  All matrices and selected chains are target-side. -/
structure Step1SeparatedPointwiseData {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta')
    (rho : AlphaCornerProbeVar d → Real) : Prop where
  firstSlope_ne_zero : ∀ h : Fin k,
    matrixBilin (attentionMatrix theta' 0 h)
      (step1AssignmentW rho) (step1AssignmentV rho) ≠ 0
  firstSlope_injective : Function.Injective fun h : Fin k =>
    matrixBilin (attentionMatrix theta' 0 h)
      (step1AssignmentW rho) (step1AssignmentV rho)
  cascadeResidue_ne_zero : ∀ h : Fin k,
    cascadeFinalProduct theta' h (H.targetCascadeData.head h).chain *ᵥ
      step1AssignmentW rho ≠ 0
  cascadeIgnition_ne_zero : ∀ (h : Fin k) (j : Fin (n + 1)),
    matrixBilin
      (cascadeIgnitionMatrix theta' h (H.targetCascadeData.head h).chain j)
      (step1AssignmentW rho) (step1AssignmentW rho) ≠ 0
  cornerSibling_ne_zero : ∀ (l : Fin (n + 2)) (a c : Fin k), a ≠ c →
    alphaCornerSlopeDiff r theta' l a c
      (step1AssignmentW rho) (step1AssignmentV rho) ≠ 0

/-- Membership in the principal open locus yields every pointwise separation,
cascade, and corner condition consumed downstream. -/
theorem step1SeparatedPointwiseData_of_mem {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta')
    {rho : AlphaCornerProbeVar d → Real} (hrho : rho ∈ step1SeparatedSet H) :
    Step1SeparatedPointwiseData H rho := by
  classical
  have hfactor := (mem_step1SeparatedSet_iff H rho).mp hrho
  let w := step1AssignmentW rho
  let v := step1AssignmentV rho
  have hslope : ∀ h : Fin k,
      matrixBilin (attentionMatrix theta' 0 h) w v ≠ 0 := by
    intro h
    exact hfactor (Sum.inl (Sum.inl h))
  have hslopePair : ∀ ac : Step1OrderedHeadPair k,
      matrixBilin (attentionMatrix theta' 0 ac.1.1) w v -
        matrixBilin (attentionMatrix theta' 0 ac.1.2) w v ≠ 0 := by
    intro ac
    exact hfactor (Sum.inl (Sum.inr ac))
  have hslopeInj : Function.Injective fun h : Fin k =>
      matrixBilin (attentionMatrix theta' 0 h) w v := by
    intro a c heq
    by_contra hac
    rcases lt_or_gt_of_ne hac with haclt | hcalt
    · let ac : Step1OrderedHeadPair k := ⟨(a, c), haclt⟩
      exact hslopePair ac (sub_eq_zero.mpr heq)
    · let ac : Step1OrderedHeadPair k := ⟨(c, a), hcalt⟩
      exact hslopePair ac (sub_eq_zero.mpr heq.symm)
  have hresidue : ∀ h : Fin k,
      cascadeFinalProduct theta' h (H.targetCascadeData.head h).chain *ᵥ w ≠ 0 := by
    intro h hzero
    change cascadeFinalProduct theta' h (H.targetCascadeData.head h).chain *ᵥ
      step1AssignmentW rho = 0 at hzero
    have hnorm := hfactor (Sum.inr (Sum.inl (Sum.inl h)))
    exact hnorm (by simp [step1SeparatedFactorValue, hzero])
  have hignition : ∀ (h : Fin k) (j : Fin (n + 1)),
      matrixBilin
        (cascadeIgnitionMatrix theta' h (H.targetCascadeData.head h).chain j)
        w w ≠ 0 := by
    intro h j hzero
    change matrixBilin
      (cascadeIgnitionMatrix theta' h (H.targetCascadeData.head h).chain j)
      (step1AssignmentW rho) (step1AssignmentW rho) = 0 at hzero
    have hsq := hfactor (Sum.inr (Sum.inl (Sum.inr (h, j))))
    change (matrixBilin
      (cascadeIgnitionMatrix theta' h (H.targetCascadeData.head h).chain j)
      (step1AssignmentW rho) (step1AssignmentW rho)) ^ 2 ≠ 0 at hsq
    exact hsq (by rw [hzero]; simp)
  have hcornerOrdered : ∀ (l : Fin (n + 2)) (ac : Step1OrderedHeadPair k),
      alphaCornerSlopeDiff r theta' l ac.1.1 ac.1.2 w v ≠ 0 := by
    intro l ac hzero
    change alphaCornerSlopeDiff r theta' l ac.1.1 ac.1.2
      (step1AssignmentW rho) (step1AssignmentV rho) = 0 at hzero
    have hsq := hfactor (Sum.inr (Sum.inr (l, ac)))
    exact hsq (by simp [step1SeparatedFactorValue, hzero])
  have hcorner : ∀ (l : Fin (n + 2)) (a c : Fin k), a ≠ c →
      alphaCornerSlopeDiff r theta' l a c w v ≠ 0 := by
    intro l a c hac
    rcases lt_or_gt_of_ne hac with haclt | hcalt
    · exact hcornerOrdered l ⟨(a, c), haclt⟩
    · intro hzero
      have hrev := hcornerOrdered l ⟨(c, a), hcalt⟩
      rw [alphaCornerSlopeDiff_swap] at hrev
      exact hrev (by simp [hzero])
  exact
    { firstSlope_ne_zero := hslope
      firstSlope_injective := hslopeInj
      cascadeResidue_ne_zero := hresidue
      cascadeIgnition_ne_zero := hignition
      cornerSibling_ne_zero := hcorner }

/-- Complete topological and algebraic properties of the target separated set. -/
structure Step1SeparatedSetProperties {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') : Prop where
  nonempty : (step1SeparatedSet H).Nonempty
  isOpen : IsOpen (step1SeparatedSet H)
  dense : Dense (step1SeparatedSet H)
  complement_null : MeasureTheory.volume (step1SeparatedSet H)ᶜ = 0
  zariski_dense : Step1ProbeZariskiDense (step1SeparatedSet H)

theorem step1SeparatedSetProperties {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') :
    Step1SeparatedSetProperties H where
  nonempty := step1SeparatedSet_nonempty H
  isOpen := isOpen_step1SeparatedSet H
  dense := dense_step1SeparatedSet H
  complement_null := volume_compl_step1SeparatedSet H
  zariski_dense := zariskiDense_step1SeparatedSet H

/-- A chosen separated assignment together with its decoded semantic data. -/
structure Step1SeparatedProbePackage {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') where
  rho : AlphaCornerProbeVar d → Real
  mem : rho ∈ step1SeparatedSet H
  pointwise : Step1SeparatedPointwiseData H rho

namespace Step1SeparatedProbePackage

variable {n k d r : Nat} {theta theta' : Params (n + 2) k d}
  {H : Step1StandingHypotheses r theta theta'}

def w (P : Step1SeparatedProbePackage H) : Vec d := step1AssignmentW P.rho
def v (P : Step1SeparatedProbePackage H) : Vec d := step1AssignmentV P.rho

theorem firstSlope_ne_zero (P : Step1SeparatedProbePackage H) (h : Fin k) :
    matrixBilin (attentionMatrix theta' 0 h) P.w P.v ≠ 0 :=
  P.pointwise.firstSlope_ne_zero h

theorem firstSlope_injective (P : Step1SeparatedProbePackage H) :
    Function.Injective fun h : Fin k =>
      matrixBilin (attentionMatrix theta' 0 h) P.w P.v :=
  P.pointwise.firstSlope_injective

theorem cascadeResidue_ne_zero (P : Step1SeparatedProbePackage H) (h : Fin k) :
    cascadeFinalProduct theta' h (H.targetCascadeData.head h).chain *ᵥ P.w ≠ 0 :=
  P.pointwise.cascadeResidue_ne_zero h

theorem cascadeIgnition_ne_zero (P : Step1SeparatedProbePackage H)
    (h : Fin k) (j : Fin (n + 1)) :
    matrixBilin
      (cascadeIgnitionMatrix theta' h (H.targetCascadeData.head h).chain j)
      P.w P.w ≠ 0 :=
  P.pointwise.cascadeIgnition_ne_zero h j

theorem cornerSibling_ne_zero (P : Step1SeparatedProbePackage H)
    (l : Fin (n + 2)) (a c : Fin k) (hac : a ≠ c) :
    alphaCornerSlopeDiff r theta' l a c P.w P.v ≠ 0 :=
  P.pointwise.cornerSibling_ne_zero l a c hac

end Step1SeparatedProbePackage

/-- Noncomputably select one point of the dense separated locus. -/
noncomputable def step1SeparatedProbePackage {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') :
    Step1SeparatedProbePackage H := by
  let hne := step1SeparatedSet_nonempty H
  let rho := Classical.choose hne
  have hrho : rho ∈ step1SeparatedSet H := Classical.choose_spec hne
  exact
    { rho := rho
      mem := hrho
      pointwise := step1SeparatedPointwiseData_of_mem H hrho }

end TransformerIdentifiability.NLayer.NoSkip
