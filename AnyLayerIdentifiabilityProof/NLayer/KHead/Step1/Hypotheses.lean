import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.SigmoidMixtures
import AnyLayerIdentifiabilityProof.NLayer.KHead.Genericity.AnchorCertificate
import AnyLayerIdentifiabilityProof.NLayer.Foundations.PolynomialGenericity
import AnyLayerIdentifiabilityProof.NLayer.Analytic.AlgebraicQuadric

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.KHead
namespace Step1

/-!
# K-head Step 1 standing hypotheses and separated probes

This file is the statement/API scaffold for
`tex_modular/sections/06a-step1-hypotheses.tex`.

It records the concrete data used at the beginning of Step 1: global equality,
chosen cascade chains, first-layer separated probes, and the promoted linear
tier bookkeeping lemma.  It also realizes the separated-probe factor as a
concrete probe polynomial and proves the dense/open/Zariski-dense package under
target regularity and the selected cascade-chain witnesses.
-/

noncomputable section

/-! ## Standing functional equality -/

/-- Global equality of two depth-`L`, `k`-head transformers on all real inputs. -/
def GlobalTransformerEquality {L k d : Nat} (r : Nat)
    (θ θ' : Params L k d) : Prop :=
  ∀ X : Matrix (Fin d) (Fin (seqLength r)) ℝ, transformer θ X = transformer θ' X

/-- Probe-output equality on positive real probe scales. -/
def ProbeOutputEquality {L k d : Nat} (r : Nat)
    (θ θ' : Params L k d) : Prop :=
  ∀ p : ProbePoint d, ∀ τ : ℝ, 0 < τ →
    probeOutput r θ p.1 p.2 τ = probeOutput r θ' p.1 p.2 τ

/-- Evaluating global transformer equality on probe matrices gives the closed-recursion
probe-output equality from equation `eq:probe-equality`. -/
theorem probeOutputEquality_of_global {r L k d : Nat} {θ θ' : Params L k d}
    (hr : 0 < r) (hglobal : GlobalTransformerEquality r θ θ') :
    ProbeOutputEquality r θ θ' := by
  intro p τ hτ
  ext i
  have hmatrix :=
    congr_fun (congr_fun (hglobal (probeMatrix r p.1 p.2 τ)) i) (Fin.last r)
  rw [transformer_probeMatrix_last hr θ p.1 p.2 τ (le_of_lt hτ) i,
    transformer_probeMatrix_last hr θ' p.1 p.2 τ (le_of_lt hτ) i] at hmatrix
  exact mul_left_cancel₀ (ne_of_gt (Real.sqrt_pos.2 hτ)) hmatrix

/-! ## Cascade chain choices -/

/-- Strictly ordered head pairs, used for the products over `1 <= a < c <= k`. -/
abbrev OrderedHeadPair (k : Nat) : Type :=
  {ac : Fin k × Fin k // ac.1 < ac.2}

/-- A fixed witnessing chain for one first-layer head.

For depth `m+1`, the chain has one chosen head in each later layer, indexed by
`Fin m`.  The fields are the nonzero final residue product and nonzero ignition
matrices named in the cascade certificate.
-/
structure CascadeChainWitness {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) where
  chain : Fin m → Fin k
  finalProduct_ne_zero : cascadeFinalProduct θ h chain ≠ 0
  ignitionMatrix_ne_zero :
    ∀ j : Fin m, cascadeIgnitionMatrix θ h chain j ≠ 0

/-- One fixed witnessing chain for every first-layer head. -/
abbrev Step1ChainChoices {m k d : Nat} (θ : Params (m + 1) k d) : Type :=
  ∀ h : Fin k, CascadeChainWitness θ h

namespace CascadeChainWitness

/-- The matrix nonzero fields imply the scalar cascade chain value is nonzero. -/
theorem chainValue_ne_zero {m k d : Nat} {θ : Params (m + 1) k d}
    {h : Fin k} (χ : CascadeChainWitness θ h) :
    cascadeChainValue θ h χ.chain ≠ 0 := by
  classical
  rw [cascadeChainValue]
  exact mul_ne_zero
    ((matrixFrobSq_ne_zero_iff _).mpr χ.finalProduct_ne_zero)
    (Finset.prod_ne_zero_iff.mpr (by
      intro j _hj
      exact (matrixFrobSq_ne_zero_iff _).mpr (χ.ignitionMatrix_ne_zero j)))

end CascadeChainWitness

/-- A nonzero head certificate has at least one chain with nonzero cascade value. -/
theorem exists_cascadeChainValue_ne_zero_of_headCertificate {m k d : Nat}
    {θ : Params (m + 1) k d} {h : Fin k}
    (hcert : CascadeHeadCertificate θ h) :
    ∃ χ : Fin m → Fin k, cascadeChainValue θ h χ ≠ 0 := by
  classical
  by_contra hnone
  apply hcert
  refine Finset.sum_eq_zero ?_
  intro χ _hχ
  by_contra hχ
  exact hnone ⟨χ, hχ⟩

/-- Extract one witnessing chain for a head from its cascade certificate. -/
theorem exists_cascadeChainWitness_of_headCertificate {m k d : Nat}
    {θ : Params (m + 1) k d} {h : Fin k}
    (hcert : CascadeHeadCertificate θ h) :
    Nonempty (CascadeChainWitness θ h) := by
  classical
  rcases exists_cascadeChainValue_ne_zero_of_headCertificate hcert with ⟨χ, hχ⟩
  rw [cascadeChainValue] at hχ
  have hfinal_sq : matrixFrobSq (cascadeFinalProduct θ h χ) ≠ 0 := by
    intro hzero
    exact hχ (by simp [hzero])
  have hignition_prod :
      (∏ j : Fin m, matrixFrobSq (cascadeIgnitionMatrix θ h χ j)) ≠ 0 := by
    intro hzero
    exact hχ (by simp [hzero])
  refine ⟨?_⟩
  exact {
    chain := χ
    finalProduct_ne_zero := (matrixFrobSq_ne_zero_iff _).mp hfinal_sq
    ignitionMatrix_ne_zero := by
      intro j
      exact (matrixFrobSq_ne_zero_iff _).mp
        ((Finset.prod_ne_zero_iff.mp hignition_prod) j (Finset.mem_univ j)) }

/-- Noncomputably choose one witnessing chain for a head from its cascade certificate. -/
noncomputable def cascadeChainWitnessOfHeadCertificate {m k d : Nat}
    {θ : Params (m + 1) k d} {h : Fin k}
    (hcert : CascadeHeadCertificate θ h) :
    CascadeChainWitness θ h :=
  Classical.choice (exists_cascadeChainWitness_of_headCertificate hcert)

/-- The chosen chain from a head certificate has nonzero scalar cascade value. -/
theorem cascadeChainWitnessOfHeadCertificate_chainValue_ne_zero {m k d : Nat}
    {θ : Params (m + 1) k d} {h : Fin k}
    (hcert : CascadeHeadCertificate θ h) :
    cascadeChainValue θ h
      (cascadeChainWitnessOfHeadCertificate hcert).chain ≠ 0 :=
  (cascadeChainWitnessOfHeadCertificate hcert).chainValue_ne_zero

/-- Extract Step 1 chain choices for every first-layer head from the cascade certificate. -/
noncomputable def step1ChainChoicesOfCascadeCertificate {m k d : Nat}
    {θ : Params (m + 1) k d} (hcert : CascadeCertificate θ) :
    Step1ChainChoices θ :=
  fun h => cascadeChainWitnessOfHeadCertificate (hcert h)

/-- Each extracted Step 1 chain has nonzero scalar cascade value. -/
theorem step1ChainChoicesOfCascadeCertificate_chainValue_ne_zero {m k d : Nat}
    {θ : Params (m + 1) k d} (hcert : CascadeCertificate θ)
    (h : Fin k) :
    cascadeChainValue θ h
      (step1ChainChoicesOfCascadeCertificate hcert h).chain ≠ 0 :=
  cascadeChainWitnessOfHeadCertificate_chainValue_ne_zero (hcert h)

/-! ## Separated probes -/

/-- Squared Euclidean norm of a finite real vector. -/
def vecNormSq {d : Nat} (x : Vec d) : ℝ :=
  x ⬝ᵥ x

theorem vecNormSq_eq_zero_iff {d : Nat} (x : Vec d) :
    vecNormSq x = 0 ↔ x = 0 := by
  simp [vecNormSq]

theorem vecNormSq_ne_zero_iff {d : Nat} (x : Vec d) :
    vecNormSq x ≠ 0 ↔ x ≠ 0 :=
  not_congr (vecNormSq_eq_zero_iff x)

/-- First-layer probe slope `q'_{1h}(w,v)=w^T A'_{1h}v`, in zero-based Lean indexing. -/
def firstLayerSlope {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (p : ProbePoint d) : ℝ :=
  matrixBilin (attentionMatrix θ 0 h) p.1 p.2

/-- First-layer slopes are all nonzero and pairwise distinct at a probe. -/
def FirstLayerSlopeSeparation {m k d : Nat} (θ : Params (m + 1) k d)
    (p : ProbePoint d) : Prop :=
  (∀ h : Fin k, firstLayerSlope θ h p ≠ 0) ∧
    Function.Injective (fun h : Fin k => firstLayerSlope θ h p)

/-- The selected final residue vector `R^h_L w`. -/
def cascadeResidueVector {m k d : Nat} {θ : Params (m + 1) k d}
    {h : Fin k} (χ : CascadeChainWitness θ h) (p : ProbePoint d) : Vec d :=
  cascadeFinalProduct θ h χ.chain *ᵥ p.1

/-- The selected ignition quadratic value `w^T N^h_j w`. -/
def cascadeIgnitionQuadratic {m k d : Nat} {θ : Params (m + 1) k d}
    {h : Fin k} (χ : CascadeChainWitness θ h) (j : Fin m)
    (p : ProbePoint d) : ℝ :=
  matrixBilin (cascadeIgnitionMatrix θ h χ.chain j) p.1 p.1

/-- All chosen chains ignite at a probe and have nonzero final residue vector. -/
def CascadeProbeIgnition {m k d : Nat} {θ : Params (m + 1) k d}
    (chains : Step1ChainChoices θ) (p : ProbePoint d) : Prop :=
  ∀ h : Fin k,
    cascadeResidueVector (chains h) p ≠ 0 ∧
      ∀ j : Fin m, cascadeIgnitionQuadratic (chains h) j p ≠ 0

/-- Corner slope difference from regularity condition `(R3)`, evaluated at a probe. -/
def cornerSlopeDiffAt {L k d : Nat} (r : Nat) (θ : Params L k d)
    (l : Fin L) (a c : Fin k) (p : ProbePoint d) : ℝ :=
  matrixBilin (attentionMatrix θ l a - attentionMatrix θ l c)
    (cornerKPrefix r θ l.val *ᵥ p.1)
    (cornerCPrefix θ l.val *ᵥ p.2 + cornerDPrefix r θ l.val *ᵥ p.1)

@[simp]
theorem eval_cornerSlopeDiffPoly_at {L k d : Nat} (r : Nat)
    (θ : Params L k d) (l : Fin L) (a c : Fin k) (p : ProbePoint d) :
    MvPolynomial.eval (probePolyEval p.1 p.2)
        (cornerSlopeDiffPoly r θ l a c) =
      cornerSlopeDiffAt r θ l a c p := by
  simp [cornerSlopeDiffAt]

/-- All same-layer corner slope differences are nonzero at a probe. -/
def CornerSlopeSeparationAtProbe {L k d : Nat} (r : Nat)
    (θ : Params L k d) (p : ProbePoint d) : Prop :=
  ∀ l : Fin L, ∀ a c : Fin k, a ≠ c →
    cornerSlopeDiffAt r θ l a c p ≠ 0

/-- The probe-level separation predicate defining `U'_1`. -/
def FirstLayerSeparatedProbe {m k d : Nat} (r : Nat)
    (θ : Params (m + 1) k d) (chains : Step1ChainChoices θ)
    (p : ProbePoint d) : Prop :=
  FirstLayerSlopeSeparation θ p ∧
    CascadeProbeIgnition chains p ∧
      CornerSlopeSeparationAtProbe r θ p

/-- The first-layer separated set `U'_1`. -/
def firstLayerSeparatedSet {m k d : Nat} (r : Nat)
    (θ : Params (m + 1) k d) (chains : Step1ChainChoices θ) :
    Set (ProbePoint d) :=
  {p | FirstLayerSeparatedProbe r θ chains p}

/-- The slope-separation factor `Delta'_sep`, as a real-valued probe function. -/
def firstLayerSlopeSeparationFactor {m k d : Nat}
    (θ : Params (m + 1) k d) (p : ProbePoint d) : ℝ :=
  (∏ h : Fin k, firstLayerSlope θ h p) *
    ∏ ac : OrderedHeadPair k,
      (firstLayerSlope θ ac.1.1 p - firstLayerSlope θ ac.1.2 p)

/-- The cascade factor `Delta'_cas`, as a real-valued probe function. -/
def cascadeProbeFactor {m k d : Nat} {θ : Params (m + 1) k d}
    (chains : Step1ChainChoices θ) (p : ProbePoint d) : ℝ :=
  ∏ h : Fin k,
    (vecNormSq (cascadeResidueVector (chains h) p) *
      ∏ j : Fin m, (cascadeIgnitionQuadratic (chains h) j p) ^ 2)

/-- The corner-separation factor `Delta'_cor`, as a real-valued probe function. -/
def cornerSlopeSeparationFactor {L k d : Nat} (r : Nat)
    (θ : Params L k d) (p : ProbePoint d) : ℝ :=
  ∏ l : Fin L, ∏ ac : OrderedHeadPair k,
    (cornerSlopeDiffAt r θ l ac.1.1 ac.1.2 p) ^ 2

/-- The complete separated-probe product
`Delta'_sep * Delta'_cas * Delta'_cor`. -/
def firstLayerSeparatedFactor {m k d : Nat} (r : Nat)
    (θ : Params (m + 1) k d) (chains : Step1ChainChoices θ)
    (p : ProbePoint d) : ℝ :=
  firstLayerSlopeSeparationFactor θ p *
    cascadeProbeFactor chains p *
      cornerSlopeSeparationFactor r θ p

/-! ### The separated factor as a concrete probe polynomial -/

/-- Squared norm polynomial for a probe-polynomial vector. -/
noncomputable def probeVecNormSqPoly {d : Nat}
    (x : Fin d → ProbePoly d) : ProbePoly d :=
  ∑ i : Fin d, x i * x i

@[simp]
theorem eval_probeVecNormSqPoly {d : Nat} (w v : Vec d)
    (x : Fin d → ProbePoly d) :
    MvPolynomial.eval (probePolyEval w v) (probeVecNormSqPoly x) =
      vecNormSq (fun i => MvPolynomial.eval (probePolyEval w v) (x i)) := by
  simp [probeVecNormSqPoly, vecNormSq, dotProduct]

/-- Probe polynomial for the first-layer slope `w^T A'_{1h}v`. -/
noncomputable def firstLayerSlopePoly {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) : ProbePoly d :=
  probePolyBilin (attentionMatrix θ 0 h) probePolyW probePolyV

@[simp]
theorem eval_firstLayerSlopePoly {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (p : ProbePoint d) :
    MvPolynomial.eval (probePolyEval p.1 p.2) (firstLayerSlopePoly θ h) =
      firstLayerSlope θ h p := by
  simp [firstLayerSlopePoly, firstLayerSlope, matrixBilin]

/-- Probe-polynomial vector for the final cascade residue `R^h_L w`. -/
noncomputable def cascadeResidueVectorPoly {m k d : Nat}
    {θ : Params (m + 1) k d} {h : Fin k}
    (χ : CascadeChainWitness θ h) : Fin d → ProbePoly d :=
  realMatrixToProbePoly (cascadeFinalProduct θ h χ.chain) *ᵥ probePolyW

@[simp]
theorem eval_cascadeResidueVectorPoly {m k d : Nat}
    {θ : Params (m + 1) k d} {h : Fin k}
    (χ : CascadeChainWitness θ h) (p : ProbePoint d) :
    (fun i => MvPolynomial.eval (probePolyEval p.1 p.2)
        (cascadeResidueVectorPoly χ i)) =
      cascadeResidueVector χ p := by
  rw [cascadeResidueVectorPoly, cascadeResidueVector]
  trans
      (realMatrixToProbePoly (cascadeFinalProduct θ h χ.chain)).map
          (MvPolynomial.eval (probePolyEval p.1 p.2)) *ᵥ
        (fun i => MvPolynomial.eval (probePolyEval p.1 p.2) (probePolyW i))
  · exact probePoly_eval_mulVec (probePolyEval p.1 p.2)
      (realMatrixToProbePoly (cascadeFinalProduct θ h χ.chain)) probePolyW
  · simp

/-- Probe polynomial for `||R^h_L w||^2`. -/
noncomputable def cascadeResidueNormSqPoly {m k d : Nat}
    {θ : Params (m + 1) k d} {h : Fin k}
    (χ : CascadeChainWitness θ h) : ProbePoly d :=
  probeVecNormSqPoly (cascadeResidueVectorPoly χ)

@[simp]
theorem eval_cascadeResidueNormSqPoly {m k d : Nat}
    {θ : Params (m + 1) k d} {h : Fin k}
    (χ : CascadeChainWitness θ h) (p : ProbePoint d) :
    MvPolynomial.eval (probePolyEval p.1 p.2)
        (cascadeResidueNormSqPoly χ) =
      vecNormSq (cascadeResidueVector χ p) := by
  simp [cascadeResidueNormSqPoly]

/-- Probe polynomial for the selected ignition quadratic `w^T N^h_j w`. -/
noncomputable def cascadeIgnitionQuadraticPoly {m k d : Nat}
    {θ : Params (m + 1) k d} {h : Fin k}
    (χ : CascadeChainWitness θ h) (j : Fin m) : ProbePoly d :=
  probePolyBilin (cascadeIgnitionMatrix θ h χ.chain j) probePolyW probePolyW

@[simp]
theorem eval_cascadeIgnitionQuadraticPoly {m k d : Nat}
    {θ : Params (m + 1) k d} {h : Fin k}
    (χ : CascadeChainWitness θ h) (j : Fin m) (p : ProbePoint d) :
    MvPolynomial.eval (probePolyEval p.1 p.2)
        (cascadeIgnitionQuadraticPoly χ j) =
      cascadeIgnitionQuadratic χ j p := by
  simp [cascadeIgnitionQuadraticPoly, cascadeIgnitionQuadratic, matrixBilin]

/-- The separated-probe product as a concrete polynomial in `(w,v)`. -/
noncomputable def firstLayerSeparatedPolynomial {m k d : Nat} (r : Nat)
    (θ : Params (m + 1) k d) (chains : Step1ChainChoices θ) :
    ProbePoly d :=
  ((∏ h : Fin k, firstLayerSlopePoly θ h) *
    ∏ ac : OrderedHeadPair k,
      (firstLayerSlopePoly θ ac.1.1 - firstLayerSlopePoly θ ac.1.2)) *
    (∏ h : Fin k,
      (cascadeResidueNormSqPoly (chains h) *
        ∏ j : Fin m, (cascadeIgnitionQuadraticPoly (chains h) j) ^ 2)) *
      ∏ l : Fin (m + 1), ∏ ac : OrderedHeadPair k,
        (cornerSlopeDiffPoly r θ l ac.1.1 ac.1.2) ^ 2

@[simp]
theorem eval_firstLayerSeparatedPolynomial {m k d : Nat} (r : Nat)
    (θ : Params (m + 1) k d) (chains : Step1ChainChoices θ)
    (p : ProbePoint d) :
    MvPolynomial.eval (probePolyEval p.1 p.2)
        (firstLayerSeparatedPolynomial r θ chains) =
      firstLayerSeparatedFactor r θ chains p := by
  simp only [firstLayerSeparatedPolynomial, firstLayerSeparatedFactor,
    firstLayerSlopeSeparationFactor, cascadeProbeFactor,
    cornerSlopeSeparationFactor, map_mul, map_prod, map_pow, map_sub,
    eval_firstLayerSlopePoly, eval_cascadeResidueNormSqPoly,
    eval_cascadeIgnitionQuadraticPoly, eval_cornerSlopeDiffPoly_at]

private theorem exists_matrix_entry_ne_zero {d : Nat}
    {A : Matrix (Fin d) (Fin d) ℝ} (hA : A ≠ 0) :
    ∃ i j : Fin d, A i j ≠ 0 := by
  classical
  by_contra hnone
  apply hA
  ext i j
  by_contra hij
  exact hnone ⟨i, j, hij⟩

private theorem matrixBilin_single_single {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) :
    matrixBilin A (Pi.single i 1) (Pi.single j 1) = A i j := by
  classical
  simp [matrixBilin]

private theorem probePolyBilin_ne_zero_of_matrix_ne_zero {d : Nat}
    {A : Matrix (Fin d) (Fin d) ℝ} (hA : A ≠ 0) :
    probePolyBilin A probePolyW probePolyV ≠ 0 := by
  rcases exists_matrix_entry_ne_zero hA with ⟨i, j, hij⟩
  exact (probePoly_ne_zero_iff_exists_eval_ne_zero
    (probePolyBilin A probePolyW probePolyV)).mpr
      ⟨Pi.single i 1, Pi.single j 1, by
        simpa [matrixBilin_single_single] using hij⟩

private theorem probeVecNormSqMulVecPoly_ne_zero_of_matrix_ne_zero {d : Nat}
    {A : Matrix (Fin d) (Fin d) ℝ} (hA : A ≠ 0) :
    probeVecNormSqPoly (realMatrixToProbePoly A *ᵥ probePolyW) ≠ 0 := by
  rcases exists_matrix_entry_ne_zero hA with ⟨i, j, hij⟩
  refine (probePoly_ne_zero_iff_exists_eval_ne_zero
    (probeVecNormSqPoly (realMatrixToProbePoly A *ᵥ probePolyW))).mpr ?_
  refine ⟨Pi.single j 1, 0, ?_⟩
  have hvec : A *ᵥ Pi.single j (1 : ℝ) ≠ 0 := by
    intro hzero
    have hi := congr_fun hzero i
    rw [Matrix.mulVec_single_one, Matrix.col_apply] at hi
    exact hij hi
  have hnorm : vecNormSq (A.col j) ≠ 0 := by
    simpa [Matrix.mulVec_single_one] using (vecNormSq_ne_zero_iff _).mpr hvec
  have heval :
      MvPolynomial.eval (probePolyEval (Pi.single j 1) 0)
          (probeVecNormSqPoly (realMatrixToProbePoly A *ᵥ probePolyW)) =
        vecNormSq (A.col j) := by
    calc
      MvPolynomial.eval (probePolyEval (Pi.single j 1) 0)
          (probeVecNormSqPoly (realMatrixToProbePoly A *ᵥ probePolyW)) =
          vecNormSq (A *ᵥ Pi.single j (1 : ℝ)) := by
        simp [probeVecNormSqPoly, vecNormSq, dotProduct, Matrix.mulVec,
          realMatrixToProbePoly]
      _ = vecNormSq (A.col j) := by
        rw [Matrix.mulVec_single_one]
  rw [heval]
  exact hnorm

private theorem probePolyQuadratic_ne_zero_of_symmetric_matrix_ne_zero {d : Nat}
    {A : Matrix (Fin d) (Fin d) ℝ} (hA_sym : Aᵀ = A) (hA : A ≠ 0) :
    probePolyBilin A probePolyW probePolyW ≠ 0 := by
  intro hpoly
  apply hA
  have hquad : ∀ w : Vec d, w ⬝ᵥ (A *ᵥ w) = 0 := by
    intro w
    have hw :
        MvPolynomial.eval (probePolyEval w 0)
          (probePolyBilin A probePolyW probePolyW) = 0 := by
      simp [hpoly]
    calc
      w ⬝ᵥ (A *ᵥ w) =
          MvPolynomial.eval (probePolyEval w 0)
            (probePolyBilin A probePolyW probePolyW) := by
        simp [probePolyBilin, realMatrixToProbePoly, Matrix.mulVec, dotProduct]
      _ = 0 := hw
  have hsym_zero :
      A + Aᵀ = 0 :=
    TransformerIdentifiability.NLayer.matrix_symPart_eq_zero_of_forall_quadratic_eq_zero
      hquad
  ext i j
  have hij := congr_fun (congr_fun hsym_zero i) j
  have htranspose : Aᵀ i j = A i j := by rw [hA_sym]
  rw [Matrix.add_apply, htranspose, Matrix.zero_apply] at hij
  have htwo : (2 : ℝ) * A i j = 0 := by linarith
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

theorem firstLayerSlopePoly_ne_zero_of_regular {m k d : Nat}
    {r : Nat} {θ : Params (m + 1) k d}
    (hθ : Regularity r θ) (h : Fin k) :
    firstLayerSlopePoly θ h ≠ 0 := by
  exact probePolyBilin_ne_zero_of_matrix_ne_zero
    (show attentionMatrix θ 0 h ≠ 0 by
      intro hzero
      exact (Regularity.symAttentionMatrix_ne_zero hθ 0 h) (by simp [hzero, sym]))

theorem firstLayerSlopeDiffPoly_ne_zero_of_regular {m k d : Nat}
    {r : Nat} {θ : Params (m + 1) k d}
    (hθ : Regularity r θ) (ac : OrderedHeadPair k) :
    firstLayerSlopePoly θ ac.1.1 - firstLayerSlopePoly θ ac.1.2 ≠ 0 := by
  intro hpoly
  have hmat_ne :
      attentionMatrix θ 0 ac.1.1 - attentionMatrix θ 0 ac.1.2 ≠ 0 :=
    (matrixFrobSq_ne_zero_iff _).mp
      (hθ.head_separation 0 ac.1.1 ac.1.2 (ne_of_lt ac.2))
  apply hmat_ne
  ext i j
  have hval := congr_arg
    (fun P : ProbePoly d =>
      MvPolynomial.eval (probePolyEval (Pi.single i 1) (Pi.single j 1)) P)
    hpoly
  simp [firstLayerSlopePoly] at hval
  simpa [Matrix.sub_apply] using hval

theorem cascadeResidueNormSqPoly_ne_zero {m k d : Nat}
    {θ : Params (m + 1) k d} {h : Fin k}
    (χ : CascadeChainWitness θ h) :
    cascadeResidueNormSqPoly χ ≠ 0 := by
  rw [cascadeResidueNormSqPoly, cascadeResidueVectorPoly]
  exact probeVecNormSqMulVecPoly_ne_zero_of_matrix_ne_zero χ.finalProduct_ne_zero

theorem cascadeIgnitionQuadraticPoly_ne_zero {m k d : Nat}
    {θ : Params (m + 1) k d} {h : Fin k}
    (χ : CascadeChainWitness θ h) (j : Fin m) :
    cascadeIgnitionQuadraticPoly χ j ≠ 0 := by
  exact probePolyQuadratic_ne_zero_of_symmetric_matrix_ne_zero
    (by simp [cascadeIgnitionMatrix])
    (χ.ignitionMatrix_ne_zero j)

theorem cornerSlopeDiffPoly_ne_zero_of_regular_ordered {m k d : Nat}
    {r : Nat} {θ : Params (m + 1) k d}
    (hθ : Regularity r θ) (l : Fin (m + 1)) (ac : OrderedHeadPair k) :
    cornerSlopeDiffPoly r θ l ac.1.1 ac.1.2 ≠ 0 :=
  hθ.corner_slope_separation l ac.1.1 ac.1.2 (ne_of_lt ac.2)

theorem firstLayerSeparatedPolynomial_ne_zero_of_regular {m k d : Nat}
    {r : Nat} {θ : Params (m + 1) k d}
    (hθ : Regularity r θ) (chains : Step1ChainChoices θ) :
    firstLayerSeparatedPolynomial r θ chains ≠ 0 := by
  classical
  rw [firstLayerSeparatedPolynomial]
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
  · refine mul_ne_zero ?_ ?_
    · exact Finset.prod_ne_zero_iff.mpr (by
        intro h _hh
        exact firstLayerSlopePoly_ne_zero_of_regular hθ h)
    · exact Finset.prod_ne_zero_iff.mpr (by
        intro ac _hac
        exact firstLayerSlopeDiffPoly_ne_zero_of_regular hθ ac)
  · exact Finset.prod_ne_zero_iff.mpr (by
      intro h _hh
      exact mul_ne_zero
        (cascadeResidueNormSqPoly_ne_zero (chains h))
        (Finset.prod_ne_zero_iff.mpr (by
          intro j _hj
          exact pow_ne_zero 2 (cascadeIgnitionQuadraticPoly_ne_zero (chains h) j))))
  · exact Finset.prod_ne_zero_iff.mpr (by
      intro l _hl
      exact Finset.prod_ne_zero_iff.mpr (by
        intro ac _hac
        exact pow_ne_zero 2
          (cornerSlopeDiffPoly_ne_zero_of_regular_ordered hθ l ac)))

theorem firstLayerSlopeSeparationFactor_ne_zero_of {m k d : Nat}
    {θ : Params (m + 1) k d} {p : ProbePoint d}
    (hsep : FirstLayerSlopeSeparation θ p) :
    firstLayerSlopeSeparationFactor θ p ≠ 0 := by
  classical
  rw [firstLayerSlopeSeparationFactor]
  exact mul_ne_zero
    (Finset.prod_ne_zero_iff.mpr (by
      intro h _hh
      exact hsep.1 h))
    (Finset.prod_ne_zero_iff.mpr (by
      intro ac _hac
      exact sub_ne_zero.mpr (by
        intro heq
        exact (ne_of_lt ac.2) (hsep.2 heq))))

theorem cascadeProbeFactor_ne_zero_of {m k d : Nat}
    {θ : Params (m + 1) k d} {chains : Step1ChainChoices θ}
    {p : ProbePoint d} (hcas : CascadeProbeIgnition chains p) :
    cascadeProbeFactor chains p ≠ 0 := by
  classical
  rw [cascadeProbeFactor]
  exact Finset.prod_ne_zero_iff.mpr (by
    intro h _hh
    exact mul_ne_zero
      ((vecNormSq_ne_zero_iff _).mpr (hcas h).1)
      (Finset.prod_ne_zero_iff.mpr (by
        intro j _hj
        exact pow_ne_zero 2 ((hcas h).2 j))))

theorem cornerSlopeSeparationFactor_ne_zero_of {L k d : Nat}
    {r : Nat} {θ : Params L k d} {p : ProbePoint d}
    (hcor : CornerSlopeSeparationAtProbe r θ p) :
    cornerSlopeSeparationFactor r θ p ≠ 0 := by
  classical
  rw [cornerSlopeSeparationFactor]
  exact Finset.prod_ne_zero_iff.mpr (by
    intro l _hl
    exact Finset.prod_ne_zero_iff.mpr (by
      intro ac _hac
      exact pow_ne_zero 2 (hcor l ac.1.1 ac.1.2 (ne_of_lt ac.2))))

/-- Membership in `U'_1` implies nonvanishing of the displayed product. -/
theorem firstLayerSeparatedFactor_ne_zero_of_mem {m k d : Nat}
    {r : Nat} {θ : Params (m + 1) k d} {chains : Step1ChainChoices θ}
    {p : ProbePoint d} (hp : p ∈ firstLayerSeparatedSet r θ chains) :
    firstLayerSeparatedFactor r θ chains p ≠ 0 := by
  rcases hp with ⟨hsep, hcas, hcor⟩
  rw [firstLayerSeparatedFactor]
  exact mul_ne_zero
    (mul_ne_zero (firstLayerSlopeSeparationFactor_ne_zero_of hsep)
      (cascadeProbeFactor_ne_zero_of hcas))
    (cornerSlopeSeparationFactor_ne_zero_of hcor)

theorem firstLayerSlopeSeparation_of_factor_ne_zero {m k d : Nat}
    {θ : Params (m + 1) k d} {p : ProbePoint d}
    (hfactor : firstLayerSlopeSeparationFactor θ p ≠ 0) :
    FirstLayerSlopeSeparation θ p := by
  classical
  rw [firstLayerSlopeSeparationFactor] at hfactor
  have hslopes :
      (∏ h : Fin k, firstLayerSlope θ h p) ≠ 0 := by
    intro hzero
    exact hfactor (by simp [hzero])
  have hpairs :
      (∏ ac : OrderedHeadPair k,
        (firstLayerSlope θ ac.1.1 p - firstLayerSlope θ ac.1.2 p)) ≠ 0 := by
    intro hzero
    exact hfactor (by simp [hzero])
  refine ⟨?_, ?_⟩
  · intro h
    exact (Finset.prod_ne_zero_iff.mp hslopes) h (Finset.mem_univ h)
  · intro a c heq
    by_contra hac
    rcases lt_or_gt_of_ne hac with hac_lt | hca_lt
    · let ac : OrderedHeadPair k := ⟨(a, c), hac_lt⟩
      have hdiff :
          firstLayerSlope θ ac.1.1 p - firstLayerSlope θ ac.1.2 p ≠ 0 :=
        (Finset.prod_ne_zero_iff.mp hpairs) ac (Finset.mem_univ ac)
      exact hdiff (by simpa [ac] using sub_eq_zero.mpr heq)
    · let ac : OrderedHeadPair k := ⟨(c, a), hca_lt⟩
      have hdiff :
          firstLayerSlope θ ac.1.1 p - firstLayerSlope θ ac.1.2 p ≠ 0 :=
        (Finset.prod_ne_zero_iff.mp hpairs) ac (Finset.mem_univ ac)
      exact hdiff (by simpa [ac] using sub_eq_zero.mpr heq.symm)

theorem cascadeProbeIgnition_of_factor_ne_zero {m k d : Nat}
    {θ : Params (m + 1) k d} {chains : Step1ChainChoices θ}
    {p : ProbePoint d} (hfactor : cascadeProbeFactor chains p ≠ 0) :
    CascadeProbeIgnition chains p := by
  classical
  rw [cascadeProbeFactor] at hfactor
  intro h
  have hhead :
      vecNormSq (cascadeResidueVector (chains h) p) *
        ∏ j : Fin m, (cascadeIgnitionQuadratic (chains h) j p) ^ 2 ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hfactor) h (Finset.mem_univ h)
  have hres_sq : vecNormSq (cascadeResidueVector (chains h) p) ≠ 0 := by
    intro hzero
    exact hhead (by simp [hzero])
  have hignition_prod :
      (∏ j : Fin m, (cascadeIgnitionQuadratic (chains h) j p) ^ 2) ≠ 0 := by
    intro hzero
    exact hhead (by simp [hzero])
  refine ⟨(vecNormSq_ne_zero_iff _).mp hres_sq, ?_⟩
  intro j
  have hpow :
      (cascadeIgnitionQuadratic (chains h) j p) ^ 2 ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hignition_prod) j (Finset.mem_univ j)
  intro hzero
  exact hpow (by simp [hzero])

theorem cornerSlopeSeparationAtProbe_of_factor_ne_zero {L k d : Nat}
    {r : Nat} {θ : Params L k d} {p : ProbePoint d}
    (hfactor : cornerSlopeSeparationFactor r θ p ≠ 0) :
    CornerSlopeSeparationAtProbe r θ p := by
  classical
  rw [cornerSlopeSeparationFactor] at hfactor
  intro l a c hac
  have hlayer :
      (∏ ac : OrderedHeadPair k,
        (cornerSlopeDiffAt r θ l ac.1.1 ac.1.2 p) ^ 2) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hfactor) l (Finset.mem_univ l)
  rcases lt_or_gt_of_ne hac with hac_lt | hca_lt
  · let ac : OrderedHeadPair k := ⟨(a, c), hac_lt⟩
    have hpow : (cornerSlopeDiffAt r θ l ac.1.1 ac.1.2 p) ^ 2 ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hlayer) ac (Finset.mem_univ ac)
    intro hzero
    exact hpow (by simp [ac, hzero])
  · let ac : OrderedHeadPair k := ⟨(c, a), hca_lt⟩
    have hpow : (cornerSlopeDiffAt r θ l ac.1.1 ac.1.2 p) ^ 2 ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hlayer) ac (Finset.mem_univ ac)
    have hswap :
        cornerSlopeDiffAt r θ l c a p = -cornerSlopeDiffAt r θ l a c p := by
      have hmat :
          attentionMatrix θ l c - attentionMatrix θ l a =
            -(attentionMatrix θ l a - attentionMatrix θ l c) := by
        ext i j
        simp
      change
        matrixBilin (attentionMatrix θ l c - attentionMatrix θ l a)
            (cornerKPrefix r θ l.val *ᵥ p.1)
            (cornerCPrefix θ l.val *ᵥ p.2 + cornerDPrefix r θ l.val *ᵥ p.1) =
          -matrixBilin (attentionMatrix θ l a - attentionMatrix θ l c)
            (cornerKPrefix r θ l.val *ᵥ p.1)
            (cornerCPrefix θ l.val *ᵥ p.2 + cornerDPrefix r θ l.val *ᵥ p.1)
      rw [hmat]
      rw [matrixBilin, Matrix.neg_mulVec, dotProduct_neg]
      rfl
    intro hzero
    exact hpow (by simp [ac, hswap, hzero])

/-- The displayed separated factor is nonzero exactly on `U'_1`. -/
theorem firstLayerSeparatedFactor_ne_zero_iff_mem {m k d : Nat}
    {r : Nat} {θ : Params (m + 1) k d} {chains : Step1ChainChoices θ}
    {p : ProbePoint d} :
    firstLayerSeparatedFactor r θ chains p ≠ 0 ↔
      p ∈ firstLayerSeparatedSet r θ chains := by
  constructor
  · intro hfactor
    have hsep_factor : firstLayerSlopeSeparationFactor θ p ≠ 0 := by
      intro hzero
      exact hfactor (by simp [firstLayerSeparatedFactor, hzero])
    have hcas_factor : cascadeProbeFactor chains p ≠ 0 := by
      intro hzero
      exact hfactor (by simp [firstLayerSeparatedFactor, hzero])
    have hcor_factor : cornerSlopeSeparationFactor r θ p ≠ 0 := by
      intro hzero
      exact hfactor (by simp [firstLayerSeparatedFactor, hzero])
    exact ⟨firstLayerSlopeSeparation_of_factor_ne_zero hsep_factor,
      cascadeProbeIgnition_of_factor_ne_zero hcas_factor,
      cornerSlopeSeparationAtProbe_of_factor_ne_zero hcor_factor⟩
  · exact firstLayerSeparatedFactor_ne_zero_of_mem

theorem continuous_probePolyEval {d : Nat} :
    Continuous (fun p : ProbePoint d => probePolyEval p.1 p.2) := by
  refine continuous_pi ?_
  intro x
  cases x with
  | inl i => exact (continuous_apply i).comp continuous_fst
  | inr i => exact (continuous_apply i).comp continuous_snd

theorem continuous_eval_probePoly {d : Nat} (P : ProbePoly d) :
    Continuous fun p : ProbePoint d =>
      MvPolynomial.eval (probePolyEval p.1 p.2) P :=
  (MvPolynomial.continuous_eval P).comp continuous_probePolyEval

/-- Coordinate homeomorphism between probe points `(w,v)` and probe-polynomial
assignments. -/
def probePointFlatHomeomorph (d : Nat) :
    ProbePoint d ≃ₜ (ProbeVar d → ℝ) where
  toFun := fun p => probePolyEval p.1 p.2
  invFun := fun ρ => (fun i => ρ (Sum.inl i), fun i => ρ (Sum.inr i))
  left_inv := by
    intro p
    rcases p with ⟨w, v⟩
    rfl
  right_inv := by
    intro ρ
    funext x
    cases x <;> rfl
  continuous_toFun := continuous_probePolyEval
  continuous_invFun := by
    refine Continuous.prodMk ?_ ?_
    · refine continuous_pi ?_
      intro i
      exact continuous_apply (Sum.inl i)
    · refine continuous_pi ?_
      intro i
      exact continuous_apply (Sum.inr i)

/-- A nonzero probe polynomial has dense nonvanishing locus in probe space. -/
theorem dense_probePoly_eval_ne_zero {d : Nat} {P : ProbePoly d}
    (hP : P ≠ 0) :
    Dense {p : ProbePoint d |
      MvPolynomial.eval (probePolyEval p.1 p.2) P ≠ 0} := by
  simpa [probePointFlatHomeomorph] using
    (dense_compl_zero_set P hP).preimage
      (probePointFlatHomeomorph d).isOpenMap

theorem continuous_firstLayerSlope {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) :
    Continuous fun p : ProbePoint d => firstLayerSlope θ h p := by
  unfold firstLayerSlope
  exact continuous_matrixBilin (attentionMatrix θ 0 h) continuous_fst continuous_snd

theorem continuous_cascadeResidueVector {m k d : Nat}
    {θ : Params (m + 1) k d} {h : Fin k}
    (χ : CascadeChainWitness θ h) :
    Continuous fun p : ProbePoint d => cascadeResidueVector χ p := by
  unfold cascadeResidueVector
  fun_prop

theorem continuous_vecNormSq {d : Nat} :
    Continuous fun x : Vec d => vecNormSq x := by
  unfold vecNormSq
  fun_prop

theorem continuous_cascadeIgnitionQuadratic {m k d : Nat}
    {θ : Params (m + 1) k d} {h : Fin k}
    (χ : CascadeChainWitness θ h) (j : Fin m) :
    Continuous fun p : ProbePoint d => cascadeIgnitionQuadratic χ j p := by
  unfold cascadeIgnitionQuadratic
  exact continuous_matrixBilin (cascadeIgnitionMatrix θ h χ.chain j)
    continuous_fst continuous_fst

theorem continuous_cornerSlopeDiffAt {L k d : Nat} (r : Nat)
    (θ : Params L k d) (l : Fin L) (a c : Fin k) :
    Continuous fun p : ProbePoint d => cornerSlopeDiffAt r θ l a c p := by
  unfold cornerSlopeDiffAt
  apply continuous_matrixBilin
  · fun_prop
  · fun_prop

theorem continuous_firstLayerSeparatedFactor {m k d : Nat} (r : Nat)
    (θ : Params (m + 1) k d) (chains : Step1ChainChoices θ) :
    Continuous fun p : ProbePoint d => firstLayerSeparatedFactor r θ chains p := by
  unfold firstLayerSeparatedFactor firstLayerSlopeSeparationFactor cascadeProbeFactor
    cornerSlopeSeparationFactor
  refine Continuous.mul (Continuous.mul ?_ ?_) ?_
  · refine Continuous.mul ?_ ?_
    · exact continuous_finsetProd (Finset.univ : Finset (Fin k)) (fun h _ =>
        continuous_firstLayerSlope θ h)
    · exact continuous_finsetProd (Finset.univ : Finset (OrderedHeadPair k)) (fun ac _ =>
        (continuous_firstLayerSlope θ ac.1.1).sub
          (continuous_firstLayerSlope θ ac.1.2))
  · exact continuous_finsetProd (Finset.univ : Finset (Fin k)) (fun h _ =>
      (continuous_vecNormSq.comp (continuous_cascadeResidueVector (chains h))).mul
        (continuous_finsetProd (Finset.univ : Finset (Fin m)) (fun j _ =>
          (continuous_cascadeIgnitionQuadratic (chains h) j).pow 2)))
  · exact continuous_finsetProd (Finset.univ : Finset (Fin (m + 1))) (fun l _ =>
      continuous_finsetProd (Finset.univ : Finset (OrderedHeadPair k)) (fun ac _ =>
        (continuous_cornerSlopeDiffAt r θ l ac.1.1 ac.1.2).pow 2))

theorem isOpen_firstLayerSeparatedSet {m k d : Nat} (r : Nat)
    (θ : Params (m + 1) k d) (chains : Step1ChainChoices θ) :
    IsOpen (firstLayerSeparatedSet r θ chains) := by
  have hopen : IsOpen
      {p : ProbePoint d | firstLayerSeparatedFactor r θ chains p ≠ 0} :=
    (continuous_firstLayerSeparatedFactor r θ chains).isOpen_preimage
      {x : ℝ | x ≠ 0} isOpen_ne
  have hset :
      {p : ProbePoint d | firstLayerSeparatedFactor r θ chains p ≠ 0} =
        firstLayerSeparatedSet r θ chains := by
    ext p
    exact firstLayerSeparatedFactor_ne_zero_iff_mem
  simpa [hset] using hopen

/-- Inline Zariski-density notion for probe polynomials in `(w,v)`. -/
def ZariskiDenseProbeSet {d : Nat} (U : Set (ProbePoint d)) : Prop :=
  ∀ P : ProbePoly d,
    (∀ p : ProbePoint d, p ∈ U →
      MvPolynomial.eval (probePolyEval p.1 p.2) P = 0) →
        P = 0

theorem zariskiDenseProbeSet_of_dense {d : Nat} {U : Set (ProbePoint d)}
    (hU : Dense U) :
    ZariskiDenseProbeSet U := by
  intro P hP
  apply MvPolynomial.funext
  intro ρ
  let p : ProbePoint d :=
    (fun i => ρ (Sum.inl i), fun i => ρ (Sum.inr i))
  have hclosed :
      IsClosed {p : ProbePoint d |
        MvPolynomial.eval (probePolyEval p.1 p.2) P = 0} :=
    isClosed_singleton.preimage (continuous_eval_probePoly P)
  have hsubset :
      U ⊆ {p : ProbePoint d |
        MvPolynomial.eval (probePolyEval p.1 p.2) P = 0} := by
    intro p hp
    exact hP p hp
  have hp_closure : p ∈ closure U := by
    simp [hU.closure_eq]
  have hp_zero :
      MvPolynomial.eval (probePolyEval p.1 p.2) P = 0 :=
    (closure_minimal hsubset hclosed) hp_closure
  have hp_eval : probePolyEval p.1 p.2 = ρ := by
    funext x
    cases x <;> rfl
  simpa [hp_eval] using hp_zero

theorem nonempty_of_dense_probe_set {d : Nat} {U : Set (ProbePoint d)}
    (hU : Dense U) :
    U.Nonempty := by
  rcases hU.inter_open_nonempty Set.univ isOpen_univ
      (show (Set.univ : Set (ProbePoint d)).Nonempty from ⟨(0, 0), trivial⟩) with
    ⟨p, _hp_univ, hpU⟩
  exact ⟨p, hpU⟩

theorem dense_firstLayerSeparatedSet_of_regular {m k d : Nat} {r : Nat}
    {θ : Params (m + 1) k d} (hθ : Regularity r θ)
    (chains : Step1ChainChoices θ) :
    Dense (firstLayerSeparatedSet r θ chains) := by
  have hpoly :
      firstLayerSeparatedPolynomial r θ chains ≠ 0 :=
    firstLayerSeparatedPolynomial_ne_zero_of_regular hθ chains
  have hdense :
      Dense {p : ProbePoint d |
        MvPolynomial.eval (probePolyEval p.1 p.2)
          (firstLayerSeparatedPolynomial r θ chains) ≠ 0} :=
    dense_probePoly_eval_ne_zero hpoly
  have hset :
      {p : ProbePoint d |
        MvPolynomial.eval (probePolyEval p.1 p.2)
          (firstLayerSeparatedPolynomial r θ chains) ≠ 0} =
        firstLayerSeparatedSet r θ chains := by
    ext p
    change
      MvPolynomial.eval (probePolyEval p.1 p.2)
          (firstLayerSeparatedPolynomial r θ chains) ≠ 0 ↔
        p ∈ firstLayerSeparatedSet r θ chains
    rw [eval_firstLayerSeparatedPolynomial,
      firstLayerSeparatedFactor_ne_zero_iff_mem]
  rw [hset] at hdense
  exact hdense

/-- Proposition-valued interface for the polynomial-zero-set conclusions about `U'_1`. -/
structure FirstLayerSeparatedSetProperties {m k d : Nat} (r : Nat)
    (θ : Params (m + 1) k d) (chains : Step1ChainChoices θ) : Prop where
  nonempty : (firstLayerSeparatedSet r θ chains).Nonempty
  isOpen : IsOpen (firstLayerSeparatedSet r θ chains)
  dense : Dense (firstLayerSeparatedSet r θ chains)
  zariski_dense : ZariskiDenseProbeSet (firstLayerSeparatedSet r θ chains)

namespace FirstLayerSeparatedSetProperties

/-- Once density of the separated product nonvanishing locus is available, the rest of
the separated-set topology follows in this file. -/
theorem of_dense {m k d : Nat} {r : Nat}
    {θ : Params (m + 1) k d} {chains : Step1ChainChoices θ}
    (hdense : Dense (firstLayerSeparatedSet r θ chains)) :
    FirstLayerSeparatedSetProperties r θ chains where
  nonempty := nonempty_of_dense_probe_set hdense
  isOpen := isOpen_firstLayerSeparatedSet r θ chains
  dense := hdense
  zariski_dense := zariskiDenseProbeSet_of_dense hdense

end FirstLayerSeparatedSetProperties

/-- The separated-set properties follow from target regularity and the fixed
cascade-chain witnesses. -/
theorem firstLayerSeparatedSetProperties_of_regular {m k d : Nat} {r : Nat}
    {θ : Params (m + 1) k d} (hθ : Regularity r θ)
    (chains : Step1ChainChoices θ) :
    FirstLayerSeparatedSetProperties r θ chains :=
  FirstLayerSeparatedSetProperties.of_dense
    (dense_firstLayerSeparatedSet_of_regular hθ chains)

/-- Concrete downstream package: a dense/open separated set, together with one
chosen separated probe from it. -/
structure FirstLayerSeparatedProbePackage {m k d : Nat} (r : Nat)
    (θ : Params (m + 1) k d) (chains : Step1ChainChoices θ) : Type where
  properties : FirstLayerSeparatedSetProperties r θ chains
  probe : ProbePoint d
  probe_mem : probe ∈ firstLayerSeparatedSet r θ chains

namespace FirstLayerSeparatedProbePackage

theorem separated {m k d : Nat} {r : Nat}
    {θ : Params (m + 1) k d} {chains : Step1ChainChoices θ}
    (P : FirstLayerSeparatedProbePackage r θ chains) :
    FirstLayerSeparatedProbe r θ chains P.probe :=
  P.probe_mem

theorem factor_ne_zero {m k d : Nat} {r : Nat}
    {θ : Params (m + 1) k d} {chains : Step1ChainChoices θ}
    (P : FirstLayerSeparatedProbePackage r θ chains) :
    firstLayerSeparatedFactor r θ chains P.probe ≠ 0 :=
  firstLayerSeparatedFactor_ne_zero_of_mem P.probe_mem

theorem firstLayerSlopeSeparation {m k d : Nat} {r : Nat}
    {θ : Params (m + 1) k d} {chains : Step1ChainChoices θ}
    (P : FirstLayerSeparatedProbePackage r θ chains) :
    FirstLayerSlopeSeparation θ P.probe :=
  P.probe_mem.1

theorem cascadeProbeIgnition {m k d : Nat} {r : Nat}
    {θ : Params (m + 1) k d} {chains : Step1ChainChoices θ}
    (P : FirstLayerSeparatedProbePackage r θ chains) :
    CascadeProbeIgnition chains P.probe :=
  P.probe_mem.2.1

theorem cornerSlopeSeparation {m k d : Nat} {r : Nat}
    {θ : Params (m + 1) k d} {chains : Step1ChainChoices θ}
    (P : FirstLayerSeparatedProbePackage r θ chains) :
    CornerSlopeSeparationAtProbe r θ P.probe :=
  P.probe_mem.2.2

end FirstLayerSeparatedProbePackage

/-- Noncomputably choose a separated probe package from the regularity proof. -/
noncomputable def firstLayerSeparatedProbePackageOfRegular {m k d : Nat}
    {r : Nat} {θ : Params (m + 1) k d} (hθ : Regularity r θ)
    (chains : Step1ChainChoices θ) :
    FirstLayerSeparatedProbePackage r θ chains := by
  let props := firstLayerSeparatedSetProperties_of_regular hθ chains
  exact
    { properties := props
      probe := Classical.choose props.nonempty
      probe_mem := Classical.choose_spec props.nonempty }

/-! ## Step 1 standing setup -/

/-- Standing hypotheses and choices fixed at the start of Step 1 for a depth `m+1`
tail.  The TeX section assumes `L >= 2`; here that is the field `later_depth_pos`. -/
structure Step1StandingHypotheses {m k d : Nat} (r : Nat)
    (θ θ' : Params (m + 1) k d) where
  later_depth_pos : 0 < m
  seq_pos : 0 < r
  target_regular : Regularity r θ'
  target_cascade : CascadeCertificate θ'
  chains : Step1ChainChoices θ'
  global_equality : GlobalTransformerEquality r θ θ'

namespace Step1StandingHypotheses

/-- The probe-output equality bundled by the standing global equality hypothesis. -/
theorem probeOutputEquality {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ') :
    ProbeOutputEquality r θ θ' :=
  probeOutputEquality_of_global H.seq_pos H.global_equality

/-- The separated set attached to the standing target and its chosen chains. -/
def separatedSet {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ') :
    Set (ProbePoint d) :=
  firstLayerSeparatedSet r θ' H.chains

theorem mem_separatedSet_iff {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) :
    p ∈ H.separatedSet ↔ FirstLayerSeparatedProbe r θ' H.chains p :=
  Iff.rfl

theorem separatedSet_properties {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ') :
    FirstLayerSeparatedSetProperties r θ' H.chains :=
  firstLayerSeparatedSetProperties_of_regular H.target_regular H.chains

/-- A concrete separated-probe package attached to the standing target. -/
noncomputable def separatedProbePackage {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ') :
    FirstLayerSeparatedProbePackage r θ' H.chains :=
  firstLayerSeparatedProbePackageOfRegular H.target_regular H.chains

end Step1StandingHypotheses

/-! ## Linear tier bookkeeping -/

/-- First-layer affine pole progression `P(q'_{1h})`. -/
def firstLayerPoleProgression {m k d : Nat} (r : Nat)
    (θ : Params (m + 1) k d) (p : ProbePoint d) (h : Fin k) :
    Set ℂ :=
  affineSigmoidPoleSet (logScale r) (firstLayerSlope θ h p)

/-- The first primed stratum as the union of first-layer affine pole progressions. -/
def firstLayerPrimedStratum {m k d : Nat} (r : Nat)
    (θ : Params (m + 1) k d) (p : ProbePoint d) : Set ℂ :=
  ⋃ h : Fin k, firstLayerPoleProgression r θ p h

/-- Real-part label attached to a first-layer progression. -/
def firstLayerPoleRealPartLabel {m k d : Nat} (r : Nat)
    (θ : Params (m + 1) k d) (p : ProbePoint d) (h : Fin k) : ℝ :=
  -logScale r / firstLayerSlope θ h p

theorem firstLayerPoleProgression_hits_Pi {m k d : Nat} {r : Nat}
    {θ : Params (m + 1) k d} {p : ProbePoint d} {h : Fin k}
    (hslope : firstLayerSlope θ h p ≠ 0) (τ : ℂ) :
    τ ∈ firstLayerPoleProgression r θ p h ↔
      ((firstLayerSlope θ h p : ℂ) * τ + (logScale r : ℂ)) ∈ Pi := by
  exact mem_affineSigmoidPoleSet_iff hslope τ

theorem firstLayerPoleProgression_subset_firstLayerPrimedStratum {m k d : Nat}
    (r : Nat) (θ : Params (m + 1) k d) (p : ProbePoint d) (h : Fin k) :
    firstLayerPoleProgression r θ p h ⊆ firstLayerPrimedStratum r θ p := by
  intro τ hτ
  exact Set.mem_iUnion.2 ⟨h, hτ⟩

theorem firstLayerPoleProgression_re {m k d : Nat} {r : Nat}
    {θ : Params (m + 1) k d} {p : ProbePoint d} {h : Fin k}
    (hslope : firstLayerSlope θ h p ≠ 0) {τ : ℂ}
    (hτ : τ ∈ firstLayerPoleProgression r θ p h) :
    τ.re = firstLayerPoleRealPartLabel r θ p h := by
  rcases hτ with ⟨n, rfl⟩
  exact affineSigmoidPole_re hslope n

/-- Prop-valued result interface for the promoted linear-tier bookkeeping statement. -/
structure LinearTierBookkeepingStatement {m k d : Nat} (r : Nat)
    (θ : Params (m + 1) k d) (p : ProbePoint d) (h : Fin k)
    (firstTier : Set ℂ) : Prop where
  slope_ne_zero : firstLayerSlope θ h p ≠ 0
  firstTier_eq_progression :
    firstTier = firstLayerPoleProgression r θ p h
  firstTier_subset_firstStratum :
    firstTier ⊆ firstLayerPrimedStratum r θ p
  realPart_label :
    ∀ τ : ℂ, τ ∈ firstTier → τ.re = firstLayerPoleRealPartLabel r θ p h

/-- `lem-linear-tier-bookkeeping`: for a separated first-layer head, the first tier is
exactly the affine pole progression, lies in the first stratum, and is labeled by the
real part of any of its points. -/
theorem lem_linear_tier_bookkeeping {m k d : Nat} {r : Nat}
    {θ : Params (m + 1) k d} {p : ProbePoint d} {h : Fin k}
    (hslope : firstLayerSlope θ h p ≠ 0) :
    LinearTierBookkeepingStatement r θ p h
      (firstLayerPoleProgression r θ p h) where
  slope_ne_zero := hslope
  firstTier_eq_progression := rfl
  firstTier_subset_firstStratum :=
    firstLayerPoleProgression_subset_firstLayerPrimedStratum r θ p h
  realPart_label := by
    intro τ hτ
    exact firstLayerPoleProgression_re hslope hτ

/-- Convenience form of linear-tier bookkeeping for a probe already known to be in
the separated set. -/
theorem lem_linear_tier_bookkeeping_of_separated {m k d : Nat} {r : Nat}
    {θ : Params (m + 1) k d} {chains : Step1ChainChoices θ}
    {p : ProbePoint d} {h : Fin k}
    (hp : p ∈ firstLayerSeparatedSet r θ chains) :
    LinearTierBookkeepingStatement r θ p h
      (firstLayerPoleProgression r θ p h) :=
  lem_linear_tier_bookkeeping (hp.1.1 h)

end

end Step1
end TransformerIdentifiability.NLayer.KHead
