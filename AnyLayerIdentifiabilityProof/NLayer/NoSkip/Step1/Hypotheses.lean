import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Genericity.Recursive
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Induction.Invariant

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.NoSkip

/-!
# Target-only Step 1 standing hypotheses

Step 1 is used only above the depth-one base case, hence the parameter depth is
written `n+2`.  This makes the cascade and multi-dial current clauses statically
available from authoritative recursive genericity.
-/

def GlobalTransformerEquality {L k d : Nat} (r : Nat)
    (theta theta' : Params L k d) : Prop :=
  ∀ X : NetworkInput r d, transformer theta X = transformer theta' X

def GlobalProbeOutputEquality {L k d : Nat} (r : Nat)
    (theta theta' : Params L k d) : Prop :=
  ∀ w v : Vec d, ∀ tau : Real, 0 < tau →
    probeOutput r theta w v tau = probeOutput r theta' w v tau

theorem globalProbeOutputEquality_of_transformer {r L k d : Nat}
    (hr : 0 < r) {theta theta' : Params L k d}
    (h : GlobalTransformerEquality r theta theta') :
    GlobalProbeOutputEquality r theta theta' :=
  probeOutput_eq_of_transformerEqualGlobally hr h

/-- Minimal Step 1 assumptions: equality of the pair and genericity of the target only. -/
structure Step1StandingHypotheses {n k d : Nat} (r : Nat)
    (theta theta' : Params (n + 2) k d) : Prop where
  r_pos : 0 < r
  probe_equal : GlobalProbeOutputEquality r theta theta'
  target_generic : RecursiveGeneric r (n + 2) k d theta'

namespace Step1StandingHypotheses

variable {n k d r : Nat} {theta theta' : Params (n + 2) k d}

theorem targetRegularity (H : Step1StandingHypotheses r theta theta') :
    Regularity theta' :=
  H.target_generic.regularity

theorem targetLocalOpenness (H : Step1StandingHypotheses r theta theta') :
    LocalOpenness r theta' :=
  H.target_generic.localOpenness

theorem targetCascadeCertificate (H : Step1StandingHypotheses r theta theta') :
    CascadeCertificate theta' :=
  H.target_generic.cascadeCertificate

theorem targetCascadeSemantics (H : Step1StandingHypotheses r theta theta') :
    CascadeCertificateSemantics theta' :=
  (cascadeCertificate_iff_semantics theta').mp H.targetCascadeCertificate

noncomputable def targetCascadeData (H : Step1StandingHypotheses r theta theta') :
    CascadeCertificateSemanticData theta' :=
  CascadeCertificateSemanticData.ofCertificate H.targetCascadeCertificate

theorem targetHeadwiseDialCertificate (H : Step1StandingHypotheses r theta theta') :
    HeadwiseDialCertificate theta' :=
  H.target_generic.headwiseDialCertificate

theorem targetOnly (H : Step1StandingHypotheses r theta theta') :
    RecursiveGeneric r (n + 2) k d theta' :=
  H.target_generic

end Step1StandingHypotheses

/-! ## NS090: the target separated-probe polynomial -/

/-- Strictly ordered head pairs, used once for every unordered sibling pair. -/
abbrev Step1OrderedHeadPair (k : Nat) :=
  {ac : Fin k × Fin k // ac.1 < ac.2}

/-- First-layer slope factors: nonzero slopes followed by pairwise differences. -/
abbrev Step1SlopeFactorIndex (k : Nat) :=
  Fin k ⊕ Step1OrderedHeadPair k

/-- Selected-chain factors: one final-residue norm per first head and one
ignition quadratic for every `(first head, later layer)`. -/
abbrev Step1CascadeFactorIndex (n k : Nat) :=
  Fin k ⊕ (Fin k × Fin (n + 1))

/-- Complete finite factor family in TeX order: slope separation, selected
cascade data, then all-alpha corner siblings.  The standing parameter depth is
`n+2`, so its later cascade layers are indexed by `Fin (n+1)`. -/
abbrev Step1SeparatedFactorIndex (n k : Nat) :=
  Step1SlopeFactorIndex k ⊕
    (Step1CascadeFactorIndex n k ⊕ (Fin (n + 2) × Step1OrderedHeadPair k))

/-- Target first-layer probe slope `wᵀA'₁h v` as a polynomial in `(w,v)`. -/
noncomputable def step1FirstSlopePoly {m k d : Nat}
    (theta : Params (m + 1) k d) (h : Fin k) : AlphaCornerProbePoly d :=
  alphaCornerProbeBilin (attentionMatrix theta 0 h)
    alphaCornerProbeW alphaCornerProbeV

/-- A selected final-residue vector `P_m^{h,χ}w` over the probe ring. -/
noncomputable def step1CascadeResidueVectorPoly {m k d : Nat}
    {theta : Params (m + 1) k d} (D : CascadeCertificateSemanticData theta)
    (h : Fin k) : Fin d → AlphaCornerProbePoly d :=
  realMatrixToAlphaCornerProbePoly
      (cascadeFinalProduct theta h (D.head h).chain) *ᵥ alphaCornerProbeW

/-- Squared Euclidean norm of a probe-polynomial vector. -/
noncomputable def step1ProbeVecNormSqPoly {d : Nat}
    (x : Fin d → AlphaCornerProbePoly d) : AlphaCornerProbePoly d :=
  ∑ i : Fin d, x i * x i

/-- Selected final-residue nonvanishing factor. -/
noncomputable def step1CascadeResiduePoly {m k d : Nat}
    {theta : Params (m + 1) k d} (D : CascadeCertificateSemanticData theta)
    (h : Fin k) : AlphaCornerProbePoly d :=
  step1ProbeVecNormSqPoly (step1CascadeResidueVectorPoly D h)

/-- Selected ignition quadratic `wᵀM_j^{h,χ}w`. -/
noncomputable def step1CascadeIgnitionPoly {m k d : Nat}
    {theta : Params (m + 1) k d} (D : CascadeCertificateSemanticData theta)
    (h : Fin k) (j : Fin m) : AlphaCornerProbePoly d :=
  alphaCornerProbeBilin
    (cascadeIgnitionMatrix theta h (D.head h).chain j)
    alphaCornerProbeW alphaCornerProbeW

/-- One member of the complete finite separated-probe factor family. -/
noncomputable def step1SeparatedFactorPoly {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') :
    Step1SeparatedFactorIndex n k → AlphaCornerProbePoly d
  | Sum.inl (Sum.inl h) => step1FirstSlopePoly theta' h
  | Sum.inl (Sum.inr ac) =>
      step1FirstSlopePoly theta' ac.1.1 - step1FirstSlopePoly theta' ac.1.2
  | Sum.inr (Sum.inl (Sum.inl h)) =>
      step1CascadeResiduePoly H.targetCascadeData h
  | Sum.inr (Sum.inl (Sum.inr hj)) =>
      (step1CascadeIgnitionPoly H.targetCascadeData hj.1 hj.2) ^ 2
  | Sum.inr (Sum.inr lac) =>
      (alphaCornerSlopeDiffPoly r theta' lac.1 lac.2.1.1 lac.2.1.2) ^ 2

/-- TeX `Δ'_sep Δ'_cas Δ'_cor`, represented as one finite product polynomial. -/
noncomputable def step1SeparatedProbePolynomial {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') : AlphaCornerProbePoly d :=
  ∏ idx : Step1SeparatedFactorIndex n k, step1SeparatedFactorPoly H idx

/-- Pointwise value of one separated factor at a probe pair. -/
noncomputable def step1SeparatedFactorValue {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w v : Vec d) :
    Step1SeparatedFactorIndex n k → Real
  | Sum.inl (Sum.inl h) => matrixBilin (attentionMatrix theta' 0 h) w v
  | Sum.inl (Sum.inr ac) =>
      matrixBilin (attentionMatrix theta' 0 ac.1.1) w v -
        matrixBilin (attentionMatrix theta' 0 ac.1.2) w v
  | Sum.inr (Sum.inl (Sum.inl h)) =>
      let x := cascadeFinalProduct theta' h (H.targetCascadeData.head h).chain *ᵥ w
      dotProduct x x
  | Sum.inr (Sum.inl (Sum.inr hj)) =>
      (matrixBilin
        (cascadeIgnitionMatrix theta' hj.1
          (H.targetCascadeData.head hj.1).chain hj.2) w w) ^ 2
  | Sum.inr (Sum.inr lac) =>
      (alphaCornerSlopeDiff r theta' lac.1 lac.2.1.1 lac.2.1.2 w v) ^ 2

@[simp] theorem eval_step1FirstSlopePoly {m k d : Nat}
    (theta : Params (m + 1) k d) (h : Fin k) (w v : Vec d) :
    MvPolynomial.eval (alphaCornerProbeEval w v) (step1FirstSlopePoly theta h) =
      matrixBilin (attentionMatrix theta 0 h) w v := by
  simp [step1FirstSlopePoly, alphaCornerProbeW, alphaCornerProbeV,
    alphaCornerProbeEval]

@[simp] theorem eval_step1CascadeResidueVectorPoly {m k d : Nat}
    {theta : Params (m + 1) k d} (D : CascadeCertificateSemanticData theta)
    (h : Fin k) (w v : Vec d) :
    (fun i => MvPolynomial.eval (alphaCornerProbeEval w v)
      (step1CascadeResidueVectorPoly D h i)) =
        cascadeFinalProduct theta h (D.head h).chain *ᵥ w := by
  ext i
  simp [step1CascadeResidueVectorPoly, realMatrixToAlphaCornerProbePoly,
    alphaCornerProbeW, alphaCornerProbeEval, Matrix.mulVec, dotProduct]

@[simp] theorem eval_step1ProbeVecNormSqPoly {d : Nat}
    (x : Fin d → AlphaCornerProbePoly d) (w v : Vec d) :
    MvPolynomial.eval (alphaCornerProbeEval w v) (step1ProbeVecNormSqPoly x) =
      dotProduct
        (fun i => MvPolynomial.eval (alphaCornerProbeEval w v) (x i))
        (fun i => MvPolynomial.eval (alphaCornerProbeEval w v) (x i)) := by
  simp [step1ProbeVecNormSqPoly, dotProduct]

@[simp] theorem eval_step1CascadeResiduePoly {m k d : Nat}
    {theta : Params (m + 1) k d} (D : CascadeCertificateSemanticData theta)
    (h : Fin k) (w v : Vec d) :
    MvPolynomial.eval (alphaCornerProbeEval w v) (step1CascadeResiduePoly D h) =
      dotProduct
        (cascadeFinalProduct theta h (D.head h).chain *ᵥ w)
        (cascadeFinalProduct theta h (D.head h).chain *ᵥ w) := by
  simp [step1CascadeResiduePoly]

@[simp] theorem eval_step1CascadeIgnitionPoly {m k d : Nat}
    {theta : Params (m + 1) k d} (D : CascadeCertificateSemanticData theta)
    (h : Fin k) (j : Fin m) (w v : Vec d) :
    MvPolynomial.eval (alphaCornerProbeEval w v)
        (step1CascadeIgnitionPoly D h j) =
      matrixBilin (cascadeIgnitionMatrix theta h (D.head h).chain j) w w := by
  simp [step1CascadeIgnitionPoly, alphaCornerProbeW, alphaCornerProbeEval]

@[simp] theorem eval_step1SeparatedFactorPoly {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (idx : Step1SeparatedFactorIndex n k)
    (w v : Vec d) :
    MvPolynomial.eval (alphaCornerProbeEval w v) (step1SeparatedFactorPoly H idx) =
      step1SeparatedFactorValue H w v idx := by
  rcases idx with idx | idx
  · rcases idx with h | ac
    · simp [step1SeparatedFactorPoly, step1SeparatedFactorValue]
    · simp [step1SeparatedFactorPoly, step1SeparatedFactorValue]
  · rcases idx with idx | lac
    · rcases idx with h | hj
      · simp [step1SeparatedFactorPoly, step1SeparatedFactorValue,
          step1CascadeResiduePoly]
      · simp [step1SeparatedFactorPoly, step1SeparatedFactorValue]
    · simp [step1SeparatedFactorPoly, step1SeparatedFactorValue]

@[simp] theorem eval_step1SeparatedProbePolynomial {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w v : Vec d) :
    MvPolynomial.eval (alphaCornerProbeEval w v) (step1SeparatedProbePolynomial H) =
      ∏ idx : Step1SeparatedFactorIndex n k, step1SeparatedFactorValue H w v idx := by
  simp [step1SeparatedProbePolynomial]

private theorem step1_exists_matrix_entry_ne_zero {d : Nat}
    {A : Matrix (Fin d) (Fin d) Real} (hA : A ≠ 0) :
    ∃ i j : Fin d, A i j ≠ 0 := by
  classical
  by_contra hnone
  apply hA
  ext i j
  by_contra hij
  exact hnone ⟨i, j, hij⟩

private theorem step1_matrixBilin_single_single {d : Nat}
    (A : Matrix (Fin d) (Fin d) Real) (i j : Fin d) :
    matrixBilin A (Pi.single i 1) (Pi.single j 1) = A i j := by
  classical
  simp [matrixBilin]

private theorem step1_bilinPoly_ne_zero_of_matrix_ne_zero {d : Nat}
    {A : Matrix (Fin d) (Fin d) Real} (hA : A ≠ 0) :
    alphaCornerProbeBilin A alphaCornerProbeW alphaCornerProbeV ≠ 0 := by
  rcases step1_exists_matrix_entry_ne_zero hA with ⟨i, j, hij⟩
  apply mvPolynomial_ne_zero_of_eval_ne_zero _
    (alphaCornerProbeEval (Pi.single i 1) (Pi.single j 1))
  simpa [alphaCornerProbeW, alphaCornerProbeV, alphaCornerProbeEval,
    step1_matrixBilin_single_single] using hij

private theorem step1_mulVec_exists_ne_zero_of_matrix_ne_zero {d : Nat}
    {A : Matrix (Fin d) (Fin d) Real} (hA : A ≠ 0) :
    ∃ w : Vec d, A *ᵥ w ≠ 0 := by
  rcases step1_exists_matrix_entry_ne_zero hA with ⟨i, j, hij⟩
  refine ⟨Pi.single j 1, ?_⟩
  intro hzero
  have hi := congr_fun hzero i
  rw [Matrix.mulVec_single_one, Matrix.col_apply] at hi
  exact hij hi

private theorem step1_dotProduct_self_ne_zero {d : Nat} {x : Vec d}
    (hx : x ≠ 0) : dotProduct x x ≠ 0 := by
  simpa using hx

private theorem step1_residuePoly_ne_zero_of_matrix_ne_zero {m k d : Nat}
    {theta : Params (m + 1) k d} (D : CascadeCertificateSemanticData theta)
    (h : Fin k) (hfinal : cascadeFinalProduct theta h (D.head h).chain ≠ 0) :
    step1CascadeResiduePoly D h ≠ 0 := by
  rcases step1_mulVec_exists_ne_zero_of_matrix_ne_zero hfinal with ⟨w, hw⟩
  apply mvPolynomial_ne_zero_of_eval_ne_zero _ (alphaCornerProbeEval w 0)
  rw [eval_step1CascadeResiduePoly]
  exact step1_dotProduct_self_ne_zero hw

private theorem step1_quadraticPoly_ne_zero_of_symmetric_matrix_ne_zero {d : Nat}
    {A : Matrix (Fin d) (Fin d) Real} (hAT : Aᵀ = A) (hA : A ≠ 0) :
    alphaCornerProbeBilin A alphaCornerProbeW alphaCornerProbeW ≠ 0 := by
  intro hpoly
  apply hA
  have hquad : ∀ w : Vec d, dotProduct w (A *ᵥ w) = 0 := by
    intro w
    have hw := congrArg
      (MvPolynomial.eval (alphaCornerProbeEval w 0)) hpoly
    simpa [alphaCornerProbeBilin, matrixBilin,
      realMatrixToAlphaCornerProbePoly, alphaCornerProbeW,
      alphaCornerProbeEval, Matrix.mulVec, dotProduct] using hw
  have hsym : A + Aᵀ = 0 :=
    TransformerIdentifiability.NLayer.matrix_symPart_eq_zero_of_forall_quadratic_eq_zero
      hquad
  ext i j
  have hij := congr_fun (congr_fun hsym i) j
  have htranspose : Aᵀ i j = A i j := by rw [hAT]
  rw [Matrix.add_apply, htranspose, Matrix.zero_apply] at hij
  have htwo : (2 : Real) * A i j = 0 := by linarith
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

theorem step1FirstSlopePoly_ne_zero {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (h : Fin k) :
    step1FirstSlopePoly theta' h ≠ 0 := by
  apply step1_bilinPoly_ne_zero_of_matrix_ne_zero
  intro hzero
  apply H.targetRegularity.attention_sym_ne_zero 0 h
  rw [hzero]
  ext i j
  simp

theorem step1FirstSlopeDiffPoly_ne_zero {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (ac : Step1OrderedHeadPair k) :
    step1FirstSlopePoly theta' ac.1.1 - step1FirstSlopePoly theta' ac.1.2 ≠ 0 := by
  intro hpoly
  have hmat :
      attentionMatrix theta' 0 ac.1.1 - attentionMatrix theta' 0 ac.1.2 ≠ 0 :=
    sub_ne_zero.mpr (fun h => (ne_of_lt ac.2)
      (H.targetRegularity.attention_pairwise 0 h))
  apply hmat
  ext i j
  have hval := congrArg
    (MvPolynomial.eval
      (alphaCornerProbeEval (Pi.single i 1) (Pi.single j 1))) hpoly
  simp [step1FirstSlopePoly, alphaCornerProbeW, alphaCornerProbeV,
    alphaCornerProbeEval] at hval
  simpa [Matrix.sub_apply] using hval

theorem step1CascadeResiduePoly_ne_zero {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (h : Fin k) :
    step1CascadeResiduePoly H.targetCascadeData h ≠ 0 :=
  step1_residuePoly_ne_zero_of_matrix_ne_zero H.targetCascadeData h
    (H.targetCascadeData.head h).semantic.final_residue_ne_zero

theorem step1CascadeIgnitionPoly_ne_zero {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (h : Fin k) (j : Fin (n + 1)) :
    step1CascadeIgnitionPoly H.targetCascadeData h j ≠ 0 := by
  apply step1_quadraticPoly_ne_zero_of_symmetric_matrix_ne_zero
  · simp [cascadeIgnitionMatrix]
  · exact (H.targetCascadeData.head h).semantic.ignition_ne_zero j

/-- Every factor in the separated family is a nonzero polynomial, using only
target regularity and the target-selected cascade data. -/
theorem step1SeparatedFactorPoly_ne_zero {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta')
    (idx : Step1SeparatedFactorIndex n k) :
    step1SeparatedFactorPoly H idx ≠ 0 := by
  rcases idx with idx | idx
  · rcases idx with h | ac
    · exact step1FirstSlopePoly_ne_zero H h
    · exact step1FirstSlopeDiffPoly_ne_zero H ac
  · rcases idx with idx | lac
    · rcases idx with h | hj
      · exact step1CascadeResiduePoly_ne_zero H h
      · exact pow_ne_zero 2 (step1CascadeIgnitionPoly_ne_zero H hj.1 hj.2)
    · exact pow_ne_zero 2
        (H.targetRegularity.alphaCornerSlopeDiffPoly_ne_zero r H.r_pos lac.1
          (ne_of_lt lac.2.2))

/-- NS090 capstone: the finite product defining the target separated set is
not the zero polynomial. -/
theorem step1SeparatedProbePolynomial_ne_zero {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') :
    step1SeparatedProbePolynomial H ≠ 0 := by
  classical
  exact mvPolynomial_finset_prod_ne_zero fun idx _ =>
    step1SeparatedFactorPoly_ne_zero H idx

end TransformerIdentifiability.NLayer.NoSkip
