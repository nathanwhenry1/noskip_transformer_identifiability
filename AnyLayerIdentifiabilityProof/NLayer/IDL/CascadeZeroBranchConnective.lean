import AnyLayerIdentifiabilityProof.NLayer.IDL.CascadeZeroBranch
import AnyLayerIdentifiabilityProof.NLayer.IDL.CascadeBridge

set_option autoImplicit false

open Matrix

namespace TransformerIdentifiability.NLayer

/-!
# R3 zero-branch connective lemmas

This file connects the formal curve-rigidity output of `CascadeCurveRigidityData` to the
real matrix-algebra core in `CascadeZeroBranch`.

The key bridge is head-peeling the formal matrices at a real first gate:
* `formalX_real_head_peel` identifies `formalX` with the TeX `(B₁-zV₁)ᵀY` expression.
* `formalY_real_head_peel` identifies `formalY` with the TeX club expression.
* `cascadeCurveRigidity_gamma_eval_zero_one_of_zeroBranch` extracts `(c0)`, `(c1)`, and
  `(♣)` from `cascadeCurveRigidity_formalX_formalY`, then invokes
  `gammaCoeffs_eq_zero_of_cascadeZeroBranch`.
-/

/-! ## Small `matC` utilities -/

/-- `matC` commutes with transpose. -/
theorem matC_transpose {d : Nat} (M : Matrix (Fin d) (Fin d) ℝ) :
    matC Mᵀ = (matC M)ᵀ := by
  ext i j
  simp [matC, Matrix.transpose_apply]

/-- The real-to-complex matrix embedding is injective. -/
theorem matC_inj {d : Nat} {M N : Matrix (Fin d) (Fin d) ℝ}
    (h : matC M = matC N) : M = N := by
  ext i j
  have hij := congrFun (congrFun h i) j
  exact Complex.ofReal_inj.mp hij

/-- A `matC` equality against a complex scalar multiple gives the real-part scalar
identity over `ℝ`. -/
theorem real_matrix_eq_real_smul_of_matC_eq_smul_matC {d : Nat}
    {M A : Matrix (Fin d) (Fin d) ℝ} {g : ℂ}
    (h : matC M = g • matC A) :
    M = g.re • A := by
  ext i j
  have hij := congrFun (congrFun h i) j
  simpa [matC, Matrix.smul_apply, smul_eq_mul] using congrArg Complex.re hij

/-- If a nonzero real matrix becomes a complex scalar multiple under `matC`, that scalar
is real. -/
theorem complex_scalar_real_of_matC_eq_smul_matC {d : Nat}
    {M A : Matrix (Fin d) (Fin d) ℝ} {g : ℂ}
    (hA : A ≠ 0) (h : matC M = g • matC A) :
    (g.re : ℂ) = g := by
  rcases exists_matrix_entry_ne_zero_of_ne_zero hA with ⟨i, j, hij_ne⟩
  have hij := congrFun (congrFun h i) j
  have him : g.im = 0 ∨ A i j = 0 := by
    simpa [matC, Matrix.smul_apply, smul_eq_mul] using congrArg Complex.im hij
  have hgim : g.im = 0 := by
    rcases him with hg | hA
    · exact hg
    · exact False.elim (hij_ne hA)
  apply Complex.ext
  · simp
  · simp [hgim]

/-- The formal skip product is `matC` of the real skip product. -/
theorem formalBprod_matC {d : Nat} (θ : LayerStream d) (n : Nat) :
    formalBprod θ n = matC (realSkipBprod θ n) := by
  induction n with
  | zero => simp [matC_one]
  | succ n ih =>
      rw [formalBprod_succ, ih, realSkipBprod_succ, ← matC_mul]

/-! ## Head-peeling `formalX` and `formalY` at a real first gate -/

/-- Head-peel `formalX` at a real first gate and real tail gates.

For `level = n + 1`, this is the formal version of
`(B₁-zV₁)ᵀ · ((Γ_tail)ᵀ A_level B_tail B₁)`. -/
theorem formalX_real_head_peel {d : Nat} (θ : LayerStream d)
    (n : Nat) (z : ℝ) (tail : Nat -> ℝ) :
    formalX θ (n + 1) (gateAssignmentOfTail z tail) =
      matC ((skipB (θ 0).1 - z • (θ 0).1)ᵀ *
        (((realW (fun k => θ (k + 1)) tail n)ᵀ * (θ (n + 1)).2 *
            realSkipBprod (fun k => θ (k + 1)) n) *
          skipB (θ 0).1)) := by
  rw [formalX, gateAssignmentOfTail_eq, formalW_matC, formalBprod_matC,
    realW_head_peel, realSkipBprod_head_peel]
  rw [← matC_transpose, Matrix.transpose_mul]
  rw [← matC_mul, ← matC_mul]
  congr 1
  simp [realGateOfTail, mul_assoc]

/-- Head-peel `formalY` at a real first gate and real tail gates.

For `level = n + 1`, this is the formal version of
`(B₁-zV₁)ᵀ · (Γ_tail)ᵀ A_level · (z B_tail V₁ + T_tail(B₁-zV₁))`. -/
theorem formalY_real_head_peel {d : Nat} (θ : LayerStream d)
    (n : Nat) (z : ℝ) (tail : Nat -> ℝ) :
    formalY θ (n + 1) (gateAssignmentOfTail z tail) =
      matC (((skipB (θ 0).1 - z • (θ 0).1)ᵀ *
          ((realW (fun k => θ (k + 1)) tail n)ᵀ * (θ (n + 1)).2)) *
        (z • (realSkipBprod (fun k => θ (k + 1)) n * (θ 0).1)
          + realT (fun k => θ (k + 1)) tail n *
              (skipB (θ 0).1 - z • (θ 0).1))) := by
  rw [formalY, gateAssignmentOfTail_eq, formalW_matC, formalT_matC,
    realW_head_peel, realT_head_peel]
  rw [← matC_transpose, Matrix.transpose_mul]
  rw [← matC_mul, ← matC_mul]
  congr 1
  simp [realGateOfTail, mul_assoc]

/-- A complex antisymmetry identity for `matC M` gives `Sym(M)=0` over `ℝ`. -/
theorem symPart_eq_zero_of_matC_add_transpose_eq_zero {d : Nat}
    {M : Matrix (Fin d) (Fin d) ℝ}
    (h : matC M + (matC M)ᵀ = 0) :
    symPart M = 0 := by
  have hanti : M + Mᵀ = 0 := by
    apply matC_inj
    rw [matC_add, matC_transpose, h, matC_zero]
  rw [symPart, hanti, smul_zero]

/-! ## Connecting curve rigidity to the zero-branch algebra core -/

/-- Product-patch zero-branch constructor for successor levels.

This connective supplies the residual matrices needed by
`cascadeCurveRigidityProvider_of_product_patch_quadratic_zero_branch_of_matrix_ne_zero`
from the real head-peeling identities, with the affine scalar coefficients fixed to zero. -/
noncomputable def cascadeCurveRigidityProvider_of_product_patch_zero_branch_level_succ
    {L d : Nat}
    {θ : Params L d} {A : Matrix (Fin d) (Fin d) ℝ}
    {levelPred : Nat} {tail : Nat → ℝ}
    {U0 : Set (ProbePair d × ℝ)}
    (patch : CoefficientSeparatingProductPatch A U0)
    (hquadratic : QuadricProbeSliceQuadraticCoefficientSeparation A patch.Uq)
    (hA : A ≠ 0)
    (hzero :
      ∀ p : ProbePair d, p ∈ patch.Uq → ∀ t : ℝ, t ∈ patch.J →
        specializedPhi θ (levelPred + 1) (gateAssignmentOfTail t tail) p = 0) :
    CascadeCurveRigidityProvider θ A (levelPred + 1) tail := by
  let η : LayerStream d := paramStream θ
  let M : ℝ → Matrix (Fin d) (Fin d) ℝ := fun t =>
    ((skipB (η 0).1 - t • (η 0).1)ᵀ *
      (((realW (fun k => η (k + 1)) tail levelPred)ᵀ *
        (η (levelPred + 1)).2 *
        realSkipBprod (fun k => η (k + 1)) levelPred) *
        skipB (η 0).1))
  let Yreal : ℝ → Matrix (Fin d) (Fin d) ℝ := fun t =>
    (((skipB (η 0).1 - t • (η 0).1)ᵀ *
        ((realW (fun k => η (k + 1)) tail levelPred)ᵀ *
          (η (levelPred + 1)).2)) *
      (t • (realSkipBprod (fun k => η (k + 1)) levelPred * (η 0).1)
        + realT (fun k => η (k + 1)) tail levelPred *
            (skipB (η 0).1 - t • (η 0).1)))
  let R : ℝ → Matrix (Fin d) (Fin d) ℝ := fun t => Yreal t + (Yreal t)ᵀ
  refine
    cascadeCurveRigidityProvider_of_product_patch_quadratic_zero_branch_of_matrix_ne_zero
      (θ := θ) (A := A) (level := levelPred + 1) (tail := tail)
      patch hquadratic 0 0 M R hA ?_ ?_ hzero
  · intro t ht
    rw [formalX_real_head_peel η levelPred t tail]
    simp [η, M]
  · intro t ht
    rw [formalY_real_head_peel η levelPred t tail]
    rw [matC_add, matC_transpose]

/-- Real coefficient extraction from `CascadeCurveRigidityData`, after head-peeling.

The returned coefficients are `γ(0).re` and `γ(1).re - γ(0).re`, i.e. the affine
coefficient data seen by the real matrix-algebra core. -/
theorem cascadeCurveRigidity_gammaCoeffs_eq_zero_of_zeroBranch {L d : Nat}
    {θ : Params L d} {A1 : Matrix (Fin d) (Fin d) ℝ} {level : Nat}
    {tail : Nat -> ℝ}
    (hd : 0 < d)
    (D : CascadeCurveRigidityData θ A1 (level + 1) tail)
    (hA1det : A1.det ≠ 0)
    (hsymA1 : symPart A1 ≠ 0)
    (hV1 : (paramStream θ 0).1 ≠ 0) :
    (D.gamma 0).re = 0 ∧ (D.gamma 1).re - (D.gamma 0).re = 0 := by
  let η : LayerStream d := paramStream θ
  let V1 : Matrix (Fin d) (Fin d) ℝ := (η 0).1
  let B1 : Matrix (Fin d) (Fin d) ℝ := skipB V1
  let ηtail : LayerStream d := fun k => η (k + 1)
  let Wtail : Matrix (Fin d) (Fin d) ℝ := realW ηtail tail level
  let Bsub : Matrix (Fin d) (Fin d) ℝ := realSkipBprod ηtail level
  let P : Matrix (Fin d) (Fin d) ℝ := Wtailᵀ * (η (level + 1)).2
  let Qt : Matrix (Fin d) (Fin d) ℝ := realT ηtail tail level
  let Y : Matrix (Fin d) (Fin d) ℝ := P * Bsub * B1
  have hB1 : B1 = 1 + V1 := by
    simp [B1, skipB]
  have hY : Y = P * Bsub * B1 := rfl
  have hx0_complex :
      matC (B1ᵀ * Y) = D.gamma 0 • matC A1 := by
    calc
      matC (B1ᵀ * Y) =
          formalX η (level + 1) (gateAssignmentOfTail 0 tail) := by
            rw [formalX_real_head_peel η level 0 tail]
            simp [η, V1, B1, ηtail, Wtail, Bsub, P, Y]
      _ = D.gamma 0 • matC A1 := by
            simpa [η, gateAssignmentOfTail] using
              (cascadeCurveRigidity_formalX_formalY D (0 : ℂ)).1
  have hx1_complex :
      matC ((B1 - V1)ᵀ * Y) = D.gamma 1 • matC A1 := by
    calc
      matC ((B1 - V1)ᵀ * Y) =
          formalX η (level + 1) (gateAssignmentOfTail 1 tail) := by
            rw [formalX_real_head_peel η level 1 tail]
            simp [η, V1, B1, ηtail, Wtail, Bsub, P, Y]
      _ = D.gamma 1 • matC A1 := by
            simpa [η, gateAssignmentOfTail] using
              (cascadeCurveRigidity_formalX_formalY D (1 : ℂ)).1
  have hc0 : B1ᵀ * Y = (D.gamma 0).re • A1 :=
    real_matrix_eq_real_smul_of_matC_eq_smul_matC hx0_complex
  have hx1_real : (B1 - V1)ᵀ * Y = (D.gamma 1).re • A1 :=
    real_matrix_eq_real_smul_of_matC_eq_smul_matC hx1_complex
  have hc1 : V1ᵀ * Y = (-((D.gamma 1).re - (D.gamma 0).re)) • A1 := by
    calc
      V1ᵀ * Y = B1ᵀ * Y - (B1 - V1)ᵀ * Y := by
        rw [Matrix.transpose_sub, sub_mul]
        abel
      _ = (D.gamma 0).re • A1 - (D.gamma 1).re • A1 := by
        rw [hc0, hx1_real]
      _ = (-((D.gamma 1).re - (D.gamma 0).re)) • A1 := by
        rw [← sub_smul]
        congr 1
        ring
  have hclub :
      ∀ z : ℝ,
        symPart ((B1 - z • V1)ᵀ * P *
          (z • (Bsub * V1) + Qt * (B1 - z • V1))) = 0 := by
    intro z
    have hy_complex :
        matC (((B1 - z • V1)ᵀ * P) *
          (z • (Bsub * V1) + Qt * (B1 - z • V1))) +
          (matC (((B1 - z • V1)ᵀ * P) *
            (z • (Bsub * V1) + Qt * (B1 - z • V1))))ᵀ = 0 := by
      calc
        matC (((B1 - z • V1)ᵀ * P) *
            (z • (Bsub * V1) + Qt * (B1 - z • V1))) +
            (matC (((B1 - z • V1)ᵀ * P) *
              (z • (Bsub * V1) + Qt * (B1 - z • V1))))ᵀ =
            formalY η (level + 1) (gateAssignmentOfTail z tail) +
              (formalY η (level + 1) (gateAssignmentOfTail z tail))ᵀ := by
              rw [formalY_real_head_peel η level z tail]
        _ = 0 := by
              simpa [η, gateAssignmentOfTail] using
                (cascadeCurveRigidity_formalX_formalY D (z : ℂ)).2
    simpa only [mul_assoc] using
      symPart_eq_zero_of_matC_add_transpose_eq_zero (M :=
        ((B1 - z • V1)ᵀ * P) *
          (z • (Bsub * V1) + Qt * (B1 - z • V1))) hy_complex
  exact gammaCoeffs_eq_zero_of_cascadeZeroBranch hd A1 V1 B1 P Bsub Qt Y
    (D.gamma 0).re ((D.gamma 1).re - (D.gamma 0).re)
    hB1 hY hc0 hc1 hclub hA1det hsymA1 hV1

/-- Wrapper form: the zero-branch curve-rigidity scalar vanishes at `0` and `1`.

The generic/depth inputs are exactly the real hypotheses consumed by
`gammaCoeffs_eq_zero_of_cascadeZeroBranch`: `det A₁ ≠ 0`, `Sym A₁ ≠ 0`, and `V₁ ≠ 0`. -/
theorem cascadeCurveRigidity_gamma_eval_zero_one_of_zeroBranch {L d : Nat}
    {θ : Params L d} {A1 : Matrix (Fin d) (Fin d) ℝ} {level : Nat}
    {tail : Nat -> ℝ}
    (hd : 0 < d)
    (D : CascadeCurveRigidityData θ A1 (level + 1) tail)
    (hA1det : A1.det ≠ 0)
    (hsymA1 : symPart A1 ≠ 0)
    (hV1 : (paramStream θ 0).1 ≠ 0) :
    D.gamma 0 = 0 ∧ D.gamma 1 = 0 := by
  let η : LayerStream d := paramStream θ
  let V1 : Matrix (Fin d) (Fin d) ℝ := (η 0).1
  let B1 : Matrix (Fin d) (Fin d) ℝ := skipB V1
  let ηtail : LayerStream d := fun k => η (k + 1)
  let Wtail : Matrix (Fin d) (Fin d) ℝ := realW ηtail tail level
  let Bsub : Matrix (Fin d) (Fin d) ℝ := realSkipBprod ηtail level
  let P : Matrix (Fin d) (Fin d) ℝ := Wtailᵀ * (η (level + 1)).2
  let Y : Matrix (Fin d) (Fin d) ℝ := P * Bsub * B1
  have hA1_ne_zero : A1 ≠ 0 := by
    intro hA1
    exact hsymA1 (by simp [hA1, symPart])
  have hx0_complex :
      matC (B1ᵀ * Y) = D.gamma 0 • matC A1 := by
    calc
      matC (B1ᵀ * Y) =
          formalX η (level + 1) (gateAssignmentOfTail 0 tail) := by
            rw [formalX_real_head_peel η level 0 tail]
            simp [η, V1, B1, ηtail, Wtail, Bsub, P, Y]
      _ = D.gamma 0 • matC A1 := by
            simpa [η, gateAssignmentOfTail] using
              (cascadeCurveRigidity_formalX_formalY D (0 : ℂ)).1
  have hx1_complex :
      matC ((B1 - V1)ᵀ * Y) = D.gamma 1 • matC A1 := by
    calc
      matC ((B1 - V1)ᵀ * Y) =
          formalX η (level + 1) (gateAssignmentOfTail 1 tail) := by
            rw [formalX_real_head_peel η level 1 tail]
            simp [η, V1, B1, ηtail, Wtail, Bsub, P, Y]
      _ = D.gamma 1 • matC A1 := by
            simpa [η, gateAssignmentOfTail] using
              (cascadeCurveRigidity_formalX_formalY D (1 : ℂ)).1
  have hγ0_real : ((D.gamma 0).re : ℂ) = D.gamma 0 :=
    complex_scalar_real_of_matC_eq_smul_matC hA1_ne_zero hx0_complex
  have hγ1_real : ((D.gamma 1).re : ℂ) = D.gamma 1 :=
    complex_scalar_real_of_matC_eq_smul_matC hA1_ne_zero hx1_complex
  have hcoeff :=
    cascadeCurveRigidity_gammaCoeffs_eq_zero_of_zeroBranch
      (θ := θ) (A1 := A1) (level := level) (tail := tail)
      hd D hA1det hsymA1 hV1
  have hγ0_zero : D.gamma 0 = 0 := by
    calc
      D.gamma 0 = ((D.gamma 0).re : ℂ) := hγ0_real.symm
      _ = 0 := by simp [hcoeff.1]
  have hre_eq : (D.gamma 1).re = (D.gamma 0).re :=
    sub_eq_zero.mp hcoeff.2
  refine ⟨hγ0_zero, ?_⟩
  calc
    D.gamma 1 = ((D.gamma 1).re : ℂ) := hγ1_real.symm
    _ = ((D.gamma 0).re : ℂ) := by rw [hre_eq]
    _ = D.gamma 0 := hγ0_real
    _ = 0 := hγ0_zero

end TransformerIdentifiability.NLayer
