import AnyLayerIdentifiabilityProof.NLayer.IDL.SaturationMatching
import Mathlib.Algebra.Polynomial.Roots

set_option autoImplicit false

open Matrix

namespace TransformerIdentifiability.NLayer

/-!
# R3 zero-branch curve-rigidity producer

This module isolates the polynomial-upgrade part of `lem:cascade`(b).  The topology and
quadric-richness work is intentionally kept outside this file: callers provide the
post-`lem:quadA` slice identities on an infinite real set.  The theorem below upgrades
those identities to the all-complex curve identity packaged by `CascadeCurveRigidityData`.
-/

/-! ## One-variable polynomial realization along a fixed real tail -/

/-- A real matrix as a constant matrix over `Polynomial ℂ`. -/
noncomputable def matPolynomialC {d : Nat} (M : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) (Polynomial ℂ) :=
  M.map fun x => Polynomial.C (x : ℂ)

/-- The one-variable polynomial gate assignment `z, tail 0, tail 1, ...`. -/
noncomputable def curveGatePoly (tail : Nat → ℝ) : Nat → Polynomial ℂ
  | 0 => Polynomial.X
  | n + 1 => Polynomial.C (tail n : ℂ)

theorem eval_curveGatePoly (tail : Nat → ℝ) (z : ℂ) (j : Nat) :
    (curveGatePoly tail j).eval z = complexGateAssignmentOfTail z tail j := by
  cases j <;> simp [curveGatePoly, complexGateAssignmentOfTail]

theorem eval_matPolynomialC {d : Nat} (z : ℂ) (M : Matrix (Fin d) (Fin d) ℝ) :
    (matPolynomialC M).map (fun p : Polynomial ℂ => p.eval z) = matC M := by
  ext i j
  simp [matPolynomialC, matC]

theorem eval_matrix_add_poly {m n : Nat} (z : ℂ)
    (A B : Matrix (Fin m) (Fin n) (Polynomial ℂ)) :
    (A + B).map (fun p : Polynomial ℂ => p.eval z) =
      A.map (fun p : Polynomial ℂ => p.eval z) + B.map (fun p : Polynomial ℂ => p.eval z) := by
  ext i j
  simp

theorem eval_matrix_sub_poly {m n : Nat} (z : ℂ)
    (A B : Matrix (Fin m) (Fin n) (Polynomial ℂ)) :
    (A - B).map (fun p : Polynomial ℂ => p.eval z) =
      A.map (fun p : Polynomial ℂ => p.eval z) - B.map (fun p : Polynomial ℂ => p.eval z) := by
  ext i j
  simp

theorem eval_matrix_mul_poly {m n o : Nat} (z : ℂ)
    (A : Matrix (Fin m) (Fin n) (Polynomial ℂ)) (B : Matrix (Fin n) (Fin o) (Polynomial ℂ)) :
    (A * B).map (fun p : Polynomial ℂ => p.eval z) =
      A.map (fun p : Polynomial ℂ => p.eval z) * B.map (fun p : Polynomial ℂ => p.eval z) := by
  ext i j
  simp [Matrix.mul_apply, Polynomial.eval_finsetSum]

theorem eval_matrix_smul_poly {m n : Nat} (z : ℂ) (c : Polynomial ℂ)
    (A : Matrix (Fin m) (Fin n) (Polynomial ℂ)) :
    (c • A).map (fun p : Polynomial ℂ => p.eval z) =
      c.eval z • A.map (fun p : Polynomial ℂ => p.eval z) := by
  ext i j
  simp [smul_eq_mul]

theorem eval_matrix_transpose_poly {m n : Nat} (z : ℂ)
    (A : Matrix (Fin m) (Fin n) (Polynomial ℂ)) :
    Aᵀ.map (fun p : Polynomial ℂ => p.eval z) =
      (A.map (fun p : Polynomial ℂ => p.eval z))ᵀ := by
  ext i j
  simp

/-- Polynomial version of `formalFactor`, after fixing all tail gates. -/
noncomputable def formalFactorCurvePoly {d : Nat} (θ : LayerStream d)
    (tail : Nat → ℝ) (j : Nat) : Matrix (Fin d) (Fin d) (Polynomial ℂ) :=
  matPolynomialC (skipB (θ j).1) - curveGatePoly tail j • matPolynomialC (θ j).1

/-- Polynomial version of `formalBprod`, after fixing all tail gates. -/
noncomputable def formalBprodCurvePoly {d : Nat} (θ : LayerStream d)
    (tail : Nat → ℝ) : Nat → Matrix (Fin d) (Fin d) (Polynomial ℂ)
  | 0 => 1
  | n + 1 => matPolynomialC (skipB (θ n).1) * formalBprodCurvePoly θ tail n

/-- Polynomial version of `formalW`, after fixing all tail gates. -/
noncomputable def formalWCurvePoly {d : Nat} (θ : LayerStream d)
    (tail : Nat → ℝ) : Nat → Matrix (Fin d) (Fin d) (Polynomial ℂ)
  | 0 => 1
  | n + 1 => formalFactorCurvePoly θ tail n * formalWCurvePoly θ tail n

/-- Polynomial version of `formalT`, after fixing all tail gates. -/
noncomputable def formalTCurvePoly {d : Nat} (θ : LayerStream d)
    (tail : Nat → ℝ) : Nat → Matrix (Fin d) (Fin d) (Polynomial ℂ)
  | 0 => 0
  | n + 1 =>
      matPolynomialC (skipB (θ n).1) * formalTCurvePoly θ tail n
        + curveGatePoly tail n • (matPolynomialC (θ n).1 * formalWCurvePoly θ tail n)

theorem eval_formalFactorCurvePoly {d : Nat} (θ : LayerStream d)
    (tail : Nat → ℝ) (z : ℂ) (j : Nat) :
    (formalFactorCurvePoly θ tail j).map (fun p : Polynomial ℂ => p.eval z) =
      formalFactor θ (complexGateAssignmentOfTail z tail) j := by
  rw [formalFactorCurvePoly, formalFactor, eval_matrix_sub_poly, eval_matPolynomialC,
    eval_matrix_smul_poly, eval_curveGatePoly, eval_matPolynomialC]

theorem eval_formalBprodCurvePoly {d : Nat} (θ : LayerStream d) (tail : Nat → ℝ) :
    ∀ (n : Nat) (z : ℂ),
      (formalBprodCurvePoly θ tail n).map (fun p : Polynomial ℂ => p.eval z) =
        formalBprod θ n := by
  intro n
  induction n with
  | zero =>
      intro z
      simp [formalBprodCurvePoly, formalBprod]
  | succ n ih =>
      intro z
      change
        (matPolynomialC (skipB (θ n).1) * formalBprodCurvePoly θ tail n).map
            (fun p : Polynomial ℂ => p.eval z) =
          matC (skipB (θ n).1) * formalBprod θ n
      rw [eval_matrix_mul_poly, eval_matPolynomialC, ih]

theorem eval_formalWCurvePoly {d : Nat} (θ : LayerStream d) (tail : Nat → ℝ) :
    ∀ (n : Nat) (z : ℂ),
      (formalWCurvePoly θ tail n).map (fun p : Polynomial ℂ => p.eval z) =
        formalW θ n (complexGateAssignmentOfTail z tail) := by
  intro n
  induction n with
  | zero =>
      intro z
      simp [formalWCurvePoly, formalW]
  | succ n ih =>
      intro z
      change
        (formalFactorCurvePoly θ tail n * formalWCurvePoly θ tail n).map
            (fun p : Polynomial ℂ => p.eval z) =
          formalFactor θ (complexGateAssignmentOfTail z tail) n *
            formalW θ n (complexGateAssignmentOfTail z tail)
      rw [eval_matrix_mul_poly, eval_formalFactorCurvePoly, ih]

theorem eval_formalTCurvePoly {d : Nat} (θ : LayerStream d) (tail : Nat → ℝ) :
    ∀ (n : Nat) (z : ℂ),
      (formalTCurvePoly θ tail n).map (fun p : Polynomial ℂ => p.eval z) =
        formalT θ n (complexGateAssignmentOfTail z tail) := by
  intro n
  induction n with
  | zero =>
      intro z
      simp [formalTCurvePoly, formalT]
  | succ n ih =>
      intro z
      change
        (matPolynomialC (skipB (θ n).1) * formalTCurvePoly θ tail n
            + curveGatePoly tail n •
              (matPolynomialC (θ n).1 * formalWCurvePoly θ tail n)).map
            (fun p : Polynomial ℂ => p.eval z) =
          matC (skipB (θ n).1) * formalT θ n (complexGateAssignmentOfTail z tail)
            + complexGateAssignmentOfTail z tail n •
              (matC (θ n).1 * formalW θ n (complexGateAssignmentOfTail z tail))
      rw [eval_matrix_add_poly, eval_matrix_mul_poly, eval_matPolynomialC, ih,
        eval_matrix_smul_poly, eval_curveGatePoly, eval_matrix_mul_poly,
        eval_matPolynomialC, eval_formalWCurvePoly]

/-- Polynomial version of `formalX` along the curve `z, tail`. -/
noncomputable def formalXCurvePoly {d : Nat} (θ : LayerStream d) (tail : Nat → ℝ)
    (n : Nat) : Matrix (Fin d) (Fin d) (Polynomial ℂ) :=
  (formalWCurvePoly θ tail n)ᵀ * matPolynomialC (θ n).2 * formalBprodCurvePoly θ tail n

/-- Polynomial version of `formalY` along the curve `z, tail`. -/
noncomputable def formalYCurvePoly {d : Nat} (θ : LayerStream d) (tail : Nat → ℝ)
    (n : Nat) : Matrix (Fin d) (Fin d) (Polynomial ℂ) :=
  (formalWCurvePoly θ tail n)ᵀ * matPolynomialC (θ n).2 * formalTCurvePoly θ tail n

theorem eval_formalXCurvePoly {d : Nat} (θ : LayerStream d) (tail : Nat → ℝ)
    (n : Nat) (z : ℂ) :
    (formalXCurvePoly θ tail n).map (fun p : Polynomial ℂ => p.eval z) =
      formalX θ n (complexGateAssignmentOfTail z tail) := by
  rw [formalXCurvePoly, formalX, eval_matrix_mul_poly, eval_matrix_mul_poly,
    eval_matrix_transpose_poly, eval_formalWCurvePoly, eval_matPolynomialC,
    eval_formalBprodCurvePoly]

theorem eval_formalYCurvePoly {d : Nat} (θ : LayerStream d) (tail : Nat → ℝ)
    (n : Nat) (z : ℂ) :
    (formalYCurvePoly θ tail n).map (fun p : Polynomial ℂ => p.eval z) =
      formalY θ n (complexGateAssignmentOfTail z tail) := by
  rw [formalYCurvePoly, formalY, eval_matrix_mul_poly, eval_matrix_mul_poly,
    eval_matrix_transpose_poly, eval_formalWCurvePoly, eval_matPolynomialC,
    eval_formalTCurvePoly]

theorem formalFactor_complexGateAssignmentOfTail_succ {d : Nat}
    (θ : LayerStream d) (tail : Nat → ℝ) (z : ℂ) (n : Nat) :
    formalFactor θ (complexGateAssignmentOfTail z tail) (n + 1) =
      matC (skipB (θ (n + 1)).1) - (tail n : ℂ) • matC (θ (n + 1)).1 := by
  simp [formalFactor, complexGateAssignmentOfTail]

/-- Along a slice with only gate `0` free, `formalW` is affine in that gate. -/
theorem formalW_complexGateAssignmentOfTail_affine {d : Nat}
    (θ : LayerStream d) (tail : Nat → ℝ) (n : Nat) :
    ∃ W0 W1 : Matrix (Fin d) (Fin d) ℂ, ∀ z : ℂ,
      formalW θ n (complexGateAssignmentOfTail z tail) = W0 + z • W1 := by
  induction n with
  | zero =>
      refine ⟨1, 0, ?_⟩
      intro z
      simp [formalW]
  | succ n ih =>
      cases n with
      | zero =>
          refine ⟨matC (skipB (θ 0).1), -matC (θ 0).1, ?_⟩
          intro z
          simp [formalW, formalFactor, complexGateAssignmentOfTail, sub_eq_add_neg]
      | succ n =>
          rcases ih with ⟨W0, W1, hW⟩
          let F : Matrix (Fin d) (Fin d) ℂ :=
            matC (skipB (θ (n + 1)).1) - (tail n : ℂ) • matC (θ (n + 1)).1
          refine ⟨F * W0, F * W1, ?_⟩
          intro z
          rw [formalW, formalFactor_complexGateAssignmentOfTail_succ, hW]
          change F * (W0 + z • W1) = F * W0 + z • (F * W1)
          rw [Matrix.mul_add, Matrix.mul_smul]

/-- Along a slice with only gate `0` free, `formalX` is affine in that gate. -/
theorem formalX_complexGateAssignmentOfTail_affine {d : Nat}
    (θ : LayerStream d) (tail : Nat → ℝ) (level : Nat) :
    ∃ X0 X1 : Matrix (Fin d) (Fin d) ℂ, ∀ z : ℂ,
      formalX θ level (complexGateAssignmentOfTail z tail) = X0 + z • X1 := by
  rcases formalW_complexGateAssignmentOfTail_affine θ tail level with ⟨W0, W1, hW⟩
  refine ⟨W0ᵀ * matC (θ level).2 * formalBprod θ level,
    W1ᵀ * matC (θ level).2 * formalBprod θ level, ?_⟩
  intro z
  rw [formalX, hW]
  rw [transpose_add, transpose_smul, Matrix.add_mul, Matrix.smul_mul, Matrix.add_mul,
    Matrix.smul_mul]

/-- Every entry of `formalX` is affine on the real first-gate slice. -/
theorem formalX_gateAssignmentOfTail_entry_affine {L d : Nat}
    (θ : Params L d) (level : Nat) (tail : Nat → ℝ) (i j : Fin d) :
    ∃ a0 a1 : ℂ, ∀ t : ℝ,
      formalX (paramStream θ) level (gateAssignmentOfTail t tail) i j =
        a0 + a1 * (t : ℂ) := by
  rcases formalX_complexGateAssignmentOfTail_affine (paramStream θ) tail level with
    ⟨X0, X1, hX⟩
  refine ⟨X0 i j, X1 i j, ?_⟩
  intro t
  calc
    formalX (paramStream θ) level (gateAssignmentOfTail t tail) i j =
        X0 i j + (t : ℂ) * X1 i j := by
      simpa [gateAssignmentOfTail, Matrix.smul_apply, smul_eq_mul] using
        congrFun (congrFun (hX (t : ℂ)) i) j
    _ = X0 i j + X1 i j * (t : ℂ) := by ring

/-- Slice-restricted form of `formalX_gateAssignmentOfTail_entry_affine`. -/
theorem formalX_gateAssignmentOfTail_entry_affine_on {L d : Nat}
    (θ : Params L d) (level : Nat) (tail : Nat → ℝ) (i j : Fin d) (J : Set ℝ) :
    ∃ a0 a1 : ℂ, ∀ t : ℝ, t ∈ J →
      formalX (paramStream θ) level (gateAssignmentOfTail t tail) i j =
        a0 + a1 * (t : ℂ) := by
  rcases formalX_gateAssignmentOfTail_entry_affine θ level tail i j with ⟨a0, a1, h⟩
  exact ⟨a0, a1, fun t _ => h t⟩

/-! ## Infinite-real-slice polynomial upgrade -/

theorem polynomial_eq_zero_of_eval_ofReal_eq_zero_on_infinite {S : Set ℝ}
    (hS : S.Infinite) {P : Polynomial ℂ}
    (hP : ∀ t : ℝ, t ∈ S → P.eval (t : ℂ) = 0) :
    P = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot P
  apply ((hS.image Complex.ofReal_injective.injOn).mono ?_)
  rintro z ⟨t, ht, rfl⟩
  simpa [Polynomial.IsRoot.def] using hP t ht

theorem matrix_polynomial_eval_zero_of_real_slice {d : Nat} {S : Set ℝ}
    (hS : S.Infinite) (P : Matrix (Fin d) (Fin d) (Polynomial ℂ))
    (hP : ∀ t : ℝ, t ∈ S → P.map (fun p : Polynomial ℂ => p.eval (t : ℂ)) = 0)
    (z : ℂ) :
    P.map (fun p : Polynomial ℂ => p.eval z) = 0 := by
  ext i j
  have hentry : P i j = 0 := by
    apply polynomial_eq_zero_of_eval_ofReal_eq_zero_on_infinite hS
    intro t ht
    have hmat := hP t ht
    exact congrFun (congrFun hmat i) j
  simp [hentry]

/-- A nonempty open subset of the real line is infinite. -/
theorem realSet_infinite_of_isOpen_nonempty {J : Set ℝ}
    (hJ_open : IsOpen J) (hJ_nonempty : J.Nonempty) :
    J.Infinite := by
  rcases hJ_nonempty with ⟨t, ht⟩
  exact infinite_of_mem_nhds t (hJ_open.mem_nhds ht)

/-- The real slice `J` in a coefficient-separating product patch is infinite. -/
theorem CoefficientSeparatingProductPatch.J_infinite {d : Nat}
    {A : Matrix (Fin d) (Fin d) ℝ} {U0 : Set (ProbePair d × ℝ)}
    (patch : CoefficientSeparatingProductPatch A U0) :
    patch.J.Infinite :=
  realSet_infinite_of_isOpen_nonempty patch.J_open patch.J_nonempty

noncomputable def affineGammaPoly (γ₀ γ₁ : ℂ) : Polynomial ℂ :=
  Polynomial.C γ₀ + Polynomial.C γ₁ * Polynomial.X

@[simp] theorem eval_affineGammaPoly (γ₀ γ₁ z : ℂ) :
    (affineGammaPoly γ₀ γ₁).eval z = γ₀ + γ₁ * z := by
  simp [affineGammaPoly]

noncomputable def curveXResidualPoly {d : Nat} (θ : LayerStream d)
    (A : Matrix (Fin d) (Fin d) ℝ) (level : Nat) (tail : Nat → ℝ)
    (γ₀ γ₁ : ℂ) : Matrix (Fin d) (Fin d) (Polynomial ℂ) :=
  formalXCurvePoly θ tail level - affineGammaPoly γ₀ γ₁ • matPolynomialC A

noncomputable def curveYSymPoly {d : Nat} (θ : LayerStream d)
    (level : Nat) (tail : Nat → ℝ) : Matrix (Fin d) (Fin d) (Polynomial ℂ) :=
  formalYCurvePoly θ tail level + (formalYCurvePoly θ tail level)ᵀ

theorem eval_curveXResidualPoly {d : Nat} (θ : LayerStream d)
    (A : Matrix (Fin d) (Fin d) ℝ) (level : Nat) (tail : Nat → ℝ)
    (γ₀ γ₁ z : ℂ) :
    (curveXResidualPoly θ A level tail γ₀ γ₁).map (fun p : Polynomial ℂ => p.eval z) =
      formalX θ level (complexGateAssignmentOfTail z tail)
        - (γ₀ + γ₁ * z) • matC A := by
  rw [curveXResidualPoly, eval_matrix_sub_poly, eval_formalXCurvePoly,
    eval_matrix_smul_poly, eval_matPolynomialC, eval_affineGammaPoly]

theorem eval_curveYSymPoly {d : Nat} (θ : LayerStream d)
    (level : Nat) (tail : Nat → ℝ) (z : ℂ) :
    (curveYSymPoly θ level tail).map (fun p : Polynomial ℂ => p.eval z) =
      formalY θ level (complexGateAssignmentOfTail z tail)
        + (formalY θ level (complexGateAssignmentOfTail z tail))ᵀ := by
  rw [curveYSymPoly, eval_matrix_add_poly, eval_formalYCurvePoly,
    eval_matrix_transpose_poly, eval_formalYCurvePoly]

/-! ## From upgraded matrix identities to the curve identity -/

/-- The complex bilinear form of `matC A` on real vectors is `matrixBilin A` coerced. -/
theorem vecC_matC_bilin_for_curve {d : Nat} (A : Matrix (Fin d) (Fin d) ℝ)
    (w v : Fin d → ℝ) :
    vecC w ⬝ᵥ (matC A *ᵥ vecC v) = (matrixBilin A w v : ℂ) := by
  simp [matrixBilin, matC, vecC, Matrix.mulVec, dotProduct]

/-- An antisymmetric complex matrix has zero quadratic form on real vectors. -/
theorem complex_quadratic_zero_of_antisymm {d : Nat} (Y : Matrix (Fin d) (Fin d) ℂ)
    (hY : Y + Yᵀ = 0) (w : Fin d → ℝ) :
    vecC w ⬝ᵥ (Y *ᵥ vecC w) = 0 := by
  let x : Fin d → ℂ := vecC w
  have hYT : Yᵀ = -Y := by
    exact eq_neg_iff_add_eq_zero.mpr (by simpa [add_comm] using hY)
  have htranspose :
      x ⬝ᵥ (Yᵀ *ᵥ x) = x ⬝ᵥ (Y *ᵥ x) := by
    simpa using Matrix.dotProduct_transpose_mulVec (A := Y) (x := x) (y := x)
  have hneg : x ⬝ᵥ (Yᵀ *ᵥ x) = -(x ⬝ᵥ (Y *ᵥ x)) := by
    rw [hYT, Matrix.neg_mulVec, dotProduct_neg]
  have hq_eq_neg : x ⬝ᵥ (Y *ᵥ x) = -(x ⬝ᵥ (Y *ᵥ x)) :=
    htranspose.symm.trans hneg
  have htwo : (2 : ℂ) * (x ⬝ᵥ (Y *ᵥ x)) = 0 := by
    have hadd : x ⬝ᵥ (Y *ᵥ x) + x ⬝ᵥ (Y *ᵥ x) = 0 := by
      calc
        x ⬝ᵥ (Y *ᵥ x) + x ⬝ᵥ (Y *ᵥ x)
            = -(x ⬝ᵥ (Y *ᵥ x)) + x ⬝ᵥ (Y *ᵥ x) := by
              exact congrArg (fun a => a + x ⬝ᵥ (Y *ᵥ x)) hq_eq_neg
        _ = 0 := neg_add_cancel _
    simpa [two_mul] using hadd
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

theorem specializedPhi_eq_gamma_matrixBilin_of_formalXY {L d : Nat}
    (θ : Params L d) (A : Matrix (Fin d) (Fin d) ℝ) (level : Nat)
    (tail : Nat → ℝ) (gamma : ℂ) (z : ℂ)
    (hX :
      formalX (paramStream θ) level (complexGateAssignmentOfTail z tail) =
        gamma • matC A)
    (hY :
      formalY (paramStream θ) level (complexGateAssignmentOfTail z tail)
        + (formalY (paramStream θ) level (complexGateAssignmentOfTail z tail))ᵀ = 0)
    (p : ProbePair d) :
    specializedPhi θ level (complexGateAssignmentOfTail z tail) p =
      gamma * (matrixBilin A p.1 p.2 : ℂ) := by
  rw [specializedPhi, formalPhi_eq_affine, hX]
  have hquad := complex_quadratic_zero_of_antisymm
    (formalY (paramStream θ) level (complexGateAssignmentOfTail z tail)) hY p.1
  rw [hquad, add_zero, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    vecC_matC_bilin_for_curve]

/-- A quadratic form is half of its symmetric-part quadratic form. -/
theorem dotProduct_mulVec_eq_half_dotProduct_symm {d : Nat}
    (Y S : Matrix (Fin d) (Fin d) ℂ) (hYSym : Y + Yᵀ = S) (w : Fin d → ℂ) :
    w ⬝ᵥ (Y *ᵥ w) = (1 / 2 : ℂ) * (w ⬝ᵥ (S *ᵥ w)) := by
  have htranspose :
      w ⬝ᵥ (Yᵀ *ᵥ w) = w ⬝ᵥ (Y *ᵥ w) := by
    simpa using Matrix.dotProduct_transpose_mulVec (A := Y) (x := w) (y := w)
  have hsym :
      w ⬝ᵥ ((Y + Yᵀ) *ᵥ w) = w ⬝ᵥ (S *ᵥ w) := by
    rw [hYSym]
  rw [Matrix.add_mulVec, dotProduct_add, htranspose] at hsym
  linear_combination (1 / 2 : ℂ) * hsym

/-- Scalar residual form of the zero-branch product-patch equation.

If `formalX - γ(t) A` and the symmetric `formalY` residual are represented by real
matrices `M` and `R t`, then vanishing of `specializedPhi` on the quadric product patch
forces the corresponding real scalar residual to vanish.  The factor `1 / 2` is the
conversion from `formalPhi`'s quadratic matrix to the supplied symmetric-part residual
`formalY + formalYᵀ = matC (R t)`. -/
theorem real_bilin_residual_eq_zero_of_specializedPhi_zero {L d : Nat}
    {θ : Params L d} {A : Matrix (Fin d) (Fin d) ℝ} {level : Nat} {tail : Nat → ℝ}
    {U0 : Set (ProbePair d × ℝ)}
    (patch : CoefficientSeparatingProductPatch A U0)
    (gamma0 gamma1 : ℂ)
    (M : Matrix (Fin d) (Fin d) ℝ) (R : ℝ → Matrix (Fin d) (Fin d) ℝ)
    (hXres :
      ∀ t : ℝ, t ∈ patch.J →
        formalX (paramStream θ) level (gateAssignmentOfTail t tail)
            - (gamma0 + gamma1 * (t : ℂ)) • matC A =
          matC M)
    (hYres :
      ∀ t : ℝ, t ∈ patch.J →
        formalY (paramStream θ) level (gateAssignmentOfTail t tail)
          + (formalY (paramStream θ) level (gateAssignmentOfTail t tail))ᵀ =
          matC (R t))
    (hzero :
      ∀ p : ProbePair d, p ∈ patch.Uq → ∀ t : ℝ, t ∈ patch.J →
        specializedPhi θ level (gateAssignmentOfTail t tail) p = 0) :
    ∀ p : ProbePair d, p ∈ patch.Uq → ∀ t : ℝ, t ∈ patch.J →
      p.1 ⬝ᵥ (M *ᵥ p.2) + (1 / 2 : ℝ) * (p.1 ⬝ᵥ ((R t) *ᵥ p.1)) = 0 := by
  intro p hp t ht
  have hquad : matrixBilin A p.1 p.2 = 0 := patch.Uq_on_quadric p hp
  have hphi := hzero p hp t ht
  rw [specializedPhi, formalPhi_eq_affine] at hphi
  have hXres' :
      formalX (paramStream θ) level (gateAssignmentOfTail t tail) =
        (gamma0 + gamma1 * (t : ℂ)) • matC A + matC M := by
    exact sub_eq_iff_eq_add'.mp (hXres t ht)
  have hYquad :=
    dotProduct_mulVec_eq_half_dotProduct_symm
      (formalY (paramStream θ) level (gateAssignmentOfTail t tail))
      (matC (R t)) (hYres t ht) (vecC p.1)
  rw [hXres', hYquad] at hphi
  rw [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul, vecC_matC_bilin_for_curve, hquad, Complex.ofReal_zero, mul_zero,
    zero_add, vecC_matC_bilin_for_curve, vecC_matC_bilin_for_curve] at hphi
  have hrealC :
      ((p.1 ⬝ᵥ (M *ᵥ p.2) + (1 / 2 : ℝ) * (p.1 ⬝ᵥ ((R t) *ᵥ p.1)) : ℝ) : ℂ) =
        0 := by
    simpa [matrixBilin, Complex.ofReal_add, Complex.ofReal_mul] using hphi
  exact Complex.ofReal_inj.mp hrealC

/-- Pointwise version of `real_bilin_residual_eq_zero_of_specializedPhi_zero`.

This is the form needed when the real residual matrix depends on the slice parameter
`t`: for a fixed `t ∈ patch.J`, the same algebra extracts the scalar residual from
`specializedPhi = 0`. -/
theorem real_bilin_residual_eq_zero_at_of_specializedPhi_zero {L d : Nat}
    {θ : Params L d} {A : Matrix (Fin d) (Fin d) ℝ} {level : Nat} {tail : Nat → ℝ}
    {U0 : Set (ProbePair d × ℝ)}
    (patch : CoefficientSeparatingProductPatch A U0)
    (gamma0 gamma1 : ℂ)
    (t : ℝ)
    (M R : Matrix (Fin d) (Fin d) ℝ)
    (hXres :
      formalX (paramStream θ) level (gateAssignmentOfTail t tail)
          - (gamma0 + gamma1 * (t : ℂ)) • matC A =
        matC M)
    (hYres :
      formalY (paramStream θ) level (gateAssignmentOfTail t tail)
        + (formalY (paramStream θ) level (gateAssignmentOfTail t tail))ᵀ =
        matC R)
    (hzero :
      ∀ p : ProbePair d, p ∈ patch.Uq →
        specializedPhi θ level (gateAssignmentOfTail t tail) p = 0) :
    ∀ p : ProbePair d, p ∈ patch.Uq →
      p.1 ⬝ᵥ (M *ᵥ p.2) + (1 / 2 : ℝ) * (p.1 ⬝ᵥ (R *ᵥ p.1)) = 0 := by
  intro p hp
  have hquad : matrixBilin A p.1 p.2 = 0 := patch.Uq_on_quadric p hp
  have hphi := hzero p hp
  rw [specializedPhi, formalPhi_eq_affine] at hphi
  have hXres' :
      formalX (paramStream θ) level (gateAssignmentOfTail t tail) =
        (gamma0 + gamma1 * (t : ℂ)) • matC A + matC M := by
    exact sub_eq_iff_eq_add'.mp hXres
  have hYquad :=
    dotProduct_mulVec_eq_half_dotProduct_symm
      (formalY (paramStream θ) level (gateAssignmentOfTail t tail))
      (matC R) hYres (vecC p.1)
  rw [hXres', hYquad] at hphi
  rw [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul, vecC_matC_bilin_for_curve, hquad, Complex.ofReal_zero, mul_zero,
    zero_add, vecC_matC_bilin_for_curve, vecC_matC_bilin_for_curve] at hphi
  have hrealC :
      ((p.1 ⬝ᵥ (M *ᵥ p.2) + (1 / 2 : ℝ) * (p.1 ⬝ᵥ (R *ᵥ p.1)) : ℝ) : ℂ) =
        0 := by
    simpa [matrixBilin, Complex.ofReal_add, Complex.ofReal_mul] using hphi
  exact Complex.ofReal_inj.mp hrealC

/-! ## Quadratic slice-rigidity handoff -/

/-- If a complex symmetric-part identity is represented by a real matrix through `matC`,
then the representing real matrix is symmetric. -/
theorem transpose_eq_self_of_complex_symm_matC {d : Nat}
    (Y : Matrix (Fin d) (Fin d) ℂ) (R : Matrix (Fin d) (Fin d) ℝ)
    (h : Y + Yᵀ = matC R) :
    Rᵀ = R := by
  ext i j
  exact Complex.ofReal_inj.mp <| by
    calc
      ((Rᵀ) i j : ℂ) = ((R j i : ℝ) : ℂ) := by
        rfl
      _ = Y j i + Y i j := by
        simpa [matC, Matrix.add_apply, Matrix.transpose_apply] using
          (congrFun (congrFun h j) i).symm
      _ = Y i j + Y j i := by
        rw [add_comm]
      _ = ((R i j : ℝ) : ℂ) := by
        simpa [matC, Matrix.add_apply, Matrix.transpose_apply] using
          congrFun (congrFun h i) j

/-- A symmetric real matrix whose half-scaled copy is antisymmetric is zero. -/
theorem matrix_eq_zero_of_half_smul_add_transpose_eq_zero_of_transpose_eq_self {d : Nat}
    {R : Matrix (Fin d) (Fin d) ℝ}
    (hhalf : (1 / 2 : ℝ) • R + ((1 / 2 : ℝ) • R)ᵀ = 0)
    (hsymm : Rᵀ = R) :
    R = 0 := by
  ext i j
  have hentry := congrFun (congrFun hhalf i) j
  have hsymm_entry := congrFun (congrFun hsymm i) j
  simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.smul_apply,
    Matrix.zero_apply] at hentry hsymm_entry
  rw [hsymm_entry] at hentry
  norm_num at hentry
  exact hentry

/-- Product-patch handoff from the explicit quadratic slice-rigidity interface.

For each real slice `t ∈ patch.J`, the scalar residual identity obtained from
`specializedPhi = 0` is fed to `QuadricProbeSliceQuadraticCoefficientSeparation` with
`X = M t` and `Y = (1/2) • R t`.  The resulting proportional `M t` is absorbed into a
new real scalar `gamma t`, while the `Y` identity combines with the symmetry forced by
`hYres` to make the formal symmetric `Y` part vanish. -/
theorem product_patch_formalXY_on_J_of_quadratic_coefficient_separation {L d : Nat}
    {θ : Params L d} {A : Matrix (Fin d) (Fin d) ℝ} {level : Nat} {tail : Nat → ℝ}
    {U0 : Set (ProbePair d × ℝ)}
    (patch : CoefficientSeparatingProductPatch A U0)
    (hquadratic : QuadricProbeSliceQuadraticCoefficientSeparation A patch.Uq)
    (gamma0 gamma1 : ℂ)
    (M R : ℝ → Matrix (Fin d) (Fin d) ℝ)
    (hXres :
      ∀ t : ℝ, t ∈ patch.J →
        formalX (paramStream θ) level (gateAssignmentOfTail t tail)
            - (gamma0 + gamma1 * (t : ℂ)) • matC A =
          matC (M t))
    (hYres :
      ∀ t : ℝ, t ∈ patch.J →
        formalY (paramStream θ) level (gateAssignmentOfTail t tail)
          + (formalY (paramStream θ) level (gateAssignmentOfTail t tail))ᵀ =
          matC (R t))
    (hzero :
      ∀ p : ProbePair d, p ∈ patch.Uq → ∀ t : ℝ, t ∈ patch.J →
        specializedPhi θ level (gateAssignmentOfTail t tail) p = 0) :
    ∃ gamma : ℝ → ℝ,
      (∀ t : ℝ, t ∈ patch.J →
        formalX (paramStream θ) level (gateAssignmentOfTail t tail) =
          (gamma0 + gamma1 * (t : ℂ) + (gamma t : ℂ)) • matC A) ∧
      (∀ t : ℝ, t ∈ patch.J →
        formalY (paramStream θ) level (gateAssignmentOfTail t tail)
          + (formalY (paramStream θ) level (gateAssignmentOfTail t tail))ᵀ = 0) := by
  classical
  let halfR : ℝ → Matrix (Fin d) (Fin d) ℝ := fun t => (1 / 2 : ℝ) • (R t)
  let hsep :
      ∀ t : ℝ, t ∈ patch.J →
        ∃ c : ℝ, M t = c • A ∧ halfR t + (halfR t)ᵀ = 0 := by
    intro t ht
    apply hquadratic (M t) (halfR t)
    intro p hp
    have hres :=
      real_bilin_residual_eq_zero_at_of_specializedPhi_zero patch gamma0 gamma1
        t (M t) (R t) (hXres t ht) (hYres t ht)
        (fun q hq => hzero q hq t ht) p hp
    simpa [halfR, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] using hres
  let gamma : ℝ → ℝ :=
    fun t => if ht : t ∈ patch.J then Classical.choose (hsep t ht) else 0
  refine ⟨gamma, ?_, ?_⟩
  · intro t ht
    have htchoose :
        gamma t = Classical.choose (hsep t ht) := by
      simp [gamma, ht]
    have hMt : M t = gamma t • A := by
      rw [htchoose]
      exact (Classical.choose_spec (hsep t ht)).1
    have hx := hXres t ht
    have hx' :
        formalX (paramStream θ) level (gateAssignmentOfTail t tail) =
          (gamma0 + gamma1 * (t : ℂ)) • matC A + matC (M t) := by
      exact sub_eq_iff_eq_add'.mp hx
    rw [hx', hMt]
    ext i j
    simp [matC, Matrix.add_apply, Matrix.smul_apply, add_mul]
  · intro t ht
    have hhalfR : halfR t + (halfR t)ᵀ = 0 := by
      exact (Classical.choose_spec (hsep t ht)).2
    have hhalf : (1 / 2 : ℝ) • (R t) + ((1 / 2 : ℝ) • (R t))ᵀ = 0 := by
      simpa [halfR] using hhalfR
    have hsymm : (R t)ᵀ = R t :=
      transpose_eq_self_of_complex_symm_matC
        (formalY (paramStream θ) level (gateAssignmentOfTail t tail)) (R t) (hYres t ht)
    have hRzero : R t = 0 :=
      matrix_eq_zero_of_half_smul_add_transpose_eq_zero_of_transpose_eq_self hhalf hsymm
    simpa [hRzero, matC] using hYres t ht

/-- Repackage a slice-wise scalar proportionality as provider-ready affine coefficients.

This is the small algebraic handoff after `product_patch_formalXY_on_J_of_quadratic_...`:
once the extra real slice scalar is known to combine with `gamma0 + gamma1 * t` into an
affine complex scalar on `patch.J`, the displayed matrix identities have the exact shape
required by `CascadeCurveRigidityProvider`. -/
theorem product_patch_formalXY_affine_on_J_of_scalar_affine {L d : Nat}
    {θ : Params L d} {A : Matrix (Fin d) (Fin d) ℝ} {level : Nat} {tail : Nat → ℝ}
    {U0 : Set (ProbePair d × ℝ)}
    (patch : CoefficientSeparatingProductPatch A U0)
    (gamma0 gamma1 : ℂ) (gamma : ℝ → ℝ)
    (hX :
      ∀ t : ℝ, t ∈ patch.J →
        formalX (paramStream θ) level (gateAssignmentOfTail t tail) =
          (gamma0 + gamma1 * (t : ℂ) + (gamma t : ℂ)) • matC A)
    (hY :
      ∀ t : ℝ, t ∈ patch.J →
        formalY (paramStream θ) level (gateAssignmentOfTail t tail)
          + (formalY (paramStream θ) level (gateAssignmentOfTail t tail))ᵀ = 0)
    (hgamma_affine :
      ∃ Gamma0 Gamma1 : ℂ, ∀ t : ℝ, t ∈ patch.J →
        gamma0 + gamma1 * (t : ℂ) + (gamma t : ℂ) =
          Gamma0 + Gamma1 * (t : ℂ)) :
    ∃ Gamma0 Gamma1 : ℂ,
      (∀ t : ℝ, t ∈ patch.J →
        formalX (paramStream θ) level (gateAssignmentOfTail t tail) =
          (Gamma0 + Gamma1 * (t : ℂ)) • matC A) ∧
      (∀ t : ℝ, t ∈ patch.J →
        formalY (paramStream θ) level (gateAssignmentOfTail t tail)
          + (formalY (paramStream θ) level (gateAssignmentOfTail t tail))ᵀ = 0) := by
  rcases hgamma_affine with ⟨Gamma0, Gamma1, hgamma⟩
  refine ⟨Gamma0, Gamma1, ?_, hY⟩
  intro t ht
  rw [hX t ht, hgamma t ht]

/-- Extract scalar affinity from one nonzero entry of `A`.

If `formalX` is a scalar multiple of `A` on `patch.J` and one entry of `formalX` over a
nonzero entry of `A` is affine in the slice parameter, then the scalar itself is affine
on `patch.J`.  This isolates the remaining TeX-side specialization: proving the chosen
`formalX` entry is affine in the first gate. -/
theorem scalar_affine_on_J_of_formalX_entry_affine {L d : Nat}
    {θ : Params L d} {A : Matrix (Fin d) (Fin d) ℝ} {level : Nat} {tail : Nat → ℝ}
    {U0 : Set (ProbePair d × ℝ)}
    (patch : CoefficientSeparatingProductPatch A U0)
    (gamma0 gamma1 : ℂ) (gamma : ℝ → ℝ)
    (i j : Fin d)
    (hAij : A i j ≠ 0)
    (hentry_affine :
      ∃ a0 a1 : ℂ, ∀ t : ℝ, t ∈ patch.J →
        formalX (paramStream θ) level (gateAssignmentOfTail t tail) i j =
          a0 + a1 * (t : ℂ))
    (hX :
      ∀ t : ℝ, t ∈ patch.J →
        formalX (paramStream θ) level (gateAssignmentOfTail t tail) =
          (gamma0 + gamma1 * (t : ℂ) + (gamma t : ℂ)) • matC A) :
    ∃ Gamma0 Gamma1 : ℂ, ∀ t : ℝ, t ∈ patch.J →
      gamma0 + gamma1 * (t : ℂ) + (gamma t : ℂ) =
        Gamma0 + Gamma1 * (t : ℂ) := by
  rcases hentry_affine with ⟨a0, a1, hentry⟩
  let Aij : ℂ := (A i j : ℂ)
  have hAijC : Aij ≠ 0 := by
    have hcast : (A i j : ℂ) ≠ 0 := by
      exact_mod_cast hAij
    simpa [Aij] using hcast
  refine ⟨a0 / Aij, a1 / Aij, ?_⟩
  intro t ht
  have hentry_scalar :
      formalX (paramStream θ) level (gateAssignmentOfTail t tail) i j =
        (gamma0 + gamma1 * (t : ℂ) + (gamma t : ℂ)) * Aij := by
    simpa [Aij, matC, Matrix.smul_apply, smul_eq_mul] using
      congrFun (congrFun (hX t ht) i) j
  have hscalar_mul :
      (gamma0 + gamma1 * (t : ℂ) + (gamma t : ℂ)) * Aij =
        a0 + a1 * (t : ℂ) := by
    exact hentry_scalar.symm.trans (hentry t ht)
  calc
    gamma0 + gamma1 * (t : ℂ) + (gamma t : ℂ)
        = (a0 + a1 * (t : ℂ)) / Aij := by
          rw [← hscalar_mul]
          field_simp [hAijC]
    _ = a0 / Aij + (a1 / Aij) * (t : ℂ) := by
          field_simp [hAijC]

/-- Product-patch handoff from quadratic coefficient separation to provider-ready affine
matrix identities, with the remaining trace/nonzero-entry affine step isolated as an
explicit input.

The hypothesis `hgamma_affine` is exactly the still-missing scalar upgrade: for whatever
slice scalar `gamma` is produced by the quadratic handoff, if it gives the slice-wise
`formalX` identity, then the total scalar is affine on the infinite real slice `patch.J`. -/
theorem product_patch_formalXY_affine_on_J_of_quadratic_coefficient_separation {L d : Nat}
    {θ : Params L d} {A : Matrix (Fin d) (Fin d) ℝ} {level : Nat} {tail : Nat → ℝ}
    {U0 : Set (ProbePair d × ℝ)}
    (patch : CoefficientSeparatingProductPatch A U0)
    (hquadratic : QuadricProbeSliceQuadraticCoefficientSeparation A patch.Uq)
    (gamma0 gamma1 : ℂ)
    (M R : ℝ → Matrix (Fin d) (Fin d) ℝ)
    (hXres :
      ∀ t : ℝ, t ∈ patch.J →
        formalX (paramStream θ) level (gateAssignmentOfTail t tail)
            - (gamma0 + gamma1 * (t : ℂ)) • matC A =
          matC (M t))
    (hYres :
      ∀ t : ℝ, t ∈ patch.J →
        formalY (paramStream θ) level (gateAssignmentOfTail t tail)
          + (formalY (paramStream θ) level (gateAssignmentOfTail t tail))ᵀ =
          matC (R t))
    (hzero :
      ∀ p : ProbePair d, p ∈ patch.Uq → ∀ t : ℝ, t ∈ patch.J →
        specializedPhi θ level (gateAssignmentOfTail t tail) p = 0)
    (hgamma_affine :
      ∀ gamma : ℝ → ℝ,
        (∀ t : ℝ, t ∈ patch.J →
          formalX (paramStream θ) level (gateAssignmentOfTail t tail) =
            (gamma0 + gamma1 * (t : ℂ) + (gamma t : ℂ)) • matC A) →
        ∃ Gamma0 Gamma1 : ℂ, ∀ t : ℝ, t ∈ patch.J →
          gamma0 + gamma1 * (t : ℂ) + (gamma t : ℂ) =
            Gamma0 + Gamma1 * (t : ℂ)) :
    ∃ Gamma0 Gamma1 : ℂ,
      (∀ t : ℝ, t ∈ patch.J →
        formalX (paramStream θ) level (gateAssignmentOfTail t tail) =
          (Gamma0 + Gamma1 * (t : ℂ)) • matC A) ∧
      (∀ t : ℝ, t ∈ patch.J →
        formalY (paramStream θ) level (gateAssignmentOfTail t tail)
          + (formalY (paramStream θ) level (gateAssignmentOfTail t tail))ᵀ = 0) := by
  rcases product_patch_formalXY_on_J_of_quadratic_coefficient_separation
      patch hquadratic gamma0 gamma1 M R hXres hYres hzero with
    ⟨gamma, hX, hY⟩
  exact product_patch_formalXY_affine_on_J_of_scalar_affine patch gamma0 gamma1 gamma
    hX hY (hgamma_affine gamma hX)

/-- Product-patch handoff using a single affine nonzero `formalX` entry for the scalar
upgrade.

Compared with
`product_patch_formalXY_affine_on_J_of_quadratic_coefficient_separation`, this theorem
replaces the abstract `hgamma_affine` input by an explicit entry-affinity hypothesis at a
chosen nonzero entry of `A`. -/
theorem product_patch_formalXY_affine_on_J_of_quadratic_coefficient_separation_entry_affine
    {L d : Nat}
    {θ : Params L d} {A : Matrix (Fin d) (Fin d) ℝ} {level : Nat} {tail : Nat → ℝ}
    {U0 : Set (ProbePair d × ℝ)}
    (patch : CoefficientSeparatingProductPatch A U0)
    (hquadratic : QuadricProbeSliceQuadraticCoefficientSeparation A patch.Uq)
    (gamma0 gamma1 : ℂ)
    (M R : ℝ → Matrix (Fin d) (Fin d) ℝ)
    (i j : Fin d)
    (hAij : A i j ≠ 0)
    (hentry_affine :
      ∃ a0 a1 : ℂ, ∀ t : ℝ, t ∈ patch.J →
        formalX (paramStream θ) level (gateAssignmentOfTail t tail) i j =
          a0 + a1 * (t : ℂ))
    (hXres :
      ∀ t : ℝ, t ∈ patch.J →
        formalX (paramStream θ) level (gateAssignmentOfTail t tail)
            - (gamma0 + gamma1 * (t : ℂ)) • matC A =
          matC (M t))
    (hYres :
      ∀ t : ℝ, t ∈ patch.J →
        formalY (paramStream θ) level (gateAssignmentOfTail t tail)
          + (formalY (paramStream θ) level (gateAssignmentOfTail t tail))ᵀ =
          matC (R t))
    (hzero :
      ∀ p : ProbePair d, p ∈ patch.Uq → ∀ t : ℝ, t ∈ patch.J →
        specializedPhi θ level (gateAssignmentOfTail t tail) p = 0) :
    ∃ Gamma0 Gamma1 : ℂ,
      (∀ t : ℝ, t ∈ patch.J →
        formalX (paramStream θ) level (gateAssignmentOfTail t tail) =
          (Gamma0 + Gamma1 * (t : ℂ)) • matC A) ∧
      (∀ t : ℝ, t ∈ patch.J →
        formalY (paramStream θ) level (gateAssignmentOfTail t tail)
          + (formalY (paramStream θ) level (gateAssignmentOfTail t tail))ᵀ = 0) := by
  exact product_patch_formalXY_affine_on_J_of_quadratic_coefficient_separation
    patch hquadratic gamma0 gamma1 M R hXres hYres hzero
    (fun gamma hX =>
      scalar_affine_on_J_of_formalX_entry_affine patch gamma0 gamma1 gamma i j hAij
        hentry_affine hX)

/-! ## Provider and constructor -/

/-- Post-`lem:quadA` slice data sufficient for the polynomial-upgrade part of
`lem:cascade`(b).

The scalar has already been written as `γ₀ + γ₁ z`, as in the trace-formula step of the
paper proof.  The slice set may be an open interval; only infinitude is needed for the
algebraic upgrade. -/
structure CascadeCurveRigidityProvider {L d : Nat} (θ : Params L d)
    (A : Matrix (Fin d) (Fin d) ℝ) (level : Nat) (tail : Nat → ℝ) where
  gamma0 : ℂ
  gamma1 : ℂ
  slice : Set ℝ
  slice_infinite : slice.Infinite
  formalX_slice :
    ∀ t : ℝ, t ∈ slice →
      formalX (paramStream θ) level (gateAssignmentOfTail t tail) =
        (gamma0 + gamma1 * (t : ℂ)) • matC A
  formalY_slice :
    ∀ t : ℝ, t ∈ slice →
      formalY (paramStream θ) level (gateAssignmentOfTail t tail)
        + (formalY (paramStream θ) level (gateAssignmentOfTail t tail))ᵀ = 0

namespace CascadeCurveRigidityProvider

variable {L d : Nat} {θ : Params L d} {A : Matrix (Fin d) (Fin d) ℝ}
variable {level : Nat} {tail : Nat → ℝ}

noncomputable def gamma (D : CascadeCurveRigidityProvider θ A level tail) (z : ℂ) : ℂ :=
  D.gamma0 + D.gamma1 * z

theorem formalX_all_complex (D : CascadeCurveRigidityProvider θ A level tail) (z : ℂ) :
    formalX (paramStream θ) level (complexGateAssignmentOfTail z tail) =
      D.gamma z • matC A := by
  have hzero :
      (curveXResidualPoly (paramStream θ) A level tail D.gamma0 D.gamma1).map
          (fun p : Polynomial ℂ => p.eval z) = 0 := by
    apply matrix_polynomial_eval_zero_of_real_slice D.slice_infinite
    intro t ht
    rw [eval_curveXResidualPoly]
    simpa [gateAssignmentOfTail, gamma] using sub_eq_zero.mpr (D.formalX_slice t ht)
  rw [eval_curveXResidualPoly] at hzero
  exact sub_eq_zero.mp (by simpa [gamma] using hzero)

theorem formalY_all_complex (D : CascadeCurveRigidityProvider θ A level tail) (z : ℂ) :
    formalY (paramStream θ) level (complexGateAssignmentOfTail z tail)
        + (formalY (paramStream θ) level (complexGateAssignmentOfTail z tail))ᵀ = 0 := by
  have hzero :
      (curveYSymPoly (paramStream θ) level tail).map (fun p : Polynomial ℂ => p.eval z) = 0 := by
    apply matrix_polynomial_eval_zero_of_real_slice D.slice_infinite
    intro t ht
    rw [eval_curveYSymPoly]
    simpa [gateAssignmentOfTail] using D.formalY_slice t ht
  rwa [eval_curveYSymPoly] at hzero

/-- Polynomial-upgrade constructor for the R3 zero branch. -/
noncomputable def toCascadeCurveRigidityData
    (D : CascadeCurveRigidityProvider θ A level tail) :
    CascadeCurveRigidityData θ A level tail where
  gamma := D.gamma
  gamma_affine := ⟨D.gamma0, D.gamma1, by intro z; rfl⟩
  curve_identity := by
    intro z p
    exact specializedPhi_eq_gamma_matrixBilin_of_formalXY θ A level tail (D.gamma z) z
      (D.formalX_all_complex z) (D.formalY_all_complex z) p

end CascadeCurveRigidityProvider

/-- The top-level constructor form of `CascadeCurveRigidityProvider.toCascadeCurveRigidityData`. -/
noncomputable def cascadeCurveRigidityData_of_provider {L d : Nat} {θ : Params L d}
    {A : Matrix (Fin d) (Fin d) ℝ} {level : Nat} {tail : Nat → ℝ}
    (D : CascadeCurveRigidityProvider θ A level tail) :
    CascadeCurveRigidityData θ A level tail :=
  D.toCascadeCurveRigidityData

/-- Provider-form constructor from the post-`lem:quadA` slice identities on an infinite real
set. -/
noncomputable def cascadeCurveRigidityProvider_of_formalXY_on_infinite {L d : Nat}
    {θ : Params L d} {A : Matrix (Fin d) (Fin d) ℝ} {level : Nat} {tail : Nat → ℝ}
    (gamma0 gamma1 : ℂ) (slice : Set ℝ) (hslice : slice.Infinite)
    (hX :
      ∀ t : ℝ, t ∈ slice →
        formalX (paramStream θ) level (gateAssignmentOfTail t tail) =
          (gamma0 + gamma1 * (t : ℂ)) • matC A)
    (hY :
      ∀ t : ℝ, t ∈ slice →
        formalY (paramStream θ) level (gateAssignmentOfTail t tail)
          + (formalY (paramStream θ) level (gateAssignmentOfTail t tail))ᵀ = 0) :
    CascadeCurveRigidityProvider θ A level tail :=
  { gamma0 := gamma0
    gamma1 := gamma1
    slice := slice
    slice_infinite := hslice
    formalX_slice := hX
    formalY_slice := hY }

/-- Product-patch constructor for the zero branch, in provider form.

The coefficient-separating product patch supplies the open nonempty real slice `J`; the
per-slice rigidity identities are kept explicit as the remaining `lem:quadA` output. -/
noncomputable def cascadeCurveRigidityProvider_of_product_patch_formalXY_on_J {L d : Nat}
    {θ : Params L d} {A : Matrix (Fin d) (Fin d) ℝ} {level : Nat} {tail : Nat → ℝ}
    {U0 : Set (ProbePair d × ℝ)}
    (patch : CoefficientSeparatingProductPatch A U0)
    (gamma0 gamma1 : ℂ)
    (hX :
      ∀ t : ℝ, t ∈ patch.J →
        formalX (paramStream θ) level (gateAssignmentOfTail t tail) =
          (gamma0 + gamma1 * (t : ℂ)) • matC A)
    (hY :
      ∀ t : ℝ, t ∈ patch.J →
        formalY (paramStream θ) level (gateAssignmentOfTail t tail)
          + (formalY (paramStream θ) level (gateAssignmentOfTail t tail))ᵀ = 0) :
    CascadeCurveRigidityProvider θ A level tail :=
  cascadeCurveRigidityProvider_of_formalXY_on_infinite gamma0 gamma1 patch.J
    patch.J_infinite hX hY

/-- Product-patch provider constructor for the zero branch from the quadratic handoff,
using affine control of one nonzero `formalX` entry to finish the scalar upgrade. -/
noncomputable def cascadeCurveRigidityProvider_of_product_patch_quadratic_zero_branch_entry_affine
    {L d : Nat}
    {θ : Params L d} {A : Matrix (Fin d) (Fin d) ℝ} {level : Nat} {tail : Nat → ℝ}
    {U0 : Set (ProbePair d × ℝ)}
    (patch : CoefficientSeparatingProductPatch A U0)
    (hquadratic : QuadricProbeSliceQuadraticCoefficientSeparation A patch.Uq)
    (gamma0 gamma1 : ℂ)
    (M R : ℝ → Matrix (Fin d) (Fin d) ℝ)
    (i j : Fin d)
    (hAij : A i j ≠ 0)
    (hentry_affine :
      ∃ a0 a1 : ℂ, ∀ t : ℝ, t ∈ patch.J →
        formalX (paramStream θ) level (gateAssignmentOfTail t tail) i j =
          a0 + a1 * (t : ℂ))
    (hXres :
      ∀ t : ℝ, t ∈ patch.J →
        formalX (paramStream θ) level (gateAssignmentOfTail t tail)
            - (gamma0 + gamma1 * (t : ℂ)) • matC A =
          matC (M t))
    (hYres :
      ∀ t : ℝ, t ∈ patch.J →
        formalY (paramStream θ) level (gateAssignmentOfTail t tail)
          + (formalY (paramStream θ) level (gateAssignmentOfTail t tail))ᵀ =
          matC (R t))
    (hzero :
      ∀ p : ProbePair d, p ∈ patch.Uq → ∀ t : ℝ, t ∈ patch.J →
        specializedPhi θ level (gateAssignmentOfTail t tail) p = 0) :
    CascadeCurveRigidityProvider θ A level tail := by
  let hformalXY :=
    product_patch_formalXY_affine_on_J_of_quadratic_coefficient_separation_entry_affine
      patch hquadratic gamma0 gamma1 M R i j hAij hentry_affine hXres hYres hzero
  let Gamma0 : ℂ := Classical.choose hformalXY
  let Gamma1 : ℂ := Classical.choose (Classical.choose_spec hformalXY)
  have hXY :
      (∀ t : ℝ, t ∈ patch.J →
        formalX (paramStream θ) level (gateAssignmentOfTail t tail) =
          (Gamma0 + Gamma1 * (t : ℂ)) • matC A) ∧
      (∀ t : ℝ, t ∈ patch.J →
        formalY (paramStream θ) level (gateAssignmentOfTail t tail)
          + (formalY (paramStream θ) level (gateAssignmentOfTail t tail))ᵀ = 0) :=
    Classical.choose_spec (Classical.choose_spec hformalXY)
  exact cascadeCurveRigidityProvider_of_product_patch_formalXY_on_J patch Gamma0 Gamma1 hXY.1 hXY.2

/-- Product-patch provider constructor for the zero branch from the quadratic handoff.

This convenience wrapper supplies the affine-control hypothesis for the selected
`formalX` entry from the general first-gate slice affine theorem. -/
noncomputable def cascadeCurveRigidityProvider_of_product_patch_quadratic_zero_branch
    {L d : Nat}
    {θ : Params L d} {A : Matrix (Fin d) (Fin d) ℝ} {level : Nat} {tail : Nat → ℝ}
    {U0 : Set (ProbePair d × ℝ)}
    (patch : CoefficientSeparatingProductPatch A U0)
    (hquadratic : QuadricProbeSliceQuadraticCoefficientSeparation A patch.Uq)
    (gamma0 gamma1 : ℂ)
    (M R : ℝ → Matrix (Fin d) (Fin d) ℝ)
    (i j : Fin d)
    (hAij : A i j ≠ 0)
    (hXres :
      ∀ t : ℝ, t ∈ patch.J →
        formalX (paramStream θ) level (gateAssignmentOfTail t tail)
            - (gamma0 + gamma1 * (t : ℂ)) • matC A =
          matC (M t))
    (hYres :
      ∀ t : ℝ, t ∈ patch.J →
        formalY (paramStream θ) level (gateAssignmentOfTail t tail)
          + (formalY (paramStream θ) level (gateAssignmentOfTail t tail))ᵀ =
          matC (R t))
    (hzero :
      ∀ p : ProbePair d, p ∈ patch.Uq → ∀ t : ℝ, t ∈ patch.J →
        specializedPhi θ level (gateAssignmentOfTail t tail) p = 0) :
    CascadeCurveRigidityProvider θ A level tail :=
  cascadeCurveRigidityProvider_of_product_patch_quadratic_zero_branch_entry_affine
    patch hquadratic gamma0 gamma1 M R i j hAij
    (formalX_gateAssignmentOfTail_entry_affine_on θ level tail i j patch.J)
    hXres hYres hzero

/-- Product-patch provider constructor for the zero branch from the quadratic handoff,
choosing a nonzero matrix entry from `A ≠ 0`. -/
noncomputable def
    cascadeCurveRigidityProvider_of_product_patch_quadratic_zero_branch_of_matrix_ne_zero
    {L d : Nat}
    {θ : Params L d} {A : Matrix (Fin d) (Fin d) ℝ} {level : Nat} {tail : Nat → ℝ}
    {U0 : Set (ProbePair d × ℝ)}
    (patch : CoefficientSeparatingProductPatch A U0)
    (hquadratic : QuadricProbeSliceQuadraticCoefficientSeparation A patch.Uq)
    (gamma0 gamma1 : ℂ)
    (M R : ℝ → Matrix (Fin d) (Fin d) ℝ)
    (hA : A ≠ 0)
    (hXres :
      ∀ t : ℝ, t ∈ patch.J →
        formalX (paramStream θ) level (gateAssignmentOfTail t tail)
            - (gamma0 + gamma1 * (t : ℂ)) • matC A =
          matC (M t))
    (hYres :
      ∀ t : ℝ, t ∈ patch.J →
        formalY (paramStream θ) level (gateAssignmentOfTail t tail)
          + (formalY (paramStream θ) level (gateAssignmentOfTail t tail))ᵀ =
          matC (R t))
    (hzero :
      ∀ p : ProbePair d, p ∈ patch.Uq → ∀ t : ℝ, t ∈ patch.J →
        specializedPhi θ level (gateAssignmentOfTail t tail) p = 0) :
    CascadeCurveRigidityProvider θ A level tail := by
  let hentry := exists_matrix_entry_ne_zero_of_ne_zero hA
  let i : Fin d := Classical.choose hentry
  let j : Fin d := Classical.choose (Classical.choose_spec hentry)
  have hAij : A i j ≠ 0 := Classical.choose_spec (Classical.choose_spec hentry)
  exact cascadeCurveRigidityProvider_of_product_patch_quadratic_zero_branch
    patch hquadratic gamma0 gamma1 M R i j hAij hXres hYres hzero

end TransformerIdentifiability.NLayer
