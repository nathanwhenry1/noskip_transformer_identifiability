import AnyLayerIdentifiabilityProof.NLayer.KHead.Step2.Trichotomy
import AnyLayerIdentifiabilityProof.NLayer.KHead.Step2.Dial
import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.QuadricRigidity
import AnyLayerIdentifiabilityProof.NLayer.KHead.Genericity.Regularity
import AnyLayerIdentifiabilityProof.NLayer.KHead.Step2.Saturated
import AnyLayerIdentifiabilityProof.NLayer.KHead.Step2.DialLimits
import AnyLayerIdentifiabilityProof.NLayer.KHead.FormalStreams
import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.ActiveStratification
import AnyLayerIdentifiabilityProof.NLayer.IDL.CascadeAlphaError
import AnyLayerIdentifiabilityProof.NLayer.KHead.Step2.AlphaSlopeLipschitz

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.KHead

/-!
# K07B.M4/M5 — zero-branch rigidity instantiation

This file instantiates the abstract K07B trichotomy scaffold (`Step2.Trichotomy`)
with a concrete matrix-form polynomial type and proves the mathematical heart of
`lem:zero-branch-rigidity` (`tex_modular/sections/07b`) as a genuine theorem: it
combines quadric rigidity (`lem_quadratic_quadric_rigidity`), polynomial
interpolation (`matrix_eq_of_infinite_eval_eq`), and the genericity data of
`Regularity`.

The "deeper slope" polynomial is given in the Step-1 *matrix form* of the TeX proof:
```
  Φ(z; w, v) = wᵀ X(z) v + wᵀ Y(z) w,      X(z) = (B - zV)ᵀ Y₀,
  Y(z) = (B - zV)ᵀ RtAlb (P(S + zV) + Q(B - zV)),
```
with `B := I + V`, `C₁ := B + S`, `Y₀ := RtAlb · P · C₁`.  The building-block matrices
`V, S, RtAlb, P, Q` are taken as given (faithfulness of these to the true transformer
products is the separate later milestone M6/M7); the rigidity argument itself is real
mathematics and is proved here as a genuine theorem, with no proof placeholders.

## The two `matrixBilin` hazard

There are two rfl-equal but distinct declarations named `matrixBilin`: the parent
`NLayer.matrixBilin` (used by `lem_quadratic_quadric_rigidity`) and the `KHead`
`matrixBilin` (used by `firstHeadQuadric`/`quadricPatch`).  We define the dial
evaluation `dialEval` and the target `zeroDialForm` with the fully-qualified parent
`NLayer.matrixBilin`, and bridge the quadric membership condition with the rfl lemma
`firstHeadSlope_eq_matrixBilin`.
-/

/-! ## Polynomial-matrix evaluation is a ring homomorphism -/

/-- Lift a real matrix to a polynomial matrix by the constant embedding. -/
noncomputable def liftC {d : Nat} (M : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) (Polynomial ℝ) :=
  M.map (Polynomial.C)

@[simp] theorem eval_liftC {d : Nat} (t : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    evalPolynomialMatrix t (liftC M) = M := by
  ext i j; simp [evalPolynomialMatrix, liftC]

@[simp] theorem eval_zeroMatrix {d : Nat} (t : ℝ) :
    evalPolynomialMatrix t (0 : Matrix (Fin d) (Fin d) (Polynomial ℝ)) = 0 := by
  ext i j; simp [evalPolynomialMatrix]

@[simp] theorem eval_add {d : Nat} (t : ℝ) (M N : Matrix (Fin d) (Fin d) (Polynomial ℝ)) :
    evalPolynomialMatrix t (M + N) = evalPolynomialMatrix t M + evalPolynomialMatrix t N := by
  ext i j; simp [evalPolynomialMatrix]

@[simp] theorem eval_sub {d : Nat} (t : ℝ) (M N : Matrix (Fin d) (Fin d) (Polynomial ℝ)) :
    evalPolynomialMatrix t (M - N) = evalPolynomialMatrix t M - evalPolynomialMatrix t N := by
  ext i j; simp [evalPolynomialMatrix]

@[simp] theorem eval_mul {d : Nat} (t : ℝ) (M N : Matrix (Fin d) (Fin d) (Polynomial ℝ)) :
    evalPolynomialMatrix t (M * N) = evalPolynomialMatrix t M * evalPolynomialMatrix t N := by
  ext i j
  simp only [evalPolynomialMatrix, Matrix.mul_apply, Polynomial.eval_finsetSum,
    Polynomial.eval_mul]

@[simp] theorem eval_transpose {d : Nat} (t : ℝ) (M : Matrix (Fin d) (Fin d) (Polynomial ℝ)) :
    evalPolynomialMatrix t (Mᵀ) = (evalPolynomialMatrix t M)ᵀ := by
  ext i j; simp [evalPolynomialMatrix]

@[simp] theorem eval_Xsmul {d : Nat} (t : ℝ) (M : Matrix (Fin d) (Fin d) (Polynomial ℝ)) :
    evalPolynomialMatrix t ((Polynomial.X : Polynomial ℝ) • M) = t • evalPolynomialMatrix t M := by
  ext i j
  simp only [evalPolynomialMatrix, Matrix.smul_apply, smul_eq_mul, Polynomial.eval_mul,
    Polynomial.eval_X]

@[simp] theorem eval_polySmul {d : Nat} (t : ℝ) (p : Polynomial ℝ)
    (M : Matrix (Fin d) (Fin d) (Polynomial ℝ)) :
    evalPolynomialMatrix t (p • M) = (Polynomial.eval t p) • evalPolynomialMatrix t M := by
  ext i j
  simp only [evalPolynomialMatrix, Matrix.smul_apply, smul_eq_mul, Polynomial.eval_mul]

theorem liftC_transpose {d : Nat} (M : Matrix (Fin d) (Fin d) ℝ) :
    (liftC M)ᵀ = liftC Mᵀ := by
  unfold liftC; rw [Matrix.transpose_map]

theorem liftC_mul {d : Nat} (M N : Matrix (Fin d) (Fin d) ℝ) :
    liftC (M * N) = liftC M * liftC N := by
  unfold liftC; rw [Matrix.map_mul]

@[simp] theorem liftC_zero {d : Nat} : liftC (0 : Matrix (Fin d) (Fin d) ℝ) = 0 := by
  ext i j; simp [liftC]

/-! ## Coefficient extraction from a vanishing quadratic matrix polynomial -/

/-- A matrix polynomial `M₀ + t M₁ + t² M₂` vanishing for every real `t` has all
coefficient matrices zero. -/
theorem matrix_poly_coeffs_zero {d : Nat} {M0 M1 M2 : Matrix (Fin d) (Fin d) ℝ}
    (h : ∀ t : ℝ, M0 + t • M1 + t ^ 2 • M2 = 0) :
    M0 = 0 ∧ M1 = 0 ∧ M2 = 0 := by
  have h0 : M0 = 0 := by have := h 0; simpa using this
  have e1 : M1 + M2 = 0 := by have := h 1; rw [h0] at this; simpa using this
  have e2 : -M1 + M2 = 0 := by
    have := h (-1); rw [h0] at this
    simpa [neg_smul] using this
  have hM1 : M1 = 0 := by
    have hcancel : M1 = -M1 := add_right_cancel (b := M2) (by rw [e1, e2])
    have h2 : M1 + M1 = 0 := by
      have := congrArg (· + M1) hcancel
      simpa using this
    have hsm : (2 : ℝ) • M1 = 0 := by rw [two_smul]; exact h2
    rcases smul_eq_zero.mp hsm with h2z | h2z
    · norm_num at h2z
    · exact h2z
  have hM2 : M2 = 0 := by
    have := e1; rw [hM1] at this; simpa using this
  exact ⟨h0, hM1, hM2⟩

/-- `Sym M = 0` unfolds to the additive symmetry `M + Mᵀ = 0`. -/
theorem add_transpose_eq_zero_of_sym_eq_zero {d : Nat} {M : Matrix (Fin d) (Fin d) ℝ}
    (h : sym M = 0) : M + Mᵀ = 0 := by
  rw [sym] at h
  rcases smul_eq_zero.mp h with h2 | h2
  · norm_num at h2
  · exact h2

/-! ## The concrete matrix-form dial polynomial -/

/-- Building-block data for the Step-1 matrix form of the deeper-slope polynomial.

`V` and `S` are the first-layer value blocks (`V = V_h`, `S = ∑_{a≠h} V_{1a}` in the
faithful instantiation); `RtAlb = Rᵀ A_{ℓb}`, `P`, `Q` are the deeper products. -/
structure QuadraticDialForm (d : Nat) where
  V : Matrix (Fin d) (Fin d) ℝ
  S : Matrix (Fin d) (Fin d) ℝ
  RtAlb : Matrix (Fin d) (Fin d) ℝ
  P : Matrix (Fin d) (Fin d) ℝ
  Q : Matrix (Fin d) (Fin d) ℝ

namespace QuadraticDialForm

variable {d : Nat}

/-- `B := I + V`. -/
def B (Φ : QuadraticDialForm d) : Matrix (Fin d) (Fin d) ℝ := 1 + Φ.V
/-- `C₁ := B + S`. -/
def C1 (Φ : QuadraticDialForm d) : Matrix (Fin d) (Fin d) ℝ := Φ.B + Φ.S
/-- `Y₀ := RtAlb · P · C₁`. -/
def Y0 (Φ : QuadraticDialForm d) : Matrix (Fin d) (Fin d) ℝ := Φ.RtAlb * Φ.P * Φ.C1

/-- The affine polynomial matrix `B - z V`. -/
noncomputable def BzV (Φ : QuadraticDialForm d) : Matrix (Fin d) (Fin d) (Polynomial ℝ) :=
  liftC Φ.B - (Polynomial.X : Polynomial ℝ) • liftC Φ.V

/-- `X(z) = (B - zV)ᵀ Y₀`, entries affine in `z`. -/
noncomputable def Xpoly (Φ : QuadraticDialForm d) : Matrix (Fin d) (Fin d) (Polynomial ℝ) :=
  Φ.BzVᵀ * liftC Φ.Y0

/-- `Y(z) = (B - zV)ᵀ RtAlb (P(S + zV) + Q(B - zV))`, entries of degree `≤ 2` in `z`. -/
noncomputable def Ypoly (Φ : QuadraticDialForm d) : Matrix (Fin d) (Fin d) (Polynomial ℝ) :=
  Φ.BzVᵀ * liftC Φ.RtAlb *
    (liftC Φ.P * (liftC Φ.S + (Polynomial.X : Polynomial ℝ) • liftC Φ.V) +
      liftC Φ.Q * Φ.BzV)

/-- The real matrix `B - t V`. -/
def BzVr (Φ : QuadraticDialForm d) (t : ℝ) : Matrix (Fin d) (Fin d) ℝ := Φ.B - t • Φ.V
/-- `X(t)` as a real matrix. -/
def Xfun (Φ : QuadraticDialForm d) (t : ℝ) : Matrix (Fin d) (Fin d) ℝ := (Φ.BzVr t)ᵀ * Φ.Y0
/-- `Y(t)` as a real matrix. -/
def Yfun (Φ : QuadraticDialForm d) (t : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  (Φ.BzVr t)ᵀ * Φ.RtAlb * (Φ.P * (Φ.S + t • Φ.V) + Φ.Q * Φ.BzVr t)

@[simp] theorem eval_BzV (Φ : QuadraticDialForm d) (t : ℝ) :
    evalPolynomialMatrix t Φ.BzV = Φ.BzVr t := by simp [BzV, BzVr]
@[simp] theorem eval_Xpoly (Φ : QuadraticDialForm d) (t : ℝ) :
    evalPolynomialMatrix t Φ.Xpoly = Φ.Xfun t := by simp [Xpoly, Xfun]
@[simp] theorem eval_Ypoly (Φ : QuadraticDialForm d) (t : ℝ) :
    evalPolynomialMatrix t Φ.Ypoly = Φ.Yfun t := by simp [Ypoly, Yfun]

/-- The affine decomposition of `X(z)`: `X₀ = Bᵀ Y₀`, `X₁ = -Vᵀ Y₀`. -/
theorem Xpoly_eq (Φ : QuadraticDialForm d) :
    Φ.Xpoly = liftC (Φ.Bᵀ * Φ.Y0) - (Polynomial.X : Polynomial ℝ) • liftC (Φ.Vᵀ * Φ.Y0) := by
  rw [Xpoly, BzV, Matrix.transpose_sub, Matrix.transpose_smul, liftC_transpose, liftC_transpose,
    Matrix.sub_mul, smul_mul_assoc, liftC_mul, liftC_mul]

/-! ## Step 5: the coefficient case analysis (genuine matrix algebra) -/

/-- **Step 5 (coefficient case analysis of `lem:zero-branch-rigidity`).**

From the two coefficient identities `Bᵀ Y₀ = γ₀ A_h`, `-Vᵀ Y₀ = γ₁ A_h`, the club
identity `Y(t) + Y(t)ᵀ = 0` for all `t`, and the genericity data (`det A_h ≠ 0`,
`Sym A_h ≠ 0`, `V ≠ 0`), the affine slope coefficients both vanish. -/
theorem gamma_eq_zero (Φ : QuadraticDialForm d)
    (Ah : Matrix (Fin d) (Fin d) ℝ) (γ0 γ1 : ℝ) (hdpos : 0 < d)
    (hc0 : Φ.Bᵀ * Φ.Y0 = γ0 • Ah)
    (hc1 : -(Φ.Vᵀ * Φ.Y0) = γ1 • Ah)
    (hclub : ∀ t : ℝ, Φ.Yfun t + (Φ.Yfun t)ᵀ = 0)
    (hdetA : Ah.det ≠ 0)
    (hsymA : sym Ah ≠ 0)
    (hVne : Φ.V ≠ 0) :
    γ0 = 0 ∧ γ1 = 0 := by
  have detY0_of_left : ∀ c : ℝ, c ≠ 0 → Φ.Bᵀ * Φ.Y0 = c • Ah → Φ.Y0.det ≠ 0 := by
    intro c hc he
    have hprod : (Φ.Bᵀ * Φ.Y0).det ≠ 0 := by
      rw [he, Matrix.det_smul]; exact mul_ne_zero (pow_ne_zero _ hc) hdetA
    rw [Matrix.det_mul] at hprod
    exact fun hy => hprod (by rw [hy, mul_zero])
  have detY0_of_right : ∀ c : ℝ, c ≠ 0 → Φ.Vᵀ * Φ.Y0 = c • Ah → Φ.Y0.det ≠ 0 := by
    intro c hc he
    have hprod : (Φ.Vᵀ * Φ.Y0).det ≠ 0 := by
      rw [he, Matrix.det_smul]; exact mul_ne_zero (pow_ne_zero _ hc) hdetA
    rw [Matrix.det_mul] at hprod
    exact fun hy => hprod (by rw [hy, mul_zero])
  have cancelY0 : ∀ M : Matrix (Fin d) (Fin d) ℝ, Φ.Y0.det ≠ 0 → M * Φ.Y0 = 0 → M = 0 := by
    intro M hdet hM
    have : M * Φ.Y0 * Φ.Y0⁻¹ = 0 := by rw [hM, Matrix.zero_mul]
    rwa [Matrix.mul_assoc, Matrix.mul_nonsing_inv Φ.Y0 (isUnit_iff_ne_zero.mpr hdet),
      Matrix.mul_one] at this
  by_contra hcon
  rw [not_and_or] at hcon
  rcases eq_or_ne γ0 0 with hγ0 | hγ0
  · -- γ₀ = 0 ⟹ (case b) γ₁ ≠ 0.
    rcases hcon with hcon0 | hγ1
    · exact hcon0 hγ0
    · have hB0 : Φ.Bᵀ * Φ.Y0 = 0 := by rw [hc0, hγ0, zero_smul]
      have hVY : Φ.Vᵀ * Φ.Y0 = (-γ1) • Ah := by
        have := hc1; rw [neg_eq_iff_eq_neg] at this; rw [this, neg_smul]
      have hdetY0 : Φ.Y0.det ≠ 0 := detY0_of_right (-γ1) (by simpa using hγ1) hVY
      have hBt0 : Φ.Bᵀ = 0 := cancelY0 _ hdetY0 hB0
      have hB0m : Φ.B = 0 := by
        have := congrArg Matrix.transpose hBt0; simpa using this
      have hVm : Φ.V = -1 := by
        have hBV : (1 : Matrix (Fin d) (Fin d) ℝ) + Φ.V = 0 := hB0m
        exact eq_neg_of_add_eq_zero_right hBV
      -- Normal form of Y(t): `t • (RtAlb P S) + t² • (RtAlb (Q - P))`.
      have hnf : ∀ t : ℝ, Φ.Yfun t
          = t • (Φ.RtAlb * Φ.P * Φ.S) + (t ^ 2) • (Φ.RtAlb * (Φ.Q - Φ.P)) := by
        intro t
        rw [Yfun, BzVr, hVm, hB0m]
        have hbz : (0 : Matrix (Fin d) (Fin d) ℝ) - t • (-1 : Matrix (Fin d) (Fin d) ℝ)
            = t • 1 := by simp
        rw [hbz, Matrix.transpose_smul, Matrix.transpose_one]
        simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_add,
          Matrix.mul_sub, mul_neg, mul_one, smul_sub, smul_smul, Matrix.mul_assoc]
        match_scalars <;> ring
      have hcoeff := matrix_poly_coeffs_zero (M0 := 0)
        (M1 := (Φ.RtAlb * Φ.P * Φ.S) + (Φ.RtAlb * Φ.P * Φ.S)ᵀ)
        (M2 := (Φ.RtAlb * (Φ.Q - Φ.P)) + (Φ.RtAlb * (Φ.Q - Φ.P))ᵀ)
        (by
          intro t
          have hct := hclub t
          rw [hnf t] at hct
          conv_rhs => rw [← hct]
          simp only [Matrix.transpose_add, Matrix.transpose_smul]
          match_scalars <;> ring)
      have hY0S : Φ.Y0 = Φ.RtAlb * Φ.P * Φ.S := by
        rw [Y0, C1, hB0m, zero_add]
      have hsymY0 : Φ.Y0 + Φ.Y0ᵀ = 0 := by rw [hY0S]; exact hcoeff.2.1
      have hY0A : Φ.Y0 = γ1 • Ah := by
        have hVt : Φ.Vᵀ = -1 := by rw [hVm]; simp
        have := hc1; rw [hVt] at this
        simpa using this
      have hsymA0 : γ1 • (Ah + Ahᵀ) = 0 := by
        have : (γ1 • Ah) + (γ1 • Ah)ᵀ = 0 := by rw [← hY0A]; exact hsymY0
        rw [Matrix.transpose_smul, ← smul_add] at this; exact this
      have hAsym : Ah + Ahᵀ = 0 := by
        rcases smul_eq_zero.mp hsymA0 with h | h
        · exact absurd h (by simpa using hγ1)
        · exact h
      exact hsymA (by rw [sym, hAsym]; simp)
  · rcases eq_or_ne γ1 0 with hγ1 | hγ1
    · -- case (a): γ₁ = 0 ⟹ Vᵀ Y₀ = 0, Y₀ invertible ⟹ V = 0.
      have hVY0 : Φ.Vᵀ * Φ.Y0 = 0 := by
        have := hc1; rw [hγ1, zero_smul, neg_eq_zero] at this; exact this
      have hdetY0 : Φ.Y0.det ≠ 0 := detY0_of_left γ0 hγ0 hc0
      have hVt0 : Φ.Vᵀ = 0 := cancelY0 _ hdetY0 hVY0
      have hV0 : Φ.V = 0 := by
        have := congrArg Matrix.transpose hVt0; simpa using this
      exact hVne hV0
    · -- case (c): γ₀ ≠ 0, γ₁ ≠ 0.
      have hdetY0 : Φ.Y0.det ≠ 0 := detY0_of_left γ0 hγ0 hc0
      set c : ℝ := -γ1 * γ0⁻¹ with hc_def
      have hc_ne : c ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hγ1) (inv_ne_zero hγ0)
      have hcg : c * γ0 = -γ1 := by rw [hc_def]; field_simp
      have hVeq : Φ.Vᵀ = c • Φ.Bᵀ := by
        have hzero : Φ.Vᵀ * Φ.Y0 - c • (Φ.Bᵀ * Φ.Y0) = 0 := by
          have e1 : Φ.Vᵀ * Φ.Y0 = (-γ1) • Ah := by
            have := hc1; rw [neg_eq_iff_eq_neg] at this; rw [this, neg_smul]
          rw [e1, hc0, smul_smul, hcg, ← sub_smul, sub_self, zero_smul]
        have hsub : (Φ.Vᵀ - c • Φ.Bᵀ) * Φ.Y0 = 0 := by
          rw [Matrix.sub_mul, smul_mul_assoc]; exact hzero
        exact sub_eq_zero.mp (cancelY0 _ hdetY0 hsub)
      have hVB : Φ.V = c • Φ.B := by
        have := congrArg Matrix.transpose hVeq
        rwa [Matrix.transpose_transpose, Matrix.transpose_smul, Matrix.transpose_transpose] at this
      have hBself : Φ.B = 1 + c • Φ.B := by
        have hBdef : Φ.B = 1 + Φ.V := rfl
        rwa [hVB] at hBdef
      have hBeq : (1 - c) • Φ.B = (1 : Matrix (Fin d) (Fin d) ℝ) := by
        linear_combination (norm := module) hBself
      have hc1_ne : (1 : ℝ) - c ≠ 0 := by
        intro h0
        rw [h0, zero_smul] at hBeq
        have h10 : (1 : Matrix (Fin d) (Fin d) ℝ) = 0 := hBeq.symm
        have i0 : Fin d := ⟨0, hdpos⟩
        have := congrFun (congrFun h10 i0) i0
        simp at this
      have hBinv : Φ.B = (1 - c)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) := by
        have := congrArg (fun M => (1 - c)⁻¹ • M) hBeq
        simp only [smul_smul, inv_mul_cancel₀ hc1_ne, one_smul] at this
        exact this
      set ν : ℝ := c * (1 - c)⁻¹ with hν_def
      have hν1 : 1 + ν = (1 - c)⁻¹ := by rw [hν_def]; field_simp; ring
      have hBν : Φ.B = (1 + ν) • (1 : Matrix (Fin d) (Fin d) ℝ) := by rw [hBinv, hν1]
      have hVν : Φ.V = ν • (1 : Matrix (Fin d) (Fin d) ℝ) := by
        rw [hVB, hBinv, smul_smul, ← hν_def]
      have hν_ne : ν ≠ 0 := mul_ne_zero hc_ne (inv_ne_zero hc1_ne)
      have hν1_ne : (1 : ℝ) + ν ≠ 0 := by rw [hν1]; exact inv_ne_zero hc1_ne
      -- Normal form of Y(t) with V = ν•1, B = (1+ν)•1.
      have hnf : ∀ t : ℝ, Φ.Yfun t
          = ((1 + ν)) • (Φ.RtAlb * (Φ.P * Φ.S)) + ((1 + ν) ^ 2) • (Φ.RtAlb * Φ.Q)
            + t • (-ν • (Φ.RtAlb * (Φ.P * Φ.S)) + (ν * (1 + ν)) • (Φ.RtAlb * Φ.P)
                - (2 * (1 + ν) * ν) • (Φ.RtAlb * Φ.Q))
            + t ^ 2 • (-(ν ^ 2) • (Φ.RtAlb * Φ.P) + (ν ^ 2) • (Φ.RtAlb * Φ.Q)) := by
        intro t
        rw [Yfun, BzVr, hVν, hBν]
        simp only [Matrix.transpose_smul, Matrix.transpose_one, Matrix.transpose_sub,
          Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
          Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
          smul_add, smul_sub, smul_smul, Matrix.mul_assoc]
        match_scalars <;> ring
      have hcoeff := matrix_poly_coeffs_zero
        (M0 := (((1 + ν)) • (Φ.RtAlb * (Φ.P * Φ.S)) + ((1 + ν) ^ 2) • (Φ.RtAlb * Φ.Q))
          + (((1 + ν)) • (Φ.RtAlb * (Φ.P * Φ.S)) + ((1 + ν) ^ 2) • (Φ.RtAlb * Φ.Q))ᵀ)
        (M1 := ((-ν • (Φ.RtAlb * (Φ.P * Φ.S)) + (ν * (1 + ν)) • (Φ.RtAlb * Φ.P)
                - (2 * (1 + ν) * ν) • (Φ.RtAlb * Φ.Q)))
          + ((-ν • (Φ.RtAlb * (Φ.P * Φ.S)) + (ν * (1 + ν)) • (Φ.RtAlb * Φ.P)
                - (2 * (1 + ν) * ν) • (Φ.RtAlb * Φ.Q)))ᵀ)
        (M2 := (-(ν ^ 2) • (Φ.RtAlb * Φ.P) + (ν ^ 2) • (Φ.RtAlb * Φ.Q))
          + (-(ν ^ 2) • (Φ.RtAlb * Φ.P) + (ν ^ 2) • (Φ.RtAlb * Φ.Q))ᵀ)
        (by
          intro t
          have hct := hclub t
          rw [hnf t] at hct
          rw [← hct]
          simp only [Matrix.transpose_add, Matrix.transpose_smul]
          match_scalars <;> ring)
      -- From the `t²` coefficient: `s(RtAlb Q) = s(RtAlb P)`.
      have hzy : (Φ.RtAlb * Φ.Q) + (Φ.RtAlb * Φ.Q)ᵀ
          = (Φ.RtAlb * Φ.P) + (Φ.RtAlb * Φ.P)ᵀ := by
        have h2 := hcoeff.2.2
        have hsm : (ν ^ 2) • (((Φ.RtAlb * Φ.Q) + (Φ.RtAlb * Φ.Q)ᵀ)
            - ((Φ.RtAlb * Φ.P) + (Φ.RtAlb * Φ.P)ᵀ)) = 0 := by
          rw [← h2]
          simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_neg]
          match_scalars <;> ring
        rcases smul_eq_zero.mp hsm with h | h
        · exact absurd h (pow_ne_zero _ hν_ne)
        · exact sub_eq_zero.mp h
      -- From the `t⁰` coefficient combined with `hzy`: `Sym Y₀ = 0`.
      have hsymY0 : Φ.Y0 + Φ.Y0ᵀ = 0 := by
        have h0 := hcoeff.1
        have hY0eq : Φ.Y0 = Φ.RtAlb * (Φ.P * Φ.S) + (1 + ν) • (Φ.RtAlb * Φ.P) := by
          rw [Y0, C1, hBν]
          simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_assoc]
          match_scalars <;> ring
        have hQP : (Φ.RtAlb * Φ.Q)ᵀ
            = (Φ.RtAlb * Φ.P) + (Φ.RtAlb * Φ.P)ᵀ - (Φ.RtAlb * Φ.Q) := by
          linear_combination (norm := module) hzy
        have hsm0 : (1 + ν) • (((Φ.RtAlb * (Φ.P * Φ.S)) + (Φ.RtAlb * (Φ.P * Φ.S))ᵀ)
            + (1 + ν) • ((Φ.RtAlb * Φ.P) + (Φ.RtAlb * Φ.P)ᵀ)) = 0 := by
          rw [← h0]
          simp only [Matrix.transpose_add, Matrix.transpose_smul]
          rw [hQP]
          match_scalars <;> ring
        have hpre : ((Φ.RtAlb * (Φ.P * Φ.S)) + (Φ.RtAlb * (Φ.P * Φ.S))ᵀ)
            + (1 + ν) • ((Φ.RtAlb * Φ.P) + (Φ.RtAlb * Φ.P)ᵀ) = 0 := by
          rcases smul_eq_zero.mp hsm0 with h | h
          · exact absurd h hν1_ne
          · exact h
        rw [hY0eq]
        simp only [Matrix.transpose_add, Matrix.transpose_smul]
        rw [← hpre]; match_scalars <;> ring
      have hBt : Φ.Bᵀ = (1 + ν) • (1 : Matrix (Fin d) (Fin d) ℝ) := by rw [hBν]; simp
      have hY0A : (1 + ν) • Φ.Y0 = γ0 • Ah := by
        have := hc0; rw [hBt] at this; rw [← this, Matrix.smul_mul, Matrix.one_mul]
      have hsymA0 : γ0 • (Ah + Ahᵀ) = 0 := by
        have hstep : (1 + ν) • (Φ.Y0 + Φ.Y0ᵀ) = 0 := by rw [hsymY0, smul_zero]
        rw [smul_add, hY0A] at hstep
        have hT : (1 + ν) • Φ.Y0ᵀ = γ0 • Ahᵀ := by
          have := congrArg Matrix.transpose hY0A
          rwa [Matrix.transpose_smul, Matrix.transpose_smul] at this
        rw [hT, ← smul_add] at hstep
        exact hstep
      have hAsym : Ah + Ahᵀ = 0 := by
        rcases smul_eq_zero.mp hsymA0 with h | h
        · exact absurd h hγ0
        · exact h
      exact hsymA (by rw [sym, hAsym]; simp)

end QuadraticDialForm

/-! ## The abstract-scaffold instantiation -/

/-- The dial evaluation `Λ[Φ](w,v,t) = wᵀ X(t) v + wᵀ Y(t) w`, written with the
**parent** `NLayer.matrixBilin` so it feeds `lem_quadratic_quadric_rigidity`. -/
noncomputable def dialEval {d : Nat} (Φ : QuadraticDialForm d)
    (x : ProbePair d × ℝ) : ℝ :=
  NLayer.matrixBilin (evalPolynomialMatrix x.2 Φ.Xpoly) x.1.1 x.1.2 +
    NLayer.matrixBilin (evalPolynomialMatrix x.2 Φ.Ypoly) x.1.1 x.1.1

/-- The concrete dial polynomial evaluates continuously on probe/time space. -/
theorem continuous_dialEval {d : Nat} (Φ : QuadraticDialForm d) :
    Continuous (dialEval Φ) := by
  unfold dialEval NLayer.matrixBilin evalPolynomialMatrix Matrix.mulVec dotProduct
  fun_prop

/-- On a preconnected set, a continuous real-valued function that never vanishes
has constant positive sign once it is positive at one point. -/
theorem positiveOn_of_preconnected_of_nonzero {α : Type} [TopologicalSpace α]
    {s : Set α} {f : α → ℝ}
    (hs : IsPreconnected s) (hf : Continuous f)
    (hne : ∀ x ∈ s, f x ≠ 0) (hpos : ∃ x ∈ s, 0 < f x) :
    ∀ x ∈ s, 0 < f x := by
  intro x hx
  exact hs.lt_of_ne hf.continuousOn hne hpos hx

/-- On a preconnected set, a continuous real-valued function that never vanishes
has constant negative sign once it is negative at one point. -/
theorem negativeOn_of_preconnected_of_nonzero {α : Type} [TopologicalSpace α]
    {s : Set α} {f : α → ℝ}
    (hs : IsPreconnected s) (hf : Continuous f)
    (hne : ∀ x ∈ s, f x ≠ 0) (hneg : ∃ x ∈ s, f x < 0) :
    ∀ x ∈ s, f x < 0 := by
  intro x hx
  exact hs.gt_of_ne hf.continuousOn hne hneg hx

/-- The positive dial-evaluation locus is open. -/
theorem isOpen_dialEval_pos {d : Nat} (Φ : QuadraticDialForm d) :
    IsOpen {x : ProbePair d × ℝ | 0 < dialEval Φ x} := by
  simpa using isOpen_Ioi.preimage (continuous_dialEval Φ)

/-- The negative dial-evaluation locus is open. -/
theorem isOpen_dialEval_neg {d : Nat} (Φ : QuadraticDialForm d) :
    IsOpen {x : ProbePair d × ℝ | dialEval Φ x < 0} := by
  simpa using isOpen_Iio.preimage (continuous_dialEval Φ)

/-- The nonvanishing dial-evaluation locus is open. -/
theorem isOpen_dialEval_ne_zero {d : Nat} (Φ : QuadraticDialForm d) :
    IsOpen {x : ProbePair d × ℝ | dialEval Φ x ≠ 0} := by
  simpa [ne_eq] using
    isOpen_ne.preimage (continuous_dialEval Φ)

/-- The connected component of the nonvanishing locus through a positive point
has positive dial evaluation everywhere. -/
theorem dialEval_pos_on_nonzero_component {d : Nat} (Φ : QuadraticDialForm d)
    {x0 : ProbePair d × ℝ} (hx0 : 0 < dialEval Φ x0) :
    ∀ x ∈ connectedComponentIn {x : ProbePair d × ℝ | dialEval Φ x ≠ 0} x0,
      0 < dialEval Φ x := by
  apply positiveOn_of_preconnected_of_nonzero isPreconnected_connectedComponentIn
    (continuous_dialEval Φ)
  · intro x hx
    exact connectedComponentIn_subset _ _ hx
  · exact ⟨x0, mem_connectedComponentIn (ne_of_gt hx0), hx0⟩

/-- The connected component of the nonvanishing locus through a negative point
has negative dial evaluation everywhere. -/
theorem dialEval_neg_on_nonzero_component {d : Nat} (Φ : QuadraticDialForm d)
    {x0 : ProbePair d × ℝ} (hx0 : dialEval Φ x0 < 0) :
    ∀ x ∈ connectedComponentIn {x : ProbePair d × ℝ | dialEval Φ x ≠ 0} x0,
      dialEval Φ x < 0 := by
  apply negativeOn_of_preconnected_of_nonzero isPreconnected_connectedComponentIn
    (continuous_dialEval Φ)
  · intro x hx
    exact connectedComponentIn_subset _ _ hx
  · exact ⟨x0, mem_connectedComponentIn (ne_of_lt hx0), hx0⟩

/-- `ZeroPolynomial`: the affine block `X` is the zero matrix and the symmetric part
of `Y` vanishes (encoded as `Y + Yᵀ = 0`). -/
def zeroDialForm {d : Nat} (Φ : QuadraticDialForm d) : Prop :=
  Φ.Xpoly = 0 ∧ Φ.Ypoly + Φ.Ypolyᵀ = 0

/-- Concrete trichotomy predicates instantiating the K07B scaffold with regions
`Set (ProbePair d × ℝ)` inside the quadric-patch cylinder of `A_h`, and polynomials
`QuadraticDialForm d`. -/
noncomputable def dialPredicates {k d : Nat} (A : Fin k → Matrix (Fin d) (Fin d) ℝ)
    (h : Fin k) :
    TrichotomyPredicates (Set (ProbePair d × ℝ)) (QuadraticDialForm d) where
  RegionNonempty U := U.Nonempty
  RegionConnected U := IsPreconnected U
  RegionRelativelyOpen U := RelativelyOpenIn U (quadricPatchCylinder A h)
  RegionSubset U V := U ⊆ V
  PositiveOn Φ U := ∀ x ∈ U, 0 < dialEval Φ x
  NegativeOn Φ U := ∀ x ∈ U, dialEval Φ x < 0
  VanishesOn Φ U := ∀ x ∈ U, dialEval Φ x = 0
  ZeroPolynomial Φ := zeroDialForm Φ
  Estimate _ _ _ _ := True

/-- Concrete estimate payload for the dial trichotomy: every processed deeper
gate has the pointwise `ExpCloseTo` limit prescribed by the current saturated
labels along the head-dial path. -/
structure DialEstimate {m k d : Nat} (r : Nat) (θ : Params (m + 1) k d)
    (head : Fin k) (order : List DeeperHead) (n : Nat)
    (U : Set (ProbePair d × ℝ))
    (labels : DeeperHead → TrichotomyLabel) : Prop where
  gate :
    ∀ {q : Nat} (hqpos : 1 ≤ q) (hq : q < m + 1) (a : Fin k),
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead) ∈
        processedPrefix order n →
      ∀ x : ProbePair d × ℝ, x ∈ U →
        ExpCloseTo
          (fun τ => actualProbeGate r θ
            (headDialPath (attentionMatrix θ 0) head (logScale r) x.1 x.2 τ).1
            (headDialPath (attentionMatrix θ 0) head (logScale r) x.1 x.2 τ).2
            τ ⟨q, hq⟩ a)
          (trichotomyToSaturatedLabels r (m + 1) k labels (q + 1) a)

/-- Concrete dial predicates with the same region/sign clauses as
`dialPredicates`, but with the honest processed-gate estimate payload. -/
noncomputable def dialPredicatesWithEstimate {m k d : Nat} (r : Nat)
    (θ : Params (m + 1) k d) (head : Fin k) :
    TrichotomyPredicates (Set (ProbePair d × ℝ)) (QuadraticDialForm d) where
  RegionNonempty U := U.Nonempty
  RegionConnected U := IsPreconnected U
  RegionRelativelyOpen U :=
    RelativelyOpenIn U (quadricPatchCylinder (attentionMatrix θ 0) head)
  RegionSubset U V := U ⊆ V
  PositiveOn Φ U := ∀ x ∈ U, 0 < dialEval Φ x
  NegativeOn Φ U := ∀ x ∈ U, dialEval Φ x < 0
  VanishesOn Φ U := ∀ x ∈ U, dialEval Φ x = 0
  ZeroPolynomial Φ := zeroDialForm Φ
  Estimate order n U labels := DialEstimate r θ head order n U labels

namespace DialEstimate

/-- Restrict a dial estimate to a smaller region without changing the processed
prefix or labels. -/
theorem restrict {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {order : List DeeperHead} {n : Nat} {U V : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel}
    (hsub : V ⊆ U)
    (hEst : DialEstimate r θ head order n U labels) :
    DialEstimate r θ head order n V labels where
  gate hqpos hq a hmem x hx :=
    hEst.gate hqpos hq a hmem x (hsub hx)

end DialEstimate

/-! ## Faithfulness of the dial form (M6/M7)

The declarations below make the `QuadraticDialForm` fed to the trichotomy instance
*faithful* to the true iterated transformer products.  The key deliverables are:

* `deeperValueStream` — the layer-shifted value stream feeding the `Saturated`
  products (`saturatedC`/`saturatedTailD`/`saturatedKLayer`);
* `satZetaPoint` — the ζ-general frozen recursion point (head-`h` layer-0 gate `→ t`,
  other layer-0 gates `→ 1`, deeper layer `l` gate `→ ζ_l`), the analogue of
  `dialSatPoint` *without* the `K = I` collapse;
* **F2** (`satZetaPoint_fst`/`satZetaPoint_snd`) — the honest closed forms
  `w_N = R(ζ)(B - tV)w`, `v_N = P·C₁·v + [P(S+tV)+Q(B-tV)]w` (TeX `lem:polynomial-structure`),
  proved by induction on layers via `layerProduct` accumulation and the `saturatedE`
  telescoping recursion;
* `phiHead` — the genuine per-head `QuadraticDialForm` built from the actual products;
* **F1** (`dialEval_phiHead_eq_frozenSlope`) — the faithfulness identity
  `dialEval (phiHead …) (p,t) = matrixBilin A_{ℓb} (satZetaPoint … (ℓ-1))`.
-/

/-- Layer-shifted value stream: TeX layer `l ≥ 2` reads the value matrices of
`Params` layer `l - 1` (out-of-range indices clamp to layer `0`, never used). -/
noncomputable def deeperValueStream {m k d : Nat} (θ : Params (m + 1) k d) :
    Nat → Fin k → Matrix (Fin d) (Fin d) ℝ :=
  fun l a => if h : l - 1 < m + 1 then valueMatrix θ ⟨l - 1, h⟩ a else valueMatrix θ 0 a

theorem deeperValueStream_succ {m k d : Nat} (θ : Params (m + 1) k d)
    (n : Nat) (hn : n < m + 1) (a : Fin k) :
    deeperValueStream θ (n + 1) a = valueMatrix θ ⟨n, hn⟩ a := by
  show (if h : (n + 1) - 1 < m + 1 then valueMatrix θ ⟨(n + 1) - 1, h⟩ a
        else valueMatrix θ 0 a) = valueMatrix θ ⟨n, hn⟩ a
  simp only [Nat.add_sub_cancel, dif_pos hn]

theorem saturatedC_deeperValueStream_succ {m k d : Nat} (θ : Params (m + 1) k d)
    (n : Nat) (hn : n < m + 1) :
    saturatedC (deeperValueStream θ) (n + 1) = collapseMatrix θ ⟨n, hn⟩ := by
  rw [saturatedC, collapseMatrix, valueSum]
  congr 1
  exact Finset.sum_congr rfl fun a _ => deeperValueStream_succ θ n hn a

theorem saturatedTailD_deeperValueStream_succ {m k d : Nat} (θ : Params (m + 1) k d)
    (ζ : SaturatedLabels k) (n : Nat) (hn : n < m + 1) :
    saturatedTailD (deeperValueStream θ) ζ (n + 1) = gatedValueSum θ ⟨n, hn⟩ (ζ (n + 1)) := by
  rw [saturatedTailD, gatedValueSum]
  exact Finset.sum_congr rfl fun a _ => by rw [deeperValueStream_succ θ n hn a]

/-- `valueSum` at layer `0` splits off the dialed head. -/
theorem valueSum_zero_eq_head_add_other {m k d : Nat} (θ : Params (m + 1) k d) (h : Fin k) :
    valueSum θ 0 = valueMatrix θ 0 h + firstLayerOtherValueSum θ h := by
  rw [valueSum, firstLayerOtherValueSum]
  exact (Finset.add_sum_erase Finset.univ (fun a => valueMatrix θ 0 a) (Finset.mem_univ h)).symm

/-- `C₁ = collapseMatrix θ 0 = B + S`, the layer-0 collapse in `B, S` form. -/
theorem collapseMatrix_zero_eq_B_add_S {m k d : Nat} (θ : Params (m + 1) k d) (h : Fin k) :
    collapseMatrix θ 0 = firstLayerUnsatB θ h + firstLayerOtherValueSum θ h := by
  rw [collapseMatrix, firstLayerUnsatB, valueSum_zero_eq_head_add_other θ h]
  abel

/-- The saturated layer-0 value sum in `S + tV` form. -/
theorem gatedValueSum_satGate_eq {m k d : Nat} (θ : Params (m + 1) k d) (h : Fin k) (t : ℝ) :
    gatedValueSum θ 0 (satGate t h) =
      firstLayerOtherValueSum θ h + t • valueMatrix θ 0 h := by
  rw [gatedValueSum_satGate, valueSum_zero_eq_head_add_other θ h]
  module

/-- The layer-0 saturated `w`-step matrix is `B - tV`. -/
theorem firstStep_w_matrix {m k d : Nat} (θ : Params (m + 1) k d) (h : Fin k) (t : ℝ) :
    collapseMatrix θ 0 - gatedValueSum θ 0 (satGate t h) =
      firstLayerUnsatB θ h - t • valueMatrix θ 0 h := by
  rw [gatedValueSum_satGate, collapseMatrix, firstLayerUnsatB]
  module

/-- Extend a layer product by one top factor (local copy of the private
`Saturated.layerProduct_succ_left`). -/
private theorem lp_succ_left {d : Nat}
    (M : Nat → Matrix (Fin d) (Fin d) ℝ) {j i : Nat} (hi : i ≤ j + 1) :
    layerProduct M (j + 1) i = M (j + 1) * layerProduct M j i := by
  by_cases hji : j < i
  · have hsucc : j + 1 ≤ i := Nat.succ_le_of_lt hji
    have hi_eq : i = j + 1 := Nat.le_antisymm hi hsucc
    subst i
    simp
  · have hnot : ¬ j + 1 < i := not_lt_of_ge hi
    have hle : i ≤ j := Nat.le_of_not_gt hji
    have hlen : j + 1 - i + 1 = (j - i + 1) + 1 := by omega
    have hidx : i + (j - i + 1) = j + 1 := by omega
    simp [layerProduct, hnot, hji, hlen, hidx]

/-- The saturated `E`-sum vanishes at the first deeper layer (empty index range). -/
theorem saturatedE_one {d : Nat} (C D K : Nat → Matrix (Fin d) (Fin d) ℝ) :
    saturatedE C D K 1 = 0 := by
  rw [saturatedE, Finset.Icc_eq_empty (by norm_num : ¬ (2 : ℕ) ≤ 1)]
  simp

/-- The `saturatedE` telescoping recursion: peel the top layer. -/
theorem saturatedE_succ {d : Nat} (C D K : Nat → Matrix (Fin d) (Fin d) ℝ) (n : Nat)
    (hn : 1 ≤ n) :
    saturatedE C D K (n + 1) =
      C (n + 1) * saturatedE C D K n + D (n + 1) * layerProduct K n 2 := by
  have h2 : 2 ≤ n + 1 := by omega
  have hlast : layerProduct C (n + 1) (n + 1 + 1) * D (n + 1) * layerProduct K (n + 1 - 1) 2
      = D (n + 1) * layerProduct K n 2 := by
    rw [layerProduct_empty C (by omega : n + 1 < n + 1 + 1)]
    simp
  have hsum : (∑ j ∈ Finset.Icc 2 n,
        layerProduct C (n + 1) (j + 1) * D j * layerProduct K (j - 1) 2)
      = C (n + 1) * saturatedE C D K n := by
    rw [saturatedE, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjn : j + 1 ≤ n + 1 := by have := (Finset.mem_Icc.mp hj).2; omega
    rw [lp_succ_left C hjn]
    noncomm_ring
  rw [saturatedE, Finset.sum_Icc_succ_top h2, hlast, hsum]

/-! ### The ζ-general frozen recursion point -/

/-- The saturated layer-`n` gate vector for the ζ-general frozen recursion: `satGate`
at layer `0`, the frozen labels `ζ_{n+1}` at deeper layer `n`. -/
noncomputable def satZetaGate {k : Nat} (ζ : SaturatedLabels k) (t : ℝ) (h : Fin k) (n : Nat) :
    Fin k → ℝ :=
  if n = 0 then satGate t h else ζ (n + 1)

@[simp] theorem satZetaGate_zero {k : Nat} (ζ : SaturatedLabels k) (t : ℝ) (h : Fin k) :
    satZetaGate ζ t h 0 = satGate t h := by simp [satZetaGate]

theorem satZetaGate_pos {k : Nat} (ζ : SaturatedLabels k) (t : ℝ) (h : Fin k)
    {n : Nat} (hn : 0 < n) :
    satZetaGate ζ t h n = ζ (n + 1) := by
  rw [satZetaGate, if_neg (Nat.pos_iff_ne_zero.mp hn)]

/-- The ζ-general saturated recursion point at layer `n`: gated steps with the head-`h`
dial at layer `0` and the frozen labels `ζ` at each deeper layer. -/
noncomputable def satZetaPoint {m k d : Nat} (θ : Params (m + 1) k d) (h : Fin k)
    (ζ : SaturatedLabels k) (p : ProbePair d) (t : ℝ) : Nat → ProbePoint d
  | 0 => (p.1, p.2)
  | n + 1 =>
      if hn : n < m + 1 then
        gatedEffectivePoint θ ⟨n, hn⟩ (satZetaGate ζ t h n)
          (satZetaPoint θ h ζ p t n).1 (satZetaPoint θ h ζ p t n).2
      else satZetaPoint θ h ζ p t n

@[simp] theorem satZetaPoint_zero {m k d : Nat} (θ : Params (m + 1) k d) (h : Fin k)
    (ζ : SaturatedLabels k) (p : ProbePair d) (t : ℝ) :
    satZetaPoint θ h ζ p t 0 = (p.1, p.2) :=
  rfl

theorem satZetaPoint_succ_of_lt {m k d : Nat} (θ : Params (m + 1) k d) (h : Fin k)
    (ζ : SaturatedLabels k) (p : ProbePair d) (t : ℝ) (n : Nat) (hn : n < m + 1) :
    satZetaPoint θ h ζ p t (n + 1) =
      gatedEffectivePoint θ ⟨n, hn⟩ (satZetaGate ζ t h n)
        (satZetaPoint θ h ζ p t n).1 (satZetaPoint θ h ζ p t n).2 := by
  rw [satZetaPoint]; exact dif_pos hn

theorem satZetaPoint_succ_of_ge {m k d : Nat} (θ : Params (m + 1) k d) (h : Fin k)
    (ζ : SaturatedLabels k) (p : ProbePair d) (t : ℝ) (n : Nat) (hn : ¬ n < m + 1) :
    satZetaPoint θ h ζ p t (n + 1) = satZetaPoint θ h ζ p t n := by
  rw [satZetaPoint]; exact dif_neg hn

theorem satZetaPoint_one {m k d : Nat} (θ : Params (m + 1) k d) (h : Fin k)
    (ζ : SaturatedLabels k) (p : ProbePair d) (t : ℝ) :
    satZetaPoint θ h ζ p t 1 = gatedEffectivePoint θ 0 (satGate t h) p.1 p.2 := by
  have h0 : (⟨0, Nat.succ_pos m⟩ : Fin (m + 1)) = 0 := by apply Fin.ext; simp
  rw [satZetaPoint_succ_of_lt θ h ζ p t 0 (Nat.succ_pos m)]
  simp only [satZetaGate_zero, satZetaPoint_zero, h0]

/-! ### Saturated formal evaluation -/

/-- Formal gate assignment induced by the ζ-general frozen recursion. -/
noncomputable def satZetaGateAssignment {m k : Nat} (ζ : SaturatedLabels k)
    (t : ℝ) (h : Fin k) : FormalVar (m + 1) k → ℝ :=
  fun x => satZetaGate ζ t h x.1.1 x.2

/-- Evaluating the formal point recursion under the ζ-general saturated gates recovers
the frozen point `satZetaPoint`. -/
theorem eval_formalPoint_satZetaGateAssignment {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (ζ : SaturatedLabels k)
    (p : ProbePair d) (t : ℝ) :
    ∀ (n : Nat) (hn : n ≤ m + 1),
      evalFormalVec (satZetaGateAssignment (m := m) ζ t h)
          (formalPoint θ p.1 p.2 n hn).1 =
          (satZetaPoint θ h ζ p t n).1 ∧
        evalFormalVec (satZetaGateAssignment (m := m) ζ t h)
          (formalPoint θ p.1 p.2 n hn).2 =
          (satZetaPoint θ h ζ p t n).2
  | 0, _hn => by
      simp [formalPoint]
  | n + 1, hn => by
      have hprev :
          evalFormalVec (satZetaGateAssignment (m := m) ζ t h)
              (formalPoint θ p.1 p.2 n (Nat.le_of_succ_le hn)).1 =
              (satZetaPoint θ h ζ p t n).1 ∧
            evalFormalVec (satZetaGateAssignment (m := m) ζ t h)
              (formalPoint θ p.1 p.2 n (Nat.le_of_succ_le hn)).2 =
              (satZetaPoint θ h ζ p t n).2 :=
        eval_formalPoint_satZetaGateAssignment θ h ζ p t n (Nat.le_of_succ_le hn)
      constructor
      · rw [satZetaPoint_succ_of_lt θ h ζ p t n (Nat.lt_of_succ_le hn)]
        simp [formalPoint, eval_formalStepPoint_fst, hprev.1, hprev.2,
          satZetaGateAssignment]
      · rw [satZetaPoint_succ_of_lt θ h ζ p t n (Nat.lt_of_succ_le hn)]
        simp [formalPoint, eval_formalStepPoint_snd, hprev.1, hprev.2,
          satZetaGateAssignment]

/-- Formal `w_n` evaluated under the ζ-general saturated gates gives the first coordinate
of `satZetaPoint`. -/
theorem eval_formalW_satZetaGateAssignment {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (ζ : SaturatedLabels k)
    (p : ProbePair d) (t : ℝ) {n : Nat} (hn : n ≤ m + 1) :
    evalFormalVec (satZetaGateAssignment (m := m) ζ t h)
        (formalW θ p.1 p.2 n hn) =
      (satZetaPoint θ h ζ p t n).1 := by
  simpa [formalW] using
    (eval_formalPoint_satZetaGateAssignment θ h ζ p t n hn).1

/-- Formal `v_n` evaluated under the ζ-general saturated gates gives the second coordinate
of `satZetaPoint`. -/
theorem eval_formalV_satZetaGateAssignment {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (ζ : SaturatedLabels k)
    (p : ProbePair d) (t : ℝ) {n : Nat} (hn : n ≤ m + 1) :
    evalFormalVec (satZetaGateAssignment (m := m) ζ t h)
        (formalV θ p.1 p.2 n hn) =
      (satZetaPoint θ h ζ p t n).2 := by
  simpa [formalV] using
    (eval_formalPoint_satZetaGateAssignment θ h ζ p t n hn).2

/-- Formal slopes evaluated under the ζ-general saturated gates are the frozen slopes at
`satZetaPoint`. -/
theorem eval_formalSlope_satZetaGateAssignment {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (ζ : SaturatedLabels k)
    (p : ProbePair d) (t : ℝ) (n : Nat) (hn : n < m + 1) (a : Fin k) :
    MvPolynomial.eval (satZetaGateAssignment (m := m) ζ t h)
        (formalSlope θ p.1 p.2 ⟨n, hn⟩ a) =
      matrixBilin (attentionMatrix θ ⟨n, hn⟩ a)
        (satZetaPoint θ h ζ p t n).1
        (satZetaPoint θ h ζ p t n).2 := by
  rw [eval_formalSlope]
  rw [eval_formalW_satZetaGateAssignment θ h ζ p t (Nat.le_of_lt hn),
    eval_formalV_satZetaGateAssignment θ h ζ p t (Nat.le_of_lt hn)]

/-- The deeper-layer gated value sum equals the frozen `saturatedTailD` product. -/
theorem gatedValueSum_satZetaGate_pos {m k d : Nat} (θ : Params (m + 1) k d) (h : Fin k)
    (ζ : SaturatedLabels k) (t : ℝ) {n : Nat} (hnpos : 0 < n) (hn : n < m + 1) :
    gatedValueSum θ ⟨n, hn⟩ (satZetaGate ζ t h n) =
      saturatedTailD (deeperValueStream θ) ζ (n + 1) := by
  rw [satZetaGate_pos ζ t h hnpos, saturatedTailD_deeperValueStream_succ θ ζ n hn]

/-- The deeper-layer saturated `w`-step matrix is the frozen `saturatedKLayer` product. -/
theorem satZetaStepMatrixK {m k d : Nat} (θ : Params (m + 1) k d) (h : Fin k)
    (ζ : SaturatedLabels k) (t : ℝ) {n : Nat} (hnpos : 0 < n) (hn : n < m + 1) :
    collapseMatrix θ ⟨n, hn⟩ - gatedValueSum θ ⟨n, hn⟩ (satZetaGate ζ t h n) =
      saturatedKLayer (deeperValueStream θ) ζ (n + 1) := by
  rw [gatedValueSum_satZetaGate_pos θ h ζ t hnpos hn, saturatedKLayer,
    saturatedC_deeperValueStream_succ θ n hn]

/-! ### F2 — the honest closed forms (`lem:polynomial-structure`) -/

/-- Vector-algebra helper closing the deeper induction step for the `w` coordinate. -/
private theorem key_fst {d : Nat} (M : Nat → Matrix (Fin d) (Fin d) ℝ) (n : Nat)
    (hn : 2 ≤ n + 1) (x : Vec d) :
    M (n + 1) *ᵥ (layerProduct M n 2 *ᵥ x) = layerProduct M (n + 1) 2 *ᵥ x := by
  rw [Matrix.mulVec_mulVec, lp_succ_left M hn]

/-- Vector-algebra helper closing the deeper induction step for the `v` coordinate. -/
private theorem step_algebra {d : Nat} (zc zd P E R : Matrix (Fin d) (Fin d) ℝ)
    (X Y : Vec d) :
    zc *ᵥ (P *ᵥ X + E *ᵥ Y) + zd *ᵥ (R *ᵥ Y)
      = (zc * P) *ᵥ X + (zc * E + zd * R) *ᵥ Y := by
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.add_mulVec]
  abel

/-- **F2 (`w`-coordinate)**.  The frozen recursion point's first coordinate is the honest
`w_N = R(ζ)·(B - tV)·w`, where `R(ζ) = K_{N:2}(ζ)` is the deeper `saturatedKLayer` product. -/
theorem satZetaPoint_fst {m k d : Nat} (θ : Params (m + 1) k d) (h : Fin k)
    (ζ : SaturatedLabels k) (p : ProbePair d) (t : ℝ) (n : Nat)
    (hn1 : 1 ≤ n) (hnm : n ≤ m + 1) :
    (satZetaPoint θ h ζ p t n).1 =
      layerProduct (saturatedKLayer (deeperValueStream θ) ζ) n 2 *ᵥ
        ((firstLayerUnsatB θ h - t • valueMatrix θ 0 h) *ᵥ p.1) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      have hone : layerProduct (saturatedKLayer (deeperValueStream θ) ζ) (0 + 1) 2 = 1 := by simp
      rw [satZetaPoint_one, gatedEffectivePoint_fst, hone, Matrix.one_mulVec,
        firstStep_w_matrix θ h t]
    · have hlt : n < m + 1 := by omega
      rw [satZetaPoint_succ_of_lt θ h ζ p t n hlt, gatedEffectivePoint_fst,
        ih hnpos (by omega), satZetaStepMatrixK θ h ζ t hnpos hlt]
      exact key_fst (saturatedKLayer (deeperValueStream θ) ζ) n (by omega)
        ((firstLayerUnsatB θ h - t • valueMatrix θ 0 h) *ᵥ p.1)

/-- **F2 (`v`-coordinate)**.  The frozen recursion point's second coordinate is the honest
`v_N = P·C₁·v + [P(S+tV)+Q(B-tV)]·w`, with `P = C_{N:2}`, `Q = saturatedE`, `C₁ = collapse₀`. -/
theorem satZetaPoint_snd {m k d : Nat} (θ : Params (m + 1) k d) (h : Fin k)
    (ζ : SaturatedLabels k) (p : ProbePair d) (t : ℝ) (n : Nat)
    (hn1 : 1 ≤ n) (hnm : n ≤ m + 1) :
    (satZetaPoint θ h ζ p t n).2 =
      layerProduct (saturatedC (deeperValueStream θ)) n 2 *ᵥ
          (collapseMatrix θ 0 *ᵥ p.2
            + (firstLayerOtherValueSum θ h + t • valueMatrix θ 0 h) *ᵥ p.1)
      + saturatedE (saturatedC (deeperValueStream θ))
          (saturatedTailD (deeperValueStream θ) ζ)
          (saturatedKLayer (deeperValueStream θ) ζ) n *ᵥ
          ((firstLayerUnsatB θ h - t • valueMatrix θ 0 h) *ᵥ p.1) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      have hone : layerProduct (saturatedC (deeperValueStream θ)) (0 + 1) 2 = 1 := by simp
      rw [satZetaPoint_one, gatedEffectivePoint_snd, hone, Matrix.one_mulVec,
        saturatedE_one, Matrix.zero_mulVec, add_zero, gatedValueSum_satGate_eq]
    · have hlt : n < m + 1 := by omega
      rw [satZetaPoint_succ_of_lt θ h ζ p t n hlt, gatedEffectivePoint_snd,
        ih hnpos (by omega), satZetaPoint_fst θ h ζ p t n hnpos (by omega),
        ← saturatedC_deeperValueStream_succ θ n hlt,
        gatedValueSum_satZetaGate_pos θ h ζ t hnpos hlt, step_algebra,
        lp_succ_left (saturatedC (deeperValueStream θ)) (show (2 : ℕ) ≤ n + 1 by omega),
        saturatedE_succ (saturatedC (deeperValueStream θ))
          (saturatedTailD (deeperValueStream θ) ζ)
          (saturatedKLayer (deeperValueStream θ) ζ) n hnpos]

/-! ### The faithful per-head dial form and the faithfulness identity (F1) -/

/-- **The genuine per-head `QuadraticDialForm`** (TeX `def:phi-head`).  For the first-layer
dialed head `h` and the deeper head `(ℓ, b) = (j + 2, b)`, its five matrix blocks are the
*actual* iterated transformer products: `V = V_{1h}`, `S = ∑_{a≠h} V_{1a}`,
`RtAlb = Rᵀ A_{ℓb}`, `P = C_{ℓ-1:2}`, `Q = ∑ C D K`, all built from the frozen
`deeperValueStream` and labels `ζ`.  (Contrast the earlier degenerate constant form.) -/
noncomputable def phiHead {m k d : Nat} (θ : Params (m + 1) k d) (h : Fin k)
    (j : Fin m) (b : Fin k) (ζ : SaturatedLabels k) : QuadraticDialForm d where
  V := valueMatrix θ 0 h
  S := firstLayerOtherValueSum θ h
  RtAlb :=
    (saturatedTailK (saturatedM (saturatedC (deeperValueStream θ)) (j.val + 1))
        (saturatedE (saturatedC (deeperValueStream θ)) (saturatedTailD (deeperValueStream θ) ζ)
          (saturatedKLayer (deeperValueStream θ) ζ) (j.val + 1)))ᵀ *
      attentionMatrix θ (laterLayer j) b
  P := saturatedM (saturatedC (deeperValueStream θ)) (j.val + 1)
  Q := saturatedE (saturatedC (deeperValueStream θ)) (saturatedTailD (deeperValueStream θ) ζ)
        (saturatedKLayer (deeperValueStream θ) ζ) (j.val + 1)

@[simp] theorem phiHead_V {m k d : Nat} (θ : Params (m + 1) k d) (h : Fin k)
    (j : Fin m) (b : Fin k) (ζ : SaturatedLabels k) :
    (phiHead θ h j b ζ).V = valueMatrix θ 0 h :=
  rfl

/-- Updating a trichotomy label at a strictly later layer does not change the
numeric saturated label adapter at the old layer. -/
theorem trichotomyToSaturatedLabels_setLabel_eq_of_layer_lt (r L k : Nat)
    (labels : DeeperHead → TrichotomyLabel) (current : DeeperHead)
    (label : TrichotomyLabel) {l : Nat} (hl : l < current.layer) (a : Fin k) :
    trichotomyToSaturatedLabels r L k (setLabel labels current label) l a =
      trichotomyToSaturatedLabels r L k labels l a := by
  have hne : ({ layer := l, head := (a : Nat) + 1 } : DeeperHead) ≠ current := by
    intro heq
    have hlayer := congrArg DeeperHead.layer heq
    simp at hlayer
    omega
  simp [trichotomyToSaturatedLabels, setLabel, hne]

/-- A layer product is unchanged when its factor streams agree on the layer
interval used by the product. -/
theorem layerProductFrom_eq_of_eq_on_range {d : Nat}
    {M N : Nat → Matrix (Fin d) (Fin d) ℝ} (i n : Nat)
    (hMN : ∀ l : Nat, i ≤ l → l < i + n → M l = N l) :
    layerProductFrom M i n = layerProductFrom N i n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [layerProductFrom_succ, layerProductFrom_succ,
        hMN (i + n) (by omega) (by omega)]
      exact congrArg (fun X => N (i + n) * X)
        (ih (fun l hli hlt => hMN l hli (by omega)))

/-- Prefix form of `layerProductFrom_eq_of_eq_on_range`, phrased by an
ambient upper bound. -/
theorem layerProduct_eq_of_eq_on_le {d : Nat}
    {M N : Nat → Matrix (Fin d) (Fin d) ℝ} {j i L : Nat}
    (hMN : ∀ l : Nat, i ≤ l → l ≤ L → M l = N l) (hj : j ≤ L) :
    layerProduct M j i = layerProduct N j i := by
  by_cases hji : j < i
  · simp [layerProduct, hji]
  · simp only [layerProduct, hji, ↓reduceIte]
    apply layerProductFrom_eq_of_eq_on_range
    intro l hil hlt
    apply hMN l hil
    omega

/-- `saturatedTailD` only reads the numeric labels at its own layer. -/
theorem saturatedTailD_eq_of_labels_eq {k d : Nat}
    (V : Nat → Fin k → Matrix (Fin d) (Fin d) ℝ)
    {ζ η : SaturatedLabels k} {l : Nat} (hζη : ζ l = η l) :
    saturatedTailD V ζ l = saturatedTailD V η l := by
  simp [saturatedTailD, hζη]

/-- `saturatedKLayer` only reads the numeric labels at its own layer. -/
theorem saturatedKLayer_eq_of_labels_eq {k d : Nat}
    (V : Nat → Fin k → Matrix (Fin d) (Fin d) ℝ)
    {ζ η : SaturatedLabels k} {l : Nat} (hζη : ζ l = η l) :
    saturatedKLayer V ζ l = saturatedKLayer V η l := by
  simp [saturatedKLayer, saturatedTailD_eq_of_labels_eq V hζη]

/-- The saturated error sum through layer `L` is stable under changes to labels
strictly above `L`. -/
theorem saturatedE_eq_of_labels_eq_on_le {k d : Nat}
    (V : Nat → Fin k → Matrix (Fin d) (Fin d) ℝ)
    (C : Nat → Matrix (Fin d) (Fin d) ℝ) {ζ η : SaturatedLabels k} (L : Nat)
    (hζη : ∀ l : Nat, 2 ≤ l → l ≤ L → ζ l = η l) :
    saturatedE C (saturatedTailD V ζ) (saturatedKLayer V ζ) L =
      saturatedE C (saturatedTailD V η) (saturatedKLayer V η) L := by
  unfold saturatedE
  apply Finset.sum_congr rfl
  intro l hl
  have hlow : 2 ≤ l := (Finset.mem_Icc.mp hl).1
  have hhigh : l ≤ L := (Finset.mem_Icc.mp hl).2
  have hD : saturatedTailD V ζ l = saturatedTailD V η l :=
    saturatedTailD_eq_of_labels_eq V (hζη l hlow hhigh)
  have hK :
      layerProduct (saturatedKLayer V ζ) (l - 1) 2 =
        layerProduct (saturatedKLayer V η) (l - 1) 2 := by
    apply layerProduct_eq_of_eq_on_le (L := L)
    · intro q hqlo hqhi
      exact saturatedKLayer_eq_of_labels_eq V (hζη q hqlo hqhi)
    · omega
  rw [hD, hK]

/-- The faithful per-head form for layer `j + 2` only reads saturated labels
through layer `j + 1`. -/
theorem phiHead_eq_of_saturatedLabels_eq_on_le {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (j : Fin m) (b : Fin k)
    {ζ η : SaturatedLabels k}
    (hζη : ∀ l : Nat, l ≤ j.val + 1 → ζ l = η l) :
    phiHead θ h j b ζ = phiHead θ h j b η := by
  have hE :
      saturatedE (saturatedC (deeperValueStream θ)) (saturatedTailD (deeperValueStream θ) ζ)
          (saturatedKLayer (deeperValueStream θ) ζ) (j.val + 1) =
        saturatedE (saturatedC (deeperValueStream θ)) (saturatedTailD (deeperValueStream θ) η)
          (saturatedKLayer (deeperValueStream θ) η) (j.val + 1) :=
    saturatedE_eq_of_labels_eq_on_le (deeperValueStream θ)
      (saturatedC (deeperValueStream θ)) (j.val + 1)
      (fun l _hlow hhigh => hζη l hhigh)
  unfold phiHead
  rw [QuadraticDialForm.mk.injEq]
  refine ⟨rfl, rfl, ?_, rfl, hE⟩
  rw [hE]

/-- The conjugation identity `wᵀ (Pᵀ A Q) u = (Pw)ᵀ A (Qu)`, bridging the parent
`NLayer.matrixBilin` (used by `dialEval`) and the `KHead` `matrixBilin` (used by the
frozen slope). -/
theorem matrixBilin_conj {d : Nat} (A P Q : Matrix (Fin d) (Fin d) ℝ) (w u : Vec d) :
    NLayer.matrixBilin (Pᵀ * A * Q) w u = matrixBilin A (P *ᵥ w) (Q *ᵥ u) := by
  have h1 : (Pᵀ * A * Q) *ᵥ u = Pᵀ *ᵥ (A *ᵥ (Q *ᵥ u)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  show w ⬝ᵥ ((Pᵀ * A * Q) *ᵥ u) = (P *ᵥ w) ⬝ᵥ (A *ᵥ (Q *ᵥ u))
  rw [h1, dotProduct_comm w, adjoint_dotProduct, dotProduct_comm]

/-- **F1 (the faithfulness identity)**.  `dialEval (phiHead …)` at `(p, t)` equals the honest
frozen deeper slope `matrixBilin A_{ℓb} (satZetaPoint … (ℓ-1))`.  This is the deep Step-2
identity: the abstract dial polynomial evaluates to the true iterated-product slope. -/
theorem dialEval_phiHead_eq_frozenSlope {m k d : Nat} (θ : Params (m + 1) k d) (h : Fin k)
    (j : Fin m) (b : Fin k) (ζ : SaturatedLabels k) (p : ProbePair d) (t : ℝ) :
    dialEval (phiHead θ h j b ζ) (p, t) =
      matrixBilin (attentionMatrix θ (laterLayer j) b)
        (satZetaPoint θ h ζ p t (j.val + 1)).1
        (satZetaPoint θ h ζ p t (j.val + 1)).2 := by
  set A := attentionMatrix θ (laterLayer j) b with hAdef
  -- Projection facts for the `phiHead` blocks.
  have hV : (phiHead θ h j b ζ).V = valueMatrix θ 0 h := rfl
  have hS : (phiHead θ h j b ζ).S = firstLayerOtherValueSum θ h := rfl
  have hP : (phiHead θ h j b ζ).P
      = layerProduct (saturatedC (deeperValueStream θ)) (j.val + 1) 2 := rfl
  have hQ : (phiHead θ h j b ζ).Q
      = saturatedE (saturatedC (deeperValueStream θ)) (saturatedTailD (deeperValueStream θ) ζ)
          (saturatedKLayer (deeperValueStream θ) ζ) (j.val + 1) := rfl
  have hRt : (phiHead θ h j b ζ).RtAlb
      = (saturatedTailK (saturatedM (saturatedC (deeperValueStream θ)) (j.val + 1))
            (saturatedE (saturatedC (deeperValueStream θ)) (saturatedTailD (deeperValueStream θ) ζ)
              (saturatedKLayer (deeperValueStream θ) ζ) (j.val + 1)))ᵀ * A := rfl
  have hB : (phiHead θ h j b ζ).B = firstLayerUnsatB θ h := by
    rw [QuadraticDialForm.B, hV, firstLayerUnsatB]
  have hC1 : (phiHead θ h j b ζ).C1 = collapseMatrix θ 0 := by
    rw [QuadraticDialForm.C1, hB, hS, ← collapseMatrix_zero_eq_B_add_S θ h]
  have hBzVr : (phiHead θ h j b ζ).BzVr t
      = firstLayerUnsatB θ h - t • valueMatrix θ 0 h := by
    rw [QuadraticDialForm.BzVr, hB, hV]
  -- The two matrix-form identities: `Xfun`/`Yfun` are conjugates of `A_{ℓb}`.
  have hXfun : (phiHead θ h j b ζ).Xfun t
      = ((saturatedTailK (saturatedM (saturatedC (deeperValueStream θ)) (j.val + 1))
            (saturatedE (saturatedC (deeperValueStream θ)) (saturatedTailD (deeperValueStream θ) ζ)
              (saturatedKLayer (deeperValueStream θ) ζ) (j.val + 1))) *
          (firstLayerUnsatB θ h - t • valueMatrix θ 0 h))ᵀ * A *
          (layerProduct (saturatedC (deeperValueStream θ)) (j.val + 1) 2 * collapseMatrix θ 0) := by
    rw [QuadraticDialForm.Xfun, QuadraticDialForm.Y0, hBzVr, hRt, hP, hC1, Matrix.transpose_mul]
    noncomm_ring
  have hYfun : (phiHead θ h j b ζ).Yfun t
      = ((saturatedTailK (saturatedM (saturatedC (deeperValueStream θ)) (j.val + 1))
            (saturatedE (saturatedC (deeperValueStream θ)) (saturatedTailD (deeperValueStream θ) ζ)
              (saturatedKLayer (deeperValueStream θ) ζ) (j.val + 1))) *
          (firstLayerUnsatB θ h - t • valueMatrix θ 0 h))ᵀ * A *
          (layerProduct (saturatedC (deeperValueStream θ)) (j.val + 1) 2 *
              (firstLayerOtherValueSum θ h + t • valueMatrix θ 0 h) +
            saturatedE (saturatedC (deeperValueStream θ)) (saturatedTailD (deeperValueStream θ) ζ)
                (saturatedKLayer (deeperValueStream θ) ζ) (j.val + 1) *
              (firstLayerUnsatB θ h - t • valueMatrix θ 0 h)) := by
    rw [QuadraticDialForm.Yfun, hBzVr, hRt, hP, hQ, hS, hV, Matrix.transpose_mul]
    noncomm_ring
  -- Frozen slope in honest closed form (F2), with the `w`-product folded to `saturatedTailK`.
  rw [satZetaPoint_fst θ h ζ p t (j.val + 1) (by omega) (by omega),
    satZetaPoint_snd θ h ζ p t (j.val + 1) (by omega) (by omega),
    ← saturatedK_eq_layerProduct (deeperValueStream θ) ζ (j.val + 1)]
  -- Expand `dialEval` and apply the conjugation identity to both quadratic terms.
  rw [dialEval, QuadraticDialForm.eval_Xpoly, QuadraticDialForm.eval_Ypoly, hXfun, hYfun,
    matrixBilin_conj, matrixBilin_conj]
  simp only [Matrix.mul_add, Matrix.mulVec_mulVec, Matrix.mulVec_add, Matrix.add_mulVec,
    matrixBilin_add_right']
  abel

/-- The faithful per-head dial form for an abstract deeper head, with a `V`-only fallback
outside the valid `(2 ≤ ℓ ≤ m+1, 1 ≤ b ≤ k)` index range.  In every branch the value block
is `valueMatrix θ 0 h`, so the zero-branch rigidity hypothesis `Φ.V = V_{1h}` is `rfl`. -/
noncomputable def phiHeadOfDeeperHead {m k d : Nat} (r : Nat) (θ : Params (m + 1) k d)
    (h : Fin k) (dh : DeeperHead) (labels : DeeperHead → TrichotomyLabel) :
    QuadraticDialForm d :=
  if hb : dh.layer - 2 < m ∧ dh.head - 1 < k then
    phiHead θ h ⟨dh.layer - 2, hb.1⟩ ⟨dh.head - 1, hb.2⟩
      (trichotomyToSaturatedLabels r (m + 1) k labels)
  else
    { V := valueMatrix θ 0 h, S := 0, RtAlb := 0, P := 0, Q := 0 }

@[simp] theorem phiHeadOfDeeperHead_V {m k d : Nat} (r : Nat) (θ : Params (m + 1) k d)
    (h : Fin k) (dh : DeeperHead) (labels : DeeperHead → TrichotomyLabel) :
    (phiHeadOfDeeperHead r θ h dh labels).V = valueMatrix θ 0 h := by
  unfold phiHeadOfDeeperHead
  split <;> rfl

/-- Setting the label of a head at the same or a later layer leaves the old
faithful form unchanged.  The lower-bound hypothesis excludes artificial
non-deeper layers, where the fallback-valid branch can read layer `0`/`1`
adapter slots. -/
theorem phiHeadOfDeeperHead_setLabel_eq_of_layer_le {m k d : Nat}
    (r : Nat) (θ : Params (m + 1) k d) (h : Fin k)
    (labels : DeeperHead → TrichotomyLabel) (label : TrichotomyLabel)
    {old current : DeeperHead} (hold : 2 ≤ old.layer)
    (hle : old.layer ≤ current.layer) :
    phiHeadOfDeeperHead r θ h old (setLabel labels current label) =
      phiHeadOfDeeperHead r θ h old labels := by
  unfold phiHeadOfDeeperHead
  by_cases hvalid : old.layer - 2 < m ∧ old.head - 1 < k
  · simp [hvalid]
    apply phiHead_eq_of_saturatedLabels_eq_on_le
    intro l hl
    funext a
    have hl_prefix : l ≤ old.layer - 2 + 1 := by
      simpa using hl
    exact trichotomyToSaturatedLabels_setLabel_eq_of_layer_lt r (m + 1) k labels current
      label (by omega) a
  · simp [hvalid]

/-- Faithfulness identity for the one-based deeper-head index shape consumed by
`tendsto_satZetaActualProbePoint`: label layer `n + 1` corresponds to actual
parameter layer `n`. -/
theorem dialEval_phiHeadOfDeeperHead_succ_eq_frozenSlope {m k d : Nat} (r : Nat)
    (θ : Params (m + 1) k d) (h : Fin k)
    (labels : DeeperHead → TrichotomyLabel) (n : Nat) (hnpos : 1 ≤ n)
    (hn : n < m + 1) (a : Fin k) (p : ProbePair d) (t : ℝ) :
    dialEval
        (phiHeadOfDeeperHead r θ h
          { layer := n + 1, head := (a : Nat) + 1 } labels) (p, t) =
      matrixBilin (attentionMatrix θ ⟨n, hn⟩ a)
        (satZetaPoint θ h (trichotomyToSaturatedLabels r (m + 1) k labels) p t n).1
        (satZetaPoint θ h (trichotomyToSaturatedLabels r (m + 1) k labels) p t n).2 := by
  set ζ := trichotomyToSaturatedLabels r (m + 1) k labels
  have hvalid :
      (n + 1) - 2 < m ∧ ((a : Nat) + 1) - 1 < k := by
    constructor <;> omega
  have hidx : (n + 1) - 2 + 1 = n := by omega
  have hidx' : n - 1 + 1 = n := by omega
  have hhead : (((a : Nat) + 1) - 1) = (a : Nat) := by omega
  have hlater : ∀ hnm : n - 1 < m,
      laterLayer (⟨n - 1, hnm⟩ : Fin m) = (⟨n, hn⟩ : Fin (m + 1)) := by
    intro hnm
    apply Fin.ext
    simpa [laterLayer, hidx']
  have hbase :=
    dialEval_phiHead_eq_frozenSlope θ h
      ⟨(n + 1) - 2, hvalid.1⟩
      ⟨((a : Nat) + 1) - 1, hvalid.2⟩ ζ p t
  rw [phiHeadOfDeeperHead, dif_pos hvalid]
  simpa [ζ, hidx, hidx', hhead, hlater, Fin.ext_iff] using hbase

/-- **The faithful formal-slope data** (replacing the degenerate constant).  Each abstract
deeper head `(ℓ, b)` is sent to its genuine per-head `QuadraticDialForm` `phiHead …`,
and `Λ = Φ` (the dial evaluation of the same faithful form). -/
noncomputable def dialFormalData {m k d : Nat} (r : Nat) (θ : Params (m + 1) k d) (h : Fin k) :
    TrichotomyFormalData (QuadraticDialForm d) where
  Phi dh labels := phiHeadOfDeeperHead r θ h dh labels
  Lambda dh labels := phiHeadOfDeeperHead r θ h dh labels

/-- A processing-invariant current region inherits the sign-region topology from a
`SignRegionData` base region by restriction. -/
theorem signRegionTopologyStatement_of_processingInvariant_dial_signRegionData
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    (D : SignRegionData θ head)
    {currentRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n : Nat}
    (hInv : ProcessingInvariantStatement
      (dialPredicates (attentionMatrix θ 0) head) (dialFormalData r θ head)
      D.region currentRegion (deeperHeadOrder (m + 1) k) n labels) :
    SignRegionTopologyStatement (attentionMatrix θ 0) (valueMatrix θ 0) head
      currentRegion :=
  _root_.TransformerIdentifiability.NLayer.KHead.SignRegionTopologyStatement.restrict
    (signRegionData_signRegionTopologyStatement D)
    hInv.region_subset_base hInv.region_nonempty hInv.region_connected
    hInv.region_relativelyOpen

/-- Equality-wrapper version of
`signRegionTopologyStatement_of_processingInvariant_dial_signRegionData` for
call sites whose abstract base region is definitionally hidden. -/
theorem signRegionTopologyStatement_of_processingInvariant_dial_signRegionData_eq
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    (D : SignRegionData θ head)
    {baseRegion currentRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n : Nat}
    (hbase : baseRegion = D.region)
    (hInv : ProcessingInvariantStatement
      (dialPredicates (attentionMatrix θ 0) head) (dialFormalData r θ head)
      baseRegion currentRegion (deeperHeadOrder (m + 1) k) n labels) :
    SignRegionTopologyStatement (attentionMatrix θ 0) (valueMatrix θ 0) head
      currentRegion := by
  subst hbase
  exact signRegionTopologyStatement_of_processingInvariant_dial_signRegionData D hInv

/-- `F.Phi` for an old deeper head is unchanged by setting a same- or later-layer label. -/
theorem dialFormalData_Phi_setLabel_eq_of_layer_le {m k d : Nat}
    (r : Nat) (θ : Params (m + 1) k d) (h : Fin k)
    (labels : DeeperHead → TrichotomyLabel) (label : TrichotomyLabel)
    {old current : DeeperHead} (hold : 2 ≤ old.layer)
    (hle : old.layer ≤ current.layer) :
    (dialFormalData r θ h).Phi old (setLabel labels current label) =
      (dialFormalData r θ h).Phi old labels := by
  simpa [dialFormalData] using
    phiHeadOfDeeperHead_setLabel_eq_of_layer_le r θ h labels label hold hle

/-- `F.Lambda` for an old deeper head is unchanged by setting a same- or later-layer label. -/
theorem dialFormalData_Lambda_setLabel_eq_of_layer_le {m k d : Nat}
    (r : Nat) (θ : Params (m + 1) k d) (h : Fin k)
    (labels : DeeperHead → TrichotomyLabel) (label : TrichotomyLabel)
    {old current : DeeperHead} (hold : 2 ≤ old.layer)
    (hle : old.layer ≤ current.layer) :
    (dialFormalData r θ h).Lambda old (setLabel labels current label) =
      (dialFormalData r θ h).Lambda old labels := by
  simpa [dialFormalData] using
    phiHeadOfDeeperHead_setLabel_eq_of_layer_le r θ h labels label hold hle

/-- The lexicographic deeper-head order has no duplicates. -/
theorem deeperHeadOrder_nodup (L k : Nat) : (deeperHeadOrder L k).Nodup := by
  rw [deeperHeadOrder, List.nodup_flatMap]
  constructor
  · intro layerOffset _hlayer
    exact List.Nodup.map
      (fun a b hab => by
        have hhead := congrArg DeeperHead.head hab
        simp at hhead
        omega)
      List.nodup_range
  · have hpw : List.Pairwise (fun x y : Nat => x ≠ y) (List.range (L - 1)) :=
      List.nodup_iff_pairwise_ne.mp List.nodup_range
    refine hpw.imp ?_
    intro layer₁ layer₂ hne
    dsimp [Function.onFun]
    rw [List.disjoint_left]
    intro dh hmem₁ hmem₂
    rw [List.mem_map] at hmem₁ hmem₂
    rcases hmem₁ with ⟨head₁, _hhead₁, rfl⟩
    rcases hmem₂ with ⟨head₂, _hhead₂, heq⟩
    have hlayer := congrArg DeeperHead.layer heq
    simp at hlayer
    exact hne (by omega)

private theorem deeperHeadBlock_mem_layer {layerOffset k : Nat} {dh : DeeperHead}
    (hdh : dh ∈ (List.range k).map fun headOffset =>
      ({ layer := layerOffset + 2, head := headOffset + 1 } : DeeperHead)) :
    dh.layer = layerOffset + 2 := by
  rw [List.mem_map] at hdh
  rcases hdh with ⟨_headOffset, _hhead, rfl⟩
  rfl

private theorem deeperHeadBlock_pairwise_layer_le (layerOffset k : Nat) :
    ((List.range k).map fun headOffset =>
      ({ layer := layerOffset + 2, head := headOffset + 1 } : DeeperHead)).Pairwise
        (fun old current => old.layer ≤ current.layer) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp

private theorem deeperHeadOrder_pairwise_layer_le_aux {k : Nat} {offsets : List Nat}
    (hoffsets : offsets.Pairwise (fun earlier later => earlier ≤ later)) :
    (offsets.flatMap fun layerOffset =>
      (List.range k).map fun headOffset =>
        ({ layer := layerOffset + 2, head := headOffset + 1 } : DeeperHead)).Pairwise
          (fun old current => old.layer ≤ current.layer) := by
  induction offsets with
  | nil =>
      simp
  | cons layerOffset rest ih =>
      rw [List.flatMap_cons, List.pairwise_append]
      have hcons := List.pairwise_cons.mp hoffsets
      refine ⟨deeperHeadBlock_pairwise_layer_le layerOffset k, ih hcons.2, ?_⟩
      intro old hold current hcurrent
      rw [List.mem_flatMap] at hcurrent
      rcases hcurrent with ⟨laterOffset, hlater, hcurrent_block⟩
      have hlayer_old := deeperHeadBlock_mem_layer (k := k) hold
      have hlayer_current := deeperHeadBlock_mem_layer (k := k) hcurrent_block
      have hle_offset : layerOffset ≤ laterOffset := hcons.1 laterOffset hlater
      rw [hlayer_old, hlayer_current]
      omega

/-- The lexicographic deeper-head order is monotone in the layer coordinate. -/
theorem deeperHeadOrder_pairwise_layer_le (L k : Nat) :
    (deeperHeadOrder L k).Pairwise (fun old current => old.layer ≤ current.layer) := by
  rw [deeperHeadOrder]
  exact deeperHeadOrder_pairwise_layer_le_aux (k := k)
    (List.sortedLE_iff_pairwise.mp (List.sortedLT_range (L - 1)).sortedLE)

/-- Any processed-prefix entry occurs at a layer no later than the current
`deeperHeadOrder` entry. -/
theorem layer_le_getElem_of_mem_processedPrefix_deeperHeadOrder
    {L k n : Nat} {old : DeeperHead}
    (hold : old ∈ processedPrefix (deeperHeadOrder L k) n)
    (hn : n < (deeperHeadOrder L k).length) :
    old.layer ≤ ((deeperHeadOrder L k)[n]).layer := by
  let order := deeperHeadOrder L k
  have hold_take : old ∈ order.take n := by
    simpa [order, processedPrefix] using hold
  obtain ⟨i, hi_take, hget_old⟩ := List.getElem_of_mem hold_take
  have hi_lt_n : i < n := by
    rw [List.length_take] at hi_take
    exact lt_of_lt_of_le hi_take (Nat.min_le_left n order.length)
  have hi_order : i < order.length := lt_trans hi_lt_n hn
  have hget_take : (order.take n)[i] = order[i] := by
    exact List.getElem_take (xs := order) (j := n) (i := i)
  have hold_eq : old = order[i] := by
    rw [← hget_old, hget_take]
  have hrel : (order[i]).layer ≤ (order[n]).layer := by
    have hpair : order.Pairwise (fun old current => old.layer ≤ current.layer) := by
      simpa [order] using deeperHeadOrder_pairwise_layer_le L k
    exact (List.pairwise_iff_getElem.mp hpair) i n hi_order hn hi_lt_n
  simpa [order, hold_eq] using hrel

/-- A strictly lower layer than the current `deeperHeadOrder` entry has already
been processed. -/
theorem succ_head_mem_processedPrefix_of_layer_lt_getElem_deeperHeadOrder
    {m k idx q : Nat} {a : Fin k}
    (hidx : idx < (deeperHeadOrder (m + 1) k).length)
    (hcurrent :
      (deeperHeadOrder (m + 1) k)[idx] =
        ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    {q' : Nat} (hq'pos : 1 ≤ q') (hq' : q' < m + 1)
    (hlt : q' < q) (b : Fin k) :
    ({ layer := q' + 1, head := (b : Nat) + 1 } : DeeperHead) ∈
      processedPrefix (deeperHeadOrder (m + 1) k) idx := by
  let order := deeperHeadOrder (m + 1) k
  let old : DeeperHead := { layer := q' + 1, head := (b : Nat) + 1 }
  have hold_order : old ∈ order := by
    simpa [order, old] using succ_head_mem_deeperHeadOrder hq'pos hq' b
  obtain ⟨j, hj_order, hget_old⟩ := List.getElem_of_mem hold_order
  have hidx_order : idx < order.length := by
    simpa [order] using hidx
  have hcurrent_layer : (order[idx]).layer = q + 1 := by
    simpa [order] using congrArg DeeperHead.layer hcurrent
  have hget_old_layer : (order[j]).layer = q' + 1 := by
    simpa [old] using congrArg DeeperHead.layer hget_old
  have hj_lt_idx : j < idx := by
    by_contra hnot
    have hidx_le_j : idx ≤ j := Nat.le_of_not_gt hnot
    rcases lt_or_eq_of_le hidx_le_j with hidx_lt_j | hidx_eq_j
    · have hrel : (order[idx]).layer ≤ (order[j]).layer := by
        have hpair : order.Pairwise (fun old current => old.layer ≤ current.layer) := by
          simpa [order] using deeperHeadOrder_pairwise_layer_le (m + 1) k
        exact (List.pairwise_iff_getElem.mp hpair) idx j hidx_order hj_order hidx_lt_j
      omega
    · have hlayers : q + 1 = q' + 1 := by
        have hcurrent_layer_j : (order[j]).layer = q + 1 := by
          simpa [← hidx_eq_j] using hcurrent_layer
        exact hcurrent_layer_j.symm.trans hget_old_layer
      omega
  have hj_take : j < (order.take idx).length := by
    rw [List.length_take]
    exact lt_min hj_lt_idx hj_order
  have hget_take : (order.take idx)[j] = order[j] := by
    exact List.getElem_take (xs := order) (j := idx) (i := j)
  have hold_take : old ∈ order.take idx := by
    rw [← hget_old, ← hget_take]
    exact List.getElem_mem hj_take
  simpa [order, processedPrefix] using hold_take

/-- rfl bridge between the `KHead` `firstHeadSlope` and the **parent**
`NLayer.matrixBilin` used by the rigidity lemma. -/
theorem firstHeadSlope_eq_matrixBilin {k d : Nat}
    (A : Fin k → Matrix (Fin d) (Fin d) ℝ) (h : Fin k) (p : ProbePair d) :
    firstHeadSlope A h p = NLayer.matrixBilin (A h) p.1 p.2 :=
  rfl

/-! ## Path-T Lane C: additive rigidity-facts bundle -/

/-- **Path-T Lane C: additive first-layer rigidity-facts bundle.**  The three
first-layer genericity facts that the zero-branch rigidity leaf actually
consumes: the head's first-layer attention determinant is nonzero, its symmetric
part is nonzero, and its value matrix is nonzero.  This is the
value-matrix-parameter-free replacement for a full `Regularity r θ` witness in
the `_of_facts`/`_of_topology` trichotomy chain (matches exactly the three
`hreg.…` facts used in `lem_zero_branch_rigidity_dial`). -/
structure FirstHeadRigidityFacts {m k d : Nat} (θ : Params (m + 1) k d)
    (head : Fin k) : Prop where
  det_ne : (attentionMatrix θ 0 head).det ≠ 0
  sym_ne : sym (attentionMatrix θ 0 head) ≠ 0
  value_ne : valueMatrix θ 0 head ≠ 0

/-- A full `Regularity r θ` witness supplies the three first-layer rigidity facts
consumed by the zero-branch rigidity leaf. -/
theorem Regularity.toFirstHeadRigidityFacts {m k d r : Nat}
    {θ : Params (m + 1) k d} {head : Fin k} (hreg : Regularity r θ) :
    FirstHeadRigidityFacts θ head where
  det_ne := hreg.det_attention_ne_zero 0 head
  sym_ne := Regularity.symAttentionMatrix_ne_zero hreg 0 head
  value_ne := Regularity.valueMatrix_ne_zero hreg 0 head

/-! ## The rigidity theorem (heart of `lem:zero-branch-rigidity`) -/

/-- **`lem:zero-branch-rigidity` (concrete instance).**

If the matrix-form dial polynomial `Λ[Φ]` vanishes on a nonempty, connected,
relatively-open sign region `U ⊆ M_h × (0,1)`, then `Φ` is the zero polynomial:
its affine block `X` is `0` and `Sym Y = 0`.  Honest hypotheses: `2 ≤ d`, a
`Regularity r θ` witness (supplying `det A_h ≠ 0`, `Sym A_h ≠ 0`, `V_h ≠ 0`), the
identification `Φ.V = V_h`, and the full sign-region topology package. -/
theorem lem_zero_branch_rigidity_dial {m k d : Nat} {r : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (Φ : QuadraticDialForm d)
    (U : Set (ProbePair d × ℝ))
    (hd : 2 ≤ d) (hreg : Regularity r θ) (hVeq : Φ.V = valueMatrix θ 0 h)
    (htop : SignRegionTopologyStatement (attentionMatrix θ 0) (valueMatrix θ 0) h U)
    (hvanish : ∀ x ∈ U, dialEval Φ x = 0) :
    zeroDialForm Φ := by
  have hdetA : (attentionMatrix θ 0 h).det ≠ 0 := hreg.det_attention_ne_zero 0 h
  have hsymA : sym (attentionMatrix θ 0 h) ≠ 0 :=
    Regularity.symAttentionMatrix_ne_zero hreg 0 h
  have hVne : Φ.V ≠ 0 := by rw [hVeq]; exact Regularity.valueMatrix_ne_zero hreg 0 h
  have hJinf : (timeProjection U).Infinite := htop.time_projection_infinite
  -- Per-slice rigidity.
  have hslice : ∀ t ∈ timeProjection U,
      (∃ c : ℝ, Φ.Xfun t = c • (attentionMatrix θ 0 h)) ∧
        (Φ.Yfun t + (Φ.Yfun t)ᵀ = 0) := by
    intro t ht
    obtain ⟨p0, hp0⟩ := ht
    obtain ⟨O, hOopen, hOeq⟩ := htop.slice_open t
    have hp0slice : p0 ∈ timeSlice U t := hp0
    rw [hOeq] at hp0slice
    have hquad0 : NLayer.matrixBilin (attentionMatrix θ 0 h) p0.1 p0.2 = 0 := by
      have hq := hp0slice.2.1
      simp only [firstHeadQuadric, firstHeadSlope_eq_matrixBilin] at hq
      exact hq
    have hvanishW : ∀ p ∈ O,
        NLayer.matrixBilin (attentionMatrix θ 0 h) p.1 p.2 = 0 →
          NLayer.matrixBilin (Φ.Xfun t) p.1 p.2 + NLayer.matrixBilin (Φ.Yfun t) p.1 p.1 = 0 := by
      intro p hpO hpq
      by_cases hp1 : p.1 = 0
      · simp [hp1, NLayer.matrixBilin]
      · have hpquad : p ∈ quadricPatch (attentionMatrix θ 0) h := by
          refine ⟨?_, hp1⟩
          change firstHeadSlope (attentionMatrix θ 0) h p = 0
          rw [firstHeadSlope_eq_matrixBilin]; exact hpq
        have hpslice : p ∈ timeSlice U t := by rw [hOeq]; exact ⟨hpO, hpquad⟩
        have hv := hvanish (p, t) hpslice
        rw [dialEval] at hv
        simpa using hv
    obtain ⟨cc, hcc, hsym⟩ :=
      lem_quadratic_quadric_rigidity hd (attentionMatrix θ 0 h) (Φ.Xfun t) (Φ.Yfun t)
        p0.1 p0.2 O hdetA hp0slice.2.2 hquad0 hOopen hp0slice.1 hvanishW
    exact ⟨⟨cc, hcc⟩, add_transpose_eq_zero_of_sym_eq_zero hsym⟩
  -- `Ypoly + Ypolyᵀ = 0`.
  have hYzero : Φ.Ypoly + Φ.Ypolyᵀ = 0 := by
    apply matrix_eq_of_infinite_eval_eq _ _ (timeProjection U) hJinf
    intro t ht
    simp only [eval_add, eval_transpose, QuadraticDialForm.eval_Ypoly, eval_zeroMatrix]
    exact (hslice t ht).2
  -- The club identity for all real `t`.
  have hclub : ∀ t : ℝ, Φ.Yfun t + (Φ.Yfun t)ᵀ = 0 := by
    intro t
    have := congrArg (evalPolynomialMatrix t) hYzero
    simpa using this
  -- A nonzero entry of `A_h`.
  obtain ⟨i0, j0, hij⟩ : ∃ i j, (attentionMatrix θ 0 h) i j ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hz : (attentionMatrix θ 0 h) = 0 := by ext i j; exact hcon i j
    apply hdetA
    rw [hz]
    haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    exact Matrix.det_zero this
  -- Interpolate: `Xpoly = γ • liftC A_h`.
  set γ : Polynomial ℝ :=
    Polynomial.C (((attentionMatrix θ 0 h) i0 j0)⁻¹) * (Φ.Xpoly i0 j0) with hγ_def
  have hXeq : Φ.Xpoly = γ • liftC (attentionMatrix θ 0 h) := by
    apply matrix_eq_of_infinite_eval_eq _ _ (timeProjection U) hJinf
    intro t ht
    obtain ⟨cval, hcval⟩ := (hslice t ht).1
    rw [eval_polySmul, eval_liftC, QuadraticDialForm.eval_Xpoly]
    have hentry : Polynomial.eval t (Φ.Xpoly i0 j0) = (Φ.Xfun t) i0 j0 := by
      have := congrFun (congrFun (QuadraticDialForm.eval_Xpoly Φ t) i0) j0
      simpa [evalPolynomialMatrix] using this
    have hev : Polynomial.eval t γ = cval := by
      rw [hγ_def, Polynomial.eval_mul, Polynomial.eval_C, hentry, hcval]
      simp only [Matrix.smul_apply, smul_eq_mul]
      field_simp [hij]
    rw [hev, hcval]
  -- Extract coefficient identities.
  have hmateq : liftC (Φ.Bᵀ * Φ.Y0) - (Polynomial.X : Polynomial ℝ) • liftC (Φ.Vᵀ * Φ.Y0)
      = γ • liftC (attentionMatrix θ 0 h) := by
    rw [← Φ.Xpoly_eq]; exact hXeq
  have hentry : ∀ i j,
      Polynomial.C ((Φ.Bᵀ * Φ.Y0) i j) - Polynomial.X * Polynomial.C ((Φ.Vᵀ * Φ.Y0) i j)
        = γ * Polynomial.C ((attentionMatrix θ 0 h) i j) := by
    intro i j
    have hij_eq := congrFun (congrFun hmateq i) j
    simpa only [Matrix.sub_apply, Matrix.smul_apply, liftC, Matrix.map_apply, smul_eq_mul]
      using hij_eq
  have hc0 : Φ.Bᵀ * Φ.Y0 = (γ.coeff 0) • (attentionMatrix θ 0 h) := by
    ext i j
    have := congrArg (fun p => p.coeff 0) (hentry i j)
    simp only [Matrix.smul_apply, smul_eq_mul]
    simpa [Polynomial.coeff_C, Polynomial.coeff_mul_C] using this
  have hc1 : -(Φ.Vᵀ * Φ.Y0) = (γ.coeff 1) • (attentionMatrix θ 0 h) := by
    ext i j
    have := congrArg (fun p => p.coeff 1) (hentry i j)
    simp only [Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
    simpa [Polynomial.coeff_C, Polynomial.coeff_mul_C, Polynomial.coeff_X_mul] using this
  -- Case analysis forces both coefficients to vanish.
  obtain ⟨hγ0, hγ1⟩ :=
    Φ.gamma_eq_zero (attentionMatrix θ 0 h) (γ.coeff 0) (γ.coeff 1) (by omega)
      hc0 hc1 hclub hdetA hsymA hVne
  -- Conclude `Xpoly = 0`.
  refine ⟨?_, hYzero⟩
  have hB0 : Φ.Bᵀ * Φ.Y0 = 0 := by rw [hc0, hγ0, zero_smul]
  have hV0 : Φ.Vᵀ * Φ.Y0 = 0 := by
    have := hc1; rw [hγ1, zero_smul, neg_eq_zero] at this; exact this
  rw [Φ.Xpoly_eq, hB0, hV0, liftC_zero, smul_zero, sub_zero]

/-- **`lem:zero-branch-rigidity` (concrete instance), additive `_of_facts` form.**

Identical to `lem_zero_branch_rigidity_dial`, but driven by a
`FirstHeadRigidityFacts θ h` bundle in place of a full `Regularity r θ` witness,
and with the sign-region topology taken over a **free** value-matrix parameter
`V'` (the value block is unused by the argument beyond `Φ.V = valueMatrix θ 0 h`). -/
theorem lem_zero_branch_rigidity_dial_of_facts {m k d : Nat}
    {V' : Fin k → Matrix (Fin d) (Fin d) ℝ}
    (θ : Params (m + 1) k d) (h : Fin k) (Φ : QuadraticDialForm d)
    (U : Set (ProbePair d × ℝ))
    (hd : 2 ≤ d) (hfacts : FirstHeadRigidityFacts θ h) (hVeq : Φ.V = valueMatrix θ 0 h)
    (htop : SignRegionTopologyStatement (attentionMatrix θ 0) V' h U)
    (hvanish : ∀ x ∈ U, dialEval Φ x = 0) :
    zeroDialForm Φ := by
  have hdetA : (attentionMatrix θ 0 h).det ≠ 0 := hfacts.det_ne
  have hsymA : sym (attentionMatrix θ 0 h) ≠ 0 := hfacts.sym_ne
  have hVne : Φ.V ≠ 0 := by rw [hVeq]; exact hfacts.value_ne
  have hJinf : (timeProjection U).Infinite := htop.time_projection_infinite
  -- Per-slice rigidity.
  have hslice : ∀ t ∈ timeProjection U,
      (∃ c : ℝ, Φ.Xfun t = c • (attentionMatrix θ 0 h)) ∧
        (Φ.Yfun t + (Φ.Yfun t)ᵀ = 0) := by
    intro t ht
    obtain ⟨p0, hp0⟩ := ht
    obtain ⟨O, hOopen, hOeq⟩ := htop.slice_open t
    have hp0slice : p0 ∈ timeSlice U t := hp0
    rw [hOeq] at hp0slice
    have hquad0 : NLayer.matrixBilin (attentionMatrix θ 0 h) p0.1 p0.2 = 0 := by
      have hq := hp0slice.2.1
      simp only [firstHeadQuadric, firstHeadSlope_eq_matrixBilin] at hq
      exact hq
    have hvanishW : ∀ p ∈ O,
        NLayer.matrixBilin (attentionMatrix θ 0 h) p.1 p.2 = 0 →
          NLayer.matrixBilin (Φ.Xfun t) p.1 p.2 + NLayer.matrixBilin (Φ.Yfun t) p.1 p.1 = 0 := by
      intro p hpO hpq
      by_cases hp1 : p.1 = 0
      · simp [hp1, NLayer.matrixBilin]
      · have hpquad : p ∈ quadricPatch (attentionMatrix θ 0) h := by
          refine ⟨?_, hp1⟩
          change firstHeadSlope (attentionMatrix θ 0) h p = 0
          rw [firstHeadSlope_eq_matrixBilin]; exact hpq
        have hpslice : p ∈ timeSlice U t := by rw [hOeq]; exact ⟨hpO, hpquad⟩
        have hv := hvanish (p, t) hpslice
        rw [dialEval] at hv
        simpa using hv
    obtain ⟨cc, hcc, hsym⟩ :=
      lem_quadratic_quadric_rigidity hd (attentionMatrix θ 0 h) (Φ.Xfun t) (Φ.Yfun t)
        p0.1 p0.2 O hdetA hp0slice.2.2 hquad0 hOopen hp0slice.1 hvanishW
    exact ⟨⟨cc, hcc⟩, add_transpose_eq_zero_of_sym_eq_zero hsym⟩
  -- `Ypoly + Ypolyᵀ = 0`.
  have hYzero : Φ.Ypoly + Φ.Ypolyᵀ = 0 := by
    apply matrix_eq_of_infinite_eval_eq _ _ (timeProjection U) hJinf
    intro t ht
    simp only [eval_add, eval_transpose, QuadraticDialForm.eval_Ypoly, eval_zeroMatrix]
    exact (hslice t ht).2
  -- The club identity for all real `t`.
  have hclub : ∀ t : ℝ, Φ.Yfun t + (Φ.Yfun t)ᵀ = 0 := by
    intro t
    have := congrArg (evalPolynomialMatrix t) hYzero
    simpa using this
  -- A nonzero entry of `A_h`.
  obtain ⟨i0, j0, hij⟩ : ∃ i j, (attentionMatrix θ 0 h) i j ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hz : (attentionMatrix θ 0 h) = 0 := by ext i j; exact hcon i j
    apply hdetA
    rw [hz]
    haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    exact Matrix.det_zero this
  -- Interpolate: `Xpoly = γ • liftC A_h`.
  set γ : Polynomial ℝ :=
    Polynomial.C (((attentionMatrix θ 0 h) i0 j0)⁻¹) * (Φ.Xpoly i0 j0) with hγ_def
  have hXeq : Φ.Xpoly = γ • liftC (attentionMatrix θ 0 h) := by
    apply matrix_eq_of_infinite_eval_eq _ _ (timeProjection U) hJinf
    intro t ht
    obtain ⟨cval, hcval⟩ := (hslice t ht).1
    rw [eval_polySmul, eval_liftC, QuadraticDialForm.eval_Xpoly]
    have hentry : Polynomial.eval t (Φ.Xpoly i0 j0) = (Φ.Xfun t) i0 j0 := by
      have := congrFun (congrFun (QuadraticDialForm.eval_Xpoly Φ t) i0) j0
      simpa [evalPolynomialMatrix] using this
    have hev : Polynomial.eval t γ = cval := by
      rw [hγ_def, Polynomial.eval_mul, Polynomial.eval_C, hentry, hcval]
      simp only [Matrix.smul_apply, smul_eq_mul]
      field_simp [hij]
    rw [hev, hcval]
  -- Extract coefficient identities.
  have hmateq : liftC (Φ.Bᵀ * Φ.Y0) - (Polynomial.X : Polynomial ℝ) • liftC (Φ.Vᵀ * Φ.Y0)
      = γ • liftC (attentionMatrix θ 0 h) := by
    rw [← Φ.Xpoly_eq]; exact hXeq
  have hentry : ∀ i j,
      Polynomial.C ((Φ.Bᵀ * Φ.Y0) i j) - Polynomial.X * Polynomial.C ((Φ.Vᵀ * Φ.Y0) i j)
        = γ * Polynomial.C ((attentionMatrix θ 0 h) i j) := by
    intro i j
    have hij_eq := congrFun (congrFun hmateq i) j
    simpa only [Matrix.sub_apply, Matrix.smul_apply, liftC, Matrix.map_apply, smul_eq_mul]
      using hij_eq
  have hc0 : Φ.Bᵀ * Φ.Y0 = (γ.coeff 0) • (attentionMatrix θ 0 h) := by
    ext i j
    have := congrArg (fun p => p.coeff 0) (hentry i j)
    simp only [Matrix.smul_apply, smul_eq_mul]
    simpa [Polynomial.coeff_C, Polynomial.coeff_mul_C] using this
  have hc1 : -(Φ.Vᵀ * Φ.Y0) = (γ.coeff 1) • (attentionMatrix θ 0 h) := by
    ext i j
    have := congrArg (fun p => p.coeff 1) (hentry i j)
    simp only [Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
    simpa [Polynomial.coeff_C, Polynomial.coeff_mul_C, Polynomial.coeff_X_mul] using this
  -- Case analysis forces both coefficients to vanish.
  obtain ⟨hγ0, hγ1⟩ :=
    Φ.gamma_eq_zero (attentionMatrix θ 0 h) (γ.coeff 0) (γ.coeff 1) (by omega)
      hc0 hc1 hclub hdetA hsymA hVne
  -- Conclude `Xpoly = 0`.
  refine ⟨?_, hYzero⟩
  have hB0 : Φ.Bᵀ * Φ.Y0 = 0 := by rw [hc0, hγ0, zero_smul]
  have hV0 : Φ.Vᵀ * Φ.Y0 = 0 := by
    have := hc1; rw [hγ1, zero_smul, neg_eq_zero] at this; exact this
  rw [Φ.Xpoly_eq, hB0, hV0, liftC_zero, smul_zero, sub_zero]

/-- Packaged as the abstract scaffold interface `lem_zero_branch_rigidity_S`, now for the
**faithful** per-head form: rigidity applies to the genuine `phiHeadOfDeeperHead …`, whose
value block is `valueMatrix θ 0 h` by construction (`hVeq` is discharged automatically). -/
theorem lem_zero_branch_rigidity_S_instance {m k d : Nat} {r : Nat}
    (θ : Params (m + 1) k d) (h : Fin k)
    (U : Set (ProbePair d × ℝ)) (labels : DeeperHead → TrichotomyLabel) (dh : DeeperHead)
    (hd : 2 ≤ d) (hreg : Regularity r θ)
    (htop : SignRegionTopologyStatement (attentionMatrix θ 0) (valueMatrix θ 0) h U) :
    lem_zero_branch_rigidity_S (dialPredicates (attentionMatrix θ 0) h) (dialFormalData r θ h)
      U labels dh := by
  intro hvan
  exact lem_zero_branch_rigidity_dial θ h (phiHeadOfDeeperHead r θ h dh labels) U hd hreg
    (phiHeadOfDeeperHead_V r θ h dh labels) htop hvan

/-- Additive `_of_facts` form of `lem_zero_branch_rigidity_S_instance`: the same
faithful per-head rigidity statement, driven by a `FirstHeadRigidityFacts θ h`
bundle and a sign-region topology over a **free** value-matrix parameter `V'`. -/
theorem lem_zero_branch_rigidity_S_instance_of_facts {m k d : Nat} {r : Nat}
    {V' : Fin k → Matrix (Fin d) (Fin d) ℝ}
    (θ : Params (m + 1) k d) (h : Fin k)
    (U : Set (ProbePair d × ℝ)) (labels : DeeperHead → TrichotomyLabel) (dh : DeeperHead)
    (hd : 2 ≤ d) (hfacts : FirstHeadRigidityFacts θ h)
    (htop : SignRegionTopologyStatement (attentionMatrix θ 0) V' h U) :
    lem_zero_branch_rigidity_S (dialPredicates (attentionMatrix θ 0) h) (dialFormalData r θ h)
      U labels dh := by
  intro hvan
  exact lem_zero_branch_rigidity_dial_of_facts θ h (phiHeadOfDeeperHead r θ h dh labels) U hd
    hfacts (phiHeadOfDeeperHead_V r θ h dh labels) htop hvan

/-- Transport an old concrete `LabelSignLink` across a region restriction and a
same- or later-layer label update.  This is pure bookkeeping: signs restrict
along `V ⊆ U`, and the old `Phi`/`Lambda` objects are unchanged by the label
update. -/
theorem labelSignLink_dial_restrict_setLabel_of_layer_le {m k d r : Nat}
    {θ : Params (m + 1) k d} {h : Fin k}
    {U V : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {old current : DeeperHead}
    (label : TrichotomyLabel) (hsub : V ⊆ U)
    (hold : 2 ≤ old.layer) (hle : old.layer ≤ current.layer)
    (hne : old ≠ current)
    (hlink : LabelSignLink (dialPredicates (attentionMatrix θ 0) h)
      (dialFormalData r θ h) U labels old) :
    LabelSignLink (dialPredicates (attentionMatrix θ 0) h)
      (dialFormalData r θ h) V (setLabel labels current label) old := by
  have hphi :
      phiHeadOfDeeperHead r θ h old (setLabel labels current label) =
        phiHeadOfDeeperHead r θ h old labels :=
    phiHeadOfDeeperHead_setLabel_eq_of_layer_le r θ h labels label hold hle
  have hlabel_old : setLabel labels current label old = labels old :=
    setLabel_of_ne labels label hne
  unfold LabelSignLink at hlink ⊢
  rw [hlabel_old]
  cases hlabel : labels old with
  | zero =>
      rw [hlabel] at hlink
      intro x hx
      simpa [dialPredicates, dialFormalData, hphi] using hlink x (hsub hx)
  | one =>
      rw [hlabel] at hlink
      intro x hx
      simpa [dialPredicates, dialFormalData, hphi] using hlink x (hsub hx)
  | alpha =>
      rw [hlabel] at hlink
      simpa [dialPredicates, dialFormalData, hphi] using hlink

/-- Processed-prefix specialization of
`labelSignLink_dial_restrict_setLabel_of_layer_le` for the current head
`(deeperHeadOrder (m+1) k)[n]`.  The layer comparison is kept explicit so this
lemma can be used with any already-proved monotonicity fact for the order. -/
theorem labelSignLink_dial_restrict_setLabel_getElem_of_mem_processedPrefix
    {m k d r : Nat} {θ : Params (m + 1) k d} {h : Fin k}
    {U V : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n : Nat}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    {old : DeeperHead}
    (holdmem : old ∈ processedPrefix (deeperHeadOrder (m + 1) k) n)
    (hle : old.layer ≤ ((deeperHeadOrder (m + 1) k)[n]).layer)
    (label : TrichotomyLabel) (hsub : V ⊆ U)
    (hlink : LabelSignLink (dialPredicates (attentionMatrix θ 0) h)
      (dialFormalData r θ h) U labels old) :
    LabelSignLink (dialPredicates (attentionMatrix θ 0) h)
      (dialFormalData r θ h) V
      (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) label) old := by
  have hold : 2 ≤ old.layer := by
    have hmem_order :
        old ∈ deeperHeadOrder (m + 1) k :=
      mem_order_of_mem_processedPrefix holdmem
    exact (mem_deeperHeadOrder_iff.mp hmem_order).1
  have hnodup : (deeperHeadOrder (m + 1) k).Nodup :=
    deeperHeadOrder_nodup (m + 1) k
  have hcurrent_not :
      (deeperHeadOrder (m + 1) k)[n] ∉
        processedPrefix (deeperHeadOrder (m + 1) k) n :=
    getElem_not_mem_processedPrefix_of_nodup hnodup hn
  have hne : old ≠ (deeperHeadOrder (m + 1) k)[n] := by
    intro heq
    exact hcurrent_not (by simpa [heq] using holdmem)
  exact labelSignLink_dial_restrict_setLabel_of_layer_le (r := r) (θ := θ) (h := h)
    (label := label) hsub hold hle hne hlink

/-- `deeperHeadOrder` convenience wrapper for
`labelSignLink_dial_restrict_setLabel_getElem_of_mem_processedPrefix`: the
lexicographic processed-prefix layer comparison is discharged automatically. -/
theorem labelSignLink_dial_restrict_setLabel_getElem_of_mem_processedPrefix_deeperHeadOrder
    {m k d r : Nat} {θ : Params (m + 1) k d} {h : Fin k}
    {U V : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n : Nat}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    {old : DeeperHead}
    (holdmem : old ∈ processedPrefix (deeperHeadOrder (m + 1) k) n)
    (label : TrichotomyLabel) (hsub : V ⊆ U)
    (hlink : LabelSignLink (dialPredicates (attentionMatrix θ 0) h)
      (dialFormalData r θ h) U labels old) :
    LabelSignLink (dialPredicates (attentionMatrix θ 0) h)
      (dialFormalData r θ h) V
      (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) label) old := by
  exact labelSignLink_dial_restrict_setLabel_getElem_of_mem_processedPrefix
    (r := r) (θ := θ) (h := h) (hn := hn) (holdmem := holdmem)
    (hle := layer_le_getElem_of_mem_processedPrefix_deeperHeadOrder holdmem hn)
    (label := label) hsub hlink

/-- Honest-estimate variant of
`labelSignLink_dial_restrict_setLabel_getElem_of_mem_processedPrefix`.
The sign and zero-polynomial predicates are definitionally the same as for
`dialPredicates`; only the estimate slot changes. -/
theorem labelSignLink_dialWithEstimate_restrict_setLabel_getElem_of_mem_processedPrefix
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {U V : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n : Nat}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    {old : DeeperHead}
    (holdmem : old ∈ processedPrefix (deeperHeadOrder (m + 1) k) n)
    (hle : old.layer ≤ ((deeperHeadOrder (m + 1) k)[n]).layer)
    (label : TrichotomyLabel) (hsub : V ⊆ U)
    (hlink : LabelSignLink (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) U labels old) :
    LabelSignLink (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) V
      (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) label) old := by
  have hold : 2 ≤ old.layer := by
    have hmem_order :
        old ∈ deeperHeadOrder (m + 1) k :=
      mem_order_of_mem_processedPrefix holdmem
    exact (mem_deeperHeadOrder_iff.mp hmem_order).1
  have hnodup : (deeperHeadOrder (m + 1) k).Nodup :=
    deeperHeadOrder_nodup (m + 1) k
  have hcurrent_not :
      (deeperHeadOrder (m + 1) k)[n] ∉
        processedPrefix (deeperHeadOrder (m + 1) k) n :=
    getElem_not_mem_processedPrefix_of_nodup hnodup hn
  have hne : old ≠ (deeperHeadOrder (m + 1) k)[n] := by
    intro heq
    exact hcurrent_not (by simpa [heq] using holdmem)
  have hphi :
      phiHeadOfDeeperHead r θ head old
          (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) label) =
        phiHeadOfDeeperHead r θ head old labels :=
    phiHeadOfDeeperHead_setLabel_eq_of_layer_le r θ head labels label hold hle
  have hlabel_old :
      setLabel labels ((deeperHeadOrder (m + 1) k)[n]) label old = labels old :=
    setLabel_of_ne labels label hne
  unfold LabelSignLink at hlink ⊢
  rw [hlabel_old]
  cases hlabel : labels old with
  | zero =>
      rw [hlabel] at hlink
      intro x hx
      simpa [dialPredicatesWithEstimate, dialFormalData, hphi] using hlink x (hsub hx)
  | one =>
      rw [hlabel] at hlink
      intro x hx
      simpa [dialPredicatesWithEstimate, dialFormalData, hphi] using hlink x (hsub hx)
  | alpha =>
      rw [hlabel] at hlink
      simpa [dialPredicatesWithEstimate, dialFormalData, hphi] using hlink

/-- `deeperHeadOrder` convenience wrapper for the honest-estimate label-link
transport: the processed-prefix layer comparison is discharged automatically. -/
theorem labelSignLink_dialWithEstimate_restrict_setLabel_getElem_of_mem_processedPrefix_deeperHeadOrder
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {U V : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n : Nat}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    {old : DeeperHead}
    (holdmem : old ∈ processedPrefix (deeperHeadOrder (m + 1) k) n)
    (label : TrichotomyLabel) (hsub : V ⊆ U)
    (hlink : LabelSignLink (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) U labels old) :
    LabelSignLink (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) V
      (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) label) old := by
  exact labelSignLink_dialWithEstimate_restrict_setLabel_getElem_of_mem_processedPrefix
    (r := r) (θ := θ) (head := head) (hn := hn) (holdmem := holdmem)
    (hle := layer_le_getElem_of_mem_processedPrefix_deeperHeadOrder holdmem hn)
    (label := label) hsub hlink

/-- Successor processed-prefix splitter for an indexed entry. -/
theorem mem_processedPrefix_succ_iff_getElem {order : List DeeperHead} {n : Nat}
    (hn : n < order.length) {old : DeeperHead} :
    old ∈ processedPrefix order (n + 1) ↔
      old ∈ processedPrefix order n ∨ old = order[n] := by
  revert n
  induction order with
  | nil =>
      intro n hn
      simp at hn
  | cons head tail ih =>
      intro n hn
      cases n with
      | zero =>
          simp [processedPrefix]
      | succ n =>
          have hn_tail : n < tail.length := by
            simpa using Nat.lt_of_succ_lt_succ hn
          have htail := ih hn_tail
          constructor
          · intro hmem
            simp [processedPrefix] at hmem ⊢
            rcases hmem with hhead | htail_mem
            · exact Or.inl (Or.inl hhead)
            · rcases htail.mp htail_mem with hprefix | hcurrent
              · exact Or.inl (Or.inr hprefix)
              · exact Or.inr hcurrent
          · intro hmem
            simp [processedPrefix] at hmem ⊢
            rcases hmem with hprefix | hcurrent
            · rcases hprefix with hhead | hprefix_tail
              · exact Or.inl hhead
              · exact Or.inr (htail.mpr (Or.inl hprefix_tail))
            · exact Or.inr (htail.mpr (Or.inr hcurrent))

/-- Extend the concrete dial estimate by one processed `deeperHeadOrder` entry
when the caller supplies the current gate estimate for the newly set label. -/
theorem DialEstimate.extend_getElem_of_current_gate
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {U : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n : Nat}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    {q : Nat} (hqpos : 1 ≤ q) (hq : q < m + 1) (a : Fin k)
    (hcurrent_eq :
      ((deeperHeadOrder (m + 1) k)[n] : DeeperHead) =
        { layer := q + 1, head := (a : Nat) + 1 })
    (label : TrichotomyLabel)
    (hEst : DialEstimate r θ head (deeperHeadOrder (m + 1) k) n U labels)
    (hcurrent : ∀ x : ProbePair d × ℝ, x ∈ U →
      ExpCloseTo
        (fun τ => actualProbeGate r θ
          (headDialPath (attentionMatrix θ 0) head (logScale r) x.1 x.2 τ).1
          (headDialPath (attentionMatrix θ 0) head (logScale r) x.1 x.2 τ).2
          τ ⟨q, hq⟩ a)
        (label.eval 0 1 (alpha r))) :
    DialEstimate r θ head (deeperHeadOrder (m + 1) k) (n + 1) U
      (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) label) where
  gate := by
    intro q' hqpos' hq' a' hmem x hx
    have hsplit :=
      (mem_processedPrefix_succ_iff_getElem
        (order := deeperHeadOrder (m + 1) k) (n := n) hn).mp hmem
    rcases hsplit with hold | hcurrent_mem
    · have hstable :
        trichotomyToSaturatedLabels r (m + 1) k
            (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) label)
            (q' + 1) a' =
          trichotomyToSaturatedLabels r (m + 1) k labels (q' + 1) a' := by
        have hset :
            setLabel labels ((deeperHeadOrder (m + 1) k)[n]) label
                ({ layer := q' + 1, head := (a' : Nat) + 1 } : DeeperHead) =
              labels ({ layer := q' + 1, head := (a' : Nat) + 1 } : DeeperHead) :=
          setLabel_eq_on_processedPrefix_of_getElem_nodup
            (deeperHeadOrder_nodup (m + 1) k) labels hn label hold
        simpa [trichotomyToSaturatedLabels] using
          congrArg (fun label => label.eval 0 1 (alpha r)) hset
      rw [hstable]
      exact hEst.gate hqpos' hq' a' hold x hx
    · have hgate_eq :
          ({ layer := q' + 1, head := (a' : Nat) + 1 } : DeeperHead) =
            ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead) :=
        hcurrent_mem.trans hcurrent_eq
      have hqeq : q' = q := by
        have := congrArg DeeperHead.layer hgate_eq
        simpa using this
      have haeq_val : (a' : Nat) = (a : Nat) := by
        have hhead_succ : (a' : Nat) + 1 = (a : Nat) + 1 := by
          simpa using congrArg DeeperHead.head hgate_eq
        exact Nat.succ.inj hhead_succ
      have haeq : a' = a := Fin.ext haeq_val
      have hlabel_current :
          trichotomyToSaturatedLabels r (m + 1) k
              (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) label)
              (q + 1) a =
            label.eval 0 1 (alpha r) := by
        apply trichotomyToSaturatedLabels_eq_of_label
        rw [← hcurrent_eq]
        exact setLabel_self labels ((deeperHeadOrder (m + 1) k)[n]) label
      simpa [hqeq, haeq, hlabel_current] using hcurrent x hx

/-- Extend an honest dial estimate to a smaller successor region after setting the
current `deeperHeadOrder` label.  The caller supplies the current-head gate
estimate only on the successor region. -/
theorem DialEstimate.extend_getElem_subset_of_current_gate
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {currentRegion nextRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n : Nat}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    {q : Nat} (hqpos : 1 ≤ q) (hq : q < m + 1) (a : Fin k)
    (hcurrent_eq :
      ((deeperHeadOrder (m + 1) k)[n] : DeeperHead) =
        { layer := q + 1, head := (a : Nat) + 1 })
    (label : TrichotomyLabel)
    (hsub : nextRegion ⊆ currentRegion)
    (hEst :
      DialEstimate r θ head (deeperHeadOrder (m + 1) k) n currentRegion labels)
    (hcurrent : ∀ x : ProbePair d × ℝ, x ∈ nextRegion →
      ExpCloseTo
        (fun τ => actualProbeGate r θ
          (headDialPath (attentionMatrix θ 0) head (logScale r) x.1 x.2 τ).1
          (headDialPath (attentionMatrix θ 0) head (logScale r) x.1 x.2 τ).2
          τ ⟨q, hq⟩ a)
        (label.eval 0 1 (alpha r))) :
    (dialPredicatesWithEstimate r θ head).Estimate
      (deeperHeadOrder (m + 1) k) (n + 1) nextRegion
      (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) label) :=
  DialEstimate.extend_getElem_of_current_gate
    (r := r) (θ := θ) (head := head) (U := nextRegion) (labels := labels)
    (hn := hn) hqpos hq a hcurrent_eq label
    (DialEstimate.restrict hsub hEst) hcurrent

/-- Honest successor estimate for the positive branch, with the current gate
estimate supplied explicitly on the successor region. -/
theorem DialEstimate.estimate_one_getElem
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {currentRegion nextRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n : Nat}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    {q : Nat} (hqpos : 1 ≤ q) (hq : q < m + 1) (a : Fin k)
    (hcurrent_eq :
      ((deeperHeadOrder (m + 1) k)[n] : DeeperHead) =
        { layer := q + 1, head := (a : Nat) + 1 })
    (hsub : nextRegion ⊆ currentRegion)
    (hEst :
      DialEstimate r θ head (deeperHeadOrder (m + 1) k) n currentRegion labels)
    (hcurrent : ∀ x : ProbePair d × ℝ, x ∈ nextRegion →
      ExpCloseTo
        (fun τ => actualProbeGate r θ
          (headDialPath (attentionMatrix θ 0) head (logScale r) x.1 x.2 τ).1
          (headDialPath (attentionMatrix θ 0) head (logScale r) x.1 x.2 τ).2
          τ ⟨q, hq⟩ a)
        1) :
    (dialPredicatesWithEstimate r θ head).Estimate
      (deeperHeadOrder (m + 1) k) (n + 1) nextRegion
      (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) TrichotomyLabel.one) :=
  DialEstimate.extend_getElem_subset_of_current_gate
    (r := r) (θ := θ) (head := head) (currentRegion := currentRegion)
    (nextRegion := nextRegion) (labels := labels) (hn := hn)
    hqpos hq a hcurrent_eq TrichotomyLabel.one hsub hEst
    (by
      intro x hx
      simpa using hcurrent x hx)

/-- Honest successor estimate for the negative/zero-label branch, with the
current gate estimate supplied explicitly on the successor region. -/
theorem DialEstimate.estimate_zero_getElem
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {currentRegion nextRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n : Nat}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    {q : Nat} (hqpos : 1 ≤ q) (hq : q < m + 1) (a : Fin k)
    (hcurrent_eq :
      ((deeperHeadOrder (m + 1) k)[n] : DeeperHead) =
        { layer := q + 1, head := (a : Nat) + 1 })
    (hsub : nextRegion ⊆ currentRegion)
    (hEst :
      DialEstimate r θ head (deeperHeadOrder (m + 1) k) n currentRegion labels)
    (hcurrent : ∀ x : ProbePair d × ℝ, x ∈ nextRegion →
      ExpCloseTo
        (fun τ => actualProbeGate r θ
          (headDialPath (attentionMatrix θ 0) head (logScale r) x.1 x.2 τ).1
          (headDialPath (attentionMatrix θ 0) head (logScale r) x.1 x.2 τ).2
          τ ⟨q, hq⟩ a)
        0) :
    (dialPredicatesWithEstimate r θ head).Estimate
      (deeperHeadOrder (m + 1) k) (n + 1) nextRegion
      (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) TrichotomyLabel.zero) :=
  DialEstimate.extend_getElem_subset_of_current_gate
    (r := r) (θ := θ) (head := head) (currentRegion := currentRegion)
    (nextRegion := nextRegion) (labels := labels) (hn := hn)
    hqpos hq a hcurrent_eq TrichotomyLabel.zero hsub hEst
    (by
      intro x hx
      simpa using hcurrent x hx)

/-- Honest successor estimate for the alpha branch, with the current gate
estimate supplied explicitly on the successor region. -/
theorem DialEstimate.estimate_alpha_getElem
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {currentRegion nextRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n : Nat}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    {q : Nat} (hqpos : 1 ≤ q) (hq : q < m + 1) (a : Fin k)
    (hcurrent_eq :
      ((deeperHeadOrder (m + 1) k)[n] : DeeperHead) =
        { layer := q + 1, head := (a : Nat) + 1 })
    (hsub : nextRegion ⊆ currentRegion)
    (hEst :
      DialEstimate r θ head (deeperHeadOrder (m + 1) k) n currentRegion labels)
    (hcurrent : ∀ x : ProbePair d × ℝ, x ∈ nextRegion →
      ExpCloseTo
        (fun τ => actualProbeGate r θ
          (headDialPath (attentionMatrix θ 0) head (logScale r) x.1 x.2 τ).1
          (headDialPath (attentionMatrix θ 0) head (logScale r) x.1 x.2 τ).2
          τ ⟨q, hq⟩ a)
        (alpha r)) :
    (dialPredicatesWithEstimate r θ head).Estimate
      (deeperHeadOrder (m + 1) k) (n + 1) nextRegion
      (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) TrichotomyLabel.alpha) :=
  DialEstimate.extend_getElem_subset_of_current_gate
    (r := r) (θ := θ) (head := head) (currentRegion := currentRegion)
    (nextRegion := nextRegion) (labels := labels) (hn := hn)
    hqpos hq a hcurrent_eq TrichotomyLabel.alpha hsub hEst
    (by
      intro x hx
      simpa using hcurrent x hx)

/-- Assemble the next concrete processing invariant after setting the current
`deeperHeadOrder` label.  The old processed links are transported by the
prefix/set-label stability lemmas; the caller supplies exactly the new current
head link and the branch-specific estimate. -/
theorem processingInvariant_dial_setLabel_getElem_of_current_link
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {baseRegion currentRegion nextRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n : Nat}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    (label : TrichotomyLabel)
    (hInv : ProcessingInvariantStatement (dialPredicates (attentionMatrix θ 0) head)
      (dialFormalData r θ head) baseRegion currentRegion
      (deeperHeadOrder (m + 1) k) n labels)
    (hsub : nextRegion ⊆ currentRegion)
    (hnonempty : nextRegion.Nonempty)
    (hconnected : IsPreconnected nextRegion)
    (hrelopen :
      RelativelyOpenIn nextRegion (quadricPatchCylinder (attentionMatrix θ 0) head))
    (hestimate :
      (dialPredicates (attentionMatrix θ 0) head).Estimate
        (deeperHeadOrder (m + 1) k) (n + 1) nextRegion
        (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) label))
    (hcurrent : LabelSignLink (dialPredicates (attentionMatrix θ 0) head)
      (dialFormalData r θ head) nextRegion
      (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) label)
      ((deeperHeadOrder (m + 1) k)[n])) :
    ProcessingInvariantStatement (dialPredicates (attentionMatrix θ 0) head)
      (dialFormalData r θ head) baseRegion nextRegion
      (deeperHeadOrder (m + 1) k) (n + 1)
      (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) label) where
  region_nonempty := hnonempty
  region_connected := hconnected
  region_relativelyOpen := hrelopen
  region_subset_base := hsub.trans hInv.region_subset_base
  label_sign_link := by
    intro old hold_succ
    have hsplit :=
      (mem_processedPrefix_succ_iff_getElem
        (order := deeperHeadOrder (m + 1) k) (n := n) hn).mp hold_succ
    rcases hsplit with hold_old | hcurrent_eq
    · exact
        labelSignLink_dial_restrict_setLabel_getElem_of_mem_processedPrefix_deeperHeadOrder
          (r := r) (θ := θ) (h := head) (U := currentRegion) (V := nextRegion)
          (labels := labels) (hn := hn) (old := old) hold_old label hsub
          (hInv.label_sign_link old hold_old)
    · simpa [hcurrent_eq] using hcurrent
  estimate := hestimate

/-- Package `processingInvariant_dial_setLabel_getElem_of_current_link` as a
one-step result for a concrete branch. -/
noncomputable def trichotomyStepResult_dial_setLabel_getElem_of_current_link
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {baseRegion currentRegion nextRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n : Nat}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    (branch : TrichotomyStepBranch) (label : TrichotomyLabel)
    (hInv : ProcessingInvariantStatement (dialPredicates (attentionMatrix θ 0) head)
      (dialFormalData r θ head) baseRegion currentRegion
      (deeperHeadOrder (m + 1) k) n labels)
    (hsub : nextRegion ⊆ currentRegion)
    (hnonempty : nextRegion.Nonempty)
    (hconnected : IsPreconnected nextRegion)
    (hrelopen :
      RelativelyOpenIn nextRegion (quadricPatchCylinder (attentionMatrix θ 0) head))
    (hestimate :
      (dialPredicates (attentionMatrix θ 0) head).Estimate
        (deeperHeadOrder (m + 1) k) (n + 1) nextRegion
        (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) label))
    (hcurrent : LabelSignLink (dialPredicates (attentionMatrix θ 0) head)
      (dialFormalData r θ head) nextRegion
      (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) label)
      ((deeperHeadOrder (m + 1) k)[n])) :
    TrichotomyStepResult (dialPredicates (attentionMatrix θ 0) head)
      (dialFormalData r θ head) baseRegion currentRegion
      (deeperHeadOrder (m + 1) k) n labels
      ((deeperHeadOrder (m + 1) k)[n]) where
  branch := branch
  nextRegion := nextRegion
  nextLabels := setLabel labels ((deeperHeadOrder (m + 1) k)[n]) label
  nextRegion_subset_current := hsub
  processed_label := by
    rw [setLabel_self]
    cases label <;> simp
  next_invariant :=
    processingInvariant_dial_setLabel_getElem_of_current_link
      (r := r) (θ := θ) (head := head) (hn := hn) label hInv hsub
      hnonempty hconnected hrelopen hestimate hcurrent

/-- Honest-estimate variant of
`processingInvariant_dial_setLabel_getElem_of_current_link`.  The old processed
links are transported exactly as before; the caller supplies the successor
`DialEstimate` payload and current-head sign link for `dialPredicatesWithEstimate`. -/
theorem processingInvariant_dialWithEstimate_setLabel_getElem_of_current_link
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {baseRegion currentRegion nextRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n : Nat}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    (label : TrichotomyLabel)
    (hInv : ProcessingInvariantStatement (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) baseRegion currentRegion
      (deeperHeadOrder (m + 1) k) n labels)
    (hsub : nextRegion ⊆ currentRegion)
    (hnonempty : nextRegion.Nonempty)
    (hconnected : IsPreconnected nextRegion)
    (hrelopen :
      RelativelyOpenIn nextRegion (quadricPatchCylinder (attentionMatrix θ 0) head))
    (hestimate :
      (dialPredicatesWithEstimate r θ head).Estimate
        (deeperHeadOrder (m + 1) k) (n + 1) nextRegion
        (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) label))
    (hcurrent : LabelSignLink (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) nextRegion
      (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) label)
      ((deeperHeadOrder (m + 1) k)[n])) :
    ProcessingInvariantStatement (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) baseRegion nextRegion
      (deeperHeadOrder (m + 1) k) (n + 1)
      (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) label) where
  region_nonempty := hnonempty
  region_connected := hconnected
  region_relativelyOpen := hrelopen
  region_subset_base := hsub.trans hInv.region_subset_base
  label_sign_link := by
    intro old hold_succ
    have hsplit :=
      (mem_processedPrefix_succ_iff_getElem
        (order := deeperHeadOrder (m + 1) k) (n := n) hn).mp hold_succ
    rcases hsplit with hold_old | hcurrent_eq
    · exact
        labelSignLink_dialWithEstimate_restrict_setLabel_getElem_of_mem_processedPrefix_deeperHeadOrder
          (r := r) (θ := θ) (head := head) (U := currentRegion) (V := nextRegion)
          (labels := labels) (hn := hn) (old := old) hold_old label hsub
          (hInv.label_sign_link old hold_old)
    · simpa [hcurrent_eq] using hcurrent
  estimate := hestimate

/-- Package
`processingInvariant_dialWithEstimate_setLabel_getElem_of_current_link` as a
one-step result for a concrete branch using the honest estimate predicate. -/
noncomputable def trichotomyStepResult_dialWithEstimate_setLabel_getElem_of_current_link
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {baseRegion currentRegion nextRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n : Nat}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    (branch : TrichotomyStepBranch) (label : TrichotomyLabel)
    (hInv : ProcessingInvariantStatement (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) baseRegion currentRegion
      (deeperHeadOrder (m + 1) k) n labels)
    (hsub : nextRegion ⊆ currentRegion)
    (hnonempty : nextRegion.Nonempty)
    (hconnected : IsPreconnected nextRegion)
    (hrelopen :
      RelativelyOpenIn nextRegion (quadricPatchCylinder (attentionMatrix θ 0) head))
    (hestimate :
      (dialPredicatesWithEstimate r θ head).Estimate
        (deeperHeadOrder (m + 1) k) (n + 1) nextRegion
        (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) label))
    (hcurrent : LabelSignLink (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) nextRegion
      (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) label)
      ((deeperHeadOrder (m + 1) k)[n])) :
    TrichotomyStepResult (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) baseRegion currentRegion
      (deeperHeadOrder (m + 1) k) n labels
      ((deeperHeadOrder (m + 1) k)[n]) where
  branch := branch
  nextRegion := nextRegion
  nextLabels := setLabel labels ((deeperHeadOrder (m + 1) k)[n]) label
  nextRegion_subset_current := hsub
  processed_label := by
    rw [setLabel_self]
    cases label <;> simp
  next_invariant :=
    processingInvariant_dialWithEstimate_setLabel_getElem_of_current_link
      (r := r) (θ := θ) (head := head) (hn := hn) label hInv hsub
      hnonempty hconnected hrelopen hestimate hcurrent

/-- The concrete positive-branch component through a point where the current
dial polynomial is positive. -/
noncomputable def positiveBranchComponent_getElem
    {m k d r : Nat} (θ : Params (m + 1) k d) (head : Fin k)
    (currentRegion : Set (ProbePair d × ℝ))
    (labels : DeeperHead → TrichotomyLabel) (n : Nat)
    (hn : n < (deeperHeadOrder (m + 1) k).length) (x0 : ProbePair d × ℝ) :
    Set (ProbePair d × ℝ) :=
  connectedComponentIn
    (currentRegion ∩
      {x : ProbePair d × ℝ |
        dialEval
          (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels) x ≠ 0})
    x0

/-- Topology package for the concrete positive branch component. -/
theorem positiveBranchComponent_getElem_topology
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {baseRegion currentRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n : Nat}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    (hInv : ProcessingInvariantStatement (dialPredicates (attentionMatrix θ 0) head)
      (dialFormalData r θ head) baseRegion currentRegion
      (deeperHeadOrder (m + 1) k) n labels)
    {x0 : ProbePair d × ℝ}
    (hx0_current : x0 ∈ currentRegion)
    (hx0_pos :
      0 < dialEval
        (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels) x0)
    (hdet : (attentionMatrix θ 0 head).det ≠ 0) :
    (positiveBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0).Nonempty ∧
      IsPreconnected
        (positiveBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0) ∧
      RelativelyOpenIn
        (positiveBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0)
        (quadricPatchCylinder (attentionMatrix θ 0) head) ∧
      positiveBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0 ⊆
        currentRegion := by
  let Φ : QuadraticDialForm d :=
    phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels
  let nonzeroLocus : Set (ProbePair d × ℝ) := {x | dialEval Φ x ≠ 0}
  let nextRegion : Set (ProbePair d × ℝ) :=
    positiveBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0
  have hnext :
      nextRegion = connectedComponentIn (currentRegion ∩ nonzeroLocus) x0 := by
    rfl
  have hx0_nonzero : dialEval Φ x0 ≠ 0 := ne_of_gt (by
    simpa [Φ] using hx0_pos)
  have hx0_open : x0 ∈ currentRegion ∩ nonzeroLocus := ⟨hx0_current, hx0_nonzero⟩
  have hsub : nextRegion ⊆ currentRegion := by
    intro x hx
    rw [hnext] at hx
    exact (connectedComponentIn_subset (currentRegion ∩ nonzeroLocus) x0 hx).1
  have hnonempty : nextRegion.Nonempty := by
    rw [hnext]
    exact ⟨x0, mem_connectedComponentIn hx0_open⟩
  have hconnected : IsPreconnected nextRegion := by
    rw [hnext]
    exact isPreconnected_connectedComponentIn
  have hopen_current :
      RelativelyOpenIn (currentRegion ∩ nonzeroLocus)
        (quadricPatchCylinder (attentionMatrix θ 0) head) := by
    change RelativelyOpenIn (currentRegion ∩ {x | dialEval Φ x ≠ 0})
      (quadricPatchCylinder (attentionMatrix θ 0) head)
    exact hInv.region_relativelyOpen.inter_open (isOpen_dialEval_ne_zero Φ)
  have hrelopen :
      RelativelyOpenIn nextRegion (quadricPatchCylinder (attentionMatrix θ 0) head) := by
    rw [hnext]
    exact connectedComponentIn_relativelyOpenIn_quadricPatchCylinder
      (A := attentionMatrix θ 0) (h := head) hdet hopen_current hx0_open
  exact ⟨hnonempty, hconnected, hrelopen, hsub⟩

/-- Current-head sign link for the concrete positive branch component. -/
theorem labelSignLink_dial_positiveBranchComponent_getElem
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {currentRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n : Nat}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    {x0 : ProbePair d × ℝ}
    (hx0_current : x0 ∈ currentRegion)
    (hx0_pos :
      0 < dialEval
        (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels) x0) :
    LabelSignLink (dialPredicates (attentionMatrix θ 0) head)
      (dialFormalData r θ head)
      (positiveBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0)
      (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) TrichotomyLabel.one)
      ((deeperHeadOrder (m + 1) k)[n]) := by
  let current : DeeperHead := (deeperHeadOrder (m + 1) k)[n]
  let Φ : QuadraticDialForm d := phiHeadOfDeeperHead r θ head current labels
  let nonzeroLocus : Set (ProbePair d × ℝ) := {x | dialEval Φ x ≠ 0}
  let nextRegion : Set (ProbePair d × ℝ) :=
    positiveBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0
  have hnext :
      nextRegion = connectedComponentIn (currentRegion ∩ nonzeroLocus) x0 := by
    rfl
  have hx0_posΦ : 0 < dialEval Φ x0 := by
    simpa [Φ, current] using hx0_pos
  have hx0_nonzero : dialEval Φ x0 ≠ 0 := ne_of_gt hx0_posΦ
  have hx0_open : x0 ∈ currentRegion ∩ nonzeroLocus := ⟨hx0_current, hx0_nonzero⟩
  have hcurrent_layer : 2 ≤ current.layer := by
    have hmem : current ∈ deeperHeadOrder (m + 1) k :=
      List.getElem_mem hn
    exact (mem_deeperHeadOrder_iff.mp hmem).1
  have hlambda_current :
      (dialFormalData r θ head).Lambda current
          (setLabel labels current TrichotomyLabel.one) =
        (dialFormalData r θ head).Lambda current labels :=
    dialFormalData_Lambda_setLabel_eq_of_layer_le r θ head labels TrichotomyLabel.one
      hcurrent_layer le_rfl
  have hpos_on : ∀ x ∈ nextRegion, 0 < dialEval Φ x := by
    rw [hnext]
    apply positiveOn_of_preconnected_of_nonzero isPreconnected_connectedComponentIn
      (continuous_dialEval Φ)
    · intro x hx
      exact (connectedComponentIn_subset (currentRegion ∩ nonzeroLocus) x0 hx).2
    · exact ⟨x0, mem_connectedComponentIn hx0_open, hx0_posΦ⟩
  change LabelSignLink (dialPredicates (attentionMatrix θ 0) head)
    (dialFormalData r θ head) nextRegion
    (setLabel labels current TrichotomyLabel.one) current
  unfold LabelSignLink
  rw [setLabel_self]
  change ∀ x ∈ nextRegion,
    0 < dialEval
      ((dialFormalData r θ head).Lambda current
        (setLabel labels current TrichotomyLabel.one)) x
  rw [hlambda_current]
  exact hpos_on

/-- One-step result wrapper for the concrete positive branch component, with the
branch estimate supplied explicitly. -/
noncomputable def trichotomyStepResult_dial_positiveBranchComponent_getElem
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {baseRegion currentRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n : Nat}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    (hInv : ProcessingInvariantStatement (dialPredicates (attentionMatrix θ 0) head)
      (dialFormalData r θ head) baseRegion currentRegion
      (deeperHeadOrder (m + 1) k) n labels)
    {x0 : ProbePair d × ℝ}
    (hx0_current : x0 ∈ currentRegion)
    (hx0_pos :
      0 < dialEval
        (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels) x0)
    (hdet : (attentionMatrix θ 0 head).det ≠ 0)
    (hestimate :
      (dialPredicates (attentionMatrix θ 0) head).Estimate
        (deeperHeadOrder (m + 1) k) (n + 1)
        (positiveBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0)
        (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) TrichotomyLabel.one)) :
    TrichotomyStepResult (dialPredicates (attentionMatrix θ 0) head)
      (dialFormalData r θ head) baseRegion currentRegion
      (deeperHeadOrder (m + 1) k) n labels
      ((deeperHeadOrder (m + 1) k)[n]) :=
  let htop := positiveBranchComponent_getElem_topology
    (r := r) (θ := θ) (head := head) (hn := hn) hInv hx0_current hx0_pos hdet
  trichotomyStepResult_dial_setLabel_getElem_of_current_link
    (r := r) (θ := θ) (head := head) (hn := hn) TrichotomyStepBranch.nonzero
    TrichotomyLabel.one hInv
    htop.2.2.2 htop.1 htop.2.1 htop.2.2.1
    hestimate
    (labelSignLink_dial_positiveBranchComponent_getElem
      (r := r) (θ := θ) (head := head) (hn := hn) hx0_current hx0_pos)

/-- Honest-estimate topology package for the concrete positive branch component. -/
theorem positiveBranchComponent_getElem_topology_withEstimate
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {baseRegion currentRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n : Nat}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    (hInv : ProcessingInvariantStatement (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) baseRegion currentRegion
      (deeperHeadOrder (m + 1) k) n labels)
    {x0 : ProbePair d × ℝ}
    (hx0_current : x0 ∈ currentRegion)
    (hx0_pos :
      0 < dialEval
        (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels) x0)
    (hdet : (attentionMatrix θ 0 head).det ≠ 0) :
    (positiveBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0).Nonempty ∧
      IsPreconnected
        (positiveBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0) ∧
      RelativelyOpenIn
        (positiveBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0)
        (quadricPatchCylinder (attentionMatrix θ 0) head) ∧
      positiveBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0 ⊆
        currentRegion := by
  let Φ : QuadraticDialForm d :=
    phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels
  let nonzeroLocus : Set (ProbePair d × ℝ) := {x | dialEval Φ x ≠ 0}
  let nextRegion : Set (ProbePair d × ℝ) :=
    positiveBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0
  have hnext :
      nextRegion = connectedComponentIn (currentRegion ∩ nonzeroLocus) x0 := by
    rfl
  have hx0_nonzero : dialEval Φ x0 ≠ 0 := ne_of_gt (by
    simpa [Φ] using hx0_pos)
  have hx0_open : x0 ∈ currentRegion ∩ nonzeroLocus := ⟨hx0_current, hx0_nonzero⟩
  have hsub : nextRegion ⊆ currentRegion := by
    intro x hx
    rw [hnext] at hx
    exact (connectedComponentIn_subset (currentRegion ∩ nonzeroLocus) x0 hx).1
  have hnonempty : nextRegion.Nonempty := by
    rw [hnext]
    exact ⟨x0, mem_connectedComponentIn hx0_open⟩
  have hconnected : IsPreconnected nextRegion := by
    rw [hnext]
    exact isPreconnected_connectedComponentIn
  have hopen_current :
      RelativelyOpenIn (currentRegion ∩ nonzeroLocus)
        (quadricPatchCylinder (attentionMatrix θ 0) head) := by
    change RelativelyOpenIn (currentRegion ∩ {x | dialEval Φ x ≠ 0})
      (quadricPatchCylinder (attentionMatrix θ 0) head)
    exact hInv.region_relativelyOpen.inter_open (isOpen_dialEval_ne_zero Φ)
  have hrelopen :
      RelativelyOpenIn nextRegion (quadricPatchCylinder (attentionMatrix θ 0) head) := by
    rw [hnext]
    exact connectedComponentIn_relativelyOpenIn_quadricPatchCylinder
      (A := attentionMatrix θ 0) (h := head) hdet hopen_current hx0_open
  exact ⟨hnonempty, hconnected, hrelopen, hsub⟩

/-- Honest-estimate current-head sign link for the concrete positive branch component. -/
theorem labelSignLink_dialWithEstimate_positiveBranchComponent_getElem
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {currentRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n : Nat}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    {x0 : ProbePair d × ℝ}
    (hx0_current : x0 ∈ currentRegion)
    (hx0_pos :
      0 < dialEval
        (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels) x0) :
    LabelSignLink (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head)
      (positiveBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0)
      (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) TrichotomyLabel.one)
      ((deeperHeadOrder (m + 1) k)[n]) := by
  let current : DeeperHead := (deeperHeadOrder (m + 1) k)[n]
  let Φ : QuadraticDialForm d := phiHeadOfDeeperHead r θ head current labels
  let nonzeroLocus : Set (ProbePair d × ℝ) := {x | dialEval Φ x ≠ 0}
  let nextRegion : Set (ProbePair d × ℝ) :=
    positiveBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0
  have hnext :
      nextRegion = connectedComponentIn (currentRegion ∩ nonzeroLocus) x0 := by
    rfl
  have hx0_posΦ : 0 < dialEval Φ x0 := by
    simpa [Φ, current] using hx0_pos
  have hx0_nonzero : dialEval Φ x0 ≠ 0 := ne_of_gt hx0_posΦ
  have hx0_open : x0 ∈ currentRegion ∩ nonzeroLocus := ⟨hx0_current, hx0_nonzero⟩
  have hcurrent_layer : 2 ≤ current.layer := by
    have hmem : current ∈ deeperHeadOrder (m + 1) k :=
      List.getElem_mem hn
    exact (mem_deeperHeadOrder_iff.mp hmem).1
  have hlambda_current :
      (dialFormalData r θ head).Lambda current
          (setLabel labels current TrichotomyLabel.one) =
        (dialFormalData r θ head).Lambda current labels :=
    dialFormalData_Lambda_setLabel_eq_of_layer_le r θ head labels TrichotomyLabel.one
      hcurrent_layer le_rfl
  have hpos_on : ∀ x ∈ nextRegion, 0 < dialEval Φ x := by
    rw [hnext]
    apply positiveOn_of_preconnected_of_nonzero isPreconnected_connectedComponentIn
      (continuous_dialEval Φ)
    · intro x hx
      exact (connectedComponentIn_subset (currentRegion ∩ nonzeroLocus) x0 hx).2
    · exact ⟨x0, mem_connectedComponentIn hx0_open, hx0_posΦ⟩
  change LabelSignLink (dialPredicatesWithEstimate r θ head)
    (dialFormalData r θ head) nextRegion
    (setLabel labels current TrichotomyLabel.one) current
  unfold LabelSignLink
  rw [setLabel_self]
  change ∀ x ∈ nextRegion,
    0 < dialEval
      ((dialFormalData r θ head).Lambda current
        (setLabel labels current TrichotomyLabel.one)) x
  rw [hlambda_current]
  exact hpos_on

/-- One-step result wrapper for the concrete positive branch component using the
honest estimate predicate, with the branch estimate supplied explicitly. -/
noncomputable def trichotomyStepResult_dialWithEstimate_positiveBranchComponent_getElem
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {baseRegion currentRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n : Nat}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    (hInv : ProcessingInvariantStatement (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) baseRegion currentRegion
      (deeperHeadOrder (m + 1) k) n labels)
    {x0 : ProbePair d × ℝ}
    (hx0_current : x0 ∈ currentRegion)
    (hx0_pos :
      0 < dialEval
        (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels) x0)
    (hdet : (attentionMatrix θ 0 head).det ≠ 0)
    (hestimate :
      (dialPredicatesWithEstimate r θ head).Estimate
        (deeperHeadOrder (m + 1) k) (n + 1)
        (positiveBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0)
        (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) TrichotomyLabel.one)) :
    TrichotomyStepResult (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) baseRegion currentRegion
      (deeperHeadOrder (m + 1) k) n labels
      ((deeperHeadOrder (m + 1) k)[n]) :=
  let htop := positiveBranchComponent_getElem_topology_withEstimate
    (r := r) (θ := θ) (head := head) (hn := hn) hInv hx0_current hx0_pos hdet
  trichotomyStepResult_dialWithEstimate_setLabel_getElem_of_current_link
    (r := r) (θ := θ) (head := head) (hn := hn) TrichotomyStepBranch.nonzero
    TrichotomyLabel.one hInv
    htop.2.2.2 htop.1 htop.2.1 htop.2.2.1
    hestimate
    (labelSignLink_dialWithEstimate_positiveBranchComponent_getElem
      (r := r) (θ := θ) (head := head) (hn := hn) hx0_current hx0_pos)

/-- The concrete negative-branch component through a point where the current
dial polynomial is negative. -/
noncomputable def negativeBranchComponent_getElem
    {m k d r : Nat} (θ : Params (m + 1) k d) (head : Fin k)
    (currentRegion : Set (ProbePair d × ℝ))
    (labels : DeeperHead → TrichotomyLabel) (n : Nat)
    (hn : n < (deeperHeadOrder (m + 1) k).length) (x0 : ProbePair d × ℝ) :
    Set (ProbePair d × ℝ) :=
  connectedComponentIn
    (currentRegion ∩
      {x : ProbePair d × ℝ |
        dialEval
          (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels) x ≠ 0})
    x0

/-- Topology package for the concrete negative branch component. -/
theorem negativeBranchComponent_getElem_topology
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {baseRegion currentRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n : Nat}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    (hInv : ProcessingInvariantStatement (dialPredicates (attentionMatrix θ 0) head)
      (dialFormalData r θ head) baseRegion currentRegion
      (deeperHeadOrder (m + 1) k) n labels)
    {x0 : ProbePair d × ℝ}
    (hx0_current : x0 ∈ currentRegion)
    (hx0_neg :
      dialEval
        (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels) x0 < 0)
    (hdet : (attentionMatrix θ 0 head).det ≠ 0) :
    (negativeBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0).Nonempty ∧
      IsPreconnected
        (negativeBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0) ∧
      RelativelyOpenIn
        (negativeBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0)
        (quadricPatchCylinder (attentionMatrix θ 0) head) ∧
      negativeBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0 ⊆
        currentRegion := by
  let Φ : QuadraticDialForm d :=
    phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels
  let nonzeroLocus : Set (ProbePair d × ℝ) := {x | dialEval Φ x ≠ 0}
  let nextRegion : Set (ProbePair d × ℝ) :=
    negativeBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0
  have hnext :
      nextRegion = connectedComponentIn (currentRegion ∩ nonzeroLocus) x0 := by
    rfl
  have hx0_nonzero : dialEval Φ x0 ≠ 0 := ne_of_lt (by
    simpa [Φ] using hx0_neg)
  have hx0_open : x0 ∈ currentRegion ∩ nonzeroLocus := ⟨hx0_current, hx0_nonzero⟩
  have hsub : nextRegion ⊆ currentRegion := by
    intro x hx
    rw [hnext] at hx
    exact (connectedComponentIn_subset (currentRegion ∩ nonzeroLocus) x0 hx).1
  have hnonempty : nextRegion.Nonempty := by
    rw [hnext]
    exact ⟨x0, mem_connectedComponentIn hx0_open⟩
  have hconnected : IsPreconnected nextRegion := by
    rw [hnext]
    exact isPreconnected_connectedComponentIn
  have hopen_current :
      RelativelyOpenIn (currentRegion ∩ nonzeroLocus)
        (quadricPatchCylinder (attentionMatrix θ 0) head) := by
    change RelativelyOpenIn (currentRegion ∩ {x | dialEval Φ x ≠ 0})
      (quadricPatchCylinder (attentionMatrix θ 0) head)
    exact hInv.region_relativelyOpen.inter_open (isOpen_dialEval_ne_zero Φ)
  have hrelopen :
      RelativelyOpenIn nextRegion (quadricPatchCylinder (attentionMatrix θ 0) head) := by
    rw [hnext]
    exact connectedComponentIn_relativelyOpenIn_quadricPatchCylinder
      (A := attentionMatrix θ 0) (h := head) hdet hopen_current hx0_open
  exact ⟨hnonempty, hconnected, hrelopen, hsub⟩

/-- Current-head sign link for the concrete negative branch component. -/
theorem labelSignLink_dial_negativeBranchComponent_getElem
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {currentRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n : Nat}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    {x0 : ProbePair d × ℝ}
    (hx0_current : x0 ∈ currentRegion)
    (hx0_neg :
      dialEval
        (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels) x0 < 0) :
    LabelSignLink (dialPredicates (attentionMatrix θ 0) head)
      (dialFormalData r θ head)
      (negativeBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0)
      (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) TrichotomyLabel.zero)
      ((deeperHeadOrder (m + 1) k)[n]) := by
  let current : DeeperHead := (deeperHeadOrder (m + 1) k)[n]
  let Φ : QuadraticDialForm d := phiHeadOfDeeperHead r θ head current labels
  let nonzeroLocus : Set (ProbePair d × ℝ) := {x | dialEval Φ x ≠ 0}
  let nextRegion : Set (ProbePair d × ℝ) :=
    negativeBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0
  have hnext :
      nextRegion = connectedComponentIn (currentRegion ∩ nonzeroLocus) x0 := by
    rfl
  have hx0_negΦ : dialEval Φ x0 < 0 := by
    simpa [Φ, current] using hx0_neg
  have hx0_nonzero : dialEval Φ x0 ≠ 0 := ne_of_lt hx0_negΦ
  have hx0_open : x0 ∈ currentRegion ∩ nonzeroLocus := ⟨hx0_current, hx0_nonzero⟩
  have hcurrent_layer : 2 ≤ current.layer := by
    have hmem : current ∈ deeperHeadOrder (m + 1) k :=
      List.getElem_mem hn
    exact (mem_deeperHeadOrder_iff.mp hmem).1
  have hlambda_current :
      (dialFormalData r θ head).Lambda current
          (setLabel labels current TrichotomyLabel.zero) =
        (dialFormalData r θ head).Lambda current labels :=
    dialFormalData_Lambda_setLabel_eq_of_layer_le r θ head labels TrichotomyLabel.zero
      hcurrent_layer le_rfl
  have hneg_on : ∀ x ∈ nextRegion, dialEval Φ x < 0 := by
    rw [hnext]
    apply negativeOn_of_preconnected_of_nonzero isPreconnected_connectedComponentIn
      (continuous_dialEval Φ)
    · intro x hx
      exact (connectedComponentIn_subset (currentRegion ∩ nonzeroLocus) x0 hx).2
    · exact ⟨x0, mem_connectedComponentIn hx0_open, hx0_negΦ⟩
  change LabelSignLink (dialPredicates (attentionMatrix θ 0) head)
    (dialFormalData r θ head) nextRegion
    (setLabel labels current TrichotomyLabel.zero) current
  unfold LabelSignLink
  rw [setLabel_self]
  change ∀ x ∈ nextRegion,
    dialEval
      ((dialFormalData r θ head).Lambda current
        (setLabel labels current TrichotomyLabel.zero)) x < 0
  rw [hlambda_current]
  exact hneg_on

/-- One-step result wrapper for the concrete negative branch component, with the
branch estimate supplied explicitly. -/
noncomputable def trichotomyStepResult_dial_negativeBranchComponent_getElem_of_estimate
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {baseRegion currentRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n : Nat}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    (hInv : ProcessingInvariantStatement (dialPredicates (attentionMatrix θ 0) head)
      (dialFormalData r θ head) baseRegion currentRegion
      (deeperHeadOrder (m + 1) k) n labels)
    {x0 : ProbePair d × ℝ}
    (hx0_current : x0 ∈ currentRegion)
    (hx0_neg :
      dialEval
        (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels) x0 < 0)
    (hdet : (attentionMatrix θ 0 head).det ≠ 0)
    (hestimate :
      (dialPredicates (attentionMatrix θ 0) head).Estimate
        (deeperHeadOrder (m + 1) k) (n + 1)
        (negativeBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0)
        (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) TrichotomyLabel.zero)) :
    TrichotomyStepResult (dialPredicates (attentionMatrix θ 0) head)
      (dialFormalData r θ head) baseRegion currentRegion
      (deeperHeadOrder (m + 1) k) n labels
      ((deeperHeadOrder (m + 1) k)[n]) :=
  let htop := negativeBranchComponent_getElem_topology
    (r := r) (θ := θ) (head := head) (hn := hn) hInv hx0_current hx0_neg hdet
  trichotomyStepResult_dial_setLabel_getElem_of_current_link
    (r := r) (θ := θ) (head := head) (hn := hn) TrichotomyStepBranch.nonzero
    TrichotomyLabel.zero hInv
    htop.2.2.2 htop.1 htop.2.1 htop.2.2.1
    hestimate
    (labelSignLink_dial_negativeBranchComponent_getElem
      (r := r) (θ := θ) (head := head) (hn := hn) hx0_current hx0_neg)

/-- Honest-estimate topology package for the concrete negative branch component. -/
theorem negativeBranchComponent_getElem_topology_withEstimate
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {baseRegion currentRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n : Nat}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    (hInv : ProcessingInvariantStatement (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) baseRegion currentRegion
      (deeperHeadOrder (m + 1) k) n labels)
    {x0 : ProbePair d × ℝ}
    (hx0_current : x0 ∈ currentRegion)
    (hx0_neg :
      dialEval
        (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels) x0 < 0)
    (hdet : (attentionMatrix θ 0 head).det ≠ 0) :
    (negativeBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0).Nonempty ∧
      IsPreconnected
        (negativeBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0) ∧
      RelativelyOpenIn
        (negativeBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0)
        (quadricPatchCylinder (attentionMatrix θ 0) head) ∧
      negativeBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0 ⊆
        currentRegion := by
  let Φ : QuadraticDialForm d :=
    phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels
  let nonzeroLocus : Set (ProbePair d × ℝ) := {x | dialEval Φ x ≠ 0}
  let nextRegion : Set (ProbePair d × ℝ) :=
    negativeBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0
  have hnext :
      nextRegion = connectedComponentIn (currentRegion ∩ nonzeroLocus) x0 := by
    rfl
  have hx0_nonzero : dialEval Φ x0 ≠ 0 := ne_of_lt (by
    simpa [Φ] using hx0_neg)
  have hx0_open : x0 ∈ currentRegion ∩ nonzeroLocus := ⟨hx0_current, hx0_nonzero⟩
  have hsub : nextRegion ⊆ currentRegion := by
    intro x hx
    rw [hnext] at hx
    exact (connectedComponentIn_subset (currentRegion ∩ nonzeroLocus) x0 hx).1
  have hnonempty : nextRegion.Nonempty := by
    rw [hnext]
    exact ⟨x0, mem_connectedComponentIn hx0_open⟩
  have hconnected : IsPreconnected nextRegion := by
    rw [hnext]
    exact isPreconnected_connectedComponentIn
  have hopen_current :
      RelativelyOpenIn (currentRegion ∩ nonzeroLocus)
        (quadricPatchCylinder (attentionMatrix θ 0) head) := by
    change RelativelyOpenIn (currentRegion ∩ {x | dialEval Φ x ≠ 0})
      (quadricPatchCylinder (attentionMatrix θ 0) head)
    exact hInv.region_relativelyOpen.inter_open (isOpen_dialEval_ne_zero Φ)
  have hrelopen :
      RelativelyOpenIn nextRegion (quadricPatchCylinder (attentionMatrix θ 0) head) := by
    rw [hnext]
    exact connectedComponentIn_relativelyOpenIn_quadricPatchCylinder
      (A := attentionMatrix θ 0) (h := head) hdet hopen_current hx0_open
  exact ⟨hnonempty, hconnected, hrelopen, hsub⟩

/-- Honest-estimate current-head sign link for the concrete negative branch component. -/
theorem labelSignLink_dialWithEstimate_negativeBranchComponent_getElem
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {currentRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n : Nat}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    {x0 : ProbePair d × ℝ}
    (hx0_current : x0 ∈ currentRegion)
    (hx0_neg :
      dialEval
        (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels) x0 < 0) :
    LabelSignLink (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head)
      (negativeBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0)
      (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) TrichotomyLabel.zero)
      ((deeperHeadOrder (m + 1) k)[n]) := by
  let current : DeeperHead := (deeperHeadOrder (m + 1) k)[n]
  let Φ : QuadraticDialForm d := phiHeadOfDeeperHead r θ head current labels
  let nonzeroLocus : Set (ProbePair d × ℝ) := {x | dialEval Φ x ≠ 0}
  let nextRegion : Set (ProbePair d × ℝ) :=
    negativeBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0
  have hnext :
      nextRegion = connectedComponentIn (currentRegion ∩ nonzeroLocus) x0 := by
    rfl
  have hx0_negΦ : dialEval Φ x0 < 0 := by
    simpa [Φ, current] using hx0_neg
  have hx0_nonzero : dialEval Φ x0 ≠ 0 := ne_of_lt hx0_negΦ
  have hx0_open : x0 ∈ currentRegion ∩ nonzeroLocus := ⟨hx0_current, hx0_nonzero⟩
  have hcurrent_layer : 2 ≤ current.layer := by
    have hmem : current ∈ deeperHeadOrder (m + 1) k :=
      List.getElem_mem hn
    exact (mem_deeperHeadOrder_iff.mp hmem).1
  have hlambda_current :
      (dialFormalData r θ head).Lambda current
          (setLabel labels current TrichotomyLabel.zero) =
        (dialFormalData r θ head).Lambda current labels :=
    dialFormalData_Lambda_setLabel_eq_of_layer_le r θ head labels TrichotomyLabel.zero
      hcurrent_layer le_rfl
  have hneg_on : ∀ x ∈ nextRegion, dialEval Φ x < 0 := by
    rw [hnext]
    apply negativeOn_of_preconnected_of_nonzero isPreconnected_connectedComponentIn
      (continuous_dialEval Φ)
    · intro x hx
      exact (connectedComponentIn_subset (currentRegion ∩ nonzeroLocus) x0 hx).2
    · exact ⟨x0, mem_connectedComponentIn hx0_open, hx0_negΦ⟩
  change LabelSignLink (dialPredicatesWithEstimate r θ head)
    (dialFormalData r θ head) nextRegion
    (setLabel labels current TrichotomyLabel.zero) current
  unfold LabelSignLink
  rw [setLabel_self]
  change ∀ x ∈ nextRegion,
    dialEval
      ((dialFormalData r θ head).Lambda current
        (setLabel labels current TrichotomyLabel.zero)) x < 0
  rw [hlambda_current]
  exact hneg_on

/-- One-step result wrapper for the concrete negative branch component using the
honest estimate predicate, with the branch estimate supplied explicitly. -/
noncomputable def trichotomyStepResult_dialWithEstimate_negativeBranchComponent_getElem_of_estimate
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {baseRegion currentRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n : Nat}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    (hInv : ProcessingInvariantStatement (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) baseRegion currentRegion
      (deeperHeadOrder (m + 1) k) n labels)
    {x0 : ProbePair d × ℝ}
    (hx0_current : x0 ∈ currentRegion)
    (hx0_neg :
      dialEval
        (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels) x0 < 0)
    (hdet : (attentionMatrix θ 0 head).det ≠ 0)
    (hestimate :
      (dialPredicatesWithEstimate r θ head).Estimate
        (deeperHeadOrder (m + 1) k) (n + 1)
        (negativeBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0)
        (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) TrichotomyLabel.zero)) :
    TrichotomyStepResult (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) baseRegion currentRegion
      (deeperHeadOrder (m + 1) k) n labels
      ((deeperHeadOrder (m + 1) k)[n]) :=
  let htop := negativeBranchComponent_getElem_topology_withEstimate
    (r := r) (θ := θ) (head := head) (hn := hn) hInv hx0_current hx0_neg hdet
  trichotomyStepResult_dialWithEstimate_setLabel_getElem_of_current_link
    (r := r) (θ := θ) (head := head) (hn := hn) TrichotomyStepBranch.nonzero
    TrichotomyLabel.zero hInv
    htop.2.2.2 htop.1 htop.2.1 htop.2.2.1
    hestimate
    (labelSignLink_dialWithEstimate_negativeBranchComponent_getElem
      (r := r) (θ := θ) (head := head) (hn := hn) hx0_current hx0_neg)

/-- One-step result wrapper for the concrete negative branch component. -/
noncomputable def trichotomyStepResult_dial_negativeBranchComponent_getElem
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {baseRegion currentRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n : Nat}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    (hInv : ProcessingInvariantStatement (dialPredicates (attentionMatrix θ 0) head)
      (dialFormalData r θ head) baseRegion currentRegion
      (deeperHeadOrder (m + 1) k) n labels)
    {x0 : ProbePair d × ℝ}
    (hx0_current : x0 ∈ currentRegion)
    (hx0_neg :
      dialEval
        (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels) x0 < 0)
    (hdet : (attentionMatrix θ 0 head).det ≠ 0) :
    TrichotomyStepResult (dialPredicates (attentionMatrix θ 0) head)
      (dialFormalData r θ head) baseRegion currentRegion
      (deeperHeadOrder (m + 1) k) n labels
      ((deeperHeadOrder (m + 1) k)[n]) :=
  trichotomyStepResult_dial_negativeBranchComponent_getElem_of_estimate
    (r := r) (θ := θ) (head := head) (baseRegion := baseRegion)
    (currentRegion := currentRegion) (labels := labels) (hn := hn)
    hInv hx0_current hx0_neg hdet
    trivial

/-- Current-head `alpha` link when the faithful current dial form is already
known to be the zero polynomial.  The only bookkeeping is transporting `Phi`
across the same-head label update. -/
theorem labelSignLink_dial_alpha_getElem_of_zeroDialForm
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {currentRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n : Nat}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    (hz :
      zeroDialForm
        (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels)) :
    LabelSignLink (dialPredicates (attentionMatrix θ 0) head)
      (dialFormalData r θ head) currentRegion
      (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) TrichotomyLabel.alpha)
      ((deeperHeadOrder (m + 1) k)[n]) := by
  let current : DeeperHead := (deeperHeadOrder (m + 1) k)[n]
  have hcurrent_layer : 2 ≤ current.layer := by
    have hmem : current ∈ deeperHeadOrder (m + 1) k :=
      List.getElem_mem hn
    exact (mem_deeperHeadOrder_iff.mp hmem).1
  have hphi_current :
      (dialFormalData r θ head).Phi current
          (setLabel labels current TrichotomyLabel.alpha) =
        (dialFormalData r θ head).Phi current labels :=
    dialFormalData_Phi_setLabel_eq_of_layer_le r θ head labels TrichotomyLabel.alpha
      hcurrent_layer le_rfl
  change LabelSignLink (dialPredicates (attentionMatrix θ 0) head)
    (dialFormalData r θ head) currentRegion
    (setLabel labels current TrichotomyLabel.alpha) current
  unfold LabelSignLink
  rw [setLabel_self]
  change zeroDialForm
    ((dialFormalData r θ head).Phi current
      (setLabel labels current TrichotomyLabel.alpha))
  rw [hphi_current]
  simpa [current] using hz

/-- Current-head `alpha` link from the zero/vanishing branch, using the concrete
zero-branch rigidity instance to obtain the zero dial form. -/
theorem labelSignLink_dial_alpha_getElem_of_vanishes
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {currentRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n : Nat}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    (hd : 2 ≤ d) (hreg : Regularity r θ)
    (htop :
      SignRegionTopologyStatement (attentionMatrix θ 0) (valueMatrix θ 0) head
        currentRegion)
    (hvanish :
      ∀ x ∈ currentRegion,
        dialEval
          (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels) x = 0) :
    LabelSignLink (dialPredicates (attentionMatrix θ 0) head)
      (dialFormalData r θ head) currentRegion
      (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) TrichotomyLabel.alpha)
      ((deeperHeadOrder (m + 1) k)[n]) := by
  have hz :
      zeroDialForm
        (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels) := by
    have hrig :=
      lem_zero_branch_rigidity_S_instance
        (r := r) θ head currentRegion labels ((deeperHeadOrder (m + 1) k)[n])
        hd hreg htop
    exact hrig (by simpa [dialPredicates, dialFormalData] using hvanish)
  exact labelSignLink_dial_alpha_getElem_of_zeroDialForm
    (r := r) (θ := θ) (head := head) (currentRegion := currentRegion)
    (labels := labels) (hn := hn) hz

/-- One-step result wrapper for the zero/alpha branch when the current zero dial
form and the branch estimate are supplied.  The estimate input is deliberately
explicit: this helper packages the branch, but does not prove the analytic
zero-branch error. -/
noncomputable def trichotomyStepResult_dial_alpha_getElem_of_zeroDialForm
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {baseRegion currentRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n : Nat}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    (hInv : ProcessingInvariantStatement (dialPredicates (attentionMatrix θ 0) head)
      (dialFormalData r θ head) baseRegion currentRegion
      (deeperHeadOrder (m + 1) k) n labels)
    (hz :
      zeroDialForm
        (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels))
    (hestimate :
      (dialPredicates (attentionMatrix θ 0) head).Estimate
        (deeperHeadOrder (m + 1) k) (n + 1) currentRegion
        (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) TrichotomyLabel.alpha)) :
    TrichotomyStepResult (dialPredicates (attentionMatrix θ 0) head)
      (dialFormalData r θ head) baseRegion currentRegion
      (deeperHeadOrder (m + 1) k) n labels
      ((deeperHeadOrder (m + 1) k)[n]) :=
  trichotomyStepResult_dial_setLabel_getElem_of_current_link
    (r := r) (θ := θ) (head := head) (currentRegion := currentRegion)
    (nextRegion := currentRegion) (labels := labels) (hn := hn)
    TrichotomyStepBranch.zero TrichotomyLabel.alpha hInv
    (fun _ hx => hx) hInv.region_nonempty hInv.region_connected hInv.region_relativelyOpen
    hestimate
    (labelSignLink_dial_alpha_getElem_of_zeroDialForm
      (r := r) (θ := θ) (head := head) (currentRegion := currentRegion)
      (labels := labels) (hn := hn) hz)

/-- One-step result wrapper for the zero/alpha branch from a vanishing current
dial evaluation on the current region, plus the explicit branch estimate. -/
noncomputable def trichotomyStepResult_dial_alpha_getElem_of_vanishes
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {baseRegion currentRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n : Nat}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    (hInv : ProcessingInvariantStatement (dialPredicates (attentionMatrix θ 0) head)
      (dialFormalData r θ head) baseRegion currentRegion
      (deeperHeadOrder (m + 1) k) n labels)
    (hd : 2 ≤ d) (hreg : Regularity r θ)
    (htop :
      SignRegionTopologyStatement (attentionMatrix θ 0) (valueMatrix θ 0) head
        currentRegion)
    (hvanish :
      ∀ x ∈ currentRegion,
        dialEval
          (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels) x = 0)
    (hestimate :
      (dialPredicates (attentionMatrix θ 0) head).Estimate
        (deeperHeadOrder (m + 1) k) (n + 1) currentRegion
        (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) TrichotomyLabel.alpha)) :
    TrichotomyStepResult (dialPredicates (attentionMatrix θ 0) head)
      (dialFormalData r θ head) baseRegion currentRegion
      (deeperHeadOrder (m + 1) k) n labels
      ((deeperHeadOrder (m + 1) k)[n]) :=
  trichotomyStepResult_dial_alpha_getElem_of_zeroDialForm
    (r := r) (θ := θ) (head := head) (baseRegion := baseRegion)
    (currentRegion := currentRegion) (labels := labels) (hn := hn) hInv
    (by
      have hrig :=
        lem_zero_branch_rigidity_S_instance
          (r := r) θ head currentRegion labels ((deeperHeadOrder (m + 1) k)[n])
          hd hreg htop
      exact hrig (by simpa [dialPredicates, dialFormalData] using hvanish))
    hestimate

/-- Honest-estimate current-head `alpha` link when the faithful current dial form
is already known to be the zero polynomial. -/
theorem labelSignLink_dialWithEstimate_alpha_getElem_of_zeroDialForm
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {currentRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n : Nat}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    (hz :
      zeroDialForm
        (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels)) :
    LabelSignLink (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) currentRegion
      (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) TrichotomyLabel.alpha)
      ((deeperHeadOrder (m + 1) k)[n]) := by
  let current : DeeperHead := (deeperHeadOrder (m + 1) k)[n]
  have hcurrent_layer : 2 ≤ current.layer := by
    have hmem : current ∈ deeperHeadOrder (m + 1) k :=
      List.getElem_mem hn
    exact (mem_deeperHeadOrder_iff.mp hmem).1
  have hphi_current :
      (dialFormalData r θ head).Phi current
          (setLabel labels current TrichotomyLabel.alpha) =
        (dialFormalData r θ head).Phi current labels :=
    dialFormalData_Phi_setLabel_eq_of_layer_le r θ head labels TrichotomyLabel.alpha
      hcurrent_layer le_rfl
  change LabelSignLink (dialPredicatesWithEstimate r θ head)
    (dialFormalData r θ head) currentRegion
    (setLabel labels current TrichotomyLabel.alpha) current
  unfold LabelSignLink
  rw [setLabel_self]
  change zeroDialForm
    ((dialFormalData r θ head).Phi current
      (setLabel labels current TrichotomyLabel.alpha))
  rw [hphi_current]
  simpa [current] using hz

/-- Honest-estimate current-head `alpha` link from the zero/vanishing branch,
using the concrete zero-branch rigidity instance to obtain the zero dial form. -/
theorem labelSignLink_dialWithEstimate_alpha_getElem_of_vanishes
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {currentRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n : Nat}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    (hd : 2 ≤ d) (hreg : Regularity r θ)
    (htop :
      SignRegionTopologyStatement (attentionMatrix θ 0) (valueMatrix θ 0) head
        currentRegion)
    (hvanish :
      ∀ x ∈ currentRegion,
        dialEval
          (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels) x = 0) :
    LabelSignLink (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) currentRegion
      (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) TrichotomyLabel.alpha)
      ((deeperHeadOrder (m + 1) k)[n]) := by
  have hz :
      zeroDialForm
        (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels) := by
    have hrig :=
      lem_zero_branch_rigidity_S_instance
        (r := r) θ head currentRegion labels ((deeperHeadOrder (m + 1) k)[n])
        hd hreg htop
    exact hrig (by simpa [dialPredicates, dialFormalData] using hvanish)
  exact labelSignLink_dialWithEstimate_alpha_getElem_of_zeroDialForm
    (r := r) (θ := θ) (head := head) (currentRegion := currentRegion)
    (labels := labels) (hn := hn) hz

/-- Honest-estimate one-step result wrapper for the zero/alpha branch when the
current zero dial form and the branch estimate are supplied explicitly. -/
noncomputable def trichotomyStepResult_dialWithEstimate_alpha_getElem_of_zeroDialForm
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {baseRegion currentRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n : Nat}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    (hInv : ProcessingInvariantStatement (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) baseRegion currentRegion
      (deeperHeadOrder (m + 1) k) n labels)
    (hz :
      zeroDialForm
        (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels))
    (hestimate :
      (dialPredicatesWithEstimate r θ head).Estimate
        (deeperHeadOrder (m + 1) k) (n + 1) currentRegion
        (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) TrichotomyLabel.alpha)) :
    TrichotomyStepResult (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) baseRegion currentRegion
      (deeperHeadOrder (m + 1) k) n labels
      ((deeperHeadOrder (m + 1) k)[n]) :=
  trichotomyStepResult_dialWithEstimate_setLabel_getElem_of_current_link
    (r := r) (θ := θ) (head := head) (currentRegion := currentRegion)
    (nextRegion := currentRegion) (labels := labels) (hn := hn)
    TrichotomyStepBranch.zero TrichotomyLabel.alpha hInv
    (fun _ hx => hx) hInv.region_nonempty hInv.region_connected hInv.region_relativelyOpen
    hestimate
    (labelSignLink_dialWithEstimate_alpha_getElem_of_zeroDialForm
      (r := r) (θ := θ) (head := head) (currentRegion := currentRegion)
      (labels := labels) (hn := hn) hz)

/-- Honest-estimate one-step result wrapper for the zero/alpha branch from a
vanishing current dial evaluation, plus the explicit branch estimate. -/
noncomputable def trichotomyStepResult_dialWithEstimate_alpha_getElem_of_vanishes
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {baseRegion currentRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n : Nat}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    (hInv : ProcessingInvariantStatement (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) baseRegion currentRegion
      (deeperHeadOrder (m + 1) k) n labels)
    (hd : 2 ≤ d) (hreg : Regularity r θ)
    (htop :
      SignRegionTopologyStatement (attentionMatrix θ 0) (valueMatrix θ 0) head
        currentRegion)
    (hvanish :
      ∀ x ∈ currentRegion,
        dialEval
          (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels) x = 0)
    (hestimate :
      (dialPredicatesWithEstimate r θ head).Estimate
        (deeperHeadOrder (m + 1) k) (n + 1) currentRegion
        (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) TrichotomyLabel.alpha)) :
    TrichotomyStepResult (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) baseRegion currentRegion
      (deeperHeadOrder (m + 1) k) n labels
      ((deeperHeadOrder (m + 1) k)[n]) :=
  trichotomyStepResult_dialWithEstimate_alpha_getElem_of_zeroDialForm
    (r := r) (θ := θ) (head := head) (baseRegion := baseRegion)
    (currentRegion := currentRegion) (labels := labels) (hn := hn) hInv
    (by
      have hrig :=
        lem_zero_branch_rigidity_S_instance
          (r := r) θ head currentRegion labels ((deeperHeadOrder (m + 1) k)[n])
          hd hreg htop
      exact hrig (by simpa [dialPredicates, dialFormalData] using hvanish))
    hestimate

/-- Additive `_of_facts` form of
`trichotomyStepResult_dialWithEstimate_alpha_getElem_of_vanishes`: the same
zero/alpha wrapper, driven by a `FirstHeadRigidityFacts θ head` bundle and a
sign-region topology over a **free** value-matrix parameter `V'`. -/
noncomputable def trichotomyStepResult_dialWithEstimate_alpha_getElem_of_vanishes_of_facts
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {V' : Fin k → Matrix (Fin d) (Fin d) ℝ}
    {baseRegion currentRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n : Nat}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    (hInv : ProcessingInvariantStatement (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) baseRegion currentRegion
      (deeperHeadOrder (m + 1) k) n labels)
    (hd : 2 ≤ d) (hfacts : FirstHeadRigidityFacts θ head)
    (htop :
      SignRegionTopologyStatement (attentionMatrix θ 0) V' head
        currentRegion)
    (hvanish :
      ∀ x ∈ currentRegion,
        dialEval
          (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels) x = 0)
    (hestimate :
      (dialPredicatesWithEstimate r θ head).Estimate
        (deeperHeadOrder (m + 1) k) (n + 1) currentRegion
        (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) TrichotomyLabel.alpha)) :
    TrichotomyStepResult (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) baseRegion currentRegion
      (deeperHeadOrder (m + 1) k) n labels
      ((deeperHeadOrder (m + 1) k)[n]) :=
  trichotomyStepResult_dialWithEstimate_alpha_getElem_of_zeroDialForm
    (r := r) (θ := θ) (head := head) (baseRegion := baseRegion)
    (currentRegion := currentRegion) (labels := labels) (hn := hn) hInv
    (by
      have hrig :=
        lem_zero_branch_rigidity_S_instance_of_facts
          (r := r) θ head currentRegion labels ((deeperHeadOrder (m + 1) k)[n])
          hd hfacts htop
      exact hrig (by simpa [dialPredicates, dialFormalData] using hvanish))
    hestimate

/-- Concrete one-step trichotomy assembly for the current `deeperHeadOrder`
entry.  The theorem performs only the finite sign/zero case split.  Analytic
branch estimates and the zero-branch rigidity/topology inputs remain explicit
hypotheses. -/
theorem lem_trichotomy_step_S_dial_getElem_of_branch_estimates
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {baseRegion currentRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n : Nat}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    (hdet : (attentionMatrix θ 0 head).det ≠ 0)
    (hd : 2 ≤ d) (hreg : Regularity r θ)
    (htop :
      SignRegionTopologyStatement (attentionMatrix θ 0) (valueMatrix θ 0) head
        currentRegion)
    (hestimate_pos : ∀ (x0 : ProbePair d × ℝ),
      x0 ∈ currentRegion →
      0 < dialEval
        (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels) x0 →
      (dialPredicates (attentionMatrix θ 0) head).Estimate
        (deeperHeadOrder (m + 1) k) (n + 1)
        (positiveBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0)
        (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) TrichotomyLabel.one))
    (hestimate_neg : ∀ (x0 : ProbePair d × ℝ),
      x0 ∈ currentRegion →
      dialEval
        (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels) x0 < 0 →
      (dialPredicates (attentionMatrix θ 0) head).Estimate
        (deeperHeadOrder (m + 1) k) (n + 1)
        (negativeBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0)
        (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) TrichotomyLabel.zero))
    (hestimate_alpha :
      (∀ x ∈ currentRegion,
        dialEval
          (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels) x = 0) →
      (dialPredicates (attentionMatrix θ 0) head).Estimate
        (deeperHeadOrder (m + 1) k) (n + 1) currentRegion
        (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) TrichotomyLabel.alpha)) :
    lem_trichotomy_step_S (dialPredicates (attentionMatrix θ 0) head)
      (dialFormalData r θ head) baseRegion currentRegion
      (deeperHeadOrder (m + 1) k) n labels
      ((deeperHeadOrder (m + 1) k)[n]) := by
  intro hInv
  classical
  by_cases hpos :
      ∃ x0 : ProbePair d × ℝ,
        x0 ∈ currentRegion ∧
          0 < dialEval
            (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels) x0
  · rcases hpos with ⟨x0, hx0_current, hx0_pos⟩
    exact
      ⟨trichotomyStepResult_dial_positiveBranchComponent_getElem
          (r := r) (θ := θ) (head := head) (baseRegion := baseRegion)
          (currentRegion := currentRegion) (labels := labels) (hn := hn)
          hInv hx0_current hx0_pos hdet
          (hestimate_pos x0 hx0_current hx0_pos),
        trivial⟩
  · by_cases hneg :
        ∃ x0 : ProbePair d × ℝ,
          x0 ∈ currentRegion ∧
            dialEval
              (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels)
              x0 < 0
    · rcases hneg with ⟨x0, hx0_current, hx0_neg⟩
      exact
        ⟨trichotomyStepResult_dial_negativeBranchComponent_getElem_of_estimate
            (r := r) (θ := θ) (head := head) (baseRegion := baseRegion)
            (currentRegion := currentRegion) (labels := labels) (hn := hn)
            hInv hx0_current hx0_neg hdet
            (hestimate_neg x0 hx0_current hx0_neg),
          trivial⟩
    · have hvanish :
          ∀ x ∈ currentRegion,
            dialEval
              (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels)
              x = 0 := by
        intro x hx
        rcases lt_trichotomy
            (dialEval
              (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels)
              x) 0 with hlt | heq | hgt
        · exact False.elim (hneg ⟨x, hx, hlt⟩)
        · exact heq
        · exact False.elim (hpos ⟨x, hx, hgt⟩)
      exact
        ⟨trichotomyStepResult_dial_alpha_getElem_of_vanishes
            (r := r) (θ := θ) (head := head) (baseRegion := baseRegion)
            (currentRegion := currentRegion) (labels := labels) (hn := hn)
            hInv hd hreg htop hvanish (hestimate_alpha hvanish),
          trivial⟩

/-- Honest-estimate one-step trichotomy assembly for the current
`deeperHeadOrder` entry.  The theorem performs only the finite sign/zero case
split; branch estimates remain explicit hypotheses. -/
theorem lem_trichotomy_step_S_dialWithEstimate_getElem_of_branch_estimates
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {baseRegion currentRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n : Nat}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    (hdet : (attentionMatrix θ 0 head).det ≠ 0)
    (hd : 2 ≤ d) (hreg : Regularity r θ)
    (htop :
      SignRegionTopologyStatement (attentionMatrix θ 0) (valueMatrix θ 0) head
        currentRegion)
    (hestimate_pos : ∀ (x0 : ProbePair d × ℝ),
      x0 ∈ currentRegion →
      0 < dialEval
        (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels) x0 →
      (dialPredicatesWithEstimate r θ head).Estimate
        (deeperHeadOrder (m + 1) k) (n + 1)
        (positiveBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0)
        (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) TrichotomyLabel.one))
    (hestimate_neg : ∀ (x0 : ProbePair d × ℝ),
      x0 ∈ currentRegion →
      dialEval
        (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels) x0 < 0 →
      (dialPredicatesWithEstimate r θ head).Estimate
        (deeperHeadOrder (m + 1) k) (n + 1)
        (negativeBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0)
        (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) TrichotomyLabel.zero))
    (hestimate_alpha :
      (∀ x ∈ currentRegion,
        dialEval
          (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels) x = 0) →
      (dialPredicatesWithEstimate r θ head).Estimate
        (deeperHeadOrder (m + 1) k) (n + 1) currentRegion
        (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) TrichotomyLabel.alpha)) :
    lem_trichotomy_step_S (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) baseRegion currentRegion
      (deeperHeadOrder (m + 1) k) n labels
      ((deeperHeadOrder (m + 1) k)[n]) := by
  intro hInv
  classical
  by_cases hpos :
      ∃ x0 : ProbePair d × ℝ,
        x0 ∈ currentRegion ∧
          0 < dialEval
            (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels) x0
  · rcases hpos with ⟨x0, hx0_current, hx0_pos⟩
    exact
      ⟨trichotomyStepResult_dialWithEstimate_positiveBranchComponent_getElem
          (r := r) (θ := θ) (head := head) (baseRegion := baseRegion)
          (currentRegion := currentRegion) (labels := labels) (hn := hn)
          hInv hx0_current hx0_pos hdet
          (hestimate_pos x0 hx0_current hx0_pos),
        trivial⟩
  · by_cases hneg :
        ∃ x0 : ProbePair d × ℝ,
          x0 ∈ currentRegion ∧
            dialEval
              (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels)
              x0 < 0
    · rcases hneg with ⟨x0, hx0_current, hx0_neg⟩
      exact
        ⟨trichotomyStepResult_dialWithEstimate_negativeBranchComponent_getElem_of_estimate
            (r := r) (θ := θ) (head := head) (baseRegion := baseRegion)
            (currentRegion := currentRegion) (labels := labels) (hn := hn)
            hInv hx0_current hx0_neg hdet
            (hestimate_neg x0 hx0_current hx0_neg),
          trivial⟩
    · have hvanish :
          ∀ x ∈ currentRegion,
            dialEval
              (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels)
              x = 0 := by
        intro x hx
        rcases lt_trichotomy
            (dialEval
              (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels)
              x) 0 with hlt | heq | hgt
        · exact False.elim (hneg ⟨x, hx, hlt⟩)
        · exact heq
        · exact False.elim (hpos ⟨x, hx, hgt⟩)
      exact
        ⟨trichotomyStepResult_dialWithEstimate_alpha_getElem_of_vanishes
            (r := r) (θ := θ) (head := head) (baseRegion := baseRegion)
            (currentRegion := currentRegion) (labels := labels) (hn := hn)
            hInv hd hreg htop hvanish (hestimate_alpha hvanish),
          trivial⟩

/-- Additive `_of_facts` form of
`lem_trichotomy_step_S_dialWithEstimate_getElem_of_branch_estimates`: the same
finite sign/zero case split, driven by a `FirstHeadRigidityFacts θ head` bundle
and a sign-region topology over a **free** value-matrix parameter `V'`. -/
theorem lem_trichotomy_step_S_dialWithEstimate_getElem_of_branch_estimates_of_facts
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {V' : Fin k → Matrix (Fin d) (Fin d) ℝ}
    {baseRegion currentRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n : Nat}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    (hdet : (attentionMatrix θ 0 head).det ≠ 0)
    (hd : 2 ≤ d) (hfacts : FirstHeadRigidityFacts θ head)
    (htop :
      SignRegionTopologyStatement (attentionMatrix θ 0) V' head
        currentRegion)
    (hestimate_pos : ∀ (x0 : ProbePair d × ℝ),
      x0 ∈ currentRegion →
      0 < dialEval
        (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels) x0 →
      (dialPredicatesWithEstimate r θ head).Estimate
        (deeperHeadOrder (m + 1) k) (n + 1)
        (positiveBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0)
        (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) TrichotomyLabel.one))
    (hestimate_neg : ∀ (x0 : ProbePair d × ℝ),
      x0 ∈ currentRegion →
      dialEval
        (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels) x0 < 0 →
      (dialPredicatesWithEstimate r θ head).Estimate
        (deeperHeadOrder (m + 1) k) (n + 1)
        (negativeBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0)
        (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) TrichotomyLabel.zero))
    (hestimate_alpha :
      (∀ x ∈ currentRegion,
        dialEval
          (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels) x = 0) →
      (dialPredicatesWithEstimate r θ head).Estimate
        (deeperHeadOrder (m + 1) k) (n + 1) currentRegion
        (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) TrichotomyLabel.alpha)) :
    lem_trichotomy_step_S (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) baseRegion currentRegion
      (deeperHeadOrder (m + 1) k) n labels
      ((deeperHeadOrder (m + 1) k)[n]) := by
  intro hInv
  classical
  by_cases hpos :
      ∃ x0 : ProbePair d × ℝ,
        x0 ∈ currentRegion ∧
          0 < dialEval
            (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels) x0
  · rcases hpos with ⟨x0, hx0_current, hx0_pos⟩
    exact
      ⟨trichotomyStepResult_dialWithEstimate_positiveBranchComponent_getElem
          (r := r) (θ := θ) (head := head) (baseRegion := baseRegion)
          (currentRegion := currentRegion) (labels := labels) (hn := hn)
          hInv hx0_current hx0_pos hdet
          (hestimate_pos x0 hx0_current hx0_pos),
        trivial⟩
  · by_cases hneg :
        ∃ x0 : ProbePair d × ℝ,
          x0 ∈ currentRegion ∧
            dialEval
              (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels)
              x0 < 0
    · rcases hneg with ⟨x0, hx0_current, hx0_neg⟩
      exact
        ⟨trichotomyStepResult_dialWithEstimate_negativeBranchComponent_getElem_of_estimate
            (r := r) (θ := θ) (head := head) (baseRegion := baseRegion)
            (currentRegion := currentRegion) (labels := labels) (hn := hn)
            hInv hx0_current hx0_neg hdet
            (hestimate_neg x0 hx0_current hx0_neg),
          trivial⟩
    · have hvanish :
          ∀ x ∈ currentRegion,
            dialEval
              (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels)
              x = 0 := by
        intro x hx
        rcases lt_trichotomy
            (dialEval
              (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels)
              x) 0 with hlt | heq | hgt
        · exact False.elim (hneg ⟨x, hx, hlt⟩)
        · exact heq
        · exact False.elim (hpos ⟨x, hx, hgt⟩)
      exact
        ⟨trichotomyStepResult_dialWithEstimate_alpha_getElem_of_vanishes_of_facts
            (r := r) (θ := θ) (head := head) (baseRegion := baseRegion)
            (currentRegion := currentRegion) (labels := labels) (hn := hn)
            hInv hd hfacts htop hvanish (hestimate_alpha hvanish),
          trivial⟩

/-- A final concrete trichotomy label `1` gives positivity of the corresponding dial
polynomial on the final region. -/
theorem TrichotomyResult.dialEval_pos_of_label_one {m k d r : Nat}
    {θ : Params (m + 1) k d} {h : Fin k}
    {baseRegion : Set (ProbePair d × ℝ)} {order : List DeeperHead}
    (R : TrichotomyResult (dialPredicates (attentionMatrix θ 0) h)
      (dialFormalData r θ h) baseRegion order)
    {dh : DeeperHead} (hdh : dh ∈ order) {x : ProbePair d × ℝ}
    (hx : x ∈ R.Ustar) (hlabel : R.labels dh = TrichotomyLabel.one) :
    0 < dialEval (phiHeadOfDeeperHead r θ h dh R.labels) x := by
  have hlink := R.label_sign_link dh hdh
  unfold LabelSignLink at hlink
  rw [hlabel] at hlink
  simpa [dialPredicates, dialFormalData] using hlink x hx

/-- A final concrete trichotomy label `0` gives negativity of the corresponding dial
polynomial on the final region. -/
theorem TrichotomyResult.dialEval_neg_of_label_zero {m k d r : Nat}
    {θ : Params (m + 1) k d} {h : Fin k}
    {baseRegion : Set (ProbePair d × ℝ)} {order : List DeeperHead}
    (R : TrichotomyResult (dialPredicates (attentionMatrix θ 0) h)
      (dialFormalData r θ h) baseRegion order)
    {dh : DeeperHead} (hdh : dh ∈ order) {x : ProbePair d × ℝ}
    (hx : x ∈ R.Ustar) (hlabel : R.labels dh = TrichotomyLabel.zero) :
    dialEval (phiHeadOfDeeperHead r θ h dh R.labels) x < 0 := by
  have hlink := R.label_sign_link dh hdh
  unfold LabelSignLink at hlink
  rw [hlabel] at hlink
  simpa [dialPredicates, dialFormalData] using hlink x hx

/-- A final concrete trichotomy label `alpha` gives the zero-polynomial dial form. -/
theorem TrichotomyResult.zeroDialForm_of_label_alpha {m k d r : Nat}
    {θ : Params (m + 1) k d} {h : Fin k}
    {baseRegion : Set (ProbePair d × ℝ)} {order : List DeeperHead}
    (R : TrichotomyResult (dialPredicates (attentionMatrix θ 0) h)
      (dialFormalData r θ h) baseRegion order)
    {dh : DeeperHead} (hdh : dh ∈ order)
    (hlabel : R.labels dh = TrichotomyLabel.alpha) :
    zeroDialForm (phiHeadOfDeeperHead r θ h dh R.labels) := by
  have hlink := R.label_sign_link dh hdh
  unfold LabelSignLink at hlink
  rw [hlabel] at hlink
  simpa [dialPredicates, dialFormalData] using hlink

/-- Concrete pointwise case split exported from a final trichotomy result. -/
theorem TrichotomyResult.dialEval_label_cases {m k d r : Nat}
    {θ : Params (m + 1) k d} {h : Fin k}
    {baseRegion : Set (ProbePair d × ℝ)} {order : List DeeperHead}
    (R : TrichotomyResult (dialPredicates (attentionMatrix θ 0) h)
      (dialFormalData r θ h) baseRegion order)
    {dh : DeeperHead} (hdh : dh ∈ order) {x : ProbePair d × ℝ}
    (hx : x ∈ R.Ustar) :
    (R.labels dh = TrichotomyLabel.one ∧
        0 < dialEval (phiHeadOfDeeperHead r θ h dh R.labels) x) ∨
      (R.labels dh = TrichotomyLabel.zero ∧
        dialEval (phiHeadOfDeeperHead r θ h dh R.labels) x < 0) ∨
      (R.labels dh = TrichotomyLabel.alpha ∧
        zeroDialForm (phiHeadOfDeeperHead r θ h dh R.labels)) := by
  cases hlabel : R.labels dh with
  | one =>
      left
      exact ⟨rfl, R.dialEval_pos_of_label_one hdh hx hlabel⟩
  | zero =>
      right
      left
      exact ⟨rfl, R.dialEval_neg_of_label_zero hdh hx hlabel⟩
  | alpha =>
      right
      right
      exact ⟨rfl, R.zeroDialForm_of_label_alpha hdh hlabel⟩

/-- A processed honest-estimate invariant label `1` gives positivity of the
corresponding dial polynomial on the current region. -/
theorem ProcessingInvariantStatement.dialEval_pos_of_label_one_withEstimate
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {baseRegion currentRegion : Set (ProbePair d × ℝ)} {order : List DeeperHead}
    {labels : DeeperHead → TrichotomyLabel} {idx : Nat}
    (hInv : ProcessingInvariantStatement (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) baseRegion currentRegion order idx labels)
    {dh : DeeperHead} (hdh : dh ∈ processedPrefix order idx)
    {x : ProbePair d × ℝ} (hx : x ∈ currentRegion)
    (hlabel : labels dh = TrichotomyLabel.one) :
    0 < dialEval (phiHeadOfDeeperHead r θ head dh labels) x := by
  have hlink := hInv.label_sign_link dh hdh
  unfold LabelSignLink at hlink
  rw [hlabel] at hlink
  simpa [dialPredicatesWithEstimate, dialFormalData] using hlink x hx

/-- A processed honest-estimate invariant label `0` gives negativity of the
corresponding dial polynomial on the current region. -/
theorem ProcessingInvariantStatement.dialEval_neg_of_label_zero_withEstimate
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {baseRegion currentRegion : Set (ProbePair d × ℝ)} {order : List DeeperHead}
    {labels : DeeperHead → TrichotomyLabel} {idx : Nat}
    (hInv : ProcessingInvariantStatement (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) baseRegion currentRegion order idx labels)
    {dh : DeeperHead} (hdh : dh ∈ processedPrefix order idx)
    {x : ProbePair d × ℝ} (hx : x ∈ currentRegion)
    (hlabel : labels dh = TrichotomyLabel.zero) :
    dialEval (phiHeadOfDeeperHead r θ head dh labels) x < 0 := by
  have hlink := hInv.label_sign_link dh hdh
  unfold LabelSignLink at hlink
  rw [hlabel] at hlink
  simpa [dialPredicatesWithEstimate, dialFormalData] using hlink x hx

/-- A processed honest-estimate invariant label `alpha` gives the zero-polynomial
dial form. -/
theorem ProcessingInvariantStatement.zeroDialForm_of_label_alpha_withEstimate
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {baseRegion currentRegion : Set (ProbePair d × ℝ)} {order : List DeeperHead}
    {labels : DeeperHead → TrichotomyLabel} {idx : Nat}
    (hInv : ProcessingInvariantStatement (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) baseRegion currentRegion order idx labels)
    {dh : DeeperHead} (hdh : dh ∈ processedPrefix order idx)
    (hlabel : labels dh = TrichotomyLabel.alpha) :
    zeroDialForm (phiHeadOfDeeperHead r θ head dh labels) := by
  have hlink := hInv.label_sign_link dh hdh
  unfold LabelSignLink at hlink
  rw [hlabel] at hlink
  simpa [dialPredicatesWithEstimate, dialFormalData] using hlink

/-- Concrete pointwise label case split exported from a processed
honest-estimate invariant. -/
theorem ProcessingInvariantStatement.dialEval_label_cases_withEstimate
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {baseRegion currentRegion : Set (ProbePair d × ℝ)} {order : List DeeperHead}
    {labels : DeeperHead → TrichotomyLabel} {idx : Nat}
    (hInv : ProcessingInvariantStatement (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) baseRegion currentRegion order idx labels)
    {dh : DeeperHead} (hdh : dh ∈ processedPrefix order idx)
    {x : ProbePair d × ℝ} (hx : x ∈ currentRegion) :
    (labels dh = TrichotomyLabel.one ∧
        0 < dialEval (phiHeadOfDeeperHead r θ head dh labels) x) ∨
      (labels dh = TrichotomyLabel.zero ∧
        dialEval (phiHeadOfDeeperHead r θ head dh labels) x < 0) ∨
      (labels dh = TrichotomyLabel.alpha ∧
        zeroDialForm (phiHeadOfDeeperHead r θ head dh labels)) := by
  cases hlabel : labels dh with
  | one =>
      left
      exact ⟨rfl, hInv.dialEval_pos_of_label_one_withEstimate hdh hx hlabel⟩
  | zero =>
      right
      left
      exact ⟨rfl, hInv.dialEval_neg_of_label_zero_withEstimate hdh hx hlabel⟩
  | alpha =>
      right
      right
      exact ⟨rfl, hInv.zeroDialForm_of_label_alpha_withEstimate hdh hlabel⟩

/-! ## L1/L2 — ζ-general per-point convergence and the α-branch gate limit

The analytic core the honest trichotomy `Estimate` consumes.  Along the θ-dial path the actual
probe recursion converges to the ζ-general frozen point `satZetaPoint`, provided each deeper
head's gate converges to its trichotomy label value.  The three label cases are exactly the
three branches of the K07B `LabelSignLink` (`Step2.Trichotomy`):

* label `1` (`PositiveOn`): the frozen deeper slope is positive, so the gate saturates to `1`
  via `expCloseTo_sig_of_tendsto_pos`;
* label `0` (`NegativeOn`): the frozen deeper slope is negative, so the gate saturates to `0`
  via the negative mirror `tendsto_gate_zero_of_tendsto_neg`;
* label `α` (`ZeroPolynomial`): the rescaled actual slope `τ·λ_l(τ)` tends to `0` (the α-branch
  estimate, from `zeroDialForm`), so the gate tends to `sig(logScale r) = alpha r` by continuity
  of `sig` (`tendsto_gate_alpha_of_tendsto_tau_mul_zero`).
-/

section SatZetaLimits
open Filter Topology

/-- **Frozen value vanishes (partial L2 / faithfulness input).**  If `Φ` is the zero dial form
(`Φ.Xpoly = 0` and `Sym Φ.Ypoly = 0`), then the dial evaluation `dialEval Φ` vanishes at every
point.  Combined with `dialEval_phiHead_eq_frozenSlope` this is precisely the statement that the
frozen deeper slope of an α-labeled head is identically `0` — the input to the α-branch estimate
`τ·λ → 0` (the deeper slope's frozen value is `0`, so `τ·λ = τ·(actual − frozen) = τ·actual`). -/
theorem dialEval_eq_zero_of_zeroDialForm {d : Nat} (Φ : QuadraticDialForm d)
    (hz : zeroDialForm Φ) (x : ProbePair d × ℝ) :
    dialEval Φ x = 0 := by
  obtain ⟨hX, hY⟩ := hz
  set Y := evalPolynomialMatrix x.2 Φ.Ypoly with hYdef
  have hYsym : Y + Yᵀ = 0 := by
    have hcong := congrArg (evalPolynomialMatrix x.2) hY
    rw [eval_add, eval_transpose, eval_zeroMatrix] at hcong
    rw [hYdef]; exact hcong
  have hterm1 : NLayer.matrixBilin (evalPolynomialMatrix x.2 Φ.Xpoly) x.1.1 x.1.2 = 0 := by
    rw [hX, eval_zeroMatrix]; simp [NLayer.matrixBilin]
  have hswap : NLayer.matrixBilin Yᵀ x.1.1 x.1.1 = NLayer.matrixBilin Y x.1.1 x.1.1 := by
    show x.1.1 ⬝ᵥ (Yᵀ *ᵥ x.1.1) = x.1.1 ⬝ᵥ (Y *ᵥ x.1.1)
    rw [dotProduct_comm x.1.1 (Yᵀ *ᵥ x.1.1), adjoint_dotProduct Y x.1.1 x.1.1]
  have hsplit : NLayer.matrixBilin (Y + Yᵀ) x.1.1 x.1.1
      = NLayer.matrixBilin Y x.1.1 x.1.1 + NLayer.matrixBilin Yᵀ x.1.1 x.1.1 := by
    show x.1.1 ⬝ᵥ ((Y + Yᵀ) *ᵥ x.1.1)
        = x.1.1 ⬝ᵥ (Y *ᵥ x.1.1) + x.1.1 ⬝ᵥ (Yᵀ *ᵥ x.1.1)
    rw [Matrix.add_mulVec, dotProduct_add]
  have hterm2 : NLayer.matrixBilin Y x.1.1 x.1.1 = 0 := by
    have hzs : NLayer.matrixBilin (Y + Yᵀ) x.1.1 x.1.1 = 0 := by
      rw [hYsym]; simp [NLayer.matrixBilin]
    rw [hsplit, hswap] at hzs; linarith
  rw [dialEval, hterm1, zero_add, ← hYdef]
  exact hterm2

/-- **Negative mirror** of `expCloseTo_sig_of_tendsto_pos`.  If the (dialed) slope tends to a
negative limit, the gate `sig(τ·λ(τ) + b)` tends to `0`.  This reuses the reusable cascade
lemma `eventuallyExpClose_sig_tau_mul_of_tendsto_neg` (`IDL.CascadeSaturation`). -/
theorem tendsto_gate_zero_of_tendsto_neg {lam : ℝ → ℝ} {Λ b : ℝ}
    (hΛ : Λ < 0) (hlam : Tendsto lam atTop (𝓝 Λ)) :
    Tendsto (fun τ => sig (τ * lam τ + b)) atTop (𝓝 0) :=
  (expCloseTo_of_eventuallyExpClose
    (eventuallyExpClose_sig_tau_mul_of_tendsto_neg hΛ hlam)).tendsto

/-- **α-branch gate limit.**  If the rescaled slope `τ·λ(τ)` tends to `0`, the gate
`sig(τ·λ(τ) + logScale r)` tends to `alpha r = sig(logScale r)`, by continuity of `sig`.  The
`τ·λ(τ) → 0` hypothesis is exactly the α-branch estimate (Task 2 / L2). -/
theorem tendsto_gate_alpha_of_tendsto_tau_mul_zero (r : Nat) {lam : ℝ → ℝ}
    (hzero : Tendsto (fun τ => τ * lam τ) atTop (𝓝 0)) :
    Tendsto (fun τ => sig (τ * lam τ + logScale r)) atTop (𝓝 (alpha r)) := by
  have h1 : Tendsto (fun τ => τ * lam τ + logScale r) atTop (𝓝 (0 + logScale r)) :=
    hzero.add_const _
  have h2 := (continuous_sig.tendsto (0 + logScale r)).comp h1
  simpa [alpha, zero_add, Function.comp] using h2

/-- Bridge from proposition-valued exponential closeness to the data-carrying
eventual exponential-close predicate. -/
noncomputable def eventuallyExpClose_of_expCloseTo
    {f : ℝ → ℝ} {a : ℝ} (h : ExpCloseTo f a) :
    EventuallyExpClose f a :=
  let rate := Classical.choose h
  let hrateData := Classical.choose_spec h
  let coeff := Classical.choose hrateData
  let hcoeffData := Classical.choose_spec hrateData
  let start := Classical.choose hcoeffData
  let hspec := Classical.choose_spec hcoeffData
  ⟨rate, hspec.1, coeff, hspec.2.1, start, hspec.2.2⟩

/-! ## Bounded K-head formal-variable telescope -/

/-- Prefix assignment on a finite list of formal variables: the first `n` listed
coordinates use the live assignment `rho`, while all remaining coordinates use
the saturated/base assignment `sigma`. -/
noncomputable def formalVarPrefixAssignment {L k : Nat}
    (rho sigma : ℝ -> FormalVar L k -> ℝ)
    (vars : List (FormalVar L k)) (n : Nat) (tau : ℝ) :
    FormalVar L k -> ℝ :=
  fun x => if x ∈ vars.take n then rho tau x else sigma tau x

@[simp] theorem formalVarPrefixAssignment_of_mem_take {L k : Nat}
    (rho sigma : ℝ -> FormalVar L k -> ℝ)
    (vars : List (FormalVar L k)) (n : Nat) (tau : ℝ)
    {x : FormalVar L k} (hx : x ∈ vars.take n) :
    formalVarPrefixAssignment rho sigma vars n tau x = rho tau x := by
  simp [formalVarPrefixAssignment, hx]

@[simp] theorem formalVarPrefixAssignment_of_not_mem_take {L k : Nat}
    (rho sigma : ℝ -> FormalVar L k -> ℝ)
    (vars : List (FormalVar L k)) (n : Nat) (tau : ℝ)
    {x : FormalVar L k} (hx : x ∉ vars.take n) :
    formalVarPrefixAssignment rho sigma vars n tau x = sigma tau x := by
  simp [formalVarPrefixAssignment, hx]

@[simp] theorem formalVarPrefixAssignment_zero {L k : Nat}
    (rho sigma : ℝ -> FormalVar L k -> ℝ)
    (vars : List (FormalVar L k)) (tau : ℝ) :
    formalVarPrefixAssignment rho sigma vars 0 tau = sigma tau := by
  funext x
  simp [formalVarPrefixAssignment]

theorem formalVarPrefixAssignment_length_of_mem {L k : Nat}
    (rho sigma : ℝ -> FormalVar L k -> ℝ)
    (vars : List (FormalVar L k)) (tau : ℝ)
    {x : FormalVar L k} (hx : x ∈ vars) :
    formalVarPrefixAssignment rho sigma vars vars.length tau x = rho tau x := by
  have htake : vars.take vars.length = vars := List.take_length (l := vars)
  simp [formalVarPrefixAssignment, htake, hx]

theorem formalVarPrefixAssignment_length_of_not_mem {L k : Nat}
    (rho sigma : ℝ -> FormalVar L k -> ℝ)
    (vars : List (FormalVar L k)) (tau : ℝ)
    {x : FormalVar L k} (hx : x ∉ vars) :
    formalVarPrefixAssignment rho sigma vars vars.length tau x = sigma tau x := by
  have htake : vars.take vars.length = vars := List.take_length (l := vars)
  simp [formalVarPrefixAssignment, htake, hx]

/-- Generic finite-coordinate telescope for K-head formal polynomial
assignments.  The list `vars` is explicit so downstream callers can choose the
active coordinates and exclude live coordinates such as the selected first-layer
head. -/
noncomputable def eventuallyExpClose_eval_formalPoly_delta_of_formalVarPrefix_lipschitz
    {L k : Nat} (p : FormalPoly L k)
    (vars : List (FormalVar L k))
    (rho sigma : ℝ -> FormalVar L k -> ℝ)
    (K T : Nat -> ℝ)
    (hcoord : ∀ i : Nat, (hi : i < vars.length) ->
      EventuallyExpClose
        (fun tau => rho tau (vars[i]'hi) - sigma tau (vars[i]'hi)) 0)
    (hK : ∀ i : Nat, i < vars.length -> 0 ≤ K i)
    (hLip : ∀ i : Nat, (hi : i < vars.length) ->
      ∀ tau : ℝ, T i ≤ tau ->
        |MvPolynomial.eval (formalVarPrefixAssignment rho sigma vars (i + 1) tau) p -
          MvPolynomial.eval (formalVarPrefixAssignment rho sigma vars i tau) p| ≤
          K i * |rho tau (vars[i]'hi) - sigma tau (vars[i]'hi)|) :
    EventuallyExpClose
      (fun tau =>
        MvPolynomial.eval (formalVarPrefixAssignment rho sigma vars vars.length tau) p -
        MvPolynomial.eval (formalVarPrefixAssignment rho sigma vars 0 tau) p)
      0 := by
  classical
  let A : ℝ -> Nat -> ℝ :=
    fun tau n => MvPolynomial.eval (formalVarPrefixAssignment rho sigma vars n tau) p
  have hterm :
      ∀ i : Nat, i < vars.length ->
        EventuallyExpClose (fun tau => A tau (i + 1) - A tau i) 0 := by
    intro i hi
    exact
      eventuallyExpClose_delta_of_eventual_lipschitz
        (x := fun tau => rho tau (vars[i]'hi) - sigma tau (vars[i]'hi))
        (delta := fun tau => A tau (i + 1) - A tau i)
        (a := 0) (K := K i) (T := T i)
        (hcoord i hi) (hK i hi)
        (by
          intro tau htau
          simpa [A] using hLip i hi tau htau)
  have hsum :
      EventuallyExpClose
        (fun tau =>
          (Finset.range vars.length).sum (fun i => A tau (i + 1) - A tau i))
        0 :=
    EventuallyExpClose.sum_range_zero vars.length hterm
  refine hsum.congr_of_forall_eq ?_ rfl
  intro tau
  have htel := sum_range_forward_difference (fun n => A tau n) vars.length
  calc
    (Finset.range vars.length).sum (fun i => A tau (i + 1) - A tau i)
        = A tau vars.length - A tau 0 := htel
    _ =
        MvPolynomial.eval (formalVarPrefixAssignment rho sigma vars vars.length tau) p -
          MvPolynomial.eval (formalVarPrefixAssignment rho sigma vars 0 tau) p := rfl

/-- Exponential zero-slope control is the strict rate needed for the alpha branch:
the extra factor of `τ` is absorbed by exponential decay. -/
theorem tendsto_tau_mul_of_eventuallyExpClose_zero {lam : ℝ → ℝ}
    (h : EventuallyExpClose lam 0) :
    Tendsto (fun τ => τ * lam τ) atTop (𝓝 0) := by
  have hdecay :
      Tendsto (fun τ : ℝ => h.coeff * (τ ^ (1 : ℝ) * Real.exp (-h.rate * τ)))
        atTop (𝓝 0) := by
    simpa using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) h.rate h.rate_pos).const_mul
        h.coeff
  have hbound :
      ∀ᶠ τ : ℝ in atTop,
        ‖τ * lam τ‖ ≤ h.coeff * (τ ^ (1 : ℝ) * Real.exp (-h.rate * τ)) := by
    filter_upwards [eventually_ge_atTop h.start, eventually_ge_atTop (0 : ℝ)] with τ hτs hτ0
    have hlam : |lam τ| ≤ h.coeff * Real.exp (-h.rate * τ) := by
      simpa using h.bound τ hτs
    calc
      ‖τ * lam τ‖ = |τ * lam τ| := Real.norm_eq_abs _
      _ = |τ| * |lam τ| := abs_mul τ (lam τ)
      _ = τ * |lam τ| := by rw [abs_of_nonneg hτ0]
      _ ≤ τ * (h.coeff * Real.exp (-h.rate * τ)) :=
        mul_le_mul_of_nonneg_left hlam hτ0
      _ = h.coeff * (τ * Real.exp (-h.rate * τ)) := by ring
      _ = h.coeff * (τ ^ (1 : ℝ) * Real.exp (-h.rate * τ)) := by
        rw [Real.rpow_one]
  exact squeeze_zero_norm' hbound hdecay

/-- Proposition-valued `ExpCloseTo` version of
`tendsto_tau_mul_of_eventuallyExpClose_zero`. -/
theorem tendsto_tau_mul_of_expCloseTo_zero {lam : ℝ → ℝ}
    (h : ExpCloseTo lam 0) :
    Tendsto (fun τ => τ * lam τ) atTop (𝓝 0) := by
  obtain ⟨rate, coeff, start, hrate, hcoeff, hbound⟩ := h
  exact tendsto_tau_mul_of_eventuallyExpClose_zero
    ({ rate := rate
       rate_pos := hrate
       coeff := coeff
       coeff_nonneg := hcoeff
       start := start
       bound := hbound } : EventuallyExpClose lam 0)

/-- Exponential zero-slope control discharges the alpha-branch gate limit. -/
theorem tendsto_gate_alpha_of_eventuallyExpClose_zero (r : Nat) {lam : ℝ → ℝ}
    (h : EventuallyExpClose lam 0) :
    Tendsto (fun τ => sig (τ * lam τ + logScale r)) atTop (𝓝 (alpha r)) :=
  tendsto_gate_alpha_of_tendsto_tau_mul_zero r (tendsto_tau_mul_of_eventuallyExpClose_zero h)

/-- `ExpCloseTo` version of the alpha-branch gate limit. -/
theorem tendsto_gate_alpha_of_expCloseTo_zero (r : Nat) {lam : ℝ → ℝ}
    (h : ExpCloseTo lam 0) :
    Tendsto (fun τ => sig (τ * lam τ + logScale r)) atTop (𝓝 (alpha r)) :=
  tendsto_gate_alpha_of_tendsto_tau_mul_zero r (tendsto_tau_mul_of_expCloseTo_zero h)

/-- Stronger alpha-branch gate estimate: an exponentially small slope gives an
exponentially close gate to `alpha r`. -/
noncomputable def expCloseTo_gate_alpha_of_expCloseTo_slope_zero (r : Nat) {lam : ℝ → ℝ}
    (h : ExpCloseTo lam 0) :
    ExpCloseTo (fun τ => sig (τ * lam τ + logScale r)) (alpha r) := by
  obtain ⟨rate, coeff, start, hrate, hcoeff, hbound⟩ := h
  let hee : EventuallyExpClose lam 0 :=
    { rate := rate
      rate_pos := hrate
      coeff := coeff
      coeff_nonneg := hcoeff
      start := start
      bound := hbound }
  have hsig :=
    eventuallyExpClose_sig_tau_mul_of_eventuallyExpClose_zero
      (lam := lam) (b := logScale r) (c := rate / 2) hee
      (by linarith [hrate]) (by linarith [hrate])
  exact expCloseTo_of_eventuallyExpClose ((hsig.congr_of_forall_eq (fun _ => rfl) (by simp [alpha])))

/-- **L1 — ζ-general per-point convergence.**  Generalizes `tendsto_dialActualProbePoint`
(`Step2.DialLimits`) from the `K = I` collapse (`dialSatPoint`, all deeper labels `1`) to the
ζ-general frozen recursion point `satZetaPoint`.  Along the θ-dial path the layer-`n` actual
probe point converges to `satZetaPoint θ h ζ p t n`, for every `n ≤ m + 1`, provided:

* the layer-0 dial data (`ht_pos`/`ht_lt_one`/`hq`/`hpi`/`hsep`), exactly as in the template; and
* `hlabel`, the per-deeper-head trichotomy classification: each deeper head `(n, a)` with
  `1 ≤ n < m + 1` is in one of the three label cases, with the matching analytic witness
  (positive frozen slope for label `1`, negative frozen slope for label `0`, or the α-branch
  estimate `τ·λ → 0` for label `α`).

The proof is a faithful generalization of the template: base case `tendsto_headDialPath`;
successor couples `continuous_gatedEffectivePoint` with the per-layer gate convergence, where the
layer-0 gates track `satGate` (`tendsto_dialLayerGates_zero`) and each deeper gate converges to
its label value through the three cases above. -/
theorem tendsto_satZetaActualProbePoint (r : Nat) {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (ζ : SaturatedLabels k) (p : ProbePair d) (t : ℝ)
    (ht_pos : 0 < t) (ht_lt_one : t < 1)
    (hq : firstHeadSlope (attentionMatrix θ 0) h p = 0)
    (hpi : firstHeadPi (attentionMatrix θ 0) h p ≠ 0)
    (hsep : ∀ a : Fin k, a ≠ h → 0 < matrixBilin (attentionMatrix θ 0 a) p.1 p.2)
    (hlabel : ∀ (n : Nat), 1 ≤ n → (hn : n < m + 1) → ∀ (a : Fin k),
      (ζ (n + 1) a = 1 ∧ 0 < matrixBilin (attentionMatrix θ ⟨n, hn⟩ a)
          (satZetaPoint θ h ζ p t n).1 (satZetaPoint θ h ζ p t n).2)
      ∨ (ζ (n + 1) a = 0 ∧ matrixBilin (attentionMatrix θ ⟨n, hn⟩ a)
          (satZetaPoint θ h ζ p t n).1 (satZetaPoint θ h ζ p t n).2 < 0)
      ∨ (ζ (n + 1) a = alpha r ∧ Tendsto (fun τ => τ * actualProbeSlope r θ
          (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
          (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2 τ ⟨n, hn⟩ a)
          atTop (𝓝 0)))
    (n : Nat) (hn : n ≤ m + 1) :
    Tendsto (fun τ => actualProbePoint r θ
        (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
        (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2 n hn τ)
      atTop (𝓝 (satZetaPoint θ h ζ p t n)) := by
  revert hn
  induction n with
  | zero =>
      intro hn
      simp only [actualProbePoint_zero, satZetaPoint_zero]
      exact tendsto_headDialPath (attentionMatrix θ 0) h (logScale r) p t
  | succ n ih =>
      intro hn
      have hlt : n < m + 1 := Nat.lt_of_succ_le hn
      have hIH := ih (Nat.le_of_succ_le hn)
      have hgate : Tendsto (fun τ => layerGates r θ ⟨n, hlt⟩
          (actualProbePoint r θ
            (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
            (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2 n
            (Nat.le_of_succ_le hn) τ).1
          (actualProbePoint r θ
            (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
            (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2 n
            (Nat.le_of_succ_le hn) τ).2 τ)
          atTop (𝓝 (satZetaGate ζ t h n)) := by
        rcases Nat.eq_zero_or_pos n with hn0 | hnpos
        · subst hn0
          have h0 : (⟨0, hlt⟩ : Fin (m + 1)) = 0 := by apply Fin.ext; simp
          rw [satZetaGate_zero]
          have hz := tendsto_dialLayerGates_zero r θ h p t ht_pos ht_lt_one hq hpi hsep
          refine hz.congr (fun τ => ?_)
          simp only [actualProbePoint_zero, h0]
        · rw [satZetaGate_pos ζ t h hnpos, tendsto_pi_nhds]
          intro a
          have hcontB : Continuous (fun q : ProbePair d =>
              matrixBilin (attentionMatrix θ ⟨n, hlt⟩ a) q.1 q.2) :=
            continuous_matrixBilin _ continuous_fst continuous_snd
          have hslope := (hcontB.tendsto (satZetaPoint θ h ζ p t n)).comp hIH
          rcases hlabel n hnpos hlt a with ⟨hζ1, hpos⟩ | ⟨hζ0, hneg⟩ | ⟨hζa, hzero⟩
          · rw [hζ1]
            have heng := (expCloseTo_sig_of_tendsto_pos (b := logScale r) hpos hslope).tendsto
            refine heng.congr (fun τ => ?_)
            simp only [Function.comp_apply, layerGates, headGate]
          · rw [hζ0]
            have heng := tendsto_gate_zero_of_tendsto_neg (b := logScale r) hneg hslope
            refine heng.congr (fun τ => ?_)
            simp only [Function.comp_apply, layerGates, headGate]
          · rw [hζa]
            refine (tendsto_gate_alpha_of_tendsto_tau_mul_zero r (lam := fun τ =>
                actualProbeSlope r θ
                  (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
                  (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2 τ ⟨n, hlt⟩ a)
                hzero).congr (fun τ => ?_)
            simp only [layerGates, headGate, actualProbeSlope]
      have hcont := continuous_gatedEffectivePoint θ ⟨n, hlt⟩
      have hcomp := (hcont.tendsto (satZetaGate ζ t h n, satZetaPoint θ h ζ p t n)).comp
        (hgate.prodMk_nhds hIH)
      rw [satZetaPoint_succ_of_lt θ h ζ p t n hlt]
      refine hcomp.congr (fun τ => ?_)
      simp only [Function.comp_apply]
      rw [actualProbePoint_succ]

/-- Prefix form of `tendsto_satZetaActualProbePoint`.  To prove convergence of the layer-`N`
actual probe point, it is enough to know the label/analytic cases for strictly earlier deeper
layers `n < N`.  This is the non-circular shape needed when the current layer-`N` slope is being
estimated from a zero dial form. -/
theorem tendsto_satZetaActualProbePoint_prefix (r : Nat) {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (ζ : SaturatedLabels k)
    (p : ProbePair d) (t : ℝ)
    (ht_pos : 0 < t) (ht_lt_one : t < 1)
    (hq : firstHeadSlope (attentionMatrix θ 0) h p = 0)
    (hpi : firstHeadPi (attentionMatrix θ 0) h p ≠ 0)
    (hsep : ∀ a : Fin k, a ≠ h → 0 < matrixBilin (attentionMatrix θ 0 a) p.1 p.2)
    (N : Nat) (hN : N ≤ m + 1)
    (hlabel : ∀ (n : Nat), 1 ≤ n → n < N → (hn : n < m + 1) → ∀ (a : Fin k),
      (ζ (n + 1) a = 1 ∧ 0 < matrixBilin (attentionMatrix θ ⟨n, hn⟩ a)
          (satZetaPoint θ h ζ p t n).1 (satZetaPoint θ h ζ p t n).2)
      ∨ (ζ (n + 1) a = 0 ∧ matrixBilin (attentionMatrix θ ⟨n, hn⟩ a)
          (satZetaPoint θ h ζ p t n).1 (satZetaPoint θ h ζ p t n).2 < 0)
      ∨ (ζ (n + 1) a = alpha r ∧ Tendsto (fun τ => τ * actualProbeSlope r θ
          (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
          (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2 τ ⟨n, hn⟩ a)
          atTop (𝓝 0))) :
    Tendsto (fun τ => actualProbePoint r θ
        (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
        (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2 N hN τ)
      atTop (𝓝 (satZetaPoint θ h ζ p t N)) := by
  revert hN hlabel
  induction N with
  | zero =>
      intro hN _hlabel
      simp only [actualProbePoint_zero, satZetaPoint_zero]
      exact tendsto_headDialPath (attentionMatrix θ 0) h (logScale r) p t
  | succ N ih =>
      intro hN hlabel
      have hlt : N < m + 1 := Nat.lt_of_succ_le hN
      have hIH := ih (Nat.le_of_succ_le hN)
        (fun n hnpos hnN hn a =>
          hlabel n hnpos (lt_trans hnN (Nat.lt_succ_self N)) hn a)
      have hgate : Tendsto (fun τ => layerGates r θ ⟨N, hlt⟩
          (actualProbePoint r θ
            (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
            (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2 N
            (Nat.le_of_succ_le hN) τ).1
          (actualProbePoint r θ
            (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
            (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2 N
            (Nat.le_of_succ_le hN) τ).2 τ)
          atTop (𝓝 (satZetaGate ζ t h N)) := by
        rcases Nat.eq_zero_or_pos N with hN0 | hNpos
        · subst hN0
          have h0 : (⟨0, hlt⟩ : Fin (m + 1)) = 0 := by apply Fin.ext; simp
          rw [satZetaGate_zero]
          have hz := tendsto_dialLayerGates_zero r θ h p t ht_pos ht_lt_one hq hpi hsep
          refine hz.congr (fun τ => ?_)
          simp only [actualProbePoint_zero, h0]
        · rw [satZetaGate_pos ζ t h hNpos, tendsto_pi_nhds]
          intro a
          have hcontB : Continuous (fun q : ProbePair d =>
              matrixBilin (attentionMatrix θ ⟨N, hlt⟩ a) q.1 q.2) :=
            continuous_matrixBilin _ continuous_fst continuous_snd
          have hslope := (hcontB.tendsto (satZetaPoint θ h ζ p t N)).comp hIH
          rcases hlabel N hNpos (Nat.lt_succ_self N) hlt a with
            ⟨hζ1, hpos⟩ | ⟨hζ0, hneg⟩ | ⟨hζa, hzero⟩
          · rw [hζ1]
            have heng := (expCloseTo_sig_of_tendsto_pos (b := logScale r) hpos hslope).tendsto
            refine heng.congr (fun τ => ?_)
            simp only [Function.comp_apply, layerGates, headGate]
          · rw [hζ0]
            have heng := tendsto_gate_zero_of_tendsto_neg (b := logScale r) hneg hslope
            refine heng.congr (fun τ => ?_)
            simp only [Function.comp_apply, layerGates, headGate]
          · rw [hζa]
            refine (tendsto_gate_alpha_of_tendsto_tau_mul_zero r (lam := fun τ =>
                actualProbeSlope r θ
                  (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
                  (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2 τ ⟨N, hlt⟩ a)
                hzero).congr (fun τ => ?_)
            simp only [layerGates, headGate, actualProbeSlope]
      have hcont := continuous_gatedEffectivePoint θ ⟨N, hlt⟩
      have hcomp := (hcont.tendsto (satZetaGate ζ t h N, satZetaPoint θ h ζ p t N)).comp
        (hgate.prodMk_nhds hIH)
      rw [satZetaPoint_succ_of_lt θ h ζ p t N hlt]
      refine hcomp.congr (fun τ => ?_)
      simp only [Function.comp_apply]
      rw [actualProbePoint_succ]

/-- If the actual prefix point converges to the ζ-frozen point, then the corresponding actual
slope converges to the frozen bilinear slope. -/
theorem tendsto_actualProbeSlope_of_tendsto_satZetaPoint (r : Nat) {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (ζ : SaturatedLabels k)
    (p : ProbePair d) (t : ℝ) (n : Nat) (hn : n < m + 1) (a : Fin k)
    (hpt : Tendsto (fun τ => actualProbePoint r θ
        (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
        (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2
        n (Nat.le_of_lt hn) τ)
      atTop (𝓝 (satZetaPoint θ h ζ p t n))) :
    Tendsto (fun τ => actualProbeSlope r θ
        (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
        (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2
        τ ⟨n, hn⟩ a)
      atTop (𝓝 (matrixBilin (attentionMatrix θ ⟨n, hn⟩ a)
        (satZetaPoint θ h ζ p t n).1 (satZetaPoint θ h ζ p t n).2)) := by
  have hcont : Continuous (fun q : ProbePair d =>
      matrixBilin (attentionMatrix θ ⟨n, hn⟩ a) q.1 q.2) :=
    continuous_matrixBilin _ continuous_fst continuous_snd
  have hcomp := (hcont.tendsto (satZetaPoint θ h ζ p t n)).comp hpt
  refine hcomp.congr (fun τ => ?_)
  simp only [Function.comp_apply, actualProbeSlope]

/-- Zero dial form cancels the corresponding formal slope under the saturated ζ-gate
assignment.  This is the algebraic cancellation bridge used before estimating the live
actual slope's deviation from the frozen saturated value. -/
theorem eval_formalSlope_satZetaGateAssignment_zero_of_zeroDialForm
    {m k d r : Nat} (θ : Params (m + 1) k d) (head : Fin k)
    (labels : DeeperHead → TrichotomyLabel)
    (p : ProbePair d) (t : ℝ)
    (q : Nat) (hqpos : 1 ≤ q) (hq : q < m + 1) (a : Fin k)
    (hz : zeroDialForm
      (phiHeadOfDeeperHead r θ head
        { layer := q + 1, head := (a : Nat) + 1 } labels)) :
    MvPolynomial.eval
      (fun x : FormalVar (m + 1) k =>
        satZetaGate (trichotomyToSaturatedLabels r (m + 1) k labels)
          t head x.1.1 x.2)
      (formalSlope θ p.1 p.2 ⟨q, hq⟩ a) = 0 := by
  change MvPolynomial.eval
      (satZetaGateAssignment (m := m)
        (trichotomyToSaturatedLabels r (m + 1) k labels) t head)
      (formalSlope θ p.1 p.2 ⟨q, hq⟩ a) = 0
  rw [eval_formalSlope_satZetaGateAssignment]
  have hdial :=
    dialEval_phiHeadOfDeeperHead_succ_eq_frozenSlope r θ head labels
      q hqpos hq a p t
  have hzeroEval := dialEval_eq_zero_of_zeroDialForm
    (phiHeadOfDeeperHead r θ head { layer := q + 1, head := (a : Nat) + 1 } labels)
    hz (p, t)
  rw [hdial] at hzeroEval
  exact hzeroEval

/-- Zero dial form plus prefix-point convergence gives the unscaled alpha-branch slope limit.
This proves the algebraic/faithfulness part of L2; the remaining estimate is the rate upgrade
from `actualProbeSlope -> 0` to `τ * actualProbeSlope -> 0`. -/
theorem tendsto_actualProbeSlope_zero_of_zeroDialForm {m k d r : Nat}
    (θ : Params (m + 1) k d) (h : Fin k)
    (labels : DeeperHead → TrichotomyLabel) (p : ProbePair d) (t : ℝ)
    (n : Nat) (hnpos : 1 ≤ n) (hn : n < m + 1) (a : Fin k)
    (hpt : Tendsto (fun τ => actualProbePoint r θ
        (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
        (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2
        n (Nat.le_of_lt hn) τ)
      atTop (𝓝 (satZetaPoint θ h
        (trichotomyToSaturatedLabels r (m + 1) k labels) p t n)))
    (hz : zeroDialForm (phiHeadOfDeeperHead r θ h
      { layer := n + 1, head := (a : Nat) + 1 } labels)) :
    Tendsto (fun τ => actualProbeSlope r θ
        (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
        (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2
        τ ⟨n, hn⟩ a) atTop (𝓝 0) := by
  have hslope := tendsto_actualProbeSlope_of_tendsto_satZetaPoint r θ h
    (trichotomyToSaturatedLabels r (m + 1) k labels) p t n hn a hpt
  have hdial :=
    dialEval_phiHeadOfDeeperHead_succ_eq_frozenSlope r θ h labels n hnpos hn a p t
  have hzeroEval := dialEval_eq_zero_of_zeroDialForm
    (phiHeadOfDeeperHead r θ h { layer := n + 1, head := (a : Nat) + 1 } labels)
    hz (p, t)
  have hfrozen : matrixBilin (attentionMatrix θ ⟨n, hn⟩ a)
      (satZetaPoint θ h (trichotomyToSaturatedLabels r (m + 1) k labels) p t n).1
      (satZetaPoint θ h (trichotomyToSaturatedLabels r (m + 1) k labels) p t n).2 = 0 := by
    rw [hdial] at hzeroEval
    exact hzeroEval
  have hfrozen' :
      (satZetaPoint θ h (trichotomyToSaturatedLabels r (m + 1) k labels) p t n).1 ⬝ᵥ
        (attentionMatrix θ ⟨n, hn⟩ a) *ᵥ
          (satZetaPoint θ h (trichotomyToSaturatedLabels r (m + 1) k labels) p t n).2 = 0 := by
    simpa [matrixBilin] using hfrozen
  simpa [hfrozen'] using hslope

/-- Non-circular current-head slope limit: prior label cases give prefix-point convergence, and
the current head's zero dial form then forces its actual slope to tend to zero. -/
theorem tendsto_actualProbeSlope_zero_of_zeroDialForm_prefix {m k d r : Nat}
    (θ : Params (m + 1) k d) (h : Fin k)
    (labels : DeeperHead → TrichotomyLabel) (p : ProbePair d) (t : ℝ)
    (ht_pos : 0 < t) (ht_lt_one : t < 1)
    (hq : firstHeadSlope (attentionMatrix θ 0) h p = 0)
    (hpi : firstHeadPi (attentionMatrix θ 0) h p ≠ 0)
    (hsep : ∀ a : Fin k, a ≠ h → 0 < matrixBilin (attentionMatrix θ 0 a) p.1 p.2)
    (n : Nat) (hnpos : 1 ≤ n) (hn : n < m + 1) (a : Fin k)
    (hlabel : ∀ (q : Nat), 1 ≤ q → q < n → (hq' : q < m + 1) → ∀ (b : Fin k),
      (trichotomyToSaturatedLabels r (m + 1) k labels (q + 1) b = 1 ∧
        0 < matrixBilin (attentionMatrix θ ⟨q, hq'⟩ b)
          (satZetaPoint θ h (trichotomyToSaturatedLabels r (m + 1) k labels) p t q).1
          (satZetaPoint θ h (trichotomyToSaturatedLabels r (m + 1) k labels) p t q).2)
      ∨ (trichotomyToSaturatedLabels r (m + 1) k labels (q + 1) b = 0 ∧
        matrixBilin (attentionMatrix θ ⟨q, hq'⟩ b)
          (satZetaPoint θ h (trichotomyToSaturatedLabels r (m + 1) k labels) p t q).1
          (satZetaPoint θ h (trichotomyToSaturatedLabels r (m + 1) k labels) p t q).2 < 0)
      ∨ (trichotomyToSaturatedLabels r (m + 1) k labels (q + 1) b = alpha r ∧
        Tendsto (fun τ => τ * actualProbeSlope r θ
          (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
          (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2
          τ ⟨q, hq'⟩ b) atTop (𝓝 0)))
    (hz : zeroDialForm (phiHeadOfDeeperHead r θ h
      { layer := n + 1, head := (a : Nat) + 1 } labels)) :
    Tendsto (fun τ => actualProbeSlope r θ
        (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
        (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2
        τ ⟨n, hn⟩ a) atTop (𝓝 0) := by
  have hpt := tendsto_satZetaActualProbePoint_prefix r θ h
    (trichotomyToSaturatedLabels r (m + 1) k labels) p t
    ht_pos ht_lt_one hq hpi hsep n (Nat.le_of_lt hn) hlabel
  exact tendsto_actualProbeSlope_zero_of_zeroDialForm θ h labels p t n hnpos hn a hpt hz

/-- Actual-probe specialization of `tendsto_tau_mul_of_expCloseTo_zero`: once the
zero-branch error work upgrades the current actual slope to exponential closeness to zero,
the desired rescaled alpha estimate follows immediately. -/
theorem tendsto_tau_mul_actualProbeSlope_of_expCloseTo_zero {m k d r : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (p : ProbePair d) (t : ℝ)
    (n : Nat) (hn : n < m + 1) (a : Fin k)
    (hstrict : ExpCloseTo (fun τ => actualProbeSlope r θ
      (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
      (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2
      τ ⟨n, hn⟩ a) 0) :
    Tendsto (fun τ => τ * actualProbeSlope r θ
      (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
      (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2
      τ ⟨n, hn⟩ a) atTop (𝓝 0) :=
  tendsto_tau_mul_of_expCloseTo_zero hstrict

/-- If the live actual slope differs exponentially from the frozen matrix-bilinear
slope, and the current dial form is zero, then the actual slope is exponentially
close to zero. -/
noncomputable def expCloseTo_actualProbeSlope_zero_of_zeroDialForm_delta {m k d r : Nat}
    (θ : Params (m + 1) k d) (h : Fin k)
    (labels : DeeperHead → TrichotomyLabel) (p : ProbePair d) (t : ℝ)
    (n : Nat) (hnpos : 1 ≤ n) (hn : n < m + 1) (a : Fin k)
    (hdelta :
      EventuallyExpClose
        (fun τ =>
          actualProbeSlope r θ
            (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
            (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2
            τ ⟨n, hn⟩ a -
          matrixBilin (attentionMatrix θ ⟨n, hn⟩ a)
            (satZetaPoint θ h
              (trichotomyToSaturatedLabels r (m + 1) k labels) p t n).1
            (satZetaPoint θ h
              (trichotomyToSaturatedLabels r (m + 1) k labels) p t n).2)
        0)
    (hz : zeroDialForm (phiHeadOfDeeperHead r θ h
      { layer := n + 1, head := (a : Nat) + 1 } labels)) :
    ExpCloseTo (fun τ => actualProbeSlope r θ
      (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
      (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2
      τ ⟨n, hn⟩ a) 0 := by
  have hdial :=
    dialEval_phiHeadOfDeeperHead_succ_eq_frozenSlope r θ h labels n hnpos hn a p t
  have hzeroEval := dialEval_eq_zero_of_zeroDialForm
    (phiHeadOfDeeperHead r θ h { layer := n + 1, head := (a : Nat) + 1 } labels)
    hz (p, t)
  have hfrozen : matrixBilin (attentionMatrix θ ⟨n, hn⟩ a)
      (satZetaPoint θ h (trichotomyToSaturatedLabels r (m + 1) k labels) p t n).1
      (satZetaPoint θ h (trichotomyToSaturatedLabels r (m + 1) k labels) p t n).2 = 0 := by
    rw [hdial] at hzeroEval
    exact hzeroEval
  refine expCloseTo_congr ?_ (expCloseTo_of_eventuallyExpClose hdelta)
  intro τ
  rw [hfrozen, sub_zero]

/-- First-layer nondial actual gates saturate along the selected-head dial path.

This is the actual-gate wrapper around `expCloseTo_dialGateAlong_zero_of_pos`, used by
the zero/alpha strict estimate setup for the nondial heads at layer `0`. -/
theorem expCloseTo_actualProbeGate_first_nondial_of_sep
    {m k d r : Nat} (θ : Params (m + 1) k d) (h : Fin k)
    (p : ProbePair d) (t : ℝ)
    (hsep : ∀ a : Fin k, a ≠ h →
      0 < matrixBilin (attentionMatrix θ 0 a) p.1 p.2) :
    ∀ b : Fin k, b ≠ h →
      ExpCloseTo (fun τ => actualProbeGate r θ
        (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
        (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2
        τ ⟨0, Nat.succ_pos m⟩ b) 1 := by
  intro b hb
  refine expCloseTo_congr ?_ (expCloseTo_dialGateAlong_zero_of_pos
    r θ h b (logScale r) (p, t) (hsep b hb))
  intro τ
  rw [dialGateAlong]
  rw [dif_pos (Nat.succ_pos m)]

/-! ## L2 — the α-branch slope delta (live minus frozen, exponentially small) -/

/-- The finite list of all formal gate variables whose layer index is `< n`. -/
def formalVarsBelow (L k n : Nat) : List (FormalVar L k) :=
  ((List.finRange L).flatMap (fun l => (List.finRange k).map (fun b => (l, b)))).filter
    (fun x => decide (x.1.1 < n))

theorem mem_formalVarsBelow {L k n : Nat} (x : FormalVar L k) :
    x ∈ formalVarsBelow L k n ↔ x.1.1 < n := by
  unfold formalVarsBelow
  simp only [List.mem_filter, List.mem_flatMap, List.mem_map, List.mem_finRange,
    decide_eq_true_eq, true_and]
  constructor
  · rintro ⟨_, hx⟩; exact hx
  · intro hx; exact ⟨⟨x.1, x.2, rfl⟩, hx⟩

/-- Generic finite-coordinate telescope for a **τ-dependent** family of K-head formal
polynomials `P τ`.  This is the path (moving-base) analogue of
`eventuallyExpClose_eval_formalPoly_delta_of_formalVarPrefix_lipschitz`: the polynomial is
allowed to vary with `τ` (as it must along a dial path, whose base moves), while the
telescoping algebra over the finite variable list is unchanged. -/
noncomputable def eventuallyExpClose_eval_formalPolyPath_delta_of_formalVarPrefix_lipschitz
    {L k : Nat} (P : ℝ → FormalPoly L k)
    (vars : List (FormalVar L k))
    (rho sigma : ℝ -> FormalVar L k -> ℝ)
    (K T : Nat -> ℝ)
    (hcoord : ∀ i : Nat, (hi : i < vars.length) ->
      EventuallyExpClose
        (fun tau => rho tau (vars[i]'hi) - sigma tau (vars[i]'hi)) 0)
    (hK : ∀ i : Nat, i < vars.length -> 0 ≤ K i)
    (hLip : ∀ i : Nat, (hi : i < vars.length) ->
      ∀ tau : ℝ, T i ≤ tau ->
        |MvPolynomial.eval (formalVarPrefixAssignment rho sigma vars (i + 1) tau) (P tau) -
          MvPolynomial.eval (formalVarPrefixAssignment rho sigma vars i tau) (P tau)| ≤
          K i * |rho tau (vars[i]'hi) - sigma tau (vars[i]'hi)|) :
    EventuallyExpClose
      (fun tau =>
        MvPolynomial.eval (formalVarPrefixAssignment rho sigma vars vars.length tau) (P tau) -
        MvPolynomial.eval (formalVarPrefixAssignment rho sigma vars 0 tau) (P tau))
      0 := by
  classical
  let A : ℝ -> Nat -> ℝ :=
    fun tau n => MvPolynomial.eval (formalVarPrefixAssignment rho sigma vars n tau) (P tau)
  have hterm :
      ∀ i : Nat, i < vars.length ->
        EventuallyExpClose (fun tau => A tau (i + 1) - A tau i) 0 := by
    intro i hi
    exact
      eventuallyExpClose_delta_of_eventual_lipschitz
        (x := fun tau => rho tau (vars[i]'hi) - sigma tau (vars[i]'hi))
        (delta := fun tau => A tau (i + 1) - A tau i)
        (a := 0) (K := K i) (T := T i)
        (hcoord i hi) (hK i hi)
        (by
          intro tau htau
          simpa [A] using hLip i hi tau htau)
  have hsum :
      EventuallyExpClose
        (fun tau =>
          (Finset.range vars.length).sum (fun i => A tau (i + 1) - A tau i))
        0 :=
    EventuallyExpClose.sum_range_zero vars.length hterm
  refine hsum.congr_of_forall_eq ?_ rfl
  intro tau
  have htel := sum_range_forward_difference (fun n => A tau n) vars.length
  calc
    (Finset.range vars.length).sum (fun i => A tau (i + 1) - A tau i)
        = A tau vars.length - A tau 0 := htel
    _ =
        MvPolynomial.eval (formalVarPrefixAssignment rho sigma vars vars.length tau) (P tau) -
          MvPolynomial.eval (formalVarPrefixAssignment rho sigma vars 0 tau) (P tau) := rfl

/-- The actual (live) formal gate assignment along the `h`-dial path based at `(p,t)`. -/
noncomputable def dialActualGate {m k d : Nat} (r : Nat) (θ : Params (m + 1) k d) (h : Fin k)
    (p : ProbePair d) (t : ℝ) (τ : ℝ) : FormalVar (m + 1) k → ℝ :=
  actualProbeGateAssignment r θ
    (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
    (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2 τ

/-- The frozen (reference) formal gate assignment along the dial path: the selected
first-layer dial head keeps its **actual** live value, every other first-layer head is
frozen at `1`, and each deeper head is frozen at its ζ-label.  This is the tuple `ŝ(τ)` of
the zero-branch error lemma. -/
noncomputable def dialFrozenGate {m k d : Nat} (r : Nat) (θ : Params (m + 1) k d) (h : Fin k)
    (labels : DeeperHead → TrichotomyLabel) (p : ProbePair d) (t : ℝ) (τ : ℝ) :
    FormalVar (m + 1) k → ℝ :=
  satZetaGateAssignment (trichotomyToSaturatedLabels r (m + 1) k labels)
    (dialActualGate r θ h p t τ (0, h)) h

/-- **The α-branch delta (L2 core).**  Along the `h`-dial path based at `(p,t)`, the live
actual deeper slope minus the frozen saturated slope tends to `0` exponentially, given the
per-coordinate closeness of the prior live gates to their frozen values (`hgate`) and the
per-coordinate polynomial Lipschitz control of the formal slope along the moving base
(`hLip`).  The frozen slope of an α-labelled head is identically `0` (from `hz`), so this
is exactly the `hdelta` hypothesis of
`expCloseTo_actualProbeSlope_zero_of_zeroDialForm_delta`. -/
noncomputable def eventuallyExpClose_actualProbeSlope_frozen_delta_of_gate_lipschitz
    {m k d r : Nat} (θ : Params (m + 1) k d) (h : Fin k)
    (labels : DeeperHead → TrichotomyLabel) (p : ProbePair d) (t : ℝ)
    (n : Nat) (hnpos : 1 ≤ n) (hn : n < m + 1) (a : Fin k)
    (hz : zeroDialForm (phiHeadOfDeeperHead r θ h
      { layer := n + 1, head := (a : Nat) + 1 } labels))
    (K T : Nat → ℝ)
    (hK : ∀ i : Nat, i < (formalVarsBelow (m + 1) k n).length → 0 ≤ K i)
    (hgate : ∀ i : Nat, (hi : i < (formalVarsBelow (m + 1) k n).length) →
      EventuallyExpClose
        (fun τ =>
          dialActualGate r θ h p t τ ((formalVarsBelow (m + 1) k n)[i]'hi) -
          dialFrozenGate r θ h labels p t τ ((formalVarsBelow (m + 1) k n)[i]'hi)) 0)
    (hLip : ∀ i : Nat, (hi : i < (formalVarsBelow (m + 1) k n).length) →
      ∀ τ : ℝ, T i ≤ τ →
        |MvPolynomial.eval
            (formalVarPrefixAssignment (fun τ => dialActualGate r θ h p t τ)
              (fun τ => dialFrozenGate r θ h labels p t τ)
              (formalVarsBelow (m + 1) k n) (i + 1) τ)
            (formalSlope θ
              (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
              (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2 ⟨n, hn⟩ a) -
          MvPolynomial.eval
            (formalVarPrefixAssignment (fun τ => dialActualGate r θ h p t τ)
              (fun τ => dialFrozenGate r θ h labels p t τ)
              (formalVarsBelow (m + 1) k n) i τ)
            (formalSlope θ
              (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
              (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2 ⟨n, hn⟩ a)|
          ≤ K i *
            |dialActualGate r θ h p t τ ((formalVarsBelow (m + 1) k n)[i]'hi) -
              dialFrozenGate r θ h labels p t τ ((formalVarsBelow (m + 1) k n)[i]'hi)|) :
    EventuallyExpClose
      (fun τ =>
        actualProbeSlope r θ
          (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
          (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2
          τ ⟨n, hn⟩ a -
        matrixBilin (attentionMatrix θ ⟨n, hn⟩ a)
          (satZetaPoint θ h
            (trichotomyToSaturatedLabels r (m + 1) k labels) p t n).1
          (satZetaPoint θ h
            (trichotomyToSaturatedLabels r (m + 1) k labels) p t n).2)
      0 := by
  classical
  set ζ := trichotomyToSaturatedLabels r (m + 1) k labels with hζ
  set vars := formalVarsBelow (m + 1) k n with hvars
  set rho : ℝ → FormalVar (m + 1) k → ℝ := fun τ => dialActualGate r θ h p t τ with hrho
  set sigma : ℝ → FormalVar (m + 1) k → ℝ := fun τ => dialFrozenGate r θ h labels p t τ with hsigma
  set P : ℝ → FormalPoly (m + 1) k :=
    fun τ =>
      formalSlope θ
        (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
        (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2 ⟨n, hn⟩ a with hP
  -- The telescope over the finite prior-variable list.
  have htel :=
    eventuallyExpClose_eval_formalPolyPath_delta_of_formalVarPrefix_lipschitz
      P vars rho sigma K T hgate hK hLip
  -- Endpoint identity: the "all-live" evaluation is the actual dial-path slope.
  have hEA : ∀ τ : ℝ,
      MvPolynomial.eval (formalVarPrefixAssignment rho sigma vars vars.length τ) (P τ) =
        actualProbeSlope r θ
          (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
          (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2 τ ⟨n, hn⟩ a := by
    intro τ
    have hagree :
        MvPolynomial.eval (formalVarPrefixAssignment rho sigma vars vars.length τ) (P τ) =
          MvPolynomial.eval (rho τ) (P τ) := by
      refine eval_formalSlope_eq_of_eq_on_active (θ := θ)
        (formalVarPrefixAssignment rho sigma vars vars.length τ) (rho τ)
        (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
        (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2 ⟨n, hn⟩ a ?_
      intro l' a' hl' _ha'
      have hmem : ((l', a') : FormalVar (m + 1) k) ∈ vars := by
        rw [hvars, mem_formalVarsBelow]; exact hl'
      exact formalVarPrefixAssignment_length_of_mem rho sigma vars τ hmem
    rw [hagree, hrho]
    exact eval_formalSlope_actualProbeGateAssignment r θ _ _ τ ⟨n, hn⟩ a
  -- Endpoint identity: the "all-frozen" evaluation is the (identically-zero) frozen slope.
  have hEB : ∀ τ : ℝ,
      MvPolynomial.eval (formalVarPrefixAssignment rho sigma vars 0 τ) (P τ) = 0 := by
    intro τ
    rw [formalVarPrefixAssignment_zero]
    have hpath := eval_formalSlope_satZetaGateAssignment θ h ζ
      (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ)
      (dialActualGate r θ h p t τ (0, h)) n hn a
    have hval :
        MvPolynomial.eval (sigma τ) (P τ) =
          matrixBilin (attentionMatrix θ ⟨n, hn⟩ a)
            (satZetaPoint θ h ζ
              (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ)
              (dialActualGate r θ h p t τ (0, h)) n).1
            (satZetaPoint θ h ζ
              (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ)
              (dialActualGate r θ h p t τ (0, h)) n).2 := by
      rw [hsigma, hP]; exact hpath
    rw [hval]
    have hdial :=
      dialEval_phiHeadOfDeeperHead_succ_eq_frozenSlope r θ h labels n hnpos hn a
        (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ)
        (dialActualGate r θ h p t τ (0, h))
    rw [hζ, ← hdial]
    exact dialEval_eq_zero_of_zeroDialForm _ hz _
  -- Frozen slope at the fixed base `(p,t)` also vanishes.
  have hEC :
      matrixBilin (attentionMatrix θ ⟨n, hn⟩ a)
        (satZetaPoint θ h ζ p t n).1 (satZetaPoint θ h ζ p t n).2 = 0 := by
    have hdial :=
      dialEval_phiHeadOfDeeperHead_succ_eq_frozenSlope r θ h labels n hnpos hn a p t
    rw [hζ, ← hdial]
    exact dialEval_eq_zero_of_zeroDialForm _ hz _
  refine htel.congr_of_forall_eq ?_ rfl
  intro τ
  rw [hEA τ, hEB τ, hEC]

/-- Reshape closeness to a constant into closeness of the centered function to `0`. -/
noncomputable def eventuallyExpClose_sub_const {f : ℝ → ℝ} {c : ℝ} (h : EventuallyExpClose f c) :
    EventuallyExpClose (fun τ => f τ - c) 0 :=
  ⟨h.rate, h.rate_pos, h.coeff, h.coeff_nonneg, h.start, fun τ hτ => by
    simpa using h.bound τ hτ⟩

/-- Per-coordinate discharge of the α-branch delta gate hypothesis.  For every prior formal
gate variable (layer `< n`), the live actual gate along the dial path is exponentially close
to its frozen reference value: the dial head itself contributes an identically-zero
difference, every other first-layer head saturates to `1` (from separation `hsep`), and each
processed deeper head saturates to its ζ-label (from `hprior`). -/
noncomputable def eventuallyExpClose_dialActualGate_sub_dialFrozenGate
    {m k d r : Nat} (θ : Params (m + 1) k d) (h : Fin k)
    (labels : DeeperHead → TrichotomyLabel) (p : ProbePair d) (t : ℝ) (n : Nat)
    (hsep : ∀ a : Fin k, a ≠ h → 0 < matrixBilin (attentionMatrix θ 0 a) p.1 p.2)
    (hprior : ∀ (q : Nat), 1 ≤ q → q < n → (hq' : q < m + 1) → ∀ (b : Fin k),
      EventuallyExpClose
        (fun τ => actualProbeGate r θ
          (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
          (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2 τ ⟨q, hq'⟩ b)
        (trichotomyToSaturatedLabels r (m + 1) k labels (q + 1) b))
    (x : FormalVar (m + 1) k) (hx : x.1.1 < n) :
    EventuallyExpClose
      (fun τ => dialActualGate r θ h p t τ x - dialFrozenGate r θ h labels p t τ x) 0 := by
  classical
  obtain ⟨l, b⟩ := x
  simp only [dialActualGate, dialFrozenGate, actualProbeGateAssignment,
    satZetaGateAssignment] at hx ⊢
  -- `hx : l.1 < n`.  Now case on the layer.
  by_cases hl0 : l.1 = 0
  · -- First-layer head.
    have hl : l = (⟨0, Nat.succ_pos m⟩ : Fin (m + 1)) := Fin.ext (by simpa using hl0)
    subst hl
    by_cases hbh : b = h
    · subst hbh
      refine EventuallyExpClose.of_forall_eq (fun τ => ?_)
      rw [satZetaGate_zero]
      simp [satGate]
    · have hclose := expCloseTo_actualProbeGate_first_nondial_of_sep (r := r) θ h p t hsep b hbh
      have hee : EventuallyExpClose
          (fun τ => actualProbeGate r θ
            (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
            (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2
            τ ⟨0, Nat.succ_pos m⟩ b) 1 :=
        eventuallyExpClose_of_expCloseTo hclose
      have h0 := eventuallyExpClose_sub_const hee
      refine h0.congr_of_forall_eq (fun τ => ?_) rfl
      rw [satZetaGate_zero]
      simp [satGate, hbh]
  · -- Deeper head.
    have hlpos : 0 < l.1 := Nat.pos_of_ne_zero hl0
    have hprior' := hprior l.1 hlpos hx l.2 b
    have h0 := eventuallyExpClose_sub_const hprior'
    refine h0.congr_of_forall_eq (fun τ => ?_) rfl
    rw [satZetaGate_pos _ _ _ hlpos]

/-- **α-branch delta from honest inputs.**  Assembles `hdelta` from the zero dial form,
first-layer separation, the processed prior-gate closeness facts, and the per-coordinate
polynomial Lipschitz control along the dial path. -/
noncomputable def eventuallyExpClose_actualProbeSlope_frozen_delta_of_sep_prior_lipschitz
    {m k d r : Nat} (θ : Params (m + 1) k d) (h : Fin k)
    (labels : DeeperHead → TrichotomyLabel) (p : ProbePair d) (t : ℝ)
    (n : Nat) (hnpos : 1 ≤ n) (hn : n < m + 1) (a : Fin k)
    (hz : zeroDialForm (phiHeadOfDeeperHead r θ h
      { layer := n + 1, head := (a : Nat) + 1 } labels))
    (hsep : ∀ b : Fin k, b ≠ h → 0 < matrixBilin (attentionMatrix θ 0 b) p.1 p.2)
    (hprior : ∀ (q : Nat), 1 ≤ q → q < n → (hq' : q < m + 1) → ∀ (b : Fin k),
      EventuallyExpClose
        (fun τ => actualProbeGate r θ
          (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
          (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2 τ ⟨q, hq'⟩ b)
        (trichotomyToSaturatedLabels r (m + 1) k labels (q + 1) b))
    (K T : Nat → ℝ)
    (hK : ∀ i : Nat, i < (formalVarsBelow (m + 1) k n).length → 0 ≤ K i)
    (hLip : ∀ i : Nat, (hi : i < (formalVarsBelow (m + 1) k n).length) →
      ∀ τ : ℝ, T i ≤ τ →
        |MvPolynomial.eval
            (formalVarPrefixAssignment (fun τ => dialActualGate r θ h p t τ)
              (fun τ => dialFrozenGate r θ h labels p t τ)
              (formalVarsBelow (m + 1) k n) (i + 1) τ)
            (formalSlope θ
              (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
              (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2 ⟨n, hn⟩ a) -
          MvPolynomial.eval
            (formalVarPrefixAssignment (fun τ => dialActualGate r θ h p t τ)
              (fun τ => dialFrozenGate r θ h labels p t τ)
              (formalVarsBelow (m + 1) k n) i τ)
            (formalSlope θ
              (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
              (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2 ⟨n, hn⟩ a)|
          ≤ K i *
            |dialActualGate r θ h p t τ ((formalVarsBelow (m + 1) k n)[i]'hi) -
              dialFrozenGate r θ h labels p t τ ((formalVarsBelow (m + 1) k n)[i]'hi)|) :
    EventuallyExpClose
      (fun τ =>
        actualProbeSlope r θ
          (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
          (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2
          τ ⟨n, hn⟩ a -
        matrixBilin (attentionMatrix θ ⟨n, hn⟩ a)
          (satZetaPoint θ h
            (trichotomyToSaturatedLabels r (m + 1) k labels) p t n).1
          (satZetaPoint θ h
            (trichotomyToSaturatedLabels r (m + 1) k labels) p t n).2)
      0 :=
  eventuallyExpClose_actualProbeSlope_frozen_delta_of_gate_lipschitz
    θ h labels p t n hnpos hn a hz K T hK
    (fun i hi =>
      eventuallyExpClose_dialActualGate_sub_dialFrozenGate θ h labels p t n hsep hprior
        ((formalVarsBelow (m + 1) k n)[i]'hi)
        ((mem_formalVarsBelow _).mp (List.getElem_mem hi)))
    hLip

/-- **Unconditional α-branch strict slope estimate.**  From the zero dial form, first-layer
separation, the processed prior-gate closeness, and the per-coordinate polynomial Lipschitz
control, the live actual deeper slope is exponentially close to `0`. -/
noncomputable def expCloseTo_actualProbeSlope_zero_of_zeroDialForm_sep_prior_lipschitz
    {m k d r : Nat} (θ : Params (m + 1) k d) (h : Fin k)
    (labels : DeeperHead → TrichotomyLabel) (p : ProbePair d) (t : ℝ)
    (n : Nat) (hnpos : 1 ≤ n) (hn : n < m + 1) (a : Fin k)
    (hz : zeroDialForm (phiHeadOfDeeperHead r θ h
      { layer := n + 1, head := (a : Nat) + 1 } labels))
    (hsep : ∀ b : Fin k, b ≠ h → 0 < matrixBilin (attentionMatrix θ 0 b) p.1 p.2)
    (hprior : ∀ (q : Nat), 1 ≤ q → q < n → (hq' : q < m + 1) → ∀ (b : Fin k),
      EventuallyExpClose
        (fun τ => actualProbeGate r θ
          (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
          (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2 τ ⟨q, hq'⟩ b)
        (trichotomyToSaturatedLabels r (m + 1) k labels (q + 1) b))
    (K T : Nat → ℝ)
    (hK : ∀ i : Nat, i < (formalVarsBelow (m + 1) k n).length → 0 ≤ K i)
    (hLip : ∀ i : Nat, (hi : i < (formalVarsBelow (m + 1) k n).length) →
      ∀ τ : ℝ, T i ≤ τ →
        |MvPolynomial.eval
            (formalVarPrefixAssignment (fun τ => dialActualGate r θ h p t τ)
              (fun τ => dialFrozenGate r θ h labels p t τ)
              (formalVarsBelow (m + 1) k n) (i + 1) τ)
            (formalSlope θ
              (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
              (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2 ⟨n, hn⟩ a) -
          MvPolynomial.eval
            (formalVarPrefixAssignment (fun τ => dialActualGate r θ h p t τ)
              (fun τ => dialFrozenGate r θ h labels p t τ)
              (formalVarsBelow (m + 1) k n) i τ)
            (formalSlope θ
              (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
              (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2 ⟨n, hn⟩ a)|
          ≤ K i *
            |dialActualGate r θ h p t τ ((formalVarsBelow (m + 1) k n)[i]'hi) -
              dialFrozenGate r θ h labels p t τ ((formalVarsBelow (m + 1) k n)[i]'hi)|) :
    ExpCloseTo (fun τ => actualProbeSlope r θ
      (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
      (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2
      τ ⟨n, hn⟩ a) 0 :=
  expCloseTo_actualProbeSlope_zero_of_zeroDialForm_delta θ h labels p t n hnpos hn a
    (eventuallyExpClose_actualProbeSlope_frozen_delta_of_sep_prior_lipschitz
      θ h labels p t n hnpos hn a hz hsep hprior K T hK hLip)
    hz

/-- **The α-branch estimate, discharged.**  From the zero dial form, first-layer separation,
processed prior-gate closeness, and the per-coordinate polynomial Lipschitz control along the
dial path, the rescaled live slope `τ · λ(τ)` tends to `0`.  This is exactly the α-branch
hypothesis consumed by `tendsto_satZetaActualProbePoint`. -/
theorem tendsto_tau_mul_actualProbeSlope_zero_of_zeroDialForm_sep_prior_lipschitz
    {m k d r : Nat} (θ : Params (m + 1) k d) (h : Fin k)
    (labels : DeeperHead → TrichotomyLabel) (p : ProbePair d) (t : ℝ)
    (n : Nat) (hnpos : 1 ≤ n) (hn : n < m + 1) (a : Fin k)
    (hz : zeroDialForm (phiHeadOfDeeperHead r θ h
      { layer := n + 1, head := (a : Nat) + 1 } labels))
    (hsep : ∀ b : Fin k, b ≠ h → 0 < matrixBilin (attentionMatrix θ 0 b) p.1 p.2)
    (hprior : ∀ (q : Nat), 1 ≤ q → q < n → (hq' : q < m + 1) → ∀ (b : Fin k),
      EventuallyExpClose
        (fun τ => actualProbeGate r θ
          (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
          (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2 τ ⟨q, hq'⟩ b)
        (trichotomyToSaturatedLabels r (m + 1) k labels (q + 1) b))
    (K T : Nat → ℝ)
    (hK : ∀ i : Nat, i < (formalVarsBelow (m + 1) k n).length → 0 ≤ K i)
    (hLip : ∀ i : Nat, (hi : i < (formalVarsBelow (m + 1) k n).length) →
      ∀ τ : ℝ, T i ≤ τ →
        |MvPolynomial.eval
            (formalVarPrefixAssignment (fun τ => dialActualGate r θ h p t τ)
              (fun τ => dialFrozenGate r θ h labels p t τ)
              (formalVarsBelow (m + 1) k n) (i + 1) τ)
            (formalSlope θ
              (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
              (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2 ⟨n, hn⟩ a) -
          MvPolynomial.eval
            (formalVarPrefixAssignment (fun τ => dialActualGate r θ h p t τ)
              (fun τ => dialFrozenGate r θ h labels p t τ)
              (formalVarsBelow (m + 1) k n) i τ)
            (formalSlope θ
              (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
              (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2 ⟨n, hn⟩ a)|
          ≤ K i *
            |dialActualGate r θ h p t τ ((formalVarsBelow (m + 1) k n)[i]'hi) -
              dialFrozenGate r θ h labels p t τ ((formalVarsBelow (m + 1) k n)[i]'hi)|) :
    Filter.Tendsto (fun τ => τ * actualProbeSlope r θ
      (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
      (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2
      τ ⟨n, hn⟩ a) Filter.atTop (nhds 0) :=
  tendsto_tau_mul_actualProbeSlope_of_expCloseTo_zero θ h p t n hn a
    (expCloseTo_actualProbeSlope_zero_of_zeroDialForm_sep_prior_lipschitz
      θ h labels p t n hnpos hn a hz hsep hprior K T hK hLip)

/-! ## L2 — discharging `hLip`: the polynomial Lipschitz control is a genuine fact -/

/-- The list of prior formal gate variables is duplicate-free. -/
theorem nodup_formalVarsBelow (L k n : Nat) : (formalVarsBelow L k n).Nodup := by
  classical
  unfold formalVarsBelow
  apply List.Nodup.filter
  rw [List.nodup_flatMap]
  refine ⟨?_, ?_⟩
  · intro l _hl
    exact List.Nodup.map (fun b b' hbb' => by simpa using hbb') (List.nodup_finRange k)
  · exact (List.nodup_finRange L).imp (fun {l l'} hll' => by
      intro x hx hx'
      rw [List.mem_map] at hx hx'
      obtain ⟨b, _, hb⟩ := hx
      obtain ⟨b', _, hb'⟩ := hx'
      exact hll' (congrArg Prod.fst (hb.trans hb'.symm)))

/-- Two consecutive prefix assignments agree away from the single newly-activated
coordinate `vars[i]`. -/
theorem formalVarPrefixAssignment_succ_eq_of_ne {L k : Nat}
    (rho sigma : ℝ → FormalVar L k → ℝ) (vars : List (FormalVar L k))
    (i : Nat) (hi : i < vars.length) (τ : ℝ) {j : FormalVar L k} (hj : j ≠ vars[i]'hi) :
    formalVarPrefixAssignment rho sigma vars (i + 1) τ j =
      formalVarPrefixAssignment rho sigma vars i τ j := by
  by_cases hji : j ∈ vars.take i
  · have hji1 : j ∈ vars.take (i + 1) := by
      rw [List.take_succ_eq_append_getElem hi]; exact List.mem_append_left _ hji
    rw [formalVarPrefixAssignment_of_mem_take _ _ _ _ _ hji1,
      formalVarPrefixAssignment_of_mem_take _ _ _ _ _ hji]
  · have hji1 : j ∉ vars.take (i + 1) := by
      rw [List.take_succ_eq_append_getElem hi]
      simp only [List.mem_append, List.mem_singleton]
      rintro (h | h)
      · exact hji h
      · exact hj h
    rw [formalVarPrefixAssignment_of_not_mem_take _ _ _ _ _ hji1,
      formalVarPrefixAssignment_of_not_mem_take _ _ _ _ _ hji]

/-- The live actual dial gate is bounded (a sigmoid). -/
noncomputable def eventuallyBoundedReal_dialActualGate {m k d : Nat} (r : Nat)
    (θ : Params (m + 1) k d) (h : Fin k) (p : ProbePair d) (t : ℝ)
    (x : FormalVar (m + 1) k) :
    EventuallyBoundedReal (fun τ => dialActualGate r θ h p t τ x) :=
  EventuallyBoundedReal.of_bound 1 zero_le_one 0 (fun τ _ => by
    simp only [dialActualGate, actualProbeGateAssignment]
    rw [actualProbeGate_eq_sig, abs_of_nonneg (sig_pos _).le]
    exact sig_le_one _)

/-- The frozen (saturated) dial gate is bounded: layer-`0` heads saturate to a gate in
`(0,1)` or to `1`, and every deeper head is frozen at its (constant) ζ-label. -/
noncomputable def eventuallyBoundedReal_dialFrozenGate {m k d : Nat} (r : Nat)
    (θ : Params (m + 1) k d) (h : Fin k) (labels : DeeperHead → TrichotomyLabel)
    (p : ProbePair d) (t : ℝ) (x : FormalVar (m + 1) k) :
    EventuallyBoundedReal (fun τ => dialFrozenGate r θ h labels p t τ x) :=
  EventuallyBoundedReal.of_bound
    (1 + |trichotomyToSaturatedLabels r (m + 1) k labels (x.1.1 + 1) x.2|)
    (by positivity) 0 (fun τ _ => by
      by_cases hx0 : x.1.1 = 0
      · have hval : dialFrozenGate r θ h labels p t τ x =
            satGate (dialActualGate r θ h p t τ (0, h)) h x.2 := by
          simp only [dialFrozenGate, satZetaGateAssignment]
          rw [hx0, satZetaGate_zero]
        rw [hval]
        simp only [satGate]
        by_cases hxh : x.2 = h
        · rw [if_pos hxh]
          have hb : |dialActualGate r θ h p t τ (0, h)| ≤ 1 := by
            simp only [dialActualGate, actualProbeGateAssignment]
            rw [actualProbeGate_eq_sig, abs_of_nonneg (sig_pos _).le]
            exact sig_le_one _
          exact le_trans hb (le_add_of_nonneg_right (abs_nonneg _))
        · rw [if_neg hxh, abs_one]
          exact le_add_of_nonneg_right (abs_nonneg _)
      · have hpos : 0 < x.1.1 := Nat.pos_of_ne_zero hx0
        have hval : dialFrozenGate r θ h labels p t τ x =
            trichotomyToSaturatedLabels r (m + 1) k labels (x.1.1 + 1) x.2 := by
          simp only [dialFrozenGate, satZetaGateAssignment]
          rw [satZetaGate_pos _ _ _ hpos]
        rw [hval]
        exact le_add_of_nonneg_left zero_le_one)

/-- The dial path is eventually bounded (it converges to its base point). -/
noncomputable def eventuallyBoundedProbePair_headDialPath {m k d : Nat} (r : Nat)
    (θ : Params (m + 1) k d) (h : Fin k) (p : ProbePair d) (t : ℝ) :
    EventuallyBoundedProbePair
      (fun τ => headDialPath (attentionMatrix θ 0) h (logScale r) p t τ) where
  fst := fun i => EventuallyBoundedReal.ofTendsto
    (((continuous_apply i).comp continuous_fst).continuousAt.tendsto.comp
      (tendsto_headDialPath (attentionMatrix θ 0) h (logScale r) p t))
  snd := fun i => EventuallyBoundedReal.ofTendsto
    (((continuous_apply i).comp continuous_snd).continuousAt.tendsto.comp
      (tendsto_headDialPath (attentionMatrix θ 0) h (logScale r) p t))

/-- **The `hLip` hypothesis of the α-branch, discharged as a genuine fact.**  For the formal
slope polynomial along the dial path, every telescope step is genuinely polynomial-Lipschitz
in its single activated gate coordinate, with an explicit constant `K i` and threshold `T i`.
The constant is the eventually-bounded coefficient-sum slice-Lipschitz constant; the threshold
combines the coordinate-box start with that bound's start. -/
theorem exists_KT_hLip_dialPath {m k d r : Nat} (θ : Params (m + 1) k d) (h : Fin k)
    (labels : DeeperHead → TrichotomyLabel) (p : ProbePair d) (t : ℝ)
    (n : Nat) (hn : n < m + 1) (a : Fin k) :
    ∃ K T : Nat → ℝ,
      (∀ i : Nat, i < (formalVarsBelow (m + 1) k n).length → 0 ≤ K i) ∧
      (∀ i : Nat, (hi : i < (formalVarsBelow (m + 1) k n).length) →
        ∀ τ : ℝ, T i ≤ τ →
          |MvPolynomial.eval
              (formalVarPrefixAssignment (fun τ => dialActualGate r θ h p t τ)
                (fun τ => dialFrozenGate r θ h labels p t τ)
                (formalVarsBelow (m + 1) k n) (i + 1) τ)
              (formalSlope θ
                (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
                (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2 ⟨n, hn⟩ a) -
            MvPolynomial.eval
              (formalVarPrefixAssignment (fun τ => dialActualGate r θ h p t τ)
                (fun τ => dialFrozenGate r θ h labels p t τ)
                (formalVarsBelow (m + 1) k n) i τ)
              (formalSlope θ
                (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
                (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2 ⟨n, hn⟩ a)|
            ≤ K i *
              |dialActualGate r θ h p t τ ((formalVarsBelow (m + 1) k n)[i]'hi) -
                dialFrozenGate r θ h labels p t τ ((formalVarsBelow (m + 1) k n)[i]'hi)|) := by
  classical
  have hpath : EventuallyBoundedProbePair
      (fun τ => headDialPath (attentionMatrix θ 0) h (logScale r) p t τ) :=
    eventuallyBoundedProbePair_headDialPath r θ h p t
  have hActB : ∀ x : FormalVar (m + 1) k,
      EventuallyBoundedReal (fun τ => dialActualGate r θ h p t τ x) :=
    fun x => eventuallyBoundedReal_dialActualGate r θ h p t x
  have hFrozB : ∀ x : FormalVar (m + 1) k,
      EventuallyBoundedReal (fun τ => dialFrozenGate r θ h labels p t τ x) :=
    fun x => eventuallyBoundedReal_dialFrozenGate r θ h labels p t x
  set R : FormalVar (m + 1) k → ℝ := fun x => (hActB x).radius + (hFrozB x).radius with hRdef
  have hR : ∀ j, 0 ≤ R j := fun j => add_nonneg (hActB j).radius_nonneg (hFrozB j).radius_nonneg
  -- A single coordinate-box start dominating every gate's own start.
  set Tbox : ℝ :=
    ∑ x : FormalVar (m + 1) k, (|(hActB x).start| + |(hFrozB x).start|) with hTboxdef
  have hstart_le : ∀ j : FormalVar (m + 1) k,
      (hActB j).start ≤ Tbox ∧ (hFrozB j).start ≤ Tbox := by
    intro j
    have hle : |(hActB j).start| + |(hFrozB j).start| ≤ Tbox :=
      Finset.single_le_sum
        (f := fun x : FormalVar (m + 1) k => |(hActB x).start| + |(hFrozB x).start|)
        (fun x _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ j)
    refine ⟨le_trans (le_trans (le_abs_self _) (le_add_of_nonneg_right (abs_nonneg _))) hle,
      le_trans (le_trans (le_abs_self _) (le_add_of_nonneg_left (abs_nonneg _))) hle⟩
  -- Uniform coordinate box: for all `τ ≥ Tbox` the prefix assignments lie in the `R`-box.
  have hbox : ∀ τ : ℝ, Tbox ≤ τ → ∀ N : Nat, ∀ j : FormalVar (m + 1) k,
      |formalVarPrefixAssignment (fun τ => dialActualGate r θ h p t τ)
          (fun τ => dialFrozenGate r θ h labels p t τ)
          (formalVarsBelow (m + 1) k n) N τ j| ≤ R j := by
    intro τ hτ N j
    by_cases hjn : j ∈ (formalVarsBelow (m + 1) k n).take N
    · rw [formalVarPrefixAssignment_of_mem_take _ _ _ _ _ hjn]
      exact le_trans ((hActB j).bound τ (le_trans (hstart_le j).1 hτ))
        (le_add_of_nonneg_right (hFrozB j).radius_nonneg)
    · rw [formalVarPrefixAssignment_of_not_mem_take _ _ _ _ _ hjn]
      exact le_trans ((hFrozB j).bound τ (le_trans (hstart_le j).2 hτ))
        (le_add_of_nonneg_left (hActB j).radius_nonneg)
  -- The threshold and constant for each activated coordinate come from the τ-uniform
  -- slice-Lipschitz constant `eventuallyBoundedReal_realFormalSliceLip_of_path`.
  refine ⟨fun i => if hi : i < (formalVarsBelow (m + 1) k n).length then
      (eventuallyBoundedReal_realFormalSliceLip_of_path θ ⟨n, hn⟩ a
        ((formalVarsBelow (m + 1) k n)[i]'hi) R hR hpath).radius else 0,
    fun i => if hi : i < (formalVarsBelow (m + 1) k n).length then
      max Tbox (eventuallyBoundedReal_realFormalSliceLip_of_path θ ⟨n, hn⟩ a
        ((formalVarsBelow (m + 1) k n)[i]'hi) R hR hpath).start else 0, ?_, ?_⟩
  · intro i hi
    simp only [dif_pos hi]
    exact (eventuallyBoundedReal_realFormalSliceLip_of_path θ ⟨n, hn⟩ a
      ((formalVarsBelow (m + 1) k n)[i]'hi) R hR hpath).radius_nonneg
  · intro i hi τ hτ
    simp only [dif_pos hi]
    simp only [dif_pos hi] at hτ
    set hc := eventuallyBoundedReal_realFormalSliceLip_of_path θ ⟨n, hn⟩ a
      ((formalVarsBelow (m + 1) k n)[i]'hi) R hR hpath with hcdef
    set P : FormalPoly (m + 1) k :=
      formalSlope θ
        (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
        (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2 ⟨n, hn⟩ a with hP
    set X : FormalVar (m + 1) k → ℝ :=
      formalVarPrefixAssignment (fun τ => dialActualGate r θ h p t τ)
        (fun τ => dialFrozenGate r θ h labels p t τ) (formalVarsBelow (m + 1) k n) (i + 1) τ
      with hX
    set Y : FormalVar (m + 1) k → ℝ :=
      formalVarPrefixAssignment (fun τ => dialActualGate r θ h p t τ)
        (fun τ => dialFrozenGate r θ h labels p t τ) (formalVarsBelow (m + 1) k n) i τ
      with hY
    have hτ0 : Tbox ≤ τ := le_trans (le_max_left _ _) hτ
    have hτs : hc.start ≤ τ := le_trans (le_max_right _ _) hτ
    have hx : ∀ j, |X j| ≤ R j := fun j => hbox τ hτ0 (i + 1) j
    have hy : ∀ j, |Y j| ≤ R j := fun j => hbox τ hτ0 i j
    have heq : ∀ j, j ≠ (formalVarsBelow (m + 1) k n)[i]'hi → X j = Y j := by
      intro j hj
      exact formalVarPrefixAssignment_succ_eq_of_ne _ _ _ i hi τ hj
    have hpoly :=
      eval_sub_eval_abs_le_realSliceLip P ((formalVarsBelow (m + 1) k n)[i]'hi) R X Y hR hx hy heq
    have hLle : realSliceLip P ((formalVarsBelow (m + 1) k n)[i]'hi) R ≤ hc.radius := by
      have hb := hc.bound τ hτs
      rw [← hP] at hb
      rw [abs_of_nonneg (realSliceLip_nonneg P _ R hR)] at hb
      exact hb
    have hXc : X ((formalVarsBelow (m + 1) k n)[i]'hi) =
        dialActualGate r θ h p t τ ((formalVarsBelow (m + 1) k n)[i]'hi) := by
      rw [hX]
      apply formalVarPrefixAssignment_of_mem_take
      rw [List.take_succ_eq_append_getElem hi]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    have hYc : Y ((formalVarsBelow (m + 1) k n)[i]'hi) =
        dialFrozenGate r θ h labels p t τ ((formalVarsBelow (m + 1) k n)[i]'hi) := by
      rw [hY]
      apply formalVarPrefixAssignment_of_not_mem_take
      exact getElem_not_mem_take_of_nodup (nodup_formalVarsBelow (m + 1) k n) hi
    calc
      |MvPolynomial.eval X P - MvPolynomial.eval Y P|
          ≤ realSliceLip P ((formalVarsBelow (m + 1) k n)[i]'hi) R *
              |X ((formalVarsBelow (m + 1) k n)[i]'hi) -
                Y ((formalVarsBelow (m + 1) k n)[i]'hi)| := hpoly
      _ ≤ hc.radius *
            |X ((formalVarsBelow (m + 1) k n)[i]'hi) -
              Y ((formalVarsBelow (m + 1) k n)[i]'hi)| :=
        mul_le_mul_of_nonneg_right hLle (abs_nonneg _)
      _ = hc.radius *
            |dialActualGate r θ h p t τ ((formalVarsBelow (m + 1) k n)[i]'hi) -
              dialFrozenGate r θ h labels p t τ ((formalVarsBelow (m + 1) k n)[i]'hi)| := by
            rw [hXc, hYc]

/-- **Unconditional α-branch strict slope estimate.**  From the zero dial form, first-layer
separation, and the processed prior-gate closeness alone — the per-coordinate polynomial
Lipschitz control is now supplied internally by `exists_KT_hLip_dialPath`. -/
noncomputable def expCloseTo_actualProbeSlope_zero_of_zeroDialForm_sep
    {m k d r : Nat} (θ : Params (m + 1) k d) (h : Fin k)
    (labels : DeeperHead → TrichotomyLabel) (p : ProbePair d) (t : ℝ)
    (n : Nat) (hnpos : 1 ≤ n) (hn : n < m + 1) (a : Fin k)
    (hz : zeroDialForm (phiHeadOfDeeperHead r θ h
      { layer := n + 1, head := (a : Nat) + 1 } labels))
    (hsep : ∀ b : Fin k, b ≠ h → 0 < matrixBilin (attentionMatrix θ 0 b) p.1 p.2)
    (hprior : ∀ (q : Nat), 1 ≤ q → q < n → (hq' : q < m + 1) → ∀ (b : Fin k),
      EventuallyExpClose
        (fun τ => actualProbeGate r θ
          (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
          (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2 τ ⟨q, hq'⟩ b)
        (trichotomyToSaturatedLabels r (m + 1) k labels (q + 1) b)) :
    ExpCloseTo (fun τ => actualProbeSlope r θ
      (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
      (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2
      τ ⟨n, hn⟩ a) 0 := by
  classical
  obtain ⟨K, T, hK, hLip⟩ := exists_KT_hLip_dialPath θ h labels p t n hn a
  exact expCloseTo_actualProbeSlope_zero_of_zeroDialForm_sep_prior_lipschitz
    θ h labels p t n hnpos hn a hz hsep hprior K T hK hLip

/-- **The α-branch estimate, fully discharged.**  From the zero dial form, first-layer
separation, and processed prior-gate closeness, the rescaled live slope `τ · λ(τ)` tends to
`0`.  No Lipschitz hypothesis: it is proved internally. -/
theorem tendsto_tau_mul_actualProbeSlope_zero_of_zeroDialForm_sep
    {m k d r : Nat} (θ : Params (m + 1) k d) (h : Fin k)
    (labels : DeeperHead → TrichotomyLabel) (p : ProbePair d) (t : ℝ)
    (n : Nat) (hnpos : 1 ≤ n) (hn : n < m + 1) (a : Fin k)
    (hz : zeroDialForm (phiHeadOfDeeperHead r θ h
      { layer := n + 1, head := (a : Nat) + 1 } labels))
    (hsep : ∀ b : Fin k, b ≠ h → 0 < matrixBilin (attentionMatrix θ 0 b) p.1 p.2)
    (hprior : ∀ (q : Nat), 1 ≤ q → q < n → (hq' : q < m + 1) → ∀ (b : Fin k),
      EventuallyExpClose
        (fun τ => actualProbeGate r θ
          (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
          (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2 τ ⟨q, hq'⟩ b)
        (trichotomyToSaturatedLabels r (m + 1) k labels (q + 1) b)) :
    Filter.Tendsto (fun τ => τ * actualProbeSlope r θ
      (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
      (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2
      τ ⟨n, hn⟩ a) Filter.atTop (nhds 0) :=
  tendsto_tau_mul_actualProbeSlope_of_expCloseTo_zero θ h p t n hn a
    (expCloseTo_actualProbeSlope_zero_of_zeroDialForm_sep
      θ h labels p t n hnpos hn a hz hsep hprior)


/-- Actual-gate alpha estimate from an exponentially small actual slope.  This is the
rate-strengthened form consumed after the zero-branch error estimate is proved. -/
noncomputable def expCloseTo_actualProbeGate_alpha_of_actualProbeSlope_expCloseTo_zero
    {m k d r : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (p : ProbePair d) (t : ℝ)
    (n : Nat) (hn : n < m + 1) (a : Fin k)
    (hstrict : ExpCloseTo (fun τ => actualProbeSlope r θ
      (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
      (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2
      τ ⟨n, hn⟩ a) 0) :
    ExpCloseTo (fun τ => actualProbeGate r θ
      (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
      (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2
      τ ⟨n, hn⟩ a) (alpha r) := by
  exact expCloseTo_congr (fun τ => by rw [actualProbeGate_eq_sig])
    (expCloseTo_gate_alpha_of_expCloseTo_slope_zero r hstrict)

/-- Current-region alpha successor estimate from pointwise strict actual-slope
estimates. -/
theorem DialEstimate.estimate_alpha_getElem_currentRegion_of_actualProbeSlope_expCloseTo_zero
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {baseRegion currentRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n q : Nat} {a : Fin k}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    (hInv : ProcessingInvariantStatement (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) baseRegion currentRegion
      (deeperHeadOrder (m + 1) k) n labels)
    (hqpos : 1 ≤ q) (hq : q < m + 1)
    (hcurrent : (deeperHeadOrder (m + 1) k)[n] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    (hstrict : ∀ x ∈ currentRegion,
      ExpCloseTo (fun τ => actualProbeSlope r θ
        (headDialPath (attentionMatrix θ 0) head (logScale r) x.1 x.2 τ).1
        (headDialPath (attentionMatrix θ 0) head (logScale r) x.1 x.2 τ).2
        τ ⟨q, hq⟩ a) 0) :
    (dialPredicatesWithEstimate r θ head).Estimate
      (deeperHeadOrder (m + 1) k) (n + 1) currentRegion
      (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) TrichotomyLabel.alpha) := by
  refine DialEstimate.estimate_alpha_getElem
    (r := r) (θ := θ) (head := head) (currentRegion := currentRegion)
    (nextRegion := currentRegion) (labels := labels) (hn := hn)
    hqpos hq a hcurrent (fun _ hx => hx) hInv.estimate ?_
  intro x hx
  exact expCloseTo_actualProbeGate_alpha_of_actualProbeSlope_expCloseTo_zero
    θ head x.1 x.2 q hq a (hstrict x hx)

/-- Current-region alpha successor estimate from a zero dial form and the explicit
live-minus-frozen delta estimate. -/
theorem DialEstimate.estimate_alpha_getElem_currentRegion_of_zeroDialForm_delta
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {baseRegion currentRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n q : Nat} {a : Fin k}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    (hInv : ProcessingInvariantStatement (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) baseRegion currentRegion
      (deeperHeadOrder (m + 1) k) n labels)
    (hqpos : 1 ≤ q) (hq : q < m + 1)
    (hcurrent : (deeperHeadOrder (m + 1) k)[n] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    (hz : zeroDialForm
      (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels))
    (hdelta : ∀ x ∈ currentRegion,
      EventuallyExpClose
        (fun τ => actualProbeSlope r θ
          (headDialPath (attentionMatrix θ 0) head (logScale r) x.1 x.2 τ).1
          (headDialPath (attentionMatrix θ 0) head (logScale r) x.1 x.2 τ).2
          τ ⟨q, hq⟩ a -
          matrixBilin (attentionMatrix θ ⟨q, hq⟩ a)
            (satZetaPoint θ head
              (trichotomyToSaturatedLabels r (m + 1) k labels) x.1 x.2 q).1
            (satZetaPoint θ head
              (trichotomyToSaturatedLabels r (m + 1) k labels) x.1 x.2 q).2)
        0) :
    (dialPredicatesWithEstimate r θ head).Estimate
      (deeperHeadOrder (m + 1) k) (n + 1) currentRegion
      (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) TrichotomyLabel.alpha) := by
  refine DialEstimate.estimate_alpha_getElem_currentRegion_of_actualProbeSlope_expCloseTo_zero
    (r := r) (θ := θ) (head := head) (baseRegion := baseRegion)
    (currentRegion := currentRegion) (labels := labels) (hn := hn)
    hInv hqpos hq hcurrent ?_
  intro x hx
  have hz_current : zeroDialForm
      (phiHeadOfDeeperHead r θ head
        ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead) labels) := by
    simpa [hcurrent] using hz
  exact expCloseTo_actualProbeSlope_zero_of_zeroDialForm_delta
    θ head labels x.1 x.2 q hqpos hq a (hdelta x hx) hz_current

/-- Prefix zero-form plus a strict slope-rate estimate gives both the already-proved
unscaled zero slope and the remaining rescaled alpha estimate.  The strict-rate input is
the target of the remaining zero-branch error propagation, not a restatement of
`τ * actualProbeSlope -> 0`. -/
theorem tendsto_actualProbeSlope_zero_and_tau_mul_of_zeroDialForm_prefix {m k d r : Nat}
    (θ : Params (m + 1) k d) (h : Fin k)
    (labels : DeeperHead → TrichotomyLabel) (p : ProbePair d) (t : ℝ)
    (ht_pos : 0 < t) (ht_lt_one : t < 1)
    (hq : firstHeadSlope (attentionMatrix θ 0) h p = 0)
    (hpi : firstHeadPi (attentionMatrix θ 0) h p ≠ 0)
    (hsep : ∀ a : Fin k, a ≠ h → 0 < matrixBilin (attentionMatrix θ 0 a) p.1 p.2)
    (n : Nat) (hnpos : 1 ≤ n) (hn : n < m + 1) (a : Fin k)
    (hlabel : ∀ (q : Nat), 1 ≤ q → q < n → (hq' : q < m + 1) → ∀ (b : Fin k),
      (trichotomyToSaturatedLabels r (m + 1) k labels (q + 1) b = 1 ∧
        0 < matrixBilin (attentionMatrix θ ⟨q, hq'⟩ b)
          (satZetaPoint θ h (trichotomyToSaturatedLabels r (m + 1) k labels) p t q).1
          (satZetaPoint θ h (trichotomyToSaturatedLabels r (m + 1) k labels) p t q).2)
      ∨ (trichotomyToSaturatedLabels r (m + 1) k labels (q + 1) b = 0 ∧
        matrixBilin (attentionMatrix θ ⟨q, hq'⟩ b)
          (satZetaPoint θ h (trichotomyToSaturatedLabels r (m + 1) k labels) p t q).1
          (satZetaPoint θ h (trichotomyToSaturatedLabels r (m + 1) k labels) p t q).2 < 0)
      ∨ (trichotomyToSaturatedLabels r (m + 1) k labels (q + 1) b = alpha r ∧
        Tendsto (fun τ => τ * actualProbeSlope r θ
          (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
          (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2
          τ ⟨q, hq'⟩ b) atTop (𝓝 0)))
    (hz : zeroDialForm (phiHeadOfDeeperHead r θ h
      { layer := n + 1, head := (a : Nat) + 1 } labels))
    (hstrict : ExpCloseTo (fun τ => actualProbeSlope r θ
      (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
      (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2
      τ ⟨n, hn⟩ a) 0) :
    Tendsto (fun τ => actualProbeSlope r θ
        (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
        (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2
        τ ⟨n, hn⟩ a) atTop (𝓝 0)
      ∧ Tendsto (fun τ => τ * actualProbeSlope r θ
        (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
        (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2
        τ ⟨n, hn⟩ a) atTop (𝓝 0) := by
  exact
    ⟨tendsto_actualProbeSlope_zero_of_zeroDialForm_prefix θ h labels p t ht_pos ht_lt_one
        hq hpi hsep n hnpos hn a hlabel hz,
      tendsto_tau_mul_actualProbeSlope_of_expCloseTo_zero θ h p t n hn a hstrict⟩

/-- Convert the processed lower-layer portion of an honest-estimate invariant into
the prefix `hlabel` premise consumed by `tendsto_satZetaActualProbePoint_prefix`,
isolating the α-branch rate estimate as an explicit hypothesis. -/
theorem ProcessingInvariantStatement.satZeta_hlabel_prefix_of_alpha_estimate
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {baseRegion currentRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {idx q : Nat} {a : Fin k}
    (hInv : ProcessingInvariantStatement (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) baseRegion currentRegion
      (deeperHeadOrder (m + 1) k) idx labels)
    (hidx : idx < (deeperHeadOrder (m + 1) k).length)
    (hcurrent :
      (deeperHeadOrder (m + 1) k)[idx] =
        ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    {p : ProbePair d} {t : ℝ} (hx : (p, t) ∈ currentRegion)
    (halpha : ∀ (q' : Nat), 1 ≤ q' → q' < q → (hq' : q' < m + 1) →
      ∀ (b : Fin k),
        labels ({ layer := q' + 1, head := (b : Nat) + 1 } : DeeperHead) =
            TrichotomyLabel.alpha →
          Tendsto (fun τ => τ * actualProbeSlope r θ
            (headDialPath (attentionMatrix θ 0) head (logScale r) p t τ).1
            (headDialPath (attentionMatrix θ 0) head (logScale r) p t τ).2
            τ ⟨q', hq'⟩ b) atTop (𝓝 0)) :
    ∀ (q' : Nat), 1 ≤ q' → q' < q → ∀ (hq' : q' < m + 1) (b : Fin k),
      (trichotomyToSaturatedLabels r (m + 1) k labels (q' + 1) b = 1 ∧
        0 < matrixBilin (attentionMatrix θ ⟨q', hq'⟩ b)
          (satZetaPoint θ head (trichotomyToSaturatedLabels r (m + 1) k labels) p t q').1
          (satZetaPoint θ head (trichotomyToSaturatedLabels r (m + 1) k labels) p t q').2)
      ∨ (trichotomyToSaturatedLabels r (m + 1) k labels (q' + 1) b = 0 ∧
        matrixBilin (attentionMatrix θ ⟨q', hq'⟩ b)
          (satZetaPoint θ head (trichotomyToSaturatedLabels r (m + 1) k labels) p t q').1
          (satZetaPoint θ head (trichotomyToSaturatedLabels r (m + 1) k labels) p t q').2 < 0)
      ∨ (trichotomyToSaturatedLabels r (m + 1) k labels (q' + 1) b = alpha r ∧
        Tendsto (fun τ => τ * actualProbeSlope r θ
          (headDialPath (attentionMatrix θ 0) head (logScale r) p t τ).1
          (headDialPath (attentionMatrix θ 0) head (logScale r) p t τ).2
          τ ⟨q', hq'⟩ b) atTop (𝓝 0)) := by
  intro q' hq'pos hlt hq' b
  have hmem :
      ({ layer := q' + 1, head := (b : Nat) + 1 } : DeeperHead) ∈
        processedPrefix (deeperHeadOrder (m + 1) k) idx :=
    succ_head_mem_processedPrefix_of_layer_lt_getElem_deeperHeadOrder
      hidx hcurrent hq'pos hq' hlt b
  have hdial :=
    dialEval_phiHeadOfDeeperHead_succ_eq_frozenSlope r θ head labels
      q' hq'pos hq' b p t
  rcases hInv.dialEval_label_cases_withEstimate hmem hx with
    ⟨hlabel, hpos⟩ | ⟨hlabel, hneg⟩ | ⟨hlabel, _hzero⟩
  · left
    exact
      ⟨trichotomyToSaturatedLabels_eq_one_of_label_one r (m + 1) k
          labels (q' + 1) b hlabel,
        by simpa [hdial] using hpos⟩
  · right
    left
    exact
      ⟨trichotomyToSaturatedLabels_eq_zero_of_label_zero r (m + 1) k
          labels (q' + 1) b hlabel,
        by simpa [hdial] using hneg⟩
  · right
    right
    exact
      ⟨trichotomyToSaturatedLabels_eq_alpha_of_label_alpha r (m + 1) k
          labels (q' + 1) b hlabel,
        halpha q' hq'pos hlt hq' b hlabel⟩

/-- Processed lower-layer gates from the current invariant, repackaged in the
data-carrying exponential-close form. -/
noncomputable def ProcessingInvariantStatement.priorGate_eventuallyExpClose_of_current_getElem
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {baseRegion currentRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {idx q : Nat} {a : Fin k}
    (hInv : ProcessingInvariantStatement (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) baseRegion currentRegion
      (deeperHeadOrder (m + 1) k) idx labels)
    (hidx : idx < (deeperHeadOrder (m + 1) k).length)
    (hcurrent :
      (deeperHeadOrder (m + 1) k)[idx] =
        ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead)) :
    ∀ x ∈ currentRegion, ∀ q' : Nat, 1 ≤ q' → q' < q →
      (hq' : q' < m + 1) → ∀ b : Fin k,
        EventuallyExpClose
          (fun τ => actualProbeGate r θ
            (headDialPath (attentionMatrix θ 0) head (logScale r) x.1 x.2 τ).1
            (headDialPath (attentionMatrix θ 0) head (logScale r) x.1 x.2 τ).2
            τ ⟨q', hq'⟩ b)
          (trichotomyToSaturatedLabels r (m + 1) k labels (q' + 1) b) := by
  intro x hx q' hq'pos hlt hq' b
  have hmem :
      ({ layer := q' + 1, head := (b : Nat) + 1 } : DeeperHead) ∈
        processedPrefix (deeperHeadOrder (m + 1) k) idx :=
    succ_head_mem_processedPrefix_of_layer_lt_getElem_deeperHeadOrder
      hidx hcurrent hq'pos hq' hlt b
  exact eventuallyExpClose_of_expCloseTo
    (hInv.estimate.gate hq'pos hq' b hmem x hx)

/-- Pointwise current-gate estimate for the positive branch.  The lower-layer
processed invariant supplies the prefix ζ-limit; positivity of the current dial
form identifies the limiting frozen slope as positive, so the live gate
exponentially saturates to `1`. -/
theorem expCloseTo_actualProbeGate_one_of_dialEval_pos_prefix
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {baseRegion currentRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {idx q : Nat} {a : Fin k}
    (hInv : ProcessingInvariantStatement (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) baseRegion currentRegion
      (deeperHeadOrder (m + 1) k) idx labels)
    (hidx : idx < (deeperHeadOrder (m + 1) k).length)
    (hqpos : 1 ≤ q) (hq : q < m + 1)
    (hcurrent : (deeperHeadOrder (m + 1) k)[idx] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    {p : ProbePair d} {t : ℝ} (hx : (p, t) ∈ currentRegion)
    (ht_pos : 0 < t) (ht_lt_one : t < 1)
    (hfirst : firstHeadSlope (attentionMatrix θ 0) head p = 0)
    (hpi : firstHeadPi (attentionMatrix θ 0) head p ≠ 0)
    (hsep : ∀ b : Fin k, b ≠ head →
      0 < matrixBilin (attentionMatrix θ 0 b) p.1 p.2)
    (halpha : ∀ (q' : Nat), 1 ≤ q' → q' < q → (hq' : q' < m + 1) →
      ∀ (b : Fin k),
        labels ({ layer := q' + 1, head := (b : Nat) + 1 } : DeeperHead) =
            TrichotomyLabel.alpha →
          Tendsto (fun τ => τ * actualProbeSlope r θ
            (headDialPath (attentionMatrix θ 0) head (logScale r) p t τ).1
            (headDialPath (attentionMatrix θ 0) head (logScale r) p t τ).2
            τ ⟨q', hq'⟩ b) atTop (𝓝 0))
    (hpos : 0 < dialEval
      (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[idx]) labels) (p, t)) :
    ExpCloseTo (fun τ => actualProbeGate r θ
      (headDialPath (attentionMatrix θ 0) head (logScale r) p t τ).1
      (headDialPath (attentionMatrix θ 0) head (logScale r) p t τ).2
      τ ⟨q, hq⟩ a) 1 := by
  let ζ := trichotomyToSaturatedLabels r (m + 1) k labels
  have hlabel :=
    hInv.satZeta_hlabel_prefix_of_alpha_estimate
      hidx hcurrent hx halpha
  have hpt := tendsto_satZetaActualProbePoint_prefix r θ head ζ p t
    ht_pos ht_lt_one hfirst hpi hsep q (Nat.le_of_lt hq) hlabel
  have hslope := tendsto_actualProbeSlope_of_tendsto_satZetaPoint r θ head ζ p t
    q hq a hpt
  have hdial :=
    dialEval_phiHeadOfDeeperHead_succ_eq_frozenSlope r θ head labels q hqpos hq a p t
  have hpos_current :
      0 < dialEval
        (phiHeadOfDeeperHead r θ head
          ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead) labels) (p, t) := by
    simpa [hcurrent] using hpos
  have hfrozen_pos :
      0 < matrixBilin (attentionMatrix θ ⟨q, hq⟩ a)
        (satZetaPoint θ head ζ p t q).1
        (satZetaPoint θ head ζ p t q).2 := by
    simpa [ζ, hdial] using hpos_current
  exact expCloseTo_congr (fun τ => by rw [actualProbeGate_eq_sig])
    (expCloseTo_sig_of_tendsto_pos (b := logScale r) hfrozen_pos hslope)

/-- Pointwise current-gate estimate for the negative branch.  The lower-layer
processed invariant supplies the prefix ζ-limit; negativity of the current dial
form identifies the limiting frozen slope as negative, so the live gate
exponentially saturates to `0`. -/
theorem expCloseTo_actualProbeGate_zero_of_dialEval_neg_prefix
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {baseRegion currentRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {idx q : Nat} {a : Fin k}
    (hInv : ProcessingInvariantStatement (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) baseRegion currentRegion
      (deeperHeadOrder (m + 1) k) idx labels)
    (hidx : idx < (deeperHeadOrder (m + 1) k).length)
    (hqpos : 1 ≤ q) (hq : q < m + 1)
    (hcurrent : (deeperHeadOrder (m + 1) k)[idx] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    {p : ProbePair d} {t : ℝ} (hx : (p, t) ∈ currentRegion)
    (ht_pos : 0 < t) (ht_lt_one : t < 1)
    (hfirst : firstHeadSlope (attentionMatrix θ 0) head p = 0)
    (hpi : firstHeadPi (attentionMatrix θ 0) head p ≠ 0)
    (hsep : ∀ b : Fin k, b ≠ head →
      0 < matrixBilin (attentionMatrix θ 0 b) p.1 p.2)
    (halpha : ∀ (q' : Nat), 1 ≤ q' → q' < q → (hq' : q' < m + 1) →
      ∀ (b : Fin k),
        labels ({ layer := q' + 1, head := (b : Nat) + 1 } : DeeperHead) =
            TrichotomyLabel.alpha →
          Tendsto (fun τ => τ * actualProbeSlope r θ
            (headDialPath (attentionMatrix θ 0) head (logScale r) p t τ).1
            (headDialPath (attentionMatrix θ 0) head (logScale r) p t τ).2
            τ ⟨q', hq'⟩ b) atTop (𝓝 0))
    (hneg : dialEval
      (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[idx]) labels) (p, t) < 0) :
    ExpCloseTo (fun τ => actualProbeGate r θ
      (headDialPath (attentionMatrix θ 0) head (logScale r) p t τ).1
      (headDialPath (attentionMatrix θ 0) head (logScale r) p t τ).2
      τ ⟨q, hq⟩ a) 0 := by
  let ζ := trichotomyToSaturatedLabels r (m + 1) k labels
  have hlabel :=
    hInv.satZeta_hlabel_prefix_of_alpha_estimate
      hidx hcurrent hx halpha
  have hpt := tendsto_satZetaActualProbePoint_prefix r θ head ζ p t
    ht_pos ht_lt_one hfirst hpi hsep q (Nat.le_of_lt hq) hlabel
  have hslope := tendsto_actualProbeSlope_of_tendsto_satZetaPoint r θ head ζ p t
    q hq a hpt
  have hdial :=
    dialEval_phiHeadOfDeeperHead_succ_eq_frozenSlope r θ head labels q hqpos hq a p t
  have hneg_current :
      dialEval
        (phiHeadOfDeeperHead r θ head
          ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead) labels) (p, t) < 0 := by
    simpa [hcurrent] using hneg
  have hfrozen_neg :
      matrixBilin (attentionMatrix θ ⟨q, hq⟩ a)
        (satZetaPoint θ head ζ p t q).1
        (satZetaPoint θ head ζ p t q).2 < 0 := by
    simpa [ζ, hdial] using hneg_current
  exact expCloseTo_congr (fun τ => by rw [actualProbeGate_eq_sig])
    (expCloseTo_sig_of_tendsto_neg (b := logScale r) hfrozen_neg hslope)

/-- Honest successor estimate for the concrete positive branch.  The branch
component supplies a positive current dial value at every point, and the
pointwise prefix gate theorem supplies the current-gate estimate consumed by
`DialEstimate.estimate_one_getElem`. -/
theorem DialEstimate.estimate_one_getElem_positiveBranchComponent
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {baseRegion currentRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n q : Nat} {a : Fin k}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    (hInv : ProcessingInvariantStatement (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) baseRegion currentRegion
      (deeperHeadOrder (m + 1) k) n labels)
    (hqpos : 1 ≤ q) (hq : q < m + 1)
    (hcurrent : (deeperHeadOrder (m + 1) k)[n] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    {x0 : ProbePair d × ℝ}
    (hx0_current : x0 ∈ currentRegion)
    (hx0_pos :
      0 < dialEval
        (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels) x0)
    (hdet : (attentionMatrix θ 0 head).det ≠ 0)
    (ht_pos : ∀ x ∈
      positiveBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0,
        0 < x.2)
    (ht_lt_one : ∀ x ∈
      positiveBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0,
        x.2 < 1)
    (hfirst : ∀ x ∈
      positiveBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0,
        firstHeadSlope (attentionMatrix θ 0) head x.1 = 0)
    (hpi : ∀ x ∈
      positiveBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0,
        firstHeadPi (attentionMatrix θ 0) head x.1 ≠ 0)
    (hsep : ∀ x ∈
      positiveBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0,
        ∀ b : Fin k, b ≠ head →
          0 < matrixBilin (attentionMatrix θ 0 b) x.1.1 x.1.2)
    (halpha : ∀ x ∈
      positiveBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0,
        ∀ (q' : Nat), 1 ≤ q' → q' < q → (hq' : q' < m + 1) →
          ∀ (b : Fin k),
            labels ({ layer := q' + 1, head := (b : Nat) + 1 } : DeeperHead) =
                TrichotomyLabel.alpha →
              Tendsto (fun τ => τ * actualProbeSlope r θ
                (headDialPath (attentionMatrix θ 0) head (logScale r) x.1 x.2 τ).1
                (headDialPath (attentionMatrix θ 0) head (logScale r) x.1 x.2 τ).2
                τ ⟨q', hq'⟩ b) atTop (𝓝 0)) :
    (dialPredicatesWithEstimate r θ head).Estimate
      (deeperHeadOrder (m + 1) k) (n + 1)
      (positiveBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0)
      (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) TrichotomyLabel.one) := by
  let nextRegion : Set (ProbePair d × ℝ) :=
    positiveBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0
  let Φ : QuadraticDialForm d :=
    phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels
  let nonzeroLocus : Set (ProbePair d × ℝ) := {x | dialEval Φ x ≠ 0}
  have hnext :
      nextRegion = connectedComponentIn (currentRegion ∩ nonzeroLocus) x0 := by
    rfl
  have hx0_posΦ : 0 < dialEval Φ x0 := by
    simpa [Φ] using hx0_pos
  have hx0_nonzero : dialEval Φ x0 ≠ 0 := ne_of_gt hx0_posΦ
  have hx0_open : x0 ∈ currentRegion ∩ nonzeroLocus := ⟨hx0_current, hx0_nonzero⟩
  have hpos_on : ∀ x ∈ nextRegion, 0 < dialEval Φ x := by
    rw [hnext]
    apply positiveOn_of_preconnected_of_nonzero isPreconnected_connectedComponentIn
      (continuous_dialEval Φ)
    · intro x hx
      exact (connectedComponentIn_subset (currentRegion ∩ nonzeroLocus) x0 hx).2
    · exact ⟨x0, mem_connectedComponentIn hx0_open, hx0_posΦ⟩
  have htop := positiveBranchComponent_getElem_topology_withEstimate
    (r := r) (θ := θ) (head := head) (hn := hn) hInv hx0_current hx0_pos hdet
  refine DialEstimate.estimate_one_getElem
    (r := r) (θ := θ) (head := head) (currentRegion := currentRegion)
    (nextRegion := nextRegion) (labels := labels) (hn := hn)
    hqpos hq a hcurrent htop.2.2.2 hInv.estimate ?_
  intro x hx
  rcases x with ⟨p, t⟩
  exact expCloseTo_actualProbeGate_one_of_dialEval_pos_prefix
    (r := r) (θ := θ) (head := head) (baseRegion := baseRegion)
    (currentRegion := currentRegion) (labels := labels) (idx := n) (q := q) (a := a)
    hInv hn hqpos hq hcurrent (htop.2.2.2 hx)
    (ht_pos (p, t) hx) (ht_lt_one (p, t) hx)
    (hfirst (p, t) hx) (hpi (p, t) hx) (hsep (p, t) hx)
    (halpha (p, t) hx) (by simpa [Φ] using hpos_on (p, t) hx)

/-- Honest successor estimate for the concrete negative branch.  The branch
component supplies a negative current dial value at every point, and the
pointwise prefix gate theorem supplies the current-gate estimate consumed by
`DialEstimate.estimate_zero_getElem`. -/
theorem DialEstimate.estimate_zero_getElem_negativeBranchComponent
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {baseRegion currentRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n q : Nat} {a : Fin k}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    (hInv : ProcessingInvariantStatement (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) baseRegion currentRegion
      (deeperHeadOrder (m + 1) k) n labels)
    (hqpos : 1 ≤ q) (hq : q < m + 1)
    (hcurrent : (deeperHeadOrder (m + 1) k)[n] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    {x0 : ProbePair d × ℝ}
    (hx0_current : x0 ∈ currentRegion)
    (hx0_neg :
      dialEval
        (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels) x0 < 0)
    (hdet : (attentionMatrix θ 0 head).det ≠ 0)
    (ht_pos : ∀ x ∈
      negativeBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0,
        0 < x.2)
    (ht_lt_one : ∀ x ∈
      negativeBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0,
        x.2 < 1)
    (hfirst : ∀ x ∈
      negativeBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0,
        firstHeadSlope (attentionMatrix θ 0) head x.1 = 0)
    (hpi : ∀ x ∈
      negativeBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0,
        firstHeadPi (attentionMatrix θ 0) head x.1 ≠ 0)
    (hsep : ∀ x ∈
      negativeBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0,
        ∀ b : Fin k, b ≠ head →
          0 < matrixBilin (attentionMatrix θ 0 b) x.1.1 x.1.2)
    (halpha : ∀ x ∈
      negativeBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0,
        ∀ (q' : Nat), 1 ≤ q' → q' < q → (hq' : q' < m + 1) →
          ∀ (b : Fin k),
            labels ({ layer := q' + 1, head := (b : Nat) + 1 } : DeeperHead) =
                TrichotomyLabel.alpha →
              Tendsto (fun τ => τ * actualProbeSlope r θ
                (headDialPath (attentionMatrix θ 0) head (logScale r) x.1 x.2 τ).1
                (headDialPath (attentionMatrix θ 0) head (logScale r) x.1 x.2 τ).2
                τ ⟨q', hq'⟩ b) atTop (𝓝 0)) :
    (dialPredicatesWithEstimate r θ head).Estimate
      (deeperHeadOrder (m + 1) k) (n + 1)
      (negativeBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0)
      (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) TrichotomyLabel.zero) := by
  let nextRegion : Set (ProbePair d × ℝ) :=
    negativeBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0
  let Φ : QuadraticDialForm d :=
    phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels
  let nonzeroLocus : Set (ProbePair d × ℝ) := {x | dialEval Φ x ≠ 0}
  have hnext :
      nextRegion = connectedComponentIn (currentRegion ∩ nonzeroLocus) x0 := by
    rfl
  have hx0_negΦ : dialEval Φ x0 < 0 := by
    simpa [Φ] using hx0_neg
  have hx0_nonzero : dialEval Φ x0 ≠ 0 := ne_of_lt hx0_negΦ
  have hx0_open : x0 ∈ currentRegion ∩ nonzeroLocus := ⟨hx0_current, hx0_nonzero⟩
  have hneg_on : ∀ x ∈ nextRegion, dialEval Φ x < 0 := by
    rw [hnext]
    apply negativeOn_of_preconnected_of_nonzero isPreconnected_connectedComponentIn
      (continuous_dialEval Φ)
    · intro x hx
      exact (connectedComponentIn_subset (currentRegion ∩ nonzeroLocus) x0 hx).2
    · exact ⟨x0, mem_connectedComponentIn hx0_open, hx0_negΦ⟩
  have htop := negativeBranchComponent_getElem_topology_withEstimate
    (r := r) (θ := θ) (head := head) (hn := hn) hInv hx0_current hx0_neg hdet
  refine DialEstimate.estimate_zero_getElem
    (r := r) (θ := θ) (head := head) (currentRegion := currentRegion)
    (nextRegion := nextRegion) (labels := labels) (hn := hn)
    hqpos hq a hcurrent htop.2.2.2 hInv.estimate ?_
  intro x hx
  rcases x with ⟨p, t⟩
  exact expCloseTo_actualProbeGate_zero_of_dialEval_neg_prefix
    (r := r) (θ := θ) (head := head) (baseRegion := baseRegion)
    (currentRegion := currentRegion) (labels := labels) (idx := n) (q := q) (a := a)
    hInv hn hqpos hq hcurrent (htop.2.2.2 hx)
    (ht_pos (p, t) hx) (ht_lt_one (p, t) hx)
    (hfirst (p, t) hx) (hpi (p, t) hx) (hsep (p, t) hx)
    (halpha (p, t) hx) (by simpa [Φ] using hneg_on (p, t) hx)

/-- Convert a final concrete trichotomy result into the `hlabel` premise consumed by
`tendsto_satZetaActualProbePoint`, isolating the still-hard α-branch estimate as
the only extra hypothesis.

The `1` and `0` branches are discharged from the final `LabelSignLink` plus the
faithfulness identity for `phiHeadOfDeeperHead`; the `α` branch supplies the
numeric saturated label and delegates exactly the rescaled-slope estimate
`τ * actualProbeSlope → 0`. -/
theorem TrichotomyResult.satZeta_hlabel_of_alpha_estimate {m k d r : Nat}
    {θ : Params (m + 1) k d} {h : Fin k}
    {baseRegion : Set (ProbePair d × ℝ)}
    (R : TrichotomyResult (dialPredicates (attentionMatrix θ 0) h)
      (dialFormalData r θ h) baseRegion (deeperHeadOrder (m + 1) k))
    {p : ProbePair d} {t : ℝ} (hx : (p, t) ∈ R.Ustar)
    (halpha : ∀ (n : Nat), 1 ≤ n → (hn : n < m + 1) → ∀ (a : Fin k),
      R.labels { layer := n + 1, head := (a : Nat) + 1 } = TrichotomyLabel.alpha →
        Tendsto (fun τ => τ * actualProbeSlope r θ
          (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
          (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2
          τ ⟨n, hn⟩ a) atTop (𝓝 0)) :
    ∀ (n : Nat), 1 ≤ n → (hn : n < m + 1) → ∀ (a : Fin k),
      (trichotomyToSaturatedLabels r (m + 1) k R.labels (n + 1) a = 1 ∧
        0 < matrixBilin (attentionMatrix θ ⟨n, hn⟩ a)
          (satZetaPoint θ h (trichotomyToSaturatedLabels r (m + 1) k R.labels) p t n).1
          (satZetaPoint θ h (trichotomyToSaturatedLabels r (m + 1) k R.labels) p t n).2)
      ∨ (trichotomyToSaturatedLabels r (m + 1) k R.labels (n + 1) a = 0 ∧
        matrixBilin (attentionMatrix θ ⟨n, hn⟩ a)
          (satZetaPoint θ h (trichotomyToSaturatedLabels r (m + 1) k R.labels) p t n).1
          (satZetaPoint θ h (trichotomyToSaturatedLabels r (m + 1) k R.labels) p t n).2 < 0)
      ∨ (trichotomyToSaturatedLabels r (m + 1) k R.labels (n + 1) a = alpha r ∧
        Tendsto (fun τ => τ * actualProbeSlope r θ
          (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
          (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2
          τ ⟨n, hn⟩ a) atTop (𝓝 0)) := by
  intro n hnpos hn a
  have hmem :
      ({ layer := n + 1, head := (a : Nat) + 1 } : DeeperHead) ∈
        deeperHeadOrder (m + 1) k :=
    succ_head_mem_deeperHeadOrder hnpos hn a
  have hdial :=
    dialEval_phiHeadOfDeeperHead_succ_eq_frozenSlope r θ h R.labels n hnpos hn a p t
  rcases R.dialEval_label_cases hmem hx with
    ⟨hlabel, hpos⟩ | ⟨hlabel, hneg⟩ | ⟨hlabel, _hzero⟩
  · left
    exact
      ⟨trichotomyToSaturatedLabels_eq_one_of_label_one r (m + 1) k
          R.labels (n + 1) a hlabel,
        by simpa [hdial] using hpos⟩
  · right
    left
    exact
      ⟨trichotomyToSaturatedLabels_eq_zero_of_label_zero r (m + 1) k
          R.labels (n + 1) a hlabel,
        by simpa [hdial] using hneg⟩
  · right
    right
    exact
      ⟨trichotomyToSaturatedLabels_eq_alpha_of_label_alpha r (m + 1) k
          R.labels (n + 1) a hlabel,
        halpha n hnpos hn a hlabel⟩

/-- Final-label ζ-point convergence from a concrete trichotomy result, with the
remaining α-branch estimate supplied as an explicit hypothesis. -/
theorem TrichotomyResult.tendsto_satZetaActualProbePoint_of_alpha_estimate
    {m k d r : Nat} {θ : Params (m + 1) k d} {h : Fin k}
    {baseRegion : Set (ProbePair d × ℝ)}
    (R : TrichotomyResult (dialPredicates (attentionMatrix θ 0) h)
      (dialFormalData r θ h) baseRegion (deeperHeadOrder (m + 1) k))
    {p : ProbePair d} {t : ℝ} (hx : (p, t) ∈ R.Ustar)
    (halpha : ∀ (n : Nat), 1 ≤ n → (hn : n < m + 1) → ∀ (a : Fin k),
      R.labels { layer := n + 1, head := (a : Nat) + 1 } = TrichotomyLabel.alpha →
        Tendsto (fun τ => τ * actualProbeSlope r θ
          (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
          (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2
          τ ⟨n, hn⟩ a) atTop (𝓝 0))
    (ht_pos : 0 < t) (ht_lt_one : t < 1)
    (hq : firstHeadSlope (attentionMatrix θ 0) h p = 0)
    (hpi : firstHeadPi (attentionMatrix θ 0) h p ≠ 0)
    (hsep : ∀ a : Fin k, a ≠ h → 0 < matrixBilin (attentionMatrix θ 0 a) p.1 p.2)
    (n : Nat) (hn : n ≤ m + 1) :
    Tendsto (fun τ => actualProbePoint r θ
        (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
        (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2 n hn τ)
      atTop (𝓝 (satZetaPoint θ h
        (trichotomyToSaturatedLabels r (m + 1) k R.labels) p t n)) :=
  tendsto_satZetaActualProbePoint r θ h
    (trichotomyToSaturatedLabels r (m + 1) k R.labels) p t ht_pos ht_lt_one
    hq hpi hsep (R.satZeta_hlabel_of_alpha_estimate hx halpha) n hn


/-- Invariant-level α-branch successor estimate.  Mirrors the positive/negative branch
siblings: separation is passed explicitly, the processed prior-gate closeness is read off the
processing invariant, and the current head's zero dial form supplies the vanishing frozen
slope.  The remaining input is the per-point, per-coordinate polynomial Lipschitz control of
the formal slope along the dial path. -/
theorem DialEstimate.estimate_alpha_getElem_currentRegion_of_zeroDialForm_sep_lipschitz
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {baseRegion currentRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n q : Nat} {a : Fin k}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    (hInv : ProcessingInvariantStatement (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) baseRegion currentRegion
      (deeperHeadOrder (m + 1) k) n labels)
    (hqpos : 1 ≤ q) (hq : q < m + 1)
    (hcurrent : (deeperHeadOrder (m + 1) k)[n] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    (hz : zeroDialForm
      (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels))
    (hsep : ∀ x ∈ currentRegion, ∀ b : Fin k, b ≠ head →
      0 < matrixBilin (attentionMatrix θ 0 b) x.1.1 x.1.2)
    (K T : ProbePair d × ℝ → Nat → ℝ)
    (hK : ∀ x ∈ currentRegion, ∀ i : Nat,
      i < (formalVarsBelow (m + 1) k q).length → 0 ≤ K x i)
    (hLip : ∀ x ∈ currentRegion, ∀ i : Nat,
      (hi : i < (formalVarsBelow (m + 1) k q).length) →
      ∀ τ : ℝ, T x i ≤ τ →
        |MvPolynomial.eval
            (formalVarPrefixAssignment (fun τ => dialActualGate r θ head x.1 x.2 τ)
              (fun τ => dialFrozenGate r θ head labels x.1 x.2 τ)
              (formalVarsBelow (m + 1) k q) (i + 1) τ)
            (formalSlope θ
              (headDialPath (attentionMatrix θ 0) head (logScale r) x.1 x.2 τ).1
              (headDialPath (attentionMatrix θ 0) head (logScale r) x.1 x.2 τ).2 ⟨q, hq⟩ a) -
          MvPolynomial.eval
            (formalVarPrefixAssignment (fun τ => dialActualGate r θ head x.1 x.2 τ)
              (fun τ => dialFrozenGate r θ head labels x.1 x.2 τ)
              (formalVarsBelow (m + 1) k q) i τ)
            (formalSlope θ
              (headDialPath (attentionMatrix θ 0) head (logScale r) x.1 x.2 τ).1
              (headDialPath (attentionMatrix θ 0) head (logScale r) x.1 x.2 τ).2 ⟨q, hq⟩ a)|
          ≤ K x i *
            |dialActualGate r θ head x.1 x.2 τ ((formalVarsBelow (m + 1) k q)[i]'hi) -
              dialFrozenGate r θ head labels x.1 x.2 τ ((formalVarsBelow (m + 1) k q)[i]'hi)|) :
    (dialPredicatesWithEstimate r θ head).Estimate
      (deeperHeadOrder (m + 1) k) (n + 1) currentRegion
      (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) TrichotomyLabel.alpha) := by
  refine DialEstimate.estimate_alpha_getElem_currentRegion_of_actualProbeSlope_expCloseTo_zero
    (r := r) (θ := θ) (head := head) (baseRegion := baseRegion)
    (currentRegion := currentRegion) (labels := labels) (hn := hn)
    hInv hqpos hq hcurrent ?_
  intro x hx
  have hz_current : zeroDialForm
      (phiHeadOfDeeperHead r θ head
        ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead) labels) := by
    simpa [hcurrent] using hz
  exact
    expCloseTo_actualProbeSlope_zero_of_zeroDialForm_sep_prior_lipschitz
      θ head labels x.1 x.2 q hqpos hq a hz_current
      (hsep x hx)
      (hInv.priorGate_eventuallyExpClose_of_current_getElem hn hcurrent x hx)
      (K x) (T x) (hK x hx) (hLip x hx)

/-- **Invariant-level α-branch successor estimate, fully unconditional.**  Same as
`estimate_alpha_getElem_currentRegion_of_zeroDialForm_sep_lipschitz`, but with the
per-coordinate polynomial Lipschitz control now discharged internally: the only remaining
inputs are the honest ones — the current head's zero dial form (`hz`), first-layer separation
(`hsep`), and the processing invariant supplying the processed prior-gate closeness. -/
theorem DialEstimate.estimate_alpha_getElem_currentRegion_of_zeroDialForm_sep
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {baseRegion currentRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n q : Nat} {a : Fin k}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    (hInv : ProcessingInvariantStatement (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) baseRegion currentRegion
      (deeperHeadOrder (m + 1) k) n labels)
    (hqpos : 1 ≤ q) (hq : q < m + 1)
    (hcurrent : (deeperHeadOrder (m + 1) k)[n] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    (hz : zeroDialForm
      (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels))
    (hsep : ∀ x ∈ currentRegion, ∀ b : Fin k, b ≠ head →
      0 < matrixBilin (attentionMatrix θ 0 b) x.1.1 x.1.2) :
    (dialPredicatesWithEstimate r θ head).Estimate
      (deeperHeadOrder (m + 1) k) (n + 1) currentRegion
      (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) TrichotomyLabel.alpha) := by
  refine DialEstimate.estimate_alpha_getElem_currentRegion_of_actualProbeSlope_expCloseTo_zero
    (r := r) (θ := θ) (head := head) (baseRegion := baseRegion)
    (currentRegion := currentRegion) (labels := labels) (hn := hn)
    hInv hqpos hq hcurrent ?_
  intro x hx
  have hz_current : zeroDialForm
      (phiHeadOfDeeperHead r θ head
        ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead) labels) := by
    simpa [hcurrent] using hz
  exact
    expCloseTo_actualProbeSlope_zero_of_zeroDialForm_sep
      θ head labels x.1 x.2 q hqpos hq a hz_current
      (hsep x hx)
      (hInv.priorGate_eventuallyExpClose_of_current_getElem hn hcurrent x hx)

/-! ## K07B.M8/M9 — concrete `prop_trichotomy_S` assembly

The declarations below wire the already-proved per-index step assembler
(`lem_trichotomy_step_S_dialWithEstimate_getElem_of_branch_estimates`) and the three
unconditional branch estimates into a concrete `prop_trichotomy_S` for the honest
`dialPredicatesWithEstimate` predicate, from genuine genericity inputs: a
`SignRegionData θ head` (supplying the base region topology and the first-layer
`t ∈ (0,1)`, `firstHeadSlope = 0`, `firstHeadPi ≠ 0` facts by restriction), a
`Regularity r θ` witness, `det A_head ≠ 0`, first-layer separation, and `2 ≤ d`.

The two assembly obstacles are discharged here:

* the current-region sign-region topology is re-established on every refined region by
  restricting `signRegionData_signRegionTopologyStatement` along the processing invariant;
* the prior-α slope convergence consumed by the positive/negative branch estimates is
  produced **per head** (no recursion over α-layers) from the processed-gate closeness in
  the `DialEstimate` payload via
  `tendsto_tau_mul_actualProbeSlope_zero_of_zeroDialForm_sep`; the α branch's `hz` is
  obtained from the vanishing dial evaluation by the zero-branch rigidity instance. -/

/-- Every entry of `deeperHeadOrder (m+1) k` is a genuine successor head
`{ layer := q+1, head := a+1 }` with `1 ≤ q < m+1` and `a : Fin k`. -/
theorem exists_decompose_getElem_deeperHeadOrder {m k : Nat} {n : Nat}
    (hn : n < (deeperHeadOrder (m + 1) k).length) :
    ∃ (q : Nat) (a : Fin k), 1 ≤ q ∧ q < m + 1 ∧
      (deeperHeadOrder (m + 1) k)[n] =
        ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead) := by
  have hmem : (deeperHeadOrder (m + 1) k)[n] ∈ deeperHeadOrder (m + 1) k :=
    List.getElem_mem hn
  obtain ⟨h2, hle, h1, hhk⟩ := mem_deeperHeadOrder_iff.mp hmem
  refine ⟨(deeperHeadOrder (m + 1) k)[n].layer - 1,
    ⟨(deeperHeadOrder (m + 1) k)[n].head - 1, by omega⟩, by omega, by omega, ?_⟩
  have hL : (deeperHeadOrder (m + 1) k)[n].layer - 1 + 1 =
      (deeperHeadOrder (m + 1) k)[n].layer := by omega
  have hH : (deeperHeadOrder (m + 1) k)[n].head - 1 + 1 =
      (deeperHeadOrder (m + 1) k)[n].head := by omega
  simp only [hL, hH]

/-- **Prior-α slope convergence from the processing invariant.**  For the head currently
being processed at layer `q+1`, every strictly-lower-layer head that carries the `alpha`
label has `τ · λ(τ) → 0` at every point of the current region.  This is exactly the
`halpha` input required by the positive/negative branch estimates.  It is proved
**per head** — no recursion over the α-layers — because the α slope estimate
`tendsto_tau_mul_actualProbeSlope_zero_of_zeroDialForm_sep` only consumes the processed
lower-gate closeness (read off `hInv.estimate.gate`), the head's zero dial form (read off
the invariant's label/sign link), and first-layer separation. -/
theorem alphaSlope_tendsto_of_processingInvariant_sep {m k d r : Nat}
    {θ : Params (m + 1) k d} {head : Fin k}
    {baseRegion currentRegion : Set (ProbePair d × ℝ)}
    {labels : DeeperHead → TrichotomyLabel} {n q : Nat} {a : Fin k}
    (hn : n < (deeperHeadOrder (m + 1) k).length)
    (hInv : ProcessingInvariantStatement (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) baseRegion currentRegion
      (deeperHeadOrder (m + 1) k) n labels)
    (_hqpos : 1 ≤ q) (_hq : q < m + 1)
    (hcurrent : (deeperHeadOrder (m + 1) k)[n] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    (hsep : ∀ x ∈ currentRegion, ∀ b : Fin k, b ≠ head →
      0 < matrixBilin (attentionMatrix θ 0 b) x.1.1 x.1.2) :
    ∀ x ∈ currentRegion, ∀ (q' : Nat), 1 ≤ q' → q' < q → (hq' : q' < m + 1) →
      ∀ (b : Fin k),
        labels ({ layer := q' + 1, head := (b : Nat) + 1 } : DeeperHead) =
            TrichotomyLabel.alpha →
          Tendsto (fun τ => τ * actualProbeSlope r θ
            (headDialPath (attentionMatrix θ 0) head (logScale r) x.1 x.2 τ).1
            (headDialPath (attentionMatrix θ 0) head (logScale r) x.1 x.2 τ).2
            τ ⟨q', hq'⟩ b) atTop (𝓝 0) := by
  intro x hx q' hq'pos hlt hq' b hlabel
  have hmem :
      ({ layer := q' + 1, head := (b : Nat) + 1 } : DeeperHead) ∈
        processedPrefix (deeperHeadOrder (m + 1) k) n :=
    succ_head_mem_processedPrefix_of_layer_lt_getElem_deeperHeadOrder
      hn hcurrent hq'pos hq' hlt b
  have hz : zeroDialForm
      (phiHeadOfDeeperHead r θ head
        ({ layer := q' + 1, head := (b : Nat) + 1 } : DeeperHead) labels) :=
    hInv.zeroDialForm_of_label_alpha_withEstimate hmem hlabel
  have hprior : ∀ (q'' : Nat), 1 ≤ q'' → q'' < q' → (hq'' : q'' < m + 1) →
      ∀ (b'' : Fin k),
        EventuallyExpClose
          (fun τ => actualProbeGate r θ
            (headDialPath (attentionMatrix θ 0) head (logScale r) x.1 x.2 τ).1
            (headDialPath (attentionMatrix θ 0) head (logScale r) x.1 x.2 τ).2
            τ ⟨q'', hq''⟩ b'')
          (trichotomyToSaturatedLabels r (m + 1) k labels (q'' + 1) b'') := by
    intro q'' hq''pos hlt'' hq'' b''
    have hmem'' :
        ({ layer := q'' + 1, head := (b'' : Nat) + 1 } : DeeperHead) ∈
          processedPrefix (deeperHeadOrder (m + 1) k) n :=
      succ_head_mem_processedPrefix_of_layer_lt_getElem_deeperHeadOrder
        hn hcurrent hq''pos hq'' (lt_trans hlt'' hlt) b''
    exact eventuallyExpClose_of_expCloseTo
      (hInv.estimate.gate hq''pos hq'' b'' hmem'' x hx)
  exact tendsto_tau_mul_actualProbeSlope_zero_of_zeroDialForm_sep
    θ head labels x.1 x.2 q' hq'pos hq' b hz (hsep x hx) hprior

/-- **Uniform one-step trichotomy for `dialPredicatesWithEstimate`.**  The per-index
assembler proves the step only for the head `order[n]`; this lemma upgrades it to the
`∀ h` form consumed by `prop_trichotomy_of_initial_and_step`.  The upgrade is honest:
`TrichotomyLabel` has no "unprocessed" constructor, so the `processed_label` clause for an
arbitrary `h` is discharged by exhaustiveness.  For `n` past the order length the step is
the trivial identity advance. -/
theorem lem_trichotomy_step_S_dialWithEstimate_uniform_of_signRegionData
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    (D : SignRegionData θ head)
    (hdet : (attentionMatrix θ 0 head).det ≠ 0)
    (hd : 2 ≤ d) (hreg : Regularity r θ)
    (hsep : ∀ x ∈ D.region, ∀ b : Fin k, b ≠ head →
      0 < matrixBilin (attentionMatrix θ 0 b) x.1.1 x.1.2)
    (currentRegion : Set (ProbePair d × ℝ)) (n : Nat)
    (labels : DeeperHead → TrichotomyLabel) (h : DeeperHead) :
    lem_trichotomy_step_S (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) D.region currentRegion
      (deeperHeadOrder (m + 1) k) n labels h := by
  intro hInv
  by_cases hn : n < (deeperHeadOrder (m + 1) k).length
  · obtain ⟨q, a, hqpos, hq, hcurrent⟩ := exists_decompose_getElem_deeperHeadOrder hn
    have htop : SignRegionTopologyStatement (attentionMatrix θ 0) (valueMatrix θ 0) head
        currentRegion :=
      SignRegionTopologyStatement.restrict (signRegionData_signRegionTopologyStatement D)
        hInv.region_subset_base hInv.region_nonempty hInv.region_connected
        hInv.region_relativelyOpen
    have hIface : SignRegionInterface (attentionMatrix θ 0) (valueMatrix θ 0) head
        currentRegion :=
      (signRegionData_signRegionInterface D).restrict hInv.region_subset_base
    have hsep_cur : ∀ x ∈ currentRegion, ∀ b : Fin k, b ≠ head →
        0 < matrixBilin (attentionMatrix θ 0 b) x.1.1 x.1.2 :=
      fun x hx b hb => hsep x (hInv.region_subset_base hx) b hb
    have halpha_cur :=
      alphaSlope_tendsto_of_processingInvariant_sep hn hInv hqpos hq hcurrent hsep_cur
    -- positive branch estimate provider
    have hestimate_pos : ∀ (x0 : ProbePair d × ℝ), x0 ∈ currentRegion →
        0 < dialEval
          (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels) x0 →
        (dialPredicatesWithEstimate r θ head).Estimate
          (deeperHeadOrder (m + 1) k) (n + 1)
          (positiveBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0)
          (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) TrichotomyLabel.one) := by
      intro x0 hx0 hx0pos
      have hsubP :
          positiveBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0 ⊆
            currentRegion :=
        (positiveBranchComponent_getElem_topology_withEstimate hn hInv hx0 hx0pos hdet).2.2.2
      exact DialEstimate.estimate_one_getElem_positiveBranchComponent
        hn hInv hqpos hq hcurrent hx0 hx0pos hdet
        (fun x hx => hIface.t_pos x (hsubP hx))
        (fun x hx => hIface.t_lt_one x (hsubP hx))
        (fun x hx => hIface.point_on_quadric x (hsubP hx))
        (fun x hx => hIface.pi_ne_zero x (hsubP hx))
        (fun x hx => hsep_cur x (hsubP hx))
        (fun x hx => halpha_cur x (hsubP hx))
    -- negative branch estimate provider
    have hestimate_neg : ∀ (x0 : ProbePair d × ℝ), x0 ∈ currentRegion →
        dialEval
          (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels) x0 < 0 →
        (dialPredicatesWithEstimate r θ head).Estimate
          (deeperHeadOrder (m + 1) k) (n + 1)
          (negativeBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0)
          (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) TrichotomyLabel.zero) := by
      intro x0 hx0 hx0neg
      have hsubN :
          negativeBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0 ⊆
            currentRegion :=
        (negativeBranchComponent_getElem_topology_withEstimate hn hInv hx0 hx0neg hdet).2.2.2
      exact DialEstimate.estimate_zero_getElem_negativeBranchComponent
        hn hInv hqpos hq hcurrent hx0 hx0neg hdet
        (fun x hx => hIface.t_pos x (hsubN hx))
        (fun x hx => hIface.t_lt_one x (hsubN hx))
        (fun x hx => hIface.point_on_quadric x (hsubN hx))
        (fun x hx => hIface.pi_ne_zero x (hsubN hx))
        (fun x hx => hsep_cur x (hsubN hx))
        (fun x hx => halpha_cur x (hsubN hx))
    -- α branch estimate provider (rigidity bridge for `hz`, then unconditional estimate)
    have hestimate_alpha :
        (∀ x ∈ currentRegion,
          dialEval
            (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels) x = 0) →
        (dialPredicatesWithEstimate r θ head).Estimate
          (deeperHeadOrder (m + 1) k) (n + 1) currentRegion
          (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) TrichotomyLabel.alpha) := by
      intro hvanish
      have hz : zeroDialForm
          (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels) := by
        have hrig := lem_zero_branch_rigidity_S_instance
          (r := r) θ head currentRegion labels ((deeperHeadOrder (m + 1) k)[n]) hd hreg htop
        exact hrig (by simpa [dialPredicates, dialFormalData] using hvanish)
      exact DialEstimate.estimate_alpha_getElem_currentRegion_of_zeroDialForm_sep
        hn hInv hqpos hq hcurrent hz hsep_cur
    -- assemble the step for `order[n]`, then relabel the head parameter to `h`
    obtain ⟨result_n, _⟩ :=
      lem_trichotomy_step_S_dialWithEstimate_getElem_of_branch_estimates
        hn hdet hd hreg htop hestimate_pos hestimate_neg hestimate_alpha hInv
    exact ⟨{ branch := result_n.branch
             nextRegion := result_n.nextRegion
             nextLabels := result_n.nextLabels
             nextRegion_subset_current := result_n.nextRegion_subset_current
             processed_label := by cases result_n.nextLabels h <;> simp
             next_invariant := result_n.next_invariant }, trivial⟩
  · push_neg at hn
    have htake :
        processedPrefix (deeperHeadOrder (m + 1) k) (n + 1) =
          processedPrefix (deeperHeadOrder (m + 1) k) n := by
      simp only [processedPrefix]
      rw [List.take_of_length_le (le_trans hn (Nat.le_succ n)),
        List.take_of_length_le hn]
    refine ⟨{ branch := TrichotomyStepBranch.nonzero
              nextRegion := currentRegion
              nextLabels := labels
              nextRegion_subset_current := subset_rfl
              processed_label := by cases labels h <;> simp
              next_invariant := ?_ }, trivial⟩
    exact { region_nonempty := hInv.region_nonempty
            region_connected := hInv.region_connected
            region_relativelyOpen := hInv.region_relativelyOpen
            region_subset_base := hInv.region_subset_base
            label_sign_link := fun h' hh' => hInv.label_sign_link h' (htake ▸ hh')
            estimate :=
              { gate := fun hqpos hq a hmem x hx =>
                  hInv.estimate.gate hqpos hq a (htake ▸ hmem) x hx } }

/-- **Uniform one-step trichotomy for `dialPredicatesWithEstimate`, additive
`_of_topology` form.**  Identical to
`lem_trichotomy_step_S_dialWithEstimate_uniform_of_signRegionData`, but driven by
a `SignRegionTopologyStatement (attentionMatrix θ 0) V' head U` over a **free**
value-matrix parameter `V'` and a `FirstHeadRigidityFacts θ head` bundle, in place
of a `SignRegionData θ head` + `Regularity r θ`. -/
theorem lem_trichotomy_step_S_dialWithEstimate_uniform_of_topology
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {V' : Fin k → Matrix (Fin d) (Fin d) ℝ}
    (U : Set (ProbePair d × ℝ))
    (htop : SignRegionTopologyStatement (attentionMatrix θ 0) V' head U)
    (hfacts : FirstHeadRigidityFacts θ head)
    (hd : 2 ≤ d)
    (hsep : ∀ x ∈ U, ∀ b : Fin k, b ≠ head →
      0 < matrixBilin (attentionMatrix θ 0 b) x.1.1 x.1.2)
    (currentRegion : Set (ProbePair d × ℝ)) (n : Nat)
    (labels : DeeperHead → TrichotomyLabel) (h : DeeperHead) :
    lem_trichotomy_step_S (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) U currentRegion
      (deeperHeadOrder (m + 1) k) n labels h := by
  intro hInv
  have hdet : (attentionMatrix θ 0 head).det ≠ 0 := hfacts.det_ne
  by_cases hn : n < (deeperHeadOrder (m + 1) k).length
  · obtain ⟨q, a, hqpos, hq, hcurrent⟩ := exists_decompose_getElem_deeperHeadOrder hn
    have htop_cur : SignRegionTopologyStatement (attentionMatrix θ 0) V' head
        currentRegion :=
      htop.restrict hInv.region_subset_base hInv.region_nonempty hInv.region_connected
        hInv.region_relativelyOpen
    have hIface : SignRegionInterface (attentionMatrix θ 0) V' head
        currentRegion :=
      htop.interface.restrict hInv.region_subset_base
    have hsep_cur : ∀ x ∈ currentRegion, ∀ b : Fin k, b ≠ head →
        0 < matrixBilin (attentionMatrix θ 0 b) x.1.1 x.1.2 :=
      fun x hx b hb => hsep x (hInv.region_subset_base hx) b hb
    have halpha_cur :=
      alphaSlope_tendsto_of_processingInvariant_sep hn hInv hqpos hq hcurrent hsep_cur
    -- positive branch estimate provider
    have hestimate_pos : ∀ (x0 : ProbePair d × ℝ), x0 ∈ currentRegion →
        0 < dialEval
          (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels) x0 →
        (dialPredicatesWithEstimate r θ head).Estimate
          (deeperHeadOrder (m + 1) k) (n + 1)
          (positiveBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0)
          (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) TrichotomyLabel.one) := by
      intro x0 hx0 hx0pos
      have hsubP :
          positiveBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0 ⊆
            currentRegion :=
        (positiveBranchComponent_getElem_topology_withEstimate hn hInv hx0 hx0pos hdet).2.2.2
      exact DialEstimate.estimate_one_getElem_positiveBranchComponent
        hn hInv hqpos hq hcurrent hx0 hx0pos hdet
        (fun x hx => hIface.t_pos x (hsubP hx))
        (fun x hx => hIface.t_lt_one x (hsubP hx))
        (fun x hx => hIface.point_on_quadric x (hsubP hx))
        (fun x hx => hIface.pi_ne_zero x (hsubP hx))
        (fun x hx => hsep_cur x (hsubP hx))
        (fun x hx => halpha_cur x (hsubP hx))
    -- negative branch estimate provider
    have hestimate_neg : ∀ (x0 : ProbePair d × ℝ), x0 ∈ currentRegion →
        dialEval
          (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels) x0 < 0 →
        (dialPredicatesWithEstimate r θ head).Estimate
          (deeperHeadOrder (m + 1) k) (n + 1)
          (negativeBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0)
          (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) TrichotomyLabel.zero) := by
      intro x0 hx0 hx0neg
      have hsubN :
          negativeBranchComponent_getElem (r := r) θ head currentRegion labels n hn x0 ⊆
            currentRegion :=
        (negativeBranchComponent_getElem_topology_withEstimate hn hInv hx0 hx0neg hdet).2.2.2
      exact DialEstimate.estimate_zero_getElem_negativeBranchComponent
        hn hInv hqpos hq hcurrent hx0 hx0neg hdet
        (fun x hx => hIface.t_pos x (hsubN hx))
        (fun x hx => hIface.t_lt_one x (hsubN hx))
        (fun x hx => hIface.point_on_quadric x (hsubN hx))
        (fun x hx => hIface.pi_ne_zero x (hsubN hx))
        (fun x hx => hsep_cur x (hsubN hx))
        (fun x hx => halpha_cur x (hsubN hx))
    -- α branch estimate provider (rigidity bridge for `hz`, then unconditional estimate)
    have hestimate_alpha :
        (∀ x ∈ currentRegion,
          dialEval
            (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels) x = 0) →
        (dialPredicatesWithEstimate r θ head).Estimate
          (deeperHeadOrder (m + 1) k) (n + 1) currentRegion
          (setLabel labels ((deeperHeadOrder (m + 1) k)[n]) TrichotomyLabel.alpha) := by
      intro hvanish
      have hz : zeroDialForm
          (phiHeadOfDeeperHead r θ head ((deeperHeadOrder (m + 1) k)[n]) labels) := by
        have hrig := lem_zero_branch_rigidity_S_instance_of_facts
          (r := r) θ head currentRegion labels ((deeperHeadOrder (m + 1) k)[n]) hd hfacts htop_cur
        exact hrig (by simpa [dialPredicates, dialFormalData] using hvanish)
      exact DialEstimate.estimate_alpha_getElem_currentRegion_of_zeroDialForm_sep
        hn hInv hqpos hq hcurrent hz hsep_cur
    -- assemble the step for `order[n]`, then relabel the head parameter to `h`
    obtain ⟨result_n, _⟩ :=
      lem_trichotomy_step_S_dialWithEstimate_getElem_of_branch_estimates_of_facts
        hn hdet hd hfacts htop_cur hestimate_pos hestimate_neg hestimate_alpha hInv
    exact ⟨{ branch := result_n.branch
             nextRegion := result_n.nextRegion
             nextLabels := result_n.nextLabels
             nextRegion_subset_current := result_n.nextRegion_subset_current
             processed_label := by cases result_n.nextLabels h <;> simp
             next_invariant := result_n.next_invariant }, trivial⟩
  · push_neg at hn
    have htake :
        processedPrefix (deeperHeadOrder (m + 1) k) (n + 1) =
          processedPrefix (deeperHeadOrder (m + 1) k) n := by
      simp only [processedPrefix]
      rw [List.take_of_length_le (le_trans hn (Nat.le_succ n)),
        List.take_of_length_le hn]
    refine ⟨{ branch := TrichotomyStepBranch.nonzero
              nextRegion := currentRegion
              nextLabels := labels
              nextRegion_subset_current := subset_rfl
              processed_label := by cases labels h <;> simp
              next_invariant := ?_ }, trivial⟩
    exact { region_nonempty := hInv.region_nonempty
            region_connected := hInv.region_connected
            region_relativelyOpen := hInv.region_relativelyOpen
            region_subset_base := hInv.region_subset_base
            label_sign_link := fun h' hh' => hInv.label_sign_link h' (htake ▸ hh')
            estimate :=
              { gate := fun hqpos hq a hmem x hx =>
                  hInv.estimate.gate hqpos hq a (htake ▸ hmem) x hx } }

/-- **K07B.M8/M9 — concrete `prop_trichotomy_S` for the honest dial predicate.**

From genuine genericity inputs — a `SignRegionData θ head`, a `Regularity r θ` witness,
`det A_head ≠ 0`, first-layer separation, and `2 ≤ d` — the full multi-head trichotomy
proposition holds for `dialPredicatesWithEstimate` over the base region `D.region`. -/
theorem prop_trichotomy_S_dialWithEstimate_of_signRegionData
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    (D : SignRegionData θ head)
    (hdet : (attentionMatrix θ 0 head).det ≠ 0)
    (hd : 2 ≤ d) (hreg : Regularity r θ)
    (hsep : ∀ x ∈ D.region, ∀ b : Fin k, b ≠ head →
      0 < matrixBilin (attentionMatrix θ 0 b) x.1.1 x.1.2) :
    prop_trichotomy_S (dialPredicatesWithEstimate r θ head) (dialFormalData r θ head)
      D.region (deeperHeadOrder (m + 1) k) := by
  refine prop_trichotomy_of_initial_and_step (dialPredicatesWithEstimate r θ head)
    (dialFormalData r θ head) D.region (deeperHeadOrder (m + 1) k)
    (fun _ => TrichotomyLabel.alpha) ?_ ?_
  · exact processingInvariant_zero (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) D.region (deeperHeadOrder (m + 1) k)
      (fun _ => TrichotomyLabel.alpha)
      D.nonempty D.region_connected
      (signRegionData_relativelyOpenIn_quadricPatchCylinder D)
      subset_rfl
      { gate := fun _hqpos _hq _a hmem _x _hx => by
          simp only [processedPrefix, List.take_zero, List.not_mem_nil] at hmem }
  · exact fun currentRegion n labels h =>
      lem_trichotomy_step_S_dialWithEstimate_uniform_of_signRegionData
        D hdet hd hreg hsep currentRegion n labels h

/-- **The concrete trichotomy result, exposed.**  The `TrichotomyResult` witnessing
`prop_trichotomy_S_dialWithEstimate_of_signRegionData`, carrying the final region
`Ustar`, the `labels : DeeperHead → TrichotomyLabel`, the label/sign links, and the honest
`DialEstimate` processed-gate payload.  K07C consumes `.labels` and `.estimate`. -/
noncomputable def trichotomyResult_dialWithEstimate_of_signRegionData
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    (D : SignRegionData θ head)
    (hdet : (attentionMatrix θ 0 head).det ≠ 0)
    (hd : 2 ≤ d) (hreg : Regularity r θ)
    (hsep : ∀ x ∈ D.region, ∀ b : Fin k, b ≠ head →
      0 < matrixBilin (attentionMatrix θ 0 b) x.1.1 x.1.2) :
    TrichotomyResult (dialPredicatesWithEstimate r θ head) (dialFormalData r θ head)
      D.region (deeperHeadOrder (m + 1) k) :=
  (prop_trichotomy_S_dialWithEstimate_of_signRegionData D hdet hd hreg hsep).choose

/-- **Additive `_of_topology` form of `prop_trichotomy_S_dialWithEstimate_of_signRegionData`.**

From a `SignRegionTopologyStatement (attentionMatrix θ 0) V' head U` over a
**free** value-matrix parameter `V'`, a `FirstHeadRigidityFacts θ head` bundle,
`2 ≤ d`, and first-layer separation over the base region `U`, the full multi-head
trichotomy proposition holds for `dialPredicatesWithEstimate` over `U`. -/
theorem prop_trichotomy_S_dialWithEstimate_of_topology
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {V' : Fin k → Matrix (Fin d) (Fin d) ℝ}
    (U : Set (ProbePair d × ℝ))
    (htop : SignRegionTopologyStatement (attentionMatrix θ 0) V' head U)
    (hfacts : FirstHeadRigidityFacts θ head) (hd : 2 ≤ d)
    (hsep : ∀ x ∈ U, ∀ b : Fin k, b ≠ head →
      0 < matrixBilin (attentionMatrix θ 0 b) x.1.1 x.1.2) :
    prop_trichotomy_S (dialPredicatesWithEstimate r θ head) (dialFormalData r θ head)
      U (deeperHeadOrder (m + 1) k) := by
  refine prop_trichotomy_of_initial_and_step (dialPredicatesWithEstimate r θ head)
    (dialFormalData r θ head) U (deeperHeadOrder (m + 1) k)
    (fun _ => TrichotomyLabel.alpha) ?_ ?_
  · exact processingInvariant_zero (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) U (deeperHeadOrder (m + 1) k)
      (fun _ => TrichotomyLabel.alpha)
      htop.nonempty htop.connected
      htop.relatively_open
      subset_rfl
      { gate := fun _hqpos _hq _a hmem _x _hx => by
          simp only [processedPrefix, List.take_zero, List.not_mem_nil] at hmem }
  · exact fun currentRegion n labels h =>
      lem_trichotomy_step_S_dialWithEstimate_uniform_of_topology
        U htop hfacts hd hsep currentRegion n labels h

/-- **The concrete trichotomy result, exposed (additive `_of_topology` form).**  The
`TrichotomyResult` witnessing `prop_trichotomy_S_dialWithEstimate_of_topology`, carrying
the final region `Ustar`, the `labels`, the label/sign links, and the honest `DialEstimate`
processed-gate payload. -/
noncomputable def trichotomyResult_dialWithEstimate_of_topology
    {m k d r : Nat} {θ : Params (m + 1) k d} {head : Fin k}
    {V' : Fin k → Matrix (Fin d) (Fin d) ℝ}
    (U : Set (ProbePair d × ℝ))
    (htop : SignRegionTopologyStatement (attentionMatrix θ 0) V' head U)
    (hfacts : FirstHeadRigidityFacts θ head) (hd : 2 ≤ d)
    (hsep : ∀ x ∈ U, ∀ b : Fin k, b ≠ head →
      0 < matrixBilin (attentionMatrix θ 0 b) x.1.1 x.1.2) :
    TrichotomyResult (dialPredicatesWithEstimate r θ head) (dialFormalData r θ head)
      U (deeperHeadOrder (m + 1) k) :=
  (prop_trichotomy_S_dialWithEstimate_of_topology U htop hfacts hd hsep).choose

/-- **Downcast to the `dialPredicates` (unit-estimate) result.**  The region clauses and the
label/sign links of `dialPredicatesWithEstimate` and `dialPredicates` coincide
definitionally, so a `dialPredicatesWithEstimate` result restricts to a `dialPredicates`
result with the **same** `Ustar` and `labels`, forgetting the `DialEstimate` payload.  This
is the record consumed by `TrichotomyResult.satZeta_hlabel_of_alpha_estimate` (K07C.M6). -/
noncomputable def TrichotomyResult.toDialPredicates {m k d r : Nat}
    {θ : Params (m + 1) k d} {head : Fin k}
    {baseRegion : Set (ProbePair d × ℝ)} {order : List DeeperHead}
    (R : TrichotomyResult (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) baseRegion order) :
    TrichotomyResult (dialPredicates (attentionMatrix θ 0) head)
      (dialFormalData r θ head) baseRegion order where
  Ustar := R.Ustar
  labels := R.labels
  region_nonempty := R.region_nonempty
  region_connected := R.region_connected
  region_relativelyOpen := R.region_relativelyOpen
  region_subset_base := R.region_subset_base
  label_sign_link := R.label_sign_link
  estimate := trivial

@[simp] theorem TrichotomyResult.toDialPredicates_labels {m k d r : Nat}
    {θ : Params (m + 1) k d} {head : Fin k}
    {baseRegion : Set (ProbePair d × ℝ)} {order : List DeeperHead}
    (R : TrichotomyResult (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) baseRegion order) :
    R.toDialPredicates.labels = R.labels := rfl

@[simp] theorem TrichotomyResult.toDialPredicates_Ustar {m k d r : Nat}
    {θ : Params (m + 1) k d} {head : Fin k}
    {baseRegion : Set (ProbePair d × ℝ)} {order : List DeeperHead}
    (R : TrichotomyResult (dialPredicatesWithEstimate r θ head)
      (dialFormalData r θ head) baseRegion order) :
    R.toDialPredicates.Ustar = R.Ustar := rfl

end SatZetaLimits

end TransformerIdentifiability.NLayer.KHead
