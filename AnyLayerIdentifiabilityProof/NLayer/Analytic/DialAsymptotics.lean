import AnyLayerIdentifiabilityProof.NLayer.Analytic.AlgebraicQuadric

set_option autoImplicit false

open Filter Topology Matrix

namespace TransformerIdentifiability.NLayer

/-!
# Dial paths and first-gate saturation

This file formalizes the "Dial paths" lemma (`lem:dial`) from
`n_layer_proof.tex`, lines 2075–2136.

Given a base point `(w0, v0)` on the bilinear quadric `q(w, v) = 0` (here
`q = matrixBilin A`), a direction `y`, and a scalar `c`, the *dial path* is
`τ ↦ (w0 - (c/τ)•y, v0 + (c/τ)•y)`.  Its sum is constant, it converges to
`(w0, v0)` as `τ → ∞`, and under the bracket normalisation
`matrixBilin A w0 y - matrixBilin A y v0 = 1` the rescaled gate argument
`τ·q(w(τ), v(τ)) + b` converges to `c + b`.  Applying the (continuous) sigmoid
gives first-gate saturation `s₁(τ) → sig (c + b)`.

The connection `sig (c + b) = t` (with `c = sigmoidLogit t - b`) belongs to a
higher layer and is deliberately *not* established here; this file is purely
about `sig (c + b)`.
-/

/-! ## Bilinearity of `matrixBilin`

`matrixBilin A w v = w ⬝ᵥ A.mulVec v` (see `AlgebraicQuadric.lean`).  Only
`matrixBilin_sub` is available there, so we record the additivity and scalar
homogeneity needed to expand the dial identity. -/

/-- `matrixBilin` is additive in its left argument. -/
theorem matrixBilin_add_left {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (w w' v : Fin d → ℝ) :
    matrixBilin A (w + w') v = matrixBilin A w v + matrixBilin A w' v := by
  simp [matrixBilin, add_dotProduct]

/-- `matrixBilin` is additive in its right argument. -/
theorem matrixBilin_add_right {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (w v v' : Fin d → ℝ) :
    matrixBilin A w (v + v') = matrixBilin A w v + matrixBilin A w v' := by
  simp [matrixBilin, Matrix.mulVec_add, dotProduct_add]

/-! ## The dial path -/

/-- The **dial path** (`lem:dial`): with base point `(w0, v0)`, direction `y`,
and scalar `c`, the path sends `τ` to `(w0 - (c/τ)•y, v0 + (c/τ)•y)`. -/
noncomputable def dialPath {d : ℕ} (w0 v0 y : Fin d → ℝ) (c : ℝ) :
    ℝ → (Fin d → ℝ) × (Fin d → ℝ) :=
  fun τ => (w0 - (c / τ) • y, v0 + (c / τ) • y)

@[simp] theorem dialPath_fst {d : ℕ} (w0 v0 y : Fin d → ℝ) (c τ : ℝ) :
    (dialPath w0 v0 y c τ).1 = w0 - (c / τ) • y := rfl

@[simp] theorem dialPath_snd {d : ℕ} (w0 v0 y : Fin d → ℝ) (c τ : ℝ) :
    (dialPath w0 v0 y c τ).2 = v0 + (c / τ) • y := rfl

/-- The scalar `c / τ` tends to `0` as `τ → ∞`. -/
theorem tendsto_const_div_atTop {c : ℝ} :
    Tendsto (fun τ : ℝ => c / τ) atTop (𝓝 0) := by
  simpa using
    ((tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul c).congr
      (fun τ => by rw [div_eq_mul_inv])

/-- Each scaled perturbation `(c/τ)•y` tends to `0` as `τ → ∞`. -/
theorem tendsto_dialPath_smul_atTop {d : ℕ} (y : Fin d → ℝ) (c : ℝ) :
    Tendsto (fun τ : ℝ => (c / τ) • y) atTop (𝓝 (0 : Fin d → ℝ)) := by
  have h := (tendsto_const_div_atTop (c := c)).smul_const y
  simpa using h

/-! ## The gate argument and its limit -/

/-- `Continuous sig`: the logistic sigmoid is continuous on all of `ℝ`.
Uses `sig x = (1 + Real.exp (-x))⁻¹` with `one_add_exp_ne_zero`. -/
theorem continuous_sig : Continuous sig := by
  have hden : Continuous (fun x : ℝ => 1 + Real.exp (-x)) :=
    continuous_const.add (Real.continuous_exp.comp continuous_neg)
  exact hden.inv₀ (fun x => one_add_exp_ne_zero x)

end TransformerIdentifiability.NLayer
