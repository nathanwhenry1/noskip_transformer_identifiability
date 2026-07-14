import AnyLayerIdentifiabilityProof.NLayer.Analytic.DialAsymptotics

set_option autoImplicit false

open Filter Topology
open scoped NNReal

namespace TransformerIdentifiability.NLayer

/-!
# Sigmoid tail and Lipschitz bounds (`eq:tail`)

Pure real-analysis estimates on the logistic sigmoid `sig x = (1 + exp(-x))⁻¹`,
isolated at the `Analytic` layer so the cascade saturation argument can consume them.

The three payoffs are:
* the exponential tail bounds `1 - sig x ≤ exp(-x)` and `sig x ≤ exp x`
  (TeX `eq:tail`), which drive gate saturation when the rescaled gate argument
  tends to `±∞`;
* the global Lipschitz bound `|sig u - sig v| ≤ |u - v| / 4` (from `|sig'| ≤ ¼`),
  which controls the `α`-branch of `lem:cascade`;
* the elementary envelope `t · exp(-a t) ≤ 1 / (e a)`, used to absorb a stray
  linear factor `τ` into a slightly smaller exponential rate.
-/

/-- `sig x > 0`. -/
theorem sig_pos (x : ℝ) : 0 < sig x := by
  rw [sig]
  exact inv_pos.mpr (one_add_exp_pos x)

/-- `sig x < 1`. -/
theorem sig_lt_one (x : ℝ) : sig x < 1 := by
  rw [sig]
  rw [inv_lt_one_iff₀]
  right
  have : (0 : ℝ) < Real.exp (-x) := Real.exp_pos _
  linarith

/-- `sig x ≤ 1`. -/
theorem sig_le_one (x : ℝ) : sig x ≤ 1 := (sig_lt_one x).le

/-- The exact complementary identity `1 - sig x = exp(-x) · sig x`. -/
theorem one_sub_sig_eq (x : ℝ) : 1 - sig x = Real.exp (-x) * sig x := by
  have h := sig_mul_denom x
  have hrw : 1 - sig x = sig x * (1 + Real.exp (-x)) - sig x := by rw [h]
  rw [hrw]; ring

/-- `eq:tail` upper branch: `1 - sig x ≤ exp(-x)`. -/
theorem one_sub_sig_le_exp_neg (x : ℝ) : 1 - sig x ≤ Real.exp (-x) := by
  rw [one_sub_sig_eq]
  calc Real.exp (-x) * sig x ≤ Real.exp (-x) * 1 :=
        mul_le_mul_of_nonneg_left (sig_le_one x) (Real.exp_pos _).le
    _ = Real.exp (-x) := mul_one _

/-- `eq:tail` lower branch: `sig x ≤ exp x`. -/
theorem sig_le_exp (x : ℝ) : sig x ≤ Real.exp x := by
  have h1 : (0 : ℝ) < 1 + Real.exp (-x) := one_add_exp_pos x
  rw [sig, inv_eq_one_div, div_le_iff₀ h1]
  have hrw : Real.exp x * (1 + Real.exp (-x)) = Real.exp x + 1 := by
    rw [mul_add, mul_one, ← Real.exp_add]; simp
  rw [hrw]; linarith [Real.exp_pos x]

/-- The sigmoid has derivative `sig x · (1 - sig x)` everywhere. -/
theorem hasDerivAt_sig (x : ℝ) :
    HasDerivAt sig (sig x * (1 - sig x)) x := by
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-x)) x := by
    simpa using (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
  have hden : HasDerivAt (fun x : ℝ => 1 + Real.exp (-x)) (-Real.exp (-x)) x :=
    hexp.const_add 1
  have hne : (1 + Real.exp (-x)) ≠ 0 := one_add_exp_ne_zero x
  have hinv : HasDerivAt sig (- -Real.exp (-x) / (1 + Real.exp (-x)) ^ 2) x :=
    hden.inv hne
  have hval :
      - -Real.exp (-x) / (1 + Real.exp (-x)) ^ 2 = sig x * (1 - sig x) := by
    rw [one_sub_sig_eq, sig]
    field_simp
  rwa [hval] at hinv

/-- The sigmoid is differentiable. -/
theorem differentiable_sig : Differentiable ℝ sig :=
  fun x => (hasDerivAt_sig x).differentiableAt

/-- The derivative of `sig` is `sig x · (1 - sig x)`. -/
theorem deriv_sig (x : ℝ) : deriv sig x = sig x * (1 - sig x) :=
  (hasDerivAt_sig x).deriv

/-- The derivative of `sig` is nonnegative. -/
theorem deriv_sig_nonneg (x : ℝ) : 0 ≤ deriv sig x := by
  rw [deriv_sig]
  exact mul_nonneg (sig_pos x).le (by linarith [sig_le_one x])

/-- The derivative of `sig` is at most `¼` (since `y(1-y) ≤ ¼`). -/
theorem deriv_sig_le (x : ℝ) : deriv sig x ≤ 1 / 4 := by
  rw [deriv_sig]
  nlinarith [sq_nonneg (sig x - 1 / 2), sig_pos x, sig_le_one x]

/-- `sig` is globally `¼`-Lipschitz. -/
theorem lipschitzWith_sig : LipschitzWith (1 / 4 : ℝ≥0) sig := by
  apply lipschitzWith_of_nnnorm_deriv_le differentiable_sig
  intro x
  have hbound : ‖deriv sig x‖ ≤ ((1 / 4 : ℝ≥0) : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (deriv_sig_nonneg x)]
    push_cast
    exact deriv_sig_le x
  exact_mod_cast hbound

/-- The `α`-branch Lipschitz estimate `|sig u - sig v| ≤ |u - v| / 4`. -/
theorem abs_sig_sub_sig_le (u v : ℝ) : |sig u - sig v| ≤ |u - v| / 4 := by
  have h := lipschitzWith_sig.dist_le_mul u v
  rw [Real.dist_eq, Real.dist_eq] at h
  calc |sig u - sig v| ≤ ((1 / 4 : ℝ≥0) : ℝ) * |u - v| := h
    _ = |u - v| / 4 := by push_cast; ring

/-- Elementary exponential envelope: for `a > 0` and `t ≥ 0`,
`t · exp(-a t) ≤ 1 / (e · a)`.  Used to absorb a linear factor `τ` into a
slightly smaller exponential rate. -/
theorem mul_exp_neg_le {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) :
    t * Real.exp (-a * t) ≤ 1 / (Real.exp 1 * a) := by
  -- From `e·y ≤ exp y` with `y = a*t`, i.e. `a*t ≤ exp(a*t)/e`.
  have hkey : Real.exp 1 * (a * t) ≤ Real.exp (a * t) := by
    have h := Real.add_one_le_exp (a * t - 1)
    have : a * t ≤ Real.exp (a * t - 1) := by linarith
    calc Real.exp 1 * (a * t)
        ≤ Real.exp 1 * Real.exp (a * t - 1) :=
          mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
      _ = Real.exp (a * t) := by rw [← Real.exp_add]; ring_nf
  have hexp_pos : 0 < Real.exp (a * t) := Real.exp_pos _
  have hea : 0 < Real.exp 1 * a := by positivity
  rw [neg_mul, Real.exp_neg]
  refine (le_div_iff₀ hea).mpr ?_
  have h2 : t * (Real.exp 1 * a) ≤ Real.exp (a * t) := by nlinarith [hkey]
  calc t * (Real.exp (a * t))⁻¹ * (Real.exp 1 * a)
      = (t * (Real.exp 1 * a)) * (Real.exp (a * t))⁻¹ := by ring
    _ ≤ Real.exp (a * t) * (Real.exp (a * t))⁻¹ :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = 1 := mul_inv_cancel₀ hexp_pos.ne'

end TransformerIdentifiability.NLayer
