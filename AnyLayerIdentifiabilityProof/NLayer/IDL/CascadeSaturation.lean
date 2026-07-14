import AnyLayerIdentifiabilityProof.NLayer.IDL.SaturationMatching
import AnyLayerIdentifiabilityProof.NLayer.Analytic.SigmoidTail

set_option autoImplicit false

open Filter Topology

namespace TransformerIdentifiability.NLayer

/-!
# Abstract gate saturation (`lem:cascade`(a) analytic core)

The deeper recursion gates have the shape `g(τ) = sig(τ · λ(τ) + b)`, where the
*slope* `λ(τ)` is a continuous quantity built from the running point and the prior
gates.  This file isolates the three purely-analytic saturation conclusions, stated
abstractly in `λ`, that the cascade consumes:

* if `λ(τ) → Λ > 0`, the gate is exponentially close to `1`;
* if `λ(τ) → Λ < 0`, the gate is exponentially close to `0`;
* if `λ(τ)` is itself exponentially close to `0` at rate `r₀`, then for every
  `0 < c < r₀` the gate is exponentially close to `sig b = α`.

All three land in the existing `EventuallyExpClose` package (which carries data, hence
the `def`s) so the trichotomy/matching plumbing can consume them unchanged.
-/

/-- An exponentially-close family converges to its limit value: the `EventuallyExpClose`
data yields topological convergence (`squeeze` against `coeff · exp(-rate·τ) → 0`). -/
theorem EventuallyExpClose.tendsto {f : ℝ → ℝ} {a : ℝ}
    (h : EventuallyExpClose f a) :
    Tendsto f atTop (𝓝 a) := by
  have hsub : Tendsto (fun τ : ℝ => f τ - a) atTop (𝓝 0) := by
    have hbound :
        ∀ᶠ τ : ℝ in atTop, ‖f τ - a‖ ≤ h.coeff * Real.exp (-h.rate * τ) := by
      filter_upwards [eventually_ge_atTop h.start] with τ hτ
      simpa [Real.norm_eq_abs] using h.bound τ hτ
    have hzero :
        Tendsto (fun τ : ℝ => h.coeff * Real.exp (-h.rate * τ)) atTop (𝓝 0) := by
      have hmul : Tendsto (fun τ : ℝ => h.rate * τ) atTop atTop :=
        Tendsto.const_mul_atTop h.rate_pos tendsto_id
      have hexp : Tendsto (fun τ : ℝ => Real.exp (-h.rate * τ)) atTop (𝓝 0) := by
        have hcomp := Real.tendsto_exp_neg_atTop_nhds_zero.comp hmul
        refine hcomp.congr ?_
        intro τ
        simp [Function.comp, neg_mul]
      simpa using hexp.const_mul h.coeff
    exact squeeze_zero_norm' hbound hzero
  have := hsub.add_const a
  simpa using this

namespace EventuallyExpClose

/-- Pointwise equal functions and equal limits preserve exponential closeness. -/
def congr_of_forall_eq {f g : ℝ → ℝ} {a b : ℝ}
    (h : EventuallyExpClose f a) (hfg : ∀ τ : ℝ, f τ = g τ) (hab : a = b) :
    EventuallyExpClose g b := by
  refine ⟨h.rate, h.rate_pos, h.coeff, h.coeff_nonneg, h.start, ?_⟩
  intro τ hτ
  simpa [← hfg τ, ← hab] using h.bound τ hτ

/-- A pointwise constant path is exponentially close with zero error. -/
def of_forall_eq {f : ℝ → ℝ} {a : ℝ} (hfa : ∀ τ : ℝ, f τ = a) :
    EventuallyExpClose f a :=
  (refl a).congr_of_forall_eq (fun τ => (hfa τ).symm) rfl

/-- Negating an exponentially-close family negates its limit. -/
def neg {f : ℝ → ℝ} {a : ℝ} (h : EventuallyExpClose f a) :
    EventuallyExpClose (fun τ => -f τ) (-a) := by
  refine ⟨h.rate, h.rate_pos, h.coeff, h.coeff_nonneg, h.start, ?_⟩
  intro τ hτ
  rw [show (-f τ) - (-a) = -(f τ - a) by ring, abs_neg]
  exact h.bound τ hτ

/-- The sum of exponentially-close families is exponentially close, with the smaller
rate and the sum of the coefficients. -/
def add {f g : ℝ → ℝ} {a b : ℝ}
    (hf : EventuallyExpClose f a) (hg : EventuallyExpClose g b) :
    EventuallyExpClose (fun τ => f τ + g τ) (a + b) := by
  refine ⟨min hf.rate hg.rate, lt_min hf.rate_pos hg.rate_pos,
    hf.coeff + hg.coeff, add_nonneg hf.coeff_nonneg hg.coeff_nonneg,
    max (max hf.start hg.start) 0, ?_⟩
  intro τ hτ
  have hτ_fg : max hf.start hg.start ≤ τ := le_trans (le_max_left _ _) hτ
  have hτ_f : hf.start ≤ τ := le_trans (le_max_left _ _) hτ_fg
  have hτ_g : hg.start ≤ τ := le_trans (le_max_right _ _) hτ_fg
  have hτ0 : 0 ≤ τ := le_trans (le_max_right _ _) hτ
  have hExp_f :
      Real.exp (-hf.rate * τ) ≤ Real.exp (-(min hf.rate hg.rate) * τ) := by
    apply Real.exp_le_exp.mpr
    have hmul : min hf.rate hg.rate * τ ≤ hf.rate * τ :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) hτ0
    nlinarith [hmul]
  have hExp_g :
      Real.exp (-hg.rate * τ) ≤ Real.exp (-(min hf.rate hg.rate) * τ) := by
    apply Real.exp_le_exp.mpr
    have hmul : min hf.rate hg.rate * τ ≤ hg.rate * τ :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hτ0
    nlinarith [hmul]
  have hCoeff_f :
      hf.coeff * Real.exp (-hf.rate * τ) ≤
        hf.coeff * Real.exp (-(min hf.rate hg.rate) * τ) :=
    mul_le_mul_of_nonneg_left hExp_f hf.coeff_nonneg
  have hCoeff_g :
      hg.coeff * Real.exp (-hg.rate * τ) ≤
        hg.coeff * Real.exp (-(min hf.rate hg.rate) * τ) :=
    mul_le_mul_of_nonneg_left hExp_g hg.coeff_nonneg
  calc
    |(f τ + g τ) - (a + b)|
        = |(f τ - a) + (g τ - b)| := by ring_nf
    _ ≤ |f τ - a| + |g τ - b| := abs_add_le _ _
    _ ≤ hf.coeff * Real.exp (-hf.rate * τ) +
        hg.coeff * Real.exp (-hg.rate * τ) :=
      add_le_add (hf.bound τ hτ_f) (hg.bound τ hτ_g)
    _ ≤ hf.coeff * Real.exp (-(min hf.rate hg.rate) * τ) +
        hg.coeff * Real.exp (-(min hf.rate hg.rate) * τ) :=
      add_le_add hCoeff_f hCoeff_g
    _ = (hf.coeff + hg.coeff) * Real.exp (-(min hf.rate hg.rate) * τ) := by
      ring

/-- The difference of exponentially-close families is exponentially close, with the
smaller rate and the sum of the coefficients. -/
def sub {f g : ℝ → ℝ} {a b : ℝ}
    (hf : EventuallyExpClose f a) (hg : EventuallyExpClose g b) :
    EventuallyExpClose (fun τ => f τ - g τ) (a - b) :=
  (hf.add hg.neg).congr_of_forall_eq (fun τ => by ring) (by ring)

/-- Multiplication by a scalar preserves exponential closeness. -/
def const_mul {f : ℝ → ℝ} {a c : ℝ} (h : EventuallyExpClose f a) :
    EventuallyExpClose (fun τ => c * f τ) (c * a) := by
  refine ⟨h.rate, h.rate_pos, |c| * h.coeff,
    mul_nonneg (abs_nonneg c) h.coeff_nonneg, h.start, ?_⟩
  intro τ hτ
  calc
    |c * f τ - c * a|
        = |c| * |f τ - a| := by
      rw [← mul_sub, abs_mul]
    _ ≤ |c| * (h.coeff * Real.exp (-h.rate * τ)) :=
      mul_le_mul_of_nonneg_left (h.bound τ hτ) (abs_nonneg c)
    _ = (|c| * h.coeff) * Real.exp (-h.rate * τ) := by
      ring

/-- Right multiplication by a scalar preserves exponential closeness. -/
def mul_const {f : ℝ → ℝ} {a c : ℝ} (h : EventuallyExpClose f a) :
    EventuallyExpClose (fun τ => f τ * c) (a * c) :=
  (h.const_mul (c := c)).congr_of_forall_eq (fun τ => by ring) (by ring)

end EventuallyExpClose

/-- `lem:cascade`(a), positive branch.  If the slope tends to a positive limit, the gate
`sig(τ·λ(τ) + b)` is `EventuallyExpClose` to `1`. -/
noncomputable def eventuallyExpClose_sig_tau_mul_of_tendsto_pos
    {lam : ℝ → ℝ} {Λ b : ℝ} (hΛ : 0 < Λ)
    (hlam : Tendsto lam atTop (𝓝 Λ)) :
    EventuallyExpClose (fun τ => sig (τ * lam τ + b)) 1 := by
  have hev : ∀ᶠ τ in atTop, Λ / 2 < lam τ :=
    hlam (Ioi_mem_nhds (by linarith))
  refine ⟨Λ / 2, by linarith, Real.exp (-b), (Real.exp_pos _).le,
    max (Classical.choose (eventually_atTop.1 hev)) 0, ?_⟩
  intro τ hτ
  have hT := Classical.choose_spec (eventually_atTop.1 hev)
  have hτT : Classical.choose (eventually_atTop.1 hev) ≤ τ :=
    le_trans (le_max_left _ _) hτ
  have hτ0 : 0 ≤ τ := le_trans (le_max_right _ _) hτ
  have hlamτ : Λ / 2 < lam τ := hT τ hτT
  have habs : |sig (τ * lam τ + b) - 1| = 1 - sig (τ * lam τ + b) := by
    rw [abs_of_nonpos (by linarith [sig_le_one (τ * lam τ + b)])]; ring
  rw [habs]
  calc 1 - sig (τ * lam τ + b)
      ≤ Real.exp (-(τ * lam τ + b)) := one_sub_sig_le_exp_neg _
    _ ≤ Real.exp (-b) * Real.exp (-(Λ / 2) * τ) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hmul : Λ / 2 * τ ≤ lam τ * τ :=
          mul_le_mul_of_nonneg_right hlamτ.le hτ0
        nlinarith [hmul]

/-- `lem:cascade`(a), negative branch.  If the slope tends to a negative limit, the gate
`sig(τ·λ(τ) + b)` is `EventuallyExpClose` to `0`. -/
noncomputable def eventuallyExpClose_sig_tau_mul_of_tendsto_neg
    {lam : ℝ → ℝ} {Λ b : ℝ} (hΛ : Λ < 0)
    (hlam : Tendsto lam atTop (𝓝 Λ)) :
    EventuallyExpClose (fun τ => sig (τ * lam τ + b)) 0 := by
  have hev : ∀ᶠ τ in atTop, lam τ < Λ / 2 :=
    hlam (Iio_mem_nhds (by linarith))
  refine ⟨-(Λ / 2), by linarith, Real.exp b, (Real.exp_pos _).le,
    max (Classical.choose (eventually_atTop.1 hev)) 0, ?_⟩
  intro τ hτ
  have hT := Classical.choose_spec (eventually_atTop.1 hev)
  have hτT : Classical.choose (eventually_atTop.1 hev) ≤ τ :=
    le_trans (le_max_left _ _) hτ
  have hτ0 : 0 ≤ τ := le_trans (le_max_right _ _) hτ
  have hlamτ : lam τ < Λ / 2 := hT τ hτT
  have habs : |sig (τ * lam τ + b) - 0| = sig (τ * lam τ + b) := by
    rw [sub_zero, abs_of_nonneg (sig_pos _).le]
  rw [habs]
  calc sig (τ * lam τ + b)
      ≤ Real.exp (τ * lam τ + b) := sig_le_exp _
    _ ≤ Real.exp b * Real.exp (-(-(Λ / 2)) * τ) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hmul : lam τ * τ ≤ Λ / 2 * τ :=
          mul_le_mul_of_nonneg_right hlamτ.le hτ0
        nlinarith [hmul]

/-- `lem:cascade`(b), `γ ≡ 0` branch.  If the slope is itself exponentially close to `0`
at rate `r₀`, then for every `0 < c < r₀` the gate `sig(τ·λ(τ) + b)` is
`EventuallyExpClose` to `sig b` (the constant `α`).  The stray linear factor `τ` is
absorbed by lowering the rate from `r₀` to `c`. -/
noncomputable def eventuallyExpClose_sig_tau_mul_of_eventuallyExpClose_zero
    {lam : ℝ → ℝ} {b c : ℝ} (h : EventuallyExpClose lam 0)
    (hc : 0 < c) (hc' : c < h.rate) :
    EventuallyExpClose (fun τ => sig (τ * lam τ + b)) (sig b) := by
  have hrc : 0 < Real.exp 1 * (h.rate - c) := mul_pos (Real.exp_pos _) (by linarith)
  refine ⟨c, hc, h.coeff / 4 * (1 / (Real.exp 1 * (h.rate - c))), ?_, max h.start 0, ?_⟩
  · exact mul_nonneg (by linarith [h.coeff_nonneg]) (le_of_lt (div_pos one_pos hrc))
  intro τ hτ
  have hτs : h.start ≤ τ := le_trans (le_max_left _ _) hτ
  have hτ0 : 0 ≤ τ := le_trans (le_max_right _ _) hτ
  have hlam : |lam τ| ≤ h.coeff * Real.exp (-h.rate * τ) := by
    simpa using h.bound τ hτs
  have hτexp :
      τ * Real.exp (-h.rate * τ)
        ≤ (1 / (Real.exp 1 * (h.rate - c))) * Real.exp (-c * τ) := by
    have hfac :
        Real.exp (-h.rate * τ)
          = Real.exp (-(h.rate - c) * τ) * Real.exp (-c * τ) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hfac, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (mul_exp_neg_le (by linarith : 0 < h.rate - c) hτ0) (Real.exp_pos _).le
  have key :
      τ * |lam τ|
        ≤ h.coeff * ((1 / (Real.exp 1 * (h.rate - c))) * Real.exp (-c * τ)) :=
    calc τ * |lam τ|
        ≤ τ * (h.coeff * Real.exp (-h.rate * τ)) :=
          mul_le_mul_of_nonneg_left hlam hτ0
      _ = h.coeff * (τ * Real.exp (-h.rate * τ)) := by ring
      _ ≤ h.coeff * ((1 / (Real.exp 1 * (h.rate - c))) * Real.exp (-c * τ)) :=
          mul_le_mul_of_nonneg_left hτexp h.coeff_nonneg
  calc |sig (τ * lam τ + b) - sig b|
      ≤ |τ * lam τ + b - b| / 4 := abs_sig_sub_sig_le _ _
    _ = τ * |lam τ| / 4 := by
        rw [add_sub_cancel_right, abs_mul, abs_of_nonneg hτ0]
    _ ≤ h.coeff * ((1 / (Real.exp 1 * (h.rate - c))) * Real.exp (-c * τ)) / 4 := by
        linarith [key]
    _ = h.coeff / 4 * (1 / (Real.exp 1 * (h.rate - c))) * Real.exp (-c * τ) := by ring

end TransformerIdentifiability.NLayer
