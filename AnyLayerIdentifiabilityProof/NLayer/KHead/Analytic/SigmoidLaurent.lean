import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.LaurentNormalForm
import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.SigmoidMixtures

set_option autoImplicit false

open Filter Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.KHead

/-! ### Import-safe sigmoid Laurent normal forms

The denominator-unit and punctured factor helpers live upstream in
`SigmoidMixtures.lean`.  These wrappers attach those exact factorizations to the
downstream `LaurentNormalFormAt` API without making the sigmoid file import this
dominance file.
-/

/-- The sigmoid has a residue-one simple Laurent pole at every point of `Π`. -/
theorem csig_normalForm_of_mem_Pi {ζ : ℂ} (hζ : ζ ∈ Pi) :
    LaurentNormalFormAt csig ζ 1 1 := by
  refine ⟨by norm_num, ?_⟩
  exact csig_simplePole_factor_of_mem_Pi hζ

/-- Composition with an analytic map transfers the exact sigmoid pole order. -/
theorem csig_comp_normalForm {H : ℂ -> ℂ} {ξ ϖ cκ : ℂ} {κ : ℕ}
    (hϖ : ϖ ∈ Pi) (hH : AnalyticAt ℂ H ξ) (hHξ : H ξ = ϖ) (hκ : 1 ≤ κ)
    (hNF : LaurentNormalFormAt (fun z => H z - ϖ) ξ (-(κ : ℤ)) cκ) :
    LaurentNormalFormAt (fun z => csig (H z)) ξ (κ : ℤ) cκ⁻¹ := by
  have _ : 1 ≤ κ := hκ
  refine ⟨inv_ne_zero hNF.coeff_ne_zero, ?_⟩
  rcases hNF.factored with ⟨A, hA, hAξ, hHfac⟩
  let g : ℂ -> ℂ := fun z => (A z * csigDenomUnitAt ϖ (H z))⁻¹
  refine ⟨g, ?_, ?_, ?_⟩
  · have hUH :
        AnalyticAt ℂ (fun z : ℂ => csigDenomUnitAt ϖ (H z)) ξ :=
      (csigDenomUnitAt_analyticAt ϖ).comp_of_eq hH hHξ
    have hprod : AnalyticAt ℂ
        (fun z : ℂ => A z * csigDenomUnitAt ϖ (H z)) ξ :=
      hA.mul hUH
    refine hprod.inv ?_
    simp [hAξ, hHξ, csigDenomUnitAt_self_of_mem_Pi hϖ, hNF.coeff_ne_zero]
  · simp [g, hAξ, hHξ, csigDenomUnitAt_self_of_mem_Pi hϖ]
  · filter_upwards [hHfac] with z hfac
    have hden_factor :
        1 + Complex.exp (-(H z)) = (H z - ϖ) * csigDenomUnitAt ϖ (H z) :=
      csig_denom_eq_sub_mul_unit_of_mem_Pi hϖ (H z)
    have hpow :
        (z - ξ) ^ (- (-(κ : ℤ))) = (z - ξ) ^ κ := by
      simp
    calc
      csig (H z) = (1 + Complex.exp (-(H z)))⁻¹ := by
        rfl
      _ = ((A z * (z - ξ) ^ (- (-(κ : ℤ)))) *
            csigDenomUnitAt ϖ (H z))⁻¹ := by
        rw [hden_factor, hfac]
      _ = (((z - ξ) ^ κ * A z) * csigDenomUnitAt ϖ (H z))⁻¹ := by
        rw [hpow]
        ring
      _ = (A z * csigDenomUnitAt ϖ (H z))⁻¹ * (z - ξ) ^ (-(κ : ℤ)) := by
        rw [mul_assoc, _root_.mul_inv_rev]
        simp [_root_.zpow_neg, zpow_natCast]

/-- A nonzero meromorphic germ has an exact Laurent normal form at the center. -/
theorem lem_exact_order_at_center {H : ℂ -> ℂ} {ξ : ℂ}
    (hmer : MeromorphicAt H ξ)
    (hnot : ¬ (H =ᶠ[nhdsWithin ξ ({ξ}ᶜ : Set ℂ)] fun _ => 0)) :
    ∃ (μ : ℤ) (coeff : ℂ), LaurentNormalFormAt H ξ μ coeff := by
  have hfinite : meromorphicOrderAt H ξ ≠ ⊤ := by
    intro htop
    apply hnot
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 htop] with z hz
    exact hz
  obtain ⟨n, hn : meromorphicOrderAt H ξ = n⟩ :=
    Option.ne_none_iff_exists'.mp hfinite
  rcases (meromorphicOrderAt_eq_int_iff hmer).1 hn with ⟨g, hg, hg_ne, hHg⟩
  refine ⟨-n, g ξ, ?_⟩
  refine ⟨hg_ne, ?_⟩
  refine ⟨g, hg, rfl, ?_⟩
  filter_upwards [hHg] with z hz
  simpa [smul_eq_mul, mul_comm] using hz

/-- Exact Laurent normal forms inherit any meromorphic-order upper pole bound. -/
theorem lem_exact_order_at_center_le {H : ℂ -> ℂ} {ξ : ℂ} {m : ℤ}
    (hmer : MeromorphicAt H ξ)
    (hnot : ¬ (H =ᶠ[nhdsWithin ξ ({ξ}ᶜ : Set ℂ)] fun _ => 0))
    (hbound : ((-m : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt H ξ) :
    ∃ (μ : ℤ) (coeff : ℂ), LaurentNormalFormAt H ξ μ coeff ∧ μ ≤ m := by
  rcases lem_exact_order_at_center (H := H) (ξ := ξ) hmer hnot with ⟨μ, coeff, hNF⟩
  refine ⟨μ, coeff, hNF, ?_⟩
  have hbound' : ((-m : ℤ) : WithTop ℤ) ≤ ((-μ : ℤ) : WithTop ℤ) := by
    simpa [hNF.order_eq] using hbound
  have hle : -m ≤ -μ := by
    exact_mod_cast hbound'
  linarith


end TransformerIdentifiability.NLayer.KHead
