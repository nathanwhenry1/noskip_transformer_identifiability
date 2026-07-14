import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.PlaneTopology
import AnyLayerIdentifiabilityProof.NLayer.Analytic.SigmoidTail

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.KHead

/-!
# Sigmoid mixtures for the k-head analytic packets

This file exposes the K04B-facing API for sigmoid poles, finite aggregate
mixtures, and pole transfer.  The hard one-variable analytic facts are reused
from the verified single-head analytic toolkit; this packet adds the k-head
wrappers and the finite-support aggregate bookkeeping used downstream.
-/

/-! ## Re-exported sigmoid pole calculus -/

/-- Complex logistic sigmoid. -/
noncomputable abbrev csig : ℂ -> ℂ :=
  TransformerIdentifiability.NLayer.csig

/-- Local blow-up along punctured neighborhoods. -/
abbrev BlowsUpAt (G : ℂ -> ℂ) (τ : ℂ) : Prop :=
  TransformerIdentifiability.NLayer.BlowsUpAt G τ

/-- Local boundedness along punctured neighborhoods. -/
abbrev PuncturedBoundedAt (G : ℂ -> ℂ) (τ : ℂ) : Prop :=
  TransformerIdentifiability.NLayer.PuncturedBoundedAt G τ

/-- Punctured-neighborhood isolation from an exceptional set. -/
abbrev IsPuncturedIsolated (E : Set ℂ) (τ : ℂ) : Prop :=
  TransformerIdentifiability.NLayer.IsPuncturedIsolated E τ

/-- The affine pole indexed by `n` for `τ ↦ σ(slopeτ+b)`. -/
noncomputable abbrev affineSigmoidPole (b lam : ℝ) (n : ℤ) : ℂ :=
  TransformerIdentifiability.NLayer.sigmoidPole b lam n

/-- The affine pole progression `P(slope)`. -/
noncomputable abbrev affineSigmoidPoleSet (b lam : ℝ) : Set ℂ :=
  TransformerIdentifiability.NLayer.firstPoleSet b lam

/-- **K04B.E.lem-sigmoid-poles.S/P**.

The complex sigmoid is meromorphic at every point. -/
theorem csig_meromorphicAt (z : ℂ) : MeromorphicAt csig z :=
  TransformerIdentifiability.NLayer.csig_meromorphicAt z

/-- The sigmoid is analytic away from the odd-pi pole set. -/
theorem csig_analyticAt_of_notMem_Pi {z : ℂ} (hz : z ∉ Pi) :
    AnalyticAt ℂ csig z := by
  exact TransformerIdentifiability.NLayer.csig_analyticAt
    (by
      intro hzero
      exact hz ((mem_Pi_iff_denom_zero z).2 hzero))

/-- The sigmoid blows up at every point of `Π`. -/
theorem csig_blowsUpAt_of_mem_Pi {z : ℂ} (hz : z ∈ Pi) :
    BlowsUpAt csig z := by
  have hzOdd : z ∈ TransformerIdentifiability.NLayer.oddPiI := by
    simpa [Pi, sigmoidPoleSet_eq_oddPiI] using hz
  have hid :
      Tendsto (fun w : ℂ => w) (nhdsWithin z ({z}ᶜ : Set ℂ)) (nhds z) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hnotacc : z ∉ acc Pi :=
    Pi_closedDiscrete.noAccum z (by simp)
  have hne : ∀ᶠ w in nhdsWithin z ({z}ᶜ : Set ℂ),
      1 + Complex.exp (-w) ≠ 0 := by
    have havoid :
        ∀ᶠ w in nhdsWithin z ({z}ᶜ : Set ℂ), w ∉ Pi :=
      TransformerIdentifiability.NLayer.eventually_notMem_of_not_mem_acc hnotacc
    filter_upwards [havoid] with w hw hzero
    exact hw ((mem_Pi_iff_denom_zero w).2 hzero)
  exact TransformerIdentifiability.NLayer.csig_blowsUpAt_of_tendsto_pole
    (H := fun w : ℂ => w) hzOdd hid hne

/-- The sigmoid is not analytic at a pole. -/
theorem csig_not_analyticAt_of_mem_Pi {z : ℂ} (hz : z ∈ Pi) :
    ¬ AnalyticAt ℂ csig z := by
  intro h
  exact TransformerIdentifiability.NLayer.no_eventuallyEq_of_continuousAt_of_blowsUpAt
    h.continuousAt Filter.EventuallyEq.rfl (csig_blowsUpAt_of_mem_Pi hz)

/-- The exact analytic locus of the complex sigmoid. -/
theorem csig_analyticAt_iff_notMem_Pi (z : ℂ) :
    AnalyticAt ℂ csig z ↔ z ∉ Pi := by
  constructor
  · intro h hz
    exact csig_not_analyticAt_of_mem_Pi hz h
  · exact csig_analyticAt_of_notMem_Pi

/-! ### Exact local denominator factors -/

/-- The analytic unit obtained by dividing the sigmoid denominator by `z - ζ`.

At points `ζ ∈ Π`, this is the local unit in
`1 + exp(-z) = (z - ζ) * csigDenomUnitAt ζ z`, normalized to value `1`.
This is the concrete denominator factor used by the K06B exact sigmoid normal
forms. -/
noncomputable def csigDenomUnitAt (ζ : ℂ) : ℂ -> ℂ :=
  dslope (fun z : ℂ => 1 + Complex.exp (-z)) ζ

/-- The denominator unit is analytic at its center. -/
theorem csigDenomUnitAt_analyticAt (ζ : ℂ) :
    AnalyticAt ℂ (csigDenomUnitAt ζ) ζ := by
  have hD : AnalyticAt ℂ (fun z : ℂ => 1 + Complex.exp (-z)) ζ := by
    simpa using TransformerIdentifiability.NLayer.denom_analytic ζ
  rcases hD with ⟨p, hp⟩
  exact ⟨p.fslope, by simpa [csigDenomUnitAt] using hp.has_fpower_series_dslope_fslope⟩

/-- At a sigmoid pole, the derivative of the denominator is `1`. -/
theorem csig_denom_deriv_eq_one_of_mem_Pi {ζ : ℂ} (hζ : ζ ∈ Pi) :
    deriv (fun z : ℂ => 1 + Complex.exp (-z)) ζ = 1 := by
  have hzero : 1 + Complex.exp (-ζ) = 0 := (mem_Pi_iff_denom_zero ζ).1 hζ
  have hexpζ : Complex.exp (-ζ) = -1 := by
    linear_combination hzero
  have hderiv : HasDerivAt (fun z : ℂ => 1 + Complex.exp (-z)) 1 ζ := by
    have hneg : HasDerivAt (fun z : ℂ => -z) (-1 : ℂ) ζ := by
      simpa using (hasDerivAt_id ζ).neg
    have hexp : HasDerivAt (fun z : ℂ => Complex.exp (-z))
        (Complex.exp (-ζ) * (-1 : ℂ)) ζ := hneg.cexp
    have h := (hasDerivAt_const ζ (1 : ℂ)).add hexp
    convert h using 1
    rw [hexpζ]
    ring
  exact hderiv.deriv

/-- The denominator unit has value `1` at each point of `Π`. -/
theorem csigDenomUnitAt_self_of_mem_Pi {ζ : ℂ} (hζ : ζ ∈ Pi) :
    csigDenomUnitAt ζ ζ = 1 := by
  simp [csigDenomUnitAt, csig_denom_deriv_eq_one_of_mem_Pi hζ]

/-- Exact global factorization of the sigmoid denominator at a pole. -/
theorem csig_denom_eq_sub_mul_unit_of_mem_Pi {ζ : ℂ} (hζ : ζ ∈ Pi) (z : ℂ) :
    1 + Complex.exp (-z) = (z - ζ) * csigDenomUnitAt ζ z := by
  have hzero :
      (fun w : ℂ => 1 + Complex.exp (-w)) ζ = 0 :=
    (mem_Pi_iff_denom_zero ζ).1 hζ
  have h := sub_smul_dslope_of_zero
    (f := fun w : ℂ => 1 + Complex.exp (-w)) (a := ζ) hzero z
  simpa [csigDenomUnitAt, smul_eq_mul] using h.symm

/-- Residue-one punctured Laurent factorization of `csig` at each point of `Π`.

This is the body of `csig_normalForm_of_mem_Pi` without mentioning the
downstream `LaurentNormalFormAt` type, which currently lives in a file importing
this one. -/
theorem csig_simplePole_factor_of_mem_Pi {ζ : ℂ} (hζ : ζ ∈ Pi) :
    ∃ g : ℂ -> ℂ, AnalyticAt ℂ g ζ ∧ g ζ = 1 ∧
      ∀ᶠ z in nhdsWithin ζ ({ζ}ᶜ : Set ℂ),
        csig z = g z * (z - ζ) ^ (-1 : ℤ) := by
  refine ⟨fun z => (csigDenomUnitAt ζ z)⁻¹, ?_, ?_, ?_⟩
  · exact (csigDenomUnitAt_analyticAt ζ).inv
      (by simp [csigDenomUnitAt_self_of_mem_Pi hζ])
  · simp [csigDenomUnitAt_self_of_mem_Pi hζ]
  · filter_upwards [self_mem_nhdsWithin] with z _hz
    have hfactor : 1 + Complex.exp (-z) = (z - ζ) * csigDenomUnitAt ζ z :=
      csig_denom_eq_sub_mul_unit_of_mem_Pi hζ z
    calc
      csig z = (1 + Complex.exp (-z))⁻¹ := by
        rfl
      _ = ((z - ζ) * csigDenomUnitAt ζ z)⁻¹ := by rw [hfactor]
      _ = (csigDenomUnitAt ζ z)⁻¹ * (z - ζ)⁻¹ := by
        rw [mul_inv_rev]
      _ = (csigDenomUnitAt ζ z)⁻¹ * (z - ζ) ^ (-1 : ℤ) := by
        simp

/-- Composition form of the exact sigmoid pole factorization.

If `H - ϖ` is locally `(z - ξ)^κ * A z` with `A ξ = cκ ≠ 0` and
`ϖ ∈ Π`, then `csig ∘ H` has the corresponding punctured Laurent factor with
leading coefficient `cκ⁻¹`.  This is the reusable factor-level helper needed to
wrap `csig_comp_normalForm` once `LaurentNormalFormAt` is available upstream of
this file. -/
theorem csig_comp_simplePole_factor_of_eventually_eq_pow_mul
    {H : ℂ -> ℂ} {ξ ϖ cκ : ℂ} {κ : ℕ}
    (hϖ : ϖ ∈ Pi) (hH : AnalyticAt ℂ H ξ) (hHξ : H ξ = ϖ)
    (_hκ : 1 ≤ κ) {A : ℂ -> ℂ}
    (hA : AnalyticAt ℂ A ξ) (hAξ : A ξ = cκ) (hcκ : cκ ≠ 0)
    (hHfactor : ∀ᶠ z in nhds ξ, H z - ϖ = (z - ξ) ^ κ * A z) :
    ∃ g : ℂ -> ℂ, AnalyticAt ℂ g ξ ∧ g ξ = cκ⁻¹ ∧
      ∀ᶠ z in nhdsWithin ξ ({ξ}ᶜ : Set ℂ),
        csig (H z) = g z * (z - ξ) ^ (-(κ : ℤ)) := by
  let g : ℂ -> ℂ := fun z => (A z * csigDenomUnitAt ϖ (H z))⁻¹
  refine ⟨g, ?_, ?_, ?_⟩
  · have hUH :
        AnalyticAt ℂ (fun z : ℂ => csigDenomUnitAt ϖ (H z)) ξ :=
      (csigDenomUnitAt_analyticAt ϖ).comp_of_eq hH hHξ
    have hprod : AnalyticAt ℂ
        (fun z : ℂ => A z * csigDenomUnitAt ϖ (H z)) ξ :=
      hA.mul hUH
    refine hprod.inv ?_
    simp [hAξ, hHξ, csigDenomUnitAt_self_of_mem_Pi hϖ, hcκ]
  · simp [g, hAξ, hHξ, csigDenomUnitAt_self_of_mem_Pi hϖ]
  · filter_upwards [hHfactor.filter_mono nhdsWithin_le_nhds] with z hfac
    have hden_factor :
        1 + Complex.exp (-(H z)) = (H z - ϖ) * csigDenomUnitAt ϖ (H z) :=
      csig_denom_eq_sub_mul_unit_of_mem_Pi hϖ (H z)
    calc
      csig (H z) = (1 + Complex.exp (-(H z)))⁻¹ := by
        rfl
      _ = (((z - ξ) ^ κ * A z) * csigDenomUnitAt ϖ (H z))⁻¹ := by
        rw [hden_factor, hfac]
      _ = (A z * csigDenomUnitAt ϖ (H z))⁻¹ * (z - ξ) ^ (-(κ : ℤ)) := by
        rw [mul_assoc, mul_inv_rev, mul_inv_rev]
        simp [zpow_neg, zpow_natCast]

/-- Membership in the affine pole progression is the same as hitting `Π`. -/
theorem mem_affineSigmoidPoleSet_iff {b lam : ℝ} (hlam : lam ≠ 0) (τ : ℂ) :
    τ ∈ affineSigmoidPoleSet b lam ↔ (lam : ℂ) * τ + (b : ℂ) ∈ Pi := by
  constructor
  · rintro ⟨n, rfl⟩
    rw [Pi, sigmoidPoleSet_eq_oddPiI, TransformerIdentifiability.NLayer.oddPiI]
    refine ⟨n, ?_⟩
    have hlamC : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam
    rw [TransformerIdentifiability.NLayer.sigmoidPole]
    field_simp [hlamC]
    push_cast
    ring
  · intro hτ
    rw [Pi, sigmoidPoleSet_eq_oddPiI,
      TransformerIdentifiability.NLayer.oddPiI] at hτ
    rcases hτ with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hlamC : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam
    apply (mul_left_inj' hlamC).mp
    calc
      affineSigmoidPole b lam n * (lam : ℂ)
          = (((2 * (n : ℂ) + 1) * (Real.pi : ℂ) * Complex.I) - (b : ℂ)) := by
            simp [affineSigmoidPole, TransformerIdentifiability.NLayer.sigmoidPole, hlamC]
      _ = τ * (lam : ℂ) := by
          rw [← hn]
          ring

/-- The real part of every affine sigmoid pole lies on one vertical line. -/
theorem affineSigmoidPole_re {b lam : ℝ} (hlam : lam ≠ 0) (n : ℤ) :
    (affineSigmoidPole b lam n).re = -b / lam :=
  TransformerIdentifiability.NLayer.sigmoidPole_re hlam n

/-- Affine pole progressions are closed and discrete in the plane. -/
theorem affineSigmoidPoleSet_closedDiscrete (b lam : ℝ) (hlam : lam ≠ 0) :
    ClosedDiscreteIn (affineSigmoidPoleSet b lam) Set.univ := by
  let H : ℂ -> ℂ := fun τ => (lam : ℂ) * τ + (b : ℂ)
  have hH : AnalyticOnNhd ℂ H Set.univ := by
    intro τ _hτ
    exact (analyticAt_const.mul analyticAt_id).add analyticAt_const
  have hHnonconst : ∀ c : ℂ, ¬ Set.EqOn H (fun _ : ℂ => c) Set.univ := by
    intro c hEq
    have h0 : (b : ℂ) = c := by
      simpa [H] using hEq (by simp : (0 : ℂ) ∈ (Set.univ : Set ℂ))
    have h1 : (lam : ℂ) + (b : ℂ) = c := by
      simpa [H] using hEq (by simp : (1 : ℂ) ∈ (Set.univ : Set ℂ))
    have hlamC : (lam : ℂ) = 0 := by
      calc
        (lam : ℂ) = (lam : ℂ) + (b : ℂ) - (b : ℂ) := by ring
        _ = c - (b : ℂ) := by rw [h1]
        _ = 0 := by rw [← h0]; ring
    exact (Complex.ofReal_ne_zero.mpr hlam) hlamC
  have hpre :
      ClosedDiscreteIn (Set.univ ∩ H ⁻¹' Pi) Set.univ :=
    closedDiscrete_preimage isOpen_univ isPreconnected_univ hH hHnonconst Pi_closedDiscrete
  have hEq : Set.univ ∩ H ⁻¹' Pi = affineSigmoidPoleSet b lam := by
    ext τ
    simp [H, mem_affineSigmoidPoleSet_iff hlam τ]
  simpa [hEq] using hpre

/-- Affine pole progressions are countable. -/
theorem affineSigmoidPoleSet_countable (b lam : ℝ) (hlam : lam ≠ 0) :
    (affineSigmoidPoleSet b lam).Countable :=
  (affineSigmoidPoleSet_closedDiscrete b lam hlam).countable

/-- Affine pole progressions are closed. -/
theorem affineSigmoidPoleSet_closed (b lam : ℝ) (hlam : lam ≠ 0) :
    IsClosed (affineSigmoidPoleSet b lam) := by
  simpa using (affineSigmoidPoleSet_closedDiscrete b lam hlam).isClosed_rel

/-- Real points are never affine sigmoid poles when the slope is nonzero. -/
theorem ofReal_notMem_affineSigmoidPoleSet (b lam x : ℝ) (hlam : lam ≠ 0) :
    (x : ℂ) ∉ affineSigmoidPoleSet b lam := by
  intro hx
  have harg : (lam : ℂ) * (x : ℂ) + (b : ℂ) ∈ Pi :=
    (mem_affineSigmoidPoleSet_iff hlam (x : ℂ)).1 hx
  have hargReal :
      (lam : ℂ) * (x : ℂ) + (b : ℂ) = ((lam * x + b : ℝ) : ℂ) := by
    norm_num
  rw [hargReal] at harg
  exact ofReal_notMem_Pi (lam * x + b) harg

/-- Distinct nonzero slopes have disjoint progressions when `b ≠ 0`. -/
theorem affineSigmoidPoleSet_inter_eq_empty_of_ne {b lam mu : ℝ}
    (hb : b ≠ 0) (hlam : lam ≠ 0) (hmu : mu ≠ 0) (hneq : lam ≠ mu) :
    affineSigmoidPoleSet b lam ∩ affineSigmoidPoleSet b mu = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.2
  intro τ hτ
  rcases hτ.1 with ⟨n, hn⟩
  rcases hτ.2 with ⟨m, hm⟩
  have hpole :
      TransformerIdentifiability.NLayer.sigmoidPole b lam n =
        TransformerIdentifiability.NLayer.sigmoidPole b mu m := by
    rw [hn, hm]
  have hmulam : mu = lam :=
    TransformerIdentifiability.NLayer.slope_eq_of_sigmoidPole_eq
      (b := b) (lam := mu) (lam' := lam) hb hmu hlam hpole
  exact hneq hmulam.symm

/-- Away from its affine pole progression, `τ ↦ σ(slopeτ+b)` is analytic. -/
theorem affine_csig_analyticAt_of_notMem_poleSet {b lam : ℝ} {τ : ℂ}
    (hlam : lam ≠ 0) (hτ : τ ∉ affineSigmoidPoleSet b lam) :
    AnalyticAt ℂ (fun z : ℂ => csig ((lam : ℂ) * z + (b : ℂ))) τ := by
  have hden :
      1 + Complex.exp (-((lam : ℂ) * τ + (b : ℂ))) ≠ 0 := by
    intro hzero
    exact hτ ((mem_affineSigmoidPoleSet_iff hlam τ).2
      ((mem_Pi_iff_denom_zero ((lam : ℂ) * τ + (b : ℂ))).2 hzero))
  simpa [csig, TransformerIdentifiability.NLayer.csig] using
    (TransformerIdentifiability.NLayer.affine_denom_analyticAt b lam τ).inv hden

/-- Zero-slope sigmoid terms are constant, hence analytic. -/
theorem affine_csig_analyticAt_zero_slope (b : ℝ) (τ : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => csig ((0 : ℂ) * z + (b : ℂ))) τ := by
  simpa using (analyticAt_const :
    AnalyticAt ℂ (fun _ : ℂ => csig (b : ℂ)) τ)

/-- Affine sigmoid terms blow up at their indexed poles. -/
theorem affine_csig_blowsUpAt_sigmoidPole (b lam : ℝ) (hlam : lam ≠ 0) (n : ℤ) :
    BlowsUpAt (fun τ : ℂ => csig ((lam : ℂ) * τ + (b : ℂ)))
      (affineSigmoidPole b lam n) :=
  TransformerIdentifiability.NLayer.affine_csig_blowsUpAt_sigmoidPole b lam hlam n

/-! ## Aggregate finite sigmoid mixtures -/

/-- Aggregate coefficient at slope `slope`. -/
noncomputable def aggregateCoeff {p N : Nat}
    (M : Fin p -> Fin N -> ℂ) (lam : Fin p -> ℝ) (slope : ℝ) : Fin N -> ℂ :=
  ∑ h : Fin p, if lam h = slope then M h else 0

/-- Finite support of nonzero aggregate nonzero slopes. -/
noncomputable def slopeSupportFinset {p N : Nat}
    (M : Fin p -> Fin N -> ℂ) (lam : Fin p -> ℝ) : Finset ℝ :=
  (Finset.univ.image lam).filter fun slope => slope ≠ 0 ∧ aggregateCoeff M lam slope ≠ 0

/-- Singular set attached to the nonzero aggregate support. -/
noncomputable def mixtureSingularSet {p N : Nat} (b : ℝ)
    (M : Fin p -> Fin N -> ℂ) (lam : Fin p -> ℝ) : Set ℂ :=
  ⋃ slope ∈ slopeSupportFinset M lam, affineSigmoidPoleSet b slope

/-- A finite vector-valued sigmoid mixture. -/
noncomputable def sigmoidMixture {p N : Nat} (b : ℝ)
    (H : ℂ -> Fin N -> ℂ) (M : Fin p -> Fin N -> ℂ) (lam : Fin p -> ℝ) :
    ℂ -> Fin N -> ℂ :=
  fun τ => H τ + ∑ h : Fin p, csig ((lam h : ℂ) * τ + (b : ℂ)) • M h

/-- The part of a mixture with slope `slope` removed and replaced by a holomorphic
aggregate term in local pole calculations. -/
noncomputable def sigmoidMixtureRegularPartAtSlope {p N : Nat} (b : ℝ)
    (H : ℂ -> Fin N -> ℂ) (M : Fin p -> Fin N -> ℂ) (lam : Fin p -> ℝ)
    (slope : ℝ) : ℂ -> Fin N -> ℂ :=
  fun τ => H τ +
    ∑ h : Fin p,
      if lam h = slope then 0
      else csig ((lam h : ℂ) * τ + (b : ℂ)) • M h

theorem aggregateCoeff_eq_zero_of_notMem_image {p N : Nat}
    {M : Fin p -> Fin N -> ℂ} {lam : Fin p -> ℝ} {slope : ℝ}
    (hslope : slope ∉ Finset.univ.image lam) :
    aggregateCoeff M lam slope = 0 := by
  classical
  rw [aggregateCoeff]
  exact Finset.sum_eq_zero fun h _hh => by
    have hne : lam h ≠ slope := by
      intro heq
      exact hslope (Finset.mem_image.mpr ⟨h, Finset.mem_univ h, heq⟩)
    simp [hne]

theorem mem_slopeSupportFinset_iff {p N : Nat}
    (M : Fin p -> Fin N -> ℂ) (lam : Fin p -> ℝ) (slope : ℝ) :
    slope ∈ slopeSupportFinset M lam ↔
      slope ≠ 0 ∧ aggregateCoeff M lam slope ≠ 0 := by
  classical
  constructor
  · intro hslope
    have hslope' :
        (∃ h : Fin p, lam h = slope) ∧
          slope ≠ 0 ∧ aggregateCoeff M lam slope ≠ 0 := by
      simpa [slopeSupportFinset] using hslope
    exact hslope'.2
  · intro hslope
    have himage : slope ∈ Finset.univ.image lam := by
      by_contra hnot
      exact hslope.2 (aggregateCoeff_eq_zero_of_notMem_image
        (M := M) (lam := lam) hnot)
    simp [slopeSupportFinset, himage, hslope]

/-- The aggregate at an isolated separated slope is the corresponding head coefficient. -/
theorem aggregateCoeff_eq_single_of_pairwise {p N : Nat}
    {M : Fin p -> Fin N -> ℂ} {lam : Fin p -> ℝ}
    (hpair : Pairwise fun i j => lam i ≠ lam j) (h : Fin p) :
    aggregateCoeff M lam (lam h) = M h := by
  classical
  rw [aggregateCoeff]
  exact
    (Finset.sum_eq_single
      (s := (Finset.univ : Finset (Fin p)))
      (f := fun i : Fin p => if lam i = lam h then M i else (0 : Fin N -> ℂ))
      h
      (by
        intro i _hi hih
        have hne : lam i ≠ lam h := hpair hih
        simp [hne])
      (by
        intro hh
        simp at hh)).trans
      (by simp)

/-- Under separated nonzero nontrivial heads, the aggregate support is exactly the
image of the head slopes. -/
theorem slopeSupportFinset_eq_image_of_pairwise_nonzero {p N : Nat}
    {M : Fin p -> Fin N -> ℂ} {lam : Fin p -> ℝ}
    (hpair : Pairwise fun i j => lam i ≠ lam j)
    (hlam : ∀ h : Fin p, lam h ≠ 0)
    (hM : ∀ h : Fin p, M h ≠ 0) :
    slopeSupportFinset M lam = Finset.univ.image lam := by
  classical
  ext slope
  constructor
  · intro hslope
    have hslope' :
        slope ∈ (Finset.univ.image lam).filter
          (fun slope => slope ≠ 0 ∧ aggregateCoeff M lam slope ≠ 0) := by
      simpa [slopeSupportFinset] using hslope
    exact (Finset.mem_filter.mp hslope').1
  · intro hslope
    rcases Finset.mem_image.mp hslope with ⟨h, _hh, rfl⟩
    rw [mem_slopeSupportFinset_iff]
    exact ⟨hlam h, by simpa [aggregateCoeff_eq_single_of_pairwise hpair h] using hM h⟩

/-- Aggregate equality on nonzero slopes identifies the finite aggregate supports. -/
theorem slopeSupportFinset_eq_of_aggregateCoeff_eq {p q N : Nat}
    {M : Fin p -> Fin N -> ℂ} {lam : Fin p -> ℝ}
    {M' : Fin q -> Fin N -> ℂ} {lam' : Fin q -> ℝ}
    (hagg : ∀ slope : ℝ, slope ≠ 0 -> aggregateCoeff M lam slope = aggregateCoeff M' lam' slope) :
    slopeSupportFinset M lam = slopeSupportFinset M' lam' := by
  classical
  ext slope
  by_cases hslope0 : slope = 0
  · simp [mem_slopeSupportFinset_iff, hslope0]
  · rw [mem_slopeSupportFinset_iff, mem_slopeSupportFinset_iff, hagg slope hslope0]

/-- Aggregate equality identifies the corresponding singular sets. -/
theorem mixtureSingularSet_eq_of_aggregateCoeff_eq {p q N : Nat} (b : ℝ)
    {M : Fin p -> Fin N -> ℂ} {lam : Fin p -> ℝ}
    {M' : Fin q -> Fin N -> ℂ} {lam' : Fin q -> ℝ}
    (hagg : ∀ slope : ℝ, slope ≠ 0 -> aggregateCoeff M lam slope = aggregateCoeff M' lam' slope) :
    mixtureSingularSet b M lam = mixtureSingularSet b M' lam' := by
  classical
  simp [mixtureSingularSet, slopeSupportFinset_eq_of_aggregateCoeff_eq hagg]

/-- The mixture singular set is a finite union of closed-discrete pole progressions. -/
theorem mixtureSingularSet_closedDiscrete {p N : Nat} (b : ℝ)
    (M : Fin p -> Fin N -> ℂ) (lam : Fin p -> ℝ) :
    ClosedDiscreteIn (mixtureSingularSet b M lam) Set.univ := by
  classical
  rw [mixtureSingularSet]
  refine closedDiscreteIn_finset_biUnion (slopeSupportFinset M lam) isOpen_univ ?_
  intro slope hslope
  have hslopene : slope ≠ 0 := (mem_slopeSupportFinset_iff M lam slope).1 hslope |>.1
  exact affineSigmoidPoleSet_closedDiscrete b slope hslopene

/-- The mixture singular set is countable. -/
theorem mixtureSingularSet_countable {p N : Nat} (b : ℝ)
    (M : Fin p -> Fin N -> ℂ) (lam : Fin p -> ℝ) :
    (mixtureSingularSet b M lam).Countable :=
  (mixtureSingularSet_closedDiscrete b M lam).countable

/-- The mixture singular set is closed. -/
theorem mixtureSingularSet_closed {p N : Nat} (b : ℝ)
    (M : Fin p -> Fin N -> ℂ) (lam : Fin p -> ℝ) :
    IsClosed (mixtureSingularSet b M lam) := by
  simpa using (mixtureSingularSet_closedDiscrete b M lam).isClosed_rel

/-- The regular domain of a finite aggregate mixture is a plane domain. -/
theorem mixtureRegularDomain_planeDomain {p N : Nat} (b : ℝ)
    (M : Fin p -> Fin N -> ℂ) (lam : Fin p -> ℝ) :
    PlaneDomain (mixtureSingularSet b M lam)ᶜ :=
  countable_closed_compl_planeDomain
    (mixtureSingularSet_countable b M lam)
    (mixtureSingularSet_closed b M lam)

/-- Mixture singular sets avoid the real axis. -/
theorem ofReal_notMem_mixtureSingularSet {p N : Nat} (b x : ℝ)
    (M : Fin p -> Fin N -> ℂ) (lam : Fin p -> ℝ) :
    (x : ℂ) ∉ mixtureSingularSet b M lam := by
  classical
  intro hx
  rw [mixtureSingularSet] at hx
  simp only [Set.mem_iUnion, exists_prop] at hx
  rcases hx with ⟨slope, hslope, hxslope⟩
  have hslopene : slope ≠ 0 := (mem_slopeSupportFinset_iff M lam slope).1 hslope |>.1
  exact ofReal_notMem_affineSigmoidPoleSet b slope x hslopene hxslope

/-- Algebraic local decomposition by the aggregate coefficient at a slope. -/
theorem sigmoidMixture_decompose_by_aggregate {p N : Nat} (b slope : ℝ)
    (H : ℂ -> Fin N -> ℂ) (M : Fin p -> Fin N -> ℂ) (lam : Fin p -> ℝ)
    (τ : ℂ) :
    sigmoidMixture b H M lam τ =
      sigmoidMixtureRegularPartAtSlope b H M lam slope τ +
        csig ((slope : ℂ) * τ + (b : ℂ)) • aggregateCoeff M lam slope := by
  classical
  ext j
  simp only [sigmoidMixture, sigmoidMixtureRegularPartAtSlope, aggregateCoeff,
    Pi.add_apply, Finset.sum_apply, Pi.smul_apply]
  rw [Finset.smul_sum, add_assoc]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro h _hh
  by_cases hslope : lam h = slope
  · simp [hslope]
  · simp [hslope]

/-- Coordinate form of the aggregate decomposition. -/
theorem sigmoidMixture_decompose_by_aggregate_coord {p N : Nat} (b slope : ℝ)
    (H : ℂ -> Fin N -> ℂ) (M : Fin p -> Fin N -> ℂ) (lam : Fin p -> ℝ)
    (τ : ℂ) (j : Fin N) :
    sigmoidMixture b H M lam τ j =
      sigmoidMixtureRegularPartAtSlope b H M lam slope τ j +
        csig ((slope : ℂ) * τ + (b : ℂ)) * aggregateCoeff M lam slope j := by
  have h := congrArg (fun v : Fin N -> ℂ => v j)
    (sigmoidMixture_decompose_by_aggregate b slope H M lam τ)
  simpa [Pi.smul_apply] using h

/-- Regroup a sigmoid mixture by aggregate slope, coordinatewise.  This is the
analytic form that removes cancelled aggregate slopes from the singular set. -/
theorem sigmoidMixture_coord_eq_sum_image_aggregate {p N : Nat} (b : ℝ)
    (H : ℂ -> Fin N -> ℂ) (M : Fin p -> Fin N -> ℂ) (lam : Fin p -> ℝ)
    (τ : ℂ) (j : Fin N) :
    sigmoidMixture b H M lam τ j =
      H τ j + ∑ slope ∈ Finset.univ.image lam,
        csig ((slope : ℂ) * τ + (b : ℂ)) *
          aggregateCoeff M lam slope j := by
  classical
  simp only [sigmoidMixture, Pi.add_apply, Finset.sum_apply, Pi.smul_apply]
  congr 1
  symm
  simp only [aggregateCoeff]
  have hgroup :=
    (Finset.sum_image'
      (s := (Finset.univ : Finset (Fin p)))
      (g := lam)
      (f := fun slope : ℝ =>
        csig ((slope : ℂ) * τ + (b : ℂ)) *
          ∑ h : Fin p, if lam h = slope then M h j else 0)
      (h := fun h : Fin p =>
        csig (((lam h : ℝ) : ℂ) * τ + (b : ℂ)) * M h j)
      ?_)
  have hleft :
      (∑ x ∈ Finset.univ.image lam,
        csig ((x : ℂ) * τ + (b : ℂ)) *
          (∑ c : Fin p, if lam c = x then M c else 0) j) =
      (∑ x ∈ Finset.univ.image lam,
        csig ((x : ℂ) * τ + (b : ℂ)) *
          ∑ c : Fin p, if lam c = x then M c j else 0) := by
    refine Finset.sum_congr rfl ?_
    intro x _hx
    congr 1
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl ?_
    intro c _hc
    by_cases hc : lam c = x
    · simp [hc]
    · simp [hc]
  exact hleft.trans hgroup
  intro i _hi
  calc
    csig (((lam i : ℝ) : ℂ) * τ + (b : ℂ)) *
        ∑ h : Fin p, (if lam h = lam i then M h j else 0)
        = ∑ h : Fin p,
          csig (((lam i : ℝ) : ℂ) * τ + (b : ℂ)) *
            (if lam h = lam i then M h j else 0) := by
          rw [Finset.mul_sum]
    _ = ∑ h : Fin p,
          if lam h = lam i then
            csig (((lam h : ℝ) : ℂ) * τ + (b : ℂ)) * M h j
          else 0 := by
          refine Finset.sum_congr rfl ?_
          intro h _hh
          by_cases hh : lam h = lam i
          · simp [hh]
          · simp [hh]
    _ = ∑ h ∈ (Finset.univ : Finset (Fin p)) with lam h = lam i,
          csig (((lam h : ℝ) : ℂ) * τ + (b : ℂ)) * M h j := by
          rw [Finset.sum_filter]

/-- Coordinatewise holomorphy of a finite sigmoid mixture away from its aggregate
singular set. -/
theorem sigmoidMixture_coord_analyticOnNhd_mixtureSingularSet_compl {p N : Nat} (b : ℝ)
    (H : ℂ -> Fin N -> ℂ) (M : Fin p -> Fin N -> ℂ) (lam : Fin p -> ℝ)
    (hH : ∀ j : Fin N,
      AnalyticOnNhd ℂ (fun τ : ℂ => H τ j) (mixtureSingularSet b M lam)ᶜ) :
    ∀ j : Fin N,
      AnalyticOnNhd ℂ (fun τ : ℂ => sigmoidMixture b H M lam τ j)
        (mixtureSingularSet b M lam)ᶜ := by
  classical
  intro j τ hτ
  have hrepr :
      (fun z : ℂ => sigmoidMixture b H M lam z j) =
        fun z : ℂ => H z j + ∑ slope ∈ Finset.univ.image lam,
          csig ((slope : ℂ) * z + (b : ℂ)) *
            aggregateCoeff M lam slope j := by
    funext z
    exact sigmoidMixture_coord_eq_sum_image_aggregate b H M lam z j
  rw [hrepr]
  refine (hH j τ hτ).add ?_
  have hsumFun :
      (∑ slope ∈ Finset.univ.image lam,
        fun z : ℂ =>
          csig ((slope : ℂ) * z + (b : ℂ)) *
            aggregateCoeff M lam slope j) =
        (fun z : ℂ => ∑ slope ∈ Finset.univ.image lam,
          csig ((slope : ℂ) * z + (b : ℂ)) *
            aggregateCoeff M lam slope j) := by
    funext z
    simp
  rw [← hsumFun]
  refine Finset.analyticAt_sum
    (𝕜 := ℂ) (E := ℂ) (F := ℂ)
    (Finset.univ.image lam) ?_
  intro slope _hslope_image
  by_cases hcoord : aggregateCoeff M lam slope j = 0
  · simpa [hcoord] using
      (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) τ)
  · by_cases hslope0 : slope = 0
    · simpa [hslope0] using
        (analyticAt_const : AnalyticAt ℂ
          (fun _ : ℂ => csig (b : ℂ) * aggregateCoeff M lam slope j) τ)
    · have hvecne : aggregateCoeff M lam slope ≠ 0 := by
        intro hzero
        exact hcoord (congrFun hzero j)
      have hsupp : slope ∈ slopeSupportFinset M lam :=
        (mem_slopeSupportFinset_iff M lam slope).2 ⟨hslope0, hvecne⟩
      have hnotPole : τ ∉ affineSigmoidPoleSet b slope := by
        intro hτpole
        exact hτ (by
          rw [mixtureSingularSet]
          exact Set.mem_iUnion.2
            ⟨slope, Set.mem_iUnion.2 ⟨hsupp, hτpole⟩⟩)
      have hsig : AnalyticAt ℂ
          (fun z : ℂ => csig ((slope : ℂ) * z + (b : ℂ))) τ :=
        affine_csig_analyticAt_of_notMem_poleSet hslope0 hnotPole
      simpa using hsig.mul
        (analyticAt_const : AnalyticAt ℂ
          (fun _ : ℂ => aggregateCoeff M lam slope j) τ)

/-- A continuous function is locally bounded on punctured neighborhoods. -/
theorem continuousAt_puncturedBounded {F : ℂ -> ℂ} {τ : ℂ}
    (hF : ContinuousAt F τ) :
    PuncturedBoundedAt F τ := by
  refine ⟨‖F τ‖ + 1, ?_⟩
  have hlt : ‖F τ‖ < ‖F τ‖ + 1 := by linarith
  have hnear : ∀ᶠ z in nhds τ, ‖F z‖ < ‖F τ‖ + 1 :=
    hF.norm.eventually (Iio_mem_nhds hlt)
  exact (hnear.filter_mono nhdsWithin_le_nhds).mono fun _ hz => le_of_lt hz

/-- Multiplying a blowing-up function by a nonzero constant preserves blow-up. -/
theorem BlowsUpAt.const_mul {A : ℂ -> ℂ} {τ c : ℂ}
    (hA : BlowsUpAt A τ) (hc : c ≠ 0) :
    BlowsUpAt (fun z => c * A z) τ := by
  have h :=
    TransformerIdentifiability.NLayer.BlowsUpAt.mul_tendsto_ne_zero
      (A := A) (G := fun _ : ℂ => c) hA tendsto_const_nhds hc
  simpa [mul_comm] using h

/-- The regular part at a separated affine pole is analytic coordinatewise. -/
theorem sigmoidMixtureRegularPartAtSlope_coord_analyticAt {p N : Nat}
    {b slope : ℝ} {ξ : ℂ}
    (hb : b ≠ 0) (hslope : slope ≠ 0) (hξ : ξ ∈ affineSigmoidPoleSet b slope)
    {H : ℂ -> Fin N -> ℂ} {M : Fin p -> Fin N -> ℂ} {lam : Fin p -> ℝ}
    (j : Fin N) (hH : AnalyticAt ℂ (fun τ : ℂ => H τ j) ξ) :
    AnalyticAt ℂ
      (fun τ : ℂ => sigmoidMixtureRegularPartAtSlope b H M lam slope τ j) ξ := by
  classical
  unfold sigmoidMixtureRegularPartAtSlope
  refine hH.add ?_
  simp only [Finset.sum_apply]
  have hsumFun :
      (∑ h : Fin p, fun τ : ℂ =>
        (if lam h = slope then 0
         else csig ((lam h : ℂ) * τ + (b : ℂ)) • M h) j) =
        (fun τ : ℂ =>
          ∑ h : Fin p,
            (if lam h = slope then 0
             else csig ((lam h : ℂ) * τ + (b : ℂ)) • M h) j) := by
    funext τ
    simp
  rw [← hsumFun]
  refine Finset.analyticAt_sum
    (𝕜 := ℂ) (E := ℂ) (F := ℂ)
    (Finset.univ : Finset (Fin p)) ?_
  intro h _hh
  by_cases heq : lam h = slope
  · simpa [heq] using
      (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) ξ)
  · by_cases hzero : lam h = 0
    · have hzeroSlope : (0 : ℝ) ≠ slope := fun h0 => hslope h0.symm
      simpa [heq, hzero, hzeroSlope, Pi.smul_apply] using
        (analyticAt_const :
          AnalyticAt ℂ (fun _ : ℂ => csig (b : ℂ) * M h j) ξ)
    · have hξnot : ξ ∉ affineSigmoidPoleSet b (lam h) := by
        intro hξh
        have hinter :
            affineSigmoidPoleSet b slope ∩ affineSigmoidPoleSet b (lam h) = ∅ :=
          affineSigmoidPoleSet_inter_eq_empty_of_ne
            hb hslope hzero (by simpa [eq_comm] using heq)
        have hmem : ξ ∈ affineSigmoidPoleSet b slope ∩ affineSigmoidPoleSet b (lam h) :=
          ⟨hξ, hξh⟩
        simp [hinter] at hmem
      have han :
          AnalyticAt ℂ
            (fun τ : ℂ => csig ((lam h : ℂ) * τ + (b : ℂ))) ξ :=
        affine_csig_analyticAt_of_notMem_poleSet hzero hξnot
      simpa [heq, Pi.smul_apply] using
        han.mul (analyticAt_const :
          AnalyticAt ℂ (fun _ : ℂ => M h j) ξ)

/-- A nonzero aggregate coordinate creates a genuine pole at every separated
progression point. -/
theorem sigmoidMixture_coord_blowsUpAt_of_aggregate_ne {p N : Nat}
    {b slope : ℝ} {ξ : ℂ}
    (hb : b ≠ 0) (hslope : slope ≠ 0) (hξ : ξ ∈ affineSigmoidPoleSet b slope)
    {H : ℂ -> Fin N -> ℂ} {M : Fin p -> Fin N -> ℂ} {lam : Fin p -> ℝ}
    (hH : ∀ j : Fin N, AnalyticAt ℂ (fun τ : ℂ => H τ j) ξ)
    {j : Fin N} (hcoeff : aggregateCoeff M lam slope j ≠ 0) :
    BlowsUpAt (fun τ : ℂ => sigmoidMixture b H M lam τ j) ξ := by
  classical
  have hB :
      PuncturedBoundedAt
        (fun τ : ℂ => sigmoidMixtureRegularPartAtSlope b H M lam slope τ j) ξ :=
    continuousAt_puncturedBounded
      (sigmoidMixtureRegularPartAtSlope_coord_analyticAt
        hb hslope hξ j (hH j)).continuousAt
  rcases hξ with ⟨n, rfl⟩
  have hA :
      BlowsUpAt (fun τ : ℂ => csig ((slope : ℂ) * τ + (b : ℂ)))
        (affineSigmoidPole b slope n) :=
    affine_csig_blowsUpAt_sigmoidPole b slope hslope n
  have hmain :
      BlowsUpAt
        (fun τ : ℂ =>
          sigmoidMixtureRegularPartAtSlope b H M lam slope τ j +
            csig ((slope : ℂ) * τ + (b : ℂ)) * aggregateCoeff M lam slope j)
        (affineSigmoidPole b slope n) :=
    TransformerIdentifiability.NLayer.BlowsUpAt.bounded_add_mul_tendsto_ne_zero
      hB hA tendsto_const_nhds hcoeff
  have hfun :
      (fun τ : ℂ => sigmoidMixture b H M lam τ j) =
        fun τ : ℂ =>
          sigmoidMixtureRegularPartAtSlope b H M lam slope τ j +
            csig ((slope : ℂ) * τ + (b : ℂ)) * aggregateCoeff M lam slope j := by
    funext τ
    exact sigmoidMixture_decompose_by_aggregate_coord b slope H M lam τ j
  simpa [hfun] using hmain

/-- A nonzero aggregate-coefficient gap at a common affine pole creates a genuine
pole in the coordinatewise difference of two mixtures. -/
theorem sigmoidMixture_coord_sub_blowsUpAt_of_aggregateCoeff_sub_ne {p q N : Nat}
    {b slope : ℝ} {ξ : ℂ}
    (hb : b ≠ 0) (hslope : slope ≠ 0) (hξ : ξ ∈ affineSigmoidPoleSet b slope)
    {H H' : ℂ -> Fin N -> ℂ}
    {M : Fin p -> Fin N -> ℂ} {lam : Fin p -> ℝ}
    {M' : Fin q -> Fin N -> ℂ} {lam' : Fin q -> ℝ}
    (hH : ∀ j : Fin N, AnalyticAt ℂ (fun τ : ℂ => H τ j) ξ)
    (hH' : ∀ j : Fin N, AnalyticAt ℂ (fun τ : ℂ => H' τ j) ξ)
    {j : Fin N}
    (hcoeff :
      aggregateCoeff M lam slope j - aggregateCoeff M' lam' slope j ≠ 0) :
    BlowsUpAt
      (fun τ : ℂ =>
        sigmoidMixture b H M lam τ j - sigmoidMixture b H' M' lam' τ j) ξ := by
  classical
  have hreg :
      AnalyticAt ℂ
        (fun τ : ℂ =>
          sigmoidMixtureRegularPartAtSlope b H M lam slope τ j -
            sigmoidMixtureRegularPartAtSlope b H' M' lam' slope τ j) ξ :=
    (sigmoidMixtureRegularPartAtSlope_coord_analyticAt
      hb hslope hξ j (hH j)).sub
      (sigmoidMixtureRegularPartAtSlope_coord_analyticAt
        hb hslope hξ j (hH' j))
  have hB :
      PuncturedBoundedAt
        (fun τ : ℂ =>
          sigmoidMixtureRegularPartAtSlope b H M lam slope τ j -
            sigmoidMixtureRegularPartAtSlope b H' M' lam' slope τ j) ξ :=
    continuousAt_puncturedBounded hreg.continuousAt
  rcases hξ with ⟨n, rfl⟩
  have hA :
      BlowsUpAt (fun τ : ℂ => csig ((slope : ℂ) * τ + (b : ℂ)))
        (affineSigmoidPole b slope n) :=
    affine_csig_blowsUpAt_sigmoidPole b slope hslope n
  have hmain :
      BlowsUpAt
        (fun τ : ℂ =>
          (sigmoidMixtureRegularPartAtSlope b H M lam slope τ j -
              sigmoidMixtureRegularPartAtSlope b H' M' lam' slope τ j) +
            csig ((slope : ℂ) * τ + (b : ℂ)) *
              (aggregateCoeff M lam slope j - aggregateCoeff M' lam' slope j))
        (affineSigmoidPole b slope n) :=
    TransformerIdentifiability.NLayer.BlowsUpAt.bounded_add_mul_tendsto_ne_zero
      hB hA tendsto_const_nhds hcoeff
  have hfun :
      (fun τ : ℂ =>
        sigmoidMixture b H M lam τ j - sigmoidMixture b H' M' lam' τ j) =
        fun τ : ℂ =>
          (sigmoidMixtureRegularPartAtSlope b H M lam slope τ j -
              sigmoidMixtureRegularPartAtSlope b H' M' lam' slope τ j) +
            csig ((slope : ℂ) * τ + (b : ℂ)) *
              (aggregateCoeff M lam slope j - aggregateCoeff M' lam' slope j) := by
    funext τ
    rw [sigmoidMixture_decompose_by_aggregate_coord b slope H M lam τ j,
      sigmoidMixture_decompose_by_aggregate_coord b slope H' M' lam' τ j]
    ring
  simpa [hfun] using hmain

/-- Real-tail equality of two aggregate sigmoid mixtures identifies the aggregate
coefficient at every nonzero slope lying in their common aggregate support. -/
theorem aggregateCoeff_eq_of_sigmoidMixture_real_tail_eq_of_mem_slopeSupportFinset
    {p q N : Nat} {b T0 : ℝ}
    (hb : b ≠ 0)
    {H H' : ℂ -> Fin N -> ℂ}
    {M : Fin p -> Fin N -> ℂ} {lam : Fin p -> ℝ}
    {M' : Fin q -> Fin N -> ℂ} {lam' : Fin q -> ℝ}
    (hH : ∀ j : Fin N, ∀ τ : ℂ, AnalyticAt ℂ (fun z : ℂ => H z j) τ)
    (hH' : ∀ j : Fin N, ∀ τ : ℂ, AnalyticAt ℂ (fun z : ℂ => H' z j) τ)
    (hEq : ∀ t : ℝ, T0 < t ->
      sigmoidMixture b H M lam (t : ℂ) =
        sigmoidMixture b H' M' lam' (t : ℂ))
    {slope : ℝ}
    (hslope : slope ∈ slopeSupportFinset M lam)
    (_hslope' : slope ∈ slopeSupportFinset M' lam') :
    aggregateCoeff M lam slope = aggregateCoeff M' lam' slope := by
  classical
  ext j
  by_contra hcoeff_eq
  let ξ : ℂ := affineSigmoidPole b slope 0
  let E : Set ℂ := mixtureSingularSet b M lam ∪ mixtureSingularSet b M' lam'
  have hslope_ne : slope ≠ 0 :=
    (mem_slopeSupportFinset_iff M lam slope).1 hslope |>.1
  have hξ : ξ ∈ affineSigmoidPoleSet b slope := ⟨0, rfl⟩
  have hcoeff_sub :
      aggregateCoeff M lam slope j - aggregateCoeff M' lam' slope j ≠ 0 := by
    intro hzero
    exact hcoeff_eq (sub_eq_zero.mp hzero)
  have hDblow :
      BlowsUpAt
        (fun τ : ℂ =>
          sigmoidMixture b H M lam τ j - sigmoidMixture b H' M' lam' τ j) ξ :=
    sigmoidMixture_coord_sub_blowsUpAt_of_aggregateCoeff_sub_ne
      (b := b) (slope := slope) (ξ := ξ)
      (H := H) (H' := H') (M := M) (lam := lam) (M' := M') (lam' := lam')
      hb hslope_ne hξ
      (fun i => hH i ξ) (fun i => hH' i ξ) hcoeff_sub
  have hEcount : E.Countable := by
    dsimp [E]
    exact (mixtureSingularSet_countable b M lam).union
      (mixtureSingularSet_countable b M' lam')
  have hEclosedDiscrete : ClosedDiscreteIn E Set.univ := by
    dsimp [E]
    exact (mixtureSingularSet_closedDiscrete b M lam).union
      (mixtureSingularSet_closedDiscrete b M' lam')
  have hDisol : IsPuncturedIsolated E ξ :=
    TransformerIdentifiability.NLayer.eventually_notMem_of_not_mem_acc
      (hEclosedDiscrete.noAccum ξ (by simp))
  have hzeroAnalytic :
      AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) (∅ : Set ℂ)ᶜ := by
    intro τ _hτ
    exact analyticAt_const
  have hmix :
      ∀ i : Fin N,
        AnalyticOnNhd ℂ (fun τ : ℂ => sigmoidMixture b H M lam τ i)
          (mixtureSingularSet b M lam)ᶜ :=
    sigmoidMixture_coord_analyticOnNhd_mixtureSingularSet_compl
      (b := b) (H := H) (M := M) (lam := lam)
      (by
        intro i τ _hτ
        exact hH i τ)
  have hmix' :
      ∀ i : Fin N,
        AnalyticOnNhd ℂ (fun τ : ℂ => sigmoidMixture b H' M' lam' τ i)
          (mixtureSingularSet b M' lam')ᶜ :=
    sigmoidMixture_coord_analyticOnNhd_mixtureSingularSet_compl
      (b := b) (H := H') (M := M') (lam := lam')
      (by
        intro i τ _hτ
        exact hH' i τ)
  have hDanalytic :
      AnalyticOnNhd ℂ
        (fun τ : ℂ =>
          sigmoidMixture b H M lam τ j - sigmoidMixture b H' M' lam' τ j) Eᶜ := by
    intro τ hτ
    have hτM : τ ∈ (mixtureSingularSet b M lam)ᶜ := by
      intro hτM
      exact hτ (by
        dsimp [E]
        exact Or.inl hτM)
    have hτM' : τ ∈ (mixtureSingularSet b M' lam')ᶜ := by
      intro hτM'
      exact hτ (by
        dsimp [E]
        exact Or.inr hτM')
    exact (hmix j τ hτM).sub (hmix' j τ hτM')
  have hz0 : (((T0 + 1 : ℝ) : ℂ)) ∈ ((∅ : Set ℂ) ∪ E)ᶜ := by
    rw [Set.mem_compl_iff, Set.mem_union]
    intro hmem
    rcases hmem with hempty | hE
    · simp at hempty
    · dsimp [E] at hE
      rcases hE with hM | hM'
      · exact ofReal_notMem_mixtureSingularSet b (T0 + 1) M lam hM
      · exact ofReal_notMem_mixtureSingularSet b (T0 + 1) M' lam' hM'
  have hξempty : ξ ∈ (∅ : Set ℂ) :=
    TransformerIdentifiability.NLayer.pole_transfer_of_real_tail_eq
      (E_F := (∅ : Set ℂ)) (E_G := E)
      (F := fun _ : ℂ => (0 : ℂ))
      (G := fun τ : ℂ =>
        sigmoidMixture b H M lam τ j - sigmoidMixture b H' M' lam' τ j)
      (T0 := T0) (x0 := T0 + 1) (τ := ξ)
      isClosed_empty
      (by simp)
      hEcount hzeroAnalytic hDanalytic
      (by linarith) hz0
      (by
        intro t ht
        have htEq := congrFun (hEq t ht) j
        change (0 : ℂ) =
          sigmoidMixture b H M lam (t : ℂ) j -
            sigmoidMixture b H' M' lam' (t : ℂ) j
        rw [htEq]
        simp)
      (by
        intro _hξ
        exact continuousAt_const)
      hDisol hDblow
  simp at hξempty

/-- If real-tail equality is paired with equality of aggregate supports, then the
aggregate coefficients agree at every nonzero slope. -/
theorem aggregateCoeff_eq_of_sigmoidMixture_real_tail_eq_of_slopeSupportFinset_eq
    {p q N : Nat} {b T0 : ℝ}
    (hb : b ≠ 0)
    {H H' : ℂ -> Fin N -> ℂ}
    {M : Fin p -> Fin N -> ℂ} {lam : Fin p -> ℝ}
    {M' : Fin q -> Fin N -> ℂ} {lam' : Fin q -> ℝ}
    (hH : ∀ j : Fin N, ∀ τ : ℂ, AnalyticAt ℂ (fun z : ℂ => H z j) τ)
    (hH' : ∀ j : Fin N, ∀ τ : ℂ, AnalyticAt ℂ (fun z : ℂ => H' z j) τ)
    (hEq : ∀ t : ℝ, T0 < t ->
      sigmoidMixture b H M lam (t : ℂ) =
        sigmoidMixture b H' M' lam' (t : ℂ))
    (hsupp : slopeSupportFinset M lam = slopeSupportFinset M' lam') :
    ∀ slope : ℝ, slope ≠ 0 ->
      aggregateCoeff M lam slope = aggregateCoeff M' lam' slope := by
  intro slope hslope_ne
  by_cases hmem : slope ∈ slopeSupportFinset M lam
  · have hmem' : slope ∈ slopeSupportFinset M' lam' := by
      simpa [hsupp] using hmem
    exact aggregateCoeff_eq_of_sigmoidMixture_real_tail_eq_of_mem_slopeSupportFinset
      (b := b) (T0 := T0) (H := H) (H' := H') (slope := slope)
      (M := M) (lam := lam) (M' := M') (lam' := lam')
      hb hH hH' hEq hmem hmem'
  · have hmem' : slope ∉ slopeSupportFinset M' lam' := by
      intro hmem'
      exact hmem (by simpa [hsupp] using hmem')
    have hM : aggregateCoeff M lam slope = 0 := by
      by_contra hne
      exact hmem ((mem_slopeSupportFinset_iff M lam slope).2 ⟨hslope_ne, hne⟩)
    have hM' : aggregateCoeff M' lam' slope = 0 := by
      by_contra hne
      exact hmem' ((mem_slopeSupportFinset_iff M' lam' slope).2 ⟨hslope_ne, hne⟩)
    rw [hM, hM']

/-- **K04B.E.lem-explicit-sigmoid-mixture-recovery.S/P**.

Separated nonzero heads are recovered by the aggregate support, aggregate
coefficients, and the disjoint union of their pole progressions. -/
theorem lem_explicit_sigmoid_mixture_recovery {p N : Nat} (b : ℝ)
    {M : Fin p -> Fin N -> ℂ} {lam : Fin p -> ℝ}
    (hpair : Pairwise fun i j => lam i ≠ lam j)
    (hlam : ∀ h : Fin p, lam h ≠ 0)
    (hM : ∀ h : Fin p, M h ≠ 0) :
    slopeSupportFinset M lam = Finset.univ.image lam ∧
      (∀ h : Fin p, aggregateCoeff M lam (lam h) = M h) ∧
      mixtureSingularSet b M lam =
        ⋃ h : Fin p, affineSigmoidPoleSet b (lam h) := by
  classical
  have hsupp := slopeSupportFinset_eq_image_of_pairwise_nonzero hpair hlam hM
  refine ⟨hsupp, fun h => aggregateCoeff_eq_single_of_pairwise hpair h, ?_⟩
  ext τ
  simp [mixtureSingularSet, hsupp]

/-- **K04B.E.lem-explicit-sigmoid-mixture-recovery.S/P**.

Aggregate matching is equivalent to equality of the recovered nonzero slope
support and singular set data. -/
theorem lem_explicit_sigmoid_mixture_aggregate_matching {p q N : Nat} (b : ℝ)
    {M : Fin p -> Fin N -> ℂ} {lam : Fin p -> ℝ}
    {M' : Fin q -> Fin N -> ℂ} {lam' : Fin q -> ℝ}
    (hagg : ∀ slope : ℝ, slope ≠ 0 -> aggregateCoeff M lam slope = aggregateCoeff M' lam' slope) :
    slopeSupportFinset M lam = slopeSupportFinset M' lam' ∧
      mixtureSingularSet b M lam = mixtureSingularSet b M' lam' :=
  ⟨slopeSupportFinset_eq_of_aggregateCoeff_eq hagg,
    mixtureSingularSet_eq_of_aggregateCoeff_eq b hagg⟩

/-! ## Pole-transfer APIs -/

/-- **K04B.E.lem-pole-transfer.S/P**.

Pole transfer from equality on a punctured-accumulating set in the common
regular domain. -/
theorem lem_pole_transfer_of_frequentlyEq {E_F E_G : Set ℂ} {F G : ℂ -> ℂ}
    {z0 τ : ℂ}
    (hEFclosed : IsClosed E_F)
    (hEFcount : E_F.Countable)
    (hEGcount : E_G.Countable)
    (hF : AnalyticOnNhd ℂ F E_Fᶜ)
    (hGanalytic : AnalyticOnNhd ℂ G E_Gᶜ)
    (hz0 : z0 ∈ (E_F ∪ E_G)ᶜ)
    (hfg : ∃ᶠ z in nhdsWithin z0 ({z0}ᶜ : Set ℂ), F z = G z)
    (hFcont : τ ∉ E_F -> ContinuousAt F τ)
    (hGisol : IsPuncturedIsolated E_G τ)
    (hGblow : BlowsUpAt G τ) :
    τ ∈ E_F :=
  TransformerIdentifiability.NLayer.pole_transfer_of_frequentlyEq
    hEFclosed hEFcount hEGcount hF hGanalytic hz0 hfg hFcont hGisol hGblow

/-- **K04B.E.lem-pole-transfer.S/P**.

Pole transfer when the identity-theorem input comes from equality on a real
tail. -/
theorem lem_pole_transfer_of_real_tail_eq {E_F E_G : Set ℂ} {F G : ℂ -> ℂ}
    {T0 x0 : ℝ} {τ : ℂ}
    (hEFclosed : IsClosed E_F)
    (hEFcount : E_F.Countable)
    (hEGcount : E_G.Countable)
    (hF : AnalyticOnNhd ℂ F E_Fᶜ)
    (hGanalytic : AnalyticOnNhd ℂ G E_Gᶜ)
    (hx0 : T0 < x0)
    (hz0 : (x0 : ℂ) ∈ (E_F ∪ E_G)ᶜ)
    (hfg : ∀ t : ℝ, T0 < t -> F (t : ℂ) = G (t : ℂ))
    (hFcont : τ ∉ E_F -> ContinuousAt F τ)
    (hGisol : IsPuncturedIsolated E_G τ)
    (hGblow : BlowsUpAt G τ) :
    τ ∈ E_F :=
  TransformerIdentifiability.NLayer.pole_transfer_of_real_tail_eq
    hEFclosed hEFcount hEGcount hF hGanalytic hx0 hz0 hfg hFcont hGisol hGblow

end TransformerIdentifiability.NLayer.KHead
