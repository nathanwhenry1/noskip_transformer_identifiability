import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Core
import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.SigmoidMixtures
import AnyLayerIdentifiabilityProof.NLayer.Foundations.PolynomialGenericity
import AnyLayerIdentifiabilityProof.NLayer.KHead.Matching
import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.QuadricRigidity

set_option autoImplicit false

open Filter Matrix

namespace TransformerIdentifiability.NLayer.NoSkip

/-!
# Shared analytic toolbox for the no-skip model

This file gives the no-skip development stable names for the model-independent
plane-topology and pole-transfer API.  The proofs remain in the shared `KHead`
analytic modules: the declarations below are definition aliases or theorem
adapters, so no complex-analysis argument is duplicated here.

The sections below expose plane topology, pole transfer, finite sigmoid-mixture
recovery, polynomial genericity, matching, elementary topology, and the exact
no-skip telescoping specialization under one stable namespace.

## Reuse and import audit

The plane/pole/mixture declarations and finite matching declarations are
direct theorem reuse from `KHead.Analytic.SigmoidMixtures` and
`KHead.Matching`; their statements are independent of `Params`, `layer`, and
`transformer`.  The scalar hyperplane helpers are reused from
`KHead.Analytic.QuadricRigidity`, while the multi-quadric theorem itself is new
in `NoSkip.Analytic.MultiQuadricRigidity`.  Polynomial genericity is adapted
from the neutral parent `NLayer.Foundations` modules.  The telescoping algebra
is neutral; only its final `C = valueSum` specialization is no-skip-specific.

Those legacy analytic modules transitively import `KHead.Core` for shared
matrix notation and sigmoid-pole definitions, and `NoSkip.Core` itself reuses
the common parameter carrier from that file.  None of the adapters below
references `KHead.layer`, `KHead.transformer`, or the skip collapse identity,
and no `KHead` module imports this `NoSkip` module, so the dependency is
one-way and introduces no realization-semantic cycle.
-/

/-! ## Closed countable exceptional sets -/

/-- A subset of `U` which is relatively closed and has no accumulation point in
`U`. -/
abbrev ClosedDiscreteIn (A U : Set ℂ) : Prop :=
  KHead.ClosedDiscreteIn A U

namespace ClosedDiscreteIn

/-- Closed-discrete subsets of the complex plane are countable. -/
theorem countable {A U : Set ℂ} (h : ClosedDiscreteIn A U) :
    A.Countable :=
  KHead.ClosedDiscreteIn.countable h

end ClosedDiscreteIn

/-- A nonempty open connected subset of the complex plane. -/
abbrev PlaneDomain (U : Set ℂ) : Prop :=
  KHead.PlaneDomain U

/-- The complement of a closed countable exceptional set is a plane domain. -/
theorem countable_closed_compl_planeDomain {E : Set ℂ}
    (hEcount : E.Countable) (hEclosed : IsClosed E) :
    PlaneDomain Eᶜ :=
  KHead.countable_closed_compl_planeDomain hEcount hEclosed

/-! ## Sigmoid poles and affine pole progressions -/

/-- TeX notation `Π = (2ℤ+1)π i` for the sigmoid pole set. -/
abbrev Pi : Set ℂ :=
  sigmoidPoleSet

/-- The shared no-skip pole set is the neutral odd-`π i` set. -/
theorem sigmoidPoleSet_eq_oddPiI :
    sigmoidPoleSet = TransformerIdentifiability.NLayer.oddPiI :=
  KHead.sigmoidPoleSet_eq_oddPiI

/-- Membership in `Π` is equivalent to vanishing of the logistic denominator. -/
theorem mem_Pi_iff_denom_zero (z : ℂ) :
    z ∈ Pi ↔ 1 + Complex.exp (-z) = 0 :=
  KHead.mem_Pi_iff_denom_zero z

/-- `Π` is closed and discrete in the plane. -/
theorem Pi_closedDiscrete : ClosedDiscreteIn Pi Set.univ :=
  KHead.Pi_closedDiscrete

/-- `Π` is countable. -/
theorem Pi_countable : Pi.Countable :=
  Pi_closedDiscrete.countable

/-- `Π` is closed. -/
theorem Pi_closed : IsClosed Pi := by
  simpa using Pi_closedDiscrete.isClosed_rel

/-- The real axis does not meet `Π`. -/
theorem ofReal_notMem_Pi (x : ℝ) : (x : ℂ) ∉ Pi :=
  KHead.ofReal_notMem_Pi x

/-- The pole indexed by `n` for `τ ↦ σ(λτ+b)`. -/
noncomputable abbrev affineSigmoidPole (b lam : ℝ) (n : ℤ) : ℂ :=
  KHead.affineSigmoidPole b lam n

/-- The arithmetic pole progression `P(λ)` for `τ ↦ σ(λτ+b)`. -/
noncomputable abbrev affineSigmoidPoleSet (b lam : ℝ) : Set ℂ :=
  KHead.affineSigmoidPoleSet b lam

/-- Membership in the affine progression is equivalent to its argument hitting
`Π`. -/
theorem mem_affineSigmoidPoleSet_iff {b lam : ℝ} (hlam : lam ≠ 0) (τ : ℂ) :
    τ ∈ affineSigmoidPoleSet b lam ↔ (lam : ℂ) * τ + (b : ℂ) ∈ Pi :=
  KHead.mem_affineSigmoidPoleSet_iff hlam τ

/-- Every pole in `P(λ)` lies on the vertical line `Re τ = -b/λ`. -/
theorem affineSigmoidPole_re {b lam : ℝ} (hlam : lam ≠ 0) (n : ℤ) :
    (affineSigmoidPole b lam n).re = -b / lam :=
  KHead.affineSigmoidPole_re hlam n

/-- A nonzero-slope affine pole progression is closed and discrete. -/
theorem affineSigmoidPoleSet_closedDiscrete (b lam : ℝ) (hlam : lam ≠ 0) :
    ClosedDiscreteIn (affineSigmoidPoleSet b lam) Set.univ :=
  KHead.affineSigmoidPoleSet_closedDiscrete b lam hlam

/-- A nonzero-slope affine pole progression is countable. -/
theorem affineSigmoidPoleSet_countable (b lam : ℝ) (hlam : lam ≠ 0) :
    (affineSigmoidPoleSet b lam).Countable :=
  KHead.affineSigmoidPoleSet_countable b lam hlam

/-- A nonzero-slope affine pole progression is closed. -/
theorem affineSigmoidPoleSet_closed (b lam : ℝ) (hlam : lam ≠ 0) :
    IsClosed (affineSigmoidPoleSet b lam) :=
  KHead.affineSigmoidPoleSet_closed b lam hlam

/-- Real points never belong to a nonzero-slope affine pole progression. -/
theorem ofReal_notMem_affineSigmoidPoleSet (b lam x : ℝ) (hlam : lam ≠ 0) :
    (x : ℂ) ∉ affineSigmoidPoleSet b lam :=
  KHead.ofReal_notMem_affineSigmoidPoleSet b lam x hlam

/-- For nonzero bias, distinct nonzero slopes have disjoint pole progressions. -/
theorem affineSigmoidPoleSet_inter_eq_empty_of_ne {b lam mu : ℝ}
    (hb : b ≠ 0) (hlam : lam ≠ 0) (hmu : mu ≠ 0) (hneq : lam ≠ mu) :
    affineSigmoidPoleSet b lam ∩ affineSigmoidPoleSet b mu = ∅ :=
  KHead.affineSigmoidPoleSet_inter_eq_empty_of_ne hb hlam hmu hneq

/-! ## Pole transfer -/

/-- Local blow-up along punctured neighborhoods. -/
abbrev BlowsUpAt (G : ℂ → ℂ) (τ : ℂ) : Prop :=
  TransformerIdentifiability.NLayer.BlowsUpAt G τ

/-- Punctured-neighborhood isolation from an exceptional set. -/
abbrev IsPuncturedIsolated (E : Set ℂ) (τ : ℂ) : Prop :=
  TransformerIdentifiability.NLayer.IsPuncturedIsolated E τ

/-- Pole transfer when equality is known on a punctured-accumulating subset of
the common regular domain. -/
theorem pole_transfer_of_frequentlyEq {E_F E_G : Set ℂ} {F G : ℂ → ℂ}
    {z0 τ : ℂ}
    (hEFclosed : IsClosed E_F)
    (hEFcount : E_F.Countable)
    (hEGcount : E_G.Countable)
    (hF : AnalyticOnNhd ℂ F E_Fᶜ)
    (hGanalytic : AnalyticOnNhd ℂ G E_Gᶜ)
    (hz0 : z0 ∈ (E_F ∪ E_G)ᶜ)
    (hfg : ∃ᶠ z in nhdsWithin z0 ({z0}ᶜ : Set ℂ), F z = G z)
    (hFcont : τ ∉ E_F → ContinuousAt F τ)
    (hGisol : IsPuncturedIsolated E_G τ)
    (hGblow : BlowsUpAt G τ) :
    τ ∈ E_F :=
  KHead.lem_pole_transfer_of_frequentlyEq hEFclosed hEFcount hEGcount hF
    hGanalytic hz0 hfg hFcont hGisol hGblow

/-- Pole transfer from equality on a real tail. -/
theorem pole_transfer_of_real_tail_eq {E_F E_G : Set ℂ} {F G : ℂ → ℂ}
    {T0 x0 : ℝ} {τ : ℂ}
    (hEFclosed : IsClosed E_F)
    (hEFcount : E_F.Countable)
    (hEGcount : E_G.Countable)
    (hF : AnalyticOnNhd ℂ F E_Fᶜ)
    (hGanalytic : AnalyticOnNhd ℂ G E_Gᶜ)
    (hx0 : T0 < x0)
    (hz0 : (x0 : ℂ) ∈ (E_F ∪ E_G)ᶜ)
    (hfg : ∀ t : ℝ, T0 < t → F (t : ℂ) = G (t : ℂ))
    (hFcont : τ ∉ E_F → ContinuousAt F τ)
    (hGisol : IsPuncturedIsolated E_G τ)
    (hGblow : BlowsUpAt G τ) :
    τ ∈ E_F :=
  KHead.lem_pole_transfer_of_real_tail_eq hEFclosed hEFcount hEGcount hF
    hGanalytic hx0 hz0 hfg hFcont hGisol hGblow

/-- Compatibility spelling retained for the transferred TeX lemma. -/
theorem lem_pole_transfer_of_frequentlyEq {E_F E_G : Set ℂ} {F G : ℂ → ℂ}
    {z0 τ : ℂ}
    (hEFclosed : IsClosed E_F)
    (hEFcount : E_F.Countable)
    (hEGcount : E_G.Countable)
    (hF : AnalyticOnNhd ℂ F E_Fᶜ)
    (hGanalytic : AnalyticOnNhd ℂ G E_Gᶜ)
    (hz0 : z0 ∈ (E_F ∪ E_G)ᶜ)
    (hfg : ∃ᶠ z in nhdsWithin z0 ({z0}ᶜ : Set ℂ), F z = G z)
    (hFcont : τ ∉ E_F → ContinuousAt F τ)
    (hGisol : IsPuncturedIsolated E_G τ)
    (hGblow : BlowsUpAt G τ) :
    τ ∈ E_F :=
  pole_transfer_of_frequentlyEq hEFclosed hEFcount hEGcount hF hGanalytic
    hz0 hfg hFcont hGisol hGblow

/-- Compatibility spelling retained for the transferred TeX lemma. -/
theorem lem_pole_transfer_of_real_tail_eq {E_F E_G : Set ℂ} {F G : ℂ → ℂ}
    {T0 x0 : ℝ} {τ : ℂ}
    (hEFclosed : IsClosed E_F)
    (hEFcount : E_F.Countable)
    (hEGcount : E_G.Countable)
    (hF : AnalyticOnNhd ℂ F E_Fᶜ)
    (hGanalytic : AnalyticOnNhd ℂ G E_Gᶜ)
    (hx0 : T0 < x0)
    (hz0 : (x0 : ℂ) ∈ (E_F ∪ E_G)ᶜ)
    (hfg : ∀ t : ℝ, T0 < t → F (t : ℂ) = G (t : ℂ))
    (hFcont : τ ∉ E_F → ContinuousAt F τ)
    (hGisol : IsPuncturedIsolated E_G τ)
    (hGblow : BlowsUpAt G τ) :
    τ ∈ E_F :=
  pole_transfer_of_real_tail_eq hEFclosed hEFcount hEGcount hF hGanalytic
    hx0 hz0 hfg hFcont hGisol hGblow

/-! ## Aggregate sigmoid-mixture recovery -/

/-- The complex logistic sigmoid. -/
noncomputable abbrev csig : ℂ → ℂ :=
  KHead.csig

/-- Local boundedness on a punctured neighborhood. -/
abbrev PuncturedBoundedAt (G : ℂ → ℂ) (τ : ℂ) : Prop :=
  TransformerIdentifiability.NLayer.PuncturedBoundedAt G τ

/-- Residue-one local factorization of `csig` at a sigmoid pole. -/
theorem csig_simplePole_factor_of_mem_Pi {ζ : ℂ} (hζ : ζ ∈ Pi) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g ζ ∧ g ζ = 1 ∧
      ∀ᶠ z in nhdsWithin ζ ({ζ}ᶜ : Set ℂ),
        csig z = g z * (z - ζ) ^ (-1 : ℤ) :=
  KHead.csig_simplePole_factor_of_mem_Pi hζ

/-- Aggregate vector coefficient of all heads having a given slope. -/
noncomputable abbrev aggregateCoeff {p N : Nat}
    (M : Fin p → Fin N → ℂ) (lam : Fin p → ℝ) (slope : ℝ) : Fin N → ℂ :=
  KHead.aggregateCoeff M lam slope

/-- Finite support of nonzero aggregate coefficients at nonzero slopes. -/
noncomputable abbrev slopeSupportFinset {p N : Nat}
    (M : Fin p → Fin N → ℂ) (lam : Fin p → ℝ) : Finset ℝ :=
  KHead.slopeSupportFinset M lam

/-- Union of the pole progressions belonging to the aggregate support. -/
noncomputable abbrev mixtureSingularSet {p N : Nat} (b : ℝ)
    (M : Fin p → Fin N → ℂ) (lam : Fin p → ℝ) : Set ℂ :=
  KHead.mixtureSingularSet b M lam

/-- A finite vector-valued sigmoid mixture with an arbitrary entire part `H`. -/
noncomputable abbrev sigmoidMixture {p N : Nat} (b : ℝ)
    (H : ℂ → Fin N → ℂ) (M : Fin p → Fin N → ℂ) (lam : Fin p → ℝ) :
    ℂ → Fin N → ℂ :=
  KHead.sigmoidMixture b H M lam

/-- The base-case specialization whose entire part is a constant vector. -/
noncomputable abbrev constantSigmoidMixture {p N : Nat} (b : ℝ)
    (C : Fin N → ℂ) (M : Fin p → Fin N → ℂ) (lam : Fin p → ℝ) :
    ℂ → Fin N → ℂ :=
  sigmoidMixture b (fun _ => C) M lam

/-- Characterization of membership in the finite aggregate support. -/
theorem mem_slopeSupportFinset_iff {p N : Nat}
    (M : Fin p → Fin N → ℂ) (lam : Fin p → ℝ) (slope : ℝ) :
    slope ∈ slopeSupportFinset M lam ↔
      slope ≠ 0 ∧ aggregateCoeff M lam slope ≠ 0 :=
  KHead.mem_slopeSupportFinset_iff M lam slope

/-- At a separated slope, the aggregate coefficient is its unique head
coefficient. -/
theorem aggregateCoeff_eq_single_of_pairwise {p N : Nat}
    {M : Fin p → Fin N → ℂ} {lam : Fin p → ℝ}
    (hpair : Pairwise fun i j => lam i ≠ lam j) (h : Fin p) :
    aggregateCoeff M lam (lam h) = M h :=
  KHead.aggregateCoeff_eq_single_of_pairwise hpair h

/-- Under separated, nonzero, nontrivial heads, aggregate support is precisely
the image of the head slopes. -/
theorem slopeSupportFinset_eq_image_of_pairwise_nonzero {p N : Nat}
    {M : Fin p → Fin N → ℂ} {lam : Fin p → ℝ}
    (hpair : Pairwise fun i j => lam i ≠ lam j)
    (hlam : ∀ h : Fin p, lam h ≠ 0)
    (hM : ∀ h : Fin p, M h ≠ 0) :
    slopeSupportFinset M lam = Finset.univ.image lam :=
  KHead.slopeSupportFinset_eq_image_of_pairwise_nonzero hpair hlam hM

/-- Equality of aggregate coefficients on nonzero slopes identifies aggregate
supports. -/
theorem slopeSupportFinset_eq_of_aggregateCoeff_eq {p q N : Nat}
    {M : Fin p → Fin N → ℂ} {lam : Fin p → ℝ}
    {M' : Fin q → Fin N → ℂ} {lam' : Fin q → ℝ}
    (hagg : ∀ slope : ℝ, slope ≠ 0 →
      aggregateCoeff M lam slope = aggregateCoeff M' lam' slope) :
    slopeSupportFinset M lam = slopeSupportFinset M' lam' :=
  KHead.slopeSupportFinset_eq_of_aggregateCoeff_eq hagg

/-- Equality of aggregate coefficients identifies mixture singular sets. -/
theorem mixtureSingularSet_eq_of_aggregateCoeff_eq {p q N : Nat} (b : ℝ)
    {M : Fin p → Fin N → ℂ} {lam : Fin p → ℝ}
    {M' : Fin q → Fin N → ℂ} {lam' : Fin q → ℝ}
    (hagg : ∀ slope : ℝ, slope ≠ 0 →
      aggregateCoeff M lam slope = aggregateCoeff M' lam' slope) :
    mixtureSingularSet b M lam = mixtureSingularSet b M' lam' :=
  KHead.mixtureSingularSet_eq_of_aggregateCoeff_eq b hagg

/-- A mixture singular set is closed and discrete. -/
theorem mixtureSingularSet_closedDiscrete {p N : Nat} (b : ℝ)
    (M : Fin p → Fin N → ℂ) (lam : Fin p → ℝ) :
    ClosedDiscreteIn (mixtureSingularSet b M lam) Set.univ :=
  KHead.mixtureSingularSet_closedDiscrete b M lam

/-- A mixture singular set is countable. -/
theorem mixtureSingularSet_countable {p N : Nat} (b : ℝ)
    (M : Fin p → Fin N → ℂ) (lam : Fin p → ℝ) :
    (mixtureSingularSet b M lam).Countable :=
  KHead.mixtureSingularSet_countable b M lam

/-- A mixture singular set is closed. -/
theorem mixtureSingularSet_closed {p N : Nat} (b : ℝ)
    (M : Fin p → Fin N → ℂ) (lam : Fin p → ℝ) :
    IsClosed (mixtureSingularSet b M lam) :=
  KHead.mixtureSingularSet_closed b M lam

/-- Mixture singular sets avoid the real axis. -/
theorem ofReal_notMem_mixtureSingularSet {p N : Nat} (b x : ℝ)
    (M : Fin p → Fin N → ℂ) (lam : Fin p → ℝ) :
    (x : ℂ) ∉ mixtureSingularSet b M lam :=
  KHead.ofReal_notMem_mixtureSingularSet b x M lam

/-- Coordinatewise holomorphy away from the aggregate singular set. -/
theorem sigmoidMixture_coord_analyticOnNhd_mixtureSingularSet_compl {p N : Nat}
    (b : ℝ) (H : ℂ → Fin N → ℂ) (M : Fin p → Fin N → ℂ)
    (lam : Fin p → ℝ)
    (hH : ∀ j : Fin N,
      AnalyticOnNhd ℂ (fun τ : ℂ => H τ j) (mixtureSingularSet b M lam)ᶜ) :
    ∀ j : Fin N,
      AnalyticOnNhd ℂ (fun τ : ℂ => sigmoidMixture b H M lam τ j)
        (mixtureSingularSet b M lam)ᶜ :=
  KHead.sigmoidMixture_coord_analyticOnNhd_mixtureSingularSet_compl b H M lam hH

/-- Entire-constant mixtures are holomorphic coordinatewise away from their
aggregate singular set. -/
theorem constantSigmoidMixture_coord_analyticOnNhd_mixtureSingularSet_compl
    {p N : Nat} (b : ℝ) (C : Fin N → ℂ)
    (M : Fin p → Fin N → ℂ) (lam : Fin p → ℝ) :
    ∀ j : Fin N,
      AnalyticOnNhd ℂ (fun τ : ℂ => constantSigmoidMixture b C M lam τ j)
        (mixtureSingularSet b M lam)ᶜ :=
  sigmoidMixture_coord_analyticOnNhd_mixtureSingularSet_compl b
    (fun _ : ℂ => C) M lam (by
      intro j τ _hτ
      exact analyticAt_const)

/-- A nonzero aggregate coordinate produces genuine blow-up at each point of its
separated pole progression.  This is the local residue-detection interface. -/
theorem sigmoidMixture_coord_blowsUpAt_of_aggregate_ne {p N : Nat}
    {b slope : ℝ} {ξ : ℂ}
    (hb : b ≠ 0) (hslope : slope ≠ 0)
    (hξ : ξ ∈ affineSigmoidPoleSet b slope)
    {H : ℂ → Fin N → ℂ} {M : Fin p → Fin N → ℂ} {lam : Fin p → ℝ}
    (hH : ∀ j : Fin N, AnalyticAt ℂ (fun τ : ℂ => H τ j) ξ)
    {j : Fin N} (hcoeff : aggregateCoeff M lam slope j ≠ 0) :
    BlowsUpAt (fun τ : ℂ => sigmoidMixture b H M lam τ j) ξ :=
  KHead.sigmoidMixture_coord_blowsUpAt_of_aggregate_ne
    hb hslope hξ hH hcoeff

/-- Entire-constant specialization of local aggregate pole detection. -/
theorem constantSigmoidMixture_coord_blowsUpAt_of_aggregate_ne {p N : Nat}
    {b slope : ℝ} {ξ : ℂ}
    (hb : b ≠ 0) (hslope : slope ≠ 0)
    (hξ : ξ ∈ affineSigmoidPoleSet b slope)
    {C : Fin N → ℂ} {M : Fin p → Fin N → ℂ} {lam : Fin p → ℝ}
    {j : Fin N} (hcoeff : aggregateCoeff M lam slope j ≠ 0) :
    BlowsUpAt (fun τ : ℂ => constantSigmoidMixture b C M lam τ j) ξ :=
  sigmoidMixture_coord_blowsUpAt_of_aggregate_ne hb hslope hξ
    (by
      intro i
      exact analyticAt_const)
    hcoeff

/-- A nonzero aggregate-coefficient gap creates a genuine pole in the difference
of two mixtures. -/
theorem sigmoidMixture_coord_sub_blowsUpAt_of_aggregateCoeff_sub_ne {p q N : Nat}
    {b slope : ℝ} {ξ : ℂ}
    (hb : b ≠ 0) (hslope : slope ≠ 0)
    (hξ : ξ ∈ affineSigmoidPoleSet b slope)
    {H H' : ℂ → Fin N → ℂ}
    {M : Fin p → Fin N → ℂ} {lam : Fin p → ℝ}
    {M' : Fin q → Fin N → ℂ} {lam' : Fin q → ℝ}
    (hH : ∀ j : Fin N, AnalyticAt ℂ (fun τ : ℂ => H τ j) ξ)
    (hH' : ∀ j : Fin N, AnalyticAt ℂ (fun τ : ℂ => H' τ j) ξ)
    {j : Fin N}
    (hcoeff : aggregateCoeff M lam slope j -
      aggregateCoeff M' lam' slope j ≠ 0) :
    BlowsUpAt
      (fun τ : ℂ =>
        sigmoidMixture b H M lam τ j - sigmoidMixture b H' M' lam' τ j) ξ :=
  KHead.sigmoidMixture_coord_sub_blowsUpAt_of_aggregateCoeff_sub_ne
    hb hslope hξ hH hH' hcoeff

/-- Real-tail equality recovers an aggregate coefficient at a slope belonging to
both aggregate supports. -/
theorem aggregateCoeff_eq_of_sigmoidMixture_real_tail_eq_of_mem_slopeSupportFinset
    {p q N : Nat} {b T0 : ℝ}
    (hb : b ≠ 0)
    {H H' : ℂ → Fin N → ℂ}
    {M : Fin p → Fin N → ℂ} {lam : Fin p → ℝ}
    {M' : Fin q → Fin N → ℂ} {lam' : Fin q → ℝ}
    (hH : ∀ j : Fin N, ∀ τ : ℂ, AnalyticAt ℂ (fun z : ℂ => H z j) τ)
    (hH' : ∀ j : Fin N, ∀ τ : ℂ, AnalyticAt ℂ (fun z : ℂ => H' z j) τ)
    (hEq : ∀ t : ℝ, T0 < t →
      sigmoidMixture b H M lam (t : ℂ) =
        sigmoidMixture b H' M' lam' (t : ℂ))
    {slope : ℝ}
    (hslope : slope ∈ slopeSupportFinset M lam)
    (hslope' : slope ∈ slopeSupportFinset M' lam') :
    aggregateCoeff M lam slope = aggregateCoeff M' lam' slope :=
  KHead.aggregateCoeff_eq_of_sigmoidMixture_real_tail_eq_of_mem_slopeSupportFinset
    hb hH hH' hEq hslope hslope'

/-- Entire-constant specialization of recovery at a common supported slope. -/
theorem aggregateCoeff_eq_of_constantSigmoidMixture_real_tail_eq_of_mem_slopeSupportFinset
    {p q N : Nat} {b T0 : ℝ}
    (hb : b ≠ 0)
    {C C' : Fin N → ℂ}
    {M : Fin p → Fin N → ℂ} {lam : Fin p → ℝ}
    {M' : Fin q → Fin N → ℂ} {lam' : Fin q → ℝ}
    (hEq : ∀ t : ℝ, T0 < t →
      constantSigmoidMixture b C M lam (t : ℂ) =
        constantSigmoidMixture b C' M' lam' (t : ℂ))
    {slope : ℝ}
    (hslope : slope ∈ slopeSupportFinset M lam)
    (hslope' : slope ∈ slopeSupportFinset M' lam') :
    aggregateCoeff M lam slope = aggregateCoeff M' lam' slope :=
  aggregateCoeff_eq_of_sigmoidMixture_real_tail_eq_of_mem_slopeSupportFinset
    (H := fun _ : ℂ => C) (H' := fun _ : ℂ => C') hb
    (by
      intro j τ
      exact analyticAt_const)
    (by
      intro j τ
      exact analyticAt_const)
    hEq hslope hslope'

/-- Real-tail equality plus support equality recovers every nonzero aggregate
coefficient. -/
theorem aggregateCoeff_eq_of_sigmoidMixture_real_tail_eq_of_slopeSupportFinset_eq
    {p q N : Nat} {b T0 : ℝ}
    (hb : b ≠ 0)
    {H H' : ℂ → Fin N → ℂ}
    {M : Fin p → Fin N → ℂ} {lam : Fin p → ℝ}
    {M' : Fin q → Fin N → ℂ} {lam' : Fin q → ℝ}
    (hH : ∀ j : Fin N, ∀ τ : ℂ, AnalyticAt ℂ (fun z : ℂ => H z j) τ)
    (hH' : ∀ j : Fin N, ∀ τ : ℂ, AnalyticAt ℂ (fun z : ℂ => H' z j) τ)
    (hEq : ∀ t : ℝ, T0 < t →
      sigmoidMixture b H M lam (t : ℂ) =
        sigmoidMixture b H' M' lam' (t : ℂ))
    (hsupp : slopeSupportFinset M lam = slopeSupportFinset M' lam') :
    ∀ slope : ℝ, slope ≠ 0 →
      aggregateCoeff M lam slope = aggregateCoeff M' lam' slope :=
  KHead.aggregateCoeff_eq_of_sigmoidMixture_real_tail_eq_of_slopeSupportFinset_eq
    hb hH hH' hEq hsupp

/-- Entire-constant specialization of aggregate coefficient recovery.  The
constants may differ, matching the no-skip base-case formula. -/
theorem aggregateCoeff_eq_of_constantSigmoidMixture_real_tail_eq_of_slopeSupportFinset_eq
    {p q N : Nat} {b T0 : ℝ}
    (hb : b ≠ 0)
    {C C' : Fin N → ℂ}
    {M : Fin p → Fin N → ℂ} {lam : Fin p → ℝ}
    {M' : Fin q → Fin N → ℂ} {lam' : Fin q → ℝ}
    (hEq : ∀ t : ℝ, T0 < t →
      constantSigmoidMixture b C M lam (t : ℂ) =
        constantSigmoidMixture b C' M' lam' (t : ℂ))
    (hsupp : slopeSupportFinset M lam = slopeSupportFinset M' lam') :
    ∀ slope : ℝ, slope ≠ 0 →
      aggregateCoeff M lam slope = aggregateCoeff M' lam' slope := by
  exact aggregateCoeff_eq_of_sigmoidMixture_real_tail_eq_of_slopeSupportFinset_eq
    (H := fun _ : ℂ => C) (H' := fun _ : ℂ => C') hb
    (by
      intro j τ
      exact analyticAt_const)
    (by
      intro j τ
      exact analyticAt_const)
    hEq hsupp

/-- Separated nonzero heads are recovered from aggregate support, aggregate
coefficients, and the disjoint union of their pole progressions. -/
theorem lem_explicit_sigmoid_mixture_recovery {p N : Nat} (b : ℝ)
    {M : Fin p → Fin N → ℂ} {lam : Fin p → ℝ}
    (hpair : Pairwise fun i j => lam i ≠ lam j)
    (hlam : ∀ h : Fin p, lam h ≠ 0)
    (hM : ∀ h : Fin p, M h ≠ 0) :
    slopeSupportFinset M lam = Finset.univ.image lam ∧
      (∀ h : Fin p, aggregateCoeff M lam (lam h) = M h) ∧
      mixtureSingularSet b M lam =
        ⋃ h : Fin p, affineSigmoidPoleSet b (lam h) :=
  KHead.lem_explicit_sigmoid_mixture_recovery b hpair hlam hM

/-- Aggregate coefficient equality packages the recovered support and singular
set equalities. -/
theorem lem_explicit_sigmoid_mixture_aggregate_matching {p q N : Nat} (b : ℝ)
    {M : Fin p → Fin N → ℂ} {lam : Fin p → ℝ}
    {M' : Fin q → Fin N → ℂ} {lam' : Fin q → ℝ}
    (hagg : ∀ slope : ℝ, slope ≠ 0 →
      aggregateCoeff M lam slope = aggregateCoeff M' lam' slope) :
    slopeSupportFinset M lam = slopeSupportFinset M' lam' ∧
      mixtureSingularSet b M lam = mixtureSingularSet b M' lam' :=
  KHead.lem_explicit_sigmoid_mixture_aggregate_matching b hagg

/-! ## Polynomial zero sets and coefficient witnesses -/

/-- The evaluation zero set of a real multivariate polynomial. -/
def mvPolynomialZeroSet {ι : Type*} (p : MvPolynomial ι ℝ) : Set (ι → ℝ) :=
  {x | MvPolynomial.eval x p = 0}

/-- The evaluation nonvanishing locus of a real multivariate polynomial. -/
def mvPolynomialNonvanishingSet {ι : Type*}
    (p : MvPolynomial ι ℝ) : Set (ι → ℝ) :=
  {x | MvPolynomial.eval x p ≠ 0}

/-- A nonzero real coordinate polynomial has a Lebesgue-null zero set. -/
theorem mvPolynomial_zeroSet_null {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : MvPolynomial ι ℝ) (hp : p ≠ 0) :
    MeasureTheory.volume (mvPolynomialZeroSet p) = 0 := by
  simpa [mvPolynomialZeroSet] using
    TransformerIdentifiability.NLayer.mvpoly_eval_null' p hp

/-- A real coordinate-polynomial zero set is closed. -/
theorem mvPolynomial_zeroSet_closed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : MvPolynomial ι ℝ) :
    IsClosed (mvPolynomialZeroSet p) := by
  simpa [mvPolynomialZeroSet] using
    (isClosed_singleton.preimage (MvPolynomial.continuous_eval p))

/-- A nonzero real coordinate polynomial has zero set with empty interior. -/
theorem mvPolynomial_zeroSet_interior_eq_empty
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : MvPolynomial ι ℝ) (hp : p ≠ 0) :
    interior (mvPolynomialZeroSet p) = ∅ := by
  rw [interior_eq_empty_iff_dense_compl]
  simpa [mvPolynomialZeroSet, mvPolynomialNonvanishingSet] using
    TransformerIdentifiability.NLayer.dense_compl_zero_set p hp

/-- The nonvanishing locus of a nonzero real coordinate polynomial is dense. -/
theorem dense_mvPolynomialNonvanishingSet
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : MvPolynomial ι ℝ) (hp : p ≠ 0) :
    Dense (mvPolynomialNonvanishingSet p) := by
  simpa [mvPolynomialNonvanishingSet] using
    TransformerIdentifiability.NLayer.dense_compl_zero_set p hp

/-- The nonvanishing locus of every real coordinate polynomial is open. -/
theorem isOpen_mvPolynomialNonvanishingSet
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : MvPolynomial ι ℝ) :
    IsOpen (mvPolynomialNonvanishingSet p) := by
  simpa [mvPolynomialNonvanishingSet] using
    TransformerIdentifiability.NLayer.isOpen_eval_ne_zero p

/-- Vanishing on a nonempty open set forces a real multivariate polynomial to
be the zero polynomial. -/
theorem mvPolynomial_eq_zero_of_eval_eqOn_isOpen
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : MvPolynomial ι ℝ} {U : Set (ι → ℝ)}
    (hU : IsOpen U) (hUne : U.Nonempty)
    (hp : ∀ x ∈ U, MvPolynomial.eval x p = 0) :
    p = 0 :=
  TransformerIdentifiability.NLayer.eq_zero_of_eval_eqOn_isOpen hU hUne hp

/-- One nonzero evaluation witnesses that a real multivariate polynomial is
nonzero. -/
theorem mvPolynomial_ne_zero_of_eval_ne_zero {ι : Type*}
    (p : MvPolynomial ι ℝ) (x : ι → ℝ)
    (hp : MvPolynomial.eval x p ≠ 0) :
    p ≠ 0 := by
  intro hzero
  exact hp (by simp [hzero])

/-- A multivariate polynomial is zero exactly when all monomial coefficients
vanish. -/
theorem mvPolynomial_eq_zero_iff_coeff_eq_zero
    {ι R : Type*} [CommSemiring R] (p : MvPolynomial ι R) :
    p = 0 ↔ ∀ m, MvPolynomial.coeff m p = 0 := by
  constructor
  · intro hp m
    simp [hp]
  · intro hp
    ext m
    simpa using hp m

/-- A multivariate polynomial is nonzero exactly when one monomial coefficient
is nonzero. -/
theorem mvPolynomial_ne_zero_iff_exists_coeff_ne_zero
    {ι R : Type*} [CommSemiring R] (p : MvPolynomial ι R) :
    p ≠ 0 ↔ ∃ m, MvPolynomial.coeff m p ≠ 0 := by
  classical
  constructor
  · intro hp
    by_contra hcoeff
    simp only [not_exists, not_not] at hcoeff
    exact hp ((mvPolynomial_eq_zero_iff_coeff_eq_zero p).2 hcoeff)
  · rintro ⟨m, hm⟩ hzero
    exact hm (by simp [hzero])

/-- A single nonzero monomial coefficient witnesses multivariate-polynomial
nonvanishing. -/
theorem mvPolynomial_ne_zero_of_coeff_ne_zero
    {ι R : Type*} [CommSemiring R] {p : MvPolynomial ι R} {m}
    (hm : MvPolynomial.coeff m p ≠ 0) :
    p ≠ 0 :=
  (mvPolynomial_ne_zero_iff_exists_coeff_ne_zero p).2 ⟨m, hm⟩

/-- A univariate polynomial is zero exactly when every coefficient vanishes. -/
theorem polynomial_eq_zero_iff_coeff_eq_zero
    {R : Type*} [Semiring R] (p : Polynomial R) :
    p = 0 ↔ ∀ n, p.coeff n = 0 := by
  constructor
  · intro hp n
    simp [hp]
  · intro hp
    ext n
    simpa using hp n

/-- A univariate polynomial is nonzero exactly when one coefficient is
nonzero.  This applies in particular to `Polynomial (MvPolynomial ι ℝ)`, the
coefficient-polynomial type used by the genericity certificates. -/
theorem polynomial_ne_zero_iff_exists_coeff_ne_zero
    {R : Type*} [Semiring R] (p : Polynomial R) :
    p ≠ 0 ↔ ∃ n, p.coeff n ≠ 0 := by
  classical
  constructor
  · intro hp
    by_contra hcoeff
    simp only [not_exists, not_not] at hcoeff
    exact hp ((polynomial_eq_zero_iff_coeff_eq_zero p).2 hcoeff)
  · rintro ⟨n, hn⟩ hzero
    exact hn (by simp [hzero])

/-- A nonzero coefficient witnesses univariate-polynomial nonvanishing. -/
theorem polynomial_ne_zero_of_coeff_ne_zero
    {R : Type*} [Semiring R] {p : Polynomial R} {n : Nat}
    (hn : p.coeff n ≠ 0) :
    p ≠ 0 :=
  (polynomial_ne_zero_iff_exists_coeff_ne_zero p).2 ⟨n, hn⟩

/-- A nonzero polynomial has a nonzero coefficient. -/
theorem exists_polynomial_coeff_ne_zero_of_ne_zero
    {R : Type*} [Semiring R] {p : Polynomial R} (hp : p ≠ 0) :
    ∃ n, p.coeff n ≠ 0 :=
  (polynomial_ne_zero_iff_exists_coeff_ne_zero p).1 hp

/-- Finite products of nonzero multivariate polynomials remain nonzero. -/
theorem mvPolynomial_finset_prod_ne_zero {ι κ : Type*} {s : Finset κ}
    {p : κ → MvPolynomial ι ℝ} (hp : ∀ a, a ∈ s → p a ≠ 0) :
    (∏ a ∈ s, p a) ≠ 0 :=
  TransformerIdentifiability.NLayer.mvpoly_finset_prod_ne_zero hp

/-- The common nonvanishing locus of a finite family of nonzero coordinate
polynomials is dense. -/
theorem dense_forall_mvPolynomial_eval_ne_zero_finset
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    {s : Finset κ} {p : κ → MvPolynomial ι ℝ}
    (hp : ∀ a, a ∈ s → p a ≠ 0) :
    Dense {x : ι → ℝ |
      ∀ a, a ∈ s → MvPolynomial.eval x (p a) ≠ 0} :=
  TransformerIdentifiability.NLayer.dense_forall_eval_ne_zero_finset hp

/-- The common nonvanishing locus of a finite coordinate-polynomial family is
open. -/
theorem isOpen_forall_mvPolynomial_eval_ne_zero_finset
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset κ) (p : κ → MvPolynomial ι ℝ) :
    IsOpen {x : ι → ℝ |
      ∀ a, a ∈ s → MvPolynomial.eval x (p a) ≠ 0} :=
  TransformerIdentifiability.NLayer.isOpen_forall_eval_ne_zero_finset s p

/-- A finite product of nonzero coordinate polynomials has a null zero set. -/
theorem mvPolynomial_finset_product_zeroSet_null
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    {s : Finset κ} {p : κ → MvPolynomial ι ℝ}
    (hp : ∀ a, a ∈ s → p a ≠ 0) :
    MeasureTheory.volume
      (mvPolynomialZeroSet (∏ a ∈ s, p a)) = 0 :=
  mvPolynomial_zeroSet_null _ (mvPolynomial_finset_prod_ne_zero hp)

/-- A packaged finite family of nonzero real coordinate polynomials. -/
abbrev PolynomialNonvanishingData (ι κ : Type*) :=
  TransformerIdentifiability.NLayer.PolynomialNonvanishingData ι κ

namespace PolynomialNonvanishingData

/-- Common nonvanishing carrier of a packaged polynomial family. -/
abbrev carrier {ι κ : Type*} (D : PolynomialNonvanishingData ι κ) :
    Set (ι → ℝ) :=
  TransformerIdentifiability.NLayer.PolynomialNonvanishingData.carrier D

/-- A packaged polynomial nonvanishing carrier is open. -/
theorem isOpen_carrier {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (D : PolynomialNonvanishingData ι κ) :
    IsOpen D.carrier :=
  TransformerIdentifiability.NLayer.PolynomialNonvanishingData.isOpen_carrier D

/-- A packaged polynomial nonvanishing carrier is dense. -/
theorem dense_carrier {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (D : PolynomialNonvanishingData ι κ) :
    Dense D.carrier :=
  TransformerIdentifiability.NLayer.PolynomialNonvanishingData.dense_carrier D

end PolynomialNonvanishingData

/-! ## Target-to-source attention matching -/

/-- Probe variables for a bilinear attention form: source/left variables followed
by target/right variables. -/
abbrev BilinVar (d : Nat) : Type :=
  KHead.BilinVar d

/-- Polynomial representing `wᵀ M v`. -/
noncomputable abbrev attentionBilinPoly {d : Nat}
    (M : Matrix (Fin d) (Fin d) ℝ) : MvPolynomial (BilinVar d) ℝ :=
  KHead.attentionBilinPoly M

/-- The factor `t - wᵀ M v`. -/
noncomputable abbrev attentionFactorPoly {d : Nat}
    (M : Matrix (Fin d) (Fin d) ℝ) :
    Polynomial (MvPolynomial (BilinVar d) ℝ) :=
  KHead.attentionFactorPoly M

/-- Product of the attention factors of a head family. -/
noncomputable abbrev attentionProductPoly {d k : Nat}
    (B : Fin k → Matrix (Fin d) (Fin d) ℝ) :
    Polynomial (MvPolynomial (BilinVar d) ℝ) :=
  KHead.attentionProductPoly B

/-- Zariski density in the bilinear probe coordinates. -/
abbrev ProbeZariskiDense {d : Nat}
    (U : Set ((Fin d → ℝ) × (Fin d → ℝ))) : Prop :=
  KHead.ProbeZariskiDense U

/-- Explicit orientation predicate: `σ` maps each target index `h` to its
matching source index `σ h`. -/
def TargetToSourcePermutation {k : Nat} {α : Type*}
    (source target : Fin k → α) (σ : Equiv.Perm (Fin k)) : Prop :=
  ∀ h, source (σ h) = target h

/-- Zariski-dense pointwise product equality gives equality of the formal
attention-product polynomials. -/
theorem attentionProductPoly_eq_of_probeZariskiDense {d k : Nat}
    (B B' : Fin k → Matrix (Fin d) (Fin d) ℝ)
    (U : Set ((Fin d → ℝ) × (Fin d → ℝ)))
    (hU : ProbeZariskiDense U)
    (hprodU : ∀ x ∈ U, ∀ t : ℝ,
      ∏ c : Fin k, (t - x.1 ⬝ᵥ (B c).mulVec x.2) =
        ∏ h : Fin k, (t - x.1 ⬝ᵥ (B' h).mulVec x.2)) :
    attentionProductPoly B = attentionProductPoly B' :=
  KHead.attentionProductPoly_eq_of_probeZariskiDense B B' U hU hprodU

/-- Zariski-dense probe equality globalizes to the pointwise product identity
for every real `(t,w,v)`. -/
theorem attention_product_identity_of_probeZariskiDense {d k : Nat}
    (B B' : Fin k → Matrix (Fin d) (Fin d) ℝ)
    (U : Set ((Fin d → ℝ) × (Fin d → ℝ)))
    (hU : ProbeZariskiDense U)
    (hprodU : ∀ x ∈ U, ∀ t : ℝ,
      ∏ c : Fin k, (t - x.1 ⬝ᵥ (B c).mulVec x.2) =
        ∏ h : Fin k, (t - x.1 ⬝ᵥ (B' h).mulVec x.2)) :
    ∀ (t : ℝ) (w v : Fin d → ℝ),
      ∏ c : Fin k, (t - w ⬝ᵥ (B c).mulVec v) =
        ∏ h : Fin k, (t - w ⬝ᵥ (B' h).mulVec v) :=
  KHead.attention_product_identity_of_probeZariskiDense B B' U hU hprodU

/-- Unique attention matching with the TeX orientation: the returned
permutation maps target head `h` to source head `σ h`. -/
theorem unique_attention_permutation {d k : Nat}
    (B B' : Fin k → Matrix (Fin d) (Fin d) ℝ)
    (hB' : Function.Injective B')
    (hid : ∀ (t : ℝ) (w v : Fin d → ℝ),
      ∏ c : Fin k, (t - w ⬝ᵥ (B c).mulVec v) =
        ∏ h : Fin k, (t - w ⬝ᵥ (B' h).mulVec v)) :
    ∃! σ : Equiv.Perm (Fin k), TargetToSourcePermutation B B' σ := by
  simpa [TargetToSourcePermutation] using
    KHead.unique_attention_permutation B B' hB' hid

/-- Algebraic global labeling from product equality on a Zariski-dense probe
set, again target-to-source. -/
theorem global_labeling_algebraic {d k : Nat}
    (B B' : Fin k → Matrix (Fin d) (Fin d) ℝ)
    (U : Set ((Fin d → ℝ) × (Fin d → ℝ)))
    (hB' : Function.Injective B')
    (hU : ProbeZariskiDense U)
    (hprodU : ∀ x ∈ U, ∀ t : ℝ,
      ∏ c : Fin k, (t - x.1 ⬝ᵥ (B c).mulVec x.2) =
        ∏ h : Fin k, (t - x.1 ⬝ᵥ (B' h).mulVec x.2)) :
    ∃! σ : Equiv.Perm (Fin k), TargetToSourcePermutation B B' σ := by
  simpa [TargetToSourcePermutation] using
    KHead.global_labeling_algebraic B B' U hB' hU hprodU

/-- Pointwise unique target-to-source matching for two scalar head families. -/
theorem pointwise_unique_matching {k : Nat}
    (q q' : Fin k → ℝ)
    (hq' : Function.Injective q')
    (hprod : ∀ t : ℝ,
      ∏ c : Fin k, (t - q c) = ∏ h : Fin k, (t - q' h)) :
    ∃! σ : Equiv.Perm (Fin k), TargetToSourcePermutation q q' σ := by
  simpa [TargetToSourcePermutation] using
    KHead.pointwise_unique_matching q q' hq' hprod

/-- Canonical pointwise target-to-source permutation selected from product
equality. -/
noncomputable abbrev pointwiseProductMatching {X : Type*} {k : Nat}
    (q q' : X → Fin k → ℝ)
    (hq' : ∀ x, Function.Injective (q' x))
    (hprod : ∀ x, ∀ t : ℝ,
      ∏ c : Fin k, (t - q x c) = ∏ h : Fin k, (t - q' x h)) :
    X → Equiv.Perm (Fin k) :=
  KHead.pointwiseProductMatching q q' hq' hprod

/-- Specification of the canonical pointwise target-to-source permutation. -/
theorem pointwiseProductMatching_spec {X : Type*} {k : Nat}
    (q q' : X → Fin k → ℝ)
    (hq' : ∀ x, Function.Injective (q' x))
    (hprod : ∀ x, ∀ t : ℝ,
      ∏ c : Fin k, (t - q x c) = ∏ h : Fin k, (t - q' x h))
    (x : X) :
    TargetToSourcePermutation (q x) (q' x)
      (pointwiseProductMatching q q' hq' hprod x) := by
  simpa [TargetToSourcePermutation] using
    KHead.pointwiseProductMatching_spec q q' hq' hprod x

/-- The bilinear-probe pointwise matching map on a probe set. -/
noncomputable abbrev attentionGlobalLabelingMatching {d k : Nat}
    (B B' : Fin k → Matrix (Fin d) (Fin d) ℝ)
    (U : Set ((Fin d → ℝ) × (Fin d → ℝ)))
    (hsep : ∀ x, x ∈ U →
      Function.Injective (fun h : Fin k => x.1 ⬝ᵥ (B' h).mulVec x.2))
    (hprodU : ∀ x, x ∈ U → ∀ t : ℝ,
      ∏ c : Fin k, (t - x.1 ⬝ᵥ (B c).mulVec x.2) =
        ∏ h : Fin k, (t - x.1 ⬝ᵥ (B' h).mulVec x.2)) :
    U → Equiv.Perm (Fin k) :=
  KHead.attentionGlobalLabelingMatching B B' U hsep hprodU

/-- Full global-labeling interface: local constancy, constancy on connected
components, and one unique target-to-source matrix permutation agreeing with
every pointwise label. -/
theorem global_labeling {d k : Nat}
    (B B' : Fin k → Matrix (Fin d) (Fin d) ℝ)
    (U : Set ((Fin d → ℝ) × (Fin d → ℝ)))
    (hsep : ∀ x, x ∈ U →
      Function.Injective (fun h : Fin k => x.1 ⬝ᵥ (B' h).mulVec x.2))
    (hprodU : ∀ x, x ∈ U → ∀ t : ℝ,
      ∏ c : Fin k, (t - x.1 ⬝ᵥ (B c).mulVec x.2) =
        ∏ h : Fin k, (t - x.1 ⬝ᵥ (B' h).mulVec x.2))
    (hB' : Function.Injective B')
    (hU : ProbeZariskiDense U) :
    IsLocallyConstant (attentionGlobalLabelingMatching B B' U hsep hprodU) ∧
      (∀ {C : Set U}, IsPreconnected C → ∀ {x y : U},
        x ∈ C → y ∈ C →
          attentionGlobalLabelingMatching B B' U hsep hprodU x =
            attentionGlobalLabelingMatching B B' U hsep hprodU y) ∧
      ∃! σ : Equiv.Perm (Fin k),
        TargetToSourcePermutation B B' σ ∧
          ∀ x : U,
            attentionGlobalLabelingMatching B B' U hsep hprodU x = σ := by
  simpa [TargetToSourcePermutation] using
    KHead.global_labeling B B' U hsep hprodU hB' hU

/-! ## Elementary slices, relative openness, and open-set rigidity -/

/-- Slice of a subset of a product at a fixed second coordinate. -/
def firstCoordinateSlice {α β : Type*} (U : Set (α × β)) (y : β) : Set α :=
  {x | (x, y) ∈ U}

/-- Slice of a subset of a product at a fixed first coordinate. -/
def secondCoordinateSlice {α β : Type*} (U : Set (α × β)) (x : α) : Set β :=
  {y | (x, y) ∈ U}

/-- A first-coordinate slice of an ambient open product set is open. -/
theorem isOpen_firstCoordinateSlice
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {U : Set (α × β)} (hU : IsOpen U) (y : β) :
    IsOpen (firstCoordinateSlice U y) := by
  exact hU.preimage (continuous_id.prodMk continuous_const)

/-- A second-coordinate slice of an ambient open product set is open. -/
theorem isOpen_secondCoordinateSlice
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {U : Set (α × β)} (hU : IsOpen U) (x : α) :
    IsOpen (secondCoordinateSlice U x) := by
  exact hU.preimage (continuous_const.prodMk continuous_id)

/-- A nonempty open product set has a nonempty open first-coordinate slice. -/
theorem exists_nonempty_open_firstCoordinateSlice
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {U : Set (α × β)} (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ y : β, IsOpen (firstCoordinateSlice U y) ∧
      (firstCoordinateSlice U y).Nonempty := by
  rcases hUne with ⟨⟨x, y⟩, hxy⟩
  exact ⟨y, isOpen_firstCoordinateSlice hU y, x, hxy⟩

/-- A nonempty open product set has a nonempty open second-coordinate slice. -/
theorem exists_nonempty_open_secondCoordinateSlice
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {U : Set (α × β)} (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ x : α, IsOpen (secondCoordinateSlice U x) ∧
      (secondCoordinateSlice U x).Nonempty := by
  rcases hUne with ⟨⟨x, y⟩, hxy⟩
  exact ⟨x, isOpen_secondCoordinateSlice hU x, y, hxy⟩

/-- The empty subset is relatively open in every ambient set. -/
theorem relativelyOpenIn_empty {α : Type*} [TopologicalSpace α]
    (ambient : Set α) :
    RelativelyOpenIn ∅ ambient :=
  ⟨∅, isOpen_empty, by simp⟩

/-- Every ambient set is relatively open in itself. -/
theorem relativelyOpenIn_self {α : Type*} [TopologicalSpace α]
    (ambient : Set α) :
    RelativelyOpenIn ambient ambient :=
  ⟨Set.univ, isOpen_univ, by simp⟩

/-- Relative openness is preserved by intersecting with an ambient open set. -/
theorem RelativelyOpenIn.inter_open {α : Type*} [TopologicalSpace α]
    {U H O : Set α} (hU : RelativelyOpenIn U H) (hO : IsOpen O) :
    RelativelyOpenIn (U ∩ O) H := by
  rcases hU with ⟨O₀, hO₀, rfl⟩
  refine ⟨O₀ ∩ O, hO₀.inter hO, ?_⟩
  ext x
  simp [and_left_comm, and_comm]

/-- Relative openness is preserved by finite intersections in one ambient set. -/
theorem RelativelyOpenIn.inter {α : Type*} [TopologicalSpace α]
    {U V H : Set α} (hU : RelativelyOpenIn U H)
    (hV : RelativelyOpenIn V H) :
    RelativelyOpenIn (U ∩ V) H := by
  rcases hU with ⟨Oᵤ, hOᵤ, rfl⟩
  rcases hV with ⟨Oᵥ, hOᵥ, rfl⟩
  refine ⟨Oᵤ ∩ Oᵥ, hOᵤ.inter hOᵥ, ?_⟩
  ext x
  simp [and_left_comm, and_assoc, and_comm]

/-- Products of open sets are open. -/
theorem isOpen_set_prod {α β : Type*}
    [TopologicalSpace α] [TopologicalSpace β]
    {U : Set α} {V : Set β} (hU : IsOpen U) (hV : IsOpen V) :
    IsOpen (U ×ˢ V) :=
  hU.prod hV

/-- Products of preconnected sets are preconnected. -/
theorem isPreconnected_set_prod {α β : Type*}
    [TopologicalSpace α] [TopologicalSpace β]
    {U : Set α} {V : Set β} (hU : IsPreconnected U)
    (hV : IsPreconnected V) :
    IsPreconnected (U ×ˢ V) :=
  hU.prod hV

/-- Products of connected sets are connected. -/
theorem isConnected_set_prod {α β : Type*}
    [TopologicalSpace α] [TopologicalSpace β]
    {U : Set α} {V : Set β} (hU : IsConnected U)
    (hV : IsConnected V) :
    IsConnected (U ×ˢ V) :=
  hU.prod hV

/-- Convex real sets are preconnected. -/
theorem isPreconnected_of_convex {E : Type*}
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U : Set E} (hU : Convex ℝ U) :
    IsPreconnected U :=
  hU.isPreconnected

/-- Nonempty convex real sets are connected. -/
theorem isConnected_of_convex {E : Type*}
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U : Set E} (hU : Convex ℝ U) (hUne : U.Nonempty) :
    IsConnected U :=
  ⟨hUne, hU.isPreconnected⟩

/-- A nonempty real open interval is connected. -/
theorem isConnected_Ioo_of_lt {a b : ℝ} (hab : a < b) :
    IsConnected (Set.Ioo a b) :=
  ⟨⟨(a + b) / 2, by constructor <;> linarith⟩, isPreconnected_Ioo⟩

/-- A nested three-factor product of connected sets is connected. -/
theorem isConnected_set_prod3 {α β γ : Type*}
    [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
    {U : Set α} {V : Set β} {W : Set γ}
    (hU : IsConnected U) (hV : IsConnected V) (hW : IsConnected W) :
    IsConnected ((U ×ˢ V) ×ˢ W) :=
  (hU.prod hV).prod hW

/-- A nested three-factor product of open sets is open. -/
theorem isOpen_set_prod3 {α β γ : Type*}
    [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
    {U : Set α} {V : Set β} {W : Set γ}
    (hU : IsOpen U) (hV : IsOpen V) (hW : IsOpen W) :
    IsOpen ((U ×ˢ V) ×ˢ W) :=
  (hU.prod hV).prod hW

/-- A nested three-factor product of preconnected sets is preconnected. -/
theorem isPreconnected_set_prod3 {α β γ : Type*}
    [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
    {U : Set α} {V : Set β} {W : Set γ}
    (hU : IsPreconnected U) (hV : IsPreconnected V)
    (hW : IsPreconnected W) :
    IsPreconnected ((U ×ˢ V) ×ˢ W) :=
  (hU.prod hV).prod hW

/-! ### Neutral affine and open-eigenvector facts -/

/-- Linear hyperplane with normal `u`. -/
abbrev hyperplane {d : Nat} (u : Fin d → ℝ) : Set (Fin d → ℝ) :=
  KHead.hyperplane u

/-- An affine scalar map vanishing on a nonempty relatively open subset of a
nonzero hyperplane vanishes on the entire hyperplane. -/
theorem lem_affine_hyperplane {d : Nat} {u c : Fin d → ℝ} {β : ℝ}
    {O : Set (Fin d → ℝ)} (hu : u ≠ 0)
    (hO_rel : RelativelyOpenIn O (hyperplane u))
    (hO_nonempty : O.Nonempty)
    (hzero : ∀ v : Fin d → ℝ, v ∈ O → dotProduct c v + β = 0) :
    (∀ v : Fin d → ℝ, v ∈ hyperplane u → dotProduct c v + β = 0) ∧
      (∃ a : ℝ, c = a • u) ∧ β = 0 :=
  KHead.lem_affine_hyperplane hu hO_rel hO_nonempty hzero

/-- A matrix having every vector in a nonempty open set as an eigenvector is a
scalar matrix. -/
theorem lem_eigenvector_open {d : Nat} (hd : 2 ≤ d)
    {Y : Set (Fin d → ℝ)} (hY_open : IsOpen Y) (hY_nonempty : Y.Nonempty)
    (M : Matrix (Fin d) (Fin d) ℝ)
    (hM : ∀ y : Fin d → ℝ, y ∈ Y → ∃ c : ℝ, M *ᵥ y = c • y) :
    ∃ c : ℝ, M = c • (1 : Matrix (Fin d) (Fin d) ℝ) :=
  KHead.lem_eigenvector_open hd hY_open hY_nonempty M hM

/-- A linear form vanishing on a nonempty open set vanishes identically. -/
theorem linearForm_eq_zero_of_forall_mem_open {d : Nat}
    {W : Set (Fin d → ℝ)} (hW_open : IsOpen W) (hW_nonempty : W.Nonempty)
    {r : Fin d → ℝ}
    (hzero : ∀ w : Fin d → ℝ, w ∈ W → dotProduct r w = 0) :
    r = 0 :=
  KHead.linearForm_eq_zero_of_forall_mem_open hW_open hW_nonempty hzero

/-- Rowwise linear-form vanishing on a nonempty open set forces a matrix to be
zero.  This is the open-`w` slice lemma used by BaseCase and multi-quadric
rigidity. -/
theorem matrix_eq_zero_of_forall_row_dotProduct_eq_zero_on_open {d : Nat}
    {W : Set (Fin d → ℝ)} (hW_open : IsOpen W) (hW_nonempty : W.Nonempty)
    {E : Matrix (Fin d) (Fin d) ℝ}
    (hzero : ∀ j : Fin d, ∀ w : Fin d → ℝ, w ∈ W →
      dotProduct (fun i : Fin d => E j i) w = 0) :
    E = 0 :=
  KHead.matrix_eq_zero_of_forall_row_dotProduct_eq_zero_on_open
    hW_open hW_nonempty hzero

/-- Direct matrix-vector form of the open-`w` slice lemma. -/
theorem matrix_eq_zero_of_forall_mulVec_eq_zero_on_open {d : Nat}
    {W : Set (Fin d → ℝ)} (hW_open : IsOpen W) (hW_nonempty : W.Nonempty)
    {E : Matrix (Fin d) (Fin d) ℝ}
    (hzero : ∀ w : Fin d → ℝ, w ∈ W → E *ᵥ w = 0) :
    E = 0 := by
  apply matrix_eq_zero_of_forall_row_dotProduct_eq_zero_on_open
    hW_open hW_nonempty
  intro j w hw
  simpa [Matrix.mulVec] using congrFun (hzero w hw) j

/-! ## Noncommutative telescoping and no-skip saturation matrices -/

/-- The noncommutative telescoping error
`Σ_{j=2}^L C_{L:j+1} (C_j-K_j) K_{j-1:2}`. -/
noncomputable def matrixTelescopingError {d : Nat}
    (C KLayer : Nat → Matrix (Fin d) (Fin d) ℝ) (L : Nat) :
    Matrix (Fin d) (Fin d) ℝ :=
  ∑ j ∈ Finset.Icc 2 L,
    layerProduct C L (j + 1) * (C j - KLayer j) *
      layerProduct KLayer (j - 1) 2

/-- Extend a nonempty layer product by one factor on the left. -/
theorem layerProduct_succ_left_of_le {d : Nat}
    (M : Nat → Matrix (Fin d) (Fin d) ℝ) {j i : Nat}
    (hi : i ≤ j + 1) :
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
    rw [show layerProduct M (j + 1) i =
        KHead.layerProductFrom M i (j + 1 - i + 1) by
          simp [KHead.layerProduct, hnot]]
    rw [show layerProduct M j i =
        KHead.layerProductFrom M i (j - i + 1) by
          simp [KHead.layerProduct, hji]]
    rw [hlen, KHead.layerProductFrom_succ, hidx]

/-- Model-neutral noncommutative telescoping identity, with products ordered as
`M_{j:i} = M_j⋯M_i`. -/
theorem matrix_telescoping_identity {d : Nat} (L : Nat)
    (C KLayer : Nat → Matrix (Fin d) (Fin d) ℝ) :
    layerProduct C L 2 - layerProduct KLayer L 2 =
      matrixTelescopingError C KLayer L := by
  induction L with
  | zero =>
      simp [matrixTelescopingError]
  | succ L ih =>
      by_cases hL : L = 0
      · subst L
        simp [matrixTelescopingError]
      · have h2 : 2 ≤ L + 1 := by omega
        let f : Nat → Matrix (Fin d) (Fin d) ℝ := fun j =>
          layerProduct C (L + 1) (j + 1) * (C j - KLayer j) *
            layerProduct KLayer (j - 1) 2
        calc
          layerProduct C (L + 1) 2 - layerProduct KLayer (L + 1) 2
              = C (L + 1) * layerProduct C L 2 -
                  KLayer (L + 1) * layerProduct KLayer L 2 := by
                rw [layerProduct_succ_left_of_le C h2,
                  layerProduct_succ_left_of_le KLayer h2]
          _ = C (L + 1) *
                (layerProduct C L 2 - layerProduct KLayer L 2) +
                (C (L + 1) - KLayer (L + 1)) *
                  layerProduct KLayer L 2 := by
                noncomm_ring
          _ = C (L + 1) * matrixTelescopingError C KLayer L +
                (C (L + 1) - KLayer (L + 1)) *
                  layerProduct KLayer L 2 := by
                rw [ih]
          _ = (∑ j ∈ Finset.Icc 2 L, f j) +
                (C (L + 1) - KLayer (L + 1)) *
                  layerProduct KLayer L 2 := by
                unfold matrixTelescopingError
                rw [Finset.mul_sum]
                apply congrArg (fun x => x +
                  (C (L + 1) - KLayer (L + 1)) *
                    layerProduct KLayer L 2)
                apply Finset.sum_congr rfl
                intro j hj
                have hjle : j + 1 ≤ L + 1 := by
                  have hj' := (Finset.mem_Icc.mp hj).2
                  omega
                dsimp [f]
                rw [layerProduct_succ_left_of_le C hjle]
                noncomm_ring
          _ = ∑ j ∈ Finset.Icc 2 (L + 1), f j := by
                rw [Finset.sum_Icc_succ_top h2]
                dsimp [f]
                simp
          _ = matrixTelescopingError C KLayer (L + 1) := by
                rfl

/-- Below the first tail layer, the telescoping sum is empty. -/
@[simp] theorem matrixTelescopingError_eq_zero_of_lt_two {d : Nat}
    (C KLayer : Nat → Matrix (Fin d) (Fin d) ℝ) {L : Nat} (hL : L < 2) :
    matrixTelescopingError C KLayer L = 0 := by
  unfold matrixTelescopingError
  have hempty : Finset.Icc 2 L = ∅ := by
    exact Finset.Icc_eq_empty (by omega)
  simp [hempty]

/-- Empty-product form of telescoping when `L < 2`. -/
theorem matrix_telescoping_empty {d : Nat}
    (C KLayer : Nat → Matrix (Fin d) (Fin d) ℝ) {L : Nat} (hL : L < 2) :
    layerProduct C L 2 = 1 ∧ layerProduct KLayer L 2 = 1 ∧
      matrixTelescopingError C KLayer L = 0 := by
  exact ⟨layerProduct_empty C hL, layerProduct_empty KLayer hL,
    matrixTelescopingError_eq_zero_of_lt_two C KLayer hL⟩

/-- Numeric saturated labels for all deeper layers. -/
abbrev NoSkipSaturatedLabels (k : Nat) : Type :=
  Nat → Fin k → ℝ

/-- No-skip collapsed layer matrix `C_l = Σ_a V_{la}`. -/
noncomputable def noSkipSaturatedC {k d : Nat}
    (V : Nat → Fin k → Matrix (Fin d) (Fin d) ℝ) (l : Nat) :
    Matrix (Fin d) (Fin d) ℝ :=
  ∑ a : Fin k, V l a

/-- Bridge to NS012: a parameter layer's no-skip saturated `C` is exactly its
`collapseMatrix = valueSum`. -/
theorem noSkipSaturatedC_of_params_eq_collapseMatrix {L k d : Nat}
    (θ : Params L k d) (l : Fin L) (n : Nat) :
    noSkipSaturatedC (fun _ a => valueMatrix θ l a) n =
      collapseMatrix θ l := by
  simp [noSkipSaturatedC, collapseMatrix_eq_valueSum, valueSum]

/-- Saturated contribution `D_l = Σ_a ζ_{la} V_{la}`. -/
noncomputable def noSkipSaturatedD {k d : Nat}
    (V : Nat → Fin k → Matrix (Fin d) (Fin d) ℝ)
    (ζ : NoSkipSaturatedLabels k) (l : Nat) :
    Matrix (Fin d) (Fin d) ℝ :=
  ∑ a : Fin k, ζ l a • V l a

/-- Saturated transport layer `K_l = C_l - D_l`. -/
noncomputable def noSkipSaturatedKLayer {k d : Nat}
    (V : Nat → Fin k → Matrix (Fin d) (Fin d) ℝ)
    (ζ : NoSkipSaturatedLabels k) (l : Nat) :
    Matrix (Fin d) (Fin d) ℝ :=
  noSkipSaturatedC V l - noSkipSaturatedD V ζ l

/-- TeX matrix `M = C_{L:2}`. -/
noncomputable def noSkipSaturatedM {d : Nat}
    (C : Nat → Matrix (Fin d) (Fin d) ℝ) (L : Nat) :
    Matrix (Fin d) (Fin d) ℝ :=
  layerProduct C L 2

/-- TeX matrix `E = Σ_{j=2}^L C_{L:j+1} D_j K_{j-1:2}`. -/
noncomputable def noSkipSaturatedE {d : Nat}
    (C D KLayer : Nat → Matrix (Fin d) (Fin d) ℝ) (L : Nat) :
    Matrix (Fin d) (Fin d) ℝ :=
  ∑ j ∈ Finset.Icc 2 L,
    layerProduct C L (j + 1) * D j *
      layerProduct KLayer (j - 1) 2

/-- TeX aggregate transport `K = M - E`. -/
noncomputable def noSkipSaturatedK {d : Nat}
    (M E : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  M - E

/-- Telescoping specialized to any supplied `D_j = C_j - K_j` family. -/
theorem noSkipSaturatedK_eq_layerProduct_of_sub_eq {d : Nat}
    (C D KLayer : Nat → Matrix (Fin d) (Fin d) ℝ) (L : Nat)
    (hD : ∀ j ∈ Finset.Icc 2 L, D j = C j - KLayer j) :
    noSkipSaturatedK (noSkipSaturatedM C L)
        (noSkipSaturatedE C D KLayer L) =
      layerProduct KLayer L 2 := by
  unfold noSkipSaturatedK noSkipSaturatedM noSkipSaturatedE
  have htel := matrix_telescoping_identity L C KLayer
  have hE :
      (∑ j ∈ Finset.Icc 2 L,
        layerProduct C L (j + 1) * D j *
          layerProduct KLayer (j - 1) 2) =
      matrixTelescopingError C KLayer L := by
    unfold matrixTelescopingError
    apply Finset.sum_congr rfl
    intro j hj
    rw [hD j hj]
  rw [hE, ← htel]
  abel

/-- Exact no-skip `C/D/K/E` specialization:
`M - E = K_{L:2}` for `C_l = Σ_a V_{la}` and
`D_l = Σ_a ζ_{la}V_{la}`. -/
theorem noSkipSaturatedK_eq_layerProduct {k d : Nat}
    (V : Nat → Fin k → Matrix (Fin d) (Fin d) ℝ)
    (ζ : NoSkipSaturatedLabels k) (L : Nat) :
    noSkipSaturatedK (noSkipSaturatedM (noSkipSaturatedC V) L)
        (noSkipSaturatedE (noSkipSaturatedC V) (noSkipSaturatedD V ζ)
          (noSkipSaturatedKLayer V ζ) L) =
      layerProduct (noSkipSaturatedKLayer V ζ) L 2 := by
  apply noSkipSaturatedK_eq_layerProduct_of_sub_eq
  intro j _hj
  dsimp [noSkipSaturatedKLayer]
  abel

/-- Empty-tail convention for the exact no-skip specialization. -/
theorem noSkipSaturated_empty {k d : Nat}
    (V : Nat → Fin k → Matrix (Fin d) (Fin d) ℝ)
    (ζ : NoSkipSaturatedLabels k) {L : Nat} (hL : L < 2) :
    noSkipSaturatedM (noSkipSaturatedC V) L = 1 ∧
      noSkipSaturatedE (noSkipSaturatedC V) (noSkipSaturatedD V ζ)
        (noSkipSaturatedKLayer V ζ) L = 0 ∧
      noSkipSaturatedK
        (noSkipSaturatedM (noSkipSaturatedC V) L)
        (noSkipSaturatedE (noSkipSaturatedC V) (noSkipSaturatedD V ζ)
          (noSkipSaturatedKLayer V ζ) L) = 1 := by
  have hM : noSkipSaturatedM (noSkipSaturatedC V) L = 1 := by
    exact layerProduct_empty _ hL
  have hE : noSkipSaturatedE (noSkipSaturatedC V) (noSkipSaturatedD V ζ)
      (noSkipSaturatedKLayer V ζ) L = 0 := by
    unfold noSkipSaturatedE
    have hempty : Finset.Icc 2 L = ∅ := Finset.Icc_eq_empty (by omega)
    simp [hempty]
  exact ⟨hM, hE, by simp [noSkipSaturatedK, hM, hE]⟩

end TransformerIdentifiability.NLayer.NoSkip
