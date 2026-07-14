import AnyLayerIdentifiabilityProof.NLayer.KHead.Permutation

/-!
# k-head probe-wise matching

This file contains the finite matching API used by the k-head permutation packet.  It is
the pointwise algebraic part of TeX Lemma `lem:global-labeling`: when the primed probe
values are distinct and the two monic products have the same roots, the matching
permutation is forced uniquely.
-/

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.KHead

/-- **Pointwise probe matching** (pointwise part of tex `lem:global-labeling`).

If two ordered `k`-tuples of real probe values have the same monic product and the primed
values are pairwise distinct, then there is a unique target-to-source permutation matching
each primed value to an unprimed value. -/
theorem pointwise_unique_matching {k : ℕ}
    (q q' : Fin k → ℝ)
    (hq' : Function.Injective q')
    (hprod : ∀ t : ℝ, ∏ c : Fin k, (t - q c) = ∏ h : Fin k, (t - q' h)) :
    ∃! σ : Equiv.Perm (Fin k), ∀ h, q (σ h) = q' h := by
  classical
  have hExists : ∀ h : Fin k, ∃ c : Fin k, q c = q' h := by
    intro h
    have hroot := hprod (q' h)
    have hrhs : (∏ g : Fin k, (q' h - q' g)) = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ h) (by simp)
    have hleft : (∏ c : Fin k, (q' h - q c)) = 0 := by
      rw [hroot, hrhs]
    obtain ⟨c, _hc_mem, hc⟩ := (Finset.prod_eq_zero_iff.mp hleft)
    exact ⟨c, (sub_eq_zero.mp hc).symm⟩
  let σfun : Fin k → Fin k := fun h => Classical.choose (hExists h)
  have hσfun : ∀ h : Fin k, q (σfun h) = q' h := fun h =>
    Classical.choose_spec (hExists h)
  have hσinj : Function.Injective σfun := by
    intro h g hhg
    apply hq'
    calc
      q' h = q (σfun h) := (hσfun h).symm
      _ = q (σfun g) := by rw [hhg]
      _ = q' g := hσfun g
  have hσbij : Function.Bijective σfun :=
    hσinj.bijective_of_finite
  let σ : Equiv.Perm (Fin k) := Equiv.ofBijective σfun hσbij
  refine ⟨σ, ?_, ?_⟩
  · intro h
    change q (σfun h) = q' h
    exact hσfun h
  · intro τ hτ
    apply Equiv.ext
    intro h
    obtain ⟨g, hg⟩ := hσbij.2 (τ h)
    have hg_eq : h = g := by
      apply hq'
      calc
        q' h = q (τ h) := (hτ h).symm
        _ = q (σfun g) := by rw [← hg]
        _ = q' g := hσfun g
    subst g
    change τ h = σfun h
    exact hg.symm

/-- The canonical pointwise permutation selected by `pointwise_unique_matching`. -/
noncomputable def pointwiseProductMatching {X : Type*} {k : ℕ}
    (q q' : X → Fin k → ℝ)
    (hq' : ∀ x, Function.Injective (q' x))
    (hprod : ∀ x, ∀ t : ℝ,
      ∏ c : Fin k, (t - q x c) = ∏ h : Fin k, (t - q' x h)) :
    X → Equiv.Perm (Fin k) :=
  fun x =>
    Classical.choose
      (pointwise_unique_matching (q x) (q' x) (hq' x) (hprod x)).exists

theorem pointwiseProductMatching_spec {X : Type*} {k : ℕ}
    (q q' : X → Fin k → ℝ)
    (hq' : ∀ x, Function.Injective (q' x))
    (hprod : ∀ x, ∀ t : ℝ,
      ∏ c : Fin k, (t - q x c) = ∏ h : Fin k, (t - q' x h))
    (x : X) :
    ∀ h, q x (pointwiseProductMatching q q' hq' hprod x h) = q' x h := by
  exact
    Classical.choose_spec
      (pointwise_unique_matching (q x) (q' x) (hq' x) (hprod x)).exists

theorem pointwiseProductMatching_unique {X : Type*} {k : ℕ}
    (q q' : X → Fin k → ℝ)
    (hq' : ∀ x, Function.Injective (q' x))
    (hprod : ∀ x, ∀ t : ℝ,
      ∏ c : Fin k, (t - q x c) = ∏ h : Fin k, (t - q' x h))
    {x : X} {σ : Equiv.Perm (Fin k)}
    (hσ : ∀ h, q x (σ h) = q' x h) :
    σ = pointwiseProductMatching q q' hq' hprod x := by
  exact
    (pointwise_unique_matching (q x) (q' x) (hq' x) (hprod x)).unique
      hσ (pointwiseProductMatching_spec q q' hq' hprod x)

/-- Local constancy of the pointwise matching permutation.

This is the local-constancy step of TeX Lemma `lem:global-labeling`, stated for any
continuous families of real probe values. -/
theorem pointwiseProductMatching_isLocallyConstant {X : Type*} [TopologicalSpace X]
    {k : ℕ}
    (q q' : X → Fin k → ℝ)
    (hq' : ∀ x, Function.Injective (q' x))
    (hprod : ∀ x, ∀ t : ℝ,
      ∏ c : Fin k, (t - q x c) = ∏ h : Fin k, (t - q' x h))
    (hq : ∀ c, Continuous fun x => q x c)
    (hq'_cont : ∀ h, Continuous fun x => q' x h) :
    IsLocallyConstant (pointwiseProductMatching q q' hq' hprod) := by
  classical
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x₀
  let σ₀ := pointwiseProductMatching q q' hq' hprod x₀
  have hσ₀ : ∀ h, q x₀ (σ₀ h) = q' x₀ h := by
    intro h
    exact pointwiseProductMatching_spec q q' hq' hprod x₀ h
  have hbad : ∀ σ : Equiv.Perm (Fin k), σ ≠ σ₀ →
      ∀ᶠ x in 𝓝 x₀, ¬ ∀ h, q x (σ h) = q' x h := by
    intro σ hσ
    have hdiff : ∃ h, σ h ≠ σ₀ h := by
      by_contra hnone
      apply hσ
      apply Equiv.ext
      intro h
      exact Classical.not_not.mp ((not_exists.mp hnone) h)
    obtain ⟨h, hh⟩ := hdiff
    let g : Fin k := σ₀.symm (σ h)
    have hσ₀g : σ₀ g = σ h := by
      simp [g]
    have hg_ne : g ≠ h := by
      intro hg
      exact hh (by simpa [hg] using hσ₀g.symm)
    have hne_val : q x₀ (σ h) - q' x₀ h ≠ 0 := by
      intro hzero
      have hmatch : q x₀ (σ h) = q' x₀ h := sub_eq_zero.mp hzero
      have htarget_g : q' x₀ g = q' x₀ h := by
        calc
          q' x₀ g = q x₀ (σ₀ g) := (hσ₀ g).symm
          _ = q x₀ (σ h) := by rw [hσ₀g]
          _ = q' x₀ h := hmatch
      exact hg_ne (hq' x₀ htarget_g)
    have hcont :
        ContinuousAt (fun x => q x (σ h) - q' x h) x₀ :=
      (hq (σ h)).continuousAt.sub (hq'_cont h).continuousAt
    exact (hcont.eventually_ne hne_val).mono fun x hx hmatch =>
      hx (sub_eq_zero.mpr (hmatch h))
  have hall : ∀ᶠ x in 𝓝 x₀,
      ∀ σ : Equiv.Perm (Fin k), σ ≠ σ₀ → ¬ ∀ h, q x (σ h) = q' x h := by
    rw [Filter.eventually_all]
    intro σ
    by_cases hσ : σ = σ₀
    · exact Eventually.of_forall fun _ hne => (hne hσ).elim
    · exact (hbad σ hσ).mono fun _ hx _ => hx
  filter_upwards [hall] with x hx
  by_contra hne
  exact hx (pointwiseProductMatching q q' hq' hprod x) hne
    (pointwiseProductMatching_spec q q' hq' hprod x)

/-- The canonical pointwise matching on a subset `U`, using the subspace topology when
local constancy is invoked. -/
noncomputable def pointwiseProductMatchingOn {X : Type*} {k : ℕ}
    (q q' : X → Fin k → ℝ)
    (U : Set X)
    (hq' : ∀ x, x ∈ U → Function.Injective (q' x))
    (hprod : ∀ x, x ∈ U → ∀ t : ℝ,
      ∏ c : Fin k, (t - q x c) = ∏ h : Fin k, (t - q' x h)) :
    U → Equiv.Perm (Fin k) :=
  pointwiseProductMatching
    (fun x : U => q x.1)
    (fun x : U => q' x.1)
    (fun x => hq' x.1 x.2)
    (fun x => hprod x.1 x.2)

theorem pointwiseProductMatchingOn_spec {X : Type*} {k : ℕ}
    (q q' : X → Fin k → ℝ)
    (U : Set X)
    (hq' : ∀ x, x ∈ U → Function.Injective (q' x))
    (hprod : ∀ x, x ∈ U → ∀ t : ℝ,
      ∏ c : Fin k, (t - q x c) = ∏ h : Fin k, (t - q' x h))
    (x : U) :
    ∀ h, q x.1 (pointwiseProductMatchingOn q q' U hq' hprod x h) = q' x.1 h := by
  exact
    pointwiseProductMatching_spec
      (fun x : U => q x.1)
      (fun x : U => q' x.1)
      (fun x => hq' x.1 x.2)
      (fun x => hprod x.1 x.2)
      x

theorem pointwiseProductMatchingOn_unique {X : Type*} {k : ℕ}
    (q q' : X → Fin k → ℝ)
    (U : Set X)
    (hq' : ∀ x, x ∈ U → Function.Injective (q' x))
    (hprod : ∀ x, x ∈ U → ∀ t : ℝ,
      ∏ c : Fin k, (t - q x c) = ∏ h : Fin k, (t - q' x h))
    {x : U} {σ : Equiv.Perm (Fin k)}
    (hσ : ∀ h, q x.1 (σ h) = q' x.1 h) :
    σ = pointwiseProductMatchingOn q q' U hq' hprod x := by
  exact
    pointwiseProductMatching_unique
      (fun x : U => q x.1)
      (fun x : U => q' x.1)
      (fun x => hq' x.1 x.2)
      (fun x => hprod x.1 x.2)
      hσ

theorem pointwiseProductMatchingOn_isLocallyConstant {X : Type*} [TopologicalSpace X]
    {k : ℕ}
    (q q' : X → Fin k → ℝ)
    (U : Set X)
    (hq' : ∀ x, x ∈ U → Function.Injective (q' x))
    (hprod : ∀ x, x ∈ U → ∀ t : ℝ,
      ∏ c : Fin k, (t - q x c) = ∏ h : Fin k, (t - q' x h))
    (hq : ∀ c, ContinuousOn (fun x => q x c) U)
    (hq'_cont : ∀ h, ContinuousOn (fun x => q' x h) U) :
    IsLocallyConstant (pointwiseProductMatchingOn q q' U hq' hprod) := by
  exact
    pointwiseProductMatching_isLocallyConstant
      (fun x : U => q x.1)
      (fun x : U => q' x.1)
      (fun x => hq' x.1 x.2)
      (fun x => hprod x.1 x.2)
      (fun c => (hq c).restrict)
      (fun h => (hq'_cont h).restrict)

/-- A locally constant pointwise matching is constant on preconnected subsets.  This is
the connected-component step of TeX Lemma `lem:global-labeling`. -/
theorem pointwiseProductMatchingOn_eq_on_preconnected {X : Type*} [TopologicalSpace X]
    {k : ℕ}
    (q q' : X → Fin k → ℝ)
    (U : Set X)
    (hq' : ∀ x, x ∈ U → Function.Injective (q' x))
    (hprod : ∀ x, x ∈ U → ∀ t : ℝ,
      ∏ c : Fin k, (t - q x c) = ∏ h : Fin k, (t - q' x h))
    (hq : ∀ c, ContinuousOn (fun x => q x c) U)
    (hq'_cont : ∀ h, ContinuousOn (fun x => q' x h) U)
    {C : Set U} (hC : IsPreconnected C) {x y : U}
    (hx : x ∈ C) (hy : y ∈ C) :
    pointwiseProductMatchingOn q q' U hq' hprod x =
      pointwiseProductMatchingOn q q' U hq' hprod y := by
  exact
    (pointwiseProductMatchingOn_isLocallyConstant q q' U hq' hprod hq hq'_cont)
      |>.apply_eq_of_isPreconnected hC hx hy

theorem continuous_attention_probe_value {d k : ℕ}
    (B : Fin k → Matrix (Fin d) (Fin d) ℝ) (c : Fin k) :
    Continuous fun x : (Fin d → ℝ) × (Fin d → ℝ) =>
      x.1 ⬝ᵥ (B c).mulVec x.2 := by
  fun_prop

/-- The pointwise matching map for bilinear attention probes. -/
noncomputable def attentionGlobalLabelingMatching {d k : ℕ}
    (B B' : Fin k → Matrix (Fin d) (Fin d) ℝ)
    (U : Set ((Fin d → ℝ) × (Fin d → ℝ)))
    (hsep : ∀ x, x ∈ U →
      Function.Injective (fun h : Fin k => x.1 ⬝ᵥ (B' h).mulVec x.2))
    (hprodU : ∀ x, x ∈ U → ∀ t : ℝ,
      ∏ c : Fin k, (t - x.1 ⬝ᵥ (B c).mulVec x.2) =
        ∏ h : Fin k, (t - x.1 ⬝ᵥ (B' h).mulVec x.2)) :
    U → Equiv.Perm (Fin k) :=
  pointwiseProductMatchingOn
    (fun x c => x.1 ⬝ᵥ (B c).mulVec x.2)
    (fun x h => x.1 ⬝ᵥ (B' h).mulVec x.2)
    U hsep hprodU

theorem attentionGlobalLabelingMatching_isLocallyConstant {d k : ℕ}
    (B B' : Fin k → Matrix (Fin d) (Fin d) ℝ)
    (U : Set ((Fin d → ℝ) × (Fin d → ℝ)))
    (hsep : ∀ x, x ∈ U →
      Function.Injective (fun h : Fin k => x.1 ⬝ᵥ (B' h).mulVec x.2))
    (hprodU : ∀ x, x ∈ U → ∀ t : ℝ,
      ∏ c : Fin k, (t - x.1 ⬝ᵥ (B c).mulVec x.2) =
        ∏ h : Fin k, (t - x.1 ⬝ᵥ (B' h).mulVec x.2)) :
    IsLocallyConstant (attentionGlobalLabelingMatching B B' U hsep hprodU) := by
  exact
    pointwiseProductMatchingOn_isLocallyConstant
      (fun x c => x.1 ⬝ᵥ (B c).mulVec x.2)
      (fun x h => x.1 ⬝ᵥ (B' h).mulVec x.2)
      U hsep hprodU
      (fun c => (continuous_attention_probe_value B c).continuousOn)
      (fun h => (continuous_attention_probe_value B' h).continuousOn)

theorem pointwise_matching_eq_matrix_permutation {d k : ℕ}
    (B B' : Fin k → Matrix (Fin d) (Fin d) ℝ)
    (x : (Fin d → ℝ) × (Fin d → ℝ))
    {ρ σ : Equiv.Perm (Fin k)}
    (hρ : ∀ h, B (ρ h) = B' h)
    (hsep : Function.Injective (fun h : Fin k => x.1 ⬝ᵥ (B' h).mulVec x.2))
    (hprod : ∀ t : ℝ,
      ∏ c : Fin k, (t - x.1 ⬝ᵥ (B c).mulVec x.2) =
        ∏ h : Fin k, (t - x.1 ⬝ᵥ (B' h).mulVec x.2))
    (hσ : ∀ h, x.1 ⬝ᵥ (B (σ h)).mulVec x.2 =
      x.1 ⬝ᵥ (B' h).mulVec x.2) :
    σ = ρ := by
  let q : Fin k → ℝ := fun c => x.1 ⬝ᵥ (B c).mulVec x.2
  let q' : Fin k → ℝ := fun h => x.1 ⬝ᵥ (B' h).mulVec x.2
  have hρmatch : ∀ h, q (ρ h) = q' h := by
    intro h
    simp [q, q', hρ h]
  exact (pointwise_unique_matching q q' hsep hprod).unique hσ hρmatch

/-- Combined Lean API for TeX Lemma `lem:global-labeling`.

It packages the proved local-constancy and connected-component conclusions for the
pointwise matching map together with the Zariski-dense algebraic globalization to a
single matrix-level permutation. -/
theorem global_labeling {d k : ℕ}
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
      ∃! ρ : Equiv.Perm (Fin k),
        (∀ h, B (ρ h) = B' h) ∧
          ∀ x : U, attentionGlobalLabelingMatching B B' U hsep hprodU x = ρ := by
  classical
  let σ := attentionGlobalLabelingMatching B B' U hsep hprodU
  have hloc : IsLocallyConstant σ :=
    attentionGlobalLabelingMatching_isLocallyConstant B B' U hsep hprodU
  have hcomponent :
      ∀ {C : Set U}, IsPreconnected C → ∀ {x y : U},
        x ∈ C → y ∈ C → σ x = σ y := by
    intro C hC x y hx hy
    exact hloc.apply_eq_of_isPreconnected hC hx hy
  have hglobal := global_labeling_algebraic B B' U hB' hU hprodU
  refine ⟨hloc, hcomponent, ?_⟩
  obtain ⟨ρ, hρ, hρuniq⟩ := hglobal
  refine ⟨ρ, ?_, ?_⟩
  · refine ⟨hρ, ?_⟩
    intro x
    symm
    apply pointwiseProductMatchingOn_unique
      (fun x c => x.1 ⬝ᵥ (B c).mulVec x.2)
      (fun x h => x.1 ⬝ᵥ (B' h).mulVec x.2)
      U hsep hprodU
    intro h
    simp [hρ h]
  · intro τ hτ
    exact hρuniq τ hτ.1

end TransformerIdentifiability.NLayer.KHead
