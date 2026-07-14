import AnyLayerIdentifiabilityProof.NLayer.Analytic.AnalyticToolkit

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer

/-!
# Singular stratification

Target contents:
* constant-probe observable stratification
* stratum blow-up lemma
* last-layer formula for the holomorphic extension

Corresponds to:
* `n_layer_proof.tex`, Section 4.3
* the Step 1 helper lemmas `stratpole` and `lastlayer`
-/

/-- Abstract interface for the sigmoid-gate singular stratification constructed in
`n_layer_proof.tex`, Proposition `strat`.

The full transformer-specific construction still has to instantiate this structure from
the slope polynomials.  Once instantiated, the two lemmas below give the hard analytic
content of Auxiliary Lemma `stratpole`.
-/
structure SigmoidStratification
    (S : Nat -> Set ℂ) (H s : Nat -> ℂ -> ℂ) (m : Nat) : Prop where
  strata : StrataSystem S m
  regular : ∀ j, j < m -> S j ⊆ (partialUnion S j)ᶜ
  gate_eq : ∀ j, j < m -> s j = fun τ => csig (H j τ)
  pole_value : ∀ j, j < m -> ∀ τ, τ ∈ S j -> H j τ ∈ oddPiI
  H_tendsto_at_stratum :
    ∀ j, j < m -> ∀ τ, τ ∈ S j ->
      Filter.Tendsto (H j) (nhdsWithin τ ({τ}ᶜ : Set ℂ)) (nhds (H j τ))
  denom_eventually_ne :
    ∀ j, j < m -> ∀ τ, τ ∈ S j ->
      ∀ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ), 1 + Complex.exp (-(H j z)) ≠ 0

namespace SigmoidStratification

/-- Accessor for closedness of the partial union of strata. -/
theorem closed_partialUnion {S : Nat -> Set ℂ} {H s : Nat -> ℂ -> ℂ} {m n : Nat}
    (h : SigmoidStratification S H s m) (hn : n ≤ m) :
    IsClosed (partialUnion S n) :=
  h.strata.closed_partial n hn

/-- Accessor for the no-accumulation condition on the regular domain before a stratum. -/
theorem noAccumIn {S : Nat -> Set ℂ} {H s : Nat -> ℂ -> ℂ} {m j : Nat}
    (h : SigmoidStratification S H s m) (hj : j < m) :
    NoAccumIn (S j) (partialUnion S j)ᶜ :=
  h.strata.noAccumIn j hj

/-- Formula for a gate as the sigmoid of its preactivation. -/
theorem gate_formula {S : Nat -> Set ℂ} {H s : Nat -> ℂ -> ℂ} {m j : Nat}
    (h : SigmoidStratification S H s m) (hj : j < m) :
    s j = fun τ => csig (H j τ) :=
  h.gate_eq j hj

/-- Pole value accessor for points of a stratum. -/
theorem gateArgument_mem_oddPiI {S : Nat -> Set ℂ} {H s : Nat -> ℂ -> ℂ}
    {m j : Nat} (h : SigmoidStratification S H s m) (hj : j < m)
    {τ : ℂ} (hτ : τ ∈ S j) :
    H j τ ∈ oddPiI :=
  h.pole_value j hj τ hτ

/-- Restrict the stratification system to an initial segment. -/
theorem strata_restrict {S : Nat -> Set ℂ} {H s : Nat -> ℂ -> ℂ} {m n : Nat}
    (h : SigmoidStratification S H s m) (hn : n ≤ m) :
    StrataSystem S n :=
  h.strata.restrict hn

/-- One-step accumulation descent for the partial-union tower of a sigmoid
stratification. -/
theorem acc_partialUnion_succ_subset {S : Nat -> Set ℂ} {H s : Nat -> ℂ -> ℂ}
    {m n : Nat} (h : SigmoidStratification S H s m) (hn : n + 1 ≤ m) :
    acc (partialUnion S (n + 1)) ⊆ partialUnion S n :=
  TransformerIdentifiability.NLayer.acc_partialUnion_succ_subset (h.strata_restrict hn)

/-- Iterated accumulation descent for the partial-union tower of a sigmoid
stratification. -/
theorem accIter_partialUnion_subset {S : Nat -> Set ℂ} {H s : Nat -> ℂ -> ℂ}
    {m : Nat} (h : SigmoidStratification S H s m) :
    ∀ k : Nat, k ≤ m -> accIter k (partialUnion S m) ⊆ partialUnion S (m - k) :=
  TransformerIdentifiability.NLayer.accIter_partialUnion_subset h.strata

/-- After `m` accumulations, the full `m`-stratum partial union is empty. -/
theorem accIter_partialUnion_eq_empty {S : Nat -> Set ℂ} {H s : Nat -> ℂ -> ℂ}
    {m : Nat} (h : SigmoidStratification S H s m) :
    accIter m (partialUnion S m) = ∅ :=
  TransformerIdentifiability.NLayer.accIter_partialUnion_eq_empty h.strata

/-- `n_layer_proof.tex`, Auxiliary Lemma `stratpole`, item (i), in the abstract
stratification interface. -/
theorem punctured_isolated {S : Nat -> Set ℂ} {H s : Nat -> ℂ -> ℂ} {m j : Nat}
    (h : SigmoidStratification S H s m) (hj : j < m) {τ : ℂ} (hτ : τ ∈ S j) :
    IsPuncturedIsolated (partialUnion S (j + 1)) τ := by
  exact strata_punctured_isolated_partialUnion_succ
    (h.strata.restrict (Nat.succ_le_of_lt hj)) hτ (h.regular j hj hτ)

/-- `n_layer_proof.tex`, Auxiliary Lemma `stratpole`, item (ii), in the abstract
stratification interface. -/
theorem gate_blowsUpAt {S : Nat -> Set ℂ} {H s : Nat -> ℂ -> ℂ} {m j : Nat}
    (h : SigmoidStratification S H s m) (hj : j < m) {τ : ℂ} (hτ : τ ∈ S j) :
    BlowsUpAt (s j) τ := by
  rw [h.gate_formula hj]
  exact csig_blowsUpAt_of_tendsto_pole (h.gateArgument_mem_oddPiI hj hτ)
    (h.H_tendsto_at_stratum j hj τ hτ) (h.denom_eventually_ne j hj τ hτ)

/-- Filter form of punctured regularity after stratum `j`. -/
theorem punctured_regular_succ {S : Nat -> Set ℂ} {H s : Nat -> ℂ -> ℂ}
    {m j : Nat} (h : SigmoidStratification S H s m) (hj : j < m)
    {τ : ℂ} (hτ : τ ∈ S j) :
    ∀ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ), z ∈ (partialUnion S (j + 1))ᶜ := by
  simpa [IsPuncturedIsolated] using h.punctured_isolated hj hτ

/-- Packaged `stratpole` conclusion for a sigmoid stratification point. -/
structure StratPoleData {S : Nat -> Set ℂ} {H s : Nat -> ℂ -> ℂ}
    {m : Nat} (h : SigmoidStratification S H s m) (j : Nat) (τ : ℂ) :
    Prop where
  punctured_regular_succ :
    ∀ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ), z ∈ (partialUnion S (j + 1))ᶜ
  gate_blowsUpAt : BlowsUpAt (s j) τ

/-- Build the packaged `stratpole` conclusion from stratum membership. -/
theorem stratpole {S : Nat -> Set ℂ} {H s : Nat -> ℂ -> ℂ} {m j : Nat}
    (h : SigmoidStratification S H s m) (hj : j < m) {τ : ℂ} (hτ : τ ∈ S j) :
    StratPoleData h j τ where
  punctured_regular_succ := h.punctured_regular_succ hj hτ
  gate_blowsUpAt := h.gate_blowsUpAt hj hτ

end SigmoidStratification

end TransformerIdentifiability.NLayer
