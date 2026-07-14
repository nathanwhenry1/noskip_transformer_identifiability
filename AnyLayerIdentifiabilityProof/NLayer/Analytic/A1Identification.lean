import AnyLayerIdentifiabilityProof.NLayer.Analytic.Stratification
import AnyLayerIdentifiabilityProof.NLayer.Analytic.AlgebraicQuadric

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer

/-!
# Step 1: identification of the first attention matrix

Target contents:
* standing hypothesis for the inductive step
* pole hierarchy and tier sets
* transfer from the generic side to the unknown side
* proof that `A_1 = A'_1`
* depth certificate `V_1 != 0`

Corresponds to `n_layer_proof.tex`, Section 5.
-/

/-- Claim D shape in `n_layer_proof.tex`, Proposition `A1`.

If every point of the last generic tier is an isolated blowing-up point for the generic
observable, pole transfer puts the whole tier into the unknown exceptional set.
-/
theorem transferred_tier_subset {E_F E_G T : Set ℂ} {F G : ℂ -> ℂ} {z0 : ℂ}
    (hEFclosed : IsClosed E_F)
    (hEFcount : E_F.Countable)
    (hEGcount : E_G.Countable)
    (hF : AnalyticOnNhd ℂ F E_Fᶜ)
    (hGanalytic : AnalyticOnNhd ℂ G E_Gᶜ)
    (hz0 : z0 ∈ (E_F ∪ E_G)ᶜ)
    (hfg : ∃ᶠ z in nhdsWithin z0 ({z0}ᶜ : Set ℂ), F z = G z)
    (hFcont : ∀ τ, τ ∉ E_F -> ContinuousAt F τ)
    (hTisol : ∀ τ, τ ∈ T -> IsPuncturedIsolated E_G τ)
    (hTblow : ∀ τ, τ ∈ T -> BlowsUpAt G τ) :
    T ⊆ E_F := by
  intro τ hτ
  exact pole_transfer_of_frequentlyEq hEFclosed hEFcount hEGcount hF hGanalytic
    hz0 hfg (hFcont τ) (hTisol τ hτ) (hTblow τ hτ)

/-- Iterating accumulation after one initial accumulation.

This is a small indexing helper for Step 4 of `prop:A1`, where the proof rewrites
`acc^{j-1}(acc T_{j+1})` as `acc^j(T_{j+1})`.
-/
theorem accIter_acc (k : Nat) (A : Set ℂ) :
    accIter k (acc A) = accIter (k + 1) A := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      simp [accIter, ih]

/-- Step 4 chain induction in `n_layer_proof.tex`, Proposition `A1`.

If every tier accumulates on the next one, then the first tier lies in the iterated
accumulation of the `k`-th tier.
-/
theorem tier_chain_subset_accIter {T : Nat -> Set ℂ} :
    ∀ k : Nat,
      (∀ j, j < k -> T j ⊆ acc (T (j + 1))) ->
      T 0 ⊆ accIter k (T k) := by
  intro k
  induction k with
  | zero =>
      intro _ z hz
      simpa [accIter] using hz
  | succ k ih =>
      intro hchain
      have hprev : T 0 ⊆ accIter k (T k) := by
        exact ih (fun j hj => hchain j (Nat.lt_trans hj (Nat.lt_succ_self k)))
      have hstep : accIter k (T k) ⊆ accIter (k + 1) (T (k + 1)) := by
        have hmono := accIter_mono (hchain k (Nat.lt_succ_self k)) k
        simpa [accIter_acc] using hmono
      exact fun z hz => hstep (hprev hz)

/-- Abstract descent conclusion from Step 4 of `prop:A1`.

Once the last generic tier has transferred into the unknown singular union, the
`strataacc` descent forces the first generic tier into the first unknown stratum.
Here `partialUnion S 1` is the zero-indexed version of `S^1`.
-/
theorem tier_descent_to_first_stratum {S T : Nat -> Set ℂ} {m : Nat}
    (hm : 0 < m)
    (hS : StrataSystem S m)
    (hChain : ∀ j, j + 1 < m -> T j ⊆ acc (T (j + 1)))
    (hLast : T (m - 1) ⊆ partialUnion S m) :
    T 0 ⊆ partialUnion S 1 := by
  have hTierAcc : T 0 ⊆ accIter (m - 1) (T (m - 1)) := by
    refine tier_chain_subset_accIter (T := T) (m - 1) ?_
    intro j hj
    exact hChain j (by omega)
  have hIntoUnknown :
      accIter (m - 1) (T (m - 1)) ⊆ accIter (m - 1) (partialUnion S m) :=
    accIter_mono hLast (m - 1)
  have hDescent :
      accIter (m - 1) (partialUnion S m) ⊆ partialUnion S (m - (m - 1)) :=
    accIter_partialUnion_subset hS (m - 1) (by omega)
  intro z hz
  have hzFirst : z ∈ partialUnion S (m - (m - 1)) :=
    hDescent (hIntoUnknown (hTierAcc hz))
  have hm_sub : m - (m - 1) = 1 := by omega
  simpa [hm_sub] using hzFirst

/-- Set-level form of the Step 4 descent: after the transferred last tier and the
`strataacc` descent, the first generic tier lies in the first unknown stratum. -/
theorem tier_descent_to_first_set {S T : Nat -> Set ℂ} {m : Nat}
    (hm : 0 < m)
    (hS : StrataSystem S m)
    (hChain : ∀ j, j + 1 < m -> T j ⊆ acc (T (j + 1)))
    (hLast : T (m - 1) ⊆ partialUnion S m) :
    T 0 ⊆ S 0 := by
  simpa using tier_descent_to_first_stratum (S := S) (T := T) hm hS hChain hLast

/-- Step 4 of Proposition `A1`, in the first-stratum set form.

The hypotheses match the end of the natural-language proof:
* Claim B gives `hChain`;
* Claim D gives `hLast`;
* Proposition `strat(d)` identifies the first primed tier with `firstPoleSet b lam'`;
* the unprimed first stratum lies in `firstPoleSet b lam`.

Under those assumptions the real-part comparison of the affine sigmoid poles gives
`lam = lam'`, i.e. `wᵀ A₁ v = wᵀ A₁' v` for the fixed probe. -/
theorem first_slope_eq_of_tier_descent {S T : Nat -> Set ℂ} {m : Nat}
    {b lam lam' : ℝ}
    (hb : b ≠ 0)
    (hlam : lam ≠ 0)
    (hlam' : lam' ≠ 0)
    (hm : 0 < m)
    (hS : StrataSystem S m)
    (hChain : ∀ j, j + 1 < m -> T j ⊆ acc (T (j + 1)))
    (hLast : T (m - 1) ⊆ partialUnion S m)
    (hFirstPrimed : firstPoleSet b lam' ⊆ T 0)
    (hFirstUnprimed : S 0 ⊆ firstPoleSet b lam) :
    lam = lam' := by
  have hT0S0 : T 0 ⊆ S 0 :=
    tier_descent_to_first_set (S := S) (T := T) hm hS hChain hLast
  exact slope_eq_of_firstPoleSet_subset hb hlam hlam'
    (fun z hz => hFirstUnprimed (hT0S0 (hFirstPrimed hz)))

/-- Packaged one-probe Step 1 descent obligations.

For a fixed probe, `lam` and `lam'` are the two first-layer bilinear slopes.  This
structure names exactly the hypotheses consumed by `first_slope_eq_of_tier_descent`,
without committing to any downstream concrete construction of the strata or tiers. -/
structure TierDescentSlopeData {m : Nat} (S T : Nat -> Set ℂ)
    (b lam lam' : ℝ) : Prop where
  base_ne_zero : b ≠ 0
  slope_ne_zero : lam ≠ 0
  primed_slope_ne_zero : lam' ≠ 0
  depth_pos : 0 < m
  strata : StrataSystem S m
  chain : ∀ j, j + 1 < m -> T j ⊆ acc (T (j + 1))
  last_subset : T (m - 1) ⊆ partialUnion S m
  first_primed_subset : firstPoleSet b lam' ⊆ T 0
  first_unprimed_subset : S 0 ⊆ firstPoleSet b lam

namespace TierDescentSlopeData

variable {S T : Nat -> Set ℂ} {m : Nat} {b lam lam' : ℝ}

/-- Compile the packaged one-probe descent obligations to equality of the two slopes. -/
theorem slope_eq (D : TierDescentSlopeData (m := m) S T b lam lam') :
    lam = lam' :=
  first_slope_eq_of_tier_descent (S := S) (T := T)
    D.base_ne_zero D.slope_ne_zero D.primed_slope_ne_zero D.depth_pos
    D.strata D.chain D.last_subset D.first_primed_subset D.first_unprimed_subset

end TierDescentSlopeData

/-- Step 5 of Proposition `A1`, after the probe argument has supplied the bilinear
identity for every probe.

This theorem intentionally isolates the remaining algebraic-continuation obligation from
the natural-language proof: in the TeX proof the identity is first obtained on the generic
open set `O_star` and then extended to all probes by the Zariski lemma.  Once that global
bilinear identity is available, the matrix equality is immediate. -/
theorem A1_eq_of_all_probe_slope_eq {d : Nat}
    {A A' : Matrix (Fin d) (Fin d) ℝ}
    (hSlope : ∀ w v : Fin d -> ℝ, matrixBilin A w v = matrixBilin A' w v) :
    A = A' :=
  matrix_eq_of_forall_bilin_eq hSlope

/-- Probe-level slope equality package.

The `extend` field is the exact algebraic-continuation obligation: equality proved on
the probe predicate `P` must extend to all probes. -/
structure ProbeSlopeEqualityData {d : Nat}
    (A A' : Matrix (Fin d) (Fin d) ℝ)
    (P : (Fin d -> ℝ) -> (Fin d -> ℝ) -> Prop) : Prop where
  slope_eq_on :
    ∀ w v : Fin d -> ℝ, P w v -> matrixBilin A w v = matrixBilin A' w v
  extend :
    (∀ w v : Fin d -> ℝ, P w v -> matrixBilin A w v = matrixBilin A' w v) ->
      ∀ w v : Fin d -> ℝ, matrixBilin A w v = matrixBilin A' w v

namespace ProbeSlopeEqualityData

variable {d : Nat} {A A' : Matrix (Fin d) (Fin d) ℝ}
variable {P : (Fin d -> ℝ) -> (Fin d -> ℝ) -> Prop}

/-- Extend packaged probe-set equality to all probes. -/
theorem all_probe_slope_eq (D : ProbeSlopeEqualityData A A' P) :
    ∀ w v : Fin d -> ℝ, matrixBilin A w v = matrixBilin A' w v :=
  D.extend D.slope_eq_on

/-- Compile packaged probe-set equality to equality of the two first matrices. -/
theorem matrix_eq (D : ProbeSlopeEqualityData A A' P) :
    A = A' :=
  A1_eq_of_all_probe_slope_eq D.all_probe_slope_eq

end ProbeSlopeEqualityData

/-- Abstract compiled endpoint of Step 1.

For each probe, assume the Step 1-4 tier construction has produced a stratification `S`,
tier sets `T`, and the first-stratum identifications needed by
`first_slope_eq_of_tier_descent`.  Then the first attention matrices are equal.

The theorem is abstract because the current split has not yet formalized the concrete
probe polynomials `φ'_m`, the nested largeness regions `N_k`, or the resulting concrete
tier sets.  Those pieces will instantiate `S`, `T`, and the hypotheses below. -/
theorem A1_eq_of_probe_tier_descent {d m : Nat} {b : ℝ}
    {A A' : Matrix (Fin d) (Fin d) ℝ}
    (P : (Fin d -> ℝ) -> (Fin d -> ℝ) -> Prop)
    (S T : (Fin d -> ℝ) -> (Fin d -> ℝ) -> Nat -> Set ℂ)
    (hb : b ≠ 0)
    (hm : 0 < m)
    (hNonzero :
      ∀ w v : Fin d -> ℝ, P w v ->
        matrixBilin A w v ≠ 0 ∧ matrixBilin A' w v ≠ 0)
    (hStrata : ∀ w v : Fin d -> ℝ, P w v -> StrataSystem (S w v) m)
    (hChain :
      ∀ w v : Fin d -> ℝ, P w v -> ∀ j, j + 1 < m ->
        T w v j ⊆ acc (T w v (j + 1)))
    (hLast :
      ∀ w v : Fin d -> ℝ, P w v ->
        T w v (m - 1) ⊆ partialUnion (S w v) m)
    (hFirstPrimed :
      ∀ w v : Fin d -> ℝ, P w v ->
        firstPoleSet b (matrixBilin A' w v) ⊆ T w v 0)
    (hFirstUnprimed :
      ∀ w v : Fin d -> ℝ, P w v ->
        S w v 0 ⊆ firstPoleSet b (matrixBilin A w v))
    (hExtend :
      (∀ w v : Fin d -> ℝ, P w v -> matrixBilin A w v = matrixBilin A' w v) ->
        ∀ w v : Fin d -> ℝ, matrixBilin A w v = matrixBilin A' w v) :
    A = A' := by
  apply A1_eq_of_all_probe_slope_eq
  apply hExtend
  intro w v hP
  exact first_slope_eq_of_tier_descent (S := S w v) (T := T w v)
    (b := b) (lam := matrixBilin A w v) (lam' := matrixBilin A' w v)
    hb (hNonzero w v hP).1 (hNonzero w v hP).2 hm (hStrata w v hP)
    (hChain w v hP) (hLast w v hP) (hFirstPrimed w v hP) (hFirstUnprimed w v hP)

/-- Packaged all-probe Step 1 descent obligations.

This is a constructor-friendly version of `A1_eq_of_probe_tier_descent`: downstream
files can assemble the fields once, then use `.probe_slope_eq`, `.all_probe_slope_eq`,
or `.matrix_eq` depending on how much of the final conclusion they need. -/
structure ProbeTierDescentData {d m : Nat} (b : ℝ)
    (A A' : Matrix (Fin d) (Fin d) ℝ)
    (P : (Fin d -> ℝ) -> (Fin d -> ℝ) -> Prop)
    (S T : (Fin d -> ℝ) -> (Fin d -> ℝ) -> Nat -> Set ℂ) : Prop where
  base_ne_zero : b ≠ 0
  depth_pos : 0 < m
  nonzero :
    ∀ w v : Fin d -> ℝ, P w v ->
      matrixBilin A w v ≠ 0 ∧ matrixBilin A' w v ≠ 0
  strata : ∀ w v : Fin d -> ℝ, P w v -> StrataSystem (S w v) m
  chain :
    ∀ w v : Fin d -> ℝ, P w v -> ∀ j, j + 1 < m ->
      T w v j ⊆ acc (T w v (j + 1))
  last_subset :
    ∀ w v : Fin d -> ℝ, P w v ->
      T w v (m - 1) ⊆ partialUnion (S w v) m
  first_primed_subset :
    ∀ w v : Fin d -> ℝ, P w v ->
      firstPoleSet b (matrixBilin A' w v) ⊆ T w v 0
  first_unprimed_subset :
    ∀ w v : Fin d -> ℝ, P w v ->
      S w v 0 ⊆ firstPoleSet b (matrixBilin A w v)
  extend :
    (∀ w v : Fin d -> ℝ, P w v -> matrixBilin A w v = matrixBilin A' w v) ->
      ∀ w v : Fin d -> ℝ, matrixBilin A w v = matrixBilin A' w v

namespace ProbeTierDescentData

variable {d m : Nat} {b : ℝ} {A A' : Matrix (Fin d) (Fin d) ℝ}
variable {P : (Fin d -> ℝ) -> (Fin d -> ℝ) -> Prop}
variable {S T : (Fin d -> ℝ) -> (Fin d -> ℝ) -> Nat -> Set ℂ}

/-- Extract the one-probe descent package at a probe satisfying `P`. -/
def toTierDescentSlopeData (D : ProbeTierDescentData (m := m) b A A' P S T)
    {w v : Fin d -> ℝ} (hP : P w v) :
    TierDescentSlopeData (m := m) (S w v) (T w v) b
      (matrixBilin A w v) (matrixBilin A' w v) where
  base_ne_zero := D.base_ne_zero
  slope_ne_zero := (D.nonzero w v hP).1
  primed_slope_ne_zero := (D.nonzero w v hP).2
  depth_pos := D.depth_pos
  strata := D.strata w v hP
  chain := D.chain w v hP
  last_subset := D.last_subset w v hP
  first_primed_subset := D.first_primed_subset w v hP
  first_unprimed_subset := D.first_unprimed_subset w v hP

/-- Probe-level slope equality from packaged descent obligations. -/
theorem probe_slope_eq (D : ProbeTierDescentData (m := m) b A A' P S T)
    {w v : Fin d -> ℝ} (hP : P w v) :
    matrixBilin A w v = matrixBilin A' w v :=
  (D.toTierDescentSlopeData hP).slope_eq

/-- Extend packaged descent equality to all probes. -/
theorem all_probe_slope_eq (D : ProbeTierDescentData (m := m) b A A' P S T) :
    ∀ w v : Fin d -> ℝ, matrixBilin A w v = matrixBilin A' w v :=
  D.extend fun w v hP => D.probe_slope_eq (w := w) (v := v) hP

/-- Compile packaged all-probe descent obligations to equality of the two matrices. -/
theorem matrix_eq (D : ProbeTierDescentData (m := m) b A A' P S T) :
    A = A' :=
  A1_eq_of_all_probe_slope_eq D.all_probe_slope_eq

end ProbeTierDescentData

end TransformerIdentifiability.NLayer
