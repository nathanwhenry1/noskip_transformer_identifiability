import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Probe
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Induction.Relabel
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Genericity.Recursive
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.DimensionThreshold

set_option autoImplicit false

open Matrix
open scoped Matrix.Norms.Frobenius

namespace TransformerIdentifiability.NLayer.NoSkip

abbrev NetworkInput (r d : Nat) := Matrix (Fin d) (Fin (seqLength r)) Real

structure NonemptyOpenInputSet {r d : Nat} (omega : Set (NetworkInput r d)) : Prop where
  isOpen : IsOpen omega
  nonempty : omega.Nonempty

def TransformerEqualOn {r m k d : Nat} (theta theta' : Params m k d)
    (omega : Set (NetworkInput r d)) : Prop :=
  ∀ X, X ∈ omega → transformer theta X = transformer theta' X

def TransformerEqualGlobally {r m k d : Nat} (theta theta' : Params m k d) : Prop :=
  ∀ X : NetworkInput r d, transformer theta X = transformer theta' X

def ProbeOutputEqual (r : Nat) {m k d : Nat} (theta theta' : Params m k d) : Prop :=
  ∀ w v : Vec d, ∀ tau : Real, 0 < tau →
    probeOutput r theta w v tau = probeOutput r theta' w v tau

theorem probeOutput_eq_of_transformerEqualGlobally {r m k d : Nat}
    (hr : 0 < r) {theta theta' : Params m k d}
    (hglobal : TransformerEqualGlobally (r := r) theta theta') :
    ProbeOutputEqual r theta theta' := by
  intro w v tau htau
  have htheta := probeOutput_eq_inv_sqrt_transformer_last hr theta w v tau htau
  have htheta' := probeOutput_eq_inv_sqrt_transformer_last hr theta' w v tau htau
  rw [← htheta, ← htheta', hglobal (probeMatrix r w v tau)]

structure OpenSetToGlobalConclusion (r : Nat) {m k d : Nat}
    (theta theta' : Params m k d) : Prop where
  global_equal : TransformerEqualGlobally (r := r) theta theta'
  probe_equal : ProbeOutputEqual r theta theta'

theorem transformerEqualGlobally_of_equalOn_nonempty_open_of_analytic {r m k d : Nat}
    {theta theta' : Params m k d} {omega : Set (NetworkInput r d)}
    (hanalytic : AnalyticOnNhd Real (fun X : NetworkInput r d => transformer theta X) Set.univ)
    (hanalytic' : AnalyticOnNhd Real (fun X : NetworkInput r d => transformer theta' X) Set.univ)
    (hopen : IsOpen omega) (hnonempty : omega.Nonempty)
    (heq : TransformerEqualOn (r := r) theta theta' omega) :
    TransformerEqualGlobally (r := r) theta theta' := by
  rcases hnonempty with ⟨X0, hX0⟩
  have heventually :
      (fun X : NetworkInput r d => transformer theta X) =ᶠ[nhds X0]
        (fun X : NetworkInput r d => transformer theta' X) :=
    Set.EqOn.eventuallyEq_of_mem heq (IsOpen.mem_nhds hopen hX0)
  have hfun := AnalyticOnNhd.eq_of_eventuallyEq hanalytic hanalytic' heventually
  intro X
  exact congrFun hfun X

section Analyticity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] {U : Set E}

theorem analyticOnNhd_matrix_coord {n p : Nat}
    {F : E → Matrix (Fin n) (Fin p) Real}
    (hF : AnalyticOnNhd Real F U) (i : Fin n) (j : Fin p) :
    AnalyticOnNhd Real (fun x => F x i j) U := by
  let row : Matrix (Fin n) (Fin p) Real →L[Real] (Fin p → Real) :=
    ContinuousLinearMap.proj i
  let coord : (Fin p → Real) →L[Real] Real := ContinuousLinearMap.proj j
  simpa [row, coord, Function.comp] using (coord.comp row).comp_analyticOnNhd hF

theorem analyticOnNhd_matrix_of_coords {n p : Nat}
    {F : E → Matrix (Fin n) (Fin p) Real}
    (hF : ∀ i j, AnalyticOnNhd Real (fun x => F x i j) U) :
    AnalyticOnNhd Real F U := by
  let Mof : (Fin n → Fin p → Real) →L[Real] Matrix (Fin n) (Fin p) Real :=
    LinearMap.toContinuousLinearMap
      ((Matrix.ofLinearEquiv Real : (Fin n → Fin p → Real) ≃ₗ[Real]
        Matrix (Fin n) (Fin p) Real).toLinearMap)
  have hPi : AnalyticOnNhd Real (fun x => fun i => fun j => F x i j) U := by
    apply AnalyticOnNhd.pi
    intro i
    apply AnalyticOnNhd.pi
    intro j
    exact hF i j
  simpa [Mof, Function.comp] using Mof.comp_analyticOnNhd hPi

theorem analyticOnNhd_matrix_transpose_coord {n p : Nat}
    {F : E → Matrix (Fin n) (Fin p) Real}
    (hF : ∀ i j, AnalyticOnNhd Real (fun x => F x i j) U)
    (i : Fin p) (j : Fin n) : AnalyticOnNhd Real (fun x => (F x)ᵀ i j) U := by
  simpa [Matrix.transpose_apply] using hF j i

theorem analyticOnNhd_matrix_mul_coord {n p q : Nat}
    {F : E → Matrix (Fin n) (Fin p) Real}
    {G : E → Matrix (Fin p) (Fin q) Real}
    (hF : ∀ i j, AnalyticOnNhd Real (fun x => F x i j) U)
    (hG : ∀ i j, AnalyticOnNhd Real (fun x => G x i j) U)
    (i : Fin n) (j : Fin q) : AnalyticOnNhd Real (fun x => (F x * G x) i j) U := by
  simp only [Matrix.mul_apply]
  apply Finset.analyticOnNhd_fun_sum
  intro a _
  exact (hF i a).mul (hG a j)

theorem softmaxColC_coord_analyticOnNhd {T : Nat}
    {F : E → Matrix (Fin T) (Fin T) Real}
    (hF : ∀ i j, AnalyticOnNhd Real (fun x => F x i j) U)
    (i j : Fin T) : AnalyticOnNhd Real (fun x => softmaxColC (F x) i j) U := by
  by_cases hij : i ≤ j
  · have hnum : AnalyticOnNhd Real (fun x => Real.exp (F x i j)) U := (hF i j).rexp
    have hden : AnalyticOnNhd Real
        (fun x => ∑ i' ∈ Finset.Iic j, Real.exp (F x i' j)) U := by
      apply Finset.analyticOnNhd_fun_sum
      intro i' _
      exact (hF i' j).rexp
    have hden_ne : ∀ x ∈ U,
        (∑ i' ∈ Finset.Iic j, Real.exp (F x i' j)) ≠ 0 := by
      intro x _
      exact ne_of_gt (Finset.sum_pos
        (fun i' _ => Real.exp_pos (F x i' j)) ⟨j, Finset.mem_Iic.2 le_rfl⟩)
    simpa [softmaxColC, TransformerIdentifiability.NLayer.causalSoftmax, hij] using
      hnum.div hden hden_ne
  · simpa [softmaxColC, TransformerIdentifiability.NLayer.causalSoftmax, hij] using
      (analyticOnNhd_const (𝕜 := Real) (v := (0 : Real)) (s := U))

theorem layer_coord_analyticOnNhd_comp {L k d T : Nat} (theta : Params L k d)
    (l : Fin L) {F : E → Matrix (Fin d) (Fin T) Real}
    (hF : ∀ i j, AnalyticOnNhd Real (fun x => F x i j) U)
    (i : Fin d) (j : Fin T) :
    AnalyticOnNhd Real (fun x => layer theta l (F x) i j) U := by
  have hsum : AnalyticOnNhd Real
      (fun x : E => ∑ a : Fin k,
        (valueMatrix theta l a * F x *
          softmaxColC ((F x)ᵀ * attentionMatrix theta l a * F x)) i j) U := by
    apply Finset.analyticOnNhd_fun_sum
    intro a _
    have hV : ∀ i' j', AnalyticOnNhd Real
        (fun _x : E => valueMatrix theta l a i' j') U := by
      intro i' j'; exact analyticOnNhd_const
    have hA : ∀ i' j', AnalyticOnNhd Real
        (fun _x : E => attentionMatrix theta l a i' j') U := by
      intro i' j'; exact analyticOnNhd_const
    have hFT : ∀ i' j', AnalyticOnNhd Real (fun x => (F x)ᵀ i' j') U :=
      fun i' j' => analyticOnNhd_matrix_transpose_coord hF i' j'
    have hleft : ∀ i' j', AnalyticOnNhd Real
        (fun x => ((F x)ᵀ * attentionMatrix theta l a) i' j') U :=
      fun i' j' => analyticOnNhd_matrix_mul_coord hFT hA i' j'
    have hscore : ∀ i' j', AnalyticOnNhd Real
        (fun x => ((F x)ᵀ * attentionMatrix theta l a * F x) i' j') U :=
      fun i' j' => analyticOnNhd_matrix_mul_coord hleft hF i' j'
    have hsoft : ∀ i' j', AnalyticOnNhd Real
        (fun x => softmaxColC
          ((F x)ᵀ * attentionMatrix theta l a * F x) i' j') U :=
      fun i' j' => softmaxColC_coord_analyticOnNhd hscore i' j'
    have hVF : ∀ i' j', AnalyticOnNhd Real
        (fun x => (valueMatrix theta l a * F x) i' j') U :=
      fun i' j' => analyticOnNhd_matrix_mul_coord hV hF i' j'
    exact analyticOnNhd_matrix_mul_coord hVF hsoft i j
  intro x hx
  refine AnalyticAt.congr (hsum x hx) ?_
  filter_upwards with y
  simp [layer, Matrix.sum_apply]

theorem transformer_coord_analyticOnNhd_comp {r m k d : Nat}
    (theta : Params m k d) {F : E → NetworkInput r d}
    (hF : ∀ i j, AnalyticOnNhd Real (fun x => F x i j) U) :
    ∀ i j, AnalyticOnNhd Real (fun x => transformer theta (F x) i j) U := by
  revert theta F hF
  induction m with
  | zero => intro theta F hF i j; simpa using hF i j
  | succ m ih =>
      intro theta F hF i j
      simpa [transformer] using ih (Fin.tail theta)
        (F := fun x => layer theta 0 (F x))
        (layer_coord_analyticOnNhd_comp theta 0 hF) i j

end Analyticity

theorem networkInput_coord_analyticOnNhd_univ {r d : Nat}
    (i : Fin d) (j : Fin (seqLength r)) :
    AnalyticOnNhd Real (fun X : NetworkInput r d => X i j) Set.univ := by
  have hid : AnalyticOnNhd Real (fun X : NetworkInput r d => X) Set.univ := by
    simpa using (ContinuousLinearMap.id Real (NetworkInput r d)).analyticOnNhd Set.univ
  exact analyticOnNhd_matrix_coord hid i j

theorem transformer_analyticOnNhd_univ {r m k d : Nat} (theta : Params m k d) :
    AnalyticOnNhd Real (fun X : NetworkInput r d => transformer theta X) Set.univ := by
  apply analyticOnNhd_matrix_of_coords
  intro i j
  exact transformer_coord_analyticOnNhd_comp theta
    (fun i' j' => networkInput_coord_analyticOnNhd_univ i' j') i j

theorem openSetToGlobal {r m k d : Nat} (hr : 0 < r)
    (theta theta' : Params m k d) (omega : Set (NetworkInput r d))
    (homega : NonemptyOpenInputSet omega)
    (heq : TransformerEqualOn (r := r) theta theta' omega) :
    OpenSetToGlobalConclusion r theta theta' := by
  have hglobal := transformerEqualGlobally_of_equalOn_nonempty_open_of_analytic
    (transformer_analyticOnNhd_univ (r := r) theta)
    (transformer_analyticOnNhd_univ (r := r) theta')
    homega.isOpen homega.nonempty heq
  exact ⟨hglobal, probeOutput_eq_of_transformerEqualGlobally hr hglobal⟩

/-!
# The gauge-threaded induction invariant conclusion (`thm:open-induction-invariant`)

This section is a STATEMENT-only packaging of clauses C1–C5 of the strengthened
open-set induction invariant.  Nothing here is proved: the conclusion structure
and the reduced-pair package are exactly the data the depth induction
(NS154/NS155) will produce and consume.

Depth-indexing convention.  The "whole network" at the current recursion level
has `n + 1` layers, i.e. `theta theta' : Params (n + 1) k d` (the TeX depth is
`m = n + 1 ≥ 1`).  The reduced-pair clause (C5) only fires when there are at
least two layers, so it is stated on `Params (p + 2) k d` and folded into the
general package by a match on `n` (base `n = 0` is vacuous, `n = p + 1` carries
the C5 data).  All head-permutation and gauge orientations are taken verbatim
from `TargetToSourceMatching` (Gauge.lean), `relabelFirstLayer` /
`inputGaugeTail` (Relabel.lean) and `RecursiveGeneric` (Recursive.lean).
-/

noncomputable section

/-- `G_1`, the layer-1 output gauge of a matching: the gauge sitting at the
interface between the first and second layers (`G_0 = I` on the input side, so
this is the first nontrivial gauge). -/
def firstGaugeOf {L k d : Nat} {theta theta' : Params (L + 1) k d}
    (matching : TargetToSourceMatching theta theta') : GaugeMatrix d :=
  matching.gauge.get (0 : Fin (L + 1)).succ

/-- Clause C5 (reduced pair), on a network with at least two layers.  With
`σ₁ = matching.headPerm 0` and `G₁ = firstGaugeOf matching`:

* `θ̄ := σ₁ ·₁ θ` has `θ̄_{≥2} = θ_{≥2}` (`tail_relabel_eq`);
* `Layer₁^{θ̄} = G₁⁻¹ ∘ Layer₁^{θ'}` columnwise (`firstLayer_eq`);
* there is a nonempty open `Ω_tail` on which the source tail `θ_{≥2}` and the
  input-gauged target tail `G₁ ▷ θ'_{≥2}` realize the same transformer
  (`tail_open`);
* the input-gauged target tail is recursively generic, i.e.
  `G₁ ▷ θ'_{≥2} ∈ 𝒢_{m-1,k}` (`gaugedTail_generic`).

Together these are exactly the hypothesis package for the recursive call at
depth `m - 1 = p + 1`. -/
structure ReducedPair (r : Nat) {p k d : Nat} (theta theta' : Params (p + 2) k d)
    (matching : TargetToSourceMatching theta theta') : Prop where
  /-- `θ̄_{≥2} = θ_{≥2}`: relabeling only the first layer leaves the tail fixed. -/
  tail_relabel_eq :
    Fin.tail (relabelFirstLayer theta (matching.headPerm 0)) = Fin.tail theta
  /-- `Layer₁^{θ̄} = G₁⁻¹ ∘ Layer₁^{θ'}`, with `G₁⁻¹` acting columnwise. -/
  firstLayer_eq : ∀ {T : Nat} (X : Matrix (Fin d) (Fin T) Real),
    layer (relabelFirstLayer theta (matching.headPerm 0)) 0 X =
      (firstGaugeOf matching).invMatrix * layer theta' 0 X
  /-- A nonempty open `Ω_tail` on which the source tail and the input-gauged
  target tail agree as transformers. -/
  tail_open : ∃ omega : Set (NetworkInput r d),
    NonemptyOpenInputSet omega ∧
      TransformerEqualOn (r := r) (Fin.tail theta)
        (inputGaugeTail (firstGaugeOf matching) (Fin.tail theta')) omega
  /-- `G₁ ▷ θ'_{≥2} ∈ 𝒢_{m-1,k}`. -/
  gaugedTail_generic :
    RecursiveGeneric r (p + 1) k d
      (inputGaugeTail (firstGaugeOf matching) (Fin.tail theta'))

/-- Clause C5 folded into the general `n + 1`-layer package: vacuous in the
one-layer base case, and the full `ReducedPair` data once there are at least two
layers. -/
def ReducedPairPackage (r : Nat) {n k d : Nat} (theta theta' : Params (n + 1) k d)
    (matching : TargetToSourceMatching theta theta') : Prop :=
  match n with
  | 0 => True
  | _ + 1 => ReducedPair r theta theta' matching

/-- The full conclusion package of `thm:open-induction-invariant`, clauses
C1–C5.  This is a `Type` (it carries the matching data), not a proof.

* C1 — `global`: the open-set equality has extended to all of `ℝ^{d×T}`
  (globalized via `openSetToGlobal` from NS150).
* C2/C3 — `matching` and `matching_unique`: a `TargetToSourceMatching`
  bundles the unique target-to-source permutation family
  `σ_j = matching.headPerm (j-1)` and the unique boundary-normalized gauge chain
  `G_j = matching.gauge.get j` (with `G_0 = G_m = I`), and its
  `attention_eq`/`value_eq` fields are exactly the C2 relations
  `A_{j,σ_j(h)} = G_{j-1}ᵀ A'_{jh} G_{j-1}`,
  `V_{j,σ_j(h)} = G_j⁻¹ V'_{jh} G_{j-1}`.  Paired matching (C3) is encoded by
  there being a single such structure whose uniqueness is asserted, with no
  separate value permutation or second gauge.
* C4 — `firstAttention_eq`, `firstValue_eq`, `firstGauge_unique`: the first
  layer explicitly.  `A_{1,σ_1(h)} = A'_{1h}` (no input-interface gauge, since
  `G_0 = I`), and `G_1 = firstGaugeOf matching` is the unique invertible matrix
  with `V'_{1h} = G_1 V_{1,σ_1(h)}`.
* C5 — `reducedPair`: the reduced-pair recursive-call package (`ReducedPairPackage`). -/
structure OpenInductionInvariantConclusion (r : Nat) {n k d : Nat}
    (theta theta' : Params (n + 1) k d) : Type where
  /-- C1: equality extends to all inputs. -/
  global : TransformerEqualGlobally (r := r) theta theta'
  /-- C2/C3: the target-to-source permutation family and gauge chain, with the
  TeX attention/value relations. -/
  matching : TargetToSourceMatching theta theta'
  /-- C2/C3 uniqueness: the matching data is unique. -/
  matching_unique : ∀ matching' : TargetToSourceMatching theta theta',
    matching' = matching
  /-- C4 (attention): `A_{1,σ_1(h)} = A'_{1h}`, no gauge on the input interface. -/
  firstAttention_eq : ∀ h : Fin k,
    attentionMatrix theta 0 (matching.headPerm 0 h) = attentionMatrix theta' 0 h
  /-- C4 (value): `V'_{1h} = G_1 V_{1,σ_1(h)}` with `G_1 = firstGaugeOf matching`. -/
  firstValue_eq : ∀ h : Fin k,
    valueMatrix theta' 0 h =
      (firstGaugeOf matching).matrix * valueMatrix theta 0 (matching.headPerm 0 h)
  /-- C4 (uniqueness): `G_1` is the unique invertible matrix with the value
  relation, by joint surjectivity of the primed first layer. -/
  firstGauge_unique : ∀ H : GaugeMatrix d,
    (∀ h : Fin k, valueMatrix theta' 0 h =
        H.matrix * valueMatrix theta 0 (matching.headPerm 0 h)) →
      H = firstGaugeOf matching
  /-- C5: the reduced-pair recursive-call package (vacuous when `n = 0`). -/
  reducedPair : ReducedPairPackage r theta theta' matching

/-- Top-level statement of `thm:open-induction-invariant`: under the standing
hypotheses (`r ≥ 2`, the no-skip dimension threshold, target genericity
`θ' ∈ 𝒢_{m,k}`, and open-set equality on a nonempty open `Ω`), the full C1–C5
conclusion package holds. -/
def OpenInductionInvariant (r : Nat) {n k d : Nat}
    (theta theta' : Params (n + 1) k d)
    (omega : Set (NetworkInput r d)) : Prop :=
  2 ≤ r →
  dStarNS (n + 1) k ≤ d →
  RecursiveGeneric r (n + 1) k d theta' →
  NonemptyOpenInputSet omega →
  TransformerEqualOn (r := r) theta theta' omega →
  Nonempty (OpenInductionInvariantConclusion r theta theta')

end

end TransformerIdentifiability.NLayer.NoSkip
