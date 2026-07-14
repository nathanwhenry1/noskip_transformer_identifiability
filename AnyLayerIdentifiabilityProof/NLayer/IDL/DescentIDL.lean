import AnyLayerIdentifiabilityProof.NLayer.Genericity.GenericityMain
import AnyLayerIdentifiabilityProof.NLayer.IDL.SaturationMatching

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer

/-!
# Step 3: realization, sweep, and `ID_L`

Target contents:
* realization lemma
* sweep lemma
* induction proof of the strengthened identifiability theorem `ID_L`

Corresponds to `n_layer_proof.tex`, Section 7.
-/

namespace Params

/-- The first layer of a positive-depth parameter family. -/
abbrev headLayer {L d : Nat} (θ : Params (L + 1) d) :
    Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ :=
  θ 0

/-- The first value matrix of a positive-depth parameter family. -/
abbrev headValue {L d : Nat} (θ : Params (L + 1) d) :
    Matrix (Fin d) (Fin d) ℝ :=
  (headLayer θ).1

/-- The first attention matrix of a positive-depth parameter family. -/
abbrev headAttention {L d : Nat} (θ : Params (L + 1) d) :
    Matrix (Fin d) (Fin d) ℝ :=
  (headLayer θ).2

/-- The tail parameter family after removing the first layer. -/
abbrev tail {L d : Nat} (θ : Params (L + 1) d) : Params L d :=
  Fin.tail θ

/-- A positive-depth parameter family is determined by its first layer and its tail. -/
theorem eq_of_headLayer_tail_eq {L d : Nat} {θ θ' : Params (L + 1) d}
    (hhead : headLayer θ = headLayer θ')
    (htail : tail θ = tail θ') :
    θ = θ' := by
  funext i
  refine Fin.cases ?_ ?_ i
  · exact hhead
  · intro j
    exact congrFun htail j

end Params

/-! ## Constructor-friendly `ID_L` endpoint wrappers -/

/-- Data sufficient to stitch one identified head layer and one identified tail into
full equality of positive-depth parameter families. -/
structure HeadTailIdentificationData {L d : Nat}
    (θ θ' : Params (L + 1) d) : Prop where
  headValue_eq : Params.headValue θ = Params.headValue θ'
  headAttention_eq : Params.headAttention θ = Params.headAttention θ'
  tail_eq : Params.tail θ = Params.tail θ'

namespace HeadTailIdentificationData

variable {L d : Nat} {θ θ' : Params (L + 1) d}

/-- The two component equalities combine to equality of the whole first layer. -/
theorem headLayer_eq (D : HeadTailIdentificationData θ θ') :
    Params.headLayer θ = Params.headLayer θ' :=
  Prod.ext D.headValue_eq D.headAttention_eq

/-- Compile head/tail identification data to equality of the full parameter family. -/
theorem params_eq (D : HeadTailIdentificationData θ θ') :
    θ = θ' :=
  Params.eq_of_headLayer_tail_eq D.headLayer_eq D.tail_eq

/-- Build head/tail identification data from the three component obligations usually
left at the end of the `ID_L` induction step. -/
def ofComponentEq
    (hvalue : Params.headValue θ = Params.headValue θ')
    (htail : Params.tail θ = Params.tail θ')
    (hattention : Params.headAttention θ = Params.headAttention θ') :
    HeadTailIdentificationData θ θ' where
  headValue_eq := hvalue
  headAttention_eq := hattention
  tail_eq := htail

end HeadTailIdentificationData

/-! ## First-layer effective paths -/

/-- A real probe point `(w, v)`.  This mirrors the TeX notation for the endpoint of a
path in `R^{2d}` without committing this file to a concrete analytic path class yet. -/
abbrev ProbePoint (d : Nat) : Type :=
  (Fin d -> ℝ) × (Fin d -> ℝ)

/-- A pointwise real probe path.  The analytic `H_T` obligations are supplied by the
realization/sweep packages below, so this type only records the values on real `τ`. -/
abbrev ProbePath (d : Nat) : Type :=
  ℝ -> ProbePoint d

/-- The constant path associated to a probe pair. -/
def constantProbePath {d : Nat} (p : ProbePair d) : ProbePath d :=
  fun _ => p

@[simp]
theorem constantProbePath_apply {d : Nat} (p : ProbePair d) (τ : ℝ) :
    constantProbePath p τ = p :=
  rfl

/-- The first sigmoid gate along a probe. -/
noncomputable def firstLayerGate {d : Nat} (r : Nat)
    (A : Matrix (Fin d) (Fin d) ℝ) (w v : Fin d -> ℝ) (τ : ℝ) : ℝ :=
  sig (τ * matrixBilin A w v + Real.log r)

/-- The dial map `Φ_t(w,v)` for a fixed first value matrix. -/
noncomputable def firstLayerDialPoint {d : Nat}
    (V : Matrix (Fin d) (Fin d) ℝ) (t : ℝ)
    (w v : Fin d -> ℝ) : ProbePoint d :=
  (w + V.mulVec w - t • V.mulVec w,
    v + V.mulVec v + t • V.mulVec w)

/-- The first-layer effective point, obtained by dialing with the actual first gate. -/
noncomputable def firstLayerEffectivePoint {d : Nat} (r : Nat)
    (V A : Matrix (Fin d) (Fin d) ℝ) (w v : Fin d -> ℝ) (τ : ℝ) :
    ProbePoint d :=
  firstLayerDialPoint V (firstLayerGate r A w v τ) w v

/-- The first-layer effective point for a positive-depth parameter family. -/
noncomputable def paramsFirstLayerEffectivePoint {L d : Nat} (r : Nat)
    (θ : Params (L + 1) d) (w v : Fin d -> ℝ) (τ : ℝ) :
    ProbePoint d :=
  firstLayerEffectivePoint r (Params.headValue θ) (Params.headAttention θ) w v τ

@[simp]
theorem firstLayerDialPoint_fst {d : Nat} (V : Matrix (Fin d) (Fin d) ℝ)
    (t : ℝ) (w v : Fin d -> ℝ) :
    (firstLayerDialPoint V t w v).1 = w + V.mulVec w - t • V.mulVec w :=
  rfl

@[simp]
theorem firstLayerDialPoint_snd {d : Nat} (V : Matrix (Fin d) (Fin d) ℝ)
    (t : ℝ) (w v : Fin d -> ℝ) :
    (firstLayerDialPoint V t w v).2 = v + V.mulVec v + t • V.mulVec w :=
  rfl

/-- Peeling restated through the effective-point interface used by realization. -/
theorem peeling_paramsFirstLayerEffectivePoint {L d : Nat} (r : Nat) (hr : 0 < r)
    (θ : Params (L + 1) d) (w v : Fin d -> ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    Fobs r θ w v τ =
      Fobs r (Params.tail θ)
        (paramsFirstLayerEffectivePoint r θ w v τ).1
        (paramsFirstLayerEffectivePoint r θ w v τ).2 τ := by
  simpa [Params.tail, Params.headValue, Params.headAttention, Params.headLayer,
    paramsFirstLayerEffectivePoint, firstLayerEffectivePoint, firstLayerDialPoint,
    firstLayerGate, matrixBilin] using peeling r hr θ w v hτ

/-- Closed-recursion form of `peeling_paramsFirstLayerEffectivePoint`. -/
theorem Frec_succ_paramsFirstLayerEffectivePoint {L d : Nat} (r : Nat)
    (θ : Params (L + 1) d) (w v : Fin d -> ℝ) (τ : ℝ) :
    Frec r θ w v τ =
      Frec r (Params.tail θ)
        (paramsFirstLayerEffectivePoint r θ w v τ).1
        (paramsFirstLayerEffectivePoint r θ w v τ).2 τ := by
  simpa [Params.tail, Params.headValue, Params.headAttention, Params.headLayer,
    paramsFirstLayerEffectivePoint, firstLayerEffectivePoint, firstLayerDialPoint,
    firstLayerGate, matrixBilin] using Frec_succ r θ w v τ

/-! ## Matching packages consumed by the `ID_L` stitch step -/

/-- First-layer matching in the form needed by Step 3.

The `endpoint` field deliberately consumes `FirstLayerEndpointData` from
`SaturationMatching`: it carries the Step 1/Step 2 first-attention endpoint and the
nonzero target-value certificate.  The matching argument then adds equality of the first
value matrices. -/
structure FirstLayerMatchedData {L d : Nat}
    (θ θ' : Params (L + 1) d) : Prop where
  endpoint :
    FirstLayerEndpointData (Params.headAttention θ) (Params.headAttention θ')
      (Params.headValue θ)
  headValue_eq : Params.headValue θ = Params.headValue θ'

namespace FirstLayerMatchedData

variable {L d : Nat} {θ θ' : Params (L + 1) d}

/-- The matched first layer gives equality of first attention matrices. -/
theorem headAttention_eq (D : FirstLayerMatchedData θ θ') :
    Params.headAttention θ = Params.headAttention θ' :=
  D.endpoint.attention_eq

/-- The Step 1/Step 2 target-value certificate says the first value matrix is nonzero. -/
theorem headValue_ne_zero (D : FirstLayerMatchedData θ θ') :
    Params.headValue θ ≠ 0 :=
  D.endpoint.targetValue_ne_zero

/-- Matched first layers produce identical effective first-layer points. -/
theorem paramsFirstLayerEffectivePoint_eq (D : FirstLayerMatchedData θ θ')
    (r : Nat) (w v : Fin d -> ℝ) (τ : ℝ) :
    paramsFirstLayerEffectivePoint r θ w v τ =
      paramsFirstLayerEffectivePoint r θ' w v τ := by
  simp [paramsFirstLayerEffectivePoint, firstLayerEffectivePoint, firstLayerDialPoint,
    firstLayerGate, matrixBilin, D.headValue_eq, D.headAttention_eq]

/-- Convert matched first-layer data and identified tails into the generic head/tail
stitch package. -/
def toHeadTailIdentificationData (D : FirstLayerMatchedData θ θ')
    (htail : Params.tail θ = Params.tail θ') :
    HeadTailIdentificationData θ θ' :=
  HeadTailIdentificationData.ofComponentEq D.headValue_eq htail D.headAttention_eq

/-- Compile matched first-layer data and identified tails to equality of parameters. -/
theorem params_eq (D : FirstLayerMatchedData θ θ')
    (htail : Params.tail θ = Params.tail θ') :
    θ = θ' :=
  (D.toHeadTailIdentificationData htail).params_eq

/-- Constructor from the matching conclusion and an existing first-layer endpoint. -/
def ofEndpointAndHeadValueEq
    (endpoint :
      FirstLayerEndpointData (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (hvalue : Params.headValue θ = Params.headValue θ') :
    FirstLayerMatchedData θ θ' where
  endpoint := endpoint
  headValue_eq := hvalue

/-- Constructor from component equalities and a nonzero first value matrix. -/
def ofComponentEq
    (hvalue : Params.headValue θ = Params.headValue θ')
    (hattention : Params.headAttention θ = Params.headAttention θ')
    (hvalue_ne : Params.headValue θ ≠ 0) :
    FirstLayerMatchedData θ θ' where
  endpoint := FirstLayerEndpointData.of_attention_eq hattention hvalue_ne
  headValue_eq := hvalue

end FirstLayerMatchedData

/-- The generic `(G3)` first-skip determinant condition transfers from the primed first
value matrix to the matched unprimed first value matrix. -/
theorem headValueSkip_det_ne_zero_of_matching
    {L d : Nat} {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ') :
    (skipB (Params.headValue θ)).det ≠ 0 := by
  have hprimed : (skipB (Params.headValue θ')).det ≠ 0 := by
    simpa [Params.headValue, Params.headLayer, paramStream_apply_of_lt] using
      hstep.g3_det_firstSkip
  simpa [matching.headValue_eq] using hprimed

/-! ## Realization and sweep interfaces -/

/-- Pointwise realization output for Lemma `realization`.

`source` is the lifted full-depth path and `target` is the lower-depth path.  The record
states only the part needed by the induction assembly: after `threshold`, the first-layer
effective path of `source` is exactly `target`.  Analytic membership in `H_T`, endpoint
limits, and the Banach fixed-point construction are intentionally supplied by future
constructors of this record. -/
structure RealizationData {d : Nat} (r : Nat)
    (V A : Matrix (Fin d) (Fin d) ℝ)
    (target source : ProbePath d) where
  threshold : ℝ
  threshold_nonneg : 0 ≤ threshold
  effective_eq :
    ∀ τ : ℝ, threshold < τ ->
      firstLayerEffectivePoint r V A (source τ).1 (source τ).2 τ = target τ

/-- A sweep package: every lower-depth path in `TailPaths` can be realized by a
full-depth path in `FullPaths` through the common first layer. -/
structure TailPathLiftData {L d : Nat} (r : Nat)
    (θ θ' : Params (L + 1) d)
    (FullPaths TailPaths : Set (ProbePath d)) : Prop where
  matching : FirstLayerMatchedData θ θ'
  realize :
    ∀ target : ProbePath d, target ∈ TailPaths ->
      ∃ source : ProbePath d, source ∈ FullPaths ∧
        Nonempty (RealizationData r (Params.headValue θ) (Params.headAttention θ)
          target source)

/-- The open lower-depth region and its realization lifts, as produced by Lemma
`sweep` in the TeX proof. -/
structure SweepData {L d : Nat} (r : Nat)
    (θ θ' : Params (L + 1) d)
    (FullPaths TailPaths : Set (ProbePath d)) where
  tailRegion : Set (ProbePoint d)
  tailRegion_open : IsOpen tailRegion
  tailRegion_nonempty : tailRegion.Nonempty
  tail_anchor_nonempty :
    L = 1 ∨ (tailRegion ∩ unwoundAnchorSet (Params.tail θ')).Nonempty
  constant_paths_available :
    ∀ p : ProbePair d, p ∈ tailRegion -> constantProbePath p ∈ TailPaths
  lifts : TailPathLiftData r θ θ' FullPaths TailPaths

/-- Agreement of observables along one real path after a nonnegative threshold. -/
def ObservableAgreementOnPath {L d : Nat} (r : Nat)
    (θ θ' : Params L d) (P : ProbePath d) (T : ℝ) : Prop :=
  0 ≤ T ∧
    ∀ τ : ℝ, T < τ ->
      Fobs r θ (P τ).1 (P τ).2 τ =
        Fobs r θ' (P τ).1 (P τ).2 τ

/-- Agreement of observables along every path in a path class. -/
def ObservableAgreementForPaths {L d : Nat} (r : Nat)
    (θ θ' : Params L d) (Paths : Set (ProbePath d)) : Prop :=
  ∀ P : ProbePath d, P ∈ Paths -> ∃ T : ℝ, ObservableAgreementOnPath r θ θ' P T

/-- Realization/sweep transfer: full-depth path agreement descends to lower-depth path
agreement for the tails once the first layer is matched. -/
theorem tail_observableAgreement_of_lifts {L d : Nat} (r : Nat) (hr : 0 < r)
    {θ θ' : Params (L + 1) d} {FullPaths TailPaths : Set (ProbePath d)}
    (D : TailPathLiftData r θ θ' FullPaths TailPaths)
    (hfull : ObservableAgreementForPaths r θ θ' FullPaths) :
    ObservableAgreementForPaths r (Params.tail θ) (Params.tail θ') TailPaths := by
  intro target htarget
  rcases D.realize target htarget with ⟨source, hsource, hR⟩
  rcases hR with ⟨R⟩
  rcases hfull source hsource with ⟨Tfull, _hTfull_nonneg, hTfull_eq⟩
  refine ⟨max R.threshold Tfull, ?_, ?_⟩
  · exact le_trans R.threshold_nonneg (le_max_left R.threshold Tfull)
  · intro τ hτ
    have hRτ : R.threshold < τ := lt_of_le_of_lt (le_max_left R.threshold Tfull) hτ
    have hFullτ : Tfull < τ := lt_of_le_of_lt (le_max_right R.threshold Tfull) hτ
    have hmax_nonneg : 0 ≤ max R.threshold Tfull :=
      le_trans R.threshold_nonneg (le_max_left R.threshold Tfull)
    have hτ_nonneg : 0 ≤ τ := le_of_lt (lt_of_le_of_lt hmax_nonneg hτ)
    have hRealize := R.effective_eq τ hRτ
    have hRealizeParams :
        paramsFirstLayerEffectivePoint r θ (source τ).1 (source τ).2 τ = target τ := by
      simpa [paramsFirstLayerEffectivePoint] using hRealize
    have hMatch := D.matching.paramsFirstLayerEffectivePoint_eq r
      (source τ).1 (source τ).2 τ
    calc
      Fobs r (Params.tail θ) (target τ).1 (target τ).2 τ
          = Fobs r (Params.tail θ)
              (paramsFirstLayerEffectivePoint r θ (source τ).1 (source τ).2 τ).1
              (paramsFirstLayerEffectivePoint r θ (source τ).1 (source τ).2 τ).2 τ := by
            rw [← hRealizeParams]
      _ = Fobs r θ (source τ).1 (source τ).2 τ := by
            exact (peeling_paramsFirstLayerEffectivePoint r hr θ
              (source τ).1 (source τ).2 hτ_nonneg).symm
      _ = Fobs r θ' (source τ).1 (source τ).2 τ := hTfull_eq τ hFullτ
      _ = Fobs r (Params.tail θ')
              (paramsFirstLayerEffectivePoint r θ' (source τ).1 (source τ).2 τ).1
              (paramsFirstLayerEffectivePoint r θ' (source τ).1 (source τ).2 τ).2 τ := by
            exact peeling_paramsFirstLayerEffectivePoint r hr θ'
              (source τ).1 (source τ).2 hτ_nonneg
      _ = Fobs r (Params.tail θ')
              (paramsFirstLayerEffectivePoint r θ (source τ).1 (source τ).2 τ).1
              (paramsFirstLayerEffectivePoint r θ (source τ).1 (source τ).2 τ).2 τ := by
            rw [← hMatch]
      _ = Fobs r (Params.tail θ') (target τ).1 (target τ).2 τ := by
            rw [hRealizeParams]

namespace SweepData

/-- A sweep package supplies the lower-depth observable agreement needed by the
inductive hypothesis. -/
theorem tail_observableAgreement {L d : Nat} {r : Nat} (hr : 0 < r)
    {θ θ' : Params (L + 1) d} {FullPaths TailPaths : Set (ProbePath d)}
    (S : SweepData r θ θ' FullPaths TailPaths)
    (hfull : ObservableAgreementForPaths r θ θ' FullPaths) :
    ObservableAgreementForPaths r (Params.tail θ) (Params.tail θ') TailPaths :=
  tail_observableAgreement_of_lifts r hr S.lifts hfull

end SweepData

/-! ## `ID_L` induction assembly -/

/-- Data left after realization/sweep and the lower-depth inductive hypothesis have
identified the tail. -/
structure IDLInductionAssemblyData {L d : Nat}
    (θ θ' : Params (L + 1) d) : Prop where
  matching : FirstLayerMatchedData θ θ'
  tail_eq : Params.tail θ = Params.tail θ'

namespace IDLInductionAssemblyData

variable {L d : Nat} {θ θ' : Params (L + 1) d}

/-- Compile the Step 3 induction assembly data to equality of parameters. -/
theorem params_eq (D : IDLInductionAssemblyData θ θ') :
    θ = θ' :=
  D.matching.params_eq D.tail_eq

end IDLInductionAssemblyData

/-- The `ID_L` stitch step: matching identifies the first layer and the induction
hypothesis identifies the tail. -/
theorem IDL_induction_step {L d : Nat} {θ θ' : Params (L + 1) d}
    (matching : FirstLayerMatchedData θ θ')
    (htail : Params.tail θ = Params.tail θ') :
    θ = θ' :=
  (IDLInductionAssemblyData.mk matching htail).params_eq

/-- The depth-one stitch endpoint.  The analytic one-layer pole-transfer argument is
still responsible for constructing `FirstLayerMatchedData`; once it does, there is no
tail left to identify. -/
theorem IDL_base_of_firstLayerMatched {d : Nat} {θ θ' : Params 1 d}
    (matching : FirstLayerMatchedData θ θ') :
    θ = θ' := by
  apply matching.params_eq
  funext i
  exact Fin.elim0 i

/-! ## N-layer induction assembly wrappers -/

/-- N-layer wrapper around the `ID_L` induction step. -/
theorem IDL_nLayer_induction_step {L d : Nat}
    {θ θ' : Params (L + 1) d}
    (matching : FirstLayerMatchedData θ θ')
    (htail : Params.tail θ = Params.tail θ') :
    θ = θ' :=
  IDL_induction_step matching htail

/-- N-layer wrapper around the depth-one stitch endpoint. -/
theorem IDL_nLayer_depth_one_stitch {d : Nat} {θ θ' : Params 1 d}
    (matching : FirstLayerMatchedData θ θ') :
    θ = θ' :=
  IDL_base_of_firstLayerMatched matching

end TransformerIdentifiability.NLayer
