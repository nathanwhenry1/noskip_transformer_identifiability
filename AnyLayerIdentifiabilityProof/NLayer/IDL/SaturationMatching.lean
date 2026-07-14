import AnyLayerIdentifiabilityProof.NLayer.Analytic.A1Identification
import AnyLayerIdentifiabilityProof.NLayer.Step1.OStar

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer

open Matrix

/-!
# Step 2: saturated limits, trichotomy, and matching

Target contents:
* sign region
* dial paths
* cascade lemma
* trichotomy
* matching and the `K = I` extraction

Corresponds to `n_layer_proof.tex`, Section 6.
-/

/-! ## Step 1 endpoint packages for later matching -/

/-- Matrix-level data supplied by Step 1 before the saturation/matching argument starts:
the first attention matrices agree, and the selected first value matrix is nonzero.

The `targetValue` field is intentionally generic.  Downstream files can instantiate it
with `firstValue θ`, the concrete positive-depth first value matrix, or another
definitionally convenient representative. -/
structure FirstLayerEndpointData {d : Nat}
    (A A' targetValue : Matrix (Fin d) (Fin d) ℝ) : Prop where
  attention_eq : A = A'
  targetValue_ne_zero : targetValue ≠ 0

namespace FirstLayerEndpointData

variable {d : Nat} {A A' targetValue : Matrix (Fin d) (Fin d) ℝ}

/-- A packaged first-layer endpoint gives equality of the associated bilinear slopes. -/
theorem slope_eq (D : FirstLayerEndpointData A A' targetValue)
    (w v : Fin d -> ℝ) :
    matrixBilin A w v = matrixBilin A' w v := by
  rw [D.attention_eq]

/-- Constructor from an already identified first attention matrix and a nonzero target
value matrix. -/
def of_attention_eq (hA : A = A') (hTarget : targetValue ≠ 0) :
    FirstLayerEndpointData A A' targetValue where
  attention_eq := hA
  targetValue_ne_zero := hTarget

end FirstLayerEndpointData

/-! ## First-layer geometry and dial paths -/

/-- The quadric `q(w,v)=w^T A v=0` used by the saturation argument. -/
def firstLayerQuadric {d : Nat} (A : Matrix (Fin d) (Fin d) ℝ)
    (p : ProbePair d) : Prop :=
  matrixBilin A p.1 p.2 = 0

/-- Quadratic slice-rigidity interface for `lem:quadA`.

On the selected quadric probe slice, every real quadratic residual of the form
`wᵀ X v + wᵀ Y w` is forced to have its bilinear part proportional to `A` and its
quadratic part antisymmetric.  This is kept as an explicit hypothesis: it is not a
consequence of the linear/vector coefficient-separation field on product patches. -/
def QuadricProbeSliceQuadraticCoefficientSeparation {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (Uq : Set (ProbePair d)) : Prop :=
  ∀ X Y : Matrix (Fin d) (Fin d) ℝ,
    (∀ p : ProbePair d, p ∈ Uq →
      p.1 ⬝ᵥ (X *ᵥ p.2) + p.1 ⬝ᵥ (Y *ᵥ p.1) = 0) →
    ∃ c : ℝ, X = c • A ∧ Y + Yᵀ = 0

/-- The vector `π(w,v)=A^T w - A v` from the sign-region and dial-path argument. -/
noncomputable def firstLayerPi {d : Nat} (A : Matrix (Fin d) (Fin d) ℝ)
    (p : ProbePair d) : Fin d -> ℝ :=
  Aᵀ *ᵥ p.1 - A *ᵥ p.2

/-- The nonvanishing conditions carried by every point of the sign region. -/
def firstLayerRegular {d : Nat} (A : Matrix (Fin d) (Fin d) ℝ)
    (p : ProbePair d) : Prop :=
  p.1 ≠ 0 ∧ Aᵀ *ᵥ p.1 ≠ 0 ∧ firstLayerPi A p ≠ 0

/-- A formal gate assignment with a free first gate and real tail constants.

The tail is zero-based: `tail 0` is the TeX constant `varsigma_2`. -/
noncomputable def complexGateAssignmentOfTail (z0 : ℂ) (tail : Nat -> ℝ) :
    Nat -> ℂ
  | 0 => z0
  | n + 1 => (tail n : ℂ)

/-- Real first-gate specialization of `complexGateAssignmentOfTail`. -/
noncomputable def gateAssignmentOfTail (t : ℝ) (tail : Nat -> ℝ) : Nat -> ℂ :=
  complexGateAssignmentOfTail (t : ℂ) tail

/-- The specialization `(t,1,...,1)` used for the primed sign-region positivity. -/
noncomputable def gateAssignmentOneTail (t : ℝ) : Nat -> ℂ :=
  gateAssignmentOfTail t fun _ => 1

/-- Formal slope polynomial specialized to a finite parameter family. -/
noncomputable def specializedPhi {L d : Nat} (θ : Params L d) (n : Nat)
    (z : Nat -> ℂ) (p : ProbePair d) : ℂ :=
  formalPhi (paramStream θ) n z p.1 p.2

/-- Explicit inverse coordinate for the real sigmoid on `(0, 1)`. -/
noncomputable def sigmoidLogit (t : ℝ) : ℝ :=
  Real.log (t / (1 - t))

/-- The explicit logit coordinate maps back to the prescribed sigmoid value. -/
theorem sig_sigmoidLogit {t : ℝ} (ht_pos : 0 < t) (ht_lt_one : t < 1) :
    sig (sigmoidLogit t) = t := by
  have hden_pos : 0 < 1 - t := by linarith
  have hratio_pos : 0 < t / (1 - t) := div_pos ht_pos hden_pos
  have ht_ne : t ≠ 0 := ne_of_gt ht_pos
  have hden_ne : 1 - t ≠ 0 := ne_of_gt hden_pos
  rw [sig, sigmoidLogit]
  rw [Real.exp_neg, Real.exp_log hratio_pos]
  field_simp [ht_ne, hden_ne]
  ring

namespace FirstLayerEndpointData

variable {d : Nat} {A A' targetValue : Matrix (Fin d) (Fin d) ℝ}

/-- Positive-depth wrapper: endpoint equality of `firstAttention` unfolds to equality
of the concrete first-layer attention matrices. -/
theorem headAttention_eq {L d : Nat} {θ θ' : Params (L + 1) d}
    {targetValue : Matrix (Fin d) (Fin d) ℝ}
    (D : FirstLayerEndpointData (firstAttention θ) (firstAttention θ') targetValue) :
    (θ 0).2 = (θ' 0).2 := by
  have hθ : firstAttention θ = (θ 0).2 := by
    simpa using firstAttention_eq_of_pos θ (Nat.succ_pos L)
  have hθ' : firstAttention θ' = (θ' 0).2 := by
    simpa using firstAttention_eq_of_pos θ' (Nat.succ_pos L)
  calc
    (θ 0).2 = firstAttention θ := hθ.symm
    _ = firstAttention θ' := D.attention_eq
    _ = (θ' 0).2 := hθ'

end FirstLayerEndpointData

/-- The dial-path `w` component
`w(τ)=w^0-(c/τ)y`. -/
noncomputable def dialW {d : Nat} (p : ProbePair d) (c : ℝ)
    (y : Fin d -> ℝ) (τ : ℝ) : Fin d -> ℝ :=
  p.1 - (c / τ) • y

/-- The dial-path `v` component
`v(τ)=v^0+(c/τ)y`. -/
noncomputable def dialV {d : Nat} (p : ProbePair d) (c : ℝ)
    (y : Fin d -> ℝ) (τ : ℝ) : Fin d -> ℝ :=
  p.2 + (c / τ) • y

/-- Pair-valued dial path. -/
noncomputable def dialProbe {d : Nat} (p : ProbePair d) (c : ℝ)
    (y : Fin d -> ℝ) (τ : ℝ) : ProbePair d :=
  (dialW p c y τ, dialV p c y τ)

/-- Dot product against a matrix-vector product can be transposed to the other vector. -/
theorem dotProduct_mulVec_eq_dotProduct_transpose_mulVec {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (w y : Fin d -> ℝ) :
    w ⬝ᵥ A *ᵥ y = y ⬝ᵥ Aᵀ *ᵥ w := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, transpose_apply]
  rw [Finset.sum_comm]
  simp only [mul_left_comm, mul_comm]

/-- Choose a normalized direction for a nonzero finite vector. -/
noncomputable def normalizedDirectionOfNonzero {d : Nat}
    (q : Fin d -> ℝ) (hq : q ≠ 0) :
    { y : Fin d -> ℝ // y ⬝ᵥ q = 1 } := by
  classical
  have hexists : ∃ i : Fin d, q i ≠ 0 := by
    by_contra h
    apply hq
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  let i := Classical.choose hexists
  have hi : q i ≠ 0 := Classical.choose_spec hexists
  refine ⟨Pi.single i (q i)⁻¹, ?_⟩
  rw [single_dotProduct]
  exact inv_mul_cancel₀ hi

/-- Algebraic identity behind the packaged first-layer dial path. -/
theorem dial_first_gate_argument_identity {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (p : ProbePair d) (b c : ℝ)
    (y : Fin d -> ℝ)
    (hquad : firstLayerQuadric A p)
    (hnorm : y ⬝ᵥ firstLayerPi A p = 1) :
    ∀ τ : ℝ, τ ≠ 0 ->
      τ * matrixBilin A (dialW p c y τ) (dialV p c y τ) + b =
        c + b - c ^ 2 * matrixBilin A y y / τ := by
  intro τ hτ
  have hquad0 : p.1 ⬝ᵥ A *ᵥ p.2 = 0 := by
    simpa [firstLayerQuadric, matrixBilin] using hquad
  have htranspose : p.1 ⬝ᵥ A *ᵥ y = y ⬝ᵥ Aᵀ *ᵥ p.1 :=
    dotProduct_mulVec_eq_dotProduct_transpose_mulVec A p.1 y
  have hlinear : p.1 ⬝ᵥ A *ᵥ y - y ⬝ᵥ A *ᵥ p.2 = 1 := by
    rw [htranspose]
    simpa [firstLayerPi, sub_dotProduct] using hnorm
  simp only [matrixBilin, dialW, dialV, Matrix.mulVec_add, Matrix.mulVec_smul,
    dotProduct_add, sub_dotProduct, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [hquad0]
  field_simp [hτ]
  linear_combination τ * c * hlinear

/-- Constructor-friendly package for the exact dial identity.

The field `c_targets_t` records the role of `c` as `logit(t)-b` without committing this
file to a particular `logit` definition. -/
structure DialPathData {d : Nat} (A : Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ) where
  base : ProbePair d
  t : ℝ
  t_pos : 0 < t
  t_lt_one : t < 1
  c : ℝ
  y : Fin d -> ℝ
  base_on_quadric : firstLayerQuadric A base
  direction_normalized : y ⬝ᵥ firstLayerPi A base = 1
  c_targets_t : sig (c + b) = t
  exact_identity :
    ∀ τ : ℝ, τ ≠ 0 ->
      τ * matrixBilin A (dialW base c y τ) (dialV base c y τ) + b =
        c + b - c ^ 2 * matrixBilin A y y / τ

namespace DialPathData

variable {d : Nat} {A : Matrix (Fin d) (Fin d) ℝ} {b : ℝ}

/-- Pair-valued path associated to packaged dial data. -/
noncomputable def probe (D : DialPathData A b) (τ : ℝ) : ProbePair d :=
  dialProbe D.base D.c D.y τ

/-- Canonical dial path through a regular point of the first-layer quadric and a
target first-gate value `t ∈ (0, 1)`. -/
noncomputable def ofRegularQuadric
    (A : Matrix (Fin d) (Fin d) ℝ) (b : ℝ)
    (p : ProbePair d) (t : ℝ)
    (hquad : firstLayerQuadric A p)
    (hregular : firstLayerRegular A p)
    (ht_pos : 0 < t) (ht_lt_one : t < 1) :
    DialPathData A b :=
  let yData := normalizedDirectionOfNonzero (firstLayerPi A p) hregular.2.2
  { base := p
    t := t
    t_pos := ht_pos
    t_lt_one := ht_lt_one
    c := sigmoidLogit t - b
    y := yData.1
    base_on_quadric := hquad
    direction_normalized := yData.2
    c_targets_t := by
      simpa [sigmoidLogit] using sig_sigmoidLogit ht_pos ht_lt_one
    exact_identity :=
      dial_first_gate_argument_identity A p b (sigmoidLogit t - b) yData.1
        hquad yData.2 }

end DialPathData

/-! ## Sign region, cascade, and trichotomy interfaces -/

/-- Product patch supplied by the sign-region construction for the matching argument.

The usual topological product data is bundled with the Step 4 coefficient-separation
property used by TeX Proposition `matching`.  The separation field is intentionally
explicit: it is the quadric-richness content of the chosen relatively open patch, not a
consequence of mere nonemptiness, openness of `J`, and membership in the quadric. -/
structure CoefficientSeparatingProductPatch {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (U0 : Set (ProbePair d × ℝ)) where
  Uq : Set (ProbePair d)
  J : Set ℝ
  Uq_nonempty : Uq.Nonempty
  J_nonempty : J.Nonempty
  J_open : IsOpen J
  Uq_on_quadric : ∀ p ∈ Uq, firstLayerQuadric A p
  product_subset :
    {x : ProbePair d × ℝ | x.1 ∈ Uq ∧ x.2 ∈ J} ⊆ U0
  quadratic_coefficient_separation :
    QuadricProbeSliceQuadraticCoefficientSeparation A Uq
  coefficient_separation :
    ∀ (M : Matrix (Fin d) (Fin d) ℝ)
      (R : ℝ -> Matrix (Fin d) (Fin d) ℝ),
      (∀ p : ProbePair d, p ∈ Uq -> ∀ t : ℝ, t ∈ J ->
        Matrix.mulVec M p.2 + Matrix.mulVec (R t) p.1 = 0) ->
        (∀ v : Fin d -> ℝ, Matrix.mulVec M v = 0) ∧
          (∀ t : ℝ, t ∈ J -> R t = 0)

/-- The sign-region output from Lemma `region`.

The product-neighborhood field is intentionally stated as a constructor obligation over
sets of `(probe,t)` pairs.  Its output includes the quadric coefficient-separation
property used in matching Step 4. -/
structure SignRegionData {L d : Nat} (θ' : Params L d)
    (O : Set (ProbePair d)) (A : Matrix (Fin d) (Fin d) ℝ) (b : ℝ) where
  U : Set (ProbePair d × ℝ)
  nonempty : U.Nonempty
  relatively_open :
    ∃ W : Set (ProbePair d × ℝ),
      IsOpen W ∧
        U = W ∩ {x | firstLayerQuadric A x.1 ∧ 0 < x.2 ∧ x.2 < 1}
  connected : IsPreconnected U
  point_on_quadric : ∀ x ∈ U, firstLayerQuadric A x.1
  point_regular : ∀ x ∈ U, firstLayerRegular A x.1
  point_mem_base : ∀ x ∈ U, x.1 ∈ O
  primed_positive :
    ∀ x ∈ U, ∀ n : Nat, 1 ≤ n -> n < L ->
      0 < (specializedPhi θ' n (gateAssignmentOneTail x.2) x.1).re
  product_neighborhood :
    ∀ U0 : Set (ProbePair d × ℝ), U0 ⊆ U -> U0.Nonempty ->
      (∃ W0 : Set (ProbePair d × ℝ), IsOpen W0 ∧ U0 = W0 ∩ U) ->
      CoefficientSeparatingProductPatch A U0

namespace SignRegionData

variable {L d : Nat} {θ' : Params L d} {O : Set (ProbePair d)}
variable {A : Matrix (Fin d) (Fin d) ℝ} {b : ℝ}

theorem t_pos (S : SignRegionData θ' O A b) {x : ProbePair d × ℝ}
    (hx : x ∈ S.U) : 0 < x.2 := by
  rcases S.relatively_open with ⟨W, _hW, hU⟩
  have hx' : x ∈ W ∩ {x | firstLayerQuadric A x.1 ∧ 0 < x.2 ∧ x.2 < 1} := by
    simpa [hU] using hx
  exact hx'.2.2.1

theorem t_lt_one (S : SignRegionData θ' O A b) {x : ProbePair d × ℝ}
    (hx : x ∈ S.U) : x.2 < 1 := by
  rcases S.relatively_open with ⟨W, _hW, hU⟩
  have hx' : x ∈ W ∩ {x | firstLayerQuadric A x.1 ∧ 0 < x.2 ∧ x.2 < 1} := by
    simpa [hU] using hx
  exact hx'.2.2.2

theorem pi_ne_zero (S : SignRegionData θ' O A b) {x : ProbePair d × ℝ}
    (hx : x ∈ S.U) : firstLayerPi A x.1 ≠ 0 :=
  (S.point_regular x hx).2.2

end SignRegionData

/-- Exponential convergence package for saturated gates along a dial path. -/
structure EventuallyExpClose (f : ℝ -> ℝ) (a : ℝ) where
  rate : ℝ
  rate_pos : 0 < rate
  coeff : ℝ
  coeff_nonneg : 0 ≤ coeff
  start : ℝ
  bound : ∀ τ : ℝ, start ≤ τ -> |f τ - a| ≤ coeff * Real.exp (-rate * τ)

namespace EventuallyExpClose

/-- A constant path is exponentially close to its value. -/
def refl (a : ℝ) : EventuallyExpClose (fun _ : ℝ => a) a := by
  refine ⟨1, by norm_num, 0, by norm_num, 0, ?_⟩
  intro τ _hτ
  simp

end EventuallyExpClose

/-- Gate values along a dial path, indexed by zero-based formal level. -/
abbrev GateAlongBase (d : Nat) :=
  Nat -> ProbePair d × ℝ -> ℝ -> ℝ

/-- The three possible unprimed saturation constants in Proposition `trichotomy`. -/
def IsTrichotomyConstant (b : ℝ) (a : ℝ) : Prop :=
  a = 0 ∨ a = 1 ∨ a = sig b

/-- The curve-rigidity output of the zero branch in Lemma `cascade`.

`level` is zero-based: TeX level `ell` corresponds to `level = ell - 1`, and the
specialized first gate is the free variable `z`. -/
structure CascadeCurveRigidityData {L d : Nat} (θ : Params L d)
    (A : Matrix (Fin d) (Fin d) ℝ) (level : Nat) (tail : Nat -> ℝ) where
  gamma : ℂ -> ℂ
  gamma_affine : ∃ gamma0 gamma1 : ℂ, ∀ z : ℂ, gamma z = gamma0 + gamma1 * z
  curve_identity :
    ∀ (z : ℂ) (p : ProbePair d),
      specializedPhi θ level (complexGateAssignmentOfTail z tail) p =
        gamma z * (matrixBilin A p.1 p.2 : ℂ)

/-- Constructor-friendly statement of one cascade step.

The analytic estimates and the quadric rigidity upgrade are fields, so later work can
prove them independently while downstream trichotomy code consumes one stable shape. -/
structure CascadeStepData {L d : Nat} (θ : Params L d)
    (A : Matrix (Fin d) (Fin d) ℝ) (U0 : Set (ProbePair d × ℝ))
    (level : Nat) (tail : Nat -> ℝ) (gate : GateAlongBase d) where
  level_pos : 1 ≤ level
  level_lt_depth : level < L
  prior_saturates :
    ∀ x ∈ U0, ∀ n : Nat, 1 ≤ n -> n < level ->
      EventuallyExpClose (fun τ => gate n x τ) (tail (n - 1))
  limit_slope : ProbePair d × ℝ -> ℂ
  limit_slope_eq :
    ∀ x ∈ U0,
      limit_slope x = specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1
  gate_saturates_of_nonzero :
    ∀ x ∈ U0, limit_slope x ≠ 0 ->
      EventuallyExpClose (fun τ => gate level x τ)
        (if 0 < (limit_slope x).re then 1 else 0)
  zero_branch :
    (∀ x ∈ U0, limit_slope x = 0) ->
      CascadeCurveRigidityData θ A level tail

/-- Trichotomy package from Proposition `trichotomy`.

The constants are indexed by zero-based formal level, so `varsigma 1` is the TeX
constant `varsigma_2`. -/
structure TrichotomyData {L d : Nat} (b : ℝ)
    (signU Ustar : Set (ProbePair d × ℝ))
    (unprimed primed : GateAlongBase d) where
  subset_sign_region : Ustar ⊆ signU
  nonempty : Ustar.Nonempty
  relatively_open_in_sign_region :
    ∃ W : Set (ProbePair d × ℝ), IsOpen W ∧ Ustar = W ∩ signU
  connected : IsPreconnected Ustar
  varsigma : Nat -> ℝ
  varsigma_mem :
    ∀ n : Nat, 1 ≤ n -> n < L -> IsTrichotomyConstant b (varsigma n)
  unprimed_saturates :
    ∀ x ∈ Ustar, ∀ n : Nat, 1 ≤ n -> n < L ->
      EventuallyExpClose (fun τ => unprimed n x τ) (varsigma n)
  primed_saturates_one :
    ∀ x ∈ Ustar, ∀ n : Nat, 1 ≤ n -> n < L ->
      EventuallyExpClose (fun τ => primed n x τ) 1

/-! ## Matching and `K = I` extraction -/

/-- Product of real skip matrices `B_n ... B_1`, zero-based in the layer stream. -/
noncomputable def realSkipBprod {d : Nat} (θ : LayerStream d) :
    Nat -> Matrix (Fin d) (Fin d) ℝ
  | 0 => 1
  | n + 1 => skipB (θ n).1 * realSkipBprod θ n

@[simp]
theorem realSkipBprod_zero {d : Nat} (θ : LayerStream d) :
    realSkipBprod θ 0 = 1 := rfl

@[simp]
theorem realSkipBprod_succ {d : Nat} (θ : LayerStream d) (n : Nat) :
    realSkipBprod θ (n + 1) = skipB (θ n).1 * realSkipBprod θ n := rfl

/-- Skip matrices satisfy `B - V = I`. -/
theorem skipB_sub_value {d : Nat} (V : Matrix (Fin d) (Fin d) ℝ) :
    skipB V - V = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [skipB, Matrix.one_apply_eq]
  · simp [skipB, Matrix.one_apply_ne hij]

/-- Algebraic data at the end of matching Step 6. -/
structure KExtractionData {d : Nat}
    (V V' B B' : Matrix (Fin d) (Fin d) ℝ) where
  K : Matrix (Fin d) (Fin d) ℝ
  skip_unprimed : B - V = 1
  skip_primed : B' - V' = 1
  maps_value : K * V = V'
  maps_skip : K * B = B'

namespace KExtractionData

variable {d : Nat} {V V' B B' : Matrix (Fin d) (Fin d) ℝ}

/-- The cancellation step in Proposition `matching`: if `K` maps both `V` and `B` to
their primed counterparts and both sides satisfy `B - V = I`, then `K = I`. -/
theorem K_eq_one (D : KExtractionData V V' B B') : D.K = 1 := by
  calc
    D.K = D.K * 1 := by rw [mul_one]
    _ = D.K * (B - V) := by rw [D.skip_unprimed]
    _ = D.K * B - D.K * V := by rw [Matrix.mul_sub]
    _ = B' - V' := by rw [D.maps_skip, D.maps_value]
    _ = 1 := D.skip_primed

/-- The same cancellation identifies the first value matrices. -/
theorem value_eq (D : KExtractionData V V' B B') : V = V' := by
  calc
    V = (1 : Matrix (Fin d) (Fin d) ℝ) * V := by rw [one_mul]
    _ = D.K * V := by rw [D.K_eq_one]
    _ = V' := D.maps_value

/-- The same cancellation identifies the first skip matrices. -/
theorem skip_eq (D : KExtractionData V V' B B') : B = B' := by
  calc
    B = (1 : Matrix (Fin d) (Fin d) ℝ) * B := by rw [one_mul]
    _ = D.K * B := by rw [D.K_eq_one]
    _ = B' := D.maps_skip

end KExtractionData

/-- Output package of Proposition `matching` for the first layer. -/
structure FirstLayerMatchingData {L d : Nat}
    (θ θ' : Params (L + 1) d) : Prop where
  skipProduct_eq :
    realSkipBprod (paramStream θ) (L + 1) =
      realSkipBprod (paramStream θ') (L + 1)
  headSkip_eq : skipB (θ 0).1 = skipB (θ' 0).1
  headValue_eq : (θ 0).1 = (θ' 0).1

namespace FirstLayerMatchingData

variable {L d : Nat} {θ θ' : Params (L + 1) d}

/-- Combine matching with the Step 1 endpoint to identify the whole first layer. -/
theorem headLayer_eq
    (D : FirstLayerMatchingData θ θ')
    {targetValue : Matrix (Fin d) (Fin d) ℝ}
    (E : FirstLayerEndpointData (firstAttention θ) (firstAttention θ') targetValue) :
    θ 0 = θ' 0 :=
  Prod.ext D.headValue_eq E.headAttention_eq

/-- Constructor from the `K = I` extraction data produced by the coefficient comparison
in the matching proof. -/
def ofKExtraction
    (skipProduct_eq :
      realSkipBprod (paramStream θ) (L + 1) =
        realSkipBprod (paramStream θ') (L + 1))
    (D : KExtractionData (θ 0).1 (θ' 0).1 (skipB (θ 0).1) (skipB (θ' 0).1)) :
    FirstLayerMatchingData θ θ' where
  skipProduct_eq := skipProduct_eq
  headSkip_eq := D.skip_eq
  headValue_eq := D.value_eq

end FirstLayerMatchingData

/-- Limit and coefficient-comparison output immediately before `K = I`. -/
structure MatchingLimitData {L d : Nat} (θ θ' : Params (L + 1) d) where
  skipProduct_eq :
    realSkipBprod (paramStream θ) (L + 1) =
      realSkipBprod (paramStream θ') (L + 1)
  K : Matrix (Fin d) (Fin d) ℝ
  K_maps_headValue : K * (θ 0).1 = (θ' 0).1
  K_maps_headSkip : K * skipB (θ 0).1 = skipB (θ' 0).1

namespace MatchingLimitData

variable {L d : Nat} {θ θ' : Params (L + 1) d}

/-- Convert the coefficient-comparison endpoint into the abstract `K` extraction data. -/
def toKExtractionData (D : MatchingLimitData θ θ') :
    KExtractionData (θ 0).1 (θ' 0).1 (skipB (θ 0).1) (skipB (θ' 0).1) where
  K := D.K
  skip_unprimed := skipB_sub_value (θ 0).1
  skip_primed := skipB_sub_value (θ' 0).1
  maps_value := D.K_maps_headValue
  maps_skip := D.K_maps_headSkip

/-- Compile limit/coefficient data to the first-layer matching package. -/
def toFirstLayerMatchingData (D : MatchingLimitData θ θ') :
    FirstLayerMatchingData θ θ' :=
  FirstLayerMatchingData.ofKExtraction D.skipProduct_eq D.toKExtractionData

end MatchingLimitData

end TransformerIdentifiability.NLayer
