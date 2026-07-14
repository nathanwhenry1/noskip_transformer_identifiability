import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Probe
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.SharedToolbox
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Genericity.Regularity

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.NoSkip

/-!
# No-skip depth-one probe formula

At depth one, the recursively computed probe output is a constant vector
`C₁ v` plus a finite sigmoid mixture.  In the no-skip model,
`C₁ = ∑ a, V₁ₐ`; there is no identity summand in this constant.

This file currently contains only the formula and source/target conversion API
needed by aggregate recovery.  Separation and recovery hypotheses belong to
the later base-case packets.
-/

noncomputable section

/-- First-layer attention matrices of a depth-one no-skip parameter. -/
def baseAttention {k d : Nat} (θ : Params 1 k d) :
    Fin k → Matrix (Fin d) (Fin d) ℝ :=
  fun a => attentionMatrix θ 0 a

/-- First-layer value matrices of a depth-one no-skip parameter. -/
def baseValue {k d : Nat} (θ : Params 1 k d) :
    Fin k → Matrix (Fin d) (Fin d) ℝ :=
  fun a => valueMatrix θ 0 a

/-- The depth-one probe slope `qₐ(w,v) = wᵀ A₁ₐ v`. -/
def baseSlope {k d : Nat} (θ : Params 1 k d) (w v : Vec d) :
    Fin k → ℝ :=
  fun a => matrixBilin (baseAttention θ a) w v

/-- The entire real constant `C₁ v` in the depth-one probe formula. -/
def baseConstant {k d : Nat} (θ : Params 1 k d) (v : Vec d) : Vec d :=
  collapseMatrix θ 0 *ᵥ v

/-- In the no-skip model the base constant is `(∑ₐ V₁ₐ) v`. -/
theorem baseConstant_eq_value_sum {k d : Nat} (θ : Params 1 k d) (v : Vec d) :
    baseConstant θ v = (∑ a : Fin k, baseValue θ a) *ᵥ v := by
  simp [baseConstant, baseValue, collapseMatrix, valueSum]

/-- Complexified depth-one coefficient `V₁ₐ w`. -/
def baseCoeffC {k d : Nat} (θ : Params 1 k d) (w : Vec d) :
    Fin k → Fin d → ℂ :=
  fun a i => ((baseValue θ a *ᵥ w) i : ℂ)

/-- Complexification of the entire constant `C₁ v`. -/
def baseEntirePartC {k d : Nat} (θ : Params 1 k d) (v : Vec d) :
    Fin d → ℂ :=
  fun i => ((baseConstant θ v i : ℝ) : ℂ)

/-- The depth-one no-skip complex probe formula as a constant entire part plus
a finite sigmoid mixture. -/
def baseProbeMixtureC {k d : Nat} (r : Nat) (θ : Params 1 k d)
    (w v : Vec d) : ℂ → Fin d → ℂ :=
  constantSigmoidMixture (logScale r) (baseEntirePartC θ v)
    (baseCoeffC θ w) (baseSlope θ w v)

@[simp] theorem baseProbeMixtureC_apply {k d : Nat} (r : Nat)
    (θ : Params 1 k d) (w v : Vec d) (τ : ℂ) (i : Fin d) :
    baseProbeMixtureC r θ w v τ i =
      ((baseConstant θ v i : ℝ) : ℂ) +
        ∑ a : Fin k,
          csig (((baseSlope θ w v a : ℝ) : ℂ) * τ + (logScale r : ℂ)) *
            ((baseValue θ a *ᵥ w) i : ℂ) := by
  simp [baseProbeMixtureC, baseEntirePartC, baseCoeffC, baseConstant,
    constantSigmoidMixture, sigmoidMixture, KHead.sigmoidMixture]

/-- The TeX bias `b = log r` is nonzero under the standing base-case
assumption `1 < r`. -/
theorem logScale_ne_zero_of_one_lt {r : Nat} (hr : 1 < r) :
    logScale r ≠ 0 :=
  ne_of_gt (Real.log_pos (by exact_mod_cast hr))

/-- The closed depth-one recursion is exactly
`C₁ v + ∑ₐ σ(τ qₐ(w,v) + log r) V₁ₐ w`.

No sign condition on `τ` is needed for this closed recursion identity. -/
theorem probeOutput_depth_one {k d r : Nat} (θ : Params 1 k d)
    (w v : Vec d) (τ : ℝ) :
    probeOutput r θ w v τ =
      baseConstant θ v +
        ∑ a : Fin k,
          headGate r (baseAttention θ a) w v τ • (baseValue θ a *ᵥ w) := by
  simp [probeOutput, baseConstant, gatedValueSum_mulVec, layerGates,
    baseAttention, baseValue]

/-- The normalized depth-one transformer observable has the same explicit
formula at positive probe time. -/
theorem probeObservable_depth_one {k d r : Nat} (hr : 0 < r)
    (θ : Params 1 k d) (w v : Vec d) (τ : ℝ) (hτ : 0 < τ) :
    probeObservable r θ w v τ =
      baseConstant θ v +
        ∑ a : Fin k,
          headGate r (baseAttention θ a) w v τ • (baseValue θ a *ᵥ w) := by
  rw [probeObservable_eq_probeOutput hr θ w v τ hτ]
  exact probeOutput_depth_one θ w v τ

/-- Source/target form of the two real depth-one equations used by the base
case. -/
theorem probeObservable_depth_one_pair {k d r : Nat} (hr : 0 < r)
    (θ θ' : Params 1 k d) (w v : Vec d) (τ : ℝ) (hτ : 0 < τ) :
    (probeObservable r θ w v τ =
      baseConstant θ v +
        ∑ a : Fin k,
          headGate r (baseAttention θ a) w v τ • (baseValue θ a *ᵥ w)) ∧
    (probeObservable r θ' w v τ =
      baseConstant θ' v +
        ∑ h : Fin k,
          headGate r (baseAttention θ' h) w v τ • (baseValue θ' h *ᵥ w)) :=
  ⟨probeObservable_depth_one hr θ w v τ hτ,
    probeObservable_depth_one hr θ' w v τ hτ⟩

/-- On real probe times, the complex mixture is the coordinatewise
complexification of the closed depth-one recursion. -/
theorem baseProbeMixtureC_ofReal_eq_probeOutput {k d r : Nat}
    (θ : Params 1 k d) (w v : Vec d) (τ : ℝ) :
    baseProbeMixtureC r θ w v (τ : ℂ) =
      fun i : Fin d => ((probeOutput r θ w v τ i : ℝ) : ℂ) := by
  ext i
  have hsig : ∀ a : Fin k,
      csig ((τ : ℂ) * (baseSlope θ w v a : ℂ) + Complex.log (r : ℂ)) =
        ((headGate r (baseAttention θ a) w v τ : ℝ) : ℂ) := by
    intro a
    rw [← Complex.natCast_log (n := r)]
    change csig ((τ : ℂ) * (baseSlope θ w v a : ℂ) + (logScale r : ℂ)) =
      ((sig (τ * matrixBilin (baseAttention θ a) w v + logScale r) : ℝ) : ℂ)
    rw [← TransformerIdentifiability.NLayer.csig_ofReal
      (τ * matrixBilin (baseAttention θ a) w v + logScale r)]
    congr 1
    simp [baseSlope]
  simp [baseProbeMixtureC_apply, probeOutput_depth_one, hsig, baseConstant,
    baseAttention, baseValue, mul_comm]

/-- Positive-real equality of closed source and target probe outputs gives
positive-real equality of their complex mixture formulas. -/
theorem baseProbeMixtureC_positive_real_eq_of_probeOutput_eq {k d r : Nat}
    {θ θ' : Params 1 k d} {w v : Vec d}
    (hEq : ∀ τ : ℝ, 0 < τ →
      probeOutput r θ w v τ = probeOutput r θ' w v τ) :
    ∀ τ : ℝ, 0 < τ →
      baseProbeMixtureC r θ w v (τ : ℂ) =
        baseProbeMixtureC r θ' w v (τ : ℂ) := by
  intro τ hτ
  calc
    baseProbeMixtureC r θ w v (τ : ℂ) =
        (fun i : Fin d => ((probeOutput r θ w v τ i : ℝ) : ℂ)) :=
      baseProbeMixtureC_ofReal_eq_probeOutput θ w v τ
    _ = (fun i : Fin d => ((probeOutput r θ' w v τ i : ℝ) : ℂ)) := by
      ext i
      exact congrArg (fun y : Vec d => ((y i : ℝ) : ℂ)) (hEq τ hτ)
    _ = baseProbeMixtureC r θ' w v (τ : ℂ) :=
      (baseProbeMixtureC_ofReal_eq_probeOutput θ' w v τ).symm

/-- Observable-level source/target equality compiles directly to the complex
mixture equality expected by aggregate recovery. -/
theorem baseProbeMixtureC_positive_real_eq_of_probeObservable_eq {k d r : Nat}
    (hr : 0 < r) {θ θ' : Params 1 k d} {w v : Vec d}
    (hEq : ∀ τ : ℝ, 0 < τ →
      probeObservable r θ w v τ = probeObservable r θ' w v τ) :
    ∀ τ : ℝ, 0 < τ →
      baseProbeMixtureC r θ w v (τ : ℂ) =
        baseProbeMixtureC r θ' w v (τ : ℂ) := by
  apply baseProbeMixtureC_positive_real_eq_of_probeOutput_eq
  intro τ hτ
  rw [← probeObservable_eq_probeOutput hr θ w v τ hτ,
    ← probeObservable_eq_probeOutput hr θ' w v τ hτ]
  exact hEq τ hτ

/-! ## Separated-probe polynomial -/

/-- A depth-one probe is separated when all slopes are nonzero and distinct and
every value matrix acts nontrivially on `w`. -/
structure BaseSeparatedProbe {k d : Nat} (θ : Params 1 k d)
    (w v : Vec d) : Prop where
  slope_ne_zero : ∀ a : Fin k, baseSlope θ w v a ≠ 0
  slope_injective : Function.Injective (baseSlope θ w v)
  value_action_ne_zero : ∀ a : Fin k, baseValue θ a *ᵥ w ≠ 0

/-- Probe-coordinate variables: the left block is `w`, the right block is `v`. -/
abbrev BaseProbeVar (d : Nat) := Sum (Fin d) (Fin d)

/-- Polynomial ring in a depth-one probe pair `(w,v)`. -/
abbrev BaseProbePoly (d : Nat) := MvPolynomial (BaseProbeVar d) ℝ

noncomputable def baseProbeW {d : Nat} (i : Fin d) : BaseProbePoly d :=
  MvPolynomial.X (Sum.inl i)

noncomputable def baseProbeV {d : Nat} (i : Fin d) : BaseProbePoly d :=
  MvPolynomial.X (Sum.inr i)

/-- Evaluation of probe-coordinate polynomials at `(w,v)`. -/
def baseProbeEval {d : Nat} (w v : Vec d) : BaseProbeVar d → ℝ
  | Sum.inl i => w i
  | Sum.inr i => v i

@[simp] theorem eval_baseProbeW {d : Nat} (w v : Vec d) (i : Fin d) :
    MvPolynomial.eval (baseProbeEval w v) (baseProbeW i) = w i := by
  simp [baseProbeEval, baseProbeW]

@[simp] theorem eval_baseProbeV {d : Nat} (w v : Vec d) (i : Fin d) :
    MvPolynomial.eval (baseProbeEval w v) (baseProbeV i) = v i := by
  simp [baseProbeEval, baseProbeV]

/-- Polynomial encoding of the bilinear form `wᵀAv`. -/
noncomputable def baseBilinPoly {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) : BaseProbePoly d :=
  ∑ i : Fin d, ∑ j : Fin d,
    MvPolynomial.C (A i j) * baseProbeW i * baseProbeV j

@[simp] theorem eval_baseBilinPoly {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (w v : Vec d) :
    MvPolynomial.eval (baseProbeEval w v) (baseBilinPoly A) =
      matrixBilin A w v := by
  simp only [baseBilinPoly, MvPolynomial.eval_sum, MvPolynomial.eval_mul,
    MvPolynomial.eval_C, eval_baseProbeW, eval_baseProbeV]
  rw [matrixBilin]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  ring

/-- Polynomial vector encoding `Vw`. -/
noncomputable def baseValueActionPoly {d : Nat}
    (V : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) : BaseProbePoly d :=
  ∑ j : Fin d, MvPolynomial.C (V i j) * baseProbeW j

@[simp] theorem eval_baseValueActionPoly {d : Nat}
    (V : Matrix (Fin d) (Fin d) ℝ) (w v : Vec d) (i : Fin d) :
    MvPolynomial.eval (baseProbeEval w v) (baseValueActionPoly V i) =
      (V *ᵥ w) i := by
  simp [baseValueActionPoly, Matrix.mulVec, dotProduct]

/-- Squared Euclidean norm polynomial of `Vw`. -/
noncomputable def baseValueActionSqPoly {d : Nat}
    (V : Matrix (Fin d) (Fin d) ℝ) : BaseProbePoly d :=
  ∑ i : Fin d, baseValueActionPoly V i * baseValueActionPoly V i

@[simp] theorem eval_baseValueActionSqPoly {d : Nat}
    (V : Matrix (Fin d) (Fin d) ℝ) (w v : Vec d) :
    MvPolynomial.eval (baseProbeEval w v) (baseValueActionSqPoly V) =
      ∑ i : Fin d, (V *ᵥ w) i * (V *ᵥ w) i := by
  simp [baseValueActionSqPoly]

/-- Strictly ordered head pairs, matching the TeX product over `a<c`. -/
abbrev BaseOrderedHeadPair (k : Nat) :=
  {ac : Fin k × Fin k // ac.1 < ac.2}

/-- The finite factor family in the base separated-probe polynomial. -/
inductive BaseSeparationFactorIndex (k : Nat)
  | slope (a : Fin k)
  | slopeDifference (ac : BaseOrderedHeadPair k)
  | valueAction (a : Fin k)
  deriving DecidableEq, Fintype

/-- A slope, pairwise slope-difference, or squared value-action factor. -/
noncomputable def baseSeparationFactorPoly {k d : Nat} (θ : Params 1 k d) :
    BaseSeparationFactorIndex k → BaseProbePoly d
  | .slope a => baseBilinPoly (baseAttention θ a)
  | .slopeDifference ac =>
      baseBilinPoly (baseAttention θ ac.1.1 - baseAttention θ ac.1.2)
  | .valueAction a => baseValueActionSqPoly (baseValue θ a)

/-- The single finite product polynomial cutting out all failures of depth-one
probe separation. -/
noncomputable def baseSeparationPoly {k d : Nat} (θ : Params 1 k d) :
    BaseProbePoly d :=
  ∏ idx : BaseSeparationFactorIndex k, baseSeparationFactorPoly θ idx

@[simp] theorem eval_baseSeparationFactorPoly {k d : Nat}
    (θ : Params 1 k d) (w v : Vec d) (idx : BaseSeparationFactorIndex k) :
    MvPolynomial.eval (baseProbeEval w v) (baseSeparationFactorPoly θ idx) =
      match idx with
      | .slope a => baseSlope θ w v a
      | .slopeDifference ac =>
          baseSlope θ w v ac.1.1 - baseSlope θ w v ac.1.2
      | .valueAction a =>
          ∑ i : Fin d,
            (baseValue θ a *ᵥ w) i * (baseValue θ a *ᵥ w) i := by
  cases idx with
  | slope a => simp [baseSeparationFactorPoly, baseSlope]
  | slopeDifference ac =>
      simp only [baseSeparationFactorPoly, eval_baseBilinPoly]
      simpa [baseSlope] using
        (TransformerIdentifiability.NLayer.matrixBilin_sub
          (baseAttention θ ac.1.1) (baseAttention θ ac.1.2) w v)
  | valueAction a => simp [baseSeparationFactorPoly]

@[simp] theorem eval_baseSeparationPoly {k d : Nat}
    (θ : Params 1 k d) (w v : Vec d) :
    MvPolynomial.eval (baseProbeEval w v) (baseSeparationPoly θ) =
      ∏ idx : BaseSeparationFactorIndex k,
        MvPolynomial.eval (baseProbeEval w v)
          (baseSeparationFactorPoly θ idx) := by
  simp [baseSeparationPoly]

theorem sum_mul_self_ne_zero_iff {d : Nat} (x : Vec d) :
    (∑ i : Fin d, x i * x i) ≠ 0 ↔ x ≠ 0 := by
  constructor
  · intro hsum hzero
    subst x
    simp at hsum
  · intro hx hsum
    apply hx
    funext i
    have hi :=
      ((Finset.sum_eq_zero_iff_of_nonneg
        (fun j _hj => mul_self_nonneg (x j))).mp hsum) i (Finset.mem_univ i)
    exact mul_self_eq_zero.mp hi

/-- Pointwise nonvanishing of the product polynomial is exactly probe
separation.  This is the algebraic interface used by the later topology step. -/
theorem eval_baseSeparationPoly_ne_zero_iff {k d : Nat}
    (θ : Params 1 k d) (w v : Vec d) :
    MvPolynomial.eval (baseProbeEval w v) (baseSeparationPoly θ) ≠ 0 ↔
      BaseSeparatedProbe θ w v := by
  rw [eval_baseSeparationPoly]
  constructor
  · intro hprod
    have hall : ∀ idx : BaseSeparationFactorIndex k,
        MvPolynomial.eval (baseProbeEval w v)
          (baseSeparationFactorPoly θ idx) ≠ 0 := by
      intro idx
      exact (Finset.prod_ne_zero_iff.mp hprod) idx (Finset.mem_univ idx)
    refine ⟨?_, ?_, ?_⟩
    · intro a
      simpa using hall (.slope a)
    · intro a c heq
      by_contra hne
      rcases lt_or_gt_of_ne hne with hac | hca
      · have hf := hall (.slopeDifference ⟨(a, c), hac⟩)
        rw [eval_baseSeparationFactorPoly] at hf
        exact hf (sub_eq_zero.mpr heq)
      · have hf := hall (.slopeDifference ⟨(c, a), hca⟩)
        rw [eval_baseSeparationFactorPoly] at hf
        exact hf (sub_eq_zero.mpr heq.symm)
    · intro a
      have hf := hall (.valueAction a)
      rw [eval_baseSeparationFactorPoly] at hf
      exact (sum_mul_self_ne_zero_iff (baseValue θ a *ᵥ w)).mp hf
  · intro hsep
    apply Finset.prod_ne_zero_iff.mpr
    intro idx _hidx
    cases idx with
    | slope a =>
        simpa using hsep.slope_ne_zero a
    | slopeDifference ac =>
        rw [eval_baseSeparationFactorPoly]
        apply sub_ne_zero.mpr
        intro heq
        exact (ne_of_lt ac.2) (hsep.slope_injective heq)
    | valueAction a =>
        rw [eval_baseSeparationFactorPoly]
        exact (sum_mul_self_ne_zero_iff (baseValue θ a *ᵥ w)).mpr
          (hsep.value_action_ne_zero a)

theorem baseBilinPoly_ne_zero_of_matrix_ne_zero {d : Nat}
    {A : Matrix (Fin d) (Fin d) ℝ} (hA : A ≠ 0) :
    baseBilinPoly A ≠ 0 := by
  classical
  have hex : ∃ i j : Fin d, A i j ≠ 0 := by
    by_contra h
    apply hA
    ext i j
    by_contra hij
    exact h ⟨i, j, hij⟩
  obtain ⟨i, j, hij⟩ := hex
  let w : Vec d := fun x => if x = i then 1 else 0
  let v : Vec d := fun x => if x = j then 1 else 0
  apply mvPolynomial_ne_zero_of_eval_ne_zero
    (baseBilinPoly A) (baseProbeEval w v)
  rw [eval_baseBilinPoly]
  simpa [w, v, matrixBilin, Matrix.mulVec, dotProduct] using hij

theorem baseValueActionSqPoly_ne_zero_of_matrix_ne_zero {d : Nat}
    {V : Matrix (Fin d) (Fin d) ℝ} (hV : V ≠ 0) :
    baseValueActionSqPoly V ≠ 0 := by
  classical
  have hex : ∃ i j : Fin d, V i j ≠ 0 := by
    by_contra h
    apply hV
    ext i j
    by_contra hij
    exact h ⟨i, j, hij⟩
  obtain ⟨i, j, hij⟩ := hex
  let w : Vec d := fun x => if x = j then 1 else 0
  apply mvPolynomial_ne_zero_of_eval_ne_zero
    (baseValueActionSqPoly V) (baseProbeEval w 0)
  rw [eval_baseValueActionSqPoly]
  have hcoord : (V *ᵥ w) i ≠ 0 := by
    simpa [w, Matrix.mulVec, dotProduct] using hij
  have hnonneg : ∀ x ∈ (Finset.univ : Finset (Fin d)),
      0 ≤ (V *ᵥ w) x * (V *ᵥ w) x := by
    intro x _hx
    exact mul_self_nonneg _
  exact ne_of_gt (Finset.sum_pos' hnonneg
    ⟨i, Finset.mem_univ i, mul_self_pos.mpr hcoord⟩)

/-- Under R1/R2, every individual separated-probe factor is a nonzero
polynomial. -/
theorem baseSeparationFactorPoly_ne_zero_of_regularity {k d : Nat}
    {θ : Params 1 k d} (hθ : Regularity θ) :
    ∀ idx : BaseSeparationFactorIndex k,
      baseSeparationFactorPoly θ idx ≠ 0 := by
  intro idx
  cases idx with
  | slope a =>
      apply baseBilinPoly_ne_zero_of_matrix_ne_zero
      intro hzero
      have hdet := hθ.attention_det_ne_zero (0 : Fin 1) a
      have hsym := hθ.attention_sym_ne_zero (0 : Fin 1) a
      have hmatrix : attentionMatrix θ 0 a = 0 := by
        simpa [baseAttention] using hzero
      have hd : 0 < d := by
        by_contra hnot
        have hd0 : d = 0 := Nat.eq_zero_of_not_pos hnot
        subst d
        apply hsym
        ext i
        exact Fin.elim0 i
      apply hdet
      rw [hmatrix]
      exact Matrix.det_zero ⟨⟨0, hd⟩⟩
  | slopeDifference ac =>
      apply baseBilinPoly_ne_zero_of_matrix_ne_zero
      exact sub_ne_zero.mpr
        (hθ.attention_ne_of_ne (0 : Fin 1) (ne_of_lt ac.2))
  | valueAction a =>
      exact baseValueActionSqPoly_ne_zero_of_matrix_ne_zero
        (hθ.value_ne_zero (0 : Fin 1) a)

/-- The full separated-probe product polynomial is nonzero under R1/R2. -/
theorem baseSeparationPoly_ne_zero_of_regularity {k d : Nat}
    {θ : Params 1 k d} (hθ : Regularity θ) :
    baseSeparationPoly θ ≠ 0 := by
  apply mvPolynomial_finset_prod_ne_zero
  intro idx _hidx
  exact baseSeparationFactorPoly_ne_zero_of_regularity hθ idx

/-! ## Topology of separated probes -/

theorem continuous_baseProbeEval {d : Nat} :
    Continuous (fun p : ProbePoint d => baseProbeEval p.1 p.2) := by
  refine continuous_pi ?_
  intro x
  cases x with
  | inl i => exact (continuous_apply i).comp continuous_fst
  | inr i => exact (continuous_apply i).comp continuous_snd

/-- Coordinate homeomorphism between probe pairs and polynomial assignments. -/
def baseProbeEvalHomeomorph (d : Nat) :
    ProbePoint d ≃ₜ (BaseProbeVar d → ℝ) where
  toFun := fun p => baseProbeEval p.1 p.2
  invFun := fun ρ => (fun i => ρ (Sum.inl i), fun i => ρ (Sum.inr i))
  left_inv := by
    rintro ⟨w, v⟩
    rfl
  right_inv := by
    intro ρ
    funext x
    cases x <;> rfl
  continuous_toFun := continuous_baseProbeEval
  continuous_invFun := by
    refine Continuous.prodMk ?_ ?_
    · refine continuous_pi ?_
      intro i
      exact continuous_apply (Sum.inl i)
    · refine continuous_pi ?_
      intro i
      exact continuous_apply (Sum.inr i)

/-- The depth-one separated probe set, defined as one polynomial
nonvanishing locus. -/
def baseSeparatedProbeSet {k d : Nat} (θ : Params 1 k d) :
    Set (ProbePoint d) :=
  {p | MvPolynomial.eval (baseProbeEval p.1 p.2) (baseSeparationPoly θ) ≠ 0}

@[simp] theorem mem_baseSeparatedProbeSet_iff {k d : Nat}
    (θ : Params 1 k d) (p : ProbePoint d) :
    p ∈ baseSeparatedProbeSet θ ↔ BaseSeparatedProbe θ p.1 p.2 := by
  exact eval_baseSeparationPoly_ne_zero_iff θ p.1 p.2

/-- Principal-open presentation used as the base-case Zariski-open notion. -/
def IsBaseProbePrincipalZariskiOpen {d : Nat} (U : Set (ProbePoint d)) : Prop :=
  ∃ P : BaseProbePoly d, P ≠ 0 ∧
    U = {p | MvPolynomial.eval (baseProbeEval p.1 p.2) P ≠ 0}

theorem baseSeparatedProbeSet_principalZariskiOpen_of_regularity {k d : Nat}
    {θ : Params 1 k d} (hθ : Regularity θ) :
    IsBaseProbePrincipalZariskiOpen (baseSeparatedProbeSet θ) :=
  ⟨baseSeparationPoly θ, baseSeparationPoly_ne_zero_of_regularity hθ, rfl⟩

theorem isOpen_baseSeparatedProbeSet {k d : Nat} (θ : Params 1 k d) :
    IsOpen (baseSeparatedProbeSet θ) := by
  have hopen := isOpen_mvPolynomialNonvanishingSet (baseSeparationPoly θ)
  exact (by
    simpa [baseSeparatedProbeSet, mvPolynomialNonvanishingSet,
      baseProbeEvalHomeomorph] using
      hopen.preimage (baseProbeEvalHomeomorph d).continuous)

theorem dense_baseSeparatedProbeSet_of_regularity {k d : Nat}
    {θ : Params 1 k d} (hθ : Regularity θ) :
    Dense (baseSeparatedProbeSet θ) := by
  have hdense := dense_mvPolynomialNonvanishingSet
    (baseSeparationPoly θ) (baseSeparationPoly_ne_zero_of_regularity hθ)
  simpa [baseSeparatedProbeSet, mvPolynomialNonvanishingSet,
    baseProbeEvalHomeomorph] using
    hdense.preimage (baseProbeEvalHomeomorph d).isOpenMap

theorem baseSeparatedProbeSet_nonempty_of_regularity {k d : Nat}
    {θ : Params 1 k d} (hθ : Regularity θ) :
    (baseSeparatedProbeSet θ).Nonempty := by
  have hdense := dense_baseSeparatedProbeSet_of_regularity hθ
  rcases hdense.inter_open_nonempty Set.univ isOpen_univ
      (show (Set.univ : Set (ProbePoint d)).Nonempty from ⟨(0, 0), trivial⟩) with
    ⟨p, _hp_univ, hp⟩
  exact ⟨p, hp⟩

/-- Euclidean density implies the polynomial-vanishing formulation of Zariski
density used by global attention matching. -/
theorem probeZariskiDense_of_dense {d : Nat} {U : Set (ProbePoint d)}
    (hU : Dense U) : ProbeZariskiDense U := by
  intro P hP
  apply MvPolynomial.funext
  intro ρ
  let p : ProbePoint d :=
    (fun i => ρ (Sum.inl i), fun i => ρ (Sum.inr i))
  have hclosed : IsClosed {q : ProbePoint d |
      MvPolynomial.eval (baseProbeEval q.1 q.2) P = 0} :=
    isClosed_singleton.preimage
      ((MvPolynomial.continuous_eval P).comp continuous_baseProbeEval)
  have hsubset : U ⊆ {q : ProbePoint d |
      MvPolynomial.eval (baseProbeEval q.1 q.2) P = 0} := by
    intro q hq
    have heval : baseProbeEval q.1 q.2 = Sum.elim q.1 q.2 := by
      funext x
      cases x <;> rfl
    change MvPolynomial.eval (baseProbeEval q.1 q.2) P = 0
    rw [heval]
    exact hP q hq
  have hp_closure : p ∈ closure U := by
    simp [hU.closure_eq]
  have hp_zero : MvPolynomial.eval (baseProbeEval p.1 p.2) P = 0 :=
    (closure_minimal hsubset hclosed) hp_closure
  have hp_eval : baseProbeEval p.1 p.2 = ρ := by
    funext x
    cases x <;> rfl
  simpa [hp_eval] using hp_zero

theorem baseSeparatedProbeSet_zariskiDense_of_regularity {k d : Nat}
    {θ : Params 1 k d} (hθ : Regularity θ) :
    ProbeZariskiDense (baseSeparatedProbeSet θ) :=
  probeZariskiDense_of_dense (dense_baseSeparatedProbeSet_of_regularity hθ)

/-- A nonempty Euclidean-open separated subset ready for pointwise base-case
recovery. -/
structure BaseSeparatedOpenProbeData {k d : Nat} (θ : Params 1 k d) where
  Ω : Set (ProbePoint d)
  isOpen_omega : IsOpen Ω
  omega_nonempty : Ω.Nonempty
  omega_subset : Ω ⊆ baseSeparatedProbeSet θ
  separated : ∀ p ∈ Ω, BaseSeparatedProbe θ p.1 p.2

/-- The full separated locus itself supplies the recovery subset. -/
def baseSeparatedOpenProbeDataOfRegularity {k d : Nat}
    {θ : Params 1 k d} (hθ : Regularity θ) :
    BaseSeparatedOpenProbeData θ where
  Ω := baseSeparatedProbeSet θ
  isOpen_omega := isOpen_baseSeparatedProbeSet θ
  omega_nonempty := baseSeparatedProbeSet_nonempty_of_regularity hθ
  omega_subset := Set.Subset.rfl
  separated := by
    intro p hp
    exact (mem_baseSeparatedProbeSet_iff θ p).mp hp

/-! ## Aggregate mixture recovery -/

/-- A pole belonging to a target aggregate slope transfers to the source
mixture.  The two constant entire parts are allowed to differ. -/
theorem baseProbeMixtureC_pole_mem_source_of_positive_real_eq
    {k d r : Nat} (hr : 1 < r) {θ θ' : Params 1 k d} {w v : Vec d}
    (hEq : ∀ τ : ℝ, 0 < τ →
      baseProbeMixtureC r θ w v (τ : ℂ) =
        baseProbeMixtureC r θ' w v (τ : ℂ))
    {slope : ℝ}
    (hslope : slope ∈
      slopeSupportFinset (baseCoeffC θ' w) (baseSlope θ' w v))
    {ξ : ℂ} (hξ : ξ ∈ affineSigmoidPoleSet (logScale r) slope) :
    ξ ∈ mixtureSingularSet (logScale r) (baseCoeffC θ w)
      (baseSlope θ w v) := by
  classical
  let E : Set ℂ :=
    mixtureSingularSet (logScale r) (baseCoeffC θ w) (baseSlope θ w v)
  let E' : Set ℂ :=
    mixtureSingularSet (logScale r) (baseCoeffC θ' w) (baseSlope θ' w v)
  have hb : logScale r ≠ 0 := logScale_ne_zero_of_one_lt hr
  have hslope_ne : slope ≠ 0 :=
    (mem_slopeSupportFinset_iff (baseCoeffC θ' w)
      (baseSlope θ' w v) slope).1 hslope |>.1
  have hcoeff_vec_ne :
      aggregateCoeff (baseCoeffC θ' w) (baseSlope θ' w v) slope ≠ 0 :=
    (mem_slopeSupportFinset_iff (baseCoeffC θ' w)
      (baseSlope θ' w v) slope).1 hslope |>.2
  obtain ⟨i, hcoeff_i⟩ : ∃ i : Fin d,
      aggregateCoeff (baseCoeffC θ' w) (baseSlope θ' w v) slope i ≠ 0 := by
    by_contra hnone
    apply hcoeff_vec_ne
    ext i
    by_contra hi
    exact hnone ⟨i, hi⟩
  have hEclosed : IsClosed E := by
    dsimp [E]
    exact mixtureSingularSet_closed (logScale r)
      (baseCoeffC θ w) (baseSlope θ w v)
  have hEcount : E.Countable := by
    dsimp [E]
    exact mixtureSingularSet_countable (logScale r)
      (baseCoeffC θ w) (baseSlope θ w v)
  have hE'count : E'.Countable := by
    dsimp [E']
    exact mixtureSingularSet_countable (logScale r)
      (baseCoeffC θ' w) (baseSlope θ' w v)
  have hFanalytic :
      AnalyticOnNhd ℂ (fun τ : ℂ => baseProbeMixtureC r θ w v τ i) Eᶜ := by
    dsimp [E]
    simpa [baseProbeMixtureC] using
      (constantSigmoidMixture_coord_analyticOnNhd_mixtureSingularSet_compl
        (logScale r) (baseEntirePartC θ v) (baseCoeffC θ w)
        (baseSlope θ w v) i)
  have hGanalytic :
      AnalyticOnNhd ℂ (fun τ : ℂ => baseProbeMixtureC r θ' w v τ i) E'ᶜ := by
    dsimp [E']
    simpa [baseProbeMixtureC] using
      (constantSigmoidMixture_coord_analyticOnNhd_mixtureSingularSet_compl
        (logScale r) (baseEntirePartC θ' v) (baseCoeffC θ' w)
        (baseSlope θ' w v) i)
  have hz0 : ((1 : ℝ) : ℂ) ∈ (E ∪ E')ᶜ := by
    rw [Set.mem_compl_iff, Set.mem_union]
    intro hmem
    rcases hmem with hmem | hmem
    · exact ofReal_notMem_mixtureSingularSet (logScale r) 1
        (baseCoeffC θ w) (baseSlope θ w v) (by simpa [E] using hmem)
    · exact ofReal_notMem_mixtureSingularSet (logScale r) 1
        (baseCoeffC θ' w) (baseSlope θ' w v) (by simpa [E'] using hmem)
  have hE'closedDiscrete : ClosedDiscreteIn E' Set.univ := by
    dsimp [E']
    exact mixtureSingularSet_closedDiscrete (logScale r)
      (baseCoeffC θ' w) (baseSlope θ' w v)
  have hGisol : IsPuncturedIsolated E' ξ :=
    eventually_notMem_of_not_mem_acc
      (hE'closedDiscrete.noAccum ξ (by simp))
  have hGblow :
      BlowsUpAt (fun τ : ℂ => baseProbeMixtureC r θ' w v τ i) ξ := by
    simpa [baseProbeMixtureC] using
      (constantSigmoidMixture_coord_blowsUpAt_of_aggregate_ne
        (b := logScale r) (slope := slope) (ξ := ξ)
        (C := baseEntirePartC θ' v)
        (M := baseCoeffC θ' w) (lam := baseSlope θ' w v)
        hb hslope_ne hξ hcoeff_i)
  have hpole : ξ ∈ E :=
    lem_pole_transfer_of_real_tail_eq
      (E_F := E) (E_G := E')
      (F := fun τ : ℂ => baseProbeMixtureC r θ w v τ i)
      (G := fun τ : ℂ => baseProbeMixtureC r θ' w v τ i)
      (T0 := 0) (x0 := 1) (τ := ξ)
      hEclosed hEcount hE'count hFanalytic hGanalytic
      (by norm_num : (0 : ℝ) < 1) hz0
      (by
        intro t ht
        exact congrFun (hEq t ht) i)
      (by
        intro hξE
        exact (hFanalytic ξ hξE).continuousAt)
      hGisol hGblow
  simpa [E] using hpole

/-- Every supported target aggregate slope belongs to the source support. -/
theorem base_slopeSupportFinset_subset_of_positive_real_eq
    {k d r : Nat} (hr : 1 < r) {θ θ' : Params 1 k d} {w v : Vec d}
    (hEq : ∀ τ : ℝ, 0 < τ →
      baseProbeMixtureC r θ w v (τ : ℂ) =
        baseProbeMixtureC r θ' w v (τ : ℂ)) :
    slopeSupportFinset (baseCoeffC θ' w) (baseSlope θ' w v) ⊆
      slopeSupportFinset (baseCoeffC θ w) (baseSlope θ w v) := by
  classical
  intro slope hslope
  let ξ : ℂ := affineSigmoidPole (logScale r) slope 0
  have hξ : ξ ∈ affineSigmoidPoleSet (logScale r) slope := ⟨0, rfl⟩
  have hpole : ξ ∈ mixtureSingularSet (logScale r) (baseCoeffC θ w)
      (baseSlope θ w v) :=
    baseProbeMixtureC_pole_mem_source_of_positive_real_eq
      (r := r) hr hEq hslope hξ
  rw [mixtureSingularSet] at hpole
  rcases Set.mem_iUnion.mp hpole with ⟨mu, hpole⟩
  rcases Set.mem_iUnion.mp hpole with ⟨hmu_supp, hξmu⟩
  have hb : logScale r ≠ 0 := logScale_ne_zero_of_one_lt hr
  have hslope_ne : slope ≠ 0 :=
    (mem_slopeSupportFinset_iff (baseCoeffC θ' w)
      (baseSlope θ' w v) slope).1 hslope |>.1
  have hmu_ne : mu ≠ 0 :=
    (mem_slopeSupportFinset_iff (baseCoeffC θ w)
      (baseSlope θ w v) mu).1 hmu_supp |>.1
  have hmu_eq : mu = slope := by
    by_contra hne
    have hneq : slope ≠ mu := fun hsmu => hne hsmu.symm
    have hinter :
        affineSigmoidPoleSet (logScale r) slope ∩
          affineSigmoidPoleSet (logScale r) mu = ∅ :=
      affineSigmoidPoleSet_inter_eq_empty_of_ne
        hb hslope_ne hmu_ne hneq
    have hboth : ξ ∈ affineSigmoidPoleSet (logScale r) slope ∩
        affineSigmoidPoleSet (logScale r) mu := ⟨hξ, hξmu⟩
    rw [hinter] at hboth
    exact hboth
  simpa [hmu_eq] using hmu_supp

/-- Positive-real equality identifies the finite aggregate slope supports. -/
theorem base_slopeSupportFinset_eq_of_positive_real_eq
    {k d r : Nat} (hr : 1 < r) {θ θ' : Params 1 k d} {w v : Vec d}
    (hEq : ∀ τ : ℝ, 0 < τ →
      baseProbeMixtureC r θ w v (τ : ℂ) =
        baseProbeMixtureC r θ' w v (τ : ℂ)) :
    slopeSupportFinset (baseCoeffC θ w) (baseSlope θ w v) =
      slopeSupportFinset (baseCoeffC θ' w) (baseSlope θ' w v) := by
  ext slope
  constructor
  · intro hslope
    exact base_slopeSupportFinset_subset_of_positive_real_eq
      (θ := θ') (θ' := θ) hr (fun τ hτ => (hEq τ hτ).symm) hslope
  · intro hslope
    exact base_slopeSupportFinset_subset_of_positive_real_eq
      (θ := θ) (θ' := θ') hr hEq hslope

/-- Positive-real equality identifies every nonzero aggregate coefficient,
even though the source and target constant entire parts may differ. -/
theorem base_aggregateCoeff_eq_of_positive_real_eq
    {k d r : Nat} (hr : 1 < r) {θ θ' : Params 1 k d} {w v : Vec d}
    (hEq : ∀ τ : ℝ, 0 < τ →
      baseProbeMixtureC r θ w v (τ : ℂ) =
        baseProbeMixtureC r θ' w v (τ : ℂ)) :
    ∀ slope : ℝ, slope ≠ 0 →
      aggregateCoeff (baseCoeffC θ w) (baseSlope θ w v) slope =
        aggregateCoeff (baseCoeffC θ' w) (baseSlope θ' w v) slope := by
  have hsupp := base_slopeSupportFinset_eq_of_positive_real_eq
    (r := r) hr hEq
  exact aggregateCoeff_eq_of_constantSigmoidMixture_real_tail_eq_of_slopeSupportFinset_eq
    (b := logScale r) (T0 := (0 : ℝ))
    (C := baseEntirePartC θ v) (C' := baseEntirePartC θ' v)
    (M := baseCoeffC θ w) (lam := baseSlope θ w v)
    (M' := baseCoeffC θ' w) (lam' := baseSlope θ' w v)
    (logScale_ne_zero_of_one_lt hr)
    (by simpa [baseProbeMixtureC] using hEq)
    hsupp

/-- Source/target aggregate recovery on a Zariski-dense target-separated probe
set. -/
structure BaseAggregateRecoveryData {k d : Nat}
    (θ θ' : Params 1 k d) where
  U : Set (ProbePoint d)
  zariski_dense : ProbeZariskiDense U
  target_separated : ∀ p ∈ U, BaseSeparatedProbe θ' p.1 p.2
  support_eq_on : ∀ p ∈ U,
    slopeSupportFinset (baseCoeffC θ p.1) (baseSlope θ p.1 p.2) =
      slopeSupportFinset (baseCoeffC θ' p.1) (baseSlope θ' p.1 p.2)
  aggregate_eq_on : ∀ p, p ∈ U → ∀ slope : ℝ, slope ≠ 0 →
    aggregateCoeff (baseCoeffC θ p.1) (baseSlope θ p.1 p.2) slope =
      aggregateCoeff (baseCoeffC θ' p.1) (baseSlope θ' p.1 p.2) slope

/-- Positive-real closed probe-output equality on a chosen target-separated set. -/
structure BasePositiveRealProbeOutputEqualityData {k d : Nat} (r : Nat)
    (θ θ' : Params 1 k d) where
  U : Set (ProbePoint d)
  zariski_dense : ProbeZariskiDense U
  target_separated : ∀ p ∈ U, BaseSeparatedProbe θ' p.1 p.2
  positive_real_eq_on : ∀ p, p ∈ U → ∀ τ : ℝ, 0 < τ →
    probeOutput r θ p.1 p.2 τ = probeOutput r θ' p.1 p.2 τ

/-- Compile pointwise probe-output equality into exact aggregate recovery. -/
def BasePositiveRealProbeOutputEqualityData.toAggregateRecovery
    {k d r : Nat} {θ θ' : Params 1 k d}
    (D : BasePositiveRealProbeOutputEqualityData r θ θ') (hr : 1 < r) :
    BaseAggregateRecoveryData θ θ' where
  U := D.U
  zariski_dense := D.zariski_dense
  target_separated := D.target_separated
  support_eq_on := by
    intro p hp
    exact base_slopeSupportFinset_eq_of_positive_real_eq (r := r) hr
      (baseProbeMixtureC_positive_real_eq_of_probeOutput_eq
        (D.positive_real_eq_on p hp))
  aggregate_eq_on := by
    intro p hp
    exact base_aggregateCoeff_eq_of_positive_real_eq (r := r) hr
      (baseProbeMixtureC_positive_real_eq_of_probeOutput_eq
        (D.positive_real_eq_on p hp))

/-- TeX-facing specialization: regularity supplies the target separated set,
and pointwise output equality supplies aggregate recovery on that set. -/
def baseAggregateRecoveryOnSeparatedSet {k d r : Nat}
    {θ θ' : Params 1 k d} (hr : 1 < r) (hθ' : Regularity θ')
    (hEq : ∀ p, p ∈ baseSeparatedProbeSet θ' → ∀ τ : ℝ, 0 < τ →
      probeOutput r θ p.1 p.2 τ = probeOutput r θ' p.1 p.2 τ) :
    BaseAggregateRecoveryData θ θ' :=
  (show BasePositiveRealProbeOutputEqualityData r θ θ' from
    { U := baseSeparatedProbeSet θ'
      zariski_dense := baseSeparatedProbeSet_zariskiDense_of_regularity hθ'
      target_separated := by
        intro p hp
        exact (mem_baseSeparatedProbeSet_iff θ' p).mp hp
      positive_real_eq_on := hEq }).toAggregateRecovery hr

/-! ## Probe-wise paired recovery -/

namespace BaseSeparatedProbe

theorem slope_pairwise {k d : Nat} {θ : Params 1 k d} {w v : Vec d}
    (hsep : BaseSeparatedProbe θ w v) :
    Pairwise fun a c : Fin k => baseSlope θ w v a ≠ baseSlope θ w v c := by
  intro a c hne heq
  exact hne (hsep.slope_injective heq)

theorem coeffC_ne_zero {k d : Nat} {θ : Params 1 k d} {w v : Vec d}
    (hsep : BaseSeparatedProbe θ w v) (a : Fin k) :
    baseCoeffC θ w a ≠ 0 := by
  intro hzero
  apply hsep.value_action_ne_zero a
  ext i
  have hi : (((baseValue θ a *ᵥ w) i : ℝ) : ℂ) = 0 := by
    simpa [baseCoeffC] using congrFun hzero i
  exact Complex.ofReal_inj.mp hi

end BaseSeparatedProbe

/-- A target-to-source pairing at one probe.  Thus `σ h` is the source head
matching target head `h`. -/
def BaseProbePairing {k d : Nat} (θ θ' : Params 1 k d)
    (w v : Vec d) (σ : Equiv.Perm (Fin k)) : Prop :=
  ∀ h : Fin k,
    baseSlope θ w v (σ h) = baseSlope θ' w v h ∧
      baseCoeffC θ w (σ h) = baseCoeffC θ' w h

/-- Finite aggregate counting recovers a target-to-source permutation and its
paired vector coefficient at a separated target probe. -/
theorem exists_baseProbePairing_of_aggregateCoeff_eq {k d : Nat}
    {θ θ' : Params 1 k d} {w v : Vec d}
    (hsep' : BaseSeparatedProbe θ' w v)
    (hagg : ∀ slope : ℝ, slope ≠ 0 →
      aggregateCoeff (baseCoeffC θ w) (baseSlope θ w v) slope =
        aggregateCoeff (baseCoeffC θ' w) (baseSlope θ' w v) slope) :
    ∃ σ : Equiv.Perm (Fin k), BaseProbePairing θ θ' w v σ := by
  classical
  let lam : Fin k → ℝ := baseSlope θ w v
  let lam' : Fin k → ℝ := baseSlope θ' w v
  let M : Fin k → Fin d → ℂ := baseCoeffC θ w
  let M' : Fin k → Fin d → ℂ := baseCoeffC θ' w
  have hsupp_eq : slopeSupportFinset M lam = slopeSupportFinset M' lam' :=
    slopeSupportFinset_eq_of_aggregateCoeff_eq
      (M := M) (lam := lam) (M' := M') (lam' := lam') hagg
  have hprimed_supp : slopeSupportFinset M' lam' = Finset.univ.image lam' :=
    slopeSupportFinset_eq_image_of_pairwise_nonzero
      (M := M') (lam := lam') hsep'.slope_pairwise hsep'.slope_ne_zero
      hsep'.coeffC_ne_zero
  have hExists : ∀ h : Fin k, ∃ c : Fin k, lam c = lam' h := by
    intro h
    have hmem_prime : lam' h ∈ slopeSupportFinset M' lam' := by
      rw [hprimed_supp]
      exact Finset.mem_image.mpr ⟨h, Finset.mem_univ h, rfl⟩
    have hmem_source : lam' h ∈ slopeSupportFinset M lam := by
      simpa [hsupp_eq] using hmem_prime
    change lam' h ∈ (Finset.univ.image lam).filter
      (fun slope => slope ≠ 0 ∧ aggregateCoeff M lam slope ≠ 0) at hmem_source
    rcases Finset.mem_image.mp (Finset.mem_filter.mp hmem_source).1 with
      ⟨c, _hc, hc⟩
    exact ⟨c, hc⟩
  let σfun : Fin k → Fin k := fun h => Classical.choose (hExists h)
  have hσfun : ∀ h : Fin k, lam (σfun h) = lam' h := fun h =>
    Classical.choose_spec (hExists h)
  have hσinj : Function.Injective σfun := by
    intro h g hhg
    apply hsep'.slope_injective
    calc
      lam' h = lam (σfun h) := (hσfun h).symm
      _ = lam (σfun g) := by rw [hhg]
      _ = lam' g := hσfun g
  have hσbij : Function.Bijective σfun := hσinj.bijective_of_finite
  let σ : Equiv.Perm (Fin k) := Equiv.ofBijective σfun hσbij
  have hlam_inj : Function.Injective lam := by
    intro c e hce
    rcases hσbij.2 c with ⟨h, hh⟩
    rcases hσbij.2 e with ⟨g, hg⟩
    have hprime_eq : lam' h = lam' g := by
      calc
        lam' h = lam (σfun h) := (hσfun h).symm
        _ = lam c := by rw [hh]
        _ = lam e := hce
        _ = lam (σfun g) := by rw [hg]
        _ = lam' g := hσfun g
    have hhg : h = g := hsep'.slope_injective hprime_eq
    calc
      c = σfun h := hh.symm
      _ = σfun g := by rw [hhg]
      _ = e := hg
  have hlam_pairwise : Pairwise fun c e : Fin k => lam c ≠ lam e := by
    intro c e hne heq
    exact hne (hlam_inj heq)
  refine ⟨σ, ?_⟩
  intro h
  change lam (σfun h) = lam' h ∧ M (σfun h) = M' h
  refine ⟨hσfun h, ?_⟩
  calc
    M (σfun h) = aggregateCoeff M lam (lam (σfun h)) :=
      (aggregateCoeff_eq_single_of_pairwise
        (M := M) (lam := lam) hlam_pairwise (σfun h)).symm
    _ = aggregateCoeff M lam (lam' h) := by rw [hσfun h]
    _ = aggregateCoeff M' lam' (lam' h) :=
      hagg (lam' h) (hsep'.slope_ne_zero h)
    _ = M' h := aggregateCoeff_eq_single_of_pairwise
      (M := M') (lam := lam') hsep'.slope_pairwise h

/-- At a separated target probe, a target-to-source pairing is unique. -/
theorem baseProbePairing_unique {k d : Nat}
    {θ θ' : Params 1 k d} {w v : Vec d}
    (hsep' : BaseSeparatedProbe θ' w v)
    {σ τ : Equiv.Perm (Fin k)}
    (hσ : BaseProbePairing θ θ' w v σ)
    (hτ : BaseProbePairing θ θ' w v τ) : σ = τ := by
  have hsource_inj : Function.Injective (baseSlope θ w v) := by
    intro c e hce
    let h : Fin k := σ.symm c
    let g : Fin k := σ.symm e
    have hc : σ h = c := by simp [h]
    have he : σ g = e := by simp [g]
    have htarget : baseSlope θ' w v h = baseSlope θ' w v g := by
      calc
        baseSlope θ' w v h = baseSlope θ w v (σ h) := (hσ h).1.symm
        _ = baseSlope θ w v c := by rw [hc]
        _ = baseSlope θ w v e := hce
        _ = baseSlope θ w v (σ g) := by rw [he]
        _ = baseSlope θ' w v g := (hσ g).1
    have hhg : h = g := hsep'.slope_injective htarget
    calc
      c = σ h := hc.symm
      _ = σ g := by rw [hhg]
      _ = e := he
  ext h
  have hsigma : σ h = τ h := hsource_inj (by
    calc
      baseSlope θ w v (σ h) = baseSlope θ' w v h := (hσ h).1
      _ = baseSlope θ w v (τ h) := (hτ h).1.symm)
  exact congrArg Fin.val hsigma

/-- Existence and uniqueness of the target-to-source pairing at one separated
probe. -/
theorem existsUnique_baseProbePairing_of_aggregateCoeff_eq {k d : Nat}
    {θ θ' : Params 1 k d} {w v : Vec d}
    (hsep' : BaseSeparatedProbe θ' w v)
    (hagg : ∀ slope : ℝ, slope ≠ 0 →
      aggregateCoeff (baseCoeffC θ w) (baseSlope θ w v) slope =
        aggregateCoeff (baseCoeffC θ' w) (baseSlope θ' w v) slope) :
    ∃! σ : Equiv.Perm (Fin k), BaseProbePairing θ θ' w v σ := by
  rcases exists_baseProbePairing_of_aggregateCoeff_eq hsep' hagg with ⟨σ, hσ⟩
  exact ⟨σ, hσ, fun τ hτ => baseProbePairing_unique hsep' hτ hσ⟩

/-- Probe-wise paired recovery, without any assertion that the permutation is
constant across probes. -/
structure BasePairedProbeRecoveryData {k d : Nat}
    (θ θ' : Params 1 k d) where
  U : Set (ProbePoint d)
  zariski_dense : ProbeZariskiDense U
  target_separated : ∀ p ∈ U, BaseSeparatedProbe θ' p.1 p.2
  paired_on : ∀ p, p ∈ U →
    ∃! σ : Equiv.Perm (Fin k), BaseProbePairing θ θ' p.1 p.2 σ

/-- Aggregate recovery compiles to unique probe-wise paired recovery. -/
def BaseAggregateRecoveryData.toPairedProbeRecovery {k d : Nat}
    {θ θ' : Params 1 k d} (D : BaseAggregateRecoveryData θ θ') :
    BasePairedProbeRecoveryData θ θ' where
  U := D.U
  zariski_dense := D.zariski_dense
  target_separated := D.target_separated
  paired_on := by
    intro p hp
    exact existsUnique_baseProbePairing_of_aggregateCoeff_eq
      (D.target_separated p hp) (D.aggregate_eq_on p hp)

/-! ## Global attention permutation -/

/-- Product identity on the Zariski-dense probe set obtained from probe-wise
pairings. -/
theorem BasePairedProbeRecoveryData.slopeProduct_eq_on {k d : Nat}
    {θ θ' : Params 1 k d} (D : BasePairedProbeRecoveryData θ θ') :
    ∀ p, p ∈ D.U → ∀ t : ℝ,
      ∏ c : Fin k, (t - baseSlope θ p.1 p.2 c) =
        ∏ h : Fin k, (t - baseSlope θ' p.1 p.2 h) := by
  classical
  intro p hp t
  rcases D.paired_on p hp with ⟨σ, hσ, _hunique⟩
  have hreindex :
      (∏ h : Fin k, (t - baseSlope θ p.1 p.2 (σ h))) =
        ∏ c : Fin k, (t - baseSlope θ p.1 p.2 c) := by
    simpa using
      (Fintype.prod_equiv σ
        (fun h : Fin k => t - baseSlope θ p.1 p.2 (σ h))
        (fun c : Fin k => t - baseSlope θ p.1 p.2 c)
        (by intro h; rfl))
  calc
    ∏ c : Fin k, (t - baseSlope θ p.1 p.2 c) =
        ∏ h : Fin k, (t - baseSlope θ p.1 p.2 (σ h)) := hreindex.symm
    _ = ∏ h : Fin k, (t - baseSlope θ' p.1 p.2 h) := by
      refine Finset.prod_congr rfl ?_
      intro h _hh
      rw [(hσ h).1]

/-- Equality of the formal source and target attention-product polynomials. -/
theorem BasePairedProbeRecoveryData.attentionProductPoly_eq {k d : Nat}
    {θ θ' : Params 1 k d} (D : BasePairedProbeRecoveryData θ θ') :
    attentionProductPoly (baseAttention θ) =
      attentionProductPoly (baseAttention θ') := by
  apply attentionProductPoly_eq_of_probeZariskiDense
    (baseAttention θ) (baseAttention θ') D.U D.zariski_dense
  intro p hp t
  simpa [baseSlope, matrixBilin] using D.slopeProduct_eq_on p hp t

/-- The product identity globalized to every real probe. -/
theorem BasePairedProbeRecoveryData.globalSlopeProductIdentity {k d : Nat}
    {θ θ' : Params 1 k d} (D : BasePairedProbeRecoveryData θ θ') :
    ∀ (t : ℝ) (w v : Vec d),
      ∏ c : Fin k, (t - baseSlope θ w v c) =
        ∏ h : Fin k, (t - baseSlope θ' w v h) := by
  have hid := attention_product_identity_of_probeZariskiDense
    (baseAttention θ) (baseAttention θ') D.U D.zariski_dense
    (by
      intro p hp t
      simpa [baseSlope, matrixBilin] using D.slopeProduct_eq_on p hp t)
  intro t w v
  simpa [baseSlope, matrixBilin] using hid t w v

/-- R2 makes the target depth-one attention family injective. -/
theorem baseAttention_injective_of_regularity {k d : Nat}
    {θ : Params 1 k d} (hθ : Regularity θ) :
    Function.Injective (baseAttention θ) := by
  intro a c heq
  by_contra hne
  exact (hθ.attention_ne_of_ne (0 : Fin 1) hne)
    (by simpa [baseAttention] using heq)

/-- The unique global target-to-source attention permutation. -/
theorem BasePairedProbeRecoveryData.attentionPermutation {k d : Nat}
    {θ θ' : Params 1 k d} (D : BasePairedProbeRecoveryData θ θ')
    (hθ' : Regularity θ') :
    ∃! σ : Equiv.Perm (Fin k),
      ∀ h : Fin k, baseAttention θ (σ h) = baseAttention θ' h := by
  simpa [TargetToSourcePermutation] using
    (global_labeling_algebraic
      (baseAttention θ) (baseAttention θ') D.U
      (baseAttention_injective_of_regularity hθ') D.zariski_dense
      (by
        intro p hp t
        simpa [baseSlope, matrixBilin] using D.slopeProduct_eq_on p hp t))

/-- End-to-end NS086 wrapper on the canonical target separated set. -/
theorem baseAttentionPermutation_of_probeOutput_eq {k d r : Nat}
    {θ θ' : Params 1 k d} (hr : 1 < r) (hθ' : Regularity θ')
    (hEq : ∀ p, p ∈ baseSeparatedProbeSet θ' → ∀ τ : ℝ, 0 < τ →
      probeOutput r θ p.1 p.2 τ = probeOutput r θ' p.1 p.2 τ) :
    ∃! σ : Equiv.Perm (Fin k),
      ∀ h : Fin k, baseAttention θ (σ h) = baseAttention θ' h := by
  exact ((baseAggregateRecoveryOnSeparatedSet hr hθ' hEq).toPairedProbeRecovery)
    |>.attentionPermutation hθ'

/-! ## First-layer value recovery -/

/-- Once the attention permutation is fixed globally, every probe-wise label is
that same permutation, so its vector coefficient is attached to the fixed
source head. -/
theorem BasePairedProbeRecoveryData.coeffC_eq_of_attentionPermutation
    {k d : Nat} {θ θ' : Params 1 k d}
    (D : BasePairedProbeRecoveryData θ θ') {σ : Equiv.Perm (Fin k)}
    (hσ_att : ∀ h : Fin k, baseAttention θ (σ h) = baseAttention θ' h)
    {p : ProbePoint d} (hp : p ∈ D.U) :
    ∀ h : Fin k, baseCoeffC θ p.1 (σ h) = baseCoeffC θ' p.1 h := by
  classical
  rcases D.paired_on p hp with ⟨τ, hτ, _hτunique⟩
  have hσ_slope : ∀ h : Fin k,
      baseSlope θ p.1 p.2 (σ h) = baseSlope θ' p.1 p.2 h := by
    intro h
    simp [baseSlope, hσ_att h]
  have hτ_eq : τ = σ := by
    apply Equiv.ext
    intro h
    have hτ_slope := (hτ h).1
    have hσ_at : baseSlope θ p.1 p.2 (τ h) =
        baseSlope θ' p.1 p.2 (σ.symm (τ h)) := by
      simpa using hσ_slope (σ.symm (τ h))
    have htarget : baseSlope θ' p.1 p.2 h =
        baseSlope θ' p.1 p.2 (σ.symm (τ h)) :=
      hτ_slope.symm.trans hσ_at
    have hh : h = σ.symm (τ h) :=
      (D.target_separated p hp).slope_injective htarget
    calc
      τ h = σ (σ.symm (τ h)) := by simp
      _ = σ h := by rw [← hh]
  intro h
  simpa [hτ_eq] using (hτ h).2

/-- Exact paired value matrices for a fixed target-to-source permutation. -/
structure BaseValueRecoveryData {k d : Nat}
    (θ θ' : Params 1 k d) (σ : Equiv.Perm (Fin k)) : Prop where
  value_matrix_eq : ∀ h : Fin k, baseValue θ (σ h) = baseValue θ' h

/-- Equality of complexified value actions on a nonempty open set of `w`
forces exact equality of the corresponding real matrices. -/
theorem BaseValueRecoveryData.of_coeffC_eq_on_nonempty_open
    {k d : Nat} {θ θ' : Params 1 k d} {σ : Equiv.Perm (Fin k)}
    {W : Set (Vec d)} (hW_open : IsOpen W) (hW_nonempty : W.Nonempty)
    (hcoeff : ∀ h : Fin k, ∀ w : Vec d, w ∈ W →
      baseCoeffC θ w (σ h) = baseCoeffC θ' w h) :
    BaseValueRecoveryData θ θ' σ := by
  refine ⟨?_⟩
  intro h
  apply sub_eq_zero.mp
  apply matrix_eq_zero_of_forall_mulVec_eq_zero_on_open hW_open hW_nonempty
  intro w hw
  rw [Matrix.sub_mulVec]
  apply sub_eq_zero.mpr
  ext i
  have hi : (((baseValue θ (σ h) *ᵥ w) i : ℝ) : ℂ) =
      (((baseValue θ' h *ᵥ w) i : ℝ) : ℂ) := by
    simpa [baseCoeffC] using congrFun (hcoeff h w hw) i
  exact Complex.ofReal_inj.mp hi

/-- A nonempty open family of paired probes supplies value recovery for the
fixed global attention permutation. -/
theorem BasePairedProbeRecoveryData.valueRecovery_of_openProbeSet
    {k d : Nat} {θ θ' : Params 1 k d}
    (D : BasePairedProbeRecoveryData θ θ') {σ : Equiv.Perm (Fin k)}
    (hσ_att : ∀ h : Fin k, baseAttention θ (σ h) = baseAttention θ' h)
    {Ω : Set (ProbePoint d)} (hΩ_open : IsOpen Ω) (hΩ_nonempty : Ω.Nonempty)
    (hΩ_subset : Ω ⊆ D.U) : BaseValueRecoveryData θ θ' σ := by
  rcases exists_nonempty_open_firstCoordinateSlice hΩ_open hΩ_nonempty with
    ⟨v0, hW_open, hW_nonempty⟩
  apply BaseValueRecoveryData.of_coeffC_eq_on_nonempty_open
    hW_open hW_nonempty
  intro h w hw
  exact D.coeffC_eq_of_attentionPermutation hσ_att
    (p := (w, v0)) (hΩ_subset hw) h

/-- Exact first-layer recovery: the unique target-to-source attention
permutation also pairs the value matrices. -/
structure BaseFirstLayerValueRecoveryData {k d : Nat}
    (θ θ' : Params 1 k d) where
  σ : Equiv.Perm (Fin k)
  attention_eq : ∀ h : Fin k, baseAttention θ (σ h) = baseAttention θ' h
  attention_unique : ∀ τ : Equiv.Perm (Fin k),
    (∀ h : Fin k, baseAttention θ (τ h) = baseAttention θ' h) → τ = σ
  value_eq : ∀ h : Fin k, baseValue θ (σ h) = baseValue θ' h

/-- Package global attention matching and open-slice value recovery. -/
def BasePairedProbeRecoveryData.toFirstLayerValueRecovery
    {k d : Nat} {θ θ' : Params 1 k d}
    (D : BasePairedProbeRecoveryData θ θ') (hθ' : Regularity θ')
    {Ω : Set (ProbePoint d)} (hΩ_open : IsOpen Ω) (hΩ_nonempty : Ω.Nonempty)
    (hΩ_subset : Ω ⊆ D.U) : BaseFirstLayerValueRecoveryData θ θ' := by
  classical
  let hperm := D.attentionPermutation hθ'
  let σ : Equiv.Perm (Fin k) := Classical.choose hperm
  have hσ : ∀ h : Fin k, baseAttention θ (σ h) = baseAttention θ' h :=
    (Classical.choose_spec hperm).1
  have hσ_unique : ∀ τ : Equiv.Perm (Fin k),
      (∀ h : Fin k, baseAttention θ (τ h) = baseAttention θ' h) → τ = σ :=
    (Classical.choose_spec hperm).2
  let hvalue := D.valueRecovery_of_openProbeSet hσ hΩ_open hΩ_nonempty hΩ_subset
  exact
    { σ := σ
      attention_eq := hσ
      attention_unique := hσ_unique
      value_eq := hvalue.value_matrix_eq }

/-! ## Depth-one capstone -/

/-- Exact depth-one equality written as a boundary-normalized gauge matching.
Both interfaces carry the identity gauge. -/
def identityGaugeBaseMatching {k d : Nat} {θ θ' : Params 1 k d}
    (R : BaseFirstLayerValueRecoveryData θ θ') :
    TargetToSourceMatching θ θ' where
  headPerm := fun _ => R.σ
  gauge := 1
  attention_eq := by
    intro l h
    have hl : l = (0 : Fin 1) := Subsingleton.elim _ _
    subst l
    simpa [baseAttention] using R.attention_eq h
  value_eq := by
    intro l h
    have hl : l = (0 : Fin 1) := Subsingleton.elim _ _
    subst l
    simpa [baseValue] using R.value_eq h

/-- Exact depth-one induction endpoint: one unique target-to-source permutation,
exact paired matrices, and the trivial boundary gauge. -/
structure BaseCaseConclusion {k d : Nat} (θ θ' : Params 1 k d) where
  recovery : BaseFirstLayerValueRecoveryData θ θ'
  matching : TargetToSourceMatching θ θ'
  matching_headPerm : matching.headPerm = fun _ => recovery.σ
  matching_gauge : matching.gauge = 1

/-- Build the capstone from exact first-layer recovery. -/
def BaseFirstLayerValueRecoveryData.toBaseCaseConclusion
    {k d : Nat} {θ θ' : Params 1 k d}
    (R : BaseFirstLayerValueRecoveryData θ θ') : BaseCaseConclusion θ θ' where
  recovery := R
  matching := identityGaugeBaseMatching R
  matching_headPerm := rfl
  matching_gauge := rfl

namespace BaseCaseConclusion

theorem attention_eq {k d : Nat} {θ θ' : Params 1 k d}
    (C : BaseCaseConclusion θ θ') (h : Fin k) :
    baseAttention θ (C.recovery.σ h) = baseAttention θ' h :=
  C.recovery.attention_eq h

theorem value_eq {k d : Nat} {θ θ' : Params 1 k d}
    (C : BaseCaseConclusion θ θ') (h : Fin k) :
    baseValue θ (C.recovery.σ h) = baseValue θ' h :=
  C.recovery.value_eq h

theorem boundaryGauge_eq_identity {k d : Nat} {θ θ' : Params 1 k d}
    (C : BaseCaseConclusion θ θ') : C.matching.gauge = 1 :=
  C.matching_gauge

/-- Unique target-to-source permutation simultaneously pairing attentions and
values. -/
theorem existsUnique_pairedMatrices {k d : Nat} {θ θ' : Params 1 k d}
    (C : BaseCaseConclusion θ θ') :
    ∃! σ : Equiv.Perm (Fin k), ∀ h : Fin k,
      baseAttention θ (σ h) = baseAttention θ' h ∧
        baseValue θ (σ h) = baseValue θ' h := by
  refine ⟨C.recovery.σ, ?_, ?_⟩
  · intro h
    exact ⟨C.attention_eq h, C.value_eq h⟩
  · intro τ hτ
    exact C.recovery.attention_unique τ (fun h => (hτ h).1)

end BaseCaseConclusion

/-- NS088 constructor: regular target parameters and global positive-real
closed-probe equality produce the exact depth-one conclusion. -/
noncomputable def baseCaseConclusionOfProbeOutputEq {k d r : Nat}
    {θ θ' : Params 1 k d} (hr : 1 < r) (hθ' : Regularity θ')
    (hEq : ∀ (w v : Vec d) (τ : ℝ), 0 < τ →
      probeOutput r θ w v τ = probeOutput r θ' w v τ) :
    BaseCaseConclusion θ θ' := by
  let D : BasePairedProbeRecoveryData θ θ' :=
    (baseAggregateRecoveryOnSeparatedSet hr hθ'
      (fun p _hp τ hτ => hEq p.1 p.2 τ hτ)).toPairedProbeRecovery
  let R : BaseFirstLayerValueRecoveryData θ θ' :=
    D.toFirstLayerValueRecovery hθ'
      (isOpen_baseSeparatedProbeSet θ')
      (baseSeparatedProbeSet_nonempty_of_regularity hθ')
      (by intro p hp; exact hp)
  exact R.toBaseCaseConclusion

/-- TeX-facing normalized-observable constructor for the depth-one capstone. -/
noncomputable def baseCaseConclusionOfProbeObservableEq {k d r : Nat}
    {θ θ' : Params 1 k d} (hr : 1 < r) (hθ' : Regularity θ')
    (hEq : ∀ (w v : Vec d) (τ : ℝ), 0 < τ →
      probeObservable r θ w v τ = probeObservable r θ' w v τ) :
    BaseCaseConclusion θ θ' := by
  apply baseCaseConclusionOfProbeOutputEq hr hθ'
  intro w v τ hτ
  have hr0 : 0 < r := Nat.zero_lt_of_lt hr
  rw [← probeObservable_eq_probeOutput hr0 θ w v τ hτ,
    ← probeObservable_eq_probeOutput hr0 θ' w v τ hτ]
  exact hEq w v τ hτ

/-- Propositional form of the exact depth-one endpoint for a candidate
target-to-source permutation. -/
def BaseCaseDepthOnePredicate {k d : Nat} (θ θ' : Params 1 k d)
    (σ : Equiv.Perm (Fin k)) : Prop :=
  (∀ h : Fin k,
    baseAttention θ (σ h) = baseAttention θ' h ∧
      baseValue θ (σ h) = baseValue θ' h) ∧
  ∃ M : TargetToSourceMatching θ θ',
    M.headPerm = (fun _ => σ) ∧ M.gauge = 1

/-- Global positive-real closed-probe equality gives one unique exact
target-to-source depth-one matching with identity boundary gauge. -/
theorem depthOne_identifiability_of_probeOutput_eq {k d r : Nat}
    {θ θ' : Params 1 k d} (hr : 1 < r) (hθ' : Regularity θ')
    (hEq : ∀ (w v : Vec d) (τ : ℝ), 0 < τ →
      probeOutput r θ w v τ = probeOutput r θ' w v τ) :
    ∃! σ : Equiv.Perm (Fin k), BaseCaseDepthOnePredicate θ θ' σ := by
  let C := baseCaseConclusionOfProbeOutputEq hr hθ' hEq
  refine ⟨C.recovery.σ, ?_, ?_⟩
  · refine ⟨?_, C.matching, C.matching_headPerm, C.matching_gauge⟩
    intro h
    exact ⟨C.attention_eq h, C.value_eq h⟩
  · intro τ hτ
    exact C.recovery.attention_unique τ (fun h => (hτ.1 h).1)

/-- Normalized-observable form of the exact depth-one identifiability theorem. -/
theorem depthOne_identifiability_of_probeObservable_eq {k d r : Nat}
    {θ θ' : Params 1 k d} (hr : 1 < r) (hθ' : Regularity θ')
    (hEq : ∀ (w v : Vec d) (τ : ℝ), 0 < τ →
      probeObservable r θ w v τ = probeObservable r θ' w v τ) :
    ∃! σ : Equiv.Perm (Fin k), BaseCaseDepthOnePredicate θ θ' σ := by
  let C := baseCaseConclusionOfProbeObservableEq hr hθ' hEq
  refine ⟨C.recovery.σ, ?_, ?_⟩
  · refine ⟨?_, C.matching, C.matching_headPerm, C.matching_gauge⟩
    intro h
    exact ⟨C.attention_eq h, C.value_eq h⟩
  · intro τ hτ
    exact C.recovery.attention_unique τ (fun h => (hτ.1 h).1)

end

end TransformerIdentifiability.NLayer.NoSkip
