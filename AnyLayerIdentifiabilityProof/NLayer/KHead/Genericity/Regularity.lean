import AnyLayerIdentifiabilityProof.NLayer.KHead.FormalStreams

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.KHead

/-!
# K-head genericity: regularity and local openness

This file contains the concrete, finite-dimensional predicates from TeX
Section 03b that do not depend on the headwise anchor certificate.  The
corner-slope condition is represented as nonvanishing of an actual polynomial
in the probe variables `(w, v)`.
-/

/-! ## Basic finite algebra helpers -/

/-- Squared Frobenius norm, kept as a polynomial expression in matrix entries. -/
noncomputable def matrixFrobSq {m n : Nat} (M : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin n, M i j * M i j

@[simp]
theorem matrixFrobSq_zero {m n : Nat} :
    matrixFrobSq (0 : Matrix (Fin m) (Fin n) ℝ) = 0 := by
  simp [matrixFrobSq]

theorem matrixFrobSq_nonneg {m n : Nat} (M : Matrix (Fin m) (Fin n) ℝ) :
    0 ≤ matrixFrobSq M := by
  exact Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => mul_self_nonneg (M i j)

theorem matrixFrobSq_eq_zero_iff {m n : Nat} (M : Matrix (Fin m) (Fin n) ℝ) :
    matrixFrobSq M = 0 ↔ M = 0 := by
  constructor
  · intro h
    ext i j
    have hrow :
        (∑ j : Fin n, M i j * M i j) = 0 := by
      exact
        ((Finset.sum_eq_zero_iff_of_nonneg
          (s := (Finset.univ : Finset (Fin m)))
          (f := fun i : Fin m => ∑ j : Fin n, M i j * M i j)
          (fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg (M i j))).mp h)
          i (Finset.mem_univ i)
    have hentry :
        M i j * M i j = 0 := by
      exact
        ((Finset.sum_eq_zero_iff_of_nonneg
          (s := (Finset.univ : Finset (Fin n)))
          (f := fun j : Fin n => M i j * M i j)
          (fun j _ => mul_self_nonneg (M i j))).mp hrow)
          j (Finset.mem_univ j)
    exact mul_self_eq_zero.mp hentry
  · intro h
    simp [h]

theorem matrixFrobSq_ne_zero_iff {m n : Nat} (M : Matrix (Fin m) (Fin n) ℝ) :
    matrixFrobSq M ≠ 0 ↔ M ≠ 0 :=
  not_congr (matrixFrobSq_eq_zero_iff M)

theorem matrixFrobSq_sub_ne_zero_iff {m n : Nat}
    (M N : Matrix (Fin m) (Fin n) ℝ) :
    matrixFrobSq (M - N) ≠ 0 ↔ M ≠ N := by
  rw [matrixFrobSq_ne_zero_iff, sub_ne_zero]

/-- Over `ℝ`, a multivariate polynomial is nonzero iff some real evaluation is nonzero. -/
theorem realMvPolynomial_ne_zero_iff_exists_eval_ne_zero {ι : Type*}
    (p : MvPolynomial ι ℝ) :
    p ≠ 0 ↔ ∃ x : ι → ℝ, MvPolynomial.eval x p ≠ 0 := by
  constructor
  · intro hp
    by_contra h
    apply hp
    apply MvPolynomial.funext
    intro x
    have hx : MvPolynomial.eval x p = 0 := by
      by_contra hx
      exact h ⟨x, hx⟩
    simp [hx]
  · rintro ⟨x, hx⟩ hzero
    exact hx (by simp [hzero])

/-- A nonzero real multivariate polynomial has a nonzero evaluation on any product of
infinite coordinate sets. -/
theorem realMvPolynomial_ne_zero_iff_exists_eval_ne_zero_on_pi {ι : Type*}
    (p : MvPolynomial ι ℝ) (s : ι → Set ℝ)
    (hs : ∀ i, (s i).Infinite) :
    p ≠ 0 ↔
      ∃ x : ι → ℝ, x ∈ Set.pi Set.univ s ∧ MvPolynomial.eval x p ≠ 0 := by
  constructor
  · intro hp
    by_contra hnone
    apply hp
    exact MvPolynomial.funext_set s hs (by
      intro x hx
      have hzero : MvPolynomial.eval x p = 0 := by
        by_contra hxne
        exact hnone ⟨x, hx, hxne⟩
      simp [hzero])
  · rintro ⟨x, _hx, hxne⟩ hzero
    exact hxne (by simp [hzero])

/-- Probe-polynomial variables: left summand for `w`, right summand for `v`. -/
abbrev ProbeVar (d : Nat) : Type := Sum (Fin d) (Fin d)

/-- Polynomial ring in the probe coordinates `(w, v)`. -/
abbrev ProbePoly (d : Nat) : Type := MvPolynomial (ProbeVar d) ℝ

/-- Coordinate polynomial for the `w` probe stream. -/
noncomputable def probePolyW {d : Nat} : Fin d → ProbePoly d :=
  fun i => MvPolynomial.X (Sum.inl i)

/-- Coordinate polynomial for the `v` probe stream. -/
noncomputable def probePolyV {d : Nat} : Fin d → ProbePoly d :=
  fun i => MvPolynomial.X (Sum.inr i)

/-- Evaluation assignment for probe-polynomial variables. -/
def probePolyEval {d : Nat} (w v : Vec d) : ProbeVar d → ℝ
  | Sum.inl i => w i
  | Sum.inr i => v i

theorem probePoly_ne_zero_iff_exists_eval_ne_zero_on_pi {d : Nat}
    (p : ProbePoly d) (sw sv : Fin d → Set ℝ)
    (hsw : ∀ i, (sw i).Infinite) (hsv : ∀ i, (sv i).Infinite) :
    p ≠ 0 ↔
      ∃ w v : Vec d,
        (∀ i, w i ∈ sw i) ∧ (∀ i, v i ∈ sv i) ∧
          MvPolynomial.eval (probePolyEval w v) p ≠ 0 := by
  let s : ProbeVar d → Set ℝ := fun
    | Sum.inl i => sw i
    | Sum.inr i => sv i
  have hs : ∀ x, (s x).Infinite := by
    intro x
    cases x with
    | inl i => exact hsw i
    | inr i => exact hsv i
  rw [realMvPolynomial_ne_zero_iff_exists_eval_ne_zero_on_pi p s hs]
  constructor
  · rintro ⟨ρ, hρ, hρne⟩
    refine ⟨fun i => ρ (Sum.inl i), fun i => ρ (Sum.inr i), ?_, ?_, ?_⟩
    · intro i
      exact hρ (Sum.inl i) trivial
    · intro i
      exact hρ (Sum.inr i) trivial
    · have hEval :
          probePolyEval (fun i => ρ (Sum.inl i)) (fun i => ρ (Sum.inr i)) = ρ := by
        funext x
        cases x <;> rfl
      simpa [hEval] using hρne
  · rintro ⟨w, v, hw, hv, hne⟩
    refine ⟨probePolyEval w v, ?_, hne⟩
    intro x _hx
    cases x with
    | inl i => exact hw i
    | inr i => exact hv i

@[simp]
theorem probePolyEval_W {d : Nat} (w v : Vec d) (i : Fin d) :
    MvPolynomial.eval (probePolyEval w v) (probePolyW i) = w i := by
  simp [probePolyEval, probePolyW]

@[simp]
theorem probePolyEval_V {d : Nat} (w v : Vec d) (i : Fin d) :
    MvPolynomial.eval (probePolyEval w v) (probePolyV i) = v i := by
  simp [probePolyEval, probePolyV]

/-- Cast a real matrix into the probe-polynomial ring. -/
noncomputable def realMatrixToProbePoly {d : Nat}
    (M : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) (ProbePoly d) :=
  M.map (MvPolynomial.C : ℝ →+* ProbePoly d)

@[simp]
theorem realMatrixToProbePoly_apply {d : Nat}
    (M : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) :
    realMatrixToProbePoly M i j = MvPolynomial.C (M i j) :=
  rfl

@[simp]
theorem map_realMatrixToProbePoly {d : Nat}
    (ρ : ProbeVar d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    (realMatrixToProbePoly M).map (MvPolynomial.eval ρ) = M := by
  ext i j
  simp [realMatrixToProbePoly]

/-- Evaluation commutes with probe-polynomial matrix-vector multiplication. -/
theorem probePoly_eval_mulVec {d : Nat} {m n : Type*} [Fintype n]
    (ρ : ProbeVar d → ℝ) (M : Matrix m n (ProbePoly d))
    (v : n → ProbePoly d) :
    (fun i => MvPolynomial.eval ρ (M.mulVec v i)) =
      (M.map (MvPolynomial.eval ρ)).mulVec
        (fun j => MvPolynomial.eval ρ (v j)) := by
  funext i
  simp [Matrix.mulVec, dotProduct]

/-- Bilinear form over probe-polynomial vectors. -/
noncomputable def probePolyBilin {d : Nat} (A : Matrix (Fin d) (Fin d) ℝ)
    (w v : Fin d → ProbePoly d) : ProbePoly d :=
  w ⬝ᵥ realMatrixToProbePoly A *ᵥ v

@[simp]
theorem eval_probePolyBilin {d : Nat} (ρ : ProbeVar d → ℝ)
    (A : Matrix (Fin d) (Fin d) ℝ) (w v : Fin d → ProbePoly d) :
    MvPolynomial.eval ρ (probePolyBilin A w v) =
      (fun i => MvPolynomial.eval ρ (w i)) ⬝ᵥ
        A *ᵥ (fun i => MvPolynomial.eval ρ (v i)) := by
  simp [probePolyBilin, Matrix.mulVec, dotProduct, realMatrixToProbePoly]

/-- Prefix product `M_(n-1) ... M_0`, with the empty product equal to `1`. -/
def matrixPrefixProduct {d : Nat} (M : Nat → Matrix (Fin d) (Fin d) ℝ) :
    Nat → Matrix (Fin d) (Fin d) ℝ
  | 0 => 1
  | n + 1 => M n * matrixPrefixProduct M n

@[simp]
theorem matrixPrefixProduct_zero {d : Nat}
    (M : Nat → Matrix (Fin d) (Fin d) ℝ) :
    matrixPrefixProduct M 0 = 1 :=
  rfl

@[simp]
theorem matrixPrefixProduct_succ {d : Nat}
    (M : Nat → Matrix (Fin d) (Fin d) ℝ) (n : Nat) :
    matrixPrefixProduct M (n + 1) = M n * matrixPrefixProduct M n :=
  rfl

/-! ## All-`alpha` corner streams -/

/-- Collapsed matrix stream, extended by identity outside the finite depth. -/
noncomputable def collapseMatrixStream {L k d : Nat} (θ : Params L k d) (n : Nat) :
    Matrix (Fin d) (Fin d) ℝ :=
  if h : n < L then collapseMatrix θ ⟨n, h⟩ else 1

/-- Sum of value matrices, extended by zero outside the finite depth. -/
noncomputable def valueSumStream {L k d : Nat} (θ : Params L k d) (n : Nat) :
    Matrix (Fin d) (Fin d) ℝ :=
  if h : n < L then valueSum θ ⟨n, h⟩ else 0

/-- The all-`alpha` saturated `K_i = C_i - alpha * sum_b V_ib`. -/
noncomputable def cornerKStream {L k d : Nat} (r : Nat) (θ : Params L k d)
    (n : Nat) : Matrix (Fin d) (Fin d) ℝ :=
  collapseMatrixStream θ n - (alpha r) • valueSumStream θ n

/-- Product of all-`alpha` `K` matrices through the first `n` layers. -/
noncomputable def cornerKPrefix {L k d : Nat} (r : Nat) (θ : Params L k d)
    (n : Nat) : Matrix (Fin d) (Fin d) ℝ :=
  matrixPrefixProduct (cornerKStream r θ) n

/-- Product of collapsed matrices through the first `n` layers. -/
noncomputable def cornerCPrefix {L k d : Nat} (θ : Params L k d)
    (n : Nat) : Matrix (Fin d) (Fin d) ℝ :=
  matrixPrefixProduct (collapseMatrixStream θ) n

/-- The affine `w`-coefficient in the all-`alpha` corner formula for `v_n`. -/
noncomputable def cornerDPrefix {L k d : Nat} (r : Nat) (θ : Params L k d) :
    Nat → Matrix (Fin d) (Fin d) ℝ
  | 0 => 0
  | n + 1 =>
      collapseMatrixStream θ n * cornerDPrefix r θ n +
        ((alpha r) • valueSumStream θ n) * cornerKPrefix r θ n

@[simp]
theorem cornerDPrefix_zero {L k d : Nat} (r : Nat) (θ : Params L k d) :
    cornerDPrefix r θ 0 = 0 :=
  rfl

@[simp]
theorem cornerDPrefix_succ {L k d : Nat} (r : Nat) (θ : Params L k d) (n : Nat) :
    cornerDPrefix r θ (n + 1) =
      collapseMatrixStream θ n * cornerDPrefix r θ n +
        ((alpha r) • valueSumStream θ n) * cornerKPrefix r θ n :=
  rfl

/-- Corner `w` stream, as a polynomial vector in the probe variables. -/
noncomputable def cornerWPoly {L k d : Nat} (r : Nat) (θ : Params L k d)
    (l : Fin L) : Fin d → ProbePoly d :=
  realMatrixToProbePoly (cornerKPrefix r θ l.val) *ᵥ probePolyW

/-- Corner `v` stream, as a polynomial vector in the probe variables. -/
noncomputable def cornerVPoly {L k d : Nat} (r : Nat) (θ : Params L k d)
    (l : Fin L) : Fin d → ProbePoly d :=
  realMatrixToProbePoly (cornerCPrefix θ l.val) *ᵥ probePolyV +
    realMatrixToProbePoly (cornerDPrefix r θ l.val) *ᵥ probePolyW

/-- Difference of two same-layer corner slope polynomials. -/
noncomputable def cornerSlopeDiffPoly {L k d : Nat} (r : Nat) (θ : Params L k d)
    (l : Fin L) (a c : Fin k) : ProbePoly d :=
  probePolyBilin (attentionMatrix θ l a - attentionMatrix θ l c)
    (cornerWPoly r θ l) (cornerVPoly r θ l)

@[simp]
theorem eval_cornerWPoly {L k d : Nat} (r : Nat) (θ : Params L k d)
    (l : Fin L) (w v : Vec d) :
    (fun i => MvPolynomial.eval (probePolyEval w v) (cornerWPoly r θ l i)) =
      cornerKPrefix r θ l.val *ᵥ w := by
  rw [cornerWPoly]
  trans
      (realMatrixToProbePoly (cornerKPrefix r θ l.val)).map
          (MvPolynomial.eval (probePolyEval w v)) *ᵥ
        (fun i => MvPolynomial.eval (probePolyEval w v) (probePolyW i))
  · exact probePoly_eval_mulVec (probePolyEval w v)
      (realMatrixToProbePoly (cornerKPrefix r θ l.val)) probePolyW
  · simp

@[simp]
theorem eval_cornerVPoly {L k d : Nat} (r : Nat) (θ : Params L k d)
    (l : Fin L) (w v : Vec d) :
    (fun i => MvPolynomial.eval (probePolyEval w v) (cornerVPoly r θ l i)) =
      cornerCPrefix θ l.val *ᵥ v + cornerDPrefix r θ l.val *ᵥ w := by
  ext i
  simp [cornerVPoly, Matrix.mulVec, dotProduct, realMatrixToProbePoly]

@[simp]
theorem eval_cornerSlopeDiffPoly {L k d : Nat} (r : Nat) (θ : Params L k d)
    (l : Fin L) (a c : Fin k) (w v : Vec d) :
    MvPolynomial.eval (probePolyEval w v) (cornerSlopeDiffPoly r θ l a c) =
      matrixBilin (attentionMatrix θ l a - attentionMatrix θ l c)
        (cornerKPrefix r θ l.val *ᵥ w)
        (cornerCPrefix θ l.val *ᵥ v + cornerDPrefix r θ l.val *ᵥ w) := by
  simp [cornerSlopeDiffPoly, matrixBilin]

/-- A probe polynomial is nonzero iff it has a nonzero real probe evaluation. -/
theorem probePoly_ne_zero_iff_exists_eval_ne_zero {d : Nat} (p : ProbePoly d) :
    p ≠ 0 ↔ ∃ w v : Vec d, MvPolynomial.eval (probePolyEval w v) p ≠ 0 := by
  rw [realMvPolynomial_ne_zero_iff_exists_eval_ne_zero]
  constructor
  · rintro ⟨ρ, hρ⟩
    have hEval :
        probePolyEval (fun i => ρ (Sum.inl i)) (fun i => ρ (Sum.inr i)) = ρ := by
      funext x
      cases x <;> rfl
    exact ⟨fun i => ρ (Sum.inl i), fun i => ρ (Sum.inr i), by simpa [hEval] using hρ⟩
  · rintro ⟨w, v, hne⟩
    exact ⟨probePolyEval w v, hne⟩

/-- Corner slope separation is equivalent to one nonzero real probe evaluation. -/
theorem cornerSlopeDiffPoly_ne_zero_iff_exists_eval_ne_zero {L k d : Nat}
    (r : Nat) (θ : Params L k d) (l : Fin L) (a c : Fin k) :
    cornerSlopeDiffPoly r θ l a c ≠ 0 ↔
      ∃ w v : Vec d,
        matrixBilin (attentionMatrix θ l a - attentionMatrix θ l c)
          (cornerKPrefix r θ l.val *ᵥ w)
          (cornerCPrefix θ l.val *ᵥ v + cornerDPrefix r θ l.val *ᵥ w) ≠ 0 := by
  rw [probePoly_ne_zero_iff_exists_eval_ne_zero]
  constructor
  · rintro ⟨w, v, hne⟩
    exact ⟨w, v, by simpa using hne⟩
  · rintro ⟨w, v, hne⟩
    exact ⟨w, v, by simpa using hne⟩

/-- Corner slope separation can be witnessed inside any product of infinite coordinate
sets for the probe variables. -/
theorem cornerSlopeDiffPoly_ne_zero_iff_exists_eval_ne_zero_on_pi {L k d : Nat}
    (r : Nat) (θ : Params L k d) (l : Fin L) (a c : Fin k)
    (sw sv : Fin d → Set ℝ)
    (hsw : ∀ i, (sw i).Infinite) (hsv : ∀ i, (sv i).Infinite) :
    cornerSlopeDiffPoly r θ l a c ≠ 0 ↔
      ∃ w v : Vec d,
        (∀ i, w i ∈ sw i) ∧ (∀ i, v i ∈ sv i) ∧
          matrixBilin (attentionMatrix θ l a - attentionMatrix θ l c)
            (cornerKPrefix r θ l.val *ᵥ w)
            (cornerCPrefix θ l.val *ᵥ v + cornerDPrefix r θ l.val *ᵥ w) ≠ 0 := by
  rw [probePoly_ne_zero_iff_exists_eval_ne_zero_on_pi
    (p := cornerSlopeDiffPoly r θ l a c) sw sv hsw hsv]
  constructor
  · rintro ⟨w, v, hw, hv, hne⟩
    exact ⟨w, v, hw, hv, by simpa using hne⟩
  · rintro ⟨w, v, hw, hv, hne⟩
    exact ⟨w, v, hw, hv, by simpa using hne⟩

/-! ## Regularity and local openness -/

/-- `K03B.E.def-regularity.S/P`: concrete target-side regularity clauses. -/
structure Regularity {L k d : Nat} (r : Nat) (θ : Params L k d) : Prop where
  det_attention_ne_zero :
    ∀ l : Fin L, ∀ a : Fin k, (attentionMatrix θ l a).det ≠ 0
  sym_attention_ne_zero :
    ∀ l : Fin L, ∀ a : Fin k, matrixFrobSq (sym (attentionMatrix θ l a)) ≠ 0
  value_ne_zero :
    ∀ l : Fin L, ∀ a : Fin k, matrixFrobSq (valueMatrix θ l a) ≠ 0
  head_separation :
    ∀ l : Fin L, ∀ a c : Fin k, a ≠ c →
      matrixFrobSq (attentionMatrix θ l a - attentionMatrix θ l c) ≠ 0
  corner_slope_separation :
    ∀ l : Fin L, ∀ a c : Fin k, a ≠ c →
      cornerSlopeDiffPoly r θ l a c ≠ 0

namespace Regularity

theorem symAttentionMatrix_ne_zero {L k d : Nat} {r : Nat} {θ : Params L k d}
    (hθ : Regularity r θ) (l : Fin L) (a : Fin k) :
    sym (attentionMatrix θ l a) ≠ 0 :=
  (matrixFrobSq_ne_zero_iff _).mp (hθ.sym_attention_ne_zero l a)

theorem valueMatrix_ne_zero {L k d : Nat} {r : Nat} {θ : Params L k d}
    (hθ : Regularity r θ) (l : Fin L) (a : Fin k) :
    valueMatrix θ l a ≠ 0 :=
  (matrixFrobSq_ne_zero_iff _).mp (hθ.value_ne_zero l a)

theorem headAttention_ne {L k d : Nat} {r : Nat} {θ : Params L k d}
    (hθ : Regularity r θ) (l : Fin L) {a c : Fin k} (hac : a ≠ c) :
    attentionMatrix θ l a ≠ attentionMatrix θ l c :=
  (matrixFrobSq_sub_ne_zero_iff _ _).mp (hθ.head_separation l a c hac)

theorem exists_cornerSlope_eval_ne_zero {L k d : Nat} {r : Nat}
    {θ : Params L k d} (hθ : Regularity r θ)
    (l : Fin L) {a c : Fin k} (hac : a ≠ c) :
    ∃ w v : Vec d,
      matrixBilin (attentionMatrix θ l a - attentionMatrix θ l c)
        (cornerKPrefix r θ l.val *ᵥ w)
        (cornerCPrefix θ l.val *ᵥ v + cornerDPrefix r θ l.val *ᵥ w) ≠ 0 :=
  (cornerSlopeDiffPoly_ne_zero_iff_exists_eval_ne_zero r θ l a c).mp
    (hθ.corner_slope_separation l a c hac)

theorem exists_cornerSlope_eval_ne_zero_on_pi {L k d : Nat} {r : Nat}
    {θ : Params L k d} (hθ : Regularity r θ)
    (l : Fin L) {a c : Fin k} (hac : a ≠ c)
    (sw sv : Fin d → Set ℝ)
    (hsw : ∀ i, (sw i).Infinite) (hsv : ∀ i, (sv i).Infinite) :
    ∃ w v : Vec d,
      (∀ i, w i ∈ sw i) ∧ (∀ i, v i ∈ sv i) ∧
        matrixBilin (attentionMatrix θ l a - attentionMatrix θ l c)
          (cornerKPrefix r θ l.val *ᵥ w)
          (cornerCPrefix θ l.val *ᵥ v + cornerDPrefix r θ l.val *ᵥ w) ≠ 0 :=
  (cornerSlopeDiffPoly_ne_zero_iff_exists_eval_ne_zero_on_pi
    r θ l a c sw sv hsw hsv).mp (hθ.corner_slope_separation l a c hac)

end Regularity

/-- The causal softmax matrix at zero logits, `Gamma_0`. -/
noncomputable def gammaZero (r : Nat) :
    Matrix (Fin (seqLength r)) (Fin (seqLength r)) ℝ :=
  softmaxColC (0 : Matrix (Fin (seqLength r)) (Fin (seqLength r)) ℝ)

/-- Matrix basis vector for flattening finite matrix operators. -/
noncomputable def matrixBasis {m n : Nat} (p : Fin m × Fin n) :
    Matrix (Fin m) (Fin n) ℝ :=
  fun i j => if (i, j) = p then 1 else 0

@[simp]
theorem matrixBasis_self {m n : Nat} (p : Fin m × Fin n) :
    matrixBasis p p.1 p.2 = 1 := by
  simp [matrixBasis]

theorem matrixBasis_of_ne {m n : Nat} {p q : Fin m × Fin n} (hpq : p ≠ q) :
    matrixBasis q p.1 p.2 = 0 := by
  simp [matrixBasis, hpq]

/-- Matrix of a function on finite matrices in the coordinate basis `matrixBasis`. -/
noncomputable def matrixOperatorMatrix {m n : Nat}
    (F : Matrix (Fin m) (Fin n) ℝ → Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℝ :=
  fun p q => F (matrixBasis q) p.1 p.2

@[simp]
theorem matrixOperatorMatrix_apply {m n : Nat}
    (F : Matrix (Fin m) (Fin n) ℝ → Matrix (Fin m) (Fin n) ℝ)
    (p q : Fin m × Fin n) :
    matrixOperatorMatrix F p q = F (matrixBasis q) p.1 p.2 :=
  rfl

@[simp]
theorem matrixOperatorMatrix_id {m n : Nat} :
    matrixOperatorMatrix (fun H : Matrix (Fin m) (Fin n) ℝ => H) = 1 := by
  ext p q
  by_cases hpq : p = q
  · subst q
    simp [matrixBasis]
  · simp [matrixBasis, hpq]

/-- The derivative operator from TeX Definition `local-openness`. -/
noncomputable def localDerivative {L k d : Nat} (r : Nat) (θ : Params L k d)
    (l : Fin L) (H : Matrix (Fin d) (Fin (seqLength r)) ℝ) :
    Matrix (Fin d) (Fin (seqLength r)) ℝ :=
  H + ∑ a : Fin k, valueMatrix θ l a * H * gammaZero r

@[simp]
theorem localDerivative_zero {L k d : Nat} (r : Nat) (θ : Params L k d)
    (l : Fin L) :
    localDerivative r θ l (0 : Matrix (Fin d) (Fin (seqLength r)) ℝ) = 0 := by
  simp [localDerivative]

theorem localDerivative_add {L k d : Nat} (r : Nat) (θ : Params L k d)
    (l : Fin L) (H K : Matrix (Fin d) (Fin (seqLength r)) ℝ) :
    localDerivative r θ l (H + K) =
      localDerivative r θ l H + localDerivative r θ l K := by
  ext i j
  simp [localDerivative, Matrix.add_mul, Matrix.mul_add, Finset.sum_add_distrib,
    add_assoc, add_left_comm]

theorem localDerivative_smul {L k d : Nat} (r : Nat) (θ : Params L k d)
    (l : Fin L) (c : ℝ) (H : Matrix (Fin d) (Fin (seqLength r)) ℝ) :
    localDerivative r θ l (c • H) = c • localDerivative r θ l H := by
  simp [localDerivative, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum, smul_add]

/-- The local derivative packaged as a real linear map. -/
noncomputable def localDerivativeLinearMap {L k d : Nat} (r : Nat)
    (θ : Params L k d) (l : Fin L) :
    Matrix (Fin d) (Fin (seqLength r)) ℝ →ₗ[ℝ]
      Matrix (Fin d) (Fin (seqLength r)) ℝ where
  toFun := localDerivative r θ l
  map_add' := localDerivative_add r θ l
  map_smul' := localDerivative_smul r θ l

@[simp]
theorem localDerivativeLinearMap_apply {L k d : Nat} (r : Nat)
    (θ : Params L k d) (l : Fin L)
    (H : Matrix (Fin d) (Fin (seqLength r)) ℝ) :
    localDerivativeLinearMap r θ l H = localDerivative r θ l H :=
  rfl

/-- Determinant of the flattened local derivative operator. -/
noncomputable def localOpennessDet {L k d : Nat} (r : Nat) (θ : Params L k d)
    (l : Fin L) : ℝ :=
  (matrixOperatorMatrix (localDerivative r θ l)).det

/-- `K03B.E.def-local-openness.S/P`: every layer derivative is invertible at zero. -/
def LocalOpenness {L k d : Nat} (r : Nat) (θ : Params L k d) : Prop :=
  ∀ l : Fin L, localOpennessDet r θ l ≠ 0

end TransformerIdentifiability.NLayer.KHead
