import AnyLayerIdentifiabilityProof.NLayer.Analytic.AlgebraicQuadric
import AnyLayerIdentifiabilityProof.NLayer.Foundations.PolynomialGenericity

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer

open Matrix

/-!
# Step 0/1 generic probe region

Owner shard for the concrete Step 1 theorem statement, `kappa_j`, `O_star`, the
nonvanishing/genericity hypotheses, the visible coordinate choice, and the real-tail
observable agreement interface.
-/

/-- A constant-probe pair `(w, v)`. -/
abbrev ProbePair (d : Nat) : Type :=
  (Fin d -> ℝ) × (Fin d -> ℝ)

/-- The variable type for real polynomials in the probe coordinates.  The first
component selects the `w` or `v` block, and the second component selects the coordinate. -/
abbrev ProbeVar (d : Nat) : Type :=
  Fin 2 × Fin d

/-- Evaluation of a probe-coordinate polynomial at a concrete pair `(w, v)`. -/
def probeEval {d : Nat} (p : ProbePair d) : ProbeVar d -> ℝ :=
  fun x => if x.1 = 0 then p.1 x.2 else p.2 x.2

/-- A real-valued function on probe pairs is represented by a real multivariate
polynomial in the `w` and `v` coordinates. -/
def IsProbePolynomial (d : Nat) (f : ProbePair d -> ℝ) : Prop :=
  ∃ p : MvPolynomial (ProbeVar d) ℝ,
    ∀ x : ProbePair d, MvPolynomial.eval (probeEval x) p = f x

/-- A represented probe polynomial whose representing polynomial is not identically zero. -/
def IsNonzeroProbePolynomial (d : Nat) (f : ProbePair d -> ℝ) : Prop :=
  ∃ p : MvPolynomial (ProbeVar d) ℝ,
    p ≠ 0 ∧ ∀ x : ProbePair d, MvPolynomial.eval (probeEval x) p = f x

theorem IsNonzeroProbePolynomial.isPolynomial {d : Nat} {f : ProbePair d -> ℝ}
    (h : IsNonzeroProbePolynomial d f) :
    IsProbePolynomial d f := by
  rcases h with ⟨p, _hp, h_eval⟩
  exact ⟨p, h_eval⟩

/-- Convert probe-coordinate functions back to probe pairs. -/
def probeOfEval {d : Nat} (x : ProbeVar d -> ℝ) : ProbePair d :=
  (fun i => x ((0 : Fin 2), i), fun i => x ((1 : Fin 2), i))

@[simp]
theorem probeEval_probeOfEval {d : Nat} (x : ProbeVar d -> ℝ) :
    probeEval (probeOfEval x) = x := by
  funext a
  rcases a with ⟨b, i⟩
  by_cases h0 : b = 0
  · subst b
    simp [probeEval, probeOfEval]
  · have h1 : b = 1 := by
      apply Fin.ext
      omega
    subst b
    simp [probeEval, probeOfEval]

@[simp]
theorem probeOfEval_probeEval {d : Nat} (p : ProbePair d) :
    probeOfEval (probeEval p) = p := by
  ext i <;> simp [probeEval, probeOfEval]

theorem continuous_probeEval {d : Nat} :
    Continuous (probeEval : ProbePair d -> ProbeVar d -> ℝ) := by
  refine continuous_pi ?_
  intro a
  by_cases h : a.1 = 0
  · simpa [probeEval, h] using
      (continuous_apply a.2).comp (continuous_fst : Continuous fun p : ProbePair d => p.1)
  · simpa [probeEval, h] using
      (continuous_apply a.2).comp (continuous_snd : Continuous fun p : ProbePair d => p.2)

theorem continuous_probeOfEval {d : Nat} :
    Continuous (probeOfEval : (ProbeVar d -> ℝ) -> ProbePair d) := by
  have hw : Continuous (fun x : ProbeVar d -> ℝ =>
      fun i : Fin d => x ((0 : Fin 2), i)) :=
    continuous_pi fun i => continuous_apply ((0 : Fin 2), i)
  have hv : Continuous (fun x : ProbeVar d -> ℝ =>
      fun i : Fin d => x ((1 : Fin 2), i)) :=
    continuous_pi fun i => continuous_apply ((1 : Fin 2), i)
  exact hw.prodMk hv

/-- Probe pairs are homeomorphic to their flat coordinate functions. -/
def probeEvalHomeomorph (d : Nat) : ProbePair d ≃ₜ (ProbeVar d -> ℝ) where
  toFun := probeEval
  invFun := probeOfEval
  left_inv := probeOfEval_probeEval
  right_inv := probeEval_probeOfEval
  continuous_toFun := continuous_probeEval
  continuous_invFun := continuous_probeOfEval

theorem IsProbePolynomial.continuous {d : Nat} {f : ProbePair d -> ℝ}
    (h : IsProbePolynomial d f) :
    Continuous f := by
  rcases h with ⟨p, hp⟩
  have hpoly : Continuous (fun x : ProbePair d => MvPolynomial.eval (probeEval x) p) :=
    (MvPolynomial.continuous_eval p).comp continuous_probeEval
  have hEq : (fun x : ProbePair d => MvPolynomial.eval (probeEval x) p) = f := by
    funext x
    exact hp x
  simpa [hEq] using hpoly

theorem IsProbePolynomial.isOpen_ne_zero {d : Nat} {f : ProbePair d -> ℝ}
    (h : IsProbePolynomial d f) :
    IsOpen {x : ProbePair d | f x ≠ 0} := by
  simpa using (h.continuous.isOpen_preimage {y : ℝ | y ≠ 0} isOpen_ne)

theorem IsNonzeroProbePolynomial.isOpen_ne_zero {d : Nat} {f : ProbePair d -> ℝ}
    (h : IsNonzeroProbePolynomial d f) :
    IsOpen {x : ProbePair d | f x ≠ 0} :=
  h.isPolynomial.isOpen_ne_zero

theorem IsNonzeroProbePolynomial.dense_ne_zero {d : Nat} {f : ProbePair d -> ℝ}
    (h : IsNonzeroProbePolynomial d f) :
    Dense {x : ProbePair d | f x ≠ 0} := by
  rcases h with ⟨p, hp_ne, hp_eval⟩
  have hdense :
      Dense {x : ProbeVar d -> ℝ | MvPolynomial.eval x p ≠ 0} :=
    dense_compl_zero_set p hp_ne
  have hpre :
      Dense ((probeEval : ProbePair d -> ProbeVar d -> ℝ) ⁻¹'
        {x : ProbeVar d -> ℝ | MvPolynomial.eval x p ≠ 0}) :=
    hdense.preimage (probeEvalHomeomorph d).isOpenMap
  have hset :
      ((probeEval : ProbePair d -> ProbeVar d -> ℝ) ⁻¹'
        {x : ProbeVar d -> ℝ | MvPolynomial.eval x p ≠ 0})
        = {x : ProbePair d | f x ≠ 0} := by
    ext x
    simp [hp_eval x]
  simpa [hset] using hpre

/-- One layer of parameters, used for infinite formal layer streams. -/
abbrev Layer (d : Nat) : Type :=
  Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ

/-- A stream of layers.  Formal slope-polynomial APIs are naturally indexed by `Nat`. -/
abbrev LayerStream (d : Nat) : Type :=
  Nat -> Layer d

/-- Extend finite network parameters to a `Nat`-indexed stream.  Out-of-range layers are
zero and are irrelevant for all statements that carry their depth bounds. -/
noncomputable def paramStream {L d : Nat} (θ : Params L d) : LayerStream d :=
  fun n => if h : n < L then θ ⟨n, h⟩ else (0, 0)

@[simp]
theorem paramStream_apply_of_lt {L d n : Nat} (θ : Params L d) (h : n < L) :
    paramStream θ n = θ ⟨n, h⟩ := by
  simp [paramStream, h]

@[simp]
theorem paramStream_apply_of_not_lt {L d n : Nat} (θ : Params L d) (h : ¬ n < L) :
    paramStream θ n = (0, 0) := by
  simp [paramStream, h]

/-- Product `V_{n-1} ... V_0` over the real value matrices of a layer stream. -/
noncomputable def realVprod {d : Nat} (θ : LayerStream d) :
    Nat -> Matrix (Fin d) (Fin d) ℝ
  | 0 => 1
  | n + 1 => (θ n).1 * realVprod θ n

@[simp]
theorem realVprod_zero {d : Nat} (θ : LayerStream d) :
    realVprod θ 0 = 1 := rfl

@[simp]
theorem realVprod_succ {d : Nat} (θ : LayerStream d) (n : Nat) :
    realVprod θ (n + 1) = (θ n).1 * realVprod θ n := rfl

/-- Symmetric part of a real square matrix.  The quadratic form agrees with the original
matrix, but this is the exact form used in the TeX definition of `kappa_j`. -/
noncomputable def symPart {d : Nat} (M : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  ((1 / 2 : ℝ) • (M + Mᵀ))

/-- Matrix appearing in `kappa_{n+2}` for a zero-based layer stream. -/
noncomputable def kappaMatrix {d : Nat} (θ : LayerStream d) (n : Nat) :
    Matrix (Fin d) (Fin d) ℝ :=
  symPart ((realVprod θ (n + 1))ᵀ * (θ (n + 1)).2 * realVprod θ (n + 1))

/-- Zero-based form of the TeX quantity
`w^T Sym(V'_{j-1:1}^T A'_j V'_{j-1:1}) w`; this is `kappa_{n+2}`. -/
noncomputable def kappaIndex {d : Nat} (θ : LayerStream d) (n : Nat)
    (w : Fin d -> ℝ) : ℝ :=
  matrixBilin (kappaMatrix θ n) w w

/-- One-based `kappa_j`; meaningful for `2 <= j`, where it is `kappaIndex (j - 2)`. -/
noncomputable def kappa_j {d : Nat} (θ : LayerStream d) (j : Nat)
    (w : Fin d -> ℝ) : ℝ :=
  kappaIndex θ (j - 2) w

@[simp]
theorem kappa_j_add_two {d : Nat} (θ : LayerStream d) (n : Nat)
    (w : Fin d -> ℝ) :
    kappa_j θ (n + 2) w = kappaIndex θ n w := by
  simp [kappa_j]

/-- Finite-parameter wrapper for `kappa_j`. -/
noncomputable def kappaParam_j {L d : Nat} (θ : Params L d) (j : Nat)
    (w : Fin d -> ℝ) : ℝ :=
  kappa_j (paramStream θ) j w

/-- The first attention matrix, with a harmless zero fallback when `L = 0`. -/
noncomputable def firstAttention {L d : Nat} (θ : Params L d) :
    Matrix (Fin d) (Fin d) ℝ :=
  (paramStream θ 0).2

theorem firstAttention_eq_of_pos {L d : Nat} (θ : Params L d) (hL : 0 < L) :
    firstAttention θ = (θ ⟨0, hL⟩).2 := by
  simp [firstAttention, hL]

/-- The first-layer slope `w^T A_1 v`. -/
noncomputable def firstSlope {L d : Nat} (θ : Params L d)
    (w v : Fin d -> ℝ) : ℝ :=
  matrixBilin (firstAttention θ) w v

/-! ## Concrete probe-coordinate polynomials -/

/-- The `w_i` probe-coordinate polynomial. -/
noncomputable def probeWVar {d : Nat} (i : Fin d) :
    MvPolynomial (ProbeVar d) ℝ :=
  MvPolynomial.X ((0 : Fin 2), i)

/-- The `v_i` probe-coordinate polynomial. -/
noncomputable def probeVVar {d : Nat} (i : Fin d) :
    MvPolynomial (ProbeVar d) ℝ :=
  MvPolynomial.X ((1 : Fin 2), i)

@[simp]
theorem eval_probeWVar {d : Nat} (p : ProbePair d) (i : Fin d) :
    MvPolynomial.eval (probeEval p) (probeWVar i) = p.1 i := by
  simp [probeWVar, probeEval]

@[simp]
theorem eval_probeVVar {d : Nat} (p : ProbePair d) (i : Fin d) :
    MvPolynomial.eval (probeEval p) (probeVVar i) = p.2 i := by
  simp [probeVVar, probeEval]

/-- Probe-coordinate polynomial for `wᵀ A v`. -/
noncomputable def matrixBilinProbePoly {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) :
    MvPolynomial (ProbeVar d) ℝ :=
  ∑ i : Fin d, ∑ j : Fin d,
    MvPolynomial.C (A i j) * probeWVar i * probeVVar j

/-- Probe-coordinate polynomial for the quadratic form `wᵀ A w`. -/
noncomputable def matrixQuadProbePoly {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) :
    MvPolynomial (ProbeVar d) ℝ :=
  ∑ i : Fin d, ∑ j : Fin d,
    MvPolynomial.C (A i j) * probeWVar i * probeWVar j

/-- Probe-coordinate polynomial for the `i`th coordinate of `A *ᵥ w`. -/
noncomputable def matrixMulVecCoordProbePoly {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) :
    MvPolynomial (ProbeVar d) ℝ :=
  ∑ j : Fin d, MvPolynomial.C (A i j) * probeWVar j

theorem eval_matrixBilinProbePoly {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (p : ProbePair d) :
    MvPolynomial.eval (probeEval p) (matrixBilinProbePoly A) =
      matrixBilin A p.1 p.2 := by
  simp only [matrixBilinProbePoly, MvPolynomial.eval_sum, MvPolynomial.eval_mul,
    MvPolynomial.eval_C, eval_probeWVar, eval_probeVVar]
  unfold matrixBilin
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  ring

theorem eval_matrixQuadProbePoly {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (p : ProbePair d) :
    MvPolynomial.eval (probeEval p) (matrixQuadProbePoly A) =
      matrixBilin A p.1 p.1 := by
  simp only [matrixQuadProbePoly, MvPolynomial.eval_sum, MvPolynomial.eval_mul,
    MvPolynomial.eval_C, eval_probeWVar]
  unfold matrixBilin
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  ring

theorem eval_matrixMulVecCoordProbePoly {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) (p : ProbePair d) :
    MvPolynomial.eval (probeEval p) (matrixMulVecCoordProbePoly A i) =
      (A *ᵥ p.1) i := by
  simp [matrixMulVecCoordProbePoly, Matrix.mulVec, dotProduct]

theorem matrix_mulVec_single_one {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) :
    (A *ᵥ Pi.single j 1) i = A i j := by
  classical
  have h := matrixBilin_single_single A i j
  simpa [matrixBilin, dotProduct] using h

theorem matrixBilin_add_left {d : Nat} (A : Matrix (Fin d) (Fin d) ℝ)
    (u v w : Fin d -> ℝ) :
    matrixBilin A (u + v) w = matrixBilin A u w + matrixBilin A v w := by
  simp [matrixBilin, add_dotProduct]

theorem matrixBilin_add_right {d : Nat} (A : Matrix (Fin d) (Fin d) ℝ)
    (u v w : Fin d -> ℝ) :
    matrixBilin A u (v + w) = matrixBilin A u v + matrixBilin A u w := by
  simp [matrixBilin, Matrix.mulVec_add, dotProduct_add]

theorem exists_matrix_entry_ne_zero_of_ne_zero {d : Nat}
    {A : Matrix (Fin d) (Fin d) ℝ} (hA : A ≠ 0) :
    ∃ i j : Fin d, A i j ≠ 0 := by
  classical
  by_contra hnone
  apply hA
  ext i j
  by_contra hij
  exact hnone ⟨i, j, hij⟩

theorem matrixBilinProbePoly_ne_zero_of_matrix_ne_zero {d : Nat}
    {A : Matrix (Fin d) (Fin d) ℝ} (hA : A ≠ 0) :
    matrixBilinProbePoly A ≠ 0 := by
  classical
  rcases exists_matrix_entry_ne_zero_of_ne_zero hA with ⟨i, j, hij⟩
  intro hpoly
  have hzero :
      matrixBilin A (Pi.single i 1) (Pi.single j 1) = 0 := by
    have heval := eval_matrixBilinProbePoly A
      ((Pi.single i 1), (Pi.single j 1))
    simpa [hpoly] using heval.symm
  exact hij (by simpa [matrixBilin_single_single] using hzero)

theorem matrixMulVecCoordProbePoly_ne_zero_of_entry_ne_zero {d : Nat}
    {A : Matrix (Fin d) (Fin d) ℝ} {i j : Fin d} (hij : A i j ≠ 0) :
    matrixMulVecCoordProbePoly A i ≠ 0 := by
  classical
  intro hpoly
  let p : ProbePair d := (Pi.single j 1, 0)
  have hzero : (A *ᵥ p.1) i = 0 := by
    have heval := eval_matrixMulVecCoordProbePoly A i p
    simpa [hpoly] using heval.symm
  exact hij (by simpa [p, matrix_mulVec_single_one] using hzero)

theorem matrixQuad_eq_zero_of_forall_self_bilin_eq_zero_of_symmetric {d : Nat}
    {A : Matrix (Fin d) (Fin d) ℝ}
    (hsym : Aᵀ = A)
    (hquad : ∀ w : Fin d -> ℝ, matrixBilin A w w = 0) :
    A = 0 := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    simpa [matrixBilin_single_single] using hquad (Pi.single i 1)
  · have hii : A i i = 0 := by
      simpa [matrixBilin_single_single] using hquad (Pi.single i 1)
    have hjj : A j j = 0 := by
      simpa [matrixBilin_single_single] using hquad (Pi.single j 1)
    have hsum := hquad (Pi.single i 1 + Pi.single j 1)
    have hji : A j i = A i j := by
      have hentry := congr_fun (congr_fun hsym j) i
      simpa [Matrix.transpose_apply] using hentry.symm
    have htwo : (2 : ℝ) * A i j = 0 := by
      have hpolar :
          matrixBilin A (Pi.single i 1 + Pi.single j 1)
              (Pi.single i 1 + Pi.single j 1)
            = A i i + A i j + A j i + A j j := by
        rw [matrixBilin_add_left, matrixBilin_add_right, matrixBilin_add_right]
        simp [matrixBilin_single_single]
        ring
      nlinarith [hsum, hpolar, hii, hjj, hji]
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

theorem exists_matrixBilin_self_ne_zero_of_transpose_eq_self_ne_zero {d : Nat}
    {A : Matrix (Fin d) (Fin d) ℝ} (hsym : Aᵀ = A) (hA : A ≠ 0) :
    ∃ w : Fin d -> ℝ, matrixBilin A w w ≠ 0 := by
  classical
  by_contra hnone
  apply hA
  exact matrixQuad_eq_zero_of_forall_self_bilin_eq_zero_of_symmetric hsym (by
    intro w
    by_contra hw
    exact hnone ⟨w, hw⟩)

theorem matrixQuadProbePoly_ne_zero_of_symmetric_matrix_ne_zero {d : Nat}
    {A : Matrix (Fin d) (Fin d) ℝ} (hsym : Aᵀ = A) (hA : A ≠ 0) :
    matrixQuadProbePoly A ≠ 0 := by
  classical
  rcases exists_matrixBilin_self_ne_zero_of_transpose_eq_self_ne_zero hsym hA with
    ⟨w, hw⟩
  intro hpoly
  let p : ProbePair d := (w, 0)
  have hzero : matrixBilin A w w = 0 := by
    have heval := eval_matrixQuadProbePoly A p
    simpa [p, hpoly] using heval.symm
  exact hw hzero

theorem symPart_transpose {d : Nat} (A : Matrix (Fin d) (Fin d) ℝ) :
    (symPart A)ᵀ = symPart A := by
  ext i j
  simp [symPart, Matrix.transpose_apply, add_comm, mul_add]

theorem kappaMatrix_transpose {d : Nat} (θ : LayerStream d) (n : Nat) :
    (kappaMatrix θ n)ᵀ = kappaMatrix θ n :=
  symPart_transpose _

theorem firstSlope_isNonzeroProbePolynomial_of_firstAttention_ne_zero {L d : Nat}
    {θ : Params L d} (hA : firstAttention θ ≠ 0) :
    IsNonzeroProbePolynomial d (fun p : ProbePair d => firstSlope θ p.1 p.2) :=
  ⟨matrixBilinProbePoly (firstAttention θ),
    matrixBilinProbePoly_ne_zero_of_matrix_ne_zero hA,
    by
      intro p
      simpa [firstSlope] using eval_matrixBilinProbePoly (firstAttention θ) p⟩

theorem kappaParam_isNonzeroProbePolynomial_of_kappaMatrix_ne_zero {L d : Nat}
    {θ : Params L d} {j : Nat}
    (hKappa : kappaMatrix (paramStream θ) (j - 2) ≠ 0) :
    IsNonzeroProbePolynomial d (fun p : ProbePair d => kappaParam_j θ j p.1) :=
  ⟨matrixQuadProbePoly (kappaMatrix (paramStream θ) (j - 2)),
    matrixQuadProbePoly_ne_zero_of_symmetric_matrix_ne_zero
      (kappaMatrix_transpose (paramStream θ) (j - 2)) hKappa,
    by
      intro p
      simpa [kappaParam_j, kappa_j, kappaIndex] using
        eval_matrixQuadProbePoly (kappaMatrix (paramStream θ) (j - 2)) p⟩

/-- The visible real tail vector `V_L ... V_1 w`. -/
noncomputable def visibleTailVector {L d : Nat} (θ : Params L d)
    (w : Fin d -> ℝ) : Fin d -> ℝ :=
  realVprod (paramStream θ) L *ᵥ w

/-- A scalar visible coordinate `e_i^T V_L ... V_1 w`. -/
noncomputable def visibleTailCoord {L d : Nat} (θ : Params L d)
    (w : Fin d -> ℝ) (i : Fin d) : ℝ :=
  visibleTailVector θ w i

theorem visibleTailCoord_isProbePolynomial {L d : Nat} (θ : Params L d)
    (i : Fin d) :
    IsProbePolynomial d (fun p : ProbePair d => visibleTailCoord θ p.1 i) :=
  ⟨matrixMulVecCoordProbePoly (realVprod (paramStream θ) L) i, by
    intro p
    simpa [visibleTailCoord, visibleTailVector] using
      eval_matrixMulVecCoordProbePoly (realVprod (paramStream θ) L) i p⟩

theorem visibleTailCoord_isNonzeroProbePolynomial_of_entry_ne_zero {L d : Nat}
    {θ : Params L d} {i j : Fin d}
    (hij : realVprod (paramStream θ) L i j ≠ 0) :
    IsNonzeroProbePolynomial d (fun p : ProbePair d => visibleTailCoord θ p.1 i) :=
  ⟨matrixMulVecCoordProbePoly (realVprod (paramStream θ) L) i,
    matrixMulVecCoordProbePoly_ne_zero_of_entry_ne_zero hij,
    by
      intro p
      simpa [visibleTailCoord, visibleTailVector] using
        eval_matrixMulVecCoordProbePoly (realVprod (paramStream θ) L) i p⟩

theorem visibleCoord_nonzero_of_visibleTailMatrix_ne_zero {L d : Nat}
    {θ : Params L d}
    (hV : realVprod (paramStream θ) L ≠ 0) :
    ∃ i : Fin d,
      IsNonzeroProbePolynomial d (fun p : ProbePair d => visibleTailCoord θ p.1 i) := by
  rcases exists_matrix_entry_ne_zero_of_ne_zero hV with ⟨i, j, hij⟩
  exact ⟨i, visibleTailCoord_isNonzeroProbePolynomial_of_entry_ne_zero hij⟩

/-- The concrete Step 0 generic probe region

`O_star = {(w,v) in O : w^T A'_1 v != 0, kappa_j(w) != 0 for 2 <= j <= L,
V'_{L:1} w != 0}`.
-/
noncomputable def O_star {L d : Nat} (θ' : Params L d) (O : Set (ProbePair d)) :
    Set (ProbePair d) :=
  {p | p ∈ O
    ∧ firstSlope θ' p.1 p.2 ≠ 0
    ∧ (∀ j : Nat, 2 ≤ j -> j ≤ L -> kappaParam_j θ' j p.1 ≠ 0)
    ∧ visibleTailVector θ' p.1 ≠ 0}

theorem O_star_mem_base {L d : Nat} {θ' : Params L d} {O : Set (ProbePair d)}
    {p : ProbePair d} (hp : p ∈ O_star θ' O) :
    p ∈ O :=
  hp.1

theorem O_star_firstSlope_ne {L d : Nat} {θ' : Params L d} {O : Set (ProbePair d)}
    {p : ProbePair d} (hp : p ∈ O_star θ' O) :
    firstSlope θ' p.1 p.2 ≠ 0 :=
  hp.2.1

theorem O_star_kappa_ne {L d : Nat} {θ' : Params L d} {O : Set (ProbePair d)}
    {p : ProbePair d} (hp : p ∈ O_star θ' O) {j : Nat}
    (hj2 : 2 ≤ j) (hjL : j ≤ L) :
    kappaParam_j θ' j p.1 ≠ 0 :=
  hp.2.2.1 j hj2 hjL

theorem O_star_visibleTailVector_ne {L d : Nat} {θ' : Params L d}
    {O : Set (ProbePair d)} {p : ProbePair d} (hp : p ∈ O_star θ' O) :
    visibleTailVector θ' p.1 ≠ 0 :=
  hp.2.2.2

/-- The finite set of one-based kappa indices appearing in `O_star`. -/
def kappaIndexFinset (L : Nat) : Finset Nat :=
  (Finset.range (L + 1)).filter fun j => 2 ≤ j

@[simp]
theorem mem_kappaIndexFinset {L j : Nat} :
    j ∈ kappaIndexFinset L ↔ 2 ≤ j ∧ j ≤ L := by
  constructor
  · intro hj
    exact ⟨(Finset.mem_filter.mp hj).2,
      Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)⟩
  · rintro ⟨hj2, hjL⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hjL), hj2⟩

/-- A finite intersection of open dense sets is dense. -/
theorem dense_biInter_finset_of_isOpen {α X : Type*} [TopologicalSpace X]
    [DecidableEq α] (s : Finset α) (f : α -> Set X)
    (ho : ∀ i ∈ s, IsOpen (f i)) (hd : ∀ i ∈ s, Dense (f i)) :
    Dense (⋂ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert a s has ih =>
      have hs_open : ∀ i ∈ s, IsOpen (f i) := fun i hi =>
        ho i (Finset.mem_insert_of_mem hi)
      have hs_dense : ∀ i ∈ s, Dense (f i) := fun i hi =>
        hd i (Finset.mem_insert_of_mem hi)
      have htail : Dense (⋂ i ∈ s, f i) := ih hs_open hs_dense
      have hmain : Dense (f a ∩ ⋂ i ∈ s, f i) :=
        (hd a (Finset.mem_insert_self a s)).inter_of_isOpen_left htail
          (ho a (Finset.mem_insert_self a s))
      have hset :
          (⋂ i ∈ insert a s, f i) = f a ∩ ⋂ i ∈ s, f i := by
        ext x
        constructor
        · intro hx
          refine ⟨Set.mem_iInter.mp (Set.mem_iInter.mp hx a)
              (Finset.mem_insert_self a s), ?_⟩
          simp only [Set.mem_iInter]
          intro i hi
          exact Set.mem_iInter.mp (Set.mem_iInter.mp hx i)
            (Finset.mem_insert_of_mem hi)
        · rintro ⟨hxa, hxs⟩
          simp only [Set.mem_iInter]
          intro i hi
          rcases Finset.mem_insert.mp hi with rfl | his
          · exact hxa
          · exact Set.mem_iInter.mp (Set.mem_iInter.mp hxs i) his
      simpa [hset] using hmain

/-- Openness of the finite kappa nonvanishing condition from nonzero polynomial witnesses. -/
theorem isOpen_kappa_ne_of_nonzero_probe_polynomials {L d : Nat}
    {θ' : Params L d}
    (hKappa : ∀ j : Nat, 2 ≤ j -> j ≤ L ->
      IsNonzeroProbePolynomial d (fun p : ProbePair d => kappaParam_j θ' j p.1)) :
    IsOpen {p : ProbePair d |
      ∀ j : Nat, 2 ≤ j -> j ≤ L -> kappaParam_j θ' j p.1 ≠ 0} := by
  have hfin : IsOpen (⋂ j ∈ kappaIndexFinset L,
      {p : ProbePair d | kappaParam_j θ' j p.1 ≠ 0}) := by
    refine isOpen_biInter_finset ?_
    intro j hj
    exact (hKappa j (mem_kappaIndexFinset.mp hj).1
      (mem_kappaIndexFinset.mp hj).2).isOpen_ne_zero
  have hset :
      {p : ProbePair d |
        ∀ j : Nat, 2 ≤ j -> j ≤ L -> kappaParam_j θ' j p.1 ≠ 0}
        =
      ⋂ j ∈ kappaIndexFinset L,
        {p : ProbePair d | kappaParam_j θ' j p.1 ≠ 0} := by
    ext p
    constructor
    · intro hp
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      intro j hj
      exact hp j (mem_kappaIndexFinset.mp hj).1 (mem_kappaIndexFinset.mp hj).2
    · intro hp j hj2 hjL
      have hj : j ∈ kappaIndexFinset L := mem_kappaIndexFinset.mpr ⟨hj2, hjL⟩
      exact (Set.mem_iInter.mp (Set.mem_iInter.mp hp j) hj)
  simpa [hset] using hfin

/-- Density of the finite kappa nonvanishing condition from nonzero polynomial witnesses. -/
theorem dense_kappa_ne_of_nonzero_probe_polynomials {L d : Nat}
    {θ' : Params L d}
    (hKappa : ∀ j : Nat, 2 ≤ j -> j ≤ L ->
      IsNonzeroProbePolynomial d (fun p : ProbePair d => kappaParam_j θ' j p.1)) :
    Dense {p : ProbePair d |
      ∀ j : Nat, 2 ≤ j -> j ≤ L -> kappaParam_j θ' j p.1 ≠ 0} := by
  have hfin : Dense (⋂ j ∈ kappaIndexFinset L,
      {p : ProbePair d | kappaParam_j θ' j p.1 ≠ 0}) := by
    refine dense_biInter_finset_of_isOpen (kappaIndexFinset L)
      (fun j => {p : ProbePair d | kappaParam_j θ' j p.1 ≠ 0}) ?_ ?_
    · intro j hj
      exact (hKappa j (mem_kappaIndexFinset.mp hj).1
        (mem_kappaIndexFinset.mp hj).2).isOpen_ne_zero
    · intro j hj
      exact (hKappa j (mem_kappaIndexFinset.mp hj).1
        (mem_kappaIndexFinset.mp hj).2).dense_ne_zero
  have hset :
      {p : ProbePair d |
        ∀ j : Nat, 2 ≤ j -> j ≤ L -> kappaParam_j θ' j p.1 ≠ 0}
        =
      ⋂ j ∈ kappaIndexFinset L,
        {p : ProbePair d | kappaParam_j θ' j p.1 ≠ 0} := by
    ext p
    constructor
    · intro hp
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      intro j hj
      exact hp j (mem_kappaIndexFinset.mp hj).1 (mem_kappaIndexFinset.mp hj).2
    · intro hp j hj2 hjL
      have hj : j ∈ kappaIndexFinset L := mem_kappaIndexFinset.mpr ⟨hj2, hjL⟩
      exact (Set.mem_iInter.mp (Set.mem_iInter.mp hp j) hj)
  simpa [hset] using hfin

/-- Density of the first-slope and finite-kappa nonvanishing intersection. -/
theorem dense_firstSlope_kappa_ne_of_nonzero_probe_polynomials {L d : Nat}
    {θ' : Params L d}
    (hFirst :
      IsNonzeroProbePolynomial d (fun p : ProbePair d => firstSlope θ' p.1 p.2))
    (hKappa : ∀ j : Nat, 2 ≤ j -> j ≤ L ->
      IsNonzeroProbePolynomial d (fun p : ProbePair d => kappaParam_j θ' j p.1)) :
    Dense ({p : ProbePair d | firstSlope θ' p.1 p.2 ≠ 0} ∩
      {p : ProbePair d |
        ∀ j : Nat, 2 ≤ j -> j ≤ L -> kappaParam_j θ' j p.1 ≠ 0}) :=
  hFirst.dense_ne_zero.inter_of_isOpen_right
    (dense_kappa_ne_of_nonzero_probe_polynomials hKappa)
    (isOpen_kappa_ne_of_nonzero_probe_polynomials hKappa)

/-- Assumption package for the Zariski/generic part of Step 0.  The hard facts are kept
as explicit hypotheses here: each defining scalar condition has a nonzero polynomial
witness, visible coordinates have polynomial witnesses with at least one nonzero
coordinate polynomial, and the resulting `O_star` is nonempty. -/
structure OStarGenericAssumptions (L d : Nat) (θ' : Params L d)
    (O : Set (ProbePair d)) : Prop where
  isOpen_O : IsOpen O
  nonempty_O : O.Nonempty
  firstSlope_polynomial :
    IsNonzeroProbePolynomial d (fun p : ProbePair d => firstSlope θ' p.1 p.2)
  kappa_polynomial :
    ∀ j : Nat, 2 ≤ j -> j ≤ L ->
      IsNonzeroProbePolynomial d (fun p : ProbePair d => kappaParam_j θ' j p.1)
  visibleCoord_polynomial :
    ∀ i : Fin d,
      IsProbePolynomial d (fun p : ProbePair d => visibleTailCoord θ' p.1 i)
  visibleCoord_nonzero :
    ∃ i : Fin d,
      IsNonzeroProbePolynomial d (fun p : ProbePair d => visibleTailCoord θ' p.1 i)
  nonempty_O_star : (O_star θ' O).Nonempty

theorem OStarGenericAssumptions.isOpen_firstSlope_ne {L d : Nat}
    {θ' : Params L d} {O : Set (ProbePair d)}
    (h : OStarGenericAssumptions L d θ' O) :
    IsOpen {p : ProbePair d | firstSlope θ' p.1 p.2 ≠ 0} :=
  h.firstSlope_polynomial.isOpen_ne_zero

theorem OStarGenericAssumptions.isOpen_kappa_ne {L d : Nat}
    {θ' : Params L d} {O : Set (ProbePair d)}
    (h : OStarGenericAssumptions L d θ' O) :
    IsOpen {p : ProbePair d |
      ∀ j : Nat, 2 ≤ j -> j ≤ L -> kappaParam_j θ' j p.1 ≠ 0} := by
  have hfin : IsOpen (⋂ j ∈ kappaIndexFinset L,
      {p : ProbePair d | kappaParam_j θ' j p.1 ≠ 0}) := by
    refine isOpen_biInter_finset ?_
    intro j hj
    exact (h.kappa_polynomial j (mem_kappaIndexFinset.mp hj).1
      (mem_kappaIndexFinset.mp hj).2).isOpen_ne_zero
  have hset :
      {p : ProbePair d |
        ∀ j : Nat, 2 ≤ j -> j ≤ L -> kappaParam_j θ' j p.1 ≠ 0}
        =
      ⋂ j ∈ kappaIndexFinset L,
        {p : ProbePair d | kappaParam_j θ' j p.1 ≠ 0} := by
    ext p
    constructor
    · intro hp
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      intro j hj
      exact hp j (mem_kappaIndexFinset.mp hj).1 (mem_kappaIndexFinset.mp hj).2
    · intro hp j hj2 hjL
      have hj : j ∈ kappaIndexFinset L := mem_kappaIndexFinset.mpr ⟨hj2, hjL⟩
      exact (Set.mem_iInter.mp (Set.mem_iInter.mp hp j) hj)
  simpa [hset] using hfin

theorem visibleTailVector_ne_iff_exists_coord_ne {L d : Nat}
    {θ : Params L d} {w : Fin d -> ℝ} :
    visibleTailVector θ w ≠ 0 ↔
      ∃ i : Fin d, visibleTailCoord θ w i ≠ 0 := by
  constructor
  · intro h
    classical
    by_contra hnone
    apply h
    funext i
    by_contra hi
    exact hnone ⟨i, by simpa [visibleTailCoord] using hi⟩
  · rintro ⟨i, hi⟩ hzero
    exact hi (by simp [visibleTailCoord, hzero])

/-- Density of visible-tail nonvanishing from one nonzero visible-coordinate polynomial. -/
theorem dense_visibleTailVector_ne_of_visibleCoord_nonzero {L d : Nat}
    {θ' : Params L d}
    (hVisible : ∃ i : Fin d,
      IsNonzeroProbePolynomial d (fun p : ProbePair d => visibleTailCoord θ' p.1 i)) :
    Dense {p : ProbePair d | visibleTailVector θ' p.1 ≠ 0} := by
  rcases hVisible with ⟨i, hi⟩
  refine Dense.mono ?_ hi.dense_ne_zero
  intro p hp
  exact visibleTailVector_ne_iff_exists_coord_ne.mpr ⟨i, hp⟩

theorem OStarGenericAssumptions.isOpen_visibleTailVector_ne {L d : Nat}
    {θ' : Params L d} {O : Set (ProbePair d)}
    (h : OStarGenericAssumptions L d θ' O) :
    IsOpen {p : ProbePair d | visibleTailVector θ' p.1 ≠ 0} := by
  have hopen : IsOpen (⋃ i : Fin d,
      {p : ProbePair d | visibleTailCoord θ' p.1 i ≠ 0}) :=
    isOpen_iUnion fun i => (h.visibleCoord_polynomial i).isOpen_ne_zero
  have hset :
      {p : ProbePair d | visibleTailVector θ' p.1 ≠ 0}
        =
      ⋃ i : Fin d, {p : ProbePair d | visibleTailCoord θ' p.1 i ≠ 0} := by
    ext p
    simp [visibleTailVector_ne_iff_exists_coord_ne]
  simpa [hset] using hopen

theorem OStarGenericAssumptions.isOpen_O_star {L d : Nat}
    {θ' : Params L d} {O : Set (ProbePair d)}
    (h : OStarGenericAssumptions L d θ' O) :
    IsOpen (O_star θ' O) := by
  have hfirst := h.isOpen_firstSlope_ne
  have hkappa := h.isOpen_kappa_ne
  have hvisible := h.isOpen_visibleTailVector_ne
  have hmain : IsOpen
      (((O ∩ {p : ProbePair d | firstSlope θ' p.1 p.2 ≠ 0})
        ∩ {p : ProbePair d |
          ∀ j : Nat, 2 ≤ j -> j ≤ L -> kappaParam_j θ' j p.1 ≠ 0})
        ∩ {p : ProbePair d | visibleTailVector θ' p.1 ≠ 0}) :=
    ((h.isOpen_O.inter hfirst).inter hkappa).inter hvisible
  have hset :
      O_star θ' O =
        (((O ∩ {p : ProbePair d | firstSlope θ' p.1 p.2 ≠ 0})
          ∩ {p : ProbePair d |
            ∀ j : Nat, 2 ≤ j -> j ≤ L -> kappaParam_j θ' j p.1 ≠ 0})
          ∩ {p : ProbePair d | visibleTailVector θ' p.1 ≠ 0}) := by
    ext p
    constructor
    · intro hp
      exact ⟨⟨⟨hp.1, hp.2.1⟩, hp.2.2.1⟩, hp.2.2.2⟩
    · rintro ⟨⟨⟨hO, hfirst⟩, hkappa⟩, hvisible⟩
      exact ⟨hO, hfirst, hkappa, hvisible⟩
  simpa [hset] using hmain

/-- Relative density of `O_star` in an open base set `O`, using only the finite
nonzero-polynomial witnesses. -/
theorem dense_O_star_in_O_of_open_O {L d : Nat} {θ' : Params L d}
    {O : Set (ProbePair d)} (hOpenO : IsOpen O)
    (hFirst :
      IsNonzeroProbePolynomial d (fun p : ProbePair d => firstSlope θ' p.1 p.2))
    (hKappa : ∀ j : Nat, 2 ≤ j -> j ≤ L ->
      IsNonzeroProbePolynomial d (fun p : ProbePair d => kappaParam_j θ' j p.1))
    (hVisible : ∃ i : Fin d,
      IsNonzeroProbePolynomial d (fun p : ProbePair d => visibleTailCoord θ' p.1 i)) :
    Dense (((↑) : O -> ProbePair d) ⁻¹' O_star θ' O) := by
  have hfk_dense :
      Dense ({p : ProbePair d | firstSlope θ' p.1 p.2 ≠ 0} ∩
        {p : ProbePair d |
          ∀ j : Nat, 2 ≤ j -> j ≤ L -> kappaParam_j θ' j p.1 ≠ 0}) :=
    dense_firstSlope_kappa_ne_of_nonzero_probe_polynomials hFirst hKappa
  have hfk_open :
      IsOpen ({p : ProbePair d | firstSlope θ' p.1 p.2 ≠ 0} ∩
        {p : ProbePair d |
          ∀ j : Nat, 2 ≤ j -> j ≤ L -> kappaParam_j θ' j p.1 ≠ 0}) :=
    hFirst.isOpen_ne_zero.inter (isOpen_kappa_ne_of_nonzero_probe_polynomials hKappa)
  have hvisible_dense :
      Dense {p : ProbePair d | visibleTailVector θ' p.1 ≠ 0} :=
    dense_visibleTailVector_ne_of_visibleCoord_nonzero hVisible
  have hcondition_dense :
      Dense (({p : ProbePair d | firstSlope θ' p.1 p.2 ≠ 0} ∩
        {p : ProbePair d |
          ∀ j : Nat, 2 ≤ j -> j ≤ L -> kappaParam_j θ' j p.1 ≠ 0}) ∩
        {p : ProbePair d | visibleTailVector θ' p.1 ≠ 0}) :=
    hfk_dense.inter_of_isOpen_left hvisible_dense hfk_open
  have hpre : Dense (((↑) : O -> ProbePair d) ⁻¹'
      (({p : ProbePair d | firstSlope θ' p.1 p.2 ≠ 0} ∩
        {p : ProbePair d |
          ∀ j : Nat, 2 ≤ j -> j ≤ L -> kappaParam_j θ' j p.1 ≠ 0}) ∩
        {p : ProbePair d | visibleTailVector θ' p.1 ≠ 0})) :=
    hcondition_dense.preimage hOpenO.isOpenMap_subtype_val
  have hset :
      (((↑) : O -> ProbePair d) ⁻¹'
        (({p : ProbePair d | firstSlope θ' p.1 p.2 ≠ 0} ∩
          {p : ProbePair d |
            ∀ j : Nat, 2 ≤ j -> j ≤ L -> kappaParam_j θ' j p.1 ≠ 0}) ∩
          {p : ProbePair d | visibleTailVector θ' p.1 ≠ 0}))
        =
      (((↑) : O -> ProbePair d) ⁻¹' O_star θ' O) := by
    ext p
    constructor
    · rintro ⟨⟨hfirst, hkappa⟩, hvisible⟩
      exact ⟨p.2, hfirst, hkappa, hvisible⟩
    · intro hp
      exact ⟨⟨hp.2.1, hp.2.2.1⟩, hp.2.2.2⟩
  simpa [hset] using hpre

/-- Nonemptiness of `O_star` from an open nonempty base set and the concrete nonzero
polynomial witnesses for the first-slope, kappa, and visible-tail conditions. -/
theorem O_star_nonempty_of_open_nonempty_nonzero_probe_polynomials {L d : Nat}
    {θ' : Params L d} {O : Set (ProbePair d)}
    (hOpenO : IsOpen O) (hNonemptyO : O.Nonempty)
    (hFirst :
      IsNonzeroProbePolynomial d (fun p : ProbePair d => firstSlope θ' p.1 p.2))
    (hKappa : ∀ j : Nat, 2 ≤ j -> j ≤ L ->
      IsNonzeroProbePolynomial d (fun p : ProbePair d => kappaParam_j θ' j p.1))
    (hVisible : ∃ i : Fin d,
      IsNonzeroProbePolynomial d (fun p : ProbePair d => visibleTailCoord θ' p.1 i)) :
    (O_star θ' O).Nonempty := by
  have hdense : Dense (((↑) : O -> ProbePair d) ⁻¹' O_star θ' O) :=
    dense_O_star_in_O_of_open_O hOpenO hFirst hKappa hVisible
  haveI : Nonempty O := Set.Nonempty.to_subtype hNonemptyO
  rcases hdense.nonempty with ⟨p, hp⟩
  exact ⟨p.1, hp⟩

/-- Concrete polynomial-genericity data sufficient to build `OStarGenericAssumptions`.

This removes the redundant `nonempty_O_star` field from constructor users: it is derived
from relative density inside the open nonempty base set `O`. -/
structure OStarConcreteGenericData (L d : Nat) (θ' : Params L d)
    (O : Set (ProbePair d)) : Prop where
  isOpen_O : IsOpen O
  nonempty_O : O.Nonempty
  firstSlope_nonzero :
    IsNonzeroProbePolynomial d (fun p : ProbePair d => firstSlope θ' p.1 p.2)
  kappa_nonzero :
    ∀ j : Nat, 2 ≤ j -> j ≤ L ->
      IsNonzeroProbePolynomial d (fun p : ProbePair d => kappaParam_j θ' j p.1)
  visibleCoord_polynomial :
    ∀ i : Fin d,
      IsProbePolynomial d (fun p : ProbePair d => visibleTailCoord θ' p.1 i)
  visibleCoord_nonzero :
    ∃ i : Fin d,
      IsNonzeroProbePolynomial d (fun p : ProbePair d => visibleTailCoord θ' p.1 i)

namespace OStarConcreteGenericData

variable {L d : Nat} {θ' : Params L d} {O : Set (ProbePair d)}

theorem nonempty_O_star (D : OStarConcreteGenericData L d θ' O) :
    (O_star θ' O).Nonempty :=
  O_star_nonempty_of_open_nonempty_nonzero_probe_polynomials
    (OStarConcreteGenericData.isOpen_O D) (OStarConcreteGenericData.nonempty_O D)
    (OStarConcreteGenericData.firstSlope_nonzero D)
    (OStarConcreteGenericData.kappa_nonzero D)
    (OStarConcreteGenericData.visibleCoord_nonzero D)

/-- Compile concrete polynomial-genericity data to the downstream generic package. -/
def toOStarGenericAssumptions (D : OStarConcreteGenericData L d θ' O) :
    OStarGenericAssumptions L d θ' O where
  isOpen_O := OStarConcreteGenericData.isOpen_O D
  nonempty_O := OStarConcreteGenericData.nonempty_O D
  firstSlope_polynomial := OStarConcreteGenericData.firstSlope_nonzero D
  kappa_polynomial := OStarConcreteGenericData.kappa_nonzero D
  visibleCoord_polynomial := OStarConcreteGenericData.visibleCoord_polynomial D
  visibleCoord_nonzero := OStarConcreteGenericData.visibleCoord_nonzero D
  nonempty_O_star := OStarConcreteGenericData.nonempty_O_star D

/-- Build concrete probe-genericity data from matrix-level nonzero facts.

The first field says the primed first attention matrix is nonzero.  The kappa field says
each displayed symmetric quadratic matrix defining `κ_j` is nonzero.  The visible field
says the real visible tail matrix `V'_{L:1}` is nonzero, so at least one visible
coordinate polynomial is nonzero. -/
def ofMatrixNonzero
    (hOpenO : IsOpen O) (hNonemptyO : O.Nonempty)
    (hFirst : firstAttention θ' ≠ 0)
    (hKappa : ∀ j : Nat, 2 ≤ j -> j ≤ L ->
      kappaMatrix (paramStream θ') (j - 2) ≠ 0)
    (hVisible : realVprod (paramStream θ') L ≠ 0) :
    OStarConcreteGenericData L d θ' O where
  isOpen_O := hOpenO
  nonempty_O := hNonemptyO
  firstSlope_nonzero :=
    firstSlope_isNonzeroProbePolynomial_of_firstAttention_ne_zero hFirst
  kappa_nonzero := fun j hj2 hjL =>
    kappaParam_isNonzeroProbePolynomial_of_kappaMatrix_ne_zero
      (hKappa j hj2 hjL)
  visibleCoord_polynomial := visibleTailCoord_isProbePolynomial θ'
  visibleCoord_nonzero := visibleCoord_nonzero_of_visibleTailMatrix_ne_zero hVisible

end OStarConcreteGenericData

/-- Direct constructor for `OStarGenericAssumptions` from matrix-level nonzero facts. -/
def OStarGenericAssumptions.ofMatrixNonzero {L d : Nat}
    {θ' : Params L d} {O : Set (ProbePair d)}
    (hOpenO : IsOpen O) (hNonemptyO : O.Nonempty)
    (hFirst : firstAttention θ' ≠ 0)
    (hKappa : ∀ j : Nat, 2 ≤ j -> j ≤ L ->
      kappaMatrix (paramStream θ') (j - 2) ≠ 0)
    (hVisible : realVprod (paramStream θ') L ≠ 0) :
    OStarGenericAssumptions L d θ' O :=
  (OStarConcreteGenericData.ofMatrixNonzero (L := L) (d := d) (θ' := θ') (O := O)
    hOpenO hNonemptyO hFirst hKappa hVisible).toOStarGenericAssumptions

theorem O_star_nonempty_of_generic {L d : Nat} {θ' : Params L d}
    {O : Set (ProbePair d)} (h : OStarGenericAssumptions L d θ' O) :
    (O_star θ' O).Nonempty :=
  h.nonempty_O_star

theorem exists_visibleTailCoord_ne_zero_of_visibleTailVector_ne_zero {L d : Nat}
    {θ : Params L d} {w : Fin d -> ℝ}
    (h : visibleTailVector θ w ≠ 0) :
    ∃ i : Fin d, visibleTailCoord θ w i ≠ 0 := by
  classical
  by_contra hnone
  apply h
  funext i
  by_contra hi
  exact hnone ⟨i, by simpa [visibleTailCoord] using hi⟩

theorem exists_visibleTailCoord_ne_zero_of_mem_O_star {L d : Nat}
    {θ' : Params L d} {O : Set (ProbePair d)} {p : ProbePair d}
    (hp : p ∈ O_star θ' O) :
    ∃ i : Fin d, visibleTailCoord θ' p.1 i ≠ 0 :=
  exists_visibleTailCoord_ne_zero_of_visibleTailVector_ne_zero
    (O_star_visibleTailVector_ne hp)

/-- A chosen visible coordinate for a fixed generic probe. -/
structure VisibleCoordinateChoice {L d : Nat} (θ : Params L d) (p : ProbePair d) where
  iota : Fin d
  nonzero : visibleTailCoord θ p.1 iota ≠ 0

/-- Choose `iota` with `e_iota^T V'_{L:1} w != 0` from membership in `O_star`. -/
noncomputable def visibleCoordinateChoiceOfOStar {L d : Nat}
    {θ' : Params L d} {O : Set (ProbePair d)} {p : ProbePair d}
    (hp : p ∈ O_star θ' O) :
    VisibleCoordinateChoice θ' p := by
  classical
  let hcoord := exists_visibleTailCoord_ne_zero_of_mem_O_star hp
  exact ⟨Classical.choose hcoord, Classical.choose_spec hcoord⟩

/-- Fixed-probe real-tail agreement interval. -/
def RealTailObservableAgreementAt {L d : Nat} (r : Nat)
    (θ θ' : Params L d) (p : ProbePair d) (T0 : ℝ) : Prop :=
  ∀ tau : ℝ, T0 < tau -> Fobs r θ p.1 p.2 tau = Fobs r θ' p.1 p.2 tau

/-- Global constant-probe tail agreement hypothesis `(H)`. -/
structure ConstantProbeTailAgreement (r L d : Nat)
    (θ θ' : Params L d) where
  T0 : ℝ
  eqOnTail : ∀ p : ProbePair d, RealTailObservableAgreementAt r θ θ' p T0

theorem ConstantProbeTailAgreement.at {r L d : Nat} {θ θ' : Params L d}
    (h : ConstantProbeTailAgreement r L d θ θ') (p : ProbePair d) :
    RealTailObservableAgreementAt r θ θ' p h.T0 :=
  h.eqOnTail p

/-- Local constant-probe tail agreement on a base probe region `O`.

This is the Step 1 invariant needed by the path/open-set IDL proof: after recursion,
agreement is only known for constant paths whose probes lie in the current open region. -/
structure LocalProbeTailAgreement (r L d : Nat) (O : Set (ProbePair d))
    (θ θ' : Params L d) where
  T0 : ProbePair d -> ℝ
  eqOnTail :
    ∀ p : ProbePair d, p ∈ O -> RealTailObservableAgreementAt r θ θ' p (T0 p)

theorem LocalProbeTailAgreement.at {r L d : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (h : LocalProbeTailAgreement r L d O θ θ') {p : ProbePair d} (hp : p ∈ O) :
    RealTailObservableAgreementAt r θ θ' p (h.T0 p) :=
  h.eqOnTail p hp

/-- Step 0 data after fixing one probe in `O_star`: the probe, visible coordinate, and
the real tail interval on which the two observables agree. -/
structure FixedOStarProbe (r L d : Nat) (O : Set (ProbePair d))
    (θ θ' : Params L d) where
  probe : ProbePair d
  mem_O_star : probe ∈ O_star θ' O
  iota : Fin d
  visible_iota_ne : visibleTailCoord θ' probe.1 iota ≠ 0
  T0 : ℝ
  tail_agreement : RealTailObservableAgreementAt r θ θ' probe T0

noncomputable def FixedOStarProbe.ofLocalAgreement {r L d : Nat}
    {O : Set (ProbePair d)} {θ θ' : Params L d}
    (hAgree : LocalProbeTailAgreement r L d O θ θ') {p : ProbePair d}
    (hp : p ∈ O_star θ' O) :
    FixedOStarProbe r L d O θ θ' := by
  classical
  let c := visibleCoordinateChoiceOfOStar hp
  exact
    { probe := p
      mem_O_star := hp
      iota := c.iota
      visible_iota_ne := c.nonzero
      T0 := hAgree.T0 p
      tail_agreement := hAgree.at hp.1 }

/-- Standing assumptions for the concrete Step 1 theorem interface. -/
structure Step1StandingAssumptions (r L d : Nat) (O : Set (ProbePair d))
    (θ θ' : Params L d) where
  depth_pos : 0 < L
  generic : OStarGenericAssumptions L d θ' O
  agreement : LocalProbeTailAgreement r L d O θ θ'

/-- Concrete Step 1 conclusion: identify the first attention matrix. -/
def Step1Conclusion {L d : Nat} (θ θ' : Params L d) : Prop :=
  firstAttention θ = firstAttention θ'

/-- Concrete theorem statement for Step 1, Section 5, Proposition `A1`.  Later shards
provide the proof from the packaged genericity and tail-agreement assumptions. -/
def ConcreteStep1TheoremStatement (r L d : Nat) (O : Set (ProbePair d))
    (θ θ' : Params L d) : Prop :=
  Step1StandingAssumptions r L d O θ θ' -> Step1Conclusion θ θ'

end TransformerIdentifiability.NLayer
