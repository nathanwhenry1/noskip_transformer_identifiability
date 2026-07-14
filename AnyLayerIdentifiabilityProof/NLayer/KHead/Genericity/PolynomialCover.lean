import AnyLayerIdentifiabilityProof.NLayer.KHead.Genericity.AnchorCertificate
import AnyLayerIdentifiabilityProof.NLayer.Foundations.ParamPolynomialGenericity

set_option autoImplicit false

open Matrix MvPolynomial
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.KHead

/-!
# K-head parameter polynomial covers

This shard starts the algebraic-properness bridge for the k-head genericity
predicates.  It provides a coordinate polynomial ring for `Params L k d`,
generic value/attention matrices, a reusable finite polynomial predicate-cover
type, and concrete nonzero witness polynomials for the elementary matrix
clauses of regularity.
-/

/-- One k-head parameter coordinate: layer, head, then value/attention entry. -/
abbrev KHeadParamCoord (L k d : Nat) : Type :=
  Fin L × (Fin k × TransformerIdentifiability.NLayer.LayerCoord d)

/-- Coordinate ring of the flattened k-head parameter space. -/
abbrev KHeadParamRing (L k d : Nat) : Type :=
  MvPolynomial (KHeadParamCoord L k d) ℝ

/-- Flatten all k-head parameters, keeping layer/head coordinates explicit. -/
def kHeadParamFlat {L k d : Nat} (θ : Params L k d) :
    KHeadParamCoord L k d → ℝ :=
  fun c => TransformerIdentifiability.NLayer.layerFlat (θ c.1 c.2.1) c.2.2

@[simp]
theorem kHeadParamFlat_value {L k d : Nat} (θ : Params L k d)
    (l : Fin L) (a : Fin k) (i j : Fin d) :
    kHeadParamFlat θ (l, (a, Sum.inl (i, j))) = valueMatrix θ l a i j :=
  rfl

@[simp]
theorem kHeadParamFlat_attention {L k d : Nat} (θ : Params L k d)
    (l : Fin L) (a : Fin k) (i j : Fin d) :
    kHeadParamFlat θ (l, (a, Sum.inr (i, j))) = attentionMatrix θ l a i j :=
  rfl

/-! ## Generic coordinate matrices -/

/-- The generic k-head value matrix at layer `l`, head `a`. -/
noncomputable def kHeadGenValue (L k d : Nat) (l : Fin L) (a : Fin k) :
    Matrix (Fin d) (Fin d) (KHeadParamRing L k d) :=
  Matrix.of fun i j => MvPolynomial.X (l, (a, Sum.inl (i, j)))

/-- The generic k-head attention matrix at layer `l`, head `a`. -/
noncomputable def kHeadGenAttention (L k d : Nat) (l : Fin L) (a : Fin k) :
    Matrix (Fin d) (Fin d) (KHeadParamRing L k d) :=
  Matrix.of fun i j => MvPolynomial.X (l, (a, Sum.inr (i, j)))

@[simp]
theorem map_kHeadGenValue {L k d : Nat} (θ : Params L k d)
    (l : Fin L) (a : Fin k) :
    (kHeadGenValue L k d l a).map (MvPolynomial.eval (kHeadParamFlat θ)) =
      valueMatrix θ l a := by
  ext i j
  simp [kHeadGenValue, Matrix.map_apply]

@[simp]
theorem map_kHeadGenAttention {L k d : Nat} (θ : Params L k d)
    (l : Fin L) (a : Fin k) :
    (kHeadGenAttention L k d l a).map (MvPolynomial.eval (kHeadParamFlat θ)) =
      attentionMatrix θ l a := by
  ext i j
  simp [kHeadGenAttention, Matrix.map_apply]

/-- Evaluation of the determinant of a generic value matrix. -/
theorem eval_det_kHeadGenValue {L k d : Nat} (θ : Params L k d)
    (l : Fin L) (a : Fin k) :
    (MvPolynomial.eval (kHeadParamFlat θ)) (kHeadGenValue L k d l a).det =
      (valueMatrix θ l a).det := by
  rw [← map_kHeadGenValue θ l a]
  simpa [RingHom.mapMatrix_apply] using
    (RingHom.map_det (MvPolynomial.eval (kHeadParamFlat θ))
      (kHeadGenValue L k d l a))

/-- Evaluation of the determinant of a generic attention matrix. -/
theorem eval_det_kHeadGenAttention {L k d : Nat} (θ : Params L k d)
    (l : Fin L) (a : Fin k) :
    (MvPolynomial.eval (kHeadParamFlat θ)) (kHeadGenAttention L k d l a).det =
      (attentionMatrix θ l a).det := by
  rw [← map_kHeadGenAttention θ l a]
  simpa [RingHom.mapMatrix_apply] using
    (RingHom.map_det (MvPolynomial.eval (kHeadParamFlat θ))
      (kHeadGenAttention L k d l a))

/-! ## Polynomial versions of the regularity matrix expressions -/

/-- Squared Frobenius norm as a polynomial expression. -/
noncomputable def matrixFrobSqPoly {ι : Type*} {m n : Nat}
    (M : Matrix (Fin m) (Fin n) (MvPolynomial ι ℝ)) : MvPolynomial ι ℝ :=
  ∑ i : Fin m, ∑ j : Fin n, M i j * M i j

@[simp]
theorem eval_matrixFrobSqPoly {ι : Type*} {m n : Nat}
    (ρ : ι → ℝ) (M : Matrix (Fin m) (Fin n) (MvPolynomial ι ℝ)) :
    MvPolynomial.eval ρ (matrixFrobSqPoly M) =
      matrixFrobSq (M.map (MvPolynomial.eval ρ)) := by
  simp [matrixFrobSqPoly, matrixFrobSq, Matrix.map_apply]

/-- Matrix symmetrization over a parameter-polynomial ring. -/
noncomputable def genSym {ι : Type*} {d : Nat}
    (M : Matrix (Fin d) (Fin d) (MvPolynomial ι ℝ)) :
    Matrix (Fin d) (Fin d) (MvPolynomial ι ℝ) :=
  (MvPolynomial.C ((2 : ℝ)⁻¹) : MvPolynomial ι ℝ) • (M + Mᵀ)

@[simp]
theorem map_genSym {ι : Type*} {d : Nat} (ρ : ι → ℝ)
    (M : Matrix (Fin d) (Fin d) (MvPolynomial ι ℝ)) :
    (genSym M).map (MvPolynomial.eval ρ) =
      sym (M.map (MvPolynomial.eval ρ)) := by
  ext i j
  simp [genSym, sym, Matrix.map_apply, Matrix.smul_apply, Matrix.add_apply,
    Matrix.transpose_apply]
  ring

/-- Distinct ordered head pairs. -/
abbrev DistinctHeadPair (k : Nat) : Type :=
  {ac : Fin k × Fin k // ac.1 ≠ ac.2}

/-- The elementary matrix-polynomial clauses from regularity `(R1)` and `(R2)`. -/
inductive KHeadBasicMatrixIndex (L k : Nat) : Type
  | detAttention (l : Fin L) (a : Fin k)
  | symAttention (l : Fin L) (a : Fin k)
  | value (l : Fin L) (a : Fin k)
  | headSeparation (l : Fin L) (ac : DistinctHeadPair k)
  deriving DecidableEq, Fintype

/-- The predicate cut out by the elementary matrix-polynomial clauses. -/
def KHeadBasicMatrixClauses {L k d : Nat} (θ : Params L k d) : Prop :=
  (∀ l : Fin L, ∀ a : Fin k, (attentionMatrix θ l a).det ≠ 0) ∧
    (∀ l : Fin L, ∀ a : Fin k, matrixFrobSq (sym (attentionMatrix θ l a)) ≠ 0) ∧
      (∀ l : Fin L, ∀ a : Fin k, matrixFrobSq (valueMatrix θ l a) ≠ 0) ∧
        (∀ l : Fin L, ∀ ac : DistinctHeadPair k,
          matrixFrobSq
            (attentionMatrix θ l ac.1.1 - attentionMatrix θ l ac.1.2) ≠ 0)

/-- Polynomial attached to one elementary matrix clause. -/
noncomputable def kHeadBasicMatrixPoly {L k d : Nat} :
    KHeadBasicMatrixIndex L k → KHeadParamRing L k d
  | KHeadBasicMatrixIndex.detAttention l a =>
      (kHeadGenAttention L k d l a).det
  | KHeadBasicMatrixIndex.symAttention l a =>
      matrixFrobSqPoly (genSym (kHeadGenAttention L k d l a))
  | KHeadBasicMatrixIndex.value l a =>
      matrixFrobSqPoly (kHeadGenValue L k d l a)
  | KHeadBasicMatrixIndex.headSeparation l ac =>
      matrixFrobSqPoly
        (kHeadGenAttention L k d l ac.1.1 - kHeadGenAttention L k d l ac.1.2)

/-- A nonzero evaluation proves that a real multivariate polynomial is nonzero. -/
theorem mvPolynomial_ne_zero_of_eval_ne_zero {ι : Type*} (x : ι → ℝ)
    {p : MvPolynomial ι ℝ} (hp : MvPolynomial.eval x p ≠ 0) : p ≠ 0 := by
  intro hzero
  exact hp (by simp [hzero])

private theorem matrixBasis_ne_zero {d : Nat} (i0 : Fin d) :
    matrixBasis (i0, i0) ≠ (0 : Matrix (Fin d) (Fin d) ℝ) := by
  intro hzero
  have hentry := congr_fun (congr_fun hzero i0) i0
  simp [matrixBasis] at hentry

private theorem sym_matrixBasis_ne_zero {d : Nat} (i0 : Fin d) :
    sym (matrixBasis (i0, i0)) ≠ (0 : Matrix (Fin d) (Fin d) ℝ) := by
  intro hzero
  have hentry := congr_fun (congr_fun hzero i0) i0
  simp [matrixBasis, sym] at hentry

private theorem sym_one_matrix {d : Nat} :
    sym (1 : Matrix (Fin d) (Fin d) ℝ) = 1 := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [sym]
    ring
  · simp [sym, h]

private theorem matrixOne_ne_zero {d : Nat} (hd : 0 < d) :
    (1 : Matrix (Fin d) (Fin d) ℝ) ≠ 0 := by
  let i0 : Fin d := ⟨0, hd⟩
  intro hzero
  have hentry := congr_fun (congr_fun hzero i0) i0
  simp at hentry

private theorem matrixFrobSq_one_pos {d : Nat} (hd : 0 < d) :
    0 < matrixFrobSq (1 : Matrix (Fin d) (Fin d) ℝ) := by
  exact lt_of_le_of_ne' (matrixFrobSq_nonneg _)
    ((matrixFrobSq_ne_zero_iff _).mpr (matrixOne_ne_zero hd))

/-- `K03D.E.prop-genericity-witnesses.P`, elementary matrix-clause part:
the explicit determinant/Frobenius/separation polynomials from `(R1)` and
`(R2)` are nonzero when `d > 0`. -/
theorem kHeadBasicMatrixPoly_ne_zero {L k d : Nat} (hd : 0 < d) :
    ∀ idx : KHeadBasicMatrixIndex L k, kHeadBasicMatrixPoly (d := d) idx ≠ 0 := by
  classical
  intro idx
  let i0 : Fin d := ⟨0, hd⟩
  let E : Matrix (Fin d) (Fin d) ℝ := matrixBasis (i0, i0)
  cases idx with
  | detAttention l a =>
      let θ : Params L k d := fun l' a' =>
        ((0 : Matrix (Fin d) (Fin d) ℝ),
          if l' = l ∧ a' = a then (1 : Matrix (Fin d) (Fin d) ℝ) else 0)
      refine mvPolynomial_ne_zero_of_eval_ne_zero (kHeadParamFlat θ) ?_
      rw [kHeadBasicMatrixPoly, eval_det_kHeadGenAttention θ l a]
      have hA : attentionMatrix θ l a = (1 : Matrix (Fin d) (Fin d) ℝ) := by
        simp [θ]
      simp [hA]
  | symAttention l a =>
      let θ : Params L k d := fun l' a' =>
        ((0 : Matrix (Fin d) (Fin d) ℝ), if l' = l ∧ a' = a then E else 0)
      refine mvPolynomial_ne_zero_of_eval_ne_zero (kHeadParamFlat θ) ?_
      rw [kHeadBasicMatrixPoly, eval_matrixFrobSqPoly, map_genSym, map_kHeadGenAttention]
      have hA : attentionMatrix θ l a = E := by
        simp [θ, E]
      rw [hA]
      exact (matrixFrobSq_ne_zero_iff _).mpr (sym_matrixBasis_ne_zero i0)
  | value l a =>
      let θ : Params L k d := fun l' a' =>
        (if l' = l ∧ a' = a then E else 0,
          (0 : Matrix (Fin d) (Fin d) ℝ))
      refine mvPolynomial_ne_zero_of_eval_ne_zero (kHeadParamFlat θ) ?_
      rw [kHeadBasicMatrixPoly, eval_matrixFrobSqPoly, map_kHeadGenValue]
      have hV : valueMatrix θ l a = E := by
        simp [θ, E]
      rw [hV]
      exact (matrixFrobSq_ne_zero_iff _).mpr (matrixBasis_ne_zero i0)
  | headSeparation l ac =>
      let θ : Params L k d := fun l' a' =>
        ((0 : Matrix (Fin d) (Fin d) ℝ),
          if l' = l ∧ a' = ac.1.1 then E else 0)
      refine mvPolynomial_ne_zero_of_eval_ne_zero (kHeadParamFlat θ) ?_
      rw [kHeadBasicMatrixPoly, eval_matrixFrobSqPoly]
      have hmap :
          (kHeadGenAttention L k d l ac.1.1 - kHeadGenAttention L k d l ac.1.2).map
              (MvPolynomial.eval (kHeadParamFlat θ)) =
            E := by
        ext i j
        have hne : ac.1.2 ≠ ac.1.1 := Ne.symm ac.2
        simp [Matrix.map_apply, kHeadGenAttention, θ, E, hne]
      rw [hmap]
      exact (matrixFrobSq_ne_zero_iff _).mpr (matrixBasis_ne_zero i0)

/-! ## Corner-slope parameter polynomials -/

/-- Generic sum of the value matrices in one layer. -/
noncomputable def genValueSum (L k d : Nat) (l : Fin L) :
    Matrix (Fin d) (Fin d) (KHeadParamRing L k d) :=
  ∑ a : Fin k, kHeadGenValue L k d l a

/-- Generic collapsed matrix `I + sum_a V_la`. -/
noncomputable def genCollapseMatrix (L k d : Nat) (l : Fin L) :
    Matrix (Fin d) (Fin d) (KHeadParamRing L k d) :=
  1 + genValueSum L k d l

@[simp]
theorem map_genValueSum {L k d : Nat} (θ : Params L k d) (l : Fin L) :
    (genValueSum L k d l).map (MvPolynomial.eval (kHeadParamFlat θ)) =
      valueSum θ l := by
  ext i j
  simp [genValueSum, valueSum, Matrix.map_apply, Matrix.sum_apply, kHeadGenValue]

@[simp]
theorem map_genCollapseMatrix {L k d : Nat} (θ : Params L k d) (l : Fin L) :
    (genCollapseMatrix L k d l).map (MvPolynomial.eval (kHeadParamFlat θ)) =
      collapseMatrix θ l := by
  ext i j
  have hV :
      MvPolynomial.eval (kHeadParamFlat θ) (genValueSum L k d l i j) =
        valueSum θ l i j := by
    simpa [Matrix.map_apply] using congr_fun (congr_fun (map_genValueSum θ l) i) j
  have hOne :
      MvPolynomial.eval (kHeadParamFlat θ)
          ((1 : Matrix (Fin d) (Fin d) (KHeadParamRing L k d)) i j) =
        (1 : Matrix (Fin d) (Fin d) ℝ) i j := by
    have hOneMatrix :
        ((1 : Matrix (Fin d) (Fin d) (KHeadParamRing L k d)).map
            (MvPolynomial.eval (kHeadParamFlat θ))) =
          (1 : Matrix (Fin d) (Fin d) ℝ) :=
      Matrix.map_one (MvPolynomial.eval (kHeadParamFlat θ)) (by simp) (by simp)
    simpa [Matrix.map_apply] using congr_fun (congr_fun hOneMatrix i) j
  simp [genCollapseMatrix, collapseMatrix, Matrix.map_apply, Matrix.add_apply, hV, hOne]

/-- Generic collapsed-matrix stream, extended by identity outside the finite depth. -/
noncomputable def genCollapseMatrixStream (L k d : Nat) (n : Nat) :
    Matrix (Fin d) (Fin d) (KHeadParamRing L k d) :=
  if h : n < L then genCollapseMatrix L k d ⟨n, h⟩ else 1

/-- Generic value-sum stream, extended by zero outside the finite depth. -/
noncomputable def genValueSumStream (L k d : Nat) (n : Nat) :
    Matrix (Fin d) (Fin d) (KHeadParamRing L k d) :=
  if h : n < L then genValueSum L k d ⟨n, h⟩ else 0

@[simp]
theorem map_genCollapseMatrixStream {L k d : Nat} (θ : Params L k d) (n : Nat) :
    (genCollapseMatrixStream L k d n).map (MvPolynomial.eval (kHeadParamFlat θ)) =
      collapseMatrixStream θ n := by
  by_cases hn : n < L
  · simp [genCollapseMatrixStream, collapseMatrixStream, hn]
  · simp [genCollapseMatrixStream, collapseMatrixStream, hn]

@[simp]
theorem map_genValueSumStream {L k d : Nat} (θ : Params L k d) (n : Nat) :
    (genValueSumStream L k d n).map (MvPolynomial.eval (kHeadParamFlat θ)) =
      valueSumStream θ n := by
  by_cases hn : n < L
  · simp [genValueSumStream, valueSumStream, hn]
  · simp [genValueSumStream, valueSumStream, hn]

/-- Generic all-`alpha` corner `K` stream. -/
noncomputable def genCornerKStream (r L k d : Nat) (n : Nat) :
    Matrix (Fin d) (Fin d) (KHeadParamRing L k d) :=
  genCollapseMatrixStream L k d n -
    (MvPolynomial.C (alpha r) : KHeadParamRing L k d) • genValueSumStream L k d n

@[simp]
theorem map_genCornerKStream {L k d : Nat} (r : Nat)
    (θ : Params L k d) (n : Nat) :
    (genCornerKStream r L k d n).map (MvPolynomial.eval (kHeadParamFlat θ)) =
      cornerKStream r θ n := by
  ext i j
  have hC :
      MvPolynomial.eval (kHeadParamFlat θ) (genCollapseMatrixStream L k d n i j) =
        collapseMatrixStream θ n i j := by
    simpa [Matrix.map_apply] using
      congr_fun (congr_fun (map_genCollapseMatrixStream θ n) i) j
  have hV :
      MvPolynomial.eval (kHeadParamFlat θ) (genValueSumStream L k d n i j) =
        valueSumStream θ n i j := by
    simpa [Matrix.map_apply] using
      congr_fun (congr_fun (map_genValueSumStream θ n) i) j
  simp [genCornerKStream, cornerKStream, Matrix.map_apply, Matrix.sub_apply,
    Matrix.smul_apply, hC, hV]

/-- Prefix product for polynomial-valued matrix streams. -/
def genMatrixPrefixProduct {d : Nat} {R : Type*} [Semiring R]
    (M : Nat → Matrix (Fin d) (Fin d) R) :
    Nat → Matrix (Fin d) (Fin d) R
  | 0 => 1
  | n + 1 => M n * genMatrixPrefixProduct M n

@[simp]
theorem genMatrixPrefixProduct_zero {d : Nat} {R : Type*} [Semiring R]
    (M : Nat → Matrix (Fin d) (Fin d) R) :
    genMatrixPrefixProduct M 0 = 1 :=
  rfl

@[simp]
theorem genMatrixPrefixProduct_succ {d : Nat} {R : Type*} [Semiring R]
    (M : Nat → Matrix (Fin d) (Fin d) R) (n : Nat) :
    genMatrixPrefixProduct M (n + 1) = M n * genMatrixPrefixProduct M n :=
  rfl

private theorem map_genMatrixPrefixProduct_eval {L k d : Nat}
    (θ : Params L k d)
    (M : Nat → Matrix (Fin d) (Fin d) (KHeadParamRing L k d))
    (N : Nat → Matrix (Fin d) (Fin d) ℝ)
    (hM : ∀ n, (M n).map (MvPolynomial.eval (kHeadParamFlat θ)) = N n) :
    ∀ n,
      (genMatrixPrefixProduct M n).map (MvPolynomial.eval (kHeadParamFlat θ)) =
        matrixPrefixProduct N n := by
  intro n
  induction n with
  | zero =>
      simp [genMatrixPrefixProduct, matrixPrefixProduct]
  | succ n ih =>
      simp [genMatrixPrefixProduct, matrixPrefixProduct, Matrix.map_mul, hM n, ih]

/-- Generic product of all-`alpha` corner `K` matrices. -/
noncomputable def genCornerKPrefix (r L k d : Nat) (n : Nat) :
    Matrix (Fin d) (Fin d) (KHeadParamRing L k d) :=
  genMatrixPrefixProduct (genCornerKStream r L k d) n

/-- Generic product of collapsed matrices. -/
noncomputable def genCornerCPrefix (L k d : Nat) (n : Nat) :
    Matrix (Fin d) (Fin d) (KHeadParamRing L k d) :=
  genMatrixPrefixProduct (genCollapseMatrixStream L k d) n

@[simp]
theorem map_genCornerKPrefix {L k d : Nat} (r : Nat)
    (θ : Params L k d) (n : Nat) :
    (genCornerKPrefix r L k d n).map (MvPolynomial.eval (kHeadParamFlat θ)) =
      cornerKPrefix r θ n := by
  simpa [genCornerKPrefix, cornerKPrefix] using
    map_genMatrixPrefixProduct_eval θ (genCornerKStream r L k d)
      (cornerKStream r θ) (fun n => map_genCornerKStream r θ n) n

@[simp]
theorem map_genCornerCPrefix {L k d : Nat}
    (θ : Params L k d) (n : Nat) :
    (genCornerCPrefix L k d n).map (MvPolynomial.eval (kHeadParamFlat θ)) =
      cornerCPrefix θ n := by
  simpa [genCornerCPrefix, cornerCPrefix] using
    map_genMatrixPrefixProduct_eval θ (genCollapseMatrixStream L k d)
      (collapseMatrixStream θ) (fun n => map_genCollapseMatrixStream θ n) n

/-- Generic affine `w`-coefficient in the all-`alpha` corner formula for `v_n`. -/
noncomputable def genCornerDPrefix (r L k d : Nat) :
    Nat → Matrix (Fin d) (Fin d) (KHeadParamRing L k d)
  | 0 => 0
  | n + 1 =>
      genCollapseMatrixStream L k d n * genCornerDPrefix r L k d n +
        ((MvPolynomial.C (alpha r) : KHeadParamRing L k d) •
          genValueSumStream L k d n) *
            genCornerKPrefix r L k d n

@[simp]
theorem genCornerDPrefix_zero {r L k d : Nat} :
    genCornerDPrefix r L k d 0 = 0 :=
  rfl

@[simp]
theorem genCornerDPrefix_succ {r L k d : Nat} (n : Nat) :
    genCornerDPrefix r L k d (n + 1) =
      genCollapseMatrixStream L k d n * genCornerDPrefix r L k d n +
        ((MvPolynomial.C (alpha r) : KHeadParamRing L k d) •
          genValueSumStream L k d n) *
            genCornerKPrefix r L k d n :=
  rfl

@[simp]
theorem map_genCornerDPrefix {L k d : Nat} (r : Nat)
    (θ : Params L k d) :
    ∀ n,
      (genCornerDPrefix r L k d n).map (MvPolynomial.eval (kHeadParamFlat θ)) =
        cornerDPrefix r θ n := by
  intro n
  induction n with
  | zero =>
      simp [genCornerDPrefix, cornerDPrefix]
  | succ n ih =>
      ext i j
      have hC :
          ∀ x : Fin d,
            MvPolynomial.eval (kHeadParamFlat θ)
                (genCollapseMatrixStream L k d n i x) =
              collapseMatrixStream θ n i x := by
        intro x
        simpa [Matrix.map_apply] using
          congr_fun (congr_fun (map_genCollapseMatrixStream θ n) i) x
      have hD :
          ∀ x : Fin d,
            MvPolynomial.eval (kHeadParamFlat θ)
                (genCornerDPrefix r L k d n x j) =
              cornerDPrefix r θ n x j := by
        intro x
        simpa [Matrix.map_apply] using congr_fun (congr_fun ih x) j
      have hV :
          ∀ x : Fin d,
            MvPolynomial.eval (kHeadParamFlat θ)
                (genValueSumStream L k d n i x) =
              valueSumStream θ n i x := by
        intro x
        simpa [Matrix.map_apply] using
          congr_fun (congr_fun (map_genValueSumStream θ n) i) x
      have hK :
          ∀ x : Fin d,
            MvPolynomial.eval (kHeadParamFlat θ)
                (genCornerKPrefix r L k d n x j) =
              cornerKPrefix r θ n x j := by
        intro x
        simpa [Matrix.map_apply] using
          congr_fun (congr_fun (map_genCornerKPrefix r θ n) x) j
      simp [genCornerDPrefix, cornerDPrefix, Matrix.map_apply, Matrix.add_apply,
        Matrix.mul_apply, Matrix.smul_apply, Finset.mul_sum, hC, hD, hV, hK]

/-- Cast a fixed real vector into a parameter-polynomial ring. -/
noncomputable def genConstVec {ι : Type*} {d : Nat} (w : Vec d) :
    Fin d → MvPolynomial ι ℝ :=
  fun i => MvPolynomial.C (w i)

@[simp]
theorem eval_genConstVec {ι : Type*} {d : Nat} (ρ : ι → ℝ) (w : Vec d) :
    (fun i => MvPolynomial.eval ρ (genConstVec w i)) = w := by
  ext i
  simp [genConstVec]

/-- Generic corner `w` stream evaluated at a fixed real probe vector. -/
noncomputable def genCornerWAt (r L k d : Nat) (l : Fin L) (w : Vec d) :
    Fin d → KHeadParamRing L k d :=
  genCornerKPrefix r L k d l.val *ᵥ genConstVec w

/-- Generic corner `v` stream evaluated at fixed real probe vectors. -/
noncomputable def genCornerVAt (r L k d : Nat) (l : Fin L) (w v : Vec d) :
    Fin d → KHeadParamRing L k d :=
  genCornerCPrefix L k d l.val *ᵥ genConstVec v +
    genCornerDPrefix r L k d l.val *ᵥ genConstVec w

@[simp]
theorem eval_genCornerWAt {L k d : Nat} (r : Nat)
    (θ : Params L k d) (l : Fin L) (w : Vec d) :
    (fun i =>
      MvPolynomial.eval (kHeadParamFlat θ) (genCornerWAt r L k d l w i)) =
        cornerKPrefix r θ l.val *ᵥ w := by
  ext i
  have hK :
      ∀ x : Fin d,
        MvPolynomial.eval (kHeadParamFlat θ)
            (genCornerKPrefix r L k d l.val i x) =
          cornerKPrefix r θ l.val i x := by
    intro x
    exact congr_fun (congr_fun (map_genCornerKPrefix r θ l.val) i) x
  simp [genCornerWAt, genConstVec, Matrix.mulVec, dotProduct, hK]

@[simp]
theorem eval_genCornerVAt {L k d : Nat} (r : Nat)
    (θ : Params L k d) (l : Fin L) (w v : Vec d) :
    (fun i =>
      MvPolynomial.eval (kHeadParamFlat θ) (genCornerVAt r L k d l w v i)) =
        cornerCPrefix θ l.val *ᵥ v + cornerDPrefix r θ l.val *ᵥ w := by
  ext i
  have hC :
      ∀ x : Fin d,
        MvPolynomial.eval (kHeadParamFlat θ)
            (genCornerCPrefix L k d l.val i x) =
          cornerCPrefix θ l.val i x := by
    intro x
    exact congr_fun (congr_fun (map_genCornerCPrefix θ l.val) i) x
  have hD :
      ∀ x : Fin d,
        MvPolynomial.eval (kHeadParamFlat θ)
            (genCornerDPrefix r L k d l.val i x) =
          cornerDPrefix r θ l.val i x := by
    intro x
    exact congr_fun (congr_fun (map_genCornerDPrefix r θ l.val) i) x
  simp [genCornerVAt, genConstVec, Matrix.mulVec, dotProduct, hC, hD]

/-- Bilinear form over a parameter-polynomial ring. -/
noncomputable def genParamBilin {ι : Type*} {d : Nat}
    (A : Matrix (Fin d) (Fin d) (MvPolynomial ι ℝ))
    (w v : Fin d → MvPolynomial ι ℝ) : MvPolynomial ι ℝ :=
  w ⬝ᵥ A *ᵥ v

@[simp]
theorem eval_genParamBilin {ι : Type*} {d : Nat} (ρ : ι → ℝ)
    (A : Matrix (Fin d) (Fin d) (MvPolynomial ι ℝ))
    (w v : Fin d → MvPolynomial ι ℝ) :
    MvPolynomial.eval ρ (genParamBilin A w v) =
      matrixBilin (A.map (MvPolynomial.eval ρ))
        (fun i => MvPolynomial.eval ρ (w i))
        (fun i => MvPolynomial.eval ρ (v i)) := by
  simp [genParamBilin, matrixBilin, Matrix.mulVec, dotProduct, Matrix.map_apply]

/-- Parameter polynomial obtained by evaluating the corner slope difference at fixed probes. -/
noncomputable def kHeadCornerSlopeProbeEvalPoly (r L k d : Nat)
    (w v : Vec d) (l : Fin L) (a c : Fin k) : KHeadParamRing L k d :=
  genParamBilin
    (kHeadGenAttention L k d l a - kHeadGenAttention L k d l c)
    (genCornerWAt r L k d l w)
    (genCornerVAt r L k d l w v)

@[simp]
theorem eval_kHeadCornerSlopeProbeEvalPoly {L k d : Nat} (r : Nat)
    (θ : Params L k d) (w v : Vec d) (l : Fin L) (a c : Fin k) :
    (MvPolynomial.eval (kHeadParamFlat θ))
        (kHeadCornerSlopeProbeEvalPoly r L k d w v l a c) =
      MvPolynomial.eval (probePolyEval w v) (cornerSlopeDiffPoly r θ l a c) := by
  rw [eval_cornerSlopeDiffPoly]
  have hA :
      (kHeadGenAttention L k d l a - kHeadGenAttention L k d l c).map
          (MvPolynomial.eval (kHeadParamFlat θ)) =
        attentionMatrix θ l a - attentionMatrix θ l c := by
    ext i j
    simp [Matrix.map_apply, kHeadGenAttention]
  simp [kHeadCornerSlopeProbeEvalPoly, hA]

/-- Nonvanishing of a fixed-probe parameter polynomial implies the R3 corner-slope
probe polynomial is nonzero. -/
theorem cornerSlopeDiffPoly_ne_zero_of_probeEvalPoly_ne_zero {L k d : Nat}
    {r : Nat} {θ : Params L k d} {w v : Vec d}
    {l : Fin L} {a c : Fin k}
    (h :
      (MvPolynomial.eval (kHeadParamFlat θ))
        (kHeadCornerSlopeProbeEvalPoly r L k d w v l a c) ≠ 0) :
    cornerSlopeDiffPoly r θ l a c ≠ 0 := by
  exact (probePoly_ne_zero_iff_exists_eval_ne_zero
    (cornerSlopeDiffPoly r θ l a c)).mpr
      ⟨w, v, by simpa using h⟩

/-- Ordered corner-slope separation clauses. -/
abbrev KHeadCornerSlopeIndex (L k : Nat) : Type :=
  Fin L × DistinctHeadPair k

/-- The R3 corner-slope separation clauses indexed by ordered distinct head
pairs. -/
def KHeadCornerSlopeClauses {L k d : Nat} (r : Nat) (θ : Params L k d) : Prop :=
  ∀ l : Fin L, ∀ ac : DistinctHeadPair k,
    cornerSlopeDiffPoly r θ l ac.1.1 ac.1.2 ≠ 0

/-- Corner-slope polynomial for one ordered same-layer head pair, evaluated on a
fixed basis probe. -/
noncomputable def kHeadCornerSlopeBasisProbePoly {L k d : Nat} (r : Nat)
    (i0 : Fin d) : KHeadCornerSlopeIndex L k → KHeadParamRing L k d :=
  fun idx =>
    kHeadCornerSlopeProbeEvalPoly r L k d (Pi.single i0 1) (Pi.single i0 1)
      idx.1 idx.2.1.1 idx.2.1.2

private theorem valueSum_eq_zero_of_forall_value_zero {L k d : Nat}
    {θ : Params L k d} (hV : ∀ l a, valueMatrix θ l a = 0) (l : Fin L) :
    valueSum θ l = 0 := by
  simp [valueSum, hV]

private theorem valueSumStream_eq_zero_of_forall_value_zero {L k d : Nat}
    {θ : Params L k d} (hV : ∀ l a, valueMatrix θ l a = 0) (n : Nat) :
    valueSumStream θ n = 0 := by
  by_cases hn : n < L
  · simp [valueSumStream, hn, valueSum_eq_zero_of_forall_value_zero hV]
  · simp [valueSumStream, hn]

private theorem collapseMatrixStream_eq_one_of_forall_value_zero {L k d : Nat}
    {θ : Params L k d} (hV : ∀ l a, valueMatrix θ l a = 0) (n : Nat) :
    collapseMatrixStream θ n = 1 := by
  by_cases hn : n < L
  · simp [collapseMatrixStream, hn, collapseMatrix,
      valueSum_eq_zero_of_forall_value_zero hV]
  · simp [collapseMatrixStream, hn]

private theorem cornerKPrefix_eq_one_of_forall_value_zero {L k d : Nat}
    (r : Nat) {θ : Params L k d}
    (hV : ∀ l a, valueMatrix θ l a = 0) :
    ∀ n, cornerKPrefix r θ n = 1 := by
  intro n
  induction n with
  | zero =>
      simp [cornerKPrefix]
  | succ n ih =>
      calc
        cornerKPrefix r θ (n + 1) =
            cornerKStream r θ n * cornerKPrefix r θ n := rfl
        _ = 1 := by
          simp [cornerKStream, collapseMatrixStream_eq_one_of_forall_value_zero hV,
            valueSumStream_eq_zero_of_forall_value_zero hV, ih]

private theorem cornerCPrefix_eq_one_of_forall_value_zero {L k d : Nat}
    {θ : Params L k d} (hV : ∀ l a, valueMatrix θ l a = 0) :
    ∀ n, cornerCPrefix θ n = 1 := by
  intro n
  induction n with
  | zero =>
      simp [cornerCPrefix]
  | succ n ih =>
      calc
        cornerCPrefix θ (n + 1) =
            collapseMatrixStream θ n * cornerCPrefix θ n := rfl
        _ = 1 := by
          simp [collapseMatrixStream_eq_one_of_forall_value_zero hV, ih]

private theorem cornerDPrefix_eq_zero_of_forall_value_zero {L k d : Nat}
    (r : Nat) {θ : Params L k d}
    (hV : ∀ l a, valueMatrix θ l a = 0) :
    ∀ n, cornerDPrefix r θ n = 0 := by
  intro n
  induction n with
  | zero =>
      simp [cornerDPrefix]
  | succ n ih =>
      calc
        cornerDPrefix r θ (n + 1) =
            collapseMatrixStream θ n * cornerDPrefix r θ n +
              ((alpha r) • valueSumStream θ n) * cornerKPrefix r θ n := rfl
        _ = 0 := by
          simp [collapseMatrixStream_eq_one_of_forall_value_zero hV,
            valueSumStream_eq_zero_of_forall_value_zero hV,
            cornerKPrefix_eq_one_of_forall_value_zero r hV, ih]

private theorem kHead_matrixBilin_single_single {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) :
    matrixBilin A (Pi.single i 1) (Pi.single j 1) = A i j := by
  classical
  simp [matrixBilin]

/-- `K03D.E.prop-genericity-witnesses.P`, corner-slope part:
the fixed-basis-probe corner-slope polynomials are nonzero.  Their carriers
are stronger than the R3 predicate because a nonzero fixed probe evaluation
forces the whole probe polynomial to be nonzero. -/
theorem kHeadCornerSlopeBasisProbePoly_ne_zero {L k d : Nat} (r : Nat)
    (i0 : Fin d) :
    ∀ idx : KHeadCornerSlopeIndex L k,
      kHeadCornerSlopeBasisProbePoly (L := L) (k := k) (d := d) r i0 idx ≠ 0 := by
  classical
  intro idx
  let E : Matrix (Fin d) (Fin d) ℝ := matrixBasis (i0, i0)
  let θ : Params L k d := fun l' a' =>
    ((0 : Matrix (Fin d) (Fin d) ℝ),
      if l' = idx.1 ∧ a' = idx.2.1.1 then E else 0)
  refine mvPolynomial_ne_zero_of_eval_ne_zero (kHeadParamFlat θ) ?_
  rw [kHeadCornerSlopeBasisProbePoly, eval_kHeadCornerSlopeProbeEvalPoly,
    eval_cornerSlopeDiffPoly]
  have hV : ∀ l' a', valueMatrix θ l' a' = 0 := by
    intro l' a'
    simp [θ]
  have hA_left : attentionMatrix θ idx.1 idx.2.1.1 = E := by
    simp [θ, E]
  have hA_right : attentionMatrix θ idx.1 idx.2.1.2 = 0 := by
    have hne : idx.2.1.2 ≠ idx.2.1.1 := Ne.symm idx.2.2
    simp [θ, E, hne]
  have hA :
      attentionMatrix θ idx.1 idx.2.1.1 -
          attentionMatrix θ idx.1 idx.2.1.2 = E := by
    simp [hA_left, hA_right]
  have hWprobe :
      cornerKPrefix r θ idx.1.val *ᵥ Pi.single i0 1 = Pi.single i0 1 := by
    rw [cornerKPrefix_eq_one_of_forall_value_zero r hV idx.1.val]
    exact Matrix.one_mulVec (Pi.single i0 (1 : ℝ))
  have hVprobe :
      cornerCPrefix θ idx.1.val *ᵥ Pi.single i0 1 +
          cornerDPrefix r θ idx.1.val *ᵥ Pi.single i0 1 =
        Pi.single i0 1 := by
    rw [cornerCPrefix_eq_one_of_forall_value_zero hV idx.1.val,
      cornerDPrefix_eq_zero_of_forall_value_zero r hV idx.1.val]
    rw [Matrix.one_mulVec, Matrix.zero_mulVec]
    simp
  have htarget :
      matrixBilin
          (attentionMatrix θ idx.1 idx.2.1.1 -
            attentionMatrix θ idx.1 idx.2.1.2)
          (cornerKPrefix r θ idx.1.val *ᵥ Pi.single i0 1)
          (cornerCPrefix θ idx.1.val *ᵥ Pi.single i0 1 +
            cornerDPrefix r θ idx.1.val *ᵥ Pi.single i0 1) = 1 := by
    rw [hA, hWprobe, hVprobe, kHead_matrixBilin_single_single]
    simp [E, matrixBasis]
  exact by
    rw [htarget]
    norm_num

/-! ## Cascade-certificate parameter polynomials -/

/-- Generic cascade residue product along a fixed head chain. -/
noncomputable def genCascadeProduct (m k d : Nat) (h : Fin k)
    (χ : Fin m → Fin k) :
    Nat → Matrix (Fin d) (Fin d) (KHeadParamRing (m + 1) k d)
  | 0 => kHeadGenValue (m + 1) k d 0 h
  | n + 1 =>
      if hn : n < m then
        kHeadGenValue (m + 1) k d (laterLayer ⟨n, hn⟩) (χ ⟨n, hn⟩) *
          genCascadeProduct m k d h χ n
      else
        genCascadeProduct m k d h χ n

@[simp]
theorem map_genCascadeProduct {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (χ : Fin m → Fin k) :
    ∀ n,
      (genCascadeProduct m k d h χ n).map
          (MvPolynomial.eval (kHeadParamFlat θ)) =
        cascadeProduct θ h χ n := by
  intro n
  induction n with
  | zero =>
      simp [genCascadeProduct, cascadeProduct]
  | succ n ih =>
      by_cases hn : n < m
      · simp [genCascadeProduct, cascadeProduct, hn, Matrix.map_mul, ih]
      · simp [genCascadeProduct, cascadeProduct, hn, ih]

/-- Generic final cascade residue product. -/
noncomputable def genCascadeFinalProduct (m k d : Nat) (h : Fin k)
    (χ : Fin m → Fin k) :
    Matrix (Fin d) (Fin d) (KHeadParamRing (m + 1) k d) :=
  genCascadeProduct m k d h χ m

@[simp]
theorem map_genCascadeFinalProduct {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (χ : Fin m → Fin k) :
    (genCascadeFinalProduct m k d h χ).map
        (MvPolynomial.eval (kHeadParamFlat θ)) =
      cascadeFinalProduct θ h χ := by
  simp [genCascadeFinalProduct, cascadeFinalProduct]

/-- Generic ignition matrix for one later layer of a cascade chain. -/
noncomputable def genCascadeIgnitionMatrix (m k d : Nat) (h : Fin k)
    (χ : Fin m → Fin k) (j : Fin m) :
    Matrix (Fin d) (Fin d) (KHeadParamRing (m + 1) k d) :=
  genSym ((genCascadeProduct m k d h χ j.val)ᵀ *
    kHeadGenAttention (m + 1) k d (laterLayer j) (χ j) *
      genCascadeProduct m k d h χ j.val)

@[simp]
theorem map_genCascadeIgnitionMatrix {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (χ : Fin m → Fin k)
    (j : Fin m) :
    (genCascadeIgnitionMatrix m k d h χ j).map
        (MvPolynomial.eval (kHeadParamFlat θ)) =
      cascadeIgnitionMatrix θ h χ j := by
  rw [genCascadeIgnitionMatrix, cascadeIgnitionMatrix, map_genSym]
  simp [Matrix.map_mul, Matrix.transpose_map]

/-- Parameter polynomial for one cascade chain value. -/
noncomputable def kHeadCascadeChainValuePoly (m k d : Nat) (h : Fin k)
    (χ : Fin m → Fin k) : KHeadParamRing (m + 1) k d :=
  matrixFrobSqPoly (genCascadeFinalProduct m k d h χ) *
    ∏ j : Fin m, matrixFrobSqPoly (genCascadeIgnitionMatrix m k d h χ j)

@[simp]
theorem eval_kHeadCascadeChainValuePoly {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (χ : Fin m → Fin k) :
    (MvPolynomial.eval (kHeadParamFlat θ))
        (kHeadCascadeChainValuePoly m k d h χ) =
      cascadeChainValue θ h χ := by
  simp [kHeadCascadeChainValuePoly, cascadeChainValue]

/-- Parameter polynomial for the literal headwise cascade sum. -/
noncomputable def kHeadCascadeHeadPoly (m k d : Nat) (h : Fin k) :
    KHeadParamRing (m + 1) k d :=
  ∑ χ : Fin m → Fin k, kHeadCascadeChainValuePoly m k d h χ

@[simp]
theorem eval_kHeadCascadeHeadPoly {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) :
    (MvPolynomial.eval (kHeadParamFlat θ)) (kHeadCascadeHeadPoly m k d h) =
      ∑ χ : Fin m → Fin k, cascadeChainValue θ h χ := by
  simp [kHeadCascadeHeadPoly]

/-- Canonical cascade chain for head `h`: keep selecting head `h`. -/
def kHeadCascadeCanonicalChain {m k : Nat} (h : Fin k) : Fin m → Fin k :=
  fun _ => h

/-- The lower-degree canonical-chain cascade polynomial for one first-layer head. -/
noncomputable def kHeadCascadeCanonicalChainPoly (m k d : Nat) (h : Fin k) :
    KHeadParamRing (m + 1) k d :=
  kHeadCascadeChainValuePoly m k d h (kHeadCascadeCanonicalChain (m := m) h)

@[simp]
theorem eval_kHeadCascadeCanonicalChainPoly {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) :
    (MvPolynomial.eval (kHeadParamFlat θ))
        (kHeadCascadeCanonicalChainPoly m k d h) =
      cascadeChainValue θ h (kHeadCascadeCanonicalChain (m := m) h) := by
  simp [kHeadCascadeCanonicalChainPoly]

/-- Cascade chain values are nonnegative because they are products of squared
Frobenius norms. -/
theorem cascadeChainValue_nonneg {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (χ : Fin m → Fin k) :
    0 ≤ cascadeChainValue θ h χ := by
  unfold cascadeChainValue
  exact mul_nonneg (matrixFrobSq_nonneg _)
    (Finset.prod_nonneg fun j _ => matrixFrobSq_nonneg _)

/-- `K03D.E.prop-genericity-witnesses.P`, cascade-certificate part:
the canonical-chain cascade polynomials are nonzero when `d > 0`. -/
theorem kHeadCascadeCanonicalChainPoly_ne_zero {m k d : Nat} (hd : 0 < d) :
    ∀ h : Fin k, kHeadCascadeCanonicalChainPoly m k d h ≠ 0 := by
  classical
  intro h
  let χ0 : Fin m → Fin k := kHeadCascadeCanonicalChain (m := m) h
  let θ : Params (m + 1) k d := fun _l a =>
    (if a = h then (1 : Matrix (Fin d) (Fin d) ℝ) else 0,
      if a = h then (1 : Matrix (Fin d) (Fin d) ℝ) else 0)
  refine mvPolynomial_ne_zero_of_eval_ne_zero (kHeadParamFlat θ) ?_
  rw [kHeadCascadeCanonicalChainPoly, eval_kHeadCascadeChainValuePoly]
  change cascadeChainValue θ h χ0 ≠ 0
  have hV : ∀ l : Fin (m + 1), valueMatrix θ l h = 1 := by
    intro l
    simp [θ]
  have hA : ∀ l : Fin (m + 1), attentionMatrix θ l h = 1 := by
    intro l
    simp [θ]
  have hprod_one :
      ∀ n, n ≤ m → cascadeProduct θ h χ0 n = 1 := by
    intro n hnle
    induction n with
    | zero =>
        simpa [cascadeProduct] using hV (0 : Fin (m + 1))
    | succ n ih =>
        have hn : n < m := Nat.lt_of_succ_le hnle
        have hnle' : n ≤ m := Nat.le_of_lt hn
        calc
          cascadeProduct θ h χ0 (n + 1) =
              valueMatrix θ (laterLayer ⟨n, hn⟩) (χ0 ⟨n, hn⟩) *
                cascadeProduct θ h χ0 n := by
            simp [cascadeProduct, hn]
          _ = 1 := by
            rw [ih hnle']
            simp [χ0, kHeadCascadeCanonicalChain, hV]
  have hfinal_one : cascadeFinalProduct θ h χ0 = 1 := by
    simpa [cascadeFinalProduct] using hprod_one m le_rfl
  have hignition_one :
      ∀ j : Fin m, cascadeIgnitionMatrix θ h χ0 j = 1 := by
    intro j
    have hp := hprod_one j.val (Nat.le_of_lt j.isLt)
    simp [cascadeIgnitionMatrix, hp, χ0, kHeadCascadeCanonicalChain, hA,
      sym_one_matrix]
  have hfinal_pos :
      0 < matrixFrobSq (cascadeFinalProduct θ h χ0) := by
    rw [hfinal_one]
    exact matrixFrobSq_one_pos hd
  have hignition_pos :
      ∀ j : Fin m, 0 < matrixFrobSq (cascadeIgnitionMatrix θ h χ0 j) := by
    intro j
    rw [hignition_one j]
    exact matrixFrobSq_one_pos hd
  have hchain_pos : 0 < cascadeChainValue θ h χ0 := by
    unfold cascadeChainValue
    exact mul_pos hfinal_pos
      (Finset.prod_pos fun j _ => hignition_pos j)
  exact ne_of_gt hchain_pos

/-! ## Reusable finite polynomial covers for k-head parameter predicates -/

/-- Common nonvanishing locus of a k-head parameter-polynomial package. -/
def kHeadParamNonvanishingCarrier {L k d : Nat} {κ : Type*}
    (D : PolynomialNonvanishingData (KHeadParamCoord L k d) κ) :
    Set (Params L k d) :=
  kHeadParamFlat ⁻¹' D.carrier

@[simp]
theorem mem_kHeadParamNonvanishingCarrier {L k d : Nat} {κ : Type*}
    (D : PolynomialNonvanishingData (KHeadParamCoord L k d) κ)
    (θ : Params L k d) :
    θ ∈ kHeadParamNonvanishingCarrier D ↔
      ∀ a, a ∈ D.indices →
        (MvPolynomial.eval (kHeadParamFlat θ)) (D.poly a) ≠ 0 := by
  rfl

/-- A finite coordinate-polynomial package whose common nonvanishing locus implies
a k-head parameter predicate. -/
structure KHeadParamPolynomialPredicateCover
    (L k d : Nat) (P : Params L k d → Prop) : Type 1 where
  κ : Type
  data : PolynomialNonvanishingData (KHeadParamCoord L k d) κ
  carrier_subset : kHeadParamNonvanishingCarrier data ⊆ {θ | P θ}

namespace KHeadParamPolynomialPredicateCover

/-- The empty polynomial family covers the always-true k-head predicate. -/
def trueCover (L k d : Nat) :
    KHeadParamPolynomialPredicateCover L k d (fun _θ => True) where
  κ := Empty
  data :=
    { indices := ∅
      poly := Empty.elim
      nonzero := by
        intro a ha
        cases ha }
  carrier_subset := by
    intro θ hθ
    trivial

/-- Finite union/product assembly for conjunctions of k-head predicate covers. -/
noncomputable def and {L k d : Nat} {P Q : Params L k d → Prop}
    (CP : KHeadParamPolynomialPredicateCover L k d P)
    (CQ : KHeadParamPolynomialPredicateCover L k d Q) :
    KHeadParamPolynomialPredicateCover L k d (fun θ => P θ ∧ Q θ) where
  κ := CP.κ ⊕ CQ.κ
  data :=
    { indices := by
        classical
        exact CP.data.indices.map ⟨Sum.inl, Sum.inl_injective⟩ ∪
          CQ.data.indices.map ⟨Sum.inr, Sum.inr_injective⟩
      poly := fun a =>
        match a with
        | Sum.inl i => CP.data.poly i
        | Sum.inr i => CQ.data.poly i
      nonzero := by
        intro a ha
        classical
        cases a with
        | inl i =>
            exact CP.data.nonzero i (by
              have hi : Sum.inl i ∈ CP.data.indices.map ⟨Sum.inl, Sum.inl_injective⟩ :=
                Finset.mem_union.mp ha |>.resolve_right (by
                  intro h
                  simp [Finset.mem_map] at h)
              simpa [Finset.mem_map] using hi)
        | inr i =>
            exact CQ.data.nonzero i (by
              have hi : Sum.inr i ∈ CQ.data.indices.map ⟨Sum.inr, Sum.inr_injective⟩ :=
                Finset.mem_union.mp ha |>.resolve_left (by
                  intro h
                  simp [Finset.mem_map] at h)
              simpa [Finset.mem_map] using hi) }
  carrier_subset := by
    intro θ hθ
    constructor
    · apply CP.carrier_subset
      intro a ha
      exact hθ (Sum.inl a) (by
        classical
        exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨a, ha, rfl⟩))
    · apply CQ.carrier_subset
      intro a ha
      exact hθ (Sum.inr a) (by
        classical
        exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨a, ha, rfl⟩))

/-- Retarget a polynomial cover along a predicate implication, preserving the
same finite polynomial package. -/
def mono {L k d : Nat} {P Q : Params L k d → Prop}
    (C : KHeadParamPolynomialPredicateCover L k d P)
    (hPQ : ∀ θ, P θ → Q θ) :
    KHeadParamPolynomialPredicateCover L k d Q where
  κ := C.κ
  data := C.data
  carrier_subset := by
    intro θ hθ
    exact hPQ θ (C.carrier_subset hθ)

end KHeadParamPolynomialPredicateCover

/-! ## Cascade-certificate polynomial cover -/

/-- Concrete finite cover for cascade certificates.  The carried polynomial for
each first-layer head is the canonical chain that repeatedly selects the same
head; nonvanishing of that single nonnegative chain value forces the headwise
cascade sum to be nonzero. -/
noncomputable def kHeadCascadePolynomialCover (m k d : Nat) (hd : 0 < d) :
    KHeadParamPolynomialPredicateCover (m + 1) k d
      (fun θ => CascadeCertificate θ) where
  κ := Fin k
  data :=
    { indices := Finset.univ
      poly := kHeadCascadeCanonicalChainPoly m k d
      nonzero := by
        intro h _hh
        exact kHeadCascadeCanonicalChainPoly_ne_zero (m := m) (k := k) (d := d) hd h }
  carrier_subset := by
    intro θ hθ h
    have hpoly := hθ h (Finset.mem_univ h)
    have hchain_ne :
        cascadeChainValue θ h (kHeadCascadeCanonicalChain (m := m) h) ≠ 0 := by
      simpa using hpoly
    have hchain_pos :
        0 < cascadeChainValue θ h (kHeadCascadeCanonicalChain (m := m) h) :=
      lt_of_le_of_ne'
        (cascadeChainValue_nonneg θ h (kHeadCascadeCanonicalChain (m := m) h))
        hchain_ne
    have hsum_pos :
        0 < ∑ χ : Fin m → Fin k, cascadeChainValue θ h χ := by
      exact Finset.sum_pos'
        (s := (Finset.univ : Finset (Fin m → Fin k)))
        (f := fun χ : Fin m → Fin k => cascadeChainValue θ h χ)
        (fun χ _hχ => cascadeChainValue_nonneg θ h χ)
        ⟨kHeadCascadeCanonicalChain (m := m) h, Finset.mem_univ _, hchain_pos⟩
    exact ne_of_gt hsum_pos

/-! ## Tail-coordinate renaming for recursive k-head covers -/

/-- Embed k-head tail coordinates into one-more-layer coordinates by shifting the
layer index. -/
def tailKHeadParamCoordEmbedding (L k d : Nat) :
    KHeadParamCoord L k d → KHeadParamCoord (L + 1) k d :=
  fun c => (Fin.succ c.1, c.2)

theorem tailKHeadParamCoordEmbedding_injective (L k d : Nat) :
    Function.Injective (tailKHeadParamCoordEmbedding L k d) := by
  intro a b h
  cases a with
  | mk la ca =>
  cases b with
  | mk lb cb =>
    simp [tailKHeadParamCoordEmbedding] at h
    exact Prod.ext h.1 h.2

@[simp]
theorem kHeadParamFlat_tailKHeadParamCoordEmbedding {L k d : Nat}
    (θ : Params (L + 1) k d) (c : KHeadParamCoord L k d) :
    kHeadParamFlat θ (tailKHeadParamCoordEmbedding L k d c) =
      kHeadParamFlat (Fin.tail θ) c := by
  cases c with
  | mk l ac =>
  cases ac with
  | mk a coord =>
  cases coord with
  | inl ij =>
      cases ij
      rfl
  | inr ij =>
      cases ij
      rfl

theorem eval_tail_kHead_rename {L k d : Nat} (θ : Params (L + 1) k d)
    (p : KHeadParamRing L k d) :
    (MvPolynomial.eval (kHeadParamFlat θ))
        (MvPolynomial.rename (tailKHeadParamCoordEmbedding L k d) p) =
      (MvPolynomial.eval (kHeadParamFlat (Fin.tail θ))) p := by
  simpa [Function.comp_def] using
    (MvPolynomial.eval_rename (tailKHeadParamCoordEmbedding L k d)
      (kHeadParamFlat θ) p)

namespace KHeadParamPolynomialPredicateCover

/-- Lift a k-head predicate cover on tail parameters to a cover on one-more-layer
parameters. -/
noncomputable def tailLift {L k d : Nat} {P : Params L k d → Prop}
    (C : KHeadParamPolynomialPredicateCover L k d P) :
    KHeadParamPolynomialPredicateCover (L + 1) k d (fun θ => P (Fin.tail θ)) where
  κ := C.κ
  data :=
    { indices := C.data.indices
      poly := fun a =>
        MvPolynomial.rename (tailKHeadParamCoordEmbedding L k d) (C.data.poly a)
      nonzero := by
        intro a ha
        exact (MvPolynomial.rename_injective (tailKHeadParamCoordEmbedding L k d)
          (tailKHeadParamCoordEmbedding_injective L k d)).ne (C.data.nonzero a ha) }
  carrier_subset := by
    intro θ hθ
    apply C.carrier_subset
    intro a ha
    have h := hθ a ha
    simpa [eval_tail_kHead_rename θ (C.data.poly a)] using h

/-- Recursive-step assembly: combine a lifted tail cover with a current-step
k-head cover. -/
noncomputable def tailAnd {L k d : Nat} {P : Params L k d → Prop}
    {Q : Params (L + 1) k d → Prop}
    (Ctail : KHeadParamPolynomialPredicateCover L k d P)
    (Cstep : KHeadParamPolynomialPredicateCover (L + 1) k d Q) :
    KHeadParamPolynomialPredicateCover (L + 1) k d
      (fun θ => P (Fin.tail θ) ∧ Q θ) :=
  and (tailLift Ctail) Cstep

end KHeadParamPolynomialPredicateCover

/-! ## Local-openness determinant polynomials -/

private theorem matrix_mul_basis_mul_apply {d T : Nat}
    (V : Matrix (Fin d) (Fin d) ℝ) (G : Matrix (Fin T) (Fin T) ℝ)
    (p q : Fin d × Fin T) :
    (V * matrixBasis q * G) p.1 p.2 = V p.1 q.1 * G q.2 p.2 := by
  classical
  cases p with
  | mk pi pj =>
  cases q with
  | mk qi qj =>
  have hinner :
      ∀ x : Fin T,
        (∑ x_1 : Fin d, if x_1 = qi ∧ x = qj then V pi x_1 else 0) =
      if x = qj then V pi qi else 0 := by
    intro x
    by_cases hx : x = qj
    · subst x
      simp
    · simp [hx]
  simp [Matrix.mul_apply, matrixBasis, hinner]

private theorem matrix_finset_sum_apply {ι m n R : Type*} [AddCommMonoid R]
    (s : Finset ι) (M : ι → Matrix m n R) (i : m) (j : n) :
    (s.sum M) i j = s.sum (fun x => M x i j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert a s ha ih =>
      simp [Finset.sum_insert, ha, ih]

private theorem matrix_univ_sum_apply {ι m n R : Type*} [Fintype ι]
    [AddCommMonoid R] (M : ι → Matrix m n R) (i : m) (j : n) :
    (∑ x : ι, M x) i j = ∑ x : ι, M x i j := by
  exact matrix_finset_sum_apply (s := Finset.univ) M i j

private theorem localDerivative_value_sum_basis_apply {L k d r : Nat}
    (θ : Params L k d) (l : Fin L)
    (p q : Fin d × Fin (seqLength r)) :
    ((∑ a : Fin k, valueMatrix θ l a * matrixBasis q * gammaZero r) p.1 p.2) =
      ∑ a : Fin k, valueMatrix θ l a p.1 q.1 * gammaZero r q.2 p.2 := by
  classical
  rw [matrix_univ_sum_apply]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [matrix_mul_basis_mul_apply (V := valueMatrix θ l a) (G := gammaZero r)
    (p := p) (q := q)]

/-- Generic matrix of the local derivative operator in the finite coordinate basis. -/
noncomputable def genLocalDerivativeOperatorMatrix (r L k d : Nat) (l : Fin L) :
    Matrix (Fin d × Fin (seqLength r)) (Fin d × Fin (seqLength r))
      (KHeadParamRing L k d) :=
  fun p q =>
    (if p = q then 1 else 0) +
      ∑ a : Fin k,
        kHeadGenValue L k d l a p.1 q.1 *
          (MvPolynomial.C (gammaZero r q.2 p.2) : KHeadParamRing L k d)

@[simp]
theorem map_genLocalDerivativeOperatorMatrix {L k d : Nat} (r : Nat)
    (θ : Params L k d) (l : Fin L) :
    (genLocalDerivativeOperatorMatrix r L k d l).map
        (MvPolynomial.eval (kHeadParamFlat θ)) =
      matrixOperatorMatrix (localDerivative r θ l) := by
  ext p q
  cases p with
  | mk pi pj =>
  cases q with
  | mk qi qj =>
  simp [genLocalDerivativeOperatorMatrix, matrixOperatorMatrix, localDerivative,
    Matrix.map_apply, Matrix.add_apply, matrixBasis]
  rw [localDerivative_value_sum_basis_apply (θ := θ) (l := l)
    (p := (pi, pj)) (q := (qi, qj))]
  apply Finset.sum_congr rfl
  intro a _ha
  simp [kHeadGenValue]

/-- Evaluation of the generic local-openness determinant. -/
theorem eval_det_genLocalDerivativeOperatorMatrix {L k d : Nat} (r : Nat)
    (θ : Params L k d) (l : Fin L) :
    (MvPolynomial.eval (kHeadParamFlat θ))
        (genLocalDerivativeOperatorMatrix r L k d l).det =
      localOpennessDet r θ l := by
  rw [localOpennessDet, ← map_genLocalDerivativeOperatorMatrix r θ l]
  simpa [RingHom.mapMatrix_apply] using
    (RingHom.map_det (MvPolynomial.eval (kHeadParamFlat θ))
      (genLocalDerivativeOperatorMatrix r L k d l))

/-- Local-openness determinant polynomial for one layer. -/
noncomputable def kHeadLocalOpennessPoly (r L k d : Nat) (l : Fin L) :
    KHeadParamRing L k d :=
  (genLocalDerivativeOperatorMatrix r L k d l).det

/-- `K03D.E.prop-genericity-witnesses.P`, local-openness part:
each local derivative determinant polynomial is nonzero. -/
theorem kHeadLocalOpennessPoly_ne_zero (r L k d : Nat) :
    ∀ l : Fin L, kHeadLocalOpennessPoly r L k d l ≠ 0 := by
  classical
  intro l
  let θ : Params L k d := fun _l _a =>
    ((0 : Matrix (Fin d) (Fin d) ℝ), (0 : Matrix (Fin d) (Fin d) ℝ))
  refine mvPolynomial_ne_zero_of_eval_ne_zero (kHeadParamFlat θ) ?_
  rw [kHeadLocalOpennessPoly, eval_det_genLocalDerivativeOperatorMatrix r θ l,
    localOpennessDet]
  have hmat :
      matrixOperatorMatrix (localDerivative r θ l) =
        (1 : Matrix (Fin d × Fin (seqLength r)) (Fin d × Fin (seqLength r)) ℝ) := by
    have hderiv : localDerivative r θ l = fun H => H := by
      funext H
      ext i j
      simp [localDerivative, θ]
    rw [hderiv, matrixOperatorMatrix_id]
  simp [hmat]

/-- Concrete finite cover for local-openness determinant clauses. -/
noncomputable def kHeadLocalOpennessPolynomialCover (r L k d : Nat) :
    KHeadParamPolynomialPredicateCover L k d (fun θ => LocalOpenness r θ) where
  κ := Fin L
  data :=
    { indices := Finset.univ
      poly := kHeadLocalOpennessPoly r L k d
      nonzero := by
        intro l _hl
        exact kHeadLocalOpennessPoly_ne_zero r L k d l }
  carrier_subset := by
    intro θ hθ l
    have hpoly := hθ l (Finset.mem_univ l)
    simpa [kHeadLocalOpennessPoly, eval_det_genLocalDerivativeOperatorMatrix r θ l] using hpoly

/-- Concrete finite cover for the elementary matrix clauses `(R1)` and `(R2)`. -/
noncomputable def kHeadBasicMatrixPolynomialCover (L k d : Nat) (hd : 0 < d) :
    KHeadParamPolynomialPredicateCover L k d (fun θ => KHeadBasicMatrixClauses θ) where
  κ := KHeadBasicMatrixIndex L k
  data :=
    { indices := Finset.univ
      poly := kHeadBasicMatrixPoly
      nonzero := by
        intro idx _hidx
        exact kHeadBasicMatrixPoly_ne_zero (L := L) (k := k) (d := d) hd idx }
  carrier_subset := by
    intro θ hθ
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro l a
      have hpoly :=
        hθ (KHeadBasicMatrixIndex.detAttention l a) (Finset.mem_univ _)
      simpa [kHeadBasicMatrixPoly, eval_det_kHeadGenAttention θ l a] using hpoly
    · intro l a
      have hpoly :=
        hθ (KHeadBasicMatrixIndex.symAttention l a) (Finset.mem_univ _)
      simpa [kHeadBasicMatrixPoly] using hpoly
    · intro l a
      have hpoly := hθ (KHeadBasicMatrixIndex.value l a) (Finset.mem_univ _)
      simpa [kHeadBasicMatrixPoly] using hpoly
    · intro l ac
      have hpoly :=
        hθ (KHeadBasicMatrixIndex.headSeparation l ac) (Finset.mem_univ _)
      have hmap :
          (kHeadGenAttention L k d l ac.1.1 - kHeadGenAttention L k d l ac.1.2).map
              (MvPolynomial.eval (kHeadParamFlat θ)) =
            attentionMatrix θ l ac.1.1 - attentionMatrix θ l ac.1.2 := by
        ext i j
        simp [Matrix.map_apply, kHeadGenAttention]
      simpa [kHeadBasicMatrixPoly, hmap] using hpoly

/-- Concrete finite cover for the fixed-probe corner-slope clauses `(R3)`. -/
noncomputable def kHeadCornerSlopePolynomialCover (r L k d : Nat) (hd : 0 < d) :
    KHeadParamPolynomialPredicateCover L k d (fun θ => KHeadCornerSlopeClauses r θ) where
  κ := KHeadCornerSlopeIndex L k
  data :=
    { indices := Finset.univ
      poly := kHeadCornerSlopeBasisProbePoly r ⟨0, hd⟩
      nonzero := by
        intro idx _hidx
        exact kHeadCornerSlopeBasisProbePoly_ne_zero
          (L := L) (k := k) (d := d) r ⟨0, hd⟩ idx }
  carrier_subset := by
    intro θ hθ l ac
    have hpoly := hθ (l, ac) (Finset.mem_univ _)
    exact cornerSlopeDiffPoly_ne_zero_of_probeEvalPoly_ne_zero
      (L := L) (k := k) (d := d) (r := r) (θ := θ)
      (w := Pi.single ⟨0, hd⟩ 1) (v := Pi.single ⟨0, hd⟩ 1)
      (l := l) (a := ac.1.1) (c := ac.1.2) (by
        simpa [kHeadCornerSlopeBasisProbePoly] using hpoly)

/-- Concrete finite cover for all regularity clauses `(R1)`--`(R3)`. -/
noncomputable def kHeadRegularityPolynomialCover (r L k d : Nat) (hd : 0 < d) :
    KHeadParamPolynomialPredicateCover L k d (fun θ => Regularity r θ) :=
  KHeadParamPolynomialPredicateCover.mono
    (KHeadParamPolynomialPredicateCover.and
      (kHeadBasicMatrixPolynomialCover L k d hd)
      (kHeadCornerSlopePolynomialCover r L k d hd))
    (by
      intro θ hθ
      exact
        { det_attention_ne_zero := hθ.1.1
          sym_attention_ne_zero := hθ.1.2.1
          value_ne_zero := hθ.1.2.2.1
          head_separation := by
            intro l a c hac
            exact hθ.1.2.2.2 l ⟨(a, c), hac⟩
          corner_slope_separation := by
            intro l a c hac
            exact hθ.2 l ⟨(a, c), hac⟩ })

/-! ## Anchor-certificate parameter polynomials -/

/-- The same-layer anchor separation rows are all heads except the anchor head. -/
@[simp]
theorem fintype_card_anchorSeparationHead {k : Nat} (h : Fin k) :
    Fintype.card (AnchorSeparationHead k h) = k - 1 := by
  classical
  simp [AnchorSeparationHead, Fintype.card_subtype_compl (fun a : Fin k => a = h)]

/-- The number of anchor-certificate rows for one first-layer head. -/
@[simp]
theorem fintype_card_anchorRow {m k : Nat} (h : Fin k) :
    Fintype.card (AnchorRow m k h) = nBullet (m + 1) k + 1 := by
  classical
  have hk : 0 < k := Fin.pos h
  simp [AnchorRow, nBullet, Fintype.card_sum, Fintype.card_prod, Nat.mul_add,
    Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  omega

/-- Convert the explicit anchor row-count bound into the card hypothesis used by
coordinate embeddings. -/
theorem anchorRow_card_le_of_nBullet_succ_le {m k d : Nat} {h : Fin k}
    (hrows : nBullet (m + 1) k + 1 ≤ d) :
    Fintype.card (AnchorRow m k h) ≤ d := by
  rw [fintype_card_anchorRow]
  exact hrows

/-- Choose coordinate slots for the anchor rows from the explicit row-count bound. -/
noncomputable def anchorRowEmbeddingOfCardLe {m k d : Nat} {h : Fin k}
    (hrows : Fintype.card (AnchorRow m k h) ≤ d) :
    AnchorRow m k h ↪ Fin d where
  toFun := fun row => Fin.castLE hrows ((Fintype.equivFin (AnchorRow m k h)) row)
  inj' := by
    intro row row' hrow
    apply (Fintype.equivFin (AnchorRow m k h)).injective
    exact Fin.castLE_injective hrows hrow

/-- Choose coordinate slots for the anchor rows from the explicit
`n_bullet(m+1,k)+1 ≤ d` row-count bound. -/
noncomputable def anchorRowEmbeddingOfNBulletSuccLe {m k d : Nat} {h : Fin k}
    (hrows : nBullet (m + 1) k + 1 ≤ d) :
    AnchorRow m k h ↪ Fin d :=
  anchorRowEmbeddingOfCardLe (anchorRow_card_le_of_nBullet_succ_le hrows)

/-- Evaluation commutes with parameter-polynomial matrix-vector multiplication. -/
theorem eval_kHeadParamRing_mulVec {L k d : Nat} {m n : Type*} [Fintype n]
    (θ : Params L k d) (M : Matrix m n (KHeadParamRing L k d))
    (v : n → KHeadParamRing L k d) :
    (fun i => MvPolynomial.eval (kHeadParamFlat θ) (M.mulVec v i)) =
      (M.map (MvPolynomial.eval (kHeadParamFlat θ))).mulVec
        (fun j => MvPolynomial.eval (kHeadParamFlat θ) (v j)) := by
  funext i
  simp [Matrix.mulVec, dotProduct]

/-! ### Fixed-evaluation anchor Gram polynomials -/

/-- Generic polynomial vector for `w^h(t) = (I + (1-t)V_0h) w0`,
with `t` and `w0` fixed as real parameters. -/
noncomputable def genAnchorHeadDialWAt {m k d : Nat}
    (h : Fin k) (t : ℝ) (w0 : Vec d) : Fin d → KHeadParamRing (m + 1) k d :=
  ((1 : Matrix (Fin d) (Fin d) (KHeadParamRing (m + 1) k d)) +
      (MvPolynomial.C (1 - t) : KHeadParamRing (m + 1) k d) •
        kHeadGenValue (m + 1) k d 0 h) *ᵥ genConstVec w0

@[simp]
theorem eval_genAnchorHeadDialWAt {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (t : ℝ) (w0 : Vec d) :
    (fun i =>
      MvPolynomial.eval (kHeadParamFlat θ) (genAnchorHeadDialWAt h t w0 i)) =
      headDialW θ h t w0 := by
  rw [genAnchorHeadDialWAt, headDialW]
  trans
      (((1 : Matrix (Fin d) (Fin d) (KHeadParamRing (m + 1) k d)) +
          (MvPolynomial.C (1 - t) : KHeadParamRing (m + 1) k d) •
            kHeadGenValue (m + 1) k d 0 h).map
          (MvPolynomial.eval (kHeadParamFlat θ))) *ᵥ
        (fun i => MvPolynomial.eval (kHeadParamFlat θ) (genConstVec w0 i))
  · exact eval_kHeadParamRing_mulVec θ
      ((1 : Matrix (Fin d) (Fin d) (KHeadParamRing (m + 1) k d)) +
        (MvPolynomial.C (1 - t) : KHeadParamRing (m + 1) k d) •
          kHeadGenValue (m + 1) k d 0 h)
      (genConstVec w0)
  · rw [eval_genConstVec]
    congr 1
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, kHeadGenValue]
    · simp [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, kHeadGenValue, hij]

/-- Generic polynomial version of an anchor row gradient at fixed `(t,w0)`. -/
noncomputable def genAnchorRowGradientAt {m k d : Nat}
    (h : Fin k) (t : ℝ) (w0 : Vec d) :
    AnchorRow m k h → Fin d → KHeadParamRing (m + 1) k d
  | Sum.inl (Sum.inl _) =>
      (kHeadGenAttention (m + 1) k d 0 h)ᵀ *ᵥ genConstVec w0
  | Sum.inl (Sum.inr a) =>
      (kHeadGenAttention (m + 1) k d 0 a.1)ᵀ *ᵥ genConstVec w0
  | Sum.inr (Sum.inl jb) =>
      let j : Fin m := jb.1
      let b : Fin k := jb.2
      (genCornerCPrefix (m + 1) k d (j.val + 1))ᵀ *ᵥ
        ((kHeadGenAttention (m + 1) k d (laterLayer j) b)ᵀ *ᵥ
          genAnchorHeadDialWAt h t w0)
  | Sum.inr (Sum.inr _) =>
      -(((kHeadGenAttention (m + 1) k d 0 h)ᵀ *
          kHeadGenValue (m + 1) k d 0 h) *ᵥ genConstVec w0)

@[simp]
theorem eval_genAnchorRowGradientAt {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (t : ℝ) (w0 : Vec d)
    (row : AnchorRow m k h) :
    (fun i =>
      MvPolynomial.eval (kHeadParamFlat θ)
        (genAnchorRowGradientAt h t w0 row i)) =
      anchorRowGradient θ h t w0 row := by
  classical
  cases row with
  | inl row0 =>
      cases row0 with
      | inl u =>
          cases u
          rw [genAnchorRowGradientAt, anchorRowGradient]
          trans
              ((kHeadGenAttention (m + 1) k d 0 h)ᵀ).map
                  (MvPolynomial.eval (kHeadParamFlat θ)) *ᵥ
                (fun i => MvPolynomial.eval (kHeadParamFlat θ) (genConstVec w0 i))
          · exact eval_kHeadParamRing_mulVec θ
              ((kHeadGenAttention (m + 1) k d 0 h)ᵀ) (genConstVec w0)
          · rw [Matrix.transpose_map, map_kHeadGenAttention, eval_genConstVec]
      | inr a =>
          rw [genAnchorRowGradientAt, anchorRowGradient]
          trans
              ((kHeadGenAttention (m + 1) k d 0 a.1)ᵀ).map
                  (MvPolynomial.eval (kHeadParamFlat θ)) *ᵥ
                (fun i => MvPolynomial.eval (kHeadParamFlat θ) (genConstVec w0 i))
          · exact eval_kHeadParamRing_mulVec θ
              ((kHeadGenAttention (m + 1) k d 0 a.1)ᵀ) (genConstVec w0)
          · rw [Matrix.transpose_map, map_kHeadGenAttention, eval_genConstVec]
  | inr row1 =>
      cases row1 with
      | inl jb =>
          rcases jb with ⟨j, b⟩
          rw [genAnchorRowGradientAt, anchorRowGradient]
          trans
              ((genCornerCPrefix (m + 1) k d (j.val + 1))ᵀ).map
                  (MvPolynomial.eval (kHeadParamFlat θ)) *ᵥ
                (fun i =>
                  MvPolynomial.eval (kHeadParamFlat θ)
                    (((kHeadGenAttention (m + 1) k d (laterLayer j) b)ᵀ *ᵥ
                      genAnchorHeadDialWAt h t w0) i))
          · exact eval_kHeadParamRing_mulVec θ
              ((genCornerCPrefix (m + 1) k d (j.val + 1))ᵀ)
              ((kHeadGenAttention (m + 1) k d (laterLayer j) b)ᵀ *ᵥ
                genAnchorHeadDialWAt h t w0)
          · rw [Matrix.transpose_map, map_genCornerCPrefix]
            trans
                (collapsePrefix θ (j.val + 1))ᵀ *ᵥ
                  (((kHeadGenAttention (m + 1) k d (laterLayer j) b)ᵀ).map
                      (MvPolynomial.eval (kHeadParamFlat θ)) *ᵥ
                    (fun i =>
                      MvPolynomial.eval (kHeadParamFlat θ)
                        (genAnchorHeadDialWAt h t w0 i)))
            · congr
              exact eval_kHeadParamRing_mulVec θ
                ((kHeadGenAttention (m + 1) k d (laterLayer j) b)ᵀ)
                (genAnchorHeadDialWAt h t w0)
            · rw [Matrix.transpose_map, map_kHeadGenAttention,
                eval_genAnchorHeadDialWAt]
      | inr u =>
          cases u
          rw [genAnchorRowGradientAt, anchorRowGradient]
          trans
              -((((kHeadGenAttention (m + 1) k d 0 h)ᵀ *
                    kHeadGenValue (m + 1) k d 0 h).map
                  (MvPolynomial.eval (kHeadParamFlat θ))) *ᵥ
                (fun i => MvPolynomial.eval (kHeadParamFlat θ) (genConstVec w0 i)))
          ·
            have hmul := eval_kHeadParamRing_mulVec θ
              (((kHeadGenAttention (m + 1) k d 0 h)ᵀ *
                kHeadGenValue (m + 1) k d 0 h))
              (genConstVec w0)
            funext i
            simpa [Pi.neg_apply] using congrArg Neg.neg (congr_fun hmul i)
          · rw [Matrix.map_mul, Matrix.transpose_map, map_kHeadGenAttention,
              map_kHeadGenValue, eval_genConstVec]
            simp [Matrix.mulVec_mulVec]

/-- Generic polynomial matrix whose columns are the fixed-evaluation anchor
gradients. -/
noncomputable def genAnchorGradientMatrixAt {m k d : Nat}
    (h : Fin k) (t : ℝ) (w0 : Vec d) :
    Matrix (Fin d) (AnchorRow m k h) (KHeadParamRing (m + 1) k d) :=
  Matrix.of fun i row => genAnchorRowGradientAt h t w0 row i

@[simp]
theorem map_genAnchorGradientMatrixAt {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (t : ℝ) (w0 : Vec d) :
    (genAnchorGradientMatrixAt h t w0).map
        (MvPolynomial.eval (kHeadParamFlat θ)) =
      anchorGradientMatrix θ h t w0 := by
  ext i row
  exact congr_fun (eval_genAnchorRowGradientAt θ h t w0 row) i

/-- Parameter-coordinate polynomial obtained by evaluating the anchor Gram
determinant at fixed `(t,w0)`. -/
noncomputable def kHeadAnchorGramEvalPoly (m k d : Nat)
    (h : Fin k) (t : ℝ) (w0 : Vec d) : KHeadParamRing (m + 1) k d :=
  let G := genAnchorGradientMatrixAt h t w0
  ((Gᵀ * G) :
    Matrix (AnchorRow m k h) (AnchorRow m k h)
      (KHeadParamRing (m + 1) k d)).det

@[simp]
theorem eval_kHeadAnchorGramEvalPoly {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (t : ℝ) (w0 : Vec d) :
    (MvPolynomial.eval (kHeadParamFlat θ))
        (kHeadAnchorGramEvalPoly m k d h t w0) =
      anchorGramDet θ h t w0 := by
  let evalHom := MvPolynomial.eval (kHeadParamFlat θ)
  let Gp := genAnchorGradientMatrixAt (m := m) (k := k) (d := d) h t w0
  change evalHom (((Gpᵀ * Gp) :
    Matrix (AnchorRow m k h) (AnchorRow m k h)
      (KHeadParamRing (m + 1) k d)).det) =
      anchorGramDet θ h t w0
  rw [RingHom.map_det]
  change (((Gpᵀ * Gp).map evalHom) :
    Matrix (AnchorRow m k h) (AnchorRow m k h) ℝ).det =
      anchorGramDet θ h t w0
  rw [Matrix.map_mul, Matrix.transpose_map, map_genAnchorGradientMatrixAt]
  rfl

private noncomputable def coordinateColumnMatrix {α : Type*} {d : Nat}
    (e : α ↪ Fin d) : Matrix (Fin d) α ℝ :=
  fun i row => (Pi.single (e row) (1 : ℝ) : Fin d → ℝ) i

private theorem coordinateColumnMatrix_gram_eq_one {α : Type*} [Fintype α]
    [DecidableEq α] {d : Nat} (e : α ↪ Fin d) :
    ((coordinateColumnMatrix e)ᵀ * coordinateColumnMatrix e : Matrix α α ℝ) = 1 := by
  classical
  ext row row'
  rw [Matrix.mul_apply]
  by_cases hrow : row = row'
  · subst row'
    rw [Finset.sum_eq_single (e row)]
    · simp [coordinateColumnMatrix]
    · intro x _hx hxne
      simp [coordinateColumnMatrix, hxne]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ _))
  · have he : e row ≠ e row' := fun h => hrow (e.injective h)
    rw [Finset.sum_eq_zero]
    · simp [hrow]
    · intro x _hx
      by_cases hx : x = e row
      · subst x
        simp [coordinateColumnMatrix, he]
      · simp [coordinateColumnMatrix, hx]

private theorem anchorGramDet_eq_one_of_gradient_eq_coordinateColumnMatrix
    {m k d : Nat} {θ : Params (m + 1) k d} {h : Fin k}
    {t : ℝ} {w0 : Vec d} (e : AnchorRow m k h ↪ Fin d)
    (hG : anchorGradientMatrix θ h t w0 = coordinateColumnMatrix e) :
    anchorGramDet θ h t w0 = 1 := by
  simp [anchorGramDet, hG, coordinateColumnMatrix_gram_eq_one e]

private noncomputable def anchorWitnessW0 {m k d : Nat} {h : Fin k}
    (e : AnchorRow m k h ↪ Fin d) : Vec d :=
  Pi.single (e (anchorRowAnchor h)) 1

private noncomputable def anchorWitnessFirstValue {m k d : Nat} {h : Fin k}
    (e : AnchorRow m k h ↪ Fin d) (a : Fin k) :
    Matrix (Fin d) (Fin d) ℝ :=
  if a = h then
    matrixBasis (e (anchorRowTransversality h), e (anchorRowAnchor h))
  else
    0

private noncomputable def anchorWitnessFirstAttention {m k d : Nat} {h : Fin k}
    (e : AnchorRow m k h ↪ Fin d) (a : Fin k) :
    Matrix (Fin d) (Fin d) ℝ :=
  if ha : a = h then
    matrixBasis (e (anchorRowAnchor h), e (anchorRowAnchor h)) -
      matrixBasis (e (anchorRowTransversality h), e (anchorRowTransversality h))
  else
    matrixBasis (e (anchorRowAnchor h), e (anchorRowSeparation ⟨a, ha⟩))

private noncomputable def anchorWitnessLaterAttention {m k d : Nat} {h : Fin k}
    (e : AnchorRow m k h ↪ Fin d) (j : Fin m) (a : Fin k) :
    Matrix (Fin d) (Fin d) ℝ :=
  matrixBasis (e (anchorRowAnchor h), e (anchorRowLevel h j a))

private noncomputable def anchorWitnessParams {m k d : Nat} {h : Fin k}
    (e : AnchorRow m k h ↪ Fin d) : Params (m + 1) k d :=
  fun l a =>
    (Fin.cases (anchorWitnessFirstValue e a) (fun _j => 0) l,
      Fin.cases (anchorWitnessFirstAttention e a)
        (fun j => anchorWitnessLaterAttention e j a) l)

private theorem anchorRowTransversality_ne_anchor {m k : Nat} (h : Fin k) :
    anchorRowTransversality (m := m) h ≠ anchorRowAnchor h := by
  intro hrow
  cases hrow

private theorem anchorRowAnchor_ne_transversality {m k : Nat} (h : Fin k) :
    anchorRowAnchor (m := m) h ≠ anchorRowTransversality h := by
  exact Ne.symm (anchorRowTransversality_ne_anchor h)

private theorem anchorRowLevel_ne_transversality {m k : Nat}
    (h : Fin k) (j : Fin m) (a : Fin k) :
    anchorRowLevel h j a ≠ anchorRowTransversality h := by
  intro hrow
  cases hrow

private theorem anchorRowLevel_ne_anchor {m k : Nat}
    (h : Fin k) (j : Fin m) (a : Fin k) :
    anchorRowLevel h j a ≠ anchorRowAnchor h := by
  intro hrow
  cases hrow

private theorem anchorRowSeparation_ne_anchor {m k : Nat} {h : Fin k}
    (a : AnchorSeparationHead k h) :
    anchorRowSeparation (m := m) a ≠ anchorRowAnchor h := by
  intro hrow
  cases hrow

private theorem anchorRowSeparation_ne_transversality {m k : Nat} {h : Fin k}
    (a : AnchorSeparationHead k h) :
    anchorRowSeparation (m := m) a ≠ anchorRowTransversality h := by
  intro hrow
  cases hrow

private theorem matrixBasis_mulVec_single {d : Nat} (p q : Fin d) :
    matrixBasis (p, q) *ᵥ (Pi.single q 1 : Fin d → ℝ) =
      (Pi.single p 1 : Fin d → ℝ) := by
  ext i
  by_cases hi : i = p
  · subst i
    rw [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single q]
    · simp [matrixBasis]
    · intro x _hx hxne
      simp [matrixBasis, hxne]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ _))
  · rw [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_zero]
    · simp [hi]
    · intro x _hx
      simp [matrixBasis, hi]

private theorem matrixBasis_transpose_mulVec_single {d : Nat} (p q : Fin d) :
    (matrixBasis (p, q))ᵀ *ᵥ (Pi.single p 1 : Fin d → ℝ) =
      (Pi.single q 1 : Fin d → ℝ) := by
  ext i
  by_cases hi : i = q
  · subst i
    rw [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single p]
    · simp [matrixBasis]
    · intro x _hx hxne
      simp [matrixBasis, hxne]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ _))
  · rw [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_zero]
    · simp [hi]
    · intro x _hx
      simp [matrixBasis, hi]

private theorem matrixBasis_transpose_mulVec_single_of_ne {d : Nat}
    {p q r : Fin d} (hrp : r ≠ p) :
    (matrixBasis (p, q))ᵀ *ᵥ (Pi.single r 1 : Fin d → ℝ) = 0 := by
  ext i
  rw [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_zero]
  · simp
  · intro x _hx
    by_cases hx : x = r
    · subst x
      simp [matrixBasis, hrp]
    · simp [hx]

private theorem matrixBasis_col_self {d : Nat} (p q : Fin d) :
    (matrixBasis (p, q)).col q = (Pi.single p 1 : Fin d → ℝ) := by
  ext i
  by_cases hi : i = p
  · subst i
    simp [matrixBasis]
  · simp [matrixBasis, hi]

private theorem matrixBasis_row_self {d : Nat} (p q : Fin d) :
    (matrixBasis (p, q)).row p = (Pi.single q 1 : Fin d → ℝ) := by
  ext i
  by_cases hi : i = q
  · subst i
    simp [matrixBasis]
  · simp [matrixBasis, hi]

private theorem matrixBasis_col_of_ne {d : Nat} {p q r : Fin d} (hrq : r ≠ q) :
    (matrixBasis (p, q)).col r = (0 : Fin d → ℝ) := by
  ext i
  simp [matrixBasis, hrq]

private theorem matrixBasis_row_of_ne {d : Nat} {p q r : Fin d} (hrp : r ≠ p) :
    (matrixBasis (p, q)).row r = (0 : Fin d → ℝ) := by
  ext i
  simp [matrixBasis, hrp]

private theorem anchorWitness_gradient_anchor {m k d : Nat} {h : Fin k}
    (e : AnchorRow m k h ↪ Fin d) :
    anchorRowGradient (anchorWitnessParams e) h 1 (anchorWitnessW0 e)
        (anchorRowAnchor h) =
      (Pi.single (e (anchorRowAnchor h)) 1 : Vec d) := by
  have hne :
      e (anchorRowTransversality h) ≠ e (anchorRowAnchor h) := by
    exact fun hEq => anchorRowTransversality_ne_anchor h (e.injective hEq)
  ext i
  by_cases hi : i = e (anchorRowAnchor h)
  · subst i
    have hrow_ne :
        (Sum.inl (Sum.inl PUnit.unit) : AnchorRow m k h) ≠
          anchorRowTransversality h := by
      simpa [anchorRowAnchor] using anchorRowAnchor_ne_transversality (m := m) h
    simp [anchorRowGradient, anchorRowAnchor, anchorWitnessParams,
      anchorWitnessFirstAttention, anchorWitnessW0, matrixBasis, hrow_ne]
  ·
    have hi' : i ≠ e (Sum.inl (Sum.inl PUnit.unit) : AnchorRow m k h) := by
      simpa [anchorRowAnchor] using hi
    have hrow_ne :
        (Sum.inl (Sum.inl PUnit.unit) : AnchorRow m k h) ≠
          anchorRowTransversality h := by
      simpa [anchorRowAnchor] using anchorRowAnchor_ne_transversality (m := m) h
    simp [anchorRowGradient, anchorRowAnchor, anchorWitnessParams,
      anchorWitnessFirstAttention, anchorWitnessW0, matrixBasis, hi', hrow_ne]

private theorem anchorWitness_gradient_separation {m k d : Nat} {h : Fin k}
    (e : AnchorRow m k h ↪ Fin d) (a : AnchorSeparationHead k h) :
    anchorRowGradient (anchorWitnessParams e) h 1 (anchorWitnessW0 e)
        (anchorRowSeparation a) =
      (Pi.single (e (anchorRowSeparation a)) 1 : Vec d) := by
  have ha : ¬ a.1 = h := a.2
  ext i
  by_cases hi : i = e (anchorRowSeparation a)
  · subst i
    simp [anchorRowGradient, anchorRowSeparation, anchorWitnessParams,
      anchorWitnessFirstAttention, anchorWitnessW0, matrixBasis, ha]
  ·
    have hi' : i ≠ e (Sum.inl (Sum.inr a) : AnchorRow m k h) := by
      simpa [anchorRowSeparation] using hi
    simp [anchorRowGradient, anchorRowSeparation, anchorWitnessParams,
      anchorWitnessFirstAttention, anchorWitnessW0, matrixBasis, ha, hi']

private theorem anchorWitness_value_first_h_mul_w0 {m k d : Nat} {h : Fin k}
    (e : AnchorRow m k h ↪ Fin d) :
    valueMatrix (anchorWitnessParams e) 0 h *ᵥ anchorWitnessW0 e =
      (Pi.single (e (anchorRowTransversality h)) 1 : Vec d) := by
  ext i
  by_cases hi : i = e (anchorRowTransversality h)
  · subst i
    simp [anchorWitnessParams, anchorWitnessFirstValue, anchorWitnessW0,
      matrixBasis]
  · simp [anchorWitnessParams, anchorWitnessFirstValue, anchorWitnessW0,
      matrixBasis, hi]

private theorem anchorWitness_gradient_transversality {m k d : Nat} {h : Fin k}
    (e : AnchorRow m k h ↪ Fin d) :
    anchorRowGradient (anchorWitnessParams e) h 1 (anchorWitnessW0 e)
        (anchorRowTransversality h) =
      (Pi.single (e (anchorRowTransversality h)) 1 : Vec d) := by
  have hne :
      e (anchorRowAnchor h) ≠ e (anchorRowTransversality h) := by
    exact fun hEq => anchorRowAnchor_ne_transversality h (e.injective hEq)
  rw [anchorRowGradient_transversality, anchorWitness_value_first_h_mul_w0]
  change
    -((anchorWitnessFirstAttention e h)ᵀ *ᵥ
        (Pi.single (e (anchorRowTransversality h)) 1 : Vec d)) =
      (Pi.single (e (anchorRowTransversality h)) 1 : Vec d)
  ext i
  have hrow_ne :
      (anchorRowAnchor h : AnchorRow m k h) ≠ anchorRowTransversality h :=
    anchorRowAnchor_ne_transversality h
  have hrow_ne' :
      (anchorRowTransversality h : AnchorRow m k h) ≠ anchorRowAnchor h :=
    Ne.symm hrow_ne
  by_cases hi : i = e (anchorRowTransversality h)
  · subst i
    simp [anchorWitnessFirstAttention, matrixBasis, hrow_ne']
  ·
    have hi' : i ≠ e (Sum.inr (Sum.inr PUnit.unit) : AnchorRow m k h) := by
      simpa [anchorRowTransversality] using hi
    simp [anchorWitnessFirstAttention, matrixBasis, hrow_ne', hi]

private theorem anchorWitness_valueSum_zero {m k d : Nat} {h : Fin k}
    (e : AnchorRow m k h ↪ Fin d) :
    valueSum (anchorWitnessParams e) 0 =
      matrixBasis (e (anchorRowTransversality h), e (anchorRowAnchor h)) := by
  ext i j
  rw [valueSum, Matrix.sum_apply]
  rw [Finset.sum_eq_single h]
  · simp [anchorWitnessParams, anchorWitnessFirstValue]
  · intro a _ha hane
    simp [anchorWitnessParams, anchorWitnessFirstValue, hane]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ h))

private theorem anchorWitness_valueSum_later {m k d : Nat} {h : Fin k}
    (e : AnchorRow m k h ↪ Fin d) (j : Fin m) :
    valueSum (anchorWitnessParams e) (laterLayer j) = 0 := by
  ext i q
  simp [valueSum, anchorWitnessParams, laterLayer]

private theorem anchorWitness_collapseMatrix_zero_transpose_mulVec_of_row_ne_trans
    {m k d : Nat} {h : Fin k} (e : AnchorRow m k h ↪ Fin d)
    {row : AnchorRow m k h} (hrow : row ≠ anchorRowTransversality h) :
    (collapseMatrix (anchorWitnessParams e) 0)ᵀ *ᵥ
        (Pi.single (e row) 1 : Vec d) =
      (Pi.single (e row) 1 : Vec d) := by
  have hcoord : e row ≠ e (anchorRowTransversality h) := by
    exact fun hEq => hrow (e.injective hEq)
  rw [collapseMatrix, anchorWitness_valueSum_zero]
  rw [Matrix.transpose_add, Matrix.add_mulVec, Matrix.transpose_one, Matrix.one_mulVec]
  rw [matrixBasis_transpose_mulVec_single_of_ne hcoord]
  simp

private theorem anchorWitness_collapseMatrixStream_succ_eq_one
    {m k d : Nat} {h : Fin k} (e : AnchorRow m k h ↪ Fin d) (n : Nat) :
    collapseMatrixStream (anchorWitnessParams e) (n + 1) = 1 := by
  by_cases hn : n < m
  · have hsucc : n + 1 < m + 1 := Nat.succ_lt_succ hn
    let j : Fin m := ⟨n, hn⟩
    have hlayer : (⟨n + 1, hsucc⟩ : Fin (m + 1)) = laterLayer j := rfl
    simp [collapseMatrixStream, hsucc, collapseMatrix, hlayer,
      anchorWitness_valueSum_later]
  · have hnot : ¬ n + 1 < m + 1 := by
      exact fun hsucc => hn (Nat.succ_lt_succ_iff.mp hsucc)
    simp [collapseMatrixStream, hnot]

private theorem anchorWitness_collapsePrefix_succ_eq_first
    {m k d : Nat} {h : Fin k} (e : AnchorRow m k h ↪ Fin d) :
    ∀ n : Nat,
      collapsePrefix (anchorWitnessParams e) (n + 1) =
        collapseMatrix (anchorWitnessParams e) 0
  | 0 => by
      simp [collapsePrefix, cornerCPrefix, matrixPrefixProduct, collapseMatrixStream]
  | n + 1 => by
      have ih := anchorWitness_collapsePrefix_succ_eq_first e n
      change
        collapseMatrixStream (anchorWitnessParams e) (n + 1) *
            matrixPrefixProduct (collapseMatrixStream (anchorWitnessParams e)) (n + 1) =
          collapseMatrix (anchorWitnessParams e) 0
      rw [anchorWitness_collapseMatrixStream_succ_eq_one e n]
      simpa [collapsePrefix, cornerCPrefix] using ih

private theorem anchorWitness_collapsePrefix_transpose_mulVec_of_row_ne_trans
    {m k d : Nat} {h : Fin k} (e : AnchorRow m k h ↪ Fin d)
    {row : AnchorRow m k h} (hrow : row ≠ anchorRowTransversality h) :
    ∀ n : Nat, 0 < n →
      (collapsePrefix (anchorWitnessParams e) n)ᵀ *ᵥ
          (Pi.single (e row) 1 : Vec d) =
        (Pi.single (e row) 1 : Vec d)
  | 0, hn => False.elim (Nat.lt_asymm hn hn)
  | n + 1, _hn => by
      rw [anchorWitness_collapsePrefix_succ_eq_first e n]
      exact anchorWitness_collapseMatrix_zero_transpose_mulVec_of_row_ne_trans e hrow

private theorem anchorWitness_headDialW_one {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (w0 : Vec d) :
    headDialW θ h 1 w0 = w0 := by
  simp [headDialW]

private theorem anchorWitness_gradient_level {m k d : Nat} {h : Fin k}
    (e : AnchorRow m k h ↪ Fin d) (j : Fin m) (a : Fin k) :
    anchorRowGradient (anchorWitnessParams e) h 1 (anchorWitnessW0 e)
        (anchorRowLevel h j a) =
      (Pi.single (e (anchorRowLevel h j a)) 1 : Vec d) := by
  rw [anchorRowGradient_level, anchorWitness_headDialW_one]
  have hA :
      (attentionMatrix (anchorWitnessParams e) (laterLayer j) a)ᵀ *ᵥ
          anchorWitnessW0 e =
        (Pi.single (e (anchorRowLevel h j a)) 1 : Vec d) := by
    ext i
    by_cases hi : i = e (anchorRowLevel h j a)
    · subst i
      simp [anchorWitnessParams, anchorWitnessLaterAttention, anchorWitnessW0,
        laterLayer, matrixBasis]
    ·
      have hi' : i ≠ e (Sum.inr (Sum.inl (j, a)) : AnchorRow m k h) := by
        simpa [anchorRowLevel] using hi
      simp [anchorWitnessParams, anchorWitnessLaterAttention, anchorWitnessW0,
        laterLayer, matrixBasis, hi]
  rw [hA]
  exact anchorWitness_collapsePrefix_transpose_mulVec_of_row_ne_trans
    e (anchorRowLevel_ne_transversality h j a) (j.val + 1) (Nat.succ_pos j.val)

private theorem anchorWitness_gradientMatrix_eq_coordinateColumnMatrix
    {m k d : Nat} {h : Fin k} (e : AnchorRow m k h ↪ Fin d) :
    anchorGradientMatrix (anchorWitnessParams e) h 1 (anchorWitnessW0 e) =
      coordinateColumnMatrix e := by
  ext i row
  have hgrad :
      anchorRowGradient (anchorWitnessParams e) h 1 (anchorWitnessW0 e) row =
        (Pi.single (e row) 1 : Vec d) := by
    cases row with
    | inl row0 =>
        cases row0 with
        | inl u =>
            cases u
            exact anchorWitness_gradient_anchor e
        | inr a =>
            exact anchorWitness_gradient_separation e a
    | inr row1 =>
        cases row1 with
        | inl jb =>
            rcases jb with ⟨j, a⟩
            exact anchorWitness_gradient_level e j a
        | inr u =>
            cases u
            exact anchorWitness_gradient_transversality e
  simp [anchorGradientMatrix, coordinateColumnMatrix, hgrad]

/-- Fixed-evaluation anchor Gram determinant polynomial for one first-layer
head, using the explicit row-coordinate embedding supplied by the row budget. -/
noncomputable def kHeadAnchorHeadPoly (m k d : Nat)
    (hrows : nBullet (m + 1) k + 1 ≤ d) (h : Fin k) :
    KHeadParamRing (m + 1) k d :=
  let e := anchorRowEmbeddingOfNBulletSuccLe (h := h) hrows
  kHeadAnchorGramEvalPoly m k d h 1 (anchorWitnessW0 e)

/-- `K03D.E.prop-genericity-witnesses.P`, anchor-certificate part:
the fixed-evaluation anchor Gram polynomials are nonzero under the explicit
row-budget hypothesis. -/
theorem kHeadAnchorHeadPoly_ne_zero {m k d : Nat}
    (hrows : nBullet (m + 1) k + 1 ≤ d) :
    ∀ h : Fin k, kHeadAnchorHeadPoly m k d hrows h ≠ 0 := by
  classical
  intro h
  let e := anchorRowEmbeddingOfNBulletSuccLe (h := h) hrows
  let θ : Params (m + 1) k d := anchorWitnessParams e
  refine mvPolynomial_ne_zero_of_eval_ne_zero (kHeadParamFlat θ) ?_
  rw [kHeadAnchorHeadPoly, eval_kHeadAnchorGramEvalPoly]
  have hG := anchorWitness_gradientMatrix_eq_coordinateColumnMatrix e
  have hdet := anchorGramDet_eq_one_of_gradient_eq_coordinateColumnMatrix e hG
  rw [hdet]
  norm_num

/-- Concrete finite cover for all headwise anchor certificates. -/
noncomputable def kHeadAnchorPolynomialCover (m k d : Nat)
    (hrows : nBullet (m + 1) k + 1 ≤ d) :
    KHeadParamPolynomialPredicateCover (m + 1) k d
      (fun θ => AnchorCertificate θ) where
  κ := Fin k
  data :=
    { indices := Finset.univ
      poly := kHeadAnchorHeadPoly m k d hrows
      nonzero := by
        intro h _hh
        exact kHeadAnchorHeadPoly_ne_zero hrows h }
  carrier_subset := by
    intro θ hθ h
    let e := anchorRowEmbeddingOfNBulletSuccLe (h := h) hrows
    refine ⟨1, anchorWitnessW0 e, ?_⟩
    have hpoly := hθ h (Finset.mem_univ h)
    simpa [kHeadAnchorHeadPoly, e] using hpoly

/-- Current-step generic clauses with the anchor certificate left as a separate
assembly obligation. -/
def CurrentGenericClausesNoAnchor {m k d : Nat} (r : Nat)
    (θ : Params (m + 1) k d) : Prop :=
  Regularity r θ ∧ LocalOpenness r θ ∧ CascadeCertificate θ

/-- Add an anchor certificate to the no-anchor current-step package. -/
theorem currentGenericClauses_of_noAnchor {m k d r : Nat}
    {θ : Params (m + 1) k d}
    (hθ : CurrentGenericClausesNoAnchor r θ) (hanchor : AnchorCertificate θ) :
    CurrentGenericClauses r θ :=
  ⟨hθ.1, hθ.2.1, hθ.2.2, hanchor⟩

/-- Concrete finite cover for current-step generic clauses except for the anchor
certificate.  The cascade component is the existing `kHeadCascadePolynomialCover`. -/
noncomputable def kHeadCurrentGenericClausesNoAnchorPolynomialCover
    (r m k d : Nat) (hd : 0 < d) :
    KHeadParamPolynomialPredicateCover (m + 1) k d
      (fun θ => CurrentGenericClausesNoAnchor r θ) :=
  KHeadParamPolynomialPredicateCover.mono
    (KHeadParamPolynomialPredicateCover.and
      (KHeadParamPolynomialPredicateCover.and
        (kHeadRegularityPolynomialCover r (m + 1) k d hd)
        (kHeadLocalOpennessPolynomialCover r (m + 1) k d))
      (kHeadCascadePolynomialCover m k d hd))
    (by
      intro θ hθ
      exact ⟨hθ.1.1, hθ.1.2, hθ.2⟩)

/-- Concrete finite cover for the full current-step generic clauses. -/
noncomputable def kHeadCurrentGenericClausesPolynomialCover
    (r m k d : Nat) (hd : 0 < d)
    (hrows : nBullet (m + 1) k + 1 ≤ d) :
    KHeadParamPolynomialPredicateCover (m + 1) k d
      (fun θ => CurrentGenericClauses r θ) :=
  KHeadParamPolynomialPredicateCover.mono
    (KHeadParamPolynomialPredicateCover.and
      (kHeadCurrentGenericClausesNoAnchorPolynomialCover r m k d hd)
      (kHeadAnchorPolynomialCover m k d hrows))
    (by
      intro θ hθ
      exact currentGenericClauses_of_noAnchor hθ.1 hθ.2)

/-- Row-budget monotonicity for passing from a depth-`L+1` recursive cover to
its tail depth `L`. -/
theorem nBullet_tail_budget_of_succ {L k d : Nat}
    (hrows : nBullet (L + 1) k + 1 ≤ d) :
    nBullet L k + 1 ≤ d := by
  have hmono : nBullet L k ≤ nBullet (L + 1) k := by
    unfold nBullet
    exact Nat.mul_le_mul_left k (Nat.le_succ L)
  exact le_trans (Nat.add_le_add_right hmono 1) hrows

/-- Concrete finite recursive-generic polynomial cover.  Depth zero is the empty
cover; each successor combines the lifted tail cover with the full current-step
cover. -/
noncomputable def kHeadRecursiveGenericPolynomialCover (r : Nat) :
    (L k d : Nat) → 0 < d → nBullet L k + 1 ≤ d →
      KHeadParamPolynomialPredicateCover L k d
        (fun θ => RecursiveGeneric r L k d θ)
  | 0, k, d, _hd, _hrows =>
      KHeadParamPolynomialPredicateCover.trueCover 0 k d
  | L + 1, k, d, hd, hrows =>
      KHeadParamPolynomialPredicateCover.mono
        (KHeadParamPolynomialPredicateCover.tailAnd
          (kHeadRecursiveGenericPolynomialCover r L k d hd
            (nBullet_tail_budget_of_succ hrows))
          (kHeadCurrentGenericClausesPolynomialCover r L k d hd hrows))
        (by
          intro θ hθ
          simpa [RecursiveGeneric] using hθ)

end TransformerIdentifiability.NLayer.KHead
