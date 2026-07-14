import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Gauge
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.FormalStreams
import AnyLayerIdentifiabilityProof.NLayer.Foundations.ParamPolynomialGenericity

set_option autoImplicit false

open Filter Matrix
open scoped Matrix.Norms.Frobenius

namespace TransformerIdentifiability.NLayer.NoSkip

/-! ## Semantic no-skip regularity -/

/-- TeX Definition `def:regularity`, clauses R1--R4. -/
structure Regularity {L k d : Nat} (theta : Params L k d) : Prop where
  attention_det_ne_zero :
    ∀ l : Fin L, ∀ a : Fin k, (attentionMatrix theta l a).det ≠ 0
  attention_sym_ne_zero :
    ∀ l : Fin L, ∀ a : Fin k, sym (attentionMatrix theta l a) ≠ 0
  value_ne_zero :
    ∀ l : Fin L, ∀ a : Fin k, valueMatrix theta l a ≠ 0
  attention_pairwise : PairwiseDistinctAttentions theta
  transmission :
    ∀ l : Fin L, (collapseMatrix theta l).det ≠ 0
  joint_surjective :
    ∀ l : Fin L, JointSurjective theta l

namespace Regularity

variable {L k d : Nat} {theta : Params L k d}

theorem attention_ne_of_ne (h : Regularity theta) (l : Fin L) {a c : Fin k}
    (hac : a ≠ c) : attentionMatrix theta l a ≠ attentionMatrix theta l c :=
  fun heq => hac (h.attention_pairwise l heq)

theorem collapseMatrix_isUnit_det (h : Regularity theta) (l : Fin L) :
    IsUnit (collapseMatrix theta l).det :=
  Ne.isUnit (h.transmission l)

theorem jointSurjectivityGram_det_ne_zero (h : Regularity theta) (l : Fin L) :
    (jointSurjectivityGram theta l).det ≠ 0 :=
  (jointSurjective_iff_gram_det_ne_zero theta l).mp (h.joint_surjective l)

end Regularity

/-! ## Explicit R1/R2 parameter polynomials -/

/-- One coordinate of the shared `(V,A)` k-head parameter tuple. -/
abbrev NSParamCoord (L k d : Nat) :=
  Fin L × (Fin k × TransformerIdentifiability.NLayer.LayerCoord d)

abbrev NSParamRing (L k d : Nat) := MvPolynomial (NSParamCoord L k d) Real

def nsParamFlat {L k d : Nat} (theta : Params L k d) : NSParamCoord L k d → Real :=
  fun c => TransformerIdentifiability.NLayer.layerFlat (theta c.1 c.2.1) c.2.2

@[simp] theorem nsParamFlat_value {L k d : Nat} (theta : Params L k d)
    (l : Fin L) (a : Fin k) (i j : Fin d) :
    nsParamFlat theta (l, (a, Sum.inl (i, j))) = valueMatrix theta l a i j :=
  rfl

@[simp] theorem nsParamFlat_attention {L k d : Nat} (theta : Params L k d)
    (l : Fin L) (a : Fin k) (i j : Fin d) :
    nsParamFlat theta (l, (a, Sum.inr (i, j))) = attentionMatrix theta l a i j :=
  rfl

noncomputable def nsGenValue (L k d : Nat) (l : Fin L) (a : Fin k) :
    Matrix (Fin d) (Fin d) (NSParamRing L k d) :=
  fun i j => MvPolynomial.X (l, (a, Sum.inl (i, j)))

noncomputable def nsGenAttention (L k d : Nat) (l : Fin L) (a : Fin k) :
    Matrix (Fin d) (Fin d) (NSParamRing L k d) :=
  fun i j => MvPolynomial.X (l, (a, Sum.inr (i, j)))

@[simp] theorem map_nsGenValue {L k d : Nat} (theta : Params L k d)
    (l : Fin L) (a : Fin k) :
    (nsGenValue L k d l a).map (MvPolynomial.eval (nsParamFlat theta)) =
      valueMatrix theta l a := by
  ext i j
  simp [nsGenValue, nsParamFlat, Matrix.map_apply,
    TransformerIdentifiability.NLayer.layerFlat,
    TransformerIdentifiability.NLayer.sumFlat,
    TransformerIdentifiability.NLayer.matrixFlat]

@[simp] theorem map_nsGenAttention {L k d : Nat} (theta : Params L k d)
    (l : Fin L) (a : Fin k) :
    (nsGenAttention L k d l a).map (MvPolynomial.eval (nsParamFlat theta)) =
      attentionMatrix theta l a := by
  ext i j
  simp [nsGenAttention, nsParamFlat, Matrix.map_apply,
    TransformerIdentifiability.NLayer.layerFlat,
    TransformerIdentifiability.NLayer.sumFlat,
    TransformerIdentifiability.NLayer.matrixFlat]

noncomputable def matrixFrobSqNS {m n : Nat}
    (M : Matrix (Fin m) (Fin n) Real) : Real :=
  ∑ i : Fin m, ∑ j : Fin n, M i j * M i j

theorem matrixFrobSqNS_eq_zero_iff {m n : Nat}
    (M : Matrix (Fin m) (Fin n) Real) : matrixFrobSqNS M = 0 ↔ M = 0 := by
  constructor
  · intro h
    ext i j
    have hrow : (∑ j : Fin n, M i j * M i j) = 0 :=
      ((Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg (M i j))).mp h)
        i (Finset.mem_univ i)
    exact mul_self_eq_zero.mp
      (((Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => mul_self_nonneg (M i j))).mp hrow) j (Finset.mem_univ j))
  · rintro rfl
    simp [matrixFrobSqNS]

theorem matrixFrobSqNS_ne_zero_iff {m n : Nat}
    (M : Matrix (Fin m) (Fin n) Real) : matrixFrobSqNS M ≠ 0 ↔ M ≠ 0 :=
  not_congr (matrixFrobSqNS_eq_zero_iff M)

noncomputable def matrixFrobSqNSPoly {ι : Type*} {m n : Nat}
    (M : Matrix (Fin m) (Fin n) (MvPolynomial ι Real)) : MvPolynomial ι Real :=
  ∑ i : Fin m, ∑ j : Fin n, M i j * M i j

@[simp] theorem eval_matrixFrobSqNSPoly {ι : Type*} {m n : Nat}
    (rho : ι → Real) (M : Matrix (Fin m) (Fin n) (MvPolynomial ι Real)) :
    MvPolynomial.eval rho (matrixFrobSqNSPoly M) =
      matrixFrobSqNS (M.map (MvPolynomial.eval rho)) := by
  simp [matrixFrobSqNSPoly, matrixFrobSqNS, Matrix.map_apply]

noncomputable def nsGenSym {ι : Type*} {d : Nat}
    (M : Matrix (Fin d) (Fin d) (MvPolynomial ι Real)) :
    Matrix (Fin d) (Fin d) (MvPolynomial ι Real) :=
  (MvPolynomial.C ((2 : Real)⁻¹) : MvPolynomial ι Real) • (M + Mᵀ)

@[simp] theorem map_nsGenSym {ι : Type*} {d : Nat} (rho : ι → Real)
    (M : Matrix (Fin d) (Fin d) (MvPolynomial ι Real)) :
    (nsGenSym M).map (MvPolynomial.eval rho) =
      sym (M.map (MvPolynomial.eval rho)) := by
  ext i j
  simp [nsGenSym, sym, Matrix.map_apply, Matrix.smul_apply, Matrix.add_apply]
  ring

abbrev DistinctHeadPairNS (k : Nat) := {ac : Fin k × Fin k // ac.1 ≠ ac.2}

inductive BasicMatrixIndexNS (L k : Nat)
  | detAttention (l : Fin L) (a : Fin k)
  | symAttention (l : Fin L) (a : Fin k)
  | value (l : Fin L) (a : Fin k)
  | headSeparation (l : Fin L) (ac : DistinctHeadPairNS k)
  deriving DecidableEq, Fintype

noncomputable def basicMatrixPolyNS {L k d : Nat} :
    BasicMatrixIndexNS L k → NSParamRing L k d
  | .detAttention l a => (nsGenAttention L k d l a).det
  | .symAttention l a => matrixFrobSqNSPoly (nsGenSym (nsGenAttention L k d l a))
  | .value l a => matrixFrobSqNSPoly (nsGenValue L k d l a)
  | .headSeparation l ac =>
      matrixFrobSqNSPoly
        (nsGenAttention L k d l ac.1.1 - nsGenAttention L k d l ac.1.2)

def BasicMatrixClausesNS {L k d : Nat} (theta : Params L k d) : Prop :=
  (∀ l a, (attentionMatrix theta l a).det ≠ 0) ∧
  (∀ l a, sym (attentionMatrix theta l a) ≠ 0) ∧
  (∀ l a, valueMatrix theta l a ≠ 0) ∧
  PairwiseDistinctAttentions theta

theorem eval_det_nsGenAttention {L k d : Nat} (theta : Params L k d)
    (l : Fin L) (a : Fin k) :
    MvPolynomial.eval (nsParamFlat theta) (nsGenAttention L k d l a).det =
      (attentionMatrix theta l a).det := by
  rw [← map_nsGenAttention theta l a]
  exact RingHom.map_det _ _

@[simp] theorem eval_basicMatrixPolyNS {L k d : Nat} (theta : Params L k d) :
    ∀ idx : BasicMatrixIndexNS L k,
      MvPolynomial.eval (nsParamFlat theta) (basicMatrixPolyNS (d := d) idx) =
        match idx with
        | .detAttention l a => (attentionMatrix theta l a).det
        | .symAttention l a => matrixFrobSqNS (sym (attentionMatrix theta l a))
        | .value l a => matrixFrobSqNS (valueMatrix theta l a)
        | .headSeparation l ac => matrixFrobSqNS
            (attentionMatrix theta l ac.1.1 - attentionMatrix theta l ac.1.2) := by
  intro idx
  cases idx <;>
    simp [basicMatrixPolyNS, eval_det_nsGenAttention, Matrix.map_sub]

theorem basicMatrixClausesNS_iff {L k d : Nat} (theta : Params L k d) :
    BasicMatrixClausesNS theta ↔
      ∀ idx : BasicMatrixIndexNS L k,
        MvPolynomial.eval (nsParamFlat theta) (basicMatrixPolyNS (d := d) idx) ≠ 0 := by
  constructor
  · rintro ⟨hdet, hsym, hvalue, hpair⟩ idx
    cases idx with
    | detAttention l a => simpa using hdet l a
    | symAttention l a =>
        rw [eval_basicMatrixPolyNS, matrixFrobSqNS_ne_zero_iff]
        exact hsym l a
    | value l a =>
        rw [eval_basicMatrixPolyNS, matrixFrobSqNS_ne_zero_iff]
        exact hvalue l a
    | headSeparation l ac =>
        rw [eval_basicMatrixPolyNS, matrixFrobSqNS_ne_zero_iff, sub_ne_zero]
        exact fun heq => ac.2 (hpair l heq)
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro l a
      simpa using h (.detAttention l a)
    · intro l a
      have hs := h (.symAttention l a)
      simpa [matrixFrobSqNS_ne_zero_iff] using hs
    · intro l a
      have hv := h (.value l a)
      simpa [matrixFrobSqNS_ne_zero_iff] using hv
    · intro l a c heq
      by_contra hac
      have hs := h (.headSeparation l ⟨(a, c), hac⟩)
      exact hs (by simp [eval_basicMatrixPolyNS, heq, matrixFrobSqNS])

/-! ## Explicit R3/R4 parameter polynomials -/

noncomputable def nsGenValueSum (L k d : Nat) (l : Fin L) :
    Matrix (Fin d) (Fin d) (NSParamRing L k d) :=
  ∑ a : Fin k, nsGenValue L k d l a

noncomputable def nsGenJointGram (L k d : Nat) (l : Fin L) :
    Matrix (Fin d) (Fin d) (NSParamRing L k d) :=
  ∑ a : Fin k, nsGenValue L k d l a * (nsGenValue L k d l a)ᵀ

@[simp] theorem map_nsGenValueSum {L k d : Nat} (theta : Params L k d)
    (l : Fin L) :
    (nsGenValueSum L k d l).map (MvPolynomial.eval (nsParamFlat theta)) =
      collapseMatrix theta l := by
  ext i j
  simp [nsGenValueSum, collapseMatrix, valueSum, Matrix.map_apply, Matrix.sum_apply,
    nsGenValue]

@[simp] theorem map_nsGenJointGram {L k d : Nat} (theta : Params L k d)
    (l : Fin L) :
    (nsGenJointGram L k d l).map (MvPolynomial.eval (nsParamFlat theta)) =
      jointSurjectivityGram theta l := by
  ext i j
  simp [nsGenJointGram, jointSurjectivityGram, Matrix.map_apply, Matrix.sum_apply,
    Matrix.mul_apply, nsGenValue]

inductive StructuralMatrixIndexNS (L : Nat)
  | transmission (l : Fin L)
  | jointSurjectivity (l : Fin L)
  deriving DecidableEq, Fintype

noncomputable def structuralMatrixPolyNS {L k d : Nat} :
    StructuralMatrixIndexNS L → NSParamRing L k d
  | .transmission l => (nsGenValueSum L k d l).det
  | .jointSurjectivity l => (nsGenJointGram L k d l).det

def StructuralMatrixClausesNS {L k d : Nat} (theta : Params L k d) : Prop :=
  (∀ l : Fin L, (collapseMatrix theta l).det ≠ 0) ∧
    (∀ l : Fin L, JointSurjective theta l)

@[simp] theorem eval_structuralMatrixPolyNS {L k d : Nat} (theta : Params L k d) :
    ∀ idx : StructuralMatrixIndexNS L,
      MvPolynomial.eval (nsParamFlat theta) (structuralMatrixPolyNS (k := k) (d := d) idx) =
        match idx with
        | .transmission l => (collapseMatrix theta l).det
        | .jointSurjectivity l => (jointSurjectivityGram theta l).det := by
  intro idx
  cases idx with
  | transmission l =>
      simp only [structuralMatrixPolyNS]
      rw [← map_nsGenValueSum theta l]
      exact RingHom.map_det _ _
  | jointSurjectivity l =>
      simp only [structuralMatrixPolyNS]
      rw [← map_nsGenJointGram theta l]
      exact RingHom.map_det _ _

theorem structuralMatrixClausesNS_iff {L k d : Nat} (theta : Params L k d) :
    StructuralMatrixClausesNS theta ↔
      ∀ idx : StructuralMatrixIndexNS L,
        MvPolynomial.eval (nsParamFlat theta)
          (structuralMatrixPolyNS (k := k) (d := d) idx) ≠ 0 := by
  constructor
  · rintro ⟨htrans, hjoint⟩ idx
    cases idx with
    | transmission l => simpa using htrans l
    | jointSurjectivity l =>
        rw [eval_structuralMatrixPolyNS]
        exact (jointSurjective_iff_gram_det_ne_zero theta l).mp (hjoint l)
  · intro h
    refine ⟨?_, ?_⟩
    · intro l
      simpa using h (.transmission l)
    · intro l
      apply (jointSurjective_iff_gram_det_ne_zero theta l).mpr
      simpa using h (.jointSurjectivity l)

theorem regularity_iff_polynomial_clauses {L k d : Nat} (theta : Params L k d) :
    Regularity theta ↔ BasicMatrixClausesNS theta ∧ StructuralMatrixClausesNS theta := by
  constructor
  · intro h
    exact ⟨⟨h.attention_det_ne_zero, h.attention_sym_ne_zero, h.value_ne_zero,
      h.attention_pairwise⟩, h.transmission, h.joint_surjective⟩
  · rintro ⟨⟨hdet, hsym, hvalue, hpair⟩, htrans, hjoint⟩
    exact ⟨hdet, hsym, hvalue, hpair, htrans, hjoint⟩

/-! ## All-`alpha` corner streams -/

/-- Constant gate family `z_{la} = alpha r` at every layer and head. -/
noncomputable def allAlphaGateFamily (r L k : Nat) : FrozenGateFamily L k :=
  fun _ _ ↦ alpha r

@[simp] theorem allAlphaGateFamily_apply (r : Nat) {L k : Nat}
    (l : Fin L) (a : Fin k) :
    allAlphaGateFamily r L k l a = alpha r :=
  rfl

/-- The collapsed-matrix prefix `C_{n-1:0}` used at the all-`alpha` corner. -/
noncomputable def alphaCornerCPrefix {L k d : Nat} (r : Nat) (theta : Params L k d)
    (n : Nat) (hn : n ≤ L) : Matrix (Fin d) (Fin d) Real :=
  frozenP theta (allAlphaGateFamily r L k) n hn

@[simp] theorem alphaCornerCPrefix_zero {L k d : Nat} (r : Nat)
    (theta : Params L k d) (h0 : 0 ≤ L) :
    alphaCornerCPrefix r theta 0 h0 = 1 :=
  rfl

@[simp] theorem alphaCornerCPrefix_succ {L k d : Nat} (r : Nat)
    (theta : Params L k d) {n : Nat} (hn : n + 1 ≤ L) :
    alphaCornerCPrefix r theta (n + 1) hn =
      collapseMatrix theta ⟨n, Nat.lt_of_succ_le hn⟩ *
        alphaCornerCPrefix r theta n (Nat.le_of_succ_le hn) :=
  rfl

/-- At the all-`alpha` corner, `D_l = alpha C_l`. -/
theorem frozenD_allAlpha {L k d : Nat} (r : Nat) (theta : Params L k d)
    (l : Fin L) :
    frozenD theta (allAlphaGateFamily r L k) l = alpha r • collapseMatrix theta l := by
  rw [frozenD_eq_sum, collapseMatrix_eq_valueSum]
  simp only [allAlphaGateFamily_apply, valueSum]
  exact (Finset.smul_sum :
    alpha r • (∑ a : Fin k, valueMatrix theta l a) =
      ∑ a : Fin k, alpha r • valueMatrix theta l a).symm

/-- At the all-`alpha` corner, `K_l = (1-alpha) C_l`. -/
theorem frozenK_allAlpha {L k d : Nat} (r : Nat) (theta : Params L k d)
    (l : Fin L) :
    frozenK theta (allAlphaGateFamily r L k) l =
      (1 - alpha r) • collapseMatrix theta l := by
  rw [frozenK, frozenD_allAlpha]
  ext i j
  simp [Matrix.sub_apply, Matrix.smul_apply]
  ring

/-- Closed all-`alpha` contrast product
`R_n = (1-alpha)^n C_{n-1:0}` for every bounded prefix. -/
theorem frozenR_allAlpha {L k d : Nat} (r : Nat) (theta : Params L k d) :
    ∀ (n : Nat) (hn : n ≤ L),
      frozenR theta (allAlphaGateFamily r L k) n hn =
        ((1 - alpha r) ^ n) • alphaCornerCPrefix r theta n hn
  | 0, _hn => by simp
  | n + 1, hn => by
      rw [frozenR_succ, frozenK_allAlpha,
        frozenR_allAlpha r theta n (Nat.le_of_succ_le hn)]
      rw [alphaCornerCPrefix_succ, pow_succ]
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      ring_nf

/-- Closed all-`alpha` transfer matrix
`Q_n = (1-(1-alpha)^n) C_{n-1:0}`. -/
theorem frozenQ_allAlpha {L k d : Nat} (r : Nat) (theta : Params L k d)
    (n : Nat) (hn : n ≤ L) :
    frozenQ theta (allAlphaGateFamily r L k) n hn =
      (1 - (1 - alpha r) ^ n) • alphaCornerCPrefix r theta n hn := by
  have hcons := frozenR_add_Q_eq_P theta (allAlphaGateFamily r L k) n hn
  rw [frozenR_allAlpha r theta n hn] at hcons
  simp only [alphaCornerCPrefix] at hcons
  change
    frozenQ theta (allAlphaGateFamily r L k) n hn =
      (1 - (1 - alpha r) ^ n) •
        frozenP theta (allAlphaGateFamily r L k) n hn
  ext i j
  have hij := congr_fun (congr_fun hcons i) j
  simp only [Matrix.add_apply, Matrix.smul_apply] at hij ⊢
  linear_combination hij

/-- Bounded-prefix all-`alpha` contrast stream formula. -/
theorem eval_formalW_allAlpha {L k d : Nat} (r : Nat) (theta : Params L k d)
    (w v : Vec d) (n : Nat) (hn : n ≤ L) :
    evalFormalVec (frozenGateAssignment (allAlphaGateFamily r L k))
        (formalW theta w v n hn) =
      ((1 - alpha r) ^ n) • (alphaCornerCPrefix r theta n hn *ᵥ w) := by
  rw [eval_formalW_frozenGateAssignment, frozenR_allAlpha]
  exact Matrix.smul_mulVec _ _ _

/-- Bounded-prefix all-`alpha` last-token stream formula. -/
theorem eval_formalV_allAlpha {L k d : Nat} (r : Nat) (theta : Params L k d)
    (w v : Vec d) (n : Nat) (hn : n ≤ L) :
    evalFormalVec (frozenGateAssignment (allAlphaGateFamily r L k))
        (formalV theta w v n hn) =
      alphaCornerCPrefix r theta n hn *ᵥ
        (v + (1 - (1 - alpha r) ^ n) • w) := by
  rw [eval_formalV_frozenGateAssignment, frozenQ_allAlpha]
  simp only [alphaCornerCPrefix, Matrix.smul_mulVec, Matrix.mulVec_add,
    Matrix.mulVec_smul]

/-- Empty-prefix corner streams are the initial probe streams. -/
@[simp] theorem eval_formalPoint_allAlpha_zero {L k d : Nat} (r : Nat)
    (theta : Params L k d) (w v : Vec d) (h0 : 0 ≤ L) :
    (evalFormalVec (frozenGateAssignment (allAlphaGateFamily r L k))
        (formalW theta w v 0 h0),
      evalFormalVec (frozenGateAssignment (allAlphaGateFamily r L k))
        (formalV theta w v 0 h0)) = (w, v) := by
  simp

/-- TeX `eq:alpha-corner-streams` in zero-based layer indexing.

For `l : Fin L`, the prefix length `l.val` corresponds to TeX `ell-1`.
-/
theorem alphaCornerStreams {L k d : Nat} (r : Nat) (theta : Params L k d)
    (l : Fin L) (w v : Vec d) :
    evalFormalVec (frozenGateAssignment (allAlphaGateFamily r L k))
          (formalW theta w v l.1 (Nat.le_of_lt l.2)) =
        ((1 - alpha r) ^ l.1) •
          (alphaCornerCPrefix r theta l.1 (Nat.le_of_lt l.2) *ᵥ w) ∧
      evalFormalVec (frozenGateAssignment (allAlphaGateFamily r L k))
          (formalV theta w v l.1 (Nat.le_of_lt l.2)) =
        alphaCornerCPrefix r theta l.1 (Nat.le_of_lt l.2) *ᵥ
          (v + (1 - (1 - alpha r) ^ l.1) • w) :=
  ⟨eval_formalW_allAlpha r theta w v l.1 (Nat.le_of_lt l.2),
    eval_formalV_allAlpha r theta w v l.1 (Nat.le_of_lt l.2)⟩

/-! ## Automatic all-`alpha` corner separation -/

/-- Probe-polynomial variables, with one coordinate block each for `w` and `v`. -/
abbrev AlphaCornerProbeVar (d : Nat) : Type := Sum (Fin d) (Fin d)

/-- Polynomial ring for all-`alpha` corner slopes. -/
abbrev AlphaCornerProbePoly (d : Nat) : Type :=
  MvPolynomial (AlphaCornerProbeVar d) Real

noncomputable def alphaCornerProbeW {d : Nat} : Fin d → AlphaCornerProbePoly d :=
  fun i ↦ MvPolynomial.X (Sum.inl i)

noncomputable def alphaCornerProbeV {d : Nat} : Fin d → AlphaCornerProbePoly d :=
  fun i ↦ MvPolynomial.X (Sum.inr i)

def alphaCornerProbeEval {d : Nat} (w v : Vec d) : AlphaCornerProbeVar d → Real
  | Sum.inl i => w i
  | Sum.inr i => v i

noncomputable def realMatrixToAlphaCornerProbePoly {d : Nat}
    (M : Matrix (Fin d) (Fin d) Real) :
    Matrix (Fin d) (Fin d) (AlphaCornerProbePoly d) :=
  M.map (MvPolynomial.C : Real →+* AlphaCornerProbePoly d)

noncomputable def alphaCornerProbeBilin {d : Nat}
    (A : Matrix (Fin d) (Fin d) Real)
    (w v : Fin d → AlphaCornerProbePoly d) : AlphaCornerProbePoly d :=
  w ⬝ᵥ realMatrixToAlphaCornerProbePoly A *ᵥ v

noncomputable def alphaCornerWPoly {L k d : Nat} (r : Nat)
    (theta : Params L k d) (l : Fin L) : Fin d → AlphaCornerProbePoly d :=
  (MvPolynomial.C ((1 - alpha r) ^ l.1) : AlphaCornerProbePoly d) •
    (realMatrixToAlphaCornerProbePoly
      (alphaCornerCPrefix r theta l.1 (Nat.le_of_lt l.2)) *ᵥ
        alphaCornerProbeW (d := d))

noncomputable def alphaCornerVPoly {L k d : Nat} (r : Nat)
    (theta : Params L k d) (l : Fin L) : Fin d → AlphaCornerProbePoly d :=
  realMatrixToAlphaCornerProbePoly
      (alphaCornerCPrefix r theta l.1 (Nat.le_of_lt l.2)) *ᵥ
    (alphaCornerProbeV (d := d) +
      (MvPolynomial.C (1 - (1 - alpha r) ^ l.1) : AlphaCornerProbePoly d) •
        alphaCornerProbeW (d := d))

/-- Polynomial `Delta phi_{l,a,c}` at the all-`alpha` corner. -/
noncomputable def alphaCornerSlopeDiffPoly {L k d : Nat} (r : Nat)
    (theta : Params L k d) (l : Fin L) (a c : Fin k) : AlphaCornerProbePoly d :=
  alphaCornerProbeBilin (attentionMatrix theta l a - attentionMatrix theta l c)
    (alphaCornerWPoly r theta l) (alphaCornerVPoly r theta l)

/-- Semantic all-`alpha` same-layer slope difference. -/
noncomputable def alphaCornerSlopeDiff {L k d : Nat} (r : Nat)
    (theta : Params L k d) (l : Fin L) (a c : Fin k) (w v : Vec d) : Real :=
  matrixBilin (attentionMatrix theta l a - attentionMatrix theta l c)
    (((1 - alpha r) ^ l.1) •
      (alphaCornerCPrefix r theta l.1 (Nat.le_of_lt l.2) *ᵥ w))
    (alphaCornerCPrefix r theta l.1 (Nat.le_of_lt l.2) *ᵥ
      (v + (1 - (1 - alpha r) ^ l.1) • w))

@[simp] theorem eval_alphaCornerProbeBilin {d : Nat}
    (rho : AlphaCornerProbeVar d → Real) (A : Matrix (Fin d) (Fin d) Real)
    (w v : Fin d → AlphaCornerProbePoly d) :
    MvPolynomial.eval rho (alphaCornerProbeBilin A w v) =
      matrixBilin A (fun i ↦ MvPolynomial.eval rho (w i))
        (fun i ↦ MvPolynomial.eval rho (v i)) := by
  simp [alphaCornerProbeBilin, matrixBilin, realMatrixToAlphaCornerProbePoly,
    Matrix.mulVec, dotProduct]

@[simp] theorem eval_alphaCornerWPoly {L k d : Nat} (r : Nat)
    (theta : Params L k d) (l : Fin L) (w v : Vec d) :
    (fun i ↦ MvPolynomial.eval (alphaCornerProbeEval w v)
      (alphaCornerWPoly r theta l i)) =
      ((1 - alpha r) ^ l.1) •
        (alphaCornerCPrefix r theta l.1 (Nat.le_of_lt l.2) *ᵥ w) := by
  ext i
  simp [alphaCornerWPoly, alphaCornerProbeEval, alphaCornerProbeW,
    realMatrixToAlphaCornerProbePoly, Matrix.mulVec, dotProduct]

@[simp] theorem eval_alphaCornerVPoly {L k d : Nat} (r : Nat)
    (theta : Params L k d) (l : Fin L) (w v : Vec d) :
    (fun i ↦ MvPolynomial.eval (alphaCornerProbeEval w v)
      (alphaCornerVPoly r theta l i)) =
      alphaCornerCPrefix r theta l.1 (Nat.le_of_lt l.2) *ᵥ
        (v + (1 - (1 - alpha r) ^ l.1) • w) := by
  ext i
  simp [alphaCornerVPoly, alphaCornerProbeEval, alphaCornerProbeW,
    alphaCornerProbeV, realMatrixToAlphaCornerProbePoly, Matrix.mulVec, dotProduct]

@[simp] theorem eval_alphaCornerSlopeDiffPoly {L k d : Nat} (r : Nat)
    (theta : Params L k d) (l : Fin L) (a c : Fin k) (w v : Vec d) :
    MvPolynomial.eval (alphaCornerProbeEval w v)
        (alphaCornerSlopeDiffPoly r theta l a c) =
      alphaCornerSlopeDiff r theta l a c w v := by
  rw [alphaCornerSlopeDiffPoly, eval_alphaCornerProbeBilin,
    eval_alphaCornerWPoly, eval_alphaCornerVPoly]
  rfl

theorem alphaCornerProbePoly_ne_zero_iff_exists_eval_ne_zero {d : Nat}
    (p : AlphaCornerProbePoly d) :
    p ≠ 0 ↔ ∃ w v : Vec d, MvPolynomial.eval (alphaCornerProbeEval w v) p ≠ 0 := by
  constructor
  · intro hp
    by_contra h
    apply hp
    apply MvPolynomial.funext
    intro rho
    let w : Vec d := fun i ↦ rho (Sum.inl i)
    let v : Vec d := fun i ↦ rho (Sum.inr i)
    have heval : alphaCornerProbeEval w v = rho := by
      funext x
      cases x <;> rfl
    have hz : MvPolynomial.eval (alphaCornerProbeEval w v) p = 0 := by
      by_contra hne
      exact h ⟨w, v, hne⟩
    rw [← heval]
    exact hz
  · rintro ⟨w, v, hne⟩ rfl
    exact hne (by simp)

theorem alphaCornerCPrefix_det_ne_zero {L k d : Nat} (r : Nat)
    (theta : Params L k d) (htrans : ∀ l : Fin L, (collapseMatrix theta l).det ≠ 0) :
    ∀ (n : Nat) (hn : n ≤ L), (alphaCornerCPrefix r theta n hn).det ≠ 0
  | 0, _hn => by simp
  | n + 1, hn => by
      rw [alphaCornerCPrefix_succ, Matrix.det_mul]
      exact mul_ne_zero (htrans ⟨n, Nat.lt_of_succ_le hn⟩)
        (alphaCornerCPrefix_det_ne_zero r theta htrans n (Nat.le_of_succ_le hn))

theorem one_sub_alpha_pow_ne_zero (r n : Nat) (hr : 0 < r) :
    (1 - alpha r) ^ n ≠ 0 := by
  apply pow_ne_zero
  rw [alpha_eq_div r hr]
  have hden : (0 : Real) < (r : Real) + 1 := by positivity
  calc
    1 - (r : Real) / ((r : Real) + 1) = 1 / ((r : Real) + 1) := by
      field_simp [ne_of_gt hden]
      ring
    _ ≠ 0 := one_div_ne_zero (ne_of_gt hden)

private theorem matrixBilin_smul_left {d : Nat}
    (A : Matrix (Fin d) (Fin d) Real) (s : Real) (w v : Vec d) :
    matrixBilin A (s • w) v = s * matrixBilin A w v := by
  simp [matrixBilin, smul_dotProduct, smul_eq_mul]

private theorem exists_matrixBilin_ne_zero_of_matrix_ne_zero {d : Nat}
    {A : Matrix (Fin d) (Fin d) Real} (hA : A ≠ 0) :
    ∃ w v : Vec d, matrixBilin A w v ≠ 0 := by
  classical
  have hentry : ∃ i j : Fin d, A i j ≠ 0 := by
    by_contra hnone
    apply hA
    ext i j
    by_contra hij
    exact hnone ⟨i, j, hij⟩
  rcases hentry with ⟨i, j, hij⟩
  refine ⟨Pi.single i 1, Pi.single j 1, ?_⟩
  simpa [matrixBilin] using hij

/-- R2 and R3 force every same-layer all-`alpha` slope difference polynomial
to be nonzero. -/
theorem alphaCornerSlopeDiffPoly_ne_zero {L k d : Nat} (r : Nat)
    (theta : Params L k d) (hr : 0 < r)
    (hpair : PairwiseDistinctAttentions theta)
    (htrans : ∀ l : Fin L, (collapseMatrix theta l).det ≠ 0)
    (l : Fin L) {a c : Fin k} (hac : a ≠ c) :
    alphaCornerSlopeDiffPoly r theta l a c ≠ 0 := by
  let P := alphaCornerCPrefix r theta l.1 (Nat.le_of_lt l.2)
  let A := attentionMatrix theta l a - attentionMatrix theta l c
  have hA : A ≠ 0 := by
    exact sub_ne_zero.mpr (fun heq ↦ hac (hpair l heq))
  have hPdet : P.det ≠ 0 :=
    alphaCornerCPrefix_det_ne_zero r theta htrans l.1 (Nat.le_of_lt l.2)
  have hPsurj : Function.Surjective P.mulVec := by
    rw [Matrix.mulVec_surjective_iff_isUnit, Matrix.isUnit_iff_isUnit_det]
    exact hPdet.isUnit
  rcases exists_matrixBilin_ne_zero_of_matrix_ne_zero hA with ⟨x, y, hxy⟩
  rcases hPsurj x with ⟨w, hw⟩
  rcases hPsurj y with ⟨z, hz⟩
  let q : Real := 1 - (1 - alpha r) ^ l.1
  let v : Vec d := z - q • w
  have hv : P *ᵥ (v + q • w) = y := by
    have hvz : v + q • w = z := by
      simp [v]
    rw [hvz, hz]
  apply (alphaCornerProbePoly_ne_zero_iff_exists_eval_ne_zero
    (alphaCornerSlopeDiffPoly r theta l a c)).mpr
  refine ⟨w, v, ?_⟩
  rw [eval_alphaCornerSlopeDiffPoly]
  change matrixBilin A (((1 - alpha r) ^ l.1) • (P *ᵥ w))
    (P *ᵥ (v + q • w)) ≠ 0
  rw [hw, hv, matrixBilin_smul_left]
  exact mul_ne_zero (one_sub_alpha_pow_ne_zero r l.1 hr) hxy

namespace Regularity

variable {L k d : Nat} {theta : Params L k d}

/-- Corner separation is derived from regularity; it is not an additional field. -/
theorem alphaCornerSlopeDiffPoly_ne_zero (h : Regularity theta) (r : Nat)
    (hr : 0 < r) (l : Fin L) {a c : Fin k} (hac : a ≠ c) :
    NoSkip.alphaCornerSlopeDiffPoly r theta l a c ≠ 0 :=
  NoSkip.alphaCornerSlopeDiffPoly_ne_zero r theta hr h.attention_pairwise
    h.transmission l hac

/-- Semantic witness form used by sibling-avoidance arguments. -/
theorem exists_alphaCornerSlopeDiff_ne_zero (h : Regularity theta) (r : Nat)
    (hr : 0 < r) (l : Fin L) {a c : Fin k} (hac : a ≠ c) :
    ∃ w v : Vec d, alphaCornerSlopeDiff r theta l a c w v ≠ 0 := by
  have hp := h.alphaCornerSlopeDiffPoly_ne_zero r hr l hac
  rcases (alphaCornerProbePoly_ne_zero_iff_exists_eval_ne_zero
    (alphaCornerSlopeDiffPoly r theta l a c)).mp hp with ⟨w, v, hwv⟩
  exact ⟨w, v, by simpa using hwv⟩

end Regularity

/-! ## The zero-score causal averaging matrix -/

/-- The causal softmax matrix at zero logits, TeX `Gamma_0`. -/
noncomputable def gammaZero (r : Nat) :
    Matrix (Fin (seqLength r)) (Fin (seqLength r)) Real :=
  softmaxColC (0 : Matrix (Fin (seqLength r)) (Fin (seqLength r)) Real)

@[simp] theorem gammaZero_apply (r : Nat) (i j : Fin (seqLength r)) :
    gammaZero r i j = if i ≤ j then ((j.val + 1 : Nat) : Real)⁻¹ else 0 := by
  classical
  simp [gammaZero, Fin.card_Iic]

/-- `Gamma_0` is upper triangular in the natural token order. -/
theorem gammaZero_upperTriangular (r : Nat) :
    (gammaZero r).BlockTriangular id := by
  intro i j hji
  simp only [gammaZero_apply]
  simp [show ¬i ≤ j by simpa using hji]

@[simp] theorem gammaZero_diagonal (r : Nat) (i : Fin (seqLength r)) :
    gammaZero r i i = ((i.val + 1 : Nat) : Real)⁻¹ := by
  simp

theorem gammaZero_diagonal_ne_zero (r : Nat) (i : Fin (seqLength r)) :
    gammaZero r i i ≠ 0 := by
  rw [gammaZero_diagonal]
  exact inv_ne_zero (by positivity)

theorem gammaZero_det (r : Nat) :
    (gammaZero r).det = ∏ i : Fin (seqLength r), ((i.val + 1 : Nat) : Real)⁻¹ := by
  rw [Matrix.det_of_upperTriangular (gammaZero_upperTriangular r)]
  simp

/-- The zero-score averaging matrix is nonsingular. -/
theorem gammaZero_det_ne_zero (r : Nat) : (gammaZero r).det ≠ 0 := by
  rw [gammaZero_det]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => inv_ne_zero (by positivity)

/-! ## No-skip layer derivative at zero -/

/-- The no-skip derivative `H ↦ C_l H Gamma_0` at the zero input. -/
noncomputable def localDerivative {L k d : Nat} (r : Nat) (theta : Params L k d)
    (l : Fin L) (H : Matrix (Fin d) (Fin (seqLength r)) Real) :
    Matrix (Fin d) (Fin (seqLength r)) Real :=
  collapseMatrix theta l * H * gammaZero r

@[simp] theorem localDerivative_zero {L k d r : Nat} (theta : Params L k d)
    (l : Fin L) :
    localDerivative r theta l (0 : Matrix (Fin d) (Fin (seqLength r)) Real) = 0 := by
  simp [localDerivative]

theorem localDerivative_add {L k d r : Nat} (theta : Params L k d)
    (l : Fin L) (H K : Matrix (Fin d) (Fin (seqLength r)) Real) :
    localDerivative r theta l (H + K) =
      localDerivative r theta l H + localDerivative r theta l K := by
  simp [localDerivative, Matrix.mul_add, Matrix.add_mul]

theorem localDerivative_smul {L k d r : Nat} (theta : Params L k d)
    (l : Fin L) (c : Real) (H : Matrix (Fin d) (Fin (seqLength r)) Real) :
    localDerivative r theta l (c • H) = c • localDerivative r theta l H := by
  simp [localDerivative, Matrix.mul_smul, Matrix.smul_mul]

/-- Algebraic derivative as a real linear map. -/
noncomputable def localDerivativeLinearMap {L k d : Nat} (r : Nat)
    (theta : Params L k d) (l : Fin L) :
    Matrix (Fin d) (Fin (seqLength r)) Real →ₗ[Real]
      Matrix (Fin d) (Fin (seqLength r)) Real where
  toFun := localDerivative r theta l
  map_add' := localDerivative_add theta l
  map_smul' := localDerivative_smul theta l

@[simp] theorem localDerivativeLinearMap_apply {L k d r : Nat}
    (theta : Params L k d) (l : Fin L)
    (H : Matrix (Fin d) (Fin (seqLength r)) Real) :
    localDerivativeLinearMap r theta l H = localDerivative r theta l H :=
  rfl

/-- Continuous derivative map; continuity is automatic in finite dimensions. -/
noncomputable def localDerivativeContinuousLinearMap {L k d : Nat} (r : Nat)
    (theta : Params L k d) (l : Fin L) :
    Matrix (Fin d) (Fin (seqLength r)) Real →L[Real]
      Matrix (Fin d) (Fin (seqLength r)) Real :=
  LinearMap.toContinuousLinearMap (localDerivativeLinearMap r theta l)

@[simp] theorem localDerivativeContinuousLinearMap_apply {L k d r : Nat}
    (theta : Params L k d) (l : Fin L)
    (H : Matrix (Fin d) (Fin (seqLength r)) Real) :
    localDerivativeContinuousLinearMap r theta l H = localDerivative r theta l H := by
  simp [localDerivativeContinuousLinearMap]

/-- Head-sum form of the no-skip derivative. -/
theorem localDerivative_eq_head_sum {L k d r : Nat} (theta : Params L k d)
    (l : Fin L) (H : Matrix (Fin d) (Fin (seqLength r)) Real) :
    localDerivative r theta l H =
      ∑ a : Fin k, valueMatrix theta l a * H * gammaZero r := by
  simp [localDerivative, collapseMatrix, valueSum, Matrix.sum_mul]

/-- The causal column softmax is continuous as a matrix-valued map. -/
theorem continuous_softmaxColC {T : Nat} :
    Continuous (softmaxColC : Matrix (Fin T) (Fin T) Real →
      Matrix (Fin T) (Fin T) Real) := by
  refine continuous_matrix ?_
  intro i j
  by_cases hij : i ≤ j
  · have hnum :
        Continuous fun M : Matrix (Fin T) (Fin T) Real => Real.exp (M i j) :=
      Real.continuous_exp.comp ((continuous_id : Continuous
        (fun M : Matrix (Fin T) (Fin T) Real => M)).matrix_elem i j)
    have hden :
        Continuous fun M : Matrix (Fin T) (Fin T) Real =>
          ∑ i' ∈ Finset.Iic j, Real.exp (M i' j) := by
      apply continuous_finsetSum
      intro i' _hi'
      exact Real.continuous_exp.comp ((continuous_id : Continuous
        (fun M : Matrix (Fin T) (Fin T) Real => M)).matrix_elem i' j)
    have hden_ne :
        ∀ M : Matrix (Fin T) (Fin T) Real,
          (∑ i' ∈ Finset.Iic j, Real.exp (M i' j)) ≠ 0 := by
      intro M
      exact ne_of_gt (Finset.sum_pos
        (fun i' _hi' => Real.exp_pos (M i' j))
        ⟨j, Finset.mem_Iic.2 le_rfl⟩)
    simpa [softmaxColC, TransformerIdentifiability.NLayer.causalSoftmax, hij] using
      hnum.div hden hden_ne
  · simpa [softmaxColC, TransformerIdentifiability.NLayer.causalSoftmax, hij] using
      (continuous_const : Continuous fun _M : Matrix (Fin T) (Fin T) Real => (0 : Real))

/-- The quadratic attention-score map is continuous. -/
theorem continuous_quadraticScore {d T : Nat}
    (A : Matrix (Fin d) (Fin d) Real) :
    Continuous fun X : Matrix (Fin d) (Fin T) Real => Xᵀ * A * X := by
  exact Continuous.matrix_mul
    (Continuous.matrix_mul
      ((continuous_id : Continuous fun X : Matrix (Fin d) (Fin T) Real => X).matrix_transpose)
      continuous_const)
    continuous_id

/-- The softmax perturbation along a quadratic score tends to zero at zero input. -/
theorem softmax_quadraticScore_sub_gammaZero_tendsto_zero {d r : Nat}
    (A : Matrix (Fin d) (Fin d) Real) :
    Tendsto
      (fun X : Matrix (Fin d) (Fin (seqLength r)) Real =>
        softmaxColC (Xᵀ * A * X) - gammaZero r)
      (nhds 0) (nhds 0) := by
  have hsoft :
      Tendsto
        (fun X : Matrix (Fin d) (Fin (seqLength r)) Real =>
          softmaxColC (Xᵀ * A * X))
        (nhds 0) (nhds (gammaZero r)) := by
    have hcont :
        Continuous fun X : Matrix (Fin d) (Fin (seqLength r)) Real =>
          softmaxColC (Xᵀ * A * X) :=
      continuous_softmaxColC.comp (continuous_quadraticScore A)
    have hcont0 :
        ContinuousAt
          (fun X : Matrix (Fin d) (Fin (seqLength r)) Real =>
            softmaxColC (Xᵀ * A * X)) 0 :=
      hcont.continuousAt
    simpa [gammaZero] using hcont0.tendsto
  exact tendsto_sub_nhds_zero_iff.mpr hsoft

/-- If `G(X) → 0`, then `X G(X) = o(X)` in Frobenius norm. -/
theorem matrix_mul_tendsto_zero_right_isLittleO {d T : Nat}
    {G : Matrix (Fin d) (Fin T) Real → Matrix (Fin T) (Fin T) Real}
    (hG : Tendsto G (nhds (0 : Matrix (Fin d) (Fin T) Real))
      (nhds (0 : Matrix (Fin T) (Fin T) Real))) :
    (fun X : Matrix (Fin d) (Fin T) Real => X * G X)
      =o[nhds (0 : Matrix (Fin d) (Fin T) Real)]
        fun X : Matrix (Fin d) (Fin T) Real => X := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hnorm :
      Tendsto (fun X : Matrix (Fin d) (Fin T) Real => ‖G X‖)
        (nhds (0 : Matrix (Fin d) (Fin T) Real)) (nhds (0 : Real)) := by
    simpa using hG.norm
  have hsmall : {y : Real | y < c} ∈ nhds (0 : Real) := Iio_mem_nhds hc
  filter_upwards [hnorm hsmall] with X hX
  calc
    ‖X * G X‖ ≤ ‖X‖ * ‖G X‖ := Matrix.frobenius_norm_mul X (G X)
    _ ≤ ‖X‖ * c := mul_le_mul_of_nonneg_left (le_of_lt hX) (norm_nonneg X)
    _ = c * ‖X‖ := mul_comm _ _

/-- Fixed left multiplication preserves the quadratic softmax `o(X)` estimate. -/
theorem matrix_const_mul_mul_tendsto_zero_right_isLittleO {d T : Nat}
    (V : Matrix (Fin d) (Fin d) Real)
    {G : Matrix (Fin d) (Fin T) Real → Matrix (Fin T) (Fin T) Real}
    (hG : Tendsto G (nhds (0 : Matrix (Fin d) (Fin T) Real))
      (nhds (0 : Matrix (Fin T) (Fin T) Real))) :
    (fun X : Matrix (Fin d) (Fin T) Real => V * X * G X)
      =o[nhds (0 : Matrix (Fin d) (Fin T) Real)]
        fun X : Matrix (Fin d) (Fin T) Real => X := by
  have hleft :
      (fun X : Matrix (Fin d) (Fin T) Real => V * (X * G X))
        =O[nhds (0 : Matrix (Fin d) (Fin T) Real)]
          fun X : Matrix (Fin d) (Fin T) Real => X * G X := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨‖V‖, Eventually.of_forall ?_⟩
    intro X
    exact Matrix.frobenius_norm_mul V (X * G X)
  have hprod := matrix_mul_tendsto_zero_right_isLittleO (d := d) (T := T) hG
  simpa [Matrix.mul_assoc] using hleft.trans_isLittleO hprod

/-- Exact no-skip remainder after subtracting `C_l X Gamma_0`. -/
theorem layer_sub_localDerivative_eq_softmax_remainder {L k d r : Nat}
    (theta : Params L k d) (l : Fin L)
    (X : Matrix (Fin d) (Fin (seqLength r)) Real) :
    layer theta l X - localDerivative r theta l X =
      ∑ a : Fin k, valueMatrix theta l a * X *
        (softmaxColC (Xᵀ * attentionMatrix theta l a * X) - gammaZero r) := by
  rw [layer, localDerivative_eq_head_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [← Matrix.mul_sub]

/-- One head's no-skip softmax remainder is `o(X)` at zero. -/
theorem one_head_softmax_remainder_isLittleO {L k d r : Nat}
    (theta : Params L k d) (l : Fin L) (a : Fin k) :
    (fun X : Matrix (Fin d) (Fin (seqLength r)) Real =>
      valueMatrix theta l a * X *
        (softmaxColC (Xᵀ * attentionMatrix theta l a * X) - gammaZero r))
      =o[nhds (0 : Matrix (Fin d) (Fin (seqLength r)) Real)]
        fun X : Matrix (Fin d) (Fin (seqLength r)) Real => X := by
  exact matrix_const_mul_mul_tendsto_zero_right_isLittleO
    (valueMatrix theta l a)
    (softmax_quadraticScore_sub_gammaZero_tendsto_zero
      (attentionMatrix theta l a))

/-- The finite sum of headwise softmax remainders is `o(X)`. -/
theorem softmax_remainder_sum_isLittleO {L k d r : Nat}
    (theta : Params L k d) (l : Fin L) :
    (fun X : Matrix (Fin d) (Fin (seqLength r)) Real =>
      ∑ a : Fin k, valueMatrix theta l a * X *
        (softmaxColC (Xᵀ * attentionMatrix theta l a * X) - gammaZero r))
      =o[nhds (0 : Matrix (Fin d) (Fin (seqLength r)) Real)]
        fun X : Matrix (Fin d) (Fin (seqLength r)) Real => X := by
  simpa using
    (Asymptotics.IsLittleO.sum (s := Finset.univ)
      (A := fun a : Fin k => fun X : Matrix (Fin d) (Fin (seqLength r)) Real =>
        valueMatrix theta l a * X *
          (softmaxColC (Xᵀ * attentionMatrix theta l a * X) - gammaZero r))
      (g' := fun X : Matrix (Fin d) (Fin (seqLength r)) Real => X)
      (l := nhds (0 : Matrix (Fin d) (Fin (seqLength r)) Real))
      (fun a _ha => one_head_softmax_remainder_isLittleO theta l a))

/-- The complete no-skip layer remainder is little-o of its input. -/
theorem layer_sub_localDerivative_isLittleO_at_zero {L k d r : Nat}
    (theta : Params L k d) (l : Fin L) :
    (fun X : Matrix (Fin d) (Fin (seqLength r)) Real =>
      layer theta l X - localDerivative r theta l X)
      =o[nhds (0 : Matrix (Fin d) (Fin (seqLength r)) Real)]
        fun X : Matrix (Fin d) (Fin (seqLength r)) Real => X :=
  (softmax_remainder_sum_isLittleO theta l).congr_left
    (fun X => (layer_sub_localDerivative_eq_softmax_remainder theta l X).symm)

/-- The no-skip layer has derivative `H ↦ C_l H Gamma_0` at zero. -/
theorem layer_hasFDerivAt_localDerivative {L k d r : Nat}
    (theta : Params L k d) (l : Fin L) :
    HasFDerivAt
      (fun X : Matrix (Fin d) (Fin (seqLength r)) Real => layer theta l X)
      (localDerivativeContinuousLinearMap r theta l) 0 := by
  apply HasFDerivAt.of_isLittleO
  simpa using layer_sub_localDerivative_isLittleO_at_zero (r := r) theta l

/-- Explicit inverse of `H ↦ C_l H Gamma_0`, using the two nonsingular factors. -/
noncomputable def localDerivativeLinearEquiv {L k d r : Nat}
    (theta : Params L k d) (l : Fin L)
    (hC : (collapseMatrix theta l).det ≠ 0) :
    Matrix (Fin d) (Fin (seqLength r)) Real ≃ₗ[Real]
      Matrix (Fin d) (Fin (seqLength r)) Real where
  toLinearMap := localDerivativeLinearMap r theta l
  invFun := fun Y => (collapseMatrix theta l)⁻¹ * Y * (gammaZero r)⁻¹
  left_inv H := by
    have hCu : IsUnit (collapseMatrix theta l).det := hC.isUnit
    have hGu : IsUnit (gammaZero r).det := (gammaZero_det_ne_zero r).isUnit
    change (collapseMatrix theta l)⁻¹ *
      (collapseMatrix theta l * H * gammaZero r) * (gammaZero r)⁻¹ = H
    calc
      (collapseMatrix theta l)⁻¹ *
          (collapseMatrix theta l * H * gammaZero r) * (gammaZero r)⁻¹ =
        ((collapseMatrix theta l)⁻¹ * collapseMatrix theta l) * H *
          (gammaZero r * (gammaZero r)⁻¹) := by
            simp only [Matrix.mul_assoc]
      _ = H := by
        rw [Matrix.nonsing_inv_mul _ hCu, Matrix.mul_nonsing_inv _ hGu]
        simp
  right_inv Y := by
    have hCu : IsUnit (collapseMatrix theta l).det := hC.isUnit
    have hGu : IsUnit (gammaZero r).det := (gammaZero_det_ne_zero r).isUnit
    change collapseMatrix theta l *
      ((collapseMatrix theta l)⁻¹ * Y * (gammaZero r)⁻¹) * gammaZero r = Y
    calc
      collapseMatrix theta l *
          ((collapseMatrix theta l)⁻¹ * Y * (gammaZero r)⁻¹) * gammaZero r =
        (collapseMatrix theta l * (collapseMatrix theta l)⁻¹) * Y *
          ((gammaZero r)⁻¹ * gammaZero r) := by
            simp only [Matrix.mul_assoc]
      _ = Y := by
        rw [Matrix.mul_nonsing_inv _ hCu, Matrix.nonsing_inv_mul _ hGu]
        simp

@[simp] theorem localDerivativeLinearEquiv_apply {L k d r : Nat}
    (theta : Params L k d) (l : Fin L)
    (hC : (collapseMatrix theta l).det ≠ 0)
    (H : Matrix (Fin d) (Fin (seqLength r)) Real) :
    localDerivativeLinearEquiv (r := r) theta l hC H = localDerivative r theta l H :=
  rfl

/-- The invertible derivative as a continuous linear equivalence. -/
noncomputable def localDerivativeContinuousLinearEquiv {L k d r : Nat}
    (theta : Params L k d) (l : Fin L)
    (hC : (collapseMatrix theta l).det ≠ 0) :
    Matrix (Fin d) (Fin (seqLength r)) Real ≃L[Real]
      Matrix (Fin d) (Fin (seqLength r)) Real :=
  (localDerivativeLinearEquiv (r := r) theta l hC).toContinuousLinearEquiv

@[simp] theorem localDerivativeContinuousLinearEquiv_apply {L k d r : Nat}
    (theta : Params L k d) (l : Fin L)
    (hC : (collapseMatrix theta l).det ≠ 0)
    (H : Matrix (Fin d) (Fin (seqLength r)) Real) :
    localDerivativeContinuousLinearEquiv (r := r) theta l hC H =
      localDerivative r theta l H := by
  simp [localDerivativeContinuousLinearEquiv]

section LayerAnalyticity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] {U : Set E}

private theorem regularity_analyticOnNhd_matrix_coord {n m : Nat}
    {F : E → Matrix (Fin n) (Fin m) Real}
    (hF : AnalyticOnNhd Real F U) (i : Fin n) (j : Fin m) :
    AnalyticOnNhd Real (fun x : E => F x i j) U := by
  let Prow : Matrix (Fin n) (Fin m) Real →L[Real] (Fin m → Real) :=
    ContinuousLinearMap.proj i
  let Pcoord : (Fin m → Real) →L[Real] Real := ContinuousLinearMap.proj j
  simpa [Prow, Pcoord, Function.comp] using
    (Pcoord.comp Prow).comp_analyticOnNhd hF

private theorem regularity_analyticOnNhd_matrix_of_coords {n m : Nat}
    {F : E → Matrix (Fin n) (Fin m) Real}
    (hF : ∀ i : Fin n, ∀ j : Fin m,
      AnalyticOnNhd Real (fun x : E => F x i j) U) :
    AnalyticOnNhd Real F U := by
  let Mof : (Fin n → Fin m → Real) →L[Real] Matrix (Fin n) (Fin m) Real :=
    LinearMap.toContinuousLinearMap
      ((Matrix.ofLinearEquiv Real : (Fin n → Fin m → Real) ≃ₗ[Real]
        Matrix (Fin n) (Fin m) Real).toLinearMap)
  have hPi :
      AnalyticOnNhd Real (fun x : E => fun i : Fin n => fun j : Fin m => F x i j) U := by
    apply AnalyticOnNhd.pi
    intro i
    apply AnalyticOnNhd.pi
    intro j
    exact hF i j
  simpa [Mof, Function.comp] using Mof.comp_analyticOnNhd hPi

private theorem regularity_analyticOnNhd_matrix_transpose_coord {n m : Nat}
    {F : E → Matrix (Fin n) (Fin m) Real}
    (hF : ∀ i : Fin n, ∀ j : Fin m,
      AnalyticOnNhd Real (fun x : E => F x i j) U)
    (i : Fin m) (j : Fin n) :
    AnalyticOnNhd Real (fun x : E => (F x)ᵀ i j) U := by
  simpa [Matrix.transpose_apply] using hF j i

private theorem regularity_analyticOnNhd_matrix_mul_coord {n m p : Nat}
    {F : E → Matrix (Fin n) (Fin m) Real}
    {G : E → Matrix (Fin m) (Fin p) Real}
    (hF : ∀ i : Fin n, ∀ j : Fin m,
      AnalyticOnNhd Real (fun x : E => F x i j) U)
    (hG : ∀ i : Fin m, ∀ j : Fin p,
      AnalyticOnNhd Real (fun x : E => G x i j) U)
    (i : Fin n) (q : Fin p) :
    AnalyticOnNhd Real (fun x : E => (F x * G x) i q) U := by
  simp only [Matrix.mul_apply]
  apply Finset.analyticOnNhd_fun_sum
  intro j _hj
  exact (hF i j).mul (hG j q)

private theorem regularity_softmaxColC_coord_analyticOnNhd {T : Nat}
    {F : E → Matrix (Fin T) (Fin T) Real}
    (hF : ∀ i : Fin T, ∀ j : Fin T,
      AnalyticOnNhd Real (fun x : E => F x i j) U)
    (i j : Fin T) :
    AnalyticOnNhd Real (fun x : E => softmaxColC (F x) i j) U := by
  by_cases hij : i ≤ j
  · have hnum : AnalyticOnNhd Real (fun x : E => Real.exp (F x i j)) U :=
      (hF i j).rexp
    have hden :
        AnalyticOnNhd Real
          (fun x : E => ∑ i' ∈ Finset.Iic j, Real.exp (F x i' j)) U := by
      apply Finset.analyticOnNhd_fun_sum
      intro i' _hi'
      exact (hF i' j).rexp
    have hden_ne :
        ∀ x ∈ U, (∑ i' ∈ Finset.Iic j, Real.exp (F x i' j)) ≠ 0 := by
      intro x _hx
      exact ne_of_gt (Finset.sum_pos
        (fun i' _hi' => Real.exp_pos (F x i' j))
        ⟨j, Finset.mem_Iic.2 le_rfl⟩)
    simpa [softmaxColC, TransformerIdentifiability.NLayer.causalSoftmax, hij] using
      hnum.div hden hden_ne
  · simpa [softmaxColC, TransformerIdentifiability.NLayer.causalSoftmax, hij] using
      (analyticOnNhd_const (𝕜 := Real) (v := (0 : Real)) (s := U))

private theorem regularity_layer_coord_analyticOnNhd_id {L k d r : Nat}
    (theta : Params L k d) (l : Fin L) (i : Fin d) (j : Fin (seqLength r)) :
    AnalyticOnNhd Real
      (fun X : Matrix (Fin d) (Fin (seqLength r)) Real => layer theta l X i j)
      Set.univ := by
  have hId : AnalyticOnNhd Real
      (fun X : Matrix (Fin d) (Fin (seqLength r)) Real => X) Set.univ :=
    (ContinuousLinearMap.id Real
      (Matrix (Fin d) (Fin (seqLength r)) Real)).analyticOnNhd Set.univ
  have hX : ∀ i : Fin d, ∀ j : Fin (seqLength r),
      AnalyticOnNhd Real
        (fun X : Matrix (Fin d) (Fin (seqLength r)) Real => X i j) Set.univ := by
    intro i' j'
    exact regularity_analyticOnNhd_matrix_coord hId i' j'
  have hsum :
      AnalyticOnNhd Real
        (fun X : Matrix (Fin d) (Fin (seqLength r)) Real =>
          (∑ a : Fin k, valueMatrix theta l a * X *
            softmaxColC (Xᵀ * attentionMatrix theta l a * X)) i j) Set.univ := by
    simpa [Matrix.sum_apply] using
      (Finset.analyticOnNhd_fun_sum (N := Finset.univ) (s := Set.univ)
        (f := fun a : Fin k => fun X : Matrix (Fin d) (Fin (seqLength r)) Real =>
          (valueMatrix theta l a * X *
            softmaxColC (Xᵀ * attentionMatrix theta l a * X)) i j)
        (by
          intro a _ha
          have hV : ∀ i' : Fin d, ∀ j' : Fin d,
              AnalyticOnNhd Real
                (fun _X : Matrix (Fin d) (Fin (seqLength r)) Real =>
                  valueMatrix theta l a i' j') Set.univ := by
            intro i' j'
            exact analyticOnNhd_const (𝕜 := Real)
              (v := valueMatrix theta l a i' j') (s := Set.univ)
          have hA : ∀ i' : Fin d, ∀ j' : Fin d,
              AnalyticOnNhd Real
                (fun _X : Matrix (Fin d) (Fin (seqLength r)) Real =>
                  attentionMatrix theta l a i' j') Set.univ := by
            intro i' j'
            exact analyticOnNhd_const (𝕜 := Real)
              (v := attentionMatrix theta l a i' j') (s := Set.univ)
          have hXT : ∀ i' : Fin (seqLength r), ∀ j' : Fin d,
              AnalyticOnNhd Real
                (fun X : Matrix (Fin d) (Fin (seqLength r)) Real => Xᵀ i' j') Set.univ := by
            intro i' j'
            exact regularity_analyticOnNhd_matrix_transpose_coord hX i' j'
          have hleft : ∀ i' : Fin (seqLength r), ∀ j' : Fin d,
              AnalyticOnNhd Real
                (fun X : Matrix (Fin d) (Fin (seqLength r)) Real =>
                  (Xᵀ * attentionMatrix theta l a) i' j') Set.univ := by
            intro i' j'
            exact regularity_analyticOnNhd_matrix_mul_coord hXT hA i' j'
          have hscore : ∀ i' : Fin (seqLength r), ∀ j' : Fin (seqLength r),
              AnalyticOnNhd Real
                (fun X : Matrix (Fin d) (Fin (seqLength r)) Real =>
                  (Xᵀ * attentionMatrix theta l a * X) i' j') Set.univ := by
            intro i' j'
            exact regularity_analyticOnNhd_matrix_mul_coord hleft hX i' j'
          have hsoft : ∀ i' : Fin (seqLength r), ∀ j' : Fin (seqLength r),
              AnalyticOnNhd Real
                (fun X : Matrix (Fin d) (Fin (seqLength r)) Real =>
                  softmaxColC (Xᵀ * attentionMatrix theta l a * X) i' j')
                Set.univ := by
            intro i' j'
            exact regularity_softmaxColC_coord_analyticOnNhd hscore i' j'
          have hVX : ∀ i' : Fin d, ∀ j' : Fin (seqLength r),
              AnalyticOnNhd Real
                (fun X : Matrix (Fin d) (Fin (seqLength r)) Real =>
                  (valueMatrix theta l a * X) i' j') Set.univ := by
            intro i' j'
            exact regularity_analyticOnNhd_matrix_mul_coord hV hX i' j'
          exact regularity_analyticOnNhd_matrix_mul_coord hVX hsoft i j))
  simpa [layer, Matrix.sum_apply] using hsum

/-- Every no-skip layer is analytic at zero. -/
theorem layer_analyticAt {L k d r : Nat} (theta : Params L k d) (l : Fin L) :
    AnalyticAt Real
      (fun X : Matrix (Fin d) (Fin (seqLength r)) Real => layer theta l X) 0 := by
  have hOn : AnalyticOnNhd Real
      (fun X : Matrix (Fin d) (Fin (seqLength r)) Real => layer theta l X)
      Set.univ := by
    apply regularity_analyticOnNhd_matrix_of_coords
    intro i j
    exact regularity_layer_coord_analyticOnNhd_id theta l i j
  exact hOn 0 (Set.mem_univ _)

end LayerAnalyticity

/-- Analyticity upgrades the derivative at zero to a strict derivative. -/
theorem layer_hasStrictFDerivAt_localDerivative {L k d r : Nat}
    (theta : Params L k d) (l : Fin L) :
    HasStrictFDerivAt
      (fun X : Matrix (Fin d) (Fin (seqLength r)) Real => layer theta l X)
      (localDerivativeContinuousLinearMap r theta l) 0 := by
  have hstrict := (layer_analyticAt (r := r) theta l).hasStrictFDerivAt
  exact hstrict.congr_fderiv (layer_hasFDerivAt_localDerivative (r := r) theta l).fderiv

/-- Strict derivative expressed through the transmission-built equivalence. -/
theorem layer_hasStrictFDerivAt_localDerivativeEquiv {L k d r : Nat}
    (theta : Params L k d) (l : Fin L)
    (hC : (collapseMatrix theta l).det ≠ 0) :
    HasStrictFDerivAt
      (fun X : Matrix (Fin d) (Fin (seqLength r)) Real => layer theta l X)
      (↑(localDerivativeContinuousLinearEquiv (r := r) theta l hC) :
        Matrix (Fin d) (Fin (seqLength r)) Real →L[Real]
          Matrix (Fin d) (Fin (seqLength r)) Real) 0 := by
  simpa only [localDerivativeContinuousLinearEquiv_apply] using
    layer_hasStrictFDerivAt_localDerivative (r := r) theta l

/-- Open image and explicit local-preimage data supplied by the inverse function theorem. -/
structure LocalOpenLayerImage {L k d : Nat} (r : Nat) (theta : Params L k d)
    (l : Fin L) where
  domain : Set (Matrix (Fin d) (Fin (seqLength r)) Real)
  imageSet : Set (Matrix (Fin d) (Fin (seqLength r)) Real)
  localPreimage : Matrix (Fin d) (Fin (seqLength r)) Real →
    Matrix (Fin d) (Fin (seqLength r)) Real
  domain_open : IsOpen domain
  zero_mem_domain : (0 : Matrix (Fin d) (Fin (seqLength r)) Real) ∈ domain
  image_open : IsOpen imageSet
  zero_mem_image : (0 : Matrix (Fin d) (Fin (seqLength r)) Real) ∈ imageSet
  preimage_mem_domain : ∀ Y ∈ imageSet, localPreimage Y ∈ domain
  right_inverse : ∀ Y ∈ imageSet, layer theta l (localPreimage Y) = Y

namespace LocalOpenLayerImage

theorem image_nonempty {L k d r : Nat} {theta : Params L k d} {l : Fin L}
    (D : LocalOpenLayerImage r theta l) : D.imageSet.Nonempty :=
  ⟨0, D.zero_mem_image⟩

theorem image_subset_layer_image {L k d r : Nat} {theta : Params L k d} {l : Fin L}
    (D : LocalOpenLayerImage r theta l) :
    D.imageSet ⊆
      (fun X : Matrix (Fin d) (Fin (seqLength r)) Real => layer theta l X) '' D.domain := by
  intro Y hY
  exact ⟨D.localPreimage Y, D.preimage_mem_domain Y hY, D.right_inverse Y hY⟩

end LocalOpenLayerImage

/-- Inverse-function-theorem core: an invertible strict derivative gives an
open neighborhood of zero with explicit preimages under the layer. -/
theorem localOpenLayerImage_of_hasStrictFDerivAt_equiv {L k d r : Nat}
    {theta : Params L k d} {l : Fin L}
    (E : Matrix (Fin d) (Fin (seqLength r)) Real ≃L[Real]
      Matrix (Fin d) (Fin (seqLength r)) Real)
    (hderiv : HasStrictFDerivAt
      (fun X : Matrix (Fin d) (Fin (seqLength r)) Real => layer theta l X)
      (↑E : Matrix (Fin d) (Fin (seqLength r)) Real →L[Real]
        Matrix (Fin d) (Fin (seqLength r)) Real) 0) :
    Nonempty (LocalOpenLayerImage r theta l) := by
  let f : Matrix (Fin d) (Fin (seqLength r)) Real →
      Matrix (Fin d) (Fin (seqLength r)) Real := fun X => layer theta l X
  let inv : Matrix (Fin d) (Fin (seqLength r)) Real →
      Matrix (Fin d) (Fin (seqLength r)) Real :=
    hderiv.localInverse f E 0
  have hright : ∀ᶠ Y in nhds (f 0), f (inv Y) = Y := by
    simpa [f, inv] using hderiv.eventually_right_inverse
  rw [Filter.eventually_iff, mem_nhds_iff] at hright
  obtain ⟨Omega, hOmega_subset, hOmega_open, hOmega_mem⟩ := hright
  have hzero : (0 : Matrix (Fin d) (Fin (seqLength r)) Real) ∈ Omega := by
    simpa [f] using hOmega_mem
  refine ⟨{
    domain := Set.univ
    imageSet := Omega
    localPreimage := inv
    domain_open := isOpen_univ
    zero_mem_domain := Set.mem_univ _
    image_open := hOmega_open
    zero_mem_image := hzero
    preimage_mem_domain := fun _Y _hY => Set.mem_univ _
    right_inverse := ?_
  }⟩
  intro Y hY
  exact hOmega_subset hY

/-- Transmission alone supplies local openness of each no-skip layer. -/
theorem localOpenLayerImage_of_transmission {L k d r : Nat}
    (theta : Params L k d) (l : Fin L)
    (hC : (collapseMatrix theta l).det ≠ 0) :
    Nonempty (LocalOpenLayerImage r theta l) :=
  localOpenLayerImage_of_hasStrictFDerivAt_equiv
    (localDerivativeContinuousLinearEquiv (r := r) theta l hC)
    (layer_hasStrictFDerivAt_localDerivativeEquiv (r := r) theta l hC)

namespace Regularity

variable {L k d : Nat} {theta : Params L k d}

/-- Every regular no-skip layer has a nonempty open set of locally attained outputs. -/
theorem localOpenLayerImage (h : Regularity theta) (r : Nat) (l : Fin L) :
    Nonempty (LocalOpenLayerImage r theta l) :=
  localOpenLayerImage_of_transmission theta l (h.transmission l)

end Regularity

/-! ## Local-openness determinant is exactly transmission -/

/-- Determinant of the flattened no-skip derivative in the standard matrix basis. -/
noncomputable def localOpennessDet {L k d r : Nat} (theta : Params L k d)
    (l : Fin L) : Real :=
  (LinearMap.toMatrix
    (Matrix.stdBasis Real (Fin d) (Fin (seqLength r)))
    (Matrix.stdBasis Real (Fin d) (Fin (seqLength r)))
    (localDerivativeLinearMap r theta l)).det

/-- Minimal semantic local-openness predicate for one layer. -/
def LocalOpennessAt {L k d r : Nat} (theta : Params L k d) (l : Fin L) : Prop :=
  localOpennessDet (r := r) theta l ≠ 0

/-- Layerwise local openness, deliberately defined rather than stored in `Regularity`. -/
def LocalOpenness {L k d : Nat} (r : Nat) (theta : Params L k d) : Prop :=
  ∀ l : Fin L, LocalOpennessAt (r := r) theta l

/-- Transmission makes the flattened derivative determinant nonzero. -/
theorem localOpennessAt_of_transmission {L k d r : Nat} (theta : Params L k d)
    (l : Fin L) (hC : (collapseMatrix theta l).det ≠ 0) :
    LocalOpennessAt (r := r) theta l := by
  let b := Matrix.stdBasis Real (Fin d) (Fin (seqLength r))
  have hu := (localDerivativeLinearEquiv (r := r) theta l hC).isUnit_det b b
  change IsUnit (LinearMap.toMatrix b b (localDerivativeLinearMap r theta l)).det at hu
  exact hu.ne_zero

/-- A nonzero flattened derivative determinant forces transmission. -/
theorem transmission_of_localOpennessAt {L k d r : Nat} (theta : Params L k d)
    (l : Fin L) (hopen : LocalOpennessAt (r := r) theta l) :
    (collapseMatrix theta l).det ≠ 0 := by
  let b := Matrix.stdBasis Real (Fin d) (Fin (seqLength r))
  have hu : IsUnit (LinearMap.toMatrix b b (localDerivativeLinearMap r theta l)).det :=
    hopen.isUnit
  let E : Matrix (Fin d) (Fin (seqLength r)) Real ≃ₗ[Real]
      Matrix (Fin d) (Fin (seqLength r)) Real :=
    LinearEquiv.ofIsUnitDet (f := localDerivativeLinearMap r theta l)
      (v := b) (v' := b) hu
  have hderiv_inj : Function.Injective (localDerivative r theta l) := by
    intro H K hHK
    exact E.injective hHK
  have hCinj : Function.Injective (collapseMatrix theta l).mulVec := by
    intro w z hwz
    let Hw : Matrix (Fin d) (Fin (seqLength r)) Real := fun i _j => w i
    let Hz : Matrix (Fin d) (Fin (seqLength r)) Real := fun i _j => z i
    have hCH : collapseMatrix theta l * Hw = collapseMatrix theta l * Hz := by
      ext i j
      have hi := congr_fun hwz i
      simpa [Hw, Hz, Matrix.mul_apply, Matrix.mulVec, dotProduct] using hi
    have hLH : localDerivative r theta l Hw = localDerivative r theta l Hz := by
      simp only [localDerivative]
      rw [hCH]
    have hH := hderiv_inj hLH
    funext i
    have hij := congr_fun (congr_fun hH i) (Fin.last r)
    simpa [Hw, Hz] using hij
  have hunit : IsUnit (collapseMatrix theta l) :=
    Matrix.mulVec_injective_iff_isUnit.mp hCinj
  exact ((Matrix.isUnit_iff_isUnit_det (A := collapseMatrix theta l)).mp hunit).ne_zero

/-- TeX local openness is equivalent to transmission because `Gamma_0` is nonsingular. -/
theorem localOpennessAt_iff_transmission {L k d r : Nat} (theta : Params L k d)
    (l : Fin L) :
    LocalOpennessAt (r := r) theta l ↔ (collapseMatrix theta l).det ≠ 0 :=
  ⟨transmission_of_localOpennessAt theta l, localOpennessAt_of_transmission theta l⟩

theorem localOpenness_iff_transmission {L k d r : Nat} (theta : Params L k d) :
    LocalOpenness r theta ↔ ∀ l : Fin L, (collapseMatrix theta l).det ≠ 0 := by
  simp only [LocalOpenness, localOpennessAt_iff_transmission]

/-- The same equivalence connected directly to the NS047 transmission polynomial. -/
theorem localOpennessAt_iff_transmissionPolynomial {L k d r : Nat}
    (theta : Params L k d) (l : Fin L) :
    LocalOpennessAt (r := r) theta l ↔
      MvPolynomial.eval (nsParamFlat theta)
        (structuralMatrixPolyNS (k := k) (d := d)
          (.transmission l : StructuralMatrixIndexNS L)) ≠ 0 := by
  rw [localOpennessAt_iff_transmission, eval_structuralMatrixPolyNS]

namespace Regularity

variable {L k d : Nat} {theta : Params L k d}

theorem localOpenness (h : Regularity theta) (r : Nat) : LocalOpenness r theta :=
  (localOpenness_iff_transmission theta).mpr h.transmission

end Regularity

/-! ## Target regularity API -/

/-- Compact target-only regularity interface for Step 1 and the polynomial cover.

Every field is a consequence of `Regularity theta`; in particular, local openness
and corner separation are exported conclusions rather than additional genericity
assumptions.  The sole parameter is the target parameter `theta`, so this package
cannot introduce source-side regularity into downstream theorem signatures.
-/
structure TargetRegularityPackage {L k d : Nat} (theta : Params L k d) : Prop where
  regularity : Regularity theta
  polynomialClauses :
    BasicMatrixClausesNS theta ∧ StructuralMatrixClausesNS theta
  localOpenness : ∀ r : Nat, LocalOpenness r theta
  localOpenLayerImage :
    ∀ (r : Nat) (l : Fin L), Nonempty (LocalOpenLayerImage r theta l)
  cornerSeparationPolynomial :
    ∀ (r : Nat), 0 < r → ∀ (l : Fin L) {a c : Fin k}, a ≠ c →
      alphaCornerSlopeDiffPoly r theta l a c ≠ 0
  cornerSeparationWitness :
    ∀ (r : Nat), 0 < r → ∀ (l : Fin L) {a c : Fin k}, a ≠ c →
      ∃ w v : Vec d, alphaCornerSlopeDiff r theta l a c w v ≠ 0

/-- Semantic target regularity supplies the complete compact target interface. -/
theorem targetRegularityPackage_of_regular {L k d : Nat}
    {theta : Params L k d} (h : Regularity theta) :
    TargetRegularityPackage theta where
  regularity := h
  polynomialClauses := (regularity_iff_polynomial_clauses theta).mp h
  localOpenness := h.localOpenness
  localOpenLayerImage := h.localOpenLayerImage
  cornerSeparationPolynomial := h.alphaCornerSlopeDiffPoly_ne_zero
  cornerSeparationWitness := h.exists_alphaCornerSlopeDiff_ne_zero

/-- The compact package adds no hypothesis beyond target regularity. -/
theorem targetRegularityPackage_iff {L k d : Nat} (theta : Params L k d) :
    TargetRegularityPackage theta ↔ Regularity theta :=
  ⟨TargetRegularityPackage.regularity, targetRegularityPackage_of_regular⟩

end TransformerIdentifiability.NLayer.NoSkip
