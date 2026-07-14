import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Genericity.Recursive
import Mathlib.Analysis.InnerProductSpace.GramMatrix

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.NoSkip

/-!
# Stability under the first-interface input gauge

We use the input action already defined by the cascade certificate.  It sends
the first layer to `(V G, Gᵀ A G)` and leaves every deeper layer unchanged.
-/

noncomputable section

/-! ## Structural and regularity clauses -/

@[simp] theorem collapseMatrix_cascadeInputGaugeAction_zero {m k d : Nat}
    (G : GaugeMatrix d) (theta : Params (m + 1) k d) :
    collapseMatrix (cascadeInputGaugeAction G theta) 0 =
      collapseMatrix theta 0 * G.matrix := by
  rw [collapseMatrix_eq_valueSum, collapseMatrix_eq_valueSum]
  simp only [valueSum, valueMatrix_cascadeInputGaugeAction_zero]
  rw [Matrix.sum_mul]

@[simp] theorem collapseMatrix_cascadeInputGaugeAction_succ {m k d : Nat}
    (G : GaugeMatrix d) (theta : Params (m + 1) k d)
    (l : Fin m) :
    collapseMatrix (cascadeInputGaugeAction G theta) l.succ =
      collapseMatrix theta l.succ := by
  rw [collapseMatrix_eq_valueSum, collapseMatrix_eq_valueSum]
  simp only [valueSum, valueMatrix_cascadeInputGaugeAction_succ]

theorem jointSurjective_cascadeInputGaugeAction_zero_iff {m k d : Nat}
    (G : GaugeMatrix d) (theta : Params (m + 1) k d) :
    JointSurjective (cascadeInputGaugeAction G theta) 0 ↔
      JointSurjective theta 0 := by
  constructor
  · intro h y
    rcases h y with ⟨x, hx⟩
    let x' : Fin k × Fin d → Real := fun aj =>
      G.matrix.mulVec (fun q => x (aj.1, q)) aj.2
    refine ⟨x', ?_⟩
    rw [jointValueMatrix_mulVec] at hx ⊢
    rw [← hx]
    apply Finset.sum_congr rfl
    intro a _ha
    rw [valueMatrix_cascadeInputGaugeAction_zero]
    change valueMatrix theta 0 a *ᵥ
        (G.matrix *ᵥ fun q => x (a, q)) =
      (valueMatrix theta 0 a * G.matrix) *ᵥ fun q => x (a, q)
    exact Matrix.mulVec_mulVec _ _ _
  · intro h y
    rcases h y with ⟨x, hx⟩
    let x' : Fin k × Fin d → Real := fun aj =>
      G.invMatrix.mulVec (fun q => x (aj.1, q)) aj.2
    refine ⟨x', ?_⟩
    rw [jointValueMatrix_mulVec] at hx ⊢
    rw [← hx]
    apply Finset.sum_congr rfl
    intro a _ha
    rw [valueMatrix_cascadeInputGaugeAction_zero]
    change (valueMatrix theta 0 a * G.matrix) *ᵥ
        (G.invMatrix *ᵥ fun q => x (a, q)) =
      valueMatrix theta 0 a *ᵥ fun q => x (a, q)
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc,
      G.matrix_mul_invMatrix, Matrix.mul_one]

@[simp] theorem jointSurjective_cascadeInputGaugeAction_succ_iff {m k d : Nat}
    (G : GaugeMatrix d) (theta : Params (m + 1) k d) (l : Fin m) :
    JointSurjective (cascadeInputGaugeAction G theta) l.succ ↔
      JointSurjective theta l.succ := by
  have hmatrix : jointValueMatrix (cascadeInputGaugeAction G theta) l.succ =
      jointValueMatrix theta l.succ := by
    ext i aj
    exact congr_fun (congr_fun
      (valueMatrix_cascadeInputGaugeAction_succ G theta l aj.1) i) aj.2
  simp only [JointSurjective, hmatrix]

theorem regularity_cascadeInputGaugeAction_iff {m k d : Nat}
    (G : GaugeMatrix d) (theta : Params (m + 1) k d) :
    Regularity (cascadeInputGaugeAction G theta) ↔ Regularity theta := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro l
      induction l using Fin.cases with
      | zero =>
        intro a hzero
        apply h.attention_det_ne_zero 0 a
        rw [attentionMatrix_cascadeInputGaugeAction_zero, Matrix.det_mul,
          Matrix.det_mul, Matrix.det_transpose, hzero]
        simp
      | succ j =>
        intro a
        have hj := h.attention_det_ne_zero j.succ a
        rwa [attentionMatrix_cascadeInputGaugeAction_succ] at hj
    · intro l
      induction l using Fin.cases with
      | zero =>
        intro a
        have hs := h.attention_sym_ne_zero 0 a
        rw [attentionMatrix_cascadeInputGaugeAction_zero,
          sym_transpose_mul_mul, gauge_congruence_ne_zero_iff] at hs
        exact hs
      | succ j =>
        intro a
        have hj := h.attention_sym_ne_zero j.succ a
        rwa [attentionMatrix_cascadeInputGaugeAction_succ] at hj
    · intro l
      induction l using Fin.cases with
      | zero =>
        intro a
        have hv := h.value_ne_zero 0 a
        rw [valueMatrix_cascadeInputGaugeAction_zero,
          right_mul_gaugeMatrix_ne_zero_iff] at hv
        exact hv
      | succ j =>
        intro a
        have hj := h.value_ne_zero j.succ a
        rwa [valueMatrix_cascadeInputGaugeAction_succ] at hj
    · intro l
      induction l using Fin.cases with
      | zero =>
        intro a c heq
        apply h.attention_pairwise 0
        simp [heq]
      | succ j =>
        intro a c heq
        apply h.attention_pairwise j.succ
        simpa using heq
    · intro l
      induction l using Fin.cases with
      | zero =>
        intro hzero
        apply h.transmission 0
        rw [collapseMatrix_cascadeInputGaugeAction_zero, Matrix.det_mul, hzero]
        simp
      | succ j =>
        have hj := h.transmission j.succ
        rwa [collapseMatrix_cascadeInputGaugeAction_succ] at hj
    · intro l
      induction l using Fin.cases with
      | zero =>
        exact (jointSurjective_cascadeInputGaugeAction_zero_iff G theta).1
          (h.joint_surjective 0)
      | succ j =>
        exact (jointSurjective_cascadeInputGaugeAction_succ_iff G theta j).1
          (h.joint_surjective j.succ)
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro l
      induction l using Fin.cases with
      | zero =>
        intro a
        simp only [attentionMatrix_cascadeInputGaugeAction_zero, Matrix.det_mul,
          Matrix.det_transpose]
        exact mul_ne_zero (mul_ne_zero G.det_ne_zero (h.attention_det_ne_zero 0 a))
          G.det_ne_zero
      | succ j =>
        intro a
        rw [attentionMatrix_cascadeInputGaugeAction_succ]
        exact h.attention_det_ne_zero j.succ a
    · intro l
      induction l using Fin.cases with
      | zero =>
        intro a
        rw [attentionMatrix_cascadeInputGaugeAction_zero,
          sym_transpose_mul_mul, gauge_congruence_ne_zero_iff]
        exact h.attention_sym_ne_zero 0 a
      | succ j =>
        intro a
        rw [attentionMatrix_cascadeInputGaugeAction_succ]
        exact h.attention_sym_ne_zero j.succ a
    · intro l
      induction l using Fin.cases with
      | zero =>
        intro a
        rw [valueMatrix_cascadeInputGaugeAction_zero,
          right_mul_gaugeMatrix_ne_zero_iff]
        exact h.value_ne_zero 0 a
      | succ j =>
        intro a
        rw [valueMatrix_cascadeInputGaugeAction_succ]
        exact h.value_ne_zero j.succ a
    · intro l
      induction l using Fin.cases with
      | zero =>
        intro a c heq
        change attentionMatrix (cascadeInputGaugeAction G theta) 0 a =
          attentionMatrix (cascadeInputGaugeAction G theta) 0 c at heq
        rw [attentionMatrix_cascadeInputGaugeAction_zero,
          attentionMatrix_cascadeInputGaugeAction_zero] at heq
        exact h.attention_pairwise 0 (gauge_congruence_injective G heq)
      | succ j =>
        intro a c heq
        change attentionMatrix (cascadeInputGaugeAction G theta) j.succ a =
          attentionMatrix (cascadeInputGaugeAction G theta) j.succ c at heq
        rw [attentionMatrix_cascadeInputGaugeAction_succ,
          attentionMatrix_cascadeInputGaugeAction_succ] at heq
        exact h.attention_pairwise j.succ heq
    · intro l
      induction l using Fin.cases with
      | zero =>
        simp only [collapseMatrix_cascadeInputGaugeAction_zero,
          Matrix.det_mul]
        exact mul_ne_zero (h.transmission 0) G.det_ne_zero
      | succ j =>
        rw [collapseMatrix_cascadeInputGaugeAction_succ]
        exact h.transmission j.succ
    · intro l
      induction l using Fin.cases with
      | zero =>
        exact (jointSurjective_cascadeInputGaugeAction_zero_iff G theta).2
          (h.joint_surjective 0)
      | succ j =>
        exact (jointSurjective_cascadeInputGaugeAction_succ_iff G theta j).2
          (h.joint_surjective j.succ)

theorem localOpenness_cascadeInputGaugeAction_iff {m k d r : Nat}
    (G : GaugeMatrix d) (theta : Params (m + 1) k d) :
    LocalOpenness r (cascadeInputGaugeAction G theta) ↔ LocalOpenness r theta := by
  rw [localOpenness_iff_transmission, localOpenness_iff_transmission]
  constructor <;> intro h l
  · induction l using Fin.cases with
    | zero =>
      intro hzero
      apply h 0
      rw [collapseMatrix_cascadeInputGaugeAction_zero, Matrix.det_mul, hzero]
      simp
    | succ j =>
      have hj := h j.succ
      rwa [collapseMatrix_cascadeInputGaugeAction_succ] at hj
  · induction l using Fin.cases with
    | zero =>
      simp only [collapseMatrix_cascadeInputGaugeAction_zero, Matrix.det_mul]
      exact mul_ne_zero (h 0) G.det_ne_zero
    | succ j =>
      rw [collapseMatrix_cascadeInputGaugeAction_succ]
      exact h j.succ

/-! ## Multi-dial covariance -/

@[simp] theorem tail_cascadeInputGaugeAction {m k d : Nat}
    (G : GaugeMatrix d) (theta : Params (m + 1) k d) :
    Fin.tail (cascadeInputGaugeAction G theta) = Fin.tail theta := by
  funext l a
  exact cascadeInputGaugeAction_succ G theta l a

@[simp] theorem dialValueMatrix_cascadeInputGaugeAction {n k d : Nat}
    (G : GaugeMatrix d) (theta : Params (n + 1) k d)
    (t : Fin k → Real) :
    dialValueMatrix (cascadeInputGaugeAction G theta) t =
      dialValueMatrix theta t * G.matrix := by
  unfold dialValueMatrix
  simp_rw [valueMatrix_cascadeInputGaugeAction_zero]
  rw [Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro a _ha
  ext i j
  simp [Matrix.smul_apply, Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _hq
  ring

@[simp] theorem dialContrast_cascadeInputGaugeAction {n k d : Nat}
    (G : GaugeMatrix d) (theta : Params (n + 1) k d)
    (t : Fin k → Real) (w : Vec d) :
    dialContrast (cascadeInputGaugeAction G theta) t w =
      dialContrast theta t (G.matrix *ᵥ w) := by
  unfold dialContrast
  rw [collapseMatrix_cascadeInputGaugeAction_zero,
    dialValueMatrix_cascadeInputGaugeAction, ← Matrix.sub_mul,
    Matrix.mulVec_mulVec]

@[simp] theorem anchorGradient_cascadeInputGaugeAction {n k d : Nat}
    (G : GaugeMatrix d) (theta : Params (n + 1) k d)
    (w : Vec d) (a : Fin k) :
    anchorGradient (cascadeInputGaugeAction G theta) w a =
      G.matrixᵀ *ᵥ anchorGradient theta (G.matrix *ᵥ w) a := by
  unfold anchorGradient
  rw [attentionMatrix_cascadeInputGaugeAction_zero]
  simp [Matrix.transpose_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]

@[simp] theorem levelPrefixMatrix_cascadeInputGaugeAction {n k d : Nat}
    (G : GaugeMatrix d) (theta : Params (n + 1) k d)
    (jb : LevelRowIndex (n + 1) k) :
    levelPrefixMatrix (cascadeInputGaugeAction G theta) jb =
      levelPrefixMatrix theta jb := by
  simp [levelPrefixMatrix]

@[simp] theorem levelFullPrefixMatrix_cascadeInputGaugeAction {n k d : Nat}
    (G : GaugeMatrix d) (theta : Params (n + 1) k d)
    (jb : LevelRowIndex (n + 1) k) :
    levelFullPrefixMatrix (cascadeInputGaugeAction G theta) jb =
      levelFullPrefixMatrix theta jb * G.matrix := by
  rw [levelFullPrefixMatrix, levelFullPrefixMatrix,
    levelPrefixMatrix_cascadeInputGaugeAction,
    collapseMatrix_cascadeInputGaugeAction_zero, Matrix.mul_assoc]

@[simp] theorem attentionMatrix_cascadeInputGaugeAction_levelLayer {n k d : Nat}
    (G : GaugeMatrix d) (theta : Params (n + 1) k d)
    (jb : LevelRowIndex (n + 1) k) :
    attentionMatrix (cascadeInputGaugeAction G theta) (levelLayer jb) jb.2 =
      attentionMatrix theta (levelLayer jb) jb.2 := by
  change attentionMatrix (cascadeInputGaugeAction G theta) jb.1.succ jb.2 = _
  exact attentionMatrix_cascadeInputGaugeAction_succ G theta jb.1 jb.2

@[simp] theorem levelGradient_cascadeInputGaugeAction {n k d : Nat}
    (G : GaugeMatrix d) (theta : Params (n + 1) k d)
    (t : Fin k → Real) (w : Vec d) (jb : LevelRowIndex (n + 1) k) :
    levelGradient (cascadeInputGaugeAction G theta) t w jb =
      G.matrixᵀ *ᵥ levelGradient theta t (G.matrix *ᵥ w) jb := by
  unfold levelGradient
  rw [levelFullPrefixMatrix_cascadeInputGaugeAction,
    attentionMatrix_cascadeInputGaugeAction_levelLayer,
    levelPrefixMatrix_cascadeInputGaugeAction,
    dialContrast_cascadeInputGaugeAction]
  simp [Matrix.transpose_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem multiDialRowGradient_cascadeInputGaugeAction {n k d : Nat}
    (G : GaugeMatrix d) (theta : Params (n + 1) k d)
    (t : Fin k → Real) (w : Vec d) (row : MultiDialRow (n + 1) k) :
    multiDialRowGradient (cascadeInputGaugeAction G theta) t w row =
      G.matrixᵀ *ᵥ multiDialRowGradient theta t (G.matrix *ᵥ w) row := by
  rcases row with a | jb
  · exact anchorGradient_cascadeInputGaugeAction G theta w a
  · exact levelGradient_cascadeInputGaugeAction G theta t w jb

theorem multiDialGramDet_ne_zero_iff_linearIndependent {n k d : Nat}
    (theta : Params (n + 1) k d) (t : Fin k → Real) (w : Vec d) :
    multiDialGramDet theta t w ≠ 0 ↔
      LinearIndependent Real (multiDialRowGradient theta t w) := by
  constructor
  · exact linearIndependent_multiDialRowGradient_of_gramDet_ne_zero theta t w
  · intro hli
    let Gm := multiDialGradientMatrix theta t w
    let A : Matrix (MultiDialRow (n + 1) k) (MultiDialRow (n + 1) k) Real :=
      Gmᵀ * Gm
    have hGrank : Gm.rank = Fintype.card (MultiDialRow (n + 1) k) := by
      rw [Matrix.rank_eq_finrank_span_cols]
      have hcard := (linearIndependent_iff_card_eq_finrank_span.mp hli)
      simpa [Gm, multiDialGradientMatrix, Matrix.col] using hcard.symm
    have hArank : A.rank = Fintype.card (MultiDialRow (n + 1) k) := by
      change (Gmᵀ * Gm).rank = _
      rw [Matrix.rank_transpose_mul_self]
      exact hGrank
    have hAcols : LinearIndependent Real A.col := by
      apply linearIndependent_iff_card_eq_finrank_span.mpr
      simpa [Set.finrank, Matrix.rank_eq_finrank_span_cols] using hArank.symm
    have hAunit : IsUnit A := Matrix.linearIndependent_cols_iff_isUnit.mp hAcols
    have hdetunit : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hAunit
    have hAdet : A.det ≠ 0 := isUnit_iff_ne_zero.mp hdetunit
    simpa [multiDialGramDet, multiDialGramMatrix, Gm, A] using hAdet

theorem transposeGauge_mulVec_injective {d : Nat} (G : GaugeMatrix d) :
    Function.Injective G.matrixᵀ.mulVec := by
  intro x y hxy
  have h := congrArg (fun z => G.invTranspose *ᵥ z) hxy
  have hx : G.invTranspose *ᵥ (G.matrixᵀ *ᵥ x) = x := by
    calc
      _ = (G.invTranspose * G.matrixᵀ) *ᵥ x :=
        Matrix.mulVec_mulVec x G.invTranspose G.matrixᵀ
      _ = x := by rw [G.invTranspose_mul_matrix_transpose, Matrix.one_mulVec]
  have hy : G.invTranspose *ᵥ (G.matrixᵀ *ᵥ y) = y := by
    calc
      _ = (G.invTranspose * G.matrixᵀ) *ᵥ y :=
        Matrix.mulVec_mulVec y G.invTranspose G.matrixᵀ
      _ = y := by rw [G.invTranspose_mul_matrix_transpose, Matrix.one_mulVec]
  exact hx.symm.trans (h.trans hy)

theorem multiDialCertificate_cascadeInputGaugeAction_iff {n k d : Nat}
    (G : GaugeMatrix d) (theta : Params (n + 1) k d) :
    MultiDialCertificate (cascadeInputGaugeAction G theta) ↔
      MultiDialCertificate theta := by
  rw [multiDialCertificate_iff_exists_gramDet_ne_zero,
    multiDialCertificate_iff_exists_gramDet_ne_zero]
  constructor
  · rintro ⟨t, w, hdet⟩
    refine ⟨t, G.matrix *ᵥ w, ?_⟩
    rw [multiDialGramDet_ne_zero_iff_linearIndependent] at hdet ⊢
    have hcomp : (fun row => G.matrixᵀ *ᵥ
        multiDialRowGradient theta t (G.matrix *ᵥ w) row) =
        multiDialRowGradient (cascadeInputGaugeAction G theta) t w := by
      funext row
      exact (multiDialRowGradient_cascadeInputGaugeAction G theta t w row).symm
    rw [← hcomp] at hdet
    exact LinearIndependent.of_comp G.matrixᵀ.mulVecLin hdet
  · rintro ⟨t, w, hdet⟩
    refine ⟨t, G.invMatrix *ᵥ w, ?_⟩
    rw [multiDialGramDet_ne_zero_iff_linearIndependent] at hdet ⊢
    have hGw : G.matrix *ᵥ (G.invMatrix *ᵥ w) = w := by
      calc
        _ = (G.matrix * G.invMatrix) *ᵥ w :=
          Matrix.mulVec_mulVec w G.matrix G.invMatrix
        _ = w := by rw [G.matrix_mul_invMatrix, Matrix.one_mulVec]
    have hcov : multiDialRowGradient (cascadeInputGaugeAction G theta) t
        (G.invMatrix *ᵥ w) =
        fun row => G.matrixᵀ *ᵥ multiDialRowGradient theta t w row := by
      funext row
      rw [multiDialRowGradient_cascadeInputGaugeAction, hGw]
    rw [hcov]
    have hker : G.matrixᵀ.mulVecLin.ker = ⊥ :=
      LinearMap.ker_eq_bot.mpr (transposeGauge_mulVec_injective G)
    have hmapped := hdet.map' G.matrixᵀ.mulVecLin hker
    change LinearIndependent Real
      (G.matrixᵀ.mulVecLin ∘ multiDialRowGradient theta t w)
    exact hmapped

/-- Gauge covariance of the repaired headwise certificate.  The distinguished
head and scalar dial are unchanged; only the probe vector is transported. -/
theorem headwiseDialCertificate_cascadeInputGaugeAction_iff {n k d : Nat}
    (G : GaugeMatrix d) (theta : Params (n + 1) k d) :
    HeadwiseDialCertificate (cascadeInputGaugeAction G theta) ↔
      HeadwiseDialCertificate theta := by
  constructor
  · intro hcert h
    rcases hcert h with ⟨t, ht, w, hdet⟩
    refine ⟨t, ht, G.matrix *ᵥ w, ?_⟩
    rw [multiDialGramDet_ne_zero_iff_linearIndependent] at hdet ⊢
    have hcomp : (fun row => G.matrixᵀ *ᵥ
        multiDialRowGradient theta (headwiseDialTuple h t)
          (G.matrix *ᵥ w) row) =
        multiDialRowGradient (cascadeInputGaugeAction G theta)
          (headwiseDialTuple h t) w := by
      funext row
      exact (multiDialRowGradient_cascadeInputGaugeAction G theta
        (headwiseDialTuple h t) w row).symm
    rw [← hcomp] at hdet
    exact LinearIndependent.of_comp G.matrixᵀ.mulVecLin hdet
  · intro hcert h
    rcases hcert h with ⟨t, ht, w, hdet⟩
    refine ⟨t, ht, G.invMatrix *ᵥ w, ?_⟩
    rw [multiDialGramDet_ne_zero_iff_linearIndependent] at hdet ⊢
    have hGw : G.matrix *ᵥ (G.invMatrix *ᵥ w) = w := by
      calc
        _ = (G.matrix * G.invMatrix) *ᵥ w :=
          Matrix.mulVec_mulVec w G.matrix G.invMatrix
        _ = w := by rw [G.matrix_mul_invMatrix, Matrix.one_mulVec]
    have hcov : multiDialRowGradient (cascadeInputGaugeAction G theta)
        (headwiseDialTuple h t) (G.invMatrix *ᵥ w) =
        fun row => G.matrixᵀ *ᵥ
          multiDialRowGradient theta (headwiseDialTuple h t) w row := by
      funext row
      rw [multiDialRowGradient_cascadeInputGaugeAction, hGw]
    rw [hcov]
    have hker : G.matrixᵀ.mulVecLin.ker = ⊥ :=
      LinearMap.ker_eq_bot.mpr (transposeGauge_mulVec_injective G)
    have hmapped := hdet.map' G.matrixᵀ.mulVecLin hker
    change LinearIndependent Real
      (G.matrixᵀ.mulVecLin ∘
        multiDialRowGradient theta (headwiseDialTuple h t) w)
    exact hmapped

/-! ## Recursive genericity -/

theorem currentGenericClauses_cascadeInputGaugeAction_iff {m k d r : Nat}
    (G : GaugeMatrix d) (theta : Params (m + 2) k d) :
    CurrentGenericClauses r (cascadeInputGaugeAction G theta) ↔
      CurrentGenericClauses r theta := by
  constructor <;> intro h
  · exact ⟨(regularity_cascadeInputGaugeAction_iff G theta).1 h.regularity,
      (cascadeCertificate_inputGauge_iff G theta).1 h.cascadeCertificate,
      (headwiseDialCertificate_cascadeInputGaugeAction_iff G theta).1
        h.headwiseDialCertificate⟩
  · exact ⟨(regularity_cascadeInputGaugeAction_iff G theta).2 h.regularity,
      (cascadeCertificate_inputGauge_iff G theta).2 h.cascadeCertificate,
      (headwiseDialCertificate_cascadeInputGaugeAction_iff G theta).2
        h.headwiseDialCertificate⟩

theorem recursiveGeneric_cascadeInputGaugeAction_iff {m k d r : Nat}
    (G : GaugeMatrix d) (theta : Params (m + 1) k d) :
    RecursiveGeneric r (m + 1) k d (cascadeInputGaugeAction G theta) ↔
      RecursiveGeneric r (m + 1) k d theta := by
  cases m with
  | zero =>
      exact regularity_cascadeInputGaugeAction_iff G theta
  | succ m =>
      rw [recursiveGeneric_succ_succ, recursiveGeneric_succ_succ,
        tail_cascadeInputGaugeAction,
        currentGenericClauses_cascadeInputGaugeAction_iff]

end

end TransformerIdentifiability.NLayer.NoSkip
