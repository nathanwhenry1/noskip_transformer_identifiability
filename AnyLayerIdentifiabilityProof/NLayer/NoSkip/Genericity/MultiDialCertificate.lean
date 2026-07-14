import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Genericity.MultiDialRows

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.NoSkip

/-!
# The simultaneous multi-dial Gram certificate

The auxiliary polynomial variables are the complete dial tuple `t : Fin k → ℝ`
and probe vector `w : Fin d → ℝ`.  At total depth `n+1`, the fixed column index
from `MultiDialRows` has cardinality `k * (n+1)`: anchors first, followed by all
corrected deeper-level rows, including the final layer.
-/

/-! ## Numeric Gram matrix and determinant -/

/-- The row Gram matrix `GᵀG` of all simultaneous multi-dial gradients. -/
noncomputable def multiDialGramMatrix {n k d : Nat}
    (theta : Params (n + 1) k d) (t : Fin k → Real) (w : Vec d) :
    Matrix (MultiDialRow (n + 1) k) (MultiDialRow (n + 1) k) Real :=
  (multiDialGradientMatrix theta t w)ᵀ * multiDialGradientMatrix theta t w

/-- TeX `𝒜(θ;t,w) = det(GᵀG)`. -/
noncomputable def multiDialGramDet {n k d : Nat}
    (theta : Params (n + 1) k d) (t : Fin k → Real) (w : Vec d) : Real :=
  (multiDialGramMatrix theta t w).det

@[simp] theorem multiDialGramMatrix_apply {n k d : Nat}
    (theta : Params (n + 1) k d) (t : Fin k → Real) (w : Vec d)
    (row row' : MultiDialRow (n + 1) k) :
    multiDialGramMatrix theta t w row row' =
      dotProduct (multiDialRowGradient theta t w row)
        (multiDialRowGradient theta t w row') := by
  simp [multiDialGramMatrix, Matrix.mul_apply, dotProduct]

/-! ## Polynomial realization in `(t,w)` -/

/-- Auxiliary variables for the complete dial tuple and probe vector. -/
abbrev MultiDialAuxVar (k d : Nat) := Fin k ⊕ Fin d

/-- Polynomial ring in the auxiliary coordinates `(t,w)`. -/
abbrev MultiDialAuxPoly (k d : Nat) := MvPolynomial (MultiDialAuxVar k d) Real

/-- Polynomial coordinate for one dial component. -/
noncomputable def multiDialAuxT {k d : Nat} (a : Fin k) : MultiDialAuxPoly k d :=
  MvPolynomial.X (Sum.inl a)

/-- Polynomial coordinate for one probe-vector component. -/
noncomputable def multiDialAuxW {k d : Nat} (i : Fin d) : MultiDialAuxPoly k d :=
  MvPolynomial.X (Sum.inr i)

/-- Evaluation assignment corresponding to a concrete pair `(t,w)`. -/
def multiDialAuxEval {k d : Nat} (t : Fin k → Real) (w : Vec d) :
    MultiDialAuxVar k d → Real
  | Sum.inl a => t a
  | Sum.inr i => w i

@[simp] theorem eval_multiDialAuxT {k d : Nat} (t : Fin k → Real)
    (w : Vec d) (a : Fin k) :
    MvPolynomial.eval (multiDialAuxEval t w) (multiDialAuxT a) = t a := by
  simp [multiDialAuxT, multiDialAuxEval]

@[simp] theorem eval_multiDialAuxW {k d : Nat} (t : Fin k → Real)
    (w : Vec d) (i : Fin d) :
    MvPolynomial.eval (multiDialAuxEval t w) (multiDialAuxW i) = w i := by
  simp [multiDialAuxW, multiDialAuxEval]

/-- Embed a real matrix as a constant matrix over the auxiliary polynomial
ring. -/
noncomputable def realMatrixToMultiDialAuxPoly {k d : Nat}
    (M : Matrix (Fin d) (Fin d) Real) :
    Matrix (Fin d) (Fin d) (MultiDialAuxPoly k d) :=
  M.map (MvPolynomial.C : Real →+* MultiDialAuxPoly k d)

@[simp] theorem map_realMatrixToMultiDialAuxPoly {k d : Nat}
    (rho : MultiDialAuxVar k d → Real)
    (M : Matrix (Fin d) (Fin d) Real) :
    (realMatrixToMultiDialAuxPoly (k := k) M).map (MvPolynomial.eval rho) = M := by
  ext i j
  simp [realMatrixToMultiDialAuxPoly]

/-- Evaluation commutes with matrix-vector multiplication over the auxiliary
polynomial ring. -/
theorem multiDialAux_eval_mulVec {k d : Nat} {m q : Type*} [Fintype q]
    (rho : MultiDialAuxVar k d → Real)
    (M : Matrix m q (MultiDialAuxPoly k d)) (v : q → MultiDialAuxPoly k d) :
    (fun i => MvPolynomial.eval rho (M.mulVec v i)) =
      (M.map (MvPolynomial.eval rho)).mulVec
        (fun j => MvPolynomial.eval rho (v j)) := by
  funext i
  simp [Matrix.mulVec, dotProduct]

/-- Polynomial version of `T_t = ∑ a, t_a V_{1a}`. -/
noncomputable def multiDialValueMatrixPoly {n k d : Nat}
    (theta : Params (n + 1) k d) :
    Matrix (Fin d) (Fin d) (MultiDialAuxPoly k d) :=
  ∑ a : Fin k, multiDialAuxT (d := d) a •
    realMatrixToMultiDialAuxPoly (k := k) (valueMatrix theta 0 a)

@[simp] theorem map_multiDialValueMatrixPoly {n k d : Nat}
    (theta : Params (n + 1) k d) (t : Fin k → Real) (w : Vec d) :
    (multiDialValueMatrixPoly theta).map
        (MvPolynomial.eval (multiDialAuxEval t w)) =
      dialValueMatrix theta t := by
  ext i j
  simp [multiDialValueMatrixPoly, dialValueMatrix, Matrix.sum_apply,
    Matrix.smul_apply, realMatrixToMultiDialAuxPoly]

/-- Polynomial vector for `(C₁-T_t)w`. -/
noncomputable def multiDialContrastPoly {n k d : Nat}
    (theta : Params (n + 1) k d) : Fin d → MultiDialAuxPoly k d :=
  (realMatrixToMultiDialAuxPoly (k := k) (collapseMatrix theta 0) -
      multiDialValueMatrixPoly theta) *ᵥ multiDialAuxW

@[simp] theorem eval_multiDialContrastPoly {n k d : Nat}
    (theta : Params (n + 1) k d) (t : Fin k → Real) (w : Vec d) :
    (fun i => MvPolynomial.eval (multiDialAuxEval t w)
      (multiDialContrastPoly theta i)) = dialContrast theta t w := by
  rw [multiDialContrastPoly, dialContrast]
  trans
      ((realMatrixToMultiDialAuxPoly (k := k) (collapseMatrix theta 0) -
          multiDialValueMatrixPoly theta).map
        (MvPolynomial.eval (multiDialAuxEval t w))) *ᵥ
          (fun i => MvPolynomial.eval (multiDialAuxEval t w) (multiDialAuxW i))
  · exact multiDialAux_eval_mulVec (multiDialAuxEval t w)
      (realMatrixToMultiDialAuxPoly (k := k) (collapseMatrix theta 0) -
        multiDialValueMatrixPoly theta) multiDialAuxW
  · have hmap :
        (realMatrixToMultiDialAuxPoly (k := k) (collapseMatrix theta 0) -
            multiDialValueMatrixPoly theta).map
              (MvPolynomial.eval (multiDialAuxEval t w)) =
          collapseMatrix theta 0 - dialValueMatrix theta t := by
        ext i j
        simp only [Matrix.map_apply, Matrix.sub_apply, map_sub]
        change MvPolynomial.eval (multiDialAuxEval t w)
            (realMatrixToMultiDialAuxPoly (k := k) (collapseMatrix theta 0) i j) -
              MvPolynomial.eval (multiDialAuxEval t w)
                (multiDialValueMatrixPoly theta i j) =
            collapseMatrix theta 0 i j - dialValueMatrix theta t i j
        congr
        · exact congr_fun (congr_fun
            (map_realMatrixToMultiDialAuxPoly (multiDialAuxEval t w)
              (collapseMatrix theta 0)) i) j
        · exact congr_fun (congr_fun
            (map_multiDialValueMatrixPoly theta t w) i) j
    rw [hmap]
    simp

/-- Polynomial realization of every fixed-order gradient column. -/
noncomputable def multiDialRowGradientPoly {n k d : Nat}
    (theta : Params (n + 1) k d) :
    MultiDialRow (n + 1) k → Fin d → MultiDialAuxPoly k d
  | Sum.inl a =>
      realMatrixToMultiDialAuxPoly (k := k) ((attentionMatrix theta 0 a)ᵀ) *ᵥ
        multiDialAuxW
  | Sum.inr jb =>
      realMatrixToMultiDialAuxPoly (k := k)
        ((levelFullPrefixMatrix theta jb)ᵀ *
          ((attentionMatrix theta (levelLayer jb) jb.2)ᵀ *
            levelPrefixMatrix theta jb)) *ᵥ multiDialContrastPoly theta

@[simp] theorem eval_multiDialRowGradientPoly {n k d : Nat}
    (theta : Params (n + 1) k d) (t : Fin k → Real) (w : Vec d)
    (row : MultiDialRow (n + 1) k) :
    (fun i => MvPolynomial.eval (multiDialAuxEval t w)
      (multiDialRowGradientPoly theta row i)) =
        multiDialRowGradient theta t w row := by
  rcases row with a | row
  · rw [multiDialRowGradientPoly, multiDialRowGradient]
    trans
        (realMatrixToMultiDialAuxPoly (k := k)
          ((attentionMatrix theta 0 a)ᵀ)).map
            (MvPolynomial.eval (multiDialAuxEval t w)) *ᵥ
          (fun i => MvPolynomial.eval (multiDialAuxEval t w) (multiDialAuxW i))
    · exact multiDialAux_eval_mulVec (multiDialAuxEval t w)
        (realMatrixToMultiDialAuxPoly (k := k) ((attentionMatrix theta 0 a)ᵀ))
        multiDialAuxW
    · simp [anchorGradient]
  · rw [multiDialRowGradientPoly, multiDialRowGradient]
    trans
        (realMatrixToMultiDialAuxPoly (k := k)
          ((levelFullPrefixMatrix theta row)ᵀ *
            ((attentionMatrix theta (levelLayer row) row.2)ᵀ *
              levelPrefixMatrix theta row))).map
            (MvPolynomial.eval (multiDialAuxEval t w)) *ᵥ
          (fun i => MvPolynomial.eval (multiDialAuxEval t w)
            (multiDialContrastPoly theta i))
    · exact multiDialAux_eval_mulVec (multiDialAuxEval t w)
        (realMatrixToMultiDialAuxPoly (k := k)
          ((levelFullPrefixMatrix theta row)ᵀ *
            ((attentionMatrix theta (levelLayer row) row.2)ᵀ *
              levelPrefixMatrix theta row)))
        (multiDialContrastPoly theta)
    · rw [map_realMatrixToMultiDialAuxPoly, eval_multiDialContrastPoly]
      simp [levelGradient, Matrix.mulVec_mulVec]

/-- Polynomial matrix whose columns are the polynomial gradient vectors. -/
noncomputable def multiDialGradientPolyMatrix {n k d : Nat}
    (theta : Params (n + 1) k d) :
    Matrix (Fin d) (MultiDialRow (n + 1) k) (MultiDialAuxPoly k d) :=
  Matrix.of fun i row => multiDialRowGradientPoly theta row i

@[simp] theorem map_multiDialGradientPolyMatrix {n k d : Nat}
    (theta : Params (n + 1) k d) (t : Fin k → Real) (w : Vec d) :
    (multiDialGradientPolyMatrix theta).map
        (MvPolynomial.eval (multiDialAuxEval t w)) =
      multiDialGradientMatrix theta t w := by
  ext i row
  exact congr_fun (eval_multiDialRowGradientPoly theta t w row) i

/-- The Gram determinant as an actual polynomial in the full auxiliary tuple
`(t,w)`. -/
noncomputable def multiDialGramPoly {n k d : Nat}
    (theta : Params (n + 1) k d) : MultiDialAuxPoly k d :=
  let G := multiDialGradientPolyMatrix theta
  ((Gᵀ * G) : Matrix (MultiDialRow (n + 1) k)
    (MultiDialRow (n + 1) k) (MultiDialAuxPoly k d)).det

@[simp] theorem eval_multiDialGramPoly {n k d : Nat}
    (theta : Params (n + 1) k d) (t : Fin k → Real) (w : Vec d) :
    MvPolynomial.eval (multiDialAuxEval t w) (multiDialGramPoly theta) =
      multiDialGramDet theta t w := by
  let evalHom := MvPolynomial.eval (multiDialAuxEval t w)
  let Gp := multiDialGradientPolyMatrix theta
  change evalHom (((Gpᵀ * Gp) : Matrix (MultiDialRow (n + 1) k)
    (MultiDialRow (n + 1) k) (MultiDialAuxPoly k d)).det) =
      multiDialGramDet theta t w
  rw [RingHom.map_det]
  change (((Gpᵀ * Gp).map evalHom) : Matrix (MultiDialRow (n + 1) k)
    (MultiDialRow (n + 1) k) Real).det = multiDialGramDet theta t w
  rw [Matrix.map_mul, Matrix.transpose_map, map_multiDialGradientPolyMatrix]
  rfl

/-! ## Coefficient certificate -/

/-- TeX coefficient sum of squares `p^anc(θ)`.  It is nonzero exactly when
`multiDialGramPoly θ` is not the zero polynomial in `(t,w)`. -/
noncomputable def multiDialCoefficientCertificate {n k d : Nat}
    (theta : Params (n + 1) k d) : Real :=
  ∑ monomial ∈ (multiDialGramPoly theta).support,
    (MvPolynomial.coeff monomial (multiDialGramPoly theta)) ^ 2

theorem multiDialCoefficientCertificate_ne_zero_iff {n k d : Nat}
    (theta : Params (n + 1) k d) :
    multiDialCoefficientCertificate theta ≠ 0 ↔ multiDialGramPoly theta ≠ 0 := by
  classical
  constructor
  · intro hcert hpoly
    apply hcert
    simp [multiDialCoefficientCertificate, hpoly]
  · intro hpoly
    rcases (mvPolynomial_ne_zero_iff_exists_coeff_ne_zero
      (multiDialGramPoly theta)).mp hpoly with ⟨monomial, hcoeff⟩
    have hmem : monomial ∈ (multiDialGramPoly theta).support :=
      MvPolynomial.mem_support_iff.mpr hcoeff
    have hpos : 0 < multiDialCoefficientCertificate theta := by
      apply Finset.sum_pos'
      · intro m hm
        positivity
      · exact ⟨monomial, hmem, sq_pos_of_ne_zero hcoeff⟩
    exact ne_of_gt hpos

/-- Semantic multi-dial certificate: some coefficient of the auxiliary Gram
polynomial is nonzero, expressed by the TeX sum of coefficient squares. -/
def MultiDialCertificate {n k d : Nat} (theta : Params (n + 1) k d) : Prop :=
  multiDialCoefficientCertificate theta ≠ 0

theorem multiDialCertificate_iff_gramPoly_ne_zero {n k d : Nat}
    (theta : Params (n + 1) k d) :
    MultiDialCertificate theta ↔ multiDialGramPoly theta ≠ 0 :=
  multiDialCoefficientCertificate_ne_zero_iff theta

/-- A nonzero auxiliary polynomial has a concrete real evaluation where it is
nonzero. -/
theorem multiDialGramPoly_ne_zero_iff_exists_eval_ne_zero {n k d : Nat}
    (theta : Params (n + 1) k d) :
    multiDialGramPoly theta ≠ 0 ↔
      ∃ t : Fin k → Real, ∃ w : Vec d, multiDialGramDet theta t w ≠ 0 := by
  constructor
  · intro hpoly
    by_contra hnone
    apply hpoly
    apply MvPolynomial.funext
    intro rho
    let t : Fin k → Real := fun a => rho (Sum.inl a)
    let w : Vec d := fun i => rho (Sum.inr i)
    have heval : multiDialAuxEval t w = rho := by
      funext x
      rcases x with a | i <;> rfl
    have hdet : multiDialGramDet theta t w = 0 := by
      by_contra hne
      exact hnone ⟨t, w, hne⟩
    rw [← eval_multiDialGramPoly theta t w] at hdet
    rw [← heval]
    exact hdet
  · rintro ⟨t, w, hdet⟩ hzero
    apply hdet
    rw [← eval_multiDialGramPoly theta t w, hzero]
    simp

theorem multiDialCertificate_iff_exists_gramDet_ne_zero {n k d : Nat}
    (theta : Params (n + 1) k d) :
    MultiDialCertificate theta ↔
      ∃ t : Fin k → Real, ∃ w : Vec d, multiDialGramDet theta t w ≠ 0 := by
  rw [multiDialCertificate_iff_gramPoly_ne_zero,
    multiDialGramPoly_ne_zero_iff_exists_eval_ne_zero]

/-! ## Independence and the dimension consequence -/

/-- A nonzero Gram evaluation makes all fixed-order gradient columns linearly
independent. -/
theorem linearIndependent_multiDialRowGradient_of_gramDet_ne_zero {n k d : Nat}
    (theta : Params (n + 1) k d) (t : Fin k → Real) (w : Vec d)
    (hdet : multiDialGramDet theta t w ≠ 0) :
    LinearIndependent Real (multiDialRowGradient theta t w) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro coeff hsum row
  let G := multiDialGradientMatrix theta t w
  let A : Matrix (MultiDialRow (n + 1) k) (MultiDialRow (n + 1) k) Real :=
    Gᵀ * G
  have hG : G *ᵥ coeff = 0 := by
    funext i
    have hi := congr_fun hsum i
    simpa [G, multiDialGradientMatrix, Matrix.mulVec, dotProduct, mul_comm] using hi
  have hA : A *ᵥ coeff = 0 := by
    calc
      A *ᵥ coeff = Gᵀ *ᵥ (G *ᵥ coeff) := by
        exact (Matrix.mulVec_mulVec coeff Gᵀ G).symm
      _ = 0 := by rw [hG, Matrix.mulVec_zero]
  have hA_det : A.det ≠ 0 := by
    simpa [multiDialGramDet, multiDialGramMatrix, G, A] using hdet
  have hA_unit : IsUnit A.det := isUnit_iff_ne_zero.mpr hA_det
  have hcoeff : coeff = 0 := by
    calc
      coeff = (1 : Matrix (MultiDialRow (n + 1) k)
          (MultiDialRow (n + 1) k) Real) *ᵥ coeff := by simp
      _ = (A⁻¹ * A) *ᵥ coeff := by rw [Matrix.nonsing_inv_mul A hA_unit]
      _ = A⁻¹ *ᵥ (A *ᵥ coeff) := (Matrix.mulVec_mulVec coeff A⁻¹ A).symm
      _ = 0 := by rw [hA, Matrix.mulVec_zero]
  exact congr_fun hcoeff row

/-- The same implication stated directly from polynomial evaluation. -/
theorem linearIndependent_multiDialRowGradient_of_gramPoly_eval_ne_zero
    {n k d : Nat} (theta : Params (n + 1) k d) (t : Fin k → Real)
    (w : Vec d)
    (heval : MvPolynomial.eval (multiDialAuxEval t w)
      (multiDialGramPoly theta) ≠ 0) :
    LinearIndependent Real (multiDialRowGradient theta t w) :=
  linearIndependent_multiDialRowGradient_of_gramDet_ne_zero theta t w
    (by simpa using heval)

/-- Dimension audit: a nonzero Gram evaluation forces the exact two-family row
count `k*(n+1)` to fit in the ambient dimension. -/
theorem multiDial_rowCount_le_of_gramDet_ne_zero {n k d : Nat}
    (theta : Params (n + 1) k d) (t : Fin k → Real) (w : Vec d)
    (hdet : multiDialGramDet theta t w ≠ 0) :
    k * (n + 1) ≤ d := by
  have hli := linearIndependent_multiDialRowGradient_of_gramDet_ne_zero
    theta t w hdet
  have hcard := hli.fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card Real] at hcard
  rw [card_multiDialRow_depth_succ] at hcard
  simpa using hcard

/-- Packaged evaluation consequence used by downstream affine solving. -/
theorem multiDial_independence_and_rowCount_of_gramDet_ne_zero {n k d : Nat}
    (theta : Params (n + 1) k d) (t : Fin k → Real) (w : Vec d)
    (hdet : multiDialGramDet theta t w ≠ 0) :
    LinearIndependent Real (multiDialRowGradient theta t w) ∧
      k * (n + 1) ≤ d :=
  ⟨linearIndependent_multiDialRowGradient_of_gramDet_ne_zero theta t w hdet,
    multiDial_rowCount_le_of_gramDet_ne_zero theta t w hdet⟩

end TransformerIdentifiability.NLayer.NoSkip
