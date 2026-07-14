import AnyLayerIdentifiabilityProof.NLayer.KHead.Genericity.Regularity

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.KHead

/-!
# K-head genericity: cascade and anchor certificates

This file ports the finite certificate data from TeX Section 03b.  The full
sign-region lemma is represented by the `SignRegionData` API below, with the
algebraic center construction, solved-coordinate chart, shrinking argument, and
topological consequences proved in Lean.
-/

/-! ## Cascade certificate -/

/-- The TeX count `n_bullet(m,k) = k*m`. -/
def nBullet (m k : Nat) : Nat :=
  k * m

@[simp]
theorem nBullet_zero_left (k : Nat) : nBullet 0 k = 0 := by
  simp [nBullet]

@[simp]
theorem nBullet_zero_right (m : Nat) : nBullet m 0 = 0 := by
  simp [nBullet]

/-- A later layer of a positive tail, converting a `Fin m` index to layer `1+n`. -/
def laterLayer {m : Nat} (n : Fin m) : Fin (m + 1) :=
  ⟨n.val + 1, Nat.succ_lt_succ n.isLt⟩

@[simp]
theorem laterLayer_val {m : Nat} (n : Fin m) :
    (laterLayer n).val = n.val + 1 :=
  rfl

/-- Product along a cascade chain after `n` later layers.

For a tail of depth `m+1`, `n = 0` is the first-layer value matrix
`V_0h`; each successor multiplies by the selected value matrix in the next
layer. -/
noncomputable def cascadeProduct {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (χ : Fin m → Fin k) : Nat → Matrix (Fin d) (Fin d) ℝ
  | 0 => valueMatrix θ 0 h
  | n + 1 =>
      if hn : n < m then
        valueMatrix θ (laterLayer ⟨n, hn⟩) (χ ⟨n, hn⟩) *
          cascadeProduct θ h χ n
      else
        cascadeProduct θ h χ n

@[simp]
theorem cascadeProduct_zero {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (χ : Fin m → Fin k) :
    cascadeProduct θ h χ 0 = valueMatrix θ 0 h :=
  rfl

/-- Final residue product for a cascade chain. -/
noncomputable def cascadeFinalProduct {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (χ : Fin m → Fin k) : Matrix (Fin d) (Fin d) ℝ :=
  cascadeProduct θ h χ m

/-- Ignition matrix for a later layer in a cascade chain. -/
noncomputable def cascadeIgnitionMatrix {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (χ : Fin m → Fin k) (j : Fin m) :
    Matrix (Fin d) (Fin d) ℝ :=
  sym ((cascadeProduct θ h χ j.val)ᵀ *
    attentionMatrix θ (laterLayer j) (χ j) *
      cascadeProduct θ h χ j.val)

/-- One chain polynomial value: nonzero residue and all nonzero ignitions. -/
noncomputable def cascadeChainValue {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (χ : Fin m → Fin k) : ℝ :=
  matrixFrobSq (cascadeFinalProduct θ h χ) *
    ∏ j : Fin m, matrixFrobSq (cascadeIgnitionMatrix θ h χ j)

/-- Headwise cascade certificate: a finite polynomial-or over all chains. -/
def CascadeHeadCertificate {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) : Prop :=
  (∑ χ : Fin m → Fin k, cascadeChainValue θ h χ) ≠ 0

/-- `K03B.E.def-cascade-certificate.S/P`: all first-layer heads have a cascade chain. -/
def CascadeCertificate {m k d : Nat} (θ : Params (m + 1) k d) : Prop :=
  ∀ h : Fin k, CascadeHeadCertificate θ h

/-! ## Headwise anchor certificate rows -/

/-- Same-layer separation heads, excluding the anchor head. -/
abbrev AnchorSeparationHead (k : Nat) (h : Fin k) : Type :=
  {a : Fin k // a ≠ h}

/-- Certificate rows for a positive tail of depth `m+1`.

The row families are: anchor row, same-layer separation rows, deeper level
rows, and the final transversality row. -/
abbrev AnchorRow (m k : Nat) (h : Fin k) : Type :=
  (PUnit ⊕ AnchorSeparationHead k h) ⊕ ((Fin m × Fin k) ⊕ PUnit)

/-- The anchor row index. -/
def anchorRowAnchor {m k : Nat} (h : Fin k) : AnchorRow m k h :=
  Sum.inl (Sum.inl PUnit.unit)

/-- A same-layer separation row index. -/
def anchorRowSeparation {m k : Nat} {h : Fin k} (a : AnchorSeparationHead k h) :
    AnchorRow m k h :=
  Sum.inl (Sum.inr a)

/-- A deeper level row index. -/
def anchorRowLevel {m k : Nat} (h : Fin k) (j : Fin m) (b : Fin k) :
    AnchorRow m k h :=
  Sum.inr (Sum.inl (j, b))

/-- The transversality row index. -/
def anchorRowTransversality {m k : Nat} (h : Fin k) : AnchorRow m k h :=
  Sum.inr (Sum.inr PUnit.unit)

/-- The dialed first-stream vector `w^h(t) = (I + (1-t)V_0h) w0`. -/
noncomputable def headDialW {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (t : ℝ) (w0 : Vec d) : Vec d :=
  (1 + (1 - t) • valueMatrix θ 0 h) *ᵥ w0

/-- Collapsed product `C_(n-1) ... C_0` through the first `n` layers. -/
noncomputable def collapsePrefix {m k d : Nat} (θ : Params (m + 1) k d)
    (n : Nat) : Matrix (Fin d) (Fin d) ℝ :=
  cornerCPrefix θ n

/-- Gradient of a certificate row with respect to `v`. -/
noncomputable def anchorRowGradient {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (t : ℝ) (w0 : Vec d) :
    AnchorRow m k h → Vec d
  | Sum.inl (Sum.inl _) =>
      (attentionMatrix θ 0 h)ᵀ *ᵥ w0
  | Sum.inl (Sum.inr a) =>
      (attentionMatrix θ 0 a.1)ᵀ *ᵥ w0
  | Sum.inr (Sum.inl jb) =>
      let j : Fin m := jb.1
      let b : Fin k := jb.2
      (collapsePrefix θ (j.val + 1))ᵀ *ᵥ
        ((attentionMatrix θ (laterLayer j) b)ᵀ *ᵥ headDialW θ h t w0)
  | Sum.inr (Sum.inr _) =>
      -((attentionMatrix θ 0 h)ᵀ *ᵥ (valueMatrix θ 0 h *ᵥ w0))

/-- Constant term of a certificate row as an affine function of `v`. -/
noncomputable def anchorRowConstant {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (t : ℝ) (w0 : Vec d) :
    AnchorRow m k h → ℝ
  | Sum.inl (Sum.inl _) => 0
  | Sum.inl (Sum.inr _) => 0
  | Sum.inr (Sum.inl jb) =>
      let j : Fin m := jb.1
      let b : Fin k := jb.2
      matrixBilin (attentionMatrix θ (laterLayer j) b)
        (headDialW θ h t w0)
        ((collapsePrefix θ (j.val + 1) - 1 -
            (1 - t) • valueMatrix θ 0 h) *ᵥ w0)
  | Sum.inr (Sum.inr _) =>
      matrixBilin (attentionMatrix θ 0 h) w0 (valueMatrix θ 0 h *ᵥ w0)

/-- Certificate row value, packaged explicitly as an affine function of `v`. -/
noncomputable def anchorRowValue {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (t : ℝ) (w0 : Vec d) (row : AnchorRow m k h)
    (v : Vec d) : ℝ :=
  anchorRowGradient θ h t w0 row ⬝ᵥ v + anchorRowConstant θ h t w0 row

/-- The `d x rows` matrix whose columns are the certificate-row gradients. -/
noncomputable def anchorGradientMatrix {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (t : ℝ) (w0 : Vec d) :
    Matrix (Fin d) (AnchorRow m k h) ℝ :=
  Matrix.of fun i row => anchorRowGradient θ h t w0 row i

/-- Gram determinant of the headwise anchor gradient matrix. -/
noncomputable def anchorGramDet {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (t : ℝ) (w0 : Vec d) : ℝ :=
  let G := anchorGradientMatrix θ h t w0
  ((Gᵀ * G) : Matrix (AnchorRow m k h) (AnchorRow m k h) ℝ).det

/-- Right-hand side used when pinning the affine certificate rows. -/
def anchorRowTarget {m k : Nat} (h : Fin k) : AnchorRow m k h → ℝ
  | Sum.inl (Sum.inl _) => 0
  | Sum.inl (Sum.inr _) => 1
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr _) => 1

@[simp]
theorem anchorRowTarget_anchor {m k : Nat} (h : Fin k) :
    anchorRowTarget (m := m) h (anchorRowAnchor h) = 0 :=
  rfl

@[simp]
theorem anchorRowTarget_separation {m k : Nat} {h : Fin k}
    (a : AnchorSeparationHead k h) :
    anchorRowTarget (m := m) h (anchorRowSeparation a) = 1 :=
  rfl

@[simp]
theorem anchorRowTarget_level {m k : Nat} (h : Fin k) (j : Fin m) (b : Fin k) :
    anchorRowTarget h (anchorRowLevel h j b) = 1 :=
  rfl

@[simp]
theorem anchorRowTarget_transversality {m k : Nat} (h : Fin k) :
    anchorRowTarget (m := m) h (anchorRowTransversality h) = 1 :=
  rfl

/-- Headwise anchor certificate, represented by one nonzero Gram evaluation. -/
def AnchorHeadCertificate {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) : Prop :=
  ∃ t : ℝ, ∃ w0 : Vec d, anchorGramDet θ h t w0 ≠ 0

/-- `K03B.E.def-anchor-certificate.S/P`: all first-layer heads have a certificate. -/
def AnchorCertificate {m k d : Nat} (θ : Params (m + 1) k d) : Prop :=
  ∀ h : Fin k, AnchorHeadCertificate θ h

/-! ## Easy row-affine API -/

/-- `K03B.E.lem-row-affine.S/P`: each certificate row is affine in `v`. -/
theorem lem_row_affine {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (t : ℝ) (w0 : Vec d) (row : AnchorRow m k h) :
    ∃ g : Vec d, ∃ c : ℝ, ∀ v : Vec d,
      anchorRowValue θ h t w0 row v = g ⬝ᵥ v + c := by
  exact ⟨anchorRowGradient θ h t w0 row,
    anchorRowConstant θ h t w0 row, fun _ => rfl⟩

@[simp]
theorem anchorRowValue_eq_gradient_add_constant {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (t : ℝ) (w0 : Vec d)
    (row : AnchorRow m k h) (v : Vec d) :
    anchorRowValue θ h t w0 row v =
      anchorRowGradient θ h t w0 row ⬝ᵥ v +
        anchorRowConstant θ h t w0 row :=
  rfl

@[simp]
theorem anchorRowConstant_anchor {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (t : ℝ) (w0 : Vec d) :
    anchorRowConstant θ h t w0 (anchorRowAnchor h) = 0 :=
  rfl

@[simp]
theorem anchorRowConstant_separation {m k d : Nat} (θ : Params (m + 1) k d)
    {h : Fin k} (t : ℝ) (w0 : Vec d) (a : AnchorSeparationHead k h) :
    anchorRowConstant θ h t w0 (anchorRowSeparation a) = 0 :=
  rfl

@[simp]
theorem anchorRowGradient_anchor {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (t : ℝ) (w0 : Vec d) :
    anchorRowGradient θ h t w0 (anchorRowAnchor h) =
      (attentionMatrix θ 0 h)ᵀ *ᵥ w0 :=
  rfl

@[simp]
theorem anchorRowGradient_separation {m k d : Nat} (θ : Params (m + 1) k d)
    {h : Fin k} (t : ℝ) (w0 : Vec d) (a : AnchorSeparationHead k h) :
    anchorRowGradient θ h t w0 (anchorRowSeparation a) =
      (attentionMatrix θ 0 a.1)ᵀ *ᵥ w0 :=
  rfl

@[simp]
theorem anchorRowGradient_level {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (t : ℝ) (w0 : Vec d) (j : Fin m) (b : Fin k) :
    anchorRowGradient θ h t w0 (anchorRowLevel h j b) =
      (collapsePrefix θ (j.val + 1))ᵀ *ᵥ
        ((attentionMatrix θ (laterLayer j) b)ᵀ *ᵥ headDialW θ h t w0) :=
  rfl

@[simp]
theorem anchorRowGradient_transversality {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (t : ℝ) (w0 : Vec d) :
    anchorRowGradient θ h t w0 (anchorRowTransversality h) =
      -((attentionMatrix θ 0 h)ᵀ *ᵥ (valueMatrix θ 0 h *ᵥ w0)) :=
  rfl

/-- Multiplying by the transpose of the gradient matrix evaluates all row gradients. -/
theorem anchorGradientMatrix_transpose_mulVec {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (t : ℝ) (w0 v : Vec d) :
    (anchorGradientMatrix θ h t w0)ᵀ *ᵥ v =
      fun row => anchorRowGradient θ h t w0 row ⬝ᵥ v := by
  ext row
  simp [anchorGradientMatrix, Matrix.mulVec, dotProduct]

/-- A nonzero Gram determinant makes the affine certificate-row map surjective. -/
theorem exists_anchor_row_pinning_of_anchorGramDet_ne_zero {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (t : ℝ) (w0 : Vec d)
    (hgram : anchorGramDet θ h t w0 ≠ 0) :
    ∃ v : Vec d, ∀ row : AnchorRow m k h,
      anchorRowValue θ h t w0 row v = anchorRowTarget h row := by
  classical
  let G := anchorGradientMatrix θ h t w0
  let A : Matrix (AnchorRow m k h) (AnchorRow m k h) ℝ := Gᵀ * G
  let y : AnchorRow m k h → ℝ :=
    fun row => anchorRowTarget h row - anchorRowConstant θ h t w0 row
  let vsol : Vec d := G *ᵥ (A⁻¹ *ᵥ y)
  refine ⟨vsol, ?_⟩
  have hA_det : A.det ≠ 0 := by
    simpa [anchorGramDet, G, A] using hgram
  have hA_unit : IsUnit A.det := isUnit_iff_ne_zero.mpr hA_det
  have hA_solve : A *ᵥ (A⁻¹ *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hA_unit, Matrix.one_mulVec]
  have hG_solve : Gᵀ *ᵥ vsol = y := by
    change Gᵀ *ᵥ (G *ᵥ (A⁻¹ *ᵥ y)) = y
    rw [Matrix.mulVec_mulVec]
    exact hA_solve
  intro row
  calc
    anchorRowValue θ h t w0 row vsol
        = anchorRowGradient θ h t w0 row ⬝ᵥ vsol +
            anchorRowConstant θ h t w0 row := rfl
    _ = (Gᵀ *ᵥ vsol) row + anchorRowConstant θ h t w0 row := by
      rw [anchorGradientMatrix_transpose_mulVec]
    _ = y row + anchorRowConstant θ h t w0 row := by
      rw [hG_solve]
    _ = anchorRowTarget h row := by
      simp [y]

/-! ## Auxiliary polynomial form of the anchor Gram determinant -/

/-- Auxiliary variables for the anchor certificate: the scalar `t` and the vector `w0`. -/
abbrev AnchorAuxVar (d : Nat) : Type :=
  PUnit ⊕ Fin d

/-- Polynomial ring in the anchor auxiliary variables `(t,w0)`. -/
abbrev AnchorAuxPoly (d : Nat) : Type :=
  MvPolynomial (AnchorAuxVar d) ℝ

/-- The polynomial coordinate for `t`. -/
noncomputable def anchorAuxT {d : Nat} : AnchorAuxPoly d :=
  MvPolynomial.X (Sum.inl PUnit.unit)

/-- The polynomial coordinate for `w0`. -/
noncomputable def anchorAuxW0 {d : Nat} : Fin d → AnchorAuxPoly d :=
  fun i => MvPolynomial.X (Sum.inr i)

/-- Evaluation assignment for the anchor auxiliary variables. -/
def anchorAuxEval {d : Nat} (t : ℝ) (w0 : Vec d) : AnchorAuxVar d → ℝ
  | Sum.inl _ => t
  | Sum.inr i => w0 i

@[simp]
theorem anchorAuxEval_t {d : Nat} (t : ℝ) (w0 : Vec d) :
    MvPolynomial.eval (anchorAuxEval t w0) (anchorAuxT : AnchorAuxPoly d) = t := by
  simp [anchorAuxT, anchorAuxEval]

@[simp]
theorem anchorAuxEval_w0 {d : Nat} (t : ℝ) (w0 : Vec d) (i : Fin d) :
    MvPolynomial.eval (anchorAuxEval t w0) (anchorAuxW0 i) = w0 i := by
  simp [anchorAuxW0, anchorAuxEval]

/-- Cast a real matrix into the anchor auxiliary polynomial ring. -/
noncomputable def realMatrixToAnchorAuxPoly {d : Nat}
    (M : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) (AnchorAuxPoly d) :=
  M.map (MvPolynomial.C : ℝ →+* AnchorAuxPoly d)

@[simp]
theorem realMatrixToAnchorAuxPoly_apply {d : Nat}
    (M : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) :
    realMatrixToAnchorAuxPoly M i j = MvPolynomial.C (M i j) :=
  rfl

@[simp]
theorem map_realMatrixToAnchorAuxPoly {d : Nat}
    (ρ : AnchorAuxVar d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    (realMatrixToAnchorAuxPoly M).map (MvPolynomial.eval ρ) = M := by
  ext i j
  simp [realMatrixToAnchorAuxPoly]

/-- Evaluation commutes with polynomial matrix-vector multiplication. -/
theorem anchorAux_eval_mulVec {d : Nat} {m n : Type*} [Fintype n]
    (ρ : AnchorAuxVar d → ℝ) (M : Matrix m n (AnchorAuxPoly d))
    (v : n → AnchorAuxPoly d) :
    (fun i => MvPolynomial.eval ρ (M.mulVec v i)) =
      (M.map (MvPolynomial.eval ρ)).mulVec
        (fun j => MvPolynomial.eval ρ (v j)) := by
  funext i
  simp [Matrix.mulVec, dotProduct]

/-- Polynomial matrix `I + (1-t)V_0h` used in the dialed first stream. -/
noncomputable def anchorHeadDialMatrixPoly {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) :
    Matrix (Fin d) (Fin d) (AnchorAuxPoly d) :=
  realMatrixToAnchorAuxPoly (1 : Matrix (Fin d) (Fin d) ℝ) +
    ((MvPolynomial.C (1 : ℝ) : AnchorAuxPoly d) - (anchorAuxT : AnchorAuxPoly d)) •
      realMatrixToAnchorAuxPoly (valueMatrix θ 0 h)

@[simp]
theorem map_anchorHeadDialMatrixPoly {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (t : ℝ) (w0 : Vec d) :
    (anchorHeadDialMatrixPoly θ h).map (MvPolynomial.eval (anchorAuxEval t w0)) =
      (1 : Matrix (Fin d) (Fin d) ℝ) + (1 - t) • valueMatrix θ 0 h := by
  ext i j
  simp [anchorHeadDialMatrixPoly, Matrix.add_apply, Matrix.smul_apply]

/-- Polynomial vector for `w^h(t) = (I + (1-t)V_0h)w0`. -/
noncomputable def anchorHeadDialWPoly {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) : Fin d → AnchorAuxPoly d :=
  anchorHeadDialMatrixPoly θ h *ᵥ anchorAuxW0

@[simp]
theorem eval_anchorHeadDialWPoly {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (t : ℝ) (w0 : Vec d) :
    (fun i =>
      MvPolynomial.eval (anchorAuxEval t w0) (anchorHeadDialWPoly θ h i)) =
      headDialW θ h t w0 := by
  rw [anchorHeadDialWPoly, headDialW]
  trans
      ((anchorHeadDialMatrixPoly θ h).map
          (MvPolynomial.eval (anchorAuxEval t w0))).mulVec
        (fun i => MvPolynomial.eval (anchorAuxEval t w0) (anchorAuxW0 i))
  · exact anchorAux_eval_mulVec (anchorAuxEval t w0)
      (anchorHeadDialMatrixPoly θ h) anchorAuxW0
  · rw [map_anchorHeadDialMatrixPoly]
    simp

/-- Polynomial version of a certificate-row gradient in the auxiliary variables. -/
noncomputable def anchorRowGradientPoly {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) :
    AnchorRow m k h → Fin d → AnchorAuxPoly d
  | Sum.inl (Sum.inl _) =>
      realMatrixToAnchorAuxPoly ((attentionMatrix θ 0 h)ᵀ) *ᵥ anchorAuxW0
  | Sum.inl (Sum.inr a) =>
      realMatrixToAnchorAuxPoly ((attentionMatrix θ 0 a.1)ᵀ) *ᵥ anchorAuxW0
  | Sum.inr (Sum.inl jb) =>
      let j : Fin m := jb.1
      let b : Fin k := jb.2
      realMatrixToAnchorAuxPoly
        ((collapsePrefix θ (j.val + 1))ᵀ * (attentionMatrix θ (laterLayer j) b)ᵀ) *ᵥ
          anchorHeadDialWPoly θ h
  | Sum.inr (Sum.inr _) =>
      -(realMatrixToAnchorAuxPoly ((attentionMatrix θ 0 h)ᵀ * valueMatrix θ 0 h) *ᵥ
        anchorAuxW0)

@[simp]
theorem eval_anchorRowGradientPoly {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (t : ℝ) (w0 : Vec d)
    (row : AnchorRow m k h) :
    (fun i =>
      MvPolynomial.eval (anchorAuxEval t w0) (anchorRowGradientPoly θ h row i)) =
      anchorRowGradient θ h t w0 row := by
  classical
  cases row with
  | inl row0 =>
      cases row0 with
      | inl u =>
          cases u
          rw [anchorRowGradientPoly, anchorRowGradient]
          trans
              ((realMatrixToAnchorAuxPoly ((attentionMatrix θ 0 h)ᵀ)).map
                  (MvPolynomial.eval (anchorAuxEval t w0))).mulVec
                (fun i => MvPolynomial.eval (anchorAuxEval t w0) (anchorAuxW0 i))
          · exact anchorAux_eval_mulVec (anchorAuxEval t w0)
              (realMatrixToAnchorAuxPoly ((attentionMatrix θ 0 h)ᵀ)) anchorAuxW0
          · simp
      | inr a =>
          rw [anchorRowGradientPoly, anchorRowGradient]
          trans
              ((realMatrixToAnchorAuxPoly ((attentionMatrix θ 0 a.1)ᵀ)).map
                  (MvPolynomial.eval (anchorAuxEval t w0))).mulVec
                (fun i => MvPolynomial.eval (anchorAuxEval t w0) (anchorAuxW0 i))
          · exact anchorAux_eval_mulVec (anchorAuxEval t w0)
              (realMatrixToAnchorAuxPoly ((attentionMatrix θ 0 a.1)ᵀ)) anchorAuxW0
          · simp
  | inr row1 =>
      cases row1 with
      | inl jb =>
          rcases jb with ⟨j, b⟩
          rw [anchorRowGradientPoly, anchorRowGradient]
          trans
              ((realMatrixToAnchorAuxPoly
                  ((collapsePrefix θ (j.val + 1))ᵀ *
                    (attentionMatrix θ (laterLayer j) b)ᵀ)).map
                  (MvPolynomial.eval (anchorAuxEval t w0))).mulVec
                (fun i =>
                  MvPolynomial.eval (anchorAuxEval t w0) (anchorHeadDialWPoly θ h i))
          · exact anchorAux_eval_mulVec (anchorAuxEval t w0)
              (realMatrixToAnchorAuxPoly
                ((collapsePrefix θ (j.val + 1))ᵀ *
                  (attentionMatrix θ (laterLayer j) b)ᵀ))
              (anchorHeadDialWPoly θ h)
          · rw [map_realMatrixToAnchorAuxPoly, eval_anchorHeadDialWPoly]
            rw [Matrix.mulVec_mulVec]
      | inr u =>
          cases u
          rw [anchorRowGradientPoly, anchorRowGradient]
          trans
              -(((realMatrixToAnchorAuxPoly
                    ((attentionMatrix θ 0 h)ᵀ * valueMatrix θ 0 h)).map
                    (MvPolynomial.eval (anchorAuxEval t w0))).mulVec
                  (fun i => MvPolynomial.eval (anchorAuxEval t w0) (anchorAuxW0 i)))
          · funext i
            simp [Matrix.mulVec, dotProduct]
          · rw [map_realMatrixToAnchorAuxPoly]
            simp [Matrix.mulVec_mulVec]

/-- Polynomial matrix whose columns are the auxiliary-polynomial gradients. -/
noncomputable def anchorGradientPolyMatrix {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) :
    Matrix (Fin d) (AnchorRow m k h) (AnchorAuxPoly d) :=
  Matrix.of fun i row => anchorRowGradientPoly θ h row i

@[simp]
theorem map_anchorGradientPolyMatrix {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (t : ℝ) (w0 : Vec d) :
    (anchorGradientPolyMatrix θ h).map (MvPolynomial.eval (anchorAuxEval t w0)) =
      anchorGradientMatrix θ h t w0 := by
  ext i row
  exact congr_fun (eval_anchorRowGradientPoly θ h t w0 row) i

/-- The anchor Gram determinant as an actual polynomial in `(t,w0)`. -/
noncomputable def anchorGramPoly {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) : AnchorAuxPoly d :=
  let G := anchorGradientPolyMatrix θ h
  ((Gᵀ * G) : Matrix (AnchorRow m k h) (AnchorRow m k h) (AnchorAuxPoly d)).det

@[simp]
theorem eval_anchorGramPoly {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (t : ℝ) (w0 : Vec d) :
    MvPolynomial.eval (anchorAuxEval t w0) (anchorGramPoly θ h) =
      anchorGramDet θ h t w0 := by
  let evalHom := MvPolynomial.eval (anchorAuxEval t w0)
  let Gp := anchorGradientPolyMatrix θ h
  change evalHom (((Gpᵀ * Gp) :
    Matrix (AnchorRow m k h) (AnchorRow m k h) (AnchorAuxPoly d)).det) =
      anchorGramDet θ h t w0
  rw [RingHom.map_det]
  change (((Gpᵀ * Gp).map evalHom) :
    Matrix (AnchorRow m k h) (AnchorRow m k h) ℝ).det =
      anchorGramDet θ h t w0
  rw [Matrix.map_mul, Matrix.transpose_map,
    map_anchorGradientPolyMatrix]
  rfl

/-- Over `ℝ`, a multivariate polynomial is nonzero iff some real evaluation is nonzero. -/
theorem mvPolynomial_ne_zero_iff_exists_eval_ne_zero {ι : Type*}
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

/-- The existential certificate and the coefficient-polynomial certificate are equivalent. -/
theorem anchorHeadCertificate_iff_anchorGramPoly_ne_zero {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) :
    AnchorHeadCertificate θ h ↔ anchorGramPoly θ h ≠ 0 := by
  constructor
  · rintro ⟨t, w0, hgram⟩ hzero
    exact hgram (by rw [← eval_anchorGramPoly θ h t w0, hzero, map_zero])
  · intro hpoly
    rcases (mvPolynomial_ne_zero_iff_exists_eval_ne_zero (anchorGramPoly θ h)).mp hpoly with
      ⟨ρ, hρ⟩
    refine ⟨ρ (Sum.inl PUnit.unit), fun i => ρ (Sum.inr i), ?_⟩
    have hEval :
        anchorAuxEval (ρ (Sum.inl PUnit.unit)) (fun i => ρ (Sum.inr i)) = ρ := by
      funext x
      cases x with
      | inl u => cases u; rfl
      | inr i => rfl
    rw [← eval_anchorGramPoly θ h (ρ (Sum.inl PUnit.unit)) (fun i => ρ (Sum.inr i))]
    simpa [hEval] using hρ

/-- A nonzero anchor Gram polynomial has a nonzero evaluation with `t` in `(0,1)`. -/
theorem exists_anchorGramDet_ne_zero_with_t_mem_Ioo_of_anchorGramPoly_ne_zero
    {m k d : Nat} (θ : Params (m + 1) k d) (h : Fin k)
    (hpoly : anchorGramPoly θ h ≠ 0) :
    ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∃ w0 : Vec d, anchorGramDet θ h t w0 ≠ 0 := by
  classical
  by_contra hnone
  let s : AnchorAuxVar d → Set ℝ
    | Sum.inl _ => Set.Ioo (0 : ℝ) 1
    | Sum.inr _ => Set.univ
  have hs : ∀ x : AnchorAuxVar d, (s x).Infinite := by
    intro x
    cases x with
    | inl u =>
        cases u
        exact Set.Ioo_infinite zero_lt_one
    | inr _ =>
        exact Set.infinite_univ
  have hzero_on :
      ∀ ρ : AnchorAuxVar d → ℝ, ρ ∈ Set.pi Set.univ s →
        MvPolynomial.eval ρ (anchorGramPoly θ h) =
          MvPolynomial.eval ρ (0 : AnchorAuxPoly d) := by
    intro ρ hρ
    by_contra hρ_ne
    have ht : ρ (Sum.inl PUnit.unit) ∈ Set.Ioo (0 : ℝ) 1 := by
      exact hρ (Sum.inl PUnit.unit) trivial
    have hEval :
        anchorAuxEval (ρ (Sum.inl PUnit.unit)) (fun i => ρ (Sum.inr i)) = ρ := by
      funext x
      cases x with
      | inl u => cases u; rfl
      | inr i => rfl
    have hgram :
        anchorGramDet θ h (ρ (Sum.inl PUnit.unit)) (fun i => ρ (Sum.inr i)) ≠ 0 := by
      rw [← eval_anchorGramPoly θ h (ρ (Sum.inl PUnit.unit)) (fun i => ρ (Sum.inr i))]
      simpa [hEval] using hρ_ne
    exact hnone ⟨ρ (Sum.inl PUnit.unit), ht, ⟨fun i => ρ (Sum.inr i), hgram⟩⟩
  apply hpoly
  exact MvPolynomial.funext_set s hs hzero_on

/-! ## Sign-region helper definitions and easy consequences -/

/-- Dial covector `pi'_h(w,v) = A_h^T w - A_h v`. -/
noncomputable def dialCovector {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (w v : Vec d) : Vec d :=
  (attentionMatrix θ 0 h)ᵀ *ᵥ w - attentionMatrix θ 0 h *ᵥ v

/-- Dial transversality scalar `pi'_h(w,v)^T V_h w`. -/
noncomputable def dialTransversality {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (w v : Vec d) : ℝ :=
  dialCovector θ h w v ⬝ᵥ (valueMatrix θ 0 h *ᵥ w)

/-- A point of the sign-region slab, written as `((w,v),t)`. -/
abbrev SignRegionPoint (d : Nat) : Type :=
  (Vec d × Vec d) × ℝ

/-- The deleted-coordinate index set for the solved quadric chart. -/
abbrev DeletedCoord (d : Nat) (pivot : Fin d) : Type :=
  {i : Fin d // i ≠ pivot}

/-- Vectors with the pivot coordinate removed. -/
abbrev DeletedVec (d : Nat) (pivot : Fin d) : Type :=
  DeletedCoord d pivot → ℝ

/-- Chart source coordinates `(w, \hat v, t)`. -/
abbrev SignRegionChartInput (d : Nat) (pivot : Fin d) : Type :=
  (Vec d × DeletedVec d pivot) × ℝ

/-- Delete the pivot coordinate from `v`. -/
def signRegionHat {d : Nat} (pivot : Fin d) (v : Vec d) : DeletedVec d pivot :=
  fun i => v i.1

/-- The pivot denominator `κ_h(w) = ((A_h)^T w)_pivot`. -/
noncomputable def signRegionKappa {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (pivot : Fin d) (w : Vec d) : ℝ :=
  ((attentionMatrix θ 0 h)ᵀ *ᵥ w) pivot

/-- The solved-coordinate chart map `γ_h(w,\hat v)`.  It is used only on the
open denominator-nonzero domain, but is total as a Lean function. -/
noncomputable def signRegionGamma {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (pivot : Fin d) (w : Vec d) (vhat : DeletedVec d pivot) :
    Vec d :=
  fun i =>
    if hi : i = pivot then
      - (signRegionKappa θ h pivot w)⁻¹ *
        ∑ j : DeletedCoord d pivot,
          ((attentionMatrix θ 0 h)ᵀ *ᵥ w) j.1 * vhat j
    else
      vhat ⟨i, hi⟩

/-- The chart domain `W_*^h × R^(d-1) × R`. -/
def signRegionChartDomain {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (pivot : Fin d) : Set (SignRegionChartInput d pivot) :=
  {x | signRegionKappa θ h pivot x.1.1 ≠ 0}

/-- The TeX chart map `Φ_h(w,\hat v,t) = (w, γ_h(w,\hat v), t)`. -/
noncomputable def signRegionChart {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (pivot : Fin d) :
    SignRegionChartInput d pivot → SignRegionPoint d :=
  fun x => ((x.1.1, signRegionGamma θ h pivot x.1.1 x.1.2), x.2)

/-- Projection inverse to the solved-coordinate chart on its image. -/
def signRegionProjection {d : Nat} (pivot : Fin d) :
    SignRegionPoint d → SignRegionChartInput d pivot :=
  fun p => ((p.1.1, signRegionHat pivot p.1.2), p.2)

/-- The bilinear quadric slab `Q_h × (0,1)`. -/
def signRegionSlab {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) : Set (SignRegionPoint d) :=
  {p | matrixBilin (attentionMatrix θ 0 h) p.1.1 p.1.2 = 0 ∧
    p.2 ∈ Set.Ioo (0 : ℝ) 1}

/-- The chart-source product box `B(w0,ρ) × B(vhat0,ρ) × (t0-ρ,t0+ρ)`. -/
def signRegionSourceBox {d : Nat} (pivot : Fin d)
    (w0 : Vec d) (vhat0 : DeletedVec d pivot) (t0 ρ : ℝ) :
    Set (SignRegionChartInput d pivot) :=
  {x | x.1.1 ∈ Metric.ball w0 ρ ∧
    x.1.2 ∈ Metric.ball vhat0 ρ ∧
      x.2 ∈ Set.Ioo (t0 - ρ) (t0 + ρ)}

/-- The corresponding ambient box in `(w,v,t)` coordinates. -/
def signRegionAmbientBox {d : Nat} (pivot : Fin d)
    (w0 : Vec d) (vhat0 : DeletedVec d pivot) (t0 ρ : ℝ) :
    Set (SignRegionPoint d) :=
  {p | p.1.1 ∈ Metric.ball w0 ρ ∧
    signRegionHat pivot p.1.2 ∈ Metric.ball vhat0 ρ ∧
      p.2 ∈ Set.Ioo (t0 - ρ) (t0 + ρ)}

/-- Same-layer separation value for a non-anchor first-layer head. -/
noncomputable def signRegionSeparationValue {m k d : Nat}
    (θ : Params (m + 1) k d) {h : Fin k} (a : AnchorSeparationHead k h)
    (p : SignRegionPoint d) : ℝ :=
  matrixBilin (attentionMatrix θ 0 a.1) p.1.1 p.1.2

/-- Deeper-level label value, with `j : Fin m` representing TeX layer `2 + j`. -/
noncomputable def signRegionLevelValue {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (j : Fin m) (b : Fin k)
    (p : SignRegionPoint d) : ℝ :=
  anchorRowValue θ h p.2 p.1.1 (anchorRowLevel h j b) p.1.2

/-- Transversality value on a sign-region point. -/
noncomputable def signRegionTransversalityValue {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (p : SignRegionPoint d) : ℝ :=
  dialTransversality θ h p.1.1 p.1.2

/-- The finite family of strict sign inequalities in TeX Lemma `sign-region`:
same-layer separation, deeper-level labels, and transversality. -/
abbrev SignRegionStrictIndex (m k : Nat) (h : Fin k) : Type :=
  (AnchorSeparationHead k h ⊕ (Fin m × Fin k)) ⊕ PUnit

/-- Value of one strict sign inequality. -/
noncomputable def signRegionStrictValue {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) :
    SignRegionStrictIndex m k h → SignRegionPoint d → ℝ
  | Sum.inl (Sum.inl a), p => signRegionSeparationValue θ a p
  | Sum.inl (Sum.inr jb), p => signRegionLevelValue θ h jb.1 jb.2 p
  | Sum.inr _, p => signRegionTransversalityValue θ h p

/-- The open strict-sign locus used before shrinking to the chart box. -/
def signRegionStrictPositiveSet {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) : Set (SignRegionPoint d) :=
  {p | ∀ idx : SignRegionStrictIndex m k h, 0 < signRegionStrictValue θ h idx p}

/-- A finite family of strict inequalities cuts out an open set. -/
theorem isOpen_finite_strictPositiveSet {X ι : Type*} [TopologicalSpace X]
    [Finite ι] (F : ι → X → ℝ) (hF : ∀ i, Continuous (F i)) :
    IsOpen {x : X | ∀ i : ι, 0 < F i x} := by
  have hset :
      {x : X | ∀ i : ι, 0 < F i x} =
        ⋂ i : ι, {x : X | F i x ∈ Set.Ioi (0 : ℝ)} := by
    ext x
    simp
  rw [hset]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_Ioi.preimage (hF i)

/-- Strict inequalities persist in a neighborhood of a point where they all hold. -/
theorem finite_strictPositiveSet_mem_nhds {X ι : Type*} [TopologicalSpace X]
    [Finite ι] (F : ι → X → ℝ) (hF : ∀ i, Continuous (F i))
    {x0 : X} (hx0 : ∀ i : ι, 0 < F i x0) :
    {x : X | ∀ i : ι, 0 < F i x} ∈ nhds x0 :=
  (isOpen_finite_strictPositiveSet F hF).mem_nhds hx0

/-- The local matrix bilinear form is continuous under continuous probe streams. -/
theorem continuous_matrixBilin {X : Type*} [TopologicalSpace X] {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) {w v : X → Vec d}
    (hw : Continuous w) (hv : Continuous v) :
    Continuous fun x => matrixBilin A (w x) (v x) := by
  unfold matrixBilin
  fun_prop

/-- Same-layer separation values are continuous in `(w,v,t)`. -/
theorem continuous_signRegionSeparationValue {m k d : Nat}
    (θ : Params (m + 1) k d) {h : Fin k}
    (a : AnchorSeparationHead k h) :
    Continuous (signRegionSeparationValue θ a) := by
  unfold signRegionSeparationValue matrixBilin
  fun_prop

/-- Deeper-level sign-region values are continuous in `(w,v,t)`. -/
theorem continuous_signRegionLevelValue {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (j : Fin m) (b : Fin k) :
    Continuous (signRegionLevelValue θ h j b) := by
  change Continuous fun p : SignRegionPoint d =>
    anchorRowGradient θ h p.2 p.1.1 (anchorRowLevel h j b) ⬝ᵥ p.1.2 +
      anchorRowConstant θ h p.2 p.1.1 (anchorRowLevel h j b)
  have hlin :
      Continuous fun p : SignRegionPoint d =>
        anchorRowGradient θ h p.2 p.1.1 (anchorRowLevel h j b) ⬝ᵥ p.1.2 := by
    unfold anchorRowGradient headDialW collapsePrefix
    fun_prop
  have hconst :
      Continuous fun p : SignRegionPoint d =>
        anchorRowConstant θ h p.2 p.1.1 (anchorRowLevel h j b) := by
    change Continuous fun p : SignRegionPoint d =>
      matrixBilin (attentionMatrix θ (laterLayer j) b)
        (headDialW θ h p.2 p.1.1)
        ((collapsePrefix θ (j.val + 1) - 1 - (1 - p.2) • valueMatrix θ 0 h) *ᵥ p.1.1)
    apply continuous_matrixBilin
    · unfold headDialW
      fun_prop
    · unfold collapsePrefix
      fun_prop
  exact hlin.add hconst

/-- Dial transversality is continuous in `(w,v,t)`. -/
theorem continuous_signRegionTransversalityValue {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) :
    Continuous (signRegionTransversalityValue θ h) := by
  unfold signRegionTransversalityValue dialTransversality dialCovector
  fun_prop

/-- Every strict sign-region inequality is continuous. -/
theorem continuous_signRegionStrictValue {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k)
    (idx : SignRegionStrictIndex m k h) :
    Continuous (signRegionStrictValue θ h idx) := by
  cases idx with
  | inl idx0 =>
      cases idx0 with
      | inl a =>
          simpa [signRegionStrictValue] using
            continuous_signRegionSeparationValue θ a
      | inr jb =>
          rcases jb with ⟨j, b⟩
          simpa [signRegionStrictValue] using
            continuous_signRegionLevelValue θ h j b
  | inr u =>
      cases u
      simpa [signRegionStrictValue] using
        continuous_signRegionTransversalityValue θ h

/-- The strict-positive sign-region locus is open. -/
theorem isOpen_signRegionStrictPositiveSet {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) :
    IsOpen (signRegionStrictPositiveSet θ h) :=
  isOpen_finite_strictPositiveSet (signRegionStrictValue θ h)
    (continuous_signRegionStrictValue θ h)

/-- Deleting the pivot coordinate after `γ_h` recovers the chart coordinate. -/
@[simp]
theorem signRegionHat_gamma {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (pivot : Fin d) (w : Vec d) (vhat : DeletedVec d pivot) :
    signRegionHat pivot (signRegionGamma θ h pivot w vhat) = vhat := by
  funext i
  simp [signRegionHat, signRegionGamma, i.2]

/-- The projection is a left inverse for the chart map. -/
@[simp]
theorem signRegionProjection_chart {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (pivot : Fin d) (x : SignRegionChartInput d pivot) :
    signRegionProjection pivot (signRegionChart θ h pivot x) = x := by
  rcases x with ⟨⟨w, vhat⟩, t⟩
  simp [signRegionProjection, signRegionChart]

/-- The bilinear anchor equation can be read as a dot product against
`A^T w`; this is the algebraic form used by the solved-coordinate chart. -/
theorem matrixBilin_eq_transpose_mulVec_dot {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (w v : Vec d) :
    matrixBilin A w v = (Aᵀ *ᵥ w) ⬝ᵥ v := by
  simp only [matrixBilin, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  conv_lhs =>
    arg 2
    intro i
    rw [Finset.mul_sum]
  conv_rhs =>
    arg 2
    intro j
    rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The solved-coordinate chart lands on the anchor quadric whenever its
denominator is nonzero. -/
theorem matrixBilin_signRegionGamma_eq_zero {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (pivot : Fin d)
    (w : Vec d) (vhat : DeletedVec d pivot)
    (hκ : signRegionKappa θ h pivot w ≠ 0) :
    matrixBilin (attentionMatrix θ 0 h) w
      (signRegionGamma θ h pivot w vhat) = 0 := by
  let c : Vec d := (attentionMatrix θ 0 h)ᵀ *ᵥ w
  let S : ℝ := ∑ j : DeletedCoord d pivot, c j.1 * vhat j
  rw [matrixBilin_eq_transpose_mulVec_dot]
  change c ⬝ᵥ signRegionGamma θ h pivot w vhat = 0
  rw [dotProduct]
  rw [Fintype.sum_eq_add_sum_subtype_ne
    (fun i : Fin d => c i * signRegionGamma θ h pivot w vhat i) pivot]
  have hsum :
      (∑ x : DeletedCoord d pivot,
        c x.1 * signRegionGamma θ h pivot w vhat x.1) = S := by
    apply Finset.sum_congr rfl
    intro x _
    simp [signRegionGamma, x.2]
  have hpivot :
      signRegionGamma θ h pivot w vhat pivot = - (c pivot)⁻¹ * S := by
    simp [S, c, signRegionGamma, signRegionKappa]
  rw [hsum, hpivot]
  have hc : c pivot ≠ 0 := by
    simpa [c, signRegionKappa] using hκ
  field_simp [hc]
  ring_nf

/-- On the anchor quadric, the solved-coordinate chart recovers the original
`v` from its deleted-coordinate projection. -/
theorem signRegionGamma_hat_eq_of_matrixBilin_eq_zero {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (pivot : Fin d)
    (w v : Vec d) (hκ : signRegionKappa θ h pivot w ≠ 0)
    (hquad : matrixBilin (attentionMatrix θ 0 h) w v = 0) :
    signRegionGamma θ h pivot w (signRegionHat pivot v) = v := by
  ext i
  by_cases hi : i = pivot
  · subst i
    rw [signRegionGamma]
    simp only [signRegionHat]
    have hdot :
        ((attentionMatrix θ 0 h)ᵀ *ᵥ w) ⬝ᵥ v = 0 := by
      rw [matrixBilin_eq_transpose_mulVec_dot] at hquad
      exact hquad
    rw [dotProduct] at hdot
    rw [Fintype.sum_eq_add_sum_subtype_ne
      (fun i : Fin d => ((attentionMatrix θ 0 h)ᵀ *ᵥ w) i * v i) pivot] at hdot
    have hsum :
        (∑ j : DeletedCoord d pivot,
          ((attentionMatrix θ 0 h)ᵀ *ᵥ w) j.1 * v j.1) =
            -(((attentionMatrix θ 0 h)ᵀ *ᵥ w) pivot * v pivot) := by
      linarith
    rw [hsum]
    simp [signRegionKappa] at hκ ⊢
    field_simp [hκ]
  · simp [signRegionGamma, signRegionHat, hi]

/-- The chart map sends denominator-nonzero source points with `t ∈ (0,1)` into
the bilinear sign-region slab. -/
theorem signRegionChart_mem_slab {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (pivot : Fin d)
    (x : SignRegionChartInput d pivot)
    (hxκ : signRegionKappa θ h pivot x.1.1 ≠ 0)
    (ht : x.2 ∈ Set.Ioo (0 : ℝ) 1) :
    signRegionChart θ h pivot x ∈ signRegionSlab θ h := by
  rcases x with ⟨⟨w, vhat⟩, t⟩
  exact ⟨matrixBilin_signRegionGamma_eq_zero θ h pivot w vhat hxκ, ht⟩

/-- A slab point in the denominator-nonzero chart domain is fixed by charting
its deleted-coordinate projection. -/
theorem signRegionChart_projection_eq_of_mem_slab {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (pivot : Fin d)
    (p : SignRegionPoint d)
    (hκ : signRegionKappa θ h pivot p.1.1 ≠ 0)
    (hquad : matrixBilin (attentionMatrix θ 0 h) p.1.1 p.1.2 = 0) :
    signRegionChart θ h pivot (signRegionProjection pivot p) = p := by
  rcases p with ⟨⟨w, v⟩, t⟩
  simp [signRegionChart, signRegionProjection,
    signRegionGamma_hat_eq_of_matrixBilin_eq_zero θ h pivot w v hκ hquad]

/-- Under the standard denominator and interval containments, the chart image
of the source box is exactly the relatively open ambient box cut out inside
the anchor quadric slab. -/
theorem signRegionChart_image_sourceBox_eq_slab_inter_ambientBox {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (pivot : Fin d)
    (w0 : Vec d) (vhat0 : DeletedVec d pivot) (t0 ρ : ℝ)
    (hball :
      Metric.ball w0 ρ ⊆ {w | signRegionKappa θ h pivot w ≠ 0})
    (hinterval :
      Set.Ioo (t0 - ρ) (t0 + ρ) ⊆ Set.Ioo (0 : ℝ) 1) :
    signRegionChart θ h pivot ''
        signRegionSourceBox pivot w0 vhat0 t0 ρ =
      signRegionSlab θ h ∩
        signRegionAmbientBox pivot w0 vhat0 t0 ρ := by
  ext p
  constructor
  · rintro ⟨x, hxbox, rfl⟩
    rcases x with ⟨⟨w, vhat⟩, t⟩
    rcases hxbox with ⟨hw, hvhat, ht⟩
    refine ⟨?_, ?_⟩
    · exact signRegionChart_mem_slab θ h pivot ((w, vhat), t)
        (hball hw) (hinterval ht)
    · refine ⟨hw, ?_, ht⟩
      simpa [signRegionChart] using hvhat
  · rintro ⟨hslab, hamb⟩
    rcases p with ⟨⟨w, v⟩, t⟩
    rcases hslab with ⟨hquad, _ht01⟩
    rcases hamb with ⟨hw, hvhat, htbox⟩
    refine ⟨((w, signRegionHat pivot v), t), ?_, ?_⟩
    · exact ⟨hw, hvhat, htbox⟩
    · exact signRegionChart_projection_eq_of_mem_slab θ h pivot ((w, v), t)
        (hball hw) hquad

/-- Coordinate deletion is continuous. -/
theorem continuous_signRegionHat {d : Nat} (pivot : Fin d) :
    Continuous (signRegionHat pivot : Vec d → DeletedVec d pivot) := by
  rw [continuous_pi_iff]
  intro i
  exact continuous_apply i.1

/-- The chart projection `(w,v,t) ↦ (w,\hat v,t)` is continuous. -/
theorem continuous_signRegionProjection {d : Nat} (pivot : Fin d) :
    Continuous (signRegionProjection pivot :
      SignRegionPoint d → SignRegionChartInput d pivot) := by
  have hw : Continuous fun p : SignRegionPoint d => p.1.1 :=
    (continuous_fst : Continuous fun q : Vec d × Vec d => q.1).comp
      (continuous_fst : Continuous fun p : SignRegionPoint d => p.1)
  have hv : Continuous fun p : SignRegionPoint d => p.1.2 :=
    (continuous_snd : Continuous fun q : Vec d × Vec d => q.2).comp
      (continuous_fst : Continuous fun p : SignRegionPoint d => p.1)
  have ht : Continuous fun p : SignRegionPoint d => p.2 :=
    continuous_snd
  change Continuous fun p : SignRegionPoint d =>
    ((p.1.1, signRegionHat pivot p.1.2), p.2)
  exact (hw.prodMk ((continuous_signRegionHat pivot).comp hv)).prodMk ht

/-- The pivot denominator is continuous in `w`. -/
theorem continuous_signRegionKappa {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (pivot : Fin d) :
    Continuous fun w : Vec d => signRegionKappa θ h pivot w := by
  simpa [signRegionKappa, Matrix.mulVec, dotProduct] using
    (continuous_finsetSum Finset.univ fun j _ =>
      (continuous_const :
        Continuous fun _ : Vec d => ((attentionMatrix θ 0 h)ᵀ) pivot j).mul
          (continuous_apply j))

/-- The denominator-nonzero chart domain is open. -/
theorem isOpen_signRegionChartDomain {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (pivot : Fin d) :
    IsOpen (signRegionChartDomain θ h pivot) := by
  have hw : Continuous fun x : SignRegionChartInput d pivot => x.1.1 :=
    (continuous_fst : Continuous fun q : Vec d × DeletedVec d pivot => q.1).comp
      (continuous_fst : Continuous fun x : SignRegionChartInput d pivot => x.1)
  simpa [signRegionChartDomain] using
    isOpen_ne.preimage ((continuous_signRegionKappa θ h pivot).comp hw)

/-- The chart-source box is open. -/
theorem isOpen_signRegionSourceBox {d : Nat} (pivot : Fin d)
    (w0 : Vec d) (vhat0 : DeletedVec d pivot) (t0 ρ : ℝ) :
    IsOpen (signRegionSourceBox pivot w0 vhat0 t0 ρ) := by
  have hw : Continuous fun x : SignRegionChartInput d pivot => x.1.1 :=
    (continuous_fst : Continuous fun q : Vec d × DeletedVec d pivot => q.1).comp
      (continuous_fst : Continuous fun x : SignRegionChartInput d pivot => x.1)
  have hv : Continuous fun x : SignRegionChartInput d pivot => x.1.2 :=
    (continuous_snd : Continuous fun q : Vec d × DeletedVec d pivot => q.2).comp
      (continuous_fst : Continuous fun x : SignRegionChartInput d pivot => x.1)
  have ht : Continuous fun x : SignRegionChartInput d pivot => x.2 :=
    continuous_snd
  have hwb : IsOpen {x : SignRegionChartInput d pivot | x.1.1 ∈ Metric.ball w0 ρ} :=
    Metric.isOpen_ball.preimage hw
  have hvb : IsOpen {x : SignRegionChartInput d pivot | x.1.2 ∈ Metric.ball vhat0 ρ} :=
    Metric.isOpen_ball.preimage hv
  have htb :
      IsOpen {x : SignRegionChartInput d pivot | x.2 ∈ Set.Ioo (t0 - ρ) (t0 + ρ)} :=
    isOpen_Ioo.preimage ht
  simpa [signRegionSourceBox, Set.setOf_and] using hwb.inter (hvb.inter htb)

/-- The ambient box is open in `(w,v,t)` coordinates. -/
theorem isOpen_signRegionAmbientBox {d : Nat} (pivot : Fin d)
    (w0 : Vec d) (vhat0 : DeletedVec d pivot) (t0 ρ : ℝ) :
    IsOpen (signRegionAmbientBox pivot w0 vhat0 t0 ρ) := by
  have hw : Continuous fun p : SignRegionPoint d => p.1.1 :=
    (continuous_fst : Continuous fun q : Vec d × Vec d => q.1).comp
      (continuous_fst : Continuous fun p : SignRegionPoint d => p.1)
  have hv : Continuous fun p : SignRegionPoint d => p.1.2 :=
    (continuous_snd : Continuous fun q : Vec d × Vec d => q.2).comp
      (continuous_fst : Continuous fun p : SignRegionPoint d => p.1)
  have ht : Continuous fun p : SignRegionPoint d => p.2 :=
    continuous_snd
  have hwb : IsOpen {p : SignRegionPoint d | p.1.1 ∈ Metric.ball w0 ρ} :=
    Metric.isOpen_ball.preimage hw
  have hvb :
      IsOpen {p : SignRegionPoint d |
        signRegionHat pivot p.1.2 ∈ Metric.ball vhat0 ρ} :=
    Metric.isOpen_ball.preimage ((continuous_signRegionHat pivot).comp hv)
  have htb :
      IsOpen {p : SignRegionPoint d | p.2 ∈ Set.Ioo (t0 - ρ) (t0 + ρ)} :=
    isOpen_Ioo.preimage ht
  simpa [signRegionAmbientBox, Set.setOf_and] using hwb.inter (hvb.inter htb)

/-- The `w` coordinate projection from chart-source coordinates is analytic. -/
theorem analyticOnNhd_signRegionChart_w {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (pivot : Fin d) :
    AnalyticOnNhd ℝ (fun x : SignRegionChartInput d pivot => x.1.1)
      (signRegionChartDomain θ h pivot) := by
  let F : SignRegionChartInput d pivot →L[ℝ] Vec d × DeletedVec d pivot :=
    ContinuousLinearMap.fst ℝ (Vec d × DeletedVec d pivot) ℝ
  let G : (Vec d × DeletedVec d pivot) →L[ℝ] Vec d :=
    ContinuousLinearMap.fst ℝ (Vec d) (DeletedVec d pivot)
  change AnalyticOnNhd ℝ (⇑(G.comp F)) (signRegionChartDomain θ h pivot)
  exact (G.comp F).analyticOnNhd (signRegionChartDomain θ h pivot)

/-- One coordinate of the `w` projection is analytic on the chart domain. -/
theorem analyticOnNhd_signRegionChart_w_coord {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (pivot : Fin d)
    (i : Fin d) :
    AnalyticOnNhd ℝ (fun x : SignRegionChartInput d pivot => x.1.1 i)
      (signRegionChartDomain θ h pivot) := by
  have hw := analyticOnNhd_signRegionChart_w θ h pivot
  let P : Vec d →L[ℝ] ℝ := ContinuousLinearMap.proj i
  simpa [P, Function.comp] using P.comp_analyticOnNhd hw

/-- One deleted `v` coordinate is analytic on the chart domain. -/
theorem analyticOnNhd_signRegionChart_vhat_coord {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (pivot : Fin d)
    (i : DeletedCoord d pivot) :
    AnalyticOnNhd ℝ (fun x : SignRegionChartInput d pivot => x.1.2 i)
      (signRegionChartDomain θ h pivot) := by
  let F : SignRegionChartInput d pivot →L[ℝ] Vec d × DeletedVec d pivot :=
    ContinuousLinearMap.fst ℝ (Vec d × DeletedVec d pivot) ℝ
  let G : (Vec d × DeletedVec d pivot) →L[ℝ] DeletedVec d pivot :=
    ContinuousLinearMap.snd ℝ (Vec d) (DeletedVec d pivot)
  let P : DeletedVec d pivot →L[ℝ] ℝ := ContinuousLinearMap.proj i
  change AnalyticOnNhd ℝ (⇑(P.comp (G.comp F)))
    (signRegionChartDomain θ h pivot)
  exact (P.comp (G.comp F)).analyticOnNhd (signRegionChartDomain θ h pivot)

/-- The `t` coordinate projection from chart-source coordinates is analytic. -/
theorem analyticOnNhd_signRegionChart_t {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (pivot : Fin d) :
    AnalyticOnNhd ℝ (fun x : SignRegionChartInput d pivot => x.2)
      (signRegionChartDomain θ h pivot) := by
  let F : SignRegionChartInput d pivot →L[ℝ] ℝ :=
    ContinuousLinearMap.snd ℝ (Vec d × DeletedVec d pivot) ℝ
  change AnalyticOnNhd ℝ (⇑F) (signRegionChartDomain θ h pivot)
  exact F.analyticOnNhd (signRegionChartDomain θ h pivot)

/-- A coordinate of `A_h^T w` is analytic in chart-source coordinates. -/
theorem analyticOnNhd_signRegionTransposeMulVecCoord {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (pivot coord : Fin d) :
    AnalyticOnNhd ℝ
      (fun x : SignRegionChartInput d pivot =>
        ((attentionMatrix θ 0 h)ᵀ *ᵥ x.1.1) coord)
      (signRegionChartDomain θ h pivot) := by
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.analyticOnNhd_fun_sum
  intro j _hj
  have hjcoord :=
    analyticOnNhd_signRegionChart_w_coord θ h pivot j
  simpa [Matrix.transpose_apply] using
    ((analyticOnNhd_const
      (v := ((attentionMatrix θ 0 h)ᵀ) coord j)).mul hjcoord)

/-- The chart denominator is analytic on the denominator-nonzero chart domain. -/
theorem analyticOnNhd_signRegionKappaOnChartDomain {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (pivot : Fin d) :
    AnalyticOnNhd ℝ
      (fun x : SignRegionChartInput d pivot =>
        signRegionKappa θ h pivot x.1.1)
      (signRegionChartDomain θ h pivot) := by
  simpa [signRegionKappa] using
    analyticOnNhd_signRegionTransposeMulVecCoord θ h pivot pivot

/-- One coordinate of the solved-coordinate map `γ_h` is analytic on the chart domain. -/
theorem analyticOnNhd_signRegionGamma_coord {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (pivot i : Fin d) :
    AnalyticOnNhd ℝ
      (fun x : SignRegionChartInput d pivot =>
        signRegionGamma θ h pivot x.1.1 x.1.2 i)
      (signRegionChartDomain θ h pivot) := by
  by_cases hi : i = pivot
  · subst i
    have hk_inv :
        AnalyticOnNhd ℝ
          (fun x : SignRegionChartInput d pivot =>
            (signRegionKappa θ h pivot x.1.1)⁻¹)
          (signRegionChartDomain θ h pivot) := by
      apply AnalyticOnNhd.inv
      · exact analyticOnNhd_signRegionKappaOnChartDomain θ h pivot
      · intro x hx
        simpa [signRegionChartDomain] using hx
    have hsum :
        AnalyticOnNhd ℝ
          (fun x : SignRegionChartInput d pivot =>
            ∑ j : DeletedCoord d pivot,
              ((attentionMatrix θ 0 h)ᵀ *ᵥ x.1.1) j.1 * x.1.2 j)
          (signRegionChartDomain θ h pivot) := by
      apply Finset.analyticOnNhd_fun_sum
      intro j _hj
      exact
        (analyticOnNhd_signRegionTransposeMulVecCoord θ h pivot j.1).mul
          (analyticOnNhd_signRegionChart_vhat_coord θ h pivot j)
    simpa [signRegionGamma] using (hk_inv.mul hsum).neg
  · simpa [signRegionGamma, hi] using
      analyticOnNhd_signRegionChart_vhat_coord θ h pivot ⟨i, hi⟩

/-- The solved-coordinate map `γ_h` is analytic on the chart domain. -/
theorem analyticOnNhd_signRegionGamma {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (pivot : Fin d) :
    AnalyticOnNhd ℝ
      (fun x : SignRegionChartInput d pivot =>
        signRegionGamma θ h pivot x.1.1 x.1.2)
      (signRegionChartDomain θ h pivot) := by
  apply AnalyticOnNhd.pi
  intro i
  exact analyticOnNhd_signRegionGamma_coord θ h pivot i

/-- The full solved-coordinate chart is analytic on its denominator-nonzero domain. -/
theorem analyticOnNhd_signRegionChart {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (pivot : Fin d) :
    AnalyticOnNhd ℝ (signRegionChart θ h pivot)
      (signRegionChartDomain θ h pivot) := by
  change AnalyticOnNhd ℝ
    (fun x : SignRegionChartInput d pivot =>
      ((x.1.1, signRegionGamma θ h pivot x.1.1 x.1.2), x.2))
    (signRegionChartDomain θ h pivot)
  exact ((analyticOnNhd_signRegionChart_w θ h pivot).prod
    (analyticOnNhd_signRegionGamma θ h pivot)).prod
      (analyticOnNhd_signRegionChart_t θ h pivot)

/-- The full solved-coordinate chart is continuous on its denominator-nonzero domain. -/
theorem continuousOn_signRegionChart {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (pivot : Fin d) :
    ContinuousOn (signRegionChart θ h pivot)
      (signRegionChartDomain θ h pivot) :=
  (analyticOnNhd_signRegionChart θ h pivot).continuousOn

/-- A source product box is contained in the ambient metric ball with the same center
whenever its radius is bounded by the ambient ball radius. -/
theorem signRegionSourceBox_subset_ball {d : Nat} (pivot : Fin d)
    (w0 : Vec d) (vhat0 : DeletedVec d pivot) (t0 ρ ε : ℝ)
    (hρε : ρ ≤ ε) :
    signRegionSourceBox pivot w0 vhat0 t0 ρ ⊆
      Metric.ball ((w0, vhat0), t0) ε := by
  intro x hx
  rcases hx with ⟨hw, hv, ht⟩
  rw [Metric.mem_ball]
  rw [Prod.dist_eq, Prod.dist_eq, max_lt_iff, max_lt_iff]
  rw [Metric.mem_ball] at hw hv
  have ht' : dist x.2 t0 < ρ := by
    rw [Real.dist_eq]
    rcases ht with ⟨hlt, htu⟩
    rw [abs_lt]
    constructor <;> linarith
  exact ⟨⟨lt_of_lt_of_le hw hρε, lt_of_lt_of_le hv hρε⟩,
    lt_of_lt_of_le ht' hρε⟩

/-- The chart-source box is convex. -/
theorem convex_signRegionSourceBox {d : Nat} (pivot : Fin d)
    (w0 : Vec d) (vhat0 : DeletedVec d pivot) (t0 ρ : ℝ) :
    Convex ℝ (signRegionSourceBox pivot w0 vhat0 t0 ρ) := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨hxw, hxv, hxt⟩
  rcases hy with ⟨hyw, hyv, hyt⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa using (convex_ball w0 ρ hxw hyw ha hb hab)
  · simpa using (convex_ball vhat0 ρ hxv hyv ha hb hab)
  · simpa using
      (convex_Ioo (𝕜 := ℝ) (t0 - ρ) (t0 + ρ) hxt hyt ha hb hab)

/-- The solved-coordinate chart is bijective from a source box onto its image. -/
theorem signRegionChart_bijOn_sourceBox {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (pivot : Fin d)
    (w0 : Vec d) (vhat0 : DeletedVec d pivot) (t0 ρ : ℝ) :
    Set.BijOn (signRegionChart θ h pivot)
      (signRegionSourceBox pivot w0 vhat0 t0 ρ)
      (signRegionChart θ h pivot ''
        signRegionSourceBox pivot w0 vhat0 t0 ρ) := by
  refine ⟨?maps, ?inj, ?surj⟩
  · intro x hx
    exact ⟨x, hx, rfl⟩
  · intro x _hx y _hy hxy
    have hproj := congrArg (signRegionProjection pivot) hxy
    simpa using hproj
  · intro p hp
    exact hp

/-- On a chart image, projecting to source coordinates and charting back fixes the point. -/
theorem signRegionChart_projection_inverse_on_image {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (pivot : Fin d)
    (source : Set (SignRegionChartInput d pivot)) :
    ∀ p ∈ signRegionChart θ h pivot '' source,
      signRegionChart θ h pivot (signRegionProjection pivot p) = p := by
  rintro p ⟨x, _hx, rfl⟩
  simp

/-- The certificate transversality row is exactly the dial transversality scalar. -/
theorem anchorRowValue_transversality_eq_dialTransversality {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (t : ℝ) (w v : Vec d) :
    anchorRowValue θ h t w (anchorRowTransversality h) v =
      dialTransversality θ h w v := by
  let A := attentionMatrix θ 0 h
  let V := valueMatrix θ 0 h
  have hconst : w ⬝ᵥ (A * V) *ᵥ w = Aᵀ *ᵥ w ⬝ᵥ V *ᵥ w := by
    calc
      w ⬝ᵥ (A * V) *ᵥ w = w ⬝ᵥ A *ᵥ (V *ᵥ w) := by
        rw [← Matrix.mulVec_mulVec]
      _ = (V *ᵥ w) ⬝ᵥ Aᵀ *ᵥ w :=
        (Matrix.dotProduct_transpose_mulVec (A := A) (x := V *ᵥ w) (y := w)).symm
      _ = Aᵀ *ᵥ w ⬝ᵥ V *ᵥ w := dotProduct_comm _ _
  have hlin : ((Aᵀ * V) *ᵥ w) ⬝ᵥ v = A *ᵥ v ⬝ᵥ V *ᵥ w := by
    calc
      ((Aᵀ * V) *ᵥ w) ⬝ᵥ v = (Aᵀ *ᵥ (V *ᵥ w)) ⬝ᵥ v := by
        rw [← Matrix.mulVec_mulVec]
      _ = v ⬝ᵥ Aᵀ *ᵥ (V *ᵥ w) := dotProduct_comm _ _
      _ = (V *ᵥ w) ⬝ᵥ A *ᵥ v :=
        Matrix.dotProduct_transpose_mulVec (A := A) (x := v) (y := V *ᵥ w)
      _ = A *ᵥ v ⬝ᵥ V *ᵥ w := dotProduct_comm _ _
  simp [anchorRowValue, anchorRowGradient, anchorRowConstant, anchorRowTransversality,
    dialTransversality, dialCovector, matrixBilin, A, V, hconst, hlin]
  ring

/-- The anchor row is the defining bilinear quadric equation. -/
theorem anchorRowValue_anchor_eq_matrixBilin {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (t : ℝ) (w v : Vec d) :
    anchorRowValue θ h t w (anchorRowAnchor h) v =
      matrixBilin (attentionMatrix θ 0 h) w v := by
  let A := attentionMatrix θ 0 h
  have hdot :
      (Aᵀ *ᵥ w) ⬝ᵥ v = w ⬝ᵥ A *ᵥ v := by
    calc
      (Aᵀ *ᵥ w) ⬝ᵥ v = v ⬝ᵥ Aᵀ *ᵥ w := dotProduct_comm _ _
      _ = w ⬝ᵥ A *ᵥ v :=
        Matrix.dotProduct_transpose_mulVec (A := A) (x := v) (y := w)
  simp [anchorRowValue, anchorRowGradient, anchorRowConstant, anchorRowAnchor,
    matrixBilin, A, hdot]

/-- A same-layer separation row is the corresponding first-layer bilinear form. -/
theorem anchorRowValue_separation_eq_matrixBilin {m k d : Nat}
    (θ : Params (m + 1) k d) {h : Fin k} (a : AnchorSeparationHead k h)
    (t : ℝ) (w v : Vec d) :
    anchorRowValue θ h t w (anchorRowSeparation a) v =
      matrixBilin (attentionMatrix θ 0 a.1) w v := by
  let A := attentionMatrix θ 0 a.1
  have hdot :
      (Aᵀ *ᵥ w) ⬝ᵥ v = w ⬝ᵥ A *ᵥ v := by
    calc
      (Aᵀ *ᵥ w) ⬝ᵥ v = v ⬝ᵥ Aᵀ *ᵥ w := dotProduct_comm _ _
      _ = w ⬝ᵥ A *ᵥ v :=
        Matrix.dotProduct_transpose_mulVec (A := A) (x := v) (y := w)
  simp [anchorRowValue, anchorRowGradient, anchorRowConstant, anchorRowSeparation,
    matrixBilin, A, hdot]

/-- Supporting helper for `K03B.E.lem-sign-region`: positive transversality gives
the nonzero factors consumed by later dial and quadric arguments. -/
theorem lem_sign_region_transversality_nonzero {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (w v : Vec d)
    (hpos : 0 < dialTransversality θ h w v) :
    dialCovector θ h w v ≠ 0 ∧
      valueMatrix θ 0 h *ᵥ w ≠ 0 ∧
        w ≠ 0 := by
  have htrans_ne : dialTransversality θ h w v ≠ 0 := ne_of_gt hpos
  have hcov : dialCovector θ h w v ≠ 0 := by
    intro hzero
    exact htrans_ne (by simp [dialTransversality, hzero])
  have hvalue : valueMatrix θ 0 h *ᵥ w ≠ 0 := by
    intro hzero
    exact htrans_ne (by simp [dialTransversality, hzero])
  have hw : w ≠ 0 := by
    intro hzero
    exact hvalue (by simp [hzero])
  exact ⟨hcov, hvalue, hw⟩

/-- A nonzero Gram determinant makes every gradient column nonzero. -/
theorem anchorRowGradient_ne_zero_of_anchorGramDet_ne_zero {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (t : ℝ) (w0 : Vec d)
    (hgram : anchorGramDet θ h t w0 ≠ 0) (row : AnchorRow m k h) :
    anchorRowGradient θ h t w0 row ≠ 0 := by
  classical
  intro hrow
  let G := anchorGradientMatrix θ h t w0
  have hcol : ∀ i : AnchorRow m k h, (Gᵀ * G) i row = 0 := by
    intro i
    simp [G, anchorGradientMatrix, Matrix.mul_apply, hrow]
  have hdet : ((Gᵀ * G) : Matrix (AnchorRow m k h) (AnchorRow m k h) ℝ).det = 0 :=
    Matrix.det_eq_zero_of_column_eq_zero row hcol
  exact hgram (by simpa [anchorGramDet, G] using hdet)

/-- A nonzero Gram determinant supplies the pivot index used by the quadric chart. -/
theorem exists_signRegionPivot_of_anchorGramDet_ne_zero {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (t : ℝ) (w0 : Vec d)
    (hgram : anchorGramDet θ h t w0 ≠ 0) :
    ∃ pivot : Fin d, signRegionKappa θ h pivot w0 ≠ 0 := by
  classical
  have hgrad :
      ((attentionMatrix θ 0 h)ᵀ *ᵥ w0) ≠ 0 := by
    simpa [anchorRowGradient_anchor] using
      anchorRowGradient_ne_zero_of_anchorGramDet_ne_zero θ h t w0 hgram
        (anchorRowAnchor h)
  by_contra hnone
  apply hgrad
  funext i
  by_contra hi
  exact hnone ⟨i, by simpa [signRegionKappa] using hi⟩

/-- Center data produced by the algebraic part of the sign-region proof. -/
structure SignRegionCenterData {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) where
  t : ℝ
  t_mem_Ioo : t ∈ Set.Ioo (0 : ℝ) 1
  w0 : Vec d
  v : Vec d
  gram_ne_zero : anchorGramDet θ h t w0 ≠ 0
  pinned_rows : ∀ row : AnchorRow m k h,
    anchorRowValue θ h t w0 row v = anchorRowTarget h row
  transversality_eq_one : dialTransversality θ h w0 v = 1
  transversality_pos : 0 < dialTransversality θ h w0 v
  transversality_nonzero :
    dialCovector θ h w0 v ≠ 0 ∧
      valueMatrix θ 0 h *ᵥ w0 ≠ 0 ∧
        w0 ≠ 0

/-- The center point associated to algebraic sign-region center data. -/
def SignRegionCenterData.point {m k d : Nat} {θ : Params (m + 1) k d}
    {h : Fin k} (D : SignRegionCenterData θ h) : SignRegionPoint d :=
  ((D.w0, D.v), D.t)

namespace SignRegionCenterData

theorem anchor_eq_zero {m k d : Nat} {θ : Params (m + 1) k d}
    {h : Fin k} (D : SignRegionCenterData θ h) :
    matrixBilin (attentionMatrix θ 0 h) D.w0 D.v = 0 := by
  have hrow := D.pinned_rows (anchorRowAnchor h)
  rwa [anchorRowValue_anchor_eq_matrixBilin] at hrow

theorem separation_eq_one {m k d : Nat} {θ : Params (m + 1) k d}
    {h : Fin k} (D : SignRegionCenterData θ h)
    (a : AnchorSeparationHead k h) :
    signRegionSeparationValue θ a D.point = 1 := by
  have hrow := D.pinned_rows (anchorRowSeparation a)
  exact (by
    simpa [signRegionSeparationValue, point] using
      (anchorRowValue_separation_eq_matrixBilin θ a D.t D.w0 D.v).symm.trans hrow)

theorem level_eq_one {m k d : Nat} {θ : Params (m + 1) k d}
    {h : Fin k} (D : SignRegionCenterData θ h) (j : Fin m) (b : Fin k) :
    signRegionLevelValue θ h j b D.point = 1 := by
  have hrow := D.pinned_rows (anchorRowLevel h j b)
  simpa [signRegionLevelValue, point] using hrow

theorem transversality_value_eq_one {m k d : Nat}
    {θ : Params (m + 1) k d} {h : Fin k}
    (D : SignRegionCenterData θ h) :
    signRegionTransversalityValue θ h D.point = 1 := by
  simpa [signRegionTransversalityValue, point] using D.transversality_eq_one

theorem point_mem_slab {m k d : Nat} {θ : Params (m + 1) k d}
    {h : Fin k} (D : SignRegionCenterData θ h) :
    D.point ∈ signRegionSlab θ h := by
  exact ⟨D.anchor_eq_zero, D.t_mem_Ioo⟩

theorem point_mem_strictPositiveSet {m k d : Nat}
    {θ : Params (m + 1) k d} {h : Fin k}
    (D : SignRegionCenterData θ h) :
    D.point ∈ signRegionStrictPositiveSet θ h := by
  intro idx
  cases idx with
  | inl idx0 =>
      cases idx0 with
      | inl a =>
          rw [signRegionStrictValue, D.separation_eq_one a]
          norm_num
      | inr jb =>
          rcases jb with ⟨j, b⟩
          rw [signRegionStrictValue, D.level_eq_one j b]
          norm_num
  | inr u =>
      cases u
      rw [signRegionStrictValue, D.transversality_value_eq_one]
      norm_num

/-- The strict-positive sign-region locus is a neighborhood of the algebraic
center data point. -/
theorem strictPositiveSet_mem_nhds {m k d : Nat}
    {θ : Params (m + 1) k d} {h : Fin k}
    (D : SignRegionCenterData θ h) :
    signRegionStrictPositiveSet θ h ∈ nhds D.point :=
  (isOpen_signRegionStrictPositiveSet θ h).mem_nhds D.point_mem_strictPositiveSet

theorem exists_pivot {m k d : Nat} {θ : Params (m + 1) k d}
    {h : Fin k} (D : SignRegionCenterData θ h) :
    ∃ pivot : Fin d, signRegionKappa θ h pivot D.w0 ≠ 0 :=
  exists_signRegionPivot_of_anchorGramDet_ne_zero θ h D.t D.w0 D.gram_ne_zero

end SignRegionCenterData

/-- Full data asserted by the TeX sign-region lemma after choosing one first-layer head.

This structure intentionally includes the topological/sign information from
Lemma `sign-region`: the solved-coordinate chart, the source box, the ambient
identity as a relatively open quadric slab, connectedness, pinned center data,
same-layer separation, deeper-level labels, and transversality positivity. -/
structure SignRegionData {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) where
  center : SignRegionCenterData θ h
  pivot : Fin d
  pivot_nonzero : signRegionKappa θ h pivot center.w0 ≠ 0
  vHat : DeletedVec d pivot
  vHat_eq : vHat = signRegionHat pivot center.v
  rho : ℝ
  rho_pos : 0 < rho
  interval_subset_Ioo :
    Set.Ioo (center.t - rho) (center.t + rho) ⊆ Set.Ioo (0 : ℝ) 1
  w_ball_subset_chart :
    Metric.ball center.w0 rho ⊆ {w | signRegionKappa θ h pivot w ≠ 0}
  region : Set (SignRegionPoint d)
  region_eq_chart_image :
    region = signRegionChart θ h pivot ''
      signRegionSourceBox pivot center.w0 vHat center.t rho
  ambient_identity :
    region = signRegionSlab θ h ∩
      signRegionAmbientBox pivot center.w0 vHat center.t rho
  center_chart :
    signRegionChart θ h pivot ((center.w0, vHat), center.t) =
      center.point
  center_mem_region : center.point ∈ region
  chart_continuousOn :
    ContinuousOn (signRegionChart θ h pivot) (signRegionChartDomain θ h pivot)
  chart_analyticOnNhd :
    AnalyticOnNhd ℝ (signRegionChart θ h pivot) (signRegionChartDomain θ h pivot)
  chart_bijective :
    Set.BijOn (signRegionChart θ h pivot)
      (signRegionSourceBox pivot center.w0 vHat center.t rho) region
  chart_projection_inverse :
    ∀ p ∈ region, signRegionChart θ h pivot (signRegionProjection pivot p) = p
  source_convex :
    Convex ℝ (signRegionSourceBox pivot center.w0 vHat center.t rho)
  region_connected : IsPreconnected region
  separation_positive :
    ∀ p ∈ region, ∀ a : AnchorSeparationHead k h,
      0 < signRegionSeparationValue θ a p
  level_positive :
    ∀ p ∈ region, ∀ j : Fin m, ∀ b : Fin k,
      0 < signRegionLevelValue θ h j b p
  transversality_positive :
    ∀ p ∈ region, 0 < signRegionTransversalityValue θ h p

namespace SignRegionData

theorem nonempty {m k d : Nat} {θ : Params (m + 1) k d}
    {h : Fin k} (D : SignRegionData θ h) :
    D.region.Nonempty :=
  ⟨D.center.point, D.center_mem_region⟩

theorem region_subset_slab {m k d : Nat} {θ : Params (m + 1) k d}
    {h : Fin k} (D : SignRegionData θ h) :
    D.region ⊆ signRegionSlab θ h := by
  rw [D.ambient_identity]
  exact Set.inter_subset_left

theorem relatively_open {m k d : Nat} {θ : Params (m + 1) k d}
    {h : Fin k} (D : SignRegionData θ h) :
    ∃ O : Set (SignRegionPoint d), IsOpen O ∧ D.region = signRegionSlab θ h ∩ O := by
  refine ⟨signRegionAmbientBox D.pivot D.center.w0 D.vHat D.center.t D.rho,
    isOpen_signRegionAmbientBox D.pivot D.center.w0 D.vHat D.center.t D.rho, ?_⟩
  exact D.ambient_identity

theorem transversality_nonzero {m k d : Nat} {θ : Params (m + 1) k d}
    {h : Fin k} (D : SignRegionData θ h) {p : SignRegionPoint d}
    (hp : p ∈ D.region) :
    dialCovector θ h p.1.1 p.1.2 ≠ 0 ∧
      valueMatrix θ 0 h *ᵥ p.1.1 ≠ 0 ∧
        p.1.1 ≠ 0 := by
  exact lem_sign_region_transversality_nonzero θ h p.1.1 p.1.2
    (by simpa [signRegionTransversalityValue] using D.transversality_positive p hp)

end SignRegionData

/-- `K03B.E.lem-sign-region.S`: proposition-valued representation of the full
TeX sign-region lemma/API. -/
def lem_sign_region_statement {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) : Prop :=
  AnchorHeadCertificate θ h → Nonempty (SignRegionData θ h)

/-- Algebraic center construction for the sign-region lemma.

This proves the non-topological core of the sign-region lemma: the certificate
selects `t in (0,1)`, a base vector, and a probe vector whose affine rows are
pinned to the TeX target values; in particular the dial transversality is `1`.
-/
theorem exists_signRegionCenterData_of_anchorHeadCertificate {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k)
    (hcert : AnchorHeadCertificate θ h) :
    Nonempty (SignRegionCenterData θ h) := by
  classical
  have hpoly : anchorGramPoly θ h ≠ 0 :=
    (anchorHeadCertificate_iff_anchorGramPoly_ne_zero θ h).mp hcert
  rcases exists_anchorGramDet_ne_zero_with_t_mem_Ioo_of_anchorGramPoly_ne_zero
      θ h hpoly with ⟨t, ht, w0, hgram⟩
  rcases exists_anchor_row_pinning_of_anchorGramDet_ne_zero θ h t w0 hgram with
    ⟨v, hpinned⟩
  have htrans_eq_one : dialTransversality θ h w0 v = 1 := by
    rw [← anchorRowValue_transversality_eq_dialTransversality θ h t w0 v]
    simpa using hpinned (anchorRowTransversality h)
  have htrans_pos : 0 < dialTransversality θ h w0 v := by
    rw [htrans_eq_one]
    norm_num
  exact ⟨
    { t := t
      t_mem_Ioo := ht
      w0 := w0
      v := v
      gram_ne_zero := hgram
      pinned_rows := hpinned
      transversality_eq_one := htrans_eq_one
      transversality_pos := htrans_pos
      transversality_nonzero :=
        lem_sign_region_transversality_nonzero θ h w0 v htrans_pos }⟩

/-- `K03B.E.lem-sign-region.P`: proof of the proposition-valued sign-region
statement from the headwise anchor certificate. -/
theorem lem_sign_region_statement_proof {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) :
    lem_sign_region_statement θ h := by
  classical
  intro hcert
  rcases exists_signRegionCenterData_of_anchorHeadCertificate θ h hcert with ⟨D⟩
  rcases D.exists_pivot with ⟨pivot, hpivot⟩
  let vHat : DeletedVec d pivot := signRegionHat pivot D.v
  let x0 : SignRegionChartInput d pivot := ((D.w0, vHat), D.t)
  have hvHat_eq : vHat = signRegionHat pivot D.v := rfl
  have hx0_domain : x0 ∈ signRegionChartDomain θ h pivot := by
    simpa [x0, vHat, signRegionChartDomain] using hpivot
  have hcenter_chart : signRegionChart θ h pivot x0 = D.point := by
    dsimp [x0, vHat]
    exact signRegionChart_projection_eq_of_mem_slab θ h pivot D.point
      hpivot D.anchor_eq_zero
  have hstrict_source_nhds :
      (signRegionChart θ h pivot) ⁻¹' signRegionStrictPositiveSet θ h ∈
        nhds x0 := by
    have hcont : ContinuousAt (signRegionChart θ h pivot) x0 :=
      ((analyticOnNhd_signRegionChart θ h pivot) x0 hx0_domain).continuousAt
    exact hcont.preimage_mem_nhds
      (by simpa [hcenter_chart] using D.strictPositiveSet_mem_nhds)
  rcases Metric.mem_nhds_iff.mp hstrict_source_nhds with
    ⟨εStrict, hεStrict_pos, hεStrict_subset⟩
  have hw_open :
      IsOpen {w : Vec d | signRegionKappa θ h pivot w ≠ 0} := by
    simpa using isOpen_ne.preimage (continuous_signRegionKappa θ h pivot)
  have hw_nhds :
      {w : Vec d | signRegionKappa θ h pivot w ≠ 0} ∈ nhds D.w0 :=
    hw_open.mem_nhds hpivot
  rcases Metric.mem_nhds_iff.mp hw_nhds with
    ⟨εW, hεW_pos, hεW_subset⟩
  have ht_nhds : Set.Ioo (0 : ℝ) 1 ∈ nhds D.t :=
    isOpen_Ioo.mem_nhds D.t_mem_Ioo
  rcases Metric.mem_nhds_iff.mp ht_nhds with
    ⟨εT, hεT_pos, hεT_subset⟩
  let ρ : ℝ := min εStrict (min εW εT)
  have hρ_pos : 0 < ρ := by
    exact lt_min hεStrict_pos (lt_min hεW_pos hεT_pos)
  have hρ_le_strict : ρ ≤ εStrict := by
    exact min_le_left εStrict (min εW εT)
  have hρ_le_w : ρ ≤ εW := by
    exact le_trans (min_le_right εStrict (min εW εT)) (min_le_left εW εT)
  have hρ_le_t : ρ ≤ εT := by
    exact le_trans (min_le_right εStrict (min εW εT)) (min_le_right εW εT)
  have hinterval :
      Set.Ioo (D.t - ρ) (D.t + ρ) ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro s hs
    apply hεT_subset
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    rcases hs with ⟨hlo, hhi⟩
    constructor <;> linarith
  have hwball :
      Metric.ball D.w0 ρ ⊆ {w | signRegionKappa θ h pivot w ≠ 0} := by
    intro w hw
    apply hεW_subset
    rw [Metric.mem_ball] at hw ⊢
    exact lt_of_lt_of_le hw hρ_le_w
  let source : Set (SignRegionChartInput d pivot) :=
    signRegionSourceBox pivot D.w0 vHat D.t ρ
  let region : Set (SignRegionPoint d) :=
    signRegionChart θ h pivot '' source
  have hsource_strict :
      signRegionChart θ h pivot '' source ⊆
        signRegionStrictPositiveSet θ h := by
    rintro p ⟨x, hx, rfl⟩
    exact hεStrict_subset
      (signRegionSourceBox_subset_ball pivot D.w0 vHat D.t ρ εStrict
        hρ_le_strict (by simpa [source] using hx))
  have hambient :
      region = signRegionSlab θ h ∩
        signRegionAmbientBox pivot D.w0 vHat D.t ρ := by
    simpa [region, source] using
      signRegionChart_image_sourceBox_eq_slab_inter_ambientBox
        θ h pivot D.w0 vHat D.t ρ hwball hinterval
  have hsource_subset_domain :
      source ⊆ signRegionChartDomain θ h pivot := by
    intro x hx
    exact hwball (by simpa [source] using hx.1)
  have hx0_source : x0 ∈ source := by
    refine ⟨?_, ?_, ?_⟩
    · have hwself : D.w0 ∈ Metric.ball D.w0 ρ := Metric.mem_ball_self hρ_pos
      simpa [x0, source] using hwself
    · have hvself : vHat ∈ Metric.ball vHat ρ := Metric.mem_ball_self hρ_pos
      simpa [x0, source] using hvself
    · dsimp [x0, source, signRegionSourceBox]
      exact ⟨sub_lt_self D.t hρ_pos, lt_add_of_pos_right D.t hρ_pos⟩
  have hcenter_mem_region : D.point ∈ region := by
    exact ⟨x0, hx0_source, hcenter_chart⟩
  have hsource_convex : Convex ℝ source := by
    simpa [source] using convex_signRegionSourceBox pivot D.w0 vHat D.t ρ
  have hregion_connected : IsPreconnected region := by
    simpa [region] using
      hsource_convex.isPreconnected.image (signRegionChart θ h pivot)
        ((continuousOn_signRegionChart θ h pivot).mono hsource_subset_domain)
  have hbij :
      Set.BijOn (signRegionChart θ h pivot) source region := by
    simpa [region, source] using
      signRegionChart_bijOn_sourceBox θ h pivot D.w0 vHat D.t ρ
  have hproj_inv :
      ∀ p ∈ region, signRegionChart θ h pivot (signRegionProjection pivot p) = p := by
    simpa [region] using
      signRegionChart_projection_inverse_on_image θ h pivot source
  have hsep :
      ∀ p ∈ region, ∀ a : AnchorSeparationHead k h,
        0 < signRegionSeparationValue θ a p := by
    intro p hp a
    have hpstrict : p ∈ signRegionStrictPositiveSet θ h :=
      hsource_strict (by simpa [region] using hp)
    simpa [signRegionStrictValue] using hpstrict (Sum.inl (Sum.inl a))
  have hlevel :
      ∀ p ∈ region, ∀ j : Fin m, ∀ b : Fin k,
        0 < signRegionLevelValue θ h j b p := by
    intro p hp j b
    have hpstrict : p ∈ signRegionStrictPositiveSet θ h :=
      hsource_strict (by simpa [region] using hp)
    simpa [signRegionStrictValue] using hpstrict (Sum.inl (Sum.inr (j, b)))
  have htrans :
      ∀ p ∈ region, 0 < signRegionTransversalityValue θ h p := by
    intro p hp
    have hpstrict : p ∈ signRegionStrictPositiveSet θ h :=
      hsource_strict (by simpa [region] using hp)
    simpa [signRegionStrictValue] using hpstrict (Sum.inr PUnit.unit)
  exact ⟨
    { center := D
      pivot := pivot
      pivot_nonzero := hpivot
      vHat := vHat
      vHat_eq := hvHat_eq
      rho := ρ
      rho_pos := hρ_pos
      interval_subset_Ioo := hinterval
      w_ball_subset_chart := hwball
      region := region
      region_eq_chart_image := by
        simp [region, source]
      ambient_identity := hambient
      center_chart := by
        simpa [x0] using hcenter_chart
      center_mem_region := hcenter_mem_region
      chart_continuousOn := continuousOn_signRegionChart θ h pivot
      chart_analyticOnNhd := analyticOnNhd_signRegionChart θ h pivot
      chart_bijective := hbij
      chart_projection_inverse := hproj_inv
      source_convex := hsource_convex
      region_connected := hregion_connected
      separation_positive := hsep
      level_positive := hlevel
      transversality_positive := htrans }⟩

/-! ## Recursive generic set -/

/-- Current positive-tail generic clauses applied at an induction step. -/
def CurrentGenericClauses {m k d : Nat} (r : Nat) (θ : Params (m + 1) k d) :
    Prop :=
  Regularity r θ ∧
    LocalOpenness r θ ∧
      CascadeCertificate θ ∧
        AnchorCertificate θ

/-- `K03B.E.def-recursive-G.S/P`: recursive k-head generic set. -/
noncomputable def RecursiveGeneric (r : Nat) :
    (L k d : Nat) → Params L k d → Prop
  | 0, _k, _d, _θ => True
  | L + 1, k, d, θ =>
      RecursiveGeneric r L k d (Fin.tail θ) ∧
        CurrentGenericClauses r θ

/-- The recursive generic parameter set. -/
def RecursiveGenericSet (r L k d : Nat) : Set (Params L k d) :=
  {θ | RecursiveGeneric r L k d θ}

/-- The complement of the recursive generic set. -/
def RecursiveGenericBadSet (r L k d : Nat) : Set (Params L k d) :=
  (RecursiveGenericSet r L k d)ᶜ

@[simp]
theorem recursiveGeneric_zero {r k d : Nat} (θ : Params 0 k d) :
    RecursiveGeneric r 0 k d θ :=
  trivial

@[simp]
theorem recursiveGeneric_succ {r L k d : Nat} (θ : Params (L + 1) k d) :
    RecursiveGeneric r (L + 1) k d θ ↔
      RecursiveGeneric r L k d (Fin.tail θ) ∧
        CurrentGenericClauses r θ :=
  Iff.rfl

@[simp]
theorem mem_recursiveGenericSet {r L k d : Nat} {θ : Params L k d} :
    θ ∈ RecursiveGenericSet r L k d ↔ RecursiveGeneric r L k d θ :=
  Iff.rfl

end TransformerIdentifiability.NLayer.KHead
