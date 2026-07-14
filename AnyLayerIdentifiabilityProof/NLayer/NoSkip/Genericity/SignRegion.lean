import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Genericity.MultiDialCertificate

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.NoSkip

/-!
# The pinned multi-dial center

This file begins the sign-region construction with its finite-dimensional
affine solve.  The corrected certificate has only anchor targets `0` and level
targets `-1`.
-/

noncomputable section

/-- Target vector for the simultaneous affine solve: every first-layer anchor
is zero and every deeper frozen level is negative. -/
def multiDialPinnedTarget {m k : Nat} : MultiDialRow m k → Real
  | Sum.inl _ => 0
  | Sum.inr _ => -1

@[simp] theorem multiDialPinnedTarget_anchor {m k : Nat} (a : Fin k) :
    multiDialPinnedTarget (m := m) (MultiDialRow.anchor a) = 0 :=
  rfl

@[simp] theorem multiDialPinnedTarget_level {m k : Nat}
    (jb : LevelRowIndex m k) :
    multiDialPinnedTarget (MultiDialRow.level jb) = -1 :=
  rfl

/-- Explicit minimum-norm affine solution
`v = G (GᵀG)⁻¹ (y-R(0))`. -/
noncomputable def multiDialPinnedCenter {n k d : Nat}
    (theta : Params (n + 1) k d) (t : Fin k → Real) (w : Vec d) : Vec d :=
  let G := multiDialGradientMatrix theta t w
  let A : Matrix (MultiDialRow (n + 1) k) (MultiDialRow (n + 1) k) Real :=
    Gᵀ * G
  G *ᵥ (A⁻¹ *ᵥ
    (multiDialPinnedTarget - multiDialConstantVector theta t w))

/-- A nonzero corrected Gram determinant makes the complete anchor-and-level
affine row map surjective at the prescribed target. -/
theorem multiDialRowVector_pinnedCenter_of_gramDet_ne_zero
    {n k d : Nat} (theta : Params (n + 1) k d)
    (t : Fin k → Real) (w : Vec d)
    (hgram : multiDialGramDet theta t w ≠ 0) :
    multiDialRowVector theta t w (multiDialPinnedCenter theta t w) =
      multiDialPinnedTarget := by
  classical
  let G := multiDialGradientMatrix theta t w
  let A : Matrix (MultiDialRow (n + 1) k) (MultiDialRow (n + 1) k) Real :=
    Gᵀ * G
  let y : MultiDialRow (n + 1) k → Real :=
    multiDialPinnedTarget - multiDialConstantVector theta t w
  have hA_det : A.det ≠ 0 := by
    simpa [multiDialGramDet, multiDialGramMatrix, G, A] using hgram
  have hA_unit : IsUnit A.det := isUnit_iff_ne_zero.mpr hA_det
  have hA_solve : A *ᵥ (A⁻¹ *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hA_unit,
      Matrix.one_mulVec]
  have hG_solve : Gᵀ *ᵥ (multiDialPinnedCenter theta t w) = y := by
    change Gᵀ *ᵥ (G *ᵥ (A⁻¹ *ᵥ y)) = y
    rw [Matrix.mulVec_mulVec]
    exact hA_solve
  rw [multiDialRowVector_eq_gradientMatrix_transpose_mulVec_add]
  change Gᵀ *ᵥ (multiDialPinnedCenter theta t w) +
      multiDialConstantVector theta t w = multiDialPinnedTarget
  rw [hG_solve]
  ext row
  simp [y]

/-- Pointwise pinning form used by later chart and sign arguments. -/
theorem exists_multiDial_row_pinning_of_gramDet_ne_zero
    {n k d : Nat} (theta : Params (n + 1) k d)
    (t : Fin k → Real) (w : Vec d)
    (hgram : multiDialGramDet theta t w ≠ 0) :
    ∃ v : Vec d, ∀ row : MultiDialRow (n + 1) k,
      multiDialRowValue theta t w row v = multiDialPinnedTarget row := by
  refine ⟨multiDialPinnedCenter theta t w, ?_⟩
  intro row
  exact congr_fun
    (multiDialRowVector_pinnedCenter_of_gramDet_ne_zero theta t w hgram) row

/-- Every anchor quadric contains the pinned center. -/
theorem multiDialPinnedCenter_anchorRow_eq_zero_of_gramDet_ne_zero
    {n k d : Nat} (theta : Params (n + 1) k d)
    (t : Fin k → Real) (w : Vec d)
    (hgram : multiDialGramDet theta t w ≠ 0) (a : Fin k) :
    anchorRow theta w a (multiDialPinnedCenter theta t w) = 0 := by
  have h := congr_fun
    (multiDialRowVector_pinnedCenter_of_gramDet_ne_zero theta t w hgram)
    (MultiDialRow.anchor a)
  simpa [multiDialRowVector] using h

/-- Every deeper frozen level has the strict negative center value `-1`. -/
theorem multiDialPinnedCenter_levelRow_eq_neg_one_of_gramDet_ne_zero
    {n k d : Nat} (theta : Params (n + 1) k d)
    (t : Fin k → Real) (w : Vec d)
    (hgram : multiDialGramDet theta t w ≠ 0)
    (jb : LevelRowIndex (n + 1) k) :
    levelRow theta t w jb (multiDialPinnedCenter theta t w) = -1 := by
  have h := congr_fun
    (multiDialRowVector_pinnedCenter_of_gramDet_ne_zero theta t w hgram)
    (MultiDialRow.level jb)
  simpa [multiDialRowVector] using h

/-- Certificate-level capstone: choose a nonzero Gram evaluation and solve all
anchor and deeper-level rows simultaneously. -/
theorem MultiDialCertificate.exists_pinned_center
    {n k d : Nat} {theta : Params (n + 1) k d}
    (hcert : MultiDialCertificate theta) :
    ∃ t : Fin k → Real, ∃ w v : Vec d,
      multiDialGramDet theta t w ≠ 0 ∧
      (∀ a : Fin k, anchorRow theta w a v = 0) ∧
      (∀ jb : LevelRowIndex (n + 1) k, levelRow theta t w jb v = -1) := by
  rw [multiDialCertificate_iff_exists_gramDet_ne_zero] at hcert
  rcases hcert with ⟨t, w, hgram⟩
  refine ⟨t, w, multiDialPinnedCenter theta t w, hgram, ?_, ?_⟩
  · exact multiDialPinnedCenter_anchorRow_eq_zero_of_gramDet_ne_zero
      theta t w hgram
  · exact multiDialPinnedCenter_levelRow_eq_neg_one_of_gramDet_ne_zero
      theta t w hgram

/-! ## Coordinate pivot for the multi-quadric chart -/

/-- The TeX anchor matrix `Γ(w)`: its rows are the first-layer anchor
gradients. -/
noncomputable def anchorGradientMatrix {m k d : Nat}
    (theta : Params (m + 1) k d) (w : Vec d) :
    Matrix (Fin k) (Fin d) Real :=
  Matrix.of fun a i => anchorGradient theta w a i

@[simp] theorem anchorGradientMatrix_apply {m k d : Nat}
    (theta : Params (m + 1) k d) (w : Vec d)
    (a : Fin k) (i : Fin d) :
    anchorGradientMatrix theta w a i = anchorGradient theta w a i :=
  rfl

@[simp] theorem anchorGradientMatrix_row {m k d : Nat}
    (theta : Params (m + 1) k d) (w : Vec d) (a : Fin k) :
    (anchorGradientMatrix theta w).row a = anchorGradient theta w a :=
  rfl

/-- `Γ(w) v` is exactly the vector of anchor-row evaluations. -/
@[simp] theorem anchorGradientMatrix_mulVec {m k d : Nat}
    (theta : Params (m + 1) k d) (w v : Vec d) :
    anchorGradientMatrix theta w *ᵥ v = fun a => anchorRow theta w a v := by
  ext a
  simp [anchorGradientMatrix, anchorRow_eq_dotProduct, Matrix.mulVec,
    dotProduct]

/-- The genuine coordinate minor `Γ(w)_{:,pivot}` used to solve for the
selected coordinates of `v`. -/
noncomputable def anchorPivotMatrix {m k d : Nat}
    (theta : Params (m + 1) k d) (w : Vec d)
    (pivot : Fin k ↪ Fin d) : Matrix (Fin k) (Fin k) Real :=
  (anchorGradientMatrix theta w).submatrix id pivot

@[simp] theorem anchorPivotMatrix_apply {m k d : Nat}
    (theta : Params (m + 1) k d) (w : Vec d)
    (pivot : Fin k ↪ Fin d) (a b : Fin k) :
    anchorPivotMatrix theta w pivot a b =
      anchorGradient theta w a (pivot b) :=
  rfl

theorem anchorPivotMatrix_eq_submatrix {m k d : Nat}
    (theta : Params (m + 1) k d) (w : Vec d)
    (pivot : Fin k ↪ Fin d) :
    anchorPivotMatrix theta w pivot =
      (anchorGradientMatrix theta w).submatrix id pivot :=
  rfl

@[simp] theorem anchorPivotMatrix_row {m k d : Nat}
    (theta : Params (m + 1) k d) (w : Vec d)
    (pivot : Fin k ↪ Fin d) (a : Fin k) :
    (anchorPivotMatrix theta w pivot).row a =
      fun b => anchorGradient theta w a (pivot b) :=
  rfl

@[simp] theorem anchorPivotMatrix_mulVec_apply {m k d : Nat}
    (theta : Params (m + 1) k d) (w : Vec d)
    (pivot : Fin k ↪ Fin d) (z : Fin k → Real) (a : Fin k) :
    (anchorPivotMatrix theta w pivot *ᵥ z) a =
      ∑ b : Fin k, anchorGradient theta w a (pivot b) * z b := by
  simp [anchorPivotMatrix, Matrix.mulVec, dotProduct]

/-- Pointwise local-invertibility condition for a fixed coordinate pivot. -/
def AnchorPivotInvertibleAt {m k d : Nat}
    (theta : Params (m + 1) k d) (pivot : Fin k ↪ Fin d)
    (w : Vec d) : Prop :=
  (anchorPivotMatrix theta w pivot).det ≠ 0

/-- Domain on which the fixed coordinate minor can be used as a chart pivot. -/
def anchorPivotDomain {m k d : Nat}
    (theta : Params (m + 1) k d) (pivot : Fin k ↪ Fin d) :
    Set (Vec d) :=
  {w | AnchorPivotInvertibleAt theta pivot w}

@[simp] theorem mem_anchorPivotDomain_iff {m k d : Nat}
    (theta : Params (m + 1) k d) (pivot : Fin k ↪ Fin d)
    (w : Vec d) :
    w ∈ anchorPivotDomain theta pivot ↔
      (anchorPivotMatrix theta w pivot).det ≠ 0 :=
  Iff.rfl

theorem AnchorPivotInvertibleAt.isUnit_det {m k d : Nat}
    {theta : Params (m + 1) k d} {pivot : Fin k ↪ Fin d}
    {w : Vec d} (h : AnchorPivotInvertibleAt theta pivot w) :
    IsUnit (anchorPivotMatrix theta w pivot).det :=
  isUnit_iff_ne_zero.mpr h

theorem AnchorPivotInvertibleAt.mul_nonsing_inv {m k d : Nat}
    {theta : Params (m + 1) k d} {pivot : Fin k ↪ Fin d}
    {w : Vec d} (h : AnchorPivotInvertibleAt theta pivot w) :
    anchorPivotMatrix theta w pivot *
        (anchorPivotMatrix theta w pivot)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ h.isUnit_det

theorem AnchorPivotInvertibleAt.nonsing_inv_mul {m k d : Nat}
    {theta : Params (m + 1) k d} {pivot : Fin k ↪ Fin d}
    {w : Vec d} (h : AnchorPivotInvertibleAt theta pivot w) :
    (anchorPivotMatrix theta w pivot)⁻¹ *
        anchorPivotMatrix theta w pivot = 1 :=
  Matrix.nonsing_inv_mul _ h.isUnit_det

theorem AnchorPivotInvertibleAt.mulVec_nonsing_inv_mulVec {m k d : Nat}
    {theta : Params (m + 1) k d} {pivot : Fin k ↪ Fin d}
    {w : Vec d} (h : AnchorPivotInvertibleAt theta pivot w)
    (y : Fin k → Real) :
    anchorPivotMatrix theta w pivot *ᵥ
        ((anchorPivotMatrix theta w pivot)⁻¹ *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec, h.mul_nonsing_inv, Matrix.one_mulVec]

theorem AnchorPivotInvertibleAt.eq_nonsing_inv_mulVec_of_mulVec_eq
    {m k d : Nat}
    {theta : Params (m + 1) k d} {pivot : Fin k ↪ Fin d}
    {w : Vec d} (h : AnchorPivotInvertibleAt theta pivot w)
    {x y : Fin k → Real}
    (hxy : anchorPivotMatrix theta w pivot *ᵥ x = y) :
    x = (anchorPivotMatrix theta w pivot)⁻¹ *ᵥ y := by
  calc
    x = (1 : Matrix (Fin k) (Fin k) Real) *ᵥ x := by simp
    _ = ((anchorPivotMatrix theta w pivot)⁻¹ *
          anchorPivotMatrix theta w pivot) *ᵥ x := by
        rw [h.nonsing_inv_mul]
    _ = (anchorPivotMatrix theta w pivot)⁻¹ *ᵥ
          (anchorPivotMatrix theta w pivot *ᵥ x) :=
        (Matrix.mulVec_mulVec _ _ _).symm
    _ = (anchorPivotMatrix theta w pivot)⁻¹ *ᵥ y := by rw [hxy]

/-- Coordinate-row pivot lemma.  A linearly independent family of `k`
vectors in `R^d` admits `k` actual ambient coordinates on which its coordinate
matrix has nonzero determinant. -/
theorem exists_coordinate_pivot_of_linearIndependent
    {k d : Nat} (g : Fin k → Vec d)
    (hli : LinearIndependent Real g) :
    ∃ pivot : Fin k ↪ Fin d,
      (Matrix.of fun a b => g a (pivot b)).det ≠ 0 := by
  classical
  let C : Matrix (Fin d) (Fin k) Real := Matrix.of fun i a => g a i
  have hcols : LinearIndependent Real C.col := by
    simpa [C, Matrix.col] using hli
  have hrows_transpose : LinearIndependent Real Cᵀ.row := by
    simpa [Matrix.row, Matrix.col] using hcols
  have hrank : C.rank = k := by
    rw [← Matrix.rank_transpose]
    simpa using hrows_transpose.rank_matrix
  have hspan : Submodule.span Real (Set.range C.row) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← C.rank_eq_finrank_span_row, hrank,
      Module.finrank_fintype_fun_eq_card]
    simp
  let I : Set (Fin k → Real) :=
    (linearIndepOn_empty Real id).extend
      (Set.empty_subset (Set.range C.row))
  let basis : Module.Basis I Real (Fin k → Real) :=
    Module.Basis.ofSpan hspan.ge
  have hI_subset : I ⊆ Set.range C.row := by
    intro x hx
    have hxb : x ∈ Set.range basis := by
      refine ⟨⟨x, hx⟩, ?_⟩
      simp [basis, I]
    exact Module.Basis.ofSpan_subset hspan.ge hxb
  letI : Fintype I :=
    Set.Finite.fintype ((Set.finite_range C.row).subset hI_subset)
  have hcardI : Fintype.card I = k := by
    rw [← Module.finrank_eq_card_basis basis,
      Module.finrank_fintype_fun_eq_card]
    simp
  let e : Fin k ≃ I :=
    Fintype.equivOfCardEq (by simpa using hcardI.symm)
  have hbrow : ∀ a : Fin k, ∃ i : Fin d, basis (e a) = C.row i := by
    intro a
    have hb_apply : basis (e a) = (e a : Fin k → Real) := by
      change Module.Basis.ofSpan hspan.ge (e a) = (e a : Fin k → Real)
      exact Module.Basis.ofSpan_apply_self hspan.ge (e a)
    have hmemI : basis (e a) ∈ I := by
      rw [hb_apply]
      exact (e a).property
    rcases hI_subset hmemI with ⟨i, hi⟩
    exact ⟨i, hi.symm⟩
  choose p hp using hbrow
  have hp_injective : Function.Injective p := by
    intro a a' haa'
    apply e.injective
    apply basis.injective
    rw [hp a, hp a', haa']
  let pivot : Fin k ↪ Fin d := ⟨p, hp_injective⟩
  let Q : Matrix (Fin k) (Fin k) Real := C.submatrix pivot id
  have hQrows : LinearIndependent Real Q.row := by
    have hbe : LinearIndependent Real (fun a : Fin k => basis (e a)) :=
      basis.linearIndependent.comp e e.injective
    convert hbe using 1
    ext a j
    simp [Q, pivot, hp]
  have hQunit : IsUnit Q :=
    Matrix.linearIndependent_rows_iff_isUnit.mp hQrows
  have hQdet : Q.det ≠ 0 :=
    (Q.isUnit_iff_isUnit_det.mp hQunit).ne_zero
  refine ⟨pivot, ?_⟩
  have hmatrix : (Matrix.of fun a b => g a (pivot b)) = Qᵀ := by
    ext a b
    rfl
  rw [hmatrix, Matrix.det_transpose]
  exact hQdet

/-- The anchor subfamily of a nondegenerate full multi-dial Gram family is
linearly independent. -/
theorem linearIndependent_anchorGradient_of_gramDet_ne_zero
    {n k d : Nat} (theta : Params (n + 1) k d)
    (t : Fin k → Real) (w : Vec d)
    (hgram : multiDialGramDet theta t w ≠ 0) :
    LinearIndependent Real (anchorGradient theta w) := by
  have hfull := linearIndependent_multiDialRowGradient_of_gramDet_ne_zero
    theta t w hgram
  have hanchor := hfull.comp (fun a : Fin k => MultiDialRow.anchor a)
    (by
      intro a b hab
      exact Sum.inl.inj hab)
  simpa only [multiDialRowGradient_anchor] using hanchor

/-- Anchor-column independence alone is the exact hypothesis needed for
coordinate-pivot selection. -/
theorem exists_anchorPivot_of_linearIndependent
    {m k d : Nat} (theta : Params (m + 1) k d) (w : Vec d)
    (hli : LinearIndependent Real (anchorGradient theta w)) :
    ∃ pivot : Fin k ↪ Fin d,
      AnchorPivotInvertibleAt theta pivot w := by
  simpa [AnchorPivotInvertibleAt, anchorPivotMatrix] using
    exists_coordinate_pivot_of_linearIndependent
      (anchorGradient theta w) hli

/-- A nonzero full Gram determinant supplies a genuine coordinate pivot for
the anchor matrix. -/
theorem exists_anchorPivot_of_gramDet_ne_zero
    {n k d : Nat} (theta : Params (n + 1) k d)
    (t : Fin k → Real) (w : Vec d)
    (hgram : multiDialGramDet theta t w ≠ 0) :
    ∃ pivot : Fin k ↪ Fin d,
      AnchorPivotInvertibleAt theta pivot w := by
  exact exists_anchorPivot_of_linearIndependent theta w
    (linearIndependent_anchorGradient_of_gramDet_ne_zero
      theta t w hgram)

/-- Selected coordinate-pivot package consumed by the chart construction. -/
structure AnchorCoordinatePivot {m k d : Nat}
    (theta : Params (m + 1) k d) (w : Vec d) where
  pivot : Fin k ↪ Fin d
  invertibleAt : AnchorPivotInvertibleAt theta pivot w

namespace AnchorCoordinatePivot

variable {m k d : Nat} {theta : Params (m + 1) k d} {w : Vec d}

theorem det_ne_zero (P : AnchorCoordinatePivot theta w) :
    (anchorPivotMatrix theta w P.pivot).det ≠ 0 :=
  P.invertibleAt

theorem isUnit_det (P : AnchorCoordinatePivot theta w) :
    IsUnit (anchorPivotMatrix theta w P.pivot).det :=
  P.invertibleAt.isUnit_det

@[simp] theorem center_mem_domain (P : AnchorCoordinatePivot theta w) :
    w ∈ anchorPivotDomain theta P.pivot :=
  P.invertibleAt

end AnchorCoordinatePivot

/-- Canonical choice of the coordinate pivot supplied by a full Gram witness. -/
noncomputable def anchorCoordinatePivotOfGram
    {n k d : Nat} (theta : Params (n + 1) k d)
    (t : Fin k → Real) (w : Vec d)
    (hgram : multiDialGramDet theta t w ≠ 0) :
    AnchorCoordinatePivot theta w :=
  ⟨Classical.choose
      (exists_anchorPivot_of_gramDet_ne_zero theta t w hgram),
    Classical.choose_spec
      (exists_anchorPivot_of_gramDet_ne_zero theta t w hgram)⟩

/-! ## Multi-coordinate solved chart -/

abbrev AnchorFreeCoord {k d : Nat} (pivot : Fin k ↪ Fin d) :=
  {i : Fin d // i ∉ Set.range pivot}

abbrev AnchorFreeVec {k d : Nat} (pivot : Fin k ↪ Fin d) :=
  AnchorFreeCoord pivot → Real

noncomputable def anchorCoordEquiv {k d : Nat} (pivot : Fin k ↪ Fin d) :
    Fin k ⊕ AnchorFreeCoord pivot ≃ Fin d :=
  (Equiv.sumCongr (Equiv.ofInjective pivot pivot.injective) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range pivot))

@[simp] theorem anchorCoordEquiv_inl {k d : Nat} (pivot : Fin k ↪ Fin d)
    (a : Fin k) : anchorCoordEquiv pivot (Sum.inl a) = pivot a := by
  unfold anchorCoordEquiv
  rw [Equiv.trans_apply]
  exact Equiv.Set.sumCompl_apply_inl _ _

@[simp] theorem anchorCoordEquiv_inr {k d : Nat} (pivot : Fin k ↪ Fin d)
    (i : AnchorFreeCoord pivot) : anchorCoordEquiv pivot (Sum.inr i) = i.1 := by
  unfold anchorCoordEquiv
  rw [Equiv.trans_apply]
  exact Equiv.Set.sumCompl_apply_inr _ _

def anchorDelete {k d : Nat} (pivot : Fin k ↪ Fin d)
    (v : Vec d) : AnchorFreeVec pivot :=
  fun i => v i.1

def anchorPivotCoords {k d : Nat} (pivot : Fin k ↪ Fin d)
    (v : Vec d) : Fin k → Real :=
  fun a => v (pivot a)

noncomputable def anchorInsert {k d : Nat} (pivot : Fin k ↪ Fin d)
    (z : Fin k → Real) (vhat : AnchorFreeVec pivot) : Vec d :=
  fun i => Sum.elim z vhat ((anchorCoordEquiv pivot).symm i)

@[simp] theorem anchorInsert_pivot {k d : Nat} (pivot : Fin k ↪ Fin d)
    (z : Fin k → Real) (vhat : AnchorFreeVec pivot) (a : Fin k) :
    anchorInsert pivot z vhat (pivot a) = z a := by
  have h := (anchorCoordEquiv pivot).symm_apply_apply (Sum.inl a)
  rw [anchorCoordEquiv_inl] at h
  rw [anchorInsert, h]
  rfl

@[simp] theorem anchorInsert_free {k d : Nat} (pivot : Fin k ↪ Fin d)
    (z : Fin k → Real) (vhat : AnchorFreeVec pivot)
    (i : AnchorFreeCoord pivot) :
    anchorInsert pivot z vhat i.1 = vhat i := by
  have h := (anchorCoordEquiv pivot).symm_apply_apply (Sum.inr i)
  rw [anchorCoordEquiv_inr] at h
  rw [anchorInsert, h]
  rfl

@[simp] theorem anchorDelete_insert {k d : Nat} (pivot : Fin k ↪ Fin d)
    (z : Fin k → Real) (vhat : AnchorFreeVec pivot) :
    anchorDelete pivot (anchorInsert pivot z vhat) = vhat := by
  funext i
  simp [anchorDelete]

@[simp] theorem anchorPivotCoords_insert {k d : Nat} (pivot : Fin k ↪ Fin d)
    (z : Fin k → Real) (vhat : AnchorFreeVec pivot) :
    anchorPivotCoords pivot (anchorInsert pivot z vhat) = z := by
  funext a
  simp [anchorPivotCoords]

@[simp] theorem anchorInsert_coords_delete {k d : Nat}
    (pivot : Fin k ↪ Fin d) (v : Vec d) :
    anchorInsert pivot (anchorPivotCoords pivot v) (anchorDelete pivot v) = v := by
  funext i
  obtain ⟨a | j, hij⟩ := (anchorCoordEquiv pivot).surjective i
  · subst i
    simp [anchorPivotCoords]
  · subst i
    simp [anchorDelete]

theorem continuous_anchorDelete {k d : Nat} (pivot : Fin k ↪ Fin d) :
    Continuous (anchorDelete pivot : Vec d → AnchorFreeVec pivot) := by
  rw [continuous_pi_iff]
  intro i
  exact continuous_apply i.1

theorem continuous_anchorInsert {k d : Nat} (pivot : Fin k ↪ Fin d) :
    Continuous fun x : (Fin k → Real) × AnchorFreeVec pivot =>
      anchorInsert pivot x.1 x.2 := by
  rw [continuous_pi_iff]
  intro i
  obtain ⟨a | j, hij⟩ := (anchorCoordEquiv pivot).surjective i
  · subst i
    simpa using ((continuous_apply a).comp
      (continuous_fst : Continuous fun x :
        (Fin k → Real) × AnchorFreeVec pivot => x.1))
  · subst i
    simpa using ((continuous_apply j).comp
      (continuous_snd : Continuous fun x :
        (Fin k → Real) × AnchorFreeVec pivot => x.2))

noncomputable def anchorFreeMatrix {m k d : Nat}
    (theta : Params (m + 1) k d) (w : Vec d)
    (pivot : Fin k ↪ Fin d) : Matrix (Fin k) (AnchorFreeCoord pivot) Real :=
  (anchorGradientMatrix theta w).submatrix id Subtype.val

@[simp] theorem anchorFreeMatrix_apply {m k d : Nat}
    (theta : Params (m + 1) k d) (w : Vec d)
    (pivot : Fin k ↪ Fin d) (a : Fin k) (i : AnchorFreeCoord pivot) :
    anchorFreeMatrix theta w pivot a i = anchorGradient theta w a i.1 := rfl

theorem anchorGradientMatrix_mulVec_insert {m k d : Nat}
    (theta : Params (m + 1) k d) (w : Vec d)
    (pivot : Fin k ↪ Fin d) (z : Fin k → Real)
    (vhat : AnchorFreeVec pivot) :
    anchorGradientMatrix theta w *ᵥ anchorInsert pivot z vhat =
      anchorPivotMatrix theta w pivot *ᵥ z +
        anchorFreeMatrix theta w pivot *ᵥ vhat := by
  ext a
  simp only [Matrix.mulVec, Pi.add_apply]
  calc
    (∑ i : Fin d, anchorGradientMatrix theta w a i * anchorInsert pivot z vhat i) =
        ∑ q : Fin k ⊕ AnchorFreeCoord pivot,
          anchorGradientMatrix theta w a (anchorCoordEquiv pivot q) *
            anchorInsert pivot z vhat (anchorCoordEquiv pivot q) := by
      exact ((anchorCoordEquiv pivot).sum_comp fun i =>
        anchorGradientMatrix theta w a i * anchorInsert pivot z vhat i).symm
    _ = (∑ b : Fin k, anchorGradient theta w a (pivot b) * z b) +
          ∑ i : AnchorFreeCoord pivot,
            anchorGradient theta w a i.1 * vhat i := by
      simp [Fintype.sum_sum_type]
    _ = _ := by rfl

abbrev AnchorChartInput {k d : Nat} (pivot : Fin k ↪ Fin d) :=
  Vec d × AnchorFreeVec pivot

def anchorChartDomain {m k d : Nat} (theta : Params (m + 1) k d)
    (pivot : Fin k ↪ Fin d) : Set (AnchorChartInput pivot) :=
  {x | x.1 ∈ anchorPivotDomain theta pivot}

noncomputable def anchorGamma {m k d : Nat}
    (theta : Params (m + 1) k d) (pivot : Fin k ↪ Fin d)
    (w : Vec d) (vhat : AnchorFreeVec pivot) : Vec d :=
  anchorInsert pivot
    (-((anchorPivotMatrix theta w pivot)⁻¹ *ᵥ
      (anchorFreeMatrix theta w pivot *ᵥ vhat))) vhat

@[simp] theorem anchorDelete_gamma {m k d : Nat}
    (theta : Params (m + 1) k d) (pivot : Fin k ↪ Fin d)
    (w : Vec d) (vhat : AnchorFreeVec pivot) :
    anchorDelete pivot (anchorGamma theta pivot w vhat) = vhat := by
  simp [anchorGamma]

@[simp] theorem anchorPivotCoords_gamma {m k d : Nat}
    (theta : Params (m + 1) k d) (pivot : Fin k ↪ Fin d)
    (w : Vec d) (vhat : AnchorFreeVec pivot) :
    anchorPivotCoords pivot (anchorGamma theta pivot w vhat) =
      -((anchorPivotMatrix theta w pivot)⁻¹ *ᵥ
        (anchorFreeMatrix theta w pivot *ᵥ vhat)) := by
  simp [anchorGamma]

theorem anchorGradientMatrix_mulVec_gamma_eq_zero {m k d : Nat}
    (theta : Params (m + 1) k d) (pivot : Fin k ↪ Fin d)
    (w : Vec d) (vhat : AnchorFreeVec pivot)
    (hw : w ∈ anchorPivotDomain theta pivot) :
    anchorGradientMatrix theta w *ᵥ anchorGamma theta pivot w vhat = 0 := by
  rw [anchorGamma, anchorGradientMatrix_mulVec_insert]
  have hinv : AnchorPivotInvertibleAt theta pivot w := hw
  have hsolve := hinv.mulVec_nonsing_inv_mulVec
    (anchorFreeMatrix theta w pivot *ᵥ vhat)
  rw [Matrix.mulVec_neg, hsolve]
  simp

theorem anchorRow_gamma_eq_zero {m k d : Nat}
    (theta : Params (m + 1) k d) (pivot : Fin k ↪ Fin d)
    (w : Vec d) (vhat : AnchorFreeVec pivot)
    (hw : w ∈ anchorPivotDomain theta pivot) (a : Fin k) :
    anchorRow theta w a (anchorGamma theta pivot w vhat) = 0 := by
  have h := congr_fun
    (anchorGradientMatrix_mulVec_gamma_eq_zero theta pivot w vhat hw) a
  simpa using h

theorem anchorGamma_eq_of_delete_eq_of_anchor_eq {m k d : Nat}
    (theta : Params (m + 1) k d) (pivot : Fin k ↪ Fin d)
    (w v : Vec d) (vhat : AnchorFreeVec pivot)
    (hw : w ∈ anchorPivotDomain theta pivot)
    (hdelete : anchorDelete pivot v = vhat)
    (hanchor : anchorGradientMatrix theta w *ᵥ v = 0) :
    anchorGamma theta pivot w vhat = v := by
  have hv_insert :
      v = anchorInsert pivot (anchorPivotCoords pivot v) vhat := by
    rw [← hdelete, anchorInsert_coords_delete]
  have hsplit := anchorGradientMatrix_mulVec_insert theta w pivot
    (anchorPivotCoords pivot v) vhat
  rw [← hv_insert, hanchor] at hsplit
  have hpivot_eq :
      anchorPivotCoords pivot v =
        -((anchorPivotMatrix theta w pivot)⁻¹ *ᵥ
          (anchorFreeMatrix theta w pivot *ᵥ vhat)) := by
    have hmul :
        anchorPivotMatrix theta w pivot *ᵥ anchorPivotCoords pivot v =
          -(anchorFreeMatrix theta w pivot *ᵥ vhat) := by
      apply eq_neg_of_add_eq_zero_left
      exact hsplit.symm
    have hinv : AnchorPivotInvertibleAt theta pivot w := hw
    rw [hinv.eq_nonsing_inv_mulVec_of_mulVec_eq hmul,
      Matrix.mulVec_neg]
  rw [anchorGamma, hv_insert, hpivot_eq]

theorem anchorGamma_eq_of_delete_eq_of_anchorRows_eq_zero {m k d : Nat}
    (theta : Params (m + 1) k d) (pivot : Fin k ↪ Fin d)
    (w v : Vec d) (vhat : AnchorFreeVec pivot)
    (hw : w ∈ anchorPivotDomain theta pivot)
    (hdelete : anchorDelete pivot v = vhat)
    (hanchor : ∀ a : Fin k, anchorRow theta w a v = 0) :
    anchorGamma theta pivot w vhat = v := by
  apply anchorGamma_eq_of_delete_eq_of_anchor_eq theta pivot
    w v vhat hw hdelete
  ext a
  simpa using hanchor a

noncomputable def anchorChart {m k d : Nat}
    (theta : Params (m + 1) k d) (pivot : Fin k ↪ Fin d) :
    AnchorChartInput pivot → Vec d × Vec d :=
  fun x => (x.1, anchorGamma theta pivot x.1 x.2)

def anchorChartProjection {k d : Nat} (pivot : Fin k ↪ Fin d) :
    (Vec d × Vec d) → AnchorChartInput pivot :=
  fun p => (p.1, anchorDelete pivot p.2)

theorem continuous_anchorChartProjection {k d : Nat}
    (pivot : Fin k ↪ Fin d) :
    Continuous (anchorChartProjection pivot :
      (Vec d × Vec d) → AnchorChartInput pivot) := by
  exact continuous_fst.prodMk ((continuous_anchorDelete pivot).comp continuous_snd)

@[simp] theorem anchorChartProjection_chart {m k d : Nat}
    (theta : Params (m + 1) k d) (pivot : Fin k ↪ Fin d)
    (x : AnchorChartInput pivot) :
    anchorChartProjection pivot (anchorChart theta pivot x) = x := by
  rcases x with ⟨w, vhat⟩
  simp [anchorChartProjection, anchorChart]

theorem anchorChart_projection_eq_of_anchor_eq {m k d : Nat}
    (theta : Params (m + 1) k d) (pivot : Fin k ↪ Fin d)
    (p : Vec d × Vec d) (hw : p.1 ∈ anchorPivotDomain theta pivot)
    (hanchor : anchorGradientMatrix theta p.1 *ᵥ p.2 = 0) :
    anchorChart theta pivot (anchorChartProjection pivot p) = p := by
  rcases p with ⟨w, v⟩
  apply Prod.ext
  · rfl
  · exact anchorGamma_eq_of_delete_eq_of_anchor_eq theta pivot
      w v (anchorDelete pivot v) hw rfl hanchor

section Analyticity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  {U : Set E}

theorem analyticOnNhd_matrix_det_of_coords {n : Nat}
    {F : E → Matrix (Fin n) (Fin n) Real}
    (hF : ∀ i j, AnalyticOnNhd Real (fun x => F x i j) U) :
    AnalyticOnNhd Real (fun x => (F x).det) U := by
  simp_rw [Matrix.det_apply']
  apply Finset.analyticOnNhd_fun_sum
  intro sigma _hsigma
  exact (analyticOnNhd_const (v := (Equiv.Perm.sign sigma : Real))).mul
    (Finset.analyticOnNhd_fun_prod Finset.univ fun i _hi => hF (sigma i) i)

theorem analyticOnNhd_matrix_adjugate_coord_of_coords {n : Nat}
    {F : E → Matrix (Fin n) (Fin n) Real}
    (hF : ∀ i j, AnalyticOnNhd Real (fun x => F x i j) U)
    (i j : Fin n) :
    AnalyticOnNhd Real (fun x => (F x).adjugate i j) U := by
  simp_rw [Matrix.adjugate_apply]
  apply analyticOnNhd_matrix_det_of_coords
  intro r c
  by_cases hr : r = j
  · subst r
    simpa using (analyticOnNhd_const
      (v := (Pi.single i (1 : Real) : Fin n → Real) c)
      (s := U) (E := E))
  · simpa [Matrix.updateRow, hr] using hF r c

theorem analyticOnNhd_matrix_inv_coord_of_coords {n : Nat}
    {F : E → Matrix (Fin n) (Fin n) Real}
    (hF : ∀ i j, AnalyticOnNhd Real (fun x => F x i j) U)
    (hdet : ∀ x ∈ U, (F x).det ≠ 0) (i j : Fin n) :
    AnalyticOnNhd Real (fun x => (F x)⁻¹ i j) U := by
  have hdet_analytic := analyticOnNhd_matrix_det_of_coords hF
  have hdet_inv : AnalyticOnNhd Real (fun x => ((F x).det)⁻¹) U := by
    exact hdet_analytic.inv hdet
  have hadj := analyticOnNhd_matrix_adjugate_coord_of_coords hF i j
  simpa [Matrix.inv_def, Ring.inverse_eq_inv, Pi.smul_apply, smul_eq_mul] using
    hdet_inv.mul hadj

end Analyticity

theorem analyticOnNhd_anchorChart_w_coord {m k d : Nat}
    (theta : Params (m + 1) k d) (pivot : Fin k ↪ Fin d) (i : Fin d) :
    AnalyticOnNhd Real (fun x : AnchorChartInput pivot => x.1 i)
      (anchorChartDomain theta pivot) := by
  let F : AnchorChartInput pivot →L[Real] Vec d :=
    ContinuousLinearMap.fst Real (Vec d) (AnchorFreeVec pivot)
  let P : Vec d →L[Real] Real := ContinuousLinearMap.proj i
  change AnalyticOnNhd Real ⇑(P.comp F) (anchorChartDomain theta pivot)
  exact (P.comp F).analyticOnNhd _

theorem analyticOnNhd_anchorChart_vhat_coord {m k d : Nat}
    (theta : Params (m + 1) k d) (pivot : Fin k ↪ Fin d)
    (i : AnchorFreeCoord pivot) :
    AnalyticOnNhd Real (fun x : AnchorChartInput pivot => x.2 i)
      (anchorChartDomain theta pivot) := by
  let F : AnchorChartInput pivot →L[Real] AnchorFreeVec pivot :=
    ContinuousLinearMap.snd Real (Vec d) (AnchorFreeVec pivot)
  let P : AnchorFreeVec pivot →L[Real] Real := ContinuousLinearMap.proj i
  change AnalyticOnNhd Real ⇑(P.comp F) (anchorChartDomain theta pivot)
  exact (P.comp F).analyticOnNhd _

theorem analyticOnNhd_anchorGradient_coord {m k d : Nat}
    (theta : Params (m + 1) k d) (pivot : Fin k ↪ Fin d)
    (a : Fin k) (i : Fin d) :
    AnalyticOnNhd Real
      (fun x : AnchorChartInput pivot => anchorGradient theta x.1 a i)
      (anchorChartDomain theta pivot) := by
  simp only [anchorGradient, Matrix.mulVec, dotProduct]
  apply Finset.analyticOnNhd_fun_sum
  intro j _hj
  exact (analyticOnNhd_const
      (v := (attentionMatrix theta 0 a)ᵀ i j)).mul
    (analyticOnNhd_anchorChart_w_coord theta pivot j)

theorem analyticOnNhd_anchorPivotMatrix_coord {m k d : Nat}
    (theta : Params (m + 1) k d) (pivot : Fin k ↪ Fin d)
    (a b : Fin k) :
    AnalyticOnNhd Real
      (fun x : AnchorChartInput pivot =>
        anchorPivotMatrix theta x.1 pivot a b)
      (anchorChartDomain theta pivot) := by
  simpa using analyticOnNhd_anchorGradient_coord theta pivot a (pivot b)

theorem analyticOnNhd_anchorFreeMulVec_coord {m k d : Nat}
    (theta : Params (m + 1) k d) (pivot : Fin k ↪ Fin d)
    (a : Fin k) :
    AnalyticOnNhd Real
      (fun x : AnchorChartInput pivot =>
        (anchorFreeMatrix theta x.1 pivot *ᵥ x.2) a)
      (anchorChartDomain theta pivot) := by
  simp only [Matrix.mulVec, anchorFreeMatrix_apply]
  apply Finset.analyticOnNhd_fun_sum
  intro i _hi
  exact (analyticOnNhd_anchorGradient_coord theta pivot a i.1).mul
    (analyticOnNhd_anchorChart_vhat_coord theta pivot i)

theorem analyticOnNhd_anchorPivotInv_coord {m k d : Nat}
    (theta : Params (m + 1) k d) (pivot : Fin k ↪ Fin d)
    (a b : Fin k) :
    AnalyticOnNhd Real
      (fun x : AnchorChartInput pivot =>
        (anchorPivotMatrix theta x.1 pivot)⁻¹ a b)
      (anchorChartDomain theta pivot) := by
  apply analyticOnNhd_matrix_inv_coord_of_coords
  · exact analyticOnNhd_anchorPivotMatrix_coord theta pivot
  · intro x hx
    exact hx

theorem analyticOnNhd_anchorGamma_pivotCoord {m k d : Nat}
    (theta : Params (m + 1) k d) (pivot : Fin k ↪ Fin d)
    (b : Fin k) :
    AnalyticOnNhd Real
      (fun x : AnchorChartInput pivot =>
        anchorGamma theta pivot x.1 x.2 (pivot b))
      (anchorChartDomain theta pivot) := by
  simp only [anchorGamma, anchorInsert_pivot, Pi.neg_apply, Matrix.mulVec,
    dotProduct]
  apply AnalyticOnNhd.neg
  apply Finset.analyticOnNhd_fun_sum
  intro a _ha
  exact (analyticOnNhd_anchorPivotInv_coord theta pivot b a).mul
    (analyticOnNhd_anchorFreeMulVec_coord theta pivot a)

theorem analyticOnNhd_anchorGamma_coord {m k d : Nat}
    (theta : Params (m + 1) k d) (pivot : Fin k ↪ Fin d)
    (i : Fin d) :
    AnalyticOnNhd Real
      (fun x : AnchorChartInput pivot =>
        anchorGamma theta pivot x.1 x.2 i)
      (anchorChartDomain theta pivot) := by
  obtain ⟨b | j, hij⟩ := (anchorCoordEquiv pivot).surjective i
  · subst i
    exact analyticOnNhd_anchorGamma_pivotCoord theta pivot b
  · subst i
    simpa [anchorGamma] using
      analyticOnNhd_anchorChart_vhat_coord theta pivot j

theorem analyticOnNhd_anchorGamma {m k d : Nat}
    (theta : Params (m + 1) k d) (pivot : Fin k ↪ Fin d) :
    AnalyticOnNhd Real
      (fun x : AnchorChartInput pivot => anchorGamma theta pivot x.1 x.2)
      (anchorChartDomain theta pivot) := by
  apply AnalyticOnNhd.pi
  intro i
  exact analyticOnNhd_anchorGamma_coord theta pivot i

theorem analyticOnNhd_anchorChart {m k d : Nat}
    (theta : Params (m + 1) k d) (pivot : Fin k ↪ Fin d) :
    AnalyticOnNhd Real (anchorChart theta pivot)
      (anchorChartDomain theta pivot) := by
  have hw : AnalyticOnNhd Real
      (fun x : AnchorChartInput pivot => x.1)
      (anchorChartDomain theta pivot) := by
    apply AnalyticOnNhd.pi
    exact analyticOnNhd_anchorChart_w_coord theta pivot
  exact hw.prod (analyticOnNhd_anchorGamma theta pivot)

theorem continuousOn_anchorGamma {m k d : Nat}
    (theta : Params (m + 1) k d) (pivot : Fin k ↪ Fin d) :
    ContinuousOn
      (fun x : AnchorChartInput pivot => anchorGamma theta pivot x.1 x.2)
      (anchorChartDomain theta pivot) :=
  (analyticOnNhd_anchorGamma theta pivot).continuousOn

theorem continuousOn_anchorChart {m k d : Nat}
    (theta : Params (m + 1) k d) (pivot : Fin k ↪ Fin d) :
    ContinuousOn (anchorChart theta pivot)
      (anchorChartDomain theta pivot) :=
  (analyticOnNhd_anchorChart theta pivot).continuousOn

/-! ## Anchor Gram determinant `δ(w) = det(Γ(w)Γ(w)ᵀ)`

The anchor Gram matrix is the `k × k` product of the anchor gradient matrix with
its transpose.  Its determinant is nonnegative (Gram/positive-semidefinite) and
is nonzero exactly when the anchor gradients are linearly independent, so it is
strictly positive iff they are independent.  This is TeX `δ(w)`. -/

/-- The anchor Gram matrix `Γ(w) Γ(w)ᵀ`. -/
noncomputable def anchorGramMatrix {m k d : Nat}
    (theta : Params (m + 1) k d) (w : Vec d) : Matrix (Fin k) (Fin k) Real :=
  anchorGradientMatrix theta w * (anchorGradientMatrix theta w)ᵀ

/-- TeX `δ(w) = det(Γ(w) Γ(w)ᵀ)`. -/
noncomputable def anchorGramDet {m k d : Nat}
    (theta : Params (m + 1) k d) (w : Vec d) : Real :=
  (anchorGramMatrix theta w).det

theorem anchorGramMatrix_posSemidef {m k d : Nat}
    (theta : Params (m + 1) k d) (w : Vec d) :
    (anchorGramMatrix theta w).PosSemidef := by
  simpa [anchorGramMatrix] using
    Matrix.posSemidef_self_mul_conjTranspose (A := anchorGradientMatrix theta w)

theorem anchorGramDet_nonneg {m k d : Nat}
    (theta : Params (m + 1) k d) (w : Vec d) :
    0 ≤ anchorGramDet theta w :=
  (anchorGramMatrix_posSemidef theta w).det_nonneg

/-- A linear combination of anchor gradients is the transpose gradient matrix
applied to the coefficient vector. -/
theorem anchorGradient_smul_sum_eq_transpose_mulVec {m k d : Nat}
    (theta : Params (m + 1) k d) (w : Vec d) (c : Fin k → Real) :
    ∑ a, c a • anchorGradient theta w a =
      (anchorGradientMatrix theta w)ᵀ *ᵥ c := by
  ext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec,
    dotProduct, Matrix.transpose_apply, anchorGradientMatrix_apply]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

/-- The Gram determinant is nonzero exactly when the anchor gradients are
linearly independent. -/
theorem anchorGramDet_ne_zero_iff_linearIndependent {m k d : Nat}
    (theta : Params (m + 1) k d) (w : Vec d) :
    anchorGramDet theta w ≠ 0 ↔
      LinearIndependent Real (anchorGradient theta w) := by
  classical
  constructor
  · intro hdet
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have hGtc : (anchorGradientMatrix theta w)ᵀ *ᵥ c = 0 := by
      rw [← anchorGradient_smul_sum_eq_transpose_mulVec]; exact hc
    have hgram : anchorGramMatrix theta w *ᵥ c = 0 := by
      rw [anchorGramMatrix, ← Matrix.mulVec_mulVec, hGtc, Matrix.mulVec_zero]
    have hc0 : c = 0 :=
      Matrix.eq_zero_of_mulVec_eq_zero (by simpa [anchorGramDet] using hdet) hgram
    exact congr_fun hc0 i
  · intro hindep hdet0
    have hdet0' : (anchorGramMatrix theta w).det = 0 := by
      simpa [anchorGramDet] using hdet0
    obtain ⟨c, hcne, hc⟩ :=
      (Matrix.exists_mulVec_eq_zero_iff).mpr hdet0'
    rw [anchorGramMatrix] at hc
    have hgc : anchorGradientMatrix theta w *ᵥ
        ((anchorGradientMatrix theta w)ᵀ *ᵥ c) = 0 := by
      rw [Matrix.mulVec_mulVec]; exact hc
    have key : ∀ y : Fin d → Real,
        c ⬝ᵥ (anchorGradientMatrix theta w *ᵥ y) =
          ((anchorGradientMatrix theta w)ᵀ *ᵥ c) ⬝ᵥ y := by
      intro y
      rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
    have hself :
        ((anchorGradientMatrix theta w)ᵀ *ᵥ c) ⬝ᵥ
          ((anchorGradientMatrix theta w)ᵀ *ᵥ c) = 0 := by
      rw [← key ((anchorGradientMatrix theta w)ᵀ *ᵥ c), hgc, dotProduct_zero]
    have hzero : (anchorGradientMatrix theta w)ᵀ *ᵥ c = 0 :=
      dotProduct_self_eq_zero.mp hself
    rw [← anchorGradient_smul_sum_eq_transpose_mulVec] at hzero
    exact hcne (funext (Fintype.linearIndependent_iff.mp hindep c hzero))

theorem anchorGramDet_pos_of_linearIndependent {m k d : Nat}
    (theta : Params (m + 1) k d) (w : Vec d)
    (h : LinearIndependent Real (anchorGradient theta w)) :
    0 < anchorGramDet theta w :=
  lt_of_le_of_ne (anchorGramDet_nonneg theta w)
    (Ne.symm ((anchorGramDet_ne_zero_iff_linearIndependent theta w).mpr h))

theorem linearIndependent_anchorGradient_of_anchorGramDet_pos {m k d : Nat}
    (theta : Params (m + 1) k d) (w : Vec d)
    (h : 0 < anchorGramDet theta w) :
    LinearIndependent Real (anchorGradient theta w) :=
  (anchorGramDet_ne_zero_iff_linearIndependent theta w).mp h.ne'

/-- Independence of the anchor gradients forces `w ≠ 0` (given at least one
head): each gradient `(A'_{1a})ᵀ w` is nonzero, and it vanishes when `w = 0`. -/
theorem anchor_w_ne_zero_of_linearIndependent {m k d : Nat}
    (theta : Params (m + 1) k d) (w : Vec d)
    (h : LinearIndependent Real (anchorGradient theta w)) (a : Fin k) :
    w ≠ 0 := by
  intro hw
  refine h.ne_zero a ?_
  rw [hw]
  simp [anchorGradient]

/-- Continuity of the Gram determinant in `w` (it is a polynomial). -/
theorem continuous_anchorGramDet {m k d : Nat}
    (theta : Params (m + 1) k d) :
    Continuous (fun w : Vec d => anchorGramDet theta w) := by
  unfold anchorGramDet anchorGramMatrix
  apply Continuous.matrix_det
  refine continuous_matrix ?_
  intro a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, anchorGradientMatrix_apply,
    anchorGradient, Matrix.mulVec, dotProduct]
  fun_prop

/-! ## Ambient sign-region geometry

The multi-quadric sign region lives in `𝒬 × (0,1)^k`, where
`𝒬 = ⋂_a {(w,v) : wᵀA'_{1a}v = 0}`.  The solved-coordinate chart
`Φ(w, v̂, t) = (w, γ(w,v̂), t)` maps a product box in chart coordinates onto the
region, and the region is exactly the quadric slab cut by an ambient open
box. -/

/-- Ambient point `(w, v, t)` in `ℝ^d × ℝ^d × ℝ^k`. -/
abbrev MultiSignPoint (d k : Nat) := (Vec d × Vec d) × (Fin k → Real)

/-- Chart-source point `((w, v̂), t)`. -/
abbrev MultiSignChartInput {k d : Nat} (pivot : Fin k ↪ Fin d) :=
  AnchorChartInput pivot × (Fin k → Real)

/-- The multi-quadric solved-coordinate chart
`Φ(w, v̂, t) = (w, γ(w,v̂), t)`. -/
noncomputable def multiSignChart {m k d : Nat} (theta : Params (m + 1) k d)
    (pivot : Fin k ↪ Fin d) : MultiSignChartInput pivot → MultiSignPoint d k :=
  fun x => (anchorChart theta pivot x.1, x.2)

/-- The inverse projection `(w, v, t) ↦ (w, v̂, t)`. -/
def multiSignProjection {k d : Nat} (pivot : Fin k ↪ Fin d) :
    MultiSignPoint d k → MultiSignChartInput pivot :=
  fun p => (anchorChartProjection pivot p.1, p.2)

/-- TeX `𝒬 × (0,1)^k`. -/
def multiSignSlab {m k d : Nat} (theta : Params (m + 1) k d) :
    Set (MultiSignPoint d k) :=
  {p | (∀ a, anchorRow theta p.1.1 a p.1.2 = 0) ∧
    (∀ a, p.2 a ∈ Set.Ioo (0 : ℝ) 1)}

/-- The chart-source product box `B(w₀,ρ) × B(v̂₀,ρ) × ∏_a (t₀_a-ρ, t₀_a+ρ)`. -/
def multiSignSourceBox {k d : Nat} (pivot : Fin k ↪ Fin d)
    (w0 : Vec d) (vhat0 : AnchorFreeVec pivot) (t0 : Fin k → Real) (rho : Real) :
    Set (MultiSignChartInput pivot) :=
  {x | x.1.1 ∈ Metric.ball w0 rho ∧ x.1.2 ∈ Metric.ball vhat0 rho ∧
    (∀ a, x.2 a ∈ Set.Ioo (t0 a - rho) (t0 a + rho))}

/-- The ambient box `O_ρ` in `(w, v, t)` coordinates. -/
def multiSignAmbientBox {k d : Nat} (pivot : Fin k ↪ Fin d)
    (w0 : Vec d) (vhat0 : AnchorFreeVec pivot) (t0 : Fin k → Real) (rho : Real) :
    Set (MultiSignPoint d k) :=
  {p | p.1.1 ∈ Metric.ball w0 rho ∧
    anchorDelete pivot p.1.2 ∈ Metric.ball vhat0 rho ∧
    (∀ a, p.2 a ∈ Set.Ioo (t0 a - rho) (t0 a + rho))}

/-- The chart domain where the pivot minor is invertible. -/
def multiSignChartDomain {m k d : Nat} (theta : Params (m + 1) k d)
    (pivot : Fin k ↪ Fin d) : Set (MultiSignChartInput pivot) :=
  {x | x.1 ∈ anchorChartDomain theta pivot}

theorem continuous_anchorPivotDet {m k d : Nat}
    (theta : Params (m + 1) k d) (pivot : Fin k ↪ Fin d) :
    Continuous fun w : Vec d => (anchorPivotMatrix theta w pivot).det := by
  apply Continuous.matrix_det
  refine continuous_matrix ?_
  intro a b
  simp only [anchorPivotMatrix_apply, anchorGradient, Matrix.mulVec, dotProduct]
  fun_prop

theorem isOpen_anchorPivotDomain {m k d : Nat}
    (theta : Params (m + 1) k d) (pivot : Fin k ↪ Fin d) :
    IsOpen (anchorPivotDomain theta pivot) := by
  simpa [anchorPivotDomain, AnchorPivotInvertibleAt, Set.preimage] using
    (isOpen_ne.preimage (continuous_anchorPivotDet theta pivot))

theorem isOpen_anchorChartDomain {m k d : Nat}
    (theta : Params (m + 1) k d) (pivot : Fin k ↪ Fin d) :
    IsOpen (anchorChartDomain theta pivot) :=
  (isOpen_anchorPivotDomain theta pivot).preimage continuous_fst

theorem isOpen_multiSignChartDomain {m k d : Nat}
    (theta : Params (m + 1) k d) (pivot : Fin k ↪ Fin d) :
    IsOpen (multiSignChartDomain theta pivot) :=
  (isOpen_anchorChartDomain theta pivot).preimage continuous_fst

theorem continuous_multiSignProjection {k d : Nat} (pivot : Fin k ↪ Fin d) :
    Continuous (multiSignProjection pivot :
      MultiSignPoint d k → MultiSignChartInput pivot) :=
  ((continuous_anchorChartProjection pivot).comp continuous_fst).prodMk
    continuous_snd

theorem continuousOn_multiSignChart {m k d : Nat}
    (theta : Params (m + 1) k d) (pivot : Fin k ↪ Fin d) :
    ContinuousOn (multiSignChart theta pivot)
      (multiSignChartDomain theta pivot) := by
  apply ContinuousOn.prodMk
  · exact (continuousOn_anchorChart theta pivot).comp
      continuous_fst.continuousOn (fun x hx => hx)
  · exact continuous_snd.continuousOn

/-- The chart image of the source box is exactly the quadric slab cut by the
ambient box.  This is the ambient identity `𝒰 = (𝒬 × (0,1)^k) ∩ O_ρ`. -/
theorem multiSignChart_image_sourceBox {m k d : Nat}
    (theta : Params (m + 1) k d) (pivot : Fin k ↪ Fin d)
    (w0 : Vec d) (vhat0 : AnchorFreeVec pivot) (t0 : Fin k → Real) (rho : Real)
    (hball : Metric.ball w0 rho ⊆ anchorPivotDomain theta pivot)
    (hinterval : ∀ a, Set.Ioo (t0 a - rho) (t0 a + rho) ⊆ Set.Ioo (0 : ℝ) 1) :
    multiSignChart theta pivot '' multiSignSourceBox pivot w0 vhat0 t0 rho =
      multiSignSlab theta ∩ multiSignAmbientBox pivot w0 vhat0 t0 rho := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases x with ⟨⟨w, vhat⟩, t⟩
    rcases hx with ⟨hw, hvhat, ht⟩
    have hwdom : w ∈ anchorPivotDomain theta pivot := hball hw
    simp only [multiSignChart, anchorChart, multiSignSlab, multiSignAmbientBox,
      Set.mem_inter_iff, Set.mem_setOf_eq]
    refine ⟨⟨fun a => ?_, fun a => hinterval a (ht a)⟩, hw, ?_, ht⟩
    · exact anchorRow_gamma_eq_zero theta pivot w vhat hwdom a
    · rw [anchorDelete_gamma]; exact hvhat
  · rintro ⟨⟨hquad, ht01⟩, hw, hvhat, ht⟩
    rcases p with ⟨⟨w, v⟩, t⟩
    have hwdom : w ∈ anchorPivotDomain theta pivot := hball hw
    refine ⟨((w, anchorDelete pivot v), t), ⟨hw, hvhat, ht⟩, ?_⟩
    have hanchor : anchorGradientMatrix theta w *ᵥ v = 0 := by
      funext a; simpa using hquad a
    have hchart := anchorChart_projection_eq_of_anchor_eq theta pivot (w, v)
      hwdom hanchor
    refine Prod.ext ?_ rfl
    calc anchorChart theta pivot (w, anchorDelete pivot v)
        = anchorChart theta pivot (anchorChartProjection pivot (w, v)) := rfl
      _ = (w, v) := hchart

theorem isOpen_multiSignAmbientBox {k d : Nat} (pivot : Fin k ↪ Fin d)
    (w0 : Vec d) (vhat0 : AnchorFreeVec pivot) (t0 : Fin k → Real) (rho : Real) :
    IsOpen (multiSignAmbientBox pivot w0 vhat0 t0 rho) := by
  have hw : Continuous fun p : MultiSignPoint d k => p.1.1 :=
    continuous_fst.comp continuous_fst
  have hv : Continuous fun p : MultiSignPoint d k => p.1.2 :=
    continuous_snd.comp continuous_fst
  have hA : IsOpen {p : MultiSignPoint d k | p.1.1 ∈ Metric.ball w0 rho} :=
    Metric.isOpen_ball.preimage hw
  have hB : IsOpen {p : MultiSignPoint d k |
      anchorDelete pivot p.1.2 ∈ Metric.ball vhat0 rho} :=
    Metric.isOpen_ball.preimage ((continuous_anchorDelete pivot).comp hv)
  have hC : IsOpen {p : MultiSignPoint d k |
      ∀ a, p.2 a ∈ Set.Ioo (t0 a - rho) (t0 a + rho)} := by
    have hset : {p : MultiSignPoint d k |
        ∀ a, p.2 a ∈ Set.Ioo (t0 a - rho) (t0 a + rho)} =
          ⋂ a, {p : MultiSignPoint d k | p.2 a ∈ Set.Ioo (t0 a - rho) (t0 a + rho)} := by
      ext p; simp
    rw [hset]
    exact isOpen_iInter_of_finite fun a =>
      isOpen_Ioo.preimage ((continuous_apply a).comp continuous_snd)
  simpa [multiSignAmbientBox, Set.setOf_and] using hA.inter (hB.inter hC)

theorem convex_multiSignSourceBox {k d : Nat} (pivot : Fin k ↪ Fin d)
    (w0 : Vec d) (vhat0 : AnchorFreeVec pivot) (t0 : Fin k → Real) (rho : Real) :
    Convex ℝ (multiSignSourceBox pivot w0 vhat0 t0 rho) := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨hxw, hxv, hxt⟩
  rcases hy with ⟨hyw, hyv, hyt⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa using convex_ball w0 rho hxw hyw ha hb hab
  · simpa using convex_ball vhat0 rho hxv hyv ha hb hab
  · intro c
    have hc := convex_Ioo (𝕜 := ℝ) (t0 c - rho) (t0 c + rho) (hxt c) (hyt c) ha hb hab
    simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hc

/-! ## Strict sign locus (deeper primed levels negative, Gram positive) -/

/-- Continuity of a deeper primed level value `g_{jb}(w,v,t)` in `(w,v,t)`. -/
theorem continuous_multiSignLevelValue {n k d : Nat}
    (theta : Params (n + 1) k d) (jb : LevelRowIndex (n + 1) k) :
    Continuous fun p : MultiSignPoint d k =>
      levelRow theta p.2 p.1.1 jb p.1.2 := by
  have hfun : (fun p : MultiSignPoint d k => levelRow theta p.2 p.1.1 jb p.1.2)
      = (fun p : MultiSignPoint d k =>
          (levelGradient theta p.2 p.1.1 jb) ⬝ᵥ p.1.2 +
            levelConstant theta p.2 p.1.1 jb) := by
    funext p
    exact levelRow_eq_dotProduct_add_constant theta p.2 p.1.1 jb p.1.2
  rw [hfun]
  unfold levelGradient levelConstant dialContrast dialValueMatrix
  simp only [matrixBilin_apply, Matrix.mulVec, dotProduct, Matrix.sub_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.transpose_apply]
  fun_prop

/-- TeX open set `O`: every deeper primed level is negative and the anchor Gram
determinant is positive. -/
def multiSignStrictSet {n k d : Nat} (theta : Params (n + 1) k d) :
    Set (MultiSignPoint d k) :=
  {p | (∀ jb : LevelRowIndex (n + 1) k,
      levelRow theta p.2 p.1.1 jb p.1.2 < 0) ∧
    0 < anchorGramDet theta p.1.1}

theorem isOpen_multiSignStrictSet {n k d : Nat} (theta : Params (n + 1) k d) :
    IsOpen (multiSignStrictSet theta) := by
  have hgram : IsOpen {p : MultiSignPoint d k | 0 < anchorGramDet theta p.1.1} :=
    isOpen_Ioi.preimage
      ((continuous_anchorGramDet theta).comp (continuous_fst.comp continuous_fst))
  have hlev : IsOpen {p : MultiSignPoint d k |
      ∀ jb : LevelRowIndex (n + 1) k, levelRow theta p.2 p.1.1 jb p.1.2 < 0} := by
    have hset : {p : MultiSignPoint d k |
        ∀ jb : LevelRowIndex (n + 1) k, levelRow theta p.2 p.1.1 jb p.1.2 < 0} =
          ⋂ jb : LevelRowIndex (n + 1) k,
            {p : MultiSignPoint d k | levelRow theta p.2 p.1.1 jb p.1.2 < 0} := by
      ext p; simp
    rw [hset]
    exact isOpen_iInter_of_finite fun jb =>
      isOpen_Iio.preimage (continuous_multiSignLevelValue theta jb)
  simpa [multiSignStrictSet, Set.setOf_and] using hlev.inter hgram

/-- The chart-source box lies in a metric ball of the chart center. -/
theorem multiSignSourceBox_subset_ball {k d : Nat} (pivot : Fin k ↪ Fin d)
    (w0 : Vec d) (vhat0 : AnchorFreeVec pivot) (t0 : Fin k → Real)
    (rho eps : Real) (hrho : 0 < rho) (hle : rho ≤ eps) :
    multiSignSourceBox pivot w0 vhat0 t0 rho ⊆
      Metric.ball ((w0, vhat0), t0) eps := by
  intro x hx
  rcases hx with ⟨hw, hv, ht⟩
  rw [Metric.mem_ball, Prod.dist_eq, Prod.dist_eq, max_lt_iff, max_lt_iff]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact lt_of_lt_of_le (Metric.mem_ball.mp hw) hle
  · exact lt_of_lt_of_le (Metric.mem_ball.mp hv) hle
  · rw [dist_pi_lt_iff (lt_of_lt_of_le hrho hle)]
    intro a
    have ha := ht a
    rw [Set.mem_Ioo] at ha
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith [ha.1, hle], by linarith [ha.2, hle]⟩

/-- A positive box radius keeping all dial intervals inside `(0,1)`. -/
theorem exists_rho_interval {k : Nat} (t0 : Fin k → Real)
    (ht : ∀ a, t0 a ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ rho : Real, 0 < rho ∧
      ∀ a, Set.Ioo (t0 a - rho) (t0 a + rho) ⊆ Set.Ioo (0 : ℝ) 1 := by
  classical
  rcases isEmpty_or_nonempty (Fin k) with hempty | hne
  · exact ⟨1, one_pos, fun a => (hempty.false a).elim⟩
  · let f : Fin k → Real := fun a => min (t0 a) (1 - t0 a)
    have hfpos : ∀ a, 0 < f a := fun a =>
      lt_min (ht a).1 (by have := (ht a).2; linarith)
    obtain ⟨a0⟩ := hne
    let rho := Finset.univ.inf' ⟨a0, Finset.mem_univ a0⟩ f
    have hrhopos : 0 < rho := (Finset.lt_inf'_iff _).mpr (fun a _ => hfpos a)
    refine ⟨rho, hrhopos, fun a => ?_⟩
    have hra : rho ≤ f a := Finset.inf'_le f (Finset.mem_univ a)
    intro y hy
    rw [Set.mem_Ioo] at hy ⊢
    have h1 : rho ≤ t0 a := le_trans hra (min_le_left _ _)
    have h2 : rho ≤ 1 - t0 a := le_trans hra (min_le_right _ _)
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩

/-- Projection is a left inverse of the chart. -/
@[simp] theorem multiSignProjection_chart {m k d : Nat}
    (theta : Params (m + 1) k d) (pivot : Fin k ↪ Fin d)
    (x : MultiSignChartInput pivot) :
    multiSignProjection pivot (multiSignChart theta pivot x) = x := by
  rcases x with ⟨⟨w, vhat⟩, t⟩
  simp [multiSignProjection, multiSignChart, anchorChartProjection_chart]

/-- A multi-dial certificate has a nonzero Gram evaluation with the dial tuple
already inside the open box `(0,1)^k` (TeX Step 1). -/
theorem exists_gramDet_ne_zero_with_t_mem_Ioo {n k d : Nat}
    (theta : Params (n + 1) k d) (hcert : MultiDialCertificate theta) :
    ∃ t : Fin k → Real, ∃ w : Vec d,
      (∀ a, t a ∈ Set.Ioo (0 : ℝ) 1) ∧ multiDialGramDet theta t w ≠ 0 := by
  classical
  have hpoly : multiDialGramPoly theta ≠ 0 :=
    (multiDialCertificate_iff_gramPoly_ne_zero theta).mp hcert
  have hdense := dense_compl_zero_set (multiDialGramPoly theta) hpoly
  set Box : Set (MultiDialAuxVar k d → Real) :=
    {rho | ∀ a : Fin k, rho (Sum.inl a) ∈ Set.Ioo (0 : ℝ) 1} with hBox
  have hBoxOpen : IsOpen Box := by
    have hset : Box = ⋂ a : Fin k,
        {rho : MultiDialAuxVar k d → Real | rho (Sum.inl a) ∈ Set.Ioo (0 : ℝ) 1} := by
      ext rho; simp [hBox]
    rw [hset]
    exact isOpen_iInter_of_finite fun a =>
      isOpen_Ioo.preimage (continuous_apply (Sum.inl a))
  have hBoxNe : Box.Nonempty := by
    refine ⟨fun x => Sum.elim (fun _ => (1 / 2 : ℝ)) (fun _ => 0) x, ?_⟩
    intro a; constructor <;> norm_num
  obtain ⟨rho, hrho_box, hrho_ne⟩ :=
    hdense.inter_open_nonempty Box hBoxOpen hBoxNe
  refine ⟨fun a => rho (Sum.inl a), fun i => rho (Sum.inr i), hrho_box, ?_⟩
  have heval : multiDialAuxEval (fun a => rho (Sum.inl a))
      (fun i => rho (Sum.inr i)) = rho := by
    funext x; rcases x with a | i <;> rfl
  rw [← eval_multiDialGramPoly, heval]
  exact hrho_ne

/-! ## The multi-dial sign region (TeX Lemma `lem:multi-sign-region`) -/

/-- The full sign-region datum for the multi-quadric no-skip model: the pinned
center `(t°,w°,v°)`, the coordinate block `I⋆` (as an embedding `pivot`), the
radius `ρ`, the box `B_ρ` (recorded through its data), the region `𝒰`, and the
ambient identity, chart image, center membership, and strict sign locus. -/
structure MultiDialSignRegion {n k d : Nat} (theta : Params (n + 1) k d) where
  /-- The pinned center dial tuple `t°`. -/
  t0 : Fin k → Real
  /-- The pinned center probe `w°`. -/
  w0 : Vec d
  /-- The pinned center solved point `v°`. -/
  v0 : Vec d
  /-- The coordinate block `I⋆`. -/
  pivot : Fin k ↪ Fin d
  /-- The deleted-coordinate center `v̂°`. -/
  vHat : AnchorFreeVec pivot
  /-- The box radius `ρ`. -/
  rho : Real
  /-- The region `𝒰 = Φ(B_ρ)`. -/
  region : Set (MultiSignPoint d k)
  rho_pos : 0 < rho
  vHat_eq : vHat = anchorDelete pivot v0
  pivot_invertibleAt : AnchorPivotInvertibleAt theta pivot w0
  interval_subset : ∀ a, Set.Ioo (t0 a - rho) (t0 a + rho) ⊆ Set.Ioo (0 : ℝ) 1
  ball_subset_domain : Metric.ball w0 rho ⊆ anchorPivotDomain theta pivot
  region_eq_image :
    region = multiSignChart theta pivot '' multiSignSourceBox pivot w0 vHat t0 rho
  ambient_identity :
    region = multiSignSlab theta ∩ multiSignAmbientBox pivot w0 vHat t0 rho
  center_mem : ((w0, v0), t0) ∈ region
  strict_subset : region ⊆ multiSignStrictSet theta

/-- Existence of the multi-dial sign region from the multi-dial certificate
(TeX Lemma `lem:multi-sign-region`, parts (a)–(d)). -/
theorem MultiDialCertificate.exists_multiDialSignRegion {n k d : Nat}
    {theta : Params (n + 1) k d} (hcert : MultiDialCertificate theta) :
    Nonempty (MultiDialSignRegion theta) := by
  classical
  obtain ⟨t0, w0, ht0, hgram⟩ :=
    exists_gramDet_ne_zero_with_t_mem_Ioo theta hcert
  set v0 := multiDialPinnedCenter theta t0 w0 with hv0def
  have hanchor0 : ∀ a, anchorRow theta w0 a v0 = 0 := fun a =>
    multiDialPinnedCenter_anchorRow_eq_zero_of_gramDet_ne_zero theta t0 w0 hgram a
  have hlevel0 : ∀ jb, levelRow theta t0 w0 jb v0 = -1 := fun jb =>
    multiDialPinnedCenter_levelRow_eq_neg_one_of_gramDet_ne_zero theta t0 w0 hgram jb
  have hindep0 : LinearIndependent Real (anchorGradient theta w0) :=
    linearIndependent_anchorGradient_of_gramDet_ne_zero theta t0 w0 hgram
  have hgrampos0 : 0 < anchorGramDet theta w0 :=
    anchorGramDet_pos_of_linearIndependent theta w0 hindep0
  set P := anchorCoordinatePivotOfGram theta t0 w0 hgram with hP
  set pivot := P.pivot with hpiv
  have hinvAt : AnchorPivotInvertibleAt theta pivot w0 := P.invertibleAt
  have hw0dom : w0 ∈ anchorPivotDomain theta pivot := hinvAt
  set vHat := anchorDelete pivot v0 with hvhat
  have hgamma : anchorGamma theta pivot w0 vHat = v0 :=
    anchorGamma_eq_of_delete_eq_of_anchorRows_eq_zero theta pivot w0 v0 vHat
      hw0dom rfl hanchor0
  have hchart0 : multiSignChart theta pivot ((w0, vHat), t0) = ((w0, v0), t0) := by
    simp only [multiSignChart, anchorChart]
    rw [hgamma]
  have hstrict0 : ((w0, v0), t0) ∈ multiSignStrictSet theta := by
    refine ⟨fun jb => ?_, hgrampos0⟩
    rw [hlevel0 jb]; norm_num
  have hx0dom : ((w0, vHat), t0) ∈ multiSignChartDomain theta pivot := hw0dom
  have hWopen : IsOpen (multiSignChartDomain theta pivot ∩
      (multiSignChart theta pivot) ⁻¹' (multiSignStrictSet theta)) :=
    (continuousOn_multiSignChart theta pivot).isOpen_inter_preimage
      (isOpen_multiSignChartDomain theta pivot) (isOpen_multiSignStrictSet theta)
  have hx0W : ((w0, vHat), t0) ∈ multiSignChartDomain theta pivot ∩
      (multiSignChart theta pivot) ⁻¹' (multiSignStrictSet theta) := by
    refine ⟨hx0dom, ?_⟩
    rw [Set.mem_preimage, hchart0]; exact hstrict0
  obtain ⟨rhoStr, hrhoStr_pos, hrhoStr_sub⟩ :=
    Metric.mem_nhds_iff.mp (hWopen.mem_nhds hx0W)
  obtain ⟨rhoDom, hrhoDom_pos, hrhoDom_sub⟩ :=
    Metric.isOpen_iff.mp (isOpen_anchorPivotDomain theta pivot) w0 hw0dom
  obtain ⟨rhoInt, hrhoInt_pos, hrhoInt_sub⟩ := exists_rho_interval t0 ht0
  set rho := min rhoDom (min rhoInt rhoStr) with hrhodef
  have hrho_pos : 0 < rho :=
    lt_min hrhoDom_pos (lt_min hrhoInt_pos hrhoStr_pos)
  have hrho_le_dom : rho ≤ rhoDom := min_le_left _ _
  have hrho_le_int : rho ≤ rhoInt := le_trans (min_le_right _ _) (min_le_left _ _)
  have hrho_le_str : rho ≤ rhoStr := le_trans (min_le_right _ _) (min_le_right _ _)
  have hball_dom : Metric.ball w0 rho ⊆ anchorPivotDomain theta pivot :=
    (Metric.ball_subset_ball hrho_le_dom).trans hrhoDom_sub
  have hint_sub : ∀ a, Set.Ioo (t0 a - rho) (t0 a + rho) ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro a
    refine subset_trans (Set.Ioo_subset_Ioo ?_ ?_) (hrhoInt_sub a)
    · linarith [hrho_le_int]
    · linarith [hrho_le_int]
  have himage :
      multiSignChart theta pivot '' multiSignSourceBox pivot w0 vHat t0 rho =
        multiSignSlab theta ∩ multiSignAmbientBox pivot w0 vHat t0 rho :=
    multiSignChart_image_sourceBox theta pivot w0 vHat t0 rho hball_dom hint_sub
  have hx0src : ((w0, vHat), t0) ∈ multiSignSourceBox pivot w0 vHat t0 rho := by
    refine ⟨Metric.mem_ball_self hrho_pos, Metric.mem_ball_self hrho_pos, fun a => ?_⟩
    rw [Set.mem_Ioo]; exact ⟨by linarith [hrho_pos], by linarith [hrho_pos]⟩
  have hcenter_mem :
      ((w0, v0), t0) ∈ multiSignChart theta pivot '' multiSignSourceBox pivot w0 vHat t0 rho := by
    rw [← hchart0]; exact ⟨_, hx0src, rfl⟩
  have hstrict_sub :
      multiSignChart theta pivot '' multiSignSourceBox pivot w0 vHat t0 rho ⊆
        multiSignStrictSet theta := by
    rintro p ⟨x, hx, rfl⟩
    have hxball : x ∈ Metric.ball ((w0, vHat), t0) rhoStr :=
      multiSignSourceBox_subset_ball pivot w0 vHat t0 rho rhoStr hrho_pos hrho_le_str hx
    exact (hrhoStr_sub hxball).2
  exact ⟨{
    t0 := t0, w0 := w0, v0 := v0, pivot := pivot, vHat := vHat, rho := rho,
    region := multiSignChart theta pivot '' multiSignSourceBox pivot w0 vHat t0 rho,
    rho_pos := hrho_pos,
    vHat_eq := hvhat,
    pivot_invertibleAt := hinvAt,
    interval_subset := hint_sub,
    ball_subset_domain := hball_dom,
    region_eq_image := rfl,
    ambient_identity := himage,
    center_mem := hcenter_mem,
    strict_subset := hstrict_sub }⟩

namespace MultiDialSignRegion

variable {n k d : Nat} {theta : Params (n + 1) k d}

/-- (c) The region is nonempty. -/
theorem nonempty (D : MultiDialSignRegion theta) : D.region.Nonempty :=
  ⟨_, D.center_mem⟩

/-- The region lies in the quadric slab `𝒬 × (0,1)^k`. -/
theorem region_subset_slab (D : MultiDialSignRegion theta) :
    D.region ⊆ multiSignSlab theta := by
  rw [D.ambient_identity]; exact Set.inter_subset_left

/-- (c) The region is relatively open in `𝒬 × (0,1)^k`, equal to the slab cut by
the ambient box `O_ρ`. -/
theorem relativelyOpen (D : MultiDialSignRegion theta) :
    RelativelyOpenIn D.region (multiSignSlab theta) :=
  ⟨multiSignAmbientBox D.pivot D.w0 D.vHat D.t0 D.rho,
    isOpen_multiSignAmbientBox _ _ _ _ _,
    D.ambient_identity.trans (Set.inter_comm _ _)⟩

/-- (c) The region is connected (continuous image of a convex box). -/
theorem isPreconnected (D : MultiDialSignRegion theta) :
    IsPreconnected D.region := by
  rw [D.region_eq_image]
  have hf : ContinuousOn (multiSignChart theta D.pivot)
      (multiSignSourceBox D.pivot D.w0 D.vHat D.t0 D.rho) :=
    (continuousOn_multiSignChart theta D.pivot).mono
      (fun x hx => D.ball_subset_domain hx.1)
  exact (convex_multiSignSourceBox D.pivot D.w0 D.vHat D.t0 D.rho).isPreconnected.image
    _ hf

/-- (c) `Φ|_{B_ρ}` is a bijection onto `𝒰`. -/
theorem chart_bijOn (D : MultiDialSignRegion theta) :
    Set.BijOn (multiSignChart theta D.pivot)
      (multiSignSourceBox D.pivot D.w0 D.vHat D.t0 D.rho) D.region := by
  rw [D.region_eq_image]
  refine ⟨fun x hx => ⟨x, hx, rfl⟩, ?_, fun p hp => hp⟩
  intro x _ y _ hxy
  have := congrArg (multiSignProjection D.pivot) hxy
  simpa using this

/-- (c) The chart inverse is `(w,v,t) ↦ (w,v̂,t)`. -/
theorem chart_projection_inverse (D : MultiDialSignRegion theta) :
    ∀ p ∈ D.region,
      multiSignChart theta D.pivot (multiSignProjection D.pivot p) = p := by
  rw [D.region_eq_image]
  rintro p ⟨x, hx, rfl⟩
  rw [multiSignProjection_chart]

/-- Continuity of `Φ` on the chart domain. -/
theorem chart_continuousOn (D : MultiDialSignRegion theta) :
    ContinuousOn (multiSignChart theta D.pivot)
      (multiSignChartDomain theta D.pivot) :=
  continuousOn_multiSignChart theta D.pivot

/-- Continuity of the chart inverse projection. -/
theorem projection_continuous (D : MultiDialSignRegion theta) :
    Continuous (multiSignProjection D.pivot :
      MultiSignPoint d k → MultiSignChartInput D.pivot) :=
  continuous_multiSignProjection D.pivot

/-- The center anchor rows vanish (the center lies on `𝒬`). -/
theorem center_anchorRow (D : MultiDialSignRegion theta) (a : Fin k) :
    anchorRow theta D.w0 a D.v0 = 0 :=
  (D.region_subset_slab D.center_mem).1 a

/-- (b)/(c) The chart sends the pinned center chart-input to the center point. -/
theorem center_chart (D : MultiDialSignRegion theta) :
    multiSignChart theta D.pivot ((D.w0, D.vHat), D.t0) = ((D.w0, D.v0), D.t0) := by
  have hgamma : anchorGamma theta D.pivot D.w0 D.vHat = D.v0 := by
    rw [D.vHat_eq]
    exact anchorGamma_eq_of_delete_eq_of_anchorRows_eq_zero theta D.pivot D.w0
      D.v0 (anchorDelete D.pivot D.v0) D.pivot_invertibleAt rfl
      (fun a => D.center_anchorRow a)
  simp only [multiSignChart, anchorChart]
  rw [hgamma]

/-- (d) Every deeper primed level is negative on `𝒰`. -/
theorem levelRow_neg (D : MultiDialSignRegion theta) {p : MultiSignPoint d k}
    (hp : p ∈ D.region) (jb : LevelRowIndex (n + 1) k) :
    levelRow theta p.2 p.1.1 jb p.1.2 < 0 :=
  (D.strict_subset hp).1 jb

/-- (d) The anchor Gram determinant `δ(w) = det(Γ(w)Γ(w)ᵀ)` is positive on `𝒰`. -/
theorem anchorGramDet_pos (D : MultiDialSignRegion theta) {p : MultiSignPoint d k}
    (hp : p ∈ D.region) :
    0 < anchorGramDet theta p.1.1 :=
  (D.strict_subset hp).2

/-- (d) The `k` anchor gradients `(A'_{1a})ᵀ w` are linearly independent on `𝒰`. -/
theorem linearIndependent_anchorGradient (D : MultiDialSignRegion theta)
    {p : MultiSignPoint d k} (hp : p ∈ D.region) :
    LinearIndependent Real (anchorGradient theta p.1.1) :=
  linearIndependent_anchorGradient_of_anchorGramDet_pos theta p.1.1
    (D.anchorGramDet_pos hp)

/-- (d) `w ≠ 0` on `𝒰` (anchor independence forces it, given a head). -/
theorem w_ne_zero (D : MultiDialSignRegion theta) {p : MultiSignPoint d k}
    (hp : p ∈ D.region) (a : Fin k) :
    p.1.1 ≠ 0 :=
  anchor_w_ne_zero_of_linearIndependent theta p.1.1
    (D.linearIndependent_anchorGradient hp) a

end MultiDialSignRegion

end

end TransformerIdentifiability.NLayer.NoSkip
