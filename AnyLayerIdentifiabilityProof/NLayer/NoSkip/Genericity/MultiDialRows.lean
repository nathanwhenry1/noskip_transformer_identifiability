import AnyLayerIdentifiabilityProof.NLayer.NoSkip.DimensionThreshold
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.FormalStreams
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.SharedToolbox

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.NoSkip

/-!
# Simultaneous multi-dial row indices

For a positive-depth `m`-layer tail, the certificate has `k` anchor rows and
`(m-1) * k` deeper-level rows.  The sum ordering fixes anchors first and levels
lexicographically.  The former transversality family is deliberately absent:
at one head its adjugate repair is provably proportional to the anchor column.
-/

abbrev AnchorRowIndex (k : Nat) := Fin k
abbrev LevelRowIndex (m k : Nat) := Fin (m - 1) × Fin k

/-- Disjoint union of the two simultaneous-certificate row families. -/
abbrev MultiDialRow (m k : Nat) :=
  AnchorRowIndex k ⊕ LevelRowIndex m k

namespace MultiDialRow

def anchor {m k : Nat} (a : AnchorRowIndex k) : MultiDialRow m k := Sum.inl a
def level {m k : Nat} (jb : LevelRowIndex m k) : MultiDialRow m k := Sum.inr jb

@[simp] theorem card_anchorRowIndex (k : Nat) :
    Fintype.card (AnchorRowIndex k) = k := by
  simp [AnchorRowIndex]

@[simp] theorem card_levelRowIndex (m k : Nat) :
    Fintype.card (LevelRowIndex m k) = (m - 1) * k := by
  simp [LevelRowIndex]

/-- The row audit: at positive depth the two families contain `k*m` rows. -/
@[simp] theorem card (m k : Nat) (hm : 0 < m) :
    Fintype.card (MultiDialRow m k) = k * m := by
  simp only [MultiDialRow, Fintype.card_sum, card_anchorRowIndex,
    card_levelRowIndex]
  calc
    k + (m - 1) * k = ((m - 1) + 1) * k := by ring
    _ = m * k := by rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm.ne')]
    _ = k * m := Nat.mul_comm _ _

/-- A canonical enumeration in the certificate's fixed family order. -/
noncomputable def equivFin (m k : Nat) (hm : 0 < m) :
    MultiDialRow m k ≃ Fin (k * m) :=
  (Fintype.equivFin (MultiDialRow m k)).trans (finCongr (card m k hm))

/-- The threshold always has enough ambient coordinates for all certificate rows. -/
theorem card_le_dStarNS (m k : Nat) (hm : 0 < m) :
    Fintype.card (MultiDialRow m k) ≤ dStarNS m k := by
  rw [card m k hm]
  exact le_trans (Nat.mul_le_mul_left k (Nat.le_succ m))
    (rowBudget_le_dStarNS m k)

/-- Embed the row family into ambient coordinates under the raw row budget. -/
noncomputable def embeddingOfCardLe {m k d : Nat}
    (hrows : k * m ≤ d) (hm : 0 < m) : MultiDialRow m k ↪ Fin d :=
  (equivFin m k hm).toEmbedding.trans (Fin.castLEEmb hrows)

end MultiDialRow

/-! ## First-layer dial and zero-frozen tail streams -/

/-- TeX `T_t = sum_a t_a V_{1a}`. -/
noncomputable def dialValueMatrix {m k d : Nat} (theta : Params (m + 1) k d)
    (t : Fin k → Real) : Matrix (Fin d) (Fin d) Real :=
  ∑ a : Fin k, t a • valueMatrix theta 0 a

/-- TeX `w^t(w) = (C_1-T_t)w`. -/
noncomputable def dialContrast {m k d : Nat} (theta : Params (m + 1) k d)
    (t : Fin k → Real) (w : Vec d) : Vec d :=
  (collapseMatrix theta 0 - dialValueMatrix theta t) *ᵥ w

/-- First-layer repeated stream after assigning the simultaneous dial tuple. -/
noncomputable def dialRepeated {m k d : Nat} (theta : Params (m + 1) k d)
    (t : Fin k → Real) (w v : Vec d) : Vec d :=
  collapseMatrix theta 0 *ᵥ v + dialValueMatrix theta t *ᵥ w

/-- Zero-frozen tail streams after `n` later layers. -/
noncomputable def zeroFrozenPrefixPoint {m k d : Nat} (theta : Params (m + 1) k d)
    (t : Fin k → Real) (w v : Vec d) (n : Nat) (hn : n ≤ m) : Vec d × Vec d :=
  let P := frozenP (Fin.tail theta) (allZeroGateFamily m k) n hn
  (P *ᵥ dialContrast theta t w, P *ᵥ dialRepeated theta t w v)

@[simp] theorem dialValueMatrix_zero {m k d : Nat} (theta : Params (m + 1) k d) :
    dialValueMatrix theta (0 : Fin k → Real) = 0 := by
  simp [dialValueMatrix]

theorem dialValueMatrix_add {m k d : Nat} (theta : Params (m + 1) k d)
    (t s : Fin k → Real) :
    dialValueMatrix theta (t + s) = dialValueMatrix theta t + dialValueMatrix theta s := by
  simp only [dialValueMatrix, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem dialValueMatrix_smul {m k d : Nat} (theta : Params (m + 1) k d)
    (c : Real) (t : Fin k → Real) :
    dialValueMatrix theta (c • t) = c • dialValueMatrix theta t := by
  simp [dialValueMatrix, Pi.smul_apply, smul_smul, Finset.smul_sum]

theorem dialContrast_add {m k d : Nat} (theta : Params (m + 1) k d)
    (t : Fin k → Real) (w z : Vec d) :
    dialContrast theta t (w + z) = dialContrast theta t w + dialContrast theta t z := by
  simp [dialContrast, Matrix.mulVec_add]

theorem dialContrast_smul {m k d : Nat} (theta : Params (m + 1) k d)
    (t : Fin k → Real) (c : Real) (w : Vec d) :
    dialContrast theta t (c • w) = c • dialContrast theta t w := by
  simp [dialContrast, Matrix.mulVec_smul]

@[simp] theorem zeroFrozenPrefixPoint_zero {m k d : Nat}
    (theta : Params (m + 1) k d) (t : Fin k → Real) (w v : Vec d) :
    zeroFrozenPrefixPoint theta t w v 0 (Nat.zero_le m) =
      (dialContrast theta t w, dialRepeated theta t w v) := by
  simp [zeroFrozenPrefixPoint]

theorem zeroFrozenPrefixPoint_fst {m k d : Nat}
    (theta : Params (m + 1) k d) (t : Fin k → Real) (w v : Vec d)
    (n : Nat) (hn : n ≤ m) :
    (zeroFrozenPrefixPoint theta t w v n hn).1 =
      frozenP (Fin.tail theta) (allZeroGateFamily m k) n hn *ᵥ
        dialContrast theta t w :=
  rfl

theorem zeroFrozenPrefixPoint_snd {m k d : Nat}
    (theta : Params (m + 1) k d) (t : Fin k → Real) (w v : Vec d)
    (n : Nat) (hn : n ≤ m) :
    (zeroFrozenPrefixPoint theta t w v n hn).2 =
      frozenP (Fin.tail theta) (allZeroGateFamily m k) n hn *ᵥ
        dialRepeated theta t w v :=
  rfl

/-! ## Anchor affine rows -/

noncomputable def anchorRow {m k d : Nat} (theta : Params (m + 1) k d)
    (w : Vec d) (a : Fin k) (v : Vec d) : Real :=
  matrixBilin (attentionMatrix theta 0 a) w v

noncomputable def anchorGradient {m k d : Nat} (theta : Params (m + 1) k d)
    (w : Vec d) (a : Fin k) : Vec d :=
  (attentionMatrix theta 0 a)ᵀ *ᵥ w

@[simp] theorem anchorRow_eq_dotProduct {m k d : Nat} (theta : Params (m + 1) k d)
    (w : Vec d) (a : Fin k) (v : Vec d) :
    anchorRow theta w a v = dotProduct (anchorGradient theta w a) v := by
  simpa [anchorRow, anchorGradient] using
    (TransformerIdentifiability.NLayer.matrixBilin_eq_transpose_dot
      (attentionMatrix theta 0 a) w v)

@[simp] theorem anchorRow_zero {m k d : Nat} (theta : Params (m + 1) k d)
    (w : Vec d) (a : Fin k) : anchorRow theta w a 0 = 0 := by
  simp [anchorRow_eq_dotProduct]

theorem anchorRow_add {m k d : Nat} (theta : Params (m + 1) k d)
    (w : Vec d) (a : Fin k) (v z : Vec d) :
    anchorRow theta w a (v + z) = anchorRow theta w a v + anchorRow theta w a z := by
  simp [anchorRow_eq_dotProduct, dotProduct_add]

theorem anchorRow_smul {m k d : Nat} (theta : Params (m + 1) k d)
    (w : Vec d) (a : Fin k) (c : Real) (v : Vec d) :
    anchorRow theta w a (c • v) = c * anchorRow theta w a v := by
  simp [anchorRow_eq_dotProduct, dotProduct_smul]

/-! ## Deeper all-zero-frozen level rows -/

/-- Number of already traversed tail layers before a deeper level row.  A row
with index `0` is the first deeper layer (TeX layer `j = 2`). -/
def levelPrefixDepth {n k : Nat} (jb : LevelRowIndex (n + 1) k) : Nat :=
  jb.1.val

theorem levelPrefixDepth_le {n k : Nat} (jb : LevelRowIndex (n + 1) k) :
    levelPrefixDepth jb ≤ n := by
  simp [levelPrefixDepth]

/-- The original-parameter layer read by a deeper level row. -/
def levelLayer {n k : Nat} (jb : LevelRowIndex (n + 1) k) : Fin (n + 1) :=
  ⟨jb.1.val + 1, by omega⟩

/-- A total depth `n+1` has exactly `n*k` deeper level rows. -/
@[simp] theorem card_levelRowIndex_depth_succ (n k : Nat) :
    Fintype.card (LevelRowIndex (n + 1) k) = n * k := by
  simp [LevelRowIndex]

/-- The corrected total-row count specializes at depth `n+1` to
`k*(n+1)`: `k` anchors and `n*k` levels. -/
@[simp] theorem card_multiDialRow_depth_succ (n k : Nat) :
    Fintype.card (MultiDialRow (n + 1) k) = k * (n + 1) := by
  exact MultiDialRow.card (n + 1) k (Nat.succ_pos n)

/-- Every non-first layer of a depth-`n+1` parameter and every head correspond
to exactly one level-row index. -/
theorem existsUnique_levelRowIndex_of_layer_ne_zero {n k : Nat}
    (l : Fin (n + 1)) (hl : l ≠ 0) (b : Fin k) :
    ∃! jb : LevelRowIndex (n + 1) k, levelLayer jb = l ∧ jb.2 = b := by
  have hlval : l.val ≠ 0 := by
    intro hzero
    apply hl
    apply Fin.ext
    simpa using hzero
  have hlpos : 0 < l.val := Nat.pos_of_ne_zero hlval
  let j : Fin ((n + 1) - 1) := ⟨l.val - 1, by omega⟩
  let jb : LevelRowIndex (n + 1) k := (j, b)
  refine ⟨jb, ?_, ?_⟩
  · constructor
    · apply Fin.ext
      simp [levelLayer, jb, j]
      omega
    · rfl
  · intro jb' hjb'
    apply Prod.ext
    · apply Fin.ext
      have hlayer := congrArg Fin.val hjb'.1
      change jb'.1.val = j.val
      simp [levelLayer] at hlayer
      simp [j]
      omega
    · exact hjb'.2

/-- Index of the final deeper layer. -/
def finalLevelRowIndex {n k : Nat} (hn : 0 < n) (b : Fin k) :
    LevelRowIndex (n + 1) k :=
  (⟨n - 1, by simp; omega⟩, b)

@[simp] theorem levelPrefixDepth_finalLevelRowIndex {n k : Nat}
    (hn : 0 < n) (b : Fin k) :
    levelPrefixDepth (finalLevelRowIndex hn b) = n - 1 :=
  rfl

@[simp] theorem levelLayer_finalLevelRowIndex {n k : Nat}
    (hn : 0 < n) (b : Fin k) :
    levelLayer (finalLevelRowIndex hn b) = Fin.last n := by
  apply Fin.ext
  simp [levelLayer, finalLevelRowIndex]
  omega

/-- TeX `C_{j-1:2}` through the existing bounded all-zero `frozenP` API. -/
noncomputable def levelPrefixMatrix {n k d : Nat} (theta : Params (n + 1) k d)
    (jb : LevelRowIndex (n + 1) k) : Matrix (Fin d) (Fin d) Real :=
  frozenP (Fin.tail theta) (allZeroGateFamily n k)
    (levelPrefixDepth jb) (levelPrefixDepth_le jb)

/-- TeX `C_{j-1:1} = C_{j-1:2} C_1`. -/
noncomputable def levelFullPrefixMatrix {n k d : Nat}
    (theta : Params (n + 1) k d) (jb : LevelRowIndex (n + 1) k) :
    Matrix (Fin d) (Fin d) Real :=
  levelPrefixMatrix theta jb * collapseMatrix theta 0

/-- TeX `L_{j,b}(v)`, evaluated at the bounded zero-frozen prefix point. -/
noncomputable def levelRow {n k d : Nat} (theta : Params (n + 1) k d)
    (t : Fin k → Real) (w : Vec d) (jb : LevelRowIndex (n + 1) k) (v : Vec d) : Real :=
  let p := zeroFrozenPrefixPoint theta t w v
    (levelPrefixDepth jb) (levelPrefixDepth_le jb)
  matrixBilin (attentionMatrix theta (levelLayer jb) jb.2) p.1 p.2

/-- TeX `∇_v L_{j,b} = C_{j-1:1}ᵀ A_{j,b}ᵀ C_{j-1:2} w^t`. -/
noncomputable def levelGradient {n k d : Nat} (theta : Params (n + 1) k d)
    (t : Fin k → Real) (w : Vec d) (jb : LevelRowIndex (n + 1) k) : Vec d :=
  (levelFullPrefixMatrix theta jb)ᵀ *ᵥ
    ((attentionMatrix theta (levelLayer jb) jb.2)ᵀ *ᵥ
      (levelPrefixMatrix theta jb *ᵥ dialContrast theta t w))

/-- Displayed constant term
`(C_{j-1:2}w^t)ᵀ A_{j,b} C_{j-1:2}T_t w`. -/
noncomputable def levelConstant {n k d : Nat} (theta : Params (n + 1) k d)
    (t : Fin k → Real) (w : Vec d) (jb : LevelRowIndex (n + 1) k) : Real :=
  matrixBilin (attentionMatrix theta (levelLayer jb) jb.2)
    (levelPrefixMatrix theta jb *ᵥ dialContrast theta t w)
    (levelPrefixMatrix theta jb *ᵥ (dialValueMatrix theta t *ᵥ w))

/-- First frozen stream in TeX `eq:ns-frozen-streams`. -/
theorem zeroFrozenPrefixPoint_level_fst {n k d : Nat}
    (theta : Params (n + 1) k d) (t : Fin k → Real) (w v : Vec d)
    (jb : LevelRowIndex (n + 1) k) :
    (zeroFrozenPrefixPoint theta t w v
      (levelPrefixDepth jb) (levelPrefixDepth_le jb)).1 =
      levelPrefixMatrix theta jb *ᵥ dialContrast theta t w :=
  rfl

/-- Second frozen stream in TeX `eq:ns-frozen-streams`, split into its linear
`C_{j-1:1}v` part and its constant `C_{j-1:2}T_t w` part. -/
theorem zeroFrozenPrefixPoint_level_snd {n k d : Nat}
    (theta : Params (n + 1) k d) (t : Fin k → Real) (w v : Vec d)
    (jb : LevelRowIndex (n + 1) k) :
    (zeroFrozenPrefixPoint theta t w v
      (levelPrefixDepth jb) (levelPrefixDepth_le jb)).2 =
      levelFullPrefixMatrix theta jb *ᵥ v +
        levelPrefixMatrix theta jb *ᵥ (dialValueMatrix theta t *ᵥ w) := by
  simp [zeroFrozenPrefixPoint_snd, levelPrefixMatrix, levelFullPrefixMatrix,
    dialRepeated, Matrix.mulVec_add, Matrix.mulVec_mulVec]

/-- The empty prefix before the first deeper layer is the identity. -/
theorem levelPrefixMatrix_eq_one_of_depth_eq_zero {n k d : Nat}
    (theta : Params (n + 1) k d) (jb : LevelRowIndex (n + 1) k)
    (hzero : levelPrefixDepth jb = 0) :
    levelPrefixMatrix theta jb = 1 := by
  unfold levelPrefixMatrix
  convert frozenP_zero (Fin.tail theta) (allZeroGateFamily n k) (Nat.zero_le n)

/-- Exact first-deeper case of the bounded prefix product. -/
@[simp] theorem levelPrefixMatrix_firstDeeper {n k d : Nat}
    (theta : Params (n + 1) k d) (hn : 0 < n) (b : Fin k) :
    levelPrefixMatrix theta
      (⟨⟨0, by omega⟩, b⟩ : LevelRowIndex (n + 1) k) = 1 := by
  simp [levelPrefixMatrix, levelPrefixDepth]

@[simp] theorem levelLayer_firstDeeper {n k : Nat} (hn : 0 < n) (b : Fin k) :
    levelLayer (⟨⟨0, by omega⟩, b⟩ : LevelRowIndex (n + 1) k) =
      (⟨1, by omega⟩ : Fin (n + 1)) := by
  rfl

@[simp] theorem levelFullPrefixMatrix_firstDeeper {n k d : Nat}
    (theta : Params (n + 1) k d) (hn : 0 < n) (b : Fin k) :
    levelFullPrefixMatrix theta
      (⟨⟨0, by omega⟩, b⟩ : LevelRowIndex (n + 1) k) = collapseMatrix theta 0 := by
  let jb : LevelRowIndex (n + 1) k := ⟨⟨0, by omega⟩, b⟩
  change levelFullPrefixMatrix theta jb = collapseMatrix theta 0
  have hp : levelPrefixMatrix theta jb = 1 :=
    levelPrefixMatrix_eq_one_of_depth_eq_zero theta jb rfl
  rw [levelFullPrefixMatrix, hp]
  simp

/-- At the first deeper layer, `C_{j-1:2}=I` and
`C_{j-1:1}=C_1`, including the exact gradient boundary case. -/
@[simp] theorem levelGradient_firstDeeper {n k d : Nat}
    (theta : Params (n + 1) k d) (t : Fin k → Real) (w : Vec d)
    (hn : 0 < n) (b : Fin k) :
    levelGradient theta t w (⟨⟨0, by omega⟩, b⟩ : LevelRowIndex (n + 1) k) =
      (collapseMatrix theta 0)ᵀ *ᵥ
        ((attentionMatrix theta ⟨1, by omega⟩ b)ᵀ *ᵥ dialContrast theta t w) := by
  let jb : LevelRowIndex (n + 1) k := ⟨⟨0, by omega⟩, b⟩
  change levelGradient theta t w jb = _
  have hp : levelPrefixMatrix theta jb = 1 :=
    levelPrefixMatrix_eq_one_of_depth_eq_zero theta jb rfl
  have hM : levelFullPrefixMatrix theta jb = collapseMatrix theta 0 := by
    rw [levelFullPrefixMatrix, hp]
    simp
  have hlayer : levelLayer jb = (⟨1, by omega⟩ : Fin (n + 1)) := rfl
  have hb : jb.2 = b := rfl
  rw [levelGradient, hp, hM, hlayer, hb]
  simp

@[simp] theorem levelConstant_firstDeeper {n k d : Nat}
    (theta : Params (n + 1) k d) (t : Fin k → Real) (w : Vec d)
    (hn : 0 < n) (b : Fin k) :
    levelConstant theta t w (⟨⟨0, by omega⟩, b⟩ : LevelRowIndex (n + 1) k) =
      matrixBilin (attentionMatrix theta ⟨1, by omega⟩ b)
        (dialContrast theta t w) (dialValueMatrix theta t *ᵥ w) := by
  let jb : LevelRowIndex (n + 1) k := ⟨⟨0, by omega⟩, b⟩
  change levelConstant theta t w jb = _
  have hp : levelPrefixMatrix theta jb = 1 :=
    levelPrefixMatrix_eq_one_of_depth_eq_zero theta jb rfl
  have hlayer : levelLayer jb = (⟨1, by omega⟩ : Fin (n + 1)) := rfl
  have hb : jb.2 = b := rfl
  rw [levelConstant, hp, hlayer, hb]
  simp

/-- A level row is affine in `v`, with the displayed gradient and constant. -/
theorem levelRow_eq_dotProduct_add_constant {n k d : Nat}
    (theta : Params (n + 1) k d) (t : Fin k → Real) (w : Vec d)
    (jb : LevelRowIndex (n + 1) k) (v : Vec d) :
    levelRow theta t w jb v =
      dotProduct (levelGradient theta t w jb) v + levelConstant theta t w jb := by
  let A := attentionMatrix theta (levelLayer jb) jb.2
  let P := levelPrefixMatrix theta jb
  let M := levelFullPrefixMatrix theta jb
  let x := P *ᵥ dialContrast theta t w
  let c := P *ᵥ (dialValueMatrix theta t *ᵥ w)
  have adjoint_dot (N : Matrix (Fin d) (Fin d) Real) (y z : Vec d) :
      dotProduct y (N *ᵥ z) = dotProduct (Nᵀ *ᵥ y) z := by
    calc
      dotProduct y (N *ᵥ z) = dotProduct z (Nᵀ *ᵥ y) :=
        (Matrix.dotProduct_transpose_mulVec N z y).symm
      _ = dotProduct (Nᵀ *ᵥ y) z := dotProduct_comm _ _
  have hlinear : matrixBilin A x (M *ᵥ v) =
      dotProduct (Mᵀ *ᵥ (Aᵀ *ᵥ x)) v := by
    rw [matrixBilin_apply, adjoint_dot A, adjoint_dot M]
  change matrixBilin A
      (zeroFrozenPrefixPoint theta t w v
        (levelPrefixDepth jb) (levelPrefixDepth_le jb)).1
      (zeroFrozenPrefixPoint theta t w v
        (levelPrefixDepth jb) (levelPrefixDepth_le jb)).2 = _
  rw [zeroFrozenPrefixPoint_level_fst, zeroFrozenPrefixPoint_level_snd]
  change matrixBilin A x (M *ᵥ v + c) =
    dotProduct (Mᵀ *ᵥ (Aᵀ *ᵥ x)) v + matrixBilin A x c
  rw [show matrixBilin A x (M *ᵥ v + c) =
      matrixBilin A x (M *ᵥ v) + matrixBilin A x c by
        simp [matrixBilin, Matrix.mulVec_add, dotProduct_add], hlinear]

@[simp] theorem levelRow_zero {n k d : Nat} (theta : Params (n + 1) k d)
    (t : Fin k → Real) (w : Vec d) (jb : LevelRowIndex (n + 1) k) :
    levelRow theta t w jb 0 = levelConstant theta t w jb := by
  rw [levelRow_eq_dotProduct_add_constant]
  simp

/-- Existential affine-map packaging used by the combined row matrix. -/
theorem levelRow_affine {n k d : Nat} (theta : Params (n + 1) k d)
    (t : Fin k → Real) (w : Vec d) (jb : LevelRowIndex (n + 1) k) :
    ∃ g : Vec d, ∃ c : Real, ∀ v : Vec d,
      levelRow theta t w jb v = dotProduct g v + c :=
  ⟨levelGradient theta t w jb, levelConstant theta t w jb,
    levelRow_eq_dotProduct_add_constant theta t w jb⟩

/-! ## Why the transversality family is excluded -/

/-- With one head, the former adjugate-transversality column is always a
scalar multiple of the anchor column: `C₁ = V₁` and
`adj(C₁) C₁ = det(C₁) I`.  Under transmission the scalar is nonzero, so adding
that column makes the combined family linearly dependent rather than adding a
new constraint. -/
theorem singleHead_adjugateTransGradient_eq_det_smul_anchorGradient
    {n d : Nat} (theta : Params (n + 1) 1 d) (w : Vec d) :
    -((attentionMatrix theta 0 0)ᵀ *ᵥ
      ((collapseMatrix theta 0).adjugate *ᵥ
        (valueMatrix theta 0 0 *ᵥ w))) =
      (collapseMatrix theta 0).det • (-(anchorGradient theta w 0)) := by
  have hcollapse : collapseMatrix theta 0 = valueMatrix theta 0 0 := by
    simp [collapseMatrix, valueSum]
  have htransport :
      (collapseMatrix theta 0).adjugate *ᵥ
          (valueMatrix theta 0 0 *ᵥ w) =
        (collapseMatrix theta 0).det • w := by
    rw [← hcollapse, Matrix.mulVec_mulVec, Matrix.adjugate_mul]
    rw [Matrix.smul_mulVec]
    simp
  rw [htransport, Matrix.mulVec_smul]
  simp [anchorGradient]

/-- Under transmission, the proportionality scalar in the obstruction above
is nonzero. -/
theorem singleHead_adjugateTransGradient_proportional_of_transmission
    {n d : Nat} (theta : Params (n + 1) 1 d) (w : Vec d)
    (htransmission : (collapseMatrix theta 0).det ≠ 0) :
    ∃ c : Real, c ≠ 0 ∧
      -((attentionMatrix theta 0 0)ᵀ *ᵥ
        ((collapseMatrix theta 0).adjugate *ᵥ
          (valueMatrix theta 0 0 *ᵥ w))) =
        c • anchorGradient theta w 0 := by
  refine ⟨-(collapseMatrix theta 0).det, neg_ne_zero.mpr htransmission, ?_⟩
  rw [singleHead_adjugateTransGradient_eq_det_smul_anchorGradient]
  simp

/-! ## Combined fixed-order row matrix -/

/-- Gradient of any simultaneous-certificate row.  The sum ordering is fixed
by `MultiDialRow`: anchors first and corrected level rows second. -/
noncomputable def multiDialRowGradient {n k d : Nat}
    (theta : Params (n + 1) k d) (t : Fin k → Real) (w : Vec d) :
    MultiDialRow (n + 1) k → Vec d
  | Sum.inl a => anchorGradient theta w a
  | Sum.inr jb => levelGradient theta t w jb

/-- Constant term of any simultaneous-certificate row. -/
noncomputable def multiDialRowConstant {n k d : Nat}
    (theta : Params (n + 1) k d) (t : Fin k → Real) (w : Vec d) :
    MultiDialRow (n + 1) k → Real
  | Sum.inl _a => 0
  | Sum.inr jb => levelConstant theta t w jb

/-- Actual row evaluation, before replacing it by its affine normal form. -/
noncomputable def multiDialRowValue {n k d : Nat}
    (theta : Params (n + 1) k d) (t : Fin k → Real) (w : Vec d) :
    MultiDialRow (n + 1) k → Vec d → Real
  | Sum.inl a => anchorRow theta w a
  | Sum.inr jb => levelRow theta t w jb

/-- TeX gradient matrix `G`, with one row gradient in each column. -/
noncomputable def multiDialGradientMatrix {n k d : Nat}
    (theta : Params (n + 1) k d) (t : Fin k → Real) (w : Vec d) :
    Matrix (Fin d) (MultiDialRow (n + 1) k) Real :=
  Matrix.of fun i row => multiDialRowGradient theta t w row i

/-- Vector of constant terms in the fixed row order. -/
noncomputable def multiDialConstantVector {n k d : Nat}
    (theta : Params (n + 1) k d) (t : Fin k → Real) (w : Vec d) :
    MultiDialRow (n + 1) k → Real :=
  multiDialRowConstant theta t w

/-- Evaluation of all certificate rows in the fixed order. -/
noncomputable def multiDialRowVector {n k d : Nat}
    (theta : Params (n + 1) k d) (t : Fin k → Real) (w v : Vec d) :
    MultiDialRow (n + 1) k → Real :=
  fun row => multiDialRowValue theta t w row v

@[simp] theorem multiDialRowGradient_anchor {n k d : Nat}
    (theta : Params (n + 1) k d) (t : Fin k → Real) (w : Vec d) (a : Fin k) :
    multiDialRowGradient theta t w (MultiDialRow.anchor a) =
      anchorGradient theta w a :=
  rfl

@[simp] theorem multiDialRowGradient_level {n k d : Nat}
    (theta : Params (n + 1) k d) (t : Fin k → Real) (w : Vec d)
    (jb : LevelRowIndex (n + 1) k) :
    multiDialRowGradient theta t w (MultiDialRow.level jb) =
      levelGradient theta t w jb :=
  rfl

@[simp] theorem multiDialRowConstant_anchor {n k d : Nat}
    (theta : Params (n + 1) k d) (t : Fin k → Real) (w : Vec d) (a : Fin k) :
    multiDialRowConstant theta t w (MultiDialRow.anchor a) = 0 :=
  rfl

@[simp] theorem multiDialRowConstant_level {n k d : Nat}
    (theta : Params (n + 1) k d) (t : Fin k → Real) (w : Vec d)
    (jb : LevelRowIndex (n + 1) k) :
    multiDialRowConstant theta t w (MultiDialRow.level jb) =
      levelConstant theta t w jb :=
  rfl

@[simp] theorem multiDialRowValue_anchor {n k d : Nat}
    (theta : Params (n + 1) k d) (t : Fin k → Real) (w v : Vec d) (a : Fin k) :
    multiDialRowValue theta t w (MultiDialRow.anchor a) v = anchorRow theta w a v :=
  rfl

@[simp] theorem multiDialRowValue_level {n k d : Nat}
    (theta : Params (n + 1) k d) (t : Fin k → Real) (w v : Vec d)
    (jb : LevelRowIndex (n + 1) k) :
    multiDialRowValue theta t w (MultiDialRow.level jb) v = levelRow theta t w jb v :=
  rfl

/-- Uniform affine normal form for both row families. -/
theorem multiDialRowValue_eq_dotProduct_add_constant {n k d : Nat}
    (theta : Params (n + 1) k d) (t : Fin k → Real) (w v : Vec d)
    (row : MultiDialRow (n + 1) k) :
    multiDialRowValue theta t w row v =
      dotProduct (multiDialRowGradient theta t w row) v +
        multiDialRowConstant theta t w row := by
  rcases row with a | jb
  · change anchorRow theta w a v = dotProduct (anchorGradient theta w a) v + 0
    rw [anchorRow_eq_dotProduct]
    simp
  · exact levelRow_eq_dotProduct_add_constant theta t w jb v

@[simp] theorem multiDialGradientMatrix_apply {n k d : Nat}
    (theta : Params (n + 1) k d) (t : Fin k → Real) (w : Vec d)
    (i : Fin d) (row : MultiDialRow (n + 1) k) :
    multiDialGradientMatrix theta t w i row =
      multiDialRowGradient theta t w row i :=
  rfl

@[simp] theorem multiDialGradientMatrix_anchor {n k d : Nat}
    (theta : Params (n + 1) k d) (t : Fin k → Real) (w : Vec d)
    (i : Fin d) (a : Fin k) :
    multiDialGradientMatrix theta t w i (MultiDialRow.anchor a) =
      anchorGradient theta w a i :=
  rfl

@[simp] theorem multiDialGradientMatrix_level {n k d : Nat}
    (theta : Params (n + 1) k d) (t : Fin k → Real) (w : Vec d)
    (i : Fin d) (jb : LevelRowIndex (n + 1) k) :
    multiDialGradientMatrix theta t w i (MultiDialRow.level jb) =
      levelGradient theta t w jb i :=
  rfl

/-- Multiplication by `Gᵀ` evaluates every gradient against `v`. -/
theorem multiDialGradientMatrix_transpose_mulVec {n k d : Nat}
    (theta : Params (n + 1) k d) (t : Fin k → Real) (w v : Vec d) :
    (multiDialGradientMatrix theta t w)ᵀ *ᵥ v =
      fun row => dotProduct (multiDialRowGradient theta t w row) v := by
  ext row
  simp [multiDialGradientMatrix, Matrix.mulVec, dotProduct]

/-- Combined affine-row evaluation `R(v) = Gᵀv + R(0)`. -/
theorem multiDialRowVector_eq_gradientMatrix_transpose_mulVec_add {n k d : Nat}
    (theta : Params (n + 1) k d) (t : Fin k → Real) (w v : Vec d) :
    multiDialRowVector theta t w v =
      (multiDialGradientMatrix theta t w)ᵀ *ᵥ v +
        multiDialConstantVector theta t w := by
  funext row
  rw [multiDialRowVector, multiDialRowValue_eq_dotProduct_add_constant,
    multiDialGradientMatrix_transpose_mulVec]
  rfl

/-- The final deeper layer is present as an actual level column of the
combined matrix. -/
theorem multiDialGradientMatrix_includes_finalLayer {n k d : Nat}
    (theta : Params (n + 1) k d) (t : Fin k → Real) (w : Vec d)
    (hn : 0 < n) (b : Fin k) :
    (levelLayer (finalLevelRowIndex hn b) = Fin.last n) ∧
      (∀ i : Fin d,
        multiDialGradientMatrix theta t w i
            (MultiDialRow.level (finalLevelRowIndex hn b)) =
          levelGradient theta t w (finalLevelRowIndex hn b) i) := by
  constructor
  · exact levelLayer_finalLevelRowIndex hn b
  · intro i
    rfl

end TransformerIdentifiability.NLayer.NoSkip
