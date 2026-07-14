import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Genericity.HeadwiseCertificate

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.NoSkip

/-!
# Explicit multi-dial certificate witness design

At total depth `n+1`, the corrected certificate has exactly `k*(n+1)` rows:
`k` anchors and `n*k` deeper-level rows.  An injection of this row family into
`Fin d` assigns one coordinate to every intended gradient column.

The reopened witness is deliberately diagonal.

* `t=0` and `w` is the coordinate of anchor head `0`.
* In every layer, head `0` carries the identity value matrix and every other
  head carries zero.  Consequently every collapsed matrix `C_j` is `I`, as is
  `C_1-T_t`.
* The transpose of first attention `a` is the rank-one matrix
  `e_(anchor a) w^T`.
* At every later layer/head `(j,b)`, the attention transpose is
  `e_(level (j,b)) w^T`.

Thus the expected anchor and level columns are their pairwise distinct
allocated coordinate vectors.  NS068 and NS069 prove those gradient
computations; NS071 assembles their independence and Gram nonvanishing.
-/

section WitnessCoordinates

variable {n k d : Nat}

/-- The conservative public threshold implies the exact corrected row budget. -/
theorem certificateWitness_rowBudget (hd : dStarNS (n + 1) k ≤ d) :
    k * (n + 1) ≤ d := by
  have h := le_trans
    (MultiDialRow.card_le_dStarNS (n + 1) k (Nat.succ_pos n)) hd
  rw [MultiDialRow.card (n + 1) k (Nat.succ_pos n)] at h
  exact h

/-- One distinct ambient coordinate for each of the `k*(n+1)` rows. -/
noncomputable def certificateRowEmbedding (hrows : k * (n + 1) ≤ d) :
    MultiDialRow (n + 1) k ↪ Fin d :=
  MultiDialRow.embeddingOfCardLe hrows (Nat.succ_pos n)

noncomputable def certificateAnchorCoord (hrows : k * (n + 1) ≤ d)
    (a : Fin k) : Fin d :=
  certificateRowEmbedding hrows (MultiDialRow.anchor a)

noncomputable def certificateLevelCoord (hrows : k * (n + 1) ≤ d)
    (jb : LevelRowIndex (n + 1) k) : Fin d :=
  certificateRowEmbedding hrows (MultiDialRow.level jb)

theorem certificateAnchorCoord_injective (hrows : k * (n + 1) ≤ d) :
    Function.Injective (certificateAnchorCoord hrows) := by
  intro a b hab
  exact Sum.inl.inj ((certificateRowEmbedding hrows).injective hab)

theorem certificateLevelCoord_injective (hrows : k * (n + 1) ≤ d) :
    Function.Injective (certificateLevelCoord hrows) := by
  intro jb jb' hab
  exact Sum.inr.inj ((certificateRowEmbedding hrows).injective hab)

theorem certificateAnchorCoord_ne_levelCoord (hrows : k * (n + 1) ≤ d)
    (a : Fin k) (jb : LevelRowIndex (n + 1) k) :
    certificateAnchorCoord hrows a ≠ certificateLevelCoord hrows jb := by
  intro hab
  have := (certificateRowEmbedding hrows).injective hab
  cases this

/-- Standard coordinate vector attached to a certificate row. -/
noncomputable def certificateBasis (hrows : k * (n + 1) ≤ d)
    (row : MultiDialRow (n + 1) k) : Vec d :=
  Pi.single (certificateRowEmbedding hrows row) 1

/-- Expected result of the NS068--NS069 block computations. -/
noncomputable def certificateIntendedGradient
    (hrows : k * (n + 1) ≤ d) :
    MultiDialRow (n + 1) k → Vec d :=
  certificateBasis hrows

@[simp] theorem certificateIntendedGradient_anchor
    (hrows : k * (n + 1) ≤ d) (a : Fin k) :
    certificateIntendedGradient hrows (MultiDialRow.anchor a) =
      certificateBasis hrows (MultiDialRow.anchor a) :=
  rfl

@[simp] theorem certificateIntendedGradient_level
    (hrows : k * (n + 1) ≤ d) (jb : LevelRowIndex (n + 1) k) :
    certificateIntendedGradient hrows (MultiDialRow.level jb) =
      certificateBasis hrows (MultiDialRow.level jb) :=
  rfl

@[simp] theorem certificateBasis_apply_self (hrows : k * (n + 1) ≤ d)
    (row : MultiDialRow (n + 1) k) :
    certificateBasis hrows row (certificateRowEmbedding hrows row) = 1 := by
  simp [certificateBasis]

theorem certificateBasis_apply_other (hrows : k * (n + 1) ≤ d)
    (row row' : MultiDialRow (n + 1) k) (hne : row' ≠ row) :
    certificateBasis hrows row (certificateRowEmbedding hrows row') = 0 := by
  have hemb : certificateRowEmbedding hrows row' ≠
      certificateRowEmbedding hrows row := by
    intro h
    exact hne ((certificateRowEmbedding hrows).injective h)
  simp [certificateBasis, hemb]

end WitnessCoordinates

section WitnessMatrices

variable {d : Nat}

/-- Rank-one matrix `u v^T`, written without analytic inner products. -/
noncomputable def certificateOuter (u v : Vec d) :
    Matrix (Fin d) (Fin d) Real :=
  fun i j => u i * v j

/-- Rank-one action formula used by the later block computations. -/
theorem certificateOuter_mulVec (u v x : Vec d) :
    certificateOuter u v *ᵥ x = dotProduct v x • u := by
  funext i
  simp [certificateOuter, Matrix.mulVec, dotProduct, Finset.mul_sum,
    mul_left_comm, mul_comm]

end WitnessMatrices

section WitnessParameters

variable {n k d : Nat} (hrows : k * (n + 1) ≤ d) (hk : 0 < k)

/-- Distinguished head used to make every layer's value sum the identity. -/
def certificateHeadZero : Fin k := ⟨0, hk⟩

/-- Chosen auxiliary dial tuple. -/
def certificateWitnessT : Fin k → Real := 0

/-- Chosen probe vector, reusing the coordinate of anchor head zero. -/
noncomputable def certificateWitnessW : Vec d :=
  certificateBasis hrows (MultiDialRow.anchor (certificateHeadZero hk))

/-- In every layer, head zero carries `I` and every other head carries `0`. -/
noncomputable def certificateValue (a : Fin k) :
    Matrix (Fin d) (Fin d) Real :=
  if a = certificateHeadZero hk then 1 else 0

/-- First-layer attention transpose `e_(anchor a) w^T`. -/
noncomputable def certificateFirstAttentionTranspose (a : Fin k) :
    Matrix (Fin d) (Fin d) Real :=
  certificateOuter
    (certificateBasis hrows (MultiDialRow.anchor a))
    (certificateWitnessW hrows hk)

noncomputable def certificateFirstAttention (a : Fin k) :
    Matrix (Fin d) (Fin d) Real :=
  (certificateFirstAttentionTranspose hrows hk a)ᵀ

/-- Corrected level-row index corresponding to a non-first layer. -/
def certificateLevelRowOfLayer
    (_hrows : k * (n + 1) ≤ d)
    (l : Fin (n + 1)) (hl : l ≠ 0) (b : Fin k) :
    LevelRowIndex (n + 1) k :=
  (⟨l.val - 1, by
      have hlval : l.val ≠ 0 := by
        intro h
        apply hl
        apply Fin.ext
        simpa using h
      omega⟩, b)

@[simp] theorem levelLayer_certificateLevelRowOfLayer
    (l : Fin (n + 1)) (hl : l ≠ 0) (b : Fin k) :
    levelLayer (certificateLevelRowOfLayer hrows l hl b) = l := by
  apply Fin.ext
  simp [levelLayer, certificateLevelRowOfLayer]
  have hlval : l.val ≠ 0 := by
    intro h
    apply hl
    apply Fin.ext
    simpa using h
  omega

/-- Later attention transpose `e_(level (l,b)) w^T`. -/
noncomputable def certificateLaterAttentionTranspose
    (l : Fin (n + 1)) (hl : l ≠ 0) (b : Fin k) :
    Matrix (Fin d) (Fin d) Real :=
  certificateOuter
    (certificateBasis hrows
      (MultiDialRow.level (certificateLevelRowOfLayer hrows l hl b)))
    (certificateWitnessW hrows hk)

noncomputable def certificateLaterAttention
    (l : Fin (n + 1)) (hl : l ≠ 0) (b : Fin k) :
    Matrix (Fin d) (Fin d) Real :=
  (certificateLaterAttentionTranspose hrows hk l hl b)ᵀ

/-- Complete arbitrary-depth/head parameter witness under the exact budget. -/
noncomputable def certificateWitnessParams : Params (n + 1) k d :=
  fun l a =>
    if hl : l = 0 then
      (certificateValue hk a, certificateFirstAttention hrows hk a)
    else
      (certificateValue hk a, certificateLaterAttention hrows hk l hl a)

@[simp] theorem certificateWitnessParams_value
    (l : Fin (n + 1)) (a : Fin k) :
    valueMatrix (certificateWitnessParams hrows hk) l a =
      certificateValue hk a := by
  by_cases hl : l = 0 <;> simp [certificateWitnessParams, hl]

@[simp] theorem certificateWitnessParams_attention_first (a : Fin k) :
    attentionMatrix (certificateWitnessParams hrows hk) 0 a =
      certificateFirstAttention hrows hk a := by
  simp [certificateWitnessParams]

theorem certificateWitnessParams_attention_later
    (l : Fin (n + 1)) (hl : l ≠ 0) (a : Fin k) :
    attentionMatrix (certificateWitnessParams hrows hk) l a =
      certificateLaterAttention hrows hk l hl a := by
  simp [certificateWitnessParams, hl]

/-- Every layer's headwise value sum is exactly the identity. -/
theorem certificateValue_sum :
    (∑ a : Fin k, certificateValue (d := d) hk a) =
      (1 : Matrix (Fin d) (Fin d) Real) := by
  classical
  simp [certificateValue]

/-- Hence every required no-skip collapsed matrix `C_j` is `I`. -/
@[simp] theorem certificateWitness_collapse (l : Fin (n + 1)) :
    collapseMatrix (certificateWitnessParams hrows hk) l = 1 := by
  rw [collapseMatrix, valueSum]
  simp [certificateValue_sum]

theorem certificateWitness_collapse_det_ne_zero (l : Fin (n + 1)) :
    (collapseMatrix (certificateWitnessParams hrows hk) l).det ≠ 0 := by
  rw [certificateWitness_collapse]
  simp

@[simp] theorem certificateWitness_dialValueMatrix :
    dialValueMatrix (certificateWitnessParams hrows hk)
      (certificateWitnessT (k := k)) = 0 := by
  exact dialValueMatrix_zero (certificateWitnessParams hrows hk)

/-- At the chosen dial tuple, `C_1-T_t=I`. -/
@[simp] theorem certificateWitness_firstCollapse_sub_dial :
    collapseMatrix (certificateWitnessParams hrows hk) 0 -
        dialValueMatrix (certificateWitnessParams hrows hk)
          (certificateWitnessT (k := k)) = 1 := by
  rw [certificateWitness_dialValueMatrix, sub_zero,
    certificateWitness_collapse]

theorem certificateWitness_firstCollapse_sub_dial_det_ne_zero :
    (collapseMatrix (certificateWitnessParams hrows hk) 0 -
      dialValueMatrix (certificateWitnessParams hrows hk)
        (certificateWitnessT (k := k))).det ≠ 0 := by
  rw [certificateWitness_firstCollapse_sub_dial]
  simp

/-- Compact exact-budget design package consumed by NS068--NS071. -/
structure MultiDialCertificateWitnessDesign where
  theta : Params (n + 1) k d
  t : Fin k → Real
  w : Vec d
  rowCoord : MultiDialRow (n + 1) k ↪ Fin d
  collapse_det_ne_zero : ∀ l, (collapseMatrix theta l).det ≠ 0
  first_sub_dial_det_ne_zero :
    (collapseMatrix theta 0 - dialValueMatrix theta t).det ≠ 0

/-- The explicit witness under the sharp `k*(n+1) ≤ d` row budget. -/
noncomputable def explicitMultiDialCertificateWitnessDesignOfRowBudget :
    MultiDialCertificateWitnessDesign (n := n) (k := k) (d := d) where
  theta := certificateWitnessParams hrows hk
  t := certificateWitnessT (k := k)
  w := certificateWitnessW hrows hk
  rowCoord := certificateRowEmbedding hrows
  collapse_det_ne_zero := certificateWitness_collapse_det_ne_zero hrows hk
  first_sub_dial_det_ne_zero :=
    certificateWitness_firstCollapse_sub_dial_det_ne_zero hrows hk

/-- Public-threshold wrapper; the witness itself uses only the sharp budget. -/
noncomputable def explicitMultiDialCertificateWitnessDesign
    (hd : dStarNS (n + 1) k ≤ d) :
    MultiDialCertificateWitnessDesign (n := n) (k := k) (d := d) :=
  explicitMultiDialCertificateWitnessDesignOfRowBudget
    (certificateWitness_rowBudget hd) hk

end WitnessParameters

/-! ## NS068: anchor-block evaluation -/

section WitnessAnchorBlock

variable {n k d : Nat} (hrows : k * (n + 1) ≤ d) (hk : 0 < k)

/-- Every allocated coordinate vector has Euclidean square norm one. -/
@[simp] theorem dotProduct_certificateBasis_self
    (row : MultiDialRow (n + 1) k) :
    dotProduct (certificateBasis hrows row) (certificateBasis hrows row) = 1 := by
  classical
  unfold certificateBasis
  rw [single_dotProduct]
  simp

/-- The reused anchor-zero coordinate is a normalized probe vector. -/
@[simp] theorem dotProduct_certificateWitnessW_self :
    dotProduct (certificateWitnessW hrows hk)
      (certificateWitnessW hrows hk) = 1 := by
  exact dotProduct_certificateBasis_self hrows
    (MultiDialRow.anchor (certificateHeadZero hk))

/-- Every first-layer anchor gradient is its allocated standard basis vector:
`A_{1a}^T w = e_(anchor a)`. -/
@[simp] theorem certificateWitness_anchorGradient (a : Fin k) :
    anchorGradient (certificateWitnessParams hrows hk)
        (certificateWitnessW hrows hk) a =
      certificateIntendedGradient hrows (MultiDialRow.anchor a) := by
  rw [anchorGradient, certificateWitnessParams_attention_first,
    certificateFirstAttention, Matrix.transpose_transpose,
    certificateFirstAttentionTranspose, certificateOuter_mulVec,
    dotProduct_certificateWitnessW_self]
  simp [certificateIntendedGradient]

/-- The complete allocated coordinate-vector family is injectively indexed. -/
theorem certificateBasis_injective :
    Function.Injective
      (certificateBasis hrows : MultiDialRow (n + 1) k → Vec d) := by
  intro row row' hvec
  by_contra hne
  have hcoord : certificateRowEmbedding hrows row' ≠
      certificateRowEmbedding hrows row := by
    intro h
    exact hne ((certificateRowEmbedding hrows).injective h.symm)
  have happ := congr_fun hvec (certificateRowEmbedding hrows row)
  simp [certificateBasis, hcoord] at happ

/-- Different heads have different anchor-gradient columns. -/
theorem certificateWitness_anchorGradient_injective :
    Function.Injective
      (anchorGradient (certificateWitnessParams hrows hk)
        (certificateWitnessW hrows hk)) := by
  intro a b hab
  apply Sum.inl.inj
  apply certificateBasis_injective hrows
  simpa [certificateIntendedGradient] using
    (certificateWitness_anchorGradient hrows hk a).symm.trans
      (hab.trans (certificateWitness_anchorGradient hrows hk b))

/-- The anchor block alone is linearly independent.  No level-column or full
certificate independence is asserted here. -/
theorem certificateWitness_anchorGradients_linearIndependent :
    LinearIndependent Real
      (anchorGradient (certificateWitnessParams hrows hk)
        (certificateWitnessW hrows hk)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro coeff hsum a
  have ha := congr_fun hsum (certificateAnchorCoord hrows a)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at ha
  simp_rw [certificateWitness_anchorGradient hrows hk] at ha
  simpa [certificateIntendedGradient, certificateBasis, certificateAnchorCoord,
    Pi.single_apply, MultiDialRow.anchor] using ha

end WitnessAnchorBlock

/-! ## NS069: deeper level-block evaluation -/

section WitnessLevelBlocks

variable {n k d : Nat} (hrows : k * (n + 1) ≤ d) (hk : 0 < k)

/-- Every collapsed matrix in the witness tail is also the identity. -/
@[simp] theorem certificateWitness_tail_collapse (l : Fin n) :
    collapseMatrix (Fin.tail (certificateWitnessParams hrows hk)) l = 1 := by
  change collapseMatrix (certificateWitnessParams hrows hk) l.succ = 1
  exact certificateWitness_collapse hrows hk l.succ

/-- Every bounded collapsed tail-prefix product is the identity. -/
@[simp] theorem certificateWitness_tail_frozenP :
    ∀ (q : Nat) (hq : q ≤ n),
      frozenP (Fin.tail (certificateWitnessParams hrows hk))
        (allZeroGateFamily n k) q hq = 1
  | 0, hq => by simp
  | q + 1, hq => by
      rw [frozenP_succ, certificateWitness_tail_collapse,
        certificateWitness_tail_frozenP q (Nat.le_of_succ_le hq)]
      simp

/-- Every corrected deeper-row prefix `C_{j-1:2}` is `I`. -/
@[simp] theorem certificateWitness_levelPrefixMatrix
    (jb : LevelRowIndex (n + 1) k) :
    levelPrefixMatrix (certificateWitnessParams hrows hk) jb = 1 := by
  unfold levelPrefixMatrix
  exact certificateWitness_tail_frozenP hrows hk
    (levelPrefixDepth jb) (levelPrefixDepth_le jb)

/-- Every full corrected prefix `C_{j-1:1}` is `I`. -/
@[simp] theorem certificateWitness_levelFullPrefixMatrix
    (jb : LevelRowIndex (n + 1) k) :
    levelFullPrefixMatrix (certificateWitnessParams hrows hk) jb = 1 := by
  rw [levelFullPrefixMatrix, certificateWitness_levelPrefixMatrix,
    certificateWitness_collapse]
  simp

/-- At `t=0`, the witness contrast vector is exactly the chosen probe `w`. -/
@[simp] theorem certificateWitness_dialContrast :
    dialContrast (certificateWitnessParams hrows hk)
        (certificateWitnessT (k := k)) (certificateWitnessW hrows hk) =
      certificateWitnessW hrows hk := by
  rw [dialContrast, certificateWitness_firstCollapse_sub_dial]
  simp

/-- A corrected level row always belongs to a non-first layer. -/
theorem levelLayer_ne_zero (jb : LevelRowIndex (n + 1) k) :
    levelLayer jb ≠ 0 := by
  intro hzero
  have hval := congrArg Fin.val hzero
  simp [levelLayer] at hval

/-- The later-layer-to-level-row constructor is inverse to the corrected
`levelLayer` projection. -/
@[simp] theorem certificateLevelRowOfLayer_levelLayer
    (jb : LevelRowIndex (n + 1) k) :
    certificateLevelRowOfLayer hrows (levelLayer jb)
        (levelLayer_ne_zero jb) jb.2 = jb := by
  apply Prod.ext
  · apply Fin.ext
    simp [certificateLevelRowOfLayer, levelLayer]
  · rfl

/-- The chosen later attention transpose sends `w` to its allocated level
coordinate. -/
@[simp] theorem certificateLaterAttentionTranspose_mulVec
    (l : Fin (n + 1)) (hl : l ≠ 0) (b : Fin k) :
    certificateLaterAttentionTranspose hrows hk l hl b *ᵥ
        certificateWitnessW hrows hk =
      certificateBasis hrows
        (MultiDialRow.level (certificateLevelRowOfLayer hrows l hl b)) := by
  rw [certificateLaterAttentionTranspose, certificateOuter_mulVec,
    dotProduct_certificateWitnessW_self]
  simp

/-- Every corrected deeper gradient is exactly its intended allocated
coordinate column. -/
@[simp] theorem certificateWitness_levelGradient
    (jb : LevelRowIndex (n + 1) k) :
    levelGradient (certificateWitnessParams hrows hk)
        (certificateWitnessT (k := k)) (certificateWitnessW hrows hk) jb =
      certificateIntendedGradient hrows (MultiDialRow.level jb) := by
  rw [levelGradient, certificateWitness_levelFullPrefixMatrix,
    certificateWitness_levelPrefixMatrix, certificateWitness_dialContrast]
  simp only [Matrix.transpose_one, Matrix.one_mulVec]
  rw [certificateWitnessParams_attention_later hrows hk (levelLayer jb)
    (levelLayer_ne_zero jb) jb.2, certificateLaterAttention,
    Matrix.transpose_transpose, certificateLaterAttentionTranspose_mulVec,
    certificateLevelRowOfLayer_levelLayer]
  rfl

end WitnessLevelBlocks

/-! ## NS070: two-family coordinate collision audit -/

section WitnessCoordinateAudit

variable {n k d : Nat} (hrows : k * (n + 1) ≤ d)

/-- The combined coordinate assignment is injective on every corrected row,
not merely within each individual block. -/
theorem certificateRowEmbedding_injective :
    Function.Injective
      (certificateRowEmbedding hrows : MultiDialRow (n + 1) k → Fin d) :=
  (certificateRowEmbedding hrows).injective

/-- Exact collision criterion for arbitrary rows in the combined assignment. -/
@[simp] theorem certificateRowEmbedding_eq_iff
    (row row' : MultiDialRow (n + 1) k) :
    certificateRowEmbedding hrows row = certificateRowEmbedding hrows row' ↔
      row = row' := by
  constructor
  · intro h
    exact certificateRowEmbedding_injective hrows h
  · exact congrArg (certificateRowEmbedding hrows)

/-- The two constructors exhaust the corrected witness row type.  This is the
formal no-third-family audit. -/
theorem certificateWitness_no_third_family
    (row : MultiDialRow (n + 1) k) :
    (∃ a : Fin k, row = MultiDialRow.anchor a) ∨
      ∃ jb : LevelRowIndex (n + 1) k, row = MultiDialRow.level jb := by
  rcases row with a | jb
  · exact Or.inl ⟨a, rfl⟩
  · exact Or.inr ⟨jb, rfl⟩

/-- The image of the combined coordinate assignment is exactly the union of
the anchor-coordinate image and the level-coordinate image. -/
theorem certificateRowEmbedding_range :
    Set.range
        (certificateRowEmbedding hrows : MultiDialRow (n + 1) k → Fin d) =
      Set.range (certificateAnchorCoord hrows) ∪
        Set.range (certificateLevelCoord hrows) := by
  ext i
  constructor
  · rintro ⟨row, rfl⟩
    rcases row with a | jb
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr ⟨jb, rfl⟩
  · rintro (⟨a, rfl⟩ | ⟨jb, rfl⟩)
    · exact ⟨MultiDialRow.anchor a, rfl⟩
    · exact ⟨MultiDialRow.level jb, rfl⟩

/-- The two coordinate images are disjoint. -/
theorem certificateCoordinateRanges_disjoint :
    Disjoint (Set.range (certificateAnchorCoord hrows))
      (Set.range (certificateLevelCoord hrows)) := by
  rw [Set.disjoint_left]
  rintro i ⟨a, rfl⟩ ⟨jb, hcollision⟩
  exact certificateAnchorCoord_ne_levelCoord hrows a jb hcollision.symm

/-- The anchor block contains exactly `k` row indices. -/
@[simp] theorem certificateAnchorBlock_card :
    Fintype.card (AnchorRowIndex k) = k := by
  simp [AnchorRowIndex]

/-- The level block contains exactly `n*k` row indices at depth `n+1`. -/
@[simp] theorem certificateLevelBlock_card :
    Fintype.card (LevelRowIndex (n + 1) k) = n * k :=
  card_levelRowIndex_depth_succ n k

/-- The exhausted two-family witness has exactly `k*(n+1)` rows. -/
@[simp] theorem certificateWitnessRow_card :
    Fintype.card (MultiDialRow (n + 1) k) = k * (n + 1) :=
  card_multiDialRow_depth_succ n k

/-- Cardinal arithmetic for the disjoint anchor/level decomposition. -/
theorem certificateWitnessBlock_card_sum :
    Fintype.card (AnchorRowIndex k) +
        Fintype.card (LevelRowIndex (n + 1) k) =
      k * (n + 1) := by
  rw [certificateAnchorBlock_card, certificateLevelBlock_card]
  ring

end WitnessCoordinateAudit

/-! ## NS071: full witness independence and numeric Gram value -/

section WitnessIndependence

variable {n k d : Nat} (hrows : k * (n + 1) ≤ d) (hk : 0 < k)

/-- The anchor and level computations combine into the standard coordinate
vector assigned to every corrected row. -/
@[simp] theorem certificateWitness_multiDialRowGradient
    (row : MultiDialRow (n + 1) k) :
    multiDialRowGradient (certificateWitnessParams hrows hk)
        (certificateWitnessT (k := k)) (certificateWitnessW hrows hk) row =
      certificateIntendedGradient hrows row := by
  rcases row with a | jb
  · exact certificateWitness_anchorGradient hrows hk a
  · exact certificateWitness_levelGradient hrows hk jb

/-- Matrix whose columns are precisely the injected coordinate vectors. -/
noncomputable def certificateCoordinateGradientMatrix :
    Matrix (Fin d) (MultiDialRow (n + 1) k) Real :=
  Matrix.of fun i row => certificateBasis hrows row i

@[simp] theorem certificateCoordinateGradientMatrix_apply
    (i : Fin d) (row : MultiDialRow (n + 1) k) :
    certificateCoordinateGradientMatrix hrows i row =
      certificateBasis hrows row i :=
  rfl

/-- The complete witness gradient matrix is the coordinate-column matrix. -/
theorem certificateWitness_multiDialGradientMatrix :
    multiDialGradientMatrix (certificateWitnessParams hrows hk)
        (certificateWitnessT (k := k)) (certificateWitnessW hrows hk) =
      certificateCoordinateGradientMatrix hrows := by
  ext i row
  rw [multiDialGradientMatrix_apply,
    certificateWitness_multiDialRowGradient]
  rfl

/-- Distinct allocated coordinate vectors are orthogonal, while each has
square norm one. -/
@[simp] theorem dotProduct_certificateBasis
    (row row' : MultiDialRow (n + 1) k) :
    dotProduct (certificateBasis hrows row) (certificateBasis hrows row') =
      if row = row' then 1 else 0 := by
  classical
  by_cases hrow : row = row'
  · subst row'
    simp
  · unfold certificateBasis
    rw [single_dotProduct]
    have hemb : certificateRowEmbedding hrows row' ≠
        certificateRowEmbedding hrows row := by
      intro h
      exact hrow (certificateRowEmbedding_injective hrows h.symm)
    simp [hrow]

/-- The coordinate-column Gram matrix is the identity. -/
theorem certificateCoordinateGradientMatrix_gram :
    (certificateCoordinateGradientMatrix hrows)ᵀ *
        certificateCoordinateGradientMatrix hrows = 1 := by
  ext row row'
  change dotProduct (certificateBasis hrows row)
      (certificateBasis hrows row') = (1 : Matrix
        (MultiDialRow (n + 1) k) (MultiDialRow (n + 1) k) Real) row row'
  by_cases h : row = row'
  · subst h; simp [Matrix.one_apply_eq]
  · simp [h, Matrix.one_apply_ne h]

/-- The numeric witness Gram matrix is exactly the identity. -/
@[simp] theorem certificateWitness_multiDialGramMatrix :
    multiDialGramMatrix (certificateWitnessParams hrows hk)
        (certificateWitnessT (k := k)) (certificateWitnessW hrows hk) = 1 := by
  rw [multiDialGramMatrix, certificateWitness_multiDialGradientMatrix,
    certificateCoordinateGradientMatrix_gram]

/-- Consequently the numeric witness Gram determinant is exactly one. -/
@[simp] theorem certificateWitness_multiDialGramDet :
    multiDialGramDet (certificateWitnessParams hrows hk)
        (certificateWitnessT (k := k)) (certificateWitnessW hrows hk) = 1 := by
  rw [multiDialGramDet, certificateWitness_multiDialGramMatrix]
  exact Matrix.det_one

/-- Concrete nonzero Gram evaluation under the sharp row budget. -/
theorem certificateWitness_multiDialGramDet_ne_zero :
    multiDialGramDet (certificateWitnessParams hrows hk)
        (certificateWitnessT (k := k)) (certificateWitnessW hrows hk) ≠ 0 := by
  rw [certificateWitness_multiDialGramDet]
  norm_num

/-- Every corrected witness gradient column is linearly independent. -/
theorem certificateWitness_multiDialRowGradients_linearIndependent :
    LinearIndependent Real
      (multiDialRowGradient (certificateWitnessParams hrows hk)
        (certificateWitnessT (k := k)) (certificateWitnessW hrows hk)) :=
  linearIndependent_multiDialRowGradient_of_gramDet_ne_zero
    (certificateWitnessParams hrows hk) (certificateWitnessT (k := k))
    (certificateWitnessW hrows hk)
    (certificateWitness_multiDialGramDet_ne_zero hrows hk)

include hrows hk in
/-- Sharp-budget existential capstone consumed by polynomial properness. -/
theorem exists_multiDialGramDet_ne_zero_of_rowBudget :
    ∃ theta : Params (n + 1) k d,
      ∃ t : Fin k → Real, ∃ w : Vec d,
        multiDialGramDet theta t w ≠ 0 :=
  ⟨certificateWitnessParams hrows hk, certificateWitnessT (k := k),
    certificateWitnessW hrows hk,
    certificateWitness_multiDialGramDet_ne_zero hrows hk⟩

include hk in
/-- Conservative-threshold wrapper around the sharp-budget witness. -/
theorem exists_multiDialGramDet_ne_zero_of_dStarNS
    (hd : dStarNS (n + 1) k ≤ d) :
    ∃ theta : Params (n + 1) k d,
      ∃ t : Fin k → Real, ∃ w : Vec d,
        multiDialGramDet theta t w ≠ 0 :=
  exists_multiDialGramDet_ne_zero_of_rowBudget
    (certificateWitness_rowBudget hd) hk

/-! ## NS072 — properness of the coefficient certificate polynomial

The multi-dial Gram polynomial `multiDialGramPoly θ` is not identically zero in
`(t,w)` whenever the ambient dimension admits the sharp row budget: the explicit
witness supplies a concrete evaluation where the numeric Gram determinant is one.
Equivalently, the TeX coefficient sum-of-squares certificate is nonzero for some
parameter tuple at every allowed dimension, including all `d` above the minimal
row dimension `k*(n+1)`. -/

include hrows hk in
/-- The Gram polynomial is a nonzero element of the auxiliary polynomial ring
under the sharp row budget: the witness parameters realize it. -/
theorem exists_multiDialGramPoly_ne_zero_of_rowBudget :
    ∃ theta : Params (n + 1) k d, multiDialGramPoly theta ≠ 0 := by
  refine ⟨certificateWitnessParams hrows hk, ?_⟩
  rw [multiDialGramPoly_ne_zero_iff_exists_eval_ne_zero]
  exact ⟨certificateWitnessT (k := k), certificateWitnessW hrows hk,
    certificateWitness_multiDialGramDet_ne_zero hrows hk⟩

include hrows hk in
/-- Properness of the coefficient certificate under the sharp row budget:
the TeX sum-of-squares certificate is nonzero for the witness parameters. -/
theorem exists_multiDialCertificate_of_rowBudget :
    ∃ theta : Params (n + 1) k d, MultiDialCertificate theta := by
  refine ⟨certificateWitnessParams hrows hk, ?_⟩
  rw [multiDialCertificate_iff_exists_gramDet_ne_zero]
  exact ⟨certificateWitnessT (k := k), certificateWitnessW hrows hk,
    certificateWitness_multiDialGramDet_ne_zero hrows hk⟩

include hk in
/-- Properness of the coefficient certificate above the conservative dimension
threshold, extending the minimal-row-dimension witness to every larger `d`. -/
theorem exists_multiDialCertificate_of_dStarNS
    (hd : dStarNS (n + 1) k ≤ d) :
    ∃ theta : Params (n + 1) k d, MultiDialCertificate theta :=
  exists_multiDialCertificate_of_rowBudget (certificateWitness_rowBudget hd) hk

include hrows hk in
/-- The same diagonal witness proves every repaired scalar head restriction:
at scalar dial zero, `0 * e_h` is the common zero tuple for all `h`. -/
theorem certificateWitness_headwiseDialCertificate :
    HeadwiseDialCertificate (certificateWitnessParams hrows hk) := by
  exact headwiseDialCertificate_of_zero_gramDet
    (certificateWitnessParams hrows hk) (certificateWitnessW hrows hk)
    (by simpa only using certificateWitness_multiDialGramDet_ne_zero hrows hk)

include hrows hk in
/-- Properness of the repaired headwise coefficient condition at the sharp row
budget. -/
theorem exists_headwiseDialCertificate_of_rowBudget :
    ∃ theta : Params (n + 1) k d, HeadwiseDialCertificate theta :=
  ⟨certificateWitnessParams hrows hk,
    certificateWitness_headwiseDialCertificate hrows hk⟩

end WitnessIndependence

end TransformerIdentifiability.NLayer.NoSkip
