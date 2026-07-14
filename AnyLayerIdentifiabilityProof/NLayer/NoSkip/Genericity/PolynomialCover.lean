import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Genericity.Recursive
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Genericity.CertificateWitness
import AnyLayerIdentifiabilityProof.NLayer.KHead.Genericity.PolynomialCover

set_option autoImplicit false

open Matrix
open scoped BigOperators

open TransformerIdentifiability.NLayer.KHead
  (KHeadParamPolynomialPredicateCover KHeadParamCoord kHeadParamFlat
    kHeadParamNonvanishingCarrier)

namespace TransformerIdentifiability.NLayer.NoSkip

/-!
# NS080 — Polynomial cover of the recursive no-skip generic set

We assemble the finite family of nonzero parameter polynomials `p_1,…,p_R`
whose common nonvanishing locus is contained in the recursive generic set
`RecursiveGeneric` (TeX `def:recursive-G`).  The exceptional set
`𝒩_{L,k} := ⋃_i {p_i = 0}` is exposed through the reusable k-head
`KHeadParamPolynomialPredicateCover` framework (the parameter type
`NoSkip.Params = KHead.Params` is literally shared, and `nsParamFlat` and
`kHeadParamFlat` are definitionally equal), so the open/dense/full-measure
consequences in `Null.lean` follow directly from the shared toolbox.

The cover recurses over tail depth exactly as `RecursiveGeneric` does:

* depth `0` is vacuous (empty family);
* depth `1` is regularity (with derived local openness);
* depth `L+2` combines the lifted tail cover with the current-layer package of
  regularity, the cascade certificate (NS057), and the multi-dial certificate
  (NS072).

Every per-clause polynomial is proper (nonzero) by an explicit witness:
regularity uses identity/zero parameter witnesses, cascade uses the identity
witness `cascadeIdentityWitness`, and the multi-dial Gram polynomial uses the
minimal-row-budget witness `certificateWitnessParams`.
-/

/-- `nsParamFlat` and `kHeadParamFlat` are the same flattening. -/
theorem nsParamFlat_eq_kHeadParamFlat {L k d : Nat} (θ : Params L k d) :
    nsParamFlat θ = kHeadParamFlat θ := rfl

/-- `sym` of the identity matrix is the identity. -/
theorem sym_one {d : Nat} : sym (1 : Matrix (Fin d) (Fin d) ℝ) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [sym]; ring
  · have h' : j ≠ i := Ne.symm h
    simp [sym, h, h']

/-! ## Neutral flattening helpers -/

/-- Constant parameter-ring vector from a real vector. -/
noncomputable def nsConstVec {L k d : Nat} (w : Vec d) :
    Fin d → NSParamRing L k d :=
  fun i => MvPolynomial.C (w i)

@[simp] theorem eval_nsConstVec {L k d : Nat} (θ : Params L k d) (w : Vec d)
    (i : Fin d) :
    MvPolynomial.eval (nsParamFlat θ) (nsConstVec (L := L) (k := k) w i) = w i := by
  simp [nsConstVec]

/-- Evaluation commutes with parameter-ring matrix-vector multiplication. -/
theorem eval_nsParamRing_mulVec {L k d : Nat} {m n : Type*} [Fintype n]
    (θ : Params L k d) (M : Matrix m n (NSParamRing L k d))
    (v : n → NSParamRing L k d) :
    (fun i => MvPolynomial.eval (nsParamFlat θ) (M.mulVec v i)) =
      (M.map (MvPolynomial.eval (nsParamFlat θ))).mulVec
        (fun j => MvPolynomial.eval (nsParamFlat θ) (v j)) := by
  funext i
  simp [Matrix.mulVec, dotProduct]

/-! ## Regularity cover -/

/-- Finite polynomial index set for regularity: the basic R1/R2 clauses plus the
structural R3/R4 clauses. -/
abbrev RegularityIndex (L k : Nat) : Type :=
  BasicMatrixIndexNS L k ⊕ StructuralMatrixIndexNS L

/-- Regularity polynomial family. -/
noncomputable def regularityPoly (L k d : Nat) :
    RegularityIndex L k → NSParamRing L k d
  | Sum.inl b => basicMatrixPolyNS (d := d) b
  | Sum.inr s => structuralMatrixPolyNS (k := k) (d := d) s

theorem basicMatrixPolyNS_ne_zero {L k d : Nat} (hd : 0 < d)
    (idx : BasicMatrixIndexNS L k) : basicMatrixPolyNS (d := d) idx ≠ 0 := by
  classical
  have hone : (1 : Matrix (Fin d) (Fin d) ℝ) ≠ 0 := identityMatrix_ne_zero_of_pos hd
  cases idx with
  | detAttention l a =>
      let θ : Params L k d := fun l' a' =>
        ((0 : Matrix (Fin d) (Fin d) ℝ),
          if l' = l ∧ a' = a then (1 : Matrix (Fin d) (Fin d) ℝ) else 0)
      refine mvPolynomial_ne_zero_of_eval_ne_zero _ (nsParamFlat θ) ?_
      have hA : attentionMatrix θ l a = (1 : Matrix (Fin d) (Fin d) ℝ) := by
        simp [θ, attentionMatrix]
      rw [basicMatrixPolyNS, eval_det_nsGenAttention, hA]
      simp
  | symAttention l a =>
      let θ : Params L k d := fun l' a' =>
        ((0 : Matrix (Fin d) (Fin d) ℝ),
          if l' = l ∧ a' = a then (1 : Matrix (Fin d) (Fin d) ℝ) else 0)
      refine mvPolynomial_ne_zero_of_eval_ne_zero _ (nsParamFlat θ) ?_
      have hA : attentionMatrix θ l a = (1 : Matrix (Fin d) (Fin d) ℝ) := by
        simp [θ, attentionMatrix]
      rw [basicMatrixPolyNS, eval_matrixFrobSqNSPoly, map_nsGenSym, map_nsGenAttention,
        hA, matrixFrobSqNS_ne_zero_iff, sym_one]
      exact hone
  | value l a =>
      let θ : Params L k d := fun l' a' =>
        (if l' = l ∧ a' = a then (1 : Matrix (Fin d) (Fin d) ℝ) else 0,
          (0 : Matrix (Fin d) (Fin d) ℝ))
      refine mvPolynomial_ne_zero_of_eval_ne_zero _ (nsParamFlat θ) ?_
      have hV : valueMatrix θ l a = (1 : Matrix (Fin d) (Fin d) ℝ) := by
        simp [θ, valueMatrix]
      rw [basicMatrixPolyNS, eval_matrixFrobSqNSPoly, map_nsGenValue, hV,
        matrixFrobSqNS_ne_zero_iff]
      exact hone
  | headSeparation l ac =>
      let θ : Params L k d := fun l' a' =>
        ((0 : Matrix (Fin d) (Fin d) ℝ),
          if l' = l ∧ a' = ac.1.1 then (1 : Matrix (Fin d) (Fin d) ℝ) else 0)
      refine mvPolynomial_ne_zero_of_eval_ne_zero _ (nsParamFlat θ) ?_
      have hne : ac.1.2 ≠ ac.1.1 := Ne.symm ac.2
      have h1 : attentionMatrix θ l ac.1.1 = (1 : Matrix (Fin d) (Fin d) ℝ) := by
        simp [θ, attentionMatrix]
      have h2 : attentionMatrix θ l ac.1.2 = (0 : Matrix (Fin d) (Fin d) ℝ) := by
        simp [θ, attentionMatrix, hne]
      have hmap :
          (nsGenAttention L k d l ac.1.1 - nsGenAttention L k d l ac.1.2).map
              (MvPolynomial.eval (nsParamFlat θ)) = (1 : Matrix (Fin d) (Fin d) ℝ) := by
        have hsub :
            (nsGenAttention L k d l ac.1.1 - nsGenAttention L k d l ac.1.2).map
                (MvPolynomial.eval (nsParamFlat θ)) =
              (nsGenAttention L k d l ac.1.1).map (MvPolynomial.eval (nsParamFlat θ)) -
                (nsGenAttention L k d l ac.1.2).map (MvPolynomial.eval (nsParamFlat θ)) := by
          ext i j; simp only [Matrix.map_apply, Matrix.sub_apply, map_sub]
        rw [hsub, map_nsGenAttention, map_nsGenAttention, h1, h2, sub_zero]
      rw [basicMatrixPolyNS, eval_matrixFrobSqNSPoly, hmap, matrixFrobSqNS_ne_zero_iff]
      exact hone

theorem structuralMatrixPolyNS_ne_zero {L k d : Nat} (hk : 0 < k)
    (idx : StructuralMatrixIndexNS L) :
    structuralMatrixPolyNS (k := k) (d := d) idx ≠ 0 := by
  classical
  let h0 : Fin k := ⟨0, hk⟩
  let θ : Params L k d := fun _l' a' =>
    ((if a' = h0 then (1 : Matrix (Fin d) (Fin d) ℝ) else 0),
      (0 : Matrix (Fin d) (Fin d) ℝ))
  have hval : ∀ l a, valueMatrix θ l a = (if a = h0 then (1 : Matrix (Fin d) (Fin d) ℝ) else 0) := by
    intro l a; simp [θ, valueMatrix]
  have hcollapse : ∀ l : Fin L, collapseMatrix θ l = (1 : Matrix (Fin d) (Fin d) ℝ) := by
    intro l
    rw [collapseMatrix, valueSum]
    rw [Finset.sum_eq_single h0]
    · simp [hval]
    · intro a _ha hne; simp [hval, hne]
    · intro hnot; exact absurd (Finset.mem_univ h0) hnot
  cases idx with
  | transmission l =>
      refine mvPolynomial_ne_zero_of_eval_ne_zero _ (nsParamFlat θ) ?_
      have h := eval_structuralMatrixPolyNS (k := k) θ (.transmission l)
      dsimp only at h
      rw [h, hcollapse l]
      simp
  | jointSurjectivity l =>
      refine mvPolynomial_ne_zero_of_eval_ne_zero _ (nsParamFlat θ) ?_
      have h := eval_structuralMatrixPolyNS (k := k) θ (.jointSurjectivity l)
      dsimp only at h
      have hgram : jointSurjectivityGram θ l = (1 : Matrix (Fin d) (Fin d) ℝ) := by
        rw [jointSurjectivityGram]
        rw [Finset.sum_eq_single h0]
        · simp [hval]
        · intro a _ha hne; simp [hval, hne]
        · intro hnot; exact absurd (Finset.mem_univ h0) hnot
      rw [h, hgram]; simp

/-- Finite regularity cover. -/
noncomputable def regularityCover (L k d : Nat) (hd : 0 < d) (hk : 0 < k) :
    KHeadParamPolynomialPredicateCover L k d (fun θ => Regularity θ) where
  κ := RegularityIndex L k
  data :=
    { indices := Finset.univ
      poly := regularityPoly L k d
      nonzero := by
        intro idx _hidx
        cases idx with
        | inl b => exact basicMatrixPolyNS_ne_zero hd b
        | inr s => exact structuralMatrixPolyNS_ne_zero hk s }
  carrier_subset := by
    intro θ hθ
    change Regularity θ
    rw [regularity_iff_polynomial_clauses]
    refine ⟨(basicMatrixClausesNS_iff θ).mpr ?_, (structuralMatrixClausesNS_iff θ).mpr ?_⟩
    · intro idx
      have := hθ (Sum.inl idx) (Finset.mem_univ _)
      simpa only [regularityPoly, nsParamFlat_eq_kHeadParamFlat] using this
    · intro idx
      have := hθ (Sum.inr idx) (Finset.mem_univ _)
      simpa only [regularityPoly, nsParamFlat_eq_kHeadParamFlat] using this

/-! ## Cascade certificate cover -/

/-- Generic parameter-ring cascade product along a chain. -/
noncomputable def nsGenCascadeProduct (m k d : Nat) (h : Fin k) (χ : CascadeChain m k) :
    Nat → Matrix (Fin d) (Fin d) (NSParamRing (m + 1) k d)
  | 0 => nsGenValue (m + 1) k d 0 h
  | n + 1 =>
      if hn : n < m then
        nsGenValue (m + 1) k d (laterLayer ⟨n, hn⟩) (χ ⟨n, hn⟩) *
          nsGenCascadeProduct m k d h χ n
      else
        nsGenCascadeProduct m k d h χ n

@[simp] theorem map_nsGenCascadeProduct {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (χ : CascadeChain m k) :
    ∀ n, (nsGenCascadeProduct m k d h χ n).map (MvPolynomial.eval (nsParamFlat θ)) =
        cascadeProduct θ h χ n := by
  intro n
  induction n with
  | zero => simp [nsGenCascadeProduct, cascadeProduct]
  | succ n ih =>
      by_cases hn : n < m
      · simp [nsGenCascadeProduct, cascadeProduct, hn, Matrix.map_mul, ih]
      · simp [nsGenCascadeProduct, cascadeProduct, hn, ih]

/-- Generic parameter-ring final residue product. -/
noncomputable def nsGenCascadeFinalProduct (m k d : Nat) (h : Fin k) (χ : CascadeChain m k) :
    Matrix (Fin d) (Fin d) (NSParamRing (m + 1) k d) :=
  nsGenCascadeProduct m k d h χ m

@[simp] theorem map_nsGenCascadeFinalProduct {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (χ : CascadeChain m k) :
    (nsGenCascadeFinalProduct m k d h χ).map (MvPolynomial.eval (nsParamFlat θ)) =
      cascadeFinalProduct θ h χ := by
  simp [nsGenCascadeFinalProduct, cascadeFinalProduct]

/-- Generic parameter-ring ignition matrix. -/
noncomputable def nsGenCascadeIgnitionMatrix (m k d : Nat) (h : Fin k) (χ : CascadeChain m k)
    (j : Fin m) : Matrix (Fin d) (Fin d) (NSParamRing (m + 1) k d) :=
  nsGenSym ((nsGenCascadeProduct m k d h χ j.val)ᵀ *
    nsGenAttention (m + 1) k d (laterLayer j) (χ j) *
      nsGenCascadeProduct m k d h χ j.val)

@[simp] theorem map_nsGenCascadeIgnitionMatrix {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (χ : CascadeChain m k) (j : Fin m) :
    (nsGenCascadeIgnitionMatrix m k d h χ j).map (MvPolynomial.eval (nsParamFlat θ)) =
      cascadeIgnitionMatrix θ h χ j := by
  rw [nsGenCascadeIgnitionMatrix, cascadeIgnitionMatrix, map_nsGenSym]
  simp [Matrix.map_mul, Matrix.transpose_map]

/-- Parameter polynomial for one cascade chain value. -/
noncomputable def nsCascadeChainValuePoly (m k d : Nat) (h : Fin k) (χ : CascadeChain m k) :
    NSParamRing (m + 1) k d :=
  matrixFrobSqNSPoly (nsGenCascadeFinalProduct m k d h χ) *
    ∏ j : Fin m, matrixFrobSqNSPoly (nsGenCascadeIgnitionMatrix m k d h χ j)

@[simp] theorem eval_nsCascadeChainValuePoly {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (χ : CascadeChain m k) :
    MvPolynomial.eval (nsParamFlat θ) (nsCascadeChainValuePoly m k d h χ) =
      cascadeChainValue θ h χ := by
  simp only [nsCascadeChainValuePoly, map_mul, map_prod, eval_matrixFrobSqNSPoly,
    map_nsGenCascadeFinalProduct, map_nsGenCascadeIgnitionMatrix]
  rfl

/-- Canonical-chain cascade polynomial for one first-layer head. -/
noncomputable def nsCascadeCanonicalChainPoly (m k d : Nat) (h : Fin k) :
    NSParamRing (m + 1) k d :=
  nsCascadeChainValuePoly m k d h (cascadeCanonicalChain h)

@[simp] theorem eval_nsCascadeCanonicalChainPoly {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) :
    MvPolynomial.eval (nsParamFlat θ) (nsCascadeCanonicalChainPoly m k d h) =
      cascadeChainValue θ h (cascadeCanonicalChain h) := by
  simp [nsCascadeCanonicalChainPoly]

theorem nsCascadeCanonicalChainPoly_ne_zero {m k d : Nat} (hd : 0 < d) (h : Fin k) :
    nsCascadeCanonicalChainPoly m k d h ≠ 0 := by
  refine mvPolynomial_ne_zero_of_eval_ne_zero _ (nsParamFlat (cascadeIdentityWitness m k d)) ?_
  rw [eval_nsCascadeCanonicalChainPoly]
  exact (cascadeChainValue_ne_zero_iff_semantic _ h _).mpr
    (cascadeChainSemanticData_cascadeIdentityWitness hd h (cascadeCanonicalChain h))

/-- Finite cascade-certificate cover. -/
noncomputable def cascadeCover (m k d : Nat) (hd : 0 < d) :
    KHeadParamPolynomialPredicateCover (m + 1) k d (fun θ => CascadeCertificate θ) where
  κ := Fin k
  data :=
    { indices := Finset.univ
      poly := nsCascadeCanonicalChainPoly m k d
      nonzero := by
        intro h _hh
        exact nsCascadeCanonicalChainPoly_ne_zero hd h }
  carrier_subset := by
    intro θ hθ
    change CascadeCertificate θ
    intro h
    have hpoly : MvPolynomial.eval (nsParamFlat θ) (nsCascadeCanonicalChainPoly m k d h) ≠ 0 := by
      have := hθ h (Finset.mem_univ h)
      simpa only [nsParamFlat_eq_kHeadParamFlat] using this
    rw [eval_nsCascadeCanonicalChainPoly] at hpoly
    exact (cascadeHeadValue_ne_zero_iff_exists_chainValue_ne_zero θ h).mpr
      ⟨cascadeCanonicalChain h, hpoly⟩

/-! ## Multi-dial certificate cover

At the fixed evaluation point `(t, w) = (0, w₀)` the multi-dial Gram determinant
is a genuine parameter polynomial: every gradient column becomes a product of the
parameter-symbolic collapse/attention matrices applied to the constant vector
`w₀`.  Its nonvanishing implies `MultiDialCertificate` (NS072), and the
minimal-row-budget witness `certificateWitnessParams` makes it a nonzero
polynomial. -/

/-- Collapse of a tail layer is the collapse of the shifted original layer. -/
theorem collapseMatrix_tail {n k d : Nat} (θ : Params (n + 1) k d) (l : Fin n) :
    collapseMatrix (Fin.tail θ) l = collapseMatrix θ l.succ := rfl

/-- Parameter-symbolic collapse prefix product over the tail (TeX `C_{depth:1}`
for the tail, equivalently the all-zero-gate `frozenP`). -/
noncomputable def nsGenTailCollapsePrefix (n k d : Nat) :
    (depth : Nat) → depth ≤ n → Matrix (Fin d) (Fin d) (NSParamRing (n + 1) k d)
  | 0, _ => 1
  | j + 1, hj =>
      nsGenValueSum (n + 1) k d (Fin.succ ⟨j, Nat.lt_of_succ_le hj⟩) *
        nsGenTailCollapsePrefix n k d j (Nat.le_of_succ_le hj)

theorem map_nsGenTailCollapsePrefix {n k d : Nat} (θ : Params (n + 1) k d) :
    ∀ (depth : Nat) (hdepth : depth ≤ n),
      (nsGenTailCollapsePrefix n k d depth hdepth).map (MvPolynomial.eval (nsParamFlat θ)) =
        frozenP (Fin.tail θ) (allZeroGateFamily n k) depth hdepth := by
  intro depth
  induction depth with
  | zero =>
      intro hdepth
      rw [nsGenTailCollapsePrefix, frozenP_zero]
      exact Matrix.map_one _ (map_zero _) (map_one _)
  | succ j ih =>
      intro hdepth
      rw [nsGenTailCollapsePrefix, frozenP_succ, Matrix.map_mul,
        map_nsGenValueSum, ih (Nat.le_of_succ_le hdepth)]
      rw [collapseMatrix_tail θ ⟨j, Nat.lt_of_succ_le hdepth⟩]

/-- Parameter-symbolic level prefix matrix `C_{j-1:2}`. -/
noncomputable def nsGenLevelPrefix (n k d : Nat) (jb : LevelRowIndex (n + 1) k) :
    Matrix (Fin d) (Fin d) (NSParamRing (n + 1) k d) :=
  nsGenTailCollapsePrefix n k d (levelPrefixDepth jb) (levelPrefixDepth_le jb)

@[simp] theorem map_nsGenLevelPrefix {n k d : Nat} (θ : Params (n + 1) k d)
    (jb : LevelRowIndex (n + 1) k) :
    (nsGenLevelPrefix n k d jb).map (MvPolynomial.eval (nsParamFlat θ)) =
      levelPrefixMatrix θ jb := by
  rw [nsGenLevelPrefix, levelPrefixMatrix, map_nsGenTailCollapsePrefix]

/-- The dial contrast vector at `t = 0` collapses to `C₁ w`. -/
theorem dialContrast_zero_eq {n k d : Nat} (θ : Params (n + 1) k d) (w : Vec d) :
    dialContrast θ (0 : Fin k → Real) w = collapseMatrix θ 0 *ᵥ w := by
  simp [dialContrast]

/-- The level gradient at `t = 0` in single-matrix form. -/
theorem levelGradient_zero_eq {n k d : Nat} (θ : Params (n + 1) k d) (w : Vec d)
    (jb : LevelRowIndex (n + 1) k) :
    levelGradient θ (0 : Fin k → Real) w jb =
      ((levelFullPrefixMatrix θ jb)ᵀ * (attentionMatrix θ (levelLayer jb) jb.2)ᵀ *
        levelPrefixMatrix θ jb * collapseMatrix θ 0) *ᵥ w := by
  rw [levelGradient, dialContrast_zero_eq]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- Parameter-symbolic anchor gradient column. -/
noncomputable def nsGenAnchorGradCol (n k d : Nat) (w₀ : Vec d) (a : Fin k) :
    Fin d → NSParamRing (n + 1) k d :=
  (nsGenAttention (n + 1) k d 0 a)ᵀ *ᵥ nsConstVec w₀

theorem eval_nsGenAnchorGradCol {n k d : Nat} (θ : Params (n + 1) k d) (w₀ : Vec d)
    (a : Fin k) :
    (fun i => MvPolynomial.eval (nsParamFlat θ) (nsGenAnchorGradCol n k d w₀ a i)) =
      anchorGradient θ w₀ a := by
  rw [nsGenAnchorGradCol, eval_nsParamRing_mulVec]
  have h1 : ((nsGenAttention (n + 1) k d 0 a)ᵀ).map (MvPolynomial.eval (nsParamFlat θ)) =
      (attentionMatrix θ 0 a)ᵀ := by
    rw [Matrix.transpose_map, map_nsGenAttention]
  simp only [h1]
  have hw : (fun j => MvPolynomial.eval (nsParamFlat θ) (nsConstVec (L := n + 1) (k := k) w₀ j))
      = w₀ := by
    funext j; exact eval_nsConstVec θ w₀ j
  rw [hw]
  rfl

/-- Parameter-symbolic level gradient column at `t = 0`. -/
noncomputable def nsGenLevelGradCol (n k d : Nat) (w₀ : Vec d) (jb : LevelRowIndex (n + 1) k) :
    Fin d → NSParamRing (n + 1) k d :=
  ((nsGenLevelPrefix n k d jb * nsGenValueSum (n + 1) k d 0)ᵀ *
    (nsGenAttention (n + 1) k d (levelLayer jb) jb.2)ᵀ *
    nsGenLevelPrefix n k d jb * nsGenValueSum (n + 1) k d 0) *ᵥ nsConstVec w₀

theorem eval_nsGenLevelGradCol {n k d : Nat} (θ : Params (n + 1) k d) (w₀ : Vec d)
    (jb : LevelRowIndex (n + 1) k) :
    (fun i => MvPolynomial.eval (nsParamFlat θ) (nsGenLevelGradCol n k d w₀ jb i)) =
      levelGradient θ (0 : Fin k → Real) w₀ jb := by
  rw [nsGenLevelGradCol, eval_nsParamRing_mulVec, levelGradient_zero_eq]
  have hmap :
      (((nsGenLevelPrefix n k d jb * nsGenValueSum (n + 1) k d 0)ᵀ *
        (nsGenAttention (n + 1) k d (levelLayer jb) jb.2)ᵀ *
        nsGenLevelPrefix n k d jb * nsGenValueSum (n + 1) k d 0)).map
          (MvPolynomial.eval (nsParamFlat θ)) =
      (levelFullPrefixMatrix θ jb)ᵀ * (attentionMatrix θ (levelLayer jb) jb.2)ᵀ *
        levelPrefixMatrix θ jb * collapseMatrix θ 0 := by
    simp only [Matrix.map_mul, Matrix.transpose_map, map_nsGenLevelPrefix,
      map_nsGenValueSum, map_nsGenAttention, levelFullPrefixMatrix]
  rw [hmap]
  have hw : (fun j => MvPolynomial.eval (nsParamFlat θ) (nsConstVec (L := n + 1) (k := k) w₀ j))
      = w₀ := by
    funext j; exact eval_nsConstVec θ w₀ j
  rw [hw]

/-- Parameter-symbolic multi-dial gradient matrix at `(t, w) = (0, w₀)`. -/
noncomputable def nsGenMultiDialGradientMatrix (n k d : Nat) (w₀ : Vec d) :
    Matrix (Fin d) (MultiDialRow (n + 1) k) (NSParamRing (n + 1) k d) :=
  Matrix.of fun i row =>
    match row with
    | Sum.inl a => nsGenAnchorGradCol n k d w₀ a i
    | Sum.inr jb => nsGenLevelGradCol n k d w₀ jb i

theorem map_nsGenMultiDialGradientMatrix {n k d : Nat} (θ : Params (n + 1) k d)
    (w₀ : Vec d) :
    (nsGenMultiDialGradientMatrix n k d w₀).map (MvPolynomial.eval (nsParamFlat θ)) =
      multiDialGradientMatrix θ (0 : Fin k → Real) w₀ := by
  ext i row
  rw [Matrix.map_apply, multiDialGradientMatrix]
  rcases row with a | jb
  · change MvPolynomial.eval (nsParamFlat θ) (nsGenAnchorGradCol n k d w₀ a i) = _
    exact congrFun (eval_nsGenAnchorGradCol θ w₀ a) i
  · change MvPolynomial.eval (nsParamFlat θ) (nsGenLevelGradCol n k d w₀ jb i) = _
    exact congrFun (eval_nsGenLevelGradCol θ w₀ jb) i

/-- The multi-dial Gram determinant polynomial at the fixed evaluation point. -/
noncomputable def nsMultiDialGramEvalPoly (n k d : Nat) (w₀ : Vec d) :
    NSParamRing (n + 1) k d :=
  let G := nsGenMultiDialGradientMatrix n k d w₀
  (Gᵀ * G).det

theorem eval_nsMultiDialGramEvalPoly {n k d : Nat} (θ : Params (n + 1) k d) (w₀ : Vec d) :
    MvPolynomial.eval (nsParamFlat θ) (nsMultiDialGramEvalPoly n k d w₀) =
      multiDialGramDet θ (0 : Fin k → Real) w₀ := by
  let evalHom := MvPolynomial.eval (nsParamFlat θ)
  let Gp := nsGenMultiDialGradientMatrix n k d w₀
  change evalHom ((Gpᵀ * Gp).det) = multiDialGramDet θ 0 w₀
  rw [RingHom.map_det]
  change ((Gpᵀ * Gp).map evalHom).det = multiDialGramDet θ 0 w₀
  rw [Matrix.map_mul, Matrix.transpose_map, map_nsGenMultiDialGradientMatrix]
  rfl

theorem nsMultiDialGramEvalPoly_ne_zero {n k d : Nat} (hk : 0 < k)
    (hrows : k * (n + 1) ≤ d) :
    nsMultiDialGramEvalPoly n k d (certificateWitnessW hrows hk) ≠ 0 := by
  refine mvPolynomial_ne_zero_of_eval_ne_zero _
    (nsParamFlat (certificateWitnessParams hrows hk)) ?_
  rw [eval_nsMultiDialGramEvalPoly]
  have hwit := certificateWitness_multiDialGramDet_ne_zero hrows hk
  have ht : (certificateWitnessT (k := k)) = (0 : Fin k → Real) := rfl
  rw [ht] at hwit
  exact hwit

/-- Finite headwise certificate cover for positive head count.  The diagonal
witness is evaluated at the zero tuple, which lies in every scalar restriction
`t e_h`; one parameter polynomial therefore certifies all heads at once. -/
noncomputable def multiDialCoverPos (n k d : Nat) (hk : 0 < k) (hrows : k * (n + 1) ≤ d) :
    KHeadParamPolynomialPredicateCover (n + 1) k d
      (fun θ => HeadwiseDialCertificate θ) where
  κ := Unit
  data :=
    { indices := Finset.univ
      poly := fun _ => nsMultiDialGramEvalPoly n k d (certificateWitnessW hrows hk)
      nonzero := by
        intro _ _
        exact nsMultiDialGramEvalPoly_ne_zero hk hrows }
  carrier_subset := by
    intro θ hθ
    change HeadwiseDialCertificate θ
    have hpoly : MvPolynomial.eval (nsParamFlat θ)
        (nsMultiDialGramEvalPoly n k d (certificateWitnessW hrows hk)) ≠ 0 := by
      have := hθ () (Finset.mem_univ _)
      simpa only [nsParamFlat_eq_kHeadParamFlat] using this
    rw [eval_nsMultiDialGramEvalPoly] at hpoly
    exact headwiseDialCertificate_of_zero_gramDet θ
      (certificateWitnessW hrows hk) hpoly

/-- The multi-dial certificate is automatic when there are no heads. -/
theorem multiDialCertificate_of_k_zero {n d : Nat} (θ : Params (n + 1) 0 d) :
    HeadwiseDialCertificate θ :=
  headwiseDialCertificate_of_k_zero θ

/-- Finite multi-dial certificate cover. -/
noncomputable def multiDialCover (n k d : Nat) (hd : dStarNS (n + 1) k ≤ d) :
    KHeadParamPolynomialPredicateCover (n + 1) k d
      (fun θ => HeadwiseDialCertificate θ) :=
  match k with
  | 0 =>
      (KHeadParamPolynomialPredicateCover.trueCover (n + 1) 0 d).mono
        (fun θ _ => multiDialCertificate_of_k_zero θ)
  | k + 1 =>
      multiDialCoverPos n (k + 1) d (Nat.succ_pos k)
        (certificateWitness_rowBudget hd)

/-! ## Current-layer package cover -/

/-- Finite cover of the current-layer generic package (regularity, cascade,
multi-dial) at total depth `L+2`. -/
noncomputable def currentGenericCover (r L k d : Nat) (hd : dStarNS (L + 2) k ≤ d)
    (hk : 0 < k) :
    KHeadParamPolynomialPredicateCover (L + 2) k d (fun θ => CurrentGenericClauses r θ) :=
  have hd0 : 0 < d := lt_of_lt_of_le (dStarNS_pos (L + 2) k) hd
  (KHeadParamPolynomialPredicateCover.and
    (KHeadParamPolynomialPredicateCover.and
      (regularityCover (L + 2) k d hd0 hk)
      (cascadeCover (L + 1) k d hd0))
    (multiDialCover (L + 1) k d hd)).mono
    (fun _θ h => CurrentGenericClauses.of_components h.1.1 h.1.2 h.2)

/-! ## Recursive generic cover -/

/-- The finite recursive-generic polynomial cover, mirroring the base/successor
recursion of `RecursiveGeneric` (`def:recursive-G`).  Depth zero is the empty
family; depth one is regularity; every deeper total depth `L+2` combines the
lifted tail cover with the current-layer package. -/
noncomputable def recursiveGenericCover (r : Nat) :
    (L k d : Nat) → dStarNS L k ≤ d → 0 < k →
      KHeadParamPolynomialPredicateCover L k d (fun θ => RecursiveGeneric r L k d θ)
  | 0, k, d, _hd, _hk =>
      (KHeadParamPolynomialPredicateCover.trueCover 0 k d).mono (fun _θ _ => trivial)
  | 1, k, d, hd, hk =>
      (regularityCover 1 k d (lt_of_lt_of_le (dStarNS_pos 1 k) hd) hk).mono
        (fun _θ h => RecursiveGeneric.one h)
  | L + 2, k, d, hd, hk =>
      (KHeadParamPolynomialPredicateCover.tailAnd
        (recursiveGenericCover r (L + 1) k d ((dStarNS_tail_le (L + 1) k).trans hd) hk)
        (currentGenericCover r L k d hd hk)).mono
        (fun _θ h => RecursiveGeneric.succ_succ h.1 h.2)

/-- **NS080 main inclusion.**  The common nonvanishing locus of the finite
recursive-generic polynomial family is contained in the recursive generic set. -/
theorem recursiveGenericCover_carrier_subset (r L k d : Nat) (hd : dStarNS L k ≤ d)
    (hk : 0 < k) :
    kHeadParamNonvanishingCarrier (recursiveGenericCover r L k d hd hk).data ⊆
      RecursiveGenericSet r L k d :=
  (recursiveGenericCover r L k d hd hk).carrier_subset

end TransformerIdentifiability.NLayer.NoSkip
