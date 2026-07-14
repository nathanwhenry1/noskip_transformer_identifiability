import AnyLayerIdentifiabilityProof.NLayer.KHead.Core

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.KHead

/-!
# Factor-level identifiability scaffold

This file records the Lean API for `tex_modular/sections/10-factor-level.tex`.
The concrete content is the factor tuple, its induced matrix-level parameter,
change-of-basis actions inside one head, and proposition-valued statement
interfaces for TeX labels `lem-rank-factorization` and `cor-factor-fiber`.
-/

noncomputable section

/-! ## Invertible changes of basis -/

/-- A square invertible real matrix, used for the `GL_rho(R)` gauge in one head. -/
structure ChangeOfBasis (rho : Nat) where
  matrix : Matrix (Fin rho) (Fin rho) Real
  det_ne_zero : matrix.det ≠ 0

namespace ChangeOfBasis

variable {rho : Nat}

/-- The matrix inverse of a change of basis. -/
def invMatrix (G : ChangeOfBasis rho) : Matrix (Fin rho) (Fin rho) Real :=
  G.matrix⁻¹

@[simp]
theorem matrix_mul_invMatrix (G : ChangeOfBasis rho) :
    G.matrix * G.invMatrix = 1 := by
  exact Matrix.mul_nonsing_inv G.matrix (Ne.isUnit G.det_ne_zero)

@[simp]
theorem invMatrix_mul_matrix (G : ChangeOfBasis rho) :
    G.invMatrix * G.matrix = 1 := by
  exact Matrix.nonsing_inv_mul G.matrix (Ne.isUnit G.det_ne_zero)

/-- Change-of-basis data is extensional in the underlying matrix. -/
@[ext]
theorem ext {G H : ChangeOfBasis rho} (h : G.matrix = H.matrix) :
    G = H := by
  cases G with
  | mk Gmat Gdet =>
      cases H with
      | mk Hmat Hdet =>
          dsimp at h
          subst Hmat
          rfl

end ChangeOfBasis

/-- Multiplying one factor by `G` and the other by `G^{-1}` preserves the product. -/
@[simp]
theorem changeOfBasis_product {m rho n : Nat}
    (A : Matrix (Fin m) (Fin rho) Real)
    (B : Matrix (Fin rho) (Fin n) Real)
    (G : ChangeOfBasis rho) :
    (A * G.matrix) * (G.invMatrix * B) = A * B := by
  calc
    (A * G.matrix) * (G.invMatrix * B)
        = ((A * G.matrix) * G.invMatrix) * B := by
          rw [← Matrix.mul_assoc]
    _ = (A * (G.matrix * G.invMatrix)) * B := by
          exact congrArg (fun M => M * B)
            (Matrix.mul_assoc A G.matrix G.invMatrix)
    _ = A * B := by
          rw [ChangeOfBasis.matrix_mul_invMatrix G]
          simp

/-! ## Factor tuples and induced matrix parameters -/

/-- Factor representation of one head:
`V = valueOut * valueIn` and `A = keyTranspose * query`. -/
structure HeadFactors (d dv : Nat) where
  valueOut : Matrix (Fin d) (Fin dv) Real
  valueIn : Matrix (Fin dv) (Fin d) Real
  keyTranspose : Matrix (Fin d) (Fin d) Real
  query : Matrix (Fin d) (Fin d) Real

namespace HeadFactors

variable {d dv : Nat}

/-- The value product `V = W_O W_V`. -/
def valueProduct (F : HeadFactors d dv) : Matrix (Fin d) (Fin d) Real :=
  F.valueOut * F.valueIn

/-- The attention product `A = W_K^T W_Q`, storing `W_K^T` directly. -/
def attentionProduct (F : HeadFactors d dv) : Matrix (Fin d) (Fin d) Real :=
  F.keyTranspose * F.query

/-- The matrix-level head corresponding to the factor-level head. -/
def toMatrixHead (F : HeadFactors d dv) :
    Matrix (Fin d) (Fin d) Real × Matrix (Fin d) (Fin d) Real :=
  (F.valueProduct, F.attentionProduct)

@[simp]
theorem toMatrixHead_fst (F : HeadFactors d dv) :
    F.toMatrixHead.1 = F.valueProduct :=
  rfl

@[simp]
theorem toMatrixHead_snd (F : HeadFactors d dv) :
    F.toMatrixHead.2 = F.attentionProduct :=
  rfl

/-- Independent value and attention changes of basis inside one head. -/
def changeBasis (F : HeadFactors d dv)
    (Gv : ChangeOfBasis dv) (Ga : ChangeOfBasis d) : HeadFactors d dv where
  valueOut := F.valueOut * Gv.matrix
  valueIn := Gv.invMatrix * F.valueIn
  keyTranspose := F.keyTranspose * Ga.matrix
  query := Ga.invMatrix * F.query

@[simp]
theorem valueProduct_changeBasis (F : HeadFactors d dv)
    (Gv : ChangeOfBasis dv) (Ga : ChangeOfBasis d) :
    valueProduct (changeBasis F Gv Ga) = valueProduct F := by
  simp [valueProduct, changeBasis]

@[simp]
theorem attentionProduct_changeBasis (F : HeadFactors d dv)
    (Gv : ChangeOfBasis dv) (Ga : ChangeOfBasis d) :
    attentionProduct (changeBasis F Gv Ga) = attentionProduct F := by
  simp [attentionProduct, changeBasis]

@[simp]
theorem toMatrixHead_changeBasis (F : HeadFactors d dv)
    (Gv : ChangeOfBasis dv) (Ga : ChangeOfBasis d) :
    toMatrixHead (changeBasis F Gv Ga) = toMatrixHead F := by
  simp [toMatrixHead]

end HeadFactors

/-- Depth-`L`, `k`-head factor-level parameter family. -/
abbrev FactorParams (L k d dv : Nat) : Type :=
  Fin L → Fin k → HeadFactors d dv

/-- The matrix-level parameter induced by a factor-level parameter. -/
def factorParamsToMatrices {L k d dv : Nat}
    (phi : FactorParams L k d dv) : Params L k d :=
  fun l a => (phi l a).toMatrixHead

@[simp]
theorem valueMatrix_factorParamsToMatrices {L k d dv : Nat}
    (phi : FactorParams L k d dv) (l : Fin L) (a : Fin k) :
    valueMatrix (factorParamsToMatrices phi) l a =
      HeadFactors.valueProduct (phi l a) :=
  rfl

@[simp]
theorem attentionMatrix_factorParamsToMatrices {L k d dv : Nat}
    (phi : FactorParams L k d dv) (l : Fin L) (a : Fin k) :
    attentionMatrix (factorParamsToMatrices phi) l a =
      HeadFactors.attentionProduct (phi l a) :=
  rfl

/-- Equality of the realized factor-level networks at a fixed token count. -/
def FactorRealizationEq {L k d dv T : Nat}
    (phi psi : FactorParams L k d dv) : Prop :=
  ∀ X : Matrix (Fin d) (Fin T) Real,
    transformer (factorParamsToMatrices phi) X =
      transformer (factorParamsToMatrices psi) X

/-! ## TeX `lem-rank-factorization` as an API -/

/-- Full rank of the middle-dimension product in a rank-factorization input. -/
def ProductFullRank {m rho n : Nat}
    (A : Matrix (Fin m) (Fin rho) Real)
    (B : Matrix (Fin rho) (Fin n) Real) : Prop :=
  Matrix.rank (A * B) = rho

namespace ProductFullRank

variable {m rho n : Nat}
variable {A : Matrix (Fin m) (Fin rho) Real}
variable {B : Matrix (Fin rho) (Fin n) Real}

/-- A full-rank middle product forces the left factor to have full column rank. -/
theorem left_rank_eq (h : ProductFullRank A B) :
    Matrix.rank A = rho := by
  apply le_antisymm
  · exact Matrix.rank_le_width A
  · have hle := Matrix.rank_mul_le_left A B
    rwa [h] at hle

/-- A full-rank middle product forces the right factor to have full row rank. -/
theorem right_rank_eq (h : ProductFullRank A B) :
    Matrix.rank B = rho := by
  apply le_antisymm
  · exact (Matrix.rank_le_card_height B).trans (Fintype.card_fin rho).le
  · have hle := Matrix.rank_mul_le_right A B
    rwa [h] at hle

/-- Full product rank makes left multiplication by the left factor injective. -/
theorem left_mulVecLin_injective (h : ProductFullRank A B) :
    Function.Injective A.mulVecLin := by
  have hrank : Module.finrank Real (LinearMap.range A.mulVecLin) =
      Module.finrank Real (Fin rho → Real) := by
    simpa [Matrix.rank, Module.finrank_fintype_fun_eq_card] using h.left_rank_eq
  have hsum := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  rw [hrank] at hsum
  have hker_rank : Module.finrank Real (LinearMap.ker A.mulVecLin) = 0 :=
    by omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hker_rank)

/-- Full product rank makes right multiplication by the right factor surjective. -/
theorem right_mulVecLin_surjective (h : ProductFullRank A B) :
    Function.Surjective B.mulVecLin := by
  have hrange : LinearMap.range B.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    simpa [Matrix.rank, Module.finrank_fintype_fun_eq_card] using h.right_rank_eq
  exact LinearMap.range_eq_top.mp hrange

/-- Left cancellation by a full-column-rank factor. -/
theorem left_cancel {q : Nat}
    {C C' : Matrix (Fin rho) (Fin q) Real}
    (h : ProductFullRank A B) (hC : A * C = A * C') :
    C = C' := by
  apply Matrix.toLin'.injective
  have hlin := congrArg Matrix.toLin' hC
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul] at hlin
  exact (LinearMap.cancel_left
    (by simpa [Matrix.toLin'_apply'] using h.left_mulVecLin_injective)).mp hlin

/-- Right cancellation by a full-row-rank factor. -/
theorem right_cancel {q : Nat}
    {D D' : Matrix (Fin q) (Fin rho) Real}
    (h : ProductFullRank A B) (hD : D * B = D' * B) :
    D = D' := by
  apply Matrix.toLin'.injective
  have hlin := congrArg Matrix.toLin' hD
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul] at hlin
  exact (LinearMap.cancel_right
    (by simpa [Matrix.toLin'_apply'] using h.right_mulVecLin_surjective)).mp hlin

end ProductFullRank

/-- Hypotheses of TeX `lem-rank-factorization`. -/
structure RankFactorizationHyp {m rho n : Nat}
    (A A' : Matrix (Fin m) (Fin rho) Real)
    (B B' : Matrix (Fin rho) (Fin n) Real) : Prop where
  product_eq : A * B = A' * B'
  product_full_rank : ProductFullRank A B

namespace RankFactorizationHyp

variable {m rho n : Nat}
variable {A A' : Matrix (Fin m) (Fin rho) Real}
variable {B B' : Matrix (Fin rho) (Fin n) Real}

/-- The primed product is full rank as well, by equality of products. -/
theorem primed_product_full_rank (h : RankFactorizationHyp A A' B B') :
    ProductFullRank A' B' := by
  dsimp [ProductFullRank]
  rw [← h.product_eq]
  exact h.product_full_rank

end RankFactorizationHyp

namespace RankFactorization

variable {m rho n : Nat}
variable {A A' : Matrix (Fin m) (Fin rho) Real}
variable {B B' : Matrix (Fin rho) (Fin n) Real}

/-- Product equality and surjectivity of the right primed factor put the primed
left-factor range inside the unprimed left-factor range. -/
theorem left_range_le_of_product_eq
    (hprod : A * B = A' * B')
    (hB' : Function.Surjective B'.mulVecLin) :
    LinearMap.range A'.mulVecLin ≤ LinearMap.range A.mulVecLin := by
  intro y hy
  rcases hy with ⟨x, rfl⟩
  rcases hB' x with ⟨z, hz⟩
  refine ⟨B.mulVecLin z, ?_⟩
  have hlin := congrArg Matrix.toLin' hprod
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul] at hlin
  have hzlin := congrArg (fun f => f z) hlin
  simpa [Matrix.toLin'_apply', hz] using hzlin

/-- The transition linear map `G` defined by `A' = A G` when the columns of
`A'` lie in the range of the injective map `A`. -/
noncomputable def leftTransitionLin
    (hAinj : Function.Injective A.mulVecLin)
    (hrange : LinearMap.range A'.mulVecLin ≤ LinearMap.range A.mulVecLin) :
    (Fin rho → Real) →ₗ[Real] (Fin rho → Real) :=
  let e := LinearEquiv.ofInjective A.mulVecLin hAinj
  e.symm.toLinearMap.comp
    (LinearMap.codRestrict (LinearMap.range A.mulVecLin) A'.mulVecLin
      (fun x => hrange ⟨x, rfl⟩))

/-- Matrix form of `leftTransitionLin`. -/
noncomputable def leftTransition
    (hAinj : Function.Injective A.mulVecLin)
    (hrange : LinearMap.range A'.mulVecLin ≤ LinearMap.range A.mulVecLin) :
    Matrix (Fin rho) (Fin rho) Real :=
  LinearMap.toMatrix' (leftTransitionLin (A := A) (A' := A') hAinj hrange)

/-- The transition matrix satisfies `A' = A * G`. -/
theorem leftTransition_spec
    (hAinj : Function.Injective A.mulVecLin)
    (hrange : LinearMap.range A'.mulVecLin ≤ LinearMap.range A.mulVecLin) :
    A' = A * leftTransition (A := A) (A' := A') hAinj hrange := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, leftTransition, Matrix.toLin'_toMatrix']
  apply LinearMap.ext
  intro x
  ext i
  let e := LinearEquiv.ofInjective A.mulVecLin hAinj
  let Glin := leftTransitionLin (A := A) (A' := A') hAinj hrange
  change A'.mulVecLin x i = A.mulVecLin (Glin x) i
  have hsub : e (Glin x) =
      ⟨A'.mulVecLin x, hrange ⟨x, rfl⟩⟩ := by
    dsimp [Glin, leftTransitionLin]
    exact e.apply_symm_apply ⟨A'.mulVecLin x, hrange ⟨x, rfl⟩⟩
  have hval := congrArg Subtype.val hsub
  exact (congrFun hval i).symm

end RankFactorization

/-- One concrete witness for the conclusion of TeX `lem-rank-factorization`. -/
structure RankFactorizationWitness {m rho n : Nat}
    (A A' : Matrix (Fin m) (Fin rho) Real)
    (B B' : Matrix (Fin rho) (Fin n) Real) where
  G : ChangeOfBasis rho
  left_eq : A' = A * G.matrix
  right_eq : B' = G.invMatrix * B

namespace RankFactorizationWitness

variable {m rho n : Nat}
variable {A A' : Matrix (Fin m) (Fin rho) Real}
variable {B B' : Matrix (Fin rho) (Fin n) Real}

/-- A displayed gauge witness automatically preserves the matrix product. -/
theorem product_eq (W : RankFactorizationWitness A A' B B') :
    A' * B' = A * B := by
  rcases W with ⟨G, hleft, hright⟩
  subst A'
  subst B'
  exact changeOfBasis_product A B G

/-- Under the full-rank hypothesis on the unprimed factorization, two displayed
rank-factorization witnesses have the same gauge. -/
theorem gauge_eq_of_productFullRank
    (W W' : RankFactorizationWitness A A' B B')
    (hfull : ProductFullRank A B) :
    W.G = W'.G := by
  apply ChangeOfBasis.ext
  apply hfull.left_cancel
  rw [← W.left_eq, ← W'.left_eq]

end RankFactorizationWitness

/-- Conclusion of TeX `lem-rank-factorization`, including uniqueness of `G`. -/
def RankFactorizationConclusion {m rho n : Nat}
    (A A' : Matrix (Fin m) (Fin rho) Real)
    (B B' : Matrix (Fin rho) (Fin n) Real) : Prop :=
  ∃! G : ChangeOfBasis rho,
    A' = A * G.matrix ∧ B' = G.invMatrix * B

namespace RankFactorizationWitness

variable {m rho n : Nat}
variable {A A' : Matrix (Fin m) (Fin rho) Real}
variable {B B' : Matrix (Fin rho) (Fin n) Real}

/-- A displayed rank-factorization witness plus full product rank proves the
existential-and-unique conclusion of the rank-factorization lemma. -/
theorem conclusion_of_productFullRank
    (W : RankFactorizationWitness A A' B B')
    (hfull : ProductFullRank A B) :
    RankFactorizationConclusion A A' B B' := by
  refine ⟨W.G, ⟨W.left_eq, W.right_eq⟩, ?_⟩
  intro G hG
  apply ChangeOfBasis.ext
  apply hfull.left_cancel
  rw [← W.left_eq, ← hG.1]

end RankFactorizationWitness

/-- Stable API name for TeX `lem-rank-factorization`. -/
theorem lem_rank_factorization {m rho n : Nat}
    (A A' : Matrix (Fin m) (Fin rho) Real)
    (B B' : Matrix (Fin rho) (Fin n) Real) :
  RankFactorizationHyp A A' B B' →
    RankFactorizationConclusion A A' B B' := by
  intro h
  let hfull := h.product_full_rank
  let hfull' := h.primed_product_full_rank
  have hAinj : Function.Injective A.mulVecLin := hfull.left_mulVecLin_injective
  have hA'inj : Function.Injective A'.mulVecLin := hfull'.left_mulVecLin_injective
  have hBsurj : Function.Surjective B.mulVecLin := hfull.right_mulVecLin_surjective
  have hB'surj : Function.Surjective B'.mulVecLin := hfull'.right_mulVecLin_surjective
  let hrange : LinearMap.range A'.mulVecLin ≤ LinearMap.range A.mulVecLin :=
    RankFactorization.left_range_le_of_product_eq h.product_eq hB'surj
  let hrange' : LinearMap.range A.mulVecLin ≤ LinearMap.range A'.mulVecLin :=
    RankFactorization.left_range_le_of_product_eq h.product_eq.symm hBsurj
  let Gmat : Matrix (Fin rho) (Fin rho) Real :=
    RankFactorization.leftTransition (A := A) (A' := A') hAinj hrange
  let Hmat : Matrix (Fin rho) (Fin rho) Real :=
    RankFactorization.leftTransition (A := A') (A' := A) hA'inj hrange'
  have hleft : A' = A * Gmat :=
    RankFactorization.leftTransition_spec (A := A) (A' := A') hAinj hrange
  have hleft' : A = A' * Hmat :=
    RankFactorization.leftTransition_spec (A := A') (A' := A) hA'inj hrange'
  have hGH : Gmat * Hmat = 1 := by
    have hcancel : (1 : Matrix (Fin rho) (Fin rho) Real) = Gmat * Hmat := by
      apply hfull.left_cancel
      calc
        A * (1 : Matrix (Fin rho) (Fin rho) Real) = A := by simp
        _ = A' * Hmat := hleft'
        _ = (A * Gmat) * Hmat := by rw [hleft]
        _ = A * (Gmat * Hmat) := by rw [Matrix.mul_assoc]
    exact hcancel.symm
  have hGdet : Gmat.det ≠ 0 := by
    have hunitG : IsUnit Gmat := isUnit_iff_exists_inv.mpr ⟨Hmat, hGH⟩
    exact (Matrix.isUnit_iff_isUnit_det Gmat).mp hunitG |>.ne_zero
  let G : ChangeOfBasis rho := ⟨Gmat, hGdet⟩
  have hB : B = Gmat * B' := by
    apply hfull.left_cancel
    calc
      A * B = A' * B' := h.product_eq
      _ = (A * Gmat) * B' := by rw [← hleft]
      _ = A * (Gmat * B') := by rw [Matrix.mul_assoc]
  have hright : B' = G.invMatrix * B := by
    calc
      B' = (1 : Matrix (Fin rho) (Fin rho) Real) * B' := by simp
      _ = (G.invMatrix * G.matrix) * B' := by rw [ChangeOfBasis.invMatrix_mul_matrix G]
      _ = G.invMatrix * (G.matrix * B') := by rw [Matrix.mul_assoc]
      _ = G.invMatrix * B := by rw [← hB]
  exact (RankFactorizationWitness.conclusion_of_productFullRank
    (A := A) (A' := A') (B := B) (B' := B')
    ⟨G, hleft, hright⟩ hfull)

/-! ## Extracting the gauge from rank factorization -/

/-- The canonical gauge chosen from `lem_rank_factorization`. -/
noncomputable def rankFactorizationBasis {m rho n : Nat}
    {A A' : Matrix (Fin m) (Fin rho) Real}
    {B B' : Matrix (Fin rho) (Fin n) Real}
    (hprod : A * B = A' * B') (hfull : ProductFullRank A B) :
    ChangeOfBasis rho :=
  Classical.choose
    (lem_rank_factorization A A' B B'
      ⟨hprod, hfull⟩)

theorem rankFactorizationBasis_left_eq {m rho n : Nat}
    {A A' : Matrix (Fin m) (Fin rho) Real}
    {B B' : Matrix (Fin rho) (Fin n) Real}
    (hprod : A * B = A' * B') (hfull : ProductFullRank A B) :
    A' = A * (rankFactorizationBasis hprod hfull).matrix := by
  exact (Classical.choose_spec
    (lem_rank_factorization A A' B B'
      ⟨hprod, hfull⟩)).1.1

theorem rankFactorizationBasis_right_eq {m rho n : Nat}
    {A A' : Matrix (Fin m) (Fin rho) Real}
    {B B' : Matrix (Fin rho) (Fin n) Real}
    (hprod : A * B = A' * B') (hfull : ProductFullRank A B) :
    B' = (rankFactorizationBasis hprod hfull).invMatrix * B := by
  exact (Classical.choose_spec
    (lem_rank_factorization A A' B B'
      ⟨hprod, hfull⟩)).1.2

/-! ## Factor-level fiber interface -/

/-- The primed factor tuple satisfies the generic rank assumptions used in the
factor-level packet. -/
structure FactorFullRank {L k d dv : Nat}
    (phi : FactorParams L k d dv) : Prop where
  value_full_rank :
    ∀ l : Fin L, ∀ a : Fin k,
      ProductFullRank (phi l a).valueOut (phi l a).valueIn
  attention_full_rank :
    ∀ l : Fin L, ∀ a : Fin k,
      ProductFullRank (phi l a).keyTranspose (phi l a).query

/-- Matrix-level fiber data, with the layerwise head permutations already chosen. -/
structure MatrixLevelFiberWitness {L k d : Nat}
    (theta theta' : Params L k d) where
  pi : ∀ _l : Fin L, Equiv.Perm (Fin k)
  value_eq :
    ∀ l : Fin L, ∀ a : Fin k,
      valueMatrix theta l a = valueMatrix theta' l (pi l a)
  attention_eq :
    ∀ l : Fin L, ∀ a : Fin k,
      attentionMatrix theta l a = attentionMatrix theta' l (pi l a)

/-- Factor-level fiber data: layerwise head permutations and independent value
and attention gauges in each head. -/
structure FactorFiberWitness {L k d dv : Nat}
    (phi phi' : FactorParams L k d dv) where
  pi : ∀ _l : Fin L, Equiv.Perm (Fin k)
  valueBasis : ∀ _l : Fin L, Fin k → ChangeOfBasis dv
  attentionBasis : ∀ _l : Fin L, Fin k → ChangeOfBasis d
  valueOut_eq :
    ∀ l : Fin L, ∀ a : Fin k,
      (phi l a).valueOut =
        (phi' l (pi l a)).valueOut * (valueBasis l a).matrix
  valueIn_eq :
    ∀ l : Fin L, ∀ a : Fin k,
      (phi l a).valueIn =
        (valueBasis l a).invMatrix * (phi' l (pi l a)).valueIn
  keyTranspose_eq :
    ∀ l : Fin L, ∀ a : Fin k,
      (phi l a).keyTranspose =
        (phi' l (pi l a)).keyTranspose * (attentionBasis l a).matrix
  query_eq :
    ∀ l : Fin L, ∀ a : Fin k,
      (phi l a).query =
        (attentionBasis l a).invMatrix * (phi' l (pi l a)).query

namespace FactorFiberWitness

variable {L k d dv : Nat}
variable {phi phi' : FactorParams L k d dv}

/-- A factor-level fiber witness gives equality of value products after the
stored layerwise permutation. -/
theorem valueProduct_eq (W : FactorFiberWitness phi phi')
    (l : Fin L) (a : Fin k) :
    HeadFactors.valueProduct (phi l a) =
      HeadFactors.valueProduct (phi' l (W.pi l a)) := by
  rw [HeadFactors.valueProduct, W.valueOut_eq l a, W.valueIn_eq l a]
  exact changeOfBasis_product
    (phi' l (W.pi l a)).valueOut
    (phi' l (W.pi l a)).valueIn
    (W.valueBasis l a)

/-- A factor-level fiber witness gives equality of attention products after the
stored layerwise permutation. -/
theorem attentionProduct_eq (W : FactorFiberWitness phi phi')
    (l : Fin L) (a : Fin k) :
    HeadFactors.attentionProduct (phi l a) =
      HeadFactors.attentionProduct (phi' l (W.pi l a)) := by
  rw [HeadFactors.attentionProduct, W.keyTranspose_eq l a, W.query_eq l a]
  exact changeOfBasis_product
    (phi' l (W.pi l a)).keyTranspose
    (phi' l (W.pi l a)).query
    (W.attentionBasis l a)

/-- Forget the factor gauges and retain only the induced matrix-level fiber
witness. -/
def toMatrixLevelFiberWitness (W : FactorFiberWitness phi phi') :
    MatrixLevelFiberWitness
      (factorParamsToMatrices phi) (factorParamsToMatrices phi') where
  pi := W.pi
  value_eq := by
    intro l a
    exact W.valueProduct_eq l a
  attention_eq := by
    intro l a
    exact W.attentionProduct_eq l a

end FactorFiberWitness

/-- Lift a matrix-level fiber witness for induced products to a factor-level
fiber witness, using the full-rank hypotheses on the primed factorization to
recover the headwise change-of-basis gauges. -/
noncomputable def factorFiberWitness_of_matrixLevelFiberWitness
    {L k d dv : Nat}
    {phi phi' : FactorParams L k d dv}
    (hM : MatrixLevelFiberWitness
      (factorParamsToMatrices phi) (factorParamsToMatrices phi'))
    (hfull' : FactorFullRank phi') :
    FactorFiberWitness phi phi' := by
  let valueBasis : ∀ _l : Fin L, Fin k → ChangeOfBasis dv :=
    fun l a =>
      rankFactorizationBasis
        (A := (phi' l (hM.pi l a)).valueOut)
        (A' := (phi l a).valueOut)
        (B := (phi' l (hM.pi l a)).valueIn)
        (B' := (phi l a).valueIn)
        (by
          simpa [HeadFactors.valueProduct] using (hM.value_eq l a).symm)
        (hfull'.value_full_rank l (hM.pi l a))
  let attentionBasis : ∀ _l : Fin L, Fin k → ChangeOfBasis d :=
    fun l a =>
      rankFactorizationBasis
        (A := (phi' l (hM.pi l a)).keyTranspose)
        (A' := (phi l a).keyTranspose)
        (B := (phi' l (hM.pi l a)).query)
        (B' := (phi l a).query)
        (by
          simpa [HeadFactors.attentionProduct] using (hM.attention_eq l a).symm)
        (hfull'.attention_full_rank l (hM.pi l a))
  refine
    { pi := hM.pi
      valueBasis := valueBasis
      attentionBasis := attentionBasis
      valueOut_eq := ?_
      valueIn_eq := ?_
      keyTranspose_eq := ?_
      query_eq := ?_ }
  · intro l a
    dsimp [valueBasis]
    exact rankFactorizationBasis_left_eq
      (A := (phi' l (hM.pi l a)).valueOut)
      (A' := (phi l a).valueOut)
      (B := (phi' l (hM.pi l a)).valueIn)
      (B' := (phi l a).valueIn)
      (by
        simpa [HeadFactors.valueProduct] using (hM.value_eq l a).symm)
      (hfull'.value_full_rank l (hM.pi l a))
  · intro l a
    dsimp [valueBasis]
    exact rankFactorizationBasis_right_eq
      (A := (phi' l (hM.pi l a)).valueOut)
      (A' := (phi l a).valueOut)
      (B := (phi' l (hM.pi l a)).valueIn)
      (B' := (phi l a).valueIn)
      (by
        simpa [HeadFactors.valueProduct] using (hM.value_eq l a).symm)
      (hfull'.value_full_rank l (hM.pi l a))
  · intro l a
    dsimp [attentionBasis]
    exact rankFactorizationBasis_left_eq
      (A := (phi' l (hM.pi l a)).keyTranspose)
      (A' := (phi l a).keyTranspose)
      (B := (phi' l (hM.pi l a)).query)
      (B' := (phi l a).query)
      (by
        simpa [HeadFactors.attentionProduct] using (hM.attention_eq l a).symm)
      (hfull'.attention_full_rank l (hM.pi l a))
  · intro l a
    dsimp [attentionBasis]
    exact rankFactorizationBasis_right_eq
      (A := (phi' l (hM.pi l a)).keyTranspose)
      (A' := (phi l a).keyTranspose)
      (B := (phi' l (hM.pi l a)).query)
      (B' := (phi l a).query)
      (by
        simpa [HeadFactors.attentionProduct] using (hM.attention_eq l a).symm)
      (hfull'.attention_full_rank l (hM.pi l a))

/-- The factor-level generic predicate obtained by combining an abstract
matrix-level generic predicate with the rank assumptions of this packet. -/
def FactorGenericForFiber {L k d dv : Nat}
    (MatrixGeneric : Params L k d → Prop)
    (phi : FactorParams L k d dv) : Prop :=
  MatrixGeneric (factorParamsToMatrices phi) ∧ FactorFullRank phi

/-- Stable API name for TeX `cor-factor-fiber`.

The matrix-level generic predicate is left abstract so this file does not depend
on the downstream matrix-fiber packet. -/
def cor_factor_fiber {L k d dv T : Nat}
    (MatrixGeneric : Params L k d → Prop) : Prop :=
  ∀ phi' : FactorParams L k d dv,
    FactorGenericForFiber MatrixGeneric phi' →
      ∀ phi : FactorParams L k d dv,
        FactorRealizationEq (T := T) phi phi' ↔
          ∃ _witness : FactorFiberWitness phi phi', True

end

end TransformerIdentifiability.NLayer.KHead
