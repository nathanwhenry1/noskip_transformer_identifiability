import AnyLayerIdentifiabilityProof.NLayer.NoSkip.MatrixFiber
import AnyLayerIdentifiabilityProof.NLayer.KHead.FactorLevel

set_option autoImplicit false

open Matrix

namespace TransformerIdentifiability.NLayer.NoSkip

noncomputable section

/-! # Factor-level recovery with interface and inner gauges -/

abbrev FactorParams (L k d dv : Nat) := KHead.FactorParams L k d dv
abbrev HeadFactors (d dv : Nat) := KHead.HeadFactors d dv
abbrev ChangeOfBasis (rho : Nat) := KHead.ChangeOfBasis rho
abbrev FactorFullRank {L k d dv : Nat} :=
  @KHead.FactorFullRank L k d dv

/-- Matrix parameters induced by a no-skip factor tuple. -/
def factorParamsToMatrices {L k d dv : Nat}
    (phi : FactorParams L k d dv) : Params L k d :=
  KHead.factorParamsToMatrices phi

@[simp] theorem valueMatrix_factorParamsToMatrices {L k d dv : Nat}
    (phi : FactorParams L k d dv) (l : Fin L) (a : Fin k) :
    valueMatrix (factorParamsToMatrices phi) l a =
      KHead.HeadFactors.valueProduct (phi l a) :=
  rfl

@[simp] theorem attentionMatrix_factorParamsToMatrices {L k d dv : Nat}
    (phi : FactorParams L k d dv) (l : Fin L) (a : Fin k) :
    attentionMatrix (factorParamsToMatrices phi) l a =
      KHead.HeadFactors.attentionProduct (phi l a) :=
  rfl

/-- Left and right multiplication by nonsingular square matrices preserve the
middle rank of a factorization. -/
theorem productFullRank_mul_invertibles
    {d rho : Nat} {A : Matrix (Fin d) (Fin rho) Real}
    {B : Matrix (Fin rho) (Fin d) Real}
    (hfull : KHead.ProductFullRank A B)
    (L R : Matrix (Fin d) (Fin d) Real)
    (hL : IsUnit L.det) (hR : IsUnit R.det) :
    KHead.ProductFullRank (L * A) (B * R) := by
  dsimp [KHead.ProductFullRank] at hfull ⊢
  calc
    Matrix.rank ((L * A) * (B * R)) =
        Matrix.rank (L * (A * B) * R) := by
      congr 1
      simp only [Matrix.mul_assoc]
    _ = Matrix.rank (L * (A * B)) :=
      Matrix.rank_mul_eq_left_of_isUnit_det R (L * (A * B)) hR
    _ = Matrix.rank (A * B) :=
      Matrix.rank_mul_eq_right_of_isUnit_det L (A * B) hL
    _ = rho := hfull

section GaugedFactors

variable {L k d dv : Nat} {phi phi' : FactorParams L k d dv}
  (M : TargetToSourceMatching
    (factorParamsToMatrices phi) (factorParamsToMatrices phi'))

/-- Source-to-target head index associated with the target-to-source matching. -/
def factorTargetHead (l : Fin L) (a : Fin k) : Fin k :=
  (M.headPerm l).symm a

def gaugedTargetValueOut (l : Fin L) (a : Fin k) :
    Matrix (Fin d) (Fin dv) Real :=
  (M.gauge.get l.succ).invMatrix *
    (phi' l (factorTargetHead M l a)).valueOut

def gaugedTargetValueIn (l : Fin L) (a : Fin k) :
    Matrix (Fin dv) (Fin d) Real :=
  (phi' l (factorTargetHead M l a)).valueIn *
    (M.gauge.get l.castSucc).matrix

def gaugedTargetKeyTranspose (l : Fin L) (a : Fin k) :
    Matrix (Fin d) (Fin d) Real :=
  ((M.gauge.get l.castSucc).matrix)ᵀ *
    (phi' l (factorTargetHead M l a)).keyTranspose

def gaugedTargetQuery (l : Fin L) (a : Fin k) :
    Matrix (Fin d) (Fin d) Real :=
  (phi' l (factorTargetHead M l a)).query *
    (M.gauge.get l.castSucc).matrix

theorem valueProduct_eq_gaugedTarget (l : Fin L) (a : Fin k) :
    KHead.HeadFactors.valueProduct (phi l a) =
      gaugedTargetValueOut M l a * gaugedTargetValueIn M l a := by
  let h : Fin k := factorTargetHead M l a
  have heq := M.value_eq l h
  simpa [h, factorTargetHead, gaugedTargetValueOut, gaugedTargetValueIn,
    KHead.HeadFactors.valueProduct, Matrix.mul_assoc] using heq

theorem attentionProduct_eq_gaugedTarget (l : Fin L) (a : Fin k) :
    KHead.HeadFactors.attentionProduct (phi l a) =
      gaugedTargetKeyTranspose M l a * gaugedTargetQuery M l a := by
  let h : Fin k := factorTargetHead M l a
  have heq := M.attention_eq l h
  simpa [h, factorTargetHead, gaugedTargetKeyTranspose, gaugedTargetQuery,
    KHead.HeadFactors.attentionProduct, Matrix.mul_assoc] using heq

theorem gaugedTarget_value_fullRank (hfull : FactorFullRank phi')
    (l : Fin L) (a : Fin k) :
    KHead.ProductFullRank (gaugedTargetValueOut M l a)
      (gaugedTargetValueIn M l a) := by
  apply productFullRank_mul_invertibles
    (hfull.value_full_rank l (factorTargetHead M l a))
  · exact Matrix.isUnit_nonsing_inv_det (M.gauge.get l.succ).matrix
      (Ne.isUnit (M.gauge.get l.succ).det_ne_zero)
  · exact Ne.isUnit (M.gauge.get l.castSucc).det_ne_zero

theorem gaugedTarget_attention_fullRank (hfull : FactorFullRank phi')
    (l : Fin L) (a : Fin k) :
    KHead.ProductFullRank (gaugedTargetKeyTranspose M l a)
      (gaugedTargetQuery M l a) := by
  apply productFullRank_mul_invertibles
    (hfull.attention_full_rank l (factorTargetHead M l a))
  · exact Matrix.isUnit_det_transpose _
      (Ne.isUnit (M.gauge.get l.castSucc).det_ne_zero)
  · exact Ne.isUnit (M.gauge.get l.castSucc).det_ne_zero

end GaugedFactors

/-- Factor-level conclusion: the matrix matching is unique, and for each
matched head the two product factorizations have unique inner bases. -/
structure FactorLevelIdentifiabilityConclusion
    {L k d dv : Nat} (phi phi' : FactorParams L k d dv) : Type where
  matching : TargetToSourceMatching
    (factorParamsToMatrices phi) (factorParamsToMatrices phi')
  matching_unique : ∀ matching' : TargetToSourceMatching
      (factorParamsToMatrices phi) (factorParamsToMatrices phi'),
    matching' = matching
  valueBasis : Fin L → Fin k → ChangeOfBasis dv
  attentionBasis : Fin L → Fin k → ChangeOfBasis d
  valueOut_eq : ∀ l : Fin L, ∀ a : Fin k,
    (phi l a).valueOut = gaugedTargetValueOut matching l a *
      (valueBasis l a).matrix
  valueIn_eq : ∀ l : Fin L, ∀ a : Fin k,
    (phi l a).valueIn = (valueBasis l a).invMatrix *
      gaugedTargetValueIn matching l a
  keyTranspose_eq : ∀ l : Fin L, ∀ a : Fin k,
    (phi l a).keyTranspose = gaugedTargetKeyTranspose matching l a *
      (attentionBasis l a).matrix
  query_eq : ∀ l : Fin L, ∀ a : Fin k,
    (phi l a).query = (attentionBasis l a).invMatrix *
      gaugedTargetQuery matching l a
  valueBasis_unique : ∀ l : Fin L, ∀ a : Fin k, ∀ K : ChangeOfBasis dv,
    (phi l a).valueOut = gaugedTargetValueOut matching l a * K.matrix →
    (phi l a).valueIn = K.invMatrix * gaugedTargetValueIn matching l a →
    K = valueBasis l a
  attentionBasis_unique : ∀ l : Fin L, ∀ a : Fin k, ∀ K : ChangeOfBasis d,
    (phi l a).keyTranspose =
      gaugedTargetKeyTranspose matching l a * K.matrix →
    (phi l a).query = K.invMatrix * gaugedTargetQuery matching l a →
    K = attentionBasis l a

/-- Lift the unique matrix matching through every full-rank head
factorization. -/
noncomputable def factorLevelIdentifiabilityOfMatrix
    {L k d dv : Nat} {phi phi' : FactorParams L k d dv}
    (C : GenericMatrixIdentifiabilityConclusion
      (factorParamsToMatrices phi) (factorParamsToMatrices phi'))
    (hfull : FactorFullRank phi') :
    FactorLevelIdentifiabilityConclusion phi phi' := by
  let M := C.matching
  let valueBasis : ∀ l : Fin L, Fin k → ChangeOfBasis dv := fun l a =>
    KHead.rankFactorizationBasis
      (A := gaugedTargetValueOut M l a)
      (A' := (phi l a).valueOut)
      (B := gaugedTargetValueIn M l a)
      (B' := (phi l a).valueIn)
      (valueProduct_eq_gaugedTarget M l a).symm
      (gaugedTarget_value_fullRank M hfull l a)
  let attentionBasis : ∀ l : Fin L, Fin k → ChangeOfBasis d := fun l a =>
    KHead.rankFactorizationBasis
      (A := gaugedTargetKeyTranspose M l a)
      (A' := (phi l a).keyTranspose)
      (B := gaugedTargetQuery M l a)
      (B' := (phi l a).query)
      (attentionProduct_eq_gaugedTarget M l a).symm
      (gaugedTarget_attention_fullRank M hfull l a)
  refine {
    matching := M
    matching_unique := C.unique
    valueBasis := valueBasis
    attentionBasis := attentionBasis
    valueOut_eq := ?_
    valueIn_eq := ?_
    keyTranspose_eq := ?_
    query_eq := ?_
    valueBasis_unique := ?_
    attentionBasis_unique := ?_
  }
  · intro l a
    exact KHead.rankFactorizationBasis_left_eq
      (valueProduct_eq_gaugedTarget M l a).symm
      (gaugedTarget_value_fullRank M hfull l a)
  · intro l a
    exact KHead.rankFactorizationBasis_right_eq
      (valueProduct_eq_gaugedTarget M l a).symm
      (gaugedTarget_value_fullRank M hfull l a)
  · intro l a
    exact KHead.rankFactorizationBasis_left_eq
      (attentionProduct_eq_gaugedTarget M l a).symm
      (gaugedTarget_attention_fullRank M hfull l a)
  · intro l a
    exact KHead.rankFactorizationBasis_right_eq
      (attentionProduct_eq_gaugedTarget M l a).symm
      (gaugedTarget_attention_fullRank M hfull l a)
  · intro l a K hleft hright
    let W : KHead.RankFactorizationWitness
        (gaugedTargetValueOut M l a) (phi l a).valueOut
        (gaugedTargetValueIn M l a) (phi l a).valueIn :=
      ⟨K, hleft, hright⟩
    let W0 : KHead.RankFactorizationWitness
        (gaugedTargetValueOut M l a) (phi l a).valueOut
        (gaugedTargetValueIn M l a) (phi l a).valueIn :=
      ⟨valueBasis l a,
        KHead.rankFactorizationBasis_left_eq
          (valueProduct_eq_gaugedTarget M l a).symm
          (gaugedTarget_value_fullRank M hfull l a),
        KHead.rankFactorizationBasis_right_eq
          (valueProduct_eq_gaugedTarget M l a).symm
          (gaugedTarget_value_fullRank M hfull l a)⟩
    exact KHead.RankFactorizationWitness.gauge_eq_of_productFullRank
      W W0 (gaugedTarget_value_fullRank M hfull l a)
  · intro l a K hleft hright
    let W : KHead.RankFactorizationWitness
        (gaugedTargetKeyTranspose M l a) (phi l a).keyTranspose
        (gaugedTargetQuery M l a) (phi l a).query :=
      ⟨K, hleft, hright⟩
    let W0 : KHead.RankFactorizationWitness
        (gaugedTargetKeyTranspose M l a) (phi l a).keyTranspose
        (gaugedTargetQuery M l a) (phi l a).query :=
      ⟨attentionBasis l a,
        KHead.rankFactorizationBasis_left_eq
          (attentionProduct_eq_gaugedTarget M l a).symm
          (gaugedTarget_attention_fullRank M hfull l a),
        KHead.rankFactorizationBasis_right_eq
          (attentionProduct_eq_gaugedTarget M l a).symm
          (gaugedTarget_attention_fullRank M hfull l a)⟩
    exact KHead.RankFactorizationWitness.gauge_eq_of_productFullRank
      W W0 (gaugedTarget_attention_fullRank M hfull l a)

/-- TeX `cor:factor-fiber`, forward recovery direction. -/
theorem factorLevelIdentifiability
    {n k d dv r : Nat} (hr : 2 ≤ r) (hd : dStarNS (n + 1) k ≤ d)
    (hk : 0 < k) {phi phi' : FactorParams (n + 1) k d dv}
    (htarget : factorParamsToMatrices phi' ∈
      (RecursiveGenericExceptionalSet r (n + 1) k d hd hk)ᶜ)
    (hfull : FactorFullRank phi')
    (hequal : TransformerEqualGlobally (r := r)
      (factorParamsToMatrices phi) (factorParamsToMatrices phi')) :
    Nonempty (FactorLevelIdentifiabilityConclusion phi phi') := by
  let C : GenericMatrixIdentifiabilityConclusion
      (factorParamsToMatrices phi) (factorParamsToMatrices phi') :=
    Classical.choice (genericMatrixIdentifiability hr hd hk htarget hequal)
  exact ⟨factorLevelIdentifiabilityOfMatrix C hfull⟩

namespace FactorLevelIdentifiabilityConclusion

variable {L k d dv : Nat} {phi phi' : FactorParams L k d dv}

/-- Converse direction: all displayed factor transformations preserve the
factor-level realization. -/
theorem realizes (C : FactorLevelIdentifiabilityConclusion phi phi')
    {T : Nat} (X : Matrix (Fin d) (Fin T) Real) :
    transformer (factorParamsToMatrices phi) X =
      transformer (factorParamsToMatrices phi') X := by
  rw [eq_combinedGaugePermuteAction_of_matching C.matching]
  exact permutationGaugeOrbit_realizes
    (fun l => (C.matching.headPerm l).symm) C.matching.gauge⁻¹
      (factorParamsToMatrices phi') X

end FactorLevelIdentifiabilityConclusion

end

end TransformerIdentifiability.NLayer.NoSkip
