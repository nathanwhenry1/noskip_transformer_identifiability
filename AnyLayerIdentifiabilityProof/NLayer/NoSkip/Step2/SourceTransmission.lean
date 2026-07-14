import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Genericity.Regularity

set_option autoImplicit false

open Matrix
open scoped Matrix.Norms.Frobenius

namespace TransformerIdentifiability.NLayer.NoSkip

noncomputable section

/-!
# Equality-derived source transmission

This is the derivative-at-zero repair from `lem:source-transmission` in the
no-skip TeX proof.  It is deliberately proved before any source regularity is
available: equality with a transmitting target first identifies the complete
collapsed product, and invertibility of that product then forces every source
head sum to be invertible.
-/

/-- The ordered product `C_{L:1}` of the no-skip head sums. -/
noncomputable def transmissionProduct {k d : Nat} :
    {L : Nat} -> Params L k d -> Matrix (Fin d) (Fin d) Real
  | 0, _ => 1
  | _ + 1, theta =>
      transmissionProduct (Fin.tail theta) * collapseMatrix theta 0

@[simp] theorem transmissionProduct_zero {k d : Nat} (theta : Params 0 k d) :
    transmissionProduct theta = 1 :=
  rfl

@[simp] theorem transmissionProduct_succ {L k d : Nat}
    (theta : Params (L + 1) k d) :
    transmissionProduct theta =
      transmissionProduct (Fin.tail theta) * collapseMatrix theta 0 :=
  rfl

/-- The derivative of a complete no-skip transformer at zero, expressed as a
composition of the layer derivatives. -/
noncomputable def transformerDerivative (r : Nat) {k d : Nat} :
    {L : Nat} -> Params L k d ->
      Matrix (Fin d) (Fin (seqLength r)) Real →L[Real]
        Matrix (Fin d) (Fin (seqLength r)) Real
  | 0, _ => ContinuousLinearMap.id Real _
  | _ + 1, theta =>
      (transformerDerivative r (Fin.tail theta)).comp
        (localDerivativeContinuousLinearMap r theta 0)

@[simp] theorem transformer_zero_input {L k d T : Nat} (theta : Params L k d) :
    transformer theta (0 : Matrix (Fin d) (Fin T) Real) = 0 := by
  induction L with
  | zero => rfl
  | succ L ih =>
      rw [transformer_succ, layer_zero]
      exact ih (Fin.tail theta)

/-- Chain rule for the derivative of the full no-skip transformer at zero. -/
theorem transformer_hasFDerivAt_zero {r L k d : Nat} (theta : Params L k d) :
    HasFDerivAt
      (fun X : Matrix (Fin d) (Fin (seqLength r)) Real => transformer theta X)
      (transformerDerivative r theta) 0 := by
  induction L with
  | zero =>
      simpa [transformer, transformerDerivative] using
        (hasFDerivAt_id (𝕜 := Real)
          (0 : Matrix (Fin d) (Fin (seqLength r)) Real))
  | succ L ih =>
      have htail := ih (Fin.tail theta)
      have hlayer := layer_hasFDerivAt_localDerivative (r := r) theta 0
      have htail' : HasFDerivAt
          (fun X : Matrix (Fin d) (Fin (seqLength r)) Real =>
            transformer (Fin.tail theta) X)
          (transformerDerivative r (Fin.tail theta)) (layer theta 0 0) := by
        simpa using htail
      have hcomp := htail'.comp
        (0 : Matrix (Fin d) (Fin (seqLength r)) Real) hlayer
      simpa [Function.comp_def, transformerDerivative, transformer_zero_input] using hcomp

/-- Closed form for the derivative: `H |-> C_{L:1} H Gamma_0^L`. -/
theorem transformerDerivative_apply {r L k d : Nat} (theta : Params L k d)
    (H : Matrix (Fin d) (Fin (seqLength r)) Real) :
    transformerDerivative r theta H =
      transmissionProduct theta * H * (gammaZero r) ^ L := by
  induction L generalizing H with
  | zero => simp [transformerDerivative, transmissionProduct]
  | succ L ih =>
      rw [transformerDerivative, ContinuousLinearMap.comp_apply,
        localDerivativeContinuousLinearMap_apply, localDerivative,
        ih (Fin.tail theta), transmissionProduct_succ]
      rw [pow_succ']
      simp only [Matrix.mul_assoc]

/-- Equality of realization maps identifies their derivatives at zero. -/
theorem transformerDerivative_eq_of_transformer_eq {r L k d : Nat}
    {theta theta' : Params L k d}
    (heq : forall X : Matrix (Fin d) (Fin (seqLength r)) Real,
      transformer theta X = transformer theta' X) :
    transformerDerivative r theta = transformerDerivative r theta' := by
  have hs := transformer_hasFDerivAt_zero (r := r) theta
  have ht := transformer_hasFDerivAt_zero (r := r) theta'
  apply HasFDerivAt.unique hs
  exact ht.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun X => heq X)

/-- The common right factor `Gamma_0^L` in the derivative is invertible. -/
theorem gammaZero_pow_det_ne_zero (r L : Nat) :
    ((gammaZero r) ^ L).det ≠ 0 := by
  rw [Matrix.det_pow]
  exact pow_ne_zero _ (gammaZero_det_ne_zero r)

/-- A matrix is determined by left multiplication on all `d x (r+1)` inputs. -/
theorem matrix_eq_of_mul_eq_mul_all_inputs {r d : Nat}
    {A B : Matrix (Fin d) (Fin d) Real}
    (h : forall H : Matrix (Fin d) (Fin (seqLength r)) Real, A * H = B * H) :
    A = B := by
  ext i j
  let q : Fin (seqLength r) := 0
  let H : Matrix (Fin d) (Fin (seqLength r)) Real :=
    fun x y => if x = j && y = q then 1 else 0
  have hij := congrArg (fun M => M i q) (h H)
  simpa [Matrix.mul_apply, H, q] using hij

/-- The complete collapsed products agree whenever the realization maps do. -/
theorem transmissionProduct_eq_of_transformer_eq {r L k d : Nat}
    {theta theta' : Params L k d}
    (heq : forall X : Matrix (Fin d) (Fin (seqLength r)) Real,
      transformer theta X = transformer theta' X) :
    transmissionProduct theta = transmissionProduct theta' := by
  have hderiv := transformerDerivative_eq_of_transformer_eq (r := r) heq
  apply matrix_eq_of_mul_eq_mul_all_inputs (r := r)
  intro H
  have h : transformerDerivative r theta H = transformerDerivative r theta' H :=
    congrArg (fun f => f H) hderiv
  rw [transformerDerivative_apply, transformerDerivative_apply] at h
  have hGamma : IsUnit (((gammaZero r) ^ L).det) :=
    (gammaZero_pow_det_ne_zero r L).isUnit
  calc
    transmissionProduct theta * H =
        (transmissionProduct theta * H * (gammaZero r) ^ L) *
          ((gammaZero r) ^ L)⁻¹ := by
            rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hGamma]
            simp
    _ = (transmissionProduct theta' * H * (gammaZero r) ^ L) *
          ((gammaZero r) ^ L)⁻¹ := by rw [h]
    _ = transmissionProduct theta' * H := by
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hGamma]
          simp

/-- Target transmission makes its complete collapsed product invertible. -/
theorem transmissionProduct_det_ne_zero_of_regularity {L k d : Nat}
    {theta : Params L k d} (hreg : Regularity theta) :
    (transmissionProduct theta).det ≠ 0 := by
  induction L with
  | zero => simp
  | succ L ih =>
      rw [transmissionProduct_succ, Matrix.det_mul]
      exact mul_ne_zero (ih (hreg := {
        attention_det_ne_zero := fun l a => hreg.attention_det_ne_zero l.succ a
        attention_sym_ne_zero := fun l a => hreg.attention_sym_ne_zero l.succ a
        value_ne_zero := fun l a => hreg.value_ne_zero l.succ a
        attention_pairwise := fun l => hreg.attention_pairwise l.succ
        transmission := fun l => hreg.transmission l.succ
        joint_surjective := fun l => hreg.joint_surjective l.succ }))
        (hreg.transmission 0)

/-- If `C_{L:1}` is invertible, every factor `C_l` is invertible. -/
theorem transmission_of_transmissionProduct_det_ne_zero {L k d : Nat}
    {theta : Params L k d} (hprod : (transmissionProduct theta).det ≠ 0) :
    forall l : Fin L, (collapseMatrix theta l).det ≠ 0 := by
  induction L with
  | zero => intro l; exact Fin.elim0 l
  | succ L ih =>
      rw [transmissionProduct_succ, Matrix.det_mul] at hprod
      have htail : (transmissionProduct (Fin.tail theta)).det ≠ 0 :=
        left_ne_zero_of_mul hprod
      have hfirst : (collapseMatrix theta 0).det ≠ 0 :=
        right_ne_zero_of_mul hprod
      intro l
      refine Fin.cases hfirst ?_ l
      intro j
      simpa using ih htail j

/-- **TeX `lem:source-transmission`.**  Equality with a regular target forces
the arbitrary source to transmit at every layer, before source genericity or
value matching has been assumed. -/
theorem source_transmission_of_transformer_eq {r L k d : Nat}
    {theta theta' : Params L k d} (hreg' : Regularity theta')
    (heq : forall X : Matrix (Fin d) (Fin (seqLength r)) Real,
      transformer theta X = transformer theta' X) :
    transmissionProduct theta = transmissionProduct theta' /\
      (forall l : Fin L, (collapseMatrix theta l).det ≠ 0) := by
  have hproduct := transmissionProduct_eq_of_transformer_eq (r := r) heq
  refine ⟨hproduct, ?_⟩
  apply transmission_of_transmissionProduct_det_ne_zero
  rw [hproduct]
  exact transmissionProduct_det_ne_zero_of_regularity hreg'

end

end TransformerIdentifiability.NLayer.NoSkip
