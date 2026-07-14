import Mathlib

set_option autoImplicit false

open MeasureTheory Matrix

namespace TransformerIdentifiability.NLayer

/-!
# Core model definitions

This file is the foundation for the split `n_layer_proof.tex` formalization.
It contains the causal softmax, one attention layer, the depth-`L` parameter
space, and the recursively defined transformer.

Corresponds to:
* `n_layer_proof.tex`, Section 2.1
* `n_layer_proof.tex`, Section 2.1-2.2
* the trusted base in `identifiability.lean`
-/

/-- The real logistic sigmoid. -/
noncomputable def sig (x : Real) : Real := (1 + Real.exp (-x))⁻¹

/-- Column-wise causal softmax: entry `(i, j)` is
`exp (M i j) / sum_{i' <= j} exp (M i' j)` for `i <= j`, and `0` otherwise. -/
noncomputable def causalSoftmax {T : Nat} (M : Matrix (Fin T) (Fin T) Real) :
    Matrix (Fin T) (Fin T) Real :=
  Matrix.of fun i j =>
    if i <= j then Real.exp (M i j) / ∑ i' ∈ Finset.Iic j, Real.exp (M i' j) else 0

/-- One single-head causal attention layer with additive skip connection:
`X ↦ X + V * X * causalSoftmax (Xᵀ * A * X)`. -/
noncomputable def attnLayer {d T : Nat} (V A : Matrix (Fin d) (Fin d) Real)
    (X : Matrix (Fin d) (Fin T) Real) : Matrix (Fin d) (Fin T) Real :=
  X + V * X * causalSoftmax (Xᵀ * A * X)

/-- Depth-`L` parameter space: layer `l` carries `(V l, A l)`. -/
abbrev Params (L d : Nat) : Type :=
  Fin L -> Matrix (Fin d) (Fin d) Real × Matrix (Fin d) (Fin d) Real

namespace Params

/-! ## Layer projections and extensionality -/

/-- The value matrix at a chosen layer. -/
abbrev valueMatrix {L d : Nat} (θ : Params L d) (l : Fin L) :
    Matrix (Fin d) (Fin d) Real :=
  (θ l).1

/-- The attention matrix at a chosen layer. -/
abbrev attentionMatrix {L d : Nat} (θ : Params L d) (l : Fin L) :
    Matrix (Fin d) (Fin d) Real :=
  (θ l).2

@[simp] theorem valueMatrix_apply {L d : Nat} (θ : Params L d) (l : Fin L) :
    valueMatrix θ l = (θ l).1 :=
  rfl

@[simp] theorem attentionMatrix_apply {L d : Nat} (θ : Params L d) (l : Fin L) :
    attentionMatrix θ l = (θ l).2 :=
  rfl

/-- Componentwise equality of one layer, phrased in the named projections. -/
theorem layer_eq_of_valueMatrix_attentionMatrix_eq {L d : Nat}
    {θ θ' : Params L d} (l : Fin L)
    (hvalue : valueMatrix θ l = valueMatrix θ' l)
    (hattention : attentionMatrix θ l = attentionMatrix θ' l) :
    θ l = θ' l :=
  Prod.ext hvalue hattention

/-- Parameter extensionality by value and attention matrices at every layer. -/
theorem ext {L d : Nat} {θ θ' : Params L d}
    (hvalue : ∀ l, valueMatrix θ l = valueMatrix θ' l)
    (hattention : ∀ l, attentionMatrix θ l = attentionMatrix θ' l) :
    θ = θ' := by
  funext l
  exact layer_eq_of_valueMatrix_attentionMatrix_eq l (hvalue l) (hattention l)

end Params

/-- The depth-`L` network, applying the first layer and then recursing on the tail. -/
noncomputable def transformer {d T : Nat} :
    {L : Nat} -> Params L d -> Matrix (Fin d) (Fin T) Real -> Matrix (Fin d) (Fin T) Real
  | 0, _, X => X
  | _ + 1, θ, X => transformer (Fin.tail θ) (attnLayer (θ 0).1 (θ 0).2 X)

@[simp] theorem transformer_zero {d T : Nat} (θ : Params 0 d)
    (X : Matrix (Fin d) (Fin T) Real) :
    transformer θ X = X :=
  rfl

/-- Give matrices the product Lebesgue measure-space structure. -/
noncomputable instance {n m : Nat} : MeasureSpace (Matrix (Fin n) (Fin m) Real) :=
  inferInstanceAs (MeasureSpace (Fin n -> Fin m -> Real))

end TransformerIdentifiability.NLayer
