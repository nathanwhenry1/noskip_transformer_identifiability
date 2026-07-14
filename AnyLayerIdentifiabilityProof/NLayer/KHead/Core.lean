import AnyLayerIdentifiabilityProof.NLayer.Foundations.Core

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.KHead

/-!
# K-head core notation and model definitions

This file ports the notation packet for the k-head extension. It mirrors
`tex_modular/sections/01-notation.tex`: the standing integer context, sigmoid
normalization constants, matrix symmetrization, layer-product convention,
k-head parameter space, causal column softmax, k-head layers, the depth-`L`
network, and the skip/collapse identity.
-/

/-- Relative openness for a subset of an ambient set, represented by an ambient open set. -/
def RelativelyOpenIn {E : Type*} [TopologicalSpace E] (O H : Set E) : Prop :=
  ∃ U : Set E, IsOpen U ∧ O = U ∩ H

/-- Standing natural-number hypotheses from the notation section. -/
structure Context where
  L : Nat
  k : Nat
  r : Nat
  d : Nat
  hL : 1 ≤ L
  hk : 1 ≤ k
  hr : 2 ≤ r
  hd : 2 ≤ d

/-- The sequence length `T = r + 1`. -/
abbrev seqLength (r : Nat) : Nat := r + 1

namespace Context

/-- The notation-section sequence length attached to a context. -/
abbrev T (ctx : Context) : Nat := seqLength ctx.r

@[simp] theorem T_eq (ctx : Context) : ctx.T = ctx.r + 1 := rfl

theorem r_pos (ctx : Context) : 0 < ctx.r := by
  exact lt_of_lt_of_le (by norm_num : (0 : Nat) < 2) ctx.hr

theorem L_pos (ctx : Context) : 0 < ctx.L := by
  exact ctx.hL

theorem k_pos (ctx : Context) : 0 < ctx.k := by
  exact ctx.hk

theorem d_pos (ctx : Context) : 0 < ctx.d := by
  exact lt_of_lt_of_le (by norm_num : (0 : Nat) < 2) ctx.hd

end Context

/-- The TeX constant `b = log r`. -/
noncomputable abbrev logScale (r : Nat) : Real := Real.log (r : Real)

/-- The TeX constant `alpha = sig (log r)`. -/
noncomputable abbrev alpha (r : Nat) : Real := sig (logScale r)

/-- For positive natural `r`, `sig (log r) = r / (r + 1)`. -/
theorem alpha_eq_div (r : Nat) (hr : 0 < r) :
    alpha r = (r : Real) / ((r : Real) + 1) := by
  rw [alpha, logScale, sig]
  rw [Real.exp_neg, Real.exp_log (by exact_mod_cast hr)]
  field_simp [show (r : Real) ≠ 0 by exact_mod_cast Nat.ne_of_gt hr]

/-- Matrix symmetrization, `Sym(M) = (1 / 2) • (M + Mᵀ)`. -/
noncomputable def sym {d : Nat} (M : Matrix (Fin d) (Fin d) Real) :
    Matrix (Fin d) (Fin d) Real :=
  ((2 : Real)⁻¹) • (M + Mᵀ)

@[simp] theorem sym_apply {d : Nat} (M : Matrix (Fin d) (Fin d) Real) (i j : Fin d) :
    sym M i j = ((2 : Real)⁻¹) * (M i j + M j i) := by
  simp [sym, mul_add]

@[simp] theorem sym_transpose {d : Nat} (M : Matrix (Fin d) (Fin d) Real) :
    (sym M)ᵀ = sym M := by
  ext i j
  simp [sym, add_comm, mul_add]

/-- Product helper for the convention `M_{j:i} = M_j M_{j-1} ... M_i`. -/
def layerProductFrom {d : Nat} (M : Nat → Matrix (Fin d) (Fin d) Real) (i : Nat) :
    Nat → Matrix (Fin d) (Fin d) Real
  | 0 => 1
  | n + 1 => M (i + n) * layerProductFrom M i n

/-- Layer-product convention: `M_{j:i}`, with value `1` when `j < i`. -/
def layerProduct {d : Nat} (M : Nat → Matrix (Fin d) (Fin d) Real) (j i : Nat) :
    Matrix (Fin d) (Fin d) Real :=
  if j < i then 1 else layerProductFrom M i (j - i + 1)

@[simp] theorem layerProductFrom_zero {d : Nat}
    (M : Nat → Matrix (Fin d) (Fin d) Real) (i : Nat) :
    layerProductFrom M i 0 = 1 :=
  rfl

@[simp] theorem layerProductFrom_succ {d : Nat}
    (M : Nat → Matrix (Fin d) (Fin d) Real) (i n : Nat) :
    layerProductFrom M i (n + 1) = M (i + n) * layerProductFrom M i n :=
  rfl

@[simp] theorem layerProduct_empty {d : Nat}
    (M : Nat → Matrix (Fin d) (Fin d) Real) {j i : Nat} (h : j < i) :
    layerProduct M j i = 1 := by
  simp [layerProduct, h]

@[simp] theorem layerProduct_diagonal {d : Nat}
    (M : Nat → Matrix (Fin d) (Fin d) Real) (i : Nat) :
    layerProduct M i i = M i := by
  simp [layerProduct, layerProductFrom]

/-- The complex pole set `(2 Z + 1) pi i` for the logistic sigmoid. -/
def sigmoidPoleSet : Set Complex :=
  {z | ∃ n : Int, z = (((2 * n + 1 : Int) : Complex) * (Real.pi : Complex) * Complex.I)}

theorem mem_sigmoidPoleSet (z : Complex) :
    z ∈ sigmoidPoleSet ↔
      ∃ n : Int, z = (((2 * n + 1 : Int) : Complex) * (Real.pi : Complex) * Complex.I) :=
  Iff.rfl

/-- A depth-`L`, `k`-head parameter family. -/
abbrev Params (L k d : Nat) : Type :=
  Fin L → Fin k → Matrix (Fin d) (Fin d) Real × Matrix (Fin d) (Fin d) Real

/-- The TeX parameter space `P_{L,k}`. -/
abbrev ParameterSpace (L k d : Nat) : Type := Params L k d

namespace Params

/-- The value matrix `V_{la}`. -/
abbrev valueMatrix {L k d : Nat} (θ : Params L k d) (l : Fin L) (a : Fin k) :
    Matrix (Fin d) (Fin d) Real :=
  (θ l a).1

/-- The attention matrix `A_{la}`. -/
abbrev attentionMatrix {L k d : Nat} (θ : Params L k d) (l : Fin L) (a : Fin k) :
    Matrix (Fin d) (Fin d) Real :=
  (θ l a).2

@[simp] theorem valueMatrix_apply {L k d : Nat} (θ : Params L k d)
    (l : Fin L) (a : Fin k) :
    valueMatrix θ l a = (θ l a).1 :=
  rfl

@[simp] theorem attentionMatrix_apply {L k d : Nat} (θ : Params L k d)
    (l : Fin L) (a : Fin k) :
    attentionMatrix θ l a = (θ l a).2 :=
  rfl

/-- Componentwise equality of one head in one layer. -/
theorem head_eq_of_valueMatrix_attentionMatrix_eq {L k d : Nat}
    {θ θ' : Params L k d} (l : Fin L) (a : Fin k)
    (hvalue : valueMatrix θ l a = valueMatrix θ' l a)
    (hattention : attentionMatrix θ l a = attentionMatrix θ' l a) :
    θ l a = θ' l a :=
  Prod.ext hvalue hattention

/-- Parameter extensionality by all value and attention matrices. -/
theorem ext {L k d : Nat} {θ θ' : Params L k d}
    (hvalue : ∀ l a, valueMatrix θ l a = valueMatrix θ' l a)
    (hattention : ∀ l a, attentionMatrix θ l a = attentionMatrix θ' l a) :
    θ = θ' := by
  funext l a
  exact head_eq_of_valueMatrix_attentionMatrix_eq l a (hvalue l a) (hattention l a)

end Params

export Params (valueMatrix attentionMatrix)

/-- Column-wise causal softmax from the notation packet. -/
noncomputable abbrev softmaxColC {T : Nat} (M : Matrix (Fin T) (Fin T) Real) :
    Matrix (Fin T) (Fin T) Real :=
  causalSoftmax M

@[simp] theorem softmaxColC_apply {T : Nat} (M : Matrix (Fin T) (Fin T) Real)
    (i j : Fin T) :
    softmaxColC M i j =
      if i ≤ j then Real.exp (M i j) / ∑ i' ∈ Finset.Iic j, Real.exp (M i' j) else 0 :=
  rfl

/-- Sum of value matrices in a fixed layer. -/
noncomputable def valueSum {L k d : Nat} (θ : Params L k d) (l : Fin L) :
    Matrix (Fin d) (Fin d) Real :=
  ∑ a : Fin k, valueMatrix θ l a

/-- The collapsed linear part `C_l = I + sum_a V_{la}`. -/
noncomputable def collapseMatrix {L k d : Nat} (θ : Params L k d) (l : Fin L) :
    Matrix (Fin d) (Fin d) Real :=
  1 + valueSum θ l

/-- The skip-connection cancellation identity `C_l - sum_a V_{la} = I`. -/
@[simp] theorem collapseMatrix_sub_valueSum {L k d : Nat}
    (θ : Params L k d) (l : Fin L) :
    collapseMatrix θ l - valueSum θ l = 1 := by
  simp [collapseMatrix]

/-- One `k`-head causal attention layer with additive skip connection. -/
noncomputable def layer {L k d T : Nat} (θ : Params L k d) (l : Fin L)
    (X : Matrix (Fin d) (Fin T) Real) : Matrix (Fin d) (Fin T) Real :=
  X + ∑ a : Fin k,
    valueMatrix θ l a * X * softmaxColC (Xᵀ * attentionMatrix θ l a * X)

@[simp] theorem layer_zero_heads {L d T : Nat} (θ : Params L 0 d) (l : Fin L)
    (X : Matrix (Fin d) (Fin T) Real) :
    layer θ l X = X := by
  simp [layer]

/-- The depth-`L`, `k`-head network `Layer_L o ... o Layer_1`. -/
noncomputable def transformer {k d T : Nat} :
    {L : Nat} → Params L k d → Matrix (Fin d) (Fin T) Real → Matrix (Fin d) (Fin T) Real
  | 0, _, X => X
  | _ + 1, θ, X => transformer (Fin.tail θ) (layer θ 0 X)

@[simp] theorem transformer_zero {k d T : Nat} (θ : Params 0 k d)
    (X : Matrix (Fin d) (Fin T) Real) :
    transformer θ X = X :=
  rfl

@[simp] theorem transformer_succ {L k d T : Nat} (θ : Params (L + 1) k d)
    (X : Matrix (Fin d) (Fin T) Real) :
    transformer θ X = transformer (Fin.tail θ) (layer θ 0 X) :=
  rfl

/-- Embed the single-head parameter space as the `k = 1` case. -/
abbrev ofSingleHeadParams {L d : Nat} (θ : TransformerIdentifiability.NLayer.Params L d) :
    Params L 1 d :=
  fun l _ => θ l

theorem valueMatrix_ofSingleHeadParams {L d : Nat}
    (θ : TransformerIdentifiability.NLayer.Params L d) (l : Fin L) (a : Fin 1) :
    valueMatrix (ofSingleHeadParams θ) l a =
      TransformerIdentifiability.NLayer.Params.valueMatrix θ l :=
  rfl

theorem attentionMatrix_ofSingleHeadParams {L d : Nat}
    (θ : TransformerIdentifiability.NLayer.Params L d) (l : Fin L) (a : Fin 1) :
    attentionMatrix (ofSingleHeadParams θ) l a =
      TransformerIdentifiability.NLayer.Params.attentionMatrix θ l :=
  rfl

@[simp] theorem layer_ofSingleHeadParams {L d T : Nat}
    (θ : TransformerIdentifiability.NLayer.Params L d) (l : Fin L)
    (X : Matrix (Fin d) (Fin T) Real) :
    layer (ofSingleHeadParams θ) l X =
      TransformerIdentifiability.NLayer.attnLayer
        (TransformerIdentifiability.NLayer.Params.valueMatrix θ l)
        (TransformerIdentifiability.NLayer.Params.attentionMatrix θ l) X := by
  simp [layer, TransformerIdentifiability.NLayer.attnLayer, ofSingleHeadParams]

end TransformerIdentifiability.NLayer.KHead
