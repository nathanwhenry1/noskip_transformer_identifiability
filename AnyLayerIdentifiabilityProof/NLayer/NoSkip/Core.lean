import AnyLayerIdentifiabilityProof.NLayer.KHead.Core

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.NoSkip

/-!
# No-skip k-head core

The parameter representation and notation are shared with the k-head skip
development.  The realization map in this file is independent: `layer` is the
sum of attention heads and has no additive copy of its input.
-/

abbrev RelativelyOpenIn {E : Type*} [TopologicalSpace E] (O H : Set E) : Prop :=
  KHead.RelativelyOpenIn O H
abbrev Context := KHead.Context
abbrev seqLength (r : Nat) : Nat := KHead.seqLength r
noncomputable abbrev logScale (r : Nat) : Real := KHead.logScale r
noncomputable abbrev alpha (r : Nat) : Real := KHead.alpha r
noncomputable abbrev sym {d : Nat} (M : Matrix (Fin d) (Fin d) Real) :
    Matrix (Fin d) (Fin d) Real :=
  KHead.sym M
abbrev layerProductFrom {d : Nat} (M : Nat → Matrix (Fin d) (Fin d) Real) (i : Nat) :
    Nat → Matrix (Fin d) (Fin d) Real :=
  KHead.layerProductFrom M i
abbrev layerProduct {d : Nat} (M : Nat → Matrix (Fin d) (Fin d) Real) (j i : Nat) :
    Matrix (Fin d) (Fin d) Real :=
  KHead.layerProduct M j i
abbrev sigmoidPoleSet := KHead.sigmoidPoleSet

namespace Context

abbrev T (ctx : Context) : Nat := KHead.Context.T ctx

@[simp] theorem T_eq (ctx : Context) : ctx.T = ctx.r + 1 := KHead.Context.T_eq ctx
theorem r_pos (ctx : Context) : 0 < ctx.r := KHead.Context.r_pos ctx
theorem L_pos (ctx : Context) : 0 < ctx.L := KHead.Context.L_pos ctx
theorem k_pos (ctx : Context) : 0 < ctx.k := KHead.Context.k_pos ctx
theorem d_pos (ctx : Context) : 0 < ctx.d := KHead.Context.d_pos ctx

end Context

theorem alpha_eq_div (r : Nat) (hr : 0 < r) :
    alpha r = (r : Real) / ((r : Real) + 1) :=
  KHead.alpha_eq_div r hr

@[simp] theorem sym_apply {d : Nat} (M : Matrix (Fin d) (Fin d) Real) (i j : Fin d) :
    sym M i j = ((2 : Real)⁻¹) * (M i j + M j i) :=
  KHead.sym_apply M i j

@[simp] theorem sym_transpose {d : Nat} (M : Matrix (Fin d) (Fin d) Real) :
    (sym M)ᵀ = sym M :=
  KHead.sym_transpose M

@[simp] theorem layerProductFrom_zero {d : Nat}
    (M : Nat → Matrix (Fin d) (Fin d) Real) (i : Nat) :
    layerProductFrom M i 0 = 1 :=
  KHead.layerProductFrom_zero M i

@[simp] theorem layerProductFrom_succ {d : Nat}
    (M : Nat → Matrix (Fin d) (Fin d) Real) (i n : Nat) :
    layerProductFrom M i (n + 1) = M (i + n) * layerProductFrom M i n :=
  KHead.layerProductFrom_succ M i n

@[simp] theorem layerProduct_empty {d : Nat}
    (M : Nat → Matrix (Fin d) (Fin d) Real) {j i : Nat} (h : j < i) :
    layerProduct M j i = 1 :=
  KHead.layerProduct_empty M h

@[simp] theorem layerProduct_diagonal {d : Nat}
    (M : Nat → Matrix (Fin d) (Fin d) Real) (i : Nat) :
    layerProduct M i i = M i :=
  KHead.layerProduct_diagonal M i

theorem mem_sigmoidPoleSet (z : Complex) :
    z ∈ sigmoidPoleSet ↔
      ∃ n : Int, z = (((2 * n + 1 : Int) : Complex) * (Real.pi : Complex) * Complex.I) :=
  KHead.mem_sigmoidPoleSet z

/-- The no-skip and skip developments deliberately share this neutral tuple type. -/
abbrev Params := KHead.Params
abbrev ParameterSpace := KHead.ParameterSpace

namespace Params

abbrev valueMatrix {L k d : Nat} (theta : Params L k d) (l : Fin L) (a : Fin k) :
    Matrix (Fin d) (Fin d) Real :=
  KHead.Params.valueMatrix theta l a
abbrev attentionMatrix {L k d : Nat} (theta : Params L k d) (l : Fin L) (a : Fin k) :
    Matrix (Fin d) (Fin d) Real :=
  KHead.Params.attentionMatrix theta l a

@[simp] theorem valueMatrix_apply {L k d : Nat} (theta : Params L k d)
    (l : Fin L) (a : Fin k) :
    valueMatrix theta l a = (theta l a).1 :=
  rfl

@[simp] theorem attentionMatrix_apply {L k d : Nat} (theta : Params L k d)
    (l : Fin L) (a : Fin k) :
    attentionMatrix theta l a = (theta l a).2 :=
  rfl

theorem head_eq_of_valueMatrix_attentionMatrix_eq {L k d : Nat}
    {theta theta' : Params L k d} (l : Fin L) (a : Fin k)
    (hvalue : valueMatrix theta l a = valueMatrix theta' l a)
    (hattention : attentionMatrix theta l a = attentionMatrix theta' l a) :
    theta l a = theta' l a :=
  Prod.ext hvalue hattention

theorem ext {L k d : Nat} {theta theta' : Params L k d}
    (hvalue : ∀ l a, valueMatrix theta l a = valueMatrix theta' l a)
    (hattention : ∀ l a, attentionMatrix theta l a = attentionMatrix theta' l a) :
    theta = theta' := by
  funext l a
  exact head_eq_of_valueMatrix_attentionMatrix_eq l a (hvalue l a) (hattention l a)

end Params

export Params (valueMatrix attentionMatrix)

noncomputable abbrev softmaxColC {T : Nat} (M : Matrix (Fin T) (Fin T) Real) :
    Matrix (Fin T) (Fin T) Real :=
  KHead.softmaxColC M

@[simp] theorem softmaxColC_apply {T : Nat} (M : Matrix (Fin T) (Fin T) Real)
    (i j : Fin T) :
    softmaxColC M i j =
      if i ≤ j then Real.exp (M i j) / ∑ i' ∈ Finset.Iic j, Real.exp (M i' j) else 0 :=
  rfl

/-- `C_l`, the sum of the value matrices in layer `l`. -/
noncomputable def valueSum {L k d : Nat} (theta : Params L k d) (l : Fin L) :
    Matrix (Fin d) (Fin d) Real :=
  ∑ a : Fin k, valueMatrix theta l a

/-- In the no-skip model the collapsed matrix is exactly `C_l = sum_a V_la`. -/
noncomputable def collapseMatrix {L k d : Nat} (theta : Params L k d) (l : Fin L) :
    Matrix (Fin d) (Fin d) Real :=
  valueSum theta l

@[simp] theorem collapseMatrix_eq_valueSum {L k d : Nat}
    (theta : Params L k d) (l : Fin L) :
    collapseMatrix theta l = valueSum theta l :=
  rfl

/-- The no-skip annihilation identity `C_l - sum_a V_la = 0`. -/
@[simp] theorem collapseMatrix_sub_valueSum {L k d : Nat}
    (theta : Params L k d) (l : Fin L) :
    collapseMatrix theta l - valueSum theta l = 0 := by
  simp [collapseMatrix]

/-- One k-head causal attention layer without a skip connection. -/
noncomputable def layer {L k d T : Nat} (theta : Params L k d) (l : Fin L)
    (X : Matrix (Fin d) (Fin T) Real) : Matrix (Fin d) (Fin T) Real :=
  ∑ a : Fin k,
    valueMatrix theta l a * X * softmaxColC (Xᵀ * attentionMatrix theta l a * X)

@[simp] theorem layer_zero {L k d T : Nat} (theta : Params L k d) (l : Fin L) :
    layer theta l (0 : Matrix (Fin d) (Fin T) Real) = 0 := by
  simp [layer]

@[simp] theorem layer_zero_heads {L d T : Nat} (theta : Params L 0 d) (l : Fin L)
    (X : Matrix (Fin d) (Fin T) Real) :
    layer theta l X = 0 := by
  simp [layer]

/-- Extensionality of a layer through its finite head sum. -/
theorem layer_eq_of_head_eq {L k d T : Nat} {theta theta' : Params L k d} (l : Fin L)
    (X : Matrix (Fin d) (Fin T) Real)
    (hvalue : ∀ a, valueMatrix theta l a = valueMatrix theta' l a)
    (hattention : ∀ a, attentionMatrix theta l a = attentionMatrix theta' l a) :
    layer theta l X = layer theta' l X := by
  apply Finset.sum_congr rfl
  intro a _ha
  rw [hvalue a, hattention a]

/-- Layerwise head relabeling, in target-to-source evaluation orientation. -/
def permuteHeads {L k d : Nat} (sigma : Fin L → Equiv.Perm (Fin k))
    (theta : Params L k d) : Params L k d :=
  fun l a => theta l (sigma l a)

@[simp] theorem valueMatrix_permuteHeads {L k d : Nat}
    (sigma : Fin L → Equiv.Perm (Fin k)) (theta : Params L k d) (l : Fin L) (a : Fin k) :
    valueMatrix (permuteHeads sigma theta) l a = valueMatrix theta l (sigma l a) :=
  rfl

@[simp] theorem attentionMatrix_permuteHeads {L k d : Nat}
    (sigma : Fin L → Equiv.Perm (Fin k)) (theta : Params L k d) (l : Fin L) (a : Fin k) :
    attentionMatrix (permuteHeads sigma theta) l a = attentionMatrix theta l (sigma l a) :=
  rfl

/-- Relabeling the heads of a layer does not change its finite sum. -/
theorem layer_permuteHeads {L k d T : Nat} (sigma : Fin L → Equiv.Perm (Fin k))
    (theta : Params L k d) (l : Fin L) (X : Matrix (Fin d) (Fin T) Real) :
    layer (permuteHeads sigma theta) l X = layer theta l X := by
  simp only [layer, valueMatrix_permuteHeads, attentionMatrix_permuteHeads]
  exact Equiv.sum_comp (sigma l) fun a =>
    valueMatrix theta l a * X * softmaxColC (Xᵀ * attentionMatrix theta l a * X)

/-- The depth-`L` no-skip transformer. -/
noncomputable def transformer {k d T : Nat} :
    {L : Nat} → Params L k d → Matrix (Fin d) (Fin T) Real → Matrix (Fin d) (Fin T) Real
  | 0, _, X => X
  | _ + 1, theta, X => transformer (Fin.tail theta) (layer theta 0 X)

@[simp] theorem transformer_zero {k d T : Nat} (theta : Params 0 k d)
    (X : Matrix (Fin d) (Fin T) Real) :
    transformer theta X = X :=
  rfl

@[simp] theorem transformer_succ {L k d T : Nat} (theta : Params (L + 1) k d)
    (X : Matrix (Fin d) (Fin T) Real) :
    transformer theta X = transformer (Fin.tail theta) (layer theta 0 X) :=
  rfl

@[simp] theorem layer_tail {L k d T : Nat} (theta : Params (L + 1) k d)
    (l : Fin L) (X : Matrix (Fin d) (Fin T) Real) :
    layer (Fin.tail theta) l X = layer theta l.succ X :=
  rfl

/-- Extensionality of the layer composition defining a transformer. -/
theorem transformer_eq_of_layer_eq {L k d T : Nat} {theta theta' : Params L k d}
    (hlayer : ∀ l (X : Matrix (Fin d) (Fin T) Real), layer theta l X = layer theta' l X)
    (X : Matrix (Fin d) (Fin T) Real) :
    transformer theta X = transformer theta' X := by
  induction L generalizing X with
  | zero => rfl
  | succ L ih =>
      rw [transformer_succ, transformer_succ, hlayer 0 X]
      exact ih (theta := Fin.tail theta) (theta' := Fin.tail theta')
        (fun l Y => by simpa using hlayer l.succ Y) (layer theta' 0 X)

/-- Per-layer head permutations leave the full no-skip transformer unchanged. -/
theorem transformer_permuteHeads {L k d T : Nat}
    (sigma : Fin L → Equiv.Perm (Fin k)) (theta : Params L k d)
    (X : Matrix (Fin d) (Fin T) Real) :
    transformer (permuteHeads sigma theta) X = transformer theta X := by
  apply transformer_eq_of_layer_eq
  intro l Y
  exact layer_permuteHeads sigma theta l Y

end TransformerIdentifiability.NLayer.NoSkip
