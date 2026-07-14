import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Step2.TrichotomyInstance
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.SharedToolbox
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Genericity.Regularity

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.NoSkip

/-!
# Saturated no-skip tail matrices

The external tail indices are the TeX one-based indices `2,...,L`.  Parameter
tuples remain Lean's zero-based `Fin L`, so `saturatedValueFamily` is the sole
index conversion point.
-/

noncomputable section

/-- A parameter value head exposed at a one-based TeX layer.  Values outside
`1,...,L` are set to zero; all saturated products only query `2,...,L`. -/
noncomputable def saturatedValueFamily {L k d : Nat} (theta : Params L k d) :
    Nat → Fin k → Matrix (Fin d) (Fin d) Real :=
  fun j a => if hj : 1 ≤ j ∧ j ≤ L then
    valueMatrix theta ⟨j - 1, by omega⟩ a else 0

theorem saturatedValueFamily_of_mem {L k d : Nat} (theta : Params L k d)
    {j : Nat} (hj1 : 1 ≤ j) (hjL : j ≤ L) (a : Fin k) :
    saturatedValueFamily theta j a =
      valueMatrix theta ⟨j - 1, by omega⟩ a := by
  rw [saturatedValueFamily, dif_pos ⟨hj1, hjL⟩]

/-- Numerical deeper gate tuple produced by the trichotomy. -/
noncomputable def saturatedNumericLabels {L k : Nat} (r : Nat)
    (labels : DeeperHead → TrichotomyLabel) : NoSkipSaturatedLabels k :=
  fun j a => if 2 ≤ j ∧ j ≤ L then
    trichotomyLabelValue r (labels { layer := j, head := a.1 + 1 }) else 0

theorem saturatedNumericLabels_of_mem {L k : Nat} (r : Nat)
    (labels : DeeperHead → TrichotomyLabel) {j : Nat}
    (hj2 : 2 ≤ j) (hjL : j ≤ L) (a : Fin k) :
    saturatedNumericLabels (L := L) r labels j a =
      trichotomyLabelValue r (labels { layer := j, head := a.1 + 1 }) := by
  rw [saturatedNumericLabels, if_pos ⟨hj2, hjL⟩]

/-- The all-zero deeper labels forced on the primed side by the simultaneous
dial. -/
def saturatedAllZeroLabels (k : Nat) : NoSkipSaturatedLabels k :=
  fun _ _ => 0

/-- Canonical saturated tail package for one network and one global deeper
label tuple. -/
structure SaturatedData {L k d : Nat} (theta : Params L k d)
    (r : Nat) (labels : DeeperHead → TrichotomyLabel) where
  C : Nat → Matrix (Fin d) (Fin d) Real
  D : Nat → Matrix (Fin d) (Fin d) Real
  KLayer : Nat → Matrix (Fin d) (Fin d) Real
  M : Matrix (Fin d) (Fin d) Real
  E : Matrix (Fin d) (Fin d) Real
  K : Matrix (Fin d) (Fin d) Real
  C_eq : C = noSkipSaturatedC (saturatedValueFamily theta)
  D_eq : D = noSkipSaturatedD (saturatedValueFamily theta)
      (saturatedNumericLabels (L := L) r labels)
  KLayer_eq : KLayer = noSkipSaturatedKLayer (saturatedValueFamily theta)
      (saturatedNumericLabels (L := L) r labels)
  M_eq : M = noSkipSaturatedM C L
  E_eq : E = noSkipSaturatedE C D KLayer L
  K_eq : K = noSkipSaturatedK M E

/-- The definitional saturated package used downstream. -/
noncomputable def saturatedData {L k d : Nat} (theta : Params L k d)
    (r : Nat) (labels : DeeperHead → TrichotomyLabel) :
    SaturatedData theta r labels where
  C := noSkipSaturatedC (saturatedValueFamily theta)
  D := noSkipSaturatedD (saturatedValueFamily theta)
    (saturatedNumericLabels (L := L) r labels)
  KLayer := noSkipSaturatedKLayer (saturatedValueFamily theta)
    (saturatedNumericLabels (L := L) r labels)
  M := noSkipSaturatedM (noSkipSaturatedC (saturatedValueFamily theta)) L
  E := noSkipSaturatedE
    (noSkipSaturatedC (saturatedValueFamily theta))
    (noSkipSaturatedD (saturatedValueFamily theta)
      (saturatedNumericLabels (L := L) r labels))
    (noSkipSaturatedKLayer (saturatedValueFamily theta)
      (saturatedNumericLabels (L := L) r labels)) L
  K := noSkipSaturatedK
    (noSkipSaturatedM (noSkipSaturatedC (saturatedValueFamily theta)) L)
    (noSkipSaturatedE
      (noSkipSaturatedC (saturatedValueFamily theta))
      (noSkipSaturatedD (saturatedValueFamily theta)
        (saturatedNumericLabels (L := L) r labels))
      (noSkipSaturatedKLayer (saturatedValueFamily theta)
        (saturatedNumericLabels (L := L) r labels)) L)
  C_eq := rfl
  D_eq := rfl
  KLayer_eq := rfl
  M_eq := rfl
  E_eq := rfl
  K_eq := rfl

/-- Primed all-zero saturated tail data. -/
structure PrimedZeroSaturatedData {L k d : Nat} (theta : Params L k d) where
  C : Nat → Matrix (Fin d) (Fin d) Real
  D : Nat → Matrix (Fin d) (Fin d) Real
  KLayer : Nat → Matrix (Fin d) (Fin d) Real
  M : Matrix (Fin d) (Fin d) Real
  E : Matrix (Fin d) (Fin d) Real
  C_eq : C = noSkipSaturatedC (saturatedValueFamily theta)
  D_eq_zero : D = 0
  KLayer_eq_C : KLayer = C
  M_eq : M = noSkipSaturatedM C L
  E_eq_zero : E = 0

noncomputable def primedZeroSaturatedData {L k d : Nat} (theta : Params L k d) :
    PrimedZeroSaturatedData theta where
  C := noSkipSaturatedC (saturatedValueFamily theta)
  D := 0
  KLayer := noSkipSaturatedC (saturatedValueFamily theta)
  M := noSkipSaturatedM (noSkipSaturatedC (saturatedValueFamily theta)) L
  E := 0
  C_eq := rfl
  D_eq_zero := rfl
  KLayer_eq_C := rfl
  M_eq := rfl
  E_eq_zero := rfl

@[simp] theorem saturatedAllZeroD_eq_zero {L k d : Nat} (theta : Params L k d) :
    noSkipSaturatedD (saturatedValueFamily theta) (saturatedAllZeroLabels k) = 0 := by
  funext j
  simp [noSkipSaturatedD, saturatedAllZeroLabels]

@[simp] theorem saturatedAllZeroKLayer_eq_C {L k d : Nat} (theta : Params L k d) :
    noSkipSaturatedKLayer (saturatedValueFamily theta) (saturatedAllZeroLabels k) =
      noSkipSaturatedC (saturatedValueFamily theta) := by
  funext j
  simp [noSkipSaturatedKLayer]

/-! ## Telescoping and primed transmission -/

/-- The aggregate saturated transport is the ordered product of the layerwise
contrast transports, including the empty-tail convention. -/
theorem SaturatedData.K_eq_layerProduct {L k d : Nat} {theta : Params L k d}
    {r : Nat} {labels : DeeperHead → TrichotomyLabel}
    (S : SaturatedData theta r labels) :
    S.K = layerProduct S.KLayer L 2 := by
  rw [S.K_eq, S.M_eq, S.E_eq, S.C_eq, S.D_eq, S.KLayer_eq]
  exact noSkipSaturatedK_eq_layerProduct
    (saturatedValueFamily theta) (saturatedNumericLabels (L := L) r labels) L

private theorem layerProductFrom_det_ne_zero {d : Nat}
    (M : Nat → Matrix (Fin d) (Fin d) Real) (i n : Nat)
    (hM : ∀ q, q < n → (M (i + q)).det ≠ 0) :
    (layerProductFrom M i n).det ≠ 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [layerProductFrom_succ, Matrix.det_mul]
      exact mul_ne_zero (hM n (Nat.lt_succ_self n))
        (ih (fun q hq => hM q (Nat.lt_succ_of_lt hq)))

theorem layerProduct_det_ne_zero_of_interval {d : Nat}
    (M : Nat → Matrix (Fin d) (Fin d) Real) (L : Nat)
    (hM : ∀ j, 2 ≤ j → j ≤ L → (M j).det ≠ 0) :
    (layerProduct M L 2).det ≠ 0 := by
  by_cases hL : L < 2
  · simp [layerProduct_empty M hL]
  · have h2L : 2 ≤ L := Nat.le_of_not_gt hL
    change (if L < 2 then 1 else layerProductFrom M 2 (L - 2 + 1)).det ≠ 0
    rw [if_neg hL]
    apply layerProductFrom_det_ne_zero
    intro q hq
    apply hM (2 + q) (by omega)
    omega

theorem noSkipSaturatedC_eq_collapseMatrix {L k d : Nat}
    (theta : Params L k d) {j : Nat} (hj1 : 1 ≤ j) (hjL : j ≤ L) :
    noSkipSaturatedC (saturatedValueFamily theta) j =
      collapseMatrix theta ⟨j - 1, by omega⟩ := by
  simp only [noSkipSaturatedC, saturatedValueFamily_of_mem theta hj1 hjL]
  rfl

/-- Target transmission regularity makes the primed all-zero tail product
`M' = C'_{L:2}` invertible. -/
theorem PrimedZeroSaturatedData.M_det_ne_zero {L k d : Nat}
    {theta : Params L k d} (S : PrimedZeroSaturatedData theta)
    (hreg : Regularity theta) : S.M.det ≠ 0 := by
  rw [S.M_eq]
  rw [S.C_eq]
  apply layerProduct_det_ne_zero_of_interval
  intro j hj2 hjL
  rw [noSkipSaturatedC_eq_collapseMatrix theta (by omega) hjL]
  exact hreg.transmission ⟨j - 1, by omega⟩

/-- Canonical primed all-zero specialization of the invertibility theorem. -/
theorem primedZeroSaturatedData_M_det_ne_zero {L k d : Nat}
    {theta : Params L k d} (hreg : Regularity theta) :
    (primedZeroSaturatedData theta).M.det ≠ 0 :=
  (primedZeroSaturatedData theta).M_det_ne_zero hreg

end

end TransformerIdentifiability.NLayer.NoSkip
