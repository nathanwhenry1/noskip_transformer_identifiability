import AnyLayerIdentifiabilityProof.NLayer.Foundations.Core
import AnyLayerIdentifiabilityProof.NLayer.Foundations.PolynomialGenericity

set_option autoImplicit false

open MeasureTheory Matrix MvPolynomial

namespace TransformerIdentifiability.NLayer

/-!
# Polynomial genericity on the `Params L d` space

This file connects the coordinate-polynomial null-set lemmas in
`NLayer.PolynomialGenericity` to the concrete L-layer parameter space.  It provides the
L-layer analogue of the two-layer `flat` map used in `2_layer_identifiability.lean`.
-/

/-- One matrix coordinate. -/
abbrev MatrixCoord (d : Nat) : Type :=
  Fin d × Fin d

/-- One layer coordinate: value-matrix entries on the left, attention-matrix entries on
the right. -/
abbrev LayerCoord (d : Nat) : Type :=
  MatrixCoord d ⊕ MatrixCoord d

/-- Full depth-`L` parameter coordinates. -/
abbrev ParamCoord (L d : Nat) : Type :=
  Fin L × LayerCoord d

/-- Coordinate ring of the flattened depth-`L` parameter space. -/
abbrev ParamRing (L d : Nat) : Type :=
  MvPolynomial (ParamCoord L d) ℝ

/-- Uncurry a finite two-index real function. -/
def uncurry₂ {α β : Type*} (x : α -> β -> ℝ) : α × β -> ℝ :=
  fun k => x k.1 k.2

/-- Uncurrying finite real coordinates preserves product Lebesgue measure. -/
theorem measurePreserving_uncurry₂ (α β : Type*) [Fintype α] [Fintype β] :
    MeasurePreserving
      (uncurry₂ : (α -> β -> ℝ) -> (α × β -> ℝ))
      (volume : Measure (α -> β -> ℝ))
      (volume : Measure (α × β -> ℝ)) := by
  set f : (α -> β -> ℝ) -> (α × β -> ℝ) := uncurry₂ with hf
  have hfmeas : Measurable f := by
    rw [measurable_pi_iff]
    intro k
    exact (measurable_pi_apply k.2).comp (measurable_pi_apply k.1)
  refine ⟨hfmeas, ?_⟩
  rw [volume_pi (α := fun _ : α × β => ℝ)]
  symm
  refine Measure.pi_eq (fun s hs => ?_)
  rw [Measure.map_apply hfmeas (MeasurableSet.univ_pi hs)]
  have hpre : f ⁻¹' (Set.univ.pi s)
      = Set.univ.pi (fun i : α => Set.univ.pi (fun j : β => s (i, j))) := by
    ext x
    simp only [hf, uncurry₂, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
      Prod.forall]
  rw [hpre, volume_pi_pi]
  simp_rw [volume_pi_pi]
  rw [← Finset.univ_product_univ, Finset.prod_product]

/-- Uncurry a square matrix into its flat coordinate function. -/
def matrixFlat {d : Nat} (M : Matrix (Fin d) (Fin d) ℝ) : MatrixCoord d -> ℝ :=
  fun k => M k.1 k.2

/-- Matrix uncurrying preserves product Lebesgue measure. -/
theorem measurePreserving_matrixFlat (d : Nat) :
    MeasurePreserving
      (matrixFlat : Matrix (Fin d) (Fin d) ℝ -> MatrixCoord d -> ℝ)
      (volume : Measure (Matrix (Fin d) (Fin d) ℝ))
      (volume : Measure (MatrixCoord d -> ℝ)) := by
  simpa [matrixFlat, MatrixCoord, uncurry₂] using
    measurePreserving_uncurry₂ (Fin d) (Fin d)

/-- Combine two flat coordinate functions into a sum-indexed coordinate function. -/
def sumFlat {α β : Type*} (p : (α -> ℝ) × (β -> ℝ)) : α ⊕ β -> ℝ :=
  Sum.elim p.1 p.2

/-- Combining finite coordinate blocks over a sum preserves product Lebesgue measure. -/
theorem measurePreserving_sumFlat {α β : Type*} [Fintype α] [Fintype β] :
    MeasurePreserving
      (sumFlat : (α -> ℝ) × (β -> ℝ) -> (α ⊕ β -> ℝ))
      (volume : Measure ((α -> ℝ) × (β -> ℝ)))
      (volume : Measure (α ⊕ β -> ℝ)) := by
  have h := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : α ⊕ β => ℝ)
  have heq : (sumFlat : (α -> ℝ) × (β -> ℝ) -> (α ⊕ β -> ℝ))
      = ⇑(MeasurableEquiv.sumPiEquivProdPi (fun _ : α ⊕ β => ℝ)).symm := by
    funext p
    rw [MeasurableEquiv.coe_sumPiEquivProdPi_symm]
    funext x
    cases x <;> rfl
  rw [heq]
  exact h

/-- Flatten one `(V, A)` layer into value and attention coordinates. -/
def layerFlat {d : Nat}
    (p : Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ) :
    LayerCoord d -> ℝ :=
  sumFlat (matrixFlat p.1, matrixFlat p.2)

/-- One-layer flattening preserves product Lebesgue measure. -/
theorem measurePreserving_layerFlat (d : Nat) :
    MeasurePreserving
      (layerFlat : Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ ->
        LayerCoord d -> ℝ)
      (volume : Measure (Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ))
      (volume : Measure (LayerCoord d -> ℝ)) := by
  haveI : SFinite (volume : Measure (Matrix (Fin d) (Fin d) ℝ)) :=
    inferInstanceAs (SFinite (volume : Measure (Fin d -> Fin d -> ℝ)))
  exact measurePreserving_sumFlat.comp
    ((measurePreserving_matrixFlat d).prod (measurePreserving_matrixFlat d))

/-- Flatten each layer, retaining a curried layer/coordinate index. -/
def paramsLayerFlat {L d : Nat} (θ : Params L d) : Fin L -> LayerCoord d -> ℝ :=
  fun l => layerFlat (θ l)

/-- Componentwise layer flattening preserves product Lebesgue measure. -/
theorem measurePreserving_paramsLayerFlat (L d : Nat) :
    MeasurePreserving
      (paramsLayerFlat : Params L d -> Fin L -> LayerCoord d -> ℝ)
      (volume : Measure (Params L d))
      (volume : Measure (Fin L -> LayerCoord d -> ℝ)) := by
  simpa [paramsLayerFlat] using
    (volume_preserving_pi (ι := Fin L)
      (α' := fun _ : Fin L =>
        Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
      (β' := fun _ : Fin L => LayerCoord d -> ℝ)
      (f := fun _ : Fin L => layerFlat)
      (fun _ => measurePreserving_layerFlat d))

/-- Flatten all parameters to a single coordinate function. -/
def paramFlat {L d : Nat} (θ : Params L d) : ParamCoord L d -> ℝ :=
  uncurry₂ (paramsLayerFlat θ)

/-- Full parameter flattening preserves product Lebesgue measure. -/
theorem measurePreserving_paramFlat (L d : Nat) :
    MeasurePreserving
      (paramFlat : Params L d -> ParamCoord L d -> ℝ)
      (volume : Measure (Params L d))
      (volume : Measure (ParamCoord L d -> ℝ)) := by
  simpa [paramFlat, Function.comp_def] using
    (measurePreserving_uncurry₂ (Fin L) (LayerCoord d)).comp
      (measurePreserving_paramsLayerFlat L d)

@[simp]
theorem paramFlat_value {L d : Nat} (θ : Params L d) (l : Fin L)
    (i j : Fin d) :
    paramFlat θ (l, Sum.inl (i, j)) = (θ l).1 i j :=
  rfl

@[simp]
theorem paramFlat_attention {L d : Nat} (θ : Params L d) (l : Fin L)
    (i j : Fin d) :
    paramFlat θ (l, Sum.inr (i, j)) = (θ l).2 i j :=
  rfl

/-! ## Generic coordinate matrices -/

/-- The generic value matrix at layer `l`. -/
noncomputable def genValue (L d : Nat) (l : Fin L) :
    Matrix (Fin d) (Fin d) (ParamRing L d) :=
  Matrix.of fun i j => MvPolynomial.X (l, Sum.inl (i, j))

/-- The generic attention matrix at layer `l`. -/
noncomputable def genAttention (L d : Nat) (l : Fin L) :
    Matrix (Fin d) (Fin d) (ParamRing L d) :=
  Matrix.of fun i j => MvPolynomial.X (l, Sum.inr (i, j))

theorem map_genValue {L d : Nat} (θ : Params L d) (l : Fin L) :
    (genValue L d l).map (MvPolynomial.eval (paramFlat θ)) = (θ l).1 := by
  ext i j
  simp [genValue, Matrix.map_apply]

theorem map_genAttention {L d : Nat} (θ : Params L d) (l : Fin L) :
    (genAttention L d l).map (MvPolynomial.eval (paramFlat θ)) = (θ l).2 := by
  ext i j
  simp [genAttention, Matrix.map_apply]

/-! ## Null sets pulled back to parameters -/

/-- Pull a packaged finite coordinate-polynomial nonvanishing locus back to the
parameter space. -/
def paramNonvanishingCarrier {L d : Nat} {κ : Type*}
    (D : PolynomialNonvanishingData (ParamCoord L d) κ) : Set (Params L d) :=
  paramFlat ⁻¹' D.carrier

@[simp]
theorem mem_paramNonvanishingCarrier {L d : Nat} {κ : Type*}
    (D : PolynomialNonvanishingData (ParamCoord L d) κ) (θ : Params L d) :
    θ ∈ paramNonvanishingCarrier D ↔
      ∀ a, a ∈ D.indices -> (MvPolynomial.eval (paramFlat θ)) (D.poly a) ≠ 0 := by
  rfl

/-- The complement of a finite coordinate-polynomial nonvanishing locus, pulled back to
`Params L d`, is Lebesgue-null. -/
theorem paramNonvanishingCarrier_compl_null {L d : Nat} {κ : Type*}
    (D : PolynomialNonvanishingData (ParamCoord L d) κ) :
    volume (paramNonvanishingCarrier D)ᶜ = 0 := by
  classical
  have hmp := measurePreserving_paramFlat L d
  set p : MvPolynomial (ParamCoord L d) ℝ := ∏ a ∈ D.indices, D.poly a with hp_def
  have hp : p ≠ 0 := by
    rw [hp_def]
    exact mvpoly_finset_prod_ne_zero D.nonzero
  have htarget : D.carrierᶜ =
      {x : ParamCoord L d -> ℝ | (MvPolynomial.eval x) p = 0} := by
    ext x
    constructor
    · intro hx
      by_contra hne
      exact hx ((eval_finset_prod_ne_zero_iff (s := D.indices) (p := D.poly) x).mp
        (by simpa [hp_def] using hne))
    · intro hx hcarrier
      exact ((eval_finset_prod_ne_zero_iff (s := D.indices) (p := D.poly) x).mpr
        (by simpa [PolynomialNonvanishingData.carrier] using hcarrier)) hx
  have htarget_null : volume D.carrierᶜ = 0 := by
    rw [htarget]
    exact mvpoly_eval_null' p hp
  have hmeas : NullMeasurableSet D.carrierᶜ :=
    (D.isOpen_carrier.measurableSet.compl).nullMeasurableSet
  have hset : (paramNonvanishingCarrier D)ᶜ =
      paramFlat ⁻¹' (D.carrierᶜ) := by
    ext θ
    rfl
  rw [hset, hmp.measure_preimage hmeas]
  exact htarget_null

end TransformerIdentifiability.NLayer
