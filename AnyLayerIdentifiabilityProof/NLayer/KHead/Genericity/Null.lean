import AnyLayerIdentifiabilityProof.NLayer.KHead.Genericity.PolynomialCover

set_option autoImplicit false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open MeasureTheory Matrix MvPolynomial
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.KHead

/-!
# K-head algebraic null-set bridge

This shard packages the measure-theoretic part of K03D for k-head parameter
polynomial covers.  The zero-set lemmas are direct wrappers around the
foundation polynomial genericity API; the new work here is the product
Lebesgue bridge for the k-head flattening map.
-/

/-! ## K03D zero-set wrappers -/

/-- `K03D.E.lem-poly-zero.P`: a nonzero real coordinate polynomial has a null
zero set. -/
theorem kHead_mvpoly_zero_set_null {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : MvPolynomial ι ℝ) (hp : p ≠ 0) :
    volume {x : ι → ℝ | (MvPolynomial.eval x) p = 0} = 0 :=
  mvpoly_eval_null' p hp

/-- The zero set of a coordinate polynomial is closed. -/
theorem kHead_mvpoly_zero_set_closed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : MvPolynomial ι ℝ) :
    IsClosed {x : ι → ℝ | (MvPolynomial.eval x) p = 0} :=
  isClosed_singleton.preimage (MvPolynomial.continuous_eval p)

/-- The zero set of a nonzero coordinate polynomial has empty interior. -/
theorem kHead_mvpoly_zero_set_interior_eq_empty
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : MvPolynomial ι ℝ) (hp : p ≠ 0) :
    interior {x : ι → ℝ | (MvPolynomial.eval x) p = 0} = ∅ := by
  rw [interior_eq_empty_iff_dense_compl]
  simpa [Set.compl_setOf] using dense_compl_zero_set p hp

/-- A finite product of nonzero coordinate polynomials has a null zero set. -/
theorem kHead_mvpoly_finset_product_zero_set_null
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    {s : Finset κ} {p : κ → MvPolynomial ι ℝ}
    (hp : ∀ a, a ∈ s → p a ≠ 0) :
    volume {x : ι → ℝ | (MvPolynomial.eval x) (∏ a ∈ s, p a) = 0} = 0 :=
  mvpoly_eval_null' (∏ a ∈ s, p a) (mvpoly_finset_prod_ne_zero hp)

/-! ## Measure-preserving k-head parameter flattening -/

/-- Flatten all heads in one layer into value/attention coordinate functions. -/
def kHeadHeadsFlat {k d : Nat}
    (η : Fin k →
      Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ) :
    Fin k → TransformerIdentifiability.NLayer.LayerCoord d → ℝ :=
  fun a => TransformerIdentifiability.NLayer.layerFlat (η a)

/-- Uncurry head and entry coordinates inside one layer. -/
def kHeadHeadsUncurry {k d : Nat}
    (η : Fin k → TransformerIdentifiability.NLayer.LayerCoord d → ℝ) :
    Fin k × TransformerIdentifiability.NLayer.LayerCoord d → ℝ :=
  TransformerIdentifiability.NLayer.uncurry₂ η

/-- Flatten all heads in each layer, still curried by layer. -/
def kHeadParamFlatCurried {L k d : Nat} (θ : Params L k d) :
    Fin L → Fin k → TransformerIdentifiability.NLayer.LayerCoord d → ℝ :=
  fun l => kHeadHeadsFlat (θ l)

/-- Uncurry head/entry coordinates in every layer. -/
def kHeadParamFlatLayerUncurried {L k d : Nat}
    (θ : Fin L → Fin k → TransformerIdentifiability.NLayer.LayerCoord d → ℝ) :
    Fin L → Fin k × TransformerIdentifiability.NLayer.LayerCoord d → ℝ :=
  fun l => kHeadHeadsUncurry (θ l)

theorem measurePreserving_kHeadHeadsFlat (k d : Nat) :
    MeasurePreserving
      (kHeadHeadsFlat :
        (Fin k →
          Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ) →
            Fin k → TransformerIdentifiability.NLayer.LayerCoord d → ℝ)
      volume volume := by
  simpa [kHeadHeadsFlat] using
    (volume_preserving_pi
      (ι := Fin k)
      (α' := fun _ : Fin k =>
        Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
      (β' := fun _ : Fin k =>
        TransformerIdentifiability.NLayer.LayerCoord d → ℝ)
      (f := fun _ : Fin k => TransformerIdentifiability.NLayer.layerFlat)
      (fun _ => TransformerIdentifiability.NLayer.measurePreserving_layerFlat d))

theorem measurePreserving_kHeadParamFlatCurried (L k d : Nat) :
    MeasurePreserving
      (kHeadParamFlatCurried :
        Params L k d →
          Fin L → Fin k → TransformerIdentifiability.NLayer.LayerCoord d → ℝ)
      volume volume := by
  simpa [kHeadParamFlatCurried] using
    (volume_preserving_pi
      (ι := Fin L)
      (α' := fun _ : Fin L =>
        Fin k → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
      (β' := fun _ : Fin L =>
        Fin k → TransformerIdentifiability.NLayer.LayerCoord d → ℝ)
      (f := fun _ : Fin L => kHeadHeadsFlat)
      (fun _ => measurePreserving_kHeadHeadsFlat k d))

theorem measurePreserving_kHeadParamFlatLayerUncurried (L k d : Nat) :
    MeasurePreserving
      (kHeadParamFlatLayerUncurried :
        (Fin L → Fin k → TransformerIdentifiability.NLayer.LayerCoord d → ℝ) →
          Fin L → Fin k × TransformerIdentifiability.NLayer.LayerCoord d → ℝ)
      volume volume := by
  simpa [kHeadParamFlatLayerUncurried, kHeadHeadsUncurry] using
    (volume_preserving_pi
      (ι := Fin L)
      (α' := fun _ : Fin L =>
        Fin k → TransformerIdentifiability.NLayer.LayerCoord d → ℝ)
      (β' := fun _ : Fin L =>
        Fin k × TransformerIdentifiability.NLayer.LayerCoord d → ℝ)
      (f := fun _ : Fin L =>
        (TransformerIdentifiability.NLayer.uncurry₂ :
          (Fin k → TransformerIdentifiability.NLayer.LayerCoord d → ℝ) →
            Fin k × TransformerIdentifiability.NLayer.LayerCoord d → ℝ))
      (fun _ =>
        TransformerIdentifiability.NLayer.measurePreserving_uncurry₂
          (Fin k) (TransformerIdentifiability.NLayer.LayerCoord d)))

/-- K-head parameter flattening preserves product Lebesgue measure. -/
theorem measurePreserving_kHeadParamFlat (L k d : Nat) :
    MeasurePreserving
      (kHeadParamFlat : Params L k d → KHeadParamCoord L k d → ℝ)
      volume volume := by
  have hcurried := measurePreserving_kHeadParamFlatCurried L k d
  have hhead := measurePreserving_kHeadParamFlatLayerUncurried L k d
  have hlayer :=
    TransformerIdentifiability.NLayer.measurePreserving_uncurry₂
      (Fin L) (Fin k × TransformerIdentifiability.NLayer.LayerCoord d)
  simpa [kHeadParamFlat, kHeadParamFlatCurried, kHeadParamFlatLayerUncurried,
    kHeadHeadsFlat, kHeadHeadsUncurry, TransformerIdentifiability.NLayer.uncurry₂,
    Function.comp_def] using hlayer.comp (hhead.comp hcurried)

/-! ## Topology of k-head finite polynomial covers -/

/-- K-head parameter flattening is continuous. -/
theorem continuous_kHeadParamFlat (L k d : Nat) :
    Continuous (kHeadParamFlat : Params L k d → KHeadParamCoord L k d → ℝ) := by
  refine continuous_pi ?_
  rintro ⟨l, a, coord⟩
  cases coord with
  | inl ij =>
      rcases ij with ⟨i, j⟩
      change Continuous (fun θ : Params L k d => (θ l a).1 i j)
      exact (continuous_apply j).comp
        ((continuous_apply i).comp
          (continuous_fst.comp ((continuous_apply a).comp (continuous_apply l))))
  | inr ij =>
      rcases ij with ⟨i, j⟩
      change Continuous (fun θ : Params L k d => (θ l a).2 i j)
      exact (continuous_apply j).comp
        ((continuous_apply i).comp
          (continuous_snd.comp ((continuous_apply a).comp (continuous_apply l))))

/-- Reassemble a flattened k-head coordinate function into parameter matrices. -/
def kHeadParamUnflat {L k d : Nat}
    (x : KHeadParamCoord L k d → ℝ) : Params L k d :=
  fun l a =>
    (fun i j => x (l, (a, Sum.inl (i, j))),
      fun i j => x (l, (a, Sum.inr (i, j))))

/-- Reassembling flattened k-head coordinates is continuous. -/
theorem continuous_kHeadParamUnflat (L k d : Nat) :
    Continuous
      (kHeadParamUnflat :
        (KHeadParamCoord L k d → ℝ) → Params L k d) := by
  refine continuous_pi ?_
  intro l
  refine continuous_pi ?_
  intro a
  refine (continuous_pi ?_).prodMk (continuous_pi ?_)
  · intro i
    refine continuous_pi ?_
    intro j
    change Continuous
      (fun x : KHeadParamCoord L k d → ℝ => x (l, (a, Sum.inl (i, j))))
    exact continuous_apply _
  · intro i
    refine continuous_pi ?_
    intro j
    change Continuous
      (fun x : KHeadParamCoord L k d → ℝ => x (l, (a, Sum.inr (i, j))))
    exact continuous_apply _

@[simp]
theorem kHeadParamUnflat_flat {L k d : Nat} (θ : Params L k d) :
    kHeadParamUnflat (kHeadParamFlat θ) = θ := by
  funext l a
  exact Prod.ext (by ext i j; rfl) (by ext i j; rfl)

@[simp]
theorem kHeadParamFlat_unflat {L k d : Nat}
    (x : KHeadParamCoord L k d → ℝ) :
    kHeadParamFlat (kHeadParamUnflat x) = x := by
  funext c
  rcases c with ⟨l, a, coord⟩
  cases coord with
  | inl ij =>
      rcases ij with ⟨i, j⟩
      simp [kHeadParamFlat, kHeadParamUnflat,
        TransformerIdentifiability.NLayer.layerFlat,
        TransformerIdentifiability.NLayer.sumFlat,
        TransformerIdentifiability.NLayer.matrixFlat]
  | inr ij =>
      rcases ij with ⟨i, j⟩
      simp [kHeadParamFlat, kHeadParamUnflat,
        TransformerIdentifiability.NLayer.layerFlat,
        TransformerIdentifiability.NLayer.sumFlat,
        TransformerIdentifiability.NLayer.matrixFlat]

/-- K-head parameter flattening is a coordinate homeomorphism. -/
def kHeadParamFlatHomeomorph (L k d : Nat) :
    Params L k d ≃ₜ (KHeadParamCoord L k d → ℝ) where
  toFun := kHeadParamFlat
  invFun := kHeadParamUnflat
  left_inv := kHeadParamUnflat_flat
  right_inv := kHeadParamFlat_unflat
  continuous_toFun := continuous_kHeadParamFlat L k d
  continuous_invFun := continuous_kHeadParamUnflat L k d

/-- K-head parameter flattening is an open map. -/
theorem isOpenMap_kHeadParamFlat (L k d : Nat) :
    IsOpenMap (kHeadParamFlat : Params L k d → KHeadParamCoord L k d → ℝ) :=
  (kHeadParamFlatHomeomorph L k d).isOpenMap

/-- The common nonvanishing locus of a finite k-head coordinate-polynomial
package is open in parameter space. -/
theorem isOpen_kHeadParamNonvanishingCarrier
    {L k d : Nat} {κ : Type*}
    (D : PolynomialNonvanishingData (KHeadParamCoord L k d) κ) :
    IsOpen (kHeadParamNonvanishingCarrier D) :=
  D.isOpen_carrier.preimage (continuous_kHeadParamFlat L k d)

/-- The common nonvanishing locus of a finite k-head coordinate-polynomial
package is dense in parameter space. -/
theorem dense_kHeadParamNonvanishingCarrier
    {L k d : Nat} {κ : Type*}
    (D : PolynomialNonvanishingData (KHeadParamCoord L k d) κ) :
    Dense (kHeadParamNonvanishingCarrier D) := by
  simpa [kHeadParamNonvanishingCarrier] using
    D.dense_carrier.preimage (isOpenMap_kHeadParamFlat L k d)

/-- The exceptional complement of a finite k-head coordinate-polynomial
nonvanishing locus has empty interior. -/
theorem kHeadParamNonvanishingCarrier_compl_interior_eq_empty
    {L k d : Nat} {κ : Type*}
    (D : PolynomialNonvanishingData (KHeadParamCoord L k d) κ) :
    interior ((kHeadParamNonvanishingCarrier D)ᶜ) = ∅ := by
  rw [interior_eq_empty_iff_dense_compl]
  simpa [compl_compl] using dense_kHeadParamNonvanishingCarrier D

/-! ## Nullness of k-head finite polynomial covers -/

/-- The complement of a finite k-head coordinate-polynomial nonvanishing locus is
Lebesgue-null in parameter space. -/
theorem kHeadParamNonvanishingCarrier_compl_null
    {L k d : Nat} {κ : Type*}
    (D : PolynomialNonvanishingData (KHeadParamCoord L k d) κ) :
    volume (kHeadParamNonvanishingCarrier D)ᶜ = 0 := by
  classical
  have hmp := measurePreserving_kHeadParamFlat L k d
  set p : MvPolynomial (KHeadParamCoord L k d) ℝ :=
    ∏ a ∈ D.indices, D.poly a with hp_def
  have hp : p ≠ 0 := by
    rw [hp_def]
    exact mvpoly_finset_prod_ne_zero D.nonzero
  have htarget : D.carrierᶜ =
      {x : KHeadParamCoord L k d → ℝ | (MvPolynomial.eval x) p = 0} := by
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
  have hset : (kHeadParamNonvanishingCarrier D)ᶜ =
      kHeadParamFlat ⁻¹' (D.carrierᶜ) := by
    ext θ
    rfl
  rw [hset, hmp.measure_preimage hmeas]
  exact htarget_null

namespace KHeadParamPolynomialPredicateCover

/-- The exceptional set attached to a k-head polynomial predicate cover. -/
def badSet {L k d : Nat} {P : Params L k d → Prop}
    (C : KHeadParamPolynomialPredicateCover L k d P) : Set (Params L k d) :=
  (kHeadParamNonvanishingCarrier C.data)ᶜ

/-- The carrier of a k-head polynomial predicate cover is open. -/
theorem isOpen_carrier {L k d : Nat} {P : Params L k d → Prop}
    (C : KHeadParamPolynomialPredicateCover L k d P) :
    IsOpen (kHeadParamNonvanishingCarrier C.data) :=
  isOpen_kHeadParamNonvanishingCarrier C.data

/-- The carrier of a k-head polynomial predicate cover is dense. -/
theorem dense_carrier {L k d : Nat} {P : Params L k d → Prop}
    (C : KHeadParamPolynomialPredicateCover L k d P) :
    Dense (kHeadParamNonvanishingCarrier C.data) :=
  dense_kHeadParamNonvanishingCarrier C.data

/-- The cover's exceptional set is closed. -/
theorem isClosed_badSet {L k d : Nat} {P : Params L k d → Prop}
    (C : KHeadParamPolynomialPredicateCover L k d P) :
    IsClosed (C.badSet : Set (Params L k d)) := by
  simpa [badSet] using (isOpen_carrier C).isClosed_compl

/-- The cover's exceptional set is null. -/
theorem badSet_null {L k d : Nat} {P : Params L k d → Prop}
    (C : KHeadParamPolynomialPredicateCover L k d P) :
    volume (C.badSet : Set (Params L k d)) = 0 := by
  simpa [badSet] using kHeadParamNonvanishingCarrier_compl_null C.data

/-- The cover's exceptional set has empty interior. -/
theorem badSet_interior_eq_empty {L k d : Nat} {P : Params L k d → Prop}
    (C : KHeadParamPolynomialPredicateCover L k d P) :
    interior (C.badSet : Set (Params L k d)) = ∅ := by
  simpa [badSet] using
    kHeadParamNonvanishingCarrier_compl_interior_eq_empty C.data

/-- The complement of the cover's exceptional set is dense. -/
theorem dense_compl_badSet {L k d : Nat} {P : Params L k d → Prop}
    (C : KHeadParamPolynomialPredicateCover L k d P) :
    Dense ((C.badSet : Set (Params L k d))ᶜ) := by
  simpa [badSet, compl_compl] using dense_carrier C

/-- The predicate bad set is contained in the polynomial exceptional set. -/
theorem predicateBadSet_subset_badSet
    {L k d : Nat} {P : Params L k d → Prop}
    (C : KHeadParamPolynomialPredicateCover L k d P) :
    {θ : Params L k d | ¬ P θ} ⊆ C.badSet := by
  intro θ hθ hcarrier
  exact hθ (C.carrier_subset hcarrier)

/-- `K03D.E.prop-generic-algebraic.P`, cover-to-null form: any finite
nonzero coordinate-polynomial package whose carrier implies a k-head predicate
has null predicate complement. -/
theorem predicateBadSet_null
    {L k d : Nat} {P : Params L k d → Prop}
    (C : KHeadParamPolynomialPredicateCover L k d P) :
    volume ({θ : Params L k d | ¬ P θ}) = 0 := by
  exact measure_mono_null (predicateBadSet_subset_badSet C) (badSet_null C)

/-- The predicate bad set controlled by a k-head polynomial cover has empty
interior. -/
theorem predicateBadSet_interior_eq_empty
    {L k d : Nat} {P : Params L k d → Prop}
    (C : KHeadParamPolynomialPredicateCover L k d P) :
    interior ({θ : Params L k d | ¬ P θ}) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro θ hθ
  have hbad : θ ∈ interior (C.badSet : Set (Params L k d)) :=
    interior_mono (predicateBadSet_subset_badSet C) hθ
  rw [badSet_interior_eq_empty C] at hbad
  exact hbad

/-- Any predicate controlled by a k-head polynomial cover holds on a dense set. -/
theorem dense_predicateSet
    {L k d : Nat} {P : Params L k d → Prop}
    (C : KHeadParamPolynomialPredicateCover L k d P) :
    Dense ({θ : Params L k d | P θ}) := by
  classical
  simpa [Set.compl_setOf] using
    (interior_eq_empty_iff_dense_compl.mp
      (predicateBadSet_interior_eq_empty C))

end KHeadParamPolynomialPredicateCover

/-! ## Nullness consequences for k-head genericity predicates -/

/-- `K03D.E.prop-generic-algebraic.P`, recursive-generic bridge form:
once a finite nonzero coordinate-polynomial package implies the recursive
k-head generic predicate, the recursive-generic bad set is null. -/
theorem recursiveGenericBadSet_null_of_kHeadParamPolynomialPredicateCover
    {r L k d : Nat}
    (C : KHeadParamPolynomialPredicateCover L k d
      (fun θ => RecursiveGeneric r L k d θ)) :
    volume (RecursiveGenericBadSet r L k d : Set (Params L k d)) = 0 := by
  simpa [RecursiveGenericBadSet, RecursiveGenericSet] using
    KHeadParamPolynomialPredicateCover.predicateBadSet_null C

/-- Data-level version of `recursiveGenericBadSet_null_of_kHeadParamPolynomialPredicateCover`.
This is the direct endpoint needed after constructing the finite product cover
for all recursive genericity clauses. -/
theorem recursiveGenericBadSet_null_of_kHeadParamNonvanishingCarrier_subset
    {r L k d : Nat} {κ : Type*}
    (D : PolynomialNonvanishingData (KHeadParamCoord L k d) κ)
    (hsubset :
      kHeadParamNonvanishingCarrier D ⊆ RecursiveGenericSet r L k d) :
    volume (RecursiveGenericBadSet r L k d : Set (Params L k d)) = 0 := by
  refine measure_mono_null ?_ (kHeadParamNonvanishingCarrier_compl_null D)
  intro θ hbad hθpoly
  exact hbad (hsubset hθpoly)

/-! ## Concrete recursive-generic nullness wrappers -/

/-- Concrete algebraic-null consequence for the fully assembled recursive
k-head genericity cover. -/
theorem kHeadRecursiveGenericBadSet_null {r L k d : Nat}
    (hd : 0 < d) (hrows : nBullet L k + 1 ≤ d) :
    volume (RecursiveGenericBadSet r L k d : Set (Params L k d)) = 0 := by
  exact recursiveGenericBadSet_null_of_kHeadParamPolynomialPredicateCover
    (kHeadRecursiveGenericPolynomialCover r L k d hd hrows)

/-- The concrete recursive-generic bad set has empty interior. -/
theorem kHeadRecursiveGenericBadSet_interior_eq_empty {r L k d : Nat}
    (hd : 0 < d) (hrows : nBullet L k + 1 ≤ d) :
    interior (RecursiveGenericBadSet r L k d : Set (Params L k d)) = ∅ := by
  change interior ({θ : Params L k d | ¬ RecursiveGeneric r L k d θ}) = ∅
  exact KHeadParamPolynomialPredicateCover.predicateBadSet_interior_eq_empty
    (kHeadRecursiveGenericPolynomialCover r L k d hd hrows)

/-- The concrete recursive-generic parameter set is dense. -/
theorem dense_kHeadRecursiveGenericSet {r L k d : Nat}
    (hd : 0 < d) (hrows : nBullet L k + 1 ≤ d) :
    Dense (RecursiveGenericSet r L k d : Set (Params L k d)) := by
  change Dense ({θ : Params L k d | RecursiveGeneric r L k d θ})
  exact KHeadParamPolynomialPredicateCover.dense_predicateSet
    (kHeadRecursiveGenericPolynomialCover r L k d hd hrows)

/-! ## Concrete local-openness consequences -/

/-- The concrete local-openness polynomial carrier is exactly the
`LocalOpenness` predicate. -/
theorem kHeadLocalOpennessPolynomialCover_carrier_eq
    {r L k d : Nat} :
    kHeadParamNonvanishingCarrier
        (kHeadLocalOpennessPolynomialCover r L k d).data =
      {θ : Params L k d | LocalOpenness r θ} := by
  ext θ
  constructor
  · intro hθ
    exact (kHeadLocalOpennessPolynomialCover r L k d).carrier_subset hθ
  · intro hθ l _hl
    simpa [kHeadLocalOpennessPolynomialCover, kHeadLocalOpennessPoly,
      eval_det_genLocalDerivativeOperatorMatrix r θ l] using hθ l

/-- The concrete local-openness polynomial carrier is open. -/
theorem isOpen_kHeadLocalOpennessPolynomialCover_carrier
    {r L k d : Nat} :
    IsOpen
      (kHeadParamNonvanishingCarrier
        (kHeadLocalOpennessPolynomialCover r L k d).data) :=
  KHeadParamPolynomialPredicateCover.isOpen_carrier
    (kHeadLocalOpennessPolynomialCover r L k d)

/-- The concrete local-openness predicate is open. -/
theorem isOpen_kHeadLocalOpenness {r L k d : Nat} :
    IsOpen ({θ : Params L k d | LocalOpenness r θ}) := by
  rw [← kHeadLocalOpennessPolynomialCover_carrier_eq (r := r) (L := L)
    (k := k) (d := d)]
  exact isOpen_kHeadLocalOpennessPolynomialCover_carrier

/-- The concrete local-openness polynomial carrier is dense. -/
theorem dense_kHeadLocalOpennessPolynomialCover_carrier
    {r L k d : Nat} :
    Dense
      (kHeadParamNonvanishingCarrier
        (kHeadLocalOpennessPolynomialCover r L k d).data) :=
  KHeadParamPolynomialPredicateCover.dense_carrier
    (kHeadLocalOpennessPolynomialCover r L k d)

/-- The concrete local-openness predicate is dense. -/
theorem dense_kHeadLocalOpenness {r L k d : Nat} :
    Dense ({θ : Params L k d | LocalOpenness r θ}) := by
  rw [← kHeadLocalOpennessPolynomialCover_carrier_eq (r := r) (L := L)
    (k := k) (d := d)]
  exact dense_kHeadLocalOpennessPolynomialCover_carrier

/-- The concrete local-openness polynomial exceptional set is closed. -/
theorem isClosed_kHeadLocalOpennessPolynomialCover_badSet
    {r L k d : Nat} :
    IsClosed
      ((kHeadLocalOpennessPolynomialCover r L k d).badSet :
        Set (Params L k d)) :=
  KHeadParamPolynomialPredicateCover.isClosed_badSet
    (kHeadLocalOpennessPolynomialCover r L k d)

/-- The concrete local-openness bad set is closed. -/
theorem isClosed_kHeadLocalOpenness_badSet {r L k d : Nat} :
    IsClosed ({θ : Params L k d | ¬ LocalOpenness r θ}) := by
  simpa [Set.compl_setOf] using (isOpen_kHeadLocalOpenness (r := r) (L := L)
    (k := k) (d := d)).isClosed_compl

/-- The concrete local-openness polynomial exceptional set is null. -/
theorem kHeadLocalOpennessPolynomialCover_badSet_null
    {r L k d : Nat} :
    volume
      ((kHeadLocalOpennessPolynomialCover r L k d).badSet :
        Set (Params L k d)) = 0 :=
  KHeadParamPolynomialPredicateCover.badSet_null
    (kHeadLocalOpennessPolynomialCover r L k d)

/-- Concrete algebraic-null consequence for the local-openness cover. -/
theorem kHeadLocalOpenness_badSet_null {r L k d : Nat} :
    volume ({θ : Params L k d | ¬ LocalOpenness r θ}) = 0 := by
  exact KHeadParamPolynomialPredicateCover.predicateBadSet_null
    (kHeadLocalOpennessPolynomialCover r L k d)

/-- The concrete local-openness polynomial exceptional set has empty interior. -/
theorem kHeadLocalOpennessPolynomialCover_badSet_interior_eq_empty
    {r L k d : Nat} :
    interior
      ((kHeadLocalOpennessPolynomialCover r L k d).badSet :
        Set (Params L k d)) = ∅ :=
  KHeadParamPolynomialPredicateCover.badSet_interior_eq_empty
    (kHeadLocalOpennessPolynomialCover r L k d)

/-- The concrete local-openness bad set has empty interior. -/
theorem kHeadLocalOpenness_badSet_interior_eq_empty
    {r L k d : Nat} :
    interior ({θ : Params L k d | ¬ LocalOpenness r θ}) = ∅ :=
  KHeadParamPolynomialPredicateCover.predicateBadSet_interior_eq_empty
    (kHeadLocalOpennessPolynomialCover r L k d)

/-- The complement of the concrete local-openness polynomial exceptional set is
dense. -/
theorem dense_compl_kHeadLocalOpennessPolynomialCover_badSet
    {r L k d : Nat} :
    Dense
      (((kHeadLocalOpennessPolynomialCover r L k d).badSet :
        Set (Params L k d))ᶜ) :=
  KHeadParamPolynomialPredicateCover.dense_compl_badSet
    (kHeadLocalOpennessPolynomialCover r L k d)

/-- Concrete algebraic-null consequence for the currently proved elementary
matrix-clause cover `(R1)`--`(R2)`. -/
theorem kHeadBasicMatrixClauses_badSet_null {L k d : Nat} (hd : 0 < d) :
    volume ({θ : Params L k d | ¬ KHeadBasicMatrixClauses θ}) = 0 := by
  exact KHeadParamPolynomialPredicateCover.predicateBadSet_null
    (kHeadBasicMatrixPolynomialCover L k d hd)

/-- The concrete elementary matrix-clause polynomial carrier is open. -/
theorem isOpen_kHeadBasicMatrixPolynomialCover_carrier
    {L k d : Nat} (hd : 0 < d) :
    IsOpen
      (kHeadParamNonvanishingCarrier
        (kHeadBasicMatrixPolynomialCover L k d hd).data) :=
  KHeadParamPolynomialPredicateCover.isOpen_carrier
    (kHeadBasicMatrixPolynomialCover L k d hd)

/-- The concrete elementary matrix-clause polynomial carrier is dense. -/
theorem dense_kHeadBasicMatrixPolynomialCover_carrier
    {L k d : Nat} (hd : 0 < d) :
    Dense
      (kHeadParamNonvanishingCarrier
        (kHeadBasicMatrixPolynomialCover L k d hd).data) :=
  KHeadParamPolynomialPredicateCover.dense_carrier
    (kHeadBasicMatrixPolynomialCover L k d hd)

/-- The concrete elementary matrix-clause polynomial exceptional set has empty
interior. -/
theorem kHeadBasicMatrixPolynomialCover_badSet_interior_eq_empty
    {L k d : Nat} (hd : 0 < d) :
    interior
      ((kHeadBasicMatrixPolynomialCover L k d hd).badSet :
        Set (Params L k d)) = ∅ :=
  KHeadParamPolynomialPredicateCover.badSet_interior_eq_empty
    (kHeadBasicMatrixPolynomialCover L k d hd)

/-- The concrete elementary matrix-clause bad set has empty interior. -/
theorem kHeadBasicMatrixClauses_badSet_interior_eq_empty
    {L k d : Nat} (hd : 0 < d) :
    interior ({θ : Params L k d | ¬ KHeadBasicMatrixClauses θ}) = ∅ :=
  KHeadParamPolynomialPredicateCover.predicateBadSet_interior_eq_empty
    (kHeadBasicMatrixPolynomialCover L k d hd)

/-- The concrete elementary matrix clauses hold on a dense set. -/
theorem dense_kHeadBasicMatrixClauses {L k d : Nat} (hd : 0 < d) :
    Dense ({θ : Params L k d | KHeadBasicMatrixClauses θ}) :=
  KHeadParamPolynomialPredicateCover.dense_predicateSet
    (kHeadBasicMatrixPolynomialCover L k d hd)

end TransformerIdentifiability.NLayer.KHead
