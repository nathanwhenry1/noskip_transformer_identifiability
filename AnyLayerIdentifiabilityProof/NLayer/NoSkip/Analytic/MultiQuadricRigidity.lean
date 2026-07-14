import AnyLayerIdentifiabilityProof.NLayer.NoSkip.SharedToolbox

set_option autoImplicit false

open Matrix

namespace TransformerIdentifiability.NLayer.NoSkip

/-!
# Geometry of the simultaneous first-layer quadrics

This file uses the transpose-dot form of `w^T A v`; doing so keeps the slice
definition manifestly linear in `v` and independent of transformer semantics.
-/

/-- One bilinear form in the family defining the multi-quadric. -/
noncomputable def multiQuadricForm {k d : Nat}
    (A : Fin k → Matrix (Fin d) (Fin d) Real) (a : Fin k)
    (w v : Fin d → Real) : Real :=
  dotProduct ((A a)ᵀ *ᵥ w) v

/-- Matrix whose rows are the anchor gradients at `w`. -/
noncomputable def multiQuadricGradientMatrix {k d : Nat}
    (A : Fin k → Matrix (Fin d) (Fin d) Real) (w : Fin d → Real) :
    Matrix (Fin k) (Fin d) Real :=
  fun a i => ((A a)ᵀ *ᵥ w) i

/-- TeX `H_w`, the common linear zero slice of all first-layer quadrics. -/
def multiQuadricSlice {k d : Nat}
    (A : Fin k → Matrix (Fin d) (Fin d) Real) (w : Fin d → Real) :
    Set (Fin d → Real) :=
  {v | ∀ a : Fin k, multiQuadricForm A a w v = 0}

/-- TeX `Q`, the intersection of the `k` bilinear quadrics. -/
def multiQuadric {k d : Nat}
    (A : Fin k → Matrix (Fin d) (Fin d) Real) :
    Set ((Fin d → Real) × (Fin d → Real)) :=
  {wv | wv.2 ∈ multiQuadricSlice A wv.1}

@[simp] theorem mem_multiQuadricSlice_iff {k d : Nat}
    (A : Fin k → Matrix (Fin d) (Fin d) Real) (w v : Fin d → Real) :
    v ∈ multiQuadricSlice A w ↔
      ∀ a : Fin k, multiQuadricForm A a w v = 0 :=
  Iff.rfl

@[simp] theorem mem_multiQuadric_iff {k d : Nat}
    (A : Fin k → Matrix (Fin d) (Fin d) Real) (w v : Fin d → Real) :
    (w, v) ∈ multiQuadric A ↔ v ∈ multiQuadricSlice A w :=
  Iff.rfl

@[simp] theorem mem_multiQuadric_iff_forall {k d : Nat}
    (A : Fin k → Matrix (Fin d) (Fin d) Real) (w v : Fin d → Real) :
    (w, v) ∈ multiQuadric A ↔
      ∀ a : Fin k, multiQuadricForm A a w v = 0 :=
  Iff.rfl

@[simp] theorem zero_mem_multiQuadricSlice {k d : Nat}
    (A : Fin k → Matrix (Fin d) (Fin d) Real) (w : Fin d → Real) :
    (0 : Fin d → Real) ∈ multiQuadricSlice A w := by
  intro a
  simp [multiQuadricForm]

theorem add_mem_multiQuadricSlice {k d : Nat}
    {A : Fin k → Matrix (Fin d) (Fin d) Real} {w v₁ v₂ : Fin d → Real}
    (hv₁ : v₁ ∈ multiQuadricSlice A w) (hv₂ : v₂ ∈ multiQuadricSlice A w) :
    v₁ + v₂ ∈ multiQuadricSlice A w := by
  change ∀ a : Fin k, multiQuadricForm A a w v₁ = 0 at hv₁
  change ∀ a : Fin k, multiQuadricForm A a w v₂ = 0 at hv₂
  change ∀ a : Fin k, multiQuadricForm A a w (v₁ + v₂) = 0
  intro a
  have hv₁a : dotProduct ((A a)ᵀ *ᵥ w) v₁ = 0 := by
    simpa [multiQuadricForm] using hv₁ a
  have hv₂a : dotProduct ((A a)ᵀ *ᵥ w) v₂ = 0 := by
    simpa [multiQuadricForm] using hv₂ a
  simp [multiQuadricForm, dotProduct_add, hv₁a, hv₂a]

theorem smul_mem_multiQuadricSlice {k d : Nat}
    {A : Fin k → Matrix (Fin d) (Fin d) Real} {w v : Fin d → Real}
    (hv : v ∈ multiQuadricSlice A w) (c : Real) :
    c • v ∈ multiQuadricSlice A w := by
  change ∀ a : Fin k, multiQuadricForm A a w v = 0 at hv
  change ∀ a : Fin k, multiQuadricForm A a w (c • v) = 0
  intro a
  have hva : dotProduct ((A a)ᵀ *ᵥ w) v = 0 := by
    simpa [multiQuadricForm] using hv a
  simp [multiQuadricForm, dotProduct_smul, hva]

/-- The slice family as an actual linear subspace, for affine restriction. -/
def multiQuadricSliceSubmodule {k d : Nat}
    (A : Fin k → Matrix (Fin d) (Fin d) Real) (w : Fin d → Real) :
    Submodule Real (Fin d → Real) where
  carrier := multiQuadricSlice A w
  zero_mem' := zero_mem_multiQuadricSlice A w
  add_mem' := add_mem_multiQuadricSlice
  smul_mem' := fun c _ hv => smul_mem_multiQuadricSlice hv c

@[simp] theorem mem_multiQuadricSliceSubmodule_iff {k d : Nat}
    (A : Fin k → Matrix (Fin d) (Fin d) Real) (w v : Fin d → Real) :
    v ∈ multiQuadricSliceSubmodule A w ↔ v ∈ multiQuadricSlice A w :=
  Iff.rfl

/-- Concrete witnesses for the slice hypothesis in TeX Lemma
`lem:multi-quadric-rigidity`.  This is data rather than a proposition so its
open base and slice family have usable projections. -/
structure MultiQuadricSliceWitness {k d : Nat}
    (A : Fin k → Matrix (Fin d) (Fin d) Real)
    (S : Set ((Fin d → Real) × (Fin d → Real))) where
  W : Set (Fin d → Real)
  W_open : IsOpen W
  W_nonempty : W.Nonempty
  slice : (w : Fin d → Real) → Set (Fin d → Real)
  slice_nonempty : ∀ w, w ∈ W → (slice w).Nonempty
  slice_relativelyOpen :
    ∀ w, w ∈ W → RelativelyOpenIn (slice w) (multiQuadricSlice A w)
  slice_subset : ∀ w, w ∈ W → Set.prod {w} (slice w) ⊆ S

/-- The proposition that `S` admits the exact open-base, relatively-open-slice
structure required by the TeX rigidity lemma. -/
def MultiQuadricSliceStructure {k d : Nat}
    (A : Fin k → Matrix (Fin d) (Fin d) Real)
    (S : Set ((Fin d → Real) × (Fin d → Real))) : Prop :=
  Nonempty (MultiQuadricSliceWitness A S)

theorem MultiQuadricSliceWitness.mem_slice_of_subset_multiQuadric {k d : Nat}
    {A : Fin k → Matrix (Fin d) (Fin d) Real}
    {S : Set ((Fin d → Real) × (Fin d → Real))}
    (hS : MultiQuadricSliceWitness A S) (hSQ : S ⊆ multiQuadric A)
    {w v : Fin d → Real} (hw : w ∈ hS.W) (hv : v ∈ hS.slice w) :
    v ∈ multiQuadricSlice A w := by
  have hpair : (w, v) ∈ S := hS.slice_subset w hw ⟨by simp, hv⟩
  exact (mem_multiQuadric_iff A w v).mp (hSQ hpair)

/-! ## Affine restriction to a linear subspace -/

/-- A vector-valued affine map which vanishes on a nonempty relatively open
subset of a finite-dimensional linear subspace vanishes on the whole
subspace.  No codomain topology or choice of coordinates is needed. -/
theorem affineMap_eq_zero_on_submodule_of_relativelyOpen {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
    [AddCommGroup F] [Module Real F]
    (H : Submodule Real E) {O : Set E}
    (hO_rel : RelativelyOpenIn O (H : Set E)) (hO_nonempty : O.Nonempty)
    (L : E →ₗ[Real] F) (b : F)
    (hzero : ∀ v : E, v ∈ O → L v + b = 0) :
    ∀ v : E, v ∈ H → L v + b = 0 := by
  rcases hO_rel with ⟨U, hU_open, rfl⟩
  rcases hO_nonempty with ⟨v₀, hv₀U, hv₀H⟩
  let v₀H : H := ⟨v₀, hv₀H⟩
  let D : Set H := {h | (h : E) + (v₀H : E) ∈ U}
  have hD_open : IsOpen D := by
    exact hU_open.preimage (continuous_subtype_val.add continuous_const)
  have hD_zero : (0 : H) ∈ D := by
    simpa [D, v₀H] using hv₀U
  let K : Submodule Real H := LinearMap.ker (L.domRestrict H)
  have hD_subset : D ⊆ (K : Set H) := by
    intro h hh
    change L (h : E) = 0
    have hvH : (h : E) + v₀ ∈ H := H.add_mem h.property hv₀H
    have hvzero : L ((h : E) + v₀) + b = 0 :=
      hzero ((h : E) + v₀) ⟨hh, hvH⟩
    have hv₀zero : L v₀ + b = 0 := hzero v₀ ⟨hv₀U, hv₀H⟩
    rw [L.map_add] at hvzero
    calc
      L (h : E) = (L (h : E) + L v₀ + b) - (L v₀ + b) := by abel
      _ = 0 := by rw [hvzero, hv₀zero, sub_self]
  have hK_interior : (interior (K : Set H)).Nonempty := by
    have hD_interior : D ⊆ interior (K : Set H) :=
      (IsOpen.subset_interior_iff hD_open).2 hD_subset
    exact ⟨0, hD_interior hD_zero⟩
  have hK_top : K = ⊤ := K.eq_top_of_nonempty_interior' hK_interior
  have hLzero : ∀ v : E, v ∈ H → L v = 0 := by
    intro v hv
    have hvker : (⟨v, hv⟩ : H) ∈ K := by
      rw [hK_top]
      trivial
    exact hvker
  have hb : b = 0 := by
    have := hzero v₀ ⟨hv₀U, hv₀H⟩
    simpa [hLzero v₀ hv₀H] using this
  intro v hv
  simp [hLzero v hv, hb]

/-- Exact `H_w` specialization of the generic affine restriction theorem. -/
theorem affineMatrix_eq_zero_on_multiQuadricSlice_of_relativelyOpen {k d : Nat}
    (A : Fin k → Matrix (Fin d) (Fin d) Real) (w : Fin d → Real)
    (Xi0 : Matrix (Fin d) (Fin d) Real) (b : Fin d → Real)
    {O : Set (Fin d → Real)}
    (hO_rel : RelativelyOpenIn O (multiQuadricSlice A w))
    (hO_nonempty : O.Nonempty)
    (hzero : ∀ v : Fin d → Real, v ∈ O → Xi0 *ᵥ v + b = 0) :
    ∀ v : Fin d → Real, v ∈ multiQuadricSlice A w → Xi0 *ᵥ v + b = 0 := by
  apply affineMap_eq_zero_on_submodule_of_relativelyOpen
    (multiQuadricSliceSubmodule A w) hO_rel hO_nonempty Xi0.mulVecLin b
  intro v hv
  simpa [Matrix.mulVecLin_apply] using hzero v hv

/-! ## Multi-quadric rigidity -/

/-- TeX `lem:multi-quadric-rigidity`, with the slice witness exposed so the
second conclusion can name its open base `W`. -/
theorem multiQuadricRigidity_of_witness {k d : Nat}
    {A : Fin k → Matrix (Fin d) (Fin d) Real}
    {S : Set ((Fin d → Real) × (Fin d → Real))}
    (hS : MultiQuadricSliceWitness A S) (hSQ : S ⊆ multiQuadric A)
    (Xi0 Xi1 : Matrix (Fin d) (Fin d) Real)
    (hidentity : ∀ w v : Fin d → Real, (w, v) ∈ S →
      Xi0 *ᵥ v + Xi1 *ᵥ w = 0) :
    Xi1 = 0 ∧
      ∀ w : Fin d → Real, w ∈ hS.W →
        ∀ v : Fin d → Real, v ∈ multiQuadricSlice A w → Xi0 *ᵥ v = 0 := by
  have hidentityOnQ : ∀ w v : Fin d → Real,
      (w, v) ∈ S → (w, v) ∈ multiQuadric A →
        Xi0 *ᵥ v + Xi1 *ᵥ w = 0 := by
    intro w v hmem _hquadric
    exact hidentity w v hmem
  have hsliceAffine : ∀ w : Fin d → Real, w ∈ hS.W →
      ∀ v : Fin d → Real, v ∈ multiQuadricSlice A w →
        Xi0 *ᵥ v + Xi1 *ᵥ w = 0 := by
    intro w hw
    apply affineMatrix_eq_zero_on_multiQuadricSlice_of_relativelyOpen
      A w Xi0 (Xi1 *ᵥ w) (hS.slice_relativelyOpen w hw)
      (hS.slice_nonempty w hw)
    intro v hv
    have hmem : (w, v) ∈ S := hS.slice_subset w hw ⟨by simp, hv⟩
    exact hidentityOnQ w v hmem (hSQ hmem)
  have hXi1w : ∀ w : Fin d → Real, w ∈ hS.W → Xi1 *ᵥ w = 0 := by
    intro w hw
    have hzero := hsliceAffine w hw 0 (zero_mem_multiQuadricSlice A w)
    simpa using hzero
  have hXi1 : Xi1 = 0 :=
    matrix_eq_zero_of_forall_mulVec_eq_zero_on_open
      hS.W_open hS.W_nonempty hXi1w
  refine ⟨hXi1, ?_⟩
  intro w hw v hv
  have hzero := hsliceAffine w hw v hv
  rw [hXi1w w hw, add_zero] at hzero
  exact hzero

/-- Proposition-packaged form of multi-quadric rigidity.  The existentially
returned witness is the one asserted by `MultiQuadricSliceStructure`; exposing
it is necessary to state the slice-wise conclusion. -/
theorem multiQuadricRigidity {k d : Nat}
    {A : Fin k → Matrix (Fin d) (Fin d) Real}
    {S : Set ((Fin d → Real) × (Fin d → Real))}
    (hS : MultiQuadricSliceStructure A S) (hSQ : S ⊆ multiQuadric A)
    (Xi0 Xi1 : Matrix (Fin d) (Fin d) Real)
    (hidentity : ∀ w v : Fin d → Real, (w, v) ∈ S →
      Xi0 *ᵥ v + Xi1 *ᵥ w = 0) :
    Xi1 = 0 ∧
      ∃ witness : MultiQuadricSliceWitness A S,
        ∀ w : Fin d → Real, w ∈ witness.W →
          ∀ v : Fin d → Real, v ∈ multiQuadricSlice A w → Xi0 *ᵥ v = 0 := by
  rcases hS with ⟨witness⟩
  rcases multiQuadricRigidity_of_witness witness hSQ Xi0 Xi1 hidentity with
    ⟨hXi1, hXi0⟩
  exact ⟨hXi1, witness, hXi0⟩

/-! ## Scalar quadratic identities on a multi-quadric -/

/-- A linear functional annihilating the kernel of a full-row-rank matrix is
in its row span, with explicit Gram coefficients. -/
theorem exists_transpose_mulVec_eq_of_dotProduct_eq_zero_on_kernel
    {k d : Nat} (G : Matrix (Fin k) (Fin d) Real)
    (hdet : (G * Gᵀ).det ≠ 0) (x : Fin d → Real)
    (hann : ∀ v : Fin d → Real, G *ᵥ v = 0 → dotProduct x v = 0) :
    ∃ c : Fin k → Real, x = Gᵀ *ᵥ c := by
  let c : Fin k → Real := (G * Gᵀ)⁻¹ *ᵥ (G *ᵥ x)
  let z : Fin d → Real := x - Gᵀ *ᵥ c
  have hunit : IsUnit (G * Gᵀ).det := isUnit_iff_ne_zero.mpr hdet
  have hGz : G *ᵥ z = 0 := by
    change G *ᵥ (x - Gᵀ *ᵥ c) = 0
    dsimp only [c]
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec, sub_self]
  have hxz : dotProduct x z = 0 := hann z hGz
  have hpz : dotProduct (Gᵀ *ᵥ c) z = 0 := by
    calc
      dotProduct (Gᵀ *ᵥ c) z = dotProduct z (Gᵀ *ᵥ c) := dotProduct_comm _ _
      _ = Matrix.vecMul z Gᵀ ⬝ᵥ c := Matrix.dotProduct_mulVec z Gᵀ c
      _ = dotProduct (G *ᵥ z) c := by rw [Matrix.vecMul_transpose]
      _ = 0 := by rw [hGz, zero_dotProduct]
  have hzz : dotProduct z z = 0 := by
    change dotProduct (x - Gᵀ *ᵥ c) z = 0
    rw [sub_dotProduct, hxz, hpz, sub_zero]
  have hz : z = 0 := dotProduct_self_eq_zero.mp hzz
  refine ⟨c, ?_⟩
  exact sub_eq_zero.mp hz

/-- Pointwise ideal-membership conclusion for a scalar quadratic identity on
an intersection of quadrics.  This is the correct first stage of zero-branch
rigidity: `Xᵀw` lies in the span of the anchor gradients; it is not asserted to
vanish.  The symmetric quadratic coefficient does vanish. -/
theorem multiQuadricQuadraticRigidity_of_witness {k d : Nat}
    {A : Fin k → Matrix (Fin d) (Fin d) Real}
    {S : Set ((Fin d → Real) × (Fin d → Real))}
    (hS : MultiQuadricSliceWitness A S)
    (hgram : ∀ w ∈ hS.W,
      (multiQuadricGradientMatrix A w *
        (multiQuadricGradientMatrix A w)ᵀ).det ≠ 0)
    (X Y : Matrix (Fin d) (Fin d) Real)
    (hidentity : ∀ w v : Fin d → Real, (w, v) ∈ S →
      matrixBilin X w v + matrixBilin Y w w = 0) :
    sym Y = 0 ∧
      ∀ w ∈ hS.W, ∃ c : Fin k → Real,
        Xᵀ *ᵥ w =
          (multiQuadricGradientMatrix A w)ᵀ *ᵥ c := by
  let G : (Fin d → Real) → Matrix (Fin k) (Fin d) Real :=
    multiQuadricGradientMatrix A
  have haffine : ∀ w, w ∈ hS.W → ∀ v,
      v ∈ multiQuadricSlice A w →
        matrixBilin X w v + matrixBilin Y w w = 0 := by
    intro w hw
    let L : (Fin d → Real) →ₗ[Real] Real :=
      { toFun := fun v => matrixBilin X w v
        map_add' := by intro u v; simp [matrixBilin, Matrix.mulVec_add, dotProduct_add]
        map_smul' := by intro c v; simp [matrixBilin, Matrix.mulVec_smul, dotProduct_smul] }
    have hopen := hS.slice_relativelyOpen w hw
    have hne := hS.slice_nonempty w hw
    have hz : ∀ v ∈ hS.slice w, L v + matrixBilin Y w w = 0 := by
      intro v hv
      exact hidentity w v (hS.slice_subset w hw ⟨by simp, hv⟩)
    exact affineMap_eq_zero_on_submodule_of_relativelyOpen
      (multiQuadricSliceSubmodule A w) hopen hne L (matrixBilin Y w w) hz
  have hYquad : ∀ w ∈ hS.W, matrixBilin Y w w = 0 := by
    intro w hw
    have h0 := haffine w hw 0 (zero_mem_multiQuadricSlice A w)
    simpa [matrixBilin] using h0
  refine ⟨KHead.sym_eq_zero_of_forall_matrixBilin_self_eq_zero_on_open
      hS.W_open hS.W_nonempty hYquad, ?_⟩
  intro w hw
  apply exists_transpose_mulVec_eq_of_dotProduct_eq_zero_on_kernel (G w)
    (hgram w hw) (Xᵀ *ᵥ w)
  intro v hGv
  have hv : v ∈ multiQuadricSlice A w := by
    intro a
    have ha := congrFun hGv a
    simpa [G, multiQuadricForm, Matrix.mulVec, dotProduct] using ha
  have hz := haffine w hw v hv
  rw [hYquad w hw, add_zero] at hz
  calc
    dotProduct (Xᵀ *ᵥ w) v = dotProduct v (Xᵀ *ᵥ w) := dotProduct_comm _ _
    _ = dotProduct w (X *ᵥ v) := Matrix.dotProduct_transpose_mulVec X v w
    _ = 0 := hz

end TransformerIdentifiability.NLayer.NoSkip
