import AnyLayerIdentifiabilityProof.NLayer.Analytic.SlopePaths

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer

open Matrix

/-!
# Algebraic and quadric rigidity toolkit

Target contents:
* zero sets of polynomials
* dominant top coefficient and nested largeness
* affine vanishing on hyperplane slices
* slice/projection/parallel rigidity
* quadratic and linear quadric rigidity lemmas

Corresponds to `n_layer_proof.tex`, Section 4.4-4.5.
-/

/-! ## Bilinear endpoint algebra -/

/-- The real matrix bilinear form `w^T A v`, written with mathlib's dot product and
matrix-vector multiplication.

This is the scalar polynomial used in Step 5 of Proposition `A1`. -/
noncomputable def matrixBilin {d : Nat} (A : Matrix (Fin d) (Fin d) ℝ)
    (w v : Fin d -> ℝ) : ℝ :=
  dotProduct w (Matrix.mulVec A v)

/-- The coordinate base for solving one coordinate in a quadric chart. -/
noncomputable abbrev QuadricGraphBase (d : Nat) (i : Fin d) :=
  (Fin d -> ℝ) × ({j : Fin d // j ≠ i} -> ℝ)

/-- Delete one coordinate from a vector. -/
noncomputable def eraseCoord {d : Nat} (i : Fin d)
    (v : Fin d -> ℝ) : {j : Fin d // j ≠ i} -> ℝ :=
  fun j => v j

/-- Insert one displayed coordinate into a vector with that coordinate deleted. -/
noncomputable def insertCoord {d : Nat} (i : Fin d) (x : ℝ)
    (u : {j : Fin d // j ≠ i} -> ℝ) : Fin d -> ℝ :=
  fun j => if h : j = i then x else u ⟨j, h⟩

@[simp] theorem insertCoord_same {d : Nat} (i : Fin d) (x : ℝ)
    (u : {j : Fin d // j ≠ i} -> ℝ) :
    insertCoord i x u i = x := by
  simp [insertCoord]

@[simp] theorem eraseCoord_insertCoord {d : Nat} (i : Fin d) (x : ℝ)
    (u : {j : Fin d // j ≠ i} -> ℝ) :
    eraseCoord i (insertCoord i x u) = u := by
  ext j
  simp [eraseCoord, insertCoord, j.property]

@[simp] theorem insertCoord_eraseCoord {d : Nat} (i : Fin d) (v : Fin d -> ℝ) :
    insertCoord i (v i) (eraseCoord i v) = v := by
  ext j
  by_cases h : j = i
  · subst j
    simp [insertCoord]
  · simp [insertCoord, eraseCoord, h]

/-- The bilinear form can be read as `(transpose A * w) dot v`. -/
theorem matrixBilin_eq_transpose_dot {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (w v : Fin d -> ℝ) :
    matrixBilin A w v = dotProduct (Matrix.mulVec (Matrix.transpose A) w) v := by
  simp only [matrixBilin, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  conv_lhs =>
    arg 2
    intro i
    rw [Finset.mul_sum]
  conv_rhs =>
    arg 2
    intro j
    rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Reinserted vectors differ from the zero-inserted vector by a coordinate vector. -/
theorem insertCoord_eq_zero_add_single {d : Nat} (i : Fin d) (x : ℝ)
    (u : {j : Fin d // j ≠ i} -> ℝ) :
    insertCoord i x u = insertCoord i 0 u + Pi.single i x := by
  ext j
  by_cases h : j = i
  · subst j
    simp [insertCoord]
  · simp [insertCoord, h]

/-- The bilinear form against a right coordinate vector is the corresponding
coordinate of `transpose A * w`. -/
theorem matrixBilin_single_right {d : Nat} (A : Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d -> ℝ) (i : Fin d) (x : ℝ) :
    matrixBilin A w (Pi.single i x) =
      x * ((Matrix.mulVec (Matrix.transpose A) w) i) := by
  rw [matrixBilin_eq_transpose_dot]
  rw [dotProduct_comm, single_dotProduct]

/-- The bilinear form is affine in an inserted right coordinate. -/
theorem matrixBilin_insertCoord {d : Nat} (A : Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d -> ℝ) (i : Fin d) (x : ℝ)
    (u : {j : Fin d // j ≠ i} -> ℝ) :
    matrixBilin A w (insertCoord i x u) =
      matrixBilin A w (insertCoord i 0 u) +
        x * ((Matrix.mulVec (Matrix.transpose A) w) i) := by
  rw [insertCoord_eq_zero_add_single]
  have hadd :
      matrixBilin A w (insertCoord i 0 u + Pi.single i x) =
        matrixBilin A w (insertCoord i 0 u) +
          matrixBilin A w (Pi.single i x) := by
    simp [matrixBilin, Matrix.mulVec_add, dotProduct_add]
  rw [hadd, matrixBilin_single_right]

/-- The zero-displayed-coordinate insertion is affine in every erased coordinate. -/
theorem insertCoord_zero_add_single_erased {d : Nat} (i : Fin d)
    (u : {j : Fin d // j ≠ i} -> ℝ) (e : {j : Fin d // j ≠ i}) (t : ℝ) :
    insertCoord i 0 (u + t • Pi.single e (1 : ℝ)) =
      insertCoord i 0 u + Pi.single e.1 t := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [insertCoord, e.property]
  · by_cases hje : j = e.1
    · subst j
      simp [insertCoord, e.property]
    · have hsub : (⟨j, hji⟩ : {j : Fin d // j ≠ i}) ≠ e := by
        intro h
        exact hje (Subtype.ext_iff.mp h)
      simp [insertCoord, hji, hje, hsub]

/-- The coordinate that solves `w^T A v = 0` when `(transpose A * w)_i ≠ 0`. -/
noncomputable def solvedCoord {d : Nat} (A : Matrix (Fin d) (Fin d) ℝ)
    (i : Fin d) (w : Fin d -> ℝ) (u : {j : Fin d // j ≠ i} -> ℝ) : ℝ :=
  - matrixBilin A w (insertCoord i 0 u) /
    ((Matrix.mulVec (Matrix.transpose A) w) i)

/-- Inserting the solved coordinate lands on the bilinear quadric. -/
theorem matrixBilin_insertCoord_solved {d : Nat} (A : Matrix (Fin d) (Fin d) ℝ)
    {i : Fin d} {w : Fin d -> ℝ} {u : {j : Fin d // j ≠ i} -> ℝ}
    (hcoeff : (Matrix.mulVec (Matrix.transpose A) w) i ≠ 0) :
    matrixBilin A w (insertCoord i (solvedCoord A i w u) u) = 0 := by
  rw [matrixBilin_insertCoord]
  unfold solvedCoord
  field_simp [hcoeff]
  ring

/-- On the quadric, the solved coordinate recovers the original coordinate. -/
theorem solvedCoord_eq_of_quadric {d : Nat} (A : Matrix (Fin d) (Fin d) ℝ)
    {i : Fin d} {w v : Fin d -> ℝ}
    (hcoeff : (Matrix.mulVec (Matrix.transpose A) w) i ≠ 0)
    (hquad : matrixBilin A w v = 0) :
    solvedCoord A i w (eraseCoord i v) = v i := by
  have hquad' :
      matrixBilin A w (insertCoord i (v i) (eraseCoord i v)) = 0 := by
    simpa using hquad
  rw [matrixBilin_insertCoord] at hquad'
  unfold solvedCoord
  field_simp [hcoeff]
  linarith

/-- The probe obtained by solving the displayed right coordinate in a bilinear
quadric chart. -/
noncomputable def solvedCoordProbe {d : Nat} (A : Matrix (Fin d) (Fin d) ℝ)
    (i : Fin d) (x : QuadricGraphBase d i) : (Fin d -> ℝ) × (Fin d -> ℝ) :=
  (x.1, insertCoord i (solvedCoord A i x.1 x.2) x.2)

/-- Solving the displayed coordinate is affine in each erased right coordinate. -/
theorem solvedCoord_add_single_erased {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) {i : Fin d}
    {w : Fin d -> ℝ} {u : {j : Fin d // j ≠ i} -> ℝ}
    (e : {j : Fin d // j ≠ i}) (t : ℝ)
    (hcoeff : (Matrix.mulVec (Matrix.transpose A) w) i ≠ 0) :
    solvedCoord A i w (u + t • Pi.single e (1 : ℝ)) =
      solvedCoord A i w u -
        t * (Matrix.mulVec (Matrix.transpose A) w) e.1 /
          (Matrix.mulVec (Matrix.transpose A) w) i := by
  rw [solvedCoord, solvedCoord, insertCoord_zero_add_single_erased]
  rw [show matrixBilin A w (insertCoord i 0 u + Pi.single e.1 t) =
      matrixBilin A w (insertCoord i 0 u) +
        matrixBilin A w (Pi.single e.1 t) by
        simp [matrixBilin, Matrix.mulVec_add, dotProduct_add]]
  rw [matrixBilin_single_right]
  field_simp [hcoeff]
  ring

/-- Dot product with a solved-coordinate probe after varying one erased coordinate. -/
theorem dotProduct_solvedCoordProbe_add_single_erased {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) {i : Fin d}
    {w : Fin d -> ℝ} {u : {j : Fin d // j ≠ i} -> ℝ}
    (m : Fin d -> ℝ) (e : {j : Fin d // j ≠ i}) (t : ℝ)
    (hcoeff : (Matrix.mulVec (Matrix.transpose A) w) i ≠ 0) :
    dotProduct m (solvedCoordProbe A i (w, u + t • Pi.single e (1 : ℝ))).2 =
      dotProduct m (solvedCoordProbe A i (w, u)).2 +
        t * (m e.1 -
          m i * (Matrix.mulVec (Matrix.transpose A) w) e.1 /
            (Matrix.mulVec (Matrix.transpose A) w) i) := by
  simp only [solvedCoordProbe]
  rw [insertCoord_eq_zero_add_single, insertCoord_eq_zero_add_single]
  rw [insertCoord_zero_add_single_erased]
  rw [dotProduct_add, dotProduct_add, dotProduct_add]
  rw [solvedCoord_add_single_erased A e t hcoeff]
  have hdot_insert :
      dotProduct m (insertCoord i (solvedCoord A i w u) u) =
        dotProduct m (insertCoord i 0 u) + m i * solvedCoord A i w u := by
    rw [insertCoord_eq_zero_add_single]
    rw [dotProduct_add]
    simp
  rw [hdot_insert]
  have hdot_single : ∀ a : Fin d, ∀ x : ℝ,
      dotProduct m (Pi.single a x) = m a * x := by
    intro a x
    rw [dotProduct_comm, single_dotProduct]
    ring
  simp [hdot_single]
  ring_nf

/-- Solved-coordinate chart probes lie on the bilinear quadric whenever the displayed
coefficient is nonzero. -/
theorem matrixBilin_solvedCoordProbe {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) {i : Fin d} {x : QuadricGraphBase d i}
    (hcoeff : (Matrix.mulVec (Matrix.transpose A) x.1) i ≠ 0) :
    matrixBilin A (solvedCoordProbe A i x).1 (solvedCoordProbe A i x).2 = 0 := by
  exact matrixBilin_insertCoord_solved (A := A) (i := i) (w := x.1) (u := x.2)
    hcoeff

/-- On the quadric, the solved-coordinate probe recovers the original probe after
deleting the displayed coordinate. -/
theorem solvedCoordProbe_eq_of_quadric {d : Nat} (A : Matrix (Fin d) (Fin d) ℝ)
    {i : Fin d} {w v : Fin d -> ℝ}
    (hcoeff : (Matrix.mulVec (Matrix.transpose A) w) i ≠ 0)
    (hquad : matrixBilin A w v = 0) :
    solvedCoordProbe A i (w, eraseCoord i v) = (w, v) := by
  ext j
  · rfl
  · simp [solvedCoordProbe, solvedCoord_eq_of_quadric A hcoeff hquad]

/-- A square matrix with nonzero determinant has trivial kernel for `mulVec`. -/
theorem matrix_mulVec_eq_zero_of_det_ne_zero {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (hdet : A.det ≠ 0)
    {x : Fin d -> ℝ} (hAx : Matrix.mulVec A x = 0) :
    x = 0 := by
  have hmul : Matrix.mulVec (A.adjugate * A) x = 0 := by
    rw [← Matrix.mulVec_mulVec, hAx]
    simp
  have hdetx : Matrix.mulVec (A.det • (1 : Matrix (Fin d) (Fin d) ℝ)) x = 0 := by
    simpa [Matrix.adjugate_mul] using hmul
  have hdetx' : A.det • x = 0 := by
    simpa [Matrix.smul_mulVec, Matrix.one_mulVec] using hdetx
  ext i
  have hi := congrFun hdetx' i
  have hdet_mul : A.det * x i = 0 := by
    simpa [Pi.smul_apply, smul_eq_mul] using hi
  exact (mul_eq_zero.mp hdet_mul).resolve_left hdet

/-- The transpose of a matrix with nonzero determinant also has trivial `mulVec`
kernel. -/
theorem transpose_mulVec_eq_zero_of_det_ne_zero {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (hdet : A.det ≠ 0)
    {x : Fin d -> ℝ} (hAx : Matrix.mulVec (Matrix.transpose A) x = 0) :
    x = 0 := by
  exact matrix_mulVec_eq_zero_of_det_ne_zero (Matrix.transpose A)
    (by simpa using hdet) hAx

/-- For a nonsingular matrix, every nonzero left vector has a nonzero solved-coordinate
coefficient in some coordinate. -/
theorem exists_transpose_mulVec_ne_zero_coord_of_ne_zero {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (hdet : A.det ≠ 0)
    {w : Fin d -> ℝ} (hw : w ≠ 0) :
    ∃ i : Fin d, (Matrix.mulVec (Matrix.transpose A) w) i ≠ 0 := by
  classical
  by_contra h
  apply hw
  apply transpose_mulVec_eq_zero_of_det_ne_zero A hdet
  ext i
  exact by_contra fun hi => h ⟨i, hi⟩

/-- In dimension at least two, every vector has a nonzero orthogonal vector for the
standard dot product. -/
theorem exists_ne_zero_dotProduct_eq_zero_of_two_le {d : Nat}
    (hd : 2 ≤ d) (y : Fin d -> ℝ) :
    ∃ w : Fin d -> ℝ, w ≠ 0 ∧ dotProduct w y = 0 := by
  classical
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr hd
  by_cases hy : y = 0
  · rcases exists_pair_ne (Fin d) with ⟨a, _b, _hab⟩
    refine ⟨Pi.single a (1 : ℝ), ?_, ?_⟩
    · intro hzero
      have ha := congrFun hzero a
      simpa using ha
    · simp [hy, dotProduct]
  · have hycoord : ∃ a : Fin d, y a ≠ 0 := by
      by_contra h
      apply hy
      ext a
      exact by_contra fun ha => h ⟨a, ha⟩
    rcases hycoord with ⟨a, ha⟩
    rcases exists_ne a with ⟨b, hba⟩
    refine ⟨Pi.single a (y b) - Pi.single b (y a), ?_, ?_⟩
    · intro hzero
      have hb := congrFun hzero b
      rw [Pi.sub_apply, Pi.single_eq_of_ne hba, Pi.single_eq_same, zero_sub] at hb
      exact ha (neg_eq_zero.mp hb)
    · rw [sub_dotProduct, single_dotProduct, single_dotProduct]
      ring

/-- A real matrix whose quadratic form vanishes identically has zero symmetric part. -/
theorem matrix_symPart_eq_zero_of_forall_quadratic_eq_zero {d : Nat}
    {Y : Matrix (Fin d) (Fin d) ℝ}
    (h : ∀ w : Fin d -> ℝ, w ⬝ᵥ (Y *ᵥ w) = 0) :
    Y + Yᵀ = 0 := by
  ext i j
  simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.zero_apply]
  have hii := h (Pi.single i (1 : ℝ))
  have hjj := h (Pi.single j (1 : ℝ))
  have hij := h (Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ))
  rw [Matrix.mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply] at hii
  rw [Matrix.mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply] at hjj
  simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add] at hij
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one,
    single_dotProduct, single_dotProduct, single_dotProduct, single_dotProduct,
    one_mul, one_mul, Matrix.col_apply, Matrix.col_apply] at hij
  simp only [Matrix.col_apply] at hij
  linarith

/-- A homogeneous quadratic form vanishing on a nonempty open set vanishes
everywhere.  The proof evaluates the form at `w0 + t z` and `w0 - t z` inside the
open set and cancels the affine and mixed terms. -/
theorem quadratic_eq_zero_of_forall_mem_open {d : Nat}
    {W : Set (Fin d -> ℝ)} (hW_open : IsOpen W) (hW_nonempty : W.Nonempty)
    {Y : Matrix (Fin d) (Fin d) ℝ}
    (hzero : ∀ w : Fin d -> ℝ, w ∈ W -> w ⬝ᵥ (Y *ᵥ w) = 0) :
    ∀ z : Fin d -> ℝ, z ⬝ᵥ (Y *ᵥ z) = 0 := by
  rcases hW_nonempty with ⟨w0, hw0⟩
  intro z
  have hplus_event :
      ∀ᶠ t in nhds (0 : ℝ), w0 + t • z ∈ W := by
    have hcont : ContinuousAt (fun t : ℝ => w0 + t • z) 0 := by
      exact continuous_const.continuousAt.add
        (continuous_id.smul continuous_const).continuousAt
    exact hcont.preimage_mem_nhds (by simpa using hW_open.mem_nhds hw0)
  have hminus_event :
      ∀ᶠ t in nhds (0 : ℝ), w0 - t • z ∈ W := by
    have hcont : ContinuousAt (fun t : ℝ => w0 - t • z) 0 := by
      exact continuous_const.continuousAt.sub
        (continuous_id.smul continuous_const).continuousAt
    exact hcont.preimage_mem_nhds (by simpa using hW_open.mem_nhds hw0)
  have hne_freq : ∃ᶠ t in nhds (0 : ℝ), t ≠ 0 :=
    (frequently_lt_nhds (0 : ℝ)).mono fun t ht => ne_of_lt ht
  rcases (hne_freq.and_eventually (hplus_event.and hminus_event)).exists with
    ⟨t, ht_ne, htplus, htminus⟩
  have h0 := hzero w0 hw0
  have hp := hzero (w0 + t • z) htplus
  have hm := hzero (w0 - t • z) htminus
  have htz : t ^ 2 * (z ⬝ᵥ (Y *ᵥ z)) = 0 := by
    simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul,
      dotProduct_add, dotProduct_sub, add_dotProduct, sub_dotProduct,
      dotProduct_smul, smul_dotProduct, smul_eq_mul] at hp hm
    ring_nf at hp hm ⊢
    nlinarith
  exact (mul_eq_zero.mp htz).resolve_left (pow_ne_zero 2 ht_ne)

/-- Open-set version of `matrix_symPart_eq_zero_of_forall_quadratic_eq_zero`. -/
theorem matrix_symPart_eq_zero_of_forall_quadratic_eq_zero_on_open {d : Nat}
    {W : Set (Fin d -> ℝ)} (hW_open : IsOpen W) (hW_nonempty : W.Nonempty)
    {Y : Matrix (Fin d) (Fin d) ℝ}
    (hzero : ∀ w : Fin d -> ℝ, w ∈ W -> w ⬝ᵥ (Y *ᵥ w) = 0) :
    Y + Yᵀ = 0 :=
  matrix_symPart_eq_zero_of_forall_quadratic_eq_zero
    (quadratic_eq_zero_of_forall_mem_open hW_open hW_nonempty hzero)

/-- A coordinate wedge of two linear forms is a homogeneous quadratic identity; if it
vanishes on a nonempty open set, it vanishes everywhere. -/
theorem dotProduct_mul_coord_sub_dotProduct_mul_coord_eq_zero_of_forall_mem_open
    {d : Nat} {W : Set (Fin d -> ℝ)} (hW_open : IsOpen W)
    (hW_nonempty : W.Nonempty) {r s : Fin d -> ℝ} {i j : Fin d}
    (hzero : ∀ z : Fin d -> ℝ, z ∈ W ->
      dotProduct r z * z j - dotProduct s z * z i = 0) :
    ∀ z : Fin d -> ℝ, dotProduct r z * z j - dotProduct s z * z i = 0 := by
  rcases hW_nonempty with ⟨z0, hz0⟩
  intro z
  have hplus_event :
      ∀ᶠ t in nhds (0 : ℝ), z0 + t • z ∈ W := by
    have hcont : ContinuousAt (fun t : ℝ => z0 + t • z) 0 := by
      exact continuous_const.continuousAt.add
        (continuous_id.smul continuous_const).continuousAt
    exact hcont.preimage_mem_nhds (by simpa using hW_open.mem_nhds hz0)
  have hminus_event :
      ∀ᶠ t in nhds (0 : ℝ), z0 - t • z ∈ W := by
    have hcont : ContinuousAt (fun t : ℝ => z0 - t • z) 0 := by
      exact continuous_const.continuousAt.sub
        (continuous_id.smul continuous_const).continuousAt
    exact hcont.preimage_mem_nhds (by simpa using hW_open.mem_nhds hz0)
  have hne_freq : ∃ᶠ t in nhds (0 : ℝ), t ≠ 0 :=
    (frequently_lt_nhds (0 : ℝ)).mono fun t ht => ne_of_lt ht
  rcases (hne_freq.and_eventually (hplus_event.and hminus_event)).exists with
    ⟨t, ht_ne, htplus, htminus⟩
  have h0 := hzero z0 hz0
  have hp := hzero (z0 + t • z) htplus
  have hm := hzero (z0 - t • z) htminus
  have htz :
      t ^ 2 * (dotProduct r z * z j - dotProduct s z * z i) = 0 := by
    simp only [dotProduct_add, dotProduct_sub, dotProduct_smul, Pi.add_apply,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hp hm
    ring_nf at hp hm ⊢
    nlinarith
  exact (mul_eq_zero.mp htz).resolve_left (pow_ne_zero 2 ht_ne)

/-- A matrix that sends every vector to a scalar multiple of itself is scalar, in
dimension at least two. -/
theorem matrix_eq_smul_one_of_forall_mulVec_eq_smul_self {d : Nat}
    (hd : 2 ≤ d) (M : Matrix (Fin d) (Fin d) ℝ)
    (hM : ∀ z : Fin d -> ℝ, ∃ c : ℝ, M *ᵥ z = c • z) :
    ∃ c : ℝ, M = c • (1 : Matrix (Fin d) (Fin d) ℝ) := by
  classical
  have hdpos : 0 < d := Nat.lt_of_lt_of_le (by norm_num) hd
  let base : Fin d := ⟨0, hdpos⟩
  let colScale : Fin d -> ℝ := fun j => (M *ᵥ Pi.single j (1 : ℝ)) j
  have hcol :
      ∀ j : Fin d, M *ᵥ Pi.single j (1 : ℝ) =
        colScale j • Pi.single j (1 : ℝ) := by
    intro j
    rcases hM (Pi.single j (1 : ℝ)) with ⟨c, hc⟩
    ext i
    by_cases hij : i = j
    · subst i
      simp [colScale]
    · have hi := congrFun hc i
      simp [hij] at hi ⊢
      exact hi
  have hscale_eq : ∀ j : Fin d, colScale j = colScale base := by
    intro j
    by_cases hj : j = base
    · subst j
      rfl
    · rcases hM (Pi.single base (1 : ℝ) + Pi.single j (1 : ℝ)) with ⟨c, hc⟩
      have hbase := congrFun hc base
      have hjcoord := congrFun hc j
      rw [Matrix.mulVec_add, hcol base, hcol j] at hbase hjcoord
      simp [colScale, hj, Ne.symm hj] at hbase hjcoord
      change (M *ᵥ Pi.single j (1 : ℝ)) j =
        (M *ᵥ Pi.single base (1 : ℝ)) base
      simpa using hjcoord.trans hbase.symm
  refine ⟨colScale base, ?_⟩
  ext i j
  have hentry := congrFun (hcol j) i
  rw [hscale_eq j] at hentry
  by_cases hij : i = j
  · subst i
    simpa [colScale] using hentry
  · have hzero : M i j = 0 := by
      simpa [colScale, hij] using hentry
    simpa [Matrix.one_apply, hij] using hzero

/-- If a matrix sends every vector in a nonempty open set to a scalar multiple of that
vector, then the matrix is scalar. -/
theorem matrix_eq_smul_one_of_forall_mulVec_eq_smul_self_on_open {d : Nat}
    (hd : 2 ≤ d) {W : Set (Fin d -> ℝ)} (hW_open : IsOpen W)
    (hW_nonempty : W.Nonempty) (M : Matrix (Fin d) (Fin d) ℝ)
    (hM : ∀ z : Fin d -> ℝ, z ∈ W -> ∃ c : ℝ, M *ᵥ z = c • z) :
    ∃ c : ℝ, M = c • (1 : Matrix (Fin d) (Fin d) ℝ) := by
  classical
  have hwedge : ∀ i j : Fin d, ∀ z : Fin d -> ℝ,
      dotProduct (fun k => M i k) z * z j -
        dotProduct (fun k => M j k) z * z i = 0 := by
    intro i j
    exact
      dotProduct_mul_coord_sub_dotProduct_mul_coord_eq_zero_of_forall_mem_open
        hW_open hW_nonempty (i := i) (j := j) (by
          intro z hz
          rcases hM z hz with ⟨c, hc⟩
          have hi := congrFun hc i
          have hj := congrFun hc j
          simp [Matrix.mulVec, Pi.smul_apply] at hi hj
          rw [hi, hj]
          ring)
  have hM_global : ∀ z : Fin d -> ℝ, ∃ c : ℝ, M *ᵥ z = c • z := by
    intro z
    by_cases hz : z = 0
    · refine ⟨0, ?_⟩
      simp [hz]
    · have hcoord : ∃ k : Fin d, z k ≠ 0 := by
        by_contra hzero
        apply hz
        ext k
        exact by_contra fun hk => hzero ⟨k, hk⟩
      rcases hcoord with ⟨k, hk⟩
      refine ⟨(M *ᵥ z) k / z k, ?_⟩
      ext i
      by_cases hik : i = k
      · subst i
        simp [Pi.smul_apply]
        field_simp [hk]
      · have hwed := hwedge i k z
        change (M *ᵥ z) i * z k - (M *ᵥ z) k * z i = 0 at hwed
        rw [Pi.smul_apply]
        change (M *ᵥ z) i = ((M *ᵥ z) k / z k) * z i
        field_simp [hk]
        nlinarith [hwed]
  exact matrix_eq_smul_one_of_forall_mulVec_eq_smul_self hd M hM_global

/-- Open-set parallel-rigidity with an invertible target matrix. -/
theorem matrix_eq_smul_of_forall_mulVec_eq_smul_on_open {d : Nat}
    (hd : 2 ≤ d) {W : Set (Fin d -> ℝ)} (hW_open : IsOpen W)
    (hW_nonempty : W.Nonempty) {M N : Matrix (Fin d) (Fin d) ℝ}
    (hdetN : N.det ≠ 0)
    (hMN : ∀ w : Fin d -> ℝ, w ∈ W -> ∃ c : ℝ, M *ᵥ w = c • (N *ᵥ w)) :
    ∃ c : ℝ, M = c • N := by
  classical
  let P : Matrix (Fin d) (Fin d) ℝ := M * N⁻¹
  let V : Set (Fin d -> ℝ) := {z | N⁻¹ *ᵥ z ∈ W}
  have hinv_cont : Continuous fun z : Fin d -> ℝ => N⁻¹ *ᵥ z := by
    rw [continuous_pi_iff]
    intro i
    simpa [Matrix.mulVec, dotProduct] using
      (continuous_finsetSum Finset.univ fun j _ =>
        continuous_const.mul (continuous_apply j))
  have hV_open : IsOpen V := hW_open.preimage hinv_cont
  have hV_nonempty : V.Nonempty := by
    rcases hW_nonempty with ⟨w0, hw0⟩
    refine ⟨N *ᵥ w0, ?_⟩
    have hleft : N⁻¹ *ᵥ (N *ᵥ w0) = w0 := by
      have hmul : (N⁻¹ * N) *ᵥ w0 = w0 := by
        rw [Matrix.nonsing_inv_mul N (Ne.isUnit hdetN), Matrix.one_mulVec]
      simpa [Matrix.mulVec_mulVec] using hmul
    simpa [V, hleft] using hw0
  have hP : ∀ z : Fin d -> ℝ, z ∈ V -> ∃ c : ℝ, P *ᵥ z = c • z := by
    intro z hz
    rcases hMN (N⁻¹ *ᵥ z) hz with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have hright : N *ᵥ (N⁻¹ *ᵥ z) = z := by
      have hmul : (N * N⁻¹) *ᵥ z = z := by
        rw [Matrix.mul_nonsing_inv N (Ne.isUnit hdetN), Matrix.one_mulVec]
      simpa [Matrix.mulVec_mulVec] using hmul
    simpa [P, Matrix.mulVec_mulVec, hright] using hc
  rcases matrix_eq_smul_one_of_forall_mulVec_eq_smul_self_on_open
      hd hV_open hV_nonempty P hP with
    ⟨c, hPscalar⟩
  refine ⟨c, ?_⟩
  have hmul := congrArg (fun Q : Matrix (Fin d) (Fin d) ℝ => Q * N) hPscalar
  simpa [P, Matrix.mul_assoc, Matrix.nonsing_inv_mul N (Ne.isUnit hdetN)] using hmul

/-- A reduced solved-coordinate chart witness that separates scalar linear forms on a
selected subset of the bilinear quadric.

The hard geometry/topology is deliberately external: callers must supply a base of
chart parameters mapping into the selected slice and prove that vanishing on that
chart base forces both linear coefficient vectors to be zero. -/
structure SolvedCoordChartLinearFormSeparationData {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ)
    (Uq : Set ((Fin d -> ℝ) × (Fin d -> ℝ))) : Type where
  pivot : Fin d
  base : Set (QuadricGraphBase d pivot)
  coeff_ne :
    ∀ x : QuadricGraphBase d pivot, x ∈ base ->
      (Matrix.mulVec (Matrix.transpose A) x.1) pivot ≠ 0
  mapsTo :
    ∀ x : QuadricGraphBase d pivot, x ∈ base ->
      solvedCoordProbe A pivot x ∈ Uq
  separates :
    ∀ m r : Fin d -> ℝ,
      (∀ x : QuadricGraphBase d pivot, x ∈ base ->
        dotProduct m (solvedCoordProbe A pivot x).2 +
          dotProduct r (solvedCoordProbe A pivot x).1 = 0) ->
      m = 0 ∧ r = 0

namespace SolvedCoordChartLinearFormSeparationData

variable {d : Nat} {A : Matrix (Fin d) (Fin d) ℝ}
variable {Uq : Set ((Fin d -> ℝ) × (Fin d -> ℝ))}

/-- Constructor form for solved-coordinate chart data from an already separated
parameter base.  This is the reusable assembly step once the local open chart and its
scalar separation theorem have been proved. -/
def ofBase {pivot : Fin d} {B : Set (QuadricGraphBase d pivot)}
    (hcoeff :
      ∀ x : QuadricGraphBase d pivot, x ∈ B ->
        (Matrix.mulVec (Matrix.transpose A) x.1) pivot ≠ 0)
    (hmaps :
      ∀ x : QuadricGraphBase d pivot, x ∈ B ->
        solvedCoordProbe A pivot x ∈ Uq)
    (hseparates :
      ∀ m r : Fin d -> ℝ,
        (∀ x : QuadricGraphBase d pivot, x ∈ B ->
          dotProduct m (solvedCoordProbe A pivot x).2 +
            dotProduct r (solvedCoordProbe A pivot x).1 = 0) ->
        m = 0 ∧ r = 0) :
    SolvedCoordChartLinearFormSeparationData A Uq where
  pivot := pivot
  base := B
  coeff_ne := hcoeff
  mapsTo := hmaps
  separates := hseparates

/-- Compile a solved-coordinate chart separation witness into scalar no-linear
separation on the selected quadric slice. -/
theorem linearForm_eq_zero
    (D : SolvedCoordChartLinearFormSeparationData A Uq)
    {m r : Fin d -> ℝ}
    (hvanish :
      ∀ p : (Fin d -> ℝ) × (Fin d -> ℝ), p ∈ Uq ->
        dotProduct m p.2 + dotProduct r p.1 = 0) :
    m = 0 ∧ r = 0 :=
  D.separates m r fun x hx => hvanish (solvedCoordProbe A D.pivot x)
    (D.mapsTo x hx)

end SolvedCoordChartLinearFormSeparationData

/-- The bilinear form of a matrix difference is the difference of bilinear forms. -/
theorem matrixBilin_sub {d : Nat} (A A' : Matrix (Fin d) (Fin d) ℝ)
    (w v : Fin d -> ℝ) :
    matrixBilin (A - A') w v = matrixBilin A w v - matrixBilin A' w v := by
  simp [matrixBilin, Matrix.sub_mulVec, dotProduct_sub]

/-- Pointwise bilinear equality is equivalent to vanishing of the bilinear form of the
matrix difference. -/
theorem matrixBilin_eq_iff_sub_eq_zero {d : Nat} (A A' : Matrix (Fin d) (Fin d) ℝ)
    (w v : Fin d -> ℝ) :
    matrixBilin A w v = matrixBilin A' w v ↔ matrixBilin (A - A') w v = 0 := by
  rw [matrixBilin_sub, sub_eq_zero]

/-- Testing the bilinear form on coordinate vectors reads off a matrix entry. -/
theorem matrixBilin_single_single {d : Nat} (A : Matrix (Fin d) (Fin d) ℝ)
    (i j : Fin d) :
    matrixBilin A (Pi.single i 1) (Pi.single j 1) = A i j := by
  classical
  simp [matrixBilin]

/-- If two matrices have the same bilinear form on all coordinate probes, they are equal.

This is the final basis-vector evaluation in Step 5 of Proposition `A1`. -/
theorem matrix_eq_of_basis_bilin_eq {d : Nat}
    {A A' : Matrix (Fin d) (Fin d) ℝ}
    (h : ∀ i j : Fin d,
      matrixBilin A (Pi.single i 1) (Pi.single j 1) =
        matrixBilin A' (Pi.single i 1) (Pi.single j 1)) :
    A = A' := by
  ext i j
  simpa [matrixBilin_single_single] using h i j

/-- If two matrices have the same bilinear form on all probes, they are equal. -/
theorem matrix_eq_of_forall_bilin_eq {d : Nat}
    {A A' : Matrix (Fin d) (Fin d) ℝ}
    (h : ∀ w v : Fin d -> ℝ, matrixBilin A w v = matrixBilin A' w v) :
    A = A' :=
  matrix_eq_of_basis_bilin_eq fun i j => h (Pi.single i 1) (Pi.single j 1)

/-- Vanishing of the difference bilinear form on all probes identifies the matrix. -/
theorem matrix_eq_of_forall_bilin_sub_eq_zero {d : Nat}
    {A A' : Matrix (Fin d) (Fin d) ℝ}
    (h : ∀ w v : Fin d -> ℝ, matrixBilin (A - A') w v = 0) :
    A = A' := by
  apply matrix_eq_of_forall_bilin_eq
  intro w v
  have hsub := h w v
  exact (matrixBilin_eq_iff_sub_eq_zero A A' w v).mpr hsub

/-- Constructor package for bilinear equality of two matrices. -/
structure MatrixBilinearEqualityData {d : Nat}
    (A A' : Matrix (Fin d) (Fin d) ℝ) : Prop where
  bilin_eq : ∀ w v : Fin d -> ℝ, matrixBilin A w v = matrixBilin A' w v

namespace MatrixBilinearEqualityData

variable {d : Nat} {A A' : Matrix (Fin d) (Fin d) ℝ}

/-- Compile packaged bilinear equality to matrix equality. -/
theorem matrix_eq (D : MatrixBilinearEqualityData A A') :
    A = A' :=
  matrix_eq_of_forall_bilin_eq D.bilin_eq

end MatrixBilinearEqualityData

/-- Constructor package for the difference-form bilinear endpoint. -/
structure MatrixBilinearSubZeroData {d : Nat}
    (A A' : Matrix (Fin d) (Fin d) ℝ) : Prop where
  bilin_sub_eq_zero : ∀ w v : Fin d -> ℝ, matrixBilin (A - A') w v = 0

namespace MatrixBilinearSubZeroData

variable {d : Nat} {A A' : Matrix (Fin d) (Fin d) ℝ}

/-- Compile packaged difference-form bilinear vanishing to matrix equality. -/
theorem matrix_eq (D : MatrixBilinearSubZeroData A A') :
    A = A' :=
  matrix_eq_of_forall_bilin_sub_eq_zero D.bilin_sub_eq_zero

end MatrixBilinearSubZeroData

/-! ## One-step largeness estimate -/

/-- A one-variable tail presentation
`lead x * z^D + sum_{i<D} lower_i x * z^i`.

This evaluator is the local algebraic shape used in Lemma `nested`, Step 2, after viewing
a multivariate polynomial as a polynomial in its last variable over the previous
variables. -/
noncomputable def tailPolynomial {α : Type*} (D : Nat)
    (lead : α -> ℂ) (lower : Fin D -> α -> ℂ) (x : α) (z : ℂ) : ℂ :=
  lead x * z ^ D + ∑ i : Fin D, lower i x * z ^ (i : Nat)

/-- The continuous threshold from Lemma `nested`, Step 2, in evaluator form. -/
noncomputable def tailThreshold {α : Type*} (D : Nat)
    (lead : α -> ℂ) (lower : Fin D -> α -> ℂ) (x : α) : ℝ :=
  1 + ∑ i : Fin D, ‖lower i x‖ / ‖lead x‖

/-- The explicit largeness threshold is positive where the leading coefficient is nonzero. -/
theorem tailThreshold_pos {α : Type*} {D : Nat}
    {lead : α -> ℂ} {lower : Fin D -> α -> ℂ} {x : α}
    (hlead : lead x ≠ 0) :
    0 < tailThreshold D lead lower x := by
  have hlead_norm_pos : 0 < ‖lead x‖ := norm_pos_iff.mpr hlead
  have hsum_nonneg : 0 ≤ ∑ i : Fin D, ‖lower i x‖ / ‖lead x‖ := by
    exact Finset.sum_nonneg fun i _ => div_nonneg (norm_nonneg _) hlead_norm_pos.le
  unfold tailThreshold
  linarith

/-- If the leading term has strictly larger norm than the whole lower-order tail, then
the tail presentation cannot vanish.

This is the final inequality step inside Lemma `nested`, Step 2. -/
theorem tailPolynomial_ne_zero_of_norm_tail_lt {α : Type*} {D : Nat}
    {lead : α -> ℂ} {lower : Fin D -> α -> ℂ} {x : α} {z : ℂ}
    (hdom : ‖∑ i : Fin D, lower i x * z ^ (i : Nat)‖ < ‖lead x * z ^ D‖) :
    tailPolynomial D lead lower x z ≠ 0 := by
  intro hzero
  have hlead_eq :
      lead x * z ^ D = -(∑ i : Fin D, lower i x * z ^ (i : Nat)) := by
    exact eq_neg_of_add_eq_zero_left (by simpa [tailPolynomial] using hzero)
  have hnorm_eq :
      ‖lead x * z ^ D‖ = ‖∑ i : Fin D, lower i x * z ^ (i : Nat)‖ := by
    rw [hlead_eq, norm_neg]
  linarith

/-- The explicit threshold from Lemma `nested`, Step 2, makes the leading term dominate
the lower-order tail. -/
theorem norm_tail_lt_leading_norm_of_tailThreshold {α : Type*} {D : Nat}
    {lead : α -> ℂ} {lower : Fin D -> α -> ℂ} {x : α} {z : ℂ}
    (hD : 0 < D)
    (hlead : lead x ≠ 0)
    (hlarge : tailThreshold D lead lower x < ‖z‖) :
    ‖∑ i : Fin D, lower i x * z ^ (i : Nat)‖ < ‖lead x * z ^ D‖ := by
  have hlead_norm_pos : 0 < ‖lead x‖ := norm_pos_iff.mpr hlead
  have hsum_div_nonneg : 0 ≤ ∑ i : Fin D, ‖lower i x‖ / ‖lead x‖ := by
    exact Finset.sum_nonneg fun i _ => div_nonneg (norm_nonneg _) hlead_norm_pos.le
  have hsum_div_lt : (∑ i : Fin D, ‖lower i x‖ / ‖lead x‖) < ‖z‖ := by
    have hle : (∑ i : Fin D, ‖lower i x‖ / ‖lead x‖) ≤
        1 + ∑ i : Fin D, ‖lower i x‖ / ‖lead x‖ := by
      linarith
    exact lt_of_le_of_lt hle (by simpa [tailThreshold] using hlarge)
  have hr_gt_one : 1 < ‖z‖ := by
    have hle : 1 ≤ 1 + ∑ i : Fin D, ‖lower i x‖ / ‖lead x‖ := by
      linarith
    exact lt_of_le_of_lt hle (by simpa [tailThreshold] using hlarge)
  have hr_pos : 0 < ‖z‖ := lt_trans zero_lt_one hr_gt_one
  have hr_ge_one : 1 ≤ ‖z‖ := le_of_lt hr_gt_one
  have hsum_div_mul :
      (∑ i : Fin D, ‖lower i x‖ / ‖lead x‖) * ‖lead x‖ =
        ∑ i : Fin D, ‖lower i x‖ := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    exact div_mul_cancel₀ _ hlead_norm_pos.ne'
  have hsum_lt : (∑ i : Fin D, ‖lower i x‖) < ‖lead x‖ * ‖z‖ := by
    have hmul := mul_lt_mul_of_pos_right hsum_div_lt hlead_norm_pos
    rw [hsum_div_mul] at hmul
    simpa [mul_comm] using hmul
  have htail_le :
      ‖∑ i : Fin D, lower i x * z ^ (i : Nat)‖ ≤
        (∑ i : Fin D, ‖lower i x‖) * ‖z‖ ^ (D - 1) := by
    calc
      ‖∑ i : Fin D, lower i x * z ^ (i : Nat)‖
          ≤ ∑ i : Fin D, ‖lower i x * z ^ (i : Nat)‖ := norm_sum_le _ _
      _ = ∑ i : Fin D, ‖lower i x‖ * ‖z‖ ^ (i : Nat) := by
            simp [norm_pow]
      _ ≤ ∑ i : Fin D, ‖lower i x‖ * ‖z‖ ^ (D - 1) := by
            refine Finset.sum_le_sum ?_
            intro i _hi
            have hpow : ‖z‖ ^ (i : Nat) ≤ ‖z‖ ^ (D - 1) :=
              pow_le_pow_right₀ hr_ge_one (by omega)
            exact mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
      _ = (∑ i : Fin D, ‖lower i x‖) * ‖z‖ ^ (D - 1) := by
            rw [Finset.sum_mul]
  have hpow_pos : 0 < ‖z‖ ^ (D - 1) := pow_pos hr_pos _
  have hpow_succ : ‖z‖ * ‖z‖ ^ (D - 1) = ‖z‖ ^ D := by
    rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hD]
  have htail_bound_lt :
      (∑ i : Fin D, ‖lower i x‖) * ‖z‖ ^ (D - 1) <
        ‖lead x‖ * ‖z‖ ^ D := by
    calc
      (∑ i : Fin D, ‖lower i x‖) * ‖z‖ ^ (D - 1)
          < (‖lead x‖ * ‖z‖) * ‖z‖ ^ (D - 1) :=
            mul_lt_mul_of_pos_right hsum_lt hpow_pos
      _ = ‖lead x‖ * (‖z‖ * ‖z‖ ^ (D - 1)) := by ring
      _ = ‖lead x‖ * ‖z‖ ^ D := by rw [hpow_succ]
  calc
    ‖∑ i : Fin D, lower i x * z ^ (i : Nat)‖
        ≤ (∑ i : Fin D, ‖lower i x‖) * ‖z‖ ^ (D - 1) := htail_le
    _ < ‖lead x‖ * ‖z‖ ^ D := htail_bound_lt
    _ = ‖lead x * z ^ D‖ := by rw [norm_mul, norm_pow]

/-- Nonvanishing outside the explicit largeness threshold from Lemma `nested`, Step 2. -/
theorem tailPolynomial_ne_zero_of_tailThreshold {α : Type*} {D : Nat}
    {lead : α -> ℂ} {lower : Fin D -> α -> ℂ} {x : α} {z : ℂ}
    (hD : 0 < D)
    (hlead : lead x ≠ 0)
    (hlarge : tailThreshold D lead lower x < ‖z‖) :
    tailPolynomial D lead lower x z ≠ 0 :=
  tailPolynomial_ne_zero_of_norm_tail_lt
    (norm_tail_lt_leading_norm_of_tailThreshold hD hlead hlarge)

/-- The explicit threshold is continuous on any base region where the leading coefficient
is continuous and zero-free.

This is the continuity assertion for `R_K` in Lemma `nested`, Step 2. -/
theorem continuousOn_tailThreshold {α : Type*} [TopologicalSpace α] {D : Nat}
    {lead : α -> ℂ} {lower : Fin D -> α -> ℂ} {U : Set α}
    (hlead_cont : ContinuousOn lead U)
    (hlower_cont : ∀ i : Fin D, ContinuousOn (lower i) U)
    (hlead_ne : ∀ x ∈ U, lead x ≠ 0) :
    ContinuousOn (tailThreshold D lead lower) U := by
  have hden_cont : ContinuousOn (fun x => ‖lead x‖) U := hlead_cont.norm
  have hden_ne : ∀ x ∈ U, ‖lead x‖ ≠ 0 := by
    intro x hx
    exact norm_ne_zero_iff.mpr (hlead_ne x hx)
  have hsum : ContinuousOn
      (fun x => ∑ i : Fin D, ‖lower i x‖ / ‖lead x‖) U := by
    simpa using
      (continuousOn_finsetSum (Finset.univ : Finset (Fin D)) fun i _hi =>
        (hlower_cont i).norm.div hden_cont hden_ne)
  simpa [tailThreshold] using continuousOn_const.add hsum

end TransformerIdentifiability.NLayer
