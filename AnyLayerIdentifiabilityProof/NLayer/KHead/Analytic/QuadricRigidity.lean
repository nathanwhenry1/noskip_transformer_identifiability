import AnyLayerIdentifiabilityProof.NLayer.KHead.Core
import AnyLayerIdentifiabilityProof.NLayer.Analytic.AlgebraicQuadric

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.KHead

/-!
# K-head quadric rigidity packet

This file is the K04F owner shard.  The two main quadric-rigidity lemmas are exposed
as proposition-valued APIs and proved from local slice geometry, elementary open-set
arguments, and the existing single-head analytic anchors.
-/

/-- Linear hyperplane with normal `u`, written using the matrix dot product. -/
def hyperplane {d : Nat} (u : Fin d -> ℝ) : Set (Fin d -> ℝ) :=
  {v | dotProduct u v = 0}

@[simp]
theorem mem_hyperplane {d : Nat} (u v : Fin d -> ℝ) :
    v ∈ hyperplane u ↔ dotProduct u v = 0 :=
  Iff.rfl

@[simp]
theorem zero_mem_hyperplane {d : Nat} (u : Fin d -> ℝ) :
    (0 : Fin d -> ℝ) ∈ hyperplane u := by
  simp [hyperplane]

theorem continuous_matrix_mulVec {d : Nat} (M : Matrix (Fin d) (Fin d) ℝ) :
    Continuous fun x : Fin d -> ℝ => M *ᵥ x := by
  rw [continuous_pi_iff]
  intro i
  simpa [Matrix.mulVec, dotProduct] using
    (continuous_finsetSum Finset.univ fun j _ =>
      continuous_const.mul (continuous_apply j))

theorem continuous_dotProduct_const_right {d : Nat} (v : Fin d -> ℝ) :
    Continuous fun u : Fin d -> ℝ => dotProduct u v := by
  simpa [dotProduct] using
    (continuous_finsetSum Finset.univ fun i _ =>
      (continuous_apply i).mul continuous_const)

theorem continuous_dotProduct_self {d : Nat} :
    Continuous fun u : Fin d -> ℝ => dotProduct u u := by
  simpa [dotProduct] using
    (continuous_finsetSum Finset.univ fun i _ =>
      (continuous_apply i).mul (continuous_apply i))

/-- Orthogonal projection of `v0` onto the fiber normal to `Aᵀ *ᵥ w`.  The formula is
only used on neighborhoods where the normal is nonzero. -/
noncomputable def quadricSliceProjection {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (v0 w : Fin d -> ℝ) : Fin d -> ℝ :=
  let u : Fin d -> ℝ := Aᵀ *ᵥ w
  v0 - (dotProduct u v0 / dotProduct u u) • u

theorem continuousAt_quadricSliceProjection {d : Nat}
    {A : Matrix (Fin d) (Fin d) ℝ} {v0 w0 : Fin d -> ℝ}
    (hnormal : Aᵀ *ᵥ w0 ≠ 0) :
    ContinuousAt (quadricSliceProjection A v0) w0 := by
  let n : (Fin d -> ℝ) -> (Fin d -> ℝ) := fun w => Aᵀ *ᵥ w
  have hn : Continuous n := by
    simpa [n] using continuous_matrix_mulVec (Aᵀ)
  have hnum : ContinuousAt (fun w : Fin d -> ℝ => dotProduct (n w) v0) w0 := by
    simpa [Function.comp_def, n] using
      (continuous_dotProduct_const_right v0).continuousAt.comp hn.continuousAt
  have hden : ContinuousAt (fun w : Fin d -> ℝ => dotProduct (n w) (n w)) w0 := by
    simpa [Function.comp_def, n] using
      continuous_dotProduct_self.continuousAt.comp hn.continuousAt
  have hden_ne : dotProduct (n w0) (n w0) ≠ 0 := by
    intro hzero
    exact hnormal (dotProduct_self_eq_zero.mp hzero)
  have hratio :
      ContinuousAt
        (fun w : Fin d -> ℝ => dotProduct (n w) v0 / dotProduct (n w) (n w)) w0 :=
    hnum.div hden hden_ne
  have hproj :
      ContinuousAt
        (fun w : Fin d -> ℝ =>
          v0 - (dotProduct (n w) v0 / dotProduct (n w) (n w)) • n w) w0 :=
    continuousAt_const.sub (hratio.smul hn.continuousAt)
  simpa [quadricSliceProjection, n] using hproj

theorem quadricSliceProjection_eq_self_of_dotProduct_eq_zero {d : Nat}
    {A : Matrix (Fin d) (Fin d) ℝ} {v0 w : Fin d -> ℝ}
    (hzero : dotProduct (Aᵀ *ᵥ w) v0 = 0) :
    quadricSliceProjection A v0 w = v0 := by
  simp [quadricSliceProjection, hzero]

theorem quadricSliceProjection_mem_hyperplane {d : Nat}
    {A : Matrix (Fin d) (Fin d) ℝ} {v0 w : Fin d -> ℝ}
    (hnormal : Aᵀ *ᵥ w ≠ 0) :
    quadricSliceProjection A v0 w ∈ hyperplane (Aᵀ *ᵥ w) := by
  let u : Fin d -> ℝ := Aᵀ *ᵥ w
  have hden_ne : dotProduct u u ≠ 0 := by
    intro hzero
    exact hnormal (by simpa [u] using dotProduct_self_eq_zero.mp hzero)
  simp only [quadricSliceProjection, mem_hyperplane]
  change dotProduct u (v0 - (dotProduct u v0 / dotProduct u u) • u) = 0
  rw [dotProduct_sub, dotProduct_smul]
  simp only [smul_eq_mul]
  field_simp [hden_ne]
  ring

/-- Local product-and-slice data around a nonsingular bilinear quadric point. -/
def QuadricSliceData {d : Nat} (A : Matrix (Fin d) (Fin d) ℝ)
    (w0 v0 : Fin d -> ℝ) (W : Set ((Fin d -> ℝ) × (Fin d -> ℝ))) : Prop :=
  ∃ U V : Set (Fin d -> ℝ),
    IsOpen U ∧
    IsOpen V ∧
    w0 ∈ U ∧
    v0 ∈ V ∧
    (0 : Fin d -> ℝ) ∉ U ∧
    U ×ˢ V ⊆ W ∧
    (∀ w : Fin d -> ℝ, w ∈ U -> Aᵀ *ᵥ w ≠ 0) ∧
    (∀ w : Fin d -> ℝ, w ∈ U ->
      RelativelyOpenIn (V ∩ hyperplane (Aᵀ *ᵥ w)) (hyperplane (Aᵀ *ᵥ w))) ∧
    (∀ w : Fin d -> ℝ, w ∈ U ->
      (V ∩ hyperplane (Aᵀ *ᵥ w)).Nonempty) ∧
    (∀ w : Fin d -> ℝ, ∀ _hw : w ∈ U,
      ∀ v : Fin d -> ℝ, v ∈ V ∩ hyperplane (Aᵀ *ᵥ w) -> (w, v) ∈ W) ∧
    (∀ w : Fin d -> ℝ, ∀ _hw : w ∈ U,
      ∀ v : Fin d -> ℝ, v ∈ V ∩ hyperplane (Aᵀ *ᵥ w) ->
        matrixBilin A w v = 0)

theorem quadricSliceData_of_open {d : Nat}
    {A : Matrix (Fin d) (Fin d) ℝ} {w0 v0 : Fin d -> ℝ}
    {W : Set ((Fin d -> ℝ) × (Fin d -> ℝ))}
    (hdetA : A.det ≠ 0) (hw0_ne : w0 ≠ 0)
    (hquad0 : matrixBilin A w0 v0 = 0)
    (hW_open : IsOpen W) (hW_mem : (w0, v0) ∈ W) :
    QuadricSliceData A w0 v0 W := by
  classical
  have hnormal_w0 : Aᵀ *ᵥ w0 ≠ 0 := by
    intro hzero
    exact hw0_ne (transpose_mulVec_eq_zero_of_det_ne_zero A hdetA hzero)
  have hquad0_dot : dotProduct (Aᵀ *ᵥ w0) v0 = 0 := by
    simpa [matrixBilin_eq_transpose_dot] using hquad0
  have hW_nhds : W ∈ nhds (w0, v0) := hW_open.mem_nhds hW_mem
  have hW_prod : W ∈ nhds w0 ×ˢ nhds v0 := by
    simpa [nhds_prod_eq] using hW_nhds
  rcases Filter.mem_prod_iff.mp hW_prod with
    ⟨Uraw, hUraw, Vraw, hVraw, hprod_raw⟩
  rcases mem_nhds_iff.mp hUraw with ⟨Uo, hUo_sub, hUo_open, hw0Uo⟩
  rcases mem_nhds_iff.mp hVraw with ⟨Vo, hVo_sub, hVo_open, hv0Vo⟩
  have hproj_cont : ContinuousAt (quadricSliceProjection A v0) w0 :=
    continuousAt_quadricSliceProjection hnormal_w0
  have hproj_w0 : quadricSliceProjection A v0 w0 = v0 :=
    quadricSliceProjection_eq_self_of_dotProduct_eq_zero hquad0_dot
  have hproj_pre : {w : Fin d -> ℝ | quadricSliceProjection A v0 w ∈ Vo} ∈ nhds w0 := by
    have hVo_nhds : Vo ∈ nhds (quadricSliceProjection A v0 w0) := by
      simpa [hproj_w0] using hVo_open.mem_nhds hv0Vo
    exact hproj_cont.preimage_mem_nhds hVo_nhds
  rcases mem_nhds_iff.mp hproj_pre with ⟨Up, hUp_sub, hUp_open, hw0Up⟩
  let Ubase : Set (Fin d -> ℝ) := Uo ∩ {w | w ≠ 0}
  let U : Set (Fin d -> ℝ) := Ubase ∩ Up
  refine ⟨U, Vo, ?_, hVo_open, ?_, hv0Vo, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hUo_open.inter isOpen_ne).inter hUp_open
  · exact ⟨⟨hw0Uo, hw0_ne⟩, hw0Up⟩
  · intro hzeroU
    exact hzeroU.1.2 rfl
  · rintro ⟨w, v⟩ hp
    exact hprod_raw ⟨hUo_sub hp.1.1.1, hVo_sub hp.2⟩
  · intro w hw hzero
    exact hw.1.2 (transpose_mulVec_eq_zero_of_det_ne_zero A hdetA hzero)
  · intro w _hw
    exact ⟨Vo, hVo_open, rfl⟩
  · intro w hw
    refine ⟨quadricSliceProjection A v0 w, ?_⟩
    exact ⟨hUp_sub hw.2, quadricSliceProjection_mem_hyperplane (by
      exact (by
        intro hzero
        exact hw.1.2 (transpose_mulVec_eq_zero_of_det_ne_zero A hdetA hzero)))⟩
  · intro w hw v hv
    exact hprod_raw ⟨hUo_sub hw.1.1, hVo_sub hv.1⟩
  · intro w _hw v hv
    rw [matrixBilin_eq_transpose_dot]
    exact hv.2

theorem mem_hyperplane_add_smul {d : Nat} {u v h : Fin d -> ℝ}
    (hv : v ∈ hyperplane u) (hh : h ∈ hyperplane u) (t : ℝ) :
    v + t • h ∈ hyperplane u := by
  simp only [mem_hyperplane] at hv hh ⊢
  rw [dotProduct_add, dotProduct_smul]
  rw [hv, hh]
  ring

/-- If a vector annihilates the hyperplane normal to `u`, then it is a scalar multiple
of `u`.  This is the coefficient extraction used in `lem:affine-hyperplane`. -/
theorem vector_eq_smul_of_forall_dotProduct_eq_zero_on_hyperplane {d : Nat}
    {u c : Fin d -> ℝ} (hu : u ≠ 0)
    (hc : ∀ h : Fin d -> ℝ, h ∈ hyperplane u -> dotProduct c h = 0) :
    ∃ a : ℝ, c = a • u := by
  classical
  have hu_coord : ∃ i : Fin d, u i ≠ 0 := by
    by_contra h
    apply hu
    ext i
    exact by_contra fun hi => h ⟨i, hi⟩
  rcases hu_coord with ⟨i0, hi0⟩
  refine ⟨c i0 / u i0, ?_⟩
  ext j
  by_cases hji : j = i0
  · subst j
    simp [hi0]
  · let hvec : Fin d -> ℝ := Pi.single i0 (u j) - Pi.single j (u i0)
    have hh : hvec ∈ hyperplane u := by
      simp [hvec, hyperplane, dotProduct_sub, dotProduct_single]
      ring
    have hrel : c i0 * u j - c j * u i0 = 0 := by
      simpa [hvec, dotProduct_sub, dotProduct_single] using hc hvec hh
    have hmul : c j * u i0 = c i0 * u j := by
      linarith
    calc
      c j = (c j * u i0) / u i0 := by field_simp [hi0]
      _ = (c i0 * u j) / u i0 := by rw [hmul]
      _ = (c i0 / u i0) * u j := by field_simp [hi0]

/-- **K04F.E.lem-affine-hyperplane.S/P**.

An affine function vanishing on a nonempty relatively open subset of a nonzero
linear hyperplane vanishes on the whole hyperplane; its linear coefficient is
parallel to the normal and its constant term is zero. -/
theorem lem_affine_hyperplane {d : Nat} {u c : Fin d -> ℝ} {β : ℝ}
    {O : Set (Fin d -> ℝ)} (hu : u ≠ 0)
    (hO_rel : RelativelyOpenIn O (hyperplane u)) (hO_nonempty : O.Nonempty)
    (hzero : ∀ v : Fin d -> ℝ, v ∈ O -> dotProduct c v + β = 0) :
    (∀ v : Fin d -> ℝ, v ∈ hyperplane u -> dotProduct c v + β = 0) ∧
      (∃ a : ℝ, c = a • u) ∧ β = 0 := by
  rcases hO_rel with ⟨U, hU_open, rfl⟩
  rcases hO_nonempty with ⟨v0, hv0O⟩
  have hv0U : v0 ∈ U := hv0O.1
  have hv0H : v0 ∈ hyperplane u := hv0O.2
  have hzero_v0 : dotProduct c v0 + β = 0 := hzero v0 hv0O
  have hc_ann : ∀ h : Fin d -> ℝ, h ∈ hyperplane u -> dotProduct c h = 0 := by
    intro h hh
    have hline_event : ∀ᶠ t in nhds (0 : ℝ), v0 + t • h ∈ U := by
      have hcont : ContinuousAt (fun t : ℝ => v0 + t • h) 0 := by
        exact continuous_const.continuousAt.add
          (continuous_id.smul continuous_const).continuousAt
      exact hcont.preimage_mem_nhds (by simpa using hU_open.mem_nhds hv0U)
    have hne_freq : ∃ᶠ t in nhds (0 : ℝ), t ≠ 0 :=
      (frequently_lt_nhds (0 : ℝ)).mono fun t ht => ne_of_lt ht
    rcases (hne_freq.and_eventually hline_event).exists with ⟨t, ht_ne, htU⟩
    have htH : v0 + t • h ∈ hyperplane u :=
      mem_hyperplane_add_smul hv0H hh t
    have hzero_t : dotProduct c (v0 + t • h) + β = 0 :=
      hzero (v0 + t • h) ⟨htU, htH⟩
    have ht_mul : t * dotProduct c h = 0 := by
      rw [dotProduct_add, dotProduct_smul] at hzero_t
      simp only [smul_eq_mul] at hzero_t
      linarith
    exact (mul_eq_zero.mp ht_mul).resolve_left ht_ne
  have hc_span := vector_eq_smul_of_forall_dotProduct_eq_zero_on_hyperplane hu hc_ann
  have hbeta : β = 0 := by
    have hc_v0 : dotProduct c v0 = 0 := hc_ann v0 hv0H
    linarith
  refine ⟨?_, hc_span, hbeta⟩
  intro v hv
  have hcv : dotProduct c v = 0 := hc_ann v hv
  linarith

/-- **K04F.E.lem-eigenvector-open.S/P**.

A matrix that sends every vector in a nonempty open set to a scalar multiple of
itself is scalar, in dimension at least two. -/
theorem lem_eigenvector_open {d : Nat} (hd : 2 ≤ d)
    {Y : Set (Fin d -> ℝ)} (hY_open : IsOpen Y) (hY_nonempty : Y.Nonempty)
    (M : Matrix (Fin d) (Fin d) ℝ)
    (hM : ∀ y : Fin d -> ℝ, y ∈ Y -> ∃ c : ℝ, M *ᵥ y = c • y) :
    ∃ c : ℝ, M = c • (1 : Matrix (Fin d) (Fin d) ℝ) :=
  matrix_eq_smul_one_of_forall_mulVec_eq_smul_self_on_open
    hd hY_open hY_nonempty M hM

/-- A linear form vanishing on a nonempty open set vanishes identically. -/
theorem linearForm_eq_zero_of_forall_mem_open {d : Nat}
    {W : Set (Fin d -> ℝ)} (hW_open : IsOpen W) (hW_nonempty : W.Nonempty)
    {r : Fin d -> ℝ}
    (hzero : ∀ w : Fin d -> ℝ, w ∈ W -> dotProduct r w = 0) :
    r = 0 := by
  rcases hW_nonempty with ⟨w0, hw0⟩
  have hglobal : ∀ z : Fin d -> ℝ, dotProduct r z = 0 := by
    intro z
    have hline_event : ∀ᶠ t in nhds (0 : ℝ), w0 + t • z ∈ W := by
      have hcont : ContinuousAt (fun t : ℝ => w0 + t • z) 0 := by
        exact continuous_const.continuousAt.add
          (continuous_id.smul continuous_const).continuousAt
      exact hcont.preimage_mem_nhds (by simpa using hW_open.mem_nhds hw0)
    have hne_freq : ∃ᶠ t in nhds (0 : ℝ), t ≠ 0 :=
      (frequently_lt_nhds (0 : ℝ)).mono fun t ht => ne_of_lt ht
    rcases (hne_freq.and_eventually hline_event).exists with ⟨t, ht_ne, htW⟩
    have h0 := hzero w0 hw0
    have ht := hzero (w0 + t • z) htW
    have ht_mul : t * dotProduct r z = 0 := by
      rw [dotProduct_add, dotProduct_smul] at ht
      simp only [smul_eq_mul] at ht
      linarith
    exact (mul_eq_zero.mp ht_mul).resolve_left ht_ne
  exact dotProduct_eq_zero r hglobal

/-- Row-wise open-set vanishing of linear forms forces a matrix to be zero. -/
theorem matrix_eq_zero_of_forall_row_dotProduct_eq_zero_on_open {d : Nat}
    {W : Set (Fin d -> ℝ)} (hW_open : IsOpen W) (hW_nonempty : W.Nonempty)
    {E : Matrix (Fin d) (Fin d) ℝ}
    (hzero : ∀ j : Fin d, ∀ w : Fin d -> ℝ, w ∈ W ->
      dotProduct (fun i : Fin d => E j i) w = 0) :
    E = 0 := by
  ext j i
  have hrow :
      (fun i : Fin d => E j i) = 0 :=
    linearForm_eq_zero_of_forall_mem_open hW_open hW_nonempty (hzero j)
  exact congrFun hrow i

/-- A fixed vector that is parallel to every vector in a nonempty open set must be zero
in dimension at least two. -/
theorem vector_eq_zero_of_forall_mem_open_eq_smul {d : Nat} (hd : 2 ≤ d)
    {W : Set (Fin d -> ℝ)} (hW_open : IsOpen W) (hW_nonempty : W.Nonempty)
    {z : Fin d -> ℝ}
    (hz : ∀ w : Fin d -> ℝ, w ∈ W -> ∃ a : ℝ, z = a • w) :
    z = 0 := by
  classical
  by_contra hz_ne
  rcases exists_ne_zero_dotProduct_eq_zero_of_two_le hd z with ⟨r, hr_ne, hrz⟩
  have hzero : ∀ w : Fin d -> ℝ, w ∈ W -> dotProduct r w = 0 := by
    intro w hw
    rcases hz w hw with ⟨a, haz⟩
    have ha_ne : a ≠ 0 := by
      intro ha
      apply hz_ne
      simpa [ha] using haz
    have hdot : dotProduct r z = a * dotProduct r w := by
      rw [haz, dotProduct_smul]
      simp [smul_eq_mul]
    have hmul : a * dotProduct r w = 0 := by
      linarith
    exact (mul_eq_zero.mp hmul).resolve_left ha_ne
  have hr_zero : r = 0 :=
    linearForm_eq_zero_of_forall_mem_open hW_open hW_nonempty hzero
  exact hr_ne hr_zero

/-- If a fixed vector is parallel to `Aᵀw` for every `w` in a nonempty open set and
`A` is nonsingular, then the fixed vector is zero. -/
theorem vector_eq_zero_of_forall_mem_open_eq_smul_transpose_mulVec {d : Nat}
    (hd : 2 ≤ d) {W : Set (Fin d -> ℝ)}
    (hW_open : IsOpen W) (hW_nonempty : W.Nonempty)
    {A : Matrix (Fin d) (Fin d) ℝ} (hdetA : A.det ≠ 0)
    {c : Fin d -> ℝ}
    (hc : ∀ w : Fin d -> ℝ, w ∈ W -> ∃ a : ℝ, c = a • (Aᵀ *ᵥ w)) :
    c = 0 := by
  classical
  let N : Matrix (Fin d) (Fin d) ℝ := Aᵀ
  have hdetN : N.det ≠ 0 := by
    simpa [N] using hdetA
  let z : Fin d -> ℝ := N⁻¹ *ᵥ c
  have hz_parallel : ∀ w : Fin d -> ℝ, w ∈ W -> ∃ a : ℝ, z = a • w := by
    intro w hw
    rcases hc w hw with ⟨a, hca⟩
    refine ⟨a, ?_⟩
    have hleft : N⁻¹ *ᵥ (N *ᵥ w) = w := by
      have hmul : (N⁻¹ * N) *ᵥ w = w := by
        rw [Matrix.nonsing_inv_mul N (Ne.isUnit hdetN), Matrix.one_mulVec]
      simpa [Matrix.mulVec_mulVec] using hmul
    calc
      z = N⁻¹ *ᵥ c := rfl
      _ = N⁻¹ *ᵥ (a • (N *ᵥ w)) := by rw [hca]
      _ = a • (N⁻¹ *ᵥ (N *ᵥ w)) := by rw [Matrix.mulVec_smul]
      _ = a • w := by rw [hleft]
  have hz_zero : z = 0 :=
    vector_eq_zero_of_forall_mem_open_eq_smul hd hW_open hW_nonempty hz_parallel
  have hright : N *ᵥ z = c := by
    have hmul : (N * N⁻¹) *ᵥ c = c := by
      rw [Matrix.mul_nonsing_inv N (Ne.isUnit hdetN), Matrix.one_mulVec]
    simpa [z, Matrix.mulVec_mulVec] using hmul
  rw [hz_zero] at hright
  simpa using hright.symm

/-- If `Y + Yᵀ = 0`, then the K-head `Sym(Y)` is zero. -/
theorem sym_eq_zero_of_add_transpose_eq_zero {d : Nat}
    {Y : Matrix (Fin d) (Fin d) ℝ} (hY : Y + Yᵀ = 0) :
    sym Y = 0 := by
  simp [sym, hY]

/-- The symmetric part of a quadratic form vanishing on a nonempty open set is zero. -/
theorem sym_eq_zero_of_forall_matrixBilin_self_eq_zero_on_open {d : Nat}
    {W : Set (Fin d -> ℝ)} (hW_open : IsOpen W) (hW_nonempty : W.Nonempty)
    {Y : Matrix (Fin d) (Fin d) ℝ}
    (hzero : ∀ w : Fin d -> ℝ, w ∈ W -> matrixBilin Y w w = 0) :
    sym Y = 0 := by
  apply sym_eq_zero_of_add_transpose_eq_zero
  apply matrix_symPart_eq_zero_of_forall_quadratic_eq_zero_on_open hW_open hW_nonempty
  intro w hw
  simpa [matrixBilin] using hzero w hw

/-- Open-set parallel rigidity for transposed matrices, packaged in the orientation
used by the quadratic quadric-rigidity proof after slicing. -/
theorem matrix_eq_smul_of_forall_transpose_mulVec_eq_smul_on_open {d : Nat}
    (hd : 2 ≤ d) {W : Set (Fin d -> ℝ)} (hW_open : IsOpen W)
    (hW_nonempty : W.Nonempty) {A X : Matrix (Fin d) (Fin d) ℝ}
    (hdetA : A.det ≠ 0)
    (hparallel : ∀ w : Fin d -> ℝ, w ∈ W ->
      ∃ c : ℝ, Xᵀ *ᵥ w = c • (Aᵀ *ᵥ w)) :
    ∃ c : ℝ, X = c • A := by
  have hdetAT : Aᵀ.det ≠ 0 := by
    simpa using hdetA
  rcases matrix_eq_smul_of_forall_mulVec_eq_smul_on_open
      hd hW_open hW_nonempty (M := Xᵀ) (N := Aᵀ) hdetAT hparallel with
    ⟨c, hc⟩
  refine ⟨c, ?_⟩
  have hct := congrArg Matrix.transpose hc
  simpa using hct

/-- Unblocked post-slicing form of the quadratic quadric-rigidity conclusion. -/
theorem quadratic_quadric_rigidity_conclusion_of_slice_data {d : Nat}
    (hd : 2 ≤ d) {W : Set (Fin d -> ℝ)} (hW_open : IsOpen W)
    (hW_nonempty : W.Nonempty) {A X Y : Matrix (Fin d) (Fin d) ℝ}
    (hdetA : A.det ≠ 0)
    (hX : ∀ w : Fin d -> ℝ, w ∈ W ->
      ∃ c : ℝ, Xᵀ *ᵥ w = c • (Aᵀ *ᵥ w))
    (hY : ∀ w : Fin d -> ℝ, w ∈ W -> matrixBilin Y w w = 0) :
    ∃ c : ℝ, X = c • A ∧ sym Y = 0 := by
  rcases matrix_eq_smul_of_forall_transpose_mulVec_eq_smul_on_open
      hd hW_open hW_nonempty hdetA hX with ⟨c, hc⟩
  exact ⟨c, hc, sym_eq_zero_of_forall_matrixBilin_self_eq_zero_on_open
    hW_open hW_nonempty hY⟩

/-- **K04F.E.lem-linear-quadric-rigidity.S**.

Proposition-valued statement of linear quadric rigidity. -/
def lem_linear_quadric_rigidity_statement (d : Nat) : Prop :=
  2 ≤ d ->
    ∀ (A C E : Matrix (Fin d) (Fin d) ℝ)
      (w0 v0 : Fin d -> ℝ) (W : Set ((Fin d -> ℝ) × (Fin d -> ℝ))),
      A.det ≠ 0 ->
      w0 ≠ 0 ->
      matrixBilin A w0 v0 = 0 ->
      IsOpen W ->
      (w0, v0) ∈ W ->
      (∀ p : (Fin d -> ℝ) × (Fin d -> ℝ), p ∈ W ->
        matrixBilin A p.1 p.2 = 0 -> C *ᵥ p.2 + E *ᵥ p.1 = 0) ->
      C = 0 ∧ E = 0

/-- **K04F.E.lem-quadratic-quadric-rigidity.S**.

Proposition-valued statement of quadratic quadric rigidity. -/
def lem_quadratic_quadric_rigidity_statement (d : Nat) : Prop :=
  2 ≤ d ->
    ∀ (A X Y : Matrix (Fin d) (Fin d) ℝ)
      (w0 v0 : Fin d -> ℝ) (W : Set ((Fin d -> ℝ) × (Fin d -> ℝ))),
      A.det ≠ 0 ->
      w0 ≠ 0 ->
      matrixBilin A w0 v0 = 0 ->
      IsOpen W ->
      (w0, v0) ∈ W ->
      (∀ p : (Fin d -> ℝ) × (Fin d -> ℝ), p ∈ W ->
        matrixBilin A p.1 p.2 = 0 ->
        matrixBilin X p.1 p.2 + matrixBilin Y p.1 p.1 = 0) ->
      ∃ c : ℝ, X = c • A ∧ sym Y = 0

/-- **K04F.E.lem-linear-quadric-rigidity.P**.

Linear quadric rigidity near a nonsingular bilinear quadric point. -/
theorem lem_linear_quadric_rigidity {d : Nat} (hd : 2 ≤ d)
    (A C E : Matrix (Fin d) (Fin d) ℝ)
    (w0 v0 : Fin d -> ℝ) (W : Set ((Fin d -> ℝ) × (Fin d -> ℝ)))
    (hdetA : A.det ≠ 0) (hw0_ne : w0 ≠ 0)
    (hquad0 : matrixBilin A w0 v0 = 0)
    (hW_open : IsOpen W) (hW_mem : (w0, v0) ∈ W)
    (hvanish : ∀ p : (Fin d -> ℝ) × (Fin d -> ℝ), p ∈ W ->
      matrixBilin A p.1 p.2 = 0 -> C *ᵥ p.2 + E *ᵥ p.1 = 0) :
    C = 0 ∧ E = 0 := by
  classical
  rcases quadricSliceData_of_open hdetA hw0_ne hquad0 hW_open hW_mem with
    ⟨U, V, hU_open, _hV_open, hw0U, _hv0V, _hzero_not,
      _hprod, hnormal, hslice_rel, hslice_nonempty, hslice_mem_W,
      hslice_quadric⟩
  have hU_nonempty : U.Nonempty := ⟨w0, hw0U⟩
  have hrow :
      ∀ j : Fin d, ∀ w : Fin d -> ℝ, w ∈ U ->
        (∃ a : ℝ, (fun i : Fin d => C j i) = a • (Aᵀ *ᵥ w)) ∧
          dotProduct (fun i : Fin d => E j i) w = 0 := by
    intro j w hw
    have hzero_aff :
        ∀ v : Fin d -> ℝ, v ∈ V ∩ hyperplane (Aᵀ *ᵥ w) ->
          dotProduct (fun i : Fin d => C j i) v +
            dotProduct (fun i : Fin d => E j i) w = 0 := by
      intro v hv
      have hvec := hvanish (w, v) (hslice_mem_W w hw v hv)
        (hslice_quadric w hw v hv)
      have hj := congrFun hvec j
      simpa [Matrix.mulVec] using hj
    have haff := lem_affine_hyperplane
      (u := Aᵀ *ᵥ w) (c := fun i : Fin d => C j i)
      (β := dotProduct (fun i : Fin d => E j i) w)
      (hnormal w hw) (hslice_rel w hw) (hslice_nonempty w hw) hzero_aff
    exact ⟨haff.2.1, haff.2.2⟩
  have hE : E = 0 :=
    matrix_eq_zero_of_forall_row_dotProduct_eq_zero_on_open
      hU_open hU_nonempty (E := E) (by
        intro j w hw
        exact (hrow j w hw).2)
  have hC : C = 0 := by
    ext j i
    have hrow_zero : (fun i : Fin d => C j i) = 0 :=
      vector_eq_zero_of_forall_mem_open_eq_smul_transpose_mulVec
        hd hU_open hU_nonempty hdetA (by
          intro w hw
          exact (hrow j w hw).1)
    exact congrFun hrow_zero i
  exact ⟨hC, hE⟩

/-- Proposition-valued proof wrapper for linear quadric rigidity. -/
theorem lem_linear_quadric_rigidity_statement_proof (d : Nat) :
    lem_linear_quadric_rigidity_statement d := by
  intro hd A C E w0 v0 W hdetA hw0_ne hquad0 hW_open hW_mem hvanish
  exact lem_linear_quadric_rigidity hd A C E w0 v0 W
    hdetA hw0_ne hquad0 hW_open hW_mem hvanish

/-- **K04F.E.lem-quadratic-quadric-rigidity.P**.

Quadratic quadric rigidity near a nonsingular bilinear quadric point. -/
theorem lem_quadratic_quadric_rigidity {d : Nat} (hd : 2 ≤ d)
    (A X Y : Matrix (Fin d) (Fin d) ℝ)
    (w0 v0 : Fin d -> ℝ) (W : Set ((Fin d -> ℝ) × (Fin d -> ℝ)))
    (hdetA : A.det ≠ 0) (hw0_ne : w0 ≠ 0)
    (hquad0 : matrixBilin A w0 v0 = 0)
    (hW_open : IsOpen W) (hW_mem : (w0, v0) ∈ W)
    (hvanish : ∀ p : (Fin d -> ℝ) × (Fin d -> ℝ), p ∈ W ->
      matrixBilin A p.1 p.2 = 0 ->
      matrixBilin X p.1 p.2 + matrixBilin Y p.1 p.1 = 0) :
    ∃ c : ℝ, X = c • A ∧ sym Y = 0 := by
  classical
  rcases quadricSliceData_of_open hdetA hw0_ne hquad0 hW_open hW_mem with
    ⟨U, V, hU_open, _hV_open, hw0U, _hv0V, _hzero_not,
      _hprod, hnormal, hslice_rel, hslice_nonempty, hslice_mem_W,
      hslice_quadric⟩
  have hU_nonempty : U.Nonempty := ⟨w0, hw0U⟩
  have hslice :
      ∀ w : Fin d -> ℝ, w ∈ U ->
        (∃ c : ℝ, Xᵀ *ᵥ w = c • (Aᵀ *ᵥ w)) ∧
          matrixBilin Y w w = 0 := by
    intro w hw
    have hzero_aff :
        ∀ v : Fin d -> ℝ, v ∈ V ∩ hyperplane (Aᵀ *ᵥ w) ->
          dotProduct (Xᵀ *ᵥ w) v + matrixBilin Y w w = 0 := by
      intro v hv
      have hscalar := hvanish (w, v) (hslice_mem_W w hw v hv)
        (hslice_quadric w hw v hv)
      simpa [matrixBilin_eq_transpose_dot] using hscalar
    have haff := lem_affine_hyperplane
      (u := Aᵀ *ᵥ w) (c := Xᵀ *ᵥ w) (β := matrixBilin Y w w)
      (hnormal w hw) (hslice_rel w hw) (hslice_nonempty w hw) hzero_aff
    exact ⟨haff.2.1, haff.2.2⟩
  exact quadratic_quadric_rigidity_conclusion_of_slice_data
    hd hU_open hU_nonempty hdetA
    (fun w hw => (hslice w hw).1)
    (fun w hw => (hslice w hw).2)

/-- Proposition-valued proof wrapper for quadratic quadric rigidity. -/
theorem lem_quadratic_quadric_rigidity_statement_proof (d : Nat) :
    lem_quadratic_quadric_rigidity_statement d := by
  intro hd A X Y w0 v0 W hdetA hw0_ne hquad0 hW_open hW_mem hvanish
  exact lem_quadratic_quadric_rigidity hd A X Y w0 v0 W
    hdetA hw0_ne hquad0 hW_open hW_mem hvanish

end TransformerIdentifiability.NLayer.KHead
