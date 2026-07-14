import AnyLayerIdentifiabilityProof.NLayer.KHead.Core
import AnyLayerIdentifiabilityProof.NLayer.IDL.SaturationMatching
import AnyLayerIdentifiabilityProof.NLayer.KHead.Genericity.AnchorCertificate
import AnyLayerIdentifiabilityProof.NLayer.Analytic.SigmoidTail
import Mathlib.Topology.Connected.LocallyConnected

set_option autoImplicit false

open Matrix Topology

namespace TransformerIdentifiability.NLayer.KHead

/-!
# K-head Step 2 dial API scaffold

This file records the statement/API surface for the 07a fragments
`tex_modular/sections/07a1-sign-region-topology.tex` and `07a2-head-dial.tex`.

The full Step 2 proof gates are not available here, so theorem-shaped TeX items are
represented as proposition-valued records or definitions.  The definitions below are
intended to be stable downstream names for later proof work.
-/

/-! ## Shared first-layer geometry -/

/-- First-layer slope for a selected k-head attention matrix. -/
noncomputable def firstHeadSlope {k d : Nat}
    (A : Fin k -> Matrix (Fin d) (Fin d) ℝ) (h : Fin k)
    (p : ProbePair d) : ℝ :=
  matrixBilin (A h) p.1 p.2

/-- The selected first-head quadric `q_h(w,v)=0`. -/
def firstHeadQuadric {k d : Nat}
    (A : Fin k -> Matrix (Fin d) (Fin d) ℝ) (h : Fin k)
    (p : ProbePair d) : Prop :=
  firstHeadSlope A h p = 0

/-- The selected first-head dial vector `pi_h(w,v)=A_h^T w-A_h v`. -/
noncomputable def firstHeadPi {k d : Nat}
    (A : Fin k -> Matrix (Fin d) (Fin d) ℝ) (h : Fin k)
    (p : ProbePair d) : Fin d -> ℝ :=
  firstLayerPi (A h) p

/-- The quadric patch `M_h={q_h=0,w≠0}`. -/
def quadricPatch {k d : Nat}
    (A : Fin k -> Matrix (Fin d) (Fin d) ℝ) (h : Fin k) :
    Set (ProbePair d) :=
  {p | firstHeadQuadric A h p ∧ p.1 ≠ 0}

/-- The cylinder `M_h × (0,1)` used by the topology statements. -/
def quadricPatchCylinder {k d : Nat}
    (A : Fin k -> Matrix (Fin d) (Fin d) ℝ) (h : Fin k) :
    Set (ProbePair d × ℝ) :=
  {x | x.1 ∈ quadricPatch A h ∧ 0 < x.2 ∧ x.2 < 1}

/-- Projection of a probe/time region to the dial variable. -/
def timeProjection {d : Nat} (U : Set (ProbePair d × ℝ)) : Set ℝ :=
  {t | ∃ p : ProbePair d, (p, t) ∈ U}

/-- Probe slice at a fixed dial value. -/
def timeSlice {d : Nat} (U : Set (ProbePair d × ℝ)) (t : ℝ) :
    Set (ProbePair d) :=
  {p | (p, t) ∈ U}

theorem continuous_firstHeadSlope {k d : Nat}
    (A : Fin k -> Matrix (Fin d) (Fin d) ℝ) (h : Fin k) :
    Continuous (firstHeadSlope A h) := by
  unfold firstHeadSlope matrixBilin
  fun_prop

theorem isClosed_firstHeadQuadric {k d : Nat}
    (A : Fin k -> Matrix (Fin d) (Fin d) ℝ) (h : Fin k) :
    IsClosed {p : ProbePair d | firstHeadQuadric A h p} := by
  simpa [firstHeadQuadric] using
    (isClosed_singleton.preimage (continuous_firstHeadSlope A h))

theorem relativelyOpenIn_empty {α : Type} [TopologicalSpace α]
    (ambient : Set α) :
    RelativelyOpenIn ∅ ambient := by
  exact ⟨∅, isOpen_empty, by simp⟩

theorem relativelyOpenIn_self {α : Type} [TopologicalSpace α]
    (ambient : Set α) :
    RelativelyOpenIn ambient ambient := by
  exact ⟨Set.univ, isOpen_univ, by simp⟩

/-- Relative openness is preserved by intersecting with an ambient open set. -/
theorem RelativelyOpenIn.inter_open {α : Type} [TopologicalSpace α]
    {U H O : Set α}
    (hU : RelativelyOpenIn U H) (hO : IsOpen O) :
    RelativelyOpenIn (U ∩ O) H := by
  rcases hU with ⟨O0, hO0, hUeq⟩
  refine ⟨O0 ∩ O, hO0.inter hO, ?_⟩
  ext x
  simp [hUeq, and_left_comm, and_comm]

/-- Relative openness is preserved under finite intersections in the same ambient set. -/
theorem RelativelyOpenIn.inter {α : Type} [TopologicalSpace α]
    {U V H : Set α}
    (hU : RelativelyOpenIn U H) (hV : RelativelyOpenIn V H) :
    RelativelyOpenIn (U ∩ V) H := by
  rcases hU with ⟨OU, hOU, hUeq⟩
  rcases hV with ⟨OV, hOV, hVeq⟩
  refine ⟨OU ∩ OV, hOU.inter hOV, ?_⟩
  ext x
  simp [hUeq, hVeq, and_left_comm, and_assoc, and_comm]

/-- In a locally connected ambient subtype, connected components of relatively open
subsets are relatively open in the ambient subtype. -/
theorem connectedComponentIn_relativelyOpenIn_of_locallyConnected
    {α : Type} [TopologicalSpace α] {H O : Set α} {x0 : α}
    [LocallyConnectedSpace H]
    (hO : RelativelyOpenIn O H) (hx0 : x0 ∈ O) :
    RelativelyOpenIn (connectedComponentIn O x0) H := by
  rcases hO with ⟨U, hU_open, hO_eq⟩
  have hOH : O ⊆ H := by
    intro x hx
    rw [hO_eq] at hx
    exact hx.2
  let x0H : H := ⟨x0, hOH hx0⟩
  let Osub : Set H := {x : H | (x : α) ∈ O}
  have hOsub_open : IsOpen Osub := by
    have hpre : Osub = ((↑) : H → α) ⁻¹' U := by
      ext x
      simp [Osub, hO_eq]
    rw [hpre]
    exact hU_open.preimage continuous_subtype_val
  have hcomp_open : IsOpen (connectedComponentIn Osub x0H) :=
    hOsub_open.connectedComponentIn
  rcases isOpen_induced_iff.mp hcomp_open with ⟨W, hW_open, hW_eq⟩
  refine ⟨W, hW_open, ?_⟩
  ext x
  constructor
  · intro hx
    have hxO : x ∈ O := connectedComponentIn_subset O x0 hx
    have hxH : x ∈ H := hOH hxO
    have hxsub : (⟨x, hxH⟩ : H) ∈ connectedComponentIn Osub x0H := by
      let S : Set H := ((↑) : H → α) ⁻¹' connectedComponentIn O x0
      have hCsubH : connectedComponentIn O x0 ⊆ H :=
        (connectedComponentIn_subset O x0).trans hOH
      have hS_pre : IsPreconnected S := by
        refine IsInducing.subtypeVal.isPreconnected_image.mp ?_
        have himage :
            ((↑) : H → α) '' S = connectedComponentIn O x0 := by
          rw [Subtype.image_preimage_coe, Set.inter_eq_right.2 hCsubH]
        simpa [himage] using (isPreconnected_connectedComponentIn :
          IsPreconnected (connectedComponentIn O x0))
      have hx0S : x0H ∈ S := by
        exact mem_connectedComponentIn hx0
      have hSsub : S ⊆ Osub := by
        intro y hy
        exact connectedComponentIn_subset O x0 hy
      exact hS_pre.subset_connectedComponentIn hx0S hSsub hx
    have hxW : (⟨x, hxH⟩ : H) ∈ ((↑) : H → α) ⁻¹' W := by
      simpa [hW_eq] using hxsub
    exact ⟨hxW, hxH⟩
  · intro hx
    rcases hx with ⟨hxW, hxH⟩
    have hxsub : (⟨x, hxH⟩ : H) ∈ connectedComponentIn Osub x0H := by
      rw [← hW_eq]
      exact hxW
    let T : Set α := ((↑) : H → α) '' connectedComponentIn Osub x0H
    have hT_pre : IsPreconnected T :=
      isPreconnected_connectedComponentIn.image ((↑) : H → α)
        continuous_subtype_val.continuousOn
    have hx0T : x0 ∈ T := by
      exact ⟨x0H, mem_connectedComponentIn hx0, rfl⟩
    have hTsub : T ⊆ O := by
      intro y hy
      rcases hy with ⟨z, hz, rfl⟩
      exact connectedComponentIn_subset Osub x0H hz
    exact hT_pre.subset_connectedComponentIn hx0T hTsub ⟨⟨x, hxH⟩, hxsub, rfl⟩

theorem relativelyOpenIn_quadricPatch_firstHeadQuadric {k d : Nat}
    (A : Fin k -> Matrix (Fin d) (Fin d) ℝ) (h : Fin k) :
    RelativelyOpenIn (quadricPatch A h)
      {p : ProbePair d | firstHeadQuadric A h p} := by
  refine ⟨{p : ProbePair d | p.1 ≠ 0}, ?_, ?_⟩
  · exact isOpen_ne.preimage continuous_fst
  · ext p
    simp [quadricPatch, and_comm]

theorem quadricPatch_nonempty_of_two_le {k d : Nat}
    (A : Fin k -> Matrix (Fin d) (Fin d) ℝ) (h : Fin k)
    (hd : 2 ≤ d) :
    (quadricPatch A h).Nonempty := by
  let i : Fin d := ⟨0, by omega⟩
  refine ⟨(Pi.single i (1 : ℝ), 0), ?_⟩
  constructor
  · simp [firstHeadQuadric, firstHeadSlope, matrixBilin]
  · intro hzero
    have hi := congrFun hzero i
    simp [i] at hi

theorem quadricPatchCylinder_eq_prod {k d : Nat}
    (A : Fin k -> Matrix (Fin d) (Fin d) ℝ) (h : Fin k) :
    quadricPatchCylinder A h =
      quadricPatch A h ×ˢ Set.Ioo (0 : ℝ) 1 := by
  ext x
  simp [quadricPatchCylinder]

theorem quadricPatchCylinder_nonempty_of_two_le {k d : Nat}
    (A : Fin k -> Matrix (Fin d) (Fin d) ℝ) (h : Fin k)
    (hd : 2 ≤ d) :
    (quadricPatchCylinder A h).Nonempty := by
  rcases quadricPatch_nonempty_of_two_le A h hd with ⟨p, hp⟩
  exact ⟨(p, (1 / 2 : ℝ)), hp, by norm_num, by norm_num⟩

theorem timeProjection_nonempty {d : Nat} {U : Set (ProbePair d × ℝ)}
    (hU : U.Nonempty) :
    (timeProjection U).Nonempty := by
  rcases hU with ⟨x, hx⟩
  exact ⟨x.2, x.1, by simpa using hx⟩

theorem timeProjection_open_of_relativelyOpenIn_quadricPatchCylinder {k d : Nat}
    {A : Fin k -> Matrix (Fin d) (Fin d) ℝ} {h : Fin k}
    {U : Set (ProbePair d × ℝ)}
    (hU : RelativelyOpenIn U (quadricPatchCylinder A h)) :
    IsOpen (timeProjection U) := by
  rcases hU with ⟨O, hO_open, rfl⟩
  rw [isOpen_iff_mem_nhds]
  intro t ht
  rcases ht with ⟨p, hpO, hpCyl⟩
  exact Filter.mem_of_superset
    (((hO_open.preimage (continuous_const.prodMk continuous_id)).inter isOpen_Ioo).mem_nhds
      ⟨hpO, hpCyl.2.1, hpCyl.2.2⟩)
    (by
      intro s hs
      exact ⟨p, hs.1, hpCyl.1, hs.2.1, hs.2.2⟩)

theorem timeProjection_infinite_of_nonempty_relativelyOpenIn_quadricPatchCylinder
    {k d : Nat}
    {A : Fin k -> Matrix (Fin d) (Fin d) ℝ} {h : Fin k}
    {U : Set (ProbePair d × ℝ)}
    (hU_nonempty : U.Nonempty)
    (hU_open : RelativelyOpenIn U (quadricPatchCylinder A h)) :
    (timeProjection U).Infinite := by
  exact infinite_of_mem_nhds
    (timeProjection_nonempty hU_nonempty).choose
    ((timeProjection_open_of_relativelyOpenIn_quadricPatchCylinder hU_open).mem_nhds
      (timeProjection_nonempty hU_nonempty).choose_spec)

theorem timeSlice_relativelyOpenIn_of_relativelyOpenIn_quadricPatchCylinder
    {k d : Nat}
    {A : Fin k -> Matrix (Fin d) (Fin d) ℝ} {h : Fin k}
    {U : Set (ProbePair d × ℝ)} (t : ℝ)
    (hU : RelativelyOpenIn U (quadricPatchCylinder A h)) :
    RelativelyOpenIn (timeSlice U t) (quadricPatch A h) := by
  rcases hU with ⟨O, hO_open, rfl⟩
  by_cases ht : 0 < t ∧ t < 1
  · refine ⟨{p : ProbePair d | (p, t) ∈ O}, ?_, ?_⟩
    · exact hO_open.preimage (continuous_id.prodMk continuous_const)
    · ext p
      simp [timeSlice, quadricPatchCylinder, ht]
  · refine ⟨∅, isOpen_empty, ?_⟩
    ext p
    simp [timeSlice, quadricPatchCylinder, ht]

private def quadricPatchCylinderCoeff {k d : Nat}
    (A : Fin k → Matrix (Fin d) (Fin d) ℝ) (h : Fin k) (i : Fin d) :
    Set (quadricPatchCylinder A h) :=
  {x | (Matrix.mulVec (Matrix.transpose (A h)) ((x : ProbePair d × ℝ).1.1)) i ≠ 0}

private def quadricPatchCylinderCoeffBase {k d : Nat}
    (A : Fin k → Matrix (Fin d) (Fin d) ℝ) (h : Fin k) (i : Fin d) :
    Set (QuadricGraphBase d i × ℝ) :=
  {x | (Matrix.mulVec (Matrix.transpose (A h)) x.1.1) i ≠ 0 ∧ 0 < x.2 ∧ x.2 < 1}

private theorem isOpen_quadricPatchCylinderCoeff {k d : Nat}
    (A : Fin k → Matrix (Fin d) (Fin d) ℝ) (h : Fin k) (i : Fin d) :
    IsOpen (quadricPatchCylinderCoeff A h i) := by
  have hcoeff :
      Continuous fun x : quadricPatchCylinder A h =>
        (Matrix.mulVec (Matrix.transpose (A h)) ((x : ProbePair d × ℝ).1.1)) i := by
    unfold Matrix.mulVec dotProduct
    fun_prop
  simpa [quadricPatchCylinderCoeff] using
    hcoeff.isOpen_preimage {y : ℝ | y ≠ 0} isOpen_ne

private theorem isOpen_quadricPatchCylinderCoeffBase {k d : Nat}
    (A : Fin k → Matrix (Fin d) (Fin d) ℝ) (h : Fin k) (i : Fin d) :
    IsOpen (quadricPatchCylinderCoeffBase A h i) := by
  have hcoeff :
      Continuous fun x : QuadricGraphBase d i × ℝ =>
        (Matrix.mulVec (Matrix.transpose (A h)) x.1.1) i := by
    unfold Matrix.mulVec dotProduct
    fun_prop
  have ht : IsOpen {x : QuadricGraphBase d i × ℝ | 0 < x.2 ∧ x.2 < 1} := by
    simpa [Set.mem_Ioo] using
      (isOpen_Ioo : IsOpen (Set.Ioo (0 : ℝ) 1)).preimage continuous_snd
  simpa [quadricPatchCylinderCoeffBase, and_assoc] using
    (hcoeff.isOpen_preimage {y : ℝ | y ≠ 0} isOpen_ne).inter ht

private theorem continuous_insertCoord {d : Nat} (i : Fin d) :
    Continuous fun x : ℝ × ({j : Fin d // j ≠ i} → ℝ) => insertCoord i x.1 x.2 := by
  rw [continuous_pi_iff]
  intro j
  by_cases hji : j = i
  · subst j
    simpa [insertCoord] using
      (continuous_fst : Continuous fun x : ℝ × ({j : Fin d // j ≠ i} → ℝ) => x.1)
  · simpa [insertCoord, hji] using
      ((continuous_apply ⟨j, hji⟩).comp
        (continuous_snd : Continuous fun x : ℝ × ({j : Fin d // j ≠ i} → ℝ) => x.2))

private theorem continuous_eraseCoord {d : Nat} (i : Fin d) :
    Continuous fun v : Fin d → ℝ => eraseCoord i v := by
  rw [continuous_pi_iff]
  intro j
  simpa [eraseCoord] using
    (continuous_apply (j : Fin d) : Continuous fun v : Fin d → ℝ => v j)

private def quadricCoeffBase {d : Nat} (A : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) :
    Set (QuadricGraphBase d i) :=
  {x | (Matrix.mulVec (Matrix.transpose A) x.1) i ≠ 0}

private theorem continuous_solvedCoordProbe_on_coeff_ne {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) :
    Continuous fun x : quadricCoeffBase A i => solvedCoordProbe A i x.1 := by
  have h_insert := continuous_insertCoord i
  have h_zero :
      Continuous fun x : quadricCoeffBase A i => insertCoord i 0 (x.1.2) :=
    h_insert.comp (continuous_const.prodMk (continuous_snd.comp continuous_subtype_val))
  have h_num :
      Continuous fun x : quadricCoeffBase A i =>
        matrixBilin A x.1.1 (insertCoord i 0 x.1.2) := by
    unfold matrixBilin
    fun_prop
  have h_den :
      Continuous fun x : quadricCoeffBase A i =>
        (Matrix.mulVec (Matrix.transpose A) x.1.1) i := by
    unfold Matrix.mulVec dotProduct
    fun_prop
  have h_solved :
      Continuous fun x : quadricCoeffBase A i => solvedCoord A i x.1.1 x.1.2 := by
    unfold solvedCoord
    exact h_num.neg.div h_den (fun x => x.2)
  unfold solvedCoordProbe
  exact (continuous_fst.comp continuous_subtype_val).prodMk
    (h_insert.comp (h_solved.prodMk (continuous_snd.comp continuous_subtype_val)))

private noncomputable def quadricPatchCylinderCoeffHomeomorph {k d : Nat}
    (A : Fin k → Matrix (Fin d) (Fin d) ℝ) (h : Fin k) (i : Fin d) :
    quadricPatchCylinderCoeff A h i ≃ₜ quadricPatchCylinderCoeffBase A h i where
  toFun := fun x =>
    let y : ProbePair d × ℝ := (x : quadricPatchCylinder A h)
    ⟨((y.1.1, eraseCoord i y.1.2), y.2), x.2, x.1.2.2.1, x.1.2.2.2⟩
  invFun := fun x =>
    let p : ProbePair d := solvedCoordProbe (A h) i x.1.1
    let y : ProbePair d × ℝ := (p, x.1.2)
    ⟨⟨y, by
        have hquad : firstHeadQuadric A h p := by
          simpa [firstHeadQuadric, firstHeadSlope] using
            matrixBilin_solvedCoordProbe (A h) (i := i) (x := x.1.1) x.2.1
        have hw_ne : p.1 ≠ 0 := by
          intro hp0
          have hw0 : x.1.1.1 = 0 := by
            simpa [p, solvedCoordProbe] using hp0
          exact x.2.1 (by simp [hw0])
        exact ⟨⟨hquad, hw_ne⟩, x.2.2.1, x.2.2.2⟩⟩, by
      simpa [y, p, quadricPatchCylinderCoeff] using x.2.1⟩
  left_inv := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    let y : ProbePair d × ℝ := (x : quadricPatchCylinder A h)
    change (solvedCoordProbe (A h) i (y.1.1, eraseCoord i y.1.2), y.2) = y
    have hquad : matrixBilin (A h) y.1.1 y.1.2 = 0 := by
      simpa [y, firstHeadQuadric, firstHeadSlope] using x.1.2.1.1
    have hprobe :
        solvedCoordProbe (A h) i (y.1.1, eraseCoord i y.1.2) = y.1 :=
      solvedCoordProbe_eq_of_quadric (A h) (i := i) (hcoeff := x.2) hquad
    exact Prod.ext hprobe rfl
  right_inv := by
    intro x
    apply Subtype.ext
    ext j <;> simp [solvedCoordProbe]
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ (fun x => by
      exact ⟨x.2, x.1.2.2.1, x.1.2.2.2⟩)
    have hAmb :
        Continuous fun x : quadricPatchCylinderCoeff A h i =>
          (((x : quadricPatchCylinder A h) : ProbePair d × ℝ)) :=
      continuous_subtype_val.comp continuous_subtype_val
    have hProbe : Continuous fun x : quadricPatchCylinderCoeff A h i =>
        (((x : quadricPatchCylinder A h) : ProbePair d × ℝ).1) :=
      continuous_fst.comp hAmb
    have hw : Continuous fun x : quadricPatchCylinderCoeff A h i =>
        (((x : quadricPatchCylinder A h) : ProbePair d × ℝ).1.1) :=
      continuous_fst.comp hProbe
    have hv : Continuous fun x : quadricPatchCylinderCoeff A h i =>
        (((x : quadricPatchCylinder A h) : ProbePair d × ℝ).1.2) :=
      continuous_snd.comp hProbe
    have ht : Continuous fun x : quadricPatchCylinderCoeff A h i =>
        (((x : quadricPatchCylinder A h) : ProbePair d × ℝ).2) :=
      continuous_snd.comp hAmb
    exact (hw.prodMk ((continuous_eraseCoord i).comp hv)).prodMk ht
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ (fun x => by
      simpa [quadricPatchCylinderCoeff] using x.2.1)
    refine Continuous.subtype_mk ?_ (fun x => by
      have hquad : firstHeadQuadric A h (solvedCoordProbe (A h) i x.1.1) := by
        simpa [firstHeadQuadric, firstHeadSlope] using
          matrixBilin_solvedCoordProbe (A h) (i := i) (x := x.1.1) x.2.1
      have hw_ne : (solvedCoordProbe (A h) i x.1.1).1 ≠ 0 := by
        intro hp0
        have hw0 : x.1.1.1 = 0 := by
          simpa [solvedCoordProbe] using hp0
        exact x.2.1 (by simp [hw0])
      exact ⟨⟨hquad, hw_ne⟩, x.2.2.1, x.2.2.2⟩)
    have hcoeffMap :
        Continuous fun x : quadricPatchCylinderCoeffBase A h i =>
          (⟨x.1.1, x.2.1⟩ : quadricCoeffBase (A h) i) := by
      exact Continuous.subtype_mk
        ((continuous_fst : Continuous fun x : QuadricGraphBase d i × ℝ => x.1).comp
          continuous_subtype_val)
        (fun x => x.2.1)
    have hprobe :
        Continuous fun x : quadricPatchCylinderCoeffBase A h i =>
          solvedCoordProbe (A h) i x.1.1 :=
      (continuous_solvedCoordProbe_on_coeff_ne (A h) i).comp hcoeffMap
    exact hprobe.prodMk
      ((continuous_snd : Continuous fun x : QuadricGraphBase d i × ℝ => x.2).comp
        continuous_subtype_val)

private theorem locallyConnectedSpace_quadricPatchCylinderCoeff {k d : Nat}
    (A : Fin k → Matrix (Fin d) (Fin d) ℝ) (h : Fin k) (i : Fin d) :
    LocallyConnectedSpace (quadricPatchCylinderCoeff A h i) := by
  have hbase_open := isOpen_quadricPatchCylinderCoeffBase A h i
  haveI : LocallyConnectedSpace (quadricPatchCylinderCoeffBase A h i) :=
    hbase_open.locallyConnectedSpace
  exact (quadricPatchCylinderCoeffHomeomorph A h i).locallyConnectedSpace

/-- The quadric-patch cylinder is locally connected when the selected attention
matrix is nonsingular. -/
theorem locallyConnectedSpace_quadricPatchCylinder_of_det_ne_zero {k d : Nat}
    (A : Fin k → Matrix (Fin d) (Fin d) ℝ) (h : Fin k)
    (hdet : (A h).det ≠ 0) :
    LocallyConnectedSpace (quadricPatchCylinder A h) := by
  rw [locallyConnectedSpace_iff_subsets_isOpen_isConnected]
  intro x S hS
  rcases exists_transpose_mulVec_ne_zero_coord_of_ne_zero (A h) hdet x.2.1.2 with
    ⟨i, hcoeff⟩
  let P : Set (quadricPatchCylinder A h) := quadricPatchCylinderCoeff A h i
  have hxP : x ∈ P := hcoeff
  have hP_open : IsOpen P := isOpen_quadricPatchCylinderCoeff A h i
  haveI : LocallyConnectedSpace P := locallyConnectedSpace_quadricPatchCylinderCoeff A h i
  have hpreS : ((↑) : P → quadricPatchCylinder A h) ⁻¹' S ∈ 𝓝 (⟨x, hxP⟩ : P) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds hS
  rcases (locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp inferInstance)
      (⟨x, hxP⟩ : P) (((↑) : P → quadricPatchCylinder A h) ⁻¹' S) hpreS with
    ⟨V, hVsub, hVopen, hxV, hVconn⟩
  refine ⟨((↑) : P → quadricPatchCylinder A h) '' V, ?_, ?_, ?_, ?_⟩
  · rintro y ⟨z, hzV, rfl⟩
    exact hVsub hzV
  · exact hP_open.isOpenMap_subtype_val V hVopen
  · exact ⟨⟨x, hxP⟩, hxV, rfl⟩
  · exact hVconn.image ((↑) : P → quadricPatchCylinder A h)
      continuous_subtype_val.continuousOn

/-- Connected components of relatively open subsets of the nonsingular
quadric-patch cylinder are relatively open in that cylinder. -/
theorem connectedComponentIn_relativelyOpenIn_quadricPatchCylinder
    {k d : Nat} {A : Fin k → Matrix (Fin d) (Fin d) ℝ} {h : Fin k}
    {O : Set (ProbePair d × ℝ)} {x0 : ProbePair d × ℝ}
    (hdet : (A h).det ≠ 0)
    (hO : RelativelyOpenIn O (quadricPatchCylinder A h)) (hx0 : x0 ∈ O) :
    RelativelyOpenIn (connectedComponentIn O x0) (quadricPatchCylinder A h) := by
  haveI : LocallyConnectedSpace (quadricPatchCylinder A h) :=
    locallyConnectedSpace_quadricPatchCylinder_of_det_ne_zero A h hdet
  exact connectedComponentIn_relativelyOpenIn_of_locallyConnected hO hx0

/-! ## `assump-sign-region-interface.S` -/

/-- Sign-region interface consumed by the dial pass. -/
structure SignRegionInterface {k d : Nat}
    (A : Fin k -> Matrix (Fin d) (Fin d) ℝ)
    (V' : Fin k -> Matrix (Fin d) (Fin d) ℝ)
    (h : Fin k) (U : Set (ProbePair d × ℝ)) : Prop where
  point_on_quadric : ∀ x ∈ U, firstHeadQuadric A h x.1
  t_pos : ∀ x ∈ U, 0 < x.2
  t_lt_one : ∀ x ∈ U, x.2 < 1
  w_ne_zero : ∀ x ∈ U, x.1.1 ≠ 0
  target_value_ne_zero : ∀ x ∈ U, V' h *ᵥ x.1.1 ≠ 0
  pi_ne_zero : ∀ x ∈ U, firstHeadPi A h x.1 ≠ 0

namespace SignRegionInterface

variable {k d : Nat}
variable {A : Fin k -> Matrix (Fin d) (Fin d) ℝ}
variable {V' : Fin k -> Matrix (Fin d) (Fin d) ℝ}
variable {h : Fin k} {U : Set (ProbePair d × ℝ)}

/-- The sign-region interface places every point in `M_h × (0,1)`. -/
theorem subset_quadricPatchCylinder (S : SignRegionInterface A V' h U) :
    U ⊆ quadricPatchCylinder A h := by
  intro x hx
  exact ⟨⟨S.point_on_quadric x hx, S.w_ne_zero x hx⟩,
    S.t_pos x hx, S.t_lt_one x hx⟩

theorem restrict {W : Set (ProbePair d × ℝ)}
    (S : SignRegionInterface A V' h U) (hsub : W ⊆ U) :
    SignRegionInterface A V' h W where
  point_on_quadric := fun x hx => S.point_on_quadric x (hsub hx)
  t_pos := fun x hx => S.t_pos x (hsub hx)
  t_lt_one := fun x hx => S.t_lt_one x (hsub hx)
  w_ne_zero := fun x hx => S.w_ne_zero x (hsub hx)
  target_value_ne_zero := fun x hx => S.target_value_ne_zero x (hsub hx)
  pi_ne_zero := fun x hx => S.pi_ne_zero x (hsub hx)

end SignRegionInterface

/-! ## `lem-quadric-patch-topology.S` and `cor-sign-region-topology.S` -/

/-- Proposition-valued API for the topology of the selected quadric patch. -/
structure QuadricPatchTopologyStatement {k d : Nat}
    (A : Fin k -> Matrix (Fin d) (Fin d) ℝ) (h : Fin k) : Prop where
  det_ne_zero : (A h).det ≠ 0
  dimension_bound : 2 ≤ d
  patch_nonempty : (quadricPatch A h).Nonempty
  cylinder_nonempty : (quadricPatchCylinder A h).Nonempty
  patch_relatively_open :
    RelativelyOpenIn (quadricPatch A h)
      {p : ProbePair d | firstHeadQuadric A h p}
  cylinder_eq_prod :
    quadricPatchCylinder A h =
      quadricPatch A h ×ˢ Set.Ioo (0 : ℝ) 1
  time_projection_open :
    ∀ U : Set (ProbePair d × ℝ),
      U.Nonempty ->
      RelativelyOpenIn U (quadricPatchCylinder A h) ->
      IsOpen (timeProjection U)
  time_projection_infinite_of_connected :
    ∀ U : Set (ProbePair d × ℝ),
      U.Nonempty ->
      RelativelyOpenIn U (quadricPatchCylinder A h) ->
      IsPreconnected U ->
      (timeProjection U).Infinite
  slice_open :
    ∀ U : Set (ProbePair d × ℝ), ∀ t : ℝ,
      RelativelyOpenIn U (quadricPatchCylinder A h) ->
      RelativelyOpenIn (timeSlice U t) (quadricPatch A h)

theorem quadricPatchTopologyStatement_of_dimension {k d : Nat}
    (A : Fin k -> Matrix (Fin d) (Fin d) ℝ) (h : Fin k)
    (hdet : (A h).det ≠ 0) (hd : 2 ≤ d) :
    QuadricPatchTopologyStatement A h where
  det_ne_zero := hdet
  dimension_bound := hd
  patch_nonempty := quadricPatch_nonempty_of_two_le A h hd
  cylinder_nonempty := quadricPatchCylinder_nonempty_of_two_le A h hd
  patch_relatively_open := relativelyOpenIn_quadricPatch_firstHeadQuadric A h
  cylinder_eq_prod := quadricPatchCylinder_eq_prod A h
  time_projection_open := fun _U _hU_nonempty hU_open =>
    timeProjection_open_of_relativelyOpenIn_quadricPatchCylinder hU_open
  time_projection_infinite_of_connected := fun _U hU_nonempty hU_open _hU_connected =>
    timeProjection_infinite_of_nonempty_relativelyOpenIn_quadricPatchCylinder
      hU_nonempty hU_open
  slice_open := fun U t hU_open =>
    timeSlice_relativelyOpenIn_of_relativelyOpenIn_quadricPatchCylinder
      (U := U) t hU_open

/-- Proposition-valued API for the topology of the sign region. -/
structure SignRegionTopologyStatement {k d : Nat}
    (A : Fin k -> Matrix (Fin d) (Fin d) ℝ)
    (V' : Fin k -> Matrix (Fin d) (Fin d) ℝ)
    (h : Fin k) (U : Set (ProbePair d × ℝ)) : Prop where
  interface : SignRegionInterface A V' h U
  nonempty : U.Nonempty
  connected : IsPreconnected U
  relatively_open : RelativelyOpenIn U (quadricPatchCylinder A h)
  time_projection_open : IsOpen (timeProjection U)
  time_projection_infinite : (timeProjection U).Infinite
  slice_open : ∀ t : ℝ, RelativelyOpenIn (timeSlice U t) (quadricPatch A h)

theorem signRegionTopologyStatement_of_relativelyOpen {k d : Nat}
    {A : Fin k -> Matrix (Fin d) (Fin d) ℝ}
    {V' : Fin k -> Matrix (Fin d) (Fin d) ℝ}
    {h : Fin k} {U : Set (ProbePair d × ℝ)}
    (S : SignRegionInterface A V' h U)
    (hU_nonempty : U.Nonempty)
    (hU_connected : IsPreconnected U)
    (hU_open : RelativelyOpenIn U (quadricPatchCylinder A h)) :
    SignRegionTopologyStatement A V' h U where
  interface := S
  nonempty := hU_nonempty
  connected := hU_connected
  relatively_open := hU_open
  time_projection_open :=
    timeProjection_open_of_relativelyOpenIn_quadricPatchCylinder hU_open
  time_projection_infinite :=
    timeProjection_infinite_of_nonempty_relativelyOpenIn_quadricPatchCylinder
      hU_nonempty hU_open
  slice_open := fun t =>
    timeSlice_relativelyOpenIn_of_relativelyOpenIn_quadricPatchCylinder t hU_open

namespace SignRegionTopologyStatement

variable {k d : Nat}
variable {A : Fin k -> Matrix (Fin d) (Fin d) ℝ}
variable {V' : Fin k -> Matrix (Fin d) (Fin d) ℝ}
variable {h : Fin k} {U W : Set (ProbePair d × ℝ)}

theorem restrict (T : SignRegionTopologyStatement A V' h U)
    (hsub : W ⊆ U)
    (hW_nonempty : W.Nonempty)
    (hW_connected : IsPreconnected W)
    (hW_open : RelativelyOpenIn W (quadricPatchCylinder A h)) :
    SignRegionTopologyStatement A V' h W :=
  signRegionTopologyStatement_of_relativelyOpen
    (T.interface.restrict hsub) hW_nonempty hW_connected hW_open

end SignRegionTopologyStatement

/-! ## `lem-poly-infinite.S` -/

/-- A real polynomial vanishes on a set. -/
def PolynomialVanishesOn (p : Polynomial ℝ) (S : Set ℝ) : Prop :=
  ∀ z ∈ S, Polynomial.eval z p = 0

/-- A real polynomial vanishing on an infinite set is the zero polynomial. -/
theorem polynomial_zero_of_infinite_roots
    (p : Polynomial ℝ) (S : Set ℝ)
    (hS : S.Infinite) (hpS : PolynomialVanishesOn p S) :
    p = 0 := by
  refine Polynomial.eq_zero_of_infinite_isRoot p (hS.mono ?_)
  intro z hz
  exact Polynomial.IsRoot.def.mpr (hpS z hz)

/-- Entrywise evaluation of a matrix with polynomial entries. -/
noncomputable def evalPolynomialMatrix {m n : Nat} (z : ℝ)
    (M : Matrix (Fin m) (Fin n) (Polynomial ℝ)) :
    Matrix (Fin m) (Fin n) ℝ :=
  fun i j => Polynomial.eval z (M i j)

/-- Matrix polynomial equality from equality on an infinite set of real evaluations. -/
theorem matrix_eq_of_infinite_eval_eq {m n : Nat}
    (M N : Matrix (Fin m) (Fin n) (Polynomial ℝ)) (S : Set ℝ)
    (hS : S.Infinite)
    (hEval : ∀ z ∈ S, evalPolynomialMatrix z M = evalPolynomialMatrix z N) :
    M = N := by
  funext i j
  apply sub_eq_zero.mp
  exact polynomial_zero_of_infinite_roots (M i j - N i j) S hS (by
    intro z hz
    have hentry : Polynomial.eval z (M i j) = Polynomial.eval z (N i j) := by
      simpa [evalPolynomialMatrix] using congrArg (fun X => X i j) (hEval z hz)
    simp [Polynomial.eval_sub, hentry])

/-- Proposition-valued API for polynomial equality from an infinite evaluation set. -/
structure PolyInfiniteStatement : Prop where
  polynomial_zero_of_infinite_roots :
    ∀ (p : Polynomial ℝ) (S : Set ℝ),
      S.Infinite ->
      PolynomialVanishesOn p S ->
      p = 0
  matrix_eq_of_infinite_eval_eq :
    ∀ {m n : Nat} (M N : Matrix (Fin m) (Fin n) (Polynomial ℝ)) (S : Set ℝ),
      S.Infinite ->
      (∀ z ∈ S, evalPolynomialMatrix z M = evalPolynomialMatrix z N) ->
      M = N

/-- Concrete proof package for `lem-poly-infinite.S`. -/
theorem polyInfiniteStatement : PolyInfiniteStatement where
  polynomial_zero_of_infinite_roots := polynomial_zero_of_infinite_roots
  matrix_eq_of_infinite_eval_eq := matrix_eq_of_infinite_eval_eq

/-! ## `def-dial-path.S` -/

/-- The TeX scalar `c=logit(t)-b`. -/
noncomputable def headDialC (b t : ℝ) : ℝ :=
  sigmoidLogit t - b

/-- The TeX dial direction `y=pi_h(w,v)/||pi_h(w,v)||^2`, using dot product norm squared. -/
noncomputable def headDialDirection {k d : Nat}
    (A : Fin k -> Matrix (Fin d) (Fin d) ℝ) (h : Fin k)
    (p : ProbePair d) : Fin d -> ℝ :=
  ((firstHeadPi A h p ⬝ᵥ firstHeadPi A h p)⁻¹) • firstHeadPi A h p

/-- The `h`-dial path based at `(p,t)`. -/
noncomputable def headDialPath {k d : Nat}
    (A : Fin k -> Matrix (Fin d) (Fin d) ℝ) (h : Fin k)
    (b : ℝ) (p : ProbePair d) (t τ : ℝ) : ProbePair d :=
  dialProbe p (headDialC b t) (headDialDirection A h p) τ

/-- Packaged dial-path inputs for a base point in the sign region. -/
structure DialPathStatement {k d : Nat}
    (A : Fin k -> Matrix (Fin d) (Fin d) ℝ)
    (V' : Fin k -> Matrix (Fin d) (Fin d) ℝ)
    (h : Fin k) (b : ℝ) (U : Set (ProbePair d × ℝ)) where
  base : ProbePair d × ℝ
  base_mem : base ∈ U
  interface : SignRegionInterface A V' h U
  path : ℝ -> ProbePair d
  path_eq : ∀ τ : ℝ, path τ = headDialPath A h b base.1 base.2 τ

/-! ## `lem-head-dial.S` -/

/-- Exponential closeness as a proposition, avoiding opaque theorem assumptions.

Used for the saturating gates (`lem:head-dial`(iv)/(v)), which decay to `1` at the
genuinely *exponential* rate `e^{-b}e^{-η'τ/2}`. -/
def ExpCloseTo (f : ℝ -> ℝ) (a : ℝ) : Prop :=
  ∃ rate coeff start : ℝ,
    0 < rate ∧ 0 ≤ coeff ∧
      ∀ τ : ℝ, start ≤ τ -> |f τ - a| ≤ coeff * Real.exp (-rate * τ)

/-- Algebraic `O(1/τ)` closeness as a proposition (matching `lem:head-dial`(iii)).

The dialed head gate tracks its target only at the *algebraic* rate `coeff/τ`, not
exponentially; this predicate records exactly that decay. -/
def AlgCloseTo (f : ℝ -> ℝ) (a : ℝ) : Prop :=
  ∃ coeff start : ℝ,
    0 ≤ coeff ∧ 1 ≤ start ∧
      ∀ τ : ℝ, start ≤ τ -> |f τ - a| ≤ coeff / τ

/-- Constants and margins displayed in the head-dial lemma. -/
structure HeadDialConstants where
  cMax : ℝ
  piMin : ℝ
  rho : ℝ
  threshold : ℝ
  coeff : ℝ
  cMax_nonneg : 0 ≤ cMax
  piMin_pos : 0 < piMin
  rho_pos : 0 < rho
  threshold_ge_one : 1 ≤ threshold
  coeff_nonneg : 0 ≤ coeff

/-- Gate values along a k-head dial path.

The first index is a zero-based layer and the second is the head in that layer.
-/
abbrev KHeadGateAlongBase (k d : Nat) :=
  Nat -> Fin k -> ProbePair d × ℝ -> ℝ -> ℝ

/-- Data/API record for the head-dial estimates. -/
structure HeadDialStatement {k d : Nat}
    (A : Fin k -> Matrix (Fin d) (Fin d) ℝ)
    (V' : Fin k -> Matrix (Fin d) (Fin d) ℝ)
    (h : Fin k) (b : ℝ) (U K : Set (ProbePair d × ℝ))
    (unprimed primed : KHeadGateAlongBase k d) where
  interface : SignRegionInterface A V' h U
  compact_base : IsCompact K
  nonempty_base : K.Nonempty
  base_subset : K ⊆ U
  constants : HeadDialConstants
  exact_dial_identity :
    ∀ x ∈ K, ∀ τ : ℝ, τ ≠ 0 ->
      τ * firstHeadSlope A h (headDialPath A h b x.1 x.2 τ) + b =
        headDialC b x.2 + b -
          (headDialC b x.2) ^ 2 *
            matrixBilin (A h) (headDialDirection A h x.1)
              (headDialDirection A h x.1) / τ
  dial_gate_tracks :
    ∀ x ∈ K, AlgCloseTo (fun τ => unprimed 0 h x τ) x.2 ∧
      (∀ τ : ℝ, unprimed 0 h x τ = primed 0 h x τ)
  nondial_first_gates_saturate :
    ∀ a : Fin k, a ≠ h ->
      ∀ x ∈ K, ExpCloseTo (fun τ => unprimed 0 a x τ) 1 ∧
        ExpCloseTo (fun τ => primed 0 a x τ) 1
  primed_deeper_gates_saturate :
    ∀ level : Nat, 1 ≤ level ->
      ∀ a : Fin k, ∀ x ∈ K,
        ExpCloseTo (fun τ => primed level a x τ) 1

/-! ### `lem:head-dial` core estimates (proved)

The mathematical content of parts (i)–(iii) of `lem:head-dial`, as genuine
theorems.  Parts (iv)/(v) (nondial/deeper gate saturation) require the concrete
probe-recursion gate functions and are scoped separately. -/

/-- **Exact dial identity** (`eq:dial-exact`, `lem:head-dial`(i)).

At a base point on the selected head's quadric (`firstHeadSlope A h p = 0`) with
nonvanishing dial covector (`firstHeadPi A h p ≠ 0`), the rescaled dialed head slope
equals `logit t` up to an *exact* `O(1/τ)` correction, whose coefficient is the
quadratic form of the (normalised) dial direction.  The identity holds for every
`τ ≠ 0`. -/
theorem headDial_exact_identity {k d : Nat}
    (A : Fin k -> Matrix (Fin d) (Fin d) ℝ) (h : Fin k) (b t : ℝ)
    (p : ProbePair d)
    (hq : firstHeadSlope A h p = 0)
    (hpi : firstHeadPi A h p ≠ 0)
    {τ : ℝ} (hτ : τ ≠ 0) :
    τ * firstHeadSlope A h (headDialPath A h b p t τ) + b =
      sigmoidLogit t -
        (headDialC b t) ^ 2 *
          matrixBilin (A h) (headDialDirection A h p) (headDialDirection A h p) / τ := by
  -- The dial direction `y = π/‖π‖²` is normalised: `y ⬝ᵥ π = 1`.
  have hself_ne : firstHeadPi A h p ⬝ᵥ firstHeadPi A h p ≠ 0 :=
    fun hzero => hpi (dotProduct_self_eq_zero.mp hzero)
  have hnorm : headDialDirection A h p ⬝ᵥ firstHeadPi A h p = 1 := by
    simp only [headDialDirection, smul_dotProduct, smul_eq_mul]
    exact inv_mul_cancel₀ hself_ne
  -- Base point lies on the quadric.
  have hquad0 : p.1 ⬝ᵥ (A h) *ᵥ p.2 = 0 := by
    simpa [firstHeadSlope, matrixBilin] using hq
  -- The linear-in-(c/τ) coefficient is `y ⬝ᵥ π = 1`.
  have htranspose : p.1 ⬝ᵥ (A h) *ᵥ headDialDirection A h p
      = headDialDirection A h p ⬝ᵥ (A h)ᵀ *ᵥ p.1 :=
    dotProduct_mulVec_eq_dotProduct_transpose_mulVec (A h) p.1 (headDialDirection A h p)
  have hlinear : p.1 ⬝ᵥ (A h) *ᵥ headDialDirection A h p
      - headDialDirection A h p ⬝ᵥ (A h) *ᵥ p.2 = 1 := by
    rw [htranspose]
    simpa [firstHeadPi, firstLayerPi, dotProduct_sub] using hnorm
  -- `c + b = logit t`.
  have hcb : headDialC b t + b = sigmoidLogit t := by
    rw [headDialC]; ring
  rw [← hcb]
  simp only [firstHeadSlope, headDialPath, dialProbe, dialW, dialV, matrixBilin,
    Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, sub_dotProduct,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [hquad0]
  field_simp [hτ]
  linear_combination τ * (headDialC b t) * hlinear

/-- **Dial-gate tracking** (`lem:head-dial`(iii)).

The dialed head gate `s_{1h}(τ) = σ(τ q_h(w(τ),v(τ)) + b)` tracks its free target
`t ∈ (0,1)` at the *algebraic* rate `C/τ` (not exponentially), with the explicit
nonnegative coefficient `c² |yᵀ A_h y| / 4`.  Packaged as `AlgCloseTo`. -/
theorem headDial_gate_tracks {k d : Nat}
    (A : Fin k -> Matrix (Fin d) (Fin d) ℝ) (h : Fin k) (b t : ℝ)
    (p : ProbePair d)
    (ht_pos : 0 < t) (ht_lt_one : t < 1)
    (hq : firstHeadSlope A h p = 0)
    (hpi : firstHeadPi A h p ≠ 0) :
    AlgCloseTo
      (fun τ => sig (τ * firstHeadSlope A h (headDialPath A h b p t τ) + b)) t := by
  refine ⟨(headDialC b t) ^ 2 *
      |matrixBilin (A h) (headDialDirection A h p) (headDialDirection A h p)| / 4,
    1, by positivity, le_refl 1, ?_⟩
  intro τ hτ
  have hτ0 : (0 : ℝ) < τ := lt_of_lt_of_le zero_lt_one hτ
  have hτne : τ ≠ 0 := ne_of_gt hτ0
  have hid := headDial_exact_identity A h b t p hq hpi hτne
  -- Sigmoid is `¼`-Lipschitz and `t = σ(logit t)`.
  have hstep :
      |sig (τ * firstHeadSlope A h (headDialPath A h b p t τ) + b) - t|
        ≤ |(τ * firstHeadSlope A h (headDialPath A h b p t τ) + b) - sigmoidLogit t| / 4 := by
    have hL := abs_sig_sub_sig_le
      (τ * firstHeadSlope A h (headDialPath A h b p t τ) + b) (sigmoidLogit t)
    rwa [sig_sigmoidLogit ht_pos ht_lt_one] at hL
  -- The gate-argument deviation is exactly the `O(1/τ)` term of (i).
  have hdiff :
      (τ * firstHeadSlope A h (headDialPath A h b p t τ) + b) - sigmoidLogit t
        = -((headDialC b t) ^ 2 *
            matrixBilin (A h) (headDialDirection A h p) (headDialDirection A h p) / τ) := by
    rw [hid]; ring
  calc
    |sig (τ * firstHeadSlope A h (headDialPath A h b p t τ) + b) - t|
        ≤ |(τ * firstHeadSlope A h (headDialPath A h b p t τ) + b) - sigmoidLogit t| / 4 := hstep
    _ = (headDialC b t) ^ 2 *
          |matrixBilin (A h) (headDialDirection A h p) (headDialDirection A h p)| / 4 / τ := by
        rw [hdiff, abs_neg, abs_div, abs_mul,
          abs_of_nonneg (sq_nonneg (headDialC b t)), abs_of_pos hτ0]
        ring

/-- **Probe motion** (`lem:head-dial`(ii)), component-exact form.

Each token component of the `h`-dial probe moves off the base point by exactly
`|c|‖y‖/τ` (with `c = headDialC b t`, `y = headDialDirection A h p`).  This is the
honest per-coordinate displacement; the aggregate `√2` prefactor of the TeX bound is
a Euclidean-product-norm convention (the ambient product carries the sup norm here),
so the coordinatewise equalities are the norm-agnostic statement. -/
theorem headDial_probe_motion {k d : Nat}
    (A : Fin k -> Matrix (Fin d) (Fin d) ℝ) (h : Fin k) (b t : ℝ)
    (p : ProbePair d) {τ : ℝ} (hτ : 0 < τ) :
    ‖(headDialPath A h b p t τ).1 - p.1‖
        = |headDialC b t| / τ * ‖headDialDirection A h p‖
      ∧ ‖(headDialPath A h b p t τ).2 - p.2‖
        = |headDialC b t| / τ * ‖headDialDirection A h p‖ := by
  have hw : (headDialPath A h b p t τ).1
      = p.1 - (headDialC b t / τ) • headDialDirection A h p := rfl
  have hv : (headDialPath A h b p t τ).2
      = p.2 + (headDialC b t / τ) • headDialDirection A h p := rfl
  refine ⟨?_, ?_⟩
  · rw [hw]
    have hsub : p.1 - (headDialC b t / τ) • headDialDirection A h p - p.1
        = -((headDialC b t / τ) • headDialDirection A h p) := by abel
    rw [hsub, norm_neg, norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hτ]
  · rw [hv]
    have hsub : p.2 + (headDialC b t / τ) • headDialDirection A h p - p.2
        = (headDialC b t / τ) • headDialDirection A h p := by abel
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hτ]

/-! ## `K07A.M5`: sign-region genericity input (`SignRegionData`) adapters

The genericity development produces a `SignRegionData θ h` witness (from an
`AnchorHeadCertificate`, itself obtained on the generic parameter set).  For the
layer-0 attention/value matrices this witness supplies exactly the data the dial
pass consumes: it lands in the selected quadric slab, it is nonempty, connected,
and relatively open inside `M_h × (0,1)`, and carries the three transversality
nonvanishing facts.  The lemmas below convert that single hypothesis `D` into the
`SignRegionInterface`, `SignRegionTopologyStatement`, and `DialPathStatement`
records of this file. -/

section SignRegionDataAdapters

variable {m k d : Nat} {θ : Params (m + 1) k d} {h : Fin k}

/-- For the layer-0 attention matrices, the dial-vector `firstHeadPi` is exactly
the genericity dial covector `π'_h(w,v)=A_h^T w-A_h v`. -/
theorem firstHeadPi_eq_dialCovector (p : ProbePair d) :
    firstHeadPi (attentionMatrix θ 0) h p = dialCovector θ h p.1 p.2 :=
  rfl

/-- The genericity sign region `D.region` meets the dial-pass sign-region
interface for `(A,V') = (attentionMatrix θ 0, valueMatrix θ 0)`. -/
theorem signRegionData_signRegionInterface (D : SignRegionData θ h) :
    SignRegionInterface (attentionMatrix θ 0) (valueMatrix θ 0) h D.region where
  point_on_quadric := fun _ hx => (D.region_subset_slab hx).1
  t_pos := fun _ hx => (D.region_subset_slab hx).2.1
  t_lt_one := fun _ hx => (D.region_subset_slab hx).2.2
  w_ne_zero := fun _ hx => (D.transversality_nonzero hx).2.2
  target_value_ne_zero := fun _ hx => (D.transversality_nonzero hx).2.1
  pi_ne_zero := fun _ hx => by
    rw [firstHeadPi_eq_dialCovector]
    exact (D.transversality_nonzero hx).1

/-- The selected quadric-patch cylinder is the sign-region slab cut by `w ≠ 0`. -/
theorem quadricPatchCylinder_eq_slab_inter_wne :
    quadricPatchCylinder (attentionMatrix θ 0) h
      = signRegionSlab θ h ∩ {p : SignRegionPoint d | p.1.1 ≠ 0} := by
  ext p
  simp only [quadricPatchCylinder, quadricPatch, firstHeadQuadric, firstHeadSlope,
    signRegionSlab, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Ioo]
  tauto

/-- The genericity sign region is relatively open inside the quadric-patch
cylinder, witnessed by the ambient box of the sign-region chart. -/
theorem signRegionData_relativelyOpenIn_quadricPatchCylinder
    (D : SignRegionData θ h) :
    RelativelyOpenIn D.region (quadricPatchCylinder (attentionMatrix θ 0) h) := by
  refine ⟨signRegionAmbientBox D.pivot D.center.w0 D.vHat D.center.t D.rho,
    isOpen_signRegionAmbientBox D.pivot D.center.w0 D.vHat D.center.t D.rho, ?_⟩
  rw [quadricPatchCylinder_eq_slab_inter_wne]
  ext p
  constructor
  · intro hp
    have htrans := D.transversality_nonzero hp
    rw [D.ambient_identity] at hp
    exact ⟨hp.2, hp.1, htrans.2.2⟩
  · intro hp
    rw [D.ambient_identity]
    exact ⟨hp.2.1, hp.1⟩

/-- The genericity sign region satisfies the full sign-region topology package. -/
theorem signRegionData_signRegionTopologyStatement (D : SignRegionData θ h) :
    SignRegionTopologyStatement (attentionMatrix θ 0) (valueMatrix θ 0) h D.region :=
  signRegionTopologyStatement_of_relativelyOpen
    (signRegionData_signRegionInterface D)
    D.nonempty
    D.region_connected
    (signRegionData_relativelyOpenIn_quadricPatchCylinder D)

/-- The genericity sign region packages a dial-path statement based at the pinned
center point, for any base logit shift `b`. -/
noncomputable def signRegionData_dialPathStatement (b : ℝ) (D : SignRegionData θ h) :
    DialPathStatement (attentionMatrix θ 0) (valueMatrix θ 0) h b D.region where
  base := D.center.point
  base_mem := D.center_mem_region
  interface := signRegionData_signRegionInterface D
  path := fun τ =>
    headDialPath (attentionMatrix θ 0) h b D.center.point.1 D.center.point.2 τ
  path_eq := fun _ => rfl

end SignRegionDataAdapters

/-! ## Path-T Lane A: attention transport congruences

The sign-region geometry objects (`firstHeadSlope`, `firstHeadQuadric`,
`firstHeadPi`, `quadricPatch`, `quadricPatchCylinder`) depend on the attention
family `A : Fin k → Matrix (Fin d) (Fin d) ℝ` ONLY through the selected head
`A h`.  Likewise `SignRegionInterface`/`SignRegionTopologyStatement` touch `A`
only through those geometry objects (the value-matrix parameter `V'` is carried
free).  The lemmas below transport each of these across an equality of the
selected head `A h = A' h`, keeping `V'` untouched.  This lets a downstream file
build a source sign-region witness from a target `SignRegionData θ' h` by
rewriting `attentionMatrix (relabelFirstLayer θ σ) 0 = attentionMatrix θ' 0`
(apply `congrFun` at the head to obtain the `A h = A' h` hypothesis). -/

section AttentionTransport

variable {k d : Nat}
variable {A A' : Fin k -> Matrix (Fin d) (Fin d) ℝ}
variable {V' : Fin k -> Matrix (Fin d) (Fin d) ℝ}
variable {h : Fin k} {U : Set (ProbePair d × ℝ)}

/-- The first-layer slope depends on the attention family only through `A h`. -/
theorem firstHeadSlope_congr (hA : A h = A' h) :
    firstHeadSlope A h = firstHeadSlope A' h := by
  funext p
  unfold firstHeadSlope
  rw [hA]

/-- The selected first-head quadric depends on the attention family only through
`A h`. -/
theorem firstHeadQuadric_congr (hA : A h = A' h) :
    firstHeadQuadric A h = firstHeadQuadric A' h := by
  funext p
  unfold firstHeadQuadric
  rw [firstHeadSlope_congr hA]

/-- The selected first-head dial vector depends on the attention family only
through `A h`. -/
theorem firstHeadPi_congr (hA : A h = A' h) :
    firstHeadPi A h = firstHeadPi A' h := by
  funext p
  unfold firstHeadPi
  rw [hA]

/-- The quadric patch depends on the attention family only through `A h`. -/
theorem quadricPatch_congr (hA : A h = A' h) :
    quadricPatch A h = quadricPatch A' h := by
  unfold quadricPatch
  rw [firstHeadQuadric_congr hA]

/-- The quadric-patch cylinder depends on the attention family only through
`A h`. -/
theorem quadricPatchCylinder_congr (hA : A h = A' h) :
    quadricPatchCylinder A h = quadricPatchCylinder A' h := by
  unfold quadricPatchCylinder
  rw [quadricPatch_congr hA]

/-- Transport a `SignRegionInterface` across an equality of the selected head,
keeping the value-matrix parameter `V'` free. -/
theorem SignRegionInterface.congr_attention (hA : A h = A' h)
    (S : SignRegionInterface A' V' h U) :
    SignRegionInterface A V' h U where
  point_on_quadric := fun x hx => by
    rw [firstHeadQuadric_congr hA]; exact S.point_on_quadric x hx
  t_pos := S.t_pos
  t_lt_one := S.t_lt_one
  w_ne_zero := S.w_ne_zero
  target_value_ne_zero := S.target_value_ne_zero
  pi_ne_zero := fun x hx => by
    rw [firstHeadPi_congr hA]; exact S.pi_ne_zero x hx

/-- Transport a `SignRegionTopologyStatement` across an equality of the selected
head, keeping the value-matrix parameter `V'` free.  The topology package is
re-derived via `signRegionTopologyStatement_of_relativelyOpen` to avoid motive
issues from rewriting inside the structure. -/
theorem SignRegionTopologyStatement.congr_attention (hA : A h = A' h)
    (T : SignRegionTopologyStatement A' V' h U) :
    SignRegionTopologyStatement A V' h U :=
  signRegionTopologyStatement_of_relativelyOpen
    (T.interface.congr_attention hA)
    T.nonempty
    T.connected
    (by rw [quadricPatchCylinder_congr hA]; exact T.relatively_open)

end AttentionTransport

end TransformerIdentifiability.NLayer.KHead
