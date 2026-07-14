import AnyLayerIdentifiabilityProof.NLayer.KHead.Probe
import AnyLayerIdentifiabilityProof.NLayer.KHead.Step2.Trichotomy
import AnyLayerIdentifiabilityProof.NLayer.KHead.Step2.Dial
import AnyLayerIdentifiabilityProof.NLayer.KHead.Step2.DialLimits

set_option autoImplicit false

open Matrix Filter Topology
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.KHead

/-!
# K-head Step 2 saturated limits scaffold

This file is the K07C statement/API scaffold for the 07c fragments
`tex_modular/sections/07c1-telescoping.tex`, `07c2-saturated-limit.tex`, and
`07c3-slices-first-values.tex`.  The hard saturated-limit,
slice-rigidity, and first-value identification arguments remain represented as
Prop-valued interfaces until the K07B-gated trichotomy inputs are available.
-/

/-! ## Label and saturated-tail definitions -/

/-- The three allowed saturated constants `{0, 1, alpha}` for a fixed `r`. -/
def IsSaturatedLabel (r : Nat) (z : ℝ) : Prop :=
  z = 0 ∨ z = 1 ∨ z = alpha r

/-- A deeper-layer label tuple, indexed by TeX layer number and head. -/
abbrev SaturatedLabels (k : Nat) : Type :=
  Nat -> Fin k -> ℝ

/-! ## Trichotomy → saturated labels adapter

The K07B trichotomy (`Step2/Trichotomy.lean`) produces its output as a total map
`labels : DeeperHead → TrichotomyLabel` over the abstract deeper-head index type.
The K07C saturated-tail machinery above instead consumes numeric labels through
`SaturatedLabels k = Nat → Fin k → ℝ`.  The adapter below is the formal bridge
between the two.

Index convention (documented deliberately, verified against `deeperHeadOrder` and
`IsDeeperHead` in `Step2/Trichotomy.lean`):

* `DeeperHead` is **1-based**: `IsDeeperHead L k h` requires `2 ≤ h.layer ≤ L` and
  `1 ≤ h.head ≤ k`, and `deeperHeadOrder` enumerates `⟨layerOffset + 2, headOffset + 1⟩`.
* `SaturatedLabels k = Nat → Fin k → ℝ` is consumed by `saturatedTailD`/`saturatedE`
  with the first `Nat` argument used **directly** as the TeX layer number `ℓ`
  (layers range over `Finset.Icc 2 L` there) and the second `Fin k` argument as the
  **0-based** head index.

Hence the slot `(l : Nat, a : Fin k)` of `SaturatedLabels` corresponds to the
deeper head `⟨l, (a : Nat) + 1⟩`:

* TeX layer `ℓ = l` maps to `DeeperHead.layer = l` (identity on the layer index), and
* TeX head `b = (a : Nat) + 1` maps to `DeeperHead.head` (0-based `Fin k` slot `a`
  shifted to the 1-based head number `a + 1`).

Each trichotomy label is then evaluated to its numeric constant via
`TrichotomyLabel.eval 0 1 (alpha r)`, matching `IsSaturatedLabel r`. -/
noncomputable def trichotomyToSaturatedLabels (r _L k : Nat)
    (labels : DeeperHead → TrichotomyLabel) : SaturatedLabels k :=
  fun l a => (labels ⟨l, (a : Nat) + 1⟩).eval 0 1 (alpha r)

/-- Wellformedness of the adapter: every value produced by
`trichotomyToSaturatedLabels` is one of the three saturated constants
`{0, 1, alpha r}`, i.e. satisfies `IsSaturatedLabel r`. -/
theorem isSaturatedLabel_trichotomyToSaturatedLabels (r L k : Nat)
    (labels : DeeperHead → TrichotomyLabel) (l : Nat) (a : Fin k) :
    IsSaturatedLabel r (trichotomyToSaturatedLabels r L k labels l a) := by
  simp only [trichotomyToSaturatedLabels, IsSaturatedLabel]
  cases labels ⟨l, (a : Nat) + 1⟩ with
  | zero => simp
  | one => simp
  | alpha => simp

/-- Generic pointwise rewrite for the trichotomy-to-saturated label adapter. -/
theorem trichotomyToSaturatedLabels_eq_of_label (r L k : Nat)
    (labels : DeeperHead → TrichotomyLabel) (l : Nat) (a : Fin k)
    {label : TrichotomyLabel}
    (hlabel : labels ⟨l, (a : Nat) + 1⟩ = label) :
    trichotomyToSaturatedLabels r L k labels l a =
      label.eval 0 1 (alpha r) := by
  simp [trichotomyToSaturatedLabels, hlabel]

@[simp]
theorem trichotomyToSaturatedLabels_eq_zero_of_label_zero (r L k : Nat)
    (labels : DeeperHead → TrichotomyLabel) (l : Nat) (a : Fin k)
    (hlabel : labels ⟨l, (a : Nat) + 1⟩ = TrichotomyLabel.zero) :
    trichotomyToSaturatedLabels r L k labels l a = 0 := by
  simpa using trichotomyToSaturatedLabels_eq_of_label r L k labels l a hlabel

@[simp]
theorem trichotomyToSaturatedLabels_eq_one_of_label_one (r L k : Nat)
    (labels : DeeperHead → TrichotomyLabel) (l : Nat) (a : Fin k)
    (hlabel : labels ⟨l, (a : Nat) + 1⟩ = TrichotomyLabel.one) :
    trichotomyToSaturatedLabels r L k labels l a = 1 := by
  simpa using trichotomyToSaturatedLabels_eq_of_label r L k labels l a hlabel

@[simp]
theorem trichotomyToSaturatedLabels_eq_alpha_of_label_alpha (r L k : Nat)
    (labels : DeeperHead → TrichotomyLabel) (l : Nat) (a : Fin k)
    (hlabel : labels ⟨l, (a : Nat) + 1⟩ = TrichotomyLabel.alpha) :
    trichotomyToSaturatedLabels r L k labels l a = alpha r := by
  simpa using trichotomyToSaturatedLabels_eq_of_label r L k labels l a hlabel

/-- TeX `C_l = I + sum_a V_{la}` for a supplied value stream. -/
noncomputable def saturatedC {k d : Nat}
    (V : Nat -> Fin k -> Matrix (Fin d) (Fin d) ℝ) (l : Nat) :
    Matrix (Fin d) (Fin d) ℝ :=
  1 + ∑ a : Fin k, V l a

/-- TeX `D_l = sum_a zeta_{la} V_{la}` for the saturated tail. -/
noncomputable def saturatedTailD {k d : Nat}
    (V : Nat -> Fin k -> Matrix (Fin d) (Fin d) ℝ)
    (zeta : SaturatedLabels k) (l : Nat) :
    Matrix (Fin d) (Fin d) ℝ :=
  ∑ a : Fin k, zeta l a • V l a

/-- TeX `K_l = C_l - D_l`. -/
noncomputable def saturatedKLayer {k d : Nat}
    (V : Nat -> Fin k -> Matrix (Fin d) (Fin d) ℝ)
    (zeta : SaturatedLabels k) (l : Nat) :
    Matrix (Fin d) (Fin d) ℝ :=
  saturatedC V l - saturatedTailD V zeta l

/-- TeX product `C_{L:2}` with the packet's natural-number layer convention. -/
noncomputable def saturatedM {d : Nat}
    (C : Nat -> Matrix (Fin d) (Fin d) ℝ) (L : Nat) :
    Matrix (Fin d) (Fin d) ℝ :=
  layerProduct C L 2

/-- TeX sum `sum_{j=2}^L C_{L:j+1} D_j K_{j-1:2}`. -/
noncomputable def saturatedE {d : Nat}
    (C D KLayer : Nat -> Matrix (Fin d) (Fin d) ℝ) (L : Nat) :
    Matrix (Fin d) (Fin d) ℝ :=
  Finset.sum (Finset.Icc 2 L) fun j =>
    layerProduct C L (j + 1) * D j * layerProduct KLayer (j - 1) 2

/-- TeX `K = M - E` for the saturated tail. -/
noncomputable def saturatedTailK {d : Nat}
    (M E : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  M - E

/-- A constructor-friendly package for the constant saturated tail matrices. -/
structure SaturatedTailData (d : Nat) where
  C : Nat -> Matrix (Fin d) (Fin d) ℝ
  D : Nat -> Matrix (Fin d) (Fin d) ℝ
  KLayer : Nat -> Matrix (Fin d) (Fin d) ℝ
  M : Matrix (Fin d) (Fin d) ℝ
  E : Matrix (Fin d) (Fin d) ℝ
  K : Matrix (Fin d) (Fin d) ℝ

/-! ## First-layer saturated limit expressions -/

/-- Sum of all first-layer value matrices except the fixed dialed head. -/
noncomputable def valueSumExceptHead {k d : Nat}
    (V : Fin k -> Matrix (Fin d) (Fin d) ℝ) (h : Fin k) :
    Matrix (Fin d) (Fin d) ℝ :=
  Finset.sum ((Finset.univ : Finset (Fin k)).filter fun a => a ≠ h) fun a => V a

/-- TeX `C_1 = I + S_h + V_h`. -/
noncomputable def firstLayerCForHead {k d : Nat}
    (V : Fin k -> Matrix (Fin d) (Fin d) ℝ) (h : Fin k) :
    Matrix (Fin d) (Fin d) ℝ :=
  1 + valueSumExceptHead V h + V h

/-- TeX `w_1^infty = (I + (1 - t) V_h) w`. -/
noncomputable def firstLayerWLimit {d : Nat}
    (Vh : Matrix (Fin d) (Fin d) ℝ) (t : ℝ) (p : ProbePoint d) :
    Vec d :=
  (1 + (1 - t) • Vh) *ᵥ p.1

/-- TeX `v_1^infty = C_1 v + (S_h + t V_h) w`. -/
noncomputable def firstLayerVLimit {d : Nat}
    (C1 S Vh : Matrix (Fin d) (Fin d) ℝ) (t : ℝ) (p : ProbePoint d) :
    Vec d :=
  C1 *ᵥ p.2 + (S + t • Vh) *ᵥ p.1

/-- TeX unprimed saturated limit vector `B_h(w,v,t)`. -/
noncomputable def unprimedSaturatedLimitVector {d : Nat}
    (M E K S Vh C1 : Matrix (Fin d) (Fin d) ℝ)
    (t : ℝ) (p : ProbePoint d) :
    Vec d :=
  (M * C1) *ᵥ p.2 +
    (M * S + E * (1 + Vh) + t • (K * Vh)) *ᵥ p.1

/-- TeX primed saturated limit vector `B'_h(w,v,t)`. -/
noncomputable def primedSaturatedLimitVector {d : Nat}
    (M' C1' Vh' : Matrix (Fin d) (Fin d) ℝ)
    (t : ℝ) (p : ProbePoint d) :
    Vec d :=
  (M' * C1') *ᵥ p.2 +
    (M' * C1' - 1 - Vh' + t • Vh') *ᵥ p.1

/-! ## TeX statement boxes as APIs -/

/-- `hyp-w-nonzero.S`: nonvanishing of `V'_h w`, and hence `w`, on `Ustar`. -/
def hyp_w_nonzero_S {d : Nat}
    (Ustar : Set (ProbePoint d × ℝ))
    (Vh' : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∀ x : ProbePoint d × ℝ, x ∈ Ustar -> Vh' *ᵥ x.1.1 ≠ 0 ∧ x.1.1 ≠ 0

/-- Immediate consequence of `hyp_w_nonzero_S` used by the slice API. -/
theorem hyp_w_nonzero_S.left_ne_zero {d : Nat}
    {Ustar : Set (ProbePoint d × ℝ)}
    {Vh' : Matrix (Fin d) (Fin d) ℝ}
    (H : hyp_w_nonzero_S Ustar Vh') {x : ProbePoint d × ℝ}
    (hx : x ∈ Ustar) :
    x.1.1 ≠ 0 :=
  (H x hx).2

/-- `lem-telescoping.S`: noncommutative telescoping identity, statement form only. -/
def lem_telescoping_S {d : Nat} (n : Nat)
    (C KLayer : Nat -> Matrix (Fin d) (Fin d) ℝ) : Prop :=
  layerProduct C n 2 - layerProduct KLayer n 2 =
    Finset.sum (Finset.Icc 2 n) fun j =>
      layerProduct C n (j + 1) * (C j - KLayer j) *
        layerProduct KLayer (j - 1) 2

/-- Extend a layer product by one top factor. -/
private theorem layerProduct_succ_left {d : Nat}
    (M : Nat -> Matrix (Fin d) (Fin d) ℝ) {j i : Nat} (hi : i ≤ j + 1) :
    layerProduct M (j + 1) i = M (j + 1) * layerProduct M j i := by
  by_cases hji : j < i
  · have hsucc : j + 1 ≤ i := Nat.succ_le_of_lt hji
    have hi_eq : i = j + 1 := Nat.le_antisymm hi hsucc
    subst i
    simp
  · have hnot : ¬ j + 1 < i := not_lt_of_ge hi
    have hle : i ≤ j := Nat.le_of_not_gt hji
    have hlen : j + 1 - i + 1 = (j - i + 1) + 1 := by omega
    have hidx : i + (j - i + 1) = j + 1 := by omega
    simp [layerProduct, hnot, hji, hlen, hidx]

/-- Concrete proof of `lem-telescoping.S` for the file's `layerProduct` convention. -/
theorem lem_telescoping_S.holds {d : Nat} (n : Nat)
    (C KLayer : Nat -> Matrix (Fin d) (Fin d) ℝ) :
    lem_telescoping_S n C KLayer := by
  induction n with
  | zero =>
      simp [lem_telescoping_S]
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        simp [lem_telescoping_S]
      · unfold lem_telescoping_S at ih ⊢
        have h2 : 2 ≤ n + 1 := by omega
        let f : Nat -> Matrix (Fin d) (Fin d) ℝ := fun j =>
          layerProduct C (n + 1) (j + 1) * (C j - KLayer j) *
            layerProduct KLayer (j - 1) 2
        calc
          layerProduct C (n + 1) 2 - layerProduct KLayer (n + 1) 2
              = C (n + 1) * layerProduct C n 2 -
                  KLayer (n + 1) * layerProduct KLayer n 2 := by
                rw [layerProduct_succ_left C (j := n) (i := 2) h2,
                  layerProduct_succ_left KLayer (j := n) (i := 2) h2]
          _ = C (n + 1) * (layerProduct C n 2 - layerProduct KLayer n 2) +
                (C (n + 1) - KLayer (n + 1)) * layerProduct KLayer n 2 := by
                noncomm_ring
          _ = C (n + 1) *
                (Finset.sum (Finset.Icc 2 n) fun j =>
                  layerProduct C n (j + 1) * (C j - KLayer j) *
                    layerProduct KLayer (j - 1) 2) +
                (C (n + 1) - KLayer (n + 1)) * layerProduct KLayer n 2 := by
                rw [ih]
          _ = (Finset.sum (Finset.Icc 2 n) f) +
                (C (n + 1) - KLayer (n + 1)) * layerProduct KLayer n 2 := by
                rw [Finset.mul_sum]
                apply congrArg (fun x => x +
                  (C (n + 1) - KLayer (n + 1)) * layerProduct KLayer n 2)
                apply Finset.sum_congr rfl
                intro j hj
                have hjle : j + 1 ≤ n + 1 := by
                  have hj' := (Finset.mem_Icc.mp hj).2
                  omega
                dsimp [f]
                rw [layerProduct_succ_left C (j := n) (i := j + 1) hjle]
                noncomm_ring
          _ = Finset.sum (Finset.Icc 2 (n + 1)) f := by
                rw [Finset.sum_Icc_succ_top h2]
                dsimp [f]
                simp

/-- Saturated-tail specialization of telescoping when `D_j = C_j - K_j` on the tail. -/
theorem saturatedK_eq_layerProduct_of_sub_eq {d : Nat}
    (C D KLayer : Nat -> Matrix (Fin d) (Fin d) ℝ) (L : Nat)
    (hD : ∀ j : Nat, j ∈ Finset.Icc 2 L -> D j = C j - KLayer j) :
    saturatedTailK (saturatedM C L) (saturatedE C D KLayer L) =
      layerProduct KLayer L 2 := by
  unfold saturatedTailK saturatedM saturatedE
  have htel := lem_telescoping_S.holds L C KLayer
  unfold lem_telescoping_S at htel
  have hE : (Finset.sum (Finset.Icc 2 L) fun j =>
      layerProduct C L (j + 1) * D j * layerProduct KLayer (j - 1) 2) =
      Finset.sum (Finset.Icc 2 L) fun j =>
        layerProduct C L (j + 1) * (C j - KLayer j) *
          layerProduct KLayer (j - 1) 2 := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hD j hj]
  rw [hE]
  rw [← htel]
  abel

/-- For the saturated definitions above, the aggregate `K = M - E` is the tail product. -/
theorem saturatedK_eq_layerProduct {k d : Nat}
    (V : Nat -> Fin k -> Matrix (Fin d) (Fin d) ℝ)
    (zeta : SaturatedLabels k) (L : Nat) :
    saturatedTailK (saturatedM (saturatedC V) L)
        (saturatedE (saturatedC V) (saturatedTailD V zeta) (saturatedKLayer V zeta) L) =
      layerProduct (saturatedKLayer V zeta) L 2 := by
  apply saturatedK_eq_layerProduct_of_sub_eq
  intro j _hj
  dsimp [saturatedKLayer]
  abel

/-- `lem-saturated-limit.S`: pointwise equality of the two saturated limit vectors. -/
def lem_saturated_limit_S {d : Nat}
    (Ustar : Set (ProbePoint d × ℝ))
    (unprimed primed : ProbePoint d × ℝ -> Vec d) : Prop :=
  ∀ x : ProbePoint d × ℝ, x ∈ Ustar -> unprimed x = primed x

/-- Optional rate slots for future analytic proofs of `lem-saturated-limit.S`. -/
structure SaturatedLimitAPI {d : Nat}
    (Ustar : Set (ProbePoint d × ℝ))
    (unprimed primed : ProbePoint d × ℝ -> Vec d) where
  unprimed_rate : ProbePoint d × ℝ -> Prop
  primed_rate : ProbePoint d × ℝ -> Prop
  limits_equal : lem_saturated_limit_S Ustar unprimed primed

/-- The quadric `Q_h = {(w,v) : w^T A_h v = 0}`. -/
def saturatedFirstHeadQuadric {d : Nat} (Ah : Matrix (Fin d) (Fin d) ℝ) :
    Set (ProbePoint d) :=
  {p | matrixBilin Ah p.1 p.2 = 0}

/-- Fixed-`t` slice `Ustar(t)`. -/
def saturatedSlice {d : Nat}
    (Ustar : Set (ProbePoint d × ℝ)) (t : ℝ) :
    Set (ProbePoint d) :=
  {p | (p, t) ∈ Ustar}

/-- Parameter set `Jstar = {t in (0,1) : Ustar(t) is nonempty}`. -/
def saturatedParameterSet {d : Nat}
    (Ustar : Set (ProbePoint d × ℝ)) : Set ℝ :=
  {t | 0 < t ∧ t < 1 ∧ (saturatedSlice Ustar t).Nonempty}

/-- `lem-slices.S`: fixed-`t` slice conclusions, statement/API form. -/
structure lem_slices_S {d : Nat}
    (Ah : Matrix (Fin d) (Fin d) ℝ)
    (Ustar : Set (ProbePoint d × ℝ)) : Prop where
  slice_relatively_open :
    ∀ t : ℝ, 0 < t -> t < 1 ->
      ∃ W : Set (ProbePoint d),
        IsOpen W ∧ saturatedSlice Ustar t = W ∩ saturatedFirstHeadQuadric Ah
  parameter_nonempty : (saturatedParameterSet Ustar).Nonempty
  parameter_open : IsOpen (saturatedParameterSet Ustar)
  parameter_preconnected : IsPreconnected (saturatedParameterSet Ustar)
  two_parameters :
    ∃ t1 t2 : ℝ, t1 ∈ saturatedParameterSet Ustar ∧
      t2 ∈ saturatedParameterSet Ustar ∧ t1 ≠ t2
  nonzero_on_slices :
    ∀ Vh' : Matrix (Fin d) (Fin d) ℝ,
      hyp_w_nonzero_S Ustar Vh' ->
        ∀ t : ℝ, t ∈ saturatedParameterSet Ustar ->
          ∀ p : ProbePoint d, p ∈ saturatedSlice Ustar t -> p.1 ≠ 0

/-! ## K07C.M8: `lem-slices.S` builder from the K07A sign-region topology

The six fields of `lem_slices_S` are produced from the K07A sign-region topology
package `SignRegionTopologyStatement A V' h U` (proved upstream in `Step2/Dial.lean`,
`cor:sign-region-topology`).  The selected quadric matrix is the relabeled first head
`Ah = A h`, and the produced region is `Ustar = U`.  Only the last field
`nonzero_on_slices` consumes the paper hypothesis `hyp_w_nonzero_S` (as an honest
input); the remaining five fields are discharged entirely from the topology package.

The bridge identity below matches the K07A quadric patch `M_h = {q_h = 0, w ≠ 0}`
to the saturated quadric `Q_h = {w^T A_h v = 0}` cut by the open set `{w ≠ 0}`, so a
relatively-open time slice in `M_h` becomes a relatively-open slice in `Q_h`. -/

/-- The K07A quadric patch is the saturated first-head quadric cut by `{w ≠ 0}`. -/
theorem quadricPatch_eq_saturatedFirstHeadQuadric_inter {k d : Nat}
    (A : Fin k -> Matrix (Fin d) (Fin d) ℝ) (h : Fin k) :
    quadricPatch A h =
      {p : ProbePoint d | p.1 ≠ 0} ∩ saturatedFirstHeadQuadric (A h) := by
  ext p
  simp only [quadricPatch, firstHeadQuadric, firstHeadSlope, saturatedFirstHeadQuadric,
    Set.mem_inter_iff, Set.mem_setOf_eq]
  tauto

/-- **K07C.M8 (`lem:slices`) builder.** From the K07A sign-region topology package
for a relabeled first head, produce the full `lem_slices_S` conclusion for the
saturated quadric `Q_{A h}` and region `U`.  Every field except `nonzero_on_slices`
is derived from the topology package; `nonzero_on_slices` takes the paper hypothesis
`hyp_w_nonzero_S` as an honest input. -/
theorem lem_slices_S_of_signRegionTopology {k d : Nat}
    {A V' : Fin k -> Matrix (Fin d) (Fin d) ℝ} {h : Fin k}
    {U : Set (ProbePair d × ℝ)}
    (T : SignRegionTopologyStatement A V' h U) :
    lem_slices_S (A h) U := by
  -- The saturated parameter set is exactly the K07A time projection.
  have hset : saturatedParameterSet U = timeProjection U := by
    ext t
    simp only [saturatedParameterSet, timeProjection, saturatedSlice, Set.mem_setOf_eq,
      Set.Nonempty]
    constructor
    · rintro ⟨-, -, p, hp⟩
      exact ⟨p, hp⟩
    · rintro ⟨p, hp⟩
      exact ⟨T.interface.t_pos (p, t) hp, T.interface.t_lt_one (p, t) hp, p, hp⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- slice_relatively_open
    intro t _ht0 _ht1
    obtain ⟨O, hO_open, hOeq⟩ := T.slice_open t
    refine ⟨O ∩ {p : ProbePoint d | p.1 ≠ 0},
      hO_open.inter (isOpen_ne.preimage continuous_fst), ?_⟩
    rw [show saturatedSlice U t = timeSlice U t from rfl, hOeq,
      quadricPatch_eq_saturatedFirstHeadQuadric_inter]
    ext p
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    tauto
  · -- parameter_nonempty
    obtain ⟨x, hx⟩ := T.nonempty
    exact ⟨x.2, T.interface.t_pos x hx, T.interface.t_lt_one x hx, x.1, hx⟩
  · -- parameter_open
    rw [hset]
    exact T.time_projection_open
  · -- parameter_preconnected
    rw [hset]
    have hproj : timeProjection U = Prod.snd '' U := by
      ext t
      simp only [timeProjection, Set.mem_image, Set.mem_setOf_eq]
      constructor
      · rintro ⟨p, hp⟩
        exact ⟨(p, t), hp, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.1, hx⟩
    rw [hproj]
    exact T.connected.image Prod.snd continuous_snd.continuousOn
  · -- two_parameters
    rw [hset]
    obtain ⟨t1, ht1, t2, ht2, hne⟩ := T.time_projection_infinite.nontrivial
    exact ⟨t1, t2, ht1, ht2, hne⟩
  · -- nonzero_on_slices
    intro Vh' H t _ht p hp
    exact hyp_w_nonzero_S.left_ne_zero H (x := (p, t)) hp

/-- **K07C.M8 concrete tie.** For the genericity sign-region witness `SignRegionData θ h`,
the builder produces `lem_slices_S` for the relabeled first-head attention matrix
`Ah = attentionMatrix θ 0 h` and region `Ustar = D.region`. -/
theorem lem_slices_S_of_signRegionData {m k d : Nat} {θ : Params (m + 1) k d}
    {h : Fin k} (D : SignRegionData θ h) :
    lem_slices_S (attentionMatrix θ 0 h) D.region :=
  lem_slices_S_of_signRegionTopology (signRegionData_signRegionTopologyStatement D)

/-- Relabeled first-layer value matching conclusion. -/
def firstLayerValuesMatched {L k d : Nat} (hL : 0 < L)
    (theta theta' : Params L k d) (sigma : Equiv.Perm (Fin k)) : Prop :=
  ∀ h : Fin k,
    valueMatrix theta ⟨0, hL⟩ (sigma h) =
      valueMatrix theta' ⟨0, hL⟩ h

/-- `prop-first-V.S`: first-layer value identification, statement/API form. -/
structure prop_first_V_S {L k d : Nat} (hL : 0 < L)
    (theta theta' : Params L k d) where
  sigma : Equiv.Perm (Fin k)
  values_matched : firstLayerValuesMatched hL theta theta' sigma

/-! ## Immediate algebraic endpoint used after coefficient extraction -/

/-- The `K = I` cancellation data obtained after affine-in-`t` coefficient extraction. -/
structure SaturatedKCancellationData {d : Nat}
    (K V V' B B' : Matrix (Fin d) (Fin d) ℝ) : Prop where
  skip_unprimed : B - V = 1
  skip_primed : B' - V' = 1
  maps_value : K * V = V'
  maps_skip : K * B = B'

namespace SaturatedKCancellationData

variable {d : Nat}
variable {K V V' B B' : Matrix (Fin d) (Fin d) ℝ}

/-- The final TeX cancellation chain: if `K` maps both value and skip parts, then `K = I`. -/
theorem K_eq_one (D : SaturatedKCancellationData K V V' B B') : K = 1 := by
  calc
    K = K * 1 := by rw [mul_one]
    _ = K * (B - V) := by rw [D.skip_unprimed]
    _ = K * B - K * V := by rw [Matrix.mul_sub]
    _ = B' - V' := by rw [D.maps_skip, D.maps_value]
    _ = 1 := D.skip_primed

/-- The same cancellation identifies the selected first-layer values. -/
theorem value_eq (D : SaturatedKCancellationData K V V' B B') : V = V' := by
  calc
    V = (1 : Matrix (Fin d) (Fin d) ℝ) * V := by rw [one_mul]
    _ = K * V := by rw [D.K_eq_one]
    _ = V' := D.maps_value

/-- The same cancellation identifies the selected first-layer skip matrices. -/
theorem skip_eq (D : SaturatedKCancellationData K V V' B B') : B = B' := by
  calc
    B = (1 : Matrix (Fin d) (Fin d) ℝ) * B := by rw [one_mul]
    _ = K * B := by rw [D.K_eq_one]
    _ = B' := D.maps_skip

end SaturatedKCancellationData

/-! ## K07C.M7: `lem:saturated-limit` assembly

The declarations below assemble the pointwise saturated-limit equality
`lem_saturated_limit_S` (TeX `lem:saturated-limit`, `eq:limits-equal`).

The proof has three genuine ingredients, all discharged here:

* **Telescoping identification** (TeX Step 4, `eq:unprimed-limit`).  The pure matrix-algebra
  identity `unprimedSaturatedLimitVector_eq_mulVec` shows that the saturated-tail closed form
  `M v_1^∞ + E w_1^∞` (evaluated on the first-layer limit streams) equals the packaged limit
  vector `B_h = unprimedSaturatedLimitVector …`.  This is the bridge that downstream code
  applies to the honest ζ-frozen recursion closed form `satZetaPoint_snd`.
* **Primed observable convergence** (TeX Step 2/3/5, `rem:primed-uniform-saturation`).
  `tendsto_probeOutput_primedSaturatedLimitVector` proves, fully, that the θ′ probe observable
  along the head-dial path converges to the primed telescoped limit vector `B'_h`.  Every
  deeper primed gate saturates to `1` (all-ones `dialSatPoint`), so the tail telescopes to the
  skip-identity form `E' = M' - I`; this is `tendsto_dialActualProbePoint` (head-dial (iv)/(v))
  composed with `dialSatPoint_snd` and the primed algebra.
* **Equality of limits** (TeX Step 6, `eq:limits-equal`).
  `lem_saturated_limit_S_of_primed_convergence` combines the two observable limits with the
  standing probe-output equality `θ = θ′` (transformer agreement) and uniqueness of limits to
  produce the pointwise equality `B_h = B'_h` on the trichotomy region.

Placement note: this file is *upstream* of `Step2/TrichotomyInstance.lean`
(`TrichotomyInstance` imports `Saturated`), so the ζ-side observable convergence
`tendsto_satZetaActualProbePoint` — which lives in `TrichotomyInstance` — cannot be referenced
here without an import cycle.  It is therefore threaded in as the hypothesis `hUnprimed`
below; downstream (in / past `TrichotomyInstance`, where both `satZetaPoint_snd` and
`tendsto_satZetaActualProbePoint` are available) it is discharged by the ζ-frozen convergence
composed with `unprimedSaturatedLimitVector_eq_mulVec`. -/

/-- **Telescoping identification (TeX Step 4).**  The saturated-tail closed form
`M v_1^∞ + E w_1^∞`, written on the first-layer limit streams
`v_1^∞ = C_1 v + (S + t V) w` and `w_1^∞ = (B - t V) w` with `B = I + V`, equals the packaged
unprimed limit vector `B_h = unprimedSaturatedLimitVector M E (M-E) S V C_1`.  Pure matrix
algebra; this is the algebraic content of `eq:unprimed-limit`. -/
theorem unprimedSaturatedLimitVector_eq_mulVec {d : Nat}
    (M E S Vh C1 : Matrix (Fin d) (Fin d) ℝ) (t : ℝ) (w v : Vec d) :
    M *ᵥ (C1 *ᵥ v + (S + t • Vh) *ᵥ w)
        + E *ᵥ ((1 + Vh - t • Vh) *ᵥ w)
      = unprimedSaturatedLimitVector M E (saturatedTailK M E) S Vh C1 t (w, v) := by
  have hmat : M * (S + t • Vh) + E * (1 + Vh - t • Vh)
      = M * S + E * (1 + Vh) + t • (saturatedTailK M E * Vh) := by
    simp only [saturatedTailK, mul_add, mul_sub, sub_mul, mul_one, mul_smul_comm, smul_sub]
    abel
  simp only [unprimedSaturatedLimitVector]
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    add_assoc, ← Matrix.add_mulVec, hmat]

/-- **Primed observable convergence (TeX Step 2/3/5).**  Along the head-dial path (based on the
common first-layer attention `attentionMatrix θ' 0`), the θ′ probe observable converges to the
primed telescoped limit vector `B'_h = primedSaturatedLimitVector M' C1' V'_h`, provided
`V'_h = valueMatrix θ' 0 h` and `M' C1' = collapsePrefix θ' (m+1)` (the skip-identity
`E' = M' - I` telescoping) and the honest head-dial inputs: first-head quadric/dial nonvanishing
`hq`/`hpi`, first-layer separation `hsep`, and the primed deeper-slope positivity `hpos`
(`rem:primed-uniform-saturation`).  Every deeper primed gate saturates to `1`
(`tendsto_dialActualProbePoint`), so the observable converges to `(dialSatPoint θ' …).2`, which
`dialSatPoint_snd` identifies with `B'_h`. -/
theorem tendsto_probeOutput_primedSaturatedLimitVector
    {m k d : Nat} (r : Nat) (θ' : Params (m + 1) k d) (h : Fin k)
    (p : ProbePair d) (t : ℝ)
    (M' C1' Vh' : Matrix (Fin d) (Fin d) ℝ)
    (hVh' : Vh' = valueMatrix θ' 0 h)
    (hMC : M' * C1' = collapsePrefix θ' (m + 1))
    (ht_pos : 0 < t) (ht_lt_one : t < 1)
    (hq : firstHeadSlope (attentionMatrix θ' 0) h p = 0)
    (hpi : firstHeadPi (attentionMatrix θ' 0) h p ≠ 0)
    (hsep : ∀ a : Fin k, a ≠ h → 0 < matrixBilin (attentionMatrix θ' 0 a) p.1 p.2)
    (hpos : ∀ (n : Nat), 1 ≤ n → (hn : n < m + 1) → ∀ a : Fin k,
      0 < matrixBilin (attentionMatrix θ' ⟨n, hn⟩ a)
        (dialSatPoint θ' h p t n).1 (dialSatPoint θ' h p t n).2) :
    Tendsto (fun τ => probeOutput r θ'
        (headDialPath (attentionMatrix θ' 0) h (logScale r) p t τ).1
        (headDialPath (attentionMatrix θ' 0) h (logScale r) p t τ).2 τ)
      atTop (𝓝 (primedSaturatedLimitVector M' C1' Vh' t p)) := by
  have hpt := tendsto_dialActualProbePoint r θ' h p t ht_pos ht_lt_one hq hpi hsep hpos
    (m + 1) (le_refl _)
  have hsnd := (continuous_snd.tendsto (dialSatPoint θ' h p t (m + 1))).comp hpt
  have hlim : (dialSatPoint θ' h p t (m + 1)).2 = primedSaturatedLimitVector M' C1' Vh' t p := by
    rw [dialSatPoint_snd θ' h p t (m + 1) (Nat.le_add_left 1 m), primedSaturatedLimitVector,
      hMC, hVh']
    have hcoef : collapsePrefix θ' (m + 1) - 1 - (1 - t) • valueMatrix θ' 0 h
        = collapsePrefix θ' (m + 1) - 1 - valueMatrix θ' 0 h + t • valueMatrix θ' 0 h := by
      rw [sub_smul, one_smul]; abel
    rw [hcoef]
  rw [← hlim]
  refine hsnd.congr (fun τ => ?_)
  simp only [Function.comp_apply]
  exact actualProbePoint_snd_eq_probeOutput r θ'
    (headDialPath (attentionMatrix θ' 0) h (logScale r) p t τ).1
    (headDialPath (attentionMatrix θ' 0) h (logScale r) p t τ).2 τ

/-- **`lem:saturated-limit` (TeX Step 6, `eq:limits-equal`).**  On the trichotomy region `Ustar`
the two saturated limit vectors coincide.

The θ′ (primed) observable convergence is discharged internally by
`tendsto_probeOutput_primedSaturatedLimitVector` from the honest head-dial inputs: the common
first-layer attention `hAttn : attentionMatrix θ 0 = attentionMatrix θ' 0` (`eq:A-first-equal`,
from `prop:first-A`), the base-point sign-region facts (`hUstar_*`), the primed deeper-slope
positivity `hposθ'` (`rem:primed-uniform-saturation`), and the primed telescoping data
`hVh'`/`hMC`.  The θ (unprimed) observable convergence `hUnprimed` is the ζ-side saturation
`tendsto_satZetaActualProbePoint` re-expressed through `unprimedSaturatedLimitVector_eq_mulVec`;
it is threaded as a hypothesis only because `satZetaPoint`/`tendsto_satZetaActualProbePoint`
live in `TrichotomyInstance`, which is downstream of this file.  The transformer agreement
`hAgree` (probe-output equality of `θ` and `θ'`) makes the two observables equal at every finite
`τ`; uniqueness of limits then gives `B_h = B'_h`. -/
theorem lem_saturated_limit_S_of_primed_convergence
    {m k d : Nat} (r : Nat) (θ θ' : Params (m + 1) k d) (h : Fin k)
    (Ustar : Set (ProbePoint d × ℝ))
    (M E S Vh C1 M' C1' Vh' : Matrix (Fin d) (Fin d) ℝ)
    (hVh' : Vh' = valueMatrix θ' 0 h)
    (hMC : M' * C1' = collapsePrefix θ' (m + 1))
    (hAttn : attentionMatrix θ 0 = attentionMatrix θ' 0)
    (hAgree : ∀ (w v : Vec d) (τ : ℝ), 0 < τ →
      probeOutput r θ w v τ = probeOutput r θ' w v τ)
    (hUstar_tpos : ∀ x ∈ Ustar, 0 < x.2)
    (hUstar_tlt : ∀ x ∈ Ustar, x.2 < 1)
    (hUstar_q : ∀ x ∈ Ustar, firstHeadSlope (attentionMatrix θ 0) h x.1 = 0)
    (hUstar_pi : ∀ x ∈ Ustar, firstHeadPi (attentionMatrix θ 0) h x.1 ≠ 0)
    (hUstar_sep : ∀ x ∈ Ustar, ∀ a : Fin k, a ≠ h →
      0 < matrixBilin (attentionMatrix θ 0 a) x.1.1 x.1.2)
    (hposθ' : ∀ x ∈ Ustar, ∀ (n : Nat), 1 ≤ n → (hn : n < m + 1) → ∀ a : Fin k,
      0 < matrixBilin (attentionMatrix θ' ⟨n, hn⟩ a)
        (dialSatPoint θ' h x.1 x.2 n).1 (dialSatPoint θ' h x.1 x.2 n).2)
    (hUnprimed : ∀ x ∈ Ustar,
      Tendsto (fun τ => probeOutput r θ
          (headDialPath (attentionMatrix θ 0) h (logScale r) x.1 x.2 τ).1
          (headDialPath (attentionMatrix θ 0) h (logScale r) x.1 x.2 τ).2 τ)
        atTop (𝓝 (unprimedSaturatedLimitVector M E (saturatedTailK M E) S Vh C1 x.2 x.1))) :
    lem_saturated_limit_S Ustar
      (fun x => unprimedSaturatedLimitVector M E (saturatedTailK M E) S Vh C1 x.2 x.1)
      (fun x => primedSaturatedLimitVector M' C1' Vh' x.2 x.1) := by
  intro x hx
  -- θ′ observable converges to the primed limit vector.
  have hprimed : Tendsto (fun τ => probeOutput r θ'
      (headDialPath (attentionMatrix θ 0) h (logScale r) x.1 x.2 τ).1
      (headDialPath (attentionMatrix θ 0) h (logScale r) x.1 x.2 τ).2 τ)
      atTop (𝓝 (primedSaturatedLimitVector M' C1' Vh' x.2 x.1)) := by
    rw [hAttn]
    exact tendsto_probeOutput_primedSaturatedLimitVector r θ' h x.1 x.2 M' C1' Vh' hVh' hMC
      (hUstar_tpos x hx) (hUstar_tlt x hx)
      (by rw [← hAttn]; exact hUstar_q x hx)
      (by rw [← hAttn]; exact hUstar_pi x hx)
      (fun a ha => by rw [← hAttn]; exact hUstar_sep x hx a ha)
      (hposθ' x hx)
  -- Transformer agreement: the two observables coincide for large τ.
  have hEq : (fun τ => probeOutput r θ
        (headDialPath (attentionMatrix θ 0) h (logScale r) x.1 x.2 τ).1
        (headDialPath (attentionMatrix θ 0) h (logScale r) x.1 x.2 τ).2 τ)
      =ᶠ[atTop] (fun τ => probeOutput r θ'
        (headDialPath (attentionMatrix θ 0) h (logScale r) x.1 x.2 τ).1
        (headDialPath (attentionMatrix θ 0) h (logScale r) x.1 x.2 τ).2 τ) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with τ hτ
    exact hAgree (headDialPath (attentionMatrix θ 0) h (logScale r) x.1 x.2 τ).1
      (headDialPath (attentionMatrix θ 0) h (logScale r) x.1 x.2 τ).2 τ hτ
  -- Uniqueness of limits.
  have hunp' := Tendsto.congr' hEq (hUnprimed x hx)
  exact tendsto_nhds_unique hunp' hprimed

/-- **`lem:saturated-limit` packaged as a `SaturatedLimitAPI`.**  Thin wrapper over
`lem_saturated_limit_S_of_primed_convergence`: the rate slots are the auxiliary `True` (the
`O(1/τ)` rates `eq:unprimed-rate`/`eq:primed-rate` are not consumed by the equality), while
`limits_equal` is the genuine proof of `eq:limits-equal`. -/
noncomputable def saturatedLimitAPI_of_primed_convergence
    {m k d : Nat} (r : Nat) (θ θ' : Params (m + 1) k d) (h : Fin k)
    (Ustar : Set (ProbePoint d × ℝ))
    (M E S Vh C1 M' C1' Vh' : Matrix (Fin d) (Fin d) ℝ)
    (hVh' : Vh' = valueMatrix θ' 0 h)
    (hMC : M' * C1' = collapsePrefix θ' (m + 1))
    (hAttn : attentionMatrix θ 0 = attentionMatrix θ' 0)
    (hAgree : ∀ (w v : Vec d) (τ : ℝ), 0 < τ →
      probeOutput r θ w v τ = probeOutput r θ' w v τ)
    (hUstar_tpos : ∀ x ∈ Ustar, 0 < x.2)
    (hUstar_tlt : ∀ x ∈ Ustar, x.2 < 1)
    (hUstar_q : ∀ x ∈ Ustar, firstHeadSlope (attentionMatrix θ 0) h x.1 = 0)
    (hUstar_pi : ∀ x ∈ Ustar, firstHeadPi (attentionMatrix θ 0) h x.1 ≠ 0)
    (hUstar_sep : ∀ x ∈ Ustar, ∀ a : Fin k, a ≠ h →
      0 < matrixBilin (attentionMatrix θ 0 a) x.1.1 x.1.2)
    (hposθ' : ∀ x ∈ Ustar, ∀ (n : Nat), 1 ≤ n → (hn : n < m + 1) → ∀ a : Fin k,
      0 < matrixBilin (attentionMatrix θ' ⟨n, hn⟩ a)
        (dialSatPoint θ' h x.1 x.2 n).1 (dialSatPoint θ' h x.1 x.2 n).2)
    (hUnprimed : ∀ x ∈ Ustar,
      Tendsto (fun τ => probeOutput r θ
          (headDialPath (attentionMatrix θ 0) h (logScale r) x.1 x.2 τ).1
          (headDialPath (attentionMatrix θ 0) h (logScale r) x.1 x.2 τ).2 τ)
        atTop (𝓝 (unprimedSaturatedLimitVector M E (saturatedTailK M E) S Vh C1 x.2 x.1))) :
    SaturatedLimitAPI Ustar
      (fun x => unprimedSaturatedLimitVector M E (saturatedTailK M E) S Vh C1 x.2 x.1)
      (fun x => primedSaturatedLimitVector M' C1' Vh' x.2 x.1) where
  unprimed_rate := fun _ => True
  primed_rate := fun _ => True
  limits_equal :=
    lem_saturated_limit_S_of_primed_convergence r θ θ' h Ustar M E S Vh C1 M' C1' Vh'
      hVh' hMC hAttn hAgree hUstar_tpos hUstar_tlt hUstar_q hUstar_pi hUstar_sep hposθ' hUnprimed

end TransformerIdentifiability.NLayer.KHead
