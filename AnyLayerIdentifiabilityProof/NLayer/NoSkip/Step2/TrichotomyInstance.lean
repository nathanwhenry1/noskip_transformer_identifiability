import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Step2.Trichotomy
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Step2.MultiDial
import AnyLayerIdentifiabilityProof.NLayer.KHead.Step2.TrichotomyInstance

set_option autoImplicit false

open Filter
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.NoSkip

/-!
# Tuple-dial formal assignments

The old skip proof froze a distinguished first head and saturated its siblings.
The no-skip dial instead keeps the entire independent tuple `t : Fin k → ℝ`
at layer zero.  Deeper heads are frozen according to the trichotomy labels.
-/

noncomputable section

/-- Convert a trichotomy label to its numerical frozen gate. -/
noncomputable def trichotomyLabelValue (r : Nat) (label : TrichotomyLabel) : Real :=
  TrichotomyLabel.eval 0 1 (alpha r) label

@[simp] theorem trichotomyLabelValue_zero (r : Nat) :
    trichotomyLabelValue r KHead.TrichotomyLabel.zero = 0 :=
  rfl

@[simp] theorem trichotomyLabelValue_one (r : Nat) :
    trichotomyLabelValue r KHead.TrichotomyLabel.one = 1 :=
  rfl

@[simp] theorem trichotomyLabelValue_alpha (r : Nat) :
    trichotomyLabelValue r KHead.TrichotomyLabel.alpha = alpha r :=
  rfl

/-- A zero-based formal `(layer,head)` index viewed as the one-based deeper
head record used by the abstract processing order. -/
def formalVarDeeperHead {L k : Nat} (x : FormalVar L k) : DeeperHead :=
  { layer := x.1.1 + 1, head := x.2.1 + 1 }

/-- Frozen tuple for the no-skip multi-dial: the complete first-layer vector
is `t`, while every deeper head receives its trichotomy value. -/
noncomputable def tupleDialFrozenFamily {n k : Nat} (r : Nat)
    (t : Fin k → Real) (labels : DeeperHead → TrichotomyLabel) :
    FrozenGateFamily (n + 1) k :=
  fun l a => if l.1 = 0 then t a
    else trichotomyLabelValue r (labels (formalVarDeeperHead (l, a)))

/-- Formal-polynomial assignment corresponding to `tupleDialFrozenFamily`. -/
noncomputable def tupleDialFrozenAssignment {n k : Nat} (r : Nat)
    (t : Fin k → Real) (labels : DeeperHead → TrichotomyLabel) :
    FormalAssignment (n + 1) k :=
  frozenGateAssignment (tupleDialFrozenFamily r t labels)

@[simp] theorem tupleDialFrozenFamily_first {n k : Nat} (r : Nat)
    (t : Fin k → Real) (labels : DeeperHead → TrichotomyLabel) (a : Fin k) :
    tupleDialFrozenFamily (n := n) r t labels ⟨0, Nat.succ_pos n⟩ a = t a := by
  rw [tupleDialFrozenFamily, if_pos rfl]

@[simp] theorem tupleDialFrozenAssignment_first {n k : Nat} (r : Nat)
    (t : Fin k → Real) (labels : DeeperHead → TrichotomyLabel) (a : Fin k) :
    tupleDialFrozenAssignment (n := n) r t labels (⟨0, Nat.succ_pos n⟩, a) = t a := by
  change tupleDialFrozenFamily r t labels ⟨0, Nat.succ_pos n⟩ a = t a
  exact tupleDialFrozenFamily_first r t labels a

theorem tupleDialFrozenFamily_deeper {n k : Nat} (r : Nat)
    (t : Fin k → Real) (labels : DeeperHead → TrichotomyLabel)
    (l : Fin (n + 1)) (a : Fin k) (hl : 0 < l.1) :
    tupleDialFrozenFamily r t labels l a =
      trichotomyLabelValue r (labels { layer := l.1 + 1, head := a.1 + 1 }) := by
  simp [tupleDialFrozenFamily, Nat.ne_of_gt hl, formalVarDeeperHead]

theorem tupleDialFrozenAssignment_deeper {n k : Nat} (r : Nat)
    (t : Fin k → Real) (labels : DeeperHead → TrichotomyLabel)
    (l : Fin (n + 1)) (a : Fin k) (hl : 0 < l.1) :
    tupleDialFrozenAssignment r t labels (l, a) =
      trichotomyLabelValue r (labels { layer := l.1 + 1, head := a.1 + 1 }) := by
  exact tupleDialFrozenFamily_deeper r t labels l a hl

/-- The tuple assignment evaluates the no-skip formal streams to the frozen
recursion with first-layer vector `t` and the chosen deeper labels. -/
theorem eval_formalPoint_tupleDialFrozenAssignment {n k d : Nat} (r : Nat)
    (theta : Params (n + 1) k d) (t : Fin k → Real)
    (labels : DeeperHead → TrichotomyLabel) (w v : Vec d)
    (q : Nat) (hq : q ≤ n + 1) :
    evalFormalVec (tupleDialFrozenAssignment r t labels)
        (formalPoint theta w v q hq).1 =
        (frozenPoint theta (tupleDialFrozenFamily r t labels) w v q hq).1 ∧
      evalFormalVec (tupleDialFrozenAssignment r t labels)
        (formalPoint theta w v q hq).2 =
        (frozenPoint theta (tupleDialFrozenFamily r t labels) w v q hq).2 :=
  eval_formalPoint_frozenGateAssignment theta (tupleDialFrozenFamily r t labels) w v q hq

/-! ### Prefix substitutions used by the finite trichotomy telescope -/

/-- A mixed assignment: variables in the processed prefix use the live
assignment and all remaining variables use the tuple-frozen assignment. -/
noncomputable def tupleDialPrefixAssignment {L k : Nat}
    (live frozen : FormalAssignment L k) (vars : List (FormalVar L k))
    (q : Nat) : FormalAssignment L k :=
  fun x => if x ∈ vars.take q then live x else frozen x

@[simp] theorem tupleDialPrefixAssignment_zero {L k : Nat}
    (live frozen : FormalAssignment L k) (vars : List (FormalVar L k)) :
    tupleDialPrefixAssignment live frozen vars 0 = frozen := by
  funext x
  simp [tupleDialPrefixAssignment]

theorem tupleDialPrefixAssignment_of_mem_take {L k : Nat}
    (live frozen : FormalAssignment L k) (vars : List (FormalVar L k))
    (q : Nat) {x : FormalVar L k} (hx : x ∈ vars.take q) :
    tupleDialPrefixAssignment live frozen vars q x = live x := by
  simp [tupleDialPrefixAssignment, hx]

theorem tupleDialPrefixAssignment_of_not_mem_take {L k : Nat}
    (live frozen : FormalAssignment L k) (vars : List (FormalVar L k))
    (q : Nat) {x : FormalVar L k} (hx : x ∉ vars.take q) :
    tupleDialPrefixAssignment live frozen vars q x = frozen x := by
  simp [tupleDialPrefixAssignment, hx]

theorem tupleDialPrefixAssignment_length {L k : Nat}
    (live frozen : FormalAssignment L k) (vars : List (FormalVar L k))
    {x : FormalVar L k} (hx : x ∈ vars) :
    tupleDialPrefixAssignment live frozen vars vars.length x = live x := by
  simp [tupleDialPrefixAssignment, List.take_length, hx]

/-- Consecutive prefix assignments differ only at the newly activated tuple
coordinate. -/
theorem tupleDialPrefixAssignment_succ_eq_of_ne {L k : Nat}
    (live frozen : FormalAssignment L k) (vars : List (FormalVar L k))
    (q : Nat) (hq : q < vars.length) {x : FormalVar L k}
    (hx : x ≠ vars[q]'hq) :
    tupleDialPrefixAssignment live frozen vars (q + 1) x =
      tupleDialPrefixAssignment live frozen vars q x := by
  by_cases hxq : x ∈ vars.take q
  · have hxq1 : x ∈ vars.take (q + 1) := by
      rw [List.take_succ_eq_append_getElem hq]
      exact List.mem_append_left _ hxq
    rw [tupleDialPrefixAssignment_of_mem_take _ _ _ _ hxq1,
      tupleDialPrefixAssignment_of_mem_take _ _ _ _ hxq]
  · have hxq1 : x ∉ vars.take (q + 1) := by
      rw [List.take_succ_eq_append_getElem hq]
      simp only [List.mem_append, List.mem_singleton]
      rintro (h | h)
      · exact hxq h
      · exact hx h
    rw [tupleDialPrefixAssignment_of_not_mem_take _ _ _ _ hxq1,
      tupleDialPrefixAssignment_of_not_mem_take _ _ _ _ hxq]

/-! ## NS120: tuple-dial region restriction along the chart -/

/-- The product source box of a multi-dial chart is ambient-open. -/
theorem isOpen_multiSignSourceBox {k d : Nat} (pivot : Fin k ↪ Fin d)
    (w0 : Vec d) (vHat : AnchorFreeVec pivot) (t0 : Fin k → Real) (rho : Real) :
    IsOpen (multiSignSourceBox pivot w0 vHat t0 rho) := by
  have hw : IsOpen {x : MultiSignChartInput pivot | x.1.1 ∈ Metric.ball w0 rho} :=
    Metric.isOpen_ball.preimage (continuous_fst.comp continuous_fst)
  have hv : IsOpen {x : MultiSignChartInput pivot | x.1.2 ∈ Metric.ball vHat rho} :=
    Metric.isOpen_ball.preimage (continuous_snd.comp continuous_fst)
  have ht : IsOpen {x : MultiSignChartInput pivot |
      ∀ a, x.2 a ∈ Set.Ioo (t0 a - rho) (t0 a + rho)} := by
    have heq : {x : MultiSignChartInput pivot |
        ∀ a, x.2 a ∈ Set.Ioo (t0 a - rho) (t0 a + rho)} =
        ⋂ a, {x : MultiSignChartInput pivot |
          x.2 a ∈ Set.Ioo (t0 a - rho) (t0 a + rho)} := by
      ext x
      simp
    rw [heq]
    exact isOpen_iInter_of_finite fun a =>
      isOpen_Ioo.preimage ((continuous_apply a).comp continuous_snd)
  simpa [multiSignSourceBox, Set.setOf_and] using hw.inter (hv.inter ht)

/-- A chart-stable tuple-dial region.  Unlike `MultiDialSignRegion`, this
record is closed under later open sign restrictions: the source need not be a
product box, but remains a nonempty connected open subset of the original
chart box. -/
structure MultiDialRestrictedRegion {n k d : Nat}
    {theta : Params (n + 1) k d} (D : MultiDialSignRegion theta) where
  source : Set (MultiSignChartInput D.pivot)
  region : Set (MultiSignPoint d k)
  source_subset : source ⊆
    multiSignSourceBox D.pivot D.w0 D.vHat D.t0 D.rho
  source_nonempty : source.Nonempty
  source_open : IsOpen source
  source_preconnected : IsPreconnected source
  region_eq_image : region = multiSignChart theta D.pivot '' source

namespace MultiDialRestrictedRegion

variable {n k d : Nat} {theta : Params (n + 1) k d}
  {D : MultiDialSignRegion theta}

/-- The original sign region as the initial chart-stable region. -/
noncomputable def full (D : MultiDialSignRegion theta) :
    MultiDialRestrictedRegion D where
  source := multiSignSourceBox D.pivot D.w0 D.vHat D.t0 D.rho
  region := D.region
  source_subset := Set.Subset.rfl
  source_nonempty := by
    refine ⟨((D.w0, D.vHat), D.t0), ?_⟩
    exact ⟨Metric.mem_ball_self D.rho_pos, Metric.mem_ball_self D.rho_pos,
      fun a => ⟨by linarith [D.rho_pos], by linarith [D.rho_pos]⟩⟩
  source_open := isOpen_multiSignSourceBox D.pivot D.w0 D.vHat D.t0 D.rho
  source_preconnected :=
    (convex_multiSignSourceBox D.pivot D.w0 D.vHat D.t0 D.rho).isPreconnected
  region_eq_image := D.region_eq_image

/-- Every restricted region remains inside the original sign region. -/
theorem region_subset (R : MultiDialRestrictedRegion D) : R.region ⊆ D.region := by
  rw [R.region_eq_image, D.region_eq_image]
  exact Set.image_mono R.source_subset

theorem nonempty (R : MultiDialRestrictedRegion D) : R.region.Nonempty := by
  rcases R.source_nonempty with ⟨x, hx⟩
  exact ⟨multiSignChart theta D.pivot x, by rw [R.region_eq_image]; exact ⟨x, hx, rfl⟩⟩

/-- Restricted regions are connected, by continuity of the same solved chart. -/
theorem isPreconnected (R : MultiDialRestrictedRegion D) :
    IsPreconnected R.region := by
  rw [R.region_eq_image]
  exact R.source_preconnected.image _
    ((D.chart_continuousOn).mono
      (fun x hx => D.ball_subset_domain (R.source_subset hx).1))

/-- On a restricted region, projection is still the inverse chart. -/
theorem chart_projection_inverse (R : MultiDialRestrictedRegion D) :
    ∀ p ∈ R.region,
      multiSignChart theta D.pivot (multiSignProjection D.pivot p) = p := by
  intro p hp
  exact D.chart_projection_inverse p (R.region_subset hp)

/-- The solved chart remains bijective after restriction. -/
theorem chart_bijOn (R : MultiDialRestrictedRegion D) :
    Set.BijOn (multiSignChart theta D.pivot) R.source R.region := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [R.region_eq_image]
    exact ⟨x, hx, rfl⟩
  · intro x hx y hy hxy
    have := congrArg (multiSignProjection D.pivot) hxy
    simpa using this
  · intro p hp
    rw [R.region_eq_image] at hp
    exact hp

/-- Intrinsic description of a chart restriction using the continuous inverse
projection. -/
theorem region_eq_base_inter_projection (R : MultiDialRestrictedRegion D) :
    R.region = D.region ∩ (multiSignProjection D.pivot) ⁻¹' R.source := by
  ext p
  constructor
  · intro hp
    have hpD := R.region_subset hp
    refine ⟨hpD, ?_⟩
    rw [R.region_eq_image] at hp
    rcases hp with ⟨x, hx, rfl⟩
    simpa using hx
  · rintro ⟨hpD, hproj⟩
    rw [R.region_eq_image]
    refine ⟨multiSignProjection D.pivot p, hproj, ?_⟩
    exact D.chart_projection_inverse p hpD

/-- Restricted regions remain relatively open in the full multi-quadric slab. -/
theorem relativelyOpen (R : MultiDialRestrictedRegion D) :
    RelativelyOpenIn R.region (multiSignSlab theta) := by
  rw [R.region_eq_base_inter_projection]
  exact D.relativelyOpen.inter_open
    (R.source_open.preimage D.projection_continuous)

/-- Compact-uniform multi-dial motion estimates restrict without any change of
path or constants. -/
theorem exists_uniform_motion_bound (R : MultiDialRestrictedRegion D) (r : Nat)
    {K : Set (MultiSignPoint d k)} (hK : IsCompact K) (hKR : K ⊆ R.region) :
    ∃ C : Real, 0 ≤ C ∧ ∀ p ∈ K, ∀ tau : Real, 1 ≤ tau →
      ‖(multiDialPath r theta p tau).2 - p.1.2‖ ≤ C / tau :=
  exists_uniform_multiDialPath_motion_bound r D hK
    (hKR.trans R.region_subset)

/-- Restrict a chart-stable region around any one of its points by an ambient
open sign condition.  A sufficiently small chart ball supplies nonemptiness,
connectedness and openness automatically; no branch conclusion is assumed. -/
theorem exists_restrict_ambientOpen (R : MultiDialRestrictedRegion D)
    {O : Set (MultiSignPoint d k)} (hO : IsOpen O)
    {p : MultiSignPoint d k} (hpR : p ∈ R.region) (hpO : p ∈ O) :
    ∃ R' : MultiDialRestrictedRegion D,
      p ∈ R'.region ∧ R'.region ⊆ R.region ∩ O := by
  let x := multiSignProjection D.pivot p
  have hxR : x ∈ R.source := by
    rw [R.region_eq_base_inter_projection] at hpR
    exact hpR.2
  have hpchart : multiSignChart theta D.pivot x = p :=
    R.chart_projection_inverse p hpR
  have hxdom : x ∈ multiSignChartDomain theta D.pivot :=
    D.ball_subset_domain (R.source_subset hxR).1
  let S : Set (MultiSignChartInput D.pivot) :=
    R.source ∩ (multiSignChartDomain theta D.pivot ∩
      (multiSignChart theta D.pivot) ⁻¹' O)
  have hchartOpen : IsOpen (multiSignChartDomain theta D.pivot ∩
      (multiSignChart theta D.pivot) ⁻¹' O) :=
    (D.chart_continuousOn).isOpen_inter_preimage
      (isOpen_multiSignChartDomain theta D.pivot) hO
  have hSopen : IsOpen S := R.source_open.inter hchartOpen
  have hxS : x ∈ S := ⟨hxR, hxdom, by simpa [hpchart] using hpO⟩
  obtain ⟨eps, heps, hball⟩ := Metric.isOpen_iff.mp hSopen x hxS
  let source' := Metric.ball x eps
  let region' := multiSignChart theta D.pivot '' source'
  let R' : MultiDialRestrictedRegion D := {
    source := source'
    region := region'
    source_subset := fun y hy => R.source_subset (hball hy).1
    source_nonempty := ⟨x, Metric.mem_ball_self heps⟩
    source_open := Metric.isOpen_ball
    source_preconnected := (convex_ball x eps).isPreconnected
    region_eq_image := rfl }
  refine ⟨R', ?_, ?_⟩
  · change p ∈ region'
    rw [← hpchart]
    exact ⟨x, Metric.mem_ball_self heps, rfl⟩
  · intro q hq
    change q ∈ region' at hq
    rcases hq with ⟨y, hy, rfl⟩
    have hyS := hball hy
    refine ⟨?_, hyS.2.2⟩
    rw [R.region_eq_image]
    exact ⟨y, hyS.1, rfl⟩

end MultiDialRestrictedRegion

/-! ## NS121: the concrete tuple-dial processing invariant -/

/-- Exponential closeness used by the no-skip processed-head estimate.  This
is proposition-valued data, not an opaque branch assumption. -/
def TupleDialExpCloseTo (f : Real → Real) (a : Real) : Prop :=
  ∃ rate coeff start : Real,
    0 < rate ∧ 0 ≤ coeff ∧
      ∀ tau : Real, start ≤ tau →
        |f tau - a| ≤ coeff * Real.exp (-rate * tau)

/-- The live gate assignment along the simultaneous tuple-dial path. -/
noncomputable def tupleDialLiveAssignment {n k d : Nat} (r : Nat)
    (theta : Params (n + 1) k d) (p : MultiSignPoint d k) (tau : Real) :
    FormalAssignment (n + 1) k :=
  actualProbeGateAssignment r theta
    (multiDialPath r theta p tau).1 (multiDialPath r theta p tau).2 tau

/-- The frozen deeper-head slope as a function on tuple-dial base points.
Invalid one-based deeper-head indices are sent to zero; entries of
`deeperHeadOrder` always take the valid branch. -/
noncomputable def tupleDialFrozenSlopeForm {n k d : Nat} (r : Nat)
    (theta : Params (n + 1) k d) (dh : DeeperHead)
    (labels : DeeperHead → TrichotomyLabel) : MultiSignPoint d k → Real :=
  fun p =>
    if hvalid : 2 ≤ dh.layer ∧ dh.layer ≤ n + 1 ∧
        1 ≤ dh.head ∧ dh.head ≤ k then
      MvPolynomial.eval (tupleDialFrozenAssignment r p.2 labels)
        (formalSlope theta p.1.1 p.1.2
          ⟨dh.layer - 1, by omega⟩ ⟨dh.head - 1, by omega⟩)
    else 0

/-- Faithful tuple-dial formal data for the abstract trichotomy scaffold.  `Phi`
and `Lambda` are the same frozen formal-slope evaluation; sign and polynomial
rigidity consequences are supplied by later branch theorems. -/
noncomputable def tupleDialFormalData {n k d : Nat} (r : Nat)
    (theta : Params (n + 1) k d) :
    KHead.TrichotomyFormalData (MultiSignPoint d k → Real) where
  Phi dh labels := tupleDialFrozenSlopeForm r theta dh labels
  Lambda dh labels := tupleDialFrozenSlopeForm r theta dh labels

/-- Honest estimate payload carried by the processing invariant.  It records
the exact live/frozen tuple assignments, exponential estimates only for the
already processed heads, and compact-uniform probe motion.  It contains no
claim about the branch of the current unprocessed head. -/
structure TupleDialEstimate {n k d : Nat} (r : Nat)
    (theta : Params (n + 1) k d) (D : MultiDialSignRegion theta)
    (order : List DeeperHead) (q : Nat) (R : MultiDialRestrictedRegion D)
    (labels : DeeperHead → TrichotomyLabel) : Prop where
  firstLayer_live_eq_frozen :
    ∀ p ∈ R.region, ∀ tau : Real, tau ≠ 0 → ∀ a : Fin k,
      tupleDialLiveAssignment r theta p tau (⟨0, Nat.succ_pos n⟩, a) =
        tupleDialFrozenAssignment r p.2 labels (⟨0, Nat.succ_pos n⟩, a)
  processed_gate_expClose :
    ∀ x : FormalVar (n + 1) k,
      formalVarDeeperHead x ∈ processedPrefix order q →
      ∀ p ∈ R.region,
        TupleDialExpCloseTo
          (fun tau => tupleDialLiveAssignment r theta p tau x)
          (tupleDialFrozenAssignment r p.2 labels x)
  compact_uniform_motion :
    ∀ K : Set (MultiSignPoint d k), IsCompact K → K ⊆ R.region →
      ∃ C : Real, 0 ≤ C ∧ ∀ p ∈ K, ∀ tau : Real, 1 ≤ tau →
        ‖(multiDialPath r theta p tau).2 - p.1.2‖ ≤ C / tau

namespace TupleDialEstimate

variable {n k d : Nat} {r : Nat} {theta : Params (n + 1) k d}
  {D : MultiDialSignRegion theta} {order : List DeeperHead} {q : Nat}
  {R S : MultiDialRestrictedRegion D}
  {labels : DeeperHead → TrichotomyLabel}

/-- All estimate fields restrict to a smaller chart region. -/
theorem restrict (hSR : S.region ⊆ R.region)
    (hEst : TupleDialEstimate r theta D order q R labels) :
    TupleDialEstimate r theta D order q S labels where
  firstLayer_live_eq_frozen := fun p hp =>
    hEst.firstLayer_live_eq_frozen p (hSR hp)
  processed_gate_expClose := fun x hx p hp =>
    hEst.processed_gate_expClose x hx p (hSR hp)
  compact_uniform_motion := by
    intro K hK hKS
    exact S.exists_uniform_motion_bound r hK hKS

end TupleDialEstimate

/-- Concrete predicates instantiating the abstract KHead processing invariant
on chart-stable tuple-dial regions. -/
noncomputable def tupleDialPredicates {n k d : Nat} (r : Nat)
    (theta : Params (n + 1) k d) (D : MultiDialSignRegion theta) :
    KHead.TrichotomyPredicates (MultiDialRestrictedRegion D)
      (MultiSignPoint d k → Real) where
  RegionNonempty R := R.region.Nonempty
  RegionConnected R := IsPreconnected R.region
  RegionRelativelyOpen R := RelativelyOpenIn R.region (multiSignSlab theta)
  RegionSubset R S := R.region ⊆ S.region
  PositiveOn phi R := ∀ p ∈ R.region, 0 < phi p
  NegativeOn phi R := ∀ p ∈ R.region, phi p < 0
  VanishesOn phi R := ∀ p ∈ R.region, phi p = 0
  ZeroPolynomial phi := phi = 0
  Estimate order q R labels := TupleDialEstimate r theta D order q R labels

/-- Stable no-skip name for the instantiated abstract processing invariant. -/
def TupleDialProcessingInvariant {n k d : Nat} (r : Nat)
    (theta : Params (n + 1) k d) (D : MultiDialSignRegion theta)
    (baseRegion currentRegion : MultiDialRestrictedRegion D)
    (order : List DeeperHead) (q : Nat)
    (labels : DeeperHead → TrichotomyLabel) : Prop :=
  KHead.ProcessingInvariantStatement (tupleDialPredicates r theta D)
    (tupleDialFormalData r theta) baseRegion currentRegion order q labels

/-- Processed label/sign links restrict to a smaller tuple-dial region.  The
`alpha` case is a global zero-form statement and is unchanged. -/
theorem tupleDialLabelSignLink_restrict {n k d : Nat} {r : Nat}
    {theta : Params (n + 1) k d} {D : MultiDialSignRegion theta}
    {R S : MultiDialRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {h : DeeperHead}
    (hSR : S.region ⊆ R.region)
    (hlink : KHead.LabelSignLink (tupleDialPredicates r theta D)
      (tupleDialFormalData r theta) R labels h) :
    KHead.LabelSignLink (tupleDialPredicates r theta D)
      (tupleDialFormalData r theta) S labels h := by
  unfold KHead.LabelSignLink at hlink ⊢
  cases hlabel : labels h with
  | zero =>
      rw [hlabel] at hlink
      simp only [tupleDialPredicates] at hlink ⊢
      intro p hp
      exact hlink p (hSR hp)
  | one =>
      rw [hlabel] at hlink
      simp only [tupleDialPredicates] at hlink ⊢
      intro p hp
      exact hlink p (hSR hp)
  | alpha =>
      rw [hlabel] at hlink
      simp only [tupleDialPredicates] at hlink ⊢
      exact hlink

/-- Restrict the complete abstract invariant without changing its stage or
labels.  Topology comes from NS120 and all estimate fields restrict honestly. -/
theorem TupleDialProcessingInvariant.restrict {n k d : Nat} {r : Nat}
    {theta : Params (n + 1) k d} {D : MultiDialSignRegion theta}
    {baseRegion R S : MultiDialRestrictedRegion D}
    {order : List DeeperHead} {q : Nat}
    {labels : DeeperHead → TrichotomyLabel}
    (hInv : TupleDialProcessingInvariant r theta D baseRegion R order q labels)
    (hSR : S.region ⊆ R.region) :
    TupleDialProcessingInvariant r theta D baseRegion S order q labels where
  region_nonempty := S.nonempty
  region_connected := S.isPreconnected
  region_relativelyOpen := S.relativelyOpen
  region_subset_base := hSR.trans hInv.region_subset_base
  label_sign_link := fun h hh =>
    tupleDialLabelSignLink_restrict hSR (hInv.label_sign_link h hh)
  estimate := hInv.estimate.restrict hSR

/-- At stage zero the estimate is genuine: first-layer live gates equal their
tuple targets exactly, the processed-head clause is vacuous, and compact motion
comes from NS115 through the NS120 restriction API. -/
theorem tupleDialEstimate_zero {n k d : Nat} (r : Nat)
    {theta : Params (n + 1) k d} (D : MultiDialSignRegion theta)
    (labels : DeeperHead → TrichotomyLabel) :
    TupleDialEstimate r theta D (deeperHeadOrder (n + 1) k) 0
      (MultiDialRestrictedRegion.full D) labels where
  firstLayer_live_eq_frozen := by
    intro p hp tau htau a
    let bp : MultiDialBasePoint D :=
      ⟨p, (MultiDialRestrictedRegion.full D).region_subset hp⟩
    change actualProbeGate r theta
        (multiDialPath r theta p tau).1 (multiDialPath r theta p tau).2 tau
          ⟨0, Nat.succ_pos n⟩ a = p.2 a
    exact bp.firstLayer_gate_eq r htau a
  processed_gate_expClose := by
    intro x hx
    simp [KHead.processedPrefix] at hx
  compact_uniform_motion := by
    intro K hK hKD
    exact (MultiDialRestrictedRegion.full D).exists_uniform_motion_bound r hK hKD

/-- Initial concrete processing invariant, obtained directly from the abstract
`processingInvariant_zero` constructor. -/
theorem tupleDialProcessingInvariant_zero {n k d : Nat} (r : Nat)
    {theta : Params (n + 1) k d} (D : MultiDialSignRegion theta)
    (labels : DeeperHead → TrichotomyLabel) :
    TupleDialProcessingInvariant r theta D
      (MultiDialRestrictedRegion.full D) (MultiDialRestrictedRegion.full D)
      (deeperHeadOrder (n + 1) k) 0 labels := by
  apply KHead.processingInvariant_zero
  · exact (MultiDialRestrictedRegion.full D).nonempty
  · exact (MultiDialRestrictedRegion.full D).isPreconnected
  · exact (MultiDialRestrictedRegion.full D).relativelyOpen
  · exact Set.Subset.rfl
  · exact tupleDialEstimate_zero r D labels

/-- The invariant exposes precisely the processed-head exponential estimates. -/
theorem TupleDialProcessingInvariant.processed_gate_expClose
    {n k d : Nat} {r : Nat} {theta : Params (n + 1) k d}
    {D : MultiDialSignRegion theta}
    {baseRegion currentRegion : MultiDialRestrictedRegion D}
    {order : List DeeperHead} {q : Nat}
    {labels : DeeperHead → TrichotomyLabel}
    (hInv : TupleDialProcessingInvariant r theta D baseRegion currentRegion
      order q labels)
    (x : FormalVar (n + 1) k)
    (hx : formalVarDeeperHead x ∈ processedPrefix order q)
    (p : MultiSignPoint d k) (hp : p ∈ currentRegion.region) :
    TupleDialExpCloseTo
      (fun tau => tupleDialLiveAssignment r theta p tau x)
      (tupleDialFrozenAssignment r p.2 labels x) :=
  hInv.estimate.processed_gate_expClose x hx p hp

/-- The invariant retains exact simultaneous first-layer live/frozen tracking. -/
theorem TupleDialProcessingInvariant.firstLayer_live_eq_frozen
    {n k d : Nat} {r : Nat} {theta : Params (n + 1) k d}
    {D : MultiDialSignRegion theta}
    {baseRegion currentRegion : MultiDialRestrictedRegion D}
    {order : List DeeperHead} {q : Nat}
    {labels : DeeperHead → TrichotomyLabel}
    (hInv : TupleDialProcessingInvariant r theta D baseRegion currentRegion
      order q labels)
    (p : MultiSignPoint d k) (hp : p ∈ currentRegion.region)
    (tau : Real) (htau : tau ≠ 0) (a : Fin k) :
    tupleDialLiveAssignment r theta p tau (⟨0, Nat.succ_pos n⟩, a) =
      tupleDialFrozenAssignment r p.2 labels (⟨0, Nat.succ_pos n⟩, a) :=
  hInv.estimate.firstLayer_live_eq_frozen p hp tau htau a

/-- Compact-uniform motion is retained at every invariant stage. -/
theorem TupleDialProcessingInvariant.compact_uniform_motion
    {n k d : Nat} {r : Nat} {theta : Params (n + 1) k d}
    {D : MultiDialSignRegion theta}
    {baseRegion currentRegion : MultiDialRestrictedRegion D}
    {order : List DeeperHead} {q : Nat}
    {labels : DeeperHead → TrichotomyLabel}
    (hInv : TupleDialProcessingInvariant r theta D baseRegion currentRegion
      order q labels)
    (K : Set (MultiSignPoint d k)) (hK : IsCompact K)
    (hKR : K ⊆ currentRegion.region) :
    ∃ C : Real, 0 ≤ C ∧ ∀ p ∈ K, ∀ tau : Real, 1 ≤ tau →
      ‖(multiDialPath r theta p tau).2 - p.1.2‖ ≤ C / tau :=
  hInv.estimate.compact_uniform_motion K hK hKR

/-! ## Paired source/target processing API

The dial geometry belongs to the target parameters, while the live gates and
formal slopes belong to the source parameters.  Only the first attention
matrices must agree in order to initialize exact tuple tracking. -/

/-- Source live gates evaluated along a path constructed from the target dial
geometry. -/
noncomputable def pairedTupleDialLiveAssignment {n k d : Nat} (r : Nat)
    (thetaLive thetaDial : Params (n + 1) k d)
    (p : MultiSignPoint d k) (tau : Real) : FormalAssignment (n + 1) k :=
  actualProbeGateAssignment r thetaLive
    (multiDialPath r thetaDial p tau).1 (multiDialPath r thetaDial p tau).2 tau

/-- Honest paired estimate: gate estimates refer to the source network, while
the compact motion field refers to the target dial path. -/
structure PairedTupleDialEstimate {n k d : Nat} (r : Nat)
    (thetaLive thetaDial : Params (n + 1) k d)
    (D : MultiDialSignRegion thetaDial)
    (order : List DeeperHead) (q : Nat) (R : MultiDialRestrictedRegion D)
    (labels : DeeperHead → TrichotomyLabel) : Prop where
  firstLayer_live_eq_frozen :
    ∀ p ∈ R.region, ∀ tau : Real, tau ≠ 0 → ∀ a : Fin k,
      pairedTupleDialLiveAssignment r thetaLive thetaDial p tau
          (⟨0, Nat.succ_pos n⟩, a) =
        tupleDialFrozenAssignment r p.2 labels (⟨0, Nat.succ_pos n⟩, a)
  processed_gate_expClose :
    ∀ x : FormalVar (n + 1) k,
      formalVarDeeperHead x ∈ processedPrefix order q →
      ∀ p ∈ R.region,
        TupleDialExpCloseTo
          (fun tau => pairedTupleDialLiveAssignment r thetaLive thetaDial p tau x)
          (tupleDialFrozenAssignment r p.2 labels x)
  compact_uniform_motion :
    ∀ K : Set (MultiSignPoint d k), IsCompact K → K ⊆ R.region →
      ∃ C : Real, 0 ≤ C ∧ ∀ p ∈ K, ∀ tau : Real, 1 ≤ tau →
        ‖(multiDialPath r thetaDial p tau).2 - p.1.2‖ ≤ C / tau

namespace PairedTupleDialEstimate

variable {n k d : Nat} {r : Nat}
  {thetaLive thetaDial : Params (n + 1) k d}
  {D : MultiDialSignRegion thetaDial} {order : List DeeperHead} {q : Nat}
  {R S : MultiDialRestrictedRegion D}
  {labels : DeeperHead → TrichotomyLabel}

theorem restrict (hSR : S.region ⊆ R.region)
    (hEst : PairedTupleDialEstimate r thetaLive thetaDial D order q R labels) :
    PairedTupleDialEstimate r thetaLive thetaDial D order q S labels where
  firstLayer_live_eq_frozen := fun p hp =>
    hEst.firstLayer_live_eq_frozen p (hSR hp)
  processed_gate_expClose := fun x hx p hp =>
    hEst.processed_gate_expClose x hx p (hSR hp)
  compact_uniform_motion := by
    intro K hK hKS
    exact S.exists_uniform_motion_bound r hK hKS

end PairedTupleDialEstimate

/-- Abstract predicates for a source network processed over a target-network
multi-dial region. -/
noncomputable def pairedTupleDialPredicates {n k d : Nat} (r : Nat)
    (thetaLive thetaDial : Params (n + 1) k d)
    (D : MultiDialSignRegion thetaDial) :
    KHead.TrichotomyPredicates (MultiDialRestrictedRegion D)
      (MultiSignPoint d k → Real) where
  RegionNonempty R := R.region.Nonempty
  RegionConnected R := IsPreconnected R.region
  RegionRelativelyOpen R := RelativelyOpenIn R.region (multiSignSlab thetaDial)
  RegionSubset R S := R.region ⊆ S.region
  PositiveOn phi R := ∀ p ∈ R.region, 0 < phi p
  NegativeOn phi R := ∀ p ∈ R.region, phi p < 0
  VanishesOn phi R := ∀ p ∈ R.region, phi p = 0
  ZeroPolynomial phi := phi = 0
  Estimate order q R labels :=
    PairedTupleDialEstimate r thetaLive thetaDial D order q R labels

/-- Processing invariant with explicitly separated source/live and target/dial
parameters.  The formal slope data is source data. -/
def PairedTupleDialProcessingInvariant {n k d : Nat} (r : Nat)
    (thetaLive thetaDial : Params (n + 1) k d)
    (D : MultiDialSignRegion thetaDial)
    (baseRegion currentRegion : MultiDialRestrictedRegion D)
    (order : List DeeperHead) (q : Nat)
    (labels : DeeperHead → TrichotomyLabel) : Prop :=
  KHead.ProcessingInvariantStatement
    (pairedTupleDialPredicates r thetaLive thetaDial D)
    (tupleDialFormalData r thetaLive) baseRegion currentRegion order q labels

theorem pairedTupleDialLabelSignLink_restrict
    {n k d : Nat} {r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d}
    {D : MultiDialSignRegion thetaDial} {R S : MultiDialRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {h : DeeperHead}
    (hSR : S.region ⊆ R.region)
    (hlink : KHead.LabelSignLink
      (pairedTupleDialPredicates r thetaLive thetaDial D)
      (tupleDialFormalData r thetaLive) R labels h) :
    KHead.LabelSignLink (pairedTupleDialPredicates r thetaLive thetaDial D)
      (tupleDialFormalData r thetaLive) S labels h := by
  unfold KHead.LabelSignLink at hlink ⊢
  cases hlabel : labels h with
  | zero =>
      rw [hlabel] at hlink
      simp only [pairedTupleDialPredicates] at hlink ⊢
      exact fun p hp => hlink p (hSR hp)
  | one =>
      rw [hlabel] at hlink
      simp only [pairedTupleDialPredicates] at hlink ⊢
      exact fun p hp => hlink p (hSR hp)
  | alpha =>
      rw [hlabel] at hlink
      simpa only [pairedTupleDialPredicates] using hlink

theorem PairedTupleDialProcessingInvariant.restrict
    {n k d : Nat} {r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d}
    {D : MultiDialSignRegion thetaDial}
    {baseRegion R S : MultiDialRestrictedRegion D}
    {order : List DeeperHead} {q : Nat}
    {labels : DeeperHead → TrichotomyLabel}
    (hInv : PairedTupleDialProcessingInvariant r thetaLive thetaDial D
      baseRegion R order q labels)
    (hSR : S.region ⊆ R.region) :
    PairedTupleDialProcessingInvariant r thetaLive thetaDial D
      baseRegion S order q labels where
  region_nonempty := S.nonempty
  region_connected := S.isPreconnected
  region_relativelyOpen := S.relativelyOpen
  region_subset_base := hSR.trans hInv.region_subset_base
  label_sign_link := fun h hh => pairedTupleDialLabelSignLink_restrict hSR
    (hInv.label_sign_link h hh)
  estimate := hInv.estimate.restrict hSR

/-- The paired base estimate uses only equality of source and target
first-layer attention matrices. -/
theorem pairedTupleDialEstimate_zero {n k d : Nat} (r : Nat)
    {thetaLive thetaDial : Params (n + 1) k d}
    (D : MultiDialSignRegion thetaDial)
    (hA : ∀ a, attentionMatrix thetaLive 0 a = attentionMatrix thetaDial 0 a)
    (labels : DeeperHead → TrichotomyLabel) :
    PairedTupleDialEstimate r thetaLive thetaDial D
      (deeperHeadOrder (n + 1) k) 0 (MultiDialRestrictedRegion.full D) labels where
  firstLayer_live_eq_frozen := by
    intro p hp tau htau a
    let bp : MultiDialBasePoint D :=
      ⟨p, (MultiDialRestrictedRegion.full D).region_subset hp⟩
    change actualProbeGate r thetaLive
        (multiDialPath r thetaDial p tau).1 (multiDialPath r thetaDial p tau).2 tau
          ⟨0, Nat.succ_pos n⟩ a = p.2 a
    exact (bp.paired_firstLayer_gate_eq r hA htau a).1
  processed_gate_expClose := by
    intro x hx
    simp [KHead.processedPrefix] at hx
  compact_uniform_motion := by
    intro K hK hKD
    exact (MultiDialRestrictedRegion.full D).exists_uniform_motion_bound r hK hKD

theorem pairedTupleDialProcessingInvariant_zero {n k d : Nat} (r : Nat)
    {thetaLive thetaDial : Params (n + 1) k d}
    (D : MultiDialSignRegion thetaDial)
    (hA : ∀ a, attentionMatrix thetaLive 0 a = attentionMatrix thetaDial 0 a)
    (labels : DeeperHead → TrichotomyLabel) :
    PairedTupleDialProcessingInvariant r thetaLive thetaDial D
      (MultiDialRestrictedRegion.full D) (MultiDialRestrictedRegion.full D)
      (deeperHeadOrder (n + 1) k) 0 labels := by
  apply KHead.processingInvariant_zero
  · exact (MultiDialRestrictedRegion.full D).nonempty
  · exact (MultiDialRestrictedRegion.full D).isPreconnected
  · exact (MultiDialRestrictedRegion.full D).relativelyOpen
  · exact Set.Subset.rfl
  · exact pairedTupleDialEstimate_zero r D hA labels

theorem PairedTupleDialProcessingInvariant.processed_gate_expClose
    {n k d : Nat} {r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d}
    {D : MultiDialSignRegion thetaDial}
    {baseRegion currentRegion : MultiDialRestrictedRegion D}
    {order : List DeeperHead} {q : Nat}
    {labels : DeeperHead → TrichotomyLabel}
    (hInv : PairedTupleDialProcessingInvariant r thetaLive thetaDial D
      baseRegion currentRegion order q labels)
    (x : FormalVar (n + 1) k)
    (hx : formalVarDeeperHead x ∈ processedPrefix order q)
    (p : MultiSignPoint d k) (hp : p ∈ currentRegion.region) :
    TupleDialExpCloseTo
      (fun tau => pairedTupleDialLiveAssignment r thetaLive thetaDial p tau x)
      (tupleDialFrozenAssignment r p.2 labels x) :=
  hInv.estimate.processed_gate_expClose x hx p hp

theorem PairedTupleDialProcessingInvariant.firstLayer_live_eq_frozen
    {n k d : Nat} {r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d}
    {D : MultiDialSignRegion thetaDial}
    {baseRegion currentRegion : MultiDialRestrictedRegion D}
    {order : List DeeperHead} {q : Nat}
    {labels : DeeperHead → TrichotomyLabel}
    (hInv : PairedTupleDialProcessingInvariant r thetaLive thetaDial D
      baseRegion currentRegion order q labels)
    (p : MultiSignPoint d k) (hp : p ∈ currentRegion.region)
    (tau : Real) (htau : tau ≠ 0) (a : Fin k) :
    pairedTupleDialLiveAssignment r thetaLive thetaDial p tau
        (⟨0, Nat.succ_pos n⟩, a) =
      tupleDialFrozenAssignment r p.2 labels (⟨0, Nat.succ_pos n⟩, a) :=
  hInv.estimate.firstLayer_live_eq_frozen p hp tau htau a

theorem PairedTupleDialProcessingInvariant.compact_uniform_motion
    {n k d : Nat} {r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d}
    {D : MultiDialSignRegion thetaDial}
    {baseRegion currentRegion : MultiDialRestrictedRegion D}
    {order : List DeeperHead} {q : Nat}
    {labels : DeeperHead → TrichotomyLabel}
    (hInv : PairedTupleDialProcessingInvariant r thetaLive thetaDial D
      baseRegion currentRegion order q labels)
    (K : Set (MultiSignPoint d k)) (hK : IsCompact K)
    (hKR : K ⊆ currentRegion.region) :
    ∃ C : Real, 0 ≤ C ∧ ∀ p ∈ K, ∀ tau : Real, 1 ≤ tau →
      ‖(multiDialPath r thetaDial p tau).2 - p.1.2‖ ≤ C / tau :=
  hInv.estimate.compact_uniform_motion K hK hKR

/-! ## NS122: positive branch -/

theorem TupleDialExpCloseTo.tendsto {f : Real → Real} {a : Real}
    (h : TupleDialExpCloseTo f a) : Tendsto f atTop (nhds a) := by
  rcases h with ⟨rate, coeff, start, hrate, hcoeff, hbound⟩
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hid : Tendsto (fun tau : Real => tau) atTop atTop := by
    simpa using (Filter.tendsto_id : Tendsto id atTop atTop)
  have hrτ : Tendsto (fun tau : Real => rate * tau) atTop atTop :=
    hid.const_mul_atTop hrate
  have hneg : Tendsto (fun tau : Real => -(rate * tau)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hrτ
  have hexp : Tendsto (fun tau : Real => coeff * Real.exp (-(rate * tau)))
      atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (Real.tendsto_exp_atBot.comp hneg).const_mul coeff
  apply squeeze_zero'
  · filter_upwards with tau
    exact norm_nonneg _
  · filter_upwards [eventually_ge_atTop start] with tau htau
    simpa [Real.norm_eq_abs, neg_mul] using hbound tau htau
  · exact hexp

/-- The tuple-dial probe itself converges to its base probe. -/
theorem tendsto_multiDialPath_atTop {n k d : Nat} (r : Nat)
    (theta : Params (n + 1) k d) (p : MultiSignPoint d k) :
    Tendsto (fun tau => multiDialPath r theta p tau) atTop (nhds p.1) := by
  have hzero : Tendsto
      (fun tau : Real => tau⁻¹ • multiDialDirection r theta p.1.1 p.2)
      atTop (nhds 0) := by
    simpa using (tendsto_inv_atTop_zero (𝕜 := Real)).smul_const
      (multiDialDirection r theta p.1.1 p.2)
  have hv : Tendsto (fun tau => (multiDialPath r theta p tau).2)
      atTop (nhds p.1.2) := by
    simpa [multiDialPath] using hzero.const_add p.1.2
  exact tendsto_const_nhds.prodMk_nhds hv

/-- Continuity of one no-skip recursion step in gates and incoming streams. -/
theorem continuous_gatedEffectivePoint_data {L k d : Nat}
    (theta : Params L k d) (l : Fin L) :
    Continuous (fun z : (Fin k → Real) × ProbePoint d =>
      gatedEffectivePoint theta l z.1 z.2.1 z.2.2) := by
  unfold gatedEffectivePoint gatedValueSum KHead.gatedValueSum
  fun_prop

/-- If every gate in layers before `q` tends to its tuple-frozen value, the
entire live stream through layer `q` tends to the frozen recursion at the base
probe.  This is where the `O(1/tau)` probe motion enters the branch proof. -/
theorem tendsto_actualProbePoint_multiDial_to_frozen {n k d : Nat} (r : Nat)
    (theta : Params (n + 1) k d) (p : MultiSignPoint d k)
    (labels : DeeperHead → TrichotomyLabel) :
    ∀ (q : Nat) (hq : q ≤ n + 1),
      (∀ (l : Fin (n + 1)), l.1 < q → ∀ a : Fin k,
        Tendsto (fun tau => tupleDialLiveAssignment r theta p tau (l, a))
          atTop (nhds (tupleDialFrozenAssignment r p.2 labels (l, a)))) →
      Tendsto (fun tau => actualProbePoint r theta
          (multiDialPath r theta p tau).1 (multiDialPath r theta p tau).2 q hq tau)
        atTop
        (nhds (frozenPoint theta (tupleDialFrozenFamily r p.2 labels)
          p.1.1 p.1.2 q hq)) := by
  intro q
  induction q with
  | zero =>
      intro hq _hgate
      simpa using tendsto_multiDialPath_atTop r theta p
  | succ q ih =>
      intro hq hgate
      let l : Fin (n + 1) := ⟨q, Nat.lt_of_succ_le hq⟩
      have hprev := ih (Nat.le_of_succ_le hq)
        (fun l' hl' a => hgate l' (lt_trans hl' (Nat.lt_succ_self q)) a)
      have hgates : Tendsto
          (fun tau a => tupleDialLiveAssignment r theta p tau (l, a))
          atTop (nhds (fun a => tupleDialFrozenAssignment r p.2 labels (l, a))) :=
        tendsto_pi_nhds.mpr (fun a => hgate l (Nat.lt_succ_self q) a)
      have hdata := hgates.prodMk_nhds hprev
      have hstep := (continuous_gatedEffectivePoint_data theta l).continuousAt.tendsto.comp hdata
      simpa [actualProbePoint_succ, frozenPoint_succ, l, tupleDialLiveAssignment,
        actualProbeGateAssignment, tupleDialFrozenAssignment, frozenGateAssignment]
        using hstep

/-- Every gate in a layer strictly before the current deeper head converges to
its frozen tuple value, solely from the processing invariant. -/
theorem tendsto_prior_tupleGate_of_processingInvariant
    {n k d : Nat} {r : Nat} {theta : Params (n + 1) k d}
    {D : MultiDialSignRegion theta}
    {baseRegion currentRegion : MultiDialRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx q : Nat} {a : Fin k}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (hcurrent : (deeperHeadOrder (n + 1) k)[idx] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    (hInv : TupleDialProcessingInvariant r theta D baseRegion currentRegion
      (deeperHeadOrder (n + 1) k) idx labels)
    (p : MultiSignPoint d k) (hp : p ∈ currentRegion.region)
    (l : Fin (n + 1)) (hl : l.1 < q) (b : Fin k) :
    Tendsto (fun tau => tupleDialLiveAssignment r theta p tau (l, b))
      atTop (nhds (tupleDialFrozenAssignment r p.2 labels (l, b))) := by
  by_cases hl0 : l.1 = 0
  · have heq : ∀ᶠ tau : Real in atTop,
        tupleDialLiveAssignment r theta p tau (l, b) =
          tupleDialFrozenAssignment r p.2 labels (l, b) := by
      filter_upwards [eventually_ge_atTop (1 : Real)] with tau htau
      have htau0 : tau ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one htau)
      have lzero : l = ⟨0, Nat.succ_pos n⟩ := by
        apply Fin.ext
        exact hl0
      subst l
      exact hInv.firstLayer_live_eq_frozen p hp tau htau0 b
    exact Filter.Tendsto.congr' (Filter.EventuallyEq.symm heq) tendsto_const_nhds
  · have hlpos : 1 ≤ l.1 := Nat.one_le_iff_ne_zero.mpr hl0
    have hprocessed : formalVarDeeperHead (l, b) ∈
        processedPrefix (deeperHeadOrder (n + 1) k) idx := by
      exact KHead.succ_head_mem_processedPrefix_of_layer_lt_getElem_deeperHeadOrder
        hidx hcurrent hlpos l.2 hl b
    exact (hInv.processed_gate_expClose (l, b) hprocessed p hp).tendsto

/-- The current actual slope converges to its faithful frozen tuple slope. -/
theorem tendsto_currentTupleSlope_of_processingInvariant
    {n k d : Nat} {r : Nat} {theta : Params (n + 1) k d}
    {D : MultiDialSignRegion theta}
    {baseRegion currentRegion : MultiDialRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx q : Nat} {a : Fin k}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (hqpos : 1 ≤ q) (hq : q < n + 1)
    (hcurrent : (deeperHeadOrder (n + 1) k)[idx] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    (hInv : TupleDialProcessingInvariant r theta D baseRegion currentRegion
      (deeperHeadOrder (n + 1) k) idx labels)
    (p : MultiSignPoint d k) (hp : p ∈ currentRegion.region) :
    Tendsto (fun tau => actualProbeSlope r theta
        (multiDialPath r theta p tau).1 (multiDialPath r theta p tau).2 tau
        ⟨q, hq⟩ a)
      atTop
      (nhds (tupleDialFrozenSlopeForm r theta
        (deeperHeadOrder (n + 1) k)[idx] labels p)) := by
  have hpoint := tendsto_actualProbePoint_multiDial_to_frozen r theta p labels q
    (Nat.le_of_lt hq) (fun l hl b =>
      tendsto_prior_tupleGate_of_processingInvariant hidx hcurrent hInv p hp l hl b)
  have hcont : Continuous (fun z : ProbePoint d =>
      matrixBilin (attentionMatrix theta ⟨q, hq⟩ a) z.1 z.2) := by
    unfold matrixBilin KHead.matrixBilin Matrix.mulVec dotProduct
    fun_prop
  have hslope := hcont.continuousAt.tendsto.comp hpoint
  have hvalid : 2 ≤ q + 1 ∧ q + 1 ≤ n + 1 ∧
      1 ≤ (a : Nat) + 1 ∧ (a : Nat) + 1 ≤ k := by
    constructor
    · omega
    constructor
    · omega
    constructor
    · omega
    · exact Nat.succ_le_of_lt a.2
  have hslope' : Tendsto (fun tau => matrixBilin
        (attentionMatrix theta ⟨q, hq⟩ a)
        (actualProbePoint r theta
          (multiDialPath r theta p tau).1 (multiDialPath r theta p tau).2
          q (Nat.le_of_lt hq) tau).1
        (actualProbePoint r theta
          (multiDialPath r theta p tau).1 (multiDialPath r theta p tau).2
          q (Nat.le_of_lt hq) tau).2)
      atTop (nhds (matrixBilin (attentionMatrix theta ⟨q, hq⟩ a)
        (frozenPoint theta (tupleDialFrozenFamily r p.2 labels)
          p.1.1 p.1.2 q (Nat.le_of_lt hq)).1
        (frozenPoint theta (tupleDialFrozenFamily r p.2 labels)
          p.1.1 p.1.2 q (Nat.le_of_lt hq)).2)) := by
    simpa [Function.comp_def] using hslope
  have htarget : tupleDialFrozenSlopeForm r theta
      (deeperHeadOrder (n + 1) k)[idx] labels p =
      matrixBilin (attentionMatrix theta ⟨q, hq⟩ a)
        (frozenPoint theta (tupleDialFrozenFamily r p.2 labels)
          p.1.1 p.1.2 q (Nat.le_of_lt hq)).1
        (frozenPoint theta (tupleDialFrozenFamily r p.2 labels)
          p.1.1 p.1.2 q (Nat.le_of_lt hq)).2 := by
    rw [hcurrent]
    rw [tupleDialFrozenSlopeForm, dif_pos hvalid]
    change MvPolynomial.eval (tupleDialFrozenAssignment r p.2 labels)
        (formalSlope theta p.1.1 p.1.2 ⟨q, by omega⟩ ⟨a.1, by omega⟩) = _
    rw [formalSlope, eval_formalBilin]
    change matrixBilin (attentionMatrix theta ⟨q, hq⟩ a)
      (evalFormalVec (frozenGateAssignment (tupleDialFrozenFamily r p.2 labels))
        (formalW theta p.1.1 p.1.2 q (Nat.le_of_lt hq)))
      (evalFormalVec (frozenGateAssignment (tupleDialFrozenFamily r p.2 labels))
        (formalV theta p.1.1 p.1.2 q (Nat.le_of_lt hq))) = _
    have hfp := eval_formalPoint_frozenGateAssignment theta
      (tupleDialFrozenFamily r p.2 labels) p.1.1 p.1.2 q (Nat.le_of_lt hq)
    rw [show evalFormalVec (frozenGateAssignment (tupleDialFrozenFamily r p.2 labels))
          (formalW theta p.1.1 p.1.2 q (Nat.le_of_lt hq)) =
          (frozenPoint theta (tupleDialFrozenFamily r p.2 labels)
            p.1.1 p.1.2 q (Nat.le_of_lt hq)).1 from hfp.1,
      show evalFormalVec (frozenGateAssignment (tupleDialFrozenFamily r p.2 labels))
          (formalV theta p.1.1 p.1.2 q (Nat.le_of_lt hq)) =
          (frozenPoint theta (tupleDialFrozenFamily r p.2 labels)
            p.1.1 p.1.2 q (Nat.le_of_lt hq)).2 from hfp.2]
  rw [htarget]
  simpa [actualProbeSlope] using hslope'

/-- Frozen tuple streams vary continuously with the chart base point. -/
theorem continuous_frozenPoint_tupleDial {n k d : Nat} (r : Nat)
    (theta : Params (n + 1) k d) (labels : DeeperHead → TrichotomyLabel) :
    ∀ (q : Nat) (hq : q ≤ n + 1),
      Continuous (fun p : MultiSignPoint d k =>
        frozenPoint theta (tupleDialFrozenFamily r p.2 labels)
          p.1.1 p.1.2 q hq) := by
  intro q
  induction q with
  | zero =>
      intro hq
      simpa using (continuous_fst.comp continuous_fst).prodMk
        (continuous_snd.comp continuous_fst)
  | succ q ih =>
      intro hq
      let l : Fin (n + 1) := ⟨q, Nat.lt_of_succ_le hq⟩
      have hprev := ih (Nat.le_of_succ_le hq)
      have hgates : Continuous (fun p : MultiSignPoint d k =>
          tupleDialFrozenFamily r p.2 labels l) := by
        apply continuous_pi
        intro a
        by_cases hq0 : q = 0
        · subst q
          simpa [tupleDialFrozenFamily] using
            ((continuous_apply a).comp continuous_snd)
        · simpa [tupleDialFrozenFamily, l, hq0] using
            (continuous_const : Continuous (fun _ : MultiSignPoint d k =>
              trichotomyLabelValue r (labels (formalVarDeeperHead (l, a)))))
      have hdata := hgates.prodMk hprev
      have hstep := (continuous_gatedEffectivePoint_data theta l).comp hdata
      change Continuous (fun p : MultiSignPoint d k =>
        gatedEffectivePoint theta l
          (tupleDialFrozenFamily r p.2 labels l)
          (frozenPoint theta (tupleDialFrozenFamily r p.2 labels)
            p.1.1 p.1.2 q (Nat.le_of_succ_le hq)).1
          (frozenPoint theta (tupleDialFrozenFamily r p.2 labels)
            p.1.1 p.1.2 q (Nat.le_of_succ_le hq)).2)
      exact hstep

/-- Continuity of the current faithful frozen slope on the whole tuple chart. -/
theorem continuous_currentTupleFrozenSlope
    {n k d : Nat} (r : Nat) (theta : Params (n + 1) k d)
    (labels : DeeperHead → TrichotomyLabel) {idx q : Nat} {a : Fin k}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (hqpos : 1 ≤ q) (hq : q < n + 1)
    (hcurrent : (deeperHeadOrder (n + 1) k)[idx] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead)) :
    Continuous (tupleDialFrozenSlopeForm r theta
      (deeperHeadOrder (n + 1) k)[idx] labels) := by
  have hvalid : 2 ≤ q + 1 ∧ q + 1 ≤ n + 1 ∧
      1 ≤ (a : Nat) + 1 ∧ (a : Nat) + 1 ≤ k := by
    constructor
    · omega
    constructor
    · omega
    constructor
    · omega
    · exact Nat.succ_le_of_lt a.2
  have heq : tupleDialFrozenSlopeForm r theta
      (deeperHeadOrder (n + 1) k)[idx] labels =
      fun p => matrixBilin (attentionMatrix theta ⟨q, hq⟩ a)
        (frozenPoint theta (tupleDialFrozenFamily r p.2 labels)
          p.1.1 p.1.2 q (Nat.le_of_lt hq)).1
        (frozenPoint theta (tupleDialFrozenFamily r p.2 labels)
          p.1.1 p.1.2 q (Nat.le_of_lt hq)).2 := by
    funext p
    rw [hcurrent, tupleDialFrozenSlopeForm, dif_pos hvalid]
    change MvPolynomial.eval (frozenGateAssignment (tupleDialFrozenFamily r p.2 labels))
      (formalSlope theta p.1.1 p.1.2 ⟨q, by omega⟩ ⟨a.1, by omega⟩) = _
    rw [formalSlope, eval_formalBilin]
    have hfp := eval_formalPoint_frozenGateAssignment theta
      (tupleDialFrozenFamily r p.2 labels) p.1.1 p.1.2 q (Nat.le_of_lt hq)
    change matrixBilin (attentionMatrix theta ⟨q, hq⟩ a)
      (evalFormalVec (frozenGateAssignment (tupleDialFrozenFamily r p.2 labels))
        (formalW theta p.1.1 p.1.2 q (Nat.le_of_lt hq)))
      (evalFormalVec (frozenGateAssignment (tupleDialFrozenFamily r p.2 labels))
        (formalV theta p.1.1 p.1.2 q (Nat.le_of_lt hq))) = _
    rw [show evalFormalVec (frozenGateAssignment (tupleDialFrozenFamily r p.2 labels))
          (formalW theta p.1.1 p.1.2 q (Nat.le_of_lt hq)) =
          (frozenPoint theta (tupleDialFrozenFamily r p.2 labels)
            p.1.1 p.1.2 q (Nat.le_of_lt hq)).1 from hfp.1,
      show evalFormalVec (frozenGateAssignment (tupleDialFrozenFamily r p.2 labels))
          (formalV theta p.1.1 p.1.2 q (Nat.le_of_lt hq)) =
          (frozenPoint theta (tupleDialFrozenFamily r p.2 labels)
            p.1.1 p.1.2 q (Nat.le_of_lt hq)).2 from hfp.2]
  rw [heq]
  have hpnt := continuous_frozenPoint_tupleDial r theta labels q (Nat.le_of_lt hq)
  unfold matrixBilin KHead.matrixBilin Matrix.mulVec dotProduct
  fun_prop

/-- Pointwise positive-branch output: positivity is imposed only on the frozen
slope; live-slope convergence is derived from the invariant, and sigmoid
saturation then gives exponential convergence of the current live gate to `1`. -/
theorem currentTupleGate_expClose_one_of_frozen_pos
    {n k d : Nat} {r : Nat} {theta : Params (n + 1) k d}
    {D : MultiDialSignRegion theta}
    {baseRegion currentRegion : MultiDialRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx q : Nat} {a : Fin k}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (hqpos : 1 ≤ q) (hq : q < n + 1)
    (hcurrent : (deeperHeadOrder (n + 1) k)[idx] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    (hInv : TupleDialProcessingInvariant r theta D baseRegion currentRegion
      (deeperHeadOrder (n + 1) k) idx labels)
    (p : MultiSignPoint d k) (hp : p ∈ currentRegion.region)
    (hpos : 0 < tupleDialFrozenSlopeForm r theta
      (deeperHeadOrder (n + 1) k)[idx] labels p) :
    TupleDialExpCloseTo
      (fun tau => tupleDialLiveAssignment r theta p tau (⟨q, hq⟩, a)) 1 := by
  have hslope := tendsto_currentTupleSlope_of_processingInvariant
    hidx hqpos hq hcurrent hInv p hp
  have hsat := KHead.expCloseTo_sig_of_tendsto_pos (b := logScale r) hpos hslope
  simpa [TupleDialExpCloseTo, KHead.ExpCloseTo, tupleDialLiveAssignment,
    actualProbeGateAssignment, actualProbeGate_eq_sig] using hsat

/-- Restrict to an open connected chart neighbourhood on which the current
frozen slope is positive. -/
theorem exists_positiveTupleDialRestriction
    {n k d : Nat} {r : Nat} {theta : Params (n + 1) k d}
    {D : MultiDialSignRegion theta} (R : MultiDialRestrictedRegion D)
    (labels : DeeperHead → TrichotomyLabel) {idx q : Nat} {a : Fin k}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (hqpos : 1 ≤ q) (hq : q < n + 1)
    (hcurrent : (deeperHeadOrder (n + 1) k)[idx] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    {p : MultiSignPoint d k} (hp : p ∈ R.region)
    (hpos : 0 < tupleDialFrozenSlopeForm r theta
      (deeperHeadOrder (n + 1) k)[idx] labels p) :
    ∃ R' : MultiDialRestrictedRegion D,
      p ∈ R'.region ∧ R'.region ⊆ R.region ∧
      ∀ x ∈ R'.region, 0 < tupleDialFrozenSlopeForm r theta
        (deeperHeadOrder (n + 1) k)[idx] labels x := by
  let phi := tupleDialFrozenSlopeForm r theta
    (deeperHeadOrder (n + 1) k)[idx] labels
  let O : Set (MultiSignPoint d k) := {x | 0 < phi x}
  have hphi : Continuous phi :=
    continuous_currentTupleFrozenSlope r theta labels hidx hqpos hq hcurrent
  have hO : IsOpen O := isOpen_Ioi.preimage hphi
  have hpO : p ∈ O := hpos
  rcases R.exists_restrict_ambientOpen hO hp hpO with ⟨R', hpR', hsub⟩
  refine ⟨R', hpR', fun x hx => (hsub hx).1, ?_⟩
  intro x hx
  exact (hsub hx).2

/-- On every nonempty compact subset of a positive branch restriction, the
frozen slope has a strictly positive uniform margin. -/
theorem exists_compact_positiveTupleSlope_margin
    {n k d : Nat} {r : Nat} {theta : Params (n + 1) k d}
    {D : MultiDialSignRegion theta} {R : MultiDialRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx q : Nat} {a : Fin k}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (hqpos : 1 ≤ q) (hq : q < n + 1)
    (hcurrent : (deeperHeadOrder (n + 1) k)[idx] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    (hpositive : ∀ x ∈ R.region, 0 < tupleDialFrozenSlopeForm r theta
      (deeperHeadOrder (n + 1) k)[idx] labels x)
    {K : Set (MultiSignPoint d k)} (hK : IsCompact K) (hKne : K.Nonempty)
    (hKR : K ⊆ R.region) :
    ∃ eta : Real, 0 < eta ∧ ∀ x ∈ K,
      eta ≤ tupleDialFrozenSlopeForm r theta
        (deeperHeadOrder (n + 1) k)[idx] labels x := by
  let phi := tupleDialFrozenSlopeForm r theta
    (deeperHeadOrder (n + 1) k)[idx] labels
  have hcont : Continuous phi :=
    continuous_currentTupleFrozenSlope r theta labels hidx hqpos hq hcurrent
  obtain ⟨x0, hx0K, hx0min⟩ := hK.exists_isMinOn hKne hcont.continuousOn
  refine ⟨phi x0, hpositive x0 (hKR hx0K), ?_⟩
  intro x hxK
  exact hx0min hxK

/-- Update the honest estimate after the positive current gate has been proved.
All old processed estimates restrict and keep the same frozen targets; the new
entry is supplied by `currentTupleGate_expClose_one_of_frozen_pos`. -/
theorem TupleDialEstimate.extend_one
    {n k d : Nat} {r : Nat} {theta : Params (n + 1) k d}
    {D : MultiDialSignRegion theta}
    {R S : MultiDialRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx q : Nat} {a : Fin k}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (hqpos : 1 ≤ q) (hq : q < n + 1)
    (hcurrent : (deeperHeadOrder (n + 1) k)[idx] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    (hSR : S.region ⊆ R.region)
    (hEst : TupleDialEstimate r theta D (deeperHeadOrder (n + 1) k)
      idx R labels)
    (hgate : ∀ p ∈ S.region, TupleDialExpCloseTo
      (fun tau => tupleDialLiveAssignment r theta p tau (⟨q, hq⟩, a)) 1) :
    TupleDialEstimate r theta D (deeperHeadOrder (n + 1) k) (idx + 1) S
      (setLabel labels (deeperHeadOrder (n + 1) k)[idx] KHead.TrichotomyLabel.one) where
  firstLayer_live_eq_frozen := by
    intro p hp tau htau b
    have hold := hEst.firstLayer_live_eq_frozen p (hSR hp) tau htau b
    simpa [tupleDialFrozenAssignment_first] using hold
  processed_gate_expClose := by
    intro x hx p hp
    have hsplit := (KHead.mem_processedPrefix_succ_iff_getElem hidx).mp hx
    rcases hsplit with hold | hnew
    · have hnot : (deeperHeadOrder (n + 1) k)[idx] ∉
          processedPrefix (deeperHeadOrder (n + 1) k) idx :=
        getElem_not_mem_processedPrefix_of_nodup
          (KHead.deeperHeadOrder_nodup (n + 1) k) hidx
      have hne : formalVarDeeperHead x ≠ (deeperHeadOrder (n + 1) k)[idx] := by
        intro heq
        exact hnot (heq ▸ hold)
      have holdEst := hEst.processed_gate_expClose x hold p (hSR hp)
      have htarget : tupleDialFrozenAssignment r p.2
          (setLabel labels (deeperHeadOrder (n + 1) k)[idx]
            KHead.TrichotomyLabel.one) x =
          tupleDialFrozenAssignment r p.2 labels x := by
        rcases x with ⟨l, b⟩
        by_cases hl0 : l.1 = 0
        · simp [tupleDialFrozenAssignment, tupleDialFrozenFamily, hl0]
        · simp [tupleDialFrozenAssignment, tupleDialFrozenFamily, hl0,
            setLabel_of_ne labels KHead.TrichotomyLabel.one hne]
      rw [htarget]
      exact holdEst
    · have hdh : formalVarDeeperHead x =
          ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead) := by
        rw [hnew, hcurrent]
      have hx : x = (⟨q, hq⟩, a) := by
        rcases x with ⟨l, b⟩
        apply Prod.ext
        · apply Fin.ext
          simpa [formalVarDeeperHead] using congrArg (fun z : DeeperHead => z.layer) hdh
        · apply Fin.ext
          simpa [formalVarDeeperHead] using congrArg (fun z : DeeperHead => z.head) hdh
      subst x
      simpa [tupleDialFrozenAssignment, tupleDialFrozenFamily, Nat.ne_of_gt hqpos,
        formalVarDeeperHead, hcurrent, setLabel_self] using hgate p hp
  compact_uniform_motion := by
    intro K hK hKS
    exact S.exists_uniform_motion_bound r hK hKS

/-- Complete positive-branch package at one processing slot.  The returned
region is an NS120 restriction, positivity is a proved frozen-slope fact,
current live-gate saturation is derived from the old invariant, and the
successor estimate preserves every prior head while adding the current one. -/
theorem exists_positiveTupleDialBranch
    {n k d : Nat} {r : Nat} {theta : Params (n + 1) k d}
    {D : MultiDialSignRegion theta}
    {baseRegion currentRegion : MultiDialRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx q : Nat} {a : Fin k}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (hqpos : 1 ≤ q) (hq : q < n + 1)
    (hcurrent : (deeperHeadOrder (n + 1) k)[idx] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    (hInv : TupleDialProcessingInvariant r theta D baseRegion currentRegion
      (deeperHeadOrder (n + 1) k) idx labels)
    {p : MultiSignPoint d k} (hp : p ∈ currentRegion.region)
    (hpos : 0 < tupleDialFrozenSlopeForm r theta
      (deeperHeadOrder (n + 1) k)[idx] labels p) :
    ∃ nextRegion : MultiDialRestrictedRegion D,
      p ∈ nextRegion.region ∧
      nextRegion.region ⊆ currentRegion.region ∧
      (∀ x ∈ nextRegion.region, 0 < tupleDialFrozenSlopeForm r theta
        (deeperHeadOrder (n + 1) k)[idx] labels x) ∧
      (∀ x ∈ nextRegion.region, TupleDialExpCloseTo
        (fun tau => tupleDialLiveAssignment r theta x tau (⟨q, hq⟩, a)) 1) ∧
      TupleDialEstimate r theta D (deeperHeadOrder (n + 1) k) (idx + 1)
        nextRegion
        (setLabel labels (deeperHeadOrder (n + 1) k)[idx]
          KHead.TrichotomyLabel.one) := by
  rcases exists_positiveTupleDialRestriction currentRegion labels hidx hqpos hq
      hcurrent hp hpos with ⟨nextRegion, hpnext, hsub, hpositive⟩
  have hgate : ∀ x ∈ nextRegion.region, TupleDialExpCloseTo
      (fun tau => tupleDialLiveAssignment r theta x tau (⟨q, hq⟩, a)) 1 := by
    intro x hx
    exact currentTupleGate_expClose_one_of_frozen_pos hidx hqpos hq hcurrent
      hInv x (hsub hx) (hpositive x hx)
  have hestimate := hInv.estimate.extend_one hidx hqpos hq hcurrent hsub hgate
  exact ⟨nextRegion, hpnext, hsub, hpositive, hgate, hestimate⟩

/-! ## NS123: negative branch -/

/-- Pointwise negative-branch output: a negative faithful frozen slope and the
processing invariant force the current live gate exponentially to zero. -/
theorem currentTupleGate_expClose_zero_of_frozen_neg
    {n k d : Nat} {r : Nat} {theta : Params (n + 1) k d}
    {D : MultiDialSignRegion theta}
    {baseRegion currentRegion : MultiDialRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx q : Nat} {a : Fin k}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (hqpos : 1 ≤ q) (hq : q < n + 1)
    (hcurrent : (deeperHeadOrder (n + 1) k)[idx] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    (hInv : TupleDialProcessingInvariant r theta D baseRegion currentRegion
      (deeperHeadOrder (n + 1) k) idx labels)
    (p : MultiSignPoint d k) (hp : p ∈ currentRegion.region)
    (hneg : tupleDialFrozenSlopeForm r theta
      (deeperHeadOrder (n + 1) k)[idx] labels p < 0) :
    TupleDialExpCloseTo
      (fun tau => tupleDialLiveAssignment r theta p tau (⟨q, hq⟩, a)) 0 := by
  have hslope := tendsto_currentTupleSlope_of_processingInvariant
    hidx hqpos hq hcurrent hInv p hp
  have hsat := KHead.expCloseTo_sig_of_tendsto_neg (b := logScale r) hneg hslope
  simpa [TupleDialExpCloseTo, KHead.ExpCloseTo, tupleDialLiveAssignment,
    actualProbeGateAssignment, actualProbeGate_eq_sig] using hsat

/-- Restrict to an open connected chart neighbourhood on which the current
faithful frozen slope is negative. -/
theorem exists_negativeTupleDialRestriction
    {n k d : Nat} {r : Nat} {theta : Params (n + 1) k d}
    {D : MultiDialSignRegion theta} (R : MultiDialRestrictedRegion D)
    (labels : DeeperHead → TrichotomyLabel) {idx q : Nat} {a : Fin k}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (hqpos : 1 ≤ q) (hq : q < n + 1)
    (hcurrent : (deeperHeadOrder (n + 1) k)[idx] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    {p : MultiSignPoint d k} (hp : p ∈ R.region)
    (hneg : tupleDialFrozenSlopeForm r theta
      (deeperHeadOrder (n + 1) k)[idx] labels p < 0) :
    ∃ R' : MultiDialRestrictedRegion D,
      p ∈ R'.region ∧ R'.region ⊆ R.region ∧
      ∀ x ∈ R'.region, tupleDialFrozenSlopeForm r theta
        (deeperHeadOrder (n + 1) k)[idx] labels x < 0 := by
  let phi := tupleDialFrozenSlopeForm r theta
    (deeperHeadOrder (n + 1) k)[idx] labels
  let O : Set (MultiSignPoint d k) := {x | phi x < 0}
  have hphi : Continuous phi :=
    continuous_currentTupleFrozenSlope r theta labels hidx hqpos hq hcurrent
  have hO : IsOpen O := isOpen_Iio.preimage hphi
  have hpO : p ∈ O := hneg
  rcases R.exists_restrict_ambientOpen hO hp hpO with ⟨R', hpR', hsub⟩
  refine ⟨R', hpR', fun x hx => (hsub hx).1, ?_⟩
  intro x hx
  exact (hsub hx).2

/-- Every nonempty compact subset of a negative branch restriction has one
strict negative margin for the current frozen slope. -/
theorem exists_compact_negativeTupleSlope_margin
    {n k d : Nat} {r : Nat} {theta : Params (n + 1) k d}
    {D : MultiDialSignRegion theta} {R : MultiDialRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx q : Nat} {a : Fin k}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (hqpos : 1 ≤ q) (hq : q < n + 1)
    (hcurrent : (deeperHeadOrder (n + 1) k)[idx] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    (hnegative : ∀ x ∈ R.region, tupleDialFrozenSlopeForm r theta
      (deeperHeadOrder (n + 1) k)[idx] labels x < 0)
    {K : Set (MultiSignPoint d k)} (hK : IsCompact K) (hKne : K.Nonempty)
    (hKR : K ⊆ R.region) :
    ∃ eta : Real, 0 < eta ∧ ∀ x ∈ K,
      tupleDialFrozenSlopeForm r theta
        (deeperHeadOrder (n + 1) k)[idx] labels x ≤ -eta := by
  let phi := tupleDialFrozenSlopeForm r theta
    (deeperHeadOrder (n + 1) k)[idx] labels
  have hcont : Continuous phi :=
    continuous_currentTupleFrozenSlope r theta labels hidx hqpos hq hcurrent
  obtain ⟨x0, hx0K, hx0max⟩ := hK.exists_isMaxOn hKne hcont.continuousOn
  refine ⟨-(phi x0), by linarith [hnegative x0 (hKR hx0K)], ?_⟩
  intro x hxK
  simpa using hx0max hxK

/-- Update the honest estimate after proving the negative current gate.  Old
processed estimates restrict unchanged, and the new entry has frozen target
zero under the updated label. -/
theorem TupleDialEstimate.extend_zero
    {n k d : Nat} {r : Nat} {theta : Params (n + 1) k d}
    {D : MultiDialSignRegion theta}
    {R S : MultiDialRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx q : Nat} {a : Fin k}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (hqpos : 1 ≤ q) (hq : q < n + 1)
    (hcurrent : (deeperHeadOrder (n + 1) k)[idx] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    (hSR : S.region ⊆ R.region)
    (hEst : TupleDialEstimate r theta D (deeperHeadOrder (n + 1) k)
      idx R labels)
    (hgate : ∀ p ∈ S.region, TupleDialExpCloseTo
      (fun tau => tupleDialLiveAssignment r theta p tau (⟨q, hq⟩, a)) 0) :
    TupleDialEstimate r theta D (deeperHeadOrder (n + 1) k) (idx + 1) S
      (setLabel labels (deeperHeadOrder (n + 1) k)[idx]
        KHead.TrichotomyLabel.zero) where
  firstLayer_live_eq_frozen := by
    intro p hp tau htau b
    have hold := hEst.firstLayer_live_eq_frozen p (hSR hp) tau htau b
    simpa [tupleDialFrozenAssignment_first] using hold
  processed_gate_expClose := by
    intro x hx p hp
    have hsplit := (KHead.mem_processedPrefix_succ_iff_getElem hidx).mp hx
    rcases hsplit with hold | hnew
    · have hnot : (deeperHeadOrder (n + 1) k)[idx] ∉
          processedPrefix (deeperHeadOrder (n + 1) k) idx :=
        getElem_not_mem_processedPrefix_of_nodup
          (KHead.deeperHeadOrder_nodup (n + 1) k) hidx
      have hne : formalVarDeeperHead x ≠ (deeperHeadOrder (n + 1) k)[idx] := by
        intro heq
        exact hnot (heq ▸ hold)
      have holdEst := hEst.processed_gate_expClose x hold p (hSR hp)
      have htarget : tupleDialFrozenAssignment r p.2
          (setLabel labels (deeperHeadOrder (n + 1) k)[idx]
            KHead.TrichotomyLabel.zero) x =
          tupleDialFrozenAssignment r p.2 labels x := by
        rcases x with ⟨l, b⟩
        by_cases hl0 : l.1 = 0
        · simp [tupleDialFrozenAssignment, tupleDialFrozenFamily, hl0]
        · simp [tupleDialFrozenAssignment, tupleDialFrozenFamily, hl0,
            setLabel_of_ne labels KHead.TrichotomyLabel.zero hne]
      rw [htarget]
      exact holdEst
    · have hdh : formalVarDeeperHead x =
          ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead) := by
        rw [hnew, hcurrent]
      have hx : x = (⟨q, hq⟩, a) := by
        rcases x with ⟨l, b⟩
        apply Prod.ext
        · apply Fin.ext
          simpa [formalVarDeeperHead] using
            congrArg (fun z : DeeperHead => z.layer) hdh
        · apply Fin.ext
          simpa [formalVarDeeperHead] using
            congrArg (fun z : DeeperHead => z.head) hdh
      subst x
      simpa [tupleDialFrozenAssignment, tupleDialFrozenFamily, Nat.ne_of_gt hqpos,
        formalVarDeeperHead, hcurrent, setLabel_self] using hgate p hp
  compact_uniform_motion := by
    intro K hK hKS
    exact S.exists_uniform_motion_bound r hK hKS

/-- Complete negative-branch package at one processing slot.  The returned
chart restriction is connected and relatively open by construction; the
current gate converges exponentially to zero, and the successor estimate
retains all previously processed gates while adding the current zero label. -/
theorem exists_negativeTupleDialBranch
    {n k d : Nat} {r : Nat} {theta : Params (n + 1) k d}
    {D : MultiDialSignRegion theta}
    {baseRegion currentRegion : MultiDialRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx q : Nat} {a : Fin k}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (hqpos : 1 ≤ q) (hq : q < n + 1)
    (hcurrent : (deeperHeadOrder (n + 1) k)[idx] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    (hInv : TupleDialProcessingInvariant r theta D baseRegion currentRegion
      (deeperHeadOrder (n + 1) k) idx labels)
    {p : MultiSignPoint d k} (hp : p ∈ currentRegion.region)
    (hneg : tupleDialFrozenSlopeForm r theta
      (deeperHeadOrder (n + 1) k)[idx] labels p < 0) :
    ∃ nextRegion : MultiDialRestrictedRegion D,
      p ∈ nextRegion.region ∧
      nextRegion.region ⊆ currentRegion.region ∧
      (∀ x ∈ nextRegion.region, tupleDialFrozenSlopeForm r theta
        (deeperHeadOrder (n + 1) k)[idx] labels x < 0) ∧
      (∀ x ∈ nextRegion.region, TupleDialExpCloseTo
        (fun tau => tupleDialLiveAssignment r theta x tau (⟨q, hq⟩, a)) 0) ∧
      TupleDialEstimate r theta D (deeperHeadOrder (n + 1) k) (idx + 1)
        nextRegion
        (setLabel labels (deeperHeadOrder (n + 1) k)[idx]
          KHead.TrichotomyLabel.zero) := by
  rcases exists_negativeTupleDialRestriction currentRegion labels hidx hqpos hq
      hcurrent hp hneg with ⟨nextRegion, hpnext, hsub, hnegative⟩
  have hgate : ∀ x ∈ nextRegion.region, TupleDialExpCloseTo
      (fun tau => tupleDialLiveAssignment r theta x tau (⟨q, hq⟩, a)) 0 := by
    intro x hx
    exact currentTupleGate_expClose_zero_of_frozen_neg hidx hqpos hq hcurrent
      hInv x (hsub hx) (hnegative x hx)
  have hestimate := hInv.estimate.extend_zero hidx hqpos hq hcurrent hsub hgate
  exact ⟨nextRegion, hpnext, hsub, hnegative, hgate, hestimate⟩

/-! ## NS124: zero-branch tuple polynomial -/

/-- Substitute the independent first-layer tuple by polynomial variables and
all deeper heads by their fixed trichotomy constants. -/
noncomputable def tupleDialPolynomialSubstitution {n k : Nat} (r : Nat)
    (labels : DeeperHead → TrichotomyLabel) (x : FormalVar (n + 1) k) :
    MvPolynomial (Fin k) Real :=
  if x.1.1 = 0 then MvPolynomial.X x.2
  else MvPolynomial.C
    (trichotomyLabelValue r (labels (formalVarDeeperHead x)))

/-- The current faithful frozen slope as an honest multivariate polynomial in
the complete first-layer dial tuple.  Probe vectors remain parameters here;
NS125 is responsible for rigidity in those slice coordinates. -/
noncomputable def tupleDialFrozenSlopePoly {n k d : Nat} (r : Nat)
    (theta : Params (n + 1) k d) (labels : DeeperHead → TrichotomyLabel)
    (w v : Vec d) (l : Fin (n + 1)) (a : Fin k) :
    MvPolynomial (Fin k) Real :=
  MvPolynomial.bind₁ (tupleDialPolynomialSubstitution r labels)
    (formalSlope theta w v l a)

@[simp] theorem eval_tupleDialPolynomialSubstitution {n k : Nat} (r : Nat)
    (labels : DeeperHead → TrichotomyLabel) (t : Fin k → Real)
    (x : FormalVar (n + 1) k) :
    MvPolynomial.eval t (tupleDialPolynomialSubstitution r labels x) =
      tupleDialFrozenAssignment r t labels x := by
  rcases x with ⟨l, a⟩
  by_cases hl0 : l.1 = 0
  · have hl : l = ⟨0, Nat.succ_pos n⟩ := Fin.ext (by simpa using hl0)
    subst l
    rw [tupleDialPolynomialSubstitution, if_pos rfl, MvPolynomial.eval_X]
    exact (tupleDialFrozenAssignment_first r t labels a).symm
  · simp [tupleDialPolynomialSubstitution, tupleDialFrozenAssignment,
      tupleDialFrozenFamily, hl0, formalVarDeeperHead]

/-- Evaluation of the tuple polynomial is exactly the existing faithful
frozen-slope evaluation. -/
theorem eval_tupleDialFrozenSlopePoly {n k d : Nat} (r : Nat)
    (theta : Params (n + 1) k d) (labels : DeeperHead → TrichotomyLabel)
    (t : Fin k → Real) (w v : Vec d) (l : Fin (n + 1)) (a : Fin k) :
    MvPolynomial.eval t (tupleDialFrozenSlopePoly r theta labels w v l a) =
      MvPolynomial.eval (tupleDialFrozenAssignment r t labels)
        (formalSlope theta w v l a) := by
  classical
  rw [tupleDialFrozenSlopePoly]
  change MvPolynomial.eval₂Hom (RingHom.id Real) t
      (MvPolynomial.bind₁ (tupleDialPolynomialSubstitution r labels)
        (formalSlope theta w v l a)) = _
  rw [MvPolynomial.eval₂Hom_bind₁]
  apply MvPolynomial.eval₂Hom_congr rfl ?_ rfl
  funext x
  exact eval_tupleDialPolynomialSubstitution r labels t x

/-- Valid deeper-head packaging: `tupleDialFrozenSlopeForm` is evaluation of
the explicit tuple polynomial. -/
theorem tupleDialFrozenSlopeForm_eq_eval_poly
    {n k d : Nat} (r : Nat) (theta : Params (n + 1) k d)
    (labels : DeeperHead → TrichotomyLabel) {q : Nat} (hqpos : 1 ≤ q)
    (hq : q < n + 1) (a : Fin k) (p : MultiSignPoint d k) :
    tupleDialFrozenSlopeForm r theta
        ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead) labels p =
      MvPolynomial.eval p.2
        (tupleDialFrozenSlopePoly r theta labels p.1.1 p.1.2 ⟨q, hq⟩ a) := by
  have hvalid : 2 ≤ (q + 1) ∧ q + 1 ≤ n + 1 ∧
      1 ≤ (a : Nat) + 1 ∧ (a : Nat) + 1 ≤ k :=
    ⟨by omega, by omega, by omega, Nat.succ_le_of_lt a.2⟩
  rw [tupleDialFrozenSlopeForm, dif_pos hvalid]
  exact (eval_tupleDialFrozenSlopePoly r theta labels p.2 p.1.1 p.1.2
    ⟨q, hq⟩ a).symm

/-- Polynomial identity in the tuple variable from vanishing on any nonempty
ambient-open set of dial tuples. -/
theorem tupleDialFrozenSlopePoly_eq_zero_of_vanishOn_open
    {n k d : Nat} (r : Nat) (theta : Params (n + 1) k d)
    (labels : DeeperHead → TrichotomyLabel) (w v : Vec d)
    (l : Fin (n + 1)) (a : Fin k) {U : Set (Fin k → Real)}
    (hU : IsOpen U) (hUne : U.Nonempty)
    (hzero : ∀ t ∈ U,
      MvPolynomial.eval (tupleDialFrozenAssignment r t labels)
        (formalSlope theta w v l a) = 0) :
    tupleDialFrozenSlopePoly r theta labels w v l a = 0 := by
  apply mvPolynomial_eq_zero_of_eval_eqOn_isOpen hU hUne
  intro t ht
  rw [eval_tupleDialFrozenSlopePoly]
  exact hzero t ht

/-! ## NS128: one-head trichotomy assembly -/

/-- Updating a label at the same or a later layer does not change an old
frozen slope: that slope has strict prefix support. -/
theorem tupleDialFrozenSlopeForm_setLabel_eq_of_layer_le
    {n k d : Nat} (r : Nat) (theta : Params (n + 1) k d)
    (labels : DeeperHead → TrichotomyLabel) (label : TrichotomyLabel)
    {old current : DeeperHead}
    (hold : old ∈ deeperHeadOrder (n + 1) k)
    (hle : old.layer ≤ current.layer) :
    tupleDialFrozenSlopeForm r theta old (setLabel labels current label) =
      tupleDialFrozenSlopeForm r theta old labels := by
  have hv := mem_deeperHeadOrder_iff.mp hold
  have hvalid : 2 ≤ old.layer ∧ old.layer ≤ n + 1 ∧
      1 ≤ old.head ∧ old.head ≤ k := hv
  funext p
  rw [tupleDialFrozenSlopeForm, dif_pos hvalid,
    tupleDialFrozenSlopeForm, dif_pos hvalid]
  apply MvPolynomial.eval₂_congr
  intro y mon hymon hcoeff
  have hmem : mon ∈ (formalSlope theta p.1.1 p.1.2
      ⟨old.layer - 1, by omega⟩ ⟨old.head - 1, by omega⟩).support :=
    MvPolynomial.mem_support_iff.mpr hcoeff
  have hlt : y.1.1 < old.layer - 1 := by
    by_contra hnot
    have hzero := formalSlope_supportBefore theta p.1.1 p.1.2
      ⟨old.layer - 1, by omega⟩ ⟨old.head - 1, by omega⟩
      mon hmem y (Nat.le_of_not_gt hnot)
    exact (Finsupp.mem_support_iff.mp hymon) hzero
  have hdne : formalVarDeeperHead y ≠ current := by
    intro heq
    have hlay := congrArg (fun z : DeeperHead => z.layer) heq
    simp only [formalVarDeeperHead] at hlay
    omega
  rcases y with ⟨l, a⟩
  by_cases hl0 : l.1 = 0
  · simp [tupleDialFrozenAssignment, frozenGateAssignment,
      tupleDialFrozenFamily, hl0]
  · simp [tupleDialFrozenAssignment, frozenGateAssignment,
      tupleDialFrozenFamily, hl0, setLabel_of_ne labels label hdne]

/-- An already processed label/sign link survives both region restriction and
the current same/later-layer label update. -/
theorem tupleDialLabelSignLink_restrict_setLabel_old
    {n k d : Nat} {r : Nat} {theta : Params (n + 1) k d}
    {D : MultiDialSignRegion theta}
    {R S : MultiDialRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx : Nat}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    {old : DeeperHead}
    (hold : old ∈ processedPrefix (deeperHeadOrder (n + 1) k) idx)
    (label : TrichotomyLabel) (hSR : S.region ⊆ R.region)
    (hlink : KHead.LabelSignLink (tupleDialPredicates r theta D)
      (tupleDialFormalData r theta) R labels old) :
    KHead.LabelSignLink (tupleDialPredicates r theta D)
      (tupleDialFormalData r theta) S
      (setLabel labels (deeperHeadOrder (n + 1) k)[idx] label) old := by
  have holdOrder : old ∈ deeperHeadOrder (n + 1) k :=
    mem_order_of_mem_processedPrefix hold
  have hle : old.layer ≤ (deeperHeadOrder (n + 1) k)[idx].layer :=
    KHead.layer_le_getElem_of_mem_processedPrefix_deeperHeadOrder hold hidx
  have hnot : (deeperHeadOrder (n + 1) k)[idx] ∉
      processedPrefix (deeperHeadOrder (n + 1) k) idx :=
    getElem_not_mem_processedPrefix_of_nodup
      (KHead.deeperHeadOrder_nodup (n + 1) k) hidx
  have hne : old ≠ (deeperHeadOrder (n + 1) k)[idx] := by
    intro heq
    exact hnot (heq ▸ hold)
  have hform := tupleDialFrozenSlopeForm_setLabel_eq_of_layer_le
    r theta labels label holdOrder hle
  unfold KHead.LabelSignLink at hlink ⊢
  have hlabelOld : setLabel labels (deeperHeadOrder (n + 1) k)[idx] label old =
      labels old := setLabel_of_ne labels label hne
  rw [hlabelOld]
  cases hlabel : labels old with
  | zero =>
      rw [hlabel] at hlink
      simp only [tupleDialPredicates, tupleDialFormalData] at hlink ⊢
      rw [hform]
      intro p hp
      exact hlink p (hSR hp)
  | one =>
      rw [hlabel] at hlink
      simp only [tupleDialPredicates, tupleDialFormalData] at hlink ⊢
      rw [hform]
      intro p hp
      exact hlink p (hSR hp)
  | alpha =>
      rw [hlabel] at hlink
      simp only [tupleDialPredicates, tupleDialFormalData] at hlink ⊢
      rw [hform]
      exact hlink

/-- Assemble the successor abstract processing invariant from one proved branch.
The caller supplies only the new current-head link and successor estimate; all
old links and region facts are preserved here. -/
theorem tupleDialProcessingInvariant_succ
    {n k d : Nat} {r : Nat} {theta : Params (n + 1) k d}
    {D : MultiDialSignRegion theta}
    {baseRegion currentRegion nextRegion : MultiDialRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx : Nat}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (label : TrichotomyLabel)
    (hInv : TupleDialProcessingInvariant r theta D baseRegion currentRegion
      (deeperHeadOrder (n + 1) k) idx labels)
    (hsub : nextRegion.region ⊆ currentRegion.region)
    (hestimate : TupleDialEstimate r theta D (deeperHeadOrder (n + 1) k)
      (idx + 1) nextRegion
      (setLabel labels (deeperHeadOrder (n + 1) k)[idx] label))
    (hcurrent : KHead.LabelSignLink (tupleDialPredicates r theta D)
      (tupleDialFormalData r theta) nextRegion
      (setLabel labels (deeperHeadOrder (n + 1) k)[idx] label)
      (deeperHeadOrder (n + 1) k)[idx]) :
    TupleDialProcessingInvariant r theta D baseRegion nextRegion
      (deeperHeadOrder (n + 1) k) (idx + 1)
      (setLabel labels (deeperHeadOrder (n + 1) k)[idx] label) where
  region_nonempty := nextRegion.nonempty
  region_connected := nextRegion.isPreconnected
  region_relativelyOpen := nextRegion.relativelyOpen
  region_subset_base := hsub.trans hInv.region_subset_base
  label_sign_link := by
    intro old holdSucc
    rcases (KHead.mem_processedPrefix_succ_iff_getElem hidx).mp holdSucc with hold | hnew
    · exact tupleDialLabelSignLink_restrict_setLabel_old hidx hold label hsub
        (hInv.label_sign_link old hold)
    · simpa [hnew] using hcurrent
  estimate := hestimate

/-- Positive branch upgraded from its analytic package to a full successor
processing invariant. -/
theorem exists_positiveTupleDialInvariantStep
    {n k d : Nat} {r : Nat} {theta : Params (n + 1) k d}
    {D : MultiDialSignRegion theta}
    {baseRegion currentRegion : MultiDialRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx q : Nat} {a : Fin k}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (hqpos : 1 ≤ q) (hq : q < n + 1)
    (hcurrent : (deeperHeadOrder (n + 1) k)[idx] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    (hInv : TupleDialProcessingInvariant r theta D baseRegion currentRegion
      (deeperHeadOrder (n + 1) k) idx labels)
    {p : MultiSignPoint d k} (hp : p ∈ currentRegion.region)
    (hpos : 0 < tupleDialFrozenSlopeForm r theta
      (deeperHeadOrder (n + 1) k)[idx] labels p) :
    ∃ nextRegion : MultiDialRestrictedRegion D,
      nextRegion.region ⊆ currentRegion.region ∧
      TupleDialProcessingInvariant r theta D baseRegion nextRegion
        (deeperHeadOrder (n + 1) k) (idx + 1)
        (setLabel labels (deeperHeadOrder (n + 1) k)[idx]
          KHead.TrichotomyLabel.one) := by
  rcases exists_positiveTupleDialBranch hidx hqpos hq hcurrent hInv hp hpos with
    ⟨nextRegion, _hp, hsub, hpositive, _hgate, hestimate⟩
  have horder : (deeperHeadOrder (n + 1) k)[idx] ∈
      deeperHeadOrder (n + 1) k := List.getElem_mem hidx
  have hform := tupleDialFrozenSlopeForm_setLabel_eq_of_layer_le r theta labels
    KHead.TrichotomyLabel.one horder le_rfl
  have hlink : KHead.LabelSignLink (tupleDialPredicates r theta D)
      (tupleDialFormalData r theta) nextRegion
      (setLabel labels (deeperHeadOrder (n + 1) k)[idx]
        KHead.TrichotomyLabel.one)
      (deeperHeadOrder (n + 1) k)[idx] := by
    unfold KHead.LabelSignLink
    rw [setLabel_self]
    simp only [tupleDialPredicates, tupleDialFormalData]
    rw [hform]
    exact hpositive
  exact ⟨nextRegion, hsub,
    tupleDialProcessingInvariant_succ hidx KHead.TrichotomyLabel.one hInv hsub
      hestimate hlink⟩

/-- Negative branch upgraded from its analytic package to a full successor
processing invariant. -/
theorem exists_negativeTupleDialInvariantStep
    {n k d : Nat} {r : Nat} {theta : Params (n + 1) k d}
    {D : MultiDialSignRegion theta}
    {baseRegion currentRegion : MultiDialRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx q : Nat} {a : Fin k}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (hqpos : 1 ≤ q) (hq : q < n + 1)
    (hcurrent : (deeperHeadOrder (n + 1) k)[idx] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    (hInv : TupleDialProcessingInvariant r theta D baseRegion currentRegion
      (deeperHeadOrder (n + 1) k) idx labels)
    {p : MultiSignPoint d k} (hp : p ∈ currentRegion.region)
    (hneg : tupleDialFrozenSlopeForm r theta
      (deeperHeadOrder (n + 1) k)[idx] labels p < 0) :
    ∃ nextRegion : MultiDialRestrictedRegion D,
      nextRegion.region ⊆ currentRegion.region ∧
      TupleDialProcessingInvariant r theta D baseRegion nextRegion
        (deeperHeadOrder (n + 1) k) (idx + 1)
        (setLabel labels (deeperHeadOrder (n + 1) k)[idx]
          KHead.TrichotomyLabel.zero) := by
  rcases exists_negativeTupleDialBranch hidx hqpos hq hcurrent hInv hp hneg with
    ⟨nextRegion, _hp, hsub, hnegative, _hgate, hestimate⟩
  have horder : (deeperHeadOrder (n + 1) k)[idx] ∈
      deeperHeadOrder (n + 1) k := List.getElem_mem hidx
  have hform := tupleDialFrozenSlopeForm_setLabel_eq_of_layer_le r theta labels
    KHead.TrichotomyLabel.zero horder le_rfl
  have hlink : KHead.LabelSignLink (tupleDialPredicates r theta D)
      (tupleDialFormalData r theta) nextRegion
      (setLabel labels (deeperHeadOrder (n + 1) k)[idx]
        KHead.TrichotomyLabel.zero)
      (deeperHeadOrder (n + 1) k)[idx] := by
    unfold KHead.LabelSignLink
    rw [setLabel_self]
    simp only [tupleDialPredicates, tupleDialFormalData]
    rw [hform]
    exact hnegative
  exact ⟨nextRegion, hsub,
    tupleDialProcessingInvariant_succ hidx KHead.TrichotomyLabel.zero hInv hsub
      hestimate hlink⟩

/-- Temporary exact interface filled by NS127: the zero value at the chosen
base point must produce an actual alpha-labeled successor invariant.  It asks
for the branch conclusion rather than assuming it inside the invariant. -/
def TupleDialAlphaStepProvider {n k d : Nat} (r : Nat)
    (theta : Params (n + 1) k d) (D : MultiDialSignRegion theta) : Prop :=
  ∀ (baseRegion currentRegion : MultiDialRestrictedRegion D)
    (labels : DeeperHead → TrichotomyLabel) (idx q : Nat) (a : Fin k),
    (hidx : idx < (deeperHeadOrder (n + 1) k).length) →
    (hqpos : 1 ≤ q) → (hq : q < n + 1) →
    (hcurrent : (deeperHeadOrder (n + 1) k)[idx] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead)) →
    (hInv : TupleDialProcessingInvariant r theta D baseRegion currentRegion
      (deeperHeadOrder (n + 1) k) idx labels) →
    ∀ p ∈ currentRegion.region,
      tupleDialFrozenSlopeForm r theta
        (deeperHeadOrder (n + 1) k)[idx] labels p = 0 →
      ∃ nextRegion : MultiDialRestrictedRegion D,
        nextRegion.region ⊆ currentRegion.region ∧
        TupleDialProcessingInvariant r theta D baseRegion nextRegion
          (deeperHeadOrder (n + 1) k) (idx + 1)
          (setLabel labels (deeperHeadOrder (n + 1) k)[idx]
            KHead.TrichotomyLabel.alpha)

/-- Positive/negative/zero sign split at one current head.  The positive and
negative branches are fully concrete above; the sole parameter is the exact
NS127 alpha-step theorem. -/
theorem exists_tupleDialTrichotomyStep_of_alphaProvider
    {n k d : Nat} {r : Nat} {theta : Params (n + 1) k d}
    {D : MultiDialSignRegion theta}
    (halpha : TupleDialAlphaStepProvider r theta D)
    {baseRegion currentRegion : MultiDialRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx : Nat}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (hInv : TupleDialProcessingInvariant r theta D baseRegion currentRegion
      (deeperHeadOrder (n + 1) k) idx labels) :
    ∃ nextRegion : MultiDialRestrictedRegion D,
      ∃ nextLabels : DeeperHead → TrichotomyLabel,
        nextRegion.region ⊆ currentRegion.region ∧
        TupleDialProcessingInvariant r theta D baseRegion nextRegion
          (deeperHeadOrder (n + 1) k) (idx + 1) nextLabels := by
  rcases KHead.exists_decompose_getElem_deeperHeadOrder hidx with
    ⟨q, a, hqpos, hq, hcurrent⟩
  rcases hInv.region_nonempty with ⟨p, hp⟩
  let phi := tupleDialFrozenSlopeForm r theta
    (deeperHeadOrder (n + 1) k)[idx] labels p
  rcases lt_trichotomy phi 0 with hneg | hzero | hpos
  · rcases exists_negativeTupleDialInvariantStep hidx hqpos hq hcurrent hInv hp hneg with
      ⟨nextRegion, hsub, hnext⟩
    exact ⟨nextRegion,
      setLabel labels (deeperHeadOrder (n + 1) k)[idx] KHead.TrichotomyLabel.zero,
      hsub, hnext⟩
  · rcases halpha baseRegion currentRegion labels idx q a hidx hqpos hq hcurrent
      hInv p hp hzero with ⟨nextRegion, hsub, hnext⟩
    exact ⟨nextRegion,
      setLabel labels (deeperHeadOrder (n + 1) k)[idx] KHead.TrichotomyLabel.alpha,
      hsub, hnext⟩
  · rcases exists_positiveTupleDialInvariantStep hidx hqpos hq hcurrent hInv hp hpos with
      ⟨nextRegion, hsub, hnext⟩
    exact ⟨nextRegion,
      setLabel labels (deeperHeadOrder (n + 1) k)[idx] KHead.TrichotomyLabel.one,
      hsub, hnext⟩

/-! ## NS129: finite trichotomy fold -/

/-- Iterate the concrete one-head step from an arbitrary valid prefix.  The
measure is the number of unprocessed entries, so every recursive call uses the
genuine next entry of `deeperHeadOrder`. -/
theorem exists_tupleDialFiniteFold_of_alphaProvider
    {n k d : Nat} {r : Nat} {theta : Params (n + 1) k d}
    {D : MultiDialSignRegion theta}
    (halpha : TupleDialAlphaStepProvider r theta D)
    {baseRegion currentRegion : MultiDialRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx : Nat}
    (hidxle : idx ≤ (deeperHeadOrder (n + 1) k).length)
    (hInv : TupleDialProcessingInvariant r theta D baseRegion currentRegion
      (deeperHeadOrder (n + 1) k) idx labels) :
    ∃ finalRegion : MultiDialRestrictedRegion D,
      ∃ finalLabels : DeeperHead → TrichotomyLabel,
        finalRegion.region ⊆ currentRegion.region ∧
        TupleDialProcessingInvariant r theta D baseRegion finalRegion
          (deeperHeadOrder (n + 1) k)
          (deeperHeadOrder (n + 1) k).length finalLabels := by
  by_cases hdone : idx = (deeperHeadOrder (n + 1) k).length
  · subst idx
    exact ⟨currentRegion, labels, Set.Subset.rfl, hInv⟩
  · have hidx : idx < (deeperHeadOrder (n + 1) k).length :=
      lt_of_le_of_ne hidxle hdone
    rcases exists_tupleDialTrichotomyStep_of_alphaProvider halpha hidx hInv with
      ⟨nextRegion, nextLabels, hnextSub, hnextInv⟩
    rcases exists_tupleDialFiniteFold_of_alphaProvider halpha
        (idx := idx + 1) (Nat.succ_le_iff.mpr hidx) hnextInv with
      ⟨finalRegion, finalLabels, hfinalSub, hfinalInv⟩
    exact ⟨finalRegion, finalLabels, hfinalSub.trans hnextSub, hfinalInv⟩
termination_by (deeperHeadOrder (n + 1) k).length - idx

/-- Starting from the honest zero-prefix invariant, the finite fold produces
one final restricted region and one global tuple of trichotomy labels. -/
theorem exists_tupleDialFinalInvariant_of_alphaProvider
    {n k d : Nat} {r : Nat} {theta : Params (n + 1) k d}
    (D : MultiDialSignRegion theta)
    (halpha : TupleDialAlphaStepProvider r theta D) :
    ∃ finalRegion : MultiDialRestrictedRegion D,
      ∃ finalLabels : DeeperHead → TrichotomyLabel,
        finalRegion.region ⊆ (MultiDialRestrictedRegion.full D).region ∧
        TupleDialProcessingInvariant r theta D (MultiDialRestrictedRegion.full D) finalRegion
          (deeperHeadOrder (n + 1) k)
          (deeperHeadOrder (n + 1) k).length finalLabels := by
  exact exists_tupleDialFiniteFold_of_alphaProvider halpha (Nat.zero_le _)
    (tupleDialProcessingInvariant_zero r D (fun _ => KHead.TrichotomyLabel.alpha))

/-! ## Paired source/target nonzero branches and conditional capstone -/

/-- Source recursion converges to its source frozen recursion while its input
probe follows the target-network dial path. -/
theorem tendsto_actualProbePoint_pairedTupleDial_to_frozen
    {n k d : Nat} (r : Nat)
    (thetaLive thetaDial : Params (n + 1) k d)
    (p : MultiSignPoint d k) (labels : DeeperHead → TrichotomyLabel) :
    ∀ (q : Nat) (hq : q ≤ n + 1),
      (∀ (l : Fin (n + 1)), l.1 < q → ∀ a : Fin k,
        Tendsto
          (fun tau => pairedTupleDialLiveAssignment r thetaLive thetaDial p tau (l, a))
          atTop (nhds (tupleDialFrozenAssignment r p.2 labels (l, a)))) →
      Tendsto (fun tau => actualProbePoint r thetaLive
          (multiDialPath r thetaDial p tau).1 (multiDialPath r thetaDial p tau).2
          q hq tau)
        atTop (nhds (frozenPoint thetaLive
          (tupleDialFrozenFamily r p.2 labels) p.1.1 p.1.2 q hq)) := by
  intro q
  induction q with
  | zero =>
      intro hq _hgate
      simpa using tendsto_multiDialPath_atTop r thetaDial p
  | succ q ih =>
      intro hq hgate
      let l : Fin (n + 1) := ⟨q, Nat.lt_of_succ_le hq⟩
      have hprev := ih (Nat.le_of_succ_le hq)
        (fun l' hl' a => hgate l' (lt_trans hl' (Nat.lt_succ_self q)) a)
      have hgates : Tendsto
          (fun tau a => pairedTupleDialLiveAssignment r thetaLive thetaDial p tau (l, a))
          atTop (nhds (fun a => tupleDialFrozenAssignment r p.2 labels (l, a))) :=
        tendsto_pi_nhds.mpr (fun a => hgate l (Nat.lt_succ_self q) a)
      have hstep := (continuous_gatedEffectivePoint_data thetaLive l).continuousAt.tendsto.comp
        (hgates.prodMk_nhds hprev)
      simpa [actualProbePoint_succ, frozenPoint_succ, l,
        pairedTupleDialLiveAssignment, actualProbeGateAssignment,
        tupleDialFrozenAssignment, frozenGateAssignment] using hstep

theorem tendsto_prior_pairedTupleGate_of_processingInvariant
    {n k d : Nat} {r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d}
    {D : MultiDialSignRegion thetaDial}
    {baseRegion currentRegion : MultiDialRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx q : Nat} {a : Fin k}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (hcurrent : (deeperHeadOrder (n + 1) k)[idx] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    (hInv : PairedTupleDialProcessingInvariant r thetaLive thetaDial D
      baseRegion currentRegion (deeperHeadOrder (n + 1) k) idx labels)
    (p : MultiSignPoint d k) (hp : p ∈ currentRegion.region)
    (l : Fin (n + 1)) (hl : l.1 < q) (b : Fin k) :
    Tendsto
      (fun tau => pairedTupleDialLiveAssignment r thetaLive thetaDial p tau (l, b))
      atTop (nhds (tupleDialFrozenAssignment r p.2 labels (l, b))) := by
  by_cases hl0 : l.1 = 0
  · have heq : ∀ᶠ tau : Real in atTop,
        pairedTupleDialLiveAssignment r thetaLive thetaDial p tau (l, b) =
          tupleDialFrozenAssignment r p.2 labels (l, b) := by
      filter_upwards [eventually_ge_atTop (1 : Real)] with tau htau
      have htau0 : tau ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one htau)
      have lzero : l = ⟨0, Nat.succ_pos n⟩ := Fin.ext hl0
      subst l
      exact hInv.firstLayer_live_eq_frozen p hp tau htau0 b
    exact Filter.Tendsto.congr' (Filter.EventuallyEq.symm heq) tendsto_const_nhds
  · have hlpos : 1 ≤ l.1 := Nat.one_le_iff_ne_zero.mpr hl0
    have hprocessed : formalVarDeeperHead (l, b) ∈
        processedPrefix (deeperHeadOrder (n + 1) k) idx :=
      KHead.succ_head_mem_processedPrefix_of_layer_lt_getElem_deeperHeadOrder
        hidx hcurrent hlpos l.2 hl b
    exact (hInv.processed_gate_expClose (l, b) hprocessed p hp).tendsto

/-- Current source slope convergence along the target dial. -/
theorem tendsto_currentPairedTupleSlope_of_processingInvariant
    {n k d : Nat} {r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d}
    {D : MultiDialSignRegion thetaDial}
    {baseRegion currentRegion : MultiDialRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx q : Nat} {a : Fin k}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (hqpos : 1 ≤ q) (hq : q < n + 1)
    (hcurrent : (deeperHeadOrder (n + 1) k)[idx] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    (hInv : PairedTupleDialProcessingInvariant r thetaLive thetaDial D
      baseRegion currentRegion (deeperHeadOrder (n + 1) k) idx labels)
    (p : MultiSignPoint d k) (hp : p ∈ currentRegion.region) :
    Tendsto (fun tau => actualProbeSlope r thetaLive
        (multiDialPath r thetaDial p tau).1 (multiDialPath r thetaDial p tau).2 tau
        ⟨q, hq⟩ a) atTop
      (nhds (tupleDialFrozenSlopeForm r thetaLive
        (deeperHeadOrder (n + 1) k)[idx] labels p)) := by
  have hpoint := tendsto_actualProbePoint_pairedTupleDial_to_frozen
    r thetaLive thetaDial p labels q (Nat.le_of_lt hq) (fun l hl b =>
      tendsto_prior_pairedTupleGate_of_processingInvariant
        hidx hcurrent hInv p hp l hl b)
  have hcont : Continuous (fun z : ProbePoint d =>
      matrixBilin (attentionMatrix thetaLive ⟨q, hq⟩ a) z.1 z.2) := by
    unfold matrixBilin KHead.matrixBilin Matrix.mulVec dotProduct
    fun_prop
  have hslope := hcont.continuousAt.tendsto.comp hpoint
  have hvalid : 2 ≤ q + 1 ∧ q + 1 ≤ n + 1 ∧
      1 ≤ (a : Nat) + 1 ∧ (a : Nat) + 1 ≤ k := by
    constructor <;> omega
  have htarget : tupleDialFrozenSlopeForm r thetaLive
      (deeperHeadOrder (n + 1) k)[idx] labels p =
      matrixBilin (attentionMatrix thetaLive ⟨q, hq⟩ a)
        (frozenPoint thetaLive (tupleDialFrozenFamily r p.2 labels)
          p.1.1 p.1.2 q (Nat.le_of_lt hq)).1
        (frozenPoint thetaLive (tupleDialFrozenFamily r p.2 labels)
          p.1.1 p.1.2 q (Nat.le_of_lt hq)).2 := by
    rw [hcurrent, tupleDialFrozenSlopeForm, dif_pos hvalid]
    change MvPolynomial.eval (tupleDialFrozenAssignment r p.2 labels)
        (formalSlope thetaLive p.1.1 p.1.2 ⟨q, by omega⟩ ⟨a.1, by omega⟩) = _
    rw [formalSlope, eval_formalBilin]
    have hfp := eval_formalPoint_frozenGateAssignment thetaLive
      (tupleDialFrozenFamily r p.2 labels) p.1.1 p.1.2 q (Nat.le_of_lt hq)
    change matrixBilin (attentionMatrix thetaLive ⟨q, hq⟩ a)
      (evalFormalVec (frozenGateAssignment (tupleDialFrozenFamily r p.2 labels))
        (formalW thetaLive p.1.1 p.1.2 q (Nat.le_of_lt hq)))
      (evalFormalVec (frozenGateAssignment (tupleDialFrozenFamily r p.2 labels))
        (formalV thetaLive p.1.1 p.1.2 q (Nat.le_of_lt hq))) = _
    rw [show evalFormalVec (frozenGateAssignment (tupleDialFrozenFamily r p.2 labels))
          (formalW thetaLive p.1.1 p.1.2 q (Nat.le_of_lt hq)) =
          (frozenPoint thetaLive (tupleDialFrozenFamily r p.2 labels)
            p.1.1 p.1.2 q (Nat.le_of_lt hq)).1 from hfp.1,
      show evalFormalVec (frozenGateAssignment (tupleDialFrozenFamily r p.2 labels))
          (formalV thetaLive p.1.1 p.1.2 q (Nat.le_of_lt hq)) =
          (frozenPoint thetaLive (tupleDialFrozenFamily r p.2 labels)
            p.1.1 p.1.2 q (Nat.le_of_lt hq)).2 from hfp.2]
  rw [htarget]
  simpa [actualProbeSlope, Function.comp_def] using hslope

theorem currentPairedTupleGate_expClose_one_of_frozen_pos
    {n k d : Nat} {r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d}
    {D : MultiDialSignRegion thetaDial}
    {baseRegion currentRegion : MultiDialRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx q : Nat} {a : Fin k}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (hqpos : 1 ≤ q) (hq : q < n + 1)
    (hcurrent : (deeperHeadOrder (n + 1) k)[idx] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    (hInv : PairedTupleDialProcessingInvariant r thetaLive thetaDial D
      baseRegion currentRegion (deeperHeadOrder (n + 1) k) idx labels)
    (p : MultiSignPoint d k) (hp : p ∈ currentRegion.region)
    (hpos : 0 < tupleDialFrozenSlopeForm r thetaLive
      (deeperHeadOrder (n + 1) k)[idx] labels p) :
    TupleDialExpCloseTo (fun tau => pairedTupleDialLiveAssignment r thetaLive
      thetaDial p tau (⟨q, hq⟩, a)) 1 := by
  have hslope := tendsto_currentPairedTupleSlope_of_processingInvariant
    hidx hqpos hq hcurrent hInv p hp
  have hsat := KHead.expCloseTo_sig_of_tendsto_pos (b := logScale r) hpos hslope
  simpa [TupleDialExpCloseTo, KHead.ExpCloseTo, pairedTupleDialLiveAssignment,
    actualProbeGateAssignment, actualProbeGate_eq_sig] using hsat

theorem currentPairedTupleGate_expClose_zero_of_frozen_neg
    {n k d : Nat} {r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d}
    {D : MultiDialSignRegion thetaDial}
    {baseRegion currentRegion : MultiDialRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx q : Nat} {a : Fin k}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (hqpos : 1 ≤ q) (hq : q < n + 1)
    (hcurrent : (deeperHeadOrder (n + 1) k)[idx] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    (hInv : PairedTupleDialProcessingInvariant r thetaLive thetaDial D
      baseRegion currentRegion (deeperHeadOrder (n + 1) k) idx labels)
    (p : MultiSignPoint d k) (hp : p ∈ currentRegion.region)
    (hneg : tupleDialFrozenSlopeForm r thetaLive
      (deeperHeadOrder (n + 1) k)[idx] labels p < 0) :
    TupleDialExpCloseTo (fun tau => pairedTupleDialLiveAssignment r thetaLive
      thetaDial p tau (⟨q, hq⟩, a)) 0 := by
  have hslope := tendsto_currentPairedTupleSlope_of_processingInvariant
    hidx hqpos hq hcurrent hInv p hp
  have hsat := KHead.expCloseTo_sig_of_tendsto_neg (b := logScale r) hneg hslope
  simpa [TupleDialExpCloseTo, KHead.ExpCloseTo, pairedTupleDialLiveAssignment,
    actualProbeGateAssignment, actualProbeGate_eq_sig] using hsat

/-- Restrict a target-dial chart by a sign condition on a source frozen slope. -/
theorem exists_pairedTupleDialRestriction_of_sign
    {n k d : Nat} {r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d}
    {D : MultiDialSignRegion thetaDial} (R : MultiDialRestrictedRegion D)
    (labels : DeeperHead → TrichotomyLabel) {idx q : Nat} {a : Fin k}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (hqpos : 1 ≤ q) (hq : q < n + 1)
    (hcurrent : (deeperHeadOrder (n + 1) k)[idx] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    (positive : Bool) {p : MultiSignPoint d k} (hp : p ∈ R.region)
    (hsign : if positive then 0 < tupleDialFrozenSlopeForm r thetaLive
        (deeperHeadOrder (n + 1) k)[idx] labels p
      else tupleDialFrozenSlopeForm r thetaLive
        (deeperHeadOrder (n + 1) k)[idx] labels p < 0) :
    ∃ R' : MultiDialRestrictedRegion D,
      p ∈ R'.region ∧ R'.region ⊆ R.region ∧
      ∀ x ∈ R'.region,
        if positive then 0 < tupleDialFrozenSlopeForm r thetaLive
            (deeperHeadOrder (n + 1) k)[idx] labels x
        else tupleDialFrozenSlopeForm r thetaLive
            (deeperHeadOrder (n + 1) k)[idx] labels x < 0 := by
  let phi := tupleDialFrozenSlopeForm r thetaLive
    (deeperHeadOrder (n + 1) k)[idx] labels
  let O : Set (MultiSignPoint d k) :=
    if positive then {x | 0 < phi x} else {x | phi x < 0}
  have hphi : Continuous phi :=
    continuous_currentTupleFrozenSlope r thetaLive labels hidx hqpos hq hcurrent
  have hO : IsOpen O := by
    cases positive <;> simp only [O, Bool.false_eq_true, if_false, if_true]
    · exact isOpen_Iio.preimage hphi
    · exact isOpen_Ioi.preimage hphi
  have hpO : p ∈ O := by cases positive <;> simpa [O] using hsign
  rcases R.exists_restrict_ambientOpen hO hp hpO with ⟨R', hpR', hsub⟩
  refine ⟨R', hpR', fun x hx => (hsub hx).1, ?_⟩
  intro x hx
  have hxO := (hsub hx).2
  cases positive <;> simpa [O] using hxO

/-- Extend the paired estimate by one freshly proved current-gate estimate. -/
theorem PairedTupleDialEstimate.extend_current
    {n k d : Nat} {r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d}
    {D : MultiDialSignRegion thetaDial}
    {R S : MultiDialRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx q : Nat} {a : Fin k}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (hqpos : 1 ≤ q) (hq : q < n + 1)
    (hcurrent : (deeperHeadOrder (n + 1) k)[idx] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    (label : TrichotomyLabel) (hSR : S.region ⊆ R.region)
    (hEst : PairedTupleDialEstimate r thetaLive thetaDial D
      (deeperHeadOrder (n + 1) k) idx R labels)
    (hgate : ∀ p ∈ S.region, TupleDialExpCloseTo
      (fun tau => pairedTupleDialLiveAssignment r thetaLive thetaDial p tau
        (⟨q, hq⟩, a)) (trichotomyLabelValue r label)) :
    PairedTupleDialEstimate r thetaLive thetaDial D
      (deeperHeadOrder (n + 1) k) (idx + 1) S
      (setLabel labels (deeperHeadOrder (n + 1) k)[idx] label) where
  firstLayer_live_eq_frozen := by
    intro p hp tau htau b
    simpa [tupleDialFrozenAssignment_first] using
      hEst.firstLayer_live_eq_frozen p (hSR hp) tau htau b
  processed_gate_expClose := by
    intro x hx p hp
    rcases (KHead.mem_processedPrefix_succ_iff_getElem hidx).mp hx with hold | hnew
    · have hnot : (deeperHeadOrder (n + 1) k)[idx] ∉
          processedPrefix (deeperHeadOrder (n + 1) k) idx :=
        getElem_not_mem_processedPrefix_of_nodup
          (KHead.deeperHeadOrder_nodup (n + 1) k) hidx
      have hne : formalVarDeeperHead x ≠ (deeperHeadOrder (n + 1) k)[idx] := by
        intro heq
        exact hnot (heq ▸ hold)
      have holdEst := hEst.processed_gate_expClose x hold p (hSR hp)
      have htarget : tupleDialFrozenAssignment r p.2
          (setLabel labels (deeperHeadOrder (n + 1) k)[idx] label) x =
          tupleDialFrozenAssignment r p.2 labels x := by
        rcases x with ⟨l, b⟩
        by_cases hl0 : l.1 = 0
        · simp [tupleDialFrozenAssignment, tupleDialFrozenFamily, hl0]
        · simp [tupleDialFrozenAssignment, tupleDialFrozenFamily, hl0,
            setLabel_of_ne labels label hne]
      rw [htarget]
      exact holdEst
    · have hdh : formalVarDeeperHead x =
          ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead) := by
        rw [hnew, hcurrent]
      have hx : x = (⟨q, hq⟩, a) := by
        rcases x with ⟨l, b⟩
        apply Prod.ext
        · apply Fin.ext
          simpa [formalVarDeeperHead] using
            congrArg (fun z : DeeperHead => z.layer) hdh
        · apply Fin.ext
          simpa [formalVarDeeperHead] using
            congrArg (fun z : DeeperHead => z.head) hdh
      subst x
      simpa [tupleDialFrozenAssignment, tupleDialFrozenFamily,
        Nat.ne_of_gt hqpos, formalVarDeeperHead, hcurrent, setLabel_self] using
        hgate p hp
  compact_uniform_motion := by
    intro K hK hKS
    exact S.exists_uniform_motion_bound r hK hKS

theorem exists_positivePairedTupleDialBranch
    {n k d : Nat} {r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d}
    {D : MultiDialSignRegion thetaDial}
    {baseRegion currentRegion : MultiDialRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx q : Nat} {a : Fin k}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (hqpos : 1 ≤ q) (hq : q < n + 1)
    (hcurrent : (deeperHeadOrder (n + 1) k)[idx] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    (hInv : PairedTupleDialProcessingInvariant r thetaLive thetaDial D
      baseRegion currentRegion (deeperHeadOrder (n + 1) k) idx labels)
    {p : MultiSignPoint d k} (hp : p ∈ currentRegion.region)
    (hpos : 0 < tupleDialFrozenSlopeForm r thetaLive
      (deeperHeadOrder (n + 1) k)[idx] labels p) :
    ∃ nextRegion : MultiDialRestrictedRegion D,
      nextRegion.region ⊆ currentRegion.region ∧
      (∀ x ∈ nextRegion.region, 0 < tupleDialFrozenSlopeForm r thetaLive
        (deeperHeadOrder (n + 1) k)[idx] labels x) ∧
      PairedTupleDialEstimate r thetaLive thetaDial D
        (deeperHeadOrder (n + 1) k) (idx + 1) nextRegion
        (setLabel labels (deeperHeadOrder (n + 1) k)[idx]
          KHead.TrichotomyLabel.one) := by
  rcases exists_pairedTupleDialRestriction_of_sign currentRegion labels hidx hqpos hq
      hcurrent true hp (by simpa using hpos) with
    ⟨nextRegion, _hpnext, hsub, hpositive⟩
  have hgate : ∀ x ∈ nextRegion.region, TupleDialExpCloseTo
      (fun tau => pairedTupleDialLiveAssignment r thetaLive thetaDial x tau
        (⟨q, hq⟩, a)) (trichotomyLabelValue r KHead.TrichotomyLabel.one) := by
    intro x hx
    simpa using currentPairedTupleGate_expClose_one_of_frozen_pos
      hidx hqpos hq hcurrent hInv x (hsub hx) (by simpa using hpositive x hx)
  exact ⟨nextRegion, hsub, (by simpa using hpositive),
    hInv.estimate.extend_current hidx hqpos hq hcurrent
      KHead.TrichotomyLabel.one hsub hgate⟩

theorem exists_negativePairedTupleDialBranch
    {n k d : Nat} {r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d}
    {D : MultiDialSignRegion thetaDial}
    {baseRegion currentRegion : MultiDialRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx q : Nat} {a : Fin k}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (hqpos : 1 ≤ q) (hq : q < n + 1)
    (hcurrent : (deeperHeadOrder (n + 1) k)[idx] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    (hInv : PairedTupleDialProcessingInvariant r thetaLive thetaDial D
      baseRegion currentRegion (deeperHeadOrder (n + 1) k) idx labels)
    {p : MultiSignPoint d k} (hp : p ∈ currentRegion.region)
    (hneg : tupleDialFrozenSlopeForm r thetaLive
      (deeperHeadOrder (n + 1) k)[idx] labels p < 0) :
    ∃ nextRegion : MultiDialRestrictedRegion D,
      nextRegion.region ⊆ currentRegion.region ∧
      (∀ x ∈ nextRegion.region, tupleDialFrozenSlopeForm r thetaLive
        (deeperHeadOrder (n + 1) k)[idx] labels x < 0) ∧
      PairedTupleDialEstimate r thetaLive thetaDial D
        (deeperHeadOrder (n + 1) k) (idx + 1) nextRegion
        (setLabel labels (deeperHeadOrder (n + 1) k)[idx]
          KHead.TrichotomyLabel.zero) := by
  rcases exists_pairedTupleDialRestriction_of_sign currentRegion labels hidx hqpos hq
      hcurrent false hp (by simpa using hneg) with
    ⟨nextRegion, _hpnext, hsub, hnegative⟩
  have hgate : ∀ x ∈ nextRegion.region, TupleDialExpCloseTo
      (fun tau => pairedTupleDialLiveAssignment r thetaLive thetaDial x tau
        (⟨q, hq⟩, a)) (trichotomyLabelValue r KHead.TrichotomyLabel.zero) := by
    intro x hx
    simpa using currentPairedTupleGate_expClose_zero_of_frozen_neg
      hidx hqpos hq hcurrent hInv x (hsub hx) (by simpa using hnegative x hx)
  exact ⟨nextRegion, hsub, (by simpa using hnegative),
    hInv.estimate.extend_current hidx hqpos hq hcurrent
      KHead.TrichotomyLabel.zero hsub hgate⟩

theorem pairedTupleDialLabelSignLink_restrict_setLabel_old
    {n k d : Nat} {r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d}
    {D : MultiDialSignRegion thetaDial} {R S : MultiDialRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx : Nat} {old : DeeperHead}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (hold : old ∈ processedPrefix (deeperHeadOrder (n + 1) k) idx)
    (label : TrichotomyLabel) (hSR : S.region ⊆ R.region)
    (hlink : KHead.LabelSignLink
      (pairedTupleDialPredicates r thetaLive thetaDial D)
      (tupleDialFormalData r thetaLive) R labels old) :
    KHead.LabelSignLink (pairedTupleDialPredicates r thetaLive thetaDial D)
      (tupleDialFormalData r thetaLive) S
      (setLabel labels (deeperHeadOrder (n + 1) k)[idx] label) old := by
  have hnot : (deeperHeadOrder (n + 1) k)[idx] ∉
      processedPrefix (deeperHeadOrder (n + 1) k) idx :=
    getElem_not_mem_processedPrefix_of_nodup
      (KHead.deeperHeadOrder_nodup (n + 1) k) hidx
  have hne : old ≠ (deeperHeadOrder (n + 1) k)[idx] := fun heq => hnot (heq ▸ hold)
  have horder : old ∈ deeperHeadOrder (n + 1) k :=
    List.mem_of_mem_take hold
  have hlayer : old.layer ≤ (deeperHeadOrder (n + 1) k)[idx].layer :=
    KHead.layer_le_getElem_of_mem_processedPrefix_deeperHeadOrder hold hidx
  have hform := tupleDialFrozenSlopeForm_setLabel_eq_of_layer_le
    r thetaLive labels label horder hlayer
  unfold KHead.LabelSignLink at hlink ⊢
  have hlabelOld :
      setLabel labels (deeperHeadOrder (n + 1) k)[idx] label old = labels old :=
    setLabel_of_ne labels label hne
  rw [hlabelOld]
  cases hlabel : labels old with
  | zero =>
      rw [hlabel] at hlink
      simp only [pairedTupleDialPredicates, tupleDialFormalData] at hlink ⊢
      rw [hform]
      exact fun p hp => hlink p (hSR hp)
  | one =>
      rw [hlabel] at hlink
      simp only [pairedTupleDialPredicates, tupleDialFormalData] at hlink ⊢
      rw [hform]
      exact fun p hp => hlink p (hSR hp)
  | alpha =>
      rw [hlabel] at hlink
      simp only [pairedTupleDialPredicates, tupleDialFormalData] at hlink ⊢
      rw [hform]
      exact hlink

theorem pairedTupleDialProcessingInvariant_succ
    {n k d : Nat} {r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d}
    {D : MultiDialSignRegion thetaDial}
    {baseRegion currentRegion nextRegion : MultiDialRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx : Nat}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (label : TrichotomyLabel)
    (hInv : PairedTupleDialProcessingInvariant r thetaLive thetaDial D
      baseRegion currentRegion (deeperHeadOrder (n + 1) k) idx labels)
    (hsub : nextRegion.region ⊆ currentRegion.region)
    (hestimate : PairedTupleDialEstimate r thetaLive thetaDial D
      (deeperHeadOrder (n + 1) k) (idx + 1) nextRegion
      (setLabel labels (deeperHeadOrder (n + 1) k)[idx] label))
    (hcurrent : KHead.LabelSignLink
      (pairedTupleDialPredicates r thetaLive thetaDial D)
      (tupleDialFormalData r thetaLive) nextRegion
      (setLabel labels (deeperHeadOrder (n + 1) k)[idx] label)
      (deeperHeadOrder (n + 1) k)[idx]) :
    PairedTupleDialProcessingInvariant r thetaLive thetaDial D
      baseRegion nextRegion (deeperHeadOrder (n + 1) k) (idx + 1)
      (setLabel labels (deeperHeadOrder (n + 1) k)[idx] label) where
  region_nonempty := nextRegion.nonempty
  region_connected := nextRegion.isPreconnected
  region_relativelyOpen := nextRegion.relativelyOpen
  region_subset_base := hsub.trans hInv.region_subset_base
  label_sign_link := by
    intro old holdSucc
    rcases (KHead.mem_processedPrefix_succ_iff_getElem hidx).mp holdSucc with hold | hnew
    · exact pairedTupleDialLabelSignLink_restrict_setLabel_old
        hidx hold label hsub (hInv.label_sign_link old hold)
    · simpa [hnew] using hcurrent
  estimate := hestimate

theorem exists_positivePairedTupleDialInvariantStep
    {n k d : Nat} {r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d}
    {D : MultiDialSignRegion thetaDial}
    {baseRegion currentRegion : MultiDialRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx q : Nat} {a : Fin k}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (hqpos : 1 ≤ q) (hq : q < n + 1)
    (hcurrent : (deeperHeadOrder (n + 1) k)[idx] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    (hInv : PairedTupleDialProcessingInvariant r thetaLive thetaDial D
      baseRegion currentRegion (deeperHeadOrder (n + 1) k) idx labels)
    {p : MultiSignPoint d k} (hp : p ∈ currentRegion.region)
    (hpos : 0 < tupleDialFrozenSlopeForm r thetaLive
      (deeperHeadOrder (n + 1) k)[idx] labels p) :
    ∃ nextRegion : MultiDialRestrictedRegion D,
      nextRegion.region ⊆ currentRegion.region ∧
      PairedTupleDialProcessingInvariant r thetaLive thetaDial D
        baseRegion nextRegion (deeperHeadOrder (n + 1) k) (idx + 1)
        (setLabel labels (deeperHeadOrder (n + 1) k)[idx]
          KHead.TrichotomyLabel.one) := by
  rcases exists_positivePairedTupleDialBranch hidx hqpos hq hcurrent hInv hp hpos with
    ⟨nextRegion, hsub, hpositive, hestimate⟩
  have horder : (deeperHeadOrder (n + 1) k)[idx] ∈
      deeperHeadOrder (n + 1) k := List.getElem_mem hidx
  have hform := tupleDialFrozenSlopeForm_setLabel_eq_of_layer_le
    r thetaLive labels KHead.TrichotomyLabel.one horder le_rfl
  have hlink : KHead.LabelSignLink
      (pairedTupleDialPredicates r thetaLive thetaDial D)
      (tupleDialFormalData r thetaLive) nextRegion
      (setLabel labels (deeperHeadOrder (n + 1) k)[idx]
        KHead.TrichotomyLabel.one)
      (deeperHeadOrder (n + 1) k)[idx] := by
    unfold KHead.LabelSignLink
    rw [setLabel_self]
    simp only [pairedTupleDialPredicates, tupleDialFormalData]
    rw [hform]
    exact hpositive
  exact ⟨nextRegion, hsub, pairedTupleDialProcessingInvariant_succ
    hidx KHead.TrichotomyLabel.one hInv hsub hestimate hlink⟩

theorem exists_negativePairedTupleDialInvariantStep
    {n k d : Nat} {r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d}
    {D : MultiDialSignRegion thetaDial}
    {baseRegion currentRegion : MultiDialRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx q : Nat} {a : Fin k}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (hqpos : 1 ≤ q) (hq : q < n + 1)
    (hcurrent : (deeperHeadOrder (n + 1) k)[idx] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead))
    (hInv : PairedTupleDialProcessingInvariant r thetaLive thetaDial D
      baseRegion currentRegion (deeperHeadOrder (n + 1) k) idx labels)
    {p : MultiSignPoint d k} (hp : p ∈ currentRegion.region)
    (hneg : tupleDialFrozenSlopeForm r thetaLive
      (deeperHeadOrder (n + 1) k)[idx] labels p < 0) :
    ∃ nextRegion : MultiDialRestrictedRegion D,
      nextRegion.region ⊆ currentRegion.region ∧
      PairedTupleDialProcessingInvariant r thetaLive thetaDial D
        baseRegion nextRegion (deeperHeadOrder (n + 1) k) (idx + 1)
        (setLabel labels (deeperHeadOrder (n + 1) k)[idx]
          KHead.TrichotomyLabel.zero) := by
  rcases exists_negativePairedTupleDialBranch hidx hqpos hq hcurrent hInv hp hneg with
    ⟨nextRegion, hsub, hnegative, hestimate⟩
  have horder : (deeperHeadOrder (n + 1) k)[idx] ∈
      deeperHeadOrder (n + 1) k := List.getElem_mem hidx
  have hform := tupleDialFrozenSlopeForm_setLabel_eq_of_layer_le
    r thetaLive labels KHead.TrichotomyLabel.zero horder le_rfl
  have hlink : KHead.LabelSignLink
      (pairedTupleDialPredicates r thetaLive thetaDial D)
      (tupleDialFormalData r thetaLive) nextRegion
      (setLabel labels (deeperHeadOrder (n + 1) k)[idx]
        KHead.TrichotomyLabel.zero)
      (deeperHeadOrder (n + 1) k)[idx] := by
    unfold KHead.LabelSignLink
    rw [setLabel_self]
    simp only [pairedTupleDialPredicates, tupleDialFormalData]
    rw [hform]
    exact hnegative
  exact ⟨nextRegion, hsub, pairedTupleDialProcessingInvariant_succ
    hidx KHead.TrichotomyLabel.zero hInv hsub hestimate hlink⟩

/-- The single remaining analytic input to the paired trichotomy: a zero
source frozen slope on the target chart produces the alpha successor. -/
def PairedTupleDialAlphaStepProvider {n k d : Nat} (r : Nat)
    (thetaLive thetaDial : Params (n + 1) k d)
    (D : MultiDialSignRegion thetaDial) : Prop :=
  ∀ (baseRegion currentRegion : MultiDialRestrictedRegion D)
    (labels : DeeperHead → TrichotomyLabel) (idx q : Nat) (a : Fin k),
    (hidx : idx < (deeperHeadOrder (n + 1) k).length) →
    (hqpos : 1 ≤ q) → (hq : q < n + 1) →
    (hcurrent : (deeperHeadOrder (n + 1) k)[idx] =
      ({ layer := q + 1, head := (a : Nat) + 1 } : DeeperHead)) →
    (hInv : PairedTupleDialProcessingInvariant r thetaLive thetaDial D
      baseRegion currentRegion (deeperHeadOrder (n + 1) k) idx labels) →
    ∀ p ∈ currentRegion.region,
      tupleDialFrozenSlopeForm r thetaLive
        (deeperHeadOrder (n + 1) k)[idx] labels p = 0 →
      ∃ nextRegion : MultiDialRestrictedRegion D,
        nextRegion.region ⊆ currentRegion.region ∧
        PairedTupleDialProcessingInvariant r thetaLive thetaDial D
          baseRegion nextRegion (deeperHeadOrder (n + 1) k) (idx + 1)
          (setLabel labels (deeperHeadOrder (n + 1) k)[idx]
            KHead.TrichotomyLabel.alpha)

/-- Honest paired one-head trichotomy, conditional only on the explicit alpha
provider above. -/
theorem exists_pairedTupleDialTrichotomyStep_of_alphaProvider
    {n k d : Nat} {r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d}
    {D : MultiDialSignRegion thetaDial}
    (halpha : PairedTupleDialAlphaStepProvider r thetaLive thetaDial D)
    {baseRegion currentRegion : MultiDialRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx : Nat}
    (hidx : idx < (deeperHeadOrder (n + 1) k).length)
    (hInv : PairedTupleDialProcessingInvariant r thetaLive thetaDial D
      baseRegion currentRegion (deeperHeadOrder (n + 1) k) idx labels) :
    ∃ nextRegion : MultiDialRestrictedRegion D,
      ∃ nextLabels : DeeperHead → TrichotomyLabel,
        nextRegion.region ⊆ currentRegion.region ∧
        PairedTupleDialProcessingInvariant r thetaLive thetaDial D
          baseRegion nextRegion (deeperHeadOrder (n + 1) k) (idx + 1)
          nextLabels := by
  rcases KHead.exists_decompose_getElem_deeperHeadOrder hidx with
    ⟨q, a, hqpos, hq, hcurrent⟩
  rcases hInv.region_nonempty with ⟨p, hp⟩
  let phi := tupleDialFrozenSlopeForm r thetaLive
    (deeperHeadOrder (n + 1) k)[idx] labels p
  rcases lt_trichotomy phi 0 with hneg | hzero | hpos
  · rcases exists_negativePairedTupleDialInvariantStep
      hidx hqpos hq hcurrent hInv hp hneg with ⟨nextRegion, hsub, hnext⟩
    exact ⟨nextRegion, setLabel labels (deeperHeadOrder (n + 1) k)[idx]
      KHead.TrichotomyLabel.zero, hsub, hnext⟩
  · rcases halpha baseRegion currentRegion labels idx q a hidx hqpos hq hcurrent
      hInv p hp hzero with ⟨nextRegion, hsub, hnext⟩
    exact ⟨nextRegion, setLabel labels (deeperHeadOrder (n + 1) k)[idx]
      KHead.TrichotomyLabel.alpha, hsub, hnext⟩
  · rcases exists_positivePairedTupleDialInvariantStep
      hidx hqpos hq hcurrent hInv hp hpos with ⟨nextRegion, hsub, hnext⟩
    exact ⟨nextRegion, setLabel labels (deeperHeadOrder (n + 1) k)[idx]
      KHead.TrichotomyLabel.one, hsub, hnext⟩

theorem exists_pairedTupleDialFiniteFold_of_alphaProvider
    {n k d : Nat} {r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d}
    {D : MultiDialSignRegion thetaDial}
    (halpha : PairedTupleDialAlphaStepProvider r thetaLive thetaDial D)
    {baseRegion currentRegion : MultiDialRestrictedRegion D}
    {labels : DeeperHead → TrichotomyLabel} {idx : Nat}
    (hidxle : idx ≤ (deeperHeadOrder (n + 1) k).length)
    (hInv : PairedTupleDialProcessingInvariant r thetaLive thetaDial D
      baseRegion currentRegion (deeperHeadOrder (n + 1) k) idx labels) :
    ∃ finalRegion : MultiDialRestrictedRegion D,
      ∃ finalLabels : DeeperHead → TrichotomyLabel,
        finalRegion.region ⊆ currentRegion.region ∧
        PairedTupleDialProcessingInvariant r thetaLive thetaDial D
          baseRegion finalRegion (deeperHeadOrder (n + 1) k)
          (deeperHeadOrder (n + 1) k).length finalLabels := by
  by_cases hdone : idx = (deeperHeadOrder (n + 1) k).length
  · subst idx
    exact ⟨currentRegion, labels, Set.Subset.rfl, hInv⟩
  · have hidx : idx < (deeperHeadOrder (n + 1) k).length :=
      lt_of_le_of_ne hidxle hdone
    rcases exists_pairedTupleDialTrichotomyStep_of_alphaProvider halpha hidx hInv with
      ⟨nextRegion, nextLabels, hnextSub, hnextInv⟩
    rcases exists_pairedTupleDialFiniteFold_of_alphaProvider halpha
        (idx := idx + 1) (Nat.succ_le_iff.mpr hidx) hnextInv with
      ⟨finalRegion, finalLabels, hfinalSub, hfinalInv⟩
    exact ⟨finalRegion, finalLabels, hfinalSub.trans hnextSub, hfinalInv⟩
termination_by (deeperHeadOrder (n + 1) k).length - idx

/-- Conditional paired capstone.  Apart from the Step-1 first-attention
equality, its sole analytic premise is `PairedTupleDialAlphaStepProvider`. -/
theorem prop_pairedTupleDialTrichotomy_of_alphaProvider
    {n k d : Nat} {r : Nat}
    {thetaLive thetaDial : Params (n + 1) k d}
    (D : MultiDialSignRegion thetaDial)
    (hA : ∀ a, attentionMatrix thetaLive 0 a = attentionMatrix thetaDial 0 a)
    (halpha : PairedTupleDialAlphaStepProvider r thetaLive thetaDial D) :
    KHead.prop_trichotomy_S (pairedTupleDialPredicates r thetaLive thetaDial D)
      (tupleDialFormalData r thetaLive) (MultiDialRestrictedRegion.full D)
      (deeperHeadOrder (n + 1) k) := by
  have hinit := pairedTupleDialProcessingInvariant_zero r D hA
    (fun _ => KHead.TrichotomyLabel.alpha)
  rcases exists_pairedTupleDialFiniteFold_of_alphaProvider halpha
      (Nat.zero_le _) hinit with ⟨Ustar, labels, _hsub, hfinal⟩
  refine ⟨?_, trivial⟩
  exact
    { Ustar := Ustar
      labels := labels
      region_nonempty := hfinal.region_nonempty
      region_connected := hfinal.region_connected
      region_relativelyOpen := hfinal.region_relativelyOpen
      region_subset_base := hfinal.region_subset_base
      label_sign_link := by
        intro h hh
        exact hfinal.label_sign_link h (by simpa [KHead.processedPrefix] using hh)
      estimate := hfinal.estimate }

end

end TransformerIdentifiability.NLayer.NoSkip
