import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Step1.SelectedTowers
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Analytic.PoleArcs

set_option autoImplicit false

open Filter Matrix

namespace TransformerIdentifiability.NLayer.NoSkip

/-!
# No-skip Step 1 tier transition (`tra:cascade` ignition core)

This file ports the *tier-transition* core of the KHead `Step1/TierCascade.lean`
cluster to the no-skip active-stratification API.  Under the no-skip dictionary
(`C_ℓ := Σ_a V_{ℓa}`, `collapseMatrix theta l = valueSum theta l`) the cascade
arguments treat the layer constant `C_ℓ` as opaque; nothing below expands it via
a skip cancellation identity.

The load-bearing statement (`tra:cascade`, one processed tier ignites the next)
is: at a *selected level pole* `τ` of the currently processed tier `j` — the
selected level `D.level (j, headAt j)` hits `Π` at `τ` — the selected **gate**
`csig (D.level (j, headAt j))` acquires an exact positive-order Laurent pole with
nonzero coefficient and a full selected pole arc.  That gate is exactly the
driver that ignites the level machinery of tier `j+1`.

Dominance enters purely as hypotheses (`step1TowerDominance`, over the NS100
`DominanceTowerData`): from strict per-stage threshold domination we recover the
non-strict `SatisfiesTowerThresholds` interface and the selected-tower
nonvanishing capstone.  This matches the KHead
`step1TowerDominance`/`_satisfiesThresholds`/`_eval_ne_zero` cluster, phrased
directly over a single tower rather than the (not-yet-ported) finite dominance
family.
-/

noncomputable section

variable {n k d r : Nat}

/-! ## Regularity supplies active heads -/

/-- Under target regularity every head is active at every layer.  This is the
no-skip analogue of the KHead `allHeadsActive_of_regular`; the selected-chain
heads consumed by the ignition step are therefore always active. -/
theorem step1_head_active {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (l : Fin (n + 2)) (a : Fin k) :
    a ∈ activeHeads theta' l :=
  (mem_activeHeads_iff_valueMatrix_ne_zero theta' l a).2
    (H.targetRegularity.value_ne_zero l a)

/-! ## Selected level poles and selected-only collisions -/

/-- The selected level hits `Π` at `τ`: a selected level pole of tier `j`. -/
def step1SelectedLevelPole {k d : Nat}
    (D : ActiveStratificationData (n + 2) k d) (C : Step1SelectedChain n k)
    (j : Step1TierIndex n) (τ : ℂ) : Prop :=
  D.level (C.selectedVar j) τ ∈ Pi

/-- True selected-only collision semantics: the selected level hits `Π` and
every sibling head in the same tier avoids `Π` at `τ`. -/
def step1SelectedOnlyCollision {k d : Nat}
    (D : ActiveStratificationData (n + 2) k d) (C : Step1SelectedChain n k)
    (j : Step1TierIndex n) (τ : ℂ) : Prop :=
  D.level (C.selectedVar j) τ ∈ Pi ∧
    ∀ c : Fin k, c ≠ C.headAt j → D.level (j, c) τ ∉ Pi

/-- A selected-only collision is in particular a selected level pole. -/
theorem step1SelectedOnlyCollision.selectedLevelPole {k d : Nat}
    {D : ActiveStratificationData (n + 2) k d} {C : Step1SelectedChain n k}
    {j : Step1TierIndex n} {τ : ℂ}
    (hcollision : step1SelectedOnlyCollision D C j τ) :
    step1SelectedLevelPole D C j τ :=
  hcollision.1

/-- A selected-only collision at a domain point lands in the active reduced
stratum of the currently processed tier.  No-skip analogue of the KHead
`step1SelectedOnlyCollision_mem_activeStratum`. -/
theorem step1SelectedOnlyCollision_mem_activeStratum {k d : Nat}
    {theta' : Params (n + 2) k d} {D : ActiveStratificationData (n + 2) k d}
    (hD : ActiveHeadSingularStratification (r := r) theta' D)
    {C : Step1SelectedChain n k} {j : Step1TierIndex n}
    (hactive : C.headAt j ∈ activeHeads theta' j)
    {τ : ℂ} (hτΩ : τ ∈ D.Omega j.1)
    (hcollision : step1SelectedOnlyCollision D C j τ) :
    τ ∈ D.stratum j.1 :=
  (mem_activeStratum_iff hD j τ).2
    ⟨C.headAt j, hactive, hτΩ, hcollision.1⟩

/-- A selected collision is excluded from the immediately following recursive
domain.  This small fact prevents an unsound same-point tier fold: adjacent
tier propagation must use a punctured neighbourhood and select a *new* point. -/
theorem step1SelectedLevelPole_not_mem_nextOmega {k d : Nat}
    {theta' : Params (n + 2) k d} {D : ActiveStratificationData (n + 2) k d}
    (hD : ActiveHeadSingularStratification (r := r) theta' D)
    (C : Step1SelectedChain n k) (j : Step1LaterTierIndex n)
    (hactive : C.headAt ⟨j.1, by omega⟩ ∈ activeHeads theta' ⟨j.1, by omega⟩)
    {τ : ℂ} (hτΩ : τ ∈ D.Omega j.1)
    (hpole : step1SelectedLevelPole D C ⟨j.1, by omega⟩ τ) :
    τ ∉ D.Omega (j.1 + 1) := by
  let l : Fin (n + 2) := ⟨j.1, by omega⟩
  have hstratum : τ ∈ D.stratum l.1 :=
    (mem_activeStratum_iff hD l τ).2 ⟨C.headAt l, hactive, hτΩ, hpole⟩
  rw [hD.omega_succ l]
  exact fun hmem => hmem.2 hstratum

/-! ## Successor selected level pole (the ignition payload) -/

/-- Pole-oriented successor selected-level payload for the concrete no-skip
cascade.  At the currently processed tier point `τ`, the selected gate is
meromorphic, is not analytic, and carries the local arc package producing
arbitrarily close `Π`-preimages.  This is the no-skip analogue of the KHead
`step1SuccessorSelectedLevelPole`, phrased on the ignition gate
`csig (selected level)` (the object for which the no-skip analytic tree supplies
a positive-order Laurent normal form and a selected arc). -/
def step1SuccessorSelectedLevelPole {k d : Nat}
    (D : ActiveStratificationData (n + 2) k d) (C : Step1SelectedChain n k)
    (j : Step1TierIndex n) (τ : ℂ) : Prop :=
  MeromorphicAt (step1SelectedGateFunction D C j) τ ∧
    ¬ AnalyticAt ℂ (step1SelectedGateFunction D C j) τ ∧
      ∃ q : Nat, ArcStructureResult (step1SelectedGateFunction D C j) τ q

theorem step1SuccessorSelectedLevelPole.meromorphicAt {k d : Nat}
    {D : ActiveStratificationData (n + 2) k d} {C : Step1SelectedChain n k}
    {j : Step1TierIndex n} {τ : ℂ}
    (hpole : step1SuccessorSelectedLevelPole D C j τ) :
    MeromorphicAt (step1SelectedGateFunction D C j) τ :=
  hpole.1

theorem step1SuccessorSelectedLevelPole.not_analyticAt {k d : Nat}
    {D : ActiveStratificationData (n + 2) k d} {C : Step1SelectedChain n k}
    {j : Step1TierIndex n} {τ : ℂ}
    (hpole : step1SuccessorSelectedLevelPole D C j τ) :
    ¬ AnalyticAt ℂ (step1SelectedGateFunction D C j) τ :=
  hpole.2.1

theorem step1SuccessorSelectedLevelPole.arcStructure {k d : Nat}
    {D : ActiveStratificationData (n + 2) k d} {C : Step1SelectedChain n k}
    {j : Step1TierIndex n} {τ : ℂ}
    (hpole : step1SuccessorSelectedLevelPole D C j τ) :
    ∃ q : Nat, ArcStructureResult (step1SelectedGateFunction D C j) τ q :=
  hpole.2.2

theorem step1SuccessorSelectedLevelPole.levelPreimageResult {k d : Nat}
    {D : ActiveStratificationData (n + 2) k d} {C : Step1SelectedChain n k}
    {j : Step1TierIndex n} {τ : ℂ}
    (hpole : step1SuccessorSelectedLevelPole D C j τ) :
    LevelPreimageResult (step1SelectedGateFunction D C j) τ := by
  obtain ⟨q, harc⟩ := hpole.arcStructure
  exact KHead.lem_level_preimage harc

/-- Explicit successor-pole normal form at a no-skip tier point.

This keeps the exact positive-order Laurent normal form of the ignition gate,
one punctured domain disc, and the arc package together — the no-skip analogue of
the KHead `Step1SuccessorPoleNormalForm` structure. -/
structure Step1SuccessorPoleNormalForm {k d : Nat}
    (D : ActiveStratificationData (n + 2) k d) (C : Step1SelectedChain n k)
    (j : Step1TierIndex n) (τ : ℂ) : Type where
  q : Nat
  q_pos : 1 ≤ q
  coeff : ℂ
  radius : ℝ
  radius_pos : 0 < radius
  punctured_subset_omega : puncturedDisc τ radius ⊆ D.Omega j.1
  normalForm :
    LaurentNormalFormAt (step1SelectedGateFunction D C j) τ (q : ℤ) coeff
  arcStructure :
    ArcStructureResult (step1SelectedGateFunction D C j) τ q

namespace Step1SuccessorPoleNormalForm

variable {k d : Nat} {D : ActiveStratificationData (n + 2) k d}
  {C : Step1SelectedChain n k} {j : Step1TierIndex n} {τ : ℂ}

/-- The leading Laurent coefficient in the successor normal form is nonzero. -/
theorem coeff_ne_zero (N : Step1SuccessorPoleNormalForm D C j τ) :
    N.coeff ≠ 0 :=
  N.normalForm.leadingCoeff_ne_zero

/-- The ignition gate is meromorphic at the tier point. -/
theorem meromorphicAt (N : Step1SuccessorPoleNormalForm D C j τ) :
    MeromorphicAt (step1SelectedGateFunction D C j) τ :=
  N.normalForm.meromorphicAt

/-- The positive-order successor normal form is not analytic at the tier point. -/
theorem not_analyticAt (N : Step1SuccessorPoleNormalForm D C j τ) :
    ¬ AnalyticAt ℂ (step1SelectedGateFunction D C j) τ := by
  have hq : (1 : ℤ) ≤ (N.q : ℤ) := by exact_mod_cast N.q_pos
  exact N.normalForm.not_analyticAt hq

/-- The explicit normal form fills the pole-oriented successor field. -/
theorem successorSelectedLevelPole (N : Step1SuccessorPoleNormalForm D C j τ) :
    step1SuccessorSelectedLevelPole D C j τ :=
  ⟨N.meromorphicAt, N.not_analyticAt, ⟨N.q, N.arcStructure⟩⟩

/-- Forget the proof fields of an explicit normal form into the finite-fold
record.  `selectedPoleRecord_isExact` immediately restores every analytic
field, so folding never reduces the pole to a Boolean marker. -/
def toSelectedPoleRecord (N : Step1SuccessorPoleNormalForm D C j τ)
    (h : Fin k) : Step1SelectedPoleRecord n k d where
  firstHead := h
  chain := C
  tier := j
  point := τ
  order := N.q
  coefficient := N.coeff
  radius := N.radius

/-- The fold record obtained from an NS104 normal form is exact. -/
theorem selectedPoleRecord_isExact
    (N : Step1SuccessorPoleNormalForm D C j τ) (h : Fin k)
    (hτΩ : τ ∈ D.Omega j.1) (hpole : step1SelectedLevelPole D C j τ) :
    (N.toSelectedPoleRecord h).IsExact D := by
  exact ⟨hτΩ, hpole, N.q_pos, N.coeff_ne_zero, N.radius_pos,
    N.punctured_subset_omega, N.normalForm, N.arcStructure⟩

/-- Recover the complete NS104 normal-form object from a retained exact pole
record.  This is the bridge used by the adjacent fold: the next induction step
consumes the analytic data stored by the preceding step. -/
noncomputable def ofSelectedPoleRecord
    (P : Step1SelectedPoleRecord n k d) (hP : P.IsExact D) :
    Step1SuccessorPoleNormalForm D P.chain P.tier P.point where
  q := P.order
  q_pos := hP.2.2.1
  coeff := P.coefficient
  radius := P.radius
  radius_pos := hP.2.2.2.2.1
  punctured_subset_omega := hP.2.2.2.2.2.1
  normalForm := hP.2.2.2.2.2.2.1
  arcStructure := hP.2.2.2.2.2.2.2

end Step1SuccessorPoleNormalForm

/-! ## The tier-transition theorem (`tra:cascade` ignition) -/

/-- **Tier ignition.**  From a selected level pole of the currently processed
tier `j` — the selected level `D.level (j, headAt j)` hits `Π` at a domain point
`τ` — the selected gate `csig (D.level (j, headAt j))` acquires an explicit
positive-order Laurent normal form (nonzero coefficient, meromorphic, not
analytic) together with its selected pole arc.  This is the no-skip transfer of
`tra:cascade`: one processed tier ignites the next.

The active-head hypothesis is discharged from target regularity via
`step1_head_active`; the chain witness `C` is the only external input. -/
theorem step1SuccessorPoleNormalForm_nonempty {k d : Nat}
    {theta' : Params (n + 2) k d} {D : ActiveStratificationData (n + 2) k d}
    (hD : ActiveHeadSingularStratification (r := r) theta' D)
    (C : Step1SelectedChain n k) (j : Step1TierIndex n)
    (hactive : C.headAt j ∈ activeHeads theta' j)
    {τ : ℂ} (hτΩ : τ ∈ D.Omega j.1)
    (hpole : step1SelectedLevelPole D C j τ) :
    Nonempty (Step1SuccessorPoleNormalForm D C j τ) := by
  have hpiPi : D.level (j, C.headAt j) τ ∈ Pi := hpole
  obtain ⟨kappa, c, hkappa, _hc, _hLevelNF, hSigNF⟩ :=
    activeLevel_sigmoid_normalForms_at_pole hD j (C.headAt j) hactive hτΩ hpiPi
  have harcNE : Nonempty
      (SelectedArcData (step1SelectedGateFunction D C j) τ kappa c⁻¹) :=
    selectedArcData_of_normalForm hkappa hSigNF
  have harcStruct :
      ArcStructureResult (step1SelectedGateFunction D C j) τ kappa :=
    SelectedArcData.toArcStructureResult (Classical.choice harcNE) hkappa
  have hopen : IsOpen (D.Omega j.1) :=
    (hD.domain j.1 (Nat.le_of_lt j.2)).isOpen
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen τ hτΩ
  refine ⟨
    { q := kappa
      q_pos := hkappa
      coeff := c⁻¹
      radius := ε
      radius_pos := hε
      punctured_subset_omega := ?_
      normalForm := hSigNF
      arcStructure := harcStruct }⟩
  intro z hz
  exact hball (Metric.mem_ball.mpr hz.2)

/-- **Tier ignition (data form).**  The chosen explicit successor normal form.
Its underlying nonemptiness is `step1SuccessorPoleNormalForm_nonempty`. -/
noncomputable def step1SuccessorPoleNormalForm_of_selectedLevelPole {k d : Nat}
    {theta' : Params (n + 2) k d} {D : ActiveStratificationData (n + 2) k d}
    (hD : ActiveHeadSingularStratification (r := r) theta' D)
    (C : Step1SelectedChain n k) (j : Step1TierIndex n)
    (hactive : C.headAt j ∈ activeHeads theta' j)
    {τ : ℂ} (hτΩ : τ ∈ D.Omega j.1)
    (hpole : step1SelectedLevelPole D C j τ) :
    Step1SuccessorPoleNormalForm D C j τ :=
  Classical.choice
    (step1SuccessorPoleNormalForm_nonempty hD C j hactive hτΩ hpole)

/-- Immediate ignition corollary: the constructed normal form fills the
pole-oriented successor predicate, i.e. the next tier is ignited. -/
theorem step1_successorSelectedLevelPole_of_selectedLevelPole {k d : Nat}
    {theta' : Params (n + 2) k d} {D : ActiveStratificationData (n + 2) k d}
    (hD : ActiveHeadSingularStratification (r := r) theta' D)
    (C : Step1SelectedChain n k) (j : Step1TierIndex n)
    (hactive : C.headAt j ∈ activeHeads theta' j)
    {τ : ℂ} (hτΩ : τ ∈ D.Omega j.1)
    (hpole : step1SelectedLevelPole D C j τ) :
    step1SuccessorSelectedLevelPole D C j τ :=
  (step1SuccessorPoleNormalForm_of_selectedLevelPole
    hD C j hactive hτΩ hpole).successorSelectedLevelPole

/-! ## One-slot ignition and the finite tier fold -/

/-- Concrete NS104 one-slot operator.  Given the current selected collision,
the theorem constructs (rather than assumes) the exact Laurent/arc payload and
installs it in the next ready ignition slot while preserving the strengthened
`Step1TierInvariant`. -/
theorem step1_processIgnition_of_selectedLevelPole
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta')
    (D : ActiveStratificationData (n + 2) k d)
    (hD : ActiveHeadSingularStratification (r := r) theta' D)
    (w : Vec d) {B : Step1TierBookkeeping n k d}
    (hInv : Step1TierInvariant H D w B)
    (h : Fin k) (j : Step1LaterTierIndex n)
    (hready : Step1ReadyToProcess B.processed (h, .ignition j))
    {τ : ℂ} (hτΩ : τ ∈ D.Omega j.toTier.1)
    (hpole : step1SelectedLevelPole D (B.chain h) j.toTier τ) :
    ∃ P : Step1SelectedPoleRecord n k d,
      P = (step1SuccessorPoleNormalForm_of_selectedLevelPole hD (B.chain h) j.toTier
        (step1_head_active H j.toTier ((B.chain h).headAt j.toTier)) hτΩ hpole).toSelectedPoleRecord h ∧
      Step1TierInvariant H D w (step1ProcessIgnition H w B h j P) := by
  let N : Step1SuccessorPoleNormalForm D (B.chain h) j.toTier τ :=
    step1SuccessorPoleNormalForm_of_selectedLevelPole hD (B.chain h) j.toTier
      (step1_head_active H j.toTier ((B.chain h).headAt j.toTier)) hτΩ hpole
  let P : Step1SelectedPoleRecord n k d := N.toSelectedPoleRecord h
  refine ⟨P, rfl, ?_⟩
  apply step1ProcessIgnition_preserves_invariant H w D hInv hready
  · rfl
  · rfl
  · rfl
  · exact N.selectedPoleRecord_isExact h hτΩ hpole

/-- Add the concrete NS104 ignition step to an existing processing-order fold.
This is the induction constructor used head-by-head and tier-by-tier; all
previous exact pole records remain present by `Step1ProcessingFold`'s invariant
theorem. -/
theorem step1ProcessingFold_ignition_of_selectedLevelPole
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta')
    (D : ActiveStratificationData (n + 2) k d)
    (hD : ActiveHeadSingularStratification (r := r) theta' D)
    (w : Vec d) {B₀ B : Step1TierBookkeeping n k d}
    (fold : Step1ProcessingFold H D w B₀ B)
    (hInv₀ : Step1TierInvariant H D w B₀)
    (h : Fin k) (j : Step1LaterTierIndex n)
    (hready : Step1ReadyToProcess B.processed (h, .ignition j))
    {τ : ℂ} (hτΩ : τ ∈ D.Omega j.toTier.1)
    (hpole : step1SelectedLevelPole D (B.chain h) j.toTier τ) :
    ∃ P : Step1SelectedPoleRecord n k d,
      Step1ProcessingFold H D w B₀ (step1ProcessIgnition H w B h j P) ∧
      Step1TierInvariant H D w (step1ProcessIgnition H w B h j P) := by
  have hInv : Step1TierInvariant H D w B := fold.preserves_invariant hInv₀
  rcases step1_processIgnition_of_selectedLevelPole H D hD w hInv h j hready hτΩ hpole with
    ⟨P, hP, hInv'⟩
  refine ⟨P, ?_, hInv'⟩
  have hPexact : P.IsExact D := by
    rw [hP]
    exact
      (step1SuccessorPoleNormalForm_of_selectedLevelPole hD (B.chain h) j.toTier
        (step1_head_active H j.toTier ((B.chain h).headAt j.toTier)) hτΩ hpole).selectedPoleRecord_isExact
          h hτΩ hpole
  apply Step1ProcessingFold.ignition fold hready
  · simp [hP, Step1SuccessorPoleNormalForm.toSelectedPoleRecord]
  · simp [hP, Step1SuccessorPoleNormalForm.toSelectedPoleRecord]
  · simp [hP, Step1SuccessorPoleNormalForm.toSelectedPoleRecord]
  · exact hPexact

/-! ## Tower dominance (hypotheses feeding the ignition)

The KHead `step1TowerDominance` cluster is phrased over the finite dominance
family from `DominanceSibling.lean`, which is not yet ported to the no-skip tree.
Here we port the same mathematical content directly over a single NS100
`DominanceTowerData`: strict per-stage threshold domination, its conversion to
the non-strict `SatisfiesTowerThresholds` interface, and the selected-tower
nonvanishing capstone. -/

/-- Strict finite-tower dominance: every stage threshold is strictly dominated by
the corresponding selected gate magnitude. -/
def step1TowerDominance {k p : Nat} {c : HeadChain (n + 2) k p}
    {f : FormalPoly (n + 2) k} (data : DominanceTowerData c f)
    (z : FormalVar (n + 2) k → ℂ) : Prop :=
  ∀ i : Fin p,
    dominanceTowerThreshold data i z < ‖z (c.selectedVar i)‖

/-- Reduced form of `step1TowerDominance`: the strict inequality at one stage. -/
theorem step1TowerDominance_iff {k p : Nat} {c : HeadChain (n + 2) k p}
    {f : FormalPoly (n + 2) k} {data : DominanceTowerData c f}
    {z : FormalVar (n + 2) k → ℂ}
    (hdom : step1TowerDominance data z) (i : Fin p) :
    dominanceTowerThreshold data i z < ‖z (c.selectedVar i)‖ :=
  hdom i

/-- Conversion to the NS100 non-strict tower-threshold interface.  The thresholds
are `≥ 1 ≥ 0`, so the strict `<` supplies the non-strict coercion-norm
inequality. -/
theorem step1TowerDominance_satisfiesThresholds {k p : Nat}
    {c : HeadChain (n + 2) k p} {f : FormalPoly (n + 2) k}
    {data : DominanceTowerData c f} (hconst : data.topConstant ≠ 0)
    {z : FormalVar (n + 2) k → ℂ} (hdom : step1TowerDominance data z) :
    SatisfiesTowerThresholds c (dominanceTowerThreshold data) z := by
  intro i
  have hge1 : (1 : ℝ) ≤ dominanceTowerThreshold data i z :=
    towerThreshold_ge_one data hconst i z
  have hnonneg : (0 : ℝ) ≤ dominanceTowerThreshold data i z :=
    le_trans zero_le_one hge1
  have hnorm :
      ‖((dominanceTowerThreshold data i z : ℝ) : ℂ)‖ =
        dominanceTowerThreshold data i z := by
    simp [abs_of_nonneg hnonneg]
  rw [hnorm]
  exact le_of_lt (hdom i)

/-- Selected-tower nonvanishing from strict tower dominance.  This is the no-skip
`step1TowerDominance_eval_ne_zero`: `dominance_tower_core_nonvanishing` applied
through `step1TowerDominance_satisfiesThresholds`. -/
theorem step1TowerDominance_eval_ne_zero {k p : Nat}
    {c : HeadChain (n + 2) k p} {f : FormalPoly (n + 2) k}
    {data : DominanceTowerData c f}
    (hdeg : ∀ i : Fin p, 1 ≤ data.degree i)
    (hconst : data.topConstant ≠ 0)
    (htop : DominanceTowerTopConstant data)
    (hfinal : DominanceTowerFinalCoeff data)
    (hrec : DominanceTowerEvalRecurrence data)
    {z : FormalVar (n + 2) k → ℂ} (hdom : step1TowerDominance data z) :
    f.eval₂ (algebraMap ℝ ℂ) z ≠ 0 :=
  dominance_tower_core_nonvanishing data hdeg hconst htop hfinal hrec
    (step1TowerDominance_satisfiesThresholds hconst hdom)

end

end TransformerIdentifiability.NLayer.NoSkip
