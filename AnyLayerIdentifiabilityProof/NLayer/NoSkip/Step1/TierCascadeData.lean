import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Step1.Hypotheses
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Analytic.ActiveStratification
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Analytic.PoleArcs

set_option autoImplicit false

open Matrix

namespace TransformerIdentifiability.NLayer.NoSkip

/-!
# Step 1 tier-cascade bookkeeping

This file contains only finite indices, selected-chain data, coefficient
records, the processing order, and proof-light predicates relating them to the
target cascade certificate and active stratification.  Pole creation,
dominance towers, sibling exclusion, and blowup are intentionally downstream.
-/

noncomputable section

/-! ## Tier indices and stratification slots -/

/-- Zero-based tiers for a parameter family of depth `n + 2`. -/
abbrev Step1TierIndex (n : Nat) := Fin (n + 2)

/-- The later tiers, whose value `j` addresses ambient tier `j + 1`. -/
abbrev Step1LaterTierIndex (n : Nat) := Fin (n + 1)

/-- The first tier. -/
def step1FirstTierIndex (n : Nat) : Step1TierIndex n :=
  ⟨0, by omega⟩

/-- Embed a later-tier index into the complete tier type. -/
def Step1LaterTierIndex.toTier {n : Nat} (j : Step1LaterTierIndex n) :
    Step1TierIndex n :=
  laterLayer j

@[simp] theorem Step1LaterTierIndex.toTier_val {n : Nat}
    (j : Step1LaterTierIndex n) :
    j.toTier.val = j.val + 1 :=
  rfl

/-- The final zero-based tier. -/
def step1FinalTierIndex (n : Nat) : Step1TierIndex n :=
  Fin.last (n + 1)

@[simp] theorem step1FinalTierIndex_val (n : Nat) :
    (step1FinalTierIndex n).val = n + 1 :=
  rfl

/-- Domain on which the level functions at tier `j` are holomorphic. -/
def step1TierDomain {n k d : Nat}
    (D : ActiveStratificationData (n + 2) k d) (j : Step1TierIndex n) : Set ℂ :=
  D.Omega j.val

/-- Singular stratum associated with tier `j`. -/
def step1TierStratum {n k d : Nat}
    (D : ActiveStratificationData (n + 2) k d) (j : Step1TierIndex n) : Set ℂ :=
  D.stratum j.val

/-- A point lies in the analytic domain for the given tier. -/
def InStep1TierDomain {n k d : Nat}
    (D : ActiveStratificationData (n + 2) k d)
    (j : Step1TierIndex n) (tau : ℂ) : Prop :=
  tau ∈ step1TierDomain D j

/-- A point lies in the singular stratum for the given tier. -/
def InStep1TierStratum {n k d : Nat}
    (D : ActiveStratificationData (n + 2) k d)
    (j : Step1TierIndex n) (tau : ℂ) : Prop :=
  tau ∈ step1TierStratum D j

/-! ## Selected chains -/

/-- One first-layer head together with one selected head at every later tier. -/
structure Step1SelectedChain (n k : Nat) where
  firstHead : Fin k
  laterHead : Step1LaterTierIndex n → Fin k

namespace Step1SelectedChain

/-- Selected head at an arbitrary complete tier. -/
def headAt {n k : Nat} (C : Step1SelectedChain n k) :
    Step1TierIndex n → Fin k :=
  Fin.cases C.firstHead C.laterHead

@[simp] theorem headAt_first {n k : Nat} (C : Step1SelectedChain n k) :
    C.headAt (step1FirstTierIndex n) = C.firstHead :=
  rfl

@[simp] theorem headAt_later {n k : Nat} (C : Step1SelectedChain n k)
    (j : Step1LaterTierIndex n) :
    C.headAt j.toTier = C.laterHead j := by
  simp [headAt, Step1LaterTierIndex.toTier, laterLayer]

/-- Formal gate variable selected at a tier. -/
def selectedVar {n k : Nat} (C : Step1SelectedChain n k)
    (j : Step1TierIndex n) : FormalVar (n + 2) k :=
  (j, C.headAt j)

@[simp] theorem selectedVar_layer {n k : Nat} (C : Step1SelectedChain n k)
    (j : Step1TierIndex n) :
    (C.selectedVar j).1 = j :=
  rfl

@[simp] theorem selectedVar_head {n k : Nat} (C : Step1SelectedChain n k)
    (j : Step1TierIndex n) :
    (C.selectedVar j).2 = C.headAt j :=
  rfl

/-- Forget a cascade semantic witness to its proof-free selected chain. -/
def ofCascade {n k : Nat} (h : Fin k) (chi : CascadeChain (n + 1) k) :
    Step1SelectedChain n k where
  firstHead := h
  laterHead := chi

@[simp] theorem ofCascade_firstHead {n k : Nat} (h : Fin k)
    (chi : CascadeChain (n + 1) k) :
    (ofCascade h chi).firstHead = h :=
  rfl

@[simp] theorem ofCascade_laterHead {n k : Nat} (h : Fin k)
    (chi : CascadeChain (n + 1) k) (j : Step1LaterTierIndex n) :
    (ofCascade h chi).laterHead j = chi j :=
  rfl

end Step1SelectedChain

/-! ## Selected analytic functions -/

/-- The selected level function at a complete tier.  This definition lives in
the data module so that the finite-fold invariant can retain exact analytic
payloads without depending on the theorem that constructs them. -/
def step1SelectedLevelFunction {n k d : Nat}
    (D : ActiveStratificationData (n + 2) k d) (C : Step1SelectedChain n k)
    (j : Step1TierIndex n) : ℂ → ℂ :=
  D.level (C.selectedVar j)

/-- The selected gate function at a complete tier. -/
def step1SelectedGateFunction {n k d : Nat}
    (D : ActiveStratificationData (n + 2) k d) (C : Step1SelectedChain n k)
    (j : Step1TierIndex n) : ℂ → ℂ :=
  fun z => csig (step1SelectedLevelFunction D C j z)

@[simp] theorem step1SelectedLevelFunction_apply {n k d : Nat}
    (D : ActiveStratificationData (n + 2) k d) (C : Step1SelectedChain n k)
    (j : Step1TierIndex n) (z : ℂ) :
    step1SelectedLevelFunction D C j z = D.level (j, C.headAt j) z :=
  rfl

@[simp] theorem step1SelectedGateFunction_apply {n k d : Nat}
    (D : ActiveStratificationData (n + 2) k d) (C : Step1SelectedChain n k)
    (j : Step1TierIndex n) (z : ℂ) :
    step1SelectedGateFunction D C j z = csig (D.level (j, C.headAt j) z) :=
  rfl

/-- The target chain selected by the authoritative recursive-genericity witness. -/
def step1TargetSelectedChain {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (h : Fin k) :
    Step1SelectedChain n k :=
  Step1SelectedChain.ofCascade h (H.targetCascadeData.head h).chain

@[simp] theorem step1TargetSelectedChain_firstHead {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (h : Fin k) :
    (step1TargetSelectedChain H h).firstHead = h :=
  rfl

@[simp] theorem step1TargetSelectedChain_laterHead {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (h : Fin k)
    (j : Step1LaterTierIndex n) :
    (step1TargetSelectedChain H h).laterHead j =
      (H.targetCascadeData.head h).chain j :=
  rfl

/-! ## Residue and ignition records -/

/-- One coordinate of the selected value residue after an arbitrary tier. -/
structure Step1TierResidueRecord (n k d : Nat) where
  firstHead : Fin k
  chain : Step1SelectedChain n k
  tier : Step1TierIndex n
  coordinate : Fin d
  coefficient : ℝ

/-- One coordinate of the final selected residue vector. -/
structure Step1ResidueRecord (n k d : Nat) where
  firstHead : Fin k
  chain : Step1SelectedChain n k
  coordinate : Fin d
  coefficient : ℝ

/-- One selected ignition quadratic at a later tier. -/
structure Step1IgnitionRecord (n k d : Nat) where
  firstHead : Fin k
  chain : Step1SelectedChain n k
  stage : Step1LaterTierIndex n
  matrix : Matrix (Fin d) (Fin d) ℝ
  coefficient : ℝ

/-- Exact analytic data retained when an ignition slot is processed.  The
point and Laurent constants are stored as data; `IsExact` below ties them to
the selected chain and the concrete active stratification. -/
structure Step1SelectedPoleRecord (n k d : Nat) where
  firstHead : Fin k
  chain : Step1SelectedChain n k
  tier : Step1TierIndex n
  point : ℂ
  order : Nat
  coefficient : ℂ
  radius : ℝ

namespace Step1SelectedPoleRecord

/-- A retained pole record is the exact selected collision and gate Laurent
payload, not merely a marker saying that a tier was reached. -/
def IsExact {n k d : Nat} (D : ActiveStratificationData (n + 2) k d)
    (P : Step1SelectedPoleRecord n k d) : Prop :=
  P.point ∈ D.Omega P.tier.1 ∧
  D.level (P.chain.selectedVar P.tier) P.point ∈ Pi ∧
  1 ≤ P.order ∧
  P.coefficient ≠ 0 ∧
  0 < P.radius ∧
  puncturedDisc P.point P.radius ⊆ D.Omega P.tier.1 ∧
  LaurentNormalFormAt (step1SelectedGateFunction D P.chain P.tier) P.point
      (P.order : ℤ) P.coefficient ∧
  ArcStructureResult (step1SelectedGateFunction D P.chain P.tier) P.point P.order

theorem isExact_levelPole {n k d : Nat}
    {D : ActiveStratificationData (n + 2) k d}
    {P : Step1SelectedPoleRecord n k d} (hP : P.IsExact D) :
    D.level (P.chain.selectedVar P.tier) P.point ∈ Pi :=
  hP.2.1

theorem isExact_normalForm {n k d : Nat}
    {D : ActiveStratificationData (n + 2) k d}
    {P : Step1SelectedPoleRecord n k d} (hP : P.IsExact D) :
    LaurentNormalFormAt (step1SelectedGateFunction D P.chain P.tier) P.point
      (P.order : ℤ) P.coefficient :=
  hP.2.2.2.2.2.2.1

end Step1SelectedPoleRecord

namespace Step1ResidueRecord

/-- The recorded residue coordinate is nonzero. -/
def IsNonzero {n k d : Nat} (R : Step1ResidueRecord n k d) : Prop :=
  R.coefficient ≠ 0

end Step1ResidueRecord

namespace Step1TierResidueRecord

/-- The tier-local residue coordinate is nonzero. -/
def IsNonzero {n k d : Nat} (R : Step1TierResidueRecord n k d) : Prop :=
  R.coefficient ≠ 0

end Step1TierResidueRecord

namespace Step1IgnitionRecord

/-- The recorded ignition coefficient is nonzero. -/
def IsNonzero {n k d : Nat} (R : Step1IgnitionRecord n k d) : Prop :=
  R.coefficient ≠ 0

end Step1IgnitionRecord

/-- Canonical target residue record for a probe vector and coordinate. -/
noncomputable def step1TargetTierResidueRecord {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w : Vec d)
    (h : Fin k) (j : Step1TierIndex n) (i : Fin d) :
    Step1TierResidueRecord n k d where
  firstHead := h
  chain := step1TargetSelectedChain H h
  tier := j
  coordinate := i
  coefficient :=
    (cascadeProduct theta' h (H.targetCascadeData.head h).chain j.val *ᵥ w) i

/-- Canonical target final-residue record for a probe vector and coordinate. -/
noncomputable def step1TargetResidueRecord {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w : Vec d)
    (h : Fin k) (i : Fin d) : Step1ResidueRecord n k d where
  firstHead := h
  chain := step1TargetSelectedChain H h
  coordinate := i
  coefficient :=
    (cascadeFinalProduct theta' h (H.targetCascadeData.head h).chain *ᵥ w) i

/-- Canonical target ignition record for a probe vector and later tier. -/
noncomputable def step1TargetIgnitionRecord {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w : Vec d)
    (h : Fin k) (j : Step1LaterTierIndex n) : Step1IgnitionRecord n k d where
  firstHead := h
  chain := step1TargetSelectedChain H h
  stage := j
  matrix := cascadeIgnitionMatrix theta' h
    (H.targetCascadeData.head h).chain j
  coefficient := matrixBilin
    (cascadeIgnitionMatrix theta' h (H.targetCascadeData.head h).chain j) w w

@[simp] theorem step1TargetTierResidueRecord_first_coefficient {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w : Vec d)
    (h : Fin k) (i : Fin d) :
    (step1TargetTierResidueRecord H w h (step1FirstTierIndex n) i).coefficient =
      (valueMatrix theta' 0 h *ᵥ w) i :=
  rfl

@[simp] theorem step1TargetTierResidueRecord_final_coefficient {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w : Vec d)
    (h : Fin k) (i : Fin d) :
    (step1TargetTierResidueRecord H w h (step1FinalTierIndex n) i).coefficient =
      (step1TargetResidueRecord H w h i).coefficient :=
  rfl

@[simp] theorem step1TargetResidueRecord_coefficient {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w : Vec d)
    (h : Fin k) (i : Fin d) :
    (step1TargetResidueRecord H w h i).coefficient =
      (cascadeFinalProduct theta' h (H.targetCascadeData.head h).chain *ᵥ w) i :=
  rfl

@[simp] theorem step1TargetIgnitionRecord_matrix {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w : Vec d)
    (h : Fin k) (j : Step1LaterTierIndex n) :
    (step1TargetIgnitionRecord H w h j).matrix =
      cascadeIgnitionMatrix theta' h (H.targetCascadeData.head h).chain j :=
  rfl

@[simp] theorem step1TargetIgnitionRecord_coefficient {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w : Vec d)
    (h : Fin k) (j : Step1LaterTierIndex n) :
    (step1TargetIgnitionRecord H w h j).coefficient =
      matrixBilin
        (cascadeIgnitionMatrix theta' h (H.targetCascadeData.head h).chain j) w w :=
  rfl

/-- The certificate's selected final-residue matrix is nonzero before choosing a probe. -/
theorem step1TargetFinalResidueMatrix_ne_zero {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (h : Fin k) :
    cascadeFinalProduct theta' h (H.targetCascadeData.head h).chain ≠ 0 :=
  (H.targetCascadeData.head h).semantic.final_residue_ne_zero

/-- Every certificate-selected ignition matrix is nonzero. -/
theorem step1TargetIgnitionMatrix_ne_zero {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (h : Fin k)
    (j : Step1LaterTierIndex n) :
    cascadeIgnitionMatrix theta' h (H.targetCascadeData.head h).chain j ≠ 0 :=
  (H.targetCascadeData.head h).semantic.ignition_ne_zero j

/-- A residue record agrees with the target certificate and probe. -/
def Step1TierResidueRecord.IsCanonical {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w : Vec d)
    (R : Step1TierResidueRecord n k d) : Prop :=
  R = step1TargetTierResidueRecord H w R.firstHead R.tier R.coordinate

/-- A final residue record agrees with the target certificate and probe. -/
def Step1ResidueRecord.IsCanonical {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w : Vec d)
    (R : Step1ResidueRecord n k d) : Prop :=
  R = step1TargetResidueRecord H w R.firstHead R.coordinate

/-- An ignition record agrees with the target certificate and probe. -/
def Step1IgnitionRecord.IsCanonical {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w : Vec d)
    (R : Step1IgnitionRecord n k d) : Prop :=
  R = step1TargetIgnitionRecord H w R.firstHead R.stage

@[simp] theorem step1TargetResidueRecord_isCanonical {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w : Vec d)
    (h : Fin k) (i : Fin d) :
    (step1TargetResidueRecord H w h i).IsCanonical H w :=
  rfl

@[simp] theorem step1TargetTierResidueRecord_isCanonical {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w : Vec d)
    (h : Fin k) (j : Step1TierIndex n) (i : Fin d) :
    (step1TargetTierResidueRecord H w h j i).IsCanonical H w :=
  rfl

@[simp] theorem step1TargetIgnitionRecord_isCanonical {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w : Vec d)
    (h : Fin k) (j : Step1LaterTierIndex n) :
    (step1TargetIgnitionRecord H w h j).IsCanonical H w :=
  rfl

/-! ## Finite processing order -/

/-- For one first head, process all ignition stages in increasing order and
then all residue coordinates. -/
inductive Step1ProcessSlot (n d : Nat)
  | ignition (stage : Step1LaterTierIndex n)
  | residue (coordinate : Fin d)
deriving DecidableEq, Fintype

/-- Complete processing index, grouped first by the first-layer head. -/
abbrev Step1ProcessingIndex (n k d : Nat) :=
  Fin k × Step1ProcessSlot n d

/-- Rank of a slot inside one selected chain. -/
def step1ProcessSlotRank {n d : Nat} : Step1ProcessSlot n d → Nat
  | .ignition j => j.val
  | .residue i => n + 1 + i.val

/-- Lexicographic numeric rank: first head, then ignition stages, then residue coordinates. -/
def step1ProcessingRank {n k d : Nat} (idx : Step1ProcessingIndex n k d) : Nat :=
  idx.1.val * (n + 1 + d) + step1ProcessSlotRank idx.2

/-- Strict processing order. -/
def Step1ProcessedBefore {n k d : Nat}
    (i j : Step1ProcessingIndex n k d) : Prop :=
  step1ProcessingRank i < step1ProcessingRank j

@[simp] theorem step1ProcessSlotRank_ignition {n d : Nat}
    (j : Step1LaterTierIndex n) :
    step1ProcessSlotRank (Step1ProcessSlot.ignition j : Step1ProcessSlot n d) = j.val :=
  rfl

@[simp] theorem step1ProcessSlotRank_residue {n d : Nat} (i : Fin d) :
    step1ProcessSlotRank (Step1ProcessSlot.residue i : Step1ProcessSlot n d) =
      n + 1 + i.val :=
  rfl

theorem step1_ignition_before_residue {n k d : Nat} (h : Fin k)
    (j : Step1LaterTierIndex n) (i : Fin d) :
    Step1ProcessedBefore
      (h, Step1ProcessSlot.ignition j)
      (h, Step1ProcessSlot.residue i) := by
  unfold Step1ProcessedBefore step1ProcessingRank
  simp only [step1ProcessSlotRank_ignition, step1ProcessSlotRank_residue]
  omega

/-- A processed set is an initial segment of the finite processing order. -/
def Step1IsProcessingPrefix {n k d : Nat}
    (processed : Finset (Step1ProcessingIndex n k d)) : Prop :=
  ∀ i j, Step1ProcessedBefore i j → j ∈ processed → i ∈ processed

theorem step1_empty_isProcessingPrefix {n k d : Nat} :
    Step1IsProcessingPrefix
      (∅ : Finset (Step1ProcessingIndex n k d)) := by
  intro i j hij hj
  simp at hj

/-- A slot is ready precisely when it is new and every strictly earlier slot
has already been processed. -/
def Step1ReadyToProcess {n k d : Nat}
    (processed : Finset (Step1ProcessingIndex n k d))
    (idx : Step1ProcessingIndex n k d) : Prop :=
  idx ∉ processed ∧ ∀ i, Step1ProcessedBefore i idx → i ∈ processed

/-- Inserting the next ready slot preserves the initial-segment property. -/
theorem step1_insert_isProcessingPrefix {n k d : Nat}
    {processed : Finset (Step1ProcessingIndex n k d)}
    {idx : Step1ProcessingIndex n k d}
    (hpref : Step1IsProcessingPrefix processed)
    (hready : Step1ReadyToProcess processed idx) :
    Step1IsProcessingPrefix (insert idx processed) := by
  intro i j hij hj
  simp only [Finset.mem_insert] at hj ⊢
  rcases hj with rfl | hj
  · exact Or.inr (hready.2 i hij)
  · exact Or.inr (hpref i j hij hj)

/-- Every proper processing prefix has a next ready slot.  We choose a missing
slot of minimal numeric rank; minimality supplies all of its predecessors. -/
theorem step1_exists_ready_of_ne_univ {n k d : Nat}
    (processed : Finset (Step1ProcessingIndex n k d))
    (hne : processed ≠ Finset.univ) :
    ∃ idx, Step1ReadyToProcess processed idx := by
  classical
  let missing : Finset (Step1ProcessingIndex n k d) := Finset.univ \ processed
  have hmissing : missing.Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hsub
    apply hne
    apply Finset.eq_univ_of_forall
    intro idx
    by_contra hidx
    exact hidx (hsub (by simp [missing, hidx]))
  let ranks : Finset Nat := missing.image step1ProcessingRank
  have hranks : ranks.Nonempty := hmissing.image _
  have hminmem : ranks.min' hranks ∈ ranks := Finset.min'_mem ranks hranks
  rcases Finset.mem_image.mp hminmem with ⟨idx, hidxMissing, hidxRank⟩
  refine ⟨idx, ?_, ?_⟩
  · simpa [missing] using hidxMissing
  · intro i hi
    by_contra hiProcessed
    have hiMissing : i ∈ missing := by simp [missing, hiProcessed]
    have hiRankMem : step1ProcessingRank i ∈ ranks :=
      Finset.mem_image.mpr ⟨i, hiMissing, rfl⟩
    have hle := Finset.min'_le ranks (step1ProcessingRank i) hiRankMem
    rw [← hidxRank] at hle
    exact (not_le_of_gt hi) hle

/-! ## Proof-light cascade state and invariants -/

/-- Mutable bookkeeping consumed by the later tier proofs.  No analytic fact is
stored as a field. -/
structure Step1TierBookkeeping (n k d : Nat) where
  chain : Fin k → Step1SelectedChain n k
  domain : Step1TierIndex n → Set ℂ
  stratum : Step1TierIndex n → Set ℂ
  processed : Finset (Step1ProcessingIndex n k d)
  residue : Fin k → Fin d → Option (Step1ResidueRecord n k d)
  ignition : Fin k → Step1LaterTierIndex n → Option (Step1IgnitionRecord n k d)
  selectedPole : Fin k → Step1TierIndex n → Option (Step1SelectedPoleRecord n k d)

/-- Chain choices in the state are exactly the target certificate choices. -/
def Step1ChainsMatch {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta')
    (B : Step1TierBookkeeping n k d) : Prop :=
  ∀ h, B.chain h = step1TargetSelectedChain H h

/-- Domain and stratum slots are exactly those of the active stratification. -/
def Step1DomainsMatch {n k d : Nat}
    (D : ActiveStratificationData (n + 2) k d)
    (B : Step1TierBookkeeping n k d) : Prop :=
  (∀ j, B.domain j = step1TierDomain D j) ∧
  (∀ j, B.stratum j = step1TierStratum D j)

/-- Every present coefficient record is the canonical target record. -/
def Step1RecordsMatch {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w : Vec d)
    (B : Step1TierBookkeeping n k d) : Prop :=
  (∀ h i R, B.residue h i = some R →
      R = step1TargetResidueRecord H w h i) ∧
  (∀ h j R, B.ignition h j = some R →
      R = step1TargetIgnitionRecord H w h j)

/-- Every retained pole is attached to the correct head, selected chain and
tier, and contains the exact collision/Laurent/arc data. -/
def Step1SelectedPolesMatch {n k d : Nat}
    (D : ActiveStratificationData (n + 2) k d)
    (B : Step1TierBookkeeping n k d) : Prop :=
  ∀ h j P, B.selectedPole h j = some P →
    P.firstHead = h ∧ P.chain = B.chain h ∧ P.tier = j ∧ P.IsExact D

/-- The processed set is a prefix and records are present exactly at processed slots. -/
def Step1ProcessingCoherent {n k d : Nat}
    (B : Step1TierBookkeeping n k d) : Prop :=
  Step1IsProcessingPrefix B.processed ∧
  ∀ h slot,
    (h, slot) ∈ B.processed ↔
      match slot with
      | .ignition j =>
          (∃ R, B.ignition h j = some R) ∧
          ∃ P, B.selectedPole h j.toTier = some P
      | .residue i => ∃ R, B.residue h i = some R

/-- Complete bookkeeping invariant.  It is a conjunction rather than a record
with analytic proof fields, so later stages may strengthen it locally. -/
def Step1TierInvariant {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta')
    (D : ActiveStratificationData (n + 2) k d) (w : Vec d)
    (B : Step1TierBookkeeping n k d) : Prop :=
  Step1ChainsMatch H B ∧
  Step1DomainsMatch D B ∧
  Step1RecordsMatch H w B ∧
  Step1SelectedPolesMatch D B ∧
  Step1ProcessingCoherent B

/-- Empty initial bookkeeping for a fixed target certificate and stratification. -/
def step1InitialTierBookkeeping {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta')
    (D : ActiveStratificationData (n + 2) k d) :
    Step1TierBookkeeping n k d where
  chain := step1TargetSelectedChain H
  domain := step1TierDomain D
  stratum := step1TierStratum D
  processed := ∅
  residue := fun _ _ => none
  ignition := fun _ _ => none
  selectedPole := fun _ _ => none

/-- The empty state satisfies every bookkeeping invariant, independently of
the later analytic construction. -/
theorem step1InitialTierInvariant {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta')
    (D : ActiveStratificationData (n + 2) k d) (w : Vec d) :
    Step1TierInvariant H D w (step1InitialTierBookkeeping H D) := by
  refine ⟨fun h => rfl, ⟨fun j => rfl, fun j => rfl⟩, ?_, ?_, ?_⟩
  · constructor
    · intro h i R hR
      change (none : Option (Step1ResidueRecord n k d)) = some R at hR
      contradiction
    · intro h i R hR
      change (none : Option (Step1IgnitionRecord n k d)) = some R at hR
      contradiction
  · intro h j P hP
    change (none : Option (Step1SelectedPoleRecord n k d)) = some P at hP
    contradiction
  · refine ⟨step1_empty_isProcessingPrefix, ?_⟩
    intro h slot
    cases slot <;> simp [step1InitialTierBookkeeping]

/-! ## One-slot state operators -/

/-- Process one ignition slot, retaining both its canonical algebraic record
and the exact analytic selected-pole payload constructed by the tier theorem. -/
def step1ProcessIgnition {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w : Vec d)
    (B : Step1TierBookkeeping n k d) (h : Fin k)
    (j : Step1LaterTierIndex n) (P : Step1SelectedPoleRecord n k d) :
    Step1TierBookkeeping n k d where
  chain := B.chain
  domain := B.domain
  stratum := B.stratum
  processed := insert (h, .ignition j) B.processed
  residue := B.residue
  ignition := Function.update B.ignition h
    (Function.update (B.ignition h) j (some (step1TargetIgnitionRecord H w h j)))
  selectedPole := Function.update B.selectedPole h
    (Function.update (B.selectedPole h) j.toTier (some P))

/-- Process one final-residue coordinate. -/
def step1ProcessResidue {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w : Vec d)
    (B : Step1TierBookkeeping n k d) (h : Fin k) (i : Fin d) :
    Step1TierBookkeeping n k d where
  chain := B.chain
  domain := B.domain
  stratum := B.stratum
  processed := insert (h, .residue i) B.processed
  residue := Function.update B.residue h
    (Function.update (B.residue h) i (some (step1TargetResidueRecord H w h i)))
  ignition := B.ignition
  selectedPole := B.selectedPole

/-- The exact pole side of the invariant is preserved by one ignition update. -/
theorem step1ProcessIgnition_selectedPolesMatch {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w : Vec d)
    {D : ActiveStratificationData (n + 2) k d}
    {B : Step1TierBookkeeping n k d} {h : Fin k}
    {j : Step1LaterTierIndex n} {P : Step1SelectedPoleRecord n k d}
    (hmatch : Step1SelectedPolesMatch D B)
    (hhead : P.firstHead = h) (hchain : P.chain = B.chain h)
    (htier : P.tier = j.toTier) (hexact : P.IsExact D) :
    Step1SelectedPolesMatch D (step1ProcessIgnition H w B h j P) := by
  intro h' t P' hP'
  by_cases hh : h' = h
  · subst h'
    by_cases ht : t = j.toTier
    · subst t
      simp only [step1ProcessIgnition, Function.update_self] at hP'
      cases hP'
      exact ⟨hhead, hchain, htier, hexact⟩
    · have hne : t ≠ j.toTier := ht
      simp [step1ProcessIgnition, Function.update, hne] at hP'
      exact hmatch h t P' hP'
  · have hne : h' ≠ h := hh
    simp [step1ProcessIgnition, Function.update, hne] at hP'
    exact hmatch h' t P' hP'

/-- Processing one ready ignition slot preserves the complete strengthened
invariant, including the exact pole payload. -/
theorem step1ProcessIgnition_preserves_invariant {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w : Vec d)
    (D : ActiveStratificationData (n + 2) k d)
    {B : Step1TierBookkeeping n k d} {h : Fin k}
    {j : Step1LaterTierIndex n} {P : Step1SelectedPoleRecord n k d}
    (hInv : Step1TierInvariant H D w B)
    (hready : Step1ReadyToProcess B.processed (h, .ignition j))
    (hhead : P.firstHead = h) (hchain : P.chain = B.chain h)
    (htier : P.tier = j.toTier) (hexact : P.IsExact D) :
    Step1TierInvariant H D w (step1ProcessIgnition H w B h j P) := by
  rcases hInv with ⟨hchains, hdomains, hrecords, hpoles, hcoherent⟩
  refine ⟨hchains, hdomains, ?_, ?_, ?_⟩
  · constructor
    · exact hrecords.1
    · intro h' j' R hR
      by_cases hh : h' = h
      · subst h'
        by_cases hj : j' = j
        · subst j'
          simp [step1ProcessIgnition] at hR
          cases hR
          rfl
        · simp [step1ProcessIgnition, Function.update, hj] at hR
          exact hrecords.2 h j' R hR
      · simp [step1ProcessIgnition, Function.update, hh] at hR
        exact hrecords.2 h' j' R hR
  · exact step1ProcessIgnition_selectedPolesMatch H w hpoles
      hhead hchain htier hexact
  · constructor
    · exact step1_insert_isProcessingPrefix hcoherent.1 hready
    · intro h' slot
      have hold := hcoherent.2 h' slot
      simp only [step1ProcessIgnition]
      rw [Finset.mem_insert, hold]
      cases slot with
      | ignition j' =>
          by_cases hh : h' = h
          · subst h'
            by_cases hj : j' = j
            · subst j'
              simp
            · have hjtier : j'.toTier ≠ j.toTier := by
                intro heq
                apply hj
                apply Fin.ext
                simpa using congrArg Fin.val heq
              simp [Function.update, hj, hjtier]
          · simp [Function.update, hh]
      | residue i =>
          simp

/-- Processing one ready residue slot preserves the complete strengthened
invariant and leaves all exact pole payloads untouched. -/
theorem step1ProcessResidue_preserves_invariant {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w : Vec d)
    (D : ActiveStratificationData (n + 2) k d)
    {B : Step1TierBookkeeping n k d} {h : Fin k} {i : Fin d}
    (hInv : Step1TierInvariant H D w B)
    (hready : Step1ReadyToProcess B.processed (h, .residue i)) :
    Step1TierInvariant H D w (step1ProcessResidue H w B h i) := by
  rcases hInv with ⟨hchains, hdomains, hrecords, hpoles, hcoherent⟩
  refine ⟨hchains, hdomains, ?_, hpoles, ?_⟩
  · constructor
    · intro h' i' R hR
      by_cases hh : h' = h
      · subst h'
        by_cases hi : i' = i
        · subst i'
          simp [step1ProcessResidue] at hR
          cases hR
          rfl
        · simp [step1ProcessResidue, Function.update, hi] at hR
          exact hrecords.1 h i' R hR
      · simp [step1ProcessResidue, Function.update, hh] at hR
        exact hrecords.1 h' i' R hR
    · exact hrecords.2
  · constructor
    · exact step1_insert_isProcessingPrefix hcoherent.1 hready
    · intro h' slot
      have hold := hcoherent.2 h' slot
      simp only [step1ProcessResidue]
      rw [Finset.mem_insert, hold]
      cases slot with
      | ignition j => simp
      | residue i' =>
          by_cases hh : h' = h
          · subst h'
            by_cases hi : i' = i
            · subst i'; simp
            · simp [Function.update, hi]
          · simp [Function.update, hh]

/-- Reflexive-transitive fold of the two one-slot operators in the declared
processing order.  Ignition constructors must carry an already constructed
exact pole record; thus the fold cannot manufacture or forget analytic data. -/
inductive Step1ProcessingFold {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (D : ActiveStratificationData (n + 2) k d)
    (w : Vec d) : Step1TierBookkeeping n k d → Step1TierBookkeeping n k d → Prop
  | refl (B) : Step1ProcessingFold H D w B B
  | ignition {B B' : Step1TierBookkeeping n k d} {h : Fin k}
      {j : Step1LaterTierIndex n} {P : Step1SelectedPoleRecord n k d}
      (fold : Step1ProcessingFold H D w B B')
      (ready : Step1ReadyToProcess B'.processed (h, .ignition j))
      (head : P.firstHead = h) (chain : P.chain = B'.chain h)
      (tier : P.tier = j.toTier) (exact : P.IsExact D) :
      Step1ProcessingFold H D w B (step1ProcessIgnition H w B' h j P)
  | residue {B B' : Step1TierBookkeeping n k d} {h : Fin k} {i : Fin d}
      (fold : Step1ProcessingFold H D w B B')
      (ready : Step1ReadyToProcess B'.processed (h, .residue i)) :
      Step1ProcessingFold H D w B (step1ProcessResidue H w B' h i)

/-- Finite folding preserves the complete tier invariant at every prefix. -/
theorem Step1ProcessingFold.preserves_invariant {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    {H : Step1StandingHypotheses r theta theta'}
    {D : ActiveStratificationData (n + 2) k d} {w : Vec d}
    {B B' : Step1TierBookkeeping n k d}
    (fold : Step1ProcessingFold H D w B B')
    (hInv : Step1TierInvariant H D w B) :
    Step1TierInvariant H D w B' := by
  induction fold with
  | refl => exact hInv
  | ignition fold ready head chain tier exact ih =>
      exact step1ProcessIgnition_preserves_invariant H w D ih ready head chain tier exact
  | residue fold ready ih =>
      exact step1ProcessResidue_preserves_invariant H w D ih ready

/-- A terminal fold has processed every head/slot. -/
def Step1ProcessingComplete {n k d : Nat} (B : Step1TierBookkeeping n k d) : Prop :=
  B.processed = Finset.univ

/-- A producer for every ready ignition payload closes the entire finite
processing fold.  Residue slots are algebraic state updates, so no additional
producer is needed for them. -/
theorem step1_exists_complete_processingFold_of_ignitionProducer
    {n k d r : Nat} {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta')
    (D : ActiveStratificationData (n + 2) k d) (w : Vec d)
    (B₀ : Step1TierBookkeeping n k d)
    (produce : ∀ (B : Step1TierBookkeeping n k d),
      Step1ProcessingFold H D w B₀ B →
      ∀ (h : Fin k) (j : Step1LaterTierIndex n),
        Step1ReadyToProcess B.processed (h, .ignition j) →
        ∃ P : Step1SelectedPoleRecord n k d,
          P.firstHead = h ∧ P.chain = B.chain h ∧ P.tier = j.toTier ∧ P.IsExact D) :
    ∃ B : Step1TierBookkeeping n k d,
      Step1ProcessingFold H D w B₀ B ∧ Step1ProcessingComplete B := by
  classical
  let rec go (B : Step1TierBookkeeping n k d)
      (fold : Step1ProcessingFold H D w B₀ B) :
      ∃ B' : Step1TierBookkeeping n k d,
        Step1ProcessingFold H D w B₀ B' ∧ Step1ProcessingComplete B' := by
    by_cases hcomplete : B.processed = Finset.univ
    · exact ⟨B, fold, hcomplete⟩
    · rcases step1_exists_ready_of_ne_univ B.processed hcomplete with
        ⟨⟨h, slot⟩, hready⟩
      cases slot with
      | ignition j =>
          rcases produce B fold h j hready with ⟨P, hhead, hchain, htier, hexact⟩
          exact go (step1ProcessIgnition H w B h j P)
            (.ignition fold hready hhead hchain htier hexact)
      | residue i =>
          exact go (step1ProcessResidue H w B h i) (.residue fold hready)
    termination_by (Finset.univ \ B.processed).card
    decreasing_by
      all_goals
        simp only [step1ProcessIgnition, step1ProcessResidue]
        have hnot := hready.1
        simp only [Finset.sdiff_insert]
        apply Finset.card_erase_lt_of_mem
        simp [hnot]
  exact go B₀ (.refl B₀)

/-- At a complete invariant, every ignition slot has a canonical ignition
record and its selected pole payload remains exact. -/
theorem step1_complete_ignition_payload {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    {H : Step1StandingHypotheses r theta theta'}
    {D : ActiveStratificationData (n + 2) k d} {w : Vec d}
    {B : Step1TierBookkeeping n k d}
    (hInv : Step1TierInvariant H D w B) (hcomplete : Step1ProcessingComplete B)
    (h : Fin k) (j : Step1LaterTierIndex n) :
    (∃ R, B.ignition h j = some R ∧ R = step1TargetIgnitionRecord H w h j) ∧
    ∃ P, B.selectedPole h j.toTier = some P ∧ P.firstHead = h ∧
      P.chain = B.chain h ∧ P.tier = j.toTier ∧ P.IsExact D := by
  have hmem : (h, Step1ProcessSlot.ignition j) ∈ B.processed := by
    rw [hcomplete]
    simp
  rcases (hInv.2.2.2.2.2 h (.ignition j)).1 hmem with ⟨⟨R, hR⟩, P, hP⟩
  have hRcanon := hInv.2.2.1.2 h j R hR
  rcases hInv.2.2.2.1 h j.toTier P hP with ⟨hh, hc, ht, he⟩
  exact ⟨⟨R, hR, hRcanon⟩, P, hP, hh, hc, ht, he⟩

end

end TransformerIdentifiability.NLayer.NoSkip
