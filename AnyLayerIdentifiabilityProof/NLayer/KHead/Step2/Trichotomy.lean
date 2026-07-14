set_option autoImplicit false

universe u

namespace TransformerIdentifiability.NLayer.KHead

/-!
# K07B Step 2 trichotomy scaffold

This file records the statement/API surface for the multi-head Step 2 trichotomy.
It deliberately avoids importing the Step 2 dial file: K07B depends on the K07A
dial construction, so the hard analytic claims are exposed only as `Prop`-valued
interfaces and result records.
-/

/-- The three labels used by the trichotomy: `0`, `1`, and `alpha = sig b`. -/
inductive TrichotomyLabel where
  | zero
  | one
  | alpha
  deriving DecidableEq

namespace TrichotomyLabel

/-- Interpret a trichotomy label in any target type. -/
def eval {α : Type u} (zeroValue oneValue alphaValue : α) : TrichotomyLabel → α
  | .zero => zeroValue
  | .one => oneValue
  | .alpha => alphaValue

@[simp]
theorem eval_zero {α : Type u} (zeroValue oneValue alphaValue : α) :
    eval zeroValue oneValue alphaValue TrichotomyLabel.zero = zeroValue :=
  rfl

@[simp]
theorem eval_one {α : Type u} (zeroValue oneValue alphaValue : α) :
    eval zeroValue oneValue alphaValue TrichotomyLabel.one = oneValue :=
  rfl

@[simp]
theorem eval_alpha {α : Type u} (zeroValue oneValue alphaValue : α) :
    eval zeroValue oneValue alphaValue TrichotomyLabel.alpha = alphaValue :=
  rfl

end TrichotomyLabel

/-- A deeper head `(layer, head)`, corresponding to TeX indices `(ell,b)`. -/
structure DeeperHead where
  layer : Nat
  head : Nat
  deriving DecidableEq

/-- Predicate for the deeper-head index range `2 <= ell <= L`, `1 <= b <= k`. -/
def IsDeeperHead (L k : Nat) (h : DeeperHead) : Prop :=
  2 ≤ h.layer ∧ h.layer ≤ L ∧ 1 ≤ h.head ∧ h.head ≤ k

/-- The number `N = (L - 1) k` of deeper heads in the TeX packet. -/
def deeperHeadCount (L k : Nat) : Nat :=
  (L - 1) * k

/-- Lexicographic deeper-head order
`(2,1),...,(2,k),(3,1),...,(L,k)`. -/
def deeperHeadOrder (L k : Nat) : List DeeperHead :=
  (List.range (L - 1)).flatMap fun layerOffset =>
    (List.range k).map fun headOffset =>
      { layer := layerOffset + 2, head := headOffset + 1 }

/-- The lexicographic deeper-head list has the expected cardinality `(L - 1) * k`. -/
theorem deeperHeadOrder_length (L k : Nat) :
    (deeperHeadOrder L k).length = deeperHeadCount L k := by
  simp [deeperHeadOrder, deeperHeadCount, List.map_const']

/-- The lexicographic deeper-head list contains exactly the admissible one-based
deeper-head indices. -/
theorem mem_deeperHeadOrder_iff {L k : Nat} {h : DeeperHead} :
    h ∈ deeperHeadOrder L k ↔ IsDeeperHead L k h := by
  unfold deeperHeadOrder IsDeeperHead
  rw [List.mem_flatMap]
  constructor
  · intro hmem
    rcases hmem with ⟨layerOffset, hlayer, hmap⟩
    rw [List.mem_range] at hlayer
    rw [List.mem_map] at hmap
    rcases hmap with ⟨headOffset, hhead, heq⟩
    rw [List.mem_range] at hhead
    subst h
    constructor
    · simp
    constructor
    · simp; omega
    constructor
    · simp
    · simp; omega
  · intro hdeep
    cases h with
    | mk layer head =>
      simp only at hdeep ⊢
      rcases hdeep with ⟨hlow, hle, hhlo, hhle⟩
      refine ⟨layer - 2, ?_, ?_⟩
      · rw [List.mem_range]
        omega
      · rw [List.mem_map]
        refine ⟨head - 1, ?_, ?_⟩
        · rw [List.mem_range]
          omega
        · congr <;> omega

/-- Direct constructor form of `mem_deeperHeadOrder_iff`, useful for K07C's
zero-based head slots. -/
theorem mk_mem_deeperHeadOrder {L k layer head : Nat}
    (hlow : 2 ≤ layer) (hle : layer ≤ L)
    (hhlo : 1 ≤ head) (hhle : head ≤ k) :
    ({ layer := layer, head := head } : DeeperHead) ∈ deeperHeadOrder L k := by
  exact mem_deeperHeadOrder_iff.mpr ⟨hlow, hle, hhlo, hhle⟩

/-- Membership form used by K07C: Lean layer `n` (`1 ≤ n < m+1`) and
zero-based head `a` correspond to the one-based deeper head `(n+1, a+1)`. -/
theorem succ_head_mem_deeperHeadOrder {m k n : Nat} (hnpos : 1 ≤ n)
    (hn : n < m + 1) (a : Fin k) :
    ({ layer := n + 1, head := (a : Nat) + 1 } : DeeperHead) ∈
      deeperHeadOrder (m + 1) k := by
  apply mk_mem_deeperHeadOrder
  · omega
  · omega
  · omega
  · exact Nat.succ_le_of_lt a.isLt

/-- The processed prefix `P_n` of an explicit deeper-head order. -/
def processedPrefix (order : List DeeperHead) (n : Nat) : List DeeperHead :=
  order.take n

theorem mem_order_of_mem_processedPrefix {order : List DeeperHead} {n : Nat}
    {h : DeeperHead} (hh : h ∈ processedPrefix order n) :
    h ∈ order := by
  exact List.mem_of_mem_take (by simpa [processedPrefix] using hh)

theorem getElem_not_mem_processedPrefix_of_nodup {order : List DeeperHead}
    (hnodup : order.Nodup) {n : Nat} (hn : n < order.length) :
    order[n] ∉ processedPrefix order n := by
  revert n
  induction order with
  | nil =>
      intro n hn
      simp at hn
  | cons head tail ih =>
      intro n hn
      cases n with
      | zero =>
          simp [processedPrefix]
      | succ n =>
          intro hmem
          have hn_tail : n < tail.length := by simpa using Nat.lt_of_succ_lt_succ hn
          have hnodup_tail : tail.Nodup := by
            simpa using hnodup.of_cons
          have hhead_not_mem : head ∉ tail := by
            simpa using (show head ∉ tail ∧ tail.Nodup from by simpa using hnodup).1
          simp [processedPrefix] at hmem
          rcases hmem with hhead | htail
          · exact hhead_not_mem (by
              have hget : tail[n] ∈ tail := List.getElem_mem hn_tail
              simpa [hhead] using hget)
          · exact ih hnodup_tail hn_tail htail

/-- Update one head label while leaving all other labels unchanged. -/
def setLabel (labels : DeeperHead → TrichotomyLabel) (h : DeeperHead)
    (label : TrichotomyLabel) : DeeperHead → TrichotomyLabel :=
  fun g => if g = h then label else labels g

@[simp]
theorem setLabel_self (labels : DeeperHead → TrichotomyLabel) (h : DeeperHead)
    (label : TrichotomyLabel) :
    setLabel labels h label h = label := by
  simp [setLabel]

theorem setLabel_of_ne (labels : DeeperHead → TrichotomyLabel) {h g : DeeperHead}
    (label : TrichotomyLabel) (hne : g ≠ h) :
    setLabel labels h label g = labels g := by
  simp [setLabel, hne]

theorem setLabel_eq_on_processedPrefix_of_not_mem {order : List DeeperHead} {n : Nat}
    (labels : DeeperHead → TrichotomyLabel) {h g : DeeperHead}
    (label : TrichotomyLabel) (hg : g ∈ processedPrefix order n)
    (hh : h ∉ processedPrefix order n) :
    setLabel labels h label g = labels g := by
  exact setLabel_of_ne labels label (by
    intro hgh
    exact hh (hgh ▸ hg))

theorem setLabel_eq_on_processedPrefix_of_getElem_nodup {order : List DeeperHead}
    (hnodup : order.Nodup) (labels : DeeperHead → TrichotomyLabel)
    {n : Nat} (hn : n < order.length) {g : DeeperHead}
    (label : TrichotomyLabel) (hg : g ∈ processedPrefix order n) :
    setLabel labels order[n] label g = labels g :=
  setLabel_eq_on_processedPrefix_of_not_mem labels label hg
    (getElem_not_mem_processedPrefix_of_nodup hnodup hn)

/-- Abstract region/polynomial predicates consumed by the K07B statement layer. -/
structure TrichotomyPredicates (Region Poly : Type u) where
  RegionNonempty : Region → Prop
  RegionConnected : Region → Prop
  RegionRelativelyOpen : Region → Prop
  RegionSubset : Region → Region → Prop
  PositiveOn : Poly → Region → Prop
  NegativeOn : Poly → Region → Prop
  VanishesOn : Poly → Region → Prop
  ZeroPolynomial : Poly → Prop
  Estimate :
    List DeeperHead → Nat → Region → (DeeperHead → TrichotomyLabel) → Prop

/-- The abstract formal slope polynomials `Phi` and their dial evaluations `Lambda`. -/
structure TrichotomyFormalData (Poly : Type u) where
  Phi : DeeperHead → (DeeperHead → TrichotomyLabel) → Poly
  Lambda : DeeperHead → (DeeperHead → TrichotomyLabel) → Poly

/-- Label/sign link from Definition `def-processing-invariant.S`. -/
def LabelSignLink {Region Poly : Type u}
    (P : TrichotomyPredicates Region Poly) (F : TrichotomyFormalData Poly)
    (region : Region) (labels : DeeperHead → TrichotomyLabel)
    (h : DeeperHead) : Prop :=
  match labels h with
  | TrichotomyLabel.zero => P.NegativeOn (F.Lambda h labels) region
  | TrichotomyLabel.one => P.PositiveOn (F.Lambda h labels) region
  | TrichotomyLabel.alpha => P.ZeroPolynomial (F.Phi h labels)

/-- TeX box `def-processing-invariant.S`. -/
structure ProcessingInvariantStatement {Region Poly : Type u}
    (P : TrichotomyPredicates Region Poly) (F : TrichotomyFormalData Poly)
    (baseRegion currentRegion : Region) (order : List DeeperHead) (n : Nat)
    (labels : DeeperHead → TrichotomyLabel) : Prop where
  region_nonempty : P.RegionNonempty currentRegion
  region_connected : P.RegionConnected currentRegion
  region_relativelyOpen : P.RegionRelativelyOpen currentRegion
  region_subset_base : P.RegionSubset currentRegion baseRegion
  label_sign_link :
    ∀ h : DeeperHead,
      h ∈ processedPrefix order n → LabelSignLink P F currentRegion labels h
  estimate : P.Estimate order n currentRegion labels

/-- Stable API alias for TeX box `def-processing-invariant.S`. -/
def def_processing_invariant_S {Region Poly : Type u}
    (P : TrichotomyPredicates Region Poly) (F : TrichotomyFormalData Poly)
    (baseRegion currentRegion : Region) (order : List DeeperHead) (n : Nat)
    (labels : DeeperHead → TrichotomyLabel) : Prop :=
  ProcessingInvariantStatement P F baseRegion currentRegion order n labels

/-- Base case of the processing invariant: no deeper head has been processed yet,
so the label/sign clause is vacuous. -/
theorem processingInvariant_zero {Region Poly : Type u}
    (P : TrichotomyPredicates Region Poly) (F : TrichotomyFormalData Poly)
    (baseRegion : Region) (order : List DeeperHead)
    (labels : DeeperHead → TrichotomyLabel)
    (hNonempty : P.RegionNonempty baseRegion)
    (hConnected : P.RegionConnected baseRegion)
    (hRelOpen : P.RegionRelativelyOpen baseRegion)
    (hSubset : P.RegionSubset baseRegion baseRegion)
    (hEstimate : P.Estimate order 0 baseRegion labels) :
    ProcessingInvariantStatement P F baseRegion baseRegion order 0 labels where
  region_nonempty := hNonempty
  region_connected := hConnected
  region_relativelyOpen := hRelOpen
  region_subset_base := hSubset
  label_sign_link := by
    intro h hh
    simp [processedPrefix] at hh
  estimate := hEstimate

/-- TeX box `lem-zero-branch-rigidity.S`, represented as a proposition interface. -/
def lem_zero_branch_rigidity_S {Region Poly : Type u}
    (P : TrichotomyPredicates Region Poly) (F : TrichotomyFormalData Poly)
    (region : Region) (labels : DeeperHead → TrichotomyLabel)
    (h : DeeperHead) : Prop :=
  P.VanishesOn (F.Lambda h labels) region → P.ZeroPolynomial (F.Phi h labels)

/-- TeX box `lem-zero-branch-error.S`, represented as a proposition interface. -/
def lem_zero_branch_error_S {Region Poly : Type u}
    (P : TrichotomyPredicates Region Poly) (F : TrichotomyFormalData Poly)
    (region : Region) (order : List DeeperHead) (n : Nat)
    (labels : DeeperHead → TrichotomyLabel) (h : DeeperHead) : Prop :=
  P.ZeroPolynomial (F.Phi h labels) →
    P.Estimate order n region labels →
      P.Estimate order (n + 1) region (setLabel labels h TrichotomyLabel.alpha)

/-- Branch tags for one trichotomy step. -/
inductive TrichotomyStepBranch where
  | zero
  | nonzero
  deriving DecidableEq

/-- Result interface for one step of the trichotomy recursion. -/
structure TrichotomyStepResult {Region Poly : Type u}
    (P : TrichotomyPredicates Region Poly) (F : TrichotomyFormalData Poly)
    (baseRegion currentRegion : Region) (order : List DeeperHead) (n : Nat)
    (labels : DeeperHead → TrichotomyLabel) (h : DeeperHead) where
  branch : TrichotomyStepBranch
  nextRegion : Region
  nextLabels : DeeperHead → TrichotomyLabel
  nextRegion_subset_current : P.RegionSubset nextRegion currentRegion
  processed_label : nextLabels h = TrichotomyLabel.zero ∨
    nextLabels h = TrichotomyLabel.one ∨ nextLabels h = TrichotomyLabel.alpha
  next_invariant :
    ProcessingInvariantStatement P F baseRegion nextRegion order (n + 1) nextLabels

/-- TeX box `lem-trichotomy-step.S`, represented as a proposition interface. -/
def lem_trichotomy_step_S {Region Poly : Type u}
    (P : TrichotomyPredicates Region Poly) (F : TrichotomyFormalData Poly)
    (baseRegion currentRegion : Region) (order : List DeeperHead) (n : Nat)
    (labels : DeeperHead → TrichotomyLabel) (h : DeeperHead) : Prop :=
  ProcessingInvariantStatement P F baseRegion currentRegion order n labels →
    ∃ _result :
      TrichotomyStepResult P F baseRegion currentRegion order n labels h,
      True

/-- Final result interface for Proposition `prop-trichotomy.S`. -/
structure TrichotomyResult {Region Poly : Type u}
    (P : TrichotomyPredicates Region Poly) (F : TrichotomyFormalData Poly)
    (baseRegion : Region) (order : List DeeperHead) where
  Ustar : Region
  labels : DeeperHead → TrichotomyLabel
  region_nonempty : P.RegionNonempty Ustar
  region_connected : P.RegionConnected Ustar
  region_relativelyOpen : P.RegionRelativelyOpen Ustar
  region_subset_base : P.RegionSubset Ustar baseRegion
  label_sign_link :
    ∀ h : DeeperHead, h ∈ order → LabelSignLink P F Ustar labels h
  estimate : P.Estimate order order.length Ustar labels

/-- TeX box `prop-trichotomy.S`, represented as a proposition interface. -/
def prop_trichotomy_S {Region Poly : Type u}
    (P : TrichotomyPredicates Region Poly) (F : TrichotomyFormalData Poly)
    (baseRegion : Region) (order : List DeeperHead) : Prop :=
  ∃ _result : TrichotomyResult P F baseRegion order, True

private theorem trichotomy_fold_aux {Region Poly : Type u}
    (P : TrichotomyPredicates Region Poly) (F : TrichotomyFormalData Poly)
    (baseRegion : Region) (order remaining : List DeeperHead) (n : Nat)
    (currentRegion : Region) (labels : DeeperHead → TrichotomyLabel)
    (hInv : ProcessingInvariantStatement P F baseRegion currentRegion order n labels)
    (hstep :
      ∀ (currentRegion : Region) (n : Nat) (labels : DeeperHead → TrichotomyLabel)
        (h : DeeperHead),
        lem_trichotomy_step_S P F baseRegion currentRegion order n labels h) :
    ∃ (finalRegion : Region) (finalLabels : DeeperHead → TrichotomyLabel),
      ProcessingInvariantStatement P F baseRegion finalRegion order (n + remaining.length)
        finalLabels := by
  induction remaining generalizing n currentRegion labels with
  | nil =>
      exact ⟨currentRegion, labels, by simpa using hInv⟩
  | cons h tail ih =>
      rcases hstep currentRegion n labels h hInv with ⟨stepResult, _⟩
      rcases ih (n := n + 1) (currentRegion := stepResult.nextRegion)
          (labels := stepResult.nextLabels) stepResult.next_invariant with
        ⟨finalRegion, finalLabels, hFinal⟩
      refine ⟨finalRegion, finalLabels, ?_⟩
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hFinal

/-- Fold a proved one-step trichotomy over the finite deeper-head order.

This is the formal recursion bookkeeping for TeX `prop:trichotomy`: once the
base invariant and the per-head step are available, the final region, labels,
label/sign links, and estimate are assembled without additional analytic input. -/
theorem prop_trichotomy_of_initial_and_step {Region Poly : Type u}
    (P : TrichotomyPredicates Region Poly) (F : TrichotomyFormalData Poly)
    (baseRegion : Region) (order : List DeeperHead)
    (initialLabels : DeeperHead → TrichotomyLabel)
    (hinit :
      ProcessingInvariantStatement P F baseRegion baseRegion order 0 initialLabels)
    (hstep :
      ∀ (currentRegion : Region) (n : Nat) (labels : DeeperHead → TrichotomyLabel)
        (h : DeeperHead),
        lem_trichotomy_step_S P F baseRegion currentRegion order n labels h) :
    prop_trichotomy_S P F baseRegion order := by
  rcases trichotomy_fold_aux P F baseRegion order order 0 baseRegion initialLabels hinit hstep with
    ⟨Ustar, labels, hFinalRaw⟩
  have hFinal :
      ProcessingInvariantStatement P F baseRegion Ustar order order.length labels := by
    simpa using hFinalRaw
  refine ⟨?_, trivial⟩
  exact
    { Ustar := Ustar
      labels := labels
      region_nonempty := hFinal.region_nonempty
      region_connected := hFinal.region_connected
      region_relativelyOpen := hFinal.region_relativelyOpen
      region_subset_base := hFinal.region_subset_base
      label_sign_link := by
        intro h hh
        exact hFinal.label_sign_link h (by simpa [processedPrefix] using hh)
      estimate := hFinal.estimate }

end TransformerIdentifiability.NLayer.KHead
