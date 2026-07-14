import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.FormalPolySplit

set_option autoImplicit false

open Filter Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.KHead

/-! ## `lem:multi-affine` -/

/-- Result interface for **K04E lem-multi-affine**. -/
structure MultiAffineResult {L k d : Nat} (θ : Params L k d) (w v : Vec d) : Prop where
  formalW_blockMultiAffine :
    ∀ (n : Nat) (hn : n ≤ L) (i : Fin d), BlockMultiAffine (formalW θ w v n hn i)
  formalV_blockMultiAffine :
    ∀ (n : Nat) (hn : n ≤ L) (i : Fin d), BlockMultiAffine (formalV θ w v n hn i)
  formalSlope_blockDegree_two :
    ∀ (l : Fin L) (a : Fin k), BlockDegreeLE 2 (formalSlope θ w v l a)

/-- **K04E.E.lem-multi-affine.S/P**.

Formal-stream proof of block multi-affinity and the slope block-degree bound. -/
theorem lem_multi_affine {L k d : Nat} {θ : Params L k d} {w v : Vec d} :
    MultiAffineResult θ w v where
  formalW_blockMultiAffine := formalW_blockMultiAffine θ w v
  formalV_blockMultiAffine := formalV_blockMultiAffine θ w v
  formalSlope_blockDegree_two := formalSlope_blockDegree_two θ w v

/-! ## `lem:selected-top` -/

/-- Remove all variables above layer `n` from an exponent vector. -/
noncomputable def truncateExponentLayersLE {L k : Nat} (n : Nat)
    (m : FormalVar L k →₀ Nat) : FormalVar L k →₀ Nat :=
  Finsupp.onFinset m.support (fun x => if x.1.1 ≤ n then m x else 0) (by
    intro x hx
    by_cases hxle : x.1.1 ≤ n
    · exact Finsupp.mem_support_iff.mpr (by simpa [hxle] using hx)
    · simp [hxle] at hx)

@[simp] theorem truncateExponentLayersLE_apply {L k : Nat} (n : Nat)
    (m : FormalVar L k →₀ Nat) (x : FormalVar L k) :
    truncateExponentLayersLE n m x = if x.1.1 ≤ n then m x else 0 := by
  simp [truncateExponentLayersLE]

theorem truncateExponentLayersLE_supported {L k : Nat} (n : Nat)
    (m : FormalVar L k →₀ Nat) :
    SupportedInLayersLE (L := L) (k := k) n (truncateExponentLayersLE n m) := by
  intro x hx
  simp [Nat.not_le_of_gt hx]

/-- Target exponent of a variable in a selected tail block.  Selected variables get
`deg`; all nonselected variables in the same layer range get exponent zero. -/
noncomputable def selectedTailTarget {L k p : Nat} (c : HeadChain L k p)
    (deg : Nat) (x : FormalVar L k) : Nat := by
  classical
  exact if c.IsSelectedVar x then deg else 0

/-- A monomial has the selected-tail exponent pattern on layers `i ≤ layer < n`. -/
def SelectedTailMatches {L k p : Nat} (c : HeadChain L k p)
    (i n deg : Nat) (m : FormalVar L k →₀ Nat) : Prop :=
  ∀ x : FormalVar L k, i ≤ x.1.1 -> x.1.1 < n ->
    m x = selectedTailTarget c deg x

/-- Coefficient extraction for a selected chain tail.  It keeps exactly the
monomials whose variables in layers `i ≤ layer < n` match the selected tail with
degree `deg`, and then forgets all variables above layer `i`. -/
noncomputable def selectedTailCoeff {L k p : Nat} (c : HeadChain L k p)
    (i n deg : Nat) (f : FormalPoly L k) : FormalPoly L k := by
  classical
  exact ∑ m ∈ f.support,
    if SelectedTailMatches c i n deg m then
      MvPolynomial.monomial (truncateExponentLayersLE i m) (f.coeff m)
    else 0

theorem selectedTailCoeff_polynomialInLayersLE {L k p : Nat}
    (c : HeadChain L k p) (i n deg : Nat) (f : FormalPoly L k) :
    PolynomialInLayersLE (L := L) (k := k) i (selectedTailCoeff c i n deg f) := by
  classical
  unfold selectedTailCoeff
  refine PolynomialInLayersLE.sum (s := f.support) ?_
  intro m hm
  by_cases hmatch : SelectedTailMatches c i n deg m
  · simpa [hmatch] using
      (PolynomialInLayersLE.monomial
        (truncateExponentLayersLE_supported (L := L) (k := k) i m)
        (a := f.coeff m))
  · simpa [hmatch] using
      (PolynomialInLayersLE.zero (L := L) (k := k) (n := i))

/-- Selected-tail coefficient of the `w_n` stream coordinate vector. -/
noncomputable def selectedTopStreamCoeff {L k d p : Nat} (θ : Params L k d)
    (w v : Vec d) (c : HeadChain L k p)
    (i n : Nat) (_hin : i ≤ n) (hn : n ≤ p) : FormalVec L k d :=
  fun r => selectedTailCoeff c i n 1
    (formalW θ w v n (Nat.le_trans hn c.length_le) r)

/-- Full selected quadratic-tail coefficient of a slope at a chain layer. -/
noncomputable def selectedTopSlopeQuadraticCoeff {L k d p : Nat}
    (θ : Params L k d) (w v : Vec d) (c : HeadChain L k p)
    (j : Fin p) (a : Fin k) : FormalPoly L k :=
  selectedTailCoeff c 0 j.1 2 (formalSlope θ w v (c.layer j) a)

/-- Full selected-tail coefficient of the terminal `w_p` stream. -/
noncomputable def selectedTopTerminalCoeff {L k d p : Nat} (θ : Params L k d)
    (w v : Vec d) (c : HeadChain L k p) (r : Fin d) : FormalPoly L k :=
  selectedTailCoeff c 0 p 1 (formalW θ w v p c.length_le r)

/-- The selected top-coefficient data appearing along one chain. -/
structure SelectedTopData {L k d p : Nat} (θ : Params L k d)
    (w v : Vec d) (c : HeadChain L k p) where
  /-- The formal selected stream coefficient vectors. -/
  streamCoeff : (i n : Nat) -> i ≤ n -> n ≤ p -> FormalVec L k d
  /-- The formal selected quadratic slope-top coefficients. -/
  slopeQuadraticCoeff : (j : Fin p) -> Fin k -> FormalPoly L k
  /-- The selected coordinate functions from the last chain value matrix. -/
  terminalCoordCoeff : Fin d -> FormalPoly L k

/-- Canonical selected-top data extracted from the formal stream and slope
polynomials. -/
noncomputable def selectedTopData {L k d p : Nat} (θ : Params L k d)
    (w v : Vec d) (c : HeadChain L k p) : SelectedTopData θ w v c where
  streamCoeff := selectedTopStreamCoeff θ w v c
  slopeQuadraticCoeff := selectedTopSlopeQuadraticCoeff θ w v c
  terminalCoordCoeff := selectedTopTerminalCoeff θ w v c

/-- Result interface for **K04E lem-selected-top**.  The coefficient data is tied
to concrete selected-tail coefficient extractions from the formal stream and
slope polynomials, and the extracted coefficients carry layer-support facts. -/
structure SelectedTopResult {L k d p : Nat} (θ : Params L k d)
    (w v : Vec d) (c : HeadChain L k p) : Prop where
  coefficient_data :
    ∃ data : SelectedTopData θ w v c,
      (∀ (i n : Nat) (hin : i ≤ n) (hn : n ≤ p),
        data.streamCoeff i n hin hn = selectedTopStreamCoeff θ w v c i n hin hn) ∧
      (∀ (j : Fin p) (a : Fin k),
        data.slopeQuadraticCoeff j a = selectedTopSlopeQuadraticCoeff θ w v c j a) ∧
      (∀ r : Fin d,
        data.terminalCoordCoeff r = selectedTopTerminalCoeff θ w v c r) ∧
      (∀ (i n : Nat) (hin : i ≤ n) (hn : n ≤ p) (r : Fin d),
        PolynomialInLayersLE i (data.streamCoeff i n hin hn r)) ∧
      (∀ (j : Fin p) (a : Fin k),
        PolynomialInLayersLE j.1 (data.slopeQuadraticCoeff j a)) ∧
      (∀ r : Fin d, PolynomialInLayersLE p (data.terminalCoordCoeff r))
  formal_stream_support :
    ∀ (n : Nat) (hn : n ≤ p) (r : Fin d),
      PolynomialInLayersLE n (formalW θ w v n (Nat.le_trans hn c.length_le) r)
  formal_slope_support :
    ∀ (j : Fin p) (a : Fin k),
      PolynomialInLayersLE j.1 (formalSlope θ w v (c.layer j) a)
  formal_slope_blockDegree_two :
    ∀ (j : Fin p) (a : Fin k),
      BlockDegreeLE 2 (formalSlope θ w v (c.layer j) a)

theorem selectedTop_coefficient_data {L k d p : Nat} (θ : Params L k d)
    (w v : Vec d) (c : HeadChain L k p) :
    ∃ data : SelectedTopData θ w v c,
      (∀ (i n : Nat) (hin : i ≤ n) (hn : n ≤ p),
        data.streamCoeff i n hin hn = selectedTopStreamCoeff θ w v c i n hin hn) ∧
      (∀ (j : Fin p) (a : Fin k),
        data.slopeQuadraticCoeff j a = selectedTopSlopeQuadraticCoeff θ w v c j a) ∧
      (∀ r : Fin d,
        data.terminalCoordCoeff r = selectedTopTerminalCoeff θ w v c r) ∧
      (∀ (i n : Nat) (hin : i ≤ n) (hn : n ≤ p) (r : Fin d),
        PolynomialInLayersLE i (data.streamCoeff i n hin hn r)) ∧
      (∀ (j : Fin p) (a : Fin k),
        PolynomialInLayersLE j.1 (data.slopeQuadraticCoeff j a)) ∧
      (∀ r : Fin d, PolynomialInLayersLE p (data.terminalCoordCoeff r)) := by
  refine ⟨selectedTopData θ w v c, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i n hin hn
    rfl
  · intro j a
    rfl
  · intro r
    rfl
  · intro i n hin hn r
    exact selectedTailCoeff_polynomialInLayersLE c i n 1
      (formalW θ w v n (Nat.le_trans hn c.length_le) r)
  · intro j a
    exact PolynomialInLayersLE.mono (Nat.zero_le j.1)
      (selectedTailCoeff_polynomialInLayersLE c 0 j.1 2
        (formalSlope θ w v (c.layer j) a))
  · intro r
    exact PolynomialInLayersLE.mono (Nat.zero_le p)
      (selectedTailCoeff_polynomialInLayersLE c 0 p 1
        (formalW θ w v p c.length_le r))

theorem selectedTop_formalStream_support {L k d p : Nat} (θ : Params L k d)
    (w v : Vec d) (c : HeadChain L k p) :
    ∀ (n : Nat) (hn : n ≤ p) (r : Fin d),
      PolynomialInLayersLE n (formalW θ w v n (Nat.le_trans hn c.length_le) r) := by
  intro n hn r
  exact PolynomialInLayersLT.to_LE
    (((formalPoint_layerBoundedBlockAffine θ w v n
      (Nat.le_trans hn c.length_le)).1 r).support_lt)

theorem selectedTop_formalSlope_support {L k d p : Nat} (θ : Params L k d)
    (w v : Vec d) (c : HeadChain L k p) :
    ∀ (j : Fin p) (a : Fin k),
      PolynomialInLayersLE j.1 (formalSlope θ w v (c.layer j) a) := by
  intro j a
  simpa [HeadChain.layer] using
    (PolynomialInLayersLT.to_LE
      (formalSlope_polynomialInLayersLT θ w v (c.layer j) a))

/-- **K04E.E.lem-selected-top.S/P**.

Concrete selected-tail coefficient/support theorem for the selected-top
interface. -/
theorem lem_selected_top {L k d p : Nat} {θ : Params L k d} {w v : Vec d}
    {c : HeadChain L k p} : SelectedTopResult θ w v c where
  coefficient_data := selectedTop_coefficient_data θ w v c
  formal_stream_support := selectedTop_formalStream_support θ w v c
  formal_slope_support := selectedTop_formalSlope_support θ w v c
  formal_slope_blockDegree_two := fun j a => formalSlope_blockDegree_two θ w v (c.layer j) a

/-! ## `lem:tower-dominance` -/

/-- Iterated selected-leading coefficient data for a dominance tower. -/
structure DominanceTowerData {L k p : Nat} (c : HeadChain L k p)
    (f : FormalPoly L k) where
  degree : Fin p -> Nat
  leadingCoeff : (i : Nat) -> i ≤ p -> FormalPoly L k
  lowerCoeff : (i : Fin p) -> Fin (degree i) -> FormalPoly L k
  topConstant : ℝ

/-- A pointwise gate assignment satisfies all selected-variable largeness
thresholds of a dominance tower. -/
def SatisfiesTowerThresholds {L k p : Nat} (c : HeadChain L k p)
    (threshold : (i : Fin p) -> (FormalVar L k -> ℂ) -> ℝ) (z : FormalVar L k -> ℂ) :
    Prop :=
  ∀ i : Fin p, ‖(threshold i z : ℂ)‖ ≤ ‖z (c.selectedVar i)‖

/-- Product of the selected-variable norms already exposed before stage `i`. -/
noncomputable def towerPriorNormProduct {L k p : Nat} (c : HeadChain L k p)
    (degree : Fin p -> Nat) (i : Nat) (z : FormalVar L k -> ℂ) : ℝ :=
  ∏ j ∈ (Finset.univ.filter (fun j : Fin p => j.1 < i)),
    ‖z (c.selectedVar j)‖ ^ degree j

/-- Sum of lower-coefficient magnitudes in the one-variable presentation at stage `i`. -/
noncomputable def towerLowerNormSum {L k p : Nat} {c : HeadChain L k p}
    {f : FormalPoly L k} (data : DominanceTowerData c f)
    (i : Fin p) (z : FormalVar L k -> ℂ) : ℝ :=
  ∑ s : Fin (data.degree i),
    ‖evalFormalPolyComplex z (data.lowerCoeff i s)‖

/-- The concrete continuous largeness threshold used by the proved dominance core.

The denominator uses `max 1` of the prior selected-product.  On threshold-satisfying
points the prior selected variables have norm at least `1`, so this agrees with the
usual tower denominator during the dominance induction, while remaining globally
continuous as a function of all gate variables. -/
noncomputable def dominanceTowerThreshold {L k p : Nat} {c : HeadChain L k p}
    {f : FormalPoly L k} (data : DominanceTowerData c f)
    (i : Fin p) (z : FormalVar L k -> ℂ) : ℝ :=
  1 +
    ((2 : ℝ) ^ (i.1 + 1) * towerLowerNormSum data i z) /
      (‖(data.topConstant : ℂ)‖ *
        max 1 (towerPriorNormProduct c data.degree i.1 z))

/-- The selected monomial factor accumulated through the first `i` tower stages. -/
noncomputable def towerSelectedMonomial {L k p : Nat} (c : HeadChain L k p)
    (degree : Fin p -> Nat) (i : Nat) (z : FormalVar L k -> ℂ) : ℂ :=
  ∏ j ∈ (Finset.univ.filter (fun j : Fin p => j.1 < i)),
    z (c.selectedVar j) ^ degree j

/-- Recursive one-variable decomposition of the tower at complex evaluation points. -/
def DominanceTowerEvalRecurrence {L k p : Nat} {c : HeadChain L k p}
    {f : FormalPoly L k} (data : DominanceTowerData c f) : Prop :=
  ∀ (i : Fin p) (z : FormalVar L k -> ℂ),
    evalFormalPolyComplex z (data.leadingCoeff (i.1 + 1) (Nat.succ_le_of_lt i.2)) =
      evalFormalPolyComplex z (data.leadingCoeff i.1 (Nat.le_of_lt i.2)) *
          z (c.selectedVar i) ^ data.degree i +
        ∑ s : Fin (data.degree i),
          evalFormalPolyComplex z (data.lowerCoeff i s) *
            z (c.selectedVar i) ^ (s : Nat)

/-- The top selected coefficient is the advertised nonzero constant. -/
def DominanceTowerTopConstant {L k p : Nat} {c : HeadChain L k p}
    {f : FormalPoly L k} (data : DominanceTowerData c f) : Prop :=
  ∀ z : FormalVar L k -> ℂ,
    evalFormalPolyComplex z (data.leadingCoeff 0 (Nat.zero_le p)) =
      (data.topConstant : ℂ)

/-- The last leading coefficient is the original polynomial. -/
def DominanceTowerFinalCoeff {L k p : Nat} {c : HeadChain L k p}
    {f : FormalPoly L k} (data : DominanceTowerData c f) : Prop :=
  data.leadingCoeff p le_rfl = f

/-- `eval₂` is continuous as a function of the complex coordinate assignment. -/
theorem continuous_evalFormalPolyComplex {L k : Nat} (f : FormalPoly L k) :
    Continuous fun z : FormalVar L k -> ℂ => evalFormalPolyComplex z f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
      simpa [evalFormalPolyComplex] using
        (continuous_const : Continuous fun _ : FormalVar L k -> ℂ => (a : ℂ))
  | add p q hp hq =>
      simpa [evalFormalPolyComplex] using hp.add hq
  | mul_X p x hp =>
      simpa [evalFormalPolyComplex] using hp.mul (continuous_apply x)

theorem continuous_towerPriorNormProduct {L k p : Nat}
    (c : HeadChain L k p) (degree : Fin p -> Nat) (i : Nat) :
    Continuous fun z : FormalVar L k -> ℂ =>
      towerPriorNormProduct c degree i z := by
  classical
  unfold towerPriorNormProduct
  exact continuous_finsetProd _ fun j _ =>
    ((continuous_apply (c.selectedVar j) :
      Continuous fun z : FormalVar L k -> ℂ => z (c.selectedVar j)).norm.pow (degree j))

theorem continuous_towerLowerNormSum {L k p : Nat} {c : HeadChain L k p}
    {f : FormalPoly L k} (data : DominanceTowerData c f) (i : Fin p) :
    Continuous fun z : FormalVar L k -> ℂ => towerLowerNormSum data i z := by
  classical
  unfold towerLowerNormSum
  exact continuous_finsetSum _ fun s _ =>
    (continuous_evalFormalPolyComplex (data.lowerCoeff i s)).norm

theorem continuous_dominanceTowerThreshold {L k p : Nat} {c : HeadChain L k p}
    {f : FormalPoly L k} (data : DominanceTowerData c f) (hconst : data.topConstant ≠ 0)
    (i : Fin p) :
    Continuous (dominanceTowerThreshold data i) := by
  classical
  have hnum : Continuous fun z : FormalVar L k -> ℂ =>
      (2 : ℝ) ^ (i.1 + 1) * towerLowerNormSum data i z :=
    continuous_const.mul (continuous_towerLowerNormSum data i)
  have hprod : Continuous fun z : FormalVar L k -> ℂ =>
      towerPriorNormProduct c data.degree i.1 z :=
    continuous_towerPriorNormProduct c data.degree i.1
  have hden : Continuous fun z : FormalVar L k -> ℂ =>
      ‖(data.topConstant : ℂ)‖ *
        max 1 (towerPriorNormProduct c data.degree i.1 z) :=
    continuous_const.mul (continuous_const.max hprod)
  have hden_ne : ∀ z : FormalVar L k -> ℂ,
      ‖(data.topConstant : ℂ)‖ *
          max 1 (towerPriorNormProduct c data.degree i.1 z) ≠ 0 := by
    intro z
    have hconst_pos : 0 < ‖(data.topConstant : ℂ)‖ := by
      exact norm_pos_iff.mpr (by exact_mod_cast hconst)
    have hmax_pos : 0 < max 1 (towerPriorNormProduct c data.degree i.1 z) :=
      lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    exact mul_ne_zero hconst_pos.ne' hmax_pos.ne'
  change Continuous fun z : FormalVar L k -> ℂ =>
    1 + ((2 : ℝ) ^ (i.1 + 1) * towerLowerNormSum data i z) /
      (‖(data.topConstant : ℂ)‖ *
        max 1 (towerPriorNormProduct c data.degree i.1 z))
  exact continuous_const.add (hnum.div hden hden_ne)

theorem towerPriorNormProduct_nonneg {L k p : Nat} (c : HeadChain L k p)
    (degree : Fin p -> Nat) (i : Nat) (z : FormalVar L k -> ℂ) :
    0 ≤ towerPriorNormProduct c degree i z := by
  classical
  unfold towerPriorNormProduct
  exact Finset.prod_nonneg fun j _ => pow_nonneg (norm_nonneg _) _

theorem towerLowerNormSum_nonneg {L k p : Nat} {c : HeadChain L k p}
    {f : FormalPoly L k} (data : DominanceTowerData c f)
    (i : Fin p) (z : FormalVar L k -> ℂ) :
    0 ≤ towerLowerNormSum data i z := by
  classical
  unfold towerLowerNormSum
  exact Finset.sum_nonneg fun s _ => norm_nonneg _

theorem towerPriorNormProduct_eq_one_of_zero {L k p : Nat}
    (c : HeadChain L k p) (degree : Fin p -> Nat) (z : FormalVar L k -> ℂ) :
    towerPriorNormProduct c degree 0 z = 1 := by
  classical
  simp [towerPriorNormProduct]

theorem towerPriorNormProduct_succ {L k p : Nat} (c : HeadChain L k p)
    (degree : Fin p -> Nat) (i : Fin p) (z : FormalVar L k -> ℂ) :
    towerPriorNormProduct c degree (i.1 + 1) z =
      towerPriorNormProduct c degree i.1 z *
        ‖z (c.selectedVar i)‖ ^ degree i := by
  classical
  unfold towerPriorNormProduct
  have hfilter :
      (Finset.univ.filter (fun j : Fin p => j.1 < i.1 + 1)) =
        insert i (Finset.univ.filter (fun j : Fin p => j.1 < i.1)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hj
      have hle : j.1 ≤ i.1 := Nat.le_of_lt_succ hj
      rcases Nat.lt_or_eq_of_le hle with hlt | heq
      · exact Or.inr hlt
      · exact Or.inl (Fin.ext heq)
    · intro hj
      rcases hj with hji | hlt
      · subst j
        exact Nat.lt_succ_self i.1
      · exact Nat.lt_trans hlt (Nat.lt_succ_self i.1)
  have hnotmem : i ∉ Finset.univ.filter (fun j : Fin p => j.1 < i.1) := by
    simp
  rw [hfilter, Finset.prod_insert hnotmem]
  ring

theorem real_threshold_le_selected_norm_of_satisfies {L k p : Nat}
    {c : HeadChain L k p}
    {threshold : (i : Fin p) -> (FormalVar L k -> ℂ) -> ℝ}
    {z : FormalVar L k -> ℂ} (hz : SatisfiesTowerThresholds c threshold z)
    {i : Fin p} (hthreshold_nonneg : 0 ≤ threshold i z) :
    threshold i z ≤ ‖z (c.selectedVar i)‖ := by
  have hnorm : ‖((threshold i z : ℝ) : ℂ)‖ = threshold i z := by
    simp [abs_of_nonneg hthreshold_nonneg]
  rw [← hnorm]
  exact hz i

theorem towerPriorNormProduct_ge_one_of_thresholds {L k p : Nat}
    (c : HeadChain L k p) (degree : Fin p -> Nat)
    (threshold : (i : Fin p) -> (FormalVar L k -> ℂ) -> ℝ)
    (hthreshold_one : ∀ i z, 1 ≤ threshold i z)
    {z : FormalVar L k -> ℂ} (hz : SatisfiesTowerThresholds c threshold z) :
    ∀ i : Nat, 1 ≤ towerPriorNormProduct c degree i z := by
  classical
  intro i
  induction i with
  | zero =>
      simp [towerPriorNormProduct]
  | succ i ih =>
      by_cases hi : i < p
      · let j : Fin p := ⟨i, hi⟩
        have hprod_succ :
            towerPriorNormProduct c degree (i + 1) z =
              towerPriorNormProduct c degree i z *
                ‖z (c.selectedVar j)‖ ^ degree j := by
          simpa [j] using towerPriorNormProduct_succ c degree j z
        have hzeta_ge_one : 1 ≤ ‖z (c.selectedVar j)‖ := by
          have hthr_le_norm := hz j
          have hthr_one := hthreshold_one j z
          exact hthr_one.trans
            (real_threshold_le_selected_norm_of_satisfies hz
              (le_trans zero_le_one hthr_one))
        have hpow_ge_one : 1 ≤ ‖z (c.selectedVar j)‖ ^ degree j :=
          one_le_pow₀ hzeta_ge_one
        rw [hprod_succ]
        nlinarith [mul_le_mul ih hpow_ge_one (by positivity) (by positivity)]
      · unfold towerPriorNormProduct
        exact Finset.one_le_prod fun j _hj =>
          one_le_pow₀
            ((hthreshold_one j z).trans
              (real_threshold_le_selected_norm_of_satisfies hz
                (le_trans zero_le_one (hthreshold_one j z))))

theorem towerThreshold_ge_one {L k p : Nat} {c : HeadChain L k p}
    {f : FormalPoly L k} (data : DominanceTowerData c f) (hconst : data.topConstant ≠ 0)
    (i : Fin p) (z : FormalVar L k -> ℂ) :
    1 ≤ dominanceTowerThreshold data i z := by
  classical
  have hconst_pos : 0 < ‖(data.topConstant : ℂ)‖ := by
    exact norm_pos_iff.mpr (by exact_mod_cast hconst)
  have hmax_pos : 0 < max 1 (towerPriorNormProduct c data.degree i.1 z) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hden_pos :
      0 < ‖(data.topConstant : ℂ)‖ *
        max 1 (towerPriorNormProduct c data.degree i.1 z) :=
    mul_pos hconst_pos hmax_pos
  have hnum_nonneg :
      0 ≤ (2 : ℝ) ^ (i.1 + 1) * towerLowerNormSum data i z :=
    mul_nonneg (by positivity) (towerLowerNormSum_nonneg data i z)
  unfold dominanceTowerThreshold
  exact le_add_of_nonneg_right (div_nonneg hnum_nonneg hden_pos.le)

theorem tower_lower_tail_norm_le {L k p : Nat} {c : HeadChain L k p}
    {f : FormalPoly L k} (data : DominanceTowerData c f)
    (i : Fin p)
    {z : FormalVar L k -> ℂ}
    (hzeta_ge_one : 1 ≤ ‖z (c.selectedVar i)‖) :
    ‖∑ s : Fin (data.degree i),
        evalFormalPolyComplex z (data.lowerCoeff i s) *
          z (c.selectedVar i) ^ (s : Nat)‖ ≤
      towerLowerNormSum data i z *
        ‖z (c.selectedVar i)‖ ^ (data.degree i - 1) := by
  classical
  calc
    ‖∑ s : Fin (data.degree i),
        evalFormalPolyComplex z (data.lowerCoeff i s) *
          z (c.selectedVar i) ^ (s : Nat)‖
        ≤ ∑ s : Fin (data.degree i),
            ‖evalFormalPolyComplex z (data.lowerCoeff i s) *
              z (c.selectedVar i) ^ (s : Nat)‖ := norm_sum_le _ _
    _ = ∑ s : Fin (data.degree i),
            ‖evalFormalPolyComplex z (data.lowerCoeff i s)‖ *
              ‖z (c.selectedVar i)‖ ^ (s : Nat) := by
          simp [norm_pow]
    _ ≤ ∑ s : Fin (data.degree i),
            ‖evalFormalPolyComplex z (data.lowerCoeff i s)‖ *
              ‖z (c.selectedVar i)‖ ^ (data.degree i - 1) := by
          refine Finset.sum_le_sum ?_
          intro s _hs
          have hs_le : (s : Nat) ≤ data.degree i - 1 := by
            omega
          have hpow :
              ‖z (c.selectedVar i)‖ ^ (s : Nat) ≤
                ‖z (c.selectedVar i)‖ ^ (data.degree i - 1) :=
            pow_le_pow_right₀ hzeta_ge_one hs_le
          exact mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
    _ = towerLowerNormSum data i z *
          ‖z (c.selectedVar i)‖ ^ (data.degree i - 1) := by
          simp [towerLowerNormSum, Finset.sum_mul]

theorem tower_lower_scaled_le {L k p : Nat} {c : HeadChain L k p}
    {f : FormalPoly L k} (data : DominanceTowerData c f)
    (hdeg : ∀ i : Fin p, 1 ≤ data.degree i)
    (hconst : data.topConstant ≠ 0) (i : Fin p)
    {z : FormalVar L k -> ℂ}
    (hprior_ge_one : 1 ≤ towerPriorNormProduct c data.degree i.1 z)
    (hlarge : dominanceTowerThreshold data i z ≤ ‖z (c.selectedVar i)‖) :
    towerLowerNormSum data i z *
        ‖z (c.selectedVar i)‖ ^ (data.degree i - 1) ≤
      ((1 / ((2 : ℝ) ^ (i.1 + 1))) *
        ‖(data.topConstant : ℂ)‖ *
          towerPriorNormProduct c data.degree i.1 z) *
        ‖z (c.selectedVar i)‖ ^ data.degree i := by
  classical
  have hconst_pos : 0 < ‖(data.topConstant : ℂ)‖ := by
    exact norm_pos_iff.mpr (by exact_mod_cast hconst)
  have hmax_eq :
      max 1 (towerPriorNormProduct c data.degree i.1 z) =
        towerPriorNormProduct c data.degree i.1 z := by
    exact max_eq_right hprior_ge_one
  have hden_pos :
      0 < ‖(data.topConstant : ℂ)‖ *
          towerPriorNormProduct c data.degree i.1 z :=
    mul_pos hconst_pos (lt_of_lt_of_le zero_lt_one hprior_ge_one)
  have htwo_pos : 0 < (2 : ℝ) ^ (i.1 + 1) := by positivity
  have hterm_le_threshold :
      ((2 : ℝ) ^ (i.1 + 1) * towerLowerNormSum data i z) /
          (‖(data.topConstant : ℂ)‖ *
            towerPriorNormProduct c data.degree i.1 z) ≤
        dominanceTowerThreshold data i z := by
    unfold dominanceTowerThreshold
    rw [hmax_eq]
    linarith
  have hterm_le_norm :
      ((2 : ℝ) ^ (i.1 + 1) * towerLowerNormSum data i z) /
          (‖(data.topConstant : ℂ)‖ *
            towerPriorNormProduct c data.degree i.1 z) ≤
        ‖z (c.selectedVar i)‖ :=
    hterm_le_threshold.trans hlarge
  have hsum_le :
      towerLowerNormSum data i z ≤
        (1 / ((2 : ℝ) ^ (i.1 + 1))) *
          ‖(data.topConstant : ℂ)‖ *
            towerPriorNormProduct c data.degree i.1 z *
          ‖z (c.selectedVar i)‖ := by
    have hmul := mul_le_mul_of_nonneg_right hterm_le_norm hden_pos.le
    rw [div_mul_cancel₀] at hmul
    · have hmul' := mul_le_mul_of_nonneg_right hmul (inv_nonneg.mpr htwo_pos.le)
      calc
        towerLowerNormSum data i z
            = ((2 : ℝ) ^ (i.1 + 1) * towerLowerNormSum data i z) *
                (((2 : ℝ) ^ (i.1 + 1))⁻¹) := by
              field_simp [htwo_pos.ne']
        _ ≤ ‖z (c.selectedVar i)‖ *
              (‖(data.topConstant : ℂ)‖ *
                towerPriorNormProduct c data.degree i.1 z) *
              (((2 : ℝ) ^ (i.1 + 1))⁻¹) := hmul'
        _ = (1 / ((2 : ℝ) ^ (i.1 + 1))) *
              ‖(data.topConstant : ℂ)‖ *
                towerPriorNormProduct c data.degree i.1 z *
              ‖z (c.selectedVar i)‖ := by
              ring
    · exact hden_pos.ne'
  have hzeta_nonneg : 0 ≤ ‖z (c.selectedVar i)‖ := norm_nonneg _
  have hpow_split :
      ‖z (c.selectedVar i)‖ ^ data.degree i =
        ‖z (c.selectedVar i)‖ *
          ‖z (c.selectedVar i)‖ ^ (data.degree i - 1) := by
    calc
      ‖z (c.selectedVar i)‖ ^ data.degree i =
          ‖z (c.selectedVar i)‖ ^ ((data.degree i - 1) + 1) := by
            rw [Nat.sub_add_cancel (hdeg i)]
      _ = ‖z (c.selectedVar i)‖ ^ (data.degree i - 1) *
            ‖z (c.selectedVar i)‖ := by
            rw [pow_succ]
      _ = ‖z (c.selectedVar i)‖ *
            ‖z (c.selectedVar i)‖ ^ (data.degree i - 1) := by
            ring
  calc
    towerLowerNormSum data i z *
        ‖z (c.selectedVar i)‖ ^ (data.degree i - 1)
        ≤ ((1 / ((2 : ℝ) ^ (i.1 + 1))) *
            ‖(data.topConstant : ℂ)‖ *
              towerPriorNormProduct c data.degree i.1 z *
            ‖z (c.selectedVar i)‖) *
            ‖z (c.selectedVar i)‖ ^ (data.degree i - 1) :=
          mul_le_mul_of_nonneg_right hsum_le (pow_nonneg hzeta_nonneg _)
    _ = ((1 / ((2 : ℝ) ^ (i.1 + 1))) *
          ‖(data.topConstant : ℂ)‖ *
            towerPriorNormProduct c data.degree i.1 z) *
          ‖z (c.selectedVar i)‖ ^ data.degree i := by
          rw [hpow_split]
          ring

theorem dominance_tower_core_lower_bound {L k p : Nat} {c : HeadChain L k p}
    {f : FormalPoly L k} (data : DominanceTowerData c f)
    (hdeg : ∀ i : Fin p, 1 ≤ data.degree i)
    (hconst : data.topConstant ≠ 0)
    (htop : DominanceTowerTopConstant data)
    (hrec : DominanceTowerEvalRecurrence data)
    {z : FormalVar L k -> ℂ}
    (hz : SatisfiesTowerThresholds c (dominanceTowerThreshold data) z) :
    ∀ (i : Nat) (hi : i ≤ p),
      ((1 / ((2 : ℝ) ^ i)) * ‖(data.topConstant : ℂ)‖ *
          towerPriorNormProduct c data.degree i z) ≤
        ‖evalFormalPolyComplex z (data.leadingCoeff i hi)‖ := by
  classical
  intro i
  induction i with
  | zero =>
      intro hi
      simp [towerPriorNormProduct_eq_one_of_zero, htop z]
  | succ i ih =>
      intro hi
      have hi_lt : i < p := Nat.lt_of_succ_le hi
      let j : Fin p := ⟨i, hi_lt⟩
      have ih' :
          ((1 / ((2 : ℝ) ^ i)) * ‖(data.topConstant : ℂ)‖ *
              towerPriorNormProduct c data.degree i z) ≤
            ‖evalFormalPolyComplex z (data.leadingCoeff i (Nat.le_of_lt hi_lt))‖ :=
        ih (Nat.le_of_lt hi_lt)
      have hthreshold_one :
          ∀ j z, 1 ≤ dominanceTowerThreshold data j z :=
        towerThreshold_ge_one data hconst
      have hprior_ge_one :
          1 ≤ towerPriorNormProduct c data.degree i z :=
        towerPriorNormProduct_ge_one_of_thresholds c data.degree
          (dominanceTowerThreshold data) hthreshold_one hz i
      have hzeta_ge_one : 1 ≤ ‖z (c.selectedVar j)‖ := by
        exact (hthreshold_one j z).trans
          (real_threshold_le_selected_norm_of_satisfies hz
            (le_trans zero_le_one (hthreshold_one j z)))
      have htail_norm :
          ‖∑ s : Fin (data.degree j),
              evalFormalPolyComplex z (data.lowerCoeff j s) *
                z (c.selectedVar j) ^ (s : Nat)‖ ≤
            towerLowerNormSum data j z *
              ‖z (c.selectedVar j)‖ ^ (data.degree j - 1) :=
        tower_lower_tail_norm_le data j hzeta_ge_one
      have hscaled :
          towerLowerNormSum data j z *
              ‖z (c.selectedVar j)‖ ^ (data.degree j - 1) ≤
            ((1 / ((2 : ℝ) ^ (j.1 + 1))) *
              ‖(data.topConstant : ℂ)‖ *
                towerPriorNormProduct c data.degree j.1 z) *
              ‖z (c.selectedVar j)‖ ^ data.degree j :=
        tower_lower_scaled_le data hdeg hconst j hprior_ge_one
          (real_threshold_le_selected_norm_of_satisfies hz
            (le_trans zero_le_one (hthreshold_one j z)))
      have hzeta_nonneg : 0 ≤ ‖z (c.selectedVar j)‖ := norm_nonneg _
      have htail_le_half :
          ‖∑ s : Fin (data.degree j),
              evalFormalPolyComplex z (data.lowerCoeff j s) *
                z (c.selectedVar j) ^ (s : Nat)‖ ≤
            (1 / ((2 : ℝ) ^ (i + 1)) *
              ‖(data.topConstant : ℂ)‖ *
                towerPriorNormProduct c data.degree i z) *
              ‖z (c.selectedVar j)‖ ^ data.degree j := by
        exact htail_norm.trans (by simpa [j] using hscaled)
      have hlead_norm :
          ((1 / ((2 : ℝ) ^ i)) * ‖(data.topConstant : ℂ)‖ *
              towerPriorNormProduct c data.degree i z) *
              ‖z (c.selectedVar j)‖ ^ data.degree j ≤
            ‖evalFormalPolyComplex z (data.leadingCoeff i (Nat.le_of_lt hi_lt)) *
              z (c.selectedVar j) ^ data.degree j‖ := by
        calc
          ((1 / ((2 : ℝ) ^ i)) * ‖(data.topConstant : ℂ)‖ *
              towerPriorNormProduct c data.degree i z) *
              ‖z (c.selectedVar j)‖ ^ data.degree j
              ≤ ‖evalFormalPolyComplex z
                    (data.leadingCoeff i (Nat.le_of_lt hi_lt))‖ *
                  ‖z (c.selectedVar j)‖ ^ data.degree j :=
                mul_le_mul_of_nonneg_right ih' (pow_nonneg hzeta_nonneg _)
          _ = ‖evalFormalPolyComplex z
                  (data.leadingCoeff i (Nat.le_of_lt hi_lt)) *
                z (c.selectedVar j) ^ data.degree j‖ := by
                rw [norm_mul, norm_pow]
      have htarget_eq :
          (1 / ((2 : ℝ) ^ (i + 1)) * ‖(data.topConstant : ℂ)‖ *
              towerPriorNormProduct c data.degree (i + 1) z) =
            (1 / ((2 : ℝ) ^ (i + 1)) * ‖(data.topConstant : ℂ)‖ *
              towerPriorNormProduct c data.degree i z) *
              ‖z (c.selectedVar j)‖ ^ data.degree j := by
        rw [towerPriorNormProduct_succ c data.degree j z]
        ring
      have hhalf_le :
          (1 / ((2 : ℝ) ^ (i + 1)) * ‖(data.topConstant : ℂ)‖ *
              towerPriorNormProduct c data.degree (i + 1) z) ≤
            ‖evalFormalPolyComplex z
                (data.leadingCoeff i (Nat.le_of_lt hi_lt)) *
              z (c.selectedVar j) ^ data.degree j‖ -
              ‖∑ s : Fin (data.degree j),
                evalFormalPolyComplex z (data.lowerCoeff j s) *
                  z (c.selectedVar j) ^ (s : Nat)‖ := by
        have hlead_half :
            2 * ((1 / ((2 : ℝ) ^ (i + 1)) *
              ‖(data.topConstant : ℂ)‖ *
                towerPriorNormProduct c data.degree i z) *
              ‖z (c.selectedVar j)‖ ^ data.degree j) =
              ((1 / ((2 : ℝ) ^ i)) * ‖(data.topConstant : ℂ)‖ *
                towerPriorNormProduct c data.degree i z) *
              ‖z (c.selectedVar j)‖ ^ data.degree j := by
          have hpow : (2 : ℝ) ^ (i + 1) = 2 * (2 : ℝ) ^ i := by
            rw [pow_succ]
            ring
          field_simp [hpow]
          ring
        rw [htarget_eq]
        nlinarith
      calc
        (1 / ((2 : ℝ) ^ (i + 1)) * ‖(data.topConstant : ℂ)‖ *
            towerPriorNormProduct c data.degree (i + 1) z)
            ≤ ‖evalFormalPolyComplex z
                (data.leadingCoeff i (Nat.le_of_lt hi_lt)) *
              z (c.selectedVar j) ^ data.degree j‖ -
              ‖∑ s : Fin (data.degree j),
                evalFormalPolyComplex z (data.lowerCoeff j s) *
                  z (c.selectedVar j) ^ (s : Nat)‖ := hhalf_le
        _ ≤ ‖evalFormalPolyComplex z
              (data.leadingCoeff i (Nat.le_of_lt hi_lt)) *
              z (c.selectedVar j) ^ data.degree j +
            ∑ s : Fin (data.degree j),
              evalFormalPolyComplex z (data.lowerCoeff j s) *
                z (c.selectedVar j) ^ (s : Nat)‖ := by
              simpa [sub_neg_eq_add, norm_neg] using
                (norm_sub_norm_le
                  (evalFormalPolyComplex z
                    (data.leadingCoeff i (Nat.le_of_lt hi_lt)) *
                    z (c.selectedVar j) ^ data.degree j)
                  (-(∑ s : Fin (data.degree j),
                    evalFormalPolyComplex z (data.lowerCoeff j s) *
                      z (c.selectedVar j) ^ (s : Nat))))
        _ = ‖evalFormalPolyComplex z
              (data.leadingCoeff (i + 1) hi)‖ := by
              rw [← hrec j z]

theorem dominance_tower_core_nonvanishing {L k p : Nat} {c : HeadChain L k p}
    {f : FormalPoly L k} (data : DominanceTowerData c f)
    (hdeg : ∀ i : Fin p, 1 ≤ data.degree i)
    (hconst : data.topConstant ≠ 0)
    (htop : DominanceTowerTopConstant data)
    (hfinal : DominanceTowerFinalCoeff data)
    (hrec : DominanceTowerEvalRecurrence data)
    {z : FormalVar L k -> ℂ}
    (hz : SatisfiesTowerThresholds c (dominanceTowerThreshold data) z) :
    f.eval₂ (algebraMap ℝ ℂ) z ≠ 0 := by
  have hlower := dominance_tower_core_lower_bound data hdeg hconst htop hrec hz p le_rfl
  have hconst_norm_pos : 0 < ‖(data.topConstant : ℂ)‖ := by
    exact norm_pos_iff.mpr (by exact_mod_cast hconst)
  have hprod_ge_one :
      1 ≤ towerPriorNormProduct c data.degree p z :=
    towerPriorNormProduct_ge_one_of_thresholds c data.degree
      (dominanceTowerThreshold data)
      (towerThreshold_ge_one data hconst) hz p
  have hleft_pos :
      0 < (1 / ((2 : ℝ) ^ p)) * ‖(data.topConstant : ℂ)‖ *
        towerPriorNormProduct c data.degree p z := by
    have htwo_pos : 0 < (2 : ℝ) ^ p := by positivity
    have hprod_pos : 0 < towerPriorNormProduct c data.degree p z :=
      lt_of_lt_of_le zero_lt_one hprod_ge_one
    exact mul_pos (mul_pos (one_div_pos.mpr htwo_pos) hconst_norm_pos) hprod_pos
  have hnorm_pos :
      0 < ‖evalFormalPolyComplex z (data.leadingCoeff p le_rfl)‖ :=
    lt_of_lt_of_le hleft_pos hlower
  have hlead_ne : evalFormalPolyComplex z (data.leadingCoeff p le_rfl) ≠ 0 :=
    norm_pos_iff.mp hnorm_pos
  rw [hfinal] at hlead_ne
  simpa [evalFormalPolyComplex] using hlead_ne

/-- Result interface for **K04E lem-tower-dominance**. -/
structure TowerDominanceResult {L k p : Nat} (c : HeadChain L k p)
    (f : FormalPoly L k) : Prop where
  tower_data :
    ∃ data : DominanceTowerData c f,
      (∀ i : Fin p, 1 ≤ data.degree i) ∧
      data.topConstant ≠ 0 ∧
      DominanceTowerTopConstant data ∧
      DominanceTowerFinalCoeff data ∧
      DominanceTowerEvalRecurrence data ∧
      (∀ (i : Nat) (hi : i ≤ p), PolynomialInLayersLE i (data.leadingCoeff i hi)) ∧
      (∀ i : Fin p, Continuous (dominanceTowerThreshold data i)) ∧
      ∀ z : FormalVar L k -> ℂ,
        SatisfiesTowerThresholds c (dominanceTowerThreshold data) z ->
          f.eval₂ (algebraMap ℝ ℂ) z ≠ 0

theorem towerDominanceResult_of_core {L k p : Nat} {c : HeadChain L k p}
    {f : FormalPoly L k} (data : DominanceTowerData c f)
    (hdeg : ∀ i : Fin p, 1 ≤ data.degree i)
    (hconst : data.topConstant ≠ 0)
    (htop : DominanceTowerTopConstant data)
    (hfinal : DominanceTowerFinalCoeff data)
    (hrec : DominanceTowerEvalRecurrence data)
    (hsupport :
      ∀ (i : Nat) (hi : i ≤ p), PolynomialInLayersLE i (data.leadingCoeff i hi)) :
    TowerDominanceResult c f where
  tower_data := by
    refine ⟨data, hdeg, hconst, htop, hfinal, hrec, hsupport, ?_, ?_⟩
    · intro i
      exact continuous_dominanceTowerThreshold data hconst i
    · intro z hz
      exact dominance_tower_core_nonvanishing data hdeg hconst htop hfinal hrec hz

/-- **K04E.E.lem-tower-dominance.S/P**.

Concrete dominance-tower constructor with globally continuous thresholds and
selected-variable largeness nonvanishing. -/
theorem lem_tower_dominance {L k p : Nat} {c : HeadChain L k p}
    {f : FormalPoly L k} (data : DominanceTowerData c f)
    (hdeg : ∀ i : Fin p, 1 ≤ data.degree i)
    (hconst : data.topConstant ≠ 0)
    (htop : DominanceTowerTopConstant data)
    (hfinal : DominanceTowerFinalCoeff data)
    (hrec : DominanceTowerEvalRecurrence data)
    (hsupport :
      ∀ (i : Nat) (hi : i ≤ p), PolynomialInLayersLE i (data.leadingCoeff i hi)) :
    TowerDominanceResult c f :=
  towerDominanceResult_of_core data hdeg hconst htop hfinal hrec hsupport


end TransformerIdentifiability.NLayer.KHead
