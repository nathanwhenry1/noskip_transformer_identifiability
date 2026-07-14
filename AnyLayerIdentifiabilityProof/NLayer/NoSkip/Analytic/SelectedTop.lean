import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Analytic.FormalPolySplit
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Analytic.SiblingAvoidance
import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.FormalPolySplit

set_option autoImplicit false

open Filter Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.NoSkip

/-!
# Selected tops and dominance towers

The NoSkip structural proof combines NS031 strict prefix support with direct
`degreeOf` bounds.  This is the precise interface consumed by NS096's
constant/linear/quadratic split and does not unfold any network realization.
-/

noncomputable section

/-! ## Selected chains and structural degree bounds -/

structure HeadChain (L k : Nat) (p : Nat) where
  head : Fin p → Fin k
  length_le : p ≤ L

namespace HeadChain

def layer {L k p : Nat} (c : HeadChain L k p) (i : Fin p) : Fin L :=
  ⟨i.1, Nat.lt_of_lt_of_le i.2 c.length_le⟩

def selectedVar {L k p : Nat} (c : HeadChain L k p) (i : Fin p) : FormalVar L k :=
  (c.layer i, c.head i)

def IsSelectedVar {L k p : Nat} (c : HeadChain L k p)
    (x : FormalVar L k) : Prop :=
  ∃ i : Fin p, x = c.selectedVar i

@[simp] theorem selectedVar_layer {L k p : Nat}
    (c : HeadChain L k p) (i : Fin p) :
    (c.selectedVar i).1 = c.layer i := rfl

@[simp] theorem selectedVar_head {L k p : Nat}
    (c : HeadChain L k p) (i : Fin p) :
    (c.selectedVar i).2 = c.head i := rfl

theorem selectedVar_isSelected {L k p : Nat}
    (c : HeadChain L k p) (i : Fin p) :
    c.IsSelectedVar (c.selectedVar i) := ⟨i, rfl⟩

end HeadChain

/-- Support through layer `n`, expressed using NS031's strict-prefix support. -/
abbrev PolynomialInLayersLE {L k : Nat} (n : Nat) (f : FormalPoly L k) : Prop :=
  FormalPolySupportBefore (n + 1) f

/-- Strict layer-prefix support. -/
abbrev PolynomialInLayersLT {L k : Nat} (n : Nat) (f : FormalPoly L k) : Prop :=
  FormalPolySupportBefore n f

/-- Total degree in each complete head block.  This is stronger than the
legacy coordinatewise `BlockDegreeLE` below and is the invariant required by
canonical selected-tail extraction. -/
def BlockTotalDegreeLE {L k : Nat} (D : Nat) (f : FormalPoly L k) : Prop :=
  ∀ m ∈ f.support, ∀ l : Fin L, (∑ a : Fin k, m (l, a)) ≤ D

/-- Coordinatewise degree at most one in every formal gate variable. -/
def BlockMultiAffine {L k : Nat} (f : FormalPoly L k) : Prop :=
  ∀ x : FormalVar L k, MvPolynomial.degreeOf x f ≤ 1

/-- Coordinatewise formal-gate degree bound. -/
def BlockDegreeLE {L k : Nat} (D : Nat) (f : FormalPoly L k) : Prop :=
  ∀ x : FormalVar L k, MvPolynomial.degreeOf x f ≤ D

theorem degreeOf_eq_zero_of_supportBefore {L k n : Nat}
    {f : FormalPoly L k} (hf : FormalPolySupportBefore n f)
    {x : FormalVar L k} (hx : n ≤ x.1.1) :
    MvPolynomial.degreeOf x f = 0 := by
  apply Nat.eq_zero_of_le_zero
  rw [MvPolynomial.degreeOf_le_iff]
  intro m hm
  simp [hf m hm x hx]

theorem degreeOf_formalGatedValueSum_le {L k d : Nat}
    (theta : Params L k d) (l : Fin L) (i j : Fin d)
    (x : FormalVar L k) :
    MvPolynomial.degreeOf x (formalGatedValueSum theta l i j) ≤
      if x.1 = l then 1 else 0 := by
  classical
  simp only [formalGatedValueSum, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine le_trans (MvPolynomial.degreeOf_sum_le x Finset.univ
    (fun a => formalGate l a * formalValueMatrix theta l a i j)) ?_
  apply Finset.sup_le
  intro a _ha
  refine le_trans (MvPolynomial.degreeOf_mul_le x
    (formalGate l a) (formalValueMatrix theta l a i j)) ?_
  simp [formalGate, formalValueMatrix, realMatrixToFormal,
    MvPolynomial.degreeOf_X]
  by_cases hxl : x.1 = l
  · simp only [hxl, if_true]
    split <;> omega
  · have hpair : x ≠ (l, a) := by
      intro h
      exact hxl (congrArg Prod.fst h)
    simp [hxl, hpair]

theorem degreeOf_realMatrixToFormal_entry {L k d : Nat}
    (M : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) (x : FormalVar L k) :
    MvPolynomial.degreeOf x (realMatrixToFormal (L := L) (k := k) M i j) = 0 := by
  simp [realMatrixToFormal]

theorem degreeOf_formalMatrix_mulVec_le {L k d D E : Nat}
    (M : Matrix (Fin d) (Fin d) (FormalPoly L k))
    (u : FormalVec L k d) (x : FormalVar L k)
    (hM : ∀ i j, MvPolynomial.degreeOf x (M i j) ≤ D)
    (hu : ∀ j, MvPolynomial.degreeOf x (u j) ≤ E) :
    ∀ i, MvPolynomial.degreeOf x ((M *ᵥ u) i) ≤ D + E := by
  classical
  intro i
  simp only [Matrix.mulVec, dotProduct]
  refine le_trans (MvPolynomial.degreeOf_sum_le x Finset.univ
    (fun j => M i j * u j)) ?_
  apply Finset.sup_le
  intro j _hj
  exact (MvPolynomial.degreeOf_mul_le x (M i j) (u j)).trans
    (Nat.add_le_add (hM i j) (hu j))

/-- Every coordinate of both formal streams is degree at most one in each gate
variable.  Prefix support ensures current-layer gates never multiply a prior
occurrence of the same variable. -/
theorem formalPoint_blockMultiAffine {L k d : Nat}
    (theta : Params L k d) (w v : Vec d) :
    ∀ (n : Nat) (hn : n ≤ L),
      (∀ i, BlockMultiAffine (formalW theta w v n hn i)) ∧
      (∀ i, BlockMultiAffine (formalV theta w v n hn i)) := by
  intro n hn
  induction n with
  | zero =>
      constructor <;> intro i x <;>
        simp [formalW, formalV, formalPoint, realVecToFormal, formalConst]
  | succ n ih =>
      have hnprev : n ≤ L := Nat.le_of_succ_le hn
      rcases ih hnprev with ⟨hwdeg, hvdeg⟩
      let l : Fin L := ⟨n, Nat.lt_of_succ_le hn⟩
      let W := formalW theta w v n hnprev
      let V := formalV theta w v n hnprev
      have hWsupport : ∀ i, FormalPolySupportBefore n (W i) := by
        intro i
        exact formalW_supportBefore theta w v n hnprev i
      have hVsupport : ∀ i, FormalPolySupportBefore n (V i) := by
        intro i
        exact formalV_supportBefore theta w v n hnprev i
      constructor
      · intro i x
        change MvPolynomial.degreeOf x
          ((formalStepPoint theta l W V).1 i) ≤ 1
        simp only [formalStepPoint]
        by_cases hx : x.1.1 < n
        · have hxl : x.1 ≠ l := by
            intro heq
            have := congrArg Fin.val heq
            simp [l] at this
            omega
          have hD0 : ∀ i j,
              MvPolynomial.degreeOf x (formalGatedValueSum theta l i j) ≤ 0 := by
            intro i j
            simpa [hxl] using degreeOf_formalGatedValueSum_le theta l i j x
          have hC0 : ∀ i j,
              MvPolynomial.degreeOf x (formalCollapseMatrix theta l i j) ≤ 0 := by
            intro i j
            simp [formalCollapseMatrix]
          have hM0 : ∀ i j, MvPolynomial.degreeOf x
              ((formalCollapseMatrix theta l - formalGatedValueSum theta l) i j) ≤ 0 := by
            intro i j
            have hCeq : MvPolynomial.degreeOf x
                (formalCollapseMatrix theta l i j) = 0 :=
              Nat.eq_zero_of_le_zero (hC0 i j)
            have hDeq : MvPolynomial.degreeOf x
                (formalGatedValueSum theta l i j) = 0 :=
              Nat.eq_zero_of_le_zero (hD0 i j)
            exact (MvPolynomial.degreeOf_sub_le x _ _).trans
              (by simp [hCeq, hDeq])
          exact (degreeOf_formalMatrix_mulVec_le
            (formalCollapseMatrix theta l - formalGatedValueSum theta l)
            W x hM0 (fun j => hwdeg j x) i).trans (by omega)
        · have hnx : n ≤ x.1.1 := Nat.le_of_not_gt hx
          have hW0 : ∀ j, MvPolynomial.degreeOf x (W j) ≤ 0 := by
            intro j
            simp [degreeOf_eq_zero_of_supportBefore (hWsupport j) hnx]
          have hM1 : ∀ i j, MvPolynomial.degreeOf x
              ((formalCollapseMatrix theta l - formalGatedValueSum theta l) i j) ≤ 1 := by
            intro i j
            refine (MvPolynomial.degreeOf_sub_le x _ _).trans ?_
            have hD := degreeOf_formalGatedValueSum_le theta l i j x
            have hDle : MvPolynomial.degreeOf x
                (formalGatedValueSum theta l i j) ≤ 1 :=
              hD.trans (by split <;> omega)
            have hC : MvPolynomial.degreeOf x (formalCollapseMatrix theta l i j) = 0 := by
              simp [formalCollapseMatrix]
            simpa [hC] using max_le (Nat.zero_le 1) hDle
          exact (degreeOf_formalMatrix_mulVec_le
            (formalCollapseMatrix theta l - formalGatedValueSum theta l)
            W x hM1 hW0 i).trans (by omega)
      · intro i x
        change MvPolynomial.degreeOf x
          ((formalStepPoint theta l W V).2 i) ≤ 1
        simp only [formalStepPoint]
        by_cases hx : x.1.1 < n
        · have hxl : x.1 ≠ l := by
            intro heq
            have := congrArg Fin.val heq
            simp [l] at this
            omega
          have hD0 : ∀ i j,
              MvPolynomial.degreeOf x (formalGatedValueSum theta l i j) ≤ 0 := by
            intro i j
            simpa [hxl] using degreeOf_formalGatedValueSum_le theta l i j x
          have hC0 : ∀ i j,
              MvPolynomial.degreeOf x (formalCollapseMatrix theta l i j) ≤ 0 := by
            intro i j
            simp [formalCollapseMatrix]
          have hCV := degreeOf_formalMatrix_mulVec_le
            (formalCollapseMatrix theta l) V x hC0 (fun j => hvdeg j x) i
          have hDW := degreeOf_formalMatrix_mulVec_le
            (formalGatedValueSum theta l) W x hD0 (fun j => hwdeg j x) i
          exact (MvPolynomial.degreeOf_add_le x _ _).trans (by omega)
        · have hnx : n ≤ x.1.1 := Nat.le_of_not_gt hx
          have hW0 : ∀ j, MvPolynomial.degreeOf x (W j) ≤ 0 := by
            intro j
            simp [degreeOf_eq_zero_of_supportBefore (hWsupport j) hnx]
          have hV0 : ∀ j, MvPolynomial.degreeOf x (V j) ≤ 0 := by
            intro j
            simp [degreeOf_eq_zero_of_supportBefore (hVsupport j) hnx]
          have hC0 : ∀ i j,
              MvPolynomial.degreeOf x (formalCollapseMatrix theta l i j) ≤ 0 := by
            intro i j
            simp [formalCollapseMatrix]
          have hD1 : ∀ i j,
              MvPolynomial.degreeOf x (formalGatedValueSum theta l i j) ≤ 1 := by
            intro i j
            exact (degreeOf_formalGatedValueSum_le theta l i j x).trans
              (by split <;> omega)
          have hCV := degreeOf_formalMatrix_mulVec_le
            (formalCollapseMatrix theta l) V x hC0 hV0 i
          have hDW := degreeOf_formalMatrix_mulVec_le
            (formalGatedValueSum theta l) W x hD1 hW0 i
          exact (MvPolynomial.degreeOf_add_le x _ _).trans (by omega)

theorem formalW_blockMultiAffine {L k d : Nat} (theta : Params L k d)
    (w v : Vec d) (n : Nat) (hn : n ≤ L) (i : Fin d) :
    BlockMultiAffine (formalW theta w v n hn i) :=
  (formalPoint_blockMultiAffine theta w v n hn).1 i

theorem formalV_blockMultiAffine {L k d : Nat} (theta : Params L k d)
    (w v : Vec d) (n : Nat) (hn : n ≤ L) (i : Fin d) :
    BlockMultiAffine (formalV theta w v n hn i) :=
  (formalPoint_blockMultiAffine theta w v n hn).2 i

/-- The genuine total-block invariant for no-skip formal streams.  We reuse
only the neutral polynomial closure lemmas from the KHead analytic toolbox;
the recursion unfolded here is the no-skip `formalStepPoint`. -/
theorem formalPoint_layerBoundedBlockAffine {L k d : Nat}
    (theta : Params L k d) (w v : Vec d) :
    ∀ (n : Nat) (hn : n ≤ L),
      (∀ i, KHead.LayerBoundedBlockAffine n (formalW theta w v n hn i)) ∧
      (∀ i, KHead.LayerBoundedBlockAffine n (formalV theta w v n hn i)) := by
  intro n hn
  induction n with
  | zero =>
      constructor <;> intro i <;>
        simp [formalW, formalV, formalPoint, realVecToFormal, formalConst,
          KHead.LayerBoundedBlockAffine.C]
  | succ n ih =>
      have hnprev : n ≤ L := Nat.le_of_succ_le hn
      rcases ih hnprev with ⟨hw, hv⟩
      let l : Fin L := ⟨n, Nat.lt_of_succ_le hn⟩
      let W := formalW theta w v n hnprev
      let V := formalV theta w v n hnprev
      have hCW : ∀ i, KHead.LayerBoundedBlockAffine n
          ((realMatrixToFormal (collapseMatrix theta l) *ᵥ W) i) :=
        KHead.layerBounded_realMatrixToFormal_mulVec (collapseMatrix theta l) hw
      have hCV : ∀ i, KHead.LayerBoundedBlockAffine n
          ((realMatrixToFormal (collapseMatrix theta l) *ᵥ V) i) :=
        KHead.layerBounded_realMatrixToFormal_mulVec (collapseMatrix theta l) hv
      have hDW : ∀ i, KHead.LayerBoundedBlockAffine (n + 1)
          ((formalGatedValueSum theta l *ᵥ W) i) := by
        intro i
        have hk := KHead.layerBounded_formalGatedValueSum_mulVec
          (x := W) theta (l := l) rfl hw i
        simpa [formalGatedValueSum, KHead.formalGatedValueSum,
          formalGate, KHead.formalGate, formalValueMatrix, KHead.formalValueMatrix,
          realMatrixToFormal, KHead.realMatrixToFormal] using hk
      constructor
      · intro i
        change KHead.LayerBoundedBlockAffine (n + 1)
          (((formalCollapseMatrix theta l - formalGatedValueSum theta l) *ᵥ W) i)
        have hC := KHead.LayerBoundedBlockAffine.mono (Nat.le_succ n) (hCW i)
        simpa only [Matrix.sub_mulVec] using KHead.LayerBoundedBlockAffine.sub hC (hDW i)
      · intro i
        change KHead.LayerBoundedBlockAffine (n + 1)
          ((formalCollapseMatrix theta l *ᵥ V + formalGatedValueSum theta l *ᵥ W) i)
        have hC := KHead.LayerBoundedBlockAffine.mono (Nat.le_succ n) (hCV i)
        simpa only [Pi.add_apply] using KHead.LayerBoundedBlockAffine.add hC (hDW i)

theorem formalW_blockTotalDegree_one {L k d : Nat} (theta : Params L k d)
    (w v : Vec d) (n : Nat) (hn : n ≤ L) (i : Fin d) :
    BlockTotalDegreeLE 1 (formalW theta w v n hn i) := by
  intro m hm l
  exact ((formalPoint_layerBoundedBlockAffine theta w v n hn).1 i).block m hm |>.block_sum_le_one l

theorem formalV_blockTotalDegree_one {L k d : Nat} (theta : Params L k d)
    (w v : Vec d) (n : Nat) (hn : n ≤ L) (i : Fin d) :
    BlockTotalDegreeLE 1 (formalV theta w v n hn i) := by
  intro m hm l
  exact ((formalPoint_layerBoundedBlockAffine theta w v n hn).2 i).block m hm |>.block_sum_le_one l

theorem formalBilin_blockDegree_two {L k d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (W V : FormalVec L k d)
    (hW : ∀ i, BlockMultiAffine (W i))
    (hV : ∀ i, BlockMultiAffine (V i)) :
    BlockDegreeLE 2 (formalBilin A W V) := by
  intro x
  simp only [formalBilin, dotProduct]
  have hAV : ∀ i,
      MvPolynomial.degreeOf x ((realMatrixToFormal A *ᵥ V) i) ≤ 1 := by
    intro i
    exact (degreeOf_formalMatrix_mulVec_le (D := 0) (E := 1)
      (realMatrixToFormal A) V x
      (fun i j => by simp)
      (fun j => hV j x) i).trans (by omega)
  refine le_trans (MvPolynomial.degreeOf_sum_le x Finset.univ
    (fun i => W i * (realMatrixToFormal A *ᵥ V) i)) ?_
  apply Finset.sup_le
  intro i _hi
  exact (MvPolynomial.degreeOf_mul_le x _ _).trans
    (Nat.add_le_add (hW i x) (hAV i))

theorem formalSlope_blockDegree_two {L k d : Nat}
    (theta : Params L k d) (w v : Vec d) (l : Fin L) (a : Fin k) :
    BlockDegreeLE 2 (formalSlope theta w v l a) := by
  exact formalBilin_blockDegree_two (attentionMatrix theta l a)
    (formalW theta w v l.1 (Nat.le_of_lt l.2))
    (formalV theta w v l.1 (Nat.le_of_lt l.2))
    (fun i => formalW_blockMultiAffine theta w v l.1 (Nat.le_of_lt l.2) i)
    (fun i => formalV_blockMultiAffine theta w v l.1 (Nat.le_of_lt l.2) i)

/-- Total degree at most two in every complete head block of a no-skip slope. -/
theorem formalSlope_blockTotalDegree_two {L k d : Nat}
    (theta : Params L k d) (w v : Vec d) (l : Fin L) (a : Fin k) :
    BlockTotalDegreeLE 2 (formalSlope theta w v l a) := by
  have hk : KHead.BlockDegreeLE 2
      (KHead.formalBilin (attentionMatrix theta l a)
        (formalW theta w v l.1 (Nat.le_of_lt l.2))
        (formalV theta w v l.1 (Nat.le_of_lt l.2))) :=
    KHead.blockDegreeLE_two_formalBilin (attentionMatrix theta l a)
      (formalW theta w v l.1 (Nat.le_of_lt l.2))
      (formalV theta w v l.1 (Nat.le_of_lt l.2))
      (fun i => ((formalPoint_layerBoundedBlockAffine theta w v l.1
        (Nat.le_of_lt l.2)).1 i).block)
      (fun i => ((formalPoint_layerBoundedBlockAffine theta w v l.1
        (Nat.le_of_lt l.2)).2 i).block)
  simpa [BlockTotalDegreeLE, KHead.BlockDegreeLE, formalSlope,
    formalBilin, KHead.formalBilin, realMatrixToFormal, KHead.realMatrixToFormal] using hk

structure MultiAffineResult {L k d : Nat}
    (theta : Params L k d) (w v : Vec d) : Prop where
  formalW_blockMultiAffine :
    ∀ n (hn : n ≤ L) i, BlockMultiAffine (formalW theta w v n hn i)
  formalV_blockMultiAffine :
    ∀ n (hn : n ≤ L) i, BlockMultiAffine (formalV theta w v n hn i)
  formalSlope_blockDegree_two :
    ∀ l a, BlockDegreeLE 2 (formalSlope theta w v l a)

theorem lem_multi_affine {L k d : Nat} {theta : Params L k d} {w v : Vec d} :
    MultiAffineResult theta w v where
  formalW_blockMultiAffine := formalW_blockMultiAffine theta w v
  formalV_blockMultiAffine := formalV_blockMultiAffine theta w v
  formalSlope_blockDegree_two := formalSlope_blockDegree_two theta w v

/-! ## Selected-tail coefficients -/

/-- Monomial support through layer `n`. -/
def SupportedInLayersLE {L k : Nat} (n : Nat)
    (m : FormalVar L k →₀ Nat) : Prop :=
  ∀ x : FormalVar L k, n < x.1.1 → m x = 0

namespace PolynomialInLayersLE

theorem zero {L k n : Nat} :
    PolynomialInLayersLE (L := L) (k := k) n 0 := by
  simp [FormalPolySupportBefore]

theorem monomial {L k n : Nat} {m : FormalVar L k →₀ Nat} {a : ℝ}
    (hm : SupportedInLayersLE n m) :
    PolynomialInLayersLE n
      (MvPolynomial.monomial m a : FormalPoly L k) := by
  classical
  intro u hu x hx
  have hsub :
      (MvPolynomial.monomial m a : FormalPoly L k).support ⊆
        ({m} : Finset (FormalVar L k →₀ Nat)) :=
    MvPolynomial.support_monomial_subset
  have hum : u = m := by simpa using hsub hu
  subst u
  exact hm x (by omega)

theorem sum {L k n : Nat} {ι : Type*}
    (s : Finset ι) {f : ι → FormalPoly L k}
    (hf : ∀ i ∈ s, PolynomialInLayersLE n (f i)) :
    PolynomialInLayersLE n (∑ i ∈ s, f i) := by
  classical
  intro m hm x hx
  have hmem : m ∈ s.biUnion (fun i => (f i).support) := by
    exact MvPolynomial.support_sum (s := s) (f := f)
      (by simpa using hm)
  rcases Finset.mem_biUnion.mp hmem with ⟨i, hi, hmi⟩
  exact hf i hi m hmi x hx

theorem mono {L k i n : Nat} (hin : i ≤ n) {f : FormalPoly L k}
    (hf : PolynomialInLayersLE i f) : PolynomialInLayersLE n f := by
  intro m hm x hx
  exact hf m hm x (by omega)

end PolynomialInLayersLE

/-- Remove variables above layer `n` from an exponent vector. -/
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
    SupportedInLayersLE (L := L) (k := k) n
      (truncateExponentLayersLE n m) := by
  intro x hx
  simp [Nat.not_le_of_gt hx]

/-- Target exponent of a gate in a selected tail. -/
noncomputable def selectedTailTarget {L k p : Nat} (c : HeadChain L k p)
    (deg : Nat) (x : FormalVar L k) : Nat := by
  classical
  exact if c.IsSelectedVar x then deg else 0

/-- A monomial matches the selected exponent pattern on `i ≤ layer < n`. -/
def SelectedTailMatches {L k p : Nat} (c : HeadChain L k p)
    (i n deg : Nat) (m : FormalVar L k →₀ Nat) : Prop :=
  ∀ x : FormalVar L k, i ≤ x.1.1 → x.1.1 < n →
    m x = selectedTailTarget c deg x

/-- Extract matching selected-tail monomials, then truncate above layer `i`. -/
noncomputable def selectedTailCoeff {L k p : Nat} (c : HeadChain L k p)
    (i n deg : Nat) (f : FormalPoly L k) : FormalPoly L k := by
  classical
  exact ∑ m ∈ f.support,
    if SelectedTailMatches c i n deg m then
      MvPolynomial.monomial (truncateExponentLayersLE i m) (f.coeff m)
    else 0

theorem selectedTailCoeff_polynomialInLayersLE {L k p : Nat}
    (c : HeadChain L k p) (i n deg : Nat) (f : FormalPoly L k) :
    PolynomialInLayersLE i (selectedTailCoeff c i n deg f) := by
  classical
  unfold selectedTailCoeff
  refine PolynomialInLayersLE.sum f.support ?_
  intro m hm
  by_cases hmatch : SelectedTailMatches c i n deg m
  · simpa [hmatch] using
      (PolynomialInLayersLE.monomial
        (truncateExponentLayersLE_supported (L := L) (k := k) i m)
        (a := f.coeff m))
  · simpa [hmatch] using
      (PolynomialInLayersLE.zero (L := L) (k := k) (n := i))

/-- Selected-tail coefficient of a formal stream coordinate. -/
noncomputable def selectedTopStreamCoeff {L k d p : Nat} (theta : Params L k d)
    (w v : Vec d) (c : HeadChain L k p)
    (i n : Nat) (_hin : i ≤ n) (hn : n ≤ p) : FormalVec L k d :=
  fun r => selectedTailCoeff c i n 1
    (formalW theta w v n (Nat.le_trans hn c.length_le) r)

/-- Selected quadratic-tail coefficient of a slope at a chain layer. -/
noncomputable def selectedTopSlopeQuadraticCoeff {L k d p : Nat}
    (theta : Params L k d) (w v : Vec d) (c : HeadChain L k p)
    (j : Fin p) (a : Fin k) : FormalPoly L k :=
  selectedTailCoeff c 0 j.1 2 (formalSlope theta w v (c.layer j) a)

/-- Full selected-tail coefficient of the terminal stream. -/
noncomputable def selectedTopTerminalCoeff {L k d p : Nat} (theta : Params L k d)
    (w v : Vec d) (c : HeadChain L k p) (r : Fin d) : FormalPoly L k :=
  selectedTailCoeff c 0 p 1 (formalW theta w v p c.length_le r)

structure SelectedTopData {L k d p : Nat} (theta : Params L k d)
    (w v : Vec d) (c : HeadChain L k p) where
  streamCoeff : (i n : Nat) → i ≤ n → n ≤ p → FormalVec L k d
  slopeQuadraticCoeff : Fin p → Fin k → FormalPoly L k
  terminalCoordCoeff : Fin d → FormalPoly L k

noncomputable def selectedTopData {L k d p : Nat} (theta : Params L k d)
    (w v : Vec d) (c : HeadChain L k p) : SelectedTopData theta w v c where
  streamCoeff := selectedTopStreamCoeff theta w v c
  slopeQuadraticCoeff := selectedTopSlopeQuadraticCoeff theta w v c
  terminalCoordCoeff := selectedTopTerminalCoeff theta w v c

structure SelectedTopResult {L k d p : Nat} (theta : Params L k d)
    (w v : Vec d) (c : HeadChain L k p) : Prop where
  coefficient_data :
    ∃ data : SelectedTopData theta w v c,
      (∀ i n (hin : i ≤ n) (hn : n ≤ p),
        data.streamCoeff i n hin hn = selectedTopStreamCoeff theta w v c i n hin hn) ∧
      (∀ j a, data.slopeQuadraticCoeff j a =
        selectedTopSlopeQuadraticCoeff theta w v c j a) ∧
      (∀ r, data.terminalCoordCoeff r = selectedTopTerminalCoeff theta w v c r) ∧
      (∀ i n (hin : i ≤ n) (hn : n ≤ p) r,
        PolynomialInLayersLE i (data.streamCoeff i n hin hn r)) ∧
      (∀ j a, PolynomialInLayersLE j.1 (data.slopeQuadraticCoeff j a)) ∧
      (∀ r, PolynomialInLayersLE p (data.terminalCoordCoeff r))
  formal_stream_support :
    ∀ n (hn : n ≤ p) r,
      PolynomialInLayersLE n
        (formalW theta w v n (Nat.le_trans hn c.length_le) r)
  formal_slope_support :
    ∀ j a, PolynomialInLayersLE j.1
      (formalSlope theta w v (c.layer j) a)
  formal_slope_blockDegree_two :
    ∀ j a, BlockDegreeLE 2 (formalSlope theta w v (c.layer j) a)

theorem selectedTop_coefficient_data {L k d p : Nat} (theta : Params L k d)
    (w v : Vec d) (c : HeadChain L k p) :
    ∃ data : SelectedTopData theta w v c,
      (∀ i n (hin : i ≤ n) (hn : n ≤ p),
        data.streamCoeff i n hin hn = selectedTopStreamCoeff theta w v c i n hin hn) ∧
      (∀ j a, data.slopeQuadraticCoeff j a =
        selectedTopSlopeQuadraticCoeff theta w v c j a) ∧
      (∀ r, data.terminalCoordCoeff r = selectedTopTerminalCoeff theta w v c r) ∧
      (∀ i n (hin : i ≤ n) (hn : n ≤ p) r,
        PolynomialInLayersLE i (data.streamCoeff i n hin hn r)) ∧
      (∀ j a, PolynomialInLayersLE j.1 (data.slopeQuadraticCoeff j a)) ∧
      (∀ r, PolynomialInLayersLE p (data.terminalCoordCoeff r)) := by
  refine ⟨selectedTopData theta w v c, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros
    exact selectedTailCoeff_polynomialInLayersLE c _ _ 1 _
  · intro j a
    exact PolynomialInLayersLE.mono (Nat.zero_le j.1)
      (selectedTailCoeff_polynomialInLayersLE c 0 j.1 2 _)
  · intro r
    exact PolynomialInLayersLE.mono (Nat.zero_le p)
      (selectedTailCoeff_polynomialInLayersLE c 0 p 1 _)

theorem selectedTop_formalStream_support {L k d p : Nat}
    (theta : Params L k d) (w v : Vec d) (c : HeadChain L k p) :
    ∀ n (hn : n ≤ p) r,
      PolynomialInLayersLE n
        (formalW theta w v n (Nat.le_trans hn c.length_le) r) := by
  intro n hn r m hm x hx
  exact formalW_supportBefore theta w v n (Nat.le_trans hn c.length_le) r
    m hm x (by omega)

theorem selectedTop_formalSlope_support {L k d p : Nat}
    (theta : Params L k d) (w v : Vec d) (c : HeadChain L k p) :
    ∀ j a, PolynomialInLayersLE j.1
      (formalSlope theta w v (c.layer j) a) := by
  intro j a m hm x hx
  exact formalSlope_supportBefore theta w v (c.layer j) a m hm x (by
    change j.1 ≤ x.1.1
    omega)

/-- NS096's quadratic split with its degree premise discharged structurally. -/
theorem eval_complexFormalSlope_quadratic_split {L k d : Nat}
    (theta : Params L k d) (w v : Vec d) (l : Fin L) (a : Fin k)
    (x : FormalVar L k) (z : FormalVar L k → ℂ) :
    complexFormalSlope theta w v z (l, a) =
      evalFormalPolyComplex z (coeffOfVar x 0 (formalSlope theta w v l a)) +
        evalFormalPolyComplex z (coeffOfVar x 1 (formalSlope theta w v l a)) * z x +
        evalFormalPolyComplex z (coeffOfVar x 2 (formalSlope theta w v l a)) *
          (z x) ^ 2 :=
  eval_complexFormalSlope_eq_coeff_zero_add_one_add_two theta w v l a x
    (formalSlope_blockDegree_two theta w v l a x) z

theorem lem_selected_top {L k d p : Nat} {theta : Params L k d} {w v : Vec d}
    {c : HeadChain L k p} : SelectedTopResult theta w v c where
  coefficient_data := selectedTop_coefficient_data theta w v c
  formal_stream_support := selectedTop_formalStream_support theta w v c
  formal_slope_support := selectedTop_formalSlope_support theta w v c
  formal_slope_blockDegree_two := fun j a =>
    formalSlope_blockDegree_two theta w v (c.layer j) a


/-! ## `lem:tower-dominance` -/

/-- Iterated selected-leading coefficient data for a dominance tower. -/
structure DominanceTowerData {L k p : Nat} (c : HeadChain L k p)
    (f : FormalPoly L k) where
  degree : Fin p -> Nat
  leadingCoeff : (i : Nat) -> i ≤ p -> FormalPoly L k
  lowerCoeff : (i : Fin p) -> Fin (degree i) -> FormalPoly L k
  topConstant : ℝ

def CanonicalTowerEvalRecurrence {L k p : Nat} {c : HeadChain L k p}
    {f : FormalPoly L k} (data : DominanceTowerData c f) : Prop :=
  ∀ (i : Fin p) (z : FormalVar L k → ℂ),
    evalFormalPolyComplex z (data.leadingCoeff (i.1 + 1) (Nat.succ_le_of_lt i.2)) =
      evalFormalPolyComplex z (data.leadingCoeff i.1 (Nat.le_of_lt i.2)) *
          z (c.selectedVar i) ^ data.degree i +
        ∑ s : Fin (data.degree i), evalFormalPolyComplex z (data.lowerCoeff i s) *
          z (c.selectedVar i) ^ (s : Nat)

def CanonicalTowerTopConstant {L k p : Nat} {c : HeadChain L k p}
    {f : FormalPoly L k} (data : DominanceTowerData c f) : Prop :=
  ∀ z, evalFormalPolyComplex z (data.leadingCoeff 0 (Nat.zero_le p)) =
    (data.topConstant : ℂ)

def CanonicalTowerFinalCoeff {L k p : Nat} {c : HeadChain L k p}
    {f : FormalPoly L k} (data : DominanceTowerData c f) : Prop :=
  data.leadingCoeff p le_rfl = f

/-! ### Canonical clean-tail tower from a total block-degree bound -/

theorem coeffOfVar_blockTotalDegreeLE {L k D : Nat} (x : FormalVar L k) (s : Nat)
    {f : FormalPoly L k} (hf : BlockTotalDegreeLE D f) :
    BlockTotalDegreeLE D (coeffOfVar x s f) := by
  classical
  intro m hm l
  rcases coeffOfVar_support_exists hm with ⟨u, hu, _hux, rfl⟩
  calc
    (∑ a : Fin k, (Finsupp.erase x u) (l, a)) ≤ ∑ a : Fin k, u (l, a) := by
      refine Finset.sum_le_sum ?_
      intro a _ha
      by_cases hax : (l, a) = x
      · subst hax; simp
      · simp [Finsupp.erase_ne hax]
    _ ≤ D := hf u hu l

theorem coeffOfVar_top_no_currentLayer {L k D : Nat} (x : FormalVar L k)
    {f : FormalPoly L k} (hf : BlockTotalDegreeLE D f)
    {m : FormalVar L k →₀ Nat} (hm : m ∈ (coeffOfVar x D f).support)
    (a : Fin k) : m (x.1, a) = 0 := by
  classical
  rcases coeffOfVar_support_exists hm with ⟨u, hu, hux, rfl⟩
  have hsum_le := hf u hu x.1
  have hx_le : u x ≤ ∑ b : Fin k, u (x.1, b) := by
    simpa using Finset.single_le_sum (f := fun b => u (x.1, b))
      (fun b _ => Nat.zero_le _) (Finset.mem_univ x.2)
  have hsum_eq : (∑ b : Fin k, u (x.1, b)) = D := by
    rw [hux] at hx_le
    omega
  by_cases hax : (x.1, a) = x
  · rw [hax]; simp
  · have hne : a ≠ x.2 := by
      intro ha; apply hax; cases x; simp_all
    have hmem : a ∈ Finset.univ.erase x.2 := Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩
    have hle : u (x.1, a) ≤ ∑ b ∈ Finset.univ.erase x.2, u (x.1, b) := by
      exact Finset.single_le_sum (s := Finset.univ.erase x.2)
        (f := fun b => u (x.1, b)) (fun b _ => Nat.zero_le _) hmem
    have hsplit := Finset.add_sum_erase Finset.univ (fun b => u (x.1, b))
      (Finset.mem_univ x.2)
    have hzero : u (x.1, a) = 0 := by
      have hxeq : u (x.1, x.2) = D := by simpa using hux
      have hrest : (∑ b ∈ Finset.univ.erase x.2, u (x.1, b)) = 0 := by
        have heq : D + (∑ b ∈ Finset.univ.erase x.2, u (x.1, b)) = D := by
          calc
            D + (∑ b ∈ Finset.univ.erase x.2, u (x.1, b)) =
                u (x.1, x.2) + ∑ b ∈ Finset.univ.erase x.2, u (x.1, b) := by
                  rw [hxeq]
            _ = ∑ b : Fin k, u (x.1, b) := hsplit
            _ = D := hsum_eq
        omega
      exact Nat.eq_zero_of_le_zero (by simpa [hrest] using hle)
    simp [Finsupp.erase_ne hax, hzero]

theorem coeffOfVar_top_supportBefore {L k D n : Nat} (x : FormalVar L k)
    (hx : x.1.1 = n) {f : FormalPoly L k}
    (hf : BlockTotalDegreeLE D f) (hfn : PolynomialInLayersLE n f) :
    PolynomialInLayersLT n (coeffOfVar x D f) := by
  classical
  intro m hm y hy
  rcases Nat.eq_or_lt_of_le hy with heq | hlt
  · have hyx1 : y.1 = x.1 := Fin.ext (by omega)
    change m (y.1, y.2) = 0
    rw [hyx1]
    exact coeffOfVar_top_no_currentLayer x hf hm y.2
  · rcases coeffOfVar_support_exists hm with ⟨u, hu, _hux, rfl⟩
    by_cases hyx : y = x
    · subst y; simp
    · rw [Finsupp.erase_ne hyx]
      exact hfn u hu y hlt

section CanonicalTower

variable {L k p : Nat} (c : HeadChain L k p) (deg : Nat) (f : FormalPoly L k)

noncomputable def topLeadingCoeff : Nat → FormalPoly L k
  | 0 => f
  | t + 1 => if h : t < p then
      coeffOfVar (c.selectedVar ⟨p - 1 - t, by omega⟩) deg (topLeadingCoeff t)
    else topLeadingCoeff t

@[simp] theorem topLeadingCoeff_zero : topLeadingCoeff c deg f 0 = f := rfl

theorem topLeadingCoeff_blockTotal (hf : BlockTotalDegreeLE deg f) :
    ∀ t, BlockTotalDegreeLE deg (topLeadingCoeff c deg f t)
  | 0 => hf
  | t + 1 => by
      rw [topLeadingCoeff]
      split_ifs with ht
      · exact coeffOfVar_blockTotalDegreeLE _ _ (topLeadingCoeff_blockTotal hf t)
      · exact topLeadingCoeff_blockTotal hf t

theorem topLeadingCoeff_support (hf : PolynomialInLayersLT p f)
    (hfb : BlockTotalDegreeLE deg f) :
    ∀ t, PolynomialInLayersLT (p - t) (topLeadingCoeff c deg f t)
  | 0 => by simpa using hf
  | t + 1 => by
      rw [topLeadingCoeff]
      split_ifs with ht
      · have ih := topLeadingCoeff_support hf hfb t
        have hle : PolynomialInLayersLE (p - 1 - t) (topLeadingCoeff c deg f t) := by
          intro m hm y hy
          exact ih m hm y (by omega)
        have hx : (c.selectedVar ⟨p - 1 - t, by omega⟩).1.1 = p - 1 - t := rfl
        have hs := coeffOfVar_top_supportBefore
          (c.selectedVar ⟨p - 1 - t, by omega⟩) hx
          (topLeadingCoeff_blockTotal c deg f hfb t) hle
        intro m hm y hy
        exact hs m hm y (by omega)
      · have heq : p - (t + 1) = p - t := by omega
        rw [heq]
        exact topLeadingCoeff_support hf hfb t

theorem topLeadingCoeff_full_const (hf : PolynomialInLayersLT p f)
    (hfb : BlockTotalDegreeLE deg f) :
    topLeadingCoeff c deg f p = MvPolynomial.C ((topLeadingCoeff c deg f p).coeff 0) := by
  classical
  have hs : PolynomialInLayersLT 0 (topLeadingCoeff c deg f p) := by
    simpa using topLeadingCoeff_support c deg f hf hfb p
  apply MvPolynomial.ext
  intro m
  by_cases hm : m = 0
  · subst m; simp
  · rw [MvPolynomial.coeff_C]
    have hz : (topLeadingCoeff c deg f p).coeff m = 0 := by
      by_contra hn
      apply hm
      ext y
      exact hs m (MvPolynomial.mem_support_iff.mpr hn) y (Nat.zero_le _)
    rw [if_neg (Ne.symm hm)]
    exact hz

theorem topLeadingCoeff_succ_extract (i : Nat) (hi : i < p) :
    topLeadingCoeff c deg f (p - i) =
      coeffOfVar (c.selectedVar ⟨i, hi⟩) deg
        (topLeadingCoeff c deg f (p - i - 1)) := by
  set t := p - i - 1 with ht
  have hpi : p - i = t + 1 := by omega
  have hidx : p - 1 - t = i := by omega
  have htp : t < p := by omega
  rw [hpi, topLeadingCoeff]
  simp only [htp, dif_pos]
  congr 1
  exact congrArg c.selectedVar (Fin.ext hidx)

noncomputable def genericTowerData : DominanceTowerData c f where
  degree := fun _ => deg
  leadingCoeff := fun i _ => topLeadingCoeff c deg f (p - i)
  lowerCoeff := fun i s => coeffOfVar (c.selectedVar i) s.1
    (topLeadingCoeff c deg f (p - i.1 - 1))
  topConstant := (topLeadingCoeff c deg f p).coeff 0

theorem genericTower_degree_pos (hdeg : 1 ≤ deg) :
    ∀ i : Fin p, 1 ≤ (genericTowerData c deg f).degree i := fun _ => hdeg

theorem genericTower_topConstant (hf : PolynomialInLayersLT p f)
    (hfb : BlockTotalDegreeLE deg f) :
    CanonicalTowerTopConstant (genericTowerData c deg f) := by
  intro z
  change evalFormalPolyComplex z (topLeadingCoeff c deg f (p - 0)) = _
  rw [Nat.sub_zero, topLeadingCoeff_full_const c deg f hf hfb]
  simp [evalFormalPolyComplex, genericTowerData]

theorem genericTower_finalCoeff : CanonicalTowerFinalCoeff (genericTowerData c deg f) := by
  change topLeadingCoeff c deg f (p - p) = f
  simp

theorem genericTower_leadingCoeff_support (hf : PolynomialInLayersLT p f)
    (hfb : BlockTotalDegreeLE deg f) :
    ∀ i (hi : i ≤ p), PolynomialInLayersLE i
      ((genericTowerData c deg f).leadingCoeff i hi) := by
  intro i hi
  have hs := topLeadingCoeff_support c deg f hf hfb (p - i)
  have heq : p - (p - i) = i := by omega
  rw [heq] at hs
  intro m hm y hy
  exact hs m hm y (by omega)

/-- Every lower coefficient used by a canonical dominance threshold is
supported in layers at most its tower stage. -/
theorem genericTower_lowerCoeff_support (hf : PolynomialInLayersLT p f)
    (hfb : BlockTotalDegreeLE deg f) :
    ∀ (i : Fin p) (s : Fin ((genericTowerData c deg f).degree i)),
      PolynomialInLayersLE i.1 ((genericTowerData c deg f).lowerCoeff i s) := by
  intro i s m hm y hy
  change m ∈ (coeffOfVar (c.selectedVar i) s.1
    (topLeadingCoeff c deg f (p - i.1 - 1))).support at hm
  rcases coeffOfVar_support_exists hm with ⟨u, hu, _hux, rfl⟩
  by_cases hyx : y = c.selectedVar i
  · subst y
    simp
  · rw [Finsupp.erase_ne hyx]
    have hs := topLeadingCoeff_support c deg f hf hfb (p - i.1 - 1)
    exact hs u hu y (by omega)

/-- The variable split off at a canonical tower stage is absent from every
lower coefficient used by that stage's dominance threshold. -/
theorem genericTower_lowerCoeff_notMem (hf : PolynomialInLayersLT p f)
    (hfb : BlockTotalDegreeLE deg f) :
    ∀ (i : Fin p) (s : Fin ((genericTowerData c deg f).degree i)),
      c.selectedVar i ∉ ((genericTowerData c deg f).lowerCoeff i s).vars := by
  intro i s
  exact coeffOfVar_notMem_vars

theorem genericTower_evalRecurrence (hfb : BlockTotalDegreeLE deg f) :
    CanonicalTowerEvalRecurrence (genericTowerData c deg f) := by
  classical
  intro i z
  set g := topLeadingCoeff c deg f (p - i.1 - 1)
  have hD : MvPolynomial.degreeOf (c.selectedVar i) g ≤ deg := by
    rw [MvPolynomial.degreeOf_le_iff]
    intro m hm
    have hsingle : m (c.selectedVar i) ≤ ∑ a : Fin k, m ((c.selectedVar i).1, a) := by
      simpa using Finset.single_le_sum (f := fun a => m ((c.selectedVar i).1, a))
        (fun a _ => Nat.zero_le _) (Finset.mem_univ (c.selectedVar i).2)
    exact le_trans hsingle (topLeadingCoeff_blockTotal c deg f hfb _ m hm _)
  have hlead := topLeadingCoeff_succ_extract c deg f i.1 i.2
  change evalFormalPolyComplex z (topLeadingCoeff c deg f (p - (i.1 + 1))) =
    evalFormalPolyComplex z (topLeadingCoeff c deg f (p - i.1)) *
      z (c.selectedVar i) ^ deg + ∑ s : Fin deg,
        evalFormalPolyComplex z (coeffOfVar (c.selectedVar i) s.1 g) *
          z (c.selectedVar i) ^ (s : Nat)
  have hlhs : p - (i.1 + 1) = p - i.1 - 1 := by omega
  rw [hlhs, hlead]
  have hsplit := evalFormalPolyComplex_eq_sum_coeffOfVar (x := c.selectedVar i)
    (D := deg) (f := g) hD z
  rw [hsplit, Finset.sum_range_succ]
  rw [← Fin.sum_univ_eq_sum_range
    (fun s => evalFormalPolyComplex z (coeffOfVar (c.selectedVar i) s g) *
      z (c.selectedVar i) ^ s) deg]
  exact add_comm _ _

end CanonicalTower

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

/-- Result interface for **NS100 lem-tower-dominance**. -/
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

/-- **NS100.E.lem-tower-dominance.S/P**.

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


/-- Pointwise coefficient of `coeffOfVar`: the `u`-coefficient of `coeffOfVar x s f`
is the `(u + s·x)`-coefficient of `f`, provided `u` has no `x`. -/
theorem coeffOfVar_coeff {L k : Nat} (x : FormalVar L k) (s : Nat)
    (f : FormalPoly L k) (u : FormalVar L k →₀ Nat) :
    (coeffOfVar x s f).coeff u =
      if u x = 0 then f.coeff (u + Finsupp.single x s) else 0 := by
  classical
  rw [coeffOfVar, MvPolynomial.coeff_sum]
  -- key: `erase x b = u` together with `b x = s` forces `b = u + single x s`,
  -- which in turn needs `u x = 0`.
  have hkey : ∀ b : FormalVar L k →₀ Nat, b x = s →
      (Finsupp.erase x b = u ↔ (u x = 0 ∧ b = u + Finsupp.single x s)) := by
    intro b hbx
    constructor
    · intro hb
      have hux0 : u x = 0 := by rw [← hb, Finsupp.erase_same]
      refine ⟨hux0, ?_⟩
      ext y
      rcases eq_or_ne y x with rfl | hyx
      · rw [Finsupp.add_apply, Finsupp.single_eq_same]; omega
      · have h1 : b y = u y := by
          have := Finsupp.ext_iff.mp hb y
          rwa [Finsupp.erase_ne hyx] at this
        have hs0 : (Finsupp.single x s) y = 0 := by
          rw [Finsupp.single_apply, if_neg]; exact fun h => hyx h.symm
        rw [Finsupp.add_apply, hs0]; omega
    · rintro ⟨hux0, rfl⟩
      ext y
      rcases eq_or_ne y x with rfl | hyx
      · rw [Finsupp.erase_same]; omega
      · have hs0 : (Finsupp.single x s) y = 0 := by
          rw [Finsupp.single_apply, if_neg]; exact fun h => hyx h.symm
        rw [Finsupp.erase_ne hyx, Finsupp.add_apply, hs0]; omega
  by_cases hux : u x = 0
  · rw [if_pos hux]
    by_cases hmem : (u + Finsupp.single x s) ∈ f.support.filter (fun m => m x = s)
    · rw [Finset.sum_eq_single (u + Finsupp.single x s)]
      · have herase : Finsupp.erase x (u + Finsupp.single x s) = u := by
          ext y; by_cases hyx : y = x
          · subst y; simp [hux]
          · simp [Finsupp.erase_ne hyx]
        rw [MvPolynomial.coeff_monomial, herase, if_pos rfl]
      · intro b hb hbne
        have hbx : b x = s := (Finset.mem_filter.mp hb).2
        rw [MvPolynomial.coeff_monomial, if_neg]
        intro hbu
        exact hbne (((hkey b hbx).mp hbu).2)
      · intro hnot; exact absurd hmem hnot
    · have hzero : f.coeff (u + Finsupp.single x s) = 0 := by
        by_contra hc
        exact hmem (Finset.mem_filter.mpr
          ⟨MvPolynomial.mem_support_iff.mpr hc, by simp [hux]⟩)
      rw [hzero]
      apply Finset.sum_eq_zero
      intro b hb
      have hbx : b x = s := (Finset.mem_filter.mp hb).2
      rw [MvPolynomial.coeff_monomial, if_neg]
      intro hbu
      exact hmem (by rw [← ((hkey b hbx).mp hbu).2]; exact hb)
  · rw [if_neg hux]
    apply Finset.sum_eq_zero
    intro b hb
    have hbx : b x = s := (Finset.mem_filter.mp hb).2
    rw [MvPolynomial.coeff_monomial, if_neg]
    intro hbu
    exact hux ((hkey b hbx).mp hbu).1

/-- Coefficient at `0` of one extraction step. -/
theorem coeffOfVar_coeff_zero {L k : Nat} (x : FormalVar L k) (s : Nat)
    (f : FormalPoly L k) :
    (coeffOfVar x s f).coeff 0 = f.coeff (Finsupp.single x s) := by
  rw [coeffOfVar_coeff]; simp

section Bridge

variable {L k p : Nat} (c : HeadChain L k p) (deg : Nat) (f : FormalPoly L k)

/-- Successor unfolding of `topLeadingCoeff` at the natural chain index. -/
theorem topLeadingCoeff_succ' (t : Nat) (ht : t < p) :
    topLeadingCoeff c deg f (t + 1) =
      coeffOfVar (c.selectedVar ⟨p - 1 - t, by omega⟩) deg (topLeadingCoeff c deg f t) := by
  rw [topLeadingCoeff]
  simp only [ht, dif_pos]

/-- Layers of distinct chain positions differ, so their selected variables differ. -/
theorem selectedVar_ne_of_ne {i j : Fin p} (hij : i.1 ≠ j.1) :
    c.selectedVar i ≠ c.selectedVar j := by
  intro h
  apply hij
  have := congrArg (fun x : FormalVar L k => x.1.1) h
  simpa [HeadChain.selectedVar, HeadChain.layer] using this

/-- Bridge: the fully-iterated top extraction's constant term is a single
selected-monomial coefficient of `f`. -/
theorem topLeadingCoeff_coeff_zero :
    (topLeadingCoeff c deg f p).coeff 0 =
      f.coeff (∑ i : Fin p, Finsupp.single (c.selectedVar i) deg) := by
  classical
  -- generalized statement over the extraction count `t` and a base exponent `u`
  suffices hgen : ∀ t : Nat, t ≤ p → ∀ u : FormalVar L k →₀ Nat,
      (∀ i : Fin p, p - t ≤ i.1 → u (c.selectedVar i) = 0) →
      (topLeadingCoeff c deg f t).coeff u =
        f.coeff (u + ∑ i ∈ Finset.univ.filter (fun i : Fin p => p - t ≤ i.1),
          Finsupp.single (c.selectedVar i) deg) by
    have := hgen p le_rfl 0 (by intro i hi; simp)
    simpa using this
  intro t
  induction t with
  | zero =>
      intro _ u _
      have hempty : Finset.univ.filter (fun i : Fin p => p - 0 ≤ i.1) = ∅ :=
        Finset.filter_eq_empty_iff.mpr (fun i _ => by omega)
      rw [hempty, Finset.sum_empty, add_zero]
      simp [topLeadingCoeff]
  | succ t ih =>
      intro ht u hu
      have htp : t < p := by omega
      rw [topLeadingCoeff_succ' c deg f t htp, coeffOfVar_coeff]
      set j : Fin p := ⟨p - 1 - t, by omega⟩ with hj
      have hjv : (j : Nat) = p - 1 - t := rfl
      have huj : u (c.selectedVar j) = 0 := by
        apply hu j; omega
      rw [if_pos huj]
      have hu' : ∀ i : Fin p, p - t ≤ i.1 →
          (u + Finsupp.single (c.selectedVar j) deg) (c.selectedVar i) = 0 := by
        intro i hi
        rw [Finsupp.add_apply]
        have h1 : u (c.selectedVar i) = 0 := hu i (by omega)
        have h2 : Finsupp.single (c.selectedVar j) deg (c.selectedVar i) = 0 := by
          rw [Finsupp.single_apply, if_neg]
          exact fun h => (selectedVar_ne_of_ne c (by omega)) h.symm
        rw [h1, h2]
      rw [ih (by omega) _ hu']
      have hfilter :
          Finset.univ.filter (fun i : Fin p => p - (t + 1) ≤ i.1) =
            insert j (Finset.univ.filter (fun i : Fin p => p - t ≤ i.1)) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · intro hle
          rcases Nat.lt_or_ge i.1 (p - t) with hlt | hge
          · left; apply Fin.ext; omega
          · right; exact hge
        · rintro (rfl | hge)
          · omega
          · omega
      have hjnotmem : j ∉ Finset.univ.filter (fun i : Fin p => p - t ≤ i.1) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      rw [hfilter, Finset.sum_insert hjnotmem,
        add_assoc u (Finsupp.single (c.selectedVar j) deg)]

end Bridge


end

end TransformerIdentifiability.NLayer.NoSkip
