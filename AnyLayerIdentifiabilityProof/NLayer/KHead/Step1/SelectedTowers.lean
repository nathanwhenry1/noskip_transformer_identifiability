import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.DominanceSibling
import AnyLayerIdentifiabilityProof.NLayer.KHead.Step1.Hypotheses

set_option autoImplicit false

open Matrix

namespace TransformerIdentifiability.NLayer.KHead.Step1

/-!
# Selected Step 1 tower bookkeeping

This file contains the edit-safe selected-branch declarations used by the Step 1
tier cascade.  It deliberately stops before constructing the hard selected
tower polynomials: the declarations here are the finite member/index skeleton
and the nonvanishing constants supplied directly by the separated-probe
hypotheses.
-/

/-! ## Selected chain adapters -/

/-- Selected head along the Step 1 cascade chain for a fixed first-layer head. -/
def step1SelectedHead {m k d : Nat} {θ : Params (m + 1) k d}
    (chains : Step1ChainChoices θ) (h : Fin k) : Nat -> Fin k
  | 0 => h
  | j + 1 =>
      if hj : j < m then
        (chains h).chain ⟨j, hj⟩
      else h

@[simp]
theorem step1SelectedHead_zero {m k d : Nat} {θ : Params (m + 1) k d}
    (chains : Step1ChainChoices θ) (h : Fin k) :
    step1SelectedHead chains h 0 = h :=
  rfl

@[simp]
theorem step1SelectedHead_succ_of_lt {m k d : Nat} {θ : Params (m + 1) k d}
    (chains : Step1ChainChoices θ) (h : Fin k) {j : Nat} (hj : j < m) :
    step1SelectedHead chains h (j + 1) = (chains h).chain ⟨j, hj⟩ := by
  simp [step1SelectedHead, hj]

@[simp]
theorem step1SelectedHead_succ_of_not_lt {m k d : Nat} {θ : Params (m + 1) k d}
    (chains : Step1ChainChoices θ) (h : Fin k) {j : Nat} (hj : ¬ j < m) :
    step1SelectedHead chains h (j + 1) = h := by
  simp [step1SelectedHead, hj]

/-- K04E head-chain adapter for the selected Step 1 branch up to tier `j`. -/
def step1HeadChain {m k d : Nat} {θ : Params (m + 1) k d}
    (chains : Step1ChainChoices θ) (h : Fin k) (j : Nat) (hj : j ≤ m + 1) :
    HeadChain (m + 1) k j where
  head := fun i => step1SelectedHead chains h i.1
  length_le := hj

@[simp]
theorem step1HeadChain_head {m k d : Nat} {θ : Params (m + 1) k d}
    (chains : Step1ChainChoices θ) (h : Fin k) {j : Nat} (hj : j ≤ m + 1)
    (i : Fin j) :
    (step1HeadChain chains h j hj).head i = step1SelectedHead chains h i.1 :=
  rfl

@[simp]
theorem step1HeadChain_layer {m k d : Nat} {θ : Params (m + 1) k d}
    (chains : Step1ChainChoices θ) (h : Fin k) {j : Nat} (hj : j ≤ m + 1)
    (i : Fin j) :
    (step1HeadChain chains h j hj).layer i =
      ⟨i.1, Nat.lt_of_lt_of_le i.2 hj⟩ :=
  rfl

@[simp]
theorem step1HeadChain_selectedVar {m k d : Nat} {θ : Params (m + 1) k d}
    (chains : Step1ChainChoices θ) (h : Fin k) {j : Nat} (hj : j ≤ m + 1)
    (i : Fin j) :
    (step1HeadChain chains h j hj).selectedVar i =
      (⟨i.1, Nat.lt_of_lt_of_le i.2 hj⟩, step1SelectedHead chains h i.1) :=
  rfl

theorem step1HeadChain_selectedValueProduct_prefix {m k d : Nat}
    {θ : Params (m + 1) k d} (chains : Step1ChainChoices θ) (h : Fin k)
    (N n : Nat) (hN : N ≤ m + 1) (hn : n ≤ N) :
    HeadChain.selectedValueProduct θ (step1HeadChain chains h N hN) n hn =
      HeadChain.selectedValueProduct θ
        (step1HeadChain chains h n (Nat.le_trans hn hN)) n le_rfl := by
  revert N
  induction n with
  | zero =>
      intro N hN hn
      rfl
  | succ n ih =>
      intro N hN hn
      rw [HeadChain.selectedValueProduct_succ, HeadChain.selectedValueProduct_succ]
      have hnN : n ≤ N := Nat.le_trans (Nat.le_succ n) hn
      have hleft := ih N hN hnN
      have hright := ih (n + 1) (Nat.le_trans hn hN) (Nat.le_succ n)
      rw [hleft, hright]
      simp [HeadChain.layer, step1HeadChain]

theorem step1HeadChain_selectedValueProduct_eq_cascadeProduct {m k d : Nat}
    {θ : Params (m + 1) k d} (chains : Step1ChainChoices θ) (h : Fin k)
    (n : Nat) (hn : n ≤ m) :
    HeadChain.selectedValueProduct θ
        (step1HeadChain chains h (n + 1) (Nat.succ_le_succ hn)) (n + 1) le_rfl =
      cascadeProduct θ h (chains h).chain n := by
  induction n with
  | zero =>
      simp [HeadChain.selectedValueProduct, step1HeadChain, cascadeProduct, HeadChain.layer]
  | succ n ih =>
      have hnlt : n < m := Nat.lt_of_succ_le hn
      have hnle : n ≤ m := Nat.le_of_lt hnlt
      rw [HeadChain.selectedValueProduct_succ]
      have hprefix :=
        step1HeadChain_selectedValueProduct_prefix (θ := θ) chains h (n + 2) (n + 1)
          (Nat.succ_le_succ hn) (Nat.le_succ (n + 1))
      rw [hprefix, ih hnle]
      simp [cascadeProduct, hnlt, HeadChain.layer, step1HeadChain, laterLayer]

theorem step1HeadChain_selectedValueProduct_eq_cascadeProduct_fin {m k d : Nat}
    {θ : Params (m + 1) k d} (chains : Step1ChainChoices θ) (h : Fin k)
    (s : Fin m) :
    HeadChain.selectedValueProduct θ
        (step1HeadChain chains h (s.1 + 1)
          (Nat.succ_le_succ (Nat.le_of_lt s.2))) (s.1 + 1) le_rfl =
      cascadeProduct θ h (chains h).chain s.1 :=
  step1HeadChain_selectedValueProduct_eq_cascadeProduct (θ := θ) chains h s.1
    (Nat.le_of_lt s.2)

theorem step1HeadChain_selectedValueProduct_eq_cascadeFinalProduct {m k d : Nat}
    {θ : Params (m + 1) k d} (chains : Step1ChainChoices θ) (h : Fin k) :
    HeadChain.selectedValueProduct θ
        (step1HeadChain chains h (m + 1) le_rfl) (m + 1) le_rfl =
      cascadeFinalProduct θ h (chains h).chain := by
  simpa [cascadeFinalProduct] using
    step1HeadChain_selectedValueProduct_eq_cascadeProduct (θ := θ) chains h m le_rfl

theorem step1HeadChain_selectedValueProduct_mulVec_eq_cascadeResidueVector {m k d : Nat}
    {θ : Params (m + 1) k d} (chains : Step1ChainChoices θ)
    (p : ProbePoint d) (h : Fin k) :
    HeadChain.selectedValueProduct θ
        (step1HeadChain chains h (m + 1) le_rfl) (m + 1) le_rfl *ᵥ p.1 =
      cascadeResidueVector (chains h) p := by
  rw [step1HeadChain_selectedValueProduct_eq_cascadeFinalProduct]
  rfl

/-! ## Ignition quadratic bridges -/

theorem matrixBilin_sym_self {d : Nat}
    (M : Matrix (Fin d) (Fin d) ℝ) (w : Vec d) :
    matrixBilin (sym M) w w = matrixBilin M w w := by
  have hT : w ⬝ᵥ Mᵀ *ᵥ w = w ⬝ᵥ M *ᵥ w := by
    simpa using Matrix.dotProduct_transpose_mulVec (A := M) (x := w) (y := w)
  simp [matrixBilin, sym, Matrix.add_mulVec, Matrix.smul_mulVec, hT]
  ring

theorem matrixBilin_transpose_mul_mul_self {d : Nat}
    (A P : Matrix (Fin d) (Fin d) ℝ) (w : Vec d) :
    matrixBilin (Pᵀ * A * P) w w =
      matrixBilin A (P *ᵥ w) (P *ᵥ w) := by
  calc
    matrixBilin (Pᵀ * A * P) w w
        = w ⬝ᵥ Pᵀ *ᵥ ((A * P) *ᵥ w) := by
          simp [matrixBilin, Matrix.mul_assoc, Matrix.mulVec_mulVec]
    _ = ((A * P) *ᵥ w) ⬝ᵥ P *ᵥ w := by
          exact Matrix.dotProduct_transpose_mulVec (A := P) (x := w)
            (y := (A * P) *ᵥ w)
    _ = matrixBilin A (P *ᵥ w) (P *ᵥ w) := by
          rw [dotProduct_comm]
          simp [matrixBilin, Matrix.mulVec_mulVec]

theorem matrixBilin_sym_transpose_mul_mul_self {d : Nat}
    (A P : Matrix (Fin d) (Fin d) ℝ) (w : Vec d) :
    matrixBilin (sym (Pᵀ * A * P)) w w =
      matrixBilin A (P *ᵥ w) (P *ᵥ w) := by
  rw [matrixBilin_sym_self, matrixBilin_transpose_mul_mul_self]

theorem step1IgnitionQuadratic_eq_selectedValueProduct_laterLayer {m k d r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) (h : Fin k) (s : Fin m) :
    matrixBilin (attentionMatrix θ' (laterLayer s) ((H.chains h).chain s))
      (HeadChain.selectedValueProduct θ'
        (step1HeadChain H.chains h (s.1 + 1)
          (Nat.succ_le_succ (Nat.le_of_lt s.2)))
        (s.1 + 1) le_rfl *ᵥ p.1)
      (HeadChain.selectedValueProduct θ'
        (step1HeadChain H.chains h (s.1 + 1)
          (Nat.succ_le_succ (Nat.le_of_lt s.2)))
        (s.1 + 1) le_rfl *ᵥ p.1) =
    cascadeIgnitionQuadratic (H.chains h) s p := by
  rw [step1HeadChain_selectedValueProduct_eq_cascadeProduct_fin]
  rw [cascadeIgnitionQuadratic, cascadeIgnitionMatrix,
    matrixBilin_sym_transpose_mul_mul_self]

theorem step1IgnitionQuadratic_eq_selectedValueProduct {m k d r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) (h : Fin k) (s : Fin m) :
    matrixBilin (attentionMatrix θ' ⟨s.1 + 1, Nat.succ_lt_succ s.2⟩
        (step1SelectedHead H.chains h (s.1 + 1)))
      (HeadChain.selectedValueProduct θ'
        (step1HeadChain H.chains h (s.1 + 1)
          (Nat.succ_le_succ (Nat.le_of_lt s.2)))
        (s.1 + 1) le_rfl *ᵥ p.1)
      (HeadChain.selectedValueProduct θ'
        (step1HeadChain H.chains h (s.1 + 1)
          (Nat.succ_le_succ (Nat.le_of_lt s.2)))
        (s.1 + 1) le_rfl *ᵥ p.1) =
    cascadeIgnitionQuadratic (H.chains h) s p := by
  simpa [laterLayer, step1SelectedHead, s.2] using
    step1IgnitionQuadratic_eq_selectedValueProduct_laterLayer H p h s

/-! ## Separated-probe nonvanishing facts -/

theorem cascadeProbeIgnition_residue_ne_zero {m k d : Nat}
    {θ : Params (m + 1) k d} {chains : Step1ChainChoices θ}
    {p : ProbePoint d} (hcas : CascadeProbeIgnition chains p) (h : Fin k) :
    cascadeResidueVector (chains h) p ≠ 0 :=
  (hcas h).1

theorem cascadeProbeIgnition_ignition_ne_zero {m k d : Nat}
    {θ : Params (m + 1) k d} {chains : Step1ChainChoices θ}
    {p : ProbePoint d} (hcas : CascadeProbeIgnition chains p)
    (h : Fin k) (j : Fin m) :
    cascadeIgnitionQuadratic (chains h) j p ≠ 0 :=
  (hcas h).2 j

theorem separatedProbe_cascadeProbeIgnition {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    {p : ProbePoint d} (hp : p ∈ H.separatedSet) :
    CascadeProbeIgnition H.chains p :=
  hp.2.1

theorem separatedProbe_residue_ne_zero {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    {p : ProbePoint d} (hp : p ∈ H.separatedSet) (h : Fin k) :
    cascadeResidueVector (H.chains h) p ≠ 0 :=
  cascadeProbeIgnition_residue_ne_zero (separatedProbe_cascadeProbeIgnition H hp) h

theorem separatedProbe_ignition_ne_zero {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    {p : ProbePoint d} (hp : p ∈ H.separatedSet)
    (h : Fin k) (j : Fin m) :
    cascadeIgnitionQuadratic (H.chains h) j p ≠ 0 :=
  cascadeProbeIgnition_ignition_ne_zero (separatedProbe_cascadeProbeIgnition H hp) h j

theorem separatedProbe_exists_residueCoordinate_ne_zero {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    {p : ProbePoint d} (hp : p ∈ H.separatedSet) (h : Fin k) :
    ∃ ι : Fin d, cascadeResidueVector (H.chains h) p ι ≠ 0 := by
  have hres := separatedProbe_residue_ne_zero H hp h
  by_contra hnone
  apply hres
  funext ι
  by_contra hι
  exact hnone ⟨ι, hι⟩

/-! ## All-`alpha` formal corner evaluations -/

@[simp]
theorem gatedValueSum_const {L k d : Nat} (θ : Params L k d)
    (l : Fin L) (α : ℝ) :
    gatedValueSum θ l (fun _ : Fin k => α) = α • valueSum θ l := by
  simp [gatedValueSum, valueSum, Finset.smul_sum]

theorem evalFormalVec_allAlpha_formalPoint {L k d : Nat} (r : Nat)
    (θ : Params L k d) (w v : Vec d) :
    ∀ (n : Nat) (hn : n ≤ L),
      evalFormalVec (fun _ : FormalVar L k => alpha r)
          (formalPoint θ w v n hn).1 =
        cornerKPrefix r θ n *ᵥ w ∧
      evalFormalVec (fun _ : FormalVar L k => alpha r)
          (formalPoint θ w v n hn).2 =
        cornerCPrefix θ n *ᵥ v + cornerDPrefix r θ n *ᵥ w
  | 0, _hn => by
      simp [formalPoint, cornerKPrefix, cornerCPrefix, matrixPrefixProduct]
  | n + 1, hn => by
      let ρ : FormalVar L k → ℝ := fun _ => alpha r
      have hnlt : n < L := Nat.lt_of_succ_le hn
      let l : Fin L := ⟨n, hnlt⟩
      have hprev :=
        evalFormalVec_allAlpha_formalPoint r θ w v n (Nat.le_of_succ_le hn)
      have hprevW :
          evalFormalVec ρ (formalW θ w v n (Nat.le_of_succ_le hn)) =
            cornerKPrefix r θ n *ᵥ w := by
        simpa [ρ, formalW] using hprev.1
      have hprevV :
          evalFormalVec ρ (formalV θ w v n (Nat.le_of_succ_le hn)) =
            cornerCPrefix θ n *ᵥ v + cornerDPrefix r θ n *ᵥ w := by
        simpa [ρ, formalV] using hprev.2
      have hstreamC : collapseMatrixStream θ n = collapseMatrix θ l := by
        dsimp [collapseMatrixStream]
        split
        · congr
        · contradiction
      have hstreamV : valueSumStream θ n = valueSum θ l := by
        dsimp [valueSumStream]
        split
        · congr
        · contradiction
      constructor
      · calc
          evalFormalVec ρ (formalPoint θ w v (n + 1) hn).1
              =
                (gatedEffectivePoint θ l (fun _ : Fin k => alpha r)
                  (evalFormalVec ρ (formalW θ w v n (Nat.le_of_succ_le hn)))
                  (evalFormalVec ρ (formalV θ w v n (Nat.le_of_succ_le hn)))).1 := by
                    simp [formalPoint, l, eval_formalStepPoint_fst, ρ, formalW, formalV]
          _ =
                (collapseMatrix θ l - alpha r • valueSum θ l) *ᵥ
                  (cornerKPrefix r θ n *ᵥ w) := by
                    simp [hprevW]
          _ = cornerKPrefix r θ (n + 1) *ᵥ w := by
                    rw [Matrix.mulVec_mulVec]
                    simp [cornerKPrefix, cornerKStream, hstreamC, hstreamV]
      · calc
          evalFormalVec ρ (formalPoint θ w v (n + 1) hn).2
              =
                (gatedEffectivePoint θ l (fun _ : Fin k => alpha r)
                  (evalFormalVec ρ (formalW θ w v n (Nat.le_of_succ_le hn)))
                  (evalFormalVec ρ (formalV θ w v n (Nat.le_of_succ_le hn)))).2 := by
                    simp [formalPoint, l, eval_formalStepPoint_snd, ρ, formalW, formalV]
          _ =
                collapseMatrix θ l *ᵥ
                    (cornerCPrefix θ n *ᵥ v + cornerDPrefix r θ n *ᵥ w) +
                  (alpha r • valueSum θ l) *ᵥ
                    (cornerKPrefix r θ n *ᵥ w) := by
                    simp [hprevW, hprevV]
          _ = cornerCPrefix θ (n + 1) *ᵥ v +
                cornerDPrefix r θ (n + 1) *ᵥ w := by
                    simp [cornerCPrefix, hstreamC, hstreamV, Matrix.mulVec_add,
                      Matrix.add_mulVec, Matrix.mulVec_mulVec, add_assoc]

theorem evalFormalVec_allAlpha_formalW {L k d : Nat} (r : Nat)
    (θ : Params L k d) (w v : Vec d) (n : Nat) (hn : n ≤ L) :
    evalFormalVec (fun _ : FormalVar L k => alpha r) (formalW θ w v n hn) =
      cornerKPrefix r θ n *ᵥ w :=
  (evalFormalVec_allAlpha_formalPoint r θ w v n hn).1

theorem evalFormalVec_allAlpha_formalV {L k d : Nat} (r : Nat)
    (θ : Params L k d) (w v : Vec d) (n : Nat) (hn : n ≤ L) :
    evalFormalVec (fun _ : FormalVar L k => alpha r) (formalV θ w v n hn) =
      cornerCPrefix θ n *ᵥ v + cornerDPrefix r θ n *ᵥ w :=
  (evalFormalVec_allAlpha_formalPoint r θ w v n hn).2

/-- Real formal slope differences at the all-`alpha` assignment are the
corner-slope bilinear forms. -/
theorem evalFormal_slopeDiff_corner_real {m k d : Nat} (r : Nat)
    (θ : Params (m + 1) k d) (p : ProbePoint d)
    (l : Fin (m + 1)) (a c : Fin k) :
    MvPolynomial.eval (fun _ : FormalVar (m + 1) k => alpha r)
        (formalSlope θ p.1 p.2 l a - formalSlope θ p.1 p.2 l c) =
      cornerSlopeDiffAt r θ l a c p := by
  rw [MvPolynomial.eval_sub, eval_formalSlope, eval_formalSlope]
  rw [evalFormalVec_allAlpha_formalW, evalFormalVec_allAlpha_formalV]
  simp [cornerSlopeDiffAt, matrixBilin, Matrix.sub_mulVec, dotProduct_sub]

/-- The formal slope difference evaluated at the constant all-`alpha` corner
assignment is the `(R3)` corner bilinear form. -/
theorem evalFormal_slopeDiff_corner {m k d : Nat} (r : Nat)
    (θ : Params (m + 1) k d) (p : ProbePoint d)
    (l : Fin (m + 1)) (a c : Fin k) :
    evalFormalPolyComplex (fun _ : FormalVar (m + 1) k => (alpha r : ℂ))
        (formalSlope θ p.1 p.2 l a - formalSlope θ p.1 p.2 l c) =
      (cornerSlopeDiffAt r θ l a c p : ℂ) := by
  rw [evalFormalPolyComplex_ofReal]
  exact_mod_cast evalFormal_slopeDiff_corner_real r θ p l a c

/-! ## Canonical finite member indices -/

/-- Residue coordinates that actually occur in the selected final residue vector. -/
abbrev Step1ResidueCoordinateIndex {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) (h : Fin k) : Type :=
  {ι : Fin d // cascadeResidueVector (H.chains h) p ι ≠ 0}

noncomputable instance step1ResidueCoordinateIndex_fintype {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) (h : Fin k) :
    Fintype (Step1ResidueCoordinateIndex H p h) := by
  classical
  infer_instance

theorem step1ResidueCoordinateIndex_nonempty {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    {p : ProbePoint d} (hp : p ∈ H.separatedSet) (h : Fin k) :
    Nonempty (Step1ResidueCoordinateIndex H p h) := by
  rcases separatedProbe_exists_residueCoordinate_ne_zero H hp h with ⟨ι, hι⟩
  exact ⟨⟨ι, hι⟩⟩

/-- Canonical finite dominance-family member indices: ignition members plus
nonzero residue-coordinate members. -/
abbrev Step1TowerMemberIndex {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) (h : Fin k) : Type :=
  Fin m ⊕ Step1ResidueCoordinateIndex H p h

noncomputable instance step1TowerMemberIndex_fintype {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) (h : Fin k) :
    Fintype (Step1TowerMemberIndex H p h) := by
  classical
  infer_instance

theorem step1TowerMemberIndex_nonempty {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    {p : ProbePoint d} (hp : p ∈ H.separatedSet) (h : Fin k) :
    Nonempty (Step1TowerMemberIndex H p h) := by
  exact ⟨Sum.inr (Classical.choice (step1ResidueCoordinateIndex_nonempty H hp h))⟩

theorem step1TowerMemberIndex_card {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) (h : Fin k) :
    Fintype.card (Step1TowerMemberIndex H p h) =
      m + Fintype.card (Step1ResidueCoordinateIndex H p h) := by
  classical
  simp [Step1TowerMemberIndex]

/-- Number of selected variables used by a canonical member tower. -/
def step1TowerMemberChainLength {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) (h : Fin k) (idx : Step1TowerMemberIndex H p h) : Nat :=
  match idx with
  | Sum.inl s => s.1
  | Sum.inr _ => m

@[simp]
theorem step1TowerMemberChainLength_ignition {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) (h : Fin k) (s : Fin m) :
    step1TowerMemberChainLength H p h
      (Sum.inl s : Step1TowerMemberIndex H p h) = s.1 :=
  rfl

@[simp]
theorem step1TowerMemberChainLength_residue {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) (h : Fin k) (ι : Step1ResidueCoordinateIndex H p h) :
    step1TowerMemberChainLength H p h
      (Sum.inr ι : Step1TowerMemberIndex H p h) = m :=
  rfl

theorem step1TowerMemberChainLength_le_m {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) (h : Fin k) (idx : Step1TowerMemberIndex H p h) :
    step1TowerMemberChainLength H p h idx ≤ m := by
  cases idx with
  | inl s => exact Nat.le_of_lt s.2
  | inr _ => exact le_rfl

theorem step1TowerMemberChainLength_le_depth {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) (h : Fin k) (idx : Step1TowerMemberIndex H p h) :
    step1TowerMemberChainLength H p h idx ≤ m + 1 :=
  Nat.le_trans (step1TowerMemberChainLength_le_m H p h idx) (Nat.le_succ m)

/-- Selected head-chain prefix attached to a canonical finite-family member. -/
def step1TowerMemberHeadChain {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) (h : Fin k) (idx : Step1TowerMemberIndex H p h) :
    HeadChain (m + 1) k (step1TowerMemberChainLength H p h idx) :=
  step1HeadChain H.chains h (step1TowerMemberChainLength H p h idx)
    (step1TowerMemberChainLength_le_depth H p h idx)

@[simp]
theorem step1TowerMemberHeadChain_head {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) (h : Fin k) (idx : Step1TowerMemberIndex H p h)
    (i : Fin (step1TowerMemberChainLength H p h idx)) :
    (step1TowerMemberHeadChain H p h idx).head i =
      step1SelectedHead H.chains h i.1 :=
  rfl

/-! ## Top constants carried by the separated-probe package -/

/-- Top constant for the ignition member attached to stage `s`. -/
noncomputable def step1IgnitionTopConstant {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) (h : Fin k) (s : Fin m) : ℝ :=
  -cascadeIgnitionQuadratic (H.chains h) s p

/-- Top constant for the residue member attached to a nonzero coordinate. -/
noncomputable def step1ResidueTopConstant {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) (h : Fin k) (_ι : Step1ResidueCoordinateIndex H p h) : ℝ :=
  (-1 : ℝ) ^ m * cascadeResidueVector (H.chains h) p _ι.1

theorem step1IgnitionTopConstant_ne_zero {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    {p : ProbePoint d} (hp : p ∈ H.separatedSet) (h : Fin k) (s : Fin m) :
    step1IgnitionTopConstant H p h s ≠ 0 := by
  simpa [step1IgnitionTopConstant] using
    (neg_ne_zero.mpr (separatedProbe_ignition_ne_zero H hp h s))

theorem step1ResidueTopConstant_ne_zero {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) (h : Fin k) (ι : Step1ResidueCoordinateIndex H p h) :
    step1ResidueTopConstant H p h ι ≠ 0 := by
  have hsign : ((-1 : ℝ) ^ m) ≠ 0 := pow_ne_zero m (by norm_num)
  exact mul_ne_zero hsign ι.2

theorem step1ResidueTopConstant_eq_selectedValueProduct {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) (h : Fin k) (ι : Step1ResidueCoordinateIndex H p h) :
    step1ResidueTopConstant H p h ι =
      (-1 : ℝ) ^ m *
        (HeadChain.selectedValueProduct θ'
            (step1HeadChain H.chains h (m + 1) le_rfl) (m + 1) le_rfl *ᵥ p.1) ι.1 := by
  rw [step1HeadChain_selectedValueProduct_mulVec_eq_cascadeResidueVector]
  rfl

theorem step1IgnitionTopConstant_eq_selectedValueProduct {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) (h : Fin k) (s : Fin m) :
    step1IgnitionTopConstant H p h s =
      -matrixBilin (attentionMatrix θ' ⟨s.1 + 1, Nat.succ_lt_succ s.2⟩
          (step1SelectedHead H.chains h (s.1 + 1)))
        (HeadChain.selectedValueProduct θ'
          (step1HeadChain H.chains h (s.1 + 1)
            (Nat.succ_le_succ (Nat.le_of_lt s.2)))
          (s.1 + 1) le_rfl *ᵥ p.1)
        (HeadChain.selectedValueProduct θ'
          (step1HeadChain H.chains h (s.1 + 1)
            (Nat.succ_le_succ (Nat.le_of_lt s.2)))
          (s.1 + 1) le_rfl *ᵥ p.1) := by
  rw [step1IgnitionTopConstant,
    ← step1IgnitionQuadratic_eq_selectedValueProduct H p h s]

/-! ## Planned dominance-family names -/

/-- C3-facing alias for the canonical selected dominance-family member indices. -/
abbrev Step1DominanceFamilyIndex {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) (h : Fin k) : Type :=
  Step1TowerMemberIndex H p h

noncomputable instance step1DominanceFamilyIndex_fintype {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) (h : Fin k) :
    Fintype (Step1DominanceFamilyIndex H p h) := by
  classical
  infer_instance

theorem step1DominanceFamilyIndex_nonempty {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    {p : ProbePoint d} (hp : p ∈ H.separatedSet) (h : Fin k) :
    Nonempty (Step1DominanceFamilyIndex H p h) := by
  simpa [Step1DominanceFamilyIndex] using step1TowerMemberIndex_nonempty H hp h

theorem step1DominanceFamilyIndex_card {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) (h : Fin k) :
    Fintype.card (Step1DominanceFamilyIndex H p h) =
      m + Fintype.card (Step1ResidueCoordinateIndex H p h) := by
  simp [Step1DominanceFamilyIndex, step1TowerMemberIndex_card H p h]

/-- Number of selected variables used by a C3-facing dominance-family member. -/
def step1DominanceFamilyChainLength {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) (h : Fin k) (idx : Step1DominanceFamilyIndex H p h) : Nat :=
  step1TowerMemberChainLength H p h idx

@[simp]
theorem step1DominanceFamilyChainLength_ignition {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) (h : Fin k) (s : Fin m) :
    step1DominanceFamilyChainLength H p h
      (Sum.inl s : Step1DominanceFamilyIndex H p h) = s.1 :=
  rfl

@[simp]
theorem step1DominanceFamilyChainLength_residue {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) (h : Fin k) (ι : Step1ResidueCoordinateIndex H p h) :
    step1DominanceFamilyChainLength H p h
      (Sum.inr ι : Step1DominanceFamilyIndex H p h) = m :=
  rfl

theorem step1DominanceFamilyChainLength_eq {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) (h : Fin k) (idx : Step1DominanceFamilyIndex H p h) :
    step1DominanceFamilyChainLength H p h idx =
      step1TowerMemberChainLength H p h idx :=
  rfl

theorem step1DominanceFamilyChainLength_le_m {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) (h : Fin k) (idx : Step1DominanceFamilyIndex H p h) :
    step1DominanceFamilyChainLength H p h idx ≤ m :=
  step1TowerMemberChainLength_le_m H p h idx

theorem step1DominanceFamilyChainLength_le_depth {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) (h : Fin k) (idx : Step1DominanceFamilyIndex H p h) :
    step1DominanceFamilyChainLength H p h idx ≤ m + 1 :=
  step1TowerMemberChainLength_le_depth H p h idx

/-- Selected head-chain prefix attached to a C3-facing dominance-family member. -/
def step1DominanceFamilyHeadChain {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) (h : Fin k) (idx : Step1DominanceFamilyIndex H p h) :
    HeadChain (m + 1) k (step1DominanceFamilyChainLength H p h idx) :=
  step1HeadChain H.chains h (step1DominanceFamilyChainLength H p h idx)
    (step1DominanceFamilyChainLength_le_depth H p h idx)

theorem step1DominanceFamilyHeadChain_eq {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) (h : Fin k) (idx : Step1DominanceFamilyIndex H p h) :
    step1DominanceFamilyHeadChain H p h idx =
      step1TowerMemberHeadChain H p h idx :=
  rfl

@[simp]
theorem step1DominanceFamilyHeadChain_head {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) (h : Fin k) (idx : Step1DominanceFamilyIndex H p h)
    (i : Fin (step1DominanceFamilyChainLength H p h idx)) :
    (step1DominanceFamilyHeadChain H p h idx).head i =
      step1SelectedHead H.chains h i.1 :=
  rfl

@[simp]
theorem step1DominanceFamilyHeadChain_layer {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) (h : Fin k) (idx : Step1DominanceFamilyIndex H p h)
    (i : Fin (step1DominanceFamilyChainLength H p h idx)) :
    (step1DominanceFamilyHeadChain H p h idx).layer i =
      ⟨i.1,
        Nat.lt_of_lt_of_le i.2
          (step1DominanceFamilyChainLength_le_depth H p h idx)⟩ :=
  rfl

@[simp]
theorem step1DominanceFamilyHeadChain_selectedVar {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) (h : Fin k) (idx : Step1DominanceFamilyIndex H p h)
    (i : Fin (step1DominanceFamilyChainLength H p h idx)) :
    (step1DominanceFamilyHeadChain H p h idx).selectedVar i =
      (⟨i.1,
        Nat.lt_of_lt_of_le i.2
          (step1DominanceFamilyChainLength_le_depth H p h idx)⟩,
        step1SelectedHead H.chains h i.1) :=
  rfl

/-- Data tag recording whether a dominance-family index names an ignition or residue member. -/
inductive Step1DominanceFamilyMemberKind : Type
  | ignition
  | residue

/-- The data tag attached to a C3-facing dominance-family index. -/
def step1DominanceFamilyMemberKind {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) (h : Fin k) (idx : Step1DominanceFamilyIndex H p h) :
    Step1DominanceFamilyMemberKind :=
  match idx with
  | Sum.inl _ => Step1DominanceFamilyMemberKind.ignition
  | Sum.inr _ => Step1DominanceFamilyMemberKind.residue

@[simp]
theorem step1DominanceFamilyMemberKind_ignition {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) (h : Fin k) (s : Fin m) :
    step1DominanceFamilyMemberKind H p h
      (Sum.inl s : Step1DominanceFamilyIndex H p h) =
        Step1DominanceFamilyMemberKind.ignition :=
  rfl

@[simp]
theorem step1DominanceFamilyMemberKind_residue {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) (h : Fin k) (ι : Step1ResidueCoordinateIndex H p h) :
    step1DominanceFamilyMemberKind H p h
      (Sum.inr ι : Step1DominanceFamilyIndex H p h) =
        Step1DominanceFamilyMemberKind.residue :=
  rfl

/-- Top constant carried by a C3-facing dominance-family member index. -/
noncomputable def step1DominanceFamilyTopConstant {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) (h : Fin k) (idx : Step1DominanceFamilyIndex H p h) : ℝ :=
  match idx with
  | Sum.inl s => step1IgnitionTopConstant H p h s
  | Sum.inr ι => step1ResidueTopConstant H p h ι

@[simp]
theorem step1DominanceFamilyTopConstant_ignition {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) (h : Fin k) (s : Fin m) :
    step1DominanceFamilyTopConstant H p h
      (Sum.inl s : Step1DominanceFamilyIndex H p h) =
        step1IgnitionTopConstant H p h s :=
  rfl

@[simp]
theorem step1DominanceFamilyTopConstant_residue {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) (h : Fin k) (ι : Step1ResidueCoordinateIndex H p h) :
    step1DominanceFamilyTopConstant H p h
      (Sum.inr ι : Step1DominanceFamilyIndex H p h) =
        step1ResidueTopConstant H p h ι :=
  rfl

theorem step1DominanceFamilyTopConstant_residue_eq_selectedValueProduct {m k d : Nat}
    {r : Nat} {θ θ' : Params (m + 1) k d}
    (H : Step1StandingHypotheses r θ θ') (p : ProbePoint d) (h : Fin k)
    (ι : Step1ResidueCoordinateIndex H p h) :
    step1DominanceFamilyTopConstant H p h
        (Sum.inr ι : Step1DominanceFamilyIndex H p h) =
      (-1 : ℝ) ^ m *
        (HeadChain.selectedValueProduct θ'
            (step1HeadChain H.chains h (m + 1) le_rfl) (m + 1) le_rfl *ᵥ p.1) ι.1 := by
  simpa [step1DominanceFamilyTopConstant] using
    step1ResidueTopConstant_eq_selectedValueProduct H p h ι

theorem step1DominanceFamilyTopConstant_ignition_eq_selectedValueProduct {m k d : Nat}
    {r : Nat} {θ θ' : Params (m + 1) k d}
    (H : Step1StandingHypotheses r θ θ') (p : ProbePoint d) (h : Fin k)
    (s : Fin m) :
    step1DominanceFamilyTopConstant H p h
        (Sum.inl s : Step1DominanceFamilyIndex H p h) =
      -matrixBilin (attentionMatrix θ' ⟨s.1 + 1, Nat.succ_lt_succ s.2⟩
          (step1SelectedHead H.chains h (s.1 + 1)))
        (HeadChain.selectedValueProduct θ'
          (step1HeadChain H.chains h (s.1 + 1)
            (Nat.succ_le_succ (Nat.le_of_lt s.2)))
          (s.1 + 1) le_rfl *ᵥ p.1)
        (HeadChain.selectedValueProduct θ'
          (step1HeadChain H.chains h (s.1 + 1)
            (Nat.succ_le_succ (Nat.le_of_lt s.2)))
          (s.1 + 1) le_rfl *ᵥ p.1) := by
  simpa [step1DominanceFamilyTopConstant] using
    step1IgnitionTopConstant_eq_selectedValueProduct H p h s

theorem step1DominanceFamilyTopConstant_ne_zero {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    {p : ProbePoint d} (hp : p ∈ H.separatedSet) (h : Fin k)
    (idx : Step1DominanceFamilyIndex H p h) :
    step1DominanceFamilyTopConstant H p h idx ≠ 0 := by
  cases idx with
  | inl s =>
      simpa [step1DominanceFamilyTopConstant] using
        step1IgnitionTopConstant_ne_zero H hp h s
  | inr ι =>
      simpa [step1DominanceFamilyTopConstant] using
        step1ResidueTopConstant_ne_zero H p h ι

/-! ## C3 dominance-family member data wrapper -/

/-- One proved member of the selected Step 1 dominance family.

This is a data wrapper, not the final canonical family map: each value carries a
specific index together with the tower datum and the facts needed to feed
`lem_tower_dominance`. -/
structure Step1DominanceFamilyMember {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) (h : Fin k) : Type where
  idx : Step1DominanceFamilyIndex H p h
  poly : FormalPoly (m + 1) k
  tower : DominanceTowerData (step1DominanceFamilyHeadChain H p h idx) poly
  degree_pos : ∀ i : Fin (step1DominanceFamilyChainLength H p h idx),
    1 ≤ tower.degree i
  topConstant_ne_zero : tower.topConstant ≠ 0
  topConstant : DominanceTowerTopConstant tower
  finalCoeff : DominanceTowerFinalCoeff tower
  evalRecurrence : DominanceTowerEvalRecurrence tower
  leadingCoeff_support :
    ∀ (i : Nat) (hi : i ≤ step1DominanceFamilyChainLength H p h idx),
      PolynomialInLayersLE i (tower.leadingCoeff i hi)
  lowerCoeff_support :
    ∀ (i : Fin (step1DominanceFamilyChainLength H p h idx)) (s : Fin (tower.degree i)),
      PolynomialInLayersLE i.1 (tower.lowerCoeff i s)
  lowerCoeff_selectedVar_notMem :
    ∀ (i : Fin (step1DominanceFamilyChainLength H p h idx)) (s : Fin (tower.degree i)),
      (step1DominanceFamilyHeadChain H p h idx).selectedVar i ∉
        (tower.lowerCoeff i s).vars

namespace Step1DominanceFamilyMember

/-- The ignition/residue tag carried by a proved selected-family member. -/
def kind {m k d : Nat} {r : Nat} {θ θ' : Params (m + 1) k d}
    {H : Step1StandingHypotheses r θ θ'} {p : ProbePoint d} {h : Fin k}
    (M : Step1DominanceFamilyMember H p h) : Step1DominanceFamilyMemberKind :=
  step1DominanceFamilyMemberKind H p h M.idx

/-- A packaged member immediately gives the K04E tower-dominance result. -/
theorem towerDominanceResult {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} {H : Step1StandingHypotheses r θ θ'}
    {p : ProbePoint d} {h : Fin k} (M : Step1DominanceFamilyMember H p h) :
    TowerDominanceResult (step1DominanceFamilyHeadChain H p h M.idx) M.poly :=
  lem_tower_dominance M.tower M.degree_pos M.topConstant_ne_zero
    M.topConstant M.finalCoeff M.evalRecurrence M.leadingCoeff_support

end Step1DominanceFamilyMember

/-! ## Reusable selected-variable coefficient facts -/

/-- Constant formal polynomials are supported in every layer prefix. -/
theorem polynomialInLayersLE_const {L k : Nat} (n : Nat) (a : ℝ) :
    PolynomialInLayersLE (L := L) (k := k) n
      (MvPolynomial.C (σ := FormalVar L k) a) := by
  classical
  intro m hm x _hx
  have hsub :
      (MvPolynomial.C (σ := FormalVar L k) a).support ⊆
        ({0} : Finset (FormalVar L k →₀ Nat)) :=
    support_C_subset_zero a
  have hm0 : m = 0 := by
    simpa using hsub hm
  subst m
  simp

/-- Every support monomial of a selected-tail coefficient comes from a support
monomial of the original polynomial that matches the requested selected-tail
pattern. -/
theorem selectedTailCoeff_support_exists {L k p : Nat} {c : HeadChain L k p}
    {i n deg : Nat} {f : FormalPoly L k} {m : FormalVar L k →₀ Nat}
    (hm : m ∈ (selectedTailCoeff c i n deg f).support) :
    ∃ u ∈ f.support, SelectedTailMatches c i n deg u ∧
      m = truncateExponentLayersLE i u := by
  classical
  have hmem :
      m ∈ f.support.biUnion
        (fun u =>
          ((if SelectedTailMatches c i n deg u then
              MvPolynomial.monomial (truncateExponentLayersLE i u) (f.coeff u)
            else 0 : FormalPoly L k).support)) := by
    exact MvPolynomial.support_sum (s := f.support)
      (f := fun u =>
        (if SelectedTailMatches c i n deg u then
          MvPolynomial.monomial (truncateExponentLayersLE i u) (f.coeff u)
        else 0 : FormalPoly L k))
      (by simpa [selectedTailCoeff] using hm)
  rcases Finset.mem_biUnion.mp hmem with ⟨u, hu, hmterm⟩
  by_cases hmatch : SelectedTailMatches c i n deg u
  · have hmterm' :
        m ∈ (MvPolynomial.monomial (truncateExponentLayersLE i u) (f.coeff u) :
          FormalPoly L k).support := by
      simpa [hmatch] using hmterm
    have hsub :
        (MvPolynomial.monomial (truncateExponentLayersLE i u) (f.coeff u) :
          FormalPoly L k).support ⊆
          ({truncateExponentLayersLE i u} : Finset (FormalVar L k →₀ Nat)) :=
      MvPolynomial.support_monomial_subset
    have hm_eq : m = truncateExponentLayersLE i u := by
      simpa using hsub hmterm'
    exact ⟨u, hu, hmatch, hm_eq⟩
  · simp [hmatch] at hmterm

/-- On the retained current layer of a selected-tail coefficient, support
monomials have exactly the selected-tail target exponent pattern. -/
theorem selectedTailCoeff_support_currentLayer_eq_target {L k p : Nat}
    (c : HeadChain L k p) {i n deg : Nat} {f : FormalPoly L k}
    {m : FormalVar L k →₀ Nat}
    (hm : m ∈ (selectedTailCoeff c i n deg f).support)
    {x : FormalVar L k} (hx : x.1.1 = i) (hin : i < n) :
    m x = selectedTailTarget c deg x := by
  rcases selectedTailCoeff_support_exists (c := c) hm with
    ⟨u, _hu, hmatch, hm_eq⟩
  calc
    m x = truncateExponentLayersLE i u x := by rw [hm_eq]
    _ = u x := by simp [truncateExponentLayersLE_apply, hx]
    _ = selectedTailTarget c deg x :=
        hmatch x (Nat.le_of_eq hx.symm) (by simpa [hx] using hin)

/-- In a positive selected tail, every retained support monomial has exponent
`deg` at the selected variable for the tail's first layer. -/
theorem selectedTailCoeff_support_selectedVar_eq {L k p : Nat}
    (c : HeadChain L k p) {i n deg : Nat} (hi : i < n) (hn : n ≤ p)
    {f : FormalPoly L k} {m : FormalVar L k →₀ Nat}
    (hm : m ∈ (selectedTailCoeff c i n deg f).support) :
    m (c.selectedVar ⟨i, Nat.lt_of_lt_of_le hi hn⟩) = deg := by
  let x : FormalVar L k := c.selectedVar ⟨i, Nat.lt_of_lt_of_le hi hn⟩
  have hx : x.1.1 = i := by
    simp [x, HeadChain.selectedVar, HeadChain.layer]
  calc
    m x = selectedTailTarget c deg x :=
      selectedTailCoeff_support_currentLayer_eq_target c hm hx hi
    _ = deg := by
      simp [x, selectedTailTarget, HeadChain.selectedVar_isSelected]

/-- The selected-tail coefficient has ordinary degree at most `deg` in its
first retained selected variable. -/
theorem selectedTailCoeff_degreeOf_selectedVar_le {L k p : Nat}
    (c : HeadChain L k p) {i n deg : Nat} (hi : i < n) (hn : n ≤ p)
    (f : FormalPoly L k) :
    MvPolynomial.degreeOf (c.selectedVar ⟨i, Nat.lt_of_lt_of_le hi hn⟩)
      (selectedTailCoeff c i n deg f) ≤ deg := by
  rw [MvPolynomial.degreeOf_le_iff]
  intro m hm
  exact le_of_eq (selectedTailCoeff_support_selectedVar_eq c hi hn hm)

/-- Selected-tail extraction does not increase the total degree in any layer
block. -/
theorem selectedTailCoeff_blockDegreeLE {L k p D : Nat}
    (c : HeadChain L k p) (i n deg : Nat) {f : FormalPoly L k}
    (hf : BlockDegreeLE D f) :
    BlockDegreeLE D (selectedTailCoeff c i n deg f) := by
  classical
  intro m hm l
  rcases selectedTailCoeff_support_exists (c := c) hm with
    ⟨u, hu, _hmatch, hm_eq⟩
  rw [hm_eq]
  calc
    (∑ a : Fin k, truncateExponentLayersLE i u (l, a))
        ≤ ∑ a : Fin k, u (l, a) := by
          refine Finset.sum_le_sum ?_
          intro a _ha
          by_cases hle : (l, a).1.1 ≤ i
          · simp [truncateExponentLayersLE_apply, hle]
          · simp [truncateExponentLayersLE_apply, hle]
    _ ≤ D := hf u hu l

/-- A block-degree bound on the source polynomial gives a finite ordinary
degree bound for every variable after selected-tail extraction. -/
theorem selectedTailCoeff_degreeOf_le_of_blockDegreeLE {L k p D : Nat}
    (c : HeadChain L k p) (i n deg : Nat) {x : FormalVar L k}
    {f : FormalPoly L k} (hf : BlockDegreeLE D f) :
    MvPolynomial.degreeOf x (selectedTailCoeff c i n deg f) ≤ D :=
  blockDegreeLE_degreeOf_le (selectedTailCoeff_blockDegreeLE c i n deg hf)

/-- Support monomials of a selected-variable split of a selected-tail
coefficient come from the same selected-tail source monomials, with that
variable erased after truncation. -/
theorem coeffOfVar_selectedTailCoeff_support_exists {L k p : Nat}
    {c : HeadChain L k p} {i n deg s : Nat} {x : FormalVar L k}
    {f : FormalPoly L k} {m : FormalVar L k →₀ Nat}
    (hm : m ∈ (coeffOfVar x s (selectedTailCoeff c i n deg f)).support) :
    ∃ u ∈ f.support, SelectedTailMatches c i n deg u ∧
      (truncateExponentLayersLE i u) x = s ∧
      m = Finsupp.erase x (truncateExponentLayersLE i u) := by
  rcases coeffOfVar_support_exists hm with ⟨v, hv, hvx, hm_eq⟩
  rcases selectedTailCoeff_support_exists (c := c) hv with
    ⟨u, hu, hmatch, hv_eq⟩
  subst v
  exact ⟨u, hu, hmatch, hvx, hm_eq⟩

/-- Source-monomial characterization for the preferred successor-tail
one-variable split at the previous selected variable. -/
theorem coeffOfVar_selectedTailCoeff_succ_prevSelectedVar_support_exists
    {L k p : Nat} (c : HeadChain L k p) {i n deg : Nat}
    (hi : i < n) (hn : n ≤ p) {f : FormalPoly L k}
    {m : FormalVar L k →₀ Nat}
    (hm : m ∈
      (coeffOfVar (c.selectedVar ⟨i, Nat.lt_of_lt_of_le hi hn⟩) deg
        (selectedTailCoeff c (i + 1) n deg f)).support) :
    ∃ u ∈ f.support, SelectedTailMatches c (i + 1) n deg u ∧
      (truncateExponentLayersLE (i + 1) u)
          (c.selectedVar ⟨i, Nat.lt_of_lt_of_le hi hn⟩) = deg ∧
      m =
        Finsupp.erase (c.selectedVar ⟨i, Nat.lt_of_lt_of_le hi hn⟩)
          (truncateExponentLayersLE (i + 1) u) :=
  coeffOfVar_selectedTailCoeff_support_exists (c := c) hm

/-- Non-top one-variable coefficients vanish for a selected-tail coefficient at
the first selected variable in a positive tail. -/
theorem coeffOfVar_selectedTailCoeff_selectedVar_eq_zero_of_ne {L k p : Nat}
    (c : HeadChain L k p) {i n deg s : Nat} (hi : i < n) (hn : n ≤ p)
    (hs : s ≠ deg) (f : FormalPoly L k) :
    coeffOfVar (c.selectedVar ⟨i, Nat.lt_of_lt_of_le hi hn⟩) s
      (selectedTailCoeff c i n deg f) = 0 := by
  classical
  apply MvPolynomial.ext
  intro m
  rw [MvPolynomial.coeff_zero]
  by_contra hcoeff
  have hm :
      m ∈ (coeffOfVar (c.selectedVar ⟨i, Nat.lt_of_lt_of_le hi hn⟩) s
        (selectedTailCoeff c i n deg f)).support :=
    MvPolynomial.mem_support_iff.mpr hcoeff
  rcases coeffOfVar_support_exists hm with ⟨u, hu, hux, _hm_eq⟩
  have hdeg := selectedTailCoeff_support_selectedVar_eq c hi hn hu
  exact hs (by rw [← hux, hdeg])

/-- Evaluation form of the selected-tail leading split at the first selected
variable in a positive tail.  All lower coefficients in this one-variable split
are zero by the selected-tail support characterization. -/
theorem selectedTailCoeff_eval_eq_coeffOfVar_selected_mul {L k p : Nat}
    (c : HeadChain L k p) {i n deg : Nat} (hi : i < n) (hn : n ≤ p)
    (f : FormalPoly L k) (z : FormalVar L k -> ℂ) :
    evalFormalPolyComplex z (selectedTailCoeff c i n deg f) =
      evalFormalPolyComplex z
        (coeffOfVar (c.selectedVar ⟨i, Nat.lt_of_lt_of_le hi hn⟩) deg
          (selectedTailCoeff c i n deg f)) *
        (z (c.selectedVar ⟨i, Nat.lt_of_lt_of_le hi hn⟩)) ^ deg := by
  let x : FormalVar L k := c.selectedVar ⟨i, Nat.lt_of_lt_of_le hi hn⟩
  change evalFormalPolyComplex z (selectedTailCoeff c i n deg f) =
      evalFormalPolyComplex z (coeffOfVar x deg (selectedTailCoeff c i n deg f)) *
        (z x) ^ deg
  have hD :
      MvPolynomial.degreeOf x (selectedTailCoeff c i n deg f) ≤ deg := by
    simpa [x] using selectedTailCoeff_degreeOf_selectedVar_le c hi hn f
  rw [evalFormalPolyComplex_eq_sum_coeffOfVar (x := x)
    (D := deg) (f := selectedTailCoeff c i n deg f) hD z]
  refine Finset.sum_eq_single_of_mem deg (by simp) ?_
  intro s hs hsne
  have hzero :
      coeffOfVar x s (selectedTailCoeff c i n deg f) = 0 := by
    simpa [x] using
      coeffOfVar_selectedTailCoeff_selectedVar_eq_zero_of_ne c hi hn hsne f
  rw [hzero]
  simp [evalFormalPolyComplex]

/-- A support monomial of the successor selected-tail coefficient retains the
previous selected variable with exactly its source exponent.  This is the
generic predecessor-variable characterization available without additional
slot hypotheses on the source polynomial. -/
theorem selectedTailCoeff_succ_support_prevSelectedVar_eq_source {L k p : Nat}
    (c : HeadChain L k p) {i n deg : Nat} (hi : i < n) (hn : n ≤ p)
    {f : FormalPoly L k} {m : FormalVar L k →₀ Nat}
    (hm : m ∈ (selectedTailCoeff c (i + 1) n deg f).support) :
    ∃ u ∈ f.support, SelectedTailMatches c (i + 1) n deg u ∧
      m (c.selectedVar ⟨i, Nat.lt_of_lt_of_le hi hn⟩) =
        u (c.selectedVar ⟨i, Nat.lt_of_lt_of_le hi hn⟩) := by
  rcases selectedTailCoeff_support_exists (c := c) hm with
    ⟨u, hu, hmatch, hm_eq⟩
  refine ⟨u, hu, hmatch, ?_⟩
  let x : FormalVar L k := c.selectedVar ⟨i, Nat.lt_of_lt_of_le hi hn⟩
  calc
    m x = truncateExponentLayersLE (i + 1) u x := by rw [hm_eq]
    _ = u x := by
      have hx : x.1.1 ≤ i + 1 := by
        simp [x, HeadChain.selectedVar, HeadChain.layer]
      simp [truncateExponentLayersLE_apply, hx]

/-- A one-variable coefficient at a selected Step 1 family variable preserves
the supplied layer-prefix support bound. -/
theorem step1DominanceFamily_coeffOfVar_support {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) (h : Fin k) (idx : Step1DominanceFamilyIndex H p h)
    (i : Fin (step1DominanceFamilyChainLength H p h idx)) (s : Nat)
    {f : FormalPoly (m + 1) k}
    (hf : PolynomialInLayersLE i.1 f) :
    PolynomialInLayersLE i.1
      (coeffOfVar ((step1DominanceFamilyHeadChain H p h idx).selectedVar i) s f) :=
  coeffOfVar_support_subset hf

/-- The selected variable removed by `coeffOfVar` is absent from the resulting
coefficient polynomial. -/
theorem step1DominanceFamily_coeffOfVar_selectedVar_notMem {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) (h : Fin k) (idx : Step1DominanceFamilyIndex H p h)
    (i : Fin (step1DominanceFamilyChainLength H p h idx)) (s : Nat)
    (f : FormalPoly (m + 1) k) :
    (step1DominanceFamilyHeadChain H p h idx).selectedVar i ∉
      (coeffOfVar ((step1DominanceFamilyHeadChain H p h idx).selectedVar i) s f).vars :=
  coeffOfVar_notMem_vars

/-- The selected terminal coefficient along a selected-family chain has the
expected layer-prefix support. -/
theorem step1DominanceFamily_selectedTopTerminalCoeff_support {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) (h : Fin k) (idx : Step1DominanceFamilyIndex H p h)
    (ι : Fin d) :
    PolynomialInLayersLE (step1DominanceFamilyChainLength H p h idx)
      (selectedTopTerminalCoeff θ' p.1 p.2
        (step1DominanceFamilyHeadChain H p h idx) ι) :=
  PolynomialInLayersLE.mono (Nat.zero_le (step1DominanceFamilyChainLength H p h idx))
    (by
      simpa [selectedTopTerminalCoeff] using
        selectedTailCoeff_polynomialInLayersLE
          (step1DominanceFamilyHeadChain H p h idx) 0
          (step1DominanceFamilyChainLength H p h idx) 1
          (formalW θ' p.1 p.2 (step1DominanceFamilyChainLength H p h idx)
            (step1DominanceFamilyHeadChain H p h idx).length_le ι))

/-! ## Proved zero-stage tower members -/

/-- The constant tower datum for a zero-length head chain. -/
noncomputable def step1ConstantTowerData {L k : Nat} (c : HeadChain L k 0) (a : ℝ) :
    DominanceTowerData c (MvPolynomial.C (σ := FormalVar L k) a) where
  degree := fun i => Fin.elim0 i
  leadingCoeff := fun _ _ => MvPolynomial.C a
  lowerCoeff := fun i => Fin.elim0 i
  topConstant := a

theorem step1ConstantTower_degree_pos {L k : Nat} {c : HeadChain L k 0} (a : ℝ) :
    ∀ i : Fin 0, 1 ≤ (step1ConstantTowerData c a).degree i := by
  intro i
  exact Fin.elim0 i

theorem step1ConstantTower_topConstant {L k : Nat} {c : HeadChain L k 0} (a : ℝ) :
    DominanceTowerTopConstant (step1ConstantTowerData c a) := by
  intro z
  simp [step1ConstantTowerData, evalFormalPolyComplex]

theorem step1ConstantTower_finalCoeff {L k : Nat} {c : HeadChain L k 0} (a : ℝ) :
    DominanceTowerFinalCoeff (step1ConstantTowerData c a) :=
  rfl

theorem step1ConstantTower_evalRecurrence {L k : Nat} {c : HeadChain L k 0} (a : ℝ) :
    DominanceTowerEvalRecurrence (step1ConstantTowerData c a) := by
  intro i
  exact Fin.elim0 i

theorem step1ConstantTower_leadingCoeff_support {L k : Nat} {c : HeadChain L k 0}
    (a : ℝ) :
    ∀ (i : Nat) (hi : i ≤ 0),
      PolynomialInLayersLE i ((step1ConstantTowerData c a).leadingCoeff i hi) := by
  intro i _hi
  exact polynomialInLayersLE_const i a

theorem step1ConstantTower_lowerCoeff_support {L k : Nat} {c : HeadChain L k 0}
    (a : ℝ) :
    ∀ (i : Fin 0) (s : Fin ((step1ConstantTowerData c a).degree i)),
      PolynomialInLayersLE i.1 ((step1ConstantTowerData c a).lowerCoeff i s) := by
  intro i
  exact Fin.elim0 i

theorem step1ConstantTower_lowerCoeff_selectedVar_notMem {L k : Nat}
    {c : HeadChain L k 0} (a : ℝ) :
    ∀ (i : Fin 0) (s : Fin ((step1ConstantTowerData c a).degree i)),
      c.selectedVar i ∉ ((step1ConstantTowerData c a).lowerCoeff i s).vars := by
  intro i
  exact Fin.elim0 i

/-- A proved zero-stage ignition member.  This covers the first ignition index
when the depth has at least one later layer; the full nonconstant ignition
towers remain the open C3 algebraic task. -/
noncomputable def step1ZeroIgnitionDominanceFamilyMember {m k d : Nat} {r : Nat}
    {θ θ' : Params (m + 1) k d} (H : Step1StandingHypotheses r θ θ')
    {p : ProbePoint d} (hp : p ∈ H.separatedSet) (h : Fin k) (hm : 0 < m) :
    Step1DominanceFamilyMember H p h where
  idx := Sum.inl ⟨0, hm⟩
  poly :=
    MvPolynomial.C (σ := FormalVar (m + 1) k)
      (step1DominanceFamilyTopConstant H p h
        (Sum.inl ⟨0, hm⟩ : Step1DominanceFamilyIndex H p h))
  tower :=
    step1ConstantTowerData
      (step1DominanceFamilyHeadChain H p h
        (Sum.inl ⟨0, hm⟩ : Step1DominanceFamilyIndex H p h))
      (step1DominanceFamilyTopConstant H p h
        (Sum.inl ⟨0, hm⟩ : Step1DominanceFamilyIndex H p h))
  degree_pos := by
    exact step1ConstantTower_degree_pos
      (c := step1DominanceFamilyHeadChain H p h
        (Sum.inl ⟨0, hm⟩ : Step1DominanceFamilyIndex H p h))
      (step1DominanceFamilyTopConstant H p h
        (Sum.inl ⟨0, hm⟩ : Step1DominanceFamilyIndex H p h))
  topConstant_ne_zero := by
    simpa [step1ConstantTowerData] using
      step1DominanceFamilyTopConstant_ne_zero H hp h
        (Sum.inl ⟨0, hm⟩ : Step1DominanceFamilyIndex H p h)
  topConstant := by
    exact step1ConstantTower_topConstant
      (c := step1DominanceFamilyHeadChain H p h
        (Sum.inl ⟨0, hm⟩ : Step1DominanceFamilyIndex H p h))
      (step1DominanceFamilyTopConstant H p h
        (Sum.inl ⟨0, hm⟩ : Step1DominanceFamilyIndex H p h))
  finalCoeff := by
    exact step1ConstantTower_finalCoeff
      (c := step1DominanceFamilyHeadChain H p h
        (Sum.inl ⟨0, hm⟩ : Step1DominanceFamilyIndex H p h))
      (step1DominanceFamilyTopConstant H p h
        (Sum.inl ⟨0, hm⟩ : Step1DominanceFamilyIndex H p h))
  evalRecurrence := by
    exact step1ConstantTower_evalRecurrence
      (c := step1DominanceFamilyHeadChain H p h
        (Sum.inl ⟨0, hm⟩ : Step1DominanceFamilyIndex H p h))
      (step1DominanceFamilyTopConstant H p h
        (Sum.inl ⟨0, hm⟩ : Step1DominanceFamilyIndex H p h))
  leadingCoeff_support := by
    exact step1ConstantTower_leadingCoeff_support
      (c := step1DominanceFamilyHeadChain H p h
        (Sum.inl ⟨0, hm⟩ : Step1DominanceFamilyIndex H p h))
      (step1DominanceFamilyTopConstant H p h
        (Sum.inl ⟨0, hm⟩ : Step1DominanceFamilyIndex H p h))
  lowerCoeff_support := by
    exact step1ConstantTower_lowerCoeff_support
      (c := step1DominanceFamilyHeadChain H p h
        (Sum.inl ⟨0, hm⟩ : Step1DominanceFamilyIndex H p h))
      (step1DominanceFamilyTopConstant H p h
        (Sum.inl ⟨0, hm⟩ : Step1DominanceFamilyIndex H p h))
  lowerCoeff_selectedVar_notMem := by
    exact step1ConstantTower_lowerCoeff_selectedVar_notMem
      (c := step1DominanceFamilyHeadChain H p h
        (Sum.inl ⟨0, hm⟩ : Step1DominanceFamilyIndex H p h))
      (step1DominanceFamilyTopConstant H p h
        (Sum.inl ⟨0, hm⟩ : Step1DominanceFamilyIndex H p h))

/-- A proved zero-depth residue member.  In depth one the residue family has no
selected variables, so the carried tower is the constant zero-stage tower. -/
noncomputable def step1ZeroResidueDominanceFamilyMember {k d : Nat} {r : Nat}
    {θ θ' : Params (0 + 1) k d} (H : Step1StandingHypotheses r θ θ')
    (p : ProbePoint d) (h : Fin k) (ι : Step1ResidueCoordinateIndex H p h) :
    Step1DominanceFamilyMember H p h where
  idx := Sum.inr ι
  poly :=
    MvPolynomial.C (σ := FormalVar (0 + 1) k)
      (step1DominanceFamilyTopConstant H p h
        (Sum.inr ι : Step1DominanceFamilyIndex H p h))
  tower :=
    step1ConstantTowerData
      (step1DominanceFamilyHeadChain H p h
        (Sum.inr ι : Step1DominanceFamilyIndex H p h))
      (step1DominanceFamilyTopConstant H p h
        (Sum.inr ι : Step1DominanceFamilyIndex H p h))
  degree_pos := by
    exact step1ConstantTower_degree_pos
      (c := step1DominanceFamilyHeadChain H p h
        (Sum.inr ι : Step1DominanceFamilyIndex H p h))
      (step1DominanceFamilyTopConstant H p h
        (Sum.inr ι : Step1DominanceFamilyIndex H p h))
  topConstant_ne_zero := by
    simpa [step1ConstantTowerData] using
      step1ResidueTopConstant_ne_zero H p h ι
  topConstant := by
    exact step1ConstantTower_topConstant
      (c := step1DominanceFamilyHeadChain H p h
        (Sum.inr ι : Step1DominanceFamilyIndex H p h))
      (step1DominanceFamilyTopConstant H p h
        (Sum.inr ι : Step1DominanceFamilyIndex H p h))
  finalCoeff := by
    exact step1ConstantTower_finalCoeff
      (c := step1DominanceFamilyHeadChain H p h
        (Sum.inr ι : Step1DominanceFamilyIndex H p h))
      (step1DominanceFamilyTopConstant H p h
        (Sum.inr ι : Step1DominanceFamilyIndex H p h))
  evalRecurrence := by
    exact step1ConstantTower_evalRecurrence
      (c := step1DominanceFamilyHeadChain H p h
        (Sum.inr ι : Step1DominanceFamilyIndex H p h))
      (step1DominanceFamilyTopConstant H p h
        (Sum.inr ι : Step1DominanceFamilyIndex H p h))
  leadingCoeff_support := by
    exact step1ConstantTower_leadingCoeff_support
      (c := step1DominanceFamilyHeadChain H p h
        (Sum.inr ι : Step1DominanceFamilyIndex H p h))
      (step1DominanceFamilyTopConstant H p h
        (Sum.inr ι : Step1DominanceFamilyIndex H p h))
  lowerCoeff_support := by
    exact step1ConstantTower_lowerCoeff_support
      (c := step1DominanceFamilyHeadChain H p h
        (Sum.inr ι : Step1DominanceFamilyIndex H p h))
      (step1DominanceFamilyTopConstant H p h
        (Sum.inr ι : Step1DominanceFamilyIndex H p h))
  lowerCoeff_selectedVar_notMem := by
    exact step1ConstantTower_lowerCoeff_selectedVar_notMem
      (c := step1DominanceFamilyHeadChain H p h
        (Sum.inr ι : Step1DominanceFamilyIndex H p h))
      (step1DominanceFamilyTopConstant H p h
        (Sum.inr ι : Step1DominanceFamilyIndex H p h))


/-! ### Block-saturation support drop -/

/-- Erasing one variable preserves a per-layer block-degree bound. -/
theorem coeffOfVar_blockDegreeLE {L k D : Nat} (x : FormalVar L k) (s : Nat)
    {f : FormalPoly L k} (hf : BlockDegreeLE D f) :
    BlockDegreeLE D (coeffOfVar x s f) := by
  classical
  intro m hm l
  rcases coeffOfVar_support_exists hm with ⟨u, hu, _hux, rfl⟩
  calc
    (∑ a : Fin k, (Finsupp.erase x u) (l, a))
        ≤ ∑ a : Fin k, u (l, a) := by
          refine Finset.sum_le_sum ?_
          intro a _ha
          by_cases hax : (l, a) = x
          · subst hax; simp
          · simp [Finsupp.erase_ne hax]
    _ ≤ D := hf u hu l

/-- The `x^D` coefficient of a block-degree-`D` polynomial contains no variable
from `x`'s layer: extracting `x` to the maximal block degree saturates that
layer's budget, forcing all other layer variables to exponent zero. -/
theorem coeffOfVar_top_no_currentLayer {L k D : Nat} (x : FormalVar L k)
    {f : FormalPoly L k} (hf : BlockDegreeLE D f)
    {m : FormalVar L k →₀ Nat} (hm : m ∈ (coeffOfVar x D f).support)
    (a : Fin k) : m (x.1, a) = 0 := by
  classical
  rcases coeffOfVar_support_exists hm with ⟨u, hu, hux, rfl⟩
  have hsum_le : (∑ b : Fin k, u (x.1, b)) ≤ D := hf u hu x.1
  have hx_le : u x ≤ ∑ b : Fin k, u (x.1, b) := by
    have hxeq : u x = u (x.1, x.2) := by cases x; rfl
    rw [hxeq]
    exact Finset.single_le_sum (f := fun b => u (x.1, b))
      (fun b _ => Nat.zero_le _) (Finset.mem_univ x.2)
  have hsum_eq : (∑ b : Fin k, u (x.1, b)) = D := by
    have := hx_le
    rw [hux] at this
    omega
  -- every term other than x.2 must be zero
  by_cases hax : (x.1, a) = x
  · rw [hax]; simp
  · have hne : a ≠ x.2 := by
      intro h; apply hax; cases x; simp_all
    have hzero : u (x.1, a) = 0 := by
      have hmem : a ∈ Finset.univ.erase x.2 :=
        Finset.mem_erase.mpr ⟨hne, Finset.mem_univ a⟩
      have hle2 : u (x.1, a) ≤ ∑ b ∈ Finset.univ.erase x.2, u (x.1, b) := by
        exact Finset.single_le_sum (f := fun b => u (x.1, b))
          (fun b _hb => Nat.zero_le (u (x.1, b))) hmem
      have hsplit : u (x.1, x.2) + ∑ b ∈ Finset.univ.erase x.2, u (x.1, b)
          = ∑ b : Fin k, u (x.1, b) :=
        Finset.add_sum_erase Finset.univ (fun b => u (x.1, b)) (Finset.mem_univ x.2)
      have hxeqD : u (x.1, x.2) = D := hux
      omega
    simp [Finsupp.erase_ne hax, hzero]

/-- Extracting the top block-degree power of the current-layer selected variable
lowers the layer-support strictly below that layer. -/
theorem coeffOfVar_top_polynomialInLayersLT {L k D n : Nat} (x : FormalVar L k)
    (hx : x.1.1 = n) {f : FormalPoly L k}
    (hf : BlockDegreeLE D f) (hfn : PolynomialInLayersLE n f) :
    PolynomialInLayersLT n (coeffOfVar x D f) := by
  classical
  intro m hm y hy
  rcases Nat.eq_or_lt_of_le hy with heq | hlt
  · -- y is at layer n, same as x's layer, so y.1 = x.1
    have hyx1 : y.1 = x.1 := by
      apply Fin.ext
      rw [hx, ← heq]
    have hform : ((y.1, y.2) : FormalVar L k) = (x.1, y.2) := by rw [hyx1]
    calc m y = m (y.1, y.2) := rfl
      _ = m (x.1, y.2) := by rw [hform]
      _ = 0 := coeffOfVar_top_no_currentLayer x hf hm y.2
  · rcases coeffOfVar_support_exists hm with ⟨u, hu, _hux, rfl⟩
    by_cases hyx : y = x
    · subst y; simp
    · rw [Finsupp.erase_ne hyx]
      exact hfn u hu y hlt

/-! ### Generic clean-tail dominance tower -/

section GenericTower

variable {L k p : Nat} (c : HeadChain L k p) (deg : Nat) (f : FormalPoly L k)

/-- Iterated top-selected-variable extraction: `topLeadingCoeff t` removes the top
`t` selected variables `ζ_{p-1}, …, ζ_{p-t}` at their maximal block degree `deg`. -/
noncomputable def topLeadingCoeff : Nat → FormalPoly L k
  | 0 => f
  | (t + 1) =>
      if h : t < p then
        coeffOfVar (c.selectedVar ⟨p - 1 - t, by omega⟩) deg (topLeadingCoeff t)
      else topLeadingCoeff t

@[simp] theorem topLeadingCoeff_zero : topLeadingCoeff c deg f 0 = f := rfl

theorem topLeadingCoeff_block (hf : BlockDegreeLE deg f) :
    ∀ t, BlockDegreeLE deg (topLeadingCoeff c deg f t)
  | 0 => hf
  | (t + 1) => by
      rw [topLeadingCoeff]
      by_cases h : t < p
      · simp only [h, dif_pos]
        exact coeffOfVar_blockDegreeLE _ deg (topLeadingCoeff_block hf t)
      · simp only [h, dif_neg, not_false_iff]
        exact topLeadingCoeff_block hf t

theorem topLeadingCoeff_supp (hf : PolynomialInLayersLT p f) (hfb : BlockDegreeLE deg f) :
    ∀ t, PolynomialInLayersLT (p - t) (topLeadingCoeff c deg f t)
  | 0 => by simpa using hf
  | (t + 1) => by
      rw [topLeadingCoeff]
      by_cases h : t < p
      · simp only [h, dif_pos]
        have ihsupp := topLeadingCoeff_supp hf hfb t
        have ihblock := topLeadingCoeff_block c deg f hfb t
        -- var is at layer p-1-t, tail ⊆ layers ≤ p-1-t
        have hle : PolynomialInLayersLE (p - 1 - t) (topLeadingCoeff c deg f t) := by
          intro m hm y hy
          exact ihsupp m hm y (by omega)
        have hxlayer : (c.selectedVar ⟨p - 1 - t, by omega⟩).1.1 = p - 1 - t := by
          simp [HeadChain.selectedVar, HeadChain.layer]
        have := coeffOfVar_top_polynomialInLayersLT
          (c.selectedVar ⟨p - 1 - t, by omega⟩) hxlayer ihblock hle
        intro m hm y hy
        exact this m hm y (by omega)
      · simp only [h, dif_neg, not_false_iff]
        have heq : p - (t + 1) = p - t := by omega
        rw [heq]
        exact topLeadingCoeff_supp hf hfb t

/-- The full extraction is a constant polynomial (supported only at the empty
monomial). -/
theorem topLeadingCoeff_full_const (hf : PolynomialInLayersLT p f)
    (hfb : BlockDegreeLE deg f) :
    topLeadingCoeff c deg f p =
      MvPolynomial.C ((topLeadingCoeff c deg f p).coeff 0) := by
  classical
  have hsupp : PolynomialInLayersLT 0 (topLeadingCoeff c deg f p) := by
    simpa using topLeadingCoeff_supp c deg f hf hfb p
  -- a polynomial supported in layers < 0 has only the zero monomial
  have hzero : ∀ m ∈ (topLeadingCoeff c deg f p).support, m = 0 := by
    intro m hm
    ext y
    have := hsupp m hm y (Nat.zero_le _)
    simpa using this
  refine MvPolynomial.ext _ _ ?_
  intro m
  by_cases hm : m = 0
  · subst m; simp
  · rw [MvPolynomial.coeff_C]
    have hmne : (topLeadingCoeff c deg f p).coeff m = 0 := by
      by_contra hc
      exact hm (hzero m (MvPolynomial.mem_support_iff.mpr hc))
    simp [hmne, Ne.symm hm]

/-- One-step unfolding of the top extraction as a `coeffOfVar` at the selected
variable of the corresponding chain position. -/
theorem topLeadingCoeff_succ_extract (i : Nat) (hi : i < p) :
    topLeadingCoeff c deg f (p - i)
      = coeffOfVar (c.selectedVar ⟨i, hi⟩) deg (topLeadingCoeff c deg f (p - i - 1)) := by
  set t := p - i - 1 with ht
  have hpi : p - i = t + 1 := by omega
  have hidx : p - 1 - t = i := by omega
  have htp : t < p := by omega
  rw [hpi,
    show topLeadingCoeff c deg f (t + 1)
        = coeffOfVar (c.selectedVar ⟨p - 1 - t, by omega⟩) deg (topLeadingCoeff c deg f t)
      from by rw [topLeadingCoeff]; simp only [htp, dif_pos]]
  congr 1
  exact congrArg c.selectedVar (Fin.ext hidx)

/-- The canonical clean-tail dominance-tower datum for `f` along `c` at degree
`deg`. -/
noncomputable def genericTowerData : DominanceTowerData c f where
  degree := fun _ => deg
  leadingCoeff := fun i _ => topLeadingCoeff c deg f (p - i)
  lowerCoeff := fun i s => coeffOfVar (c.selectedVar i) s.1 (topLeadingCoeff c deg f (p - i.1 - 1))
  topConstant := (topLeadingCoeff c deg f p).coeff 0

variable (hf : PolynomialInLayersLT p f) (hfb : BlockDegreeLE deg f)

include hf hfb

theorem genericTower_degree_pos (hdeg : 1 ≤ deg) :
    ∀ i : Fin p, 1 ≤ (genericTowerData c deg f).degree i :=
  fun _ => hdeg

theorem genericTower_topConstant :
    DominanceTowerTopConstant (genericTowerData c deg f) := by
  intro z
  show evalFormalPolyComplex z (topLeadingCoeff c deg f (p - 0)) = _
  rw [Nat.sub_zero, topLeadingCoeff_full_const c deg f hf hfb]
  simp [evalFormalPolyComplex, genericTowerData]

theorem genericTower_finalCoeff :
    DominanceTowerFinalCoeff (genericTowerData c deg f) := by
  show topLeadingCoeff c deg f (p - p) = f
  rw [Nat.sub_self]; rfl

theorem genericTower_leadingCoeff_support :
    ∀ (i : Nat) (hi : i ≤ p),
      PolynomialInLayersLE i ((genericTowerData c deg f).leadingCoeff i hi) := by
  intro i hi
  show PolynomialInLayersLE i (topLeadingCoeff c deg f (p - i))
  have hsupp := topLeadingCoeff_supp c deg f hf hfb (p - i)
  have heq : p - (p - i) = i := by omega
  rw [heq] at hsupp
  exact hsupp.to_LE

theorem genericTower_lowerCoeff_support :
    ∀ (i : Fin p) (s : Fin ((genericTowerData c deg f).degree i)),
      PolynomialInLayersLE i.1 ((genericTowerData c deg f).lowerCoeff i s) := by
  intro i s
  show PolynomialInLayersLE i.1
    (coeffOfVar (c.selectedVar i) s.1 (topLeadingCoeff c deg f (p - i.1 - 1)))
  have hsupp := topLeadingCoeff_supp c deg f hf hfb (p - i.1 - 1)
  have heq : p - (p - i.1 - 1) = i.1 + 1 := by omega
  rw [heq] at hsupp
  refine coeffOfVar_support_subset ?_
  intro m hm y hy
  exact hsupp m hm y (by omega)

theorem genericTower_lowerCoeff_notMem :
    ∀ (i : Fin p) (s : Fin ((genericTowerData c deg f).degree i)),
      c.selectedVar i ∉ ((genericTowerData c deg f).lowerCoeff i s).vars := by
  intro i s
  exact coeffOfVar_notMem_vars

theorem genericTower_evalRecurrence :
    DominanceTowerEvalRecurrence (genericTowerData c deg f) := by
  classical
  intro i z
  set g := topLeadingCoeff c deg f (p - i.1 - 1) with hg
  have hgblock : BlockDegreeLE deg g := topLeadingCoeff_block c deg f hfb _
  have hD : MvPolynomial.degreeOf (c.selectedVar i) g ≤ deg :=
    blockDegreeLE_degreeOf_le hgblock
  have hlead_i :
      topLeadingCoeff c deg f (p - i.1) = coeffOfVar (c.selectedVar i) deg g := by
    rw [hg]
    exact topLeadingCoeff_succ_extract c deg f i.1 i.2
  -- unfold the tower fields
  change evalFormalPolyComplex z
      ((genericTowerData c deg f).leadingCoeff (i.1 + 1) (Nat.succ_le_of_lt i.2)) =
    evalFormalPolyComplex z
        ((genericTowerData c deg f).leadingCoeff i.1 (Nat.le_of_lt i.2)) *
        z (c.selectedVar i) ^ (genericTowerData c deg f).degree i +
      ∑ s : Fin ((genericTowerData c deg f).degree i),
        evalFormalPolyComplex z ((genericTowerData c deg f).lowerCoeff i s) *
          z (c.selectedVar i) ^ (s : Nat)
  simp only [genericTowerData]
  have hlhs : p - (i.1 + 1) = p - i.1 - 1 := by omega
  rw [hlhs, ← hg, hlead_i]
  -- now use the coeffOfVar decomposition of eval z g
  have hsplit := evalFormalPolyComplex_eq_sum_coeffOfVar (x := c.selectedVar i)
    (D := deg) (f := g) hD z
  rw [hsplit, Finset.sum_range_succ]
  rw [← Fin.sum_univ_eq_sum_range
    (fun s => evalFormalPolyComplex z (coeffOfVar (c.selectedVar i) s g) *
      z (c.selectedVar i) ^ s) deg]
  exact add_comm _ _

end GenericTower

/-! ### Canonical ignition tower -/

/-- The stage-`s` ignition polynomial `ψ_{s+1}`: the quadratic (`ζ_s^2`)
coefficient of the selected slope at layer `s+1`. -/
noncomputable def step1IgnitionPoly {m k d : Nat} {θ' : Params (m + 1) k d}
    (chains : Step1ChainChoices θ') (h : Fin k) (p : ProbePoint d)
    (s : Nat) (hs : s < m) : FormalPoly (m + 1) k :=
  coeffOfVar (((⟨s, by omega⟩ : Fin (m + 1)), step1SelectedHead chains h s)) 2
    (formalSlope θ' p.1 p.2 ⟨s + 1, by omega⟩ (step1SelectedHead chains h (s + 1)))

theorem step1IgnitionPoly_blockDegree {m k d : Nat} {θ' : Params (m + 1) k d}
    (chains : Step1ChainChoices θ') (h : Fin k) (p : ProbePoint d)
    (s : Nat) (hs : s < m) :
    BlockDegreeLE 2 (step1IgnitionPoly chains h p s hs) :=
  coeffOfVar_blockDegreeLE _ 2
    (formalSlope_blockDegree_two θ' p.1 p.2 ⟨s + 1, by omega⟩
      (step1SelectedHead chains h (s + 1)))

theorem step1IgnitionPoly_support {m k d : Nat} {θ' : Params (m + 1) k d}
    (chains : Step1ChainChoices θ') (h : Fin k) (p : ProbePoint d)
    (s : Nat) (hs : s < m) :
    PolynomialInLayersLT s (step1IgnitionPoly chains h p s hs) := by
  have hslopeblock : BlockDegreeLE 2
      (formalSlope θ' p.1 p.2 ⟨s + 1, by omega⟩ (step1SelectedHead chains h (s + 1))) :=
    formalSlope_blockDegree_two θ' p.1 p.2 ⟨s + 1, by omega⟩ (step1SelectedHead chains h (s + 1))
  have hslopeLE : PolynomialInLayersLE s
      (formalSlope θ' p.1 p.2 ⟨s + 1, by omega⟩ (step1SelectedHead chains h (s + 1))) := by
    have := formalSlope_polynomialInLayersLT θ' p.1 p.2 ⟨s + 1, by omega⟩
      (step1SelectedHead chains h (s + 1))
    intro m' hm' x hx
    exact this m' hm' x (by simp at hx ⊢; omega)
  have hxlayer :
      (((⟨s, by omega⟩ : Fin (m + 1)), step1SelectedHead chains h s)).1.1 = s := rfl
  exact coeffOfVar_top_polynomialInLayersLT _ hxlayer hslopeblock hslopeLE

/-- Canonical dominance tower for the stage-`s` ignition member. -/
noncomputable def step1IgnitionTower {m k d : Nat} {θ' : Params (m + 1) k d}
    (chains : Step1ChainChoices θ') (h : Fin k) (p : ProbePoint d)
    (s : Nat) (hs : s < m) :
    Σ f : FormalPoly (m + 1) k,
      DominanceTowerData (step1HeadChain chains h s (by omega)) f :=
  ⟨step1IgnitionPoly chains h p s hs,
    genericTowerData (step1HeadChain chains h s (by omega)) 2
      (step1IgnitionPoly chains h p s hs)⟩

theorem step1IgnitionTower_degree_pos {m k d : Nat} {θ' : Params (m + 1) k d}
    (chains : Step1ChainChoices θ') (h : Fin k) (p : ProbePoint d)
    (s : Nat) (hs : s < m) :
    ∀ i : Fin s, 1 ≤ (step1IgnitionTower chains h p s hs).2.degree i :=
  genericTower_degree_pos _ 2 _ (step1IgnitionPoly_support chains h p s hs)
    (step1IgnitionPoly_blockDegree chains h p s hs) (by norm_num)

theorem step1IgnitionTower_topConstant {m k d : Nat} {θ' : Params (m + 1) k d}
    (chains : Step1ChainChoices θ') (h : Fin k) (p : ProbePoint d)
    (s : Nat) (hs : s < m) :
    DominanceTowerTopConstant (step1IgnitionTower chains h p s hs).2 :=
  genericTower_topConstant _ 2 _ (step1IgnitionPoly_support chains h p s hs)
    (step1IgnitionPoly_blockDegree chains h p s hs)

theorem step1IgnitionTower_finalCoeff {m k d : Nat} {θ' : Params (m + 1) k d}
    (chains : Step1ChainChoices θ') (h : Fin k) (p : ProbePoint d)
    (s : Nat) (hs : s < m) :
    DominanceTowerFinalCoeff (step1IgnitionTower chains h p s hs).2 :=
  genericTower_finalCoeff _ 2 _ (step1IgnitionPoly_support chains h p s hs)
    (step1IgnitionPoly_blockDegree chains h p s hs)

theorem step1IgnitionTower_evalRecurrence {m k d : Nat} {θ' : Params (m + 1) k d}
    (chains : Step1ChainChoices θ') (h : Fin k) (p : ProbePoint d)
    (s : Nat) (hs : s < m) :
    DominanceTowerEvalRecurrence (step1IgnitionTower chains h p s hs).2 :=
  genericTower_evalRecurrence _ 2 _ (step1IgnitionPoly_support chains h p s hs)
    (step1IgnitionPoly_blockDegree chains h p s hs)

theorem step1IgnitionTower_leadingCoeff_support {m k d : Nat} {θ' : Params (m + 1) k d}
    (chains : Step1ChainChoices θ') (h : Fin k) (p : ProbePoint d)
    (s : Nat) (hs : s < m) :
    ∀ (i : Nat) (hi : i ≤ s),
      PolynomialInLayersLE i ((step1IgnitionTower chains h p s hs).2.leadingCoeff i hi) :=
  genericTower_leadingCoeff_support _ 2 _ (step1IgnitionPoly_support chains h p s hs)
    (step1IgnitionPoly_blockDegree chains h p s hs)

theorem step1IgnitionTower_lowerCoeff_support {m k d : Nat} {θ' : Params (m + 1) k d}
    (chains : Step1ChainChoices θ') (h : Fin k) (p : ProbePoint d)
    (s : Nat) (hs : s < m) :
    ∀ (i : Fin s) (t : Fin ((step1IgnitionTower chains h p s hs).2.degree i)),
      PolynomialInLayersLE i.1 ((step1IgnitionTower chains h p s hs).2.lowerCoeff i t) ∧
        (step1HeadChain chains h s (by omega)).selectedVar i ∉
          ((step1IgnitionTower chains h p s hs).2.lowerCoeff i t).vars :=
  fun i t =>
    ⟨genericTower_lowerCoeff_support _ 2 _ (step1IgnitionPoly_support chains h p s hs)
        (step1IgnitionPoly_blockDegree chains h p s hs) i t,
      genericTower_lowerCoeff_notMem _ 2 _ (step1IgnitionPoly_support chains h p s hs)
        (step1IgnitionPoly_blockDegree chains h p s hs) i t⟩

/-! ### Canonical residue tower -/

theorem blockMultiAffine_blockDegreeLE {L k : Nat} {f : FormalPoly L k}
    (hf : BlockMultiAffine f) : BlockDegreeLE 1 f := by
  intro m hm l
  exact (hf m hm).block_sum_le_one l

/-- The residue polynomial `g_ι = e_ι^⊤ V_{m,a_m} w_m`: the `ι`-coordinate of the
selected value matrix applied to the terminal formal `w`-stream. -/
noncomputable def step1ResiduePoly {m k d : Nat} {θ' : Params (m + 1) k d}
    (chains : Step1ChainChoices θ') (h : Fin k) (p : ProbePoint d) (ι : Fin d) :
    FormalPoly (m + 1) k :=
  (realMatrixToFormal (valueMatrix θ' ⟨m, by omega⟩ (step1SelectedHead chains h m)) *ᵥ
    formalW θ' p.1 p.2 m (by omega)) ι

theorem step1ResiduePoly_layerBounded {m k d : Nat} {θ' : Params (m + 1) k d}
    (chains : Step1ChainChoices θ') (h : Fin k) (p : ProbePoint d) (ι : Fin d) :
    LayerBoundedBlockAffine m (step1ResiduePoly chains h p ι) := by
  have hw : ∀ j : Fin d, LayerBoundedBlockAffine m (formalW θ' p.1 p.2 m (by omega) j) :=
    fun j => (formalPoint_layerBoundedBlockAffine θ' p.1 p.2 m (by omega)).1 j
  exact layerBounded_realMatrixToFormal_mulVec
    (valueMatrix θ' ⟨m, by omega⟩ (step1SelectedHead chains h m)) hw ι

theorem step1ResiduePoly_blockDegree {m k d : Nat} {θ' : Params (m + 1) k d}
    (chains : Step1ChainChoices θ') (h : Fin k) (p : ProbePoint d) (ι : Fin d) :
    BlockDegreeLE 1 (step1ResiduePoly chains h p ι) :=
  blockMultiAffine_blockDegreeLE (step1ResiduePoly_layerBounded chains h p ι).block

theorem step1ResiduePoly_support {m k d : Nat} {θ' : Params (m + 1) k d}
    (chains : Step1ChainChoices θ') (h : Fin k) (p : ProbePoint d) (ι : Fin d) :
    PolynomialInLayersLT m (step1ResiduePoly chains h p ι) :=
  (step1ResiduePoly_layerBounded chains h p ι).support_lt

/-- Canonical dominance tower for the residue member `g_ι`. -/
noncomputable def step1ResidueTower {m k d : Nat} {θ' : Params (m + 1) k d}
    (chains : Step1ChainChoices θ') (h : Fin k) (p : ProbePoint d) (ι : Fin d) :
    Σ f : FormalPoly (m + 1) k,
      DominanceTowerData (step1HeadChain chains h m (by omega)) f :=
  ⟨step1ResiduePoly chains h p ι,
    genericTowerData (step1HeadChain chains h m (by omega)) 1
      (step1ResiduePoly chains h p ι)⟩

theorem step1ResidueTower_degree_pos {m k d : Nat} {θ' : Params (m + 1) k d}
    (chains : Step1ChainChoices θ') (h : Fin k) (p : ProbePoint d) (ι : Fin d) :
    ∀ i : Fin m, 1 ≤ (step1ResidueTower chains h p ι).2.degree i :=
  genericTower_degree_pos _ 1 _ (step1ResiduePoly_support chains h p ι)
    (step1ResiduePoly_blockDegree chains h p ι) (le_refl 1)

theorem step1ResidueTower_topConstant {m k d : Nat} {θ' : Params (m + 1) k d}
    (chains : Step1ChainChoices θ') (h : Fin k) (p : ProbePoint d) (ι : Fin d) :
    DominanceTowerTopConstant (step1ResidueTower chains h p ι).2 :=
  genericTower_topConstant _ 1 _ (step1ResiduePoly_support chains h p ι)
    (step1ResiduePoly_blockDegree chains h p ι)

theorem step1ResidueTower_finalCoeff {m k d : Nat} {θ' : Params (m + 1) k d}
    (chains : Step1ChainChoices θ') (h : Fin k) (p : ProbePoint d) (ι : Fin d) :
    DominanceTowerFinalCoeff (step1ResidueTower chains h p ι).2 :=
  genericTower_finalCoeff _ 1 _ (step1ResiduePoly_support chains h p ι)
    (step1ResiduePoly_blockDegree chains h p ι)

theorem step1ResidueTower_evalRecurrence {m k d : Nat} {θ' : Params (m + 1) k d}
    (chains : Step1ChainChoices θ') (h : Fin k) (p : ProbePoint d) (ι : Fin d) :
    DominanceTowerEvalRecurrence (step1ResidueTower chains h p ι).2 :=
  genericTower_evalRecurrence _ 1 _ (step1ResiduePoly_support chains h p ι)
    (step1ResiduePoly_blockDegree chains h p ι)

theorem step1ResidueTower_leadingCoeff_support {m k d : Nat} {θ' : Params (m + 1) k d}
    (chains : Step1ChainChoices θ') (h : Fin k) (p : ProbePoint d) (ι : Fin d) :
    ∀ (i : Nat) (hi : i ≤ m),
      PolynomialInLayersLE i ((step1ResidueTower chains h p ι).2.leadingCoeff i hi) :=
  genericTower_leadingCoeff_support _ 1 _ (step1ResiduePoly_support chains h p ι)
    (step1ResiduePoly_blockDegree chains h p ι)

theorem step1ResidueTower_lowerCoeff_support {m k d : Nat} {θ' : Params (m + 1) k d}
    (chains : Step1ChainChoices θ') (h : Fin k) (p : ProbePoint d) (ι : Fin d) :
    ∀ (i : Fin m) (t : Fin ((step1ResidueTower chains h p ι).2.degree i)),
      PolynomialInLayersLE i.1 ((step1ResidueTower chains h p ι).2.lowerCoeff i t) ∧
        (step1HeadChain chains h m (by omega)).selectedVar i ∉
          ((step1ResidueTower chains h p ι).2.lowerCoeff i t).vars :=
  fun i t =>
    ⟨genericTower_lowerCoeff_support _ 1 _ (step1ResiduePoly_support chains h p ι)
        (step1ResiduePoly_blockDegree chains h p ι) i t,
      genericTower_lowerCoeff_notMem _ 1 _ (step1ResiduePoly_support chains h p ι)
        (step1ResiduePoly_blockDegree chains h p ι) i t⟩



/-! ### coeffOfVar as a pointwise coefficient -/

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
          · simp [Finsupp.erase_ne hyx, Finsupp.single_apply, Ne.symm hyx]
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

/-! ### Vanishing of coefficients above the layer support -/

theorem coeff_eq_zero_of_layerLT {L k N : Nat} {g : FormalPoly L k}
    (hg : PolynomialInLayersLT N g) {u : FormalVar L k →₀ Nat}
    {x : FormalVar L k} (hx : N ≤ x.1.1) (hux : u x ≠ 0) :
    g.coeff u = 0 := by
  by_contra hc
  exact hux (hg u (MvPolynomial.mem_support_iff.mpr hc) x hx)

/-! ### The w-stream selected-monomial coefficient -/

section WStream

variable {m k d : Nat} {θ' : Params (m + 1) k d}
    (chains : Step1ChainChoices θ') (h : Fin k) (w v : Vec d)

/-- The fixed depth-`m+1` selected chain. -/
noncomputable def cFull : HeadChain (m + 1) k (m + 1) := step1HeadChain chains h (m + 1) le_rfl

/-- The full selected monomial `∏_{l<N} ζ_l`. -/
noncomputable def selMono (N : Nat) (hN : N ≤ m + 1) : FormalVar (m + 1) k →₀ Nat :=
  ∑ i : Fin N, Finsupp.single ((cFull chains h).selectedVar (Fin.castLE hN i)) 1

/-- The selected value product for the first `N` layers. -/
noncomputable def svpN (N : Nat) (hN : N ≤ m + 1) : Matrix (Fin d) (Fin d) ℝ :=
  HeadChain.selectedValueProduct θ' (cFull chains h) N hN

theorem cFull_selectedVar {N : Nat} (hN : N ≤ m + 1) (i : Fin N) :
    (cFull chains h).selectedVar (Fin.castLE hN i) =
      ((⟨i.1, by omega⟩ : Fin (m + 1)), step1SelectedHead chains h i.1) := by
  simp [cFull, step1HeadChain, HeadChain.selectedVar, HeadChain.layer, Fin.castLE]

theorem selMono_succ (N : Nat) (hN1 : N + 1 ≤ m + 1) :
    selMono chains h (N + 1) hN1 =
      selMono chains h N (by omega) +
        Finsupp.single ((⟨N, by omega⟩ : Fin (m + 1)), step1SelectedHead chains h N) 1 := by
  rw [selMono, selMono, Fin.sum_univ_castSucc]
  have hlast : (cFull chains h).selectedVar (Fin.castLE hN1 (Fin.last N)) =
      ((⟨N, by omega⟩ : Fin (m + 1)), step1SelectedHead chains h N) := by
    rw [cFull_selectedVar chains h hN1 (Fin.last N)]; simp [Fin.val_last]
  rw [hlast]
  rfl

/-- The layer-`N` selected variable is exactly the `N`-th monomial factor. -/
theorem selMono_apply_layerN (N : Nat) (hN1 : N + 1 ≤ m + 1) (a : Fin k) :
    (selMono chains h (N + 1) hN1) ((⟨N, by omega⟩ : Fin (m + 1)), a) =
      if a = step1SelectedHead chains h N then 1 else 0 := by
  rw [selMono_succ]
  rw [Finsupp.add_apply]
  have h0 : (selMono chains h N (by omega))
      ((⟨N, by omega⟩ : Fin (m + 1)), a) = 0 := by
    rw [selMono]
    rw [Finsupp.finset_sum_apply]
    apply Finset.sum_eq_zero
    intro i _
    rw [Finsupp.single_apply, if_neg]
    rw [cFull_selectedVar]
    intro heq
    have := congrArg (fun x : FormalVar (m + 1) k => x.1.1) heq
    simp at this
    omega
  rw [h0, zero_add, Finsupp.single_apply]
  have hpair :
      (((⟨N, by omega⟩ : Fin (m + 1)), step1SelectedHead chains h N) =
        ((⟨N, by omega⟩ : Fin (m + 1)), a)) ↔ (a = step1SelectedHead chains h N) := by
    rw [Prod.ext_iff]
    constructor
    · rintro ⟨_, h2⟩; exact h2.symm
    · intro h2; exact ⟨rfl, h2.symm⟩
  exact if_congr hpair rfl rfl

/-- Stream step for the `w`-coordinate. -/
theorem formalW_succ_vec (N : Nat) (hN1 : N + 1 ≤ m + 1) :
    formalW θ' w v (N + 1) hN1 =
      (formalCollapseMatrix θ' ⟨N, by omega⟩ - formalGatedValueSum θ' ⟨N, by omega⟩) *ᵥ
        formalW θ' w v N (by omega) := by
  show (formalPoint θ' w v (N + 1) hN1).1 = _
  rw [formalPoint_succ]
  rfl

/-- Coefficient of a constant-matrix times a formal vector. -/
theorem coeff_realMatrix_mulVec {M : Matrix (Fin d) (Fin d) ℝ}
    {g : FormalVec (m + 1) k d} (ι : Fin d) (u : FormalVar (m + 1) k →₀ Nat) :
    ((realMatrixToFormal M *ᵥ g) ι).coeff u = ∑ j : Fin d, M ι j * (g j).coeff u := by
  classical
  rw [Matrix.mulVec, dotProduct, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [realMatrixToFormal_apply]
  show (formalConst (M ι j) * g j).coeff u = M ι j * (g j).coeff u
  rw [formalConst, MvPolynomial.coeff_C_mul]

/-- Successor recursion for the selected value product. -/
theorem svpN_succ (N : Nat) (hN1 : N + 1 ≤ m + 1) :
    svpN chains h (N + 1) hN1 =
      valueMatrix θ' ⟨N, by omega⟩ (step1SelectedHead chains h N) *
        svpN chains h N (by omega) := by
  rw [svpN, HeadChain.selectedValueProduct_succ]
  rfl

/-- Membership of the layer-`N` variable in the selected monomial's support. -/
theorem selMono_succ_mem_support (N : Nat) (hN1 : N + 1 ≤ m + 1) (a : Fin k) :
    ((⟨N, by omega⟩ : Fin (m + 1)), a) ∈ (selMono chains h (N + 1) hN1).support ↔
      a = step1SelectedHead chains h N := by
  rw [Finsupp.mem_support_iff, selMono_apply_layerN]
  by_cases ha : a = step1SelectedHead chains h N <;> simp [ha]

/-- Removing the layer-`N` selected variable returns the shorter monomial. -/
theorem selMono_succ_sub (N : Nat) (hN1 : N + 1 ≤ m + 1) :
    selMono chains h (N + 1) hN1 -
        Finsupp.single ((⟨N, by omega⟩ : Fin (m + 1)), step1SelectedHead chains h N) 1 =
      selMono chains h N (by omega) := by
  rw [selMono_succ]
  simp

/-- **B2**: the fully selected coefficient of the formal `w`-stream equals the
signed selected value product applied to `w`. -/
theorem wStream_selCoeff : ∀ (N : Nat) (hN : N ≤ m + 1) (ι : Fin d),
    (formalW θ' w v N hN ι).coeff (selMono chains h N hN) =
      (-1 : ℝ) ^ N * (svpN chains h N hN *ᵥ w) ι := by
  intro N
  induction N with
  | zero =>
      intro hN ι
      rw [selMono]
      simp only [Finset.univ_eq_empty, Finset.sum_empty, formalW_zero, realVecToFormal_apply,
        formalConst, MvPolynomial.coeff_zero_C, pow_zero, one_mul]
      rw [svpN]
      simp [HeadChain.selectedValueProduct, Matrix.one_mulVec]
  | succ N ih =>
      intro hN1 ι
      rw [formalW_succ_vec, Matrix.sub_mulVec, Pi.sub_apply, MvPolynomial.coeff_sub]
      -- collapse term vanishes
      have hcollapse :
          ((formalCollapseMatrix θ' ⟨N, by omega⟩ *ᵥ formalW θ' w v N (by omega)) ι).coeff
              (selMono chains h (N + 1) hN1) = 0 := by
        rw [formalCollapseMatrix, coeff_realMatrix_mulVec]
        apply Finset.sum_eq_zero
        intro j _
        have hzero :
            (formalW θ' w v N (by omega) j).coeff (selMono chains h (N + 1) hN1) = 0 := by
          refine coeff_eq_zero_of_layerLT
            (((formalPoint_layerBoundedBlockAffine θ' w v N (by omega)).1 j).support_lt)
            (x := ((⟨N, by omega⟩ : Fin (m + 1)), step1SelectedHead chains h N))
            (by simp) ?_
          rw [selMono_apply_layerN]; simp
        rw [hzero, mul_zero]
      rw [hcollapse, zero_sub]
      -- D term
      have hD :
          ((formalGatedValueSum θ' ⟨N, by omega⟩ *ᵥ formalW θ' w v N (by omega)) ι).coeff
              (selMono chains h (N + 1) hN1) =
            (-1 : ℝ) ^ N * (svpN chains h (N + 1) hN1 *ᵥ w) ι := by
        have hgvs :
            (formalGatedValueSum θ' ⟨N, by omega⟩ *ᵥ formalW θ' w v N (by omega)) ι =
              ∑ a : Fin k, formalGate ⟨N, by omega⟩ a *
                (formalValueMatrix θ' ⟨N, by omega⟩ a *ᵥ formalW θ' w v N (by omega)) ι := by
          rw [formalGatedValueSum, Matrix.sum_mulVec, Finset.sum_apply]
          apply Finset.sum_congr rfl
          intro a _
          rw [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
        rw [hgvs, MvPolynomial.coeff_sum]
        rw [Finset.sum_eq_single (step1SelectedHead chains h N)]
        · -- the selected term
          rw [formalGate, MvPolynomial.coeff_X_mul',
            if_pos ((selMono_succ_mem_support chains h N hN1 _).mpr rfl),
            selMono_succ_sub, formalValueMatrix, coeff_realMatrix_mulVec,
            svpN_succ, ← Matrix.mulVec_mulVec]
          rw [show ((valueMatrix θ' ⟨N, by omega⟩ (step1SelectedHead chains h N)) *ᵥ
              (svpN chains h N (by omega) *ᵥ w)) ι
              = ∑ j : Fin d, valueMatrix θ' ⟨N, by omega⟩ (step1SelectedHead chains h N) ι j *
                (svpN chains h N (by omega) *ᵥ w) j from rfl,
            Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [ih (by omega) j]
          ring
        · intro a _ hane
          rw [formalGate, MvPolynomial.coeff_X_mul',
            if_neg (fun hmem => hane ((selMono_succ_mem_support chains h N hN1 a).mp hmem))]
        · intro hnot; exact absurd (Finset.mem_univ _) hnot
      rw [hD]
      rw [pow_succ]
      ring

/-- The generic top-extraction exponent for `step1HeadChain` is the selected
monomial. -/
theorem headChain_exp_eq_selMono (N : Nat) (hN : N ≤ m + 1) :
    (∑ i : Fin N, Finsupp.single ((step1HeadChain chains h N hN).selectedVar i) 1)
      = selMono chains h N hN := by
  rw [selMono]
  apply Finset.sum_congr rfl
  intro i _
  rw [cFull_selectedVar, step1HeadChain_selectedVar]

/-- `svpN` at full depth is the cascade residue product. -/
theorem svpN_full_mulVec (p : ProbePoint d) :
    svpN chains h (m + 1) le_rfl *ᵥ p.1 = cascadeResidueVector (chains h) p := by
  rw [svpN, cFull]
  exact step1HeadChain_selectedValueProduct_mulVec_eq_cascadeResidueVector chains p h

/-- **Residue top-constant identity.** -/
theorem step1ResidueTower_topConstant_eq (p : ProbePoint d) (ι : Fin d) :
    (step1ResidueTower chains h p ι).2.topConstant =
      (-1 : ℝ) ^ m * cascadeResidueVector (chains h) p ι := by
  show (topLeadingCoeff (step1HeadChain chains h m (by omega)) 1
      (step1ResiduePoly chains h p ι) m).coeff 0 = _
  rw [topLeadingCoeff_coeff_zero, headChain_exp_eq_selMono]
  -- f_residue.coeff (selMono m) via the constant matrix and B2
  rw [step1ResiduePoly, coeff_realMatrix_mulVec]
  have hval : ∀ j : Fin d,
      valueMatrix θ' ⟨m, by omega⟩ (step1SelectedHead chains h m) ι j *
          (formalW θ' p.1 p.2 m (by omega) j).coeff (selMono chains h m (by omega)) =
        (-1 : ℝ) ^ m *
          (valueMatrix θ' ⟨m, by omega⟩ (step1SelectedHead chains h m) ι j *
            (svpN chains h m (by omega) *ᵥ p.1) j) := by
    intro j
    rw [wStream_selCoeff chains h p.1 p.2 m (by omega) j]; ring
  rw [Finset.sum_congr rfl (fun j _ => hval j)]
  -- pull out the sign and recognize the matrix product
  rw [← Finset.mul_sum]
  have hmat :
      ∑ j : Fin d,
          valueMatrix θ' ⟨m, by omega⟩ (step1SelectedHead chains h m) ι j *
            (svpN chains h m (by omega) *ᵥ p.1) j =
        (svpN chains h (m + 1) le_rfl *ᵥ p.1) ι := by
    rw [svpN_succ]
    rw [← Matrix.mulVec_mulVec]
    rfl
  rw [mul_comm ((-1 : ℝ) ^ m) _, hmat, svpN_full_mulVec, mul_comm]

/-- The residue tower's top constant is nonzero on a visible coordinate. -/
theorem step1ResidueTower_topConstant_ne_zero (p : ProbePoint d) (ι : Fin d)
    (hι : cascadeResidueVector (chains h) p ι ≠ 0) :
    (step1ResidueTower chains h p ι).2.topConstant ≠ 0 := by
  rw [step1ResidueTower_topConstant_eq]
  exact mul_ne_zero (pow_ne_zero m (by norm_num)) hι

end WStream



/-- **Bilinear two-factor extraction.** For block-multiaffine factors, the
coefficient of a doubled monomial is the product of the single coefficients. -/
theorem coeff_mul_double {L k : Nat} (d0 : FormalVar L k →₀ Nat)
    {P Q : FormalPoly L k} (hP : BlockMultiAffine P) (hQ : BlockMultiAffine Q) :
    (P * Q).coeff (d0 + d0) = P.coeff d0 * Q.coeff d0 := by
  classical
  rw [MvPolynomial.coeff_mul]
  have hmem : (d0, d0) ∈ Finset.antidiagonal (d0 + d0) := by rw [Finset.mem_antidiagonal]
  refine (Finset.sum_eq_single_of_mem (d0, d0) hmem ?_).trans rfl
  · intro b hb hbne
    rw [Finset.mem_antidiagonal] at hb
    by_cases hP0 : P.coeff b.1 = 0
    · rw [hP0, zero_mul]
    · by_cases hQ0 : Q.coeff b.2 = 0
      · rw [hQ0, mul_zero]
      · exfalso
        apply hbne
        have hb1 := MvPolynomial.mem_support_iff.mpr hP0
        have hb2 := MvPolynomial.mem_support_iff.mpr hQ0
        have hdP : ∀ x, b.1 x ≤ 1 := fun x =>
          (MvPolynomial.degreeOf_le_iff.mp (blockMultiAffine_degreeOf_le hP)) b.1 hb1
        have hdQ : ∀ x, b.2 x ≤ 1 := fun x =>
          (MvPolynomial.degreeOf_le_iff.mp (blockMultiAffine_degreeOf_le hQ)) b.2 hb2
        have hb1eq : b.1 = d0 := by
          ext x
          have hsum := Finsupp.ext_iff.mp hb x
          simp only [Finsupp.add_apply] at hsum
          have := hdP x; have := hdQ x; omega
        have hb2eq : b.2 = d0 := by
          ext x
          have hsum := Finsupp.ext_iff.mp hb x
          simp only [Finsupp.add_apply] at hsum
          have := hdP x; have := hdQ x; omega
        rw [Prod.ext_iff]; exact ⟨hb1eq, hb2eq⟩

section VStream

variable {m k d : Nat} {θ' : Params (m + 1) k d}
    (chains : Step1ChainChoices θ') (h : Fin k) (w v : Vec d)

/-- The gated-value-sum contribution to a stream coefficient. -/
theorem dTerm_selCoeff (N : Nat) (hN1 : N + 1 ≤ m + 1) (ι : Fin d) :
    ((formalGatedValueSum θ' ⟨N, by omega⟩ *ᵥ formalW θ' w v N (by omega)) ι).coeff
        (selMono chains h (N + 1) hN1) =
      (-1 : ℝ) ^ N * (svpN chains h (N + 1) hN1 *ᵥ w) ι := by
  have hgvs :
      (formalGatedValueSum θ' ⟨N, by omega⟩ *ᵥ formalW θ' w v N (by omega)) ι =
        ∑ a : Fin k, formalGate ⟨N, by omega⟩ a *
          (formalValueMatrix θ' ⟨N, by omega⟩ a *ᵥ formalW θ' w v N (by omega)) ι := by
    rw [formalGatedValueSum, Matrix.sum_mulVec, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro a _
    rw [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
  rw [hgvs, MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single (step1SelectedHead chains h N)]
  · rw [formalGate, MvPolynomial.coeff_X_mul',
      if_pos ((selMono_succ_mem_support chains h N hN1 _).mpr rfl),
      selMono_succ_sub, formalValueMatrix, coeff_realMatrix_mulVec,
      svpN_succ, ← Matrix.mulVec_mulVec]
    rw [show ((valueMatrix θ' ⟨N, by omega⟩ (step1SelectedHead chains h N)) *ᵥ
        (svpN chains h N (by omega) *ᵥ w)) ι
        = ∑ j : Fin d, valueMatrix θ' ⟨N, by omega⟩ (step1SelectedHead chains h N) ι j *
          (svpN chains h N (by omega) *ᵥ w) j from rfl,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [wStream_selCoeff chains h w v N (by omega) j]
    ring
  · intro a _ hane
    rw [formalGate, MvPolynomial.coeff_X_mul',
      if_neg (fun hmem => hane ((selMono_succ_mem_support chains h N hN1 a).mp hmem))]
  · intro hnot; exact absurd (Finset.mem_univ _) hnot

/-- Stream step for the `v`-coordinate. -/
theorem formalV_succ_vec (N : Nat) (hN1 : N + 1 ≤ m + 1) :
    formalV θ' w v (N + 1) hN1 =
      formalCollapseMatrix θ' ⟨N, by omega⟩ *ᵥ formalV θ' w v N (by omega) +
        formalGatedValueSum θ' ⟨N, by omega⟩ *ᵥ formalW θ' w v N (by omega) := by
  show (formalPoint θ' w v (N + 1) hN1).2 = _
  rw [formalPoint_succ]
  rfl

/-- **v-stream one step.** -/
theorem vStream_selCoeff_succ (N : Nat) (hN1 : N + 1 ≤ m + 1) (ι : Fin d) :
    (formalV θ' w v (N + 1) hN1 ι).coeff (selMono chains h (N + 1) hN1) =
      (-1 : ℝ) ^ N * (svpN chains h (N + 1) hN1 *ᵥ w) ι := by
  rw [formalV_succ_vec, Pi.add_apply, MvPolynomial.coeff_add]
  have hcollapse :
      ((formalCollapseMatrix θ' ⟨N, by omega⟩ *ᵥ formalV θ' w v N (by omega)) ι).coeff
          (selMono chains h (N + 1) hN1) = 0 := by
    rw [formalCollapseMatrix, coeff_realMatrix_mulVec]
    apply Finset.sum_eq_zero
    intro j _
    have hzero :
        (formalV θ' w v N (by omega) j).coeff (selMono chains h (N + 1) hN1) = 0 := by
      refine coeff_eq_zero_of_layerLT
        (((formalPoint_layerBoundedBlockAffine θ' w v N (by omega)).2 j).support_lt)
        (x := ((⟨N, by omega⟩ : Fin (m + 1)), step1SelectedHead chains h N))
        (by simp) ?_
      rw [selMono_apply_layerN]; simp
    rw [hzero, mul_zero]
  rw [hcollapse, zero_add, dTerm_selCoeff]

end VStream

section IgnitionWiring

variable {m k d : Nat} {θ' : Params (m + 1) k d}
    (chains : Step1ChainChoices θ') (h : Fin k)

/-- `svpN` is a prefix of the length-`s+1` selected chain product. -/
theorem svpN_eq_headChain (s : Nat) (hs : s < m) :
    svpN chains h (s + 1) (by omega) =
      HeadChain.selectedValueProduct θ' (step1HeadChain chains h (s + 1) (by omega))
        (s + 1) le_rfl := by
  rw [svpN, cFull]
  exact step1HeadChain_selectedValueProduct_prefix chains h (m + 1) (s + 1) le_rfl (by omega)

/-- Chains-level ignition cascade bridge. -/
theorem ignition_cascade_bridge (p : ProbePoint d) (s : Nat) (hs : s < m) :
    matrixBilin (attentionMatrix θ' ⟨s + 1, by omega⟩ (step1SelectedHead chains h (s + 1)))
        (svpN chains h (s + 1) (by omega) *ᵥ p.1)
        (svpN chains h (s + 1) (by omega) *ᵥ p.1) =
      cascadeIgnitionQuadratic (chains h) ⟨s, hs⟩ p := by
  rw [svpN_eq_headChain chains h s hs, step1SelectedHead_succ_of_lt chains h hs,
    show (⟨s + 1, by omega⟩ : Fin (m + 1)) = laterLayer ⟨s, hs⟩ from rfl]
  rw [step1HeadChain_selectedValueProduct_eq_cascadeProduct_fin chains h ⟨s, hs⟩,
    cascadeIgnitionQuadratic, cascadeIgnitionMatrix, matrixBilin_sym_transpose_mul_mul_self]

/-- The degree-2 selected exponent is the doubled selected monomial. -/
theorem headChain_exp2_eq (N : Nat) (hN : N ≤ m + 1) :
    (∑ i : Fin N, Finsupp.single ((step1HeadChain chains h N hN).selectedVar i) 2)
      = selMono chains h N hN + selMono chains h N hN := by
  rw [selMono, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [cFull_selectedVar, step1HeadChain_selectedVar]
  rw [← Finsupp.single_add]

/-- **Bilinear reduction of the ignition slope coefficient.** -/
theorem slope_selCoeff (p : ProbePoint d) (s : Nat) (hs : s < m) :
    (formalSlope θ' p.1 p.2 ⟨s + 1, by omega⟩ (step1SelectedHead chains h (s + 1))).coeff
        (selMono chains h (s + 1) (by omega) + selMono chains h (s + 1) (by omega)) =
      -matrixBilin (attentionMatrix θ' ⟨s + 1, by omega⟩ (step1SelectedHead chains h (s + 1)))
        (svpN chains h (s + 1) (by omega) *ᵥ p.1)
        (svpN chains h (s + 1) (by omega) *ᵥ p.1) := by
  set A := attentionMatrix θ' ⟨s + 1, by omega⟩ (step1SelectedHead chains h (s + 1)) with hA
  set V := formalV θ' p.1 p.2 (s + 1) (by omega) with hV
  set m0 := selMono chains h (s + 1) (by omega) with hm0
  set sv := svpN chains h (s + 1) (by omega) *ᵥ p.1 with hsv
  have hsign : (-1 : ℝ) ^ (s + 1) * (-1) ^ s = -1 := by
    rw [← pow_add, show s + 1 + s = 2 * s + 1 by ring, pow_succ, pow_mul]
    norm_num
  rw [formalSlope, formalBilin, dotProduct, MvPolynomial.coeff_sum]
  have hbma : ∀ a : Fin d, BlockMultiAffine ((realMatrixToFormal A *ᵥ V) a) := by
    intro a
    exact (layerBounded_realMatrixToFormal_mulVec A
      (fun b => (formalPoint_layerBoundedBlockAffine θ' p.1 p.2 (s + 1) (by omega)).2 b) a).block
  have hsummand : ∀ a : Fin d,
      (formalW θ' p.1 p.2 (s + 1) (by omega) a * (realMatrixToFormal A *ᵥ V) a).coeff (m0 + m0) =
        ((-1 : ℝ) ^ (s + 1) * sv a) * ((-1 : ℝ) ^ s * (A *ᵥ sv) a) := by
    intro a
    rw [coeff_mul_double m0 (formalW_blockMultiAffine θ' p.1 p.2 (s + 1) (by omega) a) (hbma a),
      wStream_selCoeff chains h p.1 p.2 (s + 1) (by omega) a]
    congr 1
    rw [coeff_realMatrix_mulVec, show (A *ᵥ sv) a = ∑ b : Fin d, A a b * sv b from rfl,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [vStream_selCoeff_succ chains h p.1 p.2 s (by omega) b]
    ring
  rw [Finset.sum_congr rfl (fun a _ => hsummand a)]
  rw [matrixBilin, dotProduct, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  linear_combination (sv a * (A *ᵥ sv) a) * hsign

/-- The selected monomial vanishes at variables in layers `≥ N`. -/
theorem selMono_apply_zero_of_ge (N : Nat) (hN : N ≤ m + 1) (l : Fin (m + 1)) (a : Fin k)
    (hl : N ≤ l.1) : (selMono chains h N hN) (l, a) = 0 := by
  rw [selMono, Finsupp.finset_sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [Finsupp.single_apply, if_neg]
  rw [cFull_selectedVar]
  intro heq
  have := congrArg (fun x : FormalVar (m + 1) k => x.1.1) heq
  simp only at this
  omega

/-- **Ignition top-constant identity.** -/
theorem step1IgnitionTower_topConstant_eq (p : ProbePoint d) (s : Nat) (hs : s < m) :
    (step1IgnitionTower chains h p s hs).2.topConstant =
      -(cascadeIgnitionQuadratic (chains h) ⟨s, hs⟩ p) := by
  show (topLeadingCoeff (step1HeadChain chains h s (by omega)) 2
      (step1IgnitionPoly chains h p s hs) s).coeff 0 = _
  rw [topLeadingCoeff_coeff_zero, headChain_exp2_eq, step1IgnitionPoly, coeffOfVar_coeff]
  have hcond :
      (selMono chains h s (by omega) + selMono chains h s (by omega))
        (((⟨s, by omega⟩ : Fin (m + 1)), step1SelectedHead chains h s)) = 0 := by
    rw [Finsupp.add_apply,
      selMono_apply_zero_of_ge chains h s (by omega) ⟨s, by omega⟩ _ (le_refl s)]
  rw [if_pos hcond]
  have hexp :
      (selMono chains h s (by omega) + selMono chains h s (by omega)) +
          Finsupp.single (((⟨s, by omega⟩ : Fin (m + 1)), step1SelectedHead chains h s)) 2 =
        selMono chains h (s + 1) (by omega) + selMono chains h (s + 1) (by omega) := by
    rw [selMono_succ chains h s (by omega),
      show (2 : Nat) = 1 + 1 from rfl, Finsupp.single_add]
    abel
  rw [hexp, slope_selCoeff chains h p s hs, ignition_cascade_bridge chains h p s hs]

/-- The ignition tower's top constant is nonzero at an igniting probe. -/
theorem step1IgnitionTower_topConstant_ne_zero (p : ProbePoint d) (s : Nat) (hs : s < m)
    (hig : cascadeIgnitionQuadratic (chains h) ⟨s, hs⟩ p ≠ 0) :
    (step1IgnitionTower chains h p s hs).2.topConstant ≠ 0 := by
  rw [step1IgnitionTower_topConstant_eq]
  exact neg_ne_zero.mpr hig

end IgnitionWiring



section Step1DominanceFamilyMembers

variable {m k d : Nat} {r : Nat} {θ θ' : Params (m + 1) k d}
    (H : Step1StandingHypotheses r θ θ')

/-- Real ignition dominance-family member built from the canonical ignition tower. -/
noncomputable def step1IgnitionDominanceFamilyMember {p : ProbePoint d}
    (hp : p ∈ H.separatedSet) (h : Fin k) (s : Fin m) :
    Step1DominanceFamilyMember H p h where
  idx := Sum.inl s
  poly := (step1IgnitionTower H.chains h p s.1 s.2).1
  tower := (step1IgnitionTower H.chains h p s.1 s.2).2
  degree_pos := step1IgnitionTower_degree_pos H.chains h p s.1 s.2
  topConstant_ne_zero :=
    step1IgnitionTower_topConstant_ne_zero H.chains h p s.1 s.2
      (separatedProbe_ignition_ne_zero H hp h s)
  topConstant := step1IgnitionTower_topConstant H.chains h p s.1 s.2
  finalCoeff := step1IgnitionTower_finalCoeff H.chains h p s.1 s.2
  evalRecurrence := step1IgnitionTower_evalRecurrence H.chains h p s.1 s.2
  leadingCoeff_support := step1IgnitionTower_leadingCoeff_support H.chains h p s.1 s.2
  lowerCoeff_support := fun i t =>
    (step1IgnitionTower_lowerCoeff_support H.chains h p s.1 s.2 i t).1
  lowerCoeff_selectedVar_notMem := fun i t =>
    (step1IgnitionTower_lowerCoeff_support H.chains h p s.1 s.2 i t).2

/-- Real residue dominance-family member built from the canonical residue tower. -/
noncomputable def step1ResidueDominanceFamilyMember {p : ProbePoint d}
    (h : Fin k) (ι : Step1ResidueCoordinateIndex H p h) :
    Step1DominanceFamilyMember H p h where
  idx := Sum.inr ι
  poly := (step1ResidueTower H.chains h p ι.1).1
  tower := (step1ResidueTower H.chains h p ι.1).2
  degree_pos := step1ResidueTower_degree_pos H.chains h p ι.1
  topConstant_ne_zero :=
    step1ResidueTower_topConstant_ne_zero H.chains h p ι.1 ι.2
  topConstant := step1ResidueTower_topConstant H.chains h p ι.1
  finalCoeff := step1ResidueTower_finalCoeff H.chains h p ι.1
  evalRecurrence := step1ResidueTower_evalRecurrence H.chains h p ι.1
  leadingCoeff_support := step1ResidueTower_leadingCoeff_support H.chains h p ι.1
  lowerCoeff_support := fun i t =>
    (step1ResidueTower_lowerCoeff_support H.chains h p ι.1 i t).1
  lowerCoeff_selectedVar_notMem := fun i t =>
    (step1ResidueTower_lowerCoeff_support H.chains h p ι.1 i t).2

/-- The canonical finite dominance family, built from the real ignition/residue towers. -/
noncomputable def step1DominanceFamily {p : ProbePoint d}
    (hp : p ∈ H.separatedSet) (h : Fin k) :
    Step1DominanceFamilyIndex H p h -> Step1DominanceFamilyMember H p h
  | Sum.inl s => step1IgnitionDominanceFamilyMember H hp h s
  | Sum.inr ι => step1ResidueDominanceFamilyMember H h ι

end Step1DominanceFamilyMembers

end TransformerIdentifiability.NLayer.KHead.Step1
