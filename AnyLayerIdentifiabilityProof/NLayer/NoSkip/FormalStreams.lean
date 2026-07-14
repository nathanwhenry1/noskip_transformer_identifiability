import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Probe

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.NoSkip

/-!
# No-skip formal streams and slope polynomials

The gate-index and polynomial embedding infrastructure is model-neutral.  It is
extracted here without importing the skip-only saturated-dial section of the
`KHead` formal-stream module.  The formal collapse matrix, recursion step,
streams, and slopes use the no-skip matrix
`C_l = ∑_a V_{la}` and contain no residual identity term.
-/

/-- Formal gate-variable index `(layer, head)`. -/
abbrev FormalVar (L k : Nat) : Type := Fin L × Fin k

/-- Polynomial ring in all formal gate variables. -/
abbrev FormalPoly (L k : Nat) : Type := MvPolynomial (FormalVar L k) ℝ

/-- Polynomial-valued model vectors. -/
abbrev FormalVec (L k d : Nat) : Type := Fin d → FormalPoly L k

/-- Real assignments for all formal gate variables. -/
abbrev FormalAssignment (L k : Nat) : Type := FormalVar L k → ℝ

/-- Embed a real scalar as a constant formal polynomial. -/
noncomputable abbrev formalConst {L k : Nat} (x : ℝ) : FormalPoly L k :=
  MvPolynomial.C x

/-- Embed a real vector coordinatewise as formal constants. -/
noncomputable def realVecToFormal {L k d : Nat} (x : Vec d) : FormalVec L k d :=
  fun i ↦ formalConst (L := L) (k := k) (x i)

/-- Embed a real matrix entrywise as formal constants. -/
noncomputable def realMatrixToFormal {L k d : Nat}
    (M : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) (FormalPoly L k) :=
  M.map (MvPolynomial.C : ℝ →+* FormalPoly L k)

@[simp] theorem realVecToFormal_apply {L k d : Nat} (x : Vec d) (i : Fin d) :
    realVecToFormal (L := L) (k := k) x i = formalConst (L := L) (k := k) (x i) :=
  rfl

@[simp] theorem realMatrixToFormal_apply {L k d : Nat}
    (M : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) :
    realMatrixToFormal (L := L) (k := k) M i j =
      formalConst (L := L) (k := k) (M i j) :=
  rfl

/-- The formal gate variable `z_{la}`. -/
noncomputable def formalGate {L k : Nat} (l : Fin L) (a : Fin k) : FormalPoly L k :=
  MvPolynomial.X (l, a)

/-- A value matrix embedded into the formal coefficient ring. -/
noncomputable def formalValueMatrix {L k d : Nat} (θ : Params L k d)
    (l : Fin L) (a : Fin k) : Matrix (Fin d) (Fin d) (FormalPoly L k) :=
  realMatrixToFormal (valueMatrix θ l a)

/-- The no-skip collapsed matrix `C_l = ∑_a V_{la}`, with formal coefficients. -/
noncomputable def formalCollapseMatrix {L k d : Nat} (θ : Params L k d)
    (l : Fin L) : Matrix (Fin d) (Fin d) (FormalPoly L k) :=
  realMatrixToFormal (collapseMatrix θ l)

/-- Formal gated value sum `D_l(z) = ∑_a z_{la} V_{la}`. -/
noncomputable def formalGatedValueSum {L k d : Nat} (θ : Params L k d)
    (l : Fin L) : Matrix (Fin d) (Fin d) (FormalPoly L k) :=
  ∑ a : Fin k, formalGate l a • formalValueMatrix θ l a

/-- One no-skip formal recursion step.

It realizes `w' = (C-D)w` and `v' = Cv + Dw` over the polynomial ring.
-/
noncomputable def formalStepPoint {L k d : Nat} (θ : Params L k d)
    (l : Fin L) (w v : FormalVec L k d) : FormalVec L k d × FormalVec L k d :=
  let D := formalGatedValueSum θ l
  ((formalCollapseMatrix θ l - D) *ᵥ w, formalCollapseMatrix θ l *ᵥ v + D *ᵥ w)

/-- Formal stream pair `(w_n(z), v_n(z))` after `n ≤ L` layers. -/
noncomputable def formalPoint {L k d : Nat} (θ : Params L k d) (w v : Vec d) :
    (n : Nat) → n ≤ L → FormalVec L k d × FormalVec L k d
  | 0, _ => (realVecToFormal w, realVecToFormal v)
  | n + 1, hn =>
      let l : Fin L := ⟨n, Nat.lt_of_succ_le hn⟩
      let prev := formalPoint θ w v n (Nat.le_of_succ_le hn)
      formalStepPoint θ l prev.1 prev.2

/-- Formal contrast stream `w_n(z)`. -/
noncomputable def formalW {L k d : Nat} (θ : Params L k d) (w v : Vec d)
    (n : Nat) (hn : n ≤ L) : FormalVec L k d :=
  (formalPoint θ w v n hn).1

/-- Formal last-token stream `v_n(z)`. -/
noncomputable def formalV {L k d : Nat} (θ : Params L k d) (w v : Vec d)
    (n : Nat) (hn : n ≤ L) : FormalVec L k d :=
  (formalPoint θ w v n hn).2

@[simp] theorem formalW_zero {L k d : Nat} (θ : Params L k d) (w v : Vec d)
    (h0 : 0 ≤ L) :
    formalW θ w v 0 h0 = realVecToFormal w :=
  rfl

@[simp] theorem formalV_zero {L k d : Nat} (θ : Params L k d) (w v : Vec d)
    (h0 : 0 ≤ L) :
    formalV θ w v 0 h0 = realVecToFormal v :=
  rfl

theorem formalPoint_succ {L k d : Nat} (θ : Params L k d) (w v : Vec d)
    {n : Nat} (hn : n + 1 ≤ L) :
    formalPoint θ w v (n + 1) hn =
      formalStepPoint θ ⟨n, Nat.lt_of_succ_le hn⟩
        (formalW θ w v n (Nat.le_of_succ_le hn))
        (formalV θ w v n (Nat.le_of_succ_le hn)) :=
  rfl

/-- Bilinear form over formal polynomial vectors. -/
noncomputable def formalBilin {L k d : Nat} (A : Matrix (Fin d) (Fin d) ℝ)
    (w v : FormalVec L k d) : FormalPoly L k :=
  w ⬝ᵥ realMatrixToFormal A *ᵥ v

/-- Formal slope `φ_{la}=w_l(z)ᵀ A_{la}v_l(z)` in zero-based layer indexing. -/
noncomputable def formalSlope {L k d : Nat} (θ : Params L k d) (w v : Vec d)
    (l : Fin L) (a : Fin k) : FormalPoly L k :=
  formalBilin (attentionMatrix θ l a)
    (formalW θ w v l.1 (Nat.le_of_lt l.2))
    (formalV θ w v l.1 (Nat.le_of_lt l.2))

/-- Evaluate a formal vector at a real gate assignment. -/
noncomputable def evalFormalVec {L k d : Nat} (ρ : FormalAssignment L k)
    (x : FormalVec L k d) : Vec d :=
  fun i ↦ MvPolynomial.eval ρ (x i)

/-- Evaluate a formal matrix at a real gate assignment. -/
noncomputable def evalFormalMatrix {L k d : Nat} (ρ : FormalAssignment L k)
    (M : Matrix (Fin d) (Fin d) (FormalPoly L k)) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j ↦ MvPolynomial.eval ρ (M i j)

@[simp] theorem evalFormalVec_realVecToFormal {L k d : Nat}
    (ρ : FormalAssignment L k) (x : Vec d) :
    evalFormalVec ρ (realVecToFormal (L := L) (k := k) x) = x := by
  ext i
  simp [evalFormalVec, realVecToFormal, formalConst]

@[simp] theorem eval_formalGate {L k : Nat} (ρ : FormalAssignment L k)
    (l : Fin L) (a : Fin k) :
    MvPolynomial.eval ρ (formalGate l a) = ρ (l, a) := by
  simp [formalGate]

@[simp] theorem evalFormalVec_add {L k d : Nat} (ρ : FormalAssignment L k)
    (x y : FormalVec L k d) :
    evalFormalVec ρ (x + y) = evalFormalVec ρ x + evalFormalVec ρ y := by
  ext i
  simp [evalFormalVec]

@[simp] theorem evalFormalVec_sub {L k d : Nat} (ρ : FormalAssignment L k)
    (x y : FormalVec L k d) :
    evalFormalVec ρ (x - y) = evalFormalVec ρ x - evalFormalVec ρ y := by
  ext i
  simp [evalFormalVec]

@[simp] theorem evalFormalVec_smul {L k d : Nat} (ρ : FormalAssignment L k)
    (c : FormalPoly L k) (x : FormalVec L k d) :
    evalFormalVec ρ (c • x) = MvPolynomial.eval ρ c • evalFormalVec ρ x := by
  ext i
  simp [evalFormalVec]

@[simp] theorem evalFormalMatrix_add {L k d : Nat} (ρ : FormalAssignment L k)
    (M N : Matrix (Fin d) (Fin d) (FormalPoly L k)) :
    evalFormalMatrix ρ (M + N) = evalFormalMatrix ρ M + evalFormalMatrix ρ N := by
  ext i j
  simp [evalFormalMatrix]

@[simp] theorem evalFormalMatrix_sub {L k d : Nat} (ρ : FormalAssignment L k)
    (M N : Matrix (Fin d) (Fin d) (FormalPoly L k)) :
    evalFormalMatrix ρ (M - N) = evalFormalMatrix ρ M - evalFormalMatrix ρ N := by
  ext i j
  simp [evalFormalMatrix]

@[simp] theorem evalFormalVec_mulVec {L k d : Nat} (ρ : FormalAssignment L k)
    (M : Matrix (Fin d) (Fin d) (FormalPoly L k)) (x : FormalVec L k d) :
    evalFormalVec ρ (M *ᵥ x) = evalFormalMatrix ρ M *ᵥ evalFormalVec ρ x := by
  ext i
  simp [evalFormalVec, evalFormalMatrix, Matrix.mulVec, dotProduct]

@[simp] theorem evalFormalMatrix_realMatrixToFormal {L k d : Nat}
    (ρ : FormalAssignment L k) (M : Matrix (Fin d) (Fin d) ℝ) :
    evalFormalMatrix ρ (realMatrixToFormal (L := L) (k := k) M) = M := by
  ext i j
  simp [evalFormalMatrix, realMatrixToFormal]

@[simp] theorem evalFormalMatrix_formalCollapseMatrix {L k d : Nat}
    (ρ : FormalAssignment L k) (θ : Params L k d) (l : Fin L) :
    evalFormalMatrix ρ (formalCollapseMatrix θ l) = collapseMatrix θ l := by
  simp [formalCollapseMatrix]

@[simp] theorem evalFormalMatrix_formalGatedValueSum {L k d : Nat}
    (ρ : FormalAssignment L k) (θ : Params L k d) (l : Fin L) :
    evalFormalMatrix ρ (formalGatedValueSum θ l) =
      gatedValueSum θ l (fun a ↦ ρ (l, a)) := by
  ext i j
  simp [evalFormalMatrix, formalGatedValueSum, KHead.gatedValueSum, formalGate,
    formalValueMatrix, realMatrixToFormal, Matrix.sum_apply, Matrix.smul_apply]

theorem eval_formalStepPoint_fst {L k d : Nat} (ρ : FormalAssignment L k)
    (θ : Params L k d) (l : Fin L) (w v : FormalVec L k d) :
    evalFormalVec ρ (formalStepPoint θ l w v).1 =
      (gatedEffectivePoint θ l (fun a ↦ ρ (l, a))
        (evalFormalVec ρ w) (evalFormalVec ρ v)).1 := by
  simp [formalStepPoint, gatedEffectivePoint]

theorem eval_formalStepPoint_snd {L k d : Nat} (ρ : FormalAssignment L k)
    (θ : Params L k d) (l : Fin L) (w v : FormalVec L k d) :
    evalFormalVec ρ (formalStepPoint θ l w v).2 =
      (gatedEffectivePoint θ l (fun a ↦ ρ (l, a))
        (evalFormalVec ρ w) (evalFormalVec ρ v)).2 := by
  simp [formalStepPoint, gatedEffectivePoint]

/-- Evaluating a formal bilinear form gives the corresponding real bilinear form. -/
theorem eval_formalBilin {L k d : Nat} (ρ : FormalAssignment L k)
    (A : Matrix (Fin d) (Fin d) ℝ) (w v : FormalVec L k d) :
    MvPolynomial.eval ρ (formalBilin A w v) =
      matrixBilin A (evalFormalVec ρ w) (evalFormalVec ρ v) := by
  simp [formalBilin, matrixBilin, evalFormalVec, realMatrixToFormal, Matrix.mulVec,
    dotProduct]

/-- Evaluation form of the formal slope for an arbitrary assignment. -/
theorem eval_formalSlope {L k d : Nat} (ρ : FormalAssignment L k)
    (θ : Params L k d) (w v : Vec d) (l : Fin L) (a : Fin k) :
    MvPolynomial.eval ρ (formalSlope θ w v l a) =
      matrixBilin (attentionMatrix θ l a)
        (evalFormalVec ρ (formalW θ w v l.1 (Nat.le_of_lt l.2)))
        (evalFormalVec ρ (formalV θ w v l.1 (Nat.le_of_lt l.2))) := by
  simp [formalSlope, eval_formalBilin]

/-- Prefix-indexed analytic probe recursion using the original parameter indices. -/
noncomputable def actualProbePoint (r : Nat) {L k d : Nat} (θ : Params L k d)
    (w v : Vec d) : (n : Nat) → n ≤ L → ℝ → ProbePoint d
  | 0, _hn, _τ => (w, v)
  | n + 1, hn, τ =>
      let l : Fin L := ⟨n, Nat.lt_of_succ_le hn⟩
      let prev := actualProbePoint r θ w v n (Nat.le_of_succ_le hn) τ
      gatedEffectivePoint θ l (layerGates r θ l prev.1 prev.2 τ) prev.1 prev.2

@[simp] theorem actualProbePoint_zero (r : Nat) {L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (h0 : 0 ≤ L) (τ : ℝ) :
    actualProbePoint r θ w v 0 h0 τ = (w, v) :=
  rfl

theorem actualProbePoint_succ (r : Nat) {L k d : Nat} (θ : Params L k d)
    (w v : Vec d) {n : Nat} (hn : n + 1 ≤ L) (τ : ℝ) :
    actualProbePoint r θ w v (n + 1) hn τ =
      let l : Fin L := ⟨n, Nat.lt_of_succ_le hn⟩
      let prev := actualProbePoint r θ w v n (Nat.le_of_succ_le hn) τ
      gatedEffectivePoint θ l (layerGates r θ l prev.1 prev.2 τ) prev.1 prev.2 :=
  rfl

private theorem layerGates_tail_succ {r L k d : Nat} (θ : Params (L + 1) k d)
    (l : Fin L) (w v : Vec d) (τ : ℝ) :
    layerGates r (Fin.tail θ) l w v τ = layerGates r θ l.succ w v τ := by
  rfl

private theorem gatedEffectivePoint_tail_succ {L k d : Nat} (θ : Params (L + 1) k d)
    (l : Fin L) (g : Fin k → ℝ) (w v : Vec d) :
    gatedEffectivePoint (Fin.tail θ) l g w v = gatedEffectivePoint θ l.succ g w v := by
  rfl

private theorem actualProbePoint_firstLayer_tail_aux {r L k d : Nat}
    (θ : Params (L + 1) k d) (w v : Vec d) (τ : ℝ) :
    ∀ (n : Nat) (hn : n + 1 ≤ L + 1),
      actualProbePoint r θ w v (n + 1) hn τ =
        actualProbePoint r (Fin.tail θ)
          (firstLayerEffectivePoint r θ w v τ).1
          (firstLayerEffectivePoint r θ w v τ).2 n
          (Nat.succ_le_succ_iff.mp hn) τ
  | 0, _hn => by
      rfl
  | n + 1, hn => by
      conv_lhs => rw [actualProbePoint_succ]
      conv_rhs => rw [actualProbePoint_succ]
      rw [actualProbePoint_firstLayer_tail_aux θ w v τ n (Nat.le_of_succ_le hn)]
      let lTail : Fin L := ⟨n, Nat.lt_of_succ_le (Nat.succ_le_succ_iff.mp hn)⟩
      have hl : (⟨n + 1, Nat.lt_of_succ_le hn⟩ : Fin (L + 1)) = lTail.succ := by
        ext
        rfl
      rw [hl]
      let prev : ProbePoint d :=
        actualProbePoint r (Fin.tail θ)
          (firstLayerEffectivePoint r θ w v τ).1
          (firstLayerEffectivePoint r θ w v τ).2 n
          (Nat.succ_le_succ_iff.mp (Nat.le_of_succ_le hn)) τ
      change
        gatedEffectivePoint θ lTail.succ
            (layerGates r θ lTail.succ prev.1 prev.2 τ) prev.1 prev.2 =
          gatedEffectivePoint (Fin.tail θ) lTail
            (layerGates r (Fin.tail θ) lTail prev.1 prev.2 τ) prev.1 prev.2
      rw [← layerGates_tail_succ θ lTail]
      rw [← gatedEffectivePoint_tail_succ θ lTail]

private theorem actualProbePoint_firstLayer_tail {r L k d : Nat}
    (θ : Params (L + 1) k d) (w v : Vec d) (τ : ℝ) :
    actualProbePoint r θ w v (L + 1) le_rfl τ =
      actualProbePoint r (Fin.tail θ)
        (firstLayerEffectivePoint r θ w v τ).1
        (firstLayerEffectivePoint r θ w v τ).2 L le_rfl τ := by
  simpa using actualProbePoint_firstLayer_tail_aux (r := r) θ w v τ L le_rfl

/-- The original-index analytic recursion agrees with the tail-recursive probe API. -/
theorem actualProbePoint_eq_probeRecursionPoint (r : Nat) {L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (τ : ℝ) :
    actualProbePoint r θ w v L le_rfl τ = probeRecursionPoint r θ w v τ := by
  induction L generalizing w v with
  | zero => simp
  | succ L ih =>
      rw [actualProbePoint_firstLayer_tail]
      rw [probeRecursionPoint_succ]
      exact ih (Fin.tail θ)
        (firstLayerEffectivePoint r θ w v τ).1
        (firstLayerEffectivePoint r θ w v τ).2

/-- The real bilinear slope used by the actual recursion at layer `l`. -/
noncomputable def actualProbeSlope (r : Nat) {L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (τ : ℝ) (l : Fin L) (a : Fin k) : ℝ :=
  matrixBilin (attentionMatrix θ l a)
    (actualProbePoint r θ w v l.1 (Nat.le_of_lt l.2) τ).1
    (actualProbePoint r θ w v l.1 (Nat.le_of_lt l.2) τ).2

/-- The actual analytic gate at layer/head `(l,a)`. -/
noncomputable def actualProbeGate (r : Nat) {L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (τ : ℝ) (l : Fin L) (a : Fin k) : ℝ :=
  layerGates r θ l
    (actualProbePoint r θ w v l.1 (Nat.le_of_lt l.2) τ).1
    (actualProbePoint r θ w v l.1 (Nat.le_of_lt l.2) τ).2 τ a

theorem actualProbeGate_eq_sig (r : Nat) {L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (τ : ℝ) (l : Fin L) (a : Fin k) :
    actualProbeGate r θ w v τ l a =
      sig (τ * actualProbeSlope r θ w v τ l a + logScale r) := by
  rfl

/-- Formal-gate assignment induced by the actual analytic recursion. -/
noncomputable def actualProbeGateAssignment (r : Nat) {L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (τ : ℝ) : FormalAssignment L k :=
  fun x ↦ actualProbeGate r θ w v τ x.1 x.2

/-- Evaluation at actual gates recovers both analytic streams at every prefix. -/
theorem eval_formalPoint_actualProbeGateAssignment (r : Nat) {L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (τ : ℝ) :
    ∀ (n : Nat) (hn : n ≤ L),
      evalFormalVec (actualProbeGateAssignment r θ w v τ)
          (formalPoint θ w v n hn).1 = (actualProbePoint r θ w v n hn τ).1 ∧
        evalFormalVec (actualProbeGateAssignment r θ w v τ)
          (formalPoint θ w v n hn).2 = (actualProbePoint r θ w v n hn τ).2
  | 0, _hn => by
      simp [formalPoint, actualProbePoint]
  | n + 1, hn => by
      have hprev := eval_formalPoint_actualProbeGateAssignment r θ w v τ n
        (Nat.le_of_succ_le hn)
      constructor
      · simp [formalPoint, actualProbePoint, eval_formalStepPoint_fst,
          hprev.1, hprev.2, actualProbeGateAssignment, actualProbeGate]
      · simp [formalPoint, actualProbePoint, eval_formalStepPoint_snd,
          hprev.1, hprev.2, actualProbeGateAssignment, actualProbeGate]

theorem eval_formalW_actualProbeGateAssignment (r : Nat) {L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (τ : ℝ) {n : Nat} (hn : n ≤ L) :
    evalFormalVec (actualProbeGateAssignment r θ w v τ) (formalW θ w v n hn) =
      (actualProbePoint r θ w v n hn τ).1 := by
  simpa [formalW] using
    (eval_formalPoint_actualProbeGateAssignment r θ w v τ n hn).1

theorem eval_formalV_actualProbeGateAssignment (r : Nat) {L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (τ : ℝ) {n : Nat} (hn : n ≤ L) :
    evalFormalVec (actualProbeGateAssignment r θ w v τ) (formalV θ w v n hn) =
      (actualProbePoint r θ w v n hn τ).2 := by
  simpa [formalV] using
    (eval_formalPoint_actualProbeGateAssignment r θ w v τ n hn).2

/-- Full-depth formal evaluation recovers the tail-recursive probe point. -/
theorem eval_formalPoint_actualProbeGateAssignment_full (r : Nat) {L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (τ : ℝ) :
    evalFormalVec (actualProbeGateAssignment r θ w v τ)
        (formalPoint θ w v L le_rfl).1 = (probeRecursionPoint r θ w v τ).1 ∧
      evalFormalVec (actualProbeGateAssignment r θ w v τ)
        (formalPoint θ w v L le_rfl).2 = (probeRecursionPoint r θ w v τ).2 := by
  rw [← actualProbePoint_eq_probeRecursionPoint r θ w v τ]
  exact eval_formalPoint_actualProbeGateAssignment r θ w v τ L le_rfl

theorem eval_formalW_actualProbeGateAssignment_full (r : Nat) {L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (τ : ℝ) :
    evalFormalVec (actualProbeGateAssignment r θ w v τ) (formalW θ w v L le_rfl) =
      (probeRecursionPoint r θ w v τ).1 := by
  rw [eval_formalW_actualProbeGateAssignment]
  exact congrArg Prod.fst (actualProbePoint_eq_probeRecursionPoint r θ w v τ)

theorem eval_formalV_actualProbeGateAssignment_full (r : Nat) {L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (τ : ℝ) :
    evalFormalVec (actualProbeGateAssignment r θ w v τ) (formalV θ w v L le_rfl) =
      (probeRecursionPoint r θ w v τ).2 := by
  rw [eval_formalV_actualProbeGateAssignment]
  exact congrArg Prod.snd (actualProbePoint_eq_probeRecursionPoint r θ w v τ)

theorem eval_formalV_actualProbeGateAssignment_eq_probeOutput (r : Nat) {L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (τ : ℝ) :
    evalFormalVec (actualProbeGateAssignment r θ w v τ) (formalV θ w v L le_rfl) =
      probeOutput r θ w v τ :=
  eval_formalV_actualProbeGateAssignment_full r θ w v τ

/-- Formal slopes evaluated at actual gates are the actual probe slopes. -/
theorem eval_formalSlope_actualProbeGateAssignment (r : Nat) {L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (τ : ℝ) (l : Fin L) (a : Fin k) :
    MvPolynomial.eval (actualProbeGateAssignment r θ w v τ)
        (formalSlope θ w v l a) = actualProbeSlope r θ w v τ l a := by
  rw [eval_formalSlope]
  simp [actualProbeSlope,
    eval_formalW_actualProbeGateAssignment r θ w v τ (Nat.le_of_lt l.2),
    eval_formalV_actualProbeGateAssignment r θ w v τ (Nat.le_of_lt l.2)]

/-! ## Polynomial dependency and support bounds -/

/-- Every variable occurring in `p` belongs to a layer strictly before `n`. -/
def FormalPolyDependsOnLayersBefore {L k : Nat} (n : Nat) (p : FormalPoly L k) : Prop :=
  ∀ x ∈ p.vars, x.1.1 < n

/-- Coordinatewise strict layer-prefix dependency for a formal vector. -/
def FormalVecDependsOnLayersBefore {L k d : Nat} (n : Nat) (x : FormalVec L k d) : Prop :=
  ∀ i, FormalPolyDependsOnLayersBefore n (x i)

/-- Entrywise strict layer-prefix dependency for a formal matrix. -/
def FormalMatrixDependsOnLayersBefore {L k d : Nat} (n : Nat)
    (M : Matrix (Fin d) (Fin d) (FormalPoly L k)) : Prop :=
  ∀ i j, FormalPolyDependsOnLayersBefore n (M i j)

/-- Monomial-support form of strict layer-prefix dependency. -/
def FormalPolySupportBefore {L k : Nat} (n : Nat) (p : FormalPoly L k) : Prop :=
  ∀ m ∈ p.support, ∀ x : FormalVar L k, n ≤ x.1.1 → m x = 0

theorem formalPolyDependsOnLayersBefore_mono {L k : Nat} {n N : Nat}
    {p : FormalPoly L k} (h : FormalPolyDependsOnLayersBefore n p) (hnN : n ≤ N) :
    FormalPolyDependsOnLayersBefore N p := by
  intro x hx
  exact lt_of_lt_of_le (h x hx) hnN

theorem formalPolyDependsOnLayersBefore_const {L k : Nat} (n : Nat) (c : ℝ) :
    FormalPolyDependsOnLayersBefore n (formalConst (L := L) (k := k) c) := by
  simp [FormalPolyDependsOnLayersBefore, formalConst]

theorem formalPolyDependsOnLayersBefore_gate {L k : Nat} {n : Nat}
    (l : Fin L) (a : Fin k) (hl : l.1 < n) :
    FormalPolyDependsOnLayersBefore n (formalGate l a) := by
  simpa [FormalPolyDependsOnLayersBefore, formalGate] using hl

theorem formalPolyDependsOnLayersBefore_add {L k : Nat} {n : Nat}
    {p q : FormalPoly L k} (hp : FormalPolyDependsOnLayersBefore n p)
    (hq : FormalPolyDependsOnLayersBefore n q) :
    FormalPolyDependsOnLayersBefore n (p + q) := by
  classical
  intro x hx
  have hx' := MvPolynomial.vars_add_subset p q hx
  rcases Finset.mem_union.mp hx' with hxp | hxq
  · exact hp x hxp
  · exact hq x hxq

theorem formalPolyDependsOnLayersBefore_sub {L k : Nat} {n : Nat}
    {p q : FormalPoly L k} (hp : FormalPolyDependsOnLayersBefore n p)
    (hq : FormalPolyDependsOnLayersBefore n q) :
    FormalPolyDependsOnLayersBefore n (p - q) := by
  classical
  intro x hx
  have hx' : x ∈ p.vars ∪ q.vars := by
    have hxsub : x ∈ (p + -q).vars := by
      simpa [sub_eq_add_neg] using hx
    have hsub := MvPolynomial.vars_add_subset p (-q) hxsub
    simpa using hsub
  rcases Finset.mem_union.mp hx' with hxp | hxq
  · exact hp x hxp
  · exact hq x hxq

theorem formalPolyDependsOnLayersBefore_mul {L k : Nat} {n : Nat}
    {p q : FormalPoly L k} (hp : FormalPolyDependsOnLayersBefore n p)
    (hq : FormalPolyDependsOnLayersBefore n q) :
    FormalPolyDependsOnLayersBefore n (p * q) := by
  classical
  intro x hx
  have hx' := MvPolynomial.vars_mul p q hx
  rcases Finset.mem_union.mp hx' with hxp | hxq
  · exact hp x hxp
  · exact hq x hxq

theorem formalPolyDependsOnLayersBefore_sum {L k ι : Nat} {n : Nat}
    (s : Finset (Fin ι)) (f : Fin ι → FormalPoly L k)
    (hf : ∀ i ∈ s, FormalPolyDependsOnLayersBefore n (f i)) :
    FormalPolyDependsOnLayersBefore n (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [FormalPolyDependsOnLayersBefore]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact formalPolyDependsOnLayersBefore_add (hf i (by simp))
        (ih (fun j hj ↦ hf j (by simp [hj])))

theorem formalVecDependsOnLayersBefore_mono {L k d : Nat} {n N : Nat}
    {x : FormalVec L k d} (h : FormalVecDependsOnLayersBefore n x) (hnN : n ≤ N) :
    FormalVecDependsOnLayersBefore N x :=
  fun i ↦ formalPolyDependsOnLayersBefore_mono (h i) hnN

theorem realVecToFormal_dependsOnLayersBefore {L k d : Nat} (n : Nat) (x : Vec d) :
    FormalVecDependsOnLayersBefore n (realVecToFormal (L := L) (k := k) x) :=
  fun i ↦ formalPolyDependsOnLayersBefore_const n (x i)

theorem realMatrixToFormal_dependsOnLayersBefore {L k d : Nat} (n : Nat)
    (M : Matrix (Fin d) (Fin d) ℝ) :
    FormalMatrixDependsOnLayersBefore n (realMatrixToFormal (L := L) (k := k) M) :=
  fun i j ↦ formalPolyDependsOnLayersBefore_const n (M i j)

theorem formalMatrixDependsOnLayersBefore_sub {L k d : Nat} {n : Nat}
    {M N : Matrix (Fin d) (Fin d) (FormalPoly L k)}
    (hM : FormalMatrixDependsOnLayersBefore n M)
    (hN : FormalMatrixDependsOnLayersBefore n N) :
    FormalMatrixDependsOnLayersBefore n (M - N) :=
  fun i j ↦ formalPolyDependsOnLayersBefore_sub (hM i j) (hN i j)

theorem formalVecDependsOnLayersBefore_add {L k d : Nat} {n : Nat}
    {x y : FormalVec L k d} (hx : FormalVecDependsOnLayersBefore n x)
    (hy : FormalVecDependsOnLayersBefore n y) :
    FormalVecDependsOnLayersBefore n (x + y) :=
  fun i ↦ formalPolyDependsOnLayersBefore_add (hx i) (hy i)

theorem formalMatrix_mulVec_dependsOnLayersBefore {L k d : Nat} {n : Nat}
    {M : Matrix (Fin d) (Fin d) (FormalPoly L k)} {x : FormalVec L k d}
    (hM : FormalMatrixDependsOnLayersBefore n M)
    (hx : FormalVecDependsOnLayersBefore n x) :
    FormalVecDependsOnLayersBefore n (M *ᵥ x) := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact formalPolyDependsOnLayersBefore_sum Finset.univ
    (fun j ↦ M i j * x j) (fun j _ ↦
      formalPolyDependsOnLayersBefore_mul (hM i j) (hx j))

theorem formalCollapseMatrix_dependsOnLayersBefore {L k d : Nat} (n : Nat)
    (θ : Params L k d) (l : Fin L) :
    FormalMatrixDependsOnLayersBefore n (formalCollapseMatrix θ l) :=
  realMatrixToFormal_dependsOnLayersBefore n (collapseMatrix θ l)

theorem formalGatedValueSum_dependsOnLayersBefore {L k d : Nat} {n : Nat}
    (θ : Params L k d) (l : Fin L) (hl : l.1 < n) :
    FormalMatrixDependsOnLayersBefore n (formalGatedValueSum θ l) := by
  intro i j
  simp only [formalGatedValueSum, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact formalPolyDependsOnLayersBefore_sum Finset.univ
    (fun a ↦ formalGate l a * formalValueMatrix θ l a i j) (fun a _ ↦
      formalPolyDependsOnLayersBefore_mul
        (formalPolyDependsOnLayersBefore_gate l a hl)
        (realMatrixToFormal_dependsOnLayersBefore n (valueMatrix θ l a) i j))

theorem formalStepPoint_dependsOnLayersBefore {L k d : Nat} {n : Nat}
    (θ : Params L k d) (l : Fin L) (hl : l.1 < n)
    (w v : FormalVec L k d) (hw : FormalVecDependsOnLayersBefore n w)
    (hv : FormalVecDependsOnLayersBefore n v) :
    FormalVecDependsOnLayersBefore n (formalStepPoint θ l w v).1 ∧
      FormalVecDependsOnLayersBefore n (formalStepPoint θ l w v).2 := by
  let hC := formalCollapseMatrix_dependsOnLayersBefore n θ l
  let hD := formalGatedValueSum_dependsOnLayersBefore θ l hl
  constructor
  · exact formalMatrix_mulVec_dependsOnLayersBefore
      (formalMatrixDependsOnLayersBefore_sub hC hD) hw
  · exact formalVecDependsOnLayersBefore_add
      (formalMatrix_mulVec_dependsOnLayersBefore hC hv)
      (formalMatrix_mulVec_dependsOnLayersBefore hD hw)

/-- `w_n` and `v_n` use exactly no variables from layer `n` or later. -/
theorem formalPoint_dependsOnLayersBefore {L k d : Nat} (θ : Params L k d)
    (w v : Vec d) : ∀ (n : Nat) (hn : n ≤ L),
      FormalVecDependsOnLayersBefore n (formalPoint θ w v n hn).1 ∧
        FormalVecDependsOnLayersBefore n (formalPoint θ w v n hn).2
  | 0, _hn => ⟨realVecToFormal_dependsOnLayersBefore 0 w,
      realVecToFormal_dependsOnLayersBefore 0 v⟩
  | n + 1, hn => by
      have hprev := formalPoint_dependsOnLayersBefore θ w v n (Nat.le_of_succ_le hn)
      exact formalStepPoint_dependsOnLayersBefore θ
        ⟨n, Nat.lt_of_succ_le hn⟩ (Nat.lt_succ_self n)
        (formalPoint θ w v n (Nat.le_of_succ_le hn)).1
        (formalPoint θ w v n (Nat.le_of_succ_le hn)).2
        (formalVecDependsOnLayersBefore_mono hprev.1 (Nat.le_succ n))
        (formalVecDependsOnLayersBefore_mono hprev.2 (Nat.le_succ n))

theorem formalW_dependsOnLayersBefore {L k d : Nat} (θ : Params L k d)
    (w v : Vec d) (n : Nat) (hn : n ≤ L) :
    FormalVecDependsOnLayersBefore n (formalW θ w v n hn) :=
  (formalPoint_dependsOnLayersBefore θ w v n hn).1

theorem formalV_dependsOnLayersBefore {L k d : Nat} (θ : Params L k d)
    (w v : Vec d) (n : Nat) (hn : n ≤ L) :
    FormalVecDependsOnLayersBefore n (formalV θ w v n hn) :=
  (formalPoint_dependsOnLayersBefore θ w v n hn).2

theorem formalBilin_dependsOnLayersBefore {L k d : Nat} {n : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (w v : FormalVec L k d)
    (hw : FormalVecDependsOnLayersBefore n w)
    (hv : FormalVecDependsOnLayersBefore n v) :
    FormalPolyDependsOnLayersBefore n (formalBilin A w v) := by
  simp only [formalBilin, dotProduct]
  have hAv := formalMatrix_mulVec_dependsOnLayersBefore
    (realMatrixToFormal_dependsOnLayersBefore n A) hv
  exact formalPolyDependsOnLayersBefore_sum Finset.univ
    (fun i ↦ w i * (realMatrixToFormal A *ᵥ v) i)
    (fun i _ ↦ formalPolyDependsOnLayersBefore_mul (hw i) (hAv i))

/-- `φ_{la}` only depends on gates from layers strictly before `l`. -/
theorem formalSlope_dependsOnLayersBefore {L k d : Nat} (θ : Params L k d)
    (w v : Vec d) (l : Fin L) (a : Fin k) :
    FormalPolyDependsOnLayersBefore l.1 (formalSlope θ w v l a) :=
  formalBilin_dependsOnLayersBefore (attentionMatrix θ l a)
    (formalW θ w v l.1 (Nat.le_of_lt l.2))
    (formalV θ w v l.1 (Nat.le_of_lt l.2))
    (formalW_dependsOnLayersBefore θ w v l.1 (Nat.le_of_lt l.2))
    (formalV_dependsOnLayersBefore θ w v l.1 (Nat.le_of_lt l.2))

theorem formalPolySupportBefore_of_dependsOnLayersBefore {L k : Nat} {n : Nat}
    {p : FormalPoly L k} (h : FormalPolyDependsOnLayersBefore n p) :
    FormalPolySupportBefore n p := by
  intro m hm x hnx
  apply MvPolynomial.mem_support_notMem_vars_zero hm
  intro hx
  exact (Nat.not_lt_of_ge hnx) (h x hx)

theorem formalW_supportBefore {L k d : Nat} (θ : Params L k d)
    (w v : Vec d) (n : Nat) (hn : n ≤ L) (i : Fin d) :
    FormalPolySupportBefore n (formalW θ w v n hn i) :=
  formalPolySupportBefore_of_dependsOnLayersBefore
    (formalW_dependsOnLayersBefore θ w v n hn i)

theorem formalV_supportBefore {L k d : Nat} (θ : Params L k d)
    (w v : Vec d) (n : Nat) (hn : n ≤ L) (i : Fin d) :
    FormalPolySupportBefore n (formalV θ w v n hn i) :=
  formalPolySupportBefore_of_dependsOnLayersBefore
    (formalV_dependsOnLayersBefore θ w v n hn i)

theorem formalSlope_supportBefore {L k d : Nat} (θ : Params L k d)
    (w v : Vec d) (l : Fin L) (a : Fin k) :
    FormalPolySupportBefore l.1 (formalSlope θ w v l a) :=
  formalPolySupportBefore_of_dependsOnLayersBefore
    (formalSlope_dependsOnLayersBefore θ w v l a)

/-! ## Linearity in the initial probe -/

@[simp] theorem realVecToFormal_add {L k d : Nat} (x y : Vec d) :
    realVecToFormal (L := L) (k := k) (x + y) =
      realVecToFormal x + realVecToFormal y := by
  ext i
  simp [realVecToFormal, formalConst]

@[simp] theorem realVecToFormal_smul {L k d : Nat} (c : ℝ) (x : Vec d) :
    realVecToFormal (L := L) (k := k) (c • x) =
      formalConst (L := L) (k := k) c • realVecToFormal x := by
  ext i
  simp [realVecToFormal, formalConst, smul_eq_mul]

theorem formalStepPoint_add {L k d : Nat} (θ : Params L k d) (l : Fin L)
    (w₁ v₁ w₂ v₂ : FormalVec L k d) :
    formalStepPoint θ l (w₁ + w₂) (v₁ + v₂) =
      ((formalStepPoint θ l w₁ v₁).1 + (formalStepPoint θ l w₂ v₂).1,
        (formalStepPoint θ l w₁ v₁).2 + (formalStepPoint θ l w₂ v₂).2) := by
  apply Prod.ext
  · simp [formalStepPoint, Matrix.mulVec_add]
  · simp only [formalStepPoint, Matrix.mulVec_add]
    abel

theorem formalStepPoint_smul {L k d : Nat} (θ : Params L k d) (l : Fin L)
    (c : FormalPoly L k) (w v : FormalVec L k d) :
    formalStepPoint θ l (c • w) (c • v) =
      (c • (formalStepPoint θ l w v).1,
        c • (formalStepPoint θ l w v).2) := by
  apply Prod.ext
  · simp [formalStepPoint, Matrix.mulVec_smul]
  · simp [formalStepPoint, Matrix.mulVec_smul, smul_add]

/-- Joint additivity of `(w_n,v_n)` in the initial pair `(w,v)`. -/
theorem formalPoint_add {L k d : Nat} (θ : Params L k d)
    (w₁ v₁ w₂ v₂ : Vec d) : ∀ (n : Nat) (hn : n ≤ L),
    formalPoint θ (w₁ + w₂) (v₁ + v₂) n hn =
      ((formalPoint θ w₁ v₁ n hn).1 + (formalPoint θ w₂ v₂ n hn).1,
        (formalPoint θ w₁ v₁ n hn).2 + (formalPoint θ w₂ v₂ n hn).2)
  | 0, _hn => by simp [formalPoint]
  | n + 1, hn => by
      simp only [formalPoint]
      rw [formalPoint_add θ w₁ v₁ w₂ v₂ n (Nat.le_of_succ_le hn)]
      exact formalStepPoint_add θ ⟨n, Nat.lt_of_succ_le hn⟩
        (formalPoint θ w₁ v₁ n (Nat.le_of_succ_le hn)).1
        (formalPoint θ w₁ v₁ n (Nat.le_of_succ_le hn)).2
        (formalPoint θ w₂ v₂ n (Nat.le_of_succ_le hn)).1
        (formalPoint θ w₂ v₂ n (Nat.le_of_succ_le hn)).2

/-- Joint homogeneity of `(w_n,v_n)` in the initial pair `(w,v)`. -/
theorem formalPoint_smul {L k d : Nat} (θ : Params L k d) (c : ℝ)
    (w v : Vec d) : ∀ (n : Nat) (hn : n ≤ L),
    formalPoint θ (c • w) (c • v) n hn =
      (formalConst (L := L) (k := k) c • (formalPoint θ w v n hn).1,
        formalConst (L := L) (k := k) c • (formalPoint θ w v n hn).2)
  | 0, _hn => by simp [formalPoint]
  | n + 1, hn => by
      simp only [formalPoint]
      rw [formalPoint_smul θ c w v n (Nat.le_of_succ_le hn)]
      exact formalStepPoint_smul θ ⟨n, Nat.lt_of_succ_le hn⟩
        (formalConst (L := L) (k := k) c)
        (formalPoint θ w v n (Nat.le_of_succ_le hn)).1
        (formalPoint θ w v n (Nat.le_of_succ_le hn)).2

theorem formalW_add {L k d : Nat} (θ : Params L k d)
    (w₁ v₁ w₂ v₂ : Vec d) (n : Nat) (hn : n ≤ L) :
    formalW θ (w₁ + w₂) (v₁ + v₂) n hn =
      formalW θ w₁ v₁ n hn + formalW θ w₂ v₂ n hn := by
  exact congrArg Prod.fst (formalPoint_add θ w₁ v₁ w₂ v₂ n hn)

theorem formalV_add {L k d : Nat} (θ : Params L k d)
    (w₁ v₁ w₂ v₂ : Vec d) (n : Nat) (hn : n ≤ L) :
    formalV θ (w₁ + w₂) (v₁ + v₂) n hn =
      formalV θ w₁ v₁ n hn + formalV θ w₂ v₂ n hn := by
  exact congrArg Prod.snd (formalPoint_add θ w₁ v₁ w₂ v₂ n hn)

theorem formalW_smul {L k d : Nat} (θ : Params L k d) (c : ℝ)
    (w v : Vec d) (n : Nat) (hn : n ≤ L) :
    formalW θ (c • w) (c • v) n hn =
      formalConst (L := L) (k := k) c • formalW θ w v n hn := by
  exact congrArg Prod.fst (formalPoint_smul θ c w v n hn)

theorem formalV_smul {L k d : Nat} (θ : Params L k d) (c : ℝ)
    (w v : Vec d) (n : Nat) (hn : n ≤ L) :
    formalV θ (c • w) (c • v) n hn =
      formalConst (L := L) (k := k) c • formalV θ w v n hn := by
  exact congrArg Prod.snd (formalPoint_smul θ c w v n hn)

@[simp] theorem formalW_zero_initial {L k d : Nat} (θ : Params L k d)
    (n : Nat) (hn : n ≤ L) :
    formalW θ (0 : Vec d) (0 : Vec d) n hn = 0 := by
  simpa using formalW_smul θ (0 : ℝ) (0 : Vec d) (0 : Vec d) n hn

@[simp] theorem formalV_zero_initial {L k d : Nat} (θ : Params L k d)
    (n : Nat) (hn : n ≤ L) :
    formalV θ (0 : Vec d) (0 : Vec d) n hn = 0 := by
  simpa using formalV_smul θ (0 : ℝ) (0 : Vec d) (0 : Vec d) n hn

/-! ## Type-level polynomial structure -/

theorem formalW_entry_polynomial {L k d : Nat} (θ : Params L k d) (w v : Vec d)
    (n : Nat) (hn : n ≤ L) (i : Fin d) :
    ∃ p : FormalPoly L k, formalW θ w v n hn i = p :=
  ⟨formalW θ w v n hn i, rfl⟩

theorem formalV_entry_polynomial {L k d : Nat} (θ : Params L k d) (w v : Vec d)
    (n : Nat) (hn : n ≤ L) (i : Fin d) :
    ∃ p : FormalPoly L k, formalV θ w v n hn i = p :=
  ⟨formalV θ w v n hn i, rfl⟩

theorem formalSlope_polynomial {L k d : Nat} (θ : Params L k d) (w v : Vec d)
    (l : Fin L) (a : Fin k) :
    ∃ p : FormalPoly L k, formalSlope θ w v l a = p :=
  ⟨formalSlope θ w v l a, rfl⟩

/-- Polynomiality, joint linearity, and strict prefix dependency of the formal streams. -/
theorem lem_polynomial_structure {L k d : Nat} (θ : Params L k d) (w v : Vec d) :
    (∀ (n : Nat) (hn : n ≤ L) (i : Fin d),
      ∃ p : FormalPoly L k, formalW θ w v n hn i = p) ∧
    (∀ (n : Nat) (hn : n ≤ L) (i : Fin d),
      ∃ p : FormalPoly L k, formalV θ w v n hn i = p) ∧
    (∀ (l : Fin L) (a : Fin k),
      ∃ p : FormalPoly L k, formalSlope θ w v l a = p) ∧
    (∀ (n : Nat) (hn : n ≤ L),
      FormalVecDependsOnLayersBefore n (formalW θ w v n hn) ∧
        FormalVecDependsOnLayersBefore n (formalV θ w v n hn)) := by
  exact ⟨formalW_entry_polynomial θ w v,
    formalV_entry_polynomial θ w v, formalSlope_polynomial θ w v,
    formalPoint_dependsOnLayersBefore θ w v⟩

/-! ## General frozen recursion -/

/-- A tuple of frozen gate labels, indexed by layer and head. -/
abbrev FrozenGateFamily (L k : Nat) : Type := (l : Fin L) → Fin k → ℝ

/-- View a tuple of frozen gate labels as an `MvPolynomial` assignment. -/
def frozenGateAssignment {L k : Nat} (ζ : FrozenGateFamily L k) : FormalAssignment L k :=
  fun x ↦ ζ x.1 x.2

@[simp] theorem frozenGateAssignment_apply {L k : Nat} (ζ : FrozenGateFamily L k)
    (l : Fin L) (a : Fin k) :
    frozenGateAssignment ζ (l, a) = ζ l a :=
  rfl

/-- Frozen gated value matrix `D_l = ∑_a ζ_{la}V_{la}`. -/
noncomputable def frozenD {L k d : Nat} (θ : Params L k d)
    (ζ : FrozenGateFamily L k) (l : Fin L) : Matrix (Fin d) (Fin d) ℝ :=
  gatedValueSum θ l (ζ l)

/-- Frozen contrast transmission matrix `K_l = C_l - D_l`. -/
noncomputable def frozenK {L k d : Nat} (θ : Params L k d)
    (ζ : FrozenGateFamily L k) (l : Fin L) : Matrix (Fin d) (Fin d) ℝ :=
  collapseMatrix θ l - frozenD θ ζ l

theorem frozenD_eq_sum {L k d : Nat} (θ : Params L k d)
    (ζ : FrozenGateFamily L k) (l : Fin L) :
    frozenD θ ζ l = ∑ a : Fin k, ζ l a • valueMatrix θ l a :=
  rfl

theorem frozenK_eq {L k d : Nat} (θ : Params L k d)
    (ζ : FrozenGateFamily L k) (l : Fin L) :
    frozenK θ ζ l = collapseMatrix θ l - frozenD θ ζ l :=
  rfl

/-- Contrast remainder product `R_n = K_{n-1}⋯K_0`. -/
noncomputable def frozenR {L k d : Nat} (θ : Params L k d)
    (ζ : FrozenGateFamily L k) : (n : Nat) → n ≤ L → Matrix (Fin d) (Fin d) ℝ
  | 0, _ => 1
  | n + 1, hn =>
      frozenK θ ζ ⟨n, Nat.lt_of_succ_le hn⟩ *
        frozenR θ ζ n (Nat.le_of_succ_le hn)

/-- Collapsed transmission product `P_n = C_{n-1}⋯C_0`. -/
noncomputable def frozenP {L k d : Nat} (θ : Params L k d)
    (ζ : FrozenGateFamily L k) : (n : Nat) → n ≤ L → Matrix (Fin d) (Fin d) ℝ
  | 0, _ => 1
  | n + 1, hn =>
      collapseMatrix θ ⟨n, Nat.lt_of_succ_le hn⟩ *
        frozenP θ ζ n (Nat.le_of_succ_le hn)

/-- Accumulated contrast-to-last-token transfer.

The recurrence `Q_{n+1}=C_nQ_n+D_nR_n` is the stable prefix form of the TeX
sum `∑_j C_{n-1:j+1}D_jK_{j-1:0}`.
-/
noncomputable def frozenQ {L k d : Nat} (θ : Params L k d)
    (ζ : FrozenGateFamily L k) : (n : Nat) → n ≤ L → Matrix (Fin d) (Fin d) ℝ
  | 0, _ => 0
  | n + 1, hn =>
      collapseMatrix θ ⟨n, Nat.lt_of_succ_le hn⟩ *
          frozenQ θ ζ n (Nat.le_of_succ_le hn) +
        frozenD θ ζ ⟨n, Nat.lt_of_succ_le hn⟩ *
          frozenR θ ζ n (Nat.le_of_succ_le hn)

@[simp] theorem frozenR_zero {L k d : Nat} (θ : Params L k d)
    (ζ : FrozenGateFamily L k) (h0 : 0 ≤ L) : frozenR θ ζ 0 h0 = 1 :=
  rfl

@[simp] theorem frozenP_zero {L k d : Nat} (θ : Params L k d)
    (ζ : FrozenGateFamily L k) (h0 : 0 ≤ L) : frozenP θ ζ 0 h0 = 1 :=
  rfl

@[simp] theorem frozenQ_zero {L k d : Nat} (θ : Params L k d)
    (ζ : FrozenGateFamily L k) (h0 : 0 ≤ L) : frozenQ θ ζ 0 h0 = 0 :=
  rfl

@[simp] theorem frozenR_succ {L k d : Nat} (θ : Params L k d)
    (ζ : FrozenGateFamily L k) {n : Nat} (hn : n + 1 ≤ L) :
    frozenR θ ζ (n + 1) hn =
      frozenK θ ζ ⟨n, Nat.lt_of_succ_le hn⟩ *
        frozenR θ ζ n (Nat.le_of_succ_le hn) :=
  rfl

@[simp] theorem frozenP_succ {L k d : Nat} (θ : Params L k d)
    (ζ : FrozenGateFamily L k) {n : Nat} (hn : n + 1 ≤ L) :
    frozenP θ ζ (n + 1) hn =
      collapseMatrix θ ⟨n, Nat.lt_of_succ_le hn⟩ *
        frozenP θ ζ n (Nat.le_of_succ_le hn) :=
  rfl

@[simp] theorem frozenQ_succ {L k d : Nat} (θ : Params L k d)
    (ζ : FrozenGateFamily L k) {n : Nat} (hn : n + 1 ≤ L) :
    frozenQ θ ζ (n + 1) hn =
      collapseMatrix θ ⟨n, Nat.lt_of_succ_le hn⟩ *
          frozenQ θ ζ n (Nat.le_of_succ_le hn) +
        frozenD θ ζ ⟨n, Nat.lt_of_succ_le hn⟩ *
          frozenR θ ζ n (Nat.le_of_succ_le hn) :=
  rfl

/-- Real probe recursion with every gate frozen to `ζ`. -/
noncomputable def frozenPoint {L k d : Nat} (θ : Params L k d)
    (ζ : FrozenGateFamily L k) (w v : Vec d) :
    (n : Nat) → n ≤ L → ProbePoint d
  | 0, _ => (w, v)
  | n + 1, hn =>
      let prev := frozenPoint θ ζ w v n (Nat.le_of_succ_le hn)
      gatedEffectivePoint θ ⟨n, Nat.lt_of_succ_le hn⟩
        (ζ ⟨n, Nat.lt_of_succ_le hn⟩) prev.1 prev.2

@[simp] theorem frozenPoint_zero {L k d : Nat} (θ : Params L k d)
    (ζ : FrozenGateFamily L k) (w v : Vec d) (h0 : 0 ≤ L) :
    frozenPoint θ ζ w v 0 h0 = (w, v) :=
  rfl

theorem frozenPoint_succ {L k d : Nat} (θ : Params L k d)
    (ζ : FrozenGateFamily L k) (w v : Vec d) {n : Nat} (hn : n + 1 ≤ L) :
    frozenPoint θ ζ w v (n + 1) hn =
      let prev := frozenPoint θ ζ w v n (Nat.le_of_succ_le hn)
      gatedEffectivePoint θ ⟨n, Nat.lt_of_succ_le hn⟩
        (ζ ⟨n, Nat.lt_of_succ_le hn⟩) prev.1 prev.2 :=
  rfl

/-- Closed matrix form of the general frozen recursion. -/
theorem frozenPoint_closed {L k d : Nat} (θ : Params L k d)
    (ζ : FrozenGateFamily L k) (w v : Vec d) : ∀ (n : Nat) (hn : n ≤ L),
    (frozenPoint θ ζ w v n hn).1 = frozenR θ ζ n hn *ᵥ w ∧
      (frozenPoint θ ζ w v n hn).2 =
        frozenP θ ζ n hn *ᵥ v + frozenQ θ ζ n hn *ᵥ w
  | 0, _hn => by simp
  | n + 1, hn => by
      have hprev := frozenPoint_closed θ ζ w v n (Nat.le_of_succ_le hn)
      constructor
      · rw [frozenPoint_succ, gatedEffectivePoint_fst, hprev.1]
        simp only [frozenK, frozenD, frozenR_succ, Matrix.mulVec_mulVec]
      · rw [frozenPoint_succ, gatedEffectivePoint_snd, hprev.1, hprev.2]
        simp only [frozenD, frozenP_succ, frozenQ_succ, Matrix.mulVec_add,
          Matrix.mulVec_mulVec, Matrix.add_mulVec]
        abel

/-- Evaluating the formal recursion at frozen labels gives the frozen real recursion. -/
theorem eval_formalPoint_frozenGateAssignment {L k d : Nat} (θ : Params L k d)
    (ζ : FrozenGateFamily L k) (w v : Vec d) : ∀ (n : Nat) (hn : n ≤ L),
    evalFormalVec (frozenGateAssignment ζ) (formalPoint θ w v n hn).1 =
        (frozenPoint θ ζ w v n hn).1 ∧
      evalFormalVec (frozenGateAssignment ζ) (formalPoint θ w v n hn).2 =
        (frozenPoint θ ζ w v n hn).2
  | 0, _hn => by simp [formalPoint, frozenPoint]
  | n + 1, hn => by
      have hprev := eval_formalPoint_frozenGateAssignment θ ζ w v n
        (Nat.le_of_succ_le hn)
      constructor
      · simp [formalPoint, frozenPoint, eval_formalStepPoint_fst, hprev.1, hprev.2,
          frozenGateAssignment]
      · simp [formalPoint, frozenPoint, eval_formalStepPoint_snd, hprev.1, hprev.2,
          frozenGateAssignment]

/-- General frozen formula `w_n = R_n w_0` for the formal contrast stream. -/
theorem eval_formalW_frozenGateAssignment {L k d : Nat} (θ : Params L k d)
    (ζ : FrozenGateFamily L k) (w v : Vec d) (n : Nat) (hn : n ≤ L) :
    evalFormalVec (frozenGateAssignment ζ) (formalW θ w v n hn) =
      frozenR θ ζ n hn *ᵥ w := by
  rw [← (frozenPoint_closed θ ζ w v n hn).1]
  simpa [formalW] using (eval_formalPoint_frozenGateAssignment θ ζ w v n hn).1

/-- General frozen formula `v_n = P_n v_0 + Q_n w_0` for the formal last-token stream. -/
theorem eval_formalV_frozenGateAssignment {L k d : Nat} (θ : Params L k d)
    (ζ : FrozenGateFamily L k) (w v : Vec d) (n : Nat) (hn : n ≤ L) :
    evalFormalVec (frozenGateAssignment ζ) (formalV θ w v n hn) =
      frozenP θ ζ n hn *ᵥ v + frozenQ θ ζ n hn *ᵥ w := by
  rw [← (frozenPoint_closed θ ζ w v n hn).2]
  simpa [formalV] using (eval_formalPoint_frozenGateAssignment θ ζ w v n hn).2

@[simp] theorem eval_formalW_frozenGateAssignment_zero {L k d : Nat}
    (θ : Params L k d) (ζ : FrozenGateFamily L k) (w v : Vec d) (h0 : 0 ≤ L) :
    evalFormalVec (frozenGateAssignment ζ) (formalW θ w v 0 h0) = w := by
  simp

@[simp] theorem eval_formalV_frozenGateAssignment_zero {L k d : Nat}
    (θ : Params L k d) (ζ : FrozenGateFamily L k) (w v : Vec d) (h0 : 0 ≤ L) :
    evalFormalVec (frozenGateAssignment ζ) (formalV θ w v 0 h0) = v := by
  simp

/-! ## All-zero and all-one frozen specializations -/

/-- Every frozen gate is zero. -/
def allZeroGateFamily (L k : Nat) : FrozenGateFamily L k :=
  fun _ _ ↦ 0

/-- Every frozen gate is one. -/
def allOneGateFamily (L k : Nat) : FrozenGateFamily L k :=
  fun _ _ ↦ 1

@[simp] theorem allZeroGateFamily_apply {L k : Nat} (l : Fin L) (a : Fin k) :
    allZeroGateFamily L k l a = 0 :=
  rfl

@[simp] theorem allOneGateFamily_apply {L k : Nat} (l : Fin L) (a : Fin k) :
    allOneGateFamily L k l a = 1 :=
  rfl

@[simp] theorem frozenD_allZero {L k d : Nat} (θ : Params L k d) (l : Fin L) :
    frozenD θ (allZeroGateFamily L k) l = 0 := by
  simpa only [frozenD, allZeroGateFamily] using gatedValueSum_allZero θ l

@[simp] theorem frozenK_allZero {L k d : Nat} (θ : Params L k d) (l : Fin L) :
    frozenK θ (allZeroGateFamily L k) l = collapseMatrix θ l := by
  simp [frozenK]

@[simp] theorem frozenD_allOne {L k d : Nat} (θ : Params L k d) (l : Fin L) :
    frozenD θ (allOneGateFamily L k) l = collapseMatrix θ l := by
  simpa only [frozenD, allOneGateFamily] using gatedValueSum_allOne θ l

@[simp] theorem frozenK_allOne {L k d : Nat} (θ : Params L k d) (l : Fin L) :
    frozenK θ (allOneGateFamily L k) l = 0 := by
  simp [frozenK]

/-- Under an all-zero freeze, the contrast product equals the collapsed product. -/
theorem frozenR_allZero_eq_P {L k d : Nat} (θ : Params L k d) :
    ∀ (n : Nat) (hn : n ≤ L),
      frozenR θ (allZeroGateFamily L k) n hn =
        frozenP θ (allZeroGateFamily L k) n hn
  | 0, _hn => by simp
  | n + 1, hn => by
      rw [frozenR_succ, frozenP_succ, frozenK_allZero]
      rw [frozenR_allZero_eq_P θ n (Nat.le_of_succ_le hn)]

/-- Under an all-zero freeze there is no contrast-to-last-token transfer. -/
theorem frozenQ_allZero_eq_zero {L k d : Nat} (θ : Params L k d) :
    ∀ (n : Nat) (hn : n ≤ L),
      frozenQ θ (allZeroGateFamily L k) n hn = 0
  | 0, _hn => by simp
  | n + 1, hn => by
      rw [frozenQ_succ, frozenD_allZero]
      rw [frozenQ_allZero_eq_zero θ n (Nat.le_of_succ_le hn)]
      simp

/-- General conservation identity `R_n + Q_n = P_n`. -/
theorem frozenR_add_Q_eq_P {L k d : Nat} (θ : Params L k d)
    (ζ : FrozenGateFamily L k) : ∀ (n : Nat) (hn : n ≤ L),
    frozenR θ ζ n hn + frozenQ θ ζ n hn = frozenP θ ζ n hn
  | 0, _hn => by simp
  | n + 1, hn => by
      rw [frozenR_succ, frozenQ_succ, frozenP_succ, frozenK]
      rw [← frozenR_add_Q_eq_P θ ζ n (Nat.le_of_succ_le hn)]
      noncomm_ring

/-- One all-one frozen layer annihilates `R`; hence every positive prefix has `R_n=0`. -/
theorem frozenR_allOne_eq_zero_of_pos {L k d : Nat} (θ : Params L k d)
    (n : Nat) (hn : n ≤ L) (hnpos : 0 < n) :
    frozenR θ (allOneGateFamily L k) n hn = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
  rw [frozenR_succ, frozenK_allOne]
  simp

/-- For every positive all-one prefix, all transmission is in `Q_n=P_n`. -/
theorem frozenQ_allOne_eq_P_of_pos {L k d : Nat} (θ : Params L k d)
    (n : Nat) (hn : n ≤ L) (hnpos : 0 < n) :
    frozenQ θ (allOneGateFamily L k) n hn =
      frozenP θ (allOneGateFamily L k) n hn := by
  have hsum := frozenR_add_Q_eq_P θ (allOneGateFamily L k) n hn
  rw [frozenR_allOne_eq_zero_of_pos θ n hn hnpos, zero_add] at hsum
  exact hsum

/-- All-zero gates transport the formal contrast stream by the common `C` product. -/
theorem eval_formalW_allZero {L k d : Nat} (θ : Params L k d)
    (w v : Vec d) (n : Nat) (hn : n ≤ L) :
    evalFormalVec (frozenGateAssignment (allZeroGateFamily L k))
        (formalW θ w v n hn) =
      frozenP θ (allZeroGateFamily L k) n hn *ᵥ w := by
  rw [eval_formalW_frozenGateAssignment, frozenR_allZero_eq_P]

/-- All-zero gates transport the formal last-token stream by the same `C` product. -/
theorem eval_formalV_allZero {L k d : Nat} (θ : Params L k d)
    (w v : Vec d) (n : Nat) (hn : n ≤ L) :
    evalFormalVec (frozenGateAssignment (allZeroGateFamily L k))
        (formalV θ w v n hn) =
      frozenP θ (allZeroGateFamily L k) n hn *ᵥ v := by
  rw [eval_formalV_frozenGateAssignment, frozenQ_allZero_eq_zero]
  simp

/-- The empty all-one prefix has not yet annihilated the initial contrast. -/
@[simp] theorem eval_formalW_allOne_zero {L k d : Nat} (θ : Params L k d)
    (w v : Vec d) (h0 : 0 ≤ L) :
    evalFormalVec (frozenGateAssignment (allOneGateFamily L k))
        (formalW θ w v 0 h0) = w := by
  simp

/-- The empty all-one prefix returns the initial last-token stream. -/
@[simp] theorem eval_formalV_allOne_zero {L k d : Nat} (θ : Params L k d)
    (w v : Vec d) (h0 : 0 ≤ L) :
    evalFormalVec (frozenGateAssignment (allOneGateFamily L k))
        (formalV θ w v 0 h0) = v := by
  simp

/-- After the first all-one frozen layer, the formal contrast stream is zero. -/
theorem eval_formalW_allOne_of_pos {L k d : Nat} (θ : Params L k d)
    (w v : Vec d) (n : Nat) (hn : n ≤ L) (hnpos : 0 < n) :
    evalFormalVec (frozenGateAssignment (allOneGateFamily L k))
        (formalW θ w v n hn) = 0 := by
  rw [eval_formalW_frozenGateAssignment,
    frozenR_allOne_eq_zero_of_pos θ n hn hnpos]
  simp

/-- After all-one saturation, only the repeated stream `P_n(w+v)` survives. -/
theorem eval_formalV_allOne_of_pos {L k d : Nat} (θ : Params L k d)
    (w v : Vec d) (n : Nat) (hn : n ≤ L) (hnpos : 0 < n) :
    evalFormalVec (frozenGateAssignment (allOneGateFamily L k))
        (formalV θ w v n hn) =
      frozenP θ (allOneGateFamily L k) n hn *ᵥ (w + v) := by
  rw [eval_formalV_frozenGateAssignment,
    frozenQ_allOne_eq_P_of_pos θ n hn hnpos, Matrix.mulVec_add]
  exact add_comm _ _

/-- Positive all-one prefixes depend on the initial pair only through `w+v`.

This is the coefficient-disappearance statement used after a dialed first layer.
-/
theorem eval_formalPoint_allOne_eq_of_repeated_eq {L k d : Nat} (θ : Params L k d)
    {w v w' v' : Vec d} (hrep : w + v = w' + v')
    (n : Nat) (hn : n ≤ L) (hnpos : 0 < n) :
    (evalFormalVec (frozenGateAssignment (allOneGateFamily L k))
        (formalW θ w v n hn),
      evalFormalVec (frozenGateAssignment (allOneGateFamily L k))
        (formalV θ w v n hn)) =
    (evalFormalVec (frozenGateAssignment (allOneGateFamily L k))
        (formalW θ w' v' n hn),
      evalFormalVec (frozenGateAssignment (allOneGateFamily L k))
        (formalV θ w' v' n hn)) := by
  rw [eval_formalW_allOne_of_pos θ w v n hn hnpos,
    eval_formalW_allOne_of_pos θ w' v' n hn hnpos,
    eval_formalV_allOne_of_pos θ w v n hn hnpos,
    eval_formalV_allOne_of_pos θ w' v' n hn hnpos, hrep]

/-! ## Downstream probe/formal-stream API -/

/-- Compact interface consumed by genericity and the two identification steps.

The fields only package theorem families proved above: analytic evaluation,
strict prefix support, joint linearity, general frozen closed forms, all-zero
transmission, and all-one annihilation.  No skip-only saturation object enters
this interface.
-/
structure ProbeFormalAPI {L k d : Nat} (θ : Params L k d) : Prop where
  analyticEvaluation :
    ∀ (r : Nat) (w v : Vec d) (τ : ℝ) (n : Nat) (hn : n ≤ L),
      evalFormalVec (actualProbeGateAssignment r θ w v τ)
          (formalPoint θ w v n hn).1 = (actualProbePoint r θ w v n hn τ).1 ∧
        evalFormalVec (actualProbeGateAssignment r θ w v τ)
          (formalPoint θ w v n hn).2 = (actualProbePoint r θ w v n hn τ).2
  analyticSlope :
    ∀ (r : Nat) (w v : Vec d) (τ : ℝ) (l : Fin L) (a : Fin k),
      MvPolynomial.eval (actualProbeGateAssignment r θ w v τ)
          (formalSlope θ w v l a) = actualProbeSlope r θ w v τ l a
  prefixSupport :
    ∀ (w v : Vec d) (n : Nat) (hn : n ≤ L),
      FormalVecDependsOnLayersBefore n (formalW θ w v n hn) ∧
        FormalVecDependsOnLayersBefore n (formalV θ w v n hn)
  slopeSupport :
    ∀ (w v : Vec d) (l : Fin L) (a : Fin k),
      FormalPolySupportBefore l.1 (formalSlope θ w v l a)
  additive :
    ∀ (w₁ v₁ w₂ v₂ : Vec d) (n : Nat) (hn : n ≤ L),
      formalPoint θ (w₁ + w₂) (v₁ + v₂) n hn =
        ((formalPoint θ w₁ v₁ n hn).1 + (formalPoint θ w₂ v₂ n hn).1,
          (formalPoint θ w₁ v₁ n hn).2 + (formalPoint θ w₂ v₂ n hn).2)
  homogeneous :
    ∀ (c : ℝ) (w v : Vec d) (n : Nat) (hn : n ≤ L),
      formalPoint θ (c • w) (c • v) n hn =
        (formalConst (L := L) (k := k) c • (formalPoint θ w v n hn).1,
          formalConst (L := L) (k := k) c • (formalPoint θ w v n hn).2)
  frozenClosed :
    ∀ (ζ : FrozenGateFamily L k) (w v : Vec d) (n : Nat) (hn : n ≤ L),
      evalFormalVec (frozenGateAssignment ζ) (formalW θ w v n hn) =
          frozenR θ ζ n hn *ᵥ w ∧
        evalFormalVec (frozenGateAssignment ζ) (formalV θ w v n hn) =
          frozenP θ ζ n hn *ᵥ v + frozenQ θ ζ n hn *ᵥ w
  allZeroTransmission :
    ∀ (w v : Vec d) (n : Nat) (hn : n ≤ L),
      evalFormalVec (frozenGateAssignment (allZeroGateFamily L k))
          (formalW θ w v n hn) = frozenP θ (allZeroGateFamily L k) n hn *ᵥ w ∧
        evalFormalVec (frozenGateAssignment (allZeroGateFamily L k))
          (formalV θ w v n hn) = frozenP θ (allZeroGateFamily L k) n hn *ᵥ v
  allOneAnnihilation :
    ∀ (w v : Vec d) (n : Nat) (hn : n ≤ L) (_hnpos : 0 < n),
      evalFormalVec (frozenGateAssignment (allOneGateFamily L k))
          (formalW θ w v n hn) = 0 ∧
        evalFormalVec (frozenGateAssignment (allOneGateFamily L k))
          (formalV θ w v n hn) =
            frozenP θ (allOneGateFamily L k) n hn *ᵥ (w + v)
  allOneSplitInvisible :
    ∀ {w v w' v' : Vec d}, w + v = w' + v' →
      ∀ (n : Nat) (hn : n ≤ L), 0 < n →
        (evalFormalVec (frozenGateAssignment (allOneGateFamily L k))
            (formalW θ w v n hn),
          evalFormalVec (frozenGateAssignment (allOneGateFamily L k))
            (formalV θ w v n hn)) =
        (evalFormalVec (frozenGateAssignment (allOneGateFamily L k))
            (formalW θ w' v' n hn),
          evalFormalVec (frozenGateAssignment (allOneGateFamily L k))
            (formalV θ w' v' n hn))

/-- The proved no-skip probe and formal-stream theory supplies the compact API. -/
theorem probeFormalAPI {L k d : Nat} (θ : Params L k d) : ProbeFormalAPI θ where
  analyticEvaluation := fun r w v τ n hn ↦
    eval_formalPoint_actualProbeGateAssignment r θ w v τ n hn
  analyticSlope := fun r w v τ l a ↦
    eval_formalSlope_actualProbeGateAssignment r θ w v τ l a
  prefixSupport := formalPoint_dependsOnLayersBefore θ
  slopeSupport := formalSlope_supportBefore θ
  additive := formalPoint_add θ
  homogeneous := formalPoint_smul θ
  frozenClosed := fun ζ w v n hn ↦
    ⟨eval_formalW_frozenGateAssignment θ ζ w v n hn,
      eval_formalV_frozenGateAssignment θ ζ w v n hn⟩
  allZeroTransmission := fun w v n hn ↦
    ⟨eval_formalW_allZero θ w v n hn, eval_formalV_allZero θ w v n hn⟩
  allOneAnnihilation := fun w v n hn hnpos ↦
    ⟨eval_formalW_allOne_of_pos θ w v n hn hnpos,
      eval_formalV_allOne_of_pos θ w v n hn hnpos⟩
  allOneSplitInvisible := fun hrep n hn hnpos ↦
    eval_formalPoint_allOne_eq_of_repeated_eq θ hrep n hn hnpos

end TransformerIdentifiability.NLayer.NoSkip
