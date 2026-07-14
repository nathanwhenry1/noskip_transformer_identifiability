import AnyLayerIdentifiabilityProof.NLayer.KHead.Probe

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.KHead

/-!
# Formal streams and slope polynomials

This file ports the formal-stream part of
`tex_modular/sections/02-probe-recursion.tex`.  The stream coordinates live in
an actual multivariate polynomial ring, so polynomiality is represented by
type rather than by a separate predicate.
-/

/-- Formal gate variable index `(layer, head)`. -/
abbrev FormalVar (L k : Nat) : Type := Fin L × Fin k

/-- Polynomial ring for all formal gate variables in a depth-`L`, `k`-head model. -/
abbrev FormalPoly (L k : Nat) : Type := MvPolynomial (FormalVar L k) ℝ

/-- Polynomial-valued vectors. -/
abbrev FormalVec (L k d : Nat) : Type := Fin d → FormalPoly L k

/-- Cast a real scalar into the formal polynomial ring. -/
noncomputable abbrev formalConst {L k : Nat} (x : ℝ) : FormalPoly L k :=
  MvPolynomial.C x

/-- Cast a real vector into formal constants. -/
noncomputable def realVecToFormal {L k d : Nat} (x : Vec d) : FormalVec L k d :=
  fun i => formalConst (L := L) (k := k) (x i)

/-- Cast a real matrix into formal constants. -/
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

/-- The formal variable `z_{la}`. -/
noncomputable def formalGate {L k : Nat} (l : Fin L) (a : Fin k) : FormalPoly L k :=
  MvPolynomial.X (l, a)

/-- Value matrix with formal coefficients. -/
noncomputable def formalValueMatrix {L k d : Nat} (θ : Params L k d)
    (l : Fin L) (a : Fin k) : Matrix (Fin d) (Fin d) (FormalPoly L k) :=
  realMatrixToFormal (valueMatrix θ l a)

/-- Collapsed matrix with formal coefficients. -/
noncomputable def formalCollapseMatrix {L k d : Nat} (θ : Params L k d)
    (l : Fin L) : Matrix (Fin d) (Fin d) (FormalPoly L k) :=
  realMatrixToFormal (collapseMatrix θ l)

/-- Formal weighted sum `∑_a z_{la} V_{la}`. -/
noncomputable def formalGatedValueSum {L k d : Nat} (θ : Params L k d)
    (l : Fin L) : Matrix (Fin d) (Fin d) (FormalPoly L k) :=
  ∑ a : Fin k, formalGate l a • formalValueMatrix θ l a

/-- One formal recursion step. -/
noncomputable def formalStepPoint {L k d : Nat} (θ : Params L k d)
    (l : Fin L) (w v : FormalVec L k d) : FormalVec L k d × FormalVec L k d :=
  let D := formalGatedValueSum θ l
  ((formalCollapseMatrix θ l - D) *ᵥ w, formalCollapseMatrix θ l *ᵥ v + D *ᵥ w)

/-- Formal streams `(w_n(z), v_n(z))` up to any `n ≤ L`. -/
noncomputable def formalPoint {L k d : Nat} (θ : Params L k d) (w v : Vec d) :
    (n : Nat) → n ≤ L → FormalVec L k d × FormalVec L k d
  | 0, _ => (realVecToFormal w, realVecToFormal v)
  | n + 1, hn =>
      let l : Fin L := ⟨n, Nat.lt_of_succ_le hn⟩
      let prev := formalPoint θ w v n (Nat.le_of_succ_le hn)
      formalStepPoint θ l prev.1 prev.2

/-- Formal `w_n(z)`. -/
noncomputable def formalW {L k d : Nat} (θ : Params L k d) (w v : Vec d)
    (n : Nat) (hn : n ≤ L) : FormalVec L k d :=
  (formalPoint θ w v n hn).1

/-- Formal `v_n(z)`. -/
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

/-- Formal slope `φ_{la} = w_l(z)^T A_{la} v_l(z)` in zero-based layer indexing. -/
noncomputable def formalSlope {L k d : Nat} (θ : Params L k d) (w v : Vec d)
    (l : Fin L) (a : Fin k) : FormalPoly L k :=
  formalBilin (attentionMatrix θ l a)
    (formalW θ w v l.1 (Nat.le_of_lt l.2))
    (formalV θ w v l.1 (Nat.le_of_lt l.2))

/-- Evaluate a formal vector at a real gate assignment. -/
noncomputable def evalFormalVec {L k d : Nat} (ρ : FormalVar L k → ℝ)
    (x : FormalVec L k d) : Vec d :=
  fun i => MvPolynomial.eval ρ (x i)

/-- Evaluate a formal matrix at a real gate assignment. -/
noncomputable def evalFormalMatrix {L k d : Nat} (ρ : FormalVar L k → ℝ)
    (M : Matrix (Fin d) (Fin d) (FormalPoly L k)) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => MvPolynomial.eval ρ (M i j)

@[simp] theorem evalFormalVec_realVecToFormal {L k d : Nat}
    (ρ : FormalVar L k → ℝ) (x : Vec d) :
    evalFormalVec ρ (realVecToFormal (L := L) (k := k) x) = x := by
  ext i
  simp [evalFormalVec, realVecToFormal, formalConst]

@[simp] theorem evalFormalVec_add {L k d : Nat} (ρ : FormalVar L k → ℝ)
    (x y : FormalVec L k d) :
    evalFormalVec ρ (x + y) = evalFormalVec ρ x + evalFormalVec ρ y := by
  ext i
  simp [evalFormalVec]

@[simp] theorem evalFormalVec_sub {L k d : Nat} (ρ : FormalVar L k → ℝ)
    (x y : FormalVec L k d) :
    evalFormalVec ρ (x - y) = evalFormalVec ρ x - evalFormalVec ρ y := by
  ext i
  simp [evalFormalVec]

@[simp] theorem evalFormalVec_smul {L k d : Nat} (ρ : FormalVar L k → ℝ)
    (c : FormalPoly L k) (x : FormalVec L k d) :
    evalFormalVec ρ (c • x) = MvPolynomial.eval ρ c • evalFormalVec ρ x := by
  ext i
  simp [evalFormalVec]

@[simp] theorem evalFormalMatrix_sub {L k d : Nat} (ρ : FormalVar L k → ℝ)
    (M N : Matrix (Fin d) (Fin d) (FormalPoly L k)) :
    evalFormalMatrix ρ (M - N) = evalFormalMatrix ρ M - evalFormalMatrix ρ N := by
  ext i j
  simp [evalFormalMatrix]

@[simp] theorem evalFormalMatrix_add {L k d : Nat} (ρ : FormalVar L k → ℝ)
    (M N : Matrix (Fin d) (Fin d) (FormalPoly L k)) :
    evalFormalMatrix ρ (M + N) = evalFormalMatrix ρ M + evalFormalMatrix ρ N := by
  ext i j
  simp [evalFormalMatrix]

@[simp] theorem evalFormalVec_mulVec {L k d : Nat} (ρ : FormalVar L k → ℝ)
    (M : Matrix (Fin d) (Fin d) (FormalPoly L k)) (x : FormalVec L k d) :
    evalFormalVec ρ (M *ᵥ x) = evalFormalMatrix ρ M *ᵥ evalFormalVec ρ x := by
  ext i
  simp [evalFormalVec, evalFormalMatrix, Matrix.mulVec, dotProduct]

@[simp] theorem evalFormalMatrix_realMatrixToFormal {L k d : Nat}
    (ρ : FormalVar L k → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    evalFormalMatrix ρ (realMatrixToFormal (L := L) (k := k) M) = M := by
  ext i j
  simp [evalFormalMatrix, realMatrixToFormal]

@[simp] theorem evalFormalMatrix_formalCollapseMatrix {L k d : Nat}
    (ρ : FormalVar L k → ℝ) (θ : Params L k d) (l : Fin L) :
    evalFormalMatrix ρ (formalCollapseMatrix θ l) = collapseMatrix θ l := by
  simp [formalCollapseMatrix]

@[simp] theorem evalFormalMatrix_formalGatedValueSum {L k d : Nat}
    (ρ : FormalVar L k → ℝ) (θ : Params L k d) (l : Fin L) :
    evalFormalMatrix ρ (formalGatedValueSum θ l) =
      gatedValueSum θ l (fun a => ρ (l, a)) := by
  ext i j
  simp [evalFormalMatrix, formalGatedValueSum, gatedValueSum, formalGate, formalValueMatrix,
    realMatrixToFormal, Matrix.sum_apply, Matrix.smul_apply]

theorem eval_formalStepPoint_fst {L k d : Nat} (ρ : FormalVar L k → ℝ)
    (θ : Params L k d) (l : Fin L) (w v : FormalVec L k d) :
    evalFormalVec ρ (formalStepPoint θ l w v).1 =
      (gatedEffectivePoint θ l (fun a => ρ (l, a)) (evalFormalVec ρ w)
        (evalFormalVec ρ v)).1 := by
  simp [formalStepPoint, gatedEffectivePoint]

theorem eval_formalStepPoint_snd {L k d : Nat} (ρ : FormalVar L k → ℝ)
    (θ : Params L k d) (l : Fin L) (w v : FormalVec L k d) :
    evalFormalVec ρ (formalStepPoint θ l w v).2 =
      (gatedEffectivePoint θ l (fun a => ρ (l, a)) (evalFormalVec ρ w)
        (evalFormalVec ρ v)).2 := by
  simp [formalStepPoint, gatedEffectivePoint]

/-- Evaluating a formal bilinear form gives the corresponding real bilinear form. -/
theorem eval_formalBilin {L k d : Nat} (ρ : FormalVar L k → ℝ)
    (A : Matrix (Fin d) (Fin d) ℝ) (w v : FormalVec L k d) :
    MvPolynomial.eval ρ (formalBilin A w v) =
      matrixBilin A (evalFormalVec ρ w) (evalFormalVec ρ v) := by
  simp [formalBilin, matrixBilin, evalFormalVec, realMatrixToFormal, Matrix.mulVec,
    dotProduct]

/-- Evaluation form of the slope identity for any gate assignment. -/
theorem eval_formalSlope {L k d : Nat} (ρ : FormalVar L k → ℝ)
    (θ : Params L k d) (w v : Vec d) (l : Fin L) (a : Fin k) :
    MvPolynomial.eval ρ (formalSlope θ w v l a) =
      matrixBilin (attentionMatrix θ l a)
        (evalFormalVec ρ (formalW θ w v l.1 (Nat.le_of_lt l.2)))
        (evalFormalVec ρ (formalV θ w v l.1 (Nat.le_of_lt l.2))) := by
  simp [formalSlope, eval_formalBilin]

/-- Entrywise polynomiality of the formal `w` stream. -/
theorem formalW_entry_polynomial {L k d : Nat} (θ : Params L k d) (w v : Vec d)
    (n : Nat) (hn : n ≤ L) (i : Fin d) :
    ∃ p : FormalPoly L k, formalW θ w v n hn i = p :=
  ⟨formalW θ w v n hn i, rfl⟩

/-- Entrywise polynomiality of the formal `v` stream. -/
theorem formalV_entry_polynomial {L k d : Nat} (θ : Params L k d) (w v : Vec d)
    (n : Nat) (hn : n ≤ L) (i : Fin d) :
    ∃ p : FormalPoly L k, formalV θ w v n hn i = p :=
  ⟨formalV θ w v n hn i, rfl⟩

/-- Polynomiality of every formal slope. -/
theorem formalSlope_polynomial {L k d : Nat} (θ : Params L k d) (w v : Vec d)
    (l : Fin L) (a : Fin k) :
    ∃ p : FormalPoly L k, formalSlope θ w v l a = p :=
  ⟨formalSlope θ w v l a, rfl⟩

/-- `K02.E.lem-polynomial-structure.S/P`: type-level polynomial structure. -/
theorem lem_polynomial_structure {L k d : Nat} (θ : Params L k d) (w v : Vec d) :
    (∀ (n : Nat) (hn : n ≤ L) (i : Fin d),
      ∃ p : FormalPoly L k, formalW θ w v n hn i = p) ∧
    (∀ (n : Nat) (hn : n ≤ L) (i : Fin d),
      ∃ p : FormalPoly L k, formalV θ w v n hn i = p) ∧
    (∀ (l : Fin L) (a : Fin k),
      ∃ p : FormalPoly L k, formalSlope θ w v l a = p) := by
  exact ⟨formalW_entry_polynomial θ w v,
    formalV_entry_polynomial θ w v, formalSlope_polynomial θ w v⟩

/-- Sum of first-layer value matrices except one head. -/
noncomputable def firstLayerOtherValueSum {L k d : Nat} (θ : Params (L + 1) k d)
    (h : Fin k) : Matrix (Fin d) (Fin d) ℝ :=
  ∑ a ∈ (Finset.univ.erase h), valueMatrix θ 0 a

/-- TeX matrix `B = I + V_{1h}` for a single unsaturated first-layer head. -/
noncomputable def firstLayerUnsatB {L k d : Nat} (θ : Params (L + 1) k d)
    (h : Fin k) : Matrix (Fin d) (Fin d) ℝ :=
  1 + valueMatrix θ 0 h

/-- TeX matrix `S = ∑_{a ≠ h} V_{1a}` for a single unsaturated first-layer head. -/
noncomputable def firstLayerUnsatS {L k d : Nat} (θ : Params (L + 1) k d)
    (h : Fin k) : Matrix (Fin d) (Fin d) ℝ :=
  firstLayerOtherValueSum θ h

/-- First-layer `w_1(z) = (B - zV)w` with all other first-layer heads saturated at `1`. -/
noncomputable def firstLayerUnsatW {L k d : Nat} (θ : Params (L + 1) k d)
    (h : Fin k) (z : ℝ) (w : Vec d) : Vec d :=
  (firstLayerUnsatB θ h - z • valueMatrix θ 0 h) *ᵥ w

/-- First-layer `v_1(z) = C_1v + (S + zV)w` with one unsaturated first-layer head. -/
noncomputable def firstLayerUnsatV {L k d : Nat} (θ : Params (L + 1) k d)
    (h : Fin k) (z : ℝ) (w v : Vec d) : Vec d :=
  collapseMatrix θ 0 *ᵥ v +
    (firstLayerUnsatS θ h + z • valueMatrix θ 0 h) *ᵥ w

theorem firstLayerUnsatW_eq {L k d : Nat} (θ : Params (L + 1) k d)
    (h : Fin k) (z : ℝ) (w : Vec d) :
    firstLayerUnsatW θ h z w =
      (firstLayerUnsatB θ h - z • valueMatrix θ 0 h) *ᵥ w :=
  rfl

theorem firstLayerUnsatV_eq {L k d : Nat} (θ : Params (L + 1) k d)
    (h : Fin k) (z : ℝ) (w v : Vec d) :
    firstLayerUnsatV θ h z w v =
      collapseMatrix θ 0 *ᵥ v +
        (firstLayerUnsatS θ h + z • valueMatrix θ 0 h) *ᵥ w :=
  rfl

/-- Saturated weighted value sum for a fixed layer. -/
noncomputable def saturatedD {L k d : Nat} (θ : Params L k d)
    (ζ : (l : Fin L) → Fin k → ℝ) (l : Fin L) : Matrix (Fin d) (Fin d) ℝ :=
  ∑ a : Fin k, ζ l a • valueMatrix θ l a

/-- Saturated `K_l = C_l - D_l`. -/
noncomputable def saturatedK {L k d : Nat} (θ : Params L k d)
    (ζ : (l : Fin L) → Fin k → ℝ) (l : Fin L) : Matrix (Fin d) (Fin d) ℝ :=
  collapseMatrix θ l - saturatedD θ ζ l

/-- One saturated real recursion step. -/
noncomputable def saturatedStepPoint {L k d : Nat} (θ : Params L k d)
    (ζ : (l : Fin L) → Fin k → ℝ) (l : Fin L) (w v : Vec d) : ProbePoint d :=
  gatedEffectivePoint θ l (ζ l) w v

@[simp] theorem saturatedStepPoint_fst {L k d : Nat} (θ : Params L k d)
    (ζ : (l : Fin L) → Fin k → ℝ) (l : Fin L) (w v : Vec d) :
    (saturatedStepPoint θ ζ l w v).1 = saturatedK θ ζ l *ᵥ w := by
  simp [saturatedStepPoint, saturatedK, saturatedD, gatedValueSum]

@[simp] theorem saturatedStepPoint_snd {L k d : Nat} (θ : Params L k d)
    (ζ : (l : Fin L) → Fin k → ℝ) (l : Fin L) (w v : Vec d) :
    (saturatedStepPoint θ ζ l w v).2 =
      collapseMatrix θ l *ᵥ v + saturatedD θ ζ l *ᵥ w := by
  simp [saturatedStepPoint, saturatedD, gatedValueSum]

end TransformerIdentifiability.NLayer.KHead
