import AnyLayerIdentifiabilityProof.NLayer.KHead.FormalStreams
import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.PlaneTopology
import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.SigmoidMixtures

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.KHead

/-!
# Active-head stratification scaffold

This file contains the unblocked algebraic part of
`tex_modular/sections/04d-stratification.tex`: active-head bookkeeping and the
formal-evaluation form of the inactive-variable lemma.  The analytic construction of the
reduced singular strata is exposed as a proposition-valued interface, but no existence
theorem is asserted here; that proof depends on the sigmoid-mixture packet.
-/

/-- A head is active exactly when its value matrix is nonzero. -/
def IsActiveHead {L k d : Nat} (θ : Params L k d) (l : Fin L) (a : Fin k) : Prop :=
  valueMatrix θ l a ≠ 0

/-- The finite active index set `A_l(θ) = {a : V_{la} ≠ 0}`. -/
noncomputable def activeHeads {L k d : Nat} (θ : Params L k d) (l : Fin L) :
    Finset (Fin k) := by
  classical
  exact Finset.univ.filter fun a => IsActiveHead θ l a

@[simp] theorem mem_activeHeads {L k d : Nat} (θ : Params L k d) (l : Fin L) (a : Fin k) :
    a ∈ activeHeads θ l ↔ IsActiveHead θ l a := by
  classical
  simp [activeHeads]

@[simp] theorem mem_activeHeads_iff_valueMatrix_ne_zero {L k d : Nat}
    (θ : Params L k d) (l : Fin L) (a : Fin k) :
    a ∈ activeHeads θ l ↔ valueMatrix θ l a ≠ 0 := by
  simp [IsActiveHead]

@[simp] theorem not_mem_activeHeads_iff_valueMatrix_eq_zero {L k d : Nat}
    (θ : Params L k d) (l : Fin L) (a : Fin k) :
    a ∉ activeHeads θ l ↔ valueMatrix θ l a = 0 := by
  classical
  rw [mem_activeHeads_iff_valueMatrix_ne_zero]
  exact not_not

/-- Active formal variables are exactly the variables attached to active heads. -/
def IsActiveVar {L k d : Nat} (θ : Params L k d) (x : FormalVar L k) : Prop :=
  IsActiveHead θ x.1 x.2

@[simp] theorem isActiveVar_iff {L k d : Nat} (θ : Params L k d)
    (l : Fin L) (a : Fin k) :
    IsActiveVar θ (l, a) ↔ a ∈ activeHeads θ l := by
  simp [IsActiveVar]

section GateAssignments

variable {L k d : Nat} (θ : Params L k d)

/-- Change one formal gate assignment at one variable. -/
def updateFormalVar (ρ : FormalVar L k → ℝ) (x : FormalVar L k) (t : ℝ) :
    FormalVar L k → ℝ :=
  fun y => if y = x then t else ρ y

@[simp] theorem updateFormalVar_same (ρ : FormalVar L k → ℝ) (x : FormalVar L k)
    (t : ℝ) :
    updateFormalVar ρ x t x = t := by
  simp [updateFormalVar]

theorem updateFormalVar_of_ne (ρ : FormalVar L k → ℝ) {x y : FormalVar L k}
    (hxy : y ≠ x) (t : ℝ) :
    updateFormalVar ρ x t y = ρ y := by
  simp [updateFormalVar, hxy]

/-- The assignment obtained by zeroing all inactive gate variables. -/
noncomputable def activeGateAssignment (ρ : FormalVar L k → ℝ) :
    FormalVar L k → ℝ := by
  classical
  exact fun x => if IsActiveVar θ x then ρ x else 0

theorem activeGateAssignment_eq_of_active (ρ : FormalVar L k → ℝ)
    {l : Fin L} {a : Fin k} (ha : a ∈ activeHeads θ l) :
    activeGateAssignment θ ρ (l, a) = ρ (l, a) := by
  simp [activeGateAssignment, IsActiveVar, (mem_activeHeads θ l a).1 ha]

theorem activeGateAssignment_eq_zero_of_inactive (ρ : FormalVar L k → ℝ)
    {l : Fin L} {a : Fin k} (ha : a ∉ activeHeads θ l) :
    activeGateAssignment θ ρ (l, a) = 0 := by
  have hnot : ¬ IsActiveVar θ (l, a) := by
    simpa using ha
  simp [activeGateAssignment, hnot]

end GateAssignments

section InactiveVariables

variable {L k d : Nat} {θ : Params L k d}

/-- Weighted value sums depend only on active head gates. -/
theorem gatedValueSum_eq_of_eq_on_active {l : Fin L} {g g' : Fin k → ℝ}
    (h : ∀ a : Fin k, a ∈ activeHeads θ l → g a = g' a) :
    gatedValueSum θ l g = gatedValueSum θ l g' := by
  classical
  simp only [gatedValueSum]
  refine Finset.sum_congr rfl ?_
  intro a _ha
  by_cases hactive : a ∈ activeHeads θ l
  · simp [h a hactive]
  · have hV : valueMatrix θ l a = 0 :=
      (not_mem_activeHeads_iff_valueMatrix_eq_zero θ l a).1 hactive
    simp [hV]

/-- One gated recursion step depends only on active head gates. -/
theorem gatedEffectivePoint_eq_of_eq_on_active {l : Fin L} {g g' : Fin k → ℝ}
    {w v : Vec d} (h : ∀ a : Fin k, a ∈ activeHeads θ l → g a = g' a) :
    gatedEffectivePoint θ l g w v = gatedEffectivePoint θ l g' w v := by
  have hD := gatedValueSum_eq_of_eq_on_active (θ := θ) (l := l) h
  simp [gatedEffectivePoint, hD]

/-- Evaluation of one formal step depends only on active head gates, assuming the input
formal streams have the same evaluated values. -/
theorem eval_formalStepPoint_eq_of_eq_on_active (ρ ρ' : FormalVar L k → ℝ)
    {l : Fin L} {w v : FormalVec L k d}
    (hρ : ∀ a : Fin k, a ∈ activeHeads θ l → ρ (l, a) = ρ' (l, a))
    (hw : evalFormalVec ρ w = evalFormalVec ρ' w)
    (hv : evalFormalVec ρ v = evalFormalVec ρ' v) :
    evalFormalVec ρ (formalStepPoint θ l w v).1 =
        evalFormalVec ρ' (formalStepPoint θ l w v).1 ∧
      evalFormalVec ρ (formalStepPoint θ l w v).2 =
        evalFormalVec ρ' (formalStepPoint θ l w v).2 := by
  constructor
  · rw [eval_formalStepPoint_fst, eval_formalStepPoint_fst, hw, hv]
    exact congrArg Prod.fst
      (gatedEffectivePoint_eq_of_eq_on_active (θ := θ) (l := l) (w := evalFormalVec ρ' w)
        (v := evalFormalVec ρ' v) hρ)
  · rw [eval_formalStepPoint_snd, eval_formalStepPoint_snd, hw, hv]
    exact congrArg Prod.snd
      (gatedEffectivePoint_eq_of_eq_on_active (θ := θ) (l := l) (w := evalFormalVec ρ' w)
        (v := evalFormalVec ρ' v) hρ)

/-- Formal streams through `n` layers depend only on active gate variables in earlier
layers.  This is the evaluation-invariance form of `lem:inactive-variables`. -/
theorem eval_formalPoint_eq_of_eq_on_active (ρ ρ' : FormalVar L k → ℝ)
    (w v : Vec d) :
    ∀ (n : Nat) (hn : n ≤ L),
      (∀ (l : Fin L) (a : Fin k), l.1 < n → a ∈ activeHeads θ l →
        ρ (l, a) = ρ' (l, a)) →
        evalFormalVec ρ (formalPoint θ w v n hn).1 =
            evalFormalVec ρ' (formalPoint θ w v n hn).1 ∧
          evalFormalVec ρ (formalPoint θ w v n hn).2 =
            evalFormalVec ρ' (formalPoint θ w v n hn).2
  | 0, _hn, _hρ => by
      simp [formalPoint]
  | n + 1, hn, hρ => by
      let l : Fin L := ⟨n, Nat.lt_of_succ_le hn⟩
      have hprev :
          evalFormalVec ρ (formalPoint θ w v n (Nat.le_of_succ_le hn)).1 =
              evalFormalVec ρ' (formalPoint θ w v n (Nat.le_of_succ_le hn)).1 ∧
            evalFormalVec ρ (formalPoint θ w v n (Nat.le_of_succ_le hn)).2 =
              evalFormalVec ρ' (formalPoint θ w v n (Nat.le_of_succ_le hn)).2 :=
        eval_formalPoint_eq_of_eq_on_active ρ ρ' w v n (Nat.le_of_succ_le hn)
          (fun l' a hl' ha => hρ l' a (Nat.lt_trans hl' (Nat.lt_succ_self n)) ha)
      have hstep :
          evalFormalVec ρ
              (formalStepPoint θ l
                (formalPoint θ w v n (Nat.le_of_succ_le hn)).1
                (formalPoint θ w v n (Nat.le_of_succ_le hn)).2).1 =
              evalFormalVec ρ'
                (formalStepPoint θ l
                  (formalPoint θ w v n (Nat.le_of_succ_le hn)).1
                  (formalPoint θ w v n (Nat.le_of_succ_le hn)).2).1 ∧
            evalFormalVec ρ
              (formalStepPoint θ l
                (formalPoint θ w v n (Nat.le_of_succ_le hn)).1
                (formalPoint θ w v n (Nat.le_of_succ_le hn)).2).2 =
              evalFormalVec ρ'
                (formalStepPoint θ l
                  (formalPoint θ w v n (Nat.le_of_succ_le hn)).1
                  (formalPoint θ w v n (Nat.le_of_succ_le hn)).2).2 :=
        eval_formalStepPoint_eq_of_eq_on_active (θ := θ) ρ ρ'
          (l := l)
          (w := (formalPoint θ w v n (Nat.le_of_succ_le hn)).1)
          (v := (formalPoint θ w v n (Nat.le_of_succ_le hn)).2)
          (fun a ha => hρ l a (by simp [l]) ha) hprev.1 hprev.2
      simpa [formalPoint, l] using hstep

theorem eval_formalW_eq_of_eq_on_active (ρ ρ' : FormalVar L k → ℝ)
    (w v : Vec d) {n : Nat} (hn : n ≤ L)
    (hρ : ∀ (l : Fin L) (a : Fin k), l.1 < n → a ∈ activeHeads θ l →
      ρ (l, a) = ρ' (l, a)) :
    evalFormalVec ρ (formalW θ w v n hn) =
      evalFormalVec ρ' (formalW θ w v n hn) :=
  (eval_formalPoint_eq_of_eq_on_active (θ := θ) ρ ρ' w v n hn hρ).1

theorem eval_formalV_eq_of_eq_on_active (ρ ρ' : FormalVar L k → ℝ)
    (w v : Vec d) {n : Nat} (hn : n ≤ L)
    (hρ : ∀ (l : Fin L) (a : Fin k), l.1 < n → a ∈ activeHeads θ l →
      ρ (l, a) = ρ' (l, a)) :
    evalFormalVec ρ (formalV θ w v n hn) =
      evalFormalVec ρ' (formalV θ w v n hn) :=
  (eval_formalPoint_eq_of_eq_on_active (θ := θ) ρ ρ' w v n hn hρ).2

/-- Formal slopes depend only on active gate variables in previous layers. -/
theorem eval_formalSlope_eq_of_eq_on_active (ρ ρ' : FormalVar L k → ℝ)
    (w v : Vec d) (l : Fin L) (a : Fin k)
    (hρ : ∀ (l' : Fin L) (a' : Fin k), l'.1 < l.1 → a' ∈ activeHeads θ l' →
      ρ (l', a') = ρ' (l', a')) :
    MvPolynomial.eval ρ (formalSlope θ w v l a) =
      MvPolynomial.eval ρ' (formalSlope θ w v l a) := by
  rw [eval_formalSlope, eval_formalSlope]
  rw [eval_formalW_eq_of_eq_on_active (θ := θ) ρ ρ' w v (Nat.le_of_lt l.2) hρ,
    eval_formalV_eq_of_eq_on_active (θ := θ) ρ ρ' w v (Nat.le_of_lt l.2) hρ]

/-- Zeroing all inactive variables does not change the evaluated formal streams. -/
theorem eval_formalPoint_activeGateAssignment (ρ : FormalVar L k → ℝ)
    (w v : Vec d) (n : Nat) (hn : n ≤ L) :
    evalFormalVec (activeGateAssignment θ ρ) (formalPoint θ w v n hn).1 =
        evalFormalVec ρ (formalPoint θ w v n hn).1 ∧
      evalFormalVec (activeGateAssignment θ ρ) (formalPoint θ w v n hn).2 =
        evalFormalVec ρ (formalPoint θ w v n hn).2 := by
  refine eval_formalPoint_eq_of_eq_on_active (θ := θ)
    (activeGateAssignment θ ρ) ρ w v n hn ?_
  intro l a _hl ha
  exact activeGateAssignment_eq_of_active θ ρ ha

theorem eval_formalW_activeGateAssignment (ρ : FormalVar L k → ℝ)
    (w v : Vec d) {n : Nat} (hn : n ≤ L) :
    evalFormalVec (activeGateAssignment θ ρ) (formalW θ w v n hn) =
      evalFormalVec ρ (formalW θ w v n hn) :=
  (eval_formalPoint_activeGateAssignment (θ := θ) ρ w v n hn).1

theorem eval_formalV_activeGateAssignment (ρ : FormalVar L k → ℝ)
    (w v : Vec d) {n : Nat} (hn : n ≤ L) :
    evalFormalVec (activeGateAssignment θ ρ) (formalV θ w v n hn) =
      evalFormalVec ρ (formalV θ w v n hn) :=
  (eval_formalPoint_activeGateAssignment (θ := θ) ρ w v n hn).2

/-- Zeroing all inactive variables does not change evaluated formal slopes. -/
theorem eval_formalSlope_activeGateAssignment (ρ : FormalVar L k → ℝ)
    (w v : Vec d) (l : Fin L) (a : Fin k) :
    MvPolynomial.eval (activeGateAssignment θ ρ) (formalSlope θ w v l a) =
      MvPolynomial.eval ρ (formalSlope θ w v l a) := by
  refine eval_formalSlope_eq_of_eq_on_active (θ := θ)
    (activeGateAssignment θ ρ) ρ w v l a ?_
  intro l' a' _hl ha
  exact activeGateAssignment_eq_of_active θ ρ ha

/-- Changing one inactive variable does not change evaluated formal streams. -/
theorem eval_formalPoint_update_inactive (ρ : FormalVar L k → ℝ)
    {l₀ : Fin L} {a₀ : Fin k} (hinactive : a₀ ∉ activeHeads θ l₀)
    (t : ℝ) (w v : Vec d) (n : Nat) (hn : n ≤ L) :
    evalFormalVec (updateFormalVar ρ (l₀, a₀) t) (formalPoint θ w v n hn).1 =
        evalFormalVec ρ (formalPoint θ w v n hn).1 ∧
      evalFormalVec (updateFormalVar ρ (l₀, a₀) t) (formalPoint θ w v n hn).2 =
        evalFormalVec ρ (formalPoint θ w v n hn).2 := by
  refine eval_formalPoint_eq_of_eq_on_active (θ := θ)
    (updateFormalVar ρ (l₀, a₀) t) ρ w v n hn ?_
  intro l a _hl ha
  have hne : (l, a) ≠ (l₀, a₀) := by
    intro hpair
    cases hpair
    exact hinactive ha
  exact updateFormalVar_of_ne ρ hne t

theorem eval_formalW_update_inactive (ρ : FormalVar L k → ℝ)
    {l₀ : Fin L} {a₀ : Fin k} (hinactive : a₀ ∉ activeHeads θ l₀)
    (t : ℝ) (w v : Vec d) {n : Nat} (hn : n ≤ L) :
    evalFormalVec (updateFormalVar ρ (l₀, a₀) t) (formalW θ w v n hn) =
      evalFormalVec ρ (formalW θ w v n hn) :=
  (eval_formalPoint_update_inactive (θ := θ) ρ hinactive t w v n hn).1

theorem eval_formalV_update_inactive (ρ : FormalVar L k → ℝ)
    {l₀ : Fin L} {a₀ : Fin k} (hinactive : a₀ ∉ activeHeads θ l₀)
    (t : ℝ) (w v : Vec d) {n : Nat} (hn : n ≤ L) :
    evalFormalVec (updateFormalVar ρ (l₀, a₀) t) (formalV θ w v n hn) =
      evalFormalVec ρ (formalV θ w v n hn) :=
  (eval_formalPoint_update_inactive (θ := θ) ρ hinactive t w v n hn).2

/-- Changing one inactive variable does not change evaluated formal slopes. -/
theorem eval_formalSlope_update_inactive (ρ : FormalVar L k → ℝ)
    {l₀ : Fin L} {a₀ : Fin k} (hinactive : a₀ ∉ activeHeads θ l₀)
    (t : ℝ) (w v : Vec d) (l : Fin L) (a : Fin k) :
    MvPolynomial.eval (updateFormalVar ρ (l₀, a₀) t) (formalSlope θ w v l a) =
      MvPolynomial.eval ρ (formalSlope θ w v l a) := by
  refine eval_formalSlope_eq_of_eq_on_active (θ := θ)
    (updateFormalVar ρ (l₀, a₀) t) ρ w v l a ?_
  intro l' a' _hl ha
  have hne : (l', a') ≠ (l₀, a₀) := by
    intro hpair
    cases hpair
    exact hinactive ha
  exact updateFormalVar_of_ne ρ hne t

/-- `K04D.E.lem-inactive-variables.S/P`: bundled inactive-variable API for streams and
slopes, stated in evaluation-invariance form. -/
theorem lem_inactive_variables (ρ : FormalVar L k → ℝ)
    {l₀ : Fin L} {a₀ : Fin k} (hinactive : valueMatrix θ l₀ a₀ = 0)
    (t : ℝ) (w v : Vec d) :
    (∀ (n : Nat) (hn : n ≤ L),
      evalFormalVec (updateFormalVar ρ (l₀, a₀) t) (formalW θ w v n hn) =
        evalFormalVec ρ (formalW θ w v n hn) ∧
      evalFormalVec (updateFormalVar ρ (l₀, a₀) t) (formalV θ w v n hn) =
        evalFormalVec ρ (formalV θ w v n hn)) ∧
    (∀ (l : Fin L) (a : Fin k),
      MvPolynomial.eval (updateFormalVar ρ (l₀, a₀) t) (formalSlope θ w v l a) =
        MvPolynomial.eval ρ (formalSlope θ w v l a)) := by
  have hinactive' : a₀ ∉ activeHeads θ l₀ := by
    rw [not_mem_activeHeads_iff_valueMatrix_eq_zero]
    exact hinactive
  constructor
  · intro n hn
    exact ⟨eval_formalW_update_inactive (θ := θ) ρ hinactive' t w v hn,
      eval_formalV_update_inactive (θ := θ) ρ hinactive' t w v hn⟩
  · intro l a
    exact eval_formalSlope_update_inactive (θ := θ) ρ hinactive' t w v l a

end InactiveVariables

section ReducedStratificationAPI

/-- Complex-valued vectors used for holomorphic continuations. -/
abbrev ComplexVec (d : Nat) : Type := Fin d → ℂ

/-- Embed a real vector as a complex-valued vector. -/
def realVecToComplex {d : Nat} (x : Vec d) : ComplexVec d :=
  fun i => (x i : ℂ)

/-- Evaluate a real formal polynomial at complex gate values. -/
noncomputable def evalFormalPolyComplex {L k : Nat}
    (η : FormalVar L k → ℂ) (p : FormalPoly L k) : ℂ :=
  MvPolynomial.eval₂ (algebraMap ℝ ℂ) η p

/-- Complex evaluation at a real-valued assignment agrees with real evaluation followed
by the scalar embedding into `ℂ`. -/
theorem evalFormalPolyComplex_ofReal {L k : Nat}
    (η : FormalVar L k → ℝ) (p : FormalPoly L k) :
    evalFormalPolyComplex (fun x => (η x : ℂ)) p =
      (MvPolynomial.eval η p : ℂ) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      simp [evalFormalPolyComplex]
  | add _p _q hp hq =>
      simp only [evalFormalPolyComplex, MvPolynomial.eval₂_add, map_add]
      change evalFormalPolyComplex (fun x => (η x : ℂ)) _p +
          evalFormalPolyComplex (fun x => (η x : ℂ)) _q =
        ((MvPolynomial.eval η _p + MvPolynomial.eval η _q : ℝ) : ℂ)
      rw [hp, hq]
      norm_num
  | mul_X _p _x hp =>
      simp only [evalFormalPolyComplex, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X,
        MvPolynomial.eval_X, map_mul]
      change evalFormalPolyComplex (fun x => (η x : ℂ)) _p * (η _x : ℂ) =
        ((MvPolynomial.eval η _p * η _x : ℝ) : ℂ)
      rw [hp]
      norm_num

/-- A formal polynomial evaluated at complex coordinates that are all real-valued is
itself real-valued. -/
theorem evalFormalPolyComplex_real_of_real_assignment {L k : Nat}
    {η : FormalVar L k → ℂ} (p : FormalPoly L k)
    (hη : ∀ x : FormalVar L k, ∃ t : ℝ, η x = t) :
    ∃ t : ℝ, evalFormalPolyComplex η p = t := by
  classical
  choose ηr hηr using hη
  have hηeq : η = fun x => (ηr x : ℂ) := by
    funext x
    exact hηr x
  refine ⟨MvPolynomial.eval ηr p, ?_⟩
  rw [hηeq]
  exact evalFormalPolyComplex_ofReal ηr p

/-- Evaluate a real formal vector at complex gate values. -/
noncomputable def evalFormalVecComplex {L k d : Nat}
    (η : FormalVar L k → ℂ) (x : FormalVec L k d) : ComplexVec d :=
  fun i => evalFormalPolyComplex η (x i)

@[simp] theorem evalFormalVecComplex_realVecToFormal {L k d : Nat}
    (η : FormalVar L k → ℂ) (x : Vec d) :
    evalFormalVecComplex η (realVecToFormal (L := L) (k := k) x) =
      realVecToComplex x := by
  ext i
  simp [evalFormalVecComplex, evalFormalPolyComplex, realVecToFormal, realVecToComplex,
    formalConst]

/-- Complex formal-vector evaluation at a real-valued assignment is the complexification
of real formal-vector evaluation. -/
theorem evalFormalVecComplex_ofReal {L k d : Nat}
    (η : FormalVar L k → ℝ) (x : FormalVec L k d) :
    evalFormalVecComplex (fun y => (η y : ℂ)) x =
      realVecToComplex (evalFormalVec η x) := by
  ext i
  simp [evalFormalVecComplex, evalFormalVec, realVecToComplex,
    evalFormalPolyComplex_ofReal]

/-- Evaluate a formal matrix at complex gate values. -/
noncomputable def evalFormalMatrixComplex {L k d : Nat}
    (η : FormalVar L k → ℂ) (M : Matrix (Fin d) (Fin d) (FormalPoly L k)) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun i j => evalFormalPolyComplex η (M i j)

@[simp] theorem evalFormalVecComplex_add {L k d : Nat}
    (η : FormalVar L k → ℂ) (x y : FormalVec L k d) :
    evalFormalVecComplex η (x + y) =
      evalFormalVecComplex η x + evalFormalVecComplex η y := by
  ext i
  simp [evalFormalVecComplex, evalFormalPolyComplex]

@[simp] theorem evalFormalVecComplex_sub {L k d : Nat}
    (η : FormalVar L k → ℂ) (x y : FormalVec L k d) :
    evalFormalVecComplex η (x - y) =
      evalFormalVecComplex η x - evalFormalVecComplex η y := by
  ext i
  simp [evalFormalVecComplex, evalFormalPolyComplex]

@[simp] theorem evalFormalMatrixComplex_add {L k d : Nat}
    (η : FormalVar L k → ℂ)
    (M N : Matrix (Fin d) (Fin d) (FormalPoly L k)) :
    evalFormalMatrixComplex η (M + N) =
      evalFormalMatrixComplex η M + evalFormalMatrixComplex η N := by
  ext i j
  simp [evalFormalMatrixComplex, evalFormalPolyComplex]

@[simp] theorem evalFormalMatrixComplex_sub {L k d : Nat}
    (η : FormalVar L k → ℂ)
    (M N : Matrix (Fin d) (Fin d) (FormalPoly L k)) :
    evalFormalMatrixComplex η (M - N) =
      evalFormalMatrixComplex η M - evalFormalMatrixComplex η N := by
  ext i j
  simp [evalFormalMatrixComplex, evalFormalPolyComplex]

@[simp] theorem evalFormalVecComplex_mulVec {L k d : Nat}
    (η : FormalVar L k → ℂ)
    (M : Matrix (Fin d) (Fin d) (FormalPoly L k)) (x : FormalVec L k d) :
    evalFormalVecComplex η (M *ᵥ x) =
      evalFormalMatrixComplex η M *ᵥ evalFormalVecComplex η x := by
  ext i
  simp [evalFormalVecComplex, evalFormalMatrixComplex, evalFormalPolyComplex,
    Matrix.mulVec, dotProduct]

@[simp] theorem evalFormalMatrixComplex_realMatrixToFormal {L k d : Nat}
    (η : FormalVar L k → ℂ) (M : Matrix (Fin d) (Fin d) ℝ) :
    evalFormalMatrixComplex η (realMatrixToFormal (L := L) (k := k) M) =
      M.map (algebraMap ℝ ℂ) := by
  ext i j
  simp [evalFormalMatrixComplex, realMatrixToFormal, evalFormalPolyComplex]

@[simp] theorem evalFormalMatrixComplex_formalCollapseMatrix {L k d : Nat}
    (η : FormalVar L k → ℂ) (θ : Params L k d) (l : Fin L) :
    evalFormalMatrixComplex η (formalCollapseMatrix θ l) =
      (collapseMatrix θ l).map (algebraMap ℝ ℂ) := by
  simp [formalCollapseMatrix]

@[simp] theorem evalFormalMatrixComplex_formalGatedValueSum {L k d : Nat}
    (η : FormalVar L k → ℂ) (θ : Params L k d) (l : Fin L) :
    evalFormalMatrixComplex η (formalGatedValueSum θ l) =
      ∑ a : Fin k, η (l, a) • (valueMatrix θ l a).map (algebraMap ℝ ℂ) := by
  ext i j
  simp [evalFormalMatrixComplex, formalGatedValueSum, formalGate, formalValueMatrix,
    realMatrixToFormal, evalFormalPolyComplex, Matrix.sum_apply, Matrix.smul_apply]

/-- Complex evaluation of the formal gated value sum depends only on active gates. -/
theorem evalFormalMatrixComplex_formalGatedValueSum_eq_of_eq_on_active {L k d : Nat}
    {θ : Params L k d} {l : Fin L} {η η' : FormalVar L k → ℂ}
    (hη : ∀ a : Fin k, a ∈ activeHeads θ l → η (l, a) = η' (l, a)) :
    evalFormalMatrixComplex η (formalGatedValueSum θ l) =
      evalFormalMatrixComplex η' (formalGatedValueSum θ l) := by
  classical
  rw [evalFormalMatrixComplex_formalGatedValueSum,
    evalFormalMatrixComplex_formalGatedValueSum]
  refine Finset.sum_congr rfl ?_
  intro a _ha
  by_cases hactive : a ∈ activeHeads θ l
  · simp [hη a hactive]
  · have hV : valueMatrix θ l a = 0 :=
      (not_mem_activeHeads_iff_valueMatrix_eq_zero θ l a).1 hactive
    simp [hV]

/-- Complex evaluation of a formal bilinear form gives the bilinear form of the
complex-evaluated vectors. -/
theorem evalFormalPolyComplex_formalBilin {L k d : Nat}
    (η : FormalVar L k → ℂ) (A : Matrix (Fin d) (Fin d) ℝ)
    (w v : FormalVec L k d) :
    evalFormalPolyComplex η (formalBilin A w v) =
      evalFormalVecComplex η w ⬝ᵥ (A.map (algebraMap ℝ ℂ)) *ᵥ
        evalFormalVecComplex η v := by
  simp [formalBilin, evalFormalVecComplex, evalFormalPolyComplex, realMatrixToFormal,
    Matrix.mulVec, dotProduct]

/-- One formal step, evaluated at complex assignments, depends only on active gates. -/
theorem eval_formalStepPointComplex_eq_of_eq_on_active {L k d : Nat}
    {θ : Params L k d} (η η' : FormalVar L k → ℂ)
    {l : Fin L} {w v : FormalVec L k d}
    (hη : ∀ a : Fin k, a ∈ activeHeads θ l → η (l, a) = η' (l, a))
    (hw : evalFormalVecComplex η w = evalFormalVecComplex η' w)
    (hv : evalFormalVecComplex η v = evalFormalVecComplex η' v) :
    evalFormalVecComplex η (formalStepPoint θ l w v).1 =
        evalFormalVecComplex η' (formalStepPoint θ l w v).1 ∧
      evalFormalVecComplex η (formalStepPoint θ l w v).2 =
        evalFormalVecComplex η' (formalStepPoint θ l w v).2 := by
  have hD :
      evalFormalMatrixComplex η (formalGatedValueSum θ l) =
        evalFormalMatrixComplex η' (formalGatedValueSum θ l) :=
    evalFormalMatrixComplex_formalGatedValueSum_eq_of_eq_on_active hη
  constructor
  · simp [formalStepPoint, hD, hw]
  · simp [formalStepPoint, hD, hw, hv]

/-- Formal streams through `n` layers have the same complex evaluation when the
assignments agree on active variables in earlier layers. -/
theorem eval_formalPointComplex_eq_of_eq_on_active {L k d : Nat}
    {θ : Params L k d} (η η' : FormalVar L k → ℂ)
    (w v : Vec d) :
    ∀ (n : Nat) (hn : n ≤ L),
      (∀ (l : Fin L) (a : Fin k), l.1 < n → a ∈ activeHeads θ l →
        η (l, a) = η' (l, a)) →
        evalFormalVecComplex η (formalPoint θ w v n hn).1 =
            evalFormalVecComplex η' (formalPoint θ w v n hn).1 ∧
          evalFormalVecComplex η (formalPoint θ w v n hn).2 =
            evalFormalVecComplex η' (formalPoint θ w v n hn).2
  | 0, _hn, _hη => by
      simp [formalPoint]
  | n + 1, hn, hη => by
      let l : Fin L := ⟨n, Nat.lt_of_succ_le hn⟩
      have hprev :
          evalFormalVecComplex η (formalPoint θ w v n (Nat.le_of_succ_le hn)).1 =
              evalFormalVecComplex η' (formalPoint θ w v n (Nat.le_of_succ_le hn)).1 ∧
            evalFormalVecComplex η (formalPoint θ w v n (Nat.le_of_succ_le hn)).2 =
              evalFormalVecComplex η' (formalPoint θ w v n (Nat.le_of_succ_le hn)).2 :=
        eval_formalPointComplex_eq_of_eq_on_active η η' w v n (Nat.le_of_succ_le hn)
          (fun l' a hl' ha => hη l' a (Nat.lt_trans hl' (Nat.lt_succ_self n)) ha)
      have hstep :
          evalFormalVecComplex η
              (formalStepPoint θ l
                (formalPoint θ w v n (Nat.le_of_succ_le hn)).1
                (formalPoint θ w v n (Nat.le_of_succ_le hn)).2).1 =
              evalFormalVecComplex η'
                (formalStepPoint θ l
                  (formalPoint θ w v n (Nat.le_of_succ_le hn)).1
                  (formalPoint θ w v n (Nat.le_of_succ_le hn)).2).1 ∧
            evalFormalVecComplex η
              (formalStepPoint θ l
                (formalPoint θ w v n (Nat.le_of_succ_le hn)).1
                (formalPoint θ w v n (Nat.le_of_succ_le hn)).2).2 =
              evalFormalVecComplex η'
                (formalStepPoint θ l
                  (formalPoint θ w v n (Nat.le_of_succ_le hn)).1
                  (formalPoint θ w v n (Nat.le_of_succ_le hn)).2).2 :=
        eval_formalStepPointComplex_eq_of_eq_on_active (θ := θ) η η'
          (l := l)
          (w := (formalPoint θ w v n (Nat.le_of_succ_le hn)).1)
          (v := (formalPoint θ w v n (Nat.le_of_succ_le hn)).2)
          (fun a ha => hη l a (by simp [l]) ha) hprev.1 hprev.2
      simpa [formalPoint, l] using hstep

/-- Complex evaluations of a formal slope depend only on active gate variables in
previous layers. -/
theorem evalFormalPolyComplex_formalSlope_eq_of_eq_on_active {L k d : Nat}
    {θ : Params L k d} (η η' : FormalVar L k → ℂ)
    (w v : Vec d) (l : Fin L) (a : Fin k)
    (hη : ∀ (l' : Fin L) (a' : Fin k), l'.1 < l.1 → a' ∈ activeHeads θ l' →
      η (l', a') = η' (l', a')) :
    evalFormalPolyComplex η (formalSlope θ w v l a) =
      evalFormalPolyComplex η' (formalSlope θ w v l a) := by
  have hprev :
      evalFormalVecComplex η (formalW θ w v l.1 (Nat.le_of_lt l.2)) =
          evalFormalVecComplex η' (formalW θ w v l.1 (Nat.le_of_lt l.2)) ∧
        evalFormalVecComplex η (formalV θ w v l.1 (Nat.le_of_lt l.2)) =
          evalFormalVecComplex η' (formalV θ w v l.1 (Nat.le_of_lt l.2)) :=
    eval_formalPointComplex_eq_of_eq_on_active (θ := θ) η η' w v l.1
      (Nat.le_of_lt l.2) hη
  rw [formalSlope, evalFormalPolyComplex_formalBilin,
    evalFormalPolyComplex_formalBilin, hprev.1, hprev.2]

/-- Analyticity is preserved by complex evaluation of a real formal polynomial at
analytic gate-coordinate functions. -/
theorem evalFormalPolyComplex_analyticOnNhd {L k : Nat} (p : FormalPoly L k)
    {U : Set ℂ} {η : FormalVar L k → ℂ → ℂ}
    (hη : ∀ x : FormalVar L k, AnalyticOnNhd ℂ (η x) U) :
    AnalyticOnNhd ℂ
      (fun τ => evalFormalPolyComplex (fun x => η x τ) p) U := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      simpa [evalFormalPolyComplex] using
        (analyticOnNhd_const (𝕜 := ℂ) (v := (algebraMap ℝ ℂ a)) (s := U))
  | add _p _q hp hq =>
      simpa [evalFormalPolyComplex] using hp.add hq
  | mul_X _p x hp =>
      simpa [evalFormalPolyComplex] using hp.mul (hη x)

/-- Coordinatewise analytic version of `evalFormalPolyComplex_analyticOnNhd`. -/
theorem evalFormalVecComplex_analyticOnNhd {L k d : Nat} (x : FormalVec L k d)
    {U : Set ℂ} {η : FormalVar L k → ℂ → ℂ}
    (hη : ∀ y : FormalVar L k, AnalyticOnNhd ℂ (η y) U) :
    ∀ i : Fin d,
      AnalyticOnNhd ℂ
        (fun τ => evalFormalVecComplex (fun y => η y τ) x i) U := by
  intro i
  exact evalFormalPolyComplex_analyticOnNhd (x i) hη

/-- Value matrices commute with passing to the tail parameter sequence. -/
theorem valueMatrix_tail_succ {L k d : Nat} (θ : Params (L + 1) k d)
    (l : Fin L) (a : Fin k) :
    valueMatrix (Fin.tail θ) l a = valueMatrix θ l.succ a := by
  rfl

/-- Attention matrices commute with passing to the tail parameter sequence. -/
theorem attentionMatrix_tail_succ {L k d : Nat} (θ : Params (L + 1) k d)
    (l : Fin L) (a : Fin k) :
    attentionMatrix (Fin.tail θ) l a = attentionMatrix θ l.succ a := by
  rfl

/-- Value sums commute with passing to the tail parameter sequence. -/
theorem valueSum_tail_succ {L k d : Nat} (θ : Params (L + 1) k d)
    (l : Fin L) :
    valueSum (Fin.tail θ) l = valueSum θ l.succ := by
  simp [valueSum, valueMatrix_tail_succ]

/-- Collapse matrices commute with passing to the tail parameter sequence. -/
theorem collapseMatrix_tail_succ {L k d : Nat} (θ : Params (L + 1) k d)
    (l : Fin L) :
    collapseMatrix (Fin.tail θ) l = collapseMatrix θ l.succ := by
  simp [collapseMatrix, valueSum_tail_succ]

/-- Gated value sums commute with passing to the tail parameter sequence. -/
theorem gatedValueSum_tail_succ {L k d : Nat} (θ : Params (L + 1) k d)
    (l : Fin L) (g : Fin k → ℝ) :
    gatedValueSum (Fin.tail θ) l g = gatedValueSum θ l.succ g := by
  simp [gatedValueSum, valueMatrix_tail_succ]

/-- Probe layer gates commute with passing to the tail parameter sequence. -/
theorem layerGates_tail_succ {r L k d : Nat} (θ : Params (L + 1) k d)
    (l : Fin L) (w v : Vec d) (τ : ℝ) :
    layerGates r (Fin.tail θ) l w v τ = layerGates r θ l.succ w v τ := by
  funext a
  simp [layerGates, attentionMatrix_tail_succ]

/-- One gated probe step commutes with passing to the tail parameter sequence. -/
theorem gatedEffectivePoint_tail_succ {L k d : Nat} (θ : Params (L + 1) k d)
    (l : Fin L) (g : Fin k → ℝ) (w v : Vec d) :
    gatedEffectivePoint (Fin.tail θ) l g w v = gatedEffectivePoint θ l.succ g w v := by
  simp [gatedEffectivePoint, collapseMatrix_tail_succ, gatedValueSum_tail_succ]

/-- Closed probe recursion indexed by the original layer number.  This exposes the
intermediate stream used to state consistency of the continued gates with the real probe
recursion. -/
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

/-- Peeling the first layer from the original-index recursion agrees with running the
same original-index recursion on `Fin.tail θ` from the first-layer probe point. -/
theorem actualProbePoint_firstLayer_tail_aux {r L k d : Nat}
    (θ : Params (L + 1) k d) (w v : Vec d) (τ : ℝ) :
    ∀ (n : Nat) (hn : n + 1 ≤ L + 1),
      actualProbePoint r θ w v (n + 1) hn τ =
        actualProbePoint r (Fin.tail θ)
          (firstLayerEffectivePoint r θ w v τ).1
          (firstLayerEffectivePoint r θ w v τ).2 n
          (Nat.succ_le_succ_iff.mp hn) τ
  | 0, _hn => by
      simp [actualProbePoint, firstLayerEffectivePoint, gatedEffectivePoint]
  | n + 1, hn => by
      conv_lhs => rw [actualProbePoint_succ]
      conv_rhs => rw [actualProbePoint_succ]
      rw [actualProbePoint_firstLayer_tail_aux θ w v τ n (Nat.le_of_succ_le hn)]
      let lTail : Fin L := ⟨n, Nat.lt_of_succ_le (Nat.succ_le_succ_iff.mp hn)⟩
      have hl :
          (⟨n + 1, Nat.lt_of_succ_le hn⟩ : Fin (L + 1)) = lTail.succ := by
        ext
        rfl
      rw [hl]
      let prev : ProbePoint d :=
        actualProbePoint r (Fin.tail θ)
          (firstLayerEffectivePoint r θ w v τ).1
          (firstLayerEffectivePoint r θ w v τ).2 n
          (Nat.succ_le_succ_iff.mp (Nat.le_of_succ_le hn)) τ
      change
        gatedEffectivePoint θ lTail.succ (layerGates r θ lTail.succ prev.1 prev.2 τ)
            prev.1 prev.2 =
          gatedEffectivePoint (Fin.tail θ) lTail
            (layerGates r (Fin.tail θ) lTail prev.1 prev.2 τ) prev.1 prev.2
      rw [← layerGates_tail_succ θ lTail]
      rw [← gatedEffectivePoint_tail_succ θ lTail]

/-- Full-depth form of `actualProbePoint_firstLayer_tail_aux`. -/
theorem actualProbePoint_firstLayer_tail {r L k d : Nat}
    (θ : Params (L + 1) k d) (w v : Vec d) (τ : ℝ) :
    actualProbePoint r θ w v (L + 1) le_rfl τ =
      actualProbePoint r (Fin.tail θ)
        (firstLayerEffectivePoint r θ w v τ).1
        (firstLayerEffectivePoint r θ w v τ).2 L le_rfl τ := by
  simpa using actualProbePoint_firstLayer_tail_aux (r := r) θ w v τ L le_rfl

/-- The original-index probe recursion agrees with the tail-recursive `Probe.lean` API
at full depth. -/
theorem actualProbePoint_eq_probeRecursionPoint (r : Nat) {L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (τ : ℝ) :
    actualProbePoint r θ w v L le_rfl τ = probeRecursionPoint r θ w v τ := by
  induction L generalizing w v with
  | zero =>
      simp
  | succ L ih =>
      rw [actualProbePoint_firstLayer_tail]
      rw [probeRecursionPoint_succ]
      exact ih (Fin.tail θ)
        (firstLayerEffectivePoint r θ w v τ).1
        (firstLayerEffectivePoint r θ w v τ).2

/-- The second coordinate of the original-index recursion is `probeOutput`. -/
theorem actualProbePoint_snd_eq_probeOutput (r : Nat) {L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (τ : ℝ) :
    (actualProbePoint r θ w v L le_rfl τ).2 = probeOutput r θ w v τ := by
  rw [actualProbePoint_eq_probeRecursionPoint]
  rfl

/-- The real slope used by the actual probe recursion at layer `l`. -/
noncomputable def actualProbeSlope (r : Nat) {L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (τ : ℝ) (l : Fin L) (a : Fin k) : ℝ :=
  matrixBilin (attentionMatrix θ l a)
    (actualProbePoint r θ w v l.1 (Nat.le_of_lt l.2) τ).1
    (actualProbePoint r θ w v l.1 (Nat.le_of_lt l.2) τ).2

/-- The actual real gate used by the probe recursion at layer `l`. -/
noncomputable def actualProbeGate (r : Nat) {L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (τ : ℝ) (l : Fin L) (a : Fin k) : ℝ :=
  layerGates r θ l
    (actualProbePoint r θ w v l.1 (Nat.le_of_lt l.2) τ).1
    (actualProbePoint r θ w v l.1 (Nat.le_of_lt l.2) τ).2 τ a

/-- The actual probe gate is the real sigmoid of its probe-recursion level. -/
theorem actualProbeGate_eq_sig (r : Nat) {L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (τ : ℝ) (l : Fin L) (a : Fin k) :
    actualProbeGate r θ w v τ l a =
      sig (τ * actualProbeSlope r θ w v τ l a + logScale r) := by
  simp [actualProbeGate, actualProbeSlope, layerGates, headGate]

/-- Real formal-gate assignment induced by the actual probe recursion at a fixed
positive-real parameter. -/
noncomputable def actualProbeGateAssignment (r : Nat) {L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (τ : ℝ) : FormalVar L k → ℝ :=
  fun x => actualProbeGate r θ w v τ x.1 x.2

/-- Evaluating the formal streams at the actual probe gates recovers the closed actual
probe recursion through every prefix depth. -/
theorem eval_formalPoint_actualProbeGateAssignment (r : Nat) {L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (τ : ℝ) :
    ∀ (n : Nat) (hn : n ≤ L),
      evalFormalVec (actualProbeGateAssignment r θ w v τ)
          (formalPoint θ w v n hn).1 =
          (actualProbePoint r θ w v n hn τ).1 ∧
        evalFormalVec (actualProbeGateAssignment r θ w v τ)
          (formalPoint θ w v n hn).2 =
          (actualProbePoint r θ w v n hn τ).2
  | 0, _hn => by
      simp [formalPoint, actualProbePoint]
  | n + 1, hn => by
      let l : Fin L := ⟨n, Nat.lt_of_succ_le hn⟩
      have hprev :
          evalFormalVec (actualProbeGateAssignment r θ w v τ)
              (formalPoint θ w v n (Nat.le_of_succ_le hn)).1 =
              (actualProbePoint r θ w v n (Nat.le_of_succ_le hn) τ).1 ∧
            evalFormalVec (actualProbeGateAssignment r θ w v τ)
              (formalPoint θ w v n (Nat.le_of_succ_le hn)).2 =
              (actualProbePoint r θ w v n (Nat.le_of_succ_le hn) τ).2 :=
        eval_formalPoint_actualProbeGateAssignment r θ w v τ n (Nat.le_of_succ_le hn)
      constructor
      · simp [formalPoint, actualProbePoint, eval_formalStepPoint_fst,
          hprev.1, hprev.2, actualProbeGateAssignment, actualProbeGate]
      · simp [formalPoint, actualProbePoint, eval_formalStepPoint_snd,
          hprev.1, hprev.2, actualProbeGateAssignment, actualProbeGate]

/-- Formal `w_n` evaluated at actual probe gates gives the first coordinate of the
actual prefix recursion. -/
theorem eval_formalW_actualProbeGateAssignment (r : Nat) {L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (τ : ℝ) {n : Nat} (hn : n ≤ L) :
    evalFormalVec (actualProbeGateAssignment r θ w v τ) (formalW θ w v n hn) =
      (actualProbePoint r θ w v n hn τ).1 := by
  simpa [formalW] using
    (eval_formalPoint_actualProbeGateAssignment r θ w v τ n hn).1

/-- Formal `v_n` evaluated at actual probe gates gives the second coordinate of the
actual prefix recursion. -/
theorem eval_formalV_actualProbeGateAssignment (r : Nat) {L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (τ : ℝ) {n : Nat} (hn : n ≤ L) :
    evalFormalVec (actualProbeGateAssignment r θ w v τ) (formalV θ w v n hn) =
      (actualProbePoint r θ w v n hn τ).2 := by
  simpa [formalV] using
    (eval_formalPoint_actualProbeGateAssignment r θ w v τ n hn).2

/-- Formal slopes evaluated at the actual probe gates are the actual probe slopes. -/
theorem eval_formalSlope_actualProbeGateAssignment (r : Nat) {L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (τ : ℝ) (l : Fin L) (a : Fin k) :
    MvPolynomial.eval (actualProbeGateAssignment r θ w v τ)
        (formalSlope θ w v l a) =
      actualProbeSlope r θ w v τ l a := by
  rw [eval_formalSlope]
  simp [actualProbeSlope,
    eval_formalW_actualProbeGateAssignment r θ w v τ (Nat.le_of_lt l.2),
    eval_formalV_actualProbeGateAssignment r θ w v τ (Nat.le_of_lt l.2)]

/-- Data slots for the active-head reduced singular stratification.  The TeX-facing
proposition below supplies the semantic fields tying these slots to a probe `(w, v)` and to
the actual recursion. -/
structure ActiveStratificationData (L k d : Nat) where
  Omega : Nat → Set ℂ
  stratum : Nat → Set ℂ
  level : FormalVar L k → ℂ → ℂ
  gate : FormalVar L k → ℂ → ℂ
  observable : ℂ → ComplexVec d

/-- The nonnegative real axis inside the complex plane. -/
def nonnegativeRealAxis : Set ℂ :=
  {z | ∃ t : ℝ, 0 ≤ t ∧ z = t}

/-- The positive real axis inside the complex plane. -/
def positiveRealAxis : Set ℂ :=
  {z | ∃ t : ℝ, 0 < t ∧ z = t}

/-- A positive real number lies on the positive real axis. -/
theorem ofReal_mem_positiveRealAxis {t : ℝ} (ht : 0 < t) :
    (t : ℂ) ∈ positiveRealAxis :=
  ⟨t, ht, rfl⟩

/-- The point `1` lies on the positive real axis. -/
theorem one_mem_positiveRealAxis : (1 : ℂ) ∈ positiveRealAxis := by
  exact ofReal_mem_positiveRealAxis (by norm_num : (0 : ℝ) < 1)

/-- The positive real axis is contained in the nonnegative real axis. -/
theorem positiveRealAxis_subset_nonnegativeRealAxis :
    positiveRealAxis ⊆ nonnegativeRealAxis := by
  intro z hz
  rcases hz with ⟨t, ht, rfl⟩
  exact ⟨t, le_of_lt ht, rfl⟩

/-- Any set containing the nonnegative real axis contains the positive real axis. -/
theorem positiveRealAxis_subset_of_nonnegativeRealAxis_subset {U : Set ℂ}
    (hU : nonnegativeRealAxis ⊆ U) :
    positiveRealAxis ⊆ U :=
  fun _ hz => hU (positiveRealAxis_subset_nonnegativeRealAxis hz)

/-- The origin lies on the nonnegative real axis. -/
theorem zero_mem_nonnegativeRealAxis : (0 : ℂ) ∈ nonnegativeRealAxis := by
  exact ⟨0, le_rfl, by simp⟩

/-- Any set containing the nonnegative real axis contains the origin. -/
theorem zero_mem_of_nonnegativeRealAxis_subset {U : Set ℂ}
    (hU : nonnegativeRealAxis ⊆ U) :
    (0 : ℂ) ∈ U :=
  hU zero_mem_nonnegativeRealAxis

/-- A function is real-valued on a subset of the complex plane. -/
def IsRealValuedOn (F : ℂ → ℂ) (A : Set ℂ) : Prop :=
  ∀ z ∈ A, ∃ x : ℝ, F z = x

/-- The reduced stratum at layer `l`, indexed only by active heads. -/
def reducedStratumAt {L k d : Nat} (θ : Params L k d)
    (D : ActiveStratificationData L k d) (l : Fin L) : Set ℂ :=
  {τ | ∃ a : Fin k, a ∈ activeHeads θ l ∧
    τ ∈ D.Omega l.1 ∧ D.level (l, a) τ ∈ Pi}

/-- The corresponding unreduced stratum, indexed by every head. -/
def fullStratumAt {L k d : Nat} (D : ActiveStratificationData L k d)
    (l : Fin L) : Set ℂ :=
  {τ | ∃ a : Fin k, τ ∈ D.Omega l.1 ∧ D.level (l, a) τ ∈ Pi}

theorem reducedStratumAt_subset_omega {L k d : Nat} (θ : Params L k d)
    (D : ActiveStratificationData L k d) (l : Fin L) :
    reducedStratumAt θ D l ⊆ D.Omega l.1 := by
  intro τ hτ
  rcases hτ with ⟨_a, _ha, hτΩ, _hτPi⟩
  exact hτΩ

theorem fullStratumAt_subset_omega {L k d : Nat}
    (D : ActiveStratificationData L k d) (l : Fin L) :
    fullStratumAt D l ⊆ D.Omega l.1 := by
  intro τ hτ
  rcases hτ with ⟨_a, hτΩ, _hτPi⟩
  exact hτΩ

theorem reducedStratumAt_subset_fullStratumAt {L k d : Nat} (θ : Params L k d)
    (D : ActiveStratificationData L k d) (l : Fin L) :
    reducedStratumAt θ D l ⊆ fullStratumAt D l := by
  intro τ hτ
  rcases hτ with ⟨a, _ha, hτΩ, hτPi⟩
  exact ⟨a, hτΩ, hτPi⟩

/-- Recursive domains for a candidate active-head stratification, generated by removing
the reduced singular stratum at each available layer.  Values after layer `L` are held
constant only to make the function total on `Nat`; all API statements below use `n ≤ L`. -/
noncomputable def activeRecursiveOmega {L k d : Nat} (θ : Params L k d)
    (level : FormalVar L k → ℂ → ℂ) : Nat → Set ℂ
  | 0 => Set.univ
  | n + 1 =>
      if hn : n < L then
        activeRecursiveOmega θ level n \
          {τ | ∃ a : Fin k, a ∈ activeHeads θ ⟨n, hn⟩ ∧
            τ ∈ activeRecursiveOmega θ level n ∧ level (⟨n, hn⟩, a) τ ∈ Pi}
      else activeRecursiveOmega θ level n

/-- Recursive reduced stratum at layer `n`, using active heads only. -/
noncomputable def activeRecursiveStratum {L k d : Nat} (θ : Params L k d)
    (level : FormalVar L k → ℂ → ℂ) (n : Nat) : Set ℂ :=
  if hn : n < L then
    {τ | ∃ a : Fin k, a ∈ activeHeads θ ⟨n, hn⟩ ∧
      τ ∈ activeRecursiveOmega θ level n ∧ level (⟨n, hn⟩, a) τ ∈ Pi}
  else ∅

@[simp] theorem activeRecursiveOmega_zero {L k d : Nat} (θ : Params L k d)
    (level : FormalVar L k → ℂ → ℂ) :
    activeRecursiveOmega θ level 0 = Set.univ :=
  rfl

/-- The recursive domain update `Ω_{j+1} = Ω_j \ S_j`. -/
theorem activeRecursiveOmega_succ {L k d : Nat} (θ : Params L k d)
    (level : FormalVar L k → ℂ → ℂ) {n : Nat} (hn : n < L) :
    activeRecursiveOmega θ level (n + 1) =
      activeRecursiveOmega θ level n \ activeRecursiveStratum θ level n := by
  simp [activeRecursiveOmega, activeRecursiveStratum, hn]

/-- If all candidate level functions are real-valued on the nonnegative real axis, the
recursive active-head removals never delete that axis. -/
theorem activeRecursiveOmega_nonnegativeRealAxis_subset_of_level_real {L k d : Nat}
    (θ : Params L k d) (level : FormalVar L k → ℂ → ℂ)
    (hlevel : ∀ x : FormalVar L k, IsRealValuedOn (level x) nonnegativeRealAxis) :
    ∀ n : Nat, n ≤ L → nonnegativeRealAxis ⊆ activeRecursiveOmega θ level n
  | 0, _hn => by
      intro τ _hτ
      simp [activeRecursiveOmega]
  | n + 1, hn => by
      intro τ hτ
      have hprev :
          τ ∈ activeRecursiveOmega θ level n :=
        activeRecursiveOmega_nonnegativeRealAxis_subset_of_level_real θ level hlevel n
          (Nat.le_of_succ_le hn) hτ
      have hnL : n < L := Nat.lt_of_succ_le hn
      rw [activeRecursiveOmega_succ θ level hnL]
      refine ⟨hprev, ?_⟩
      intro hS
      simp [activeRecursiveStratum, hnL] at hS
      rcases hS with ⟨a, _ha, _hτΩ, hτPi⟩
      rcases hlevel (⟨n, hnL⟩, a) τ hτ with ⟨x, hx⟩
      rw [hx] at hτPi
      exact ofReal_notMem_Pi x hτPi

/-- Assemble `ActiveStratificationData` from candidate level/gate/observable functions,
with `Ω_j` and `S_j` generated by the TeX recursive removal rule. -/
noncomputable def activeStratificationDataOfFunctions {L k d : Nat}
    (θ : Params L k d) (level : FormalVar L k → ℂ → ℂ)
    (gate : FormalVar L k → ℂ → ℂ) (observable : ℂ → ComplexVec d) :
    ActiveStratificationData L k d where
  Omega := activeRecursiveOmega θ level
  stratum := activeRecursiveStratum θ level
  level := level
  gate := gate
  observable := observable

@[simp] theorem activeStratificationDataOfFunctions_omega_zero {L k d : Nat}
    (θ : Params L k d) (level : FormalVar L k → ℂ → ℂ)
    (gate : FormalVar L k → ℂ → ℂ) (observable : ℂ → ComplexVec d) :
    (activeStratificationDataOfFunctions θ level gate observable).Omega 0 = Set.univ :=
  rfl

/-- For the recursive constructor, the stored stratum is exactly the active reduced
stratum determined by the stored domain and level functions. -/
theorem activeStratificationDataOfFunctions_stratum_eq {L k d : Nat}
    (θ : Params L k d) (level : FormalVar L k → ℂ → ℂ)
    (gate : FormalVar L k → ℂ → ℂ) (observable : ℂ → ComplexVec d) (l : Fin L) :
    (activeStratificationDataOfFunctions θ level gate observable).stratum l.1 =
      reducedStratumAt θ (activeStratificationDataOfFunctions θ level gate observable) l := by
  ext τ
  simp [activeStratificationDataOfFunctions, activeRecursiveStratum, reducedStratumAt, l.2]

/-- The assembled data satisfies the recursive domain update. -/
theorem activeStratificationDataOfFunctions_omega_succ {L k d : Nat}
    (θ : Params L k d) (level : FormalVar L k → ℂ → ℂ)
    (gate : FormalVar L k → ℂ → ℂ) (observable : ℂ → ComplexVec d) (l : Fin L) :
    (activeStratificationDataOfFunctions θ level gate observable).Omega (l.1 + 1) =
      (activeStratificationDataOfFunctions θ level gate observable).Omega l.1 \
        (activeStratificationDataOfFunctions θ level gate observable).stratum l.1 := by
  simpa [activeStratificationDataOfFunctions] using activeRecursiveOmega_succ θ level l.2

/-- Axis-preservation form for data assembled by the recursive constructor. -/
theorem activeStratificationDataOfFunctions_nonnegativeRealAxis_subset_omega_of_level_real
    {L k d : Nat} (θ : Params L k d) (level : FormalVar L k → ℂ → ℂ)
    (gate : FormalVar L k → ℂ → ℂ) (observable : ℂ → ComplexVec d)
    (hlevel : ∀ x : FormalVar L k, IsRealValuedOn (level x) nonnegativeRealAxis) :
    ∀ n : Nat, n ≤ L →
      nonnegativeRealAxis ⊆
        (activeStratificationDataOfFunctions θ level gate observable).Omega n := by
  intro n hn
  simpa [activeStratificationDataOfFunctions] using
    activeRecursiveOmega_nonnegativeRealAxis_subset_of_level_real θ level hlevel n hn

/-- If the active level functions are holomorphic and are not constant at a pole value,
then the reduced layer stratum is closed and discrete in the current domain.  Constant
non-pole levels contribute the empty preimage, matching the TeX induction.  This is the
layerwise geometric step in the recursive construction of
`ActiveHeadSingularStratification`. -/
theorem reducedStratumAt_closedDiscrete_of_level_data {L k d : Nat}
    (θ : Params L k d) (D : ActiveStratificationData L k d) (l : Fin L)
    (hΩ : PlaneDomain (D.Omega l.1))
    (hlevel_holomorphic :
      ∀ a : Fin k, a ∈ activeHeads θ l →
        AnalyticOnNhd ℂ (D.level (l, a)) (D.Omega l.1))
    (hlevel_not_constant_pole :
      ∀ a : Fin k, a ∈ activeHeads θ l →
        ∀ c : ℂ, c ∈ Pi →
          ¬ Set.EqOn (D.level (l, a)) (fun _ : ℂ => c) (D.Omega l.1)) :
    ClosedDiscreteIn (reducedStratumAt θ D l) (D.Omega l.1) := by
  classical
  let A : Fin k → Set ℂ :=
    fun a => D.Omega l.1 ∩ (D.level (l, a)) ⁻¹' Pi
  have hA :
      ∀ a, a ∈ activeHeads θ l → ClosedDiscreteIn (A a) (D.Omega l.1) := by
    intro a ha
    by_cases hnonconst :
        ∀ c : ℂ, ¬ Set.EqOn (D.level (l, a)) (fun _ : ℂ => c) (D.Omega l.1)
    · exact closedDiscrete_preimage hΩ.isOpen hΩ.isConnected.isPreconnected
        (hlevel_holomorphic a ha) hnonconst Pi_closedDiscrete
    · have hconst :
          ∃ c : ℂ, Set.EqOn (D.level (l, a)) (fun _ : ℂ => c) (D.Omega l.1) := by
        by_contra hnone
        apply hnonconst
        intro c hc
        exact hnone ⟨c, hc⟩
      rcases hconst with ⟨c, hc⟩
      have hAempty : A a = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.2
        intro τ hτ
        rcases hτ with ⟨hτΩ, hτPi⟩
        have hcPi : c ∈ Pi := by
          simpa [hc hτΩ] using hτPi
        exact (hlevel_not_constant_pole a ha c hcPi) hc
      simpa [hAempty] using closedDiscreteIn_empty (U := D.Omega l.1) hΩ.isOpen
  have hCD : ClosedDiscreteIn (⋃ a ∈ activeHeads θ l, A a) (D.Omega l.1) :=
    closedDiscreteIn_finset_biUnion (activeHeads θ l) hΩ.isOpen hA
  have hEq : (⋃ a, ⋃ _ : IsActiveHead θ l a, A a) = reducedStratumAt θ D l := by
    ext τ
    constructor
    · intro hτ
      simp only [A, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage] at hτ
      rcases hτ with ⟨a, ha, hτΩ, hτPi⟩
      exact ⟨a, (mem_activeHeads θ l a).2 ha, hτΩ, hτPi⟩
    · intro hτ
      rcases hτ with ⟨a, ha, hτΩ, hτPi⟩
      simp only [A, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage]
      exact ⟨a, (mem_activeHeads θ l a).1 ha, hτΩ, hτPi⟩
  simpa [hEq] using hCD

theorem reducedStratumAt_eq_empty_of_activeHeads_eq_empty {L k d : Nat}
    {θ : Params L k d} (D : ActiveStratificationData L k d) {l : Fin L}
    (hactive : activeHeads θ l = ∅) :
    reducedStratumAt θ D l = ∅ := by
  ext τ
  simp [reducedStratumAt, hactive]

/-- The full reduced singular set after `L` layers. -/
def reducedSingularSet {L k d : Nat} (D : ActiveStratificationData L k d) : Set ℂ :=
  partialUnion D.stratum L

/-- The recursive domain update already implies the partial-union complement formula.
This packages a bookkeeping obligation needed by the strong stratification interface. -/
theorem omega_eq_partialUnion_compl_of_omega_succ {L k d : Nat}
    (D : ActiveStratificationData L k d)
    (hzero : D.Omega 0 = Set.univ)
    (hsucc : ∀ l : Fin L, D.Omega (l.1 + 1) = D.Omega l.1 \ D.stratum l.1) :
    ∀ n : Nat, n ≤ L → D.Omega n = (partialUnion D.stratum n)ᶜ
  | 0, _hn => by
      simp [partialUnion, hzero]
  | n + 1, hn => by
      let l : Fin L := ⟨n, Nat.lt_of_succ_le hn⟩
      have hprev :
          D.Omega n = (partialUnion D.stratum n)ᶜ :=
        omega_eq_partialUnion_compl_of_omega_succ D hzero hsucc n
          (Nat.le_of_succ_le hn)
      calc
        D.Omega (n + 1) = D.Omega n \ D.stratum n := by
          simpa [l] using hsucc l
        _ = (partialUnion D.stratum n)ᶜ \ D.stratum n := by
          rw [hprev]
        _ = (partialUnion D.stratum (n + 1))ᶜ := by
          ext τ
          simp [partialUnion_succ, Set.diff_eq]

/-- Recursive domain updates make the domains antitone in the layer index. -/
theorem omega_subset_of_le_of_omega_succ {L k d : Nat}
    (D : ActiveStratificationData L k d)
    (hsucc : ∀ l : Fin L, D.Omega (l.1 + 1) = D.Omega l.1 \ D.stratum l.1) :
    ∀ {m n : Nat}, m ≤ n → n ≤ L → D.Omega n ⊆ D.Omega m
  | m, 0, hmn, _hn => by
      have hm : m = 0 := by omega
      subst m
      exact Set.Subset.rfl
  | m, n + 1, hmn, hn => by
      by_cases hmle : m ≤ n
      · intro τ hτ
        have hnL : n < L := Nat.lt_of_succ_le hn
        let l : Fin L := ⟨n, hnL⟩
        have hτn : τ ∈ D.Omega n := by
          have hτ' := hτ
          rw [hsucc l] at hτ'
          exact hτ'.1
        exact omega_subset_of_le_of_omega_succ D hsucc hmle
          (Nat.le_of_succ_le hn) hτn
      · have hm : m = n + 1 := by omega
        subst m
        exact Set.Subset.rfl

/-- Recursion-only subset of `ActiveHeadSingularStratification`: the data starts from
`Ω₀ = ℂ`, stores the active reduced strata, removes them recursively, and hence satisfies
the partial-union complement identity. -/
structure ActiveHeadRecursiveSkeleton {L k d : Nat} (θ : Params L k d)
    (D : ActiveStratificationData L k d) : Prop where
  omega_zero : D.Omega 0 = Set.univ
  stratum_eq : ∀ l : Fin L, D.stratum l.1 = reducedStratumAt θ D l
  omega_succ : ∀ l : Fin L, D.Omega (l.1 + 1) = D.Omega l.1 \ D.stratum l.1
  omega_eq_partialUnion_compl :
    ∀ n : Nat, n ≤ L → D.Omega n = (partialUnion D.stratum n)ᶜ

/-- The recursive constructor also gives the partial-union complement formula for all
domains up to depth `L`. -/
theorem activeStratificationDataOfFunctions_omega_eq_partialUnion_compl {L k d : Nat}
    (θ : Params L k d) (level : FormalVar L k → ℂ → ℂ)
    (gate : FormalVar L k → ℂ → ℂ) (observable : ℂ → ComplexVec d) :
    ∀ n : Nat, n ≤ L →
      (activeStratificationDataOfFunctions θ level gate observable).Omega n =
        (partialUnion (activeStratificationDataOfFunctions θ level gate observable).stratum n)ᶜ :=
  omega_eq_partialUnion_compl_of_omega_succ
    (activeStratificationDataOfFunctions θ level gate observable)
    (activeStratificationDataOfFunctions_omega_zero θ level gate observable)
    (activeStratificationDataOfFunctions_omega_succ θ level gate observable)

/-- The general recursive constructor proves all recursion-only fields without analytic
assumptions on the candidate levels or gates. -/
theorem activeStratificationDataOfFunctions_recursiveSkeleton {L k d : Nat}
    (θ : Params L k d) (level : FormalVar L k → ℂ → ℂ)
    (gate : FormalVar L k → ℂ → ℂ) (observable : ℂ → ComplexVec d) :
    ActiveHeadRecursiveSkeleton θ (activeStratificationDataOfFunctions θ level gate observable)
    where
  omega_zero := activeStratificationDataOfFunctions_omega_zero θ level gate observable
  stratum_eq := activeStratificationDataOfFunctions_stratum_eq θ level gate observable
  omega_succ := activeStratificationDataOfFunctions_omega_succ θ level gate observable
  omega_eq_partialUnion_compl :=
    activeStratificationDataOfFunctions_omega_eq_partialUnion_compl θ level gate observable

/-- Candidate active gate continuation `s_{la}`.  It is defined by well-founded recursion
on the layer index: when constructing layer `l`, only already-constructed gates from
earlier layers are available to evaluate the formal slope polynomial.  Inactive variables
are fixed to zero. -/
noncomputable def activeConstructedGate {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) : FormalVar L k → ℂ → ℂ := by
  classical
  exact WellFounded.fix ((measure (fun x : FormalVar L k => x.1.1)).wf)
    (fun x rec τ =>
      if IsActiveVar θ x then
        csig (τ * evalFormalPolyComplex
          (fun y =>
            if hy : y.1.1 < x.1.1 then rec y (by simpa [measure] using hy) τ else 0)
          (formalSlope θ w v x.1 x.2) + (logScale r : ℂ))
      else 0)

/-- Candidate active level continuation `H_{la}` built from earlier constructed gates. -/
noncomputable def activeConstructedLevel {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (x : FormalVar L k) (τ : ℂ) : ℂ :=
  τ * evalFormalPolyComplex
    (fun y => if _hy : y.1.1 < x.1.1 then activeConstructedGate (r := r) θ w v y τ else 0)
    (formalSlope θ w v x.1 x.2) + (logScale r : ℂ)

theorem activeConstructedGate_eq_of_active {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) {x : FormalVar L k}
    (hx : IsActiveVar θ x) (τ : ℂ) :
    activeConstructedGate (r := r) θ w v x τ =
      csig (activeConstructedLevel (r := r) θ w v x τ) := by
  classical
  unfold activeConstructedLevel
  rw [activeConstructedGate, WellFounded.fix_eq]
  simp [hx]

theorem activeConstructedGate_eq_zero_of_inactive {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) {x : FormalVar L k}
    (hx : ¬ IsActiveVar θ x) (τ : ℂ) :
    activeConstructedGate (r := r) θ w v x τ = 0 := by
  classical
  rw [activeConstructedGate, WellFounded.fix_eq]
  simp [hx]

/-- Constructed levels take the bias value at the origin. -/
theorem activeConstructedLevel_zero {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (x : FormalVar L k) :
    activeConstructedLevel (r := r) θ w v x 0 = (logScale r : ℂ) := by
  simp [activeConstructedLevel]

/-- Active constructed gates take the all-`alpha` value at the origin. -/
theorem activeConstructedGate_zero_of_active {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) {x : FormalVar L k}
    (hx : IsActiveVar θ x) :
    activeConstructedGate (r := r) θ w v x 0 = (alpha r : ℂ) := by
  rw [activeConstructedGate_eq_of_active θ w v hx 0,
    activeConstructedLevel_zero (r := r) θ w v x]
  simpa [alpha, csig] using TransformerIdentifiability.NLayer.csig_ofReal (logScale r)

/-- The layer-recursive constructed levels and gates are real-valued on the nonnegative
real axis. -/
theorem activeConstructedLevel_gate_real_on_nonnegativeRealAxis {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) :
    ∀ x : FormalVar L k,
      IsRealValuedOn (activeConstructedLevel (r := r) θ w v x) nonnegativeRealAxis ∧
      IsRealValuedOn (activeConstructedGate (r := r) θ w v x) nonnegativeRealAxis := by
  classical
  let P : FormalVar L k → Prop := fun x =>
    IsRealValuedOn (activeConstructedLevel (r := r) θ w v x) nonnegativeRealAxis ∧
      IsRealValuedOn (activeConstructedGate (r := r) θ w v x) nonnegativeRealAxis
  change ∀ x : FormalVar L k, P x
  intro x
  refine (measure (fun x : FormalVar L k => x.1.1)).wf.induction (C := P) x ?_
  intro x ih
  have hlevel :
      IsRealValuedOn (activeConstructedLevel (r := r) θ w v x) nonnegativeRealAxis := by
    intro τ hτ
    rcases hτ with ⟨t, ht, rfl⟩
    have hη :
        ∀ y : FormalVar L k,
          ∃ u : ℝ,
            (if hy : y.1.1 < x.1.1 then
                activeConstructedGate (r := r) θ w v y (t : ℂ)
              else 0) = (u : ℂ) := by
      intro y
      by_cases hy : y.1.1 < x.1.1
      · rcases (ih y (by simpa [measure] using hy)).2 (t : ℂ) ⟨t, ht, rfl⟩ with
          ⟨u, hu⟩
        exact ⟨u, by simpa [hy] using hu⟩
      · exact ⟨0, by simp [hy]⟩
    rcases evalFormalPolyComplex_real_of_real_assignment
        (formalSlope θ w v x.1 x.2) hη with ⟨s, hs⟩
    refine ⟨t * s + logScale r, ?_⟩
    calc
      activeConstructedLevel (r := r) θ w v x (t : ℂ)
          = (t : ℂ) * (s : ℂ) + (logScale r : ℂ) := by
              rw [activeConstructedLevel, hs]
      _ = ((t * s + logScale r : ℝ) : ℂ) := by
              norm_num
  have hgate :
      IsRealValuedOn (activeConstructedGate (r := r) θ w v x) nonnegativeRealAxis := by
    intro τ hτ
    by_cases hx : IsActiveVar θ x
    · rcases hlevel τ hτ with ⟨u, hu⟩
      refine ⟨sig u, ?_⟩
      rw [activeConstructedGate_eq_of_active θ w v hx τ, hu]
      simpa [csig] using TransformerIdentifiability.NLayer.csig_ofReal u
    · refine ⟨0, ?_⟩
      simpa using activeConstructedGate_eq_zero_of_inactive (r := r) θ w v hx τ
  exact ⟨hlevel, hgate⟩

theorem activeConstructedLevel_real_on_nonnegativeRealAxis {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (x : FormalVar L k) :
    IsRealValuedOn (activeConstructedLevel (r := r) θ w v x) nonnegativeRealAxis :=
  (activeConstructedLevel_gate_real_on_nonnegativeRealAxis (r := r) θ w v x).1

theorem activeConstructedGate_real_on_nonnegativeRealAxis {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (x : FormalVar L k) :
    IsRealValuedOn (activeConstructedGate (r := r) θ w v x) nonnegativeRealAxis :=
  (activeConstructedLevel_gate_real_on_nonnegativeRealAxis (r := r) θ w v x).2

/-- Candidate final observable obtained by evaluating the formal output vector at the
constructed active gates. -/
noncomputable def activeConstructedObservable {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) : ℂ → ComplexVec d :=
  fun τ => evalFormalVecComplex
    (fun x => activeConstructedGate (r := r) θ w v x τ)
    (formalV θ w v L le_rfl)

/-- Each coordinate of the constructed final observable is real-valued on the
nonnegative real axis. -/
theorem activeConstructedObservable_real_on_nonnegativeRealAxis {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) :
    ∀ i : Fin d,
      IsRealValuedOn
        (fun τ => activeConstructedObservable (r := r) θ w v τ i)
        nonnegativeRealAxis := by
  intro i τ hτ
  simpa [activeConstructedObservable, evalFormalVecComplex] using
    evalFormalPolyComplex_real_of_real_assignment
      ((formalV θ w v L le_rfl) i)
      (fun x =>
        activeConstructedGate_real_on_nonnegativeRealAxis (r := r) θ w v x τ hτ)

/-- Concrete recursive candidate for the active stratification data.  Its domains and
strata are generated by the recursive `Ω/S` constructor, while its levels and gates use
the layer-recursive continuation above. -/
noncomputable def activeConstructedStratificationData {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) : ActiveStratificationData L k d :=
  activeStratificationDataOfFunctions θ
    (activeConstructedLevel (r := r) θ w v)
    (activeConstructedGate (r := r) θ w v)
    (activeConstructedObservable (r := r) θ w v)

/-- The concrete `H/s/Ω/S` candidate proves the recursion-only part of the strong
stratification interface. -/
theorem activeConstructedStratificationData_recursiveSkeleton {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) :
    ActiveHeadRecursiveSkeleton θ (activeConstructedStratificationData (r := r) θ w v) := by
  exact activeStratificationDataOfFunctions_recursiveSkeleton θ
    (activeConstructedLevel (r := r) θ w v)
    (activeConstructedGate (r := r) θ w v)
    (activeConstructedObservable (r := r) θ w v)

/-- The concrete constructed recursive domains contain the nonnegative real axis at
every depth. -/
theorem activeConstructedStratificationData_nonnegativeRealAxis_subset_omega
    {r L k d : Nat} (θ : Params L k d) (w v : Vec d) :
    ∀ n : Nat, n ≤ L →
      nonnegativeRealAxis ⊆
        (activeConstructedStratificationData (r := r) θ w v).Omega n := by
  intro n hn
  simpa [activeConstructedStratificationData] using
    activeStratificationDataOfFunctions_nonnegativeRealAxis_subset_omega_of_level_real
      θ
      (activeConstructedLevel (r := r) θ w v)
      (activeConstructedGate (r := r) θ w v)
      (activeConstructedObservable (r := r) θ w v)
      (activeConstructedLevel_real_on_nonnegativeRealAxis (r := r) θ w v)
      n hn

/-- The concrete constructed recursive domains contain the positive real axis at every
depth. -/
theorem activeConstructedStratificationData_positiveRealAxis_subset_omega
    {r L k d : Nat} (θ : Params L k d) (w v : Vec d) :
    ∀ n : Nat, n ≤ L →
      positiveRealAxis ⊆
        (activeConstructedStratificationData (r := r) θ w v).Omega n := by
  intro n hn
  exact positiveRealAxis_subset_of_nonnegativeRealAxis_subset
    (activeConstructedStratificationData_nonnegativeRealAxis_subset_omega
      (r := r) θ w v n hn)

/-- Partial existential construction: the concrete recursive `H/s/Ω/S` candidate exists
and satisfies the recursion-only subset of the strong stratification interface. -/
theorem exists_activeHeadRecursiveSkeleton {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) :
    ∃ D : ActiveStratificationData L k d, ActiveHeadRecursiveSkeleton θ D :=
  ⟨activeConstructedStratificationData (r := r) θ w v,
    activeConstructedStratificationData_recursiveSkeleton (r := r) θ w v⟩

/-- A level function taking the real value `logScale r` at `0` cannot be constant with
value in the sigmoid pole set on any domain containing `0`. -/
theorem level_not_constant_pole_of_level_zero {r L k d : Nat}
    (D : ActiveStratificationData L k d) {l : Fin L} {a : Fin k}
    (h0Ω : (0 : ℂ) ∈ D.Omega l.1)
    (hzero : D.level (l, a) 0 = (logScale r : ℂ)) :
    ∀ c : ℂ, c ∈ Pi →
      ¬ Set.EqOn (D.level (l, a)) (fun _ : ℂ => c) (D.Omega l.1) := by
  intro c hcPi hconst
  have hc : (logScale r : ℂ) = c := by
    rw [← hzero]
    exact hconst h0Ω
  have hlogPi : (logScale r : ℂ) ∈ Pi := by
    simpa [hc.symm] using hcPi
  exact ofReal_notMem_Pi (logScale r) hlogPi

/-- Layerwise closed-discreteness follows from holomorphic active level functions and
their common non-pole value at the origin.  This packages the geometric proof step used in
the recursive singular-stratification construction. -/
theorem reducedStratumAt_closedDiscrete_of_level_zero {r L k d : Nat}
    (θ : Params L k d) (D : ActiveStratificationData L k d) (l : Fin L)
    (hΩ : PlaneDomain (D.Omega l.1))
    (h0Ω : (0 : ℂ) ∈ D.Omega l.1)
    (hlevel_holomorphic :
      ∀ a : Fin k, a ∈ activeHeads θ l →
        AnalyticOnNhd ℂ (D.level (l, a)) (D.Omega l.1))
    (hlevel_zero :
      ∀ a : Fin k, a ∈ activeHeads θ l →
        D.level (l, a) 0 = (logScale r : ℂ)) :
    ClosedDiscreteIn (reducedStratumAt θ D l) (D.Omega l.1) := by
  refine reducedStratumAt_closedDiscrete_of_level_data θ D l hΩ hlevel_holomorphic ?_
  intro a ha c hcPi
  exact level_not_constant_pole_of_level_zero (r := r) D h0Ω
    (hlevel_zero a ha) c hcPi

/-- Version of `reducedStratumAt_closedDiscrete_of_level_zero` for an already chosen
stratum field. -/
theorem stratum_closedDiscrete_of_level_zero_data {r L k d : Nat}
    (θ : Params L k d) (D : ActiveStratificationData L k d) (l : Fin L)
    (hstratum : D.stratum l.1 = reducedStratumAt θ D l)
    (hΩ : PlaneDomain (D.Omega l.1))
    (h0Ω : (0 : ℂ) ∈ D.Omega l.1)
    (hlevel_holomorphic :
      ∀ a : Fin k, a ∈ activeHeads θ l →
        AnalyticOnNhd ℂ (D.level (l, a)) (D.Omega l.1))
    (hlevel_zero :
      ∀ a : Fin k, a ∈ activeHeads θ l →
        D.level (l, a) 0 = (logScale r : ℂ)) :
    ClosedDiscreteIn (D.stratum l.1) (D.Omega l.1) := by
  rw [hstratum]
  exact reducedStratumAt_closedDiscrete_of_level_zero (r := r) θ D l hΩ h0Ω
    hlevel_holomorphic hlevel_zero

/-- Holomorphic level data and the recursive domain update imply the stratified
closed-discrete tower needed for the stratified-accumulation lemma. -/
theorem strataSystem_of_level_zero_axis_data {r L k d : Nat}
    (θ : Params L k d) (D : ActiveStratificationData L k d)
    (hzero : D.Omega 0 = Set.univ)
    (hsucc : ∀ l : Fin L, D.Omega (l.1 + 1) = D.Omega l.1 \ D.stratum l.1)
    (hdomain : ∀ n : Nat, n ≤ L → PlaneDomain (D.Omega n))
    (haxis : ∀ n : Nat, n ≤ L → nonnegativeRealAxis ⊆ D.Omega n)
    (hstratum : ∀ l : Fin L, D.stratum l.1 = reducedStratumAt θ D l)
    (hlevel_holomorphic : ∀ l : Fin L, ∀ a : Fin k, a ∈ activeHeads θ l →
      AnalyticOnNhd ℂ (D.level (l, a)) (D.Omega l.1))
    (hlevel_zero : ∀ l : Fin L, ∀ a : Fin k, a ∈ activeHeads θ l →
      D.level (l, a) 0 = (logScale r : ℂ)) :
    StrataSystem D.stratum L := by
  refine strataSystem_of_closedDiscreteIn ?_
  intro j hj
  let l : Fin L := ⟨j, hj⟩
  have hjle : j ≤ L := Nat.le_of_lt hj
  have hΩeq : D.Omega j = (partialUnion D.stratum j)ᶜ :=
    omega_eq_partialUnion_compl_of_omega_succ D hzero hsucc j hjle
  have hCD : ClosedDiscreteIn (D.stratum j) (D.Omega j) := by
    simpa [l] using
      stratum_closedDiscrete_of_level_zero_data (r := r) θ D l (hstratum l)
        (hdomain j hjle)
        (zero_mem_of_nonnegativeRealAxis_subset (haxis j hjle))
        (fun a ha => hlevel_holomorphic l a ha)
        (fun a ha => hlevel_zero l a ha)
  simpa [hΩeq] using hCD

/-- Complex gate assignment used when evaluating formal streams: inactive coordinates are
zeroed, while active coordinates use the continued gates. -/
noncomputable def activeComplexGateAssignment {L k d : Nat} (θ : Params L k d)
    (D : ActiveStratificationData L k d) (τ : ℂ) : FormalVar L k → ℂ :=
  by
    classical
    exact fun x => if IsActiveVar θ x then D.gate x τ else 0

theorem activeComplexGateAssignment_eq_of_active {L k d : Nat}
    (θ : Params L k d) (D : ActiveStratificationData L k d) (τ : ℂ)
    {l : Fin L} {a : Fin k} (ha : a ∈ activeHeads θ l) :
    activeComplexGateAssignment θ D τ (l, a) = D.gate (l, a) τ := by
  simp [activeComplexGateAssignment, IsActiveVar, (mem_activeHeads θ l a).1 ha]

theorem activeComplexGateAssignment_eq_zero_of_inactive {L k d : Nat}
    (θ : Params L k d) (D : ActiveStratificationData L k d) (τ : ℂ)
    {l : Fin L} {a : Fin k} (ha : a ∉ activeHeads θ l) :
    activeComplexGateAssignment θ D τ (l, a) = 0 := by
  have hnot : ¬ IsActiveVar θ (l, a) := by
    simpa using ha
  simp [activeComplexGateAssignment, hnot]

/-- For the concrete constructed data, the active complex assignment is exactly the
constructed gate function; inactive coordinates agree because constructed gates are zero
there. -/
theorem activeComplexGateAssignment_activeConstructedStratificationData_eq
    {r L k d : Nat} (θ : Params L k d) (w v : Vec d) (τ : ℂ) :
    activeComplexGateAssignment θ
        (activeConstructedStratificationData (r := r) θ w v) τ =
      fun x => activeConstructedGate (r := r) θ w v x τ := by
  funext x
  by_cases hx : IsActiveVar θ x
  · simp [activeComplexGateAssignment, activeConstructedStratificationData,
      activeStratificationDataOfFunctions, hx]
  · simp [activeComplexGateAssignment, hx,
      activeConstructedGate_eq_zero_of_inactive (r := r) θ w v hx τ]

/-- The constructed level can be rewritten using the active complex gate assignment of
the concrete constructed data.  The only difference from the defining formula is that
same-layer and later active coordinates are present in the assignment; formal slopes are
already invariant under changes to non-prior active variables. -/
theorem activeConstructedLevel_eq_activeComplexGateAssignment {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (x : FormalVar L k) (τ : ℂ) :
    activeConstructedLevel (r := r) θ w v x τ =
      τ * evalFormalPolyComplex
          (activeComplexGateAssignment θ
            (activeConstructedStratificationData (r := r) θ w v) τ)
          (formalSlope θ w v x.1 x.2) + (logScale r : ℂ) := by
  classical
  let ηPrior : FormalVar L k → ℂ :=
    fun y => if _hy : y.1.1 < x.1.1 then
      activeConstructedGate (r := r) θ w v y τ else 0
  have hprior :
      evalFormalPolyComplex ηPrior (formalSlope θ w v x.1 x.2) =
        evalFormalPolyComplex
          (activeComplexGateAssignment θ
            (activeConstructedStratificationData (r := r) θ w v) τ)
          (formalSlope θ w v x.1 x.2) := by
    refine evalFormalPolyComplex_formalSlope_eq_of_eq_on_active (θ := θ)
      ηPrior
      (activeComplexGateAssignment θ
        (activeConstructedStratificationData (r := r) θ w v) τ)
      w v x.1 x.2 ?_
    intro l' a' hl' _ha'
    rw [activeComplexGateAssignment_activeConstructedStratificationData_eq
      (r := r) θ w v τ]
    dsimp [ηPrior]
    rw [if_pos hl']
  change
    τ * evalFormalPolyComplex ηPrior (formalSlope θ w v x.1 x.2) +
        (logScale r : ℂ) =
      τ * evalFormalPolyComplex
          (activeComplexGateAssignment θ
            (activeConstructedStratificationData (r := r) θ w v) τ)
          (formalSlope θ w v x.1 x.2) + (logScale r : ℂ)
  rw [hprior]

/-- On positive real inputs, the recursively constructed levels and active gates agree
with the actual probe-recursion slopes and gates. -/
theorem activeConstructedLevel_gate_positive_real_eq_actual {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) :
    ∀ x : FormalVar L k,
      (∀ τ : ℝ, 0 < τ →
        activeConstructedLevel (r := r) θ w v x (τ : ℂ) =
          ((τ * actualProbeSlope r θ w v τ x.1 x.2 + logScale r : ℝ) : ℂ)) ∧
      (IsActiveVar θ x →
        ∀ τ : ℝ, 0 < τ →
          activeConstructedGate (r := r) θ w v x (τ : ℂ) =
            (actualProbeGate r θ w v τ x.1 x.2 : ℂ)) := by
  classical
  let P : FormalVar L k → Prop := fun x =>
    (∀ τ : ℝ, 0 < τ →
      activeConstructedLevel (r := r) θ w v x (τ : ℂ) =
        ((τ * actualProbeSlope r θ w v τ x.1 x.2 + logScale r : ℝ) : ℂ)) ∧
    (IsActiveVar θ x →
      ∀ τ : ℝ, 0 < τ →
        activeConstructedGate (r := r) θ w v x (τ : ℂ) =
          (actualProbeGate r θ w v τ x.1 x.2 : ℂ))
  change ∀ x : FormalVar L k, P x
  intro x
  refine (measure (fun x : FormalVar L k => x.1.1)).wf.induction (C := P) x ?_
  intro x ih
  have hlevelAll :
      ∀ τ : ℝ, 0 < τ →
        activeConstructedLevel (r := r) θ w v x (τ : ℂ) =
          ((τ * actualProbeSlope r θ w v τ x.1 x.2 + logScale r : ℝ) : ℂ) := by
    intro τ hτ
    let ηPrior : FormalVar L k → ℂ :=
      fun y => if _hy : y.1.1 < x.1.1 then
        activeConstructedGate (r := r) θ w v y (τ : ℂ) else 0
    let ρActual : FormalVar L k → ℝ := actualProbeGateAssignment r θ w v τ
    have hprior :
        evalFormalPolyComplex ηPrior (formalSlope θ w v x.1 x.2) =
          evalFormalPolyComplex (fun y => (ρActual y : ℂ))
            (formalSlope θ w v x.1 x.2) := by
      refine evalFormalPolyComplex_formalSlope_eq_of_eq_on_active (θ := θ)
        ηPrior (fun y => (ρActual y : ℂ)) w v x.1 x.2 ?_
      intro l' a' hl' ha'
      have hactive : IsActiveVar θ (l', a') := by
        simpa [IsActiveVar] using (mem_activeHeads θ l' a').1 ha'
      have hgate :=
        (ih (l', a') (by simpa [measure] using hl')).2 hactive τ hτ
      dsimp [ηPrior, ρActual, actualProbeGateAssignment]
      rw [if_pos hl']
      simpa using hgate
    have hreal :
        evalFormalPolyComplex (fun y => (ρActual y : ℂ))
            (formalSlope θ w v x.1 x.2) =
          (MvPolynomial.eval ρActual (formalSlope θ w v x.1 x.2) : ℂ) :=
      evalFormalPolyComplex_ofReal ρActual (formalSlope θ w v x.1 x.2)
    have hslope :
        MvPolynomial.eval ρActual (formalSlope θ w v x.1 x.2) =
          actualProbeSlope r θ w v τ x.1 x.2 := by
      simpa [ρActual] using
        eval_formalSlope_actualProbeGateAssignment r θ w v τ x.1 x.2
    have hη :
        evalFormalPolyComplex ηPrior (formalSlope θ w v x.1 x.2) =
          (actualProbeSlope r θ w v τ x.1 x.2 : ℂ) := by
      rw [hprior, hreal, hslope]
    calc
      activeConstructedLevel (r := r) θ w v x (τ : ℂ)
          = (τ : ℂ) *
              evalFormalPolyComplex ηPrior (formalSlope θ w v x.1 x.2) +
              (logScale r : ℂ) := by
                rfl
      _ = (τ : ℂ) * (actualProbeSlope r θ w v τ x.1 x.2 : ℂ) +
              (logScale r : ℂ) := by
                rw [hη]
      _ = ((τ * actualProbeSlope r θ w v τ x.1 x.2 + logScale r : ℝ) : ℂ) := by
                norm_num
  constructor
  · exact hlevelAll
  · intro hx τ hτ
    have hlevel := hlevelAll τ hτ
    rw [activeConstructedGate_eq_of_active θ w v hx (τ : ℂ), hlevel]
    rw [actualProbeGate_eq_sig]
    simpa [csig] using TransformerIdentifiability.NLayer.csig_ofReal
      (τ * actualProbeSlope r θ w v τ x.1 x.2 + logScale r)

theorem activeConstructedLevel_positive_real_eq_actual {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (x : FormalVar L k)
    (τ : ℝ) (hτ : 0 < τ) :
    activeConstructedLevel (r := r) θ w v x (τ : ℂ) =
      ((τ * actualProbeSlope r θ w v τ x.1 x.2 + logScale r : ℝ) : ℂ) :=
  (activeConstructedLevel_gate_positive_real_eq_actual (r := r) θ w v x).1 τ hτ

theorem activeConstructedGate_positive_real_eq_actual {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) {l : Fin L} {a : Fin k}
    (ha : a ∈ activeHeads θ l) (τ : ℝ) (hτ : 0 < τ) :
    activeConstructedGate (r := r) θ w v (l, a) (τ : ℂ) =
      (actualProbeGate r θ w v τ l a : ℂ) := by
  have hactive : IsActiveVar θ (l, a) := by
    simpa [IsActiveVar] using (mem_activeHeads θ l a).1 ha
  exact (activeConstructedLevel_gate_positive_real_eq_actual (r := r) θ w v (l, a)).2
    hactive τ hτ

/-- The constructed observable agrees with the closed probe output on the positive real
axis. -/
theorem activeConstructedObservable_positive_real_eq_probeOutput {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (τ : ℝ) (hτ : 0 < τ) :
    activeConstructedObservable (r := r) θ w v (τ : ℂ) =
      realVecToComplex (probeOutput r θ w v τ) := by
  classical
  let ηConstructed : FormalVar L k → ℂ :=
    fun x => activeConstructedGate (r := r) θ w v x (τ : ℂ)
  let ρActual : FormalVar L k → ℝ := actualProbeGateAssignment r θ w v τ
  have hactive :
      ∀ (l : Fin L) (a : Fin k), l.1 < L → a ∈ activeHeads θ l →
        ηConstructed (l, a) = (ρActual (l, a) : ℂ) := by
    intro l a _hl ha
    simpa [ηConstructed, ρActual, actualProbeGateAssignment] using
      activeConstructedGate_positive_real_eq_actual (r := r) θ w v ha τ hτ
  have hformalPoint :
      evalFormalVecComplex ηConstructed (formalPoint θ w v L le_rfl).2 =
        evalFormalVecComplex (fun y => (ρActual y : ℂ))
          (formalPoint θ w v L le_rfl).2 :=
    (eval_formalPointComplex_eq_of_eq_on_active (θ := θ)
      ηConstructed (fun y => (ρActual y : ℂ)) w v L le_rfl hactive).2
  have hformal :
      evalFormalVecComplex ηConstructed (formalV θ w v L le_rfl) =
        evalFormalVecComplex (fun y => (ρActual y : ℂ))
          (formalV θ w v L le_rfl) := by
    simpa [formalV] using hformalPoint
  have hreal :
      evalFormalVecComplex (fun y => (ρActual y : ℂ))
          (formalV θ w v L le_rfl) =
        realVecToComplex
          (evalFormalVec ρActual (formalV θ w v L le_rfl)) :=
    evalFormalVecComplex_ofReal ρActual (formalV θ w v L le_rfl)
  have hactual :
      evalFormalVec ρActual (formalV θ w v L le_rfl) =
        (actualProbePoint r θ w v L le_rfl τ).2 := by
    simpa [ρActual, formalV] using
      (eval_formalPoint_actualProbeGateAssignment r θ w v τ L le_rfl).2
  calc
    activeConstructedObservable (r := r) θ w v (τ : ℂ)
        = evalFormalVecComplex ηConstructed (formalV θ w v L le_rfl) := by
            rfl
    _ = evalFormalVecComplex (fun y => (ρActual y : ℂ))
          (formalV θ w v L le_rfl) := hformal
    _ = realVecToComplex
          (evalFormalVec ρActual (formalV θ w v L le_rfl)) := hreal
    _ = realVecToComplex (actualProbePoint r θ w v L le_rfl τ).2 := by
          rw [hactual]
    _ = realVecToComplex (probeOutput r θ w v τ) := by
          rw [actualProbePoint_snd_eq_probeOutput]

/-- Constructed data satisfies the strong level formula field. -/
theorem activeConstructedStratificationData_level_formula {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) :
    ∀ l : Fin L, ∀ a : Fin k, a ∈ activeHeads θ l →
      Set.EqOn
        ((activeConstructedStratificationData (r := r) θ w v).level (l, a))
        (fun τ : ℂ =>
          τ * evalFormalPolyComplex
            (activeComplexGateAssignment θ
              (activeConstructedStratificationData (r := r) θ w v) τ)
            (formalSlope θ w v l a) + (logScale r : ℂ))
        ((activeConstructedStratificationData (r := r) θ w v).Omega l.1) := by
  intro l a _ha τ _hτ
  simpa [activeConstructedStratificationData, activeStratificationDataOfFunctions] using
    activeConstructedLevel_eq_activeComplexGateAssignment (r := r) θ w v (l, a) τ

/-- Constructed data satisfies the strong gate formula field. -/
theorem activeConstructedStratificationData_gate_formula {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) :
    ∀ l : Fin L, ∀ a : Fin k, a ∈ activeHeads θ l →
      Set.EqOn
        ((activeConstructedStratificationData (r := r) θ w v).gate (l, a))
        (fun τ : ℂ =>
          csig ((activeConstructedStratificationData (r := r) θ w v).level (l, a) τ))
        ((activeConstructedStratificationData (r := r) θ w v).Omega (l.1 + 1)) := by
  intro l a ha τ _hτ
  have hactive : IsActiveVar θ (l, a) := by
    simpa [IsActiveVar] using (mem_activeHeads θ l a).1 ha
  simpa [activeConstructedStratificationData, activeStratificationDataOfFunctions] using
    activeConstructedGate_eq_of_active (r := r) θ w v hactive τ

/-- Constructed data satisfies the strong observable formula field. -/
theorem activeConstructedStratificationData_observable_formula {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) :
    Set.EqOn
      (activeConstructedStratificationData (r := r) θ w v).observable
      (fun τ : ℂ =>
        evalFormalVecComplex
          (activeComplexGateAssignment θ
            (activeConstructedStratificationData (r := r) θ w v) τ)
          (formalV θ w v L le_rfl))
      ((activeConstructedStratificationData (r := r) θ w v).Omega L) := by
  intro τ _hτ
  change
    evalFormalVecComplex
        (fun x => activeConstructedGate (r := r) θ w v x τ)
        (formalV θ w v L le_rfl) =
      evalFormalVecComplex
        (activeComplexGateAssignment θ
          (activeConstructedStratificationData (r := r) θ w v) τ)
        (formalV θ w v L le_rfl)
  rw [activeComplexGateAssignment_activeConstructedStratificationData_eq]

theorem activeConstructedStratificationData_level_zero {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) :
    ∀ l : Fin L, ∀ a : Fin k, a ∈ activeHeads θ l →
      (activeConstructedStratificationData (r := r) θ w v).level (l, a) 0 =
        (logScale r : ℂ) := by
  intro l a _ha
  simpa [activeConstructedStratificationData, activeStratificationDataOfFunctions] using
    activeConstructedLevel_zero (r := r) θ w v (l, a)

theorem activeConstructedStratificationData_gate_zero {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) :
    ∀ l : Fin L, ∀ a : Fin k, a ∈ activeHeads θ l →
      (activeConstructedStratificationData (r := r) θ w v).gate (l, a) 0 =
        (alpha r : ℂ) := by
  intro l a ha
  have hactive : IsActiveVar θ (l, a) := by
    simpa [IsActiveVar] using (mem_activeHeads θ l a).1 ha
  simpa [activeConstructedStratificationData, activeStratificationDataOfFunctions] using
    activeConstructedGate_zero_of_active (r := r) θ w v hactive

theorem activeConstructedStratificationData_level_real_on_nonnegativeRealAxis
    {r L k d : Nat} (θ : Params L k d) (w v : Vec d) :
    ∀ l : Fin L, ∀ a : Fin k, a ∈ activeHeads θ l →
      IsRealValuedOn
        ((activeConstructedStratificationData (r := r) θ w v).level (l, a))
        nonnegativeRealAxis := by
  intro l a _ha
  simpa [activeConstructedStratificationData, activeStratificationDataOfFunctions] using
    activeConstructedLevel_real_on_nonnegativeRealAxis (r := r) θ w v (l, a)

theorem activeConstructedStratificationData_gate_real_on_nonnegativeRealAxis
    {r L k d : Nat} (θ : Params L k d) (w v : Vec d) :
    ∀ l : Fin L, ∀ a : Fin k, a ∈ activeHeads θ l →
      IsRealValuedOn
        ((activeConstructedStratificationData (r := r) θ w v).gate (l, a))
        nonnegativeRealAxis := by
  intro l a _ha
  simpa [activeConstructedStratificationData, activeStratificationDataOfFunctions] using
    activeConstructedGate_real_on_nonnegativeRealAxis (r := r) θ w v (l, a)

theorem activeConstructedStratificationData_level_not_constant_pole
    {r L k d : Nat} (θ : Params L k d) (w v : Vec d) :
    ∀ l : Fin L, ∀ a : Fin k, a ∈ activeHeads θ l →
      ∀ c : ℂ, c ∈ Pi →
        ¬ Set.EqOn
          ((activeConstructedStratificationData (r := r) θ w v).level (l, a))
          (fun _ : ℂ => c)
          ((activeConstructedStratificationData (r := r) θ w v).Omega l.1) := by
  intro l a ha c hcPi
  exact level_not_constant_pole_of_level_zero (r := r)
    (activeConstructedStratificationData (r := r) θ w v)
    (zero_mem_of_nonnegativeRealAxis_subset
      (activeConstructedStratificationData_nonnegativeRealAxis_subset_omega
        (r := r) θ w v l.1 (Nat.le_of_lt l.2)))
    (activeConstructedStratificationData_level_zero (r := r) θ w v l a ha)
    c hcPi

theorem activeConstructedStratificationData_positive_level_eq_actual
    {r L k d : Nat} (θ : Params L k d) (w v : Vec d) :
    ∀ l : Fin L, ∀ a : Fin k, a ∈ activeHeads θ l →
      ∀ τ : ℝ, 0 < τ →
        (activeConstructedStratificationData (r := r) θ w v).level (l, a) (τ : ℂ) =
          ((τ * actualProbeSlope r θ w v τ l a + logScale r : ℝ) : ℂ) := by
  intro l a _ha τ hτ
  simpa [activeConstructedStratificationData, activeStratificationDataOfFunctions] using
    activeConstructedLevel_positive_real_eq_actual (r := r) θ w v (l, a) τ hτ

theorem activeConstructedStratificationData_positive_gate_eq_actual
    {r L k d : Nat} (θ : Params L k d) (w v : Vec d) :
    ∀ l : Fin L, ∀ a : Fin k, a ∈ activeHeads θ l →
      ∀ τ : ℝ, 0 < τ →
        (activeConstructedStratificationData (r := r) θ w v).gate (l, a) (τ : ℂ) =
          (actualProbeGate r θ w v τ l a : ℂ) := by
  intro l a ha τ hτ
  simpa [activeConstructedStratificationData, activeStratificationDataOfFunctions] using
    activeConstructedGate_positive_real_eq_actual (r := r) θ w v ha τ hτ

theorem activeConstructedStratificationData_observable_positive_real_eq_probeOutput
    {r L k d : Nat} (θ : Params L k d) (w v : Vec d) :
    ∀ τ : ℝ, 0 < τ →
      (activeConstructedStratificationData (r := r) θ w v).observable (τ : ℂ) =
        realVecToComplex (probeOutput r θ w v τ) := by
  intro τ hτ
  simpa [activeConstructedStratificationData, activeStratificationDataOfFunctions] using
    activeConstructedObservable_positive_real_eq_probeOutput (r := r) θ w v τ hτ

/-- Constructed levels are holomorphic on any domain where all prior constructed gates
are holomorphic.  This is the local induction step for the level functions. -/
theorem activeConstructedLevel_analyticOnNhd_of_prior_gate_analytic
    {r L k d : Nat} (θ : Params L k d) (w v : Vec d)
    (x : FormalVar L k) {U : Set ℂ}
    (hgate : ∀ y : FormalVar L k, y.1 < x.1 →
      AnalyticOnNhd ℂ (activeConstructedGate (r := r) θ w v y) U) :
    AnalyticOnNhd ℂ (activeConstructedLevel (r := r) θ w v x) U := by
  classical
  let η : FormalVar L k → ℂ → ℂ := fun y τ =>
    if _hy : y.1 < x.1 then activeConstructedGate (r := r) θ w v y τ else 0
  have hη : ∀ y : FormalVar L k, AnalyticOnNhd ℂ (η y) U := by
    intro y
    by_cases hy : y.1 < x.1
    · simpa [η, hy] using hgate y hy
    · simpa [η, hy] using
        (analyticOnNhd_const (𝕜 := ℂ) (v := (0 : ℂ)) (s := U))
  have hpoly :
      AnalyticOnNhd ℂ
        (fun τ => evalFormalPolyComplex (fun y => η y τ)
          (formalSlope θ w v x.1 x.2)) U :=
    evalFormalPolyComplex_analyticOnNhd (formalSlope θ w v x.1 x.2) hη
  have hid : AnalyticOnNhd ℂ (fun τ : ℂ => τ) U := by
    intro τ _hτ
    simpa using (analyticAt_id : AnalyticAt ℂ (fun τ : ℂ => τ) τ)
  have hconst :
      AnalyticOnNhd ℂ (fun _ : ℂ => (logScale r : ℂ)) U :=
    analyticOnNhd_const (𝕜 := ℂ) (v := (logScale r : ℂ)) (s := U)
  change
    AnalyticOnNhd ℂ
      (fun τ : ℂ =>
        τ * evalFormalPolyComplex (fun y => η y τ)
          (formalSlope θ w v x.1 x.2) + (logScale r : ℂ)) U
  exact (hid.mul hpoly).add hconst

/-- Constructed active gates are holomorphic on any domain where their level is
holomorphic and avoids the sigmoid pole set. -/
theorem activeConstructedGate_analyticOnNhd_of_level_analytic_of_avoids_Pi
    {r L k d : Nat} (θ : Params L k d) (w v : Vec d)
    {x : FormalVar L k} (hx : IsActiveVar θ x) {U : Set ℂ}
    (hlevel : AnalyticOnNhd ℂ (activeConstructedLevel (r := r) θ w v x) U)
    (havoid : ∀ τ ∈ U, activeConstructedLevel (r := r) θ w v x τ ∉ Pi) :
    AnalyticOnNhd ℂ (activeConstructedGate (r := r) θ w v x) U := by
  have hcsig :
      AnalyticOnNhd ℂ csig
        ((activeConstructedLevel (r := r) θ w v x) '' U) := by
    intro z hz
    rcases hz with ⟨τ, hτ, rfl⟩
    exact csig_analyticAt_of_notMem_Pi (havoid τ hτ)
  have hcomp := hcsig.comp' hlevel
  convert hcomp using 1
  ext τ
  simp [Function.comp, activeConstructedGate_eq_of_active (r := r) θ w v hx τ]

/-- The constructed observable is coordinatewise holomorphic on any domain where all
constructed gate coordinates are holomorphic. -/
theorem activeConstructedObservable_analyticOnNhd_of_gate_analytic
    {r L k d : Nat} (θ : Params L k d) (w v : Vec d) {U : Set ℂ}
    (hgate : ∀ x : FormalVar L k,
      AnalyticOnNhd ℂ (activeConstructedGate (r := r) θ w v x) U) :
    ∀ i : Fin d,
      AnalyticOnNhd ℂ
        (fun τ => activeConstructedObservable (r := r) θ w v τ i) U := by
  intro i
  simpa [activeConstructedObservable] using
    (evalFormalVecComplex_analyticOnNhd (formalV θ w v L le_rfl)
      (η := fun x τ => activeConstructedGate (r := r) θ w v x τ) hgate i)

/-- Membership in the next recursive domain means every active level at the current
layer avoids the sigmoid pole set. -/
theorem activeConstructedStratificationData_level_notMem_Pi_on_nextOmega
    {r L k d : Nat} (θ : Params L k d) (w v : Vec d)
    (l : Fin L) {a : Fin k} (ha : a ∈ activeHeads θ l) {τ : ℂ}
    (hτ : τ ∈ (activeConstructedStratificationData (r := r) θ w v).Omega (l.1 + 1)) :
    (activeConstructedStratificationData (r := r) θ w v).level (l, a) τ ∉ Pi := by
  let D : ActiveStratificationData L k d :=
    activeConstructedStratificationData (r := r) θ w v
  change D.level (l, a) τ ∉ Pi
  change τ ∈ D.Omega (l.1 + 1) at hτ
  intro hPi
  have hskel : ActiveHeadRecursiveSkeleton θ D := by
    simpa [D] using activeConstructedStratificationData_recursiveSkeleton (r := r) θ w v
  have hτdiff : τ ∈ D.Omega l.1 \ D.stratum l.1 := by
    simpa [hskel.omega_succ l] using hτ
  have hτS : τ ∈ D.stratum l.1 := by
    rw [hskel.stratum_eq l]
    exact ⟨a, ha, hτdiff.1, hPi⟩
  exact hτdiff.2 hτS

/-- Analyticity on a larger set restricts to any subset. -/
theorem analyticOnNhd_mono {F : ℂ → ℂ} {U V : Set ℂ}
    (hF : AnalyticOnNhd ℂ F U) (hVU : V ⊆ U) :
    AnalyticOnNhd ℂ F V := by
  intro τ hτ
  exact hF τ (hVU hτ)

/-- Recursive domains of the constructed data are antitone in the layer index. -/
theorem activeConstructedStratificationData_omega_subset_of_le
    {r L k d : Nat} (θ : Params L k d) (w v : Vec d)
    {m n : Nat} (hmn : m ≤ n) (hn : n ≤ L) :
    (activeConstructedStratificationData (r := r) θ w v).Omega n ⊆
      (activeConstructedStratificationData (r := r) θ w v).Omega m := by
  let D : ActiveStratificationData L k d :=
    activeConstructedStratificationData (r := r) θ w v
  have hskel : ActiveHeadRecursiveSkeleton θ D := by
    simpa [D] using activeConstructedStratificationData_recursiveSkeleton (r := r) θ w v
  exact omega_subset_of_le_of_omega_succ D hskel.omega_succ hmn hn

/-- The constructed levels and active gates are holomorphic on their recursive domains. -/
theorem activeConstructedLevel_gate_analyticOnNhd_recursiveDomain
    {r L k d : Nat} (θ : Params L k d) (w v : Vec d) :
    ∀ x : FormalVar L k,
      AnalyticOnNhd ℂ (activeConstructedLevel (r := r) θ w v x)
        ((activeConstructedStratificationData (r := r) θ w v).Omega x.1.1) ∧
      (IsActiveVar θ x →
        AnalyticOnNhd ℂ (activeConstructedGate (r := r) θ w v x)
          ((activeConstructedStratificationData (r := r) θ w v).Omega (x.1.1 + 1))) := by
  classical
  let D : ActiveStratificationData L k d :=
    activeConstructedStratificationData (r := r) θ w v
  let P : FormalVar L k → Prop := fun x =>
    AnalyticOnNhd ℂ (activeConstructedLevel (r := r) θ w v x) (D.Omega x.1.1) ∧
      (IsActiveVar θ x →
        AnalyticOnNhd ℂ (activeConstructedGate (r := r) θ w v x)
          (D.Omega (x.1.1 + 1)))
  change ∀ x : FormalVar L k, P x
  intro x
  refine (measure (fun x : FormalVar L k => x.1.1)).wf.induction (C := P) x ?_
  intro x ih
  have hlevel :
      AnalyticOnNhd ℂ (activeConstructedLevel (r := r) θ w v x)
        (D.Omega x.1.1) := by
    refine activeConstructedLevel_analyticOnNhd_of_prior_gate_analytic
      (r := r) θ w v x (U := D.Omega x.1.1) ?_
    intro y hy
    by_cases hyactive : IsActiveVar θ y
    · have hgate_y :
          AnalyticOnNhd ℂ (activeConstructedGate (r := r) θ w v y)
            (D.Omega (y.1.1 + 1)) :=
        (ih y (by simpa [measure] using hy)).2 hyactive
      have hsubset : D.Omega x.1.1 ⊆ D.Omega (y.1.1 + 1) := by
        simpa [D] using
          activeConstructedStratificationData_omega_subset_of_le
            (r := r) θ w v (m := y.1.1 + 1) (n := x.1.1)
            (by omega) (Nat.le_of_lt x.1.2)
      exact analyticOnNhd_mono hgate_y hsubset
    · have hconst :
          AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) (D.Omega x.1.1) :=
        analyticOnNhd_const (𝕜 := ℂ) (v := (0 : ℂ)) (s := D.Omega x.1.1)
      convert hconst using 1
      ext τ
      exact activeConstructedGate_eq_zero_of_inactive (r := r) θ w v hyactive τ
  have hgate :
      IsActiveVar θ x →
        AnalyticOnNhd ℂ (activeConstructedGate (r := r) θ w v x)
          (D.Omega (x.1.1 + 1)) := by
    intro hx
    have hlevel_next :
        AnalyticOnNhd ℂ (activeConstructedLevel (r := r) θ w v x)
          (D.Omega (x.1.1 + 1)) := by
      have hsubset : D.Omega (x.1.1 + 1) ⊆ D.Omega x.1.1 := by
        simpa [D] using
          activeConstructedStratificationData_omega_subset_of_le
            (r := r) θ w v (m := x.1.1) (n := x.1.1 + 1)
            (Nat.le_succ x.1.1) (Nat.succ_le_of_lt x.1.2)
      exact analyticOnNhd_mono hlevel hsubset
    refine activeConstructedGate_analyticOnNhd_of_level_analytic_of_avoids_Pi
      (r := r) θ w v hx hlevel_next ?_
    intro τ hτ
    have ha : x.2 ∈ activeHeads θ x.1 := by
      simpa [IsActiveVar] using hx
    have hτ' :
        τ ∈ (activeConstructedStratificationData (r := r) θ w v).Omega
          (x.1.1 + 1) := by
      simpa [D] using hτ
    have hnot :=
      activeConstructedStratificationData_level_notMem_Pi_on_nextOmega
        (r := r) θ w v x.1 (a := x.2) ha hτ'
    simpa [activeConstructedStratificationData, activeStratificationDataOfFunctions] using
      hnot
  exact ⟨hlevel, hgate⟩

/-- Constructed level coordinates are holomorphic on their recursive domains. -/
theorem activeConstructedStratificationData_level_holomorphic
    {r L k d : Nat} (θ : Params L k d) (w v : Vec d) :
    ∀ l : Fin L, ∀ a : Fin k, a ∈ activeHeads θ l →
      AnalyticOnNhd ℂ
        ((activeConstructedStratificationData (r := r) θ w v).level (l, a))
        ((activeConstructedStratificationData (r := r) θ w v).Omega l.1) := by
  intro l a _ha
  simpa [activeConstructedStratificationData, activeStratificationDataOfFunctions] using
    (activeConstructedLevel_gate_analyticOnNhd_recursiveDomain
      (r := r) θ w v (l, a)).1

/-- Constructed active gate coordinates are holomorphic on their next recursive domains. -/
theorem activeConstructedStratificationData_gate_holomorphic
    {r L k d : Nat} (θ : Params L k d) (w v : Vec d) :
    ∀ l : Fin L, ∀ a : Fin k, a ∈ activeHeads θ l →
      AnalyticOnNhd ℂ
        ((activeConstructedStratificationData (r := r) θ w v).gate (l, a))
        ((activeConstructedStratificationData (r := r) θ w v).Omega (l.1 + 1)) := by
  intro l a ha
  have hactive : IsActiveVar θ (l, a) := by
    simpa [IsActiveVar] using (mem_activeHeads θ l a).1 ha
  simpa [activeConstructedStratificationData, activeStratificationDataOfFunctions] using
    (activeConstructedLevel_gate_analyticOnNhd_recursiveDomain
      (r := r) θ w v (l, a)).2 hactive

/-- The constructed observable is coordinatewise holomorphic on the final recursive
domain. -/
theorem activeConstructedStratificationData_observable_holomorphic
    {r L k d : Nat} (θ : Params L k d) (w v : Vec d) :
    ∀ i : Fin d,
      AnalyticOnNhd ℂ
        (fun τ => (activeConstructedStratificationData (r := r) θ w v).observable τ i)
        ((activeConstructedStratificationData (r := r) θ w v).Omega L) := by
  classical
  let D : ActiveStratificationData L k d :=
    activeConstructedStratificationData (r := r) θ w v
  have hgate_all :
      ∀ x : FormalVar L k,
        AnalyticOnNhd ℂ (activeConstructedGate (r := r) θ w v x)
          (D.Omega L) := by
    intro x
    by_cases hx : IsActiveVar θ x
    · have hgate_x :
          AnalyticOnNhd ℂ (activeConstructedGate (r := r) θ w v x)
            (D.Omega (x.1.1 + 1)) :=
        (activeConstructedLevel_gate_analyticOnNhd_recursiveDomain
          (r := r) θ w v x).2 hx
      have hsubset : D.Omega L ⊆ D.Omega (x.1.1 + 1) := by
        simpa [D] using
          activeConstructedStratificationData_omega_subset_of_le
            (r := r) θ w v (m := x.1.1 + 1) (n := L)
            (Nat.succ_le_of_lt x.1.2) le_rfl
      exact analyticOnNhd_mono hgate_x hsubset
    · have hconst :
          AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) (D.Omega L) :=
        analyticOnNhd_const (𝕜 := ℂ) (v := (0 : ℂ)) (s := D.Omega L)
      convert hconst using 1
      ext τ
      exact activeConstructedGate_eq_zero_of_inactive (r := r) θ w v hx τ
  intro i
  simpa [D, activeConstructedStratificationData, activeStratificationDataOfFunctions] using
    activeConstructedObservable_analyticOnNhd_of_gate_analytic
      (r := r) θ w v (U := D.Omega L) hgate_all i

/-- The constructed recursive domains form a plane-domain tower.  At each stage, the
current active stratum is closed-discrete in the current domain, so the next partial
singular union is closed and countable; its complement is therefore a plane domain. -/
theorem activeConstructedStratificationData_domain {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) :
    ∀ n : Nat, n ≤ L →
      PlaneDomain ((activeConstructedStratificationData (r := r) θ w v).Omega n) := by
  classical
  let D : ActiveStratificationData L k d :=
    activeConstructedStratificationData (r := r) θ w v
  have hskel : ActiveHeadRecursiveSkeleton θ D := by
    simpa [D] using activeConstructedStratificationData_recursiveSkeleton (r := r) θ w v
  have haxis : ∀ n : Nat, n ≤ L → nonnegativeRealAxis ⊆ D.Omega n := by
    simpa [D] using
      activeConstructedStratificationData_nonnegativeRealAxis_subset_omega
        (r := r) θ w v
  have hlevel_holomorphic :
      ∀ l : Fin L, ∀ a : Fin k, a ∈ activeHeads θ l →
        AnalyticOnNhd ℂ (D.level (l, a)) (D.Omega l.1) := by
    simpa [D] using
      activeConstructedStratificationData_level_holomorphic (r := r) θ w v
  have hmain :
      ∀ n : Nat, n ≤ L →
        IsClosed (partialUnion D.stratum n) ∧
          (partialUnion D.stratum n).Countable ∧
          PlaneDomain (D.Omega n) := by
    intro n hn
    induction n with
    | zero =>
        have hclosed : IsClosed (partialUnion D.stratum 0) := by
          simp [partialUnion]
        have hcount : (partialUnion D.stratum 0).Countable := by
          simp [partialUnion]
        have hdomain : PlaneDomain (D.Omega 0) := by
          simpa [hskel.omega_zero] using
            (countable_closed_compl_planeDomain
              (E := (∅ : Set ℂ)) Set.countable_empty isClosed_empty)
        exact ⟨hclosed, hcount, hdomain⟩
    | succ n ih =>
        have hnle : n ≤ L := Nat.le_of_succ_le hn
        have hnL : n < L := Nat.lt_of_succ_le hn
        rcases ih hnle with ⟨_hclosedPrev, hcountPrev, hdomainPrev⟩
        let l : Fin L := ⟨n, hnL⟩
        have hCD : ClosedDiscreteIn (D.stratum n) (D.Omega n) := by
          simpa [l] using
            stratum_closedDiscrete_of_level_zero_data (r := r) θ D l (hskel.stratum_eq l)
              hdomainPrev
              (zero_mem_of_nonnegativeRealAxis_subset (haxis n hnle))
              (fun a ha => hlevel_holomorphic l a ha)
              (fun a ha => by
                simpa [D, l] using
                  activeConstructedStratificationData_level_zero
                    (r := r) θ w v l a ha)
        have hclosedSucc : IsClosed (partialUnion D.stratum (n + 1)) := by
          have hrel : IsClosed ((D.Omega n)ᶜ ∪ D.stratum n) := hCD.isClosed_rel
          have hΩeq : D.Omega n = (partialUnion D.stratum n)ᶜ :=
            hskel.omega_eq_partialUnion_compl n hnle
          rw [hΩeq] at hrel
          simpa [partialUnion_succ, Set.union_assoc, Set.union_comm, Set.union_left_comm]
            using hrel
        have hcountSucc : (partialUnion D.stratum (n + 1)).Countable := by
          have hUnion : (partialUnion D.stratum n ∪ D.stratum n).Countable :=
            hcountPrev.union hCD.countable
          simpa [partialUnion_succ, Set.union_assoc, Set.union_comm, Set.union_left_comm]
            using hUnion
        have hdomainSucc : PlaneDomain (D.Omega (n + 1)) := by
          have hΩeq : D.Omega (n + 1) = (partialUnion D.stratum (n + 1))ᶜ :=
            hskel.omega_eq_partialUnion_compl (n + 1) hn
          rw [hΩeq]
          exact countable_closed_compl_planeDomain hcountSucc hclosedSucc
        exact ⟨hclosedSucc, hcountSucc, hdomainSucc⟩
  intro n hn
  exact (hmain n hn).2.2

/-- Evaluating a formal polynomial at the active complex gate assignment is analytic on
any domain where all active gate coordinates are analytic.  Inactive coordinates contribute
only the constant zero function. -/
theorem evalFormalPolyComplex_activeComplexGateAssignment_analyticOnNhd {L k d : Nat}
    (θ : Params L k d) (D : ActiveStratificationData L k d) (p : FormalPoly L k)
    {U : Set ℂ}
    (hgate : ∀ l : Fin L, ∀ a : Fin k, a ∈ activeHeads θ l →
      AnalyticOnNhd ℂ (D.gate (l, a)) U) :
    AnalyticOnNhd ℂ
      (fun τ => evalFormalPolyComplex (activeComplexGateAssignment θ D τ) p) U := by
  refine evalFormalPolyComplex_analyticOnNhd (L := L) (k := k) p ?_
  intro x
  rcases x with ⟨l, a⟩
  by_cases ha : a ∈ activeHeads θ l
  · simpa [activeComplexGateAssignment, IsActiveVar, (mem_activeHeads θ l a).1 ha] using
      hgate l a ha
  · have hnot : ¬ IsActiveVar θ (l, a) := by
      simpa using ha
    simpa [activeComplexGateAssignment, hnot] using
      (analyticOnNhd_const (𝕜 := ℂ) (v := (0 : ℂ)) (s := U))

/-- Coordinatewise active-assignment version for formal vectors. -/
theorem evalFormalVecComplex_activeComplexGateAssignment_analyticOnNhd {L k d : Nat}
    (θ : Params L k d) (D : ActiveStratificationData L k d) (x : FormalVec L k d)
    {U : Set ℂ}
    (hgate : ∀ l : Fin L, ∀ a : Fin k, a ∈ activeHeads θ l →
      AnalyticOnNhd ℂ (D.gate (l, a)) U) :
    ∀ i : Fin d,
      AnalyticOnNhd ℂ
        (fun τ => evalFormalVecComplex (activeComplexGateAssignment θ D τ) x i) U := by
  intro i
  exact evalFormalPolyComplex_activeComplexGateAssignment_analyticOnNhd θ D (x i) hgate

/-- All value matrices are nonzero.  This is the k-head form of regularity clause (R1). -/
def AllHeadsActive {L k d : Nat} (θ : Params L k d) : Prop :=
  ∀ (l : Fin L) (a : Fin k), IsActiveHead θ l a

theorem activeHeads_eq_univ_of_all_heads_active {L k d : Nat}
    {θ : Params L k d} (hθ : AllHeadsActive θ) (l : Fin L) :
    activeHeads θ l = Finset.univ := by
  classical
  ext a
  simp [activeHeads, hθ l a]

theorem allHeadsActive_iff_activeHeads_eq_univ {L k d : Nat} {θ : Params L k d} :
    AllHeadsActive θ ↔ ∀ l : Fin L, activeHeads θ l = Finset.univ := by
  constructor
  · intro hθ l
    exact activeHeads_eq_univ_of_all_heads_active hθ l
  · intro hactive l a
    have ha : a ∈ activeHeads θ l := by
      rw [hactive l]
      simp
    exact (mem_activeHeads θ l a).1 ha

theorem activeGateAssignment_eq_self_of_all_heads_active {L k d : Nat}
    {θ : Params L k d} (hθ : AllHeadsActive θ) (ρ : FormalVar L k → ℝ) :
    activeGateAssignment θ ρ = ρ := by
  funext x
  rcases x with ⟨l, a⟩
  exact activeGateAssignment_eq_of_active θ ρ
    ((mem_activeHeads θ l a).2 (hθ l a))

theorem activeComplexGateAssignment_eq_gate_of_all_heads_active {L k d : Nat}
    {θ : Params L k d} (D : ActiveStratificationData L k d) (τ : ℂ)
    (hθ : AllHeadsActive θ) :
    activeComplexGateAssignment θ D τ = fun x => D.gate x τ := by
  funext x
  rcases x with ⟨l, a⟩
  exact activeComplexGateAssignment_eq_of_active θ D τ
    ((mem_activeHeads θ l a).2 (hθ l a))

theorem reducedStratumAt_eq_fullStratumAt_of_all_heads_active {L k d : Nat}
    {θ : Params L k d} (D : ActiveStratificationData L k d)
    (hθ : AllHeadsActive θ) (l : Fin L) :
    reducedStratumAt θ D l = fullStratumAt D l := by
  unfold reducedStratumAt fullStratumAt
  rw [activeHeads_eq_univ_of_all_heads_active hθ l]
  ext τ
  simp

/-- Positivity of the TeX bias `b = log r` under the standing sequence-length
assumption `1 < r`. -/
theorem logScale_pos_of_one_lt {r : Nat} (hr : 1 < r) : 0 < logScale r := by
  exact Real.log_pos (by exact_mod_cast hr)

/-- Coordinatewise identity theorem for complex-vector-valued functions on the final
domain: agreement on every positive real input forces agreement on the whole connected
domain. -/
theorem complexVec_eqOn_of_positiveRealAxis_eq {L k d : Nat}
    (D : ActiveStratificationData L k d)
    (hΩ : PlaneDomain (D.Omega L))
    (hpos : positiveRealAxis ⊆ D.Omega L)
    {F G : ℂ → ComplexVec d}
    (hF : ∀ i : Fin d, AnalyticOnNhd ℂ (fun τ => F τ i) (D.Omega L))
    (hG : ∀ i : Fin d, AnalyticOnNhd ℂ (fun τ => G τ i) (D.Omega L))
    (hEq : ∀ τ : ℝ, 0 < τ → F (τ : ℂ) = G (τ : ℂ)) :
    Set.EqOn F G (D.Omega L) := by
  intro z hz
  funext i
  have hfreq :
      ∃ᶠ ζ in nhdsWithin (1 : ℂ) ({(1 : ℂ)}ᶜ : Set ℂ),
        (fun τ : ℂ => F τ i) ζ = (fun τ : ℂ => G τ i) ζ := by
    exact TransformerIdentifiability.NLayer.frequently_eq_nhdsWithin_of_forall_real_tail_eq
      (Y := ℂ) (T0 := 0) (x0 := 1) (by norm_num : (0 : ℝ) < 1)
      (fun t ht => congrFun (hEq t ht) i)
  have h1Ω : (1 : ℂ) ∈ D.Omega L := hpos one_mem_positiveRealAxis
  have hcoord :
      Set.EqOn (fun τ : ℂ => F τ i) (fun τ : ℂ => G τ i) (D.Omega L) :=
    (hF i).eqOn_of_preconnected_of_frequently_eq (hG i)
      hΩ.isConnected.isPreconnected h1Ω hfreq
  exact hcoord hz

/-- Variant of `complexVec_eqOn_of_positiveRealAxis_eq` for hypotheses stated as
`Set.EqOn` on the positive real ray. -/
theorem complexVec_eqOn_of_eqOn_positiveRealAxis {L k d : Nat}
    (D : ActiveStratificationData L k d)
    (hΩ : PlaneDomain (D.Omega L))
    (hpos : positiveRealAxis ⊆ D.Omega L)
    {F G : ℂ → ComplexVec d}
    (hF : ∀ i : Fin d, AnalyticOnNhd ℂ (fun τ => F τ i) (D.Omega L))
    (hG : ∀ i : Fin d, AnalyticOnNhd ℂ (fun τ => G τ i) (D.Omega L))
    (hEq : Set.EqOn F G positiveRealAxis) :
    Set.EqOn F G (D.Omega L) :=
  complexVec_eqOn_of_positiveRealAxis_eq D hΩ hpos hF hG
    (fun τ hτ => hEq (x := (τ : ℂ)) (ofReal_mem_positiveRealAxis hτ))

/-- Observable uniqueness for the constructed data once the final constructed domain and
observable holomorphy have been supplied. -/
theorem activeConstructedStratificationData_observable_unique
    {r L k d : Nat} (θ : Params L k d) (w v : Vec d)
    (hdomain :
      PlaneDomain ((activeConstructedStratificationData (r := r) θ w v).Omega L))
    (hobservable_holomorphic :
      ∀ i : Fin d,
        AnalyticOnNhd ℂ
          (fun τ => (activeConstructedStratificationData (r := r) θ w v).observable τ i)
          ((activeConstructedStratificationData (r := r) θ w v).Omega L)) :
    ∀ G : ℂ → ComplexVec d,
      (∀ i : Fin d,
        AnalyticOnNhd ℂ (fun τ => G τ i)
          ((activeConstructedStratificationData (r := r) θ w v).Omega L)) →
      (∀ τ : ℝ, 0 < τ → G (τ : ℂ) = realVecToComplex (probeOutput r θ w v τ)) →
      Set.EqOn G (activeConstructedStratificationData (r := r) θ w v).observable
        ((activeConstructedStratificationData (r := r) θ w v).Omega L) := by
  intro G hG hEq
  refine complexVec_eqOn_of_positiveRealAxis_eq
    (activeConstructedStratificationData (r := r) θ w v) hdomain
    (activeConstructedStratificationData_positiveRealAxis_subset_omega
      (r := r) θ w v L le_rfl)
    hG hobservable_holomorphic ?_
  intro τ hτ
  rw [hEq τ hτ,
    activeConstructedStratificationData_observable_positive_real_eq_probeOutput
      (r := r) θ w v τ hτ]

/-- At the first layer, formal slopes are constant and equal to the probe bilinear
slope, independently of the gate assignment. -/
theorem evalFormalPolyComplex_formalSlope_first {L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (hL : 0 < L) (a : Fin k)
    (η : FormalVar L k → ℂ) :
    evalFormalPolyComplex η (formalSlope θ w v ⟨0, hL⟩ a) =
      (matrixBilin (attentionMatrix θ ⟨0, hL⟩ a) w v : ℂ) := by
  rw [formalSlope, evalFormalPolyComplex_formalBilin]
  simp [matrixBilin, realVecToComplex, Matrix.mulVec, dotProduct]

/-- The constructed first-layer level is the affine sigmoid argument
`τ * (wᵀ A_{0a} v) + log r`. -/
theorem activeConstructedLevel_first {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (hL : 0 < L) (a : Fin k) (τ : ℂ) :
    activeConstructedLevel (r := r) θ w v (⟨0, hL⟩, a) τ =
      τ * (matrixBilin (attentionMatrix θ ⟨0, hL⟩ a) w v : ℂ) +
        (logScale r : ℂ) := by
  rw [activeConstructedLevel]
  rw [evalFormalPolyComplex_formalSlope_first θ w v hL a]

/-- The constructed first stratum is exactly the union of affine sigmoid pole
progressions contributed by active first-layer heads with nonzero probe slope. -/
theorem activeConstructedStratificationData_first_stratum_eq_pole_progressions
    {r L k d : Nat} (θ : Params L k d) (w v : Vec d) :
    ∀ hL : 0 < L,
      (activeConstructedStratificationData (r := r) θ w v).stratum 0 =
        ⋃ a : Fin k,
          ⋃ _ : a ∈ activeHeads θ ⟨0, hL⟩,
            ⋃ _ : matrixBilin (attentionMatrix θ ⟨0, hL⟩ a) w v ≠ 0,
              affineSigmoidPoleSet (logScale r)
                (matrixBilin (attentionMatrix θ ⟨0, hL⟩ a) w v) := by
  intro hL
  classical
  let l : Fin L := ⟨0, hL⟩
  let D : ActiveStratificationData L k d :=
    activeConstructedStratificationData (r := r) θ w v
  have hskel : ActiveHeadRecursiveSkeleton θ D := by
    simpa [D] using activeConstructedStratificationData_recursiveSkeleton (r := r) θ w v
  change D.stratum l.1 =
    ⋃ a : Fin k,
      ⋃ _ : a ∈ activeHeads θ l,
        ⋃ _ : matrixBilin (attentionMatrix θ l a) w v ≠ 0,
          affineSigmoidPoleSet (logScale r)
            (matrixBilin (attentionMatrix θ l a) w v)
  rw [hskel.stratum_eq l]
  ext τ
  simp only [reducedStratumAt, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · intro hτ
    rcases hτ with ⟨a, ha, _hτΩ, hτPi⟩
    let slope : ℝ := matrixBilin (attentionMatrix θ l a) w v
    have hlevel :
        D.level (l, a) τ = τ * (slope : ℂ) + (logScale r : ℂ) := by
      simpa [D, activeConstructedStratificationData,
        activeStratificationDataOfFunctions, l, slope] using
        activeConstructedLevel_first (r := r) θ w v hL a τ
    by_cases hslope : slope = 0
    · have hlogPi : (logScale r : ℂ) ∈ Pi := by
        simpa [hlevel, hslope] using hτPi
      exact False.elim (ofReal_notMem_Pi (logScale r) hlogPi)
    · refine ⟨a, ha, hslope, ?_⟩
      have harg : (slope : ℂ) * τ + (logScale r : ℂ) ∈ Pi := by
        convert hτPi using 1
        rw [hlevel]
        ring
      exact (mem_affineSigmoidPoleSet_iff hslope τ).2 harg
  · intro hτ
    rcases hτ with ⟨a, ha, hslope, hτpole⟩
    let slope : ℝ := matrixBilin (attentionMatrix θ l a) w v
    have hslope' : slope ≠ 0 := by
      simpa [l, slope] using hslope
    have hlevel :
        D.level (l, a) τ = τ * (slope : ℂ) + (logScale r : ℂ) := by
      simpa [D, activeConstructedStratificationData,
        activeStratificationDataOfFunctions, l, slope] using
        activeConstructedLevel_first (r := r) θ w v hL a τ
    refine ⟨a, ha, ?_, ?_⟩
    · change τ ∈ D.Omega l.1
      have hΩ0 : D.Omega l.1 = Set.univ := by
        simpa [l] using hskel.omega_zero
      rw [hΩ0]
      simp
    · have harg : (slope : ℂ) * τ + (logScale r : ℂ) ∈ Pi := by
        exact (mem_affineSigmoidPoleSet_iff hslope' τ).1 (by
          simpa [l, slope] using hτpole)
      convert harg using 1
      rw [hlevel]
      ring

/-- Strong proposition-valued API for TeX `prop:singular-stratification`.

It records the probe `(w, v)`, active-head reduced recursive domains and strata,
holomorphic level/gate data, real-axis avoidance semantics, consistency with the actual
probe recursion on positive real `τ`, holomorphic continuation of the observable, and the
identity-theorem uniqueness clause.  This is intentionally an interface: the analytic
construction of such data is not proved in this file. -/
structure ActiveHeadSingularStratification {r L k d : Nat} (hr : 1 < r)
    (θ : Params L k d) (w v : Vec d) (D : ActiveStratificationData L k d) : Prop where
  omega_zero : D.Omega 0 = Set.univ
  omega_succ : ∀ l : Fin L, D.Omega (l.1 + 1) = D.Omega l.1 \ D.stratum l.1
  omega_eq_partialUnion_compl :
    ∀ n : Nat, n ≤ L → D.Omega n = (partialUnion D.stratum n)ᶜ
  domain : ∀ n : Nat, n ≤ L → PlaneDomain (D.Omega n)
  nonnegative_axis_subset : ∀ n : Nat, n ≤ L → nonnegativeRealAxis ⊆ D.Omega n
  stratum_eq : ∀ l : Fin L, D.stratum l.1 = reducedStratumAt θ D l
  stratum_closedDiscrete : ∀ l : Fin L, ClosedDiscreteIn (D.stratum l.1) (D.Omega l.1)
  first_stratum_eq_pole_progressions :
    ∀ hL : 0 < L,
      D.stratum 0 =
        ⋃ a : Fin k,
          ⋃ _ : a ∈ activeHeads θ ⟨0, hL⟩,
            ⋃ _ : matrixBilin (attentionMatrix θ ⟨0, hL⟩ a) w v ≠ 0,
              affineSigmoidPoleSet (logScale r)
                (matrixBilin (attentionMatrix θ ⟨0, hL⟩ a) w v)
  level_formula : ∀ l : Fin L, ∀ a : Fin k, a ∈ activeHeads θ l →
    Set.EqOn (D.level (l, a))
      (fun τ : ℂ =>
        τ * evalFormalPolyComplex (activeComplexGateAssignment θ D τ)
          (formalSlope θ w v l a) + (logScale r : ℂ))
      (D.Omega l.1)
  level_holomorphic : ∀ l : Fin L, ∀ a : Fin k, a ∈ activeHeads θ l →
    AnalyticOnNhd ℂ (D.level (l, a)) (D.Omega l.1)
  level_real_on_nonnegative_axis : ∀ l : Fin L, ∀ a : Fin k, a ∈ activeHeads θ l →
    IsRealValuedOn (D.level (l, a)) nonnegativeRealAxis
  level_zero : ∀ l : Fin L, ∀ a : Fin k, a ∈ activeHeads θ l →
    D.level (l, a) 0 = (logScale r : ℂ)
  level_not_constant_pole : ∀ l : Fin L, ∀ a : Fin k, a ∈ activeHeads θ l →
    ∀ c : ℂ, c ∈ Pi → ¬ Set.EqOn (D.level (l, a)) (fun _ : ℂ => c) (D.Omega l.1)
  gate_formula : ∀ l : Fin L, ∀ a : Fin k, a ∈ activeHeads θ l →
    Set.EqOn (D.gate (l, a)) (fun τ => csig (D.level (l, a) τ))
      (D.Omega (l.1 + 1))
  gate_holomorphic : ∀ l : Fin L, ∀ a : Fin k, a ∈ activeHeads θ l →
    AnalyticOnNhd ℂ (D.gate (l, a)) (D.Omega (l.1 + 1))
  gate_real_on_nonnegative_axis : ∀ l : Fin L, ∀ a : Fin k, a ∈ activeHeads θ l →
    IsRealValuedOn (D.gate (l, a)) nonnegativeRealAxis
  gate_zero : ∀ l : Fin L, ∀ a : Fin k, a ∈ activeHeads θ l →
    D.gate (l, a) 0 = (alpha r : ℂ)
  positive_level_eq_actual : ∀ l : Fin L, ∀ a : Fin k, a ∈ activeHeads θ l →
    ∀ τ : ℝ, 0 < τ →
      D.level (l, a) (τ : ℂ) =
        ((τ * actualProbeSlope r θ w v τ l a + logScale r : ℝ) : ℂ)
  positive_gate_eq_actual : ∀ l : Fin L, ∀ a : Fin k, a ∈ activeHeads θ l →
    ∀ τ : ℝ, 0 < τ →
      D.gate (l, a) (τ : ℂ) = (actualProbeGate r θ w v τ l a : ℂ)
  observable_formula :
    Set.EqOn D.observable
      (fun τ : ℂ =>
        evalFormalVecComplex (activeComplexGateAssignment θ D τ)
          (formalV θ w v L le_rfl))
      (D.Omega L)
  observable_holomorphic :
    ∀ i : Fin d, AnalyticOnNhd ℂ (fun τ => D.observable τ i) (D.Omega L)
  observable_positive_real_eq_probeOutput :
    ∀ τ : ℝ, 0 < τ → D.observable (τ : ℂ) = realVecToComplex (probeOutput r θ w v τ)
  observable_unique :
    ∀ G : ℂ → ComplexVec d,
      (∀ i : Fin d, AnalyticOnNhd ℂ (fun τ => G τ i) (D.Omega L)) →
      (∀ τ : ℝ, 0 < τ → G (τ : ℂ) = realVecToComplex (probeOutput r θ w v τ)) →
      Set.EqOn G D.observable (D.Omega L)

/-- Strong statement form for `K04D.E.prop-singular-stratification.S`. -/
def prop_singular_stratification_statement {r L k d : Nat} (hr : 1 < r)
    (θ : Params L k d) (w v : Vec d) : Prop :=
  ∃ D : ActiveStratificationData L k d, ActiveHeadSingularStratification hr θ w v D

/-- Constructor package for the concrete recursive data: once the remaining analytic
domain/holomorphy and first-stratum obligations are supplied, all semantic fields of
`ActiveHeadSingularStratification` follow from the constructed-data lemmas above. -/
theorem activeConstructedStratificationData_singularStratification_of_analytic
    {r L k d : Nat} (hr : 1 < r) (θ : Params L k d) (w v : Vec d)
    (hdomain : ∀ n : Nat, n ≤ L →
      PlaneDomain ((activeConstructedStratificationData (r := r) θ w v).Omega n))
    (hlevel_holomorphic :
      ∀ l : Fin L, ∀ a : Fin k, a ∈ activeHeads θ l →
        AnalyticOnNhd ℂ
          ((activeConstructedStratificationData (r := r) θ w v).level (l, a))
          ((activeConstructedStratificationData (r := r) θ w v).Omega l.1))
    (hgate_holomorphic :
      ∀ l : Fin L, ∀ a : Fin k, a ∈ activeHeads θ l →
        AnalyticOnNhd ℂ
          ((activeConstructedStratificationData (r := r) θ w v).gate (l, a))
          ((activeConstructedStratificationData (r := r) θ w v).Omega (l.1 + 1)))
    (hobservable_holomorphic :
      ∀ i : Fin d,
        AnalyticOnNhd ℂ
          (fun τ => (activeConstructedStratificationData (r := r) θ w v).observable τ i)
          ((activeConstructedStratificationData (r := r) θ w v).Omega L))
    (hfirst :
      ∀ hL : 0 < L,
        (activeConstructedStratificationData (r := r) θ w v).stratum 0 =
          ⋃ a : Fin k,
            ⋃ _ : a ∈ activeHeads θ ⟨0, hL⟩,
              ⋃ _ : matrixBilin (attentionMatrix θ ⟨0, hL⟩ a) w v ≠ 0,
                affineSigmoidPoleSet (logScale r)
                  (matrixBilin (attentionMatrix θ ⟨0, hL⟩ a) w v)) :
    ActiveHeadSingularStratification hr θ w v
      (activeConstructedStratificationData (r := r) θ w v) := by
  let D : ActiveStratificationData L k d :=
    activeConstructedStratificationData (r := r) θ w v
  change ActiveHeadSingularStratification hr θ w v D
  change ∀ n : Nat, n ≤ L → PlaneDomain (D.Omega n) at hdomain
  change ∀ l : Fin L, ∀ a : Fin k, a ∈ activeHeads θ l →
    AnalyticOnNhd ℂ (D.level (l, a)) (D.Omega l.1) at hlevel_holomorphic
  change ∀ l : Fin L, ∀ a : Fin k, a ∈ activeHeads θ l →
    AnalyticOnNhd ℂ (D.gate (l, a)) (D.Omega (l.1 + 1)) at hgate_holomorphic
  change ∀ i : Fin d,
    AnalyticOnNhd ℂ (fun τ => D.observable τ i) (D.Omega L) at hobservable_holomorphic
  change ∀ hL : 0 < L,
    D.stratum 0 =
      ⋃ a : Fin k,
        ⋃ _ : a ∈ activeHeads θ ⟨0, hL⟩,
          ⋃ _ : matrixBilin (attentionMatrix θ ⟨0, hL⟩ a) w v ≠ 0,
            affineSigmoidPoleSet (logScale r)
              (matrixBilin (attentionMatrix θ ⟨0, hL⟩ a) w v) at hfirst
  have hskel : ActiveHeadRecursiveSkeleton θ D := by
    simpa [D] using activeConstructedStratificationData_recursiveSkeleton (r := r) θ w v
  have haxis : ∀ n : Nat, n ≤ L → nonnegativeRealAxis ⊆ D.Omega n := by
    simpa [D] using
      activeConstructedStratificationData_nonnegativeRealAxis_subset_omega
        (r := r) θ w v
  refine
    { omega_zero := hskel.omega_zero
      omega_succ := hskel.omega_succ
      omega_eq_partialUnion_compl := hskel.omega_eq_partialUnion_compl
      domain := hdomain
      nonnegative_axis_subset := haxis
      stratum_eq := hskel.stratum_eq
      stratum_closedDiscrete := ?_
      first_stratum_eq_pole_progressions := hfirst
      level_formula := ?_
      level_holomorphic := hlevel_holomorphic
      level_real_on_nonnegative_axis := ?_
      level_zero := ?_
      level_not_constant_pole := ?_
      gate_formula := ?_
      gate_holomorphic := hgate_holomorphic
      gate_real_on_nonnegative_axis := ?_
      gate_zero := ?_
      positive_level_eq_actual := ?_
      positive_gate_eq_actual := ?_
      observable_formula := ?_
      observable_holomorphic := hobservable_holomorphic
      observable_positive_real_eq_probeOutput := ?_
      observable_unique := ?_ }
  · intro l
    exact stratum_closedDiscrete_of_level_zero_data (r := r) θ D l (hskel.stratum_eq l)
      (hdomain l.1 (Nat.le_of_lt l.2))
      (zero_mem_of_nonnegativeRealAxis_subset (haxis l.1 (Nat.le_of_lt l.2)))
      (fun a ha => hlevel_holomorphic l a ha)
      (fun a ha => by
        simpa [D] using
          activeConstructedStratificationData_level_zero (r := r) θ w v l a ha)
  · simpa [D] using activeConstructedStratificationData_level_formula (r := r) θ w v
  · simpa [D] using
      activeConstructedStratificationData_level_real_on_nonnegativeRealAxis
        (r := r) θ w v
  · simpa [D] using activeConstructedStratificationData_level_zero (r := r) θ w v
  · simpa [D] using
      activeConstructedStratificationData_level_not_constant_pole (r := r) θ w v
  · simpa [D] using activeConstructedStratificationData_gate_formula (r := r) θ w v
  · simpa [D] using
      activeConstructedStratificationData_gate_real_on_nonnegativeRealAxis
        (r := r) θ w v
  · simpa [D] using activeConstructedStratificationData_gate_zero (r := r) θ w v
  · simpa [D] using
      activeConstructedStratificationData_positive_level_eq_actual (r := r) θ w v
  · simpa [D] using
      activeConstructedStratificationData_positive_gate_eq_actual (r := r) θ w v
  · simpa [D] using activeConstructedStratificationData_observable_formula (r := r) θ w v
  · simpa [D] using
      activeConstructedStratificationData_observable_positive_real_eq_probeOutput
        (r := r) θ w v
  · simpa [D] using
      activeConstructedStratificationData_observable_unique (r := r) θ w v
        (hdomain L le_rfl) hobservable_holomorphic

/-- Constructor package for the concrete recursive data with the first-stratum formula
discharged by `activeConstructedStratificationData_first_stratum_eq_pole_progressions`. -/
theorem activeConstructedStratificationData_singularStratification_of_analytic_constructed
    {r L k d : Nat} (hr : 1 < r) (θ : Params L k d) (w v : Vec d)
    (hdomain : ∀ n : Nat, n ≤ L →
      PlaneDomain ((activeConstructedStratificationData (r := r) θ w v).Omega n))
    (hlevel_holomorphic :
      ∀ l : Fin L, ∀ a : Fin k, a ∈ activeHeads θ l →
        AnalyticOnNhd ℂ
          ((activeConstructedStratificationData (r := r) θ w v).level (l, a))
          ((activeConstructedStratificationData (r := r) θ w v).Omega l.1))
    (hgate_holomorphic :
      ∀ l : Fin L, ∀ a : Fin k, a ∈ activeHeads θ l →
        AnalyticOnNhd ℂ
          ((activeConstructedStratificationData (r := r) θ w v).gate (l, a))
          ((activeConstructedStratificationData (r := r) θ w v).Omega (l.1 + 1)))
    (hobservable_holomorphic :
      ∀ i : Fin d,
        AnalyticOnNhd ℂ
          (fun τ => (activeConstructedStratificationData (r := r) θ w v).observable τ i)
          ((activeConstructedStratificationData (r := r) θ w v).Omega L)) :
    ActiveHeadSingularStratification hr θ w v
      (activeConstructedStratificationData (r := r) θ w v) := by
  exact activeConstructedStratificationData_singularStratification_of_analytic
    hr θ w v hdomain hlevel_holomorphic hgate_holomorphic hobservable_holomorphic
    (activeConstructedStratificationData_first_stratum_eq_pole_progressions
      (r := r) θ w v)

/-- `K04D.E.prop-singular-stratification.S` instantiated by the constructed recursive
data, modulo the analytic domain and holomorphy obligations. -/
theorem prop_singular_stratification_statement_of_activeConstructedStratificationData_analytic
    {r L k d : Nat} (hr : 1 < r) (θ : Params L k d) (w v : Vec d)
    (hdomain : ∀ n : Nat, n ≤ L →
      PlaneDomain ((activeConstructedStratificationData (r := r) θ w v).Omega n))
    (hlevel_holomorphic :
      ∀ l : Fin L, ∀ a : Fin k, a ∈ activeHeads θ l →
        AnalyticOnNhd ℂ
          ((activeConstructedStratificationData (r := r) θ w v).level (l, a))
          ((activeConstructedStratificationData (r := r) θ w v).Omega l.1))
    (hgate_holomorphic :
      ∀ l : Fin L, ∀ a : Fin k, a ∈ activeHeads θ l →
        AnalyticOnNhd ℂ
          ((activeConstructedStratificationData (r := r) θ w v).gate (l, a))
          ((activeConstructedStratificationData (r := r) θ w v).Omega (l.1 + 1)))
    (hobservable_holomorphic :
      ∀ i : Fin d,
        AnalyticOnNhd ℂ
          (fun τ => (activeConstructedStratificationData (r := r) θ w v).observable τ i)
          ((activeConstructedStratificationData (r := r) θ w v).Omega L)) :
    prop_singular_stratification_statement hr θ w v := by
  refine ⟨activeConstructedStratificationData (r := r) θ w v, ?_⟩
  exact activeConstructedStratificationData_singularStratification_of_analytic_constructed
    hr θ w v hdomain hlevel_holomorphic hgate_holomorphic hobservable_holomorphic

/-- The concrete recursive construction satisfies the full active-head singular
stratification interface. -/
theorem activeConstructedStratificationData_singularStratification
    {r L k d : Nat} (hr : 1 < r) (θ : Params L k d) (w v : Vec d) :
    ActiveHeadSingularStratification hr θ w v
      (activeConstructedStratificationData (r := r) θ w v) := by
  exact activeConstructedStratificationData_singularStratification_of_analytic_constructed
    hr θ w v
    (activeConstructedStratificationData_domain (r := r) θ w v)
    (activeConstructedStratificationData_level_holomorphic (r := r) θ w v)
    (activeConstructedStratificationData_gate_holomorphic (r := r) θ w v)
    (activeConstructedStratificationData_observable_holomorphic (r := r) θ w v)

/-- **K04D.E.prop-singular-stratification.P**.

Existence form of the active-head singular stratification, instantiated by the concrete
recursive construction. -/
theorem K04D_prop_singular_stratification
    {r L k d : Nat} (hr : 1 < r) (θ : Params L k d) (w v : Vec d) :
    prop_singular_stratification_statement hr θ w v := by
  exact ⟨activeConstructedStratificationData (r := r) θ w v,
    activeConstructedStratificationData_singularStratification hr θ w v⟩

theorem activeHeadRecursiveSkeleton_of_activeHeadSingularStratification
    {r L k d : Nat} {hr : 1 < r}
    {θ : Params L k d} {w v : Vec d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification hr θ w v D) :
    ActiveHeadRecursiveSkeleton θ D where
  omega_zero := hD.omega_zero
  stratum_eq := hD.stratum_eq
  omega_succ := hD.omega_succ
  omega_eq_partialUnion_compl := hD.omega_eq_partialUnion_compl

theorem omega_eq_partialUnion_compl_derived {r L k d : Nat} {hr : 1 < r}
    {θ : Params L k d} {w v : Vec d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification hr θ w v D)
    (n : Nat) (hn : n ≤ L) :
    D.Omega n = (partialUnion D.stratum n)ᶜ :=
  omega_eq_partialUnion_compl_of_omega_succ D hD.omega_zero hD.omega_succ n hn

theorem mem_first_stratum_iff {r L k d : Nat} {hr : 1 < r}
    {θ : Params L k d} {w v : Vec d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification hr θ w v D)
    (hL : 0 < L) {τ : ℂ} :
    τ ∈ D.stratum 0 ↔
      ∃ a : Fin k, a ∈ activeHeads θ ⟨0, hL⟩ ∧
        matrixBilin (attentionMatrix θ ⟨0, hL⟩ a) w v ≠ 0 ∧
          τ ∈ affineSigmoidPoleSet (logScale r)
            (matrixBilin (attentionMatrix θ ⟨0, hL⟩ a) w v) := by
  rw [hD.first_stratum_eq_pole_progressions hL]
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨a, ha, hslope, hτ⟩
    exact ⟨a, ha, hslope, hτ⟩
  · rintro ⟨a, ha, hslope, hτ⟩
    exact ⟨a, ha, hslope, hτ⟩

theorem affineSigmoidPoleSet_subset_first_stratum {r L k d : Nat} {hr : 1 < r}
    {θ : Params L k d} {w v : Vec d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification hr θ w v D)
    (hL : 0 < L) {a : Fin k}
    (ha : a ∈ activeHeads θ ⟨0, hL⟩)
    (hslope : matrixBilin (attentionMatrix θ ⟨0, hL⟩ a) w v ≠ 0) :
    affineSigmoidPoleSet (logScale r)
        (matrixBilin (attentionMatrix θ ⟨0, hL⟩ a) w v) ⊆
      D.stratum 0 := by
  intro τ hτ
  rw [mem_first_stratum_iff hD hL]
  exact ⟨a, ha, hslope, hτ⟩

theorem first_stratum_nonempty_of_active_first_slope_ne_zero {r L k d : Nat}
    {hr : 1 < r} {θ : Params L k d} {w v : Vec d}
    {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification hr θ w v D)
    (hL : 0 < L) {a : Fin k}
    (ha : a ∈ activeHeads θ ⟨0, hL⟩)
    (hslope : matrixBilin (attentionMatrix θ ⟨0, hL⟩ a) w v ≠ 0) :
    (D.stratum 0).Nonempty := by
  refine ⟨affineSigmoidPole (logScale r)
    (matrixBilin (attentionMatrix θ ⟨0, hL⟩ a) w v) 0, ?_⟩
  exact affineSigmoidPoleSet_subset_first_stratum hD hL ha hslope
    ⟨(0 : ℤ), rfl⟩

theorem first_stratum_eq_empty_of_first_active_slopes_eq_zero {r L k d : Nat}
    {hr : 1 < r} {θ : Params L k d} {w v : Vec d}
    {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification hr θ w v D)
    (hL : 0 < L)
    (hzero : ∀ a : Fin k, a ∈ activeHeads θ ⟨0, hL⟩ →
      matrixBilin (attentionMatrix θ ⟨0, hL⟩ a) w v = 0) :
    D.stratum 0 = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.2
  intro τ hτ
  rw [mem_first_stratum_iff hD hL] at hτ
  rcases hτ with ⟨a, ha, hslope, _hτ⟩
  exact hslope (hzero a ha)

theorem first_stratum_avoids_real {r L k d : Nat} {hr : 1 < r}
    {θ : Params L k d} {w v : Vec d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification hr θ w v D)
    (hL : 0 < L) (x : ℝ) :
    (x : ℂ) ∉ D.stratum 0 := by
  intro hx
  rw [mem_first_stratum_iff hD hL] at hx
  rcases hx with ⟨a, _ha, hslope, hpole⟩
  exact ofReal_notMem_affineSigmoidPoleSet (logScale r)
    (matrixBilin (attentionMatrix θ ⟨0, hL⟩ a) w v) x hslope hpole

theorem first_stratum_closedDiscrete_univ {r L k d : Nat} {hr : 1 < r}
    {θ : Params L k d} {w v : Vec d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification hr θ w v D)
    (hL : 0 < L) :
    ClosedDiscreteIn (D.stratum 0) Set.univ := by
  simpa [hD.omega_zero] using hD.stratum_closedDiscrete ⟨0, hL⟩

theorem first_stratum_countable {r L k d : Nat} {hr : 1 < r}
    {θ : Params L k d} {w v : Vec d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification hr θ w v D)
    (hL : 0 < L) :
    (D.stratum 0).Countable :=
  (first_stratum_closedDiscrete_univ hD hL).countable

theorem level_notMem_Pi_on_nonnegativeRealAxis {r L k d : Nat} {hr : 1 < r}
    {θ : Params L k d} {w v : Vec d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification hr θ w v D)
    {l : Fin L} {a : Fin k} (ha : a ∈ activeHeads θ l)
    {τ : ℂ} (hτ : τ ∈ nonnegativeRealAxis) :
    D.level (l, a) τ ∉ Pi := by
  rcases hD.level_real_on_nonnegative_axis l a ha τ hτ with ⟨x, hx⟩
  rw [hx]
  exact ofReal_notMem_Pi x

theorem stratum_disjoint_nonnegativeRealAxis {r L k d : Nat} {hr : 1 < r}
    {θ : Params L k d} {w v : Vec d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification hr θ w v D) (l : Fin L) :
    Disjoint (D.stratum l.1) nonnegativeRealAxis := by
  rw [Set.disjoint_left]
  intro τ hτS hτAxis
  rw [hD.stratum_eq l] at hτS
  simp [reducedStratumAt] at hτS
  rcases hτS with ⟨a, ha, _hτΩ, hτPi⟩
  have haMem : a ∈ activeHeads θ l := by
    simpa using ha
  exact level_notMem_Pi_on_nonnegativeRealAxis (hD := hD) (l := l) (a := a)
    (ha := haMem) hτAxis hτPi

theorem stratum_subset_omega {r L k d : Nat} {hr : 1 < r}
    {θ : Params L k d} {w v : Vec d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification hr θ w v D) (l : Fin L) :
    D.stratum l.1 ⊆ D.Omega l.1 := by
  rw [hD.stratum_eq l]
  exact reducedStratumAt_subset_omega θ D l

theorem stratum_countable {r L k d : Nat} {hr : 1 < r}
    {θ : Params L k d} {w v : Vec d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification hr θ w v D) (l : Fin L) :
    (D.stratum l.1).Countable :=
  (hD.stratum_closedDiscrete l).countable

theorem stratum_noAccumIn {r L k d : Nat} {hr : 1 < r}
    {θ : Params L k d} {w v : Vec d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification hr θ w v D) (l : Fin L) :
    NoAccumIn (D.stratum l.1) (D.Omega l.1) :=
  (hD.stratum_closedDiscrete l).noAccumIn

theorem stratum_eq_empty_of_activeHeads_eq_empty {r L k d : Nat} {hr : 1 < r}
    {θ : Params L k d} {w v : Vec d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification hr θ w v D) {l : Fin L}
    (hactive : activeHeads θ l = ∅) :
    D.stratum l.1 = ∅ := by
  rw [hD.stratum_eq l]
  exact reducedStratumAt_eq_empty_of_activeHeads_eq_empty D hactive

theorem stratum_closedDiscrete_partialUnion_compl {r L k d : Nat} {hr : 1 < r}
    {θ : Params L k d} {w v : Vec d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification hr θ w v D)
    {j : Nat} (hj : j < L) :
    ClosedDiscreteIn (D.stratum j) (partialUnion D.stratum j)ᶜ := by
  let l : Fin L := ⟨j, hj⟩
  have hjle : j ≤ L := Nat.le_of_lt hj
  have hΩ : D.Omega j = (partialUnion D.stratum j)ᶜ :=
    omega_eq_partialUnion_compl_derived hD j hjle
  have hCD : ClosedDiscreteIn (D.stratum j) (D.Omega j) := by
    simpa [l] using
      stratum_closedDiscrete_of_level_zero_data (r := r) θ D l (hD.stratum_eq l)
        (hD.domain j hjle)
        (zero_mem_of_nonnegativeRealAxis_subset (hD.nonnegative_axis_subset j hjle))
        (fun a ha => hD.level_holomorphic l a ha)
        (fun a ha => hD.level_zero l a ha)
  simpa [hΩ] using hCD

theorem strataSystem_of_activeHeadSingularStratification {r L k d : Nat} {hr : 1 < r}
    {θ : Params L k d} {w v : Vec d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification hr θ w v D) :
    StrataSystem D.stratum L := by
  exact strataSystem_of_level_zero_axis_data (r := r) θ D hD.omega_zero hD.omega_succ
    hD.domain hD.nonnegative_axis_subset hD.stratum_eq hD.level_holomorphic
    hD.level_zero

theorem reducedSingularSet_closed {r L k d : Nat} {hr : 1 < r}
    {θ : Params L k d} {w v : Vec d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification hr θ w v D) :
    IsClosed (reducedSingularSet D) := by
  simpa [reducedSingularSet] using
    (strataSystem_of_activeHeadSingularStratification hD).closed_partial L le_rfl

theorem reducedSingularSet_countable {r L k d : Nat} {hr : 1 < r}
    {θ : Params L k d} {w v : Vec d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification hr θ w v D) :
    (reducedSingularSet D).Countable := by
  unfold reducedSingularSet
  exact TransformerIdentifiability.NLayer.partialUnion_countable_of_strata_countable
    (S := D.stratum) (m := L)
    (fun j hj => by
      let l : Fin L := ⟨j, hj⟩
      simpa [l] using (hD.stratum_closedDiscrete l).countable)
    L le_rfl

theorem finalOmega_eq_compl_reducedSingularSet {r L k d : Nat} {hr : 1 < r}
    {θ : Params L k d} {w v : Vec d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification hr θ w v D) :
    D.Omega L = (reducedSingularSet D)ᶜ := by
  simpa [reducedSingularSet] using omega_eq_partialUnion_compl_derived hD L le_rfl

theorem reducedSingularSet_compl_planeDomain {r L k d : Nat} {hr : 1 < r}
    {θ : Params L k d} {w v : Vec d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification hr θ w v D) :
    PlaneDomain (reducedSingularSet D)ᶜ := by
  simpa [← finalOmega_eq_compl_reducedSingularSet hD] using hD.domain L le_rfl

/-- The positive real ray is contained in the final reduced domain. -/
theorem positiveRealAxis_subset_finalOmegaDomain {r L k d : Nat} {hr : 1 < r}
    {θ : Params L k d} {w v : Vec d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification hr θ w v D) :
    positiveRealAxis ⊆ D.Omega L :=
  positiveRealAxis_subset_of_nonnegativeRealAxis_subset
    (hD.nonnegative_axis_subset L le_rfl)

theorem nonnegativeRealAxis_subset_finalOmega {r L k d : Nat} {hr : 1 < r}
    {θ : Params L k d} {w v : Vec d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification hr θ w v D) :
    nonnegativeRealAxis ⊆ (reducedSingularSet D)ᶜ := by
  simpa [← finalOmega_eq_compl_reducedSingularSet hD] using
    hD.nonnegative_axis_subset L le_rfl

/-- The positive real ray is contained in the complement of the reduced singular set. -/
theorem positiveRealAxis_subset_reducedSingularSet_compl {r L k d : Nat} {hr : 1 < r}
    {θ : Params L k d} {w v : Vec d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification hr θ w v D) :
    positiveRealAxis ⊆ (reducedSingularSet D)ᶜ :=
  positiveRealAxis_subset_of_nonnegativeRealAxis_subset
    (nonnegativeRealAxis_subset_finalOmega hD)

theorem reducedSingularSet_disjoint_nonnegativeRealAxis {r L k d : Nat} {hr : 1 < r}
    {θ : Params L k d} {w v : Vec d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification hr θ w v D) :
    Disjoint (reducedSingularSet D) nonnegativeRealAxis := by
  rw [Set.disjoint_left]
  intro τ hτS hτAxis
  rcases hτS with ⟨j, hj, hτj⟩
  let l : Fin L := ⟨j, hj⟩
  have hdisj := stratum_disjoint_nonnegativeRealAxis (hD := hD) l
  rw [Set.disjoint_left] at hdisj
  exact hdisj (by simpa [l] using hτj) hτAxis

/-- The reduced singular set is disjoint from the positive real ray. -/
theorem reducedSingularSet_disjoint_positiveRealAxis {r L k d : Nat} {hr : 1 < r}
    {θ : Params L k d} {w v : Vec d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification hr θ w v D) :
    Disjoint (reducedSingularSet D) positiveRealAxis := by
  rw [Set.disjoint_left]
  intro τ hτS hτPos
  exact positiveRealAxis_subset_reducedSingularSet_compl hD hτPos hτS

/-- Identity-theorem uniqueness on the final reduced domain, specialized to the strong
active-head stratification interface. -/
theorem complexVec_eqOn_finalOmega_of_positiveRealAxis_eq {r L k d : Nat} {hr : 1 < r}
    {θ : Params L k d} {w v : Vec d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification hr θ w v D)
    {F G : ℂ → ComplexVec d}
    (hF : ∀ i : Fin d, AnalyticOnNhd ℂ (fun τ => F τ i) (D.Omega L))
    (hG : ∀ i : Fin d, AnalyticOnNhd ℂ (fun τ => G τ i) (D.Omega L))
    (hEq : ∀ τ : ℝ, 0 < τ → F (τ : ℂ) = G (τ : ℂ)) :
    Set.EqOn F G (D.Omega L) :=
  complexVec_eqOn_of_positiveRealAxis_eq D (hD.domain L le_rfl)
    (positiveRealAxis_subset_finalOmegaDomain hD) hF hG hEq

/-- Positive-real probe-output semantics packaged as an `EqOn` statement on the positive
ray. -/
theorem observable_eq_probeOutput_on_positiveRealAxis {r L k d : Nat} {hr : 1 < r}
    {θ : Params L k d} {w v : Vec d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification hr θ w v D) :
    Set.EqOn D.observable
      (fun τ : ℂ => realVecToComplex (probeOutput r θ w v τ.re))
      positiveRealAxis := by
  intro τ hτ
  rcases hτ with ⟨t, ht, rfl⟩
  simp [hD.observable_positive_real_eq_probeOutput t ht]

/-- A holomorphic vector-valued function that agrees with the continued observable on the
positive real ray agrees with it throughout the final reduced domain. -/
theorem observable_unique_of_eqOn_positiveRealAxis {r L k d : Nat} {hr : 1 < r}
    {θ : Params L k d} {w v : Vec d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification hr θ w v D)
    {G : ℂ → ComplexVec d}
    (hG : ∀ i : Fin d, AnalyticOnNhd ℂ (fun τ => G τ i) (D.Omega L))
    (hEq : Set.EqOn G D.observable positiveRealAxis) :
    Set.EqOn G D.observable (D.Omega L) :=
  complexVec_eqOn_of_eqOn_positiveRealAxis D (hD.domain L le_rfl)
    (positiveRealAxis_subset_finalOmegaDomain hD) hG hD.observable_holomorphic hEq

/-- Pointwise form of the observable uniqueness field. -/
theorem observable_unique_point {r L k d : Nat} {hr : 1 < r}
    {θ : Params L k d} {w v : Vec d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification hr θ w v D)
    {G : ℂ → ComplexVec d}
    (hG : ∀ i : Fin d, AnalyticOnNhd ℂ (fun τ => G τ i) (D.Omega L))
    (hEq : ∀ τ : ℝ, 0 < τ → G (τ : ℂ) = realVecToComplex (probeOutput r θ w v τ))
    {τ : ℂ} (hτ : τ ∈ D.Omega L) :
    G τ = D.observable τ :=
  hD.observable_unique G hG hEq hτ

/-- Observable uniqueness rewritten on the reduced singular complement. -/
theorem observable_unique_on_reducedSingularSet_compl {r L k d : Nat} {hr : 1 < r}
    {θ : Params L k d} {w v : Vec d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification hr θ w v D)
    {G : ℂ → ComplexVec d}
    (hG : ∀ i : Fin d, AnalyticOnNhd ℂ (fun τ => G τ i) (D.Omega L))
    (hEq : ∀ τ : ℝ, 0 < τ → G (τ : ℂ) = realVecToComplex (probeOutput r θ w v τ)) :
    Set.EqOn G D.observable (reducedSingularSet D)ᶜ := by
  simpa [← finalOmega_eq_compl_reducedSingularSet hD] using
    hD.observable_unique G hG hEq

theorem reducedSingularSet_accumulation_subset {r L k d q : Nat} {hr : 1 < r}
    {θ : Params L k d} {w v : Vec d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification hr θ w v D) (hq : q ≤ L) :
    accIter q (reducedSingularSet D) ⊆ partialUnion D.stratum (L - q) := by
  simpa [reducedSingularSet] using
    TransformerIdentifiability.NLayer.accIter_partialUnion_subset
      (strataSystem_of_activeHeadSingularStratification hD) q hq

theorem reducedSingularSet_accIter_empty {r L k d : Nat} {hr : 1 < r}
    {θ : Params L k d} {w v : Vec d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification hr θ w v D) :
    accIter L (reducedSingularSet D) = ∅ := by
  simpa [reducedSingularSet] using
    TransformerIdentifiability.NLayer.accIter_partialUnion_eq_empty
      (strataSystem_of_activeHeadSingularStratification hD)

theorem stratum_eq_fullStratumAt_of_all_heads_active {r L k d : Nat} {hr : 1 < r}
    {θ : Params L k d} {w v : Vec d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification hr θ w v D)
    (hθ : AllHeadsActive θ) (l : Fin L) :
    D.stratum l.1 = fullStratumAt D l := by
  rw [hD.stratum_eq l]
  exact reducedStratumAt_eq_fullStratumAt_of_all_heads_active D hθ l

/-- Weak structural scaffold retained for downstream experimentation.  This is not the
TeX proposition and deliberately does not mention probes, real-axis semantics, actual
recursion, or observable continuation. -/
structure StructuralActiveHeadStratification {L k d : Nat} (θ : Params L k d)
    (D : ActiveStratificationData L k d) : Prop where
  omega_zero : D.Omega 0 = Set.univ
  stratum_eq : ∀ l : Fin L, D.stratum l.1 = reducedStratumAt θ D l
  omega_succ : ∀ l : Fin L, D.Omega (l.1 + 1) = D.Omega l.1 \ D.stratum l.1
  stratum_closedDiscrete : ∀ l : Fin L, ClosedDiscreteIn (D.stratum l.1) (D.Omega l.1)
  nonnegative_axis_subset : ∀ n : Nat, n ≤ L → nonnegativeRealAxis ⊆ D.Omega n
  level_holomorphic : ∀ l : Fin L, ∀ a ∈ activeHeads θ l,
    AnalyticOnNhd ℂ (D.level (l, a)) (D.Omega l.1)
  gate_formula : ∀ l : Fin L, ∀ a ∈ activeHeads θ l,
    Set.EqOn (D.gate (l, a)) (fun τ => csig (D.level (l, a) τ))
      (D.Omega (l.1 + 1))
  observable_holomorphic :
    ∀ i : Fin d, AnalyticOnNhd ℂ (fun τ => D.observable τ i) (D.Omega L)

theorem structuralActiveHeadStratification_of_activeHeadSingularStratification
    {r L k d : Nat} {hr : 1 < r}
    {θ : Params L k d} {w v : Vec d} {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification hr θ w v D) :
    StructuralActiveHeadStratification θ D where
  omega_zero := hD.omega_zero
  stratum_eq := hD.stratum_eq
  omega_succ := hD.omega_succ
  stratum_closedDiscrete := hD.stratum_closedDiscrete
  nonnegative_axis_subset := hD.nonnegative_axis_subset
  level_holomorphic := hD.level_holomorphic
  gate_formula := hD.gate_formula
  observable_holomorphic := hD.observable_holomorphic

/-- A concrete empty-strata witness for the weak structural scaffold only. -/
noncomputable def emptyActiveStratificationData (L k d : Nat) :
    ActiveStratificationData L k d where
  Omega := fun _ => Set.univ
  stratum := fun _ => ∅
  level := fun _ _ => 0
  gate := fun _ _ => csig 0
  observable := fun _ _ => 0

/-- The empty-strata witness satisfies only the weak structural scaffold. -/
theorem emptyActiveStratificationData_structural_spec {L k d : Nat} (θ : Params L k d) :
    StructuralActiveHeadStratification θ (emptyActiveStratificationData L k d) := by
  classical
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l
    ext τ
    simp [emptyActiveStratificationData, reducedStratumAt, zero_notMem_Pi]
  · intro l
    simp [emptyActiveStratificationData]
  · intro l
    simpa [emptyActiveStratificationData] using
      (closedDiscreteIn_empty (U := Set.univ) isOpen_univ)
  · intro n hn z hz
    simp [emptyActiveStratificationData]
  · intro l a ha τ hτ
    simpa [emptyActiveStratificationData] using
      (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) τ)
  · intro l a ha τ hτ
    simp [emptyActiveStratificationData]
  · intro i τ hτ
    simpa [emptyActiveStratificationData] using
      (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) τ)

end ReducedStratificationAPI

end TransformerIdentifiability.NLayer.KHead
