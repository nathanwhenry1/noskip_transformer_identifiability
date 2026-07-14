import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Analytic.FormalPolySplit

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.NoSkip

/-!
# No-skip level / gate recurrence realization

The no-skip `ActiveStratificationData` (in `Analytic/ActiveStratification.lean`)
carries `level`/`gate : FormalVar L k → ℂ → ℂ` as *opaque* fields, and the
constructor `activeStratificationDataOfFunctions` accepts arbitrary such
functions.  This file builds the concrete recursive realization that satisfies
the model recurrence, so that the "successor level model" (used by NS104/NS106
as a standing hypothesis) becomes a theorem for the constructed data.

The construction mirrors the KHead `activeConstructedGate`/`activeConstructedLevel`
tower (`KHead/Analytic/ActiveStratification.lean`), ported to the no-skip
`formalSlope`/`complexFormalSlope`/`formalLevel` API.  Its only model-specific
input is `NoSkip.formalSlope`, whose *strict prefix support* (NS031,
`formalSlope_dependsOnLayersBefore`) makes the layer recursion well-founded: the
formal slope at head `(l,a)` depends only on gate variables of layers `< l`.

Main declarations:

* `nsActiveGate`, `nsActiveLevel` — the concrete gate/level functions.
* `nsActiveGate_eq_csig_level` — `gate = csig(level)` at active heads.
* `nsActiveLevel_formula` — the affine level formula `τ·φ + log r`.
* `nsActiveHeadSingularStratification` — the assembled concrete
  `ActiveHeadSingularStratification` for the constructed data.
-/

noncomputable section

variable {r L k d : Nat}

/-! ## Model-neutral helpers reproved for the no-skip API -/

/-- Complex evaluation of a formal polynomial at a fully real assignment is real. -/
theorem evalFormalPolyComplex_real_of_real_assignment {L k : Nat}
    {η : FormalVar L k → ℂ} (p : FormalPoly L k)
    (hη : ∀ x : FormalVar L k, ∃ t : ℝ, η x = t) :
    ∃ t : ℝ, evalFormalPolyComplex η p = t := by
  classical
  choose ηr hηr using hη
  have hηeq : η = fun x => (ηr x : ℂ) := by
    funext x; exact hηr x
  refine ⟨MvPolynomial.eval ηr p, ?_⟩
  rw [hηeq]
  exact evalFormalPolyComplex_ofReal ηr p

/-! The following complex-evaluation adapters make precise the fact that formal
streams and slopes only depend on active gate coordinates.  Inactive coordinates
multiply a zero value matrix, so changing them cannot change a stream. -/

@[simp] theorem evalFormalVecComplex_realVecToFormal {L k d : Nat}
    (η : FormalVar L k → ℂ) (x : Vec d) :
    evalFormalVecComplex η (realVecToFormal (L := L) (k := k) x) =
      fun i => (x i : ℂ) := by
  ext i
  simp [evalFormalVecComplex, evalFormalPolyComplex, realVecToFormal, formalConst]

theorem evalFormalVecComplex_ofReal {L k d : Nat}
    (η : FormalVar L k → ℝ) (x : FormalVec L k d) :
    evalFormalVecComplex (fun y => (η y : ℂ)) x =
      fun i => (evalFormalVec η x i : ℂ) := by
  ext i
  simp [evalFormalVecComplex, evalFormalVec, evalFormalPolyComplex_ofReal]

noncomputable def nsStreamEvalFormalMatrixComplex {L k d : Nat}
    (η : FormalVar L k → ℂ)
    (M : Matrix (Fin d) (Fin d) (FormalPoly L k)) :
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

@[simp] theorem nsStreamEvalFormalMatrixComplex_add {L k d : Nat}
    (η : FormalVar L k → ℂ)
    (M N : Matrix (Fin d) (Fin d) (FormalPoly L k)) :
    nsStreamEvalFormalMatrixComplex η (M + N) =
      nsStreamEvalFormalMatrixComplex η M + nsStreamEvalFormalMatrixComplex η N := by
  ext i j
  simp [nsStreamEvalFormalMatrixComplex, evalFormalPolyComplex]

@[simp] theorem nsStreamEvalFormalMatrixComplex_sub {L k d : Nat}
    (η : FormalVar L k → ℂ)
    (M N : Matrix (Fin d) (Fin d) (FormalPoly L k)) :
    nsStreamEvalFormalMatrixComplex η (M - N) =
      nsStreamEvalFormalMatrixComplex η M - nsStreamEvalFormalMatrixComplex η N := by
  ext i j
  simp [nsStreamEvalFormalMatrixComplex, evalFormalPolyComplex]

@[simp] theorem evalFormalVecComplex_mulVec {L k d : Nat}
    (η : FormalVar L k → ℂ)
    (M : Matrix (Fin d) (Fin d) (FormalPoly L k)) (x : FormalVec L k d) :
    evalFormalVecComplex η (M *ᵥ x) =
      nsStreamEvalFormalMatrixComplex η M *ᵥ evalFormalVecComplex η x := by
  ext i
  simp [evalFormalVecComplex, nsStreamEvalFormalMatrixComplex, evalFormalPolyComplex,
    Matrix.mulVec, dotProduct]

@[simp] theorem nsStreamEvalFormalMatrixComplex_realMatrixToFormal {L k d : Nat}
    (η : FormalVar L k → ℂ) (M : Matrix (Fin d) (Fin d) ℝ) :
    nsStreamEvalFormalMatrixComplex η (realMatrixToFormal (L := L) (k := k) M) =
      M.map (algebraMap ℝ ℂ) := by
  ext i j
  simp [nsStreamEvalFormalMatrixComplex, realMatrixToFormal, evalFormalPolyComplex]

@[simp] theorem nsStreamEvalFormalMatrixComplex_formalCollapseMatrix {L k d : Nat}
    (η : FormalVar L k → ℂ) (θ : Params L k d) (l : Fin L) :
    nsStreamEvalFormalMatrixComplex η (formalCollapseMatrix θ l) =
      (collapseMatrix θ l).map (algebraMap ℝ ℂ) := by
  simp [formalCollapseMatrix]

@[simp] theorem nsStreamEvalFormalMatrixComplex_formalGatedValueSum {L k d : Nat}
    (η : FormalVar L k → ℂ) (θ : Params L k d) (l : Fin L) :
    nsStreamEvalFormalMatrixComplex η (formalGatedValueSum θ l) =
      ∑ a : Fin k, η (l, a) •
        (valueMatrix θ l a).map (algebraMap ℝ ℂ) := by
  ext i j
  simp [nsStreamEvalFormalMatrixComplex, formalGatedValueSum, formalGate,
    formalValueMatrix, realMatrixToFormal, evalFormalPolyComplex,
    Matrix.sum_apply, Matrix.smul_apply]

theorem nsStreamEvalFormalMatrixComplex_formalGatedValueSum_eq_of_eq_on_active
    {L k d : Nat} {θ : Params L k d} {l : Fin L}
    {η η' : FormalVar L k → ℂ}
    (hη : ∀ a : Fin k, a ∈ activeHeads θ l → η (l, a) = η' (l, a)) :
    nsStreamEvalFormalMatrixComplex η (formalGatedValueSum θ l) =
      nsStreamEvalFormalMatrixComplex η' (formalGatedValueSum θ l) := by
  classical
  rw [nsStreamEvalFormalMatrixComplex_formalGatedValueSum,
    nsStreamEvalFormalMatrixComplex_formalGatedValueSum]
  refine Finset.sum_congr rfl ?_
  intro a _ha
  by_cases hactive : a ∈ activeHeads θ l
  · simp [hη a hactive]
  · have hV : valueMatrix θ l a = 0 :=
      (not_mem_activeHeads_iff_valueMatrix_eq_zero θ l a).1 hactive
    simp [hV]

theorem evalFormalPolyComplex_formalBilin {L k d : Nat}
    (η : FormalVar L k → ℂ) (A : Matrix (Fin d) (Fin d) ℝ)
    (w v : FormalVec L k d) :
    evalFormalPolyComplex η (formalBilin A w v) =
      evalFormalVecComplex η w ⬝ᵥ (A.map (algebraMap ℝ ℂ)) *ᵥ
        evalFormalVecComplex η v := by
  simp [formalBilin, evalFormalVecComplex, evalFormalPolyComplex,
    realMatrixToFormal, Matrix.mulVec, dotProduct]

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
  have hD :=
    nsStreamEvalFormalMatrixComplex_formalGatedValueSum_eq_of_eq_on_active hη
  constructor
  · simp [formalStepPoint, hD, hw]
  · simp [formalStepPoint, hD, hw, hv]

theorem eval_formalPointComplex_eq_of_eq_on_active {L k d : Nat}
    {θ : Params L k d} (η η' : FormalVar L k → ℂ)
    (w v : Vec d) :
    ∀ (q : Nat) (hq : q ≤ L),
      (∀ (l : Fin L) (a : Fin k), l.1 < q → a ∈ activeHeads θ l →
        η (l, a) = η' (l, a)) →
        evalFormalVecComplex η (formalPoint θ w v q hq).1 =
            evalFormalVecComplex η' (formalPoint θ w v q hq).1 ∧
          evalFormalVecComplex η (formalPoint θ w v q hq).2 =
            evalFormalVecComplex η' (formalPoint θ w v q hq).2
  | 0, _hq, _hη => by simp [formalPoint]
  | q + 1, hq, hη => by
      let l : Fin L := ⟨q, Nat.lt_of_succ_le hq⟩
      have hprev := eval_formalPointComplex_eq_of_eq_on_active η η' w v q
        (Nat.le_of_succ_le hq)
        (fun l' a hl' ha => hη l' a (Nat.lt_trans hl' (Nat.lt_succ_self q)) ha)
      have hstep := eval_formalStepPointComplex_eq_of_eq_on_active (θ := θ) η η'
        (l := l)
        (w := (formalPoint θ w v q (Nat.le_of_succ_le hq)).1)
        (v := (formalPoint θ w v q (Nat.le_of_succ_le hq)).2)
        (fun a ha => hη l a (by simp [l]) ha) hprev.1 hprev.2
      simpa [formalPoint, l] using hstep

theorem evalFormalPolyComplex_formalSlope_eq_of_eq_on_active {L k d : Nat}
    {θ : Params L k d} (η η' : FormalVar L k → ℂ)
    (w v : Vec d) (l : Fin L) (a : Fin k)
    (hη : ∀ (l' : Fin L) (a' : Fin k), l'.1 < l.1 →
      a' ∈ activeHeads θ l' → η (l', a') = η' (l', a')) :
    evalFormalPolyComplex η (formalSlope θ w v l a) =
      evalFormalPolyComplex η' (formalSlope θ w v l a) := by
  have hprev := eval_formalPointComplex_eq_of_eq_on_active (θ := θ)
    η η' w v l.1 (Nat.le_of_lt l.2) hη
  have hprev' :
      evalFormalVecComplex η (formalW θ w v l.1 (Nat.le_of_lt l.2)) =
          evalFormalVecComplex η' (formalW θ w v l.1 (Nat.le_of_lt l.2)) ∧
        evalFormalVecComplex η (formalV θ w v l.1 (Nat.le_of_lt l.2)) =
          evalFormalVecComplex η' (formalV θ w v l.1 (Nat.le_of_lt l.2)) := by
    simpa [formalW, formalV] using hprev
  rw [formalSlope, evalFormalPolyComplex_formalBilin,
    evalFormalPolyComplex_formalBilin, hprev'.1, hprev'.2]

/-- Analyticity on a larger set restricts to any subset. -/
theorem analyticOnNhd_mono {F : ℂ → ℂ} {U V : Set ℂ}
    (hF : AnalyticOnNhd ℂ F U) (hVU : V ⊆ U) :
    AnalyticOnNhd ℂ F V := fun τ hτ => hF τ (hVU hτ)

/-- Recursive domains are antitone in the layer index. -/
theorem omega_subset_of_le_of_omega_succ {L k d : Nat}
    (D : ActiveStratificationData L k d)
    (hsucc : ∀ l : Fin L, D.Omega (l.1 + 1) = D.Omega l.1 \ D.stratum l.1) :
    ∀ {m n : Nat}, m ≤ n → n ≤ L → D.Omega n ⊆ D.Omega m
  | m, 0, hmn, _hn => by
      have hm : m = 0 := by omega
      subst m; exact Set.Subset.rfl
  | m, n + 1, hmn, hn => by
      by_cases hmle : m ≤ n
      · intro τ hτ
        have hnL : n < L := Nat.lt_of_succ_le hn
        let l : Fin L := ⟨n, hnL⟩
        have hτn : τ ∈ D.Omega n := by
          have hτ' := hτ; rw [hsucc l] at hτ'; exact hτ'.1
        exact omega_subset_of_le_of_omega_succ D hsucc hmle
          (Nat.le_of_succ_le hn) hτn
      · have hm : m = n + 1 := by omega
        subst m; exact Set.Subset.rfl

/-! ## The layer-recursive gate and level -/

/-- Candidate active gate continuation.  Defined by well-founded recursion on the
layer index: constructing head `(l,a)` uses only gates of earlier layers (the
formal slope at `(l,a)` has strict prefix support).  Inactive heads are `0`. -/
noncomputable def nsActiveGate {r L k d : Nat}
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

/-- Candidate active level continuation built from earlier constructed gates. -/
noncomputable def nsActiveLevel {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (x : FormalVar L k) (τ : ℂ) : ℂ :=
  τ * evalFormalPolyComplex
    (fun y => if _hy : y.1.1 < x.1.1 then nsActiveGate (r := r) θ w v y τ else 0)
    (formalSlope θ w v x.1 x.2) + (logScale r : ℂ)

/-- Gate → level recurrence at an active head: `gate = csig(level)`. -/
theorem nsActiveGate_eq_csig_level {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) {x : FormalVar L k}
    (hx : IsActiveVar θ x) (τ : ℂ) :
    nsActiveGate (r := r) θ w v x τ =
      csig (nsActiveLevel (r := r) θ w v x τ) := by
  classical
  unfold nsActiveLevel
  rw [nsActiveGate, WellFounded.fix_eq]
  simp [hx]

/-- Inactive heads carry the zero gate. -/
theorem nsActiveGate_eq_zero_of_inactive {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) {x : FormalVar L k}
    (hx : ¬ IsActiveVar θ x) (τ : ℂ) :
    nsActiveGate (r := r) θ w v x τ = 0 := by
  classical
  rw [nsActiveGate, WellFounded.fix_eq]
  simp [hx]

/-- Evaluating a strict-prefix-support formal slope, the layer guard `y.1.1 < x.1.1`
is invisible: it agrees with the unguarded assignment. -/
theorem evalFormalSlope_dguard_eq {L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (x : FormalVar L k)
    (g : FormalVar L k → ℂ) :
    evalFormalPolyComplex
        (fun y => if _hy : y.1.1 < x.1.1 then g y else 0)
        (formalSlope θ w v x.1 x.2) =
      evalFormalPolyComplex g (formalSlope θ w v x.1 x.2) := by
  apply evalFormalPolyComplex_congr_on_vars
  intro z hz
  have hlt : z.1.1 < x.1.1 := formalSlope_dependsOnLayersBefore θ w v x.1 x.2 z hz
  simp [hlt]

/-- **The affine level formula.**  The constructed level is
`τ · φ_{la}(gates) + log r` where `φ` is the (unguarded) complex formal slope. -/
theorem nsActiveLevel_formula {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (x : FormalVar L k) (τ : ℂ) :
    nsActiveLevel (r := r) θ w v x τ =
      τ * evalFormalPolyComplex (fun y => nsActiveGate (r := r) θ w v y τ)
        (formalSlope θ w v x.1 x.2) + (logScale r : ℂ) := by
  rw [nsActiveLevel, evalFormalSlope_dguard_eq]

/-- The affine level formula in terms of `complexFormalSlope`/`formalLevel`. -/
theorem nsActiveLevel_eq_formalLevel {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (x : FormalVar L k) (τ : ℂ) :
    nsActiveLevel (r := r) θ w v x τ =
      formalLevel (r := r) θ w v (fun y => nsActiveGate (r := r) θ w v y τ) x τ := by
  rw [nsActiveLevel_formula, formalLevel, complexFormalSlope]

/-- Constructed levels take the bias value at the origin. -/
@[simp] theorem nsActiveLevel_zero {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (x : FormalVar L k) :
    nsActiveLevel (r := r) θ w v x 0 = (logScale r : ℂ) := by
  simp [nsActiveLevel]

/-! ## Real-valuedness on the nonnegative real axis -/

/-- The constructed levels and gates are real-valued on the nonnegative real axis. -/
theorem nsActiveLevel_gate_real_on_nonnegativeRealAxis {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) :
    ∀ x : FormalVar L k,
      IsRealValuedOn (nsActiveLevel (r := r) θ w v x) nonnegativeRealAxis ∧
      IsRealValuedOn (nsActiveGate (r := r) θ w v x) nonnegativeRealAxis := by
  classical
  let P : FormalVar L k → Prop := fun x =>
    IsRealValuedOn (nsActiveLevel (r := r) θ w v x) nonnegativeRealAxis ∧
      IsRealValuedOn (nsActiveGate (r := r) θ w v x) nonnegativeRealAxis
  change ∀ x : FormalVar L k, P x
  intro x
  refine (measure (fun x : FormalVar L k => x.1.1)).wf.induction (C := P) x ?_
  intro x ih
  have hlevel :
      IsRealValuedOn (nsActiveLevel (r := r) θ w v x) nonnegativeRealAxis := by
    intro τ hτ
    rcases hτ with ⟨t, ht, rfl⟩
    have hη :
        ∀ y : FormalVar L k,
          ∃ u : ℝ,
            (if _hy : y.1.1 < x.1.1 then
                nsActiveGate (r := r) θ w v y (t : ℂ)
              else 0) = (u : ℂ) := by
      intro y
      by_cases hy : y.1.1 < x.1.1
      · rcases (ih y (by simpa [measure] using hy)).2 (t : ℂ) ⟨t, ht, rfl⟩ with ⟨u, hu⟩
        exact ⟨u, by simpa [hy] using hu⟩
      · exact ⟨0, by simp [hy]⟩
    rcases evalFormalPolyComplex_real_of_real_assignment
        (formalSlope θ w v x.1 x.2) hη with ⟨s, hs⟩
    refine ⟨t * s + logScale r, ?_⟩
    calc
      nsActiveLevel (r := r) θ w v x (t : ℂ)
          = (t : ℂ) * (s : ℂ) + (logScale r : ℂ) := by rw [nsActiveLevel, hs]
      _ = ((t * s + logScale r : ℝ) : ℂ) := by norm_num
  have hgate :
      IsRealValuedOn (nsActiveGate (r := r) θ w v x) nonnegativeRealAxis := by
    intro τ hτ
    by_cases hx : IsActiveVar θ x
    · rcases hlevel τ hτ with ⟨u, hu⟩
      refine ⟨TransformerIdentifiability.NLayer.sig u, ?_⟩
      rw [nsActiveGate_eq_csig_level θ w v hx τ, hu]
      simpa using TransformerIdentifiability.NLayer.csig_ofReal u
    · exact ⟨0, by simpa using nsActiveGate_eq_zero_of_inactive (r := r) θ w v hx τ⟩
  exact ⟨hlevel, hgate⟩

theorem nsActiveLevel_real_on_nonnegativeRealAxis {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (x : FormalVar L k) :
    IsRealValuedOn (nsActiveLevel (r := r) θ w v x) nonnegativeRealAxis :=
  (nsActiveLevel_gate_real_on_nonnegativeRealAxis (r := r) θ w v x).1

/-! ## Holomorphy on the recursive domains -/

/-- The constructed level is holomorphic wherever every prior-layer gate is. -/
theorem nsActiveLevel_analyticOnNhd_of_prior_gate {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (x : FormalVar L k) {U : Set ℂ}
    (hgate : ∀ y : FormalVar L k, y.1.1 < x.1.1 →
      AnalyticOnNhd ℂ (nsActiveGate (r := r) θ w v y) U) :
    AnalyticOnNhd ℂ (nsActiveLevel (r := r) θ w v x) U := by
  classical
  have hη : ∀ y : FormalVar L k,
      AnalyticOnNhd ℂ
        (fun τ => if _hy : y.1.1 < x.1.1 then nsActiveGate (r := r) θ w v y τ else 0) U := by
    intro y
    by_cases hy : y.1.1 < x.1.1
    · simpa [hy] using hgate y hy
    · simpa [hy] using (analyticOnNhd_const (𝕜 := ℂ) (v := (0 : ℂ)) (s := U))
  have hpoly :
      AnalyticOnNhd ℂ
        (fun τ => evalFormalPolyComplex
          (fun y => if _hy : y.1.1 < x.1.1 then nsActiveGate (r := r) θ w v y τ else 0)
          (formalSlope θ w v x.1 x.2)) U :=
    evalFormalPolyComplex_analyticOnNhd (formalSlope θ w v x.1 x.2) hη
  have hid : AnalyticOnNhd ℂ (fun τ : ℂ => τ) U := by
    intro τ _hτ; simpa using (analyticAt_id : AnalyticAt ℂ (fun τ : ℂ => τ) τ)
  have hconst : AnalyticOnNhd ℂ (fun _ : ℂ => (logScale r : ℂ)) U :=
    analyticOnNhd_const (𝕜 := ℂ) (v := (logScale r : ℂ)) (s := U)
  have hform : (nsActiveLevel (r := r) θ w v x) =
      (fun τ : ℂ => τ * evalFormalPolyComplex
        (fun y => if _hy : y.1.1 < x.1.1 then nsActiveGate (r := r) θ w v y τ else 0)
        (formalSlope θ w v x.1 x.2) + (logScale r : ℂ)) := by
    funext τ; rfl
  rw [hform]
  exact (hid.mul hpoly).add hconst

/-- Active gates are holomorphic wherever their level is holomorphic and avoids `Π`. -/
theorem nsActiveGate_analyticOnNhd_of_level {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) {x : FormalVar L k}
    (hx : IsActiveVar θ x) {U : Set ℂ}
    (hlevel : AnalyticOnNhd ℂ (nsActiveLevel (r := r) θ w v x) U)
    (havoid : ∀ τ ∈ U, nsActiveLevel (r := r) θ w v x τ ∉ Pi) :
    AnalyticOnNhd ℂ (nsActiveGate (r := r) θ w v x) U := by
  have hcsig :
      AnalyticOnNhd ℂ csig ((nsActiveLevel (r := r) θ w v x) '' U) := by
    intro z hz
    rcases hz with ⟨τ, hτ, rfl⟩
    exact KHead.csig_analyticAt_of_notMem_Pi (havoid τ hτ)
  have hcomp := hcsig.comp' hlevel
  convert hcomp using 1
  ext τ
  simp [Function.comp, nsActiveGate_eq_csig_level θ w v hx τ]

/-! ## The concrete stratification data -/

/-- Candidate final observable obtained from the constructed active gates. -/
noncomputable def nsObservable {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) : ℂ → ComplexVec d :=
  fun τ => evalFormalVecComplex
    (fun x => nsActiveGate (r := r) θ w v x τ) (formalV θ w v L le_rfl)

/-- The concrete recursive `H/s/Ω/S` candidate for the active stratification. -/
noncomputable def nsActiveStratificationData {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) : ActiveStratificationData L k d :=
  activeStratificationDataOfFunctions θ
    (nsActiveLevel (r := r) θ w v)
    (nsActiveGate (r := r) θ w v)
    (nsObservable (r := r) θ w v)

/-- The observable field of the concrete stratification is definitionally the
evaluation of the terminal no-skip formal stream at the constructed gates. -/
@[simp] theorem nsActiveStratificationData_observable {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (τ : ℂ) :
    (nsActiveStratificationData (r := r) θ w v).observable τ =
      evalFormalVecComplex (fun x => nsActiveGate (r := r) θ w v x τ)
        (formalV θ w v L le_rfl) :=
  rfl

theorem nsActiveStratificationData_recursiveSkeleton {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) :
    ActiveHeadRecursiveSkeleton θ (nsActiveStratificationData (r := r) θ w v) :=
  activeStratificationDataOfFunctions_recursiveSkeleton θ
    (nsActiveLevel (r := r) θ w v) (nsActiveGate (r := r) θ w v)
    (nsObservable (r := r) θ w v)

/-- Domains of the constructed data are antitone in the layer index. -/
theorem nsActiveStratificationData_omega_subset_of_le {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) {m n : Nat} (hmn : m ≤ n) (hn : n ≤ L) :
    (nsActiveStratificationData (r := r) θ w v).Omega n ⊆
      (nsActiveStratificationData (r := r) θ w v).Omega m :=
  omega_subset_of_le_of_omega_succ _
    (nsActiveStratificationData_recursiveSkeleton (r := r) θ w v).omega_succ hmn hn

/-- Membership in the next recursive domain forces the active level to avoid `Π`. -/
theorem nsActiveStratificationData_level_notMem_Pi_on_nextOmega {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (l : Fin L) {a : Fin k}
    (ha : a ∈ activeHeads θ l) {τ : ℂ}
    (hτ : τ ∈ (nsActiveStratificationData (r := r) θ w v).Omega (l.1 + 1)) :
    nsActiveLevel (r := r) θ w v (l, a) τ ∉ Pi :=
  (nsActiveStratificationData_recursiveSkeleton (r := r) θ w v).level_notMem_Pi_on_nextOmega
    l ha hτ

/-- **The core holomorphy induction.**  On its recursive domain each constructed
level is holomorphic, and each active gate is holomorphic on the next domain. -/
theorem nsActiveLevel_gate_analyticOnNhd_recursiveDomain {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) :
    ∀ x : FormalVar L k,
      AnalyticOnNhd ℂ (nsActiveLevel (r := r) θ w v x)
        ((nsActiveStratificationData (r := r) θ w v).Omega x.1.1) ∧
      (IsActiveVar θ x →
        AnalyticOnNhd ℂ (nsActiveGate (r := r) θ w v x)
          ((nsActiveStratificationData (r := r) θ w v).Omega (x.1.1 + 1))) := by
  classical
  set D := nsActiveStratificationData (r := r) θ w v with hDdef
  let P : FormalVar L k → Prop := fun x =>
    AnalyticOnNhd ℂ (nsActiveLevel (r := r) θ w v x) (D.Omega x.1.1) ∧
      (IsActiveVar θ x →
        AnalyticOnNhd ℂ (nsActiveGate (r := r) θ w v x) (D.Omega (x.1.1 + 1)))
  change ∀ x : FormalVar L k, P x
  intro x
  refine (measure (fun x : FormalVar L k => x.1.1)).wf.induction (C := P) x ?_
  intro x ih
  have hlevel :
      AnalyticOnNhd ℂ (nsActiveLevel (r := r) θ w v x) (D.Omega x.1.1) := by
    refine nsActiveLevel_analyticOnNhd_of_prior_gate (r := r) θ w v x ?_
    intro y hy
    by_cases hyactive : IsActiveVar θ y
    · have hgate_y :
          AnalyticOnNhd ℂ (nsActiveGate (r := r) θ w v y) (D.Omega (y.1.1 + 1)) :=
        (ih y (by simpa [measure] using hy)).2 hyactive
      have hsubset : D.Omega x.1.1 ⊆ D.Omega (y.1.1 + 1) :=
        nsActiveStratificationData_omega_subset_of_le (r := r) θ w v
          (m := y.1.1 + 1) (n := x.1.1) (by omega) (Nat.le_of_lt x.1.2)
      exact analyticOnNhd_mono hgate_y hsubset
    · have hconst : AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) (D.Omega x.1.1) :=
        analyticOnNhd_const (𝕜 := ℂ) (v := (0 : ℂ)) (s := D.Omega x.1.1)
      convert hconst using 1
      funext τ
      exact nsActiveGate_eq_zero_of_inactive (r := r) θ w v hyactive τ
  refine ⟨hlevel, ?_⟩
  intro hx
  have hlevel_next :
      AnalyticOnNhd ℂ (nsActiveLevel (r := r) θ w v x) (D.Omega (x.1.1 + 1)) := by
    have hsubset : D.Omega (x.1.1 + 1) ⊆ D.Omega x.1.1 :=
      nsActiveStratificationData_omega_subset_of_le (r := r) θ w v
        (m := x.1.1) (n := x.1.1 + 1) (Nat.le_succ x.1.1) (Nat.succ_le_of_lt x.1.2)
    exact analyticOnNhd_mono hlevel hsubset
  refine nsActiveGate_analyticOnNhd_of_level (r := r) θ w v hx hlevel_next ?_
  intro τ hτ
  have ha : x.2 ∈ activeHeads θ x.1 := by simpa [IsActiveVar] using hx
  have hnot :=
    nsActiveStratificationData_level_notMem_Pi_on_nextOmega (r := r) θ w v x.1 ha hτ
  simpa using hnot

/-! ## Assembling the concrete stratification -/

theorem nsActiveStratificationData_level_holomorphic {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) :
    ∀ l : Fin L, ∀ a : Fin k, a ∈ activeHeads θ l →
      AnalyticOnNhd ℂ
        ((nsActiveStratificationData (r := r) θ w v).level (l, a))
        ((nsActiveStratificationData (r := r) θ w v).Omega l.1) := by
  intro l a _ha
  exact (nsActiveLevel_gate_analyticOnNhd_recursiveDomain (r := r) θ w v (l, a)).1

theorem nsActiveStratificationData_level_real {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) :
    ∀ l : Fin L, ∀ a : Fin k, a ∈ activeHeads θ l →
      IsRealValuedOn
        ((nsActiveStratificationData (r := r) θ w v).level (l, a))
        nonnegativeRealAxis := by
  intro l a _ha
  exact nsActiveLevel_real_on_nonnegativeRealAxis (r := r) θ w v (l, a)

theorem nsActiveStratificationData_level_zero {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) :
    ∀ l : Fin L, ∀ a : Fin k, a ∈ activeHeads θ l →
      (nsActiveStratificationData (r := r) θ w v).level (l, a) 0 = (logScale r : ℂ) := by
  intro l a _ha
  exact nsActiveLevel_zero (r := r) θ w v (l, a)

/-- **Capstone.**  The concrete recursively-constructed data satisfies the full
active singular-head stratification interface. -/
theorem nsActiveHeadSingularStratification {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) :
    ActiveHeadSingularStratification (r := r) θ
      (nsActiveStratificationData (r := r) θ w v) :=
  activeStratificationDataOfFunctions_singularStratification (r := r) θ
    (nsActiveLevel (r := r) θ w v) (nsActiveGate (r := r) θ w v)
    (nsObservable (r := r) θ w v)
    (nsActiveStratificationData_level_holomorphic (r := r) θ w v)
    (nsActiveStratificationData_level_real (r := r) θ w v)
    (nsActiveStratificationData_level_zero (r := r) θ w v)

/-! ## Agreement with the real probe and terminal holomorphy -/

/-- On positive real inputs, every constructed level has the actual no-skip
probe slope, and every active constructed gate is the actual probe gate. -/
theorem nsActiveLevel_gate_positive_real_eq_actual {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) :
    ∀ x : FormalVar L k,
      (∀ τ : ℝ, 0 < τ →
        nsActiveLevel (r := r) θ w v x (τ : ℂ) =
          ((τ * actualProbeSlope r θ w v τ x.1 x.2 + logScale r : ℝ) : ℂ)) ∧
      (IsActiveVar θ x → ∀ τ : ℝ, 0 < τ →
        nsActiveGate (r := r) θ w v x (τ : ℂ) =
          (actualProbeGate r θ w v τ x.1 x.2 : ℂ)) := by
  classical
  let Q : FormalVar L k → Prop := fun x =>
    (∀ τ : ℝ, 0 < τ →
      nsActiveLevel (r := r) θ w v x (τ : ℂ) =
        ((τ * actualProbeSlope r θ w v τ x.1 x.2 + logScale r : ℝ) : ℂ)) ∧
    (IsActiveVar θ x → ∀ τ : ℝ, 0 < τ →
      nsActiveGate (r := r) θ w v x (τ : ℂ) =
        (actualProbeGate r θ w v τ x.1 x.2 : ℂ))
  change ∀ x : FormalVar L k, Q x
  intro x
  refine (measure (fun x : FormalVar L k => x.1.1)).wf.induction (C := Q) x ?_
  intro x ih
  have hlevelAll : ∀ τ : ℝ, 0 < τ →
      nsActiveLevel (r := r) θ w v x (τ : ℂ) =
        ((τ * actualProbeSlope r θ w v τ x.1 x.2 + logScale r : ℝ) : ℂ) := by
    intro τ hτ
    let ηPrior : FormalVar L k → ℂ := fun y =>
      if _hy : y.1.1 < x.1.1 then nsActiveGate (r := r) θ w v y (τ : ℂ) else 0
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
      nsActiveLevel (r := r) θ w v x (τ : ℂ) =
          (τ : ℂ) * evalFormalPolyComplex ηPrior
            (formalSlope θ w v x.1 x.2) + (logScale r : ℂ) := by rfl
      _ = (τ : ℂ) * (actualProbeSlope r θ w v τ x.1 x.2 : ℂ) +
          (logScale r : ℂ) := by rw [hη]
      _ = ((τ * actualProbeSlope r θ w v τ x.1 x.2 + logScale r : ℝ) : ℂ) := by
        norm_num
  constructor
  · exact hlevelAll
  · intro hx τ hτ
    rw [nsActiveGate_eq_csig_level θ w v hx (τ : ℂ), hlevelAll τ hτ,
      actualProbeGate_eq_sig]
    simpa [csig] using TransformerIdentifiability.NLayer.csig_ofReal
      (τ * actualProbeSlope r θ w v τ x.1 x.2 + logScale r)

theorem nsActiveLevel_positive_real_eq_actual {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (x : FormalVar L k)
    (τ : ℝ) (hτ : 0 < τ) :
    nsActiveLevel (r := r) θ w v x (τ : ℂ) =
      ((τ * actualProbeSlope r θ w v τ x.1 x.2 + logScale r : ℝ) : ℂ) :=
  (nsActiveLevel_gate_positive_real_eq_actual (r := r) θ w v x).1 τ hτ

theorem nsActiveGate_positive_real_eq_actual {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) {l : Fin L} {a : Fin k}
    (ha : a ∈ activeHeads θ l) (τ : ℝ) (hτ : 0 < τ) :
    nsActiveGate (r := r) θ w v (l, a) (τ : ℂ) =
      (actualProbeGate r θ w v τ l a : ℂ) := by
  have hactive : IsActiveVar θ (l, a) := by
    simpa [IsActiveVar] using (mem_activeHeads θ l a).1 ha
  exact (nsActiveLevel_gate_positive_real_eq_actual (r := r) θ w v (l, a)).2
    hactive τ hτ

/-- The constructed complex observable agrees coordinatewise with the actual
probe output on the positive real axis. -/
theorem nsObservable_positive_real_eq_probeOutput {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (τ : ℝ) (hτ : 0 < τ) :
    nsObservable (r := r) θ w v (τ : ℂ) =
      fun i => (probeOutput r θ w v τ i : ℂ) := by
  classical
  let ηConstructed : FormalVar L k → ℂ :=
    fun x => nsActiveGate (r := r) θ w v x (τ : ℂ)
  let ρActual : FormalVar L k → ℝ := actualProbeGateAssignment r θ w v τ
  have hactive : ∀ (l : Fin L) (a : Fin k), l.1 < L →
      a ∈ activeHeads θ l → ηConstructed (l, a) = (ρActual (l, a) : ℂ) := by
    intro l a _hl ha
    simpa [ηConstructed, ρActual, actualProbeGateAssignment] using
      nsActiveGate_positive_real_eq_actual (r := r) θ w v ha τ hτ
  have hformalPoint := eval_formalPointComplex_eq_of_eq_on_active (θ := θ)
    ηConstructed (fun y => (ρActual y : ℂ)) w v L le_rfl hactive
  have hformal :
      evalFormalVecComplex ηConstructed (formalV θ w v L le_rfl) =
        evalFormalVecComplex (fun y => (ρActual y : ℂ))
          (formalV θ w v L le_rfl) := by
    simpa [formalV] using hformalPoint.2
  have hreal :
      evalFormalVecComplex (fun y => (ρActual y : ℂ))
          (formalV θ w v L le_rfl) =
        fun i => (evalFormalVec ρActual (formalV θ w v L le_rfl) i : ℂ) :=
    evalFormalVecComplex_ofReal ρActual (formalV θ w v L le_rfl)
  have hactual :
      evalFormalVec ρActual (formalV θ w v L le_rfl) =
        probeOutput r θ w v τ := by
    simpa [ρActual] using
      eval_formalV_actualProbeGateAssignment_eq_probeOutput r θ w v τ
  calc
    nsObservable (r := r) θ w v (τ : ℂ) =
        evalFormalVecComplex ηConstructed (formalV θ w v L le_rfl) := by rfl
    _ = evalFormalVecComplex (fun y => (ρActual y : ℂ))
          (formalV θ w v L le_rfl) := hformal
    _ = (fun i => (evalFormalVec ρActual (formalV θ w v L le_rfl) i : ℂ)) := hreal
    _ = (fun i => (probeOutput r θ w v τ i : ℂ)) := by rw [hactual]

theorem nsActiveStratificationData_observable_positive_real_eq_probeOutput
    {r L k d : Nat} (θ : Params L k d) (w v : Vec d)
    (τ : ℝ) (hτ : 0 < τ) :
    (nsActiveStratificationData (r := r) θ w v).observable (τ : ℂ) =
      fun i => (probeOutput r θ w v τ i : ℂ) :=
  nsObservable_positive_real_eq_probeOutput (r := r) θ w v τ hτ

/-- The constructed observable is coordinatewise holomorphic on the terminal
recursive domain. -/
theorem nsActiveStratificationData_observable_holomorphic
    {r L k d : Nat} (θ : Params L k d) (w v : Vec d) :
    ∀ i : Fin d, AnalyticOnNhd ℂ
      (fun τ => (nsActiveStratificationData (r := r) θ w v).observable τ i)
      ((nsActiveStratificationData (r := r) θ w v).Omega L) := by
  classical
  let D := nsActiveStratificationData (r := r) θ w v
  have hgate : ∀ x : FormalVar L k,
      AnalyticOnNhd ℂ (nsActiveGate (r := r) θ w v x) (D.Omega L) := by
    intro x
    by_cases hx : IsActiveVar θ x
    · have hxan :=
        (nsActiveLevel_gate_analyticOnNhd_recursiveDomain (r := r) θ w v x).2 hx
      exact analyticOnNhd_mono hxan
        (nsActiveStratificationData_omega_subset_of_le (r := r) θ w v
          (m := x.1.1 + 1) (n := L) (Nat.succ_le_of_lt x.1.2) le_rfl)
    · have hconst : AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) (D.Omega L) :=
        analyticOnNhd_const (𝕜 := ℂ) (v := (0 : ℂ)) (s := D.Omega L)
      convert hconst using 1
      ext τ
      exact nsActiveGate_eq_zero_of_inactive (r := r) θ w v hx τ
  intro i
  change AnalyticOnNhd ℂ
    (fun τ => evalFormalPolyComplex
      (fun x => nsActiveGate (r := r) θ w v x τ)
      (formalV θ w v L le_rfl i)) (D.Omega L)
  exact evalFormalPolyComplex_analyticOnNhd (formalV θ w v L le_rfl i) hgate

/-! ## Quadratic-in-prior-gate realization (successor level model content)

The successor-level model used by NS106 (`Step1SuccessorLevelModel`) asserts a
quadratic-in-the-predecessor-gate shape for the successor level, with analytic
coefficients `Ψ, Β, Γ₀`.  For the concrete constructed data these are not a
hypothesis: the affine level `τ · φ_{la} + log r` is literally quadratic in any
designated gate variable `x0` (degree ≤ 2 in each gate), and the coefficient
functions are the evaluated slope coefficients `coeffOfVar x0 s`, which have
strict prefix support and are therefore holomorphic on the recursive domain. -/

/-- A variable of a strict-prefix-support polynomial lives in an earlier layer. -/
theorem lt_of_mem_vars_of_supportBefore {L k n : Nat} {p : FormalPoly L k}
    (hp : FormalPolySupportBefore n p) {y : FormalVar L k} (hy : y ∈ p.vars) :
    y.1.1 < n := by
  by_contra hle
  rcases (MvPolynomial.mem_vars_iff_mem_support y).1 hy with ⟨m, hm, hym⟩
  exact (Finsupp.mem_support_iff.mp hym) (hp m hm y (not_lt.mp hle))

/-- Prior-layer gates are holomorphic on the recursive domain of a later layer. -/
theorem nsActiveGate_prior_analyticOnNhd {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (l : Fin L) {y : FormalVar L k}
    (hy : y.1.1 < l.1) :
    AnalyticOnNhd ℂ (nsActiveGate (r := r) θ w v y)
      ((nsActiveStratificationData (r := r) θ w v).Omega l.1) := by
  by_cases hyactive : IsActiveVar θ y
  · have hgate :=
      (nsActiveLevel_gate_analyticOnNhd_recursiveDomain (r := r) θ w v y).2 hyactive
    have hsub :
        (nsActiveStratificationData (r := r) θ w v).Omega l.1 ⊆
          (nsActiveStratificationData (r := r) θ w v).Omega (y.1.1 + 1) :=
      nsActiveStratificationData_omega_subset_of_le (r := r) θ w v
        (m := y.1.1 + 1) (n := l.1) (by omega) (Nat.le_of_lt l.2)
    exact analyticOnNhd_mono hgate hsub
  · have hzero : (nsActiveGate (r := r) θ w v y) = fun _ => (0 : ℂ) := by
      funext τ; exact nsActiveGate_eq_zero_of_inactive (r := r) θ w v hyactive τ
    rw [hzero]
    exact analyticOnNhd_const (𝕜 := ℂ) (v := (0 : ℂ))
      (s := (nsActiveStratificationData (r := r) θ w v).Omega l.1)

/-- Evaluating any strict-prefix-support polynomial at the constructed gates is
holomorphic on the recursive domain. -/
theorem nsEvalPrior_analyticOnNhd {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (l : Fin L) {p : FormalPoly L k}
    (hp : FormalPolySupportBefore l.1 p) :
    AnalyticOnNhd ℂ
      (fun τ => evalFormalPolyComplex (fun y => nsActiveGate (r := r) θ w v y τ) p)
      ((nsActiveStratificationData (r := r) θ w v).Omega l.1) := by
  classical
  have hη : ∀ y : FormalVar L k,
      AnalyticOnNhd ℂ
        (fun τ => if _hy : y.1.1 < l.1 then nsActiveGate (r := r) θ w v y τ else 0)
        ((nsActiveStratificationData (r := r) θ w v).Omega l.1) := by
    intro y
    by_cases hy : y.1.1 < l.1
    · simpa [hy] using nsActiveGate_prior_analyticOnNhd (r := r) θ w v l hy
    · simpa [hy] using (analyticOnNhd_const (𝕜 := ℂ) (v := (0 : ℂ))
        (s := (nsActiveStratificationData (r := r) θ w v).Omega l.1))
  have hpoly := evalFormalPolyComplex_analyticOnNhd p hη
  have heq :
      (fun τ => evalFormalPolyComplex (fun y => nsActiveGate (r := r) θ w v y τ) p) =
        (fun τ => evalFormalPolyComplex
          (fun y => if _hy : y.1.1 < l.1 then nsActiveGate (r := r) θ w v y τ else 0) p) := by
    funext τ
    symm
    apply evalFormalPolyComplex_congr_on_vars
    intro z hz
    have hlt : z.1.1 < l.1 := lt_of_mem_vars_of_supportBefore hp hz
    simp [hlt]
  rw [heq]
  exact hpoly

/-- A strict-prefix formal-polynomial evaluation is analytic at every point of
the corresponding concrete recursive domain. -/
theorem nsEvalPrior_analyticAt {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (l : Fin L) {p : FormalPoly L k}
    (hp : FormalPolySupportBefore l.1 p) {τ : ℂ}
    (hτ : τ ∈ (nsActiveStratificationData (r := r) θ w v).Omega l.1) :
    AnalyticAt ℂ
      (fun z => evalFormalPolyComplex
        (fun y => nsActiveGate (r := r) θ w v y z) p) τ :=
  nsEvalPrior_analyticOnNhd (r := r) θ w v l hp τ hτ

/-- Consequently a strict-prefix formal-polynomial evaluation tends to its
finite value along the punctured neighbourhood filter. -/
theorem nsEvalPrior_tendsto_punctured {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (l : Fin L) {p : FormalPoly L k}
    (hp : FormalPolySupportBefore l.1 p) {τ : ℂ}
    (hτ : τ ∈ (nsActiveStratificationData (r := r) θ w v).Omega l.1) :
    Filter.Tendsto
      (fun z => evalFormalPolyComplex
        (fun y => nsActiveGate (r := r) θ w v y z) p)
      (nhdsWithin τ ({τ}ᶜ : Set ℂ))
      (nhds (evalFormalPolyComplex
        (fun y => nsActiveGate (r := r) θ w v y τ) p)) :=
  (nsEvalPrior_analyticAt (r := r) θ w v l hp hτ).continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds

/-- At a point of its layer domain, a constructed gate is analytic provided
its level avoids `Π` when the head is active.  Inactive heads are identically
zero. -/
theorem nsActiveGate_analyticAt_of_mem_omega {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (x : FormalVar L k) {τ : ℂ}
    (hτ : τ ∈ (nsActiveStratificationData (r := r) θ w v).Omega x.1.1)
    (havoid : IsActiveVar θ x → nsActiveLevel (r := r) θ w v x τ ∉ Pi) :
    AnalyticAt ℂ (nsActiveGate (r := r) θ w v x) τ := by
  by_cases hx : IsActiveVar θ x
  · have hlevel : AnalyticAt ℂ (nsActiveLevel (r := r) θ w v x) τ :=
      (nsActiveLevel_gate_analyticOnNhd_recursiveDomain (r := r) θ w v x).1 τ hτ
    have hsig : AnalyticAt ℂ csig (nsActiveLevel (r := r) θ w v x τ) :=
      KHead.csig_analyticAt_of_notMem_Pi (havoid hx)
    have heq : nsActiveGate (r := r) θ w v x =
        fun z => csig (nsActiveLevel (r := r) θ w v x z) := by
      funext z
      exact nsActiveGate_eq_csig_level θ w v hx z
    rw [heq]
    exact hsig.comp hlevel
  · have hzero : nsActiveGate (r := r) θ w v x = fun _ => (0 : ℂ) := by
      funext z
      exact nsActiveGate_eq_zero_of_inactive (r := r) θ w v hx z
    rw [hzero]
    exact analyticAt_const

/-- Evaluated slope coefficient in the designated gate variable `x0`.  For `s = 0,1,2`
these are `Γ₀, Β, Ψ` of the successor-level quadratic model. -/
noncomputable def nsLevelCoeff {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (l : Fin L) (a : Fin k)
    (x0 : FormalVar L k) (s : Nat) : ℂ → ℂ :=
  fun τ => evalFormalPolyComplex (fun y => nsActiveGate (r := r) θ w v y τ)
    (coeffOfVar x0 s (formalSlope θ w v l a))

/-- **Successor-level quadratic model, realized.**  The constructed level at head
`(l,a)` is exactly the quadratic-in-`x0`-gate shape of `Step1SuccessorLevelModel`,
with `Ψ = nsLevelCoeff … 2`, `Β = nsLevelCoeff … 1`, `Γ₀ = nsLevelCoeff … 0`,
`L₀ = log r`, whenever the slope has gate-degree `≤ 2` in `x0`. -/
theorem nsActiveLevel_quadratic_in_prior_gate {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (l : Fin L) (a : Fin k) (x0 : FormalVar L k)
    (hdeg : MvPolynomial.degreeOf x0 (formalSlope θ w v l a) ≤ 2) (τ : ℂ) :
    nsActiveLevel (r := r) θ w v (l, a) τ =
      τ * (nsActiveGate (r := r) θ w v x0 τ *
          (nsLevelCoeff (r := r) θ w v l a x0 2 τ * nsActiveGate (r := r) θ w v x0 τ
            + nsLevelCoeff (r := r) θ w v l a x0 1 τ))
        + (τ * nsLevelCoeff (r := r) θ w v l a x0 0 τ + (logScale r : ℂ)) := by
  rw [nsActiveLevel_formula]
  have hsplit :=
    eval_complexFormalSlope_eq_coeff_zero_add_one_add_two θ w v l a x0 hdeg
      (fun y => nsActiveGate (r := r) θ w v y τ)
  simp only [complexFormalSlope] at hsplit
  rw [hsplit]
  simp only [nsLevelCoeff]
  ring

/-- The coefficient functions of the successor-level quadratic model are holomorphic
on the recursive domain. -/
theorem nsLevelCoeff_analyticOnNhd {r L k d : Nat}
    (θ : Params L k d) (w v : Vec d) (l : Fin L) (a : Fin k)
    (x0 : FormalVar L k) (s : Nat) :
    AnalyticOnNhd ℂ (nsLevelCoeff (r := r) θ w v l a x0 s)
      ((nsActiveStratificationData (r := r) θ w v).Omega l.1) :=
  nsEvalPrior_analyticOnNhd (r := r) θ w v l
    (formalSlope_coeffOfVar_supportBefore θ w v l a x0 s)

end

end TransformerIdentifiability.NLayer.NoSkip
