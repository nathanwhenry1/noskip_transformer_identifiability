import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Step1.TierLocal
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Analytic.LevelRecurrence

set_option autoImplicit false

open Filter Matrix

namespace TransformerIdentifiability.NLayer.NoSkip

/-!
# No-skip Step 1 final visible-coordinate blowup (NS107, `tra:cascade` item (ii))

Authoritative math: `tra:cascade` item (ii) of
`tex_modular_no_skip_connections/sections/09-step1-attention.tex` — "the final residue
`R^h_L w ≠ 0` is verbatim", transferred under the opaque no-skip layer constant
`C_ℓ := ∑_a V_{ℓa}`, with the pole transferred to the output (SKIP §06c).

This file ports milestone M8 of the KHead `Step1/FinalBlowup.lean` cluster to the no-skip
active-stratification API.  The load-bearing statement is: at the innermost selected pole
`τ` of the final tier, the last selected residue `R^h_L w ≠ 0` makes the observable
coordinate `e_ι^⊤ F̂` have a *non-removable* singularity — it blows up (its norm tends to
`∞`) on a punctured neighbourhood of `τ`, so the pole is genuinely visible in the output
and cannot cancel.

## Abstract and concrete model layers

The general no-skip `ActiveStratificationData` carries arbitrary
`observable`/`level`/`gate` functions, so the model-neutral blowup lemma is stated using
`Step1FinalObservableModel`.  For the concrete recursive data this file now discharges
that interface: `nsFinalObservableRemainder` and
`nsFinalObservableResidueFactor` are extracted from the final `formalV` recurrence,
`nsObservable_finalCoord_split` proves their exact equality with the observable, and
`step1FinalResidueCoord_blowup_nsActive` applies the blowup theorem without an opaque
observable-model premise.

Under the no-skip dictionary `C_ℓ := ∑_a V_{ℓa}` the layer constant `C_ℓ` stays opaque;
nothing below expands it via a skip cancellation identity.

## What is proven

* `step1FinalSelectedGate_blowsUpAt` — the NS104 successor gate pole
  (`Step1SuccessorPoleNormalForm`, exact order `≥ 1`) makes the final selected gate blow up.
* `step1FinalObservableCoord_blowup` — from the gate pole, a punctured-bounded remainder
  `B`, a residue factor `G → g0 ≠ 0`, and the standing observable-decomposition model, the
  observable coordinate blows up (via `BlowsUpAt.bounded_add_mul_tendsto_ne_zero`).
* `step1FinalResidueCoord_blowup` — the residue-driven specialisation: at a nonzero final
  residue coordinate (NS103 `Step1ResidueCoordinateIndex`, whose defining nonvanishing is
  `R^h_L w ≠ 0`), the observable coordinate blows up.  Here `R^h_L w ≠ 0` is explicitly
  load-bearing: it is exactly what forces the limit `g0 = R^h_L w|_ι ≠ 0`.
-/

noncomputable section

/-! ## Generic analytic utilities

Model-neutral helpers, ported from the KHead cluster, that support producing the
punctured-bounded remainder and residue limit that feed the blowup below. -/

/-- Complex evaluation of a formal polynomial is continuous under a pointwise limit of the
gate assignment: if every formal variable's assignment tends to a limit along `F`, then the
polynomial evaluation tends to the evaluation at the limit assignment. -/
theorem evalFormalPolyComplex_tendsto {L k : Nat} {α : Type*} {F : Filter α}
    {η : α → FormalVar L k → ℂ} {c : FormalVar L k → ℂ} (p : FormalPoly L k)
    (hη : ∀ x : FormalVar L k, Tendsto (fun z => η z x) F (nhds (c x))) :
    Tendsto (fun z => evalFormalPolyComplex (η z) p) F
      (nhds (evalFormalPolyComplex c p)) := by
  simp only [evalFormalPolyComplex]
  induction p using MvPolynomial.induction_on with
  | C a =>
      simp only [MvPolynomial.eval₂_C]
      exact tendsto_const_nhds
  | add p q hp hq =>
      simp only [MvPolynomial.eval₂_add]
      exact hp.add hq
  | mul_X p x hp =>
      simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
      exact hp.mul (hη x)

/-- A function tending to a finite limit along the punctured neighbourhood filter is
punctured-bounded there. -/
theorem puncturedBoundedAt_of_tendsto {G : ℂ → ℂ} {τ L : ℂ}
    (hG : Tendsto G (nhdsWithin τ ({τ}ᶜ : Set ℂ)) (nhds L)) :
    PuncturedBoundedAt G τ := by
  refine ⟨‖L‖ + 1, ?_⟩
  exact ((hG.norm).eventually
    (Iio_mem_nhds (show ‖L‖ < ‖L‖ + 1 by linarith))).mono (fun z hz => le_of_lt hz)

/-- Expand a matrix-vector product of a finite `ℂ`-linear combination of matrices, at one
coordinate, as the same linear combination of the coordinatewise products. -/
theorem mulVec_sum_smul_apply {m K : Nat} (c : Fin K → ℂ)
    (M : Fin K → Matrix (Fin m) (Fin m) ℂ) (w : Fin m → ℂ) (i : Fin m) :
    ((∑ a : Fin K, c a • M a) *ᵥ w) i = ∑ a : Fin K, c a * ((M a *ᵥ w) i) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

/-- Coordinatewise complex evaluation of a formal matrix. -/
noncomputable def nsEvalFormalMatrixComplex {L k d : Nat}
    (η : FormalVar L k → ℂ)
    (M : Matrix (Fin d) (Fin d) (FormalPoly L k)) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => evalFormalPolyComplex η (M i j)

@[simp] theorem nsEvalFormalVecComplex_mulVec {L k d : Nat}
    (η : FormalVar L k → ℂ)
    (M : Matrix (Fin d) (Fin d) (FormalPoly L k)) (x : FormalVec L k d) :
    evalFormalVecComplex η (M *ᵥ x) =
      nsEvalFormalMatrixComplex η M *ᵥ evalFormalVecComplex η x := by
  ext i
  simp [evalFormalVecComplex, nsEvalFormalMatrixComplex, evalFormalPolyComplex,
    Matrix.mulVec, dotProduct]

@[simp] theorem nsEvalFormalMatrixComplex_realMatrixToFormal {L k d : Nat}
    (η : FormalVar L k → ℂ) (M : Matrix (Fin d) (Fin d) ℝ) :
    nsEvalFormalMatrixComplex η (realMatrixToFormal (L := L) (k := k) M) =
      M.map (algebraMap ℝ ℂ) := by
  ext i j
  simp [nsEvalFormalMatrixComplex, realMatrixToFormal, evalFormalPolyComplex]

@[simp] theorem nsEvalFormalMatrixComplex_formalGatedValueSum {L k d : Nat}
    (η : FormalVar L k → ℂ) (θ : Params L k d) (l : Fin L) :
    nsEvalFormalMatrixComplex η (formalGatedValueSum θ l) =
      ∑ a : Fin k, η (l, a) • (valueMatrix θ l a).map (algebraMap ℝ ℂ) := by
  ext i j
  simp [nsEvalFormalMatrixComplex, formalGatedValueSum, formalGate,
    formalValueMatrix, realMatrixToFormal, evalFormalPolyComplex,
    Matrix.sum_apply, Matrix.smul_apply]

/-! ## Deliverable 1 — the final selected gate has a pole (blows up) -/

/-- **`lem:observable-pole` input.**  From the NS104 successor gate pole
(`Step1SuccessorPoleNormalForm`, exact positive order `N.q ≥ 1` with nonzero leading
coefficient) the final selected gate `csig ∘ level` blows up at the transferred pole `τ`:
its norm tends to `∞` on a punctured neighbourhood.  This is the transferred-pole singular
driver of the observable coordinate. -/
theorem step1FinalSelectedGate_blowsUpAt {n k d : Nat}
    {D : ActiveStratificationData (n + 2) k d} {C : Step1SelectedChain n k}
    {jfin : Step1TierIndex n} {τ : ℂ}
    (N : Step1SuccessorPoleNormalForm D C jfin τ) :
    BlowsUpAt (step1SelectedGateFunction D C jfin) τ :=
  N.normalForm.blowsUpAt (by exact_mod_cast N.q_pos)

/-! ## Deliverable 2 — the standing observable-decomposition model -/

/-- **`lem:observable-pole` decomposition (abstract model).**  On a punctured neighbourhood
of `τ`, the observable coordinate `e_ι^⊤ F̂` splits as `B + selectedGate · G`, where `B` is
the collapse-plus-nonselected remainder and `G` carries the residue factor.  In the KHead
tree this is derived from `hD.observable_formula`; for arbitrary no-skip data it is the
small model-facing interface.  The concrete theorem
`nsActiveStratificationData_finalObservableModel` below realizes it. -/
def Step1FinalObservableModel {n k d : Nat}
    (D : ActiveStratificationData (n + 2) k d) (C : Step1SelectedChain n k)
    (jfin : Step1TierIndex n) (B G : ℂ → ℂ) (ι : Fin d) (τ : ℂ) : Prop :=
  (fun z => B z + step1SelectedGateFunction D C jfin z * G z)
    =ᶠ[nhdsWithin τ ({τ}ᶜ : Set ℂ)] (fun z => D.observable z ι)

/-! ## The concrete no-skip observable model -/

/-- The part of the terminal no-skip observable which does not contain the
selected final-layer gate.  It consists of the opaque no-skip transmission
`C_L v_L` and all nonselected final-head value terms. -/
noncomputable def nsFinalObservableRemainder {n k d r : Nat}
    (θ : Params (n + 2) k d) (w v : Vec d) (C : Step1SelectedChain n k)
    (ι : Fin d) : ℂ → ℂ := fun z =>
  let l := step1FinalTierIndex n
  let sel := C.headAt l
  let η := fun x => nsActiveGate (r := r) θ w v x z
  let W := formalW θ w v l.1 (Nat.le_of_lt l.2)
  let V := formalV θ w v l.1 (Nat.le_of_lt l.2)
  evalFormalPolyComplex η ((formalCollapseMatrix θ l *ᵥ V) ι) +
    ∑ a ∈ Finset.univ.erase sel,
      η (l, a) * evalFormalPolyComplex η ((formalValueMatrix θ l a *ᵥ W) ι)

/-- Residue factor multiplying the selected final-layer gate in the concrete
observable.  This is the selected value matrix applied to the incoming formal
`w` stream, evaluated at the constructed gates. -/
noncomputable def nsFinalObservableResidueFactor {n k d r : Nat}
    (θ : Params (n + 2) k d) (w v : Vec d) (C : Step1SelectedChain n k)
    (ι : Fin d) : ℂ → ℂ := fun z =>
  let l := step1FinalTierIndex n
  let η := fun x => nsActiveGate (r := r) θ w v x z
  let W := formalW θ w v l.1 (Nat.le_of_lt l.2)
  evalFormalPolyComplex η
    ((formalValueMatrix θ l (C.headAt l) *ᵥ W) ι)

/-- Exact last-layer coordinate split for the concrete no-skip observable.
This is the model-facing content formerly deferred as
`Step1FinalObservableModel`; no skip cancellation identity is used. -/
theorem nsObservable_finalCoord_split {n k d r : Nat}
    (θ : Params (n + 2) k d) (w v : Vec d) (C : Step1SelectedChain n k)
    (ι : Fin d) (z : ℂ) :
    (nsActiveStratificationData (r := r) θ w v).observable z ι =
      nsFinalObservableRemainder (r := r) θ w v C ι z +
        nsActiveGate (r := r) θ w v (C.selectedVar (step1FinalTierIndex n)) z *
          nsFinalObservableResidueFactor (r := r) θ w v C ι z := by
  classical
  let l := step1FinalTierIndex n
  let sel := C.headAt l
  let η : FormalVar (n + 2) k → ℂ := fun x => nsActiveGate (r := r) θ w v x z
  let W := formalW θ w v l.1 (Nat.le_of_lt l.2)
  let V := formalV θ w v l.1 (Nat.le_of_lt l.2)
  have hVdec : formalV θ w v (n + 2) le_rfl =
      formalCollapseMatrix θ l *ᵥ V + formalGatedValueSum θ l *ᵥ W := by
    dsimp [l, V, W, formalV]
    rw [formalPoint_succ]
    rfl
  have hobs :
      (nsActiveStratificationData (r := r) θ w v).observable z ι =
        evalFormalVecComplex η (formalV θ w v (n + 2) le_rfl) ι := rfl
  have hobs2 :
      (nsActiveStratificationData (r := r) θ w v).observable z ι =
        evalFormalPolyComplex η ((formalCollapseMatrix θ l *ᵥ V) ι) +
          ∑ a : Fin k, η (l, a) *
            evalFormalPolyComplex η ((formalValueMatrix θ l a *ᵥ W) ι) := by
    rw [hobs, hVdec]
    change evalFormalPolyComplex η (_ + _) = _
    rw [show evalFormalPolyComplex η
          (((formalCollapseMatrix θ l *ᵥ V) ι) +
            ((formalGatedValueSum θ l *ᵥ W) ι)) =
        evalFormalPolyComplex η ((formalCollapseMatrix θ l *ᵥ V) ι) +
          evalFormalPolyComplex η ((formalGatedValueSum θ l *ᵥ W) ι) by
      simp [evalFormalPolyComplex]]
    congr 1
    change evalFormalVecComplex η (formalGatedValueSum θ l *ᵥ W) ι = _
    rw [nsEvalFormalVecComplex_mulVec,
      nsEvalFormalMatrixComplex_formalGatedValueSum,
      mulVec_sum_smul_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    congr 1
    calc
      ((valueMatrix θ l a).map (algebraMap ℝ ℂ) *ᵥ
          evalFormalVecComplex η W) ι =
          (nsEvalFormalMatrixComplex η (formalValueMatrix θ l a) *ᵥ
            evalFormalVecComplex η W) ι := by
              rw [formalValueMatrix, nsEvalFormalMatrixComplex_realMatrixToFormal]
      _ = evalFormalVecComplex η (formalValueMatrix θ l a *ᵥ W) ι := by
            rw [nsEvalFormalVecComplex_mulVec]
      _ = evalFormalPolyComplex η ((formalValueMatrix θ l a *ᵥ W) ι) := rfl
  have hsplit :
      (∑ a : Fin k, η (l, a) *
          evalFormalPolyComplex η ((formalValueMatrix θ l a *ᵥ W) ι)) =
        η (l, sel) *
            evalFormalPolyComplex η ((formalValueMatrix θ l sel *ᵥ W) ι) +
          ∑ a ∈ Finset.univ.erase sel, η (l, a) *
            evalFormalPolyComplex η ((formalValueMatrix θ l a *ᵥ W) ι) :=
    (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ sel)).symm
  rw [hobs2, hsplit]
  simp only [nsFinalObservableRemainder, nsFinalObservableResidueFactor,
    Step1SelectedChain.selectedVar]
  change _ = (_ + ∑ a ∈ Finset.univ.erase sel, _) + η (l, sel) * _
  ring

/-- The exact split realizes the previously opaque observable-model premise for
the concrete data, as soon as the selected final head is active (so its
constructed gate is the sigmoid of its level). -/
theorem nsActiveStratificationData_finalObservableModel {n k d r : Nat}
    (θ : Params (n + 2) k d) (w v : Vec d) (C : Step1SelectedChain n k)
    (ι : Fin d) (τ : ℂ)
    (hactive : IsActiveVar θ (C.selectedVar (step1FinalTierIndex n))) :
    Step1FinalObservableModel (nsActiveStratificationData (r := r) θ w v) C
      (step1FinalTierIndex n) (nsFinalObservableRemainder (r := r) θ w v C ι)
      (nsFinalObservableResidueFactor (r := r) θ w v C ι) ι τ := by
  filter_upwards with z
  rw [step1SelectedGateFunction_apply]
  change nsFinalObservableRemainder (r := r) θ w v C ι z +
      csig (nsActiveLevel (r := r) θ w v
        (C.selectedVar (step1FinalTierIndex n)) z) *
        nsFinalObservableResidueFactor (r := r) θ w v C ι z = _
  rw [
    ← nsActiveGate_eq_csig_level (r := r) θ w v hactive z]
  exact (nsObservable_finalCoord_split (r := r) θ w v C ι z).symm

/-! ## Deliverable 4 — the final observable coordinate blows up -/

/-- **`lem:final-tier-blowup` (abstract).**  Combine the final selected gate pole
(deliverable 1), a punctured-bounded remainder `B`, a residue factor `G → g0` with the
nonzero residue limit `g0 ≠ 0`, and the standing observable decomposition (deliverable 2):
the observable coordinate `e_ι^⊤ F̂` blows up at `τ`.  The pole is therefore non-removable —
genuinely visible in the output — via `BlowsUpAt.bounded_add_mul_tendsto_ne_zero`. -/
theorem step1FinalObservableCoord_blowup {n k d : Nat}
    {D : ActiveStratificationData (n + 2) k d} {C : Step1SelectedChain n k}
    {jfin : Step1TierIndex n} {τ : ℂ}
    (N : Step1SuccessorPoleNormalForm D C jfin τ)
    {B G : ℂ → ℂ} {g0 : ℂ} {ι : Fin d}
    (hB : PuncturedBoundedAt B τ)
    (hG : Tendsto G (nhdsWithin τ ({τ}ᶜ : Set ℂ)) (nhds g0))
    (hg0 : g0 ≠ 0)
    (hmodel : Step1FinalObservableModel D C jfin B G ι τ) :
    BlowsUpAt (fun z => D.observable z ι) τ := by
  have hgate : BlowsUpAt (step1SelectedGateFunction D C jfin) τ :=
    step1FinalSelectedGate_blowsUpAt N
  have hblow : BlowsUpAt
      (fun z => B z + step1SelectedGateFunction D C jfin z * G z) τ :=
    BlowsUpAt.bounded_add_mul_tendsto_ne_zero hB hgate hG hg0
  have hnorm :
      (fun z => ‖B z + step1SelectedGateFunction D C jfin z * G z‖)
        =ᶠ[nhdsWithin τ ({τ}ᶜ : Set ℂ)]
        (fun z => ‖D.observable z ι‖) := by
    filter_upwards [hmodel] with z hz
    rw [hz]
  exact Filter.Tendsto.congr' hnorm hblow

/-- **`lem:final-tier-blowup` (residue-driven).**  At a nonzero final residue coordinate
`i` (NS103 `Step1ResidueCoordinateIndex H w h`, whose defining property is
`(cascadeFinalProduct … *ᵥ w) i ≠ 0`, i.e. `R^h_L w ≠ 0`), the observable coordinate `i.1`
blows up at the transferred final-tier pole `τ`.

Here `R^h_L w ≠ 0` is the load-bearing input: the residue factor's limit is
`g0 = step1ResidueTopConstant H w h i = (R^h_L w)_i`, and its nonvanishing
(`step1ResidueTopConstant_ne_zero`, which is exactly `i.2`) is what forces the observable
coordinate to be unbounded rather than removable. -/
theorem step1FinalResidueCoord_blowup {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta')
    {D : ActiveStratificationData (n + 2) k d}
    (w : Vec d) (h : Fin k) (i : Step1ResidueCoordinateIndex H w h) {τ : ℂ}
    (N : Step1SuccessorPoleNormalForm D (step1TargetSelectedChain H h)
      (step1FinalTierIndex n) τ)
    {B G : ℂ → ℂ}
    (hB : PuncturedBoundedAt B τ)
    (hG : Tendsto G (nhdsWithin τ ({τ}ᶜ : Set ℂ))
      (nhds ((step1ResidueTopConstant H w h i : ℝ) : ℂ)))
    (hmodel : Step1FinalObservableModel D (step1TargetSelectedChain H h)
      (step1FinalTierIndex n) B G i.1 τ) :
    BlowsUpAt (fun z => D.observable z i.1) τ := by
  have hg0 : ((step1ResidueTopConstant H w h i : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (step1ResidueTopConstant_ne_zero H w h i)
  exact step1FinalObservableCoord_blowup N hB hG hg0 hmodel

/-! ## Concrete no-skip specialisations (no observable-model premise) -/

/-- The concrete remainder has a finite punctured limit and the concrete
residue factor tends to its value at the terminal point.  The only local
geometric input beyond `τ ∈ Ω_final` is selected-only collision: every
nonselected final level avoids `Π` at `τ`. -/
theorem nsFinalObservable_localAnalyticData {n k d r : Nat}
    (θ : Params (n + 2) k d) (w v : Vec d) (C : Step1SelectedChain n k)
    (ι : Fin d) {τ : ℂ}
    (hτ : τ ∈ (nsActiveStratificationData (r := r) θ w v).Omega
      (step1FinalTierIndex n).1)
    (hselectedOnly : ∀ a : Fin k, a ≠ C.headAt (step1FinalTierIndex n) →
      IsActiveVar θ (step1FinalTierIndex n, a) →
        nsActiveLevel (r := r) θ w v (step1FinalTierIndex n, a) τ ∉ Pi) :
    PuncturedBoundedAt (nsFinalObservableRemainder (r := r) θ w v C ι) τ ∧
      Tendsto (nsFinalObservableResidueFactor (r := r) θ w v C ι)
        (nhdsWithin τ ({τ}ᶜ : Set ℂ))
        (nhds (nsFinalObservableResidueFactor (r := r) θ w v C ι τ)) := by
  classical
  let l := step1FinalTierIndex n
  let sel := C.headAt l
  let η : ℂ → FormalVar (n + 2) k → ℂ :=
    fun z x => nsActiveGate (r := r) θ w v x z
  let W := formalW θ w v l.1 (Nat.le_of_lt l.2)
  let V := formalV θ w v l.1 (Nat.le_of_lt l.2)
  have hVsupport : FormalPolySupportBefore l.1
      ((formalCollapseMatrix θ l *ᵥ V) ι) :=
    formalPolySupportBefore_of_dependsOnLayersBefore
      (formalMatrix_mulVec_dependsOnLayersBefore
        (formalCollapseMatrix_dependsOnLayersBefore l.1 θ l)
        (formalV_dependsOnLayersBefore θ w v l.1 (Nat.le_of_lt l.2)) ι)
  have hWsupport : ∀ a : Fin k, FormalPolySupportBefore l.1
      ((formalValueMatrix θ l a *ᵥ W) ι) := by
    intro a
    exact formalPolySupportBefore_of_dependsOnLayersBefore
      (formalMatrix_mulVec_dependsOnLayersBefore
        (realMatrixToFormal_dependsOnLayersBefore l.1 (valueMatrix θ l a))
        (formalW_dependsOnLayersBefore θ w v l.1 (Nat.le_of_lt l.2)) ι)
  have hcollapse : Tendsto
      (fun z => evalFormalPolyComplex (η z)
        ((formalCollapseMatrix θ l *ᵥ V) ι))
      (nhdsWithin τ ({τ}ᶜ : Set ℂ))
      (nhds (evalFormalPolyComplex (η τ)
        ((formalCollapseMatrix θ l *ᵥ V) ι))) :=
    nsEvalPrior_tendsto_punctured (r := r) θ w v l hVsupport hτ
  have hsum : Tendsto
      (fun z => ∑ a ∈ Finset.univ.erase sel,
        η z (l, a) * evalFormalPolyComplex (η z)
          ((formalValueMatrix θ l a *ᵥ W) ι))
      (nhdsWithin τ ({τ}ᶜ : Set ℂ))
      (nhds (∑ a ∈ Finset.univ.erase sel,
        η τ (l, a) * evalFormalPolyComplex (η τ)
          ((formalValueMatrix θ l a *ᵥ W) ι))) := by
    apply tendsto_finsetSum
    intro a ha
    have hane : a ≠ sel := Finset.ne_of_mem_erase ha
    have hgateAn : AnalyticAt ℂ
        (nsActiveGate (r := r) θ w v (l, a)) τ :=
      nsActiveGate_analyticAt_of_mem_omega (r := r) θ w v (l, a) hτ
        (fun haactive => hselectedOnly a hane haactive)
    have hgate : Tendsto (fun z => η z (l, a))
        (nhdsWithin τ ({τ}ᶜ : Set ℂ)) (nhds (η τ (l, a))) :=
      hgateAn.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hvalue := nsEvalPrior_tendsto_punctured (r := r) θ w v l
      (hWsupport a) hτ
    exact hgate.mul hvalue
  have hrem : Tendsto (nsFinalObservableRemainder (r := r) θ w v C ι)
      (nhdsWithin τ ({τ}ᶜ : Set ℂ))
      (nhds (nsFinalObservableRemainder (r := r) θ w v C ι τ)) := by
    change Tendsto
      (fun z => evalFormalPolyComplex (η z)
          ((formalCollapseMatrix θ l *ᵥ V) ι) +
        ∑ a ∈ Finset.univ.erase sel, η z (l, a) *
          evalFormalPolyComplex (η z) ((formalValueMatrix θ l a *ᵥ W) ι))
      (nhdsWithin τ ({τ}ᶜ : Set ℂ))
      (nhds (evalFormalPolyComplex (η τ)
          ((formalCollapseMatrix θ l *ᵥ V) ι) +
        ∑ a ∈ Finset.univ.erase sel, η τ (l, a) *
          evalFormalPolyComplex (η τ) ((formalValueMatrix θ l a *ᵥ W) ι)))
    exact hcollapse.add hsum
  have hfactor := nsEvalPrior_tendsto_punctured (r := r) θ w v l
    (hWsupport sel) hτ
  refine ⟨puncturedBoundedAt_of_tendsto hrem, ?_⟩
  change Tendsto
    (fun z => evalFormalPolyComplex (η z)
      ((formalValueMatrix θ l sel *ᵥ W) ι))
    (nhdsWithin τ ({τ}ᶜ : Set ℂ))
    (nhds (evalFormalPolyComplex (η τ)
      ((formalValueMatrix θ l sel *ᵥ W) ι)))
  exact hfactor

/-- For the recursively constructed no-skip data, the exact terminal-formal-stream
split discharges `Step1FinalObservableModel`. -/
theorem step1FinalObservableCoord_blowup_nsActive {n k d r : Nat}
    {θ : Params (n + 2) k d} (w v : Vec d) {C : Step1SelectedChain n k}
    {τ : ℂ} {ι : Fin d} {g0 : ℂ}
    (hactive : IsActiveVar θ (C.selectedVar (step1FinalTierIndex n)))
    (N : Step1SuccessorPoleNormalForm
      (nsActiveStratificationData (r := r) θ w v) C (step1FinalTierIndex n) τ)
    (hB : PuncturedBoundedAt (nsFinalObservableRemainder (r := r) θ w v C ι) τ)
    (hG : Tendsto (nsFinalObservableResidueFactor (r := r) θ w v C ι)
      (nhdsWithin τ ({τ}ᶜ : Set ℂ)) (nhds g0))
    (hg0 : g0 ≠ 0) :
    BlowsUpAt
      (fun z => (nsActiveStratificationData (r := r) θ w v).observable z ι) τ := by
  exact step1FinalObservableCoord_blowup N hB hG hg0
    (nsActiveStratificationData_finalObservableModel (r := r) θ w v C ι τ hactive)

/-- A finite punctured limit of the concrete collapse/nonselected remainder is
enough to supply its boundedness hypothesis. -/
theorem step1FinalObservableCoord_blowup_nsActive_of_remainder_tendsto
    {n k d r : Nat} {θ : Params (n + 2) k d} (w v : Vec d)
    {C : Step1SelectedChain n k} {τ : ℂ} {ι : Fin d} {b0 g0 : ℂ}
    (hactive : IsActiveVar θ (C.selectedVar (step1FinalTierIndex n)))
    (N : Step1SuccessorPoleNormalForm
      (nsActiveStratificationData (r := r) θ w v) C (step1FinalTierIndex n) τ)
    (hB : Tendsto (nsFinalObservableRemainder (r := r) θ w v C ι)
      (nhdsWithin τ ({τ}ᶜ : Set ℂ)) (nhds b0))
    (hG : Tendsto (nsFinalObservableResidueFactor (r := r) θ w v C ι)
      (nhdsWithin τ ({τ}ᶜ : Set ℂ)) (nhds g0))
    (hg0 : g0 ≠ 0) :
    BlowsUpAt
      (fun z => (nsActiveStratificationData (r := r) θ w v).observable z ι) τ :=
  step1FinalObservableCoord_blowup_nsActive w v hactive N
    (puncturedBoundedAt_of_tendsto hB) hG hg0

/-- **Concrete residue-driven final blowup.**  The observable-model assumption
has disappeared: the remainder and residue factor are the explicit functions
above, and their exact split is a theorem.  The nonzero limit is the selected
value-product coordinate via `step1ResidueTopConstant_eq_selectedValueProduct`;
its nonvanishing is the final residue hypothesis `R^h_L w ≠ 0`. -/
theorem step1FinalResidueCoord_blowup_nsActive_of_analyticData {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta')
    (w v : Vec d) (h : Fin k) (i : Step1ResidueCoordinateIndex H w h) {τ : ℂ}
    (N : Step1SuccessorPoleNormalForm
      (nsActiveStratificationData (r := r) theta' w v)
      (step1TargetSelectedChain H h) (step1FinalTierIndex n) τ)
    (hB : PuncturedBoundedAt
      (nsFinalObservableRemainder (r := r) theta' w v
        (step1TargetSelectedChain H h) i.1) τ)
    (hG : Tendsto
      (nsFinalObservableResidueFactor (r := r) theta' w v
        (step1TargetSelectedChain H h) i.1)
      (nhdsWithin τ ({τ}ᶜ : Set ℂ))
      (nhds ((step1ResidueTopConstant H w h i : ℝ) : ℂ))) :
    BlowsUpAt
      (fun z => (nsActiveStratificationData (r := r) theta' w v).observable z i.1) τ := by
  have hactiveHead :
      (step1TargetSelectedChain H h).headAt (step1FinalTierIndex n) ∈
        activeHeads theta' (step1FinalTierIndex n) :=
    step1_head_active H (step1FinalTierIndex n) _
  have hactive : IsActiveVar theta'
      ((step1TargetSelectedChain H h).selectedVar (step1FinalTierIndex n)) := by
    simpa [IsActiveVar, Step1SelectedChain.selectedVar] using hactiveHead
  have hg0 : ((step1ResidueTopConstant H w h i : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (step1ResidueTopConstant_ne_zero H w h i)
  exact step1FinalObservableCoord_blowup_nsActive w v hactive N hB hG hg0

/-- **Concrete terminal nonremovability with analytic inputs discharged.**
Membership in the final recursive domain makes every prior-gate polynomial
analytic.  Selected-only collision makes all nonselected final gates analytic.
Thus the only remaining load-bearing input is the honest terminal
noncancellation statement that the evaluated residue factor is nonzero. -/
theorem step1FinalResidueCoord_blowup_nsActive {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta')
    (w v : Vec d) (h : Fin k) (i : Step1ResidueCoordinateIndex H w h) {τ : ℂ}
    (N : Step1SuccessorPoleNormalForm
      (nsActiveStratificationData (r := r) theta' w v)
      (step1TargetSelectedChain H h) (step1FinalTierIndex n) τ)
    (hτ : τ ∈ (nsActiveStratificationData (r := r) theta' w v).Omega
      (step1FinalTierIndex n).1)
    (hselectedOnly : ∀ a : Fin k,
      a ≠ (step1TargetSelectedChain H h).headAt (step1FinalTierIndex n) →
      IsActiveVar theta' (step1FinalTierIndex n, a) →
        nsActiveLevel (r := r) theta' w v (step1FinalTierIndex n, a) τ ∉ Pi)
    (hresidue : nsFinalObservableResidueFactor (r := r) theta' w v
      (step1TargetSelectedChain H h) i.1 τ ≠ 0) :
    BlowsUpAt
      (fun z => (nsActiveStratificationData (r := r) theta' w v).observable z i.1) τ := by
  have hactiveHead :
      (step1TargetSelectedChain H h).headAt (step1FinalTierIndex n) ∈
        activeHeads theta' (step1FinalTierIndex n) :=
    step1_head_active H (step1FinalTierIndex n) _
  have hactive : IsActiveVar theta'
      ((step1TargetSelectedChain H h).selectedVar (step1FinalTierIndex n)) := by
    simpa [IsActiveVar, Step1SelectedChain.selectedVar] using hactiveHead
  rcases nsFinalObservable_localAnalyticData (r := r) theta' w v
      (step1TargetSelectedChain H h) i.1 hτ hselectedOnly with ⟨hB, hG⟩
  exact step1FinalObservableCoord_blowup_nsActive w v hactive N hB hG hresidue

end

end TransformerIdentifiability.NLayer.NoSkip
