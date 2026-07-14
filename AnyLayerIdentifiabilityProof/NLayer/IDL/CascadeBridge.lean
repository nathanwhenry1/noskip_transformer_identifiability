import AnyLayerIdentifiabilityProof.NLayer.IDL.FrecConvergence
import AnyLayerIdentifiabilityProof.NLayer.Step1.ConcreteStratification

set_option autoImplicit false

open Filter Topology Matrix

namespace TransformerIdentifiability.NLayer

/-!
# R1: the slope / limit-vector bridge (`lem:cascade` plumbing, pure algebra)

`FrecConvergence` produced the recursively-peeled limit vector `frecLimit` and the
per-level gate hypothesis `GateLimits`.  To feed these into the existing matching
machinery we must identify, with **no analysis at all**, the head-peeling real
recursion with the closed-form telescoped objects the TeX matching step speaks
(`realSkipBprod`, `formalT`, `texMatchingUnprimedSaturatedLimitVector`, …).

This file is the *real* analogue of `SlopePaths.formalVVec_eq_Bprod_add_T`:

* `realW`, `realT` — the real value-transfer recursions obtained by specialising the
  formal complex streams at a real gate assignment;
* head-peeling identities (`realSkipBprod_head_peel`, `realW_head_peel`,
  `realT_head_peel`) — peel the *first* layer instead of the last;
* `frecLimit_eq` — the limit vector is `B_{L:1} v + T_{L} w` (closed form);
* `formalBprod_eq_matC` / `formalW_eq_matC` / `formalT_eq_matC` — the ℂ↔ℝ bridges,
  which identify `realPartMatrix (formalT …)` (i.e. the matching constant `D`) with
  `realT`.

The matching-vector identification proper (`frecLimit = texMatching…LimitVector`) and
the slope bridge live downstream; see `CascadeBridgeMatching`.
-/

/-! ## Real value-transfer recursions -/

/-- Real product `W_n(ς) = (B_{n-1} - ς_{n-1} V_{n-1}) ⋯ (B_0 - ς_0 V_0)` of the
formal factors at a *real* gate assignment, zero-based. -/
noncomputable def realW {d : Nat} (θ : LayerStream d) (ς : Nat -> ℝ) :
    Nat -> Matrix (Fin d) (Fin d) ℝ
  | 0 => 1
  | n + 1 => (skipB (θ n).1 - ς n • (θ n).1) * realW θ ς n

/-- Real accumulated value-transfer matrix `T_n` at a real gate assignment, the
real analogue of `SlopePaths.formalT`. -/
noncomputable def realT {d : Nat} (θ : LayerStream d) (ς : Nat -> ℝ) :
    Nat -> Matrix (Fin d) (Fin d) ℝ
  | 0 => 0
  | n + 1 => skipB (θ n).1 * realT θ ς n + ς n • ((θ n).1 * realW θ ς n)

@[simp] theorem realW_zero {d : Nat} (θ : LayerStream d) (ς : Nat -> ℝ) :
    realW θ ς 0 = 1 := rfl

@[simp] theorem realW_succ {d : Nat} (θ : LayerStream d) (ς : Nat -> ℝ) (n : Nat) :
    realW θ ς (n + 1) = (skipB (θ n).1 - ς n • (θ n).1) * realW θ ς n := rfl

@[simp] theorem realT_zero {d : Nat} (θ : LayerStream d) (ς : Nat -> ℝ) :
    realT θ ς 0 = 0 := rfl

@[simp] theorem realT_succ {d : Nat} (θ : LayerStream d) (ς : Nat -> ℝ) (n : Nat) :
    realT θ ς (n + 1) =
      skipB (θ n).1 * realT θ ς n + ς n • ((θ n).1 * realW θ ς n) := rfl

/-! ## Head-peeling identities (peel the first layer instead of the last) -/

/-- Peel the first layer of the real skip-product. -/
theorem realSkipBprod_head_peel {d : Nat} (θ : LayerStream d) (n : Nat) :
    realSkipBprod θ (n + 1) =
      realSkipBprod (fun k => θ (k + 1)) n * skipB (θ 0).1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [realSkipBprod_succ θ (n + 1), ih, ← mul_assoc]
      rw [show skipB (θ (n + 1)).1 * realSkipBprod (fun k => θ (k + 1)) n
            = realSkipBprod (fun k => θ (k + 1)) (n + 1) from
          (realSkipBprod_succ (fun k => θ (k + 1)) n).symm]

/-- Peel the first layer of the real `W`-product. -/
theorem realW_head_peel {d : Nat} (θ : LayerStream d) (ς : Nat -> ℝ) (n : Nat) :
    realW θ ς (n + 1) =
      realW (fun k => θ (k + 1)) (fun k => ς (k + 1)) n
        * (skipB (θ 0).1 - ς 0 • (θ 0).1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [realW_succ θ ς (n + 1), ih, ← mul_assoc]
      rw [show (skipB (θ (n + 1)).1 - ς (n + 1) • (θ (n + 1)).1)
              * realW (fun k => θ (k + 1)) (fun k => ς (k + 1)) n
            = realW (fun k => θ (k + 1)) (fun k => ς (k + 1)) (n + 1) from
          (realW_succ (fun k => θ (k + 1)) (fun k => ς (k + 1)) n).symm]

/-- Peel the first layer of the real `T`-matrix: this is the recursion the TeX matching
step uses, `T_{L} = ς_0 (B_{L:1} V_0) + T'_{L-1} (B_0 - ς_0 V_0)`. -/
theorem realT_head_peel {d : Nat} (θ : LayerStream d) (ς : Nat -> ℝ) (n : Nat) :
    realT θ ς (n + 1) =
      ς 0 • (realSkipBprod (fun k => θ (k + 1)) n * (θ 0).1)
        + realT (fun k => θ (k + 1)) (fun k => ς (k + 1)) n
            * (skipB (θ 0).1 - ς 0 • (θ 0).1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [realT_succ θ ς (n + 1), ih, realW_head_peel θ ς n,
        realSkipBprod_succ (fun k => θ (k + 1)) n,
        realT_succ (fun k => θ (k + 1)) (fun k => ς (k + 1)) n]
      simp only [mul_add, add_mul, Matrix.smul_mul, Matrix.mul_smul, mul_assoc,
        add_assoc]

/-! ## The dial-peel step as a matrix-vector update -/

/-- One peeled limit point, value component, in closed matrix form
`v ↦ B v + ς (V w)`. -/
theorem effLimitPoint_snd {d : Nat} (V : Matrix (Fin d) (Fin d) ℝ) (t : ℝ)
    (pt : ProbePoint d) :
    (effLimitPoint V t pt).2 = skipB V *ᵥ pt.2 + t • (V *ᵥ pt.1) := by
  simp only [effLimitPoint, firstLayerDialPoint_snd, skipB, Matrix.add_mulVec,
    Matrix.one_mulVec]

/-- One peeled limit point, query component, in closed matrix form
`w ↦ (B - ς V) w`. -/
theorem effLimitPoint_fst {d : Nat} (V : Matrix (Fin d) (Fin d) ℝ) (t : ℝ)
    (pt : ProbePoint d) :
    (effLimitPoint V t pt).1 = (skipB V - t • V) *ᵥ pt.1 := by
  simp only [effLimitPoint, firstLayerDialPoint_fst, skipB, Matrix.sub_mulVec,
    Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]

/-- `paramStream` reads its first layer directly. -/
theorem paramStream_zero {m d : Nat} (θ : Params (m + 1) d) :
    paramStream θ 0 = θ 0 := by
  simp [paramStream]

/-- Unfold one head-peeling step of `frecLimit`. -/
theorem frecLimit_succ {d : Nat} (r : Nat) {m : Nat} (θ : Params (m + 1) d)
    (ς : Nat -> ℝ) (pt : ProbePoint d) :
    frecLimit r θ ς pt =
      frecLimit r (Params.tail θ) (fun n => ς (n + 1))
        (effLimitPoint (Params.headValue θ) (ς 0) pt) := rfl

/-! ## The closed form of the limit vector (`formalVVec_eq_Bprod_add_T`, real version) -/

/-- **R1a core.**  The recursively-peeled limit vector is the telescoped closed form
`B_{L:1} v + T_L w`, the real analogue of `SlopePaths.formalVVec_eq_Bprod_add_T`. -/
theorem frecLimit_eq {d : Nat} (r : Nat) :
    ∀ {m : Nat} (θ : Params m d) (ς : Nat -> ℝ) (pt : ProbePoint d),
      frecLimit r θ ς pt =
        realSkipBprod (paramStream θ) m *ᵥ pt.2 + realT (paramStream θ) ς m *ᵥ pt.1 := by
  intro m
  induction m with
  | zero =>
      intro θ ς pt
      simp [frecLimit]
  | succ m ih =>
      intro θ ς pt
      rw [frecLimit_succ, ih (Params.tail θ) (fun n => ς (n + 1))
            (effLimitPoint (Params.headValue θ) (ς 0) pt)]
      simp only [Params.headValue, Params.headLayer]
      rw [paramStream_tail_eq_shift θ, realSkipBprod_head_peel (paramStream θ) m,
        realT_head_peel (paramStream θ) ς m, paramStream_zero θ,
        effLimitPoint_snd, effLimitPoint_fst]
      simp only [Matrix.mulVec_add, Matrix.add_mulVec, Matrix.mulVec_mulVec,
        Matrix.smul_mulVec, Matrix.mulVec_smul, add_assoc]

/-! ## The all-ones telescoping (primed side of the trichotomy)

On the primed parameter every deeper gate saturates to `1`.  With `ς ≡ 1` the running
`W`-product collapses to the identity (`B_j - V_j = I`), and `T` telescopes to
`B_{L:1} - I`.  This is TeX matching Step 2 (`eq:limthetaprime`); it needs no rigidity. -/

/-- With all gates `1`, every running factor `B_j - V_j` is the identity, so `realW = I`. -/
theorem realW_ones {d : Nat} (η : LayerStream d) (n : Nat) :
    realW η (fun _ => (1 : ℝ)) n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [realW_succ, one_smul, skipB_sub_value, Matrix.one_mul, ih]

/-- With all gates `1`, the transfer matrix telescopes: `T_n = B_{n:1} - I`. -/
theorem realT_ones {d : Nat} (η : LayerStream d) (n : Nat) :
    realT η (fun _ => (1 : ℝ)) n = realSkipBprod η n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [realT_succ, ih, realW_ones, realSkipBprod_succ, Matrix.mul_sub,
        Matrix.mul_one, one_smul, Matrix.mul_one, sub_add, skipB_sub_value]

/-- TeX matching Step 2 (`eq:limthetaprime`): with `ς₀` free and all deeper gates `1`,
the transfer matrix is `B_{L:1} - B_1 + ς₀ V_1` (the telescoped primed coefficient). -/
theorem realT_telescope {d : Nat} (η : LayerStream d) (g : Nat -> ℝ)
    (hg : ∀ k, g (k + 1) = 1) (n : Nat) :
    realT η g (n + 1) =
      realSkipBprod η (n + 1) - skipB (η 0).1 + g 0 • (η 0).1 := by
  have hshift : (fun k => g (k + 1)) = (fun _ => (1 : ℝ)) := by funext k; exact hg k
  rw [realT_head_peel η g n, hshift, realT_ones, realSkipBprod_head_peel η n]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_smul]
  module

/-! ## ℂ ↔ ℝ bridges:  the formal complex streams at a real gate assignment are `matC`
of the real streams.  This identifies `realPartMatrix (formalT …)` (the matching constant
`D`) with `realT`. -/

@[simp] theorem matC_zero {d : Nat} : matC (0 : Matrix (Fin d) (Fin d) ℝ) = 0 := by
  ext i j; simp [matC]

theorem matC_add {d : Nat} (A B : Matrix (Fin d) (Fin d) ℝ) :
    matC (A + B) = matC A + matC B := by
  ext i j; simp [matC, Matrix.add_apply]

theorem matC_sub {d : Nat} (A B : Matrix (Fin d) (Fin d) ℝ) :
    matC (A - B) = matC A - matC B := by
  ext i j; simp [matC, Matrix.sub_apply]

theorem matC_smul {d : Nat} (t : ℝ) (A : Matrix (Fin d) (Fin d) ℝ) :
    matC (t • A) = (t : ℂ) • matC A := by
  ext i j
  simp [matC, Matrix.smul_apply, smul_eq_mul]

/-- The formal factor `B_j - z_j V_j` at a real gate is `matC` of the real factor. -/
theorem formalFactor_matC {d : Nat} (θ : LayerStream d) (ς : Nat -> ℝ) (n : Nat) :
    formalFactor θ (fun k => (ς k : ℂ)) n = matC (skipB (θ n).1 - ς n • (θ n).1) := by
  simp only [formalFactor, matC_sub, matC_smul]

/-- `formalW` at a real gate assignment is `matC` of `realW`. -/
theorem formalW_matC {d : Nat} (θ : LayerStream d) (ς : Nat -> ℝ) (n : Nat) :
    formalW θ n (fun k => (ς k : ℂ)) = matC (realW θ ς n) := by
  induction n with
  | zero => simp [matC_one]
  | succ n ih =>
      rw [formalW_succ, ih, formalFactor_matC, ← matC_mul, realW_succ]

/-- `formalT` at a real gate assignment is `matC` of `realT`.  Taking real parts gives
`realPartMatrix (formalT …) = realT …`, i.e. the matching constant `D`. -/
theorem formalT_matC {d : Nat} (θ : LayerStream d) (ς : Nat -> ℝ) (n : Nat) :
    formalT θ n (fun k => (ς k : ℂ)) = matC (realT θ ς n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [formalT_succ, ih, formalW_matC θ ς n]
      rw [← matC_mul, ← matC_mul, ← matC_smul, ← matC_add, realT_succ]

/-! ## R1b: the limiting-slope bridge

The cascade's limiting slope `Λ_ℓ` is the bilinear form `matrixBilin A_ℓ` of the running
point after `ℓ` dial-peels.  The trichotomy instead delivers positivity of the *formal*
slope `(specializedPhi …).re`.  This subsection identifies the two — pure algebra — so the
trichotomy's `SignRegionData.primed_positive` feeds `CascadeStep`'s gate-saturation. -/

/-- The running point after `n` head-peels at gates `ς`: the `ℓ`-fold dial-limit point. -/
noncomputable def peelPoint {d : Nat} :
    LayerStream d -> (Nat -> ℝ) -> Nat -> ProbePoint d -> ProbePoint d
  | _, _, 0, pt => pt
  | η, ς, n + 1, pt =>
      peelPoint (fun k => η (k + 1)) (fun k => ς (k + 1)) n
        (effLimitPoint (η 0).1 (ς 0) pt)

@[simp] theorem peelPoint_zero {d : Nat} (η : LayerStream d) (ς : Nat -> ℝ)
    (pt : ProbePoint d) : peelPoint η ς 0 pt = pt := rfl

theorem peelPoint_succ {d : Nat} (η : LayerStream d) (ς : Nat -> ℝ) (n : Nat)
    (pt : ProbePoint d) :
    peelPoint η ς (n + 1) pt =
      peelPoint (fun k => η (k + 1)) (fun k => ς (k + 1)) n
        (effLimitPoint (η 0).1 (ς 0) pt) := rfl

/-- The formal query stream at a real gate assignment is `vecC` of the peeled query
point. -/
theorem formalWVec_eq_vecC_peelPoint {d : Nat} :
    ∀ (n : Nat) (η : LayerStream d) (g : Nat -> ℝ) (pt : ProbePoint d),
      formalWVec η n (fun k => (g k : ℂ)) pt.1 = vecC (peelPoint η g n pt).1 := by
  intro n
  induction n with
  | zero => intro η g pt; simp
  | succ n ih =>
      intro η g pt
      have hWhead : formalWVec η 1 (fun k => (g k : ℂ)) pt.1
          = vecC (effLimitPoint (η 0).1 (g 0) pt).1 := by
        rw [formalWVec_one_eq_vecC_headUpdate η (fun k => (g k : ℂ)) pt.1 (g 0) rfl]; rfl
      rw [formalWVec_tail_succ_of_head η (fun k => (g k : ℂ)) pt.1
            (effLimitPoint (η 0).1 (g 0) pt).1 n hWhead]
      exact ih (fun k => η (k + 1)) (fun k => g (k + 1))
        (effLimitPoint (η 0).1 (g 0) pt)

/-- The formal value stream at a real gate assignment is `vecC` of the peeled value
point. -/
theorem formalVVec_eq_vecC_peelPoint {d : Nat} :
    ∀ (n : Nat) (η : LayerStream d) (g : Nat -> ℝ) (pt : ProbePoint d),
      formalVVec η n (fun k => (g k : ℂ)) pt.1 pt.2 = vecC (peelPoint η g n pt).2 := by
  intro n
  induction n with
  | zero => intro η g pt; simp
  | succ n ih =>
      intro η g pt
      have hWhead : formalWVec η 1 (fun k => (g k : ℂ)) pt.1
          = vecC (effLimitPoint (η 0).1 (g 0) pt).1 := by
        rw [formalWVec_one_eq_vecC_headUpdate η (fun k => (g k : ℂ)) pt.1 (g 0) rfl]; rfl
      have hVhead : formalVVec η 1 (fun k => (g k : ℂ)) pt.1 pt.2
          = vecC (effLimitPoint (η 0).1 (g 0) pt).2 := by
        rw [formalVVec_one_eq_vecC_headUpdate η (fun k => (g k : ℂ)) pt.1 pt.2 (g 0) rfl]; rfl
      rw [formalVVec_tail_succ_of_head η (fun k => (g k : ℂ)) pt.1 pt.2
            (effLimitPoint (η 0).1 (g 0) pt).1 (effLimitPoint (η 0).1 (g 0) pt).2 n
            hWhead hVhead]
      exact ih (fun k => η (k + 1)) (fun k => g (k + 1))
        (effLimitPoint (η 0).1 (g 0) pt)

/-- **R1b core, complex form.**  The formal slope `φ_ℓ` at a real gate assignment is
the bilinear slope `matrixBilin A_ℓ` of the peeled running point, coerced to `ℂ`. -/
theorem formalPhi_eq_ofReal_matrixBilin_peelPoint {d : Nat} (η : LayerStream d)
    (g : Nat -> ℝ) (n : Nat) (pt : ProbePoint d) :
    formalPhi η n (fun k => (g k : ℂ)) pt.1 pt.2 =
      (matrixBilin (η n).2 (peelPoint η g n pt).1 (peelPoint η g n pt).2 : ℂ) := by
  rw [formalPhi, formalWVec_eq_vecC_peelPoint n η g pt,
    formalVVec_eq_vecC_peelPoint n η g pt, vecC_dotProduct_matC_mulVec]
  simp only [matrixBilin]

/-- **R1b core.**  The real part of the formal slope `φ_ℓ` at a real gate assignment is
the bilinear slope `matrixBilin A_ℓ` of the peeled running point. -/
theorem re_formalPhi_eq_matrixBilin_peelPoint {d : Nat} (η : LayerStream d)
    (g : Nat -> ℝ) (n : Nat) (pt : ProbePoint d) :
    (formalPhi η n (fun k => (g k : ℂ)) pt.1 pt.2).re =
      matrixBilin (η n).2 (peelPoint η g n pt).1 (peelPoint η g n pt).2 := by
  rw [formalPhi, formalWVec_eq_vecC_peelPoint n η g pt,
    formalVVec_eq_vecC_peelPoint n η g pt, vecC_dotProduct_matC_mulVec]
  simp only [Complex.ofReal_re, matrixBilin]

/-- The real first-gate-and-ones-tail gate vector `(t, ς₂, ς₃, …)` underlying
`gateAssignmentOfTail`. -/
noncomputable def realGateOfTail (t : ℝ) (tail : Nat -> ℝ) : Nat -> ℝ
  | 0 => t
  | n + 1 => tail n

theorem gateAssignmentOfTail_eq (t : ℝ) (tail : Nat -> ℝ) :
    gateAssignmentOfTail t tail = fun k => (realGateOfTail t tail k : ℂ) := by
  funext k
  cases k with
  | zero => rfl
  | succ n => rfl

/-- **R1b, complex form.**  The trichotomy's specialised slope is the limiting bilinear
slope of the peeled running point, coerced to `ℂ`. -/
theorem specializedPhi_eq_ofReal_matrixBilin_peelPoint {L d : Nat} (θ : Params L d)
    (n : Nat) (t : ℝ) (tail : Nat -> ℝ) (p : ProbePair d) :
    specializedPhi θ n (gateAssignmentOfTail t tail) p =
      (matrixBilin (paramStream θ n).2
        (peelPoint (paramStream θ) (realGateOfTail t tail) n p).1
        (peelPoint (paramStream θ) (realGateOfTail t tail) n p).2 : ℂ) := by
  rw [specializedPhi, gateAssignmentOfTail_eq]
  exact formalPhi_eq_ofReal_matrixBilin_peelPoint
    (paramStream θ) (realGateOfTail t tail) n p

/-- For real-gate `gateAssignmentOfTail`, nonzero specialised slope already has nonzero
real part because the full value is a coerced real bilinear form. -/
theorem specializedPhi_gateAssignmentOfTail_re_ne_zero_of_ne {L d : Nat} (θ : Params L d)
    (n : Nat) (t : ℝ) (tail : Nat -> ℝ) (p : ProbePair d) :
    specializedPhi θ n (gateAssignmentOfTail t tail) p ≠ 0 ->
      (specializedPhi θ n (gateAssignmentOfTail t tail) p).re ≠ 0 := by
  intro h hRe
  apply h
  rw [specializedPhi_eq_ofReal_matrixBilin_peelPoint θ n t tail p]
  apply Complex.ext
  · simpa [specializedPhi_eq_ofReal_matrixBilin_peelPoint θ n t tail p] using hRe
  · simp

/-- **R1b.**  The real part of the trichotomy's specialised slope is the limiting bilinear
slope of the peeled running point.  With `tail = fun _ => 1` this turns
`SignRegionData.primed_positive` into positivity of the limiting slope, ready for
`CascadeStep.eventuallyExpClose_firstLayerGate_of_tendsto_pos`. -/
theorem re_specializedPhi_eq_matrixBilin_peelPoint {L d : Nat} (θ : Params L d)
    (n : Nat) (t : ℝ) (tail : Nat -> ℝ) (p : ProbePair d) :
    (specializedPhi θ n (gateAssignmentOfTail t tail) p).re =
      matrixBilin (paramStream θ n).2
        (peelPoint (paramStream θ) (realGateOfTail t tail) n p).1
        (peelPoint (paramStream θ) (realGateOfTail t tail) n p).2 := by
  rw [specializedPhi, gateAssignmentOfTail_eq]
  exact re_formalPhi_eq_matrixBilin_peelPoint (paramStream θ) (realGateOfTail t tail) n p

end TransformerIdentifiability.NLayer
