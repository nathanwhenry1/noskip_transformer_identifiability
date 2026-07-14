import AnyLayerIdentifiabilityProof.NLayer.KHead.Step2.Dial
import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.ActiveStratification
import AnyLayerIdentifiabilityProof.NLayer.IDL.CascadeSaturation
import AnyLayerIdentifiabilityProof.NLayer.KHead.Genericity.AnchorCertificate
import AnyLayerIdentifiabilityProof.NLayer.Analytic.SigmoidTail

set_option autoImplicit false

open Matrix Filter Topology

namespace TransformerIdentifiability.NLayer.KHead

/-!
# K-head Step 2 dial saturation: `lem:head-dial` (iv)/(v) and full `HeadDialStatement`

This file completes the saturation half of `lem:head-dial` and assembles a full
`HeadDialStatement` witness for the layer-0 attention/value matrices of a `SignRegionData`.

`Dial.lean` already proves the core estimates (i)/(ii)/(iii) (`headDial_exact_identity`,
`headDial_gate_tracks`, `headDial_probe_motion`) and packages the sign-region genericity
input via the `SignRegionData` adapters.  Here we add:

* a bridge `EventuallyExpClose → ExpCloseTo`, and closeness-congruence/limit helpers;
* **GAP1** — the dial path converges to its base point (`tendsto_headDialPath`), hence the
  layer-0 dialed slope converges to the base slope;
* the saturation engine `expCloseTo_sig_of_tendsto_pos` (bridge over the reusable
  `eventuallyExpClose_sig_tau_mul_of_tendsto_pos`);
* **(iv)** — the nondial first-layer gates saturate to `1`, proved *honestly* from the
  genericity separation margin `SignRegionData.separation_positive`
  (`expCloseTo_dialGateAlong_zero_of_pos`);
* **GAP3 (first layer)** — the first-layer separation value equals the layer-0 dialed
  slope (`signRegionSeparationValue_eq_matrixBilin`), supplying the strict positivity;
* **GAP2 (base case)** — along the dial path the layer-1 probe point converges to the
  saturated recursion point `P*_1` (`tendsto_dialActualProbePoint_one`);
* **GAP3 (`j = 0`)** — the saturated-point layer-1 slope equals the genericity margin
  `signRegionLevelValue` (`matrixBilin_satPoint_eq_levelValue`), so the first deeper layer
  saturates (v) *fully honestly* from `SignRegionData.level_positive`
  (`expCloseTo_dialGateAlong_one_of_signRegionData`);
* **GAP2 (general layer induction)** — along the dial path the layer-`n` actual probe point
  converges to the saturated recursion point `dialSatPoint n` for every `n`
  (`tendsto_dialActualProbePoint`), by induction coupling GAP1 with per-layer gate
  saturation; the general margin identity `matrixBilin_dialSatPoint_eq_levelValue`
  (GAP3 for all `j`) identifies each deeper saturated-point slope with `signRegionLevelValue`.
  This discharges `DeeperSlopeMargins` from `SignRegionData.level_positive` outright
  (`deeperSlopeMargins_of_signRegionData`);
* the full assembly `headDialStatement_of_signRegionData`, instantiating the gates with
  `actualProbeGate ∘ headDialPath`.  All estimates (i)/(iii)/(iv) and the deeper-gate
  saturation (v) for every layer `ℓ ≥ 1` are now proved outright from the genericity
  margins; the assembly depends only on `SignRegionData θ h`.
-/

/-! ## Closeness bridges and helpers -/

/-- Bridge: the data-carrying `EventuallyExpClose` yields the propositional `ExpCloseTo`. -/
theorem expCloseTo_of_eventuallyExpClose {f : ℝ → ℝ} {a : ℝ}
    (h : EventuallyExpClose f a) : ExpCloseTo f a :=
  ⟨h.rate, h.coeff, h.start, h.rate_pos, h.coeff_nonneg, h.bound⟩

/-- Pointwise-equal functions share `ExpCloseTo`. -/
theorem expCloseTo_congr {f g : ℝ → ℝ} {a : ℝ}
    (hfg : ∀ τ, f τ = g τ) (h : ExpCloseTo g a) : ExpCloseTo f a := by
  obtain ⟨rate, coeff, start, hr, hc, hb⟩ := h
  exact ⟨rate, coeff, start, hr, hc, fun τ hτ => by rw [hfg τ]; exact hb τ hτ⟩

/-- Pointwise-equal functions share `AlgCloseTo`. -/
theorem algCloseTo_congr {f g : ℝ → ℝ} {a : ℝ}
    (hfg : ∀ τ, f τ = g τ) (h : AlgCloseTo g a) : AlgCloseTo f a := by
  obtain ⟨coeff, start, hc, hs, hb⟩ := h
  exact ⟨coeff, start, hc, hs, fun τ hτ => by rw [hfg τ]; exact hb τ hτ⟩

/-- A constant function is exponentially close to its value (with zero coefficient). -/
theorem expCloseTo_const (a : ℝ) : ExpCloseTo (fun _ => a) a :=
  ⟨1, 0, 0, one_pos, le_refl 0, fun τ _ => by simp⟩

/-- `ExpCloseTo` implies topological convergence. -/
theorem ExpCloseTo.tendsto {f : ℝ → ℝ} {a : ℝ} (h : ExpCloseTo f a) :
    Tendsto f atTop (𝓝 a) := by
  obtain ⟨rate, coeff, start, hr, hc, hb⟩ := h
  have hee : EventuallyExpClose f a := ⟨rate, hr, coeff, hc, start, hb⟩
  exact hee.tendsto

/-- `AlgCloseTo` implies topological convergence (algebraic `C/τ → 0` squeeze). -/
theorem AlgCloseTo.tendsto {f : ℝ → ℝ} {a : ℝ} (h : AlgCloseTo f a) :
    Tendsto f atTop (𝓝 a) := by
  obtain ⟨coeff, start, hc, hs, hb⟩ := h
  have hsub : Tendsto (fun τ => f τ - a) atTop (𝓝 0) := by
    have hbound : ∀ᶠ τ in atTop, ‖f τ - a‖ ≤ coeff / τ := by
      filter_upwards [eventually_ge_atTop start] with τ hτ
      simpa [Real.norm_eq_abs] using hb τ hτ
    exact squeeze_zero_norm' hbound tendsto_const_div_atTop
  simpa using hsub.add_const a

/-! ## GAP1: dial-path convergence -/

/-- **GAP1**.  The `h`-dial path based at `p` converges to `p` as `τ → ∞`; the correction
`(c/τ)•y` vanishes in both coordinates. -/
theorem tendsto_headDialPath {k d : Nat} (A : Fin k → Matrix (Fin d) (Fin d) ℝ)
    (h : Fin k) (b : ℝ) (p : ProbePair d) (t : ℝ) :
    Tendsto (fun τ => headDialPath A h b p t τ) atTop (𝓝 p) := by
  have hw : Tendsto (fun τ => (headDialPath A h b p t τ).1) atTop (𝓝 p.1) := by
    have := (tendsto_dialPath_smul_atTop (headDialDirection A h p) (headDialC b t)).const_sub p.1
    simpa [headDialPath, dialProbe, dialW, sub_zero] using this
  have hv : Tendsto (fun τ => (headDialPath A h b p t τ).2) atTop (𝓝 p.2) := by
    have := (tendsto_dialPath_smul_atTop (headDialDirection A h p) (headDialC b t)).const_add p.2
    simpa [headDialPath, dialProbe, dialV, add_zero] using this
  exact hw.prodMk_nhds hv

/-! ## The saturation engine and the layer-0 slope -/

/-- The saturation engine: if the (dialed) slope tends to a positive limit, the gate
`sig(τ · slope(τ) + b)` is `ExpCloseTo 1`.  Wraps the reusable cascade-saturation lemma
`eventuallyExpClose_sig_tau_mul_of_tendsto_pos`. -/
theorem expCloseTo_sig_of_tendsto_pos {lam : ℝ → ℝ} {Λ b : ℝ}
    (hΛ : 0 < Λ) (hlam : Tendsto lam atTop (𝓝 Λ)) :
    ExpCloseTo (fun τ => sig (τ * lam τ + b)) 1 :=
  expCloseTo_of_eventuallyExpClose (eventuallyExpClose_sig_tau_mul_of_tendsto_pos hΛ hlam)

/-- Negative mirror of `expCloseTo_sig_of_tendsto_pos`: if the (dialed) slope tends to a
negative limit, the gate `sig(τ · slope(τ) + b)` is `ExpCloseTo 0`. -/
theorem expCloseTo_sig_of_tendsto_neg {lam : ℝ → ℝ} {Λ b : ℝ}
    (hΛ : Λ < 0) (hlam : Tendsto lam atTop (𝓝 Λ)) :
    ExpCloseTo (fun τ => sig (τ * lam τ + b)) 0 :=
  expCloseTo_of_eventuallyExpClose (eventuallyExpClose_sig_tau_mul_of_tendsto_neg hΛ hlam)

/-- The actual probe slope at layer `0` is the base bilinear slope. -/
theorem actualProbeSlope_zero (r : Nat) {m k d : Nat} (θ : Params (m + 1) k d)
    (w v : Vec d) (τ : ℝ) (a : Fin k) (hlv : 0 < m + 1) :
    actualProbeSlope r θ w v τ ⟨0, hlv⟩ a =
      matrixBilin (attentionMatrix θ 0 a) w v := by
  have h0 : (⟨0, hlv⟩ : Fin (m + 1)) = 0 := by apply Fin.ext; simp
  simp [actualProbeSlope, h0, actualProbePoint_zero]

/-! ## Instantiation of the k-head gate family along the dial path -/

/-- The k-head gate family along the `h`-dial path based at `x = (p, t)`.  For an
out-of-range layer (`level ≥ m + 1`) the value is the harmless constant `1`. -/
noncomputable def dialGateAlong (r : Nat) {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (b : ℝ) : KHeadGateAlongBase k d :=
  fun level a x τ =>
    if hlv : level < m + 1 then
      actualProbeGate r θ
        (headDialPath (attentionMatrix θ 0) h b x.1 x.2 τ).1
        (headDialPath (attentionMatrix θ 0) h b x.1 x.2 τ).2 τ ⟨level, hlv⟩ a
    else 1

/-- Layer-0 form of the dialed gate: it is the sigmoid of the layer-0 dialed slope. -/
theorem dialGateAlong_zero_eq (r : Nat) {m k d : Nat} (θ : Params (m + 1) k d)
    (h a : Fin k) (b : ℝ) (x : ProbePair d × ℝ) (τ : ℝ) :
    dialGateAlong r θ h b 0 a x τ =
      sig (τ * firstHeadSlope (attentionMatrix θ 0) a
        (headDialPath (attentionMatrix θ 0) h b x.1 x.2 τ) + logScale r) := by
  simp only [dialGateAlong]
  rw [dif_pos (Nat.succ_pos m), actualProbeGate_eq_sig,
    actualProbeSlope_zero r θ _ _ τ a (Nat.succ_pos m)]
  rfl

/-! ## GAP3 (first layer): margin identification -/

/-- **GAP3 (first layer)**.  The genericity same-layer separation value is exactly the
layer-0 bilinear slope of the corresponding head; this transports `separation_positive`
into the strict positivity consumed by the saturation engine. -/
theorem signRegionSeparationValue_eq_matrixBilin {m k d : Nat}
    (θ : Params (m + 1) k d) {h : Fin k} (a : AnchorSeparationHead k h)
    (x : ProbePair d × ℝ) :
    signRegionSeparationValue θ a x = matrixBilin (attentionMatrix θ 0 a.1) x.1.1 x.1.2 :=
  rfl

/-! ## (iv): nondial first-layer gate saturation -/

/-- **(iv)**.  If the base layer-0 slope for head `a` is strictly positive, the dialed
`a`-gate at layer 0 is exponentially close to `1`.  The saturation content is genuinely
produced by the `eventuallyExpClose` machinery; positivity is the only input. -/
theorem expCloseTo_dialGateAlong_zero_of_pos (r : Nat) {m k d : Nat}
    (θ : Params (m + 1) k d) (h a : Fin k) (b : ℝ) (x : ProbePair d × ℝ)
    (hpos : 0 < matrixBilin (attentionMatrix θ 0 a) x.1.1 x.1.2) :
    ExpCloseTo (fun τ => dialGateAlong r θ h b 0 a x τ) 1 := by
  have hslope : Tendsto (fun τ => firstHeadSlope (attentionMatrix θ 0) a
      (headDialPath (attentionMatrix θ 0) h b x.1 x.2 τ)) atTop
      (𝓝 (matrixBilin (attentionMatrix θ 0 a) x.1.1 x.1.2)) := by
    have hcont : Continuous (fun q : ProbePair d => matrixBilin (attentionMatrix θ 0 a) q.1 q.2) :=
      continuous_matrixBilin (attentionMatrix θ 0 a) continuous_fst continuous_snd
    exact (hcont.tendsto x.1).comp (tendsto_headDialPath (attentionMatrix θ 0) h b x.1 x.2)
  have heng := expCloseTo_sig_of_tendsto_pos (b := logScale r) hpos hslope
  exact expCloseTo_congr (fun τ => dialGateAlong_zero_eq r θ h a b x τ) heng

/-! ## Deeper-slope margin input (GAP2/GAP3 interface) -/

/-- The deeper-layer slope margin along the dial path: for every deeper layer `level ≥ 1`
in range, every head `a`, and every base point `x ∈ K`, the dialed slope converges to a
strictly positive limit.

This is the genericity content of `SignRegionData.level_positive` transported along the
dial path.  It is discharged below by `deeperSlopeMargins_of_signRegionData`, via the
general layer induction (GAP2, `tendsto_dialActualProbePoint`) coupling point-continuity of
`gatedEffectivePoint` with per-layer gate saturation, together with the general deeper
margin identification (GAP3, `matrixBilin_dialSatPoint_eq_levelValue`).  It remains a named
intermediate so that the *saturation* conclusion (v) is produced honestly from the
`eventuallyExpClose` machinery below.

The bound is `2 ≤ level`: the first deeper layer (`level = 1`) is discharged fully from the
genericity margins (see `expCloseTo_dialGateAlong_one_of_signRegionData`), so only layers
`≥ 2` — whose margins need the general layer induction (GAP2, `ℓ ≥ 2`) — are assumed. -/
def DeeperSlopeMargins (r : Nat) {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (b : ℝ) (K : Set (ProbePair d × ℝ)) : Prop :=
  ∀ (level : Nat), 2 ≤ level → (hlv : level < m + 1) → ∀ (a : Fin k),
    ∀ x ∈ K, ∃ Λ : ℝ, 0 < Λ ∧
      Tendsto (fun τ => actualProbeSlope r θ
        (headDialPath (attentionMatrix θ 0) h b x.1 x.2 τ).1
        (headDialPath (attentionMatrix θ 0) h b x.1 x.2 τ).2 τ ⟨level, hlv⟩ a)
        atTop (𝓝 Λ)

/-- **(v)**, layers `≥ 2`.  Given the deeper-slope margins, every layer-`≥ 2` dialed gate is
exponentially close to `1`.  Out-of-range layers give the constant gate `1`; in-range
layers saturate via the `eventuallyExpClose` engine. -/
theorem expCloseTo_dialGateAlong_deeper (r : Nat) {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (b : ℝ) (K : Set (ProbePair d × ℝ))
    (hDeep : DeeperSlopeMargins r θ h b K)
    (level : Nat) (hlevel : 2 ≤ level) (a : Fin k) (x : ProbePair d × ℝ) (hx : x ∈ K) :
    ExpCloseTo (fun τ => dialGateAlong r θ h b level a x τ) 1 := by
  by_cases hlv : level < m + 1
  · obtain ⟨Λ, hΛ, hslope⟩ := hDeep level hlevel hlv a x hx
    have hgate : ∀ τ, dialGateAlong r θ h b level a x τ =
        sig (τ * actualProbeSlope r θ
          (headDialPath (attentionMatrix θ 0) h b x.1 x.2 τ).1
          (headDialPath (attentionMatrix θ 0) h b x.1 x.2 τ).2 τ ⟨level, hlv⟩ a
          + logScale r) := by
      intro τ
      simp only [dialGateAlong]
      rw [dif_pos hlv, actualProbeGate_eq_sig]
    have heng := expCloseTo_sig_of_tendsto_pos (b := logScale r) hΛ hslope
    exact expCloseTo_congr hgate heng
  · have hconst : ∀ τ, dialGateAlong r θ h b level a x τ = 1 := by
      intro τ
      simp only [dialGateAlong]
      rw [dif_neg hlv]
    exact expCloseTo_congr hconst (expCloseTo_const 1)

/-! ## GAP2 (base case): layer-1 point convergence to the saturated point

Along the `θ`-dial path the layer-1 actual probe point converges to the saturated
recursion point `P*_1` (head-`h` gate `= t`, all other layer-0 gates `= 1`).  This is the
base case of the major layer induction: it couples GAP1 (path convergence) with the
per-head gate saturation (dial head via (iii); other heads via (iv)).  From it we obtain
the honest layer-1 deeper-gate saturation (v), where the only remaining input is the
strict positivity of the concrete saturated-point layer-1 slope — exactly the
`level_positive` genericity margin content (identified via GAP3, `j = 0`). -/

/-- The saturated layer-0 gate vector: the dial head reaches `t`, all others reach `1`. -/
noncomputable def satGate {k : Nat} (t : ℝ) (h : Fin k) : Fin k → ℝ :=
  fun a => if a = h then t else 1

/-- Joint continuity of the first gated probe step in `(gates, w, v)`. -/
theorem continuous_gatedEffectivePoint_zero {m k d : Nat} (θ : Params (m + 1) k d) :
    Continuous (fun z : (Fin k → ℝ) × (Vec d × Vec d) =>
      gatedEffectivePoint θ 0 z.1 z.2.1 z.2.2) := by
  have hfst : Continuous (fun z : (Fin k → ℝ) × (Vec d × Vec d) =>
      (collapseMatrix θ 0 - gatedValueSum θ 0 z.1) *ᵥ z.2.1) := by
    unfold gatedValueSum collapseMatrix valueSum Matrix.mulVec
    fun_prop
  have hsnd : Continuous (fun z : (Fin k → ℝ) × (Vec d × Vec d) =>
      collapseMatrix θ 0 *ᵥ z.2.2 + gatedValueSum θ 0 z.1 *ᵥ z.2.1) := by
    unfold gatedValueSum collapseMatrix valueSum Matrix.mulVec
    fun_prop
  exact hfst.prodMk hsnd

/-- Layer-0 gate along a dial path is the sigmoid of the layer-0 slope. -/
theorem layerGates_zero_dial_eq (r : Nat) {m k d : Nat} (θ : Params (m + 1) k d)
    (a : Fin k) (w v : Vec d) (τ : ℝ) :
    layerGates r θ 0 w v τ a =
      sig (τ * firstHeadSlope (attentionMatrix θ 0) a (w, v) + logScale r) := by
  simp [layerGates, headGate, firstHeadSlope]

/-- The layer-0 dialed gate vector converges to the saturated gate vector. -/
theorem tendsto_dialLayerGates_zero (r : Nat) {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (p : ProbePair d) (t : ℝ)
    (ht_pos : 0 < t) (ht_lt_one : t < 1)
    (hq : firstHeadSlope (attentionMatrix θ 0) h p = 0)
    (hpi : firstHeadPi (attentionMatrix θ 0) h p ≠ 0)
    (hsep : ∀ a : Fin k, a ≠ h → 0 < matrixBilin (attentionMatrix θ 0 a) p.1 p.2) :
    Tendsto (fun τ => layerGates r θ 0
        (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
        (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2 τ)
      atTop (𝓝 (satGate t h)) := by
  rw [tendsto_pi_nhds]
  intro a
  have hgeq : ∀ τ, layerGates r θ 0
      (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
      (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2 τ a =
      dialGateAlong r θ h (logScale r) 0 a (p, t) τ := by
    intro τ
    rw [layerGates_zero_dial_eq, dialGateAlong_zero_eq]
  by_cases hah : a = h
  · subst hah
    have hsat : satGate t a a = t := by simp [satGate]
    rw [hsat]
    have halg := headDial_gate_tracks (attentionMatrix θ 0) a (logScale r) t p
      ht_pos ht_lt_one hq hpi
    have halg' : AlgCloseTo (fun τ => dialGateAlong r θ a (logScale r) 0 a (p, t) τ) t :=
      algCloseTo_congr (fun τ => dialGateAlong_zero_eq r θ a a (logScale r) (p, t) τ) halg
    exact (halg'.tendsto).congr (fun τ => (hgeq τ).symm)
  · have hsat : satGate t h a = 1 := by simp [satGate, hah]
    rw [hsat]
    have hpos : 0 < matrixBilin (attentionMatrix θ 0 a) ((p, t) : ProbePair d × ℝ).1.1
        ((p, t) : ProbePair d × ℝ).1.2 := hsep a hah
    have hsatur : ExpCloseTo (fun τ => dialGateAlong r θ h (logScale r) 0 a (p, t) τ) 1 :=
      expCloseTo_dialGateAlong_zero_of_pos r θ h a (logScale r) (p, t) hpos
    exact (hsatur.tendsto).congr (fun τ => (hgeq τ).symm)

/-- The layer-1 actual probe point is one gated step at layer `0`. -/
theorem actualProbePoint_one (r : Nat) {m k d : Nat} (θ : Params (m + 1) k d)
    (w v : Vec d) (hn : 1 ≤ m + 1) (τ : ℝ) :
    actualProbePoint r θ w v 1 hn τ =
      gatedEffectivePoint θ 0 (layerGates r θ 0 w v τ) w v := by
  rw [actualProbePoint_succ]
  have h0 : (⟨0, Nat.lt_of_succ_le hn⟩ : Fin (m + 1)) = 0 := by apply Fin.ext; simp
  simp only [actualProbePoint_zero, h0]

/-- **GAP2 (base case)**.  Along the `θ`-dial path, the layer-1 actual probe point
converges to the saturated point `P*_1` (head-`h` gate `= t`, all others `= 1`). -/
theorem tendsto_dialActualProbePoint_one (r : Nat) {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (p : ProbePair d) (t : ℝ)
    (ht_pos : 0 < t) (ht_lt_one : t < 1)
    (hq : firstHeadSlope (attentionMatrix θ 0) h p = 0)
    (hpi : firstHeadPi (attentionMatrix θ 0) h p ≠ 0)
    (hsep : ∀ a : Fin k, a ≠ h → 0 < matrixBilin (attentionMatrix θ 0 a) p.1 p.2) :
    Tendsto (fun τ => actualProbePoint r θ
        (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
        (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2 1
        (Nat.succ_le_succ (Nat.zero_le m)) τ)
      atTop (𝓝 (gatedEffectivePoint θ 0 (satGate t h) p.1 p.2)) := by
  have hF := continuous_gatedEffectivePoint_zero θ
  have hgate := tendsto_dialLayerGates_zero r θ h p t ht_pos ht_lt_one hq hpi hsep
  have hpath := tendsto_headDialPath (attentionMatrix θ 0) h (logScale r) p t
  have hcomp := (hF.tendsto (satGate t h, p)).comp (hgate.prodMk_nhds hpath)
  refine hcomp.congr (fun τ => ?_)
  simp only [Function.comp_apply]
  rw [actualProbePoint_one]

/-- The layer-1 dialed slope converges to the saturated-point layer-1 slope. -/
theorem tendsto_dialActualProbeSlope_one (r : Nat) {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (p : ProbePair d) (t : ℝ) (b : Fin k) (h1 : 1 < m + 1)
    (ht_pos : 0 < t) (ht_lt_one : t < 1)
    (hq : firstHeadSlope (attentionMatrix θ 0) h p = 0)
    (hpi : firstHeadPi (attentionMatrix θ 0) h p ≠ 0)
    (hsep : ∀ a : Fin k, a ≠ h → 0 < matrixBilin (attentionMatrix θ 0 a) p.1 p.2) :
    Tendsto (fun τ => actualProbeSlope r θ
        (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
        (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2 τ ⟨1, h1⟩ b)
      atTop (𝓝 (matrixBilin (attentionMatrix θ ⟨1, h1⟩ b)
        (gatedEffectivePoint θ 0 (satGate t h) p.1 p.2).1
        (gatedEffectivePoint θ 0 (satGate t h) p.1 p.2).2)) := by
  have hpt := tendsto_dialActualProbePoint_one r θ h p t ht_pos ht_lt_one hq hpi hsep
  have hcont : Continuous (fun q : ProbePair d =>
      matrixBilin (attentionMatrix θ ⟨1, h1⟩ b) q.1 q.2) :=
    continuous_matrixBilin _ continuous_fst continuous_snd
  exact (hcont.tendsto _).comp hpt

/-- **Honest (v) for the first deeper layer**.  Given strict positivity of the saturated
layer-1 slope (the `level_positive` genericity margin content, identified via GAP3 with
`j = 0`), the layer-1 dialed gate saturates to `1`.  The `Tendsto` is proved via the GAP2
base case; only the positivity of the concrete saturated-point slope is an input. -/
theorem expCloseTo_dialGateAlong_one_of_pos (r : Nat) {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (p : ProbePair d) (t : ℝ) (b : Fin k) (h1 : 1 < m + 1)
    (ht_pos : 0 < t) (ht_lt_one : t < 1)
    (hq : firstHeadSlope (attentionMatrix θ 0) h p = 0)
    (hpi : firstHeadPi (attentionMatrix θ 0) h p ≠ 0)
    (hsep : ∀ a : Fin k, a ≠ h → 0 < matrixBilin (attentionMatrix θ 0 a) p.1 p.2)
    (hposdeep : 0 < matrixBilin (attentionMatrix θ ⟨1, h1⟩ b)
        (gatedEffectivePoint θ 0 (satGate t h) p.1 p.2).1
        (gatedEffectivePoint θ 0 (satGate t h) p.1 p.2).2) :
    ExpCloseTo (fun τ => dialGateAlong r θ h (logScale r) 1 b (p, t) τ) 1 := by
  have hslope := tendsto_dialActualProbeSlope_one r θ h p t b h1 ht_pos ht_lt_one hq hpi hsep
  have heng := expCloseTo_sig_of_tendsto_pos (b := logScale r) hposdeep hslope
  have hgate : ∀ τ, dialGateAlong r θ h (logScale r) 1 b (p, t) τ =
      sig (τ * actualProbeSlope r θ
        (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
        (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2 τ ⟨1, h1⟩ b
        + logScale r) := by
    intro τ
    simp only [dialGateAlong]
    rw [dif_pos h1, actualProbeGate_eq_sig]
  exact expCloseTo_congr hgate heng

/-! ## GAP3 (`j = 0`): deeper-margin identification and fully-honest layer-1 (v)

We identify the concrete saturated-point layer-1 slope with the genericity deeper-level
margin `signRegionLevelValue`, so that the positivity input for the layer-1 saturation
comes *directly* from `SignRegionData.level_positive` (no separate positivity hypothesis).
Combined with the GAP2 base case this yields the first deeper layer's saturation (v)
entirely from genericity margins + the `eventuallyExpClose` machinery. -/

/-- `matrixBilin` is additive in its right argument (k-head form). -/
theorem matrixBilin_add_right' {d : Nat} (A : Matrix (Fin d) (Fin d) ℝ)
    (w u v : Vec d) :
    matrixBilin A w (u + v) = matrixBilin A w u + matrixBilin A w v := by
  simp [matrixBilin, Matrix.mulVec_add, dotProduct_add]

/-- Adjoint identity for the transpose: `(Cᵀ *ᵥ u) ⬝ᵥ v = u ⬝ᵥ (C *ᵥ v)`. -/
theorem adjoint_dotProduct {d : Nat} (C : Matrix (Fin d) (Fin d) ℝ) (u v : Vec d) :
    (Cᵀ *ᵥ u) ⬝ᵥ v = u ⬝ᵥ (C *ᵥ v) := by
  rw [dotProduct_comm (Cᵀ *ᵥ u) v,
    dotProduct_mulVec_eq_dotProduct_transpose_mulVec Cᵀ v u, Matrix.transpose_transpose]

/-- `matrixBilin A w u = (Aᵀ *ᵥ w) ⬝ᵥ u`. -/
theorem matrixBilin_eq_transpose_dotProduct {d : Nat} (A : Matrix (Fin d) (Fin d) ℝ)
    (w u : Vec d) :
    matrixBilin A w u = (Aᵀ *ᵥ w) ⬝ᵥ u := by
  rw [matrixBilin, dotProduct_mulVec_eq_dotProduct_transpose_mulVec A w u,
    dotProduct_comm u (Aᵀ *ᵥ w)]

/-- The one-step collapsed prefix is the layer-0 collapse matrix. -/
theorem collapsePrefix_one {m k d : Nat} (θ : Params (m + 1) k d) :
    collapsePrefix θ 1 = collapseMatrix θ 0 := by
  have h0 : (⟨0, Nat.succ_pos m⟩ : Fin (m + 1)) = 0 := by apply Fin.ext; simp
  simp only [collapsePrefix, cornerCPrefix, matrixPrefixProduct_succ,
    matrixPrefixProduct_zero, mul_one, collapseMatrixStream]
  rw [dif_pos (Nat.succ_pos m), h0]

/-- The saturated layer-0 value sum: `∑ (satGate) V = ∑ V - (1-t) V_h`. -/
theorem gatedValueSum_satGate {m k d : Nat} (θ : Params (m + 1) k d) (h : Fin k) (t : ℝ) :
    gatedValueSum θ 0 (satGate t h) = valueSum θ 0 - (1 - t) • valueMatrix θ 0 h := by
  have key : ∀ a : Fin k, (satGate t h) a • valueMatrix θ 0 a
      = valueMatrix θ 0 a + (if a = h then (t - 1) • valueMatrix θ 0 h else 0) := by
    intro a
    by_cases ha : a = h
    · subst ha
      have hsh : satGate t a a = t := if_pos rfl
      rw [hsh, if_pos rfl, sub_smul, one_smul]
      abel
    · have hsa : satGate t h a = 1 := if_neg ha
      rw [hsa, if_neg ha, one_smul, add_zero]
  rw [gatedValueSum, Finset.sum_congr rfl (fun a _ => key a), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ h]
  simp only [Finset.mem_univ, if_true, valueSum]
  module

/-- The saturated point's `w`-coordinate is the dialed first-stream vector `headDialW`. -/
theorem gatedEffectivePoint_satGate_fst {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (t : ℝ) (p : ProbePair d) :
    (gatedEffectivePoint θ 0 (satGate t h) p.1 p.2).1 = headDialW θ h t p.1 := by
  rw [gatedEffectivePoint_fst, gatedValueSum_satGate, collapseMatrix, headDialW]
  congr 1
  abel

/-- **GAP3 (`j = 0` margin identification)**.  The saturated-point layer-1 slope equals the
genericity deeper-level margin `signRegionLevelValue`. -/
theorem matrixBilin_satPoint_eq_levelValue {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (p : ProbePair d) (t : ℝ) (b : Fin k) (hm : 0 < m) :
    matrixBilin (attentionMatrix θ (laterLayer ⟨0, hm⟩) b)
      (gatedEffectivePoint θ 0 (satGate t h) p.1 p.2).1
      (gatedEffectivePoint θ 0 (satGate t h) p.1 p.2).2
    = signRegionLevelValue θ h ⟨0, hm⟩ b ((p.1, p.2), t) := by
  have hval : ((⟨0, hm⟩ : Fin m).val + 1) = 1 := rfl
  have hmat : collapseMatrix θ 0 - 1 - (1 - t) • valueMatrix θ 0 h
      = valueSum θ 0 - (1 - t) • valueMatrix θ 0 h := by
    rw [collapseMatrix]; abel
  rw [gatedEffectivePoint_satGate_fst, gatedEffectivePoint_snd, gatedValueSum_satGate,
    matrixBilin_add_right']
  simp only [signRegionLevelValue, anchorRowValue, anchorRowLevel, anchorRowGradient,
    anchorRowConstant]
  rw [hval, collapsePrefix_one, adjoint_dotProduct, ← matrixBilin_eq_transpose_dotProduct,
    hmat]

/-- **Fully honest (v) for the first deeper layer**.  For any point of the sign region and
`m ≥ 1`, the layer-1 dialed gate saturates to `1`, with positivity supplied *directly* by
the genericity margin `SignRegionData.level_positive` (via the GAP3 `j = 0` identity) and
the `Tendsto` supplied by the GAP2 base case.  No positivity hypothesis is assumed. -/
theorem expCloseTo_dialGateAlong_one_of_signRegionData (r : Nat) {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (D : SignRegionData θ h) (b : Fin k)
    (x : ProbePair d × ℝ) (hxr : x ∈ D.region) (hm : 0 < m) :
    ExpCloseTo (fun τ => dialGateAlong r θ h (logScale r) 1 b x τ) 1 := by
  have S := signRegionData_signRegionInterface D
  have hsep : ∀ a : Fin k, a ≠ h → 0 < matrixBilin (attentionMatrix θ 0 a) x.1.1 x.1.2 := by
    intro a ha
    have hpos := D.separation_positive x hxr ⟨a, ha⟩
    rwa [signRegionSeparationValue_eq_matrixBilin] at hpos
  have hposdeep : 0 < matrixBilin (attentionMatrix θ (laterLayer ⟨0, hm⟩) b)
      (gatedEffectivePoint θ 0 (satGate x.2 h) x.1.1 x.1.2).1
      (gatedEffectivePoint θ 0 (satGate x.2 h) x.1.1 x.1.2).2 := by
    rw [matrixBilin_satPoint_eq_levelValue]
    exact D.level_positive x hxr ⟨0, hm⟩ b
  exact expCloseTo_dialGateAlong_one_of_pos r θ h x.1 x.2 b (Nat.succ_lt_succ hm)
    (S.t_pos x hxr) (S.t_lt_one x hxr) (S.point_on_quadric x hxr) (S.pi_ne_zero x hxr)
    hsep hposdeep


/-! ## GAP2 (general layer): the saturated recursion and its point convergence

We now discharge the general-`ℓ` obligation.  The strategy is the per-point `Tendsto`
route: along the `θ`-dial path the layer-`n` actual probe point converges to a saturated
recursion point `dialSatPoint n` (head-`h` layer-0 gate `→ t`, all other layer-0 gates and
all deeper gates `→ 1`), by induction on `n`.  Each deeper gate saturates because its slope
tends to the (positive) saturated-point slope, which the general margin identity
(`matrixBilin_dialSatPoint_eq_levelValue`) identifies with the genericity level margin
`signRegionLevelValue`. -/

/-- Joint continuity of the gated probe step at an arbitrary layer `l`, in `(gates, w, v)`. -/
theorem continuous_gatedEffectivePoint {m k d : Nat} (θ : Params (m + 1) k d)
    (l : Fin (m + 1)) :
    Continuous (fun z : (Fin k → ℝ) × (Vec d × Vec d) =>
      gatedEffectivePoint θ l z.1 z.2.1 z.2.2) := by
  have hfst : Continuous (fun z : (Fin k → ℝ) × (Vec d × Vec d) =>
      (collapseMatrix θ l - gatedValueSum θ l z.1) *ᵥ z.2.1) := by
    unfold gatedValueSum collapseMatrix valueSum Matrix.mulVec
    fun_prop
  have hsnd : Continuous (fun z : (Fin k → ℝ) × (Vec d × Vec d) =>
      collapseMatrix θ l *ᵥ z.2.2 + gatedValueSum θ l z.1 *ᵥ z.2.1) := by
    unfold gatedValueSum collapseMatrix valueSum Matrix.mulVec
    fun_prop
  exact hfst.prodMk hsnd

/-- All-ones gates yield the plain value sum. -/
theorem gatedValueSum_one {m k d : Nat} (θ : Params (m + 1) k d) (l : Fin (m + 1)) :
    gatedValueSum θ l (fun _ => 1) = valueSum θ l := by
  simp [gatedValueSum, valueSum]

/-- The saturated layer-`n` gate vector along the recursion: at layer `0` it is `satGate`;
at every deeper layer it is the all-ones vector. -/
noncomputable def dialSatGate {k : Nat} (t : ℝ) (h : Fin k) (n : Nat) : Fin k → ℝ :=
  if n = 0 then satGate t h else fun _ => 1

@[simp] theorem dialSatGate_zero {k : Nat} (t : ℝ) (h : Fin k) :
    dialSatGate t h 0 = satGate t h := by
  simp [dialSatGate]

theorem dialSatGate_succ {k : Nat} (t : ℝ) (h : Fin k) (n : Nat) :
    dialSatGate t h (n + 1) = (fun _ => 1) := by
  simp [dialSatGate]

/-- The saturated recursion point at layer `n`: run the gated step with the saturated gate
vector at every layer (`satGate` at layer `0`, all-ones deeper), extending by the previous
value past the network depth. -/
noncomputable def dialSatPoint {m k d : Nat} (θ : Params (m + 1) k d) (h : Fin k)
    (p : ProbePair d) (t : ℝ) : Nat → ProbePoint d
  | 0 => (p.1, p.2)
  | n + 1 =>
      if hn : n < m + 1 then
        gatedEffectivePoint θ ⟨n, hn⟩ (dialSatGate t h n)
          (dialSatPoint θ h p t n).1 (dialSatPoint θ h p t n).2
      else dialSatPoint θ h p t n

@[simp] theorem dialSatPoint_zero {m k d : Nat} (θ : Params (m + 1) k d) (h : Fin k)
    (p : ProbePair d) (t : ℝ) :
    dialSatPoint θ h p t 0 = (p.1, p.2) :=
  rfl

theorem dialSatPoint_succ_of_lt {m k d : Nat} (θ : Params (m + 1) k d) (h : Fin k)
    (p : ProbePair d) (t : ℝ) (n : Nat) (hn : n < m + 1) :
    dialSatPoint θ h p t (n + 1) =
      gatedEffectivePoint θ ⟨n, hn⟩ (dialSatGate t h n)
        (dialSatPoint θ h p t n).1 (dialSatPoint θ h p t n).2 := by
  rw [dialSatPoint]
  exact dif_pos hn

/-- `dialSatPoint` at layer `1` is the layer-0 saturated step, matching the base case. -/
theorem dialSatPoint_one {m k d : Nat} (θ : Params (m + 1) k d) (h : Fin k)
    (p : ProbePair d) (t : ℝ) :
    dialSatPoint θ h p t 1 = gatedEffectivePoint θ 0 (satGate t h) p.1 p.2 := by
  have h0 : (⟨0, Nat.succ_pos m⟩ : Fin (m + 1)) = 0 := by apply Fin.ext; simp
  rw [dialSatPoint_succ_of_lt θ h p t 0 (Nat.succ_pos m)]
  simp only [dialSatGate_zero, dialSatPoint_zero, h0]

theorem dialSatGate_pos {k : Nat} (t : ℝ) (h : Fin k) {n : Nat} (hn : 0 < n) :
    dialSatGate t h n = fun _ => 1 := by
  rw [dialSatGate, if_neg (Nat.pos_iff_ne_zero.mp hn)]

theorem dialSatPoint_succ_of_ge {m k d : Nat} (θ : Params (m + 1) k d) (h : Fin k)
    (p : ProbePair d) (t : ℝ) (n : Nat) (hn : ¬ n < m + 1) :
    dialSatPoint θ h p t (n + 1) = dialSatPoint θ h p t n := by
  rw [dialSatPoint]; exact dif_neg hn

/-- Recursion for the collapsed prefix product inside the network depth. -/
theorem collapsePrefix_succ_of_lt {m k d : Nat} (θ : Params (m + 1) k d) (n : Nat)
    (hn : n < m + 1) :
    collapsePrefix θ (n + 1) = collapseMatrix θ ⟨n, hn⟩ * collapsePrefix θ n := by
  have hstream : collapseMatrixStream θ n = collapseMatrix θ ⟨n, hn⟩ := by
    rw [collapseMatrixStream, dif_pos hn]
  simp only [collapsePrefix, cornerCPrefix, matrixPrefixProduct_succ, hstream]

/-- Beyond the network depth the collapsed prefix product is constant. -/
theorem collapsePrefix_succ_of_ge {m k d : Nat} (θ : Params (m + 1) k d) (n : Nat)
    (hn : ¬ n < m + 1) :
    collapsePrefix θ (n + 1) = collapsePrefix θ n := by
  have hstream : collapseMatrixStream θ n = 1 := by
    rw [collapseMatrixStream, dif_neg hn]
  simp only [collapsePrefix, cornerCPrefix, matrixPrefixProduct_succ, hstream, one_mul]

/-- **Closed form (w-coordinate)**.  For every layer `n ≥ 1` the saturated recursion point's
first coordinate is the dialed first-stream vector `headDialW` (the all-ones deeper gates
leave the `w`-stream unchanged). -/
theorem dialSatPoint_fst {m k d : Nat} (θ : Params (m + 1) k d) (h : Fin k)
    (p : ProbePair d) (t : ℝ) (n : Nat) (hn1 : 1 ≤ n) :
    (dialSatPoint θ h p t n).1 = headDialW θ h t p.1 := by
  induction n with
  | zero => exact absurd hn1 (by omega)
  | succ n ih =>
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · subst hn0
        rw [dialSatPoint_one]
        exact gatedEffectivePoint_satGate_fst θ h t p
      · by_cases hlt : n < m + 1
        · rw [dialSatPoint_succ_of_lt θ h p t n hlt, gatedEffectivePoint_fst,
            dialSatGate_pos t h hnpos, gatedValueSum_one, collapseMatrix_sub_valueSum,
            Matrix.one_mulVec]
          exact ih hnpos
        · rw [dialSatPoint_succ_of_ge θ h p t n hlt]
          exact ih hnpos

/-- **Closed form (v-coordinate)**.  For every layer `n ≥ 1` the saturated recursion point's
second coordinate is the collapsed-prefix affine form used by the anchor level rows. -/
theorem dialSatPoint_snd {m k d : Nat} (θ : Params (m + 1) k d) (h : Fin k)
    (p : ProbePair d) (t : ℝ) (n : Nat) (hn1 : 1 ≤ n) :
    (dialSatPoint θ h p t n).2 =
      collapsePrefix θ n *ᵥ p.2
        + (collapsePrefix θ n - 1 - (1 - t) • valueMatrix θ 0 h) *ᵥ p.1 := by
  induction n with
  | zero => exact absurd hn1 (by omega)
  | succ n ih =>
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · subst hn0
        rw [dialSatPoint_one, gatedEffectivePoint_snd, gatedValueSum_satGate, collapsePrefix_one]
        have hmat : valueSum θ 0 - (1 - t) • valueMatrix θ 0 h
            = collapseMatrix θ 0 - 1 - (1 - t) • valueMatrix θ 0 h := by
          rw [collapseMatrix]; abel
        rw [hmat]
      · by_cases hlt : n < m + 1
        · have hVs : valueSum θ ⟨n, hlt⟩ = collapseMatrix θ ⟨n, hlt⟩ - 1 := by
            rw [collapseMatrix]; abel
          have hcoef : ∀ (S : Matrix (Fin d) (Fin d) ℝ),
              collapseMatrix θ ⟨n, hlt⟩ * (collapsePrefix θ n - 1 - S)
                + valueSum θ ⟨n, hlt⟩ * (1 + S)
              = collapseMatrix θ ⟨n, hlt⟩ * collapsePrefix θ n - 1 - S := by
            intro S
            rw [hVs]; noncomm_ring
          rw [dialSatPoint_succ_of_lt θ h p t n hlt, gatedEffectivePoint_snd,
            dialSatGate_pos t h hnpos, gatedValueSum_one, ih hnpos,
            dialSatPoint_fst θ h p t n hnpos, headDialW,
            collapsePrefix_succ_of_lt θ n hlt]
          simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec]
          rw [add_assoc, ← Matrix.add_mulVec, hcoef ((1 - t) • valueMatrix θ 0 h)]
        · rw [dialSatPoint_succ_of_ge θ h p t n hlt, collapsePrefix_succ_of_ge θ n hlt]
          exact ih hnpos

/-- **GAP3 (general margin identification)**.  For every deeper layer `laterLayer j` the
saturated-point slope equals the genericity deeper-level margin `signRegionLevelValue`.
This generalizes `matrixBilin_satPoint_eq_levelValue` from `j = 0` to all `j : Fin m`. -/
theorem matrixBilin_dialSatPoint_eq_levelValue {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (p : ProbePair d) (t : ℝ) (j : Fin m) (b : Fin k) :
    matrixBilin (attentionMatrix θ (laterLayer j) b)
      (dialSatPoint θ h p t (j.val + 1)).1
      (dialSatPoint θ h p t (j.val + 1)).2
    = signRegionLevelValue θ h j b ((p.1, p.2), t) := by
  rw [dialSatPoint_fst θ h p t (j.val + 1) (Nat.le_add_left 1 j.val),
    dialSatPoint_snd θ h p t (j.val + 1) (Nat.le_add_left 1 j.val),
    matrixBilin_add_right']
  simp only [signRegionLevelValue, anchorRowValue, anchorRowLevel, anchorRowGradient,
    anchorRowConstant]
  rw [adjoint_dotProduct, ← matrixBilin_eq_transpose_dotProduct]

/-- **GAP2 (general layer induction)**.  Along the `θ`-dial path, the layer-`n` actual probe
point converges to the saturated recursion point `dialSatPoint n`, for every `n ≤ m + 1`.

The proof is by induction on `n`, coupling GAP1 (path convergence) at the base with the
per-layer gate saturation: at layer `0` the gates track `satGate` (dial head via (iii),
the others via (iv)); at every deeper layer the gates saturate to `1` because their slope
converges to the (positive) saturated-point slope.  Deeper positivity is supplied by
`hpos` (later discharged from the genericity `level_positive` margins via the general
margin identity). -/
theorem tendsto_dialActualProbePoint (r : Nat) {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (p : ProbePair d) (t : ℝ)
    (ht_pos : 0 < t) (ht_lt_one : t < 1)
    (hq : firstHeadSlope (attentionMatrix θ 0) h p = 0)
    (hpi : firstHeadPi (attentionMatrix θ 0) h p ≠ 0)
    (hsep : ∀ a : Fin k, a ≠ h → 0 < matrixBilin (attentionMatrix θ 0 a) p.1 p.2)
    (hpos : ∀ (n : Nat), 1 ≤ n → (hn : n < m + 1) → ∀ a : Fin k,
      0 < matrixBilin (attentionMatrix θ ⟨n, hn⟩ a)
        (dialSatPoint θ h p t n).1 (dialSatPoint θ h p t n).2)
    (n : Nat) (hn : n ≤ m + 1) :
    Tendsto (fun τ => actualProbePoint r θ
        (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
        (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2 n hn τ)
      atTop (𝓝 (dialSatPoint θ h p t n)) := by
  revert hn
  induction n with
  | zero =>
      intro hn
      simp only [actualProbePoint_zero, dialSatPoint_zero]
      exact tendsto_headDialPath (attentionMatrix θ 0) h (logScale r) p t
  | succ n ih =>
      intro hn
      have hlt : n < m + 1 := Nat.lt_of_succ_le hn
      have hIH := ih (Nat.le_of_succ_le hn)
      have hgate : Tendsto (fun τ => layerGates r θ ⟨n, hlt⟩
          (actualProbePoint r θ
            (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
            (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2 n
            (Nat.le_of_succ_le hn) τ).1
          (actualProbePoint r θ
            (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).1
            (headDialPath (attentionMatrix θ 0) h (logScale r) p t τ).2 n
            (Nat.le_of_succ_le hn) τ).2 τ)
          atTop (𝓝 (dialSatGate t h n)) := by
        rcases Nat.eq_zero_or_pos n with hn0 | hnpos
        · subst hn0
          have h0 : (⟨0, hlt⟩ : Fin (m + 1)) = 0 := by apply Fin.ext; simp
          rw [dialSatGate_zero]
          have hz := tendsto_dialLayerGates_zero r θ h p t ht_pos ht_lt_one hq hpi hsep
          refine hz.congr (fun τ => ?_)
          simp only [actualProbePoint_zero, h0]
        · rw [dialSatGate_pos t h hnpos, tendsto_pi_nhds]
          intro a
          have hcontB : Continuous (fun q : ProbePair d =>
              matrixBilin (attentionMatrix θ ⟨n, hlt⟩ a) q.1 q.2) :=
            continuous_matrixBilin _ continuous_fst continuous_snd
          have hslope := (hcontB.tendsto (dialSatPoint θ h p t n)).comp hIH
          have hΛpos := hpos n hnpos hlt a
          have heng := (expCloseTo_sig_of_tendsto_pos (b := logScale r) hΛpos hslope).tendsto
          refine heng.congr (fun τ => ?_)
          simp only [Function.comp_apply, layerGates, headGate]
      have hcont := continuous_gatedEffectivePoint θ ⟨n, hlt⟩
      have hcomp := (hcont.tendsto (dialSatGate t h n, dialSatPoint θ h p t n)).comp
        (hgate.prodMk_nhds hIH)
      rw [dialSatPoint_succ_of_lt θ h p t n hlt]
      refine hcomp.congr (fun τ => ?_)
      simp only [Function.comp_apply]
      rw [actualProbePoint_succ]

/-- **Discharge of `DeeperSlopeMargins`**.  For a `SignRegionData θ h`, the deeper-slope
margins hold over the pinned singleton base: each layer-`≥ 2` dialed slope converges to the
positive genericity level margin `signRegionLevelValue`.  The saturated-point positivity
input (`hpos`) is itself supplied by the general margin identity together with
`SignRegionData.level_positive`. -/
theorem deeperSlopeMargins_of_signRegionData (r : Nat) {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (D : SignRegionData θ h) :
    DeeperSlopeMargins r θ h (logScale r) {D.center.point} := by
  intro level hlevel hlv a x hx
  rw [Set.mem_singleton_iff] at hx
  have hxr : x ∈ D.region := hx ▸ D.center_mem_region
  have S := signRegionData_signRegionInterface D
  have hq : firstHeadSlope (attentionMatrix θ 0) h x.1 = 0 := S.point_on_quadric x hxr
  have hpi : firstHeadPi (attentionMatrix θ 0) h x.1 ≠ 0 := S.pi_ne_zero x hxr
  have ht_pos : 0 < x.2 := S.t_pos x hxr
  have ht_lt_one : x.2 < 1 := S.t_lt_one x hxr
  have hsep : ∀ a' : Fin k, a' ≠ h →
      0 < matrixBilin (attentionMatrix θ 0 a') x.1.1 x.1.2 := by
    intro a' ha'
    have hpp := D.separation_positive x hxr ⟨a', ha'⟩
    rwa [signRegionSeparationValue_eq_matrixBilin] at hpp
  have hpos : ∀ (nn : Nat), 1 ≤ nn → (hnn : nn < m + 1) → ∀ (aa : Fin k),
      0 < matrixBilin (attentionMatrix θ ⟨nn, hnn⟩ aa)
        (dialSatPoint θ h x.1 x.2 nn).1 (dialSatPoint θ h x.1 x.2 nn).2 := by
    intro nn hnn1 hnn aa
    obtain ⟨q, rfl⟩ : ∃ q, nn = q + 1 := ⟨nn - 1, by omega⟩
    have hjm : q < m := Nat.lt_of_succ_lt_succ hnn
    have hlayereq : (⟨q + 1, hnn⟩ : Fin (m + 1)) = laterLayer ⟨q, hjm⟩ := by
      apply Fin.ext; simp [laterLayer]
    rw [hlayereq, matrixBilin_dialSatPoint_eq_levelValue]
    exact D.level_positive x hxr ⟨q, hjm⟩ aa
  obtain ⟨lev, rfl⟩ : ∃ lev, level = lev + 1 := ⟨level - 1, by omega⟩
  refine ⟨matrixBilin (attentionMatrix θ ⟨lev + 1, hlv⟩ a)
      (dialSatPoint θ h x.1 x.2 (lev + 1)).1 (dialSatPoint θ h x.1 x.2 (lev + 1)).2,
    hpos (lev + 1) (by omega) hlv a, ?_⟩
  have hpt := tendsto_dialActualProbePoint r θ h x.1 x.2 ht_pos ht_lt_one hq hpi hsep hpos
    (lev + 1) (Nat.le_of_lt hlv)
  have hcontB : Continuous (fun z : ProbePair d =>
      matrixBilin (attentionMatrix θ ⟨lev + 1, hlv⟩ a) z.1 z.2) :=
    continuous_matrixBilin _ continuous_fst continuous_snd
  have hcomp := (hcontB.tendsto _).comp hpt
  refine hcomp.congr (fun τ => ?_)
  simp only [Function.comp_apply, actualProbeSlope]


/-! ## Full `HeadDialStatement` assembly -/

/-- **Full assembly**.  From a `SignRegionData θ h` alone we build a full
`HeadDialStatement` for the layer-0 attention/value matrices, with gates
`actualProbeGate ∘ headDialPath` and dial shift `b = logScale r`.  The deeper-slope margins
are discharged internally by `deeperSlopeMargins_of_signRegionData` (the general layer
induction GAP2 + margin identity GAP3), so the witness depends only on `SignRegionData`.

Provenance of the fields:
* (i) `exact_dial_identity` — `headDial_exact_identity`;
* (iii) `dial_gate_tracks` — `headDial_gate_tracks` (with `unprimed = primed`);
* (iv) `nondial_first_gates_saturate` — proved honestly from `separation_positive`;
* (v) `primed_deeper_gates_saturate` — the `eventuallyExpClose` engine over the genericity
  `level_positive` margins, using the discharged `DeeperSlopeMargins` for layers `ℓ ≥ 2`. -/
noncomputable def headDialStatement_of_signRegionData (r : Nat) {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (D : SignRegionData θ h) :
    HeadDialStatement (attentionMatrix θ 0) (valueMatrix θ 0) h (logScale r)
      D.region {D.center.point}
      (dialGateAlong r θ h (logScale r)) (dialGateAlong r θ h (logScale r)) := by
  have hDeep : DeeperSlopeMargins r θ h (logScale r) {D.center.point} :=
    deeperSlopeMargins_of_signRegionData r θ h D
  have S : SignRegionInterface (attentionMatrix θ 0) (valueMatrix θ 0) h D.region :=
    signRegionData_signRegionInterface D
  refine
    { interface := S
      compact_base := isCompact_singleton
      nonempty_base := Set.singleton_nonempty _
      base_subset := Set.singleton_subset_iff.mpr D.center_mem_region
      constants :=
        { cMax := 0, piMin := 1, rho := 1, threshold := 1, coeff := 0
          cMax_nonneg := le_refl 0, piMin_pos := one_pos, rho_pos := one_pos
          threshold_ge_one := le_refl 1, coeff_nonneg := le_refl 0 }
      exact_dial_identity := ?_
      dial_gate_tracks := ?_
      nondial_first_gates_saturate := ?_
      primed_deeper_gates_saturate := ?_ }
  · -- (i) exact dial identity
    intro x hx τ hτ
    have hxr : x ∈ D.region := (Set.singleton_subset_iff.mpr D.center_mem_region) hx
    have hq : firstHeadSlope (attentionMatrix θ 0) h x.1 = 0 := S.point_on_quadric x hxr
    have hpi : firstHeadPi (attentionMatrix θ 0) h x.1 ≠ 0 := S.pi_ne_zero x hxr
    have hid := headDial_exact_identity (attentionMatrix θ 0) h (logScale r) x.2 x.1 hq hpi hτ
    rw [hid]
    simp only [headDialC]
    ring
  · -- (iii) dial gate tracks
    intro x hx
    have hxr : x ∈ D.region := (Set.singleton_subset_iff.mpr D.center_mem_region) hx
    refine ⟨?_, fun _ => rfl⟩
    have halg := headDial_gate_tracks (attentionMatrix θ 0) h (logScale r) x.2 x.1
      (S.t_pos x hxr) (S.t_lt_one x hxr) (S.point_on_quadric x hxr) (S.pi_ne_zero x hxr)
    exact algCloseTo_congr (fun τ => dialGateAlong_zero_eq r θ h h (logScale r) x τ) halg
  · -- (iv) nondial first-layer gates saturate
    intro a ha x hx
    have hxr : x ∈ D.region := (Set.singleton_subset_iff.mpr D.center_mem_region) hx
    have hpos : 0 < matrixBilin (attentionMatrix θ 0 a) x.1.1 x.1.2 := by
      have := D.separation_positive x hxr ⟨a, ha⟩
      rwa [signRegionSeparationValue_eq_matrixBilin] at this
    have hsat : ExpCloseTo (fun τ => dialGateAlong r θ h (logScale r) 0 a x τ) 1 :=
      expCloseTo_dialGateAlong_zero_of_pos r θ h a (logScale r) x hpos
    exact ⟨hsat, hsat⟩
  · -- (v) deeper primed gates saturate
    intro level hlevel a x hx
    have hxr : x ∈ D.region := (Set.singleton_subset_iff.mpr D.center_mem_region) hx
    rcases Nat.lt_or_ge level 2 with hlt2 | hge2
    · -- level = 1: fully honest from genericity (GAP2 base + GAP3 `j = 0`)
      have hlev1 : level = 1 := by omega
      subst hlev1
      by_cases hm : 0 < m
      · exact expCloseTo_dialGateAlong_one_of_signRegionData r θ h D a x hxr hm
      · have hout : ¬ (1 < m + 1) := by omega
        have hconst : ∀ τ, dialGateAlong r θ h (logScale r) 1 a x τ = 1 := by
          intro τ; simp only [dialGateAlong]; rw [dif_neg hout]
        exact expCloseTo_congr hconst (expCloseTo_const 1)
    · -- level ≥ 2: from the deeper-slope margins (GAP2 induction, ℓ ≥ 2, remaining)
      exact expCloseTo_dialGateAlong_deeper r θ h (logScale r) {D.center.point}
        hDeep level hge2 a x hx

end TransformerIdentifiability.NLayer.KHead
