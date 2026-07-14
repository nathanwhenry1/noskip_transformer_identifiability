import AnyLayerIdentifiabilityProof.NLayer.IDL.DescentIDL

set_option autoImplicit false

open Filter Topology Matrix

namespace TransformerIdentifiability.NLayer

/-!
# Coupled `Frec` convergence from per-layer gate saturation

`prop:matching` Step 1 needs: along a dial path whose deeper gates saturate, the closed
recursion `Frec` converges to an explicit telescoped limit vector.  Gate convergence and
running-point convergence are coupled through `Frec_succ`, so we induct on the tail depth.

The input is, level by level, that the first sigmoid gate of the running recursion
converges; the output is convergence of `Frec` to a recursively-defined limit
`frecLimit`.  Both the hypothesis (`GateLimits`) and the limit (`frecLimit`) follow the
same peeling recursion, so the inductive step lines up definitionally.
-/

/-- The once-peeled effective path: peel the first layer of `θ` along `P`. -/
noncomputable def effectivePath {m d : Nat} (r : Nat) (θ : Params (m + 1) d)
    (P : ℝ → ProbePoint d) : ℝ → ProbePoint d :=
  fun τ => paramsFirstLayerEffectivePoint r θ (P τ).1 (P τ).2 τ

/-- The limiting effective point obtained by dialing the base limit `pt` with the gate
limit `ς`. -/
noncomputable def effLimitPoint {d : Nat} (V : Matrix (Fin d) (Fin d) ℝ) (ς : ℝ)
    (pt : ProbePoint d) : ProbePoint d :=
  firstLayerDialPoint V ς pt.1 pt.2

/-- Recursive per-level gate-convergence hypothesis: at each peeled layer the first
sigmoid gate of the running recursion converges to `ς` of that level, with the limit
point advancing through `effLimitPoint`. -/
def GateLimits {d : Nat} (r : Nat) :
    {m : Nat} → Params m d → (ℝ → ProbePoint d) → (Nat → ℝ) → ProbePoint d → Prop
  | 0, _, _, _, _ => True
  | _ + 1, θ, P, ς, pt =>
      Tendsto (fun τ => firstLayerGate r (Params.headAttention θ) (P τ).1 (P τ).2 τ)
          atTop (𝓝 (ς 0)) ∧
        GateLimits r (Params.tail θ) (effectivePath r θ P)
          (fun n => ς (n + 1)) (effLimitPoint (Params.headValue θ) (ς 0) pt)

/-- The recursively-defined limit vector of `Frec` along a saturating path. -/
noncomputable def frecLimit {d : Nat} (r : Nat) :
    {m : Nat} → Params m d → (Nat → ℝ) → ProbePoint d → (Fin d → ℝ)
  | 0, _, _, pt => pt.2
  | _ + 1, θ, ς, pt =>
      frecLimit r (Params.tail θ) (fun n => ς (n + 1))
        (effLimitPoint (Params.headValue θ) (ς 0) pt)

/-- `Matrix.mulVec V` is continuous (finite-dimensional linear map). -/
theorem continuous_mulVec {d : Nat} (V : Matrix (Fin d) (Fin d) ℝ) :
    Continuous (fun x : Fin d → ℝ => V.mulVec x) := by
  simpa [Matrix.mulVecLin_apply] using
    (Matrix.mulVecLin V).continuous_of_finiteDimensional

/-- The effective path converges to the limiting effective point, given gate and base
convergence. -/
theorem tendsto_effectivePath {m d : Nat} (r : Nat) (θ : Params (m + 1) d)
    (P : ℝ → ProbePoint d) (ς0 : ℝ) (pt : ProbePoint d)
    (hP : Tendsto P atTop (𝓝 pt))
    (hgate :
      Tendsto (fun τ => firstLayerGate r (Params.headAttention θ) (P τ).1 (P τ).2 τ)
        atTop (𝓝 ς0)) :
    Tendsto (effectivePath r θ P) atTop
      (𝓝 (effLimitPoint (Params.headValue θ) ς0 pt)) := by
  have hP1 : Tendsto (fun τ => (P τ).1) atTop (𝓝 pt.1) :=
    (continuous_fst.tendsto pt).comp hP
  have hP2 : Tendsto (fun τ => (P τ).2) atTop (𝓝 pt.2) :=
    (continuous_snd.tendsto pt).comp hP
  set V := Params.headValue θ with hV
  have hcont := continuous_mulVec V
  have hmv1 : Tendsto (fun τ => V.mulVec (P τ).1) atTop (𝓝 (V.mulVec pt.1)) :=
    (hcont.tendsto pt.1).comp hP1
  have hmv2 : Tendsto (fun τ => V.mulVec (P τ).2) atTop (𝓝 (V.mulVec pt.2)) :=
    (hcont.tendsto pt.2).comp hP2
  have hsmul :
      Tendsto
        (fun τ =>
          firstLayerGate r (Params.headAttention θ) (P τ).1 (P τ).2 τ • V.mulVec (P τ).1)
        atTop (𝓝 (ς0 • V.mulVec pt.1)) :=
    hgate.smul hmv1
  have h1 := (hP1.add hmv1).sub hsmul
  have h2 := (hP2.add hmv2).add hsmul
  have hpair := h1.prodMk_nhds h2
  -- both sides are definitionally the dial map of the running point
  simpa only [effectivePath, effLimitPoint, paramsFirstLayerEffectivePoint,
    firstLayerEffectivePoint, firstLayerDialPoint, firstLayerGate, hV] using hpair

/-- **`prop:matching` Step 1 convergence.**  If, along `P → pt`, the running gates
saturate (`GateLimits`), then `Frec` converges to the telescoped limit `frecLimit`. -/
theorem frec_tendsto_of_gateLimits {d : Nat} (r : Nat) :
    ∀ {m : Nat} (θ : Params m d) (P : ℝ → ProbePoint d) (ς : Nat → ℝ)
      (pt : ProbePoint d),
      Tendsto P atTop (𝓝 pt) → GateLimits r θ P ς pt →
      Tendsto (fun τ => Frec r θ (P τ).1 (P τ).2 τ) atTop (𝓝 (frecLimit r θ ς pt)) := by
  intro m
  induction m with
  | zero =>
    intro θ P ς pt hP _
    have hsnd : Tendsto (fun τ => (P τ).2) atTop (𝓝 pt.2) :=
      (continuous_snd.tendsto pt).comp hP
    simpa [Frec, frecLimit] using hsnd
  | succ m ih =>
    intro θ P ς pt hP hgl
    obtain ⟨hgate, hrest⟩ := hgl
    have heff :
        Tendsto (effectivePath r θ P) atTop
          (𝓝 (effLimitPoint (Params.headValue θ) (ς 0) pt)) :=
      tendsto_effectivePath r θ P (ς 0) pt hP hgate
    have hrec :=
      ih (Params.tail θ) (effectivePath r θ P) (fun n => ς (n + 1))
        (effLimitPoint (Params.headValue θ) (ς 0) pt) heff hrest
    have hrw :
        (fun τ => Frec r θ (P τ).1 (P τ).2 τ)
          = fun τ =>
              Frec r (Params.tail θ) (effectivePath r θ P τ).1
                (effectivePath r θ P τ).2 τ := by
      funext τ
      exact Frec_succ_paramsFirstLayerEffectivePoint r θ (P τ).1 (P τ).2 τ
    rw [hrw]
    exact hrec

end TransformerIdentifiability.NLayer
