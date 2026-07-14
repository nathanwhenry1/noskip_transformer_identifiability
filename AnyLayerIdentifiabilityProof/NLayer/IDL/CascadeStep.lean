import AnyLayerIdentifiabilityProof.NLayer.IDL.CascadeSaturation
import AnyLayerIdentifiabilityProof.NLayer.IDL.FrecConvergence

set_option autoImplicit false

open Filter Topology Matrix

namespace TransformerIdentifiability.NLayer

/-!
# One cascade step on the real recursion (`lem:cascade`(a), `Λ ≠ 0` branches)

`CascadeSaturation` proved the abstract slope saturation; `FrecConvergence` proved the
coupled `Frec` limit.  Here we connect them to the actual recursion: the running gate
`firstLayerGate r A (P τ) τ = sig(τ · matrixBilin A (P τ) + log r)` has slope
`matrixBilin A (P τ)`, which converges by continuity whenever the running point does.
When that limiting slope is nonzero the gate is `EventuallyExpClose` to the saturated
value `1[Λ>0]`.

The degenerate `Λ = 0` (`α`) branch is *not* here: it needs the curve-rigidity identity
`φ_ℓ(·,ς;·) ≡ 0`, which is supplied by the trichotomy, not by continuity alone.
-/

/-- The first-layer slope `matrixBilin A (P τ).1 (P τ).2` converges with the running
point (continuity of the bilinear form). -/
theorem tendsto_matrixBilin {d : Nat} (A : Matrix (Fin d) (Fin d) ℝ)
    (P : ℝ → ProbePoint d) (pt : ProbePoint d)
    (hP : Tendsto P atTop (𝓝 pt)) :
    Tendsto (fun τ => matrixBilin A (P τ).1 (P τ).2) atTop
      (𝓝 (matrixBilin A pt.1 pt.2)) := by
  have hbilin :
      Continuous (fun p : ProbePoint d => matrixBilin A p.1 p.2) := by
    have hcont :
        Continuous (fun p : ProbePoint d => p.1 ⬝ᵥ A.mulVec p.2) := by
      apply continuous_finset_sum
      intro i _
      exact ((continuous_apply i).comp continuous_fst).mul
        ((continuous_apply i).comp ((continuous_mulVec A).comp continuous_snd))
    simpa only [matrixBilin] using hcont
  exact (hbilin.tendsto pt).comp hP

/-- `lem:cascade`(a), positive branch on the real recursion: if the running point
converges to a point with positive first-layer slope, the running gate is exponentially
close to `1`. -/
noncomputable def eventuallyExpClose_firstLayerGate_of_tendsto_pos {d : Nat}
    (r : Nat) (A : Matrix (Fin d) (Fin d) ℝ)
    (P : ℝ → ProbePoint d) (pt : ProbePoint d)
    (hP : Tendsto P atTop (𝓝 pt)) (hΛ : 0 < matrixBilin A pt.1 pt.2) :
    EventuallyExpClose (fun τ => firstLayerGate r A (P τ).1 (P τ).2 τ) 1 :=
  eventuallyExpClose_sig_tau_mul_of_tendsto_pos hΛ (tendsto_matrixBilin A P pt hP)

/-- `lem:cascade`(a), negative branch on the real recursion: if the running point
converges to a point with negative first-layer slope, the running gate is exponentially
close to `0`. -/
noncomputable def eventuallyExpClose_firstLayerGate_of_tendsto_neg {d : Nat}
    (r : Nat) (A : Matrix (Fin d) (Fin d) ℝ)
    (P : ℝ → ProbePoint d) (pt : ProbePoint d)
    (hP : Tendsto P atTop (𝓝 pt)) (hΛ : matrixBilin A pt.1 pt.2 < 0) :
    EventuallyExpClose (fun τ => firstLayerGate r A (P τ).1 (P τ).2 τ) 0 :=
  eventuallyExpClose_sig_tau_mul_of_tendsto_neg hΛ (tendsto_matrixBilin A P pt hP)

/-- The running gate converges to the saturated value whenever the limiting slope is
nonzero (combined branches). -/
theorem tendsto_firstLayerGate_of_tendsto_ne {d : Nat}
    (r : Nat) (A : Matrix (Fin d) (Fin d) ℝ)
    (P : ℝ → ProbePoint d) (pt : ProbePoint d)
    (hP : Tendsto P atTop (𝓝 pt)) (hΛ : matrixBilin A pt.1 pt.2 ≠ 0) :
    Tendsto (fun τ => firstLayerGate r A (P τ).1 (P τ).2 τ) atTop
      (𝓝 (if 0 < matrixBilin A pt.1 pt.2 then 1 else 0)) := by
  rcases lt_or_gt_of_ne hΛ with hneg | hpos
  · rw [if_neg (by linarith)]
    exact (eventuallyExpClose_firstLayerGate_of_tendsto_neg r A P pt hP hneg).tendsto
  · rw [if_pos hpos]
    exact (eventuallyExpClose_firstLayerGate_of_tendsto_pos r A P pt hP hpos).tendsto

end TransformerIdentifiability.NLayer
