import AnyLayerIdentifiabilityProof.NLayer.KHead.Probe
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Core

set_option autoImplicit false

open Matrix

namespace TransformerIdentifiability.NLayer.NoSkip

/-!
# Two-token probe primitives

The vector, bilinear-form, and probe-matrix API is independent of whether the
transformer has skip connections, so this file re-exports the corresponding
`KHead` declarations.  The normalized last-column observable is defined here
because it uses the no-skip realization map.
-/

/-- Vectors in the model dimension. -/
abbrev Vec (d : Nat) : Type := KHead.Vec d

/-- A probe point `(w, v)`, with repeated token `w + v` and last token `v`. -/
abbrev ProbePoint (d : Nat) : Type := KHead.ProbePoint d

/-- The bilinear slope `wᵀ A v`. -/
noncomputable abbrev matrixBilin {d : Nat} (A : Matrix (Fin d) (Fin d) ℝ)
    (w v : Vec d) : ℝ :=
  KHead.matrixBilin A w v

@[simp] theorem matrixBilin_apply {d : Nat} (A : Matrix (Fin d) (Fin d) ℝ)
    (w v : Vec d) :
    matrixBilin A w v = w ⬝ᵥ A *ᵥ v :=
  KHead.matrixBilin_apply A w v

/-- Linearity of the left input of the probe bilinear form. -/
theorem matrixBilin_add_left {d : Nat} (A : Matrix (Fin d) (Fin d) ℝ)
    (w v x : Vec d) :
    matrixBilin A (w + v) x = matrixBilin A w x + matrixBilin A v x :=
  KHead.matrixBilin_add_left A w v x

/-- Scaling both inputs scales the bilinear form by the product of the scalars. -/
theorem matrixBilin_smul_smul {d : Nat} (A : Matrix (Fin d) (Fin d) ℝ)
    (c : ℝ) (w v : Vec d) :
    matrixBilin A (c • w) (c • v) = c * c * matrixBilin A w v :=
  KHead.matrixBilin_smul_smul A c w v

/-- Column vector of the probe before the common scalar `sqrt τ` is applied. -/
abbrev probeColumn {d : Nat} (r : Nat) (w v : Vec d) (j : Fin (seqLength r)) : Vec d :=
  KHead.probeColumn r w v j

/-- The TeX probe matrix `X_{w,v}(τ) = sqrt(τ)[w+v,...,w+v,v]`. -/
noncomputable abbrev probeMatrix {d : Nat} (r : Nat) (w v : Vec d) (τ : ℝ) :
    Matrix (Fin d) (Fin (seqLength r)) ℝ :=
  KHead.probeMatrix r w v τ

@[simp] theorem probeColumn_last {d : Nat} (r : Nat) (w v : Vec d) :
    probeColumn r w v (Fin.last r) = v :=
  KHead.probeColumn_last r w v

theorem probeColumn_of_ne {d : Nat} (r : Nat) (w v : Vec d)
    {j : Fin (seqLength r)} (hj : j ≠ Fin.last r) :
    probeColumn r w v j = w + v :=
  KHead.probeColumn_of_ne r w v hj

theorem probeColumn_of_lt {d : Nat} (r : Nat) (w v : Vec d)
    {j : Fin (seqLength r)} (hj : (j : Nat) < r) :
    probeColumn r w v j = w + v :=
  KHead.probeColumn_of_lt r w v hj

@[simp] theorem probeMatrix_last {d : Nat} (r : Nat) (w v : Vec d) (τ : ℝ)
    (i : Fin d) :
    probeMatrix r w v τ i (Fin.last r) = Real.sqrt τ * v i :=
  KHead.probeMatrix_last r w v τ i

theorem probeMatrix_of_ne {d : Nat} (r : Nat) (w v : Vec d) (τ : ℝ)
    (i : Fin d) {j : Fin (seqLength r)} (hj : j ≠ Fin.last r) :
    probeMatrix r w v τ i j = Real.sqrt τ * (w i + v i) :=
  KHead.probeMatrix_of_ne r w v τ i hj

theorem probeMatrix_of_lt {d : Nat} (r : Nat) (w v : Vec d) (τ : ℝ)
    (i : Fin d) {j : Fin (seqLength r)} (hj : (j : Nat) < r) :
    probeMatrix r w v τ i j = Real.sqrt τ * (w i + v i) :=
  KHead.probeMatrix_of_lt r w v τ i hj

/-- Every causal-softmax column sums to one. -/
theorem softmaxColC_sum_eq_one {T : Nat} (M : Matrix (Fin T) (Fin T) ℝ)
    (j : Fin T) :
    (∑ i : Fin T, softmaxColC M i j) = 1 :=
  KHead.softmaxColC_sum_eq_one M j

/-- On the final index, the causal prefix is the whole sequence. -/
theorem Finset_Iic_last {r : Nat} :
    Finset.Iic (Fin.last r) = (Finset.univ : Finset (Fin (seqLength r))) :=
  KHead.Finset_Iic_last

/-- Matrix product entry as the bilinear form of a row-column pair. -/
theorem transpose_mul_mul_apply {d T : Nat} (X : Matrix (Fin d) (Fin T) ℝ)
    (A : Matrix (Fin d) (Fin d) ℝ) (i j : Fin T) :
    ((Xᵀ * A * X) i j) = (fun p ↦ X p i) ⬝ᵥ A *ᵥ (fun q ↦ X q j) :=
  KHead.transpose_mul_mul_apply X A i j

/-- Probe scores are `τ` times the unscaled bilinear probe scores. -/
theorem probeScore_eq {d r : Nat} (A : Matrix (Fin d) (Fin d) ℝ)
    (w v : Vec d) (τ : ℝ) (hτ : 0 ≤ τ) (i j : Fin (seqLength r)) :
    ((probeMatrix r w v τ)ᵀ * A * probeMatrix r w v τ) i j =
      τ * matrixBilin A (probeColumn r w v i) (probeColumn r w v j) :=
  KHead.probeScore_eq A w v τ hτ i j

/-- The scalar gate `σ(τ wᵀAv + log r)` of one head on a probe. -/
noncomputable abbrev headGate {d : Nat} (r : Nat) (A : Matrix (Fin d) (Fin d) ℝ)
    (w v : Vec d) (τ : ℝ) : ℝ :=
  KHead.headGate r A w v τ

/-- Softmax normalization identity for the repeated-token mass. -/
theorem repeatedMass_eq_sig (r : Nat) (hr : 0 < r) (x y : ℝ) :
    (r : ℝ) * Real.exp x / ((r : ℝ) * Real.exp x + Real.exp y) =
      sig (x - y + logScale r) :=
  KHead.repeatedMass_eq_sig r hr x y

/-- The repeated-token mass formula written as the probe gate. -/
theorem headGate_eq_repeatedMass {d : Nat} (r : Nat) (hr : 0 < r)
    (A : Matrix (Fin d) (Fin d) ℝ) (w v : Vec d) (τ : ℝ) :
    (r : ℝ) * Real.exp (τ * matrixBilin A (w + v) v) /
        ((r : ℝ) * Real.exp (τ * matrixBilin A (w + v) v) +
          Real.exp (τ * matrixBilin A v v)) =
      headGate r A w v τ :=
  KHead.headGate_eq_repeatedMass r hr A w v τ

/-- The repeated-block mass in the final probe softmax column. -/
theorem probeSoftmax_last_repeated_mass {d r : Nat} (hr : 0 < r)
    (A : Matrix (Fin d) (Fin d) ℝ) (w v : Vec d) (τ : ℝ) (hτ : 0 ≤ τ) :
    (∑ j ∈ (Finset.univ : Finset (Fin (seqLength r))).erase (Fin.last r),
        softmaxColC ((probeMatrix r w v τ)ᵀ * A * probeMatrix r w v τ) j
          (Fin.last r)) =
      headGate r A w v τ :=
  KHead.probeSoftmax_last_repeated_mass hr A w v τ hτ

/-- A non-final probe column attends to the repeated probe vector. -/
theorem probeAttention_of_ne {d r : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (w v : Vec d) (τ : ℝ)
    (i : Fin d) {j : Fin (seqLength r)} (hj : j ≠ Fin.last r) :
    (probeMatrix r w v τ *
        softmaxColC ((probeMatrix r w v τ)ᵀ * A * probeMatrix r w v τ)) i j =
      Real.sqrt τ * (w i + v i) :=
  KHead.probeAttention_of_ne A w v τ i hj

/-- The final probe column attends to `v + g w`, with `g` the sigmoid gate. -/
theorem probeAttention_last {d r : Nat} (hr : 0 < r)
    (A : Matrix (Fin d) (Fin d) ℝ) (w v : Vec d) (τ : ℝ) (hτ : 0 ≤ τ)
    (i : Fin d) :
    (probeMatrix r w v τ *
        softmaxColC ((probeMatrix r w v τ)ᵀ * A * probeMatrix r w v τ))
        i (Fin.last r) =
      Real.sqrt τ * (v i + headGate r A w v τ * w i) :=
  KHead.probeAttention_last hr A w v τ hτ i

/-- Per-head sigmoid gates for one layer on a probe point. -/
noncomputable abbrev layerGates {L k d : Nat} (r : Nat) (θ : Params L k d)
    (l : Fin L) (w v : Vec d) (τ : ℝ) : Fin k → ℝ :=
  fun a ↦ headGate r (attentionMatrix θ l a) w v τ

/-- The gated value sum `D = ∑_a g_a V_{la}`. -/
noncomputable abbrev gatedValueSum {L k d : Nat} (θ : Params L k d)
    (l : Fin L) (g : Fin k → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  KHead.gatedValueSum θ l g

@[simp] theorem gatedValueSum_zero_heads {L d : Nat} (θ : Params L 0 d)
    (l : Fin L) (g : Fin 0 → ℝ) :
    gatedValueSum θ l g = 0 :=
  KHead.gatedValueSum_zero_heads θ l g

/-- Vector form of the gated value sum. -/
theorem gatedValueSum_mulVec {L k d : Nat} (θ : Params L k d)
    (l : Fin L) (g : Fin k → ℝ) (w : Vec d) :
    gatedValueSum θ l g *ᵥ w =
      ∑ a : Fin k, g a • (valueMatrix θ l a *ᵥ w) :=
  KHead.gatedValueSum_mulVec θ l g w

/-- In the no-skip model, `C_l x = ∑_a V_{la} x`. -/
theorem collapseMatrix_mulVec {L k d : Nat} (θ : Params L k d)
    (l : Fin L) (x : Vec d) :
    collapseMatrix θ l *ᵥ x = ∑ a : Fin k, valueMatrix θ l a *ᵥ x := by
  ext i
  simp [collapseMatrix, valueSum, Matrix.sum_mulVec]

/-- Multiplying a matrix by a column known to be a scalar multiple of `x`. -/
theorem matrix_mul_column_smul {d T : Nat}
    (V : Matrix (Fin d) (Fin d) ℝ) (Y : Matrix (Fin d) (Fin T) ℝ)
    (x : Vec d) (c : ℝ) (i : Fin d) (j : Fin T)
    (hy : ∀ p : Fin d, Y p j = c * x p) :
    (V * Y) i j = c * (V *ᵥ x) i :=
  KHead.matrix_mul_column_smul V Y x c i j hy

/-- One no-skip probe-recursion step with externally supplied gates. -/
noncomputable def gatedEffectivePoint {L k d : Nat} (θ : Params L k d)
    (l : Fin L) (g : Fin k → ℝ) (w v : Vec d) : ProbePoint d :=
  let D := gatedValueSum θ l g
  ((collapseMatrix θ l - D) *ᵥ w, collapseMatrix θ l *ᵥ v + D *ᵥ w)

@[simp] theorem gatedEffectivePoint_fst {L k d : Nat} (θ : Params L k d)
    (l : Fin L) (g : Fin k → ℝ) (w v : Vec d) :
    (gatedEffectivePoint θ l g w v).1 =
      (collapseMatrix θ l - gatedValueSum θ l g) *ᵥ w := by
  simp [gatedEffectivePoint]

@[simp] theorem gatedEffectivePoint_snd {L k d : Nat} (θ : Params L k d)
    (l : Fin L) (g : Fin k → ℝ) (w v : Vec d) :
    (gatedEffectivePoint θ l g w v).2 =
      collapseMatrix θ l *ᵥ v + gatedValueSum θ l g *ᵥ w := by
  simp [gatedEffectivePoint]

/-- The no-skip last-token update in the TeX summation form. -/
theorem gatedEffectivePoint_snd_sum {L k d : Nat} (θ : Params L k d)
    (l : Fin L) (g : Fin k → ℝ) (w v : Vec d) :
    (gatedEffectivePoint θ l g w v).2 =
      collapseMatrix θ l *ᵥ v +
        ∑ a : Fin k, g a • (valueMatrix θ l a *ᵥ w) := by
  simp [gatedValueSum_mulVec]

/-- The no-skip difference-stream update in matrix form. -/
theorem gatedEffectivePoint_fst_sum {L k d : Nat} (θ : Params L k d)
    (l : Fin L) (g : Fin k → ℝ) (w v : Vec d) :
    (gatedEffectivePoint θ l g w v).1 =
      (collapseMatrix θ l - ∑ a : Fin k, g a • valueMatrix θ l a) *ᵥ w := by
  simp [KHead.gatedValueSum]

/-- The annihilation form `w' = ∑_a (1-g_a)V_{la}w` of the no-skip update. -/
theorem gatedEffectivePoint_fst_compl_sum {L k d : Nat} (θ : Params L k d)
    (l : Fin L) (g : Fin k → ℝ) (w v : Vec d) :
    (gatedEffectivePoint θ l g w v).1 =
      ∑ a : Fin k, (1 - g a) • (valueMatrix θ l a *ᵥ w) := by
  ext i
  simp [gatedEffectivePoint, collapseMatrix, valueSum, KHead.gatedValueSum,
    Matrix.sub_mulVec, Matrix.sum_mulVec, Matrix.smul_mulVec]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _ha
  ring

/-- The updated repeated token is `u' = C_l (w + v)`. -/
theorem gatedEffectivePoint_repeated {L k d : Nat} (θ : Params L k d)
    (l : Fin L) (g : Fin k → ℝ) (w v : Vec d) :
    (gatedEffectivePoint θ l g w v).1 + (gatedEffectivePoint θ l g w v).2 =
      collapseMatrix θ l *ᵥ (w + v) := by
  ext i
  simp [gatedEffectivePoint, Matrix.sub_mulVec, Matrix.mulVec_add]

/-- Freezing every gate at zero makes the gated value sum vanish. -/
@[simp] theorem gatedValueSum_allZero {L k d : Nat} (θ : Params L k d)
    (l : Fin L) :
    gatedValueSum θ l (fun _ ↦ 0) = 0 := by
  simp [KHead.gatedValueSum]

/-- Freezing every gate at one makes the gated value sum equal `C_l`. -/
@[simp] theorem gatedValueSum_allOne {L k d : Nat} (θ : Params L k d)
    (l : Fin L) :
    gatedValueSum θ l (fun _ ↦ 1) = collapseMatrix θ l := by
  simp [KHead.gatedValueSum, collapseMatrix, valueSum]

/-- With all gates zero, the contrast stream is transported by `C_l`. -/
@[simp] theorem gatedEffectivePoint_allZero_fst {L k d : Nat} (θ : Params L k d)
    (l : Fin L) (w v : Vec d) :
    (gatedEffectivePoint θ l (fun _ ↦ 0) w v).1 = collapseMatrix θ l *ᵥ w := by
  simp [gatedEffectivePoint]

/-- With all gates zero, the last-token stream is transported by `C_l`. -/
@[simp] theorem gatedEffectivePoint_allZero_snd {L k d : Nat} (θ : Params L k d)
    (l : Fin L) (w v : Vec d) :
    (gatedEffectivePoint θ l (fun _ ↦ 0) w v).2 = collapseMatrix θ l *ᵥ v := by
  simp [gatedEffectivePoint]

/-- The paired all-zero freeze transports both streams by `C_l`. -/
theorem gatedEffectivePoint_allZero {L k d : Nat} (θ : Params L k d)
    (l : Fin L) (w v : Vec d) :
    gatedEffectivePoint θ l (fun _ ↦ 0) w v =
      (collapseMatrix θ l *ᵥ w, collapseMatrix θ l *ᵥ v) := by
  ext <;> simp

/-- With all gates one, a no-skip layer annihilates the contrast stream. -/
@[simp] theorem gatedEffectivePoint_allOne_fst {L k d : Nat} (θ : Params L k d)
    (l : Fin L) (w v : Vec d) :
    (gatedEffectivePoint θ l (fun _ ↦ 1) w v).1 = 0 := by
  simp [gatedEffectivePoint]

/-- After all-one saturation, only the repeated token `C_l (w+v)` remains. -/
@[simp] theorem gatedEffectivePoint_allOne_snd {L k d : Nat} (θ : Params L k d)
    (l : Fin L) (w v : Vec d) :
    (gatedEffectivePoint θ l (fun _ ↦ 1) w v).2 =
      collapseMatrix θ l *ᵥ (w + v) := by
  rw [gatedEffectivePoint_snd, gatedValueSum_allOne, Matrix.mulVec_add]
  exact add_comm _ _

/-- The paired all-one freeze records no-skip saturation annihilation. -/
theorem gatedEffectivePoint_allOne {L k d : Nat} (θ : Params L k d)
    (l : Fin L) (w v : Vec d) :
    gatedEffectivePoint θ l (fun _ ↦ 1) w v =
      (0, collapseMatrix θ l *ᵥ (w + v)) := by
  apply Prod.ext
  · exact gatedEffectivePoint_allOne_fst θ l w v
  · exact gatedEffectivePoint_allOne_snd θ l w v

/-- One head sends non-final probe columns through the repeated-token average. -/
theorem headProbeAttention_of_ne {L k d r : Nat} (θ : Params L k d) (l : Fin L)
    (a : Fin k) (w v : Vec d) (τ : ℝ) (i : Fin d) {j : Fin (seqLength r)}
    (hj : j ≠ Fin.last r) :
    (valueMatrix θ l a * probeMatrix r w v τ *
        softmaxColC ((probeMatrix r w v τ)ᵀ * attentionMatrix θ l a *
          probeMatrix r w v τ)) i j =
      Real.sqrt τ * (valueMatrix θ l a *ᵥ (w + v)) i := by
  rw [Matrix.mul_assoc]
  apply matrix_mul_column_smul
  intro p
  exact probeAttention_of_ne (attentionMatrix θ l a) w v τ p hj

/-- One head sends the final probe column through `v + g_a w`. -/
theorem headProbeAttention_last {L k d r : Nat} (hr : 0 < r) (θ : Params L k d)
    (l : Fin L) (a : Fin k) (w v : Vec d) (τ : ℝ) (hτ : 0 ≤ τ) (i : Fin d) :
    (valueMatrix θ l a * probeMatrix r w v τ *
        softmaxColC ((probeMatrix r w v τ)ᵀ * attentionMatrix θ l a *
          probeMatrix r w v τ)) i (Fin.last r) =
      Real.sqrt τ *
        (valueMatrix θ l a *ᵥ (v + layerGates r θ l w v τ a • w)) i := by
  rw [Matrix.mul_assoc]
  apply matrix_mul_column_smul
  intro p
  simpa [layerGates, smul_eq_mul] using
    probeAttention_last hr (attentionMatrix θ l a) w v τ hτ p

/-- A non-final column of a no-skip layer is the updated repeated token. -/
theorem layer_probeMatrix_of_ne {L k d r : Nat} (θ : Params L k d) (l : Fin L)
    (w v : Vec d) (τ : ℝ) (i : Fin d) {j : Fin (seqLength r)}
    (hj : j ≠ Fin.last r) :
    layer θ l (probeMatrix r w v τ) i j =
      Real.sqrt τ * (collapseMatrix θ l *ᵥ (w + v)) i := by
  rw [layer]
  simp only [Matrix.sum_apply]
  calc
    (∑ a : Fin k,
        (valueMatrix θ l a * probeMatrix r w v τ *
          softmaxColC ((probeMatrix r w v τ)ᵀ * attentionMatrix θ l a *
            probeMatrix r w v τ)) i j)
        = ∑ a : Fin k, Real.sqrt τ * (valueMatrix θ l a *ᵥ (w + v)) i := by
          apply Finset.sum_congr rfl
          intro a _ha
          exact headProbeAttention_of_ne θ l a w v τ i hj
    _ = Real.sqrt τ * ∑ a : Fin k, (valueMatrix θ l a *ᵥ (w + v)) i := by
          rw [Finset.mul_sum]
    _ = Real.sqrt τ * (collapseMatrix θ l *ᵥ (w + v)) i := by
          rw [collapseMatrix_mulVec]
          simp

/-- The final column of a no-skip layer is the closed-recursion `v` update. -/
theorem layer_probeMatrix_last {L k d r : Nat} (hr : 0 < r) (θ : Params L k d)
    (l : Fin L) (w v : Vec d) (τ : ℝ) (hτ : 0 ≤ τ) (i : Fin d) :
    layer θ l (probeMatrix r w v τ) i (Fin.last r) =
      Real.sqrt τ *
        (collapseMatrix θ l *ᵥ v + gatedValueSum θ l (layerGates r θ l w v τ) *ᵥ w) i := by
  rw [layer]
  simp only [Matrix.sum_apply]
  calc
    (∑ a : Fin k,
        (valueMatrix θ l a * probeMatrix r w v τ *
          softmaxColC ((probeMatrix r w v τ)ᵀ * attentionMatrix θ l a *
            probeMatrix r w v τ)) i (Fin.last r))
        = ∑ a : Fin k, Real.sqrt τ *
            (valueMatrix θ l a *ᵥ (v + layerGates r θ l w v τ a • w)) i := by
          apply Finset.sum_congr rfl
          intro a _ha
          exact headProbeAttention_last hr θ l a w v τ hτ i
    _ = Real.sqrt τ * ∑ a : Fin k,
          (valueMatrix θ l a *ᵥ (v + layerGates r θ l w v τ a • w)) i := by
          rw [Finset.mul_sum]
    _ = Real.sqrt τ *
        (collapseMatrix θ l *ᵥ v + gatedValueSum θ l (layerGates r θ l w v τ) *ᵥ w) i := by
          congr 1
          rw [collapseMatrix_mulVec, gatedValueSum_mulVec]
          simp [Matrix.mulVec_add, Matrix.mulVec_smul, Finset.sum_add_distrib]

/-- A no-skip causal-softmax layer realizes the one-step probe update. -/
theorem layer_probeMatrix {L k d r : Nat} (hr : 0 < r) (θ : Params L k d)
    (l : Fin L) (w v : Vec d) (τ : ℝ) (hτ : 0 ≤ τ) :
    layer θ l (probeMatrix r w v τ) =
      probeMatrix r (gatedEffectivePoint θ l (layerGates r θ l w v τ) w v).1
        (gatedEffectivePoint θ l (layerGates r θ l w v τ) w v).2 τ := by
  ext i j
  by_cases hj : j = Fin.last r
  · subst j
    rw [layer_probeMatrix_last hr θ l w v τ hτ i]
    simp [probeMatrix, gatedEffectivePoint]
  · rw [layer_probeMatrix_of_ne θ l w v τ i hj]
    rw [probeMatrix_of_ne r _ _ τ i hj]
    have hrep := congr_fun
      (gatedEffectivePoint_repeated θ l (layerGates r θ l w v τ) w v) i
    rw [← hrep]
    simp

/-- The normalized last-column observable
`Fθ(w,v,τ) = τ⁻¹⁄² [transformer θ (X_{w,v}(τ))]_{:,T}`.

This is defined directly from the no-skip realization map; later probe-recursion
results identify it with the recursively computed final `v` stream for `τ > 0`.
-/
noncomputable def probeObservable (r : Nat) {L k d : Nat} (theta : Params L k d)
    (w v : Vec d) (τ : ℝ) : Vec d :=
  fun i ↦
    (Real.sqrt τ)⁻¹ * transformer theta (probeMatrix r w v τ) i (Fin.last r)

@[simp] theorem probeObservable_apply (r : Nat) {L k d : Nat} (theta : Params L k d)
    (w v : Vec d) (τ : ℝ) (i : Fin d) :
    probeObservable r theta w v τ i =
      (Real.sqrt τ)⁻¹ * transformer theta (probeMatrix r w v τ) i (Fin.last r) :=
  rfl

/-- The actual first-layer effective point, with gates computed from the input probe. -/
noncomputable def firstLayerEffectivePoint {m k d : Nat} (r : Nat)
    (θ : Params (m + 1) k d) (w v : Vec d) (τ : ℝ) : ProbePoint d :=
  gatedEffectivePoint θ 0 (layerGates r θ 0 w v τ) w v

@[simp] theorem firstLayerEffectivePoint_fst {m k d : Nat} (r : Nat)
    (θ : Params (m + 1) k d) (w v : Vec d) (τ : ℝ) :
    (firstLayerEffectivePoint r θ w v τ).1 =
      (collapseMatrix θ 0 - gatedValueSum θ 0 (layerGates r θ 0 w v τ)) *ᵥ w := by
  simp [firstLayerEffectivePoint]

@[simp] theorem firstLayerEffectivePoint_snd {m k d : Nat} (r : Nat)
    (θ : Params (m + 1) k d) (w v : Vec d) (τ : ℝ) :
    (firstLayerEffectivePoint r θ w v τ).2 =
      collapseMatrix θ 0 *ᵥ v +
        gatedValueSum θ 0 (layerGates r θ 0 w v τ) *ᵥ w := by
  simp [firstLayerEffectivePoint]

/-- First-layer last-token update in the headwise TeX summation form. -/
theorem firstLayerEffectivePoint_snd_sum {m k d : Nat} (r : Nat)
    (θ : Params (m + 1) k d) (w v : Vec d) (τ : ℝ) :
    (firstLayerEffectivePoint r θ w v τ).2 =
      collapseMatrix θ 0 *ᵥ v +
        ∑ a : Fin k,
          layerGates r θ 0 w v τ a • (valueMatrix θ 0 a *ᵥ w) := by
  rw [firstLayerEffectivePoint_snd, gatedValueSum_mulVec]

/-- First-layer difference update in the no-skip annihilation form. -/
theorem firstLayerEffectivePoint_fst_compl_sum {m k d : Nat} (r : Nat)
    (θ : Params (m + 1) k d) (w v : Vec d) (τ : ℝ) :
    (firstLayerEffectivePoint r θ w v τ).1 =
      ∑ a : Fin k, (1 - layerGates r θ 0 w v τ a) •
        (valueMatrix θ 0 a *ᵥ w) := by
  exact gatedEffectivePoint_fst_compl_sum θ 0 (layerGates r θ 0 w v τ) w v

/-- Closed no-skip probe recursion through every layer. -/
noncomputable def probeRecursionPoint (r : Nat) {k d : Nat} :
    {L : Nat} → Params L k d → Vec d → Vec d → ℝ → ProbePoint d
  | 0, _, w, v, _ => (w, v)
  | _ + 1, θ, w, v, τ =>
      let pt := firstLayerEffectivePoint r θ w v τ
      probeRecursionPoint r (Fin.tail θ) pt.1 pt.2 τ

/-- The recursively computed final last-token stream `v_L`. -/
noncomputable def probeOutput (r : Nat) {L k d : Nat} (θ : Params L k d)
    (w v : Vec d) (τ : ℝ) : Vec d :=
  (probeRecursionPoint r θ w v τ).2

@[simp] theorem probeRecursionPoint_zero {r k d : Nat} (θ : Params 0 k d)
    (w v : Vec d) (τ : ℝ) :
    probeRecursionPoint r θ w v τ = (w, v) :=
  rfl

@[simp] theorem probeOutput_zero {r k d : Nat} (θ : Params 0 k d)
    (w v : Vec d) (τ : ℝ) :
    probeOutput r θ w v τ = v :=
  rfl

@[simp] theorem probeRecursionPoint_succ {r L k d : Nat}
    (θ : Params (L + 1) k d) (w v : Vec d) (τ : ℝ) :
    probeRecursionPoint r θ w v τ =
      probeRecursionPoint r (Fin.tail θ)
        (firstLayerEffectivePoint r θ w v τ).1
        (firstLayerEffectivePoint r θ w v τ).2 τ :=
  rfl

/-- The first concrete no-skip layer realizes the first recursive probe step. -/
theorem firstLayer_probeMatrix {r L k d : Nat} (hr : 0 < r)
    (θ : Params (L + 1) k d) (w v : Vec d) (τ : ℝ) (hτ : 0 ≤ τ) :
    layer θ 0 (probeMatrix r w v τ) =
      probeMatrix r (firstLayerEffectivePoint r θ w v τ).1
        (firstLayerEffectivePoint r θ w v τ).2 τ := by
  simpa [firstLayerEffectivePoint] using
    layer_probeMatrix hr θ 0 w v τ hτ

/-- Depth-inductive semantics of the no-skip probe recursion. -/
theorem transformer_probeMatrix (r : Nat) {k d : Nat} (hr : 0 < r)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    {L : Nat} → (θ : Params L k d) → (w v : Vec d) →
      transformer θ (probeMatrix r w v τ) =
        probeMatrix r (probeRecursionPoint r θ w v τ).1
          (probeRecursionPoint r θ w v τ).2 τ
  | 0, _, _, _ => by
      simp [probeRecursionPoint]
  | _ + 1, θ, w, v => by
      rw [transformer_succ]
      rw [firstLayer_probeMatrix hr θ w v τ hτ]
      exact transformer_probeMatrix r hr τ hτ (Fin.tail θ)
        (firstLayerEffectivePoint r θ w v τ).1
        (firstLayerEffectivePoint r θ w v τ).2

/-- The final transformer column is `sqrt τ` times the recursive `v_L`. -/
theorem transformer_probeMatrix_last {r L k d : Nat} (hr : 0 < r)
    (θ : Params L k d) (w v : Vec d) (τ : ℝ) (hτ : 0 ≤ τ) (i : Fin d) :
    transformer θ (probeMatrix r w v τ) i (Fin.last r) =
      Real.sqrt τ * probeOutput r θ w v τ i := by
  rw [transformer_probeMatrix r hr τ hτ θ w v]
  simp [probeOutput, probeMatrix]

/-- TeX final-column normalization, stated without the observable abbreviation. -/
theorem probeOutput_eq_inv_sqrt_transformer_last {r L k d : Nat} (hr : 0 < r)
    (θ : Params L k d) (w v : Vec d) (τ : ℝ) (hτ : 0 < τ) :
    (fun i : Fin d ↦
        (Real.sqrt τ)⁻¹ * transformer θ (probeMatrix r w v τ) i (Fin.last r)) =
      probeOutput r θ w v τ := by
  ext i
  rw [transformer_probeMatrix_last hr θ w v τ (le_of_lt hτ) i]
  field_simp [ne_of_gt (Real.sqrt_pos_of_pos hτ)]

/-- For positive scale, the normalized last-column observable is exactly `v_L`. -/
theorem probeObservable_eq_probeOutput {r L k d : Nat} (hr : 0 < r)
    (θ : Params L k d) (w v : Vec d) (τ : ℝ) (hτ : 0 < τ) :
    probeObservable r θ w v τ = probeOutput r θ w v τ := by
  exact probeOutput_eq_inv_sqrt_transformer_last hr θ w v τ hτ

/-- `prop:probe-recursion`: the no-skip depth recursion in first-layer form. -/
theorem prop_probe_recursion {r L k d : Nat} (θ : Params (L + 1) k d)
    (w v : Vec d) (τ : ℝ) :
    probeOutput r θ w v τ =
      probeOutput r (Fin.tail θ)
        ((collapseMatrix θ 0 - gatedValueSum θ 0 (layerGates r θ 0 w v τ)) *ᵥ w)
        (collapseMatrix θ 0 *ᵥ v +
          gatedValueSum θ 0 (layerGates r θ 0 w v τ) *ᵥ w) τ := by
  rfl

/-- The exact transformed probe `(ẃ, ṽ)` obtained after peeling layer zero. -/
noncomputable def firstLayerTransformedProbe {L k d : Nat} (r : Nat)
    (θ : Params (L + 1) k d) (w v : Vec d) (τ : ℝ) : ProbePoint d :=
  let D := gatedValueSum θ 0 (layerGates r θ 0 w v τ)
  ((collapseMatrix θ 0 - D) *ᵥ w, collapseMatrix θ 0 *ᵥ v + D *ᵥ w)

@[simp] theorem firstLayerTransformedProbe_fst {L k d : Nat} (r : Nat)
    (θ : Params (L + 1) k d) (w v : Vec d) (τ : ℝ) :
    (firstLayerTransformedProbe r θ w v τ).1 =
      (collapseMatrix θ 0 - gatedValueSum θ 0 (layerGates r θ 0 w v τ)) *ᵥ w := by
  simp [firstLayerTransformedProbe]

@[simp] theorem firstLayerTransformedProbe_snd {L k d : Nat} (r : Nat)
    (θ : Params (L + 1) k d) (w v : Vec d) (τ : ℝ) :
    (firstLayerTransformedProbe r θ w v τ).2 =
      collapseMatrix θ 0 *ᵥ v +
        gatedValueSum θ 0 (layerGates r θ 0 w v τ) *ᵥ w := by
  simp [firstLayerTransformedProbe]

/-- The explicit peeling point agrees with the effective point used by the recursion. -/
theorem firstLayerTransformedProbe_eq_effectivePoint {L k d : Nat} (r : Nat)
    (θ : Params (L + 1) k d) (w v : Vec d) (τ : ℝ) :
    firstLayerTransformedProbe r θ w v τ = firstLayerEffectivePoint r θ w v τ := by
  rfl

/-- Peeling identity for the recursively computed final stream. -/
theorem peeling_identity {r L k d : Nat} (θ : Params (L + 1) k d)
    (w v : Vec d) (τ : ℝ) :
    probeOutput r θ w v τ =
      probeOutput r (Fin.tail θ)
        (firstLayerTransformedProbe r θ w v τ).1
        (firstLayerTransformedProbe r θ w v τ).2 τ := by
  rfl

/-- An empty transformer tail returns the last token of its probe. -/
theorem probeObservable_zero {r k d : Nat} (hr : 0 < r) (θ : Params 0 k d)
    (w v : Vec d) (τ : ℝ) (hτ : 0 < τ) :
    probeObservable r θ w v τ = v := by
  rw [probeObservable_eq_probeOutput hr θ w v τ hτ]
  exact probeOutput_zero θ w v τ

/-- Peeling identity for the normalized last-column transformer observable. -/
theorem probeObservable_peeling_identity {r L k d : Nat} (hr : 0 < r)
    (θ : Params (L + 1) k d) (w v : Vec d) (τ : ℝ) (hτ : 0 < τ) :
    probeObservable r θ w v τ =
      probeObservable r (Fin.tail θ)
        (firstLayerTransformedProbe r θ w v τ).1
        (firstLayerTransformedProbe r θ w v τ).2 τ := by
  rw [probeObservable_eq_probeOutput hr θ w v τ hτ]
  rw [probeObservable_eq_probeOutput hr (Fin.tail θ)
    (firstLayerTransformedProbe r θ w v τ).1
    (firstLayerTransformedProbe r θ w v τ).2 τ hτ]
  exact peeling_identity θ w v τ

/-- At depth one, peeling leaves the empty tail, so the output is exactly `ṽ`. -/
theorem probeObservable_peeling_identity_depth_one {r k d : Nat} (hr : 0 < r)
    (θ : Params 1 k d) (w v : Vec d) (τ : ℝ) (hτ : 0 < τ) :
    probeObservable r θ w v τ = (firstLayerTransformedProbe r θ w v τ).2 := by
  rw [probeObservable_peeling_identity hr θ w v τ hτ]
  exact probeObservable_zero hr (Fin.tail θ)
    (firstLayerTransformedProbe r θ w v τ).1
    (firstLayerTransformedProbe r θ w v τ).2 τ hτ

end TransformerIdentifiability.NLayer.NoSkip
