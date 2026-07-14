import AnyLayerIdentifiabilityProof.NLayer.KHead.Core

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.KHead

/-!
# Multi-head probe recursion

This file contains the Lean API for the two-token probe recursion in
`tex_modular/sections/02-probe-recursion.tex`.

The central object is the closed recursion on probe points `(w, v)`, where
`w` is the difference between the repeated token and the last token and `v`
is the last token.  The actual two-token matrix constructor is also exposed
so later packets can connect the closed recursion back to the transformer
matrix semantics.
-/

/-- Vectors in the model dimension. -/
abbrev Vec (d : Nat) : Type := Fin d → ℝ

/-- A two-token probe point `(w, v)`, with repeated token `w + v` and last token `v`. -/
abbrev ProbePoint (d : Nat) : Type := Vec d × Vec d

/-- The bilinear slope `wᵀ A v`. -/
noncomputable def matrixBilin {d : Nat} (A : Matrix (Fin d) (Fin d) ℝ)
    (w v : Vec d) : ℝ :=
  w ⬝ᵥ A *ᵥ v

@[simp] theorem matrixBilin_apply {d : Nat} (A : Matrix (Fin d) (Fin d) ℝ)
    (w v : Vec d) :
    matrixBilin A w v = w ⬝ᵥ A *ᵥ v :=
  rfl

/-- Linearity of the left input of the bilinear form. -/
theorem matrixBilin_add_left {d : Nat} (A : Matrix (Fin d) (Fin d) ℝ)
    (w v x : Vec d) :
    matrixBilin A (w + v) x = matrixBilin A w x + matrixBilin A v x := by
  simp [matrixBilin, dotProduct, Finset.sum_add_distrib, add_mul]

/-- Scaling both inputs scales the bilinear form by the product of scalars. -/
theorem matrixBilin_smul_smul {d : Nat} (A : Matrix (Fin d) (Fin d) ℝ)
    (c : ℝ) (w v : Vec d) :
    matrixBilin A (c • w) (c • v) = c * c * matrixBilin A w v := by
  simp [matrixBilin, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
    mul_assoc]

/-- Column vector of the probe before the common scalar `sqrt τ` is applied. -/
def probeColumn {d : Nat} (r : Nat) (w v : Vec d) (j : Fin (r + 1)) : Vec d :=
  if j = Fin.last r then v else w + v

/-- The TeX probe matrix `X_{w,v}(τ) = sqrt(τ)[w+v,...,w+v,v]`. -/
noncomputable def probeMatrix {d : Nat} (r : Nat) (w v : Vec d) (τ : ℝ) :
    Matrix (Fin d) (Fin (r + 1)) ℝ :=
  fun i j => Real.sqrt τ * probeColumn r w v j i

@[simp] theorem probeColumn_last {d : Nat} (r : Nat) (w v : Vec d) :
    probeColumn r w v (Fin.last r) = v := by
  simp [probeColumn]

theorem probeColumn_of_ne {d : Nat} (r : Nat) (w v : Vec d)
    {j : Fin (r + 1)} (hj : j ≠ Fin.last r) :
    probeColumn r w v j = w + v := by
  simp [probeColumn, hj]

theorem probeColumn_of_lt {d : Nat} (r : Nat) (w v : Vec d)
    {j : Fin (r + 1)} (hj : (j : Nat) < r) :
    probeColumn r w v j = w + v := by
  apply probeColumn_of_ne
  intro h
  have : (j : Nat) = r := by
    simp [h]
  exact (Nat.ne_of_lt hj) this

@[simp] theorem probeMatrix_last {d : Nat} (r : Nat) (w v : Vec d) (τ : ℝ)
    (i : Fin d) :
    probeMatrix r w v τ i (Fin.last r) = Real.sqrt τ * v i := by
  simp [probeMatrix]

theorem probeMatrix_of_ne {d : Nat} (r : Nat) (w v : Vec d) (τ : ℝ)
    (i : Fin d) {j : Fin (r + 1)} (hj : j ≠ Fin.last r) :
    probeMatrix r w v τ i j = Real.sqrt τ * (w i + v i) := by
  simp [probeMatrix, probeColumn_of_ne r w v hj]

theorem probeMatrix_of_lt {d : Nat} (r : Nat) (w v : Vec d) (τ : ℝ)
    (i : Fin d) {j : Fin (r + 1)} (hj : (j : Nat) < r) :
    probeMatrix r w v τ i j = Real.sqrt τ * (w i + v i) := by
  exact probeMatrix_of_ne r w v τ i (by
    intro h
    have : (j : Nat) = r := by
      simp [h]
    exact (Nat.ne_of_lt hj) this)

/-- Every causal-softmax column sums to one. -/
theorem softmaxColC_sum_eq_one {T : Nat} (M : Matrix (Fin T) (Fin T) ℝ)
    (j : Fin T) :
    (∑ i : Fin T, softmaxColC M i j) = 1 := by
  classical
  let Z : ℝ := ∑ i' ∈ Finset.Iic j, Real.exp (M i' j)
  have hZpos : 0 < Z := by
    dsimp [Z]
    have hjmem : j ∈ Finset.Iic j := by simp
    exact Finset.sum_pos (fun _ _ => Real.exp_pos _) ⟨j, hjmem⟩
  have hZne : Z ≠ 0 := ne_of_gt hZpos
  calc
    (∑ i : Fin T, softmaxColC M i j)
        = ∑ i ∈ Finset.Iic j, Real.exp (M i j) / Z := by
          rw [← Finset.sum_subset (s₁ := Finset.Iic j) (s₂ := Finset.univ)
            (by intro x _; simp)]
          · apply Finset.sum_congr rfl
            intro i hi
            have hij : i ≤ j := by simpa using hi
            simp [softmaxColC, Z, hij]
          · intro x _ hxnot
            have hxle : ¬ x ≤ j := by simpa using hxnot
            simp [softmaxColC, hxle]
    _ = (∑ i ∈ Finset.Iic j, Real.exp (M i j)) / Z := by
          rw [Finset.sum_div]
    _ = Z / Z := by rfl
    _ = 1 := by exact div_self hZne

/-- On the final index, the causal prefix is the whole sequence. -/
theorem Finset_Iic_last {r : Nat} :
    Finset.Iic (Fin.last r) = (Finset.univ : Finset (Fin (r + 1))) := by
  ext i
  simp [Fin.le_last]

/-- Matrix product entry as the bilinear form of a row-column pair. -/
theorem transpose_mul_mul_apply {d T : Nat} (X : Matrix (Fin d) (Fin T) ℝ)
    (A : Matrix (Fin d) (Fin d) ℝ) (i j : Fin T) :
    ((Xᵀ * A * X) i j) = (fun p => X p i) ⬝ᵥ A *ᵥ (fun q => X q j) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_comm, mul_left_comm]
  simp [Finset.mul_sum]

/-- Scores induced by a probe matrix are `τ` times the unscaled bilinear probe scores. -/
theorem probeScore_eq {d r : Nat} (A : Matrix (Fin d) (Fin d) ℝ)
    (w v : Vec d) (τ : ℝ) (hτ : 0 ≤ τ) (i j : Fin (r + 1)) :
    ((probeMatrix r w v τ)ᵀ * A * probeMatrix r w v τ) i j =
      τ * matrixBilin A (probeColumn r w v i) (probeColumn r w v j) := by
  rw [transpose_mul_mul_apply]
  change matrixBilin A (Real.sqrt τ • probeColumn r w v i)
      (Real.sqrt τ • probeColumn r w v j) =
    τ * matrixBilin A (probeColumn r w v i) (probeColumn r w v j)
  rw [matrixBilin_smul_smul]
  rw [← sq]
  rw [Real.sq_sqrt hτ]

/-- The scalar gate `σ(τ wᵀAv + log r)` used by one head on a probe. -/
noncomputable def headGate {d : Nat} (r : Nat) (A : Matrix (Fin d) (Fin d) ℝ)
    (w v : Vec d) (τ : ℝ) : ℝ :=
  sig (τ * matrixBilin A w v + logScale r)

/-- Softmax normalization identity for the repeated-token mass. -/
theorem repeatedMass_eq_sig (r : Nat) (hr : 0 < r) (x y : ℝ) :
    (r : ℝ) * Real.exp x / ((r : ℝ) * Real.exp x + Real.exp y) =
      sig (x - y + logScale r) := by
  rw [sig, logScale]
  rw [Real.exp_neg, Real.exp_add, Real.exp_sub, Real.exp_log (by exact_mod_cast hr)]
  field_simp [Real.exp_ne_zero, show (r : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hr]

/-- The repeated-token mass in the final causal-softmax column is exactly `headGate`. -/
theorem headGate_eq_repeatedMass {d : Nat} (r : Nat) (hr : 0 < r)
    (A : Matrix (Fin d) (Fin d) ℝ) (w v : Vec d) (τ : ℝ) :
    (r : ℝ) * Real.exp (τ * matrixBilin A (w + v) v) /
        ((r : ℝ) * Real.exp (τ * matrixBilin A (w + v) v) +
          Real.exp (τ * matrixBilin A v v)) =
      headGate r A w v τ := by
  rw [repeatedMass_eq_sig r hr]
  rw [headGate]
  congr 2
  rw [matrixBilin_add_left]
  ring

/-- Per-head gates for one layer. -/
noncomputable def layerGates {L k d : Nat} (r : Nat) (θ : Params L k d)
    (l : Fin L) (w v : Vec d) (τ : ℝ) : Fin k → ℝ :=
  fun a => headGate r (attentionMatrix θ l a) w v τ

/-- Weighted sum `∑_a g_a V_{la}`. -/
noncomputable def gatedValueSum {L k d : Nat} (θ : Params L k d)
    (l : Fin L) (g : Fin k → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  ∑ a : Fin k, g a • valueMatrix θ l a

@[simp] theorem gatedValueSum_zero_heads {L d : Nat} (θ : Params L 0 d)
    (l : Fin L) (g : Fin 0 → ℝ) :
    gatedValueSum θ l g = 0 := by
  simp [gatedValueSum]

/-- Vector form of the weighted value sum. -/
theorem gatedValueSum_mulVec {L k d : Nat} (θ : Params L k d)
    (l : Fin L) (g : Fin k → ℝ) (w : Vec d) :
    gatedValueSum θ l g *ᵥ w =
      ∑ a : Fin k, g a • (valueMatrix θ l a *ᵥ w) := by
  simp [gatedValueSum, Matrix.sum_mulVec, Matrix.smul_mulVec]

/-- Vector action of the collapsed matrix. -/
theorem collapseMatrix_mulVec {L k d : Nat} (θ : Params L k d)
    (l : Fin L) (x : Vec d) :
    collapseMatrix θ l *ᵥ x = x + ∑ a : Fin k, valueMatrix θ l a *ᵥ x := by
  ext i
  simp [collapseMatrix, valueSum, Matrix.add_mulVec, Matrix.sum_mulVec,
    Matrix.one_mulVec]

/-- Multiplying a matrix by a column known to be a scalar multiple of `x`. -/
theorem matrix_mul_column_smul {d T : Nat}
    (V : Matrix (Fin d) (Fin d) ℝ) (Y : Matrix (Fin d) (Fin T) ℝ)
    (x : Vec d) (c : ℝ) (i : Fin d) (j : Fin T)
    (hy : ∀ p : Fin d, Y p j = c * x p) :
    (V * Y) i j = c * (V *ᵥ x) i := by
  rw [Matrix.mul_apply]
  simp only [hy, Matrix.mulVec, dotProduct]
  calc
    (∑ p : Fin d, V i p * (c * x p))
        = ∑ p : Fin d, c * (V i p * x p) := by
          apply Finset.sum_congr rfl
          intro p _
          ring
    _ = c * ∑ p : Fin d, V i p * x p := by
          rw [Finset.mul_sum]

/-- The repeated-block mass in the final probe softmax column. -/
theorem probeSoftmax_last_repeated_mass {d r : Nat} (hr : 0 < r)
    (A : Matrix (Fin d) (Fin d) ℝ) (w v : Vec d) (τ : ℝ) (hτ : 0 ≤ τ) :
    (∑ j ∈ (Finset.univ : Finset (Fin (r + 1))).erase (Fin.last r),
        softmaxColC ((probeMatrix r w v τ)ᵀ * A * probeMatrix r w v τ) j
          (Fin.last r)) =
      headGate r A w v τ := by
  classical
  let M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
    (probeMatrix r w v τ)ᵀ * A * probeMatrix r w v τ
  let β : ℝ := τ * matrixBilin A (w + v) v
  let δ : ℝ := τ * matrixBilin A v v
  have hden :
      (∑ i' ∈ Finset.Iic (Fin.last r), Real.exp (M i' (Fin.last r))) =
        (r : ℝ) * Real.exp β + Real.exp δ := by
    rw [Finset_Iic_last]
    rw [← Finset.sum_erase_add (s := (Finset.univ : Finset (Fin (r + 1))))
      (f := fun i => Real.exp (M i (Fin.last r)))
      (by simp : Fin.last r ∈ (Finset.univ : Finset (Fin (r + 1))))]
    congr 1
    · calc
        (∑ x ∈ (Finset.univ : Finset (Fin (r + 1))).erase (Fin.last r),
            Real.exp (M x (Fin.last r)))
            = ∑ _x ∈ (Finset.univ : Finset (Fin (r + 1))).erase (Fin.last r),
                Real.exp β := by
              apply Finset.sum_congr rfl
              intro x hx
              have hxne : x ≠ Fin.last r := Finset.ne_of_mem_erase hx
              have hcol : probeColumn r w v x = w + v := probeColumn_of_ne r w v hxne
              simp [M, β, probeScore_eq A w v τ hτ x (Fin.last r), hcol]
        _ = (r : ℝ) * Real.exp β := by
              rw [Finset.sum_const, nsmul_eq_mul]
              simp
    · simp [M, δ, probeScore_eq A w v τ hτ]
  calc
    (∑ j ∈ (Finset.univ : Finset (Fin (r + 1))).erase (Fin.last r),
        softmaxColC M j (Fin.last r))
        = ∑ _j ∈ (Finset.univ : Finset (Fin (r + 1))).erase (Fin.last r),
            Real.exp β / ((r : ℝ) * Real.exp β + Real.exp δ) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hjne : j ≠ Fin.last r := Finset.ne_of_mem_erase hj
          have hle : j ≤ Fin.last r := Fin.le_last j
          have hcol : probeColumn r w v j = w + v := probeColumn_of_ne r w v hjne
          simp [softmaxColC, M, hle, hden, β,
            probeScore_eq A w v τ hτ j (Fin.last r), hcol]
    _ = (r : ℝ) * (Real.exp β / ((r : ℝ) * Real.exp β + Real.exp δ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          simp
    _ = (r : ℝ) * Real.exp β / ((r : ℝ) * Real.exp β + Real.exp δ) := by ring
    _ = headGate r A w v τ := by
          dsimp only [β, δ]
          exact headGate_eq_repeatedMass r hr A w v τ

/-- A non-final probe column attends to the repeated probe vector. -/
theorem probeAttention_of_ne {d r : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (w v : Vec d) (τ : ℝ)
    (i : Fin d) {j : Fin (r + 1)} (hj : j ≠ Fin.last r) :
    (probeMatrix r w v τ *
        softmaxColC ((probeMatrix r w v τ)ᵀ * A * probeMatrix r w v τ)) i j =
      Real.sqrt τ * (w i + v i) := by
  classical
  let S : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
    softmaxColC ((probeMatrix r w v τ)ᵀ * A * probeMatrix r w v τ)
  have hsum : (∑ x : Fin (r + 1), S x j) = 1 := by
    dsimp only [S]
    exact softmaxColC_sum_eq_one _ _
  rw [Matrix.mul_apply]
  calc
    (∑ x : Fin (r + 1), probeMatrix r w v τ i x * S x j)
        = ∑ x : Fin (r + 1), (Real.sqrt τ * (w i + v i)) * S x j := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hxle : x ≤ j
          · have hxne : x ≠ Fin.last r := by
              intro hxlast
              have hlastle : Fin.last r ≤ j := by simpa [hxlast] using hxle
              exact hj (Fin.last_le_iff.mp hlastle)
            rw [probeMatrix_of_ne r w v τ i hxne]
          · have hzero : S x j = 0 := by
              dsimp only [S]
              simp [softmaxColC, hxle]
            rw [hzero]
            ring
    _ = (Real.sqrt τ * (w i + v i)) * (∑ x : Fin (r + 1), S x j) := by
          rw [Finset.mul_sum]
    _ = Real.sqrt τ * (w i + v i) := by rw [hsum, mul_one]

/-- The final probe column attends to `v + g w`, where `g` is the probe gate. -/
theorem probeAttention_last {d r : Nat} (hr : 0 < r)
    (A : Matrix (Fin d) (Fin d) ℝ) (w v : Vec d) (τ : ℝ) (hτ : 0 ≤ τ)
    (i : Fin d) :
    (probeMatrix r w v τ *
        softmaxColC ((probeMatrix r w v τ)ᵀ * A * probeMatrix r w v τ))
        i (Fin.last r) =
      Real.sqrt τ * (v i + headGate r A w v τ * w i) := by
  classical
  let S : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
    softmaxColC ((probeMatrix r w v τ)ᵀ * A * probeMatrix r w v τ)
  let g : ℝ := headGate r A w v τ
  have hmass :
      (∑ j ∈ (Finset.univ : Finset (Fin (r + 1))).erase (Fin.last r),
        S j (Fin.last r)) = g := by
    dsimp only [S, g]
    exact probeSoftmax_last_repeated_mass hr A w v τ hτ
  have hsum : (∑ j : Fin (r + 1), S j (Fin.last r)) = 1 := by
    dsimp only [S]
    exact softmaxColC_sum_eq_one _ _
  have hlast : S (Fin.last r) (Fin.last r) = 1 - g := by
    have hsplit := Finset.sum_erase_add
      (s := (Finset.univ : Finset (Fin (r + 1))))
      (f := fun j => S j (Fin.last r))
      (by simp : Fin.last r ∈ (Finset.univ : Finset (Fin (r + 1))))
    rw [hmass, hsum] at hsplit
    linarith
  rw [Matrix.mul_apply]
  rw [← Finset.sum_erase_add (s := (Finset.univ : Finset (Fin (r + 1))))
    (f := fun j => probeMatrix r w v τ i j * S j (Fin.last r))
    (by simp : Fin.last r ∈ (Finset.univ : Finset (Fin (r + 1))))]
  have hrepeated :
      (∑ x ∈ (Finset.univ : Finset (Fin (r + 1))).erase (Fin.last r),
          probeMatrix r w v τ i x * S x (Fin.last r)) =
        (Real.sqrt τ * (w i + v i)) * g := by
    calc
      (∑ x ∈ (Finset.univ : Finset (Fin (r + 1))).erase (Fin.last r),
          probeMatrix r w v τ i x * S x (Fin.last r))
          = ∑ x ∈ (Finset.univ : Finset (Fin (r + 1))).erase (Fin.last r),
              (Real.sqrt τ * (w i + v i)) * S x (Fin.last r) := by
            apply Finset.sum_congr rfl
            intro x hx
            have hxne : x ≠ Fin.last r := Finset.ne_of_mem_erase hx
            rw [probeMatrix_of_ne r w v τ i hxne]
      _ = (Real.sqrt τ * (w i + v i)) *
            (∑ x ∈ (Finset.univ : Finset (Fin (r + 1))).erase (Fin.last r),
              S x (Fin.last r)) := by
            rw [Finset.mul_sum]
      _ = (Real.sqrt τ * (w i + v i)) * g := by rw [hmass]
  rw [hrepeated, probeMatrix_last, hlast]
  ring

/-- One formal probe-recursion step with externally supplied gates. -/
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

/-- The second coordinate in the TeX summation form. -/
theorem gatedEffectivePoint_snd_sum {L k d : Nat} (θ : Params L k d)
    (l : Fin L) (g : Fin k → ℝ) (w v : Vec d) :
    (gatedEffectivePoint θ l g w v).2 =
      collapseMatrix θ l *ᵥ v +
        ∑ a : Fin k, g a • (valueMatrix θ l a *ᵥ w) := by
  simp [gatedValueSum_mulVec]

/-- The first coordinate in the TeX `w`-recursion form. -/
theorem gatedEffectivePoint_fst_sum {L k d : Nat} (θ : Params L k d)
    (l : Fin L) (g : Fin k → ℝ) (w v : Vec d) :
    (gatedEffectivePoint θ l g w v).1 =
      (collapseMatrix θ l - ∑ a : Fin k, g a • valueMatrix θ l a) *ᵥ w := by
  simp [gatedValueSum]

/-- The updated repeated token is `C_l (w + v)`. -/
theorem gatedEffectivePoint_repeated {L k d : Nat} (θ : Params L k d)
    (l : Fin L) (g : Fin k → ℝ) (w v : Vec d) :
    (gatedEffectivePoint θ l g w v).1 + (gatedEffectivePoint θ l g w v).2 =
      collapseMatrix θ l *ᵥ (w + v) := by
  ext i
  simp [gatedEffectivePoint, Matrix.sub_mulVec, Matrix.mulVec_add]

/-- One head sends non-final probe columns through the repeated-token average. -/
theorem headProbeAttention_of_ne {L k d r : Nat} (θ : Params L k d) (l : Fin L)
    (a : Fin k) (w v : Vec d) (τ : ℝ) (i : Fin d) {j : Fin (r + 1)}
    (hj : j ≠ Fin.last r) :
    (valueMatrix θ l a * probeMatrix r w v τ *
        softmaxColC ((probeMatrix r w v τ)ᵀ * attentionMatrix θ l a *
          probeMatrix r w v τ)) i j =
      Real.sqrt τ * (valueMatrix θ l a *ᵥ (w + v)) i := by
  rw [Matrix.mul_assoc]
  apply matrix_mul_column_smul
  intro p
  exact probeAttention_of_ne (attentionMatrix θ l a) w v τ p hj

/-- One head sends the final probe column through `v + g w`. -/
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

/-- The layer image of a non-final probe column is the collapsed repeated token. -/
theorem layer_probeMatrix_of_ne {L k d r : Nat} (θ : Params L k d) (l : Fin L)
    (w v : Vec d) (τ : ℝ) (i : Fin d) {j : Fin (r + 1)} (hj : j ≠ Fin.last r) :
    layer θ l (probeMatrix r w v τ) i j =
      Real.sqrt τ * (collapseMatrix θ l *ᵥ (w + v)) i := by
  rw [layer]
  simp only [Matrix.add_apply, Matrix.sum_apply]
  rw [probeMatrix_of_ne r w v τ i hj]
  calc
    Real.sqrt τ * (w i + v i) +
        (∑ a : Fin k,
          (valueMatrix θ l a * probeMatrix r w v τ *
            softmaxColC ((probeMatrix r w v τ)ᵀ * attentionMatrix θ l a *
              probeMatrix r w v τ)) i j)
        = Real.sqrt τ * (w i + v i) +
            ∑ a : Fin k, Real.sqrt τ * (valueMatrix θ l a *ᵥ (w + v)) i := by
          congr 1
          apply Finset.sum_congr rfl
          intro a _
          exact headProbeAttention_of_ne θ l a w v τ i hj
    _ = Real.sqrt τ * ((w i + v i) +
            ∑ a : Fin k, (valueMatrix θ l a *ᵥ (w + v)) i) := by
          rw [← Finset.mul_sum]
          ring
    _ = Real.sqrt τ * (collapseMatrix θ l *ᵥ (w + v)) i := by
          rw [collapseMatrix_mulVec]
          simp

/-- The layer image of the final probe column is the closed-recursion `v` update. -/
theorem layer_probeMatrix_last {L k d r : Nat} (hr : 0 < r) (θ : Params L k d)
    (l : Fin L) (w v : Vec d) (τ : ℝ) (hτ : 0 ≤ τ) (i : Fin d) :
    layer θ l (probeMatrix r w v τ) i (Fin.last r) =
      Real.sqrt τ *
        (collapseMatrix θ l *ᵥ v + gatedValueSum θ l (layerGates r θ l w v τ) *ᵥ w) i := by
  rw [layer]
  simp only [Matrix.add_apply, Matrix.sum_apply]
  rw [probeMatrix_last]
  calc
    Real.sqrt τ * v i +
        (∑ a : Fin k,
          (valueMatrix θ l a * probeMatrix r w v τ *
            softmaxColC ((probeMatrix r w v τ)ᵀ * attentionMatrix θ l a *
              probeMatrix r w v τ)) i (Fin.last r))
        = Real.sqrt τ * v i +
            ∑ a : Fin k,
              Real.sqrt τ *
                (valueMatrix θ l a *ᵥ (v + layerGates r θ l w v τ a • w)) i := by
          congr 1
          apply Finset.sum_congr rfl
          intro a _
          exact headProbeAttention_last hr θ l a w v τ hτ i
    _ = Real.sqrt τ * (v i +
            ∑ a : Fin k,
              (valueMatrix θ l a *ᵥ (v + layerGates r θ l w v τ a • w)) i) := by
          rw [← Finset.mul_sum]
          ring
    _ = Real.sqrt τ *
        (collapseMatrix θ l *ᵥ v + gatedValueSum θ l (layerGates r θ l w v τ) *ᵥ w) i := by
          congr 1
          rw [collapseMatrix_mulVec, gatedValueSum_mulVec]
          simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Params.valueMatrix_apply,
            Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          calc
            v i + ∑ x : Fin k,
                (((θ l x).1 *ᵥ v) i + layerGates r θ l w v τ x * ((θ l x).1 *ᵥ w) i)
                = v i + ((∑ x : Fin k, ((θ l x).1 *ᵥ v) i) +
                    ∑ x : Fin k, layerGates r θ l w v τ x * ((θ l x).1 *ᵥ w) i) := by
                  rw [Finset.sum_add_distrib]
            _ = v i + (∑ c : Fin k, ((θ l c).1 *ᵥ v) i) +
                ∑ x : Fin k, layerGates r θ l w v τ x * ((θ l x).1 *ᵥ w) i := by
                  ring

/-- A causal-softmax layer sends a probe matrix to the closed one-step probe update. -/
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
    have hrep := congr_fun (gatedEffectivePoint_repeated θ l
      (layerGates r θ l w v τ) w v) i
    rw [← hrep]
    simp

/-- One actual first-layer probe step, using the sigmoid gates from the layer. -/
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

theorem firstLayerEffectivePoint_snd_sum {m k d : Nat} (r : Nat)
    (θ : Params (m + 1) k d) (w v : Vec d) (τ : ℝ) :
    (firstLayerEffectivePoint r θ w v τ).2 =
      collapseMatrix θ 0 *ᵥ v +
        ∑ a : Fin k,
          layerGates r θ 0 w v τ a • (valueMatrix θ 0 a *ᵥ w) := by
  rw [firstLayerEffectivePoint_snd, gatedValueSum_mulVec]

/-- Closed multi-head probe recursion through all layers. -/
noncomputable def probeRecursionPoint (r : Nat) {k d : Nat} :
    {L : Nat} → Params L k d → Vec d → Vec d → ℝ → ProbePoint d
  | 0, _, w, v, _ => (w, v)
  | _ + 1, θ, w, v, τ =>
      let pt := firstLayerEffectivePoint r θ w v τ
      probeRecursionPoint r (Fin.tail θ) pt.1 pt.2 τ

/-- Last-column output of the closed probe recursion. -/
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

/-- The first causal-softmax layer realizes the first closed probe-recursion step. -/
theorem firstLayer_probeMatrix {r L k d : Nat} (hr : 0 < r)
    (θ : Params (L + 1) k d) (w v : Vec d) (τ : ℝ) (hτ : 0 ≤ τ) :
    layer θ 0 (probeMatrix r w v τ) =
      probeMatrix r (firstLayerEffectivePoint r θ w v τ).1
        (firstLayerEffectivePoint r θ w v τ).2 τ := by
  simpa [firstLayerEffectivePoint] using
    layer_probeMatrix hr θ 0 w v τ hτ

/-- Full causal-softmax/probe-matrix semantics for the closed probe recursion. -/
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

/-- The final transformer column is `sqrt τ` times the closed-recursion output. -/
theorem transformer_probeMatrix_last {r L k d : Nat} (hr : 0 < r)
    (θ : Params L k d) (w v : Vec d) (τ : ℝ) (hτ : 0 ≤ τ) (i : Fin d) :
    transformer θ (probeMatrix r w v τ) i (Fin.last r) =
      Real.sqrt τ * probeOutput r θ w v τ i := by
  rw [transformer_probeMatrix r hr τ hτ θ w v]
  simp [probeOutput, probeMatrix]

/-- TeX final-column normalization:
`τ^{-1/2} [transformer θ (probeMatrix r w v τ)]_{:,T} = probeOutput`. -/
theorem probeOutput_eq_inv_sqrt_transformer_last {r L k d : Nat} (hr : 0 < r)
    (θ : Params L k d) (w v : Vec d) (τ : ℝ) (hτ : 0 < τ) :
    (fun i : Fin d =>
        (Real.sqrt τ)⁻¹ * transformer θ (probeMatrix r w v τ) i (Fin.last r)) =
      probeOutput r θ w v τ := by
  ext i
  rw [transformer_probeMatrix_last hr θ w v τ (le_of_lt hτ) i]
  field_simp [ne_of_gt (Real.sqrt_pos_of_pos hτ)]

/-- `K02.E.prop-probe-recursion.S/P`: closed recursive form of the multi-head probe. -/
theorem prop_probe_recursion {r L k d : Nat} (θ : Params (L + 1) k d)
    (w v : Vec d) (τ : ℝ) :
    probeOutput r θ w v τ =
      probeOutput r (Fin.tail θ)
        ((collapseMatrix θ 0 - gatedValueSum θ 0 (layerGates r θ 0 w v τ)) *ᵥ w)
        (collapseMatrix θ 0 *ᵥ v +
          gatedValueSum θ 0 (layerGates r θ 0 w v τ) *ᵥ w) τ := by
  rfl

/-- `K02.E.lem-peeling.S/P`: peeling off the first probe-recursion layer. -/
theorem peeling_identity {r L k d : Nat} (θ : Params (L + 1) k d)
    (w v : Vec d) (τ : ℝ) :
    probeOutput r θ w v τ =
      probeOutput r (Fin.tail θ)
        (firstLayerEffectivePoint r θ w v τ).1
        (firstLayerEffectivePoint r θ w v τ).2 τ :=
  rfl

end TransformerIdentifiability.NLayer.KHead
