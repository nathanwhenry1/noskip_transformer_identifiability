import AnyLayerIdentifiabilityProof.NLayer.Foundations.Core

set_option autoImplicit false

open Matrix

namespace TransformerIdentifiability.NLayer

/-!
# Probe recursion, slope polynomials, and path observables

Target contents:
* probe input and two-type recursion
* `probe_reduction`
* `peeling`
* formal stream polynomials `W_j`, `T_j`
* slope polynomials `phi`
* slope identity
* path classes and observables

Corresponds to `n_layer_proof.tex`, Section 2.3-2.5.
-/

/-! ## Sigmoid algebra -/

theorem one_add_exp_pos (x : ℝ) : 0 < 1 + Real.exp (-x) := by positivity

theorem one_add_exp_ne_zero (x : ℝ) : 1 + Real.exp (-x) ≠ 0 := (one_add_exp_pos x).ne'

/-- The sigmoid is the reciprocal of its denominator: `sig x * (1 + e^{-x}) = 1`. -/
theorem sig_mul_denom (x : ℝ) : sig x * (1 + Real.exp (-x)) = 1 :=
  inv_mul_cancel₀ (one_add_exp_ne_zero x)

/-! ## Two-type inputs and the single-layer closure formula

A *two-type* input has `r` identical "context" columns `c • u` followed by a single
"query" column `c • v` (in the paper, `c = √τ`).  The key structural fact
(Proposition `prop:probe`, single-layer case) is that a causal attention layer maps
two-type inputs to two-type inputs, with
`u ↦ u + Vu` and `v ↦ v + Vv + σ(c²·(u-v)ᵀAv + log r) • V(u-v)`. -/

/-- A two-type input matrix: `r` context columns `c • u`, then one query column `c • v`. -/
noncomputable def twoType (r d : ℕ) (u v : Fin d → ℝ) (c : ℝ) :
    Matrix (Fin d) (Fin (r + 1)) ℝ :=
  Matrix.of fun i j => if (j : ℕ) < r then c * u i else c * v i

theorem twoType_apply_lt {r d : ℕ} {u v : Fin d → ℝ} {c : ℝ} (i : Fin d) {j : Fin (r + 1)}
    (hj : (j : ℕ) < r) : twoType r d u v c i j = c * u i := if_pos hj

theorem twoType_apply_not_lt {r d : ℕ} {u v : Fin d → ℝ} {c : ℝ} (i : Fin d) {j : Fin (r + 1)}
    (hj : ¬ (j : ℕ) < r) : twoType r d u v c i j = c * v i := if_neg hj

theorem causalSoftmax_apply {T : ℕ} (M : Matrix (Fin T) (Fin T) ℝ) (i j : Fin T) :
    causalSoftmax M i j
      = if i ≤ j then Real.exp (M i j) / ∑ i' ∈ Finset.Iic j, Real.exp (M i' j) else 0 := rfl

/-- Entry of the score matrix `Xᵀ A X` as a double sum. -/
theorem quadform_apply {d T : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (X : Matrix (Fin d) (Fin T) ℝ) (i j : Fin T) :
    (Xᵀ * A * X) i j = ∑ a, ∑ b, X a i * A a b * X b j := by
  simp_rw [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  exact Finset.sum_comm

/-- Scores of a two-type input are determined by the column types. -/
theorem twoType_score {r d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (u v : Fin d → ℝ) (c : ℝ)
    (i j : Fin (r + 1)) :
    ((twoType r d u v c)ᵀ * A * twoType r d u v c) i j
      = c ^ 2 * ((if (i : ℕ) < r then u else v) ⬝ᵥ
          A.mulVec (if (j : ℕ) < r then u else v)) := by
  rw [quadform_apply]
  have hXi : ∀ a, twoType r d u v c a i = c * (if (i : ℕ) < r then u else v) a := by
    intro a
    by_cases h : (i : ℕ) < r
    · rw [twoType_apply_lt a h, if_pos h]
    · rw [twoType_apply_not_lt a h, if_neg h]
  have hXj : ∀ b, twoType r d u v c b j = c * (if (j : ℕ) < r then u else v) b := by
    intro b
    by_cases h : (j : ℕ) < r
    · rw [twoType_apply_lt b h, if_pos h]
    · rw [twoType_apply_not_lt b h, if_neg h]
  simp_rw [hXi, hXj, dotProduct, Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- Row of `V * X` for a two-type input `X`. -/
theorem mul_twoType_apply {r d : ℕ} (V : Matrix (Fin d) (Fin d) ℝ) (u v : Fin d → ℝ)
    (c : ℝ) (i : Fin d) (k : Fin (r + 1)) :
    (V * twoType r d u v c) i k
      = c * (V.mulVec (if (k : ℕ) < r then u else v)) i := by
  rw [Matrix.mul_apply]
  have hXk : ∀ a, twoType r d u v c a k = c * (if (k : ℕ) < r then u else v) a := by
    intro a
    by_cases h : (k : ℕ) < r
    · rw [twoType_apply_lt a h, if_pos h]
    · rw [twoType_apply_not_lt a h, if_neg h]
  simp_rw [hXk, Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-- Causal softmax weights at a context column are uniform. -/
theorem causalSoftmax_twoType_lt {r d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (u v : Fin d → ℝ) (c : ℝ) {j : Fin (r + 1)} (hj : (j : ℕ) < r) (i : Fin (r + 1)) :
    causalSoftmax ((twoType r d u v c)ᵀ * A * twoType r d u v c) i j
      = if i ≤ j then (((j : ℕ) : ℝ) + 1)⁻¹ else 0 := by
  have hscore : ∀ i' : Fin (r + 1), i' ≤ j →
      ((twoType r d u v c)ᵀ * A * twoType r d u v c) i' j
        = c ^ 2 * (u ⬝ᵥ A.mulVec u) := by
    intro i' hi'
    have hi'r : (i' : ℕ) < r := lt_of_le_of_lt hi' hj
    rw [twoType_score, if_pos hi'r, if_pos hj]
  rw [causalSoftmax_apply]
  by_cases hij : i ≤ j
  · rw [if_pos hij, if_pos hij, hscore i hij]
    have hden : ∑ i' ∈ Finset.Iic j,
        Real.exp (((twoType r d u v c)ᵀ * A * twoType r d u v c) i' j)
        = (((j : ℕ) : ℝ) + 1) * Real.exp (c ^ 2 * (u ⬝ᵥ A.mulVec u)) := by
      rw [Finset.sum_congr rfl
        (fun i' hi' => by rw [hscore i' (Finset.mem_Iic.mp hi')])]
      rw [Finset.sum_const, Fin.card_Iic, nsmul_eq_mul]
      push_cast
      ring
    rw [hden]
    have hexp := Real.exp_ne_zero (c ^ 2 * (u ⬝ᵥ A.mulVec u))
    have hj1 : (((j : ℕ) : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  · rw [if_neg hij, if_neg hij]

/-- **Single-layer closure** (Proposition `prop:probe`, one-layer case): a causal
attention layer maps a two-type input to a two-type input. -/
theorem attnLayer_twoType {r d : ℕ} (hr : 0 < r) (V A : Matrix (Fin d) (Fin d) ℝ)
    (u v : Fin d → ℝ) (c : ℝ) :
    attnLayer V A (twoType r d u v c)
      = twoType r d (u + V.mulVec u)
          (v + V.mulVec v
            + sig (c ^ 2 * ((u - v) ⬝ᵥ A.mulVec v) + Real.log r) • V.mulVec (u - v)) c := by
  ext i j
  rw [attnLayer, Matrix.add_apply]
  by_cases hj : (j : ℕ) < r
  · -- context column: uniform causal weights over `j + 1` identical keys
    rw [twoType_apply_lt i hj, twoType_apply_lt i hj, Matrix.mul_apply]
    have hcs : ∀ k : Fin (r + 1),
        (V * twoType r d u v c) i k
          * causalSoftmax ((twoType r d u v c)ᵀ * A * twoType r d u v c) k j
        = if k ≤ j then c * (V.mulVec u) i * (((j : ℕ) : ℝ) + 1)⁻¹ else 0 := by
      intro k
      rw [causalSoftmax_twoType_lt A u v c hj k]
      by_cases hk : k ≤ j
      · have hkr : (k : ℕ) < r := lt_of_le_of_lt (Fin.le_def.mp hk) hj
        rw [if_pos hk, if_pos hk, mul_twoType_apply, if_pos hkr]
      · rw [if_neg hk, if_neg hk, mul_zero]
    simp_rw [hcs]
    have hfilter : Finset.filter (fun k : Fin (r + 1) => k ≤ j) Finset.univ
        = Finset.Iic j := by
      ext k
      simp [Finset.mem_Iic]
    rw [← Finset.sum_filter, hfilter, Finset.sum_const, Fin.card_Iic, nsmul_eq_mul]
    have hj1 : (((j : ℕ) : ℝ) + 1) ≠ 0 := by positivity
    rw [Pi.add_apply]
    push_cast
    field_simp
    try ring
  · -- query column: `j` is the last column
    have hjlast : j = Fin.last r := by
      apply Fin.ext
      have := j.isLt
      simp only [Fin.val_last]
      omega
    subst hjlast
    rw [twoType_apply_not_lt i hj, twoType_apply_not_lt i hj, Matrix.mul_apply]
    set suv : ℝ := c ^ 2 * (u ⬝ᵥ A.mulVec v) with hsuv
    set svv : ℝ := c ^ 2 * (v ⬝ᵥ A.mulVec v) with hsvv
    have hS : ∀ k : Fin (r + 1),
        ((twoType r d u v c)ᵀ * A * twoType r d u v c) k (Fin.last r)
          = if (k : ℕ) < r then suv else svv := by
      intro k
      rw [twoType_score, if_neg hj]
      by_cases hk : (k : ℕ) < r
      · rw [if_pos hk, if_pos hk, hsuv]
      · rw [if_neg hk, if_neg hk, hsvv]
    have hIic : Finset.Iic (Fin.last r) = (Finset.univ : Finset (Fin (r + 1))) := by
      ext k
      simp [Finset.mem_Iic, Fin.le_last]
    have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
    set D : ℝ := (r : ℝ) * Real.exp suv + Real.exp svv with hD
    have hDval : ∑ i' ∈ Finset.Iic (Fin.last r),
        Real.exp (((twoType r d u v c)ᵀ * A * twoType r d u v c) i' (Fin.last r)) = D := by
      rw [hIic, Fin.sum_univ_castSucc]
      have h1 : ∀ k : Fin r,
          Real.exp (((twoType r d u v c)ᵀ * A * twoType r d u v c) k.castSucc (Fin.last r))
            = Real.exp suv := by
        intro k
        rw [hS, if_pos (by simp)]
      have h2 : Real.exp
          (((twoType r d u v c)ᵀ * A * twoType r d u v c) (Fin.last r) (Fin.last r))
            = Real.exp svv := by
        rw [hS, if_neg (by simp)]
      simp_rw [h1]
      rw [h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hD]
    set s : ℝ := sig (c ^ 2 * ((u - v) ⬝ᵥ A.mulVec v) + Real.log r) with hs
    have hsig_arg : c ^ 2 * ((u - v) ⬝ᵥ A.mulVec v) + Real.log (r : ℝ)
        = suv - svv + Real.log (r : ℝ) := by
      rw [hsuv, hsvv, sub_dotProduct]
      ring
    have hexplog : Real.exp (Real.log (r : ℝ)) = (r : ℝ) := Real.exp_log hrpos
    have hkey : Real.exp (-(suv - svv + Real.log (r : ℝ))) * ((r : ℝ) * Real.exp suv)
        = Real.exp svv := by
      rw [show -(suv - svv + Real.log (r : ℝ)) = svv + -suv + -Real.log (r : ℝ) by ring,
        Real.exp_add, Real.exp_add, Real.exp_neg, Real.exp_neg, hexplog]
      field_simp
    have hsD : s * D = (r : ℝ) * Real.exp suv := by
      rw [hs, hsig_arg, hD]
      have hd := sig_mul_denom (suv - svv + Real.log (r : ℝ))
      linear_combination ((r : ℝ) * Real.exp suv) * hd
        - sig (suv - svv + Real.log (r : ℝ)) * hkey
    have hDpos : 0 < D := by
      rw [hD]
      have h1 : 0 < (r : ℝ) * Real.exp suv := mul_pos hrpos (Real.exp_pos _)
      have h2 : 0 < Real.exp svv := Real.exp_pos _
      linarith
    have hw1 : (r : ℝ) * (Real.exp suv / D) = s := by
      rw [← mul_div_assoc, div_eq_iff hDpos.ne']
      linear_combination -hsD
    have hw2 : Real.exp svv / D = 1 - s := by
      rw [div_eq_iff hDpos.ne']
      linear_combination hsD - hD
    have hterm : ∀ k : Fin (r + 1),
        (V * twoType r d u v c) i k
          * causalSoftmax ((twoType r d u v c)ᵀ * A * twoType r d u v c) k (Fin.last r)
        = (if (k : ℕ) < r then c * (V.mulVec u) i * (Real.exp suv / D)
           else c * (V.mulVec v) i * (Real.exp svv / D)) := by
      intro k
      rw [causalSoftmax_apply, if_pos (Fin.le_last k), hDval, hS, mul_twoType_apply]
      by_cases hk : (k : ℕ) < r
      · rw [if_pos hk, if_pos hk, if_pos hk]
      · rw [if_neg hk, if_neg hk, if_neg hk]
    simp_rw [hterm]
    rw [Fin.sum_univ_castSucc]
    have hcast : ∀ k : Fin r,
        (if ((k.castSucc : Fin (r + 1)) : ℕ) < r
          then c * (V.mulVec u) i * (Real.exp suv / D)
          else c * (V.mulVec v) i * (Real.exp svv / D))
        = c * (V.mulVec u) i * (Real.exp suv / D) :=
      fun k => if_pos (by simp)
    simp_rw [hcast]
    rw [if_neg (show ¬ ((Fin.last r : Fin (r + 1)) : ℕ) < r by simp)]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Pi.add_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.mulVec_sub, Pi.sub_apply]
    linear_combination (c * (V.mulVec u) i) * hw1 + (c * (V.mulVec v) i) * hw2

/-! ## Probe inputs and the peeling identity -/

/-- The probe input `X_{w,v}(τ) = √τ · [u ⋯ u  v]` with `u = w + v`:
`r` context columns equal to `√τ · (w+v)` and one query column `√τ · v`. -/
noncomputable def probeInput (r : ℕ) {d : ℕ} (w v : Fin d → ℝ) (τ : ℝ) :
    Matrix (Fin d) (Fin (r + 1)) ℝ :=
  twoType r d (w + v) v (Real.sqrt τ)

/-- **Single-layer probe reduction.**  One causal attention layer maps the probe at
`(w, v)` to the probe at `(w₁, v₁)`, with the *same* inverse temperature `τ`, where
`w₁ = (I+V)w - s·Vw` and `v₁ = (I+V)v + s·Vw` and `s = σ(τ·wᵀAv + log r)`.

This is Proposition `prop:probe` (case `ℓ = 1`): the gate argument `c²(u-v)ᵀAv`
becomes `τ·wᵀAv` since `c = √τ` and `u - v = w`. -/
theorem attnLayer_probeInput {r d : ℕ} (hr : 0 < r) (V A : Matrix (Fin d) (Fin d) ℝ)
    (w v : Fin d → ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    attnLayer V A (probeInput r w v τ)
      = probeInput r
          (w + V.mulVec w - sig (τ * (w ⬝ᵥ A.mulVec v) + Real.log r) • V.mulVec w)
          (v + V.mulVec v + sig (τ * (w ⬝ᵥ A.mulVec v) + Real.log r) • V.mulVec w)
          τ := by
  have hsq : Real.sqrt τ ^ 2 = τ := Real.sq_sqrt hτ
  have huv : (w + v) - v = w := add_sub_cancel_right w v
  rw [probeInput, attnLayer_twoType hr, probeInput, huv, hsq]
  rw [show (w + v) + V.mulVec (w + v)
        = (w + V.mulVec w - sig (τ * (w ⬝ᵥ A.mulVec v) + Real.log r) • V.mulVec w)
          + (v + V.mulVec v + sig (τ * (w ⬝ᵥ A.mulVec v) + Real.log r) • V.mulVec w)
        from by rw [Matrix.mulVec_add]; module]

/-- Unfolding the depth-`(L+1)` network: apply the first layer, then recurse on the tail. -/
theorem transformer_succ {d T L : ℕ} (θ : Params (L + 1) d)
    (X : Matrix (Fin d) (Fin T) ℝ) :
    transformer θ X = transformer (Fin.tail θ) (attnLayer (θ 0).1 (θ 0).2 X) := rfl

/-- The depth-`L` path observable `F^{(L)}_θ(w,v,τ)`: the last column of the network
output on the probe `X_{w,v}(τ)`, rescaled by `1/√τ`. -/
noncomputable def Fobs {d : ℕ} (r : ℕ) {L : ℕ} (θ : Params L d)
    (w v : Fin d → ℝ) (τ : ℝ) : Fin d → ℝ :=
  fun i => (Real.sqrt τ)⁻¹ * transformer θ (probeInput r w v τ) i (Fin.last r)

/-- **Peeling** (Lemma `lem:peeling`).  The depth-`(L+1)` observable equals the
depth-`L` observable of the tail parameters `θ_{≥2}`, evaluated at the once-updated
pair `(w₁, v₁)` and the *same* `τ`, with `s₁ = σ(τ·wᵀA₁v + log r)`. -/
theorem peeling {d : ℕ} (r : ℕ) (hr : 0 < r) {L : ℕ} (θ : Params (L + 1) d)
    (w v : Fin d → ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    Fobs r θ w v τ
      = Fobs r (Fin.tail θ)
          (w + (θ 0).1.mulVec w
            - sig (τ * (w ⬝ᵥ (θ 0).2.mulVec v) + Real.log r) • (θ 0).1.mulVec w)
          (v + (θ 0).1.mulVec v
            + sig (τ * (w ⬝ᵥ (θ 0).2.mulVec v) + Real.log r) • (θ 0).1.mulVec w)
          τ := by
  unfold Fobs
  rw [transformer_succ, attnLayer_probeInput hr _ _ _ _ hτ]

/-- The closed-form path recursion `F^{(L)}_θ(w,v,τ) = v_L`, defined by peeling the head
layer and recursing on the tail (Proposition `prop:probe`, equation `eq:recursion`). -/
noncomputable def Frec {d : ℕ} (r : ℕ) :
    {L : ℕ} → Params L d → (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)
  | 0, _, _, v, _ => v
  | _ + 1, θ, w, v, τ =>
      Frec r (Fin.tail θ)
        (w + (θ 0).1.mulVec w
          - sig (τ * (w ⬝ᵥ (θ 0).2.mulVec v) + Real.log r) • (θ 0).1.mulVec w)
        (v + (θ 0).1.mulVec v
          + sig (τ * (w ⬝ᵥ (θ 0).2.mulVec v) + Real.log r) • (θ 0).1.mulVec w)
        τ

/-- Unfolding the path recursion at depth `L+1`: one peeling step then recurse. -/
theorem Frec_succ {d : ℕ} (r : ℕ) {L : ℕ} (θ : Params (L + 1) d)
    (w v : Fin d → ℝ) (τ : ℝ) :
    Frec r θ w v τ
      = Frec r (Fin.tail θ)
          (w + (θ 0).1.mulVec w
            - sig (τ * (w ⬝ᵥ (θ 0).2.mulVec v) + Real.log r) • (θ 0).1.mulVec w)
          (v + (θ 0).1.mulVec v
            + sig (τ * (w ⬝ᵥ (θ 0).2.mulVec v) + Real.log r) • (θ 0).1.mulVec w)
          τ := rfl

/-- **Probe reduction** (Proposition `prop:probe`).  For `τ > 0` the transformer's
rescaled last-column observable on the probe `X_{w,v}(τ)` equals the closed-form
recursion value `v_L`.  Proved by induction on the depth using `peeling`. -/
theorem probe_reduction {d : ℕ} (r : ℕ) (hr : 0 < r) :
    ∀ {L : ℕ} (θ : Params L d) (w v : Fin d → ℝ) {τ : ℝ}, 0 < τ →
      Fobs r θ w v τ = Frec r θ w v τ := by
  intro L
  induction L with
  | zero =>
    intro θ w v τ hτ
    have hsqrt : Real.sqrt τ ≠ 0 := (Real.sqrt_pos.mpr hτ).ne'
    funext i
    rw [Fobs, Frec]
    show (Real.sqrt τ)⁻¹ * transformer θ (probeInput r w v τ) i (Fin.last r) = v i
    -- depth-`0` network is the identity, and the last column of the probe is `√τ · v`
    rw [show transformer θ (probeInput r w v τ) = probeInput r w v τ from rfl, probeInput,
      twoType_apply_not_lt i (by simp)]
    field_simp
  | succ n ih =>
    intro θ w v τ hτ
    rw [peeling r hr θ w v hτ.le, ih _ _ _ hτ, Frec_succ]

/-- Explicit theorem form of `probe_reduction`, useful for rewriting a fixed depth. -/
theorem Fobs_eq_Frec_of_pos {d L : ℕ} (r : ℕ) (hr : 0 < r) (θ : Params L d)
    (w v : Fin d → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    Fobs r θ w v τ = Frec r θ w v τ :=
  probe_reduction r hr θ w v hτ

/-- Coordinate form of `probe_reduction`. -/
theorem Fobs_apply_eq_Frec_apply_of_pos {d L : ℕ} (r : ℕ) (hr : 0 < r)
    (θ : Params L d) (w v : Fin d → ℝ) {τ : ℝ} (hτ : 0 < τ) (i : Fin d) :
    Fobs r θ w v τ i = Frec r θ w v τ i :=
  congrFun (Fobs_eq_Frec_of_pos r hr θ w v hτ) i

/-! ## Formal stream evaluators

The TeX proof uses vector-valued polynomials in formal gate variables
`z_1, z_2, ...`.  The definitions below encode those polynomials by their evaluation
maps on a gate assignment `z : Nat -> ℂ`.  This keeps the recursion close to the
closed-form probe recursion above while avoiding an early commitment to a particular
multivariate-polynomial indexing type.
-/

/-- A real matrix, viewed over `ℂ`. -/
noncomputable def matC {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℂ :=
  M.map (algebraMap ℝ ℂ)

/-- A real vector, viewed over `ℂ`. -/
noncomputable def vecC {d : ℕ} (x : Fin d → ℝ) : Fin d → ℂ :=
  fun i => (x i : ℂ)

/-- The skip matrix `B = I + V`. -/
noncomputable def skipB {d : ℕ} (V : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  1 + V

/-- The complex formal factor `B_j - z_j V_j`, with zero-based layer/gate indexing. -/
noncomputable def formalFactor {d : ℕ}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (z : Nat → ℂ) (j : Nat) : Matrix (Fin d) (Fin d) ℂ :=
  matC (skipB (θ j).1) - z j • matC (θ j).1

/-- Product of skip matrices `B_j ... B_1`, evaluated over `ℂ`.

Indexing is zero-based: `formalBprod θ n` uses layers `0, ..., n-1`. -/
noncomputable def formalBprod {d : ℕ}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ) :
    Nat → Matrix (Fin d) (Fin d) ℂ
  | 0 => 1
  | n + 1 => matC (skipB (θ n).1) * formalBprod θ n

/-- Formal product `W_n(z) = (B_n - z_n V_n) ... (B_1 - z_1 V_1)`.

Indexing is zero-based: `formalW θ n z` uses layers/gates `0, ..., n-1`. -/
noncomputable def formalW {d : ℕ}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ) :
    Nat → (Nat → ℂ) → Matrix (Fin d) (Fin d) ℂ
  | 0, _ => 1
  | n + 1, z => formalFactor θ z n * formalW θ n z

/-- Formal accumulated value-transfer matrix `T_n`.

It is the recursive form of
`sum_i z_i B_{n:i+1} V_i W_{i-1}(z)`, with zero-based indexing. -/
noncomputable def formalT {d : ℕ}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ) :
    Nat → (Nat → ℂ) → Matrix (Fin d) (Fin d) ℂ
  | 0, _ => 0
  | n + 1, z =>
      matC (skipB (θ n).1) * formalT θ n z
        + z n • (matC (θ n).1 * formalW θ n z)

/-- Formal `w_n(z)` stream. -/
noncomputable def formalWVec {d : ℕ}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) (z : Nat → ℂ) (w : Fin d → ℝ) : Fin d → ℂ :=
  formalW θ n z *ᵥ vecC w

/-- Formal `v_n(z)` stream, defined by the same affine recursion as the real gates. -/
noncomputable def formalVVec {d : ℕ}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ) :
    Nat → (Nat → ℂ) → (Fin d → ℝ) → (Fin d → ℝ) → Fin d → ℂ
  | 0, _, _, v => vecC v
  | n + 1, z, w, v =>
      matC (skipB (θ n).1) *ᵥ formalVVec θ n z w v
        + z n • (matC (θ n).1 *ᵥ formalWVec θ n z w)

/-- Formal slope polynomial `φ_{n+1}` evaluated at gate assignment `z`.

The natural-language proof indexes this as `φ_ℓ(z_1,...,z_{ℓ-1};w,v)`.
Here `n = ℓ - 1`, so the attention matrix is read from layer `n`. -/
noncomputable def formalPhi {d : ℕ}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) (z : Nat → ℂ) (w v : Fin d → ℝ) : ℂ :=
  formalWVec θ n z w ⬝ᵥ (matC (θ n).2 *ᵥ formalVVec θ n z w v)

/-- The matrix multiplying `v` in the affine decomposition of `formalPhi`. -/
noncomputable def formalX {d : ℕ}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) (z : Nat → ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  (formalW θ n z)ᵀ * matC (θ n).2 * formalBprod θ n

/-- The quadratic-in-`w` matrix in the affine decomposition of `formalPhi`. -/
noncomputable def formalY {d : ℕ}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) (z : Nat → ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  (formalW θ n z)ᵀ * matC (θ n).2 * formalT θ n z

/-- The visible coefficient vector `V_{n+1} W_n(z) w` used in the last-layer blow-up
argument.  In the TeX proof this is the vector polynomial `g_m`. -/
noncomputable def formalVisible {d : ℕ}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) (z : Nat → ℂ) (w : Fin d → ℝ) : Fin d → ℂ :=
  matC (θ n).1 *ᵥ formalWVec θ n z w

/-- A scalar coordinate of `formalVisible`. -/
noncomputable def formalVisibleCoord {d : ℕ}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) (z : Nat → ℂ) (w : Fin d → ℝ) (i : Fin d) : ℂ :=
  formalVisible θ n z w i

/-! ### Polynomial realization of the formal streams -/

/-- Polynomial ring in `K` formal gate variables. -/
abbrev GatePoly (K : Nat) := MvPolynomial (Fin K) ℂ

/-- A real matrix as a constant matrix over the gate-polynomial ring. -/
noncomputable def matPolyC {K d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) (GatePoly K) :=
  M.map fun x => MvPolynomial.C (x : ℂ)

/-- A real vector as a constant vector over the gate-polynomial ring. -/
noncomputable def vecPolyC {K d : ℕ} (x : Fin d → ℝ) : Fin d → GatePoly K :=
  fun i => MvPolynomial.C (x i : ℂ)

/-- The `j`-th gate variable in a `K`-variable polynomial ring, or `0` if `j >= K`. -/
noncomputable def gateVar (K j : Nat) : GatePoly K :=
  if h : j < K then MvPolynomial.X ⟨j, h⟩ else 0

/-- Extend a `K`-variable assignment to the zero-padded `Nat`-indexed assignment. -/
noncomputable def extendGate {K : Nat} (x : Fin K → ℂ) : Nat → ℂ :=
  fun j => if h : j < K then x ⟨j, h⟩ else 0

/-- Polynomial version of `formalFactor`. -/
noncomputable def formalFactorPoly {K d : ℕ}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (j : Nat) : Matrix (Fin d) (Fin d) (GatePoly K) :=
  matPolyC (skipB (θ j).1) - gateVar K j • matPolyC (θ j).1

/-- Polynomial version of `formalW`. -/
noncomputable def formalWPoly {K d : ℕ}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ) :
    Nat → Matrix (Fin d) (Fin d) (GatePoly K)
  | 0 => 1
  | n + 1 => formalFactorPoly θ n * formalWPoly θ n

/-- Polynomial version of `formalWVec`. -/
noncomputable def formalWVecPoly {K d : ℕ}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) (w : Fin d → ℝ) : Fin d → GatePoly K :=
  formalWPoly θ n *ᵥ vecPolyC w

/-- Polynomial version of `formalVVec`. -/
noncomputable def formalVVecPoly {K d : ℕ}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ) :
    Nat → (Fin d → ℝ) → (Fin d → ℝ) → Fin d → GatePoly K
  | 0, _, v => vecPolyC v
  | n + 1, w, v =>
      matPolyC (skipB (θ n).1) *ᵥ formalVVecPoly θ n w v
        + gateVar K n • (matPolyC (θ n).1 *ᵥ formalWVecPoly θ n w)

/-- Polynomial version of `formalPhi`. -/
noncomputable def formalPhiPoly {K d : ℕ}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) (w v : Fin d → ℝ) : GatePoly K :=
  formalWVecPoly θ n w ⬝ᵥ (matPolyC (θ n).2 *ᵥ formalVVecPoly θ n w v)

/-- Polynomial version of `formalVisible`. -/
noncomputable def formalVisiblePoly {K d : ℕ}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) (w : Fin d → ℝ) : Fin d → GatePoly K :=
  matPolyC (θ n).1 *ᵥ formalWVecPoly θ n w

theorem eval_gateVar {K : Nat} (x : Fin K → ℂ) (j : Nat) :
    MvPolynomial.eval x (gateVar K j) = extendGate x j := by
  unfold gateVar extendGate
  by_cases h : j < K
  · simp [h]
  · simp [h]

theorem eval_matPolyC {K d : ℕ} (x : Fin K → ℂ)
    (M : Matrix (Fin d) (Fin d) ℝ) :
    (matPolyC M).map (MvPolynomial.eval x) = matC M := by
  ext i j
  simp [matPolyC, matC]

theorem eval_vecPolyC {K d : ℕ} (x : Fin K → ℂ) (v : Fin d → ℝ) :
    (fun i => MvPolynomial.eval x (vecPolyC v i)) = vecC v := by
  funext i
  simp [vecPolyC, vecC]

theorem eval_matrix_mul {K m n o : ℕ} (x : Fin K → ℂ)
    (A : Matrix (Fin m) (Fin n) (GatePoly K))
    (B : Matrix (Fin n) (Fin o) (GatePoly K)) :
    (A * B).map (MvPolynomial.eval x) =
      A.map (MvPolynomial.eval x) * B.map (MvPolynomial.eval x) := by
  ext i j
  simp [Matrix.mul_apply]

theorem eval_matrix_sub {K m n : ℕ} (x : Fin K → ℂ)
    (A B : Matrix (Fin m) (Fin n) (GatePoly K)) :
    (A - B).map (MvPolynomial.eval x) =
      A.map (MvPolynomial.eval x) - B.map (MvPolynomial.eval x) := by
  ext i j
  simp

theorem eval_matrix_smul {K m n : ℕ} (x : Fin K → ℂ)
    (c : GatePoly K) (A : Matrix (Fin m) (Fin n) (GatePoly K)) :
    (c • A).map (MvPolynomial.eval x) =
      MvPolynomial.eval x c • A.map (MvPolynomial.eval x) := by
  ext i j
  simp [smul_eq_mul]

theorem eval_mulVec {K m n : ℕ} (x : Fin K → ℂ)
    (A : Matrix (Fin m) (Fin n) (GatePoly K)) (v : Fin n → GatePoly K) :
    (fun i => MvPolynomial.eval x ((A *ᵥ v) i)) =
      A.map (MvPolynomial.eval x) *ᵥ fun i => MvPolynomial.eval x (v i) := by
  funext i
  simp [Matrix.mulVec, dotProduct]

theorem eval_dotProduct {K n : ℕ} (x : Fin K → ℂ)
    (a b : Fin n → GatePoly K) :
    MvPolynomial.eval x (a ⬝ᵥ b) =
      (fun i => MvPolynomial.eval x (a i)) ⬝ᵥ
        (fun i => MvPolynomial.eval x (b i)) := by
  simp [dotProduct]

theorem eval_formalFactorPoly {K d : ℕ}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (x : Fin K → ℂ) (j : Nat) :
    (formalFactorPoly θ j).map (MvPolynomial.eval x) =
      formalFactor θ (extendGate x) j := by
  rw [formalFactorPoly, formalFactor, eval_matrix_sub, eval_matPolyC,
    eval_matrix_smul, eval_gateVar, eval_matPolyC]

theorem eval_formalWPoly {K d : ℕ}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ) :
    ∀ (n : Nat) (x : Fin K → ℂ),
      (formalWPoly θ n).map (MvPolynomial.eval x) =
        formalW θ n (extendGate x) := by
  intro n
  induction n with
  | zero =>
      intro x
      simp [formalWPoly, formalW]
  | succ n ih =>
      intro x
      change (formalFactorPoly θ n * formalWPoly θ n).map (MvPolynomial.eval x) =
        formalFactor θ (extendGate x) n * formalW θ n (extendGate x)
      rw [eval_matrix_mul, eval_formalFactorPoly, ih]

theorem eval_formalWVecPoly {K d : ℕ}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) (x : Fin K → ℂ) (w : Fin d → ℝ) :
    (fun i => MvPolynomial.eval x (formalWVecPoly θ n w i)) =
      formalWVec θ n (extendGate x) w := by
  rw [formalWVecPoly, eval_mulVec, eval_formalWPoly, eval_vecPolyC]
  rfl

theorem eval_formalVVecPoly {K d : ℕ}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ) :
    ∀ (n : Nat) (x : Fin K → ℂ) (w v : Fin d → ℝ),
      (fun i => MvPolynomial.eval x (formalVVecPoly θ n w v i)) =
        formalVVec θ n (extendGate x) w v := by
  intro n
  induction n with
  | zero =>
      intro x w v
      simp [formalVVecPoly, formalVVec, eval_vecPolyC]
  | succ n ih =>
      intro x w v
      funext i
      have hleft :
          MvPolynomial.eval x
              ((matPolyC (skipB (θ n).1) *ᵥ formalVVecPoly θ n w v) i) =
            (matC (skipB (θ n).1) *ᵥ formalVVec θ n (extendGate x) w v) i := by
        have h := congrFun
          (eval_mulVec x (matPolyC (skipB (θ n).1)) (formalVVecPoly θ n w v)) i
        simpa [eval_matPolyC, ih x w v] using h
      have hright :
          MvPolynomial.eval x
              ((matPolyC (θ n).1 *ᵥ formalWVecPoly θ n w) i) =
            (matC (θ n).1 *ᵥ formalWVec θ n (extendGate x) w) i := by
        have h := congrFun
          (eval_mulVec x (matPolyC (θ n).1) (formalWVecPoly θ n w)) i
        simpa [eval_matPolyC, eval_formalWVecPoly] using h
      simp [formalVVecPoly, formalVVec, eval_gateVar, hleft, hright]

theorem eval_formalPhiPoly {K d : ℕ}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) (x : Fin K → ℂ) (w v : Fin d → ℝ) :
    MvPolynomial.eval x (formalPhiPoly θ n w v) =
      formalPhi θ n (extendGate x) w v := by
  rw [formalPhiPoly, formalPhi, eval_dotProduct, eval_formalWVecPoly,
    eval_mulVec, eval_matPolyC, eval_formalVVecPoly]

theorem eval_formalVisiblePoly {K d : ℕ}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) (x : Fin K → ℂ) (w : Fin d → ℝ) :
    (fun i => MvPolynomial.eval x (formalVisiblePoly θ n w i)) =
      formalVisible θ n (extendGate x) w := by
  rw [formalVisiblePoly, formalVisible, eval_mulVec, eval_matPolyC, eval_formalWVecPoly]

@[simp]
theorem formalBprod_zero {d : ℕ}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ) :
    formalBprod θ 0 = 1 := rfl

@[simp]
theorem formalBprod_succ {d : ℕ}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ) (n : Nat) :
    formalBprod θ (n + 1) = matC (skipB (θ n).1) * formalBprod θ n := rfl

@[simp]
theorem formalW_zero {d : ℕ}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (z : Nat → ℂ) :
    formalW θ 0 z = 1 := rfl

@[simp]
theorem formalW_succ {d : ℕ}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) (z : Nat → ℂ) :
    formalW θ (n + 1) z = formalFactor θ z n * formalW θ n z := rfl

@[simp]
theorem formalT_zero {d : ℕ}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (z : Nat → ℂ) :
    formalT θ 0 z = 0 := rfl

@[simp]
theorem formalT_succ {d : ℕ}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) (z : Nat → ℂ) :
    formalT θ (n + 1) z =
      matC (skipB (θ n).1) * formalT θ n z
        + z n • (matC (θ n).1 * formalW θ n z) := rfl

@[simp]
theorem formalWVec_zero {d : ℕ}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (z : Nat → ℂ) (w : Fin d → ℝ) :
    formalWVec θ 0 z w = vecC w := by
  simp [formalWVec]

theorem formalWVec_succ {d : ℕ}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) (z : Nat → ℂ) (w : Fin d → ℝ) :
    formalWVec θ (n + 1) z w =
      formalFactor θ z n *ᵥ formalWVec θ n z w := by
  simp [formalWVec, Matrix.mulVec_mulVec]

@[simp]
theorem formalVVec_zero {d : ℕ}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (z : Nat → ℂ) (w v : Fin d → ℝ) :
    formalVVec θ 0 z w v = vecC v := rfl

theorem formalVVec_succ {d : ℕ}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) (z : Nat → ℂ) (w v : Fin d → ℝ) :
    formalVVec θ (n + 1) z w v =
      matC (skipB (θ n).1) *ᵥ formalVVec θ n z w v
        + z n • (matC (θ n).1 *ᵥ formalWVec θ n z w) := rfl

theorem formalVVec_succ_visible {d : ℕ}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) (z : Nat → ℂ) (w v : Fin d → ℝ) :
    formalVVec θ (n + 1) z w v =
      matC (skipB (θ n).1) *ᵥ formalVVec θ n z w v
        + z n • formalVisible θ n z w := rfl

theorem formalVVec_eq_Bprod_add_T {d : ℕ}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ) :
    ∀ (n : Nat) (z : Nat → ℂ) (w v : Fin d → ℝ),
      formalVVec θ n z w v =
        formalBprod θ n *ᵥ vecC v + formalT θ n z *ᵥ vecC w := by
  intro n
  induction n with
  | zero =>
      intro z w v
      simp
  | succ n ih =>
      intro z w v
      rw [formalVVec_succ, ih z w v]
      ext i
      simp [formalBprod_succ, formalT_succ, Matrix.mulVec_add, Matrix.add_mulVec,
        Matrix.mulVec_mulVec, Matrix.smul_mulVec, formalWVec]
      module

theorem formalPhi_zero {d : ℕ}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (z : Nat → ℂ) (w v : Fin d → ℝ) :
    formalPhi θ 0 z w v = vecC w ⬝ᵥ (matC (θ 0).2 *ᵥ vecC v) := by
  simp [formalPhi, formalWVec]

theorem formalPhi_eq_Bprod_T {d : ℕ}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) (z : Nat → ℂ) (w v : Fin d → ℝ) :
    formalPhi θ n z w v =
      formalWVec θ n z w ⬝ᵥ
        (matC (θ n).2 *ᵥ
          (formalBprod θ n *ᵥ vecC v + formalT θ n z *ᵥ vecC w)) := by
  rw [formalPhi, formalVVec_eq_Bprod_add_T]

/-- Lemma `phi(i)`: the formal slope is affine in `v`, with linear part `formalX`
and `w`-quadratic part `formalY`. -/
theorem formalPhi_eq_affine {d : ℕ}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) (z : Nat → ℂ) (w v : Fin d → ℝ) :
    formalPhi θ n z w v =
      vecC w ⬝ᵥ (formalX θ n z *ᵥ vecC v)
        + vecC w ⬝ᵥ (formalY θ n z *ᵥ vecC w) := by
  rw [formalPhi_eq_Bprod_T]
  simp [formalWVec, formalX, formalY, Matrix.mulVec_add, dotProduct_add,
    Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, Matrix.mul_assoc]

/-! ### Real-valuedness of the formal stream on real gate assignments -/

/-- A complex number that lies on the embedded real axis. -/
def IsComplexReal (z : ℂ) : Prop :=
  ∃ x : ℝ, z = (x : ℂ)

namespace IsComplexReal

theorem ofReal (x : ℝ) : IsComplexReal (x : ℂ) :=
  ⟨x, rfl⟩

theorem zero : IsComplexReal (0 : ℂ) := by
  simpa using ofReal 0

theorem one : IsComplexReal (1 : ℂ) := by
  simpa using ofReal 1

theorem add {z w : ℂ} (hz : IsComplexReal z) (hw : IsComplexReal w) :
    IsComplexReal (z + w) := by
  rcases hz with ⟨x, rfl⟩
  rcases hw with ⟨y, rfl⟩
  exact ⟨x + y, by simp⟩

theorem neg {z : ℂ} (hz : IsComplexReal z) : IsComplexReal (-z) := by
  rcases hz with ⟨x, rfl⟩
  exact ⟨-x, by simp⟩

theorem sub {z w : ℂ} (hz : IsComplexReal z) (hw : IsComplexReal w) :
    IsComplexReal (z - w) := by
  simpa [sub_eq_add_neg] using hz.add hw.neg

theorem mul {z w : ℂ} (hz : IsComplexReal z) (hw : IsComplexReal w) :
    IsComplexReal (z * w) := by
  rcases hz with ⟨x, rfl⟩
  rcases hw with ⟨y, rfl⟩
  exact ⟨x * y, by simp⟩

theorem finset_sum {ι : Type*} {s : Finset ι} {f : ι -> ℂ}
    (hf : ∀ i, i ∈ s -> IsComplexReal (f i)) :
    IsComplexReal (s.sum f) := by
  classical
  revert hf
  refine Finset.induction_on s ?base ?step
  · intro _hf
    simpa using zero
  · intro a s ha ih hf
    rw [Finset.sum_insert ha]
    exact (hf a (by simp [ha])).add
      (ih fun i hi => hf i (by simp [hi]))

end IsComplexReal

theorem matC_apply_isComplexReal {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) :
    IsComplexReal (matC M i j) :=
  ⟨M i j, by simp [matC]⟩

theorem vecC_apply_isComplexReal {d : ℕ} (x : Fin d -> ℝ) (i : Fin d) :
    IsComplexReal (vecC x i) :=
  ⟨x i, by simp [vecC]⟩

theorem mulVec_isComplexReal {m n : ℕ}
    {M : Matrix (Fin m) (Fin n) ℂ} {u : Fin n -> ℂ}
    (hM : ∀ i j, IsComplexReal (M i j))
    (hu : ∀ j, IsComplexReal (u j)) :
    ∀ i, IsComplexReal ((M *ᵥ u) i) := by
  intro i
  simpa [Matrix.mulVec, dotProduct] using
    (IsComplexReal.finset_sum (s := Finset.univ)
      (f := fun j : Fin n => M i j * u j)
      (fun j _hj => (hM i j).mul (hu j)))

theorem dotProduct_isComplexReal {n : ℕ} {u v : Fin n -> ℂ}
    (hu : ∀ i, IsComplexReal (u i))
    (hv : ∀ i, IsComplexReal (v i)) :
    IsComplexReal (u ⬝ᵥ v) := by
  simpa [dotProduct] using
    (IsComplexReal.finset_sum (s := Finset.univ)
      (f := fun i : Fin n => u i * v i)
      (fun i _hi => (hu i).mul (hv i)))

theorem formalFactor_apply_isComplexReal_of_gate {d : ℕ}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    {z : Nat -> ℂ} {j : Nat} (hz : IsComplexReal (z j)) (i k : Fin d) :
    IsComplexReal (formalFactor θ z j i k) := by
  have hB : IsComplexReal (matC (skipB (θ j).1) i k) :=
    matC_apply_isComplexReal (skipB (θ j).1) i k
  have hV : IsComplexReal (matC (θ j).1 i k) :=
    matC_apply_isComplexReal (θ j).1 i k
  simpa [formalFactor, Matrix.sub_apply, Pi.smul_apply, smul_eq_mul] using
    hB.sub (hz.mul hV)

theorem formalWVec_isComplexReal_of_gatePrefix {d : ℕ}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) (z : Nat -> ℂ) (w : Fin d -> ℝ)
    (hz : ∀ j, j < n -> IsComplexReal (z j)) :
    ∀ i, IsComplexReal (formalWVec θ n z w i) := by
  induction n with
  | zero =>
      intro i
      simpa [formalWVec_zero] using vecC_apply_isComplexReal w i
  | succ n ih =>
      intro i
      have hprev : ∀ i, IsComplexReal (formalWVec θ n z w i) := by
        exact ih fun j hj => hz j (Nat.lt_trans hj (Nat.lt_succ_self n))
      rw [formalWVec_succ]
      exact mulVec_isComplexReal
        (fun i k => formalFactor_apply_isComplexReal_of_gate θ
          (hz n (Nat.lt_succ_self n)) i k)
        hprev i

theorem formalVVec_isComplexReal_of_gatePrefix {d : ℕ}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) (z : Nat -> ℂ) (w v : Fin d -> ℝ)
    (hz : ∀ j, j < n -> IsComplexReal (z j)) :
    ∀ i, IsComplexReal (formalVVec θ n z w v i) := by
  induction n with
  | zero =>
      intro i
      simpa [formalVVec_zero] using vecC_apply_isComplexReal v i
  | succ n ih =>
      intro i
      have hprevV : ∀ i, IsComplexReal (formalVVec θ n z w v i) := by
        exact ih fun j hj => hz j (Nat.lt_trans hj (Nat.lt_succ_self n))
      have hprevW : ∀ i, IsComplexReal (formalWVec θ n z w i) :=
        formalWVec_isComplexReal_of_gatePrefix θ n z w
          (fun j hj => hz j (Nat.lt_trans hj (Nat.lt_succ_self n)))
      have hleft : IsComplexReal
          ((matC (skipB (θ n).1) *ᵥ formalVVec θ n z w v) i) :=
        mulVec_isComplexReal
          (fun i k => matC_apply_isComplexReal (skipB (θ n).1) i k)
          hprevV i
      have hright : IsComplexReal
          ((z n • (matC (θ n).1 *ᵥ formalWVec θ n z w)) i) := by
        have hinner : IsComplexReal
            ((matC (θ n).1 *ᵥ formalWVec θ n z w) i) :=
          mulVec_isComplexReal
            (fun i k => matC_apply_isComplexReal (θ n).1 i k)
            hprevW i
        simpa [Pi.smul_apply, smul_eq_mul] using
          (hz n (Nat.lt_succ_self n)).mul hinner
      rw [formalVVec_succ]
      simpa [Pi.add_apply] using hleft.add hright

theorem formalPhi_isComplexReal_of_gatePrefix {d : ℕ}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) (z : Nat -> ℂ) (w v : Fin d -> ℝ)
    (hz : ∀ j, j < n -> IsComplexReal (z j)) :
    IsComplexReal (formalPhi θ n z w v) := by
  have hW : ∀ i, IsComplexReal (formalWVec θ n z w i) :=
    formalWVec_isComplexReal_of_gatePrefix θ n z w hz
  have hV : ∀ i, IsComplexReal (formalVVec θ n z w v i) :=
    formalVVec_isComplexReal_of_gatePrefix θ n z w v hz
  have hAV : ∀ i, IsComplexReal ((matC (θ n).2 *ᵥ formalVVec θ n z w v) i) :=
    mulVec_isComplexReal
      (fun i k => matC_apply_isComplexReal (θ n).2 i k)
      hV
  simpa [formalPhi] using dotProduct_isComplexReal hW hAV

/-! ### Degree bounds for the formal stream polynomials -/

def MatrixDegreeLe {K m n : Nat} (j : Fin K) (N : Nat)
    (A : Matrix (Fin m) (Fin n) (GatePoly K)) : Prop :=
  ∀ i k, MvPolynomial.degreeOf j (A i k) ≤ N

def VectorDegreeLe {K n : Nat} (j : Fin K) (N : Nat)
    (v : Fin n → GatePoly K) : Prop :=
  ∀ i, MvPolynomial.degreeOf j (v i) ≤ N

theorem degreeOf_gateVar_le_one {K : Nat} (i : Fin K) (j : Nat) :
    MvPolynomial.degreeOf i (gateVar K j) ≤ 1 := by
  unfold gateVar
  by_cases h : j < K
  · by_cases hij : i = ⟨j, h⟩
    · rw [dif_pos h, hij]
      simp
    · rw [dif_pos h, MvPolynomial.degreeOf_X i ⟨j, h⟩]
      simp [hij]
  · simp [h]

theorem degreeOf_gateVar_eq_zero_of_ne {K : Nat} (i : Fin K) {j : Nat}
    (hij : (i : Nat) ≠ j) :
    MvPolynomial.degreeOf i (gateVar K j) = 0 := by
  unfold gateVar
  by_cases h : j < K
  · have hfin : i ≠ ⟨j, h⟩ := by
      intro hEq
      exact hij (congrArg Fin.val hEq)
    rw [dif_pos h, MvPolynomial.degreeOf_X i ⟨j, h⟩]
    simp [hfin]
  · simp [h]

theorem matrixDegreeLe_matPolyC {K d : Nat} (j : Fin K)
    (M : Matrix (Fin d) (Fin d) ℝ) :
    MatrixDegreeLe j 0 (matPolyC M) := by
  intro i k
  simp [matPolyC]

theorem vectorDegreeLe_vecPolyC {K d : Nat} (j : Fin K) (v : Fin d → ℝ) :
    VectorDegreeLe j 0 (vecPolyC v) := by
  intro i
  simp [vecPolyC]

theorem matrixDegreeLe_sub {K m n : Nat} {j : Fin K} {N : Nat}
    {A B : Matrix (Fin m) (Fin n) (GatePoly K)}
    (hA : MatrixDegreeLe j N A) (hB : MatrixDegreeLe j N B) :
    MatrixDegreeLe j N (A - B) := by
  intro i k
  exact (MvPolynomial.degreeOf_sub_le j (A i k) (B i k)).trans (by
    have ha := hA i k
    have hb := hB i k
    omega)

theorem matrixDegreeLe_mul {K m n o : Nat} {j : Fin K} {N M : Nat}
    {A : Matrix (Fin m) (Fin n) (GatePoly K)}
    {B : Matrix (Fin n) (Fin o) (GatePoly K)}
    (hA : MatrixDegreeLe j N A) (hB : MatrixDegreeLe j M B) :
    MatrixDegreeLe j (N + M) (A * B) := by
  intro i k
  have hsum :=
    MvPolynomial.degreeOf_sum_le j (Finset.univ : Finset (Fin n))
      (fun l => A i l * B l k)
  rw [Matrix.mul_apply]
  exact hsum.trans (Finset.sup_le fun l _ =>
    (MvPolynomial.degreeOf_mul_le j (A i l) (B l k)).trans (by
      have ha := hA i l
      have hb := hB l k
      omega))

theorem matrixDegreeLe_smul {K m n : Nat} {j : Fin K} {N M : Nat}
    {c : GatePoly K} {A : Matrix (Fin m) (Fin n) (GatePoly K)}
    (hc : MvPolynomial.degreeOf j c ≤ N) (hA : MatrixDegreeLe j M A) :
    MatrixDegreeLe j (N + M) (c • A) := by
  intro i k
  simpa [smul_eq_mul] using
    (MvPolynomial.degreeOf_mul_le j c (A i k)).trans (by
      have ha := hA i k
      omega)

theorem vectorDegreeLe_add {K n : Nat} {j : Fin K} {N : Nat}
    {u v : Fin n → GatePoly K}
    (hu : VectorDegreeLe j N u) (hv : VectorDegreeLe j N v) :
    VectorDegreeLe j N (u + v) := by
  intro i
  exact (MvPolynomial.degreeOf_add_le j (u i) (v i)).trans (by
    have hu_i := hu i
    have hv_i := hv i
    omega)

theorem vectorDegreeLe_smul {K n : Nat} {j : Fin K} {N M : Nat}
    {c : GatePoly K} {v : Fin n → GatePoly K}
    (hc : MvPolynomial.degreeOf j c ≤ N) (hv : VectorDegreeLe j M v) :
    VectorDegreeLe j (N + M) (c • v) := by
  intro i
  simpa [Pi.smul_apply, smul_eq_mul] using
    (MvPolynomial.degreeOf_mul_le j c (v i)).trans (by
      have hv_i := hv i
      omega)

theorem matrixDegreeLe_mulVec {K m n : Nat} {j : Fin K} {N M : Nat}
    {A : Matrix (Fin m) (Fin n) (GatePoly K)} {v : Fin n → GatePoly K}
    (hA : MatrixDegreeLe j N A) (hv : VectorDegreeLe j M v) :
    VectorDegreeLe j (N + M) (A *ᵥ v) := by
  intro i
  have hsum :=
    MvPolynomial.degreeOf_sum_le j (Finset.univ : Finset (Fin n))
      (fun l => A i l * v l)
  rw [Matrix.mulVec, dotProduct]
  exact hsum.trans (Finset.sup_le fun l _ =>
    (MvPolynomial.degreeOf_mul_le j (A i l) (v l)).trans (by
      have ha := hA i l
      have hv_l := hv l
      omega))

theorem degreeOf_dotProduct_le {K n : Nat} {j : Fin K} {N M : Nat}
    {u v : Fin n → GatePoly K}
    (hu : VectorDegreeLe j N u) (hv : VectorDegreeLe j M v) :
    MvPolynomial.degreeOf j (u ⬝ᵥ v) ≤ N + M := by
  have hsum :=
    MvPolynomial.degreeOf_sum_le j (Finset.univ : Finset (Fin n))
      (fun i => u i * v i)
  rw [dotProduct]
  exact hsum.trans (Finset.sup_le fun i _ =>
    (MvPolynomial.degreeOf_mul_le j (u i) (v i)).trans (by
      have hu_i := hu i
      have hv_i := hv i
      omega))

theorem matrixDegreeLe_formalFactorPoly {K d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (j : Fin K) (n : Nat) :
    MatrixDegreeLe j 1 (formalFactorPoly θ n) := by
  refine matrixDegreeLe_sub ?_ ?_
  · intro i k
    exact (matrixDegreeLe_matPolyC j (skipB (θ n).1) i k).trans (by omega)
  · have hsmul := matrixDegreeLe_smul
      (j := j) (N := 1) (M := 0)
      (degreeOf_gateVar_le_one j n)
      (matrixDegreeLe_matPolyC j (θ n).1)
    simpa using hsmul

theorem matrixDegreeLe_formalFactorPoly_zero_of_ne {K d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (j : Fin K) {n : Nat} (hjn : (j : Nat) ≠ n) :
    MatrixDegreeLe j 0 (formalFactorPoly θ n) := by
  refine matrixDegreeLe_sub (matrixDegreeLe_matPolyC j (skipB (θ n).1)) ?_
  have hdeg : MvPolynomial.degreeOf j (gateVar K n) ≤ 0 := by
    rw [degreeOf_gateVar_eq_zero_of_ne j hjn]
  have hsmul := matrixDegreeLe_smul
    (j := j) (N := 0) (M := 0)
    hdeg
    (matrixDegreeLe_matPolyC j (θ n).1)
  simpa using hsmul

theorem matrixDegreeLe_formalWPoly_zero_of_le {K d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ) :
    ∀ (n : Nat) (j : Fin K), n ≤ (j : Nat) →
      MatrixDegreeLe j 0 (formalWPoly θ n) := by
  intro n
  induction n with
  | zero =>
      intro j _ i k
      by_cases hik : i = k
      · subst k
        simp [formalWPoly, Matrix.one_apply_eq]
      · simp [formalWPoly, Matrix.one_apply_ne hik]
  | succ n ih =>
      intro j hle
      change MatrixDegreeLe j 0 (formalFactorPoly θ n * formalWPoly θ n)
      have hjn : (j : Nat) ≠ n := by omega
      simpa using matrixDegreeLe_mul
        (j := j) (N := 0) (M := 0)
        (matrixDegreeLe_formalFactorPoly_zero_of_ne θ j hjn)
        (ih j (by omega))

theorem matrixDegreeLe_formalWPoly_one {K d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ) :
    ∀ (n : Nat) (j : Fin K), MatrixDegreeLe j 1 (formalWPoly θ n) := by
  intro n
  induction n with
  | zero =>
      intro j i k
      by_cases hik : i = k
      · subst k
        exact
          (by
            simp [formalWPoly, Matrix.one_apply_eq] :
            MvPolynomial.degreeOf j (formalWPoly θ 0 i i) ≤ 1)
      · simp [formalWPoly, Matrix.one_apply_ne hik]
  | succ n ih =>
      intro j
      change MatrixDegreeLe j 1 (formalFactorPoly θ n * formalWPoly θ n)
      by_cases hjn : (j : Nat) = n
      · have hW0 : MatrixDegreeLe j 0 (formalWPoly θ n) :=
          matrixDegreeLe_formalWPoly_zero_of_le θ n j (by omega)
        have hmul := matrixDegreeLe_mul
          (j := j) (N := 1) (M := 0)
          (matrixDegreeLe_formalFactorPoly θ j n) hW0
        simpa using hmul
      · have hF0 : MatrixDegreeLe j 0 (formalFactorPoly θ n) :=
          matrixDegreeLe_formalFactorPoly_zero_of_ne θ j hjn
        have hmul := matrixDegreeLe_mul
          (j := j) (N := 0) (M := 1) hF0 (ih j)
        simpa [Nat.zero_add] using hmul

theorem vectorDegreeLe_formalWVecPoly_one {K d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) (j : Fin K) (w : Fin d → ℝ) :
    VectorDegreeLe j 1 (formalWVecPoly θ n w) := by
  exact matrixDegreeLe_mulVec
    (j := j) (N := 1) (M := 0)
    (matrixDegreeLe_formalWPoly_one θ n j) (vectorDegreeLe_vecPolyC j w)

theorem vectorDegreeLe_formalWVecPoly_zero_of_le {K d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) (j : Fin K) (w : Fin d → ℝ) (hnj : n ≤ (j : Nat)) :
    VectorDegreeLe j 0 (formalWVecPoly θ n w) := by
  exact matrixDegreeLe_mulVec
    (j := j) (N := 0) (M := 0)
    (matrixDegreeLe_formalWPoly_zero_of_le θ n j hnj) (vectorDegreeLe_vecPolyC j w)

theorem vectorDegreeLe_formalVVecPoly_one {K d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ) :
    ∀ (n : Nat) (j : Fin K) (w v : Fin d → ℝ),
      VectorDegreeLe j 1 (formalVVecPoly θ n w v) := by
  intro n
  induction n with
  | zero =>
      intro j w v i
      exact (vectorDegreeLe_vecPolyC j v i).trans (by omega)
  | succ n ih =>
      intro j w v
      change VectorDegreeLe j 1
        (matPolyC (skipB (θ n).1) *ᵥ formalVVecPoly θ n w v
          + gateVar K n • (matPolyC (θ n).1 *ᵥ formalWVecPoly θ n w))
      refine vectorDegreeLe_add ?_ ?_
      · have hmul := matrixDegreeLe_mulVec
          (j := j) (N := 0) (M := 1)
          (matrixDegreeLe_matPolyC j (skipB (θ n).1)) (ih j w v)
        simpa [Nat.zero_add] using hmul
      · by_cases hjn : (j : Nat) = n
        · have hinner := matrixDegreeLe_mulVec
            (j := j) (N := 0) (M := 0)
            (matrixDegreeLe_matPolyC j (θ n).1)
            (vectorDegreeLe_formalWVecPoly_zero_of_le θ n j w (by omega))
          have hsmul := vectorDegreeLe_smul
            (j := j) (N := 1) (M := 0)
            (degreeOf_gateVar_le_one j n) hinner
          simpa [Matrix.smul_mulVec] using hsmul
        · have hinner := matrixDegreeLe_mulVec
            (j := j) (N := 0) (M := 1)
            (matrixDegreeLe_matPolyC j (θ n).1)
            (vectorDegreeLe_formalWVecPoly_one θ n j w)
          have hdeg : MvPolynomial.degreeOf j (gateVar K n) ≤ 0 := by
            rw [degreeOf_gateVar_eq_zero_of_ne j hjn]
          have hsmul := vectorDegreeLe_smul
            (j := j) (N := 0) (M := 1)
            hdeg hinner
          simpa [Nat.zero_add] using hsmul

theorem vectorDegreeLe_formalVVecPoly_zero_of_le {K d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ) :
    ∀ (n : Nat) (j : Fin K) (w v : Fin d → ℝ), n ≤ (j : Nat) →
      VectorDegreeLe j 0 (formalVVecPoly θ n w v) := by
  intro n
  induction n with
  | zero =>
      intro j w v _ i
      exact vectorDegreeLe_vecPolyC j v i
  | succ n ih =>
      intro j w v hnj
      change VectorDegreeLe j 0
        (matPolyC (skipB (θ n).1) *ᵥ formalVVecPoly θ n w v
          + gateVar K n • (matPolyC (θ n).1 *ᵥ formalWVecPoly θ n w))
      refine vectorDegreeLe_add ?_ ?_
      · exact matrixDegreeLe_mulVec
          (j := j) (N := 0) (M := 0)
          (matrixDegreeLe_matPolyC j (skipB (θ n).1))
          (ih j w v (by omega))
      · have hinner := matrixDegreeLe_mulVec
          (j := j) (N := 0) (M := 0)
          (matrixDegreeLe_matPolyC j (θ n).1)
          (vectorDegreeLe_formalWVecPoly_zero_of_le θ n j w (by omega))
        have hdeg : MvPolynomial.degreeOf j (gateVar K n) ≤ 0 := by
          rw [degreeOf_gateVar_eq_zero_of_ne j (by omega)]
        have hsmul := vectorDegreeLe_smul
          (j := j) (N := 0) (M := 0)
          hdeg hinner
        simpa [Matrix.smul_mulVec] using hsmul

theorem degreeOf_formalPhiPoly_le_two {K d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) (j : Fin K) (w v : Fin d → ℝ) :
    MvPolynomial.degreeOf j (formalPhiPoly θ n w v) ≤ 2 := by
  unfold formalPhiPoly
  have hleft : VectorDegreeLe j 1 (formalWVecPoly θ n w) :=
    vectorDegreeLe_formalWVecPoly_one θ n j w
  have hright_inner : VectorDegreeLe j 1 (formalVVecPoly θ n w v) :=
    vectorDegreeLe_formalVVecPoly_one θ n j w v
  have hright : VectorDegreeLe j (0 + 1)
      (matPolyC (θ n).2 *ᵥ formalVVecPoly θ n w v) :=
    matrixDegreeLe_mulVec
      (j := j) (N := 0) (M := 1)
      (matrixDegreeLe_matPolyC j (θ n).2) hright_inner
  have hdot := degreeOf_dotProduct_le (j := j) (N := 1) (M := 0 + 1) hleft hright
  omega

theorem degreeOf_formalVisiblePoly_le_one {K d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) (j : Fin K) (w : Fin d → ℝ) (i : Fin d) :
    MvPolynomial.degreeOf j (formalVisiblePoly θ n w i) ≤ 1 := by
  unfold formalVisiblePoly
  exact matrixDegreeLe_mulVec
    (j := j) (N := 0) (M := 1)
    (matrixDegreeLe_matPolyC j (θ n).1)
    (vectorDegreeLe_formalWVecPoly_one θ n j w) i

/-! ### Coefficient extraction for formal products -/

/-- Product `V_{n-1} ... V_0`, viewed over `ℂ`. -/
noncomputable def formalVprod {d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ) :
    Nat → Matrix (Fin d) (Fin d) ℂ
  | 0 => 1
  | n + 1 => matC (θ n).1 * formalVprod θ n

/-- Entrywise coefficient extraction from a matrix of gate polynomials. -/
noncomputable def coeffMatrix {K m n : Nat} (a : Fin K →₀ Nat)
    (A : Matrix (Fin m) (Fin n) (GatePoly K)) : Matrix (Fin m) (Fin n) ℂ :=
  Matrix.of fun i j => MvPolynomial.coeff a (A i j)

/-- Entrywise coefficient extraction from a vector of gate polynomials. -/
noncomputable def coeffVector {K n : Nat} (a : Fin K →₀ Nat)
    (v : Fin n → GatePoly K) : Fin n → ℂ :=
  fun i => MvPolynomial.coeff a (v i)

@[simp]
theorem formalVprod_zero {d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ) :
    formalVprod θ 0 = 1 := rfl

@[simp]
theorem formalVprod_succ {d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ) (n : Nat) :
    formalVprod θ (n + 1) = matC (θ n).1 * formalVprod θ n := rfl

@[simp]
theorem coeffMatrix_apply {K m n : Nat} (a : Fin K →₀ Nat)
    (A : Matrix (Fin m) (Fin n) (GatePoly K)) (i : Fin m) (j : Fin n) :
    coeffMatrix a A i j = MvPolynomial.coeff a (A i j) := rfl

@[simp]
theorem coeffVector_apply {K n : Nat} (a : Fin K →₀ Nat)
    (v : Fin n → GatePoly K) (i : Fin n) :
    coeffVector a v i = MvPolynomial.coeff a (v i) := rfl

theorem coeffMatrix_sub {K m n : Nat} (a : Fin K →₀ Nat)
    (A B : Matrix (Fin m) (Fin n) (GatePoly K)) :
    coeffMatrix a (A - B) = coeffMatrix a A - coeffMatrix a B := by
  ext i j
  simp [MvPolynomial.coeff_sub]

theorem coeffVector_add {K n : Nat} (a : Fin K →₀ Nat)
    (u v : Fin n → GatePoly K) :
    coeffVector a (u + v) = coeffVector a u + coeffVector a v := by
  funext i
  simp [MvPolynomial.coeff_add]

theorem coeffVector_const_mulVec {K d : Nat} (a : Fin K →₀ Nat)
    (A : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → GatePoly K) :
    coeffVector a (matPolyC A *ᵥ v) = matC A *ᵥ coeffVector a v := by
  funext i
  simp [coeffVector, matPolyC, matC, Matrix.mulVec, dotProduct,
    MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]

theorem coeff_mul_C {K : Nat} (a : Fin K →₀ Nat) (p : GatePoly K) (c : ℂ) :
    MvPolynomial.coeff a (p * MvPolynomial.C c) = MvPolynomial.coeff a p * c := by
  rw [mul_comm, MvPolynomial.coeff_C_mul, mul_comm]

theorem coeff_gateVar_mul {K : Nat} {n : Nat} (hn : n < K)
    (a : Fin K →₀ Nat) (p : GatePoly K) :
    MvPolynomial.coeff (Finsupp.single ⟨n, hn⟩ 1 + a) (gateVar K n * p) =
      MvPolynomial.coeff a p := by
  rw [gateVar, dif_pos hn]
  rw [MvPolynomial.coeff_X_mul]

/-- Peels two explicit copies of the same gate variable from a coefficient. -/
theorem coeff_gateVar_sq_mul {K : Nat} {n : Nat} (hn : n < K)
    (a : Fin K →₀ Nat) (p : GatePoly K) :
    MvPolynomial.coeff (Finsupp.single ⟨n, hn⟩ 2 + a)
        (gateVar K n * (gateVar K n * p)) =
      MvPolynomial.coeff a p := by
  have hsplit :
      Finsupp.single ⟨n, hn⟩ 2 + a =
        Finsupp.single ⟨n, hn⟩ 1 + (Finsupp.single ⟨n, hn⟩ 1 + a) := by
    ext i
    by_cases hi : i = ⟨n, hn⟩
    · subst i
      simp [Finsupp.add_apply]
      omega
    · simp [Finsupp.add_apply, Finsupp.single_eq_of_ne hi]
  rw [hsplit, coeff_gateVar_mul hn, coeff_gateVar_mul hn]

theorem coeffVector_gateVar_smul {K d : Nat} {r : Nat} (hr : r < K)
    (a : Fin K →₀ Nat) (v : Fin d → GatePoly K) :
    coeffVector (Finsupp.single ⟨r, hr⟩ 1 + a) (gateVar K r • v) =
      coeffVector a v := by
  funext i
  simp [coeffVector, Pi.smul_apply, smul_eq_mul, coeff_gateVar_mul hr]

theorem coeffVector_mulVec_const {K m n : Nat} (a : Fin K →₀ Nat)
    (A : Matrix (Fin m) (Fin n) (GatePoly K)) (v : Fin n → ℝ) :
    coeffVector a (A *ᵥ vecPolyC v) = coeffMatrix a A *ᵥ vecC v := by
  funext i
  change MvPolynomial.coeff a (∑ x, A i x * vecPolyC v x) =
    ∑ x, MvPolynomial.coeff a (A i x) * vecC v x
  rw [MvPolynomial.coeff_sum]
  simp [vecPolyC, vecC, coeff_mul_C]

theorem coeff_gateVar_C_mul {K : Nat} {n : Nat} (hn : n < K)
    (a : Fin K →₀ Nat) (c : ℂ) (p : GatePoly K) :
    MvPolynomial.coeff (Finsupp.single ⟨n, hn⟩ 1 + a)
        ((gateVar K n * MvPolynomial.C c) * p) =
      c * MvPolynomial.coeff a p := by
  rw [gateVar, dif_pos hn]
  calc
    MvPolynomial.coeff (Finsupp.single ⟨n, hn⟩ 1 + a)
        ((MvPolynomial.X ⟨n, hn⟩ * MvPolynomial.C c) * p)
        = MvPolynomial.coeff (Finsupp.single ⟨n, hn⟩ 1 + a)
            (MvPolynomial.X ⟨n, hn⟩ * (MvPolynomial.C c * p)) := by
          rw [mul_assoc]
    _ = MvPolynomial.coeff a (MvPolynomial.C c * p) := by
          rw [MvPolynomial.coeff_X_mul]
    _ = c * MvPolynomial.coeff a p := by
          rw [MvPolynomial.coeff_C_mul]

theorem coeffMatrix_gateVar_const_mul {K d o : Nat} {r : Nat} (hr : r < K)
    (a : Fin K →₀ Nat)
    (A : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin o) (GatePoly K)) :
    coeffMatrix (Finsupp.single ⟨r, hr⟩ 1 + a)
        ((gateVar K r • matPolyC A) * B) =
      matC A * coeffMatrix a B := by
  ext i k
  change MvPolynomial.coeff (Finsupp.single ⟨r, hr⟩ 1 + a)
      (∑ x, (gateVar K r • matPolyC A) i x * B x k) =
    ∑ x, matC A i x * MvPolynomial.coeff a (B x k)
  rw [MvPolynomial.coeff_sum]
  simp [matPolyC, matC, Matrix.smul_apply, smul_eq_mul, coeff_gateVar_C_mul hr]

/-! ### Top monomial indices for coefficient formulas -/

/-- The square-free monomial index `z_0 ... z_{n-1}` in `K` variables. -/
noncomputable def gateTop (K n : Nat) : Fin K →₀ Nat :=
  Finsupp.indicator (Finset.univ.filter fun i : Fin K => (i : Nat) < n)
    (fun _ _ => 1)

@[simp]
theorem gateTop_apply_lt {K n : Nat} {i : Fin K} (hi : (i : Nat) < n) :
    gateTop K n i = 1 := by
  classical
  simp [gateTop, hi]

@[simp]
theorem gateTop_apply_ge {K n : Nat} {i : Fin K} (hi : n ≤ (i : Nat)) :
    gateTop K n i = 0 := by
  classical
  simp [gateTop, not_lt.mpr hi]

theorem gateTop_zero (K : Nat) : gateTop K 0 = 0 := by
  classical
  ext i
  simp [gateTop]

theorem gateTop_succ {K n : Nat} (hn : n < K) :
    gateTop K (n + 1) = gateTop K n + Finsupp.single ⟨n, hn⟩ 1 := by
  classical
  ext i
  by_cases hin : (i : Nat) < n
  · have hne : i ≠ ⟨n, hn⟩ := by
      intro hEq
      have : (i : Nat) = n := congrArg Fin.val hEq
      omega
    simp [gateTop_apply_lt hin, gateTop_apply_lt (Nat.lt_succ_of_lt hin),
      Finsupp.single_eq_of_ne hne]
  · have hge : n ≤ (i : Nat) := not_lt.mp hin
    by_cases hin' : (i : Nat) = n
    · have hiEq : i = ⟨n, hn⟩ := Fin.ext hin'
      simp [hiEq]
    · have hsucc_ge : n + 1 ≤ (i : Nat) := by omega
      have hne : i ≠ ⟨n, hn⟩ := by
        intro hEq
        exact hin' (congrArg Fin.val hEq)
      simp [gateTop_apply_ge hge, gateTop_apply_ge hsucc_ge,
        Finsupp.single_eq_of_ne hne]

theorem gateTop_succ_single_add {K n : Nat} (hn : n < K) :
    gateTop K (n + 1) = Finsupp.single ⟨n, hn⟩ 1 + gateTop K n := by
  rw [gateTop_succ hn, add_comm]

/-- The squared top monomial index `z_0^2 ... z_{n-1}^2` in `K` variables. -/
noncomputable def gateTopSq (K n : Nat) : Fin K →₀ Nat :=
  gateTop K n + gateTop K n

@[simp]
theorem gateTopSq_apply_lt {K n : Nat} {i : Fin K} (hi : (i : Nat) < n) :
    gateTopSq K n i = 2 := by
  simp [gateTopSq, gateTop_apply_lt hi]

@[simp]
theorem gateTopSq_apply_ge {K n : Nat} {i : Fin K} (hi : n ≤ (i : Nat)) :
    gateTopSq K n i = 0 := by
  simp [gateTopSq, gateTop_apply_ge hi]

/-- If a monomial asks for more `j`-degree than `p` has, its coefficient is zero. -/
theorem coeff_eq_zero_of_degreeOf_lt {K : Nat} {j : Fin K}
    {m : Fin K →₀ Nat} {p : GatePoly K}
    (h : MvPolynomial.degreeOf j p < m j) :
    MvPolynomial.coeff m p = 0 := by
  by_contra hcoeff
  have hm : m ∈ p.support := MvPolynomial.mem_support_iff.mpr hcoeff
  have hle := MvPolynomial.le_degreeOf_of_mem_support j hm
  omega

theorem coeff_index_le_degree_bound {K N : Nat} {j : Fin K}
    {m : Fin K →₀ Nat} {p : GatePoly K}
    (hp : MvPolynomial.degreeOf j p ≤ N) (hcoeff : MvPolynomial.coeff m p ≠ 0) :
    m j ≤ N := by
  by_contra hle
  exact hcoeff (coeff_eq_zero_of_degreeOf_lt (j := j) (m := m) (by omega))

theorem coeffMatrix_eq_zero_of_matrixDegreeLe {K m n N : Nat} {j : Fin K}
    {a : Fin K →₀ Nat} {A : Matrix (Fin m) (Fin n) (GatePoly K)}
    (hA : MatrixDegreeLe j N A) (ha : N < a j) :
    coeffMatrix a A = 0 := by
  ext i k
  exact coeff_eq_zero_of_degreeOf_lt (j := j) (m := a)
    (lt_of_le_of_lt (hA i k) ha)

theorem coeffVector_eq_zero_of_vectorDegreeLe {K n N : Nat} {j : Fin K}
    {a : Fin K →₀ Nat} {v : Fin n → GatePoly K}
    (hv : VectorDegreeLe j N v) (ha : N < a j) :
    coeffVector a v = 0 := by
  funext i
  exact coeff_eq_zero_of_degreeOf_lt (j := j) (m := a)
    (lt_of_le_of_lt (hv i) ha)

theorem antidiagonal_gateTopSq_eq_gateTop {K n : Nat}
    {x y : Fin K →₀ Nat}
    (hxy : (x, y) ∈ Finset.antidiagonal (gateTopSq K n))
    (hx : ∀ j : Fin K, x j ≤ 1) (hy : ∀ j : Fin K, y j ≤ 1) :
    x = gateTop K n ∧ y = gateTop K n := by
  classical
  have hsum : x + y = gateTopSq K n := Finset.mem_antidiagonal.mp hxy
  have hxval : ∀ j : Fin K, x j = gateTop K n j := by
    intro j
    have hxyj : x j + y j = gateTopSq K n j := by
      simpa [Finsupp.add_apply] using congrArg (fun f : Fin K →₀ Nat => f j) hsum
    by_cases hj : (j : Nat) < n
    · have htop : gateTop K n j = 1 := gateTop_apply_lt hj
      have hsq : gateTopSq K n j = 2 := gateTopSq_apply_lt hj
      have hxj := hx j
      have hyj := hy j
      omega
    · have hge : n ≤ (j : Nat) := not_lt.mp hj
      have htop : gateTop K n j = 0 := gateTop_apply_ge hge
      have hsq : gateTopSq K n j = 0 := gateTopSq_apply_ge hge
      omega
  have hyval : ∀ j : Fin K, y j = gateTop K n j := by
    intro j
    have hxyj : x j + y j = gateTopSq K n j := by
      simpa [Finsupp.add_apply] using congrArg (fun f : Fin K →₀ Nat => f j) hsum
    by_cases hj : (j : Nat) < n
    · have htop : gateTop K n j = 1 := gateTop_apply_lt hj
      have hsq : gateTopSq K n j = 2 := gateTopSq_apply_lt hj
      have hxj := hx j
      have hyj := hy j
      omega
    · have hge : n ≤ (j : Nat) := not_lt.mp hj
      have htop : gateTop K n j = 0 := gateTop_apply_ge hge
      have hsq : gateTopSq K n j = 0 := gateTopSq_apply_ge hge
      omega
  exact ⟨Finsupp.ext hxval, Finsupp.ext hyval⟩

theorem coeff_mul_gateTopSq_of_degreeLe_one {K : Nat} (n : Nat)
    {p q : GatePoly K}
    (hp : ∀ j : Fin K, MvPolynomial.degreeOf j p ≤ 1)
    (hq : ∀ j : Fin K, MvPolynomial.degreeOf j q ≤ 1) :
    MvPolynomial.coeff (gateTopSq K n) (p * q) =
      MvPolynomial.coeff (gateTop K n) p * MvPolynomial.coeff (gateTop K n) q := by
  classical
  rw [MvPolynomial.coeff_mul]
  have hmem :
      (gateTop K n, gateTop K n) ∈ Finset.antidiagonal (gateTopSq K n) := by
    rw [Finset.mem_antidiagonal]
    rfl
  refine Finset.sum_eq_single (gateTop K n, gateTop K n) ?_ ?_
  · intro b hb hbne
    by_cases hbp : MvPolynomial.coeff b.1 p = 0
    · simp [hbp]
    · by_cases hbq : MvPolynomial.coeff b.2 q = 0
      · simp [hbq]
      · have hbtop := antidiagonal_gateTopSq_eq_gateTop (K := K) (n := n) hb
          (fun j => coeff_index_le_degree_bound (hp j) hbp)
          (fun j => coeff_index_le_degree_bound (hq j) hbq)
        exact (hbne (Prod.ext hbtop.1 hbtop.2)).elim
  · intro hnot
    exact (hnot hmem).elim

theorem coeff_dotProduct_gateTopSq_of_vectorDegreeLe_one {K d : Nat} (n : Nat)
    {u v : Fin d → GatePoly K}
    (hu : ∀ j : Fin K, VectorDegreeLe j 1 u)
    (hv : ∀ j : Fin K, VectorDegreeLe j 1 v) :
    MvPolynomial.coeff (gateTopSq K n) (u ⬝ᵥ v) =
      coeffVector (gateTop K n) u ⬝ᵥ coeffVector (gateTop K n) v := by
  rw [dotProduct]
  change MvPolynomial.coeff (gateTopSq K n) (∑ i, u i * v i) =
    ∑ i, coeffVector (gateTop K n) u i * coeffVector (gateTop K n) v i
  rw [MvPolynomial.coeff_sum]
  simp [coeffVector, coeff_mul_gateTopSq_of_degreeLe_one n
    (fun j => hu j _) (fun j => hv j _)]

theorem coeffMatrix_formalWPoly_gateTop {K d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ) :
    ∀ (n : Nat), n ≤ K →
      coeffMatrix (gateTop K n) (formalWPoly θ n) =
        ((-1 : ℂ) ^ n) • formalVprod θ n := by
  intro n
  induction n with
  | zero =>
      intro _
      ext i k
      by_cases hik : i = k
      · subst k
        simp [formalWPoly, formalVprod, gateTop_zero, Matrix.one_apply_eq]
      · simp [formalWPoly, formalVprod, gateTop_zero, Matrix.one_apply_ne hik]
  | succ n ih =>
      intro hnK
      have hnlt : n < K := by omega
      have hconst :
          coeffMatrix (gateTop K (n + 1))
              (matPolyC (skipB (θ n).1) * formalWPoly θ n) = 0 := by
        refine coeffMatrix_eq_zero_of_matrixDegreeLe
          (j := ⟨n, hnlt⟩) (N := 0) ?_ ?_
        · exact matrixDegreeLe_mul
            (j := ⟨n, hnlt⟩) (N := 0) (M := 0)
            (matrixDegreeLe_matPolyC ⟨n, hnlt⟩ (skipB (θ n).1))
            (matrixDegreeLe_formalWPoly_zero_of_le θ n ⟨n, hnlt⟩ (by rfl))
        · have hval : ((⟨n, hnlt⟩ : Fin K) : Nat) < n + 1 := Nat.lt_succ_self n
          simp [gateTop_apply_lt (K := K) (n := n + 1) (i := ⟨n, hnlt⟩) hval]
      have hvar :
          coeffMatrix (gateTop K (n + 1))
              ((gateVar K n • matPolyC (θ n).1) * formalWPoly θ n) =
            matC (θ n).1 * coeffMatrix (gateTop K n) (formalWPoly θ n) := by
        rw [gateTop_succ_single_add hnlt]
        exact coeffMatrix_gateVar_const_mul hnlt (gateTop K n) (θ n).1
          (formalWPoly θ n)
      change coeffMatrix (gateTop K (n + 1))
          (formalFactorPoly θ n * formalWPoly θ n) =
        ((-1 : ℂ) ^ (n + 1)) • formalVprod θ (n + 1)
      rw [formalFactorPoly, sub_mul, coeffMatrix_sub, hconst, hvar, ih (by omega)]
      simp [formalVprod_succ, pow_succ]

theorem coeffVector_formalWVecPoly_gateTop {K d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) (hnK : n ≤ K) (w : Fin d → ℝ) :
    coeffVector (gateTop K n) (formalWVecPoly θ n w) =
      ((-1 : ℂ) ^ n) • (formalVprod θ n *ᵥ vecC w) := by
  rw [formalWVecPoly, coeffVector_mulVec_const,
    coeffMatrix_formalWPoly_gateTop θ n hnK]
  simp [Matrix.smul_mulVec]

theorem coeffVector_formalVVecPoly_gateTop_succ {K d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) (hnK : n + 1 ≤ K) (w v : Fin d → ℝ) :
    coeffVector (gateTop K (n + 1)) (formalVVecPoly θ (n + 1) w v) =
      ((-1 : ℂ) ^ n) • (formalVprod θ (n + 1) *ᵥ vecC w) := by
  have hnlt : n < K := by omega
  have hconst :
      coeffVector (gateTop K (n + 1))
          (matPolyC (skipB (θ n).1) *ᵥ formalVVecPoly θ n w v) = 0 := by
    refine coeffVector_eq_zero_of_vectorDegreeLe
      (j := ⟨n, hnlt⟩) (N := 0) ?_ ?_
    · exact matrixDegreeLe_mulVec
        (j := ⟨n, hnlt⟩) (N := 0) (M := 0)
        (matrixDegreeLe_matPolyC ⟨n, hnlt⟩ (skipB (θ n).1))
        (vectorDegreeLe_formalVVecPoly_zero_of_le θ n ⟨n, hnlt⟩ w v (by rfl))
    · have hval : ((⟨n, hnlt⟩ : Fin K) : Nat) < n + 1 := Nat.lt_succ_self n
      simp [gateTop_apply_lt (K := K) (n := n + 1) (i := ⟨n, hnlt⟩) hval]
  have hvar :
      coeffVector (gateTop K (n + 1))
          (gateVar K n • (matPolyC (θ n).1 *ᵥ formalWVecPoly θ n w)) =
        matC (θ n).1 *ᵥ coeffVector (gateTop K n) (formalWVecPoly θ n w) := by
    rw [gateTop_succ_single_add hnlt]
    rw [coeffVector_gateVar_smul hnlt, coeffVector_const_mulVec]
  change coeffVector (gateTop K (n + 1))
      (matPolyC (skipB (θ n).1) *ᵥ formalVVecPoly θ n w v
        + gateVar K n • (matPolyC (θ n).1 *ᵥ formalWVecPoly θ n w)) =
    ((-1 : ℂ) ^ n) • (formalVprod θ (n + 1) *ᵥ vecC w)
  rw [coeffVector_add, hconst, hvar, coeffVector_formalWVecPoly_gateTop θ n (by omega)]
  simp [formalVprod_succ, Matrix.mulVec_smul, Matrix.mulVec_mulVec]

theorem coeffVector_formalVisiblePoly_gateTop {K d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) (hnK : n ≤ K) (w : Fin d → ℝ) :
    coeffVector (gateTop K n) (formalVisiblePoly θ n w) =
      ((-1 : ℂ) ^ n) • (formalVprod θ (n + 1) *ᵥ vecC w) := by
  rw [formalVisiblePoly, coeffVector_const_mulVec,
    coeffVector_formalWVecPoly_gateTop θ n hnK]
  simp [formalVprod_succ, Matrix.mulVec_smul, Matrix.mulVec_mulVec]

theorem neg_one_pow_succ_mul_self (n : Nat) :
    ((-1 : ℂ) ^ (n + 1)) * ((-1 : ℂ) ^ n) = -1 := by
  rw [← pow_add]
  have hodd : Odd ((n + 1) + n) := by
    use n
    omega
  exact Odd.neg_one_pow (α := ℂ) hodd

theorem coeff_formalPhiPoly_gateTopSq_succ_raw {K d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) (hnK : n + 1 ≤ K) (w v : Fin d → ℝ) :
    MvPolynomial.coeff (gateTopSq K (n + 1)) (formalPhiPoly θ (n + 1) w v) =
      (((-1 : ℂ) ^ (n + 1)) • (formalVprod θ (n + 1) *ᵥ vecC w)) ⬝ᵥ
        (matC (θ (n + 1)).2 *ᵥ
          (((-1 : ℂ) ^ n) • (formalVprod θ (n + 1) *ᵥ vecC w))) := by
  rw [formalPhiPoly]
  rw [coeff_dotProduct_gateTopSq_of_vectorDegreeLe_one]
  · rw [coeffVector_formalWVecPoly_gateTop θ (n + 1) hnK,
      coeffVector_const_mulVec,
      coeffVector_formalVVecPoly_gateTop_succ θ n hnK]
  · intro j
    exact vectorDegreeLe_formalWVecPoly_one θ (n + 1) j w
  · intro j
    exact matrixDegreeLe_mulVec
      (j := j) (N := 0) (M := 1)
      (matrixDegreeLe_matPolyC j (θ (n + 1)).2)
      (vectorDegreeLe_formalVVecPoly_one θ (n + 1) j w v)

theorem coeff_formalPhiPoly_gateTopSq_succ {K d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) (hnK : n + 1 ≤ K) (w v : Fin d → ℝ) :
    MvPolynomial.coeff (gateTopSq K (n + 1)) (formalPhiPoly θ (n + 1) w v) =
      -((formalVprod θ (n + 1) *ᵥ vecC w) ⬝ᵥ
        (matC (θ (n + 1)).2 *ᵥ (formalVprod θ (n + 1) *ᵥ vecC w))) := by
  rw [coeff_formalPhiPoly_gateTopSq_succ_raw θ n hnK w v]
  simp [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  have hsign : ((-1 : ℂ) ^ n) * ((-1 : ℂ) ^ (n + 1)) = -1 := by
    rw [mul_comm]
    exact neg_one_pow_succ_mul_self n
  rw [← mul_assoc, hsign, neg_one_mul]

/-- The `f_ell` polynomial from the TeX proof: the expected coefficient of the last
gate squared in `formalPhiPoly θ (n + 1)`. -/
noncomputable def formalLastSqCoeffPoly {K d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) (w : Fin d → ℝ) : GatePoly K :=
  -((matPolyC (θ n).1 *ᵥ formalWVecPoly θ n w) ⬝ᵥ
      (matPolyC (θ (n + 1)).2 *ᵥ
        (matPolyC (θ n).1 *ᵥ formalWVecPoly θ n w)))

theorem neg_one_pow_mul_self (n : Nat) :
    ((-1 : ℂ) ^ n) * ((-1 : ℂ) ^ n) = 1 := by
  rw [← pow_add]
  have heven : Even (n + n) := ⟨n, rfl⟩
  exact Even.neg_one_pow (α := ℂ) heven

theorem coeff_formalLastSqCoeffPoly_gateTopSq {K d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) (hnK : n ≤ K) (w : Fin d → ℝ) :
    MvPolynomial.coeff (gateTopSq K n) (formalLastSqCoeffPoly θ n w) =
      -((formalVprod θ (n + 1) *ᵥ vecC w) ⬝ᵥ
        (matC (θ (n + 1)).2 *ᵥ (formalVprod θ (n + 1) *ᵥ vecC w))) := by
  rw [formalLastSqCoeffPoly, MvPolynomial.coeff_neg]
  rw [coeff_dotProduct_gateTopSq_of_vectorDegreeLe_one]
  · rw [coeffVector_const_mulVec, coeffVector_formalWVecPoly_gateTop θ n hnK,
      coeffVector_const_mulVec, coeffVector_const_mulVec,
      coeffVector_formalWVecPoly_gateTop θ n hnK]
    simp [formalVprod_succ, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      smul_dotProduct, dotProduct_smul]
    rw [← mul_assoc, neg_one_pow_mul_self n, one_mul]
  · intro j
    exact matrixDegreeLe_mulVec
      (j := j) (N := 0) (M := 1)
      (matrixDegreeLe_matPolyC j (θ n).1)
      (vectorDegreeLe_formalWVecPoly_one θ n j w)
  · intro j
    have hinner : VectorDegreeLe j 1 (matPolyC (θ n).1 *ᵥ formalWVecPoly θ n w) :=
      matrixDegreeLe_mulVec
        (j := j) (N := 0) (M := 1)
        (matrixDegreeLe_matPolyC j (θ n).1)
        (vectorDegreeLe_formalWVecPoly_one θ n j w)
    exact matrixDegreeLe_mulVec
      (j := j) (N := 0) (M := 1)
      (matrixDegreeLe_matPolyC j (θ (n + 1)).2)
      hinner

/-- Full coefficient-family bridge for the last gate squared in `formalPhiPoly`. -/
theorem coeff_formalPhiPoly_lastSqCoeffPoly_succ {K d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) (hnK : n < K) (w v : Fin d → ℝ) (a : Fin K →₀ Nat) :
    MvPolynomial.coeff (Finsupp.single ⟨n, hnK⟩ 2 + a)
        (formalPhiPoly θ (n + 1) w v) =
      MvPolynomial.coeff a (formalLastSqCoeffPoly θ n w) := by
  classical
  let r : Fin K := ⟨n, hnK⟩
  let z : GatePoly K := gateVar K n
  let Wn : Fin d → GatePoly K := formalWVecPoly θ n w
  let U : Fin d → GatePoly K := matPolyC (θ n).1 *ᵥ Wn
  let S : Fin d → GatePoly K := matPolyC (skipB (θ n).1) *ᵥ Wn
  let T : Fin d → GatePoly K := matPolyC (skipB (θ n).1) *ᵥ formalVVecPoly θ n w v
  let A : Matrix (Fin d) (Fin d) (GatePoly K) := matPolyC (θ (n + 1)).2
  let m : Fin K →₀ Nat := Finsupp.single r 2 + a
  have hm0 : 0 < m r := by
    simp [m]
  have hm1 : 1 < m r := by
    simp [m]
    omega
  have coeff_zero_deg0 {p : GatePoly K}
      (hp : MvPolynomial.degreeOf r p ≤ 0) :
      MvPolynomial.coeff m p = 0 := by
    exact coeff_eq_zero_of_degreeOf_lt (j := r) (m := m) (by omega)
  have coeff_zero_gate_deg0 {p : GatePoly K}
      (hp : MvPolynomial.degreeOf r p ≤ 0) :
      MvPolynomial.coeff m (z * p) = 0 := by
    have hz : MvPolynomial.degreeOf r z ≤ 1 := by
      simpa [z, r] using degreeOf_gateVar_le_one (K := K) r n
    have hmul := MvPolynomial.degreeOf_mul_le r z p
    exact coeff_eq_zero_of_degreeOf_lt (j := r) (m := m) (by omega)
  have hW0 : VectorDegreeLe r 0 Wn := by
    simpa [Wn, r] using vectorDegreeLe_formalWVecPoly_zero_of_le θ n r w (by rfl)
  have hV0 : VectorDegreeLe r 0 (formalVVecPoly θ n w v) := by
    simpa [r] using vectorDegreeLe_formalVVecPoly_zero_of_le θ n r w v (by rfl)
  have hU0 : VectorDegreeLe r 0 U := by
    exact matrixDegreeLe_mulVec
      (j := r) (N := 0) (M := 0)
      (matrixDegreeLe_matPolyC r (θ n).1) hW0
  have hS0 : VectorDegreeLe r 0 S := by
    exact matrixDegreeLe_mulVec
      (j := r) (N := 0) (M := 0)
      (matrixDegreeLe_matPolyC r (skipB (θ n).1)) hW0
  have hT0 : VectorDegreeLe r 0 T := by
    exact matrixDegreeLe_mulVec
      (j := r) (N := 0) (M := 0)
      (matrixDegreeLe_matPolyC r (skipB (θ n).1)) hV0
  have hAU0 : VectorDegreeLe r 0 (A *ᵥ U) := by
    exact matrixDegreeLe_mulVec
      (j := r) (N := 0) (M := 0)
      (matrixDegreeLe_matPolyC r (θ (n + 1)).2) hU0
  have hAT0 : VectorDegreeLe r 0 (A *ᵥ T) := by
    exact matrixDegreeLe_mulVec
      (j := r) (N := 0) (M := 0)
      (matrixDegreeLe_matPolyC r (θ (n + 1)).2) hT0
  have hS_AT0 : MvPolynomial.degreeOf r (S ⬝ᵥ (A *ᵥ T)) ≤ 0 := by
    simpa using degreeOf_dotProduct_le (j := r) (N := 0) (M := 0) hS0 hAT0
  have hS_AU0 : MvPolynomial.degreeOf r (S ⬝ᵥ (A *ᵥ U)) ≤ 0 := by
    simpa using degreeOf_dotProduct_le (j := r) (N := 0) (M := 0) hS0 hAU0
  have hU_AT0 : MvPolynomial.degreeOf r (U ⬝ᵥ (A *ᵥ T)) ≤ 0 := by
    simpa using degreeOf_dotProduct_le (j := r) (N := 0) (M := 0) hU0 hAT0
  have hWsucc :
      formalWVecPoly θ (n + 1) w = S - z • U := by
    calc
      formalWVecPoly θ (n + 1) w = formalFactorPoly θ n *ᵥ Wn := by
        change (formalFactorPoly θ n * formalWPoly θ n) *ᵥ vecPolyC w =
          formalFactorPoly θ n *ᵥ Wn
        simp [Wn, formalWVecPoly, Matrix.mulVec_mulVec]
      _ = (matPolyC (skipB (θ n).1) - z • matPolyC (θ n).1) *ᵥ Wn := by
        simp [formalFactorPoly, z]
      _ = matPolyC (skipB (θ n).1) *ᵥ Wn - (z • matPolyC (θ n).1) *ᵥ Wn := by
        rw [Matrix.sub_mulVec]
      _ = S - z • U := by
        simp [S, U, Matrix.smul_mulVec]
  have hVsucc :
      formalVVecPoly θ (n + 1) w v = T + z • U := by
    rfl
  have hphi :
      formalPhiPoly θ (n + 1) w v =
        S ⬝ᵥ (A *ᵥ T) + z * (S ⬝ᵥ (A *ᵥ U))
          - z * (U ⬝ᵥ (A *ᵥ T))
          - z * (z * (U ⬝ᵥ (A *ᵥ U))) := by
    rw [formalPhiPoly, hWsucc, hVsucc]
    simp [A, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, sub_dotProduct,
      smul_dotProduct, dotProduct_smul]
    ring
  rw [hphi, MvPolynomial.coeff_sub, MvPolynomial.coeff_sub,
    MvPolynomial.coeff_add]
  rw [coeff_zero_deg0 hS_AT0, coeff_zero_gate_deg0 hS_AU0,
    coeff_zero_gate_deg0 hU_AT0]
  rw [show MvPolynomial.coeff m (z * (z * (U ⬝ᵥ (A *ᵥ U)))) =
      MvPolynomial.coeff a (U ⬝ᵥ (A *ᵥ U)) by
    simpa [m, z, r] using
      coeff_gateVar_sq_mul (K := K) (n := n) hnK a (U ⬝ᵥ (A *ᵥ U))]
  simp [formalLastSqCoeffPoly, U, A, Wn]

end TransformerIdentifiability.NLayer
