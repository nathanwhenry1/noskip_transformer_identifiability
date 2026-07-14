import AnyLayerIdentifiabilityProof.NLayer.IDL.CascadeCurveRigidity

set_option autoImplicit false

open Matrix

namespace TransformerIdentifiability.NLayer

/-!
# The zero branch of `lem:cascade` — the `γ ≡ 0` matrix-algebra core (`prop:trichotomy`, Case 2)

This file formalizes the **pure linear-algebra heart** of the unprimed zero branch of the
trichotomy, i.e. the `K2`/`K3` impossibility analysis in the proof of
`prop:trichotomy` (`n_layer_proof.tex`, lines 2392–2454).

When `Λ_ℓ ≡ 0` on `𝒰₀`, `lem:cascade`(b) produces a degree-`≤ 1` polynomial
`γ(z) = γ₀ + γ₁ z` together with the two matrix identities
```
(♥)   (B₁ - z V₁)ᵀ Y = γ(z) A₁,      Y := (Γ^{(ℓ-1)})ᵀ A_ℓ B_{ℓ-1:1},
(♣)   Sym[(B₁ - z V₁)ᵀ (Γ^{(ℓ-1)})ᵀ A_ℓ T_{ℓ-1}(z)] = 0,
```
identically in `z`, where
`T_{ℓ-1}(z) = z B_{ℓ-1:2} V₁ + Q̃ (B₁ - z V₁)` and
`Q̃ = Σ_{j=2}^{ℓ-1} ς_j B_{ℓ-1:j+1} V_j Γ^{(j-1)}`.

Matching the affine coefficients of `(♥)` gives the two facts the TeX calls `(c0)`, `(c1)`:
```
(c0)   B₁ᵀ Y = γ₀ A₁,        (c1)   -V₁ᵀ Y = γ₁ A₁.
```

`gammaCoeffs_eq_zero_of_cascadeZeroBranch` takes `(c0)`, `(c1)`, `(♣)` together with the
genericity inputs `det A₁ ≠ 0`, `Sym A₁ ≠ 0` (clause `(G1)`) and `V₁ ≠ 0`
(`cor:depth`), the residual structure `B₁ = I + V₁`, and the defining shape
`Y = ((Γ^{(ℓ-1)})ᵀ A_ℓ B_{ℓ-1:2}) · B₁`, and concludes `γ₀ = 0 ∧ γ₁ = 0`, i.e. `γ ≡ 0`.

The argument is exactly TeX's:
* **K2** (`γ₁ = 0, γ₀ ≠ 0`): `(c1)` gives `V₁ᵀ Y = 0`; `(c0)` + `det A₁ ≠ 0` make `Y`
  invertible, so `V₁ = 0`, contradicting `cor:depth`.
* **K3** (`γ₁ ≠ 0`): `(c1)` makes `V₁, Y` invertible; if `γ₀ = 0` then `B₁ = 0`, forcing
  `Y = 0`, impossible; so `γ₀ ≠ 0` and `V₁ = c B₁` with `c = -γ₁/γ₀ ≠ 0`. With
  `B₁ = I + V₁` this yields the scalars `V₁ = ν I`, `B₁ = (1+ν) I`, `ν ≠ 0`, `1+ν ≠ 0`.
  Feeding these into `(♣)` (evaluated at the two arguments `z = 0` and `z = 1`) gives
  `Sym(P B_{ℓ-1:2}) = 0`, while `(c0)` reads `(1+ν)² P B_{ℓ-1:2} = γ₀ A₁`, whence
  `Sym A₁ = 0`, contradicting `(G1)`.

`P` abbreviates `(Γ^{(ℓ-1)})ᵀ A_ℓ` throughout; integration with `SaturationMatching`'s
`CascadeCurveRigidityData` (deriving `(♥)`/`(♣)` from the curve identity and concluding
`γ ≡ 0`) is the next step.
-/

/-- The symmetric part is additive: `Sym (M + N) = Sym M + Sym N`. -/
theorem symPart_add {d : Nat} (M N : Matrix (Fin d) (Fin d) ℝ) :
    symPart (M + N) = symPart M + symPart N := by
  ext i j
  simp only [symPart, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply,
    smul_eq_mul]
  ring

/-- The symmetric part is `ℝ`-linear in the scalar: `Sym (c • M) = c • Sym M`. -/
theorem symPart_smul {d : Nat} (c : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    symPart (c • M) = c • symPart M := by
  ext i j
  simp only [symPart, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply,
    smul_eq_mul]
  ring

/-- **`prop:trichotomy`, Case 2 (`Λ_ℓ ≡ 0`): the matrix-algebra core.**

From the matched affine coefficients `(c0)`/`(c1)` of `(♥)`, the symmetric identity `(♣)`,
and the genericity inputs (`det A₁ ≠ 0`, `Sym A₁ ≠ 0`, `V₁ ≠ 0`), with the residual
structure `B₁ = I + V₁` and `Y = (P B_{ℓ-1:2}) B₁` (`P = (Γ^{(ℓ-1)})ᵀ A_ℓ`), the
degree-`≤ 1` polynomial `γ = γ₀ + γ₁ z` of `lem:cascade`(b) must vanish identically. -/
theorem gammaCoeffs_eq_zero_of_cascadeZeroBranch {d : Nat} (hd : 0 < d)
    (A1 V1 B1 P Bsub Qt Y : Matrix (Fin d) (Fin d) ℝ) (γ₀ γ₁ : ℝ)
    (hB1 : B1 = 1 + V1)
    (hY : Y = P * Bsub * B1)
    (hc0 : B1ᵀ * Y = γ₀ • A1)
    (hc1 : V1ᵀ * Y = (-γ₁) • A1)
    (hclub : ∀ z : ℝ,
      symPart ((B1 - z • V1)ᵀ * P * (z • (Bsub * V1) + Qt * (B1 - z • V1))) = 0)
    (hA1det : A1.det ≠ 0)
    (hsymA1 : symPart A1 ≠ 0)
    (hV1 : V1 ≠ 0) :
    γ₀ = 0 ∧ γ₁ = 0 := by
  -- The identity matrix is nonzero because `0 < d`.
  have hone : (1 : Matrix (Fin d) (Fin d) ℝ) ≠ 0 := by
    intro h
    have := congrFun (congrFun h ⟨0, hd⟩) ⟨0, hd⟩
    simp only [Matrix.one_apply_eq, Matrix.zero_apply] at this
    exact one_ne_zero this
  -- ## Step A: `γ₁ = 0` (the case `γ₁ ≠ 0`, "K3", is impossible).
  have hγ1 : γ₁ = 0 := by
    by_contra hγ1
    -- `(c1)`: `det (V₁ᵀ Y) = (-γ₁)^d det A₁ ≠ 0`, so `Y` is invertible.
    have hdetY : Y.det ≠ 0 := by
      have key : V1ᵀ.det * Y.det = (-γ₁) ^ d * A1.det := by
        rw [← Matrix.det_mul, hc1, Matrix.det_smul, Fintype.card_fin]
      intro h0
      rw [h0, mul_zero] at key
      exact (mul_ne_zero (pow_ne_zero d (neg_ne_zero.mpr hγ1)) hA1det) key.symm
    have hYinv : Y * Y⁻¹ = 1 := Matrix.mul_nonsing_inv Y (Ne.isUnit hdetY)
    -- `γ₀ ≠ 0`: otherwise `(c0)` gives `B₁ᵀ Y = 0`, so `B₁ = 0`, so `Y = 0`.
    have hγ0 : γ₀ ≠ 0 := by
      intro hγ0z
      have hB1TY0 : B1ᵀ * Y = 0 := by rw [hc0, hγ0z, zero_smul]
      have hB1T0 : B1ᵀ = 0 := by
        calc B1ᵀ = B1ᵀ * (Y * Y⁻¹) := by rw [hYinv, Matrix.mul_one]
          _ = (B1ᵀ * Y) * Y⁻¹ := by rw [← Matrix.mul_assoc]
          _ = 0 := by rw [hB1TY0, Matrix.zero_mul]
      have hB10 : B1 = 0 := by
        have h := congrArg Matrix.transpose hB1T0
        rwa [Matrix.transpose_transpose, Matrix.transpose_zero] at h
      have hY0 : Y = 0 := by rw [hY, hB10, Matrix.mul_zero]
      rw [hY0] at hdetY
      exact hdetY (Matrix.det_zero ⟨⟨0, hd⟩⟩)
    -- `V₁ = c • B₁` with `c = -γ₁/γ₀ ≠ 0`.
    set c : ℝ := -γ₁ / γ₀ with hc_def
    have hc_ne : c ≠ 0 := div_ne_zero (neg_ne_zero.mpr hγ1) hγ0
    have hkey : (V1ᵀ - c • B1ᵀ) * Y = 0 := by
      rw [sub_mul, hc1, Matrix.smul_mul, hc0, smul_smul]
      rw [show c * γ₀ = -γ₁ by rw [hc_def]; field_simp]
      rw [sub_self]
    have hsub0 : V1ᵀ - c • B1ᵀ = 0 := by
      calc V1ᵀ - c • B1ᵀ = (V1ᵀ - c • B1ᵀ) * (Y * Y⁻¹) := by rw [hYinv, Matrix.mul_one]
        _ = ((V1ᵀ - c • B1ᵀ) * Y) * Y⁻¹ := by rw [← Matrix.mul_assoc]
        _ = 0 := by rw [hkey, Matrix.zero_mul]
    have hV1Teq : V1ᵀ = c • B1ᵀ := sub_eq_zero.mp hsub0
    have hV1cB1 : V1 = c • B1 := by
      have h := congrArg Matrix.transpose hV1Teq
      rwa [Matrix.transpose_transpose, Matrix.transpose_smul, Matrix.transpose_transpose] at h
    -- `(1 - c) • V₁ = c • I`.
    have hrel : (1 - c) • V1 = c • (1 : Matrix (Fin d) (Fin d) ℝ) := by
      have hexp : V1 = c • (1 : Matrix (Fin d) (Fin d) ℝ) + c • V1 := by
        conv_lhs => rw [hV1cB1, hB1]
        rw [smul_add]
      rw [sub_smul, one_smul, sub_eq_iff_eq_add]
      exact hexp
    have hc1ne : (1 : ℝ) - c ≠ 0 := by
      intro hcc
      rw [hcc, zero_smul] at hrel
      rcases smul_eq_zero.mp hrel.symm with h | h
      · exact hc_ne h
      · exact hone h
    -- Hence the scalars `V₁ = ν I`, `B₁ = (1+ν) I`.
    have hV1ν : V1 = (c / (1 - c)) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
      have h := congrArg (fun M => (1 - c)⁻¹ • M) hrel
      simp only at h
      rw [smul_smul, inv_mul_cancel₀ hc1ne, one_smul] at h
      rw [h, smul_smul]
      congr 1
      rw [div_eq_inv_mul]
    set ν : ℝ := c / (1 - c) with hν_def
    have hν_ne : ν ≠ 0 := div_ne_zero hc_ne hc1ne
    have hsum_ne : (1 : ℝ) + ν ≠ 0 := by
      have hval : (1 : ℝ) + ν = (1 - c)⁻¹ := by rw [hν_def]; field_simp; ring
      rw [hval]; exact inv_ne_zero hc1ne
    have hB1ν : B1 = (1 + ν) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
      rw [hB1, hV1ν, add_smul, one_smul]
    -- `(♣)` at `z = 0` gives `Sym (P Q̃) = 0`.
    have hS2 : symPart (P * Qt) = 0 := by
      have hz0 := hclub 0
      simp only [zero_smul, sub_zero, zero_add] at hz0
      rw [hB1ν,
        show (((1 + ν) • (1 : Matrix (Fin d) (Fin d) ℝ))ᵀ * P *
              (Qt * ((1 + ν) • (1 : Matrix (Fin d) (Fin d) ℝ))))
            = ((1 + ν) * (1 + ν)) • (P * Qt) by
          simp only [Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul,
            Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul],
        symPart_smul] at hz0
      rcases smul_eq_zero.mp hz0 with h | h
      · exact absurd (mul_self_eq_zero.mp h) hsum_ne
      · exact h
    -- `(♣)` at `z = 1` then gives `Sym (P B_{ℓ-1:2}) = 0`.
    have hS1 : symPart (P * Bsub) = 0 := by
      have hz1 := hclub 1
      simp only [one_smul] at hz1
      rw [hB1ν, hV1ν,
        show (((1 + ν) • (1 : Matrix (Fin d) (Fin d) ℝ)
                - (c / (1 - c)) • (1 : Matrix (Fin d) (Fin d) ℝ))ᵀ * P *
              (Bsub * ((c / (1 - c)) • (1 : Matrix (Fin d) (Fin d) ℝ))
                + Qt * ((1 + ν) • (1 : Matrix (Fin d) (Fin d) ℝ)
                  - (c / (1 - c)) • (1 : Matrix (Fin d) (Fin d) ℝ))))
            = ν • (P * Bsub) + (P * Qt) by
          have hb : ((1 + ν) • (1 : Matrix (Fin d) (Fin d) ℝ)
              - (c / (1 - c)) • (1 : Matrix (Fin d) (Fin d) ℝ))
              = (1 : Matrix (Fin d) (Fin d) ℝ) := by
            rw [← hν_def, ← sub_smul, show (1 + ν) - ν = (1 : ℝ) by ring, one_smul]
          rw [← hν_def, hb]
          simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_add, Matrix.mul_smul,
            Matrix.mul_one],
        symPart_add, symPart_smul, hS2, add_zero] at hz1
      rcases smul_eq_zero.mp hz1 with h | h
      · exact absurd h hν_ne
      · exact h
    -- `(c0)` reads `(1+ν)² (P B_{ℓ-1:2}) = γ₀ A₁`; symmetrising kills `Sym A₁`.
    have hfinal : ((1 + ν) * (1 + ν)) • (P * Bsub) = γ₀ • A1 := by
      have h := hc0
      rw [hY, hB1ν] at h
      rw [show ((1 + ν) • (1 : Matrix (Fin d) (Fin d) ℝ))ᵀ
            * (P * Bsub * ((1 + ν) • (1 : Matrix (Fin d) (Fin d) ℝ)))
            = ((1 + ν) * (1 + ν)) • (P * Bsub) by
          simp only [Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul,
            Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul]] at h
      exact h
    have hcontra : symPart A1 = 0 := by
      have h := congrArg symPart hfinal
      rw [symPart_smul, symPart_smul, hS1, smul_zero] at h
      rcases smul_eq_zero.mp h.symm with h' | h'
      · exact absurd h' hγ0
      · exact h'
    exact hsymA1 hcontra
  -- ## Step B: `γ₀ = 0` (the case `γ₁ = 0, γ₀ ≠ 0`, "K2", is impossible).
  refine ⟨?_, hγ1⟩
  by_contra hγ0
  -- `(c0)`: `det (B₁ᵀ Y) = γ₀^d det A₁ ≠ 0`, so `Y` is invertible.
  have hdetY : Y.det ≠ 0 := by
    have key : B1ᵀ.det * Y.det = γ₀ ^ d * A1.det := by
      rw [← Matrix.det_mul, hc0, Matrix.det_smul, Fintype.card_fin]
    intro h0
    rw [h0, mul_zero] at key
    exact (mul_ne_zero (pow_ne_zero d hγ0) hA1det) key.symm
  have hYinv : Y * Y⁻¹ = 1 := Matrix.mul_nonsing_inv Y (Ne.isUnit hdetY)
  -- `(c1)` with `γ₁ = 0`: `V₁ᵀ Y = 0`, so `V₁ = 0`.
  have hV1TY0 : V1ᵀ * Y = 0 := by rw [hc1, hγ1, neg_zero, zero_smul]
  have hV1T0 : V1ᵀ = 0 := by
    calc V1ᵀ = V1ᵀ * (Y * Y⁻¹) := by rw [hYinv, Matrix.mul_one]
      _ = (V1ᵀ * Y) * Y⁻¹ := by rw [← Matrix.mul_assoc]
      _ = 0 := by rw [hV1TY0, Matrix.zero_mul]
  have hV10 : V1 = 0 := by
    have h := congrArg Matrix.transpose hV1T0
    rwa [Matrix.transpose_transpose, Matrix.transpose_zero] at h
  exact hV1 hV10

/-!
## The bilinear/quadratic split of the curve identity (R3-item-1, first half)

`lem:cascade`(b) produces `CascadeCurveRigidityData`, whose `curve_identity` is the
polynomial identity `eq:curve`
`φ_ℓ(z,ς;w,v) = γ(z)·q(w,v)` identically in `(w,v)`.  Combined with the affine
decomposition `formalPhi_eq_affine` (`lem:phi`(i), `eq:Xspec`)
`φ_ℓ = wᵀ·formalX·v + wᵀ·formalY·w`, separating the genuinely-bilinear part from the
`w`-quadratic part yields the matrix identities `(♥)`/`(♣)` in `formalX`/`formalY` form:
`formalX = γ(z)·A` and `formalY + formalYᵀ = 0`.  (Identifying `formalX` with
`(B₁−zV₁)ᵀ·Y` via head-peeling, and then feeding `(c0)`/`(c1)`/`(♣)` into
`gammaCoeffs_eq_zero_of_cascadeZeroBranch`, is the remaining half of R3-item-1.)
-/

/-- `vecC` of the zero vector is zero. -/
@[simp] theorem vecC_zero {d : Nat} : vecC (0 : Fin d → ℝ) = 0 := by
  funext i; simp [vecC]

/-- `vecC` is additive. -/
theorem vecC_add {d : Nat} (w w' : Fin d → ℝ) : vecC (w + w') = vecC w + vecC w' := by
  funext i; simp [vecC, Pi.add_apply, Complex.ofReal_add]

/-- `vecC` of a real coordinate indicator is the complex coordinate indicator. -/
theorem vecC_single {d : Nat} (i : Fin d) :
    vecC (Pi.single i (1 : ℝ)) = Pi.single i (1 : ℂ) := by
  funext k
  by_cases h : k = i <;> simp [vecC, Pi.single_apply, h]

/-- The complex bilinear form of `matC A` on real vectors is `matrixBilin A` coerced. -/
theorem vecC_matC_bilin {d : Nat} (A : Matrix (Fin d) (Fin d) ℝ) (w v : Fin d → ℝ) :
    vecC w ⬝ᵥ (matC A *ᵥ vecC v) = (matrixBilin A w v : ℂ) := by
  simp [matrixBilin, matC, vecC, Matrix.mulVec, dotProduct]

/-! ## Real scalar extraction from `matC` identities -/

/-- Reading off a single matrix entry from the bilinear form on coordinate indicators. -/
theorem single_mulVec_single {d : Nat} (Y : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    Pi.single i (1 : ℂ) ⬝ᵥ (Y *ᵥ Pi.single j 1) = Y i j := by
  classical
  simp

/-- A complex matrix is determined by its bilinear form on real coordinate probes. -/
theorem complexMatrix_eq_of_real_bilin {d : Nat} {X X' : Matrix (Fin d) (Fin d) ℂ}
    (h : ∀ w v : Fin d → ℝ, vecC w ⬝ᵥ (X *ᵥ vecC v) = vecC w ⬝ᵥ (X' *ᵥ vecC v)) :
    X = X' := by
  ext i j
  have hij := h (Pi.single i 1) (Pi.single j 1)
  simp only [vecC_single, single_mulVec_single] at hij
  exact hij

/-- A complex quadratic form vanishing on all real vectors has zero symmetric part
(`Y + Yᵀ = 0`); this is the polarization step behind `(♣)`. -/
theorem complexQuadratic_symPart_zero {d : Nat} (Y : Matrix (Fin d) (Fin d) ℂ)
    (h : ∀ w : Fin d → ℝ, vecC w ⬝ᵥ (Y *ᵥ vecC w) = 0) :
    Y + Yᵀ = 0 := by
  ext i j
  simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.zero_apply]
  have hii := h (Pi.single i 1)
  have hjj := h (Pi.single j 1)
  have hij := h (Pi.single i 1 + Pi.single j 1)
  simp only [vecC_single, single_mulVec_single] at hii hjj
  simp only [vecC_add, vecC_single, Matrix.mulVec_add, add_dotProduct,
    dotProduct_add, single_mulVec_single] at hij
  linear_combination hij - hii - hjj

/-- **Bilinear/quadratic separation.** If a sum of a bilinear form (in `X`) and a
`w`-quadratic form (in `Y`) equals `g` times the bilinear form of `M`, identically on
real probes, then `X = g • M` and `Y` is antisymmetric. -/
theorem bilin_quadratic_separation {d : Nat}
    (X Y M : Matrix (Fin d) (Fin d) ℂ) (g : ℂ)
    (h : ∀ w v : Fin d → ℝ,
      vecC w ⬝ᵥ (X *ᵥ vecC v) + vecC w ⬝ᵥ (Y *ᵥ vecC w)
        = g * (vecC w ⬝ᵥ (M *ᵥ vecC v))) :
    X = g • M ∧ Y + Yᵀ = 0 := by
  have hq : ∀ w : Fin d → ℝ, vecC w ⬝ᵥ (Y *ᵥ vecC w) = 0 := by
    intro w
    have hw := h w 0
    simp only [vecC_zero, Matrix.mulVec_zero, dotProduct_zero, mul_zero, zero_add] at hw
    exact hw
  have hb : ∀ w v : Fin d → ℝ,
      vecC w ⬝ᵥ (X *ᵥ vecC v) = g * (vecC w ⬝ᵥ (M *ᵥ vecC v)) := by
    intro w v
    have hwv := h w v
    rw [hq w, add_zero] at hwv
    exact hwv
  refine ⟨?_, complexQuadratic_symPart_zero Y hq⟩
  apply complexMatrix_eq_of_real_bilin
  intro w v
  rw [hb w v, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- **R3-item-1 (first half): `(♥)`/`(♣)` in `formalX`/`formalY` form.** From the curve
identity packaged in `CascadeCurveRigidityData`, the affine `v`-coefficient matrix is
`γ(z)·A` and the `w`-quadratic matrix is antisymmetric, for every gate value `z`. -/
theorem cascadeCurveRigidity_formalX_formalY {L d : Nat} {θ : Params L d}
    {A : Matrix (Fin d) (Fin d) ℝ} {level : Nat} {tail : Nat → ℝ}
    (D : CascadeCurveRigidityData θ A level tail) (z : ℂ) :
    formalX (paramStream θ) level (complexGateAssignmentOfTail z tail) = D.gamma z • matC A
      ∧ formalY (paramStream θ) level (complexGateAssignmentOfTail z tail)
          + (formalY (paramStream θ) level (complexGateAssignmentOfTail z tail))ᵀ = 0 := by
  apply bilin_quadratic_separation
  intro w v
  have hcurve := D.curve_identity z (w, v)
  rw [specializedPhi, formalPhi_eq_affine] at hcurve
  rw [vecC_matC_bilin]
  exact hcurve

end TransformerIdentifiability.NLayer
