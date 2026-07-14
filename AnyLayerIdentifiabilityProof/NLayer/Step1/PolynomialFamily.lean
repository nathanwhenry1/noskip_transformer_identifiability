import AnyLayerIdentifiabilityProof.NLayer.Step1.OStar
import AnyLayerIdentifiabilityProof.NLayer.Step1.NestedLargeness

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer

open Matrix

/-!
# Step 1 polynomial family

Owner shard for packaging `f_2, ..., f_L, g`, proving their dominant top coefficient
facts under explicit nonzero hypotheses, and connecting them to nested largeness.
-/

/-! ## Concrete family -/

/-- The finite Step 1 family index.  `some n` indexes `f_{n+2}` and `none` indexes the
visible polynomial `g`. -/
abbrev Step1PolynomialIndex (K : Nat) : Type :=
  Option (Fin K)

/-- The complexified scalar whose nonvanishing corresponds to the TeX hypothesis
`kappa_{n+2}(w) != 0`. -/
noncomputable def step1KappaScalar {d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) (w : Fin d → ℝ) : ℂ :=
  (formalVprod θ (n + 1) *ᵥ vecC w) ⬝ᵥ
    (matC (θ (n + 1)).2 *ᵥ (formalVprod θ (n + 1) *ᵥ vecC w))

/-- The displayed top coefficient of `f_{n+2}`. -/
noncomputable def step1LastSqTopCoeff {d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) (w : Fin d → ℝ) : ℂ :=
  -step1KappaScalar θ n w

/-- The visible tail coordinate whose nonvanishing corresponds to
`e_iota^T V'_{L:1} w != 0` when `K = L - 1`. -/
noncomputable def step1VisibleTailCoeff {K d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (iota : Fin d) : ℂ :=
  (formalVprod θ (K + 1) *ᵥ vecC w) iota

/-- The displayed top coefficient of the visible polynomial `g`. -/
noncomputable def step1VisibleTopCoeff {K d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (iota : Fin d) : ℂ :=
  ((-1 : ℂ) ^ K) * step1VisibleTailCoeff (K := K) θ w iota

/-- The polynomial `f_{n+2}` in the common `K`-variable gate ring. -/
noncomputable def step1LastSqCoeffPoly {K d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (n : Fin K) : GatePoly K :=
  formalLastSqCoeffPoly θ (n : Nat) w

/-- The visible scalar polynomial `g = e_iota^T V_L W_{L-1}(z) w` for `K = L - 1`. -/
noncomputable def step1VisiblePoly {K d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (iota : Fin d) : GatePoly K :=
  formalVisiblePoly θ K w iota

/-- The finite family `f_2, ..., f_{K+1}, g`, all viewed in `GatePoly K`. -/
noncomputable def step1PolynomialFamilyPoly {K d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (iota : Fin d) :
    Step1PolynomialIndex K → GatePoly K
  | none => step1VisiblePoly θ w iota
  | some n => step1LastSqCoeffPoly θ w n

/-! ## Coefficient access -/

/-- Coefficient-family bridge specialized to the packaged `f_{n+2}` polynomial. -/
theorem coeff_formalPhiPoly_step1LastSqCoeffPoly_succ {K d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Fin K) (w v : Fin d → ℝ) (a : Fin K →₀ Nat) :
    MvPolynomial.coeff (Finsupp.single n 2 + a)
        (formalPhiPoly θ ((n : Nat) + 1) w v) =
      MvPolynomial.coeff a (step1LastSqCoeffPoly θ w n) := by
  simpa [step1LastSqCoeffPoly] using
    coeff_formalPhiPoly_lastSqCoeffPoly_succ θ (n : Nat) n.isLt w v a

/-- Displayed top coefficient of `f_{n+2}`. -/
theorem coeff_step1LastSqCoeffPoly_gateTopSq {K d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Fin K) (w : Fin d → ℝ) :
    MvPolynomial.coeff (gateTopSq K (n : Nat)) (step1LastSqCoeffPoly θ w n) =
      step1LastSqTopCoeff θ (n : Nat) w := by
  simpa [step1LastSqCoeffPoly, step1LastSqTopCoeff, step1KappaScalar] using
    coeff_formalLastSqCoeffPoly_gateTopSq θ (n : Nat) (Nat.le_of_lt n.isLt) w

/-- The displayed `f_{n+2}` top coefficient is nonzero under the corresponding
`kappa_{n+2}(w) != 0` hypothesis. -/
theorem coeff_step1LastSqCoeffPoly_gateTopSq_ne {K d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Fin K) (w : Fin d → ℝ)
    (hkappa : step1KappaScalar θ (n : Nat) w ≠ 0) :
    MvPolynomial.coeff (gateTopSq K (n : Nat)) (step1LastSqCoeffPoly θ w n) ≠ 0 := by
  rw [coeff_step1LastSqCoeffPoly_gateTopSq, step1LastSqTopCoeff]
  exact neg_ne_zero.mpr hkappa

/-- Displayed top coefficient of the visible polynomial `g`. -/
theorem coeff_step1VisiblePoly_gateTop {K d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (iota : Fin d) :
    MvPolynomial.coeff (gateTop K K) (step1VisiblePoly θ w iota) =
      step1VisibleTopCoeff (K := K) θ w iota := by
  have h :=
    congrFun (coeffVector_formalVisiblePoly_gateTop θ K (Nat.le_refl K) w) iota
  simpa [step1VisiblePoly, step1VisibleTopCoeff, step1VisibleTailCoeff,
    coeffVector, Pi.smul_apply, smul_eq_mul] using h

/-- The displayed visible top coefficient is nonzero under the visible-coordinate
hypothesis `e_iota^T V'_{L:1} w != 0` for `K = L - 1`. -/
theorem coeff_step1VisiblePoly_gateTop_ne {K d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (iota : Fin d)
    (hvis : step1VisibleTailCoeff (K := K) θ w iota ≠ 0) :
    MvPolynomial.coeff (gateTop K K) (step1VisiblePoly θ w iota) ≠ 0 := by
  rw [coeff_step1VisiblePoly_gateTop, step1VisibleTopCoeff]
  exact mul_ne_zero (pow_ne_zero K (by norm_num : (-1 : ℂ) ≠ 0)) hvis

/-! ## Dominant-top-coefficient access -/

theorem degreeOf_step1LastSqCoeffPoly_le_two {K d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Fin K) (j : Fin K) (w : Fin d → ℝ) :
    MvPolynomial.degreeOf j (step1LastSqCoeffPoly θ w n) ≤ 2 := by
  unfold step1LastSqCoeffPoly formalLastSqCoeffPoly
  rw [MvPolynomial.degreeOf_neg]
  have hU : VectorDegreeLe j 1
      (matPolyC (θ (n : Nat)).1 *ᵥ formalWVecPoly θ (n : Nat) w) := by
    simpa using
      matrixDegreeLe_mulVec
        (j := j) (N := 0) (M := 1)
        (matrixDegreeLe_matPolyC j (θ (n : Nat)).1)
        (vectorDegreeLe_formalWVecPoly_one θ (n : Nat) j w)
  have hAU : VectorDegreeLe j 1
      (matPolyC (θ ((n : Nat) + 1)).2 *ᵥ
        (matPolyC (θ (n : Nat)).1 *ᵥ formalWVecPoly θ (n : Nat) w)) := by
    simpa using
      matrixDegreeLe_mulVec
        (j := j) (N := 0) (M := 1)
        (matrixDegreeLe_matPolyC j (θ ((n : Nat) + 1)).2) hU
  have hdot := degreeOf_dotProduct_le (j := j) (N := 1) (M := 1) hU hAU
  omega

theorem degreeOf_step1LastSqCoeffPoly_eq_zero_of_le {K d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Fin K) {j : Fin K} (w : Fin d → ℝ) (hnj : (n : Nat) ≤ (j : Nat)) :
    MvPolynomial.degreeOf j (step1LastSqCoeffPoly θ w n) = 0 := by
  apply Nat.eq_zero_of_le_zero
  unfold step1LastSqCoeffPoly formalLastSqCoeffPoly
  rw [MvPolynomial.degreeOf_neg]
  have hU : VectorDegreeLe j 0
      (matPolyC (θ (n : Nat)).1 *ᵥ formalWVecPoly θ (n : Nat) w) :=
    matrixDegreeLe_mulVec
      (j := j) (N := 0) (M := 0)
      (matrixDegreeLe_matPolyC j (θ (n : Nat)).1)
      (vectorDegreeLe_formalWVecPoly_zero_of_le θ (n : Nat) j w hnj)
  have hAU : VectorDegreeLe j 0
      (matPolyC (θ ((n : Nat) + 1)).2 *ᵥ
        (matPolyC (θ (n : Nat)).1 *ᵥ formalWVecPoly θ (n : Nat) w)) :=
    matrixDegreeLe_mulVec
      (j := j) (N := 0) (M := 0)
      (matrixDegreeLe_matPolyC j (θ ((n : Nat) + 1)).2) hU
  simpa using degreeOf_dotProduct_le (j := j) (N := 0) (M := 0) hU hAU

theorem topMonomial_step1LastSqCoeffPoly_of_coeff_ne {K d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Fin K) (w : Fin d → ℝ)
    (hcoeff :
      MvPolynomial.coeff (gateTopSq K (n : Nat)) (step1LastSqCoeffPoly θ w n) ≠ 0) :
    topMonomial (step1LastSqCoeffPoly θ w n) = gateTopSq K (n : Nat) := by
  ext j
  rw [topMonomial_apply]
  by_cases hjn : (j : Nat) < (n : Nat)
  · have hdeg_le := degreeOf_step1LastSqCoeffPoly_le_two θ n j w
    have hmem :
        gateTopSq K (n : Nat) ∈ (step1LastSqCoeffPoly θ w n).support :=
      MvPolynomial.mem_support_iff.mpr hcoeff
    have hdeg_ge := MvPolynomial.le_degreeOf_of_mem_support j hmem
    have hgate : gateTopSq K (n : Nat) j = 2 := gateTopSq_apply_lt hjn
    have hge : 2 ≤ MvPolynomial.degreeOf j (step1LastSqCoeffPoly θ w n) := by
      simpa [hgate] using hdeg_ge
    have hdeg :
        MvPolynomial.degreeOf j (step1LastSqCoeffPoly θ w n) = 2 :=
      le_antisymm hdeg_le hge
    simp [hdeg, hgate]
  · have hnj : (n : Nat) ≤ (j : Nat) := not_lt.mp hjn
    have hdeg := degreeOf_step1LastSqCoeffPoly_eq_zero_of_le θ n w hnj
    have hgate : gateTopSq K (n : Nat) j = 0 := gateTopSq_apply_ge hnj
    simp [hdeg, hgate]

theorem hasDominantTopCoeff_step1LastSqCoeffPoly {K d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Fin K) (w : Fin d → ℝ)
    (hkappa : step1KappaScalar θ (n : Nat) w ≠ 0) :
    HasDominantTopCoeff (step1LastSqCoeffPoly θ w n) := by
  have hcoeff := coeff_step1LastSqCoeffPoly_gateTopSq_ne θ n w hkappa
  unfold HasDominantTopCoeff
  rw [topMonomial_step1LastSqCoeffPoly_of_coeff_ne θ n w hcoeff]
  exact hcoeff

theorem topMonomial_step1VisiblePoly_of_coeff_ne {K d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (iota : Fin d)
    (hcoeff : MvPolynomial.coeff (gateTop K K) (step1VisiblePoly θ w iota) ≠ 0) :
    topMonomial (step1VisiblePoly (K := K) θ w iota) = gateTop K K := by
  ext j
  rw [topMonomial_apply]
  have hdeg_le := degreeOf_formalVisiblePoly_le_one θ K j w iota
  have hmem : gateTop K K ∈ (step1VisiblePoly θ w iota).support :=
    MvPolynomial.mem_support_iff.mpr hcoeff
  have hdeg_ge := MvPolynomial.le_degreeOf_of_mem_support j hmem
  have hgate : gateTop K K j = 1 := gateTop_apply_lt j.isLt
  have hge : 1 ≤ MvPolynomial.degreeOf j (step1VisiblePoly θ w iota) := by
    simpa [step1VisiblePoly, hgate] using hdeg_ge
  have hdeg : MvPolynomial.degreeOf j (step1VisiblePoly θ w iota) = 1 :=
    le_antisymm hdeg_le hge
  simpa [step1VisiblePoly, hdeg, hgate]

theorem hasDominantTopCoeff_step1VisiblePoly {K d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (iota : Fin d)
    (hvis : step1VisibleTailCoeff (K := K) θ w iota ≠ 0) :
    HasDominantTopCoeff (step1VisiblePoly (K := K) θ w iota) := by
  have hcoeff := coeff_step1VisiblePoly_gateTop_ne (K := K) θ w iota hvis
  unfold HasDominantTopCoeff
  rw [topMonomial_step1VisiblePoly_of_coeff_ne θ w iota hcoeff]
  exact hcoeff

/-! ## Assumption package and nested-largeness/DTC wrapper -/

/-- Local Step 1 nonzero assumptions for the packaged family in `K` variables. -/
structure Step1PolynomialFamilyAssumptions (K d : Nat)
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (iota : Fin d) : Prop where
  kappa_ne : ∀ n : Fin K, step1KappaScalar θ (n : Nat) w ≠ 0
  visible_ne : step1VisibleTailCoeff (K := K) θ w iota ≠ 0

/-- Depth-indexed synonym for the Step 1 nonzero assumptions with `K = L - 1`. -/
abbrev Step1PolynomialFamilyAssumptionsForDepth (L d : Nat)
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (iota : Fin d) : Prop :=
  Step1PolynomialFamilyAssumptions (L - 1) d θ w iota

/-! ## Fixed-probe `O_star` bridge -/

theorem matC_one {d : Nat} :
    matC (1 : Matrix (Fin d) (Fin d) ℝ) = 1 := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [matC]
  · simp [matC, Matrix.one_apply_ne h]

theorem matC_mul {d : Nat} (A B : Matrix (Fin d) (Fin d) ℝ) :
    matC (A * B) = matC A * matC B := by
  ext i j
  simp [matC, Matrix.mul_apply]

theorem matC_mulVec_vecC {d : Nat} (A : Matrix (Fin d) (Fin d) ℝ)
    (x : Fin d → ℝ) :
    matC A *ᵥ vecC x = vecC (A *ᵥ x) := by
  ext i
  simp [matC, vecC, Matrix.mulVec, dotProduct]

theorem formalVprod_eq_matC_realVprod {d : Nat} (θ : LayerStream d) :
    ∀ n : Nat, formalVprod θ n = matC (realVprod θ n) := by
  intro n
  induction n with
  | zero =>
      simp [formalVprod, realVprod, matC_one]
  | succ n ih =>
      rw [formalVprod_succ, realVprod_succ, matC_mul, ih]

theorem vecC_dotProduct_matC_mulVec {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (x y : Fin d → ℝ) :
    dotProduct (vecC x) (matC A *ᵥ vecC y) =
      ((@dotProduct (Fin d) ℝ _ _ _ x (A.mulVec y)) : ℂ) := by
  simp [matC, vecC, Matrix.mulVec, dotProduct]

theorem dotProduct_mulVec_left {d : Nat}
    (P : Matrix (Fin d) (Fin d) ℝ) (x y : Fin d → ℝ) :
    dotProduct (P *ᵥ x) y = dotProduct x (Pᵀ *ᵥ y) := by
  change (∑ i : Fin d, (∑ j : Fin d, P i j * x j) * y i) =
    ∑ j : Fin d, x j * (∑ i : Fin d, Pᵀ j i * y i)
  simp only [Matrix.transpose_apply]
  calc
    (∑ i : Fin d, (∑ j : Fin d, P i j * x j) * y i)
        = ∑ i : Fin d, ∑ j : Fin d, (P i j * x j) * y i := by
          simp [Finset.sum_mul]
    _ = ∑ j : Fin d, ∑ i : Fin d, (P i j * x j) * y i := by
          exact Finset.sum_comm
    _ = ∑ j : Fin d, ∑ i : Fin d, x j * (P i j * y i) := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          refine Finset.sum_congr rfl ?_
          intro i _hi
          ring
    _ = ∑ j : Fin d, x j * ∑ i : Fin d, P i j * y i := by
          simp [Finset.mul_sum]

theorem dotProduct_transpose_mulVec_self {d : Nat}
    (M : Matrix (Fin d) (Fin d) ℝ) (w : Fin d → ℝ) :
    dotProduct w (Mᵀ *ᵥ w) = dotProduct w (M *ᵥ w) := by
  change (∑ i : Fin d, w i * (∑ j : Fin d, Mᵀ i j * w j)) =
    ∑ i : Fin d, w i * (∑ j : Fin d, M i j * w j)
  simp only [Matrix.transpose_apply]
  calc
    (∑ i : Fin d, w i * ∑ j : Fin d, M j i * w j)
        = ∑ i : Fin d, ∑ j : Fin d, w i * (M j i * w j) := by
          simp [Finset.mul_sum]
    _ = ∑ j : Fin d, ∑ i : Fin d, w i * (M j i * w j) := by
          exact Finset.sum_comm
    _ = ∑ j : Fin d, ∑ i : Fin d, w j * (M j i * w i) := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          refine Finset.sum_congr rfl ?_
          intro i _hi
          ring
    _ = ∑ j : Fin d, w j * ∑ i : Fin d, M j i * w i := by
          simp [Finset.mul_sum]

theorem matrixBilin_symPart_self {d : Nat}
    (M : Matrix (Fin d) (Fin d) ℝ) (w : Fin d → ℝ) :
    matrixBilin (symPart M) w w = matrixBilin M w w := by
  unfold matrixBilin symPart
  simp [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul,
    dotProduct_transpose_mulVec_self]
  ring

theorem matrixBilin_conj {d : Nat}
    (P A : Matrix (Fin d) (Fin d) ℝ) (w : Fin d → ℝ) :
    dotProduct (P *ᵥ w) (A *ᵥ (P *ᵥ w)) = matrixBilin (Pᵀ * A * P) w w := by
  unfold matrixBilin
  rw [dotProduct_mulVec_left]
  simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem step1KappaScalar_eq_kappaIndex {d : Nat}
    (θ : LayerStream d) (n : Nat) (w : Fin d → ℝ) :
    step1KappaScalar θ n w = (kappaIndex θ n w : ℂ) := by
  unfold step1KappaScalar kappaIndex kappaMatrix
  rw [formalVprod_eq_matC_realVprod θ (n + 1)]
  rw [matC_mulVec_vecC]
  rw [vecC_dotProduct_matC_mulVec]
  rw [matrixBilin_symPart_self]
  rw [← matrixBilin_conj]

theorem step1KappaScalar_eq_kappaParam_add_two {L d : Nat}
    (θ : Params L d) (n : Nat) (w : Fin d → ℝ) :
    step1KappaScalar (paramStream θ) n w = (kappaParam_j θ (n + 2) w : ℂ) := by
  rw [step1KappaScalar_eq_kappaIndex, kappaParam_j, kappa_j_add_two]

theorem step1KappaScalar_ne_of_kappaParam_ne {L d : Nat}
    {θ : Params L d} {n : Nat} {w : Fin d → ℝ}
    (h : kappaParam_j θ (n + 2) w ≠ 0) :
    step1KappaScalar (paramStream θ) n w ≠ 0 := by
  rw [step1KappaScalar_eq_kappaParam_add_two]
  exact_mod_cast h

theorem step1VisibleTailCoeff_eq_visibleTailCoord {L d : Nat}
    (θ : Params L d) (w : Fin d → ℝ) (iota : Fin d) (hL : 0 < L) :
    step1VisibleTailCoeff (K := L - 1) (paramStream θ) w iota =
      (visibleTailCoord θ w iota : ℂ) := by
  rw [step1VisibleTailCoeff, visibleTailCoord, visibleTailVector]
  have hK : L - 1 + 1 = L := Nat.sub_add_cancel hL
  rw [hK, formalVprod_eq_matC_realVprod (paramStream θ) L, matC_mulVec_vecC]
  simp [vecC]

theorem step1VisibleTailCoeff_ne_of_visibleTailCoord_ne {L d : Nat}
    {θ : Params L d} {w : Fin d → ℝ} {iota : Fin d} (hL : 0 < L)
    (h : visibleTailCoord θ w iota ≠ 0) :
    step1VisibleTailCoeff (K := L - 1) (paramStream θ) w iota ≠ 0 := by
  rw [step1VisibleTailCoeff_eq_visibleTailCoord θ w iota hL]
  exact_mod_cast h

theorem step1PolynomialFamilyAssumptionsForDepth_of_nonzero {L d : Nat}
    {θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ}
    {w : Fin d → ℝ} {iota : Fin d}
    (hkappa : ∀ n : Fin (L - 1), step1KappaScalar θ (n : Nat) w ≠ 0)
    (hvisible : step1VisibleTailCoeff (K := L - 1) θ w iota ≠ 0) :
    Step1PolynomialFamilyAssumptionsForDepth L d θ w iota where
  kappa_ne := hkappa
  visible_ne := hvisible

theorem step1PolynomialFamilyAssumptionsForDepth_of_OStar {L d : Nat}
    {θ' : Params L d} {O : Set (ProbePair d)} {p : ProbePair d} {iota : Fin d}
    (hL : 0 < L) (hp : p ∈ O_star θ' O)
    (hvisible : visibleTailCoord θ' p.1 iota ≠ 0) :
    Step1PolynomialFamilyAssumptionsForDepth L d (paramStream θ') p.1 iota := by
  refine step1PolynomialFamilyAssumptionsForDepth_of_nonzero ?_ ?_
  · intro n
    apply step1KappaScalar_ne_of_kappaParam_ne
    apply O_star_kappa_ne hp
    · omega
    · have hn : (n : Nat) < L - 1 := n.isLt
      omega
  · exact step1VisibleTailCoeff_ne_of_visibleTailCoord_ne hL hvisible

theorem FixedOStarProbe.step1PolynomialFamilyAssumptionsForDepth {r L d : Nat}
    {O : Set (ProbePair d)} {θ θ' : Params L d} (hL : 0 < L)
    (p : FixedOStarProbe r L d O θ θ') :
    Step1PolynomialFamilyAssumptionsForDepth L d (paramStream θ') p.probe.1 p.iota :=
  step1PolynomialFamilyAssumptionsForDepth_of_OStar hL p.mem_O_star p.visible_iota_ne

namespace Step1PolynomialFamilyAssumptions

variable {K d : Nat}
variable {θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ}
variable {w : Fin d → ℝ} {iota : Fin d}

theorem hasDominantTopCoeff_lastSq
    (h : Step1PolynomialFamilyAssumptions K d θ w iota) (n : Fin K) :
    HasDominantTopCoeff (step1LastSqCoeffPoly θ w n) :=
  hasDominantTopCoeff_step1LastSqCoeffPoly θ n w (h.kappa_ne n)

theorem hasDominantTopCoeff_visible
    (h : Step1PolynomialFamilyAssumptions K d θ w iota) :
    HasDominantTopCoeff (step1VisiblePoly (K := K) θ w iota) :=
  hasDominantTopCoeff_step1VisiblePoly θ w iota h.visible_ne

theorem hasDominantTopCoeff_poly
    (h : Step1PolynomialFamilyAssumptions K d θ w iota)
    (a : Step1PolynomialIndex K) :
    HasDominantTopCoeff (step1PolynomialFamilyPoly θ w iota a) := by
  cases a with
  | none => exact h.hasDominantTopCoeff_visible
  | some n => exact h.hasDominantTopCoeff_lastSq n

/-- The packaged family as a `DominantPolynomialFamily`, ready for product and nested
largeness APIs. -/
noncomputable def dominantPolynomialFamily
    (h : Step1PolynomialFamilyAssumptions K d θ w iota) :
    DominantPolynomialFamily (Step1PolynomialIndex K) (Fin K) ℂ where
  poly := step1PolynomialFamilyPoly θ w iota
  hasDominantTopCoeff := h.hasDominantTopCoeff_poly

theorem hasDominantTopCoeff_prod
    (h : Step1PolynomialFamilyAssumptions K d θ w iota)
    (s : Finset (Step1PolynomialIndex K)) :
    HasDominantTopCoeff (∏ a ∈ s, step1PolynomialFamilyPoly θ w iota a) :=
  (h.dominantPolynomialFamily).hasDominantTopCoeff_prod s

end Step1PolynomialFamilyAssumptions

/-! ## The global product `P = f_2 · ⋯ · f_{n+2} · g`

The TeX nested-largeness lemma forms a *single* global product of the whole family and
takes its iterated leading coefficients (`n_layer_proof.tex:1413`).  Here `P` lives in the
common gate ring `GatePoly (n+1) = ℂ[z_0,…,z_n]`, and has a dominant top coefficient by
`HasDominantTopCoeff.prod`.  It feeds `globalLcNestedTailData` to build the tower whose
`leadingCoeff_ne_on_region` is provable from this single DTC. -/

/-- The global product of the whole Step 1 family, in `GatePoly (n+1) = ℂ[z_0,…,z_n]`. -/
noncomputable def step1GlobalProductPoly {d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (iota : Fin d) (n : Nat) : MvPolynomial (Fin (n + 1)) ℂ :=
  ∏ a : Step1PolynomialIndex (n + 1), step1PolynomialFamilyPoly (K := n + 1) θ w iota a

/-- The global product has a dominant top coefficient (TeX `lem:nested`, Step 0). -/
theorem hasDominantTopCoeff_step1GlobalProductPoly {d n : Nat}
    {θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ}
    {w : Fin d → ℝ} {iota : Fin d}
    (h : Step1PolynomialFamilyAssumptions (n + 1) d θ w iota) :
    HasDominantTopCoeff (step1GlobalProductPoly θ w iota n) := by
  simpa [step1GlobalProductPoly] using h.hasDominantTopCoeff_prod Finset.univ

/-! ## Concrete nested-tail data for the propagation polynomials -/

/-- The `m`th actual formal-phi propagation polynomial, viewed in the `m+1` gate
variables used by `PolynomialTailPresentationData`.

Unlike `step1PropagationTailPoly`, this keeps the full
`formalPhiPoly θ (m+1) w v` tower, so the newly peeled last gate has the quadratic
behavior used by the scaled propagation bridge. -/
noncomputable def step1FormalPhiPropagationTailPoly {d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w v : Fin d → ℝ) (m : Nat) : MvPolynomial (Fin (m + 1)) ℂ :=
  formalPhiPoly θ (m + 1) w v

/-- Canonical last-variable tail data for the actual Step 1 formal-phi propagation
polynomial. -/
noncomputable def step1FormalPhiPropagationTailData {d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w v : Fin d → ℝ) (m : Nat) : PolynomialTailPresentationData m :=
  PolynomialTailPresentationData.ofPolynomial
    (step1FormalPhiPropagationTailPoly θ w v m)

/-- The nested-tail family whose `m`th step is the canonical presentation of the actual
`formalPhiPoly θ (m+1) w v`. -/
noncomputable def step1FormalPhiPropagationNestedTailFamily {d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w v : Fin d → ℝ) : NestedTailFamily where
  step m := (step1FormalPhiPropagationTailData θ w v m).presentation

@[simp]
theorem step1FormalPhiPropagationNestedTailFamily_step {d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w v : Fin d → ℝ) (m : Nat) :
    (step1FormalPhiPropagationNestedTailFamily θ w v).step m =
      (step1FormalPhiPropagationTailData θ w v m).presentation :=
  rfl

@[simp]
theorem step1FormalPhiPropagationTailData_poly {d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w v : Fin d → ℝ) (m : Nat) :
    (step1FormalPhiPropagationTailData θ w v m).poly =
      step1FormalPhiPropagationTailPoly θ w v m :=
  rfl

/-- Evaluation of the actual formal-phi nested-tail family step is evaluation of the
corresponding `formalPhiPoly`. -/
theorem step1FormalPhiPropagationNestedTailFamily_evalStep {d m : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w v : Fin d → ℝ) (z : Fin (m + 1) → ℂ) :
    (step1FormalPhiPropagationNestedTailFamily θ w v).evalStep z =
      MvPolynomial.eval z (step1FormalPhiPropagationTailPoly θ w v m) := by
  simpa [NestedTailFamily.evalStep, step1FormalPhiPropagationTailData] using
    PolynomialTailPresentationData.eval_nested
      (step1FormalPhiPropagationTailData θ w v m) z

/-- Evaluation of the actual formal-phi nested-tail step in the zero-padded gate-stream
convention. -/
theorem step1FormalPhiPropagationNestedTailFamily_evalStep_eq_formalPhi {d m : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w v : Fin d → ℝ) (z : Fin (m + 1) → ℂ) :
    (step1FormalPhiPropagationNestedTailFamily θ w v).evalStep z =
      formalPhi θ (m + 1) (extendGate z) w v := by
  rw [step1FormalPhiPropagationNestedTailFamily_evalStep,
    step1FormalPhiPropagationTailPoly, eval_formalPhiPoly]

/-- Polynomial-backed data for the actual Step 1 formal-phi propagation tower. -/
noncomputable def step1FormalPhiPropagationPolynomialNestedTailData {d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w v : Fin d → ℝ) : PolynomialNestedTailData where
  tailData m := step1FormalPhiPropagationTailData θ w v m
  lead_continuous := by
    intro m
    simpa [step1FormalPhiPropagationTailData] using
      continuous_polynomialTailPresentation_lead
        (step1FormalPhiPropagationTailPoly θ w v m)
  lower_continuous := by
    intro m i
    simpa [step1FormalPhiPropagationTailData] using
      continuous_polynomialTailPresentation_lower
        (step1FormalPhiPropagationTailPoly θ w v m) i

@[simp]
theorem step1FormalPhiPropagationPolynomialNestedTailData_tailData {d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w v : Fin d → ℝ) (m : Nat) :
    (step1FormalPhiPropagationPolynomialNestedTailData θ w v).tailData m =
      step1FormalPhiPropagationTailData θ w v m :=
  rfl

@[simp]
theorem step1FormalPhiPropagationPolynomialNestedTailData_toNestedTailFamily {d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w v : Fin d → ℝ) :
    (step1FormalPhiPropagationPolynomialNestedTailData θ w v).toNestedTailFamily =
      step1FormalPhiPropagationNestedTailFamily θ w v :=
  rfl

theorem degreeOf_step1FormalPhiPropagationTailPoly_last_le_two {d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w v : Fin d → ℝ) (m : Nat) :
    MvPolynomial.degreeOf (Fin.last m)
      (step1FormalPhiPropagationTailPoly θ w v m) ≤ 2 := by
  simpa [step1FormalPhiPropagationTailPoly] using
    degreeOf_formalPhiPoly_le_two θ (m + 1) (Fin.last m) w v

theorem coeff_step1FormalPhiPropagationTailPoly_gateTopSq_ne {d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w v : Fin d → ℝ) (m : Nat)
    (hkappa : step1KappaScalar θ m w ≠ 0) :
    MvPolynomial.coeff (gateTopSq (m + 1) (m + 1))
        (step1FormalPhiPropagationTailPoly θ w v m) ≠ 0 := by
  have hcoeff :
      MvPolynomial.coeff (gateTopSq (m + 1) (m + 1))
          (step1FormalPhiPropagationTailPoly θ w v m) =
        -step1KappaScalar θ m w := by
    rw [step1FormalPhiPropagationTailPoly,
      coeff_formalPhiPoly_gateTopSq_succ θ m (by omega)]
    rfl
  rw [hcoeff]
  exact neg_ne_zero.mpr hkappa

theorem degreeOf_step1FormalPhiPropagationTailPoly_last_eq_two {d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w v : Fin d → ℝ) (m : Nat)
    (hkappa : step1KappaScalar θ m w ≠ 0) :
    MvPolynomial.degreeOf (Fin.last m)
      (step1FormalPhiPropagationTailPoly θ w v m) = 2 := by
  have hcoeff :=
    coeff_step1FormalPhiPropagationTailPoly_gateTopSq_ne θ w v m hkappa
  have hmem :
      gateTopSq (m + 1) (m + 1) ∈
        (step1FormalPhiPropagationTailPoly θ w v m).support :=
    MvPolynomial.mem_support_iff.mpr hcoeff
  have hge :=
    MvPolynomial.le_degreeOf_of_mem_support (Fin.last m) hmem
  have hlast :
      gateTopSq (m + 1) (m + 1) (Fin.last m) = 2 := by
    exact gateTopSq_apply_lt (i := Fin.last m) (Nat.lt_succ_self m)
  exact le_antisymm
    (degreeOf_step1FormalPhiPropagationTailPoly_last_le_two θ w v m)
    (by simpa [hlast] using hge)

theorem step1FormalPhiPropagationTailData_degree_eq_two {d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w v : Fin d → ℝ) (m : Nat)
    (hkappa : step1KappaScalar θ m w ≠ 0) :
    (step1FormalPhiPropagationTailData θ w v m).presentation.degree = 2 := by
  change (lastVariablePolynomial
    (step1FormalPhiPropagationTailPoly θ w v m)).natDegree = 2
  unfold lastVariablePolynomial
  rw [MvPolynomial.natDegree_finSuccEquiv]
  have hrename :=
    MvPolynomial.degreeOf_rename_of_injective
      (R := ℂ) (p := step1FormalPhiPropagationTailPoly θ w v m)
      (f := nestedLastToFrontEquiv m)
      (Equiv.injective (nestedLastToFrontEquiv m)) (Fin.last m)
  simpa [degreeOf_step1FormalPhiPropagationTailPoly_last_eq_two θ w v m hkappa]
    using hrename

/-- The `m`th propagation polynomial in the nested tower, namely `f_{m+2}`, viewed in
the `m+1` gate variables used by `PolynomialTailPresentationData`.  The polynomial is
naturally independent of the last variable when `m = 0`, and more generally uses the
same zero-padded gate-polynomial convention as the rest of the Step 1 family. -/
noncomputable def step1PropagationTailPoly {d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (m : Nat) : MvPolynomial (Fin (m + 1)) ℂ :=
  step1LastSqCoeffPoly (K := m + 1) θ w ⟨m, Nat.lt_succ_self m⟩

/-- Canonical last-variable tail data for the Step 1 propagation polynomial `f_{m+2}`. -/
noncomputable def step1PropagationTailData {d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (m : Nat) : PolynomialTailPresentationData m :=
  PolynomialTailPresentationData.ofPolynomial (step1PropagationTailPoly θ w m)

/-- The last-variable leading-coefficient polynomial extracted from `f_{m+2}`. -/
noncomputable def step1PropagationLeadingCoeffPoly {d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (m : Nat) : MvPolynomial (Fin m) ℂ :=
  (lastVariablePolynomial (step1PropagationTailPoly θ w m)).leadingCoeff

@[simp]
theorem step1PropagationTailData_poly {d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (m : Nat) :
    (step1PropagationTailData θ w m).poly = step1PropagationTailPoly θ w m :=
  rfl

@[simp]
theorem step1PropagationTailData_presentation {d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (m : Nat) :
    (step1PropagationTailData θ w m).presentation =
      polynomialTailPresentation (step1PropagationTailPoly θ w m) :=
  rfl

@[simp]
theorem step1PropagationTailData_lead {d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (m : Nat) (x : Fin m → ℂ) :
    (step1PropagationTailData θ w m).presentation.lead x =
      MvPolynomial.eval x (step1PropagationLeadingCoeffPoly θ w m) :=
  rfl

/-- Evaluation of the canonical tail data is evaluation of the concrete propagation
polynomial on the nested coordinates. -/
theorem step1PropagationTailData_eval_nested {d m : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (z : Fin (m + 1) → ℂ) :
    (step1PropagationTailData θ w m).presentation.eval (nestedInit z) (nestedLast z) =
      MvPolynomial.eval z (step1PropagationTailPoly θ w m) :=
  PolynomialTailPresentationData.eval_nested (step1PropagationTailData θ w m) z

/-- The concrete Step 1 propagation polynomial `f_{m+2}` is independent of the last
variable in the `m+1`-variable presentation. -/
theorem degreeOf_step1PropagationTailPoly_last {d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (m : Nat) :
    MvPolynomial.degreeOf (Fin.last m) (step1PropagationTailPoly θ w m) = 0 := by
  simpa [step1PropagationTailPoly] using
    degreeOf_step1LastSqCoeffPoly_eq_zero_of_le θ ⟨m, Nat.lt_succ_self m⟩
      (j := Fin.last m) w (by simp)

/-- After moving the last variable to the front, the front variable still has degree
zero for the concrete propagation polynomial. -/
theorem degreeOf_step1PropagationTailPoly_rename_lastToFront_zero {d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (m : Nat) :
    MvPolynomial.degreeOf (0 : Fin (m + 1))
        (MvPolynomial.rename (nestedLastToFrontEquiv m) (step1PropagationTailPoly θ w m)) =
      0 := by
  have hrename :=
    MvPolynomial.degreeOf_rename_of_injective
      (R := ℂ) (p := step1PropagationTailPoly θ w m)
      (f := nestedLastToFrontEquiv m)
      (Equiv.injective (nestedLastToFrontEquiv m)) (Fin.last m)
  simpa [degreeOf_step1PropagationTailPoly_last θ w m] using hrename

@[simp]
theorem step1PropagationTailData_degree {d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (m : Nat) :
    (step1PropagationTailData θ w m).presentation.degree = 0 := by
  change (lastVariablePolynomial (step1PropagationTailPoly θ w m)).natDegree = 0
  unfold lastVariablePolynomial
  rw [MvPolynomial.natDegree_finSuccEquiv]
  exact degreeOf_step1PropagationTailPoly_rename_lastToFront_zero θ w m

/-- The nested-tail family whose `m`th step is the canonical presentation of
`f_{m+2}`.  For a depth `L`, the relevant propagation steps are `m < L - 1`. -/
noncomputable def step1PropagationNestedTailFamily {d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) : NestedTailFamily where
  step m := (step1PropagationTailData θ w m).presentation

@[simp]
theorem step1PropagationNestedTailFamily_step {d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (m : Nat) :
    (step1PropagationNestedTailFamily θ w).step m =
      (step1PropagationTailData θ w m).presentation :=
  rfl

/-- Evaluation of the concrete nested-tail family step is evaluation of `f_{m+2}`. -/
theorem step1PropagationNestedTailFamily_evalStep {d m : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (z : Fin (m + 1) → ℂ) :
    (step1PropagationNestedTailFamily θ w).evalStep z =
      MvPolynomial.eval z (step1PropagationTailPoly θ w m) := by
  simpa [NestedTailFamily.evalStep] using
    step1PropagationTailData_eval_nested θ w z

@[simp]
theorem step1PropagationNestedTailFamily_step_degree {d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (m : Nat) :
    ((step1PropagationNestedTailFamily θ w).step m).degree = 0 :=
  step1PropagationTailData_degree θ w m

/-- Because `f_{m+2}` is independent of the newly peeled last variable, the `m`th
nested-step evaluation is exactly evaluation of the extracted leading coefficient on the
prefix. -/
theorem step1PropagationNestedTailFamily_evalStep_eq_leadingCoeff_eval {d m : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (z : Fin (m + 1) → ℂ) :
    (step1PropagationNestedTailFamily θ w).evalStep z =
      MvPolynomial.eval (nestedInit z) (step1PropagationLeadingCoeffPoly θ w m) := by
  calc
    (step1PropagationNestedTailFamily θ w).evalStep z =
        ((step1PropagationNestedTailFamily θ w).step m).lead (nestedInit z) := by
      exact TailPresentation.eval_eq_lead_of_degree_eq_zero
        ((step1PropagationNestedTailFamily θ w).step m)
        (step1PropagationNestedTailFamily_step_degree θ w m) (nestedInit z) (nestedLast z)
    _ = MvPolynomial.eval (nestedInit z) (step1PropagationLeadingCoeffPoly θ w m) := rfl

/-- Polynomial evaluation form of
`step1PropagationNestedTailFamily_evalStep_eq_leadingCoeff_eval`. -/
theorem eval_step1PropagationTailPoly_eq_leadingCoeff_eval {d m : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (z : Fin (m + 1) → ℂ) :
    MvPolynomial.eval z (step1PropagationTailPoly θ w m) =
      MvPolynomial.eval (nestedInit z) (step1PropagationLeadingCoeffPoly θ w m) := by
  rw [← step1PropagationNestedTailFamily_evalStep θ w z]
  exact step1PropagationNestedTailFamily_evalStep_eq_leadingCoeff_eval θ w z

/-- Specialized slice form: the target leading-coefficient nonvanishing is equivalent to
nonvanishing of the concrete propagation polynomial on any extension of the prefix. -/
theorem eval_step1PropagationTailPoly_snoc_eq_leadingCoeff_eval {d m : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (x : Fin m → ℂ) (y : ℂ) :
    MvPolynomial.eval (Fin.snoc x y) (step1PropagationTailPoly θ w m) =
      MvPolynomial.eval x (step1PropagationLeadingCoeffPoly θ w m) := by
  have hinit : nestedInit (Fin.snoc x y) = x := by
    funext i
    simp [nestedInit]
  simpa [hinit] using
    eval_step1PropagationTailPoly_eq_leadingCoeff_eval θ w (Fin.snoc x y)

theorem leadingCoeff_eval_ne_zero_iff_tailPoly_eval_snoc_ne_zero {d m : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (x : Fin m → ℂ) (y : ℂ) :
    MvPolynomial.eval x (step1PropagationLeadingCoeffPoly θ w m) ≠ 0 ↔
      MvPolynomial.eval (Fin.snoc x y) (step1PropagationTailPoly θ w m) ≠ 0 := by
  rw [eval_step1PropagationTailPoly_snoc_eq_leadingCoeff_eval]

/-- In zero variables, polynomial nonzeroness is pointwise nonvanishing. -/
theorem eval_ne_zero_of_ne_zero_fin_zero {p : MvPolynomial (Fin 0) ℂ}
    (hp : p ≠ 0) (x : Fin 0 → ℂ) :
    MvPolynomial.eval x p ≠ 0 := by
  have hx : x = Fin.elim0 := by
    funext i
    exact Fin.elim0 i
  subst x
  intro h
  apply hp
  apply (MvPolynomial.isEmptyAlgEquiv ℂ (Fin 0)).injective
  simpa [MvPolynomial.isEmptyAlgEquiv_apply] using h

/-- On the depth-relevant range, the concrete propagation polynomial has a dominant top
coefficient from the packaged Step 1 assumptions. -/
theorem hasDominantTopCoeff_step1PropagationTailPoly_of_depth {L d : Nat}
    {θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ}
    {w : Fin d → ℝ} {iota : Fin d}
    (h : Step1PolynomialFamilyAssumptionsForDepth L d θ w iota)
    {m : Nat} (hm : m < L - 1) :
    HasDominantTopCoeff (step1PropagationTailPoly θ w m) :=
  hasDominantTopCoeff_step1LastSqCoeffPoly θ ⟨m, Nat.lt_succ_self m⟩ w
    (h.kappa_ne ⟨m, hm⟩)

/-- The last-variable leading coefficient extracted from `f_{m+2}` still has a dominant
top coefficient on the depth-relevant range.  This is the DTC part of the nested
largeness obligation; pointwise nonvanishing on the actual recursive region is packaged
separately below. -/
theorem hasDominantTopCoeff_step1PropagationLeadingCoeffPoly_of_depth {L d : Nat}
    {θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ}
    {w : Fin d → ℝ} {iota : Fin d}
    (h : Step1PolynomialFamilyAssumptionsForDepth L d θ w iota)
    {m : Nat} (hm : m < L - 1) :
    HasDominantTopCoeff (step1PropagationLeadingCoeffPoly θ w m) := by
  unfold step1PropagationLeadingCoeffPoly lastVariablePolynomial
  exact
    ((hasDominantTopCoeff_step1PropagationTailPoly_of_depth
        (L := L) (iota := iota) h hm).rename_of_injective
      (Equiv.injective (nestedLastToFrontEquiv m))).leadingCoeff_finSuccEquiv

/-- The extracted leading coefficient is nonzero as a polynomial on the depth-relevant
range. This is the strongest consequence available from dominant-top-coefficient data
alone; pointwise nonvanishing on every recursive region is a separate zero-free-region
fact. -/
theorem step1PropagationLeadingCoeffPoly_ne_zero_of_depth {L d : Nat}
    {θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ}
    {w : Fin d → ℝ} {iota : Fin d}
    (h : Step1PolynomialFamilyAssumptionsForDepth L d θ w iota)
    {m : Nat} (hm : m < L - 1) :
    step1PropagationLeadingCoeffPoly θ w m ≠ 0 :=
  (hasDominantTopCoeff_step1PropagationLeadingCoeffPoly_of_depth
    (L := L) (iota := iota) h hm).ne_zero

/-- The base propagation step has no previous coordinates, so the existing polynomial
nonzeroness is enough to discharge pointwise nonvanishing. -/
theorem eval_step1PropagationLeadingCoeffPoly_zero_ne_of_depth {L d : Nat}
    {θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ}
    {w : Fin d → ℝ} {iota : Fin d}
    (h : Step1PolynomialFamilyAssumptionsForDepth L d θ w iota)
    (h0 : 0 < L - 1) (x : Fin 0 → ℂ) :
    MvPolynomial.eval x (step1PropagationLeadingCoeffPoly θ w 0) ≠ 0 :=
  eval_ne_zero_of_ne_zero_fin_zero
    (step1PropagationLeadingCoeffPoly_ne_zero_of_depth
      (L := L) (iota := iota) h h0) x

/-- Polynomial-backed data for the concrete Step 1 propagation tail tower. -/
noncomputable def step1PropagationPolynomialNestedTailData {d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) : PolynomialNestedTailData where
  tailData m := step1PropagationTailData θ w m
  lead_continuous := by
    intro m
    simpa [step1PropagationTailData] using
      continuous_polynomialTailPresentation_lead (step1PropagationTailPoly θ w m)
  lower_continuous := by
    intro m i
    simpa [step1PropagationTailData] using
      continuous_polynomialTailPresentation_lower (step1PropagationTailPoly θ w m) i

@[simp]
theorem step1PropagationPolynomialNestedTailData_tailData {d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (m : Nat) :
    (step1PropagationPolynomialNestedTailData θ w).tailData m =
      step1PropagationTailData θ w m :=
  rfl

@[simp]
theorem step1PropagationPolynomialNestedTailData_toNestedTailFamily {d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) :
    (step1PropagationPolynomialNestedTailData θ w).toNestedTailFamily =
      step1PropagationNestedTailFamily θ w :=
  rfl

/-! ## Combined propagation-visible zero-free tower -/

/-- The combined Step 1 tail polynomial at level `m`.

This product is the local polynomial whose nonvanishing records both the propagation
blocker `f_{m+2}` and the visible blocker `g_{m+1}` at the same nested step.  It is a
concrete product tower version of the TeX instruction to include `g` in the finite
nested-largeness family, rather than relying on the propagation-only region. -/
noncomputable def step1PropagationVisibleTailPoly {d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (iota : Fin d) (m : Nat) :
    MvPolynomial (Fin (m + 1)) ℂ :=
  step1PropagationTailPoly θ w m *
    step1VisiblePoly (K := m + 1) θ w iota

/-- Polynomial-backed nested data for the combined propagation-visible tower. -/
noncomputable def step1PropagationVisibleNestedTailData {d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (iota : Fin d) : PolynomialNestedTailData :=
  PolynomialNestedTailData.ofPolynomials
    (fun m => step1PropagationVisibleTailPoly θ w iota m)

@[simp]
theorem step1PropagationVisibleNestedTailData_tailData {d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (iota : Fin d) (m : Nat) :
    (step1PropagationVisibleNestedTailData θ w iota).tailData m =
      PolynomialTailPresentationData.ofPolynomial
        (step1PropagationVisibleTailPoly θ w iota m) :=
  rfl

/-- Leading-coefficient factorization of the combined propagation-visible tail polynomial.

Since `f_{j+2} = step1PropagationTailPoly θ w j` is independent of the newly peeled last
variable, the last-variable leading coefficient of the product
`f_{j+2} · g_{j+1}` factors as the formal-phi leading coefficient
`step1PropagationLeadingCoeffPoly θ w j` times the visible leading coefficient. -/
theorem lastVariablePolynomial_leadingCoeff_step1PropagationVisibleTailPoly {d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (iota : Fin d) (j : Nat) :
    (lastVariablePolynomial (step1PropagationVisibleTailPoly θ w iota j)).leadingCoeff =
      step1PropagationLeadingCoeffPoly θ w j *
        (lastVariablePolynomial (step1VisiblePoly (K := j + 1) θ w iota)).leadingCoeff := by
  rw [step1PropagationVisibleTailPoly, lastVariablePolynomial_mul,
    Polynomial.leadingCoeff_mul]
  rfl

/-- Membership in the combined propagation-visible zero-free region (at the *same* depth
`j`) makes the formal-phi leading coefficient `step1PropagationLeadingCoeffPoly θ w j`
nonzero.  This is the bridge that lets the concrete formal-phi gate blow up at every
point of the combined tier, even though the combined tower's own step polynomial is the
product `f_{j+2} · g_{j+1}`, not the formal-phi preactivation. -/
theorem eval_step1PropagationLeadingCoeffPoly_ne_zero_of_propagationVisibleZeroFreeRegion
    {d : Nat}
    {θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ}
    {w : Fin d → ℝ} {iota : Fin d}
    {j : Nat} {x : Fin j → ℂ}
    (hx : x ∈ (step1PropagationVisibleNestedTailData θ w iota).zeroFreeRegion j) :
    MvPolynomial.eval x (step1PropagationLeadingCoeffPoly θ w j) ≠ 0 := by
  have hlead :
      ((step1PropagationVisibleNestedTailData θ w iota).tailData j).presentation.lead x ≠ 0 :=
    (step1PropagationVisibleNestedTailData θ w iota).lead_ne_of_mem_zeroFreeRegion hx
  have hlead' :
      MvPolynomial.eval x
          (lastVariablePolynomial
            (step1PropagationVisibleTailPoly θ w iota j)).leadingCoeff ≠ 0 := by
    simpa [step1PropagationVisibleNestedTailData_tailData,
      PolynomialTailPresentationData.ofPolynomial, polynomialTailPresentation] using hlead
  rw [lastVariablePolynomial_leadingCoeff_step1PropagationVisibleTailPoly,
    map_mul] at hlead'
  exact (mul_ne_zero_iff.mp hlead').1

/-! ## Concrete zero-free propagation regions -/

/-- The strengthened zero-free recursive region for the concrete Step 1 propagation
tower, exposed through the evaluator-form nested-tail API. -/
noncomputable def step1PropagationZeroFreeRegion {d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (m : Nat) : Set (Fin m → ℂ) :=
  (step1PropagationNestedTailFamily θ w).zeroFreeRegion m

/-- The same strengthened zero-free recursive region, exposed through the
polynomial-backed nested-tail data package. -/
noncomputable def step1PropagationPolynomialZeroFreeRegion {d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (m : Nat) : Set (Fin m → ℂ) :=
  (step1PropagationPolynomialNestedTailData θ w).zeroFreeRegion m

@[simp]
theorem step1PropagationPolynomialZeroFreeRegion_eq {d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (m : Nat) :
    step1PropagationPolynomialZeroFreeRegion θ w m =
      step1PropagationZeroFreeRegion θ w m :=
  rfl

@[simp]
theorem mem_step1PropagationZeroFreeRegion_zero {d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (z : Fin 0 → ℂ) :
    z ∈ step1PropagationZeroFreeRegion θ w 0 ↔
      MvPolynomial.eval z (step1PropagationLeadingCoeffPoly θ w 0) ≠ 0 := by
  rfl

@[simp]
theorem mem_step1PropagationZeroFreeRegion_succ {d m : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) {z : Fin (m + 1) → ℂ} :
    z ∈ step1PropagationZeroFreeRegion θ w (m + 1) ↔
      nestedInit z ∈ step1PropagationZeroFreeRegion θ w m ∧
        (step1PropagationNestedTailFamily θ w).threshold m (nestedInit z) <
          ‖nestedLast z‖ ∧
        MvPolynomial.eval z (step1PropagationLeadingCoeffPoly θ w (m + 1)) ≠ 0 := by
  rfl

/-- Zero-free-region assumptions for the concrete Step 1 propagation tower at a fixed
depth.  The leading-coefficient field is discharged by the strengthened region API; it
is kept here so downstream code can consume the same shape as the older region-based
package without conflating the two regions. -/
structure Step1PropagationZeroFreeNestedAssumptionsForDepth (L d : Nat)
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (iota : Fin d) : Prop where
  polynomialFamily : Step1PolynomialFamilyAssumptionsForDepth L d θ w iota
  leadingCoeff_ne_on_zeroFreeRegion :
    ∀ m : Nat, m < L - 1 →
      ∀ x : Fin m → ℂ,
        x ∈ step1PropagationZeroFreeRegion θ w m →
          MvPolynomial.eval x (step1PropagationLeadingCoeffPoly θ w m) ≠ 0

namespace Step1PropagationZeroFreeNestedAssumptionsForDepth

variable {L d : Nat}
variable {θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ}
variable {w : Fin d → ℝ} {iota : Fin d}

end Step1PropagationZeroFreeNestedAssumptionsForDepth

/-- Concrete nested-largeness assumptions for the Step 1 propagation polynomials at a
fixed depth.  `polynomialFamily` supplies the already-proved top coefficient
nonvanishing for `f_2, ..., f_L` and `g`; the only remaining nested-largeness
nonvanishing field is exactly the extracted leading coefficient on the recursive region
for each propagation step `m < L - 1`. -/
structure Step1PropagationNestedLargenessAssumptionsForDepth (L d : Nat)
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (iota : Fin d) : Prop where
  polynomialFamily : Step1PolynomialFamilyAssumptionsForDepth L d θ w iota
  leadingCoeff_ne_on_region :
    ∀ m : Nat, m < L - 1 →
      ∀ x : Fin m → ℂ,
        x ∈ (step1PropagationNestedTailFamily θ w).region m →
          MvPolynomial.eval x (step1PropagationLeadingCoeffPoly θ w m) ≠ 0

/-- The remaining nested-largeness nonvanishing field is equivalent to zero-freeness of
the concrete propagation polynomial on the slice obtained by adjoining a zero last
coordinate.  This is a reduction only: the current recursive region definition does not
itself impose this zero-freeness. -/
theorem leadingCoeff_ne_on_region_iff_tailPoly_snoc_zero_ne_on_region {L d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) :
    (∀ m : Nat, m < L - 1 →
      ∀ x : Fin m → ℂ,
        x ∈ (step1PropagationNestedTailFamily θ w).region m →
          MvPolynomial.eval x (step1PropagationLeadingCoeffPoly θ w m) ≠ 0) ↔
    (∀ m : Nat, m < L - 1 →
      ∀ x : Fin m → ℂ,
        x ∈ (step1PropagationNestedTailFamily θ w).region m →
          MvPolynomial.eval (Fin.snoc x 0) (step1PropagationTailPoly θ w m) ≠ 0) := by
  constructor
  · intro hlead m hm x hx
    exact (leadingCoeff_eval_ne_zero_iff_tailPoly_eval_snoc_ne_zero θ w x 0).mp
      (hlead m hm x hx)
  · intro htail m hm x hx
    exact (leadingCoeff_eval_ne_zero_iff_tailPoly_eval_snoc_ne_zero θ w x 0).mpr
      (htail m hm x hx)

/-- Constructor from the already-packaged polynomial-family assumptions plus the exact
additional zero-free-region statement still missing for nested largeness. -/
theorem step1PropagationNestedLargenessAssumptionsForDepth_of_tailPoly_snoc_zero_ne_on_region
    {L d : Nat}
    {θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ}
    {w : Fin d → ℝ} {iota : Fin d}
    (hpoly : Step1PolynomialFamilyAssumptionsForDepth L d θ w iota)
    (htail :
      ∀ m : Nat, m < L - 1 →
        ∀ x : Fin m → ℂ,
          x ∈ (step1PropagationNestedTailFamily θ w).region m →
            MvPolynomial.eval (Fin.snoc x 0) (step1PropagationTailPoly θ w m) ≠ 0) :
    Step1PropagationNestedLargenessAssumptionsForDepth L d θ w iota where
  polynomialFamily := hpoly
  leadingCoeff_ne_on_region :=
    (leadingCoeff_ne_on_region_iff_tailPoly_snoc_zero_ne_on_region θ w).mpr htail

namespace Step1PropagationNestedLargenessAssumptionsForDepth

variable {L d : Nat}
variable {θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ}
variable {w : Fin d → ℝ} {iota : Fin d}

end Step1PropagationNestedLargenessAssumptionsForDepth

end TransformerIdentifiability.NLayer
