import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Step2.HeadwiseRegion

set_option autoImplicit false

open Matrix

namespace TransformerIdentifiability.NLayer.NoSkip

noncomputable section

/-!
# Scalar-dial zero rigidity

This is the repaired zero branch of the no-skip proof.  Only one first-layer
head is dialled.  Thus the first-layer effective streams are
`(C - zV)w` and `Cv + zVw`, and every deeper frozen slope has the form

`wᵀ X(z) v + wᵀ Y(z) w`,

where

`X(z) = (C-zV)ᵀ RtA P C`,
`Y(z) = (C-zV)ᵀ RtA (zPV + Q(C-zV))`.

The crucial new hypothesis, obtained from equality at the zero input, is that
`C` is invertible.  It rules out the spurious coefficient case that invalidated
the former simultaneous-dial proof.
-/

/-- Matrix data for the repaired scalar no-skip dial. -/
structure ScalarDialForm (d : Nat) where
  C : Matrix (Fin d) (Fin d) Real
  V : Matrix (Fin d) (Fin d) Real
  RtA : Matrix (Fin d) (Fin d) Real
  P : Matrix (Fin d) (Fin d) Real
  Q : Matrix (Fin d) (Fin d) Real

namespace ScalarDialForm

variable {d : Nat}

/-- Pulling linear changes of both vectors into a bilinear-form matrix. -/
theorem matrixBilin_mulVec_mulVec
    (A R U : Matrix (Fin d) (Fin d) Real) (w v : Vec d) :
    NLayer.matrixBilin A (R *ᵥ w) (U *ᵥ v) =
      NLayer.matrixBilin (Rᵀ * A * U) w v := by
  unfold NLayer.matrixBilin
  simpa only [Matrix.mulVec_mulVec, Matrix.mul_assoc,
    Matrix.transpose_transpose] using
    (KHead.adjoint_dotProduct Rᵀ w ((A * U) *ᵥ v))

/-- Additivity in the right vector for the parent bilinear form. -/
theorem matrixBilin_add_right
    (A : Matrix (Fin d) (Fin d) Real) (w u v : Vec d) :
    NLayer.matrixBilin A w (u + v) =
      NLayer.matrixBilin A w u + NLayer.matrixBilin A w v := by
  simp [NLayer.matrixBilin, Matrix.mulVec_add, dotProduct_add]

/-- A matrix and its transpose have the same quadratic form. -/
theorem matrixBilin_transpose_self
    (M : Matrix (Fin d) (Fin d) Real) (w : Vec d) :
    NLayer.matrixBilin Mᵀ w w = NLayer.matrixBilin M w w := by
  simpa [NLayer.matrixBilin] using
    (Matrix.dotProduct_transpose_mulVec (A := M) (x := w) (y := w))

/-- Additivity in the matrix argument. -/
theorem matrixBilin_add_matrix
    (M N : Matrix (Fin d) (Fin d) Real) (w v : Vec d) :
    NLayer.matrixBilin (M + N) w v =
      NLayer.matrixBilin M w v + NLayer.matrixBilin N w v := by
  simp [NLayer.matrixBilin, Matrix.add_mulVec, dotProduct_add]

/-- The fixed right factor in `X(z)`. -/
def H (Phi : ScalarDialForm d) : Matrix (Fin d) (Fin d) Real :=
  Phi.RtA * Phi.P * Phi.C

/-- The affine matrix polynomial `C-zV`. -/
noncomputable def CzV (Phi : ScalarDialForm d) :
    Matrix (Fin d) (Fin d) (Polynomial Real) :=
  KHead.liftC Phi.C - (Polynomial.X : Polynomial Real) • KHead.liftC Phi.V

/-- The bilinear coefficient `X(z)`. -/
noncomputable def Xpoly (Phi : ScalarDialForm d) :
    Matrix (Fin d) (Fin d) (Polynomial Real) :=
  Phi.CzVᵀ * KHead.liftC Phi.H

/-- The quadratic coefficient `Y(z)`. -/
noncomputable def Ypoly (Phi : ScalarDialForm d) :
    Matrix (Fin d) (Fin d) (Polynomial Real) :=
  Phi.CzVᵀ * KHead.liftC Phi.RtA *
    ((Polynomial.X : Polynomial Real) • KHead.liftC (Phi.P * Phi.V) +
      KHead.liftC Phi.Q * Phi.CzV)

/-- The real matrix `C-tV`. -/
def CzVr (Phi : ScalarDialForm d) (t : Real) :
    Matrix (Fin d) (Fin d) Real :=
  Phi.C - t • Phi.V

/-- Real evaluation of `X`. -/
def Xfun (Phi : ScalarDialForm d) (t : Real) :
    Matrix (Fin d) (Fin d) Real :=
  (Phi.CzVr t)ᵀ * Phi.H

/-- Real evaluation of `Y`. -/
def Yfun (Phi : ScalarDialForm d) (t : Real) :
    Matrix (Fin d) (Fin d) Real :=
  (Phi.CzVr t)ᵀ * Phi.RtA *
    (t • (Phi.P * Phi.V) + Phi.Q * Phi.CzVr t)

@[simp] theorem eval_CzV (Phi : ScalarDialForm d) (t : Real) :
    KHead.evalPolynomialMatrix t Phi.CzV = Phi.CzVr t := by
  simp [CzV, CzVr]

@[simp] theorem eval_Xpoly (Phi : ScalarDialForm d) (t : Real) :
    KHead.evalPolynomialMatrix t Phi.Xpoly = Phi.Xfun t := by
  simp [Xpoly, Xfun]

@[simp] theorem eval_Ypoly (Phi : ScalarDialForm d) (t : Real) :
    KHead.evalPolynomialMatrix t Phi.Ypoly = Phi.Yfun t := by
  simp [Ypoly, Yfun]

/-- `X(z)` is affine, with the displayed constant and linear coefficients. -/
theorem Xpoly_eq (Phi : ScalarDialForm d) :
    Phi.Xpoly =
      KHead.liftC (Phi.Cᵀ * Phi.H) -
        (Polynomial.X : Polynomial Real) • KHead.liftC (Phi.Vᵀ * Phi.H) := by
  rw [Xpoly, CzV, Matrix.transpose_sub, Matrix.transpose_smul,
    KHead.liftC_transpose, KHead.liftC_transpose, Matrix.sub_mul,
    smul_mul_assoc, KHead.liftC_mul, KHead.liftC_mul]

/-- Evaluation of the repaired scalar matrix form. -/
noncomputable def eval (Phi : ScalarDialForm d)
    (x : HeadwiseSignPoint d) : Real :=
  NLayer.matrixBilin (KHead.evalPolynomialMatrix x.2 Phi.Xpoly)
      x.1.1 x.1.2 +
    NLayer.matrixBilin (KHead.evalPolynomialMatrix x.2 Phi.Ypoly)
      x.1.1 x.1.1

theorem continuous_eval (Phi : ScalarDialForm d) :
    Continuous Phi.eval := by
  unfold eval NLayer.matrixBilin KHead.evalPolynomialMatrix Matrix.mulVec dotProduct
  fun_prop

/-- The zero conclusion used by the trichotomy. -/
def IsZero (Phi : ScalarDialForm d) : Prop :=
  Phi.Xpoly = 0 ∧ Phi.Ypoly + Phi.Ypolyᵀ = 0

/-- A zero scalar form evaluates to zero at every probe and dial value. -/
theorem eval_eq_zero_of_isZero (Phi : ScalarDialForm d) (hzero : Phi.IsZero)
    (p : HeadwiseSignPoint d) : Phi.eval p = 0 := by
  have hYeval :
      KHead.evalPolynomialMatrix p.2 Phi.Ypoly +
          (KHead.evalPolynomialMatrix p.2 Phi.Ypoly)ᵀ = 0 := by
    have h := congrArg (KHead.evalPolynomialMatrix p.2) hzero.2
    simpa using h
  have hquad : NLayer.matrixBilin
      (KHead.evalPolynomialMatrix p.2 Phi.Ypoly) p.1.1 p.1.1 = 0 := by
    have h := congrArg
      (fun M => NLayer.matrixBilin M p.1.1 p.1.1) hYeval
    dsimp only at h
    rw [matrixBilin_add_matrix, matrixBilin_transpose_self] at h
    have hzeroBilin : NLayer.matrixBilin
        (0 : Matrix (Fin d) (Fin d) Real) p.1.1 p.1.1 = 0 := by
      simp [NLayer.matrixBilin]
    rw [hzeroBilin] at h
    linarith
  rw [eval, hzero.1, KHead.eval_zeroMatrix]
  simpa [NLayer.matrixBilin] using hquad

/-- The repaired coefficient case analysis.  Invertibility of `C` is the
additional input missing from the invalid older proof. -/
theorem gamma_eq_zero (Phi : ScalarDialForm d)
    (Ah : Matrix (Fin d) (Fin d) Real) (gamma0 gamma1 : Real)
    (hc0 : Phi.Cᵀ * Phi.H = gamma0 • Ah)
    (hc1 : -(Phi.Vᵀ * Phi.H) = gamma1 • Ah)
    (hclub : ∀ t : Real, Phi.Yfun t + (Phi.Yfun t)ᵀ = 0)
    (hdetC : Phi.C.det ≠ 0)
    (hdetA : Ah.det ≠ 0)
    (hsymA : sym Ah ≠ 0)
    (hVne : Phi.V ≠ 0) :
    gamma0 = 0 ∧ gamma1 = 0 := by
  have hdetCt : Phi.Cᵀ.det ≠ 0 := by
    simpa using hdetC
  have cancelC : ∀ M : Matrix (Fin d) (Fin d) Real,
      Phi.Cᵀ * M = 0 → M = 0 := by
    intro M hM
    have h := congrArg (fun N => (Phi.Cᵀ)⁻¹ * N) hM
    simpa [← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul Phi.Cᵀ hdetCt.isUnit] using h
  by_cases hgamma0 : gamma0 = 0
  · have hHmul : Phi.Cᵀ * Phi.H = 0 := by
      rw [hc0, hgamma0, zero_smul]
    have hH : Phi.H = 0 := cancelC Phi.H hHmul
    have hgamma1 : gamma1 = 0 := by
      have hsmul : gamma1 • Ah = 0 := by
        rw [← hc1, hH, Matrix.mul_zero, neg_zero]
      rcases smul_eq_zero.mp hsmul with h | hA
      · exact h
      · exact False.elim
          (hsymA (KHead.sym_eq_zero_of_add_transpose_eq_zero (by simp [hA])))
    exact ⟨hgamma0, hgamma1⟩
  · exfalso
    have hdetH : Phi.H.det ≠ 0 := by
      have hprod : (Phi.Cᵀ * Phi.H).det ≠ 0 := by
        rw [hc0, Matrix.det_smul]
        exact mul_ne_zero (pow_ne_zero _ hgamma0) hdetA
      rw [Matrix.det_mul] at hprod
      exact right_ne_zero_of_mul hprod
    have cancelH : ∀ M : Matrix (Fin d) (Fin d) Real,
        M * Phi.H = 0 → M = 0 := by
      intro M hM
      have h : M * Phi.H * Phi.H⁻¹ = 0 := by
        rw [hM, Matrix.zero_mul]
      rwa [Matrix.mul_assoc,
        Matrix.mul_nonsing_inv Phi.H hdetH.isUnit, Matrix.mul_one] at h
    let c : Real := -gamma1 * gamma0⁻¹
    have hcg : c * gamma0 = -gamma1 := by
      dsimp [c]
      field_simp
    have hVt : Phi.Vᵀ = c • Phi.Cᵀ := by
      have hVH : Phi.Vᵀ * Phi.H = (-gamma1) • Ah := by
        have h := hc1
        rw [neg_eq_iff_eq_neg] at h
        simpa [neg_smul] using h
      have hzero : (Phi.Vᵀ - c • Phi.Cᵀ) * Phi.H = 0 := by
        rw [Matrix.sub_mul, smul_mul_assoc, hVH, hc0, smul_smul,
          hcg, sub_self]
      exact sub_eq_zero.mp (cancelH _ hzero)
    have hV : Phi.V = c • Phi.C := by
      have h := congrArg Matrix.transpose hVt
      simpa using h
    have hcne : c ≠ 0 := by
      intro hc
      apply hVne
      rw [hV, hc, zero_smul]
    let HP : Matrix (Fin d) (Fin d) Real :=
      Phi.Cᵀ * Phi.RtA * Phi.P * Phi.C
    let HQ : Matrix (Fin d) (Fin d) Real :=
      Phi.Cᵀ * Phi.RtA * Phi.Q * Phi.C
    have hHP : HP = gamma0 • Ah := by
      rw [← hc0]
      simp only [HP, H, Matrix.mul_assoc]
    have hCz : ∀ t : Real, Phi.CzVr t = (1 - c * t) • Phi.C := by
      intro t
      rw [CzVr, hV]
      simp only [smul_smul]
      match_scalars <;> ring
    have hYnf : ∀ t : Real, Phi.Yfun t =
        (1 - c * t) •
          ((t * c) • HP + (1 - c * t) • HQ) := by
      intro t
      rw [Yfun, hCz, hV]
      simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul,
        smul_smul, Matrix.mul_add, Matrix.mul_assoc, HP, HQ]
      match_scalars <;> ring
    have hHQsym : HQ + HQᵀ = 0 := by
      have h := hclub 0
      rw [hYnf 0] at h
      simpa using h
    let u : Real := (2 * c)⁻¹
    have huc : u * c = (2 : Real)⁻¹ := by
      dsimp [u]
      field_simp
      <;> ring
    have hcu : c * u = (2 : Real)⁻¹ := by
      rw [mul_comm]
      exact huc
    have hone : 1 - c * u = (2 : Real)⁻¹ := by
      rw [hcu]
      norm_num
    have hYusym := hclub u
    rw [hYnf u, hone, huc] at hYusym
    have hsumSym : (HP + HQ) + (HP + HQ)ᵀ = 0 := by
      have hscaled : ((4 : Real)⁻¹) •
          ((HP + HQ) + (HP + HQ)ᵀ) = 0 := by
        calc
          ((4 : Real)⁻¹) • ((HP + HQ) + (HP + HQ)ᵀ) =
              (2 : Real)⁻¹ • ((2 : Real)⁻¹ • HP + (2 : Real)⁻¹ • HQ) +
                ((2 : Real)⁻¹ • ((2 : Real)⁻¹ • HP +
                  (2 : Real)⁻¹ • HQ))ᵀ := by
                    simp only [Matrix.transpose_smul, Matrix.transpose_add]
                    match_scalars <;> ring
          _ = 0 := hYusym
      rcases smul_eq_zero.mp hscaled with hfour | hzero
      · norm_num at hfour
      · exact hzero
    have hHPsym : HP + HPᵀ = 0 := by
      rw [Matrix.transpose_add] at hsumSym
      linear_combination (norm := module) hsumSym - hHQsym
    have hAsym : Ah + Ahᵀ = 0 := by
      rw [hHP, Matrix.transpose_smul, ← smul_add] at hHPsym
      rcases smul_eq_zero.mp hHPsym with h | h
      · exact False.elim (hgamma0 h)
      · exact h
    exact hsymA (KHead.sym_eq_zero_of_add_transpose_eq_zero hAsym)

/-- Vanishing on a repaired headwise region forces the scalar dial form to be
zero.  This combines one-quadric rigidity on every time slice, interpolation
over the infinite time projection, and `gamma_eq_zero`. -/
theorem zero_of_vanishesOn {n k d : Nat}
    {theta : Params (n + 1) k d} {h : Fin k}
    {D : HeadwiseSignRegion theta h}
    (Phi : ScalarDialForm d) (R : HeadwiseRestrictedRegion D)
    (hd : 2 ≤ d)
    (hdetC : Phi.C.det ≠ 0)
    (hdetA : (attentionMatrix theta 0 h).det ≠ 0)
    (hsymA : sym (attentionMatrix theta 0 h) ≠ 0)
    (hVne : Phi.V ≠ 0)
    (hvanish : ∀ x ∈ R.region, Phi.eval x = 0) :
    Phi.IsZero := by
  have hJinf : (KHead.timeProjection R.region).Infinite :=
    R.timeProjection_infinite
  have hslice : ∀ t ∈ KHead.timeProjection R.region,
      (∃ c : Real, Phi.Xfun t = c • attentionMatrix theta 0 h) ∧
        (Phi.Yfun t + (Phi.Yfun t)ᵀ = 0) := by
    intro t ht
    obtain ⟨p0, hp0⟩ := ht
    obtain ⟨O, hOopen, hOeq⟩ := R.timeSlice_relativelyOpen t
    have hp0slice : p0 ∈ KHead.timeSlice R.region t := hp0
    rw [hOeq] at hp0slice
    have hquad0 :
        NLayer.matrixBilin (attentionMatrix theta 0 h) p0.1 p0.2 = 0 := by
      have hq := hp0slice.2.1
      simpa [KHead.firstHeadQuadric, KHead.firstHeadSlope] using hq
    have hvanishO : ∀ p ∈ O,
        NLayer.matrixBilin (attentionMatrix theta 0 h) p.1 p.2 = 0 →
          NLayer.matrixBilin (Phi.Xfun t) p.1 p.2 +
            NLayer.matrixBilin (Phi.Yfun t) p.1 p.1 = 0 := by
      intro p hpO hpq
      by_cases hpw : p.1 = 0
      · simp [hpw, NLayer.matrixBilin]
      · have hpquad : p ∈
            KHead.quadricPatch (attentionMatrix theta 0) h := by
          exact ⟨by simpa [KHead.firstHeadQuadric, KHead.firstHeadSlope] using hpq,
            hpw⟩
        have hpslice : p ∈ KHead.timeSlice R.region t := by
          rw [hOeq]
          exact ⟨hpO, hpquad⟩
        have hv := hvanish (p, t) hpslice
        simpa [ScalarDialForm.eval] using hv
    obtain ⟨c, hc, hsym⟩ :=
      KHead.lem_quadratic_quadric_rigidity hd
        (attentionMatrix theta 0 h) (Phi.Xfun t) (Phi.Yfun t)
        p0.1 p0.2 O hdetA hp0slice.2.2 hquad0 hOopen hp0slice.1 hvanishO
    exact ⟨⟨c, hc⟩, KHead.add_transpose_eq_zero_of_sym_eq_zero hsym⟩
  have hYzero : Phi.Ypoly + Phi.Ypolyᵀ = 0 := by
    apply KHead.matrix_eq_of_infinite_eval_eq _ _
      (KHead.timeProjection R.region) hJinf
    intro t ht
    simp only [KHead.eval_add, KHead.eval_transpose, eval_Ypoly,
      KHead.eval_zeroMatrix]
    exact (hslice t ht).2
  have hclub : ∀ t : Real, Phi.Yfun t + (Phi.Yfun t)ᵀ = 0 := by
    intro t
    have h := congrArg (KHead.evalPolynomialMatrix t) hYzero
    simpa using h
  obtain ⟨i0, j0, hij⟩ :
      ∃ i j, attentionMatrix theta 0 h i j ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hA0 : attentionMatrix theta 0 h = 0 := by
      ext i j
      exact hcon i j
    apply hdetA
    rw [hA0]
    haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    exact Matrix.det_zero this
  let gamma : Polynomial Real :=
    Polynomial.C ((attentionMatrix theta 0 h i0 j0)⁻¹) * Phi.Xpoly i0 j0
  have hXeq : Phi.Xpoly =
      gamma • KHead.liftC (attentionMatrix theta 0 h) := by
    apply KHead.matrix_eq_of_infinite_eval_eq _ _
      (KHead.timeProjection R.region) hJinf
    intro t ht
    obtain ⟨c, hc⟩ := (hslice t ht).1
    rw [KHead.eval_polySmul, KHead.eval_liftC, eval_Xpoly]
    have hentry : Polynomial.eval t (Phi.Xpoly i0 j0) =
        Phi.Xfun t i0 j0 := by
      have h := congrFun (congrFun (eval_Xpoly Phi t) i0) j0
      simpa [KHead.evalPolynomialMatrix] using h
    have hgamma : Polynomial.eval t gamma = c := by
      change Polynomial.eval t
        (Polynomial.C ((attentionMatrix theta 0 h i0 j0)⁻¹) *
          Phi.Xpoly i0 j0) = c
      rw [Polynomial.eval_mul, Polynomial.eval_C, hentry, hc]
      simp only [Matrix.smul_apply, smul_eq_mul]
      field_simp [hij]
    rw [hgamma, hc]
  have hmatrix :
      KHead.liftC (Phi.Cᵀ * Phi.H) -
          (Polynomial.X : Polynomial Real) •
            KHead.liftC (Phi.Vᵀ * Phi.H) =
        gamma • KHead.liftC (attentionMatrix theta 0 h) := by
    rw [← Phi.Xpoly_eq]
    exact hXeq
  have hentry : ∀ i j,
      Polynomial.C ((Phi.Cᵀ * Phi.H) i j) -
          Polynomial.X * Polynomial.C ((Phi.Vᵀ * Phi.H) i j) =
        gamma * Polynomial.C (attentionMatrix theta 0 h i j) := by
    intro i j
    have hijEq := congrFun (congrFun hmatrix i) j
    simpa only [Matrix.sub_apply, Matrix.smul_apply, KHead.liftC,
      Matrix.map_apply, smul_eq_mul] using hijEq
  have hc0 : Phi.Cᵀ * Phi.H =
      (gamma.coeff 0) • attentionMatrix theta 0 h := by
    ext i j
    have h := congrArg (fun p => p.coeff 0) (hentry i j)
    simp only [Matrix.smul_apply, smul_eq_mul]
    simpa [Polynomial.coeff_C, Polynomial.coeff_mul_C] using h
  have hc1 : -(Phi.Vᵀ * Phi.H) =
      (gamma.coeff 1) • attentionMatrix theta 0 h := by
    ext i j
    have h := congrArg (fun p => p.coeff 1) (hentry i j)
    simp only [Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
    simpa [Polynomial.coeff_C, Polynomial.coeff_mul_C,
      Polynomial.coeff_X_mul] using h
  obtain ⟨hgamma0, hgamma1⟩ :=
    Phi.gamma_eq_zero (attentionMatrix theta 0 h)
      (gamma.coeff 0) (gamma.coeff 1) hc0 hc1 hclub
      hdetC hdetA hsymA hVne
  refine ⟨?_, hYzero⟩
  have hC0 : Phi.Cᵀ * Phi.H = 0 := by
    rw [hc0, hgamma0, zero_smul]
  have hV0 : Phi.Vᵀ * Phi.H = 0 := by
    have h := hc1
    rw [hgamma1, zero_smul, neg_eq_zero] at h
    exact h
  rw [Phi.Xpoly_eq, hC0, hV0, KHead.liftC_zero, smul_zero, sub_zero]

end ScalarDialForm

end

end TransformerIdentifiability.NLayer.NoSkip
