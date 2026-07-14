import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Step2.Slices
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Gauge

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.NoSkip

/-!
# Dial coefficient extraction and the first interface gauge
-/

noncomputable section

/-- A matrix-valued affine function vanishing on a nonempty open dial set has
zero constant and linear coefficients. -/
theorem matrix_affine_coeff_eq_zero_of_eq_zero_on_open {k d : Nat}
    {O : Set (Fin k → Real)} (hO : IsOpen O) (hOne : O.Nonempty)
    (B : Matrix (Fin d) (Fin d) Real)
    (A : Fin k → Matrix (Fin d) (Fin d) Real)
    (hzero : ∀ t ∈ O, B + ∑ a : Fin k, t a • A a = 0) :
    B = 0 ∧ ∀ a, A a = 0 := by
  classical
  have hentry : ∀ i j, B i j = 0 ∧ ∀ a, A a i j = 0 := by
    intro i j
    let P : MvPolynomial (Fin k) Real :=
      MvPolynomial.C (B i j) +
        ∑ a : Fin k, MvPolynomial.X a * MvPolynomial.C (A a i j)
    have hP : P = 0 := by
      apply mvPolynomial_eq_zero_of_eval_eqOn_isOpen hO hOne
      intro t ht
      have hij := congrArg (fun M : Matrix (Fin d) (Fin d) Real => M i j)
        (hzero t ht)
      simpa [P, Matrix.add_apply, Matrix.sum_apply, Pi.smul_apply, smul_eq_mul]
        using hij
    have hB : B i j = 0 := by
      have h := congrArg (MvPolynomial.eval (fun _ : Fin k => (0 : Real))) hP
      simpa [P] using h
    refine ⟨hB, ?_⟩
    intro a
    have h := congrArg
      (MvPolynomial.eval (Pi.single a (1 : Real))) hP
    have hBA : B i j + A a i j = 0 := by
      have hsum : ∑ x : Fin k,
          (Pi.single a (1 : Real) : Fin k → Real) x * A x i j = A a i j := by
        rw [Finset.sum_eq_single a]
        · simp
        · intro b _hb hba
          simp [hba]
        · simp
      simpa [P, hsum] using h
    linarith
  constructor
  · ext i j
    exact (hentry i j).1
  · intro a
    ext i j
    exact (hentry i j).2 a

/-- Dial coefficient extraction in the exact matrix form used after
multi-quadric rigidity. -/
theorem dial_coefficients_of_limit_affine_vanishing {k d : Nat}
    {O : Set (Fin k → Real)} (hO : IsOpen O) (hOne : O.Nonempty)
    (E C K M' : Matrix (Fin d) (Fin d) Real)
    (V V' : Fin k → Matrix (Fin d) (Fin d) Real)
    (hzero : ∀ t ∈ O,
      E * C + ∑ a : Fin k, t a • (K * V a - M' * V' a) = 0) :
    E * C = 0 ∧ ∀ a, K * V a = M' * V' a := by
  obtain ⟨hconst, hlinear⟩ :=
    matrix_affine_coeff_eq_zero_of_eq_zero_on_open hO hOne (E * C)
      (fun a => K * V a - M' * V' a) hzero
  refine ⟨hconst, fun a => ?_⟩
  exact sub_eq_zero.mp (hlinear a)

/-- If a matrix maps a source head family onto a jointly-surjective target
family head by head, then the matrix itself is surjective. -/
theorem mulVec_surjective_of_maps_value_heads {L k d : Nat}
    {theta theta' : Params L k d} (l : Fin L)
    (hjoint : JointSurjective theta' l)
    (G : Matrix (Fin d) (Fin d) Real)
    (hmap : ∀ a : Fin k, G * valueMatrix theta l a = valueMatrix theta' l a) :
    Function.Surjective G.mulVec := by
  intro y
  rcases hjoint y with ⟨x, hx⟩
  refine ⟨∑ a : Fin k, valueMatrix theta l a *ᵥ (fun j => x (a, j)), ?_⟩
  rw [Matrix.mulVec_sum]
  calc
    ∑ a : Fin k, G *ᵥ (valueMatrix theta l a *ᵥ fun j => x (a, j)) =
        ∑ a : Fin k, valueMatrix theta' l a *ᵥ (fun j => x (a, j)) := by
          apply Finset.sum_congr rfl
          intro a _ha
          calc
            G *ᵥ (valueMatrix theta l a *ᵥ fun j => x (a, j)) =
                (G * valueMatrix theta l a) *ᵥ (fun j => x (a, j)) :=
              Matrix.mulVec_mulVec (fun j => x (a, j)) G (valueMatrix theta l a)
            _ = valueMatrix theta' l a *ᵥ (fun j => x (a, j)) := by rw [hmap a]
    _ = jointValueMatrix theta' l *ᵥ x := (jointValueMatrix_mulVec theta' l x).symm
    _ = y := hx

/-- Algebraic construction of the common first value gauge
`G = M'^{-1} K`. -/
noncomputable def commonValueGaugeMatrix {d : Nat}
    (M' K : Matrix (Fin d) (Fin d) Real)
    (hG : (M'⁻¹ * K).det ≠ 0) : GaugeMatrix d where
  matrix := M'⁻¹ * K
  det_ne_zero := hG

/-- Target joint surjectivity upgrades all headwise coefficient identities to
invertibility of the common value gauge. -/
theorem commonValueGauge_det_ne_zero {L k d : Nat}
    {theta theta' : Params L k d} (l : Fin L)
    (M' K : Matrix (Fin d) (Fin d) Real) (hM' : M'.det ≠ 0)
    (hcoeff : ∀ a : Fin k,
      K * valueMatrix theta l a = M' * valueMatrix theta' l a)
    (hjoint : JointSurjective theta' l) :
    (M'⁻¹ * K).det ≠ 0 := by
  have hMunit : IsUnit M'.det := hM'.isUnit
  have hmap : ∀ a : Fin k,
      (M'⁻¹ * K) * valueMatrix theta l a = valueMatrix theta' l a := by
    intro a
    calc
      (M'⁻¹ * K) * valueMatrix theta l a = M'⁻¹ * (K * valueMatrix theta l a) :=
        Matrix.mul_assoc _ _ _
      _ = M'⁻¹ * (M' * valueMatrix theta' l a) := by rw [hcoeff a]
      _ = (M'⁻¹ * M') * valueMatrix theta' l a := (Matrix.mul_assoc _ _ _).symm
      _ = valueMatrix theta' l a := by rw [Matrix.nonsing_inv_mul _ hMunit, Matrix.one_mul]
  have hsurj := mulVec_surjective_of_maps_value_heads l hjoint (M'⁻¹ * K) hmap
  have hunit : IsUnit (M'⁻¹ * K) :=
    Matrix.mulVec_surjective_iff_isUnit.mp hsurj
  exact ((Matrix.isUnit_iff_isUnit_det (A := M'⁻¹ * K)).mp hunit).ne_zero

/-- Packaged gauge plus its simultaneous first-value equations. -/
theorem exists_commonValueGauge {L k d : Nat}
    {theta theta' : Params L k d} (l : Fin L)
    (M' K : Matrix (Fin d) (Fin d) Real) (hM' : M'.det ≠ 0)
    (hcoeff : ∀ a : Fin k,
      K * valueMatrix theta l a = M' * valueMatrix theta' l a)
    (hjoint : JointSurjective theta' l) :
    ∃ G : GaugeMatrix d,
      G.matrix = M'⁻¹ * K ∧
        ∀ a : Fin k, G.matrix * valueMatrix theta l a = valueMatrix theta' l a := by
  let hdet := commonValueGauge_det_ne_zero l M' K hM' hcoeff hjoint
  let G := commonValueGaugeMatrix M' K hdet
  refine ⟨G, rfl, ?_⟩
  intro a
  dsimp [G, commonValueGaugeMatrix]
  have hMunit : IsUnit M'.det := hM'.isUnit
  calc
    (M'⁻¹ * K) * valueMatrix theta l a = M'⁻¹ * (K * valueMatrix theta l a) :=
      Matrix.mul_assoc _ _ _
    _ = M'⁻¹ * (M' * valueMatrix theta' l a) := by rw [hcoeff a]
    _ = (M'⁻¹ * M') * valueMatrix theta' l a := (Matrix.mul_assoc _ _ _).symm
    _ = valueMatrix theta' l a := by rw [Matrix.nonsing_inv_mul _ hMunit, Matrix.one_mul]

/-! ## Uniqueness and aggregate identities -/

/-- An invertible common left factor transfers joint surjectivity from the
target head family back to the source family. -/
theorem jointSurjective_source_of_gauge_maps_values {L k d : Nat}
    {theta theta' : Params L k d} (l : Fin L) (G : GaugeMatrix d)
    (hmap : ∀ a : Fin k,
      G.matrix * valueMatrix theta l a = valueMatrix theta' l a)
    (hjoint : JointSurjective theta' l) : JointSurjective theta l := by
  intro y
  rcases hjoint (G.matrix *ᵥ y) with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  have hGy : G.matrix *ᵥ (jointValueMatrix theta l *ᵥ x) =
      G.matrix *ᵥ y := calc
    G.matrix *ᵥ (jointValueMatrix theta l *ᵥ x) =
        G.matrix *ᵥ (∑ a : Fin k,
          valueMatrix theta l a *ᵥ (fun j => x (a, j))) := by
            rw [jointValueMatrix_mulVec]
    _ = ∑ a : Fin k,
          G.matrix *ᵥ (valueMatrix theta l a *ᵥ fun j => x (a, j)) :=
        by rw [Matrix.mulVec_sum]
    _ = ∑ a : Fin k,
          valueMatrix theta' l a *ᵥ (fun j => x (a, j)) := by
        apply Finset.sum_congr rfl
        intro a _ha
        rw [Matrix.mulVec_mulVec (fun j => x (a, j)) G.matrix
          (valueMatrix theta l a), hmap a]
    _ = jointValueMatrix theta' l *ᵥ x := (jointValueMatrix_mulVec theta' l x).symm
    _ = G.matrix *ᵥ y := hx
  calc
    jointValueMatrix theta l *ᵥ x =
        (G.invMatrix * G.matrix) *ᵥ (jointValueMatrix theta l *ᵥ x) := by simp
    _ = G.invMatrix *ᵥ (G.matrix *ᵥ (jointValueMatrix theta l *ᵥ x)) :=
      (Matrix.mulVec_mulVec _ _ _).symm
    _ = G.invMatrix *ᵥ (G.matrix *ᵥ y) := by rw [hGy]
    _ = (G.invMatrix * G.matrix) *ᵥ y := Matrix.mulVec_mulVec _ _ _
    _ = y := by rw [G.invMatrix_mul_matrix, Matrix.one_mulVec]

/-- The common first-interface gauge is unique. -/
theorem commonValueGauge_unique {L k d : Nat}
    {theta theta' : Params L k d} (l : Fin L)
    (G H : GaugeMatrix d)
    (hG : ∀ a : Fin k,
      G.matrix * valueMatrix theta l a = valueMatrix theta' l a)
    (hH : ∀ a : Fin k,
      H.matrix * valueMatrix theta l a = valueMatrix theta' l a)
    (hjoint : JointSurjective theta' l) : H = G := by
  have hsource := jointSurjective_source_of_gauge_maps_values l G hG hjoint
  apply GaugeMatrix.ext
  exact matrix_eq_of_mul_valueMatrices_eq_of_jointSurjective hsource
    (fun a => (hH a).trans (hG a).symm)

/-- Summing the headwise coefficient identities recovers the aggregate
first-layer transmission identity `K C₁ = M' C₁'`. -/
theorem aggregate_collapseMatrix_eq_of_head_coefficients {L k d : Nat}
    (theta theta' : Params L k d) (l : Fin L)
    (K M' : Matrix (Fin d) (Fin d) Real)
    (hcoeff : ∀ a : Fin k,
      K * valueMatrix theta l a = M' * valueMatrix theta' l a) :
    K * collapseMatrix theta l = M' * collapseMatrix theta' l := by
  simp only [collapseMatrix_eq_valueSum, valueSum]
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun a _ha => hcoeff a)

/-- From `K=M-E` and `E C₁=0`, the `v` coefficient may use `M` or `K`
interchangeably. -/
theorem saturatedM_collapse_eq_K_collapse {d : Nat}
    (M E K C : Matrix (Fin d) (Fin d) Real)
    (hK : K = M - E) (hEC : E * C = 0) : M * C = K * C := by
  rw [hK]
  rw [sub_mul, hEC, sub_zero]

/-- Combined recovery of the observable `v` coefficient. -/
theorem recovered_v_coefficient {d : Nat}
    (M E K M' C C' : Matrix (Fin d) (Fin d) Real)
    (hK : K = M - E) (hEC : E * C = 0) (hKC : K * C = M' * C') :
    M * C = M' * C' :=
  (saturatedM_collapse_eq_K_collapse M E K C hK hEC).trans hKC

end

end TransformerIdentifiability.NLayer.NoSkip
