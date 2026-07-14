import AnyLayerIdentifiabilityProof.NLayer.IDL.CascadeAlphaBranch

set_option autoImplicit false

open Filter Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer

/-!
# Boundedness and first delta estimates for the alpha branch

This file starts the finite-`τ` error infrastructure needed for the alpha branch of
`lem:cascade`.  The declarations below are deliberately conservative: they provide
eventual boundedness closure rules and abstract Lipschitz-to-exponential delta
estimates, but they do not assert the full `CascadeAlphaSlopeErrorBound`.
-/

/-! ## Eventually bounded real-valued functions -/

/-- A real-valued function is eventually bounded along `atTop`, with explicit data. -/
structure EventuallyBoundedReal (f : ℝ -> ℝ) where
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  start : ℝ
  bound : ∀ τ : ℝ, start ≤ τ -> |f τ| ≤ radius

namespace EventuallyBoundedReal

/-- Constructor from an explicit eventual absolute-value bound. -/
def of_bound {f : ℝ -> ℝ} (R : ℝ) (hR : 0 ≤ R) (T : ℝ)
    (h : ∀ τ : ℝ, T ≤ τ -> |f τ| ≤ R) :
    EventuallyBoundedReal f where
  radius := R
  radius_nonneg := hR
  start := T
  bound := h

/-- Constant functions are eventually bounded. -/
def const (a : ℝ) : EventuallyBoundedReal (fun _ : ℝ => a) :=
  of_bound |a| (abs_nonneg a) 0 (by
    intro τ _hτ
    rfl)

/-- Pointwise equal functions share eventual boundedness. -/
def congr_of_forall_eq {f g : ℝ -> ℝ}
    (h : EventuallyBoundedReal f) (hfg : ∀ τ : ℝ, f τ = g τ) :
    EventuallyBoundedReal g :=
  of_bound h.radius h.radius_nonneg h.start (by
    intro τ hτ
    simpa [← hfg τ] using h.bound τ hτ)

/-- Negating an eventually bounded function preserves eventual boundedness. -/
def neg {f : ℝ -> ℝ} (h : EventuallyBoundedReal f) :
    EventuallyBoundedReal (fun τ => -f τ) :=
  of_bound h.radius h.radius_nonneg h.start (by
    intro τ hτ
    simpa [abs_neg] using h.bound τ hτ)

/-- Sums of eventually bounded functions are eventually bounded. -/
def add {f g : ℝ -> ℝ} (hf : EventuallyBoundedReal f)
    (hg : EventuallyBoundedReal g) :
    EventuallyBoundedReal (fun τ => f τ + g τ) :=
  of_bound (hf.radius + hg.radius)
    (add_nonneg hf.radius_nonneg hg.radius_nonneg)
    (max hf.start hg.start) (by
      intro τ hτ
      have hτ_f : hf.start ≤ τ := le_trans (le_max_left _ _) hτ
      have hτ_g : hg.start ≤ τ := le_trans (le_max_right _ _) hτ
      calc
        |f τ + g τ| ≤ |f τ| + |g τ| := abs_add_le _ _
        _ ≤ hf.radius + hg.radius := add_le_add (hf.bound τ hτ_f) (hg.bound τ hτ_g))

/-- Differences of eventually bounded functions are eventually bounded. -/
def sub {f g : ℝ -> ℝ} (hf : EventuallyBoundedReal f)
    (hg : EventuallyBoundedReal g) :
    EventuallyBoundedReal (fun τ => f τ - g τ) :=
  (hf.add hg.neg).congr_of_forall_eq (by
    intro τ
    ring)

/-- Scalar multiples of eventually bounded functions are eventually bounded. -/
def const_mul {f : ℝ -> ℝ} (h : EventuallyBoundedReal f) (c : ℝ) :
    EventuallyBoundedReal (fun τ => c * f τ) :=
  of_bound (|c| * h.radius) (mul_nonneg (abs_nonneg c) h.radius_nonneg)
    h.start (by
      intro τ hτ
      calc
        |c * f τ| = |c| * |f τ| := abs_mul _ _
        _ ≤ |c| * h.radius :=
          mul_le_mul_of_nonneg_left (h.bound τ hτ) (abs_nonneg c))

/-- Right scalar multiples of eventually bounded functions are eventually bounded. -/
def mul_const {f : ℝ -> ℝ} (h : EventuallyBoundedReal f) (c : ℝ) :
    EventuallyBoundedReal (fun τ => f τ * c) :=
  (h.const_mul c).congr_of_forall_eq (by
    intro τ
    ring)

/-- Products of eventually bounded functions are eventually bounded. -/
def mul {f g : ℝ -> ℝ} (hf : EventuallyBoundedReal f)
    (hg : EventuallyBoundedReal g) :
    EventuallyBoundedReal (fun τ => f τ * g τ) :=
  of_bound (hf.radius * hg.radius)
    (mul_nonneg hf.radius_nonneg hg.radius_nonneg)
    (max hf.start hg.start) (by
      intro τ hτ
      have hτ_f : hf.start ≤ τ := le_trans (le_max_left _ _) hτ
      have hτ_g : hg.start ≤ τ := le_trans (le_max_right _ _) hτ
      calc
        |f τ * g τ| = |f τ| * |g τ| := abs_mul _ _
        _ ≤ hf.radius * hg.radius :=
          mul_le_mul (hf.bound τ hτ_f) (hg.bound τ hτ_g)
            (abs_nonneg (g τ)) hf.radius_nonneg)

/-- Sums over a finite type of eventually bounded functions are eventually bounded. -/
noncomputable def fintype_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ι -> ℝ -> ℝ) (hF : ∀ i : ι, EventuallyBoundedReal (F i)) :
    EventuallyBoundedReal (fun τ => ∑ i : ι, F i τ) :=
  of_bound (∑ i : ι, (hF i).radius)
    (by
      classical
      simpa using
        (Finset.sum_nonneg (s := (Finset.univ : Finset ι))
          (fun i _hi => (hF i).radius_nonneg)))
    (∑ i : ι, |(hF i).start|) (by
      classical
      intro τ hτ
      have hstart_le_sum :
          ∀ i : ι, (hF i).start ≤ ∑ j : ι, |(hF j).start| := by
        intro i
        have hle_abs : (hF i).start ≤ |(hF i).start| := le_abs_self _
        have habs_le_sum :
            |(hF i).start| ≤ ∑ j : ι, |(hF j).start| := by
          simpa using
            (Finset.single_le_sum
              (s := (Finset.univ : Finset ι))
              (f := fun j => |(hF j).start|)
              (fun j _hj => abs_nonneg ((hF j).start))
              (Finset.mem_univ i))
        exact le_trans hle_abs habs_le_sum
      have hτ_i : ∀ i : ι, (hF i).start ≤ τ :=
        fun i => le_trans (hstart_le_sum i) hτ
      calc
        |∑ i : ι, F i τ| ≤ ∑ i : ι, |F i τ| := by
          simpa using
            (Finset.abs_sum_le_sum_abs (fun i : ι => F i τ) Finset.univ)
        _ ≤ ∑ i : ι, (hF i).radius := by
          simpa using
            (Finset.sum_le_sum (s := (Finset.univ : Finset ι))
              (fun i _hi => (hF i).bound τ (hτ_i i))))

/-- The real sigmoid has a uniform eventual bound, after arbitrary precomposition. -/
noncomputable def sig_comp (f : ℝ -> ℝ) : EventuallyBoundedReal (fun τ => sig (f τ)) :=
  of_bound 1 zero_le_one 0 (by
    intro τ _hτ
    rw [abs_of_nonneg (sig_pos (f τ)).le]
    exact sig_le_one (f τ))

end EventuallyBoundedReal

namespace EventuallyExpClose

/-- Exponential closeness to a constant implies eventual boundedness. -/
noncomputable def eventuallyBoundedReal {f : ℝ -> ℝ} {a : ℝ}
    (h : EventuallyExpClose f a) :
    EventuallyBoundedReal f :=
  EventuallyBoundedReal.of_bound (|a| + h.coeff)
    (add_nonneg (abs_nonneg a) h.coeff_nonneg) (max h.start 0) (by
      intro τ hτ
      have hτ_start : h.start ≤ τ := le_trans (le_max_left _ _) hτ
      have hτ_nonneg : 0 ≤ τ := le_trans (le_max_right _ _) hτ
      have hexp_le_one : Real.exp (-h.rate * τ) ≤ 1 := by
        rw [← Real.exp_zero]
        apply Real.exp_le_exp.mpr
        nlinarith [h.rate_pos, hτ_nonneg]
      have htail :
          h.coeff * Real.exp (-h.rate * τ) ≤ h.coeff := by
        simpa using mul_le_mul_of_nonneg_left hexp_le_one h.coeff_nonneg
      calc
        |f τ| = |(f τ - a) + a| := by ring_nf
        _ ≤ |f τ - a| + |a| := abs_add_le _ _
        _ ≤ h.coeff * Real.exp (-h.rate * τ) + |a| :=
          add_le_add (h.bound τ hτ_start) (le_refl |a|)
        _ ≤ h.coeff + |a| := add_le_add htail (le_refl |a|)
        _ = |a| + h.coeff := by ring)

end EventuallyExpClose

namespace EventuallyExpClose

/-- A finite range sum of exponentially-small real-valued errors is exponentially
small. -/
noncomputable def sum_range_zero (N : Nat) {F : Nat -> ℝ -> ℝ}
    (hF : ∀ k : Nat, k < N -> EventuallyExpClose (F k) 0) :
    EventuallyExpClose (fun τ => (Finset.range N).sum (fun k => F k τ)) 0 := by
  classical
  induction N with
  | zero =>
      simpa using EventuallyExpClose.refl 0
  | succ N ih =>
      have hprev :
          EventuallyExpClose (fun τ => (Finset.range N).sum (fun k => F k τ)) 0 :=
        ih (by
          intro k hk
          exact hF k (Nat.lt_trans hk (Nat.lt_succ_self N)))
      have hlast : EventuallyExpClose (F N) 0 :=
        hF N (Nat.lt_succ_self N)
      simpa [Finset.sum_range_succ] using hprev.add hlast

end EventuallyExpClose

/-! ## Eventually bounded complex-valued functions -/

/-- A complex-valued function is eventually bounded along `atTop`, with explicit data. -/
structure EventuallyBoundedComplex (F : ℝ -> ℂ) where
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  start : ℝ
  bound : ∀ τ : ℝ, start ≤ τ -> ‖F τ‖ ≤ radius

namespace EventuallyBoundedComplex

/-- Constructor from an explicit eventual norm bound. -/
def of_bound {F : ℝ -> ℂ} (R : ℝ) (hR : 0 ≤ R) (T : ℝ)
    (h : ∀ τ : ℝ, T ≤ τ -> ‖F τ‖ ≤ R) :
    EventuallyBoundedComplex F where
  radius := R
  radius_nonneg := hR
  start := T
  bound := h

/-- Constant complex-valued functions are eventually bounded. -/
noncomputable def const (z : ℂ) : EventuallyBoundedComplex (fun _ : ℝ => z) :=
  of_bound ‖z‖ (norm_nonneg z) 0 (by
    intro τ _hτ
    rfl)

/-- Real eventual boundedness gives complex eventual boundedness after coercion. -/
def ofReal {f : ℝ -> ℝ} (hf : EventuallyBoundedReal f) :
    EventuallyBoundedComplex (fun τ => (f τ : ℂ)) :=
  of_bound hf.radius hf.radius_nonneg hf.start (by
    intro τ hτ
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hf.bound τ hτ)

/-- Pointwise equal complex-valued functions share eventual boundedness. -/
def congr_of_forall_eq {F G : ℝ -> ℂ}
    (h : EventuallyBoundedComplex F) (hFG : ∀ τ : ℝ, F τ = G τ) :
    EventuallyBoundedComplex G :=
  of_bound h.radius h.radius_nonneg h.start (by
    intro τ hτ
    simpa [← hFG τ] using h.bound τ hτ)

/-- Negating an eventually bounded complex-valued function preserves boundedness. -/
def neg {F : ℝ -> ℂ} (h : EventuallyBoundedComplex F) :
    EventuallyBoundedComplex (fun τ => -F τ) :=
  of_bound h.radius h.radius_nonneg h.start (by
    intro τ hτ
    simpa using h.bound τ hτ)

/-- Sums of eventually bounded complex-valued functions are eventually bounded. -/
def add {F G : ℝ -> ℂ} (hF : EventuallyBoundedComplex F)
    (hG : EventuallyBoundedComplex G) :
    EventuallyBoundedComplex (fun τ => F τ + G τ) :=
  of_bound (hF.radius + hG.radius)
    (add_nonneg hF.radius_nonneg hG.radius_nonneg)
    (max hF.start hG.start) (by
      intro τ hτ
      have hτ_F : hF.start ≤ τ := le_trans (le_max_left _ _) hτ
      have hτ_G : hG.start ≤ τ := le_trans (le_max_right _ _) hτ
      calc
        ‖F τ + G τ‖ ≤ ‖F τ‖ + ‖G τ‖ := norm_add_le _ _
        _ ≤ hF.radius + hG.radius := add_le_add (hF.bound τ hτ_F) (hG.bound τ hτ_G))

/-- Differences of eventually bounded complex-valued functions are eventually bounded. -/
def sub {F G : ℝ -> ℂ} (hF : EventuallyBoundedComplex F)
    (hG : EventuallyBoundedComplex G) :
    EventuallyBoundedComplex (fun τ => F τ - G τ) :=
  (hF.add hG.neg).congr_of_forall_eq (by
    intro τ
    ring)

/-- Complex scalar multiples of eventually bounded functions are eventually bounded. -/
noncomputable def const_mul {F : ℝ -> ℂ} (hF : EventuallyBoundedComplex F) (z : ℂ) :
    EventuallyBoundedComplex (fun τ => z * F τ) :=
  of_bound (‖z‖ * hF.radius) (mul_nonneg (norm_nonneg z) hF.radius_nonneg)
    hF.start (by
      intro τ hτ
      calc
        ‖z * F τ‖ = ‖z‖ * ‖F τ‖ := norm_mul _ _
        _ ≤ ‖z‖ * hF.radius :=
          mul_le_mul_of_nonneg_left (hF.bound τ hτ) (norm_nonneg z))

/-- Products of eventually bounded complex-valued functions are eventually bounded. -/
def mul {F G : ℝ -> ℂ} (hF : EventuallyBoundedComplex F)
    (hG : EventuallyBoundedComplex G) :
    EventuallyBoundedComplex (fun τ => F τ * G τ) :=
  of_bound (hF.radius * hG.radius)
    (mul_nonneg hF.radius_nonneg hG.radius_nonneg)
    (max hF.start hG.start) (by
      intro τ hτ
      have hτ_F : hF.start ≤ τ := le_trans (le_max_left _ _) hτ
      have hτ_G : hG.start ≤ τ := le_trans (le_max_right _ _) hτ
      calc
        ‖F τ * G τ‖ = ‖F τ‖ * ‖G τ‖ := norm_mul _ _
        _ ≤ hF.radius * hG.radius :=
          mul_le_mul (hF.bound τ hτ_F) (hG.bound τ hτ_G)
            (norm_nonneg (G τ)) hF.radius_nonneg)

/-- Sums over a finite type of eventually bounded complex functions are eventually bounded. -/
noncomputable def fintype_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ι -> ℝ -> ℂ) (hF : ∀ i : ι, EventuallyBoundedComplex (F i)) :
    EventuallyBoundedComplex (fun τ => ∑ i : ι, F i τ) :=
  of_bound (∑ i : ι, (hF i).radius)
    (by
      classical
      simpa using
        (Finset.sum_nonneg (s := (Finset.univ : Finset ι))
          (fun i _hi => (hF i).radius_nonneg)))
    (∑ i : ι, |(hF i).start|) (by
      classical
      intro τ hτ
      have hstart_le_sum :
          ∀ i : ι, (hF i).start ≤ ∑ j : ι, |(hF j).start| := by
        intro i
        have hle_abs : (hF i).start ≤ |(hF i).start| := le_abs_self _
        have habs_le_sum :
            |(hF i).start| ≤ ∑ j : ι, |(hF j).start| := by
          simpa using
            (Finset.single_le_sum
              (s := (Finset.univ : Finset ι))
              (f := fun j => |(hF j).start|)
              (fun j _hj => abs_nonneg ((hF j).start))
              (Finset.mem_univ i))
        exact le_trans hle_abs habs_le_sum
      have hτ_i : ∀ i : ι, (hF i).start ≤ τ :=
        fun i => le_trans (hstart_le_sum i) hτ
      calc
        ‖∑ i : ι, F i τ‖ ≤ ∑ i : ι, ‖F i τ‖ := by
          simpa using
            (norm_sum_le (Finset.univ : Finset ι) (fun i : ι => F i τ))
        _ ≤ ∑ i : ι, (hF i).radius := by
          simpa using
            (Finset.sum_le_sum (s := (Finset.univ : Finset ι))
              (fun i _hi => (hF i).bound τ (hτ_i i))))

/-- Taking the complex norm of an eventually bounded complex function gives an
eventually bounded real function. -/
noncomputable def norm {F : ℝ -> ℂ} (hF : EventuallyBoundedComplex F) :
    EventuallyBoundedReal (fun τ => ‖F τ‖) :=
  EventuallyBoundedReal.of_bound hF.radius hF.radius_nonneg hF.start (by
    intro τ hτ
    rw [abs_of_nonneg (norm_nonneg (F τ))]
    exact hF.bound τ hτ)

end EventuallyBoundedComplex

/-! ## Eventually bounded probe paths -/

/-- Componentwise eventual boundedness for a probe-pair path. -/
structure EventuallyBoundedProbePair {d : Nat} (P : ℝ -> ProbePair d) where
  fst : ∀ i : Fin d, EventuallyBoundedReal (fun τ => (P τ).1 i)
  snd : ∀ i : Fin d, EventuallyBoundedReal (fun τ => (P τ).2 i)

namespace EventuallyBoundedProbePair

/-- Constant probe paths are eventually bounded. -/
def const {d : Nat} (p : ProbePair d) :
    EventuallyBoundedProbePair (fun _ : ℝ => p) where
  fst i := EventuallyBoundedReal.const (p.1 i)
  snd i := EventuallyBoundedReal.const (p.2 i)

/-- Bounded probe paths have bounded matrix-bilinear slopes. -/
noncomputable def matrixBilin {d : Nat} (A : Matrix (Fin d) (Fin d) ℝ)
    {P : ℝ -> ProbePair d} (hP : EventuallyBoundedProbePair P) :
    EventuallyBoundedReal
      (fun τ => TransformerIdentifiability.NLayer.matrixBilin A (P τ).1 (P τ).2) := by
  classical
  let term : Fin d × Fin d -> ℝ -> ℝ :=
    fun ij τ => (P τ).1 ij.1 * (A ij.1 ij.2 * (P τ).2 ij.2)
  have hterm : ∀ ij : Fin d × Fin d, EventuallyBoundedReal (term ij) := by
    intro ij
    exact (hP.fst ij.1).mul ((hP.snd ij.2).const_mul (A ij.1 ij.2))
  have hsum : EventuallyBoundedReal (fun τ => ∑ ij : Fin d × Fin d, term ij τ) :=
    EventuallyBoundedReal.fintype_sum term hterm
  exact hsum.congr_of_forall_eq (by
    intro τ
    calc
      (∑ ij : Fin d × Fin d, term ij τ)
          = ∑ i : Fin d, ∑ j : Fin d, (P τ).1 i * (A i j * (P τ).2 j) := by
            rw [← Finset.univ_product_univ, Finset.sum_product]
      _ = TransformerIdentifiability.NLayer.matrixBilin A (P τ).1 (P τ).2 := by
            simp [TransformerIdentifiability.NLayer.matrixBilin, Matrix.mulVec,
              dotProduct, Finset.mul_sum])

end EventuallyBoundedProbePair

/-! ## Honest Lipschitz-to-exponential delta estimates -/

/-- The theorem-shaped scalar delta estimate used by the alpha-error work.

This package is intentionally narrow: it says that the difference between two displayed
real-valued quantities is eventually Lipschitz-controlled by one exponentially small
gate-coordinate error.  It does not mention the cascade slope package and does not
assert any alpha-branch conclusion by itself. -/
structure CascadeAlphaDeltaEstimateData (gate : ℝ -> ℝ) (limit : ℝ)
    (actual formal : ℝ -> ℝ) where
  lipschitzConstant : ℝ
  lipschitz_nonneg : 0 ≤ lipschitzConstant
  start : ℝ
  delta_bound :
    ∀ τ : ℝ, start ≤ τ ->
      |actual τ - formal τ| ≤ lipschitzConstant * |gate τ - limit|

/-- If a delta is eventually Lipschitz-controlled by an exponentially small scalar
error, then the delta is exponentially close to zero. -/
noncomputable def eventuallyExpClose_delta_of_eventual_lipschitz
    {x delta : ℝ -> ℝ} {a K T : ℝ}
    (hx : EventuallyExpClose x a) (hK : 0 ≤ K)
    (hdelta : ∀ τ : ℝ, T ≤ τ -> |delta τ| ≤ K * |x τ - a|) :
    EventuallyExpClose delta 0 := by
  refine
    ⟨hx.rate, hx.rate_pos, K * hx.coeff,
      mul_nonneg hK hx.coeff_nonneg, max hx.start T, ?_⟩
  intro τ hτ
  have hτ_x : hx.start ≤ τ := le_trans (le_max_left _ _) hτ
  have hτ_T : T ≤ τ := le_trans (le_max_right _ _) hτ
  calc
    |delta τ - 0| = |delta τ| := by rw [sub_zero]
    _ ≤ K * |x τ - a| := hdelta τ hτ_T
    _ ≤ K * (hx.coeff * Real.exp (-hx.rate * τ)) :=
      mul_le_mul_of_nonneg_left (hx.bound τ hτ_x) hK
    _ = K * hx.coeff * Real.exp (-hx.rate * τ) := by ring

namespace CascadeAlphaDeltaEstimateData

end CascadeAlphaDeltaEstimateData

/-! ## Polynomial one-coordinate Lipschitz constants -/

/-- Product of the box radii for every coordinate except the active slice coordinate. -/
noncomputable def polynomialSliceOffRadius {K : Nat} (coord : Fin K)
    (R : Fin K -> ℝ) (m : Fin K →₀ Nat) : ℝ :=
  ∏ j ∈ (Finset.univ.erase coord), R j ^ m j

theorem polynomialSliceOffRadius_nonneg {K : Nat} (coord : Fin K)
    (R : Fin K -> ℝ) (m : Fin K →₀ Nat) (hR : ∀ j, 0 ≤ R j) :
    0 ≤ polynomialSliceOffRadius coord R m := by
  unfold polynomialSliceOffRadius
  exact Finset.prod_nonneg (fun j _hj => pow_nonneg (hR j) (m j))

theorem polynomialSlice_off_prod_norm_le {K : Nat}
    (coord : Fin K) (R x : Fin K -> ℝ) (m : Fin K →₀ Nat)
    (_hR : ∀ j, 0 ≤ R j) (hx : ∀ j, |x j| ≤ R j) :
    ‖∏ j ∈ m.support.erase coord, ((x j : ℂ) ^ m j)‖ ≤
      polynomialSliceOffRadius coord R m := by
  rw [norm_prod]
  have hprod_le :
      (∏ j ∈ m.support.erase coord, ‖(x j : ℂ) ^ m j‖) ≤
        ∏ j ∈ m.support.erase coord, R j ^ m j := by
    refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) ?_
    intro j _hj
    rw [norm_pow]
    have hnorm : ‖(x j : ℂ)‖ = |x j| :=
      RCLike.norm_ofReal (K := ℂ) (x j)
    rw [hnorm]
    exact pow_le_pow_left₀ (abs_nonneg (x j)) (hx j) (m j)
  have hsubset : m.support.erase coord ⊆ Finset.univ.erase coord := by
    intro j hj
    rw [Finset.mem_erase] at hj ⊢
    exact ⟨hj.1, Finset.mem_univ j⟩
  have hprod_eq :
      (∏ j ∈ m.support.erase coord, R j ^ m j) =
        ∏ j ∈ Finset.univ.erase coord, R j ^ m j := by
    refine Finset.prod_subset hsubset ?_
    intro j hjbig hjsmall
    have hj_not_support : j ∉ m.support := by
      intro hjsupp
      exact hjsmall (by
        rw [Finset.mem_erase]
        rw [Finset.mem_erase] at hjbig
        exact ⟨hjbig.1, hjsupp⟩)
    have hmj : m j = 0 := by
      by_contra hne
      exact hj_not_support ((Finsupp.mem_support_iff).mpr hne)
    simp [hmj]
  exact hprod_le.trans_eq hprod_eq

/-- A single monomial is Lipschitz in one real coordinate on a coordinate box. -/
theorem monomial_prod_diff_norm_le_polynomialSlice {K : Nat}
    (coord : Fin K) (R x y : Fin K -> ℝ) (m : Fin K →₀ Nat)
    (hR : ∀ j, 0 ≤ R j) (hx : ∀ j, |x j| ≤ R j)
    (hy : ∀ j, |y j| ≤ R j)
    (heq : ∀ j, j ≠ coord -> x j = y j) :
    ‖(∏ j ∈ m.support, ((x j : ℂ) ^ m j)) -
        (∏ j ∈ m.support, ((y j : ℂ) ^ m j))‖ ≤
      (((m coord : ℝ) * R coord ^ (m coord - 1)) *
          polynomialSliceOffRadius coord R m) * |x coord - y coord| := by
  by_cases hcoord : coord ∈ m.support
  · have hxprod :
        (∏ j ∈ m.support, ((x j : ℂ) ^ m j)) =
          (x coord : ℂ) ^ m coord *
            ∏ j ∈ m.support.erase coord, ((x j : ℂ) ^ m j) := by
      rw [Finset.mul_prod_erase m.support (fun j => ((x j : ℂ) ^ m j)) hcoord]
    have hyprod :
        (∏ j ∈ m.support, ((y j : ℂ) ^ m j)) =
          (y coord : ℂ) ^ m coord *
            ∏ j ∈ m.support.erase coord, ((y j : ℂ) ^ m j) := by
      rw [Finset.mul_prod_erase m.support (fun j => ((y j : ℂ) ^ m j)) hcoord]
    have hoffeq :
        (∏ j ∈ m.support.erase coord, ((x j : ℂ) ^ m j)) =
          ∏ j ∈ m.support.erase coord, ((y j : ℂ) ^ m j) := by
      refine Finset.prod_congr rfl ?_
      intro j hj
      rw [Finset.mem_erase] at hj
      rw [heq j hj.1]
    rw [hxprod, hyprod, ← hoffeq, ← sub_mul]
    have hpowNorm :
        ‖(x coord : ℂ) ^ m coord - (y coord : ℂ) ^ m coord‖ =
          |x coord ^ m coord - y coord ^ m coord| := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_sub]
      exact RCLike.norm_ofReal (K := ℂ)
        (x coord ^ m coord - y coord ^ m coord)
    have hmax_nonneg : 0 ≤ max |x coord| |y coord| :=
      le_max_of_le_left (abs_nonneg (x coord))
    have hmax_le : max |x coord| |y coord| ≤ R coord :=
      max_le (hx coord) (hy coord)
    have hpowBound :
        ‖(x coord : ℂ) ^ m coord - (y coord : ℂ) ^ m coord‖ ≤
          |x coord - y coord| * (m coord : ℝ) * R coord ^ (m coord - 1) := by
      rw [hpowNorm]
      have hbase := abs_pow_sub_pow_le (x coord) (y coord) (m coord)
      have hpowR :
          max |x coord| |y coord| ^ (m coord - 1) ≤
            R coord ^ (m coord - 1) :=
        pow_le_pow_left₀ hmax_nonneg hmax_le (m coord - 1)
      exact hbase.trans
        (mul_le_mul_of_nonneg_left hpowR
          (mul_nonneg (abs_nonneg (x coord - y coord))
            (Nat.cast_nonneg (m coord))))
    have hoffBound := polynomialSlice_off_prod_norm_le coord R x m hR hx
    have hpowBound_nonneg :
        0 ≤ |x coord - y coord| * (m coord : ℝ) * R coord ^ (m coord - 1) := by
      exact mul_nonneg
        (mul_nonneg (abs_nonneg (x coord - y coord))
          (Nat.cast_nonneg (m coord)))
        (pow_nonneg (hR coord) (m coord - 1))
    calc
      ‖((x coord : ℂ) ^ m coord - (y coord : ℂ) ^ m coord) *
          (∏ j ∈ m.support.erase coord, ((x j : ℂ) ^ m j))‖
          = ‖(x coord : ℂ) ^ m coord - (y coord : ℂ) ^ m coord‖ *
              ‖∏ j ∈ m.support.erase coord, ((x j : ℂ) ^ m j)‖ := norm_mul _ _
      _ ≤ (|x coord - y coord| * (m coord : ℝ) * R coord ^ (m coord - 1)) *
            polynomialSliceOffRadius coord R m :=
        mul_le_mul hpowBound hoffBound (norm_nonneg _) hpowBound_nonneg
      _ = (((m coord : ℝ) * R coord ^ (m coord - 1)) *
            polynomialSliceOffRadius coord R m) * |x coord - y coord| := by
          ring
  · have hprod_eq :
        (∏ j ∈ m.support, ((x j : ℂ) ^ m j)) =
          ∏ j ∈ m.support, ((y j : ℂ) ^ m j) := by
      refine Finset.prod_congr rfl ?_
      intro j hj
      have hji : j ≠ coord := by
        intro hji
        subst hji
        exact hcoord hj
      rw [heq j hji]
    rw [hprod_eq, sub_self, norm_zero]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (Nat.cast_nonneg (m coord))
          (pow_nonneg (hR coord) (m coord - 1)))
        (polynomialSliceOffRadius_nonneg coord R m hR))
      (abs_nonneg (x coord - y coord))

/-- Explicit coefficient-sum Lipschitz constant for changing one real coordinate of a
finite multivariate complex polynomial on the real box `|x_j| ≤ R_j`. -/
noncomputable def polynomialSliceLipschitzConstant {K : Nat}
    (p : GatePoly K) (coord : Fin K) (R : Fin K -> ℝ) : ℝ :=
  ∑ m ∈ p.support,
    ‖MvPolynomial.coeff m p‖ *
      (((m coord : ℝ) * R coord ^ (m coord - 1)) *
        polynomialSliceOffRadius coord R m)

theorem polynomialSliceLipschitzConstant_nonneg {K : Nat}
    (p : GatePoly K) (coord : Fin K) (R : Fin K -> ℝ)
    (hR : ∀ j, 0 ≤ R j) :
    0 ≤ polynomialSliceLipschitzConstant p coord R := by
  unfold polynomialSliceLipschitzConstant
  exact Finset.sum_nonneg (fun m _hm =>
    mul_nonneg (norm_nonneg _)
      (mul_nonneg
        (mul_nonneg (Nat.cast_nonneg (m coord))
          (pow_nonneg (hR coord) (m coord - 1)))
        (polynomialSliceOffRadius_nonneg coord R m hR)))

/-- Finite-support polynomial Lipschitz bound for one real coordinate. -/
theorem eval_sub_eval_norm_le_polynomialSliceLipschitzConstant {K : Nat}
    (p : GatePoly K) (coord : Fin K) (R x y : Fin K -> ℝ)
    (hR : ∀ j, 0 ≤ R j) (hx : ∀ j, |x j| ≤ R j)
    (hy : ∀ j, |y j| ≤ R j)
    (heq : ∀ j, j ≠ coord -> x j = y j) :
    ‖MvPolynomial.eval (fun j => (x j : ℂ)) p -
        MvPolynomial.eval (fun j => (y j : ℂ)) p‖ ≤
      polynomialSliceLipschitzConstant p coord R * |x coord - y coord| := by
  have hdiff :
      MvPolynomial.eval (fun j => (x j : ℂ)) p -
          MvPolynomial.eval (fun j => (y j : ℂ)) p =
        ∑ m ∈ p.support,
          MvPolynomial.coeff m p *
            ((∏ j ∈ m.support, ((x j : ℂ) ^ m j)) -
              (∏ j ∈ m.support, ((y j : ℂ) ^ m j))) := by
    rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro m _hm
    ring
  rw [hdiff]
  calc
    ‖∑ m ∈ p.support,
        MvPolynomial.coeff m p *
          ((∏ j ∈ m.support, ((x j : ℂ) ^ m j)) -
            ∏ j ∈ m.support, ((y j : ℂ) ^ m j))‖
        ≤ ∑ m ∈ p.support,
            ‖MvPolynomial.coeff m p *
              ((∏ j ∈ m.support, ((x j : ℂ) ^ m j)) -
                ∏ j ∈ m.support, ((y j : ℂ) ^ m j))‖ :=
      norm_sum_le p.support (fun m => MvPolynomial.coeff m p *
        ((∏ j ∈ m.support, ((x j : ℂ) ^ m j)) -
          ∏ j ∈ m.support, ((y j : ℂ) ^ m j)))
    _ ≤ ∑ m ∈ p.support,
          (‖MvPolynomial.coeff m p‖ *
            (((m coord : ℝ) * R coord ^ (m coord - 1)) *
              polynomialSliceOffRadius coord R m)) *
            |x coord - y coord| := by
      refine Finset.sum_le_sum ?_
      intro m _hm
      rw [norm_mul]
      have hmon :=
        monomial_prod_diff_norm_le_polynomialSlice coord R x y m hR hx hy heq
      calc
        ‖MvPolynomial.coeff m p‖ *
            ‖(∏ j ∈ m.support, ((x j : ℂ) ^ m j)) -
              ∏ j ∈ m.support, ((y j : ℂ) ^ m j)‖
            ≤ ‖MvPolynomial.coeff m p‖ *
                ((((m coord : ℝ) * R coord ^ (m coord - 1)) *
                    polynomialSliceOffRadius coord R m) * |x coord - y coord|) :=
          mul_le_mul_of_nonneg_left hmon (norm_nonneg _)
        _ = (‖MvPolynomial.coeff m p‖ *
              (((m coord : ℝ) * R coord ^ (m coord - 1)) *
                polynomialSliceOffRadius coord R m)) *
              |x coord - y coord| := by
            ring
    _ = polynomialSliceLipschitzConstant p coord R * |x coord - y coord| := by
      unfold polynomialSliceLipschitzConstant
      rw [Finset.sum_mul]

theorem eval_re_sub_eval_re_le_polynomialSliceLipschitzConstant {K : Nat}
    (p : GatePoly K) (coord : Fin K) (R x y : Fin K -> ℝ)
    (hR : ∀ j, 0 ≤ R j) (hx : ∀ j, |x j| ≤ R j)
    (hy : ∀ j, |y j| ≤ R j)
    (heq : ∀ j, j ≠ coord -> x j = y j) :
    |(MvPolynomial.eval (fun j => (x j : ℂ)) p).re -
        (MvPolynomial.eval (fun j => (y j : ℂ)) p).re| ≤
      polynomialSliceLipschitzConstant p coord R * |x coord - y coord| := by
  let X := MvPolynomial.eval (fun j => (x j : ℂ)) p
  let Y := MvPolynomial.eval (fun j => (y j : ℂ)) p
  have hre : |X.re - Y.re| ≤ ‖X - Y‖ := by
    simpa [X, Y, sub_eq_add_neg] using Complex.abs_re_le_norm (X - Y)
  exact hre.trans
    (eval_sub_eval_norm_le_polynomialSliceLipschitzConstant p coord R x y hR hx hy heq)

theorem specializedPhi_eq_eval_formalPhiPoly {L d : Nat}
    (θ : Params L d) (level : Nat) (z : Nat -> ℂ) (p : ProbePair d) :
    specializedPhi θ level z p =
      MvPolynomial.eval (fun i : Fin level => z i)
        (formalPhiPoly (K := level) (paramStream θ) level p.1 p.2) := by
  rw [specializedPhi, eval_formalPhiPoly]
  symm
  exact formalPhi_congr_of_eqOn_lt (paramStream θ) p.1 p.2 (by
    intro i hi
    rw [extendGate]
    simp [hi])

/-- The explicit coefficient-sum constant for a `specializedPhi` slice at a probe
pair.  Bounding this scalar along a path is the remaining compactness/coefficient task. -/
noncomputable def formalPhiSliceLipschitzConstant {L d : Nat}
    (θ : Params L d) (level : Nat) (coord : Fin level)
    (R : Fin level -> ℝ) (p : ProbePair d) : ℝ :=
  polynomialSliceLipschitzConstant
    (formalPhiPoly (K := level) (paramStream θ) level p.1 p.2) coord R

/-! ## Eventual boundedness of formal-phi coefficients -/

/-- A path of gate polynomials has eventually bounded coefficients. -/
abbrev EventuallyBoundedGatePolyCoeffs {K : Nat} (P : ℝ -> GatePoly K) : Type :=
  ∀ m : Fin K →₀ Nat, EventuallyBoundedComplex (fun τ => MvPolynomial.coeff m (P τ))

namespace EventuallyBoundedGatePolyCoeffs

noncomputable def const {K : Nat} (p : GatePoly K) :
    EventuallyBoundedGatePolyCoeffs (fun _ : ℝ => p) :=
  fun m => EventuallyBoundedComplex.const (MvPolynomial.coeff m p)

noncomputable def C_ofReal {K : Nat} {f : ℝ -> ℝ}
    (hf : EventuallyBoundedReal f) :
    EventuallyBoundedGatePolyCoeffs
      (fun τ => MvPolynomial.C (σ := Fin K) ((f τ : ℂ))) := by
  intro m
  by_cases hm : (0 : Fin K →₀ Nat) = m
  · refine (EventuallyBoundedComplex.ofReal hf).congr_of_forall_eq ?_
    intro τ
    simp [MvPolynomial.coeff_C, hm]
  · exact (EventuallyBoundedComplex.const 0).congr_of_forall_eq (by
      intro τ
      simp [MvPolynomial.coeff_C, hm])

noncomputable def add {K : Nat} {P Q : ℝ -> GatePoly K}
    (hP : EventuallyBoundedGatePolyCoeffs P)
    (hQ : EventuallyBoundedGatePolyCoeffs Q) :
    EventuallyBoundedGatePolyCoeffs (fun τ => P τ + Q τ) := by
  intro m
  exact ((hP m).add (hQ m)).congr_of_forall_eq (by
    intro τ
    simp [MvPolynomial.coeff_add])

noncomputable def sub {K : Nat} {P Q : ℝ -> GatePoly K}
    (hP : EventuallyBoundedGatePolyCoeffs P)
    (hQ : EventuallyBoundedGatePolyCoeffs Q) :
    EventuallyBoundedGatePolyCoeffs (fun τ => P τ - Q τ) := by
  intro m
  exact ((hP m).sub (hQ m)).congr_of_forall_eq (by
    intro τ
    simp [MvPolynomial.coeff_sub])

noncomputable def mul {K : Nat} {P Q : ℝ -> GatePoly K}
    (hP : EventuallyBoundedGatePolyCoeffs P)
    (hQ : EventuallyBoundedGatePolyCoeffs Q) :
    EventuallyBoundedGatePolyCoeffs (fun τ => P τ * Q τ) := by
  classical
  intro m
  let term : {x // x ∈ Finset.antidiagonal m} -> ℝ -> ℂ :=
    fun x τ => MvPolynomial.coeff x.1.1 (P τ) * MvPolynomial.coeff x.1.2 (Q τ)
  have hterm : ∀ x : {x // x ∈ Finset.antidiagonal m}, EventuallyBoundedComplex (term x) := by
    intro x
    exact (hP x.1.1).mul (hQ x.1.2)
  have hsum :
      EventuallyBoundedComplex
        (fun τ => ∑ x : {x // x ∈ Finset.antidiagonal m}, term x τ) :=
    EventuallyBoundedComplex.fintype_sum term hterm
  exact hsum.congr_of_forall_eq (by
    intro τ
    symm
    rw [MvPolynomial.coeff_mul]
    exact Finset.sum_subtype (s := Finset.antidiagonal m)
      (h := fun x => Iff.rfl)
      (f := fun x => MvPolynomial.coeff x.1 (P τ) * MvPolynomial.coeff x.2 (Q τ)))

noncomputable def fintype_sum {K : Nat} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι -> ℝ -> GatePoly K)
    (hP : ∀ i : ι, EventuallyBoundedGatePolyCoeffs (P i)) :
    EventuallyBoundedGatePolyCoeffs (fun τ => ∑ i : ι, P i τ) := by
  intro m
  have hsum : EventuallyBoundedComplex
      (fun τ => ∑ i : ι, MvPolynomial.coeff m (P i τ)) :=
    EventuallyBoundedComplex.fintype_sum
      (fun i τ => MvPolynomial.coeff m (P i τ)) (fun i => hP i m)
  exact hsum.congr_of_forall_eq (by
    intro τ
    simp [MvPolynomial.coeff_sum])

end EventuallyBoundedGatePolyCoeffs

abbrev EventuallyBoundedGatePolyVectorCoeffs {K n : Nat} (v : ℝ -> Fin n -> GatePoly K) :
    Type :=
  ∀ i : Fin n, EventuallyBoundedGatePolyCoeffs (fun τ => v τ i)

abbrev EventuallyBoundedGatePolyMatrixCoeffs {K m n : Nat}
    (A : ℝ -> Matrix (Fin m) (Fin n) (GatePoly K)) : Type :=
  ∀ i : Fin m, ∀ j : Fin n, EventuallyBoundedGatePolyCoeffs (fun τ => A τ i j)

namespace EventuallyBoundedGatePolyVectorCoeffs

noncomputable def const {K n : Nat} (v : Fin n -> GatePoly K) :
    EventuallyBoundedGatePolyVectorCoeffs (fun _ : ℝ => v) :=
  fun i => EventuallyBoundedGatePolyCoeffs.const (v i)

noncomputable def add {K n : Nat} {u v : ℝ -> Fin n -> GatePoly K}
    (hu : EventuallyBoundedGatePolyVectorCoeffs u)
    (hv : EventuallyBoundedGatePolyVectorCoeffs v) :
    EventuallyBoundedGatePolyVectorCoeffs (fun τ => u τ + v τ) :=
  fun i => (hu i).add (hv i)

noncomputable def smul {K n : Nat} {c : ℝ -> GatePoly K} {v : ℝ -> Fin n -> GatePoly K}
    (hc : EventuallyBoundedGatePolyCoeffs c)
    (hv : EventuallyBoundedGatePolyVectorCoeffs v) :
    EventuallyBoundedGatePolyVectorCoeffs (fun τ => c τ • v τ) :=
  fun i => hc.mul (hv i)

noncomputable def matVecMul {K m n : Nat} {A : ℝ -> Matrix (Fin m) (Fin n) (GatePoly K)}
    {v : ℝ -> Fin n -> GatePoly K}
    (hA : EventuallyBoundedGatePolyMatrixCoeffs A)
    (hv : EventuallyBoundedGatePolyVectorCoeffs v) :
    EventuallyBoundedGatePolyVectorCoeffs (fun τ => A τ *ᵥ v τ) := by
  classical
  intro i
  let term : Fin n -> ℝ -> GatePoly K := fun j τ => A τ i j * v τ j
  have hterm : ∀ j : Fin n, EventuallyBoundedGatePolyCoeffs (term j) :=
    fun j => (hA i j).mul (hv j)
  intro m
  exact ((EventuallyBoundedGatePolyCoeffs.fintype_sum term hterm) m).congr_of_forall_eq (by
    intro τ
    simp [term, Matrix.mulVec, dotProduct])

end EventuallyBoundedGatePolyVectorCoeffs

namespace EventuallyBoundedGatePolyMatrixCoeffs

noncomputable def const {K m n : Nat} (A : Matrix (Fin m) (Fin n) (GatePoly K)) :
    EventuallyBoundedGatePolyMatrixCoeffs (fun _ : ℝ => A) :=
  fun i j => EventuallyBoundedGatePolyCoeffs.const (A i j)

end EventuallyBoundedGatePolyMatrixCoeffs

noncomputable def eventuallyBoundedGatePolyVectorCoeffs_vecPolyC_fst {d K : Nat}
    {path : ℝ -> ProbePair d} (hpath : EventuallyBoundedProbePair path) :
    EventuallyBoundedGatePolyVectorCoeffs
      (fun τ : ℝ => vecPolyC (K := K) (d := d) (path τ).1) :=
  fun i => EventuallyBoundedGatePolyCoeffs.C_ofReal (hpath.fst i)

noncomputable def eventuallyBoundedGatePolyVectorCoeffs_vecPolyC_snd {d K : Nat}
    {path : ℝ -> ProbePair d} (hpath : EventuallyBoundedProbePair path) :
    EventuallyBoundedGatePolyVectorCoeffs
      (fun τ : ℝ => vecPolyC (K := K) (d := d) (path τ).2) :=
  fun i => EventuallyBoundedGatePolyCoeffs.C_ofReal (hpath.snd i)

noncomputable def eventuallyBoundedGatePolyVectorCoeffs_formalWVecPoly_of_path
    {L d K : Nat} (θ : Params L d) (n : Nat) {path : ℝ -> ProbePair d}
    (hpath : EventuallyBoundedProbePair path) :
    EventuallyBoundedGatePolyVectorCoeffs
      (fun τ : ℝ =>
        formalWVecPoly (K := K) (paramStream θ) n (path τ).1) :=
  EventuallyBoundedGatePolyVectorCoeffs.matVecMul
    (EventuallyBoundedGatePolyMatrixCoeffs.const (formalWPoly (K := K) (paramStream θ) n))
    (eventuallyBoundedGatePolyVectorCoeffs_vecPolyC_fst (K := K) hpath)

noncomputable def eventuallyBoundedGatePolyVectorCoeffs_formalVVecPoly_of_path
    {L d K : Nat} (θ : Params L d) :
    ∀ n : Nat, {path : ℝ -> ProbePair d} ->
      EventuallyBoundedProbePair path ->
      EventuallyBoundedGatePolyVectorCoeffs
        (fun τ : ℝ =>
          formalVVecPoly (K := K) (paramStream θ) n (path τ).1 (path τ).2)
  | 0, _path, hpath => eventuallyBoundedGatePolyVectorCoeffs_vecPolyC_snd (K := K) hpath
  | n + 1, _path, hpath =>
      let hprev :=
        eventuallyBoundedGatePolyVectorCoeffs_formalVVecPoly_of_path (K := K) θ n hpath
      let hleft :=
        EventuallyBoundedGatePolyVectorCoeffs.matVecMul
          (EventuallyBoundedGatePolyMatrixCoeffs.const
            (matPolyC (K := K) (skipB (paramStream θ n).1)))
          hprev
      let hW := eventuallyBoundedGatePolyVectorCoeffs_formalWVecPoly_of_path (K := K) θ n hpath
      let hrightCore :=
        EventuallyBoundedGatePolyVectorCoeffs.matVecMul
          (EventuallyBoundedGatePolyMatrixCoeffs.const
            (matPolyC (K := K) (paramStream θ n).1))
          hW
      let hright :=
        EventuallyBoundedGatePolyVectorCoeffs.smul
          (EventuallyBoundedGatePolyCoeffs.const (gateVar K n))
          hrightCore
      hleft.add hright

noncomputable def eventuallyBoundedGatePolyCoeffs_formalPhiPoly_of_path
    {L d K : Nat} (θ : Params L d) (n : Nat) {path : ℝ -> ProbePair d}
    (hpath : EventuallyBoundedProbePair path) :
    EventuallyBoundedGatePolyCoeffs
      (fun τ : ℝ =>
        formalPhiPoly (K := K) (paramStream θ) n (path τ).1 (path τ).2) := by
  classical
  let hW := eventuallyBoundedGatePolyVectorCoeffs_formalWVecPoly_of_path (K := K) θ n hpath
  let hV := eventuallyBoundedGatePolyVectorCoeffs_formalVVecPoly_of_path (K := K) θ n hpath
  let hAV :=
    EventuallyBoundedGatePolyVectorCoeffs.matVecMul
      (EventuallyBoundedGatePolyMatrixCoeffs.const
        (matPolyC (K := K) (paramStream θ n).2))
      hV
  have hterm : ∀ i : Fin d,
      EventuallyBoundedGatePolyCoeffs
        (fun τ =>
          formalWVecPoly (K := K) (paramStream θ) n (path τ).1 i *
            (matPolyC (K := K) (paramStream θ n).2 *ᵥ
              formalVVecPoly (K := K) (paramStream θ) n (path τ).1 (path τ).2) i) := by
    intro i
    exact (hW i).mul (hAV i)
  intro m
  exact ((EventuallyBoundedGatePolyCoeffs.fintype_sum
    (fun i τ =>
      formalWVecPoly (K := K) (paramStream θ) n (path τ).1 i *
        (matPolyC (K := K) (paramStream θ n).2 *ᵥ
          formalVVecPoly (K := K) (paramStream θ) n (path τ).1 (path τ).2) i)
    hterm) m).congr_of_forall_eq (by
      intro τ
      simp [formalPhiPoly, dotProduct])

/-- The fixed finite set of monomials with every coordinate degree at most `N`. -/
noncomputable def gateMonomialDegreeBox (K N : Nat) : Finset (Fin K →₀ Nat) :=
  (Finset.univ : Finset (Fin K)).finsupp (fun _ : Fin K => Finset.range (N + 1))

theorem mem_gateMonomialDegreeBox_iff {K N : Nat} {m : Fin K →₀ Nat} :
    m ∈ gateMonomialDegreeBox K N ↔ ∀ j : Fin K, m j ≤ N := by
  classical
  unfold gateMonomialDegreeBox
  rw [Finset.mem_finsupp_iff]
  constructor
  · intro h j
    have hj := h.2 j (Finset.mem_univ j)
    rw [Finset.mem_range] at hj
    exact Nat.lt_succ_iff.mp hj
  · intro h
    constructor
    · intro j _hj
      exact Finset.mem_univ j
    · intro j _hj
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le (h j)

theorem support_formalPhiPoly_subset_gateMonomialDegreeBox {L d K : Nat}
    (θ : Params L d) (n : Nat) (w v : Fin d -> ℝ) :
    (formalPhiPoly (K := K) (paramStream θ) n w v).support ⊆
      gateMonomialDegreeBox K 2 := by
  intro m hm
  rw [mem_gateMonomialDegreeBox_iff]
  intro j
  exact (MvPolynomial.degreeOf_le_iff.mp
    (degreeOf_formalPhiPoly_le_two (K := K) (paramStream θ) n j w v)) m hm

set_option maxHeartbeats 800000 in
-- This finite-support bound elaborates several coefficient families for `formalPhiPoly`;
-- the proof is elementary but needs more reduction budget than the file default.
noncomputable def eventuallyBoundedReal_formalPhiSliceLipschitzConstant_of_path
    {L d : Nat} (θ : Params L d) (level : Nat) (coord : Fin level)
    (R : Fin level -> ℝ) (path : ℝ -> ProbePair d)
    (hR : ∀ j, 0 ≤ R j)
    (hpath : EventuallyBoundedProbePair path) :
    EventuallyBoundedReal
      (fun τ => formalPhiSliceLipschitzConstant θ level coord R (path τ)) := by
  classical
  let q : ℝ -> GatePoly level :=
    fun τ => formalPhiPoly (K := level) (paramStream θ) level (path τ).1 (path τ).2
  let box : Finset (Fin level →₀ Nat) := gateMonomialDegreeBox level 2
  let factor : (Fin level →₀ Nat) -> ℝ :=
    fun m =>
      (((m coord : ℝ) * R coord ^ (m coord - 1)) *
        polynomialSliceOffRadius coord R m)
  have hcoeffs : EventuallyBoundedGatePolyCoeffs q :=
    eventuallyBoundedGatePolyCoeffs_formalPhiPoly_of_path (K := level) θ level hpath
  let term : (Fin level →₀ Nat) -> ℝ -> ℝ :=
    fun m τ => ‖MvPolynomial.coeff m (q τ)‖ * factor m
  have hterm : ∀ m : Fin level →₀ Nat, EventuallyBoundedReal (term m) := by
    intro m
    exact ((hcoeffs m).norm).mul_const (factor m)
  have hsum : EventuallyBoundedReal (fun τ => ∑ m : {m // m ∈ box}, term m.1 τ) :=
    EventuallyBoundedReal.fintype_sum
      (fun (m : {m // m ∈ box}) τ => term m.1 τ)
      (fun (m : {m // m ∈ box}) => hterm m.1)
  refine EventuallyBoundedReal.of_bound hsum.radius hsum.radius_nonneg hsum.start ?_
  intro τ hτ
  have hnonneg :
      0 ≤ formalPhiSliceLipschitzConstant θ level coord R (path τ) := by
    exact polynomialSliceLipschitzConstant_nonneg (q τ) coord R hR
  rw [abs_of_nonneg hnonneg]
  have hsupport : (q τ).support ⊆ box :=
    support_formalPhiPoly_subset_gateMonomialDegreeBox (K := level) θ level (path τ).1 (path τ).2
  calc
    formalPhiSliceLipschitzConstant θ level coord R (path τ)
        = ∑ m ∈ (q τ).support, term m τ := by
          simp [formalPhiSliceLipschitzConstant, polynomialSliceLipschitzConstant,
            q, term, factor]
    _ ≤ ∑ m ∈ box, term m τ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsupport ?_
          intro m _hmbox hmnot
          exact mul_nonneg (norm_nonneg _)
            (mul_nonneg
              (mul_nonneg (Nat.cast_nonneg (m coord))
                (pow_nonneg (hR coord) (m coord - 1)))
              (polynomialSliceOffRadius_nonneg coord R m hR))
    _ = ∑ m : {m // m ∈ box}, term m.1 τ := by
          exact Finset.sum_subtype (s := box) (h := fun m => Iff.rfl)
            (f := fun m => term m τ)
    _ ≤ |∑ m : {m // m ∈ box}, term m.1 τ| := le_abs_self _
    _ ≤ hsum.radius := hsum.bound τ hτ

/-! ## Finite telescoping for prior alpha gates -/

/-- Prefix assignment used by the alpha-error telescope.

Coordinate `0` is always the live first gate.  Coordinates `1 ≤ n < m` use the live
prior gates, while the remaining tail coordinates use the saturated constants. -/
noncomputable def alphaGateAssignmentPrefix
    (head : ℝ) (gate tail : Nat -> ℝ) (m : Nat) : Nat -> ℂ :=
  fun n =>
    if n = 0 then
      (head : ℂ)
    else if n < m then
      (gate n : ℂ)
    else
      (tail (n - 1) : ℂ)

/-- With no live prior gate inserted, the prefix assignment is the usual tail
assignment. -/
theorem alphaGateAssignmentPrefix_zero
    (head : ℝ) (gate tail : Nat -> ℝ) :
    alphaGateAssignmentPrefix head gate tail 0 =
      complexGateAssignmentOfTail (head : ℂ) tail := by
  funext n
  cases n with
  | zero =>
      simp [alphaGateAssignmentPrefix, complexGateAssignmentOfTail]
  | succ n =>
      simp [alphaGateAssignmentPrefix, complexGateAssignmentOfTail]

/-- The zeroth telescope step is vacuous: coordinate `0` is the same live first gate on
both sides. -/
theorem alphaGateAssignmentPrefix_one_eq_zero
    (head : ℝ) (gate tail : Nat -> ℝ) :
    alphaGateAssignmentPrefix head gate tail 1 =
      alphaGateAssignmentPrefix head gate tail 0 := by
  funext n
  cases n with
  | zero =>
      simp [alphaGateAssignmentPrefix]
  | succ n =>
      simp [alphaGateAssignmentPrefix]

/-- Real-valued version of `alphaGateAssignmentPrefix`, used to feed the polynomial
box estimates before coercing back to complex gates. -/
noncomputable def alphaGateAssignmentPrefixReal
    (head : ℝ) (gate tail : Nat -> ℝ) (m : Nat) : Nat -> ℝ :=
  fun n =>
    if n = 0 then
      head
    else if n < m then
      gate n
    else
      tail (n - 1)

theorem alphaGateAssignmentPrefixReal_ofReal
    (head : ℝ) (gate tail : Nat -> ℝ) (m : Nat) :
    (fun n => (alphaGateAssignmentPrefixReal head gate tail m n : ℂ)) =
      alphaGateAssignmentPrefix head gate tail m := by
  funext n
  unfold alphaGateAssignmentPrefixReal alphaGateAssignmentPrefix
  by_cases h0 : n = 0
  · simp [h0]
  · by_cases hm : n < m
    · simp [h0, hm]
    · simp [h0, hm]

theorem re_specializedPhi_alphaGateAssignmentPrefix_eq_matrixBilin_peelPoint
    {L d : Nat} (θ : Params L d) (level : Nat)
    (head : ℝ) (live : Nat -> ℝ) (tail : Nat -> ℝ) (p : ProbePair d) :
    (specializedPhi θ level
      (alphaGateAssignmentPrefix head live tail level) p).re =
      matrixBilin (paramStream θ level).2
        (peelPoint (paramStream θ)
          (alphaGateAssignmentPrefixReal head live tail level) level p).1
        (peelPoint (paramStream θ)
          (alphaGateAssignmentPrefixReal head live tail level) level p).2 := by
  rw [specializedPhi, ← alphaGateAssignmentPrefixReal_ofReal head live tail level]
  exact re_formalPhi_eq_matrixBilin_peelPoint (paramStream θ)
    (alphaGateAssignmentPrefixReal head live tail level) level p

theorem alphaGateAssignmentPrefixReal_succ_eq_of_ne
    (head : ℝ) (gate tail : Nat -> ℝ) {n j : Nat} (hn : 1 ≤ n)
    (hj : j ≠ n) :
    alphaGateAssignmentPrefixReal head gate tail (n + 1) j =
      alphaGateAssignmentPrefixReal head gate tail n j := by
  unfold alphaGateAssignmentPrefixReal
  by_cases hj0 : j = 0
  · simp [hj0]
  · by_cases hjlt : j < n
    · have hjsucc : j < n + 1 := by omega
      simp [hj0, hjlt, hjsucc]
    · have hjsucc : ¬ j < n + 1 := by omega
      simp [hj0, hjlt, hjsucc]

theorem alphaGateAssignmentPrefixReal_succ_sub_self
    (head : ℝ) (gate tail : Nat -> ℝ) {n : Nat} (hn : 1 ≤ n) :
    alphaGateAssignmentPrefixReal head gate tail (n + 1) n -
      alphaGateAssignmentPrefixReal head gate tail n n =
        gate n - tail (n - 1) := by
  unfold alphaGateAssignmentPrefixReal
  have hn0 : ¬ n = 0 := by omega
  have hnlt : n < n + 1 := Nat.lt_succ_self n
  simp [hn0, hnlt]

/-- A coarse coordinate box radius for all real alpha-prefix assignments below
`level`, built from eventual bounds for the head gate, all finite gate coordinates, and
the fixed tail constants. -/
noncomputable def alphaGateAssignmentPrefixRealBoxRadius {level : Nat} {head : ℝ -> ℝ}
    {gate : Nat -> ℝ -> ℝ} (hhead : EventuallyBoundedReal head)
    (hgate : ∀ j : Nat, j < level -> EventuallyBoundedReal (fun τ => gate j τ))
    (tail : Nat -> ℝ) (j : Fin level) : ℝ :=
  hhead.radius + (hgate (j : Nat) j.isLt).radius + |tail ((j : Nat) - 1)|

noncomputable def alphaGateAssignmentPrefixRealBoxStart {level : Nat} {head : ℝ -> ℝ}
    {gate : Nat -> ℝ -> ℝ} (hhead : EventuallyBoundedReal head)
    (hgate : ∀ j : Nat, j < level -> EventuallyBoundedReal (fun τ => gate j τ)) : ℝ :=
  |hhead.start| + ∑ j : Fin level, |(hgate (j : Nat) j.isLt).start|

theorem alphaGateAssignmentPrefixRealBoxRadius_nonneg {level : Nat} {head : ℝ -> ℝ}
    {gate : Nat -> ℝ -> ℝ} (hhead : EventuallyBoundedReal head)
    (hgate : ∀ j : Nat, j < level -> EventuallyBoundedReal (fun τ => gate j τ))
    (tail : Nat -> ℝ) (j : Fin level) :
    0 ≤ alphaGateAssignmentPrefixRealBoxRadius hhead hgate tail j := by
  unfold alphaGateAssignmentPrefixRealBoxRadius
  exact add_nonneg
    (add_nonneg hhead.radius_nonneg (hgate (j : Nat) j.isLt).radius_nonneg)
    (abs_nonneg _)

theorem alphaGateAssignmentPrefixRealBoxStart_head_le {level : Nat} {head : ℝ -> ℝ}
    {gate : Nat -> ℝ -> ℝ} (hhead : EventuallyBoundedReal head)
    (hgate : ∀ j : Nat, j < level -> EventuallyBoundedReal (fun τ => gate j τ)) :
    hhead.start ≤ alphaGateAssignmentPrefixRealBoxStart hhead hgate := by
  unfold alphaGateAssignmentPrefixRealBoxStart
  have hsum_nonneg : 0 ≤ ∑ j : Fin level, |(hgate (j : Nat) j.isLt).start| := by
    exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hstart_abs : hhead.start ≤ |hhead.start| := le_abs_self _
  linarith

theorem alphaGateAssignmentPrefixRealBoxStart_gate_le {level : Nat} {head : ℝ -> ℝ}
    {gate : Nat -> ℝ -> ℝ} (hhead : EventuallyBoundedReal head)
    (hgate : ∀ j : Nat, j < level -> EventuallyBoundedReal (fun τ => gate j τ))
    (j : Fin level) :
    (hgate (j : Nat) j.isLt).start ≤ alphaGateAssignmentPrefixRealBoxStart hhead hgate := by
  unfold alphaGateAssignmentPrefixRealBoxStart
  have hle_abs :
      (hgate (j : Nat) j.isLt).start ≤ |(hgate (j : Nat) j.isLt).start| :=
    le_abs_self _
  have habs_le_sum :
      |(hgate (j : Nat) j.isLt).start| ≤
        ∑ k : Fin level, |(hgate (k : Nat) k.isLt).start| := by
    simpa using
      (Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin level)))
        (f := fun k : Fin level => |(hgate (k : Nat) k.isLt).start|)
        (fun _ _ => abs_nonneg _)
        (Finset.mem_univ j))
  have hhead_abs_nonneg : 0 ≤ |hhead.start| := abs_nonneg _
  linarith

theorem alphaGateAssignmentPrefixReal_box_bound {level : Nat} {head : ℝ -> ℝ}
    {gate : Nat -> ℝ -> ℝ} (tail : Nat -> ℝ)
    (hhead : EventuallyBoundedReal head)
    (hgate : ∀ j : Nat, j < level -> EventuallyBoundedReal (fun τ => gate j τ)) :
    ∀ τ : ℝ, alphaGateAssignmentPrefixRealBoxStart hhead hgate ≤ τ ->
      ∀ m : Nat, ∀ j : Fin level,
        |alphaGateAssignmentPrefixReal (head τ) (fun k => gate k τ) tail m j| ≤
          alphaGateAssignmentPrefixRealBoxRadius hhead hgate tail j := by
  intro τ hτ m j
  have hτ_head : hhead.start ≤ τ :=
    le_trans (alphaGateAssignmentPrefixRealBoxStart_head_le hhead hgate) hτ
  have hτ_gate : (hgate (j : Nat) j.isLt).start ≤ τ :=
    le_trans (alphaGateAssignmentPrefixRealBoxStart_gate_le hhead hgate j) hτ
  unfold alphaGateAssignmentPrefixReal alphaGateAssignmentPrefixRealBoxRadius
  by_cases hj0 : (j : Nat) = 0
  · rw [if_pos hj0]
    have hb := hhead.bound τ hτ_head
    have hgate_nonneg : 0 ≤ (hgate (j : Nat) j.isLt).radius :=
      (hgate (j : Nat) j.isLt).radius_nonneg
    have htail_nonneg : 0 ≤ |tail ((j : Nat) - 1)| := abs_nonneg _
    linarith
  · rw [if_neg hj0]
    by_cases hjm : (j : Nat) < m
    · rw [if_pos hjm]
      have hb := (hgate (j : Nat) j.isLt).bound τ hτ_gate
      have hhead_nonneg : 0 ≤ hhead.radius := hhead.radius_nonneg
      have htail_nonneg : 0 ≤ |tail ((j : Nat) - 1)| := abs_nonneg _
      linarith
    · rw [if_neg hjm]
      have hhead_nonneg : 0 ≤ hhead.radius := hhead.radius_nonneg
      have hgate_nonneg : 0 ≤ (hgate (j : Nat) j.isLt).radius :=
        (hgate (j : Nat) j.isLt).radius_nonneg
      linarith [abs_nonneg (tail ((j : Nat) - 1))]

/-- Per-coordinate alpha-prefix Lipschitz input obtained from the finite-support
polynomial box constant for `formalPhiPoly`.

The remaining nontrivial compactness obligation is the `hcoeff` input: the explicit
coefficient-sum constant for the path-dependent `formalPhiPoly` slice must be eventually
bounded.  This theorem then turns that concrete coefficient bound and the coordinate box
bound into exactly the `hLip` shape needed by the telescoping estimate. -/
theorem specializedPhi_prefix_step_lipschitz_of_coefficient_bound
    {L d : Nat} (θ : Params L d) {level n : Nat}
    (hn_pos : 1 ≤ n) (hn_lt : n < level)
    (tail : Nat -> ℝ) (head : ℝ -> ℝ) (gate : Nat -> ℝ -> ℝ)
    (path : ℝ -> ProbePair d)
    (R : Fin level -> ℝ) (Tbox : ℝ)
    (hR : ∀ j : Fin level, 0 ≤ R j)
    (hbox :
      ∀ τ : ℝ, Tbox ≤ τ ->
        ∀ m : Nat, ∀ j : Fin level,
          |alphaGateAssignmentPrefixReal (head τ) (fun k => gate k τ) tail m j| ≤ R j)
    (hcoeff :
      EventuallyBoundedReal
        (fun τ => formalPhiSliceLipschitzConstant θ level ⟨n, hn_lt⟩ R (path τ))) :
    ∀ τ : ℝ, max Tbox hcoeff.start ≤ τ ->
      |(specializedPhi θ level
          (alphaGateAssignmentPrefix (head τ) (fun j => gate j τ) tail (n + 1))
          (path τ)).re -
        (specializedPhi θ level
          (alphaGateAssignmentPrefix (head τ) (fun j => gate j τ) tail n)
          (path τ)).re|
        ≤ hcoeff.radius * |gate n τ - tail (n - 1)| := by
  intro τ hτ
  let coord : Fin level := ⟨n, hn_lt⟩
  let x : Fin level -> ℝ :=
    fun j => alphaGateAssignmentPrefixReal (head τ) (fun k => gate k τ) tail (n + 1) j
  let y : Fin level -> ℝ :=
    fun j => alphaGateAssignmentPrefixReal (head τ) (fun k => gate k τ) tail n j
  let q : GatePoly level := formalPhiPoly (K := level) (paramStream θ) level
    (path τ).1 (path τ).2
  have hτ_box : Tbox ≤ τ := le_trans (le_max_left _ _) hτ
  have hτ_coeff : hcoeff.start ≤ τ := le_trans (le_max_right _ _) hτ
  have hx : ∀ j : Fin level, |x j| ≤ R j := fun j => hbox τ hτ_box (n + 1) j
  have hy : ∀ j : Fin level, |y j| ≤ R j := fun j => hbox τ hτ_box n j
  have heq : ∀ j : Fin level, j ≠ coord -> x j = y j := by
    intro j hj
    exact alphaGateAssignmentPrefixReal_succ_eq_of_ne (head τ) (fun k => gate k τ) tail
      hn_pos (by
        intro hval
        apply hj
        exact Fin.ext hval)
  have hcoord :
      x coord - y coord = gate n τ - tail (n - 1) := by
    exact alphaGateAssignmentPrefixReal_succ_sub_self (head τ) (fun k => gate k τ) tail
      hn_pos
  have hxcomplex :
      (fun j : Fin level => (x j : ℂ)) =
        fun j : Fin level =>
          alphaGateAssignmentPrefix (head τ) (fun k => gate k τ) tail (n + 1) j := by
    funext j
    exact congrFun
      (alphaGateAssignmentPrefixReal_ofReal (head τ) (fun k => gate k τ) tail (n + 1))
      (j : Nat)
  have hycomplex :
      (fun j : Fin level => (y j : ℂ)) =
        fun j : Fin level =>
          alphaGateAssignmentPrefix (head τ) (fun k => gate k τ) tail n j := by
    funext j
    exact congrFun
      (alphaGateAssignmentPrefixReal_ofReal (head τ) (fun k => gate k τ) tail n)
      (j : Nat)
  have hA :
      specializedPhi θ level
          (alphaGateAssignmentPrefix (head τ) (fun j => gate j τ) tail (n + 1))
          (path τ) =
        MvPolynomial.eval (fun j : Fin level => (x j : ℂ)) q := by
    rw [specializedPhi_eq_eval_formalPhiPoly]
    rw [← hxcomplex]
  have hB :
      specializedPhi θ level
          (alphaGateAssignmentPrefix (head τ) (fun j => gate j τ) tail n)
          (path τ) =
        MvPolynomial.eval (fun j : Fin level => (y j : ℂ)) q := by
    rw [specializedPhi_eq_eval_formalPhiPoly]
    rw [← hycomplex]
  have hpoly :=
    eval_re_sub_eval_re_le_polynomialSliceLipschitzConstant q coord R x y hR hx hy heq
  have hL_nonneg :
      0 ≤ formalPhiSliceLipschitzConstant θ level coord R (path τ) := by
    exact polynomialSliceLipschitzConstant_nonneg q coord R hR
  have hL_le :
      formalPhiSliceLipschitzConstant θ level coord R (path τ) ≤ hcoeff.radius := by
    have hb := hcoeff.bound τ hτ_coeff
    rw [abs_of_nonneg hL_nonneg] at hb
    exact hb
  calc
    |(specializedPhi θ level
        (alphaGateAssignmentPrefix (head τ) (fun j => gate j τ) tail (n + 1))
        (path τ)).re -
      (specializedPhi θ level
        (alphaGateAssignmentPrefix (head τ) (fun j => gate j τ) tail n)
        (path τ)).re|
        = |(MvPolynomial.eval (fun j : Fin level => (x j : ℂ)) q).re -
            (MvPolynomial.eval (fun j : Fin level => (y j : ℂ)) q).re| := by
          rw [hA, hB]
    _ ≤ polynomialSliceLipschitzConstant q coord R * |x coord - y coord| := hpoly
    _ ≤ hcoeff.radius * |x coord - y coord| :=
      mul_le_mul_of_nonneg_right hL_le (abs_nonneg _)
    _ = hcoeff.radius * |gate n τ - tail (n - 1)| := by
      rw [hcoord]

/-- Single alpha-prefix step with the coefficient bound supplied by bounded probe
coordinates and the canonical finite alpha-prefix box. -/
theorem specializedPhi_prefix_step_lipschitz_of_path_bound
    {L d : Nat} (θ : Params L d) {level n : Nat}
    (hn_pos : 1 ≤ n) (hn_lt : n < level)
    (tail : Nat -> ℝ) (head : ℝ -> ℝ) (gate : Nat -> ℝ -> ℝ)
    (path : ℝ -> ProbePair d)
    (hhead : EventuallyBoundedReal head)
    (hgate : ∀ j : Nat, j < level -> EventuallyBoundedReal (fun τ => gate j τ))
    (hpath : EventuallyBoundedProbePair path) :
    let R : Fin level -> ℝ := alphaGateAssignmentPrefixRealBoxRadius hhead hgate tail
    let Tbox : ℝ := alphaGateAssignmentPrefixRealBoxStart hhead hgate
    let hcoeff :=
      eventuallyBoundedReal_formalPhiSliceLipschitzConstant_of_path
        θ level ⟨n, hn_lt⟩ R path
        (alphaGateAssignmentPrefixRealBoxRadius_nonneg hhead hgate tail) hpath
    ∀ τ : ℝ, max Tbox hcoeff.start ≤ τ ->
      |(specializedPhi θ level
          (alphaGateAssignmentPrefix (head τ) (fun j => gate j τ) tail (n + 1))
          (path τ)).re -
        (specializedPhi θ level
          (alphaGateAssignmentPrefix (head τ) (fun j => gate j τ) tail n)
          (path τ)).re|
        ≤ hcoeff.radius * |gate n τ - tail (n - 1)| := by
  intro R Tbox hcoeff
  exact specializedPhi_prefix_step_lipschitz_of_coefficient_bound
    θ hn_pos hn_lt tail head gate path R Tbox
    (alphaGateAssignmentPrefixRealBoxRadius_nonneg hhead hgate tail)
    (alphaGateAssignmentPrefixReal_box_bound tail hhead hgate)
    hcoeff

/-- Sum of consecutive forward differences on `Finset.range`. -/
theorem sum_range_forward_difference (A : Nat -> ℝ) (N : Nat) :
    (Finset.range N).sum (fun k => A (k + 1) - A k) = A N - A 0 := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- Multi-coordinate delta estimate for the real part of `specializedPhi`.

The conclusion compares the assignment with live first gate and live prior gates
`1 ≤ n < level` against the formal assignment where those prior gates have been
replaced by the saturated `tail` constants.  The only analytic input is the displayed
per-coordinate Lipschitz bound for each telescope step. -/
noncomputable def eventuallyExpClose_specializedPhi_multiGate_delta_of_lipschitz
    {L d : Nat} (θ : Params L d) (level : Nat)
    (tail : Nat -> ℝ) (head : ℝ -> ℝ) (gate : Nat -> ℝ -> ℝ)
    (path : ℝ -> ProbePair d) {K T : Nat -> ℝ}
    (hgate :
      ∀ n : Nat, 1 ≤ n -> n < level ->
        EventuallyExpClose (fun τ => gate n τ) (tail (n - 1)))
    (hK : ∀ n : Nat, 1 ≤ n -> n < level -> 0 ≤ K n)
    (hLip :
      ∀ n : Nat, 1 ≤ n -> n < level ->
        ∀ τ : ℝ, T n ≤ τ ->
          |(specializedPhi θ level
              (alphaGateAssignmentPrefix (head τ) (fun j => gate j τ) tail (n + 1))
              (path τ)).re -
            (specializedPhi θ level
              (alphaGateAssignmentPrefix (head τ) (fun j => gate j τ) tail n)
              (path τ)).re|
            ≤ K n * |gate n τ - tail (n - 1)|) :
    EventuallyExpClose
      (fun τ =>
        (specializedPhi θ level
          (alphaGateAssignmentPrefix (head τ) (fun n => gate n τ) tail level)
          (path τ)).re -
        (specializedPhi θ level
          (complexGateAssignmentOfTail ((head τ : ℝ) : ℂ) tail)
          (path τ)).re)
      0 := by
  classical
  let A : ℝ -> Nat -> ℝ :=
    fun τ m =>
      (specializedPhi θ level
        (alphaGateAssignmentPrefix (head τ) (fun n => gate n τ) tail m)
        (path τ)).re
  have hterm :
      ∀ k : Nat, k < level ->
        EventuallyExpClose (fun τ => A τ (k + 1) - A τ k) 0 := by
    intro k hk
    by_cases hk_zero : k = 0
    · subst k
      refine EventuallyExpClose.of_forall_eq ?_
      intro τ
      have hassign :
          alphaGateAssignmentPrefix (head τ) (fun n => gate n τ) tail 1 =
            alphaGateAssignmentPrefix (head τ) (fun n => gate n τ) tail 0 :=
        alphaGateAssignmentPrefix_one_eq_zero (head τ) (fun n => gate n τ) tail
      change
        (specializedPhi θ level
            (alphaGateAssignmentPrefix (head τ) (fun n => gate n τ) tail 1)
            (path τ)).re -
          (specializedPhi θ level
            (alphaGateAssignmentPrefix (head τ) (fun n => gate n τ) tail 0)
            (path τ)).re = 0
      rw [hassign]
      ring
    · have hk_pos : 1 ≤ k := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk_zero)
      have hk_lt : k < level := hk
      exact
        eventuallyExpClose_delta_of_eventual_lipschitz
          (x := fun τ => gate k τ)
          (delta := fun τ => A τ (k + 1) - A τ k)
          (a := tail (k - 1)) (K := K k) (T := T k)
          (hgate k hk_pos hk_lt) (hK k hk_pos hk_lt)
          (by
            intro τ hτ
            exact hLip k hk_pos hk_lt τ hτ)
  have hsum :
      EventuallyExpClose
        (fun τ => (Finset.range level).sum (fun k => A τ (k + 1) - A τ k)) 0 :=
    EventuallyExpClose.sum_range_zero level hterm
  refine hsum.congr_of_forall_eq ?_ rfl
  intro τ
  have htel := sum_range_forward_difference (fun m => A τ m) level
  have hzero :
      A τ 0 =
        (specializedPhi θ level
          (complexGateAssignmentOfTail ((head τ : ℝ) : ℂ) tail)
          (path τ)).re := by
    change
      (specializedPhi θ level
          (alphaGateAssignmentPrefix (head τ) (fun n => gate n τ) tail 0)
          (path τ)).re =
        (specializedPhi θ level
          (complexGateAssignmentOfTail ((head τ : ℝ) : ℂ) tail)
          (path τ)).re
    rw [alphaGateAssignmentPrefix_zero]
  calc
    (Finset.range level).sum (fun k => A τ (k + 1) - A τ k)
        = A τ level - A τ 0 := htel
    _ =
        (specializedPhi θ level
          (alphaGateAssignmentPrefix (head τ) (fun n => gate n τ) tail level)
          (path τ)).re -
        (specializedPhi θ level
          (complexGateAssignmentOfTail ((head τ : ℝ) : ℂ) tail)
          (path τ)).re := by
          rw [hzero]

/-! ## Packaging the alpha slope error bound -/

/-- Constructor for the alpha-branch slope error package from the concrete
specialized-`Phi` slope identity.

The proof uses the multi-gate telescoping estimate above.  For each fixed base point
`x`, the positive prior gates are bounded by their exponential closeness to `tail`,
while coordinate `0` of the auxiliary live-gate family is identified with the bounded
head gate because alpha-prefix assignments ignore the supplied prior gate at
coordinate `0`. -/
noncomputable def cascadeAlphaSlopeErrorBound_of_specializedPhi_prefix
    {L d : Nat} (θ : Params L d) (A : Matrix (Fin d) (Fin d) ℝ)
    (level : Nat) (tail : Nat -> ℝ)
    (U : Set (ProbePair d × ℝ)) (gate : GateAlongBase d)
    (headGate : ProbePair d × ℝ -> ℝ -> ℝ)
    (path : ProbePair d × ℝ -> ℝ -> ProbePair d)
    (lam : ProbePair d × ℝ -> ℝ -> ℝ)
    (hhead :
      ∀ x ∈ U, EventuallyBoundedReal (fun τ => headGate x τ))
    (hpath :
      ∀ x ∈ U, EventuallyBoundedProbePair (path x))
    (hlam :
      ∀ x ∈ U, ∀ τ : ℝ,
        lam x τ =
          (specializedPhi θ level
            (alphaGateAssignmentPrefix (headGate x τ) (fun n => gate n x τ) tail level)
            (path x τ)).re) :
    CascadeAlphaSlopeErrorBound θ A level tail U gate headGate path lam where
  slope_error := by
    intro hprior x hx
    let head : ℝ -> ℝ := fun τ => headGate x τ
    let liveGate : Nat -> ℝ -> ℝ :=
      fun n τ => if n = 0 then headGate x τ else gate n x τ
    let pathx : ℝ -> ProbePair d := path x
    have hheadx : EventuallyBoundedReal head := by
      simpa [head] using hhead x hx
    have hpathx : EventuallyBoundedProbePair pathx := by
      simpa [pathx] using hpath x hx
    have hliveClose :
        ∀ n : Nat, 1 ≤ n -> n < level ->
          EventuallyExpClose (fun τ => liveGate n τ) (tail (n - 1)) := by
      intro n hn_pos hn_lt
      have hn0 : n ≠ 0 := by omega
      exact (hprior x hx n hn_pos hn_lt).congr_of_forall_eq
        (by intro τ; simp [liveGate, hn0]) rfl
    have hliveBound :
        ∀ j : Nat, j < level -> EventuallyBoundedReal (fun τ => liveGate j τ) := by
      intro j hj
      by_cases hj0 : j = 0
      · subst j
        exact hheadx.congr_of_forall_eq (by intro τ; simp [liveGate, head])
      · have hj_pos : 1 ≤ j := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hj0)
        exact
          (EventuallyExpClose.eventuallyBoundedReal (hprior x hx j hj_pos hj)).congr_of_forall_eq
            (by intro τ; simp [liveGate, hj0])
    let R : Fin level -> ℝ :=
      alphaGateAssignmentPrefixRealBoxRadius hheadx hliveBound tail
    let Tbox : ℝ := alphaGateAssignmentPrefixRealBoxStart hheadx hliveBound
    let hR : ∀ j : Fin level, 0 ≤ R j := by
      simpa [R] using alphaGateAssignmentPrefixRealBoxRadius_nonneg hheadx hliveBound tail
    let coeff : (n : Nat) -> (hn_lt : n < level) -> EventuallyBoundedReal
        (fun τ => formalPhiSliceLipschitzConstant θ level ⟨n, hn_lt⟩ R (pathx τ)) :=
      fun n hn_lt =>
        eventuallyBoundedReal_formalPhiSliceLipschitzConstant_of_path
          θ level ⟨n, hn_lt⟩ R pathx hR hpathx
    let K : Nat -> ℝ := fun n =>
      if hn_lt : n < level then
        (coeff n hn_lt).radius
      else
        0
    let T : Nat -> ℝ := fun n =>
      if hn_lt : n < level then
        max Tbox (coeff n hn_lt).start
      else
        0
    have hK :
        ∀ n : Nat, 1 ≤ n -> n < level -> 0 ≤ K n := by
      intro n _hn_pos hn_lt
      simpa [K, hn_lt] using (coeff n hn_lt).radius_nonneg
    have hLip :
        ∀ n : Nat, 1 ≤ n -> n < level ->
          ∀ τ : ℝ, T n ≤ τ ->
            |(specializedPhi θ level
                (alphaGateAssignmentPrefix (head τ) (fun j => liveGate j τ) tail (n + 1))
                (pathx τ)).re -
              (specializedPhi θ level
                (alphaGateAssignmentPrefix (head τ) (fun j => liveGate j τ) tail n)
                (pathx τ)).re|
              ≤ K n * |liveGate n τ - tail (n - 1)| := by
      intro n hn_pos hn_lt τ hτ
      have hstep :=
        specializedPhi_prefix_step_lipschitz_of_path_bound
          (θ := θ) (level := level) (n := n) hn_pos hn_lt tail
          head liveGate pathx hheadx hliveBound hpathx
      have hTn : max Tbox (coeff n hn_lt).start ≤ τ := by
        simpa [T, hn_lt] using hτ
      have hKn : K n = (coeff n hn_lt).radius := by
        simp [K, hn_lt]
      rw [hKn]
      exact hstep τ hTn
    have hdeltaLive :
        EventuallyExpClose
          (fun τ =>
            (specializedPhi θ level
              (alphaGateAssignmentPrefix (head τ) (fun n => liveGate n τ) tail level)
              (pathx τ)).re -
            (specializedPhi θ level
              (complexGateAssignmentOfTail ((head τ : ℝ) : ℂ) tail)
              (pathx τ)).re)
          0 :=
      eventuallyExpClose_specializedPhi_multiGate_delta_of_lipschitz
        θ level tail head liveGate pathx hliveClose hK hLip
    refine hdeltaLive.congr_of_forall_eq ?_ rfl
    intro τ
    have hassign :
        alphaGateAssignmentPrefix (head τ) (fun n => liveGate n τ) tail level =
          alphaGateAssignmentPrefix (headGate x τ) (fun n => gate n x τ) tail level := by
      funext n
      unfold alphaGateAssignmentPrefix liveGate head
      by_cases hn0 : n = 0
      · simp [hn0]
      · by_cases hnlevel : n < level
        · simp [hn0, hnlevel]
        · simp [hn0, hnlevel]
    calc
      (specializedPhi θ level
          (alphaGateAssignmentPrefix (head τ) (fun n => liveGate n τ) tail level)
          (pathx τ)).re -
        (specializedPhi θ level
          (complexGateAssignmentOfTail ((head τ : ℝ) : ℂ) tail)
          (pathx τ)).re
          =
        (specializedPhi θ level
          (alphaGateAssignmentPrefix (headGate x τ) (fun n => gate n x τ) tail level)
          (path x τ)).re -
        (specializedPhi θ level
          (complexGateAssignmentOfTail (((headGate x τ) : ℝ) : ℂ) tail)
          (path x τ)).re := by
            rw [hassign]
      _ =
        lam x τ -
        (specializedPhi θ level
          (complexGateAssignmentOfTail (((headGate x τ) : ℝ) : ℂ) tail)
          (path x τ)).re := by
            rw [hlam x hx τ]

end TransformerIdentifiability.NLayer
