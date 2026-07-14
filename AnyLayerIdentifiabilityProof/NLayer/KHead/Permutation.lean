import Mathlib

/-!
# k-head permutation kernel

The new algebraic core of the `k`-head identifiability proof: extracting the per-layer head
permutation `σ ∈ S_k`.  These lemmas have no single-head analogue (with one head every
permutation group `S_1` is trivial).  They correspond to
`n_layer_proof_k_heads_more_detail.tex`:

* `unique_attention_permutation`  ← Lemma `lem:unique-attention-permutation`
* `global_labeling`               ← Lemma `lem:global-labeling`

Both are stated pointwise over `(t, w, v)`; because `ℝ` is infinite, the pointwise product
identity is equivalent to the polynomial identity in `ℝ[t, w, v]` used in the paper.
-/

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.KHead

/-- Variables for the bilinear form `wᵀ M v`: left variables are `Sum.inl i`, right
variables are `Sum.inr j`. -/
abbrev BilinVar (d : ℕ) : Type :=
  Sum (Fin d) (Fin d)

/-- The polynomial representing the bilinear attention form `wᵀ M v`. -/
noncomputable def attentionBilinPoly {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) : MvPolynomial (BilinVar d) ℝ :=
  ∑ i : Fin d, ∑ j : Fin d,
    MvPolynomial.C (M i j) *
      MvPolynomial.X (Sum.inl i) * MvPolynomial.X (Sum.inr j)

@[simp] theorem attentionBilinPoly_eval {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (x : BilinVar d → ℝ) :
    MvPolynomial.eval x (attentionBilinPoly M) =
      (fun i : Fin d => x (Sum.inl i)) ⬝ᵥ
        (M.mulVec fun j : Fin d => x (Sum.inr j)) := by
  simp [attentionBilinPoly, dotProduct, Matrix.mulVec, Finset.mul_sum,
    mul_comm, mul_left_comm]

/-- The univariate factor `t - wᵀ M v`, with coefficients in the polynomial ring in
the bilinear probe variables `(w, v)`. -/
noncomputable def attentionFactorPoly {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) :
    Polynomial (MvPolynomial (BilinVar d) ℝ) :=
  Polynomial.X - Polynomial.C (attentionBilinPoly M)

/-- The monic product `∏ c, (t - wᵀ B_c v)` as a polynomial in `t` whose coefficients
are polynomials in the bilinear probe variables `(w, v)`. -/
noncomputable def attentionProductPoly {d k : ℕ}
    (B : Fin k → Matrix (Fin d) (Fin d) ℝ) :
    Polynomial (MvPolynomial (BilinVar d) ℝ) :=
  ∏ c : Fin k, attentionFactorPoly (B c)

@[simp] theorem attentionFactorPoly_eval {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (x : BilinVar d → ℝ) (t : ℝ) :
    ((attentionFactorPoly M).map (MvPolynomial.eval x)).eval t =
      t - (fun i : Fin d => x (Sum.inl i)) ⬝ᵥ
        (M.mulVec fun j : Fin d => x (Sum.inr j)) := by
  simp [attentionFactorPoly]

@[simp] theorem attentionProductPoly_eval {d k : ℕ}
    (B : Fin k → Matrix (Fin d) (Fin d) ℝ) (x : BilinVar d → ℝ) (t : ℝ) :
    ((attentionProductPoly B).map (MvPolynomial.eval x)).eval t =
      ∏ c : Fin k,
        (t - (fun i : Fin d => x (Sum.inl i)) ⬝ᵥ
          ((B c).mulVec fun j : Fin d => x (Sum.inr j))) := by
  rw [attentionProductPoly, Polynomial.map_prod, Polynomial.eval_prod]
  simp

/-- Zariski density of a probe set in the `(w, v)` variables, in the form needed by
TeX Lemma `lem:global-labeling`: a polynomial in the bilinear probe variables that
vanishes on the set is identically zero. -/
def ProbeZariskiDense {d : ℕ}
    (U : Set ((Fin d → ℝ) × (Fin d → ℝ))) : Prop :=
  ∀ P : MvPolynomial (BilinVar d) ℝ,
    (∀ x ∈ U, MvPolynomial.eval (Sum.elim x.1 x.2) P = 0) → P = 0

theorem attentionProductPoly_eq_of_probeZariskiDense {d k : ℕ}
    (B B' : Fin k → Matrix (Fin d) (Fin d) ℝ)
    (U : Set ((Fin d → ℝ) × (Fin d → ℝ)))
    (hU : ProbeZariskiDense U)
    (hprodU : ∀ x ∈ U, ∀ t : ℝ,
      ∏ c : Fin k, (t - x.1 ⬝ᵥ (B c).mulVec x.2) =
        ∏ h : Fin k, (t - x.1 ⬝ᵥ (B' h).mulVec x.2)) :
    attentionProductPoly B = attentionProductPoly B' := by
  classical
  let R : Polynomial (MvPolynomial (BilinVar d) ℝ) :=
    attentionProductPoly B - attentionProductPoly B'
  have hcoeff : ∀ n : ℕ, R.coeff n = 0 := by
    intro n
    apply hU
    intro x hx
    have hpoly :
        (R.map (MvPolynomial.eval (Sum.elim x.1 x.2))) = 0 := by
      apply Polynomial.funext
      intro t
      have hxprod := hprodU x hx t
      simpa [R, sub_eq_zero] using hxprod
    have hcoeff_eval :=
      congrArg (fun P : Polynomial ℝ => P.coeff n) hpoly
    simpa [Polynomial.coeff_map] using hcoeff_eval
  have hR : R = 0 := by
    apply Polynomial.ext
    intro n
    exact hcoeff n
  have hsub :
      attentionProductPoly B - attentionProductPoly B' = 0 := by
    simpa [R] using hR
  exact sub_eq_zero.mp hsub

theorem attention_product_identity_of_probeZariskiDense {d k : ℕ}
    (B B' : Fin k → Matrix (Fin d) (Fin d) ℝ)
    (U : Set ((Fin d → ℝ) × (Fin d → ℝ)))
    (hU : ProbeZariskiDense U)
    (hprodU : ∀ x ∈ U, ∀ t : ℝ,
      ∏ c : Fin k, (t - x.1 ⬝ᵥ (B c).mulVec x.2) =
        ∏ h : Fin k, (t - x.1 ⬝ᵥ (B' h).mulVec x.2)) :
    ∀ (t : ℝ) (w v : Fin d → ℝ),
      ∏ c : Fin k, (t - w ⬝ᵥ (B c).mulVec v) =
        ∏ h : Fin k, (t - w ⬝ᵥ (B' h).mulVec v) := by
  classical
  have hpoly :=
    attentionProductPoly_eq_of_probeZariskiDense B B' U hU hprodU
  intro t w v
  have hEval :=
    congrArg
      (fun P : Polynomial (MvPolynomial (BilinVar d) ℝ) =>
        (P.map (MvPolynomial.eval (Sum.elim w v))).eval t)
      hpoly
  simpa using hEval

theorem attentionBilinPoly_eq_zero_iff {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) :
    attentionBilinPoly M = 0 ↔ M = 0 := by
  constructor
  · intro hM
    ext i j
    let x : BilinVar d → ℝ := Sum.elim (Pi.single i (1 : ℝ)) (Pi.single j (1 : ℝ))
    have hEval := congrArg (MvPolynomial.eval x) hM
    have hDot :
        (Pi.single i (1 : ℝ)) ⬝ᵥ (M.mulVec (Pi.single j (1 : ℝ))) = 0 := by
      simpa [x] using hEval
    have hEntry :
        (Pi.single i (1 : ℝ)) ⬝ᵥ (M.mulVec (Pi.single j (1 : ℝ))) = M i j := by
      rw [single_one_dotProduct]
      exact congrFun (Matrix.mulVec_single_one M j) i
    simpa [hEntry] using hDot
  · intro hM
    simp [hM, attentionBilinPoly]

/-- If a finite product of bilinear forms vanishes at every real point, then one of the
matrix factors is zero. -/
theorem exists_matrix_eq_zero_of_forall_bilinear_product_eq_zero {d k : ℕ}
    (M : Fin k → Matrix (Fin d) (Fin d) ℝ)
    (hzero : ∀ w v : Fin d → ℝ,
      ∏ c : Fin k, w ⬝ᵥ (M c).mulVec v = 0) :
    ∃ c : Fin k, M c = 0 := by
  classical
  have hpoly : (∏ c : Fin k, attentionBilinPoly (M c)) = 0 := by
    apply MvPolynomial.funext
    intro x
    simpa [attentionBilinPoly_eval] using
      hzero (fun i : Fin d => x (Sum.inl i)) (fun j : Fin d => x (Sum.inr j))
  obtain ⟨c, hc⟩ : ∃ c : Fin k, attentionBilinPoly (M c) = 0 := by
    simpa [Finset.prod_eq_zero_iff] using hpoly
  exact ⟨c, (attentionBilinPoly_eq_zero_iff (M c)).mp hc⟩

/-- **Unique attention permutation** (tex `lem:unique-attention-permutation`).

If the two families of monic linear forms `t - wᵀ B_c v` and `t - wᵀ B'_h v` have equal
products for every `(t, w, v)`, and the primed matrices `B'` are pairwise distinct, then there
is a *unique* permutation `σ` with `B (σ h) = B' h` for every head `h`.

This `σ` is the target-to-source head permutation extracted from the attention matrices; the
value matrices are later carried along the *same* `σ` (no separate value permutation). -/
theorem unique_attention_permutation {d k : ℕ}
    (B B' : Fin k → Matrix (Fin d) (Fin d) ℝ)
    (hB' : Function.Injective B')
    (hid : ∀ (t : ℝ) (w v : Fin d → ℝ),
      ∏ c, (t - w ⬝ᵥ (B c).mulVec v) = ∏ h, (t - w ⬝ᵥ (B' h).mulVec v)) :
    ∃! σ : Equiv.Perm (Fin k), ∀ h, B (σ h) = B' h := by
  classical
  have hExists : ∀ h : Fin k, ∃ c : Fin k, B c = B' h := by
    intro h
    obtain ⟨c, hc⟩ :=
      exists_matrix_eq_zero_of_forall_bilinear_product_eq_zero
        (d := d) (k := k) (fun c : Fin k => B' h - B c) (by
          intro w v
          have hroot := hid (w ⬝ᵥ (B' h).mulVec v) w v
          have hrhs :
              (∏ g : Fin k,
                (w ⬝ᵥ (B' h).mulVec v - w ⬝ᵥ (B' g).mulVec v)) = 0 := by
            exact Finset.prod_eq_zero (Finset.mem_univ h) (by simp)
          calc
            (∏ c : Fin k, w ⬝ᵥ ((B' h - B c).mulVec v))
                = ∏ c : Fin k,
                    (w ⬝ᵥ (B' h).mulVec v - w ⬝ᵥ (B c).mulVec v) := by
                    simp [Matrix.sub_mulVec, dotProduct_sub]
            _ = ∏ g : Fin k,
                    (w ⬝ᵥ (B' h).mulVec v - w ⬝ᵥ (B' g).mulVec v) := hroot
            _ = 0 := hrhs)
    exact ⟨c, (sub_eq_zero.mp hc).symm⟩
  let ρfun : Fin k → Fin k := fun h => Classical.choose (hExists h)
  have hρfun : ∀ h : Fin k, B (ρfun h) = B' h := fun h =>
    Classical.choose_spec (hExists h)
  have hρinj : Function.Injective ρfun := by
    intro h g hhg
    apply hB'
    calc
      B' h = B (ρfun h) := (hρfun h).symm
      _ = B (ρfun g) := by rw [hhg]
      _ = B' g := hρfun g
  have hρbij : Function.Bijective ρfun :=
    hρinj.bijective_of_finite
  let ρ : Equiv.Perm (Fin k) := Equiv.ofBijective ρfun hρbij
  refine ⟨ρ, ?_, ?_⟩
  · intro h
    change B (ρfun h) = B' h
    exact hρfun h
  · intro τ hτ
    apply Equiv.ext
    intro h
    obtain ⟨g, hg⟩ := hρbij.2 (τ h)
    have hg_eq : h = g := by
      apply hB'
      calc
        B' h = B (τ h) := (hτ h).symm
        _ = B (ρfun g) := by rw [← hg]
        _ = B' g := hρfun g
    subst g
    change τ h = ρfun h
    exact hg.symm

/-- Algebraic globalization part of TeX Lemma `lem:global-labeling`.

If the probe product equality holds on a Zariski-dense set of `(w, v)` probes, then the
already-proved unique attention permutation is forced globally at the matrix level. -/
theorem global_labeling_algebraic {d k : ℕ}
    (B B' : Fin k → Matrix (Fin d) (Fin d) ℝ)
    (U : Set ((Fin d → ℝ) × (Fin d → ℝ)))
    (hB' : Function.Injective B')
    (hU : ProbeZariskiDense U)
    (hprodU : ∀ x ∈ U, ∀ t : ℝ,
      ∏ c : Fin k, (t - x.1 ⬝ᵥ (B c).mulVec x.2) =
        ∏ h : Fin k, (t - x.1 ⬝ᵥ (B' h).mulVec x.2)) :
    ∃! ρ : Equiv.Perm (Fin k), ∀ h, B (ρ h) = B' h := by
  exact unique_attention_permutation B B' hB'
    (attention_product_identity_of_probeZariskiDense B B' U hU hprodU)

end TransformerIdentifiability.NLayer.KHead
