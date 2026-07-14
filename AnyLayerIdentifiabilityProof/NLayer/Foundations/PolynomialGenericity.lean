import Mathlib

set_option autoImplicit false
-- These lemmas carry `[Fintype ι]`/`[DecidableEq ι]` because the proofs need them
-- (e.g. `volume` on `ι → ℝ` requires `Fintype ι`), even when they do not appear in the
-- statement type; silence the style linters that only inspect the type.
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open MeasureTheory MvPolynomial

namespace TransformerIdentifiability.NLayer

/-!
# Zero sets of polynomials (genericity toolkit)

This is a self-contained foundation file: it depends only on Mathlib and is imported by
no other module yet, so it can be developed independently of the rest of the
formalization.  It is the Lean counterpart of `n_layer_proof.tex`, Lemma `lem:zariski`
("Zero sets of polynomials"):

* the zero set of a nonzero real multivariate polynomial is closed, has empty interior,
  and Lebesgue measure zero;
* equivalently, `{p ≠ 0}` is open and dense;
* a polynomial vanishing on a nonempty open set is identically zero (identity theorem);
* finitely many nonzero polynomials have a common nonvanishing point in any nonempty
  open set.

These statements support the genericity arguments of Section 3 (`def:generic`,
`prop:genericnonempty`), where each genericity condition is the nonvanishing of finitely
many explicit polynomials of the parameters.
-/

/-- The zero set of a nonzero real multivariate polynomial in `n` variables has Lebesgue
measure zero. Proved by induction on `n` using Fubini. -/
theorem mvpoly_eval_null :
    ∀ (n : ℕ) (p : MvPolynomial (Fin n) ℝ), p ≠ 0 →
      volume {x : Fin n → ℝ | (MvPolynomial.eval x) p = 0} = 0 := by
  intro n
  induction n with
  | zero =>
    intro p hp
    have hc0 : p.coeff 0 ≠ 0 := by
      intro h
      exact hp (by rw [eq_C_of_isEmpty p, h, map_zero])
    have hempty : {x : Fin 0 → ℝ | (MvPolynomial.eval x) p = 0} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      apply hc0
      rw [Set.mem_setOf_eq, eq_C_of_isEmpty p, eval_C] at hx
      exact hx
    rw [hempty, measure_empty]
  | succ n ih =>
    intro p hp
    set q : Polynomial (MvPolynomial (Fin n) ℝ) := finSuccEquiv ℝ n p with hq_def
    have hq : q ≠ 0 := by
      rw [hq_def, Ne, EmbeddingLike.map_eq_zero_iff]
      exact hp
    set c : MvPolynomial (Fin n) ℝ := q.leadingCoeff with hc_def
    have hc : c ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hq
    have hZ : volume {s : Fin n → ℝ | (MvPolynomial.eval s) c = 0} = 0 := ih c hc
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0 with he_def
    set G : (Fin (n + 1) → ℝ) → (Fin n → ℝ) × ℝ := fun x => (Fin.tail x, x 0) with hG_def
    have hGmp : MeasurePreserving G volume (volume.prod volume) := by
      have h1 : MeasurePreserving e volume (volume.prod volume) :=
        volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
      have h2 : MeasurePreserving (Prod.swap : ℝ × (Fin n → ℝ) → (Fin n → ℝ) × ℝ)
          (volume.prod volume) (volume.prod volume) := Measure.measurePreserving_swap
      have hfun : G = Prod.swap ∘ ⇑e := by
        funext x
        have hex : (e x) = (x 0, Fin.tail x) := by
          simp only [e, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_zero]
          rfl
        simp [hG_def, Function.comp_apply, hex]
      rw [hfun]
      exact h2.comp h1
    set T : Set ((Fin n → ℝ) × ℝ) :=
      {z | (MvPolynomial.eval (Fin.cons z.2 z.1 : Fin (n + 1) → ℝ)) p = 0} with hT_def
    have hcons_meas :
        Measurable (fun z : (Fin n → ℝ) × ℝ => (Fin.cons z.2 z.1 : Fin (n + 1) → ℝ)) := by
      rw [measurable_pi_iff]
      intro i
      refine Fin.cases ?_ ?_ i
      · simpa using measurable_snd
      · intro j; simpa using (measurable_pi_apply j).comp measurable_fst
    have hT_meas : MeasurableSet T := by
      have : Measurable (fun z : (Fin n → ℝ) × ℝ =>
          (MvPolynomial.eval (Fin.cons z.2 z.1 : Fin (n + 1) → ℝ)) p) :=
        (MvPolynomial.continuous_eval p).measurable.comp hcons_meas
      exact this (measurableSet_singleton 0)
    have hSeq : {x : Fin (n + 1) → ℝ | (MvPolynomial.eval x) p = 0} = G ⁻¹' T := by
      ext x
      simp only [hG_def, hT_def, Set.mem_preimage, Set.mem_setOf_eq]
      rw [Fin.cons_self_tail]
    rw [hSeq, hGmp.measure_preimage hT_meas.nullMeasurableSet]
    rw [Measure.measure_prod_null hT_meas]
    have hsub : {s : Fin n → ℝ | volume (Prod.mk s ⁻¹' T) ≠ 0} ⊆
        {s : Fin n → ℝ | (MvPolynomial.eval s) c = 0} := by
      intro s hs
      simp only [Set.mem_setOf_eq] at hs ⊢
      by_contra hsc
      apply hs
      have hmap : Polynomial.map (MvPolynomial.eval s) q ≠ 0 := by
        intro h0
        apply hsc
        have hco : (Polynomial.map (MvPolynomial.eval s) q).coeff q.natDegree
            = (MvPolynomial.eval s) c := by
          rw [Polynomial.coeff_map]; rfl
        rw [h0] at hco
        simpa using hco.symm
      have hset :
          (Prod.mk s ⁻¹' T) = {y : ℝ | (Polynomial.map (MvPolynomial.eval s) q).IsRoot y} := by
        ext y
        simp only [hT_def, Set.mem_preimage, Set.mem_setOf_eq, Polynomial.IsRoot.def]
        rw [MvPolynomial.eval_eq_eval_mv_eval' s y p]
      rw [hset]
      exact (Polynomial.finite_setOf_isRoot hmap).measure_zero _
    have key : volume {s : Fin n → ℝ | volume (Prod.mk s ⁻¹' T) ≠ 0} = 0 :=
      measure_mono_null hsub hZ
    have hae : ∀ᵐ s ∂(volume : Measure (Fin n → ℝ)), volume (Prod.mk s ⁻¹' T) = 0 := by
      rw [ae_iff]; simpa using key
    filter_upwards [hae] with s hs
    simpa using hs

/-- Version for an arbitrary finite index type. -/
theorem mvpoly_eval_null' {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : MvPolynomial ι ℝ) (hp : p ≠ 0) :
    volume {x : ι → ℝ | (MvPolynomial.eval x) p = 0} = 0 := by
  classical
  set ev : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι with hev
  set Ψ := MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) ev.symm with hΨdef
  have hΨ : MeasurePreserving Ψ volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : ι => ℝ) ev.symm
  have hmeas : MeasurableSet {x : ι → ℝ | (MvPolynomial.eval x) p = 0} :=
    (MvPolynomial.continuous_eval p).measurable (measurableSet_singleton 0)
  rw [← hΨ.measure_preimage hmeas.nullMeasurableSet]
  have hset : Ψ ⁻¹' {x : ι → ℝ | (MvPolynomial.eval x) p = 0}
      = {y : Fin (Fintype.card ι) → ℝ | (MvPolynomial.eval y) (rename ev p) = 0} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    have hΨy : (Ψ y) = y ∘ ⇑ev := by
      funext a
      have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : ι => ℝ) ev.symm y (ev a)
      simpa [hΨdef] using h
    rw [hΨy, ← MvPolynomial.eval_rename]
  rw [hset]
  refine mvpoly_eval_null _ (rename ev p) ?_
  have := (rename_injective (⇑ev) ev.injective).ne hp
  simpa using this

/-- The nonvanishing set `{p ≠ 0}` is open: it is the preimage of the open set `{0}ᶜ`
under the continuous evaluation map. -/
theorem isOpen_eval_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (p : MvPolynomial ι ℝ) :
    IsOpen {x : ι → ℝ | (MvPolynomial.eval x) p ≠ 0} :=
  (MvPolynomial.continuous_eval p).isOpen_preimage _ isOpen_compl_singleton

/-- The complement of the zero set of a nonzero polynomial is (Euclidean) dense. -/
theorem dense_compl_zero_set {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : MvPolynomial ι ℝ) (hp : p ≠ 0) :
    Dense {x : ι → ℝ | (MvPolynomial.eval x) p ≠ 0} := by
  have hcompl : {x : ι → ℝ | (MvPolynomial.eval x) p ≠ 0}
      = {x : ι → ℝ | (MvPolynomial.eval x) p = 0}ᶜ := rfl
  rw [hcompl, ← interior_eq_empty_iff_dense_compl]
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hpos : 0 < volume (interior {x : ι → ℝ | (MvPolynomial.eval x) p = 0}) :=
    isOpen_interior.measure_pos volume ⟨x, hx⟩
  have hle : volume (interior {x : ι → ℝ | (MvPolynomial.eval x) p = 0})
      ≤ volume {x : ι → ℝ | (MvPolynomial.eval x) p = 0} := measure_mono interior_subset
  rw [mvpoly_eval_null' p hp, nonpos_iff_eq_zero] at hle
  exact hpos.ne' hle

/-! ## Finite nonvanishing families -/

/-- A finite product of nonzero real multivariate polynomials is nonzero. -/
theorem mvpoly_finset_prod_ne_zero {ι κ : Type*} {s : Finset κ}
    {p : κ → MvPolynomial ι ℝ} (hp : ∀ a, a ∈ s → p a ≠ 0) :
    (∏ a ∈ s, p a) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr hp

/-- Evaluation of a finite product is nonzero exactly when every factor evaluates
nonzero. -/
theorem eval_finset_prod_ne_zero_iff {ι κ : Type*} {s : Finset κ}
    {p : κ → MvPolynomial ι ℝ} (x : ι → ℝ) :
    (MvPolynomial.eval x) (∏ a ∈ s, p a) ≠ 0 ↔
      ∀ a, a ∈ s → (MvPolynomial.eval x) (p a) ≠ 0 := by
  rw [map_prod]
  exact Finset.prod_ne_zero_iff

/-- The common nonvanishing locus of a finite polynomial family is open. -/
theorem isOpen_forall_eval_ne_zero_finset {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset κ) (p : κ → MvPolynomial ι ℝ) :
    IsOpen {x : ι → ℝ | ∀ a, a ∈ s → (MvPolynomial.eval x) (p a) ≠ 0} := by
  have hprodOpen : IsOpen {x : ι → ℝ |
      (MvPolynomial.eval x) (∏ a ∈ s, p a) ≠ 0} :=
    isOpen_eval_ne_zero (∏ a ∈ s, p a)
  have hset : {x : ι → ℝ | (MvPolynomial.eval x) (∏ a ∈ s, p a) ≠ 0} =
      {x : ι → ℝ | ∀ a, a ∈ s → (MvPolynomial.eval x) (p a) ≠ 0} := by
    ext x
    exact eval_finset_prod_ne_zero_iff (s := s) (p := p) x
  rw [hset] at hprodOpen
  exact hprodOpen

/-- The common nonvanishing locus of a finite family of nonzero polynomials is dense. -/
theorem dense_forall_eval_ne_zero_finset {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    {s : Finset κ} {p : κ → MvPolynomial ι ℝ}
    (hp : ∀ a, a ∈ s → p a ≠ 0) :
    Dense {x : ι → ℝ | ∀ a, a ∈ s → (MvPolynomial.eval x) (p a) ≠ 0} := by
  have hprodDense : Dense {x : ι → ℝ |
      (MvPolynomial.eval x) (∏ a ∈ s, p a) ≠ 0} :=
    dense_compl_zero_set (∏ a ∈ s, p a) (mvpoly_finset_prod_ne_zero hp)
  have hset : {x : ι → ℝ | (MvPolynomial.eval x) (∏ a ∈ s, p a) ≠ 0} =
      {x : ι → ℝ | ∀ a, a ∈ s → (MvPolynomial.eval x) (p a) ≠ 0} := by
    ext x
    exact eval_finset_prod_ne_zero_iff (s := s) (p := p) x
  rw [hset] at hprodDense
  exact hprodDense

/-- Packaged finite family of nonzero real multivariate polynomials.  Its carrier is
the common nonvanishing locus, the basic open dense set used throughout the genericity
argument. -/
structure PolynomialNonvanishingData (ι κ : Type*) where
  indices : Finset κ
  poly : κ -> MvPolynomial ι ℝ
  nonzero : ∀ a, a ∈ indices -> poly a ≠ 0

namespace PolynomialNonvanishingData

/-- Common nonvanishing locus of a packaged finite polynomial family. -/
def carrier {ι κ : Type*} (D : PolynomialNonvanishingData ι κ) : Set (ι -> ℝ) :=
  {x | ∀ a, a ∈ D.indices -> (MvPolynomial.eval x) (D.poly a) ≠ 0}

theorem isOpen_carrier {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (D : PolynomialNonvanishingData ι κ) :
    IsOpen D.carrier := by
  simpa [carrier] using isOpen_forall_eval_ne_zero_finset D.indices D.poly

theorem dense_carrier {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (D : PolynomialNonvanishingData ι κ) :
    Dense D.carrier := by
  simpa [carrier] using dense_forall_eval_ne_zero_finset D.nonzero

end PolynomialNonvanishingData

/-- **Identity theorem for polynomials.**  A polynomial vanishing on a nonempty open set
is identically zero. -/
theorem eq_zero_of_eval_eqOn_isOpen {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : MvPolynomial ι ℝ} {U : Set (ι → ℝ)} (hU : IsOpen U) (hUne : U.Nonempty)
    (hp : ∀ x ∈ U, (MvPolynomial.eval x) p = 0) : p = 0 := by
  by_contra hne
  obtain ⟨x, hxU, hxne⟩ := (dense_compl_zero_set p hne).inter_open_nonempty U hU hUne
  exact hxne (hp x hxU)

/-! ## Proper linear subspaces

The final clause of `lem:zariski`: a finite union of proper linear subspaces of a
finite-dimensional real vector space is Lebesgue (Haar) null, hence has empty interior.
This is used in Section 3, where the exceptional set `N` is a finite union of proper
algebraic subsets of the parameter space. -/

end TransformerIdentifiability.NLayer
