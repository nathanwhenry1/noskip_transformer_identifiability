import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Analytic.LaurentNormalForm
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.FormalStreams

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.NoSkip

/-!
# Selected-variable splits for NoSkip formal polynomials

The splitting construction is model-independent.  Its NoSkip specialization
uses NS031 only through `FormalPolySupportBefore` and
`formalSlope_supportBefore`; no stream recurrence or network evaluation is
unfolded.  Quadratic/block-degree refinements are deliberately left to the
later selected-top layer.
-/

noncomputable section

/-- Coefficient of `x^s` after erasing `x` from every contributing monomial. -/
noncomputable def coeffOfVar {L k : Nat} (x : FormalVar L k) (s : Nat)
    (f : FormalPoly L k) : FormalPoly L k :=
  ∑ m ∈ f.support.filter (fun m => m x = s),
    (MvPolynomial.monomial (Finsupp.erase x m) (f.coeff m) : FormalPoly L k)

/-- Every coefficient-support monomial comes from an original support monomial
with the selected exponent, after erasing the selected variable. -/
theorem coeffOfVar_support_exists {L k : Nat} {x : FormalVar L k} {s : Nat}
    {f : FormalPoly L k} {m : FormalVar L k →₀ Nat}
    (hm : m ∈ (coeffOfVar x s f).support) :
    ∃ u ∈ f.support, u x = s ∧ m = Finsupp.erase x u := by
  classical
  have hmem :
      m ∈ (f.support.filter (fun u => u x = s)).biUnion
        (fun u =>
          (MvPolynomial.monomial (Finsupp.erase x u) (f.coeff u) :
            FormalPoly L k).support) := by
    exact MvPolynomial.support_sum
      (s := f.support.filter (fun u => u x = s))
      (f := fun u =>
        (MvPolynomial.monomial (Finsupp.erase x u) (f.coeff u) :
          FormalPoly L k))
      (by simpa [coeffOfVar] using hm)
  rcases Finset.mem_biUnion.mp hmem with ⟨u, hu, hmterm⟩
  have hu_support : u ∈ f.support := (Finset.mem_filter.mp hu).1
  have hux : u x = s := (Finset.mem_filter.mp hu).2
  have hsub :
      (MvPolynomial.monomial (Finsupp.erase x u) (f.coeff u) :
        FormalPoly L k).support ⊆
        ({Finsupp.erase x u} : Finset (FormalVar L k →₀ Nat)) :=
    MvPolynomial.support_monomial_subset
  have hm_eq : m = Finsupp.erase x u := by
    simpa using hsub hmterm
  exact ⟨u, hu_support, hux, hm_eq⟩

/-- The selected variable is absent from its coefficient polynomial. -/
theorem coeffOfVar_notMem_vars {L k : Nat} {x : FormalVar L k} {s : Nat}
    {f : FormalPoly L k} :
    x ∉ (coeffOfVar x s f).vars := by
  classical
  intro hxvars
  rcases (MvPolynomial.mem_vars_iff_mem_support
    (p := coeffOfVar x s f) x).mp hxvars with ⟨m, hm, hxmem⟩
  rcases coeffOfVar_support_exists hm with ⟨u, _hu, _hux, rfl⟩
  have hx_nonzero : (Finsupp.erase x u) x ≠ 0 :=
    Finsupp.mem_support_iff.mp hxmem
  exact hx_nonzero (by simp)

/-- Erasing a selected variable preserves a strict layer-prefix support bound. -/
theorem coeffOfVar_supportBefore {L k n : Nat}
    {x : FormalVar L k} {s : Nat} {f : FormalPoly L k}
    (hf : FormalPolySupportBefore n f) :
    FormalPolySupportBefore n (coeffOfVar x s f) := by
  classical
  intro m hm y hy
  rcases coeffOfVar_support_exists hm with ⟨u, hu, _hux, rfl⟩
  by_cases hyx : y = x
  · subst y
    simp
  · simpa [Finsupp.erase_ne hyx] using hf u hu y hy

/-- Evaluation depends only on values assigned to variables occurring in the
polynomial. -/
theorem evalFormalPolyComplex_congr_on_vars {L k : Nat} (f : FormalPoly L k)
    {z1 z2 : FormalVar L k → ℂ}
    (hagree : ∀ x ∈ f.vars, z1 x = z2 x) :
    evalFormalPolyComplex z1 f = evalFormalPolyComplex z2 f := by
  unfold evalFormalPolyComplex
  apply MvPolynomial.eval₂_congr
  intro x m hx hm
  exact hagree x ((MvPolynomial.mem_vars_iff_mem_support x).2
    ⟨m, MvPolynomial.mem_support_iff.mpr hm, hx⟩)

/-- Split one evaluated monomial into its erased part and selected-variable
power. -/
theorem evalFormalPolyComplex_monomial_erase_mul_pow {L k : Nat}
    (z : FormalVar L k → ℂ) (x : FormalVar L k)
    (m : FormalVar L k →₀ Nat) (c : ℝ) :
    evalFormalPolyComplex z
        (MvPolynomial.monomial m c : FormalPoly L k) =
      evalFormalPolyComplex z
        (MvPolynomial.monomial (Finsupp.erase x m) c : FormalPoly L k) *
          (z x) ^ m x := by
  have hsplit : Finsupp.erase x m + Finsupp.single x (m x) = m := by
    ext y
    by_cases hy : y = x
    · subst y
      simp
    · simp [Finsupp.erase_ne hy, Finsupp.single_eq_of_ne hy]
  calc
    evalFormalPolyComplex z (MvPolynomial.monomial m c : FormalPoly L k)
        = evalFormalPolyComplex z
            (MvPolynomial.monomial
              (Finsupp.erase x m + Finsupp.single x (m x)) c :
                FormalPoly L k) := by rw [hsplit]
    _ = evalFormalPolyComplex z
          (MvPolynomial.monomial (Finsupp.erase x m) c *
            MvPolynomial.X x ^ m x : FormalPoly L k) := by
          rw [MvPolynomial.monomial_add_single]
    _ = evalFormalPolyComplex z
          (MvPolynomial.monomial (Finsupp.erase x m) c : FormalPoly L k) *
            (z x) ^ m x := by
          simp [evalFormalPolyComplex]

/-- Reconstruct evaluation from selected-variable coefficients under a finite
degree bound. -/
theorem evalFormalPolyComplex_eq_sum_coeffOfVar {L k : Nat}
    {x : FormalVar L k} {D : Nat} {f : FormalPoly L k}
    (hD : MvPolynomial.degreeOf x f ≤ D) (z : FormalVar L k → ℂ) :
    evalFormalPolyComplex z f =
      ∑ s ∈ Finset.range (D + 1),
        evalFormalPolyComplex z (coeffOfVar x s f) * (z x) ^ s := by
  classical
  let B : (FormalVar L k →₀ Nat) → ℂ := fun m =>
    evalFormalPolyComplex z
      (MvPolynomial.monomial (Finsupp.erase x m) (f.coeff m) :
        FormalPoly L k) * (z x) ^ m x
  have hmaps : ∀ m ∈ f.support, m x ∈ Finset.range (D + 1) := by
    intro m hm
    exact Finset.mem_range.mpr
      (Nat.lt_succ_of_le ((MvPolynomial.degreeOf_le_iff.mp hD) m hm))
  have hfiber :
      (∑ s ∈ Finset.range (D + 1),
        ∑ m ∈ f.support with m x = s, B m) = ∑ m ∈ f.support, B m := by
    simpa using
      (Finset.sum_fiberwise_of_maps_to
        (s := f.support) (t := Finset.range (D + 1))
        (g := fun m : FormalVar L k →₀ Nat => m x) hmaps B)
  have hcoeff_eval : ∀ s : Nat,
      evalFormalPolyComplex z (coeffOfVar x s f) * (z x) ^ s =
        ∑ m ∈ f.support with m x = s, B m := by
    intro s
    have heval_coeff :
        evalFormalPolyComplex z (coeffOfVar x s f) =
          ∑ m ∈ f.support.filter (fun m => m x = s),
            evalFormalPolyComplex z
              (MvPolynomial.monomial (Finsupp.erase x m) (f.coeff m) :
                FormalPoly L k) := by
      simp only [coeffOfVar, evalFormalPolyComplex]
      change MvPolynomial.eval₂Hom (algebraMap ℝ ℂ) z
          (∑ m ∈ f.support.filter (fun m => m x = s),
            (MvPolynomial.monomial (Finsupp.erase x m) (f.coeff m) :
              FormalPoly L k)) =
        ∑ m ∈ f.support.filter (fun m => m x = s),
          MvPolynomial.eval₂Hom (algebraMap ℝ ℂ) z
            (MvPolynomial.monomial (Finsupp.erase x m) (f.coeff m) :
              FormalPoly L k)
      simp only [map_sum]
    calc
      evalFormalPolyComplex z (coeffOfVar x s f) * (z x) ^ s
          = (∑ m ∈ f.support with m x = s,
              evalFormalPolyComplex z
                (MvPolynomial.monomial (Finsupp.erase x m) (f.coeff m) :
                  FormalPoly L k)) * (z x) ^ s := by rw [heval_coeff]
      _ = ∑ m ∈ f.support with m x = s,
            evalFormalPolyComplex z
              (MvPolynomial.monomial (Finsupp.erase x m) (f.coeff m) :
                FormalPoly L k) * (z x) ^ s := by rw [Finset.sum_mul]
      _ = ∑ m ∈ f.support with m x = s, B m := by
        refine Finset.sum_congr rfl ?_
        intro m hm
        have hmx : m x = s := (Finset.mem_filter.mp hm).2
        simp [B, hmx]
  have hmono_sum_eval :
      evalFormalPolyComplex z
          (∑ m ∈ f.support,
            (MvPolynomial.monomial m (f.coeff m) : FormalPoly L k)) =
        ∑ m ∈ f.support,
          evalFormalPolyComplex z
            (MvPolynomial.monomial m (f.coeff m) : FormalPoly L k) := by
    simp only [evalFormalPolyComplex]
    change MvPolynomial.eval₂Hom (algebraMap ℝ ℂ) z
        (∑ m ∈ f.support,
          (MvPolynomial.monomial m (f.coeff m) : FormalPoly L k)) =
      ∑ m ∈ f.support, MvPolynomial.eval₂Hom (algebraMap ℝ ℂ) z
        (MvPolynomial.monomial m (f.coeff m) : FormalPoly L k)
    simp only [map_sum]
  calc
    evalFormalPolyComplex z f
        = evalFormalPolyComplex z
            (∑ m ∈ f.support,
              (MvPolynomial.monomial m (f.coeff m) : FormalPoly L k)) := by
          exact congrArg (evalFormalPolyComplex z) (MvPolynomial.as_sum f)
    _ = ∑ m ∈ f.support,
          evalFormalPolyComplex z
            (MvPolynomial.monomial m (f.coeff m) : FormalPoly L k) :=
          hmono_sum_eval
    _ = ∑ m ∈ f.support, B m := by
          refine Finset.sum_congr rfl ?_
          intro m _hm
          exact evalFormalPolyComplex_monomial_erase_mul_pow
            z x m (f.coeff m)
    _ = ∑ s ∈ Finset.range (D + 1),
          ∑ m ∈ f.support with m x = s, B m := hfiber.symm
    _ = ∑ s ∈ Finset.range (D + 1),
          evalFormalPolyComplex z (coeffOfVar x s f) * (z x) ^ s := by
          refine Finset.sum_congr rfl ?_
          intro s _hs
          exact (hcoeff_eval s).symm

/-- Canonical reconstruction using the polynomial's actual selected-variable
degree. -/
theorem evalFormalPolyComplex_eq_sum_coeffOfVar_degreeOf {L k : Nat}
    (x : FormalVar L k) (f : FormalPoly L k) (z : FormalVar L k → ℂ) :
    evalFormalPolyComplex z f =
      ∑ s ∈ Finset.range (MvPolynomial.degreeOf x f + 1),
        evalFormalPolyComplex z (coeffOfVar x s f) * (z x) ^ s :=
  evalFormalPolyComplex_eq_sum_coeffOfVar le_rfl z

/-- Explicit constant/linear/quadratic evaluation normal form. -/
theorem evalFormalPolyComplex_eq_coeff_zero_add_one_add_two {L k : Nat}
    {x : FormalVar L k} {f : FormalPoly L k}
    (hdegree : MvPolynomial.degreeOf x f ≤ 2)
    (z : FormalVar L k → ℂ) :
    evalFormalPolyComplex z f =
      evalFormalPolyComplex z (coeffOfVar x 0 f) +
        evalFormalPolyComplex z (coeffOfVar x 1 f) * z x +
        evalFormalPolyComplex z (coeffOfVar x 2 f) * (z x) ^ 2 := by
  rw [evalFormalPolyComplex_eq_sum_coeffOfVar hdegree z]
  simp [Finset.sum_range_succ, pow_two]

/-- NoSkip slope coefficients retain the strict prefix-support bound. -/
theorem formalSlope_coeffOfVar_supportBefore {L k d : Nat}
    (theta : Params L k d) (w v : Vec d) (l : Fin L) (a : Fin k)
    (x : FormalVar L k) (s : Nat) :
    FormalPolySupportBefore l.1
      (coeffOfVar x s (formalSlope theta w v l a)) :=
  coeffOfVar_supportBefore (formalSlope_supportBefore theta w v l a)

/-- The split variable is absent from every NoSkip slope coefficient. -/
theorem formalSlope_coeffOfVar_notMem_vars {L k d : Nat}
    (theta : Params L k d) (w v : Vec d) (l : Fin L) (a : Fin k)
    (x : FormalVar L k) (s : Nat) :
    x ∉ (coeffOfVar x s (formalSlope theta w v l a)).vars :=
  coeffOfVar_notMem_vars

/-- Canonical selected-variable split of a NoSkip formal slope. -/
theorem eval_complexFormalSlope_eq_sum_coeffOfVar {L k d : Nat}
    (theta : Params L k d) (w v : Vec d) (l : Fin L) (a : Fin k)
    (x : FormalVar L k) (z : FormalVar L k → ℂ) :
    complexFormalSlope theta w v z (l, a) =
      ∑ s ∈ Finset.range
          (MvPolynomial.degreeOf x (formalSlope theta w v l a) + 1),
        evalFormalPolyComplex z
          (coeffOfVar x s (formalSlope theta w v l a)) * (z x) ^ s := by
  exact evalFormalPolyComplex_eq_sum_coeffOfVar_degreeOf
    x (formalSlope theta w v l a) z

/-- Quadratic selected-variable split of a NoSkip formal slope, parameterized
by the degree bound proved by the downstream selected-top package. -/
theorem eval_complexFormalSlope_eq_coeff_zero_add_one_add_two {L k d : Nat}
    (theta : Params L k d) (w v : Vec d) (l : Fin L) (a : Fin k)
    (x : FormalVar L k)
    (hdegree : MvPolynomial.degreeOf x (formalSlope theta w v l a) ≤ 2)
    (z : FormalVar L k → ℂ) :
    complexFormalSlope theta w v z (l, a) =
      evalFormalPolyComplex z (coeffOfVar x 0 (formalSlope theta w v l a)) +
        evalFormalPolyComplex z (coeffOfVar x 1 (formalSlope theta w v l a)) * z x +
        evalFormalPolyComplex z (coeffOfVar x 2 (formalSlope theta w v l a)) *
          (z x) ^ 2 :=
  evalFormalPolyComplex_eq_coeff_zero_add_one_add_two hdegree z

end

end TransformerIdentifiability.NLayer.NoSkip
