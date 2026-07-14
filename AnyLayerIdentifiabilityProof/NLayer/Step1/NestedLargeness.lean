import AnyLayerIdentifiabilityProof.NLayer.Analytic.AlgebraicQuadric
import AnyLayerIdentifiabilityProof.NLayer.Foundations.DominantTopCoeff

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer

/-!
# Step 1 nested largeness

Owner shard for the abstract multivariate nested-largeness theorem and the API for
continuous thresholds and nonvanishing regions.
-/

/-! ## Dominant-product packaging -/

/-- A finite-indexed polynomial family whose members all have dominant top coefficients.

This is a thin Step 1 wrapper around the reusable facts from `DominantTopCoeff.lean`; it
lets the polynomial-family shard package `f_2, ..., f_L, g` once and then ask for the
dominant top coefficient of any finite product. -/
structure DominantPolynomialFamily (ι σ R : Type*) [Fintype σ] [DecidableEq σ]
    [CommRing R] where
  poly : ι -> MvPolynomial σ R
  hasDominantTopCoeff : ∀ a, HasDominantTopCoeff (poly a)

namespace DominantPolynomialFamily

variable {ι σ R : Type*} [Fintype σ] [DecidableEq σ] [CommRing R] [IsDomain R]

/-- The product of a finite subfamily still has a dominant top coefficient. -/
theorem hasDominantTopCoeff_prod (F : DominantPolynomialFamily ι σ R) (s : Finset ι) :
    HasDominantTopCoeff (∏ a ∈ s, F.poly a) :=
  HasDominantTopCoeff.prod s F.hasDominantTopCoeff

end DominantPolynomialFamily

/-! ## One-step evaluator presentations -/

/-- Evaluator-form presentation of a polynomial in one new variable:
`lead x * z^degree + sum_{i<degree} lower_i x * z^i`.

The base type `α` is intentionally abstract.  Downstream polynomial shards can instantiate
it with previous-coordinate spaces such as `Fin m -> ℂ`, while analytic shards can use the
same API for already-evaluated coefficient functions. -/
structure TailPresentation (α : Type*) where
  degree : Nat
  lead : α -> ℂ
  lower : Fin degree -> α -> ℂ

namespace TailPresentation

/-- Evaluate a one-step tail presentation. -/
noncomputable def eval {α : Type*} (P : TailPresentation α) (x : α) (z : ℂ) : ℂ :=
  tailPolynomial P.degree P.lead P.lower x z

/-- The explicit threshold supplied by the one-step algebraic estimate. -/
noncomputable def threshold {α : Type*} (P : TailPresentation α) (x : α) : ℝ :=
  tailThreshold P.degree P.lead P.lower x

/-- The one-step threshold is positive at points where the leading coefficient is nonzero. -/
theorem threshold_pos {α : Type*} (P : TailPresentation α) {x : α}
    (hlead : P.lead x ≠ 0) :
    0 < P.threshold x := by
  simpa [threshold] using
    tailThreshold_pos (D := P.degree) (lead := P.lead) (lower := P.lower) hlead

/-- Continuity of the one-step threshold on any base region where the leading coefficient
is continuous and zero-free, and the lower coefficients are continuous. -/
theorem continuousOn_threshold {α : Type*} [TopologicalSpace α]
    (P : TailPresentation α) {U : Set α}
    (hlead_cont : ContinuousOn P.lead U)
    (hlower_cont : ∀ i : Fin P.degree, ContinuousOn (P.lower i) U)
    (hlead_ne : ∀ x ∈ U, P.lead x ≠ 0) :
    ContinuousOn P.threshold U := by
  simpa [threshold] using
    continuousOn_tailThreshold (D := P.degree) (lead := P.lead) (lower := P.lower)
      hlead_cont hlower_cont hlead_ne

/-- Nonvanishing outside the one-step threshold.  The degree-zero case reduces to
nonvanishing of the leading coefficient. -/
theorem eval_ne_zero_of_threshold {α : Type*} (P : TailPresentation α)
    {x : α} {z : ℂ}
    (hlead : P.lead x ≠ 0)
    (hlarge : P.threshold x < ‖z‖) :
    P.eval x z ≠ 0 := by
  cases P with
  | mk degree lead lower =>
      dsimp [eval, threshold] at hlead hlarge ⊢
      cases degree with
      | zero =>
          simpa [tailPolynomial] using hlead
      | succ D =>
          exact tailPolynomial_ne_zero_of_tailThreshold
            (D := Nat.succ D) (lead := lead) (lower := lower)
            (x := x) (z := z) (Nat.succ_pos D) hlead hlarge

/-- A degree-zero tail presentation does not depend on the new variable, so its evaluation
is just its leading coefficient. -/
theorem eval_eq_lead_of_degree_eq_zero {α : Type*}
    (P : TailPresentation α) (hdegree : P.degree = 0) (x : α) (z : ℂ) :
    P.eval x z = P.lead x := by
  cases P with
  | mk degree lead lower =>
      dsimp at hdegree ⊢
      subst degree
      simp [TailPresentation.eval, tailPolynomial]

end TailPresentation

/-! ## Recursive nested regions -/

/-- Drop the last coordinate from a length-`m+1` coordinate vector. -/
def nestedInit {m : Nat} (z : Fin (m + 1) -> ℂ) : Fin m -> ℂ :=
  fun i => z i.castSucc

/-- The last coordinate of a length-`m+1` coordinate vector. -/
def nestedLast {m : Nat} (z : Fin (m + 1) -> ℂ) : ℂ :=
  z ⟨m, Nat.lt_succ_self m⟩

theorem continuous_nestedInit {m : Nat} :
    Continuous (nestedInit (m := m)) := by
  unfold nestedInit
  fun_prop

theorem continuous_nestedLast {m : Nat} :
    Continuous (nestedLast (m := m)) := by
  unfold nestedLast
  fun_prop

/-! ## Last-variable polynomial tail presentations -/

/-- The coordinate permutation that moves the last coordinate of `Fin (m+1)` to `0` and
sends each earlier coordinate `i.castSucc` to `i.succ`.

This is the adapter between the `finSuccEquiv` convention, which peels coordinate `0`,
and the nested-region convention, which peels the last coordinate. -/
def nestedLastToFrontEquiv (m : Nat) : Fin (m + 1) ≃ Fin (m + 1) :=
  (_root_.finSuccEquivLast (n := m)).trans (_root_.finSuccEquiv m).symm

@[simp] theorem nestedLastToFrontEquiv_last (m : Nat) :
    nestedLastToFrontEquiv m (Fin.last m) = (0 : Fin (m + 1)) := by
  simp [nestedLastToFrontEquiv, _root_.finSuccEquiv_symm_none]

@[simp] theorem nestedLastToFrontEquiv_castSucc {m : Nat} (i : Fin m) :
    nestedLastToFrontEquiv m i.castSucc = i.succ := by
  simp [nestedLastToFrontEquiv, _root_.finSuccEquiv_symm_some]

/-- The front-coordinate vector built from `nestedLast` and `nestedInit` agrees with the
original vector after the last-to-front permutation. -/
theorem fin_cons_nestedLast_nestedInit_comp_nestedLastToFrontEquiv {m : Nat}
    (z : Fin (m + 1) -> ℂ) :
    (Fin.cons (nestedLast z) (nestedInit z)) ∘ nestedLastToFrontEquiv m = z := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [Function.comp_apply, nestedLastToFrontEquiv_last, Fin.cons_zero]
    unfold nestedLast
    rfl
  · simp [nestedInit]

/-- View a polynomial in `m+1` variables as a one-variable polynomial in the last
coordinate, with coefficients in the previous `m` variables. -/
noncomputable def lastVariablePolynomial {m : Nat}
    (p : MvPolynomial (Fin (m + 1)) ℂ) : Polynomial (MvPolynomial (Fin m) ℂ) :=
  MvPolynomial.finSuccEquiv ℂ m (MvPolynomial.rename (nestedLastToFrontEquiv m) p)

/-- The evaluator-form tail presentation obtained from the last-variable polynomial
decomposition. -/
noncomputable def polynomialTailPresentation {m : Nat}
    (p : MvPolynomial (Fin (m + 1)) ℂ) : TailPresentation (Fin m -> ℂ) where
  degree := (lastVariablePolynomial p).natDegree
  lead := fun x => MvPolynomial.eval x (lastVariablePolynomial p).leadingCoeff
  lower := fun i x => MvPolynomial.eval x ((lastVariablePolynomial p).coeff (i : Nat))

/-- A polynomial evaluated by coefficients up to its original `natDegree`, allowing the
top coefficient to vanish after applying the coefficient homomorphism. -/
theorem Polynomial.eval₂_eq_leadingCoeff_add_sum_fin_natDegree
    {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (q : Polynomial R) (y : S) :
    q.eval₂ f y =
      f q.leadingCoeff * y ^ q.natDegree +
        ∑ i : Fin q.natDegree, f (q.coeff (i : Nat)) * y ^ (i : Nat) := by
  rw [Polynomial.eval₂_eq_sum_range' f (p := q) (n := q.natDegree + 1)
    (Nat.lt_succ_self q.natDegree) y]
  rw [Finset.sum_range_succ]
  rw [← Fin.sum_univ_eq_sum_range (fun i => f (q.coeff i) * y ^ i) q.natDegree]
  rw [add_comm]
  rw [Polynomial.leadingCoeff]

/-- The coefficient expansion of a peeled polynomial is exactly the abstract
`tailPolynomial` evaluator. -/
theorem tailPolynomial_lastVariablePolynomial_eq_eval_map {m : Nat}
    (q : Polynomial (MvPolynomial (Fin m) ℂ)) (x : Fin m -> ℂ) (y : ℂ) :
    tailPolynomial q.natDegree
        (fun x => MvPolynomial.eval x q.leadingCoeff)
        (fun i x => MvPolynomial.eval x (q.coeff (i : Nat))) x y =
      Polynomial.eval y (Polynomial.map (MvPolynomial.eval x) q) := by
  rw [← Polynomial.eval₂_eq_eval_map (MvPolynomial.eval x) (p := q) (x := y)]
  symm
  simpa [tailPolynomial] using
    Polynomial.eval₂_eq_leadingCoeff_add_sum_fin_natDegree
      (MvPolynomial.eval x) q y

/-- Evaluation of the extracted tail presentation equals evaluation of the renamed
polynomial with the last variable placed first. -/
theorem polynomialTailPresentation_eval_eq_eval_rename {m : Nat}
    (p : MvPolynomial (Fin (m + 1)) ℂ) (x : Fin m -> ℂ) (y : ℂ) :
    (polynomialTailPresentation p).eval x y =
      MvPolynomial.eval (Fin.cons y x)
        (MvPolynomial.rename (nestedLastToFrontEquiv m) p) := by
  calc
    (polynomialTailPresentation p).eval x y
        = Polynomial.eval y
            (Polynomial.map (MvPolynomial.eval x) (lastVariablePolynomial p)) := by
            simpa [polynomialTailPresentation, TailPresentation.eval] using
              tailPolynomial_lastVariablePolynomial_eq_eval_map
                (q := lastVariablePolynomial p) x y
    _ = MvPolynomial.eval (Fin.cons y x)
          (MvPolynomial.rename (nestedLastToFrontEquiv m) p) := by
          exact (MvPolynomial.eval_eq_eval_mv_eval' x y
            (MvPolynomial.rename (nestedLastToFrontEquiv m) p)).symm

/-- Evaluation theorem for the generic last-variable tail presentation, stated in the
`nestedInit`/`nestedLast` coordinates used by nested regions. -/
theorem polynomialTailPresentation_eval_nested {m : Nat}
    (p : MvPolynomial (Fin (m + 1)) ℂ) (z : Fin (m + 1) -> ℂ) :
    (polynomialTailPresentation p).eval (nestedInit z) (nestedLast z) =
      MvPolynomial.eval z p := by
  rw [polynomialTailPresentation_eval_eq_eval_rename]
  rw [MvPolynomial.eval_rename]
  rw [fin_cons_nestedLast_nestedInit_comp_nestedLastToFrontEquiv]

/-- The extracted leading coefficient evaluator is continuous. -/
theorem continuous_polynomialTailPresentation_lead {m : Nat}
    (p : MvPolynomial (Fin (m + 1)) ℂ) :
    Continuous (polynomialTailPresentation p).lead := by
  dsimp [polynomialTailPresentation]
  exact MvPolynomial.continuous_eval _

/-- The extracted lower coefficient evaluators are continuous. -/
theorem continuous_polynomialTailPresentation_lower {m : Nat}
    (p : MvPolynomial (Fin (m + 1)) ℂ)
    (i : Fin (polynomialTailPresentation p).degree) :
    Continuous ((polynomialTailPresentation p).lower i) := by
  dsimp [polynomialTailPresentation]
  exact MvPolynomial.continuous_eval _

/-- Compiled data interface for downstream workers that want to consume an arbitrary
polynomial tail presentation without unfolding the construction. -/
structure PolynomialTailPresentationData (m : Nat) where
  poly : MvPolynomial (Fin (m + 1)) ℂ
  presentation : TailPresentation (Fin m -> ℂ)
  eval_eq :
    ∀ z : Fin (m + 1) -> ℂ,
      presentation.eval (nestedInit z) (nestedLast z) = MvPolynomial.eval z poly

namespace PolynomialTailPresentationData

/-- The canonical data package from the generic last-variable extraction. -/
noncomputable def ofPolynomial {m : Nat}
    (p : MvPolynomial (Fin (m + 1)) ℂ) : PolynomialTailPresentationData m where
  poly := p
  presentation := polynomialTailPresentation p
  eval_eq := polynomialTailPresentation_eval_nested p

/-- Evaluation helper for compiled polynomial tail-presentation data. -/
theorem eval_nested {m : Nat} (D : PolynomialTailPresentationData m)
    (z : Fin (m + 1) -> ℂ) :
    D.presentation.eval (nestedInit z) (nestedLast z) = MvPolynomial.eval z D.poly :=
  D.eval_eq z

end PolynomialTailPresentationData

/-- Recursive nested largeness regions.

`NestedRegion R 0 = univ`, and `NestedRegion R (m+1)` consists of points whose first
`m` coordinates lie in `NestedRegion R m` and whose last coordinate is larger than the
threshold `R m` evaluated on that prefix. -/
def NestedRegion (R : (m : Nat) -> (Fin m -> ℂ) -> ℝ) :
    (m : Nat) -> Set (Fin m -> ℂ)
  | 0 => Set.univ
  | m + 1 =>
      {z | nestedInit z ∈ NestedRegion R m ∧ R m (nestedInit z) < ‖nestedLast z‖}

@[simp] theorem mem_nestedRegion_zero
    (R : (m : Nat) -> (Fin m -> ℂ) -> ℝ) (z : Fin 0 -> ℂ) :
    z ∈ NestedRegion R 0 := by
  trivial

@[simp] theorem mem_nestedRegion_succ
    (R : (m : Nat) -> (Fin m -> ℂ) -> ℝ) {m : Nat} {z : Fin (m + 1) -> ℂ} :
    z ∈ NestedRegion R (m + 1) ↔
      nestedInit z ∈ NestedRegion R m ∧ R m (nestedInit z) < ‖nestedLast z‖ :=
  Iff.rfl

/-- If each threshold is continuous on the previous nested region, then every nested
region is open. -/
theorem isOpen_nestedRegion
    (R : (m : Nat) -> (Fin m -> ℂ) -> ℝ)
    (hR : ∀ m : Nat, ContinuousOn (R m) (NestedRegion R m)) :
    ∀ m : Nat, IsOpen (NestedRegion R m) := by
  intro m
  induction m with
  | zero =>
      simp
  | succ m ih =>
      let baseSet : Set (Fin (m + 1) -> ℂ) := nestedInit ⁻¹' NestedRegion R m
      have hbaseOpen : IsOpen baseSet :=
        ih.preimage (continuous_nestedInit (m := m))
      have hRcomp :
          ContinuousOn (fun z : Fin (m + 1) -> ℂ => R m (nestedInit z)) baseSet := by
        simpa [baseSet, Function.comp_def] using
          (hR m).comp (continuous_nestedInit (m := m)).continuousOn
            (by intro z hz; exact hz)
      have hlast :
          ContinuousOn (fun z : Fin (m + 1) -> ℂ => ‖nestedLast z‖) baseSet :=
        ((continuous_nestedLast (m := m)).norm).continuousOn
      have hpair :
          ContinuousOn
            (fun z : Fin (m + 1) -> ℂ => (R m (nestedInit z), ‖nestedLast z‖))
            baseSet :=
        hRcomp.prodMk hlast
      have hlt : IsOpen {p : ℝ × ℝ | p.1 < p.2} :=
        isOpen_lt continuous_fst continuous_snd
      have hopen :
          IsOpen
            (baseSet ∩
              (fun z : Fin (m + 1) -> ℂ => (R m (nestedInit z), ‖nestedLast z‖)) ⁻¹'
                {p : ℝ × ℝ | p.1 < p.2}) :=
        hpair.isOpen_inter_preimage hbaseOpen hlt
      simpa [NestedRegion, baseSet] using hopen

/-! ## Nested evaluator families -/

/-- A tower of one-step tail presentations, one for each new coordinate. -/
structure NestedTailFamily where
  step : (m : Nat) -> TailPresentation (Fin m -> ℂ)

namespace NestedTailFamily

/-- The threshold tower associated to a nested evaluator family. -/
noncomputable def threshold (F : NestedTailFamily) (m : Nat) (x : Fin m -> ℂ) : ℝ :=
  (F.step m).threshold x

/-- The recursive nested regions associated to a nested evaluator family. -/
noncomputable def region (F : NestedTailFamily) (m : Nat) : Set (Fin m -> ℂ) :=
  NestedRegion F.threshold m

/-- Strengthened nested regions that also record zero-freeness of the next leading
coefficient at each constructed level.  This leaves `region` unchanged while providing
an API whose membership directly supplies the leading-coefficient hypothesis needed by
the one-step threshold estimate. -/
noncomputable def zeroFreeRegion (F : NestedTailFamily) :
    (m : Nat) -> Set (Fin m -> ℂ)
  | 0 => {x | (F.step 0).lead x ≠ 0}
  | m + 1 =>
      {z | nestedInit z ∈ F.zeroFreeRegion m ∧
           F.threshold m (nestedInit z) < ‖nestedLast z‖ ∧
           (F.step (m + 1)).lead z ≠ 0}

/-- Evaluate the `m`th one-step presentation on a length-`m+1` vector. -/
noncomputable def evalStep (F : NestedTailFamily) {m : Nat}
    (z : Fin (m + 1) -> ℂ) : ℂ :=
  (F.step m).eval (nestedInit z) (nestedLast z)

@[simp] theorem mem_region_zero (F : NestedTailFamily) (z : Fin 0 -> ℂ) :
    z ∈ F.region 0 := by
  simp [region]

@[simp] theorem mem_region_succ (F : NestedTailFamily) {m : Nat}
    {z : Fin (m + 1) -> ℂ} :
    z ∈ F.region (m + 1) ↔
      nestedInit z ∈ F.region m ∧ F.threshold m (nestedInit z) < ‖nestedLast z‖ := by
  rfl

/-- Prefix membership for a nested evaluator family. -/
theorem nestedInit_mem_of_mem_region (F : NestedTailFamily) {m : Nat}
    {z : Fin (m + 1) -> ℂ} (hz : z ∈ F.region (m + 1)) :
    nestedInit z ∈ F.region m :=
  hz.1

/-- The last-coordinate threshold inequality for a nested evaluator family. -/
theorem nestedLast_large_of_mem_region (F : NestedTailFamily) {m : Nat}
    {z : Fin (m + 1) -> ℂ} (hz : z ∈ F.region (m + 1)) :
    F.threshold m (nestedInit z) < ‖nestedLast z‖ :=
  hz.2

@[simp] theorem mem_zeroFreeRegion_zero (F : NestedTailFamily) (z : Fin 0 -> ℂ) :
    z ∈ F.zeroFreeRegion 0 ↔ (F.step 0).lead z ≠ 0 := by
  rfl

@[simp] theorem mem_zeroFreeRegion_succ (F : NestedTailFamily) {m : Nat}
    {z : Fin (m + 1) -> ℂ} :
    z ∈ F.zeroFreeRegion (m + 1) ↔
      nestedInit z ∈ F.zeroFreeRegion m ∧
        F.threshold m (nestedInit z) < ‖nestedLast z‖ ∧
        (F.step (m + 1)).lead z ≠ 0 := by
  rfl

/-- Prefix membership for a zero-free nested evaluator family. -/
theorem nestedInit_mem_of_mem_zeroFreeRegion (F : NestedTailFamily) {m : Nat}
    {z : Fin (m + 1) -> ℂ} (hz : z ∈ F.zeroFreeRegion (m + 1)) :
    nestedInit z ∈ F.zeroFreeRegion m :=
  hz.1

/-- The last-coordinate threshold inequality on zero-free nested regions. -/
theorem nestedLast_large_of_mem_zeroFreeRegion (F : NestedTailFamily) {m : Nat}
    {z : Fin (m + 1) -> ℂ} (hz : z ∈ F.zeroFreeRegion (m + 1)) :
    F.threshold m (nestedInit z) < ‖nestedLast z‖ :=
  hz.2.1

/-- Membership in the strengthened region gives zero-freeness of the corresponding
leading coefficient. -/
theorem lead_ne_of_mem_zeroFreeRegion (F : NestedTailFamily) {m : Nat}
    {x : Fin m -> ℂ} (hx : x ∈ F.zeroFreeRegion m) :
    (F.step m).lead x ≠ 0 := by
  cases m with
  | zero =>
      exact hx
  | succ m =>
      exact hx.2.2

/-- The strengthened zero-free nested region is contained in the original recursive
threshold region. -/
theorem zeroFreeRegion_subset_region (F : NestedTailFamily) :
    ∀ m : Nat, F.zeroFreeRegion m ⊆ F.region m := by
  intro m
  induction m with
  | zero =>
      intro z hz
      simp [region]
  | succ m ih =>
      intro z hz
      exact ⟨ih hz.1, hz.2.1⟩

/-- Threshold continuity on the zero-free regions from continuous step coefficients. -/
theorem continuousOn_thresholds_zeroFreeRegion (F : NestedTailFamily)
    (hlead_cont : ∀ m : Nat, Continuous (F.step m).lead)
    (hlower_cont :
      ∀ m : Nat, ∀ i : Fin (F.step m).degree,
        Continuous ((F.step m).lower i)) :
    ∀ m : Nat, ContinuousOn (F.threshold m) (F.zeroFreeRegion m) := by
  intro m
  simpa [threshold] using
    (F.step m).continuousOn_threshold
      (hlead_cont m).continuousOn
      (by
        intro i
        exact (hlower_cont m i).continuousOn)
      (by
        intro x hx
        exact F.lead_ne_of_mem_zeroFreeRegion hx)

/-- Nonvanishing of the `m`th one-step evaluator on the strengthened region. -/
theorem zeroFreeRegion_evalStep_ne_zero_of_mem_succ (F : NestedTailFamily) {m : Nat}
    {z : Fin (m + 1) -> ℂ}
    (hz : z ∈ F.zeroFreeRegion (m + 1)) :
    F.evalStep z ≠ 0 := by
  exact (F.step m).eval_ne_zero_of_threshold
    (F.lead_ne_of_mem_zeroFreeRegion (F.nestedInit_mem_of_mem_zeroFreeRegion hz))
    (by
      simpa [threshold] using F.nestedLast_large_of_mem_zeroFreeRegion hz)

/-- Openness of the strengthened zero-free regions from continuous leading and lower
coefficient functions in every one-step presentation. -/
theorem isOpen_zeroFreeRegion_of_continuous_steps (F : NestedTailFamily)
    (hlead_cont : ∀ m : Nat, Continuous (F.step m).lead)
    (hlower_cont :
      ∀ m : Nat, ∀ i : Fin (F.step m).degree,
        Continuous ((F.step m).lower i)) :
    ∀ m : Nat, IsOpen (F.zeroFreeRegion m) := by
  intro m
  induction m with
  | zero =>
      have hnonzero :
          IsOpen ((F.step 0).lead ⁻¹' ({0} : Set ℂ)ᶜ) :=
        (hlead_cont 0).isOpen_preimage _
          ((isClosed_singleton : IsClosed ({0} : Set ℂ)).isOpen_compl)
      exact hnonzero
  | succ m ih =>
      let baseSet : Set (Fin (m + 1) -> ℂ) := nestedInit ⁻¹' F.zeroFreeRegion m
      have hbaseOpen : IsOpen baseSet :=
        ih.preimage (continuous_nestedInit (m := m))
      have hthreshold_comp :
          ContinuousOn
            (fun z : Fin (m + 1) -> ℂ => F.threshold m (nestedInit z)) baseSet := by
        simpa [baseSet, Function.comp_def] using
          (F.continuousOn_thresholds_zeroFreeRegion hlead_cont hlower_cont m).comp
            (continuous_nestedInit (m := m)).continuousOn
            (by intro z hz; exact hz)
      have hlast :
          ContinuousOn (fun z : Fin (m + 1) -> ℂ => ‖nestedLast z‖) baseSet :=
        ((continuous_nestedLast (m := m)).norm).continuousOn
      have hpair :
          ContinuousOn
            (fun z : Fin (m + 1) -> ℂ => (F.threshold m (nestedInit z), ‖nestedLast z‖))
            baseSet :=
        hthreshold_comp.prodMk hlast
      have hlt : IsOpen {p : ℝ × ℝ | p.1 < p.2} :=
        isOpen_lt continuous_fst continuous_snd
      have hlargeOpen :
          IsOpen
            (baseSet ∩
              (fun z : Fin (m + 1) -> ℂ =>
                (F.threshold m (nestedInit z), ‖nestedLast z‖)) ⁻¹'
                {p : ℝ × ℝ | p.1 < p.2}) :=
        hpair.isOpen_inter_preimage hbaseOpen hlt
      have hleadOpen :
          IsOpen
            ((F.step (m + 1)).lead ⁻¹' ({0} : Set ℂ)ᶜ) :=
        (hlead_cont (m + 1)).isOpen_preimage _
          ((isClosed_singleton : IsClosed ({0} : Set ℂ)).isOpen_compl)
      have hopen :
          IsOpen
            ((baseSet ∩
              (fun z : Fin (m + 1) -> ℂ =>
                (F.threshold m (nestedInit z), ‖nestedLast z‖)) ⁻¹'
                {p : ℝ × ℝ | p.1 < p.2}) ∩
              (F.step (m + 1)).lead ⁻¹' ({0} : Set ℂ)ᶜ) :=
        hlargeOpen.inter hleadOpen
      have hset :
          F.zeroFreeRegion (m + 1) =
            ((baseSet ∩
              (fun z : Fin (m + 1) -> ℂ =>
                (F.threshold m (nestedInit z), ‖nestedLast z‖)) ⁻¹'
                {p : ℝ × ℝ | p.1 < p.2}) ∩
              (F.step (m + 1)).lead ⁻¹' ({0} : Set ℂ)ᶜ) := by
        ext z
        simp [zeroFreeRegion, baseSet, Set.preimage, and_assoc]
      rw [hset]
      exact hopen

/-- The evaluator-form nested-largeness theorem: on `N_{m+1}`, the `m`th tail
presentation is nonzero, provided its leading coefficient is nonzero on `N_m`. -/
theorem evalStep_ne_zero_of_mem_region (F : NestedTailFamily) {m : Nat}
    {z : Fin (m + 1) -> ℂ}
    (hlead : ∀ x ∈ F.region m, (F.step m).lead x ≠ 0)
    (hz : z ∈ F.region (m + 1)) :
    F.evalStep z ≠ 0 := by
  exact (F.step m).eval_ne_zero_of_threshold
    (hlead (nestedInit z) (F.nestedInit_mem_of_mem_region hz))
    (by
      simpa [threshold] using F.nestedLast_large_of_mem_region hz)

/-- Threshold continuity for every step, packaged from the one-step API. -/
theorem continuousOn_thresholds (F : NestedTailFamily)
    (hlead_cont : ∀ m : Nat, ContinuousOn (F.step m).lead (F.region m))
    (hlower_cont :
      ∀ m : Nat, ∀ i : Fin (F.step m).degree,
        ContinuousOn ((F.step m).lower i) (F.region m))
    (hlead_ne : ∀ m : Nat, ∀ x ∈ F.region m, (F.step m).lead x ≠ 0) :
    ∀ m : Nat, ContinuousOn (F.threshold m) (F.region m) := by
  intro m
  simpa [threshold] using
    (F.step m).continuousOn_threshold
      (hlead_cont m) (hlower_cont m) (hlead_ne m)

/-- Openness of all nested regions from continuity of the threshold tower. -/
theorem isOpen_region (F : NestedTailFamily)
    (hthreshold : ∀ m : Nat, ContinuousOn (F.threshold m) (F.region m)) :
    ∀ m : Nat, IsOpen (F.region m) := by
  simpa [region] using isOpen_nestedRegion F.threshold hthreshold

/-- Openness of all nested regions from continuous, zero-free leading coefficients and
continuous lower coefficients in every one-step presentation. -/
theorem isOpen_region_of_continuous_steps (F : NestedTailFamily)
    (hlead_cont : ∀ m : Nat, ContinuousOn (F.step m).lead (F.region m))
    (hlower_cont :
      ∀ m : Nat, ∀ i : Fin (F.step m).degree,
        ContinuousOn ((F.step m).lower i) (F.region m))
    (hlead_ne : ∀ m : Nat, ∀ x ∈ F.region m, (F.step m).lead x ≠ 0) :
    ∀ m : Nat, IsOpen (F.region m) :=
  F.isOpen_region (F.continuousOn_thresholds hlead_cont hlower_cont hlead_ne)

end NestedTailFamily

/-! ## Polynomial-backed nested evaluator families -/

/-- A tower of polynomial tail presentations with the coefficient continuity needed to
feed the abstract `NestedTailFamily` API.

The `tailData` field keeps the polynomial evaluation theorem for each layer, while the
continuity fields let the generic nested-region openness theorem be applied without
unfolding a downstream polynomial-family construction. -/
structure PolynomialNestedTailData where
  tailData : (m : Nat) -> PolynomialTailPresentationData m
  lead_continuous : ∀ m : Nat, Continuous (tailData m).presentation.lead
  lower_continuous :
    ∀ m : Nat, ∀ i : Fin (tailData m).presentation.degree,
      Continuous ((tailData m).presentation.lower i)

namespace PolynomialNestedTailData

/-- Forget the polynomial evaluation witnesses and view the data as an evaluator-form
nested tail family. -/
def toNestedTailFamily (D : PolynomialNestedTailData) : NestedTailFamily where
  step m := (D.tailData m).presentation

@[simp] theorem toNestedTailFamily_step (D : PolynomialNestedTailData) (m : Nat) :
    D.toNestedTailFamily.step m = (D.tailData m).presentation :=
  rfl

/-- The threshold tower of a polynomial-backed nested tail family. -/
noncomputable def threshold (D : PolynomialNestedTailData)
    (m : Nat) (x : Fin m -> ℂ) : ℝ :=
  D.toNestedTailFamily.threshold m x

/-- The recursive nested regions of a polynomial-backed nested tail family. -/
noncomputable def region (D : PolynomialNestedTailData) (m : Nat) : Set (Fin m -> ℂ) :=
  D.toNestedTailFamily.region m

/-- The strengthened zero-free nested regions of a polynomial-backed nested tail family. -/
noncomputable def zeroFreeRegion (D : PolynomialNestedTailData)
    (m : Nat) : Set (Fin m -> ℂ) :=
  D.toNestedTailFamily.zeroFreeRegion m

/-- Evaluate the `m`th polynomial-backed tail presentation on a length-`m+1` vector. -/
noncomputable def evalStep (D : PolynomialNestedTailData) {m : Nat}
    (z : Fin (m + 1) -> ℂ) : ℂ :=
  D.toNestedTailFamily.evalStep z

@[simp] theorem threshold_eq (D : PolynomialNestedTailData)
    (m : Nat) (x : Fin m -> ℂ) :
    D.threshold m x = (D.tailData m).presentation.threshold x :=
  rfl

@[simp] theorem evalStep_eq_toNestedTailFamily_evalStep
    (D : PolynomialNestedTailData) {m : Nat} (z : Fin (m + 1) -> ℂ) :
    D.evalStep z = D.toNestedTailFamily.evalStep z :=
  rfl

/-- The nested-step evaluator for compiled polynomial data is polynomial evaluation. -/
theorem toNestedTailFamily_evalStep_eq_eval
    (D : PolynomialNestedTailData) {m : Nat} (z : Fin (m + 1) -> ℂ) :
    D.toNestedTailFamily.evalStep z = MvPolynomial.eval z (D.tailData m).poly := by
  simpa [toNestedTailFamily, NestedTailFamily.evalStep] using
    (D.tailData m).eval_nested z

/-- The wrapper evaluator for compiled polynomial data is polynomial evaluation. -/
theorem evalStep_eq_eval
    (D : PolynomialNestedTailData) {m : Nat} (z : Fin (m + 1) -> ℂ) :
    D.evalStep z = MvPolynomial.eval z (D.tailData m).poly := by
  simpa [evalStep] using D.toNestedTailFamily_evalStep_eq_eval z

@[simp] theorem mem_zeroFreeRegion_zero (D : PolynomialNestedTailData)
    (z : Fin 0 -> ℂ) :
    z ∈ D.zeroFreeRegion 0 ↔ (D.tailData 0).presentation.lead z ≠ 0 := by
  rfl

@[simp] theorem mem_zeroFreeRegion_succ (D : PolynomialNestedTailData) {m : Nat}
    {z : Fin (m + 1) -> ℂ} :
    z ∈ D.zeroFreeRegion (m + 1) ↔
      nestedInit z ∈ D.zeroFreeRegion m ∧
        D.threshold m (nestedInit z) < ‖nestedLast z‖ ∧
        (D.tailData (m + 1)).presentation.lead z ≠ 0 := by
  rfl

/-- Prefix membership for a polynomial-backed zero-free nested region. -/
theorem nestedInit_mem_of_mem_zeroFreeRegion (D : PolynomialNestedTailData) {m : Nat}
    {z : Fin (m + 1) -> ℂ} (hz : z ∈ D.zeroFreeRegion (m + 1)) :
    nestedInit z ∈ D.zeroFreeRegion m :=
  D.toNestedTailFamily.nestedInit_mem_of_mem_zeroFreeRegion hz

/-- The last-coordinate threshold inequality for a polynomial-backed zero-free region. -/
theorem nestedLast_large_of_mem_zeroFreeRegion (D : PolynomialNestedTailData) {m : Nat}
    {z : Fin (m + 1) -> ℂ} (hz : z ∈ D.zeroFreeRegion (m + 1)) :
    D.threshold m (nestedInit z) < ‖nestedLast z‖ :=
  D.toNestedTailFamily.nestedLast_large_of_mem_zeroFreeRegion hz

/-- Membership in the polynomial-backed strengthened region gives zero-freeness of the
corresponding leading coefficient. -/
theorem lead_ne_of_mem_zeroFreeRegion (D : PolynomialNestedTailData) {m : Nat}
    {x : Fin m -> ℂ} (hx : x ∈ D.zeroFreeRegion m) :
    (D.tailData m).presentation.lead x ≠ 0 :=
  D.toNestedTailFamily.lead_ne_of_mem_zeroFreeRegion hx

/-- Polynomial-backed zero-free regions are contained in the original nested regions. -/
theorem zeroFreeRegion_subset_region (D : PolynomialNestedTailData) :
    ∀ m : Nat, D.zeroFreeRegion m ⊆ D.region m :=
  D.toNestedTailFamily.zeroFreeRegion_subset_region

/-- Threshold continuity on polynomial-backed zero-free regions. -/
theorem continuousOn_thresholds_zeroFreeRegion (D : PolynomialNestedTailData) :
    ∀ m : Nat, ContinuousOn (D.threshold m) (D.zeroFreeRegion m) :=
  D.toNestedTailFamily.continuousOn_thresholds_zeroFreeRegion
    (by
      intro m
      exact D.lead_continuous m)
    (by
      intro m i
      exact D.lower_continuous m i)

/-- Nonvanishing of the polynomial-backed one-step evaluator on the strengthened region. -/
theorem zeroFreeRegion_evalStep_ne_zero_of_mem_succ
    (D : PolynomialNestedTailData) {m : Nat} {z : Fin (m + 1) -> ℂ}
    (hz : z ∈ D.zeroFreeRegion (m + 1)) :
    D.evalStep z ≠ 0 := by
  simpa [evalStep, zeroFreeRegion] using
    D.toNestedTailFamily.zeroFreeRegion_evalStep_ne_zero_of_mem_succ hz

/-- Polynomial evaluation is nonzero on the strengthened region. -/
theorem zeroFreeRegion_eval_ne_zero_of_mem_succ
    (D : PolynomialNestedTailData) {m : Nat} {z : Fin (m + 1) -> ℂ}
    (hz : z ∈ D.zeroFreeRegion (m + 1)) :
    MvPolynomial.eval z (D.tailData m).poly ≠ 0 := by
  rw [← D.evalStep_eq_eval z]
  exact D.zeroFreeRegion_evalStep_ne_zero_of_mem_succ hz

/-- Openness of all polynomial-backed zero-free nested regions. -/
theorem isOpen_zeroFreeRegion (D : PolynomialNestedTailData) :
    ∀ m : Nat, IsOpen (D.zeroFreeRegion m) :=
  D.toNestedTailFamily.isOpen_zeroFreeRegion_of_continuous_steps
    (by
      intro m
      exact D.lead_continuous m)
    (by
      intro m i
      exact D.lower_continuous m i)

/-- Threshold continuity for a polynomial-backed nested tail family, assuming the leading
coefficient is nonzero on each already-constructed nested region. -/
theorem continuousOn_thresholds_of_lead_ne (D : PolynomialNestedTailData)
    (hlead_ne :
      ∀ m : Nat, ∀ x ∈ D.region m, (D.tailData m).presentation.lead x ≠ 0) :
    ∀ m : Nat, ContinuousOn (D.threshold m) (D.region m) := by
  exact D.toNestedTailFamily.continuousOn_thresholds
    (by
      intro m
      exact (D.lead_continuous m).continuousOn)
    (by
      intro m i
      exact (D.lower_continuous m i).continuousOn)
    (by
      intro m x hx
      exact hlead_ne m x hx)

/-- Openness of polynomial-backed nested regions from leading-coefficient nonvanishing on
those regions. -/
theorem isOpen_region_of_lead_ne (D : PolynomialNestedTailData)
    (hlead_ne :
      ∀ m : Nat, ∀ x ∈ D.region m, (D.tailData m).presentation.lead x ≠ 0) :
    ∀ m : Nat, IsOpen (D.region m) :=
  D.toNestedTailFamily.isOpen_region_of_continuous_steps
    (by
      intro m
      exact (D.lead_continuous m).continuousOn)
    (by
      intro m i
      exact (D.lower_continuous m i).continuousOn)
    (by
      intro m x hx
      exact hlead_ne m x hx)

/-- Canonical polynomial-backed nested data from a tower of polynomials, using the
generic last-variable extraction at every layer. -/
noncomputable def ofPolynomials
    (p : (m : Nat) -> MvPolynomial (Fin (m + 1)) ℂ) : PolynomialNestedTailData where
  tailData m := PolynomialTailPresentationData.ofPolynomial (p m)
  lead_continuous := by
    intro m
    simpa [PolynomialTailPresentationData.ofPolynomial] using
      continuous_polynomialTailPresentation_lead (p m)
  lower_continuous := by
    intro m i
    simpa [PolynomialTailPresentationData.ofPolynomial] using
      continuous_polynomialTailPresentation_lower (p m) i

@[simp] theorem ofPolynomials_tailData
    (p : (m : Nat) -> MvPolynomial (Fin (m + 1)) ℂ) (m : Nat) :
    (ofPolynomials p).tailData m = PolynomialTailPresentationData.ofPolynomial (p m) :=
  rfl

@[simp] theorem ofPolynomials_toNestedTailFamily_step
    (p : (m : Nat) -> MvPolynomial (Fin (m + 1)) ℂ) (m : Nat) :
    (ofPolynomials p).toNestedTailFamily.step m = polynomialTailPresentation (p m) :=
  rfl

/-- The nested-step evaluator for the canonical polynomial tower is polynomial
evaluation. -/
theorem ofPolynomials_evalStep_eq_eval
    (p : (m : Nat) -> MvPolynomial (Fin (m + 1)) ℂ)
    {m : Nat} (z : Fin (m + 1) -> ℂ) :
    (ofPolynomials p).evalStep z = MvPolynomial.eval z (p m) := by
  simpa using (ofPolynomials p).evalStep_eq_eval z

end PolynomialNestedTailData

/-! ## Global-product iterated leading-coefficient tower (`lem:nested`, Steps 1-2)

Given a single polynomial `P` with a dominant top coefficient (in practice the global
product `P = f_2 * ... * f_L * g`), `lem:nested` builds the nested largeness regions from
the *iterated leading coefficients* `P_K := P`, `P_k := lc_{z_{k+1}}(P_{k+1})`.  The
crucial fact (TeX Step 2) is that, on the recursive region `N_k`, the iterated leading
coefficient `P_k` is nonvanishing.

Here we build the nested tail tower whose level-`m` polynomial is exactly `P_{m+1}`
(`globalLcTower`), so that the leading coefficient of step `m` is `P_m = `(step `(m-1)`'s
polynomial).  The `leadingCoeff_ne_on_region` statement is then the literal TeX Step-2
induction, provable from `HasDominantTopCoeff P` alone (no genericity strengthening). -/

/-- The last-variable leading coefficient `lc_{z_{m+1}}(p) ∈ ℂ[z_1,…,z_m]`, viewing
`p ∈ ℂ[z_1,…,z_{m+1}]` as a one-variable polynomial in its last coordinate. -/
noncomputable def lcLast {m : Nat} (p : MvPolynomial (Fin (m + 1)) ℂ) :
    MvPolynomial (Fin m) ℂ :=
  (lastVariablePolynomial p).leadingCoeff

/-- `lc_{z_{m+1}}(1) = 1`. -/
@[simp] theorem lcLast_one {m : Nat} :
    lcLast (1 : MvPolynomial (Fin (m + 1)) ℂ) = 1 := by
  unfold lcLast lastVariablePolynomial
  rw [map_one, map_one, Polynomial.leadingCoeff_one]

/-- Viewing a product in the last variable is the product of the one-variable views: the
last-variable decomposition is a ring homomorphism. -/
theorem lastVariablePolynomial_mul {m : Nat}
    (a b : MvPolynomial (Fin (m + 1)) ℂ) :
    lastVariablePolynomial (a * b) =
      lastVariablePolynomial a * lastVariablePolynomial b := by
  unfold lastVariablePolynomial
  simp only [map_mul]

/-- **`lem:nested`, Step 1 (multiplicativity).** Iterated leading coefficients are
multiplicative over the integral domain `ℂ[z_1,…,z_m]`:
`lc_{z_{m+1}}(a·b) = lc_{z_{m+1}}(a)·lc_{z_{m+1}}(b)`. -/
theorem lcLast_mul {m : Nat} (a b : MvPolynomial (Fin (m + 1)) ℂ) :
    lcLast (a * b) = lcLast a * lcLast b := by
  unfold lcLast
  rw [lastVariablePolynomial_mul, Polynomial.leadingCoeff_mul]

/-- **`lem:nested`, Step 1.** The iterated leading coefficient of a polynomial with a
dominant top coefficient again has a dominant top coefficient (here for the last
variable). -/
theorem hasDominantTopCoeff_lcLast {m : Nat} {p : MvPolynomial (Fin (m + 1)) ℂ}
    (hp : HasDominantTopCoeff p) : HasDominantTopCoeff (lcLast p) := by
  unfold lcLast lastVariablePolynomial
  exact (hp.rename_of_injective
    (Equiv.injective (nestedLastToFrontEquiv m))).leadingCoeff_finSuccEquiv

/-- The degree of the last-variable view of `p` is exactly the per-variable degree of `p`
in its last coordinate. -/
theorem natDegree_lastVariablePolynomial {m : Nat} (p : MvPolynomial (Fin (m + 1)) ℂ) :
    (lastVariablePolynomial p).natDegree = p.degreeOf (Fin.last m) := by
  unfold lastVariablePolynomial
  rw [MvPolynomial.natDegree_finSuccEquiv,
    show (0 : Fin (m + 1)) = nestedLastToFrontEquiv m (Fin.last m) from
      (nestedLastToFrontEquiv_last m).symm,
    MvPolynomial.degreeOf_rename_of_injective (Equiv.injective _)]

/-- **`lem:nested`, Step 1 (boundary case).** If `p` does not involve its last variable,
its last-variable leading coefficient `lc_{z_{m+1}}(p)` is just `p` with that variable
dropped: evaluation of `p` only sees the first `m` coordinates. -/
theorem eval_eq_eval_lcLast_of_degreeOf_last_zero {m : Nat}
    {p : MvPolynomial (Fin (m + 1)) ℂ} (hp : p.degreeOf (Fin.last m) = 0)
    (z : Fin (m + 1) → ℂ) :
    MvPolynomial.eval z p = MvPolynomial.eval (nestedInit z) (lcLast p) := by
  have hdeg : (polynomialTailPresentation p).degree = 0 := by
    change (lastVariablePolynomial p).natDegree = 0
    rw [natDegree_lastVariablePolynomial, hp]
  rw [← polynomialTailPresentation_eval_nested p,
    TailPresentation.eval_eq_lead_of_degree_eq_zero _ hdeg]
  rfl

/-- A nonzero polynomial in zero variables never evaluates to zero. -/
theorem eval_ne_zero_fin_zero_of_ne_zero {q : MvPolynomial (Fin 0) ℂ}
    (hq : q ≠ 0) (x : Fin 0 → ℂ) :
    MvPolynomial.eval x q ≠ 0 := by
  have hx : x = Fin.elim0 := by
    funext i; exact Fin.elim0 i
  subst hx
  intro h
  apply hq
  apply (MvPolynomial.isEmptyAlgEquiv ℂ (Fin 0)).injective
  simpa [MvPolynomial.isEmptyAlgEquiv_apply] using h

/-- The global-product iterated leading-coefficient tower of a top polynomial
`P ∈ ℂ[z_1,…,z_{n+1}]`: at index `m`, the polynomial in `m+1` variables given by the
iterated leading coefficient `P_{m+1}` (peeling the top `n - m` variables of `P`).  At the
top index `n` it is `P` itself, and above the top it is the constant `1` (chosen so the
tower is total and `lc`-stable there). -/
noncomputable def globalLcTower :
    (n : Nat) → MvPolynomial (Fin (n + 1)) ℂ → (m : Nat) → MvPolynomial (Fin (m + 1)) ℂ
  | 0,     P => fun m => match m with | 0 => P | _ + 1 => 1
  | n + 1, P => fun m =>
      if h : m = n + 1 then h ▸ P
      else globalLcTower n (lcLast P) m

@[simp] theorem globalLcTower_zero_zero (P : MvPolynomial (Fin 1) ℂ) :
    globalLcTower 0 P 0 = P := rfl

@[simp] theorem globalLcTower_zero_succ (P : MvPolynomial (Fin 1) ℂ) (k : Nat) :
    globalLcTower 0 P (k + 1) = 1 := rfl

/-- The tower's value at the top index is the input polynomial. -/
theorem globalLcTower_succ_self (n : Nat) (P : MvPolynomial (Fin (n + 1 + 1)) ℂ) :
    globalLcTower (n + 1) P (n + 1) = P := by
  change (if h : n + 1 = n + 1 then h ▸ P else globalLcTower n (lcLast P) (n + 1)) = P
  rw [dif_pos rfl]

/-- Below/away from the top index, the `(n+1)`-tower agrees with the `n`-tower of the
peeled polynomial. -/
theorem globalLcTower_succ_of_ne (n : Nat) (P : MvPolynomial (Fin (n + 1 + 1)) ℂ)
    {m : Nat} (hm : m ≠ n + 1) :
    globalLcTower (n + 1) P m = globalLcTower n (lcLast P) m := by
  change (if h : m = n + 1 then h ▸ P else globalLcTower n (lcLast P) m) = _
  rw [dif_neg hm]

/-- The tower's value at its own top index is the input polynomial. -/
theorem globalLcTower_self :
    ∀ (n : Nat) (P : MvPolynomial (Fin (n + 1)) ℂ), globalLcTower n P n = P
  | 0, _ => rfl
  | n + 1, P => globalLcTower_succ_self n P

/-- Strictly above the top index the tower is the constant `1`. -/
theorem globalLcTower_of_gt :
    ∀ (n : Nat) (P : MvPolynomial (Fin (n + 1)) ℂ) (m : Nat), n < m →
      globalLcTower n P m = 1
  | 0, _, m, hm => by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hm
      simp
  | n + 1, P, m, hm => by
      have hmne : m ≠ n + 1 := Nat.ne_of_gt hm
      rw [globalLcTower_succ_of_ne n P hmne]
      exact globalLcTower_of_gt n (lcLast P) m (Nat.lt_of_succ_lt hm)

/-- **`lem:nested`, Step 0+1.** Every level of the global-product tower has a dominant top
coefficient. -/
theorem hasDominantTopCoeff_globalLcTower :
    ∀ (n : Nat) {P : MvPolynomial (Fin (n + 1)) ℂ}, HasDominantTopCoeff P →
      ∀ m : Nat, HasDominantTopCoeff (globalLcTower n P m)
  | 0, P, hP, m => by
      cases m with
      | zero => simpa using hP
      | succ k => simpa using hasDominantTopCoeff_one
  | n + 1, P, hP, m => by
      by_cases hm : m = n + 1
      · subst hm
        rw [globalLcTower_succ_self]
        exact hP
      · rw [globalLcTower_succ_of_ne n P hm]
        exact hasDominantTopCoeff_globalLcTower n (hasDominantTopCoeff_lcLast hP) m

/-- **`lem:nested`, Step 1 recursion.** Away from the top boundary, the leading
coefficient of level `m+1` is exactly level `m`: `P_m = lc_{z_{m+1}}(P_{m+1})`. -/
theorem lcLast_globalLcTower :
    ∀ (n : Nat) (P : MvPolynomial (Fin (n + 1)) ℂ) {m : Nat}, m ≠ n →
      lcLast (globalLcTower n P (m + 1)) = globalLcTower n P m
  | 0, P, m, hm => by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
      simp
  | n + 1, P, m, hm => by
      by_cases hmn : m = n
      · rw [hmn, globalLcTower_self,
          globalLcTower_succ_of_ne n P (by omega : n ≠ n + 1),
          globalLcTower_self]
      · rw [globalLcTower_succ_of_ne n P (by omega : m + 1 ≠ n + 1),
          globalLcTower_succ_of_ne n P (by omega : m ≠ n + 1)]
        exact lcLast_globalLcTower n (lcLast P) hmn

/-- The iterated-lc tower of the constant `1` is identically `1`. -/
theorem globalLcTower_one :
    ∀ (n m : Nat), globalLcTower n (1 : MvPolynomial (Fin (n + 1)) ℂ) m = 1
  | 0, m => by cases m <;> rfl
  | n + 1, m => by
      by_cases hm : m = n + 1
      · rw [hm, globalLcTower_self]
      · rw [globalLcTower_succ_of_ne n 1 hm, lcLast_one]
        exact globalLcTower_one n m

/-- **`lem:nested`, Step 1 (multiplicativity), iterated.** The iterated-lc tower of a
product is the product of the iterated-lc towers: `(a·b)_{m+1} = a_{m+1}·b_{m+1}`. -/
theorem globalLcTower_mul :
    ∀ (n : Nat) (a b : MvPolynomial (Fin (n + 1)) ℂ) (m : Nat),
      globalLcTower n (a * b) m = globalLcTower n a m * globalLcTower n b m
  | 0, a, b, m => by cases m with
      | zero => rfl
      | succ k => simp
  | n + 1, a, b, m => by
      by_cases hm : m = n + 1
      · rw [hm, globalLcTower_self, globalLcTower_self, globalLcTower_self]
      · rw [globalLcTower_succ_of_ne n (a * b) hm, lcLast_mul,
          globalLcTower_succ_of_ne n a hm, globalLcTower_succ_of_ne n b hm]
        exact globalLcTower_mul n (lcLast a) (lcLast b) m

/-- **`lem:nested`, Step 1 (multiplicativity), finite product.** For a finite family,
`(∏_a p_a)_{m+1} = ∏_a (p_a)_{m+1}`: each family member appears as an explicit factor of
the iterated leading coefficient of the global product. -/
theorem globalLcTower_prod {ι : Type*} (n : Nat) (s : Finset ι)
    (p : ι → MvPolynomial (Fin (n + 1)) ℂ) (m : Nat) :
    globalLcTower n (∏ a ∈ s, p a) m = ∏ a ∈ s, globalLcTower n (p a) m := by
  classical
  induction s using Finset.induction with
  | empty => simp [globalLcTower_one]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, globalLcTower_mul, ih, Finset.prod_insert ha]

/-- The polynomial-backed nested tail tower of the global product `P`, with level-`m`
polynomial the iterated leading coefficient `P_{m+1}`. -/
noncomputable def globalLcNestedTailData (n : Nat) (P : MvPolynomial (Fin (n + 1)) ℂ) :
    PolynomialNestedTailData :=
  PolynomialNestedTailData.ofPolynomials (fun m => globalLcTower n P m)

@[simp] theorem globalLcNestedTailData_tailData (n : Nat)
    (P : MvPolynomial (Fin (n + 1)) ℂ) (m : Nat) :
    (globalLcNestedTailData n P).tailData m =
      PolynomialTailPresentationData.ofPolynomial (globalLcTower n P m) :=
  rfl

/-- The level-`m` leading coefficient evaluator of the global-product tower is evaluation
of `P_m = lc_{z_{m+1}}(P_{m+1})`. -/
theorem globalLcNestedTailData_lead (n : Nat) (P : MvPolynomial (Fin (n + 1)) ℂ)
    {m : Nat} (x : Fin m → ℂ) :
    ((globalLcNestedTailData n P).tailData m).presentation.lead x =
      MvPolynomial.eval x (lcLast (globalLcTower n P m)) :=
  rfl

/-- The level-`m` step evaluator of the global-product tower is evaluation of `P_{m+1}`. -/
theorem globalLcNestedTailData_evalStep (n : Nat) (P : MvPolynomial (Fin (n + 1)) ℂ)
    {m : Nat} (z : Fin (m + 1) → ℂ) :
    (globalLcNestedTailData n P).evalStep z =
      MvPolynomial.eval z (globalLcTower n P m) := by
  simpa [globalLcNestedTailData] using
    PolynomialNestedTailData.ofPolynomials_evalStep_eq_eval
      (fun m => globalLcTower n P m) z

/-- **`lem:nested`, Step 2 (the inner induction).**  Given only `HasDominantTopCoeff P`,
the level-`m` leading coefficient `P_m` of the global-product iterated-lc tower is
nonvanishing on the recursive region `N_m`.  This is the `leadingCoeff_ne_on_region`
field — proved here as a theorem rather than assumed.

The induction mirrors TeX exactly: at level `0`, `P_0` is a nonzero constant (a dominant
top coefficient in zero variables); at level `m+1`, `P_{m+1} = `(level-`m` polynomial) is
nonvanishing on `N_{m+1}` by the one-step threshold estimate, using the inductive
hypothesis that `P_m` is nonvanishing on `N_m`.  Above the top index everything is the
constant `1`. -/
theorem globalLcTower_leadingCoeff_ne_on_region (n : Nat)
    {P : MvPolynomial (Fin (n + 1)) ℂ} (hP : HasDominantTopCoeff P) :
    ∀ m : Nat, ∀ x ∈ (globalLcNestedTailData n P).region m,
      ((globalLcNestedTailData n P).tailData m).presentation.lead x ≠ 0 := by
  intro m
  induction m with
  | zero =>
      intro x _hx
      rw [globalLcNestedTailData_lead]
      exact eval_ne_zero_fin_zero_of_ne_zero
        (hasDominantTopCoeff_lcLast (hasDominantTopCoeff_globalLcTower n hP 0)).ne_zero x
  | succ m ih =>
      intro x hx
      rw [globalLcNestedTailData_lead]
      rcases lt_or_ge m n with hmn | hmn
      · -- below the top boundary: reduce to nonvanishing of the step evaluator on `N_{m+1}`
        rw [lcLast_globalLcTower n P (Nat.ne_of_lt hmn)]
        rw [← globalLcNestedTailData_evalStep]
        exact (globalLcNestedTailData n P).toNestedTailFamily.evalStep_ne_zero_of_mem_region
          (fun y hy => ih y hy) hx
      · -- at/above the top boundary the level-`(m+1)` polynomial is `1`
        rw [globalLcTower_of_gt n P (m + 1) (Nat.lt_succ_of_le hmn), lcLast_one, map_one]
        exact one_ne_zero

/-- The level-`m` polynomial `P_{m+1}` of the global-product tower is nonvanishing on the
recursive region `N_{m+1}` (one step up from where its leading coefficient is controlled).
This is the one-step output of `lem:nested` Step 2, in the form consumed downstream. -/
theorem globalLcTower_eval_ne_on_region (n : Nat)
    {P : MvPolynomial (Fin (n + 1)) ℂ} (hP : HasDominantTopCoeff P) {m : Nat}
    {z : Fin (m + 1) → ℂ}
    (hz : z ∈ (globalLcNestedTailData n P).region (m + 1)) :
    MvPolynomial.eval z (globalLcTower n P m) ≠ 0 := by
  rw [← globalLcNestedTailData_evalStep]
  exact (globalLcNestedTailData n P).toNestedTailFamily.evalStep_ne_zero_of_mem_region
    (fun y hy => globalLcTower_leadingCoeff_ne_on_region n hP m y hy) hz

/-- **`lem:nested`, Conclusion.**  When the global product `P = ∏_a p_a` is built from a
finite family, each family member's iterated leading coefficient `(p_a)_{m+1}` is
nonvanishing on `N_{m+1}`.  The proof factors the nonvanishing iterated leading
coefficient of the product (TeX: "each factor is nonzero wherever `P_k ≠ 0`").

For a family member `p_a` that only involves `z_1,…,z_{m+1}`, `(p_a)_{m+1} = p_a`, so this
gives `p_a ≠ 0` on `N_{m+1}` — the conclusion used to obtain `f_{k+2} ≠ 0` on `N_k` and
`g ≠ 0` on `N_{L-1}`. -/
theorem globalLcTower_factor_eval_ne_on_region {ι : Type*} (n : Nat) (s : Finset ι)
    (p : ι → MvPolynomial (Fin (n + 1)) ℂ)
    (hP : HasDominantTopCoeff (∏ a ∈ s, p a)) {m : Nat} {z : Fin (m + 1) → ℂ}
    (hz : z ∈ (globalLcNestedTailData n (∏ a ∈ s, p a)).region (m + 1))
    {a : ι} (ha : a ∈ s) :
    MvPolynomial.eval z (globalLcTower n (p a) m) ≠ 0 := by
  have hne := globalLcTower_eval_ne_on_region n hP hz
  rw [globalLcTower_prod, map_prod] at hne
  exact fun h => hne (Finset.prod_eq_zero ha h)

end TransformerIdentifiability.NLayer
