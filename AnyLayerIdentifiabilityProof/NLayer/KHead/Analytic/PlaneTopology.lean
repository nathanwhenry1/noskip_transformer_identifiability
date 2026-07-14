import AnyLayerIdentifiabilityProof.NLayer.KHead.Core
import AnyLayerIdentifiabilityProof.NLayer.Analytic.AnalyticToolkit

set_option autoImplicit false

open Filter
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.KHead

/-!
# Plane topology for the k-head analytic packets

This file ports the plane-topology packet for the k-head proof.  Most of the hard
point-set arguments are already available in the single-head analytic toolkit; this file
exposes the k-head-facing API and proves the small bridges needed by later packets.
-/

/-! ## Accumulation and closed-discrete sets -/

/-- TeX notation `acc(A)`: accumulation points of `A`. -/
abbrev acc (A : Set ℂ) : Set ℂ := TransformerIdentifiability.NLayer.acc A

/-- Iterated accumulation sets. -/
abbrev accIter : Nat -> Set ℂ -> Set ℂ :=
  TransformerIdentifiability.NLayer.accIter

/-- `A` has no accumulation point inside `U`. -/
abbrev NoAccumIn (A U : Set ℂ) : Prop :=
  TransformerIdentifiability.NLayer.NoAccumIn A U

/-- Union of the first `n` strata. -/
abbrev partialUnion (S : Nat -> Set ℂ) (n : Nat) : Set ℂ :=
  TransformerIdentifiability.NLayer.partialUnion S n

/-- The single-head stratification interface, re-exported for k-head packets. -/
abbrev StrataSystem (S : Nat -> Set ℂ) (m : Nat) : Prop :=
  TransformerIdentifiability.NLayer.StrataSystem S m

/-- Monotonicity of accumulation sets. -/
theorem acc_mono {A B : Set ℂ} (hAB : A ⊆ B) : acc A ⊆ acc B :=
  TransformerIdentifiability.NLayer.acc_mono hAB

/-- Monotonicity of iterated accumulation sets. -/
theorem accIter_mono {A B : Set ℂ} (hAB : A ⊆ B) :
    ∀ k : Nat, accIter k A ⊆ accIter k B :=
  TransformerIdentifiability.NLayer.accIter_mono hAB

/-- Accumulation commutes with binary finite unions. -/
theorem acc_union (A B : Set ℂ) :
    acc (A ∪ B) = acc A ∪ acc B := by
  exact derivedSet_union A B

/-- Closedness in terms of containing all accumulation points. -/
theorem isClosed_iff_acc_subset {A : Set ℂ} :
    IsClosed A ↔ acc A ⊆ A := by
  constructor
  · exact TransformerIdentifiability.NLayer.acc_subset_of_isClosed
  · intro hA
    rw [← closure_subset_iff_isClosed]
    intro z hz
    rw [TransformerIdentifiability.NLayer.closure_eq_self_union_acc] at hz
    rcases hz with hzA | hzAcc
    · exact hzA
    · exact hA (by simpa [acc] using hzAcc)

/-- A relative closed-discrete subset of an ambient plane set.  The `isClosed_rel`
field is the usual subspace closedness statement, written as `Uᶜ ∪ A` closed in `ℂ`;
the `noAccum` field is the form consumed by the descent/stratification code. -/
structure ClosedDiscreteIn (A U : Set ℂ) : Prop where
  subset : A ⊆ U
  isClosed_rel : IsClosed (Uᶜ ∪ A)
  noAccum : NoAccumIn A U

namespace ClosedDiscreteIn

/-- Closed-discrete sets have no accumulation points in their ambient set. -/
theorem noAccumIn {A U : Set ℂ} (h : ClosedDiscreteIn A U) :
    NoAccumIn A U :=
  h.noAccum

/-- Closed-discrete subsets of the complex plane are countable. -/
theorem countable {A U : Set ℂ} (h : ClosedDiscreteIn A U) :
    A.Countable :=
  TransformerIdentifiability.NLayer.countable_of_subset_noAccumIn h.subset h.noAccum

/-- Binary finite unions preserve relative closed-discreteness. -/
theorem union {A B U : Set ℂ} (hA : ClosedDiscreteIn A U) (hB : ClosedDiscreteIn B U) :
    ClosedDiscreteIn (A ∪ B) U where
  subset := by
    intro z hz
    rcases hz with hzA | hzB
    · exact hA.subset hzA
    · exact hB.subset hzB
  isClosed_rel := by
    have hclosed : IsClosed ((Uᶜ ∪ A) ∪ (Uᶜ ∪ B)) :=
      hA.isClosed_rel.union hB.isClosed_rel
    simpa [Set.union_assoc, Set.union_left_comm, Set.union_comm] using hclosed
  noAccum := by
    intro z hzU hz
    change z ∈ derivedSet (A ∪ B) at hz
    rw [derivedSet_union] at hz
    rcases hz with hzA | hzB
    · exact hA.noAccum z hzU (by simpa [acc] using hzA)
    · exact hB.noAccum z hzU (by simpa [acc] using hzB)

end ClosedDiscreteIn

/-- The empty set is closed and discrete in every open ambient set. -/
theorem closedDiscreteIn_empty {U : Set ℂ} (hU : IsOpen U) :
    ClosedDiscreteIn ∅ U where
  subset := by simp
  isClosed_rel := by
    simpa using (isClosed_compl_iff.mpr hU : IsClosed Uᶜ)
  noAccum := by
    intro z hzU hz
    change z ∈ derivedSet (∅ : Set ℂ) at hz
    rw [mem_derivedSet, accPt_iff_frequently_nhdsNE] at hz
    exact (by simpa using (frequently_false (nhdsWithin z ({z}ᶜ : Set ℂ)) hz))

/-- Finite unions preserve relative closed-discreteness. -/
theorem closedDiscreteIn_finset_biUnion {ι : Type*} [DecidableEq ι]
    {U : Set ℂ} {A : ι -> Set ℂ} (s : Finset ι)
    (hU : IsOpen U) (hA : ∀ i, i ∈ s -> ClosedDiscreteIn (A i) U) :
    ClosedDiscreteIn (⋃ i ∈ s, A i) U := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using closedDiscreteIn_empty (U := U) hU
  | insert a s has ih =>
      rw [Finset.set_biUnion_insert]
      exact (hA a (by simp)).union
        (ih fun i hi => hA i (by simp [hi]))

/-- No accumulation inside an open ambient set implies relative closedness. -/
theorem relativeClosed_of_isOpen_noAccumIn {A U : Set ℂ}
    (hU : IsOpen U) (hNo : NoAccumIn A U) :
    IsClosed (Uᶜ ∪ A) := by
  rw [← closure_subset_iff_isClosed]
  intro z hz
  by_cases hzU : z ∈ U
  · have hzClosureA : z ∈ closure A := by
      rw [mem_closure_iff_nhds] at hz ⊢
      intro V hV
      have hVU : V ∩ U ∈ nhds z := inter_mem hV (hU.mem_nhds hzU)
      rcases hz (V ∩ U) hVU with ⟨y, hyVU, hyUnion⟩
      rcases hyVU with ⟨hyV, hyU⟩
      rcases hyUnion with hyUc | hyA
      · exact False.elim (hyUc hyU)
      · exact ⟨y, hyV, hyA⟩
    rw [TransformerIdentifiability.NLayer.closure_eq_self_union_acc] at hzClosureA
    exact hzClosureA.elim Or.inr (fun hzAcc => False.elim (hNo z hzU hzAcc))
  · exact Or.inl hzU

/-- For subsets of an open set, the TeX no-accumulation condition is equivalent to
relative closed-discreteness. -/
theorem closedDiscreteIn_iff_noAccumIn {A U : Set ℂ}
    (hU : IsOpen U) (hAU : A ⊆ U) :
    ClosedDiscreteIn A U ↔ NoAccumIn A U := by
  constructor
  · exact ClosedDiscreteIn.noAccumIn
  · intro hNo
    exact ⟨hAU, relativeClosed_of_isOpen_noAccumIn hU hNo, hNo⟩

/-! ## Countable complements and domains -/

/-- A plane domain is a nonempty open connected subset of `ℂ`.  Nonemptiness is part of
`IsConnected`. -/
structure PlaneDomain (Ω : Set ℂ) : Prop where
  isOpen : IsOpen Ω
  isConnected : IsConnected Ω

namespace PlaneDomain

theorem nonempty {Ω : Set ℂ} (hΩ : PlaneDomain Ω) : Ω.Nonempty :=
  hΩ.isConnected.nonempty

theorem isPreconnected {Ω : Set ℂ} (hΩ : PlaneDomain Ω) : IsPreconnected Ω :=
  hΩ.isConnected.isPreconnected

end PlaneDomain

/-- The complement of a countable subset of `ℂ` is path connected. -/
theorem countable_compl_isPathConnected {E : Set ℂ} (hE : E.Countable) :
    IsPathConnected Eᶜ :=
  TransformerIdentifiability.NLayer.countable_compl_isPathConnected hE

/-- The complement of a countable subset of `ℂ` is connected. -/
theorem countable_compl_isConnected {E : Set ℂ} (hE : E.Countable) :
    IsConnected Eᶜ :=
  (countable_compl_isPathConnected hE).isConnected

/-- The complement of a closed countable subset of `ℂ` is a plane domain. -/
theorem countable_closed_compl_planeDomain {E : Set ℂ}
    (hEcount : E.Countable) (hEclosed : IsClosed E) :
    PlaneDomain Eᶜ where
  isOpen := hEclosed.isOpen_compl
  isConnected := countable_compl_isConnected hEcount

/-! ## Preimages of closed-discrete sets -/

/-- Preimages of closed-discrete target sets under nonconstant holomorphic maps are
closed-discrete in a connected open domain. -/
theorem closedDiscrete_preimage {Ω Λ : Set ℂ} {H : ℂ -> ℂ}
    (hΩopen : IsOpen Ω) (hΩconn : IsPreconnected Ω)
    (hH : AnalyticOnNhd ℂ H Ω)
    (hHnonconst : ∀ c : ℂ, ¬ Set.EqOn H (fun _ : ℂ => c) Ω)
    (hΛ : ClosedDiscreteIn Λ Set.univ) :
    ClosedDiscreteIn (Ω ∩ H ⁻¹' Λ) Ω := by
  refine (closedDiscreteIn_iff_noAccumIn hΩopen ?_).2 ?_
  · intro z hz
    exact hz.1
  · intro τ hτΩ hτacc
    have hclosedΛ : IsClosed Λ := by
      simpa using hΛ.isClosed_rel
    have hτClosureA : τ ∈ closure (Ω ∩ H ⁻¹' Λ) :=
      derivedSet_subset_closure _ hτacc
    have hHτClosureΛ : H τ ∈ closure Λ := by
      rw [mem_closure_iff_nhds] at hτClosureA ⊢
      intro V hV
      have hpre : H ⁻¹' V ∈ nhds τ :=
        (hH τ hτΩ).continuousAt.preimage_mem_nhds hV
      rcases hτClosureA (H ⁻¹' V) hpre with ⟨y, hyPre, hyA⟩
      exact ⟨H y, hyPre, hyA.2⟩
    have hHτΛ : H τ ∈ Λ :=
      hclosedΛ.closure_subset hHτClosureΛ
    have hΛavoidWithin :
        ∀ᶠ y in nhdsWithin (H τ) ({H τ}ᶜ : Set ℂ), y ∉ Λ :=
      TransformerIdentifiability.NLayer.eventually_notMem_of_not_mem_acc
        (hΛ.noAccum (H τ) (by simp))
    rw [eventually_nhdsWithin_iff] at hΛavoidWithin
    have hΛlocal : ∀ᶠ y in nhds (H τ), y ∈ Λ -> y = H τ := by
      filter_upwards [hΛavoidWithin] with y hyAvoid hyΛ
      by_contra hyne
      exact hyAvoid hyne hyΛ
    have hHeqLocal : ∀ᶠ z in nhds τ, H z ∈ Λ -> H z = H τ :=
      (hH τ hτΩ).continuousAt.tendsto.eventually hΛlocal
    have hHeqWithin :
        ∀ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ), H z ∈ Λ -> H z = H τ :=
      hHeqLocal.filter_mono nhdsWithin_le_nhds
    have hfreqA :
        ∃ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ), z ∈ Ω ∩ H ⁻¹' Λ := by
      simpa [acc, mem_derivedSet, accPt_iff_frequently_nhdsNE] using hτacc
    have hfreqEq :
        ∃ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ),
          H z = (fun _ : ℂ => H τ) z :=
      hfreqA.mp <| by
        filter_upwards [hHeqWithin] with z hzLocal hzA
        exact hzLocal hzA.2
    have hconst : AnalyticOnNhd ℂ (fun _ : ℂ => H τ) Ω := by
      intro z hz
      simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => H τ) z)
    have hEqOn : Set.EqOn H (fun _ : ℂ => H τ) Ω :=
      hH.eqOn_of_preconnected_of_frequently_eq hconst hΩconn hτΩ hfreqEq
    exact hHnonconst (H τ) hEqOn

/-! ## The odd-pi pole set -/

/-- TeX notation `Π = (2ℤ+1)π i`, using the k-head core pole set. -/
abbrev Pi : Set ℂ := sigmoidPoleSet

/-- The k-head core pole set agrees with the single-head toolkit pole set. -/
theorem sigmoidPoleSet_eq_oddPiI :
    sigmoidPoleSet = TransformerIdentifiability.NLayer.oddPiI := by
  ext z
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [hn]
    push_cast
    ring
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [hn]
    push_cast
    ring

/-- Membership in `Π` is equivalent to vanishing of the logistic denominator. -/
theorem mem_Pi_iff_denom_zero (z : ℂ) :
    z ∈ Pi ↔ 1 + Complex.exp (-z) = 0 := by
  rw [Pi, sigmoidPoleSet_eq_oddPiI]
  exact (TransformerIdentifiability.NLayer.one_add_exp_neg_eq_zero_iff z).symm

/-- `Π` is closed and discrete in the full plane. -/
theorem Pi_closedDiscrete : ClosedDiscreteIn Pi Set.univ := by
  set D : ℂ -> ℂ := fun z => 1 + Complex.exp (-z)
  have hclosedZero : IsClosed {z : ℂ | D z = 0} := by
    have hdiff : Differentiable ℂ D :=
      (differentiable_const 1).add (differentiable_id.neg.cexp)
    simpa using
      (IsClosed.preimage hdiff.continuous (isClosed_singleton (x := (0 : ℂ))))
  have hnoZero : NoAccumIn {z : ℂ | D z = 0} Set.univ :=
    TransformerIdentifiability.NLayer.noAccumIn_of_subset_zeroSet_of_analyticOnNhd_of_not_eventually_zero
      (by intro z hz; exact hz)
      (by
        intro z hz
        simpa [D] using TransformerIdentifiability.NLayer.denom_analytic z)
      (by
        intro ζ hζU hζzero hEventually
        have hnhds : {z : ℂ | D z = 0} ∈ nhds ζ := by
          simpa [Filter.Eventually] using hEventually
        exact TransformerIdentifiability.NLayer.sigmoidPoleSet_not_mem_nhds
          (by simpa [D] using hζzero) (by simpa [D] using hnhds))
  have hzeroCD : ClosedDiscreteIn {z : ℂ | D z = 0} Set.univ := by
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      simp
    · simpa using hclosedZero
    · exact hnoZero
  have hPiZero : Pi = {z : ℂ | D z = 0} := by
    ext z
    simpa [D] using mem_Pi_iff_denom_zero z
  simpa [hPiZero] using hzeroCD

/-- Points of `Π` are purely imaginary. -/
theorem Pi_re_eq_zero {z : ℂ} (hz : z ∈ Pi) : z.re = 0 := by
  rw [Pi, sigmoidPoleSet_eq_oddPiI] at hz
  obtain ⟨n, hn⟩ := hz
  rw [hn]
  simp

/-- The origin is not in `Π`. -/
theorem zero_notMem_Pi : (0 : ℂ) ∉ Pi := by
  intro hz
  have hzero := (mem_Pi_iff_denom_zero 0).1 hz
  norm_num at hzero

/-- No point of `Π` is zero. -/
theorem Pi_ne_zero {z : ℂ} (hz : z ∈ Pi) : z ≠ 0 := by
  intro hzero
  exact zero_notMem_Pi (by simpa [hzero] using hz)

/-- `Π` is disjoint from the real axis. -/
theorem ofReal_notMem_Pi (x : ℝ) : (x : ℂ) ∉ Pi := by
  intro hx
  have hxre := Pi_re_eq_zero hx
  have hx0 : x = 0 := by simpa using hxre
  exact zero_notMem_Pi (by simpa [hx0] using hx)

/-- `Π` is symmetric under negation. -/
theorem neg_mem_Pi {z : ℂ} (hz : z ∈ Pi) : -z ∈ Pi := by
  rw [Pi, sigmoidPoleSet_eq_oddPiI] at hz ⊢
  obtain ⟨n, hn⟩ := hz
  refine ⟨-n - 1, ?_⟩
  rw [hn]
  push_cast
  ring

/-- Distinct points of `Π` are separated by at least `2π`. -/
theorem Pi_dist_ge_two_pi {z w : ℂ} (hz : z ∈ Pi) (hw : w ∈ Pi) (hzw : z ≠ w) :
    2 * Real.pi ≤ dist z w := by
  rw [Pi, sigmoidPoleSet_eq_oddPiI] at hz hw
  obtain ⟨n, hn⟩ := hz
  obtain ⟨m, hm⟩ := hw
  have hnm : n ≠ m := by
    intro h
    apply hzw
    rw [hn, hm, h]
  have hdiff_ne : n - m ≠ 0 := sub_ne_zero.mpr hnm
  have hint : (1 : ℝ) ≤ |((n - m : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs hdiff_ne
  have him :
      (z - w).im = 2 * ((n - m : ℤ) : ℝ) * Real.pi := by
    rw [hn, hm]
    push_cast
    simp [sub_eq_add_neg]
    ring
  have himLower : 2 * Real.pi ≤ |(z - w).im| := by
    rw [him]
    calc
      2 * Real.pi ≤ 2 * |((n - m : ℤ) : ℝ)| * Real.pi := by
        nlinarith [hint, Real.pi_pos]
      _ = |2 * ((n - m : ℤ) : ℝ) * Real.pi| := by
        rw [abs_mul, abs_mul]
        have htwo : |(2 : ℝ)| = 2 := by norm_num
        rw [htwo, abs_of_nonneg Real.pi_pos.le]
  have him_le_norm : |(z - w).im| ≤ ‖z - w‖ :=
    Complex.abs_im_le_norm (z - w)
  simpa [dist_eq_norm] using himLower.trans him_le_norm

/-! ## Holomorphic evaluation of polynomials -/

/-- Evaluation map for a polynomial in coordinate variables plus the distinguished
identity variable `none`. -/
def polynomialEvalMap {ι : Type*} (f : ι -> ℂ -> ℂ) (τ : ℂ) : Option ι -> ℂ
  | none => τ
  | some i => f i τ

/-- Evaluating a multivariable polynomial on holomorphic coordinate functions and the
identity coordinate is holomorphic.  The variable `none` is the TeX variable `t`, while
`some i` is the coordinate function `f_i`. -/
theorem analyticOnNhd_mvPolynomial_eval {ι : Type*} {U : Set ℂ}
    {f : ι -> ℂ -> ℂ} (hf : ∀ i, AnalyticOnNhd ℂ (f i) U)
    (P : MvPolynomial (Option ι) ℂ) :
    AnalyticOnNhd ℂ
      (fun τ : ℂ => MvPolynomial.eval (polynomialEvalMap f τ) P)
      U := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      intro τ hτ
      simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => c) τ)
  | add P Q hP hQ =>
      intro τ hτ
      simpa using (hP τ hτ).add (hQ τ hτ)
  | mul_X P x hP =>
      intro τ hτ
      have hx :
          AnalyticAt ℂ
            (fun τ : ℂ => polynomialEvalMap f τ x)
            τ := by
        cases x with
        | none =>
            simpa using (analyticAt_id : AnalyticAt ℂ (fun τ : ℂ => τ) τ)
        | some i =>
            exact hf i τ hτ
      simpa using (hP τ hτ).mul hx

/-- Finite-coordinate version of holomorphic polynomial evaluation. -/
theorem holo_evaluation {M : Nat} {U : Set ℂ}
    {f : Fin M -> ℂ -> ℂ} (hf : ∀ i, AnalyticOnNhd ℂ (f i) U)
    (P : MvPolynomial (Option (Fin M)) ℂ) :
    AnalyticOnNhd ℂ
      (fun τ : ℂ => MvPolynomial.eval (polynomialEvalMap f τ) P)
      U :=
  analyticOnNhd_mvPolynomial_eval (ι := Fin M) (U := U) (f := f) hf P

/-- Coordinatewise vector-valued holomorphic polynomial evaluation. -/
theorem holo_vector_evaluation {M N : Nat} {U : Set ℂ}
    {f : Fin M -> ℂ -> ℂ} (hf : ∀ i, AnalyticOnNhd ℂ (f i) U)
    (P : Fin N -> MvPolynomial (Option (Fin M)) ℂ) :
    ∀ n : Fin N,
      AnalyticOnNhd ℂ
        (fun τ : ℂ => MvPolynomial.eval (polynomialEvalMap f τ) (P n))
        U := by
  intro n
  exact holo_evaluation hf (P n)

/-! ## Stratified accumulation -/

/-- Successive closed-discrete strata form the `StrataSystem` interface. -/
theorem strataSystem_of_closedDiscreteIn {S : Nat -> Set ℂ} {m : Nat}
    (hS : ∀ j, j < m -> ClosedDiscreteIn (S j) (partialUnion S j)ᶜ) :
    StrataSystem S m :=
  TransformerIdentifiability.NLayer.StrataSystem.of_noAccumIn m
    (fun j hj => (hS j hj).noAccum)

/-- Partial unions in a successive closed-discrete stratification are closed. -/
theorem stratified_partialUnion_closed {S : Nat -> Set ℂ} {m n : Nat}
    (hS : ∀ j, j < m -> ClosedDiscreteIn (S j) (partialUnion S j)ᶜ)
    (hn : n ≤ m) :
    IsClosed (partialUnion S n) :=
  (strataSystem_of_closedDiscreteIn hS).closed_partial n hn

/-- Iterated accumulation of an `m`-stratum system descends by one stratum per
accumulation. -/
theorem stratified_accumulation_subset {S : Nat -> Set ℂ} {m q : Nat}
    (hS : ∀ j, j < m -> ClosedDiscreteIn (S j) (partialUnion S j)ᶜ)
    (hq : q ≤ m) :
    accIter q (partialUnion S m) ⊆ partialUnion S (m - q) :=
  TransformerIdentifiability.NLayer.accIter_partialUnion_subset
    (strataSystem_of_closedDiscreteIn hS) q hq

/-- After `m` accumulation steps, an `m`-stratum system is empty. -/
theorem stratified_accumulation_empty {S : Nat -> Set ℂ} {m : Nat}
    (hS : ∀ j, j < m -> ClosedDiscreteIn (S j) (partialUnion S j)ᶜ) :
    accIter m (partialUnion S m) = ∅ :=
  TransformerIdentifiability.NLayer.accIter_partialUnion_eq_empty
    (strataSystem_of_closedDiscreteIn hS)

end TransformerIdentifiability.NLayer.KHead
