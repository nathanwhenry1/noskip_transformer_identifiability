import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Analytic.ActiveStratification
import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.SigmoidLaurent

set_option autoImplicit false

open Filter Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.NoSkip

/-!
# Laurent normal forms for no-skip active levels

The exact-order calculus is independent of the network model and is
reused from the neutral KHead analytic files.  The only NoSkip-specific inputs
below are `formalSlope`, formal stream polynomials, and the active-stratification
interface from NS094.  No layer recurrence is unfolded here.
-/

noncomputable section

/-! ## Neutral exact-order calculus -/

/-- Exact Laurent pole order `mu` with nonzero leading coefficient `coeff`. -/
abbrev LaurentNormalFormAt (f : ℂ → ℂ) (xi : ℂ) (mu : ℤ) (coeff : ℂ) : Prop :=
  KHead.LaurentNormalFormAt f xi mu coeff

namespace LaurentNormalFormAt

theorem leadingCoeff_ne_zero {f : ℂ → ℂ} {xi : ℂ} {mu : ℤ} {c : ℂ}
    (h : LaurentNormalFormAt f xi mu c) : c ≠ 0 :=
  KHead.LaurentNormalFormAt.leadingCoeff_ne_zero h

theorem congr {f g : ℂ → ℂ} {xi : ℂ} {mu : ℤ} {c : ℂ}
    (h : LaurentNormalFormAt f xi mu c)
    (hfg : f =ᶠ[nhdsWithin xi ({xi}ᶜ : Set ℂ)] g) :
    LaurentNormalFormAt g xi mu c :=
  KHead.LaurentNormalFormAt.congr h hfg

theorem meromorphicAt {f : ℂ → ℂ} {xi : ℂ} {mu : ℤ} {c : ℂ}
    (h : LaurentNormalFormAt f xi mu c) : MeromorphicAt f xi :=
  KHead.LaurentNormalFormAt.meromorphicAt h

theorem order_eq {f : ℂ → ℂ} {xi : ℂ} {mu : ℤ} {c : ℂ}
    (h : LaurentNormalFormAt f xi mu c) :
    meromorphicOrderAt f xi = (-mu : ℤ) :=
  KHead.LaurentNormalFormAt.order_eq h

theorem tendsto_coeff_of_order_zero
    {f : ℂ → ℂ} {xi : ℂ} {mu : ℤ} {c : ℂ}
    (h : LaurentNormalFormAt f xi mu c) (hmu : mu = 0) :
    Tendsto f (nhdsWithin xi ({xi}ᶜ : Set ℂ)) (nhds c) :=
  KHead.LaurentNormalFormAt.tendsto_coeff_of_order_zero h hmu

theorem tendsto_zero_of_order_neg
    {f : ℂ → ℂ} {xi : ℂ} {mu : ℤ} {c : ℂ}
    (h : LaurentNormalFormAt f xi mu c) (hmu : mu < 0) :
    Tendsto f (nhdsWithin xi ({xi}ᶜ : Set ℂ)) (nhds 0) :=
  KHead.LaurentNormalFormAt.tendsto_zero_of_order_neg h hmu

theorem blowsUpAt {f : ℂ → ℂ} {xi : ℂ} {mu : ℤ} {c : ℂ}
    (h : LaurentNormalFormAt f xi mu c) (hmu : 1 ≤ mu) :
    BlowsUpAt f xi :=
  KHead.LaurentNormalFormAt.blowsUpAt h hmu

theorem not_analyticAt {f : ℂ → ℂ} {xi : ℂ} {mu : ℤ} {c : ℂ}
    (h : LaurentNormalFormAt f xi mu c) (hmu : 1 ≤ mu) :
    ¬ AnalyticAt ℂ f xi :=
  KHead.LaurentNormalFormAt.not_analyticAt h hmu

theorem mul {f g : ℂ → ℂ} {xi : ℂ} {mu nu : ℤ} {c d : ℂ}
    (hf : LaurentNormalFormAt f xi mu c)
    (hg : LaurentNormalFormAt g xi nu d) :
    LaurentNormalFormAt (fun z => f z * g z) xi (mu + nu) (c * d) :=
  KHead.LaurentNormalFormAt.mul hf hg

theorem pow {f : ℂ → ℂ} {xi : ℂ} {mu : ℤ} {c : ℂ}
    (hf : LaurentNormalFormAt f xi mu c) (n : ℕ) :
    LaurentNormalFormAt (fun z => f z ^ n) xi ((n : ℤ) * mu) (c ^ n) :=
  KHead.LaurentNormalFormAt.pow hf n

theorem add_of_order_lt
    {f g : ℂ → ℂ} {xi : ℂ} {mu nu : ℤ} {c d : ℂ}
    (hf : LaurentNormalFormAt f xi mu c)
    (hg : LaurentNormalFormAt g xi nu d) (hnu : nu < mu) :
    LaurentNormalFormAt (fun z => f z + g z) xi mu c :=
  KHead.LaurentNormalFormAt.add_of_order_lt hf hg hnu

theorem add_analyticAt {f g : ℂ → ℂ} {xi : ℂ} {mu : ℤ} {c : ℂ}
    (hf : LaurentNormalFormAt f xi mu c)
    (hg : AnalyticAt ℂ g xi) (hmu : 1 ≤ mu) :
    LaurentNormalFormAt (fun z => f z + g z) xi mu c :=
  KHead.LaurentNormalFormAt.add_analyticAt hf hg hmu

theorem analyticAt_normalForm_of_not_eventually_eq
    {u : ℂ → ℂ} {xi : ℂ}
    (hu : AnalyticAt ℂ u xi)
    (hnot : ¬ (u =ᶠ[nhds xi] fun _ => u xi)) :
    ∃ kappa : ℕ, 1 ≤ kappa ∧ ∃ c : ℂ, c ≠ 0 ∧
      LaurentNormalFormAt (fun z => u z - u xi) xi (-(kappa : ℤ)) c :=
  KHead.LaurentNormalFormAt.analyticAt_normalForm_of_not_eventually_eq hu hnot

theorem inv {f : ℂ → ℂ} {xi : ℂ} {mu : ℤ} {c : ℂ}
    (hf : LaurentNormalFormAt f xi mu c) :
    LaurentNormalFormAt (fun z => (f z)⁻¹) xi (-mu) c⁻¹ :=
  KHead.LaurentNormalFormAt.inv hf

end LaurentNormalFormAt

theorem csig_normalForm_of_mem_Pi {zeta : ℂ} (hzeta : zeta ∈ Pi) :
    LaurentNormalFormAt csig zeta 1 1 :=
  KHead.csig_normalForm_of_mem_Pi hzeta

theorem csig_comp_normalForm {H : ℂ → ℂ} {xi pole c : ℂ} {kappa : ℕ}
    (hpole : pole ∈ Pi) (hH : AnalyticAt ℂ H xi) (hHxi : H xi = pole)
    (hkappa : 1 ≤ kappa)
    (hNF : LaurentNormalFormAt (fun z => H z - pole) xi (-(kappa : ℤ)) c) :
    LaurentNormalFormAt (fun z => csig (H z)) xi (kappa : ℤ) c⁻¹ :=
  KHead.csig_comp_normalForm hpole hH hHxi hkappa hNF

theorem exactOrder_normalForm_of_meromorphicAt
    {H : ℂ → ℂ} {xi : ℂ} (hmer : MeromorphicAt H xi)
    (hnot : ¬ (H =ᶠ[nhdsWithin xi ({xi}ᶜ : Set ℂ)] fun _ => 0)) :
    ∃ mu : ℤ, ∃ c : ℂ, LaurentNormalFormAt H xi mu c :=
  KHead.lem_exact_order_at_center hmer hnot

theorem exactOrder_normalForm_of_meromorphicAt_le
    {H : ℂ → ℂ} {xi : ℂ} {m : ℤ} (hmer : MeromorphicAt H xi)
    (hnot : ¬ (H =ᶠ[nhdsWithin xi ({xi}ᶜ : Set ℂ)] fun _ => 0))
    (hbound : ((-m : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt H xi) :
    ∃ mu : ℤ, ∃ c : ℂ, LaurentNormalFormAt H xi mu c ∧ mu ≤ m :=
  KHead.lem_exact_order_at_center_le hmer hnot hbound

/-! ## NoSkip formal polynomial and stream adapters -/

/-- Evaluation of a NoSkip formal polynomial along meromorphic gate germs is
meromorphic.  This uses only the polynomial operations. -/
theorem evalFormalPolyComplex_meromorphicAt {L k : Nat}
    (p : FormalPoly L k) {xi : ℂ} {eta : FormalVar L k → ℂ → ℂ}
    (heta : ∀ x : FormalVar L k, MeromorphicAt (eta x) xi) :
    MeromorphicAt (fun z => evalFormalPolyComplex (fun x => eta x z) p) xi := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      simp [evalFormalPolyComplex]
  | add p q hp hq =>
      simpa [evalFormalPolyComplex] using hp.add hq
  | mul_X p x hp =>
      simpa [evalFormalPolyComplex] using hp.mul (heta x)

/-- Coordinatewise complex evaluation of a NoSkip formal vector. -/
noncomputable def evalFormalVecComplex {L k d : Nat}
    (eta : FormalVar L k → ℂ) (x : FormalVec L k d) : ComplexVec d :=
  fun i => evalFormalPolyComplex eta (x i)

theorem evalFormalVecComplex_meromorphicAt {L k d : Nat}
    (x : FormalVec L k d) {xi : ℂ} {eta : FormalVar L k → ℂ → ℂ}
    (heta : ∀ y : FormalVar L k, MeromorphicAt (eta y) xi) :
    ∀ i : Fin d, MeromorphicAt
      (fun z => evalFormalVecComplex (fun y => eta y z) x i) xi := by
  intro i
  exact evalFormalPolyComplex_meromorphicAt (x i) heta

theorem formalW_coord_meromorphicAt {L k d : Nat}
    (theta : Params L k d) (w v : Vec d) (n : Nat) (hn : n ≤ L)
    {xi : ℂ} {eta : FormalVar L k → ℂ → ℂ}
    (heta : ∀ y : FormalVar L k, MeromorphicAt (eta y) xi) (i : Fin d) :
    MeromorphicAt
      (fun z => evalFormalVecComplex (fun y => eta y z)
        (formalW theta w v n hn) i) xi :=
  evalFormalVecComplex_meromorphicAt (formalW theta w v n hn) heta i

theorem formalV_coord_meromorphicAt {L k d : Nat}
    (theta : Params L k d) (w v : Vec d) (n : Nat) (hn : n ≤ L)
    {xi : ℂ} {eta : FormalVar L k → ℂ → ℂ}
    (heta : ∀ y : FormalVar L k, MeromorphicAt (eta y) xi) (i : Fin d) :
    MeromorphicAt
      (fun z => evalFormalVecComplex (fun y => eta y z)
        (formalV theta w v n hn) i) xi :=
  evalFormalVecComplex_meromorphicAt (formalV theta w v n hn) heta i

theorem complexFormalSlope_meromorphicAt {L k d : Nat}
    (theta : Params L k d) (w v : Vec d) (x : FormalVar L k)
    {xi : ℂ} {eta : FormalVar L k → ℂ → ℂ}
    (heta : ∀ y : FormalVar L k, MeromorphicAt (eta y) xi) :
    MeromorphicAt
      (fun z => complexFormalSlope theta w v (fun y => eta y z) x) xi :=
  evalFormalPolyComplex_meromorphicAt (formalSlope theta w v x.1 x.2) heta

theorem formalLevel_meromorphicAt {r L k d : Nat}
    (theta : Params L k d) (w v : Vec d) (x : FormalVar L k)
    {xi : ℂ} {eta : FormalVar L k → ℂ → ℂ}
    (heta : ∀ y : FormalVar L k, MeromorphicAt (eta y) xi) :
    MeromorphicAt
      (fun z => formalLevel (r := r) theta w v (fun y => eta y z) x z) xi := by
  have hid : MeromorphicAt (fun z : ℂ => z) xi := analyticAt_id.meromorphicAt
  have hslope := complexFormalSlope_meromorphicAt theta w v x heta
  have hconst : MeromorphicAt (fun _ : ℂ => (logScale r : ℂ)) xi :=
    analyticAt_const.meromorphicAt
  simpa [formalLevel] using (hid.mul hslope).add hconst

/-- A nonzero meromorphic formal-polynomial germ has a finite exact Laurent
normal form. -/
theorem evalFormalPolyComplex_exactOrder_normalForm {L k : Nat}
    (p : FormalPoly L k) {xi : ℂ} {eta : FormalVar L k → ℂ → ℂ}
    (heta : ∀ x : FormalVar L k, MeromorphicAt (eta x) xi)
    (hnot : ¬ ((fun z => evalFormalPolyComplex (fun x => eta x z) p)
      =ᶠ[nhdsWithin xi ({xi}ᶜ : Set ℂ)] fun _ => 0)) :
    ∃ mu : ℤ, ∃ c : ℂ,
      LaurentNormalFormAt
        (fun z => evalFormalPolyComplex (fun x => eta x z) p) xi mu c :=
  exactOrder_normalForm_of_meromorphicAt
    (evalFormalPolyComplex_meromorphicAt p heta) hnot

/-! ## Active-level exact-order adapters -/

/-- An active level hitting `Pi` cannot be locally constant at that pole. -/
theorem activeLevel_not_eventuallyEq_at_pole
    {r L k d : Nat} {theta : Params L k d}
    {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification (r := r) theta D)
    (l : Fin L) (a : Fin k) (ha : a ∈ activeHeads theta l)
    {xi : ℂ} (hxiOmega : xi ∈ D.Omega l.1)
    (hxiPi : D.level (l, a) xi ∈ Pi) :
    ¬ (D.level (l, a) =ᶠ[nhds xi] fun _ => D.level (l, a) xi) := by
  intro heq
  have hlevel : AnalyticOnNhd ℂ (D.level (l, a)) (D.Omega l.1) :=
    hD.level_holomorphic l a ha
  have hconst : AnalyticOnNhd ℂ (fun _ : ℂ => D.level (l, a) xi)
      (D.Omega l.1) := fun _ _ => analyticAt_const
  have hEqOn := hlevel.eqOn_of_preconnected_of_eventuallyEq hconst
    (hD.domain l.1 (Nat.le_of_lt l.2)).isPreconnected hxiOmega heq
  exact level_not_constant_pole_of_level_zero (r := r) D
    (hD.origin_mem l.1 (Nat.le_of_lt l.2)) (hD.level_zero l a ha)
      (D.level (l, a) xi) hxiPi hEqOn

/-- At an active pole, the level difference has a finite positive vanishing
order and its sigmoid has the corresponding exact Laurent pole. -/
theorem activeLevel_sigmoid_normalForms_at_pole
    {r L k d : Nat} {theta : Params L k d}
    {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification (r := r) theta D)
    (l : Fin L) (a : Fin k) (ha : a ∈ activeHeads theta l)
    {xi : ℂ} (hxiOmega : xi ∈ D.Omega l.1)
    (hxiPi : D.level (l, a) xi ∈ Pi) :
    ∃ kappa : ℕ, ∃ c : ℂ, 1 ≤ kappa ∧ c ≠ 0 ∧
      LaurentNormalFormAt
        (fun z => D.level (l, a) z - D.level (l, a) xi)
        xi (-(kappa : ℤ)) c ∧
      LaurentNormalFormAt (fun z => csig (D.level (l, a) z))
        xi (kappa : ℤ) c⁻¹ := by
  have hanalytic : AnalyticAt ℂ (D.level (l, a)) xi :=
    hD.level_holomorphic l a ha xi hxiOmega
  have hnot := activeLevel_not_eventuallyEq_at_pole
    hD l a ha hxiOmega hxiPi
  obtain ⟨kappa, hkappa, c, hc, hNF⟩ :=
    LaurentNormalFormAt.analyticAt_normalForm_of_not_eventually_eq hanalytic hnot
  exact ⟨kappa, c, hkappa, hc, hNF,
    csig_comp_normalForm hxiPi hanalytic rfl hkappa hNF⟩

/-- Every point of an active reduced stratum supplies at least one active head
with exact level-zero and sigmoid-pole normal forms. -/
theorem activeStratum_exists_sigmoid_normalForms
    {r L k d : Nat} {theta : Params L k d}
    {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification (r := r) theta D)
    (l : Fin L) {xi : ℂ} (hxi : xi ∈ D.stratum l.1) :
    ∃ a : Fin k, a ∈ activeHeads theta l ∧
      ∃ kappa : ℕ, ∃ c : ℂ, 1 ≤ kappa ∧ c ≠ 0 ∧
        LaurentNormalFormAt
          (fun z => D.level (l, a) z - D.level (l, a) xi)
          xi (-(kappa : ℤ)) c ∧
        LaurentNormalFormAt (fun z => csig (D.level (l, a) z))
          xi (kappa : ℤ) c⁻¹ := by
  rw [mem_activeStratum_iff hD l xi] at hxi
  rcases hxi with ⟨a, ha, hxiOmega, hxiPi⟩
  rcases activeLevel_sigmoid_normalForms_at_pole
    hD l a ha hxiOmega hxiPi with ⟨kappa, c, hkappa, hc, hlevel, hsigmoid⟩
  exact ⟨a, ha, kappa, c, hkappa, hc, hlevel, hsigmoid⟩

end

end TransformerIdentifiability.NLayer.NoSkip
