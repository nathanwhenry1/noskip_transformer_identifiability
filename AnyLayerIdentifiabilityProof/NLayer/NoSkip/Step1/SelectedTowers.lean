import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Step1.TierCascadeData
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Analytic.LaurentNormalForm
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Analytic.SelectedTop
import AnyLayerIdentifiabilityProof.NLayer.KHead.Step1.SelectedTowers

set_option autoImplicit false

open Filter Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.NoSkip

/-!
# Step 1 first-tier pole creation (NS102)

Authoritative math: `tra:cascade` item (ii) of
`tex_modular_no_skip_connections/sections/09-step1-attention.tex`.

At a pole `ξ ∈ P(q'_{1h})` of the first-layer gate `s_{1h}` (analytically continued in
the probe parameter), the no-skip first-layer stream

  `w₁ = (C₁ − ∑_a s_{1a} V_{1a}) w  =  ∑_a (1 − s_{1a}) V_{1a} w`

has a **simple pole** whose residue is proportional to `V_{1h} w`, because the pole enters
only through the `s_{1h} V_{1h}` term.  Every other head `a ≠ h`, the collapsed constant
`C₁ w`, and (crucially) the *absent* skip summand `+X` of the skip model contribute only to
the *regular part*: none of them changes the singular/residue part.

The file proves:

* `firstTierPoleCreation_sum` — the abstract pole-creation / residue calculus, stated for
  gate germs and value coefficients.  This is the mathematically load-bearing content.
* `firstLayerStreamCoord_eq` — the no-skip first-layer stream coordinate is exactly
  `∑_a (1 − s_{1a}) (V_{1a} w)_i`, using the no-skip collapse identity
  `C₁ = ∑_a V_{1a}` (there is **no** `+w` skip term).
* `step1FirstTierPoleCreation` — the combination: at a simple pole of head `h`'s gate with
  the other heads regular, the stream coordinate `i` has an order-`1` Laurent normal form
  with leading coefficient `−(residue) · (V_{1h} w)_i`.
* `step1FirstTierPoleCreation_skip_regular` — adding an arbitrary analytic summand (the
  would-be skip contribution) leaves the principal part unchanged, formalizing that the
  absent skip term is regular.
* `step1FirstTierResidueCoefficient` — the residue magnitude `(V_{1h} w)_i` equals the
  canonical first-tier residue record coefficient of NS101.
-/

noncomputable section

/-! ## Ring-hom adapters for complex formal-polynomial evaluation -/

/-- `evalFormalPolyComplex` is the ring-hom evaluation `eval₂Hom (algebraMap ℝ ℂ) η`. -/
theorem evalFormalPolyComplex_eq_hom {L k : Nat} (η : FormalVar L k → ℂ)
    (p : FormalPoly L k) :
    evalFormalPolyComplex η p = MvPolynomial.eval₂Hom (algebraMap ℝ ℂ) η p :=
  rfl

theorem evalFormalPolyComplex_map_sub {L k : Nat} (η : FormalVar L k → ℂ)
    (p q : FormalPoly L k) :
    evalFormalPolyComplex η (p - q) =
      evalFormalPolyComplex η p - evalFormalPolyComplex η q := by
  simp only [evalFormalPolyComplex_eq_hom, map_sub]

theorem evalFormalPolyComplex_map_mul {L k : Nat} (η : FormalVar L k → ℂ)
    (p q : FormalPoly L k) :
    evalFormalPolyComplex η (p * q) =
      evalFormalPolyComplex η p * evalFormalPolyComplex η q := by
  simp only [evalFormalPolyComplex_eq_hom, map_mul]

theorem evalFormalPolyComplex_map_sum {L k : Nat} {ι : Type*} (η : FormalVar L k → ℂ)
    (s : Finset ι) (f : ι → FormalPoly L k) :
    evalFormalPolyComplex η (∑ i ∈ s, f i) =
      ∑ i ∈ s, evalFormalPolyComplex η (f i) := by
  simp only [evalFormalPolyComplex_eq_hom, map_sum]

@[simp] theorem evalFormalPolyComplex_formalConst {L k : Nat} (η : FormalVar L k → ℂ)
    (x : ℝ) :
    evalFormalPolyComplex (L := L) (k := k) η (formalConst x) = (x : ℂ) := by
  simp [evalFormalPolyComplex, formalConst, MvPolynomial.eval₂_C, Complex.coe_algebraMap]

@[simp] theorem evalFormalPolyComplex_formalGate {L k : Nat} (η : FormalVar L k → ℂ)
    (l : Fin L) (a : Fin k) :
    evalFormalPolyComplex η (formalGate l a) = η (l, a) := by
  simp [evalFormalPolyComplex, formalGate, MvPolynomial.eval₂_X]

/-! ## The abstract first-tier pole-creation calculus -/

/-- A nonzero constant germ is an order-zero Laurent normal form. -/
theorem laurentNormalFormAt_const {ξ c : ℂ} (hc : c ≠ 0) :
    LaurentNormalFormAt (fun _ => c) ξ 0 c := by
  refine ⟨hc, ⟨fun _ => c, analyticAt_const, rfl, ?_⟩⟩
  filter_upwards with z
  simp

/-- **First-tier pole creation.**

Given gate germs `g`, complex value coefficients `c`, a distinguished head `h` whose gate
has a simple pole (`LaurentNormalFormAt (g h) ξ 1 ρ`) while every other head's gate is
analytic at `ξ`, and `c h ≠ 0`, the stream coordinate `∑_a (1 − g a z) · c a` has an
order-`1` Laurent normal form with leading coefficient `−(ρ · c h)`.

The constant part `∑_a c a` and every off-head term `(1 − g a z) c a` are analytic and are
absorbed into the regular part; only the `g h` term produces the pole. -/
theorem firstTierPoleCreation_sum {k : Nat}
    (g : Fin k → ℂ → ℂ) (c : Fin k → ℂ) (h : Fin k) {ξ ρ : ℂ}
    (hpole : LaurentNormalFormAt (g h) ξ 1 ρ)
    (hreg : ∀ a, a ≠ h → AnalyticAt ℂ (g a) ξ)
    (hc : c h ≠ 0) :
    LaurentNormalFormAt (fun z => ∑ a, (1 - g a z) * c a) ξ 1 (-(ρ * c h)) := by
  classical
  -- The single singular term `g h z * (-c h)`.
  have hSing0 :=
    LaurentNormalFormAt.mul hpole (laurentNormalFormAt_const (ξ := ξ) (neg_ne_zero.mpr hc))
  have hone : (1 : ℤ) + 0 = 1 := by ring
  rw [hone] at hSing0
  -- The regular remainder.
  have hRegAnalytic : AnalyticAt ℂ
      (fun z => (∑ a, c a) - ∑ a ∈ Finset.univ.erase h, g a z * c a) ξ := by
    refine AnalyticAt.sub analyticAt_const ?_
    have hfun : (fun z => ∑ a ∈ Finset.univ.erase h, g a z * c a)
        = ∑ a ∈ Finset.univ.erase h, (fun z => g a z * c a) := by
      funext z; simp [Finset.sum_apply]
    rw [hfun]
    refine Finset.analyticAt_sum (𝕜 := ℂ) (E := ℂ) (F := ℂ) _ ?_
    intro a ha
    exact (hreg a (Finset.ne_of_mem_erase ha)).mul analyticAt_const
  -- The pointwise split into singular + regular part.
  have hfun : (fun z => ∑ a, (1 - g a z) * c a)
      = (fun z => g h z * (-c h)
          + ((∑ a, c a) - ∑ a ∈ Finset.univ.erase h, g a z * c a)) := by
    funext z
    have hsplit : ∑ a, g a z * c a
        = g h z * c h + ∑ a ∈ Finset.univ.erase h, g a z * c a := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ h)]
    have hsub : ∑ a, (1 - g a z) * c a = (∑ a, c a) - ∑ a, g a z * c a := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro a _; ring
    rw [hsub, hsplit]; ring
  rw [hfun]
  have hcoeff : ρ * (-c h) = -(ρ * c h) := by ring
  rw [hcoeff] at hSing0
  exact LaurentNormalFormAt.add_analyticAt hSing0 hRegAnalytic (le_refl 1)

/-! ## The no-skip first-layer stream coordinate in closed form -/

/-- The no-skip first-layer contrast stream, one layer in, is
`(C₁ − ∑_a z_{0a} V_{0a}) w`. -/
theorem formalW_one {L k d : Nat} (theta : Params L k d) (w v : Vec d)
    (h1 : 1 ≤ L) :
    formalW theta w v 1 h1
      = (formalCollapseMatrix theta ⟨0, Nat.lt_of_succ_le h1⟩
          - formalGatedValueSum theta ⟨0, Nat.lt_of_succ_le h1⟩)
          *ᵥ realVecToFormal w := by
  show (formalPoint theta w v 1 h1).1 = _
  rw [formalPoint_succ]
  rfl

/-- **Closed form of the first-layer no-skip stream coordinate.**

Using the no-skip collapse identity `C₁ = ∑_a V_{1a}` (there is no additive skip term),
coordinate `i` of the analytically continued first-layer stream is
`∑_a (1 − s_{1a}) (V_{1a} w)_i`. -/
theorem firstLayerStreamCoord_eq {L k d : Nat} (theta : Params L k d)
    (w v : Vec d) (h1 : 1 ≤ L) (η : FormalVar L k → ℂ) (i : Fin d) :
    evalFormalVecComplex η (formalW theta w v 1 h1) i
      = ∑ a : Fin k, (1 - η (⟨0, Nat.lt_of_succ_le h1⟩, a))
          * ((valueMatrix theta ⟨0, Nat.lt_of_succ_le h1⟩ a *ᵥ w) i : ℂ) := by
  classical
  set l0 : Fin L := ⟨0, Nat.lt_of_succ_le h1⟩ with hl0
  -- Per-entry evaluation of the collapsed-minus-gated matrix.
  have hentry : ∀ j : Fin d,
      evalFormalPolyComplex η
          ((formalCollapseMatrix theta l0 - formalGatedValueSum theta l0) i j)
        = ((collapseMatrix theta l0) i j : ℂ)
          - ∑ a : Fin k, η (l0, a) * ((valueMatrix theta l0 a) i j : ℂ) := by
    intro j
    rw [Matrix.sub_apply, evalFormalPolyComplex_map_sub]
    congr 1
    · rw [formalCollapseMatrix, realMatrixToFormal_apply, evalFormalPolyComplex_formalConst]
    · rw [formalGatedValueSum, Matrix.sum_apply, evalFormalPolyComplex_map_sum]
      refine Finset.sum_congr rfl ?_
      intro a _
      rw [Matrix.smul_apply, smul_eq_mul, evalFormalPolyComplex_map_mul,
        evalFormalPolyComplex_formalGate, formalValueMatrix, realMatrixToFormal_apply,
        evalFormalPolyComplex_formalConst]
  -- Collapse row is the sum of the value rows (no-skip identity).
  have hC : ∀ j : Fin d,
      ((collapseMatrix theta l0) i j : ℂ) = ∑ a : Fin k, ((valueMatrix theta l0 a) i j : ℂ) := by
    intro j
    rw [collapseMatrix_eq_valueSum, valueSum, Matrix.sum_apply]
    push_cast
    rfl
  -- Complexified matrix-vector coordinate.
  have hV : ∀ a : Fin k,
      ((valueMatrix theta l0 a *ᵥ w) i : ℂ)
        = ∑ j : Fin d, ((valueMatrix theta l0 a) i j : ℂ) * (w j : ℂ) := by
    intro a
    simp only [Matrix.mulVec, dotProduct]
    push_cast
    rfl
  -- Assemble.
  have hexp : ((formalCollapseMatrix theta l0 - formalGatedValueSum theta l0)
        *ᵥ realVecToFormal w) i
      = ∑ j : Fin d, (formalCollapseMatrix theta l0 - formalGatedValueSum theta l0) i j
          * formalConst (w j) := by
    simp only [Matrix.mulVec, dotProduct, realVecToFormal]
  have hstart : evalFormalVecComplex η (formalW theta w v 1 h1) i
      = evalFormalPolyComplex η
          (((formalCollapseMatrix theta l0 - formalGatedValueSum theta l0)
            *ᵥ realVecToFormal w) i) := by
    rw [evalFormalVecComplex, formalW_one]
  rw [hstart, hexp, evalFormalPolyComplex_map_sum]
  simp only [evalFormalPolyComplex_map_mul, evalFormalPolyComplex_formalConst, hentry]
  -- Now a finite double-sum reindexing, all over ℂ.
  have hLHS :
      (∑ j : Fin d,
          (((collapseMatrix theta l0) i j : ℂ)
              - ∑ a : Fin k, η (l0, a) * ((valueMatrix theta l0 a) i j : ℂ)) * (w j : ℂ))
        = ∑ j : Fin d, ∑ a : Fin k,
            (1 - η (l0, a)) * ((valueMatrix theta l0 a) i j : ℂ) * (w j : ℂ) := by
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [hC j, ← Finset.sum_sub_distrib, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro a _; ring
  have hRHS :
      (∑ a : Fin k, (1 - η (l0, a)) * ((valueMatrix theta l0 a *ᵥ w) i : ℂ))
        = ∑ a : Fin k, ∑ j : Fin d,
            (1 - η (l0, a)) * ((valueMatrix theta l0 a) i j : ℂ) * (w j : ℂ) := by
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [hV a, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _; ring
  rw [hLHS, hRHS, Finset.sum_comm]

/-! ## First-tier pole creation for the no-skip stream -/

/-- **NS102 — first-tier pole creation.**

At a simple pole `ξ` of the first-layer gate of head `h` (residue `ρ`), with every other
head's gate analytic at `ξ` and `(V_{1h} w)_i ≠ 0`, coordinate `i` of the analytically
continued no-skip first-layer stream has an order-`1` Laurent normal form with leading
coefficient `−(ρ · (V_{1h} w)_i)`.  The residue is proportional to `V_{1h} w`; the collapsed
constant `C₁ w` and the off-head terms are regular. -/
theorem step1FirstTierPoleCreation {L k d : Nat} (theta : Params L k d)
    (w v : Vec d) (h1 : 1 ≤ L) (η : FormalVar L k → ℂ → ℂ) (h : Fin k)
    {ξ ρ : ℂ} (i : Fin d)
    (hpole : LaurentNormalFormAt (η (⟨0, Nat.lt_of_succ_le h1⟩, h)) ξ 1 ρ)
    (hreg : ∀ a, a ≠ h → AnalyticAt ℂ (η (⟨0, Nat.lt_of_succ_le h1⟩, a)) ξ)
    (hc : ((valueMatrix theta ⟨0, Nat.lt_of_succ_le h1⟩ h *ᵥ w) i : ℂ) ≠ 0) :
    LaurentNormalFormAt
      (fun z => evalFormalVecComplex (fun y => η y z) (formalW theta w v 1 h1) i)
      ξ 1 (-(ρ * ((valueMatrix theta ⟨0, Nat.lt_of_succ_le h1⟩ h *ᵥ w) i : ℂ))) := by
  have hcoord :
      (fun z => evalFormalVecComplex (fun y => η y z) (formalW theta w v 1 h1) i)
        = (fun z => ∑ a : Fin k, (1 - η (⟨0, Nat.lt_of_succ_le h1⟩, a) z)
            * ((valueMatrix theta ⟨0, Nat.lt_of_succ_le h1⟩ a *ᵥ w) i : ℂ)) := by
    funext z
    exact firstLayerStreamCoord_eq theta w v h1 (fun y => η y z) i
  rw [hcoord]
  exact firstTierPoleCreation_sum
    (fun a => η (⟨0, Nat.lt_of_succ_le h1⟩, a))
    (fun a => ((valueMatrix theta ⟨0, Nat.lt_of_succ_le h1⟩ a *ᵥ w) i : ℂ))
    h hpole hreg hc

/-- **Absence of the skip term only affects the regular part.**

Adding an arbitrary germ `skip` analytic at `ξ` — the summand that the *skip* model carries
(`+X`) and the no-skip model omits — leaves the principal part of the stream coordinate
unchanged: the order and leading coefficient are identical.  This formalizes item (ii)'s
parenthetical that the skip term contributes only to the regular part. -/
theorem step1FirstTierPoleCreation_skip_regular {L k d : Nat} (theta : Params L k d)
    (w v : Vec d) (h1 : 1 ≤ L) (η : FormalVar L k → ℂ → ℂ) (h : Fin k)
    {ξ ρ : ℂ} (i : Fin d) (skip : ℂ → ℂ)
    (hpole : LaurentNormalFormAt (η (⟨0, Nat.lt_of_succ_le h1⟩, h)) ξ 1 ρ)
    (hreg : ∀ a, a ≠ h → AnalyticAt ℂ (η (⟨0, Nat.lt_of_succ_le h1⟩, a)) ξ)
    (hc : ((valueMatrix theta ⟨0, Nat.lt_of_succ_le h1⟩ h *ᵥ w) i : ℂ) ≠ 0)
    (hskip : AnalyticAt ℂ skip ξ) :
    LaurentNormalFormAt
      (fun z => evalFormalVecComplex (fun y => η y z) (formalW theta w v 1 h1) i + skip z)
      ξ 1 (-(ρ * ((valueMatrix theta ⟨0, Nat.lt_of_succ_le h1⟩ h *ᵥ w) i : ℂ))) :=
  LaurentNormalFormAt.add_analyticAt
    (step1FirstTierPoleCreation theta w v h1 η h i hpole hreg hc) hskip (le_refl 1)

/-! ## Connection to the NS101 first-tier residue record -/

/-- The zero-based first Step-1 layer index coincides with `0 : Fin (n + 2)`. -/
theorem step1FirstLayerIndex_eq {n : Nat} :
    (⟨0, Nat.lt_of_succ_le (show 1 ≤ n + 2 by omega)⟩ : Fin (n + 2)) = 0 := by
  ext; simp

/-- The residue magnitude `(V_{1h} w)_i` produced by first-tier pole creation is exactly the
canonical first-tier residue-record coefficient of NS101. -/
theorem step1FirstTierResidueCoefficient {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w : Vec d)
    (h : Fin k) (i : Fin d) :
    (step1TargetTierResidueRecord H w h (step1FirstTierIndex n) i).coefficient
      = (valueMatrix theta' 0 h *ᵥ w) i :=
  step1TargetTierResidueRecord_first_coefficient H w h i

/-- **NS102 stated in NS101 vocabulary (target continuation).**

Coordinate `i` of the analytically continued target first-layer stream has an order-`1`
Laurent normal form whose leading coefficient is `−(ρ · c)`, where `c` is the canonical
first-tier residue-record coefficient `(step1TargetTierResidueRecord …).coefficient`. -/
theorem step1TargetFirstTierPoleCreation {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w v : Vec d)
    (η : FormalVar (n + 2) k → ℂ → ℂ) (h : Fin k) {ξ ρ : ℂ} (i : Fin d)
    (hpole : LaurentNormalFormAt (η (0, h)) ξ 1 ρ)
    (hreg : ∀ a, a ≠ h → AnalyticAt ℂ (η (0, a)) ξ)
    (hc : (((step1TargetTierResidueRecord H w h (step1FirstTierIndex n) i).coefficient : ℝ) : ℂ)
        ≠ 0) :
    LaurentNormalFormAt
      (fun z => evalFormalVecComplex (fun y => η y z) (formalW theta' w v 1 (by omega)) i)
      ξ 1 (-(ρ * (((step1TargetTierResidueRecord H w h (step1FirstTierIndex n) i).coefficient
        : ℝ) : ℂ))) := by
  have hidx : (⟨0, Nat.lt_of_succ_le (show 1 ≤ n + 2 by omega)⟩ : Fin (n + 2)) = 0 :=
    step1FirstLayerIndex_eq
  rw [step1FirstTierResidueCoefficient H w h i] at hc ⊢
  refine step1FirstTierPoleCreation theta' w v (by omega) η h i ?_ ?_ ?_
  · rw [hidx]; exact hpole
  · intro a ha; rw [hidx]; exact hreg a ha
  · rw [hidx]; exact hc

/-!
# Step 1 selected tower construction (NS103)

Authoritative math: `tra:cascade` items (ii) ignition + final residue, with the
no-skip substitution dictionary `C_ℓ := ∑_a V_{ℓa}`.  This section ports the
KHead selected-tower cluster to the no-skip cascade certificate, whose data is
matrix/probe-vector based (there is no `ProbePoint`; residue and ignition are the
matrices `cascadeFinalProduct` / `cascadeIgnitionMatrix` paired with a probe
`w : Vec d`).

* `step1HeadChain` — the NS100 `HeadChain (n+2) k p` associated to an NS101
  `Step1SelectedChain`, with its layer / selected-variable structure.
* `HeadChain.selectedValueProduct` and
  `step1HeadChain_selectedValueProduct_eq_cascadeProduct` (+ `_cascadeFinalProduct`,
  `_mulVec`) — the substitution-dictionary bridge: the selected value product of
  the chain equals the NS055 cascade prefix / final product (and its residue
  vector).
* `step1IgnitionQuadratic_eq_selectedValueProduct` — the ignition quadratic of a
  later tier is the attention bilinear form on the residue-product-transported
  probe.
* `separatedProbe_*` — from a probe avoiding the separated vanishing locus, every
  selected ignition quadratic and the final residue vector are nonzero.
* `Step1TowerMemberIndex` / `step1TowerMemberHeadChain` / `step1IgnitionTopConstant`
  / `step1ResidueTopConstant` — the tower-member indexing and the nonvanishing
  "top constant" values connected to the actual selected coefficients.
-/

/-! ## The NS100 head chain of an NS101 selected chain -/

/-- The NS100 `HeadChain` of length `p` selected by an NS101 `Step1SelectedChain`. -/
def step1HeadChain {n k : Nat} (C : Step1SelectedChain n k) (p : Nat)
    (hp : p ≤ n + 2) : HeadChain (n + 2) k p where
  head := fun i => C.headAt ⟨i.1, Nat.lt_of_lt_of_le i.2 hp⟩
  length_le := hp

@[simp] theorem step1HeadChain_head {n k : Nat} (C : Step1SelectedChain n k)
    {p : Nat} (hp : p ≤ n + 2) (i : Fin p) :
    (step1HeadChain C p hp).head i = C.headAt ⟨i.1, Nat.lt_of_lt_of_le i.2 hp⟩ :=
  rfl

@[simp] theorem step1HeadChain_layer {n k : Nat} (C : Step1SelectedChain n k)
    {p : Nat} (hp : p ≤ n + 2) (i : Fin p) :
    (step1HeadChain C p hp).layer i = ⟨i.1, Nat.lt_of_lt_of_le i.2 hp⟩ :=
  rfl

@[simp] theorem step1HeadChain_selectedVar {n k : Nat} (C : Step1SelectedChain n k)
    {p : Nat} (hp : p ≤ n + 2) (i : Fin p) :
    (step1HeadChain C p hp).selectedVar i =
      C.selectedVar ⟨i.1, Nat.lt_of_lt_of_le i.2 hp⟩ :=
  rfl

/-- The selected head at tier `0` is the first head. -/
theorem step1HeadChain_head_zero {n k : Nat} (C : Step1SelectedChain n k)
    {p : Nat} (hp : p ≤ n + 2) (i : Fin p) (hi : i.1 = 0) :
    (step1HeadChain C p hp).head i = C.firstHead := by
  simp only [step1HeadChain_head]
  have hidx : (⟨i.1, Nat.lt_of_lt_of_le i.2 hp⟩ : Step1TierIndex n)
      = step1FirstTierIndex n := by
    apply Fin.ext; simp [step1FirstTierIndex, hi]
  rw [hidx, Step1SelectedChain.headAt_first]

/-- The selected head at a later tier `N + 1` is the chain's `N`-th later head. -/
theorem step1HeadChain_head_succ {n k : Nat} (C : Step1SelectedChain n k)
    {p : Nat} (hp : p ≤ n + 2) (i : Fin p) {N : Nat} (hi : i.1 = N + 1)
    (hN : N < n + 1) :
    (step1HeadChain C p hp).head i = C.laterHead ⟨N, hN⟩ := by
  simp only [step1HeadChain_head]
  have hidx : (⟨i.1, Nat.lt_of_lt_of_le i.2 hp⟩ : Step1TierIndex n)
      = Step1LaterTierIndex.toTier (⟨N, hN⟩ : Step1LaterTierIndex n) := by
    apply Fin.ext; simp [Step1LaterTierIndex.toTier, laterLayer, hi]
  rw [hidx, Step1SelectedChain.headAt_later]

/-! ## Selected value product and the cascade-product bridge -/

namespace HeadChain

/-- Matrix product `V_{p-1,a_{p-1}} ⋯ V_{0,a_0}` along the first `N` selected
layers of a head chain, with the empty product equal to the identity.  This is
the no-skip selected value product; the substitution dictionary lives in its
identification with `cascadeProduct` below. -/
noncomputable def selectedValueProduct {L k d p : Nat} (θ : Params L k d)
    (c : HeadChain L k p) : (N : Nat) → N ≤ p → Matrix (Fin d) (Fin d) ℝ
  | 0, _ => 1
  | N + 1, hN =>
      valueMatrix θ (c.layer ⟨N, hN⟩) (c.head ⟨N, hN⟩) *
        selectedValueProduct θ c N (Nat.le_of_succ_le hN)

@[simp] theorem selectedValueProduct_zero {L k d p : Nat} (θ : Params L k d)
    (c : HeadChain L k p) (h0 : 0 ≤ p) :
    selectedValueProduct θ c 0 h0 = 1 :=
  rfl

@[simp] theorem selectedValueProduct_succ {L k d p : Nat} (θ : Params L k d)
    (c : HeadChain L k p) {N : Nat} (hN : N + 1 ≤ p) :
    selectedValueProduct θ c (N + 1) hN =
      valueMatrix θ (c.layer ⟨N, hN⟩) (c.head ⟨N, hN⟩) *
        selectedValueProduct θ c N (Nat.le_of_succ_le hN) :=
  rfl

end HeadChain

/-- The selected value product of `step1HeadChain` does not depend on the chosen
chain length, as long as it exceeds the number of factors. -/
theorem step1HeadChain_selectedValueProduct_length_indep {n k d : Nat}
    (θ : Params (n + 2) k d) (C : Step1SelectedChain n k) :
    ∀ (N p p' : Nat) (hp : p ≤ n + 2) (hp' : p' ≤ n + 2)
      (hN : N ≤ p) (hN' : N ≤ p'),
      (step1HeadChain C p hp).selectedValueProduct θ N hN =
        (step1HeadChain C p' hp').selectedValueProduct θ N hN' := by
  intro N
  induction N with
  | zero => intro p p' hp hp' hN hN'; rfl
  | succ N ih =>
      intro p p' hp hp' hN hN'
      rw [HeadChain.selectedValueProduct_succ, HeadChain.selectedValueProduct_succ]
      congr 1
      exact ih p p' hp hp' (Nat.le_of_succ_le hN) (Nat.le_of_succ_le hN')

/-- The `N+1`-st selected value factor of `step1HeadChain` is the later-layer
value matrix `V_{N+1, laterHead N}` used by `cascadeProduct`. -/
theorem step1HeadChain_value_factor_succ {n k d : Nat}
    (θ : Params (n + 2) k d) (C : Step1SelectedChain n k) {p : Nat} {hp : p ≤ n + 2}
    {i : Fin p} {N : Nat} (hi : i.1 = N + 1) (hN : N < n + 1) :
    valueMatrix θ ((step1HeadChain C p hp).layer i) ((step1HeadChain C p hp).head i) =
      valueMatrix θ (laterLayer ⟨N, hN⟩) (C.laterHead ⟨N, hN⟩) := by
  rw [step1HeadChain_head_succ C hp i hi hN]
  congr 1
  apply Fin.ext
  simp [step1HeadChain_layer, laterLayer, hi]

/-- **Selected value product = cascade prefix product.**  For the first `N + 1`
selected layers this is the no-skip cascade product `cascadeProduct` after `N`
later layers (the substitution `C_ℓ := ∑_a V_{ℓa}` is already baked into the
value-only definitions on both sides). -/
theorem step1HeadChain_selectedValueProduct_eq_cascadeProduct {n k d : Nat}
    (θ : Params (n + 2) k d) (C : Step1SelectedChain n k) :
    ∀ (N : Nat) (hN : N ≤ n + 1),
      (step1HeadChain C (N + 1) (Nat.succ_le_succ hN)).selectedValueProduct
          θ (N + 1) le_rfl =
        cascadeProduct θ C.firstHead C.laterHead N := by
  intro N
  induction N with
  | zero =>
      intro _
      rw [HeadChain.selectedValueProduct_succ, HeadChain.selectedValueProduct_zero,
        Matrix.mul_one, cascadeProduct_zero]
      rw [step1HeadChain_head_zero C _ ⟨0, by omega⟩ rfl]
      rfl
  | succ N ih =>
      intro hN
      have hNlt : N < n + 1 := Nat.lt_of_succ_le hN
      rw [HeadChain.selectedValueProduct_succ,
        cascadeProduct_succ_of_lt θ C.firstHead C.laterHead hNlt]
      refine congrArg₂ (· * ·) ?_ ?_
      · -- head factor
        exact step1HeadChain_value_factor_succ θ C rfl hNlt
      · -- tail: shrink the chain length, then apply the induction hypothesis
        rw [step1HeadChain_selectedValueProduct_length_indep θ C (N + 1)
          (N + 2) (N + 1) (by omega) (by omega) (by omega) le_rfl]
        exact ih (Nat.le_of_succ_le hN)

/-- **Selected value product = cascade final product.** -/
theorem step1HeadChain_selectedValueProduct_eq_cascadeFinalProduct {n k d : Nat}
    (θ : Params (n + 2) k d) (C : Step1SelectedChain n k) :
    (step1HeadChain C (n + 2) le_rfl).selectedValueProduct θ (n + 2) le_rfl =
      cascadeFinalProduct θ C.firstHead C.laterHead := by
  have h := step1HeadChain_selectedValueProduct_eq_cascadeProduct θ C (n + 1) le_rfl
  rw [cascadeFinalProduct]
  exact h

/-- Residue-vector form of the value-product bridge: the selected value product
applied to a probe is the cascade residue vector. -/
theorem step1HeadChain_selectedValueProduct_mulVec_eq_cascadeResidueVector
    {n k d : Nat} (θ : Params (n + 2) k d) (C : Step1SelectedChain n k)
    (w : Vec d) :
    (step1HeadChain C (n + 2) le_rfl).selectedValueProduct θ (n + 2) le_rfl *ᵥ w =
      cascadeFinalProduct θ C.firstHead C.laterHead *ᵥ w := by
  rw [step1HeadChain_selectedValueProduct_eq_cascadeFinalProduct]

/-! ## Ignition quadratic bridges -/

theorem matrixBilin_sym_self {d : Nat}
    (M : Matrix (Fin d) (Fin d) ℝ) (w : Vec d) :
    matrixBilin (sym M) w w = matrixBilin M w w := by
  have hT : w ⬝ᵥ Mᵀ *ᵥ w = w ⬝ᵥ M *ᵥ w := by
    simpa using Matrix.dotProduct_transpose_mulVec (A := M) (x := w) (y := w)
  simp only [matrixBilin, KHead.matrixBilin, sym, KHead.sym, Matrix.smul_mulVec,
    dotProduct_smul, Matrix.add_mulVec, dotProduct_add, smul_eq_mul, hT]
  ring

theorem matrixBilin_transpose_mul_mul_self {d : Nat}
    (A P : Matrix (Fin d) (Fin d) ℝ) (w : Vec d) :
    matrixBilin (Pᵀ * A * P) w w =
      matrixBilin A (P *ᵥ w) (P *ᵥ w) := by
  calc
    matrixBilin (Pᵀ * A * P) w w
        = w ⬝ᵥ Pᵀ *ᵥ ((A * P) *ᵥ w) := by
          simp [matrixBilin, Matrix.mul_assoc, Matrix.mulVec_mulVec]
    _ = ((A * P) *ᵥ w) ⬝ᵥ P *ᵥ w := by
          exact Matrix.dotProduct_transpose_mulVec (A := P) (x := w)
            (y := (A * P) *ᵥ w)
    _ = matrixBilin A (P *ᵥ w) (P *ᵥ w) := by
          rw [dotProduct_comm]
          simp [matrixBilin, Matrix.mulVec_mulVec]

/-- **Ignition quadratic in terms of the cascade prefix product.**  The selected
ignition quadratic `wᵀ M_j^{h,χ} w` (the ignition-record coefficient) is the
later-layer attention bilinear form evaluated on the residue-product-transported
probe `P_j w`. -/
theorem step1IgnitionQuadratic_eq_cascadeProduct {n k d : Nat}
    (θ : Params (n + 2) k d) (h : Fin k) (χ : CascadeChain (n + 1) k)
    (j : Fin (n + 1)) (w : Vec d) :
    matrixBilin (cascadeIgnitionMatrix θ h χ j) w w =
      matrixBilin (attentionMatrix θ (laterLayer j) (χ j))
        (cascadeProduct θ h χ j.val *ᵥ w) (cascadeProduct θ h χ j.val *ᵥ w) := by
  rw [cascadeIgnitionMatrix, matrixBilin_sym_self, matrixBilin_transpose_mul_mul_self]

/-- **Ignition quadratic = selected value product.**  Same as
`step1IgnitionQuadratic_eq_cascadeProduct` but with the transported probe written
through the head chain's selected value product. -/
theorem step1IgnitionQuadratic_eq_selectedValueProduct {n k d : Nat}
    (θ : Params (n + 2) k d) (C : Step1SelectedChain n k) (j : Fin (n + 1))
    (w : Vec d) :
    matrixBilin (cascadeIgnitionMatrix θ C.firstHead C.laterHead j) w w =
      matrixBilin (attentionMatrix θ (laterLayer j) (C.laterHead j))
        ((step1HeadChain C (j.val + 1) (Nat.succ_le_succ (Nat.le_of_lt j.2))).selectedValueProduct
            θ (j.val + 1) le_rfl *ᵥ w)
        ((step1HeadChain C (j.val + 1) (Nat.succ_le_succ (Nat.le_of_lt j.2))).selectedValueProduct
            θ (j.val + 1) le_rfl *ᵥ w) := by
  rw [step1IgnitionQuadratic_eq_cascadeProduct,
    step1HeadChain_selectedValueProduct_eq_cascadeProduct θ C j.val (Nat.le_of_lt j.2)]

/-! ## Separated-probe nonvanishing facts -/

/-- Every separated factor is nonzero at a probe avoiding the separated vanishing
locus (i.e. one making the finite factor product nonzero). -/
theorem step1SeparatedFactorValue_ne_zero {n k d r : Nat}
    {theta theta' : Params (n + 2) k d} (H : Step1StandingHypotheses r theta theta')
    (w v : Vec d)
    (hsep : (∏ idx : Step1SeparatedFactorIndex n k,
        step1SeparatedFactorValue H w v idx) ≠ 0)
    (idx : Step1SeparatedFactorIndex n k) :
    step1SeparatedFactorValue H w v idx ≠ 0 :=
  fun hz => hsep (Finset.prod_eq_zero (Finset.mem_univ idx) hz)

/-- Every selected ignition quadratic is nonzero at a separated probe. -/
theorem separatedProbe_ignition_ne_zero {n k d r : Nat}
    {theta theta' : Params (n + 2) k d} (H : Step1StandingHypotheses r theta theta')
    (w v : Vec d)
    (hsep : (∏ idx : Step1SeparatedFactorIndex n k,
        step1SeparatedFactorValue H w v idx) ≠ 0)
    (h : Fin k) (j : Fin (n + 1)) :
    matrixBilin (cascadeIgnitionMatrix theta' h (H.targetCascadeData.head h).chain j) w w
      ≠ 0 := by
  have hfac := step1SeparatedFactorValue_ne_zero H w v hsep
    (Sum.inr (Sum.inl (Sum.inr (h, j))))
  simp only [step1SeparatedFactorValue] at hfac
  intro hz
  apply hfac
  rw [hz]; ring

/-- The selected final-residue vector is nonzero at a separated probe. -/
theorem separatedProbe_residue_ne_zero {n k d r : Nat}
    {theta theta' : Params (n + 2) k d} (H : Step1StandingHypotheses r theta theta')
    (w v : Vec d)
    (hsep : (∏ idx : Step1SeparatedFactorIndex n k,
        step1SeparatedFactorValue H w v idx) ≠ 0)
    (h : Fin k) :
    cascadeFinalProduct theta' h (H.targetCascadeData.head h).chain *ᵥ w ≠ 0 := by
  have hfac := step1SeparatedFactorValue_ne_zero H w v hsep
    (Sum.inr (Sum.inl (Sum.inl h)))
  simp only [step1SeparatedFactorValue] at hfac
  intro hz
  apply hfac
  rw [hz]; simp

/-- Some coordinate of the selected final-residue vector is nonzero at a
separated probe. -/
theorem separatedProbe_exists_residueCoordinate_ne_zero {n k d r : Nat}
    {theta theta' : Params (n + 2) k d} (H : Step1StandingHypotheses r theta theta')
    (w v : Vec d)
    (hsep : (∏ idx : Step1SeparatedFactorIndex n k,
        step1SeparatedFactorValue H w v idx) ≠ 0)
    (h : Fin k) :
    ∃ i : Fin d,
      (cascadeFinalProduct theta' h (H.targetCascadeData.head h).chain *ᵥ w) i ≠ 0 := by
  have hne := separatedProbe_residue_ne_zero H w v hsep h
  by_contra hnone
  apply hne
  funext i
  by_contra hi
  exact hnone ⟨i, hi⟩

/-! ## Canonical finite tower-member indices -/

/-- Residue coordinates that actually occur in the selected final residue vector. -/
abbrev Step1ResidueCoordinateIndex {n k d r : Nat}
    {theta theta' : Params (n + 2) k d} (H : Step1StandingHypotheses r theta theta')
    (w : Vec d) (h : Fin k) : Type :=
  {i : Fin d // (cascadeFinalProduct theta' h (H.targetCascadeData.head h).chain *ᵥ w) i ≠ 0}

noncomputable instance step1ResidueCoordinateIndex_fintype {n k d r : Nat}
    {theta theta' : Params (n + 2) k d} (H : Step1StandingHypotheses r theta theta')
    (w : Vec d) (h : Fin k) :
    Fintype (Step1ResidueCoordinateIndex H w h) := by
  classical
  infer_instance

theorem step1ResidueCoordinateIndex_nonempty {n k d r : Nat}
    {theta theta' : Params (n + 2) k d} (H : Step1StandingHypotheses r theta theta')
    (w v : Vec d)
    (hsep : (∏ idx : Step1SeparatedFactorIndex n k,
        step1SeparatedFactorValue H w v idx) ≠ 0)
    (h : Fin k) :
    Nonempty (Step1ResidueCoordinateIndex H w h) := by
  rcases separatedProbe_exists_residueCoordinate_ne_zero H w v hsep h with ⟨i, hi⟩
  exact ⟨⟨i, hi⟩⟩

/-- Canonical finite tower-member indices: one ignition member per later tier plus
one member per nonzero residue coordinate. -/
abbrev Step1TowerMemberIndex {n k d r : Nat}
    {theta theta' : Params (n + 2) k d} (H : Step1StandingHypotheses r theta theta')
    (w : Vec d) (h : Fin k) : Type :=
  Fin (n + 1) ⊕ Step1ResidueCoordinateIndex H w h

noncomputable instance step1TowerMemberIndex_fintype {n k d r : Nat}
    {theta theta' : Params (n + 2) k d} (H : Step1StandingHypotheses r theta theta')
    (w : Vec d) (h : Fin k) :
    Fintype (Step1TowerMemberIndex H w h) := by
  classical
  infer_instance

theorem step1TowerMemberIndex_nonempty {n k d r : Nat}
    {theta theta' : Params (n + 2) k d} (H : Step1StandingHypotheses r theta theta')
    (w v : Vec d)
    (hsep : (∏ idx : Step1SeparatedFactorIndex n k,
        step1SeparatedFactorValue H w v idx) ≠ 0)
    (h : Fin k) :
    Nonempty (Step1TowerMemberIndex H w h) :=
  ⟨Sum.inr (Classical.choice (step1ResidueCoordinateIndex_nonempty H w v hsep h))⟩

theorem step1TowerMemberIndex_card {n k d r : Nat}
    {theta theta' : Params (n + 2) k d} (H : Step1StandingHypotheses r theta theta')
    (w : Vec d) (h : Fin k) :
    Fintype.card (Step1TowerMemberIndex H w h) =
      (n + 1) + Fintype.card (Step1ResidueCoordinateIndex H w h) := by
  classical
  simp [Step1TowerMemberIndex]

/-- Number of selected variables used by a canonical member tower. -/
def step1TowerMemberChainLength {n k d r : Nat}
    {theta theta' : Params (n + 2) k d} (H : Step1StandingHypotheses r theta theta')
    (w : Vec d) (h : Fin k) (idx : Step1TowerMemberIndex H w h) : Nat :=
  match idx with
  | Sum.inl s => s.1
  | Sum.inr _ => n + 1

@[simp] theorem step1TowerMemberChainLength_ignition {n k d r : Nat}
    {theta theta' : Params (n + 2) k d} (H : Step1StandingHypotheses r theta theta')
    (w : Vec d) (h : Fin k) (s : Fin (n + 1)) :
    step1TowerMemberChainLength H w h (Sum.inl s) = s.1 :=
  rfl

@[simp] theorem step1TowerMemberChainLength_residue {n k d r : Nat}
    {theta theta' : Params (n + 2) k d} (H : Step1StandingHypotheses r theta theta')
    (w : Vec d) (h : Fin k) (i : Step1ResidueCoordinateIndex H w h) :
    step1TowerMemberChainLength H w h (Sum.inr i) = n + 1 :=
  rfl

theorem step1TowerMemberChainLength_le_depth {n k d r : Nat}
    {theta theta' : Params (n + 2) k d} (H : Step1StandingHypotheses r theta theta')
    (w : Vec d) (h : Fin k) (idx : Step1TowerMemberIndex H w h) :
    step1TowerMemberChainLength H w h idx ≤ n + 2 := by
  cases idx with
  | inl s => exact Nat.le_of_lt (Nat.lt_succ_of_lt s.2)
  | inr _ => exact Nat.le_succ _

/-- Selected head-chain prefix attached to a canonical finite-family member. -/
def step1TowerMemberHeadChain {n k d r : Nat}
    {theta theta' : Params (n + 2) k d} (H : Step1StandingHypotheses r theta theta')
    (w : Vec d) (h : Fin k) (idx : Step1TowerMemberIndex H w h) :
    HeadChain (n + 2) k (step1TowerMemberChainLength H w h idx) :=
  step1HeadChain (step1TargetSelectedChain H h)
    (step1TowerMemberChainLength H w h idx)
    (step1TowerMemberChainLength_le_depth H w h idx)

@[simp] theorem step1TowerMemberHeadChain_head {n k d r : Nat}
    {theta theta' : Params (n + 2) k d} (H : Step1StandingHypotheses r theta theta')
    (w : Vec d) (h : Fin k) (idx : Step1TowerMemberIndex H w h)
    (i : Fin (step1TowerMemberChainLength H w h idx)) :
    (step1TowerMemberHeadChain H w h idx).head i =
      (step1TargetSelectedChain H h).headAt
        ⟨i.1, Nat.lt_of_lt_of_le i.2 (step1TowerMemberChainLength_le_depth H w h idx)⟩ :=
  rfl

/-! ## Tower top constants and their nonvanishing -/

/-- Top constant for the ignition member attached to later tier `j`; equal to the
selected ignition-record coefficient. -/
noncomputable def step1IgnitionTopConstant {n k d r : Nat}
    {theta theta' : Params (n + 2) k d} (H : Step1StandingHypotheses r theta theta')
    (w : Vec d) (h : Fin k) (j : Fin (n + 1)) : ℝ :=
  matrixBilin (cascadeIgnitionMatrix theta' h (H.targetCascadeData.head h).chain j) w w

/-- Top constant for the residue member attached to a nonzero coordinate; equal to
the selected final-residue-record coefficient. -/
noncomputable def step1ResidueTopConstant {n k d r : Nat}
    {theta theta' : Params (n + 2) k d} (H : Step1StandingHypotheses r theta theta')
    (w : Vec d) (h : Fin k) (i : Step1ResidueCoordinateIndex H w h) : ℝ :=
  (cascadeFinalProduct theta' h (H.targetCascadeData.head h).chain *ᵥ w) i.1

@[simp] theorem step1IgnitionTopConstant_eq_record {n k d r : Nat}
    {theta theta' : Params (n + 2) k d} (H : Step1StandingHypotheses r theta theta')
    (w : Vec d) (h : Fin k) (j : Fin (n + 1)) :
    step1IgnitionTopConstant H w h j =
      (step1TargetIgnitionRecord H w h j).coefficient :=
  rfl

@[simp] theorem step1ResidueTopConstant_eq_record {n k d r : Nat}
    {theta theta' : Params (n + 2) k d} (H : Step1StandingHypotheses r theta theta')
    (w : Vec d) (h : Fin k) (i : Step1ResidueCoordinateIndex H w h) :
    step1ResidueTopConstant H w h i =
      (step1TargetResidueRecord H w h i.1).coefficient :=
  rfl

/-- Nonvanishing of the ignition top constant at a separated probe. -/
theorem step1IgnitionTopConstant_ne_zero {n k d r : Nat}
    {theta theta' : Params (n + 2) k d} (H : Step1StandingHypotheses r theta theta')
    (w v : Vec d)
    (hsep : (∏ idx : Step1SeparatedFactorIndex n k,
        step1SeparatedFactorValue H w v idx) ≠ 0)
    (h : Fin k) (j : Fin (n + 1)) :
    step1IgnitionTopConstant H w h j ≠ 0 :=
  separatedProbe_ignition_ne_zero H w v hsep h j

/-- Nonvanishing of the residue top constant: it is exactly the nonzero coordinate
witnessed by the residue-coordinate index. -/
theorem step1ResidueTopConstant_ne_zero {n k d r : Nat}
    {theta theta' : Params (n + 2) k d} (H : Step1StandingHypotheses r theta theta')
    (w : Vec d) (h : Fin k) (i : Step1ResidueCoordinateIndex H w h) :
    step1ResidueTopConstant H w h i ≠ 0 :=
  i.2

/-- **Residue top constant = selected value product.**  The residue top constant is
the corresponding coordinate of the head chain's selected value product applied to
the probe. -/
theorem step1ResidueTopConstant_eq_selectedValueProduct {n k d r : Nat}
    {theta theta' : Params (n + 2) k d} (H : Step1StandingHypotheses r theta theta')
    (w : Vec d) (h : Fin k) (i : Step1ResidueCoordinateIndex H w h) :
    step1ResidueTopConstant H w h i =
      ((step1HeadChain (step1TargetSelectedChain H h) (n + 2) le_rfl).selectedValueProduct
          theta' (n + 2) le_rfl *ᵥ w) i.1 := by
  rw [step1ResidueTopConstant,
    step1HeadChain_selectedValueProduct_mulVec_eq_cascadeResidueVector]
  rfl

/-- **Ignition top constant = selected value product.**  The ignition top constant
is the later-layer attention bilinear form on the cascade-product-transported
probe. -/
theorem step1IgnitionTopConstant_eq_selectedValueProduct {n k d r : Nat}
    {theta theta' : Params (n + 2) k d} (H : Step1StandingHypotheses r theta theta')
    (w : Vec d) (h : Fin k) (j : Fin (n + 1)) :
    step1IgnitionTopConstant H w h j =
      matrixBilin
        (attentionMatrix theta' (laterLayer j) ((H.targetCascadeData.head h).chain j))
        (cascadeProduct theta' h (H.targetCascadeData.head h).chain j.val *ᵥ w)
        (cascadeProduct theta' h (H.targetCascadeData.head h).chain j.val *ᵥ w) := by
  rw [step1IgnitionTopConstant, step1IgnitionQuadratic_eq_cascadeProduct]

/-! ## Canonical total-block ignition tower (NS103/NS105 bridge) -/

/-- The coefficient of the square of the currently selected gate in the next
selected level slope. -/
noncomputable def step1CanonicalIgnitionPoly {n k d r : Nat}
    {theta theta' : Params (n + 2) k d} (H : Step1StandingHypotheses r theta theta')
    (w v : Vec d) (h : Fin k) (j : Step1LaterTierIndex n) :
    FormalPoly (n + 2) k :=
  let C := step1TargetSelectedChain H h
  let cur : Step1TierIndex n := ⟨j.1, by omega⟩
  coeffOfVar (C.selectedVar cur) 2
    (formalSlope theta' w v j.toTier (C.headAt j.toTier))

theorem step1CanonicalIgnitionPoly_blockTotal {n k d r : Nat}
    {theta theta' : Params (n + 2) k d} (H : Step1StandingHypotheses r theta theta')
    (w v : Vec d) (h : Fin k) (j : Step1LaterTierIndex n) :
    BlockTotalDegreeLE 2 (step1CanonicalIgnitionPoly H w v h j) := by
  exact coeffOfVar_blockTotalDegreeLE _ 2
    (formalSlope_blockTotalDegree_two theta' w v j.toTier
      ((step1TargetSelectedChain H h).headAt j.toTier))

theorem step1CanonicalIgnitionPoly_support {n k d r : Nat}
    {theta theta' : Params (n + 2) k d} (H : Step1StandingHypotheses r theta theta')
    (w v : Vec d) (h : Fin k) (j : Step1LaterTierIndex n) :
    PolynomialInLayersLT j.1 (step1CanonicalIgnitionPoly H w v h j) := by
  let C := step1TargetSelectedChain H h
  let cur : Step1TierIndex n := ⟨j.1, by omega⟩
  apply coeffOfVar_top_supportBefore (C.selectedVar cur) (n := j.1)
  · rfl
  · exact formalSlope_blockTotalDegree_two theta' w v j.toTier (C.headAt j.toTier)
  · intro m hm x hx
    exact formalSlope_supportBefore theta' w v j.toTier (C.headAt j.toTier)
      m hm x (by
        change j.1 + 1 ≤ x.1.1
        omega)

/-- Canonical dominance tower for one selected ignition coefficient. -/
noncomputable def step1CanonicalIgnitionTower {n k d r : Nat}
    {theta theta' : Params (n + 2) k d} (H : Step1StandingHypotheses r theta theta')
    (w v : Vec d) (h : Fin k) (j : Step1LaterTierIndex n) :
    DominanceTowerData
      (step1HeadChain (step1TargetSelectedChain H h) j.1 (by omega))
      (step1CanonicalIgnitionPoly H w v h j) :=
  genericTowerData (step1HeadChain (step1TargetSelectedChain H h) j.1 (by omega)) 2
    (step1CanonicalIgnitionPoly H w v h j)

theorem step1CanonicalIgnitionTower_degree_pos {n k d r : Nat}
    {theta theta' : Params (n + 2) k d} (H : Step1StandingHypotheses r theta theta')
    (w v : Vec d) (h : Fin k) (j : Step1LaterTierIndex n) :
    ∀ i, 1 ≤ (step1CanonicalIgnitionTower H w v h j).degree i :=
  genericTower_degree_pos _ 2 _ (by norm_num)

theorem step1CanonicalIgnitionTower_topConstant {n k d r : Nat}
    {theta theta' : Params (n + 2) k d} (H : Step1StandingHypotheses r theta theta')
    (w v : Vec d) (h : Fin k) (j : Step1LaterTierIndex n) :
    CanonicalTowerTopConstant (step1CanonicalIgnitionTower H w v h j) :=
  genericTower_topConstant _ 2 _
    (step1CanonicalIgnitionPoly_support H w v h j)
    (step1CanonicalIgnitionPoly_blockTotal H w v h j)

theorem step1CanonicalIgnitionTower_finalCoeff {n k d r : Nat}
    {theta theta' : Params (n + 2) k d} (H : Step1StandingHypotheses r theta theta')
    (w v : Vec d) (h : Fin k) (j : Step1LaterTierIndex n) :
    CanonicalTowerFinalCoeff (step1CanonicalIgnitionTower H w v h j) :=
  genericTower_finalCoeff _ 2 _

theorem step1CanonicalIgnitionTower_evalRecurrence {n k d r : Nat}
    {theta theta' : Params (n + 2) k d} (H : Step1StandingHypotheses r theta theta')
    (w v : Vec d) (h : Fin k) (j : Step1LaterTierIndex n) :
    CanonicalTowerEvalRecurrence (step1CanonicalIgnitionTower H w v h j) :=
  genericTower_evalRecurrence _ 2 _
    (step1CanonicalIgnitionPoly_blockTotal H w v h j)

/-! ## Selected-monomial stream recursion -/

noncomputable def step1SelectedMonomial {n k : Nat} (C : Step1SelectedChain n k)
    (N : Nat) (hN : N ≤ n + 2) : FormalVar (n + 2) k →₀ Nat :=
  ∑ i : Fin N, Finsupp.single
    ((step1HeadChain C (n + 2) le_rfl).selectedVar (Fin.castLE hN i)) 1

noncomputable def step1SelectedValuePrefix {n k d : Nat} (theta : Params (n + 2) k d)
    (C : Step1SelectedChain n k) (N : Nat) (hN : N ≤ n + 2) :
    Matrix (Fin d) (Fin d) ℝ :=
  (step1HeadChain C (n + 2) le_rfl).selectedValueProduct theta N hN

theorem step1SelectedMonomial_succ {n k : Nat} (C : Step1SelectedChain n k)
    (N : Nat) (hN : N + 1 ≤ n + 2) :
    step1SelectedMonomial C (N + 1) hN =
      step1SelectedMonomial C N (by omega) +
        Finsupp.single (C.selectedVar ⟨N, by omega⟩) 1 := by
  rw [step1SelectedMonomial, step1SelectedMonomial, Fin.sum_univ_castSucc]
  congr 2

theorem step1SelectedValuePrefix_succ {n k d : Nat} (theta : Params (n + 2) k d)
    (C : Step1SelectedChain n k) (N : Nat) (hN : N + 1 ≤ n + 2) :
    step1SelectedValuePrefix theta C (N + 1) hN =
      valueMatrix theta ⟨N, by omega⟩ (C.headAt ⟨N, by omega⟩) *
        step1SelectedValuePrefix theta C N (by omega) := by
  rw [step1SelectedValuePrefix, HeadChain.selectedValueProduct_succ]
  rfl

theorem coeff_realMatrix_mulVec_ns {n k d : Nat} {M : Matrix (Fin d) (Fin d) ℝ}
    {g : FormalVec (n + 2) k d} (i : Fin d) (u : FormalVar (n + 2) k →₀ Nat) :
    ((realMatrixToFormal M *ᵥ g) i).coeff u = ∑ j : Fin d, M i j * (g j).coeff u := by
  classical
  rw [Matrix.mulVec, dotProduct, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [realMatrixToFormal_apply]
  show (formalConst (M i j) * g j).coeff u = _
  rw [formalConst, MvPolynomial.coeff_C_mul]

theorem step1SelectedMonomial_apply_layer {n k : Nat} (C : Step1SelectedChain n k)
    (N : Nat) (hN : N + 1 ≤ n + 2) (a : Fin k) :
    step1SelectedMonomial C (N + 1) hN (⟨N, by omega⟩, a) =
      if a = C.headAt ⟨N, by omega⟩ then 1 else 0 := by
  rw [step1SelectedMonomial_succ, Finsupp.add_apply]
  have hzero : step1SelectedMonomial C N (by omega) (⟨N, by omega⟩, a) = 0 := by
    rw [step1SelectedMonomial, Finsupp.finset_sum_apply]
    apply Finset.sum_eq_zero
    intro i _
    rw [Finsupp.single_apply, if_neg]
    intro heq
    have := congrArg (fun x : FormalVar (n + 2) k => x.1.1) heq
    simp only [step1HeadChain_selectedVar, Step1SelectedChain.selectedVar,
      Fin.castLE] at this
    omega
  rw [hzero, zero_add, Finsupp.single_apply]
  have hpair :
      (C.selectedVar ⟨N, by omega⟩ = (⟨N, by omega⟩, a)) ↔
        a = C.headAt ⟨N, by omega⟩ := by
    simp only [Step1SelectedChain.selectedVar, Prod.mk.injEq, true_and]
    exact eq_comm
  exact if_congr hpair rfl rfl

theorem step1SelectedMonomial_mem_support {n k : Nat} (C : Step1SelectedChain n k)
    (N : Nat) (hN : N + 1 ≤ n + 2) (a : Fin k) :
    (⟨N, by omega⟩, a) ∈ (step1SelectedMonomial C (N + 1) hN).support ↔
      a = C.headAt ⟨N, by omega⟩ := by
  rw [Finsupp.mem_support_iff, step1SelectedMonomial_apply_layer]
  by_cases ha : a = C.headAt ⟨N, by omega⟩ <;> simp [ha]

theorem step1SelectedMonomial_succ_sub {n k : Nat} (C : Step1SelectedChain n k)
    (N : Nat) (hN : N + 1 ≤ n + 2) :
    step1SelectedMonomial C (N + 1) hN -
        Finsupp.single (C.selectedVar ⟨N, by omega⟩) 1 =
      step1SelectedMonomial C N (by omega) := by
  rw [step1SelectedMonomial_succ]
  simp

theorem formalW_succ_vec_ns {n k d : Nat} (theta : Params (n + 2) k d)
    (w v : Vec d) (N : Nat) (hN : N + 1 ≤ n + 2) :
    formalW theta w v (N + 1) hN =
      (formalCollapseMatrix theta ⟨N, by omega⟩ -
        formalGatedValueSum theta ⟨N, by omega⟩) *ᵥ formalW theta w v N (by omega) := by
  show (formalPoint theta w v (N + 1) hN).1 = _
  rw [formalPoint_succ]
  rfl

theorem formalV_succ_vec_ns {n k d : Nat} (theta : Params (n + 2) k d)
    (w v : Vec d) (N : Nat) (hN : N + 1 ≤ n + 2) :
    formalV theta w v (N + 1) hN =
      formalCollapseMatrix theta ⟨N, by omega⟩ *ᵥ formalV theta w v N (by omega) +
        formalGatedValueSum theta ⟨N, by omega⟩ *ᵥ formalW theta w v N (by omega) := by
  show (formalPoint theta w v (N + 1) hN).2 = _
  rw [formalPoint_succ]
  rfl

/-- The selected coefficient of the no-skip contrast stream is precisely the
signed product of the selected value matrices. -/
theorem formalW_selectedCoeff_ns {n k d : Nat} (theta : Params (n + 2) k d)
    (C : Step1SelectedChain n k) (w v : Vec d) :
    ∀ (N : Nat) (hN : N ≤ n + 2) (i : Fin d),
      (formalW theta w v N hN i).coeff (step1SelectedMonomial C N hN) =
        (-1 : ℝ) ^ N * (step1SelectedValuePrefix theta C N hN *ᵥ w) i := by
  intro N
  induction N with
  | zero =>
      intro hN i
      rw [step1SelectedMonomial]
      simp only [Finset.univ_eq_empty, Finset.sum_empty, formalW_zero,
        realVecToFormal_apply, formalConst, MvPolynomial.coeff_zero_C, pow_zero, one_mul]
      rw [step1SelectedValuePrefix]
      simp [HeadChain.selectedValueProduct, Matrix.one_mulVec]
  | succ N ih =>
      intro hN i
      rw [formalW_succ_vec_ns, Matrix.sub_mulVec, Pi.sub_apply, MvPolynomial.coeff_sub]
      have hcollapse :
          ((formalCollapseMatrix theta ⟨N, by omega⟩ *ᵥ formalW theta w v N (by omega)) i).coeff
              (step1SelectedMonomial C (N + 1) hN) = 0 := by
        rw [formalCollapseMatrix, coeff_realMatrix_mulVec_ns]
        apply Finset.sum_eq_zero
        intro q _
        have hzero :
            (formalW theta w v N (by omega) q).coeff
                (step1SelectedMonomial C (N + 1) hN) = 0 := by
          refine KHead.Step1.coeff_eq_zero_of_layerLT
            (((formalPoint_layerBoundedBlockAffine theta w v N (by omega)).1 q).support_lt)
            (x := (⟨N, by omega⟩, C.headAt ⟨N, by omega⟩)) (by simp) ?_
          rw [step1SelectedMonomial_apply_layer]
          simp
        rw [hzero, mul_zero]
      rw [hcollapse, zero_sub]
      have hD :
          ((formalGatedValueSum theta ⟨N, by omega⟩ *ᵥ formalW theta w v N (by omega)) i).coeff
              (step1SelectedMonomial C (N + 1) hN) =
            (-1 : ℝ) ^ N *
              (step1SelectedValuePrefix theta C (N + 1) hN *ᵥ w) i := by
        have hgvs :
            (formalGatedValueSum theta ⟨N, by omega⟩ *ᵥ formalW theta w v N (by omega)) i =
              ∑ a : Fin k, formalGate ⟨N, by omega⟩ a *
                (formalValueMatrix theta ⟨N, by omega⟩ a *ᵥ
                  formalW theta w v N (by omega)) i := by
          rw [formalGatedValueSum, Matrix.sum_mulVec, Finset.sum_apply]
          apply Finset.sum_congr rfl
          intro a _
          rw [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
        rw [hgvs, MvPolynomial.coeff_sum]
        rw [Finset.sum_eq_single (C.headAt ⟨N, by omega⟩)]
        · rw [formalGate, MvPolynomial.coeff_X_mul',
            if_pos ((step1SelectedMonomial_mem_support C N hN _).mpr rfl),
            formalValueMatrix]
          have hsub :
              step1SelectedMonomial C (N + 1) hN -
                  Finsupp.single (⟨N, by omega⟩, C.headAt ⟨N, by omega⟩) 1 =
                step1SelectedMonomial C N (by omega) := by
            simpa [Step1SelectedChain.selectedVar] using
              step1SelectedMonomial_succ_sub C N hN
          rw [hsub, coeff_realMatrix_mulVec_ns, step1SelectedValuePrefix_succ,
            ← Matrix.mulVec_mulVec]
          rw [show ((valueMatrix theta ⟨N, by omega⟩ (C.headAt ⟨N, by omega⟩)) *ᵥ
              (step1SelectedValuePrefix theta C N (by omega) *ᵥ w)) i =
                ∑ q : Fin d, valueMatrix theta ⟨N, by omega⟩
                    (C.headAt ⟨N, by omega⟩) i q *
                  (step1SelectedValuePrefix theta C N (by omega) *ᵥ w) q from rfl,
            Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q _
          rw [ih (by omega) q]
          ring
        · intro a _ hane
          rw [formalGate, MvPolynomial.coeff_X_mul',
            if_neg (fun hmem => hane ((step1SelectedMonomial_mem_support C N hN a).mp hmem))]
        · intro hnot
          exact absurd (Finset.mem_univ _) hnot
      rw [hD, pow_succ]
      ring

theorem formalGatedValueSum_selectedCoeff_ns {n k d : Nat}
    (theta : Params (n + 2) k d) (C : Step1SelectedChain n k) (w v : Vec d)
    (N : Nat) (hN : N + 1 ≤ n + 2) (i : Fin d) :
    ((formalGatedValueSum theta ⟨N, by omega⟩ *ᵥ formalW theta w v N (by omega)) i).coeff
        (step1SelectedMonomial C (N + 1) hN) =
      (-1 : ℝ) ^ N *
        (step1SelectedValuePrefix theta C (N + 1) hN *ᵥ w) i := by
  have hgvs :
      (formalGatedValueSum theta ⟨N, by omega⟩ *ᵥ formalW theta w v N (by omega)) i =
        ∑ a : Fin k, formalGate ⟨N, by omega⟩ a *
          (formalValueMatrix theta ⟨N, by omega⟩ a *ᵥ formalW theta w v N (by omega)) i := by
    rw [formalGatedValueSum, Matrix.sum_mulVec, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro a _
    rw [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
  rw [hgvs, MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single (C.headAt ⟨N, by omega⟩)]
  · rw [formalGate, MvPolynomial.coeff_X_mul',
      if_pos ((step1SelectedMonomial_mem_support C N hN _).mpr rfl),
      formalValueMatrix]
    have hsub :
        step1SelectedMonomial C (N + 1) hN -
            Finsupp.single (⟨N, by omega⟩, C.headAt ⟨N, by omega⟩) 1 =
          step1SelectedMonomial C N (by omega) := by
      simpa [Step1SelectedChain.selectedVar] using
        step1SelectedMonomial_succ_sub C N hN
    rw [hsub, coeff_realMatrix_mulVec_ns,
      step1SelectedValuePrefix_succ, ← Matrix.mulVec_mulVec]
    rw [show ((valueMatrix theta ⟨N, by omega⟩ (C.headAt ⟨N, by omega⟩)) *ᵥ
        (step1SelectedValuePrefix theta C N (by omega) *ᵥ w)) i =
          ∑ q : Fin d, valueMatrix theta ⟨N, by omega⟩
              (C.headAt ⟨N, by omega⟩) i q *
            (step1SelectedValuePrefix theta C N (by omega) *ᵥ w) q from rfl,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    rw [formalW_selectedCoeff_ns theta C w v N (by omega) q]
    ring
  · intro a _ hane
    rw [formalGate, MvPolynomial.coeff_X_mul',
      if_neg (fun hmem => hane ((step1SelectedMonomial_mem_support C N hN a).mp hmem))]
  · intro hnot
    exact absurd (Finset.mem_univ _) hnot

theorem formalV_selectedCoeff_succ_ns {n k d : Nat}
    (theta : Params (n + 2) k d) (C : Step1SelectedChain n k) (w v : Vec d)
    (N : Nat) (hN : N + 1 ≤ n + 2) (i : Fin d) :
    (formalV theta w v (N + 1) hN i).coeff (step1SelectedMonomial C (N + 1) hN) =
      (-1 : ℝ) ^ N *
        (step1SelectedValuePrefix theta C (N + 1) hN *ᵥ w) i := by
  rw [formalV_succ_vec_ns, Pi.add_apply, MvPolynomial.coeff_add]
  have hcollapse :
      ((formalCollapseMatrix theta ⟨N, by omega⟩ *ᵥ formalV theta w v N (by omega)) i).coeff
          (step1SelectedMonomial C (N + 1) hN) = 0 := by
    rw [formalCollapseMatrix, coeff_realMatrix_mulVec_ns]
    apply Finset.sum_eq_zero
    intro q _
    have hzero :
        (formalV theta w v N (by omega) q).coeff
            (step1SelectedMonomial C (N + 1) hN) = 0 := by
      refine KHead.Step1.coeff_eq_zero_of_layerLT
        (((formalPoint_layerBoundedBlockAffine theta w v N (by omega)).2 q).support_lt)
        (x := (⟨N, by omega⟩, C.headAt ⟨N, by omega⟩)) (by simp) ?_
      rw [step1SelectedMonomial_apply_layer]
      simp
    rw [hzero, mul_zero]
  rw [hcollapse, zero_add, formalGatedValueSum_selectedCoeff_ns]

/-- Bilinear two-factor extraction from the genuine no-skip total-block bound. -/
theorem coeff_mul_double_ns {L k : Nat} (u : FormalVar L k →₀ Nat)
    {P Q : FormalPoly L k} (hP : BlockTotalDegreeLE 1 P)
    (hQ : BlockTotalDegreeLE 1 Q) :
    (P * Q).coeff (u + u) = P.coeff u * Q.coeff u := by
  classical
  rw [MvPolynomial.coeff_mul]
  have hmem : (u, u) ∈ Finset.antidiagonal (u + u) := by
    rw [Finset.mem_antidiagonal]
  refine (Finset.sum_eq_single_of_mem (u, u) hmem ?_).trans rfl
  intro b hb hbne
  rw [Finset.mem_antidiagonal] at hb
  by_cases hP0 : P.coeff b.1 = 0
  · rw [hP0, zero_mul]
  · by_cases hQ0 : Q.coeff b.2 = 0
    · rw [hQ0, mul_zero]
    · exfalso
      apply hbne
      have hb1 := MvPolynomial.mem_support_iff.mpr hP0
      have hb2 := MvPolynomial.mem_support_iff.mpr hQ0
      have hleP : ∀ x, b.1 x ≤ 1 := by
        intro x
        have hs : b.1 x ≤ ∑ a : Fin k, b.1 (x.1, a) := by
          simpa using (Finset.single_le_sum
            (fun a (_ha : a ∈ (Finset.univ : Finset (Fin k))) => Nat.zero_le (b.1 (x.1, a)))
            (Finset.mem_univ x.2))
        exact hs.trans (hP b.1 hb1 x.1)
      have hleQ : ∀ x, b.2 x ≤ 1 := by
        intro x
        have hs : b.2 x ≤ ∑ a : Fin k, b.2 (x.1, a) := by
          simpa using (Finset.single_le_sum
            (fun a (_ha : a ∈ (Finset.univ : Finset (Fin k))) => Nat.zero_le (b.2 (x.1, a)))
            (Finset.mem_univ x.2))
        exact hs.trans (hQ b.2 hb2 x.1)
      have hb1eq : b.1 = u := by
        ext x
        have hsum := Finsupp.ext_iff.mp hb x
        simp only [Finsupp.add_apply] at hsum
        have := hleP x
        have := hleQ x
        omega
      have hb2eq : b.2 = u := by
        ext x
        have hsum := Finsupp.ext_iff.mp hb x
        simp only [Finsupp.add_apply] at hsum
        have := hleP x
        have := hleQ x
        omega
      rw [Prod.ext_iff]
      exact ⟨hb1eq, hb2eq⟩

theorem step1SelectedValuePrefix_eq_short {n k d : Nat}
    (theta : Params (n + 2) k d) (C : Step1SelectedChain n k)
    (N : Nat) (hN : N ≤ n + 2) :
    step1SelectedValuePrefix theta C N hN =
      (step1HeadChain C N hN).selectedValueProduct theta N le_rfl := by
  unfold step1SelectedValuePrefix
  have hprefix : ∀ (P q : Nat) (hP : P ≤ n + 2) (hq : q ≤ P),
      (step1HeadChain C P hP).selectedValueProduct theta q hq =
        (step1HeadChain C q (Nat.le_trans hq hP)).selectedValueProduct theta q le_rfl := by
    intro P q
    revert P
    induction q with
    | zero => intro P hP hq; rfl
    | succ q ih =>
        intro P hP hq
        rw [HeadChain.selectedValueProduct_succ, HeadChain.selectedValueProduct_succ]
        have hqP : q ≤ P := Nat.le_trans (Nat.le_succ q) hq
        rw [ih P hP hqP, ih (q + 1) (Nat.le_trans hq hP) (Nat.le_succ q)]
        simp [HeadChain.layer, step1HeadChain]
  exact hprefix (n + 2) N le_rfl hN

theorem step1SelectedMonomial_apply_zero_of_ge {n k : Nat}
    (C : Step1SelectedChain n k) (N : Nat) (hN : N ≤ n + 2)
    (l : Fin (n + 2)) (a : Fin k) (hl : N ≤ l.1) :
    step1SelectedMonomial C N hN (l, a) = 0 := by
  rw [step1SelectedMonomial, Finsupp.finset_sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [Finsupp.single_apply, if_neg]
  intro heq
  have := congrArg (fun x : FormalVar (n + 2) k => x.1.1) heq
  simp only [step1HeadChain_selectedVar, Step1SelectedChain.selectedVar,
    Fin.castLE] at this
  omega

theorem step1HeadChain_exp2_eq_selectedMonomial {n k : Nat}
    (C : Step1SelectedChain n k) (N : Nat) (hN : N ≤ n + 2) :
    (∑ i : Fin N, Finsupp.single ((step1HeadChain C N hN).selectedVar i) 2) =
      step1SelectedMonomial C N hN + step1SelectedMonomial C N hN := by
  rw [step1SelectedMonomial, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finsupp.single_add]
  congr 1

/-- The degree-one selected exponent used by the canonical residue tower is
the selected monomial of the same chain prefix. -/
theorem step1HeadChain_exp_eq_selectedMonomial {n k : Nat}
    (C : Step1SelectedChain n k) (N : Nat) (hN : N ≤ n + 2) :
    (∑ i : Fin N, Finsupp.single ((step1HeadChain C N hN).selectedVar i) 1) =
      step1SelectedMonomial C N hN := by
  rw [step1SelectedMonomial]
  apply Finset.sum_congr rfl
  intro q _
  rw [step1HeadChain_selectedVar]
  congr 2

/-- The doubled selected coefficient of a later no-skip slope is the negative
attention quadratic on the selected value-prefix transport. -/
theorem formalSlope_selectedCoeff_ns {n k d : Nat}
    (theta : Params (n + 2) k d) (C : Step1SelectedChain n k)
    (w v : Vec d) (j : Step1LaterTierIndex n) :
    (formalSlope theta w v j.toTier (C.headAt j.toTier)).coeff
        (step1SelectedMonomial C (j.1 + 1) (by omega) +
          step1SelectedMonomial C (j.1 + 1) (by omega)) =
      -matrixBilin (attentionMatrix theta j.toTier (C.headAt j.toTier))
        (step1SelectedValuePrefix theta C (j.1 + 1) (by omega) *ᵥ w)
        (step1SelectedValuePrefix theta C (j.1 + 1) (by omega) *ᵥ w) := by
  set A := attentionMatrix theta j.toTier (C.headAt j.toTier) with hA
  set V := formalV theta w v (j.1 + 1) (by omega) with hV
  set u := step1SelectedMonomial C (j.1 + 1) (by omega) with hu
  set sv := step1SelectedValuePrefix theta C (j.1 + 1) (by omega) *ᵥ w with hsv
  have hsign : (-1 : ℝ) ^ (j.1 + 1) * (-1) ^ j.1 = -1 := by
    rw [← pow_add, show j.1 + 1 + j.1 = 2 * j.1 + 1 by ring, pow_succ, pow_mul]
    norm_num
  rw [formalSlope, formalBilin, dotProduct, MvPolynomial.coeff_sum]
  have hQ : ∀ a : Fin d, BlockTotalDegreeLE 1 ((realMatrixToFormal A *ᵥ V) a) := by
    intro a m hm l
    have hb := KHead.layerBounded_realMatrixToFormal_mulVec A
      (fun b => (formalPoint_layerBoundedBlockAffine theta w v (j.1 + 1) (by omega)).2 b) a
    exact (hb.block m hm).block_sum_le_one l
  have hsummand : ∀ a : Fin d,
      (formalW theta w v (j.1 + 1) (by omega) a *
          (realMatrixToFormal A *ᵥ V) a).coeff (u + u) =
        ((-1 : ℝ) ^ (j.1 + 1) * sv a) *
          ((-1 : ℝ) ^ j.1 * (A *ᵥ sv) a) := by
    intro a
    rw [coeff_mul_double_ns u
      (formalW_blockTotalDegree_one theta w v (j.1 + 1) (by omega) a) (hQ a),
      formalW_selectedCoeff_ns theta C w v (j.1 + 1) (by omega) a]
    congr 1
    rw [coeff_realMatrix_mulVec_ns,
      show (A *ᵥ sv) a = ∑ b : Fin d, A a b * sv b from rfl,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [formalV_selectedCoeff_succ_ns theta C w v j.1 (by omega) b]
    ring
  change (∑ x : Fin d,
      (formalW theta w v (j.1 + 1) (by omega) x *
        (realMatrixToFormal A *ᵥ V) x).coeff (u + u)) =
    -matrixBilin A sv sv
  rw [Finset.sum_congr rfl (fun a _ => hsummand a)]
  change (∑ a : Fin d,
      (-1 : ℝ) ^ (j.1 + 1) * sv a * ((-1 : ℝ) ^ j.1 * (A *ᵥ sv) a)) =
    -(∑ a : Fin d, sv a * (A *ᵥ sv) a)
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  linear_combination (sv a * (A *ᵥ sv) a) * hsign

/-- The genuine canonical ignition tower has the expected nonzero signed
cascade coefficient as its top constant. -/
theorem step1CanonicalIgnitionTower_topConstant_eq {n k d r : Nat}
    {theta theta' : Params (n + 2) k d} (H : Step1StandingHypotheses r theta theta')
    (w v : Vec d) (h : Fin k) (j : Step1LaterTierIndex n) :
    (step1CanonicalIgnitionTower H w v h j).topConstant =
      -step1IgnitionTopConstant H w h j := by
  let C := step1TargetSelectedChain H h
  show (topLeadingCoeff (step1HeadChain C j.1 (by omega)) 2
      (step1CanonicalIgnitionPoly H w v h j) j.1).coeff 0 = _
  rw [topLeadingCoeff_coeff_zero,
    step1HeadChain_exp2_eq_selectedMonomial C j.1 (by omega),
    step1CanonicalIgnitionPoly, coeffOfVar_coeff]
  have hcond :
      (step1SelectedMonomial C j.1 (by omega) +
          step1SelectedMonomial C j.1 (by omega))
        (C.selectedVar ⟨j.1, by omega⟩) = 0 := by
    rw [Finsupp.add_apply]
    simp only [Step1SelectedChain.selectedVar]
    rw [step1SelectedMonomial_apply_zero_of_ge C j.1 (by omega)
        ⟨j.1, by omega⟩ _ (le_refl _)]
  rw [if_pos hcond]
  have hexp :
      (step1SelectedMonomial C j.1 (by omega) +
          step1SelectedMonomial C j.1 (by omega)) +
          Finsupp.single (C.selectedVar ⟨j.1, by omega⟩) 2 =
        step1SelectedMonomial C (j.1 + 1) (by omega) +
          step1SelectedMonomial C (j.1 + 1) (by omega) := by
    ext x
    have hs := congrArg (fun u => u x)
      (step1SelectedMonomial_succ C j.1 (by omega))
    simp only [Finsupp.add_apply] at hs ⊢
    rw [hs]
    simp only [Finsupp.single_apply]
    split <;> omega
  rw [hexp, formalSlope_selectedCoeff_ns theta' C w v j]
  rw [step1SelectedValuePrefix_eq_short]
  simp only [Step1SelectedChain.headAt_later]
  rw [show j.toTier = laterLayer j from rfl]
  rw [← step1IgnitionQuadratic_eq_selectedValueProduct theta' C j w]
  change -matrixBilin
      (cascadeIgnitionMatrix theta' h (H.targetCascadeData.head h).chain j) w w =
    -matrixBilin (cascadeIgnitionMatrix theta' h
      (H.targetCascadeData.head h).chain j) w w
  rfl

theorem step1CanonicalIgnitionTower_topConstant_ne_zero {n k d r : Nat}
    {theta theta' : Params (n + 2) k d} (H : Step1StandingHypotheses r theta theta')
    (w v : Vec d)
    (hsep : (∏ idx : Step1SeparatedFactorIndex n k,
      step1SeparatedFactorValue H w v idx) ≠ 0)
    (h : Fin k) (j : Step1LaterTierIndex n) :
    (step1CanonicalIgnitionTower H w v h j).topConstant ≠ 0 := by
  rw [step1CanonicalIgnitionTower_topConstant_eq]
  exact neg_ne_zero.mpr (step1IgnitionTopConstant_ne_zero H w v hsep h j)

/-! ## Canonical terminal-residue tower -/

/-- The formal terminal residue factor for a visible coordinate.  It is the
selected final value matrix applied to the contrast stream entering the final
layer. -/
noncomputable def step1CanonicalResiduePoly {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w v : Vec d)
    (h : Fin k) (i : Step1ResidueCoordinateIndex H w h) :
    FormalPoly (n + 2) k :=
  let C := step1TargetSelectedChain H h
  let l := step1FinalTierIndex n
  (formalValueMatrix theta' l (C.headAt l) *ᵥ
    formalW theta' w v l.1 (Nat.le_of_lt l.2)) i.1

theorem step1CanonicalResiduePoly_blockTotal {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w v : Vec d)
    (h : Fin k) (i : Step1ResidueCoordinateIndex H w h) :
    BlockTotalDegreeLE 1 (step1CanonicalResiduePoly H w v h i) := by
  have hpoly := KHead.layerBounded_realMatrixToFormal_mulVec
    (valueMatrix theta' (step1FinalTierIndex n)
      ((step1TargetSelectedChain H h).headAt (step1FinalTierIndex n)))
    (fun q => (formalPoint_layerBoundedBlockAffine theta' w v
      (step1FinalTierIndex n).1
      (Nat.le_of_lt (step1FinalTierIndex n).2)).1 q) i.1
  intro m hm l
  exact (hpoly.block m (by simpa [step1CanonicalResiduePoly,
    formalValueMatrix] using hm)).block_sum_le_one l

theorem step1CanonicalResiduePoly_support {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w v : Vec d)
    (h : Fin k) (i : Step1ResidueCoordinateIndex H w h) :
    PolynomialInLayersLT (n + 1) (step1CanonicalResiduePoly H w v h i) := by
  have hpoly := KHead.layerBounded_realMatrixToFormal_mulVec
    (valueMatrix theta' (step1FinalTierIndex n)
      ((step1TargetSelectedChain H h).headAt (step1FinalTierIndex n)))
    (fun q => (formalPoint_layerBoundedBlockAffine theta' w v
      (step1FinalTierIndex n).1
      (Nat.le_of_lt (step1FinalTierIndex n).2)).1 q) i.1
  intro m hm x hx
  exact hpoly.support_lt m (by simpa [step1CanonicalResiduePoly,
    formalValueMatrix] using hm) x (by simpa using hx)

/-- Canonical dominance tower for one visible terminal residue factor. -/
noncomputable def step1CanonicalResidueTower {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w v : Vec d)
    (h : Fin k) (i : Step1ResidueCoordinateIndex H w h) :
    DominanceTowerData
      (step1HeadChain (step1TargetSelectedChain H h) (n + 1) (by omega))
      (step1CanonicalResiduePoly H w v h i) :=
  genericTowerData
    (step1HeadChain (step1TargetSelectedChain H h) (n + 1) (by omega)) 1
    (step1CanonicalResiduePoly H w v h i)

theorem step1CanonicalResidueTower_degree_pos {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w v : Vec d)
    (h : Fin k) (i : Step1ResidueCoordinateIndex H w h) :
    ∀ q, 1 ≤ (step1CanonicalResidueTower H w v h i).degree q :=
  genericTower_degree_pos _ 1 _ le_rfl

theorem step1CanonicalResidueTower_topConstant {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w v : Vec d)
    (h : Fin k) (i : Step1ResidueCoordinateIndex H w h) :
    CanonicalTowerTopConstant (step1CanonicalResidueTower H w v h i) :=
  genericTower_topConstant _ 1 _
    (step1CanonicalResiduePoly_support H w v h i)
    (step1CanonicalResiduePoly_blockTotal H w v h i)

theorem step1CanonicalResidueTower_finalCoeff {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w v : Vec d)
    (h : Fin k) (i : Step1ResidueCoordinateIndex H w h) :
    CanonicalTowerFinalCoeff (step1CanonicalResidueTower H w v h i) :=
  genericTower_finalCoeff _ 1 _

theorem step1CanonicalResidueTower_evalRecurrence {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w v : Vec d)
    (h : Fin k) (i : Step1ResidueCoordinateIndex H w h) :
    CanonicalTowerEvalRecurrence (step1CanonicalResidueTower H w v h i) :=
  genericTower_evalRecurrence _ 1 _
    (step1CanonicalResiduePoly_blockTotal H w v h i)

/-- The residue tower's top constant is the signed selected value product. -/
theorem step1CanonicalResidueTower_topConstant_eq {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w v : Vec d)
    (h : Fin k) (i : Step1ResidueCoordinateIndex H w h) :
    (step1CanonicalResidueTower H w v h i).topConstant =
      (-1 : ℝ) ^ (n + 1) * step1ResidueTopConstant H w h i := by
  let C := step1TargetSelectedChain H h
  show (topLeadingCoeff (step1HeadChain C (n + 1) (by omega)) 1
      (step1CanonicalResiduePoly H w v h i) (n + 1)).coeff 0 = _
  rw [topLeadingCoeff_coeff_zero,
    step1HeadChain_exp_eq_selectedMonomial C (n + 1) (by omega),
    step1CanonicalResiduePoly, formalValueMatrix, coeff_realMatrix_mulVec_ns]
  rw [Finset.sum_congr rfl (fun q _ => by
    change _ * (formalW theta' w v (n + 1) (by omega) q).coeff
      (step1SelectedMonomial C (n + 1) (by omega)) = _
    rw [formalW_selectedCoeff_ns theta' C w v (n + 1) (by omega) q])]
  have hfactor :
      (∑ q : Fin d,
        valueMatrix theta' (step1FinalTierIndex n)
            (C.headAt (step1FinalTierIndex n)) i.1 q *
          ((-1 : ℝ) ^ (n + 1) *
            (step1SelectedValuePrefix theta' C (n + 1) (by omega) *ᵥ w) q)) =
        (-1 : ℝ) ^ (n + 1) *
          ∑ q : Fin d, valueMatrix theta' (step1FinalTierIndex n)
              (C.headAt (step1FinalTierIndex n)) i.1 q *
            (step1SelectedValuePrefix theta' C (n + 1) (by omega) *ᵥ w) q := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [hfactor]
  change (-1 : ℝ) ^ (n + 1) *
      ((valueMatrix theta' (step1FinalTierIndex n) (C.headAt (step1FinalTierIndex n)) *ᵥ
        (step1SelectedValuePrefix theta' C (n + 1) (by omega) *ᵥ w)) i.1) = _
  rw [Matrix.mulVec_mulVec]
  have hpref := step1SelectedValuePrefix_succ theta' C (n + 1) (by omega)
  have hpref' : step1SelectedValuePrefix theta' C (n + 2) le_rfl =
      valueMatrix theta' (step1FinalTierIndex n) (C.headAt (step1FinalTierIndex n)) *
        step1SelectedValuePrefix theta' C (n + 1) (by omega) := by
    simpa [step1FinalTierIndex] using hpref
  rw [← hpref']
  change (-1 : ℝ) ^ (n + 1) *
      (step1SelectedValuePrefix theta' C (n + 2) le_rfl *ᵥ w) i.1 = _
  rw [step1SelectedValuePrefix_eq_short,
    ← step1ResidueTopConstant_eq_selectedValueProduct H w h i]

theorem step1CanonicalResidueTower_topConstant_ne_zero {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w v : Vec d)
    (h : Fin k) (i : Step1ResidueCoordinateIndex H w h) :
    (step1CanonicalResidueTower H w v h i).topConstant ≠ 0 := by
  rw [step1CanonicalResidueTower_topConstant_eq]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num))
    (step1ResidueTopConstant_ne_zero H w h i)

/-! ## The complete finite dominance family -/

/-- One canonical ignition-or-residue tower, together with every structural
fact needed by dominance persistence and tower noncancellation. -/
structure Step1CanonicalDominanceMember {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w : Vec d) (h : Fin k)
    (idx : Step1TowerMemberIndex H w h) : Type where
  poly : FormalPoly (n + 2) k
  tower : DominanceTowerData (step1TowerMemberHeadChain H w h idx) poly
  degree_pos : ∀ q, 1 ≤ tower.degree q
  topConstant_ne_zero : tower.topConstant ≠ 0
  topConstant : DominanceTowerTopConstant tower
  finalCoeff : DominanceTowerFinalCoeff tower
  evalRecurrence : DominanceTowerEvalRecurrence tower
  leadingCoeff_support : ∀ q (hq : q ≤ step1TowerMemberChainLength H w h idx),
    PolynomialInLayersLE q (tower.leadingCoeff q hq)
  lowerCoeff_support : ∀ q s,
    PolynomialInLayersLE q.1 (tower.lowerCoeff q s)
  lowerCoeff_selectedVar_notMem : ∀ q s,
    (step1TowerMemberHeadChain H w h idx).selectedVar q ∉
      (tower.lowerCoeff q s).vars

/-- The canonical finite family containing every later ignition coefficient
and every visible terminal residue coordinate. -/
noncomputable def step1CanonicalDominanceMember {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w v : Vec d)
    (hsep : (∏ idx : Step1SeparatedFactorIndex n k,
      step1SeparatedFactorValue H w v idx) ≠ 0)
    (h : Fin k) (idx : Step1TowerMemberIndex H w h) :
    Step1CanonicalDominanceMember H w h idx := by
  cases idx with
  | inl j =>
      let T := step1CanonicalIgnitionTower H w v h j
      exact {
        poly := step1CanonicalIgnitionPoly H w v h j
        tower := T
        degree_pos := step1CanonicalIgnitionTower_degree_pos H w v h j
        topConstant_ne_zero :=
          step1CanonicalIgnitionTower_topConstant_ne_zero H w v hsep h j
        topConstant := by
          simpa [DominanceTowerTopConstant, CanonicalTowerTopConstant] using
            step1CanonicalIgnitionTower_topConstant H w v h j
        finalCoeff := by
          simpa [DominanceTowerFinalCoeff, CanonicalTowerFinalCoeff] using
            step1CanonicalIgnitionTower_finalCoeff H w v h j
        evalRecurrence := by
          simpa [DominanceTowerEvalRecurrence, CanonicalTowerEvalRecurrence] using
            step1CanonicalIgnitionTower_evalRecurrence H w v h j
        leadingCoeff_support :=
          genericTower_leadingCoeff_support _ 2 _
            (step1CanonicalIgnitionPoly_support H w v h j)
            (step1CanonicalIgnitionPoly_blockTotal H w v h j)
        lowerCoeff_support :=
          genericTower_lowerCoeff_support _ 2 _
            (step1CanonicalIgnitionPoly_support H w v h j)
            (step1CanonicalIgnitionPoly_blockTotal H w v h j)
        lowerCoeff_selectedVar_notMem :=
          genericTower_lowerCoeff_notMem _ 2 _
            (step1CanonicalIgnitionPoly_support H w v h j)
            (step1CanonicalIgnitionPoly_blockTotal H w v h j) }
  | inr i =>
      let T := step1CanonicalResidueTower H w v h i
      exact {
        poly := step1CanonicalResiduePoly H w v h i
        tower := T
        degree_pos := step1CanonicalResidueTower_degree_pos H w v h i
        topConstant_ne_zero :=
          step1CanonicalResidueTower_topConstant_ne_zero H w v h i
        topConstant := by
          simpa [DominanceTowerTopConstant, CanonicalTowerTopConstant] using
            step1CanonicalResidueTower_topConstant H w v h i
        finalCoeff := by
          simpa [DominanceTowerFinalCoeff, CanonicalTowerFinalCoeff] using
            step1CanonicalResidueTower_finalCoeff H w v h i
        evalRecurrence := by
          simpa [DominanceTowerEvalRecurrence, CanonicalTowerEvalRecurrence] using
            step1CanonicalResidueTower_evalRecurrence H w v h i
        leadingCoeff_support :=
          genericTower_leadingCoeff_support _ 1 _
            (step1CanonicalResiduePoly_support H w v h i)
            (step1CanonicalResiduePoly_blockTotal H w v h i)
        lowerCoeff_support :=
          genericTower_lowerCoeff_support _ 1 _
            (step1CanonicalResiduePoly_support H w v h i)
            (step1CanonicalResiduePoly_blockTotal H w v h i)
        lowerCoeff_selectedVar_notMem :=
          genericTower_lowerCoeff_notMem _ 1 _
            (step1CanonicalResiduePoly_support H w v h i)
            (step1CanonicalResiduePoly_blockTotal H w v h i) }

/-- Strict dominance for the first `q` selected layers, simultaneously over
the whole canonical finite family.  At tier `q`, later stages are deliberately
not required yet. -/
def Step1FiniteFamilyDominance {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w v : Vec d)
    (hsep : (∏ idx : Step1SeparatedFactorIndex n k,
      step1SeparatedFactorValue H w v idx) ≠ 0)
    (h : Fin k) (q : Nat) (z : FormalVar (n + 2) k → ℂ) : Prop :=
  ∀ idx i, i.1 < q →
      dominanceTowerThreshold
          (step1CanonicalDominanceMember H w v hsep h idx).tower i z <
        ‖z ((step1TowerMemberHeadChain H w h idx).selectedVar i)‖

theorem step1FiniteFamilyDominance_zero {n k d r : Nat}
    {theta theta' : Params (n + 2) k d}
    (H : Step1StandingHypotheses r theta theta') (w v : Vec d)
    (hsep : (∏ idx : Step1SeparatedFactorIndex n k,
      step1SeparatedFactorValue H w v idx) ≠ 0) (h : Fin k)
    (z : FormalVar (n + 2) k → ℂ) :
    Step1FiniteFamilyDominance H w v hsep h 0 z := by
  intro idx i hi
  omega


end

end TransformerIdentifiability.NLayer.NoSkip
