import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Step1.TierCascade
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Analytic.SiblingAvoidance

set_option autoImplicit false

open Filter Matrix

namespace TransformerIdentifiability.NLayer.NoSkip

/-!
# No-skip Step 1 tier-local noncancellation and the gate→level recurrence

This file ports the *tier-local* core of the KHead `Step1/TierLocal.lean`
cluster to the no-skip active-stratification API.  It closes the specific gap
left open by NS104 (`Step1/TierCascade.lean`): NS104 produced the successor pole
on the ignition **gate** `csig(level)`, but deferred *propagating* that pole into
the successor tier's **level**.  The unblocker named there was "the no-skip
level-recurrence / affine pole-progression machinery — the analogue of KHead
`TierLocal.lean`".  That machinery is built here.

Three deliverables:

* **Local noncancellation + gate→level recurrence.**  A self-contained Laurent
  combinator (`levelPole_normalForm_of_gate_quadraticModel`) that turns a gate
  pole of exact order `q ≥ 1` into a *level* pole of exact order `2q` at the same
  point, provided the successor level is the quadratic-in-gate model
  `z·(s·(Ψ·s + Β) + Γ) + (z·Γ₀ + L₀)` on a punctured neighbourhood, with the
  leading factor `Ψ` analytic and **nonvanishing** at `τ` (this nonvanishing is
  exactly the local-noncancellation input `Ψ(τ) ≠ 0`).  Specialised to the NS104
  objects (`Step1SuccessorPoleNormalForm`, `step1SelectedGateFunction`,
  `step1SelectedLevelFunction`) this shows the successor tier's selected level is
  genuinely meromorphic-and-not-analytic — a real level pole
  (`step1SelectedLevelIsPole`).

* **Same-layer sibling exclusion.**  Via NS099
  (`activeSiblingLocalData_of_cornerCertificate`, from the NS049 corner
  certificate) the selected head's level germ is not identically equal to any
  same-layer sibling on the current stratification domain, so no sibling cancels
  the selected pole; and the selected level germ carries a nonzero-coefficient
  Laurent normal form (the pole is not accidentally removable).

## Model boundary (matching NS102/103/104)

The no-skip `ActiveStratificationData` carries the `level`/`gate` fields as
*opaque* functions (the model-facing dictionary boundary of NS094); it does not
carry a `level_formula`/`gate_formula` field.  Consequently the affine/quadratic
model relation connecting the successor level to the predecessor gate — supplied
in the KHead tree by `hD.level_formula`, the `formalSlope` block-degree-two
split, and `step1SuccessorLeadingFactor_ne_zero_of_tier` — enters here as a
*standing hypothesis* (`Step1SuccessorLevelModel` plus analyticity/nonvanishing
of the model coefficients), exactly as NS102/103/104 left their standing chain,
stratification, and dominance witnesses.  Under the no-skip dictionary
`C_ℓ := Σ_a V_{ℓa}` the layer constant `C_ℓ` stays opaque; nothing below expands
it via a skip cancellation identity.
-/

noncomputable section

variable {n k d r : Nat}

/-! ## Neutral Laurent order-0 / order-cast helpers

These are model-neutral facts about `LaurentNormalFormAt`, reproved directly
against the no-skip abbrev (the no-skip `LaurentNormalForm.lean` re-exports the
neutral KHead calculus but not these two shape lemmas). -/

/-- An analytic function with a nonzero value at `ξ` is a Laurent normal form of
order `0` (a removable/regular point). -/
theorem laurentNormalFormAt_zero_of_analyticAt {a : ℂ → ℂ} {ξ : ℂ}
    (ha : AnalyticAt ℂ a ξ) (hne : a ξ ≠ 0) :
    LaurentNormalFormAt a ξ 0 (a ξ) := by
  refine ⟨hne, a, ha, rfl, ?_⟩
  filter_upwards with z
  simp

/-- Transport a Laurent normal form across a proof that its order equals another
integer. -/
theorem laurentNF_order_cast {f : ℂ → ℂ} {ξ : ℂ} {μ μ' : ℤ} {c : ℂ}
    (h : LaurentNormalFormAt f ξ μ c) (hμ : μ = μ') :
    LaurentNormalFormAt f ξ μ' c := hμ ▸ h

/-! ## The gate → level recurrence (local noncancellation core)

This is the pure-Laurent heart of `lem:tier-local` / `cor:successor-pole-payload`
(KHead `step1SuccessorLevel_normalForm_of_tier`, lines ~683–911), stripped to the
model-neutral calculus.  The successor selected level, on a punctured
neighbourhood of `τ`, equals

  `z · (s z · (Ψ z · s z + Β z) + Γ z) + (z · Γ₀ z + L₀)`

where `s` is the predecessor selected gate (exact Laurent pole of order `q ≥ 1`,
from NS104) and `Ψ, Β, Γ, Γ₀` are analytic model coefficients.  The dominant term
`z · Ψ · s²` has order `0 + 0 + 2q = 2q`; every other term is dominated
(`z·s·Β` has order `q`, the analytic tail order `0`).  The nonvanishing of the
leading factor `Ψ(τ) ≠ 0` is the local-noncancellation input: it is exactly what
prevents the `s²` head from cancelling and the level from becoming analytic. -/

/-- **Local noncancellation / gate→level recurrence (Laurent core).**  A gate pole
of exact order `q ≥ 1` at `τ` propagates, through the quadratic-in-gate level
model, into a level pole of exact order `2q` at `τ`, with the explicit nonzero
leading coefficient `τ · (c · (Ψ(τ) · c))`. -/
theorem levelPole_normalForm_of_gate_quadraticModel
    {s Psi Bet Gam0 Level : ℂ → ℂ} {τ c L0 : ℂ} {q : ℕ}
    (hq : 1 ≤ q)
    (hs : LaurentNormalFormAt s τ (q : ℤ) c)
    (hτ_ne : τ ≠ 0)
    (hPsi : AnalyticAt ℂ Psi τ) (hPsiτ : Psi τ ≠ 0)
    (hBet : AnalyticAt ℂ Bet τ) (hGam0 : AnalyticAt ℂ Gam0 τ)
    (hmodel :
      (fun z => z * (s z * (Psi z * s z + Bet z)) + (z * Gam0 z + L0))
        =ᶠ[nhdsWithin τ ({τ}ᶜ : Set ℂ)] Level) :
    LaurentNormalFormAt Level τ (2 * (q : ℤ)) (τ * (c * (Psi τ * c))) := by
  have hqZ : (1 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq
  -- order-0 building blocks: the probe coordinate and the leading factor
  have hz0 : LaurentNormalFormAt (fun z : ℂ => z) τ 0 τ :=
    laurentNormalFormAt_zero_of_analyticAt (a := fun z : ℂ => z) analyticAt_id hτ_ne
  have hΨ0 : LaurentNormalFormAt Psi τ 0 (Psi τ) :=
    laurentNormalFormAt_zero_of_analyticAt hPsi hPsiτ
  -- `Ψ · s` (order q), then `Ψ · s + Β` (order q, `Β` analytic tail)
  have hΨs : LaurentNormalFormAt (fun z => Psi z * s z) τ (0 + (q : ℤ)) (Psi τ * c) :=
    hΨ0.mul hs
  have hΨsβ : LaurentNormalFormAt (fun z => Psi z * s z + Bet z) τ
      (0 + (q : ℤ)) (Psi τ * c) :=
    hΨs.add_analyticAt hBet (by rw [zero_add]; exact hqZ)
  -- `s · (Ψ · s + Β)` (order 2q), then `z · s · (Ψ · s + Β)` (order 2q)
  have hs2 : LaurentNormalFormAt (fun z => s z * (Psi z * s z + Bet z)) τ
      ((q : ℤ) + (0 + (q : ℤ))) (c * (Psi τ * c)) :=
    hs.mul hΨsβ
  have hzs2 : LaurentNormalFormAt (fun z => z * (s z * (Psi z * s z + Bet z))) τ
      (0 + ((q : ℤ) + (0 + (q : ℤ)))) (τ * (c * (Psi τ * c))) :=
    hz0.mul hs2
  -- the analytic tail `z · Γ₀ + L₀`
  have hγ' : AnalyticAt ℂ (fun z => z * Gam0 z + L0) τ :=
    (analyticAt_id.mul hGam0).add analyticAt_const
  have hmodelNF : LaurentNormalFormAt
      (fun z => z * (s z * (Psi z * s z + Bet z)) + (z * Gam0 z + L0)) τ
      (0 + ((q : ℤ) + (0 + (q : ℤ)))) (τ * (c * (Psi τ * c))) :=
    hzs2.add_analyticAt hγ' (by omega)
  exact laurentNF_order_cast (hmodelNF.congr hmodel) (by ring)

/-! ## Successor level pole for the selected chain (NS104 → level) -/

/-- The successor tier's selected level is genuinely meromorphic-and-not-analytic
at `τ`: a *real* level pole (as opposed to the gate pole carried by
`step1SuccessorSelectedLevelPole`). -/
def step1SelectedLevelIsPole {k d : Nat}
    (D : ActiveStratificationData (n + 2) k d) (C : Step1SelectedChain n k)
    (j : Step1TierIndex n) (τ : ℂ) : Prop :=
  MeromorphicAt (step1SelectedLevelFunction D C j) τ ∧
    ¬ AnalyticAt ℂ (step1SelectedLevelFunction D C j) τ

theorem step1SelectedLevelIsPole.meromorphicAt {k d : Nat}
    {D : ActiveStratificationData (n + 2) k d} {C : Step1SelectedChain n k}
    {j : Step1TierIndex n} {τ : ℂ}
    (h : step1SelectedLevelIsPole D C j τ) :
    MeromorphicAt (step1SelectedLevelFunction D C j) τ :=
  h.1

theorem step1SelectedLevelIsPole.not_analyticAt {k d : Nat}
    {D : ActiveStratificationData (n + 2) k d} {C : Step1SelectedChain n k}
    {j : Step1TierIndex n} {τ : ℂ}
    (h : step1SelectedLevelIsPole D C j τ) :
    ¬ AnalyticAt ℂ (step1SelectedLevelFunction D C j) τ :=
  h.2

/-- The quadratic-in-gate level model connecting the successor tier's selected
**level** (`step1SelectedLevelFunction D C jsucc`) to the currently processed
tier's selected **gate** (`step1SelectedGateFunction D C j`).  This is the
standing model relation supplied in the KHead tree by `hD.level_formula` and the
`formalSlope` block-degree-two split; here it is a hypothesis, since the no-skip
`ActiveStratificationData` keeps `level`/`gate` opaque. -/
def Step1SuccessorLevelModel {k d : Nat}
    (D : ActiveStratificationData (n + 2) k d) (C : Step1SelectedChain n k)
    (j jsucc : Step1TierIndex n) (Psi Bet Gam0 : ℂ → ℂ) (L0 : ℂ) (τ : ℂ) : Prop :=
  (fun z => z * (step1SelectedGateFunction D C j z *
      (Psi z * step1SelectedGateFunction D C j z + Bet z)) + (z * Gam0 z + L0))
    =ᶠ[nhdsWithin τ ({τ}ᶜ : Set ℂ)] step1SelectedLevelFunction D C jsucc

/-- **Gate pole → successor level normal form.**  From the NS104 successor gate
pole (`Step1SuccessorPoleNormalForm`, exact gate order `N.q ≥ 1`), the local
noncancellation input `Ψ(τ) ≠ 0`, and the standing quadratic level model, the
successor tier's selected level acquires an *explicit* Laurent normal form of
order `2·N.q` with nonzero leading coefficient. -/
theorem step1SuccessorLevelNormalForm_of_model {k d : Nat}
    {D : ActiveStratificationData (n + 2) k d} {C : Step1SelectedChain n k}
    {j jsucc : Step1TierIndex n} {τ : ℂ}
    (N : Step1SuccessorPoleNormalForm D C j τ)
    (hτ_ne : τ ≠ 0)
    {Psi Bet Gam0 : ℂ → ℂ} {L0 : ℂ}
    (hPsi : AnalyticAt ℂ Psi τ) (hPsiτ : Psi τ ≠ 0)
    (hBet : AnalyticAt ℂ Bet τ) (hGam0 : AnalyticAt ℂ Gam0 τ)
    (hmodel : Step1SuccessorLevelModel D C j jsucc Psi Bet Gam0 L0 τ) :
    LaurentNormalFormAt (step1SelectedLevelFunction D C jsucc) τ
      (2 * (N.q : ℤ)) (τ * (N.coeff * (Psi τ * N.coeff))) :=
  levelPole_normalForm_of_gate_quadraticModel N.q_pos N.normalForm hτ_ne
    hPsi hPsiτ hBet hGam0 hmodel

/-- **Tier ignition into the level.**  The successor tier's selected level is a
real level pole (meromorphic, not analytic) at `τ`.  This is the statement NS104
deferred: the ignition gate pole is now propagated into the successor tier's
level. -/
theorem step1_successorSelectedLevelIsPole_of_model {k d : Nat}
    {D : ActiveStratificationData (n + 2) k d} {C : Step1SelectedChain n k}
    {j jsucc : Step1TierIndex n} {τ : ℂ}
    (N : Step1SuccessorPoleNormalForm D C j τ)
    (hτ_ne : τ ≠ 0)
    {Psi Bet Gam0 : ℂ → ℂ} {L0 : ℂ}
    (hPsi : AnalyticAt ℂ Psi τ) (hPsiτ : Psi τ ≠ 0)
    (hBet : AnalyticAt ℂ Bet τ) (hGam0 : AnalyticAt ℂ Gam0 τ)
    (hmodel : Step1SuccessorLevelModel D C j jsucc Psi Bet Gam0 L0 τ) :
    step1SelectedLevelIsPole D C jsucc τ := by
  have hNF := step1SuccessorLevelNormalForm_of_model N hτ_ne
    hPsi hPsiτ hBet hGam0 hmodel
  have h2q : (1 : ℤ) ≤ 2 * (N.q : ℤ) := by
    have : (1 : ℤ) ≤ (N.q : ℤ) := by exact_mod_cast N.q_pos
    omega
  exact ⟨hNF.meromorphicAt, hNF.not_analyticAt h2q⟩

/-! ## Same-layer sibling exclusion for the selected tier (NS099) -/

/-- **Selected-tier sibling-avoidance local data.**  Package NS099
(`activeSiblingLocalData_of_cornerCertificate`) at the selected head of the
current tier: the selected level hits `Π`, no same-layer sibling germ is
identical to it on the stratification domain (sibling exclusion), and the
selected level germ carries a nonzero-coefficient Laurent normal form together
with the selected gate arc (local noncancellation of the selected term).  The
level-model / corner-certificate inputs are the standing NS049/NS094 boundary
data, as in NS102/103/104. -/
theorem step1SelectedTierSiblingLocalData {k d : Nat}
    {theta' : Params (n + 2) k d} {D : ActiveStratificationData (n + 2) k d}
    (hD : ActiveHeadSingularStratification (r := r) theta' D)
    (C : Step1SelectedChain n k) (j : Step1TierIndex n)
    (hactive : C.headAt j ∈ activeHeads theta' j)
    {τ : ℂ} (hτ : τ ∈ D.stratum j.1)
    (hpole : step1SelectedLevelPole D C j τ)
    (w v : Vec d) (eta : FormalVar (n + 2) k → ℂ → ℂ)
    (heta : ∀ y : FormalVar (n + 2) k, AnalyticAt ℂ (eta y) 0)
    (heta_zero : ∀ y : FormalVar (n + 2) k, eta y 0 = (alpha r : ℂ))
    (hlevel : ∀ a : Fin k, D.level (j, a) =
      fun tau => formalLevel (r := r) theta' w v (fun y => eta y tau) (j, a) tau)
    (hcorner : ∀ c : Fin k, c ≠ C.headAt j →
      alphaCornerSlopeDiff r theta' j (C.headAt j) c w v ≠ 0) :
    ActiveSiblingLocalData (r := r) theta' D j (C.headAt j) τ :=
  activeSiblingLocalData_of_cornerCertificate hD w v j (C.headAt j) hactive hτ
    (show D.level (j, C.headAt j) τ ∈ Pi from hpole)
    eta heta heta_zero hlevel hcorner

/-- **Sibling exclusion (selected tier).**  No same-layer sibling level germ is
identical to the selected level germ on the current stratification domain — no
sibling cancels the selected pole. -/
theorem step1SelectedTier_siblings_not_identical {k d : Nat}
    {theta' : Params (n + 2) k d} {D : ActiveStratificationData (n + 2) k d}
    (hD : ActiveHeadSingularStratification (r := r) theta' D)
    (C : Step1SelectedChain n k) (j : Step1TierIndex n)
    (hactive : C.headAt j ∈ activeHeads theta' j)
    {τ : ℂ} (hτ : τ ∈ D.stratum j.1)
    (hpole : step1SelectedLevelPole D C j τ)
    (w v : Vec d) (eta : FormalVar (n + 2) k → ℂ → ℂ)
    (heta : ∀ y : FormalVar (n + 2) k, AnalyticAt ℂ (eta y) 0)
    (heta_zero : ∀ y : FormalVar (n + 2) k, eta y 0 = (alpha r : ℂ))
    (hlevel : ∀ a : Fin k, D.level (j, a) =
      fun tau => formalLevel (r := r) theta' w v (fun y => eta y tau) (j, a) tau)
    (hcorner : ∀ c : Fin k, c ≠ C.headAt j →
      alphaCornerSlopeDiff r theta' j (C.headAt j) c w v ≠ 0) :
    ∀ c : Fin k, c ≠ C.headAt j →
      ¬ Set.EqOn (D.level (j, C.headAt j)) (D.level (j, c)) (D.Omega j.1) :=
  (step1SelectedTierSiblingLocalData hD C j hactive hτ hpole
    w v eta heta heta_zero hlevel hcorner).siblings_not_identical

/-- **Local noncancellation (selected tier).**  The selected level germ carries a
genuine (nonzero-coefficient) Laurent normal form at `τ` together with the
selected gate arc — the selected term does not accidentally cancel, so the pole
is not removable. -/
theorem step1SelectedTier_selectedArc {k d : Nat}
    {theta' : Params (n + 2) k d} {D : ActiveStratificationData (n + 2) k d}
    (hD : ActiveHeadSingularStratification (r := r) theta' D)
    (C : Step1SelectedChain n k) (j : Step1TierIndex n)
    (hactive : C.headAt j ∈ activeHeads theta' j)
    {τ : ℂ} (hτ : τ ∈ D.stratum j.1)
    (hpole : step1SelectedLevelPole D C j τ)
    (w v : Vec d) (eta : FormalVar (n + 2) k → ℂ → ℂ)
    (heta : ∀ y : FormalVar (n + 2) k, AnalyticAt ℂ (eta y) 0)
    (heta_zero : ∀ y : FormalVar (n + 2) k, eta y 0 = (alpha r : ℂ))
    (hlevel : ∀ a : Fin k, D.level (j, a) =
      fun tau => formalLevel (r := r) theta' w v (fun y => eta y tau) (j, a) tau)
    (hcorner : ∀ c : Fin k, c ≠ C.headAt j →
      alphaCornerSlopeDiff r theta' j (C.headAt j) c w v ≠ 0) :
    ∃ kappa : Nat, ∃ coeff : ℂ, 1 ≤ kappa ∧ coeff ≠ 0 ∧
      LaurentNormalFormAt
        (fun z => D.level (j, C.headAt j) z - D.level (j, C.headAt j) τ)
        τ (-(kappa : ℤ)) coeff ∧
      Nonempty (SelectedArcData
        (fun z => csig (D.level (j, C.headAt j) z)) τ kappa coeff⁻¹) :=
  (step1SelectedTierSiblingLocalData hD C j hactive hτ hpole
    w v eta heta heta_zero hlevel hcorner).selected_arc

end

end TransformerIdentifiability.NLayer.NoSkip
