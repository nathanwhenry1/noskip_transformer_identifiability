import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Analytic.LaurentNormalForm
import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.PoleArcs

set_option autoImplicit false

open Filter Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.NoSkip

/-!
# Pole arcs for no-skip formal levels

The local chart and arc constructions depend only on a complex function and its
exact Laurent normal form.  We expose that neutral API under NoSkip names, then
instantiate it for the sigmoid of an active no-skip level.  No realization or
skip-model recurrence is used here.
-/

noncomputable section

/-! ## Neutral local-pole API -/

abbrev puncturedDisc (xi : ℂ) (rho : ℝ) : Set ℂ :=
  KHead.puncturedDisc xi rho

abbrev levelPreimageIn (H : ℂ → ℂ) (xi : ℂ) (rho : ℝ) : Set ℂ :=
  KHead.levelPreimageIn H xi rho

abbrev imaginaryAxis : Set ℂ := KHead.imaginaryAxis

abbrev LevelArcData (H : ℂ → ℂ) (xi : ℂ) :=
  KHead.LevelArcData H xi

abbrev LevelArcPiSequence (H : ℂ → ℂ) (xi : ℂ) (radius : ℝ)
    (arc : LevelArcData H xi) :=
  KHead.LevelArcPiSequence H xi radius arc

abbrev ArcStructureResult (H : ℂ → ℂ) (xi : ℂ) (m : Nat) : Prop :=
  KHead.ArcStructureResult H xi m

abbrev LevelPreimageResult (H : ℂ → ℂ) (xi : ℂ) : Prop :=
  KHead.LevelPreimageResult H xi

abbrev PoleChart (H : ℂ → ℂ) (xi : ℂ) (m : Nat) (c0 : ℂ) :=
  KHead.PoleChart H xi m c0

abbrev SelectedArcData (H : ℂ → ℂ) (xi : ℂ) (m : Nat) (c0 : ℂ) :=
  KHead.SelectedArcData H xi m c0

/-- A meromorphic germ is analytic throughout a sufficiently small punctured
disc.  This discharges the only extra local-domain hypothesis of the neutral
pole-chart theorem. -/
theorem exists_puncturedDisc_analyticOnNhd_of_meromorphicAt
    {H : ℂ → ℂ} {xi : ℂ} (hH : MeromorphicAt H xi) :
    ∃ rho : ℝ, 0 < rho ∧ AnalyticOnNhd ℂ H (puncturedDisc xi rho) := by
  have hev : ∀ᶠ z in nhdsWithin xi ({xi}ᶜ : Set ℂ), AnalyticAt ℂ H z :=
    hH.eventually_analyticAt
  obtain ⟨rho, hrho, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hev
  refine ⟨rho, hrho, ?_⟩
  intro z hz
  exact hsub ⟨by simpa [KHead.puncturedDisc] using hz.2,
    by simpa [KHead.puncturedDisc] using hz.1⟩

/-- Exact positive Laurent order alone produces the full selected pole arc;
the punctured-disc holomorphy required by the neutral constructor follows from
the normal form's meromorphicity. -/
theorem selectedArcData_of_normalForm
    {H : ℂ → ℂ} {xi : ℂ} {m : Nat} {c0 : ℂ}
    (hm : 1 ≤ m) (hNF : LaurentNormalFormAt H xi (m : ℤ) c0) :
    Nonempty (SelectedArcData H xi m c0) := by
  obtain ⟨rho, hrho, hHol⟩ :=
    exists_puncturedDisc_analyticOnNhd_of_meromorphicAt
      (LaurentNormalFormAt.meromorphicAt hNF)
  exact KHead.selectedArcData_of_normalForm hm hrho hHol hNF

theorem arc_pullback
    {H : ℂ → ℂ} {xi : ℂ} {m : Nat} {c0 : ℂ}
    (A : SelectedArcData H xi m c0)
    {G : ℂ → ℂ} {mu : ℤ} {c : ℂ}
    (hG : LaurentNormalFormAt G xi mu c) :
    ∃ B : ℝ → ℂ, ContinuousOn B (Set.Icc 0 A.arcRadius) ∧ B 0 = 0 ∧
      ∃ rho1 : ℝ, 0 < rho1 ∧ rho1 ≤ A.arcRadius ∧
        ∀ rho : ℝ, 0 < rho → rho ≤ rho1 →
          G (A.arc rho) = (rho : ℂ) ^ (-mu) *
            (c * Complex.exp (-(mu : ℂ) * (A.angle : ℂ) * Complex.I) + B rho) :=
  KHead.arc_pullback A hG

theorem SelectedArcData.toLevelPreimageResult
    {H : ℂ → ℂ} {xi : ℂ} {m : Nat} {c0 : ℂ}
    (A : SelectedArcData H xi m c0) : LevelPreimageResult H xi :=
  KHead.SelectedArcData.toLevelPreimageResult A

theorem SelectedArcData.toArcStructureResult
    {H : ℂ → ℂ} {xi : ℂ} {m : Nat} {c0 : ℂ}
    (A : SelectedArcData H xi m c0) (hm : 1 ≤ m) :
    ArcStructureResult H xi m :=
  KHead.SelectedArcData.toArcStructureResult A hm

/-! ## No-skip active-level instantiation -/

/-- At an active no-skip pole, the sigmoid of the holomorphic level satisfies
all local pole-arc hypotheses and therefore carries a selected arc. -/
theorem activeLevel_sigmoid_selectedArcData
    {r L k d : Nat} {theta : Params L k d}
    {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification (r := r) theta D)
    (l : Fin L) (a : Fin k) (ha : a ∈ activeHeads theta l)
    {xi : ℂ} (hxiOmega : xi ∈ D.Omega l.1)
    (hxiPi : D.level (l, a) xi ∈ Pi) :
    ∃ kappa : Nat, ∃ c : ℂ, 1 ≤ kappa ∧ c ≠ 0 ∧
      LaurentNormalFormAt
        (fun z => D.level (l, a) z - D.level (l, a) xi)
        xi (-(kappa : ℤ)) c ∧
      Nonempty (SelectedArcData
        (fun z => csig (D.level (l, a) z)) xi kappa c⁻¹) := by
  obtain ⟨kappa, c, hkappa, hc, hlevel, hsigmoid⟩ :=
    activeLevel_sigmoid_normalForms_at_pole hD l a ha hxiOmega hxiPi
  exact ⟨kappa, c, hkappa, hc, hlevel,
    selectedArcData_of_normalForm hkappa hsigmoid⟩

/-- Every active reduced-stratum point supplies a no-skip head together with
its exact level order and selected sigmoid-pole arc. -/
theorem activeStratum_exists_selectedArcData
    {r L k d : Nat} {theta : Params L k d}
    {D : ActiveStratificationData L k d}
    (hD : ActiveHeadSingularStratification (r := r) theta D)
    (l : Fin L) {xi : ℂ} (hxi : xi ∈ D.stratum l.1) :
    ∃ a : Fin k, a ∈ activeHeads theta l ∧
      ∃ kappa : Nat, ∃ c : ℂ, 1 ≤ kappa ∧ c ≠ 0 ∧
        LaurentNormalFormAt
          (fun z => D.level (l, a) z - D.level (l, a) xi)
          xi (-(kappa : ℤ)) c ∧
        Nonempty (SelectedArcData
          (fun z => csig (D.level (l, a) z)) xi kappa c⁻¹) := by
  rw [mem_activeStratum_iff hD l xi] at hxi
  rcases hxi with ⟨a, ha, hxiOmega, hxiPi⟩
  rcases activeLevel_sigmoid_selectedArcData
    hD l a ha hxiOmega hxiPi with
    ⟨kappa, c, hkappa, hc, hlevel, hArc⟩
  exact ⟨a, ha, kappa, c, hkappa, hc, hlevel, hArc⟩

end

end TransformerIdentifiability.NLayer.NoSkip
