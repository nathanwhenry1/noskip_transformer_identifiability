import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.PlaneTopology
import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.LaurentNormalForm

set_option autoImplicit false

open Filter Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.KHead

/-! ## `lem:arc-structure` and `lem:level-preimage` -/

/-- Punctured disc centered at `ξ` with radius `ρ`. -/
def puncturedDisc (ξ : ℂ) (ρ : ℝ) : Set ℂ :=
  {τ : ℂ | τ ≠ ξ ∧ dist τ ξ < ρ}

/-- Odd-pi preimage points of a level function inside a punctured disc. -/
def levelPreimageIn (H : ℂ -> ℂ) (ξ : ℂ) (ρ : ℝ) : Set ℂ :=
  puncturedDisc ξ ρ ∩ H ⁻¹' Pi

/-- The imaginary axis in `ℂ`. -/
def imaginaryAxis : Set ℂ :=
  {z : ℂ | ∃ t : ℝ, z = (t : ℂ) * Complex.I}

/-- Data for one local real-analytic arc in the TeX arc-structure lemma. -/
structure LevelArcData (H : ℂ -> ℂ) (ξ : ℂ) where
  gamma : ℝ -> ℂ
  sign : Int
  sign_sq : sign * sign = 1
  tends_to_center : Tendsto gamma (nhdsWithin (0 : ℝ) {ρ : ℝ | 0 < ρ}) (nhds ξ)

/-- Explicit consecutive odd-pi preimage sequence carried by one local arc.  This
is the Lean-facing part of `lem:arc-structure`(d): the radii tend to zero inside
the positive half-line, the corresponding arc points are genuine punctured-disc
Pi preimages, and the points are pairwise distinct. -/
structure LevelArcPiSequence (H : ℂ -> ℂ) (ξ : ℂ) (radius : ℝ)
    (arc : LevelArcData H ξ) where
  rho : ℕ -> ℝ
  rho_pos : ∀ n : ℕ, 0 < rho n
  rho_le_radius : ∀ n : ℕ, rho n ≤ radius
  rho_tendsto_zero : Tendsto rho atTop (nhdsWithin (0 : ℝ) {ρ : ℝ | 0 < ρ})
  point_mem_radius : ∀ n : ℕ, arc.gamma (rho n) ∈ puncturedDisc ξ radius
  point_mem_pi : ∀ n : ℕ, H (arc.gamma (rho n)) ∈ Pi
  point_injective : Function.Injective fun n : ℕ => arc.gamma (rho n)

/-- Result interface for **K04E lem-arc-structure**. -/
structure ArcStructureResult (H : ℂ -> ℂ) (ξ : ℂ) (m : Nat) : Prop where
  pole_order_pos : 1 ≤ m
  arc_data :
    ∃ radius : ℝ, 0 < radius ∧
      ∃ arcs : Fin (2 * m) -> LevelArcData H ξ,
        (∀ τ ∈ puncturedDisc ξ radius, H τ ∈ imaginaryAxis ->
          ∃ q : Fin (2 * m), ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ radius ∧
            (arcs q).gamma ρ = τ) ∧
        ∀ q : Fin (2 * m), ∃ _ : LevelArcPiSequence H ξ radius (arcs q), True

/-- Constructor for the local arc-structure interface from its component data. -/
theorem arcStructureResult_of_components {H : ℂ -> ℂ} {ξ : ℂ} {m : Nat}
    (hm : 1 ≤ m) {radius : ℝ} (hradius : 0 < radius)
    {arcs : Fin (2 * m) -> LevelArcData H ξ}
    (hcover :
      ∀ τ ∈ puncturedDisc ξ radius, H τ ∈ imaginaryAxis ->
        ∃ q : Fin (2 * m), ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ radius ∧
          (arcs q).gamma ρ = τ)
    (hseq :
      ∀ q : Fin (2 * m), ∃ _ : LevelArcPiSequence H ξ radius (arcs q), True) :
    ArcStructureResult H ξ m where
  pole_order_pos := hm
  arc_data := ⟨radius, hradius, arcs, hcover, hseq⟩

/-- **K04E.E.lem-arc-structure.S/P**.

Constructor form of the local arc-structure interface from explicit arc and
odd-pi sequence data. -/
theorem lem_arc_structure {H : ℂ -> ℂ} {ξ : ℂ} {m : Nat}
    (hm : 1 ≤ m) {radius : ℝ} (hradius : 0 < radius)
    {arcs : Fin (2 * m) -> LevelArcData H ξ}
    (hcover :
      ∀ τ ∈ puncturedDisc ξ radius, H τ ∈ imaginaryAxis ->
        ∃ q : Fin (2 * m), ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ radius ∧
          (arcs q).gamma ρ = τ)
    (hseq :
      ∀ q : Fin (2 * m), ∃ _ : LevelArcPiSequence H ξ radius (arcs q), True) :
    ArcStructureResult H ξ m :=
  arcStructureResult_of_components hm hradius hcover hseq

/-- Result interface for **K04E lem-level-preimage**. -/
structure LevelPreimageResult (H : ℂ -> ℂ) (ξ : ℂ) : Prop where
  arbitrarily_close_pi_preimages :
    ∀ ρ : ℝ, 0 < ρ -> (levelPreimageIn H ξ ρ).Infinite

/-- A strengthened arc-structure package supplies arbitrarily close odd-pi
preimages by taking a tail of one explicit arc sequence. -/
theorem levelPreimageResult_of_arcStructure {H : ℂ -> ℂ} {ξ : ℂ} {m : Nat}
    (h : ArcStructureResult H ξ m) : LevelPreimageResult H ξ := by
  rcases h.arc_data with ⟨radius, _hradius_pos, arcs, _hcover, hseq⟩
  have hm_pos : 0 < 2 * m := by
    exact Nat.mul_pos (by norm_num) (lt_of_lt_of_le Nat.zero_lt_one h.pole_order_pos)
  let q0 : Fin (2 * m) := ⟨0, hm_pos⟩
  rcases hseq q0 with ⟨seq, _hseq⟩
  refine ⟨?_⟩
  intro ε hε
  have hpoints_tendsto :
      Tendsto (fun n : ℕ => (arcs q0).gamma (seq.rho n)) atTop (nhds ξ) :=
    (arcs q0).tends_to_center.comp seq.rho_tendsto_zero
  have heventually_ball :
      ∀ᶠ n in atTop, (arcs q0).gamma (seq.rho n) ∈ Metric.ball ξ ε :=
    hpoints_tendsto (Metric.ball_mem_nhds ξ hε)
  rcases Filter.eventually_atTop.1 heventually_ball with ⟨N, hN⟩
  refine Set.infinite_of_injective_forall_mem
    (s := levelPreimageIn H ξ ε)
    (f := fun n : ℕ => (arcs q0).gamma (seq.rho (N + n))) ?_ ?_
  · intro n n' hnn'
    have hidx : N + n = N + n' := seq.point_injective hnn'
    exact Nat.add_left_cancel hidx
  · intro n
    have hge : N ≤ N + n := by omega
    have hball : (arcs q0).gamma (seq.rho (N + n)) ∈ Metric.ball ξ ε :=
      hN (N + n) hge
    exact ⟨⟨(seq.point_mem_radius (N + n)).1, by
        simpa [Metric.mem_ball] using hball⟩,
      seq.point_mem_pi (N + n)⟩

/-- **K04E.E.lem-level-preimage.S/P**.

Accumulation of odd-pi preimages extracted from the strengthened local
arc-structure data. -/
theorem lem_level_preimage {H : ℂ -> ℂ} {ξ : ℂ} {m : Nat}
    (h : ArcStructureResult H ξ m) : LevelPreimageResult H ξ :=
  levelPreimageResult_of_arcStructure h


/-! ## `lem:pole-chart`, `lem:arc-structure`(e) and `lem:arc-pullback` -/

/-- The `m`-th root branch identity: `exp(-(1/m)·log u)^{-m} = u` for `u ≠ 0` and `m ≥ 1`.
This is the analytic heart of `lem:pole-chart` (the local `m`-th root of `g/c0`). -/
theorem exp_neg_inv_mul_log_zpow {m : ℕ} (hm : 1 ≤ m) {u : ℂ} (hu : u ≠ 0) :
    (Complex.exp (-((m:ℂ)⁻¹) * Complex.log u)) ^ (-(m:ℤ)) = u := by
  have hmc : (m:ℂ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hm
  rw [← Complex.exp_int_mul]
  rw [show ((-(m:ℤ) : ℤ) : ℂ) * (-((m:ℂ)⁻¹) * Complex.log u) = Complex.log u by
        push_cast; field_simp]
  exact Complex.exp_log hu

/-- `lem:pole-chart`: biholomorphic chart normal form `H = c0 · ψ^{-m}`. -/
structure PoleChart (H : ℂ -> ℂ) (ξ : ℂ) (m : Nat) (c0 : ℂ) : Type where
  domain : Set ℂ
  radius' : ℝ
  ψ : ℂ -> ℂ
  ψinv : ℂ -> ℂ
  domain_isOpen : IsOpen domain
  center_mem : ξ ∈ domain
  radius'_pos : 0 < radius'
  ψ_analytic : AnalyticOnNhd ℂ ψ domain
  ψ_center : ψ ξ = 0
  ψ_deriv_one : deriv ψ ξ = 1
  biholo_left : ∀ z ∈ domain, ψinv (ψ z) = z
  biholo_right : ∀ w ∈ Metric.ball (0:ℂ) radius', ψ (ψinv w) = w ∧ ψinv w ∈ domain
  maps_onto : ψ '' domain = Metric.ball (0:ℂ) radius'
  normal_form : ∀ z ∈ domain, z ≠ ξ -> H z = c0 * (ψ z) ^ (-(m:ℤ))
  beta_analytic_ne :
    ∃ β : ℂ -> ℂ, AnalyticOnNhd ℂ β (Metric.ball (0:ℂ) radius') ∧ β 0 = 1 ∧
      (∀ w ∈ Metric.ball (0:ℂ) radius', β w ≠ 0) ∧
      ∀ w ∈ Metric.ball (0:ℂ) radius', w ≠ 0 -> ψinv w = ξ + w * β w

/-- `lem:pole-chart`: a meromorphic `H` with a pole of order `m ≥ 1` and leading
coefficient `c0` admits a biholomorphic chart in which `H = c0 · ψ^{-m}`.  The chart is
built from the branch `η = exp(-(1/m)·log(g/c0))` (with `g` the analytic Laurent factor),
`ψ = (·-ξ)·η`, and the holomorphic inverse function theorem. -/
theorem poleChart_of_normalForm {H : ℂ -> ℂ} {ξ : ℂ} {m : ℕ} {c0 : ℂ} (hm : 1 ≤ m)
    {ρ0 : ℝ} (hρ0 : 0 < ρ0)
    (hHol : AnalyticOnNhd ℂ H (puncturedDisc ξ ρ0))
    (hNF : LaurentNormalFormAt H ξ (m : ℤ) c0) :
    Nonempty (PoleChart H ξ m c0) := by
  classical
  have hc0 : c0 ≠ 0 := hNF.coeff_ne_zero
  obtain ⟨g, hg_an, hgξ, hg_eq⟩ := hNF.factored
  have hval : g ξ / c0 = 1 := by rw [hgξ]; exact div_self hc0
  -- the branch `η` and chart candidate `ψ = (·-ξ)·η`
  set η : ℂ → ℂ := fun τ => Complex.exp (-((m:ℂ)⁻¹) * Complex.log (g τ / c0)) with hη_def
  set ψ : ℂ → ℂ := fun τ => (τ - ξ) * η τ with hψ_def
  have hη_ξ : η ξ = 1 := by
    simp only [hη_def]
    rw [hval, Complex.log_one, mul_zero, Complex.exp_zero]
  have hη_an : AnalyticAt ℂ η ξ := by
    rw [hη_def]
    have h1 : AnalyticAt ℂ (fun z => g z / c0) ξ := hg_an.div analyticAt_const hc0
    have h2 : AnalyticAt ℂ (fun z => Complex.log (g z / c0)) ξ :=
      h1.clog (by rw [hval]; exact Complex.one_mem_slitPlane)
    exact (analyticAt_const.mul h2).cexp'
  have hψ_ξ : ψ ξ = 0 := by simp only [hψ_def, sub_self, zero_mul]
  have hψ_an : AnalyticAt ℂ ψ ξ := by
    rw [hψ_def]; exact (analyticAt_id.sub analyticAt_const).mul hη_an
  have hderiv : deriv ψ ξ = 1 := by
    have hsub_diff : HasDerivAt (fun τ : ℂ => τ - ξ) 1 ξ := (hasDerivAt_id ξ).sub_const ξ
    have hη_diff : HasDerivAt η (deriv η ξ) ξ := hη_an.differentiableAt.hasDerivAt
    have hψ_hd : HasDerivAt ψ 1 ξ := by
      rw [hψ_def]
      simpa [hη_ξ, sub_self] using hsub_diff.mul hη_diff
    exact hψ_hd.deriv
  have hf' : deriv ψ ξ ≠ 0 := by rw [hderiv]; norm_num
  -- the local inverse from the holomorphic inverse function theorem
  obtain ⟨lInv, hlInv_an0, hleft, hright, hlInv_sd⟩ :
      ∃ lInv : ℂ → ℂ, AnalyticAt ℂ lInv (ψ ξ) ∧
        (∀ᶠ z in nhds ξ, lInv (ψ z) = z) ∧
        (∀ᶠ w in nhds (ψ ξ), ψ (lInv w) = w) ∧
        HasStrictDerivAt lInv (deriv ψ ξ)⁻¹ (ψ ξ) :=
    ⟨hψ_an.hasStrictDerivAt.localInverse _ _ _ hf',
     hψ_an.analyticAt_localInverse hf',
     hψ_an.hasStrictDerivAt.eventually_left_inverse hf',
     hψ_an.hasStrictDerivAt.eventually_right_inverse hf',
     hψ_an.hasStrictDerivAt.to_localInverse hf'⟩
  have hlInv0 : lInv 0 = ξ := by have := hleft.self_of_nhds; rwa [hψ_ξ] at this
  have hlInv_an00 : AnalyticAt ℂ lInv 0 := hψ_ξ ▸ hlInv_an0
  have hlInv_sd0 : HasStrictDerivAt lInv (deriv ψ ξ)⁻¹ 0 := hψ_ξ ▸ hlInv_sd
  -- the good open region `W` around `ξ`
  have haux_sp : ∀ᶠ z in nhds ξ, g z / c0 ∈ Complex.slitPlane :=
    (hg_an.continuousAt.div_const c0).preimage_mem_nhds
      (by rw [hval]; exact Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane)
  obtain ⟨Wan, hWan_prop, hWan_open, hWan_mem⟩ :=
    eventually_nhds_iff.mp hψ_an.eventually_analyticAt
  obtain ⟨Wsp, hWsp_prop, hWsp_open, hWsp_mem⟩ := eventually_nhds_iff.mp haux_sp
  obtain ⟨Wl, hWl_prop, hWl_open, hWl_mem⟩ := eventually_nhds_iff.mp hleft
  obtain ⟨Wnf, hWnf_open, hWnf_mem, hWnf_sub⟩ := mem_nhdsWithin.mp hg_eq
  set W : Set ℂ := Wan ∩ Wsp ∩ Wl ∩ Wnf with hW_def
  have hW_open : IsOpen W := ((hWan_open.inter hWsp_open).inter hWl_open).inter hWnf_open
  have hξW : ξ ∈ W := ⟨⟨⟨hWan_mem, hWsp_mem⟩, hWl_mem⟩, hWnf_mem⟩
  have hW_an : ∀ z ∈ W, AnalyticAt ℂ ψ z := fun z hz => hWan_prop z hz.1.1.1
  have hW_sp : ∀ z ∈ W, g z / c0 ∈ Complex.slitPlane := fun z hz => hWsp_prop z hz.1.1.2
  have hW_left : ∀ z ∈ W, lInv (ψ z) = z := fun z hz => hWl_prop z hz.1.2
  have hW_nf : ∀ z ∈ W, z ≠ ξ → H z = g z * (z - ξ) ^ (-(m:ℤ)) :=
    fun z hz hzξ => hWnf_sub ⟨hz.2, hzξ⟩
  -- choose the chart radius `radius'`
  have e_all : ∀ᶠ w in nhds (0:ℂ),
      ψ (lInv w) = w ∧ AnalyticAt ℂ lInv w ∧ lInv w ∈ W := by
    have e_right : ∀ᶠ w in nhds (0:ℂ), ψ (lInv w) = w := by
      have := hright; rwa [hψ_ξ] at this
    have e_an : ∀ᶠ w in nhds (0:ℂ), AnalyticAt ℂ lInv w := hlInv_an00.eventually_analyticAt
    have e_W : ∀ᶠ w in nhds (0:ℂ), lInv w ∈ W :=
      hlInv_an00.continuousAt.preimage_mem_nhds (by rw [hlInv0]; exact hW_open.mem_nhds hξW)
    exact e_right.and (e_an.and e_W)
  obtain ⟨radius', hradius'_pos, hball_sub⟩ := Metric.mem_nhds_iff.mp e_all
  -- the inverse-chart quotient `β = dslope lInv 0`
  set β : ℂ → ℂ := dslope lInv 0 with hβ_def
  have hβ0 : β 0 = 1 := by
    rw [hβ_def, dslope_same, hlInv_sd0.hasDerivAt.deriv, hderiv, inv_one]
  have hbeta_form : ∀ w ∈ Metric.ball (0:ℂ) radius', w ≠ 0 → lInv w = ξ + w * β w := by
    intro w _ hwne
    rw [hβ_def, dslope_of_ne _ hwne, slope_def_field, hlInv0, sub_zero]
    field_simp
    ring
  have hbeta_ne : ∀ w ∈ Metric.ball (0:ℂ) radius', β w ≠ 0 := by
    intro w hw
    rcases eq_or_ne w 0 with rfl | hwne
    · rw [hβ0]; exact one_ne_zero
    · rw [hβ_def, dslope_of_ne _ hwne, slope_def_field, hlInv0, sub_zero]
      refine div_ne_zero ?_ hwne
      rw [sub_ne_zero]
      intro hcontra
      have hψlw : ψ (lInv w) = w := (hball_sub hw).1
      rw [hcontra, hψ_ξ] at hψlw
      exact hwne hψlw.symm
  have hbeta_an : AnalyticOnNhd ℂ β (Metric.ball (0:ℂ) radius') := by
    intro w hw
    rcases eq_or_ne w 0 with rfl | hwne
    · rw [hβ_def]
      obtain ⟨p, hp⟩ := hlInv_an00
      exact hp.has_fpower_series_dslope_fslope.analyticAt
    · rw [hβ_def]
      have hlInv_an_w : AnalyticAt ℂ lInv w := (hball_sub hw).2.1
      have hquot : AnalyticAt ℂ (fun z => (lInv z - lInv 0) / (z - 0)) w :=
        (hlInv_an_w.sub analyticAt_const).div (analyticAt_id.sub analyticAt_const)
          (by simpa using hwne)
      have hev : (fun z => (lInv z - lInv 0) / (z - 0)) =ᶠ[nhds w] dslope lInv 0 := by
        filter_upwards [isOpen_ne.mem_nhds hwne] with z hz
        rw [dslope_of_ne _ hz, slope_def_field]
      exact hquot.congr hev
  have hψ_contOn : ContinuousOn ψ W := AnalyticOnNhd.continuousOn hW_an
  refine ⟨{
    domain := W ∩ ψ ⁻¹' Metric.ball 0 radius'
    radius' := radius'
    ψ := ψ
    ψinv := lInv
    domain_isOpen := hψ_contOn.isOpen_inter_preimage hW_open Metric.isOpen_ball
    center_mem := ⟨hξW, by
      rw [Set.mem_preimage, hψ_ξ]; exact Metric.mem_ball_self hradius'_pos⟩
    radius'_pos := hradius'_pos
    ψ_analytic := fun z hz => hW_an z hz.1
    ψ_center := hψ_ξ
    ψ_deriv_one := hderiv
    biholo_left := fun z hz => hW_left z hz.1
    biholo_right := fun w hw => ⟨(hball_sub hw).1, (hball_sub hw).2.2, by
      rw [Set.mem_preimage, (hball_sub hw).1]; exact hw⟩
    maps_onto := by
      apply Set.eq_of_subset_of_subset
      · rintro y ⟨z, hz, rfl⟩; exact hz.2
      · intro w hw
        exact ⟨lInv w, ⟨(hball_sub hw).2.2, by
          rw [Set.mem_preimage, (hball_sub hw).1]; exact hw⟩, (hball_sub hw).1⟩
    normal_form := by
      intro z hz hzξ
      have hznf : H z = g z * (z - ξ) ^ (-(m:ℤ)) := hW_nf z hz.1 hzξ
      have hη_zm : (η z) ^ (-(m:ℤ)) = g z / c0 := by
        simp only [hη_def]
        exact exp_neg_inv_mul_log_zpow hm (Complex.slitPlane_ne_zero (hW_sp z hz.1))
      rw [hznf]
      simp only [hψ_def]
      rw [mul_zpow, hη_zm]
      field_simp
    beta_analytic_ne := ⟨β, hbeta_an, hβ0, hbeta_ne, hbeta_form⟩ }⟩

/-- The exact selected-arc value (`lem:arc-structure`(c)): along the arc
`ρ ↦ ψ⁻¹(ρ e^{iθ})` at the distinguished odd-`π` angle `θ = (arg c0 - π/2)/m`, the level
function takes the exact value `H = i·‖c0‖·ρ^{-m}`.  This is the analytic heart of the
selected-arc data (`sign = +1`). -/
theorem poleChart_selectedArc_value {H : ℂ -> ℂ} {ξ : ℂ} {m : ℕ} {c0 : ℂ}
    (chart : PoleChart H ξ m c0) (hm : 1 ≤ m) (hc0 : c0 ≠ 0) {ρ : ℝ}
    (hρ : 0 < ρ) (hρlt : ρ < chart.radius') :
    H (chart.ψinv ((ρ:ℂ) *
        Complex.exp ((((Complex.arg c0 - Real.pi / 2) / (m:ℝ) : ℝ) : ℂ) * Complex.I)))
      = (‖c0‖ : ℂ) * Complex.I * (ρ:ℂ) ^ (-(m:ℤ)) := by
  have hmr_pos : (0:ℝ) < (m:ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm
  have hmr : (m:ℝ) ≠ 0 := ne_of_gt hmr_pos
  set θ : ℝ := (Complex.arg c0 - Real.pi / 2) / (m:ℝ) with hθ_def
  set e : ℂ := Complex.exp ((θ:ℂ) * Complex.I) with he_def
  have he_ne : e ≠ 0 := by rw [he_def]; exact Complex.exp_ne_zero _
  have he_norm : ‖e‖ = 1 := by
    rw [he_def, Complex.norm_exp]; simp
  have he_pow : e ^ (-(m:ℤ)) = Complex.exp (-(m:ℂ) * (θ:ℂ) * Complex.I) := by
    rw [he_def, ← Complex.exp_int_mul]; congr 1; push_cast; ring
  have hangle : Complex.arg c0 - (m:ℝ) * θ = Real.pi / 2 := by
    rw [hθ_def]; field_simp; ring
  have hangleC : (Complex.arg c0 : ℂ) - (m:ℂ) * (θ:ℂ) = ((Real.pi / 2 : ℝ) : ℂ) := by
    rw [show ((Real.pi / 2 : ℝ) : ℂ) = ((Complex.arg c0 - (m:ℝ) * θ : ℝ) : ℂ) from by rw [hangle]]
    push_cast; ring
  have hkey : c0 * e ^ (-(m:ℤ)) = (‖c0‖ : ℂ) * Complex.I := by
    rw [he_pow]
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I c0]
    rw [mul_assoc, ← Complex.exp_add,
      show (Complex.arg c0 : ℂ) * Complex.I + -(m:ℂ) * (θ:ℂ) * Complex.I
          = ((Complex.arg c0 : ℂ) - (m:ℂ) * (θ:ℂ)) * Complex.I from by ring,
      hangleC,
      show ((Real.pi / 2 : ℝ) : ℂ) * Complex.I = (Real.pi : ℂ) / 2 * Complex.I from by
        push_cast; ring,
      Complex.exp_pi_div_two_mul_I]
  have hmem : (ρ:ℂ) * e ∈ Metric.ball (0:ℂ) chart.radius' := by
    rw [Metric.mem_ball, dist_zero_right, norm_mul, he_norm, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hρ]
    exact hρlt
  have hbi := chart.biholo_right ((ρ:ℂ) * e) hmem
  have hne : chart.ψinv ((ρ:ℂ) * e) ≠ ξ := by
    intro h
    have hψ0 : chart.ψ (chart.ψinv ((ρ:ℂ) * e)) = (ρ:ℂ) * e := hbi.1
    rw [h, chart.ψ_center] at hψ0
    exact (mul_ne_zero (by exact_mod_cast hρ.ne') he_ne) hψ0.symm
  have hH := chart.normal_form (chart.ψinv ((ρ:ℂ) * e)) hbi.2 hne
  rw [hH, hbi.1, mul_zpow,
    show c0 * ((ρ:ℂ) ^ (-(m:ℤ)) * e ^ (-(m:ℤ)))
        = (ρ:ℂ) ^ (-(m:ℤ)) * (c0 * e ^ (-(m:ℤ))) from by ring,
    hkey]
  ring

/-- `lem:arc-structure`(e) selected-arc data, exact-value form (the
sequence-window carrier demanded by `rem:successor-pole-target`). -/
structure SelectedArcData (H : ℂ -> ℂ) (ξ : ℂ) (m : Nat) (c0 : ℂ) : Type where
  chart : PoleChart H ξ m c0
  arcRadius : ℝ
  arcRadius_pos : 0 < arcRadius
  arcRadius_lt : arcRadius < chart.radius'
  arc : ℝ -> ℂ
  angle : ℝ
  sign : ℤ
  sign_sq : sign * sign = 1
  Nstar : ℕ
  rho : ℕ -> ℝ
  rho_formula : ∀ n, rho n
    = (‖c0‖ / (((2 * (Nstar + n) + 1 : ℕ) : ℝ) * Real.pi)) ^ ((m:ℝ)⁻¹)
  rho_pos : ∀ n, 0 < rho n
  rho_le : ∀ n, rho n ≤ arcRadius
  rho_strictAnti : StrictAnti rho
  rho_tendsto_zero : Tendsto rho atTop (nhdsWithin 0 {ρ : ℝ | 0 < ρ})
  arc_eq : ∀ ρ : ℝ, 0 < ρ -> ρ ≤ arcRadius ->
    arc ρ = chart.ψinv ((ρ : ℂ) * Complex.exp ((angle : ℂ) * Complex.I))
  arc_value_exact :
    ∀ ρ : ℝ, 0 < ρ -> ρ ≤ arcRadius ->
      H (arc ρ) = (sign : ℂ) * Complex.I * (‖c0‖ : ℂ) * (ρ : ℂ) ^ (-(m:ℤ))
  sigma_value_exact :
    ∀ n, H (arc (rho n))
      = (sign : ℂ) * (((2 * (Nstar + n) + 1 : ℕ) : ℂ)) * (Real.pi : ℂ) * Complex.I
  sigma_mem_pi : ∀ n, H (arc (rho n)) ∈ Pi
  sigma_ne_center : ∀ n, arc (rho n) ≠ ξ
  sigma_tendsto : Tendsto (fun n => arc (rho n)) atTop (nhds ξ)
  sigma_injective : Function.Injective (fun n => arc (rho n))

/-- `lem:arc-structure`(e): a Laurent normal form of pole order `m ≥ 1` yields the full
selected-arc data — the distinguished odd-`π` arc `γ(ρ) = ψ⁻¹(ρ e^{iθ})` together with the
exact selected radii `ρ_n = (‖c0‖/((2(N*+n)+1)π))^{1/m}`. -/
theorem selectedArcData_of_normalForm {H : ℂ -> ℂ} {ξ : ℂ} {m : ℕ} {c0 : ℂ} (hm : 1 ≤ m)
    {ρ0 : ℝ} (hρ0 : 0 < ρ0)
    (hHol : AnalyticOnNhd ℂ H (puncturedDisc ξ ρ0))
    (hNF : LaurentNormalFormAt H ξ (m : ℤ) c0) :
    Nonempty (SelectedArcData H ξ m c0) := by
  classical
  obtain ⟨chart⟩ := poleChart_of_normalForm hm hρ0 hHol hNF
  obtain ⟨β, hβ_an, hβ0, hβ_ne, hβ_form⟩ := chart.beta_analytic_ne
  have hc0 : c0 ≠ 0 := hNF.coeff_ne_zero
  have hc0n : (0:ℝ) < ‖c0‖ := norm_pos_iff.mpr hc0
  have hc0nc : (‖c0‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hc0n)
  have hmr_pos : (0:ℝ) < (m:ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm
  have hmr : (m:ℝ) ≠ 0 := ne_of_gt hmr_pos
  have hmn : m ≠ 0 := by omega
  have hminv_pos : (0:ℝ) < (m:ℝ)⁻¹ := inv_pos.mpr hmr_pos
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hR : (0:ℝ) < chart.radius' := chart.radius'_pos
  set arcRadius : ℝ := chart.radius' / 2 with harcR_def
  have harcR_pos : 0 < arcRadius := by rw [harcR_def]; linarith
  have harcR_lt : arcRadius < chart.radius' := by rw [harcR_def]; linarith
  have harm_pos : (0:ℝ) < arcRadius ^ m := pow_pos harcR_pos m
  set θ : ℝ := (Complex.arg c0 - Real.pi / 2) / (m:ℝ) with hθ_def
  set e : ℂ := Complex.exp ((θ:ℂ) * Complex.I) with he_def
  have he_ne : e ≠ 0 := by rw [he_def]; exact Complex.exp_ne_zero _
  have he_norm : ‖e‖ = 1 := by rw [he_def, Complex.norm_exp]; simp
  set arc : ℝ → ℂ := fun ρ => chart.ψinv ((ρ:ℂ) * e) with harc_fn
  have hmemball : ∀ ρ : ℝ, 0 < ρ → ρ < chart.radius' →
      (ρ:ℂ) * e ∈ Metric.ball (0:ℂ) chart.radius' := by
    intro ρ hρ hρlt
    rw [Metric.mem_ball, dist_zero_right, norm_mul, he_norm, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hρ]
    exact hρlt
  have hψarc : ∀ ρ : ℝ, 0 < ρ → ρ < chart.radius' → chart.ψ (arc ρ) = (ρ:ℂ) * e :=
    fun ρ hρ hρlt => (chart.biholo_right ((ρ:ℂ)*e) (hmemball ρ hρ hρlt)).1
  have harc_ne : ∀ ρ : ℝ, 0 < ρ → ρ < chart.radius' → arc ρ ≠ ξ := by
    intro ρ hρ hρlt h
    have hp := hψarc ρ hρ hρlt
    rw [h, chart.ψ_center] at hp
    exact (mul_ne_zero (by exact_mod_cast hρ.ne') he_ne) hp.symm
  -- pick `Nstar`
  obtain ⟨Nstar, hNstar⟩ :
      ∃ N : ℕ, ‖c0‖ / (arcRadius ^ m * Real.pi) < ((2 * N + 1 : ℕ) : ℝ) := by
    obtain ⟨N, hN⟩ := exists_nat_gt (‖c0‖ / (arcRadius ^ m * Real.pi))
    exact ⟨N, lt_of_lt_of_le hN (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) N])⟩
  set D : ℕ → ℝ := fun n => ((2 * (Nstar + n) + 1 : ℕ) : ℝ) * Real.pi with hD_def
  have hDpos : ∀ n, 0 < D n := fun n => by rw [hD_def]; positivity
  set rho : ℕ → ℝ := fun n => (‖c0‖ / D n) ^ ((m:ℝ)⁻¹) with hrho_def
  have hbase_pos : ∀ n, 0 < ‖c0‖ / D n := fun n => div_pos hc0n (hDpos n)
  have hrho_pos : ∀ n, 0 < rho n := fun n => Real.rpow_pos_of_pos (hbase_pos n) _
  have hNstar' : ‖c0‖ < ((2 * Nstar + 1 : ℕ) : ℝ) * (arcRadius ^ m * Real.pi) := by
    rw [div_lt_iff₀ (by positivity)] at hNstar; linarith [hNstar]
  have hbase_le : ∀ n, ‖c0‖ / D n ≤ arcRadius ^ m := by
    intro n
    rw [div_le_iff₀ (hDpos n)]
    have h1 : ((2 * Nstar + 1 : ℕ) : ℝ) ≤ ((2 * (Nstar + n) + 1 : ℕ) : ℝ) := by
      have : 2 * Nstar + 1 ≤ 2 * (Nstar + n) + 1 := by omega
      exact_mod_cast this
    have hlt : ‖c0‖ < arcRadius ^ m * D n := by
      calc ‖c0‖ < ((2 * Nstar + 1 : ℕ) : ℝ) * (arcRadius ^ m * Real.pi) := hNstar'
        _ ≤ ((2 * (Nstar + n) + 1 : ℕ) : ℝ) * (arcRadius ^ m * Real.pi) :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = arcRadius ^ m * D n := by rw [hD_def]; ring
    linarith
  have hrho_le : ∀ n, rho n ≤ arcRadius := by
    intro n
    rw [hrho_def]
    calc (‖c0‖ / D n) ^ ((m:ℝ)⁻¹) ≤ (arcRadius ^ m) ^ ((m:ℝ)⁻¹) :=
          Real.rpow_le_rpow (hbase_pos n).le (hbase_le n) hminv_pos.le
      _ = arcRadius := Real.pow_rpow_inv_natCast harcR_pos.le hmn
  have hrho_anti : StrictAnti rho := by
    apply strictAnti_nat_of_succ_lt
    intro n
    rw [hrho_def]
    have hDlt : D n < D (n + 1) := by
      rw [hD_def]
      have hc : ((2 * (Nstar + n) + 1 : ℕ) : ℝ) < ((2 * (Nstar + (n + 1)) + 1 : ℕ) : ℝ) := by
        have : 2 * (Nstar + n) + 1 < 2 * (Nstar + (n + 1)) + 1 := by omega
        exact_mod_cast this
      exact mul_lt_mul_of_pos_right hc hpi
    exact Real.rpow_lt_rpow (hbase_pos (n+1)).le
      (div_lt_div_of_pos_left hc0n (hDpos n) hDlt) hminv_pos
  -- the radii tend to `0`
  have hD_tendsto : Tendsto D atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => 2 * (Nstar + n) + 1) atTop atTop :=
      tendsto_atTop_mono (fun n => by simp only [id_eq]; omega) tendsto_id
    have h2 : Tendsto (fun n : ℕ => ((2 * (Nstar + n) + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp h1
    rw [hD_def]; exact h2.atTop_mul_const hpi
  have hrho_tendsto0 : Tendsto rho atTop (nhds 0) := by
    have hb : Tendsto (fun n => ‖c0‖ / D n) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hD_tendsto
    have := hb.rpow_const (Or.inr hminv_pos.le)
    rwa [Real.zero_rpow (ne_of_gt hminv_pos)] at this
  have hrho_tendsto : Tendsto rho atTop (nhdsWithin (0:ℝ) {ρ : ℝ | 0 < ρ}) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hrho_tendsto0, Filter.Eventually.of_forall hrho_pos⟩
  -- the exact selected values
  have hrho_zpow : ∀ n, (↑(rho n) : ℂ) ^ (-(m:ℤ))
      = ((2 * (Nstar + n) + 1 : ℕ) : ℂ) * (Real.pi : ℂ) / (‖c0‖ : ℂ) := by
    intro n
    have hrhopow : (rho n) ^ m = ‖c0‖ / D n := by
      simp only [hrho_def]; exact Real.rpow_inv_natCast_pow (hbase_pos n).le hmn
    rw [_root_.zpow_neg, zpow_natCast, ← Complex.ofReal_pow, hrhopow]
    simp only [hD_def]
    rw [Complex.ofReal_div, inv_div]
    push_cast
    ring
  have hsigma_val : ∀ n, H (arc (rho n))
      = ((2 * (Nstar + n) + 1 : ℕ) : ℂ) * (Real.pi : ℂ) * Complex.I := by
    intro n
    have hρlt : rho n < chart.radius' := lt_of_le_of_lt (hrho_le n) harcR_lt
    have hv : H (arc (rho n)) = (‖c0‖ : ℂ) * Complex.I * (↑(rho n) : ℂ) ^ (-(m:ℤ)) :=
      poleChart_selectedArc_value chart hm hc0 (hrho_pos n) hρlt
    rw [hv, hrho_zpow n]
    field_simp
  have hsigma_pi : ∀ n, H (arc (rho n)) ∈ Pi := by
    intro n
    rw [hsigma_val n, show (Pi : Set ℂ) = oddPiI from sigmoidPoleSet_eq_oddPiI]
    exact ⟨((Nstar + n : ℕ) : ℤ), by push_cast; ring⟩
  have hsigma_ne : ∀ n, arc (rho n) ≠ ξ :=
    fun n => harc_ne (rho n) (hrho_pos n) (lt_of_le_of_lt (hrho_le n) harcR_lt)
  have harc_sub : ∀ n, arc (rho n) - ξ = (↑(rho n) : ℂ) * e * β ((↑(rho n) : ℂ) * e) := by
    intro n
    have hmem := hmemball (rho n) (hrho_pos n) (lt_of_le_of_lt (hrho_le n) harcR_lt)
    have hne0 : (↑(rho n) : ℂ) * e ≠ 0 :=
      mul_ne_zero (by exact_mod_cast (hrho_pos n).ne') he_ne
    have hform := hβ_form ((↑(rho n) : ℂ) * e) hmem hne0
    show chart.ψinv ((↑(rho n) : ℂ) * e) - ξ = _
    rw [hform]; ring
  have hsigma_tendsto : Tendsto (fun n => arc (rho n)) atTop (nhds ξ) := by
    have hβT : Tendsto β (nhds (0:ℂ)) (nhds (β 0)) :=
      (hβ_an 0 (Metric.mem_ball_self hR)).continuousAt
    have h1 : Tendsto (fun n => (↑(rho n) : ℂ) * e) atTop (nhds 0) := by
      have hc : Tendsto (fun n => (↑(rho n) : ℂ)) atTop (nhds 0) := by
        simpa using (Complex.continuous_ofReal.tendsto (0:ℝ)).comp hrho_tendsto0
      simpa using hc.mul (tendsto_const_nhds (x := e))
    have h2 : Tendsto (fun n => β ((↑(rho n) : ℂ) * e)) atTop (nhds (β 0)) := hβT.comp h1
    have h3 : Tendsto (fun n => arc (rho n) - ξ) atTop (nhds 0) := by
      have hprod := h1.mul h2
      simp only [zero_mul] at hprod
      exact hprod.congr (fun n => (harc_sub n).symm)
    have h4 := (tendsto_const_nhds (x := ξ)).add h3
    rw [add_zero] at h4
    exact h4.congr (fun n => by ring)
  have hsigma_inj : Function.Injective (fun n => arc (rho n)) := by
    intro a b hab
    have hab' : arc (rho a) = arc (rho b) := hab
    have hψa := hψarc (rho a) (hrho_pos a) (lt_of_le_of_lt (hrho_le a) harcR_lt)
    have hψb := hψarc (rho b) (hrho_pos b) (lt_of_le_of_lt (hrho_le b) harcR_lt)
    rw [hab', hψb] at hψa
    have he : (↑(rho b) : ℂ) = (↑(rho a) : ℂ) := mul_right_cancel₀ he_ne hψa
    have hrhoab : rho b = rho a := by exact_mod_cast he
    exact (hrho_anti.injective hrhoab).symm
  exact ⟨{
    chart := chart
    arcRadius := arcRadius
    arcRadius_pos := harcR_pos
    arcRadius_lt := harcR_lt
    arc := arc
    angle := θ
    sign := 1
    sign_sq := by norm_num
    Nstar := Nstar
    rho := rho
    rho_formula := fun n => rfl
    rho_pos := hrho_pos
    rho_le := hrho_le
    rho_strictAnti := hrho_anti
    rho_tendsto_zero := hrho_tendsto
    arc_eq := fun ρ _ _ => rfl
    arc_value_exact := fun ρ hρ hρle => by
      have hρlt : ρ < chart.radius' := lt_of_le_of_lt hρle harcR_lt
      have hv : H (arc ρ) = (‖c0‖ : ℂ) * Complex.I * (ρ : ℂ) ^ (-(m:ℤ)) :=
        poleChart_selectedArc_value chart hm hc0 hρ hρlt
      rw [hv]; push_cast; ring
    sigma_value_exact := fun n => by rw [hsigma_val n]; push_cast; ring
    sigma_mem_pi := hsigma_pi
    sigma_ne_center := hsigma_ne
    sigma_tendsto := hsigma_tendsto
    sigma_injective := hsigma_inj }⟩

/-- `lem:arc-pullback` (exact-order pullback of any Laurent normal form along the
selected arc, with a continuous vanishing remainder). -/
theorem arc_pullback {H : ℂ -> ℂ} {ξ : ℂ} {m : Nat} {c0 : ℂ}
    (A : SelectedArcData H ξ m c0)
    {G : ℂ -> ℂ} {μ : ℤ} {c : ℂ} (hG : LaurentNormalFormAt G ξ μ c) :
    ∃ B : ℝ -> ℂ, ContinuousOn B (Set.Icc 0 A.arcRadius) ∧ B 0 = 0 ∧
      ∃ ρ1 : ℝ, 0 < ρ1 ∧ ρ1 ≤ A.arcRadius ∧
      ∀ ρ : ℝ, 0 < ρ -> ρ ≤ ρ1 ->
        G (A.arc ρ)
          = (ρ:ℂ) ^ (-μ) *
            (c * Complex.exp (-(μ:ℂ) * (A.angle : ℂ) * Complex.I) + B ρ) := by
  classical
  obtain ⟨β, hβ_an, hβ0, hβ_ne, hβ_form⟩ := A.chart.beta_analytic_ne
  obtain ⟨g, hg_an, hgξ, hg_eq⟩ := hG.factored
  set rr : ℝ := A.arcRadius with hrr
  set R : ℝ := A.chart.radius' with hRR
  have hrr_pos : 0 < rr := A.arcRadius_pos
  have hrr_lt : rr < R := A.arcRadius_lt
  have hR_pos : 0 < R := lt_trans hrr_pos hrr_lt
  set ε : ℂ := Complex.exp ((A.angle : ℂ) * Complex.I) with hε_def
  set E : ℂ := Complex.exp (-(μ:ℂ) * (A.angle : ℂ) * Complex.I) with hE_def
  have hε_ne : ε ≠ 0 := by rw [hε_def]; exact Complex.exp_ne_zero _
  have hε_norm : ‖ε‖ = 1 := by
    rw [hε_def, Complex.norm_exp]
    have hre : ((A.angle : ℂ) * Complex.I).re = 0 := by
      rw [Complex.mul_I_re]; simp
    rw [hre, Real.exp_zero]
  have hε_pow : ε ^ (-μ) = E := by
    rw [hε_def, hE_def, ← Complex.exp_int_mul]
    congr 1
    push_cast; ring
  -- Membership of `(t)·ε` in the chart disc for `0 ≤ t < R`.
  have hmem_ball : ∀ t : ℝ, 0 ≤ t → t < R → (t : ℂ) * ε ∈ Metric.ball (0:ℂ) R := by
    intro t ht0 htR
    rw [Metric.mem_ball, dist_zero_right, norm_mul, hε_norm, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    exact htR
  -- The selected arc, minus the centre, in explicit `β`-form.
  have harc_sub : ∀ ρ : ℝ, 0 < ρ → ρ ≤ rr →
      A.arc ρ - ξ = (ρ : ℂ) * ε * β ((ρ : ℂ) * ε) := by
    intro ρ hρ hρle
    have hball : (ρ : ℂ) * ε ∈ Metric.ball (0:ℂ) R :=
      hmem_ball ρ hρ.le (lt_of_le_of_lt hρle hrr_lt)
    have hne : (ρ : ℂ) * ε ≠ 0 := mul_ne_zero (by exact_mod_cast hρ.ne') hε_ne
    have hform := hβ_form ((ρ:ℂ)*ε) hball hne
    have harc := A.arc_eq ρ hρ hρle
    rw [← hε_def] at harc
    rw [harc, hform]; ring
  have harc_ne : ∀ ρ : ℝ, 0 < ρ → ρ ≤ rr → A.arc ρ ≠ ξ := by
    intro ρ hρ hρle hEq
    have hsub := harc_sub ρ hρ hρle
    rw [hEq, sub_self] at hsub
    have hne : (ρ : ℂ) * ε * β ((ρ:ℂ)*ε) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by exact_mod_cast hρ.ne') hε_ne)
        (hβ_ne ((ρ:ℂ)*ε) (hmem_ball ρ hρ.le (lt_of_le_of_lt hρle hrr_lt)))
    exact hne hsub.symm
  -- The extended arc map `α`.
  set α : ℝ → ℂ := fun t => ξ + (t : ℂ) * ε * β ((t : ℂ) * ε) with hα_def
  have hα0 : α 0 = ξ := by rw [hα_def]; simp
  have hα_arc : ∀ ρ : ℝ, 0 < ρ → ρ ≤ rr → α ρ = A.arc ρ := by
    intro ρ hρ hρle
    rw [hα_def]
    simp only []
    rw [← harc_sub ρ hρ hρle]; ring
  have hα_contAt : ContinuousAt α 0 := by
    rw [hα_def]
    have hin : ContinuousAt (fun t : ℝ => (t:ℂ)*ε) 0 :=
      (Complex.continuous_ofReal.continuousAt).mul continuousAt_const
    have hβ_ca : ContinuousAt β (0 : ℂ) :=
      (hβ_an.continuousOn).continuousAt (Metric.ball_mem_nhds (0:ℂ) hR_pos)
    have hcomp : ContinuousAt (fun t : ℝ => β ((t:ℂ)*ε)) 0 :=
      ContinuousAt.comp_of_eq (g := β) (f := fun t : ℝ => (t:ℂ)*ε) hβ_ca hin (by simp)
    exact continuousAt_const.add (hin.mul hcomp)
  have hα_tend : Tendsto α (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds ξ) := by
    have h : Tendsto α (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (α 0)) :=
      hα_contAt.continuousWithinAt
    rw [hα0] at h; exact h
  -- Open set where `g` is analytic (hence continuous).
  obtain ⟨U, hU_an, hU_open, hU_mem⟩ := eventually_nhds_iff.mp hg_an.eventually_analyticAt
  have hg_on_U : ContinuousOn g U := AnalyticOnNhd.continuousOn hU_an
  -- Eventual facts near `0⁺`.
  have hlt : ∀ᶠ ρ in nhdsWithin (0:ℝ) (Set.Ioi 0), ρ < rr :=
    (Filter.eventually_of_mem (Iio_mem_nhds hrr_pos) fun _ hx => hx).filter_mono
      nhdsWithin_le_nhds
  have hUev : ∀ᶠ ρ in nhdsWithin (0:ℝ) (Set.Ioi 0), α ρ ∈ U :=
    hα_tend.eventually (hU_open.mem_nhds hU_mem)
  have harc_tendsto : Tendsto A.arc (nhdsWithin (0:ℝ) (Set.Ioi 0))
      (nhdsWithin ξ ({ξ}ᶜ : Set ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hα_tend.congr' ?_, ?_⟩
    · filter_upwards [self_mem_nhdsWithin, hlt] with ρ hρpos hρlt
      exact hα_arc ρ hρpos (le_of_lt hρlt)
    · filter_upwards [self_mem_nhdsWithin, hlt] with ρ hρpos hρlt
      exact harc_ne ρ hρpos (le_of_lt hρlt)
  have hLaurev : ∀ᶠ ρ in nhdsWithin (0:ℝ) (Set.Ioi 0),
      G (A.arc ρ) = g (A.arc ρ) * (A.arc ρ - ξ) ^ (-μ) :=
    harc_tendsto.eventually hg_eq
  have hev : ∀ᶠ ρ in nhdsWithin (0:ℝ) (Set.Ioi 0),
      ρ < rr ∧ α ρ ∈ U ∧ G (A.arc ρ) = g (A.arc ρ) * (A.arc ρ - ξ) ^ (-μ) :=
    hlt.and (hUev.and hLaurev)
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.mem_nhdsWithin_iff.mp hev
  set ρ1 : ℝ := min (δ/2) rr with hρ1_def
  have hρ1_pos : 0 < ρ1 := lt_min (by linarith) hrr_pos
  have hρ1_le : ρ1 ≤ rr := min_le_right _ _
  have hρ1_ltδ : ρ1 < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hαU : ∀ t : ℝ, 0 ≤ t → t ≤ ρ1 → α t ∈ U := by
    intro t ht0 htρ1
    rcases lt_or_eq_of_le ht0 with h0 | h0
    · have hmem : t ∈ Metric.ball (0:ℝ) δ ∩ Set.Ioi 0 := by
        refine ⟨?_, h0⟩
        rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos h0]
        exact lt_of_le_of_lt htρ1 hρ1_ltδ
      exact (hδ_sub hmem).2.1
    · rw [← h0, hα0]; exact hU_mem
  -- The building blocks of the remainder function.
  set s : ℝ → ℝ := fun ρ => min ρ ρ1 with hs_def
  set w : ℝ → ℂ := fun ρ => (s ρ : ℂ) * ε with hw_def
  set P : ℝ → ℂ := fun ρ => ξ + w ρ * β (w ρ) with hP_def
  set bpow : ℝ → ℂ := fun ρ => (β (w ρ)) ^ (-μ) with hbpow_def
  have hs_cont : Continuous s := by rw [hs_def]; exact continuous_id.min continuous_const
  have hw_cont : Continuous w := by
    rw [hw_def]; exact (Complex.continuous_ofReal.comp hs_cont).mul continuous_const
  have hs_nonneg : ∀ ρ ∈ Set.Icc (0:ℝ) rr, 0 ≤ s ρ := by
    intro ρ hρ; exact le_min hρ.1 hρ1_pos.le
  have hs_le : ∀ ρ, s ρ ≤ ρ1 := by intro ρ; exact min_le_right _ _
  have hw_maps : Set.MapsTo w (Set.Icc (0:ℝ) rr) (Metric.ball (0:ℂ) R) := by
    intro ρ hρ
    exact hmem_ball (s ρ) (hs_nonneg ρ hρ)
      (lt_of_le_of_lt (le_trans (hs_le ρ) hρ1_le) hrr_lt)
  have hβw_cont : ContinuousOn (fun ρ => β (w ρ)) (Set.Icc (0:ℝ) rr) :=
    (hβ_an.continuousOn).comp hw_cont.continuousOn hw_maps
  have hP_cont : ContinuousOn P (Set.Icc (0:ℝ) rr) := by
    rw [hP_def]
    exact continuousOn_const.add (hw_cont.continuousOn.mul hβw_cont)
  have hP_maps : Set.MapsTo P (Set.Icc (0:ℝ) rr) U := by
    intro ρ hρ
    have : P ρ = α (s ρ) := rfl
    rw [this]
    exact hαU (s ρ) (hs_nonneg ρ hρ) (hs_le ρ)
  have hgP_cont : ContinuousOn (fun ρ => g (P ρ)) (Set.Icc (0:ℝ) rr) :=
    hg_on_U.comp hP_cont hP_maps
  have hbpow_cont : ContinuousOn bpow (Set.Icc (0:ℝ) rr) := by
    rw [hbpow_def]
    exact hβw_cont.zpow₀ (-μ) (fun ρ hρ => Or.inl (hβ_ne (w ρ) (hw_maps hρ)))
  refine ⟨fun ρ => E * (g (P ρ) * bpow ρ - c), ?_, ?_, ⟨ρ1, hρ1_pos, hρ1_le, ?_⟩⟩
  · -- continuity
    exact continuousOn_const.mul ((hgP_cont.mul hbpow_cont).sub continuousOn_const)
  · -- value at 0
    show E * (g (P 0) * bpow 0 - c) = 0
    have hs0 : s 0 = 0 := by simp only [hs_def]; exact min_eq_left hρ1_pos.le
    have hw0 : w 0 = 0 := by simp only [hw_def, hs0, Complex.ofReal_zero, zero_mul]
    have hP0 : P 0 = ξ := by simp only [hP_def, hw0, hβ0]; simp
    have hbpow0 : bpow 0 = 1 := by
      simp only [hbpow_def, hw0, hβ0]; exact one_zpow _
    rw [hP0, hgξ, hbpow0]; ring
  · -- the exact-order identity
    intro ρ hρ hρρ1
    have hρrr : ρ ≤ rr := le_trans hρρ1 hρ1_le
    have hmemρ : ρ ∈ Metric.ball (0:ℝ) δ ∩ Set.Ioi 0 := by
      refine ⟨?_, hρ⟩
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hρ]
      exact lt_of_le_of_lt hρρ1 hρ1_ltδ
    have hLaur := (hδ_sub hmemρ).2.2
    have hsρ : s ρ = ρ := by simp only [hs_def]; exact min_eq_left hρρ1
    have hwρ : w ρ = (ρ:ℂ) * ε := by simp only [hw_def, hsρ]
    have hPρ : P ρ = A.arc ρ := by
      simp only [hP_def, hwρ]; rw [← harc_sub ρ hρ hρrr]; ring
    have hbpowρ : bpow ρ = (β ((ρ:ℂ)*ε)) ^ (-μ) := by simp only [hbpow_def, hwρ]
    have hsub := harc_sub ρ hρ hρrr
    show G (A.arc ρ) = (ρ:ℂ) ^ (-μ) * (c * E + E * (g (P ρ) * bpow ρ - c))
    rw [hLaur, hsub, hPρ, hbpowρ, mul_zpow, mul_zpow, hε_pow]
    ring

/-- The selected-arc package supplies the accumulation of odd-`π` preimages directly:
the exact selected sequence `n ↦ arc (rho n)` gives infinitely many `Π`-preimages in
every punctured neighbourhood of `ξ`.  This is the direct downgrade that keeps
`lem_level_preimage` usable from the strengthened arc data (`lem:arc-structure`(e) ⇒
`cor:level-preimage`), without passing through the legacy `ArcStructureResult`. -/
theorem SelectedArcData.toLevelPreimageResult {H : ℂ -> ℂ} {ξ : ℂ} {m : Nat} {c0 : ℂ}
    (A : SelectedArcData H ξ m c0) : LevelPreimageResult H ξ := by
  refine ⟨?_⟩
  intro ε hε
  have heventually_ball :
      ∀ᶠ n in atTop, A.arc (A.rho n) ∈ Metric.ball ξ ε :=
    A.sigma_tendsto (Metric.ball_mem_nhds ξ hε)
  rcases Filter.eventually_atTop.1 heventually_ball with ⟨N, hN⟩
  refine Set.infinite_of_injective_forall_mem
    (s := levelPreimageIn H ξ ε)
    (f := fun n : ℕ => A.arc (A.rho (N + n))) ?_ ?_
  · intro n n' hnn'
    exact Nat.add_left_cancel (A.sigma_injective hnn')
  · intro n
    have hball : A.arc (A.rho (N + n)) ∈ Metric.ball ξ ε := hN (N + n) (by omega)
    exact ⟨⟨A.sigma_ne_center (N + n), by simpa [Metric.mem_ball] using hball⟩,
      A.sigma_mem_pi (N + n)⟩


/-- General selected-arc value: along `t ↦ ψ⁻¹(t·e^{iφ})` the level function takes the
value `H = c0 · e^{-i m φ} · t^{-m}` for **any** real angle `φ` and radius `0 < t < radius'`.
The distinguished-angle specialization is `poleChart_selectedArc_value`. -/
theorem poleChart_arc_value_general {H : ℂ -> ℂ} {ξ : ℂ} {m : ℕ} {c0 : ℂ}
    (chart : PoleChart H ξ m c0) {φ t : ℝ} (ht : 0 < t) (htlt : t < chart.radius') :
    H (chart.ψinv ((t : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)))
      = c0 * Complex.exp (-(m:ℂ) * (φ : ℂ) * Complex.I) * (t : ℂ) ^ (-(m:ℤ)) := by
  set e : ℂ := Complex.exp ((φ : ℂ) * Complex.I) with he_def
  have he_ne : e ≠ 0 := by rw [he_def]; exact Complex.exp_ne_zero _
  have he_norm : ‖e‖ = 1 := by rw [he_def, Complex.norm_exp]; simp
  have he_pow : e ^ (-(m:ℤ)) = Complex.exp (-(m:ℂ) * (φ : ℂ) * Complex.I) := by
    rw [he_def, ← Complex.exp_int_mul]; congr 1; push_cast; ring
  have hmem : (t : ℂ) * e ∈ Metric.ball (0:ℂ) chart.radius' := by
    rw [Metric.mem_ball, dist_zero_right, norm_mul, he_norm, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ht]
    exact htlt
  have hbi := chart.biholo_right ((t : ℂ) * e) hmem
  have hne : chart.ψinv ((t : ℂ) * e) ≠ ξ := by
    intro h
    have hψ0 : chart.ψ (chart.ψinv ((t : ℂ) * e)) = (t : ℂ) * e := hbi.1
    rw [h, chart.ψ_center] at hψ0
    exact (mul_ne_zero (by exact_mod_cast ht.ne') he_ne) hψ0.symm
  have hH := chart.normal_form (chart.ψinv ((t : ℂ) * e)) hbi.2 hne
  rw [hH, hbi.1, mul_zpow, he_pow]
  ring

/-- Reusable per-arc odd-`π` sequence builder.  From an exact odd-`π` value law
`H(γ(ρ)) = s·i·B·ρ^{-m}` (with `s² = 1`, `B > 0`) valid on `(0, R)` along a local arc `γ`
that tends to `ξ`, extract the consecutive selected radii
`ρ_n = (B/((2(N⋆+n)+1)π))^{1/m}` (shifted to a tail so the arc points sit in the
punctured disc), whose arc points are genuine punctured-disc `Π`-preimages tending to `ξ`. -/
noncomputable def levelArcPiSequence_of_exactValue {H : ℂ -> ℂ} {ξ : ℂ} {m : ℕ} (hm : 1 ≤ m)
    {R : ℝ} (hR : 0 < R) (ad : LevelArcData H ξ)
    {B : ℝ} (hB : 0 < B) {s : ℤ} (hs2 : s * s = 1)
    (hval : ∀ ρ : ℝ, 0 < ρ → ρ < R →
      H (ad.gamma ρ) = (s:ℂ) * Complex.I * (B:ℂ) * (ρ:ℂ) ^ (-(m:ℤ)))
    (hne : ∀ ρ : ℝ, 0 < ρ → ρ < R → ad.gamma ρ ≠ ξ) :
    LevelArcPiSequence H ξ R ad := by
  classical
  have hmr_pos : (0:ℝ) < (m:ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm
  have hmr : (m:ℝ) ≠ 0 := ne_of_gt hmr_pos
  have hmn : m ≠ 0 := by omega
  have hminv_pos : (0:ℝ) < (m:ℝ)⁻¹ := inv_pos.mpr hmr_pos
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hBc : (B:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hB)
  -- pick `Nstar` (extracted non-destructively since the goal is `Type`-valued)
  have hNstar_ex : ∃ N : ℕ, B / (R ^ m * Real.pi) < ((2 * N + 1 : ℕ) : ℝ) := by
    obtain ⟨N, hN⟩ := exists_nat_gt (B / (R ^ m * Real.pi))
    exact ⟨N, lt_of_lt_of_le hN (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) N])⟩
  set Nstar : ℕ := hNstar_ex.choose with hNstar_def
  have hNstar : B / (R ^ m * Real.pi) < ((2 * Nstar + 1 : ℕ) : ℝ) := by
    rw [hNstar_def]; exact hNstar_ex.choose_spec
  set D : ℕ → ℝ := fun n => ((2 * (Nstar + n) + 1 : ℕ) : ℝ) * Real.pi with hD_def
  have hDpos : ∀ n, 0 < D n := fun n => by rw [hD_def]; positivity
  set rho : ℕ → ℝ := fun n => (B / D n) ^ ((m:ℝ)⁻¹) with hrho_def
  have hbase_pos : ∀ n, 0 < B / D n := fun n => div_pos hB (hDpos n)
  have hrho_pos : ∀ n, 0 < rho n := fun n => Real.rpow_pos_of_pos (hbase_pos n) _
  have hNstar' : B < ((2 * Nstar + 1 : ℕ) : ℝ) * (R ^ m * Real.pi) := by
    rw [div_lt_iff₀ (by positivity)] at hNstar; linarith [hNstar]
  have hbase_lt : ∀ n, B / D n < R ^ m := by
    intro n
    rw [div_lt_iff₀ (hDpos n)]
    have h1 : ((2 * Nstar + 1 : ℕ) : ℝ) ≤ ((2 * (Nstar + n) + 1 : ℕ) : ℝ) := by
      have : 2 * Nstar + 1 ≤ 2 * (Nstar + n) + 1 := by omega
      exact_mod_cast this
    calc B < ((2 * Nstar + 1 : ℕ) : ℝ) * (R ^ m * Real.pi) := hNstar'
      _ ≤ ((2 * (Nstar + n) + 1 : ℕ) : ℝ) * (R ^ m * Real.pi) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = R ^ m * D n := by rw [hD_def]; ring
  have hrho_lt : ∀ n, rho n < R := by
    intro n
    rw [hrho_def]
    calc (B / D n) ^ ((m:ℝ)⁻¹) < (R ^ m) ^ ((m:ℝ)⁻¹) :=
          Real.rpow_lt_rpow (hbase_pos n).le (hbase_lt n) hminv_pos
      _ = R := Real.pow_rpow_inv_natCast hR.le hmn
  have hrho_le : ∀ n, rho n ≤ R := fun n => (hrho_lt n).le
  have hrho_anti : StrictAnti rho := by
    apply strictAnti_nat_of_succ_lt
    intro n
    rw [hrho_def]
    have hDlt : D n < D (n + 1) := by
      rw [hD_def]
      have hc : ((2 * (Nstar + n) + 1 : ℕ) : ℝ) < ((2 * (Nstar + (n + 1)) + 1 : ℕ) : ℝ) := by
        have : 2 * (Nstar + n) + 1 < 2 * (Nstar + (n + 1)) + 1 := by omega
        exact_mod_cast this
      exact mul_lt_mul_of_pos_right hc hpi
    exact Real.rpow_lt_rpow (hbase_pos (n+1)).le
      (div_lt_div_of_pos_left hB (hDpos n) hDlt) hminv_pos
  have hD_tendsto : Tendsto D atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => 2 * (Nstar + n) + 1) atTop atTop :=
      tendsto_atTop_mono (fun n => by simp only [id_eq]; omega) tendsto_id
    have h2 : Tendsto (fun n : ℕ => ((2 * (Nstar + n) + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp h1
    rw [hD_def]; exact h2.atTop_mul_const hpi
  have hrho_tendsto0 : Tendsto rho atTop (nhds 0) := by
    have hb : Tendsto (fun n => B / D n) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hD_tendsto
    have := hb.rpow_const (Or.inr hminv_pos.le)
    rwa [Real.zero_rpow (ne_of_gt hminv_pos)] at this
  have hrho_tendsto : Tendsto rho atTop (nhdsWithin (0:ℝ) {ρ : ℝ | 0 < ρ}) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hrho_tendsto0, Filter.Eventually.of_forall hrho_pos⟩
  have hrho_zpow : ∀ n, (↑(rho n) : ℂ) ^ (-(m:ℤ))
      = ((2 * (Nstar + n) + 1 : ℕ) : ℂ) * (Real.pi : ℂ) / (B : ℂ) := by
    intro n
    have hrhopow : (rho n) ^ m = B / D n := by
      simp only [hrho_def]; exact Real.rpow_inv_natCast_pow (hbase_pos n).le hmn
    rw [_root_.zpow_neg, zpow_natCast, ← Complex.ofReal_pow, hrhopow]
    simp only [hD_def]
    rw [Complex.ofReal_div, inv_div]
    push_cast
    ring
  have hval_n : ∀ n, H (ad.gamma (rho n))
      = (s:ℂ) * ((2 * (Nstar + n) + 1 : ℕ) : ℂ) * (Real.pi : ℂ) * Complex.I := by
    intro n
    have hv := hval (rho n) (hrho_pos n) (hrho_lt n)
    rw [hv, hrho_zpow n]
    have hrw : (s:ℂ) * Complex.I * (B:ℂ)
          * (((2 * (Nstar + n) + 1 : ℕ) : ℂ) * (Real.pi : ℂ) / (B : ℂ))
        = (s:ℂ) * ((2 * (Nstar + n) + 1 : ℕ) : ℂ) * (Real.pi : ℂ) * Complex.I
          * ((B:ℂ) / (B:ℂ)) := by ring
    rw [hrw, div_self hBc, mul_one]
  have hpi_mem : ∀ n, H (ad.gamma (rho n)) ∈ Pi := by
    intro n
    rw [show (Pi : Set ℂ) = oddPiI from sigmoidPoleSet_eq_oddPiI, hval_n n]
    rcases mul_self_eq_one_iff.mp hs2 with hs | hs
    · exact ⟨((Nstar + n : ℕ) : ℤ), by rw [hs]; push_cast; ring⟩
    · exact ⟨-((Nstar + n : ℕ) : ℤ) - 1, by rw [hs]; push_cast; ring⟩
  have hinj : Function.Injective (fun n : ℕ => ad.gamma (rho n)) := by
    intro a b hab
    have hva : H (ad.gamma (rho a)) = H (ad.gamma (rho b)) := congrArg H hab
    rw [hval_n a, hval_n b] at hva
    have hsc : (s:ℂ) ≠ 0 := by
      rcases mul_self_eq_one_iff.mp hs2 with hs | hs <;> rw [hs] <;> norm_num
    have hπc : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hpi)
    have hIc : Complex.I ≠ 0 := Complex.I_ne_zero
    have h2 := mul_left_cancel₀ hsc (mul_right_cancel₀ hπc (mul_right_cancel₀ hIc hva))
    have hnat : 2 * (Nstar + a) + 1 = 2 * (Nstar + b) + 1 := by exact_mod_cast h2
    omega
  -- tail shift so arc points sit inside the punctured disc
  have hgamma_tendsto : Tendsto (fun n => ad.gamma (rho n)) atTop (nhds ξ) :=
    ad.tends_to_center.comp hrho_tendsto
  have hev_ball : ∀ᶠ n in atTop, ad.gamma (rho n) ∈ Metric.ball ξ R :=
    hgamma_tendsto (Metric.ball_mem_nhds ξ hR)
  have hev_ex : ∃ N₀ : ℕ, ∀ n, n ≥ N₀ → ad.gamma (rho n) ∈ Metric.ball ξ R :=
    Filter.eventually_atTop.1 hev_ball
  set N₀ : ℕ := hev_ex.choose with hN₀_def
  have hN₀ : ∀ n, n ≥ N₀ → ad.gamma (rho n) ∈ Metric.ball ξ R := by
    rw [hN₀_def]; exact hev_ex.choose_spec
  refine {
    rho := fun n => rho (N₀ + n)
    rho_pos := fun n => hrho_pos (N₀ + n)
    rho_le_radius := fun n => hrho_le (N₀ + n)
    rho_tendsto_zero := ?_
    point_mem_radius := ?_
    point_mem_pi := fun n => hpi_mem (N₀ + n)
    point_injective := ?_ }
  · have hshift : Tendsto (fun n : ℕ => N₀ + n) atTop atTop :=
      tendsto_atTop_mono (fun n => Nat.le_add_left n N₀) tendsto_id
    exact hrho_tendsto.comp hshift
  · intro n
    refine ⟨hne (rho (N₀ + n)) (hrho_pos (N₀ + n)) (hrho_lt (N₀ + n)), ?_⟩
    have hb := hN₀ (N₀ + n) (by omega)
    rwa [Metric.mem_ball] at hb
  · intro a b hab
    have hidx : N₀ + a = N₀ + b := hinj hab
    exact Nat.add_left_cancel hidx


/-- **K06B.C5**: the arc-coverage trichotomy.  From the exact selected-arc package
`SelectedArcData` one builds the legacy `ArcStructureResult`: a ball `radius = ρ♭ ⊆ dom`,
the `2m` rotated arcs `γ_q(ρ) = ψ⁻¹((c·ρ)·e^{iθ_q})` (with `θ_q = angle - q·(π/m)`,
`c = radius'/ρ♭`), the coverage of every imaginary-axis level point (via
`Real.cos_eq_zero_iff` and a `2m`-index-matching argument), and a genuine odd-`π`
sequence on each arc (via `levelArcPiSequence_of_exactValue`). -/
theorem SelectedArcData.toArcStructureResult {H : ℂ -> ℂ} {ξ : ℂ} {m : Nat} {c0 : ℂ}
    (A : SelectedArcData H ξ m c0) (hm : 1 ≤ m) : ArcStructureResult H ξ m := by
  classical
  -- basic numerics
  have hmn : m ≠ 0 := by omega
  have hmr_pos : (0:ℝ) < (m:ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm
  have hmr : (m:ℝ) ≠ 0 := ne_of_gt hmr_pos
  have hmc : (m:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hmn
  -- `‖c0‖ > 0` (else the sigma values would vanish)
  have hc0n : 0 < ‖c0‖ := by
    have hav := A.arc_value_exact (A.rho 0) (A.rho_pos 0) (A.rho_le 0)
    have hsv := A.sigma_value_exact 0
    rw [hav] at hsv
    have hrhs_ne : (A.sign:ℂ) * ((2 * (A.Nstar + 0) + 1 : ℕ):ℂ) * (Real.pi:ℂ) * Complex.I ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) Complex.I_ne_zero
      · rcases mul_self_eq_one_iff.mp A.sign_sq with hs | hs <;> rw [hs] <;> norm_num
      · exact_mod_cast (by omega : 2 * (A.Nstar + 0) + 1 ≠ 0)
      · exact Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)
    rcases (norm_nonneg c0).lt_or_eq with h | h
    · exact h
    · exfalso; apply hrhs_ne; rw [← hsv, ← h]; simp
  have hc0nc : (‖c0‖:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hc0n)
  -- the base-angle identity `c0·e^{-i m·angle} = sign·i·‖c0‖`
  have hbase : c0 * Complex.exp (-(m:ℂ) * (A.angle:ℂ) * Complex.I)
      = (A.sign:ℂ) * Complex.I * (‖c0‖:ℂ) := by
    have h1 : H (A.chart.ψinv ((A.arcRadius:ℂ) * Complex.exp ((A.angle:ℂ) * Complex.I)))
        = c0 * Complex.exp (-(m:ℂ) * (A.angle:ℂ) * Complex.I) * (A.arcRadius:ℂ)^(-(m:ℤ)) :=
      poleChart_arc_value_general A.chart (φ := A.angle) A.arcRadius_pos A.arcRadius_lt
    have h2 : H (A.arc A.arcRadius)
        = (A.sign:ℂ) * Complex.I * (‖c0‖:ℂ) * (A.arcRadius:ℂ)^(-(m:ℤ)) :=
      A.arc_value_exact A.arcRadius A.arcRadius_pos (le_refl _)
    have h3 : A.arc A.arcRadius
        = A.chart.ψinv ((A.arcRadius:ℂ) * Complex.exp ((A.angle:ℂ) * Complex.I)) :=
      A.arc_eq A.arcRadius A.arcRadius_pos (le_refl _)
    rw [h3, h1] at h2
    have hne0 : (A.arcRadius:ℂ)^(-(m:ℤ)) ≠ 0 :=
      zpow_ne_zero _ (by exact_mod_cast (ne_of_gt A.arcRadius_pos))
    exact mul_right_cancel₀ hne0 h2
  -- chart quotient `β` and the geometric radius `ρ♭`
  obtain ⟨β, hβ_an, hβ0, hβ_ne, hβ_form⟩ := A.chart.beta_analytic_ne
  obtain ⟨rb, hrb_pos, hball_sub⟩ :=
    Metric.isOpen_iff.mp A.chart.domain_isOpen ξ A.chart.center_mem
  set c : ℝ := A.chart.radius' / rb with hc_def
  have hc_pos : 0 < c := div_pos A.chart.radius'_pos hrb_pos
  set B : ℝ := ‖c0‖ * c ^ (-(m:ℤ)) with hB_def
  have hB_pos : 0 < B := mul_pos hc0n (zpow_pos hc_pos _)
  -- each arc tends to `ξ` (via the analytic quotient `ψ⁻¹ w = ξ + w·β w`)
  have htends : ∀ q : Fin (2 * m),
      Tendsto (fun ρ => A.chart.ψinv (((c * ρ : ℝ):ℂ)
          * Complex.exp (((A.angle - ((q:ℕ):ℝ) * (Real.pi / (m:ℝ)) : ℝ):ℂ) * Complex.I)))
        (nhdsWithin (0:ℝ) {ρ : ℝ | 0 < ρ}) (nhds ξ) := by
    intro q
    set eq : ℂ := Complex.exp (((A.angle - ((q:ℕ):ℝ) * (Real.pi / (m:ℝ)) : ℝ):ℂ) * Complex.I)
      with heq_def
    have heq_ne : eq ≠ 0 := by rw [heq_def]; exact Complex.exp_ne_zero _
    have heq_norm : ‖eq‖ = 1 := by rw [heq_def, Complex.norm_exp]; simp
    set α : ℝ → ℂ := fun t => ξ + ((c * t : ℝ):ℂ) * eq * β (((c * t : ℝ):ℂ) * eq) with hα_def
    have hα0 : α 0 = ξ := by simp [hα_def]
    have hα_contAt : ContinuousAt α 0 := by
      rw [hα_def]
      have hin : ContinuousAt (fun t : ℝ => ((c * t : ℝ):ℂ) * eq) 0 := by
        refine ContinuousAt.mul ?_ continuousAt_const
        exact (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).continuousAt
      have hβ_ca : ContinuousAt β (0:ℂ) :=
        (hβ_an.continuousOn).continuousAt (Metric.ball_mem_nhds (0:ℂ) A.chart.radius'_pos)
      have hcomp : ContinuousAt (fun t : ℝ => β (((c * t : ℝ):ℂ) * eq)) 0 :=
        ContinuousAt.comp_of_eq hβ_ca hin (by simp)
      exact continuousAt_const.add (hin.mul hcomp)
    have hα_tend : Tendsto α (nhdsWithin (0:ℝ) {ρ : ℝ | 0 < ρ}) (nhds ξ) := by
      have h : Tendsto α (nhdsWithin (0:ℝ) {ρ : ℝ | 0 < ρ}) (nhds (α 0)) :=
        hα_contAt.continuousWithinAt (s := {ρ : ℝ | 0 < ρ})
      rw [hα0] at h; exact h
    have hlt : Set.Iio rb ∈ nhdsWithin (0:ℝ) {ρ : ℝ | 0 < ρ} :=
      nhdsWithin_le_nhds (Iio_mem_nhds hrb_pos)
    refine hα_tend.congr' ?_
    filter_upwards [self_mem_nhdsWithin, hlt] with ρ hρpos hρlt
    have hρ : 0 < ρ := hρpos
    have hcρ_pos : 0 < c * ρ := mul_pos hc_pos hρ
    have hcρ_lt : c * ρ < A.chart.radius' := by
      have h1 : c * ρ < c * rb := mul_lt_mul_of_pos_left hρlt hc_pos
      rwa [hc_def, div_mul_cancel₀ A.chart.radius' (ne_of_gt hrb_pos)] at h1
    have hmem : ((c * ρ : ℝ):ℂ) * eq ∈ Metric.ball (0:ℂ) A.chart.radius' := by
      rw [Metric.mem_ball, dist_zero_right, norm_mul, heq_norm, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hcρ_pos]
      exact hcρ_lt
    have hne0 : ((c * ρ : ℝ):ℂ) * eq ≠ 0 :=
      mul_ne_zero (by exact_mod_cast (ne_of_gt hcρ_pos)) heq_ne
    have hform := hβ_form (((c * ρ : ℝ):ℂ) * eq) hmem hne0
    show ξ + ((c * ρ : ℝ):ℂ) * eq * β (((c * ρ : ℝ):ℂ) * eq)
        = A.chart.ψinv (((c * ρ : ℝ):ℂ) * eq)
    rw [hform]
  -- the `2m` arcs
  let arcs : Fin (2 * m) → LevelArcData H ξ := fun q => {
    gamma := fun ρ => A.chart.ψinv (((c * ρ : ℝ):ℂ)
        * Complex.exp (((A.angle - ((q:ℕ):ℝ) * (Real.pi / (m:ℝ)) : ℝ):ℂ) * Complex.I))
    sign := A.sign * (-1) ^ (q:ℕ)
    sign_sq := by
      have h1 : ((-1:ℤ) ^ (q:ℕ)) * ((-1) ^ (q:ℕ)) = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]; norm_num
      calc (A.sign * (-1) ^ (q:ℕ)) * (A.sign * (-1) ^ (q:ℕ))
          = (A.sign * A.sign) * ((-1) ^ (q:ℕ) * (-1) ^ (q:ℕ)) := by ring
        _ = 1 * 1 := by rw [A.sign_sq, h1]
        _ = 1 := by norm_num
    tends_to_center := htends q }
  have hgam : ∀ (q : Fin (2 * m)) (ρ : ℝ), (arcs q).gamma ρ
      = A.chart.ψinv (((c * ρ : ℝ):ℂ)
          * Complex.exp (((A.angle - ((q:ℕ):ℝ) * (Real.pi / (m:ℝ)) : ℝ):ℂ) * Complex.I)) :=
    fun _ _ => rfl
  have hsign : ∀ q : Fin (2 * m), (arcs q).sign = A.sign * (-1) ^ (q:ℕ) := fun _ => rfl
  -- exact odd-π value law along each arc
  have hval : ∀ q : Fin (2 * m), ∀ ρ : ℝ, 0 < ρ → ρ < rb →
      H ((arcs q).gamma ρ) = ((arcs q).sign : ℂ) * Complex.I * (B:ℂ) * (ρ:ℂ)^(-(m:ℤ)) := by
    intro q ρ hρ hρlt
    have hcρ_pos : 0 < c * ρ := mul_pos hc_pos hρ
    have hcρ_lt : c * ρ < A.chart.radius' := by
      have h1 : c * ρ < c * rb := mul_lt_mul_of_pos_left hρlt hc_pos
      rwa [hc_def, div_mul_cancel₀ A.chart.radius' (ne_of_gt hrb_pos)] at h1
    have hgen := poleChart_arc_value_general A.chart
        (φ := A.angle - ((q:ℕ):ℝ) * (Real.pi / (m:ℝ))) (t := c * ρ) hcρ_pos hcρ_lt
    have hexp_split :
        Complex.exp (-(m:ℂ) * ((A.angle - ((q:ℕ):ℝ) * (Real.pi / (m:ℝ)) : ℝ):ℂ) * Complex.I)
          = Complex.exp (-(m:ℂ) * (A.angle:ℂ) * Complex.I) * (-1:ℂ) ^ (q:ℕ) := by
      rw [show -(m:ℂ) * ((A.angle - ((q:ℕ):ℝ) * (Real.pi / (m:ℝ)) : ℝ):ℂ) * Complex.I
            = -(m:ℂ) * (A.angle:ℂ) * Complex.I + ((q:ℕ):ℂ) * ((Real.pi:ℂ) * Complex.I) from by
            push_cast; field_simp; ring]
      rw [Complex.exp_add, Complex.exp_nat_mul, Complex.exp_pi_mul_I]
    have hcρ_cast : ((c * ρ : ℝ):ℂ)^(-(m:ℤ)) = (c:ℂ)^(-(m:ℤ)) * (ρ:ℂ)^(-(m:ℤ)) := by
      rw [Complex.ofReal_mul, mul_zpow]
    have hB_cast : (B:ℂ) = (‖c0‖:ℂ) * (c:ℂ)^(-(m:ℤ)) := by
      rw [hB_def, Complex.ofReal_mul, Complex.ofReal_zpow]
    rw [hgam q ρ, hgen, hsign q, hexp_split, hcρ_cast, hB_cast]
    have expand : c0 * (Complex.exp (-(m:ℂ) * (A.angle:ℂ) * Complex.I) * (-1:ℂ) ^ (q:ℕ))
          * ((c:ℂ)^(-(m:ℤ)) * (ρ:ℂ)^(-(m:ℤ)))
        = (c0 * Complex.exp (-(m:ℂ) * (A.angle:ℂ) * Complex.I))
          * ((-1:ℂ) ^ (q:ℕ) * (c:ℂ)^(-(m:ℤ)) * (ρ:ℂ)^(-(m:ℤ))) := by ring
    rw [expand, hbase]
    push_cast
    ring
  -- arc points never hit `ξ`
  have hne : ∀ q : Fin (2 * m), ∀ ρ : ℝ, 0 < ρ → ρ < rb → (arcs q).gamma ρ ≠ ξ := by
    intro q ρ hρ hρlt heq
    have hcρ_pos : 0 < c * ρ := mul_pos hc_pos hρ
    have hcρ_lt : c * ρ < A.chart.radius' := by
      have h1 : c * ρ < c * rb := mul_lt_mul_of_pos_left hρlt hc_pos
      rwa [hc_def, div_mul_cancel₀ A.chart.radius' (ne_of_gt hrb_pos)] at h1
    have heq_norm : ‖Complex.exp (((A.angle - ((q:ℕ):ℝ) * (Real.pi / (m:ℝ)) : ℝ):ℂ)
        * Complex.I)‖ = 1 := by rw [Complex.norm_exp]; simp
    have hmem : ((c * ρ : ℝ):ℂ)
        * Complex.exp (((A.angle - ((q:ℕ):ℝ) * (Real.pi / (m:ℝ)) : ℝ):ℂ) * Complex.I)
        ∈ Metric.ball (0:ℂ) A.chart.radius' := by
      rw [Metric.mem_ball, dist_zero_right, norm_mul, heq_norm, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hcρ_pos]
      exact hcρ_lt
    have hbi := A.chart.biholo_right _ hmem
    have hψeq : A.chart.ψ ((arcs q).gamma ρ) = ((c * ρ : ℝ):ℂ)
        * Complex.exp (((A.angle - ((q:ℕ):ℝ) * (Real.pi / (m:ℝ)) : ℝ):ℂ) * Complex.I) := by
      rw [hgam q ρ]; exact hbi.1
    rw [heq, A.chart.ψ_center] at hψeq
    exact (mul_ne_zero (by exact_mod_cast (ne_of_gt hcρ_pos)) (Complex.exp_ne_zero _)) hψeq.symm
  -- coverage of imaginary-axis level points by the `2m` arcs
  have hcover : ∀ τ ∈ puncturedDisc ξ rb, H τ ∈ imaginaryAxis →
      ∃ q : Fin (2 * m), ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ rb ∧ (arcs q).gamma ρ = τ := by
    intro τ hτ himg
    obtain ⟨hτ_ne, hτ_dist⟩ := hτ
    have hτ_domain : τ ∈ A.chart.domain :=
      hball_sub (by rw [Metric.mem_ball]; exact hτ_dist)
    set w : ℂ := A.chart.ψ τ with hw_def
    have hw_ne : w ≠ 0 := by
      intro h0
      apply hτ_ne
      have hL := A.chart.biholo_left τ hτ_domain
      have hC := A.chart.biholo_left ξ A.chart.center_mem
      rw [A.chart.ψ_center] at hC
      rw [hw_def] at h0
      rw [h0] at hL
      rw [hC] at hL
      exact hL.symm
    have hw_norm_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw_ne
    have hw_mem : w ∈ Metric.ball (0:ℂ) A.chart.radius' := by
      rw [hw_def, ← A.chart.maps_onto]; exact ⟨τ, hτ_domain, rfl⟩
    have hw_norm_lt : ‖w‖ < A.chart.radius' := by
      rw [Metric.mem_ball, dist_zero_right] at hw_mem; exact hw_mem
    have hnf : H τ = c0 * w ^ (-(m:ℤ)) := A.chart.normal_form τ hτ_domain hτ_ne
    obtain ⟨tt, htt⟩ := himg
    have hre0 : (H τ).re = 0 := by rw [htt, Complex.mul_I_re, Complex.ofReal_im]; simp
    have hw_pow : w ^ (-(m:ℤ))
        = (‖w‖:ℂ)^(-(m:ℤ)) * Complex.exp (-(m:ℂ) * (Complex.arg w:ℂ) * Complex.I) := by
      conv_lhs => rw [show w = (‖w‖:ℂ) * Complex.exp ((Complex.arg w:ℂ) * Complex.I) from
        (Complex.norm_mul_exp_arg_mul_I w).symm]
      rw [mul_zpow]; congr 1
      rw [← Complex.exp_int_mul]; congr 1; push_cast; ring
    have key_eq : H τ = ((‖c0‖ * ‖w‖ ^ (-(m:ℤ)) : ℝ):ℂ)
        * Complex.exp (((Complex.arg c0 - (m:ℝ) * Complex.arg w : ℝ):ℂ) * Complex.I) := by
      rw [hnf, hw_pow]
      rw [show ((‖c0‖ * ‖w‖ ^ (-(m:ℤ)) : ℝ):ℂ) = (‖c0‖:ℂ) * (‖w‖:ℂ)^(-(m:ℤ)) from by
            rw [Complex.ofReal_mul, Complex.ofReal_zpow]]
      rw [show (((Complex.arg c0 - (m:ℝ) * Complex.arg w : ℝ):ℂ) * Complex.I)
            = (Complex.arg c0:ℂ) * Complex.I + (-(m:ℂ) * (Complex.arg w:ℂ) * Complex.I) from by
            push_cast; ring]
      rw [Complex.exp_add]
      conv_lhs => rw [show c0 = (‖c0‖:ℂ) * Complex.exp ((Complex.arg c0:ℂ) * Complex.I) from
        (Complex.norm_mul_exp_arg_mul_I c0).symm]
      ring
    have hre_eq : (H τ).re
        = (‖c0‖ * ‖w‖ ^ (-(m:ℤ))) * Real.cos (Complex.arg c0 - (m:ℝ) * Complex.arg w) := by
      rw [key_eq, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
    have hDpos : 0 < ‖c0‖ * ‖w‖ ^ (-(m:ℤ)) := mul_pos hc0n (zpow_pos hw_norm_pos _)
    have hcos0 : Real.cos (Complex.arg c0 - (m:ℝ) * Complex.arg w) = 0 := by
      have hzero : (‖c0‖ * ‖w‖ ^ (-(m:ℤ)))
          * Real.cos (Complex.arg c0 - (m:ℝ) * Complex.arg w) = 0 := by
        rw [← hre_eq]; exact hre0
      rcases mul_eq_zero.mp hzero with h | h
      · exact absurd h (ne_of_gt hDpos)
      · exact h
    obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp hcos0
    -- combine with the base angle: `arg c0 - m·angle ≡ sign·π/2 (mod 2π)`
    have hbase'' : Complex.exp (((Complex.arg c0 - (m:ℝ) * A.angle : ℝ):ℂ) * Complex.I)
        = (A.sign:ℂ) * Complex.I := by
      rw [show (((Complex.arg c0 - (m:ℝ) * A.angle : ℝ):ℂ) * Complex.I)
            = (Complex.arg c0:ℂ) * Complex.I + (-(m:ℂ) * (A.angle:ℂ) * Complex.I) from by
            push_cast; ring, Complex.exp_add]
      apply mul_left_cancel₀ hc0nc
      calc (‖c0‖:ℂ) * (Complex.exp ((Complex.arg c0:ℂ) * Complex.I)
            * Complex.exp (-(m:ℂ) * (A.angle:ℂ) * Complex.I))
          = c0 * Complex.exp (-(m:ℂ) * (A.angle:ℂ) * Complex.I) := by
            rw [← mul_assoc, Complex.norm_mul_exp_arg_mul_I]
        _ = (A.sign:ℂ) * Complex.I * (‖c0‖:ℂ) := hbase
        _ = (‖c0‖:ℂ) * ((A.sign:ℂ) * Complex.I) := by ring
    -- extract integer `l` with `m·(angle - arg w) = l·π`
    obtain ⟨l, hlpi⟩ : ∃ l : ℤ, (m:ℝ) * (A.angle - Complex.arg w) = (l:ℝ) * Real.pi := by
      rcases mul_self_eq_one_iff.mp A.sign_sq with hs1 | hsm1
      · have hexp1 : Complex.exp (((Complex.arg c0 - (m:ℝ) * A.angle : ℝ):ℂ) * Complex.I)
            = Complex.exp (((Real.pi / 2 : ℝ):ℂ) * Complex.I) := by
          rw [hbase'', hs1,
            show ((Real.pi / 2 : ℝ):ℂ) * Complex.I = (Real.pi:ℂ) / 2 * Complex.I from by
              push_cast; ring, Complex.exp_pi_div_two_mul_I]
          push_cast; ring
        obtain ⟨j, hj⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp1
        have hjr : Complex.arg c0 - (m:ℝ) * A.angle = Real.pi / 2 + (j:ℝ) * (2 * Real.pi) := by
          have h' : ((Complex.arg c0 - (m:ℝ) * A.angle : ℝ):ℂ)
              = ((Real.pi / 2 + (j:ℝ) * (2 * Real.pi) : ℝ):ℂ) := by
            apply mul_right_cancel₀ Complex.I_ne_zero
            rw [hj]; push_cast; ring
          exact_mod_cast h'
        refine ⟨k - 2 * j, ?_⟩
        have e1 : (m:ℝ) * Complex.arg w = Complex.arg c0 - (2 * (k:ℝ) + 1) * Real.pi / 2 := by
          linarith [hk]
        have e2 : (m:ℝ) * A.angle = Complex.arg c0 - (Real.pi / 2 + (j:ℝ) * (2 * Real.pi)) := by
          linarith [hjr]
        have expand : (m:ℝ) * (A.angle - Complex.arg w)
            = (m:ℝ) * A.angle - (m:ℝ) * Complex.arg w := by ring
        rw [expand, e1, e2]; push_cast; ring
      · have hexp1 : Complex.exp (((Complex.arg c0 - (m:ℝ) * A.angle : ℝ):ℂ) * Complex.I)
            = Complex.exp (((-(Real.pi / 2) : ℝ):ℂ) * Complex.I) := by
          rw [hbase'', hsm1,
            show ((-(Real.pi / 2) : ℝ):ℂ) * Complex.I = -((Real.pi:ℂ) / 2 * Complex.I) from by
              push_cast; ring, Complex.exp_neg, Complex.exp_pi_div_two_mul_I, Complex.inv_I]
          push_cast; ring
        obtain ⟨j, hj⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp1
        have hjr : Complex.arg c0 - (m:ℝ) * A.angle
            = -(Real.pi / 2) + (j:ℝ) * (2 * Real.pi) := by
          have h' : ((Complex.arg c0 - (m:ℝ) * A.angle : ℝ):ℂ)
              = ((-(Real.pi / 2) + (j:ℝ) * (2 * Real.pi) : ℝ):ℂ) := by
            apply mul_right_cancel₀ Complex.I_ne_zero
            rw [hj]; push_cast; ring
          exact_mod_cast h'
        refine ⟨k + 1 - 2 * j, ?_⟩
        have e1 : (m:ℝ) * Complex.arg w = Complex.arg c0 - (2 * (k:ℝ) + 1) * Real.pi / 2 := by
          linarith [hk]
        have e2 : (m:ℝ) * A.angle
            = Complex.arg c0 - (-(Real.pi / 2) + (j:ℝ) * (2 * Real.pi)) := by linarith [hjr]
        have expand : (m:ℝ) * (A.angle - Complex.arg w)
            = (m:ℝ) * A.angle - (m:ℝ) * Complex.arg w := by ring
        rw [expand, e1, e2]; push_cast; ring
    -- index matching: `q := l mod 2m`, `d := l / 2m`
    have h2m_pos : 0 < 2 * m := by omega
    have h2mZ_pos : (0:ℤ) < 2 * (m:ℤ) := by exact_mod_cast h2m_pos
    have h2mZ_ne : (2 * (m:ℤ)) ≠ 0 := ne_of_gt h2mZ_pos
    set d : ℤ := l / (2 * (m:ℤ)) with hd_def
    have hemod_nonneg : 0 ≤ l % (2 * (m:ℤ)) := Int.emod_nonneg l h2mZ_ne
    have hemod_lt : l % (2 * (m:ℤ)) < 2 * (m:ℤ) := Int.emod_lt_of_pos l h2mZ_pos
    have hqbound : (l % (2 * (m:ℤ))).toNat < 2 * m := by
      have h1 : ((l % (2 * (m:ℤ))).toNat : ℤ) = l % (2 * (m:ℤ)) := Int.toNat_of_nonneg hemod_nonneg
      have h2 : ((l % (2 * (m:ℤ))).toNat : ℤ) < ((2 * m : ℕ) : ℤ) := by
        rw [h1]; exact_mod_cast hemod_lt
      exact_mod_cast h2
    let qFin : Fin (2 * m) := ⟨(l % (2 * (m:ℤ))).toNat, hqbound⟩
    have hqval : ((qFin : ℕ) : ℤ) = l % (2 * (m:ℤ)) := Int.toNat_of_nonneg hemod_nonneg
    have hld : (l:ℤ) = 2 * (m:ℤ) * d + ((qFin : ℕ) : ℤ) := by
      rw [hqval]
      have hdm := Int.mul_ediv_add_emod l (2 * (m:ℤ))
      rw [← hd_def] at hdm
      linarith [hdm]
    set ρ : ℝ := ‖w‖ / c with hρ_def
    have hρ_pos : 0 < ρ := div_pos hw_norm_pos hc_pos
    have hρ_le : ρ ≤ rb := by
      rw [hρ_def, hc_def, div_div_eq_mul_div, div_le_iff₀ A.chart.radius'_pos,
        mul_comm rb A.chart.radius']
      exact mul_le_mul_of_nonneg_right hw_norm_lt.le hrb_pos.le
    have hθ_eq : A.angle - ((qFin : ℕ):ℝ) * (Real.pi / (m:ℝ))
        = Complex.arg w + (d:ℝ) * (2 * Real.pi) := by
      have hL : (l:ℝ) = 2 * (m:ℝ) * (d:ℝ) + ((qFin : ℕ):ℝ) := by exact_mod_cast hld
      have hmul : (m:ℝ) * (((qFin : ℕ):ℝ) * (Real.pi / (m:ℝ))) = ((qFin : ℕ):ℝ) * Real.pi := by
        have hcancel : Real.pi / (m:ℝ) * (m:ℝ) = Real.pi := div_mul_cancel₀ Real.pi hmr
        calc (m:ℝ) * (((qFin : ℕ):ℝ) * (Real.pi / (m:ℝ)))
            = ((qFin : ℕ):ℝ) * (Real.pi / (m:ℝ) * (m:ℝ)) := by ring
          _ = ((qFin : ℕ):ℝ) * Real.pi := by rw [hcancel]
      have key : (m:ℝ) * (A.angle - ((qFin : ℕ):ℝ) * (Real.pi / (m:ℝ)))
               = (m:ℝ) * (Complex.arg w + (d:ℝ) * (2 * Real.pi)) := by
        rw [mul_sub, hmul, mul_add]
        have hrearr : (m:ℝ) * A.angle - ((qFin : ℕ):ℝ) * Real.pi
            = (m:ℝ) * (A.angle - Complex.arg w) + (m:ℝ) * Complex.arg w
              - ((qFin : ℕ):ℝ) * Real.pi := by ring
        rw [hrearr, hlpi, hL]; ring
      exact mul_left_cancel₀ hmr key
    have harg_eq : ((c * ρ : ℝ):ℂ)
        * Complex.exp (((A.angle - ((qFin : ℕ):ℝ) * (Real.pi / (m:ℝ)) : ℝ):ℂ) * Complex.I) = w := by
      have hcρ : (c * ρ : ℝ) = ‖w‖ := by
        rw [hρ_def, mul_comm, div_mul_cancel₀ _ (ne_of_gt hc_pos)]
      rw [hcρ,
        show ((A.angle - ((qFin : ℕ):ℝ) * (Real.pi / (m:ℝ)) : ℝ):ℂ) * Complex.I
          = (Complex.arg w:ℂ) * Complex.I + (d:ℂ) * (2 * (Real.pi:ℂ) * Complex.I) from by
          rw [show ((A.angle - ((qFin : ℕ):ℝ) * (Real.pi / (m:ℝ)) : ℝ):ℂ)
                = ((Complex.arg w + (d:ℝ) * (2 * Real.pi) : ℝ):ℂ) from by rw [hθ_eq]]
          push_cast; ring]
      rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
      exact Complex.norm_mul_exp_arg_mul_I w
    refine ⟨qFin, ρ, hρ_pos, hρ_le, ?_⟩
    rw [hgam qFin ρ, harg_eq, hw_def]
    exact A.chart.biholo_left τ hτ_domain
  -- genuine odd-π sequence on each arc
  have hseq : ∀ q : Fin (2 * m), ∃ _ : LevelArcPiSequence H ξ rb (arcs q), True := by
    intro q
    exact ⟨levelArcPiSequence_of_exactValue hm hrb_pos (arcs q) hB_pos
      (arcs q).sign_sq (hval q) (hne q), trivial⟩
  exact arcStructureResult_of_components hm hrb_pos hcover hseq


end TransformerIdentifiability.NLayer.KHead
