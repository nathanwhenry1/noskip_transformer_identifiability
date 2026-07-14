import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.PlaneTopology

set_option autoImplicit false

open Filter Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.KHead

/-! ## Exact-order Laurent normal forms -/

/-- Exact-order Laurent normal form at a center.

For positive `μ`, this says that on a punctured neighborhood of `ξ`,
`f z = g z * (z - ξ) ^ (-μ)`, with `g` analytic and nonzero at `ξ`.  Negative
and zero values of `μ` are also allowed, matching the same Laurent-order
bookkeeping convention. -/
structure LaurentNormalFormAt (f : ℂ -> ℂ) (ξ : ℂ) (μ : ℤ) (coeff : ℂ) : Prop where
  coeff_ne_zero : coeff ≠ 0
  factored :
    ∃ g : ℂ -> ℂ, AnalyticAt ℂ g ξ ∧ g ξ = coeff ∧
      ∀ᶠ z in nhdsWithin ξ ({ξ}ᶜ : Set ℂ), f z = g z * (z - ξ) ^ (-μ)

namespace LaurentNormalFormAt

/-- The coefficient carried by a Laurent normal form is nonzero. -/
theorem leadingCoeff_ne_zero {f : ℂ -> ℂ} {ξ : ℂ} {μ : ℤ} {coeff : ℂ}
    (h : LaurentNormalFormAt f ξ μ coeff) :
    coeff ≠ 0 :=
  h.coeff_ne_zero

/-- Transport a Laurent normal form across punctured-neighborhood eventual equality. -/
theorem congr {f f' : ℂ -> ℂ} {ξ : ℂ} {μ : ℤ} {coeff : ℂ}
    (h : LaurentNormalFormAt f ξ μ coeff)
    (hff' : f =ᶠ[nhdsWithin ξ ({ξ}ᶜ : Set ℂ)] f') :
    LaurentNormalFormAt f' ξ μ coeff := by
  refine ⟨h.coeff_ne_zero, ?_⟩
  rcases h.factored with ⟨g, hg, hgξ, hfg⟩
  refine ⟨g, hg, hgξ, ?_⟩
  filter_upwards [hfg, hff'] with z hz hzz
  rw [← hzz, hz]

/-- A factored Laurent normal form is meromorphic at its center. -/
theorem meromorphicAt {f : ℂ -> ℂ} {ξ : ℂ} {μ : ℤ} {coeff : ℂ}
    (h : LaurentNormalFormAt f ξ μ coeff) :
    MeromorphicAt f ξ := by
  rcases h.factored with ⟨g, hg, _hgξ, hfg⟩
  rw [MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt]
  refine ⟨-μ, g, hg, ?_⟩
  filter_upwards [hfg] with z hz
  rw [hz]
  simp [mul_comm]

/-- The meromorphic order encoded by the factored Laurent normal form. -/
theorem order_eq {f : ℂ -> ℂ} {ξ : ℂ} {μ : ℤ} {coeff : ℂ}
    (h : LaurentNormalFormAt f ξ μ coeff) :
    meromorphicOrderAt f ξ = (-μ : ℤ) := by
  rcases h.factored with ⟨g, hg, hgξ, hfg⟩
  rw [meromorphicOrderAt_eq_int_iff h.meromorphicAt]
  refine ⟨g, hg, ?_, ?_⟩
  · simpa [hgξ] using h.coeff_ne_zero
  · filter_upwards [hfg] with z hz
    rw [hz]
    simp [mul_comm]

/-- A Laurent normal form of order zero tends to its leading coefficient. -/
theorem tendsto_coeff_of_order_zero {f : ℂ -> ℂ} {ξ : ℂ} {μ : ℤ} {coeff : ℂ}
    (h : LaurentNormalFormAt f ξ μ coeff) (hμ : μ = 0) :
    Tendsto f (nhdsWithin ξ ({ξ}ᶜ : Set ℂ)) (nhds coeff) := by
  rcases h.factored with ⟨g, hg, hgξ, hfg⟩
  have hg_tend : Tendsto g (nhdsWithin ξ ({ξ}ᶜ : Set ℂ)) (nhds coeff) := by
    simpa [hgξ] using hg.continuousAt.continuousWithinAt.tendsto
  apply hg_tend.congr'
  filter_upwards [hfg] with z hz
  simpa [hμ, hgξ] using hz.symm

/-- A Laurent normal form with negative Laurent pole order tends to zero. -/
theorem tendsto_zero_of_order_neg {f : ℂ -> ℂ} {ξ : ℂ} {μ : ℤ} {coeff : ℂ}
    (h : LaurentNormalFormAt f ξ μ coeff) (hμ : μ < 0) :
    Tendsto f (nhdsWithin ξ ({ξ}ᶜ : Set ℂ)) (nhds 0) := by
  have hpos_int : (0 : ℤ) < -μ := neg_pos.mpr hμ
  have hpos : (0 : WithTop ℤ) < meromorphicOrderAt f ξ := by
    rw [h.order_eq]
    exact_mod_cast hpos_int
  exact tendsto_zero_of_meromorphicOrderAt_pos hpos

/-- A positive Laurent pole blows up along punctured neighborhoods. -/
theorem blowsUpAt {f : ℂ -> ℂ} {ξ : ℂ} {μ : ℤ} {coeff : ℂ}
    (h : LaurentNormalFormAt f ξ μ coeff) (hμ : 1 ≤ μ) :
    BlowsUpAt f ξ := by
  have hμpos : (0 : ℤ) < μ := lt_of_lt_of_le Int.zero_lt_one hμ
  have hlt_int : -μ < (0 : ℤ) := neg_neg_of_pos hμpos
  have hlt : meromorphicOrderAt f ξ < (0 : WithTop ℤ) := by
    rw [h.order_eq]
    exact_mod_cast hlt_int
  have hcob :
      Tendsto f (nhdsWithin ξ ({ξ}ᶜ : Set ℂ)) (Bornology.cobounded ℂ) :=
    tendsto_cobounded_of_meromorphicOrderAt_neg hlt
  simpa [TransformerIdentifiability.NLayer.BlowsUpAt] using
    (tendsto_norm_atTop_iff_cobounded.2 hcob)

/-- A positive Laurent pole is not analytic at its center. -/
theorem not_analyticAt {f : ℂ -> ℂ} {ξ : ℂ} {μ : ℤ} {coeff : ℂ}
    (h : LaurentNormalFormAt f ξ μ coeff) (hμ : 1 ≤ μ) :
    ¬ AnalyticAt ℂ f ξ := by
  intro han
  have hnonneg : (0 : WithTop ℤ) ≤ meromorphicOrderAt f ξ :=
    han.meromorphicOrderAt_nonneg
  rw [h.order_eq] at hnonneg
  have hμpos : (0 : ℤ) < μ := lt_of_lt_of_le Int.zero_lt_one hμ
  have hlt_int : -μ < (0 : ℤ) := neg_neg_of_pos hμpos
  have hlt : ((-μ : ℤ) : WithTop ℤ) < (0 : WithTop ℤ) := by
    exact_mod_cast hlt_int
  exact (not_lt_of_ge hnonneg) hlt

/-- Multiplication adds Laurent orders and multiplies leading coefficients. -/
theorem mul {f f' : ℂ -> ℂ} {ξ : ℂ} {μ ν : ℤ} {coeff coeff' : ℂ}
    (hf : LaurentNormalFormAt f ξ μ coeff)
    (hf' : LaurentNormalFormAt f' ξ ν coeff') :
    LaurentNormalFormAt (fun z => f z * f' z) ξ (μ + ν) (coeff * coeff') := by
  refine ⟨mul_ne_zero hf.coeff_ne_zero hf'.coeff_ne_zero, ?_⟩
  rcases hf.factored with ⟨g, hg, hgξ, hfg⟩
  rcases hf'.factored with ⟨g', hg', hg'ξ, hf'g'⟩
  refine ⟨fun z => g z * g' z, hg.mul hg', by simp [hgξ, hg'ξ], ?_⟩
  filter_upwards [hfg, hf'g',
    (eventually_mem_nhdsWithin : ∀ᶠ z in nhdsWithin ξ ({ξ}ᶜ : Set ℂ),
      z ∈ ({ξ}ᶜ : Set ℂ))] with z hz hz' hzmem
  have hz_ne : z - ξ ≠ 0 := by
    exact sub_ne_zero.mpr (by simpa using hzmem)
  have hpow :
      (z - ξ) ^ (-μ) * (z - ξ) ^ (-ν) =
        (z - ξ) ^ (-(μ + ν)) := by
    rw [← zpow_add₀ hz_ne]
    congr 1
    ring
  calc
    f z * f' z
        = (g z * (z - ξ) ^ (-μ)) * (g' z * (z - ξ) ^ (-ν)) := by
            rw [hz, hz']
    _ = (g z * g' z) * ((z - ξ) ^ (-μ) * (z - ξ) ^ (-ν)) := by
            ring
    _ = (g z * g' z) * (z - ξ) ^ (-(μ + ν)) := by
            rw [hpow]

/-- Natural powers multiply the Laurent order and raise the leading coefficient. -/
theorem pow {f : ℂ -> ℂ} {ξ : ℂ} {μ : ℤ} {coeff : ℂ}
    (h : LaurentNormalFormAt f ξ μ coeff) (n : ℕ) :
    LaurentNormalFormAt (fun z => f z ^ n) ξ ((n : ℤ) * μ) (coeff ^ n) := by
  induction n with
  | zero =>
      refine ⟨by simp, ?_⟩
      refine ⟨fun _ => 1, analyticAt_const, by simp, ?_⟩
      filter_upwards with z
      simp
  | succ n ih =>
      simpa [pow_succ, Nat.cast_succ, add_mul, mul_add, mul_comm, mul_left_comm, mul_assoc,
        add_comm, add_left_comm, add_assoc] using ih.mul h

/-- Adding a strictly lower Laurent pole order preserves the dominant normal form. -/
theorem add_of_order_lt {f f' : ℂ -> ℂ} {ξ : ℂ} {μ μ' : ℤ} {coeff coeff' : ℂ}
    (hf : LaurentNormalFormAt f ξ μ coeff)
    (hf' : LaurentNormalFormAt f' ξ μ' coeff') (hμ : μ' < μ) :
    LaurentNormalFormAt (fun z => f z + f' z) ξ μ coeff := by
  refine ⟨hf.coeff_ne_zero, ?_⟩
  rcases hf.factored with ⟨g, hg, hgξ, hfg⟩
  rcases hf'.factored with ⟨g', hg', _hg'ξ, hf'g'⟩
  let g₀ : ℂ -> ℂ := fun z => g z + g' z * (z - ξ) ^ (μ - μ')
  have hpos : 0 < μ - μ' := sub_pos.mpr hμ
  have hpow_an : AnalyticAt ℂ (fun z : ℂ => (z - ξ) ^ (μ - μ')) ξ := by
    exact (analyticAt_id.sub analyticAt_const).zpow_nonneg (le_of_lt hpos)
  refine ⟨g₀, hg.add (hg'.mul hpow_an), ?_, ?_⟩
  · have hzero_pow : (0 : ℂ) ^ (μ - μ') = 0 :=
      _root_.zero_zpow _ hpos.ne'
    simp [g₀, hgξ, sub_self, hzero_pow]
  · filter_upwards [hfg, hf'g',
      (eventually_mem_nhdsWithin : ∀ᶠ z in nhdsWithin ξ ({ξ}ᶜ : Set ℂ),
        z ∈ ({ξ}ᶜ : Set ℂ))] with z hz hz' hzmem
    have hz_ne : z - ξ ≠ 0 :=
      sub_ne_zero.mpr (by simpa using hzmem)
    have hpow :
        (z - ξ) ^ (μ - μ') * (z - ξ) ^ (-μ) = (z - ξ) ^ (-μ') := by
      rw [← zpow_add₀ hz_ne]
      congr 1
      ring
    calc
      f z + f' z
          = g z * (z - ξ) ^ (-μ) + g' z * (z - ξ) ^ (-μ') := by
              rw [hz, hz']
      _ = (g z + g' z * (z - ξ) ^ (μ - μ')) * (z - ξ) ^ (-μ) := by
              rw [← hpow]
              ring

/-- Adding a function analytic at the center preserves a positive-pole normal form. -/
theorem add_analyticAt {f a : ℂ -> ℂ} {ξ : ℂ} {μ : ℤ} {coeff : ℂ}
    (hf : LaurentNormalFormAt f ξ μ coeff) (ha : AnalyticAt ℂ a ξ) (hμ : 1 ≤ μ) :
    LaurentNormalFormAt (fun z => f z + a z) ξ μ coeff := by
  refine ⟨hf.coeff_ne_zero, ?_⟩
  rcases hf.factored with ⟨g, hg, hgξ, hfg⟩
  let g₀ : ℂ -> ℂ := fun z => g z + a z * (z - ξ) ^ μ
  have hμ_nonneg : 0 ≤ μ := le_trans (by norm_num) hμ
  have hμ_ne : μ ≠ 0 := by omega
  have hpow_an : AnalyticAt ℂ (fun z : ℂ => (z - ξ) ^ μ) ξ := by
    exact (analyticAt_id.sub analyticAt_const).zpow_nonneg hμ_nonneg
  refine ⟨g₀, hg.add (ha.mul hpow_an), ?_, ?_⟩
  · have hzero_pow : (0 : ℂ) ^ μ = 0 :=
      _root_.zero_zpow _ hμ_ne
    simp [g₀, hgξ, sub_self, hzero_pow]
  · filter_upwards [hfg,
      (eventually_mem_nhdsWithin : ∀ᶠ z in nhdsWithin ξ ({ξ}ᶜ : Set ℂ),
        z ∈ ({ξ}ᶜ : Set ℂ))] with z hz hzmem
    have hz_ne : z - ξ ≠ 0 :=
      sub_ne_zero.mpr (by simpa using hzmem)
    have hpow : (z - ξ) ^ μ * (z - ξ) ^ (-μ) = 1 := by
      rw [← zpow_add₀ hz_ne]
      simp
    calc
      f z + a z
          = g z * (z - ξ) ^ (-μ) + a z := by
              rw [hz]
      _ = g z * (z - ξ) ^ (-μ) +
            (a z * (z - ξ) ^ μ) * (z - ξ) ^ (-μ) := by
              rw [mul_assoc, hpow, mul_one]
      _ = (g z + a z * (z - ξ) ^ μ) * (z - ξ) ^ (-μ) := by
              ring

/-- A non-locally-constant analytic function has a finite exact vanishing normal form. -/
theorem analyticAt_normalForm_of_not_eventually_eq {u : ℂ -> ℂ} {ξ : ℂ}
    (hu : AnalyticAt ℂ u ξ) (hnot : ¬ (u =ᶠ[nhds ξ] fun _ => u ξ)) :
    ∃ κ : ℕ, 1 ≤ κ ∧ ∃ coeff : ℂ, coeff ≠ 0 ∧
      LaurentNormalFormAt (fun z => u z - u ξ) ξ (-(κ : ℤ)) coeff := by
  let v : ℂ -> ℂ := fun z => u z - u ξ
  have hv : AnalyticAt ℂ v ξ := hu.sub analyticAt_const
  have hnot_zero : ¬ (∀ᶠ z in nhds ξ, v z = 0) := by
    intro hzero
    apply hnot
    filter_upwards [hzero] with z hz
    exact sub_eq_zero.mp hz
  have hfinite : analyticOrderAt v ξ ≠ ⊤ := by
    intro htop
    exact hnot_zero (analyticOrderAt_eq_top.mp htop)
  obtain ⟨κ, hκ⟩ := ENat.ne_top_iff_exists.mp hfinite
  have hκ_ne_zero : κ ≠ 0 := by
    intro hκ0
    have horder_zero : analyticOrderAt v ξ = 0 := by
      simpa [hκ0] using hκ.symm
    have hvξ_zero : v ξ = 0 := by simp [v]
    exact (hv.analyticOrderAt_ne_zero.2 hvξ_zero) horder_zero
  rcases (hv.analyticOrderAt_eq_natCast).1 hκ.symm with ⟨g, hg, hg_ne, hvg⟩
  refine ⟨κ, Nat.succ_le_of_lt (Nat.pos_of_ne_zero hκ_ne_zero), g ξ, hg_ne, ?_⟩
  refine ⟨hg_ne, ?_⟩
  refine ⟨g, hg, rfl, ?_⟩
  filter_upwards [hvg.filter_mono nhdsWithin_le_nhds] with z hz
  simpa [v, smul_eq_mul, zpow_natCast, mul_comm] using hz

/-- Inversion negates Laurent order and inverts the leading coefficient. -/
theorem inv {f : ℂ -> ℂ} {ξ : ℂ} {μ : ℤ} {coeff : ℂ}
    (h : LaurentNormalFormAt f ξ μ coeff) :
    LaurentNormalFormAt (fun z => (f z)⁻¹) ξ (-μ) coeff⁻¹ := by
  refine ⟨inv_ne_zero h.coeff_ne_zero, ?_⟩
  rcases h.factored with ⟨g, hg, hgξ, hfg⟩
  refine ⟨fun z => (g z)⁻¹, hg.inv (by simpa [hgξ] using h.coeff_ne_zero), ?_, ?_⟩
  · simp [hgξ]
  · filter_upwards [hfg] with z hz
    calc
      (f z)⁻¹
          = (g z * (z - ξ) ^ (-μ))⁻¹ := by
              rw [hz]
      _ = (g z)⁻¹ * ((z - ξ) ^ (-μ))⁻¹ := by
              rw [_root_.mul_inv_rev, mul_comm]
      _ = (g z)⁻¹ * (z - ξ) ^ μ := by
              rw [_root_.zpow_neg, inv_inv]
      _ = (g z)⁻¹ * (z - ξ) ^ (- -μ) := by
              simp

end LaurentNormalFormAt

end TransformerIdentifiability.NLayer.KHead
