import AnyLayerIdentifiabilityProof.NLayer.Analytic.AnchorGeneric

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer

/-!
# Analytic and point-set toolkit

Target contents:
* discrete sets and accumulation operators
* sigmoid poles
* countable-complement connectedness
* pole transfer
* accumulation of preimages of odd multiples of `π i`
* discrete level sets
* stratified accumulation

Corresponds to `n_layer_proof.tex`, Section 4.1-4.3.
-/

/-! ## Point-set preliminaries -/

/-- TeX notation `acc(A)`: the derived set, i.e. accumulation points of `A`. -/
abbrev acc (A : Set ℂ) : Set ℂ := derivedSet A

/-- Iterated accumulation sets: `accIter 0 A = A`, `accIter (k+1) A = acc (accIter k A)`. -/
def accIter : Nat -> Set ℂ -> Set ℂ
  | 0, A => A
  | k + 1, A => acc (accIter k A)

/-- A set has no accumulation points inside `U`.  This is the form of closed/discrete
relative strata consumed by the Step 1 descent. -/
def NoAccumIn (A U : Set ℂ) : Prop :=
  ∀ z ∈ U, z ∉ acc A

/-- `n_layer_proof.tex`, Auxiliary Lemma `discrete`, part (iii). -/
theorem acc_mono {A B : Set ℂ} (hAB : A ⊆ B) : acc A ⊆ acc B :=
  derivedSet_mono A B hAB

/-- Iterated version of `acc_mono`. -/
theorem accIter_mono {A B : Set ℂ} (hAB : A ⊆ B) :
    ∀ k : Nat, accIter k A ⊆ accIter k B := by
  intro k
  induction k with
  | zero =>
      simpa [accIter] using hAB
  | succ k ih =>
      simpa [accIter] using acc_mono ih

/-- `n_layer_proof.tex`, Auxiliary Lemma `discrete`, part (iv). -/
theorem closure_eq_self_union_acc (A : Set ℂ) :
    closure A = A ∪ acc A :=
  closure_eq_self_union_derivedSet A

/-- Closed sets contain their accumulation points. -/
theorem acc_subset_of_isClosed {A : Set ℂ} (hA : IsClosed A) : acc A ⊆ A := by
  intro z hz
  exact hA.closure_subset (derivedSet_subset_closure A hz)

/-- A subset of a regular domain with no accumulation points in that domain is
countable.  This packages the second-countability/Lindelöf argument for the recursive
stratification construction. -/
theorem countable_of_subset_noAccumIn {A U : Set ℂ}
    (hAU : A ⊆ U) (hA : NoAccumIn A U) :
    A.Countable := by
  have hdisc : IsDiscrete A := by
    rw [isDiscrete_iff_discreteTopology]
    exact discreteTopology_of_noAccPts fun z hzA => by
      simpa [acc, mem_derivedSet] using hA z (hAU hzA)
  exact (HereditarilyLindelofSpace.isLindelof A).countable_of_isDiscrete hdisc

/-- Adding a set with no accumulation points outside a closed exceptional set preserves
closedness of the union.

This is the point-set core of the recursive `strat` construction: after the previous
partial union is closed, the next stratum may accumulate only on that previous singular
set, so the enlarged partial union is still closed. -/
theorem IsClosed.union_of_noAccumIn_compl {A B : Set ℂ}
    (hA : IsClosed A) (hB : NoAccumIn B Aᶜ) :
    IsClosed (A ∪ B) := by
  rw [← closure_subset_iff_isClosed]
  intro z hz
  rw [closure_eq_self_union_acc] at hz
  rcases hz with hzAB | hzacc
  · exact hzAB
  · rw [acc, derivedSet_union] at hzacc
    rcases hzacc with hzAacc | hzBacc
    · exact Or.inl (acc_subset_of_isClosed hA hzAacc)
    · by_cases hzA : z ∈ A
      · exact Or.inl hzA
      · exact False.elim (hB z (by simpa using hzA) hzBacc)

/-- Union of the first `n` strata, with TeX indexing shifted by one:
`partialUnion S n = S^1 ∪ ... ∪ S^n` when `S 0 = S^1`. -/
def partialUnion (S : Nat -> Set ℂ) (n : Nat) : Set ℂ :=
  {z | ∃ j, j < n ∧ z ∈ S j}

@[simp]
theorem partialUnion_zero (S : Nat -> Set ℂ) :
    partialUnion S 0 = ∅ := by
  ext z
  simp [partialUnion]

theorem partialUnion_succ (S : Nat -> Set ℂ) (n : Nat) :
    partialUnion S (n + 1) = partialUnion S n ∪ S n := by
  ext z
  constructor
  · rintro ⟨j, hj, hz⟩
    by_cases hjn : j < n
    · exact Or.inl ⟨j, hjn, hz⟩
    · have hjeq : j = n := by omega
      exact Or.inr (by simpa [hjeq] using hz)
  · rintro (⟨j, hj, hz⟩ | hz)
    · exact ⟨j, Nat.lt_trans hj (Nat.lt_succ_self n), hz⟩
    · exact ⟨n, Nat.lt_succ_self n, hz⟩

@[simp]
theorem partialUnion_one (S : Nat -> Set ℂ) :
    partialUnion S 1 = S 0 := by
  ext z
  simp [partialUnion]

/-- Finite partial unions are countable when each included stratum is countable. -/
theorem partialUnion_countable_of_strata_countable {S : Nat -> Set ℂ} {m : Nat}
    (hS : ∀ j, j < m -> (S j).Countable) :
    ∀ n, n ≤ m -> (partialUnion S n).Countable := by
  intro n hn
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [partialUnion_succ]
      exact (ih (Nat.le_trans (Nat.le_succ n) hn)).union (hS n hn)

/-- If every included stratum avoids the real axis, then each finite partial union also
avoids the real axis. -/
theorem partialUnion_avoids_real_of_strata_avoids_real {S : Nat -> Set ℂ} {m : Nat}
    (hS : ∀ j, j < m -> ∀ x : ℝ, (x : ℂ) ∉ S j) :
    ∀ n, n ≤ m -> ∀ x : ℝ, (x : ℂ) ∉ partialUnion S n := by
  intro n hn x hx
  rcases hx with ⟨j, hj, hxj⟩
  exact hS j (Nat.lt_of_lt_of_le hj hn) x hxj

/-- Indexed hypotheses for the descent part of `n_layer_proof.tex`, Lemma `strataacc`.

The TeX proof first proves these hypotheses from relative closed/discrete strata.  We keep
them explicit here so the Step 1 pole hierarchy can consume a clean accumulation interface.
-/
structure StrataSystem (S : Nat -> Set ℂ) (m : Nat) : Prop where
  closed_partial : ∀ n, n ≤ m -> IsClosed (partialUnion S n)
  noAccumIn : ∀ j, j < m -> NoAccumIn (S j) (partialUnion S j)ᶜ

namespace StrataSystem

theorem restrict {S : Nat -> Set ℂ} {m n : Nat} (h : StrataSystem S m) (hn : n ≤ m) :
    StrataSystem S n where
  closed_partial k hk := h.closed_partial k (Nat.le_trans hk hn)
  noAccumIn j hj := h.noAccumIn j (Nat.lt_of_lt_of_le hj hn)

/-- Extend a stratification system by one stratum.  Closedness of the enlarged partial
union is derived from the no-accumulation condition for the new stratum. -/
theorem succ {S : Nat -> Set ℂ} {n : Nat}
    (h : StrataSystem S n)
    (hnew : NoAccumIn (S n) (partialUnion S n)ᶜ) :
    StrataSystem S (n + 1) where
  closed_partial k hk := by
    by_cases hkn : k ≤ n
    · exact h.closed_partial k hkn
    · have hk_eq : k = n + 1 := by omega
      subst k
      rw [partialUnion_succ]
      exact IsClosed.union_of_noAccumIn_compl (h.closed_partial n le_rfl) hnew
  noAccumIn j hj := by
    by_cases hjn : j < n
    · exact h.noAccumIn j hjn
    · have hj_eq : j = n := by omega
      subst j
      exact hnew

/-- Build a finite stratification system from per-stratum no-accumulation facts.  This
packages the recursive closedness argument used in the TeX `strat` construction. -/
theorem of_noAccumIn {S : Nat -> Set ℂ} :
    ∀ m : Nat,
      (∀ j, j < m -> NoAccumIn (S j) (partialUnion S j)ᶜ) ->
        StrataSystem S m
  | 0, _hno => by
      refine ⟨?_, ?_⟩
      · intro n hn
        have hn0 : n = 0 := by omega
        subst n
        rw [partialUnion_zero]
        exact isClosed_empty
      · intro j hj
        omega
  | n + 1, hno => by
      exact (of_noAccumIn n (fun j hj => hno j (Nat.lt_trans hj (Nat.lt_succ_self n)))).succ
        (hno n (Nat.lt_succ_self n))

end StrataSystem

/-- One-step descent in `lem:strataacc`: the accumulation points of the first `n+1`
strata lie in the first `n` strata. -/
theorem acc_partialUnion_succ_subset {S : Nat -> Set ℂ} {n : Nat}
    (hS : StrataSystem S (n + 1)) :
    acc (partialUnion S (n + 1)) ⊆ partialUnion S n := by
  intro x hx
  by_contra hxnot
  have hxU : x ∈ (partialUnion S n)ᶜ := by simpa using hxnot
  have hU_nhds : (partialUnion S n)ᶜ ∈ nhds x :=
    (hS.closed_partial n (Nat.le_succ n)).isOpen_compl.mem_nhds hxU
  have hxlast : x ∈ acc (S n) := by
    rw [mem_derivedSet] at hx ⊢
    rw [accPt_iff_nhds] at hx ⊢
    intro V hV
    have hVU : V ∩ (partialUnion S n)ᶜ ∈ nhds x := Filter.inter_mem hV hU_nhds
    obtain ⟨y, hy, hyne⟩ := hx (V ∩ (partialUnion S n)ᶜ) hVU
    rcases hy with ⟨hyVU, hyT⟩
    rcases hyVU with ⟨hyV, hyComp⟩
    have hyLast : y ∈ S n := by
      rw [partialUnion_succ] at hyT
      rcases hyT with hprev | hlast
      · exact False.elim (hyComp hprev)
      · exact hlast
    exact ⟨y, ⟨hyV, hyLast⟩, hyne⟩
  exact hS.noAccumIn n (Nat.lt_succ_self n) x hxU hxlast

/-- Iterated descent in `lem:strataacc`: after `k` accumulations of an `m`-stratum
system, only the first `m-k` strata can remain. -/
theorem accIter_partialUnion_subset {S : Nat -> Set ℂ} {m : Nat}
    (hS : StrataSystem S m) :
    ∀ k : Nat, k ≤ m -> accIter k (partialUnion S m) ⊆ partialUnion S (m - k) := by
  intro k hk
  induction k with
  | zero =>
      simp [accIter]
  | succ k ih =>
      have hk_le_m : k ≤ m := Nat.le_trans (Nat.le_succ k) hk
      have hih : accIter k (partialUnion S m) ⊆ partialUnion S (m - k) := ih hk_le_m
      intro z hz
      have hzacc : z ∈ acc (accIter k (partialUnion S m)) := by
        simpa [accIter] using hz
      have hzprev : z ∈ acc (partialUnion S (m - k)) := acc_mono hih hzacc
      have hsubsucc : m - k = m - (k + 1) + 1 := by omega
      have hsys : StrataSystem S (m - (k + 1) + 1) := by
        exact hS.restrict (by omega)
      have hstep := acc_partialUnion_succ_subset (S := S) (n := m - (k + 1)) hsys
      exact hstep (by simpa [hsubsucc] using hzprev)

/-- In particular, `m` iterations leave nothing. -/
theorem accIter_partialUnion_eq_empty {S : Nat -> Set ℂ} {m : Nat}
    (hS : StrataSystem S m) :
    accIter m (partialUnion S m) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.2
  intro z hz
  have hsub := accIter_partialUnion_subset hS m le_rfl hz
  simp [partialUnion] at hsub

/-! ## Countable-complement connectedness and identity theorem -/

/-- `n_layer_proof.tex`, Lemma `connect`: the complement of a countable subset of `ℂ`
is path-connected.  We use mathlib's general real-vector-space theorem instead of
reformalizing the broken-line argument from the TeX proof. -/
theorem countable_compl_isPathConnected {E : Set ℂ} (hE : E.Countable) :
    IsPathConnected Eᶜ := by
  exact hE.isPathConnected_compl_of_one_lt_rank
    (by
      rw [Complex.rank_real_complex]
      norm_num)

/-- The preconnected form consumed by analytic identity theorems. -/
theorem countable_compl_isPreconnected {E : Set ℂ} (hE : E.Countable) :
    IsPreconnected Eᶜ :=
  (countable_compl_isPathConnected hE).isConnected.isPreconnected

/-- `n_layer_proof.tex`, Lemma `connect`, identity-theorem clause.

This version isolates exactly the complex-analytic input needed later: if two analytic
functions on the complement of a countable exceptional set agree on a set accumulating at
one point of that complement, then they agree on the whole complement.
-/
theorem analytic_eqOn_countable_compl_of_frequentlyEq
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    {E : Set ℂ} {F G : ℂ -> Y} {z0 : ℂ}
    (hE : E.Countable)
    (hF : AnalyticOnNhd ℂ F Eᶜ)
    (hG : AnalyticOnNhd ℂ G Eᶜ)
    (hz0 : z0 ∈ Eᶜ)
    (hfg : ∃ᶠ z in nhdsWithin z0 ({z0}ᶜ : Set ℂ), F z = G z) :
    Set.EqOn F G Eᶜ :=
  hF.eqOn_of_preconnected_of_frequently_eq hG (countable_compl_isPreconnected hE) hz0 hfg

/-- Agreement on a real tail gives punctured-neighborhood frequent equality at any real
basepoint strictly inside that tail. -/
theorem frequently_eq_nhdsWithin_of_forall_real_tail_eq {Y : Type*} {F G : ℂ -> Y}
    {T0 x0 : ℝ}
    (hx0 : T0 < x0)
    (hEq : ∀ t : ℝ, T0 < t -> F (t : ℂ) = G (t : ℂ)) :
    ∃ᶠ z in nhdsWithin (x0 : ℂ) ({(x0 : ℂ)}ᶜ : Set ℂ), F z = G z := by
  rw [frequently_nhdsWithin_iff]
  refine mem_closure_iff_frequently.mp ?_
  have hx_real : x0 ∈ closure (Set.Ioi x0 : Set ℝ) := by
    rw [closure_Ioi (α := ℝ) x0]
    simp [Set.mem_Ici]
  have hx_complex :
      (x0 : ℂ) ∈ closure (((fun t : ℝ => (t : ℂ)) '' (Set.Ioi x0 : Set ℝ))) := by
    simpa using mem_closure_image (Complex.continuous_ofReal.continuousAt) hx_real
  refine closure_mono ?_ hx_complex
  intro z hz
  rcases hz with ⟨t, ht, rfl⟩
  have hxt : x0 < t := Set.mem_Ioi.mp ht
  constructor
  · exact hEq t (lt_trans hx0 hxt)
  · simp [hxt.ne']

/-! ## Local pole-transfer interface -/

/-- `G` blows up at `τ` along punctured neighborhoods.  This is the filter form of
`|G(z)| -> ∞ as z -> τ, z != τ` used in `lem:transfer`. -/
def BlowsUpAt (G : ℂ -> ℂ) (τ : ℂ) : Prop :=
  Filter.Tendsto (fun z => ‖G z‖) (nhdsWithin τ ({τ}ᶜ : Set ℂ)) Filter.atTop

/-- Local boundedness along punctured neighborhoods. -/
def PuncturedBoundedAt (G : ℂ -> ℂ) (τ : ℂ) : Prop :=
  ∃ C : ℝ, ∀ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ), ‖G z‖ ≤ C

/-- A blowing-up term remains blowing up after adding a locally bounded term.
This is the norm estimate used in Claim C of `prop:A1`. -/
theorem BlowsUpAt.add_puncturedBounded {A B : ℂ -> ℂ} {τ : ℂ}
    (hA : BlowsUpAt A τ)
    (hB : PuncturedBoundedAt B τ) :
    BlowsUpAt (fun z => A z + B z) τ := by
  rcases hB with ⟨C, hC⟩
  rw [BlowsUpAt] at hA ⊢
  rw [Filter.tendsto_atTop] at hA ⊢
  intro M
  filter_upwards [hA (M + C), hC] with z hAz hBz
  have htri : ‖A z‖ ≤ ‖A z + B z‖ + ‖B z‖ := by
    calc
      ‖A z‖ = ‖(A z + B z) - B z‖ := by ring_nf
      _ ≤ ‖A z + B z‖ + ‖B z‖ := norm_sub_le _ _
  linarith

/-- A blowing-up term remains blowing up after multiplying by a factor tending to a
nonzero limit. -/
theorem BlowsUpAt.mul_tendsto_ne_zero {A G : ℂ -> ℂ} {τ g0 : ℂ}
    (hA : BlowsUpAt A τ)
    (hG : Filter.Tendsto G (nhdsWithin τ ({τ}ᶜ : Set ℂ)) (nhds g0))
    (hg0 : g0 ≠ 0) :
    BlowsUpAt (fun z => A z * G z) τ := by
  rw [BlowsUpAt] at hA ⊢
  rw [Filter.tendsto_atTop] at hA ⊢
  intro M
  let c : ℝ := ‖g0‖ / 2
  have hcpos : 0 < c := by
    dsimp [c]
    positivity
  have hGnear : ∀ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ), c ≤ ‖G z‖ := by
    have hnorm : Filter.Tendsto (fun z => ‖G z‖)
        (nhdsWithin τ ({τ}ᶜ : Set ℂ)) (nhds ‖g0‖) := hG.norm
    have hc_lt : c < ‖g0‖ := by
      dsimp [c]
      have hpos : 0 < ‖g0‖ := norm_pos_iff.mpr hg0
      linarith
    exact (hnorm.eventually (Ioi_mem_nhds hc_lt)).mono fun _ hz => hz.le
  filter_upwards [hA (M / c), hGnear] with z hAz hGz
  rw [norm_mul]
  have hMle : M ≤ ‖A z‖ * c := by
    have hmul := mul_le_mul_of_nonneg_right hAz hcpos.le
    field_simp [hcpos.ne'] at hmul
    simpa [mul_comm] using hmul
  exact hMle.trans (mul_le_mul_of_nonneg_left hGz (norm_nonneg _))

/-- Claim-C shape: a locally bounded term plus a blowing-up term times a nonzero limiting
coefficient blows up. -/
theorem BlowsUpAt.bounded_add_mul_tendsto_ne_zero {B A G : ℂ -> ℂ} {τ g0 : ℂ}
    (hB : PuncturedBoundedAt B τ)
    (hA : BlowsUpAt A τ)
    (hG : Filter.Tendsto G (nhdsWithin τ ({τ}ᶜ : Set ℂ)) (nhds g0))
    (hg0 : g0 ≠ 0) :
    BlowsUpAt (fun z => B z + A z * G z) τ := by
  have hmul := hA.mul_tendsto_ne_zero hG hg0
  simpa [add_comm] using hmul.add_puncturedBounded hB

/-- A point is isolated from an exceptional set along punctured neighborhoods.
This is the filter form of the isolated-point hypothesis in `lem:transfer`. -/
def IsPuncturedIsolated (E : Set ℂ) (τ : ℂ) : Prop :=
  ∀ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ), z ∉ E

/-- If `τ` is not in a closed exceptional set, then punctured neighborhoods of `τ`
eventually avoid that set. -/
theorem eventually_notMem_of_notMem_isClosed {E : Set ℂ} (hE : IsClosed E)
    {τ : ℂ} (hτ : τ ∉ E) :
    ∀ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ), z ∉ E := by
  have hnhds : Eᶜ ∈ nhds τ := hE.isOpen_compl.mem_nhds hτ
  have hwithin : Eᶜ ∈ nhdsWithin τ ({τ}ᶜ : Set ℂ) := nhdsWithin_le_nhds hnhds
  simpa [Filter.Eventually] using hwithin

/-- If a point is not an accumulation point of `A`, then punctured neighborhoods
eventually avoid `A`. -/
theorem eventually_notMem_of_not_mem_acc {A : Set ℂ} {τ : ℂ} (hτ : τ ∉ acc A) :
    ∀ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ), z ∉ A := by
  rw [acc, mem_derivedSet, accPt_iff_frequently_nhdsNE] at hτ
  exact Filter.not_frequently.mp hτ

/-- Converse filter form: if a punctured neighborhood of `τ` avoids `A`, then `τ` is
not an accumulation point of `A`. -/
theorem not_mem_acc_of_eventually_notMem {A : Set ℂ} {τ : ℂ}
    (hτ : ∀ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ), z ∉ A) :
    τ ∉ acc A := by
  rw [acc, mem_derivedSet, accPt_iff_frequently_nhdsNE]
  exact Filter.not_frequently.mpr hτ

/-- A zero of an analytic function is punctured-isolated when the function is not
locally identically zero there. -/
theorem analyticAt_eventually_ne_zero_nhdsWithin_of_not_eventually_zero
    {D : ℂ -> ℂ} {τ : ℂ}
    (hD : AnalyticAt ℂ D τ)
    (hnot : ¬ (∀ᶠ z in nhds τ, D z = 0)) :
    ∀ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ), D z ≠ 0 :=
  hD.eventually_eq_zero_or_eventually_ne_zero.resolve_left hnot

/-- If a set is contained in a denominator zero set, and that denominator is continuous
on a domain and punctured-isolated at every zero in the domain, then the set has no
accumulation point inside the domain. -/
theorem noAccumIn_of_subset_zeroSet_of_continuousAt_of_eventually_ne_zero
    {A U : Set ℂ} {D : ℂ -> ℂ}
    (hA : A ⊆ {z | D z = 0})
    (hDcont : ∀ τ, τ ∈ U -> ContinuousAt D τ)
    (hDisolated :
      ∀ τ, τ ∈ U -> D τ = 0 ->
        ∀ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ), D z ≠ 0) :
    NoAccumIn A U := by
  intro τ hτU
  apply not_mem_acc_of_eventually_notMem
  by_cases hzero : D τ = 0
  · have hne := hDisolated τ hτU hzero
    filter_upwards [hne] with z hz hAz
    exact hz (hA hAz)
  · have hne_nhds : ∀ᶠ z in nhds τ, D z ≠ 0 := by
      have hmem : D τ ∈ ({0}ᶜ : Set ℂ) := by simpa using hzero
      exact (hDcont τ hτU).eventually (isOpen_compl_singleton.mem_nhds hmem)
    have hne_within : ∀ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ), D z ≠ 0 :=
      nhdsWithin_le_nhds hne_nhds
    filter_upwards [hne_within] with z hz hAz
    exact hz (hA hAz)

/-- Analytic version of
`noAccumIn_of_subset_zeroSet_of_continuousAt_of_eventually_ne_zero`: the punctured
isolation of denominator zeros is reduced to the non-local-identity condition. -/
theorem noAccumIn_of_subset_zeroSet_of_analyticOnNhd_of_not_eventually_zero
    {A U : Set ℂ} {D : ℂ -> ℂ}
    (hA : A ⊆ {z | D z = 0})
    (hD : AnalyticOnNhd ℂ D U)
    (hnot :
      ∀ τ, τ ∈ U -> D τ = 0 -> ¬ (∀ᶠ z in nhds τ, D z = 0)) :
    NoAccumIn A U :=
  noAccumIn_of_subset_zeroSet_of_continuousAt_of_eventually_ne_zero hA
    (fun τ hτ => (hD τ hτ).continuousAt)
    (fun τ hτ hzero =>
      analyticAt_eventually_ne_zero_nhdsWithin_of_not_eventually_zero
        (hD τ hτ) (hnot τ hτ hzero))

/-- Topological part of `n_layer_proof.tex`, Auxiliary Lemma `stratpole`, item (i).

For a stratified system, a point of the `j`-th stratum lying in the regular domain of the
previous strata has a punctured neighborhood avoiding the partial union through stratum
`j`.  This is the isolated-point hypothesis needed by pole transfer.
-/
theorem strata_punctured_isolated_partialUnion_succ {S : Nat -> Set ℂ} {j : Nat} {τ : ℂ}
    (hS : StrataSystem S (j + 1))
    (_hτS : τ ∈ S j)
    (hτprev : τ ∉ partialUnion S j) :
    IsPuncturedIsolated (partialUnion S (j + 1)) τ := by
  have hnotPrev : ∀ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ), z ∉ partialUnion S j :=
    eventually_notMem_of_notMem_isClosed (hS.closed_partial j (Nat.le_succ j)) hτprev
  have hτU : τ ∈ (partialUnion S j)ᶜ := by simpa using hτprev
  have hτnotacc : τ ∉ acc (S j) := hS.noAccumIn j (Nat.lt_succ_self j) τ hτU
  have hnotSj : ∀ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ), z ∉ S j :=
    eventually_notMem_of_not_mem_acc hτnotacc
  filter_upwards [hnotPrev, hnotSj] with z hzPrev hzSj
  rw [partialUnion_succ]
  exact fun hz => hz.elim hzPrev hzSj

/-- Local contradiction in `n_layer_proof.tex`, Lemma `transfer`.

If `F` is continuous at `τ`, `F = G` eventually on punctured neighborhoods of `τ`, and
`G` blows up there, then contradiction.  The global identity theorem in `lem:transfer`
is responsible for producing `hEq`; this lemma is the local boundedness-vs-blow-up
argument after that continuation step.
-/
theorem no_eventuallyEq_of_continuousAt_of_blowsUpAt {F G : ℂ -> ℂ} {τ : ℂ}
    (hF : ContinuousAt F τ)
    (hEq : F =ᶠ[nhdsWithin τ ({τ}ᶜ : Set ℂ)] G)
    (hG : BlowsUpAt G τ) :
    False := by
  let M : ℝ := ‖F τ‖ + 1
  have hM : ‖F τ‖ < M := by simp [M]
  have hFbound : ∀ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ), ‖F z‖ < M := by
    have hnorm : ContinuousAt (fun z => ‖F z‖) τ := hF.norm
    exact (hnorm.eventually (Iio_mem_nhds hM)).filter_mono nhdsWithin_le_nhds
  have hGbig : ∀ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ), M < ‖G z‖ :=
    hG.eventually (Filter.Ioi_mem_atTop M)
  rcases (hEq.and (hFbound.and hGbig)).exists with ⟨z, hFG, hFz, hGz⟩
  rw [hFG] at hFz
  linarith

/-- Pole transfer after the global identity theorem has already identified `F` and `G`
on the common regular domain.

This formalizes the last paragraph of `n_layer_proof.tex`, Lemma `transfer`: away from a
closed exceptional set for `F`, the equality on the common domain extends to punctured
neighborhoods of an isolated pole of `G`, contradicting boundedness of the continuous
function `F` against blow-up of `G`.
-/
theorem pole_transfer_of_eqOn_compl {E_F E_G : Set ℂ} {F G : ℂ -> ℂ} {τ : ℂ}
    (hEFclosed : IsClosed E_F)
    (hFcont : τ ∉ E_F -> ContinuousAt F τ)
    (hEqOn : Set.EqOn F G (E_F ∪ E_G)ᶜ)
    (hGisol : IsPuncturedIsolated E_G τ)
    (hG : BlowsUpAt G τ) :
    τ ∈ E_F := by
  by_contra hτF
  have hnotEF : ∀ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ), z ∉ E_F :=
    eventually_notMem_of_notMem_isClosed hEFclosed hτF
  have hEq : F =ᶠ[nhdsWithin τ ({τ}ᶜ : Set ℂ)] G := by
    filter_upwards [hnotEF, hGisol] with z hzF hzG
    exact hEqOn (by simp [hzF, hzG])
  exact no_eventuallyEq_of_continuousAt_of_blowsUpAt (hFcont hτF) hEq hG

/-- Combined pole-transfer interface mirroring `n_layer_proof.tex`, Lemma `transfer`.

The equality hypothesis is stated as equality on a set accumulating at `z0` in the
regular domain.  The previous countable-complement identity theorem promotes that to
equality on the common regular domain, after which `pole_transfer_of_eqOn_compl` supplies
the local contradiction.
-/
theorem pole_transfer_of_frequentlyEq {E_F E_G : Set ℂ} {F G : ℂ -> ℂ} {z0 τ : ℂ}
    (hEFclosed : IsClosed E_F)
    (hEFcount : E_F.Countable)
    (hEGcount : E_G.Countable)
    (hF : AnalyticOnNhd ℂ F E_Fᶜ)
    (hGanalytic : AnalyticOnNhd ℂ G E_Gᶜ)
    (hz0 : z0 ∈ (E_F ∪ E_G)ᶜ)
    (hfg : ∃ᶠ z in nhdsWithin z0 ({z0}ᶜ : Set ℂ), F z = G z)
    (hFcont : τ ∉ E_F -> ContinuousAt F τ)
    (hGisol : IsPuncturedIsolated E_G τ)
    (hGblow : BlowsUpAt G τ) :
    τ ∈ E_F := by
  have hEcount : (E_F ∪ E_G).Countable := hEFcount.union hEGcount
  have hFcommon : AnalyticOnNhd ℂ F (E_F ∪ E_G)ᶜ := by
    refine hF.mono ?_
    intro z hz hEF
    exact hz (Or.inl hEF)
  have hGcommon : AnalyticOnNhd ℂ G (E_F ∪ E_G)ᶜ := by
    refine hGanalytic.mono ?_
    intro z hz hEG
    exact hz (Or.inr hEG)
  have hEqOn : Set.EqOn F G (E_F ∪ E_G)ᶜ :=
    analytic_eqOn_countable_compl_of_frequentlyEq hEcount hFcommon hGcommon hz0 hfg
  exact pole_transfer_of_eqOn_compl hEFclosed hFcont hEqOn hGisol hGblow

/-- Pole transfer when the identity-theorem input comes from agreement on a real tail. -/
theorem pole_transfer_of_real_tail_eq {E_F E_G : Set ℂ} {F G : ℂ -> ℂ}
    {T0 x0 : ℝ} {τ : ℂ}
    (hEFclosed : IsClosed E_F)
    (hEFcount : E_F.Countable)
    (hEGcount : E_G.Countable)
    (hF : AnalyticOnNhd ℂ F E_Fᶜ)
    (hGanalytic : AnalyticOnNhd ℂ G E_Gᶜ)
    (hx0 : T0 < x0)
    (hz0 : (x0 : ℂ) ∈ (E_F ∪ E_G)ᶜ)
    (hfg : ∀ t : ℝ, T0 < t -> F (t : ℂ) = G (t : ℂ))
    (hFcont : τ ∉ E_F -> ContinuousAt F τ)
    (hGisol : IsPuncturedIsolated E_G τ)
    (hGblow : BlowsUpAt G τ) :
    τ ∈ E_F :=
  pole_transfer_of_frequentlyEq hEFclosed hEFcount hEGcount hF hGanalytic hz0
    (frequently_eq_nhdsWithin_of_forall_real_tail_eq hx0 hfg)
    hFcont hGisol hGblow

/-! ## Complex sigmoid and first-stratum pole arithmetic

This block follows the "Sigmoid basics" lemma and the real-part comparison used in
Step 1, Step 4 of `prop:A1`.  The full stratified topology is added below this layer;
these facts are already useful independently for the base case and for comparing
first-stratum vertical lines.
-/

/-- Complex logistic sigmoid, meromorphic with poles at odd multiples of `π i`. -/
noncomputable def csig (z : ℂ) : ℂ := (1 + Complex.exp (-z))⁻¹

/-- The odd multiples of `π i`, denoted `Π` in the TeX proof. -/
def oddPiI : Set ℂ := {z | ∃ k : ℤ, z = (2 * (k : ℂ) + 1) * (Real.pi : ℂ) * Complex.I}

/-- `n_layer_proof.tex`, Lemma `sigmoid basics`: denominator zeros are exactly `Π`. -/
theorem one_add_exp_neg_eq_zero_iff (z : ℂ) :
    1 + Complex.exp (-z) = 0 ↔ z ∈ oddPiI := by
  rw [oddPiI, Set.mem_setOf_eq, add_comm, add_eq_zero_iff_eq_neg,
    show (-1 : ℂ) = Complex.exp ((Real.pi : ℂ) * Complex.I) from Complex.exp_pi_mul_I.symm,
    Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨-(n + 1), ?_⟩
    have : z = -((Real.pi : ℂ) * Complex.I + n * (2 * (Real.pi : ℂ) * Complex.I)) := by
      rw [← hn]
      ring
    rw [this]
    push_cast
    ring
  · rintro ⟨k, hk⟩
    refine ⟨-(k + 1), ?_⟩
    rw [hk]
    push_cast
    ring

/-- Points of `Π` have real part zero. -/
theorem re_eq_zero_of_one_add_exp_neg_eq_zero {z : ℂ}
    (hz : 1 + Complex.exp (-z) = 0) :
    z.re = 0 := by
  rw [one_add_exp_neg_eq_zero_iff] at hz
  obtain ⟨k, hk⟩ := hz
  rw [hk]
  simp

/-- The pole set of `csig` is not itself a neighbourhood of one of its points.

This is the local discreteness input used in the proof that `csig` is analytic away
from the denominator zeros and in downstream pole-isolation arguments.
-/
theorem sigmoidPoleSet_not_mem_nhds {ζ : ℂ} (hζ : 1 + Complex.exp (-ζ) = 0) :
    {z : ℂ | 1 + Complex.exp (-z) = 0} ∉ nhds ζ := by
  intro hnhds
  let seq : Nat → ℂ := fun n => ζ + (((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ)
  have htend_real : Filter.Tendsto (fun n : Nat => (1 : ℝ) / ((n : ℝ) + 1))
      Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have htend : Filter.Tendsto seq Filter.atTop (nhds ζ) := by
    simpa [seq] using
      tendsto_const_nhds.add ((Complex.continuous_ofReal.tendsto 0).comp htend_real)
  have hevent : ∀ᶠ n in Filter.atTop, seq n ∈ {z : ℂ | 1 + Complex.exp (-z) = 0} :=
    htend.eventually hnhds
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨N, hN⟩ := hevent
  have hpole_seq : 1 + Complex.exp (-(seq N)) = 0 := hN N le_rfl
  have hreζ : ζ.re = 0 := re_eq_zero_of_one_add_exp_neg_eq_zero hζ
  have hre_seq : (seq N).re = 0 := re_eq_zero_of_one_add_exp_neg_eq_zero hpole_seq
  have hstep_ne : (1 : ℝ) / ((N : ℝ) + 1) ≠ 0 := by positivity
  apply hstep_ne
  have hre : (seq N).re = ζ.re + (1 : ℝ) / ((N : ℝ) + 1) := by
    simp only [seq, Complex.add_re, Complex.ofReal_re]
  linarith

/-- The sigmoid denominator is entire. -/
theorem denom_analytic (z : ℂ) : AnalyticAt ℂ (fun w => 1 + Complex.exp (-w)) z := by
  have hdiff : Differentiable ℂ (fun w : ℂ => 1 + Complex.exp (-w)) :=
    (differentiable_const 1).add (differentiable_id.neg.cexp)
  exact hdiff.analyticAt z

/-- The complex sigmoid is meromorphic at every point. -/
theorem csig_meromorphicAt (z : ℂ) : MeromorphicAt csig z :=
  (denom_analytic z).meromorphicAt.inv

/-- Away from its denominator zeros, the complex sigmoid is analytic. -/
theorem csig_analyticAt {z : ℂ} (hz : 1 + Complex.exp (-z) ≠ 0) :
    AnalyticAt ℂ csig z :=
  (denom_analytic z).inv hz

/-- If the denominator of `csig ∘ H` tends to zero and is nonzero on punctured
neighborhoods, then `csig ∘ H` blows up.

This is the analytic mechanism in `n_layer_proof.tex`, Auxiliary Lemma `stratpole`,
item (ii).
-/
theorem csig_blowsUpAt_of_denom_tendsto_zero {H : ℂ -> ℂ} {τ : ℂ}
    (hden : Filter.Tendsto (fun z => 1 + Complex.exp (-(H z)))
      (nhdsWithin τ ({τ}ᶜ : Set ℂ)) (nhds 0))
    (hne : ∀ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ),
      1 + Complex.exp (-(H z)) ≠ 0) :
    BlowsUpAt (fun z => csig (H z)) τ := by
  have hwithin : Filter.Tendsto (fun z => 1 + Complex.exp (-(H z)))
      (nhdsWithin τ ({τ}ᶜ : Set ℂ)) (nhdsWithin 0 ({0}ᶜ : Set ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hden ?_
    filter_upwards [hne] with z hz
    simpa using hz
  simpa [BlowsUpAt, csig] using (tendsto_norm_inv_nhdsNE_zero_atTop.comp hwithin)

/-- Blow-up of `csig ∘ H` when `H` tends to a sigmoid pole and avoids the pole set
punctured-nearby.  This is the `j ≥ 2` branch of `stratpole(ii)` in abstract form. -/
theorem csig_blowsUpAt_of_tendsto_pole {H : ℂ -> ℂ} {τ ζ : ℂ}
    (hζ : ζ ∈ oddPiI)
    (hH : Filter.Tendsto H (nhdsWithin τ ({τ}ᶜ : Set ℂ)) (nhds ζ))
    (hne : ∀ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ),
      1 + Complex.exp (-(H z)) ≠ 0) :
    BlowsUpAt (fun z => csig (H z)) τ := by
  have hden_at : ContinuousAt (fun w : ℂ => 1 + Complex.exp (-w)) ζ :=
    (denom_analytic ζ).continuousAt
  have hzero : 1 + Complex.exp (-ζ) = 0 :=
    (one_add_exp_neg_eq_zero_iff ζ).2 hζ
  have hden : Filter.Tendsto (fun z => 1 + Complex.exp (-(H z)))
      (nhdsWithin τ ({τ}ᶜ : Set ℂ)) (nhds 0) := by
    simpa [hzero] using hden_at.tendsto.comp hH
  exact csig_blowsUpAt_of_denom_tendsto_zero hden hne

/-- The poles of `τ ↦ csig (lam * τ + b)`, indexed as in the TeX proof. -/
noncomputable def sigmoidPole (b lam : ℝ) (n : ℤ) : ℂ :=
  (((((2 * n + 1 : ℤ) : ℝ) * Real.pi : ℝ) : ℂ) * Complex.I - (b : ℂ)) / (lam : ℂ)

/-- `n_layer_proof.tex`, Lemma `sigmoid basics`: pole real parts lie on one vertical line. -/
theorem sigmoidPole_re {b lam : ℝ} (hlam : lam ≠ 0) (n : ℤ) :
    (sigmoidPole b lam n).re = -b / lam := by
  simp [sigmoidPole, Complex.div_re, Complex.normSq]
  field_simp [hlam]

theorem sigmoidPole_ne_zero_of_b_ne_zero {b lam : ℝ} (hb : b ≠ 0) (hlam : lam ≠ 0)
    (n : ℤ) :
    sigmoidPole b lam n ≠ 0 := by
  intro hζ
  have hre := congrArg Complex.re hζ
  rw [sigmoidPole_re hlam] at hre
  simp only [Complex.zero_re] at hre
  have hb0 : b = 0 := by
    field_simp [hlam] at hre
    linarith
  exact hb hb0

/-- The indexed first-stratum pole is exactly a zero of the affine sigmoid denominator. -/
theorem inner_denom_sigmoidPole (b lam : ℝ) (hlam : lam ≠ 0) (n : ℤ) :
    1 + Complex.exp (-((lam : ℂ) * sigmoidPole b lam n + (b : ℂ))) = 0 := by
  rw [one_add_exp_neg_eq_zero_iff]
  refine ⟨n, ?_⟩
  have hlamC : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam
  rw [sigmoidPole, mul_comm, div_mul_cancel₀ _ hlamC]
  push_cast
  ring

/-- The affine sigmoid denominator is analytic. -/
theorem affine_denom_analyticAt (b lam : ℝ) (z : ℂ) :
    AnalyticAt ℂ (fun τ : ℂ => 1 + Complex.exp (-((lam : ℂ) * τ + (b : ℂ)))) z := by
  have haff : AnalyticAt ℂ (fun τ : ℂ => (lam : ℂ) * τ + (b : ℂ)) z :=
    (analyticAt_const.mul analyticAt_id).add analyticAt_const
  exact analyticAt_const.add (haff.neg.cexp')

/-- At an affine sigmoid pole with nonzero slope, the denominator is not identically zero
near the pole. -/
theorem affine_denom_not_eventually_zero_at_sigmoidPole (b lam : ℝ) (hlam : lam ≠ 0)
    (n : ℤ) :
    ¬ (∀ᶠ z in nhds (sigmoidPole b lam n),
      1 + Complex.exp (-((lam : ℂ) * z + (b : ℂ))) = 0) := by
  intro hzero
  set ζ : ℂ := sigmoidPole b lam n
  set D : ℂ -> ℂ := fun z => 1 + Complex.exp (-((lam : ℂ) * z + (b : ℂ))) with hD
  have hpole : D ζ = 0 := by
    rw [hD]
    change 1 + Complex.exp (-((lam : ℂ) * sigmoidPole b lam n + (b : ℂ))) = 0
    exact inner_denom_sigmoidPole b lam hlam n
  have hexpζ : Complex.exp (-((lam : ℂ) * ζ + (b : ℂ))) = -1 := by
    linear_combination hpole
  have hlin : HasDerivAt (fun z : ℂ => (lam : ℂ) * z + (b : ℂ)) (lam : ℂ) ζ := by
    have hmul : HasDerivAt (fun z : ℂ => (lam : ℂ) * z) (lam : ℂ) ζ := by
      simpa using (hasDerivAt_id ζ).const_mul (lam : ℂ)
    have hc : HasDerivAt (fun _ : ℂ => (b : ℂ)) 0 ζ := hasDerivAt_const ζ (b : ℂ)
    convert hmul.add hc using 1
    ring
  have hderiv : HasDerivAt D (lam : ℂ) ζ := by
    rw [hD]
    have hneg : HasDerivAt (fun z : ℂ => -((lam : ℂ) * z + (b : ℂ))) (-(lam : ℂ)) ζ := by
      convert hlin.neg using 1
    have hexp : HasDerivAt
        (fun z : ℂ => Complex.exp (-((lam : ℂ) * z + (b : ℂ))))
        (Complex.exp (-((lam : ℂ) * ζ + (b : ℂ))) * (-(lam : ℂ))) ζ :=
      hneg.cexp
    have h := (hasDerivAt_const ζ (1 : ℂ)).add hexp
    convert h using 1
    rw [hexpζ]
    ring
  have hDzero : D =ᶠ[nhds ζ] fun _ : ℂ => 0 := by
    simpa [D, ζ] using hzero
  have hderiv0 : HasDerivAt D 0 ζ :=
    (hDzero.hasDerivAt_iff).mpr (hasDerivAt_const ζ (0 : ℂ))
  have hlamC0 : (lam : ℂ) = 0 := hderiv.unique hderiv0
  exact (Complex.ofReal_ne_zero.mpr hlam) hlamC0

/-- Punctured-neighborhood nonvanishing of the affine sigmoid denominator at a simple pole. -/
theorem affine_denom_eventually_ne_zero_nhdsWithin_sigmoidPole (b lam : ℝ)
    (hlam : lam ≠ 0) (n : ℤ) :
    ∀ᶠ z in nhdsWithin (sigmoidPole b lam n) ({sigmoidPole b lam n}ᶜ : Set ℂ),
      1 + Complex.exp (-((lam : ℂ) * z + (b : ℂ))) ≠ 0 := by
  have hD : AnalyticAt ℂ
      (fun z : ℂ => 1 + Complex.exp (-((lam : ℂ) * z + (b : ℂ))))
      (sigmoidPole b lam n) :=
    affine_denom_analyticAt b lam (sigmoidPole b lam n)
  exact hD.eventually_eq_zero_or_eventually_ne_zero.resolve_left
    (affine_denom_not_eventually_zero_at_sigmoidPole b lam hlam n)

/-- Base stratum blow-up: `τ ↦ csig(lam * τ + b)` blows up at its affine sigmoid
poles.  This is the `j = 1` branch of `stratpole(ii)`. -/
theorem affine_csig_blowsUpAt_sigmoidPole (b lam : ℝ) (hlam : lam ≠ 0) (n : ℤ) :
    BlowsUpAt (fun τ : ℂ => csig ((lam : ℂ) * τ + (b : ℂ))) (sigmoidPole b lam n) := by
  have hden : Filter.Tendsto
      (fun τ : ℂ => 1 + Complex.exp (-((lam : ℂ) * τ + (b : ℂ))))
      (nhdsWithin (sigmoidPole b lam n) ({sigmoidPole b lam n}ᶜ : Set ℂ)) (nhds 0) := by
    have hcont : ContinuousAt
        (fun τ : ℂ => 1 + Complex.exp (-((lam : ℂ) * τ + (b : ℂ))))
        (sigmoidPole b lam n) :=
      (affine_denom_analyticAt b lam (sigmoidPole b lam n)).continuousAt
    have hzero :
        1 + Complex.exp (-((lam : ℂ) * sigmoidPole b lam n + (b : ℂ))) = 0 :=
      inner_denom_sigmoidPole b lam hlam n
    have ht : Filter.Tendsto
        (fun τ : ℂ => 1 + Complex.exp (-((lam : ℂ) * τ + (b : ℂ))))
        (nhdsWithin (sigmoidPole b lam n) ({sigmoidPole b lam n}ᶜ : Set ℂ))
        (nhds (1 + Complex.exp (-((lam : ℂ) * sigmoidPole b lam n + (b : ℂ))))) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    change Filter.Tendsto
      (fun τ : ℂ => 1 + Complex.exp (-((lam : ℂ) * τ + (b : ℂ))))
      (nhdsWithin (sigmoidPole b lam n) ({sigmoidPole b lam n}ᶜ : Set ℂ))
      (nhds (1 + Complex.exp (-((lam : ℂ) * sigmoidPole b lam n + (b : ℂ))))) at ht
    rw [hzero] at ht
    exact ht
  exact csig_blowsUpAt_of_denom_tendsto_zero hden
    (affine_denom_eventually_ne_zero_nhdsWithin_sigmoidPole b lam hlam n)

/-- The first stratum of a nonconstant affine sigmoid gate, written as a set. -/
noncomputable def firstPoleSet (b lam : ℝ) : Set ℂ :=
  Set.range (sigmoidPole b lam)

theorem sigmoidPole_mem_firstPoleSet (b lam : ℝ) (n : ℤ) :
    sigmoidPole b lam n ∈ firstPoleSet b lam :=
  ⟨n, rfl⟩

/-- Step 1, final comparison: equality of one primed and one unprimed pole forces slopes equal. -/
theorem slope_eq_of_sigmoidPole_eq {b lam lam' : ℝ} (hb : b ≠ 0)
    (hlam : lam ≠ 0) (hlam' : lam' ≠ 0) {n m : ℤ}
    (h : sigmoidPole b lam' n = sigmoidPole b lam m) : lam = lam' := by
  have hre := congrArg Complex.re h
  rw [sigmoidPole_re hlam', sigmoidPole_re hlam] at hre
  field_simp [hb, hlam, hlam'] at hre
  linarith

/-- Step 1, final comparison in inclusion form. -/
theorem slope_eq_of_sigmoidPole_subset {b lam lam' : ℝ} (hb : b ≠ 0)
    (hlam : lam ≠ 0) (hlam' : lam' ≠ 0)
    (hsub : ∀ n : ℤ, ∃ m : ℤ, sigmoidPole b lam' n = sigmoidPole b lam m) :
    lam = lam' := by
  obtain ⟨m, hm⟩ := hsub 0
  exact slope_eq_of_sigmoidPole_eq hb hlam hlam' hm

/-- Step 1, final comparison in first-stratum set form: `S'¹ ⊆ S¹` forces slopes equal. -/
theorem slope_eq_of_firstPoleSet_subset {b lam lam' : ℝ} (hb : b ≠ 0)
    (hlam : lam ≠ 0) (hlam' : lam' ≠ 0)
    (hsub : firstPoleSet b lam' ⊆ firstPoleSet b lam) :
    lam = lam' := by
  refine slope_eq_of_sigmoidPole_subset hb hlam hlam' ?_
  intro n
  obtain ⟨m, hm⟩ := hsub (sigmoidPole_mem_firstPoleSet b lam' n)
  exact ⟨m, hm.symm⟩

/-- On real arguments, `csig` agrees with the real sigmoid. -/
theorem csig_ofReal (x : ℝ) : csig (x : ℂ) = ((sig x : ℝ) : ℂ) := by
  have hexp : Complex.exp (-(x : ℂ)) = ((Real.exp (-x) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp, Complex.ofReal_neg]
  rw [csig, sig, hexp]
  norm_cast

end TransformerIdentifiability.NLayer
