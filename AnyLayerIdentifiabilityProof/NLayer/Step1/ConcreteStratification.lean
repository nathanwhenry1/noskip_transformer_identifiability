import AnyLayerIdentifiabilityProof.NLayer.Analytic.Stratification
import AnyLayerIdentifiabilityProof.NLayer.Step1.AnalyticSupport
import AnyLayerIdentifiabilityProof.NLayer.Step1.OStar
import AnyLayerIdentifiabilityProof.NLayer.Step1.PolynomialFamily

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer

open Matrix

/-!
# Concrete Step 1 stratification

Owner shard for the transformer-specific constant-probe stratum construction used by
Step 1: concrete `S^j`, `Omega_j`, `H_j`, `s_j`, the first-stratum formula,
`StrataSystem`, concrete `stratpole`, and the `lastlayer` interface.
-/

/-! ## First-stratum and last-layer packages -/

/-- First-stratum formula expected from the concrete constant-probe stratification.

When the first affine slope is nonzero, the first stratum is the standard affine sigmoid
pole set.  When the slope is zero, the first stratum is empty. -/
structure FirstStratumFormula (S0 : Set ℂ) (b lambda : ℝ) : Prop where
  nonzero : lambda ≠ 0 -> S0 = firstPoleSet b lambda
  zero : lambda = 0 -> S0 = ∅

/-- Real numbers are never odd multiples of `π i`. -/
theorem ofReal_not_mem_oddPiI (b : ℝ) : (b : ℂ) ∉ oddPiI := by
  rintro ⟨k, hk⟩
  have him := congrArg Complex.im hk
  have hodd_ne : (((2 * k + 1 : ℤ) : ℝ) : ℝ) ≠ 0 := by
    norm_cast
    omega
  have hpi_ne : (((2 * k + 1 : ℤ) : ℝ) * Real.pi) ≠ 0 :=
    mul_ne_zero hodd_ne Real.pi_ne_zero
  exact hpi_ne (by simpa using him.symm)

/-- Affine preactivation values hit `Π` exactly at the indexed affine sigmoid poles. -/
theorem affine_mem_oddPiI_iff_sigmoidPole {b lambda : ℝ} (hlambda : lambda ≠ 0)
    {τ : ℂ} :
    (lambda : ℂ) * τ + (b : ℂ) ∈ oddPiI ↔
      ∃ n : ℤ, τ = sigmoidPole b lambda n := by
  constructor
  · intro hτ
    rcases hτ with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hlambdaC : (lambda : ℂ) ≠ 0 := by exact_mod_cast hlambda
    calc
      τ = (((lambda : ℂ) * τ + (b : ℂ)) - (b : ℂ)) / (lambda : ℂ) := by
        field_simp [hlambdaC]
        ring
      _ = sigmoidPole b lambda n := by
        rw [hn, sigmoidPole]
        push_cast
        ring
  · rintro ⟨n, rfl⟩
    rw [← one_add_exp_neg_eq_zero_iff]
    exact inner_denom_sigmoidPole b lambda hlambda n

/-- First stratum cut out by the affine preactivation hitting `Π`. -/
noncomputable def affineOddPiIStratum (b lambda : ℝ) : Set ℂ :=
  {τ | (lambda : ℂ) * τ + (b : ℂ) ∈ oddPiI}

/-- The affine-`Π` stratum is exactly the zero set of the affine sigmoid denominator. -/
theorem affineOddPiIStratum_eq_denom_zero (b lambda : ℝ) :
    affineOddPiIStratum b lambda =
      {τ : ℂ | 1 + Complex.exp (-((lambda : ℂ) * τ + (b : ℂ))) = 0} := by
  ext τ
  exact (one_add_exp_neg_eq_zero_iff ((lambda : ℂ) * τ + (b : ℂ))).symm

/-- The affine sigmoid denominator is continuous. -/
theorem affine_denom_continuous (b lambda : ℝ) :
    Continuous (fun τ : ℂ => 1 + Complex.exp (-((lambda : ℂ) * τ + (b : ℂ)))) := by
  rw [continuous_iff_continuousAt]
  intro τ
  exact (affine_denom_analyticAt b lambda τ).continuousAt

/-- The affine first stratum is closed. -/
theorem affineOddPiIStratum_closed (b lambda : ℝ) :
    IsClosed (affineOddPiIStratum b lambda) := by
  rw [affineOddPiIStratum_eq_denom_zero]
  exact isClosed_singleton.preimage (affine_denom_continuous b lambda)

theorem affineOddPiIStratum_eq_firstPoleSet_of_lambda_ne_zero {b lambda : ℝ}
    (hlambda : lambda ≠ 0) :
    affineOddPiIStratum b lambda = firstPoleSet b lambda := by
  ext τ
  constructor
  · intro hτ
    rcases (affine_mem_oddPiI_iff_sigmoidPole hlambda).mp hτ with ⟨n, hn⟩
    exact ⟨n, hn.symm⟩
  · rintro ⟨n, hn⟩
    exact (affine_mem_oddPiI_iff_sigmoidPole hlambda).mpr ⟨n, hn.symm⟩

theorem affineOddPiIStratum_eq_empty_of_lambda_eq_zero {b lambda : ℝ}
    (hlambda : lambda = 0) :
    affineOddPiIStratum b lambda = ∅ := by
  ext τ
  simp [affineOddPiIStratum, hlambda, ofReal_not_mem_oddPiI b]

/-- The affine first stratum is countable: for nonzero slope it is indexed by `ℤ`, and
for zero slope it is empty. -/
theorem affineOddPiIStratum_countable (b lambda : ℝ) :
    (affineOddPiIStratum b lambda).Countable := by
  by_cases hlambda : lambda = 0
  · rw [affineOddPiIStratum_eq_empty_of_lambda_eq_zero hlambda]
    simp
  · rw [affineOddPiIStratum_eq_firstPoleSet_of_lambda_ne_zero hlambda]
    exact Set.countable_range (sigmoidPole b lambda)

/-- The affine first stratum never meets the real axis. -/
theorem affineOddPiIStratum_avoids_real (b lambda : ℝ) (x : ℝ) :
    (x : ℂ) ∉ affineOddPiIStratum b lambda := by
  intro hx
  have hreal :
      (lambda : ℂ) * (x : ℂ) + (b : ℂ) = ((lambda * x + b : ℝ) : ℂ) := by
    norm_num
  rw [affineOddPiIStratum, Set.mem_setOf_eq, hreal] at hx
  exact ofReal_not_mem_oddPiI (lambda * x + b) hx

/-- The affine first stratum has no accumulation point in the whole plane. -/
theorem affineOddPiIStratum_noAccumIn_univ (b lambda : ℝ) :
    NoAccumIn (affineOddPiIStratum b lambda) Set.univ := by
  intro ζ _hζ
  by_cases hζS : ζ ∈ affineOddPiIStratum b lambda
  · by_cases hlambda : lambda = 0
    · rw [affineOddPiIStratum_eq_empty_of_lambda_eq_zero hlambda] at hζS
      simp at hζS
    · rcases (affine_mem_oddPiI_iff_sigmoidPole (b := b) hlambda).mp hζS
        with ⟨n, hζeq⟩
      rw [hζeq]
      apply not_mem_acc_of_eventually_notMem
      have hden :=
        affine_denom_eventually_ne_zero_nhdsWithin_sigmoidPole b lambda hlambda n
      filter_upwards [hden] with z hzne hzS
      have hzden : 1 + Complex.exp (-((lambda : ℂ) * z + (b : ℂ))) = 0 := by
        simpa [affineOddPiIStratum_eq_denom_zero] using hzS
      exact hzne hzden
  · exact not_mem_acc_of_eventually_notMem
      (eventually_notMem_of_notMem_isClosed
        (affineOddPiIStratum_closed b lambda) hζS)

/-- The affine-`Π` description is already a first-stratum formula. -/
theorem firstStratumFormula_affineOddPiI (b lambda : ℝ) :
    FirstStratumFormula (affineOddPiIStratum b lambda) b lambda where
  nonzero := affineOddPiIStratum_eq_firstPoleSet_of_lambda_ne_zero
  zero := affineOddPiIStratum_eq_empty_of_lambda_eq_zero

namespace FirstStratumFormula

/-- Transport a formula across a proved set equality. -/
theorem congr {S0 T0 : Set ℂ} {b lambda : ℝ}
    (F : FirstStratumFormula S0 b lambda) (h : T0 = S0) :
    FirstStratumFormula T0 b lambda where
  nonzero := by
    intro hlambda
    rw [h]
    exact F.nonzero hlambda
  zero := by
    intro hlambda
    rw [h]
    exact F.zero hlambda

/-- Build the first-stratum formula from an affine preactivation hitting `Π`. -/
theorem of_eq_affineOddPiIStratum {S0 : Set ℂ} {b lambda : ℝ}
    (hS0 : S0 = affineOddPiIStratum b lambda) :
    FirstStratumFormula S0 b lambda :=
  (firstStratumFormula_affineOddPiI b lambda).congr hS0

end FirstStratumFormula

/-- Scalar last-layer expansion for a fixed constant probe and a fixed output
coordinate.

The concrete transformer formula supplies the coefficient functions.  Downstream Claim C
usually consumes the split form at `m + 1`, separating the last gate from the bounded
lower-layer contribution. -/
structure LastLayerExpansion (s : Nat -> ℂ -> ℂ) (m : Nat) (observable : ℂ -> ℂ) where
  base : ℂ
  coeff : Nat -> ℂ -> ℂ
  formula : ∀ τ : ℂ, observable τ = base + ∑ i ∈ Finset.range m, s i τ * coeff i τ

namespace LastLayerExpansion

/-- Replace the observable by a pointwise equal one. -/
def congr {s : Nat -> ℂ -> ℂ} {m : Nat} {observable observable' : ℂ -> ℂ}
    (E : LastLayerExpansion s m observable) (h : ∀ τ, observable' τ = observable τ) :
    LastLayerExpansion s m observable' where
  base := E.base
  coeff := E.coeff
  formula := by
    intro τ
    rw [h τ, E.formula τ]

/-- The zero-gate expansion of a constant observable. -/
noncomputable def const {s : Nat -> ℂ -> ℂ} (base : ℂ) :
    LastLayerExpansion s 0 (fun _ : ℂ => base) where
  base := base
  coeff := fun _ _ => 0
  formula := by
    intro τ
    simp

/-- Coefficients obtained by appending a final gate coefficient at index `m`. -/
noncomputable def coeffSnoc (coeff : Nat -> ℂ -> ℂ) (lastCoeff : ℂ -> ℂ)
    (m : Nat) : Nat -> ℂ -> ℂ :=
  fun i => if i = m then lastCoeff else coeff i

@[simp]
theorem coeffSnoc_apply_self (coeff : Nat -> ℂ -> ℂ) (lastCoeff : ℂ -> ℂ)
    (m : Nat) (τ : ℂ) :
    coeffSnoc coeff lastCoeff m m τ = lastCoeff τ := by
  simp [coeffSnoc]

theorem coeffSnoc_apply_of_ne (coeff : Nat -> ℂ -> ℂ) (lastCoeff : ℂ -> ℂ)
    {m i : Nat} (hi : i ≠ m) (τ : ℂ) :
    coeffSnoc coeff lastCoeff m i τ = coeff i τ := by
  simp [coeffSnoc, hi]

/-- Append one final gate term to an existing lower expansion. -/
noncomputable def snoc {s : Nat -> ℂ -> ℂ} {m : Nat}
    {lowerObservable observable : ℂ -> ℂ}
    (E : LastLayerExpansion s m lowerObservable) (lastCoeff : ℂ -> ℂ)
    (hobservable : ∀ τ, observable τ = lowerObservable τ + s m τ * lastCoeff τ) :
    LastLayerExpansion s (m + 1) observable where
  base := E.base
  coeff := coeffSnoc E.coeff lastCoeff m
  formula := by
    intro τ
    have hsum :
        (∑ i ∈ Finset.range m,
          s i τ * coeffSnoc E.coeff lastCoeff m i τ) =
        ∑ i ∈ Finset.range m, s i τ * E.coeff i τ := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have him : i ≠ m := Nat.ne_of_lt (Finset.mem_range.mp hi)
      rw [coeffSnoc_apply_of_ne E.coeff lastCoeff him]
    calc
      observable τ = lowerObservable τ + s m τ * lastCoeff τ := hobservable τ
      _ = (E.base + ∑ i ∈ Finset.range m, s i τ * E.coeff i τ)
            + s m τ * lastCoeff τ := by
          rw [E.formula τ]
      _ = E.base + ∑ i ∈ Finset.range (m + 1),
            s i τ * coeffSnoc E.coeff lastCoeff m i τ := by
          rw [Finset.sum_range_succ, hsum, coeffSnoc_apply_self]
          ring

/-- Finite linear combinations of scalar expansions, with constant weights. -/
noncomputable def fintypeLinearCombination {ι : Type*} [Fintype ι]
    {s : Nat -> ℂ -> ℂ} {m : Nat} (weight : ι -> ℂ)
    {observable : ι -> ℂ -> ℂ}
    (E : ∀ i, LastLayerExpansion s m (observable i)) :
    LastLayerExpansion s m (fun τ => ∑ i, weight i * observable i τ) where
  base := ∑ i, weight i * (E i).base
  coeff := fun j τ => ∑ i, weight i * (E i).coeff j τ
  formula := by
    intro τ
    calc
      (∑ i, weight i * observable i τ)
          = ∑ i, weight i * ((E i).base + ∑ j ∈ Finset.range m,
              s j τ * (E i).coeff j τ) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [(E i).formula τ]
      _ = (∑ i, weight i * (E i).base) +
            ∑ i, weight i * (∑ j ∈ Finset.range m,
              s j τ * (E i).coeff j τ) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl ?_
            intro i _hi
            ring
      _ = (∑ i, weight i * (E i).base) +
            ∑ j ∈ Finset.range m, s j τ * (∑ i, weight i * (E i).coeff j τ) := by
            congr 1
            calc
              (∑ i, weight i * (∑ j ∈ Finset.range m,
                s j τ * (E i).coeff j τ))
                  = ∑ i, ∑ j ∈ Finset.range m,
                      weight i * (s j τ * (E i).coeff j τ) := by
                    refine Finset.sum_congr rfl ?_
                    intro i _hi
                    rw [Finset.mul_sum]
              _ = ∑ j ∈ Finset.range m, ∑ i,
                      weight i * (s j τ * (E i).coeff j τ) := by
                    rw [Finset.sum_comm]
              _ = ∑ j ∈ Finset.range m,
                    s j τ * (∑ i, weight i * (E i).coeff j τ) := by
                    refine Finset.sum_congr rfl ?_
                    intro j _hj
                    rw [Finset.mul_sum]
                    refine Finset.sum_congr rfl ?_
                    intro i _hi
                    ring

/-- The lower-layer contribution when an expansion has a final `m`-th gate. -/
noncomputable def lower {s : Nat -> ℂ -> ℂ} {observable : ℂ -> ℂ} {m : Nat}
    (E : LastLayerExpansion s (m + 1) observable) : ℂ -> ℂ :=
  fun τ => E.base + ∑ i ∈ Finset.range m, s i τ * E.coeff i τ

/-- Split the full sum into lower terms and the last gate. -/
theorem formula_last {s : Nat -> ℂ -> ℂ} {observable : ℂ -> ℂ} {m : Nat}
    (E : LastLayerExpansion s (m + 1) observable) (τ : ℂ) :
    observable τ = E.lower τ + s m τ * E.coeff m τ := by
  calc
    observable τ = E.base + ∑ i ∈ Finset.range (m + 1), s i τ * E.coeff i τ :=
      E.formula τ
    _ = E.base + ((∑ i ∈ Finset.range m, s i τ * E.coeff i τ) +
        s m τ * E.coeff m τ) := by
      rw [Finset.sum_range_succ]
    _ = E.lower τ + s m τ * E.coeff m τ := by
      rw [lower]
      ring

/-- Lower-layer terms are punctured-neighborhood bounded if each lower gate and
coefficient is. -/
theorem lower_puncturedBounded {s : Nat -> ℂ -> ℂ} {observable : ℂ -> ℂ} {m : Nat}
    (E : LastLayerExpansion s (m + 1) observable) {τ : ℂ}
    (hs : ∀ i, i < m -> PuncturedBoundedAt (s i) τ)
    (hc : ∀ i, i < m -> PuncturedBoundedAt (E.coeff i) τ) :
    PuncturedBoundedAt E.lower τ := by
  have hsum : PuncturedBoundedAt
      (fun z => ∑ i ∈ Finset.range m, s i z * E.coeff i z) τ := by
    refine PuncturedBoundedAt.finset_sum (Finset.range m)
      (F := fun i z => s i z * E.coeff i z) (τ := τ) ?_
    intro i hi
    exact (hs i (Finset.mem_range.mp hi)).mul (hc i (Finset.mem_range.mp hi))
  exact (PuncturedBoundedAt.const E.base τ).add hsum

/-- Claim-C-ready consequence of the split last-layer formula. -/
theorem observable_blowsUpAt_of_last_gate {s : Nat -> ℂ -> ℂ} {observable : ℂ -> ℂ}
    {m : Nat} (E : LastLayerExpansion s (m + 1) observable) {τ visible0 : ℂ}
    (hlower : PuncturedBoundedAt E.lower τ)
    (hgate : BlowsUpAt (s m) τ)
    (hvisible : Filter.Tendsto (E.coeff m) (nhdsWithin τ ({τ}ᶜ : Set ℂ)) (nhds visible0))
    (hvisible0 : visible0 ≠ 0) :
    BlowsUpAt observable τ := by
  have hsplit : BlowsUpAt (fun z => E.lower z + s m z * E.coeff m z) τ :=
    hgate.bounded_add_mul_tendsto_ne_zero hlower hvisible hvisible0
  have hEq : observable = fun z => E.lower z + s m z * E.coeff m z := by
    funext z
    exact E.formula_last z
  rw [hEq]
  exact hsplit

end LastLayerExpansion

/-! ## Constant-probe stratification package -/

/-- The real first-layer slope for a fixed constant probe and layer stream. -/
noncomputable def constantProbeFirstSlope {d : Nat} (θ : LayerStream d)
    (w v : Fin d -> ℝ) : ℝ :=
  w ⬝ᵥ ((θ 0).2 *ᵥ v)

/-- The concrete stream-level first slope agrees with the public finite-parameter API. -/
theorem constantProbeFirstSlope_paramStream_eq_firstSlope {L d : Nat}
    (θ : Params L d) (w v : Fin d -> ℝ) :
    constantProbeFirstSlope (paramStream θ) w v = firstSlope θ w v := by
  rfl

/-- Concrete gate stream for a fixed constant probe.

The definition is well-founded in the gate index: `s_j` evaluates the formal
preactivation using only gates `s_i` with `i < j`, and zero-pads later coordinates. -/
noncomputable def constantProbeGate {d : Nat} (θ : LayerStream d) (b : ℝ)
    (w v : Fin d -> ℝ) (j : Nat) (τ : ℂ) : ℂ :=
  csig (τ * formalPhi θ j
    (fun i => if _h : i < j then constantProbeGate θ b w v i τ else 0) w v + (b : ℂ))
termination_by j
decreasing_by exact _h

/-- Zero-padded gate assignment used to evaluate the `j`-th formal preactivation. -/
noncomputable def constantProbeGatePrefix {d : Nat} (θ : LayerStream d) (b : ℝ)
    (w v : Fin d -> ℝ) (j : Nat) (τ : ℂ) : Nat -> ℂ :=
  fun i => if _h : i < j then constantProbeGate θ b w v i τ else 0

/-- Concrete preactivation `H_j(τ) = τ φ_{j+1}(s_{<j}(τ);w,v) + b`. -/
noncomputable def constantProbeGateArgument {d : Nat} (θ : LayerStream d) (b : ℝ)
    (w v : Fin d -> ℝ) (j : Nat) : ℂ -> ℂ :=
  fun τ => τ * formalPhi θ j (constantProbeGatePrefix θ b w v j τ) w v + (b : ℂ)

/-- Sigmoid denominator for the `j`-th concrete constant-probe gate. -/
noncomputable def constantProbeDenom {d : Nat} (θ : LayerStream d) (b : ℝ)
    (w v : Fin d -> ℝ) (j : Nat) : ℂ -> ℂ :=
  fun τ => 1 + Complex.exp (-(constantProbeGateArgument θ b w v j τ))

/-- The recursively defined concrete gate is `csig ∘ H_j`. -/
theorem constantProbeGate_eq_csig {d : Nat} (θ : LayerStream d) (b : ℝ)
    (w v : Fin d -> ℝ) (j : Nat) :
    constantProbeGate θ b w v j =
      fun τ => csig (constantProbeGateArgument θ b w v j τ) := by
  funext τ
  rw [constantProbeGate, constantProbeGateArgument]
  rfl

/-- The first concrete preactivation is the affine function
`τ ↦ λ₁ τ + b`. -/
theorem constantProbeGateArgument_zero {d : Nat} (θ : LayerStream d) (b : ℝ)
    (w v : Fin d -> ℝ) :
    constantProbeGateArgument θ b w v 0 =
      fun τ : ℂ => (constantProbeFirstSlope θ w v : ℂ) * τ + (b : ℂ) := by
  funext τ
  simp [constantProbeGateArgument, constantProbeFirstSlope, formalPhi_zero,
    matC, vecC, Matrix.mulVec, dotProduct]
  ring

/-- On a real probe parameter, the first concrete gate agrees with the public
single-layer real sigmoid gate. -/
theorem constantProbeGate_zero_paramStream_eq_sig {L d : Nat}
    (r : Nat) (θ : Params L d) (w v : Fin d -> ℝ) (τ : ℝ) :
    constantProbeGate (paramStream θ) (Real.log r) w v 0 (τ : ℂ) =
      ((sig (τ * firstSlope θ w v + Real.log r) : ℝ) : ℂ) := by
  rw [constantProbeGate_eq_csig, constantProbeGateArgument_zero]
  have harg :
      (constantProbeFirstSlope (paramStream θ) w v : ℂ) * (τ : ℂ) + (Real.log r : ℂ) =
        ((τ * firstSlope θ w v + Real.log r : ℝ) : ℂ) := by
    rw [constantProbeFirstSlope_paramStream_eq_firstSlope]
    push_cast
    ring
  change csig
      ((constantProbeFirstSlope (paramStream θ) w v : ℂ) * (τ : ℂ) + (Real.log r : ℂ)) =
    ((sig (τ * firstSlope θ w v + Real.log r) : ℝ) : ℂ)
  rw [harg, csig_ofReal]

/-- On real probe parameters, every concrete preactivation remains on the embedded
real axis.  The proof is the recursive formal-stream real-valuedness argument:
earlier real gates make the formal slope real, and `τ * φ + b` is then real. -/
theorem constantProbeGateArgument_isComplexReal_of_real {d : Nat}
    (θ : LayerStream d) (b : ℝ) (w v : Fin d -> ℝ) (x : ℝ) :
    ∀ j, IsComplexReal (constantProbeGateArgument θ b w v j (x : ℂ)) := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
      have hprefix :
          ∀ i, i < j ->
            IsComplexReal (constantProbeGatePrefix θ b w v j (x : ℂ) i) := by
        intro i hi
        have hgatei :
            IsComplexReal (constantProbeGate θ b w v i (x : ℂ)) := by
          rw [constantProbeGate_eq_csig θ b w v i]
          change IsComplexReal
            (csig (constantProbeGateArgument θ b w v i (x : ℂ)))
          rcases ih i hi with ⟨a, ha⟩
          rw [ha]
          simpa [csig_ofReal] using IsComplexReal.ofReal (sig a)
        simpa [constantProbeGatePrefix, hi] using hgatei
      have hphi :
          IsComplexReal
            (formalPhi θ j (constantProbeGatePrefix θ b w v j (x : ℂ)) w v) :=
        formalPhi_isComplexReal_of_gatePrefix θ j
          (constantProbeGatePrefix θ b w v j (x : ℂ)) w v hprefix
      have hx : IsComplexReal (x : ℂ) := IsComplexReal.ofReal x
      have hb : IsComplexReal (b : ℂ) := IsComplexReal.ofReal b
      simpa [constantProbeGateArgument] using (hx.mul hphi).add hb

/-- Concrete stratum definition: new points where the `j`-th preactivation hits `Π`,
after removing all previous strata. -/
noncomputable def constantProbeStratum {d : Nat} (θ : LayerStream d) (b : ℝ)
    (w v : Fin d -> ℝ) (j : Nat) : Set ℂ :=
  {τ |
    τ ∉ partialUnion
      (fun i => if _h : i < j then constantProbeStratum θ b w v i else ∅) j
      ∧ constantProbeGateArgument θ b w v j τ ∈ oddPiI}
termination_by j
decreasing_by exact _h

/-- Unfolded membership in the recursively defined concrete constant-probe stratum. -/
theorem constantProbeStratum_mem_iff {d : Nat} (θ : LayerStream d) (b : ℝ)
    (w v : Fin d -> ℝ) {j : Nat} {τ : ℂ} :
    τ ∈ constantProbeStratum θ b w v j ↔
      τ ∉ partialUnion
        (fun i => if _h : i < j then constantProbeStratum θ b w v i else ∅) j
        ∧ constantProbeGateArgument θ b w v j τ ∈ oddPiI := by
  rw [constantProbeStratum.eq_def]
  rfl

/-- A point in the recursively defined stratum avoids the earlier truncated union. -/
theorem constantProbeStratum_notMem_truncated_previous {d : Nat}
    (θ : LayerStream d) (b : ℝ) (w v : Fin d -> ℝ) {j : Nat} {τ : ℂ}
    (hτ : τ ∈ constantProbeStratum θ b w v j) :
    τ ∉ partialUnion
      (fun i => if _h : i < j then constantProbeStratum θ b w v i else ∅) j :=
  (constantProbeStratum_mem_iff θ b w v).mp hτ |>.1

/-- The concrete stratum definition directly supplies the pole-value condition. -/
theorem constantProbeStratum_pole_value {d : Nat} (θ : LayerStream d) (b : ℝ)
    (w v : Fin d -> ℝ) {j : Nat} {τ : ℂ}
    (hτ : τ ∈ constantProbeStratum θ b w v j) :
    constantProbeGateArgument θ b w v j τ ∈ oddPiI :=
  (constantProbeStratum_mem_iff θ b w v).mp hτ |>.2

/-- Every concrete stratum is contained in the zero set of its sigmoid denominator. -/
theorem constantProbeStratum_subset_denom_zero {d : Nat}
    (θ : LayerStream d) (b : ℝ) (w v : Fin d -> ℝ) (j : Nat) :
    constantProbeStratum θ b w v j ⊆
      {τ | constantProbeDenom θ b w v j τ = 0} := by
  intro τ hτ
  have hpole : constantProbeGateArgument θ b w v j τ ∈ oddPiI :=
    constantProbeStratum_pole_value θ b w v hτ
  simpa [constantProbeDenom] using
    (one_add_exp_neg_eq_zero_iff
      (constantProbeGateArgument θ b w v j τ)).2 hpole

/-- No concrete constant-probe stratum meets the real axis. -/
theorem constantProbeStratum_avoids_real {d : Nat}
    (θ : LayerStream d) (b : ℝ) (w v : Fin d -> ℝ) (j : Nat) (x : ℝ) :
    (x : ℂ) ∉ constantProbeStratum θ b w v j := by
  intro hx
  have hpole : constantProbeGateArgument θ b w v j (x : ℂ) ∈ oddPiI :=
    constantProbeStratum_pole_value θ b w v hx
  rcases constantProbeGateArgument_isComplexReal_of_real θ b w v x j with ⟨a, ha⟩
  rw [ha] at hpole
  exact ofReal_not_mem_oddPiI a hpole

/-- The concrete `j`-th stratum is contained in the regular domain before that stratum. -/
theorem constantProbeStratum_regular {d : Nat} (θ : LayerStream d) (b : ℝ)
    (w v : Fin d -> ℝ) (j : Nat) :
    constantProbeStratum θ b w v j ⊆
      (partialUnion (constantProbeStratum θ b w v) j)ᶜ := by
  intro τ hτ hprev
  exact constantProbeStratum_notMem_truncated_previous θ b w v hτ (by
    rcases hprev with ⟨i, hi, hτi⟩
    exact ⟨i, hi, by simpa [hi] using hτi⟩)

/-- A concrete stratum is countable once it has no accumulation points in the previous
regular domain.  Regularity is supplied by the recursive stratum definition. -/
theorem constantProbeStratum_countable_of_noAccumIn {d : Nat}
    (θ : LayerStream d) (b : ℝ) (w v : Fin d -> ℝ) (j : Nat)
    (hno :
      NoAccumIn
        (constantProbeStratum θ b w v j)
        (partialUnion (constantProbeStratum θ b w v) j)ᶜ) :
    (constantProbeStratum θ b w v j).Countable :=
  countable_of_subset_noAccumIn
    (constantProbeStratum_regular θ b w v j) hno

/-- Analyticity of a concrete preactivation on a domain implies analyticity of the
corresponding sigmoid denominator on that domain. -/
theorem constantProbeDenom_analyticOnNhd_of_H_analyticOnNhd {d : Nat}
    (θ : LayerStream d) (b : ℝ) (w v : Fin d -> ℝ) (j : Nat) {U : Set ℂ}
    (hH : AnalyticOnNhd ℂ (constantProbeGateArgument θ b w v j) U) :
    AnalyticOnNhd ℂ (constantProbeDenom θ b w v j) U := by
  intro τ hτ
  exact analyticAt_const.add ((hH τ hτ).neg.cexp')

/-- A concrete stratum has no accumulation in its regular domain once its sigmoid
denominator is analytic there and does not vanish identically near any regular zero. -/
theorem constantProbeStratum_noAccumIn_of_denom_analyticOnNhd_of_not_eventually_zero
    {d : Nat} (θ : LayerStream d) (b : ℝ) (w v : Fin d -> ℝ) (j : Nat)
    (hD :
      AnalyticOnNhd ℂ (constantProbeDenom θ b w v j)
        (partialUnion (constantProbeStratum θ b w v) j)ᶜ)
    (hnot :
      ∀ τ, τ ∉ partialUnion (constantProbeStratum θ b w v) j ->
        constantProbeDenom θ b w v j τ = 0 ->
          ¬ (∀ᶠ z in nhds τ, constantProbeDenom θ b w v j z = 0)) :
    NoAccumIn
      (constantProbeStratum θ b w v j)
      (partialUnion (constantProbeStratum θ b w v) j)ᶜ :=
  noAccumIn_of_subset_zeroSet_of_analyticOnNhd_of_not_eventually_zero
    (constantProbeStratum_subset_denom_zero θ b w v j) hD
    (fun τ hτ => hnot τ hτ)

/-- Version of
`constantProbeStratum_noAccumIn_of_denom_analyticOnNhd_of_not_eventually_zero`
where denominator analyticity is derived from preactivation analyticity. -/
theorem constantProbeStratum_noAccumIn_of_H_analyticOnNhd_of_denom_not_eventually_zero
    {d : Nat} (θ : LayerStream d) (b : ℝ) (w v : Fin d -> ℝ) (j : Nat)
    (hH :
      AnalyticOnNhd ℂ (constantProbeGateArgument θ b w v j)
        (partialUnion (constantProbeStratum θ b w v) j)ᶜ)
    (hnot :
      ∀ τ, τ ∉ partialUnion (constantProbeStratum θ b w v) j ->
        constantProbeDenom θ b w v j τ = 0 ->
          ¬ (∀ᶠ z in nhds τ, constantProbeDenom θ b w v j z = 0)) :
    NoAccumIn
      (constantProbeStratum θ b w v j)
      (partialUnion (constantProbeStratum θ b w v) j)ᶜ :=
  constantProbeStratum_noAccumIn_of_denom_analyticOnNhd_of_not_eventually_zero
    θ b w v j
    (constantProbeDenom_analyticOnNhd_of_H_analyticOnNhd θ b w v j hH)
    hnot

/-- If the current preactivation is analytic on the regular domain before stratum `j`,
and that regular domain is the complement of a countable set avoiding the real axis, then
the concrete sigmoid denominator is not locally identically zero at any regular point.

The proof uses the countable-complement identity theorem: local denominator collapse would
force the denominator to vanish on the whole regular domain, including real probe
parameters.  But the concrete preactivation is real-valued on real probes, while sigmoid
poles are never real. -/
theorem constantProbeDenom_not_eventually_zero_of_H_analyticOnNhd_of_partialUnion_facts
    {d : Nat} (θ : LayerStream d) (b : ℝ) (w v : Fin d -> ℝ) (j : Nat)
    (hH :
      AnalyticOnNhd ℂ (constantProbeGateArgument θ b w v j)
        (partialUnion (constantProbeStratum θ b w v) j)ᶜ)
    (hpartialUnion_countable :
      (partialUnion (constantProbeStratum θ b w v) j).Countable)
    (hpartialUnion_avoids_real :
      ∀ x : ℝ, (x : ℂ) ∉ partialUnion (constantProbeStratum θ b w v) j)
    {τ : ℂ}
    (hτ : τ ∉ partialUnion (constantProbeStratum θ b w v) j) :
    ¬ (∀ᶠ z in nhds τ, constantProbeDenom θ b w v j z = 0) := by
  intro hzero
  let E : Set ℂ := partialUnion (constantProbeStratum θ b w v) j
  let Dfun : ℂ -> ℂ := constantProbeDenom θ b w v j
  have hDanalytic : AnalyticOnNhd ℂ Dfun Eᶜ := by
    dsimp [Dfun, E]
    exact constantProbeDenom_analyticOnNhd_of_H_analyticOnNhd θ b w v j hH
  have hZeroAnalytic : AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) Eᶜ := by
    intro z _hz
    exact analyticAt_const
  have hfreq :
      ∃ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ),
        Dfun z = (fun _ : ℂ => (0 : ℂ)) z := by
    have hzeroWithin :
        ∀ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ),
          Dfun z = (fun _ : ℂ => (0 : ℂ)) z := by
      simpa [Dfun] using (nhdsWithin_le_nhds hzero)
    exact Filter.Eventually.frequently hzeroWithin
  have hEqOn :
      Set.EqOn Dfun (fun _ : ℂ => (0 : ℂ)) Eᶜ :=
    analytic_eqOn_countable_compl_of_frequentlyEq
      (E := E) (F := Dfun) (G := fun _ : ℂ => (0 : ℂ)) (z0 := τ)
      (by simpa [E] using hpartialUnion_countable) hDanalytic hZeroAnalytic
      (by simpa [E] using hτ) hfreq
  have h0reg : ((0 : ℝ) : ℂ) ∈ Eᶜ := by
    simpa [E] using hpartialUnion_avoids_real 0
  have hD0 : Dfun ((0 : ℝ) : ℂ) = 0 := by
    simpa using hEqOn h0reg
  have hpole :
      constantProbeGateArgument θ b w v j ((0 : ℝ) : ℂ) ∈ oddPiI := by
    rw [← one_add_exp_neg_eq_zero_iff]
    simpa [Dfun, constantProbeDenom] using hD0
  rcases constantProbeGateArgument_isComplexReal_of_real θ b w v 0 j with ⟨a, ha⟩
  rw [ha] at hpole
  exact ofReal_not_mem_oddPiI a hpole

/-- The truncated previous-union appearing in the recursive definition agrees with the
ordinary previous partial union on membership. -/
theorem constantProbe_notMem_truncated_previous_of_notMem_partialUnion {d : Nat}
    (θ : LayerStream d) (b : ℝ) (w v : Fin d -> ℝ) {j : Nat} {τ : ℂ}
    (hτ : τ ∉ partialUnion (constantProbeStratum θ b w v) j) :
    τ ∉ partialUnion
      (fun i => if _h : i < j then constantProbeStratum θ b w v i else ∅) j := by
  intro hprev
  rcases hprev with ⟨i, hi, hτi⟩
  exact hτ ⟨i, hi, by simpa [hi] using hτi⟩

/-- If a point avoids all previous concrete strata and its current preactivation hits
`Π`, then it belongs to the current recursively defined stratum. -/
theorem constantProbeStratum_mem_of_notMem_previous_and_pole {d : Nat}
    (θ : LayerStream d) (b : ℝ) (w v : Fin d -> ℝ) {j : Nat} {τ : ℂ}
    (hprev : τ ∉ partialUnion (constantProbeStratum θ b w v) j)
    (hpole : constantProbeGateArgument θ b w v j τ ∈ oddPiI) :
    τ ∈ constantProbeStratum θ b w v j := by
  rw [constantProbeStratum_mem_iff]
  exact ⟨constantProbe_notMem_truncated_previous_of_notMem_partialUnion
    θ b w v hprev, hpole⟩

/-- Analyticity is preserved by evaluating a finite gate polynomial at analytic gate
families. -/
theorem gatePolynomial_eval_analyticOnNhd {K : Nat} (p : GatePoly K)
    {U : Set ℂ} {g : Fin K -> ℂ -> ℂ}
    (hg : ∀ i, AnalyticOnNhd ℂ (g i) U) :
    AnalyticOnNhd ℂ (fun τ => MvPolynomial.eval (fun i => g i τ) p) U := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      simpa using (analyticOnNhd_const (𝕜 := ℂ) (v := a) (s := U))
  | add _p _q hp hq =>
      simpa using hp.add hq
  | mul_X _p i hp =>
      simpa using hp.mul (hg i)

private theorem partialUnion_subset_of_le {S : Nat -> Set ℂ} {i j : Nat} (hij : i ≤ j) :
    partialUnion S i ⊆ partialUnion S j := by
  intro τ hτ
  rcases hτ with ⟨k, hk, hτk⟩
  exact ⟨k, Nat.lt_of_lt_of_le hk hij, hτk⟩

/-- If a lower preactivation is analytic on its own regular domain, the corresponding
gate is analytic on any later regular domain. -/
theorem constantProbeGate_analyticOn_later_omega_of_H {d : Nat}
    (θ : LayerStream d) (b : ℝ) (w v : Fin d -> ℝ) {i j : Nat}
    (hij : i < j)
    (hH :
      AnalyticOnNhd ℂ (constantProbeGateArgument θ b w v i)
        (partialUnion (constantProbeStratum θ b w v) i)ᶜ) :
    AnalyticOnNhd ℂ (constantProbeGate θ b w v i)
      (partialUnion (constantProbeStratum θ b w v) j)ᶜ := by
  rw [constantProbeGate_eq_csig θ b w v i]
  intro τ hτ
  have hτi : τ ∈ (partialUnion (constantProbeStratum θ b w v) i)ᶜ := by
    intro hprev
    exact hτ (partialUnion_subset_of_le (S := constantProbeStratum θ b w v)
      (Nat.le_of_lt hij) hprev)
  have hden :
      1 + Complex.exp (-(constantProbeGateArgument θ b w v i τ)) ≠ 0 := by
    intro hzero
    have hpole : constantProbeGateArgument θ b w v i τ ∈ oddPiI :=
      (one_add_exp_neg_eq_zero_iff
        (constantProbeGateArgument θ b w v i τ)).mp hzero
    have hstratum :
        τ ∈ constantProbeStratum θ b w v i :=
      constantProbeStratum_mem_of_notMem_previous_and_pole θ b w v hτi hpole
    exact hτ ⟨i, hij, hstratum⟩
  exact AnalyticAt.comp_of_eq' (csig_analyticAt hden) (hH τ hτi) rfl

/-- Every concrete constant-probe preactivation is analytic on its previous regular
domain. -/
theorem constantProbeGateArgument_analyticOn_omega {d : Nat}
    (θ : LayerStream d) (b : ℝ) (w v : Fin d -> ℝ) :
    ∀ j : Nat,
      AnalyticOnNhd ℂ (constantProbeGateArgument θ b w v j)
        (partialUnion (constantProbeStratum θ b w v) j)ᶜ := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
      let U : Set ℂ := (partialUnion (constantProbeStratum θ b w v) j)ᶜ
      have hgate :
          ∀ i : Fin j, AnalyticOnNhd ℂ (constantProbeGate θ b w v (i : Nat)) U := by
        intro i
        exact constantProbeGate_analyticOn_later_omega_of_H θ b w v i.isLt
          (ih i i.isLt)
      have hphiEval :
          AnalyticOnNhd ℂ
            (fun τ => MvPolynomial.eval
              (fun i : Fin j => constantProbeGate θ b w v (i : Nat) τ)
              (formalPhiPoly θ j w v)) U :=
        gatePolynomial_eval_analyticOnNhd (formalPhiPoly θ j w v) hgate
      have hphiEq :
          (fun τ => MvPolynomial.eval
            (fun i : Fin j => constantProbeGate θ b w v (i : Nat) τ)
            (formalPhiPoly θ j w v)) =
          fun τ => formalPhi θ j (constantProbeGatePrefix θ b w v j τ) w v := by
        funext τ
        rw [eval_formalPhiPoly]
        apply congrArg (fun z => formalPhi θ j z w v)
        funext k
        by_cases hk : k < j
        · simp [extendGate, constantProbeGatePrefix, hk]
        · simp [extendGate, constantProbeGatePrefix, hk]
      have hphi :
          AnalyticOnNhd ℂ
            (fun τ => formalPhi θ j (constantProbeGatePrefix θ b w v j τ) w v) U := by
        simpa [hphiEq] using hphiEval
      intro τ hτ
      exact (analyticAt_id.mul (hphi τ hτ)).add analyticAt_const

/-- Earlier concrete gates are analytic on later regular domains. -/
theorem constantProbeGate_analyticOn_later_omega {d : Nat}
    (θ : LayerStream d) (b : ℝ) (w v : Fin d -> ℝ) {i j : Nat}
    (hij : i < j) :
    AnalyticOnNhd ℂ (constantProbeGate θ b w v i)
      (partialUnion (constantProbeStratum θ b w v) j)ᶜ :=
  constantProbeGate_analyticOn_later_omega_of_H θ b w v hij
    (constantProbeGateArgument_analyticOn_omega θ b w v i)

/-- Once a concrete stratum system is known to be isolated in the abstract
`StrataSystem` sense, the sigmoid denominator for the current gate is nonzero on
punctured neighborhoods of every point of that stratum. -/
theorem constantProbe_denom_eventually_ne_zero_of_strata {d : Nat}
    (θ : LayerStream d) (b : ℝ) (w v : Fin d -> ℝ) {m j : Nat}
    (hstrata : StrataSystem (constantProbeStratum θ b w v) m)
    (hj : j < m) {τ : ℂ} (hτ : τ ∈ constantProbeStratum θ b w v j) :
    ∀ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ),
      1 + Complex.exp (-(constantProbeGateArgument θ b w v j z)) ≠ 0 := by
  have hIso :
      IsPuncturedIsolated
        (partialUnion (constantProbeStratum θ b w v) (j + 1)) τ :=
    strata_punctured_isolated_partialUnion_succ
      (hstrata.restrict (Nat.succ_le_of_lt hj)) hτ
      (constantProbeStratum_regular θ b w v j hτ)
  have hevent :
      ∀ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ),
        z ∈ (partialUnion (constantProbeStratum θ b w v) (j + 1))ᶜ := by
    simpa [IsPuncturedIsolated] using hIso
  filter_upwards [hevent] with z hzreg hden
  have hpole : constantProbeGateArgument θ b w v j z ∈ oddPiI :=
    (one_add_exp_neg_eq_zero_iff
      (constantProbeGateArgument θ b w v j z)).mp hden
  have hprev : z ∉ partialUnion (constantProbeStratum θ b w v) j := by
    intro hzprev
    rcases hzprev with ⟨i, hi, hzi⟩
    exact hzreg ⟨i, Nat.lt_trans hi (Nat.lt_succ_self j), hzi⟩
  have hzj : z ∈ constantProbeStratum θ b w v j :=
    constantProbeStratum_mem_of_notMem_previous_and_pole θ b w v hprev hpole
  exact hzreg ⟨j, Nat.lt_succ_self j, hzj⟩

/-- The first concrete stratum is exactly the affine-`Π` stratum. -/
theorem constantProbeStratum_zero_eq_affineOddPiIStratum {d : Nat}
    (θ : LayerStream d) (b : ℝ) (w v : Fin d -> ℝ) :
    constantProbeStratum θ b w v 0 =
      affineOddPiIStratum b (constantProbeFirstSlope θ w v) := by
  ext τ
  simp [constantProbeStratum, partialUnion, affineOddPiIStratum,
    constantProbeGateArgument_zero θ b w v]

/-- The concrete first stratum satisfies the downstream first-stratum formula. -/
theorem constantProbeFirstStratumFormula {d : Nat} (θ : LayerStream d) (b : ℝ)
    (w v : Fin d -> ℝ) :
    FirstStratumFormula (constantProbeStratum θ b w v 0) b
      (constantProbeFirstSlope θ w v) :=
  FirstStratumFormula.of_eq_affineOddPiIStratum
    (constantProbeStratum_zero_eq_affineOddPiIStratum θ b w v)

/-- A formal factor only depends on its matching gate coordinate. -/
theorem formalFactor_congr_of_eq {d : Nat} (θ : LayerStream d)
    {z z' : Nat -> ℂ} {j : Nat} (hz : z j = z' j) :
    formalFactor θ z j = formalFactor θ z' j := by
  simp [formalFactor, hz]

/-- The formal weight matrix at depth `n` only depends on gate coordinates `< n`. -/
theorem formalW_congr_of_eqOn_lt {d : Nat} (θ : LayerStream d) {n : Nat}
    {z z' : Nat -> ℂ} (hz : ∀ i, i < n -> z i = z' i) :
    formalW θ n z = formalW θ n z' := by
  revert z z'
  induction n with
  | zero =>
      intro z z' _hz
      rfl
  | succ n ih =>
      intro z z' hz
      rw [formalW_succ, formalW_succ]
      rw [formalFactor_congr_of_eq θ (hz n (Nat.lt_succ_self n))]
      rw [ih (fun i hi => hz i (Nat.lt_trans hi (Nat.lt_succ_self n)))]

/-- The formal weight vector at depth `n` only depends on gate coordinates `< n`. -/
theorem formalWVec_congr_of_eqOn_lt {d : Nat} (θ : LayerStream d) {n : Nat}
    {z z' : Nat -> ℂ} (w : Fin d -> ℝ)
    (hz : ∀ i, i < n -> z i = z' i) :
    formalWVec θ n z w = formalWVec θ n z' w := by
  rw [formalWVec, formalWVec, formalW_congr_of_eqOn_lt θ hz]

/-- The formal value vector at depth `n` only depends on gate coordinates `< n`. -/
theorem formalVVec_congr_of_eqOn_lt {d : Nat} (θ : LayerStream d) {n : Nat}
    {z z' : Nat -> ℂ} (w v : Fin d -> ℝ)
    (hz : ∀ i, i < n -> z i = z' i) :
    formalVVec θ n z w v = formalVVec θ n z' w v := by
  revert z z'
  induction n with
  | zero =>
      intro z z' _hz
      rfl
  | succ n ih =>
      intro z z' hz
      rw [formalVVec_succ, formalVVec_succ]
      rw [ih (fun i hi => hz i (Nat.lt_trans hi (Nat.lt_succ_self n)))]
      rw [formalWVec_congr_of_eqOn_lt θ w
        (fun i hi => hz i (Nat.lt_trans hi (Nat.lt_succ_self n)))]
      rw [hz n (Nat.lt_succ_self n)]

/-- The visible vector at depth `n` only depends on gate coordinates `< n`. -/
theorem formalVisible_congr_of_eqOn_lt {d : Nat} (θ : LayerStream d) {n : Nat}
    {z z' : Nat -> ℂ} (w : Fin d -> ℝ)
    (hz : ∀ i, i < n -> z i = z' i) :
    formalVisible θ n z w = formalVisible θ n z' w := by
  rw [formalVisible, formalVisible, formalWVec_congr_of_eqOn_lt θ w hz]

/-- Concrete gate assignment for the full formal observable. -/
noncomputable def constantProbeGateStream {d : Nat} (θ : LayerStream d) (b : ℝ)
    (w v : Fin d -> ℝ) (τ : ℂ) : Nat -> ℂ :=
  fun j => constantProbeGate θ b w v j τ

/-- Selected complexified constant-probe observable at depth `m`. -/
noncomputable def constantProbeObservable {d : Nat} (θ : LayerStream d) (b : ℝ)
    (w v : Fin d -> ℝ) (m : Nat) (iota : Fin d) : ℂ -> ℂ :=
  fun τ => formalVVec θ m (constantProbeGateStream θ b w v τ) w v iota

/-- Lower contribution in the final one-step observable recurrence. -/
noncomputable def constantProbeLastLower {d : Nat} (θ : LayerStream d) (b : ℝ)
    (w v : Fin d -> ℝ) (m : Nat) (iota : Fin d) : ℂ -> ℂ :=
  fun τ =>
    (matC (skipB (θ m).1) *ᵥ
      formalVVec θ m (constantProbeGateStream θ b w v τ) w v) iota

/-- Visible coefficient multiplying the final gate in the one-step recurrence. -/
noncomputable def constantProbeLastCoeff {d : Nat} (θ : LayerStream d) (b : ℝ)
    (w v : Fin d -> ℝ) (m : Nat) (iota : Fin d) : ℂ -> ℂ :=
  fun τ => formalVisibleCoord θ m (constantProbeGateStream θ b w v τ) w iota

@[simp]
theorem constantProbeObservable_zero {d : Nat} (θ : LayerStream d) (b : ℝ)
    (w v : Fin d -> ℝ) (iota : Fin d) :
    constantProbeObservable θ b w v 0 iota = fun _ : ℂ => (v iota : ℂ) := by
  funext τ
  simp [constantProbeObservable, vecC]

/-- Depth-zero observable bridge to the public real recursion. -/
theorem constantProbeObservable_paramStream_zero_eq_Frec {d : Nat}
    (r : Nat) (θ : Params 0 d) (w v : Fin d -> ℝ) (iota : Fin d) (τ : ℝ) :
    constantProbeObservable (paramStream θ) (Real.log r) w v 0 iota (τ : ℂ) =
      (Frec r θ w v τ iota : ℂ) := by
  simp [constantProbeObservable_zero (paramStream θ) (Real.log r) w v iota, Frec]

/-- The formal `w` vector after one head layer is the head-updated real probe vector
when the head gate is real. -/
theorem formalWVec_one_eq_vecC_headUpdate {d : Nat} (θ : LayerStream d)
    (z : Nat -> ℂ) (w : Fin d -> ℝ) (s : ℝ) (hz : z 0 = (s : ℂ)) :
    formalWVec θ 1 z w =
      vecC (w + (θ 0).1.mulVec w - s • (θ 0).1.mulVec w) := by
  ext i
  have hone :
      (∑ x : Fin d, ((1 : Matrix (Fin d) (Fin d) ℝ) i x : ℂ) * (w x : ℂ)) =
        (w i : ℂ) := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _hj hji
      have hzero : (1 : Matrix (Fin d) (Fin d) ℝ) i j = 0 :=
        Matrix.one_apply_ne hji.symm
      simp [hzero]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  simp [formalWVec, formalW, formalFactor, skipB, matC, vecC, Matrix.mulVec,
    dotProduct, hz]
  have hsplit :
      (∑ x : Fin d,
        (((1 : Matrix (Fin d) (Fin d) ℝ) i x : ℂ) + ((θ 0).1 i x : ℂ)
            - (s : ℂ) * ((θ 0).1 i x : ℂ)) * (w x : ℂ)) =
        (∑ x : Fin d, ((1 : Matrix (Fin d) (Fin d) ℝ) i x : ℂ) * (w x : ℂ))
          + (∑ x : Fin d, ((θ 0).1 i x : ℂ) * (w x : ℂ))
          - (s : ℂ) * (∑ x : Fin d, ((θ 0).1 i x : ℂ) * (w x : ℂ)) := by
    calc
      (∑ x : Fin d,
        (((1 : Matrix (Fin d) (Fin d) ℝ) i x : ℂ) + ((θ 0).1 i x : ℂ)
            - (s : ℂ) * ((θ 0).1 i x : ℂ)) * (w x : ℂ))
          = ∑ x : Fin d,
              (((1 : Matrix (Fin d) (Fin d) ℝ) i x : ℂ) * (w x : ℂ)
                + (((θ 0).1 i x : ℂ) * (w x : ℂ)
                  - (s : ℂ) * (((θ 0).1 i x : ℂ) * (w x : ℂ)))) := by
            refine Finset.sum_congr rfl ?_
            intro x _hx
            ring
      _ = (∑ x : Fin d, ((1 : Matrix (Fin d) (Fin d) ℝ) i x : ℂ) * (w x : ℂ))
          + (∑ x : Fin d, ((θ 0).1 i x : ℂ) * (w x : ℂ))
          - (s : ℂ) * (∑ x : Fin d, ((θ 0).1 i x : ℂ) * (w x : ℂ)) := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
            ring
  rw [hsplit, hone]

/-- The formal `v` vector after one head layer is the head-updated real probe vector
when the head gate is real. -/
theorem formalVVec_one_eq_vecC_headUpdate {d : Nat} (θ : LayerStream d)
    (z : Nat -> ℂ) (w v : Fin d -> ℝ) (s : ℝ) (hz : z 0 = (s : ℂ)) :
    formalVVec θ 1 z w v =
      vecC (v + (θ 0).1.mulVec v + s • (θ 0).1.mulVec w) := by
  ext i
  have hone :
      (∑ x : Fin d, ((1 : Matrix (Fin d) (Fin d) ℝ) i x : ℂ) * (v x : ℂ)) =
        (v i : ℂ) := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _hj hji
      have hzero : (1 : Matrix (Fin d) (Fin d) ℝ) i j = 0 :=
        Matrix.one_apply_ne hji.symm
      simp [hzero]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  simp [formalVVec, formalWVec, formalW, skipB, matC, vecC, Matrix.mulVec,
    dotProduct, hz]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, hone]

/-- Shift the formal `w` vector past a peeled head layer. -/
theorem formalWVec_tail_succ_of_head {d : Nat} (θ : LayerStream d)
    (z : Nat -> ℂ) (w w₁ : Fin d -> ℝ) (n : Nat)
    (hhead : formalWVec θ 1 z w = vecC w₁) :
    formalWVec θ (n + 1) z w =
      formalWVec (fun k => θ (k + 1)) n (fun k => z (k + 1)) w₁ := by
  induction n with
  | zero =>
      simpa using hhead
  | succ n ih =>
      rw [formalWVec_succ θ (n + 1) z w,
        formalWVec_succ (fun k => θ (k + 1)) n (fun k => z (k + 1)) w₁]
      have hfactor :
          formalFactor θ z (n + 1) =
            formalFactor (fun k => θ (k + 1)) (fun k => z (k + 1)) n := by
        ext i j
        simp [formalFactor]
      rw [hfactor, ih]

/-- Shift the formal `v` vector past a peeled head layer. -/
theorem formalVVec_tail_succ_of_head {d : Nat} (θ : LayerStream d)
    (z : Nat -> ℂ) (w v w₁ v₁ : Fin d -> ℝ) (n : Nat)
    (hWhead : formalWVec θ 1 z w = vecC w₁)
    (hVhead : formalVVec θ 1 z w v = vecC v₁) :
    formalVVec θ (n + 1) z w v =
      formalVVec (fun k => θ (k + 1)) n (fun k => z (k + 1)) w₁ v₁ := by
  induction n with
  | zero =>
      simpa using hVhead
  | succ n ih =>
      rw [formalVVec_succ θ (n + 1) z w v,
        formalVVec_succ (fun k => θ (k + 1)) n (fun k => z (k + 1)) w₁ v₁]
      have hWshift :
          formalWVec θ (n + 1) z w =
            formalWVec (fun k => θ (k + 1)) n (fun k => z (k + 1)) w₁ :=
        formalWVec_tail_succ_of_head θ z w w₁ n hWhead
      rw [ih, hWshift]

/-- Shift the formal preactivation past a peeled head layer. -/
theorem formalPhi_tail_succ_of_head {d : Nat} (θ : LayerStream d)
    (z : Nat -> ℂ) (w v w₁ v₁ : Fin d -> ℝ) (n : Nat)
    (hWhead : formalWVec θ 1 z w = vecC w₁)
    (hVhead : formalVVec θ 1 z w v = vecC v₁) :
    formalPhi θ (n + 1) z w v =
      formalPhi (fun k => θ (k + 1)) n (fun k => z (k + 1)) w₁ v₁ := by
  rw [formalPhi, formalPhi]
  rw [formalWVec_tail_succ_of_head θ z w w₁ n hWhead,
    formalVVec_tail_succ_of_head θ z w v w₁ v₁ n hWhead hVhead]

/-- The formal preactivation only depends on gate coordinates below its depth. -/
theorem formalPhi_congr_of_eqOn_lt {d : Nat} (θ : LayerStream d) {n : Nat}
    {z z' : Nat -> ℂ} (w v : Fin d -> ℝ)
    (hz : ∀ i, i < n -> z i = z' i) :
    formalPhi θ n z w v = formalPhi θ n z' w v := by
  rw [formalPhi, formalPhi]
  rw [formalWVec_congr_of_eqOn_lt θ w hz,
    formalVVec_congr_of_eqOn_lt θ w v hz]

/-- Finite parameter streams commute with taking a bounded tail. -/
theorem paramStream_tail_apply {m d : Nat} (θ : Params (m + 1) d)
    {j : Nat} (hj : j < m) :
    paramStream (Fin.tail θ) j = paramStream θ (j + 1) := by
  simp [paramStream, hj, Nat.succ_lt_succ hj, Fin.tail]

/-- Finite parameter streams commute with taking the padded tail. -/
theorem paramStream_tail_eq_shift {m d : Nat} (θ : Params (m + 1) d) :
    paramStream (Fin.tail θ) = fun j => paramStream θ (j + 1) := by
  funext j
  by_cases hj : j < m
  · exact paramStream_tail_apply θ hj
  · have hjs : ¬ j + 1 < m + 1 := by omega
    simp [paramStream, hj, hjs]

/-- After peeling the real first gate, later concrete gates agree with the gates of the
tail parameter stream at the updated probe vectors. -/
theorem constantProbeGate_paramStream_tail_shift {m d : Nat} (r : Nat)
    (θ : Params (m + 1) d) (w v : Fin d -> ℝ) (τ : ℝ) :
    let s : ℝ := sig (τ * (w ⬝ᵥ (θ 0).2.mulVec v) + Real.log r)
    let w₁ : Fin d -> ℝ :=
      w + (θ 0).1.mulVec w - s • (θ 0).1.mulVec w
    let v₁ : Fin d -> ℝ :=
      v + (θ 0).1.mulVec v + s • (θ 0).1.mulVec w
    ∀ j, j < m ->
      constantProbeGate (paramStream θ) (Real.log r) w v (j + 1) (τ : ℂ) =
        constantProbeGate (paramStream (Fin.tail θ)) (Real.log r) w₁ v₁ j (τ : ℂ) := by
  let s : ℝ := sig (τ * (w ⬝ᵥ (θ 0).2.mulVec v) + Real.log r)
  let w₁ : Fin d -> ℝ := w + (θ 0).1.mulVec w - s • (θ 0).1.mulVec w
  let v₁ : Fin d -> ℝ := v + (θ 0).1.mulVec v + s • (θ 0).1.mulVec w
  have hgate0 :
      constantProbeGate (paramStream θ) (Real.log r) w v 0 (τ : ℂ) = (s : ℂ) := by
    dsimp [s]
    rw [constantProbeGate_zero_paramStream_eq_sig]
    simp [firstSlope, firstAttention, paramStream, matrixBilin]
  dsimp
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
      intro hj
      let z : Nat -> ℂ :=
        constantProbeGatePrefix (paramStream θ) (Real.log r) w v (j + 1) (τ : ℂ)
      have hz0 : z 0 = (s : ℂ) := by
        simp [z, constantProbeGatePrefix, hgate0]
      have hWhead :
          formalWVec (paramStream θ) 1 z w = vecC w₁ := by
        dsimp [w₁]
        simpa [paramStream, s, Nat.succ_pos m] using
          formalWVec_one_eq_vecC_headUpdate (paramStream θ) z w s hz0
      have hVhead :
          formalVVec (paramStream θ) 1 z w v = vecC v₁ := by
        dsimp [v₁]
        simpa [paramStream, s, Nat.succ_pos m] using
          formalVVec_one_eq_vecC_headUpdate (paramStream θ) z w v s hz0
      have hprefix :
          ∀ i, i < j ->
            (fun k => z (k + 1)) i =
              constantProbeGatePrefix (paramStream (Fin.tail θ)) (Real.log r)
                w₁ v₁ j (τ : ℂ) i := by
        intro i hi
        have his : i + 1 < j + 1 := Nat.succ_lt_succ hi
        have him : i < m := Nat.lt_trans hi hj
        have hih := ih i hi him
        simp [z, constantProbeGatePrefix, hi, his]
        simpa [w₁, v₁, s] using hih
      have hphi :
          formalPhi (paramStream θ) (j + 1) z w v =
            formalPhi (paramStream (Fin.tail θ)) j
              (constantProbeGatePrefix (paramStream (Fin.tail θ)) (Real.log r)
                w₁ v₁ j (τ : ℂ)) w₁ v₁ := by
        calc
          formalPhi (paramStream θ) (j + 1) z w v =
              formalPhi (fun k => paramStream θ (k + 1)) j
                (fun k => z (k + 1)) w₁ v₁ :=
            formalPhi_tail_succ_of_head (paramStream θ) z w v w₁ v₁ j hWhead hVhead
          _ = formalPhi (paramStream (Fin.tail θ)) j
                (fun k => z (k + 1)) w₁ v₁ := by
            rw [paramStream_tail_eq_shift θ]
          _ = formalPhi (paramStream (Fin.tail θ)) j
                (constantProbeGatePrefix (paramStream (Fin.tail θ)) (Real.log r)
                  w₁ v₁ j (τ : ℂ)) w₁ v₁ :=
            formalPhi_congr_of_eqOn_lt (paramStream (Fin.tail θ)) w₁ v₁ hprefix
      rw [constantProbeGate_eq_csig (paramStream θ) (Real.log r) w v (j + 1),
        constantProbeGate_eq_csig (paramStream (Fin.tail θ)) (Real.log r) w₁ v₁ j]
      simp [constantProbeGateArgument, z, hphi]

/-- One peeled observable step: depth `m + 1` at `(w,v)` equals depth `m` of the
tail parameters at the head-updated probe vectors. -/
theorem constantProbeObservable_paramStream_tail_shift {m d : Nat} (r : Nat)
    (θ : Params (m + 1) d) (w v : Fin d -> ℝ) (iota : Fin d) (τ : ℝ) :
    let s : ℝ := sig (τ * (w ⬝ᵥ (θ 0).2.mulVec v) + Real.log r)
    let w₁ : Fin d -> ℝ :=
      w + (θ 0).1.mulVec w - s • (θ 0).1.mulVec w
    let v₁ : Fin d -> ℝ :=
      v + (θ 0).1.mulVec v + s • (θ 0).1.mulVec w
    constantProbeObservable (paramStream θ) (Real.log r) w v (m + 1) iota (τ : ℂ) =
      constantProbeObservable (paramStream (Fin.tail θ)) (Real.log r)
        w₁ v₁ m iota (τ : ℂ) := by
  let s : ℝ := sig (τ * (w ⬝ᵥ (θ 0).2.mulVec v) + Real.log r)
  let w₁ : Fin d -> ℝ := w + (θ 0).1.mulVec w - s • (θ 0).1.mulVec w
  let v₁ : Fin d -> ℝ := v + (θ 0).1.mulVec v + s • (θ 0).1.mulVec w
  let z : Nat -> ℂ := constantProbeGateStream (paramStream θ) (Real.log r) w v (τ : ℂ)
  have hgate0 :
      constantProbeGate (paramStream θ) (Real.log r) w v 0 (τ : ℂ) = (s : ℂ) := by
    dsimp [s]
    rw [constantProbeGate_zero_paramStream_eq_sig]
    simp [firstSlope, firstAttention, paramStream, matrixBilin]
  have hz0 : z 0 = (s : ℂ) := by
    simp [z, constantProbeGateStream, hgate0]
  have hWhead :
      formalWVec (paramStream θ) 1 z w = vecC w₁ := by
    dsimp [w₁]
    simpa [paramStream, s, Nat.succ_pos m] using
      formalWVec_one_eq_vecC_headUpdate (paramStream θ) z w s hz0
  have hVhead :
      formalVVec (paramStream θ) 1 z w v = vecC v₁ := by
    dsimp [v₁]
    simpa [paramStream, s, Nat.succ_pos m] using
      formalVVec_one_eq_vecC_headUpdate (paramStream θ) z w v s hz0
  have hgateShift :
      ∀ j, j < m ->
        z (j + 1) =
          constantProbeGateStream (paramStream (Fin.tail θ)) (Real.log r)
            w₁ v₁ (τ : ℂ) j := by
    intro j hj
    simpa [z, constantProbeGateStream, w₁, v₁, s] using
      constantProbeGate_paramStream_tail_shift r θ w v τ j hj
  calc
    constantProbeObservable (paramStream θ) (Real.log r) w v (m + 1) iota (τ : ℂ)
        = formalVVec (fun k => paramStream θ (k + 1)) m
            (fun k => z (k + 1)) w₁ v₁ iota := by
          simp [constantProbeObservable, constantProbeGateStream, z,
            formalVVec_tail_succ_of_head (paramStream θ) z w v w₁ v₁ m hWhead hVhead]
    _ = formalVVec (paramStream (Fin.tail θ)) m
            (fun k => z (k + 1)) w₁ v₁ iota := by
          rw [paramStream_tail_eq_shift θ]
    _ = constantProbeObservable (paramStream (Fin.tail θ)) (Real.log r)
            w₁ v₁ m iota (τ : ℂ) := by
          rw [constantProbeObservable]
          rw [formalVVec_congr_of_eqOn_lt (paramStream (Fin.tail θ)) w₁ v₁ hgateShift]

/-- Arbitrary-depth bridge from the concrete constant-probe observable to the public
closed-form recursion. -/
theorem constantProbeObservable_paramStream_eq_Frec {d m : Nat}
    (r : Nat) (θ : Params m d) (w v : Fin d -> ℝ) (iota : Fin d) (τ : ℝ) :
    constantProbeObservable (paramStream θ) (Real.log r) w v m iota (τ : ℂ) =
      (Frec r θ w v τ iota : ℂ) := by
  induction m generalizing w v iota τ with
  | zero =>
      exact constantProbeObservable_paramStream_zero_eq_Frec r θ w v iota τ
  | succ m ih =>
      let s : ℝ := sig (τ * (w ⬝ᵥ (θ 0).2.mulVec v) + Real.log r)
      let w₁ : Fin d -> ℝ := w + (θ 0).1.mulVec w - s • (θ 0).1.mulVec w
      let v₁ : Fin d -> ℝ := v + (θ 0).1.mulVec v + s • (θ 0).1.mulVec w
      have htail :
          constantProbeObservable (paramStream θ) (Real.log r) w v (m + 1) iota (τ : ℂ) =
            constantProbeObservable (paramStream (Fin.tail θ)) (Real.log r)
              w₁ v₁ m iota (τ : ℂ) := by
        simpa [s, w₁, v₁] using
          constantProbeObservable_paramStream_tail_shift r θ w v iota τ
      have hrecTail :
          constantProbeObservable (paramStream (Fin.tail θ)) (Real.log r)
              w₁ v₁ m iota (τ : ℂ) =
            (Frec r (Fin.tail θ) w₁ v₁ τ iota : ℂ) :=
        ih (Fin.tail θ) w₁ v₁ iota τ
      have hsucc :
          Frec r θ w v τ iota = Frec r (Fin.tail θ) w₁ v₁ τ iota := by
        simpa [s, w₁, v₁] using congrFun (Frec_succ r θ w v τ) iota
      calc
        constantProbeObservable (paramStream θ) (Real.log r) w v (m + 1) iota (τ : ℂ)
            = constantProbeObservable (paramStream (Fin.tail θ)) (Real.log r)
                w₁ v₁ m iota (τ : ℂ) := htail
        _ = (Frec r (Fin.tail θ) w₁ v₁ τ iota : ℂ) := hrecTail
        _ = (Frec r θ w v τ iota : ℂ) := by rw [hsucc]

/-- Arbitrary-depth bridge from the concrete constant-probe observable to the public
transformer observable on positive real probe parameters. -/
theorem constantProbeObservable_paramStream_eq_Fobs_apply_of_pos {d m : Nat}
    (r : Nat) (hr : 0 < r) (θ : Params m d) (w v : Fin d -> ℝ)
    (iota : Fin d) {τ : ℝ} (hτ : 0 < τ) :
    constantProbeObservable (paramStream θ) (Real.log r) w v m iota (τ : ℂ) =
      (Fobs r θ w v τ iota : ℂ) := by
  rw [constantProbeObservable_paramStream_eq_Frec]
  rw [← Fobs_apply_eq_Frec_apply_of_pos r hr θ w v hτ iota]

/-- The final layer recurrence for the selected observable coordinate. -/
theorem constantProbeObservable_succ_eq_last {d : Nat} (θ : LayerStream d) (b : ℝ)
    (w v : Fin d -> ℝ) (m : Nat) (iota : Fin d) :
    constantProbeObservable θ b w v (m + 1) iota =
      fun τ =>
        constantProbeLastLower θ b w v m iota τ
          + constantProbeGate θ b w v m τ
            * constantProbeLastCoeff θ b w v m iota τ := by
  funext τ
  have h := congrFun
    (formalVVec_succ_visible θ m (constantProbeGateStream θ b w v τ) w v) iota
  simpa [constantProbeObservable, constantProbeLastLower, constantProbeLastCoeff,
    constantProbeGateStream, formalVisibleCoord, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul] using h

/-- The concrete depth-`m` observable is analytic off the first `m` strata. -/
theorem constantProbeObservable_analyticOn_regular {d : Nat}
    (θ : LayerStream d) (b : ℝ) (w v : Fin d -> ℝ) (m : Nat) (iota : Fin d) :
    AnalyticOnNhd ℂ (constantProbeObservable θ b w v m iota)
      (partialUnion (constantProbeStratum θ b w v) m)ᶜ := by
  let U : Set ℂ := (partialUnion (constantProbeStratum θ b w v) m)ᶜ
  let x : ℂ -> Fin m -> ℂ :=
    fun τ i => constantProbeGate θ b w v (i : Nat) τ
  have hgate : ∀ i : Fin m, AnalyticOnNhd ℂ (fun τ => x τ i) U := by
    intro i
    exact constantProbeGate_analyticOn_later_omega θ b w v i.isLt
  have hpoly :
      AnalyticOnNhd ℂ
        (fun τ => MvPolynomial.eval (x τ) (formalVVecPoly θ m w v iota)) U :=
    gatePolynomial_eval_analyticOnNhd (formalVVecPoly θ m w v iota) hgate
  have hEq :
      (fun τ => MvPolynomial.eval (x τ) (formalVVecPoly θ m w v iota)) =
        constantProbeObservable θ b w v m iota := by
    funext τ
    have heval :=
      congrFun (eval_formalVVecPoly θ m (x τ) w v) iota
    have hstream :
        formalVVec θ m (extendGate (x τ)) w v =
          formalVVec θ m (constantProbeGateStream θ b w v τ) w v :=
      formalVVec_congr_of_eqOn_lt θ w v (by
        intro i hi
        simp [x, extendGate, constantProbeGateStream, hi])
    calc
      MvPolynomial.eval (x τ) (formalVVecPoly θ m w v iota)
          = formalVVec θ m (extendGate (x τ)) w v iota := by
            simpa using heval
      _ = formalVVec θ m (constantProbeGateStream θ b w v τ) w v iota := by
            rw [hstream]
      _ = constantProbeObservable θ b w v m iota τ := rfl
  simpa [U, hEq] using hpoly

/-- The visible coefficient in the final one-step recurrence is analytic off the first
`m` strata. -/
theorem constantProbeLastCoeff_analyticOn_regular {d : Nat}
    (θ : LayerStream d) (b : ℝ) (w v : Fin d -> ℝ) (m : Nat) (iota : Fin d) :
    AnalyticOnNhd ℂ (constantProbeLastCoeff θ b w v m iota)
      (partialUnion (constantProbeStratum θ b w v) m)ᶜ := by
  let U : Set ℂ := (partialUnion (constantProbeStratum θ b w v) m)ᶜ
  let x : ℂ -> Fin m -> ℂ :=
    fun τ i => constantProbeGate θ b w v (i : Nat) τ
  have hgate : ∀ i : Fin m, AnalyticOnNhd ℂ (fun τ => x τ i) U := by
    intro i
    exact constantProbeGate_analyticOn_later_omega θ b w v i.isLt
  have hpoly :
      AnalyticOnNhd ℂ
        (fun τ => MvPolynomial.eval (x τ) (formalVisiblePoly θ m w iota)) U :=
    gatePolynomial_eval_analyticOnNhd (formalVisiblePoly θ m w iota) hgate
  have hEq :
      (fun τ => MvPolynomial.eval (x τ) (formalVisiblePoly θ m w iota)) =
        constantProbeLastCoeff θ b w v m iota := by
    funext τ
    have heval :=
      congrFun (eval_formalVisiblePoly θ m (x τ) w) iota
    have hstream :
        formalVisible θ m (extendGate (x τ)) w =
          formalVisible θ m (constantProbeGateStream θ b w v τ) w :=
      formalVisible_congr_of_eqOn_lt θ w (by
        intro i hi
        simp [x, extendGate, constantProbeGateStream, hi])
    calc
      MvPolynomial.eval (x τ) (formalVisiblePoly θ m w iota)
          = formalVisible θ m (extendGate (x τ)) w iota := by
            simpa using heval
      _ = formalVisible θ m (constantProbeGateStream θ b w v τ) w iota := by
            rw [hstream]
      _ = constantProbeLastCoeff θ b w v m iota τ := by
            simp [constantProbeLastCoeff, formalVisibleCoord]
  simpa [U, hEq] using hpoly

/-- Base expansion for the depth-zero selected observable. -/
noncomputable def constantProbeObservableExpansion_zero {d : Nat} (θ : LayerStream d)
    (b : ℝ) (w v : Fin d -> ℝ) (iota : Fin d) :
    LastLayerExpansion (constantProbeGate θ b w v) 0
      (constantProbeObservable θ b w v 0 iota) :=
  (LastLayerExpansion.const (s := constantProbeGate θ b w v) (v iota : ℂ)).congr
    (by
      intro τ
      simp [constantProbeObservable_zero θ b w v iota])

/-- One-step construction of the final-layer expansion from an expansion of the lower
matrix-vector term. -/
noncomputable def constantProbeLastLayerExpansion_succ {d : Nat}
    (θ : LayerStream d) (b : ℝ) (w v : Fin d -> ℝ) (m : Nat) (iota : Fin d)
    (E : LastLayerExpansion (constantProbeGate θ b w v) m
      (constantProbeLastLower θ b w v m iota)) :
    LastLayerExpansion (constantProbeGate θ b w v) (m + 1)
      (constantProbeObservable θ b w v (m + 1) iota) :=
  E.snoc (constantProbeLastCoeff θ b w v m iota)
    (by
      intro τ
      rw [constantProbeObservable_succ_eq_last θ b w v m iota])

/-- Build the expansion of the lower matrix-vector term from coordinate expansions of
the previous-depth observable. -/
noncomputable def constantProbeLastLowerExpansion {d : Nat}
    (θ : LayerStream d) (b : ℝ) (w v : Fin d -> ℝ) (m : Nat) (iota : Fin d)
    (E : ∀ k : Fin d,
      LastLayerExpansion (constantProbeGate θ b w v) m
        (constantProbeObservable θ b w v m k)) :
    LastLayerExpansion (constantProbeGate θ b w v) m
      (constantProbeLastLower θ b w v m iota) :=
  (LastLayerExpansion.fintypeLinearCombination
    (fun k : Fin d => matC (skipB (θ m).1) iota k) E).congr
    (by
      intro τ
      simp [constantProbeLastLower, constantProbeObservable, Matrix.mulVec, dotProduct])

/-- Fully recursive scalar last-layer expansion for the formal constant-probe
observable. -/
noncomputable def constantProbeObservableExpansion {d : Nat}
    (θ : LayerStream d) (b : ℝ) (w v : Fin d -> ℝ) :
    (m : Nat) -> (iota : Fin d) ->
      LastLayerExpansion (constantProbeGate θ b w v) m
        (constantProbeObservable θ b w v m iota)
  | 0, iota => constantProbeObservableExpansion_zero θ b w v iota
  | m + 1, iota =>
      constantProbeLastLayerExpansion_succ θ b w v m iota
        (constantProbeLastLowerExpansion θ b w v m iota
          (fun k => constantProbeObservableExpansion θ b w v m k))

/-- If a point is outside a later partial union, it is outside every earlier one. -/
theorem notMem_partialUnion_of_le {S : Nat -> Set ℂ} {n k : Nat} {τ : ℂ}
    (hnk : n ≤ k) (hτ : τ ∉ partialUnion S k) :
    τ ∉ partialUnion S n := by
  rintro ⟨j, hj, hS⟩
  exact hτ ⟨j, Nat.lt_of_lt_of_le hj hnk, hS⟩

/-- Every coefficient in the recursive concrete last-layer expansion is continuous at
points regular for the corresponding gate. -/
theorem constantProbeObservableExpansion_coeff_continuousAt_of_regular {d : Nat}
    (θ : LayerStream d) (b : ℝ) (w v : Fin d -> ℝ) :
    ∀ m : Nat, ∀ i : Nat, ∀ iota : Fin d, ∀ τ : ℂ,
      i < m -> τ ∉ partialUnion (constantProbeStratum θ b w v) (i + 1) ->
        ContinuousAt ((constantProbeObservableExpansion θ b w v m iota).coeff i) τ := by
  intro m
  induction m with
  | zero =>
      intro i iota τ hi _hτ
      omega
  | succ m ih =>
      intro i iota τ hi hτ
      by_cases him : i = m
      · subst i
        have hτm : τ ∉ partialUnion (constantProbeStratum θ b w v) m :=
          notMem_partialUnion_of_le (S := constantProbeStratum θ b w v) (by omega) hτ
        have hcont :=
          (constantProbeLastCoeff_analyticOn_regular θ b w v m iota τ hτm).continuousAt
        simpa [constantProbeObservableExpansion, constantProbeLastLayerExpansion_succ,
          LastLayerExpansion.snoc, LastLayerExpansion.coeffSnoc] using hcont
      · have hi' : i < m := by omega
        have hsum : ContinuousAt
            (fun z => ∑ k : Fin d, matC (skipB (θ m).1) iota k *
              (constantProbeObservableExpansion θ b w v m k).coeff i z) τ := by
          have hcoeff : ∀ k : Fin d,
              ContinuousAt ((constantProbeObservableExpansion θ b w v m k).coeff i) τ := by
            intro k
            exact ih i k τ hi' hτ
          fun_prop
        simpa [constantProbeObservableExpansion, constantProbeLastLayerExpansion_succ,
          LastLayerExpansion.snoc, LastLayerExpansion.coeffSnoc, him,
          constantProbeLastLowerExpansion, LastLayerExpansion.fintypeLinearCombination,
          LastLayerExpansion.congr] using hsum

/-- The appended final coefficient in the concrete depth-`m+1` observable expansion is
continuous at points regular for the first `m` strata. -/
theorem constantProbeObservableExpansion_lastCoeff_continuousAt_of_regular {d : Nat}
    (θ : LayerStream d) (b : ℝ) (w v : Fin d -> ℝ) (m : Nat) (iota : Fin d)
    {τ : ℂ} (hτ : τ ∉ partialUnion (constantProbeStratum θ b w v) m) :
    ContinuousAt ((constantProbeObservableExpansion θ b w v (m + 1) iota).coeff m) τ := by
  have hcont :=
    (constantProbeLastCoeff_analyticOn_regular θ b w v m iota τ hτ).continuousAt
  simpa [constantProbeObservableExpansion, constantProbeLastLayerExpansion_succ,
    LastLayerExpansion.snoc, LastLayerExpansion.coeffSnoc] using hcont

/-- Raw `stratpole` conclusion before the data is bundled as a
`ConcreteStratification`. -/
structure RawStratPoleData (S : Nat -> Set ℂ) (s : Nat -> ℂ -> ℂ)
    (j : Nat) (τ : ℂ) : Prop where
  punctured_omega_succ :
    ∀ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ), z ∈ (partialUnion S (j + 1))ᶜ
  gate_blowsUpAt : BlowsUpAt (s j) τ

/-- Set-theoretic and sigmoid-pole obligations for a transformer constant-probe
stratification.

These are exactly the non-analytic set and gate-pole facts needed to build the
`SigmoidStratification` field of `ConcreteStratification`, plus the countability and
real-axis avoidance facts consumed later in Step 1. -/
structure ConcreteStrataObligations
    (S : Nat -> Set ℂ) (H s : Nat -> ℂ -> ℂ) (m : Nat) : Prop where
  strata : StrataSystem S m
  regular : ∀ j, j < m -> S j ⊆ (partialUnion S j)ᶜ
  gate_eq : ∀ j, j < m -> s j = fun τ => csig (H j τ)
  pole_value : ∀ j, j < m -> ∀ τ, τ ∈ S j -> H j τ ∈ oddPiI
  H_tendsto_at_stratum :
    ∀ j, j < m -> ∀ τ, τ ∈ S j ->
      Filter.Tendsto (H j) (nhdsWithin τ ({τ}ᶜ : Set ℂ)) (nhds (H j τ))
  denom_eventually_ne :
    ∀ j, j < m -> ∀ τ, τ ∈ S j ->
      ∀ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ), 1 + Complex.exp (-(H j z)) ≠ 0
  partialUnion_countable : ∀ n, n ≤ m -> (partialUnion S n).Countable
  partialUnion_avoids_real : ∀ n, n ≤ m -> ∀ x : ℝ, (x : ℂ) ∉ partialUnion S n

namespace ConcreteStrataObligations

variable {S : Nat -> Set ℂ} {H s : Nat -> ℂ -> ℂ} {m : Nat}
variable (D : ConcreteStrataObligations S H s m)
include D

/-- Forget the extra set-size facts and produce the core sigmoid stratification. -/
theorem toSigmoidStratification : SigmoidStratification S H s m where
  strata := D.strata
  regular := D.regular
  gate_eq := D.gate_eq
  pole_value := D.pole_value
  H_tendsto_at_stratum := D.H_tendsto_at_stratum
  denom_eventually_ne := D.denom_eventually_ne

theorem closed_partialUnion {n : Nat} (hn : n ≤ m) :
    IsClosed (partialUnion S n) :=
  D.strata.closed_partial n hn

theorem singularSet_countable :
    (partialUnion S m).Countable :=
  D.partialUnion_countable m le_rfl

theorem singularSet_avoids_real (x : ℝ) :
    (x : ℂ) ∉ partialUnion S m :=
  D.partialUnion_avoids_real m le_rfl x

theorem punctured_isolated {j : Nat} (hj : j < m) {τ : ℂ}
    (hτ : τ ∈ S j) :
    IsPuncturedIsolated (partialUnion S (j + 1)) τ :=
  D.toSigmoidStratification.punctured_isolated hj hτ

theorem gate_blowsUpAt {j : Nat} (hj : j < m) {τ : ℂ}
    (hτ : τ ∈ S j) :
    BlowsUpAt (s j) τ :=
  D.toSigmoidStratification.gate_blowsUpAt hj hτ

theorem stratpole {j : Nat} (hj : j < m) {τ : ℂ}
    (hτ : τ ∈ S j) :
    RawStratPoleData S s j τ where
  punctured_omega_succ := by
    have hIso : IsPuncturedIsolated (partialUnion S (j + 1)) τ :=
      D.punctured_isolated hj hτ
    simpa [IsPuncturedIsolated] using hIso
  gate_blowsUpAt := D.gate_blowsUpAt hj hτ

end ConcreteStrataObligations

/-- Transformer constant-probe strata obligations with the definitional `gate_eq`
removed.

For the actual constant-probe fields, `s_j = csig ∘ H_j` follows from
`constantProbeGate_eq_csig`, so constructor users only need to provide the geometric,
pole, isolation, countability, and real-axis facts. -/
structure ConstantProbeStrataCoreObligations {d : Nat} (θ : LayerStream d) (b : ℝ)
    (w v : Fin d -> ℝ) (m : Nat) : Prop where
  strata : StrataSystem (constantProbeStratum θ b w v) m
  regular :
    ∀ j, j < m ->
      constantProbeStratum θ b w v j ⊆
        (partialUnion (constantProbeStratum θ b w v) j)ᶜ
  pole_value :
    ∀ j, j < m -> ∀ τ, τ ∈ constantProbeStratum θ b w v j ->
      constantProbeGateArgument θ b w v j τ ∈ oddPiI
  H_tendsto_at_stratum :
    ∀ j, j < m -> ∀ τ, τ ∈ constantProbeStratum θ b w v j ->
      Filter.Tendsto (constantProbeGateArgument θ b w v j)
        (nhdsWithin τ ({τ}ᶜ : Set ℂ))
        (nhds (constantProbeGateArgument θ b w v j τ))
  denom_eventually_ne :
    ∀ j, j < m -> ∀ τ, τ ∈ constantProbeStratum θ b w v j ->
      ∀ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ),
        1 + Complex.exp (-(constantProbeGateArgument θ b w v j z)) ≠ 0
  partialUnion_countable :
    ∀ n, n ≤ m -> (partialUnion (constantProbeStratum θ b w v) n).Countable
  partialUnion_avoids_real :
    ∀ n, n ≤ m -> ∀ x : ℝ,
      (x : ℂ) ∉ partialUnion (constantProbeStratum θ b w v) n

namespace ConstantProbeStrataCoreObligations

variable {d : Nat} {θ : LayerStream d} {b : ℝ} {w v : Fin d -> ℝ} {m : Nat}

/-- Constructor that discharges the two definitional constant-probe stratum fields
(`regular` and `pole_value`) from the actual recursive definition. -/
def ofStrata
    (hstrata : StrataSystem (constantProbeStratum θ b w v) m)
    (hH_tendsto_at_stratum :
      ∀ j, j < m -> ∀ τ, τ ∈ constantProbeStratum θ b w v j ->
        Filter.Tendsto (constantProbeGateArgument θ b w v j)
          (nhdsWithin τ ({τ}ᶜ : Set ℂ))
          (nhds (constantProbeGateArgument θ b w v j τ)))
    (hdenom_eventually_ne :
      ∀ j, j < m -> ∀ τ, τ ∈ constantProbeStratum θ b w v j ->
        ∀ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ),
          1 + Complex.exp (-(constantProbeGateArgument θ b w v j z)) ≠ 0)
    (hpartialUnion_countable :
      ∀ n, n ≤ m -> (partialUnion (constantProbeStratum θ b w v) n).Countable)
    (hpartialUnion_avoids_real :
      ∀ n, n ≤ m -> ∀ x : ℝ,
        (x : ℂ) ∉ partialUnion (constantProbeStratum θ b w v) n) :
    ConstantProbeStrataCoreObligations θ b w v m where
  strata := hstrata
  regular := fun j _hj => constantProbeStratum_regular θ b w v j
  pole_value := fun _j _hj _τ hτ => constantProbeStratum_pole_value θ b w v hτ
  H_tendsto_at_stratum := hH_tendsto_at_stratum
  denom_eventually_ne := hdenom_eventually_ne
  partialUnion_countable := hpartialUnion_countable
  partialUnion_avoids_real := hpartialUnion_avoids_real

/-- Constructor that additionally discharges punctured denominator nonvanishing from the
abstract stratum-isolation package and the recursive definition of the concrete strata. -/
def ofStrataAndTendsto
    (hstrata : StrataSystem (constantProbeStratum θ b w v) m)
    (hH_tendsto_at_stratum :
      ∀ j, j < m -> ∀ τ, τ ∈ constantProbeStratum θ b w v j ->
        Filter.Tendsto (constantProbeGateArgument θ b w v j)
          (nhdsWithin τ ({τ}ᶜ : Set ℂ))
          (nhds (constantProbeGateArgument θ b w v j τ)))
    (hpartialUnion_countable :
      ∀ n, n ≤ m -> (partialUnion (constantProbeStratum θ b w v) n).Countable)
    (hpartialUnion_avoids_real :
      ∀ n, n ≤ m -> ∀ x : ℝ,
        (x : ℂ) ∉ partialUnion (constantProbeStratum θ b w v) n) :
    ConstantProbeStrataCoreObligations θ b w v m :=
  ConstantProbeStrataCoreObligations.ofStrata hstrata hH_tendsto_at_stratum
    (fun _j hj _τ hτ =>
      constantProbe_denom_eventually_ne_zero_of_strata θ b w v hstrata hj hτ)
    hpartialUnion_countable hpartialUnion_avoids_real

/-- Constructor from per-stratum countability and real-axis avoidance.  This is often
the most convenient form for the concrete construction, where each stratum is proved
discrete before finite partial unions are considered. -/
def ofStrataAndTendstoOfStrataFacts
    (hstrata : StrataSystem (constantProbeStratum θ b w v) m)
    (hH_tendsto_at_stratum :
      ∀ j, j < m -> ∀ τ, τ ∈ constantProbeStratum θ b w v j ->
        Filter.Tendsto (constantProbeGateArgument θ b w v j)
          (nhdsWithin τ ({τ}ᶜ : Set ℂ))
          (nhds (constantProbeGateArgument θ b w v j τ)))
    (hstratum_countable :
      ∀ j, j < m -> (constantProbeStratum θ b w v j).Countable)
    (hstratum_avoids_real :
      ∀ j, j < m -> ∀ x : ℝ, (x : ℂ) ∉ constantProbeStratum θ b w v j) :
    ConstantProbeStrataCoreObligations θ b w v m :=
  ConstantProbeStrataCoreObligations.ofStrataAndTendsto hstrata
    hH_tendsto_at_stratum
    (partialUnion_countable_of_strata_countable hstratum_countable)
    (partialUnion_avoids_real_of_strata_avoids_real hstratum_avoids_real)

/-- Variant of `ofStrataAndTendstoOfStrataFacts` with the real-axis avoidance field
discharged by the concrete recursive constant-probe construction. -/
def ofStrataAndTendstoOfStrataCountable
    (hstrata : StrataSystem (constantProbeStratum θ b w v) m)
    (hH_tendsto_at_stratum :
      ∀ j, j < m -> ∀ τ, τ ∈ constantProbeStratum θ b w v j ->
        Filter.Tendsto (constantProbeGateArgument θ b w v j)
          (nhdsWithin τ ({τ}ᶜ : Set ℂ))
          (nhds (constantProbeGateArgument θ b w v j τ)))
    (hstratum_countable :
      ∀ j, j < m -> (constantProbeStratum θ b w v j).Countable) :
    ConstantProbeStrataCoreObligations θ b w v m :=
  ConstantProbeStrataCoreObligations.ofStrataAndTendstoOfStrataFacts hstrata
    hH_tendsto_at_stratum hstratum_countable
    (fun j _hj x => constantProbeStratum_avoids_real θ b w v j x)

/-- Constructor that derives the full `StrataSystem` from the per-stratum
no-accumulation facts.  This is the recursive topology part of the constant-probe
stratification tower: closedness of finite partial unions is automatic once each new
stratum has no accumulation in the previous regular domain. -/
def ofNoAccumAndTendstoOfStrataCountable
    (hnoAccumIn :
      ∀ j, j < m ->
        NoAccumIn
          (constantProbeStratum θ b w v j)
          (partialUnion (constantProbeStratum θ b w v) j)ᶜ)
    (hH_tendsto_at_stratum :
      ∀ j, j < m -> ∀ τ, τ ∈ constantProbeStratum θ b w v j ->
        Filter.Tendsto (constantProbeGateArgument θ b w v j)
          (nhdsWithin τ ({τ}ᶜ : Set ℂ))
          (nhds (constantProbeGateArgument θ b w v j τ)))
    (hstratum_countable :
      ∀ j, j < m -> (constantProbeStratum θ b w v j).Countable) :
    ConstantProbeStrataCoreObligations θ b w v m :=
  ConstantProbeStrataCoreObligations.ofStrataAndTendstoOfStrataCountable
    (StrataSystem.of_noAccumIn m hnoAccumIn)
    hH_tendsto_at_stratum hstratum_countable

/-- Leanest tendsto-based full-tower constructor.  Per-stratum countability is derived
from regularity plus no-accumulation in the previous regular domain. -/
def ofNoAccumAndTendsto
    (hnoAccumIn :
      ∀ j, j < m ->
        NoAccumIn
          (constantProbeStratum θ b w v j)
          (partialUnion (constantProbeStratum θ b w v) j)ᶜ)
    (hH_tendsto_at_stratum :
      ∀ j, j < m -> ∀ τ, τ ∈ constantProbeStratum θ b w v j ->
        Filter.Tendsto (constantProbeGateArgument θ b w v j)
          (nhdsWithin τ ({τ}ᶜ : Set ℂ))
          (nhds (constantProbeGateArgument θ b w v j τ))) :
    ConstantProbeStrataCoreObligations θ b w v m :=
  ConstantProbeStrataCoreObligations.ofNoAccumAndTendstoOfStrataCountable
    hnoAccumIn hH_tendsto_at_stratum
    (fun j hj =>
      constantProbeStratum_countable_of_noAccumIn θ b w v j
        (hnoAccumIn j hj))

/-- Leanest continuity-based full-tower constructor.  The remaining geometric field is
exactly per-stratum no-accumulation in the previous regular domain. -/
def ofNoAccumAndContinuousAt
    (hnoAccumIn :
      ∀ j, j < m ->
        NoAccumIn
          (constantProbeStratum θ b w v j)
          (partialUnion (constantProbeStratum θ b w v) j)ᶜ)
    (hH_continuousAt_stratum :
      ∀ j, j < m -> ∀ τ, τ ∈ constantProbeStratum θ b w v j ->
        ContinuousAt (constantProbeGateArgument θ b w v j) τ) :
    ConstantProbeStrataCoreObligations θ b w v m :=
  ConstantProbeStrataCoreObligations.ofNoAccumAndTendsto hnoAccumIn
    (fun j hj τ hτ =>
      (hH_continuousAt_stratum j hj τ hτ).tendsto.mono_left nhdsWithin_le_nhds)

/-- Recursive analytic constructor for the concrete constant-probe strata tower.

This strengthens `ofHAnalyticOnOmegaAndDenomNoCollapse`: callers only supply the
preactivation analyticity fields.  At stage `j`, the already-built tower for the previous
partial union supplies countability and real-axis avoidance, which rule out local
denominator collapse by
`constantProbeDenom_not_eventually_zero_of_H_analyticOnNhd_of_partialUnion_facts`. -/
def ofHAnalyticOnOmega
    (hH_analyticOn_omega :
      ∀ j, j < m ->
        AnalyticOnNhd ℂ (constantProbeGateArgument θ b w v j)
          (partialUnion (constantProbeStratum θ b w v) j)ᶜ) :
    ConstantProbeStrataCoreObligations θ b w v m := by
  revert hH_analyticOn_omega
  induction m with
  | zero =>
      intro _hH_analyticOn_omega
      exact ConstantProbeStrataCoreObligations.ofNoAccumAndContinuousAt
        (fun j hj => by omega)
        (fun j hj _τ _hτ => by omega)
  | succ m ih =>
      intro hH_analyticOn_omega
      let Dprev : ConstantProbeStrataCoreObligations θ b w v m :=
        ih (fun j hj => hH_analyticOn_omega j (Nat.lt_trans hj (Nat.lt_succ_self m)))
      have hnoAccumIn :
          ∀ j, j < m + 1 ->
            NoAccumIn
              (constantProbeStratum θ b w v j)
              (partialUnion (constantProbeStratum θ b w v) j)ᶜ := by
        intro j hj
        by_cases hjm : j < m
        · exact Dprev.strata.noAccumIn j hjm
        · have hj_eq : j = m := by omega
          subst j
          refine
            constantProbeStratum_noAccumIn_of_H_analyticOnNhd_of_denom_not_eventually_zero
              θ b w v m (hH_analyticOn_omega m (Nat.lt_succ_self m)) ?_
          intro τ hτ _hDτ
          exact
            constantProbeDenom_not_eventually_zero_of_H_analyticOnNhd_of_partialUnion_facts
              θ b w v m (hH_analyticOn_omega m (Nat.lt_succ_self m))
              (Dprev.partialUnion_countable m le_rfl)
              (Dprev.partialUnion_avoids_real m le_rfl) hτ
      exact ConstantProbeStrataCoreObligations.ofNoAccumAndContinuousAt
        hnoAccumIn
        (fun j hj τ hτ =>
          (hH_analyticOn_omega j hj τ
            (constantProbeStratum_regular θ b w v j hτ)).continuousAt)

/-- Fully concrete analytic constructor using the recursive analytic family proved for
constant-probe preactivations. -/
def ofConcreteAnalytic
    {d : Nat} (θ : LayerStream d) (b : ℝ) (w v : Fin d -> ℝ) (m : Nat) :
    ConstantProbeStrataCoreObligations θ b w v m :=
  ConstantProbeStrataCoreObligations.ofHAnalyticOnOmega
    (θ := θ) (b := b) (w := w) (v := v) (m := m)
    (fun j _hj => constantProbeGateArgument_analyticOn_omega θ b w v j)

/-- Preferred analytic full-tower constructor for the concrete constant-probe
stratification.  The remaining mathematical inputs are:

* each preactivation `H_j` is analytic on the previous regular domain;
* the denominator `1 + exp(-H_j)` is not locally identically zero at any regular zero.

The recursive set-theoretic fields, per-stratum countability, real-axis avoidance,
punctured denominator nonvanishing at stratum points, and `H_j` continuity/tendsto fields
are all derived. -/
def ofHAnalyticOnOmegaAndDenomNoCollapse
    (hH_analyticOn_omega :
      ∀ j, j < m ->
        AnalyticOnNhd ℂ (constantProbeGateArgument θ b w v j)
          (partialUnion (constantProbeStratum θ b w v) j)ᶜ)
    (hD_not_eventually_zero :
      ∀ j, j < m -> ∀ τ,
        τ ∉ partialUnion (constantProbeStratum θ b w v) j ->
        constantProbeDenom θ b w v j τ = 0 ->
          ¬ (∀ᶠ z in nhds τ, constantProbeDenom θ b w v j z = 0)) :
    ConstantProbeStrataCoreObligations θ b w v m :=
  ConstantProbeStrataCoreObligations.ofNoAccumAndContinuousAt
    (fun j hj =>
      constantProbeStratum_noAccumIn_of_H_analyticOnNhd_of_denom_not_eventually_zero
        θ b w v j (hH_analyticOn_omega j hj)
        (hD_not_eventually_zero j hj))
    (fun j hj τ hτ =>
      (hH_analyticOn_omega j hj τ
        (constantProbeStratum_regular θ b w v j hτ)).continuousAt)

variable (D : ConstantProbeStrataCoreObligations θ b w v m)
include D

/-- Restore the full `ConcreteStrataObligations` package for the actual constant-probe
gate definitions. -/
theorem toConcreteStrataObligations :
    ConcreteStrataObligations
      (constantProbeStratum θ b w v)
      (constantProbeGateArgument θ b w v)
      (constantProbeGate θ b w v) m where
  strata := D.strata
  regular := D.regular
  gate_eq := fun j _hj => constantProbeGate_eq_csig θ b w v j
  pole_value := D.pole_value
  H_tendsto_at_stratum := D.H_tendsto_at_stratum
  denom_eventually_ne := D.denom_eventually_ne
  partialUnion_countable := D.partialUnion_countable
  partialUnion_avoids_real := D.partialUnion_avoids_real

end ConstantProbeStrataCoreObligations

/-- Analytic obligations for the concrete observable and gates on the regular domains. -/
structure ConcreteAnalyticObligations
    (S : Nat -> Set ℂ) (s : Nat -> ℂ -> ℂ) (m : Nat)
    (observable : ℂ -> ℂ) : Prop where
  gate_analyticOn_omega :
    ∀ j, j < m -> AnalyticOnNhd ℂ (s j) (partialUnion S (j + 1))ᶜ
  observable_analyticOn_regular : AnalyticOnNhd ℂ observable (partialUnion S m)ᶜ
  observable_continuousAt_regular : ∀ τ, τ ∉ partialUnion S m -> ContinuousAt observable τ

namespace ConcreteAnalyticObligations

variable {S : Nat -> Set ℂ} {s : Nat -> ℂ -> ℂ} {m : Nat}
variable {observable : ℂ -> ℂ} (D : ConcreteAnalyticObligations S s m observable)
include D

/-- Constructor that derives regular-point continuity from the regular-domain analytic
extension. -/
def ofAnalyticOnNhd
    (hgate_analyticOn_omega :
      ∀ j, j < m -> AnalyticOnNhd ℂ (s j) (partialUnion S (j + 1))ᶜ)
    (hobservable_analyticOn_regular : AnalyticOnNhd ℂ observable (partialUnion S m)ᶜ) :
    ConcreteAnalyticObligations S s m observable where
  gate_analyticOn_omega := hgate_analyticOn_omega
  observable_analyticOn_regular := hobservable_analyticOn_regular
  observable_continuousAt_regular := fun τ hτ =>
    (hobservable_analyticOn_regular τ hτ).continuousAt

end ConcreteAnalyticObligations

/-- Packaged concrete stratification data for one constant probe.

The full transformer construction can instantiate this structure once the concrete
`S^j`, `H_j`, `s_j`, and observable extension are available.  Until then, downstream
Step 1 shards can depend on this exact interface instead of on unfinished construction
details. -/
structure ConcreteStratification (m : Nat) where
  b : ℝ
  lambda1 : ℝ
  S : Nat -> Set ℂ
  H : Nat -> ℂ -> ℂ
  s : Nat -> ℂ -> ℂ
  observable : ℂ -> ℂ
  sigmoid : SigmoidStratification S H s m
  firstStratum : FirstStratumFormula (S 0) b lambda1
  partialUnion_countable : ∀ n, n ≤ m -> (partialUnion S n).Countable
  partialUnion_avoids_real : ∀ n, n ≤ m -> ∀ x : ℝ, (x : ℂ) ∉ partialUnion S n
  gate_analyticOn_omega :
    ∀ j, j < m -> AnalyticOnNhd ℂ (s j) (partialUnion S (j + 1))ᶜ
  observable_analyticOn_regular : AnalyticOnNhd ℂ observable (partialUnion S m)ᶜ
  observable_continuousAt_regular : ∀ τ, τ ∉ partialUnion S m -> ContinuousAt observable τ
  lastLayer : LastLayerExpansion s m observable

/-- Constructor input for a transformer constant probe.

This is the sharpened instantiation checklist for `ConcreteStratification`: once the
transformer-specific construction supplies the raw sets, preactivations, gates,
observable, first-stratum formula, set/pole obligations, analytic obligations, and
last-layer expansion, this package compiles directly to the downstream interface. -/
structure ConcreteStratificationData (m : Nat) where
  b : ℝ
  lambda1 : ℝ
  S : Nat -> Set ℂ
  H : Nat -> ℂ -> ℂ
  s : Nat -> ℂ -> ℂ
  observable : ℂ -> ℂ
  firstStratum : FirstStratumFormula (S 0) b lambda1
  strata : ConcreteStrataObligations S H s m
  analytic : ConcreteAnalyticObligations S s m observable
  lastLayer : LastLayerExpansion s m observable

/-- Actual transformer constant-probe constructor data.

The fields left here are the hard transformer-specific facts: strata geometry and
regular-domain analyticity.  The concrete definitions of `S`, `H`, `s`, the
first-stratum formula, the observable, and the formal scalar last-layer expansion are
fixed by the parameters. -/
structure ConstantProbeConcreteData {d : Nat} (θ : LayerStream d) (b : ℝ)
    (w v : Fin d -> ℝ) (m : Nat) (iota : Fin d) where
  strata : ConstantProbeStrataCoreObligations θ b w v m
  analytic :
    ConcreteAnalyticObligations
      (constantProbeStratum θ b w v)
      (constantProbeGate θ b w v) m
      (constantProbeObservable θ b w v m iota)

namespace ConstantProbeConcreteData

variable {d : Nat} {θ : LayerStream d} {b : ℝ} {w v : Fin d -> ℝ}
variable {m : Nat} {iota : Fin d}

/-- Constructor for actual constant probes where regular-point continuity is supplied by
the observable's analytic extension. -/
def ofAnalyticOnNhd
    (hstrata : ConstantProbeStrataCoreObligations θ b w v m)
    (hgate_analyticOn_omega :
      ∀ j, j < m ->
        AnalyticOnNhd ℂ (constantProbeGate θ b w v j)
          (partialUnion (constantProbeStratum θ b w v) (j + 1))ᶜ)
    (hobservable_analyticOn_regular :
      AnalyticOnNhd ℂ (constantProbeObservable θ b w v m iota)
        (partialUnion (constantProbeStratum θ b w v) m)ᶜ) :
    ConstantProbeConcreteData θ b w v m iota where
  strata := hstrata
  analytic :=
    ConcreteAnalyticObligations.ofAnalyticOnNhd
      hgate_analyticOn_omega hobservable_analyticOn_regular

/-- Fully concrete constant-probe data from the recursive concrete strata and
polynomial observable analyticity. -/
noncomputable def ofConcrete
    {d : Nat} (θ : LayerStream d) (b : ℝ) (w v : Fin d -> ℝ)
    (m : Nat) (iota : Fin d) :
    ConstantProbeConcreteData θ b w v m iota :=
  ConstantProbeConcreteData.ofAnalyticOnNhd
    (θ := θ) (b := b) (w := w) (v := v) (m := m) (iota := iota)
    (ConstantProbeStrataCoreObligations.ofConcreteAnalytic θ b w v m)
    (fun j _hj =>
      constantProbeGate_analyticOn_later_omega θ b w v
        (i := j) (j := j + 1) (Nat.lt_succ_self j))
    (constantProbeObservable_analyticOn_regular θ b w v m iota)

/-- Compile the actual constant-probe fields into the generic constructor package. -/
noncomputable def toConcreteStratificationData
    (D : ConstantProbeConcreteData θ b w v m iota) :
    ConcreteStratificationData m where
  b := b
  lambda1 := constantProbeFirstSlope θ w v
  S := constantProbeStratum θ b w v
  H := constantProbeGateArgument θ b w v
  s := constantProbeGate θ b w v
  observable := constantProbeObservable θ b w v m iota
  firstStratum := constantProbeFirstStratumFormula θ b w v
  strata := D.strata.toConcreteStrataObligations
  analytic := D.analytic
  lastLayer := constantProbeObservableExpansion θ b w v m iota

/-- For finite parameters, the compiled first slope is the public `firstSlope`. -/
theorem toConcreteStratificationData_lambda1_eq_firstSlope {L d m : Nat}
    {θ : Params L d} {b : ℝ} {w v : Fin d -> ℝ} {iota : Fin d}
    (D : ConstantProbeConcreteData (paramStream θ) b w v m iota) :
    (D.toConcreteStratificationData).lambda1 = firstSlope θ w v := by
  simp [toConcreteStratificationData, constantProbeFirstSlope_paramStream_eq_firstSlope]

end ConstantProbeConcreteData

namespace ConcreteStratificationData

/-- Build the compiled `ConcreteStratification` interface from the constructor input. -/
def toConcreteStratification {m : Nat} (D : ConcreteStratificationData m) :
    ConcreteStratification m where
  b := D.b
  lambda1 := D.lambda1
  S := D.S
  H := D.H
  s := D.s
  observable := D.observable
  sigmoid := ConcreteStrataObligations.toSigmoidStratification D.strata
  firstStratum := D.firstStratum
  partialUnion_countable := D.strata.partialUnion_countable
  partialUnion_avoids_real := D.strata.partialUnion_avoids_real
  gate_analyticOn_omega := D.analytic.gate_analyticOn_omega
  observable_analyticOn_regular := D.analytic.observable_analyticOn_regular
  observable_continuousAt_regular := D.analytic.observable_continuousAt_regular
  lastLayer := D.lastLayer

end ConcreteStratificationData

namespace ConstantProbeConcreteData

variable {d : Nat} {θ : LayerStream d} {b : ℝ} {w v : Fin d -> ℝ}
variable {m : Nat} {iota : Fin d}

/-- Compile the actual constant-probe fields all the way to `ConcreteStratification`. -/
noncomputable def toConcreteStratification
    (D : ConstantProbeConcreteData θ b w v m iota) :
    ConcreteStratification m :=
  D.toConcreteStratificationData.toConcreteStratification

end ConstantProbeConcreteData

namespace ConcreteStratification

/-- Constructor alias for downstream workers that have assembled
`ConcreteStratificationData`. -/
def ofData {m : Nat} (D : ConcreteStratificationData m) : ConcreteStratification m :=
  D.toConcreteStratification

/-- The `j`-th concrete stratum, zero-indexed. -/
def stratum {m : Nat} (P : ConcreteStratification m) (j : Nat) : Set ℂ :=
  P.S j

/-- The regular domain before the `j`-th stratum, i.e. the complement of previous strata. -/
def omega {m : Nat} (P : ConcreteStratification m) (j : Nat) : Set ℂ :=
  (partialUnion P.S j)ᶜ

/-- The gate preactivation `H_j`. -/
def gateArgument {m : Nat} (P : ConcreteStratification m) (j : Nat) : ℂ -> ℂ :=
  P.H j

/-- The sigmoid gate `s_j`. -/
def gate {m : Nat} (P : ConcreteStratification m) (j : Nat) : ℂ -> ℂ :=
  P.s j

/-- The full singular set through depth `m`. -/
def singularSet {m : Nat} (P : ConcreteStratification m) : Set ℂ :=
  partialUnion P.S m

@[simp]
theorem stratum_eq {m : Nat} (P : ConcreteStratification m) (j : Nat) :
    P.stratum j = P.S j :=
  rfl

@[simp]
theorem omega_eq {m : Nat} (P : ConcreteStratification m) (j : Nat) :
    P.omega j = (partialUnion P.S j)ᶜ :=
  rfl

@[simp]
theorem gateArgument_eq {m : Nat} (P : ConcreteStratification m) (j : Nat) :
    P.gateArgument j = P.H j :=
  rfl

@[simp]
theorem gate_eq {m : Nat} (P : ConcreteStratification m) (j : Nat) :
    P.gate j = P.s j :=
  rfl

@[simp]
theorem singularSet_eq {m : Nat} (P : ConcreteStratification m) :
    P.singularSet = partialUnion P.S m :=
  rfl

theorem strataSystem {m : Nat} (P : ConcreteStratification m) :
    StrataSystem P.S m :=
  P.sigmoid.strata

theorem closed_partialUnion {m : Nat} (P : ConcreteStratification m) {n : Nat}
    (hn : n ≤ m) :
    IsClosed (partialUnion P.S n) :=
  P.strataSystem.closed_partial n hn

theorem singularSet_closed {m : Nat} (P : ConcreteStratification m) :
    IsClosed P.singularSet := by
  simpa [singularSet] using P.closed_partialUnion (n := m) le_rfl

theorem singularSet_countable {m : Nat} (P : ConcreteStratification m) :
    P.singularSet.Countable := by
  simpa [singularSet] using P.partialUnion_countable m le_rfl

theorem singularSet_avoids_real {m : Nat} (P : ConcreteStratification m) (x : ℝ) :
    (x : ℂ) ∉ P.singularSet := by
  simpa [singularSet] using P.partialUnion_avoids_real m le_rfl x

theorem stratum_subset_singular_through {m : Nat} (P : ConcreteStratification m)
    {j : Nat} (_hj : j < m) :
    P.S j ⊆ partialUnion P.S (j + 1) := by
  intro τ hτ
  exact ⟨j, Nat.lt_succ_self j, hτ⟩

theorem stratum_avoids_real {m : Nat} (P : ConcreteStratification m) {j : Nat}
    (hj : j < m) (x : ℝ) :
    (x : ℂ) ∉ P.S j := by
  intro hx
  exact P.partialUnion_avoids_real (j + 1) (Nat.succ_le_of_lt hj) x
    (P.stratum_subset_singular_through hj hx)

theorem mem_omega_of_mem_stratum {m : Nat} (P : ConcreteStratification m) {j : Nat}
    (hj : j < m) {τ : ℂ} (hτ : τ ∈ P.S j) :
    τ ∈ P.omega j := by
  simpa [omega] using P.sigmoid.regular j hj hτ

theorem gate_formula {m : Nat} (P : ConcreteStratification m) {j : Nat} (hj : j < m) :
    P.s j = fun τ => csig (P.H j τ) :=
  P.sigmoid.gate_eq j hj

theorem gate_analyticOn {m : Nat} (P : ConcreteStratification m) {j : Nat}
    (hj : j < m) :
    AnalyticOnNhd ℂ (P.s j) (P.omega (j + 1)) := by
  simpa [omega] using P.gate_analyticOn_omega j hj

theorem observable_analyticOn_singularCompl {m : Nat} (P : ConcreteStratification m) :
    AnalyticOnNhd ℂ P.observable P.singularSetᶜ := by
  simpa [singularSet] using P.observable_analyticOn_regular

theorem observable_continuousAt_of_regular {m : Nat} (P : ConcreteStratification m)
    {τ : ℂ} (hτ : τ ∉ P.singularSet) :
    ContinuousAt P.observable τ := by
  exact P.observable_continuousAt_regular τ (by simpa [singularSet] using hτ)

theorem first_stratum_eq_firstPoleSet {m : Nat} (P : ConcreteStratification m)
    (hlam : P.lambda1 ≠ 0) :
    P.S 0 = firstPoleSet P.b P.lambda1 :=
  P.firstStratum.nonzero hlam

theorem first_stratum_eq_empty {m : Nat} (P : ConcreteStratification m)
    (hlam : P.lambda1 = 0) :
    P.S 0 = ∅ :=
  P.firstStratum.zero hlam

theorem notMem_first_stratum_of_lambda_eq_zero {m : Nat} (P : ConcreteStratification m)
    (hlam : P.lambda1 = 0) (τ : ℂ) :
    τ ∉ P.S 0 := by
  rw [P.first_stratum_eq_empty hlam]
  simp

/-- Concrete `stratpole` package for a point of a stratum. -/
structure StratPoleData {m : Nat} (P : ConcreteStratification m) (j : Nat) (τ : ℂ) :
    Prop where
  punctured_omega_succ :
    ∀ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ), z ∈ P.omega (j + 1)
  gate_blowsUpAt : BlowsUpAt (P.s j) τ

/-- Concrete `stratpole`: a stratum point is punctured-regular for the next domain, and
the corresponding gate blows up there. -/
theorem stratpole {m : Nat} (P : ConcreteStratification m) {j : Nat} (hj : j < m)
    {τ : ℂ} (hτ : τ ∈ P.S j) :
    StratPoleData P j τ where
  punctured_omega_succ := by
    have hIso : IsPuncturedIsolated (partialUnion P.S (j + 1)) τ :=
      P.sigmoid.punctured_isolated hj hτ
    simpa [IsPuncturedIsolated, omega] using hIso
  gate_blowsUpAt :=
    P.sigmoid.gate_blowsUpAt hj hτ

theorem punctured_omega_succ_of_mem_stratum {m : Nat} (P : ConcreteStratification m)
    {j : Nat} (hj : j < m) {τ : ℂ} (hτ : τ ∈ P.S j) :
    ∀ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ), z ∈ P.omega (j + 1) :=
  (P.stratpole hj hτ).punctured_omega_succ

theorem gate_blowsUpAt_of_mem_stratum {m : Nat} (P : ConcreteStratification m)
    {j : Nat} (hj : j < m) {τ : ℂ} (hτ : τ ∈ P.S j) :
    BlowsUpAt (P.s j) τ :=
  (P.stratpole hj hτ).gate_blowsUpAt

theorem lower_lastlayer_puncturedBounded {m : Nat} (P : ConcreteStratification (m + 1))
    {τ : ℂ}
    (hs : ∀ i, i < m -> PuncturedBoundedAt (P.s i) τ)
    (hc : ∀ i, i < m -> PuncturedBoundedAt (P.lastLayer.coeff i) τ) :
    PuncturedBoundedAt P.lastLayer.lower τ :=
  P.lastLayer.lower_puncturedBounded hs hc

theorem observable_blowsUpAt_of_lastlayer {m : Nat} (P : ConcreteStratification (m + 1))
    {τ visible0 : ℂ}
    (hlower : PuncturedBoundedAt P.lastLayer.lower τ)
    (hgate : BlowsUpAt (P.s m) τ)
    (hvisible : Filter.Tendsto (P.lastLayer.coeff m)
      (nhdsWithin τ ({τ}ᶜ : Set ℂ)) (nhds visible0))
    (hvisible0 : visible0 ≠ 0) :
    BlowsUpAt P.observable τ :=
  P.lastLayer.observable_blowsUpAt_of_last_gate hlower hgate hvisible hvisible0

end ConcreteStratification

end TransformerIdentifiability.NLayer
