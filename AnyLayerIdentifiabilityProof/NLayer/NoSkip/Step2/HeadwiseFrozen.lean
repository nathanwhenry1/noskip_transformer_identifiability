import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Step2.ScalarZeroRigidity
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Step2.SaturatedLimits

set_option autoImplicit false

open Matrix

namespace TransformerIdentifiability.NLayer.NoSkip

noncomputable section

/-! # Faithful frozen slopes for one headwise run -/

/-- The formal gate assignment with first-layer value `z` only in head `h`
and trichotomy labels in all deeper layers. -/
noncomputable def headwiseFrozenAssignment {n k : Nat} (r : Nat)
    (h : Fin k) (z : Real) (labels : DeeperHead → TrichotomyLabel) :
    FormalAssignment (n + 1) k :=
  tupleDialFrozenAssignment r (headwiseDialTuple h z) labels

/-- The current frozen slope, indexed by its zero-based predecessor depth.
The current original layer is `q+1`, hence its TeX layer is `q+2`. -/
noncomputable def headwiseFrozenSlopeAt {n k d : Nat} (r : Nat)
    (theta : Params (n + 1) k d) (h : Fin k)
    (q : Nat) (hq : q + 1 < n + 1) (a : Fin k)
    (labels : DeeperHead → TrichotomyLabel) :
    HeadwiseSignPoint d → Real :=
  fun p ↦
    MvPolynomial.eval (headwiseFrozenAssignment r h p.2 labels)
      (formalSlope theta p.1.1 p.1.2 ⟨q + 1, hq⟩ a)

/-- The fixed matrix data appearing in the faithful scalar frozen slope. -/
noncomputable def scalarDialFormAt {n k d : Nat} (r : Nat)
    (theta : Params (n + 1) k d) (h : Fin k)
    (q : Nat) (hq : q + 1 < n + 1) (a : Fin k)
    (labels : DeeperHead → TrichotomyLabel) : ScalarDialForm d :=
  let zeta := saturatedTailFrozenFamily (n := n) (k := k) r labels
  let hqn : q ≤ n := by omega
  let R := frozenR (Fin.tail theta) zeta q hqn
  let P := frozenP (Fin.tail theta) zeta q hqn
  let Q := frozenQ (Fin.tail theta) zeta q hqn
  { C := collapseMatrix theta 0
    V := valueMatrix theta 0 h
    RtA := Rᵀ * attentionMatrix theta ⟨q + 1, hq⟩ a
    P := P
    Q := Q }

@[simp] theorem scalarDialFormAt_C {n k d : Nat} (r : Nat)
    (theta : Params (n + 1) k d) (h : Fin k)
    (q : Nat) (hq : q + 1 < n + 1) (a : Fin k)
    (labels : DeeperHead → TrichotomyLabel) :
    (scalarDialFormAt r theta h q hq a labels).C = collapseMatrix theta 0 :=
  rfl

@[simp] theorem scalarDialFormAt_V {n k d : Nat} (r : Nat)
    (theta : Params (n + 1) k d) (h : Fin k)
    (q : Nat) (hq : q + 1 < n + 1) (a : Fin k)
    (labels : DeeperHead → TrichotomyLabel) :
    (scalarDialFormAt r theta h q hq a labels).V = valueMatrix theta 0 h :=
  rfl

/-- At a headwise first-layer assignment, the gated value sum is exactly
`z V_h`. -/
theorem gatedValueSum_headwiseDialTuple {n k d : Nat}
    (theta : Params (n + 1) k d) (h : Fin k) (z : Real) :
    gatedValueSum theta 0 (headwiseDialTuple h z) =
      z • valueMatrix theta 0 h := by
  change dialValueMatrix theta (headwiseDialTuple h z) = _
  exact dialValueMatrix_headwiseDialTuple theta h z

/-- The exact no-skip first-layer stream formulas used in scalar rigidity. -/
theorem gatedEffectivePoint_headwiseDialTuple {n k d : Nat}
    (theta : Params (n + 1) k d) (h : Fin k) (z : Real)
    (w v : Vec d) :
    gatedEffectivePoint theta 0 (headwiseDialTuple h z) w v =
      ((collapseMatrix theta 0 - z • valueMatrix theta 0 h) *ᵥ w,
        collapseMatrix theta 0 *ᵥ v +
          (z • valueMatrix theta 0 h) *ᵥ w) := by
  ext <;> simp [gatedValueSum_headwiseDialTuple]

/-- The faithful formal frozen slope is exactly the repaired scalar matrix
form. -/
theorem headwiseFrozenSlopeAt_eq_scalarEval {n k d : Nat} (r : Nat)
    (theta : Params (n + 1) k d) (h : Fin k)
    (q : Nat) (hq : q + 1 < n + 1) (a : Fin k)
    (labels : DeeperHead → TrichotomyLabel)
    (p : HeadwiseSignPoint d) :
    headwiseFrozenSlopeAt r theta h q hq a labels p =
      (scalarDialFormAt r theta h q hq a labels).eval p := by
  let zeta := saturatedTailFrozenFamily (n := n) (k := k) r labels
  have hqn : q ≤ n := by omega
  rw [headwiseFrozenSlopeAt, headwiseFrozenAssignment, eval_formalSlope]
  have hp := eval_formalPoint_tupleDialFrozenAssignment r theta
    (headwiseDialTuple h p.2) labels p.1.1 p.1.2 (q + 1) (by omega)
  change matrixBilin (attentionMatrix theta ⟨q + 1, hq⟩ a)
      (evalFormalVec (tupleDialFrozenAssignment r (headwiseDialTuple h p.2) labels)
        (formalPoint theta p.1.1 p.1.2 (q + 1) (by omega)).1)
      (evalFormalVec (tupleDialFrozenAssignment r (headwiseDialTuple h p.2) labels)
        (formalPoint theta p.1.1 p.1.2 (q + 1) (by omega)).2) = _
  rw [hp.1, hp.2]
  have hsplit := frozenPoint_firstLayer_tail_aux theta
    (tupleDialFrozenFamily r (headwiseDialTuple h p.2) labels) zeta
    (tupleDialFrozenFamily_succ_eq_saturatedTail r
      (headwiseDialTuple h p.2) labels)
    p.1.1 p.1.2 q (by omega)
  rw [hsplit]
  change matrixBilin (attentionMatrix theta ⟨q + 1, hq⟩ a)
      (frozenPoint (Fin.tail theta) zeta
        (gatedEffectivePoint theta 0 (headwiseDialTuple h p.2) p.1.1 p.1.2).1
        (gatedEffectivePoint theta 0 (headwiseDialTuple h p.2) p.1.1 p.1.2).2
        q hqn).1
      (frozenPoint (Fin.tail theta) zeta
        (gatedEffectivePoint theta 0 (headwiseDialTuple h p.2) p.1.1 p.1.2).1
        (gatedEffectivePoint theta 0 (headwiseDialTuple h p.2) p.1.1 p.1.2).2
        q hqn).2 = _
  have hclosed := frozenPoint_closed (Fin.tail theta) zeta
    (gatedEffectivePoint theta 0 (headwiseDialTuple h p.2) p.1.1 p.1.2).1
    (gatedEffectivePoint theta 0 (headwiseDialTuple h p.2) p.1.1 p.1.2).2
    q hqn
  rw [hclosed.1, hclosed.2, gatedEffectivePoint_headwiseDialTuple]
  simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.smul_mulVec,
    Matrix.mulVec_smul]
  simp only [ScalarDialForm.eval, ScalarDialForm.eval_Xpoly,
    ScalarDialForm.eval_Ypoly]
  dsimp [scalarDialFormAt, ScalarDialForm.Xfun, ScalarDialForm.Yfun,
    ScalarDialForm.CzVr, ScalarDialForm.H]
  change NLayer.matrixBilin (attentionMatrix theta ⟨q + 1, hq⟩ a)
      ((frozenR (Fin.tail theta) zeta q hqn *
          (collapseMatrix theta 0 - p.2 • valueMatrix theta 0 h)) *ᵥ p.1.1)
      (((frozenP (Fin.tail theta) zeta q hqn * collapseMatrix theta 0) *ᵥ p.1.2 +
          p.2 • ((frozenP (Fin.tail theta) zeta q hqn *
            valueMatrix theta 0 h) *ᵥ p.1.1)) +
        (frozenQ (Fin.tail theta) zeta q hqn *
          (collapseMatrix theta 0 - p.2 • valueMatrix theta 0 h)) *ᵥ p.1.1) = _
  have hvec :
      ((frozenP (Fin.tail theta) zeta q hqn * collapseMatrix theta 0) *ᵥ p.1.2 +
          p.2 • ((frozenP (Fin.tail theta) zeta q hqn *
            valueMatrix theta 0 h) *ᵥ p.1.1)) +
        (frozenQ (Fin.tail theta) zeta q hqn *
          (collapseMatrix theta 0 - p.2 • valueMatrix theta 0 h)) *ᵥ p.1.1 =
      (frozenP (Fin.tail theta) zeta q hqn * collapseMatrix theta 0) *ᵥ p.1.2 +
        (p.2 • (frozenP (Fin.tail theta) zeta q hqn *
              valueMatrix theta 0 h) +
            frozenQ (Fin.tail theta) zeta q hqn *
              (collapseMatrix theta 0 - p.2 • valueMatrix theta 0 h)) *ᵥ p.1.1 := by
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec]
    abel
  rw [hvec, ScalarDialForm.matrixBilin_add_right]
  rw [ScalarDialForm.matrixBilin_mulVec_mulVec,
    ScalarDialForm.matrixBilin_mulVec_mulVec]
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  rfl

/-- TeX `lem:scalar-zero-rigidity`, now instantiated by the genuine frozen
transformer slope. -/
theorem headwiseFrozenSlopeAt_eq_zero_of_vanishesOn
    {n k d : Nat} (r : Nat)
    {thetaLive thetaDial : Params (n + 1) k d} {h : Fin k}
    {D : HeadwiseSignRegion thetaDial h}
    (R : HeadwiseRestrictedRegion D)
    (q : Nat) (hq : q + 1 < n + 1) (a : Fin k)
    (labels : DeeperHead → TrichotomyLabel)
    (hd : 2 ≤ d)
    (hdetC : (collapseMatrix thetaLive 0).det ≠ 0)
    (hdetA : (attentionMatrix thetaDial 0 h).det ≠ 0)
    (hsymA : sym (attentionMatrix thetaDial 0 h) ≠ 0)
    (hVne : valueMatrix thetaLive 0 h ≠ 0)
    (hvanish : ∀ p ∈ R.region,
      headwiseFrozenSlopeAt r thetaLive h q hq a labels p = 0) :
    headwiseFrozenSlopeAt r thetaLive h q hq a labels = 0 := by
  let Phi := scalarDialFormAt r thetaLive h q hq a labels
  have hPhiZero : Phi.IsZero := by
    apply Phi.zero_of_vanishesOn R hd
    · simpa [Phi] using hdetC
    · exact hdetA
    · exact hsymA
    · simpa [Phi] using hVne
    · intro p hp
      rw [← headwiseFrozenSlopeAt_eq_scalarEval
        r thetaLive h q hq a labels p]
      exact hvanish p hp
  funext p
  rw [Pi.zero_apply, headwiseFrozenSlopeAt_eq_scalarEval]
  exact Phi.eval_eq_zero_of_isZero hPhiZero p

end

end TransformerIdentifiability.NLayer.NoSkip
