import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Genericity.MultiDialCertificate

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer.NoSkip

/-!
# Headwise zero-tail dial certificate

The repaired proof keeps the existing `k*m` row matrix, but restricts its
first-layer tuple to `t e_h`.  The restriction is essential: each run lives on
one quadric and the runs are allowed to have unrelated deeper saturation
labels.
-/

/-- The tuple `t e_h`: head `h` has value `t` and every other head is zero. -/
def headwiseDialTuple {k : Nat} (h : Fin k) (t : Real) : Fin k → Real :=
  fun a => if a = h then t else 0

@[simp] theorem headwiseDialTuple_self {k : Nat} (h : Fin k) (t : Real) :
    headwiseDialTuple h t h = t := by
  simp [headwiseDialTuple]

@[simp] theorem headwiseDialTuple_of_ne {k : Nat} {h a : Fin k} (ha : a ≠ h)
    (t : Real) : headwiseDialTuple h t a = 0 := by
  simp [headwiseDialTuple, ha]

@[simp] theorem headwiseDialTuple_zero {k : Nat} (h : Fin k) :
    headwiseDialTuple h 0 = 0 := by
  funext a
  simp [headwiseDialTuple]

/-- Semantic form of the TeX headwise coefficient certificate.  For every
distinguished head, the restricted Gram polynomial has a nonzero evaluation. -/
def HeadwiseDialCertificate {n k d : Nat} (theta : Params (n + 1) k d) : Prop :=
  ∀ h : Fin k, ∃ t : Real, t ∈ Set.Ioo (0 : Real) 1 ∧ ∃ w : Vec d,
    multiDialGramDet theta (headwiseDialTuple h t) w ≠ 0

/-- The restricted numeric Gram determinant is continuous in the scalar dial. -/
theorem continuous_headwiseGramDet {n k d : Nat}
    (theta : Params (n + 1) k d) (h : Fin k) (w : Vec d) :
    Continuous fun t : Real =>
      multiDialGramDet theta (headwiseDialTuple h t) w := by
  have ht : Continuous fun t : Real => headwiseDialTuple h t := by
    rw [continuous_pi_iff]
    intro a
    by_cases ha : a = h
    · simpa [headwiseDialTuple, ha] using
        (continuous_id : Continuous fun t : Real => t)
    · simpa [headwiseDialTuple, ha] using
        (continuous_const : Continuous fun _t : Real => (0 : Real))
  have hD : Continuous fun t : Real =>
      dialValueMatrix theta (headwiseDialTuple h t) := by
    unfold dialValueMatrix
    fun_prop
  have hcontrast : Continuous fun t : Real =>
      dialContrast theta (headwiseDialTuple h t) w := by
    unfold dialContrast
    exact (continuous_const.sub hD).matrix_mulVec continuous_const
  have hG : Continuous fun t : Real =>
      multiDialGradientMatrix theta (headwiseDialTuple h t) w := by
    refine continuous_matrix ?_
    intro i row
    rcases row with a | jb
    · change Continuous fun _t : Real => anchorGradient theta w a i
      fun_prop
    · change Continuous fun t : Real =>
        (levelGradient theta (headwiseDialTuple h t) w jb) i
      unfold levelGradient
      exact (continuous_apply i).comp
        (continuous_const.matrix_mulVec
          (continuous_const.matrix_mulVec
            (continuous_const.matrix_mulVec hcontrast)))
  unfold multiDialGramDet multiDialGramMatrix
  exact (Continuous.matrix_mul hG.matrix_transpose hG).matrix_det

/-- A single nonzero evaluation at the zero tuple proves every headwise
restriction simultaneously.  This is the bridge used by the diagonal witness
and by the finite parameter-polynomial cover. -/
theorem headwiseDialCertificate_of_zero_gramDet {n k d : Nat}
    (theta : Params (n + 1) k d) (w : Vec d)
    (hdet : multiDialGramDet theta (0 : Fin k → Real) w ≠ 0) :
    HeadwiseDialCertificate theta := by
  intro h
  let f : Real → Real := fun t =>
    multiDialGramDet theta (headwiseDialTuple h t) w
  have hf : Continuous f := continuous_headwiseGramDet theta h w
  have hf0 : f 0 ≠ 0 := by simpa [f] using hdet
  have hopen : IsOpen {t : Real | f t ≠ 0} := by
    simpa [Set.preimage, Set.mem_compl_iff] using
      (isOpen_compl_singleton.preimage hf)
  obtain ⟨eps, heps, heps_sub⟩ := Metric.isOpen_iff.mp hopen 0 hf0
  let t : Real := min (eps / 2) (1 / 2)
  have ht0 : 0 < t := lt_min (half_pos heps) (by norm_num)
  have ht1 : t < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hdist : dist t 0 < eps := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht0]
    exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self heps)
  refine ⟨t, ⟨ht0, ht1⟩, w, ?_⟩
  exact heps_sub hdist

/-- The headwise certificate is vacuous when there are no heads. -/
theorem headwiseDialCertificate_of_k_zero {n d : Nat}
    (theta : Params (n + 1) 0 d) : HeadwiseDialCertificate theta := by
  intro h
  exact Fin.elim0 h

/-- Extract a concrete independent row family for one requested head. -/
theorem HeadwiseDialCertificate.exists_gramDet_ne_zero {n k d : Nat}
    {theta : Params (n + 1) k d} (hcert : HeadwiseDialCertificate theta)
    (h : Fin k) : ∃ t : Real, t ∈ Set.Ioo (0 : Real) 1 ∧ ∃ w : Vec d,
      multiDialGramDet theta (headwiseDialTuple h t) w ≠ 0 :=
  hcert h

end TransformerIdentifiability.NLayer.NoSkip
