import AnyLayerIdentifiabilityProof.NLayer.NoSkip.FormalStreams
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Genericity.SignRegion

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.NoSkip

/-!
# The simultaneous first-layer dial

This is the no-skip version of TeX Definition `def:multi-dial-path` and the
exact part of Lemma `lem:multi-dial`.  In contrast to the old one-head dial,
only the repeated probe vector `v` moves.  The direction is the Gram right
inverse of the complete first-layer anchor map.
-/

noncomputable section

/-- The inverse coordinate of the real sigmoid on `(0,1)`. -/
noncomputable def multiDialLogit (t : Real) : Real :=
  Real.log (t / (1 - t))

/-- The no-skip multi-dial logit really is an inverse to `sig`. -/
theorem sig_multiDialLogit {t : Real} (ht0 : 0 < t) (ht1 : t < 1) :
    sig (multiDialLogit t) = t := by
  have hden : 0 < 1 - t := by linarith
  have hratio : 0 < t / (1 - t) := div_pos ht0 hden
  have htne : t ≠ 0 := ne_of_gt ht0
  have hdenne : 1 - t ≠ 0 := ne_of_gt hden
  rw [sig, multiDialLogit, Real.exp_neg, Real.exp_log hratio]
  field_simp [htne, hdenne]
  ring

/-- TeX `c_a = logit(t_a) - b`, with `b = log r`. -/
noncomputable def multiDialC (r : Nat) {k : Nat} (t : Fin k -> Real) :
    Fin k -> Real :=
  fun a => multiDialLogit (t a) - logScale r

/-- The Gram right inverse `Gamma(w)^T (Gamma(w) Gamma(w)^T)^-1`. -/
noncomputable def multiDialRightInverse {m k d : Nat}
    (theta : Params (m + 1) k d) (w : Vec d) :
    Matrix (Fin d) (Fin k) Real :=
  (anchorGradientMatrix theta w)ᵀ * (anchorGramMatrix theta w)⁻¹

/-- The simultaneous dial direction `y`, obtained by applying the Gram right
inverse to all `k` desired logit displacements at once. -/
noncomputable def multiDialDirection {m k d : Nat} (r : Nat)
    (theta : Params (m + 1) k d) (w : Vec d) (t : Fin k -> Real) : Vec d :=
  multiDialRightInverse theta w *ᵥ multiDialC r t

/-- A point of a concrete sign region, kept together with its membership
proof so all quadric and positivity facts are available downstream. -/
structure MultiDialBasePoint {n k d : Nat} {theta : Params (n + 1) k d}
    (D : MultiDialSignRegion theta) where
  point : MultiSignPoint d k
  mem : point ∈ D.region

namespace MultiDialBasePoint

variable {n k d : Nat} {theta : Params (n + 1) k d}
    {D : MultiDialSignRegion theta}

abbrev w (p : MultiDialBasePoint D) : Vec d := p.point.1.1
abbrev v (p : MultiDialBasePoint D) : Vec d := p.point.1.2
abbrev t (p : MultiDialBasePoint D) : Fin k -> Real := p.point.2

theorem anchor_eq_zero (p : MultiDialBasePoint D) (a : Fin k) :
    anchorRow theta p.w a p.v = 0 :=
  (D.region_subset_slab p.mem).1 a

theorem t_mem_Ioo (p : MultiDialBasePoint D) (a : Fin k) :
    p.t a ∈ Set.Ioo (0 : Real) 1 :=
  (D.region_subset_slab p.mem).2 a

theorem anchorGramDet_pos (p : MultiDialBasePoint D) :
    0 < anchorGramDet theta p.w :=
  D.anchorGramDet_pos p.mem

end MultiDialBasePoint

/-- The path `(w(tau),v(tau))=(w0,v0+tau^-1 y)`. -/
noncomputable def multiDialPath {m k d : Nat} (r : Nat)
    (theta : Params (m + 1) k d) (p : MultiSignPoint d k) (tau : Real) :
    Vec d × Vec d :=
  (p.1.1, p.1.2 + tau⁻¹ • multiDialDirection r theta p.1.1 p.2)

@[simp] theorem multiDialPath_fst {m k d : Nat} (r : Nat)
    (theta : Params (m + 1) k d) (p : MultiSignPoint d k) (tau : Real) :
    (multiDialPath r theta p tau).1 = p.1.1 :=
  rfl

@[simp] theorem multiDialPath_snd {m k d : Nat} (r : Nat)
    (theta : Params (m + 1) k d) (p : MultiSignPoint d k) (tau : Real) :
    (multiDialPath r theta p tau).2 =
      p.1.2 + tau⁻¹ • multiDialDirection r theta p.1.1 p.2 :=
  rfl

/-- Full row rank makes the displayed Gram matrix a genuine right inverse. -/
theorem anchorGradientMatrix_mulVec_multiDialDirection {m k d : Nat}
    (r : Nat) (theta : Params (m + 1) k d) (w : Vec d)
    (t : Fin k -> Real) (hgram : anchorGramDet theta w ≠ 0) :
    anchorGradientMatrix theta w *ᵥ multiDialDirection r theta w t =
      multiDialC r t := by
  have hunit : IsUnit (anchorGramMatrix theta w).det :=
    isUnit_iff_ne_zero.mpr (by simpa [anchorGramDet] using hgram)
  rw [multiDialDirection, multiDialRightInverse, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc]
  change (anchorGramMatrix theta w * (anchorGramMatrix theta w)⁻¹) *ᵥ
      multiDialC r t = multiDialC r t
  rw [Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]

/-- Each anchor row evaluates to its requested simultaneous logit shift on
the dial direction. -/
theorem anchorRow_multiDialDirection {m k d : Nat} (r : Nat)
    (theta : Params (m + 1) k d) (w : Vec d) (t : Fin k -> Real)
    (hgram : anchorGramDet theta w ≠ 0) (a : Fin k) :
    anchorRow theta w a (multiDialDirection r theta w t) = multiDialC r t a := by
  have h := congr_fun
    (anchorGradientMatrix_mulVec_multiDialDirection r theta w t hgram) a
  simpa [anchorGradientMatrix_mulVec] using h

/-- Along the path, every first-layer slope is exactly `c_a/tau`. -/
theorem anchorRow_multiDialPath {m k d : Nat} (r : Nat)
    (theta : Params (m + 1) k d) (p : MultiSignPoint d k)
    (hanchor : ∀ a, anchorRow theta p.1.1 a p.1.2 = 0)
    (hgram : anchorGramDet theta p.1.1 ≠ 0) (tau : Real) (a : Fin k) :
    anchorRow theta (multiDialPath r theta p tau).1 a
        (multiDialPath r theta p tau).2 = tau⁻¹ * multiDialC r p.2 a := by
  rw [multiDialPath_fst, multiDialPath_snd, anchorRow_add,
    hanchor, zero_add, anchorRow_smul,
    anchorRow_multiDialDirection r theta p.1.1 p.2 hgram]

/-- TeX Lemma `lem:multi-dial`(i), argument form. -/
theorem multiDial_exact_firstLayer_argument {m k d : Nat} (r : Nat)
    (theta : Params (m + 1) k d) (p : MultiSignPoint d k)
    (hanchor : ∀ a, anchorRow theta p.1.1 a p.1.2 = 0)
    (hgram : anchorGramDet theta p.1.1 ≠ 0) {tau : Real} (htau : tau ≠ 0)
    (a : Fin k) :
    tau * anchorRow theta (multiDialPath r theta p tau).1 a
        (multiDialPath r theta p tau).2 + logScale r =
      multiDialLogit (p.2 a) := by
  rw [anchorRow_multiDialPath r theta p hanchor hgram tau a]
  rw [← mul_assoc, mul_inv_cancel₀ htau, one_mul]
  simp only [multiDialC]
  ring

/-- The analytic recursion's first-layer slope is the anchor row, so the
simultaneous dial identity applies directly to `actualProbeSlope`. -/
theorem actualProbeSlope_firstLayer_multiDialPath {m k d : Nat} (r : Nat)
    (theta : Params (m + 1) k d) (p : MultiSignPoint d k)
    (tau : Real) (a : Fin k) :
    actualProbeSlope r theta (multiDialPath r theta p tau).1
        (multiDialPath r theta p tau).2 tau ⟨0, Nat.succ_pos m⟩ a =
      anchorRow theta (multiDialPath r theta p tau).1 a
        (multiDialPath r theta p tau).2 := by
  rfl

/-- TeX Lemma `lem:multi-dial`(i), gate form: all first-layer gates hit their
independent targets exactly, not merely asymptotically. -/
theorem actualProbeGate_firstLayer_multiDialPath {m k d : Nat} (r : Nat)
    (theta : Params (m + 1) k d) (p : MultiSignPoint d k)
    (hanchor : ∀ a, anchorRow theta p.1.1 a p.1.2 = 0)
    (hgram : anchorGramDet theta p.1.1 ≠ 0) {tau : Real} (htau : tau ≠ 0)
    (ht : ∀ a, p.2 a ∈ Set.Ioo (0 : Real) 1) (a : Fin k) :
    actualProbeGate r theta (multiDialPath r theta p tau).1
        (multiDialPath r theta p tau).2 tau ⟨0, Nat.succ_pos m⟩ a = p.2 a := by
  rw [actualProbeGate_eq_sig, actualProbeSlope_firstLayer_multiDialPath]
  rw [multiDial_exact_firstLayer_argument r theta p hanchor hgram htau a]
  exact sig_multiDialLogit (ht a).1 (ht a).2

/-- Region-packaged exact simultaneous dial. -/
theorem MultiDialBasePoint.firstLayer_gate_eq {n k d : Nat} (r : Nat)
    {theta : Params (n + 1) k d} {D : MultiDialSignRegion theta}
    (p : MultiDialBasePoint D) {tau : Real} (htau : tau ≠ 0) (a : Fin k) :
    actualProbeGate r theta (multiDialPath r theta p.point tau).1
        (multiDialPath r theta p.point tau).2 tau ⟨0, Nat.succ_pos n⟩ a = p.t a := by
  exact actualProbeGate_firstLayer_multiDialPath r theta p.point
    p.anchor_eq_zero p.anchorGramDet_pos.ne' htau p.t_mem_Ioo a

/-- First-layer gates are definitionally determined by their attention
matrices.  This is the small bridge from Step 1's paired attention equality to
the two exact dial identities. -/
theorem actualProbeGate_firstLayer_eq_of_attention_eq {m k d : Nat} (r : Nat)
    {theta theta' : Params (m + 1) k d} (w v : Vec d) (tau : Real)
    (hA : ∀ a, attentionMatrix theta 0 a = attentionMatrix theta' 0 a)
    (a : Fin k) :
    actualProbeGate r theta w v tau ⟨0, Nat.succ_pos m⟩ a =
      actualProbeGate r theta' w v tau ⟨0, Nat.succ_pos m⟩ a := by
  simp only [actualProbeGate_eq_sig, actualProbeSlope, actualProbePoint_zero]
  have hA0 :
      attentionMatrix theta ⟨0, Nat.succ_pos m⟩ a =
        attentionMatrix theta' ⟨0, Nat.succ_pos m⟩ a := by
    simpa only using hA a
  rw [hA0]

/-- Exact simultaneous tracking for a Step-1-paired source/target pair.  The
path is constructed from the target sign region; equality of first attentions
makes the source use the very same gates. -/
theorem MultiDialBasePoint.paired_firstLayer_gate_eq {n k d : Nat} (r : Nat)
    {theta theta' : Params (n + 1) k d} {D : MultiDialSignRegion theta'}
    (p : MultiDialBasePoint D)
    (hA : ∀ a, attentionMatrix theta 0 a = attentionMatrix theta' 0 a)
    {tau : Real} (htau : tau ≠ 0) (a : Fin k) :
    actualProbeGate r theta
          (multiDialPath r theta' p.point tau).1
          (multiDialPath r theta' p.point tau).2 tau
          ⟨0, Nat.succ_pos n⟩ a = p.t a ∧
      actualProbeGate r theta'
          (multiDialPath r theta' p.point tau).1
          (multiDialPath r theta' p.point tau).2 tau
          ⟨0, Nat.succ_pos n⟩ a = p.t a := by
  have htarget := p.firstLayer_gate_eq r htau a
  exact ⟨(actualProbeGate_firstLayer_eq_of_attention_eq r
    (multiDialPath r theta' p.point tau).1
    (multiDialPath r theta' p.point tau).2 tau hA a).trans htarget, htarget⟩

/-! ## Compact-uniform probe motion -/

theorem continuousAt_multiDialLogit {t : Real} (ht0 : 0 < t) (ht1 : t < 1) :
    ContinuousAt multiDialLogit t := by
  have hden : 1 - t ≠ 0 := ne_of_gt (sub_pos.mpr ht1)
  have hratio : t / (1 - t) ≠ 0 := div_ne_zero (ne_of_gt ht0) hden
  exact (continuousAt_id.div (continuousAt_const.sub continuousAt_id) hden).log hratio

theorem continuous_anchorGramMatrix {m k d : Nat}
    (theta : Params (m + 1) k d) :
    Continuous (fun w : Vec d => anchorGramMatrix theta w) := by
  unfold anchorGramMatrix anchorGradientMatrix anchorGradient
  fun_prop

private theorem continuousAt_finset_sum_ns {X ι : Type*} [TopologicalSpace X]
    {x : X} (s : Finset ι) (f : ι → X → Real)
    (hf : ∀ i ∈ s, ContinuousAt (f i) x) :
    ContinuousAt (fun y => ∑ i ∈ s, f i y) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (continuousAt_const : ContinuousAt (fun _ : X => (0 : Real)) x)
  | @insert a s ha ih =>
      simpa [Finset.sum_insert ha] using (hf a (by simp)).add
        (ih (fun i hi => hf i (by simp [hi])))

/-- The dial direction is continuous along the sign region.  The only inverse
is the anchor Gram inverse, whose determinant is strictly positive there; the
only logarithms are evaluated at dial coordinates in `(0,1)`. -/
theorem continuousOn_multiDialDirection_signRegion {n k d : Nat} (r : Nat)
    {theta : Params (n + 1) k d} (D : MultiDialSignRegion theta) :
    ContinuousOn
      (fun p : MultiSignPoint d k => multiDialDirection r theta p.1.1 p.2)
      D.region := by
  intro p hp
  have hpSlab := D.region_subset_slab hp
  have hdet : (anchorGramMatrix theta p.1.1).det ≠ 0 := by
    simpa [anchorGramDet] using (D.anchorGramDet_pos hp).ne'
  have hInvAt : ContinuousAt
      (fun q : MultiSignPoint d k => (anchorGramMatrix theta q.1.1)⁻¹) p :=
    by
      have hInvW : ContinuousAt
          (fun w : Vec d => (anchorGramMatrix theta w)⁻¹) p.1.1 := by
        have h := ContinuousAt.comp (f := anchorGramMatrix theta) (g := Inv.inv)
          (continuousAt_matrix_inv (anchorGramMatrix theta p.1.1)
            (by simpa [Ring.inverse] using (continuousAt_inv₀ hdet)))
          (continuous_anchorGramMatrix theta).continuousAt
        simpa [Function.comp_def] using h
      have h := ContinuousAt.comp (f := fun q : MultiSignPoint d k => q.1.1)
        (g := fun w : Vec d => (anchorGramMatrix theta w)⁻¹) hInvW
        (continuous_fst.comp continuous_fst).continuousAt
      simpa [Function.comp_def] using h
  have hCAt : ContinuousAt (fun q : MultiSignPoint d k => multiDialC r q.2) p := by
    apply continuousAt_pi.mpr
    intro a
    have htAt : ContinuousAt (fun q : MultiSignPoint d k => q.2 a) p :=
      ((continuous_apply a).comp continuous_snd).continuousAt
    have hlog := ContinuousAt.comp (f := fun q : MultiSignPoint d k => q.2 a)
      (g := multiDialLogit)
      (continuousAt_multiDialLogit (hpSlab.2 a).1 (hpSlab.2 a).2) htAt
    have hlog' : ContinuousAt
        (fun q : MultiSignPoint d k => multiDialLogit (q.2 a)) p := by
      simpa [Function.comp_def] using hlog
    exact hlog'.sub continuousAt_const
  have hInvCoord (a b : Fin k) : ContinuousAt
      (fun q : MultiSignPoint d k => (anchorGramMatrix theta q.1.1)⁻¹ a b) p := by
    have h := (((continuous_apply b).comp (continuous_apply a)).continuousAt).comp hInvAt
    simpa [Function.comp_def] using h
  have hCCoord (a : Fin k) : ContinuousAt
      (fun q : MultiSignPoint d k => multiDialC r q.2 a) p := by
    have h := (continuous_apply a).continuousAt.comp hCAt
    simpa [Function.comp_def] using h
  apply ContinuousAt.continuousWithinAt
  apply continuousAt_pi.mpr
  intro i
  simp only [multiDialDirection, multiDialRightInverse, Matrix.mulVec,
    dotProduct, Matrix.mul_apply, Matrix.transpose_apply]
  apply continuousAt_finset_sum_ns
  intro a _ha
  apply ContinuousAt.mul
  · apply continuousAt_finset_sum_ns
    intro b _hb
    have hgrad : ContinuousAt
        (fun q : MultiSignPoint d k => anchorGradientMatrix theta q.1.1 b i) p := by
      unfold anchorGradientMatrix anchorGradient
      fun_prop
    exact hgrad.mul (hInvCoord b a)
  · exact hCCoord a

/-- Compact sets of sign-region base points have a uniform bound on the Gram
right-inverse/logit direction. -/
theorem exists_uniform_multiDialDirection_bound {n k d : Nat} (r : Nat)
    {theta : Params (n + 1) k d} (D : MultiDialSignRegion theta)
    {K : Set (MultiSignPoint d k)} (hK : IsCompact K) (hKD : K ⊆ D.region) :
    ∃ C : Real, 0 ≤ C ∧ ∀ p ∈ K, ‖multiDialDirection r theta p.1.1 p.2‖ ≤ C := by
  have hcont : ContinuousOn
      (fun p : MultiSignPoint d k => ‖multiDialDirection r theta p.1.1 p.2‖) K :=
    continuous_norm.comp_continuousOn
      ((continuousOn_multiDialDirection_signRegion r D).mono hKD)
  have hbdd := hK.bddAbove_image hcont
  rcases hbdd with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro p hp
  exact le_trans (hC ⟨p, hp, rfl⟩) (le_max_left _ _)

/-- TeX Lemma `lem:multi-dial`(ii): over a compact subset of the sign region,
the moving probe satisfies the uniform `C/tau` bound. -/
theorem exists_uniform_multiDialPath_motion_bound {n k d : Nat} (r : Nat)
    {theta : Params (n + 1) k d} (D : MultiDialSignRegion theta)
    {K : Set (MultiSignPoint d k)} (hK : IsCompact K) (hKD : K ⊆ D.region) :
    ∃ C : Real, 0 ≤ C ∧ ∀ p ∈ K, ∀ tau : Real, 1 ≤ tau ->
      ‖(multiDialPath r theta p tau).2 - p.1.2‖ ≤ C / tau := by
  obtain ⟨C, hC0, hC⟩ := exists_uniform_multiDialDirection_bound r D hK hKD
  refine ⟨C, hC0, ?_⟩
  intro p hp tau htau
  have htau0 : 0 < tau := lt_of_lt_of_le zero_lt_one htau
  have hinv0 : 0 ≤ tau⁻¹ := inv_nonneg.mpr htau0.le
  calc
    ‖(multiDialPath r theta p tau).2 - p.1.2‖ =
        tau⁻¹ * ‖multiDialDirection r theta p.1.1 p.2‖ := by
          simp [multiDialPath, norm_smul, abs_of_pos htau0]
    _ ≤ tau⁻¹ * C := mul_le_mul_of_nonneg_left (hC p hp) hinv0
    _ = C / tau := by rw [div_eq_mul_inv, mul_comm]

end

end TransformerIdentifiability.NLayer.NoSkip
