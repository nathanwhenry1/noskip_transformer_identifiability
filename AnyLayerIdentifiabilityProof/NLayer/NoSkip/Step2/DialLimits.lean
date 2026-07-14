import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Step2.TrichotomyInstance
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Analytic.SelectedTop
import AnyLayerIdentifiabilityProof.NLayer.KHead.Step2.AlphaSlopeLipschitz
import AnyLayerIdentifiabilityProof.NLayer.Analytic.SigmoidTail

set_option autoImplicit false

open Matrix Filter
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.NoSkip

noncomputable section

/-! ## Continuous coefficients of the moving no-skip formal slope -/

/-- Coefficientwise continuity for a family of formal polynomials. -/
def ContinuousFormalCoeffs {X : Type*} [TopologicalSpace X] {L k : Nat}
    (P : X → FormalPoly L k) : Prop :=
  ∀ m : FormalVar L k →₀ Nat, Continuous (fun x ↦ MvPolynomial.coeff m (P x))

namespace ContinuousFormalCoeffs

variable {X : Type*} [TopologicalSpace X] {L k : Nat}

theorem const (p : FormalPoly L k) : ContinuousFormalCoeffs (fun _ : X ↦ p) :=
  fun _ ↦ continuous_const

theorem add {P Q : X → FormalPoly L k}
    (hP : ContinuousFormalCoeffs P) (hQ : ContinuousFormalCoeffs Q) :
    ContinuousFormalCoeffs (fun x ↦ P x + Q x) := by
  intro m
  simpa only [MvPolynomial.coeff_add] using (hP m).add (hQ m)

theorem sub {P Q : X → FormalPoly L k}
    (hP : ContinuousFormalCoeffs P) (hQ : ContinuousFormalCoeffs Q) :
    ContinuousFormalCoeffs (fun x ↦ P x - Q x) := by
  intro m
  simpa only [MvPolynomial.coeff_sub] using (hP m).sub (hQ m)

theorem mul {P Q : X → FormalPoly L k}
    (hP : ContinuousFormalCoeffs P) (hQ : ContinuousFormalCoeffs Q) :
    ContinuousFormalCoeffs (fun x ↦ P x * Q x) := by
  classical
  intro m
  simp only [MvPolynomial.coeff_mul]
  exact continuous_finsetSum _ fun x _ ↦ (hP x.1).mul (hQ x.2)

theorem fintype_sum {I : Type*} [Fintype I]
    (P : I → X → FormalPoly L k) (hP : ∀ i, ContinuousFormalCoeffs (P i)) :
    ContinuousFormalCoeffs (fun x ↦ ∑ i, P i x) := by
  classical
  intro m
  simp only [MvPolynomial.coeff_sum]
  exact continuous_finsetSum _ fun i _ ↦ hP i m

theorem C {f : X → Real} (hf : Continuous f) :
    ContinuousFormalCoeffs
      (fun x ↦ MvPolynomial.C (f x) : X → FormalPoly L k) := by
  classical
  intro m
  by_cases hm : (0 : FormalVar L k →₀ Nat) = m
  · simpa [MvPolynomial.coeff_C, hm] using hf
  · simpa [MvPolynomial.coeff_C, hm] using
      (continuous_const : Continuous (fun _ : X ↦ (0 : Real)))

end ContinuousFormalCoeffs

/-- Coefficientwise continuity for a formal-vector family. -/
def ContinuousFormalVecCoeffs {X : Type*} [TopologicalSpace X]
    {L k d : Nat} (V : X → FormalVec L k d) : Prop :=
  ∀ i : Fin d, ContinuousFormalCoeffs (fun x ↦ V x i)

namespace ContinuousFormalVecCoeffs

variable {X : Type*} [TopologicalSpace X] {L k d : Nat}

theorem add {U V : X → FormalVec L k d}
    (hU : ContinuousFormalVecCoeffs U) (hV : ContinuousFormalVecCoeffs V) :
    ContinuousFormalVecCoeffs (fun x ↦ U x + V x) :=
  fun i ↦ (hU i).add (hV i)

theorem matVecMulConst (M : Matrix (Fin d) (Fin d) (FormalPoly L k))
    {V : X → FormalVec L k d} (hV : ContinuousFormalVecCoeffs V) :
    ContinuousFormalVecCoeffs (fun x ↦ M *ᵥ V x) := by
  classical
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact ContinuousFormalCoeffs.fintype_sum
    (fun j x ↦ M i j * V x j)
    (fun j ↦ (ContinuousFormalCoeffs.const (M i j)).mul (hV j))

end ContinuousFormalVecCoeffs

/-- Every coefficient of the no-skip formal point varies continuously with
the two real probe vectors. -/
theorem continuousFormalVecCoeffs_formalPoint {L k d : Nat}
    (theta : Params L k d) : ∀ (N : Nat) (hN : N ≤ L),
      ContinuousFormalVecCoeffs
        (fun p : Vec d × Vec d ↦ (formalPoint theta p.1 p.2 N hN).1) ∧
      ContinuousFormalVecCoeffs
        (fun p : Vec d × Vec d ↦ (formalPoint theta p.1 p.2 N hN).2)
  | 0, _ => by
      constructor
      · intro i
        exact ContinuousFormalCoeffs.C
          (((continuous_apply i).comp continuous_fst))
      · intro i
        exact ContinuousFormalCoeffs.C
          (((continuous_apply i).comp continuous_snd))
  | N + 1, hN => by
      have prev := continuousFormalVecCoeffs_formalPoint theta N
        (Nat.le_of_succ_le hN)
      let l : Fin L := ⟨N, Nat.lt_of_succ_le hN⟩
      constructor
      · simpa only [formalPoint_succ, formalStepPoint, formalW, formalV] using
          ContinuousFormalVecCoeffs.matVecMulConst
            (formalCollapseMatrix theta l - formalGatedValueSum theta l) prev.1
      · simpa only [formalPoint_succ, formalStepPoint, formalW, formalV] using
          (ContinuousFormalVecCoeffs.matVecMulConst
              (formalCollapseMatrix theta l) prev.2).add
            (ContinuousFormalVecCoeffs.matVecMulConst
              (formalGatedValueSum theta l) prev.1)

/-- Every coefficient of the moving no-skip formal slope is continuous in the
probe pair. -/
theorem continuous_formalSlope_coeff {L k d : Nat}
    (theta : Params L k d) (l : Fin L) (a : Fin k)
    (m : FormalVar L k →₀ Nat) :
    Continuous (fun p : Vec d × Vec d ↦
      MvPolynomial.coeff m (formalSlope theta p.1 p.2 l a)) := by
  have hpoint := continuousFormalVecCoeffs_formalPoint theta l.1
    (Nat.le_of_lt l.2)
  have hW : ContinuousFormalVecCoeffs
      (fun p : Vec d × Vec d ↦ formalW theta p.1 p.2 l.1 (Nat.le_of_lt l.2)) :=
    hpoint.1
  have hV : ContinuousFormalVecCoeffs
      (fun p : Vec d × Vec d ↦ formalV theta p.1 p.2 l.1 (Nat.le_of_lt l.2)) :=
    hpoint.2
  have hAV := ContinuousFormalVecCoeffs.matVecMulConst
    (realMatrixToFormal (attentionMatrix theta l a)) hV
  have hsum : ContinuousFormalCoeffs
      (fun p : Vec d × Vec d ↦ ∑ i : Fin d,
        formalW theta p.1 p.2 l.1 (Nat.le_of_lt l.2) i *
          (realMatrixToFormal (attentionMatrix theta l a) *ᵥ
            formalV theta p.1 p.2 l.1 (Nat.le_of_lt l.2)) i) :=
    ContinuousFormalCoeffs.fintype_sum _ (fun i ↦ (hW i).mul (hAV i))
  simpa [formalSlope, formalBilin, dotProduct] using hsum m

/-! ## A compact-uniform finite polynomial telescope -/

/-- The formal variables from layers strictly before `q`, in a duplicate-free
finite processing list. -/
def formalVarsBelow (L k q : Nat) : List (FormalVar L k) :=
  ((List.finRange L).flatMap
    (fun l => (List.finRange k).map (fun a => (l, a)))).filter
      (fun x => decide (x.1.1 < q))

theorem mem_formalVarsBelow {L k q : Nat} (x : FormalVar L k) :
    x ∈ formalVarsBelow L k q ↔ x.1.1 < q := by
  unfold formalVarsBelow
  simp only [List.mem_filter, List.mem_flatMap, List.mem_map, List.mem_finRange,
    decide_eq_true_eq, true_and]
  constructor
  · rintro ⟨_, hx⟩
    exact hx
  · intro hx
    exact ⟨⟨x.1, x.2, rfl⟩, hx⟩

theorem nodup_formalVarsBelow (L k q : Nat) :
    (formalVarsBelow L k q).Nodup := by
  classical
  unfold formalVarsBelow
  apply List.Nodup.filter
  rw [List.nodup_flatMap]
  refine ⟨?_, ?_⟩
  · intro l _
    exact List.Nodup.map (fun a b hab => by simpa using hab) (List.nodup_finRange k)
  · exact (List.nodup_finRange L).imp (fun {l l'} hll' => by
      intro x hx hx'
      rw [List.mem_map] at hx hx'
      obtain ⟨a, _, ha⟩ := hx
      obtain ⟨a', _, ha'⟩ := hx'
      exact hll' (congrArg Prod.fst (ha.trans ha'.symm)))

/-- A support-independent slice bound, summed over the fixed degree-two
monomial box.  On the unit gate cube it dominates `realSliceLip`. -/
noncomputable def formalBoxSliceLip {L k : Nat} (p : FormalPoly L k)
    (x : FormalVar L k) : Real :=
  ∑ m ∈ KHead.formalMonomialBox L k,
    |MvPolynomial.coeff m p| * (m x : Real)

theorem realSliceLip_one_le_formalBoxSliceLip {L k : Nat}
    (p : FormalPoly L k) (x : FormalVar L k)
    (hsupp : p.support ⊆ KHead.formalMonomialBox L k) :
    KHead.realSliceLip p x (fun _ => 1) ≤ formalBoxSliceLip p x := by
  classical
  simp only [KHead.realSliceLip, formalBoxSliceLip]
  have hone (m : FormalVar L k →₀ Nat) :
      (((m x : Real) * (1 : Real) ^ (m x - 1)) *
        KHead.realSliceOffRadius x (fun _ => 1) m) = (m x : Real) := by
    simp [KHead.realSliceOffRadius]
  simp_rw [hone]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsupp (by
    intro m _ _
    exact mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))

/-- The fixed-box slice bound varies continuously with the probe pair. -/
theorem continuous_formalBoxSliceLip_formalSlope {L k d : Nat}
    (theta : Params L k d) (l : Fin L) (a : Fin k) (x : FormalVar L k) :
    Continuous (fun p : Vec d × Vec d =>
      formalBoxSliceLip (formalSlope theta p.1 p.2 l a) x) := by
  classical
  unfold formalBoxSliceLip
  exact continuous_finsetSum _ fun m _ =>
    (continuous_formalSlope_coeff theta l a m).abs.mul continuous_const

/-- Total unit-cube Lipschitz budget for every slope coordinate. -/
noncomputable def allSlopeBoxLip {L k d : Nat} (theta : Params L k d)
    (p : Vec d × Vec d) : Real :=
  ∑ l : Fin L, ∑ a : Fin k, ∑ x : FormalVar L k,
    formalBoxSliceLip (formalSlope theta p.1 p.2 l a) x

theorem continuous_allSlopeBoxLip {L k d : Nat} (theta : Params L k d) :
    Continuous (allSlopeBoxLip theta) := by
  classical
  unfold allSlopeBoxLip
  exact continuous_finsetSum _ fun l _ => continuous_finsetSum _ fun a _ =>
    continuous_finsetSum _ fun x _ =>
      continuous_formalBoxSliceLip_formalSlope theta l a x

theorem formalBoxSliceLip_nonneg {L k : Nat} (p : FormalPoly L k)
    (x : FormalVar L k) : 0 ≤ formalBoxSliceLip p x := by
  classical
  exact Finset.sum_nonneg fun m _ =>
    mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)

theorem formalBoxSliceLip_le_allSlopeBoxLip {L k d : Nat}
    (theta : Params L k d) (p : Vec d × Vec d)
    (l : Fin L) (a : Fin k) (x : FormalVar L k) :
    formalBoxSliceLip (formalSlope theta p.1 p.2 l a) x ≤
      allSlopeBoxLip theta p := by
  classical
  unfold allSlopeBoxLip
  exact le_trans
    (Finset.single_le_sum
      (fun y _ => formalBoxSliceLip_nonneg
        (formalSlope theta p.1 p.2 l a) y) (Finset.mem_univ x))
    (le_trans
      (Finset.single_le_sum
        (fun b _ => Finset.sum_nonneg fun y _ => formalBoxSliceLip_nonneg
          (formalSlope theta p.1 p.2 l b) y) (Finset.mem_univ a))
      (Finset.single_le_sum
        (fun j _ => Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun y _ =>
          formalBoxSliceLip_nonneg (formalSlope theta p.1 p.2 j b) y)
        (Finset.mem_univ l)))

theorem allSlopeBoxLip_nonneg {L k d : Nat} (theta : Params L k d)
    (p : Vec d × Vec d) : 0 ≤ allSlopeBoxLip theta p := by
  classical
  unfold allSlopeBoxLip
  exact Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun a _ =>
    Finset.sum_nonneg fun x _ =>
      formalBoxSliceLip_nonneg (formalSlope theta p.1 p.2 l a) x

/-- Changing all prior gate coordinates changes a formal slope by at most the
total fixed-box slice budget times the sum of coordinate changes. -/
theorem formalSlope_eval_sub_eval_le_telescope {L k d : Nat}
    (theta : Params L k d) (p : Vec d × Vec d) (l : Fin L) (a : Fin k)
    (live frozen : FormalAssignment L k)
    (hlive : ∀ x, |live x| ≤ 1) (hfrozen : ∀ x, |frozen x| ≤ 1) :
    |MvPolynomial.eval live (formalSlope theta p.1 p.2 l a) -
      MvPolynomial.eval frozen (formalSlope theta p.1 p.2 l a)| ≤
      (formalVarsBelow L k l.1).length * allSlopeBoxLip theta p *
        ∑ x ∈ (Finset.univ : Finset (FormalVar L k)),
          if x.1.1 < l.1 then |live x - frozen x| else 0 := by
  classical
  let vars := formalVarsBelow L k l.1
  let A : Nat → Real := fun q =>
    MvPolynomial.eval (tupleDialPrefixAssignment live frozen vars q)
      (formalSlope theta p.1 p.2 l a)
  have hstep : ∀ i : Nat, (hi : i < vars.length) →
      |A (i + 1) - A i| ≤
        allSlopeBoxLip theta p * |live (vars[i]'hi) - frozen (vars[i]'hi)| := by
    intro i hi
    have hnew : vars[i]'hi ∉ vars.take i :=
      KHead.getElem_not_mem_take_of_nodup (nodup_formalVarsBelow L k l.1) hi
    have hmem : vars[i]'hi ∈ vars.take (i + 1) := by
      rw [List.take_succ_eq_append_getElem hi]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    have hslice := KHead.eval_sub_eval_abs_le_realSliceLip
      (formalSlope theta p.1 p.2 l a) (vars[i]'hi) (fun _ => 1)
      (tupleDialPrefixAssignment live frozen vars (i + 1))
      (tupleDialPrefixAssignment live frozen vars i)
      (fun _ => zero_le_one)
      (fun x => by
        by_cases hx : x ∈ vars.take (i + 1)
        · rw [tupleDialPrefixAssignment_of_mem_take _ _ _ _ hx]
          exact hlive x
        · rw [tupleDialPrefixAssignment_of_not_mem_take _ _ _ _ hx]
          exact hfrozen x)
      (fun x => by
        by_cases hx : x ∈ vars.take i
        · rw [tupleDialPrefixAssignment_of_mem_take _ _ _ _ hx]
          exact hlive x
        · rw [tupleDialPrefixAssignment_of_not_mem_take _ _ _ _ hx]
          exact hfrozen x)
      (fun x hx => tupleDialPrefixAssignment_succ_eq_of_ne live frozen vars i hi hx)
    have hbox := realSliceLip_one_le_formalBoxSliceLip
      (formalSlope theta p.1 p.2 l a) (vars[i]'hi)
      (by
        intro m hm
        rw [KHead.mem_formalMonomialBox_iff]
        intro x
        have hdeg : MvPolynomial.degreeOf x (formalSlope theta p.1 p.2 l a) ≤ 2 :=
          formalSlope_blockDegree_two theta p.1 p.2 l a x
        exact (MvPolynomial.degreeOf_le_iff.mp hdeg) m hm)
    have hcoord :
        tupleDialPrefixAssignment live frozen vars (i + 1) (vars[i]'hi) -
          tupleDialPrefixAssignment live frozen vars i (vars[i]'hi) =
            live (vars[i]'hi) - frozen (vars[i]'hi) := by
      rw [tupleDialPrefixAssignment_of_mem_take _ _ _ _ hmem,
        tupleDialPrefixAssignment_of_not_mem_take _ _ _ _ hnew]
    rw [hcoord] at hslice
    exact hslice.trans (mul_le_mul_of_nonneg_right
      (hbox.trans (formalBoxSliceLip_le_allSlopeBoxLip theta p l a (vars[i]'hi)))
      (abs_nonneg _))
  let S : Real := ∑ x ∈ (Finset.univ : Finset (FormalVar L k)),
    if x.1.1 < l.1 then |live x - frozen x| else 0
  have hcoord_le : ∀ i : Nat, (hi : i < vars.length) →
      |live (vars[i]'hi) - frozen (vars[i]'hi)| ≤ S := by
    intro i hi
    have hlt : (vars[i]'hi).1.1 < l.1 :=
      (mem_formalVarsBelow (vars[i]'hi)).1 (List.getElem_mem hi)
    have hsingle := Finset.single_le_sum
      (s := (Finset.univ : Finset (FormalVar L k)))
      (f := fun x => if x.1.1 < l.1 then |live x - frozen x| else 0)
      (fun x _ => by positivity) (Finset.mem_univ (vars[i]'hi))
    simpa [S, hlt] using hsingle
  have hsum : |A vars.length - A 0| ≤
      (vars.length : Real) * (allSlopeBoxLip theta p * S) := by
    rw [← sum_range_forward_difference A vars.length]
    calc
      |∑ i ∈ Finset.range vars.length, (A (i + 1) - A i)| ≤
          ∑ i ∈ Finset.range vars.length, |A (i + 1) - A i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range vars.length,
          allSlopeBoxLip theta p * S := by
        refine Finset.sum_le_sum ?_
        intro i hi
        exact (hstep i (Finset.mem_range.mp hi)).trans
          (mul_le_mul_of_nonneg_left
            (hcoord_le i (Finset.mem_range.mp hi))
            (allSlopeBoxLip_nonneg theta p))
      _ = (vars.length : Real) * (allSlopeBoxLip theta p * S) := by simp
  have hA0 : A 0 = MvPolynomial.eval frozen
      (formalSlope theta p.1 p.2 l a) := by
    simp [A]
  have hAlen : A vars.length = MvPolynomial.eval live
      (formalSlope theta p.1 p.2 l a) := by
    apply MvPolynomial.eval₂_congr
    intro x m hxm hm
    have hxvar : x ∈ (formalSlope theta p.1 p.2 l a).vars := by
      rw [MvPolynomial.mem_vars_iff_mem_support]
      exact ⟨m, MvPolynomial.mem_support_iff.mpr hm, hxm⟩
    have hxlt : x.1.1 < l.1 :=
      formalSlope_dependsOnLayersBefore theta p.1 p.2 l a x hxvar
    exact tupleDialPrefixAssignment_length live frozen vars
      ((mem_formalVarsBelow x).2 hxlt)
  rw [hA0, hAlen] at hsum
  simpa only [vars, S, Nat.cast_ofNat, mul_assoc] using hsum

/-- The all-zero deeper trichotomy labelling used by the negative sign region. -/
def tupleZeroLabels : DeeperHead → TrichotomyLabel :=
  fun _ => KHead.TrichotomyLabel.zero

@[simp] theorem tupleDialFrozenFamily_zeroLabels_deeper {n k : Nat} (r : Nat)
    (t : Fin k → Real) (l : Fin (n + 1)) (a : Fin k) (hl : 0 < l.1) :
    tupleDialFrozenFamily r t tupleZeroLabels l a = 0 := by
  rw [tupleDialFrozenFamily_deeper r t tupleZeroLabels l a hl]
  rfl

/-- Freezing the complete first tuple and every deeper gate at zero gives
exactly the bounded zero-frozen prefix point used to define `levelRow`. -/
theorem frozenPoint_tupleZero_eq_zeroFrozenPrefixPoint {n k d : Nat}
    (r : Nat) (theta : Params (n + 1) k d) (t : Fin k → Real)
    (w v : Vec d) : ∀ (q : Nat) (hq : q ≤ n),
      frozenPoint theta (tupleDialFrozenFamily r t tupleZeroLabels) w v (q + 1)
          (Nat.succ_le_succ hq) =
        zeroFrozenPrefixPoint theta t w v q hq
  | 0, _ => by
      have hfirst :
          tupleDialFrozenFamily (n := n) r t tupleZeroLabels
              ⟨0, Nat.succ_pos n⟩ = t := by
        funext a
        exact tupleDialFrozenFamily_first r t tupleZeroLabels a
      apply Prod.ext
      · simp only [frozenPoint_succ, frozenPoint_zero, gatedEffectivePoint_fst,
          zeroFrozenPrefixPoint_zero]
        rw [hfirst]
        simp [dialContrast, dialValueMatrix, KHead.gatedValueSum]
      · simp only [frozenPoint_succ, frozenPoint_zero, gatedEffectivePoint_snd,
          zeroFrozenPrefixPoint_zero]
        rw [hfirst]
        simp [dialRepeated, dialValueMatrix, KHead.gatedValueSum]
  | q + 1, hq => by
      have hq' : q ≤ n := le_trans (Nat.le_succ q) hq
      rw [frozenPoint_succ,
        frozenPoint_tupleZero_eq_zeroFrozenPrefixPoint r theta t w v q hq']
      have hgate :
          tupleDialFrozenFamily r t tupleZeroLabels
              ⟨q + 1, Nat.lt_of_succ_le (Nat.succ_le_succ hq)⟩ =
            (fun _ => 0) := by
        funext a
        exact tupleDialFrozenFamily_zeroLabels_deeper r t _ a (Nat.succ_pos q)
      have hcollapse : collapseMatrix (Fin.tail theta) ⟨q, by omega⟩ =
          collapseMatrix theta ⟨q + 1, by omega⟩ := rfl
      apply Prod.ext
      · simp only [gatedEffectivePoint_fst, hgate, gatedValueSum_allZero,
          sub_zero, zeroFrozenPrefixPoint_fst, frozenP_succ,
          Matrix.mulVec_mulVec]
        rw [hcollapse]
      · simp only [gatedEffectivePoint_snd, hgate, gatedValueSum_allZero,
          zero_mulVec, add_zero, zeroFrozenPrefixPoint_snd, frozenP_succ,
          Matrix.mulVec_mulVec]
        rw [hcollapse]

/-- Evaluation of a deeper formal slope at `(t,0,…,0)` is its affine level
row. -/
theorem eval_formalSlope_tupleDialFrozenAssignment_zero {n k d : Nat}
    (r : Nat) (theta : Params (n + 1) k d) (t : Fin k → Real)
    (w v : Vec d) (jb : LevelRowIndex (n + 1) k) :
    MvPolynomial.eval (tupleDialFrozenAssignment r t tupleZeroLabels)
        (formalSlope theta w v (levelLayer jb) jb.2) =
      levelRow theta t w jb v := by
  rw [eval_formalSlope]
  have hp := eval_formalPoint_tupleDialFrozenAssignment r theta t tupleZeroLabels
    w v (levelLayer jb).1 (Nat.le_of_lt (levelLayer jb).2)
  have hq : (levelLayer jb).1 = levelPrefixDepth jb + 1 := rfl
  change matrixBilin (attentionMatrix theta (levelLayer jb) jb.2)
      (evalFormalVec (tupleDialFrozenAssignment r t tupleZeroLabels)
        (formalPoint theta w v (levelLayer jb).1
          (Nat.le_of_lt (levelLayer jb).2)).1)
      (evalFormalVec (tupleDialFrozenAssignment r t tupleZeroLabels)
        (formalPoint theta w v (levelLayer jb).1
          (Nat.le_of_lt (levelLayer jb).2)).2) = _
  rw [hp.1, hp.2]
  change matrixBilin (attentionMatrix theta (levelLayer jb) jb.2)
      (frozenPoint theta (tupleDialFrozenFamily r t tupleZeroLabels) w v
        (levelPrefixDepth jb + 1) _).1
      (frozenPoint theta (tupleDialFrozenFamily r t tupleZeroLabels) w v
        (levelPrefixDepth jb + 1) _).2 = _
  rw [frozenPoint_tupleZero_eq_zeroFrozenPrefixPoint r theta t w v
    (levelPrefixDepth jb) (levelPrefixDepth_le jb)]
  rfl

/-- The polynomial telescope has one finite Lipschitz budget, uniformly over
all compact-base multi-dial paths after `tau = 1`. -/
theorem exists_uniform_allSlopeBoxLip_multiDialPath {n k d : Nat} (r : Nat)
    {theta : Params (n + 1) k d} (D : MultiDialSignRegion theta)
    {K : Set (MultiSignPoint d k)} (hK : IsCompact K) (hKD : K ⊆ D.region) :
    ∃ B : Real, 0 ≤ B ∧ ∀ p ∈ K, ∀ tau : Real, 1 ≤ tau →
      allSlopeBoxLip theta (multiDialPath r theta p tau) ≤ B := by
  let S : Set (MultiSignPoint d k × Real) := K ×ˢ Set.Icc (0 : Real) 1
  let F : MultiSignPoint d k × Real → Vec d × Vec d := fun z =>
    (z.1.1.1, z.1.1.2 + z.2 • multiDialDirection r theta z.1.1.1 z.1.2)
  have hdir : ContinuousOn
      (fun z : MultiSignPoint d k × Real =>
        multiDialDirection r theta z.1.1.1 z.1.2) S :=
    (continuousOn_multiDialDirection_signRegion r D).comp continuousOn_fst
      (fun z hz => hKD hz.1)
  have hF : ContinuousOn F S := by
    apply ContinuousOn.prodMk
    · exact ((continuous_fst.comp continuous_fst).comp continuous_fst).continuousOn
    · exact (((continuous_snd.comp continuous_fst).comp continuous_fst).continuousOn).add
        (continuousOn_snd.smul hdir)
  have hSc : IsCompact S := hK.prod isCompact_Icc
  have hcont : ContinuousOn (fun z => allSlopeBoxLip theta (F z)) S :=
    (continuous_allSlopeBoxLip theta).comp_continuousOn hF
  have hbdd := hSc.bddAbove_image hcont
  rcases hbdd with ⟨B, hB⟩
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro p hp tau htau
  have htau0 : 0 < tau := lt_of_lt_of_le zero_lt_one htau
  have hinv : tau⁻¹ ∈ Set.Icc (0 : Real) 1 :=
    ⟨inv_nonneg.mpr htau0.le, (inv_le_one₀ htau0).2 htau⟩
  have hz : (p, tau⁻¹) ∈ S := ⟨hp, hinv⟩
  have heq : F (p, tau⁻¹) = multiDialPath r theta p tau := rfl
  rw [← heq]
  exact le_trans (hB ⟨(p, tau⁻¹), hz, rfl⟩) (le_max_left _ _)

/-- Compact bases also have a single bound for all affine level gradients. -/
theorem exists_uniform_levelGradient_bound {n k d : Nat}
    (theta : Params (n + 1) k d) {K : Set (MultiSignPoint d k)}
    (hK : IsCompact K) :
    ∃ G : Real, 0 ≤ G ∧ ∀ p ∈ K, ∀ jb : LevelRowIndex (n + 1) k,
      ‖levelGradient theta p.2 p.1.1 jb‖ ≤ G := by
  let g : MultiSignPoint d k → Real := fun p =>
    ∑ jb : LevelRowIndex (n + 1) k, ‖levelGradient theta p.2 p.1.1 jb‖
  have hg : Continuous g := by
    classical
    unfold g levelGradient dialContrast dialValueMatrix
    fun_prop
  have hbdd := hK.bddAbove_image hg.continuousOn
  rcases hbdd with ⟨G, hG⟩
  refine ⟨max G 0, le_max_right _ _, ?_⟩
  intro p hp jb
  have hsingle : ‖levelGradient theta p.2 p.1.1 jb‖ ≤ g p := by
    classical
    exact Finset.single_le_sum (fun i _ => norm_nonneg _)
      (Finset.mem_univ jb)
  exact le_trans hsingle (le_trans (hG ⟨p, hp, rfl⟩) (le_max_left _ _))

theorem abs_dotProduct_le_card_mul_norm {d : Nat} (x y : Vec d) :
    |dotProduct x y| ≤ (d : Real) * ‖x‖ * ‖y‖ := by
  simp only [dotProduct]
  calc
    |∑ i : Fin d, x i * y i| ≤ ∑ i : Fin d, |x i * y i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, ‖x‖ * ‖y‖ := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [abs_mul]
      exact mul_le_mul (norm_le_pi_norm x i) (norm_le_pi_norm y i)
        (abs_nonneg _) (norm_nonneg _)
    _ = (d : Real) * ‖x‖ * ‖y‖ := by simp [mul_assoc]

private theorem exists_uniform_levelRow_margin_aux {n k d : Nat}
    {theta : Params (n + 1) k d} (D : MultiDialSignRegion theta)
    {K : Set (MultiSignPoint d k)} (hK : IsCompact K) (hKne : K.Nonempty)
    (hKD : K ⊆ D.region) :
    ∃ eta : Real, 0 < eta ∧ ∀ p ∈ K, ∀ jb : LevelRowIndex (n + 1) k,
      levelRow theta p.2 p.1.1 jb p.1.2 ≤ -eta := by
  by_cases hk : k = 0
  · subst k
    exact ⟨1, zero_lt_one, fun _ _ jb => Fin.elim0 jb.2⟩
  by_cases hn : n = 0
  · subst n
    exact ⟨1, zero_lt_one, fun _ _ jb => Fin.elim0 jb.1⟩
  let S : Set Real := ⋃ jb : LevelRowIndex (n + 1) k,
    (fun p : MultiSignPoint d k ↦ levelRow theta p.2 p.1.1 jb p.1.2) '' K
  have hSc : IsCompact S := by
    apply isCompact_iUnion
    intro jb
    exact hK.image (continuous_multiSignLevelValue theta jb)
  have hSne : S.Nonempty := by
    rcases hKne with ⟨p, hp⟩
    let jb : LevelRowIndex (n + 1) k :=
      (⟨0, Nat.pos_of_ne_zero hn⟩, ⟨0, Nat.pos_of_ne_zero hk⟩)
    exact ⟨_, Set.mem_iUnion.2 ⟨jb, p, hp, rfl⟩⟩
  obtain ⟨M, hMS, hMmax⟩ := hSc.exists_isGreatest hSne
  have hMneg : M < 0 := by
    rcases Set.mem_iUnion.1 hMS with ⟨jb, p, hp, rfl⟩
    exact D.levelRow_neg (hKD hp) jb
  refine ⟨-M, by linarith, ?_⟩
  intro p hp jb
  simpa using hMmax (Set.mem_iUnion.2 ⟨jb, p, hp, rfl⟩)

private theorem actualProbeGate_le_exp_of_slope_le_neg_aux {L k d : Nat}
    (r : Nat) (theta : Params L k d) (w v : Vec d) (tau eta : Real)
    (l : Fin L) (a : Fin k) (htau : 0 ≤ tau)
    (hslope : actualProbeSlope r theta w v tau l a ≤ -eta) :
    actualProbeGate r theta w v tau l a ≤
      Real.exp (logScale r) * Real.exp (-eta * tau) := by
  rw [actualProbeGate_eq_sig]
  calc
    sig (tau * actualProbeSlope r theta w v tau l a + logScale r) ≤
        Real.exp (tau * actualProbeSlope r theta w v tau l a + logScale r) :=
      sig_le_exp _
    _ ≤ Real.exp (tau * (-eta) + logScale r) := by
      apply Real.exp_le_exp.mpr
      exact add_le_add (mul_le_mul_of_nonneg_left hslope htau) le_rfl
    _ = Real.exp (logScale r) * Real.exp (-eta * tau) := by
      rw [Real.exp_add]
      ring_nf

/-! ## Uniform negative slopes along the simultaneous dial -/

/-- TeX Lemma `lem:multi-dial`(iii): on a compact part of a negative
multi-sign region, every deeper target slope remains uniformly negative along
the simultaneous dial, with one threshold for all bases, layers, and heads. -/
theorem exists_uniform_multiDial_primed_slope_bound
    {n k d : Nat} (r : Nat) {theta : Params (n + 1) k d}
    (D : MultiDialSignRegion theta) {K : Set (MultiSignPoint d k)}
    (hK : IsCompact K) (hKne : K.Nonempty) (hKD : K ⊆ D.region) :
    ∃ eta T : Real, 0 < eta ∧ 1 ≤ T ∧
      ∀ p ∈ K, ∀ tau : Real, T ≤ tau → ∀ l : Fin (n + 1),
        l ≠ 0 → ∀ a : Fin k,
          actualProbeSlope r theta
            (multiDialPath r theta p tau).1 (multiDialPath r theta p tau).2
            tau l a ≤ -(eta / 2) := by
  obtain ⟨eta, heta, hmargin⟩ :=
    exists_uniform_levelRow_margin_aux D hK hKne hKD
  obtain ⟨C, hC, hmotion⟩ :=
    exists_uniform_multiDialPath_motion_bound r D hK hKD
  obtain ⟨B, hB, hLip⟩ :=
    exists_uniform_allSlopeBoxLip_multiDialPath r D hK hKD
  obtain ⟨G, hG, hgrad⟩ := exists_uniform_levelGradient_bound theta hK
  let N : Real := Fintype.card (FormalVar (n + 1) k)
  let E : Real := Real.exp (logScale r)
  let A : Real := N * B * (N * E)
  let H : Real := (d : Real) * G * C
  let err : Real → Real := fun tau =>
    A * Real.exp (-(eta / 2) * tau) + H * tau⁻¹
  have hhalf : 0 < eta / 2 := by linarith
  have hexp0 : Tendsto (fun tau : Real => Real.exp (-(eta / 2) * tau))
      atTop (nhds 0) := by
    have hs : Tendsto (fun tau : Real => (eta / 2) * tau) atTop atTop :=
      tendsto_id.const_mul_atTop hhalf
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp hs
    simpa only [neg_mul] using h
  have herr : Tendsto err atTop (nhds 0) := by
    simpa [err] using (hexp0.const_mul A).add
      ((tendsto_inv_atTop_zero ( 𝕜 := Real)).const_mul H)
  obtain ⟨T₀, hT₀⟩ := (Metric.tendsto_atTop.mp herr) (eta / 2) hhalf
  let T : Real := max 1 T₀
  have hTone : 1 ≤ T := le_max_left _ _
  refine ⟨eta, T, heta, hTone, ?_⟩
  intro p hp tau htau
  have htau1 : 1 ≤ tau := le_trans hTone htau
  have htau0 : 0 < tau := lt_of_lt_of_le zero_lt_one htau1
  have hT₀tau : T₀ ≤ tau := le_trans (le_max_right 1 T₀) htau
  have herrsmall : err tau < eta / 2 := by
    have hd := hT₀ tau hT₀tau
    rw [Real.dist_eq, sub_zero] at hd
    exact lt_of_le_of_lt (le_abs_self (err tau)) hd
  let live : FormalAssignment (n + 1) k :=
    actualProbeGateAssignment r theta
      (multiDialPath r theta p tau).1 (multiDialPath r theta p tau).2 tau
  let frozen : FormalAssignment (n + 1) k :=
    tupleDialFrozenAssignment r p.2 tupleZeroLabels
  have hlive : ∀ x, |live x| ≤ 1 := by
    intro x
    change |actualProbeGate r theta _ _ tau x.1 x.2| ≤ 1
    rw [actualProbeGate_eq_sig,
      abs_of_nonneg (sig_pos _).le]
    exact sig_le_one _
  have hfrozen : ∀ x, |frozen x| ≤ 1 := by
    rintro ⟨l, a⟩
    change |tupleDialFrozenFamily r p.2 tupleZeroLabels l a| ≤ 1
    by_cases hl0 : l.1 = 0
    · have hl : l = ⟨0, Nat.succ_pos n⟩ := Fin.ext (by simpa using hl0)
      subst l
      rw [tupleDialFrozenFamily_first, abs_of_pos ((D.region_subset_slab (hKD hp)).2 a).1]
      exact ((D.region_subset_slab (hKD hp)).2 a).2.le
    · rw [tupleDialFrozenFamily_zeroLabels_deeper r p.2 l a
          (Nat.pos_of_ne_zero hl0), abs_zero]
      exact zero_le_one
  suffices hcore : ∀ q : Nat, (hq : q < n) → ∀ a : Fin k,
      actualProbeSlope r theta (multiDialPath r theta p tau).1
        (multiDialPath r theta p tau).2 tau
          ⟨q + 1, Nat.succ_lt_succ hq⟩ a ≤
          -(eta / 2) by
    intro l hl a
    have hlpos : 0 < l.1 := Nat.pos_of_ne_zero (by
      intro h
      apply hl
      exact Fin.ext (by simpa using h))
    obtain ⟨q, hqeq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hlpos)
    have hq : q < n := by omega
    have hlq : l = (⟨q + 1, by omega⟩ : Fin (n + 1)) := Fin.ext hqeq
    rw [hlq]
    exact hcore q hq a
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
    intro hq a
    let lq : Fin (n + 1) := ⟨q + 1, by omega⟩
    let jb : LevelRowIndex (n + 1) k := (⟨q, hq⟩, a)
    have hfirstDiff : ∀ x : FormalVar (n + 1) k, x.1.1 = 0 →
        live x = frozen x := by
      rintro ⟨lx, b⟩ hx
      have hlx : lx = ⟨0, Nat.succ_pos n⟩ := Fin.ext (by simpa using hx)
      subst lx
      have hslab := D.region_subset_slab (hKD hp)
      have hb := actualProbeGate_firstLayer_multiDialPath r theta p hslab.1
        (D.anchorGramDet_pos (hKD hp)).ne' htau0.ne' hslab.2 b
      change actualProbeGate r theta _ _ tau ⟨0, Nat.succ_pos n⟩ b =
        tupleDialFrozenAssignment r p.2 tupleZeroLabels
          (⟨0, Nat.succ_pos n⟩, b)
      rw [hb, tupleDialFrozenAssignment_first]
    have hpriorGate : ∀ x : FormalVar (n + 1) k,
        0 < x.1.1 → x.1.1 < q + 1 →
        |live x - frozen x| ≤ E * Real.exp (-(eta / 2) * tau) := by
      rintro ⟨lx, b⟩ hlx hxq
      have hzero : frozen (lx, b) = 0 := by
        change tupleDialFrozenAssignment r p.2 tupleZeroLabels (lx, b) = 0
        rw [tupleDialFrozenAssignment_deeper r p.2 tupleZeroLabels lx b hlx]
        rfl
      change |actualProbeGate r theta _ _ tau lx b - frozen (lx, b)| ≤ _
      rw [hzero, sub_zero,
        abs_of_nonneg (by
          rw [actualProbeGate_eq_sig]
          exact (sig_pos _).le)]
      obtain ⟨u, hueq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hlx)
      have huq : u < q := by omega
      have hun : u < n := lt_trans huq hq
      have hs := ih u huq hun b
      have hlxu : lx = (⟨u + 1, by omega⟩ : Fin (n + 1)) := Fin.ext hueq
      rw [hlxu]
      have hg := actualProbeGate_le_exp_of_slope_le_neg_aux r theta
        (multiDialPath r theta p tau).1 (multiDialPath r theta p tau).2
        tau (eta / 2) ⟨u + 1, by omega⟩ b htau0.le hs
      simpa [E] using hg
    have hsum :
        (∑ x ∈ (Finset.univ : Finset (FormalVar (n + 1) k)),
          if x.1.1 < lq.1 then |live x - frozen x| else 0) ≤
        N * (E * Real.exp (-(eta / 2) * tau)) := by
      calc
        (∑ x ∈ (Finset.univ : Finset (FormalVar (n + 1) k)),
            if x.1.1 < lq.1 then |live x - frozen x| else 0) ≤
            ∑ _x ∈ (Finset.univ : Finset (FormalVar (n + 1) k)),
              E * Real.exp (-(eta / 2) * tau) := by
          refine Finset.sum_le_sum ?_
          intro x _
          by_cases hxl : x.1.1 < lq.1
          · rw [if_pos hxl]
            by_cases hx0 : x.1.1 = 0
            · rw [hfirstDiff x hx0, sub_self, abs_zero]
              positivity
            · exact hpriorGate x (Nat.pos_of_ne_zero hx0) (by simpa [lq] using hxl)
          · rw [if_neg hxl]
            positivity
        _ = N * (E * Real.exp (-(eta / 2) * tau)) := by
          simp [N]
    have htel := formalSlope_eval_sub_eval_le_telescope theta
      (multiDialPath r theta p tau) lq a live frozen hlive hfrozen
    have hlen : ((formalVarsBelow (n + 1) k lq.1).length : Real) ≤ N := by
      dsimp [N]
      exact_mod_cast (nodup_formalVarsBelow (n + 1) k lq.1).length_le_card
    have hpoly :
        |MvPolynomial.eval live
            (formalSlope theta (multiDialPath r theta p tau).1
              (multiDialPath r theta p tau).2 lq a) -
          MvPolynomial.eval frozen
            (formalSlope theta (multiDialPath r theta p tau).1
              (multiDialPath r theta p tau).2 lq a)| ≤
          A * Real.exp (-(eta / 2) * tau) := by
      calc
        _ ≤ ((formalVarsBelow (n + 1) k lq.1).length : Real) *
            allSlopeBoxLip theta (multiDialPath r theta p tau) *
              (∑ x ∈ (Finset.univ : Finset (FormalVar (n + 1) k)),
                if x.1.1 < lq.1 then |live x - frozen x| else 0) := htel
        _ ≤ N * B * (N * (E * Real.exp (-(eta / 2) * tau))) := by
          have hN : 0 ≤ N := by positivity
          have hP : 0 ≤ allSlopeBoxLip theta (multiDialPath r theta p tau) :=
            allSlopeBoxLip_nonneg theta _
          have hS : 0 ≤ (∑ x ∈ (Finset.univ : Finset (FormalVar (n + 1) k)),
              if x.1.1 < lq.1 then |live x - frozen x| else 0) := by positivity
          calc
            _ ≤ N * allSlopeBoxLip theta (multiDialPath r theta p tau) *
                (∑ x ∈ (Finset.univ : Finset (FormalVar (n + 1) k)),
                  if x.1.1 < lq.1 then |live x - frozen x| else 0) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hlen hP) hS
            _ ≤ N * B *
                (∑ x ∈ (Finset.univ : Finset (FormalVar (n + 1) k)),
                  if x.1.1 < lq.1 then |live x - frozen x| else 0) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (hLip p hp tau htau1) hN) hS
            _ ≤ N * B * (N * (E * Real.exp (-(eta / 2) * tau))) :=
              mul_le_mul_of_nonneg_left hsum (mul_nonneg hN hB)
        _ = A * Real.exp (-(eta / 2) * tau) := by
          simp [A]
          ring
    have hfrozenEval : MvPolynomial.eval frozen
        (formalSlope theta (multiDialPath r theta p tau).1
          (multiDialPath r theta p tau).2 lq a) =
        levelRow theta p.2 p.1.1 jb (multiDialPath r theta p tau).2 := by
      simpa [frozen, lq, jb] using
        (eval_formalSlope_tupleDialFrozenAssignment_zero r theta p.2
          (multiDialPath r theta p tau).1 (multiDialPath r theta p tau).2 jb)
    have hactualEval : MvPolynomial.eval live
        (formalSlope theta (multiDialPath r theta p tau).1
          (multiDialPath r theta p tau).2 lq a) =
        actualProbeSlope r theta (multiDialPath r theta p tau).1
          (multiDialPath r theta p tau).2 tau lq a := by
      exact eval_formalSlope_actualProbeGateAssignment r theta _ _ tau lq a
    have hmove :
        |levelRow theta p.2 p.1.1 jb (multiDialPath r theta p tau).2 -
          levelRow theta p.2 p.1.1 jb p.1.2| ≤ H * tau⁻¹ := by
      rw [levelRow_eq_dotProduct_add_constant,
        levelRow_eq_dotProduct_add_constant]
      have heq :
          dotProduct (levelGradient theta p.2 p.1.1 jb)
              (multiDialPath r theta p tau).2 + levelConstant theta p.2 p.1.1 jb -
            (dotProduct (levelGradient theta p.2 p.1.1 jb) p.1.2 +
              levelConstant theta p.2 p.1.1 jb) =
            dotProduct (levelGradient theta p.2 p.1.1 jb)
              ((multiDialPath r theta p tau).2 - p.1.2) := by
        calc
          _ = dotProduct (levelGradient theta p.2 p.1.1 jb)
                (multiDialPath r theta p tau).2 -
              dotProduct (levelGradient theta p.2 p.1.1 jb) p.1.2 := by ring
          _ = ∑ i : Fin d,
              (levelGradient theta p.2 p.1.1 jb i *
                  (multiDialPath r theta p tau).2 i -
                levelGradient theta p.2 p.1.1 jb i * p.1.2 i) := by
            simp only [dotProduct, Finset.sum_sub_distrib]
          _ = _ := by
            apply Finset.sum_congr rfl
            intro i _
            simp [Pi.sub_apply]
            ring
      rw [heq]
      calc
        |dotProduct (levelGradient theta p.2 p.1.1 jb)
            ((multiDialPath r theta p tau).2 - p.1.2)| ≤
            (d : Real) * ‖levelGradient theta p.2 p.1.1 jb‖ *
              ‖(multiDialPath r theta p tau).2 - p.1.2‖ :=
          abs_dotProduct_le_card_mul_norm _ _
        _ ≤ (d : Real) * G * (C / tau) := by
          have hd0 : 0 ≤ (d : Real) := by positivity
          have hdelta0 : 0 ≤ ‖(multiDialPath r theta p tau).2 - p.1.2‖ :=
            norm_nonneg _
          calc
            _ ≤ (d : Real) * G *
                ‖(multiDialPath r theta p tau).2 - p.1.2‖ :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (hgrad p hp jb) hd0) hdelta0
            _ ≤ (d : Real) * G * (C / tau) :=
              mul_le_mul_of_nonneg_left (hmotion p hp tau htau1)
                (mul_nonneg hd0 hG)
        _ = H * tau⁻¹ := by simp [H, div_eq_mul_inv]; ring
    have hbase := hmargin p hp jb
    rw [hactualEval, hfrozenEval] at hpoly
    have htotal :
        actualProbeSlope r theta (multiDialPath r theta p tau).1
            (multiDialPath r theta p tau).2 tau lq a ≤
          levelRow theta p.2 p.1.1 jb p.1.2 + err tau := by
      have h₁ := (le_abs_self
        (actualProbeSlope r theta (multiDialPath r theta p tau).1
          (multiDialPath r theta p tau).2 tau lq a -
            levelRow theta p.2 p.1.1 jb (multiDialPath r theta p tau).2)).trans hpoly
      have h₂ := (le_abs_self
        (levelRow theta p.2 p.1.1 jb (multiDialPath r theta p tau).2 -
          levelRow theta p.2 p.1.1 jb p.1.2)).trans hmove
      dsimp [err]
      calc
        actualProbeSlope r theta (multiDialPath r theta p tau).1
            (multiDialPath r theta p tau).2 tau lq a =
          levelRow theta p.2 p.1.1 jb p.1.2 +
            ((actualProbeSlope r theta (multiDialPath r theta p tau).1
                (multiDialPath r theta p tau).2 tau lq a -
              levelRow theta p.2 p.1.1 jb (multiDialPath r theta p tau).2) +
            (levelRow theta p.2 p.1.1 jb (multiDialPath r theta p tau).2 -
              levelRow theta p.2 p.1.1 jb p.1.2)) := by ring
        _ ≤ levelRow theta p.2 p.1.1 jb p.1.2 +
            (A * Real.exp (-(eta / 2) * tau) + H * tau⁻¹) :=
          by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left (add_le_add h₁ h₂)
                (levelRow theta p.2 p.1.1 jb p.1.2)
    have hfinal : actualProbeSlope r theta
        (multiDialPath r theta p tau).1 (multiDialPath r theta p tau).2
        tau lq a ≤ -(eta / 2) := by
      linarith
    simpa [lq] using hfinal

/-! ## Compact sign margin -/

/-- Compact subsets of the sign region have one strictly positive margin for
all deeper frozen slopes. -/
theorem exists_uniform_levelRow_margin {n k d : Nat}
    {theta : Params (n + 1) k d} (D : MultiDialSignRegion theta)
    {K : Set (MultiSignPoint d k)} (hK : IsCompact K) (hKne : K.Nonempty)
    (hKD : K ⊆ D.region) :
    ∃ eta : Real, 0 < eta ∧ ∀ p ∈ K, ∀ jb : LevelRowIndex (n + 1) k,
      levelRow theta p.2 p.1.1 jb p.1.2 ≤ -eta := by
  by_cases hk : k = 0
  · subst k
    refine ⟨1, zero_lt_one, ?_⟩
    intro p hp jb
    exact Fin.elim0 jb.2
  by_cases hn : n = 0
  · subst n
    refine ⟨1, zero_lt_one, ?_⟩
    intro p hp jb
    exact Fin.elim0 jb.1
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  let S : Set Real := ⋃ jb : LevelRowIndex (n + 1) k,
    (fun p : MultiSignPoint d k ↦ levelRow theta p.2 p.1.1 jb p.1.2) '' K
  have hSc : IsCompact S := by
    apply isCompact_iUnion
    intro jb
    exact hK.image (continuous_multiSignLevelValue theta jb)
  have hSne : S.Nonempty := by
    rcases hKne with ⟨p, hp⟩
    let jb : LevelRowIndex (n + 1) k :=
      (⟨0, by omega⟩, ⟨0, Nat.pos_of_ne_zero hk⟩)
    refine ⟨levelRow theta p.2 p.1.1 jb p.1.2, ?_⟩
    exact Set.mem_iUnion.2 ⟨jb, ⟨p, hp, rfl⟩⟩
  obtain ⟨M, hMS, hMmax⟩ := hSc.exists_isGreatest hSne
  have hMneg : M < 0 := by
    rcases Set.mem_iUnion.1 hMS with ⟨jb, p, hp, rfl⟩
    exact D.levelRow_neg (hKD hp) jb
  refine ⟨-M, by linarith, ?_⟩
  intro p hp jb
  have hmem : levelRow theta p.2 p.1.1 jb p.1.2 ∈ S :=
    Set.mem_iUnion.2 ⟨jb, ⟨p, hp, rfl⟩⟩
  simpa using hMmax hmem

/-! ## Negative slopes imply zero-saturation -/

/-- Pointwise exponential zero-tail bound used by NS117. -/
theorem actualProbeGate_le_exp_of_slope_le_neg {L k d : Nat}
    (r : Nat) (theta : Params L k d) (w v : Vec d) (tau eta : Real)
    (l : Fin L) (a : Fin k) (htau : 0 ≤ tau)
    (hslope : actualProbeSlope r theta w v tau l a ≤ -eta) :
    actualProbeGate r theta w v tau l a ≤
      Real.exp (logScale r) * Real.exp (-eta * tau) := by
  rw [actualProbeGate_eq_sig]
  calc
    sig (tau * actualProbeSlope r theta w v tau l a + logScale r)
        ≤ Real.exp (tau * actualProbeSlope r theta w v tau l a + logScale r) :=
      sig_le_exp _
    _ ≤ Real.exp (tau * (-eta) + logScale r) := by
      apply Real.exp_le_exp.mpr
      exact add_le_add (mul_le_mul_of_nonneg_left hslope htau) le_rfl
    _ = Real.exp (logScale r) * Real.exp (-eta * tau) := by
      rw [Real.exp_add]
      ring_nf

/-- Uniform-family form of the previous estimate. -/
theorem multiDial_primed_gate_exp_bound_of_slope_bound
    {n k d : Nat} (r : Nat) {theta : Params (n + 1) k d}
    {D : MultiDialSignRegion theta} {K : Set (MultiSignPoint d k)}
    (eta T : Real)
    (hslope : ∀ p ∈ K, ∀ tau : Real, T ≤ tau → ∀ l : Fin (n + 1),
      l ≠ 0 → ∀ a : Fin k,
      actualProbeSlope r theta
        (multiDialPath r theta p tau).1 (multiDialPath r theta p tau).2
        tau l a ≤ -(eta / 2))
    (p : MultiDialBasePoint D) (hp : p.point ∈ K)
    (tau : Real) (hT : max T 0 ≤ tau) (l : Fin (n + 1)) (hl : l ≠ 0)
    (a : Fin k) :
    actualProbeGate r theta
      (multiDialPath r theta p.point tau).1
      (multiDialPath r theta p.point tau).2 tau l a ≤
      Real.exp (logScale r) * Real.exp (-(eta / 2) * tau) := by
  apply actualProbeGate_le_exp_of_slope_le_neg r theta _ _ tau (eta / 2) l a
  · exact le_trans (le_max_right T 0) hT
  · exact hslope p.point hp tau (le_trans (le_max_left T 0) hT) l hl a

/-- TeX Lemma `lem:multi-dial`(iv), compact-uniform existential form.  Every
deeper target gate converges to zero with the common exponential envelope
coming from the slope margin. -/
theorem exists_uniform_multiDial_primed_zero_saturation
    {n k d : Nat} (r : Nat) {theta : Params (n + 1) k d}
    (D : MultiDialSignRegion theta) {K : Set (MultiSignPoint d k)}
    (hK : IsCompact K) (hKne : K.Nonempty) (hKD : K ⊆ D.region) :
    ∃ eta T : Real, 0 < eta ∧ 1 ≤ T ∧
      ∀ p ∈ K, ∀ tau : Real, T ≤ tau → ∀ l : Fin (n + 1),
        l ≠ 0 → ∀ a : Fin k,
          actualProbeGate r theta
            (multiDialPath r theta p tau).1 (multiDialPath r theta p tau).2
            tau l a ≤
              Real.exp (logScale r) * Real.exp (-(eta / 2) * tau) := by
  obtain ⟨eta, T, heta, hT, hslope⟩ :=
    exists_uniform_multiDial_primed_slope_bound r D hK hKne hKD
  refine ⟨eta, T, heta, hT, ?_⟩
  intro p hp tau htau l hl a
  let bp : MultiDialBasePoint D := ⟨p, hKD hp⟩
  have hmax : max T 0 ≤ tau := by
    rw [max_eq_left (le_trans zero_le_one hT)]
    exact htau
  exact multiDial_primed_gate_exp_bound_of_slope_bound r eta T hslope
    bp hp tau hmax l hl a

end
end TransformerIdentifiability.NLayer.NoSkip
