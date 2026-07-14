import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.FormalPolySplit
import AnyLayerIdentifiabilityProof.NLayer.IDL.CascadeAlphaError

set_option autoImplicit false

open scoped BigOperators
open Matrix

namespace TransformerIdentifiability.NLayer.KHead

/-!
# α-branch slope Lipschitz control (K-head)

This file supplies the analytic ingredients for the α-branch delta of packet K07B lane L2:

* a **real** one-coordinate polynomial slice-Lipschitz inequality, generic over any finite
  index type (the K-head formal-slope polynomial `formalSlope θ w v l a` lives in
  `MvPolynomial (FormalVar (m+1) k) ℝ`, indexed by `FormalVar`, so we port the k=1
  `CascadeAlphaError` machinery from `MvPolynomial (Fin K) ℂ` to this real, `FormalVar`-indexed
  setting rather than reindexing);
* τ-uniform (eventual) boundedness of the coefficients of `formalSlope θ (path τ).1 (path τ).2 l a`
  along a bounded probe path, hence eventual boundedness of the slice-Lipschitz constant.

Together these turn the abstract `hLip` hypothesis of `TrichotomyInstance` into a genuine fact:
`TrichotomyInstance` combines them with the concrete dial gates and the finite variable box.
-/

/-! ## A generic real one-coordinate polynomial slice-Lipschitz constant -/

section GenericSlice

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Product of the box radii for every coordinate except the active slice coordinate. -/
noncomputable def realSliceOffRadius (coord : σ) (R : σ → ℝ) (m : σ →₀ Nat) : ℝ :=
  ∏ j ∈ (Finset.univ.erase coord), R j ^ m j

theorem realSliceOffRadius_nonneg (coord : σ) (R : σ → ℝ) (m : σ →₀ Nat)
    (hR : ∀ j, 0 ≤ R j) : 0 ≤ realSliceOffRadius coord R m :=
  Finset.prod_nonneg (fun j _ => pow_nonneg (hR j) (m j))

theorem realSlice_off_prod_le (coord : σ) (R x : σ → ℝ) (m : σ →₀ Nat)
    (hR : ∀ j, 0 ≤ R j) (hx : ∀ j, |x j| ≤ R j) :
    |∏ j ∈ m.support.erase coord, x j ^ m j| ≤ realSliceOffRadius coord R m := by
  rw [Finset.abs_prod]
  have hprod_le :
      (∏ j ∈ m.support.erase coord, |x j ^ m j|) ≤
        ∏ j ∈ m.support.erase coord, R j ^ m j := by
    refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) ?_
    intro j _hj
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg (x j)) (hx j) (m j)
  have hsubset : m.support.erase coord ⊆ Finset.univ.erase coord := by
    intro j hj
    rw [Finset.mem_erase] at hj ⊢
    exact ⟨hj.1, Finset.mem_univ j⟩
  have hprod_eq :
      (∏ j ∈ m.support.erase coord, R j ^ m j) =
        ∏ j ∈ Finset.univ.erase coord, R j ^ m j := by
    refine Finset.prod_subset hsubset ?_
    intro j hjbig hjsmall
    have hj_not_support : j ∉ m.support := by
      intro hjsupp
      exact hjsmall (by
        rw [Finset.mem_erase]
        rw [Finset.mem_erase] at hjbig
        exact ⟨hjbig.1, hjsupp⟩)
    have hmj : m j = 0 := by
      by_contra hne
      exact hj_not_support ((Finsupp.mem_support_iff).mpr hne)
    simp [hmj]
  exact hprod_le.trans_eq hprod_eq

/-- A single monomial is Lipschitz in one real coordinate on a coordinate box. -/
theorem monomial_prod_diff_abs_le (coord : σ) (R x y : σ → ℝ) (m : σ →₀ Nat)
    (hR : ∀ j, 0 ≤ R j) (hx : ∀ j, |x j| ≤ R j) (hy : ∀ j, |y j| ≤ R j)
    (heq : ∀ j, j ≠ coord → x j = y j) :
    |(∏ j ∈ m.support, x j ^ m j) - (∏ j ∈ m.support, y j ^ m j)| ≤
      (((m coord : ℝ) * R coord ^ (m coord - 1)) * realSliceOffRadius coord R m) *
        |x coord - y coord| := by
  by_cases hcoord : coord ∈ m.support
  · have hxprod :
        (∏ j ∈ m.support, x j ^ m j) =
          x coord ^ m coord * ∏ j ∈ m.support.erase coord, x j ^ m j := by
      rw [Finset.mul_prod_erase m.support (fun j => x j ^ m j) hcoord]
    have hyprod :
        (∏ j ∈ m.support, y j ^ m j) =
          y coord ^ m coord * ∏ j ∈ m.support.erase coord, y j ^ m j := by
      rw [Finset.mul_prod_erase m.support (fun j => y j ^ m j) hcoord]
    have hoffeq :
        (∏ j ∈ m.support.erase coord, x j ^ m j) =
          ∏ j ∈ m.support.erase coord, y j ^ m j := by
      refine Finset.prod_congr rfl ?_
      intro j hj
      rw [Finset.mem_erase] at hj
      rw [heq j hj.1]
    rw [hxprod, hyprod, ← hoffeq, ← sub_mul, abs_mul]
    have hmax_nonneg : 0 ≤ max |x coord| |y coord| :=
      le_max_of_le_left (abs_nonneg (x coord))
    have hmax_le : max |x coord| |y coord| ≤ R coord :=
      max_le (hx coord) (hy coord)
    have hpowBound :
        |x coord ^ m coord - y coord ^ m coord| ≤
          |x coord - y coord| * (m coord : ℝ) * R coord ^ (m coord - 1) := by
      have hbase := abs_pow_sub_pow_le (x coord) (y coord) (m coord)
      have hpowR :
          max |x coord| |y coord| ^ (m coord - 1) ≤ R coord ^ (m coord - 1) :=
        pow_le_pow_left₀ hmax_nonneg hmax_le (m coord - 1)
      exact hbase.trans (mul_le_mul_of_nonneg_left hpowR
        (mul_nonneg (abs_nonneg (x coord - y coord)) (Nat.cast_nonneg (m coord))))
    have hoffBound := realSlice_off_prod_le coord R x m hR hx
    have hpowBound_nonneg :
        0 ≤ |x coord - y coord| * (m coord : ℝ) * R coord ^ (m coord - 1) :=
      mul_nonneg
        (mul_nonneg (abs_nonneg (x coord - y coord)) (Nat.cast_nonneg (m coord)))
        (pow_nonneg (hR coord) (m coord - 1))
    calc
      |x coord ^ m coord - y coord ^ m coord| *
          |∏ j ∈ m.support.erase coord, x j ^ m j|
          ≤ (|x coord - y coord| * (m coord : ℝ) * R coord ^ (m coord - 1)) *
              realSliceOffRadius coord R m :=
            mul_le_mul hpowBound hoffBound (abs_nonneg _) hpowBound_nonneg
      _ = (((m coord : ℝ) * R coord ^ (m coord - 1)) * realSliceOffRadius coord R m) *
            |x coord - y coord| := by ring
  · have hprod_eq :
        (∏ j ∈ m.support, x j ^ m j) = ∏ j ∈ m.support, y j ^ m j := by
      refine Finset.prod_congr rfl ?_
      intro j hj
      have hji : j ≠ coord := by intro h; subst h; exact hcoord hj
      rw [heq j hji]
    rw [hprod_eq, sub_self, abs_zero]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (Nat.cast_nonneg (m coord)) (pow_nonneg (hR coord) (m coord - 1)))
        (realSliceOffRadius_nonneg coord R m hR))
      (abs_nonneg (x coord - y coord))

/-- Explicit coefficient-sum Lipschitz constant for changing one real coordinate of a finite
multivariate real polynomial on the real box `|x_j| ≤ R_j`. -/
noncomputable def realSliceLip (p : MvPolynomial σ ℝ) (coord : σ) (R : σ → ℝ) : ℝ :=
  ∑ m ∈ p.support,
    |MvPolynomial.coeff m p| *
      (((m coord : ℝ) * R coord ^ (m coord - 1)) * realSliceOffRadius coord R m)

theorem realSliceLip_nonneg (p : MvPolynomial σ ℝ) (coord : σ) (R : σ → ℝ)
    (hR : ∀ j, 0 ≤ R j) : 0 ≤ realSliceLip p coord R :=
  Finset.sum_nonneg (fun m _ =>
    mul_nonneg (abs_nonneg _)
      (mul_nonneg
        (mul_nonneg (Nat.cast_nonneg (m coord)) (pow_nonneg (hR coord) (m coord - 1)))
        (realSliceOffRadius_nonneg coord R m hR)))

/-- Finite-support real polynomial Lipschitz bound for one coordinate. -/
theorem eval_sub_eval_abs_le_realSliceLip (p : MvPolynomial σ ℝ) (coord : σ)
    (R x y : σ → ℝ) (hR : ∀ j, 0 ≤ R j) (hx : ∀ j, |x j| ≤ R j) (hy : ∀ j, |y j| ≤ R j)
    (heq : ∀ j, j ≠ coord → x j = y j) :
    |MvPolynomial.eval x p - MvPolynomial.eval y p| ≤
      realSliceLip p coord R * |x coord - y coord| := by
  have hdiff :
      MvPolynomial.eval x p - MvPolynomial.eval y p =
        ∑ m ∈ p.support,
          MvPolynomial.coeff m p *
            ((∏ j ∈ m.support, x j ^ m j) - (∏ j ∈ m.support, y j ^ m j)) := by
    rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro m _hm
    ring
  rw [hdiff]
  calc
    |∑ m ∈ p.support,
        MvPolynomial.coeff m p *
          ((∏ j ∈ m.support, x j ^ m j) - ∏ j ∈ m.support, y j ^ m j)|
        ≤ ∑ m ∈ p.support,
            |MvPolynomial.coeff m p *
              ((∏ j ∈ m.support, x j ^ m j) - ∏ j ∈ m.support, y j ^ m j)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ p.support,
          (|MvPolynomial.coeff m p| *
            (((m coord : ℝ) * R coord ^ (m coord - 1)) * realSliceOffRadius coord R m)) *
            |x coord - y coord| := by
          refine Finset.sum_le_sum ?_
          intro m _hm
          rw [abs_mul]
          have hmon := monomial_prod_diff_abs_le coord R x y m hR hx hy heq
          calc
            |MvPolynomial.coeff m p| *
                |(∏ j ∈ m.support, x j ^ m j) - ∏ j ∈ m.support, y j ^ m j|
                ≤ |MvPolynomial.coeff m p| *
                    ((((m coord : ℝ) * R coord ^ (m coord - 1)) *
                        realSliceOffRadius coord R m) * |x coord - y coord|) :=
                  mul_le_mul_of_nonneg_left hmon (abs_nonneg _)
            _ = (|MvPolynomial.coeff m p| *
                  (((m coord : ℝ) * R coord ^ (m coord - 1)) *
                    realSliceOffRadius coord R m)) * |x coord - y coord| := by ring
    _ = realSliceLip p coord R * |x coord - y coord| := by
          rw [realSliceLip, Finset.sum_mul]

end GenericSlice

/-! ## A generic list helper: a `Nodup` list element is missing from its own prefix -/

theorem getElem_not_mem_take_of_nodup {α : Type*} {vars : List α} (hnd : vars.Nodup)
    {i : Nat} (hi : i < vars.length) : vars[i]'hi ∉ vars.take i := by
  have hsub : (vars.take (i + 1)).Nodup := hnd.sublist (List.take_sublist (i + 1) vars)
  rw [List.take_succ_eq_append_getElem hi] at hsub
  have hdisj := List.disjoint_of_nodup_append hsub
  intro hmem
  exact hdisj hmem (List.mem_singleton_self _)

/-! ## Eventual boundedness of the coefficients of a τ-family of formal polynomials -/

section FormalCoeffs

variable {L k : Nat}

/-- Along-path eventual coefficient boundedness of a τ-family of K-head formal polynomials. -/
def EBFormalCoeffs (P : ℝ → FormalPoly L k) : Type :=
  ∀ m : FormalVar L k →₀ Nat, EventuallyBoundedReal (fun τ => MvPolynomial.coeff m (P τ))

namespace EBFormalCoeffs

noncomputable def const (p : FormalPoly L k) : EBFormalCoeffs (fun _ : ℝ => p) :=
  fun m => EventuallyBoundedReal.const (MvPolynomial.coeff m p)

noncomputable def congr {P Q : ℝ → FormalPoly L k} (h : EBFormalCoeffs P)
    (hPQ : ∀ τ, P τ = Q τ) : EBFormalCoeffs Q :=
  fun m => (h m).congr_of_forall_eq (fun τ => by rw [hPQ τ])

noncomputable def add {P Q : ℝ → FormalPoly L k} (hP : EBFormalCoeffs P)
    (hQ : EBFormalCoeffs Q) : EBFormalCoeffs (fun τ => P τ + Q τ) :=
  fun m => ((hP m).add (hQ m)).congr_of_forall_eq (fun τ => by rw [MvPolynomial.coeff_add])

noncomputable def sub {P Q : ℝ → FormalPoly L k} (hP : EBFormalCoeffs P)
    (hQ : EBFormalCoeffs Q) : EBFormalCoeffs (fun τ => P τ - Q τ) :=
  fun m => ((hP m).sub (hQ m)).congr_of_forall_eq (fun τ => by rw [MvPolynomial.coeff_sub])

noncomputable def mul {P Q : ℝ → FormalPoly L k} (hP : EBFormalCoeffs P)
    (hQ : EBFormalCoeffs Q) : EBFormalCoeffs (fun τ => P τ * Q τ) := by
  classical
  intro m
  let term : {x // x ∈ Finset.antidiagonal m} → ℝ → ℝ :=
    fun x τ => MvPolynomial.coeff x.1.1 (P τ) * MvPolynomial.coeff x.1.2 (Q τ)
  have hterm : ∀ x : {x // x ∈ Finset.antidiagonal m}, EventuallyBoundedReal (term x) :=
    fun x => (hP x.1.1).mul (hQ x.1.2)
  have hsum :
      EventuallyBoundedReal
        (fun τ => ∑ x : {x // x ∈ Finset.antidiagonal m}, term x τ) :=
    EventuallyBoundedReal.fintype_sum term hterm
  exact hsum.congr_of_forall_eq (by
    intro τ
    symm
    rw [MvPolynomial.coeff_mul]
    exact Finset.sum_subtype (s := Finset.antidiagonal m) (h := fun x => Iff.rfl)
      (f := fun x => MvPolynomial.coeff x.1 (P τ) * MvPolynomial.coeff x.2 (Q τ)))

noncomputable def fintype_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι → ℝ → FormalPoly L k) (hP : ∀ i : ι, EBFormalCoeffs (P i)) :
    EBFormalCoeffs (fun τ => ∑ i : ι, P i τ) := by
  intro m
  have hsum :
      EventuallyBoundedReal (fun τ => ∑ i : ι, MvPolynomial.coeff m (P i τ)) :=
    EventuallyBoundedReal.fintype_sum (fun i τ => MvPolynomial.coeff m (P i τ))
      (fun i => hP i m)
  exact hsum.congr_of_forall_eq (by intro τ; rw [MvPolynomial.coeff_sum])

noncomputable def C_ofReal {f : ℝ → ℝ} (hf : EventuallyBoundedReal f) :
    EBFormalCoeffs (fun τ => MvPolynomial.C (σ := FormalVar L k) (f τ)) := by
  classical
  intro m
  by_cases hm : (0 : FormalVar L k →₀ Nat) = m
  · exact hf.congr_of_forall_eq (fun τ => by simp [MvPolynomial.coeff_C, hm])
  · exact (EventuallyBoundedReal.const 0).congr_of_forall_eq
      (fun τ => by simp [MvPolynomial.coeff_C, hm])

end EBFormalCoeffs

/-- Along-path eventual coefficient boundedness of a τ-family of formal polynomial vectors. -/
def EBFormalVecCoeffs {d : Nat} (v : ℝ → FormalVec L k d) : Type :=
  ∀ i : Fin d, EBFormalCoeffs (fun τ => v τ i)

namespace EBFormalVecCoeffs

noncomputable def congr {d : Nat} {u v : ℝ → FormalVec L k d} (h : EBFormalVecCoeffs u)
    (huv : ∀ τ, u τ = v τ) : EBFormalVecCoeffs v :=
  fun i => (h i).congr (fun τ => by rw [huv τ])

noncomputable def add {d : Nat} {u v : ℝ → FormalVec L k d} (hu : EBFormalVecCoeffs u)
    (hv : EBFormalVecCoeffs v) : EBFormalVecCoeffs (fun τ => u τ + v τ) :=
  fun i => ((hu i).add (hv i)).congr (fun τ => by simp)

noncomputable def matVecMulConst {d : Nat} (M : Matrix (Fin d) (Fin d) (FormalPoly L k))
    {x : ℝ → FormalVec L k d} (hx : EBFormalVecCoeffs x) :
    EBFormalVecCoeffs (fun τ => M *ᵥ x τ) := by
  classical
  intro i
  have hsum :
      EBFormalCoeffs (fun τ => ∑ j : Fin d, M i j * x τ j) :=
    EBFormalCoeffs.fintype_sum (fun j τ => M i j * x τ j)
      (fun j => (EBFormalCoeffs.const (M i j)).mul (hx j))
  exact hsum.congr (fun τ => by simp [Matrix.mulVec, dotProduct])

end EBFormalVecCoeffs

variable {d : Nat}

/-- Coefficients of the formal `(w, v)` streams are eventually bounded along a bounded probe
path (the matrices in the recursion are τ-independent constants, so the τ-dependence enters
only through the bounded base vectors). -/
noncomputable def EBFormalVecCoeffs_formalPoint_of_path (θ : Params L k d)
    {path : ℝ → ProbePair d} (hpath : EventuallyBoundedProbePair path) :
    (n : Nat) → (hn : n ≤ L) →
      EBFormalVecCoeffs (fun τ => (formalPoint θ (path τ).1 (path τ).2 n hn).1) ×
        EBFormalVecCoeffs (fun τ => (formalPoint θ (path τ).1 (path τ).2 n hn).2)
  | 0, _hn => by
      refine ⟨?_, ?_⟩
      · exact fun i => (EBFormalCoeffs.C_ofReal (hpath.fst i)).congr (fun τ => by
          simp [formalPoint, realVecToFormal, formalConst])
      · exact fun i => (EBFormalCoeffs.C_ofReal (hpath.snd i)).congr (fun τ => by
          simp [formalPoint, realVecToFormal, formalConst])
  | n + 1, hn => by
      have prev := EBFormalVecCoeffs_formalPoint_of_path θ hpath n (Nat.le_of_succ_le hn)
      refine ⟨?_, ?_⟩
      · exact (EBFormalVecCoeffs.matVecMulConst
          (formalCollapseMatrix θ ⟨n, Nat.lt_of_succ_le hn⟩ -
            formalGatedValueSum θ ⟨n, Nat.lt_of_succ_le hn⟩) prev.1).congr (fun τ => by
          simp [formalPoint_succ, formalStepPoint, formalW, formalV])
      · exact ((EBFormalVecCoeffs.matVecMulConst
            (formalCollapseMatrix θ ⟨n, Nat.lt_of_succ_le hn⟩) prev.2).add
          (EBFormalVecCoeffs.matVecMulConst
            (formalGatedValueSum θ ⟨n, Nat.lt_of_succ_le hn⟩) prev.1)).congr (fun τ => by
          simp [formalPoint_succ, formalStepPoint, formalW, formalV])

/-- Coefficients of the formal slope polynomial are eventually bounded along a bounded probe
path. -/
noncomputable def EBFormalCoeffs_formalSlope_of_path (θ : Params L k d)
    (l : Fin L) (a : Fin k) {path : ℝ → ProbePair d}
    (hpath : EventuallyBoundedProbePair path) :
    EBFormalCoeffs (fun τ => formalSlope θ (path τ).1 (path τ).2 l a) := by
  have hpair := EBFormalVecCoeffs_formalPoint_of_path θ hpath l.1 (Nat.le_of_lt l.2)
  have hW : EBFormalVecCoeffs
      (fun τ => formalW θ (path τ).1 (path τ).2 l.1 (Nat.le_of_lt l.2)) := hpair.1
  have hV : EBFormalVecCoeffs
      (fun τ => formalV θ (path τ).1 (path τ).2 l.1 (Nat.le_of_lt l.2)) := hpair.2
  have hAV := EBFormalVecCoeffs.matVecMulConst
    (realMatrixToFormal (attentionMatrix θ l a)) hV
  have hbil : EBFormalCoeffs
      (fun τ => ∑ i : Fin d,
        (formalW θ (path τ).1 (path τ).2 l.1 (Nat.le_of_lt l.2)) i *
          (realMatrixToFormal (attentionMatrix θ l a) *ᵥ
            formalV θ (path τ).1 (path τ).2 l.1 (Nat.le_of_lt l.2)) i) :=
    EBFormalCoeffs.fintype_sum _ (fun i => (hW i).mul (hAV i))
  exact hbil.congr (fun τ => by
    simp [formalSlope, formalBilin, dotProduct])

end FormalCoeffs

/-! ## The fixed finite monomial box of the formal slope and the slice-Lipschitz constant -/

/-- The fixed finite set of monomials whose degree in every formal variable is at most `2`. -/
noncomputable def formalMonomialBox (L k : Nat) : Finset (FormalVar L k →₀ Nat) :=
  (Finset.univ : Finset (FormalVar L k)).finsupp (fun _ : FormalVar L k => Finset.range 3)

theorem mem_formalMonomialBox_iff {L k : Nat} {m : FormalVar L k →₀ Nat} :
    m ∈ formalMonomialBox L k ↔ ∀ x : FormalVar L k, m x ≤ 2 := by
  classical
  unfold formalMonomialBox
  rw [Finset.mem_finsupp_iff]
  constructor
  · intro h j
    have hj := h.2 j (Finset.mem_univ j)
    rw [Finset.mem_range] at hj
    exact Nat.lt_succ_iff.mp hj
  · intro h
    constructor
    · intro j _hj
      exact Finset.mem_univ j
    · intro j _hj
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le (h j)

theorem support_formalSlope_subset_box {L k d : Nat} (θ : Params L k d)
    (w v : Vec d) (l : Fin L) (a : Fin k) :
    (formalSlope θ w v l a).support ⊆ formalMonomialBox L k := by
  intro m hm
  rw [mem_formalMonomialBox_iff]
  intro x
  have hdeg : MvPolynomial.degreeOf x (formalSlope θ w v l a) ≤ 2 :=
    blockDegreeLE_degreeOf_le (formalSlope_blockDegree_two θ w v l a)
  exact (MvPolynomial.degreeOf_le_iff.mp hdeg) m hm

/-- Absolute value of an eventually bounded real function is eventually bounded. -/
noncomputable def eventuallyBoundedReal_abs {f : ℝ → ℝ} (h : EventuallyBoundedReal f) :
    EventuallyBoundedReal (fun τ => |f τ|) :=
  EventuallyBoundedReal.of_bound h.radius h.radius_nonneg h.start (by
    intro τ hτ
    rw [abs_abs]
    exact h.bound τ hτ)

-- Elaborating the recursive coefficient-boundedness families for `formalSlope` over the
-- finite monomial box needs more reduction budget than the file default.
set_option maxHeartbeats 1600000 in
/-- **τ-uniform boundedness of the formal-slope slice-Lipschitz constant.**  Along a bounded
probe path, the coefficient-sum Lipschitz constant of `formalSlope θ (path τ).1 (path τ).2 l a`
in any fixed coordinate stays bounded, because the coefficients are eventually bounded and the
support lives in the fixed monomial box. -/
noncomputable def eventuallyBoundedReal_realFormalSliceLip_of_path {L k d : Nat}
    (θ : Params L k d) (l : Fin L) (a : Fin k) (coord : FormalVar L k)
    (R : FormalVar L k → ℝ) {path : ℝ → ProbePair d}
    (hR : ∀ j, 0 ≤ R j) (hpath : EventuallyBoundedProbePair path) :
    EventuallyBoundedReal
      (fun τ => realSliceLip (formalSlope θ (path τ).1 (path τ).2 l a) coord R) := by
  classical
  let q : ℝ → FormalPoly L k := fun τ => formalSlope θ (path τ).1 (path τ).2 l a
  let box : Finset (FormalVar L k →₀ Nat) := formalMonomialBox L k
  let factor : (FormalVar L k →₀ Nat) → ℝ :=
    fun m => (((m coord : ℝ) * R coord ^ (m coord - 1)) * realSliceOffRadius coord R m)
  have hcoeffs : EBFormalCoeffs q := EBFormalCoeffs_formalSlope_of_path θ l a hpath
  let term : (FormalVar L k →₀ Nat) → ℝ → ℝ :=
    fun m τ => |MvPolynomial.coeff m (q τ)| * factor m
  have hterm : ∀ m : FormalVar L k →₀ Nat, EventuallyBoundedReal (term m) := by
    intro m
    exact (eventuallyBoundedReal_abs (hcoeffs m)).mul_const (factor m)
  have hsum : EventuallyBoundedReal (fun τ => ∑ m : {m // m ∈ box}, term m.1 τ) :=
    EventuallyBoundedReal.fintype_sum
      (fun (m : {m // m ∈ box}) τ => term m.1 τ)
      (fun (m : {m // m ∈ box}) => hterm m.1)
  refine EventuallyBoundedReal.of_bound hsum.radius hsum.radius_nonneg hsum.start ?_
  intro τ hτ
  have hnonneg : 0 ≤ realSliceLip (q τ) coord R :=
    realSliceLip_nonneg (q τ) coord R hR
  rw [abs_of_nonneg hnonneg]
  have hsupport : (q τ).support ⊆ box :=
    support_formalSlope_subset_box θ (path τ).1 (path τ).2 l a
  calc
    realSliceLip (q τ) coord R = ∑ m ∈ (q τ).support, term m τ := by
      simp only [realSliceLip, term, factor]
    _ ≤ ∑ m ∈ box, term m τ := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsupport ?_
      intro m _hmbox _hmnot
      exact mul_nonneg (abs_nonneg _)
        (mul_nonneg
          (mul_nonneg (Nat.cast_nonneg (m coord)) (pow_nonneg (hR coord) (m coord - 1)))
          (realSliceOffRadius_nonneg coord R m hR))
    _ = ∑ m : {m // m ∈ box}, term m.1 τ := by
      exact Finset.sum_subtype (s := box) (h := fun m => Iff.rfl) (f := fun m => term m τ)
    _ ≤ |∑ m : {m // m ∈ box}, term m.1 τ| := le_abs_self _
    _ ≤ hsum.radius := hsum.bound τ hτ

/-! ## Eventual boundedness from convergence -/

/-- A convergent real function is eventually bounded, with explicit data. -/
noncomputable def EventuallyBoundedReal.ofTendsto {f : ℝ → ℝ} {a : ℝ}
    (h : Filter.Tendsto f Filter.atTop (nhds a)) : EventuallyBoundedReal f := by
  have hex := (Metric.tendsto_atTop.mp h) 1 one_pos
  refine EventuallyBoundedReal.of_bound (|a| + 1) (by positivity) (Classical.choose hex) ?_
  intro τ hτ
  have hd : |f τ - a| < 1 := by
    rw [← Real.dist_eq]
    exact Classical.choose_spec hex τ hτ
  calc
    |f τ| = |(f τ - a) + a| := by ring_nf
    _ ≤ |f τ - a| + |a| := abs_add_le _ _
    _ ≤ 1 + |a| := by linarith [hd.le]
    _ = |a| + 1 := by ring

end TransformerIdentifiability.NLayer.KHead
