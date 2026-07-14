import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Core

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.NoSkip

/-!
# Inter-layer gauge algebra

The action is first defined for an arbitrary gauge at every interface.  A
`GaugeChain` then imposes the physical boundary conditions `G_0 = G_L = I`.
This slightly more general internal API makes hidden-state equivariance stable
under deleting the first layer.
-/

noncomputable section

/-- A real invertible `d x d` matrix. -/
structure GaugeMatrix (d : Nat) where
  matrix : Matrix (Fin d) (Fin d) Real
  det_ne_zero : matrix.det ≠ 0

namespace GaugeMatrix

variable {d : Nat}

/-- The nonsingular matrix inverse. -/
def invMatrix (G : GaugeMatrix d) : Matrix (Fin d) (Fin d) Real :=
  G.matrix⁻¹

/-- The inverse transpose `G^{-T}`. -/
def invTranspose (G : GaugeMatrix d) : Matrix (Fin d) (Fin d) Real :=
  G.invMatrixᵀ

@[simp] theorem matrix_mul_invMatrix (G : GaugeMatrix d) :
    G.matrix * G.invMatrix = 1 := by
  exact Matrix.mul_nonsing_inv G.matrix (Ne.isUnit G.det_ne_zero)

@[simp] theorem invMatrix_mul_matrix (G : GaugeMatrix d) :
    G.invMatrix * G.matrix = 1 := by
  exact Matrix.nonsing_inv_mul G.matrix (Ne.isUnit G.det_ne_zero)

@[simp] theorem matrix_transpose_mul_invTranspose (G : GaugeMatrix d) :
    G.matrixᵀ * G.invTranspose = 1 := by
  rw [invTranspose, ← Matrix.transpose_mul, invMatrix_mul_matrix]
  simp

@[simp] theorem invTranspose_mul_matrix_transpose (G : GaugeMatrix d) :
    G.invTranspose * G.matrixᵀ = 1 := by
  rw [invTranspose, ← Matrix.transpose_mul, matrix_mul_invMatrix]
  simp

/-- Invertible matrices are extensional in their underlying matrices. -/
@[ext] theorem ext {G H : GaugeMatrix d} (h : G.matrix = H.matrix) : G = H := by
  cases G
  cases H
  simp_all

protected def one : GaugeMatrix d where
  matrix := 1
  det_ne_zero := by simp

protected def mul (G H : GaugeMatrix d) : GaugeMatrix d where
  matrix := G.matrix * H.matrix
  det_ne_zero := by simp [Matrix.det_mul, G.det_ne_zero, H.det_ne_zero]

protected def inv (G : GaugeMatrix d) : GaugeMatrix d where
  matrix := G.invMatrix
  det_ne_zero := Matrix.det_ne_zero_of_left_inverse G.matrix_mul_invMatrix

instance : One (GaugeMatrix d) := ⟨GaugeMatrix.one⟩
instance : Mul (GaugeMatrix d) := ⟨GaugeMatrix.mul⟩
instance : Inv (GaugeMatrix d) := ⟨GaugeMatrix.inv⟩

@[simp] theorem matrix_one : (1 : GaugeMatrix d).matrix = 1 := rfl
@[simp] theorem matrix_mul (G H : GaugeMatrix d) : (G * H).matrix = G.matrix * H.matrix := rfl
@[simp] theorem matrix_inv (G : GaugeMatrix d) : (G⁻¹).matrix = G.invMatrix := rfl

@[simp] theorem invMatrix_inv (G : GaugeMatrix d) : (G⁻¹).invMatrix = G.matrix := by
  apply Matrix.inv_eq_right_inv
  exact G.invMatrix_mul_matrix

@[simp] theorem invMatrix_one : (1 : GaugeMatrix d).invMatrix = 1 := by
  apply Matrix.inv_eq_right_inv
  simp

@[simp] theorem invMatrix_mul (G H : GaugeMatrix d) :
    (G * H).invMatrix = H.invMatrix * G.invMatrix := by
  apply Matrix.inv_eq_right_inv
  simp only [matrix_mul]
  calc
    (G.matrix * H.matrix) * (H.invMatrix * G.invMatrix) =
        G.matrix * (H.matrix * H.invMatrix) * G.invMatrix := by
          simp only [Matrix.mul_assoc]
    _ = 1 := by simp

@[simp] theorem invTranspose_one : (1 : GaugeMatrix d).invTranspose = 1 := by
  simp [invTranspose]

@[simp] theorem invTranspose_mul (G H : GaugeMatrix d) :
    (G * H).invTranspose = G.invTranspose * H.invTranspose := by
  simp [invTranspose, Matrix.transpose_mul]

instance : Group (GaugeMatrix d) where
  mul_assoc G H K := by ext; simp [Matrix.mul_assoc]
  one_mul G := by ext; simp
  mul_one G := by ext; simp
  inv_mul_cancel G := by ext; simp

end GaugeMatrix

/-- A gauge matrix at each of the `L+1` layer interfaces. -/
abbrev InterfaceGaugeChain (L d : Nat) := Fin (L + 1) → GaugeMatrix d

/-- Pointwise identity interface gauges. -/
def identityInterfaceGauge (L d : Nat) : InterfaceGaugeChain L d :=
  fun _ => 1

/-- Pointwise composition of interface gauges. -/
def mulInterfaceGauge {L d : Nat} (G H : InterfaceGaugeChain L d) :
    InterfaceGaugeChain L d :=
  fun i => G i * H i

/-- Boundary-normalized gauges: `G_0 = G_L = I`. -/
structure GaugeChain (L d : Nat) where
  get : InterfaceGaugeChain L d
  get_zero : get 0 = 1
  get_last : get (Fin.last L) = 1

namespace GaugeChain

variable {L d : Nat}

@[ext] theorem ext {G H : GaugeChain L d} (h : G.get = H.get) : G = H := by
  cases G
  cases H
  simp_all

protected def one : GaugeChain L d where
  get := identityInterfaceGauge L d
  get_zero := rfl
  get_last := rfl

protected def mul (G H : GaugeChain L d) : GaugeChain L d where
  get := mulInterfaceGauge G.get H.get
  get_zero := by simp [mulInterfaceGauge, G.get_zero, H.get_zero]
  get_last := by simp [mulInterfaceGauge, G.get_last, H.get_last]

protected def inv (G : GaugeChain L d) : GaugeChain L d where
  get := fun i => (G.get i)⁻¹
  get_zero := by simp [G.get_zero]
  get_last := by simp [G.get_last]

instance : One (GaugeChain L d) := ⟨GaugeChain.one⟩
instance : Mul (GaugeChain L d) := ⟨GaugeChain.mul⟩
instance : Inv (GaugeChain L d) := ⟨GaugeChain.inv⟩

@[simp] theorem get_one (i : Fin (L + 1)) : (1 : GaugeChain L d).get i = 1 := rfl
@[simp] theorem get_mul (G H : GaugeChain L d) (i : Fin (L + 1)) :
    (G * H).get i = G.get i * H.get i := rfl
@[simp] theorem get_inv (G : GaugeChain L d) (i : Fin (L + 1)) :
    (G⁻¹).get i = (G.get i)⁻¹ := rfl

instance : Group (GaugeChain L d) where
  mul_assoc G H K := by ext i; simp [mul_assoc]
  one_mul G := by ext i; simp
  mul_one G := by ext i; simp
  inv_mul_cancel G := by ext i; simp

@[simp] theorem first_interface (G : GaugeChain L d) : G.get 0 = 1 :=
  G.get_zero

@[simp] theorem last_interface (G : GaugeChain L d) : G.get (Fin.last L) = 1 :=
  G.get_last

@[simp] theorem first_layer_input {L : Nat} (G : GaugeChain (L + 1) d) :
    G.get (Fin.castSucc (0 : Fin (L + 1))) = 1 := by
  simp

@[simp] theorem last_layer_output {L : Nat} (G : GaugeChain (L + 1) d) :
    G.get (Fin.last L).succ = 1 := by
  simp

end GaugeChain

/-- Delete the input interface from a general chain. -/
def tailInterfaceGauge {L d : Nat} (G : InterfaceGaugeChain (L + 1) d) :
    InterfaceGaugeChain L d :=
  Fin.tail G

/-- Gauge action with arbitrary interface endpoints.  For normalized chains it
is the physical inter-layer gauge action. -/
def gaugeAction {L k d : Nat} (G : InterfaceGaugeChain L d) (theta : Params L k d) :
    Params L k d :=
  fun l a =>
    ((G l.succ).matrix * valueMatrix theta l a * (G l.castSucc).invMatrix,
      (G l.castSucc).invTranspose * attentionMatrix theta l a * (G l.castSucc).invMatrix)

/-- Gauge action for a boundary-normalized chain. -/
def GaugeChain.act {L k d : Nat} (G : GaugeChain L d) (theta : Params L k d) :
    Params L k d :=
  gaugeAction G.get theta

@[simp] theorem valueMatrix_gaugeAction {L k d : Nat} (G : InterfaceGaugeChain L d)
    (theta : Params L k d) (l : Fin L) (a : Fin k) :
    valueMatrix (gaugeAction G theta) l a =
      (G l.succ).matrix * valueMatrix theta l a * (G l.castSucc).invMatrix :=
  rfl

@[simp] theorem attentionMatrix_gaugeAction {L k d : Nat} (G : InterfaceGaugeChain L d)
    (theta : Params L k d) (l : Fin L) (a : Fin k) :
    attentionMatrix (gaugeAction G theta) l a =
      (G l.castSucc).invTranspose * attentionMatrix theta l a * (G l.castSucc).invMatrix :=
  rfl

@[simp] theorem gaugeAction_identity {L k d : Nat} (theta : Params L k d) :
    gaugeAction (identityInterfaceGauge L d) theta = theta := by
  apply Params.ext
  · intro l a
    simp [identityInterfaceGauge]
  · intro l a
    simp [identityInterfaceGauge]

theorem gaugeAction_comp {L k d : Nat} (G H : InterfaceGaugeChain L d)
    (theta : Params L k d) :
    gaugeAction G (gaugeAction H theta) = gaugeAction (mulInterfaceGauge G H) theta := by
  apply Params.ext
  · intro l a
    simp only [valueMatrix_gaugeAction]
    simp [mulInterfaceGauge, Matrix.mul_assoc]
  · intro l a
    simp only [attentionMatrix_gaugeAction]
    simp [mulInterfaceGauge, Matrix.mul_assoc]

@[simp] theorem GaugeChain.one_act {L k d : Nat} (theta : Params L k d) :
    (1 : GaugeChain L d).act theta = theta :=
  gaugeAction_identity theta

theorem GaugeChain.mul_act {L k d : Nat} (G H : GaugeChain L d)
    (theta : Params L k d) :
    (G * H).act theta = G.act (H.act theta) := by
  symm
  exact gaugeAction_comp G.get H.get theta

/-- Gauge transformations commute with layerwise head relabeling. -/
theorem gaugeAction_permuteHeads {L k d : Nat} (G : InterfaceGaugeChain L d)
    (sigma : Fin L → Equiv.Perm (Fin k)) (theta : Params L k d) :
    gaugeAction G (permuteHeads sigma theta) = permuteHeads sigma (gaugeAction G theta) := by
  rfl

theorem GaugeChain.act_permuteHeads {L k d : Nat} (G : GaugeChain L d)
    (sigma : Fin L → Equiv.Perm (Fin k)) (theta : Params L k d) :
    G.act (permuteHeads sigma theta) = permuteHeads sigma (G.act theta) :=
  gaugeAction_permuteHeads G.get sigma theta

/-- Deleting the first parameter layer commutes with deleting the first gauge interface. -/
@[simp] theorem tail_gaugeAction {L k d : Nat} (G : InterfaceGaugeChain (L + 1) d)
    (theta : Params (L + 1) k d) :
    Fin.tail (gaugeAction G theta) = gaugeAction (tailInterfaceGauge G) (Fin.tail theta) := by
  rfl

/-- Congruence of scores under the input-side gauge at one interface. -/
theorem score_gauge_eq {d T : Nat} (G : GaugeMatrix d)
    (A : Matrix (Fin d) (Fin d) Real) (X : Matrix (Fin d) (Fin T) Real) :
    (G.matrix * X)ᵀ * (G.invTranspose * A * G.invMatrix) * (G.matrix * X) =
      Xᵀ * A * X := by
  rw [Matrix.transpose_mul]
  calc
    (Xᵀ * G.matrixᵀ) * (G.invTranspose * A * G.invMatrix) * (G.matrix * X) =
        Xᵀ * (G.matrixᵀ * G.invTranspose) * A *
          (G.invMatrix * G.matrix) * X := by
            simp only [Matrix.mul_assoc]
    _ = Xᵀ * A * X := by simp

/-- One no-skip layer is equivariant between its adjacent interface gauges. -/
theorem layer_gaugeAction {L k d T : Nat} (G : InterfaceGaugeChain L d)
    (theta : Params L k d) (l : Fin L) (X : Matrix (Fin d) (Fin T) Real) :
    layer (gaugeAction G theta) l ((G l.castSucc).matrix * X) =
      (G l.succ).matrix * layer theta l X := by
  simp only [layer, valueMatrix_gaugeAction, attentionMatrix_gaugeAction]
  calc
    (∑ a : Fin k,
        (G l.succ).matrix * valueMatrix theta l a * (G l.castSucc).invMatrix *
          ((G l.castSucc).matrix * X) *
          softmaxColC
            (((G l.castSucc).matrix * X)ᵀ *
              ((G l.castSucc).invTranspose * attentionMatrix theta l a *
                (G l.castSucc).invMatrix) *
              ((G l.castSucc).matrix * X))) =
        ∑ a : Fin k, (G l.succ).matrix *
          (valueMatrix theta l a * X *
            softmaxColC (Xᵀ * attentionMatrix theta l a * X)) := by
              apply Finset.sum_congr rfl
              intro a _ha
              rw [score_gauge_eq]
              calc
                (G l.succ).matrix * valueMatrix theta l a *
                    (G l.castSucc).invMatrix * ((G l.castSucc).matrix * X) *
                    softmaxColC (Xᵀ * attentionMatrix theta l a * X) =
                    ((G l.succ).matrix * valueMatrix theta l a) *
                      ((G l.castSucc).invMatrix * (G l.castSucc).matrix) * X *
                      softmaxColC (Xᵀ * attentionMatrix theta l a * X) := by
                        simp only [Matrix.mul_assoc]
                _ = (G l.succ).matrix *
                    (valueMatrix theta l a * X *
                      softmaxColC (Xᵀ * attentionMatrix theta l a * X)) := by
                        simp [Matrix.mul_assoc]
    _ = (G l.succ).matrix *
        ∑ a : Fin k, valueMatrix theta l a * X *
          softmaxColC (Xᵀ * attentionMatrix theta l a * X) := by
            ext i j
            simp only [Matrix.sum_apply, Matrix.mul_apply, Finset.mul_sum]
            rw [Finset.sum_comm]

/-- Hidden-state equivariance, including arbitrary input/output gauges. -/
theorem transformer_gaugeAction {L k d T : Nat} (G : InterfaceGaugeChain L d)
    (theta : Params L k d) (X : Matrix (Fin d) (Fin T) Real) :
    transformer (gaugeAction G theta) ((G 0).matrix * X) =
      (G (Fin.last L)).matrix * transformer theta X := by
  induction L generalizing X with
  | zero => simp [transformer]
  | succ L ih =>
      rw [transformer_succ, transformer_succ]
      change transformer (Fin.tail (gaugeAction G theta))
          (layer (gaugeAction G theta) 0
            ((G (Fin.castSucc (0 : Fin (L + 1)))).matrix * X)) = _
      rw [layer_gaugeAction]
      rw [tail_gaugeAction]
      exact ih (G := tailInterfaceGauge G) (theta := Fin.tail theta) (layer theta 0 X)

/-- Boundary-normalized gauge chains leave the transformer realization unchanged. -/
theorem transformer_gauge_invariant {L k d T : Nat} (G : GaugeChain L d)
    (theta : Params L k d) (X : Matrix (Fin d) (Fin T) Real) :
    transformer (G.act theta) X = transformer theta X := by
  have h := transformer_gaugeAction G.get theta X
  simpa [G.get_zero, G.get_last] using h

/-- Combined permutation and gauge invariance. -/
theorem transformer_permute_gauge_invariant {L k d T : Nat} (G : GaugeChain L d)
    (sigma : Fin L → Equiv.Perm (Fin k)) (theta : Params L k d)
    (X : Matrix (Fin d) (Fin T) Real) :
    transformer (permuteHeads sigma (G.act theta)) X = transformer theta X := by
  rw [transformer_permuteHeads, transformer_gauge_invariant]

/-! ## Joint surjectivity of the value heads -/

/-- The horizontal block matrix `[V_{l,0} | ... | V_{l,k-1}]`.  Its column
index records first the head and then the column within that head. -/
def jointValueMatrix {L k d : Nat} (theta : Params L k d) (l : Fin L) :
    Matrix (Fin d) (Fin k × Fin d) Real :=
  fun i aj => valueMatrix theta l aj.1 i aj.2

/-- A layer is jointly surjective when its horizontal value block matrix maps
onto the whole hidden-state space. -/
def JointSurjective {L k d : Nat} (theta : Params L k d) (l : Fin L) : Prop :=
  Function.Surjective (jointValueMatrix theta l).mulVec

/-- The sum of the ranges of the value heads at one layer. -/
noncomputable def jointValueRange {L k d : Nat} (theta : Params L k d) (l : Fin L) :
    Submodule Real (Fin d → Real) :=
  ⨆ a : Fin k, LinearMap.range (valueMatrix theta l a).mulVecLin

/-- Applying the horizontal block matrix is the sum of applying its individual
value heads. -/
theorem jointValueMatrix_mulVec {L k d : Nat} (theta : Params L k d) (l : Fin L)
    (x : Fin k × Fin d → Real) :
    (jointValueMatrix theta l).mulVec x =
      ∑ a : Fin k, (valueMatrix theta l a).mulVec (fun j => x (a, j)) := by
  ext i
  simp only [Matrix.mulVec, dotProduct, jointValueMatrix, Finset.sum_apply]
  rw [Fintype.sum_prod_type]

/-- The range of the horizontal block matrix is exactly the sum of the head
ranges. -/
theorem range_jointValueMatrix_mulVecLin {L k d : Nat} (theta : Params L k d)
    (l : Fin L) :
    LinearMap.range (jointValueMatrix theta l).mulVecLin = jointValueRange theta l := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    rw [Matrix.mulVecLin_apply, jointValueMatrix_mulVec]
    apply Submodule.sum_mem
    intro a _ha
    exact le_iSup (fun b : Fin k =>
      LinearMap.range (valueMatrix theta l b).mulVecLin) a
      ⟨fun j => x (a, j), rfl⟩
  · rw [jointValueRange]
    refine iSup_le fun a => ?_
    rintro y ⟨x, rfl⟩
    let z : Fin k × Fin d → Real := fun bj => if bj.1 = a then x bj.2 else 0
    refine ⟨z, ?_⟩
    rw [Matrix.mulVecLin_apply, jointValueMatrix_mulVec]
    ext i
    simp [z, Matrix.mulVec, dotProduct]

/-- Joint surjectivity is equivalent to the TeX condition that the sum of the
head ranges is the whole hidden-state space. -/
theorem jointSurjective_iff_head_ranges_span {L k d : Nat} (theta : Params L k d)
    (l : Fin L) :
    JointSurjective theta l ↔ jointValueRange theta l = ⊤ := by
  change Function.Surjective (Matrix.mulVec (jointValueMatrix theta l)) ↔ _
  have hfun :
      Function.Surjective (Matrix.mulVec (jointValueMatrix theta l)) ↔
        Function.Surjective (jointValueMatrix theta l).mulVecLin := by
    rfl
  rw [hfun, ← LinearMap.range_eq_top, range_jointValueMatrix_mulVecLin]

/-- The polynomial Gram matrix used to encode joint surjectivity. -/
noncomputable def jointSurjectivityGram {L k d : Nat} (theta : Params L k d)
    (l : Fin L) : Matrix (Fin d) (Fin d) Real :=
  ∑ a : Fin k, valueMatrix theta l a * (valueMatrix theta l a)ᵀ

/-- The headwise Gram sum is the row Gram matrix of the horizontal block
matrix. -/
theorem jointSurjectivityGram_eq_mul_transpose {L k d : Nat} (theta : Params L k d)
    (l : Fin L) :
    jointSurjectivityGram theta l =
      jointValueMatrix theta l * (jointValueMatrix theta l)ᵀ := by
  ext i j
  simp only [jointSurjectivityGram, Matrix.sum_apply, Matrix.mul_apply,
    transpose_apply, jointValueMatrix]
  rw [Fintype.sum_prod_type]

/-- For a finite real matrix, surjectivity of `mulVec` is equivalent to full
row rank. -/
theorem mulVec_surjective_iff_rank_eq_height {m : Nat} {n : Type*} [Fintype n]
    (A : Matrix (Fin m) n Real) :
    Function.Surjective A.mulVec ↔ Matrix.rank A = m := by
  constructor
  · intro h
    have hlin : Function.Surjective A.mulVecLin := by
      simpa only [Matrix.mulVecLin_apply] using h
    change Module.finrank Real (LinearMap.range A.mulVecLin) = m
    rw [LinearMap.range_eq_top.mpr hlin]
    simp [Module.finrank_fintype_fun_eq_card]
  · intro h
    have hrange : LinearMap.range A.mulVecLin = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      change Module.finrank Real (LinearMap.range A.mulVecLin) = m at h
      simpa [Module.finrank_fintype_fun_eq_card] using h
    have hlin : Function.Surjective A.mulVecLin := LinearMap.range_eq_top.mp hrange
    simpa only [Matrix.mulVecLin_apply] using hlin

/-- Joint surjectivity is exactly nonvanishing of
`det (∑_a V_{l,a} V_{l,a}ᵀ)`. -/
theorem jointSurjective_iff_gram_det_ne_zero {L k d : Nat} (theta : Params L k d)
    (l : Fin L) :
    JointSurjective theta l ↔ (jointSurjectivityGram theta l).det ≠ 0 := by
  calc
    JointSurjective theta l ↔ Matrix.rank (jointValueMatrix theta l) = d :=
      mulVec_surjective_iff_rank_eq_height (jointValueMatrix theta l)
    _ ↔ Matrix.rank (jointSurjectivityGram theta l) = d := by
      rw [jointSurjectivityGram_eq_mul_transpose,
        Matrix.rank_self_mul_transpose]
    _ ↔ Function.Surjective (jointSurjectivityGram theta l).mulVec :=
      (mulVec_surjective_iff_rank_eq_height (jointSurjectivityGram theta l)).symm
    _ ↔ (jointSurjectivityGram theta l).det ≠ 0 := by
      simp [Matrix.mulVec_surjective_iff_isUnit, Matrix.isUnit_iff_isUnit_det]

/-! ## Uniqueness of target-to-source matching data -/

/-- The target attention heads are pairwise distinct at every layer. -/
def PairwiseDistinctAttentions {L k d : Nat} (theta : Params L k d) : Prop :=
  ∀ l : Fin L, Function.Injective (fun a : Fin k => attentionMatrix theta l a)

/-- A target-to-source head matching together with a boundary-normalized gauge
chain.  The equations use the TeX orientation: `headPerm l h` is the source
head corresponding to target head `h`. -/
structure TargetToSourceMatching {L k d : Nat}
    (theta theta' : Params L k d) where
  headPerm : Fin L → Equiv.Perm (Fin k)
  gauge : GaugeChain L d
  attention_eq : ∀ (l : Fin L) (h : Fin k),
    attentionMatrix theta l (headPerm l h) =
      (gauge.get l.castSucc).matrixᵀ * attentionMatrix theta' l h *
        (gauge.get l.castSucc).matrix
  value_eq : ∀ (l : Fin L) (h : Fin k),
    valueMatrix theta l (headPerm l h) =
      (gauge.get l.succ).invMatrix * valueMatrix theta' l h *
        (gauge.get l.castSucc).matrix

namespace TargetToSourceMatching

@[ext] theorem ext {L k d : Nat} {theta theta' : Params L k d}
    {matching matching' : TargetToSourceMatching theta theta'}
    (hperm : matching.headPerm = matching'.headPerm)
    (hgauge : matching.gauge = matching'.gauge) :
    matching = matching' := by
  cases matching
  cases matching'
  simp_all

end TargetToSourceMatching

/-- Congruence by an invertible matrix is injective. -/
theorem gauge_congruence_injective {d : Nat} (G : GaugeMatrix d) :
    Function.Injective
      (fun A : Matrix (Fin d) (Fin d) Real => G.matrixᵀ * A * G.matrix) := by
  intro A B h
  have hleft := congrArg (fun M => G.invTranspose * M) h
  have hmul : A * G.matrix = B * G.matrix := by
    calc
      A * G.matrix = (G.invTranspose * G.matrixᵀ) * (A * G.matrix) := by simp
      _ = G.invTranspose * (G.matrixᵀ * (A * G.matrix)) :=
        Matrix.mul_assoc _ _ _
      _ = G.invTranspose * ((G.matrixᵀ * A) * G.matrix) := by
        rw [Matrix.mul_assoc]
      _ = G.invTranspose * ((G.matrixᵀ * B) * G.matrix) := hleft
      _ = G.invTranspose * (G.matrixᵀ * (B * G.matrix)) := by
        rw [Matrix.mul_assoc]
      _ = (G.invTranspose * G.matrixᵀ) * (B * G.matrix) := by
        rw [Matrix.mul_assoc]
      _ = B * G.matrix := by simp
  have hright := congrArg (fun M => M * G.invMatrix) hmul
  simpa [Matrix.mul_assoc] using hright

/-- Joint surjectivity lets one cancel all target value heads simultaneously
from the right. -/
theorem matrix_eq_of_mul_valueMatrices_eq_of_jointSurjective {L k d : Nat}
    {theta : Params L k d} {l : Fin L}
    (hjoint : JointSurjective theta l)
    {M N : Matrix (Fin d) (Fin d) Real}
    (hmul : ∀ a : Fin k,
      M * valueMatrix theta l a = N * valueMatrix theta l a) :
    M = N := by
  apply Matrix.mulVec_injective
  funext y
  rcases hjoint y with ⟨x, rfl⟩
  rw [jointValueMatrix_mulVec, Matrix.mulVec_sum, Matrix.mulVec_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hmul a]

/-- At one layer, equality of the input gauge forces equality of both the
target-to-source head permutation and the output gauge. -/
theorem TargetToSourceMatching.layer_unique {L k d : Nat}
    {theta theta' : Params L k d}
    (hdistinct : PairwiseDistinctAttentions theta')
    (hjoint : ∀ l : Fin L, JointSurjective theta' l)
    (matching matching' : TargetToSourceMatching theta theta')
    (l : Fin L)
    (hinput : matching.gauge.get l.castSucc = matching'.gauge.get l.castSucc) :
    matching.headPerm l = matching'.headPerm l ∧
      matching.gauge.get l.succ = matching'.gauge.get l.succ := by
  have hperm_pointwise : ∀ h : Fin k,
      matching.headPerm l h = matching'.headPerm l h := by
    intro h
    let q : Fin k := (matching'.headPerm l).symm (matching.headPerm l h)
    have hsource :
        attentionMatrix theta l (matching.headPerm l h) =
          attentionMatrix theta l (matching'.headPerm l q) := by
      simp [q]
    have hcongr :
        (matching.gauge.get l.castSucc).matrixᵀ *
              attentionMatrix theta' l h *
              (matching.gauge.get l.castSucc).matrix =
          (matching.gauge.get l.castSucc).matrixᵀ *
              attentionMatrix theta' l q *
              (matching.gauge.get l.castSucc).matrix := by
      rw [← matching.attention_eq l h, hsource,
        matching'.attention_eq l q, hinput]
    have htarget : attentionMatrix theta' l h = attentionMatrix theta' l q :=
      gauge_congruence_injective (matching.gauge.get l.castSucc) hcongr
    have hhq : h = q := (hdistinct l) htarget
    calc
      matching.headPerm l h = matching'.headPerm l q := by simp [q]
      _ = matching'.headPerm l h := by rw [← hhq]
  have hperm : matching.headPerm l = matching'.headPerm l := by
    apply Equiv.ext
    exact hperm_pointwise
  refine ⟨hperm, ?_⟩
  have hvalues : ∀ h : Fin k,
      (matching.gauge.get l.succ).invMatrix * valueMatrix theta' l h =
        (matching'.gauge.get l.succ).invMatrix * valueMatrix theta' l h := by
    intro h
    have heqSource := matching.value_eq l h
    rw [hperm] at heqSource
    have heq := heqSource.symm.trans (matching'.value_eq l h)
    rw [hinput] at heq
    have heq' := congrArg
      (fun M => M * (matching'.gauge.get l.castSucc).invMatrix) heq
    simpa [Matrix.mul_assoc] using heq'
  have hinvMatrix :
      (matching.gauge.get l.succ).invMatrix =
        (matching'.gauge.get l.succ).invMatrix :=
    matrix_eq_of_mul_valueMatrices_eq_of_jointSurjective (hjoint l) hvalues
  have hinvGauge :
      (matching.gauge.get l.succ)⁻¹ = (matching'.gauge.get l.succ)⁻¹ := by
    apply GaugeMatrix.ext
    exact hinvMatrix
  exact inv_injective hinvGauge

/-- Pairwise-distinct target attentions and jointly surjective target values
make all target-to-source matching data unique. -/
theorem targetToSourceMatching_unique {L k d : Nat}
    {theta theta' : Params L k d}
    (hdistinct : PairwiseDistinctAttentions theta')
    (hjoint : ∀ l : Fin L, JointSurjective theta' l)
    (matching matching' : TargetToSourceMatching theta theta') :
    matching.headPerm = matching'.headPerm ∧ matching.gauge = matching'.gauge := by
  have hgauge : ∀ i : Fin (L + 1), matching.gauge.get i = matching'.gauge.get i := by
    intro i
    induction i using Fin.induction with
    | zero => simp
    | succ l hprev =>
        exact (matching.layer_unique hdistinct hjoint matching' l hprev).2
  constructor
  · funext l
    exact (matching.layer_unique hdistinct hjoint matching' l
      (hgauge l.castSucc)).1
  · apply GaugeChain.ext
    funext i
    exact hgauge i

/-- Package-level form of uniqueness of the matching data. -/
theorem targetToSourceMatching_eq {L k d : Nat}
    {theta theta' : Params L k d}
    (hdistinct : PairwiseDistinctAttentions theta')
    (hjoint : ∀ l : Fin L, JointSurjective theta' l)
    (matching matching' : TargetToSourceMatching theta theta') :
    matching = matching' := by
  rcases targetToSourceMatching_unique hdistinct hjoint matching matching' with
    ⟨hperm, hgauge⟩
  exact TargetToSourceMatching.ext hperm hgauge

/-! ## Freeness of the combined permutation/gauge action -/

/-- The commuting combined action, with the same permutation convention as
`permuteHeads`: the transformed head at `a` reads the old head at `sigma l a`. -/
def combinedGaugePermuteAction {L k d : Nat}
    (sigma : Fin L → Equiv.Perm (Fin k)) (G : GaugeChain L d)
    (theta : Params L k d) : Params L k d :=
  permuteHeads sigma (G.act theta)

/-- Reusable freeness predicate for the combined head-permutation and
boundary-normalized gauge action. -/
def CombinedGaugePermuteFreeAt {L k d : Nat} (theta : Params L k d) : Prop :=
  ∀ (sigma : Fin L → Equiv.Perm (Fin k)) (G : GaugeChain L d),
    combinedGaugePermuteAction sigma G theta = theta →
      sigma = 1 ∧ G = 1

/-- The identity permutation and identity gauge give the tautological
target-to-source matching. -/
def identityTargetToSourceMatching {L k d : Nat} (theta : Params L k d) :
    TargetToSourceMatching theta theta where
  headPerm := 1
  gauge := 1
  attention_eq := by simp
  value_eq := by simp

/-- A fixed point of the combined action yields matching data in the reverse
orientation: target-to-source permutation `sigma⁻¹` and gauge `G⁻¹`. -/
def targetToSourceMatchingOfCombinedFixedPoint {L k d : Nat}
    (theta : Params L k d) (sigma : Fin L → Equiv.Perm (Fin k))
    (G : GaugeChain L d) (hfixed : combinedGaugePermuteAction sigma G theta = theta) :
    TargetToSourceMatching theta theta where
  headPerm := fun l => (sigma l).symm
  gauge := G⁻¹
  attention_eq := by
    intro l h
    have heq := congrArg
      (fun eta => attentionMatrix eta l ((sigma l).symm h)) hfixed
    simpa [combinedGaugePermuteAction] using heq.symm
  value_eq := by
    intro l h
    have heq := congrArg
      (fun eta => valueMatrix eta l ((sigma l).symm h)) hfixed
    simpa [combinedGaugePermuteAction] using heq.symm

/-- TeX `lem:gauge-uniqueness`, freeness conclusion: on the regular locus the
combined stabilizer is trivial. -/
theorem combinedGaugePermuteFreeAt_of_regular {L k d : Nat}
    {theta : Params L k d}
    (hdistinct : PairwiseDistinctAttentions theta)
    (hjoint : ∀ l : Fin L, JointSurjective theta l) :
    CombinedGaugePermuteFreeAt theta := by
  intro sigma G hfixed
  let matching :=
    targetToSourceMatchingOfCombinedFixedPoint theta sigma G hfixed
  let identity := identityTargetToSourceMatching theta
  have hunique := targetToSourceMatching_unique
    hdistinct hjoint matching identity
  constructor
  · funext l
    have hinv : (sigma l).symm = 1 := congrFun hunique.1 l
    simpa using congrArg Equiv.symm hinv
  · have hinv : G⁻¹ = 1 := hunique.2
    simpa using congrArg Inv.inv hinv

/-- Pointwise theorem form of the trivial-stabilizer result, convenient for
matrix-fiber clients that do not package a freeness predicate. -/
theorem combinedGaugePermute_stabilizer_trivial {L k d : Nat}
    {theta : Params L k d}
    (hdistinct : PairwiseDistinctAttentions theta)
    (hjoint : ∀ l : Fin L, JointSurjective theta l)
    {sigma : Fin L → Equiv.Perm (Fin k)} {G : GaugeChain L d}
    (hfixed : combinedGaugePermuteAction sigma G theta = theta) :
    sigma = 1 ∧ G = 1 :=
  combinedGaugePermuteFreeAt_of_regular hdistinct hjoint sigma G hfixed

end

end TransformerIdentifiability.NLayer.NoSkip
