import AnyLayerIdentifiabilityProof.NLayer.NoSkip.SharedToolbox
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Gauge

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.NoSkip

/-!
# No-skip cascade-certificate data

This file contains the model-independent value-chain portion of the cascade
certificate.  It uses only value matrices, later-layer attention matrices, and
their symmetric ignition forms; no collapsed-layer or skip-cancellation matrix
occurs in these definitions.

The numeric sum-of-squares certificate and its semantic witness types are both
defined here.  Their equivalence is deliberately deferred to NS055.
-/

/-! ## Chain indices and prefix products -/

/-- A later layer of a positive tail.  For a tail of depth `m + 1`, `n : Fin m`
addresses layer `n + 1`, leaving layer `0` as the first layer. -/
def laterLayer {m : Nat} (n : Fin m) : Fin (m + 1) :=
  ⟨n.val + 1, Nat.succ_lt_succ n.isLt⟩

@[simp] theorem laterLayer_val {m : Nat} (n : Fin m) :
    (laterLayer n).val = n.val + 1 :=
  rfl

theorem laterLayer_injective {m : Nat} :
    Function.Injective (@laterLayer m) := by
  intro i j hij
  apply Fin.ext
  simpa using congrArg Fin.val hij

/-- A choice of one head in each later layer. -/
abbrev CascadeChain (m k : Nat) : Type :=
  Fin m → Fin k

/-- Product along a cascade chain after `n` later layers.

At `n = 0` this is the first-layer value `V₀h`; each bounded successor
left-multiplies by the chain-selected value in the next layer.  Values past the
available later layers remain constant, making the definition total on `Nat`.
-/
noncomputable def cascadeProduct {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) (χ : CascadeChain m k) : Nat → Matrix (Fin d) (Fin d) ℝ
  | 0 => valueMatrix θ 0 h
  | n + 1 =>
      if hn : n < m then
        valueMatrix θ (laterLayer ⟨n, hn⟩) (χ ⟨n, hn⟩) *
          cascadeProduct θ h χ n
      else
        cascadeProduct θ h χ n

@[simp] theorem cascadeProduct_zero {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (χ : CascadeChain m k) :
    cascadeProduct θ h χ 0 = valueMatrix θ 0 h :=
  rfl

@[simp] theorem cascadeProduct_succ_of_lt {m k d n : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (χ : CascadeChain m k)
    (hn : n < m) :
    cascadeProduct θ h χ (n + 1) =
      valueMatrix θ (laterLayer ⟨n, hn⟩) (χ ⟨n, hn⟩) *
        cascadeProduct θ h χ n := by
  simp [cascadeProduct, hn]

@[simp] theorem cascadeProduct_succ_of_not_lt {m k d n : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (χ : CascadeChain m k)
    (hn : ¬ n < m) :
    cascadeProduct θ h χ (n + 1) = cascadeProduct θ h χ n := by
  simp [cascadeProduct, hn]

/-- Final residue matrix `P_m^{h,χ}` for the selected chain. -/
noncomputable def cascadeFinalProduct {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (χ : CascadeChain m k) :
    Matrix (Fin d) (Fin d) ℝ :=
  cascadeProduct θ h χ m

/-- Symmetric ignition matrix
`Sym(P_{j-1}ᵀ A_{j,a_j} P_{j-1})` for one later layer. -/
noncomputable def cascadeIgnitionMatrix {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (χ : CascadeChain m k)
    (j : Fin m) : Matrix (Fin d) (Fin d) ℝ :=
  sym ((cascadeProduct θ h χ j.val)ᵀ *
    attentionMatrix θ (laterLayer j) (χ j) *
      cascadeProduct θ h χ j.val)

/-! ## Numeric certificate values -/

/-- Squared Frobenius expression used only by the cascade certificate. -/
noncomputable def cascadeMatrixFrobSq {r c : Nat}
    (M : Matrix (Fin r) (Fin c) ℝ) : ℝ :=
  ∑ i : Fin r, ∑ j : Fin c, M i j * M i j

@[simp] theorem cascadeMatrixFrobSq_zero {r c : Nat} :
    cascadeMatrixFrobSq (0 : Matrix (Fin r) (Fin c) ℝ) = 0 := by
  simp [cascadeMatrixFrobSq]

theorem cascadeMatrixFrobSq_nonneg {r c : Nat}
    (M : Matrix (Fin r) (Fin c) ℝ) :
    0 ≤ cascadeMatrixFrobSq M := by
  exact Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => mul_self_nonneg (M i j)

/-- Residue factor `‖P_m^{h,χ}‖_F²`. -/
noncomputable def cascadeResidueValue {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (χ : CascadeChain m k) : ℝ :=
  cascadeMatrixFrobSq (cascadeFinalProduct θ h χ)

/-- Ignition factor `‖M_j^{h,χ}‖_F²`. -/
noncomputable def cascadeIgnitionValue {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (χ : CascadeChain m k)
    (j : Fin m) : ℝ :=
  cascadeMatrixFrobSq (cascadeIgnitionMatrix θ h χ j)

/-- One chain certificate value: its residue square times all ignition squares. -/
noncomputable def cascadeChainValue {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (χ : CascadeChain m k) : ℝ :=
  cascadeResidueValue θ h χ *
    ∏ j : Fin m, cascadeIgnitionValue θ h χ j

/-- Sum of all chain values for one first-layer head. -/
noncomputable def cascadeHeadValue {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) : ℝ :=
  ∑ χ : CascadeChain m k, cascadeChainValue θ h χ

/-- Headwise sum-of-squares certificate. -/
def CascadeHeadCertificate {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) : Prop :=
  cascadeHeadValue θ h ≠ 0

/-- Every first-layer head satisfies the sum-of-squares cascade certificate. -/
def CascadeCertificate {m k d : Nat} (θ : Params (m + 1) k d) : Prop :=
  ∀ h : Fin k, CascadeHeadCertificate θ h

/-! ## Semantic witness data (equivalence deferred to NS055) -/

/-- Semantic condition for one fixed chain: nonzero final residue and nonzero
ignition at every later layer. -/
structure CascadeChainSemanticData {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (χ : CascadeChain m k) : Prop where
  final_residue_ne_zero : cascadeFinalProduct θ h χ ≠ 0
  ignition_ne_zero : ∀ j : Fin m, cascadeIgnitionMatrix θ h χ j ≠ 0

/-- A selected semantic chain for one first-layer head. -/
structure CascadeHeadSemanticData {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) where
  chain : CascadeChain m k
  semantic : CascadeChainSemanticData θ h chain

/-- Propositional form of the headwise semantic certificate. -/
def CascadeHeadSemantics {m k d : Nat} (θ : Params (m + 1) k d)
    (h : Fin k) : Prop :=
  ∃ χ : CascadeChain m k, CascadeChainSemanticData θ h χ

/-- Propositional semantic certificate for every first-layer head. -/
def CascadeCertificateSemantics {m k d : Nat}
    (θ : Params (m + 1) k d) : Prop :=
  ∀ h : Fin k, CascadeHeadSemantics θ h

/-- Constructor-friendly semantic package selecting one chain per first-layer
head. -/
structure CascadeCertificateSemanticData {m k d : Nat}
    (θ : Params (m + 1) k d) where
  head : ∀ h : Fin k, CascadeHeadSemanticData θ h

/-! ## Sum-of-squares certificate semantics -/

theorem cascadeMatrixFrobSq_eq_zero_iff {r c : Nat}
    (M : Matrix (Fin r) (Fin c) ℝ) :
    cascadeMatrixFrobSq M = 0 ↔ M = 0 := by
  constructor
  · intro hM
    ext i j
    have hrow : (∑ j : Fin c, M i j * M i j) = 0 := by
      exact
        ((Finset.sum_eq_zero_iff_of_nonneg
          (s := (Finset.univ : Finset (Fin r)))
          (f := fun i : Fin r => ∑ j : Fin c, M i j * M i j)
          (fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg (M i j))).mp hM)
          i (Finset.mem_univ i)
    have hentry : M i j * M i j = 0 := by
      exact
        ((Finset.sum_eq_zero_iff_of_nonneg
          (s := (Finset.univ : Finset (Fin c)))
          (f := fun j : Fin c => M i j * M i j)
          (fun j _ => mul_self_nonneg (M i j))).mp hrow)
          j (Finset.mem_univ j)
    exact mul_self_eq_zero.mp hentry
  · rintro rfl
    exact cascadeMatrixFrobSq_zero

theorem cascadeMatrixFrobSq_ne_zero_iff {r c : Nat}
    (M : Matrix (Fin r) (Fin c) ℝ) :
    cascadeMatrixFrobSq M ≠ 0 ↔ M ≠ 0 :=
  not_congr (cascadeMatrixFrobSq_eq_zero_iff M)

theorem cascadeResidueValue_nonneg {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (χ : CascadeChain m k) :
    0 ≤ cascadeResidueValue θ h χ :=
  cascadeMatrixFrobSq_nonneg _

theorem cascadeIgnitionValue_nonneg {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (χ : CascadeChain m k)
    (j : Fin m) :
    0 ≤ cascadeIgnitionValue θ h χ j :=
  cascadeMatrixFrobSq_nonneg _

theorem cascadeChainValue_nonneg {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (χ : CascadeChain m k) :
    0 ≤ cascadeChainValue θ h χ := by
  exact mul_nonneg (cascadeResidueValue_nonneg θ h χ)
    (Finset.prod_nonneg fun j _ => cascadeIgnitionValue_nonneg θ h χ j)

/-- One chain value is nonzero exactly when its final residue and every ignition
matrix are nonzero.  For `m = 0`, the ignition family is empty and this reduces
to nonvanishing of the first-layer value matrix. -/
theorem cascadeChainValue_ne_zero_iff_semantic {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) (χ : CascadeChain m k) :
    cascadeChainValue θ h χ ≠ 0 ↔ CascadeChainSemanticData θ h χ := by
  constructor
  · intro hchain
    have hresValue : cascadeResidueValue θ h χ ≠ 0 := by
      intro hzero
      exact hchain (by simp [cascadeChainValue, hzero])
    have hignProduct :
        (∏ j : Fin m, cascadeIgnitionValue θ h χ j) ≠ 0 := by
      intro hzero
      exact hchain (by simp [cascadeChainValue, hzero])
    refine ⟨(cascadeMatrixFrobSq_ne_zero_iff _).mp hresValue, ?_⟩
    intro j
    have hj : cascadeIgnitionValue θ h χ j ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hignProduct) j (Finset.mem_univ j)
    exact (cascadeMatrixFrobSq_ne_zero_iff _).mp hj
  · intro hsemantic
    apply mul_ne_zero
    · exact (cascadeMatrixFrobSq_ne_zero_iff _).2
        hsemantic.final_residue_ne_zero
    · exact Finset.prod_ne_zero_iff.mpr fun j _ =>
        (cascadeMatrixFrobSq_ne_zero_iff _).2 (hsemantic.ignition_ne_zero j)

/-- A nonzero headwise sum of nonnegative chain values is equivalent to the
existence of one nonzero chain value. -/
theorem cascadeHeadValue_ne_zero_iff_exists_chainValue_ne_zero {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) :
    cascadeHeadValue θ h ≠ 0 ↔
      ∃ χ : CascadeChain m k, cascadeChainValue θ h χ ≠ 0 := by
  constructor
  · intro hsum
    by_contra hnone
    simp only [not_exists, not_not] at hnone
    apply hsum
    simp [cascadeHeadValue, hnone]
  · rintro ⟨χ, hχ⟩ hsum
    have hall : ∀ ψ ∈ (Finset.univ : Finset (CascadeChain m k)),
        cascadeChainValue θ h ψ = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (s := (Finset.univ : Finset (CascadeChain m k)))
        (f := fun ψ => cascadeChainValue θ h ψ)
        (fun ψ _ => cascadeChainValue_nonneg θ h ψ)).mp (by
          simpa [cascadeHeadValue] using hsum)
    exact hχ (hall χ (Finset.mem_univ χ))

/-- Headwise numeric certificate iff existence of a semantic chain. -/
theorem cascadeHeadCertificate_iff_semantics {m k d : Nat}
    (θ : Params (m + 1) k d) (h : Fin k) :
    CascadeHeadCertificate θ h ↔ CascadeHeadSemantics θ h := by
  rw [CascadeHeadCertificate, CascadeHeadSemantics,
    cascadeHeadValue_ne_zero_iff_exists_chainValue_ne_zero]
  constructor
  · rintro ⟨χ, hχ⟩
    exact ⟨χ, (cascadeChainValue_ne_zero_iff_semantic θ h χ).1 hχ⟩
  · rintro ⟨χ, hχ⟩
    exact ⟨χ, (cascadeChainValue_ne_zero_iff_semantic θ h χ).2 hχ⟩

/-- Full numeric cascade certificate iff every first-layer head has a semantic
chain witness.  When `k = 0`, both sides are honestly vacuous. -/
theorem cascadeCertificate_iff_semantics {m k d : Nat}
    (θ : Params (m + 1) k d) :
    CascadeCertificate θ ↔ CascadeCertificateSemantics θ := by
  constructor
  · intro hcert h
    exact (cascadeHeadCertificate_iff_semantics θ h).1 (hcert h)
  · intro hsem h
    exact (cascadeHeadCertificate_iff_semantics θ h).2 (hsem h)

namespace CascadeHeadSemanticData

/-- Forget a selected chain package to the propositional head semantics. -/
theorem toSemantics {m k d : Nat} {θ : Params (m + 1) k d} {h : Fin k}
    (D : CascadeHeadSemanticData θ h) :
    CascadeHeadSemantics θ h :=
  ⟨D.chain, D.semantic⟩

/-- Select constructor-friendly head data from propositional semantics. -/
noncomputable def ofSemantics {m k d : Nat} {θ : Params (m + 1) k d}
    {h : Fin k} (hsem : CascadeHeadSemantics θ h) :
    CascadeHeadSemanticData θ h :=
  ⟨Classical.choose hsem, Classical.choose_spec hsem⟩

end CascadeHeadSemanticData

namespace CascadeCertificateSemanticData

/-- Forget selected chains to the propositional full semantics. -/
theorem toSemantics {m k d : Nat} {θ : Params (m + 1) k d}
    (D : CascadeCertificateSemanticData θ) :
    CascadeCertificateSemantics θ :=
  fun h => (D.head h).toSemantics

/-- Selected semantic data implies the numeric certificate. -/
theorem toCertificate {m k d : Nat} {θ : Params (m + 1) k d}
    (D : CascadeCertificateSemanticData θ) :
    CascadeCertificate θ :=
  (cascadeCertificate_iff_semantics θ).2 D.toSemantics

/-- Select one semantic chain per head from the numeric certificate. -/
noncomputable def ofCertificate {m k d : Nat} {θ : Params (m + 1) k d}
    (hcert : CascadeCertificate θ) :
    CascadeCertificateSemanticData θ where
  head h := CascadeHeadSemanticData.ofSemantics
    ((cascadeHeadCertificate_iff_semantics θ h).1 (hcert h))

end CascadeCertificateSemanticData

/-- Numeric certificate iff constructor-friendly semantic data is inhabited. -/
theorem cascadeCertificate_iff_nonempty_semanticData {m k d : Nat}
    (θ : Params (m + 1) k d) :
    CascadeCertificate θ ↔ Nonempty (CascadeCertificateSemanticData θ) := by
  constructor
  · intro hcert
    exact ⟨CascadeCertificateSemanticData.ofCertificate hcert⟩
  · rintro ⟨D⟩
    exact D.toCertificate

/-! ## Input-gauge covariance -/

/-- Interface realization of the TeX input action: the input interface is
`G⁻¹`, while every output/deeper interface is the identity.  Consequently the
first-layer heads transform as `(V G, Gᵀ A G)` and deeper layers are unchanged.
-/
noncomputable def cascadeInputGaugeInterfaces (m d : Nat) (G : GaugeMatrix d) :
    InterfaceGaugeChain (m + 1) d :=
  Fin.cases G⁻¹ (fun _ => 1)

@[simp] theorem cascadeInputGaugeInterfaces_zero {m d : Nat}
    (G : GaugeMatrix d) :
    cascadeInputGaugeInterfaces m d G 0 = G⁻¹ :=
  rfl

@[simp] theorem cascadeInputGaugeInterfaces_succ {m d : Nat}
    (G : GaugeMatrix d) (i : Fin (m + 1)) :
    cascadeInputGaugeInterfaces m d G i.succ = 1 :=
  rfl

/-- Parameter action induced by `cascadeInputGaugeInterfaces`. -/
noncomputable def cascadeInputGaugeAction {m k d : Nat} (G : GaugeMatrix d)
    (θ : Params (m + 1) k d) : Params (m + 1) k d :=
  gaugeAction (cascadeInputGaugeInterfaces m d G) θ

@[simp] theorem valueMatrix_cascadeInputGaugeAction_zero {m k d : Nat}
    (G : GaugeMatrix d) (θ : Params (m + 1) k d) (a : Fin k) :
    valueMatrix (cascadeInputGaugeAction G θ) 0 a =
      valueMatrix θ 0 a * G.matrix := by
  rw [cascadeInputGaugeAction, valueMatrix_gaugeAction]
  change
    (cascadeInputGaugeInterfaces m d G (0 : Fin (m + 1)).succ).matrix *
          valueMatrix θ 0 a *
          (cascadeInputGaugeInterfaces m d G 0).invMatrix =
      valueMatrix θ 0 a * G.matrix
  rw [cascadeInputGaugeInterfaces_succ, cascadeInputGaugeInterfaces_zero,
    GaugeMatrix.invMatrix_inv]
  simp

@[simp] theorem attentionMatrix_cascadeInputGaugeAction_zero {m k d : Nat}
    (G : GaugeMatrix d) (θ : Params (m + 1) k d) (a : Fin k) :
    attentionMatrix (cascadeInputGaugeAction G θ) 0 a =
      G.matrixᵀ * attentionMatrix θ 0 a * G.matrix := by
  rw [cascadeInputGaugeAction, attentionMatrix_gaugeAction]
  change
    (cascadeInputGaugeInterfaces m d G 0).invTranspose *
          attentionMatrix θ 0 a *
          (cascadeInputGaugeInterfaces m d G 0).invMatrix =
      G.matrixᵀ * attentionMatrix θ 0 a * G.matrix
  rw [cascadeInputGaugeInterfaces_zero, GaugeMatrix.invTranspose,
    GaugeMatrix.invMatrix_inv]

@[simp] theorem cascadeInputGaugeAction_succ {m k d : Nat}
    (G : GaugeMatrix d) (θ : Params (m + 1) k d)
    (l : Fin m) (a : Fin k) :
    cascadeInputGaugeAction G θ l.succ a = θ l.succ a := by
  apply Prod.ext
  · change valueMatrix (cascadeInputGaugeAction G θ) l.succ a =
      valueMatrix θ l.succ a
    rw [cascadeInputGaugeAction, valueMatrix_gaugeAction]
    rw [Fin.castSucc_succ, cascadeInputGaugeInterfaces_succ,
      cascadeInputGaugeInterfaces_succ]
    simp
  · change attentionMatrix (cascadeInputGaugeAction G θ) l.succ a =
      attentionMatrix θ l.succ a
    rw [cascadeInputGaugeAction, attentionMatrix_gaugeAction]
    rw [Fin.castSucc_succ, cascadeInputGaugeInterfaces_succ]
    simp [GaugeMatrix.invTranspose]

@[simp] theorem valueMatrix_cascadeInputGaugeAction_succ {m k d : Nat}
    (G : GaugeMatrix d) (θ : Params (m + 1) k d)
    (l : Fin m) (a : Fin k) :
    valueMatrix (cascadeInputGaugeAction G θ) l.succ a =
      valueMatrix θ l.succ a := by
  exact congrArg Prod.fst (cascadeInputGaugeAction_succ G θ l a)

@[simp] theorem attentionMatrix_cascadeInputGaugeAction_succ {m k d : Nat}
    (G : GaugeMatrix d) (θ : Params (m + 1) k d)
    (l : Fin m) (a : Fin k) :
    attentionMatrix (cascadeInputGaugeAction G θ) l.succ a =
      attentionMatrix θ l.succ a := by
  exact congrArg Prod.snd (cascadeInputGaugeAction_succ G θ l a)

@[simp] theorem valueMatrix_cascadeInputGaugeAction_laterLayer {m k d : Nat}
    (G : GaugeMatrix d) (θ : Params (m + 1) k d)
    (l : Fin m) (a : Fin k) :
    valueMatrix (cascadeInputGaugeAction G θ) (laterLayer l) a =
      valueMatrix θ (laterLayer l) a := by
  change valueMatrix (cascadeInputGaugeAction G θ) l.succ a =
    valueMatrix θ l.succ a
  exact valueMatrix_cascadeInputGaugeAction_succ G θ l a

@[simp] theorem attentionMatrix_cascadeInputGaugeAction_laterLayer {m k d : Nat}
    (G : GaugeMatrix d) (θ : Params (m + 1) k d)
    (l : Fin m) (a : Fin k) :
    attentionMatrix (cascadeInputGaugeAction G θ) (laterLayer l) a =
      attentionMatrix θ (laterLayer l) a := by
  change attentionMatrix (cascadeInputGaugeAction G θ) l.succ a =
    attentionMatrix θ l.succ a
  exact attentionMatrix_cascadeInputGaugeAction_succ G θ l a

/-- TeX covariance `P̃_j^{h,χ} = P_j^{h,χ} G`. -/
theorem cascadeProduct_cascadeInputGaugeAction {m k d : Nat}
    (G : GaugeMatrix d) (θ : Params (m + 1) k d)
    (h : Fin k) (χ : CascadeChain m k) (n : Nat) :
    cascadeProduct (cascadeInputGaugeAction G θ) h χ n =
      cascadeProduct θ h χ n * G.matrix := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      by_cases hn : n < m
      · rw [cascadeProduct_succ_of_lt _ _ _ hn,
          cascadeProduct_succ_of_lt _ _ _ hn]
        rw [valueMatrix_cascadeInputGaugeAction_laterLayer, ih]
        simp [Matrix.mul_assoc]
      · rw [cascadeProduct_succ_of_not_lt _ _ _ hn,
          cascadeProduct_succ_of_not_lt _ _ _ hn, ih]

/-- Final-residue covariance `P̃_m = P_m G`. -/
theorem cascadeFinalProduct_cascadeInputGaugeAction {m k d : Nat}
    (G : GaugeMatrix d) (θ : Params (m + 1) k d)
    (h : Fin k) (χ : CascadeChain m k) :
    cascadeFinalProduct (cascadeInputGaugeAction G θ) h χ =
      cascadeFinalProduct θ h χ * G.matrix :=
  cascadeProduct_cascadeInputGaugeAction G θ h χ m

/-- Symmetric-part covariance under congruence. -/
theorem sym_transpose_mul_mul {d : Nat}
    (G M : Matrix (Fin d) (Fin d) ℝ) :
    sym (Gᵀ * M * G) = Gᵀ * sym M * G := by
  simp only [KHead.sym]
  rw [show (Gᵀ * M * G)ᵀ = Gᵀ * Mᵀ * G by
    simp [Matrix.transpose_mul, Matrix.mul_assoc]]
  simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

/-- TeX covariance `M̃_j^{h,χ} = Gᵀ M_j^{h,χ} G`. -/
theorem cascadeIgnitionMatrix_cascadeInputGaugeAction {m k d : Nat}
    (G : GaugeMatrix d) (θ : Params (m + 1) k d)
    (h : Fin k) (χ : CascadeChain m k) (j : Fin m) :
    cascadeIgnitionMatrix (cascadeInputGaugeAction G θ) h χ j =
      G.matrixᵀ * cascadeIgnitionMatrix θ h χ j * G.matrix := by
  unfold cascadeIgnitionMatrix
  rw [cascadeProduct_cascadeInputGaugeAction,
    attentionMatrix_cascadeInputGaugeAction_laterLayer]
  rw [Matrix.transpose_mul]
  calc
    sym ((G.matrixᵀ * (cascadeProduct θ h χ j.val)ᵀ) *
          attentionMatrix θ (laterLayer j) (χ j) *
          (cascadeProduct θ h χ j.val * G.matrix)) =
        sym (G.matrixᵀ *
          ((cascadeProduct θ h χ j.val)ᵀ *
            attentionMatrix θ (laterLayer j) (χ j) *
              cascadeProduct θ h χ j.val) * G.matrix) := by
            congr 1
            noncomm_ring
    _ = G.matrixᵀ *
          sym ((cascadeProduct θ h χ j.val)ᵀ *
            attentionMatrix θ (laterLayer j) (χ j) *
              cascadeProduct θ h χ j.val) * G.matrix :=
      sym_transpose_mul_mul G.matrix _

/-- Right multiplication by an invertible gauge matrix is injective. -/
theorem right_mul_gaugeMatrix_injective {d : Nat} (G : GaugeMatrix d) :
    Function.Injective
      (fun M : Matrix (Fin d) (Fin d) ℝ => M * G.matrix) := by
  intro M N hMN
  have h := congrArg (fun X => X * G.invMatrix) hMN
  simpa [Matrix.mul_assoc] using h

theorem right_mul_gaugeMatrix_ne_zero_iff {d : Nat} (G : GaugeMatrix d)
    (M : Matrix (Fin d) (Fin d) ℝ) :
    M * G.matrix ≠ 0 ↔ M ≠ 0 := by
  constructor
  · intro hMG hM
    exact hMG (by simp [hM])
  · intro hM hMG
    apply hM
    apply right_mul_gaugeMatrix_injective G
    simpa using hMG

theorem gauge_congruence_ne_zero_iff {d : Nat} (G : GaugeMatrix d)
    (M : Matrix (Fin d) (Fin d) ℝ) :
    G.matrixᵀ * M * G.matrix ≠ 0 ↔ M ≠ 0 := by
  constructor
  · intro hGM hM
    exact hGM (by simp [hM])
  · intro hM hGM
    apply hM
    apply gauge_congruence_injective G
    simpa using hGM

/-- A fixed chain has semantic residue/ignition data before the input gauge iff
it has the same semantic data after the input gauge. -/
theorem cascadeChainSemantics_inputGauge_iff {m k d : Nat}
    (G : GaugeMatrix d) (θ : Params (m + 1) k d)
    (h : Fin k) (χ : CascadeChain m k) :
    CascadeChainSemanticData (cascadeInputGaugeAction G θ) h χ ↔
      CascadeChainSemanticData θ h χ := by
  constructor
  · intro hsem
    refine ⟨?_, ?_⟩
    · have hres := hsem.final_residue_ne_zero
      rw [cascadeFinalProduct_cascadeInputGaugeAction,
        right_mul_gaugeMatrix_ne_zero_iff] at hres
      exact hres
    · intro j
      have hj := hsem.ignition_ne_zero j
      rw [cascadeIgnitionMatrix_cascadeInputGaugeAction,
        gauge_congruence_ne_zero_iff] at hj
      exact hj
  · intro hsem
    refine ⟨?_, ?_⟩
    · rw [cascadeFinalProduct_cascadeInputGaugeAction,
        right_mul_gaugeMatrix_ne_zero_iff]
      exact hsem.final_residue_ne_zero
    · intro j
      rw [cascadeIgnitionMatrix_cascadeInputGaugeAction,
        gauge_congruence_ne_zero_iff]
      exact hsem.ignition_ne_zero j

/-- Headwise semantic cascade invariance under the TeX input gauge. -/
theorem cascadeHeadSemantics_inputGauge_iff {m k d : Nat}
    (G : GaugeMatrix d) (θ : Params (m + 1) k d) (h : Fin k) :
    CascadeHeadSemantics (cascadeInputGaugeAction G θ) h ↔
      CascadeHeadSemantics θ h := by
  constructor
  · rintro ⟨χ, hχ⟩
    exact ⟨χ, (cascadeChainSemantics_inputGauge_iff G θ h χ).1 hχ⟩
  · rintro ⟨χ, hχ⟩
    exact ⟨χ, (cascadeChainSemantics_inputGauge_iff G θ h χ).2 hχ⟩

/-- Full semantic cascade invariance under the TeX input gauge. -/
theorem cascadeCertificateSemantics_inputGauge_iff {m k d : Nat}
    (G : GaugeMatrix d) (θ : Params (m + 1) k d) :
    CascadeCertificateSemantics (cascadeInputGaugeAction G θ) ↔
      CascadeCertificateSemantics θ := by
  constructor <;> intro hsem h
  · exact (cascadeHeadSemantics_inputGauge_iff G θ h).1 (hsem h)
  · exact (cascadeHeadSemantics_inputGauge_iff G θ h).2 (hsem h)

/-- Headwise numeric certificate invariance, deduced through NS055 semantics. -/
theorem cascadeHeadCertificate_inputGauge_iff {m k d : Nat}
    (G : GaugeMatrix d) (θ : Params (m + 1) k d) (h : Fin k) :
    CascadeHeadCertificate (cascadeInputGaugeAction G θ) h ↔
      CascadeHeadCertificate θ h := by
  rw [cascadeHeadCertificate_iff_semantics,
    cascadeHeadCertificate_iff_semantics,
    cascadeHeadSemantics_inputGauge_iff]

/-- Full numeric cascade-certificate invariance under the TeX input gauge. -/
theorem cascadeCertificate_inputGauge_iff {m k d : Nat}
    (G : GaugeMatrix d) (θ : Params (m + 1) k d) :
    CascadeCertificate (cascadeInputGaugeAction G θ) ↔
      CascadeCertificate θ := by
  rw [cascadeCertificate_iff_semantics, cascadeCertificate_iff_semantics,
    cascadeCertificateSemantics_inputGauge_iff]

/-! ## Explicit cascade witness -/

/-- Simultaneous cascade witness: every value and attention matrix in every
layer/head is the identity.  In particular, no head is made zero. -/
def cascadeIdentityWitness (m k d : Nat) : Params (m + 1) k d :=
  fun _l _a =>
    ((1 : Matrix (Fin d) (Fin d) ℝ),
      (1 : Matrix (Fin d) (Fin d) ℝ))

@[simp] theorem valueMatrix_cascadeIdentityWitness {m k d : Nat}
    (l : Fin (m + 1)) (a : Fin k) :
    valueMatrix (cascadeIdentityWitness m k d) l a = 1 :=
  rfl

@[simp] theorem attentionMatrix_cascadeIdentityWitness {m k d : Nat}
    (l : Fin (m + 1)) (a : Fin k) :
    attentionMatrix (cascadeIdentityWitness m k d) l a = 1 :=
  rfl

/-- Canonical chain for a head, selecting that same head at every later layer. -/
def cascadeCanonicalChain {m k : Nat} (h : Fin k) : CascadeChain m k :=
  fun _ => h

/-- A positive-dimensional identity matrix is nonzero. -/
theorem identityMatrix_ne_zero_of_pos {d : Nat} (hd : 0 < d) :
    (1 : Matrix (Fin d) (Fin d) ℝ) ≠ 0 := by
  let i : Fin d := ⟨0, hd⟩
  intro hzero
  have hii := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M i i) hzero
  simp [i] at hii

/-- Every bounded prefix product of the identity witness is the identity, for
every chain—not merely the canonical one. -/
theorem cascadeProduct_cascadeIdentityWitness_eq_one {m k d : Nat}
    (h : Fin k) (χ : CascadeChain m k) :
    ∀ n : Nat, n ≤ m →
      cascadeProduct (cascadeIdentityWitness m k d) h χ n = 1 := by
  intro n hn
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hnm : n < m := Nat.lt_of_succ_le hn
      rw [cascadeProduct_succ_of_lt _ _ _ hnm, ih (Nat.le_of_lt hnm)]
      simp

@[simp] theorem cascadeFinalProduct_cascadeIdentityWitness {m k d : Nat}
    (h : Fin k) (χ : CascadeChain m k) :
    cascadeFinalProduct (cascadeIdentityWitness m k d) h χ = 1 := by
  exact cascadeProduct_cascadeIdentityWitness_eq_one h χ m le_rfl

@[simp] theorem cascadeIgnitionMatrix_cascadeIdentityWitness {m k d : Nat}
    (h : Fin k) (χ : CascadeChain m k) (j : Fin m) :
    cascadeIgnitionMatrix (cascadeIdentityWitness m k d) h χ j = 1 := by
  have hp : cascadeProduct (cascadeIdentityWitness m k d) h χ j.val = 1 :=
    cascadeProduct_cascadeIdentityWitness_eq_one (d := d) h χ j.val
      (Nat.le_of_lt j.isLt)
  have hsym : sym (1 : Matrix (Fin d) (Fin d) ℝ) = 1 := by
    ext a b
    by_cases hab : a = b
    · subst b
      simp [sym]
      ring
    · have hba : b ≠ a := Ne.symm hab
      simp [sym, hab, hba]
  simp [cascadeIgnitionMatrix, hp, hsym]

/-- Every chain of the identity witness has nonzero final residue and ignition
matrices when `d > 0`. -/
theorem cascadeChainSemanticData_cascadeIdentityWitness {m k d : Nat}
    (hd : 0 < d) (h : Fin k) (χ : CascadeChain m k) :
    CascadeChainSemanticData (cascadeIdentityWitness m k d) h χ := by
  refine ⟨?_, ?_⟩
  · rw [cascadeFinalProduct_cascadeIdentityWitness]
    exact identityMatrix_ne_zero_of_pos hd
  · intro j
    rw [cascadeIgnitionMatrix_cascadeIdentityWitness]
    exact identityMatrix_ne_zero_of_pos hd

/-- Selected-chain semantic data for the identity witness. -/
def cascadeIdentityWitnessSemanticData (m k d : Nat) (hd : 0 < d) :
    CascadeCertificateSemanticData (cascadeIdentityWitness m k d) where
  head h :=
    { chain := cascadeCanonicalChain h
      semantic := cascadeChainSemanticData_cascadeIdentityWitness
        hd h (cascadeCanonicalChain h) }

/-- The identity construction satisfies the full semantic cascade certificate.
This is vacuous, rather than exceptional, when `k = 0`. -/
theorem cascadeIdentityWitness_semantics (m k d : Nat) (hd : 0 < d) :
    CascadeCertificateSemantics (cascadeIdentityWitness m k d) :=
  (cascadeIdentityWitnessSemanticData m k d hd).toSemantics

/-- The identity construction satisfies every numeric headwise cascade
certificate simultaneously. -/
theorem cascadeIdentityWitness_certificate (m k d : Nat) (hd : 0 < d) :
    CascadeCertificate (cascadeIdentityWitness m k d) :=
  (cascadeCertificate_iff_semantics _).2
    (cascadeIdentityWitness_semantics m k d hd)

/-- Cascade-certificate satisfiability in every positive hidden dimension, for
all later-layer counts and all head counts. -/
theorem exists_cascadeCertificate (m k d : Nat) (hd : 0 < d) :
    ∃ θ : Params (m + 1) k d, CascadeCertificate θ :=
  ⟨cascadeIdentityWitness m k d,
    cascadeIdentityWitness_certificate m k d hd⟩

/-! ## Target cascade API -/

/-- Compact target-only cascade interface for Step 1 and the genericity cover.

The package carries a certificate on one target parameter together with its
equivalent semantic forms and the two input-gauge invariance statements.  It has
no source parameter and hence cannot impose source-side genericity.
-/
structure TargetCascadePackage {m k d : Nat}
    (θ : Params (m + 1) k d) : Prop where
  certificate : CascadeCertificate θ
  semantics : CascadeCertificateSemantics θ
  semanticData : Nonempty (CascadeCertificateSemanticData θ)
  certificate_inputGauge_iff :
    ∀ G : GaugeMatrix d,
      CascadeCertificate (cascadeInputGaugeAction G θ) ↔ CascadeCertificate θ
  semantics_inputGauge_iff :
    ∀ G : GaugeMatrix d,
      CascadeCertificateSemantics (cascadeInputGaugeAction G θ) ↔
        CascadeCertificateSemantics θ

/-- A target cascade certificate supplies its complete compact API. -/
theorem targetCascadePackage_of_certificate {m k d : Nat}
    {θ : Params (m + 1) k d} (h : CascadeCertificate θ) :
    TargetCascadePackage θ where
  certificate := h
  semantics := (cascadeCertificate_iff_semantics θ).mp h
  semanticData := (cascadeCertificate_iff_nonempty_semanticData θ).mp h
  certificate_inputGauge_iff := fun G => cascadeCertificate_inputGauge_iff G θ
  semantics_inputGauge_iff := fun G => cascadeCertificateSemantics_inputGauge_iff G θ

/-- The compact package adds no hypothesis beyond the target cascade certificate. -/
theorem targetCascadePackage_iff {m k d : Nat} (θ : Params (m + 1) k d) :
    TargetCascadePackage θ ↔ CascadeCertificate θ :=
  ⟨TargetCascadePackage.certificate, targetCascadePackage_of_certificate⟩

/-- Package-level properness witness consumed by the genericity cover. -/
theorem exists_targetCascadePackage (m k d : Nat) (hd : 0 < d) :
    ∃ θ : Params (m + 1) k d, TargetCascadePackage θ :=
  ⟨cascadeIdentityWitness m k d,
    targetCascadePackage_of_certificate
      (cascadeIdentityWitness_certificate m k d hd)⟩

end TransformerIdentifiability.NLayer.NoSkip
