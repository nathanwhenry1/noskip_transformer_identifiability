import AnyLayerIdentifiabilityProof.NLayer.Foundations.PolynomialGenericity
import AnyLayerIdentifiabilityProof.NLayer.Analytic.AnchorGeneric
import AnyLayerIdentifiabilityProof.NLayer.Step1.OStar

set_option autoImplicit false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace TransformerIdentifiability.NLayer

/-!
# Genericity, witnesses, main theorem, and factor corollary

Target contents:
* composition identity
* unwinding of anchors
* anchor certificate gradients
* existence of anchors
* witness construction
* genericity is the complement of a finite union of proper algebraic sets
* main null-set theorem
* factor-level corollary

Corresponds to `n_layer_proof.tex`, Section 8.
-/

/-- A generic set packaged as both open and dense.  This small predicate is useful when
finite intersections and open-subtype restrictions need to preserve both facts. -/
def IsOpenDense {X : Type*} [TopologicalSpace X] (s : Set X) : Prop :=
  IsOpen s ∧ Dense s

namespace IsOpenDense

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {s t : Set X}

theorem isOpen (h : IsOpenDense s) : IsOpen s :=
  h.1

theorem dense (h : IsOpenDense s) : Dense s :=
  h.2

theorem univ : IsOpenDense (Set.univ : Set X) :=
  ⟨isOpen_univ, dense_univ⟩

theorem inter (hs : IsOpenDense s) (ht : IsOpenDense t) :
    IsOpenDense (s ∩ t) :=
  ⟨hs.isOpen.inter ht.isOpen,
    hs.dense.inter_of_isOpen_left ht.dense hs.isOpen⟩

theorem mono (hs : IsOpenDense s) (hst : s ⊆ t) (ht : IsOpen t) :
    IsOpenDense t :=
  ⟨ht, hs.dense.mono hst⟩

/-- Preimage transport for maps that are continuous and open. -/
theorem preimage {f : X -> Y} {s : Set Y} (hs : IsOpenDense s)
    (hf_cont : Continuous f) (hf_open : IsOpenMap f) :
    IsOpenDense (f ⁻¹' s) :=
  ⟨hs.isOpen.preimage hf_cont, hs.dense.preimage hf_open⟩

/-- An open dense set meets every nonempty open set. -/
theorem inter_open_nonempty (hs : IsOpenDense s) {U : Set X}
    (hU : IsOpen U) (hUne : U.Nonempty) :
    (s ∩ U).Nonempty :=
  (hs.dense.inter_open_nonempty U hU hUne).mono fun _ hx => ⟨hx.2, hx.1⟩

end IsOpenDense

/-! ## Polynomial nonvanishing to open-dense genericity -/

namespace IsOpenDense

/-- The common nonvanishing locus of a packaged finite family of nonzero polynomials is
an open dense set. -/
def ofPolynomialNonvanishingData {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (D : PolynomialNonvanishingData ι κ) :
    IsOpenDense D.carrier :=
  ⟨PolynomialNonvanishingData.isOpen_carrier D,
    PolynomialNonvanishingData.dense_carrier D⟩

end IsOpenDense

namespace PolynomialNonvanishingData

/-- View a packaged finite polynomial nonvanishing family through the local
open-dense interface used by the genericity assembly. -/
theorem isOpenDense_carrier {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (D : PolynomialNonvanishingData ι κ) :
    IsOpenDense D.carrier :=
  IsOpenDense.ofPolynomialNonvanishingData D

/-- A packaged polynomial nonvanishing locus meets every nonempty open set, restated in
the local `IsOpenDense` interface. -/
theorem inter_open_nonempty {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (D : PolynomialNonvanishingData ι κ)
    {U : Set (ι -> ℝ)} (hU : IsOpen U) (hUne : U.Nonempty) :
    (D.carrier ∩ U).Nonempty :=
  D.isOpenDense_carrier.inter_open_nonempty hU hUne

end PolynomialNonvanishingData

namespace IsOpenDense

/-- Convert the local `IsOpenDense` predicate to the upstream `AnchorGenericData`
package used by earlier files. -/
def toAnchorGenericData {L d : Nat} {s : Set (Params L d)} (h : IsOpenDense s) :
    AnchorGenericData L d where
  carrier := s
  isOpen_carrier := h.isOpen
  dense_carrier := h.dense

end IsOpenDense

namespace AnchorGenericData

/-- Build upstream generic data from the local `IsOpenDense` predicate. -/
def ofIsOpenDense {L d : Nat} (s : Set (Params L d)) (h : IsOpenDense s) :
    AnchorGenericData L d :=
  h.toAnchorGenericData

@[simp]
theorem carrier_ofIsOpenDense {L d : Nat} (s : Set (Params L d)) (h : IsOpenDense s) :
    (ofIsOpenDense s h).carrier = s :=
  rfl

end AnchorGenericData

/-! ## TeX genericity clauses and anchor bridges -/

/-- Number of certificate rows in TeX Definition `certificate`,
`N_L = binom(L,2) + 2(L-1)`. -/
def genericCertificateRows (L : Nat) : Nat :=
  Nat.choose L 2 + 2 * (L - 1)

@[simp]
theorem genericCertificateRows_one : genericCertificateRows 1 = 0 := by
  norm_num [genericCertificateRows]

theorem genericCertificateRows_mono_succ (L : Nat) :
    genericCertificateRows L ≤ genericCertificateRows (L + 1) := by
  unfold genericCertificateRows
  have hchoose : Nat.choose L 2 ≤ Nat.choose (L + 1) 2 :=
    Nat.choose_le_choose 2 (Nat.le_succ L)
  omega

/-! ### Exact anchor-certificate condition `(G4)` -/

/-- The finite gate vector `(t_1, ..., t_{L-1})` or `(s_0, ..., s_{L-2})`
from TeX Definition `certificate`, stored with zero-based indices. -/
abbrev AnchorGateVector (L : Nat) : Type :=
  Fin (L - 1) -> ℝ

/-- Extend a finite certificate gate vector to the `Nat`-indexed stream expected by the
formal-recursion helpers.  Values outside the first `L - 1` gates are irrelevant. -/
noncomputable def anchorGateStream {L : Nat} (t : AnchorGateVector L) : Nat -> ℝ :=
  fun n => if h : n < L - 1 then t ⟨n, h⟩ else 0

/-- Real product `B_n ... B_1`, with zero-based stream indexing.  Thus
`anchorRealBprod θ n` uses layers `0, ..., n - 1`. -/
noncomputable def anchorRealBprod {d : Nat} (θ : LayerStream d) :
    Nat -> Matrix (Fin d) (Fin d) ℝ
  | 0 => 1
  | n + 1 => skipB (θ n).1 * anchorRealBprod θ n

/-- Real product `(B_n - t_n V_n) ... (B_1 - t_1 V_1)`, with zero-based stream indexing.
Thus `anchorRealWprod θ t n` is the TeX matrix `W'_n(t_1,...,t_n)`. -/
noncomputable def anchorRealWprod {d : Nat} (θ : LayerStream d) (t : Nat -> ℝ) :
    Nat -> Matrix (Fin d) (Fin d) ℝ
  | 0 => 1
  | n + 1 => anchorStepMatrix θ n (t n) * anchorRealWprod θ t n

/-- The `S_{k,ell}` rows of the anchor certificate, indexed by
`0 <= k <= L - 2` and `2 <= ell <= L - k`. -/
abbrev AnchorCertificateSIndex (L : Nat) : Type :=
  Σ k : Fin (L - 1), {ell : Fin (L + 1) // 2 ≤ ell.val ∧ k.val + ell.val ≤ L}

/-- The `N_L` certificate rows: `E_j`, `S_{k,ell}`, and `T_k`. -/
abbrev AnchorCertificateRow (L : Nat) : Type :=
  (Fin (L - 1) ⊕ AnchorCertificateSIndex L) ⊕ Fin (L - 1)

/-- Squared Euclidean norm of a finite real vector, kept as a polynomial expression. -/
noncomputable def vectorNormSq {d : Nat} (x : Fin d -> ℝ) : ℝ :=
  x ⬝ᵥ x

/-- The transported vector `w_(k) = W'_k(t_1,...,t_k) w^circ` in the anchor certificate. -/
noncomputable def anchorCertificateW {L d : Nat} (θ : Params L d)
    (t : AnchorGateVector L) (k : Nat) (w0 : Fin d -> ℝ) : Fin d -> ℝ :=
  (anchorRealWprod (paramStream θ) (anchorGateStream t) k).mulVec w0

/-- Gradient of the row `E_{k+1}` with respect to `v`. -/
noncomputable def anchorCertificateGradientE {L d : Nat} (θ : Params L d)
    (t : AnchorGateVector L) (k : Fin (L - 1)) (w0 : Fin d -> ℝ) :
    Fin d -> ℝ :=
  (Matrix.transpose (anchorRealBprod (paramStream θ) k.val)).mulVec
    ((Matrix.transpose (paramStream θ k.val).2).mulVec
      (anchorCertificateW θ t k.val w0))

/-- Gradient of the row `S_{k,ell}` with respect to `v`. -/
noncomputable def anchorCertificateGradientS {L d : Nat} (θ : Params L d)
    (t s : AnchorGateVector L) (q : AnchorCertificateSIndex L) (w0 : Fin d -> ℝ) :
    Fin d -> ℝ :=
  let k : Fin (L - 1) := q.1
  let ell : Nat := q.2.1.val
  let n : Nat := k.val + ell - 1
  (Matrix.transpose (anchorRealBprod (paramStream θ) n)).mulVec
    ((Matrix.transpose (paramStream θ n).2).mulVec
      ((anchorStepMatrix (paramStream θ) k.val (s k)).mulVec
        (anchorCertificateW θ t k.val w0)))

/-- Gradient of the row `T_k` with respect to `v`. -/
noncomputable def anchorCertificateGradientT {L d : Nat} (θ : Params L d)
    (t : AnchorGateVector L) (k : Fin (L - 1)) (w0 : Fin d -> ℝ) :
    Fin d -> ℝ :=
  let M := anchorStepMatrix (paramStream θ) k.val (t k)
  let WB := Matrix.transpose (anchorRealBprod (paramStream θ) k.val)
  let AT := Matrix.transpose (paramStream θ k.val).2
  let y := (paramStream θ k.val).1.mulVec (anchorCertificateW θ t k.val w0)
  let z := (Matrix.adjugate M).mulVec y
  let u := AT.mulVec z
  fun i => - (WB.mulVec u i)

/-- Gradient of an arbitrary anchor-certificate row. -/
noncomputable def anchorCertificateGradient {L d : Nat} (θ : Params L d)
    (t s : AnchorGateVector L) (row : AnchorCertificateRow L) (w0 : Fin d -> ℝ) :
    Fin d -> ℝ :=
  match row with
  | Sum.inl (Sum.inl k) => anchorCertificateGradientE θ t k w0
  | Sum.inl (Sum.inr q) => anchorCertificateGradientS θ t s q w0
  | Sum.inr k => anchorCertificateGradientT θ t k w0

/-- The `d x N_L` matrix `𝓖` whose columns are the certificate-row gradients. -/
noncomputable def anchorCertificateGradientMatrix {L d : Nat} (θ : Params L d)
    (t s : AnchorGateVector L) (w0 : Fin d -> ℝ) :
    Matrix (Fin d) (AnchorCertificateRow L) ℝ :=
  Matrix.of fun i row => anchorCertificateGradient θ t s row w0 i

/-- The TeX polynomial `𝔠(theta'; t, s, w^circ)` from Definition `certificate`. -/
noncomputable def anchorCertificateValue {L d : Nat} (θ : Params L d)
    (t s : AnchorGateVector L) (w0 : Fin d -> ℝ) : ℝ :=
  let G := anchorCertificateGradientMatrix θ t s w0
  (Matrix.transpose G * G).det
    * (∏ k : Fin (L - 1),
        (anchorStepMatrix (paramStream θ) k.val (t k)).det)
    * (∏ k : Fin (L - 1),
        vectorNormSq ((Matrix.transpose (paramStream θ k.val).2).mulVec
          (anchorCertificateW θ t k.val w0)))

/-- Exact TeX condition `(G4)`: the anchor-certificate polynomial is not identically zero
as a function of `(t, s, w^circ)`.  Since the expression above is a polynomial, this is
the same condition as nonvanishing at some evaluation point. -/
def TexAnchorCertificate {L d : Nat} (θ : Params L d) : Prop :=
  ∃ t s : AnchorGateVector L, ∃ w0 : Fin d -> ℝ,
    anchorCertificateValue θ t s w0 ≠ 0

/-- Depth-one genericity clauses from TeX Definition `generic`. -/
structure TexGenericBaseClauses (d : Nat) (θ : Params 1 d) : Prop where
  value_ne_zero : (paramStream θ 0).1 ≠ 0
  attention_ne_zero : (paramStream θ 0).2 ≠ 0

/-- The recursive `(G1)`--`(G4)` clauses from TeX Definition `generic`, written for a
positive successor depth `L + 1`.

The `tailGeneric` and `certificate` predicates keep the recursive genericity and
anchor-certificate implementations pluggable while the matrix-level clauses are concrete. -/
structure TexGenericStepClauses (L d : Nat)
    (tailGeneric : Params L d -> Prop)
    (certificate : Params (L + 1) d -> Prop)
    (θ : Params (L + 1) d) : Prop where
  tail_generic : tailGeneric (Fin.tail θ)
  g1_det_firstAttention : (firstAttention θ).det ≠ 0
  g1_sym_firstAttention : symPart (firstAttention θ) ≠ 0
  g2_kappa :
    ∀ j : Nat, 2 ≤ j -> j ≤ L + 1 ->
      kappaMatrix (paramStream θ) (j - 2) ≠ 0
  g2_visible : realVprod (paramStream θ) (L + 1) ≠ 0
  g3_det_firstSkip : (skipB (paramStream θ 0).1).det ≠ 0
  g4_certificate : certificate θ

namespace TexGenericStepClauses

variable {L d : Nat} {tailGeneric : Params L d -> Prop}
variable {certificate : Params (L + 1) d -> Prop} {θ : Params (L + 1) d}

/-- The `(G1)` symmetric-part condition is the matrix-level nonzero fact consumed by
the Step 1 `O_star` genericity interface. -/
theorem firstAttention_ne_zero
    (D : TexGenericStepClauses L d tailGeneric certificate θ) :
    firstAttention θ ≠ 0 := by
  intro hzero
  exact D.g1_sym_firstAttention (by simp [hzero, symPart])

/-- Compile the concrete matrix-level generic clauses `(G1)/(G2)` into the existing
`OStarGenericAssumptions` package used by Step 1. -/
def toOStarGenericAssumptions
    (D : TexGenericStepClauses L d tailGeneric certificate θ)
    {O : Set (ProbePair d)} (hOpenO : IsOpen O) (hNonemptyO : O.Nonempty) :
    OStarGenericAssumptions (L + 1) d θ O :=
  OStarGenericAssumptions.ofMatrixNonzero hOpenO hNonemptyO
    D.firstAttention_ne_zero D.g2_kappa D.g2_visible

end TexGenericStepClauses

/-- Exact recursive TeX genericity predicate `𝓖^(L)` from Definition `generic`.

For `L = 1` this is `V_1 != 0` and `A_1 != 0`.  For `L >= 2` it is recursive
tail genericity plus clauses `(G1)`--`(G4)`, with `(G4)` instantiated by the concrete
anchor certificate above.  The `L = 0` case is a harmless empty-depth fallback. -/
noncomputable def TexGeneric : (L d : Nat) -> Params L d -> Prop
  | 0, _d, _θ => True
  | 1, d, θ => TexGenericBaseClauses d θ
  | L + 2, d, θ =>
      TexGenericStepClauses (L + 1) d (TexGeneric (L + 1) d)
        (fun η => TexAnchorCertificate η) θ

/-- The exact generic parameter set `𝓖^(L)`. -/
def TexGenericSet (L d : Nat) : Set (Params L d) :=
  {θ | TexGeneric L d θ}

/-- The exact bad set complementary to the TeX genericity conditions. -/
def TexGenericBadSet (L d : Nat) : Set (Params L d) :=
  (TexGenericSet L d)ᶜ

@[simp]
theorem mem_TexGenericSet {L d : Nat} {θ : Params L d} :
    θ ∈ TexGenericSet L d ↔ TexGeneric L d θ :=
  Iff.rfl

@[simp]
theorem mem_TexGenericBadSet {L d : Nat} {θ : Params L d} :
    θ ∈ TexGenericBadSet L d ↔ ¬ TexGeneric L d θ :=
  Iff.rfl

@[simp]
theorem texGeneric_one {d : Nat} {θ : Params 1 d} :
    TexGeneric 1 d θ = TexGenericBaseClauses d θ :=
  rfl

@[simp]
theorem texGeneric_succ_succ {L d : Nat} {θ : Params (L + 2) d} :
    TexGeneric (L + 2) d θ =
      TexGenericStepClauses (L + 1) d (TexGeneric (L + 1) d)
        (fun η => TexAnchorCertificate η) θ :=
  rfl

/-! ## Main-theorem and factor-corollary interfaces -/

/-- Equality of the full transformer maps on all inputs of length `r + 1`. -/
def FullTransformerAgreement {L d : Nat} (r : Nat) (θ θ' : Params L d) : Prop :=
  ∀ X : Matrix (Fin d) (Fin (r + 1)) ℝ, transformer θ X = transformer θ' X

/-- Equality of the probe observables on the positive real probe ray. -/
def ProbeObservableAgreement {L d : Nat} (r : Nat) (θ θ' : Params L d) : Prop :=
  ∀ w v : Fin d -> ℝ, ∀ τ : ℝ, 0 < τ -> Fobs r θ w v τ = Fobs r θ' w v τ

/-- Full input equality implies the probe-observable agreement used in the TeX proof of
Theorem `main`. -/
theorem probeObservableAgreement_of_fullTransformerAgreement {L d r : Nat}
    {θ θ' : Params L d} (h : FullTransformerAgreement r θ θ') :
    ProbeObservableAgreement r θ θ' := by
  intro w v τ hτ
  funext i
  simp [Fobs, h (probeInput r w v τ)]

/-- Packaged main-theorem interface: outside a supplied open dense generic set, probe
agreement identifies the parameters.  Later null-set/algebraic work can refine the
generic package without changing callers of this endpoint. -/
structure MainTheoremData (L d r : Nat) where
  generic : AnchorGenericData L d
  identify_of_probe :
    ∀ {θ θ' : Params L d}, θ' ∈ generic.carrier ->
      ProbeObservableAgreement r θ θ' -> θ = θ'

namespace MainTheoremData

/-- The full-transformer statement follows from the probe-only endpoint. -/
theorem identify_of_full {L d r : Nat} (D : MainTheoremData L d r)
    {θ θ' : Params L d} (hθ' : θ' ∈ D.generic.carrier)
    (h : FullTransformerAgreement r θ θ') :
    θ = θ' :=
  D.identify_of_probe hθ' (probeObservableAgreement_of_fullTransformerAgreement h)

end MainTheoremData

/-- One layer of factor parameters from Corollary `factors`. -/
structure FactorLayer (d dv : Nat) where
  W_O : Matrix (Fin d) (Fin dv) ℝ
  W_V : Matrix (Fin dv) (Fin d) ℝ
  W_K : Matrix (Fin d) (Fin d) ℝ
  W_Q : Matrix (Fin d) (Fin d) ℝ

namespace FactorLayer

/-- Polynomial map from one factor layer to its `(V,A)` layer. -/
noncomputable def toLayer {d dv : Nat} (F : FactorLayer d dv) :
    Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ :=
  (F.W_O * F.W_V, Matrix.transpose F.W_K * F.W_Q)

@[simp]
theorem toLayer_fst {d dv : Nat} (F : FactorLayer d dv) :
    F.toLayer.1 = F.W_O * F.W_V :=
  rfl

@[simp]
theorem toLayer_snd {d dv : Nat} (F : FactorLayer d dv) :
    F.toLayer.2 = Matrix.transpose F.W_K * F.W_Q :=
  rfl

end FactorLayer

/-- Factor parameter space for `L` ordered one-head layers. -/
abbrev FactorParams (L d dv : Nat) : Type :=
  Fin L -> FactorLayer d dv

namespace FactorParams

/-- Polynomial map `μ` from factor parameters to the `(V,A)` parameter space. -/
noncomputable def toParams {L d dv : Nat} (F : FactorParams L d dv) : Params L d :=
  fun l => (F l).toLayer

@[simp]
theorem toParams_apply {L d dv : Nat} (F : FactorParams L d dv) (l : Fin L) :
    toParams F l = (F l).toLayer :=
  rfl

end FactorParams

end TransformerIdentifiability.NLayer
