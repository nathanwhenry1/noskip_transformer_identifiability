import AnyLayerIdentifiabilityProof.NLayer.Analytic.SlopePaths

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer

open Matrix

/-!
# Anchor and genericity interfaces

Target contents:
* anchor sets `M_L`
* anchor certificate interface used by genericity condition `(G4)`
* genericity sets `G^(L)`
* statement interfaces for `ID_L` and the main theorem

This pulls the certificate interface earlier than the TeX order so later Lean
files can refer to a concrete genericity predicate without forward references.

Corresponds to `n_layer_proof.tex`, Section 3, with certificate definitions from
Section 8 staged here as declarations/definitions when formalized.
-/

/-- A constant probe pair used by the anchor/genericity interfaces.  This upstream
alias avoids depending on Step 1's concrete probe-region shard. -/
abbrev AnchorProbe (d : Nat) : Type :=
  (Fin d -> ℝ) × (Fin d -> ℝ)

/-! ## Anchor transport and unwinding interfaces -/

/-- A finite parameter tuple, viewed as a `Nat`-indexed layer stream with zero fallback
outside the declared depth.  This mirrors the formal-stream APIs in `SlopePaths.lean`
without depending on Step 1's `paramStream` helper. -/
noncomputable def anchorParamStream {L d : Nat} (θ : Params L d) :
    Nat -> Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ :=
  fun n => if h : n < L then θ ⟨n, h⟩ else (0, 0)

@[simp]
theorem anchorParamStream_apply_of_lt {L d n : Nat} (θ : Params L d) (h : n < L) :
    anchorParamStream θ n = θ ⟨n, h⟩ := by
  simp [anchorParamStream, h]

@[simp]
theorem anchorParamStream_apply_of_not_lt {L d n : Nat} (θ : Params L d)
    (h : ¬ n < L) :
    anchorParamStream θ n = (0, 0) := by
  simp [anchorParamStream, h]

/-- The real matrix `B_k - t V_k` used in the anchor transport map. -/
noncomputable def anchorStepMatrix {d : Nat}
    (θ : Nat -> Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (k : Nat) (t : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  skipB (θ k).1 - t • (θ k).1

/-- One real anchor-transport step
`(w,v) ↦ ((B_k-tV_k)w, B_k v + t V_k w)`, using zero-based layer indexing. -/
noncomputable def anchorStep {d : Nat}
    (θ : Nat -> Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (k : Nat) (t : ℝ) (p : AnchorProbe d) : AnchorProbe d :=
  ((anchorStepMatrix θ k t) *ᵥ p.1,
    skipB (θ k).1 *ᵥ p.2 + t • ((θ k).1 *ᵥ p.1))

/-- Iterated anchor transport along a zero-based gate stream.  The value at `k` is the
TeX point `p_k` after the first `k` gates have been applied. -/
noncomputable def anchorPath {d : Nat}
    (θ : Nat -> Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ) :
    Nat -> (Nat -> ℝ) -> AnchorProbe d -> AnchorProbe d
  | 0, _, p => p
  | k + 1, t, p => anchorStep θ k (t k) (anchorPath θ k t p)

@[simp]
theorem anchorPath_zero {d : Nat}
    (θ : Nat -> Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (t : Nat -> ℝ) (p : AnchorProbe d) :
    anchorPath θ 0 t p = p :=
  rfl

@[simp]
theorem anchorPath_succ {d : Nat}
    (θ : Nat -> Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (k : Nat) (t : Nat -> ℝ) (p : AnchorProbe d) :
    anchorPath θ (k + 1) t p = anchorStep θ k (t k) (anchorPath θ k t p) :=
  rfl

/-- Slope polynomial evaluated on the real transported anchor point `p_k`. -/
noncomputable def anchorSlopeAt {d : Nat}
    (θ : Nat -> Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (k : Nat) (t : Nat -> ℝ) (p : AnchorProbe d) : ℝ :=
  let pk := anchorPath θ k t p
  pk.1 ⬝ᵥ ((θ k).2 *ᵥ pk.2)

/-- The covector `A_k^T w_k - A_k v_k` from the anchor clauses, using zero-based
layer/stage indexing. -/
noncomputable def anchorCovectorAt {d : Nat}
    (θ : Nat -> Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (k : Nat) (t : Nat -> ℝ) (p : AnchorProbe d) : Fin d -> ℝ :=
  let pk := anchorPath θ k t p
  (θ k).2ᵀ *ᵥ pk.1 - (θ k).2 *ᵥ pk.2

/-- The inverse-matrix scalar appearing in clause `(d)` of TeX Lemma `unwind`. -/
noncomputable def anchorInverseScalarAt {d : Nat}
    (θ : Nat -> Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (k : Nat) (t : Nat -> ℝ) (p : AnchorProbe d) : ℝ :=
  let pk := anchorPath θ k t p
  anchorCovectorAt θ k t p ⬝ᵥ
    ((anchorStepMatrix θ k (t k))⁻¹ *ᵥ ((θ k).1 *ᵥ pk.1))

/-- Gate stream used for the TeX expressions
`φ_{k+ell}(t_1,...,t_k,s_k,1,...,1;w,v)`. -/
noncomputable def anchorUnwindGate (t s : Nat -> ℝ) (k : Nat) : Nat -> ℝ :=
  fun n => if n < k then t n else if n = k then s k else 1

/-- Concrete witness data for the right-hand side of TeX Lemma `unwind`.

The indices are zero-based: stage `k` corresponds to TeX `0 ≤ k ≤ L-2`, and
`anchorSlopeAt θ (k + ell - 1)` corresponds to `φ_{k+ell}`. -/
structure AnchorUnwindingData {L d : Nat} (θ : Params L d) (p : AnchorProbe d) where
  t : Nat -> ℝ
  s : Nat -> ℝ
  t_mem_Ioo : ∀ k, k < L - 1 -> t k ∈ Set.Ioo (0 : ℝ) 1
  s_mem_Ioo : ∀ k, k < L - 1 -> s k ∈ Set.Ioo (0 : ℝ) 1
  slope_zero : ∀ k, k < L - 1 -> anchorSlopeAt (anchorParamStream θ) k t p = 0
  attention_image_ne_zero :
    ∀ k, k < L - 1 ->
      let pk := anchorPath (anchorParamStream θ) k t p
      ((anchorParamStream θ k).2)ᵀ *ᵥ pk.1 ≠ 0
  covector_ne_zero :
    ∀ k, k < L - 1 -> anchorCovectorAt (anchorParamStream θ) k t p ≠ 0
  positive_later :
    ∀ k ell, k < L - 1 -> 2 ≤ ell -> k + ell ≤ L ->
      0 < anchorSlopeAt (anchorParamStream θ) (k + ell - 1)
        (anchorUnwindGate t s k) p
  det_step_ne_zero :
    ∀ k, k < L - 1 ->
      (anchorStepMatrix (anchorParamStream θ) k (t k)).det ≠ 0
  inverse_scalar_ne_zero :
    ∀ k, k < L - 1 -> anchorInverseScalarAt (anchorParamStream θ) k t p ≠ 0

/-- The anchor set presented by the unwinding lemma. -/
def unwoundAnchorSet {L d : Nat} (θ : Params L d) : Set (AnchorProbe d) :=
  {p | Nonempty (AnchorUnwindingData θ p)}

@[simp]
theorem mem_unwoundAnchorSet {L d : Nat} {θ : Params L d} {p : AnchorProbe d} :
    p ∈ unwoundAnchorSet θ ↔ Nonempty (AnchorUnwindingData θ p) :=
  Iff.rfl

/-- Interface for a certificate condition that can produce anchors.  The eventual
`(G4)` certificate can instantiate `certificate`; callers needing anchors consume only
`anchors_exist`. -/
structure AnchorCertificateData (L d : Nat) where
  certificate : Params L d -> Prop
  anchorSet : Params L d -> Set (AnchorProbe d)
  anchors_exist : ∀ θ, certificate θ -> (anchorSet θ).Nonempty

namespace AnchorCertificateData

end AnchorCertificateData

/-- A finite intersection of generic parameter conditions.

Later files can instantiate `G i` with polynomial nonvanishing loci, anchor-certificate
loci, or other open dense conditions. -/
def AnchorGenericSet {ι : Type*} {L d : Nat} (I : Finset ι)
    (G : ι -> Set (Params L d)) : Set (Params L d) :=
  ⋂ i ∈ I, G i

@[simp]
theorem mem_anchorGenericSet {ι : Type*} {L d : Nat} {I : Finset ι}
    {G : ι -> Set (Params L d)} {θ : Params L d} :
    θ ∈ AnchorGenericSet I G ↔ ∀ i, i ∈ I -> θ ∈ G i := by
  simp [AnchorGenericSet]

@[simp]
theorem anchorGenericSet_empty {ι : Type*} {L d : Nat}
    (G : ι -> Set (Params L d)) :
    AnchorGenericSet (∅ : Finset ι) G = Set.univ := by
  ext θ
  simp [AnchorGenericSet]

theorem anchorGenericSet_insert {ι : Type*} [DecidableEq ι] {L d : Nat}
    (a : ι) (I : Finset ι) (G : ι -> Set (Params L d)) :
    AnchorGenericSet (insert a I) G = G a ∩ AnchorGenericSet I G := by
  ext θ
  simp [AnchorGenericSet]

theorem isOpen_anchorGenericSet {ι : Type*} {L d : Nat} {I : Finset ι}
    {G : ι -> Set (Params L d)}
    (h : ∀ i, i ∈ I -> IsOpen (G i)) :
    IsOpen (AnchorGenericSet I G) := by
  simpa [AnchorGenericSet] using isOpen_biInter_finset h

theorem dense_anchorGenericSet_of_isOpen_dense {ι : Type*} [DecidableEq ι]
    {L d : Nat} (I : Finset ι) (G : ι -> Set (Params L d))
    (ho : ∀ i, i ∈ I -> IsOpen (G i)) (hd : ∀ i, i ∈ I -> Dense (G i)) :
    Dense (AnchorGenericSet I G) := by
  induction I using Finset.induction_on with
  | empty =>
      simp [AnchorGenericSet]
  | insert a I ha ih =>
      have ho_tail : ∀ i, i ∈ I -> IsOpen (G i) := fun i hi =>
        ho i (Finset.mem_insert_of_mem hi)
      have hd_tail : ∀ i, i ∈ I -> Dense (G i) := fun i hi =>
        hd i (Finset.mem_insert_of_mem hi)
      have htail : Dense (AnchorGenericSet I G) := ih ho_tail hd_tail
      have hmain : Dense (G a ∩ AnchorGenericSet I G) :=
        (hd a (Finset.mem_insert_self a I)).inter_of_isOpen_left htail
          (ho a (Finset.mem_insert_self a I))
      simpa [anchorGenericSet_insert] using hmain

/-- Packaged open dense anchor/generic parameter set.  This is intentionally upstream
of `GenericityMain.IsOpenDense`; downstream files can convert this package to their
preferred generic-open-dense wrapper. -/
structure AnchorGenericData (L d : Nat) where
  carrier : Set (Params L d)
  isOpen_carrier : IsOpen carrier
  dense_carrier : Dense carrier

namespace AnchorGenericData

theorem isOpen {L d : Nat} (G : AnchorGenericData L d) :
    IsOpen G.carrier :=
  G.isOpen_carrier

theorem dense {L d : Nat} (G : AnchorGenericData L d) :
    Dense G.carrier :=
  G.dense_carrier

/-- The whole parameter space as a trivial generic set. -/
def univ (L d : Nat) : AnchorGenericData L d where
  carrier := Set.univ
  isOpen_carrier := isOpen_univ
  dense_carrier := dense_univ

/-- Intersection of two packaged open dense generic sets. -/
def inter {L d : Nat} (G H : AnchorGenericData L d) :
    AnchorGenericData L d where
  carrier := G.carrier ∩ H.carrier
  isOpen_carrier := G.isOpen.inter H.isOpen
  dense_carrier := G.dense.inter_of_isOpen_left H.dense G.isOpen

@[simp]
theorem mem_inter_carrier {L d : Nat} {G H : AnchorGenericData L d}
    {θ : Params L d} :
    θ ∈ (G.inter H).carrier ↔ θ ∈ G.carrier ∧ θ ∈ H.carrier :=
  Iff.rfl

/-- Package a finite family of open dense anchor/generic conditions. -/
def ofFinite {ι : Type*} [DecidableEq ι] {L d : Nat}
    (I : Finset ι) (G : ι -> Set (Params L d))
    (ho : ∀ i, i ∈ I -> IsOpen (G i))
    (hd : ∀ i, i ∈ I -> Dense (G i)) :
    AnchorGenericData L d where
  carrier := AnchorGenericSet I G
  isOpen_carrier := isOpen_anchorGenericSet ho
  dense_carrier := dense_anchorGenericSet_of_isOpen_dense I G ho hd

@[simp]
theorem mem_ofFinite_carrier {ι : Type*} [DecidableEq ι] {L d : Nat}
    {I : Finset ι} {G : ι -> Set (Params L d)}
    {ho : ∀ i, i ∈ I -> IsOpen (G i)}
    {hd : ∀ i, i ∈ I -> Dense (G i)} {θ : Params L d} :
    θ ∈ (ofFinite I G ho hd).carrier ↔ ∀ i, i ∈ I -> θ ∈ G i := by
  simp [ofFinite]

end AnchorGenericData

end TransformerIdentifiability.NLayer
