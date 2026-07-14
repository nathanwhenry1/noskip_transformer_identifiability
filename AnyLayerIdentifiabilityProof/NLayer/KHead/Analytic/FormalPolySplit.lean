import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.ActiveStratification

set_option autoImplicit false

open Filter Matrix
open scoped BigOperators

namespace TransformerIdentifiability.NLayer.KHead

/-! ## Chain and coefficient bookkeeping -/

/-- A selected head chain of length `p`, together with the bound placing it in a
depth-`L` parameter family.  Layer `i : Fin p` corresponds to the ambient layer
`⟨i, i < L⟩`. -/
structure HeadChain (L k : Nat) (p : Nat) where
  head : Fin p -> Fin k
  length_le : p ≤ L

namespace HeadChain

/-- The ambient layer attached to a chain position. -/
def layer {L k p : Nat} (c : HeadChain L k p) (i : Fin p) : Fin L :=
  ⟨i.1, Nat.lt_of_lt_of_le i.2 c.length_le⟩

/-- The selected formal variable `ζ_i = z_{i,a_i}`. -/
def selectedVar {L k p : Nat} (c : HeadChain L k p) (i : Fin p) : FormalVar L k :=
  (c.layer i, c.head i)

/-- A formal variable is selected by the chain. -/
def IsSelectedVar {L k p : Nat} (c : HeadChain L k p) (x : FormalVar L k) : Prop :=
  ∃ i : Fin p, x = c.selectedVar i

@[simp] theorem selectedVar_layer {L k p : Nat} (c : HeadChain L k p) (i : Fin p) :
    (c.selectedVar i).1 = c.layer i :=
  rfl

@[simp] theorem selectedVar_head {L k p : Nat} (c : HeadChain L k p) (i : Fin p) :
    (c.selectedVar i).2 = c.head i :=
  rfl

theorem selectedVar_isSelected {L k p : Nat} (c : HeadChain L k p) (i : Fin p) :
    c.IsSelectedVar (c.selectedVar i) :=
  ⟨i, rfl⟩

/-- Matrix product `V_{j,a_j} ... V_{1,a_1}` for the first `n` entries of a
selected chain, with the empty product equal to the identity. -/
noncomputable def selectedValueProduct {L k d p : Nat} (θ : Params L k d)
    (c : HeadChain L k p) : (n : Nat) -> n ≤ p -> Matrix (Fin d) (Fin d) ℝ
  | 0, _ => 1
  | n + 1, hn =>
      valueMatrix θ (c.layer ⟨n, hn⟩) (c.head ⟨n, hn⟩) *
        selectedValueProduct θ c n (Nat.le_of_succ_le hn)

@[simp] theorem selectedValueProduct_zero {L k d p : Nat} (θ : Params L k d)
    (c : HeadChain L k p) (h0 : 0 ≤ p) :
    selectedValueProduct θ c 0 h0 = 1 :=
  rfl

@[simp] theorem selectedValueProduct_succ {L k d p : Nat} (θ : Params L k d)
    (c : HeadChain L k p) {n : Nat} (hn : n + 1 ≤ p) :
    selectedValueProduct θ c (n + 1) hn =
      valueMatrix θ (c.layer ⟨n, hn⟩) (c.head ⟨n, hn⟩) *
        selectedValueProduct θ c n (Nat.le_of_succ_le hn) :=
  rfl

end HeadChain

/-- The exponent vector for a product of selected chain variables with prescribed
exponents. -/
noncomputable def selectedExponent {L k p : Nat} (c : HeadChain L k p)
    (deg : Fin p -> Nat) : FormalVar L k →₀ Nat :=
  Finsupp.equivFunOnFinite.symm fun x =>
    ∑ i : Fin p, if x = c.selectedVar i then deg i else 0

/-- Coefficient of a selected chain monomial in a formal polynomial. -/
noncomputable def selectedCoeff {L k p : Nat} (c : HeadChain L k p)
    (deg : Fin p -> Nat) (f : FormalPoly L k) : ℝ :=
  f.coeff (selectedExponent c deg)

/-- Restriction of an exponent vector to layers at most `n`. -/
def SupportedInLayersLE {L k : Nat} (n : Nat) (m : FormalVar L k →₀ Nat) : Prop :=
  ∀ x : FormalVar L k, n < x.1.1 -> m x = 0

/-- No monomial of `f` uses variables from layers beyond `n`. -/
def PolynomialInLayersLE {L k : Nat} (n : Nat) (f : FormalPoly L k) : Prop :=
  ∀ m ∈ f.support, SupportedInLayersLE (L := L) (k := k) n m

/-- A monomial uses at most one variable from each layer, and only to first power. -/
def MonomialBlockMultiAffine {L k : Nat} (m : FormalVar L k →₀ Nat) : Prop :=
  ∀ l : Fin L, ∃ a? : Option (Fin k),
    ∀ a : Fin k, m (l, a) = if a? = some a then 1 else 0

/-- A polynomial is block-multiaffine in the layer blocks. -/
def BlockMultiAffine {L k : Nat} (f : FormalPoly L k) : Prop :=
  ∀ m ∈ f.support, MonomialBlockMultiAffine (L := L) (k := k) m

/-- Every monomial has total degree at most `D` in each layer block. -/
def BlockDegreeLE {L k : Nat} (D : Nat) (f : FormalPoly L k) : Prop :=
  ∀ m ∈ f.support, ∀ l : Fin L, (∑ a : Fin k, m (l, a)) ≤ D

/-! ## Internal support calculus for `lem:multi-affine` -/

/-- Internal invariant: a monomial only uses layers strictly below `n`. -/
def SupportedInLayersLT {L k : Nat} (n : Nat) (m : FormalVar L k →₀ Nat) : Prop :=
  ∀ x : FormalVar L k, n ≤ x.1.1 -> m x = 0

/-- Internal invariant: a polynomial only uses layers strictly below `n`. -/
def PolynomialInLayersLT {L k : Nat} (n : Nat) (f : FormalPoly L k) : Prop :=
  ∀ m ∈ f.support, SupportedInLayersLT (L := L) (k := k) n m

/-- The invariant used in the formal stream induction. -/
structure LayerBoundedBlockAffine {L k : Nat} (n : Nat) (f : FormalPoly L k) : Prop where
  block : BlockMultiAffine f
  support_lt : PolynomialInLayersLT (L := L) (k := k) n f

theorem support_C_subset_zero {L k : Nat} (c : ℝ) :
    (MvPolynomial.C (σ := FormalVar L k) c).support ⊆
      ({0} : Finset (FormalVar L k →₀ Nat)) := by
  classical
  intro m hm
  by_cases hc : c = 0
  · simp [hc] at hm
  · simpa [MvPolynomial.support_C, hc] using hm

namespace MonomialBlockMultiAffine

theorem zero {L k : Nat} :
    MonomialBlockMultiAffine (L := L) (k := k) (0 : FormalVar L k →₀ Nat) := by
  intro l
  refine ⟨none, ?_⟩
  intro a
  simp

theorem block_sum_le_one {L k : Nat} {m : FormalVar L k →₀ Nat}
    (hm : MonomialBlockMultiAffine (L := L) (k := k) m) (l : Fin L) :
    (∑ a : Fin k, m (l, a)) ≤ 1 := by
  rcases hm l with ⟨a?, ha?⟩
  cases a? with
  | none =>
      have hsum : (∑ a : Fin k, m (l, a)) = 0 := by
        simp [ha?]
      rw [hsum]
      exact Nat.zero_le 1
  | some a0 =>
      have hsum : (∑ a : Fin k, m (l, a)) = 1 := by
        calc
          (∑ a : Fin k, m (l, a))
              = ∑ a : Fin k, (if a0 = a then 1 else 0) := by
                  refine Finset.sum_congr rfl ?_
                  intro a ha
                  simpa using ha? a
          _ = 1 := by simp
      rw [hsum]

theorem add_gate_of_supportedLT {L k n : Nat} {m : FormalVar L k →₀ Nat}
    (hmBlock : MonomialBlockMultiAffine (L := L) (k := k) m)
    (hmSupp : SupportedInLayersLT (L := L) (k := k) n m)
    {l : Fin L} (hl : l.1 = n) (a0 : Fin k) :
    MonomialBlockMultiAffine (L := L) (k := k)
      (Finsupp.single (l, a0) 1 + m) := by
  intro l'
  by_cases hll' : l' = l
  · subst l'
    refine ⟨some a0, ?_⟩
    intro a
    have hmzero : m (l, a) = 0 := by
      apply hmSupp (l, a)
      rw [hl]
    by_cases ha : a0 = a
    · subst a
      simp [hmzero]
    · have hpair : (l, a0) ≠ (l, a) := by
        intro h
        exact ha (Prod.ext_iff.mp h).2
      simp [Finsupp.single_eq_of_ne' hpair, hmzero, ha]
  · rcases hmBlock l' with ⟨a?, ha?⟩
    refine ⟨a?, ?_⟩
    intro a
    have hpair : (l, a0) ≠ (l', a) := by
      intro h
      exact hll' (Prod.ext_iff.mp h).1.symm
    simp [Finsupp.single_eq_of_ne' hpair, ha? a]

end MonomialBlockMultiAffine

namespace SupportedInLayersLT

theorem add {L k n : Nat} {m₁ m₂ : FormalVar L k →₀ Nat}
    (hm₁ : SupportedInLayersLT (L := L) (k := k) n m₁)
    (hm₂ : SupportedInLayersLT (L := L) (k := k) n m₂) :
    SupportedInLayersLT (L := L) (k := k) n (m₁ + m₂) := by
  intro x hx
  simp [hm₁ x hx, hm₂ x hx]

theorem mono {L k n n' : Nat} {m : FormalVar L k →₀ Nat} (hn : n ≤ n')
    (hm : SupportedInLayersLT (L := L) (k := k) n m) :
    SupportedInLayersLT (L := L) (k := k) n' m := by
  intro x hx
  exact hm x (Nat.le_trans hn hx)

theorem to_LE {L k n : Nat} {m : FormalVar L k →₀ Nat}
    (hm : SupportedInLayersLT (L := L) (k := k) n m) :
    SupportedInLayersLE (L := L) (k := k) n m := by
  intro x hx
  exact hm x (Nat.le_of_lt hx)

theorem add_gate {L k n : Nat} {m : FormalVar L k →₀ Nat}
    (hm : SupportedInLayersLT (L := L) (k := k) n m)
    {l : Fin L} (hl : l.1 = n) (a0 : Fin k) :
    SupportedInLayersLT (L := L) (k := k) (n + 1)
      (Finsupp.single (l, a0) 1 + m) := by
  intro x hx
  by_cases hxgate : x = (l, a0)
  · subst x
    have hbad : n + 1 ≤ n := by
      rw [hl] at hx
      exact hx
    exact (Nat.not_succ_le_self n hbad).elim
  · have hsingle : Finsupp.single (l, a0) 1 x = 0 :=
      Finsupp.single_eq_of_ne hxgate
    have hmzero : m x = 0 := hm x (Nat.le_trans (Nat.le_succ n) hx)
    simp [hsingle, hmzero]

end SupportedInLayersLT

namespace SupportedInLayersLE

theorem mono {L k n n' : Nat} {m : FormalVar L k →₀ Nat} (hn : n ≤ n')
    (hm : SupportedInLayersLE (L := L) (k := k) n m) :
    SupportedInLayersLE (L := L) (k := k) n' m := by
  intro x hx
  exact hm x (Nat.lt_of_le_of_lt hn hx)

end SupportedInLayersLE

namespace PolynomialInLayersLE

theorem zero {L k n : Nat} :
    PolynomialInLayersLE (L := L) (k := k) n (0 : FormalPoly L k) := by
  intro m hm
  simp at hm

theorem mono {L k n n' : Nat} {p : FormalPoly L k} (hn : n ≤ n')
    (hp : PolynomialInLayersLE (L := L) (k := k) n p) :
    PolynomialInLayersLE (L := L) (k := k) n' p := by
  intro m hm
  exact SupportedInLayersLE.mono hn (hp m hm)

theorem of_support_subset {L k n : Nat} {p q : FormalPoly L k}
    (hq : PolynomialInLayersLE (L := L) (k := k) n q) (hsub : p.support ⊆ q.support) :
    PolynomialInLayersLE (L := L) (k := k) n p := by
  intro m hm
  exact hq m (hsub hm)

theorem monomial {L k n : Nat} {m : FormalVar L k →₀ Nat} {a : ℝ}
    (hm : SupportedInLayersLE (L := L) (k := k) n m) :
    PolynomialInLayersLE (L := L) (k := k) n
      (MvPolynomial.monomial m a : FormalPoly L k) := by
  intro u hu
  have hsub :
      (MvPolynomial.monomial m a : FormalPoly L k).support ⊆
        ({m} : Finset (FormalVar L k →₀ Nat)) :=
    MvPolynomial.support_monomial_subset
  have hu_eq : u = m := by
    simpa using hsub hu
  subst u
  exact hm

theorem sum {L k n : Nat} {ι : Type*} {s : Finset ι} {f : ι -> FormalPoly L k}
    (hf : ∀ i ∈ s, PolynomialInLayersLE (L := L) (k := k) n (f i)) :
    PolynomialInLayersLE (L := L) (k := k) n (∑ i ∈ s, f i) := by
  classical
  intro m hm
  have hmem := MvPolynomial.support_sum (s := s) (f := f) hm
  rcases Finset.mem_biUnion.mp hmem with ⟨i, hi, hm'⟩
  exact hf i hi m hm'

end PolynomialInLayersLE

namespace PolynomialInLayersLT

theorem of_support_subset {L k n : Nat} {p q : FormalPoly L k}
    (hq : PolynomialInLayersLT (L := L) (k := k) n q) (hsub : p.support ⊆ q.support) :
    PolynomialInLayersLT (L := L) (k := k) n p := by
  intro m hm
  exact hq m (hsub hm)

theorem mono {L k n n' : Nat} {p : FormalPoly L k} (hn : n ≤ n')
    (hp : PolynomialInLayersLT (L := L) (k := k) n p) :
    PolynomialInLayersLT (L := L) (k := k) n' p := by
  intro m hm
  exact SupportedInLayersLT.mono hn (hp m hm)

theorem to_LE {L k n : Nat} {p : FormalPoly L k}
    (hp : PolynomialInLayersLT (L := L) (k := k) n p) :
    PolynomialInLayersLE (L := L) (k := k) n p := by
  intro m hm
  exact SupportedInLayersLT.to_LE (hp m hm)

theorem sum {L k n : Nat} {ι : Type*} {s : Finset ι} {f : ι -> FormalPoly L k}
    (hf : ∀ i ∈ s, PolynomialInLayersLT (L := L) (k := k) n (f i)) :
    PolynomialInLayersLT (L := L) (k := k) n (∑ i ∈ s, f i) := by
  classical
  intro m hm
  have hmem := MvPolynomial.support_sum (s := s) (f := f) hm
  rcases Finset.mem_biUnion.mp hmem with ⟨i, hi, hm'⟩
  exact hf i hi m hm'

theorem C_mul {L k n : Nat} (c : ℝ) {p : FormalPoly L k}
    (hp : PolynomialInLayersLT (L := L) (k := k) n p) :
    PolynomialInLayersLT (L := L) (k := k) n
      (MvPolynomial.C (σ := FormalVar L k) c * p) := by
  classical
  intro m hm
  have hmem :=
    MvPolynomial.support_mul
      (p := (MvPolynomial.C (σ := FormalVar L k) c)) (q := p) hm
  rw [Finset.mem_add] at hmem
  rcases hmem with ⟨u, hu, v, hv, huv⟩
  have hsub :
      (MvPolynomial.C (σ := FormalVar L k) c).support ⊆
        ({0} : Finset (FormalVar L k →₀ Nat)) :=
    support_C_subset_zero c
  have hu0 : u = 0 := by
    simpa using hsub hu
  subst u
  rw [zero_add] at huv
  subst m
  exact hp v hv

theorem mul {L k n : Nat} {p q : FormalPoly L k}
    (hp : PolynomialInLayersLT (L := L) (k := k) n p)
    (hq : PolynomialInLayersLT (L := L) (k := k) n q) :
    PolynomialInLayersLT (L := L) (k := k) n (p * q) := by
  classical
  intro m hm
  have hmem := MvPolynomial.support_mul (p := p) (q := q) hm
  rw [Finset.mem_add] at hmem
  rcases hmem with ⟨u, hu, v, hv, huv⟩
  rw [← huv]
  exact SupportedInLayersLT.add (hp u hu) (hq v hv)

end PolynomialInLayersLT

namespace BlockMultiAffine

theorem of_support_subset {L k : Nat} {p q : FormalPoly L k}
    (hq : BlockMultiAffine q) (hsub : p.support ⊆ q.support) :
    BlockMultiAffine p := by
  intro m hm
  exact hq m (hsub hm)

theorem zero {L k : Nat} : BlockMultiAffine (0 : FormalPoly L k) := by
  intro m hm
  simp at hm

theorem C {L k : Nat} (c : ℝ) :
    BlockMultiAffine (MvPolynomial.C (σ := FormalVar L k) c) := by
  intro m hm
  have hsub :
      (MvPolynomial.C (σ := FormalVar L k) c).support ⊆
        ({0} : Finset (FormalVar L k →₀ Nat)) :=
    support_C_subset_zero c
  have hm0 : m = 0 := by
    simpa using hsub hm
  subst m
  exact MonomialBlockMultiAffine.zero

theorem add {L k : Nat} {p q : FormalPoly L k}
    (hp : BlockMultiAffine p) (hq : BlockMultiAffine q) :
    BlockMultiAffine (p + q) := by
  classical
  intro m hm
  have hmem := MvPolynomial.support_add (p := p) (q := q) hm
  rcases Finset.mem_union.mp hmem with hm' | hm'
  · exact hp m hm'
  · exact hq m hm'

theorem neg {L k : Nat} {p : FormalPoly L k} (hp : BlockMultiAffine p) :
    BlockMultiAffine (-p) := by
  intro m hm
  exact hp m (by simpa [MvPolynomial.support_neg] using hm)

theorem sub {L k : Nat} {p q : FormalPoly L k}
    (hp : BlockMultiAffine p) (hq : BlockMultiAffine q) :
    BlockMultiAffine (p - q) := by
  classical
  intro m hm
  have hmem := MvPolynomial.support_sub (FormalVar L k) p q hm
  rcases Finset.mem_union.mp hmem with hm' | hm'
  · exact hp m hm'
  · exact hq m hm'

theorem sum {L k : Nat} {ι : Type*} {s : Finset ι} {f : ι -> FormalPoly L k}
    (hf : ∀ i ∈ s, BlockMultiAffine (f i)) :
    BlockMultiAffine (∑ i ∈ s, f i) := by
  classical
  intro m hm
  have hmem := MvPolynomial.support_sum (s := s) (f := f) hm
  rcases Finset.mem_biUnion.mp hmem with ⟨i, hi, hm'⟩
  exact hf i hi m hm'

theorem C_mul {L k : Nat} (c : ℝ) {p : FormalPoly L k}
    (hp : BlockMultiAffine p) :
    BlockMultiAffine (MvPolynomial.C (σ := FormalVar L k) c * p) := by
  classical
  intro m hm
  have hmem :=
    MvPolynomial.support_mul
      (p := (MvPolynomial.C (σ := FormalVar L k) c)) (q := p) hm
  rw [Finset.mem_add] at hmem
  rcases hmem with ⟨u, hu, v, hv, huv⟩
  have hsub :
      (MvPolynomial.C (σ := FormalVar L k) c).support ⊆
        ({0} : Finset (FormalVar L k →₀ Nat)) :=
    support_C_subset_zero c
  have hu0 : u = 0 := by
    simpa using hsub hu
  subst u
  rw [zero_add] at huv
  subst m
  exact hp v hv

end BlockMultiAffine

namespace BlockDegreeLE

theorem of_support_subset {L k D : Nat} {p q : FormalPoly L k}
    (hq : BlockDegreeLE D q) (hsub : p.support ⊆ q.support) :
    BlockDegreeLE D p := by
  intro m hm l
  exact hq m (hsub hm) l

theorem add {L k D : Nat} {p q : FormalPoly L k}
    (hp : BlockDegreeLE D p) (hq : BlockDegreeLE D q) :
    BlockDegreeLE D (p + q) := by
  classical
  intro m hm l
  have hmem := MvPolynomial.support_add (p := p) (q := q) hm
  rcases Finset.mem_union.mp hmem with hm' | hm'
  · exact hp m hm' l
  · exact hq m hm' l

theorem sub {L k D : Nat} {p q : FormalPoly L k}
    (hp : BlockDegreeLE D p) (hq : BlockDegreeLE D q) :
    BlockDegreeLE D (p - q) := by
  classical
  intro m hm l
  have hmem := MvPolynomial.support_sub (FormalVar L k) p q hm
  rcases Finset.mem_union.mp hmem with hm' | hm'
  · exact hp m hm' l
  · exact hq m hm' l

theorem sum {L k D : Nat} {ι : Type*} {s : Finset ι} {f : ι -> FormalPoly L k}
    (hf : ∀ i ∈ s, BlockDegreeLE D (f i)) :
    BlockDegreeLE D (∑ i ∈ s, f i) := by
  classical
  intro m hm l
  have hmem := MvPolynomial.support_sum (s := s) (f := f) hm
  rcases Finset.mem_biUnion.mp hmem with ⟨i, hi, hm'⟩
  exact hf i hi m hm' l

theorem two_mul_of_block {L k : Nat} {p q : FormalPoly L k}
    (hp : BlockMultiAffine p) (hq : BlockMultiAffine q) :
    BlockDegreeLE 2 (p * q) := by
  classical
  intro m hm l
  have hmem := MvPolynomial.support_mul (p := p) (q := q) hm
  rw [Finset.mem_add] at hmem
  rcases hmem with ⟨u, hu, v, hv, huv⟩
  have hu_le : (∑ a : Fin k, u (l, a)) ≤ 1 :=
    (hp u hu).block_sum_le_one l
  have hv_le : (∑ a : Fin k, v (l, a)) ≤ 1 :=
    (hq v hv).block_sum_le_one l
  calc
    (∑ a : Fin k, m (l, a))
        = ∑ a : Fin k, (u + v) (l, a) := by rw [← huv]
    _ = (∑ a : Fin k, u (l, a)) + ∑ a : Fin k, v (l, a) := by
        simp [Pi.add_apply, Finset.sum_add_distrib]
    _ ≤ 1 + 1 := Nat.add_le_add hu_le hv_le
    _ = 2 := rfl

end BlockDegreeLE

/-! ## Single-variable formal polynomial splits -/

/-- Coefficient of `x^s` in `f`, as a polynomial in the remaining variables. -/
noncomputable def coeffOfVar {L k : Nat} (x : FormalVar L k) (s : Nat)
    (f : FormalPoly L k) : FormalPoly L k :=
  ∑ m ∈ f.support.filter (fun m => m x = s),
    (MvPolynomial.monomial (Finsupp.erase x m) (f.coeff m) : FormalPoly L k)

/-- Every support monomial of `coeffOfVar` is obtained by erasing `x` from a
support monomial of the original polynomial with exponent `s` at `x`. -/
theorem coeffOfVar_support_exists {L k : Nat} {x : FormalVar L k} {s : Nat}
    {f : FormalPoly L k} {m : FormalVar L k →₀ Nat}
    (hm : m ∈ (coeffOfVar x s f).support) :
    ∃ u ∈ f.support, u x = s ∧ m = Finsupp.erase x u := by
  classical
  have hmem :
      m ∈ (f.support.filter (fun u => u x = s)).biUnion
        (fun u =>
          (MvPolynomial.monomial (Finsupp.erase x u) (f.coeff u) :
            FormalPoly L k).support) := by
    exact MvPolynomial.support_sum (s := f.support.filter (fun u => u x = s))
      (f := fun u =>
        (MvPolynomial.monomial (Finsupp.erase x u) (f.coeff u) : FormalPoly L k))
      (by simpa [coeffOfVar] using hm)
  rcases Finset.mem_biUnion.mp hmem with ⟨u, hu, hmterm⟩
  have hu_support : u ∈ f.support := (Finset.mem_filter.mp hu).1
  have hux : u x = s := (Finset.mem_filter.mp hu).2
  have hsub :
      (MvPolynomial.monomial (Finsupp.erase x u) (f.coeff u) : FormalPoly L k).support ⊆
        ({Finsupp.erase x u} : Finset (FormalVar L k →₀ Nat)) :=
    MvPolynomial.support_monomial_subset
  have hm_eq : m = Finsupp.erase x u := by
    simpa using hsub hmterm
  exact ⟨u, hu_support, hux, hm_eq⟩

/-- The coefficient polynomial in the `x`-split no longer contains `x`. -/
theorem coeffOfVar_notMem_vars {L k : Nat} {x : FormalVar L k} {s : Nat}
    {f : FormalPoly L k} :
    x ∉ (coeffOfVar x s f).vars := by
  classical
  intro hxvars
  rcases (MvPolynomial.mem_vars_iff_mem_support (p := coeffOfVar x s f) x).mp hxvars with
    ⟨m, hm, hxmem⟩
  rcases coeffOfVar_support_exists hm with ⟨u, _hu, _hux, rfl⟩
  have hx_nonzero : (Finsupp.erase x u) x ≠ 0 := Finsupp.mem_support_iff.mp hxmem
  exact hx_nonzero (by simp)

/-- Erasing one variable from monomials preserves layer support upper bounds. -/
theorem coeffOfVar_support_subset {L k n : Nat} {x : FormalVar L k} {s : Nat}
    {f : FormalPoly L k} :
    PolynomialInLayersLE n f -> PolynomialInLayersLE n (coeffOfVar x s f) := by
  classical
  intro hf m hm y hy
  rcases coeffOfVar_support_exists hm with ⟨u, hu, _hux, rfl⟩
  by_cases hyx : y = x
  · subst y
    simp
  · simpa [Finsupp.erase_ne hyx] using hf u hu y hy

/-- Evaluation of one monomial after splitting off the selected variable. -/
theorem evalFormalPolyComplex_monomial_erase_mul_pow {L k : Nat}
    (z : FormalVar L k -> ℂ) (x : FormalVar L k) (m : FormalVar L k →₀ Nat)
    (c : ℝ) :
    evalFormalPolyComplex z (MvPolynomial.monomial m c : FormalPoly L k) =
      evalFormalPolyComplex z
        (MvPolynomial.monomial (Finsupp.erase x m) c : FormalPoly L k) * (z x) ^ m x := by
  have hsplit : Finsupp.erase x m + Finsupp.single x (m x) = m := by
    ext y
    by_cases hy : y = x
    · subst y
      simp
    · simp [Finsupp.erase_ne hy, Finsupp.single_eq_of_ne hy]
  calc
    evalFormalPolyComplex z (MvPolynomial.monomial m c : FormalPoly L k)
        = evalFormalPolyComplex z
            (MvPolynomial.monomial (Finsupp.erase x m + Finsupp.single x (m x)) c :
              FormalPoly L k) := by
            rw [hsplit]
    _ = evalFormalPolyComplex z
            (MvPolynomial.monomial (Finsupp.erase x m) c * MvPolynomial.X x ^ m x :
              FormalPoly L k) := by
            rw [MvPolynomial.monomial_add_single]
    _ = evalFormalPolyComplex z
          (MvPolynomial.monomial (Finsupp.erase x m) c : FormalPoly L k) * (z x) ^ m x := by
            simp [evalFormalPolyComplex]

/-- Reconstruct a polynomial from its coefficients in one selected variable,
after a finite `degreeOf` bound. -/
theorem evalFormalPolyComplex_eq_sum_coeffOfVar {L k : Nat} {x : FormalVar L k}
    {D : Nat} {f : FormalPoly L k} (hD : MvPolynomial.degreeOf x f ≤ D)
    (z : FormalVar L k -> ℂ) :
    evalFormalPolyComplex z f =
      ∑ s ∈ Finset.range (D + 1),
        evalFormalPolyComplex z (coeffOfVar x s f) * (z x) ^ s := by
  classical
  let B : (FormalVar L k →₀ Nat) -> ℂ := fun m =>
    evalFormalPolyComplex z
      (MvPolynomial.monomial (Finsupp.erase x m) (f.coeff m) : FormalPoly L k) *
        (z x) ^ m x
  have hmaps : ∀ m ∈ f.support, m x ∈ Finset.range (D + 1) := by
    intro m hm
    exact Finset.mem_range.mpr
      (Nat.lt_succ_of_le ((MvPolynomial.degreeOf_le_iff.mp hD) m hm))
  have hfiber :
      (∑ s ∈ Finset.range (D + 1), ∑ m ∈ f.support with m x = s, B m) =
        ∑ m ∈ f.support, B m := by
    simpa using
      (Finset.sum_fiberwise_of_maps_to (s := f.support) (t := Finset.range (D + 1))
        (g := fun m : FormalVar L k →₀ Nat => m x) hmaps B)
  have hcoeff_eval : ∀ s : Nat,
      evalFormalPolyComplex z (coeffOfVar x s f) * (z x) ^ s =
        ∑ m ∈ f.support with m x = s, B m := by
    intro s
    have heval_coeff :
        evalFormalPolyComplex z (coeffOfVar x s f) =
          ∑ m ∈ f.support.filter (fun m => m x = s),
            evalFormalPolyComplex z
              (MvPolynomial.monomial (Finsupp.erase x m) (f.coeff m) : FormalPoly L k) := by
      simp only [coeffOfVar, evalFormalPolyComplex]
      change MvPolynomial.eval₂Hom (algebraMap ℝ ℂ) z
          (∑ m ∈ f.support.filter (fun m => m x = s),
            (MvPolynomial.monomial (Finsupp.erase x m) (f.coeff m) : FormalPoly L k)) =
        ∑ m ∈ f.support.filter (fun m => m x = s),
          MvPolynomial.eval₂Hom (algebraMap ℝ ℂ) z
            (MvPolynomial.monomial (Finsupp.erase x m) (f.coeff m) : FormalPoly L k)
      simp only [map_sum]
    calc
      evalFormalPolyComplex z (coeffOfVar x s f) * (z x) ^ s
          = (∑ m ∈ f.support with m x = s,
              evalFormalPolyComplex z
                (MvPolynomial.monomial (Finsupp.erase x m) (f.coeff m) : FormalPoly L k)) *
              (z x) ^ s := by
              rw [heval_coeff]
      _ = ∑ m ∈ f.support with m x = s,
            evalFormalPolyComplex z
              (MvPolynomial.monomial (Finsupp.erase x m) (f.coeff m) : FormalPoly L k) *
                (z x) ^ s := by
              rw [Finset.sum_mul]
      _ = ∑ m ∈ f.support with m x = s, B m := by
              refine Finset.sum_congr rfl ?_
              intro m hm
              have hmx : m x = s := (Finset.mem_filter.mp hm).2
              simp [B, hmx]
  have hmono_sum_eval :
      evalFormalPolyComplex z (∑ m ∈ f.support,
          (MvPolynomial.monomial m (f.coeff m) : FormalPoly L k)) =
        ∑ m ∈ f.support,
          evalFormalPolyComplex z (MvPolynomial.monomial m (f.coeff m) : FormalPoly L k) := by
    simp only [evalFormalPolyComplex]
    change MvPolynomial.eval₂Hom (algebraMap ℝ ℂ) z (∑ m ∈ f.support,
          (MvPolynomial.monomial m (f.coeff m) : FormalPoly L k)) =
        ∑ m ∈ f.support,
          MvPolynomial.eval₂Hom (algebraMap ℝ ℂ) z
            (MvPolynomial.monomial m (f.coeff m) : FormalPoly L k)
    simp only [map_sum]
  calc
    evalFormalPolyComplex z f
        = evalFormalPolyComplex z (∑ m ∈ f.support,
            (MvPolynomial.monomial m (f.coeff m) : FormalPoly L k)) := by
            exact congrArg (evalFormalPolyComplex z) (MvPolynomial.as_sum f)
    _ = ∑ m ∈ f.support,
            evalFormalPolyComplex z (MvPolynomial.monomial m (f.coeff m) : FormalPoly L k) :=
            hmono_sum_eval
    _ = ∑ m ∈ f.support, B m := by
            refine Finset.sum_congr rfl ?_
            intro m hm
            exact evalFormalPolyComplex_monomial_erase_mul_pow z x m (f.coeff m)
    _ = ∑ s ∈ Finset.range (D + 1), ∑ m ∈ f.support with m x = s, B m := hfiber.symm
    _ = ∑ s ∈ Finset.range (D + 1),
          evalFormalPolyComplex z (coeffOfVar x s f) * (z x) ^ s := by
            refine Finset.sum_congr rfl ?_
            intro s hs
            exact (hcoeff_eval s).symm

/-- A block-degree bound controls the ordinary degree in each formal variable. -/
theorem blockDegreeLE_degreeOf_le {L k D : Nat} {x : FormalVar L k} {f : FormalPoly L k}
    (hf : BlockDegreeLE D f) : MvPolynomial.degreeOf x f ≤ D := by
  rw [MvPolynomial.degreeOf_le_iff]
  intro m hm
  have hx_le : m x ≤ ∑ a : Fin k, m (x.1, a) := by
    simpa using
      (Finset.single_le_sum (fun a _ => Nat.zero_le (m (x.1, a)))
        (Finset.mem_univ x.2))
  exact le_trans hx_le (hf m hm x.1)

/-- A block-multiaffine polynomial has ordinary degree at most one in each
formal variable. -/
theorem blockMultiAffine_degreeOf_le {L k : Nat} {x : FormalVar L k} {f : FormalPoly L k}
    (hf : BlockMultiAffine f) : MvPolynomial.degreeOf x f ≤ 1 := by
  rw [MvPolynomial.degreeOf_le_iff]
  intro m hm
  have hx_le : m x ≤ ∑ a : Fin k, m (x.1, a) := by
    simpa using
      (Finset.single_le_sum (fun a _ => Nat.zero_le (m (x.1, a)))
        (Finset.mem_univ x.2))
  exact le_trans hx_le ((hf m hm).block_sum_le_one x.1)

namespace LayerBoundedBlockAffine

theorem of_support_subset {L k n : Nat} {p q : FormalPoly L k}
    (hq : LayerBoundedBlockAffine n q) (hsub : p.support ⊆ q.support) :
    LayerBoundedBlockAffine n p :=
  ⟨BlockMultiAffine.of_support_subset hq.block hsub,
    PolynomialInLayersLT.of_support_subset hq.support_lt hsub⟩

theorem mono {L k n n' : Nat} {p : FormalPoly L k} (hn : n ≤ n')
    (hp : LayerBoundedBlockAffine n p) :
    LayerBoundedBlockAffine n' p :=
  ⟨hp.block, PolynomialInLayersLT.mono hn hp.support_lt⟩

theorem C {L k n : Nat} (c : ℝ) :
    LayerBoundedBlockAffine (L := L) (k := k) n
      (MvPolynomial.C (σ := FormalVar L k) c) := by
  refine ⟨BlockMultiAffine.C c, ?_⟩
  intro m hm x hx
  have hsub :
      (MvPolynomial.C (σ := FormalVar L k) c).support ⊆
        ({0} : Finset (FormalVar L k →₀ Nat)) :=
    support_C_subset_zero c
  have hm0 : m = 0 := by
    simpa using hsub hm
  subst m
  simp

theorem add {L k n : Nat} {p q : FormalPoly L k}
    (hp : LayerBoundedBlockAffine n p) (hq : LayerBoundedBlockAffine n q) :
    LayerBoundedBlockAffine n (p + q) := by
  classical
  refine ⟨BlockMultiAffine.add hp.block hq.block, ?_⟩
  intro m hm
  have hmem := MvPolynomial.support_add (p := p) (q := q) hm
  rcases Finset.mem_union.mp hmem with hm' | hm'
  · exact hp.support_lt m hm'
  · exact hq.support_lt m hm'

theorem neg {L k n : Nat} {p : FormalPoly L k}
    (hp : LayerBoundedBlockAffine n p) : LayerBoundedBlockAffine n (-p) := by
  refine ⟨BlockMultiAffine.neg hp.block, ?_⟩
  intro m hm
  exact hp.support_lt m (by simpa [MvPolynomial.support_neg] using hm)

theorem sub {L k n : Nat} {p q : FormalPoly L k}
    (hp : LayerBoundedBlockAffine n p) (hq : LayerBoundedBlockAffine n q) :
    LayerBoundedBlockAffine n (p - q) := by
  classical
  refine ⟨BlockMultiAffine.sub hp.block hq.block, ?_⟩
  intro m hm
  have hmem := MvPolynomial.support_sub (FormalVar L k) p q hm
  rcases Finset.mem_union.mp hmem with hm' | hm'
  · exact hp.support_lt m hm'
  · exact hq.support_lt m hm'

theorem sum {L k n : Nat} {ι : Type*} {s : Finset ι} {f : ι -> FormalPoly L k}
    (hf : ∀ i ∈ s, LayerBoundedBlockAffine n (f i)) :
    LayerBoundedBlockAffine n (∑ i ∈ s, f i) := by
  classical
  refine ⟨BlockMultiAffine.sum (fun i hi => (hf i hi).block), ?_⟩
  intro m hm
  have hmem := MvPolynomial.support_sum (s := s) (f := f) hm
  rcases Finset.mem_biUnion.mp hmem with ⟨i, hi, hm'⟩
  exact (hf i hi).support_lt m hm'

theorem C_mul {L k n : Nat} (c : ℝ) {p : FormalPoly L k}
    (hp : LayerBoundedBlockAffine n p) :
    LayerBoundedBlockAffine n (MvPolynomial.C (σ := FormalVar L k) c * p) := by
  classical
  refine ⟨BlockMultiAffine.C_mul c hp.block, ?_⟩
  intro m hm
  have hmem :=
    MvPolynomial.support_mul
      (p := (MvPolynomial.C (σ := FormalVar L k) c)) (q := p) hm
  rw [Finset.mem_add] at hmem
  rcases hmem with ⟨u, hu, v, hv, huv⟩
  have hsub :
      (MvPolynomial.C (σ := FormalVar L k) c).support ⊆
        ({0} : Finset (FormalVar L k →₀ Nat)) :=
    support_C_subset_zero c
  have hu0 : u = 0 := by
    simpa using hsub hu
  subst u
  rw [zero_add] at huv
  subst m
  exact hp.support_lt v hv

theorem formalGate_mul {L k n : Nat} {l : Fin L} (hl : l.1 = n) (a : Fin k)
    {p : FormalPoly L k} (hp : LayerBoundedBlockAffine n p) :
    LayerBoundedBlockAffine (n + 1) (formalGate l a * p) := by
  classical
  refine ⟨?_, ?_⟩
  · intro m hm
    have hmem := MvPolynomial.support_mul (p := formalGate l a) (q := p) hm
    rw [formalGate, MvPolynomial.support_X, Finset.mem_add] at hmem
    rcases hmem with ⟨u, hu, v, hv, huv⟩
    have hu' : u = Finsupp.single (l, a) 1 := by
      simpa using hu
    subst u
    rw [← huv]
    exact MonomialBlockMultiAffine.add_gate_of_supportedLT
      (hp.block v hv) (hp.support_lt v hv) hl a
  · intro m hm
    have hmem := MvPolynomial.support_mul (p := formalGate l a) (q := p) hm
    rw [formalGate, MvPolynomial.support_X, Finset.mem_add] at hmem
    rcases hmem with ⟨u, hu, v, hv, huv⟩
    have hu' : u = Finsupp.single (l, a) 1 := by
      simpa using hu
    subst u
    rw [← huv]
    exact SupportedInLayersLT.add_gate (hp.support_lt v hv) hl a

theorem formalGate_mul_C_mul {L k n : Nat} {l : Fin L} (hl : l.1 = n)
    (a : Fin k) (c : ℝ) {p : FormalPoly L k}
    (hp : LayerBoundedBlockAffine n p) :
    LayerBoundedBlockAffine (n + 1)
      ((formalGate l a * MvPolynomial.C (σ := FormalVar L k) c) * p) := by
  rw [mul_assoc]
  exact formalGate_mul hl a (C_mul c hp)

end LayerBoundedBlockAffine

theorem layerBounded_realMatrixToFormal_mulVec {L k d n : Nat}
    (M : Matrix (Fin d) (Fin d) ℝ) {x : FormalVec L k d}
    (hx : ∀ j : Fin d, LayerBoundedBlockAffine n (x j)) :
    ∀ i : Fin d, LayerBoundedBlockAffine n
      ((realMatrixToFormal (L := L) (k := k) M *ᵥ x) i) := by
  intro i
  simpa [Matrix.mulVec, dotProduct, realMatrixToFormal] using
    (LayerBoundedBlockAffine.sum (s := Finset.univ)
      (f := fun j : Fin d => MvPolynomial.C (σ := FormalVar L k) (M i j) * x j)
      (fun j hj => LayerBoundedBlockAffine.C_mul (M i j) (hx j)))

theorem layerBounded_formalGatedValueSum_mulVec {L k d n : Nat}
    (θ : Params L k d) {l : Fin L} (hl : l.1 = n) {x : FormalVec L k d}
    (hx : ∀ j : Fin d, LayerBoundedBlockAffine n (x j)) :
    ∀ i : Fin d, LayerBoundedBlockAffine (n + 1)
      ((formalGatedValueSum θ l *ᵥ x) i) := by
  intro i
  simpa [formalGatedValueSum, formalGate, formalValueMatrix, realMatrixToFormal,
    Matrix.mulVec, dotProduct, Matrix.sum_apply, Matrix.smul_apply, Finset.sum_mul,
    mul_assoc] using
    (LayerBoundedBlockAffine.sum (s := Finset.univ)
      (f := fun j : Fin d =>
        ∑ a : Fin k,
          ((formalGate l a * MvPolynomial.C (σ := FormalVar L k)
            (valueMatrix θ l a i j)) * x j))
      (fun j hj =>
        LayerBoundedBlockAffine.sum (s := Finset.univ)
          (f := fun a : Fin k =>
            ((formalGate l a * MvPolynomial.C (σ := FormalVar L k)
              (valueMatrix θ l a i j)) * x j))
          (fun a ha =>
            LayerBoundedBlockAffine.formalGate_mul_C_mul hl a
              (valueMatrix θ l a i j) (hx j))))

theorem layerBounded_formalStepPoint {L k d n : Nat} (θ : Params L k d)
    {l : Fin L} (hl : l.1 = n) {w v : FormalVec L k d}
    (hw : ∀ i : Fin d, LayerBoundedBlockAffine n (w i))
    (hv : ∀ i : Fin d, LayerBoundedBlockAffine n (v i)) :
    (∀ i : Fin d, LayerBoundedBlockAffine (n + 1) ((formalStepPoint θ l w v).1 i)) ∧
      (∀ i : Fin d, LayerBoundedBlockAffine (n + 1) ((formalStepPoint θ l w v).2 i)) := by
  constructor
  · intro i
    have hC :=
      LayerBoundedBlockAffine.mono (Nat.le_succ n)
        (layerBounded_realMatrixToFormal_mulVec (L := L) (k := k)
          (collapseMatrix θ l) hw i)
    have hD := layerBounded_formalGatedValueSum_mulVec θ hl hw i
    simpa [formalStepPoint, formalCollapseMatrix, Matrix.sub_mulVec] using
      LayerBoundedBlockAffine.sub hC hD
  · intro i
    have hC :=
      LayerBoundedBlockAffine.mono (Nat.le_succ n)
        (layerBounded_realMatrixToFormal_mulVec (L := L) (k := k)
          (collapseMatrix θ l) hv i)
    have hD := layerBounded_formalGatedValueSum_mulVec θ hl hw i
    simpa [formalStepPoint, formalCollapseMatrix] using
      LayerBoundedBlockAffine.add hC hD

theorem formalPoint_layerBoundedBlockAffine {L k d : Nat}
    (θ : Params L k d) (w v : Vec d) :
    ∀ (n : Nat) (hn : n ≤ L),
      (∀ i : Fin d, LayerBoundedBlockAffine n (formalW θ w v n hn i)) ∧
        (∀ i : Fin d, LayerBoundedBlockAffine n (formalV θ w v n hn i)) := by
  intro n
  induction n with
  | zero =>
      intro hn
      constructor
      · intro i
        simpa [formalW, formalPoint, realVecToFormal, formalConst] using
          (LayerBoundedBlockAffine.C (L := L) (k := k) (n := 0) (w i))
      · intro i
        simpa [formalV, formalPoint, realVecToFormal, formalConst] using
          (LayerBoundedBlockAffine.C (L := L) (k := k) (n := 0) (v i))
  | succ n ih =>
      intro hn
      have hprev := ih (Nat.le_of_succ_le hn)
      have hstep :=
        layerBounded_formalStepPoint (θ := θ)
          (l := ⟨n, Nat.lt_of_succ_le hn⟩) (n := n) rfl hprev.1 hprev.2
      constructor
      · intro i
        simpa [formalW, formalPoint_succ] using hstep.1 i
      · intro i
        simpa [formalV, formalPoint_succ] using hstep.2 i

theorem formalW_blockMultiAffine {L k d : Nat} (θ : Params L k d) (w v : Vec d)
    (n : Nat) (hn : n ≤ L) (i : Fin d) :
    BlockMultiAffine (formalW θ w v n hn i) :=
  ((formalPoint_layerBoundedBlockAffine θ w v n hn).1 i).block

theorem formalV_blockMultiAffine {L k d : Nat} (θ : Params L k d) (w v : Vec d)
    (n : Nat) (hn : n ≤ L) (i : Fin d) :
    BlockMultiAffine (formalV θ w v n hn i) :=
  ((formalPoint_layerBoundedBlockAffine θ w v n hn).2 i).block

theorem blockDegreeLE_two_formalBilin {L k d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (w v : FormalVec L k d)
    (hw : ∀ i : Fin d, BlockMultiAffine (w i))
    (hv : ∀ i : Fin d, BlockMultiAffine (v i)) :
    BlockDegreeLE 2 (formalBilin A w v) := by
  simpa [formalBilin, Matrix.mulVec, dotProduct, realMatrixToFormal, Finset.mul_sum, mul_assoc]
    using
      (BlockDegreeLE.sum (s := Finset.univ)
        (f := fun i : Fin d =>
          ∑ j : Fin d, w i * (MvPolynomial.C (σ := FormalVar L k) (A i j) * v j))
        (fun i hi =>
          BlockDegreeLE.sum (s := Finset.univ)
            (f := fun j : Fin d =>
              w i * (MvPolynomial.C (σ := FormalVar L k) (A i j) * v j))
            (fun j hj =>
              BlockDegreeLE.two_mul_of_block (hw i)
                (BlockMultiAffine.C_mul (A i j) (hv j)))))

theorem formalSlope_blockDegree_two {L k d : Nat} (θ : Params L k d)
    (w v : Vec d) (l : Fin L) (a : Fin k) :
    BlockDegreeLE 2 (formalSlope θ w v l a) := by
  unfold formalSlope
  exact blockDegreeLE_two_formalBilin (attentionMatrix θ l a)
    (formalW θ w v l.1 (Nat.le_of_lt l.2))
    (formalV θ w v l.1 (Nat.le_of_lt l.2))
    (fun i => formalW_blockMultiAffine θ w v l.1 (Nat.le_of_lt l.2) i)
    (fun i => formalV_blockMultiAffine θ w v l.1 (Nat.le_of_lt l.2) i)

theorem formalBilin_polynomialInLayersLT {L k d n : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (w v : FormalVec L k d)
    (hw : ∀ i : Fin d, PolynomialInLayersLT (L := L) (k := k) n (w i))
    (hv : ∀ i : Fin d, PolynomialInLayersLT (L := L) (k := k) n (v i)) :
    PolynomialInLayersLT (L := L) (k := k) n (formalBilin A w v) := by
  simpa [formalBilin, Matrix.mulVec, dotProduct, realMatrixToFormal, Finset.mul_sum,
    mul_assoc] using
      (PolynomialInLayersLT.sum (s := Finset.univ)
        (f := fun i : Fin d =>
          ∑ j : Fin d, w i * (MvPolynomial.C (σ := FormalVar L k) (A i j) * v j))
        (fun i hi =>
          PolynomialInLayersLT.sum (s := Finset.univ)
            (f := fun j : Fin d =>
              w i * (MvPolynomial.C (σ := FormalVar L k) (A i j) * v j))
            (fun j hj =>
              PolynomialInLayersLT.mul (hw i)
                (PolynomialInLayersLT.C_mul (A i j) (hv j)))))

theorem formalSlope_polynomialInLayersLT {L k d : Nat} (θ : Params L k d)
    (w v : Vec d) (l : Fin L) (a : Fin k) :
    PolynomialInLayersLT (L := L) (k := k) l.1 (formalSlope θ w v l a) := by
  unfold formalSlope
  exact formalBilin_polynomialInLayersLT (attentionMatrix θ l a)
    (formalW θ w v l.1 (Nat.le_of_lt l.2))
    (formalV θ w v l.1 (Nat.le_of_lt l.2))
    (fun i => ((formalPoint_layerBoundedBlockAffine θ w v l.1
      (Nat.le_of_lt l.2)).1 i).support_lt)
    (fun i => ((formalPoint_layerBoundedBlockAffine θ w v l.1
      (Nat.le_of_lt l.2)).2 i).support_lt)


end TransformerIdentifiability.NLayer.KHead
