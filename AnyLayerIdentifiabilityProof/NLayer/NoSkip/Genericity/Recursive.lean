import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Genericity.Regularity
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Genericity.CascadeCertificate
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Genericity.HeadwiseCertificate

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer.NoSkip

/-!
# Recursive no-skip genericity

All standing assumptions in this file are target-only.  Depth one carries only
regularity, as in the TeX base class.  At total depth `m + 2`, the index `m + 1`
is the positive number of later layers.  This is exactly the indexing used by
both `CascadeCertificate` and `MultiDialCertificate`; neither certificate is
shifted or truncated when it enters the current-depth package.
-/

/-! ## Current positive-depth clauses -/

/-- Current target clauses at total depth `m + 2`.

Local openness is deliberately not a field: NS053 proves that it follows from
the transmission field of `Regularity`.  The accessor below exports the TeX
local-openness clause without storing a duplicate genericity assumption.
-/
structure CurrentGenericClauses {m k d : Nat} (r : Nat)
    (theta : Params (m + 2) k d) : Prop where
  regularity : Regularity theta
  cascadeCertificate : CascadeCertificate theta
  headwiseDialCertificate : HeadwiseDialCertificate theta

namespace CurrentGenericClauses

variable {m k d r : Nat} {theta : Params (m + 2) k d}

/-- The current local-openness clause, derived from target regularity. -/
theorem localOpenness (h : CurrentGenericClauses r theta) :
    LocalOpenness r theta :=
  h.regularity.localOpenness r

/-- Concrete local open-image data for every current layer. -/
theorem localOpenLayerImage (h : CurrentGenericClauses r theta)
    (l : Fin (m + 2)) : Nonempty (LocalOpenLayerImage r theta l) :=
  h.regularity.localOpenLayerImage r l

/-- Constructor spelling used by downstream package assembly. -/
theorem of_components (hregular : Regularity theta)
    (hcascade : CascadeCertificate theta)
    (hheadwise : HeadwiseDialCertificate theta) :
    CurrentGenericClauses r theta :=
  ⟨hregular, hcascade, hheadwise⟩

end CurrentGenericClauses

/-! ## Depth recursion -/

/-- Recursive target genericity, following the TeX base/successor split.

Depth zero is vacuous.  Depth one requires exactly target regularity (and hence
derived local openness).  At total depth `L + 2`, the target tail is recursively
generic and the untruncated current parameter satisfies both certificates in
addition to regularity.
-/
noncomputable def RecursiveGeneric (r : Nat) :
    (L k d : Nat) → Params L k d → Prop
  | 0, _k, _d, _theta => True
  | 1, _k, _d, theta => Regularity theta
  | L + 2, k, d, theta =>
      RecursiveGeneric r (L + 1) k d (Fin.tail theta) ∧
        CurrentGenericClauses r theta

/-- The target recursive-generic parameter set. -/
def RecursiveGenericSet (r L k d : Nat) : Set (Params L k d) :=
  {theta | RecursiveGeneric r L k d theta}

@[simp] theorem recursiveGeneric_zero {r k d : Nat}
    (theta : Params 0 k d) : RecursiveGeneric r 0 k d theta :=
  trivial

/-- Exact TeX base equation: depth one is precisely regularity. -/
@[simp] theorem recursiveGeneric_one {r k d : Nat}
    (theta : Params 1 k d) :
    RecursiveGeneric r 1 k d theta ↔ Regularity theta :=
  Iff.rfl

/-- Exact tail recursion equation at every total depth `L + 2`. -/
@[simp] theorem recursiveGeneric_succ_succ {r L k d : Nat}
    (theta : Params (L + 2) k d) :
    RecursiveGeneric r (L + 2) k d theta ↔
      RecursiveGeneric r (L + 1) k d (Fin.tail theta) ∧
        CurrentGenericClauses r theta :=
  Iff.rfl

@[simp] theorem mem_recursiveGenericSet {r L k d : Nat}
    {theta : Params L k d} :
    theta ∈ RecursiveGenericSet r L k d ↔ RecursiveGeneric r L k d theta :=
  Iff.rfl

namespace RecursiveGeneric

variable {r L k d : Nat}

/-- Assemble the exact depth-one base case from target regularity. -/
theorem one {theta : Params 1 k d} (hregular : Regularity theta) :
    RecursiveGeneric r 1 k d theta :=
  hregular

/-- Assemble a total-depth-`L + 2` target from its exact tail and current data. -/
theorem succ_succ {theta : Params (L + 2) k d}
    (htail : RecursiveGeneric r (L + 1) k d (Fin.tail theta))
    (hcurrent : CurrentGenericClauses r theta) :
    RecursiveGeneric r (L + 2) k d theta :=
  ⟨htail, hcurrent⟩

/-- Eliminate positive-depth genericity to the exact one-shorter target tail.
At depth one the conclusion is the vacuous depth-zero clause. -/
theorem tail {theta : Params (L + 1) k d}
    (h : RecursiveGeneric r (L + 1) k d theta) :
    RecursiveGeneric r L k d (Fin.tail theta) := by
  cases L with
  | zero => exact recursiveGeneric_zero _
  | succ L => exact h.1

/-- Eliminate depth-two-or-more genericity to the current target clauses. -/
theorem current {theta : Params (L + 2) k d}
    (h : RecursiveGeneric r (L + 2) k d theta) :
    CurrentGenericClauses r theta :=
  h.2

/-- Every positive-depth recursively generic target is regular. -/
theorem regularity {theta : Params (L + 1) k d}
    (h : RecursiveGeneric r (L + 1) k d theta) : Regularity theta := by
  cases L with
  | zero => exact h
  | succ L => exact h.2.regularity

/-- Local openness is exposed but remains derived from current regularity. -/
theorem localOpenness {theta : Params (L + 1) k d}
    (h : RecursiveGeneric r (L + 1) k d theta) :
    LocalOpenness r theta :=
  h.regularity.localOpenness r

theorem localOpenLayerImage {theta : Params (L + 1) k d}
    (h : RecursiveGeneric r (L + 1) k d theta)
    (l : Fin (L + 1)) : Nonempty (LocalOpenLayerImage r theta l) :=
  h.regularity.localOpenLayerImage r l

theorem cascadeCertificate {theta : Params (L + 2) k d}
    (h : RecursiveGeneric r (L + 2) k d theta) :
    CascadeCertificate theta :=
  h.current.cascadeCertificate

theorem headwiseDialCertificate {theta : Params (L + 2) k d}
    (h : RecursiveGeneric r (L + 2) k d theta) :
    HeadwiseDialCertificate theta :=
  h.current.headwiseDialCertificate

end RecursiveGeneric

end TransformerIdentifiability.NLayer.NoSkip
