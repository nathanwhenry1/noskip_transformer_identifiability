import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Genericity.PolynomialCover
import AnyLayerIdentifiabilityProof.NLayer.KHead.Genericity.Null

set_option autoImplicit false

open MeasureTheory
open TransformerIdentifiability.NLayer.KHead
  (KHeadParamPolynomialPredicateCover kHeadParamNonvanishingCarrier)

namespace TransformerIdentifiability.NLayer.NoSkip

/-!
# NS080 — The exceptional set is algebraic and null (no skip)

This file states the measure/topology conclusion of `prop:generic-algebraic`.
The exceptional set `𝒩_{L,k}` is the complement of the common nonvanishing locus
of the finite recursive-generic polynomial family built in `PolynomialCover.lean`
(a finite union of proper algebraic subsets).  Its complement is open, dense, and
of full Lebesgue measure, and it contains the complement of the recursive generic
set `RecursiveGenericSet`.  All measure theory is reused from the neutral k-head
toolbox (`KHead.Genericity.Null`); the shared parameter type
`NoSkip.Params = KHead.Params` makes those wrappers apply directly.
-/

variable {r L k d : Nat}

/-- The main exceptional set `𝒩_{L,k}` (a finite union of proper algebraic
zero sets, exposed for the downstream main theorem NS156). -/
noncomputable def RecursiveGenericExceptionalSet (r L k d : Nat) (hd : dStarNS L k ≤ d)
    (hk : 0 < k) : Set (Params L k d) :=
  (recursiveGenericCover r L k d hd hk).badSet

/-- `𝒩_{L,k}` is closed (a finite union of algebraic zero sets). -/
theorem isClosed_recursiveGenericExceptionalSet (hd : dStarNS L k ≤ d) (hk : 0 < k) :
    IsClosed (RecursiveGenericExceptionalSet r L k d hd hk) :=
  (recursiveGenericCover r L k d hd hk).isClosed_badSet

/-- `𝒩_{L,k}` has Lebesgue measure zero, so its complement has full measure. -/
theorem recursiveGenericExceptionalSet_null (hd : dStarNS L k ≤ d) (hk : 0 < k) :
    volume (RecursiveGenericExceptionalSet r L k d hd hk) = 0 :=
  (recursiveGenericCover r L k d hd hk).badSet_null

/-- `𝒩_{L,k}` has empty interior. -/
theorem recursiveGenericExceptionalSet_interior_eq_empty (hd : dStarNS L k ≤ d) (hk : 0 < k) :
    interior (RecursiveGenericExceptionalSet r L k d hd hk) = ∅ :=
  (recursiveGenericCover r L k d hd hk).badSet_interior_eq_empty

/-- The complement of `𝒩_{L,k}` is open. -/
theorem isOpen_compl_recursiveGenericExceptionalSet (hd : dStarNS L k ≤ d) (hk : 0 < k) :
    IsOpen (RecursiveGenericExceptionalSet r L k d hd hk)ᶜ :=
  (isClosed_recursiveGenericExceptionalSet hd hk).isOpen_compl

/-- The complement of `𝒩_{L,k}` is dense. -/
theorem dense_compl_recursiveGenericExceptionalSet (hd : dStarNS L k ≤ d) (hk : 0 < k) :
    Dense (RecursiveGenericExceptionalSet r L k d hd hk)ᶜ :=
  (recursiveGenericCover r L k d hd hk).dense_compl_badSet

/-- The complement of `𝒩_{L,k}` is contained in the recursive generic set:
every parameter off the exceptional set is recursively generic. -/
theorem compl_recursiveGenericExceptionalSet_subset (hd : dStarNS L k ≤ d) (hk : 0 < k) :
    (RecursiveGenericExceptionalSet r L k d hd hk)ᶜ ⊆ RecursiveGenericSet r L k d := by
  intro θ hθ
  have hcarrier : θ ∈ kHeadParamNonvanishingCarrier (recursiveGenericCover r L k d hd hk).data := by
    simpa [RecursiveGenericExceptionalSet, KHeadParamPolynomialPredicateCover.badSet]
      using hθ
  exact recursiveGenericCover_carrier_subset r L k d hd hk hcarrier

/-! ## Predicate-level nullness of the recursive generic complement -/

/-- The complement of the recursive generic set has Lebesgue measure zero:
the recursive generic set has full measure. -/
theorem recursiveGenericSet_compl_null (hd : dStarNS L k ≤ d) (hk : 0 < k) :
    volume ({θ : Params L k d | ¬ RecursiveGeneric r L k d θ}) = 0 :=
  (recursiveGenericCover r L k d hd hk).predicateBadSet_null

/-- The complement of the recursive generic set has empty interior. -/
theorem recursiveGenericSet_compl_interior_eq_empty (hd : dStarNS L k ≤ d) (hk : 0 < k) :
    interior ({θ : Params L k d | ¬ RecursiveGeneric r L k d θ}) = ∅ :=
  (recursiveGenericCover r L k d hd hk).predicateBadSet_interior_eq_empty

/-- The recursive generic set is dense. -/
theorem dense_recursiveGenericSet (hd : dStarNS L k ≤ d) (hk : 0 < k) :
    Dense (RecursiveGenericSet r L k d) := by
  have h := (recursiveGenericCover r L k d hd hk).dense_predicateSet
  simpa [RecursiveGenericSet] using h

end TransformerIdentifiability.NLayer.NoSkip
