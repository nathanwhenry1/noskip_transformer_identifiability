import AnyLayerIdentifiabilityProof.NLayer.NoSkip.IdentifiabilityMain

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer.NoSkip

noncomputable section

/-! # Exact generic matrix fiber -/

/-- Parameters with the same realization as `theta'` on the prescribed input
width. -/
def realizationFiber (r : Nat) {L k d : Nat} (theta' : Params L k d) :
    Set (Params L k d) :=
  {theta | TransformerEqualGlobally (r := r) theta theta'}

/-- The full layer-permutation/interface-gauge orbit. -/
def permutationGaugeOrbit {L k d : Nat} (theta' : Params L k d) :
    Set (Params L k d) :=
  Set.range (fun p : (Fin L → Equiv.Perm (Fin k)) × GaugeChain L d =>
    combinedGaugePermuteAction p.1 p.2 theta')

/-- Matching equations reconstruct the source as the target acted on by the
inverse gauge and inverse (source-to-target) layer permutations. -/
theorem eq_combinedGaugePermuteAction_of_matching
    {L k d : Nat} {theta theta' : Params L k d}
    (M : TargetToSourceMatching theta theta') :
    theta = combinedGaugePermuteAction
      (fun l => (M.headPerm l).symm) M.gauge⁻¹ theta' := by
  apply Params.ext
  · intro l a
    let h : Fin k := (M.headPerm l).symm a
    have heq := M.value_eq l h
    simpa [combinedGaugePermuteAction, GaugeChain.act, gaugeAction, h] using heq
  · intro l a
    let h : Fin k := (M.headPerm l).symm a
    have heq := M.attention_eq l h
    simpa [combinedGaugePermuteAction, GaugeChain.act, gaugeAction, h,
      GaugeMatrix.invTranspose] using heq

/-- An explicit orbit equality produces matching data in the inverse
permutation/inverse-gauge orientation. -/
def targetToSourceMatchingOfCombinedActionEq
    {L k d : Nat} (theta' : Params L k d)
    (sigma : Fin L → Equiv.Perm (Fin k)) (G : GaugeChain L d)
    {theta : Params L k d}
    (heq : combinedGaugePermuteAction sigma G theta' = theta) :
    TargetToSourceMatching theta theta' where
  headPerm := fun l => (sigma l).symm
  gauge := G⁻¹
  attention_eq := by
    intro l h
    have hcoord := congrArg
      (fun eta => attentionMatrix eta l ((sigma l).symm h)) heq
    simpa [combinedGaugePermuteAction, GaugeMatrix.invTranspose] using hcoord.symm
  value_eq := by
    intro l h
    have hcoord := congrArg
      (fun eta => valueMatrix eta l ((sigma l).symm h)) heq
    simpa [combinedGaugePermuteAction] using hcoord.symm

/-- Regularity makes the complete permutation/gauge orbit parametrization
injective (the action is free at the target). -/
theorem permutationGaugeOrbit_parametrization_injective
    {L k d : Nat} {theta' : Params L k d} (hregular : Regularity theta') :
    Function.Injective
      (fun p : (Fin L → Equiv.Perm (Fin k)) × GaugeChain L d =>
        combinedGaugePermuteAction p.1 p.2 theta') := by
  rintro ⟨sigma, G⟩ ⟨tau, H⟩ heq
  let theta := combinedGaugePermuteAction sigma G theta'
  let Msigma : TargetToSourceMatching theta theta' :=
    targetToSourceMatchingOfCombinedActionEq theta' sigma G rfl
  let Mtau : TargetToSourceMatching theta theta' :=
    targetToSourceMatchingOfCombinedActionEq theta' tau H heq.symm
  have hmatching : Msigma = Mtau :=
    targetToSourceMatching_eq hregular.attention_pairwise
      hregular.joint_surjective Msigma Mtau
  have hpermInv : (fun l => (sigma l).symm) =
      (fun l => (tau l).symm) := by
    exact congrArg TargetToSourceMatching.headPerm hmatching
  have hgaugeInv : G⁻¹ = H⁻¹ :=
    congrArg TargetToSourceMatching.gauge hmatching
  have hperm : sigma = tau := by
    funext l
    have hl := congrFun hpermInv l
    simpa using congrArg Equiv.symm hl
  have hgauge : G = H := inv_injective hgaugeInv
  exact Prod.ext hperm hgauge

/-- TeX `cor:matrix-fiber`: off the explicit exceptional set the realization
fiber is exactly the permutation--gauge orbit. -/
theorem realizationFiber_eq_permutationGaugeOrbit
    {n k d r : Nat} (hr : 2 ≤ r) (hd : dStarNS (n + 1) k ≤ d)
    (hk : 0 < k) {theta' : Params (n + 1) k d}
    (htarget : theta' ∈
      (RecursiveGenericExceptionalSet r (n + 1) k d hd hk)ᶜ) :
    realizationFiber r theta' = permutationGaugeOrbit theta' := by
  ext theta
  constructor
  · intro htheta
    let C : GenericMatrixIdentifiabilityConclusion theta theta' :=
      Classical.choice (genericMatrixIdentifiability hr hd hk htarget htheta)
    refine ⟨((fun l => (C.matching.headPerm l).symm), C.matching.gauge⁻¹), ?_⟩
    exact (eq_combinedGaugePermuteAction_of_matching C.matching).symm
  · rintro ⟨⟨sigma, G⟩, rfl⟩
    intro X
    exact permutationGaugeOrbit_realizes sigma G theta' X

/-- The orbit parametrization in the preceding fiber theorem is free. -/
theorem generic_permutationGaugeOrbit_free
    {n k d r : Nat} (hd : dStarNS (n + 1) k ≤ d)
    (hk : 0 < k) {theta' : Params (n + 1) k d}
    (htarget : theta' ∈
      (RecursiveGenericExceptionalSet r (n + 1) k d hd hk)ᶜ) :
    Function.Injective
      (fun p : (Fin (n + 1) → Equiv.Perm (Fin k)) × GaugeChain (n + 1) d =>
        combinedGaugePermuteAction p.1 p.2 theta') := by
  apply permutationGaugeOrbit_parametrization_injective
  exact (compl_recursiveGenericExceptionalSet_subset hd hk htarget).regularity

end

end TransformerIdentifiability.NLayer.NoSkip
