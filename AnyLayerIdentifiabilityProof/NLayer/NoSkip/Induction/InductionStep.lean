import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Induction.Peeling
import AnyLayerIdentifiabilityProof.NLayer.NoSkip.BaseCase

set_option autoImplicit false

open Matrix

namespace TransformerIdentifiability.NLayer.NoSkip

noncomputable section

/-!
# Gauge-threaded depth induction

The tail target has already absorbed the first output gauge in its input
coordinates.  Consequently, when a recursive tail gauge chain is prefixed,
the new full chain has interfaces `I, G, H₁, ..., H_{m-1}, I`.
-/

/-- Prefix the first hidden-state gauge to a normalized tail gauge chain. -/
def prependGaugeChain {m d : Nat} (G : GaugeMatrix d)
    (H : GaugeChain (m + 1) d) : GaugeChain (m + 2) d where
  get := Fin.cases 1 (Fin.cases G (fun i : Fin (m + 1) => H.get i.succ))
  get_zero := rfl
  get_last := by
    have hlast : Fin.last (m + 2) = (Fin.last (m + 1)).succ := by
      ext
      simp
    rw [hlast]
    change H.get (Fin.last m).succ = 1
    simpa using H.get_last

@[simp] theorem prependGaugeChain_zero {m d : Nat} (G : GaugeMatrix d)
    (H : GaugeChain (m + 1) d) :
    (prependGaugeChain G H).get 0 = 1 :=
  rfl

@[simp] theorem prependGaugeChain_one {m d : Nat} (G : GaugeMatrix d)
    (H : GaugeChain (m + 1) d) :
    (prependGaugeChain G H).get (0 : Fin (m + 2)).succ = G :=
  rfl

@[simp] theorem prependGaugeChain_succ_succ {m d : Nat} (G : GaugeMatrix d)
    (H : GaugeChain (m + 1) d) (i : Fin (m + 1)) :
    (prependGaugeChain G H).get i.succ.succ = H.get i.succ :=
  rfl

/-- Assemble a full matching from the paired first layer and the matching of
the input-gauged target tail. -/
def prependTargetToSourceMatching
    {m k d : Nat} {theta theta' : Params (m + 2) k d}
    (sigma : Equiv.Perm (Fin k)) (G : GaugeMatrix d)
    (hattention : ∀ h : Fin k,
      attentionMatrix theta 0 (sigma h) = attentionMatrix theta' 0 h)
    (hvalue : ∀ h : Fin k,
      G.matrix * valueMatrix theta 0 (sigma h) = valueMatrix theta' 0 h)
    (tailMatching : TargetToSourceMatching (Fin.tail theta)
      (inputGaugeTail G (Fin.tail theta'))) :
    TargetToSourceMatching theta theta' where
  headPerm := consLayerPerm sigma tailMatching.headPerm
  gauge := prependGaugeChain G tailMatching.gauge
  attention_eq := by
    intro l h
    refine Fin.cases ?_ (fun j => ?_) l
    · simpa using hattention h
    · refine Fin.cases ?_ (fun i => ?_) j
      · simpa using tailMatching.attention_eq (0 : Fin (m + 1)) h
      · simpa using tailMatching.attention_eq i.succ h
  value_eq := by
    intro l h
    refine Fin.cases ?_ (fun j => ?_) l
    · have heq := hvalue h
      calc
        valueMatrix theta 0 (sigma h) =
            G.invMatrix * (G.matrix * valueMatrix theta 0 (sigma h)) := by
          rw [← Matrix.mul_assoc, GaugeMatrix.invMatrix_mul_matrix]
          simp
        _ = G.invMatrix * valueMatrix theta' 0 h := congrArg
          (fun M : Matrix (Fin d) (Fin d) Real => G.invMatrix * M) heq
        _ = G.invMatrix * valueMatrix theta' 0 h * (1 : GaugeMatrix d).matrix := by
          simp
    · refine Fin.cases ?_ (fun i => ?_) j
      · simpa [Matrix.mul_assoc] using
          tailMatching.value_eq (0 : Fin (m + 1)) h
      · simpa using tailMatching.value_eq i.succ h

@[simp] theorem prependTargetToSourceMatching_headPerm_zero
    {m k d : Nat} {theta theta' : Params (m + 2) k d}
    (sigma : Equiv.Perm (Fin k)) (G : GaugeMatrix d)
    (hattention : ∀ h : Fin k,
      attentionMatrix theta 0 (sigma h) = attentionMatrix theta' 0 h)
    (hvalue : ∀ h : Fin k,
      G.matrix * valueMatrix theta 0 (sigma h) = valueMatrix theta' 0 h)
    (tailMatching : TargetToSourceMatching (Fin.tail theta)
      (inputGaugeTail G (Fin.tail theta'))) :
    (prependTargetToSourceMatching sigma G hattention hvalue tailMatching).headPerm 0 = sigma :=
  rfl

@[simp] theorem firstGaugeOf_prependTargetToSourceMatching
    {m k d : Nat} {theta theta' : Params (m + 2) k d}
    (sigma : Equiv.Perm (Fin k)) (G : GaugeMatrix d)
    (hattention : ∀ h : Fin k,
      attentionMatrix theta 0 (sigma h) = attentionMatrix theta' 0 h)
    (hvalue : ∀ h : Fin k,
      G.matrix * valueMatrix theta 0 (sigma h) = valueMatrix theta' 0 h)
    (tailMatching : TargetToSourceMatching (Fin.tail theta)
      (inputGaugeTail G (Fin.tail theta'))) :
    firstGaugeOf
      (prependTargetToSourceMatching sigma G hattention hvalue tailMatching) = G :=
  rfl

/-- One successor step, assuming the invariant for the one-layer-shorter
input-gauged target pair. -/
theorem openInductionInvariant_succ
    {m k d r : Nat}
    (ih : ∀ (theta theta' : Params (m + 1) k d)
      (omega : Set (NetworkInput r d)),
      OpenInductionInvariant r theta theta' omega)
    (theta theta' : Params (m + 2) k d)
    (omega : Set (NetworkInput r d)) :
    OpenInductionInvariant r theta theta' omega := by
  intro hr hd hgeneric homega hequal
  have hr0 : 0 < r := lt_of_lt_of_le (by decide) hr
  have hr1 : 1 < r := hr
  let global := openSetToGlobal hr0 theta theta' omega homega hequal
  let H : Step1StandingHypotheses r theta theta' :=
    ⟨hr0, global.probe_equal, hgeneric⟩
  let P : FirstLayerPeelingResult H hr1 := Classical.choice
    (exists_firstLayerPeelingResult H hr1
      (two_le_of_dStarNS_le hd) global.global_equal)
  let tailConclusion : OpenInductionInvariantConclusion r
      (Fin.tail theta)
      (inputGaugeTail P.identification.values.gauge (Fin.tail theta')) :=
    Classical.choice
      (ih (Fin.tail theta)
        (inputGaugeTail P.identification.values.gauge (Fin.tail theta'))
        P.omegaTail hr (dStarNS_tail_budget hd) P.gaugedTail_generic
        P.omegaTail_data P.tail_equal)
  let matching : TargetToSourceMatching theta theta' :=
    prependTargetToSourceMatching P.identification.gates.sigma
      P.identification.values.gauge
      P.identification.gates.attention_eq
      P.identification.values.value_eq
      tailConclusion.matching
  have hregular : Regularity theta' := hgeneric.regularity
  have hmatchingUnique : ∀ matching' : TargetToSourceMatching theta theta',
      matching' = matching := by
    intro matching'
    exact targetToSourceMatching_eq hregular.attention_pairwise
      hregular.joint_surjective matching' matching
  have hfirstAttention : ∀ h : Fin k,
      attentionMatrix theta 0 (matching.headPerm 0 h) =
        attentionMatrix theta' 0 h := by
    intro h
    simpa [matching] using P.identification.gates.attention_eq h
  have hfirstValue : ∀ h : Fin k,
      valueMatrix theta' 0 h =
        (firstGaugeOf matching).matrix *
          valueMatrix theta 0 (matching.headPerm 0 h) := by
    intro h
    simpa [matching] using (P.identification.values.value_eq h).symm
  have hfirstGaugeUnique : ∀ K : GaugeMatrix d,
      (∀ h : Fin k, valueMatrix theta' 0 h =
          K.matrix * valueMatrix theta 0 (matching.headPerm 0 h)) →
        K = firstGaugeOf matching := by
    intro K hK
    have hK' : ∀ h : Fin k,
        K.matrix * valueMatrix theta 0 (P.identification.gates.sigma h) =
          valueMatrix theta' 0 h := by
      intro h
      simpa [matching] using (hK h).symm
    have hKG := P.identification.gauge_unique K hK'
    simpa [matching] using hKG
  have hreduced : ReducedPair r theta theta' matching := by
    refine {
      tail_relabel_eq := ?_
      firstLayer_eq := ?_
      tail_open := ?_
      gaugedTail_generic := ?_
    }
    · simpa [matching] using P.tail_relabel_eq
    · intro T X
      simpa [matching] using P.firstLayer_eq X
    · refine ⟨P.omegaTail, P.omegaTail_data, ?_⟩
      simpa [matching] using P.tail_equal
    · simpa [matching] using P.gaugedTail_generic
  exact ⟨{
    global := global.global_equal
    matching := matching
    matching_unique := hmatchingUnique
    firstAttention_eq := hfirstAttention
    firstValue_eq := hfirstValue
    firstGauge_unique := hfirstGaugeUnique
    reducedPair := hreduced
  }⟩

/-- The depth-one endpoint is the exact base-case recovery with the identity
boundary gauge. -/
theorem openInductionInvariant_one
    {k d r : Nat} (theta theta' : Params 1 k d)
    (omega : Set (NetworkInput r d)) :
    OpenInductionInvariant r theta theta' omega := by
  intro hr _hd hgeneric homega hequal
  have hr0 : 0 < r := lt_of_lt_of_le (by decide) hr
  have hr1 : 1 < r := hr
  let global := openSetToGlobal hr0 theta theta' omega homega hequal
  let C : BaseCaseConclusion theta theta' :=
    baseCaseConclusionOfProbeOutputEq hr1 hgeneric global.probe_equal
  let matching : TargetToSourceMatching theta theta' := C.matching
  have hmatchingUnique : ∀ matching' : TargetToSourceMatching theta theta',
      matching' = matching := by
    intro matching'
    exact targetToSourceMatching_eq hgeneric.attention_pairwise
      hgeneric.joint_surjective matching' matching
  have hfirstGauge : firstGaugeOf matching = 1 := by
    simp [matching, firstGaugeOf, C.matching_gauge]
  have hfirstAttention : ∀ h : Fin k,
      attentionMatrix theta 0 (matching.headPerm 0 h) =
        attentionMatrix theta' 0 h := by
    intro h
    simpa [matching, C.matching_headPerm, baseAttention] using C.attention_eq h
  have hfirstValue : ∀ h : Fin k,
      valueMatrix theta' 0 h =
        (firstGaugeOf matching).matrix *
          valueMatrix theta 0 (matching.headPerm 0 h) := by
    intro h
    simpa [matching, C.matching_headPerm, hfirstGauge, baseValue] using
      (C.value_eq h).symm
  have hfirstGaugeUnique : ∀ K : GaugeMatrix d,
      (∀ h : Fin k, valueMatrix theta' 0 h =
          K.matrix * valueMatrix theta 0 (matching.headPerm 0 h)) →
        K = firstGaugeOf matching := by
    intro K hK
    have hmul : ∀ h : Fin k,
        K.matrix * valueMatrix theta' 0 h =
          (1 : Matrix (Fin d) (Fin d) Real) * valueMatrix theta' 0 h := by
      intro h
      calc
        K.matrix * valueMatrix theta' 0 h =
            K.matrix * valueMatrix theta 0 (matching.headPerm 0 h) := by
          rw [hfirstValue h, hfirstGauge]
          simp
        _ = valueMatrix theta' 0 h := (hK h).symm
        _ = (1 : Matrix (Fin d) (Fin d) Real) * valueMatrix theta' 0 h := by
          simp
    have hmatrix : K.matrix = (1 : Matrix (Fin d) (Fin d) Real) :=
      matrix_eq_of_mul_valueMatrices_eq_of_jointSurjective
        (hgeneric.joint_surjective 0) hmul
    calc
      K = 1 := GaugeMatrix.ext hmatrix
      _ = firstGaugeOf matching := hfirstGauge.symm
  exact ⟨{
    global := global.global_equal
    matching := matching
    matching_unique := hmatchingUnique
    firstAttention_eq := hfirstAttention
    firstValue_eq := hfirstValue
    firstGauge_unique := hfirstGaugeUnique
    reducedPair := trivial
  }⟩

/-- The strengthened open-set invariant holds at every positive depth. -/
theorem openInductionInvariant_all (r k d : Nat) :
    ∀ (n : Nat) (theta theta' : Params (n + 1) k d)
      (omega : Set (NetworkInput r d)),
      OpenInductionInvariant r theta theta' omega := by
  intro n
  induction n with
  | zero =>
      intro theta theta' omega
      exact openInductionInvariant_one theta theta' omega
  | succ m ih =>
      intro theta theta' omega
      exact openInductionInvariant_succ
        (fun psi psi' omegaTail => ih psi psi' omegaTail)
        theta theta' omega

/-- Public theorem form with the depth inferred from the parameter types. -/
theorem openInductionInvariant
    {n k d r : Nat} (theta theta' : Params (n + 1) k d)
    (omega : Set (NetworkInput r d)) :
    OpenInductionInvariant r theta theta' omega :=
  openInductionInvariant_all r k d n theta theta' omega

end

end TransformerIdentifiability.NLayer.NoSkip
