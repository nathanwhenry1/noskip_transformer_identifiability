import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Analytic.PoleArcs
import AnyLayerIdentifiabilityProof.NLayer.KHead.Analytic.WindowAvoidance

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer.NoSkip

/-!
# Sequence-window avoidance

The pigeonhole argument is purely combinatorial.  These wrappers keep its API
in the NoSkip namespace and the capstone below records how it applies to the
odd-pi sequence carried by `SelectedArcData`.
-/

theorem exists_lt_sameColor_finWindow {K : Nat} (hK : 0 < K)
    (color : Fin (K + 1) → Fin K) :
    ∃ i j : Fin (K + 1), i < j ∧ color i = color j :=
  KHead.exists_lt_sameColor_finWindow hK color

theorem exists_sameColor_pair_natWindow {K start : Nat} (hK : 0 < K)
    (color : Nat → Fin K) :
    ∃ (n g : Nat) (c : Fin K),
      start ≤ n ∧ n + g < start + (K + 1) ∧
      1 ≤ g ∧ g ≤ K ∧ color n = c ∧ color (n + g) = c :=
  KHead.exists_sameColor_pair_natWindow hK color

theorem infinite_sameColor_boundedGap_of_coloring {K N : Nat} (hK : 0 < K)
    (color : Nat → Fin K) :
    ∃ (c : Fin K) (g : Nat),
      1 ≤ g ∧ g ≤ K ∧
      {n : Nat | N ≤ n ∧ color n = c ∧ color (n + g) = c}.Infinite :=
  KHead.infinite_sameColor_boundedGap_of_coloring hK color

/-- The bounded-gap recurrence output applies directly to the exact selected
arc sequence.  Every recurrent index and its shifted partner remain genuine
punctured odd-pi preimages and are distinct from the arc center. -/
theorem SelectedArcData.infinite_sameColor_boundedGap
    {H : ℂ → ℂ} {xi : ℂ} {m : Nat} {c0 : ℂ}
    (A : SelectedArcData H xi m c0)
    {K N : Nat} (hK : 0 < K) (color : Nat → Fin K) :
    ∃ (c : Fin K) (g : Nat),
      1 ≤ g ∧ g ≤ K ∧
      {n : Nat | N ≤ n ∧ color n = c ∧ color (n + g) = c}.Infinite ∧
      ∀ n : Nat,
        N ≤ n → color n = c → color (n + g) = c →
          H (A.arc (A.rho n)) ∈ Pi ∧
          H (A.arc (A.rho (n + g))) ∈ Pi ∧
          A.arc (A.rho n) ≠ xi ∧
          A.arc (A.rho (n + g)) ≠ xi := by
  obtain ⟨c, g, hg1, hgK, hInfinite⟩ :=
    infinite_sameColor_boundedGap_of_coloring hK color
  refine ⟨c, g, hg1, hgK, hInfinite, ?_⟩
  intro n _hn _hcolor _hshift
  exact ⟨A.sigma_mem_pi n, A.sigma_mem_pi (n + g),
    A.sigma_ne_center n, A.sigma_ne_center (n + g)⟩

end TransformerIdentifiability.NLayer.NoSkip
