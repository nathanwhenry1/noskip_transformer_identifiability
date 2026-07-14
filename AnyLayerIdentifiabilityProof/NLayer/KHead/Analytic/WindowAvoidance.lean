import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer.KHead

/-!
# Pure window combinatorics for sequence-window avoidance

This file contains the finite and infinite pigeonhole steps used by the
sequence-window route in `Analytic/DominanceSibling.lean`.  It deliberately has
no analytic imports, so it can be imported by the analytic sibling file without
creating a dependency cycle.
-/

/-- Finite pigeonhole for one block: a map from `K + 1` positions to `K`
colors repeats a color at two ordered positions. -/
theorem exists_lt_sameColor_finWindow {K : Nat} (_hK : 0 < K)
    (f : Fin (K + 1) -> Fin K) :
    ∃ i j : Fin (K + 1), i < j ∧ f i = f j := by
  classical
  have hcard : Fintype.card (Fin K) < Fintype.card (Fin (K + 1)) := by
    simp
  rcases Fintype.exists_ne_map_eq_of_card_lt f hcard with ⟨i, j, hij, hsame⟩
  have hval_ne : i.val ≠ j.val := by
    intro hval
    exact hij (Fin.ext hval)
  rcases Nat.lt_or_gt_of_ne hval_ne with hlt | hgt
  · exact ⟨i, j, hlt, hsame⟩
  · exact ⟨j, i, hgt, hsame.symm⟩

/-- Natural-number window form of `exists_lt_sameColor_finWindow`.  In any
`K + 1` consecutive positions, a `Fin K` coloring repeats at a positive gap at
most `K`. -/
theorem exists_sameColor_pair_natWindow {K start : Nat} (hK : 0 < K)
    (color : Nat -> Fin K) :
    ∃ (n g : Nat) (c : Fin K),
      start ≤ n ∧ n + g < start + (K + 1) ∧
      1 ≤ g ∧ g ≤ K ∧ color n = c ∧ color (n + g) = c := by
  rcases exists_lt_sameColor_finWindow (K := K) hK
      (fun i : Fin (K + 1) => color (start + i.val)) with
    ⟨i, j, hij, hsame⟩
  have hij_val : i.val < j.val := hij
  refine ⟨start + i.val, j.val - i.val, color (start + i.val), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · have hj_lt : j.val < K + 1 := j.isLt
    omega
  · omega
  · have hj_lt : j.val < K + 1 := j.isLt
    omega
  · rfl
  · have hidx : start + i.val + (j.val - i.val) = start + j.val := by
      omega
    simpa [hidx] using hsame.symm

/-- Tail recurrence pigeonhole for bounded windows.  If all sufficiently large
natural numbers are colored by `Fin K` (formalized as a total coloring, with the
tail bound recorded in the output set), then some color recurs at a fixed
positive gap `g ≤ K` for infinitely many starts in the tail. -/
theorem infinite_sameColor_boundedGap_of_coloring {K N : Nat} (hK : 0 < K)
    (color : Nat -> Fin K) :
    ∃ (c : Fin K) (g : Nat),
      1 ≤ g ∧ g ≤ K ∧
      {n : Nat | N ≤ n ∧ color n = c ∧ color (n + g) = c}.Infinite := by
  classical
  let U : Set Nat :=
    ⋃ c : Fin K, ⋃ d : Fin K,
      {n : Nat | N ≤ n ∧ color n = c ∧ color (n + (d.val + 1)) = c}
  have hU_infinite : U.Infinite := by
    rw [Set.infinite_iff_exists_gt]
    intro a
    let start := max N (a + 1)
    rcases exists_sameColor_pair_natWindow (K := K) (start := start) hK color with
      ⟨n, g, c, hn_start, _hn_end, hg_pos, hg_le, hcolor_n, hcolor_ng⟩
    let d : Fin K := ⟨g - 1, by omega⟩
    refine ⟨n, ?_, ?_⟩
    · refine Set.mem_iUnion.2 ⟨c, ?_⟩
      refine Set.mem_iUnion.2 ⟨d, ?_⟩
      have hgap : d.val + 1 = g := by
        dsimp [d]
        omega
      exact ⟨le_trans (Nat.le_max_left N (a + 1)) hn_start, hcolor_n, by
        simpa [hgap] using hcolor_ng⟩
    · have ha_start : a < start := by
        exact lt_of_lt_of_le (Nat.lt_succ_self a) (Nat.le_max_right N (a + 1))
      exact lt_of_lt_of_le ha_start hn_start
  by_contra hnone
  have hU_finite : U.Finite := by
    dsimp [U]
    refine Set.finite_iUnion ?_
    intro c
    refine Set.finite_iUnion ?_
    intro d
    have hgap_pos : 1 ≤ d.val + 1 := by omega
    have hgap_le : d.val + 1 ≤ K := Nat.succ_le_of_lt d.isLt
    have hnot_inf :
        ¬ ({n : Nat | N ≤ n ∧ color n = c ∧ color (n + (d.val + 1)) = c}.Infinite) := by
      intro hInf
      exact hnone ⟨c, d.val + 1, hgap_pos, hgap_le, hInf⟩
    by_contra hfinite
    exact hnot_inf hfinite
  exact hU_infinite hU_finite

end TransformerIdentifiability.NLayer.KHead
