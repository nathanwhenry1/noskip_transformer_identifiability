import AnyLayerIdentifiabilityProof.NLayer.NoSkip.Core

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer.NoSkip

/-!
# No-skip dimension threshold

The corrected simultaneous certificate uses `k` anchor rows and
`k * (m - 1)` deeper-level rows, hence `k*m` rows.  The public theorem retains
the earlier conservative budget `k * (m + 1)` and its maximum with the standing
lower bound two; no threshold strengthening is made silently.  The elementary
lemmas here are independent of the later row-index code.
-/

/-- TeX `d_*^ns(m,k) = max {2, k(m+1)}`. -/
def dStarNS (m k : Nat) : Nat :=
  max 2 (k * (m + 1))

theorem two_le_dStarNS (m k : Nat) : 2 ≤ dStarNS m k :=
  le_max_left _ _

theorem rowBudget_le_dStarNS (m k : Nat) : k * (m + 1) ≤ dStarNS m k :=
  le_max_right _ _

theorem dStarNS_pos (m k : Nat) : 0 < dStarNS m k :=
  lt_of_lt_of_le (by decide) (two_le_dStarNS m k)

theorem dStarNS_ne_zero (m k : Nat) : dStarNS m k ≠ 0 :=
  Nat.ne_of_gt (dStarNS_pos m k)

/-- Increasing the depth cannot decrease the no-skip dimension threshold. -/
theorem dStarNS_mono_left {m n k : Nat} (hmn : m ≤ n) :
    dStarNS m k ≤ dStarNS n k := by
  unfold dStarNS
  exact max_le_max (le_refl 2) (Nat.mul_le_mul_left k (Nat.add_le_add_right hmn 1))

/-- Increasing the number of heads cannot decrease the no-skip threshold. -/
theorem dStarNS_mono_right {m k q : Nat} (hkq : k ≤ q) :
    dStarNS m k ≤ dStarNS m q := by
  unfold dStarNS
  exact max_le_max (le_refl 2) (Nat.mul_le_mul_right (m + 1) hkq)

theorem dStarNS_tail_le (m k : Nat) : dStarNS m k ≤ dStarNS (m + 1) k :=
  dStarNS_mono_left (Nat.le_succ m)

/-- A dimension satisfying the threshold satisfies the raw row budget. -/
theorem rowBudget_le_of_dStarNS_le {m k d : Nat} (hd : dStarNS m k ≤ d) :
    k * (m + 1) ≤ d :=
  (rowBudget_le_dStarNS m k).trans hd

theorem two_le_of_dStarNS_le {m k d : Nat} (hd : dStarNS m k ≤ d) : 2 ≤ d :=
  (two_le_dStarNS m k).trans hd

theorem d_pos_of_dStarNS_le {m k d : Nat} (hd : dStarNS m k ≤ d) : 0 < d :=
  lt_of_lt_of_le (by decide) (two_le_of_dStarNS_le hd)

/-- The dimension hypothesis is inherited by every shallower recursive tail. -/
theorem dStarNS_tail_budget {m k d : Nat} (hd : dStarNS (m + 1) k ≤ d) :
    dStarNS m k ≤ d :=
  (dStarNS_tail_le m k).trans hd

theorem rowBudget_tail_of_succ {m k d : Nat}
    (hd : k * ((m + 1) + 1) ≤ d) : k * (m + 1) ≤ d := by
  exact (Nat.mul_le_mul_left k (Nat.le_succ (m + 1))).trans hd

end TransformerIdentifiability.NLayer.NoSkip
