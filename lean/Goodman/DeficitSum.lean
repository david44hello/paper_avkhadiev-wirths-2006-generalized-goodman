-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
module

public import Goodman.CoefficientClaims

@[expose] public section

noncomputable section
namespace Goodman

/-- In a sum with nonnegative weights, the exact first coefficient improves the
triangle bound by the first weight times the shortfall in that coefficient. -/
theorem norm_sum_le_first_deficit {n : ℕ} (hn : 1 ≤ n) (d : ℕ → ℂ) (w : ℕ → ℝ)
    (hw : ∀ k, 0 ≤ w k) (h0 : d 0 = 0) (hd : ∀ k, 1 ≤ k → ‖d k‖ ≤ (k : ℝ)) :
    ‖∑ k ∈ Finset.range (n+1), d k * (w k : ℂ)‖ ≤
      (∑ k ∈ Finset.range (n+1), (k : ℝ) * w k) - w 1 * (1 - ‖d 1‖) := by
  calc
    _ ≤ ∑ k ∈ Finset.range (n+1), ‖d k * (w k : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (n+1),
        ((k:ℝ)*w k - if k=1 then w 1*(1-‖d 1‖) else 0) := by
      refine Finset.sum_le_sum fun k _ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw k)]
      by_cases hk : k = 1
      · subst k
        simp
        nlinarith
      · simp only [ite_eq_right hk, sub_zero]
        rcases k with _ | k
        · simp [h0]
        · exact mul_le_mul_of_nonneg_right (hd _ (Nat.succ_pos k)) (hw _)
    _ = _ := by
      rw [Finset.sum_sub_distrib]
      simp [Finset.mem_range, show 1 < n+1 by omega]

end Goodman
