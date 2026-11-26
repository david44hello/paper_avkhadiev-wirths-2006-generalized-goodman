-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
module

public import Goodman.Defs

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology

namespace Goodman

/-- On the unit circle, reversal evaluates the original polynomial at the inverse
point and multiplies by a unit-modulus factor. -/
theorem reversed_polynomial_boundary (c : ℕ → ℂ) (n : ℕ) {w : ℂ} (hw : ‖w‖ = 1) :
    (∑ j ∈ Finset.range (n+1), c j * w^(n-j)) =
      w^n * ∑ j ∈ Finset.range (n+1), c j * (w⁻¹)^j := by
  have hw0 : w ≠ 0 := by intro h; simp [h] at hw
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hpow : w^(n-j) = w^n * (w⁻¹)^j := by
    rw [inv_pow, ← div_eq_mul_inv, eq_div_iff (pow_ne_zero _ hw0), ← pow_add, Nat.sub_add_cancel hjn]
  rw [hpow]
  ring

/-- The maximum modulus principle transfers the boundary bound to the disk. -/
theorem reversed_polynomial_weight (c : ℕ → ℂ) (n : ℕ)
    (hb : ∀ t : ℂ, ‖t‖ = 1 → ‖∑ j ∈ Finset.range (n+1), c j * t^j‖ ≤ 1) :
    IsWeight (fun w : ℂ => ∑ j ∈ Finset.range (n+1), c j * w^(n-j)) := by
  let P (w : ℂ) := ∑ j ∈ Finset.range (n+1), c j * w^(n-j)
  have hP (z : ℂ) : AnalyticAt ℂ P z :=
    Finset.analyticAt_fun_sum _ fun j _ => by fun_prop
  refine ⟨fun z _ => hP z, ?_⟩
  intro z hz
  have hd : Differentiable ℂ P := fun w => (hP w).differentiableAt
  apply Complex.norm_le_of_forall_mem_frontier_norm_le (U := disk)
    Metric.isBounded_ball hd.diffContOnCl _ (subset_closure hz)
  intro w hw
  rw [disk, frontier_ball _ one_ne_zero] at hw
  have hw' : ‖w‖ = 1 := by simpa using hw
  change ‖∑ j ∈ Finset.range (n+1), c j * w^(n-j)‖ ≤ 1
  rw [reversed_polynomial_boundary c n hw', norm_mul, norm_pow, hw', one_pow, one_mul]
  exact hb w⁻¹ (by simp [hw'])

theorem reversed_polynomial_coeff (c : ℕ → ℂ) {n j : ℕ} (hj : j ≤ n) :
    coeff (n-j) (fun w : ℂ => ∑ i ∈ Finset.range (n+1), c i * w^(n-i)) = c j := by
  unfold coeff
  rw [iteratedDeriv_fun_sum (fun i _ => by fun_prop), Finset.sum_eq_single j]
  · simp only [iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero, ite_true]
    field_simp [show ((n-j).factorial : ℂ) ≠ 0 from Nat.cast_ne_zero.mpr (n-j).factorial_ne_zero]
  · intro i hi hij
    have hle := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hne : n-j ≠ n-i := by omega
    simp only [iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero, ite_eq_right hne,
      Nat.cast_zero, mul_zero]
  · intro h
    exact (h (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))).elim

end Goodman
