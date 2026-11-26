-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
module

public import Goodman.Defs

@[expose] public section

noncomputable section
open Filter
open scoped Topology

namespace Goodman

@[simp] theorem A_at_one (n : ℕ) : A 1 n = n := by simp [A]

@[simp] theorem A_first (p : ℝ) : A p 1 = 1 := by simp [A]

theorem A_positive {p : ℝ} (hp : 0 < p) {n : ℕ} (hn : 1 ≤ n) : 0 < A p n := by
  apply div_pos _ (pow_pos hp _)
  apply Finset.sum_pos'
  · intro i hi
    positivity
  · exact ⟨0, Finset.mem_range.mpr hn, by simp⟩

theorem A_closed {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (n : ℕ) :
    A p n = (1 - p^(2*n)) / ((1 - p^2) * p^(n-1)) := by
  have h₁ : 1 - p^2 ≠ 0 := by nlinarith [mul_pos (sub_pos.mpr hp1) (by linarith : 0 < 1+p)]
  have h₂ : p^(n-1) ≠ 0 := pow_ne_zero _ hp.ne'
  have h := geom_sum_mul_neg (p^2) n
  simp only [← pow_mul] at h
  unfold A
  field_simp
  nlinarith [h]

theorem A_succ_binomial {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (j : ℕ) :
    (1-p^2) * A p (j+1) = (1/p)^j - p^2*p^j := by
  rw [A_closed hp hp1, one_div_pow]
  simp only [Nat.add_sub_cancel, Nat.mul_add, Nat.mul_one, pow_add, pow_mul, one_div]
  have h₁ : 1 - p^2 ≠ 0 := by nlinarith [mul_pos (sub_pos.mpr hp1) (by linarith : 0 < 1+p)]
  field_simp
  ring

theorem D_closed {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (r : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    D p r n = ((r+1/p)^(n-1) - p^2*(r+p)^(n-1)) / (1-p^2) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have h₁ : 1 - p^2 ≠ 0 := by nlinarith [mul_pos (sub_pos.mpr hp1) (by linarith : 0 < 1+p)]
  apply (eq_div_iff h₁).mpr
  simp only [D,Nat.succ_sub_one,Finset.sum_mul]
  rw [add_comm r (1/p),add_comm r p,add_pow,add_pow,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    _ = (m.choose j : ℝ) * r^(m-j) * ((1-p^2)*A p (j+1)) := by ring
    _ = _ := by rw [A_succ_binomial hp hp1]; ring

theorem A_tendsto_one (n : ℕ) : Tendsto (fun p : ℝ => A p n) (𝓝 1) (𝓝 (n : ℝ)) := by
  have h : ContinuousAt (fun p : ℝ => A p n) 1 := by
    unfold A
    fun_prop (disch := norm_num)
  simpa only [A_at_one] using h.tendsto

end Goodman
