-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
module

public import Goodman.CoefficientClaims

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology

namespace Goodman

theorem slitDisk_mem_nhds_zero {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    slitDisk p ∈ 𝓝 (0 : ℂ) := by
  refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : ℂ) hp) ?_
  intro z hz
  rw [Metric.mem_ball, dist_zero_right] at hz
  refine ⟨Metric.mem_ball.mpr (by simpa using hz.trans hp1), ?_⟩
  rintro ⟨r, hr, rfl⟩
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hp.trans_le hr.1)] at hz
  exact (not_lt_of_ge hr.1) hz

theorem slitR_pos {p : ℝ} (hp : 0 < p) : 0 < slitR p := by
  unfold slitR
  positivity

private theorem extremal_den_near (p : ℝ) :
    ∀ᶠ z in 𝓝 (0 : ℂ), (1 - (p : ℂ) * z) * (1 - z / (p : ℂ)) ≠ 0 := by
  have hc : ContinuousAt (fun z : ℂ => (1 - (p : ℂ) * z) * (1 - z / (p : ℂ))) 0 := by fun_prop
  exact hc.eventually_ne (by simp)

theorem slit_majorant_germ {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {q : ℂ → ℂ}
    (hq : IsSlitMap p q) :
    ∀ᶠ z in 𝓝 (0 : ℂ), (slitR p : ℂ) * (q z / (1 - q z)^2) = finitePart (extremal p z) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpp : (1 + (p : ℂ)) ≠ 0 := by
    exact_mod_cast (show 1 + p ≠ 0 by linarith)
  filter_upwards [slitDisk_mem_nhds_zero hp hp1, extremal_den_near p] with z hz hd
  have hmap := hq.1.2.choose_spec.2.1 hz
  have hnorm : ‖q z‖ < 1 := by simpa [disk] using hmap
  have hq1 : 1 - q z ≠ 0 := by
    intro h
    rw [sub_eq_zero.mp h |>.symm] at hnorm
    simp at hnorm
  have hden : (slitR p : ℂ) * ((1 - (p : ℂ)*z)*(1 - z/(p : ℂ))) =
      (slitR p : ℂ)*(1+z)^2 - 4*z := by
    unfold slitR
    push_cast
    field_simp
    ring
  have hslit := hq.2.2 z hz
  have he : finitePart (extremal p z) = z / ((1 - (p : ℂ) * z) * (1 - z / (p : ℂ))) := by
    simp only [extremal, ite_eq_right hd]
    rfl
  rw [he, ← mul_div_assoc]
  apply (div_eq_div_iff (pow_ne_zero _ hq1) hd).2
  linear_combination (q z) * hden - hslit

theorem slit_majorant_hasSum {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {q : ℂ → ℂ}
    (hq : IsSlitMap p q) : ∀ᶠ z in 𝓝 (0 : ℂ), HasSum
      (fun k : ℕ => (slitR p : ℂ) * k * q z ^ k) (finitePart (extremal p z)) := by
  filter_upwards [slitDisk_mem_nhds_zero hp hp1, slit_majorant_germ hp hp1 hq] with z hz he
  have hnorm : ‖q z‖ < 1 := by simpa [disk] using hq.1.2.choose_spec.2.1 hz
  rw [← he]
  simpa [mul_assoc, Nat.descFactorial_one] using
    (hasSum_descFactorial_mul_geometric_of_norm_lt_one 1 hnorm).mul_left (slitR p : ℂ)

end Goodman
