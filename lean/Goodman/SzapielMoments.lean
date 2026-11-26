-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
module

public import Goodman.Caratheodory
public import Goodman.CoefficientComposition
public import Goodman.Extremal

@[expose] public section

open Filter Metric
open scoped Topology

namespace Goodman

private theorem szapiel_norm_lt_one {h : ℂ → ℂ} (hh : IsSchwarz h) {t : ℂ}
    (ht : ‖t‖ = 1) {z : ℂ} (hz : z ∈ disk) : ‖t * h z‖ < 1 := by
  simpa only [norm_mul, ht, one_mul] using (mem_ball_zero_iff.mp (hh.2.1 hz) : ‖h z‖ < 1)

private theorem szapiel_denom_ne {w : ℂ} (hw : ‖w‖ < 1) : 1 - w ≠ 0 := by
  apply sub_ne_zero.mpr
  rintro rfl
  simp at hw

/-- The Cayley transform of the rotated Schwarz map has positive real part on the disk. -/
theorem szapiel_re_pos {h : ℂ → ℂ} (hh : IsSchwarz h) {t : ℂ} (ht : ‖t‖ = 1)
    {z : ℂ} (hz : z ∈ disk) : 0 < ((1 + t * h z) / (1 - t * h z)).re := by
  let w := t * h z
  have hw : ‖w‖ < 1 := szapiel_norm_lt_one hh ht hz
  have hP := congrFun (poissonKernel_eq_re_herglotzRieszKernel (c := 0) (w := w)) 1
  simp only [poissonKernel_def, Function.comp_apply, herglotzRieszKernel_def, sub_zero,
    norm_one, one_pow] at hP
  rw [← hP]
  exact div_pos (sub_pos.mpr ((sq_lt_one_iff₀ (norm_nonneg w)).mpr hw))
    (pow_pos (norm_pos_iff.mpr (szapiel_denom_ne hw)) 2)

private theorem coeff_geometric (t : ℂ) (j : ℕ) :
    coeff j (fun w : ℂ => (1 - t * w)⁻¹) = t ^ j := by
  apply coeff_of_eventually_hasSum (a := fun k => t ^ k)
  have hc : ContinuousAt (fun w : ℂ => ‖t * w‖) 0 := by fun_prop
  filter_upwards [hc.eventually_lt continuousAt_const (by simp : ‖t * (0 : ℂ)‖ < 1)] with w hw
  apply (hasSum_geometric_of_norm_lt_one hw).congr_fun
  intro k
  rw [mul_pow, mul_comm]

/-- At positive orders the Cayley transform has twice the corresponding finite moment. -/
theorem szapiel_coeff_eq {h : ℂ → ℂ} (hh : IsSchwarz h) (t : ℂ) {n : ℕ} (hn : 1 ≤ n) :
    coeff n (fun z => (1 + t * h z) / (1 - t * h z)) =
      2 * ∑ j ∈ Finset.range (n + 1), coeff n (fun z => h z ^ j) * t ^ j := by
  let G (w : ℂ) := (1 - t * w)⁻¹
  have hG : AnalyticAt ℂ G 0 :=
    (analyticAt_const.fun_sub (analyticAt_const.fun_mul analyticAt_id)).inv (by simp)
  have hh0 := hh.1 0 (mem_ball_self zero_lt_one)
  have hd : ContinuousAt (fun z => 1 - t * h z) 0 :=
    continuousAt_const.sub (continuousAt_const.mul hh0.continuousAt)
  have he : (fun z => (1 + t * h z) / (1 - t * h z)) =ᶠ[𝓝 0]
      fun z => -1 + 2 * (G ∘ h) z := by
    filter_upwards [hd.eventually_ne (by simp [hh.2.2] : 1 - t * h 0 ≠ 0)] with z hz
    simp only [Function.comp_apply, G]
    field_simp [hz]
    ring
  rw [coeff_congr_of_eventuallyEq he]
  have hshift : coeff n (fun z => -1 + 2 * (G ∘ h) z) = 2 * coeff n (G ∘ h) := by
    simp only [coeff, iteratedDeriv_const_add (show 0 < n from hn), iteratedDeriv_const_mul_field,
      mul_div_assoc]
  rw [hshift, coeff_comp_finite hG hh0 hh.2.2]
  simp only [G, coeff_geometric, mul_comm (t ^ _) (coeff n _)]

/-- Szapiel's unit-circle bound for the degree-`n` moment of a Schwarz map. -/
theorem szapiel_moment_bound {h : ℂ → ℂ} (hh : IsSchwarz h) {t : ℂ} (ht : ‖t‖ = 1)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖∑ j ∈ Finset.range (n + 1), coeff n (fun z => h z ^ j) * t ^ j‖ ≤ 1 := by
  have hA : AnalyticOnNhd ℂ (fun z => (1 + t * h z) / (1 - t * h z)) disk := by
    intro z hz
    have ha : AnalyticAt ℂ (fun v => t * h v) z := analyticAt_const.fun_mul (hh.1 z hz)
    exact (analyticAt_const.fun_add ha).fun_div (analyticAt_const.fun_sub ha)
      (szapiel_denom_ne (szapiel_norm_lt_one hh ht hz))
  have hb := caratheodory_disk_coefficient hA (fun _ hz => (szapiel_re_pos hh ht hz).le) hn
  rw [szapiel_coeff_eq hh t hn, norm_mul, Complex.norm_two] at hb
  simp only [hh.2.2, mul_zero, add_zero, sub_zero, div_one, Complex.one_re, mul_one] at hb
  linarith

end Goodman
