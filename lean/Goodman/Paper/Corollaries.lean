-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
module

public import Goodman.Paper.Coefficients

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology
namespace Goodman

/-- Multiplication by a holomorphic map into the open disk gives a strict contraction at the origin. -/
theorem schwarz_of_disk_factor {ω : ℂ → ℂ} (hω : AnalyticOnNhd ℂ ω disk)
    (hm : MapsTo ω disk disk) : IsSchwarz (fun z => z * ω z) ∧ ‖deriv (fun z => z * ω z) 0‖ < 1 := by
  have h0 : (0 : ℂ) ∈ disk := Metric.mem_ball_self zero_lt_one
  have dz := (hasDerivAt_id (0:ℂ)).fun_mul (hω 0 h0).differentiableAt.hasDerivAt
  refine ⟨⟨fun z hz => analyticAt_id.mul (hω z hz), ?_, by simp⟩, ?_⟩
  · intro z hz
    rw [disk, Metric.mem_ball, dist_zero_right, norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) (mem_ball_zero_iff.mp hz)
      (mem_ball_zero_iff.mp (hm hz)).le
  · have hd : HasDerivAt (fun z : ℂ => z * ω z) (ω 0) 0 := by simpa using dz
    rw [hd.deriv]
    exact mem_ball_zero_iff.mp (hm h0)

/-- In the version of subordination with a factor taking values in the open disk, equality
is impossible, while dilations of the extremal approach the bound. -/
theorem strict_of_disk_factor (H1 : Robertson) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {f : ℂ → Sphere} (hf : IsM p f) {ω : ℂ → ℂ} (hω : AnalyticOnNhd ℂ ω disk)
    (hm : MapsTo ω disk disk) {n : ℕ} (hn : 1 ≤ n) :
    ‖coeff n (fun z => finitePart (f (z * ω z)))‖ < A p n := by
  obtain ⟨hs,hd⟩ := schwarz_of_disk_factor hω hm
  have hu := theorem_one_bound H1 p hp hp1 f hf _ hs (fun _ => 1)
    ⟨fun _ _ => analyticAt_const, by simp⟩ n hn
  simp only [one_mul] at hu
  refine lt_of_le_of_ne hu ?_
  intro heq
  exact hd.ne (MainReduction.derivative_norm_one_of_equality transfer slit_proved
    (proposition_seven H1) hp hp1 hf hs hn heq)

/-- Dilations give the exact coefficient up to the factor rⁿ, hence the same supremum. -/
theorem dilation_modulus {p : ℝ} (hp : 0 < p) {n : ℕ} (hn : 1 ≤ n)
    {r : ℝ} (hr : 0 ≤ r) :
    ‖coeff n (fun z => finitePart (extremal p ((r : ℂ)*z)))‖ = r^n * A p n := by
  rw [coeff_extremal_scaled hp.ne', norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr, Complex.norm_real,Real.norm_eq_abs,abs_of_pos (A_positive hp hn)]

theorem dilation_sharp_limit {p : ℝ} (hp : 0 < p) {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun r : ℝ => ‖coeff n (fun z => finitePart (extremal p ((r : ℂ)*z)))‖)
      (𝓝[<] (1:ℝ)) (𝓝 (A p n)) := by
  have hc : ContinuousAt (fun r : ℝ => r^n * A p n) 1 := by fun_prop
  have ht : Tendsto (fun r : ℝ => r^n * A p n) (𝓝[<] (1:ℝ)) (𝓝 (A p n)) := by
    simpa using hc.continuousWithinAt.tendsto (s:=Iio 1)
  apply ht.congr'
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
  exact (dilation_modulus hp hn hr.1.le).symm

theorem bieberbach_bound_from_robertson (H1 : Robertson) {F : ℂ → ℂ} (hF : IsS F)
    {n : ℕ} (hn : 1 ≤ n) : ‖coeff n F‖ ≤ (n : ℝ) := by
  simpa using lemma_six H1 F hF (fun _ => 1) ⟨fun _ _ => analyticAt_const, by simp⟩ n hn

end Goodman
