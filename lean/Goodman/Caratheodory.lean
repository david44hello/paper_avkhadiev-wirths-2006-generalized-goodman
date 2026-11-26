-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
module

public import Goodman.Defs
public import Goodman.CaratheodoryBound
public import Goodman.CaratheodoryCoefficient

@[expose] public section

open Metric Filter
open scoped Topology
namespace Goodman

theorem caratheodory_all_orders (g : ℂ → ℂ) (z : ℂ) (R : ℝ) (hr : 0 < R)
    (hg : DifferentiableOn ℂ g (ball z R)) (hpos : ∀ w ∈ ball z R, 0 ≤ (g w).re)
    (l : ℕ) (hl : 1 ≤ l) :
    ‖iteratedDeriv l g z‖ ≤ 2*(l.factorial:ℝ)*(g z).re/R^l := by
  have hfac : (0:ℝ) < l.factorial := by exact_mod_cast l.factorial_pos
  have ht : ContinuousAt (fun r : ℝ => 2*(l.factorial:ℝ)*(g z).re/r^l) R :=
    continuousAt_const.div (continuousAt_id.pow _) (pow_ne_zero _ hr.ne')
  suffices h : ∀ᶠ r in 𝓝[<] R, ‖iteratedDeriv l g z‖ ≤ 2*(l.factorial:ℝ)*(g z).re/r^l by
    exact ge_of_tendsto ht.continuousWithinAt h
  filter_upwards [Ioo_mem_nhdsLT hr] with r h
  have hb := caratheodory_average_bound g z r R h.1 h.2 hg hpos l hl
  rw [caratheodory_coefficient g z r R h.1 h.2 hg l, norm_div, Complex.norm_natCast, div_le_iff₀ hfac] at hb
  convert hb using 1 <;> ring

/-- Carathéodory's positive-real-part coefficient bound on the unit disk. -/
theorem caratheodory_disk_coefficient {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g disk)
    (hpos : ∀ z ∈ disk, 0 ≤ (g z).re) {n : ℕ} (hn : 1 ≤ n) :
    ‖coeff n g‖ ≤ 2 * (g 0).re := by
  have h := caratheodory_all_orders g 0 1 zero_lt_one hg.differentiableOn hpos n hn
  have hfac : 0 < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  rw [coeff, norm_div, Complex.norm_natCast, div_le_iff₀ hfac]
  simpa [mul_comm, mul_left_comm, mul_assoc] using h

end Goodman
