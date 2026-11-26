-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
module

public import Goodman.SlitMajorant
public import Goodman.CoefficientComposition

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology

namespace Goodman

theorem coeff_koebe (n : ℕ) : coeff n (fun z : ℂ => z/(1-z)^2) = (n:ℂ) := by
  have ht := (Complex.hasFPowerSeriesOnBall_ofScalars_mul_add_zero 1 0).hasFPowerSeriesAt
  have he : (fun z : ℂ => z/(1-z)^2) =ᶠ[𝓝 0]
      (fun z => (0-1)/(1-z) + 1/(1-z)^2) := by
    filter_upwards [(show ContinuousAt (fun z : ℂ => 1-z) 0 by fun_prop).eventually_ne
        (show 1-(0:ℂ) ≠ 0 by simp)] with z hz
    field_simp
    ring
  rw [coeff_congr_of_eventuallyEq he]
  have hc := ht.analyticAt.hasFPowerSeriesAt.eq_formalMultilinearSeries ht
  simpa [coeff] using congrFun (FormalMultilinearSeries.ofScalars_series_injective ℂ ℂ hc) n

theorem slit_weight_sum {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {q : ℂ → ℂ}
    (hq : IsSlitMap p q) (n : ℕ) :
    slitR p * (∑ k ∈ Finset.range (n+1), (k:ℝ) * (coeff n (fun z => q z ^ k)).re) =
      (coeff n (fun z => finitePart (extremal p z))).re := by
  let K (z : ℂ) := z / (1-z)^2
  have hK : AnalyticAt ℂ K 0 := by dsimp [K]; fun_prop (disch := simp)
  have hqA := hq.1.1 0 (mem_of_mem_nhds (slitDisk_mem_nhds_zero hp hp1))
  have he : (fun z => (slitR p : ℂ) * (K ∘ q) z) =ᶠ[𝓝 (0:ℂ)]
      (fun z => finitePart (extremal p z)) := slit_majorant_germ hp hp1 hq
  have hc := coeff_congr_of_eventuallyEq he n
  rw [coeff_fun_const_mul, coeff_comp_finite hK hqA hq.2.1] at hc
  simpa [K, coeff_koebe, Complex.mul_re, Complex.re_sum, Complex.im_sum] using congrArg Complex.re hc

end Goodman
