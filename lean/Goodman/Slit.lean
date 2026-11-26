-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Goodman.SlitGeometry
import Goodman.SlitPositivity
import Goodman.SlitMajorant

namespace Goodman

open Filter Set
open scoped Topology

/-- The normalized conformal slit chart has positive Taylor coefficients, and its
weighted geometric series recovers the extremal function near the origin. -/
theorem slit_proved : SlitClaim := by
  intro p hp hp1
  obtain ⟨q, hq⟩ := exists_isSlitMap hp hp1
  exact ⟨q, hq, slit_coeff_pos hp hp1 hq, slit_majorant_hasSum hp hp1 hq⟩

theorem hasDerivAt_slit_zero {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {q : ℂ → ℂ}
    (hq : IsSlitMap p q) : HasDerivAt q (1 / (slitR p : ℂ)) 0 := by
  have hU := slitDisk_mem_nhds_zero hp hp1
  have hd := (hq.1.1 0 (mem_of_mem_nhds hU)).differentiableAt.hasDerivAt
  have hid := hasDerivAt_id (0 : ℂ)
  have hl : HasDerivAt (fun z => z * (1 + q z)^2) 1 0 := by
    simpa [hq.2.1] using hid.fun_mul (((hasDerivAt_const (0 : ℂ) (1 : ℂ)).fun_add hd).fun_pow 2)
  have hr : HasDerivAt (fun z => (slitR p : ℂ) * q z * (1 + z)^2)
      ((slitR p : ℂ) * deriv q 0) 0 := by
    simpa [hq.2.1] using (hd.const_mul (slitR p : ℂ)).fun_mul
      (((hasDerivAt_const (0 : ℂ) (1 : ℂ)).fun_add hid).fun_pow 2)
  have he : (fun z => z * (1 + q z)^2) =ᶠ[𝓝 (0 : ℂ)]
      (fun z => (slitR p : ℂ) * q z * (1 + z)^2) := by
    filter_upwards [hU] with z hz using hq.2.2 z hz
  have hder := hl.unique (hr.congr_of_eventuallyEq he)
  apply hd.congr_deriv
  apply (eq_div_iff (Complex.ofReal_ne_zero.mpr (slitR_pos hp).ne')).2
  simpa [mul_comm] using hder.symm

end Goodman
