-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Goodman.Paper.Coefficients

noncomputable section
open Set Filter
open scoped Topology
namespace Goodman

/-- The base estimate uses only the unweighted Bieberbach bound after passage to slit coordinates. -/
theorem base_reduction_from_schlicht
    (hB : ∀ F : ℂ → ℂ, IsS F → ∀ k : ℕ, 1 ≤ k → ‖coeff k F‖ ≤ (k : ℝ))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {f : ℂ → Sphere} (hf : IsM p f)
    {n : ℕ} (hn : 1 ≤ n) : ‖coeff n (finitePart ∘ f)‖ ≤ A p n := by
  obtain ⟨q,hq,_,_⟩ := slit_proved p hp hp1
  obtain ⟨F,hF,he⟩ := exists_slit_normalized hp hp1 hq hf
  have h0 : (0 : ℂ) ∈ disk := Metric.mem_ball_self zero_lt_one
  have hqA := hq.1.1 _ (mem_of_mem_nhds (slitDisk_mem_nhds_zero hp hp1))
  let w := fun k : ℕ => (coeff n (fun z => q z ^ k)).re
  have hw k : 0 ≤ w k := (slit_pow_coeff_nonneg hp hp1 hq k n).2
  have hc k : coeff n (fun z => q z ^ k) = (w k : ℂ) :=
    Complex.ext rfl (by simpa using (slit_pow_coeff_nonneg hp hp1 hq k n).1)
  have hR := slitR_pos hp
  have mass := (slit_weight_sum hp hp1 hq n).trans
    (congrArg Complex.re (coeff_extremal_of_ne_zero hp.ne' n))
  have hzero : coeff 0 F = 0 := by simpa [coeff] using hF.2.2.1
  have hone : coeff 1 F = 1 := by simp [coeff,hF.2.2.2]
  have sumBound := norm_sum_le_first_deficit hn (fun k => coeff k F) w hw hzero (hB F hF)
  simp only [hone,norm_one,sub_self,mul_zero,sub_zero] at sumBound
  have he' : finitePart ∘ f =ᶠ[𝓝 0] fun z => (slitR p : ℂ) * (F ∘ q) z := he
  rw [coeff_congr_of_eventuallyEq he', coeff_fun_const_mul, coeff_comp_finite (hF.1 0 h0) hqA hq.2.1,
    norm_mul, Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR]
  simp_rw [hc]
  exact (mul_le_mul_of_nonneg_left sumBound hR.le).trans_eq mass

end Goodman
