-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
module

public import Goodman.DeficitSum
public import Goodman.Extremal
public import Goodman.SlitPositivity
public import Goodman.SlitTransport
public import Goodman.SlitWeights

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology

namespace Goodman

/-- The first coefficient of the transported product gives the strict deficit. -/
theorem deficit_of_product (hprod : ProductClaim) : DeficitClaim := by
  intro p hp hp1 q hq f hf E hE n hn
  obtain ⟨Φ, hΦ, hΦ0, hΦ1, hb, he⟩ := exists_slit_product hp hp1 hq hf hE hprod
  let w (k : ℕ) := (coeff n (fun z => q z ^ k)).re
  have hw (k : ℕ) : 0 ≤ w k := (slit_pow_coeff_nonneg hp hp1 hq k n).2
  have hc (k : ℕ) : coeff n (fun z => q z ^ k) = (w k : ℂ) :=
    Complex.ext rfl (by simpa using (slit_pow_coeff_nonneg hp hp1 hq k n).1)
  have h1 : w 1 = (coeff n q).re := by simp [w]
  have hmass : slitR p * (∑ k ∈ Finset.range (n+1), (k:ℝ) * w k) = A p n := by
    have hext := congrArg Complex.re (coeff_extremal_of_ne_zero hp.ne' n)
    exact (slit_weight_sum hp hp1 hq n).trans hext
  have hbound := norm_sum_le_first_deficit hn (fun k => coeff k Φ) w hw
    (by simpa [coeff] using hΦ0) hb
  rw [hΦ1, h1] at hbound
  have hqA := hq.1.1 0 (mem_of_mem_nhds (slitDisk_mem_nhds_zero hp hp1))
  have he' : (fun z => E z * finitePart (f z)) =ᶠ[𝓝 0]
      (fun z => (slitR p : ℂ) * (Φ ∘ q) z) := he
  rw [coeff_congr_of_eventuallyEq he', coeff_fun_const_mul, coeff_comp_finite hΦ hqA hq.2.1,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (slitR_pos hp)]
  simp_rw [hc]
  calc
    _ ≤ slitR p * ((∑ k ∈ Finset.range (n+1), (k:ℝ)*w k) -
          (coeff n q).re * (1-‖E 0‖)) := mul_le_mul_of_nonneg_left hbound (slitR_pos hp).le
    _ = _ := by rw [mul_sub, hmass]; ring

end Goodman
