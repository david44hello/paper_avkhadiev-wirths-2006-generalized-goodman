-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Goodman.CoefficientComposition
import Goodman.SlitPositivity

noncomputable section
open Filter
open scoped Topology

namespace Goodman

/-- Differentiation shifts the Taylor coefficients by one degree. -/
theorem coeff_deriv_succ (f : ℂ → ℂ) (m : ℕ) :
    coeff m (deriv f) = (m + 1 : ℂ) * coeff (m + 1) f := by
  rw [coeff, coeff, iteratedDeriv_succ', Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  field_simp [show (m.factorial : ℂ) ≠ 0 by exact_mod_cast m.factorial_ne_zero,
    show (m : ℂ) + 1 ≠ 0 by exact_mod_cast (Nat.succ_ne_zero m)]

private theorem coeff_shift_by_pow {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (k d : ℕ) :
    coeff (k + d) (fun z => z ^ k * f z) = coeff d f := by
  have mono (i : ℕ) : coeff i (fun z : ℂ => z ^ k) = if i = k then 1 else 0 := by
    rw [coeff, iteratedDeriv_fun_pow_zero]
    split_ifs with h
    · subst i
      simp [Nat.cast_ne_zero.mpr k.factorial_ne_zero]
    · simp
  rw [coeff_mul (f := fun z => z ^ k) (analyticAt_id.fun_pow k) hf]
  simp [mono, ite_mul, Finset.sum_ite_eq', Finset.mem_range.mpr (show k < k + d + 1 by omega)]

/-- After removing the power of the variable, the positive-degree terms in the
Lagrange kernel cancel between a function and its scaled derivative. -/
private theorem coeff_cancel_deriv {t : ℂ → ℂ} (ht : AnalyticAt ℂ t 0) (p : ℕ) :
    coeff (p + 1) (fun z => t z - (1 / (p + 1 : ℂ)) * (z * deriv t z)) = 0 := by
  have hscaled : AnalyticAt ℂ (fun z => (1 / (p + 1 : ℂ)) * (z * deriv t z)) 0 :=
    analyticAt_const.fun_mul (analyticAt_id.fun_mul ht.deriv)
  have hshift : coeff (p + 1) (fun z => z * deriv t z) = coeff p (deriv t) := by
    simpa only [pow_one, Nat.add_comm 1 p] using coeff_shift_by_pow ht.deriv 1 p
  have hsub (f g : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
      coeff (p + 1) (fun z => f z - g z) = coeff (p + 1) f - coeff (p + 1) g := by
    simp only [coeff, iteratedDeriv_fun_sub hf.contDiffAt hg.contDiffAt, sub_div]
  rw [hsub _ _ ht hscaled, coeff_fun_const_mul, hshift, coeff_deriv_succ]
  field_simp [show (p : ℂ) + 1 ≠ 0 by exact_mod_cast (Nat.succ_ne_zero p)]
  ring

/-- The degree-`m` coefficient from the `k`th monomial in the expansion of
`g'` is the Kronecker delta. The denominator is the removable slope of `s`. -/
theorem lagrange_kernel_coeff {s : ℂ → ℂ} (hs : AnalyticAt ℂ s 0)
    (hs0 : s 0 = 0) (hs1 : deriv s 0 = 1) {m k : ℕ} (hk : k ≤ m) :
    coeff m (fun z => (deriv s z * (1 / dslope s 0 z) ^ (m + 1)) * s z ^ k) =
      if k = m then 1 else 0 := by
  let u := dslope s 0
  have hu : AnalyticAt ℂ u 0 := ⟨_, hs.choose_spec.has_fpower_series_dslope_fslope⟩
  have hu0 : u 0 = 1 := (dslope_same ..).trans hs1
  have hne : u 0 ≠ 0 := hu0 ▸ one_ne_zero
  have hV : AnalyticAt ℂ (fun z => 1 / u z) 0 := analyticAt_const.fun_div hu hne
  have hfac : s = fun z => z * u z := by
    funext z
    simpa [u, hs0] using (sub_smul_dslope s (0 : ℂ) z).symm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hreduce : (fun z => (deriv s z * (1 / u z) ^ (k + d + 1)) * s z ^ k)
      =ᶠ[𝓝 0] fun z => z ^ k * (deriv s z * (1 / u z) ^ (d + 1)) := by
    filter_upwards [hu.continuousAt.eventually_ne hne] with z hz
    rw [congrFun hfac z, Nat.add_assoc, pow_add, mul_pow]
    simp only [one_div, inv_pow]
    field_simp [hz]
  rw [coeff_congr_of_eventuallyEq hreduce, coeff_shift_by_pow (hs.deriv.fun_mul
    (hV.fun_pow (d + 1)))]
  cases d with
  | zero => simp [coeff, hu0, hs1]
  | succ p =>
    let t (z : ℂ) := (u z)⁻¹ ^ (p + 1)
    have ht : AnalyticAt ℂ t 0 := (hu.inv hne).pow _
    have hgerm : (fun z => deriv s z * (1 / u z) ^ (p + 1 + 1))
        =ᶠ[𝓝 0] fun z => t z - (1 / (p + 1 : ℂ)) * (z * deriv t z) := by
      filter_upwards [hu.eventually_analyticAt, hu.continuousAt.eventually_ne hne] with z huz hz
      have hds : deriv s z = u z + z * deriv u z := by
        rw [hfac, deriv_fun_mul (c := fun y : ℂ => y) differentiableAt_id huz.differentiableAt]
        simp
      have hdt := ((huz.differentiableAt.hasDerivAt.inv hz).pow (p + 1)).deriv
      change deriv t z = _ at hdt
      rw [hds, hdt]
      simp only [t, Nat.cast_succ, Nat.add_sub_cancel, Pi.inv_apply, one_div, inv_pow, pow_succ]
      field_simp [hz, show (p : ℂ) + 1 ≠ 0 by exact_mod_cast (Nat.succ_ne_zero p)]
      ring
    rw [coeff_congr_of_eventuallyEq hgerm, coeff_cancel_deriv ht]
    simp

end Goodman
