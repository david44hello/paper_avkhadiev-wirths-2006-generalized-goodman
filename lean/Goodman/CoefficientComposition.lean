-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
module

public import Goodman.Defs

@[expose] public section

open Filter
open scoped Topology

namespace Goodman

theorem coeff_congr_of_eventuallyEq {f g : ℂ → ℂ} (h : f =ᶠ[𝓝 0] g) (n : ℕ) :
    coeff n f = coeff n g := by
  rw [coeff, coeff, h.iteratedDeriv_eq n]

@[simp] theorem coeff_fun_const_mul (n : ℕ) (c : ℂ) (f : ℂ → ℂ) :
    coeff n (fun z => c * f z) = c * coeff n f := by
  simp only [coeff, iteratedDeriv_const_mul_field, mul_div_assoc]

private theorem iteratedDeriv_pow_mul_zero {q g : ℂ → ℂ} (hq : AnalyticAt ℂ q 0)
    (hg : AnalyticAt ℂ g 0) (hq0 : q 0 = 0) {n m : ℕ} (hn : n < m) :
    iteratedDeriv n (q ^ m * g) 0 = 0 := by
  have h₁ : 1 ≤ analyticOrderAt q 0 :=
    Order.one_le_iff_ne_zero.mpr (hq.analyticOrderAt_ne_zero.mpr hq0)
  apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ((hq.pow m).mul hg)).mp _ n hn
  rw [analyticOrderAt_mul (hq.pow m) hg, analyticOrderAt_pow hq]
  calc
    (m : ℕ∞) = m • (1 : ℕ∞) := by simp
    _ ≤ m • analyticOrderAt q 0 := nsmul_le_nsmul_right h₁ m
    _ ≤ _ := le_self_add

/-- If the inner function vanishes at zero, only the first `n + 1` Taylor terms of the
outer function contribute to the coefficient of degree `n` in their composition. -/
theorem coeff_comp_finite {F q : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) (hq : AnalyticAt ℂ q 0)
    (hq0 : q 0 = 0) (n : ℕ) :
    coeff n (F ∘ q) = ∑ k ∈ Finset.range (n + 1), coeff k F * coeff n (fun z => q z ^ k) := by
  obtain ⟨R, hR, hTaylor⟩ := hF.exists_eventuallyEq_sum_add_pow_mul (n + 1)
  let term (k : ℕ) (z : ℂ) := coeff k F * q z ^ k
  let P (z : ℂ) := ∑ k ∈ Finset.range (n + 1), term k z
  have hterm (k : ℕ) : AnalyticAt ℂ (term k) 0 := analyticAt_const.mul (hq.pow k)
  have hP : AnalyticAt ℂ P 0 := Finset.analyticAt_fun_sum _ fun k _ => hterm k
  have hRq := hR.comp_of_eq hq hq0
  have hexp : F ∘ q =ᶠ[𝓝 0] P + q ^ (n + 1) * (R ∘ q) := by
    have ht : Tendsto q (𝓝 0) (𝓝 0) := by simpa only [ContinuousAt, hq0] using hq.continuousAt
    filter_upwards [ht.eventually hTaylor] with z hz
    simpa only [Function.comp_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, P, term,
      coeff, smul_eq_mul, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hz
  rw [coeff_congr_of_eventuallyEq hexp, coeff,
    iteratedDeriv_add hP.contDiffAt ((hq.pow (n + 1)).mul hRq).contDiffAt,
    iteratedDeriv_pow_mul_zero hq hRq hq0 (Nat.lt_succ_self n), add_zero]
  unfold P
  rw [iteratedDeriv_fun_sum (fun k _ => (hterm k).contDiffAt), Finset.sum_div]
  exact Finset.sum_congr rfl fun k _ => coeff_fun_const_mul n (coeff k F) (fun z => q z ^ k)

end Goodman
