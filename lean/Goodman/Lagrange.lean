-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
module

public import Goodman.LagrangeKernel
public import Goodman.Transfer

@[expose] public section

noncomputable section
open Filter
open scoped Topology

namespace Goodman

/-- Analytic Lagrange inversion for the germ identity `H = g ∘ s`, as used in
Theorem 3(b). The factor `1 / dslope s 0 z` is the removable quotient `z / s z`. -/
theorem lagrange_inversion_coeff {s g H : ℂ → ℂ} (hs : AnalyticAt ℂ s 0)
    (hs0 : s 0 = 0) (hs1 : deriv s 0 = 1) (hg : AnalyticAt ℂ g 0)
    (hH : H =ᶠ[𝓝 0] g ∘ s) {n : ℕ} (hn : 1 ≤ n) :
    (n : ℂ) * coeff n g =
      coeff (n - 1) (fun z => deriv H z * (1 / dslope s 0 z) ^ n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let W (z : ℂ) := deriv s z * (1 / dslope s 0 z) ^ (m + 1)
  have hu : AnalyticAt ℂ (dslope s 0) 0 := ⟨_, hs.choose_spec.has_fpower_series_dslope_fslope⟩
  have hu0 : dslope s 0 0 ≠ 0 := by simp [dslope_same, hs1]
  have hW : AnalyticAt ℂ W 0 := hs.deriv.fun_mul
    ((analyticAt_const.fun_div hu hu0).fun_pow _)
  have hmap : Tendsto s (𝓝 0) (𝓝 0) := by simpa [ContinuousAt, hs0] using hs.continuousAt
  have hchain : (fun z => deriv H z * (1 / dslope s 0 z) ^ (m + 1))
      =ᶠ[𝓝 0] fun z => W z * deriv g (s z) := by
    filter_upwards [hH.deriv, hs.eventually_analyticAt,
      hmap.eventually hg.eventually_analyticAt] with z hdz hsz hgz
    rw [hdz, deriv_comp z hgz.differentiableAt hsz.differentiableAt]
    unfold W
    ring
  simp only [Nat.succ_sub_one, Nat.cast_succ]
  rw [← coeff_deriv_succ, coeff_congr_of_eventuallyEq hchain,
    transfer_coeff_composition hW hs hs0 hg.deriv]
  symm
  calc
    _ = ∑ k ∈ Finset.range (m + 1), coeff k (deriv g) * (if k = m then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact congrArg (coeff k (deriv g) * ·)
        (lagrange_kernel_coeff hs hs0 hs1 (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
    _ = _ := by simp [mul_ite, Finset.sum_ite_eq']

end Goodman
