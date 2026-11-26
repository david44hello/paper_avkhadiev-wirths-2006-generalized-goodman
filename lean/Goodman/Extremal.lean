-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Goodman.Defs

noncomputable section
open Set Filter
open scoped Topology

namespace Goodman

private def denominator (p : ℝ) (z : ℂ) : ℂ := (1 - (p : ℂ) * z) * (1 - z / p)

theorem finitePart_extremal (p : ℝ) (z : ℂ) :
    finitePart (extremal p z) = z / ((1 - (p : ℂ) * z) * (1 - z / p)) := by
  change finitePart (if denominator p z = 0 then OnePoint.infty else
    ((z / denominator p z : ℂ) : Sphere)) = z / denominator p z
  split
  · rename_i hd
    rw [hd, div_zero]
    rfl
  · rfl

private lemma norm_lt_one_of_mem_disk {z : ℂ} (hz : z ∈ disk) : ‖z‖ < 1 := by
  simpa [disk, Metric.mem_ball] using hz

/-- Equal sphere values imply the cross-product identity even at a pole.
Its factorization leaves only the diagonal inside the open disk. -/
theorem extremal_injOn {p : ℝ} (hp : p ≠ 0) : InjOn (extremal p) disk := by
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  intro z hz w hw heq
  change (if denominator p z = 0 then OnePoint.infty else ((z / denominator p z : ℂ) : Sphere)) =
    (if denominator p w = 0 then OnePoint.infty else ((w / denominator p w : ℂ) : Sphere)) at heq
  have hcross : z * denominator p w = w * denominator p z := by
    split at heq <;> split at heq
    · simp_all
    · simp at heq
    · simp at heq
    · exact (div_eq_div_iff (by assumption) (by assumption)).mp (OnePoint.coe_injective heq)
  have hfact : (z - w) * (1 - z * w) = 0 := by
    calc
      _ = z * denominator p w - w * denominator p z := by
        unfold denominator
        field_simp
        ring
      _ = 0 := sub_eq_zero.mpr hcross
  rcases mul_eq_zero.mp hfact with h | h
  · exact sub_eq_zero.mp h
  · have hnorm : ‖z * w‖ < 1 := by
      rw [norm_mul]
      calc
        ‖z‖ * ‖w‖ ≤ 1 * ‖w‖ := mul_le_mul_of_nonneg_right (norm_lt_one_of_mem_disk hz).le (norm_nonneg _)
        _ < 1 := by simpa using norm_lt_one_of_mem_disk hw
    rw [← sub_eq_zero.mp h, norm_one] at hnorm
    exact (lt_irrefl _ hnorm).elim

/-- Uniqueness of scalar Taylor coefficients for an expansion on a neighborhood of zero. -/
theorem coeff_of_eventually_hasSum {f : ℂ → ℂ} {a : ℕ → ℂ}
    (hs : ∀ᶠ z in 𝓝 0, HasSum (fun k ↦ z ^ k * a k) (f z)) (n : ℕ) :
    coeff n f = a n := by
  have h : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ a) 0 := by
    simpa [hasFPowerSeriesAt_iff, FormalMultilinearSeries.coeff_ofScalars] using hs
  have heq := h.analyticAt.hasFPowerSeriesAt.eq_formalMultilinearSeries h
  simpa [coeff, FormalMultilinearSeries.coeff_ofScalars] using
    congrArg (fun s : FormalMultilinearSeries ℂ ℂ ℂ ↦ s.coeff n) heq

/-- The product of the geometric series in `p*z` and `z/p`, shifted by the numerator `z`. -/
theorem extremal_hasSum {p : ℝ} (hp : p ≠ 0) {z : ℂ}
    (h₁ : ‖(p : ℂ) * z‖ < 1) (h₂ : ‖z / p‖ < 1) :
    HasSum (fun k ↦ z ^ k * (A p k : ℂ)) (finitePart (extremal p z)) := by
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  have hs := (hasSum_sum_range_mul_of_summable_norm
    (summable_norm_geometric_of_norm_lt_one h₁)
    (summable_norm_geometric_of_norm_lt_one h₂)).mul_left z
  rw [(hasSum_geometric_of_norm_lt_one h₁).tsum_eq,
    (hasSum_geometric_of_norm_lt_one h₂).tsum_eq] at hs
  apply (hasSum_nat_add_iff' 1).mp
  simp only [Finset.sum_range_one, pow_zero, A, Finset.range_zero, Finset.sum_empty,
    zero_div, Complex.ofReal_zero, mul_zero, sub_zero]
  rw [finitePart_extremal, div_eq_mul_inv, mul_inv]
  apply hs.congr_fun
  intro k
  simp only [Nat.add_sub_cancel, Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_pow,
    Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ k := by simpa using hj
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hjk
  simp only [Nat.add_sub_cancel_left, mul_pow, div_pow, pow_add, pow_succ, two_mul]
  field_simp

/-- Scaling the argument multiplies the extremal's degree-`n` coefficient by `a^n`. -/
theorem coeff_extremal_scaled {p : ℝ} (hp : p ≠ 0) (a : ℂ) (n : ℕ) :
    coeff n (fun z ↦ finitePart (extremal p (a * z))) = a ^ n * (A p n : ℂ) := by
  apply coeff_of_eventually_hasSum
  have h₁ : ContinuousAt (fun z : ℂ ↦ ‖(p : ℂ) * (a * z)‖) 0 := by fun_prop
  have h₂ : ContinuousAt (fun z : ℂ ↦ ‖(a * z) / (p : ℂ)‖) 0 := by fun_prop
  filter_upwards [h₁.eventually_lt continuousAt_const (by simp : ‖(p : ℂ) * (a * 0)‖ < 1),
    h₂.eventually_lt continuousAt_const (by simp : ‖(a * 0) / (p : ℂ)‖ < 1)] with z hz₁ hz₂
  apply (extremal_hasSum hp hz₁ hz₂).congr_fun
  intro k
  rw [mul_pow]
  ring

/-- Coefficients of the actual finite coordinate, including the Koebe endpoint. -/
theorem coeff_extremal_of_ne_zero {p : ℝ} (hp : p ≠ 0) (n : ℕ) :
    coeff n (finitePart ∘ extremal p) = (A p n : ℂ) := by
  simpa [Function.comp_def] using coeff_extremal_scaled hp 1 n

private lemma deriv_extremal_zero {p : ℝ} (hp : p ≠ 0) :
    deriv (finitePart ∘ extremal p) 0 = 1 := by
  simpa [coeff, A] using coeff_extremal_of_ne_zero hp 1

private lemma analyticAt_denominator (p : ℝ) (x : ℂ) : AnalyticAt ℂ (denominator p) x := by
  unfold denominator
  simp only [div_eq_mul_inv]
  fun_prop

/-- At a nonzero argument the reciprocal chart is given by the denominator divided by `z`. -/
private lemma extremal_recip {p : ℝ} {z : ℂ} (hz : z ≠ 0) :
    extremal p z = fromRecip (denominator p z / z) := by
  change (if denominator p z = 0 then OnePoint.infty else ((z / denominator p z : ℂ) : Sphere)) = _
  by_cases hd : denominator p z = 0 <;> simp [hd, fromRecip, hz]

private lemma extremal_simplePole {p : ℝ} (hp : 0 < p) (hp' : p < 1) :
    SimplePoleAt (extremal p) p := by
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hden : denominator p p = 0 := by simp [denominator, hpc]
  refine ⟨fun z ↦ denominator p z / z, (analyticAt_denominator p p).div analyticAt_id hpc,
    by simp [hden], ?_, ?_⟩
  · have h₁ := (hasDerivAt_const (p : ℂ) (1 : ℂ)).sub ((hasDerivAt_id (p : ℂ)).const_mul (p : ℂ))
    have h₂ := (hasDerivAt_const (p : ℂ) (1 : ℂ)).sub ((hasDerivAt_id (p : ℂ)).div_const (p : ℂ))
    have hder := ((h₁.mul h₂).div (hasDerivAt_id (p : ℂ)) hpc).deriv
    have hs : (p : ℂ) * p - 1 ≠ 0 := by
      exact_mod_cast (show p * p - 1 ≠ 0 by nlinarith [mul_pos (sub_pos.mpr hp') (by linarith : 0 < 1 + p)])
    rw [show deriv (fun z ↦ denominator p z / z) (p : ℂ) = _ from hder]
    simp [hpc, hs]
  · filter_upwards [eventually_ne_nhds hpc] with z hz using extremal_recip hz

/-- The rational extremal as a normalized univalent map into the Riemann sphere. -/
theorem isM_extremal {p : ℝ} (hp : 0 < p) (hp' : p < 1) : IsM p (extremal p) := by
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  refine ⟨?_, extremal_injOn hp.ne', by simp [extremal, hpc], extremal_simplePole hp hp',
    by simp [extremal], deriv_extremal_zero hp.ne'⟩
  intro x _
  by_cases hx : x = 0
  · subst x
    have hd : denominator p 0 ≠ 0 := by simp [denominator]
    refine ⟨fun z ↦ z / denominator p z, analyticAt_id.div (analyticAt_denominator p 0) hd,
      Or.inl ?_⟩
    filter_upwards [(analyticAt_denominator p 0).continuousAt.eventually_ne hd] with z hz
    exact ite_eq_right hz
  · refine ⟨fun z ↦ denominator p z / z, (analyticAt_denominator p x).div analyticAt_id hx,
      Or.inr ?_⟩
    filter_upwards [eventually_ne_nhds hx] with z hz using extremal_recip hz

/-- At the boundary parameter the affine coordinate is the normalized Koebe function. -/
theorem finitePart_extremal_one :
    finitePart ∘ extremal 1 = fun z : ℂ ↦ z / (1 - z) ^ 2 := by
  funext z
  simp [finitePart_extremal, pow_two]

theorem coeff_extremal_one (n : ℕ) : coeff n (finitePart ∘ extremal 1) = (n : ℂ) := by
  simpa [A] using coeff_extremal_of_ne_zero (p := 1) one_ne_zero n

theorem isS_koebe : IsS (fun z : ℂ ↦ z / (1 - z) ^ 2) := by
  have hone {z : ℂ} (hz : z ∈ disk) : 1 - z ≠ 0 := by
    intro heq
    have hlt := norm_lt_one_of_mem_disk hz
    rw [← sub_eq_zero.mp heq, norm_one] at hlt
    exact (lt_irrefl _ hlt)
  have hval {z : ℂ} (hz : z ∈ disk) :
      extremal 1 z = ((z / (1 - z) ^ 2 : ℂ) : Sphere) := by
    simp [extremal, hone hz, pow_two]
  refine ⟨fun x hx ↦ ?_, ?_, by simp, ?_⟩
  · exact analyticAt_id.div ((analyticAt_const.sub analyticAt_id).pow 2) (pow_ne_zero _ (hone hx))
  · intro z hz w hw h
    apply extremal_injOn (p := 1) one_ne_zero hz hw
    rw [hval hz, hval hw]
    exact congrArg (fun u : ℂ ↦ (u : Sphere)) h
  · rw [← finitePart_extremal_one]
    exact deriv_extremal_zero one_ne_zero

end Goodman
