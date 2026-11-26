-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Goodman.DiskModels

noncomputable section
open Set Metric

namespace Goodman

theorem halfPlane_convex : Convex ℝ halfPlane := convex_halfSpace_re_lt _

theorem halfPlane_zero : (0 : ℂ) ∈ halfPlane := by norm_num [halfPlane]

theorem halfPlane_isSource : IsSource halfPlane := by
  let _ : ContractibleSpace halfPlane := halfPlane_convex.contractibleSpace ⟨0, halfPlane_zero⟩
  exact ⟨isOpen_lt Complex.continuous_re continuous_const, inferInstanceAs (SimplyConnectedSpace halfPlane),
    (ne_univ_iff_exists_notMem _).mpr ⟨1, by norm_num [halfPlane]⟩⟩

private theorem mem_halfPlane_iff (x : ℂ) : x ∈ halfPlane ↔ ‖x‖ < ‖1-x‖ := by
  rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq]
  change x.re < 1 / 2 ↔ _
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  constructor <;> intro h <;> nlinarith

private theorem halfPlane_denom {x : ℂ} (hx : x ∈ halfPlane) : 1 - x ≠ 0 := by
  have h := (mem_halfPlane_iff x).mp hx
  intro he
  rw [he, norm_zero] at h
  exact (norm_nonneg x).not_gt h

theorem halfPlane_inverse_maps : MapsTo (fun x : ℂ => x/(1-x)) halfPlane disk := by
  intro x hx
  rw [disk, mem_ball_zero_iff, norm_div, div_lt_one₀ (norm_pos_iff.mpr (halfPlane_denom hx))]
  exact (mem_halfPlane_iff x).mp hx

theorem halfPlane_inverse_analytic : AnalyticOnNhd ℂ (fun x : ℂ => x/(1-x)) halfPlane :=
  fun _ hx => analyticAt_id.div (analyticAt_const.sub analyticAt_id) (halfPlane_denom hx)

/-- The centered disk chart for the sharp convex source. -/
theorem halfPlane_bihol : Bihol disk halfPlane (fun w : ℂ => w/(1+w)) := by
  have den {w : ℂ} (hw : w ∈ disk) : 1+w ≠ 0 := by
    intro he
    have : w = -1 := by linear_combination he
    simp [this, disk] at hw
  have sub_div {w : ℂ} (hw : w ∈ disk) : 1 - w/(1+w) = 1/(1+w) := by
    field_simp [den hw]
    ring
  refine ⟨fun _ hw => analyticAt_id.div (analyticAt_const.add analyticAt_id) (den hw),
    _, halfPlane_inverse_analytic, ?_, halfPlane_inverse_maps, ?_, ?_⟩
  · intro w hw
    rw [mem_halfPlane_iff, sub_div hw, norm_div, norm_div, norm_one]
    exact div_lt_div_of_pos_right (mem_ball_zero_iff.mp hw) (norm_pos_iff.mpr (den hw))
  · intro w hw
    dsimp only
    rw [sub_div hw]
    field_simp [den hw]
  · intro x hx
    dsimp only
    have he : 1 + x/(1-x) = 1/(1-x) := by
      field_simp [halfPlane_denom hx]
      ring
    rw [he]
    field_simp [halfPlane_denom hx]

theorem radius_halfPlane_zero : radius (planeDomain halfPlane) 0 = 1 := by
  have hd := ((hasDerivAt_id (0 : ℂ)).div
    ((hasDerivAt_const (0 : ℂ) (1 : ℂ)).add (hasDerivAt_id 0)) (by simp)).deriv
  have hr := radius_planeDomain_of_bihol halfPlane_bihol
  change deriv (fun w : ℂ => w/(1+w)) 0 = _ at hd
  simpa [hd] using hr

/-- Every positive-order complex coefficient equals the corresponding positive binomial sum. -/
theorem coeff_halfPlane_model {p : ℝ} (hp : 0 < p) (m : ℕ) :
    coeff (m+1) (fun x : ℂ => finitePart (extremal p (x/(1-x)))) = (D p 1 (m+1) : ℂ) := by
  have hF : AnalyticAt ℂ (finitePart ∘ extremal p) 0 := by
    simp only [Function.comp_def, finitePart_extremal]
    exact analyticAt_id.div ((analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).mul
      (analyticAt_const.sub analyticAt_id.div_const)) (by simp)
  have h := coeff_comp_diskKernel hF 1 m
  simp only [coeff_extremal_of_ne_zero hp.ne', one_pow, mul_one] at h
  simpa only [Function.comp_def, diskKernel, one_mul, D, Nat.add_sub_cancel, one_pow,
    mul_one, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast] using h

/-- Both normalized radii are one, so the positive real coefficient gives the derivative ratio. -/
theorem halfPlane_model_derivativeRatio {p : ℝ} (hp : 0 < p) {n : ℕ} (hn : 1 ≤ n) :
    derivativeRatio n (fun x : ℂ => extremal p (x/(1-x))) 0
      (radius (planeDomain halfPlane) 0) 1 = D p 1 n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [radius_halfPlane_zero, derivativeRatio_eq_affine_coeff _ _ 0 zero_le_one zero_le_one _ (by omega)]
  simp only [Complex.ofReal_one, one_mul, zero_add, sub_zero, div_one, coeff_halfPlane_model hp]
  apply Complex.norm_of_nonneg
  unfold D
  exact Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity)) (A_positive hp (by omega)).le

/-- For fixed `p`, the same map on the half-plane attains every derivative bound at zero. -/
theorem convexSharpModel : ConvexSharpModel := by
  intro p hp hp1
  obtain ⟨hU, hext, hrad, hparam⟩ := extremal_model_data hp hp1
  refine ⟨halfPlane_isSource, halfPlane_convex, halfPlane_zero, hU,
    hext.comp_analyticOnNhd halfPlane_inverse_analytic halfPlane_inverse_maps,
    (mapsTo_image (extremal p) disk).comp halfPlane_inverse_maps, ?_, hparam, ?_⟩
  · simp [extremal]
  · intro n hn
    rw [hrad]
    exact halfPlane_model_derivativeRatio hp (by omega)

theorem convexSharpness_of_convexSharpModel (h : ConvexSharpModel) : ConvexSharpness := by
  intro p hp hp1 n hn
  obtain ⟨hΩ, hc, hx, hU, hG, hm, hzero, hparam, he⟩ := h p hp hp1
  exact ⟨halfPlane, extremalTarget p, 0, 0, _, hΩ, hc, hx, hU, hG, hm, hzero, hparam, he n hn⟩

theorem convexSharpness : ConvexSharpness := convexSharpness_of_convexSharpModel convexSharpModel

/--
info: 'Goodman.convexSharpModel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms convexSharpModel

/--
info: 'Goodman.convexSharpness' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms convexSharpness

end Goodman
