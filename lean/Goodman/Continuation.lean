-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
module

public import Goodman.ChartInvariance
public import Goodman.MainReduction

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology

namespace Goodman

/-- A normalized simple-pole map has an analytic regularization on the whole disk. -/
theorem IsM.exists_regularization {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {f : ℂ → Sphere} (hf : IsM p f) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F disk ∧
      ∀ z : ℂ, z ≠ p → F z = (z - p) * finitePart (f z) := by
  classical
  obtain ⟨u, hu, hu0, hud, heq⟩ := hf.2.2.2.1
  let F : ℂ → ℂ := Function.update (fun z : ℂ => (z-p) * finitePart (f z)) p (deriv u p)⁻¹
  have Foff (z : ℂ) (hz : z ≠ p) : F z = (z-p) * finitePart (f z) :=
    Function.update_of_ne hz ..
  refine ⟨F, ?_, Foff⟩
  have hpD : (p : ℂ) ∈ disk := by simpa [disk, abs_of_pos hp] using hp1
  intro z hz
  by_cases h : z = p
  · subst z
    have hd : AnalyticAt ℂ (dslope u (p : ℂ)) p := by
      apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      · filter_upwards [self_mem_nhdsWithin, hu.eventually_analyticAt.filter_mono nhdsWithin_le_nhds]
          with t ht hta
        exact (differentiableAt_dslope_of_ne ht).2 hta.differentiableAt
      · exact continuousAt_dslope_same.mpr hu.differentiableAt
    have hd0 : dslope u (p : ℂ) p ≠ 0 := by simpa [dslope_same] using hud
    apply (hd.inv hd0).congr
    filter_upwards [heq, hd.continuousAt.eventually_ne hd0] with t ht ht'
    by_cases htp : t = p
    · subst t
      simp [F,dslope_same]
    · rw [Foff _ htp, ht]
      have ht0 : t - (p : ℂ) ≠ 0 := sub_ne_zero.mpr htp
      have hmul : (t - p) * dslope u p t = u t := by simpa [hu0] using sub_smul_dslope u (p : ℂ) t
      have hu' : u t ≠ 0 := hmul ▸ mul_ne_zero ht0 ht'
      simp only [fromRecip,if_neg hu',Pi.inv_apply]
      change (dslope u p t)⁻¹ = (t-p) * (u t)⁻¹
      rw [← hmul]
      field_simp
  · have hfin : f z ≠ OnePoint.infty := by
      intro ha
      exact h (hf.2.1 hz hpD (ha.trans hf.2.2.1.symm))
    apply ((analyticAt_id.sub analyticAt_const).mul (MainReduction.finite_germ hf.1 hz hfin)).congr
    filter_upwards [continuousAt_id.eventually_ne h] with t ht
    exact (Foff t ht).symm

/-- Equality of the finite germs at zero determines the sphere-valued function, including its pole. -/
theorem IsM.eqOn_of_germ {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {f g : ℂ → Sphere}
    (hf : IsM p f) (hg : IsM p g) (h : (finitePart ∘ f) =ᶠ[𝓝 (0 : ℂ)] (finitePart ∘ g)) :
    EqOn f g disk := by
  obtain ⟨F,hF,hFoff⟩ := hf.exists_regularization hp hp1
  obtain ⟨G,hG,hGoff⟩ := hg.exists_regularization hp hp1
  have hp0 : (0 : ℂ) ≠ p := by exact_mod_cast hp.ne
  have h0 : (0 : ℂ) ∈ disk := Metric.mem_ball_self zero_lt_one
  have hnear : F =ᶠ[𝓝 (0 : ℂ)] G := by
    filter_upwards [h,continuousAt_id.eventually_ne hp0] with t ht htp
    rw [hFoff t htp, hGoff t htp]
    exact congrArg ((t-(p:ℂ)) * ·) ht
  have hglob := hF.eqOn_of_preconnected_of_eventuallyEq hG
    (convex_ball (0:ℂ) (1:ℝ)).isPreconnected h0 hnear
  intro z hz
  by_cases hzp : z = p
  · subst z
    exact hf.2.2.1.trans hg.2.2.1.symm
  · have hpeq := hglob hz
    rw [hFoff _ hzp,hGoff _ hzp] at hpeq
    have hval := mul_left_cancel₀ (sub_ne_zero.mpr hzp) hpeq
    have hpD : (p : ℂ) ∈ disk := by simpa [disk, abs_of_pos hp] using hp1
    have fin {t : ℂ → Sphere} (ht : IsM p t) : t z ≠ OnePoint.infty :=
      fun hi => hzp (ht.2.1 hz hpD (hi.trans ht.2.2.1.symm))
    obtain ⟨a,ha⟩ := OnePoint.ne_infty_iff_exists.mp (fin hf)
    obtain ⟨b,hb⟩ := OnePoint.ne_infty_iff_exists.mp (fin hg)
    rw [← ha,← hb] at hval ⊢
    exact congrArg OnePoint.some hval

end Goodman
