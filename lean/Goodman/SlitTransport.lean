-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
module

public import Goodman.MainReduction
public import Goodman.SlitMajorant

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology

namespace Goodman

/-- Differentiating the cleared slit identity in the inverse coordinate gives its scale. -/
private theorem slit_inverse_deriv {χ : ℂ → ℂ} {R : ℂ} (hχ : AnalyticAt ℂ χ 0)
    (hzero : χ 0 = 0) (heq : (fun w => χ w * (1 + w)^2) =ᶠ[𝓝 (0 : ℂ)]
      (fun w => R * w * (1 + χ w)^2)) : HasDerivAt χ R 0 := by
  have hd := hχ.differentiableAt.hasDerivAt
  have hi := hasDerivAt_id (0 : ℂ)
  have hl : HasDerivAt (fun w => χ w * (1 + w)^2) (deriv χ 0) 0 := by
    simpa [hzero] using hd.fun_mul (((hasDerivAt_const (0 : ℂ) (1 : ℂ)).fun_add hi).fun_pow 2)
  have hr : HasDerivAt (fun w => R * w * (1 + χ w)^2) R 0 := by
    simpa [hzero] using (hi.const_mul R).fun_mul (((hasDerivAt_const (0 : ℂ) (1 : ℂ)).fun_add hd).fun_pow 2)
  rwa [← hl.unique (hr.congr_of_eventuallyEq heq)]

private theorem exists_slit_coordinates {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {q : ℂ → ℂ}
    (hq : IsSlitMap p q) {f : ℂ → Sphere} (hf : IsM p f) :
    ∃ χ F : ℂ → ℂ, AnalyticOnNhd ℂ χ disk ∧ MapsTo χ disk (slitDisk p) ∧
      LeftInvOn χ q (slitDisk p) ∧ χ 0 = 0 ∧ IsS F ∧
      ∀ z ∈ slitDisk p, finitePart (f z) = (slitR p : ℂ) * F (q z) := by
  obtain ⟨χ, hχ, _, hmap, hleft, hright⟩ := hq.1.2
  have hslit := slitDisk_mem_nhds_zero hp hp1
  have h0 : (0 : ℂ) ∈ disk := Metric.mem_ball_self zero_lt_one
  have hχ0 : χ 0 = 0 := by simpa [hq.2.1] using hleft (mem_of_mem_nhds hslit)
  have hχ' : HasDerivAt χ (slitR p : ℂ) 0 := by
    apply slit_inverse_deriv (hχ 0 h0) hχ0
    filter_upwards [show disk ∈ 𝓝 (0 : ℂ) from Metric.ball_mem_nhds _ zero_lt_one] with w hw
    simpa only [hright hw] using hq.2.2 (χ w) (hmap hw)
  have hpDisk : (p : ℂ) ∈ disk := by simpa [disk, abs_of_pos hp] using hp1
  have finite_chart {z : ℂ} (hz : z ∈ slitDisk p) :
      AnalyticAt ℂ (finitePart ∘ f) z ∧ f z = (finitePart (f z) : Sphere) := by
    have hfin : f z ≠ OnePoint.infty := by
      intro h
      have hzp : z = (p : ℂ) := hf.2.1 hz.1 hpDisk (h.trans hf.2.2.1.symm)
      exact hz.2 ⟨p, ⟨le_rfl, hp1⟩, hzp.symm⟩
    refine ⟨MainReduction.finite_germ hf.1 hz.1 hfin, ?_⟩
    obtain ⟨a, ha⟩ := OnePoint.ne_infty_iff_exists.mp hfin
    rw [← ha]
    rfl
  have hR : (slitR p : ℂ) ≠ 0 := by exact_mod_cast (slitR_pos hp).ne'
  let F := fun w => finitePart (f (χ w)) / (slitR p : ℂ)
  have hF : IsS F := by
    refine ⟨fun w hw => (((finite_chart (hmap hw)).1.comp (hχ w hw)).div_const), ?_, ?_, ?_⟩
    · intro u hu v hv he
      apply hright.injOn hu hv
      apply hf.2.1 (hmap hu).1 (hmap hv).1
      rw [(finite_chart (hmap hu)).2, (finite_chart (hmap hv)).2]
      exact congrArg (fun t : ℂ => (t : Sphere)) ((div_left_inj' hR).mp he)
    · simp only [F, hχ0, hf.2.2.2.2.1]
      exact zero_div _
    · have hf' : HasDerivAt (finitePart ∘ f) 1 0 := by
        rw [← hf.2.2.2.2.2]
        exact (finite_chart (mem_of_mem_nhds hslit)).1.differentiableAt.hasDerivAt
      simpa [F, hR, Function.comp_def] using
        ((hf'.comp_of_eq 0 hχ' hχ0.symm).div_const (slitR p : ℂ)).deriv
  refine ⟨χ, F, hχ, hmap, hleft, hχ0, hF, ?_⟩
  intro z hz
  simp only [F, hleft hz]
  field_simp

/-- On a neighborhood of the origin, the original map is recovered by composing
a normalized univalent disk map with the slit chart and restoring its scale. -/
theorem exists_slit_normalized {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {q : ℂ → ℂ}
    (hq : IsSlitMap p q) {f : ℂ → Sphere} (hf : IsM p f) :
    ∃ F : ℂ → ℂ, IsS F ∧ (finitePart ∘ f) =ᶠ[𝓝 (0 : ℂ)]
      (fun z => (slitR p : ℂ) * F (q z)) := by
  obtain ⟨_, F, _, _, _, _, hF, he⟩ := exists_slit_coordinates hp hp1 hq hf
  refine ⟨F, hF, ?_⟩
  filter_upwards [slitDisk_mem_nhds_zero hp hp1] with z hz using he z hz

/-- Transport the weighted affine coordinate to the disk by the inverse slit map. -/
theorem exists_slit_product {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {q : ℂ → ℂ}
    (hq : IsSlitMap p q) {f : ℂ → Sphere} (hf : IsM p f) {E : ℂ → ℂ}
    (hE : IsWeight E) (hprod : ProductClaim) :
    ∃ Φ : ℂ → ℂ, AnalyticAt ℂ Φ 0 ∧ Φ 0 = 0 ∧ coeff 1 Φ = E 0 ∧
      (∀ k : ℕ, 1 ≤ k → ‖coeff k Φ‖ ≤ (k : ℝ)) ∧
      (fun z => E z * finitePart (f z)) =ᶠ[𝓝 (0 : ℂ)] (fun z => (slitR p : ℂ) * Φ (q z)) := by
  obtain ⟨χ, F, hχ, hmap, hleft, hχ0, hF, he⟩ := exists_slit_coordinates hp hp1 hq hf
  have h0 : (0 : ℂ) ∈ disk := Metric.mem_ball_self zero_lt_one
  have hW : IsWeight (E ∘ χ) :=
    ⟨fun w hw => (hE.1 _ (hmap hw).1).comp (hχ w hw), fun w hw => hE.2 _ (hmap hw).1⟩
  refine ⟨fun w => F w * (E ∘ χ) w, (hF.1 0 h0).mul (hW.1 0 h0), by simp [hF.2.2.1],
    ?_, hprod F hF (E ∘ χ) hW, ?_⟩
  · simpa [coeff, hF.2.2.2, hF.2.2.1, hχ0] using
      ((hF.1 0 h0).differentiableAt.hasDerivAt.fun_mul (hW.1 0 h0).differentiableAt.hasDerivAt).deriv
  · filter_upwards [slitDisk_mem_nhds_zero hp hp1] with z hz
    simp only [Function.comp_apply, hleft hz, he z hz]
    ring

/-- The inverse slit coordinate identifies the entire transported normalized map, not
only its germ. Its derivative at zero is the positive slit scale. -/
theorem full_slit_coordinates {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {q : ℂ → ℂ}
    (hq : IsSlitMap p q) {f : ℂ → Sphere} (hf : IsM p f) :
    ∃ χ F : ℂ → ℂ, Bihol disk (slitDisk p) χ ∧ MapsTo χ disk (slitDisk p) ∧
      LeftInvOn χ q (slitDisk p) ∧ LeftInvOn q χ disk ∧ χ 0 = 0 ∧
      HasDerivAt χ (slitR p : ℂ) 0 ∧ IsS F ∧
      EqOn F (fun w => finitePart (f (χ w)) / (slitR p : ℂ)) disk ∧
      ∀ z ∈ slitDisk p, finitePart (f z) = (slitR p : ℂ) * F (q z) := by
  obtain ⟨_,F,_,_,_,_,hF,he⟩ := exists_slit_coordinates hp hp1 hq hf
  obtain ⟨χ,hχ,hqmap,hm,hl,hr⟩ := hq.1.2
  have h0 : (0 : ℂ) ∈ disk := Metric.mem_ball_self zero_lt_one
  have hχ0 : χ 0 = 0 := by
    simpa [hq.2.1] using hl (mem_of_mem_nhds (slitDisk_mem_nhds_zero hp hp1))
  have hd : HasDerivAt χ (slitR p : ℂ) 0 := by
    apply slit_inverse_deriv (hχ 0 h0) hχ0
    filter_upwards [show disk ∈ 𝓝 (0:ℂ) from Metric.ball_mem_nhds _ zero_lt_one] with t ht
    simpa [hr ht] using hq.2.2 (χ t) (hm ht)
  refine ⟨χ,F,⟨hχ,q,hq.1.1,hm,hqmap,hr,hl⟩,hm,hl,hr,hχ0,hd,hF,?_,he⟩
  intro t ht
  change F t = finitePart (f (χ t)) / (slitR p : ℂ)
  rw [he _ (hm ht),hr ht]
  have hR : (slitR p : ℂ) ≠ 0 := by exact_mod_cast (slitR_pos hp).ne'
  field_simp

end Goodman
