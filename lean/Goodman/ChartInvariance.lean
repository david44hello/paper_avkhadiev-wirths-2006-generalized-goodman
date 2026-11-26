-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Goodman.Geometry
import Goodman.SchwarzCases

noncomputable section

open Set Filter Metric
open scoped Topology

namespace Goodman

variable {Ω : Set ℂ} {U : Set Sphere} {G : ℂ → Sphere} {w x : ℂ}

private theorem zero_in_disk : (0 : ℂ) ∈ disk := mem_ball_self zero_lt_one

/-- Around a finite value the actual affine part is an analytic coordinate for the germ. -/
theorem SphereHolomorphicOn.affine_germ (hG : SphereHolomorphicOn G Ω)
    (hx : x ∈ Ω) (hp : G x ≠ OnePoint.infty) :
    AnalyticAt ℂ (finitePart ∘ G) x ∧ ∀ᶠ z in 𝓝 x, G z = (finitePart (G z) : Sphere) := by
  obtain ⟨g, hg, heq⟩ : ∃ g : ℂ → ℂ, AnalyticAt ℂ g x ∧
      ∀ᶠ z in 𝓝 x, G z = (g z : Sphere) := by
    obtain ⟨u, hu, h | h⟩ := hG x hx
    · exact ⟨u, hu, h⟩
    · have hne : u x ≠ 0 := by
        intro hzero
        exact hp (by simpa [fromRecip, hzero] using h.self_of_nhds)
      refine ⟨fun t => (u t)⁻¹, hu.inv hne, ?_⟩
      filter_upwards [h, hu.continuousAt.eventually_ne hne] with z hz hn
      simpa [fromRecip, hn] using hz
  refine ⟨hg.congr ?_, ?_⟩
  · filter_upwards [heq] with z hz using (congrArg finitePart hz).symm
  · filter_upwards [heq] with z hz
    rw [hz]
    rfl

/-- At infinity a spherical map has an analytic reciprocal coordinate vanishing there. -/
theorem SphereHolomorphicOn.recip_germ (hG : SphereHolomorphicOn G Ω)
    (hx : x ∈ Ω) (hp : G x = OnePoint.infty) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g x ∧ g x = 0 ∧ ∀ᶠ z in 𝓝 x, G z = fromRecip (g z) := by
  obtain ⟨g, hg, h | h⟩ := hG x hx
  · have heq := h.self_of_nhds
    simp [hp] at heq
  · refine ⟨g, hg, ?_, h⟩
    by_contra hne
    have heq := h.self_of_nhds
    simp [hp, fromRecip, hne] at heq

/-- Composition in spherical coordinates also covers maps taking the value infinity. -/
theorem HolomorphicFromSphereOn.comp_sphereHolomorphicOn {f : Sphere → ℂ}
    (hf : HolomorphicFromSphereOn f U) (hG : SphereHolomorphicOn G Ω) (hm : MapsTo G Ω U) :
    AnalyticOnNhd ℂ (f ∘ G) Ω := by
  intro z hz
  by_cases hp : G z = OnePoint.infty
  · obtain ⟨g, hg, hzero, heq⟩ := hG.recip_germ hz hp
    have hinfty : OnePoint.infty ∈ U := hp ▸ hm hz
    apply ((hf.2 hinfty).comp_of_eq hg hzero).congr
    filter_upwards [heq] with t ht using congrArg f ht.symm
  · obtain ⟨hg, heq⟩ := hG.affine_germ hz hp
    have hmem : (finitePart (G z) : Sphere) ∈ U := heq.self_of_nhds ▸ hm hz
    apply ((hf.1 _ hmem).comp (f := finitePart ∘ G) hg).congr
    filter_upwards [heq] with t ht using congrArg f ht.symm

/-- Differentiate the local inverse identity in one complex coordinate. -/
private theorem deriv_product_of_local_inverse {f g : ℂ → ℂ} {a b : ℂ}
    (hf : AnalyticAt ℂ f a) (hg : AnalyticAt ℂ g b) (hab : f a = b)
    (hinv : g ∘ f =ᶠ[𝓝 a] id) : deriv g b * deriv f a = 1 := by
  subst b
  rw [← deriv_comp a hg.differentiableAt hf.differentiableAt, hinv.deriv_eq, deriv_id]

namespace CenteredChart

variable (c : CenteredChart U w)

theorem inverse_comp_analyticOnNhd (hG : SphereHolomorphicOn G Ω) (hm : MapsTo G Ω U) :
    AnalyticOnNhd ℂ (c.inverse ∘ G) Ω :=
  c.inverse_holo.comp_sphereHolomorphicOn hG hm

theorem inverse_center : c.inverse (w : Sphere) = 0 := by
  rw [← c.center]
  exact c.left_inverse zero_in_disk

theorem finitePart_center : finitePart (c.forward 0) = w := by
  rw [c.center]
  rfl

theorem finite_germ_center :
    AnalyticAt ℂ (finitePart ∘ c.forward) 0 ∧
    ∀ᶠ z in 𝓝 (0 : ℂ), c.forward z = (finitePart (c.forward z) : Sphere) :=
  c.forward_holo.affine_germ zero_in_disk (c.center ▸ OnePoint.coe_ne_infty w)

theorem analyticAt_center : AnalyticAt ℂ (finitePart ∘ c.forward) 0 :=
  c.finite_germ_center.1

theorem inverse_comp_isSchwarz (hG : SphereHolomorphicOn G disk) (hm : MapsTo G disk U)
    (hzero : G 0 = (w : Sphere)) : IsSchwarz (c.inverse ∘ G) :=
  ⟨c.inverse_comp_analyticOnNhd hG hm, c.inverse_maps.comp hm, by
    simpa only [Function.comp_apply, hzero] using c.inverse_center⟩

/-- Pull a map on a planar source back along a disk parametrization through the center. -/
theorem inverse_comp_isSchwarz_of_param {φ : ℂ → ℂ} (hG : SphereHolomorphicOn G Ω)
    (hm : MapsTo G Ω U) (hφ : AnalyticOnNhd ℂ φ disk) (hφm : MapsTo φ disk Ω)
    (hcenter : G (φ 0) = (w : Sphere)) : IsSchwarz (c.inverse ∘ G ∘ φ) :=
  ⟨(c.inverse_comp_analyticOnNhd hG hm).comp hφ hφm, c.inverse_maps.comp (hm.comp hφm), by
    simpa only [Function.comp_apply, hcenter] using c.inverse_center⟩

theorem deriv_inverse_mul_deriv_forward :
    deriv (fun t : ℂ => c.inverse (t : Sphere)) w * deriv (finitePart ∘ c.forward) 0 = 1 := by
  have hw := c.forward_maps zero_in_disk
  rw [c.center] at hw
  apply deriv_product_of_local_inverse c.analyticAt_center (c.inverse_holo.1 w hw) c.finitePart_center
  filter_upwards [c.finite_germ_center.2,
    isOpen_ball.mem_nhds zero_in_disk] with z hz hzd
  change c.inverse (finitePart (c.forward z) : Sphere) = z
  rw [← hz, c.left_inverse hzd]

theorem deriv_forward_ne_zero : deriv (finitePart ∘ c.forward) 0 ≠ 0 := by
  intro h
  simpa [h] using c.deriv_inverse_mul_deriv_forward

theorem deriv_inverse_ne_zero : deriv (fun t : ℂ => c.inverse (t : Sphere)) w ≠ 0 := by
  intro h
  simpa [h] using c.deriv_inverse_mul_deriv_forward

/-- The inverse in the coordinate at infinity makes every pole of a chart simple. -/
theorem simplePoleAt (hx : x ∈ disk) (hp : c.forward x = OnePoint.infty) :
    SimplePoleAt c.forward x := by
  obtain ⟨g, hg, hzero, heq⟩ := c.forward_holo.recip_germ hx hp
  refine ⟨g, hg, hzero, ?_, heq⟩
  have hinfty : OnePoint.infty ∈ U := hp ▸ c.forward_maps hx
  have hprod := deriv_product_of_local_inverse hg (c.inverse_holo.2 hinfty) hzero (by
    filter_upwards [heq, isOpen_ball.mem_nhds hx] with z hz hzd
    change c.inverse (fromRecip (g z)) = z
    rw [← hz, c.left_inverse hzd])
  intro h
  simp [h] at hprod

variable (d : CenteredChart U w)

/-- Both orders of the transition between centered charts are Schwarz functions. -/
theorem transition_isSchwarz : IsSchwarz (c.inverse ∘ d.forward) :=
  c.inverse_comp_isSchwarz d.forward_holo d.forward_maps d.center

theorem norm_deriv_transition : ‖deriv (c.inverse ∘ d.forward) 0‖ = 1 := by
  have hf := c.transition_isSchwarz d
  have hg := d.transition_isSchwarz c
  have hprod := deriv_product_of_local_inverse (hf.1 0 zero_in_disk)
    (hg.1 0 zero_in_disk) hf.2.2 (by
      filter_upwards [isOpen_ball.mem_nhds zero_in_disk] with z hz
      change d.inverse (c.forward (c.inverse (d.forward z))) = z
      rw [c.right_inverse (d.forward_maps hz), d.left_inverse hz])
  have hnorm := congrArg norm hprod
  rw [norm_mul, norm_one] at hnorm
  apply le_antisymm hf.norm_deriv_le_one
  calc
    1 = ‖deriv (d.inverse ∘ c.forward) 0‖ * ‖deriv (c.inverse ∘ d.forward) 0‖ := hnorm.symm
    _ ≤ 1 * ‖deriv (c.inverse ∘ d.forward) 0‖ :=
      mul_le_mul_of_nonneg_right hg.norm_deriv_le_one (norm_nonneg _)
    _ = _ := one_mul _

theorem transition_isRotation : IsRotation (c.inverse ∘ d.forward) :=
  (c.transition_isSchwarz d).norm_deriv_eq_one_iff_isRotation.mp (c.norm_deriv_transition d)

/-- A transition rotation preserves the modulus of the coordinate of each target point. -/
theorem norm_inverse_eq {v : Sphere} (hv : v ∈ U) : ‖c.inverse v‖ = ‖d.inverse v‖ := by
  obtain ⟨a, ha, hrot⟩ := c.transition_isRotation d
  have h := hrot (d.inverse_maps hv)
  change c.inverse (d.forward (d.inverse v)) = a * d.inverse v at h
  rw [d.right_inverse hv] at h
  rw [h, norm_mul, ha, one_mul]

theorem norm_deriv_forward_eq :
    ‖deriv (finitePart ∘ c.forward) 0‖ = ‖deriv (finitePart ∘ d.forward) 0‖ := by
  let t := c.inverse ∘ d.forward
  have ht := c.transition_isSchwarz d
  have hgerm : (finitePart ∘ c.forward) ∘ t =ᶠ[𝓝 (0 : ℂ)] finitePart ∘ d.forward := by
    filter_upwards [isOpen_ball.mem_nhds zero_in_disk] with z hz
    exact congrArg finitePart (c.right_inverse (d.forward_maps hz))
  have hder := (c.analyticAt_center.differentiableAt.hasDerivAt.comp_of_eq 0
    (ht.1 0 zero_in_disk).differentiableAt.hasDerivAt ht.2.2.symm).deriv
  change deriv ((finitePart ∘ c.forward) ∘ t) 0 =
    deriv (finitePart ∘ c.forward) 0 * deriv t 0 at hder
  rw [hgerm.deriv_eq] at hder
  rw [hder, norm_mul, show ‖deriv t 0‖ = 1 from c.norm_deriv_transition d, mul_one]

theorem radius_eq : radius U w = ‖deriv (finitePart ∘ c.forward) 0‖ := by
  classical
  have h : Nonempty (CenteredChart U w) := ⟨c⟩
  rw [radius, dite_eq_left h]
  exact h.some.norm_deriv_forward_eq c

include c in
theorem radius_pos : 0 < radius U w := by
  rw [c.radius_eq, norm_pos_iff]
  exact c.deriv_forward_ne_zero

theorem hypDistanceFrom_eq {v : Sphere} (hv : v ∈ U) :
    hypDistanceFrom U w v = Real.artanh ‖c.inverse v‖ := by
  classical
  have h : Nonempty (CenteredChart U w) := ⟨c⟩
  rw [hypDistanceFrom, dite_eq_left h, h.some.norm_inverse_eq c hv]

theorem poleParam_eq (hp : OnePoint.infty ∈ U) : poleParam U w = ‖c.inverse OnePoint.infty‖ := by
  rw [poleParam, ite_eq_left hp, c.hypDistanceFrom_eq hp]
  apply Real.tanh_artanh
  exact ⟨lt_of_lt_of_le (by norm_num) (norm_nonneg _), mem_ball_zero_iff.mp (c.inverse_maps hp)⟩

include c in
theorem poleParam_mem_Ioo (hp : OnePoint.infty ∈ U) : poleParam U w ∈ Ioo 0 1 := by
  rw [c.poleParam_eq hp]
  refine ⟨norm_pos_iff.mpr ?_, mem_ball_zero_iff.mp (c.inverse_maps hp)⟩
  intro h
  have heq := c.right_inverse hp
  rw [h, c.center] at heq
  exact OnePoint.coe_ne_infty w heq

end CenteredChart
end Goodman
