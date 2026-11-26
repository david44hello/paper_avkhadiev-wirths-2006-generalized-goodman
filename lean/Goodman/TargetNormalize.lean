-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
module

public import Goodman.ChartInvariance

@[expose] public section

noncomputable section
open Set Filter Metric
open scoped Topology

namespace Goodman

variable {Ω : Set ℂ} {U : Set Sphere} {w x : ℂ} {G : ℂ → Sphere}

/-- Pull back either local sphere coordinate along an analytic source map. -/
theorem SphereHolomorphicOn.comp_analyticOnNhd {V : Set ℂ} {φ : ℂ → ℂ}
    (hG : SphereHolomorphicOn G Ω) (hφ : AnalyticOnNhd ℂ φ V) (hm : MapsTo φ V Ω) :
    SphereHolomorphicOn (G ∘ φ) V := by
  intro z hz
  obtain ⟨g, hg, he | he⟩ := hG _ (hm hz)
  · exact ⟨g ∘ φ, hg.comp (hφ z hz), Or.inl ((hφ z hz).continuousAt.tendsto.eventually he)⟩
  · exact ⟨g ∘ φ, hg.comp (hφ z hz), Or.inr ((hφ z hz).continuousAt.tendsto.eventually he)⟩

namespace CenteredChart

theorem unit_maps_disk {r : ℂ} (hr : ‖r‖ = 1) :
    MapsTo (fun z => r * z) disk disk := by
  intro z hz
  simpa [disk, mem_ball_zero_iff, norm_mul, hr] using (mem_ball_zero_iff.mp hz : ‖z‖ < 1)

/-- Precompose the forward chart by a rotation and undo it on the inverse chart. -/
def rotate (c : CenteredChart U w) (r : ℂ) (hr : ‖r‖ = 1) : CenteredChart U w := by
  have hr0 : r ≠ 0 := norm_ne_zero_iff.mp (hr ▸ one_ne_zero)
  have hi : ‖r⁻¹‖ = 1 := by simp [hr]
  exact {
    forward := fun z => c.forward (r * z)
    inverse := fun y => r⁻¹ * c.inverse y
    forward_holo := c.forward_holo.comp_analyticOnNhd
      (fun _ _ => analyticAt_const.mul analyticAt_id) (unit_maps_disk hr)
    inverse_holo := ⟨fun z hz => analyticAt_const.mul (c.inverse_holo.1 z hz),
      fun hp => analyticAt_const.mul (c.inverse_holo.2 hp)⟩
    forward_maps := c.forward_maps.comp (unit_maps_disk hr)
    inverse_maps := (unit_maps_disk hi).comp c.inverse_maps
    left_inverse := fun z hz => by
      change r⁻¹ * c.inverse (c.forward (r * z)) = z
      rw [c.left_inverse (unit_maps_disk hr hz), inv_mul_cancel_left₀ hr0]
    right_inverse := fun y hy => by
      change c.forward (r * (r⁻¹ * c.inverse y)) = y
      rw [mul_inv_cancel_left₀ hr0, c.right_inverse hy]
    center := by simpa using c.center }

/-- The phase is the direction of the inverse image of infinity. -/
theorem exists_pole_rotation (c : CenteredChart U w) (hp : OnePoint.infty ∈ U) :
    ∃ (r : ℂ) (hr : ‖r‖ = 1), c.inverse OnePoint.infty = r * (poleParam U w : ℂ) ∧
      (c.rotate r hr).forward (poleParam U w : ℂ) = OnePoint.infty := by
  let p := poleParam U w
  have hpos : 0 < p := (c.poleParam_mem_Ioo hp).1
  have hn : (p : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  let r := c.inverse OnePoint.infty / (p : ℂ)
  have hr : ‖r‖ = 1 := by
    rw [show ‖r‖ = ‖c.inverse OnePoint.infty‖ / ‖(p : ℂ)‖ from norm_div ..,
      Complex.norm_of_nonneg hpos.le, ← c.poleParam_eq hp, div_self hpos.ne']
  have he : r * (p : ℂ) = c.inverse OnePoint.infty := div_mul_cancel₀ _ hn
  exact ⟨r, hr, he.symm, by change c.forward (r * (p : ℂ)) = _; rw [he, c.right_inverse hp]⟩

end CenteredChart

/-- The affine coordinate change fixes infinity. -/
def normalizeValue (w a : ℂ) : Sphere → Sphere := OnePoint.map (fun v => (v - w) / a)

/-- Inverse affine change on the sphere, including at infinity. -/
def restoreValue (w a : ℂ) : Sphere → Sphere := OnePoint.map (fun v => w + a * v)

theorem restore_normalizeValue (w : ℂ) {a : ℂ} (ha : a ≠ 0) (v : Sphere) :
    restoreValue w a (normalizeValue w a v) = v := by
  induction v using OnePoint.rec with
  | infty => rfl
  | coe z =>
    apply congrArg (fun t : ℂ => (t : Sphere))
    change w + a * ((z - w) / a) = z
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ ha]
    abel

private def normalizedRecip (w a : ℂ) (u : ℂ → ℂ) (t : ℂ) := a * u t / (1 - w * u t)

private theorem normalize_recip_germ {a : ℂ} (ha : a ≠ 0) {u : ℂ → ℂ}
    (hu : AnalyticAt ℂ u x) (h0 : u x = 0) :
    AnalyticAt ℂ (normalizedRecip w a u) x ∧
    ∀ᶠ t in 𝓝 x, normalizeValue w a (fromRecip (u t)) = fromRecip (normalizedRecip w a u t) := by
  have hD : AnalyticAt ℂ (fun t => 1 - w * u t) x := analyticAt_const.sub (analyticAt_const.mul hu)
  have hn : 1 - w * u x ≠ 0 := by simp [h0]
  refine ⟨(analyticAt_const.mul hu).div hD hn, ?_⟩
  filter_upwards [hD.continuousAt.eventually_ne hn] with t ht
  by_cases h : u t = 0
  · simp [normalizeValue, fromRecip, normalizedRecip, h]
  · simp only [fromRecip, ite_eq_right h, normalizedRecip, ite_eq_right (div_ne_zero (mul_ne_zero ha h) ht),
      normalizeValue, OnePoint.map_some, OnePoint.coe_eq_coe, inv_div]
    field_simp

theorem SphereHolomorphicOn.normalizeValue {a : ℂ} (hG : SphereHolomorphicOn G Ω) (ha : a ≠ 0) :
    SphereHolomorphicOn (Goodman.normalizeValue w a ∘ G) Ω := by
  intro x hx
  by_cases hp : G x = OnePoint.infty
  · obtain ⟨u, hu, h0, he⟩ := hG.recip_germ hx hp
    obtain ⟨hf, hrec⟩ := normalize_recip_germ (w := w) ha hu h0
    refine ⟨_, hf, Or.inr ?_⟩
    filter_upwards [he, hrec] with t ht hrec using (congrArg _ ht).trans hrec
  · obtain ⟨hg, he⟩ := hG.affine_germ hx hp
    refine ⟨fun t => (finitePart (G t) - w) / a, (hg.sub analyticAt_const).div_const, Or.inl ?_⟩
    filter_upwards [he] with t ht using congrArg (Goodman.normalizeValue w a) ht

theorem SimplePoleAt.normalizeValue {a : ℂ} (hG : SimplePoleAt G x) (ha : a ≠ 0) :
    SimplePoleAt (Goodman.normalizeValue w a ∘ G) x := by
  obtain ⟨u, hu, h0, hdu, he⟩ := hG
  obtain ⟨hf, hrec⟩ := normalize_recip_germ (w := w) ha hu h0
  refine ⟨_, hf, by simp [normalizedRecip, h0], ?_, ?_⟩
  · have hd := hu.differentiableAt.hasDerivAt
    have h := (hd.const_mul a).div ((hasDerivAt_const x (1 : ℂ)).sub (hd.const_mul w))
      (by simp [h0])
    rw [show deriv (normalizedRecip w a u) x = _ from h.deriv]
    simpa [h0] using mul_ne_zero ha hdu
  · filter_upwards [he, hrec] with t ht hrec using (congrArg _ ht).trans hrec

namespace CenteredChart

variable (c : CenteredChart U w)

/-- The complex scale retains the chart's phase. Its modulus is the conformal radius. -/
def scale := deriv (finitePart ∘ c.forward) 0

def normalized : ℂ → Sphere := normalizeValue w c.scale ∘ c.forward

theorem scale_ne_zero : c.scale ≠ 0 := c.deriv_forward_ne_zero

theorem norm_scale : ‖c.scale‖ = radius U w := c.radius_eq.symm

theorem restore_normalized (z : ℂ) : restoreValue w c.scale (c.normalized z) = c.forward z :=
  restore_normalizeValue w c.scale_ne_zero _

theorem forward_bijOn : BijOn c.forward disk U :=
  (show InvOn c.inverse c.forward disk U from ⟨c.left_inverse, c.right_inverse⟩).bijOn
    c.forward_maps c.inverse_maps

theorem normalized_image : c.normalized '' disk = normalizeValue w c.scale '' U := by
  rw [normalized, image_comp, c.forward_bijOn.image_eq]

/-- The inner map in the factorization is bijective exactly when the original map is. -/
theorem inverse_comp_bijOn_iff (hm : MapsTo G Ω U) :
    BijOn (c.inverse ∘ G) Ω disk ↔ BijOn G Ω U := by
  have hinv := (show InvOn c.forward c.inverse U disk from ⟨c.right_inverse, c.left_inverse⟩).bijOn
    c.inverse_maps c.forward_maps
  exact ⟨fun h => (c.forward_bijOn.comp h).congr (fun z hz => c.right_inverse (hm hz)),
    fun h => hinv.comp h⟩

theorem normalized_germ :
    (finitePart ∘ c.normalized) =ᶠ[𝓝 0] fun z => (finitePart (c.forward z) - w) / c.scale := by
  filter_upwards [c.finite_germ_center.2] with z hz
  exact congrArg (finitePart ∘ normalizeValue w c.scale) hz

theorem deriv_normalized : deriv (finitePart ∘ c.normalized) 0 = 1 := by
  rw [c.normalized_germ.deriv_eq]
  rw [deriv_div_const, deriv_sub_const]
  exact div_self c.scale_ne_zero

theorem normalized_injOn : InjOn c.normalized disk := by
  intro z hz t ht he
  apply c.left_inverse.injOn hz ht
  rw [← c.restore_normalized z, ← c.restore_normalized t, he]

theorem normalized_zero : c.normalized 0 = (0 : ℂ) := by
  simp [normalized, c.center, normalizeValue]

theorem normalized_isM {p : ℝ} (hp : (p : ℂ) ∈ disk) (he : c.forward p = OnePoint.infty) :
    IsM p c.normalized :=
  ⟨c.forward_holo.normalizeValue c.scale_ne_zero, c.normalized_injOn,
    by simp [normalized, he, normalizeValue], (c.simplePoleAt hp he).normalizeValue c.scale_ne_zero,
    c.normalized_zero, c.deriv_normalized⟩

/-- A single rotation puts the pole at the real parameter and gives the normalized
meromorphic map used by both the centered estimate and the geometric equality case. -/
theorem exists_rotated_isM (hp : OnePoint.infty ∈ U) :
    ∃ (r : ℂ) (hr : ‖r‖ = 1), c.inverse OnePoint.infty = r * (poleParam U w : ℂ) ∧
      IsM (poleParam U w) (c.rotate r hr).normalized := by
  obtain ⟨r, hr, he, hPole⟩ := c.exists_pole_rotation hp
  have hp01 := c.poleParam_mem_Ioo hp
  have hpd : (poleParam U w : ℂ) ∈ disk :=
    mem_ball_zero_iff.mpr ((Complex.norm_of_nonneg hp01.1.le).trans_lt hp01.2)
  exact ⟨r, hr, he, (c.rotate r hr).normalized_isM hpd hPole⟩

theorem normalized_isS (hp : OnePoint.infty ∉ U) : IsS (finitePart ∘ c.normalized) := by
  have hfin {z : ℂ} (hz : z ∈ disk) : c.normalized z ≠ OnePoint.infty := by
    intro h
    have h' := c.restore_normalized z
    rw [h] at h'
    change OnePoint.infty = c.forward z at h'
    exact hp (h' ▸ c.forward_maps hz)
  have hg : SphereHolomorphicOn c.normalized disk := c.forward_holo.normalizeValue c.scale_ne_zero
  refine ⟨fun _ hz => (hg.affine_germ hz (hfin hz)).1, ?_, ?_, c.deriv_normalized⟩
  · intro z hz t ht he
    apply c.normalized_injOn hz ht
    exact ((hg.affine_germ hz (hfin hz)).2.self_of_nhds).trans
      ((congrArg (fun v : ℂ => (v : Sphere)) he).trans (hg.affine_germ ht (hfin ht)).2.self_of_nhds.symm)
  · rw [Function.comp_apply, c.normalized_zero]
    rfl

/-- The spherical factorization holds at every source point, including poles. -/
theorem factorization (hm : MapsTo G Ω U) :
    EqOn G (restoreValue w c.scale ∘ c.normalized ∘ c.inverse ∘ G) Ω := by
  intro z hz
  exact ((c.restore_normalized _).trans (c.right_inverse (hm hz))).symm

/-- On the finite locus the spherical factorization is an ordinary complex identity. -/
theorem factorization_at_finite (hm : MapsTo G Ω U) (hx : x ∈ Ω) (hfin : G x ≠ OnePoint.infty) :
    finitePart (G x) = w + c.scale * finitePart (c.normalized (c.inverse (G x))) := by
  obtain ⟨v, hv⟩ := OnePoint.ne_infty_iff_exists.mp hfin
  change finitePart (G x) = w + c.scale * finitePart (normalizeValue w c.scale (c.forward (c.inverse (G x))))
  rw [c.right_inverse (hm hx), ← hv]
  exact (congrArg finitePart (restore_normalizeValue w c.scale_ne_zero (v : Sphere))).symm

/-- The actual affine germ of an arbitrary map through the chart center. -/
theorem factorization_germ (hG : SphereHolomorphicOn G Ω) (hm : MapsTo G Ω U)
    (hΩ : IsOpen Ω) (hx : x ∈ Ω) (hw : G x = (w : Sphere)) :
    (finitePart ∘ G) =ᶠ[𝓝 x] fun z => w + c.scale * finitePart (c.normalized (c.inverse (G z))) := by
  have hf := (hG.affine_germ hx (hw ▸ OnePoint.coe_ne_infty w)).2
  filter_upwards [hf, hΩ.mem_nhds hx] with z hz hmem
  exact c.factorization_at_finite hm hmem (fun h => OnePoint.coe_ne_infty _ (hz.symm.trans h))

/-- Positive-degree coefficients retain the complex scale in the geometric theorem. -/
theorem coeff_factorization (hG : SphereHolomorphicOn G disk) (hm : MapsTo G disk U)
    (hw : G 0 = (w : Sphere)) {n : ℕ} (hn : 1 ≤ n) :
    coeff n (finitePart ∘ G) = c.scale * coeff n (fun z => finitePart (c.normalized (c.inverse (G z)))) := by
  have hg := c.factorization_germ hG hm isOpen_ball (mem_ball_self zero_lt_one) hw
  simp only [coeff, hg.iteratedDeriv_eq n, iteratedDeriv_const_add hn, iteratedDeriv_const_mul_field,
    mul_div_assoc]

end CenteredChart
end Goodman
