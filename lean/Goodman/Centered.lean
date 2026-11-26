-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
module

public import Goodman.TargetNormalize
public import Goodman.CoefficientComposition
public import Goodman.Constants

@[expose] public section

noncomputable section
open Set Filter Metric
open scoped Topology

namespace Goodman

variable {U : Set Sphere} {w : ℂ} {G : ℂ → Sphere}

/-- A unit phase drops out after taking the norm, for every analytic multiplier.
Only germ equality is used, since affine parts at poles use a filler. -/
theorem CenteredChart.norm_coeff_weighted_factor (c : CenteredChart U w)
    (hG : SphereHolomorphicOn G disk) (hm : MapsTo G disk U) (hw : G 0 = (w : Sphere))
    (E : ℂ → ℂ) (k : ℕ) :
    ‖coeff k (fun z => E z * ((finitePart (G z) - w) / (radius U w : ℂ)))‖ =
      ‖coeff k (fun z => E z * finitePart (c.normalized (c.inverse (G z))))‖ := by
  have hg := c.factorization_germ hG hm isOpen_ball (mem_ball_self zero_lt_one) hw
  let b := c.scale / (radius U w : ℂ)
  have hb : ‖b‖ = 1 := by
    rw [show ‖b‖ = ‖c.scale‖ / ‖(radius U w : ℂ)‖ from norm_div ..,
      c.norm_scale, Complex.norm_of_nonneg c.radius_pos.le, div_self c.radius_pos.ne']
  have he : (fun z => E z * ((finitePart (G z) - w) / (radius U w : ℂ))) =ᶠ[𝓝 0]
      fun z => b * (E z * finitePart (c.normalized (c.inverse (G z)))) := by
    filter_upwards [hg] with z hz
    change finitePart (G z) = _ at hz
    rw [hz]
    dsimp [b]
    ring
  rw [coeff_congr_of_eventuallyEq he, coeff_fun_const_mul, norm_mul, hb, one_mul]

/-- Weighted Rogosinski estimate at the planar endpoint, by transfer and the product bound. -/
theorem planar_weighted_comp (transfer : TransferClaim) (product : ProductClaim)
    {F h E : ℂ → ℂ} (hF : IsS F) (hh : IsSchwarz h) (hE : IsWeight E)
    {k : ℕ} (hk : 1 ≤ k) : ‖coeff k (fun z => E z * F (h z))‖ ≤ (k : ℝ) := by
  obtain ⟨T, hT, _, htransfer⟩ := transfer h hh E hE k
  rw [htransfer F (hF.1 0 (mem_ball_self zero_lt_one))]
  simpa only [mul_comm] using product F hF T hT k hk

/-- The estimate for a map already pulled back to the disk. -/
theorem centered_disk_of_chart (weighted : WeightedBound) (transfer : TransferClaim)
    (product : ProductClaim) (c : CenteredChart U w) (hG : SphereHolomorphicOn G disk)
    (hm : MapsTo G disk U) (hw : G 0 = (w : Sphere)) {E : ℂ → ℂ} (hE : IsWeight E)
    {k : ℕ} (hk : 1 ≤ k) :
    ‖coeff k (fun z => E z * ((finitePart (G z) - w) / (radius U w : ℂ)))‖ ≤ A (poleParam U w) k := by
  by_cases hp : OnePoint.infty ∈ U
  · obtain ⟨r, hr, _, hM⟩ := c.exists_rotated_isM hp
    let d := c.rotate r hr
    have hp01 := c.poleParam_mem_Ioo hp
    rw [d.norm_coeff_weighted_factor hG hm hw]
    exact weighted _ hp01.1 hp01.2 d.normalized hM
      (d.inverse ∘ G) (d.inverse_comp_isSchwarz hG hm hw) E hE k hk
  · rw [c.norm_coeff_weighted_factor hG hm hw, poleParam, ite_eq_right hp, A_at_one]
    exact planar_weighted_comp transfer product (c.normalized_isS hp) (c.inverse_comp_isSchwarz hG hm hw) hE hk

/-- Lemma 8 for arbitrary bounded weights and a spherical target. -/
theorem centeredClaim (weighted : WeightedBound) (transfer : TransferClaim)
    (product : ProductClaim) (rmt : RiemannMapping) : CenteredClaim := by
  intro Ω U x w _ hx hU G hG hm hw φ hφ hφ0 _ E hE k hk
  obtain ⟨c⟩ := rmt U hU w (hw ▸ hm hx)
  obtain ⟨_, _, hφm, _⟩ := hφ.2
  exact centered_disk_of_chart weighted transfer product c (hG.comp_analyticOnNhd hφ.1 hφm)
    (hm.comp hφm) (by simpa only [Function.comp_apply, hφ0] using hw) hE hk

/--
info: 'Goodman.centeredClaim' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms centeredClaim

end Goodman
