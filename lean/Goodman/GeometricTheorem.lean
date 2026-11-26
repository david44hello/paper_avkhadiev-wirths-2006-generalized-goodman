-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Goodman.GeometricEquality
import Goodman.UniformizationProof
import Goodman.SegmentGeometry
import Goodman.CoefficientComposition
import Goodman.Constants

noncomputable section
open Set Filter Metric
open scoped Topology

namespace Goodman

variable {U : Set Sphere} {G : ℂ → Sphere} {w : ℂ}

private theorem geometric_le_of_chart (weighted : WeightedBound) (c : CenteredChart U w)
    (hi : OnePoint.infty ∈ U) (hG : SphereHolomorphicOn G disk) (hm : MapsTo G disk U)
    (hw : G 0 = (w : Sphere)) {n : ℕ} (hn : 1 ≤ n) :
    ‖coeff n (finitePart ∘ G)‖ ≤ radius U w * A (poleParam U w) n := by
  obtain ⟨r, hr, _, hM⟩ := c.exists_rotated_isM hi
  let d := c.rotate r hr
  have hp := c.poleParam_mem_Ioo hi
  have hone : IsWeight (fun _ => 1) := ⟨analyticOnNhd_const, by simp⟩
  have h := weighted _ hp.1 hp.2 d.normalized hM (d.inverse ∘ G)
    (d.inverse_comp_isSchwarz hG hm hw) _ hone n hn
  rw [d.coeff_factorization hG hm hw hn, norm_mul, d.norm_scale]
  apply mul_le_mul_of_nonneg_left _ c.radius_pos.le
  simpa only [one_mul, Function.comp_apply] using h

/-- The geometric coefficient inequality only needs the weighted estimate and planar mapping. -/
theorem geometric_inequality (weighted : WeightedBound) (hR : PlanarRiemannMapping)
    (hU : IsTarget U) (hi : OnePoint.infty ∈ U) (hG : SphereHolomorphicOn G disk)
    (hm : MapsTo G disk U) (hw : G 0 = (w : Sphere)) :
    (0 < poleParam U w ∧ poleParam U w < 1) ∧ ∀ n : ℕ, 1 ≤ n →
      ‖coeff n (finitePart ∘ G)‖ ≤ radius U w * A (poleParam U w) n := by
  obtain ⟨c⟩ := riemannMapping_of_planarRiemannMapping hR U hU w
    (hw ▸ hm (mem_ball_self zero_lt_one))
  exact ⟨c.poleParam_mem_Ioo hi, fun _ hn => geometric_le_of_chart weighted c hi hG hm hw hn⟩

/-- Equality at a higher degree forces the normalized chart to be the extremal and
the inverse factor to be a disk rotation. Restoring the scale gives the actual target. -/
private theorem geometric_equality_forward (higher : EqualityHigher) (c : CenteredChart U w)
    (hi : OnePoint.infty ∈ U) (hG : SphereHolomorphicOn G disk) (hm : MapsTo G disk U)
    (hw : G 0 = (w : Sphere)) {n : ℕ} (hn : 2 ≤ n)
    (he : ‖coeff n (finitePart ∘ G)‖ = radius U w * A (poleParam U w) n) :
    BijOn G disk U ∧ IsSegmentOnLineThrough Uᶜ w := by
  obtain ⟨r, hr, _, hM⟩ := c.exists_rotated_isM hi
  let d := c.rotate r hr
  have hp := c.poleParam_mem_Ioo hi
  rw [d.coeff_factorization hG hm hw (by omega : 1 ≤ n), norm_mul, d.norm_scale] at he
  obtain ⟨hf, hrot⟩ := (higher _ hp.1 hp.2 d.normalized hM (d.inverse ∘ G)
    (d.inverse_comp_isSchwarz hG hm hw) n hn).mp (mul_left_cancel₀ d.radius_pos.ne' he)
  have heq : EqOn (restoreValue w d.scale ∘ extremal (poleParam U w)) d.forward disk :=
    fun z hz => (congrArg (restoreValue w d.scale) (hf hz).symm).trans (d.restore_normalized z)
  have himage := heq.image_eq.trans d.forward_bijOn.image_eq
  refine ⟨(d.inverse_comp_bijOn_iff hm).mp hrot.bijOn_disk, ?_⟩
  rw [← himage]
  exact affine_extremal_segmentOnLineThrough w d.scale_ne_zero hp.1 hp.2

/-- A centered spherical bijection agrees on the disk with a rotation of any centered
chart. The inverse factor is an analytic bijection even at poles of the original map. -/
theorem CenteredChart.exists_rotate_eqOn_of_bijOn (c : CenteredChart U w)
    (hG : SphereHolomorphicOn G disk) (hb : BijOn G disk U) (hw : G 0 = (w : Sphere)) :
    ∃ (r : ℂ) (hr : ‖r‖ = 1), EqOn (c.rotate r hr).forward G disk := by
  obtain ⟨r, hr, he⟩ := (c.inverse_comp_isSchwarz hG hb.mapsTo hw).isRotation_of_bijOn
    ((c.inverse_comp_bijOn_iff hb.mapsTo).mpr hb)
  refine ⟨r, hr, fun z hz => ?_⟩
  exact (congrArg c.forward (he hz).symm).trans (c.right_inverse (hb.mapsTo hz))

/-- A bijective map onto a slit target realizes the bound in every positive degree.
The segment parametrization supplies the chart, the conformal radius and the pole. -/
theorem geometric_equality_of_segment (hG : SphereHolomorphicOn G disk) (hb : BijOn G disk U)
    (hw : G 0 = (w : Sphere)) (hseg : IsSegmentOnLineThrough Uᶜ w) {n : ℕ} (hn : 1 ≤ n) :
    ‖coeff n (finitePart ∘ G)‖ = radius U w * A (poleParam U w) n := by
  have hwU : (w : Sphere) ∈ U := hw ▸ hb.mapsTo (mem_ball_self zero_lt_one)
  obtain ⟨_, _, p, a, _, _, _, _, hp, hp1, _, ha, _, _, _, hmodel⟩ :=
    segment_converse hseg (show (w : Sphere) ∉ Uᶜ from fun h => h hwU)
  rw [compl_compl] at hmodel
  rw [← hmodel.image_eq] at hb ⊢
  let d := affineExtremalChart w ha hp hp1
  have hparams := affine_extremal_invariants w ha hp hp1
  obtain ⟨r, hr, hchart⟩ := d.exists_rotate_eqOn_of_bijOn hG hb hw
  have hrot : IsRotation (fun z => r * z) := ⟨r, hr, eqOn_refl _ _⟩
  have hg := (hchart.symm.comp_left (g := finitePart)).eventuallyEq_of_mem
    (ball_mem_nhds (0 : ℂ) zero_lt_one)
  have he : finitePart ∘ d.forward =ᶠ[𝓝 0] fun z => w + a * (finitePart ∘ extremal p) z := by
    filter_upwards [(isM_extremal hp hp1).finite_germ_zero.2] with z hz
    exact congrArg (finitePart ∘ restoreValue w a) hz
  have hcoeff : coeff n (finitePart ∘ d.forward) = a * coeff n (finitePart ∘ extremal p) := by
    simp only [coeff, he.iteratedDeriv_eq n, iteratedDeriv_const_add hn,
      iteratedDeriv_const_mul_field, mul_div_assoc]
  calc
    ‖coeff n (finitePart ∘ G)‖ = ‖coeff n (fun z => finitePart (d.forward (r * z)))‖ :=
      congrArg norm (coeff_congr_of_eventuallyEq hg n)
    _ = ‖coeff n (finitePart ∘ d.forward)‖ := hrot.norm_coeff_comp (finitePart ∘ d.forward) n
    _ = _ := by
      rw [hcoeff, norm_mul, coeff_extremal_of_ne_zero hp.ne',
        Complex.norm_of_nonneg (A_positive hp hn).le, hparams.1, hparams.2]

/-- Theorem 2, reduced to planar Riemann mapping and the two main coefficient statements. -/
theorem geometricBound (weighted : WeightedBound) (higher : EqualityHigher)
    (hR : PlanarRiemannMapping) : GeometricBound := by
  intro U hU hi G w hG hm hw
  obtain ⟨c⟩ := riemannMapping_of_planarRiemannMapping hR U hU w
    (hw ▸ hm (mem_ball_self zero_lt_one))
  refine ⟨c.poleParam_mem_Ioo hi, fun _ hn => geometric_le_of_chart weighted c hi hG hm hw hn,
    fun n hn => ⟨geometric_equality_forward higher c hi hG hm hw hn, ?_⟩⟩
  rintro ⟨hb, hseg⟩
  exact geometric_equality_of_segment hG hb hw hseg (by omega)

/--
info: 'Goodman.geometric_inequality' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms geometric_inequality

/--
info: 'Goodman.geometricBound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms geometricBound

end Goodman
