-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Goodman.DiskDerivative
import Goodman.SegmentGeometry
import Goodman.Constants

noncomputable section
open Set Filter Metric Topology
open scoped Topology

namespace Goodman

/-- Rotation of the inverse disk chart which aligns all orders simultaneously. -/
def diskPhase (a : ℂ) : ℂ := if a = 0 then 1 else star a / (‖a‖ : ℂ)

@[simp] theorem norm_diskPhase (a : ℂ) : ‖diskPhase a‖ = 1 := by
  by_cases ha : a = 0
  · simp [diskPhase, ha]
  · simp [diskPhase, ha]

theorem star_eq_diskPhase_mul_norm (a : ℂ) : star a = diskPhase a * (‖a‖ : ℂ) := by
  by_cases ha : a = 0
  · simp [ha]
  · have h : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr ha
    simp [diskPhase, ha, h]

theorem diskPhase_real {a : ℂ} (him : a.im = 0) (hre : 0 ≤ a.re) : diskPhase a = 1 := by
  have ha : a = (a.re : ℂ) := by apply Complex.ext <;> simp [him]
  by_cases hz : a.re = 0
  · have h : a = 0 := ha.trans (by simp [hz])
    simp [h, diskPhase]
  · conv_lhs => rw [ha]
    simp [diskPhase, hz, abs_of_nonneg hre]

private theorem scaledExtremal_analyticAt (p : ℝ) (u : ℂ) :
    AnalyticAt ℂ (fun z => finitePart (extremal p (u*z))) 0 := by
  simp only [finitePart_extremal]
  apply AnalyticAt.fun_div
  · fun_prop
  · simp only [div_eq_mul_inv]
    fun_prop
  · simp

/-- The complex coefficient itself has phase `diskPhase a ^ n`, including for `p = 1`. -/
theorem coeff_disk_model {p : ℝ} (hp : 0 < p) (a : ℂ) (m : ℕ) :
    coeff (m+1) (fun z => finitePart (extremal p (diskPhase a * diskKernel (star a) z))) =
      diskPhase a ^ (m+1) * (D p ‖a‖ (m+1) : ℂ) := by
  change coeff (m+1) ((fun z => finitePart (extremal p (diskPhase a*z))) ∘ diskKernel (star a)) = _
  rw [coeff_comp_diskKernel (scaledExtremal_analyticAt p (diskPhase a))]
  simp only [coeff_extremal_scaled hp.ne', D, Nat.add_sub_cancel, Complex.ofReal_sum,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_natCast, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hpow : diskPhase a ^ (m-j) * diskPhase a ^ (j+1) = diskPhase a ^ (m+1) := by
    rw [← pow_add, show m-j+(j+1) = m+1 by have := Finset.mem_range.mp hj; omega]
  rw [star_eq_diskPhase_mul_norm a, mul_pow, ← hpow]
  ring

theorem disk_model_derivativeRatio {p : ℝ} (hp : 0 < p) {a : ℂ} (ha : a ∈ disk)
    {n : ℕ} (hn : 1 ≤ n) :
    derivativeRatio n (fun z => extremal p (diskPhase a * diskInverse a z)) a
      (radius (planeDomain disk) a) 1 = D p ‖a‖ n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [radius_planeDomain_disk ha, derivativeRatio_eq_affine_coeff _ _ 0 (diskRadius_pos ha).le
    zero_le_one _ (by omega)]
  simp only [sub_zero, Complex.ofReal_one, div_one, diskInverse_affine ha, coeff_disk_model hp,
    norm_mul, norm_pow, norm_diskPhase, one_pow, one_mul]
  apply Complex.norm_of_nonneg
  unfold D
  exact Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (norm_nonneg _) _))
      (A_positive hp (by omega)).le

private theorem regular_bihol_image {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f disk)
    (hi : InjOn f disk) (hd : ∀ z ∈ disk, deriv f z ≠ 0) :
    Bihol disk (f '' disk) f ∧ IsOpen (f '' disk) ∧ IsSimplyConnected (f '' disk) := by
  classical
  let χ := Function.invFunOn f disk
  have hl : LeftInvOn χ f disk := hi.leftInvOn_invFunOn
  have hχ : AnalyticOnNhd ℂ χ (f '' disk) := by
    rintro _ ⟨z, hz, rfl⟩
    apply (analyticAt_comp_iff_of_deriv_ne_zero (hf z hz) (hd z hz)).mp
    apply (analyticAt_id (𝕜 := ℂ)).congr
    filter_upwards [isOpen_ball.mem_nhds hz] with t ht
    exact (hl ht).symm
  let g (z : disk) := f z
  have hg : IsOpenEmbedding g := by
    apply IsOpenEmbedding.of_continuous_injective_isOpenMap
    · exact hf.continuousOn.domRestrict
    · exact hi.injective
    · apply isOpenMap_iff_nhds_le.mpr
      intro z
      change 𝓝 (f z) ≤ map (f ∘ ((↑) : disk → ℂ)) (𝓝 z)
      rw [← Filter.map_map, map_nhds_subtype_val, (show IsOpen disk from isOpen_ball).nhdsWithin_eq z.property,
        (hf z z.property).hasStrictDerivAt.map_nhds_eq (hd z z.property)]
  have hr : range g = f '' disk := Set.range_domRestrict ..
  have hs : SimplyConnectedSpace disk := disk_isSource.2.1
  refine ⟨⟨hf, χ, hχ, mapsTo_image _ _, fun _ h => Function.invFunOn_mem h,
    hl, fun _ h => Function.invFunOn_eq h⟩, hr ▸ hg.isOpen_range, ?_⟩
  rw [← hr, ← image_univ]
  exact hg.isEmbedding.isSimplyConnected_image.mpr
    ((Homeomorph.Set.univ disk).toHomotopyEquiv.simplyConnectedSpace_iff.mpr hs)

/-- In the coordinate omitting the boundary value at -1, the extremal is an affine
transform of the reflected Koebe function. This single coordinate covers the interior pole. -/
private def modelCoord (c z : ℂ) := c - c ^ 2 * (z / (1 + z)^2)

private theorem one_add_ne_on_disk {z : ℂ} (hz : z ∈ disk) : 1 + z ≠ 0 := by
  intro he
  have h : z = -1 := by linear_combination he
  simp [disk, h] at hz

private theorem modelCoord_regular {c : ℂ} (hc : c ≠ 0) {z : ℂ} (hz : z ∈ disk) :
    AnalyticAt ℂ (modelCoord c) z ∧ deriv (modelCoord c) z ≠ 0 := by
  have hn := one_add_ne_on_disk hz
  have hm : 1-z ≠ 0 := by
    intro he
    have h : z = 1 := (sub_eq_zero.mp he).symm
    simp [disk, h] at hz
  have hd := (hasDerivAt_const z c).sub
    (((hasDerivAt_id z).div (((hasDerivAt_const z (1 : ℂ)).add (hasDerivAt_id z)).pow 2)
      (pow_ne_zero _ hn)).const_mul (c^2))
  refine ⟨?_, ?_⟩
  · exact analyticAt_const.sub (analyticAt_const.mul
      (analyticAt_id.div ((analyticAt_const.add analyticAt_id).pow 2) (pow_ne_zero _ hn)))
  · have he : deriv (modelCoord c) z = -(c^2) * (1-z) / (1+z)^3 := by
      rw [show deriv (modelCoord c) z = _ from hd.deriv]
      simp only [Pi.pow_apply, Pi.add_apply, id_eq, zero_add, mul_one]
      field_simp [hn]
      ring
    rw [he]
    exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ hc)) hm) (pow_ne_zero _ hn)

private theorem modelCoord_rep {p : ℝ} (hp : 0 < p) {z : ℂ} (hz : z ∈ disk) :
    let c : ℂ := 2 + (p : ℂ) + (p : ℂ)⁻¹
    omittedParam (((-c⁻¹ : ℂ)) : Sphere) (modelCoord c z) = extremal p z := by
  let c : ℂ := 2 + (p : ℂ) + (p : ℂ)⁻¹
  have hc : c ≠ 0 := by
    change 2 + (p : ℂ) + (p : ℂ)⁻¹ ≠ 0
    exact_mod_cast (show 2 + p + p⁻¹ ≠ 0 by positivity)
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  let d := (1 - (p : ℂ)*z) * (1-z/(p : ℂ))
  have he : modelCoord c z = c * d / (1+z)^2 := by
    unfold modelCoord
    have h : (1+z)^2 - c*z = d := by dsimp [c,d]; field_simp; ring
    rw [← h]
    field_simp [one_add_ne_on_disk hz]
  change omittedParam ((-c⁻¹ : ℂ) : Sphere) (modelCoord c z) =
    (if d = 0 then OnePoint.infty else ((z/d : ℂ) : Sphere))
  rw [omittedParam_finite, he]
  by_cases h : d = 0
  · simp [h]
  · simp only [ite_eq_right h, ite_eq_right (div_ne_zero (mul_ne_zero hc h)
        (pow_ne_zero _ (one_add_ne_on_disk hz))), OnePoint.coe_eq_coe, inv_div]
    have h' : (1+z)^2 = d + c*z := by dsimp [c,d]; field_simp; ring
    rw [h']
    field_simp
    ring

/-- The extremal image has a centered chart agreeing with the rational extremal on the disk. -/
theorem extremal_model_geometry {p : ℝ} (hp : 0 < p) :
    IsTarget (extremalTarget p) ∧ ∃ C : CenteredChart (extremalTarget p) 0,
      EqOn C.forward (extremal p) disk := by
  let c : ℂ := 2 + (p : ℂ) + (p : ℂ)⁻¹
  let q : Sphere := ((-c⁻¹ : ℂ) : Sphere)
  let f := modelCoord c
  have hc : c ≠ 0 := by
    change 2 + (p : ℂ) + (p : ℂ)⁻¹ ≠ 0
    exact_mod_cast (show 2 + p + p⁻¹ ≠ 0 by positivity)
  have he : EqOn (omittedParam q ∘ f) (extremal p) disk :=
    fun _ hz => modelCoord_rep hp hz
  have hi : InjOn f disk := by
    intro x hx y hy hxy
    exact extremal_injOn hp.ne' hx hy ((he hx).symm.trans ((congrArg (omittedParam q) hxy).trans (he hy)))
  obtain ⟨hB, hop, hsc⟩ := regular_bihol_image (fun z hz => (modelCoord_regular hc hz).1)
    hi (fun z hz => (modelCoord_regular hc hz).2)
  have himg : extremalTarget p = omittedParam q '' (f '' disk) := by
    rw [← image_comp]
    exact he.image_eq.symm
  have hq : q ∉ extremalTarget p := by
    rw [himg]
    intro h
    have hm := image_subset_range (omittedParam q) _ h
    simp [omittedParam_range] at hm
  have hpre : omittedParam q ⁻¹' extremalTarget p = f '' disk := by
    rw [himg, preimage_image_eq _ (isOpenEmbedding_omittedParam q).injective]
  have hzero : extremal p 0 = (0 : ℂ) := by simp [extremal]
  have h0 : (0 : ℂ) ∈ disk := by simp [disk]
  have hw : ((0 : ℂ) : Sphere) ∈ extremalTarget p := ⟨0, h0, hzero⟩
  have hcenter : f 0 = omittedCoord q (0 : ℂ) := by
    rw [← hzero, ← he h0]
    exact (omittedCoord_param q (f 0)).symm
  let C := centeredChartOfOmittedBihol hq hw (f := f) (hpre ▸ hB) hcenter
  have hforward : EqOn C.forward (extremal p) disk := he
  refine ⟨⟨himg ▸ (isOpenEmbedding_omittedParam q).isOpenMap _ hop,
    himg ▸ (isOpenEmbedding_omittedParam q).isEmbedding.isSimplyConnected_image.mpr hsc,
    ?_⟩, C, hforward⟩
  have ho : ∀ t, omittedParam q t ≠ q := by
    intro t ht
    have h : q ∈ range (omittedParam q) := ⟨t, ht⟩
    simp [omittedParam_range] at h
  refine ⟨q, omittedParam q (f 1), hq, ?_, (ho _).symm⟩
  rw [himg]
  rintro ⟨_, ⟨z, hz, rfl⟩, heq⟩
  have hc1 : f z = f 1 := (isOpenEmbedding_omittedParam q).injective heq
  change c - c^2 * (z/(1+z)^2) = c - c^2 * (1/(1+1)^2) at hc1
  have heq' := mul_left_cancel₀ (pow_ne_zero 2 hc) (sub_right_inj.mp hc1)
  have h : (z-1)^2 = 0 := by
    field_simp [one_add_ne_on_disk hz] at heq'
    linear_combination -heq'
  have hz1 : z = 1 := sub_eq_zero.mp (pow_eq_zero_iff (by decide : 2 ≠ 0) |>.1 h)
  simp [hz1, disk] at hz

/-- Normalization and pole parameter of the same target, including the pole-free endpoint. -/
theorem extremal_model_data {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    IsTarget (extremalTarget p) ∧ SphereHolomorphicOn (extremal p) disk ∧
      radius (extremalTarget p) 0 = 1 ∧ poleParam (extremalTarget p) 0 = p := by
  obtain ⟨hU, C, hC⟩ := extremal_model_geometry hp
  rcases hp1.lt_or_eq with hlt | rfl
  · have hid : restoreValue 0 1 = id := by
      funext v
      induction v using OnePoint.rec with
      | infty => rfl
      | coe z =>
        change ((0 + 1 * z : ℂ) : Sphere) = (z : Sphere)
        simp
    have hi : poleParam (extremalTarget p) 0 = p ∧ radius (extremalTarget p) 0 = 1 := by
      simpa only [hid, Function.id_comp, norm_one, extremalTarget] using
        affine_extremal_invariants 0 (a := 1) one_ne_zero hp hlt
    exact ⟨hU, (isM_extremal hp hlt).1, hi.2, hi.1⟩
  have h0 : (0 : ℂ) ∈ disk := by simp [disk]
  have he := hC.eventuallyEq_of_mem (isOpen_ball.mem_nhds h0)
  have hd : deriv (finitePart ∘ extremal 1) 0 = 1 := by
    simpa [coeff] using coeff_extremal_one 1
  refine ⟨hU, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨g, hg, heq | heq⟩ := C.forward_holo z hz
    · exact ⟨g, hg, Or.inl ((hC.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz)).symm.trans heq)⟩
    · exact ⟨g, hg, Or.inr ((hC.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz)).symm.trans heq)⟩
  · rw [C.radius_eq, (he.fun_comp finitePart).deriv_eq, hd, norm_one]
  · have h : OnePoint.infty ∉ extremalTarget 1 := by
      rintro ⟨z, hz, heq⟩
      have hn : 1-z ≠ 0 := by
        intro he
        have h : z = 1 := (sub_eq_zero.mp he).symm
        simp [disk, h] at hz
      simp [extremal, hn] at heq
    simp [poleParam, h]

/-- One rotated rational map attains the disk bound in every order. -/
theorem diskSharpModel : DiskSharpModel := by
  intro p hp hp1 a ha
  obtain ⟨hU, hhol, hrad, hpar⟩ := extremal_model_data hp hp1
  let f (z : ℂ) := diskPhase a * diskInverse a z
  have hf : AnalyticOnNhd ℂ f disk := fun z hz =>
    analyticAt_const.mul ((diskInverse_bihol ha).1 z hz)
  have hm : MapsTo f disk disk := by
    intro z hz
    have h := mem_ball_zero_iff.mp (diskInverse_maps_disk ha hz)
    simpa [f, disk, mem_ball_zero_iff, norm_mul] using h
  refine ⟨diskPhase a, norm_diskPhase a, diskPhase_real, hU,
    hhol.comp_analyticOnNhd hf hm, (mapsTo_image _ _).comp hm, ?_, hpar, ?_⟩
  · simp [diskInverse, extremal]
  · intro n hn
    rw [hrad]
    exact disk_model_derivativeRatio hp ha (by omega)

/-- The all-order model supplies a witness for each order in the sharpness statement. -/
theorem diskSharpness_of_diskSharpModel (h : DiskSharpModel) : DiskSharpness := by
  intro p hp hp1 a ha n hn
  obtain ⟨η, _, _, hU, hG, hm, hz, hpar, he⟩ := h p hp hp1 a ha
  exact ⟨extremalTarget p, _, 0, hU, hG, hm, hz, hpar, he n hn⟩

theorem diskSharpness : DiskSharpness := diskSharpness_of_diskSharpModel diskSharpModel

/--
info: 'Goodman.diskSharpModel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms diskSharpModel

/--
info: 'Goodman.diskSharpness' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms diskSharpness

end Goodman
