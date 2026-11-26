-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
module

public import Goodman.MobiusSphere
public import Goodman.Extremal
public import Goodman.TargetNormalize

@[expose] public section

noncomputable section
open Set Metric Filter
open scoped Topology

namespace Goodman

/-- The finite real closed interval, viewed in the Riemann sphere. -/
def realSlitSegment (l r : ℝ) : Set Sphere :=
  planeDomain (Complex.ofReal '' Icc l r)

theorem realSlitSegment_eq_segment {l r : ℝ} (h : l ≤ r) :
    realSlitSegment l r = planeDomain (segment ℝ (l : ℂ) (r : ℂ)) := by
  unfold realSlitSegment
  rw [← segment_eq_Icc h]
  exact congrArg planeDomain (image_segment ℝ Complex.ofRealAm.toLinearMap.toAffineMap l r)

/-- The pole of the Joukowski map at zero is a genuine spherical value. -/
def joukowskiSphere (z : ℂ) : Sphere :=
  if z = 0 then OnePoint.infty else ((z + z⁻¹ : ℂ) : Sphere)

private lemma joukowski_unit {u : ℂ} (hu : ‖u‖ = 1) :
    u + u⁻¹ = ((2 * u.re : ℝ) : ℂ) := by
  rw [Complex.inv_eq_conj hu]
  apply Complex.ext <;> simp
  ring

private lemma joukowski_fiber {u z : ℂ} (hu : u ≠ 0) (hz : z ≠ 0)
    (he : z + z⁻¹ = u + u⁻¹) : z = u ∨ z * u = 1 := by
  have h : (z - u) * (z * u - 1) = 0 := by
    field_simp [hz, hu] at he
    linear_combination he
  simpa [mul_eq_zero, sub_eq_zero] using h

/-- The two roots over each finite value have product one. The values on the
unit circle are precisely the real interval from -2 to 2. -/
theorem joukowskiSphere_image_disk :
    joukowskiSphere '' disk = (realSlitSegment (-2) 2)ᶜ := by
  ext v
  induction v using OnePoint.rec with
  | infty => simp [joukowskiSphere, realSlitSegment, planeDomain, disk, Set.mem_image]
  | coe v =>
    change (∃ z ∈ disk, joukowskiSphere z = (v : Sphere)) ↔
      (v : Sphere) ∉ planeDomain (Complex.ofReal '' Icc (-2) 2)
    constructor
    · rintro ⟨z, hz, he⟩ ⟨_, ⟨x, hx, rfl⟩, hv⟩
      have hz0 : z ≠ 0 := by rintro rfl; simp [joukowskiSphere] at he
      have h : z + z⁻¹ = (x : ℂ) := OnePoint.coe_injective
        ((by simpa [joukowskiSphere, hz0] using he : ((z + z⁻¹ : ℂ) : Sphere) = v).trans hv.symm)
      let u : ℂ := (↑(x / 2) : ℂ) + Complex.I * ↑(Real.sqrt (1 - (x / 2)^2))
      have hhalf : ‖x / 2‖ ≤ 1 := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
      have hu : ‖u‖ = 1 := by
        have hsq := Complex.normSq_ofReal_add_I_mul_sqrt_one_sub hhalf
        change Complex.normSq u = 1 at hsq
        rw [Complex.normSq_eq_norm_sq] at hsq
        nlinarith [norm_nonneg u]
      have hur : 2 * u.re = x := by simp [u, Complex.add_re, Complex.mul_re]; ring
      rw [← hur, ← joukowski_unit hu] at h
      have hun : u ≠ 0 := norm_ne_zero_iff.mp (hu ▸ one_ne_zero)
      have hlt := mem_ball_zero_iff.mp hz
      rcases joukowski_fiber hun hz0 h with heq | hprod
      · rw [heq, hu] at hlt
        exact lt_irrefl _ hlt
      · have hn := congrArg norm hprod
        rw [norm_mul, hu, mul_one, norm_one] at hn
        exact hlt.ne hn
    · intro hv
      obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (v^2 - 4) (n := 2) (by decide)
      let z := (v + s) / 2
      let z' := (v - s) / 2
      have hprod : z * z' = 1 := by dsimp [z, z']; linear_combination -hs / 4
      have hsum : z + z' = v := by dsimp [z, z']; ring
      have hz : z ≠ 0 := left_ne_zero_of_mul_eq_one hprod
      have hz' : z' ≠ 0 := right_ne_zero_of_mul_eq_one hprod
      have hinv : z⁻¹ = z' := by field_simp [hz]; linear_combination -hprod
      have hunit : ‖z‖ ≠ 1 := by
        intro hu
        have h := (abs_le.mp (Complex.abs_re_le_norm z))
        rw [hu] at h
        apply hv
        refine ⟨_, ⟨2 * z.re, ⟨by linarith [h.1], by linarith [h.2]⟩, rfl⟩, ?_⟩
        exact congrArg OnePoint.some ((joukowski_unit hu).symm.trans (hinv ▸ hsum))
      rcases lt_or_gt_of_ne hunit with hlt | hgt
      · exact ⟨z, mem_ball_zero_iff.mpr hlt, by simp [joukowskiSphere, hz, hinv, hsum]⟩
      · have hn := congrArg norm hprod
        rw [norm_mul, norm_one] at hn
        have hlt : ‖z'‖ < 1 := by
          by_contra! hle
          nlinarith [mul_nonneg (sub_nonneg.mpr hle) (norm_nonneg z)]
        exact ⟨z', mem_ball_zero_iff.mpr hlt, by
          simp only [joukowskiSphere, ite_eq_right hz', OnePoint.coe_eq_coe]
          rw [← hinv, inv_inv, add_comm, hinv, hsum]⟩

private lemma extremal_eq_move_joukowski {p : ℝ} (hp : p ≠ 0) :
    extremal p = moveOmitted ((↑(p + 1 / p) : ℂ) : Sphere) ∘ joukowskiSphere := by
  funext z
  by_cases hz : z = 0
  · simp [hz, extremal, joukowskiSphere, Function.comp_apply]
    rfl
  · have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp
    let d := (1 - (p : ℂ) * z) * (1 - z / p)
    have hd : z + z⁻¹ - ↑(p + 1 / p) = d / z := by
      push_cast
      dsimp [d]
      field_simp [hz, hpc]
      ring
    simp only [Function.comp_apply, joukowskiSphere, ite_eq_right hz]
    change (if d = 0 then OnePoint.infty else ((z / d : ℂ) : Sphere)) =
      fromRecip (z + z⁻¹ - ↑(p + 1 / p))
    rw [hd]
    by_cases h : d = 0 <;> simp [h, hz, fromRecip]

private lemma move_real_interval {B : ℝ} (hB : 2 < B) :
    moveOmitted ((B : ℂ) : Sphere) '' realSlitSegment (-2) 2 =
      realSlitSegment (-1 / (B - 2)) (-1 / (B + 2)) := by
  let f (x : ℝ) := -1 / (B - x)
  have hpos {x : ℝ} (hx : x ∈ Icc (-2 : ℝ) 2) : 0 < B - x := sub_pos.mpr (hx.2.trans_lt hB)
  have hc : ContinuousOn f (Icc (-2) 2) :=
    continuousOn_const.div (continuousOn_const.sub continuousOn_id) fun _ hx => (hpos hx).ne'
  have ha : AntitoneOn f (Icc (-2) 2) := by
    intro x hx y hy hxy
    simpa [f, neg_div] using neg_le_neg (one_div_le_one_div_of_le (hpos hy) (by linarith : B - y ≤ B - x))
  have hi := hc.image_Icc_of_antitoneOn (by norm_num : (-2 : ℝ) ≤ 2) ha
  have hf {x : ℝ} (hx : x ∈ Icc (-2 : ℝ) 2) :
      moveOmitted ((B : ℂ) : Sphere) ((x : ℂ) : Sphere) = ((f x : ℂ) : Sphere) := by
    change fromRecip ((x : ℂ) - B) = _
    have hn : (x : ℂ) - B ≠ 0 := by exact_mod_cast (by linarith [hpos hx] : x - B ≠ 0)
    simp only [fromRecip, ite_eq_right hn, OnePoint.coe_eq_coe, f]
    push_cast
    field_simp [hn, sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hn))]
    ring
  have hi' : f '' Icc (-2) 2 = Icc (-1 / (B - 2)) (-1 / (B + 2)) := by
    simpa [f] using hi
  unfold realSlitSegment planeDomain
  rw [← hi']
  simp only [image_image]
  apply image_congr
  exact fun x hx => hf hx

theorem two_lt_extremal_parameter {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    2 < p + 1 / p := by
  rw [← sub_lt_iff_lt_add', lt_div_iff₀ hp]
  nlinarith [sq_pos_of_pos (sub_pos.mpr hp1)]

/-- Exact spherical image of the normalized extremal, with both slit endpoints included. -/
theorem extremal_image_disk {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    extremal p '' disk =
      (realSlitSegment (-1 / (p + 1 / p - 2)) (-1 / (p + 1 / p + 2)))ᶜ := by
  rw [extremal_eq_move_joukowski hp.ne', image_comp, joukowskiSphere_image_disk,
    image_compl_eq (moveOmitted _).bijective, move_real_interval (two_lt_extremal_parameter hp hp1)]

/-- The boundary pole of Koebe sends the right endpoint of the Joukowski slit
to infinity. The finite omitted values form the ray ending at -1/4. -/
theorem koebe_image_disk :
    (fun z : ℂ => z / (1-z)^2) '' disk = (Complex.ofReal '' Iic (-1/4 : ℝ))ᶜ := by
  let M := moveOmitted ((2 : ℂ) : Sphere)
  have he : extremal 1 = M ∘ joukowskiSphere := by
    convert extremal_eq_move_joukowski (p := 1) one_ne_zero using 1
    norm_num [M]
  have himg : extremal 1 '' disk = (M '' realSlitSegment (-2) 2)ᶜ := by
    rw [he, image_comp, joukowskiSphere_image_disk, image_compl_eq M.bijective]
  have hval {z : ℂ} (hz : z ∈ disk) :
      extremal 1 z = ((z/(1-z)^2 : ℂ) : Sphere) := by
    have hz1 : 1-z ≠ 0 := by
      intro hh
      have hh' : z = 1 := (sub_eq_zero.mp hh).symm
      have hn := mem_ball_zero_iff.mp hz
      simp [hh'] at hn
    simp [extremal, pow_two, hz1]
  ext v
  have hv : v ∈ (fun z : ℂ => z/(1-z)^2) '' disk ↔ (v : Sphere) ∈ extremal 1 '' disk := by
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, hval hz⟩
    · rintro ⟨z, hz, h⟩
      exact ⟨z, hz, OnePoint.coe_injective ((hval hz).symm.trans h)⟩
  rw [hv, himg, mem_compl_iff, mem_compl_iff]
  apply not_congr
  constructor
  · rintro ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, h⟩
    change fromRecip ((x : ℂ) - 2) = (v : Sphere) at h
    rcases eq_or_lt_of_le hx.2 with rfl | hlt
    · simp [fromRecip] at h
    · have hn : (x : ℂ) - 2 ≠ 0 := by exact_mod_cast (sub_neg.mpr hlt).ne
      rw [fromRecip, ite_eq_right hn, OnePoint.coe_eq_coe] at h
      refine ⟨(x-2)⁻¹, ?_, by push_cast; exact h⟩
      change (x-2)⁻¹ ≤ -1/4
      apply (inv_le_of_neg (sub_neg.mpr hlt) (by norm_num)).2
      norm_num
      linarith [hx.1]
  · rintro ⟨y, hy, rfl⟩
    change y ≤ -1/4 at hy
    have hneg : y < 0 := by linarith
    have hlo : -4 ≤ y⁻¹ := by
      have h := (inv_le_inv_of_neg (by norm_num : (-1/4 : ℝ) < 0) hneg).2 hy
      norm_num at h
      exact h
    have hhi : y⁻¹ < 0 := inv_lt_zero'.mpr hneg
    refine ⟨((↑(2+y⁻¹) : ℂ) : Sphere), ⟨_, ⟨2+y⁻¹, ⟨by linarith, by linarith⟩, rfl⟩, rfl⟩, ?_⟩
    change fromRecip (↑(2+y⁻¹) - (2 : ℂ)) = ((y : ℂ) : Sphere)
    have hn : (y : ℂ) ≠ 0 := by exact_mod_cast hneg.ne
    simp [fromRecip, hn]

theorem restoreValue_bijective (w : ℂ) {a : ℂ} (ha : a ≠ 0) :
    Function.Bijective (restoreValue w a) :=
  (((Equiv.mulLeft₀ a ha).trans (Equiv.addLeft w)).optionCongr).bijective

lemma restore_as_normalize (w : ℂ) {a : ℂ} (ha : a ≠ 0) :
    restoreValue w a = normalizeValue (-w/a) a⁻¹ := by
  funext v
  induction v using OnePoint.rec with
  | infty => rfl
  | coe z =>
    apply congrArg OnePoint.some
    change w + a*z = (z - -w/a)/a⁻¹
    field_simp
    ring

theorem sphereHolomorphicOn_affine_extremal (w : ℂ) {a : ℂ} (ha : a ≠ 0)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    SphereHolomorphicOn (restoreValue w a ∘ extremal p) disk := by
  rw [restore_as_normalize w ha]
  exact (isM_extremal hp hp1).1.normalizeValue (inv_ne_zero ha)

private lemma affine_image_segment (w a x y : ℂ) :
    restoreValue w a '' planeDomain (segment ℝ x y) =
      planeDomain (segment ℝ (w + a*x) (w + a*y)) := by
  unfold planeDomain
  simp only [segment_eq_image', image_image]
  congr 1
  funext t
  apply congrArg OnePoint.some
  change w + a * (x + t • (y - x)) = w + a*x + t • (w + a*y - (w + a*x))
  simp only [Complex.real_smul]
  ring

/-- The missing segment of an affine extremal, in the order far endpoint to near endpoint. -/
theorem affine_extremal_image_disk (w : ℂ) {a : ℂ} (ha : a ≠ 0) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    (restoreValue w a ∘ extremal p) '' disk =
      (planeDomain (segment ℝ
        (w + a * ↑(-1 / (p + 1 / p - 2))) (w + a * ↑(-1 / (p + 1 / p + 2)))))ᶜ := by
  have hB := two_lt_extremal_parameter hp hp1
  have hlt := one_div_lt_one_div_of_lt (sub_pos.mpr hB)
    (by linarith : p + 1 / p - 2 < p + 1 / p + 2)
  rw [image_comp, extremal_image_disk hp hp1, image_compl_eq (restoreValue_bijective w ha),
    realSlitSegment_eq_segment (by simpa [neg_div] using (neg_lt_neg hlt).le), affine_image_segment]

private lemma affine_segment_through (w : ℂ) {a : ℂ} (ha : a ≠ 0) {l r : ℝ} (hlr : l < r) :
    IsSegmentOnLineThrough (planeDomain (segment ℝ (w + a * ↑l) (w + a * ↑r))) w := by
  have hn : (↑r : ℂ) - ↑l ≠ 0 := by exact_mod_cast (sub_pos.mpr hlr).ne'
  have hne : w + a*(l : ℂ) ≠ w + a*(r : ℂ) := by
    intro he
    exact hlr.ne (Complex.ofReal_injective (mul_left_cancel₀ ha (add_left_cancel he)))
  have hline : w = w + a*(l : ℂ) + (↑(-l/(r-l)) : ℂ) * ((w + a*(r : ℂ)) - (w + a*(l : ℂ))) := by
    push_cast
    field_simp [hn]
    ring
  exact ⟨_, _, hne, rfl, _, hline⟩

theorem affine_extremal_segmentOnLineThrough (w : ℂ) {a : ℂ} (ha : a ≠ 0) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    IsSegmentOnLineThrough (((restoreValue w a ∘ extremal p) '' disk)ᶜ) w := by
  rw [affine_extremal_image_disk w ha hp hp1, compl_compl]
  apply affine_segment_through w ha
  simp only [neg_div, neg_lt_neg_iff]
  exact one_div_lt_one_div_of_lt (sub_pos.mpr (two_lt_extremal_parameter hp hp1)) (by linarith)

lemma affine_extremal_regular_coord (w : ℂ) {a : ℂ} (ha : a ≠ 0)
    {p : ℝ} (hp : 0 < p) {x : ℂ} (hx : x ∈ disk)
    (hfin : restoreValue w a (extremal p x) ≠ OnePoint.infty) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g x ∧ deriv g x ≠ 0 ∧
      ∀ᶠ z in 𝓝 x, restoreValue w a (extremal p z) = (g z : Sphere) := by
  let d (z : ℂ) := (1 - (p : ℂ)*z)*(1-z/(p : ℂ))
  have hd : d x ≠ 0 := by
    intro he
    apply hfin
    change restoreValue w a (if d x = 0 then OnePoint.infty else ((x/d x : ℂ) : Sphere)) = _
    rw [ite_eq_left he]
    rfl
  have hda : AnalyticAt ℂ d x := by dsimp [d]; fun_prop
  let g (z : ℂ) := w + a*(z/d z)
  have hd₁ := (hasDerivAt_const x (1 : ℂ)).sub ((hasDerivAt_id x).const_mul (p : ℂ))
  have hd₂ := (hasDerivAt_const x (1 : ℂ)).sub ((hasDerivAt_id x).div_const (p : ℂ))
  have hg := (hasDerivAt_const x w).add (((hasDerivAt_id x).div (hd₁.mul hd₂) hd).const_mul a)
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hnum : 1 * d x - x * ((0 - (p : ℂ) * 1) * (1-x/(p : ℂ)) +
      (1-(p : ℂ)*x)*(0 - 1/(p : ℂ))) = 1-x^2 := by
    dsimp [d]
    field_simp
    ring
  have hx2 : 1 - x^2 ≠ 0 := by
    intro he
    have hn := congrArg norm (sub_eq_zero.mp he)
    rw [norm_one, norm_pow] at hn
    have hlt := mem_ball_zero_iff.mp hx
    nlinarith [mul_pos (sub_pos.mpr hlt) (by positivity : 0 < 1 + ‖x‖)]
  refine ⟨g, analyticAt_const.add (analyticAt_const.mul (analyticAt_id.div hda hd)), ?_, ?_⟩
  · rw [show deriv g x = _ from hg.deriv]
    change 0 + a * ((1 * d x - x * _) / (d x)^2) ≠ 0
    simp only [Pi.sub_apply, id_eq]
    rw [hnum, zero_add]
    exact mul_ne_zero ha (div_ne_zero hx2 (pow_ne_zero _ hd))
  · filter_upwards [hda.continuousAt.eventually_ne hd] with z hz
    change restoreValue w a (if d z = 0 then OnePoint.infty else ((z/d z : ℂ) : Sphere)) = _
    rw [ite_eq_right hz]
    rfl

/-- The analytic inverse function theorem in the finite and reciprocal charts gives
an actual centered conformal chart onto the image of the affine extremal. -/
def affineExtremalChart (w : ℂ) {a : ℂ} (ha : a ≠ 0) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    CenteredChart ((restoreValue w a ∘ extremal p) '' disk) w := by
  let F := restoreValue w a ∘ extremal p
  let i := Function.invFunOn F disk
  have hM := isM_extremal hp hp1
  have hinj : InjOn F disk := (restoreValue_bijective w ha).1.injOn.comp hM.2.1 (mapsTo_image _ _)
  have hl : LeftInvOn i F disk := hinj.leftInvOn_invFunOn
  have localInv {x : ℂ} (hx : x ∈ disk) (c : ℂ → Sphere) {g : ℂ → ℂ}
      (hg : AnalyticAt ℂ g x) (hdg : deriv g x ≠ 0) (he : ∀ᶠ z in 𝓝 x, F z = c (g z)) :
      AnalyticAt ℂ (i ∘ c) (g x) := by
    apply (analyticAt_comp_iff_of_deriv_ne_zero hg hdg).1
    apply analyticAt_id.congr
    filter_upwards [he, isOpen_ball.mem_nhds hx] with z hz hzD
    change z = i (c (g z))
    rw [← hz, hl hzD]
  refine { forward := F, inverse := i, forward_holo := sphereHolomorphicOn_affine_extremal w ha hp hp1,
           forward_maps := mapsTo_image _ _, inverse_maps := (surjOn_image F disk).mapsTo_invFunOn,
           left_inverse := hl, right_inverse := (surjOn_image F disk).rightInvOn_invFunOn,
           center := by simp [F, hM.2.2.2.2.1, restoreValue], inverse_holo := ⟨?_, ?_⟩ }
  · rintro v ⟨x, hx, he⟩
    have hfin : F x ≠ OnePoint.infty := fun hh => OnePoint.coe_ne_infty v (he.symm.trans hh)
    obtain ⟨g, hg, hdg, h⟩ := affine_extremal_regular_coord w ha hp hx hfin
    have hv : g x = v := OnePoint.coe_injective (h.self_of_nhds.symm.trans he)
    exact hv ▸ localInv hx OnePoint.some hg hdg h
  · intro _
    have hpD : (p : ℂ) ∈ disk := by simpa [disk, abs_of_pos hp] using hp1
    have hs : SimplePoleAt F p := by
      dsimp only [F]
      rw [restore_as_normalize w ha]
      exact hM.2.2.2.1.normalizeValue (inv_ne_zero ha)
    obtain ⟨g, hg, hg0, hdg, he⟩ := hs
    exact hg0 ▸ localInv hpD fromRecip hg hdg he

/-- The geometric invariants agree with the pole and affine dilation of the model. -/
theorem affine_extremal_invariants (w : ℂ) {a : ℂ} (ha : a ≠ 0)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    let U := (restoreValue w a ∘ extremal p) '' disk
    poleParam U w = p ∧ radius U w = ‖a‖ := by
  let c := affineExtremalChart w ha hp hp1
  have hM := isM_extremal hp hp1
  have hpD : (p : ℂ) ∈ disk := by simpa [disk, abs_of_pos hp] using hp1
  have hi : c.forward p = OnePoint.infty := by
    change restoreValue w a (extremal p p) = _
    rw [hM.2.2.1]
    rfl
  constructor
  · rw [c.poleParam_eq (hi ▸ c.forward_maps hpD), ← hi, c.left_inverse hpD,
      Complex.norm_of_nonneg hp.le]
  · rw [c.radius_eq]
    have h0 : (0 : ℂ) ∈ disk := mem_ball_self zero_lt_one
    have he := (hM.1.affine_germ h0 (hM.2.2.2.2.1 ▸ OnePoint.coe_ne_infty _)).2
    have h : finitePart ∘ c.forward =ᶠ[𝓝 (0 : ℂ)] fun z => w + a * (finitePart ∘ extremal p) z := by
      filter_upwards [he] with z hz
      exact congrArg (finitePart ∘ restoreValue w a) hz
    rw [h.deriv_eq, deriv_const_add, deriv_const_mul _ (hM.1.affine_germ h0
      (hM.2.2.2.2.1 ▸ OnePoint.coe_ne_infty _)).1.differentiableAt, hM.2.2.2.2.2, mul_one]

/-- Pole and dilation read from the near and far endpoint distances. -/
def segmentPole (near far : ℝ) : ℝ :=
  (Real.sqrt far - Real.sqrt near) / (Real.sqrt far + Real.sqrt near)

def segmentScale (near far : ℝ) : ℝ := 4 * near * far / (far - near)

theorem segment_parameters {l r : ℝ} (hl : 0 < l) (hlr : l < r) :
    let p := segmentPole l r
    let m := segmentScale l r
    0 < p ∧ p < 1 ∧ 0 < m ∧
      m / (p + 1 / p + 2) = l ∧ m / (p + 1 / p - 2) = r := by
  let x := Real.sqrt l
  let y := Real.sqrt r
  have hx : 0 < x := Real.sqrt_pos.mpr hl
  have hxy : x < y := Real.sqrt_lt_sqrt hl.le hlr
  have hy := hx.trans hxy
  have hxs : x^2 = l := Real.sq_sqrt hl.le
  have hys : y^2 = r := Real.sq_sqrt (hl.trans hlr).le
  let p := segmentPole l r
  have hpval : segmentPole l r = (y-x)/(y+x) := rfl
  have hp : 0 < p := div_pos (sub_pos.mpr hxy) (add_pos hy hx)
  have hp1 : p < 1 := (div_lt_one (add_pos hy hx)).2 (by linarith)
  have hm : 0 < segmentScale l r := div_pos (mul_pos (mul_pos (by norm_num) hl) (hl.trans hlr)) (sub_pos.mpr hlr)
  have hB := two_lt_extremal_parameter hp hp1
  change 0 < p ∧ p < 1 ∧ 0 < segmentScale l r ∧ _
  refine ⟨hp, hp1, hm, ?_, ?_⟩
  all_goals
    apply (div_eq_iff (by first | exact (sub_pos.mpr hB).ne' | exact (by linarith : p + 1 / p + 2 ≠ 0))).2
    unfold segmentScale
    rw [hpval, ← hxs, ← hys]
    field_simp [show y^2 - x^2 ≠ 0 by linarith, (sub_pos.mpr hxy).ne', (add_pos hy hx).ne']
    ring

private lemma endpoints_left {w x y : ℂ} {t : ℝ} (hxy : x ≠ y) (ht : t < 0)
    (hw : w = x + (t : ℂ) * (y-x)) :
    0 < ‖w-x‖ ∧ ‖w-x‖ < ‖w-y‖ ∧
      ∃ u : ℂ, ‖u‖ = 1 ∧ w-x = (‖w-x‖ : ℂ)*u ∧ w-y = (‖w-y‖ : ℂ)*u := by
  let d := ‖y-x‖
  have hd : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr hxy.symm)
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have h₁ : w-x = (t : ℂ)*(y-x) := by rw [hw]; ring
  have h₂ : w-y = (↑(t-1) : ℂ)*(y-x) := by rw [hw]; push_cast; ring
  have hnear : ‖w-x‖ = (-t)*d := by rw [h₁, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_neg ht]
  have hfar : ‖w-y‖ = (1-t)*d := by
    rw [h₂, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    dsimp [d]
    ring
  rw [hnear, hfar]
  refine ⟨mul_pos (neg_pos.mpr ht) hd, mul_lt_mul_of_pos_right (by linarith) hd,
    -(y-x)/(d : ℂ), ?_, ?_, ?_⟩
  · rw [norm_div, norm_neg, Complex.norm_of_nonneg hd.le]
    exact div_self hd.ne'
  · rw [h₁]
    push_cast
    field_simp
  · rw [h₂]
    push_cast
    field_simp
    ring

/-- An exterior center on the supporting line orders the endpoints by distance and
puts both on a single ray. The unit vector points from the near endpoint to the center. -/
theorem segment_ordered_endpoints {K : Set Sphere} {w : ℂ}
    (hK : IsSegmentOnLineThrough K w) (hw : (w : Sphere) ∉ K) :
    ∃ ξ η u : ℂ, K = planeDomain (segment ℝ ξ η) ∧
      0 < ‖w-ξ‖ ∧ ‖w-ξ‖ < ‖w-η‖ ∧ ‖u‖ = 1 ∧
      w-ξ = (‖w-ξ‖ : ℂ)*u ∧ w-η = (‖w-η‖ : ℂ)*u := by
  obtain ⟨x, y, hxy, hseg, t, ht⟩ := hK
  have htout : t ∉ Icc (0 : ℝ) 1 := by
    intro h
    apply hw
    rw [hseg]
    refine ⟨w, ?_, rfl⟩
    rw [segment_eq_image']
    exact ⟨t, h, by simpa [Complex.real_smul] using ht.symm⟩
  rcases lt_or_ge t 0 with hl | hl
  · obtain ⟨h₁, h₂, u, hu⟩ := endpoints_left hxy hl ht
    exact ⟨x, y, u, hseg, h₁, h₂, hu⟩
  · have hr : 1 < t := lt_of_not_ge fun h => htout ⟨hl, h⟩
    have he : w = y + (↑(1-t) : ℂ)*(x-y) := by rw [ht]; push_cast; ring
    obtain ⟨h₁, h₂, u, hu⟩ := endpoints_left hxy.symm (by linarith : 1-t < 0) he
    exact ⟨y, x, u, hseg.trans (congrArg planeDomain (segment_symm ℝ x y)), h₁, h₂, hu⟩

/-- Converse in Theorem 2. Starting from the geometric predicate and an exterior
finite center alone, recover the pole, the modulus and direction of the multiplier,
and a bijection of the disk onto the given spherical complement. -/
theorem segment_converse {K : Set Sphere} {w : ℂ} (hK : IsSegmentOnLineThrough K w)
    (hw : (w : Sphere) ∉ K) :
    ∃ (ξ η : ℂ) (p : ℝ) (a : ℂ), K = planeDomain (segment ℝ ξ η) ∧
      0 < ‖w-ξ‖ ∧ ‖w-ξ‖ < ‖w-η‖ ∧
      p = segmentPole ‖w-ξ‖ ‖w-η‖ ∧ 0 < p ∧ p < 1 ∧
      ‖a‖ = segmentScale ‖w-ξ‖ ‖w-η‖ ∧ a ≠ 0 ∧ a / (‖a‖ : ℂ) = (w-ξ)/(‖w-ξ‖ : ℂ) ∧
      (restoreValue w a ∘ extremal p) 0 = (w : Sphere) ∧
      (restoreValue w a ∘ extremal p) p = OnePoint.infty ∧
      BijOn (restoreValue w a ∘ extremal p) disk Kᶜ := by
  obtain ⟨ξ, η, u, hseg, hnear, hdist, hu, hξ, hη⟩ := segment_ordered_endpoints hK hw
  let p := segmentPole ‖w-ξ‖ ‖w-η‖
  let m := segmentScale ‖w-ξ‖ ‖w-η‖
  let a := (m : ℂ)*u
  obtain ⟨hp, hp1, hm, hsmall, hlarge⟩ := segment_parameters hnear hdist
  change 0 < m at hm
  change 0 < p at hp
  change p < 1 at hp1
  change m / (p + 1 / p + 2) = ‖w-ξ‖ at hsmall
  change m / (p + 1 / p - 2) = ‖w-η‖ at hlarge
  have hnorm : ‖a‖ = m := by rw [show ‖a‖ = ‖(m : ℂ)‖ * ‖u‖ from norm_mul .., Complex.norm_of_nonneg hm.le, hu, mul_one]
  have ha : a ≠ 0 := norm_pos_iff.mp (hnorm ▸ hm)
  have endpoint (d : ℝ) (e : ℂ) (h : m / d = ‖w-e‖) (he : w-e = (‖w-e‖ : ℂ)*u) :
      w + a * ↑(-1 / d) = e := by
    rw [← h] at he
    dsimp [a]
    push_cast at he ⊢
    simp only [div_eq_mul_inv] at he ⊢
    linear_combination he
  have himg : (restoreValue w a ∘ extremal p) '' disk = Kᶜ := by
    rw [affine_extremal_image_disk w ha hp hp1, endpoint _ _ hsmall hξ, endpoint _ _ hlarge hη,
      segment_symm ℝ η ξ, hseg]
  have hM := isM_extremal hp hp1
  refine ⟨ξ, η, p, a, hseg, hnear, hdist, rfl, hp, hp1, hnorm, ha, ?_, ?_, ?_, ?_⟩
  · have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    have hl' : (‖w-ξ‖ : ℂ) ≠ 0 := by exact_mod_cast hnear.ne'
    rw [hnorm]
    calc
      a / (m : ℂ) = u := by dsimp [a]; field_simp
      _ = (w-ξ)/(‖w-ξ‖ : ℂ) := (eq_div_iff hl').2 (by rw [mul_comm]; exact hξ.symm)
  · simp [Function.comp_apply, hM.2.2.2.2.1, restoreValue]
  · simp [Function.comp_apply, hM.2.2.1, restoreValue]
  · rw [← himg]
    exact ((restoreValue_bijective w ha).1.injOn.comp hM.2.1 (mapsTo_image _ _)).bijOn_image

/-- Intrinsic form of the endpoint formulas: the center and its omitted
segment determine the hyperbolic pole parameter and the conformal radius. -/
theorem segment_intrinsic_parameters {K : Set Sphere} {w : ℂ}
    (hK : IsSegmentOnLineThrough K w) (hw : (w : Sphere) ∉ K) :
    ∃ ξ η : ℂ, K = planeDomain (segment ℝ ξ η) ∧ 0 < ‖w-ξ‖ ∧ ‖w-ξ‖ < ‖w-η‖ ∧
      poleParam Kᶜ w = segmentPole ‖w-ξ‖ ‖w-η‖ ∧
      radius Kᶜ w = segmentScale ‖w-ξ‖ ‖w-η‖ := by
  obtain ⟨ξ, η, p, a, hseg, hnear, hdist, he, hp, hp1, hm, ha, _, _, _, hb⟩ :=
    segment_converse hK hw
  have hi := affine_extremal_invariants w ha hp hp1
  dsimp only at hi
  rw [hb.image_eq] at hi
  exact ⟨ξ, η, hseg, hnear, hdist, hi.1.trans he, hi.2.trans hm⟩

/--
info: 'Goodman.segment_intrinsic_parameters' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms segment_intrinsic_parameters

/--
info: 'Goodman.koebe_image_disk' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms koebe_image_disk

end Goodman
