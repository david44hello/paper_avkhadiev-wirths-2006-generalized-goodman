-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
module

public import Goodman.FigureGeometry
public import Goodman.SlitGeometry

@[expose] public section

noncomputable section
open Set Metric Filter
open scoped Topology

namespace Goodman

/-- The right endpoint of the enlarged slit, equal to the real Joukowski value at p. -/
def slitB (p : ℝ) : ℝ := p + 1 / p

@[simp] theorem joukowskiSphere_zero : joukowskiSphere 0 = OnePoint.infty := by
  simp [joukowskiSphere]

theorem joukowskiSphere_of_ne_zero {z : ℂ} (hz : z ≠ 0) :
    joukowskiSphere z = ((z + 1 / z : ℂ) : Sphere) := by
  simp [joukowskiSphere, hz]

theorem joukowskiSphere_ofReal {x : ℝ} (hx : x ≠ 0) :
    joukowskiSphere (x : ℂ) = ((slitB x : ℂ) : Sphere) := by
  rw [joukowskiSphere_of_ne_zero (Complex.ofReal_ne_zero.mpr hx)]
  simp [slitB]

/-- The quadratic denominator of the extremal in Joukowski coordinates. -/
theorem extremal_den_eq_quadratic {p : ℝ} (hp : p ≠ 0) (z : ℂ) :
    (1 - (p : ℂ)*z)*(1-z/p) = 1 - (slitB p : ℂ)*z + z^2 := by
  unfold slitB
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hp]
  ring

/-- Spherical rational identity on the entire finite source plane.
The Möbius transformation takes B to infinity and infinity to zero. -/
theorem extremal_eq_reciprocal_joukowski {p : ℝ} (hp : p ≠ 0) :
    extremal p = moveOmitted ((slitB p : ℂ) : Sphere) ∘ joukowskiSphere := by
  funext z
  by_cases hz : z = 0
  · subst z
    simp [extremal]
    rfl
  · let d := 1 - (slitB p : ℂ)*z + z^2
    have he : z + z⁻¹ - (slitB p : ℂ) = d / z := by
      dsimp [d]
      field_simp [hz]
      ring
    simp only [Function.comp_apply, joukowskiSphere, ite_eq_right hz, extremal,
      extremal_den_eq_quadratic hp]
    change (if d = 0 then OnePoint.infty else ((z / d : ℂ) : Sphere)) =
      fromRecip (z + z⁻¹ - (slitB p : ℂ))
    rw [he]
    by_cases hd : d = 0 <;> simp [fromRecip, hd, hz]

theorem joukowskiSphere_injOn_disk : InjOn joukowskiSphere disk := by
  intro z hz w hw he
  apply extremal_injOn (p := 1) one_ne_zero hz hw
  rw [extremal_eq_reciprocal_joukowski one_ne_zero]
  exact congrArg (moveOmitted ((slitB 1 : ℂ) : Sphere)) he

theorem joukowskiSphere_bijOn_disk :
    BijOn joukowskiSphere disk (realSlitSegment (-2) 2)ᶜ := by
  rw [← joukowskiSphere_image_disk]
  exact joukowskiSphere_injOn_disk.bijOn_image

/-- Decrease of x + 1/x along the real radius, even with the outer endpoint included. -/
theorem joukowskiReal_strictAnti {p : ℝ} (hp : 0 < p) :
    StrictAntiOn slitB (Icc p 1) := by
  intro x hx y hy hxy
  have h := slitArcRe_strictAnti hp hx hy hxy
  unfold slitArcRe at h
  unfold slitB
  simp only [one_div]
  by_contra! hle
  linarith [mul_le_mul_of_nonneg_left (add_le_add_right hle 2) (slitR_pos hp).le]

theorem joukowskiReal_image_radius {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    slitB '' Ico p 1 = Ioc 2 (slitB p) := by
  have hc : ContinuousOn slitB (Icc p 1) := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    unfold slitB
    fun_prop (disch := exact (hp.trans_le hx.1).ne')
  simpa [slitB, one_add_one_eq_two] using
    hc.image_Ico_of_strictAntiOn hp1.le (joukowskiReal_strictAnti hp)

theorem joukowskiReal_tendsto_one_left : Tendsto slitB (𝓝[<] (1 : ℝ)) (𝓝 2) := by
  have hc : ContinuousAt slitB 1 := by unfold slitB; fun_prop (disch := norm_num)
  have h1 : slitB 1 = 2 := by norm_num [slitB]
  rw [← h1]
  exact hc.continuousWithinAt

theorem joukowskiSphere_image_radius {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    joukowskiSphere '' (Complex.ofReal '' Ico p 1) =
      planeDomain (Complex.ofReal '' Ioc 2 (slitB p)) := by
  rw [← joukowskiReal_image_radius hp hp1]
  unfold planeDomain
  simp only [image_image]
  apply image_congr
  intro x hx
  exact joukowskiSphere_ofReal (hp.trans_le hx.1).ne'

theorem joukowskiSphere_image_slitDisk {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    joukowskiSphere '' slitDisk p = (realSlitSegment (-2) (slitB p))ᶜ := by
  have hs : Complex.ofReal '' Ico p 1 ⊆ disk := by
    rintro _ ⟨x, hx, rfl⟩
    exact mem_ball_zero_iff.mpr ((Complex.norm_of_nonneg (hp.trans_le hx.1).le).trans_lt hx.2)
  rw [slitDisk, joukowskiSphere_injOn_disk.image_sdiff_subset hs, joukowskiSphere_image_disk,
    joukowskiSphere_image_radius hp hp1, sdiff_eq, ← compl_union]
  unfold realSlitSegment planeDomain
  have hB : 2 ≤ slitB p := (two_lt_extremal_parameter hp hp1).le
  rw [← image_union, ← image_union, Icc_union_Ioc_eq_Icc (by norm_num : (-2 : ℝ) ≤ 2) hB]

/-- The slope R of the affine map is determined by the two finite endpoints. -/
theorem slitR_mul_slitB_add_two {p : ℝ} (hp : 0 < p) :
    slitR p * (slitB p + 2) = 4 := by
  unfold slitR slitB
  field_simp [hp.ne', (by linarith : 1 + p ≠ 0)]
  ring

theorem four_div_slitR {p : ℝ} (hp : 0 < p) : 4 / slitR p = slitB p + 2 := by
  exact (div_eq_iff (slitR_pos hp).ne').2 (by rw [mul_comm, slitR_mul_slitB_add_two hp])

/-- The affine change of Joukowski coordinate on the sphere. -/
def slitJoukowskiAffine (p : ℝ) : Sphere → Sphere :=
  restoreValue (2 * (slitR p : ℂ) - 2) (slitR p)

theorem slitJoukowskiAffine_coe (p : ℝ) (v : ℂ) :
    slitJoukowskiAffine p (v : Sphere) = (((slitR p : ℂ) * (v + 2) - 2 : ℂ) : Sphere) := by
  apply congrArg OnePoint.some
  change 2 * (slitR p : ℂ) - 2 + (slitR p : ℂ) * v = _
  ring

@[simp] theorem slitJoukowskiAffine_infty (p : ℝ) :
    slitJoukowskiAffine p OnePoint.infty = OnePoint.infty := rfl

theorem slitJoukowskiAffine_endpoints {p : ℝ} (hp : 0 < p) :
    slitJoukowskiAffine p ((-2 : ℂ) : Sphere) = ((-2 : ℂ) : Sphere) ∧
    slitJoukowskiAffine p ((slitB p : ℂ) : Sphere) = ((2 : ℂ) : Sphere) := by
  simp only [slitJoukowskiAffine_coe, OnePoint.coe_eq_coe]
  have h : (slitR p : ℂ) * ((slitB p : ℂ) + 2) = 4 := by
    exact_mod_cast slitR_mul_slitB_add_two hp
  rw [h]
  norm_num

theorem slitJoukowskiAffine_image_compl {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    slitJoukowskiAffine p '' (realSlitSegment (-2) (slitB p))ᶜ =
      (realSlitSegment (-2) 2)ᶜ := by
  rw [image_compl_eq (f := slitJoukowskiAffine p)
    (restoreValue_bijective _ (Complex.ofReal_ne_zero.mpr (slitR_pos hp).ne'))]
  apply congrArg (fun s : Set Sphere => sᶜ)
  let a (x : ℝ) := slitR p * (x + 2) - 2
  have hm : Monotone a := fun x y h =>
    sub_le_sub_right (mul_le_mul_of_nonneg_left (add_le_add h (le_refl 2)) (slitR_pos hp).le) 2
  have hc : Continuous a := by dsimp [a]; fun_prop
  have hB : 2 < slitB p := two_lt_extremal_parameter hp hp1
  have him : a '' Icc (-2) (slitB p) = Icc (-2) 2 := by
    rw [hc.continuousOn.image_Icc_of_monotoneOn (by linarith) (hm.monotoneOn _)]
    norm_num [a, slitR_mul_slitB_add_two hp]
  unfold realSlitSegment planeDomain
  rw [← him]
  simp only [image_image]
  apply image_congr
  intro x _
  rw [slitJoukowskiAffine_coe]
  simp [a]

/-- J intertwines the normalized conformal slit map and the stated affine map at every
point of the slit disk, including the pole of J at the origin. -/
theorem slitMap_joukowski_affine {p : ℝ} {q : ℂ → ℂ} (hq : IsSlitMap p q)
    {z : ℂ} (hz : z ∈ slitDisk p) :
    joukowskiSphere (q z) = slitJoukowskiAffine p (joukowskiSphere z) := by
  by_cases hz0 : z = 0
  · simp [hz0, hq.2.1]
  have he := hq.2.2 z hz
  have hw : q z ≠ 0 := by
    intro h
    simp [h, hz0] at he
  rw [joukowskiSphere_of_ne_zero hw, joukowskiSphere_of_ne_zero hz0, slitJoukowskiAffine_coe,
    OnePoint.coe_eq_coe]
  field_simp [hz0, hw]
  linear_combination he

/-- The inverse branch taking values inside the unit disk. -/
def joukowskiDiskInverse : Sphere → ℂ := Function.invFunOn joukowskiSphere disk

theorem joukowskiDiskInverse_invOn :
    InvOn joukowskiDiskInverse joukowskiSphere disk (realSlitSegment (-2) 2)ᶜ :=
  joukowskiSphere_bijOn_disk.invOn_invFunOn

@[simp] theorem joukowskiDiskInverse_infty : joukowskiDiskInverse OnePoint.infty = 0 := by
  simpa using joukowskiDiskInverse_invOn.1 (show (0 : ℂ) ∈ disk by simp [disk])

/-- The paper's specific inverse-branch construction. -/
def joukowskiSlitMap (p : ℝ) : ℂ → ℂ :=
  joukowskiDiskInverse ∘ slitJoukowskiAffine p ∘ joukowskiSphere

@[simp] theorem joukowskiSlitMap_zero (p : ℝ) : joukowskiSlitMap p 0 = 0 := by
  simp [joukowskiSlitMap]

theorem slitMap_eqOn_joukowskiSlitMap {p : ℝ} {q : ℂ → ℂ} (hq : IsSlitMap p q) :
    EqOn q (joukowskiSlitMap p) (slitDisk p) := by
  intro z hz
  unfold joukowskiSlitMap
  simp only [Function.comp_apply, ← slitMap_joukowski_affine hq hz]
  exact (joukowskiDiskInverse_invOn.1 (hq.1.2.choose_spec.2.1 hz)).symm

private theorem isOpen_slitDisk (p : ℝ) : IsOpen (slitDisk p) := by
  have he : slitDisk p = disk \ (Complex.ofReal '' Icc p 1) := by
    ext z
    constructor
    · rintro ⟨hz, hs⟩
      refine ⟨hz, ?_⟩
      rintro ⟨x, hx, rfl⟩
      have hx1 : x ≠ 1 := by rintro rfl; simp [disk] at hz
      exact hs ⟨x, ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩, rfl⟩
    · exact fun ⟨hz, hs⟩ => ⟨hz, fun h => hs (image_mono Ico_subset_Icc_self h)⟩
  rw [he]
  exact isOpen_ball.sdiff (isCompact_Icc.image Complex.continuous_ofReal).isClosed

/-- The actual composite is a biholomorphism onto the disk with the prescribed
normalization and cleared functional equation. -/
theorem joukowskiSlitMap_isSlitMap {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    IsSlitMap p (joukowskiSlitMap p) := by
  obtain ⟨q, hq⟩ := exists_isSlitMap hp hp1
  have he := slitMap_eqOn_joukowskiSlitMap hq
  obtain ⟨χ, hχ, hm, hn, hl, hr⟩ := hq.1.2
  refine ⟨⟨hq.1.1.congr (isOpen_slitDisk p) he, χ, hχ, ?_, hn, ?_, ?_⟩,
    joukowskiSlitMap_zero p, ?_⟩
  · exact fun z hz => he hz ▸ hm hz
  · intro z hz
    rw [← he hz]
    exact hl hz
  · intro w hw
    rw [← he (hn hw)]
    exact hr hw
  · intro z hz
    rw [← he hz]
    exact hq.2.2 z hz

/-- The shifted Joukowski identity as an equality on the sphere, including z = 0. -/
theorem slitMap_joukowski_sub_two_sphere {p : ℝ} {q : ℂ → ℂ} (hp : 0 < p)
    (hq : IsSlitMap p q) {z : ℂ} (hz : z ∈ slitDisk p) :
    OnePoint.map (fun w : ℂ => w - 2) (joukowskiSphere (q z)) =
      OnePoint.map (fun v : ℂ => (slitR p : ℂ) * (v - (slitB p : ℂ))) (joukowskiSphere z) := by
  rw [slitMap_joukowski_affine hq hz]
  generalize joukowskiSphere z = v
  induction v using OnePoint.rec with
  | infty => rfl
  | coe v =>
    rw [slitJoukowskiAffine_coe]
    apply congrArg OnePoint.some
    have h : (slitR p : ℂ) * ((slitB p : ℂ) + 2) = 4 := by
      exact_mod_cast slitR_mul_slitB_add_two hp
    linear_combination h

theorem slitMap_joukowski_sub_two {p : ℝ} {q : ℂ → ℂ} (hp : 0 < p)
    (hq : IsSlitMap p q) {z : ℂ} (hz : z ∈ slitDisk p) (hz0 : z ≠ 0) :
    q z + 1 / q z - 2 = (slitR p : ℂ) * (z + 1 / z - (slitB p : ℂ)) := by
  have hw : q z ≠ 0 := by
    intro he
    simpa [he, hz0] using hq.2.2 z hz
  have h := slitMap_joukowski_sub_two_sphere hp hq hz
  rw [joukowskiSphere_of_ne_zero hz0, joukowskiSphere_of_ne_zero hw] at h
  exact OnePoint.coe_injective h

/-- The intermediate reciprocal 1/(J(w)-2) equals the summed Koebe series
everywhere in the disk, with value zero when w = 0. -/
theorem joukowski_reciprocal_two_hasSum {w : ℂ} (hw : w ∈ disk) :
    HasSum (fun k : ℕ => (k : ℂ) * w ^ k) (w / (1 - w)^2) ∧
    moveOmitted ((2 : ℂ) : Sphere) (joukowskiSphere w) = ((w / (1 - w)^2 : ℂ) : Sphere) := by
  have hw1 : 1 - w ≠ 0 := by
    intro h
    have hn := mem_ball_zero_iff.mp hw
    rw [← sub_eq_zero.mp h] at hn
    simp at hn
  refine ⟨?_, ?_⟩
  · simpa [Nat.descFactorial_one] using
      hasSum_descFactorial_mul_geometric_of_norm_lt_one 1 (mem_ball_zero_iff.mp hw)
  · have he := congrFun (extremal_eq_reciprocal_joukowski (p := 1) one_ne_zero) w
    norm_num [slitB, Function.comp_apply] at he
    rw [← he]
    simp [extremal, hw1, pow_two]

/-- The scaled Koebe sum, the quadratic quotient, and the spherical extremal
all agree on the entire slit disk. -/
theorem slitMap_rational_majorant {p : ℝ} {q : ℂ → ℂ} (hp : 0 < p)
    (hq : IsSlitMap p q) {z : ℂ} (hz : z ∈ slitDisk p) :
    let d := 1 - (slitB p : ℂ) * z + z^2
    d ≠ 0 ∧ (slitR p : ℂ) * (q z / (1 - q z)^2) = z / d ∧
      HasSum (fun k : ℕ => (slitR p : ℂ) * k * q z ^ k) (z / d) ∧
      extremal p z = ((z / d : ℂ) : Sphere) := by
  let d := 1 - (slitB p : ℂ) * z + z^2
  have hw := hq.1.2.choose_spec.2.1 hz
  have hw1 : 1 - q z ≠ 0 := by
    intro h
    have hn := mem_ball_zero_iff.mp hw
    rw [← sub_eq_zero.mp h] at hn
    simp at hn
  have hR : (slitR p : ℂ) * ((slitB p : ℂ) + 2) = 4 := by
    exact_mod_cast slitR_mul_slitB_add_two hp
  have he : (slitR p : ℂ) * q z * d = z * (1 - q z)^2 := by
    dsimp [d]
    linear_combination -(hq.2.2 z hz) - z * q z * hR
  have hd : d ≠ 0 := by
    intro h
    rw [h, mul_zero] at he
    have hz0 := (mul_eq_zero.mp he.symm).resolve_right (pow_ne_zero 2 hw1)
    simp [d, hz0] at h
  have hval : (slitR p : ℂ) * (q z / (1-q z)^2) = z / d := by
    rw [← mul_div_assoc]
    exact (div_eq_div_iff (pow_ne_zero _ hw1) hd).2 he
  refine ⟨hd, hval, ?_, ?_⟩
  · rw [← hval]
    simpa only [mul_assoc] using (joukowski_reciprocal_two_hasSum hw).1.mul_left (slitR p : ℂ)
  · unfold d at hd
    simp only [extremal, extremal_den_eq_quadratic hp.ne', ite_eq_right hd]

/-- In the spherical image the omitted endpoints are strictly ordered and negative.
The pole belongs to the disk and hence infinity belongs to the image. -/
theorem extremal_joukowski_image {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    let B := slitB p
    2 < B ∧ -1 / (B-2) < -1 / (B+2) ∧ -1 / (B+2) < 0 ∧
    extremal p '' disk = (realSlitSegment (-1 / (B-2)) (-1 / (B+2)))ᶜ ∧
    extremal p 0 = (0 : ℂ) ∧ extremal p p = OnePoint.infty ∧
    OnePoint.infty ∈ extremal p '' disk := by
  have hB : 2 < slitB p := two_lt_extremal_parameter hp hp1
  have hM := isM_extremal hp hp1
  have hpD : (p : ℂ) ∈ disk := mem_ball_zero_iff.mpr ((Complex.norm_of_nonneg hp.le).trans_lt hp1)
  refine ⟨hB, ?_, div_neg_of_neg_of_pos (by norm_num) (by linarith),
    extremal_image_disk hp hp1, hM.2.2.2.2.1, hM.2.2.1, ⟨p, hpD, hM.2.2.1⟩⟩
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  linarith

/-- info: 'Goodman.joukowskiSphere_bijOn_disk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms joukowskiSphere_bijOn_disk

/-- info: 'Goodman.joukowskiReal_strictAnti' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms joukowskiReal_strictAnti

/-- info: 'Goodman.joukowskiSphere_image_radius' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms joukowskiSphere_image_radius

/-- info: 'Goodman.joukowskiSphere_image_slitDisk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms joukowskiSphere_image_slitDisk

/-- info: 'Goodman.slitJoukowskiAffine_endpoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slitJoukowskiAffine_endpoints

/-- info: 'Goodman.slitJoukowskiAffine_image_compl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slitJoukowskiAffine_image_compl

/-- info: 'Goodman.slitMap_eqOn_joukowskiSlitMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slitMap_eqOn_joukowskiSlitMap

/-- info: 'Goodman.joukowskiSlitMap_isSlitMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms joukowskiSlitMap_isSlitMap

/-- info: 'Goodman.slitMap_joukowski_sub_two_sphere' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slitMap_joukowski_sub_two_sphere

/-- info: 'Goodman.slitMap_rational_majorant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slitMap_rational_majorant

/-- info: 'Goodman.extremal_eq_reciprocal_joukowski' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms extremal_eq_reciprocal_joukowski

/-- info: 'Goodman.extremal_joukowski_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms extremal_joukowski_image

end Goodman
