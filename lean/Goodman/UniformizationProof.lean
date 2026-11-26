-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
module

public import Goodman.MobiusSphere
public import Goodman.PlanarUniformization
public import Goodman.SharpModels

@[expose] public section

noncomputable section
open Set Filter Topology Metric

namespace Goodman

/-- Carry the topology of the target to its affine coordinate. A second omitted point
keeps the image proper, even when the original target contains infinity. -/
theorem isSource_omitted_preimage {U : Set Sphere} (hU : IsTarget U)
    {p q : Sphere} (hp : p ∉ U) (hq : q ∉ U) (hqp : q ≠ p) :
    IsSource (omittedParam p ⁻¹' U) := by
  have he := isOpenEmbedding_omittedParam p
  refine ⟨hU.1.preimage he.continuous, ?_, ?_⟩
  · have hsub : U ⊆ range (omittedParam p) := by
      rw [omittedParam_range]
      intro x hx hxp
      exact hp ((show x = p from hxp) ▸ hx)
    apply he.isEmbedding.isSimplyConnected_image.mp
    rw [image_preimage_eq_iff.mpr hsub]
    exact hU.2.1
  · apply (ne_univ_iff_exists_notMem _).mpr
    refine ⟨omittedCoord p q, ?_⟩
    change omittedParam p (omittedCoord p q) ∉ U
    rwa [omittedParam_coord hqp]

private theorem disk_neg_mem {z : ℂ} (hz : z ∈ disk) : -z ∈ disk := by
  simpa [disk, mem_ball_zero_iff] using hz

private theorem diskInverse_denom {a z : ℂ} (ha : a ∈ disk) (hz : z ∈ disk) :
    1 - star a * z ≠ 0 := by
  have h : ‖star a * z‖ < 1 := by
    rw [norm_mul, norm_star]
    calc
      ‖a‖ * ‖z‖ ≤ ‖a‖ * 1 := mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp hz).le (norm_nonneg _)
      _ < 1 := by simpa using mem_ball_zero_iff.mp ha
  intro he
  rw [← sub_eq_zero.mp he, norm_one] at h
  exact lt_irrefl _ h

/-- The conjugate-center fractional linear transformation preserves the open unit disk. -/
theorem diskInverse_maps_disk {a : ℂ} (ha : a ∈ disk) : MapsTo (diskInverse a) disk disk := by
  intro z hz
  have ha' := mem_ball_zero_iff.mp ha
  have hz' := mem_ball_zero_iff.mp hz
  have h : Complex.normSq (1 - star a * z) - Complex.normSq (z - a) =
      (1 - Complex.normSq a) * (1 - Complex.normSq z) := by
    simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
    ring
  have hs (x : ℂ) (hx : ‖x‖ < 1) : 0 < 1 - Complex.normSq x := by
    rw [Complex.normSq_eq_norm_sq]
    exact sub_pos.mpr (by simpa using (sq_lt_sq₀ (norm_nonneg x) zero_le_one).2 hx)
  have hpos := mul_pos (hs a ha') (hs z hz')
  rw [← h, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hpos
  rw [disk, mem_ball_zero_iff, diskInverse, norm_div, div_lt_one₀ (norm_pos_iff.mpr
    (diskInverse_denom ha hz))]
  exact (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (sub_pos.mp hpos)

private theorem diskInverse_undo {a z : ℂ} (ha : a ∈ disk) (hz : z ∈ disk) :
    diskInverse (-a) (diskInverse a z) = z := by
  let y := diskInverse a z
  have hy : y * (1 - star a * z) = z - a :=
    div_mul_cancel₀ _ (diskInverse_denom ha hz)
  change (y - -a) / (1 - star (-a) * y) = z
  apply (div_eq_iff (diskInverse_denom (disk_neg_mem ha) (diskInverse_maps_disk ha hz))).2
  rw [star_neg]
  linear_combination hy

theorem diskInverse_bihol {a : ℂ} (ha : a ∈ disk) : Bihol disk disk (diskInverse a) := by
  have analytic {c : ℂ} (hc : c ∈ disk) : AnalyticOnNhd ℂ (diskInverse c) disk := fun z hz =>
    (analyticAt_id.sub analyticAt_const).div
      (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)) (diskInverse_denom hc hz)
  refine ⟨analytic ha, diskInverse (-a), analytic (disk_neg_mem ha), diskInverse_maps_disk ha,
    diskInverse_maps_disk (disk_neg_mem ha), fun _ hz => diskInverse_undo ha hz, fun _ hz => ?_⟩
  simpa using diskInverse_undo (disk_neg_mem ha) hz

/-- Center the planar Riemann map at any prescribed point of its image. -/
theorem exists_centered_planar_bihol (hR : PlanarRiemannMapping) {Ω : Set ℂ}
    (hΩ : IsSource Ω) {y : ℂ} (hy : y ∈ Ω) :
    ∃ f : ℂ → ℂ, Bihol disk Ω f ∧ f 0 = y := by
  obtain ⟨φ, hφ, χ, hχ, hmφ, hmχ, hl, hr⟩ := hR Ω hΩ.1 hΩ.2.1 hΩ.2.2
  let a := χ y
  have ha : a ∈ disk := hmχ hy
  let b := diskInverse (-a)
  let c := diskInverse a
  obtain ⟨hb, _, _, hbm, _, _, _⟩ := diskInverse_bihol (disk_neg_mem ha)
  obtain ⟨hc, _, _, hcm, _, _, _⟩ := diskInverse_bihol ha
  refine ⟨φ ∘ b, ⟨fun z hz => (hφ _ (hbm hz)).comp (hb z hz), c ∘ χ,
    fun z hz => (hc _ (hmχ hz)).comp (hχ z hz), hmφ.comp hbm, hcm.comp hmχ, ?_, ?_⟩, ?_⟩
  · intro z hz
    change c (χ (φ (b z))) = z
    rw [hl (hbm hz)]
    simpa [c, b] using diskInverse_undo (disk_neg_mem ha) hz
  · intro z hz
    change φ (b (c (χ z))) = z
    rw [show b (c (χ z)) = χ z from diskInverse_undo ha (hmχ hz), hr hz]
  · change φ (diskInverse (-a) 0) = y
    simpa [diskInverse, a] using hr hy

/-- Transport a given centered planar biholomorphism to a spherical chart. -/
def centeredChartOfOmittedBihol {U : Set Sphere} {p : Sphere} (hp : p ∉ U)
    {w : ℂ} (hw : (w : Sphere) ∈ U) {f : ℂ → ℂ}
    (hB : Bihol disk (omittedParam p ⁻¹' U) f) (hcenter : f 0 = omittedCoord p w) :
    CenteredChart U w := by
  let Ω := omittedParam p ⁻¹' U
  let g := hB.2.choose
  have hg_spec : AnalyticOnNhd ℂ g Ω ∧ MapsTo f disk Ω ∧ MapsTo g Ω disk ∧
      LeftInvOn g f disk ∧ LeftInvOn f g Ω := hB.2.choose_spec
  obtain ⟨hg, hfm, hgm, hleft, hright⟩ := hg_spec
  have avoid {v : Sphere} (hv : v ∈ U) : v ≠ p := fun h => hp (h ▸ hv)
  have hcoord {v : Sphere} (hv : v ∈ U) : omittedCoord p v ∈ Ω := by
    change omittedParam p (omittedCoord p v) ∈ U
    rwa [omittedParam_coord (avoid hv)]
  refine {
    forward := omittedParam p ∘ f
    inverse := g ∘ omittedCoord p
    forward_holo := omittedParam_comp_holomorphic p hB.1
    inverse_holo := ?_
    forward_maps := fun _ hz => hfm hz
    inverse_maps := fun _ hv => hgm (hcoord hv)
    left_inverse := ?_
    right_inverse := ?_
    center := ?_ }
  · constructor
    · intro z hz
      exact (hg _ (hcoord hz)).comp (f := fun t : ℂ => omittedCoord p (t : Sphere))
        ((omittedCoord_holomorphic p).1 z (avoid hz))
    · intro hinfty
      exact (hg _ (hcoord hinfty)).comp_of_eq (f := omittedCoord p ∘ fromRecip)
        ((omittedCoord_holomorphic p).2 (avoid hinfty)) (by simp [Function.comp_apply, fromRecip])
  · intro z hz
    change g (omittedCoord p (omittedParam p (f z))) = z
    rw [omittedCoord_param, hleft hz]
  · intro v hv
    change omittedParam p (f (g (omittedCoord p v))) = v
    rw [hright (hcoord hv), omittedParam_coord (avoid hv)]
  · change omittedParam p (f 0) = (w : Sphere)
    rw [hcenter, omittedParam_coord (avoid hw)]

/-- Planar Riemann mapping in any specified omitted-point coordinate. -/
theorem nonempty_centeredChart_of_omitted_points (hR : PlanarRiemannMapping) {U : Set Sphere}
    (hU : IsTarget U) {p q : Sphere} (hp : p ∉ U) (hq : q ∉ U) (hqp : q ≠ p)
    {w : ℂ} (hw : (w : Sphere) ∈ U) : Nonempty (CenteredChart U w) := by
  have hΩ := isSource_omitted_preimage hU hp hq hqp
  have hy : omittedCoord p w ∈ omittedParam p ⁻¹' U := by
    change omittedParam p (omittedCoord p w) ∈ U
    rwa [omittedParam_coord (ne_of_mem_of_not_mem hw hp)]
  obtain ⟨f, hf, hcenter⟩ := exists_centered_planar_bihol hR hΩ hy
  exact ⟨centeredChartOfOmittedBihol hp hw hf hcenter⟩

/-- Use the ordinary affine chart whenever infinity is omitted. If the domain contains
infinity, move one of its omitted finite points to infinity. -/
theorem riemannMapping_of_planarRiemannMapping (hR : PlanarRiemannMapping) : RiemannMapping := by
  intro U hU w hw
  obtain ⟨p, q, hp, hq, hpq⟩ := hU.2.2
  by_cases hinfty : OnePoint.infty ∈ U
  · exact nonempty_centeredChart_of_omitted_points hR hU hp hq hpq.symm hw
  · by_cases he : p = OnePoint.infty
    · subst p
      exact nonempty_centeredChart_of_omitted_points hR hU hinfty hq hpq.symm hw
    · exact nonempty_centeredChart_of_omitted_points hR hU hinfty hp he hw

/--
info: 'Goodman.riemannMapping_of_planarRiemannMapping' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms riemannMapping_of_planarRiemannMapping

end Goodman
