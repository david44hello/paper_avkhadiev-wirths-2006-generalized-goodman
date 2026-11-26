-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Goodman.TargetNormalize

noncomputable section
open Set Filter Metric
open scoped Topology

namespace Goodman

/-- On open plane sets the set-theoretic inverse of an analytic bijection is analytic.
The open mapping theorem gives continuity, and isolated critical points are removable
for the inverse. -/
theorem analyticOnNhd_invFunOn_of_bijOn {s t : Set ℂ} {f : ℂ → ℂ}
    (hs : IsOpen s) (ht : IsOpen t) (hf : AnalyticOnNhd ℂ f s) (hb : BijOn f s t) :
    AnalyticOnNhd ℂ (Function.invFunOn f s) t := by
  let g := Function.invFunOn f s
  obtain ⟨hl, hr⟩ := hb.invOn_invFunOn
  have hm : MapsTo g t s := hb.surjOn.mapsTo_invFunOn
  have hnc {x : ℂ} (hx : x ∈ s) : ¬ ∀ᶠ z in 𝓝 x, f z = f x := by
    intro h
    have he : ∀ᶠ z in 𝓝 x, z = x := by
      filter_upwards [h, hs.mem_nhds hx] with z he hz using hb.injOn hz hx he
    obtain ⟨z, hzx, hne⟩ := ((he.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : ∀ᶠ z in 𝓝[≠] x, z ∈ ({x}ᶜ : Set ℂ))).exists
    exact hne hzx
  have hc {y : ℂ} (hy : y ∈ t) : ContinuousAt g y := by
    have hx := hm hy
    have hopen := ((hf _ hx).eventually_constant_or_nhds_le_map_nhds).resolve_left (hnc hx)
    rw [hr hy] at hopen
    apply Tendsto.mono_left _ hopen
    apply tendsto_map'_iff.2
    exact tendsto_id.congr' (hl.eqOn.eventuallyEq_of_mem (hs.mem_nhds hx)).symm
  intro y hy
  have hx := hm hy
  have hreg : ∀ᶠ z in 𝓝[≠] (g y), deriv f z ≠ 0 := by
    apply ((hf _ hx).deriv.eventually_eq_zero_or_eventually_ne_zero).resolve_left
    intro hzero
    obtain ⟨r, hpos, hball⟩ := Metric.mem_nhds_iff.mp (hzero.and (hs.mem_nhds hx))
    have hsub : ball (g y) r ⊆ s := fun z hz => (hball hz).2
    apply hnc hx
    filter_upwards [ball_mem_nhds (g y) hpos] with z hz
    exact isOpen_ball.is_const_of_deriv_eq_zero (convex_ball _ _).isPreconnected
      (hf.differentiableOn.mono hsub) (fun _ hz => (hball hz).1) hz (mem_ball_self hpos)
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt _ (hc hy)
  apply eventually_nhdsWithin_iff.2
  filter_upwards [(hc hy).tendsto.eventually (eventually_nhdsWithin_iff.1 hreg),
    ht.mem_nhds hy] with v hder hv hne
  have hgv : g v ≠ g y := fun he => hne ((hr hv).symm.trans ((congrArg f he).trans (hr hy)))
  exact (HasDerivAt.of_local_left_inverse (hc hv) (hf _ (hm hv)).differentiableAt.hasDerivAt
    (hder hgv) (hr.eqOn.eventuallyEq_of_mem (ht.mem_nhds hv))).differentiableAt

/-- A centered holomorphic bijection of the disk is a rotation. -/
theorem IsSchwarz.isRotation_of_bijOn {f : ℂ → ℂ} (hf : IsSchwarz f) (hb : BijOn f disk disk) :
    IsRotation f := by
  let g := Function.invFunOn f disk
  have h0 : (0 : ℂ) ∈ disk := mem_ball_self zero_lt_one
  have hl := hb.invOn_invFunOn.1
  have hg : IsSchwarz g := ⟨analyticOnNhd_invFunOn_of_bijOn isOpen_ball isOpen_ball hf.1 hb,
    hb.surjOn.mapsTo_invFunOn, by simpa [hf.2.2] using hl h0⟩
  have hd := (hg.1 0 h0).differentiableAt.hasDerivAt.comp_of_eq 0
    (hf.1 0 h0).differentiableAt.hasDerivAt hf.2.2.symm
  have he : g ∘ f =ᶠ[𝓝 0] id := hl.eqOn.eventuallyEq_of_mem (isOpen_ball.mem_nhds h0)
  have hnorm := congrArg norm (hd.deriv.symm.trans (he.deriv_eq.trans (deriv_id _)))
  rw [norm_mul, norm_one] at hnorm
  apply hf.norm_deriv_eq_one_iff_isRotation.mp
  refine le_antisymm hf.norm_deriv_le_one ?_
  calc
    1 = ‖deriv g 0‖ * ‖deriv f 0‖ := hnorm.symm
    _ ≤ 1 * ‖deriv f 0‖ := mul_le_mul_of_nonneg_right hg.norm_deriv_le_one (norm_nonneg _)
    _ = _ := one_mul _

theorem IsRotation.bijOn_disk {f : ℂ → ℂ} (hf : IsRotation f) : BijOn f disk disk := by
  obtain ⟨a, ha, he⟩ := hf
  have ha0 : a ≠ 0 := norm_ne_zero_iff.mp (ha ▸ one_ne_zero)
  apply BijOn.congr _ he.symm
  refine ⟨?_, fun _ _ _ _ h => mul_left_cancel₀ ha0 h, ?_⟩
  · intro z hz
    simpa [disk, mem_ball_zero_iff, norm_mul, ha] using (mem_ball_zero_iff.mp hz : ‖z‖ < 1)
  · intro z hz
    refine ⟨z/a, mem_ball_zero_iff.mpr ?_, mul_div_cancel₀ z ha0⟩
    simpa [norm_div, ha] using (mem_ball_zero_iff.mp hz : ‖z‖ < 1)

end Goodman
