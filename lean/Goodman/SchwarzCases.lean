-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Goodman.CoefficientClaims

noncomputable section
open Set Filter
open scoped Topology

namespace Goodman

private theorem origin_mem_disk : (0 : ℂ) ∈ disk :=
  Metric.mem_ball_self zero_lt_one

private theorem disk_nhds_origin : disk ∈ 𝓝 (0 : ℂ) :=
  Metric.ball_mem_nhds _ zero_lt_one

private theorem IsSchwarz.mapsTo_closedBall {h : ℂ → ℂ} (hh : IsSchwarz h) :
    MapsTo h disk (Metric.closedBall (h 0) 1) := by
  rw [hh.2.2]
  exact hh.2.1.mono_right Metric.ball_subset_closedBall

theorem IsSchwarz.norm_deriv_le_one {h : ℂ → ℂ} (hh : IsSchwarz h) :
    ‖deriv h 0‖ ≤ 1 :=
  Complex.norm_deriv_le_one_of_mapsTo_ball hh.1.differentiableOn hh.mapsTo_closedBall zero_lt_one

theorem IsSchwarz.norm_deriv_eq_one_iff_isRotation {h : ℂ → ℂ} (hh : IsSchwarz h) :
    ‖deriv h 0‖ = 1 ↔ IsRotation h := by
  constructor
  · intro heq
    refine ⟨deriv h 0, heq, ?_⟩
    have hlin := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div
      hh.1.differentiableOn hh.mapsTo_closedBall origin_mem_disk (by simpa using heq)
    intro z hz
    simpa [hh.2.2, smul_eq_mul, mul_comm] using hlin hz
  · rintro ⟨a, ha, hlin⟩
    rwa [(hlin.eventuallyEq_of_mem disk_nhds_origin).deriv_eq, deriv_const_mul_id]

/-- Precomposition by multiplication scales the actual iterated-derivative coefficient. -/
theorem coeff_comp_mul_left (g : ℂ → ℂ) (a : ℂ) (n : ℕ) :
    coeff n (fun z => g (a * z)) = a ^ n * coeff n g := by
  have scale (k : ℕ) :
      iteratedDeriv k (fun z => g (a * z)) = fun z => a ^ k * iteratedDeriv k g (a * z) := by
    induction k with
    | zero => simp
    | succ k ih =>
      funext z
      rw [iteratedDeriv_succ, ih, deriv_const_mul_field, deriv_comp_mul_left, iteratedDeriv_succ]
      simp only [smul_eq_mul, pow_succ, mul_assoc]
  simp [coeff, scale, mul_div_assoc]

/-- A rotation on the disk preserves every coefficient modulus of an analytic germ at zero.
The derivative identity also holds for the totalized coefficient operator on arbitrary functions. -/
theorem IsRotation.norm_coeff_comp {h : ℂ → ℂ} (hh : IsRotation h) (g : ℂ → ℂ) (n : ℕ) :
    ‖coeff n (fun z => g (h z))‖ = ‖coeff n g‖ := by
  obtain ⟨a, ha, hlin⟩ := hh
  have heq : (fun z => g (h z)) =ᶠ[𝓝 (0 : ℂ)] (fun z => g (a * z)) :=
    (hlin.comp_left (g := g)).eventuallyEq_of_mem disk_nhds_origin
  have hc : coeff n (fun z => g (h z)) = coeff n (fun z => g (a * z)) := by
    unfold coeff
    rw [heq.iteratedDeriv_eq n]
  rw [hc, coeff_comp_mul_left, norm_mul, norm_pow, ha, one_pow, one_mul]

/-- At a finite center both sphere charts give an analytic affine coordinate on a neighborhood. -/
private theorem IsM.finite_germ_at {p : ℝ} {f : ℂ → Sphere} {x : ℂ}
    (hf : IsM p f) (hx : x ∈ disk) (hfin : f x ≠ OnePoint.infty) :
    AnalyticAt ℂ (finitePart ∘ f) x ∧ ∀ᶠ z in 𝓝 x, f z = (finitePart (f z) : Sphere) := by
  obtain ⟨g, hg, hchart⟩ := hf.1 x hx
  have affine : ∃ u : ℂ → ℂ, AnalyticAt ℂ u x ∧ ∀ᶠ z in 𝓝 x, f z = (u z : Sphere) := by
    rcases hchart with h | h
    · exact ⟨g, hg, h⟩
    · have hne : g x ≠ 0 := by
        intro hzero
        exact hfin (by simpa [fromRecip, hzero] using h.self_of_nhds)
      refine ⟨fun z => (g z)⁻¹, hg.inv hne, ?_⟩
      filter_upwards [h, hg.continuousAt.eventually_ne hne] with z hz hn
      simpa [fromRecip, hn] using hz
  obtain ⟨u, hu, heq⟩ := affine
  constructor
  · apply hu.congr
    filter_upwards [heq] with z hz
    exact (congrArg finitePart hz).symm
  · filter_upwards [heq] with z hz
    rw [hz]
    rfl

theorem IsM.finite_germ_zero {p : ℝ} {f : ℂ → Sphere} (hf : IsM p f) :
    AnalyticAt ℂ (finitePart ∘ f) 0 ∧ ∀ᶠ z in 𝓝 (0 : ℂ), f z = (finitePart (f z) : Sphere) :=
  hf.finite_germ_at origin_mem_disk (by rw [hf.2.2.2.2.1]; exact OnePoint.coe_ne_infty _)

theorem IsM.hasDerivAt_zero {p : ℝ} {f : ℂ → Sphere} (hf : IsM p f) :
    HasDerivAt (finitePart ∘ f) 1 0 := by
  rw [← hf.2.2.2.2.2]
  exact hf.finite_germ_zero.1.differentiableAt.hasDerivAt

/-- The Schwarz estimate keeps the composition away from the unique pole throughout
the disk of radius `p`, so its affine coordinate is analytic there. -/
theorem IsM.finite_comp_of_norm_lt {p : ℝ} {f : ℂ → Sphere} (hf : IsM p f)
    (hp : 0 < p) (hp1 : p < 1) {h : ℂ → ℂ} (hh : IsSchwarz h) {z : ℂ} (hz : ‖z‖ < p) :
    f (h z) ≠ OnePoint.infty ∧ AnalyticAt ℂ (fun w => finitePart (f (h w))) z := by
  have hz1 : z ∈ disk := mem_ball_zero_iff.mpr (hz.trans hp1)
  have hpd : (p : ℂ) ∈ disk :=
    mem_ball_zero_iff.mpr ((Complex.norm_of_nonneg hp.le).trans_lt hp1)
  have hnorm := Complex.norm_le_norm_of_mapsTo_ball hh.1.differentiableOn
    (hh.2.1.mono_right Metric.ball_subset_closedBall) hh.2.2 (hz.trans hp1)
  have hfin : f (h z) ≠ OnePoint.infty := by
    intro hinf
    have heq := hf.2.1 (hh.2.1 hz1) hpd (hinf.trans hf.2.2.1.symm)
    have hlt := hnorm.trans_lt hz
    rw [heq, Complex.norm_of_nonneg hp.le] at hlt
    exact lt_irrefl p hlt
  exact ⟨hfin, (hf.finite_germ_at (hh.2.1 hz1) hfin).1.comp (hh.1 z hz1)⟩

theorem IsM.coeff_one_comp {p : ℝ} {f : ℂ → Sphere} (hf : IsM p f)
    {h : ℂ → ℂ} (hh : IsSchwarz h) :
    coeff 1 (fun z => finitePart (f (h z))) = deriv h 0 := by
  have hd := hf.hasDerivAt_zero.comp_of_eq 0
    (hh.1 0 origin_mem_disk).differentiableAt.hasDerivAt hh.2.2.symm
  simpa [coeff, Function.comp_def] using hd.deriv

theorem equalityFirst : EqualityFirst := by
  intro p _ _ f hf h hh
  simpa [hf.coeff_one_comp hh, A] using hh.norm_deriv_eq_one_iff_isRotation

end Goodman
