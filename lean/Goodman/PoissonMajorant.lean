-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Goodman.Transfer
import Goodman.SchwarzCases

/-!
# The Poisson majorant in Lemma 4

The Poisson integral of the boundary modulus dominates the polynomial in the disk.
It is the real part of the analytic Herglotz–Riesz integral, so its pullback by a
Schwarz map satisfies the harmonic mean value identity. All arc means are normalized.
-/

noncomputable section

open Complex Filter InnerProductSpace Metric Set
open scoped Polynomial Topology

namespace Goodman

/-- The Poisson integral of the boundary values of the modulus of a polynomial. -/
def poissonMajorant (P : ℂ[X]) (w : ℂ) : ℝ :=
  Real.circleAverage (poissonKernel 0 w • fun ζ => ‖P.eval ζ‖) 0 1

/-- The sub-mean inequality for the modulus of a polynomial on every circle. -/
theorem polynomial_norm_submean (P : ℂ[X]) (c : ℂ) (r : ℝ) :
    ‖P.eval c‖ ≤ Real.circleAverage (fun z => ‖P.eval z‖) c r := by
  have hav : Real.circleAverage (fun z => P.eval z) c r = P.eval c :=
    P.differentiable.differentiableOn.diffContOnCl.circleAverage
  exact (congrArg norm hav).ge.trans Real.norm_circleAverage_le_circleAverage_norm

/-- The positive Poisson kernel reproduces the polynomial and majorizes its modulus. -/
theorem transfer_poisson (P : ℂ[X]) {w : ℂ} (hw : w ∈ disk) :
    ‖P.eval w‖ ≤ poissonMajorant P w := by
  have hav := P.differentiable.differentiableOn.diffContOnCl.circleAverage_poissonKernel_smul hw
  refine (congrArg norm hav).ge.trans (Real.norm_circleAverage_le_circleAverage_norm.trans ?_)
  apply le_of_eq
  apply Real.circleAverage_congr_sphere
  intro ζ hζ
  have hnorm : ‖ζ‖ = 1 := by simpa using mem_sphere_zero_iff_norm.mp hζ
  have hpos : 0 ≤ poissonKernel 0 w ζ := by
    simp only [poissonKernel_def, sub_zero, hnorm, one_pow]
    exact div_nonneg (sub_nonneg.mpr (pow_le_one₀ (norm_nonneg _) (mem_ball_zero_iff.mp hw).le))
      (sq_nonneg _)
  simp [abs_of_nonneg hpos]

/-- The Poisson integral of the modulus is harmonic after composition with a Schwarz map. -/
theorem poissonMajorant_harmonic_comp (P : ℂ[X]) {h : ℂ → ℂ} (hh : IsSchwarz h) :
    HarmonicOnNhd (poissonMajorant P ∘ h) disk := by
  let F (w : ℂ) := Real.circleAverage
    (fun ζ => herglotzRieszKernel 0 w ζ • (‖P.eval ζ‖ : ℂ)) 0 1
  have hoff {w : ℂ} (hw : w ∈ disk) : w ∉ sphere 0 |(1 : ℝ)| := by
    simpa only [abs_one, mem_sphere_zero_iff_norm] using (mem_ball_zero_iff.mp hw).ne
  have hF : AnalyticOnNhd ℂ F disk :=
    (analyticOnNhd_circleAverage_herglotzRieszKernel_smul
      ((Complex.continuous_ofReal.comp P.continuous.norm).continuousOn.circleIntegrable zero_le_one)).mono
      (fun _ hw => hoff hw)
  have hRe {w : ℂ} (hw : w ∈ disk) : (F w).re = poissonMajorant P w := by
    rw [poissonMajorant, poissonKernel_eq_re_herglotzRieszKernel]
    exact re_circleAverage_herglotzRieszKernel_smul
      (P.continuous.norm.continuousOn.circleIntegrable zero_le_one) (hoff hw)
  intro z hz
  apply (harmonicAt_congr_nhds (f₁ := fun y => (F (h y)).re) _).mp
  · exact ((hF _ (hh.2.1 hz)).comp (hh.1 z hz)).harmonicAt_re
  · filter_upwards [isOpen_ball.mem_nhds hz] with y hy using hRe (hh.2.1 hy)

/-- In particular the Poisson extension itself is harmonic throughout the unit disk. -/
theorem poissonMajorant_harmonic (P : ℂ[X]) : HarmonicOnNhd (poissonMajorant P) disk :=
  poissonMajorant_harmonic_comp P (h := id) ⟨fun _ _ => analyticAt_id, fun _ hx => hx, rfl⟩

/-- At the origin the Poisson kernel is one on the unit circle. -/
theorem poissonMajorant_zero (P : ℂ[X]) :
    poissonMajorant P 0 = Real.circleAverage (fun ζ => ‖P.eval ζ‖) 0 1 := by
  apply Real.circleAverage_congr_sphere
  intro ζ hζ
  have hnorm : ‖ζ‖ = 1 := by simpa using mem_sphere_zero_iff_norm.mp hζ
  simp [poissonKernel_def, hnorm]

private theorem radial_circleAverage (f : ℂ → ℝ) (r : ℝ) :
    Real.circleAverage (fun ζ => f ((r : ℂ) * ζ)) 0 1 = Real.circleAverage f 0 r := by
  simp [Real.circleAverage, circleMap]

/-- Mean value of the pulled-back majorant on a concentric source circle. -/
theorem transfer_mean (P : ℂ[X]) {h : ℂ → ℂ} (hh : IsSchwarz h) {r : ℝ}
    (hr : 0 ≤ r) (hr' : r < 1) :
    Real.circleAverage (fun ζ => poissonMajorant P (h ((r : ℂ) * ζ))) 0 1 =
      poissonMajorant P 0 := by
  rw [radial_circleAverage (fun z => poissonMajorant P (h z)) r]
  have hav : HarmonicOnNhd (poissonMajorant P ∘ h) (closedBall 0 |r|) :=
    (poissonMajorant_harmonic_comp P hh).mono
      (closedBall_subset_ball (by simpa [abs_of_nonneg hr] using hr'))
  simpa only [Function.comp_def, hh.2.2] using hav.circleAverage_eq

/-- The pointwise majorant also bounds the source-circle average in the printed chain. -/
theorem transfer_mean_le_majorant (P : ℂ[X]) {h : ℂ → ℂ} (hh : IsSchwarz h) {r : ℝ}
    (hr : 0 ≤ r) (hr' : r < 1) :
    Real.circleAverage (fun ζ => ‖P.eval (h ((r : ℂ) * ζ))‖) 0 1 ≤
      Real.circleAverage (fun ζ => poissonMajorant P (h ((r : ℂ) * ζ))) 0 1 := by
  rw [radial_circleAverage (fun z => ‖P.eval (h z)‖),
    radial_circleAverage (fun z => poissonMajorant P (h z)) r]
  have hs : sphere (0 : ℂ) r ⊆ disk := sphere_subset_closedBall.trans (closedBall_subset_ball hr')
  refine Real.circleAverage_mono
    ((P.continuous.comp_continuousOn (hh.1.continuousOn.mono hs)).norm.circleIntegrable hr)
    (((poissonMajorant_harmonic_comp P hh).continuousOn.mono hs).circleIntegrable hr) ?_
  intro z hz
  rw [abs_of_nonneg hr] at hz
  exact transfer_poisson P (hh.2.1 (hs hz))

/-- Cauchy's formula, with the unit-modulus phase and the contractive weight removed. -/
theorem transfer_cauchy (P : ℂ[X]) {e h : ℂ → ℂ} (he : IsWeight e) (hh : IsSchwarz h)
    (n : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr' : r < 1) :
    r^n * ‖coeff n (fun z => e z * P.eval (h z))‖ ≤
      Real.circleAverage (fun ζ => ‖P.eval (h ((r : ℂ) * ζ))‖) 0 1 := by
  let f (z : ℂ) := e z * P.eval (h z)
  let scale (ζ : ℂ) := (r : ℂ) * ζ
  have hscale : MapsTo scale (closedBall 0 1) disk := by
    intro ζ hζ
    apply mem_ball_zero_iff.mpr
    rw [show scale ζ = (r : ℂ) * ζ from rfl, norm_mul, Complex.norm_of_nonneg hr]
    exact (mul_le_of_le_one_right hr (mem_closedBall_zero_iff.mp hζ)).trans_lt hr'
  have hf : AnalyticOnNhd ℂ f disk := fun z hz =>
    (he.1 z hz).fun_mul ((P.differentiable.analyticAt _).comp (hh.1 z hz))
  have hscaled : AnalyticOnNhd ℂ (f ∘ scale) (closedBall 0 1) :=
    fun ζ hζ => (hf _ (hscale hζ)).comp (analyticAt_const.fun_mul analyticAt_id)
  have hav := transfer_coeff_average zero_lt_one
    (hscaled.differentiableOn.diffContOnCl_ball Subset.rfl) n
  change _ = coeff n (fun z => f ((r : ℂ) * z)) at hav
  rw [coeff_comp_mul_left] at hav
  have hnorm := congrArg norm hav
  rw [norm_mul, norm_pow, Complex.norm_of_nonneg hr] at hnorm
  refine hnorm.ge.trans (Real.norm_circleAverage_le_circleAverage_norm.trans ?_)
  have hs := hscale.mono_left sphere_subset_closedBall
  have hc : ContinuousOn scale (sphere 0 1) := (continuous_const.mul continuous_id).continuousOn
  have hphase : ContinuousOn (fun ζ : ℂ => ζ⁻¹ ^ n) (sphere 0 1) :=
    (continuousOn_id.inv₀ (fun _ hz => ne_of_mem_sphere hz one_ne_zero)).pow n
  refine Real.circleAverage_mono
    ((hphase.mul (hf.continuousOn.comp hc hs)).norm.circleIntegrable zero_le_one)
    ((P.continuous.comp_continuousOn (hh.1.continuousOn.comp hc hs)).norm.circleIntegrable
      zero_le_one) ?_
  intro ζ hζ
  rw [abs_one] at hζ
  simpa [f, Function.comp_apply, norm_mul, norm_pow, norm_inv, mem_sphere_zero_iff_norm.mp hζ]
    using mul_le_of_le_one_left (norm_nonneg (P.eval (h (scale ζ)))) (he.2 _ (hs hζ))

end Goodman
