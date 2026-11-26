-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
module

public import Goodman.SchwarzCases
public import Goodman.Transfer
public import Goodman.UniformizationProof

@[expose] public section

/-!
# Boundary moments for the weighted transfer lemma

Cauchy's formula and the Poisson kernel bound the polynomial functional in the
normalized L¹ norm on each source circle after scaling by the radius to degree n.

A finite Schur interpolation of the transfer multiplier has the same prescribed jet
and is analytic on the closed disk. Dividing its circle values by the degree-`n`
phase gives a continuous representing density for normalized arc measure.
-/

noncomputable section
open Complex Filter MeasureTheory Metric Set
open scoped Polynomial Topology

namespace Goodman

private abbrev closedDisk := closedBall (0 : ℂ) 1

private theorem denom_ne {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ ≤ 1) :
    1 - star a * w ≠ 0 := by
  have h : ‖star a * w‖ < 1 := by
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_right (norm_nonneg _) hw).trans_lt ha
  intro he
  rw [← sub_eq_zero.mp he, norm_one] at h
  exact lt_irrefl _ h

private theorem diskInverse_regular {a : ℂ} (ha : ‖a‖ < 1) :
    AnalyticOnNhd ℂ (diskInverse a) closedDisk := fun _ hw =>
  (analyticAt_id.sub analyticAt_const).div (analyticAt_const.sub (analyticAt_const.mul analyticAt_id))
    (denom_ne ha (mem_closedBall_zero_iff.mp hw))

private theorem diskInverse_closed {a : ℂ} (ha : ‖a‖ < 1) :
    MapsTo (diskInverse a) closedDisk closedDisk := by
  have hc : closure disk = closedDisk := closure_ball _ one_ne_zero
  have h := (diskInverse_maps_disk (mem_ball_zero_iff.mpr ha)).closure_of_continuousOn
    (hc ▸ (diskInverse_regular ha).continuousOn : ContinuousOn _ (closure disk))
  simpa only [hc] using h

/-- Retain the Taylor jet of orders below k. A Schur step removes the value at
zero and divides by z. Its inverse restores one degree of contact. -/
private theorem regular_jet (k : ℕ) {E : ℂ → ℂ} (hE : IsWeight E) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F closedDisk ∧ MapsTo F closedDisk closedDisk ∧
      ∃ U : ℂ → ℂ, AnalyticAt ℂ U 0 ∧ ∀ᶠ z in 𝓝 0, E z - F z = z ^ k * U z := by
  have h0 : (0 : ℂ) ∈ disk := by simp [disk]
  have hnh : disk ∈ 𝓝 (0 : ℂ) := isOpen_ball.mem_nhds h0
  induction k generalizing E with
  | zero =>
    exact ⟨fun _ => 0, fun _ _ => analyticAt_const, fun _ _ => by simp [closedDisk],
      E, hE.1 _ h0, .of_forall fun _ => by simp⟩
  | succ k ih =>
    let a := E 0
    by_cases ha : ‖a‖ < 1
    · let b := diskInverse a ∘ E
      have hmap (z : ℂ) (hz : z ∈ disk) : E z ∈ closedDisk :=
        mem_closedBall_zero_iff.mpr (hE.2 z hz)
      have hb : AnalyticOnNhd ℂ b disk := fun z hz =>
        (diskInverse_regular ha _ (hmap z hz)).comp (hE.1 z hz)
      have hb0 : b 0 = 0 := by simp [b, diskInverse, a]
      let S := dslope b 0
      have hS : IsWeight S := by
        refine ⟨((Complex.differentiableOn_dslope hnh).2 hb.differentiableOn).analyticOnNhd
          isOpen_ball, fun z hz => ?_⟩
        have hm : MapsTo b disk (closedBall (b 0) 1) := by
          rw [hb0]
          exact fun w hw => diskInverse_closed ha (hmap w hw)
        simpa [S] using Complex.norm_dslope_le_div_of_mapsTo_ball hb.differentiableOn hm hz
      obtain ⟨G, hG, hGmap, U, hU, hu⟩ := ih hS
      let t (z : ℂ) := z * G z
      have ht : AnalyticOnNhd ℂ t closedDisk := fun z hz => analyticAt_id.fun_mul (hG z hz)
      have htmap : MapsTo t closedDisk closedDisk := by
        intro z hz
        apply mem_closedBall_zero_iff.mpr
        rw [show t z = z * G z from rfl, norm_mul]
        exact (mul_le_of_le_one_right (norm_nonneg _) (mem_closedBall_zero_iff.mp (hGmap hz))).trans
          (mem_closedBall_zero_iff.mp hz)
      have hna : ‖-a‖ < 1 := by simpa using ha
      let D (z : ℂ) := 1 - star (-a) * t z
      have hD (z : ℂ) (hz : z ∈ closedDisk) : D z ≠ 0 :=
        denom_ne hna (mem_closedBall_zero_iff.mp (htmap hz))
      have hc0 : (0 : ℂ) ∈ closedDisk := by simp [closedDisk]
      refine ⟨diskInverse (-a) ∘ t, fun z hz =>
        (diskInverse_regular hna _ (htmap hz)).comp (ht z hz),
        (diskInverse_closed hna).comp htmap, fun z => U z * (1 - star a * E z) / D z,
        (hU.fun_mul (analyticAt_const.fun_sub (analyticAt_const.fun_mul (hE.1 _ h0)))).fun_div
          (analyticAt_const.fun_sub (analyticAt_const.fun_mul (ht _ hc0))) (hD _ hc0), ?_⟩
      filter_upwards [hu, hnh] with z hz hzd
      have hden := hD z (ball_subset_closedBall hzd)
      have hstep : z * S z * (1 - star a * E z) = E z - a := by
        have h := sub_smul_dslope b 0 z
        simp only [sub_zero, smul_eq_mul, hb0] at h
        rw [show z * S z = b z from h]
        exact div_mul_cancel₀ _ (denom_ne ha (hE.2 z hzd))
      change E z - (t z - -a) / D z = z ^ (k+1) * (U z * (1 - star a * E z) / D z)
      field_simp [hden]
      simp only [D, t, star_neg]
      rw [pow_succ]
      linear_combination (norm := ring_nf) -hstep + z * (1 - star a * E z) * hz
    · have hn : ‖a‖ = 1 := le_antisymm (hE.2 _ h0) (le_of_not_gt ha)
      have hmax : IsMaxOn (norm ∘ E) disk 0 := isMaxOn_iff.mpr fun z hz =>
        (hE.2 z hz).trans_eq hn.symm
      have heq := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
        (convex_ball (0 : ℂ) 1).isPreconnected isOpen_ball hE.1.differentiableOn h0 hmax
      refine ⟨fun _ => a, fun _ _ => analyticAt_const, fun _ _ =>
        mem_closedBall_zero_iff.mpr hn.le, fun _ => 0, analyticAt_const, ?_⟩
      filter_upwards [hnh] with z hz
      simp [show E z = a from heq hz]

/-- Replacing a multiplier by its regular interpolant preserves its degree-n
pairing with every holomorphic germ. -/
private theorem regular_transfer {e h : ℂ → ℂ} (he : IsWeight e) (hh : IsSchwarz h) (n : ℕ) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F closedDisk ∧ MapsTo F closedDisk closedDisk ∧
      ∀ g : ℂ → ℂ, AnalyticAt ℂ g 0 →
        coeff n (fun z => e z * g (h z)) = coeff n (fun z => F z * g z) := by
  obtain ⟨E, hE, _, ht⟩ := transfer h hh e he n
  obtain ⟨F, hF, hm, U, hU, hu⟩ := regular_jet (n+1) hE
  refine ⟨F, hF, hm, fun g hg => (ht g hg).trans ?_⟩
  have ha := (hE.1 0 (by simp [disk])).fun_mul hg
  have hb := (hF 0 (by simp [closedDisk])).fun_mul hg
  have hd := ha.fun_sub hb
  have horder : (↑(n+1) : ℕ∞) ≤ analyticOrderAt (fun z => E z * g z - F z * g z) 0 := by
    apply (natCast_le_analyticOrderAt hd).mpr
    refine ⟨fun z => U z * g z, hU.fun_mul hg, ?_⟩
    filter_upwards [hu] with z hz
    simp only [sub_zero, smul_eq_mul, ← mul_assoc, ← hz, sub_mul]
  have hzero := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hd).mp horder n n.lt_succ_self
  rw [iteratedDeriv_fun_sub ha.contDiffAt hb.contDiffAt] at hzero
  simp only [coeff, sub_eq_zero.mp hzero]

open Real
local notation "𝕋" => AddCircle (2 * π)
local instance : Fact (0 < 2 * π) := ⟨two_pi_pos⟩
local notation "σ" => (AddCircle.haarAddCircle (T := 2 * π))
local notation "ζ" => (fun θ : 𝕋 => (AddCircle.toCircle θ : ℂ))

private theorem normalized_integral {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : ℂ → V) :
    (∫ θ : 𝕋, f (ζ θ) ∂σ) = Real.circleAverage f 0 1 := by
  rw [AddCircle.integral_haarAddCircle, Real.circleAverage,
    ← AddCircle.intervalIntegral_preimage (2 * π) 0]
  simp [AddCircle.toCircle, circleMap]

private theorem boundary_cauchy {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f closedDisk) (k : ℕ) :
    (∫ θ : 𝕋, (ζ θ)⁻¹ ^ k * f (ζ θ) ∂σ) = coeff k f := by
  rw [normalized_integral (fun z => z⁻¹ ^ k * f z)]
  apply transfer_coeff_average zero_lt_one
  exact DifferentiableOn.diffContOnCl (hf.differentiableOn.mono closure_ball_subset_closedBall)

/-- Cauchy's bound on the source circle and the Poisson majorant estimate on
that same circle. The second inequality integrates first in the target angle,
then uses unit Poisson mass in the source angle. -/
theorem transfer_radial_polynomial_L1 {e h : ℂ → ℂ} (he : IsWeight e) (hh : IsSchwarz h)
    (n : ℕ) (P : ℂ[X]) {r : ℝ} (hr : 0 < r) (hr' : r < 1) :
    r^n * ‖coeff n (fun z => e z * P.eval (h z))‖ ≤
        (∫ t : 𝕋, ‖P.eval (h ((r : ℂ) * ζ t))‖ ∂σ) ∧
      (∫ t : 𝕋, ‖P.eval (h ((r : ℂ) * ζ t))‖ ∂σ) ≤
        ∫ θ : 𝕋, ‖P.eval (ζ θ)‖ ∂σ := by
  let a (t : 𝕋) := h ((r : ℂ) * ζ t)
  have hc : Continuous ζ := continuous_subtype_val.comp AddCircle.continuous_toCircle
  have hrad (z : ℂ) (hz : ‖z‖ ≤ 1) : (r : ℂ) * z ∈ disk := by
    apply mem_ball_zero_iff.mpr
    rw [norm_mul, Complex.norm_of_nonneg hr.le]
    exact (mul_le_of_le_one_right hr.le hz).trans_lt hr'
  have hζ (t : 𝕋) : ‖ζ t‖ = 1 := Circle.norm_coe _
  have hsrc (t : 𝕋) := hrad _ (hζ t).le
  have ha (t : 𝕋) : a t ∈ disk := hh.2.1 (hsrc t)
  have hca : Continuous a := continuous_iff_continuousAt.mpr fun t =>
    (hh.1 _ (hsrc t)).continuousAt.comp (f := fun u : 𝕋 => (r : ℂ) * ζ u)
      (continuous_const.mul hc).continuousAt
  have hPc := (P.continuous.comp hca).norm
  have hPi : Integrable (fun t => ‖P.eval (a t)‖) σ :=
    hPc.integrable_of_hasCompactSupport (.of_compactSpace _)
  constructor
  · let f (z : ℂ) := e z * P.eval (h z)
    have hf : AnalyticOnNhd ℂ f disk := fun z hz =>
      (he.1 z hz).fun_mul ((P.differentiable.analyticAt _).comp (hh.1 z hz))
    have hscaled : AnalyticOnNhd ℂ (fun z => f ((r : ℂ) * z)) closedDisk := fun z hz =>
      (hf _ (hrad z (mem_closedBall_zero_iff.mp hz))).comp (analyticAt_const.fun_mul analyticAt_id)
    have hcauchy := boundary_cauchy hscaled n
    rw [coeff_comp_mul_left] at hcauchy
    have hnorm := congrArg norm hcauchy
    rw [norm_mul, norm_pow, Complex.norm_of_nonneg hr.le] at hnorm
    apply hnorm.ge.trans
    apply norm_integral_le_of_norm_le hPi
    apply Eventually.of_forall
    intro t
    simpa only [f, norm_mul, norm_pow, norm_inv, hζ, inv_one, one_pow, one_mul] using
      (show ‖e ((r : ℂ) * ζ t)‖ * ‖P.eval (a t)‖ ≤ ‖P.eval (a t)‖ from
        mul_le_of_le_one_left (norm_nonneg _) (he.2 _ (hsrc t)))
  · let K (t θ : 𝕋) := poissonKernel 0 (a t) (ζ θ)
    have hK (t θ : 𝕋) : 0 ≤ K t θ := by
      simp only [K, poissonKernel_def, sub_zero, hζ, one_pow]
      exact div_nonneg (sub_nonneg.mpr (pow_le_one₀ (norm_nonneg _) (mem_ball_zero_iff.mp (ha t)).le))
        (sq_nonneg _)
    have hcont : Continuous (Function.uncurry K) := by
      change Continuous fun p : 𝕋 × 𝕋 => poissonKernel 0 (a p.1) (ζ p.2)
      simp only [poissonKernel_def, sub_zero]
      refine (((hc.comp continuous_snd).norm.pow 2).sub ((hca.comp continuous_fst).norm.pow 2)).div
        (((hc.comp continuous_snd).sub (hca.comp continuous_fst)).norm.pow 2) ?_
      intro p
      apply pow_ne_zero
      apply norm_ne_zero_iff.mpr
      exact sub_ne_zero.mpr fun eq => (mem_ball_zero_iff.mp (ha p.1)).ne ((congrArg norm eq).symm.trans (hζ _))
    let B (t θ : 𝕋) := K t θ * ‖P.eval (ζ θ)‖
    have hB : Integrable (Function.uncurry B) (Measure.prod σ σ) :=
      (hcont.mul ((P.continuous.comp (hc.comp continuous_snd)).norm)).integrable_of_hasCompactSupport
        (.of_compactSpace _)
    have hmass (θ : 𝕋) : (∫ t : 𝕋, K t θ ∂σ) = 1 := by
      have h := transfer_poisson_mass hh hr hr' (hζ θ)
      rw [Real.circleAverage_eq_circleAverage_zero_one, ← normalized_integral] at h
      simpa [K, a] using h
    calc
      _ ≤ ∫ t : 𝕋, ∫ θ : 𝕋, B t θ ∂σ ∂σ := by
        apply integral_mono hPi hB.integral_prod_left
        intro t
        have hP : DiffContOnCl ℂ (fun z => P.eval z) (ball 0 1) :=
          P.differentiable.differentiableOn.diffContOnCl
        have hpois := hP.circleAverage_poissonKernel_smul (ha t)
        rw [← normalized_integral] at hpois
        change ‖P.eval (a t)‖ ≤ _
        rw [← hpois]
        refine (norm_integral_le_integral_norm _).trans_eq ?_
        apply integral_congr_ae
        exact .of_forall fun θ => by simp [B, K, Real.norm_eq_abs, abs_of_nonneg (hK t θ)]
      _ = ∫ θ : 𝕋, ∫ t : 𝕋, B t θ ∂σ ∂σ := integral_integral_swap hB
      _ = _ := by simp only [B, integral_mul_const, hmass, one_mul]

/-- The normalized L¹ estimate follows by letting the source radius tend to one. -/
theorem transfer_polynomial_L1 {e h : ℂ → ℂ} (he : IsWeight e) (hh : IsSchwarz h)
    (n : ℕ) (P : ℂ[X]) :
    ‖coeff n (fun z => e z * P.eval (h z))‖ ≤ ∫ θ : 𝕋, ‖P.eval (ζ θ)‖ ∂σ := by
  let C := ‖coeff n (fun z => e z * P.eval (h z))‖
  apply le_of_tendsto (f := fun r : ℝ => r^n * C) (x := 𝓝[<] (1 : ℝ))
  · simpa [C, Pi.mul_def, Pi.pow_def] using ((continuous_id.pow n).mul (continuous_const (y := C))).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[<] (1 : ℝ) ≤ 𝓝 1)
  · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
    obtain ⟨h₁, h₂⟩ := transfer_radial_polynomial_L1 he hh n P hr.1 hr.2
    exact h₁.trans h₂

private theorem shifted_fourier {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F closedDisk)
    (v : C(𝕋, ℂ)) (n : ℕ) (htrace : ∀ θ, (ζ θ)^n * v θ = F (ζ θ))
    (hhigh : ∀ j : ℕ, n < j → (∫ θ : 𝕋, v θ * (ζ θ)^j ∂σ) = 0) (m : ℤ) :
    fourierCoeff (fun θ : 𝕋 => (ζ θ)^n * v θ) m = if m < 0 then 0 else coeff m.toNat F := by
  have mode (i : ℤ) (θ : 𝕋) : fourier i θ = (ζ θ)^i := by
    rw [fourier_apply, AddCircle.toCircle_zsmul, Circle.coe_zpow]
  cases m with
  | ofNat k =>
    simp only [fourierCoeff, mode, ite_eq_right (not_lt.mpr (Int.natCast_nonneg k)),
        Int.ofNat_eq_natCast, zpow_neg, zpow_natCast, smul_eq_mul, htrace, Int.toNat_natCast, ← inv_pow]
    exact boundary_cauchy hF k
  | negSucc k =>
    have hi : -(Int.negSucc k) = ((k+1 : ℕ) : ℤ) := by omega
    simp only [fourierCoeff, mode,
        hi, zpow_natCast, ite_eq_left (Int.negSucc_lt_zero k), smul_eq_mul]
    refine Eq.trans ?_ (hhigh (k+1+n) (by omega))
    apply integral_congr_ae
    apply Eventually.of_forall
    intro θ
    change (ζ θ)^(k+1) * ((ζ θ)^n * v θ) = v θ * (ζ θ)^(k+1+n)
    rw [pow_add (ζ θ) (k+1) n]
    ac_rfl

/-- One density represents every polynomial simultaneously. It can be chosen
continuous, with the shifted density equal everywhere to the trace of a bounded
analytic multiplier. Its moments above n vanish and its remaining moments
are the reversed Taylor jet. The measure is Haar probability on the circle. -/
theorem transfer_boundary_moments {e h : ℂ → ℂ} (he : IsWeight e) (hh : IsSchwarz h) (n : ℕ) :
    ∃ (F : ℂ → ℂ) (v : C(𝕋, ℂ)),
      AnalyticOnNhd ℂ F (closedBall 0 1) ∧ MapsTo F (closedBall 0 1) (closedBall 0 1) ∧
      (∀ θ, ‖v θ‖ ≤ 1) ∧ (∀ θ, (ζ θ)^n * v θ = F (ζ θ)) ∧
      (∀ P : ℂ[X], coeff n (fun z => e z * P.eval (h z)) =
        ∫ θ : 𝕋, v θ * P.eval (ζ θ) ∂σ) ∧
      (∀ j : ℕ, n < j → (∫ θ : 𝕋, v θ * (ζ θ)^j ∂σ) = 0) ∧
      (∀ j : ℕ, j ≤ n → (∫ θ : 𝕋, v θ * (ζ θ)^j ∂σ) = coeff (n-j) F) ∧
      (∀ m : ℤ, fourierCoeff (fun θ : 𝕋 => (ζ θ)^n * v θ) m =
        if m < 0 then 0 else coeff m.toNat F) := by
  obtain ⟨F, hF, hm, ht⟩ := regular_transfer he hh n
  have hc : Continuous ζ := continuous_subtype_val.comp AddCircle.continuous_toCircle
  have hnorm (θ : 𝕋) : ‖ζ θ‖ = 1 := Circle.norm_coe _
  have hmem (θ : 𝕋) : ζ θ ∈ closedDisk := mem_closedBall_zero_iff.mpr (hnorm θ).le
  have hnz (θ : 𝕋) : ζ θ ≠ 0 := norm_ne_zero_iff.mp ((hnorm θ).trans_ne one_ne_zero)
  let v : C(𝕋, ℂ) := ⟨fun θ => (ζ θ)⁻¹ ^ n * F (ζ θ),
    ((hc.inv₀ hnz).pow n).mul (continuous_iff_continuousAt.mpr fun θ =>
      (hF _ (hmem θ)).continuousAt.comp (f := ζ) (hc.continuousAt (x := θ)))⟩
  have hrep (P : ℂ[X]) : coeff n (fun z => e z * P.eval (h z)) =
      ∫ θ : 𝕋, v θ * P.eval (ζ θ) ∂σ := by
    rw [ht _ (P.differentiable.analyticAt _), ← boundary_cauchy (f := fun z => F z * P.eval z)
      (fun z hz => (hF z hz).fun_mul (P.differentiable.analyticAt _))]
    simp [v, mul_assoc]
  have htrace (θ : 𝕋) : (ζ θ)^n * v θ = F (ζ θ) := by simp [v, hnz]
  have hhigh (j : ℕ) (hj : n < j) : (∫ θ : 𝕋, v θ * (ζ θ)^j ∂σ) = 0 := by
    have hmom := transfer_moment (he.1 0 (by simp [disk])) (hh.1 0 (by simp [disk]))
      hh.2.2 n j hj.le
    simpa using (hrep (Polynomial.X ^ j)).symm.trans (by simpa [hj.ne'] using hmom)
  refine ⟨F, v, hF, hm, fun θ => ?_, htrace, hrep, hhigh, fun j hj => ?_,
    shifted_fourier hF v n htrace hhigh⟩
  · simpa [v, norm_mul, norm_pow, norm_inv, hnorm] using mem_closedBall_zero_iff.mp (hm (hmem θ))
  · rw [← boundary_cauchy hF]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro θ
    change (ζ θ)⁻¹ ^ n * F (ζ θ) * (ζ θ)^j = (ζ θ)⁻¹ ^ (n-j) * F (ζ θ)
    conv_lhs => rw [← Nat.sub_add_cancel hj, pow_add]
    simp [inv_pow, pow_ne_zero _ (hnz θ), mul_comm, mul_left_comm]

/-- The extension on the whole complex L¹ space, together with a representing
element of the unit ball of L∞. Polynomial boundary values use normalized Haar
measure and the pairing uses ordinary multiplication. -/
theorem transfer_L1_extension {e h : ℂ → ℂ} (he : IsWeight e) (hh : IsSchwarz h) (n : ℕ) :
    ∃ (v : Lp ℂ ⊤ σ) (L : Lp ℂ 1 σ →L[ℂ] ℂ), ‖v‖ ≤ 1 ∧ ‖L‖ ≤ 1 ∧
      (∀ᵐ θ ∂σ, ‖v θ‖ ≤ 1) ∧ (∀ f, L f = ∫ θ, v θ * f θ ∂σ) ∧
      ∀ P : ℂ[X], L (ContinuousMap.toLp 1 σ ℂ P.toAddCircle) =
        coeff n (fun z => e z * P.eval (h z)) := by
  obtain ⟨_, u, _, _, hu, _, hp, _⟩ := transfer_boundary_moments he hh n
  let v := ContinuousMap.toLp ⊤ σ ℂ u
  have hv : v =ᵐ[σ] ⇑u := ContinuousMap.coeFn_toLp (𝕜 := ℂ) σ u
  have hb : ∀ᵐ θ ∂σ, ‖v θ‖ ≤ 1 := hv.mono fun θ hθ => hθ ▸ hu θ
  let L := (ContinuousLinearMap.mul ℂ ℂ).lpPairing σ ⊤ 1 v
  have hL (f : Lp ℂ 1 σ) : L f = ∫ θ, v θ * f θ ∂σ :=
    ContinuousLinearMap.lpPairing_eq_integral _ _ _
  refine ⟨v, L, ?_, L.opNorm_le_bound zero_le_one (fun f => ?_), hb, hL, fun P => ?_⟩
  · simpa using Lp.norm_le_of_ae_bound zero_le_one hb
  · rw [hL, one_mul, L1.norm_eq_integral_norm]
    apply norm_integral_le_of_norm_le (L1.integrable_coeFn f).norm
    filter_upwards [hb] with θ hθ
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hθ
  · rw [hL, hp]
    apply integral_congr_ae
    filter_upwards [hv, ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℂ) σ P.toAddCircle] with θ hθ hP
    rw [hθ, hP]
    simp [Polynomial.toAddCircle]

end Goodman
