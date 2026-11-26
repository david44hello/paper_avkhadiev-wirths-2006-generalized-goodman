-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Goodman.Defs

/-!
# Bounded analytic extension from one-sided Fourier data

The boundary measure is Haar probability on the circle of length `2π`.
The extension is the Taylor series of the nonnegative Fourier coefficients.
-/

noncomputable section

open Complex Filter MeasureTheory Metric Real Set
open scoped Topology ComplexConjugate

namespace Goodman

local notation "𝕋" => AddCircle (2 * π)
local instance : Fact (0 < 2 * π) := ⟨two_pi_pos⟩
local notation "σ" => (AddCircle.haarAddCircle (T := 2 * π))
local notation "ζ" => (fun θ : 𝕋 => (AddCircle.toCircle θ : ℂ))

private lemma mode (i : ℤ) (t : 𝕋) : fourier i t = (ζ t)^i := by
  rw [fourier_apply, AddCircle.toCircle_zsmul, Circle.coe_zpow]

private lemma unit_norm (t : 𝕋) : ‖ζ t‖ = 1 := Circle.norm_coe _
private lemma unit_ne (t : 𝕋) : ζ t ≠ 0 := (AddCircle.toCircle t).coe_ne_zero
private lemma unit_cont : Continuous ζ := continuous_subtype_val.comp AddCircle.continuous_toCircle

private lemma coefficient_bound {f : 𝕋 → ℂ} (hb : ∀ᵐ t ∂σ, ‖f t‖ ≤ 1) (n : ℤ) :
    ‖fourierCoeff f n‖ ≤ 1 := by
  calc
    _ ≤ ∫ t : 𝕋, (1 : ℝ) ∂σ := by
      apply norm_integral_le_of_norm_le (integrable_const _)
      filter_upwards [hb] with t ht
      simpa [mode, norm_zpow, unit_norm] using ht
    _ = 1 := by simp

/-- The extension obtained directly from the prescribed Fourier data. -/
def hardyExtension (f : 𝕋 → ℂ) : ℂ → ℂ :=
  FormalMultilinearSeries.ofScalarsSum (fun n : ℕ => fourierCoeff f n)

/-- All nonnegative Fourier coefficients are realized by one analytic Taylor series. -/
theorem hardyExtension_analytic_coeff {f : 𝕋 → ℂ} (hb : ∀ᵐ t ∂σ, ‖f t‖ ≤ 1) :
    AnalyticOnNhd ℂ (hardyExtension f) disk ∧
      ∀ n : ℕ, coeff n (hardyExtension f) = fourierCoeff f n := by
  let p := FormalMultilinearSeries.ofScalars ℂ (fun n : ℕ => fourierCoeff f n)
  have hr : (1 : ENNReal) ≤ p.radius := by
    apply p.le_radius_of_bound (r := (1 : NNReal)) 1
    simpa [p, FormalMultilinearSeries.ofScalars_norm] using fun n : ℕ => coefficient_bound hb n
  have ha : AnalyticOnNhd ℂ p.sum disk := p.analyticOnNhd.mono
    ((show disk = eball (0 : ℂ) 1 from (Metric.eball_coe (ε := (1 : NNReal))).symm).le.trans
      (eball_subset_eball hr))
  refine ⟨ha, fun n => ?_⟩
  have hp := (p.hasFPowerSeriesOnBall (zero_lt_one.trans_le hr)).hasFPowerSeriesAt
  have he := (ha 0 (by simp [disk])).hasFPowerSeriesAt.eq_formalMultilinearSeries hp
  simpa [p, coeff, hardyExtension, FormalMultilinearSeries.ofScalarsSum] using
    congrArg (fun q : FormalMultilinearSeries ℂ ℂ ℂ => q.coeff n) he

private lemma kernel_split {z u : ℂ} (hz : ‖z‖ < 1) (hu : ‖u‖ = 1) :
    (poissonKernel 0 z u : ℂ) = (1 - z / u)⁻¹ + (1 - conj z * u)⁻¹ - 1 := by
  have hu0 := norm_ne_zero_iff.mp (hu.trans_ne one_ne_zero)
  have hne : u ≠ z := fun e => hz.ne ((congrArg norm e).symm.trans hu)
  have hcu : conj u = u⁻¹ := by
    apply (mul_right_inj' hu0).mp
    simp [Complex.mul_conj', hu, hu0]
  have h₁ : 1 - z / u ≠ 0 := sub_ne_zero.mpr fun e => by
    have := congrArg norm e
    simp [hu] at this
    linarith
  have h₂ : 1 - conj z * u ≠ 0 := sub_ne_zero.mpr fun e => by
    have := congrArg norm e
    simp [hu] at this
    linarith
  have h₃ : u⁻¹ - conj z ≠ 0 := by rw [← hcu, ← map_sub]; exact (map_ne_zero _).mpr (sub_ne_zero.mpr hne)
  rw [poissonKernel_eq_re_herglotzRieszKernel]
  simp only [Function.comp_apply, herglotzRieszKernel_def, sub_zero, Complex.re_eq_add_conj,
    map_div₀, map_add, map_sub, hcu]
  have h₄ : 1 - u * conj z ≠ 0 := by rwa [mul_comm]
  field_simp [hu0, sub_ne_zero.mpr hne, h₁, h₂, h₃, h₄]
  ring

private lemma geometric_integral {f b : 𝕋 → ℂ} (hf : AEStronglyMeasurable f σ)
    (hb : ∀ᵐ t ∂σ, ‖f t‖ ≤ 1) (hc : Continuous b) {R : ℝ} (hR : R < 1)
    (hn : ∀ t, ‖b t‖ = R) :
    HasSum (fun n : ℕ => ∫ t, b t ^ n * f t ∂σ) (∫ t, (1 - b t)⁻¹ * f t ∂σ) := by
  apply hasSum_integral_of_dominated_convergence (fun n _ => R^n)
  · exact fun n => (hc.pow n).aestronglyMeasurable.mul hf
  · intro n
    filter_upwards [hb] with t ht
    rw [norm_mul, norm_pow, hn]
    exact mul_le_of_le_one_right (pow_nonneg ((hn t) ▸ norm_nonneg _) n) ht
  · exact .of_forall fun _ => summable_geometric_of_lt_one ((hn 0) ▸ norm_nonneg _) hR
  · exact integrable_const _
  · exact .of_forall fun t => (hasSum_geometric_of_norm_lt_one ((hn t).trans_lt hR)).mul_right _

private lemma kernel_cont {z : ℂ} (hz : ‖z‖ < 1) :
    Continuous fun t : 𝕋 => poissonKernel 0 z (ζ t) := by
  simp only [poissonKernel_def, sub_zero]
  refine ((unit_cont.norm.pow 2).sub continuous_const).div ((unit_cont.sub continuous_const).norm.pow 2) ?_
  intro t
  exact pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr fun e =>
    hz.ne ((congrArg norm e).symm.trans (unit_norm t))))

private lemma kernel_nonneg {z : ℂ} (hz : ‖z‖ < 1) (t : 𝕋) : 0 ≤ poissonKernel 0 z (ζ t) := by
  simp only [poissonKernel_def, sub_zero, unit_norm, one_pow]
  exact div_nonneg (sub_nonneg.mpr (pow_le_one₀ (norm_nonneg _) hz.le)) (sq_nonneg _)

private lemma kernel_mass {z : ℂ} (hz : ‖z‖ < 1) : (∫ t, poissonKernel 0 z (ζ t) ∂σ) = 1 := by
  have hav := (differentiable_const (c := (1 : ℂ))).differentiableOn.diffContOnCl.circleAverage_poissonKernel_smul
    (mem_ball_zero_iff.mpr hz)
  have h : (∫ t : 𝕋, (poissonKernel 0 z (ζ t) : ℂ) ∂σ) = (1 : ℂ) := by
    rw [AddCircle.integral_haarAddCircle, Real.circleAverage,
      ← AddCircle.intervalIntegral_preimage (2 * π) 0] at *
    simp_all [AddCircle.toCircle, circleMap, Complex.real_smul]
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

/-- The one-sided Fourier series of the given representative equals its Poisson integral. -/
theorem hardyExtension_eq_poisson {f : 𝕋 → ℂ} (hf : AEStronglyMeasurable f σ)
    (hb : ∀ᵐ t ∂σ, ‖f t‖ ≤ 1) (hneg : ∀ i : ℤ, i < 0 → fourierCoeff f i = 0)
    {z : ℂ} (hz : z ∈ disk) :
    hardyExtension f z = ∫ t, (poissonKernel 0 z (ζ t) : ℂ) * f t ∂σ := by
  have hz' := mem_ball_zero_iff.mp hz
  have hplus := geometric_integral hf hb (continuous_const.div unit_cont unit_ne) hz'
    (fun t => by simp : ∀ t : 𝕋, ‖z / ζ t‖ = ‖z‖)
  have hminus := geometric_integral hf hb (continuous_const.mul unit_cont) hz'
    (fun t => by simp : ∀ t : 𝕋, ‖conj z * ζ t‖ = ‖z‖)
  have hp (n : ℕ) : (∫ t, (z / ζ t)^n * f t ∂σ) = fourierCoeff f n * z^n := by
    simp only [fourierCoeff, mode, zpow_neg, zpow_natCast, smul_eq_mul, div_eq_mul_inv,
      mul_pow, inv_pow, mul_assoc, integral_const_mul]
    ring
  have hm (n : ℕ) : (∫ t, (conj z * ζ t)^n * f t ∂σ) =
      (conj z)^n * fourierCoeff f (-(n : ℤ)) := by
    simp only [fourierCoeff, neg_neg, mode, zpow_natCast, smul_eq_mul, mul_pow, mul_assoc, integral_const_mul]
  have hs : HasSum (fun n : ℕ => ∫ t, (conj z * ζ t)^n * f t ∂σ) (∫ t, f t ∂σ) := by
    convert hasSum_ite_eq (0 : ℕ) (∫ t, f t ∂σ) using 1
    funext n
    split_ifs with he
    · simp [he]
    · rw [hm, hneg _ (by omega), mul_zero]
  have hi : Integrable f σ := (memLp_one_iff_integrable.mp (MemLp.of_bound hf 1 hb))
  have hiK (b : 𝕋 → ℂ) (hc : Continuous b) (hn : ∀ t, ‖b t‖ < 1) :
      Integrable (fun t => (1 - b t)⁻¹ * f t) σ := by
    apply Integrable.mul_bdd (c := 1) _ hf hb
    apply Continuous.integrable_of_hasCompactSupport _ (.of_compactSpace _)
    exact (continuous_const.sub hc).inv₀ fun t => sub_ne_zero.mpr fun e =>
      (hn t).ne ((congrArg norm e).symm.trans norm_one)
  simp only [Pi.div_apply, Pi.mul_apply] at hplus hminus
  simp_rw [kernel_split hz' (unit_norm _), sub_mul, add_mul, one_mul]
  rw [integral_sub, integral_add, hminus.unique hs, add_sub_cancel_right]
  · simpa only [hardyExtension, FormalMultilinearSeries.ofScalars_sum_eq, hp, smul_eq_mul] using hplus.tsum_eq
  all_goals first
    | exact hi
    | apply Integrable.add <;> apply hiK
    | apply hiK
  all_goals first
    | exact continuous_const.div unit_cont unit_ne
    | exact continuous_const.mul unit_cont
    | exact fun t => by simpa using hz'

/-- The essential boundary bound holds at every interior point. -/
theorem hardyExtension_isWeight {f : 𝕋 → ℂ} (hf : AEStronglyMeasurable f σ)
    (hb : ∀ᵐ t ∂σ, ‖f t‖ ≤ 1) (hneg : ∀ i : ℤ, i < 0 → fourierCoeff f i = 0) :
    IsWeight (hardyExtension f) := by
  refine ⟨(hardyExtension_analytic_coeff hb).1, fun z hz => ?_⟩
  rw [hardyExtension_eq_poisson hf hb hneg hz, ← kernel_mass (mem_ball_zero_iff.mp hz)]
  apply norm_integral_le_of_norm_le ((kernel_cont (mem_ball_zero_iff.mp hz)).integrable_of_hasCompactSupport
    (.of_compactSpace _))
  filter_upwards [hb] with t ht
  rw [norm_mul, Complex.norm_of_nonneg (kernel_nonneg (mem_ball_zero_iff.mp hz) t)]
  exact mul_le_of_le_one_right (kernel_nonneg (mem_ball_zero_iff.mp hz) t) ht


/-- The preimage of a closed Euclidean ball centered on the unit circle. -/
abbrev hardyChordBall (x : 𝕋) (d : ℝ) := ζ ⁻¹' closedBall (ζ x) d

/-- Lebesgue differentiation on the circle, using ambient Euclidean chordal balls. -/
theorem ae_tendsto_chord_average {f : 𝕋 → ℂ} (hi : Integrable f σ) :
    ∀ᵐ x ∂σ, Tendsto (fun d => ⨍ t in hardyChordBall x d, ‖f t - f x‖ ∂σ) (𝓝[>] 0) (𝓝 0) := by
  have he : MeasurableEmbedding ζ := (unit_cont.isClosedEmbedding
    (Subtype.val_injective.comp (AddCircle.injective_toCircle two_pi_pos.ne'))).measurableEmbedding
  obtain ⟨g, _, hg⟩ := he.exists_measurable_extend hi.1.measurable_mk (fun _ => inferInstance)
  have heq : g ∘ ζ =ᵐ[σ] f := hg ▸ hi.1.ae_eq_mk.symm
  have hgi : Integrable g ((σ).map ζ) := he.integrable_map_iff.mpr (hi.congr heq.symm)
  have hdiff := (Besicovitch.vitaliFamily ((σ).map ζ)).ae_tendsto_average_norm_sub hgi.locallyIntegrable
  filter_upwards [ae_of_ae_map he.measurable.aemeasurable hdiff, heq] with x hx hx'
  apply (hx.comp (Besicovitch.tendsto_filterAt _ _)).congr
  intro d
  simp only [Function.comp_apply, setAverage_eq, he.setIntegral_map, measureReal_def,
    Measure.map_apply he.measurable measurableSet_closedBall]
  congr 1
  apply setIntegral_congr_ae (he.measurable measurableSet_closedBall)
  filter_upwards [heq] with t ht _
  change g (ζ t) = f t at ht
  change g (ζ x) = f x at hx'
  rw [ht, hx']

private lemma layer_compare (ν : Measure 𝕋) [IsFiniteMeasure ν] {W : 𝕋 → ℝ}
    (hc : Continuous W) (hn : ∀ t, 0 ≤ W t) {ε : ℝ} (hε : 0 ≤ ε)
    (hlevel : ∀ s > 0, ν.real {t | s ≤ W t} ≤ ε * (σ).real {t | s ≤ W t}) :
    (∫ t, W t ∂ν) ≤ ε * ∫ t, W t ∂σ := by
  have hi (μ : Measure 𝕋) [IsFiniteMeasure μ] : Integrable W μ :=
    hc.integrable_of_hasCompactSupport (.of_compactSpace _)
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hε (integral_nonneg hn))).mp
  rw [ENNReal.ofReal_mul hε, ofReal_integral_eq_lintegral_ofReal (hi ν) (.of_forall hn),
    ofReal_integral_eq_lintegral_ofReal (hi σ) (.of_forall hn),
    lintegral_eq_lintegral_meas_le ν (.of_forall hn) hc.aemeasurable,
    lintegral_eq_lintegral_meas_le σ (.of_forall hn) hc.aemeasurable,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' measurableSet_Ioi
  intro s hs
  simpa only [ENNReal.ofReal_mul hε, ofReal_measureReal (measure_ne_top ν _),
    ofReal_measureReal (measure_ne_top σ _)] using ENNReal.ofReal_le_ofReal (hlevel s hs)

private lemma radial_kernel (x t : 𝕋) {r : ℝ} (hr : 0 < r) :
    poissonKernel 0 ((r : ℂ) * ζ x) (ζ t) =
      (1-r^2) / ((1-r)^2 + r * dist (ζ t) (ζ x)^2) := by
  rw [← Complex.real_smul]
  simp only [poissonKernel_def, sub_zero, norm_smul, Real.norm_of_nonneg hr.le, unit_norm, mul_one,
    one_pow, dist_eq_norm, norm_sub_sq_real, real_inner_smul_right]
  congr 1
  ring

/-- At any Lebesgue point, the entire radial Poisson integral converges to the
value of the representative. The truncated kernel has only small chordal balls
as nonempty positive superlevel sets. -/
theorem poisson_tendsto_at_chord_lebesguePoint {f : 𝕋 → ℂ} (hi : Integrable f σ) {x : 𝕋}
    (hx : Tendsto (fun d => ⨍ t in hardyChordBall x d, ‖f t - f x‖ ∂σ) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun r : ℝ => ∫ t, (poissonKernel 0 ((r : ℂ) * ζ x) (ζ t) : ℂ) * f t ∂σ)
      (𝓝[<] 1) (𝓝 (f x)) := by
  let g := fun t => ‖f t - f x‖
  have hgi : Integrable g σ := (hi.sub (integrable_const _)).norm
  have hg (t) : 0 ≤ g t := norm_nonneg _
  let ν := (σ).withDensity fun t => ENNReal.ofReal (g t)
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hgi.2
  have hν (s : Set 𝕋) (hs : MeasurableSet s) : ν.real s = ∫ t in s, g t ∂σ := by
    rw [withDensity_real_apply_eq_integral (hgi.aemeasurable.ennreal_ofReal.mono_measure
      Measure.restrict_le_self) (.of_forall fun _ _ => ENNReal.ofReal_lt_top) hs.nullMeasurableSet]
    simp [hg]
  have hint (W : 𝕋 → ℝ) : (∫ t, W t ∂ν) = ∫ t, W t * g t ∂σ := by
    rw [integral_withDensity_eq_integral_toReal_smul₀ hgi.aemeasurable.ennreal_ofReal
      (.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp [hg, mul_comm]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he := half_pos hε
  obtain ⟨δ, hδ, hd⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp (hx.eventually (gt_mem_nhds he))
  change 0 < δ at hδ
  have hball (d : ℝ) (hd0 : 0 ≤ d) (hdδ : d ≤ δ) :
      ν.real (hardyChordBall x d) ≤ ε/2 * (σ).real (hardyChordBall x d) := by
    rw [hν _ (unit_cont.measurable measurableSet_closedBall)]
    rcases hd0.eq_or_lt with h | h
    · subst d
      have heq : hardyChordBall x 0 = {x} := by
        ext t
        simp only [hardyChordBall, closedBall_zero, mem_preimage, mem_singleton_iff]
        exact (Subtype.val_injective.comp (AddCircle.injective_toCircle two_pi_pos.ne')).eq_iff
      change (∫ t in hardyChordBall x 0, g t ∂σ) ≤ _
      rw [heq, integral_singleton]
      simpa [g] using mul_nonneg he.le (measureReal_nonneg (μ := σ) (s := {x}))
    · rw [← measure_smul_setAverage g (measure_ne_top _ _), smul_eq_mul, mul_comm (ε/2)]
      exact mul_le_mul_of_nonneg_left (hd ⟨h, hdδ⟩).le (measureReal_nonneg)
  let a (r : ℝ) := (1-r^2) / ((1-r)^2 + r*δ^2)
  have ha : Tendsto a (𝓝[<] 1) (𝓝 0) := by
    have hc : ContinuousAt a 1 := by
      dsimp [a]
      fun_prop (disch := simp [ne_of_gt hδ])
    simpa [a] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ r in 𝓝[<] (1 : ℝ), a r * ν.real univ < ε/2 := by
    have h : Tendsto (fun r => a r * ν.real univ) (𝓝[<] 1) (𝓝 0) := by
      simpa using ha.mul_const (ν.real univ)
    exact h.eventually_lt_const he
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num), hsmall] with r hr hsmall
  obtain ⟨hr0, hr1⟩ := hr
  let z := (r : ℂ) * ζ x
  have hz : ‖z‖ < 1 := by simpa [z, norm_mul, abs_of_pos hr0] using hr1
  let K := fun t => poissonKernel 0 z (ζ t)
  let W := fun t => max (K t - a r) 0
  have hK : Continuous K := kernel_cont hz
  have hW : Continuous W := (hK.sub continuous_const).max continuous_const
  have hnum : 0 < 1-r^2 := by nlinarith [sq_nonneg (r-1), mul_pos (sub_pos.mpr hr1) (by linarith : 0 < 1+r)]
  have hden (d : ℝ) : 0 < (1-r)^2 + r*d^2 := by positivity [sub_pos.mpr hr1]
  have ha0 : 0 ≤ a r := (div_pos hnum (hden δ)).le
  have hl : (∫ t, W t ∂ν) ≤ ε/2 * ∫ t, W t ∂σ := by
    apply layer_compare ν hW (fun _ => le_max_right _ _) he.le
    intro s hs
    let b := s + a r
    have hb : 0 < b := add_pos_of_pos_of_nonneg hs ha0
    let q := ((1-r^2)/b - (1-r)^2) / r
    have hlev (t : 𝕋) : s ≤ W t ↔ dist (ζ t) (ζ x)^2 ≤ q := by
      change s ≤ max (K t - a r) 0 ↔ _
      rw [le_max_iff, or_iff_left hs.not_ge, le_sub_iff_add_le]
      change b ≤ poissonKernel 0 ((r : ℂ) * ζ x) (ζ t) ↔ _
      rw [radial_kernel x t hr0, le_div_iff₀ (hden _)]
      dsimp [q]
      conv_rhs => rw [le_div_iff₀ hr0, le_sub_iff_add_le, le_div_iff₀ hb]
      constructor <;> intro h <;> nlinarith only [h]
    by_cases hq : 0 ≤ q
    · have hset : {t | s ≤ W t} = hardyChordBall x (√q) := by
        ext t
        simp only [mem_ofPred_eq, hardyChordBall, mem_preimage, mem_closedBall, hlev,
          Real.le_sqrt (dist_nonneg) hq]
      rw [hset]
      apply hball _ (Real.sqrt_nonneg _)
      apply (Real.sqrt_le_iff).mpr
      refine ⟨hδ.le, ?_⟩
      change ((1-r^2)/b - (1-r)^2) / r ≤ δ^2
      rw [div_le_iff₀ hr0, sub_le_iff_le_add, div_le_iff₀ hb]
      have hba : a r ≤ b := le_add_of_nonneg_left hs.le
      have hh := (div_le_iff₀ (hden δ)).mp hba
      nlinarith only [hh]
    · have hset : {t | s ≤ W t} = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun t ht =>
        hq ((sq_nonneg _).trans ((hlev t).mp ht))
      simp [hset]
  have intC (μ : Measure 𝕋) [IsFiniteMeasure μ] {U : 𝕋 → ℝ} (hc : Continuous U) : Integrable U μ :=
    hc.integrable_of_hasCompactSupport (.of_compactSpace _)
  have hWle : (∫ t, W t ∂σ) ≤ 1 := by
    rw [← kernel_mass hz]
    exact integral_mono (intC σ hW) (intC σ hK) fun t => max_le (sub_le_self _ ha0) (kernel_nonneg hz t)
  have hmain : (∫ t, K t ∂ν) ≤ ε/2 + a r * ν.real univ := calc
    _ ≤ ∫ t, W t + a r ∂ν := integral_mono (intC ν hK) ((intC ν hW).add (integrable_const _))
      fun t => by dsimp [W]; linarith [le_max_left (K t - a r) 0]
    _ = (∫ t, W t ∂ν) + a r * ν.real univ := by rw [integral_add (intC ν hW) (integrable_const _)]; simp [mul_comm]
    _ ≤ _ := by linarith [mul_le_mul_of_nonneg_left hWle he.le]
  have hKC : Continuous fun t => (K t : ℂ) := continuous_ofReal.comp hK
  have hKi := hKC.integrable_of_hasCompactSupport (μ := σ) (.of_compactSpace _)
  have hKf := integrableOn_univ.mp (IntegrableOn.continuousOn_mul hKC.continuousOn
    (integrableOn_univ.mpr hi) isCompact_univ)
  have hn : (∫ t, (K t : ℂ) * f x ∂σ) = f x := by
    rw [integral_mul_const, integral_complex_ofReal, kernel_mass hz]; simp
  rw [dist_eq_norm, ← hn, ← integral_sub hKf (hKi.mul_const _)]
  apply (norm_integral_le_integral_norm _).trans_lt
  rw [hint] at hmain
  calc
    _ = ∫ t, K t * g t ∂σ := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro t
      change ‖(K t : ℂ) * f t - (K t : ℂ) * f x‖ = K t * ‖f t - f x‖
      rw [← mul_sub, norm_mul, Complex.norm_of_nonneg (kernel_nonneg hz t)]
    _ < ε := by linarith


private lemma radial_mem_disk (x : 𝕋) {r : ℝ} (hr : r ∈ Ioo 0 1) : (r : ℂ) * ζ x ∈ disk := by
  simpa [disk, mem_ball_zero_iff, norm_mul, abs_of_pos hr.1] using hr.2

/-- The radial limit at almost every angle is the original measurable representative. -/
theorem hardyExtension_radial_ae {f : 𝕋 → ℂ} (hf : AEStronglyMeasurable f σ)
    (hb : ∀ᵐ t ∂σ, ‖f t‖ ≤ 1) (hneg : ∀ i : ℤ, i < 0 → fourierCoeff f i = 0) :
    ∀ᵐ x ∂σ, Tendsto (fun r : ℝ => hardyExtension f ((r : ℂ) * ζ x)) (𝓝[<] 1) (𝓝 (f x)) := by
  have hi : Integrable f σ := memLp_one_iff_integrable.mp (MemLp.of_bound hf 1 hb)
  filter_upwards [ae_tendsto_chord_average hi] with x hx
  apply (poisson_tendsto_at_chord_lebesguePoint hi hx).congr'
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
  exact (hardyExtension_eq_poisson hf hb hneg (radial_mem_disk x hr)).symm

/-- Full mean-square convergence of the radial sections, with Haar probability measure. -/
theorem hardyExtension_radial_L2 {f : 𝕋 → ℂ} (hf : AEStronglyMeasurable f σ)
    (hb : ∀ᵐ t ∂σ, ‖f t‖ ≤ 1) (hneg : ∀ i : ℤ, i < 0 → fourierCoeff f i = 0) :
    Tendsto (fun r : ℝ => ∫ x, ‖hardyExtension f ((r : ℂ) * ζ x) - f x‖^2 ∂σ) (𝓝[<] 1) (𝓝 0) := by
  have hE := hardyExtension_isWeight hf hb hneg
  have hrs := Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)
  have hm : ∀ᶠ (r : ℝ) in 𝓝[<] 1, AEStronglyMeasurable
      (fun x : 𝕋 => ‖hardyExtension f ((r : ℂ) * ζ x) - f x‖^2) σ := by
    filter_upwards [hrs] with r hr
    have hc : Continuous fun x : 𝕋 => hardyExtension f ((r : ℂ) * ζ x) :=
      continuous_iff_continuousAt.mpr fun x =>
        (hE.1 _ (radial_mem_disk x hr)).continuousAt.comp (f := fun t : 𝕋 => (r : ℂ) * ζ t)
          (continuous_const.mul unit_cont).continuousAt
    exact (hc.aestronglyMeasurable.sub hf).norm.pow _
  have hl := hardyExtension_radial_ae hf hb hneg
  simpa using tendsto_integral_filter_of_dominated_convergence (f := fun _ : 𝕋 => (0 : ℝ))
    (fun _ => (4 : ℝ)) hm (by
      filter_upwards [hrs] with r hr
      filter_upwards [hb] with x hx
      have h := (norm_sub_le (hardyExtension f ((r : ℂ) * ζ x)) (f x)).trans
        (add_le_add (hE.2 _ (radial_mem_disk x hr)) hx)
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      nlinarith [sq_nonneg (‖hardyExtension f ((r : ℂ) * ζ x) - f x‖ - 2),
        mul_nonneg (norm_nonneg (hardyExtension f ((r : ℂ) * ζ x) - f x)) (sub_nonneg.mpr h)]) (integrable_const _)
    (hl.mono fun x hx => by simpa using ((hx.sub_const (f x)).norm.pow 2))

/-- The implication used in the weighted transfer proof, for each supplied
boundary function with one-sided Fourier spectrum. -/
theorem transfer_hardy_boundary {f : 𝕋 → ℂ} (hf : AEStronglyMeasurable f σ)
    (hb : ∀ᵐ t ∂σ, ‖f t‖ ≤ 1) (hneg : ∀ i : ℤ, i < 0 → fourierCoeff f i = 0) :
    ∃ E : ℂ → ℂ, IsWeight E ∧ (∀ n : ℕ, coeff n E = fourierCoeff f n) ∧
      (∀ᵐ x ∂σ, Tendsto (fun r : ℝ => E ((r : ℂ) * ζ x)) (𝓝[<] 1) (𝓝 (f x))) ∧
      Tendsto (fun r : ℝ => ∫ x, ‖E ((r : ℂ) * ζ x) - f x‖^2 ∂σ) (𝓝[<] 1) (𝓝 0) :=
  ⟨hardyExtension f, hardyExtension_isWeight hf hb hneg, (hardyExtension_analytic_coeff hb).2,
    hardyExtension_radial_ae hf hb hneg, hardyExtension_radial_L2 hf hb hneg⟩

end Goodman
