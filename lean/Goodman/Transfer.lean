-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
module

public import Goodman.CoefficientClaims

@[expose] public section

/-!
# Weighted coefficient transfer

On a source circle of radius `r`, multiply the weight by the phase `(r/z)^n`.
At a target boundary point `w`, integrate this phased weight against the Poisson
kernel with pole `h z`, then multiply by `w^n`. The kernel has mean one in the
source variable. Splitting the shifted kernel into a finite geometric sum,
a holomorphic tail in `w`, and a term of order
`n+1` in `h z` gives a disk multiplier. The last term has zero source average by
Cauchy's formula. As `r` tends to one, coefficient compactness removes the factor
`r^n` from the finite jet.
-/

noncomputable section
open Set Filter Metric Complex
open scoped Topology

namespace Goodman

private theorem transfer_zero_mem : (0 : ℂ) ∈ disk := by simp [disk]

private theorem mul_pow_coeff {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (n j : ℕ) :
    coeff n (fun z => z^j * f z) = if j ≤ n then coeff (n-j) f else 0 := by
  classical
  simp only [coeff, iteratedDeriv_fun_mul (f := fun z : ℂ => z^j) (by fun_prop)
    hf.contDiffAt, iteratedDeriv_fun_pow_zero, Nat.cast_ite, Nat.cast_zero, mul_ite, ite_mul, mul_zero, zero_mul]
  by_cases hj : j ≤ n
  · have hm : j ∈ Finset.range (n+1) := Finset.mem_range.mpr (by omega)
    simp only [ite_eq_left hj, Finset.sum_ite_eq' _ _ _, ite_eq_left hm]
    have h : (n.choose j : ℂ) * j.factorial * (n-j).factorial = n.factorial := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hj
    rw [← h]
    have hc : (n.choose j : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hj).ne'
    field_simp [show (j.factorial : ℂ) ≠ 0 by exact_mod_cast j.factorial_ne_zero,
      show ((n-j).factorial : ℂ) ≠ 0 by exact_mod_cast (n-j).factorial_ne_zero]
  · have hm : j ∉ Finset.range (n+1) := by simp; omega
    simp [hj, Finset.sum_ite_eq', hm]

private theorem factor_schwarz_germ {h : ℂ → ℂ} (hh : AnalyticAt ℂ h 0) (hz : h 0 = 0) :
    ∃ b : ℂ → ℂ, AnalyticAt ℂ b 0 ∧ b 0 = deriv h 0 ∧ ∀ z, h z = z * b z := by
  obtain ⟨p, hp⟩ := hh
  refine ⟨dslope h 0, ⟨_, hp.has_fpower_series_dslope_fslope⟩, dslope_same .., fun z => ?_⟩
  simpa [hz] using (sub_smul_dslope h 0 z).symm

/-- The leading moment and the vanishing of all moments beyond the chosen degree. -/
theorem transfer_moment {e h : ℂ → ℂ} (he : AnalyticAt ℂ e 0)
    (hh : AnalyticAt ℂ h 0) (hz : h 0 = 0) (n j : ℕ) (hnj : n ≤ j) :
    coeff n (fun z => e z * h z ^ j) = if j = n then e 0 * deriv h 0 ^ n else 0 := by
  obtain ⟨b, hb, h0, hfac⟩ := factor_schwarz_germ hh hz
  have hf : (fun z => e z * h z ^ j) = (fun z => z^j * (e z * b z ^ j)) := by
    funext z
    rw [hfac, mul_pow]
    ring
  rw [hf, mul_pow_coeff (he.fun_mul (hb.fun_pow j))]
  rcases hnj.eq_or_lt with rfl | hlt
  · simp [coeff, h0]
  · simp [not_le.mpr hlt, ne_of_gt hlt]

/-- Weighted composition at a fixed degree uses only the displayed finite Taylor jet of the germ. -/
theorem transfer_coeff_composition {e h g : ℂ → ℂ} (he : AnalyticAt ℂ e 0)
    (hh : AnalyticAt ℂ h 0) (hz : h 0 = 0) (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    coeff n (fun z => e z * g (h z)) =
      ∑ j ∈ Finset.range (n+1), coeff j g * coeff n (fun z => e z * h z ^ j) := by
  obtain ⟨b, hb, _, hfac⟩ := factor_schwarz_germ hh hz
  obtain ⟨u, hu, hTaylor⟩ := hg.exists_eq_sum_add_pow_mul (n+1)
  let t (j : ℕ) (z : ℂ) := coeff j g * (e z * h z ^ j)
  let v (z : ℂ) := e z * b z ^ (n+1) * u (h z)
  have ht (j) : AnalyticAt ℂ (t j) 0 := analyticAt_const.fun_mul (he.fun_mul (hh.fun_pow j))
  have hv : AnalyticAt ℂ v 0 := (he.fun_mul (hb.fun_pow _)).fun_mul (hu.comp_of_eq hh hz)
  have hs : AnalyticAt ℂ (fun z => ∑ j ∈ Finset.range (n+1), t j z) 0 :=
    Finset.analyticAt_fun_sum _ fun j _ => ht j
  have hf : (fun z => e z * g (h z)) = (fun z =>
      (∑ j ∈ Finset.range (n+1), t j z) + z^(n+1) * v z) := by
    funext z
    rw [hTaylor, mul_add, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro j _
      simp only [t, coeff, smul_eq_mul]
      ring
    · simp only [v, smul_eq_mul]
      nth_rw 1 [hfac z]
      rw [mul_pow]
      ring
  rw [hf]
  have hzv := mul_pow_coeff hv n (n+1)
  simp only [Nat.not_succ_le_self, ite_false] at hzv
  unfold coeff at hzv ⊢
  rw [iteratedDeriv_fun_add hs.contDiffAt (g := fun z => z^(n+1) * v z) (ContDiffAt.mul (by fun_prop) hv.contDiffAt),
    add_div, hzv, add_zero, iteratedDeriv_fun_sum (fun j _ => (ht j).contDiffAt), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  simp [t, coeff, iteratedDeriv_const_mul_field, mul_div_assoc]

/-- Degree zero already transfers with the original weight. -/
theorem transfer_degree_zero {e h : ℂ → ℂ} (he : IsWeight e) (hh : IsSchwarz h) :
    ∃ E : ℂ → ℂ, IsWeight E ∧ E 0 = e 0 * deriv h 0 ^ 0 ∧
      ∀ g : ℂ → ℂ, AnalyticAt ℂ g 0 →
        coeff 0 (fun z => e z * g (h z)) = coeff 0 (fun w => E w * g w) := by
  exact ⟨e, he, by simp, fun g _ => by simp [coeff, hh.2.2]⟩

/-- Cauchy's coefficient formula with normalized angular measure. -/
theorem transfer_coeff_average {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DiffContOnCl ℂ f (ball 0 r)) (n : ℕ) :
    Real.circleAverage (fun z => z⁻¹ ^ n * f z) 0 r = coeff n f := by
  rw [Real.circleAverage_eq_circleIntegral hr.ne']
  have h : (fun z : ℂ => (z - 0)⁻¹ • (z⁻¹ ^ n * f z)) =
      (fun z => (1 / (z - 0) ^ (n + 1)) • f z) := by
    funext z
    simp [pow_succ, mul_comm, mul_left_comm]
  rw [h, hf.circleIntegral_one_div_sub_center_pow_smul hr n]
  simp [coeff, smul_eq_mul, div_eq_mul_inv, ← mul_assoc]
  ring

private theorem transfer_norm_coeff {f : ℂ → ℂ} (hf : IsWeight f) (n : ℕ) :
    ‖coeff n f‖ ≤ 1 := by
  have hbound (r : ℝ) (hr : 0 < r) (hr' : r < 1) : r^n * ‖coeff n f‖ ≤ 1 := by
    have hsd : sphere (0 : ℂ) r ⊆ disk :=
      sphere_subset_closedBall.trans (closedBall_subset_ball hr')
    have hne (z : ℂ) (hz : z ∈ sphere 0 r) : z ≠ 0 := ne_of_mem_sphere hz hr.ne'
    have hc : ContinuousOn (fun z : ℂ => z⁻¹ ^ n * f z) (sphere 0 r) :=
      ((continuousOn_id.inv₀ hne).pow _).mul (hf.1.continuousOn.mono hsd)
    rw [← transfer_coeff_average hr (hf.1.differentiableOn.diffContOnCl_ball
      (closedBall_subset_ball hr')) n]
    have hle := Real.norm_circleAverage_le_circleAverage_norm
      (f := fun z : ℂ => z⁻¹ ^ n * f z) (c := 0) (R := r)
    apply (mul_le_mul_of_nonneg_left hle (pow_nonneg hr.le n)).trans
    have hlim := Real.circleAverage_mono_on_of_le_circle (hc.norm.circleIntegrable hr.le)
      (a := r⁻¹ ^ n) (by
        intro z hz
        rw [abs_of_pos hr] at hz
        simpa [norm_mul, norm_pow, norm_inv, mem_sphere_zero_iff_norm.mp hz]
          using mul_le_mul_of_nonneg_left (hf.2 z (hsd hz)) (pow_nonneg (inv_nonneg.mpr hr.le) n))
    exact (mul_le_mul_of_nonneg_left hlim (pow_nonneg hr.le n)).trans_eq
      (by rw [← mul_pow, mul_inv_cancel₀ hr.ne', one_pow])
  apply le_of_tendsto (f := fun r : ℝ => r^n * ‖coeff n f‖) (x := 𝓝[<] (1 : ℝ))
  · simpa [Pi.mul_def, Pi.pow_def] using ((continuous_id.pow n).mul continuous_const).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[<] (1 : ℝ) ≤ 𝓝 1)
  · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr using
      hbound r hr.1 hr.2

/-- The source-circle Poisson kernel has mean one after composition with a Schwarz map. -/
theorem transfer_poisson_mass {h : ℂ → ℂ} (hh : IsSchwarz h) {r : ℝ} (hr : 0 < r)
    (hr' : r < 1) {w : ℂ} (hw : ‖w‖ = 1) :
    Real.circleAverage (fun z => poissonKernel 0 (h z) w) 0 r = 1 := by
  have ha (z : ℂ) (hz : z ∈ disk) : AnalyticAt ℂ (fun v => (w + h v) / (w - h v)) z := by
    refine (analyticAt_const.fun_add (hh.1 z hz)).fun_div (analyticAt_const.fun_sub (hh.1 z hz)) ?_
    exact sub_ne_zero.mpr (fun heq => (mem_ball_zero_iff.mp (hh.2.1 hz)).ne
      ((congrArg norm heq).symm.trans hw))
  have hav : InnerProductSpace.HarmonicOnNhd (fun z => ((w + h z) / (w - h z)).re)
      (closedBall 0 |r|) := by
    rw [abs_of_pos hr]
    exact fun z hz => (ha z (closedBall_subset_ball hr' hz)).harmonicAt_re
  simpa [poissonKernel_eq_re_herglotzRieszKernel, herglotzRieszKernel_def, hh.2.2,
    show w ≠ 0 from norm_ne_zero_iff.mp (hw.trans_ne one_ne_zero)] using hav.circleAverage_eq

/-- Compactness in the coefficient topology of the closed unit ball of disk functions. -/
theorem transfer_weight_subsequence (f : ℕ → ℂ → ℂ) (hf : ∀ m, IsWeight (f m)) :
    ∃ E : ℂ → ℂ, IsWeight E ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ k, Tendsto (fun m => coeff k (f (φ m))) atTop (𝓝 (coeff k E)) := by
  let B := closedBall (0 : ℂ) 1
  let : CompactSpace B := inferInstanceAs (CompactSpace (closedBall (0 : ℂ) 1))
  let seq (m k : ℕ) : B := ⟨coeff k (f m), mem_closedBall_zero_iff.mpr
    (transfer_norm_coeff (hf m) k)⟩
  obtain ⟨b, φ, hφ, hb⟩ := CompactSpace.tendsto_subseq seq
  let a (k : ℕ) : ℂ := b k
  have ha (k : ℕ) : ‖a k‖ ≤ 1 := mem_closedBall_zero_iff.mp (b k).property
  have hlim (k : ℕ) : Tendsto (fun m => coeff k (f (φ m))) atTop (𝓝 (a k)) :=
    continuous_subtype_val.continuousAt.tendsto.comp ((tendsto_pi_nhds.mp hb) k)
  let p := FormalMultilinearSeries.ofScalars ℂ a
  have hrad : (1 : ENNReal) ≤ p.radius := by
    apply p.le_radius_of_bound (r := (1 : NNReal)) 1
    simpa [p, FormalMultilinearSeries.ofScalars_norm] using ha
  have hE : AnalyticOnNhd ℂ p.sum disk := by
    apply p.analyticOnNhd.mono
    exact (show disk = eball (0 : ℂ) (1 : ENNReal) by exact (Metric.eball_coe (ε := (1 : NNReal))).symm).le.trans
      (eball_subset_eball hrad)
  have hcoeff (k : ℕ) : coeff k p.sum = a k := by
    have hp := (p.hasFPowerSeriesOnBall (lt_of_lt_of_le zero_lt_one hrad)).hasFPowerSeriesAt
    have heq := (hE 0 transfer_zero_mem).hasFPowerSeriesAt.eq_formalMultilinearSeries hp
    simpa [p, coeff] using congrArg (fun q : FormalMultilinearSeries ℂ ℂ ℂ => q.coeff k) heq
  refine ⟨p.sum, ⟨hE, ?_⟩, φ, hφ, fun k => hcoeff k ▸ hlim k⟩
  intro w hw
  have hw' := mem_ball_zero_iff.mp hw
  have hsum := tendsto_tsum_of_dominated_convergence (summable_geometric_of_lt_one
    (norm_nonneg w) hw') (fun k => (hlim k).mul_const (w^k)) (Eventually.of_forall
    (fun m k => by
      rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_left (by positivity) (transfer_norm_coeff (hf (φ m)) k)))
  have ht (m) : ∑' k, coeff k (f m) * w^k = f m w := by
    simpa [coeff, div_eq_inv_mul, disk] using
      (Complex.taylorSeries_eq_on_ball' (c := 0) hw (hf m).1.differentiableOn)
  change ‖FormalMultilinearSeries.ofScalarsSum a w‖ ≤ 1
  rw [FormalMultilinearSeries.ofScalars_sum_eq]
  simp only [smul_eq_mul]
  apply le_of_tendsto hsum.norm
  exact Eventually.of_forall fun m => (ht (φ m)) ▸ (hf (φ m)).2 w hw

private abbrev Boundary (r : ℝ) := sphere (0 : ℂ) r

private def boundaryValues {r : ℝ} (f : C(Boundary r, ℂ)) (z : ℂ) : ℂ := by
  classical
  exact if hz : z ∈ Boundary r then f ⟨z, hz⟩ else 0

private theorem boundaryValues_cont {r : ℝ} (f : C(Boundary r, ℂ)) :
    ContinuousOn (boundaryValues f) (Boundary r) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  convert f.continuous using 1
  funext x
  simp [Set.domRestrict, boundaryValues]

private def boundaryAverage {r : ℝ} (hr : 0 < r) : C(Boundary r, ℂ) →L[ℂ] ℂ := by
  classical
  let L : C(Boundary r, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun f => Real.circleAverage (boundaryValues f) 0 r
      map_add' := fun f g => by
        rw [← Real.circleAverage_fun_add ((boundaryValues_cont f).circleIntegrable hr.le)
          ((boundaryValues_cont g).circleIntegrable hr.le)]
        exact Real.circleAverage_congr_sphere (by
          intro z hz
          rw [abs_of_pos hr] at hz
          simp [boundaryValues, mem_sphere_zero_iff_norm.mp hz])
      map_smul' := fun c f => by
        change _ = c • _
        rw [← Real.circleAverage_fun_smul]
        exact Real.circleAverage_congr_sphere (by
          intro z hz
          rw [abs_of_pos hr] at hz
          simp [boundaryValues, mem_sphere_zero_iff_norm.mp hz]) }
  refine L.mkContinuous 1 fun f => ?_
  rw [one_mul]
  exact Real.norm_circleAverage_le_circleAverage_norm.trans
    (Real.circleAverage_mono_on_of_le_circle ((boundaryValues_cont f).norm.circleIntegrable hr.le)
      (fun z hz => by
        rw [abs_of_pos hr] at hz
        simpa [boundaryValues, mem_sphere_zero_iff_norm.mp hz] using f.norm_coe_le_norm ⟨z,hz⟩))

private theorem boundaryAverage_eq {r : ℝ} (hr : 0 < r) (F : C(Boundary r, ℂ))
    (g : ℂ → ℂ) (hg : ∀ z : Boundary r, F z = g z) :
    boundaryAverage hr F = Real.circleAverage g 0 r := by
  apply Real.circleAverage_congr_sphere
  intro z hz
  rw [abs_of_pos hr] at hz
  simpa [boundaryValues, mem_sphere_zero_iff_norm.mp hz] using hg ⟨z,hz⟩

open scoped ComplexConjugate

private theorem transfer_kernel_identity {w a : ℂ} (hw : ‖w‖ = 1) (ha : ‖a‖ < 1) (n : ℕ) :
    (∑ k ∈ Finset.range (n+1), w^k * a^(n-k)) +
      w^(n+1) * conj a / (1 - w * conj a) + a^(n+1) / (w-a) =
      w^n * (poissonKernel 0 a w : ℂ) := by
  have hwa : w ≠ a := fun h => ha.ne ((congrArg norm h).symm.trans hw)
  have hw0 := norm_ne_zero_iff.mp (hw.trans_ne one_ne_zero)
  have hc : conj w = w⁻¹ := by
    apply (mul_right_inj' hw0).mp
    simp [Complex.mul_conj', hw, hw0]
  have hd : 1 - w * conj a ≠ 0 := sub_ne_zero.mpr fun h => by
    have hh := congrArg norm h
    simp [hw] at hh
    linarith
  have hd' : w⁻¹ - conj a ≠ 0 := by
    rw [← hc, ← map_sub]
    exact (map_ne_zero _).mpr (sub_ne_zero.mpr hwa)
  rw [show (∑ k ∈ Finset.range (n+1), w^k * a^(n-k)) =
      (w^(n+1)-a^(n+1))/(w-a) by simpa using geom₂_sum hwa (n+1)]
  simp only [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply,
    herglotzRieszKernel_def, sub_zero]
  rw [Complex.re_eq_add_conj]
  simp only [map_div₀, map_add, map_sub, hc, pow_succ]
  field_simp [hd, hd', hw0, sub_ne_zero.mpr hwa]
  ring

private theorem transfer_scaled_average {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f (ball 0 r)) (n : ℕ) :
    Real.circleAverage (fun z => ((r : ℂ)/z)^n * f z) 0 r = (r : ℂ)^n * coeff n f := by
  simpa [mul_pow, div_eq_mul_inv, ← inv_pow, mul_assoc, smul_eq_mul] using
    (Real.circleAverage_fun_smul (a := (r : ℂ)^n) (f := fun z : ℂ => z⁻¹^n * f z)
      (c := 0) (R := r)).trans (congrArg ((r : ℂ)^n • ·) (transfer_coeff_average hr hf n))

private def reversedJet (c : ℕ → ℂ) (n : ℕ) (v : ℂ → ℂ) (w : ℂ) : ℂ :=
  (∑ k ∈ Finset.range (n+1), w^k * c k) + w^(n+1) * v w

private theorem coeff_reversedJet (c : ℕ → ℂ) (n : ℕ) {v : ℂ → ℂ} (hv : AnalyticAt ℂ v 0)
    (k : ℕ) (hk : k ≤ n) : coeff k (reversedJet c n v) = c k := by
  have ht := mul_pow_coeff hv k (n+1)
  simp only [show ¬ n+1 ≤ k by omega, ite_false, coeff] at ht
  unfold reversedJet coeff
  rw [iteratedDeriv_fun_add (f := fun w : ℂ => ∑ i ∈ Finset.range (n+1), w^i * c i)
    (by exact (Finset.analyticAt_fun_sum _ fun i _ => by fun_prop).contDiffAt)
    (g := fun w => w^(n+1) * v w) (ContDiffAt.mul (by fun_prop) hv.contDiffAt), add_div, ht, add_zero,
    iteratedDeriv_fun_sum (fun i _ => by fun_prop)]
  simp only [iteratedDeriv_mul_const_field, iteratedDeriv_fun_pow_zero, Nat.cast_ite,
    Nat.cast_zero, ite_mul, zero_mul, Finset.sum_ite_eq, ite_eq_left (show k ∈ Finset.range (n+1) by simp; omega)]
  field_simp [show (k.factorial : ℂ) ≠ 0 by exact_mod_cast k.factorial_ne_zero]

/-- At each interior radius the Poisson construction gives a bounded multiplier with
the desired jet scaled by the radius to the chosen degree. -/
theorem transfer_at_radius {e h : ℂ → ℂ} (he : IsWeight e) (hh : IsSchwarz h)
    (n : ℕ) {r : ℝ} (hr : 0 < r) (hr' : r < 1) :
    ∃ F : ℂ → ℂ, IsWeight F ∧ ∀ k ≤ n,
      coeff k F = (r : ℂ)^n * coeff n (fun z => e z * h z^(n-k)) := by
  classical
  have hs : Boundary r ⊆ disk := sphere_subset_closedBall.trans (closedBall_subset_ball hr')
  let H : C(Boundary r, ℂ) := ⟨_, (hh.1.continuousOn.mono hs).domRestrict⟩
  let U : C(Boundary r, ℂ) := ⟨fun z => ((r : ℂ)/(z : ℂ))^n * e z,
    ((((continuousOn_const.div continuousOn_id (fun z hz => ne_of_mem_sphere hz hr.ne')).pow n).mul
      (he.1.continuousOn.mono hs)).domRestrict)⟩
  let A := boundaryAverage hr
  let c (k : ℕ) := A (U * H^(n-k))
  let den (w : ℂ) : C(Boundary r, ℂ) := 1 - w • star H
  let v (w : ℂ) := A (U * star H * Ring.inverse (den w))
  have hH (z : Boundary r) : ‖h z‖ < 1 := mem_ball_zero_iff.mp (hh.2.1 (hs z.property))
  have hu {w : ℂ} (hw : ‖w‖ ≤ 1) : IsUnit (den w) := by
    apply (den w).isUnit_iff_forall_ne_zero.mpr
    intro z
    change 1 - w * conj (h z) ≠ 0
    apply sub_ne_zero.mpr
    intro heq
    have hlt : ‖w * conj (h z)‖ < 1 := by
      rw [norm_mul, Complex.norm_conj]
      exact (mul_le_of_le_one_left (norm_nonneg _) hw).trans_lt (hH z)
    simp [← heq] at hlt
  have hv {w : ℂ} (hw : ‖w‖ ≤ 1) : AnalyticAt ℂ v w := by
    apply (A.analyticAt _).comp (f := fun t => U * star H * Ring.inverse (den t))
    apply analyticAt_const.fun_mul
    exact (analyticOnNhd_inverse (𝕜 := ℂ) (A := C(Boundary r, ℂ)) (den w) (hu hw)).comp
      (f := den) (by dsimp [den]; fun_prop)
  have hc (k : ℕ) : c k = (r : ℂ)^n * coeff n (fun z => e z * h z^(n-k)) := by
    rw [← transfer_scaled_average hr (f := fun z => e z * h z^(n-k))
      ((he.1.mul (hh.1.fun_pow _)).differentiableOn.diffContOnCl_ball
        (closedBall_subset_ball hr'))]
    apply boundaryAverage_eq
    intro z
    exact mul_assoc _ _ _
  let F := reversedJet c n v
  have hFa {w : ℂ} (hw : ‖w‖ ≤ 1) : AnalyticAt ℂ F w := by
    exact (Finset.analyticAt_fun_sum _ fun k _ => by fun_prop).fun_add
      ((analyticAt_id.fun_pow _).fun_mul (hv hw))
  refine ⟨F, ⟨fun w hw => hFa (mem_ball_zero_iff.mp hw).le, ?_⟩,
    fun k hk => (coeff_reversedJet c n (hv (by simp)) k hk).trans (hc k)⟩
  have hFd : DifferentiableOn ℂ F (closedBall 0 1) := fun z hz =>
    (hFa (mem_closedBall_zero_iff.mp hz)).differentiableAt.differentiableWithinAt
  intro y hy
  apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
    (hFd.diffContOnCl_ball subset_rfl) ?_ (subset_closure hy)
  intro w hw
  have hw1 := mem_sphere_zero_iff_norm.mp (frontier_ball_subset_sphere hw)
  let P (z : ℂ) := poissonKernel 0 (h z) w
  let phase (z : ℂ) := ((r : ℂ)/z)^n * e z
  let correction (z : ℂ) := e z / (w - h z)
  have hne (z : ℂ) (hz : z ∈ disk) : w - h z ≠ 0 :=
    sub_ne_zero.mpr fun eq => (mem_ball_zero_iff.mp (hh.2.1 hz)).ne ((congrArg norm eq).symm.trans hw1)
  have hcorr : AnalyticOnNhd ℂ correction disk := fun z hz =>
    (he.1 z hz).fun_div (analyticAt_const.fun_sub (hh.1 z hz)) (hne z hz)
  have hP : ContinuousOn P (Boundary r) := by
    simp only [P, poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply,
      herglotzRieszKernel_def, sub_zero]
    apply Complex.continuous_re.comp_continuousOn
    exact (continuousOn_const.add (hh.1.continuousOn.mono hs)).div
      (continuousOn_const.sub (hh.1.continuousOn.mono hs)) (fun z hz => hne z (hs hz))
  have hphase : ContinuousOn phase (Boundary r) :=
    (((continuousOn_const.div continuousOn_id (fun z hz => ne_of_mem_sphere hz hr.ne')).pow n).mul
      (he.1.continuousOn.mono hs))
  have hvan := transfer_scaled_average hr
    ((hcorr.mul (hh.1.fun_pow (n+1))).differentiableOn.diffContOnCl_ball
      (closedBall_subset_ball hr')) n
  rw [transfer_moment (hcorr 0 transfer_zero_mem) (hh.1 0 transfer_zero_mem) hh.2.2
    n (n+1) (by omega)] at hvan
  simp only [Nat.succ_ne_self, ite_false, mul_zero] at hvan
  have hcancel : Real.circleAverage (fun z => phase z * (h z^(n+1)/(w-h z))) 0 r = 0 := by
    convert hvan using 2
    funext z
    dsimp [phase, correction]
    ring
  have hbc : F w = Real.circleAverage (fun z => phase z * (w^n * (P z : ℂ))) 0 r := by
    have hav : F w = A ((∑ k ∈ Finset.range (n+1), w^k • (U * H^(n-k))) +
        w^(n+1) • (U * star H * Ring.inverse (den w))) := by simp [F, reversedJet, c, v]
    rw [hav]
    let M := (∑ k ∈ Finset.range (n+1), w^k • (U * H^(n-k))) +
      w^(n+1) • (U * star H * Ring.inverse (den w))
    change Real.circleAverage (boundaryValues M) 0 r = _
    trans Real.circleAverage (boundaryValues M) 0 r +
      Real.circleAverage (fun z => phase z * (h z^(n+1)/(w-h z))) 0 r
    · rw [hcancel, add_zero]
    rw [← Real.circleAverage_fun_add]
    · apply Real.circleAverage_congr_sphere
      intro z hz
      rw [abs_of_pos hr] at hz
      let x : Boundary r := ⟨z,hz⟩
      have hinv : Ring.inverse (den w) x = (1 - w * conj (h z))⁻¹ := by
        have eq := congrArg (fun f : C(Boundary r, ℂ) => f x) (Ring.inverse_mul_cancel _ (hu hw1.le))
        change Ring.inverse (den w) x * (1 - w * conj (h z)) = 1 at eq
        exact eq_inv_of_mul_eq_one_left eq
      change boundaryValues M z + _ = _
      dsimp only [M]
      simp only [boundaryValues, dite_eq_left hz, ContinuousMap.add_apply, ContinuousMap.sum_apply,
        ContinuousMap.smul_apply, ContinuousMap.mul_apply, ContinuousMap.pow_apply, smul_eq_mul]
      change (∑ k ∈ Finset.range (n+1), w^k * (phase z * h z^(n-k))) +
        w^(n+1) * (phase z * conj (h z) * Ring.inverse (den w) x) + _ = _
      change _ = phase z * (w^n * (poissonKernel 0 (h z) w : ℂ))
      rw [hinv, ← transfer_kernel_identity hw1 (show ‖h z‖ < 1 from hH x) n]
      simp only [mul_add, Finset.mul_sum, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    · exact (boundaryValues_cont _).circleIntegrable hr.le
    · exact (hphase.mul (((hh.1.continuousOn.mono hs).pow _).div
        (continuousOn_const.sub (hh.1.continuousOn.mono hs)) (fun z hz => hne z (hs hz)))).circleIntegrable hr.le
  rw [hbc, ← transfer_poisson_mass hh hr hr' hw1]
  refine Real.norm_circleAverage_le_circleAverage_norm.trans (Real.circleAverage_mono
    ((hphase.mul (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hP))).norm.circleIntegrable hr.le)
    (hP.circleIntegrable hr.le) ?_)
  intro z hz
  rw [abs_of_pos hr] at hz
  have hnon : 0 ≤ P z := by
    simp only [P, poissonKernel_def, sub_zero, hw1, one_pow]
    exact div_nonneg (sub_nonneg.mpr (pow_le_one₀ (norm_nonneg _) (hH ⟨z,hz⟩).le)) (sq_nonneg _)
  simpa [phase, norm_mul, norm_div, norm_pow, mem_sphere_zero_iff_norm.mp hz,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, hr.ne', hw1, abs_of_nonneg hnon] using
    mul_le_of_le_one_left hnon (he.2 z (hs hz))

/-- Products with the transferred weight use its reversed finite jet. -/
theorem transfer_coeff_product {E g : ℂ → ℂ} (hE : AnalyticAt ℂ E 0)
    (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    coeff n (fun z => E z * g z) =
      ∑ j ∈ Finset.range (n+1), coeff j g * coeff (n-j) E := by
  rw [transfer_coeff_composition (h := fun z => z) hE analyticAt_id rfl hg n]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [show (fun z : ℂ => E z * z ^ j) = (fun z => z ^ j * E z) by funext z; ring,
    mul_pow_coeff hE n j, ite_eq_left hj']

/-- Weighted transfer for every degree. The limiting multiplier is chosen before the test germ. -/
theorem transfer : TransferClaim := by
  intro h hh e he n
  obtain ⟨r, _, hr, hr1⟩ := exists_seq_strictMono_tendsto' (show (0 : ℝ) < 1 by norm_num)
  choose F hF hjet using fun m => transfer_at_radius he hh n (hr m).1 (hr m).2
  obtain ⟨E, hE, φ, hφ, hlim⟩ := transfer_weight_subsequence F hF
  have he0 := he.1 0 transfer_zero_mem
  have hh0 := hh.1 0 transfer_zero_mem
  have hE0 := hE.1 0 transfer_zero_mem
  have hm (k : ℕ) (hk : k ≤ n) : coeff k E = coeff n (fun z => e z * h z^(n-k)) := by
    apply tendsto_nhds_unique (hlim k)
    simp_rw [hjet _ k hk]
    simpa using (((Complex.continuous_ofReal.continuousAt.tendsto.comp
      (hr1.comp hφ.tendsto_atTop)).pow n).mul_const (coeff n (fun z => e z * h z^(n-k))))
  refine ⟨E, hE, ?_, fun g hg => ?_⟩
  · simpa [coeff] using (hm 0 (Nat.zero_le n)).trans
      (by simpa using transfer_moment he0 hh0 hh.2.2 n n le_rfl)
  · rw [transfer_coeff_composition he0 hh0 hh.2.2 hg, transfer_coeff_product hE0 hg]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    rw [hm _ (Nat.sub_le ..), Nat.sub_sub_self hj']

end Goodman
