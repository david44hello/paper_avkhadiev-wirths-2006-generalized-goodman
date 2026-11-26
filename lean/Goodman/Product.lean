-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Goodman.CoefficientClaims

noncomputable section

open Set Filter Metric
open scoped Topology

namespace Goodman

private lemma origin_mem : (0 : ℂ) ∈ disk := mem_ball_self zero_lt_one

private lemma disk_open : IsOpen disk := isOpen_ball

private lemma sq_mem {z : ℂ} (hz : z ∈ disk) : z ^ 2 ∈ disk := by
  simp only [disk, mem_ball, dist_zero_right, norm_pow] at *
  exact pow_lt_one₀ (norm_nonneg _) hz (by decide)

private lemma slope_analytic {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f disk) :
    AnalyticOnNhd ℂ (dslope f 0) disk :=
  ((Complex.differentiableOn_dslope (disk_open.mem_nhds origin_mem)).2
    hf.differentiableOn).analyticOnNhd disk_open

/-- The square root of the removable quotient, normalized at the origin. -/
theorem exists_normalized_square_factor {F : ℂ → ℂ} (hF : IsS F) :
    ∃ M : ℂ → ℂ, AnalyticOnNhd ℂ M disk ∧ M 0 = 1 ∧
      (∀ z ∈ disk, M z ≠ 0) ∧ ∀ z ∈ disk, F z = z * M z ^ 2 := by
  obtain ⟨hFa, hFi, hF0, hF1⟩ := hF
  let g := dslope F 0
  have hg : AnalyticOnNhd ℂ g disk := slope_analytic hFa
  have hg0 : g 0 = 1 := by simp [g, hF1]
  have heq (z : ℂ) : z * g z = F z := by
    simpa [g, hF0] using sub_smul_dslope F (0 : ℂ) z
  have hnz (z : ℂ) (hz : z ∈ disk) : g z ≠ 0 := by
    intro h
    have hz0 := hFi hz origin_mem (by rw [← heq, h, mul_zero, hF0])
    subst z
    exact one_ne_zero (hg0.symm.trans h)
  let _ : ContractibleSpace disk :=
    (convex_ball (0 : ℂ) (1 : ℝ)).contractibleSpace ⟨0, origin_mem⟩
  have hsc : IsSimplyConnected disk := inferInstanceAs (SimplyConnectedSpace disk)
  obtain ⟨u, huc, hu⟩ := Complex.exists_continuousOn_pow_eq hsc disk_open
    hg.continuousOn (by rintro ⟨z, hz, he⟩; exact hnz z hz he) (n := 2) (by decide)
  have hun (z : ℂ) (hz : z ∈ disk) : u z ≠ 0 := by
    intro h
    exact hnz z hz (by rw [← hu, h]; norm_num)
  have hua : AnalyticOnNhd ℂ u disk := by
    apply DifferentiableOn.analyticOnNhd _ disk_open
    intro z hz
    have hcomp : (fun w : ℂ => w ^ 2) ∘ u =ᶠ[𝓝 z] g := Eventually.of_forall hu
    exact (HasDerivAt.of_comp_left ((huc z hz).continuousAt (disk_open.mem_nhds hz))
      (hasDerivAt_pow 2 (u z)) (hg z hz).differentiableAt.hasDerivAt
      (by simp [hun z hz]) hcomp).differentiableAt.differentiableWithinAt
  have hu0 : u 0 ^ 2 = 1 := (hu 0).trans hg0
  refine ⟨fun z => u z / u 0, fun z hz => (hua z hz).div analyticAt_const (hun 0 origin_mem),
    div_self (hun 0 origin_mem), fun z hz => div_ne_zero (hun z hz) (hun 0 origin_mem), ?_⟩
  intro z _
  rw [div_pow, hu0, div_one, hu, heq]

/-- The normalized odd schlicht function whose square is the square pullback of `F`. -/
theorem exists_odd_square_factor {F : ℂ → ℂ} (hF : IsS F) :
    ∃ M : ℂ → ℂ, AnalyticOnNhd ℂ M disk ∧ (∀ z ∈ disk, F z = z * M z ^ 2) ∧
      IsS (fun z => z * M (z ^ 2)) ∧
      (∀ z ∈ disk, (-z) * M ((-z) ^ 2) = -(z * M (z ^ 2))) ∧
      ∀ z ∈ disk, (z * M (z ^ 2)) ^ 2 = F (z ^ 2) := by
  obtain ⟨M, hM, h0, hnz, hfac⟩ := exists_normalized_square_factor hF
  have ha {z : ℂ} (hz : z ∈ disk) :
      AnalyticAt ℂ (fun w => M (w ^ 2)) z :=
    (hM _ (sq_mem hz)).comp (f := fun w : ℂ => w ^ 2) (analyticAt_id.fun_pow 2)
  have hs (z : ℂ) (hz : z ∈ disk) : (z * M (z ^ 2)) ^ 2 = F (z ^ 2) := by
    rw [mul_pow, ← hfac _ (sq_mem hz)]
  refine ⟨M, hM, hfac, ⟨fun z hz => analyticAt_id.mul (ha hz), ?_, by simp, ?_⟩,
    fun z _ => by simp, hs⟩
  · intro z hz w hw h
    have he := hF.2.1 (sq_mem hz) (sq_mem hw)
      ((hs z hz).symm.trans ((congrArg (· ^ 2) h).trans (hs w hw)))
    change z * M (z ^ 2) = w * M (w ^ 2) at h
    rw [he] at h
    exact mul_right_cancel₀ (hnz (w ^ 2) (sq_mem hw)) h
  · simpa [h0, Pi.mul_def, id_def] using ((hasDerivAt_id (0 : ℂ)).mul
      (ha origin_mem).differentiableAt.hasDerivAt).deriv

private lemma coeff_germ (n : ℕ) {f g : ℂ → ℂ} (h : f =ᶠ[𝓝 0] g) :
    coeff n f = coeff n g := by rw [coeff, coeff, h.iteratedDeriv_eq n]

/-- Leibniz's rule with the factorials absorbed into the Taylor coefficients. -/
theorem coeff_product_convolution (n : ℕ) {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    coeff n (fun z => f z * g z) =
      ∑ j ∈ Finset.range (n + 1), coeff j f * coeff (n - j) g := by
  simp only [coeff, iteratedDeriv_fun_mul hf.contDiffAt hg.contDiffAt, Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Nat.cast_choose ℂ (by simpa [Nat.lt_succ_iff] using hj : j ≤ n)]
  field_simp [Nat.factorial_ne_zero]

private lemma coeff_shift (n d : ℕ) {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) :
    coeff (n + d) (fun z => z ^ d * g z) = coeff n g := by
  rw [coeff_product_convolution _ (f := fun z : ℂ => z ^ d) (analyticAt_id.fun_pow d) hg,
    Finset.sum_eq_single d]
  · simp only [coeff, iteratedDeriv_fun_pow_zero, Nat.add_sub_cancel]
    simp [Nat.factorial_ne_zero]
  · intro i hi hid
    simp only [coeff, iteratedDeriv_fun_pow_zero, ite_eq_right hid, Nat.cast_zero, zero_div, zero_mul]
  · simp

private lemma slope_decomp (g : ℂ → ℂ) (z : ℂ) :
    g z = g 0 + z * dslope g 0 z := by
  have h := sub_smul_dslope g (0 : ℂ) z
  simpa using (eq_add_of_sub_eq' (by simpa using h.symm : g z - g 0 = z * dslope g 0 z))

private lemma coeff_dslope (j : ℕ) {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g disk) :
    coeff (j+1) g = coeff j (dslope g 0) := by
  rw [coeff_germ _ (Eventually.of_forall (slope_decomp g))]
  unfold coeff
  rw [iteratedDeriv_const_add (Nat.succ_pos _) ]
  simpa only [pow_one, coeff] using coeff_shift j 1 (slope_analytic hg 0 origin_mem)

private lemma analytic_sq_comp {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g disk) {z : ℂ}
    (hz : z ∈ disk) : AnalyticAt ℂ (fun w => g (w ^ 2)) z :=
  (hg _ (sq_mem hz)).comp (f := fun w : ℂ => w ^ 2) (analyticAt_id.fun_pow 2)

private lemma coeff_sq_comp (j : ℕ) {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g disk) :
    coeff (2*j) (fun z => g (z ^ 2)) = coeff j g := by
  induction j generalizing g with
  | zero => simp [coeff]
  | succ j ih =>
    rw [coeff_dslope j hg, ← ih (slope_analytic hg), Nat.mul_succ]
    rw [coeff_germ _ (Eventually.of_forall (fun z : ℂ => slope_decomp g (z ^ 2)))]
    unfold coeff
    rw [iteratedDeriv_const_add (by omega : 0 < 2*j+2)]
    exact coeff_shift (2*j) 2 (analytic_sq_comp (slope_analytic hg) origin_mem)

/-- Substitution of the square followed by multiplication by the coordinate
places the original coefficients at the odd indices. -/
theorem coeff_odd_square_pullback (j : ℕ) {M : ℂ → ℂ} (hM : AnalyticOnNhd ℂ M disk) :
    coeff (2*j+1) (fun z => z * M (z ^ 2)) = coeff j M := by
  rw [← coeff_sq_comp j hM]
  simpa only [pow_one] using coeff_shift (2*j) 1 (analytic_sq_comp hM origin_mem)

/-- Cauchy's formula with a continuous majorant. Only the majorant is
evaluated on the unit circle. -/
private theorem coeff_le_boundary_mean (n : ℕ) {g : ℂ → ℂ} {u : ℂ → ℝ}
    (hg : AnalyticOnNhd ℂ g disk) (hu : Continuous u)
    (hgu : ∀ z ∈ disk, ‖g z‖ ≤ u z) :
    ‖coeff n g‖ ≤ Real.circleAverage u 0 1 := by
  let S := {r : ℝ | ‖coeff n g‖ * r ^ n ≤ Real.circleAverage u 0 r}
  have hclosed : IsClosed S := isClosed_le (by fun_prop) (Real.Continuous.circleAverage hu)
  have hrad : Ioo (0 : ℝ) 1 ⊆ S := by
    intro r hr
    obtain ⟨hr0, hr1⟩ := hr
    have hsub : sphere (0 : ℂ) r ⊆ disk :=
      sphere_subset_closedBall.trans (closedBall_subset_ball hr1)
    have hnorm {z : ℂ} (hz : z ∈ sphere (0 : ℂ) r) : ‖z‖ = r := by
      simpa [mem_sphere] using hz
    have hnz {z : ℂ} (hz : z ∈ sphere (0 : ℂ) r) : z ≠ 0 :=
      norm_ne_zero_iff.mp ((hnorm hz).trans_ne hr0.ne')
    have hcauchy := (hg.differentiableOn.mono (closedBall_subset_ball hr1)
      ).circleIntegral_one_div_sub_center_pow_smul hr0 n
    have heq : Real.circleAverage (fun z : ℂ => g z / z ^ n) 0 r = coeff n g := by
      rw [Real.circleAverage_eq_circleIntegral hr0.ne']
      have he : (fun z : ℂ => (z - 0)⁻¹ • (g z / z ^ n)) =
          fun z : ℂ => (1 / (z - 0) ^ (n+1)) • g z := by
        funext z
        simp [smul_eq_mul, div_eq_mul_inv, pow_succ, mul_comm, mul_left_comm]
      rw [he, hcauchy, smul_eq_mul, smul_eq_mul, coeff]
      field_simp [Complex.two_pi_I_ne_zero]
    have hq : ContinuousOn (fun z : ℂ => g z / z ^ n) (sphere 0 r) :=
      (hg.continuousOn.mono hsub).div (continuous_id.pow n).continuousOn
        (fun _ hz => pow_ne_zero _ (hnz hz))
    have hle := Real.norm_circleAverage_le_circleAverage_norm
      (f := fun z : ℂ => g z / z ^ n) (c := 0) (R := r)
    rw [heq] at hle
    have hb : Real.circleAverage (fun z : ℂ => ‖g z / z ^ n‖) 0 r ≤
        Real.circleAverage (fun z => (r ^ n)⁻¹ • u z) 0 r := by
      apply Real.circleAverage_mono (f₂ := fun z => (r ^ n)⁻¹ • u z)
        (hq.norm.circleIntegrable hr0.le)
        ((hu.const_smul ((r ^ n)⁻¹)).continuousOn.circleIntegrable hr0.le)
      rw [abs_of_pos hr0]
      intro z hz
      rw [norm_div, norm_pow, hnorm hz, smul_eq_mul, mul_comm, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right (hgu z (hsub hz)) (by positivity)
    rw [Real.circleAverage_fun_smul, smul_eq_mul, mul_comm, ← div_eq_mul_inv] at hb
    exact (le_div_iff₀ (pow_pos hr0 n)).mp (hle.trans hb)
  have hmem : (1 : ℝ) ∈ closure (Ioo (0 : ℝ) 1) := by simp [closure_Ioo zero_ne_one]
  simpa [S] using (closure_minimal hrad hclosed hmem)

open scoped Polynomial

private lemma poly_analytic (P : ℂ[X]) (z : ℂ) : AnalyticAt ℂ (fun w => P.eval w) z :=
  P.differentiable.analyticAt _

private lemma coeff_poly (P : ℂ[X]) (n : ℕ) : coeff n (fun z => P.eval z) = P.coeff n := by
  have hd (j : ℕ) : iteratedDeriv j (fun z => P.eval z) =
      fun z => (Polynomial.derivative^[j] P).eval z := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [iteratedDeriv_succ, ih]
      funext z
      simp [Function.iterate_succ_apply']
  simp [coeff, hd, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative,
    Nat.descFactorial_self, nsmul_eq_mul, Nat.factorial_ne_zero]

private def truncPoly (b : ℕ → ℂ) (k : ℕ) : ℂ[X] :=
  ∑ j ∈ Finset.range k, Polynomial.monomial j (b j)

private lemma trunc_coeff (b : ℕ → ℂ) (k j : ℕ) :
    (truncPoly b k).coeff j = if j < k then b j else 0 := by
  classical
  simp [truncPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]

private lemma trunc_energy (b : ℕ → ℂ) (k : ℕ) :
    Real.circleAverage (fun z => ‖(truncPoly b k).eval z‖ ^ 2) 0 1 =
      ∑ j ∈ Finset.range k, ‖b j‖ ^ 2 := by
  rw [← Polynomial.sum_sq_norm_coeff_eq_circleAverage]
  have hsub : (truncPoly b k).support ⊆ Finset.range k := by
    intro j hj
    by_contra h
    simp [Polynomial.mem_support_iff, trunc_coeff, Finset.mem_range.mpr.mt h] at hj
  calc
    _ = ∑ j ∈ Finset.range k, ‖(truncPoly b k).coeff j‖ ^ 2 :=
      Finset.sum_subset hsub (fun j _ hj => by simp [Polynomial.notMem_support_iff.mp hj])
    _ = _ := Finset.sum_congr rfl fun j hj => by simp [trunc_coeff, Finset.mem_range.mp hj]

private lemma coeff_mul_congr_upto {k : ℕ} {f g p q : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (hp : AnalyticAt ℂ p 0) (hq : AnalyticAt ℂ q 0)
    (hfp : ∀ i < k, coeff i f = coeff i p) (hgq : ∀ i < k, coeff i g = coeff i q) :
    ∀ n < k, coeff n (fun z => f z * g z) = coeff n (fun z => p z * q z) := by
  intro n hn
  rw [coeff_product_convolution n hf hg, coeff_product_convolution n hp hq]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  rw [hfp i (by omega), hgq _ (by omega)]

/-- The finite coefficient pairing with a bounded analytic multiplier.
Truncating both Taylor series leaves this coefficient unchanged. -/
theorem weighted_coeff_pairing (n : ℕ) {f g E : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (hE : IsWeight E) :
    ‖coeff n (fun z => (f z * E z) * g z)‖ ≤
      ((∑ j ∈ Finset.range (n+1), ‖coeff j f‖ ^ 2) +
       (∑ j ∈ Finset.range (n+1), ‖coeff j g‖ ^ 2)) / 2 := by
  let P := truncPoly (fun i => coeff i f) (n+1)
  let Q := truncPoly (fun i => coeff i g) (n+1)
  have hp i (hi : i < n+1) : coeff i f = coeff i (fun z => P.eval z) := by
    simp [P, coeff_poly, trunc_coeff, hi]
  have hq i (hi : i < n+1) : coeff i g = coeff i (fun z => Q.eval z) := by
    simp [Q, coeff_poly, trunc_coeff, hi]
  have hE0 := hE.1 0 origin_mem
  rw [coeff_mul_congr_upto (f := fun z => f z * E z) (p := fun z => P.eval z * E z)
    (hf.mul hE0) hg ((poly_analytic P 0).mul hE0)
    (poly_analytic Q 0) (coeff_mul_congr_upto hf hE0 (poly_analytic P 0) hE0 hp
      (fun _ _ => rfl)) hq n (Nat.lt_succ_self n)]
  let u := fun z : ℂ => (2 : ℝ)⁻¹ • (‖P.eval z‖ ^ 2 + ‖Q.eval z‖ ^ 2)
  have hmean := coeff_le_boundary_mean n (u := u)
    (g := fun z => P.eval z * E z * Q.eval z)
    (fun z hz => ((poly_analytic P z).mul (hE.1 z hz)).mul (poly_analytic Q z))
    (by dsimp [u]; fun_prop) (by
      intro z hz
      simp only [u, smul_eq_mul, norm_mul]
      calc
        ‖P.eval z‖ * ‖E z‖ * ‖Q.eval z‖ ≤ ‖P.eval z‖ * 1 * ‖Q.eval z‖ := by
          gcongr
          exact hE.2 z hz
        _ ≤ _ := by nlinarith [sq_nonneg (‖P.eval z‖ - ‖Q.eval z‖)])
  dsimp only [u] at hmean
  rw [Real.circleAverage_fun_smul, Real.circleAverage_fun_add
    (f₁ := fun z => ‖P.eval z‖ ^ 2) (f₂ := fun z => ‖Q.eval z‖ ^ 2)
    ((P.continuous.norm.pow 2).continuousOn.circleIntegrable zero_le_one)
    ((Q.continuous.norm.pow 2).continuousOn.circleIntegrable zero_le_one),
    smul_eq_mul] at hmean
  simpa only [P, Q, trunc_energy, div_eq_inv_mul] using hmean

open scoped ComplexConjugate

/-- Multiplication by a disk weight contracts the squared norm of every
finite Taylor coefficient vector. Test the pairing against the reversed
conjugates of the output coefficients. -/
theorem finite_multiplier_contraction (k : ℕ) {f E : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hE : IsWeight E) :
    (∑ i ∈ Finset.range k, ‖coeff i (fun z => f z * E z)‖ ^ 2) ≤
      ∑ i ∈ Finset.range k, ‖coeff i f‖ ^ 2 := by
  cases k with
  | zero => simp
  | succ n =>
    let b := fun i => coeff i (fun z => f z * E z)
    let Q := truncPoly (fun j => conj (b (n-j))) (n+1)
    have hq (i : ℕ) (hi : i < n+1) :
        coeff i (fun z => Q.eval z) = conj (b (n-i)) := by
      simp [Q, coeff_poly, trunc_coeff, hi]
    have he : coeff n (fun z => (f z * E z) * Q.eval z) =
        ((∑ i ∈ Finset.range (n+1), ‖b i‖ ^ 2 : ℝ) : ℂ) := by
      rw [coeff_product_convolution _ (f := fun z => f z * E z)
        (hf.mul (hE.1 0 origin_mem)) (poly_analytic Q 0),
        Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := Finset.mem_range.mp hi
      rw [hq (n-i) (by omega), show n - (n - i) = i by omega]
      simp [b, Complex.mul_conj']
    have henergy : (∑ i ∈ Finset.range (n+1), ‖coeff i (fun z => Q.eval z)‖ ^ 2) =
        ∑ i ∈ Finset.range (n+1), ‖b i‖ ^ 2 := by
      calc
        _ = ∑ i ∈ Finset.range (n+1), ‖b (n-i)‖ ^ 2 := by
          exact Finset.sum_congr rfl fun i hi => by simp [hq _ (Finset.mem_range.mp hi)]
        _ = _ := by simpa using Finset.sum_range_reflect (fun i => ‖b i‖ ^ 2) (n+1)
    have hb := weighted_coeff_pairing n hf (poly_analytic Q 0) hE
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), henergy] at hb
    change (∑ i ∈ Finset.range (n+1), ‖b i‖ ^ 2) ≤ _
    linarith

/-- Robertson's inequality for odd schlicht functions implies the weighted
coefficient bound for every normalized schlicht function on the disk. -/
theorem product_of_robertson (hR : Robertson) : ProductClaim := by
  intro F hF E hE k hk
  obtain ⟨M, hM, hfac, hS, hodd, _⟩ := exists_odd_square_factor hF
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hr := hR _ hS hodd (n+1) hk
  simp_rw [coeff_odd_square_pullback _ hM] at hr
  have hM0 := hM 0 origin_mem
  have hshift := coeff_shift n 1 (g := fun z => M z * E z * M z)
    ((hM0.mul (hE.1 0 origin_mem)).mul hM0)
  have he : (fun z => F z * E z) =ᶠ[𝓝 0] fun z => z ^ 1 * ((M z * E z) * M z) := by
    filter_upwards [disk_open.mem_nhds origin_mem] with z hz
    rw [hfac z hz]
    ring
  rw [coeff_germ _ he, hshift]
  have hp := weighted_coeff_pairing n hM0 hM0 hE
  linarith

end Goodman
