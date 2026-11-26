-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
module

public import Goodman.Product
public import Goodman.CoefficientComposition

@[expose] public section

noncomputable section

open Filter Metric
open scoped Topology Polynomial

namespace Goodman

/-- The polynomial M_k formed from the first k Taylor coefficients at zero. -/
def productTaylorPoly (M : ℂ → ℂ) (k : ℕ) : ℂ[X] :=
  ∑ j ∈ Finset.range k, Polynomial.monomial j (coeff j M)

theorem productTaylorPoly_eval (M : ℂ → ℂ) (k : ℕ) (z : ℂ) :
    (productTaylorPoly M k).eval z = ∑ j ∈ Finset.range k, coeff j M * z ^ j := by
  simp [productTaylorPoly, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

theorem productTaylorPoly_coeff (M : ℂ → ℂ) (k j : ℕ) :
    (productTaylorPoly M k).coeff j = if j < k then coeff j M else 0 := by
  classical
  simp [productTaylorPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]

theorem coeff_polynomial_eval (P : ℂ[X]) (j : ℕ) : coeff j P.eval = P.coeff j := by
  have hd (i : ℕ) : iteratedDeriv i P.eval = (Polynomial.derivative^[i] P).eval := by
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [iteratedDeriv_succ, ih]
      funext z
      simp [Function.iterate_succ_apply']
  simp [coeff, hd, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative,
    Nat.descFactorial_self, nsmul_eq_mul, Nat.factorial_ne_zero]

/-- Agreement through degree k−1 is preserved under multiplication. -/
theorem coeff_product_congr_below {k : ℕ} {f g p q : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (hp : AnalyticAt ℂ p 0) (hq : AnalyticAt ℂ q 0)
    (hfp : ∀ i < k, coeff i f = coeff i p) (hgq : ∀ i < k, coeff i g = coeff i q) :
    ∀ n < k, coeff n (fun z => f z * g z) = coeff n (fun z => p z * q z) := by
  intro n hn
  rw [coeff_product_convolution n hf hg, coeff_product_convolution n hp hq]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  rw [hfp i (by omega), hgq _ (by omega)]

private theorem coeff_mul_coordinate {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    coeff (n+1) (fun z => z * g z) = coeff n g := by
  have hid (i : ℕ) : coeff i (fun z => z) = if i = 1 then 1 else 0 := by
    by_cases h : i = 1 <;> simp [coeff, iteratedDeriv_fun_id_zero, h]
  rw [coeff_product_convolution _ (f := fun z => z) analyticAt_id hg]
  simp [hid, ite_mul]

/-- Both equalities in the product lemma, for the same polynomial in both slots. -/
theorem product_truncation_identity {F M E : ℂ → ℂ} {k : ℕ} (hk : 1 ≤ k)
    (hM : AnalyticAt ℂ M 0) (hE : AnalyticAt ℂ E 0)
    (hfac : ∀ z ∈ disk, F z = z * M z ^ 2) :
    let P := productTaylorPoly M k
    coeff k (fun z => F z * E z) = coeff (k-1) (fun z => M z ^ 2 * E z) ∧
    coeff (k-1) (fun z => M z ^ 2 * E z) =
      coeff (k-1) (fun z => (P.eval z * E z) * P.eval z) := by
  dsimp only
  let P := productTaylorPoly M k
  have hp : AnalyticAt ℂ P.eval 0 := P.differentiable.analyticAt _
  have hjet (i : ℕ) (hi : i < k) : coeff i M = coeff i P.eval := by
    simp [P, coeff_polynomial_eval, productTaylorPoly_coeff, hi]
  constructor
  · have he : (fun z => F z * E z) =ᶠ[𝓝 0] fun z => z * (M z ^ 2 * E z) := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self zero_lt_one : (0 : ℂ) ∈ disk)]
        with z hz
      rw [hfac z hz, mul_assoc]
    rw [coeff_congr_of_eventuallyEq he]
    simpa only [show k - 1 + 1 = k by omega] using
      coeff_mul_coordinate ((hM.fun_pow 2).fun_mul hE) (k-1)
  · have he : (fun z => M z ^ 2 * E z) = fun z => (M z * E z) * M z := by
      funext z
      ring
    rw [he]
    exact coeff_product_congr_below (hM.fun_mul hE) hM (hp.fun_mul hE) hp
      (coeff_product_congr_below hM hE hp hE hjet (fun _ _ => rfl)) hjet _ (by omega)

/-- Coefficient convention for the Hardy H² norm on square-summable Taylor series. -/
def hardyTwoNorm (f : ℂ → ℂ) : ℝ := √(∑' j : ℕ, ‖coeff j f‖ ^ 2)

theorem polynomial_coeff_energy_hasSum (P : ℂ[X]) :
    HasSum (fun j => ‖coeff j P.eval‖ ^ 2) (∑ j ∈ P.support, ‖P.coeff j‖ ^ 2) := by
  simp_rw [coeff_polynomial_eval]
  exact hasSum_sum_of_ne_finset_zero fun j hj => by simp [Polynomial.notMem_support_iff.mp hj]

/-- Polynomial Parseval in the coefficient and unit-circle conventions. -/
theorem hardyTwoNorm_poly_sq_eq_circleAverage (P : ℂ[X]) :
    hardyTwoNorm P.eval ^ 2 = Real.circleAverage (fun z => ‖P.eval z‖ ^ 2) 0 1 := by
  rw [hardyTwoNorm, (polynomial_coeff_energy_hasSum P).tsum_eq, Real.sq_sqrt (by positivity),
    P.sum_sq_norm_coeff_eq_circleAverage]

/-- The inside radial means of a polynomial converge to its squared Hardy norm. -/
theorem polynomial_radial_means_tendsto (P : ℂ[X]) :
    Tendsto (fun r => Real.circleAverage (fun z => ‖P.eval z‖ ^ 2) 0 r)
      (𝓝[<] (1 : ℝ)) (𝓝 (hardyTwoNorm P.eval ^ 2)) := by
  rw [hardyTwoNorm_poly_sq_eq_circleAverage]
  exact (Real.Continuous.circleAverage (P.continuous.norm.pow 2)).continuousAt.continuousWithinAt

theorem product_truncation_parseval (M : ℂ → ℂ) (k : ℕ) :
    hardyTwoNorm (productTaylorPoly M k).eval ^ 2 =
      ∑ j ∈ Finset.range k, ‖coeff j M‖ ^ 2 := by
  let P := productTaylorPoly M k
  have h : HasSum (fun j => ‖coeff j P.eval‖ ^ 2)
      (∑ j ∈ Finset.range k, ‖coeff j P.eval‖ ^ 2) :=
    hasSum_sum_of_ne_finset_zero fun j hj => by
      simp [P, coeff_polynomial_eval, productTaylorPoly_coeff, Finset.mem_range.mpr.mt hj]
  change hardyTwoNorm P.eval ^ 2 = _
  rw [hardyTwoNorm, h.tsum_eq, Real.sq_sqrt (by positivity)]
  exact Finset.sum_congr rfl fun j hj => by
    simp [P, coeff_polynomial_eval, productTaylorPoly_coeff, Finset.mem_range.mp hj]

/-- All finite multiplier bounds pass to the full coefficient sum. -/
theorem hardyTwo_weight_contraction {f E : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hs : Summable (fun j => ‖coeff j f‖ ^ 2)) (hE : IsWeight E) :
    Summable (fun j => ‖coeff j (fun z => f z * E z)‖ ^ 2) ∧
      hardyTwoNorm (fun z => f z * E z) ≤ hardyTwoNorm f := by
  have hb (k : ℕ) := (finite_multiplier_contraction k hf hE).trans
    (hs.sum_le_tsum (Finset.range k) (fun _ _ => sq_nonneg _))
  exact ⟨summable_of_sum_range_le (fun _ => sq_nonneg _) hb,
    Real.sqrt_le_sqrt (Real.tsum_le_of_sum_range_le (fun _ => sq_nonneg _) hb)⟩

/-- Cauchy–Schwarz pairs the two coefficient prefixes in opposite order. -/
theorem coeff_product_finite_cauchy_schwarz (n : ℕ) {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    ‖coeff n (fun z => f z * g z)‖ ≤
      √(∑ i ∈ Finset.range (n+1), ‖coeff i f‖ ^ 2) *
      √(∑ i ∈ Finset.range (n+1), ‖coeff i g‖ ^ 2) := by
  rw [coeff_product_convolution n hf hg]
  calc
    _ ≤ ∑ i ∈ Finset.range (n+1), ‖coeff i f * coeff (n-i) g‖ := norm_sum_le _ _
    _ = ∑ i ∈ Finset.range (n+1), ‖coeff i f‖ * ‖coeff (n-i) g‖ := by simp only [norm_mul]
    _ ≤ _ := by
      have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.range (n+1)) (fun i => ‖coeff i f‖)
        (fun i => ‖coeff (n-i) g‖)
      have he : (∑ i ∈ Finset.range (n+1), ‖coeff (n-i) g‖ ^ 2) =
          ∑ i ∈ Finset.range (n+1), ‖coeff i g‖ ^ 2 := by
        simpa using Finset.sum_range_reflect (fun i => ‖coeff i g‖ ^ 2) (n+1)
      simpa only [he] using h

/-- The coefficient in the truncated product is bounded by the two full H² norms. -/
theorem product_hardy_cauchy_schwarz (M : ℂ → ℂ) (k : ℕ) {E : ℂ → ℂ} (hE : IsWeight E) :
    let P := productTaylorPoly M k
    ‖coeff (k-1) (fun z => (P.eval z * E z) * P.eval z)‖ ≤
      hardyTwoNorm (fun z => P.eval z * E z) * hardyTwoNorm P.eval := by
  let P := productTaylorPoly M k
  have hp : AnalyticAt ℂ P.eval 0 := P.differentiable.analyticAt _
  have hs := (polynomial_coeff_energy_hasSum P).summable
  have hsE := (hardyTwo_weight_contraction hp hs hE).1
  exact (coeff_product_finite_cauchy_schwarz (k-1) (hp.fun_mul (hE.1 0 (by simp [disk]))) hp).trans
    (mul_le_mul (Real.sqrt_le_sqrt (hsE.sum_le_tsum _ (fun _ _ => sq_nonneg _)))
      (Real.sqrt_le_sqrt (hs.sum_le_tsum _ (fun _ _ => sq_nonneg _)))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- Multiplication by E contracts the full H² norm of the specified polynomial. -/
theorem product_hardy_contraction (M : ℂ → ℂ) (k : ℕ) {E : ℂ → ℂ} (hE : IsWeight E) :
    let P := productTaylorPoly M k
    hardyTwoNorm (fun z => P.eval z * E z) ≤ hardyTwoNorm P.eval :=
  (hardyTwo_weight_contraction ((productTaylorPoly M k).differentiable.analyticAt _)
    (polynomial_coeff_energy_hasSum _).summable hE).2

/-- The last three steps of the printed estimate, with Robertson applied to the odd pullback. -/
theorem product_hardy_robertson_chain (hR : Robertson) {M E : ℂ → ℂ}
    (hM : AnalyticOnNhd ℂ M disk) (hS : IsS (fun z => z * M (z ^ 2)))
    (hE : IsWeight E) {k : ℕ} (hk : 1 ≤ k) :
    let P := productTaylorPoly M k
    hardyTwoNorm (fun z => P.eval z * E z) * hardyTwoNorm P.eval ≤ hardyTwoNorm P.eval ^ 2 ∧
    hardyTwoNorm P.eval ^ 2 = ∑ j ∈ Finset.range k, ‖coeff j M‖ ^ 2 ∧
    (∑ j ∈ Finset.range k, ‖coeff j M‖ ^ 2) ≤ (k : ℝ) := by
  refine ⟨?_, product_truncation_parseval M k, ?_⟩
  · rw [pow_two]
    exact mul_le_mul_of_nonneg_right (product_hardy_contraction M k hE) (Real.sqrt_nonneg _)
  · have hr := hR _ hS (fun z _ => by simp) k hk
    simpa only [coeff_odd_square_pullback _ hM] using hr

end Goodman
