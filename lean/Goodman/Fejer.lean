-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
module

public import Goodman.SchwarzCases
public import Goodman.Transfer
public import Goodman.SlitPositivity

@[expose] public section

noncomputable section
open Complex Metric Set
open scoped ComplexConjugate Topology

namespace Goodman

def geomJet (k : ℕ) (w : ℂ) := ∑ j ∈ Finset.range k, w ^ j

private theorem geomJet_analytic (k : ℕ) (w : ℂ) : AnalyticAt ℂ (geomJet k) w :=
  Finset.analyticAt_fun_sum _ fun j _ => analyticAt_id.fun_pow j

/-- The order-k Fejér kernel for normalized angular measure. -/
def fejerKernel (k : ℕ) (w : ℂ) : ℝ := ‖geomJet k w‖ ^ 2 / k

theorem fejerKernel_nonneg (k : ℕ) (w : ℂ) : 0 ≤ fejerKernel k w := by
  unfold fejerKernel
  positivity

/-- The finite Taylor polynomial with the triangular Fejér multipliers. -/
def fejerMean (k : ℕ) (E : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range k, z ^ j * (((k - j : ℕ) : ℂ) / k * coeff j E)

private theorem coeff_jet {c : ℕ → ℂ} (k j : ℕ) (hj : j < k) :
    coeff j (fun z => ∑ i ∈ Finset.range k, z ^ i * c i) = c j := by
  unfold coeff
  rw [iteratedDeriv_fun_sum (fun i _ => by fun_prop)]
  simp only [iteratedDeriv_mul_const_field, iteratedDeriv_fun_pow_zero, Nat.cast_ite,
    Nat.cast_zero, ite_mul, zero_mul, Finset.sum_ite_eq, ite_eq_left (Finset.mem_range.mpr hj)]
  field_simp [show (j.factorial : ℂ) ≠ 0 by exact_mod_cast j.factorial_ne_zero]

theorem coeff_fejerMean (E : ℂ → ℂ) {j k : ℕ} (hj : j < k) :
    coeff j (fejerMean k E) = ((k - j : ℕ) : ℂ) / k * coeff j E :=
  coeff_jet k j hj

private theorem geomJet_coeff {k j : ℕ} (hj : j < k) : coeff j (geomJet k) = 1 := by
  unfold geomJet
  simpa only [mul_one] using coeff_jet (c := fun _ => 1) k j hj

private theorem geomJet_square_coeff {k j : ℕ} (hj : j < k) :
    coeff j (fun w => geomJet k w * geomJet k w) = (j + 1 : ℕ) := by
  rw [coeff_mul (geomJet_analytic k 0) (geomJet_analytic k 0)]
  calc
    _ = ∑ _i ∈ Finset.range (j + 1), (1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      rw [geomJet_coeff (by omega : i < k), geomJet_coeff (by omega : j - i < k), mul_one]
    _ = _ := by simp

private theorem geomJet_phase (m : ℕ) {w : ℂ} (hw : ‖w‖ = 1) :
    w⁻¹ ^ m * geomJet (m+1) w = conj (geomJet (m+1) w) := by
  have hw0 : w ≠ 0 := norm_ne_zero_iff.mp (hw.trans_ne one_ne_zero)
  unfold geomJet
  rw [map_sum, Finset.mul_sum, ← Finset.sum_range_reflect (fun i => conj (w ^ i))]
  apply Finset.sum_congr rfl
  intro i hi
  have hle : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  simp only [Nat.add_sub_cancel, map_pow, ← Complex.inv_eq_conj hw, inv_pow]
  rw [← Nat.sub_add_cancel hle, pow_add]
  simp [pow_ne_zero _ hw0, mul_comm]

private theorem scaled_mem {z w : ℂ} (hz : z ∈ disk) (hw : w ∈ closedBall 0 1) :
    z * w ∈ disk := by
  simp only [disk, mem_ball, mem_closedBall, dist_zero_right, norm_mul] at *
  exact (mul_le_of_le_one_right (norm_nonneg z) hw).trans_lt hz

/-- Integrating the rotated interior values uses only a compact subdisk. The
kernel is even, so we use the rotation w rather than its inverse. -/
theorem fejerMean_eq_circleAverage {E : ℂ → ℂ} (hE : AnalyticOnNhd ℂ E disk)
    (m : ℕ) {z : ℂ} (hz : z ∈ disk) :
    fejerMean (m+1) E z =
      Real.circleAverage (fun w => (fejerKernel (m+1) w : ℂ) * E (z*w)) 0 1 := by
  let k := m+1
  let P := geomJet k
  let f (w : ℂ) := E (z*w) * (P w * P w)
  have ha (w : ℂ) (hw : w ∈ closedBall 0 1) : AnalyticAt ℂ (fun u => E (z*u)) w :=
    (hE _ (scaled_mem hz hw)).comp (analyticAt_const.fun_mul analyticAt_id)
  have hf : DiffContOnCl ℂ f (ball 0 1) := by
    apply DifferentiableOn.diffContOnCl
    intro w hw
    exact ((ha w (closure_ball_subset_closedBall hw)).fun_mul
      ((geomJet_analytic k w).fun_mul (geomJet_analytic k w))).differentiableAt.differentiableWithinAt
  have hk : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
  have hav : Real.circleAverage (fun w => (fejerKernel k w : ℂ) * E (z*w)) 0 1 =
      (k : ℂ)⁻¹ * coeff m f := by
    calc
      _ = Real.circleAverage (fun w => (k : ℂ)⁻¹ • (w⁻¹ ^ m * f w)) 0 1 := by
        apply Real.circleAverage_congr_sphere
        intro w hw
        have hw' : ‖w‖ = 1 := by simpa [mem_sphere] using hw
        have phase := geomJet_phase m hw'
        change w⁻¹ ^ m * P w = conj (P w) at phase
        have hsq := Complex.mul_conj' (P w)
        change ((‖P w‖ ^ 2 / (k : ℝ) : ℝ) : ℂ) * E (z*w) =
          (k : ℂ)⁻¹ * (w⁻¹ ^ m * (E (z*w) * (P w * P w)))
        rw [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast, ← hsq, ← phase]
        ring
      _ = _ := by rw [Real.circleAverage_fun_smul, transfer_coeff_average zero_lt_one hf]; rfl
  change fejerMean k E z = _
  rw [hav, show coeff m f = _ from coeff_mul (ha 0 (by simp))
    ((geomJet_analytic k 0).fun_mul (geomJet_analytic k 0)) m, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  have he : k - j = m - j + 1 := by dsimp [k]; omega
  rw [coeff_comp_mul_left, geomJet_square_coeff (by dsimp [k]; omega : m - j < k), ← he]
  ring

theorem fejerKernel_mass (m : ℕ) : Real.circleAverage (fejerKernel (m+1)) 0 1 = 1 := by
  have he := fejerMean_eq_circleAverage (E := fun _ => 1) (fun _ _ => analyticAt_const)
    m (z := 0) (by simp [disk])
  have h0 : fejerMean (m+1) (fun _ => 1) 0 = 1 := by
    rw [fejerMean, Finset.sum_range_succ']
    simp [coeff, show (m : ℂ) + 1 ≠ 0 by exact_mod_cast (Nat.succ_ne_zero m)]
  rw [h0] at he
  simp only [mul_one] at he
  have hc : Continuous (fejerKernel (m+1)) :=
    (((fun z => (geomJet_analytic (m+1) z).continuousAt : ∀ z, ContinuousAt _ z)
      |> continuous_iff_continuousAt.mpr).norm.pow 2).div_const _
  have he' := Complex.ofRealCLM.circleAverage_comp_comm (hc.continuousOn.circleIntegrable
    (c := 0) (by norm_num : (0:ℝ) ≤ 1))
  exact Complex.ofReal_injective (he'.symm.trans he.symm)

theorem fejerMean_isWeight {E : ℂ → ℂ} (hE : IsWeight E) (m : ℕ) :
    IsWeight (fejerMean (m+1) E) := by
  constructor
  · intro z _
    exact Finset.analyticAt_fun_sum _ fun j _ => (analyticAt_id.fun_pow j).fun_mul analyticAt_const
  intro z hz
  rw [fejerMean_eq_circleAverage hE.1 m hz]
  apply le_trans _ (fejerKernel_mass m).le
  let K := fejerKernel (m+1)
  have hc : Continuous K :=
    (((continuous_iff_continuousAt.mpr fun w => (geomJet_analytic (m+1) w).continuousAt).norm.pow 2)).div_const _
  have hd : ContinuousOn (fun w => E (z*w)) (sphere 0 1) :=
    hE.1.continuousOn.comp (continuous_const.mul continuous_id).continuousOn
      (fun _ hw => scaled_mem hz (sphere_subset_closedBall hw))
  refine Real.norm_circleAverage_le_circleAverage_norm.trans (Real.circleAverage_mono
    ((Complex.continuous_ofReal.comp hc).continuousOn.mul hd |>.norm |>.circleIntegrable zero_le_one)
    (hc.continuousOn.circleIntegrable zero_le_one) ?_)
  intro w hw
  have hw' : w ∈ sphere (0:ℂ) 1 := by simpa using hw
  change ‖(K w : ℂ) * E (z*w)‖ ≤ K w
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (fejerKernel_nonneg _ _)]
  exact mul_le_of_le_one_right (fejerKernel_nonneg _ _) (hE.2 _ (scaled_mem hz (sphere_subset_closedBall hw')))

/-- The constant term vanishes. Each remaining coefficient of H carries its
positive degree, exactly the multiplier produced by differentiation. -/
theorem fejer_derivative_identity {H E : ℂ → ℂ} (hH : AnalyticAt ℂ H 0)
    (h0 : H 0 = 0) (hE : IsWeight E) (m : ℕ) :
    coeff m (fun z => deriv H z * E z) =
      ((m+1 : ℕ) : ℂ) * coeff (m+1) (fun z => H z * fejerMean (m+1) E z) := by
  have hz : (0 : ℂ) ∈ disk := by simp [disk]
  have hc (i : ℕ) : coeff i (deriv H) = ((i+1 : ℕ) : ℂ) * coeff (i+1) H := by
    rw [coeff, coeff, iteratedDeriv_succ', Nat.factorial_succ, Nat.cast_mul]
    field_simp [show (i.factorial : ℂ) ≠ 0 by exact_mod_cast i.factorial_ne_zero,
      Nat.cast_ne_zero.mpr (Nat.succ_ne_zero i)]
  rw [coeff_mul hH.deriv (hE.1 0 hz), coeff_mul hH ((fejerMean_isWeight hE m).1 0 hz),
    Finset.sum_range_succ' _ (m+1)]
  simp only [coeff, iteratedDeriv_zero, h0, zero_div, zero_mul, add_zero, Nat.add_sub_add_right]
  change (∑ i ∈ Finset.range (m+1), coeff i (deriv H) * coeff (m-i) E) =
    ((m+1 : ℕ) : ℂ) * ∑ i ∈ Finset.range (m+1), coeff (i+1) H * coeff (m-i) (fejerMean (m+1) E)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [hc, coeff_fejerMean E (by omega : m - i < m + 1), show m + 1 - (m-i) = i+1 by omega]
  field_simp [Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)]

/-- The degree-k centered bound for all disk weights controls the weighted
derivative at degree k-1, including k=1. Only the germ of H needs to be analytic. -/
theorem fejer_derivative_bound {H : ℂ → ℂ} (hH : AnalyticAt ℂ H 0) (h0 : H 0 = 0)
    {p : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hbound : ∀ W, IsWeight W → ‖coeff k (fun z => H z * W z)‖ ≤ A p k)
    {E : ℂ → ℂ} (hE : IsWeight E) :
    ‖coeff (k-1) (fun z => deriv H z * E z)‖ ≤ k * A p k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [Nat.succ_sub_one, fejer_derivative_identity hH h0 hE, norm_mul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (hbound _ (fejerMean_isWeight hE m)) (by positivity)

#print axioms fejer_derivative_bound

end Goodman
