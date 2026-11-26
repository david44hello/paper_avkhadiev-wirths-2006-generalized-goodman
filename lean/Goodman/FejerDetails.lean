-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
module

public import Goodman.Fejer
public import Goodman.Geometry

@[expose] public section

noncomputable section
open Complex Metric
open scoped ComplexConjugate

namespace Goodman

/-- Count pairs of geometric-sum exponents with a given signed difference. -/
theorem fejer_difference_count (k : ℕ) (j : ℤ) :
    (((Finset.range k ×ˢ Finset.range k).filter
      (fun a : ℕ × ℕ => (a.1 : ℤ) - a.2 = j)).card) = k - j.natAbs := by
  have habs : j.natAbs = j.toNat + (-j).toNat := by cases j <;> simp
  rw [← Finset.card_range (k - j.natAbs)]
  apply Finset.card_bij' (fun a _ => a.2 - (-j).toNat)
    (fun n _ => (n + j.toNat, n + (-j).toNat))
  · rintro ⟨a, b⟩ h
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h ⊢
    omega
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hn ⊢
    omega
  · rintro ⟨a, b⟩ h
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h
    apply Prod.ext <;> dsimp <;> omega
  · intro n _
    simp

/-- The signed Laurent expansion of the order-`k` normalized Fejér kernel. -/
theorem fejerKernel_eq_laurent {k : ℕ} (hk : 0 < k) {w : ℂ} (hw : ‖w‖ = 1) :
    (fejerKernel k w : ℂ) = ∑ j ∈ Finset.Ioo (-(k : ℤ)) (k : ℤ),
      (1 - (j.natAbs : ℂ) / k) * w ^ j := by
  have hw0 : w ≠ 0 := norm_ne_zero_iff.mp (hw.trans_ne one_ne_zero)
  let diff (a : ℕ × ℕ) : ℤ := (a.1 : ℤ) - a.2
  have hmem : ∀ a ∈ Finset.range k ×ˢ Finset.range k,
      diff a ∈ Finset.Ioo (-(k : ℤ)) (k : ℤ) := by
    rintro ⟨a, b⟩ h
    simp only [diff, Finset.mem_Ioo, Finset.mem_product, Finset.mem_range] at h ⊢
    omega
  change ((‖∑ i ∈ Finset.range k, w ^ i‖ ^ 2 / (k : ℝ) : ℝ) : ℂ) = _
  rw [Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_pow, ← Complex.mul_conj',
    map_sum, Finset.sum_mul]
  simp_rw [Finset.mul_sum, map_pow, ← Complex.inv_eq_conj hw, inv_pow, ← div_eq_mul_inv,
    ← zpow_natCast_sub_natCast₀ hw0]
  rw [← Finset.sum_product']
  change (∑ a ∈ Finset.range k ×ˢ Finset.range k, w ^ diff a) / k = _
  rw [← Finset.sum_fiberwise_of_maps_to' hmem (fun j => w ^ j), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_Ioo.mp hj
  have hle : j.natAbs ≤ k := by cases j <;> simp_all <;> omega
  simp only [Finset.sum_const, nsmul_eq_mul, diff, fejer_difference_count, Nat.cast_sub hle]
  field_simp [Nat.cast_ne_zero.mpr hk.ne']

/-- Conjugation preserves the real kernel, including away from the unit circle. -/
theorem fejerKernel_conj (k : ℕ) (w : ℂ) : fejerKernel k (conj w) = fejerKernel k w := by
  change ‖∑ i ∈ Finset.range k, conj w ^ i‖ ^ 2 / _ = ‖∑ i ∈ Finset.range k, w ^ i‖ ^ 2 / _
  simp only [← map_pow, ← map_sum, Complex.norm_conj]

/-- Reflection preserves the normalized unit-circle average. -/
theorem circleAverage_conj_unit (F : ℂ → ℂ) :
    Real.circleAverage (fun w => F (conj w)) 0 1 = Real.circleAverage F 0 1 := by
  apply Eq.trans _ Real.circleAverage_zero_one_congr_inv
  apply Real.circleAverage_congr_sphere
  intro w hw
  have hn : ‖w‖ = 1 := by simpa [mem_sphere] using hw
  exact congrArg F (Complex.inv_eq_conj hn).symm

/-- The polynomial mean as convolution with the kernel in the printed orientation. -/
theorem fejerMean_eq_circleAverage_conj {E : ℂ → ℂ} (hE : AnalyticOnNhd ℂ E disk)
    {k : ℕ} (hk : 0 < k) {z : ℂ} (hz : z ∈ disk) :
    fejerMean k E z = Real.circleAverage
      (fun w => E (z * conj w) * (fejerKernel k w : ℂ)) 0 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  rw [fejerMean_eq_circleAverage hE m hz,
    ← circleAverage_conj_unit (fun w => (fejerKernel (m+1) w : ℂ) * E (z*w))]
  simp only [fejerKernel_conj, mul_comm]

/-- The actual normalized pullback in the centered estimate has zero constant term. -/
theorem centered_coeff_zero {φ : ℂ → ℂ} {G : ℂ → Sphere} {x w : ℂ}
    (U : Set Sphere) (hφ : φ 0 = x) (hG : G x = (w : Sphere)) :
    coeff 0 (fun z => (finitePart (G (φ z)) - w) / (radius U w : ℂ)) = 0 := by
  simp [coeff, hφ, hG, show finitePart (w : Sphere) = w from rfl]

/-- Every natural power of a disk weight is a disk weight, including the constant power. -/
theorem IsWeight.pow {v : ℂ → ℂ} (hv : IsWeight v) (j : ℕ) :
    IsWeight (fun z => v z ^ j) :=
  ⟨fun z hz => (hv.1 z hz).fun_pow j, fun z hz => by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (hv.2 z hz)⟩

#print axioms fejerKernel_eq_laurent
#print axioms fejerMean_eq_circleAverage_conj
#print axioms centered_coeff_zero
#print axioms IsWeight.pow

end Goodman
