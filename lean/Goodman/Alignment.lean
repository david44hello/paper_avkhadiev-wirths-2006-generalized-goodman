-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Mathlib

noncomputable section
namespace Goodman

private theorem eq_real_of_re_bound {z : ℂ} {b : ℝ} (h : ‖z‖ ≤ b) (hr : z.re = b) :
    z = (b : ℂ) := by
  have hn := Complex.re_le_norm z
  have he : ‖z‖ = b := le_antisymm h (hr ▸ hn)
  have hh := Complex.sq_norm_sub_sq_re z
  rw [hr, he, sub_self] at hh
  apply Complex.ext
  · simpa using hr
  · simpa using (by nlinarith [sq_nonneg z.im] : z.im = 0)

/-- If a sum attains its positive real majorant, a normalized positive-weight term fixes its
phase. Every other term of positive weight then attains its own majorant on the real axis. -/
theorem aligned_of_saturated_sum {ι : Type*} (s : Finset ι) (w B : ι → ℝ) (a : ι → ℂ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hb : ∀ i ∈ s, ‖a i‖ ≤ B i)
    {j : ι} (hj : j ∈ s) (hwj : 0 < w j) (haj : a j = 1) (hbj : B j = 1)
    (sat : ‖∑ i ∈ s, (w i : ℂ) * a i‖ = ∑ i ∈ s, w i * B i) :
    ∀ i ∈ s, 0 < w i → a i = (B i : ℂ) := by
  classical
  let S : ℂ := ∑ i ∈ s, (w i : ℂ) * a i
  have hn : 0 < ‖S‖ := by
    rw [show ‖S‖ = ∑ i ∈ s, w i * B i from sat]
    exact Finset.sum_pos' (fun i hi => mul_nonneg (hw i hi) ((norm_nonneg _).trans (hb i hi)))
      ⟨j, hj, by simpa [hbj] using hwj⟩
  let u : ℂ := (star S) / (‖S‖ : ℂ)
  have hu : ‖u‖ = 1 := by simp [u, norm_div, abs_of_pos hn, hn.ne']
  have hphase : u*S = (‖S‖ : ℂ) := by
    have h : star S * S = (‖S‖ : ℂ)^2 := by
      rw [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
      rfl
    change star S / (‖S‖ : ℂ) * S = _
    rw [div_mul_eq_mul_div, h]
    field_simp
  have hu_re : ∀ i ∈ s, (u*a i).re ≤ B i := by
    intro i hi
    calc (u*a i).re ≤ ‖u*a i‖ := Complex.re_le_norm _
         _ ≤ B i := by simpa [norm_mul, hu] using hb i hi
  have heq : ∑ i ∈ s, w i * (u*a i).re = ∑ i ∈ s, w i * B i := by
    have h := congrArg Complex.re hphase
    dsimp [S] at h
    rw [Finset.mul_sum, Complex.re_sum] at h
    calc
      _ = ∑ i ∈ s, (u * ((w i : ℂ) * a i)).re := by
        apply Finset.sum_congr rfl
        intro i _
        rw [mul_left_comm,Complex.re_ofReal_mul]
      _ = ‖S‖ := h
      _ = _ := sat
  have at_bound (i : ι) (hi : i ∈ s) (hwi : 0 < w i) : (u*a i).re = B i := by
    have hz : ∑ i ∈ s, w i * (B i - (u*a i).re) = 0 := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, heq, sub_self]
    have hz' := (Finset.sum_eq_zero_iff_of_nonneg
      (fun t ht => mul_nonneg (hw t ht) (sub_nonneg.mpr (hu_re t ht)))).mp hz i hi
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hz').resolve_left hwi.ne')).symm
  have hu1 : u = 1 := by
    have hr := at_bound j hj hwj
    rw [haj, mul_one, hbj] at hr
    simpa using eq_real_of_re_bound (le_of_eq hu) hr
  intro i hi hwi
  exact eq_real_of_re_bound (hb i hi) (by simpa [hu1] using at_bound i hi hwi)

end Goodman
