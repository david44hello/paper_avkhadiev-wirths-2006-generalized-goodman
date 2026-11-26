-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Goodman.SlitMajorant

noncomputable section
open Set Filter
open scoped Topology ComplexOrder

namespace Goodman

/-- The Taylor coefficient of a product is the finite Cauchy convolution. -/
theorem coeff_mul {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    coeff n (fun z => f z * g z) =
      ∑ i ∈ Finset.range (n + 1), coeff i f * coeff (n - i) g := by
  simp only [coeff, iteratedDeriv_fun_mul hf.contDiffAt hg.contDiffAt, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Nat.cast_choose ℂ (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
  have hfac (m : ℕ) : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
  field_simp [hfac]

private theorem coeff_zero_at (f : ℂ → ℂ) : coeff 0 f = f 0 := by simp [coeff]

private theorem coeff_add_at {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    coeff n (fun z => f z + g z) = coeff n f + coeff n g := by
  simp only [coeff, iteratedDeriv_fun_add hf.contDiffAt hg.contDiffAt, add_div]

private theorem coeff_const_mul_at (a : ℂ) (f : ℂ → ℂ) (n : ℕ) :
    coeff n (fun z => a * f z) = a * coeff n f := by
  simp [coeff, mul_div_assoc]

private theorem coeff_id_at (n : ℕ) :
    coeff n (fun z => z) = if n = 1 then 1 else 0 := by
  by_cases h : n = 1 <;> simp [coeff, iteratedDeriv_fun_id_zero, h]

private theorem coeff_shift {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    coeff (n + 1) (fun z => z * f z) = coeff n f := by
  rw [coeff_mul (f := fun z => z) analyticAt_id hf]
  simp [coeff_id_at, ite_mul]

private theorem coeff_mul_nonneg {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) {n : ℕ}
    (hf' : ∀ i ≤ n, 0 ≤ coeff i f) (hg' : ∀ i ≤ n, 0 ≤ coeff i g) :
    0 ≤ coeff n (fun z => f z * g z) := by
  rw [coeff_mul hf hg]
  exact Finset.sum_nonneg fun i hi =>
    mul_nonneg (hf' i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))) (hg' _ (Nat.sub_le ..))

/-- Each positive-degree Taylor coefficient of the slit map is positive real. -/
theorem slit_coeff_pos {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {q : ℂ → ℂ}
    (hq : IsSlitMap p q) (n : ℕ) (hn : 1 ≤ n) :
    (coeff n q).im = 0 ∧ 0 < (coeff n q).re := by
  have hU := slitDisk_mem_nhds_zero hp hp1
  have hqA := hq.1.1 0 (mem_of_mem_nhds hU)
  let u := fun z : ℂ => q z - z
  let s := fun z : ℂ => 1 + q z
  have huA : AnalyticAt ℂ u 0 := hqA.sub analyticAt_id
  have hsA : AnalyticAt ℂ s 0 := analyticAt_const.add hqA
  have hR : 0 < slitR p := by unfold slitR; positivity
  have hR1 : slitR p < 1 := by
    unfold slitR
    rw [div_lt_one (by positivity)]
    nlinarith [sq_pos_of_pos (sub_pos.mpr hp1)]
  let c : ℝ := 1 / slitR p - 1
  have hc : 0 < (c : ℂ) := Complex.zero_lt_real.mpr (sub_pos.mpr ((lt_div_iff₀ hR).mpr
    (by simpa using hR1)))
  -- The slit equation gives a recurrence with only nonnegative products.
  have germ : u =ᶠ[𝓝 0] fun z => z * ((c : ℂ) * (s z * s z) + q z * u z) := by
    filter_upwards [hU] with z hz
    have heq := hq.2.2 z hz
    have hR0 : (slitR p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
    dsimp [u, s, c]
    push_cast
    field_simp [hR0]
    linear_combination -heq
  have recurrence (m : ℕ) : coeff (m + 1) u =
      (c : ℂ) * coeff m (fun z => s z * s z) + coeff m (fun z => q z * u z) := by
    calc
      _ = coeff (m + 1) (fun z => z * ((c : ℂ) * (s z * s z) + q z * u z)) :=
        congrArg (· / ((m + 1).factorial : ℂ)) (germ.iteratedDeriv_eq (m + 1))
      _ = _ := by
        rw [coeff_shift ((analyticAt_const.fun_mul (hsA.fun_mul hsA)).fun_add (hqA.fun_mul huA)),
          coeff_add_at (analyticAt_const.fun_mul (hsA.fun_mul hsA)) (hqA.fun_mul huA), coeff_const_mul_at]
  have hqu (m : ℕ) : coeff m q = coeff m u + coeff m (fun z => z) := by
    rw [← coeff_add_at (g := fun z => z) huA analyticAt_id]
    simp [u]
  have hsq (m : ℕ) (hm : 0 < m) : coeff m s = coeff m q := by
    simp [coeff, s, iteratedDeriv_const_add hm]
  have all_coeff (m : ℕ) : 0 ≤ coeff m u ∧ 0 ≤ coeff m q ∧ 0 < coeff m s := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      cases m with
      | zero => simp [coeff_zero_at, u, s, hq.2.1]
      | succ m =>
        have hsprod : 0 < coeff m (fun z => s z * s z) := by
          rw [coeff_mul hsA hsA]
          apply Finset.sum_pos
          · intro i hi
            exact mul_pos (ih i (Finset.mem_range.mp hi)).2.2
              (ih _ (Nat.lt_succ_of_le (Nat.sub_le m i))).2.2
          · exact ⟨0, by simp⟩
        have hquprod : 0 ≤ coeff m (fun z => q z * u z) :=
          coeff_mul_nonneg hqA huA (fun i hi => (ih i (Nat.lt_succ_of_le hi)).2.1)
            (fun i hi => (ih i (Nat.lt_succ_of_le hi)).1)
        have hu : 0 < coeff (m + 1) u := (recurrence m).symm ▸
          add_pos_of_pos_of_nonneg (mul_pos hc hsprod) hquprod
        have hqpos : 0 < coeff (m + 1) q := by
          rw [hqu, coeff_id_at]
          exact add_pos_of_pos_of_nonneg hu (by split <;> simp)
        exact ⟨hu.le, hqpos.le, (hsq _ (Nat.succ_pos _)).symm ▸ hqpos⟩
  have hpos : 0 < coeff n q := (hsq n hn) ▸ (all_coeff n).2.2
  exact ⟨(Complex.pos_iff.mp hpos).2.symm, (Complex.pos_iff.mp hpos).1⟩

/-- Every Taylor coefficient of a nonnegative integral power of the slit map is nonnegative real. -/
theorem slit_pow_coeff_nonneg {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {q : ℂ → ℂ}
    (hq : IsSlitMap p q) (k n : ℕ) :
    (coeff n (fun z => q z ^ k)).im = 0 ∧ 0 ≤ (coeff n (fun z => q z ^ k)).re := by
  have hqA := hq.1.1 0 (mem_of_mem_nhds (slitDisk_mem_nhds_zero hp hp1))
  have hnonneg (m : ℕ) : 0 ≤ coeff m q := by
    cases m with
    | zero => simp [coeff_zero_at, hq.2.1]
    | succ m =>
      obtain ⟨him, hre⟩ := slit_coeff_pos hp hp1 hq _ (Nat.succ_pos m)
      exact Complex.nonneg_iff.mpr ⟨hre.le, him.symm⟩
  have hpow : 0 ≤ coeff n (fun z => q z ^ k) := by
    induction k generalizing n with
    | zero =>
      cases n <;> simp [coeff, iteratedDeriv_const]
    | succ k ih =>
      simp only [pow_succ]
      exact coeff_mul_nonneg (hqA.pow k) hqA (fun i _ => ih i) (fun i _ => hnonneg i)
  exact ⟨(Complex.nonneg_iff.mp hpow).2.symm, (Complex.nonneg_iff.mp hpow).1⟩

/-- For degree at least two, the convolution includes the strictly positive
product of the coefficients of degrees one and `n - 1`. -/
theorem slit_square_coeff_pos {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {q : ℂ → ℂ}
    (hq : IsSlitMap p q) {n : ℕ} (hn : 2 ≤ n) :
    0 < (coeff n (fun z => q z ^ 2)).re := by
  have hqA := hq.1.1 0 (mem_of_mem_nhds (slitDisk_mem_nhds_zero hp hp1))
  have hr (m : ℕ) : 0 ≤ coeff m q := by
    obtain ⟨hi, h⟩ := slit_pow_coeff_nonneg hp hp1 hq 1 m
    apply Complex.nonneg_iff.mpr
    simpa using And.intro h hi.symm
  have hpos (m : ℕ) (hm : 1 ≤ m) : 0 < coeff m q := by
    obtain ⟨hi, h⟩ := slit_coeff_pos hp hp1 hq m hm
    exact Complex.pos_iff.mpr ⟨h, hi.symm⟩
  apply (Complex.pos_iff.mp ?_).1
  simp only [sq, coeff_mul hqA hqA]
  exact Finset.sum_pos' (fun k _ => mul_nonneg (hr k) (hr _))
    ⟨1, Finset.mem_range.mpr (by omega), mul_pos (hpos 1 (by decide)) (hpos _ (by omega))⟩

end Goodman
