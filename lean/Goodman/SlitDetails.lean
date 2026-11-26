-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Goodman.Slit
import Goodman.SlitTransport
import Goodman.SlitWeights
import Goodman.DiskDerivative

noncomputable section
open Set Filter
open scoped Topology

namespace Goodman

variable {p : ℝ} {q : ℂ → ℂ}

/-- The inverse of the given slit map, with its center and its positive derivative. -/
theorem slit_inverse_chart (hp : 0 < p) (hp1 : p < 1) (hq : IsSlitMap p q) :
    ∃ χ : ℂ → ℂ, Bihol disk (slitDisk p) χ ∧ LeftInvOn χ q (slitDisk p) ∧
      LeftInvOn q χ disk ∧ χ 0 = 0 ∧ HasDerivAt χ (slitR p : ℂ) 0 := by
  obtain ⟨χ, hχ, hqmap, hχmap, hl, hr⟩ := hq.1.2
  have hχ0 : χ 0 = 0 := by
    simpa [hq.2.1] using hl (mem_of_mem_nhds (slitDisk_mem_nhds_zero hp hp1))
  refine ⟨χ, ⟨hχ, q, hq.1.1, hχmap, hqmap, hr, hl⟩, hl, hr, hχ0, ?_⟩
  have hd := (hχ 0 (by simp [disk])).differentiableAt.hasDerivAt
  have hcomp := (hasDerivAt_slit_zero hp hp1 hq).comp_of_eq 0 hd hχ0.symm
  have he : (fun z : ℂ => z) =ᶠ[𝓝 0] q ∘ χ := by
    filter_upwards [show disk ∈ 𝓝 (0 : ℂ) from Metric.ball_mem_nhds _ zero_lt_one] with z hz
    exact (hr hz).symm
  have h := (hcomp.congr_of_eventuallyEq he).unique (hasDerivAt_id 0)
  have hR : (slitR p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (slitR_pos hp).ne'
  apply hd.congr_deriv
  field_simp [hR] at h
  simpa using h

/-- Radius at the origin of the actual planar slit domain. -/
theorem radius_slitDisk (hp : 0 < p) (hp1 : p < 1) (hq : IsSlitMap p q) :
    radius (planeDomain (slitDisk p)) 0 = 4 * p / (1 + p)^2 := by
  obtain ⟨χ, hχ, _, _, h0, hd⟩ := slit_inverse_chart hp hp1 hq
  change radius (planeDomain (slitDisk p)) 0 = slitR p
  simpa only [h0, hd.deriv, Complex.norm_of_nonneg (slitR_pos hp).le] using
    radius_planeDomain_of_bihol hχ

/-- A meromorphic member of the paper's class has finite value throughout the slit disk. -/
theorem finite_on_slitDisk (hp : 0 < p) (hp1 : p < 1) {f : ℂ → Sphere} (hf : IsM p f)
    {z : ℂ} (hz : z ∈ slitDisk p) : f z ≠ OnePoint.infty := by
  have hpD : (p : ℂ) ∈ disk := by simpa [disk, abs_of_pos hp] using hp1
  intro he
  have hzp := hf.2.1 hz.1 hpD (he.trans hf.2.2.1.symm)
  exact hz.2 ⟨p, ⟨le_rfl, hp1⟩, hzp.symm⟩

/-- The positive parameter in the slit coefficient recurrence. -/
def slitC (p : ℝ) : ℝ := (1 - p)^2 / (4 * p)

theorem slitC_pos (hp : 0 < p) (hp1 : p < 1) : 0 < slitC p :=
  div_pos (sq_pos_of_pos (sub_pos.mpr hp1)) (by positivity)

theorem slitC_eq_inv_radius_sub_one (hp : 0 < p) : slitC p = 1 / slitR p - 1 := by
  unfold slitC slitR
  field_simp [hp.ne', (show 1+p ≠ 0 by linarith)]
  ring

theorem joukowski_add_two {z : ℂ} (hz : z ≠ 0) : z + z⁻¹ + 2 = (1 + z)^2 / z := by
  field_simp
  ring

theorem slit_difference_factor (w z : ℂ) :
    w * (1+z)^2 - z * (1+w)^2 = (w-z) * (1-z*w) := by ring

theorem slit_factorization (hp : 0 < p) (hq : IsSlitMap p q) {z : ℂ} (hz : z ∈ slitDisk p) :
    (q z - z) * (1 - z * q z) = (slitC p : ℂ) * z * (1 + q z)^2 := by
  rw [← slit_difference_factor, slitC_eq_inv_radius_sub_one hp]
  push_cast
  have hR := Complex.ofReal_ne_zero.mpr (slitR_pos hp).ne'
  field_simp [hR]
  linear_combination -(hq.2.2 z hz)

theorem slit_geometric_recurrence (hp : 0 < p) (hp1 : p < 1) (hq : IsSlitMap p q) :
    ∀ᶠ z in 𝓝 (0 : ℂ), HasSum (fun m : ℕ => (z * q z)^m) (1 - z * q z)⁻¹ ∧
      q z = z + (slitC p : ℂ) * z * (1 + q z)^2 * ∑' m : ℕ, (z * q z)^m := by
  filter_upwards [slitDisk_mem_nhds_zero hp hp1] with z hz
  have hn : ‖z * q z‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _)
      (mem_ball_zero_iff.mp (hq.1.2.choose_spec.2.1 hz)).le).trans_lt (mem_ball_zero_iff.mp hz.1)
  have hs := hasSum_geometric_of_norm_lt_one hn
  have hne : 1 - z * q z ≠ 0 := sub_ne_zero.mpr (fun h => by rw [← h] at hn; simp at hn)
  refine ⟨hs, ?_⟩
  rw [hs.tsum_eq, ← div_eq_mul_inv, ← sub_eq_iff_eq_add']
  exact (eq_div_iff hne).2 (slit_factorization hp hq hz)

theorem slit_coeff_one (hp : 0 < p) (hp1 : p < 1) (hq : IsSlitMap p q) :
    coeff 1 q = 1 + (slitC p : ℂ) := by
  simp [coeff, (hasDerivAt_slit_zero hp hp1 hq).deriv, slitC_eq_inv_radius_sub_one hp]

/-- The multiplier of c z in the geometric recurrence. -/
def slitKernel (q : ℂ → ℂ) (z : ℂ) : ℂ := (1 + q z)^2 / (1 - z * q z)

private theorem kernel_analytic (hqA : AnalyticAt ℂ q 0) : AnalyticAt ℂ (slitKernel q) 0 :=
  ((analyticAt_const.add hqA).pow 2).div (analyticAt_const.sub (analyticAt_id.mul hqA)) (by simp)

private theorem coeff_sum_pair {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (n : ℕ) : coeff n (fun z => f z + g z) = coeff n f + coeff n g := by
  simp only [coeff, iteratedDeriv_fun_add hf.contDiffAt hg.contDiffAt, add_div]

private theorem coeff_identity (n : ℕ) :
    coeff n (fun z => z) = if n = 1 then 1 else 0 := by
  by_cases h : n = 1 <;> simp [coeff, iteratedDeriv_fun_id_zero, h]

private theorem coeff_shift_one {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    coeff (n+1) (fun z => z * g z) = coeff n g := by
  rw [coeff_mul (f := fun z => z) analyticAt_id hg]
  simp [coeff_identity, ite_mul]

private theorem kernel_germ (hqA : AnalyticAt ℂ q 0) :
    slitKernel q =ᶠ[𝓝 0] fun z =>
      1 + (2 * q z + q z * q z + z * (slitKernel q z * q z)) := by
  have h : ContinuousAt (fun z : ℂ => 1 - z * q z) 0 :=
    (analyticAt_const.sub (analyticAt_id.mul hqA)).continuousAt
  filter_upwards [h.eventually_ne (by simp : 1 - (0 : ℂ) * q 0 ≠ 0)] with z hz
  change 1 - z * q z ≠ 0 at hz
  have he : slitKernel q z * (1 - z * q z) = (1 + q z)^2 := div_mul_cancel₀ _ hz
  linear_combination he

/-- Coefficient form of K = (1+q)² + z q K, where K = (1+q)²/(1-zq).
The two finite convolutions give the remainder after the linear term. -/
theorem slit_kernel_coeff_recurrence (hqA : AnalyticAt ℂ q 0) (n : ℕ) :
    coeff (n+1) (slitKernel q) = 2 * coeff (n+1) q +
      (∑ i : Fin (n+2), coeff i q * coeff (n+1-i) q) +
      ∑ i : Fin (n+1), coeff i (slitKernel q) * coeff (n-i) q := by
  have hK := kernel_analytic hqA
  have hquad : AnalyticAt ℂ (fun z => 2 * q z + q z * q z) 0 :=
    (analyticAt_const.fun_mul hqA).fun_add (hqA.fun_mul hqA)
  rw [coeff_congr_of_eventuallyEq (kernel_germ hqA)]
  have hadd (f : ℂ → ℂ) : coeff (n+1) (fun z => 1 + f z) = coeff (n+1) f := by
    simp only [coeff, iteratedDeriv_const_add (Nat.succ_pos n)]
  rw [hadd, coeff_sum_pair (g := fun z => z * (slitKernel q z * q z)) hquad
    (analyticAt_id.fun_mul (hK.fun_mul hqA)),
    coeff_sum_pair (analyticAt_const.fun_mul hqA) (hqA.fun_mul hqA), coeff_fun_const_mul,
    coeff_shift_one (hK.fun_mul hqA), coeff_mul hqA hqA, coeff_mul hK hqA]
  simp only [← Fin.sum_univ_eq_sum_range]

/-- The geometric recurrence shifts the coefficients of its kernel by one degree. -/
theorem slit_coeff_of_kernel (hp : 0 < p) (hp1 : p < 1) (hq : IsSlitMap p q) (n : ℕ) :
    coeff (n+2) q = (slitC p : ℂ) * coeff (n+1) (slitKernel q) := by
  have hK := kernel_analytic (hq.1.1 0 (mem_of_mem_nhds (slitDisk_mem_nhds_zero hp hp1)))
  have he : q =ᶠ[𝓝 0] fun z => z + (slitC p : ℂ) * (z * slitKernel q z) := by
    filter_upwards [slit_geometric_recurrence hp hp1 hq] with z hz
    rw [hz.1.tsum_eq] at hz
    simpa only [slitKernel, div_eq_mul_inv, mul_assoc] using hz.2
  rw [coeff_congr_of_eventuallyEq he, coeff_sum_pair (f := fun z => z)
    (g := fun z => (slitC p : ℂ) * (z * slitKernel q z)) analyticAt_id
    (analyticAt_const.fun_mul (analyticAt_id.fun_mul hK)), coeff_identity,
    coeff_fun_const_mul, coeff_shift_one hK]
  simp

private def kernelPoly {σ : Type*} (a : ℕ → MvPolynomial σ ℕ) : ℕ → MvPolynomial σ ℕ
  | 0 => 1
  | n+1 => 2 * a (n+1) + (∑ i : Fin (n+2), a i * a (n+1-i)) +
      ∑ i : Fin (n+1), kernelPoly a i * a (n-i)
termination_by n => n
decreasing_by exact Fin.isLt _

private theorem eval_kernelPoly {σ : Type*} (a : ℕ → MvPolynomial σ ℕ)
    (ev : MvPolynomial σ ℕ →+* ℂ) (hqA : AnalyticAt ℂ q 0) (h0 : q 0 = 0)
    (n : ℕ) (ha : ∀ i ≤ n, ev (a i) = coeff i q) :
    ev (kernelPoly a n) = coeff n (slitKernel q) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [kernelPoly, coeff, slitKernel, h0]
    | succ n =>
      rw [kernelPoly, slit_kernel_coeff_recurrence hqA]
      simp only [map_add, map_mul, map_ofNat, map_sum, ha _ le_rfl]
      congr 1
      · congr 1
        exact Finset.sum_congr rfl fun i _ => by rw [ha _ (by omega), ha _ (Nat.sub_le ..)]
      · exact Finset.sum_congr rfl fun i _ => by
          rw [ih i i.isLt (fun j hj => ha j (by omega)), ha _ (by omega)]

/-- For degree n+2 the variables are c (index 0) and q₁ through q_(n+1).
The remainder after the displayed monomial is a universal polynomial over ℕ. -/
theorem slit_coeff_polynomial (n : ℕ) :
    ∃ P : MvPolynomial (Fin (n+2)) ℕ, ∀ {p : ℝ} {q : ℂ → ℂ},
      0 < p → p < 1 → IsSlitMap p q →
      coeff (n+2) q = 2 * (slitC p : ℂ) * coeff (n+1) q +
        MvPolynomial.eval₂Hom (Nat.castRingHom ℂ)
          (fun i : Fin (n+2) => if i.val = 0 then (slitC p : ℂ) else coeff i q) P := by
  let a (i : ℕ) : MvPolynomial (Fin (n+2)) ℕ :=
    if h : 0 < i ∧ i < n+2 then MvPolynomial.X ⟨i, h.2⟩ else 0
  refine ⟨MvPolynomial.X 0 * ((∑ i : Fin (n+2), a i * a (n+1-i)) +
    ∑ i : Fin (n+1), kernelPoly a i * a (n-i)), ?_⟩
  intro p q hp hp1 hq
  let ev := MvPolynomial.eval₂Hom (Nat.castRingHom ℂ)
    (fun i : Fin (n+2) => if i.val = 0 then (slitC p : ℂ) else coeff i q)
  have ha (i : ℕ) (hi : i ≤ n+1) : ev (a i) = coeff i q := by
    cases i with
    | zero => simp [a, coeff, hq.2.1]
    | succ i => simp [a, (show i+1 < n+2 by omega), ev]
  have hA := hq.1.1 0 (mem_of_mem_nhds (slitDisk_mem_nhds_zero hp hp1))
  change _ = _ + ev _
  rw [slit_coeff_of_kernel hp hp1 hq, slit_kernel_coeff_recurrence hA, map_mul, map_add,
    map_sum, map_sum]
  have hc : ev (MvPolynomial.X 0) = (slitC p : ℂ) := by simp [ev]
  rw [hc]
  simp only [map_mul, ha _ (Nat.sub_le ..)]
  have hsq (i : Fin (n+2)) : ev (a i) = coeff i q := ha i (by omega)
  have hk (i : Fin (n+1)) : ev (kernelPoly a i) = coeff i (slitKernel q) :=
    eval_kernelPoly a ev hA hq.2.1 i fun j hj => ha j (by omega)
  have hprev (i : Fin (n+1)) : ev (a (n-i)) = coeff (n-i) q := ha _ (by omega)
  simp only [hsq, hk, hprev]
  ring

open scoped ComplexOrder in
private theorem natPoly_eval_nonneg {σ : Type*} {x : σ → ℂ} (hx : ∀ i, 0 ≤ x i)
    (P : MvPolynomial σ ℕ) : 0 ≤ MvPolynomial.eval₂Hom (Nat.castRingHom ℂ) x P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add _ _ hp hq => simpa using add_nonneg hp hq
  | mul_X _ i hp => simpa using mul_nonneg hp (hx i)

open scoped ComplexOrder in
/-- The term 2 c q_(n−1) in degree n ≥ 2 gives a numerical lower bound. -/
theorem slit_coeff_lower_bound (hp : 0 < p) (hp1 : p < 1) (hq : IsSlitMap p q)
    {n : ℕ} (hn : 2 ≤ n) : 2 * slitC p * (coeff (n-1) q).re ≤ (coeff n q).re := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m+2 := ⟨n-2, by omega⟩
  obtain ⟨P, hP⟩ := slit_coeff_polynomial m
  let x (i : Fin (m+2)) : ℂ := if i.val = 0 then (slitC p : ℂ) else coeff i q
  have hx (i) : 0 ≤ x i := by
    dsimp [x]
    split
    · exact Complex.zero_le_real.mpr (slitC_pos hp hp1).le
    · rename_i hi
      obtain ⟨him, hre⟩ := slit_coeff_pos hp hp1 hq i (Nat.one_le_iff_ne_zero.mpr hi)
      exact Complex.nonneg_iff.mpr ⟨hre.le, him.symm⟩
  have h := (Complex.nonneg_iff.mp (natPoly_eval_nonneg hx P)).1
  rw [hP hp hp1 hq]
  simpa [x, Complex.mul_re] using
    (le_add_of_nonneg_right h : 2 * slitC p * (coeff (m+1) q).re ≤ _)

/--
info: 'Goodman.slit_coeff_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms slit_coeff_polynomial

end Goodman
